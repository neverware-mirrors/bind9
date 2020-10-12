/*
 * Copyright (C) Internet Systems Consortium, Inc. ("ISC")
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, you can obtain one at https://mozilla.org/MPL/2.0/.
 *
 * See the COPYRIGHT file distributed with this work for additional
 * information regarding copyright ownership.
 */

#include <libgen.h>
#include <unistd.h>
#include <uv.h>

#include <isc/atomic.h>
#include <isc/buffer.h>
#include <isc/condition.h>
#include <isc/log.h>
#include <isc/magic.h>
#include <isc/mem.h>
#include <isc/netmgr.h>
#include <isc/quota.h>
#include <isc/random.h>
#include <isc/refcount.h>
#include <isc/region.h>
#include <isc/result.h>
#include <isc/sockaddr.h>
#include <isc/stdtime.h>
#include <isc/thread.h>
#include <isc/util.h>

#include "netmgr-int.h"
#include "uv-compat.h"

static atomic_uint_fast32_t last_tcpquota_log = ATOMIC_VAR_INIT(0);

static bool
can_log_tcp_quota(void) {
	isc_stdtime_t now, last;

	isc_stdtime_get(&now);
	last = atomic_exchange_relaxed(&last_tcpquota_log, now);
	if (now != last) {
		return (true);
	}

	return (false);
}

static int
tcp_connect_direct(isc_nmsocket_t *sock, isc__nm_uvreq_t *req);

static void
tcp_close_direct(isc_nmsocket_t *sock);

static isc_result_t
tcp_send_direct(isc_nmsocket_t *sock, isc__nm_uvreq_t *req);
static void
tcp_connect_cb(uv_connect_t *uvreq, int status);

static void
tcp_connection_cb(uv_stream_t *server, int status);

static void
read_cb(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf);

static void
tcp_close_cb(uv_handle_t *uvhandle);

static void
tcp_listenclose_cb(uv_handle_t *handle);
static isc_result_t
accept_connection(isc_nmsocket_t *sock, isc_quota_t *quota);
static void
stoplistening(isc_nmsocket_t *sock);
static void
stop_tcp_parent(isc_nmsocket_t *sock);
void
tcp_listenclose_direct(isc_nmsocket_t *sock);

static void
quota_accept_cb(isc_quota_t *quota, void *sock0);

static int
tcp_connect_direct(isc_nmsocket_t *sock, isc__nm_uvreq_t *req) {
	isc__networker_t *worker = NULL;
	int r;

	REQUIRE(isc__nm_in_netthread());

	worker = &sock->mgr->workers[isc_nm_tid()];

	r = uv_tcp_init(&worker->loop, &sock->uv_handle.tcp);
	if (r != 0) {
		isc__nm_incstats(sock->mgr, sock->statsindex[STATID_OPENFAIL]);
		/* Socket was never opened; no need for tcp_close_direct() */
		atomic_store(&sock->closed, true);
		sock->result = isc__nm_uverr2result(r);
		atomic_store(&sock->connect_error, true);
		return (r);
	}

	if (req->local.length != 0) {
		r = uv_tcp_bind(&sock->uv_handle.tcp, &req->local.type.sa, 0);
		if (r != 0) {
			isc__nm_incstats(sock->mgr,
					 sock->statsindex[STATID_BINDFAIL]);
			sock->result = isc__nm_uverr2result(r);
			atomic_store(&sock->connect_error, true);
			tcp_close_direct(sock);
			return (r);
		}
	}

	uv_handle_set_data(&sock->uv_handle.handle, sock);
	r = uv_tcp_connect(&req->uv_req.connect, &sock->uv_handle.tcp,
			   &req->peer.type.sa, tcp_connect_cb);
	if (r != 0) {
		isc__nm_incstats(sock->mgr,
				 sock->statsindex[STATID_CONNECTFAIL]);
		sock->result = isc__nm_uverr2result(r);
		atomic_store(&sock->connect_error, true);
		tcp_close_direct(sock);
	}
	return (r);
}

void
isc__nm_async_tcpconnect(isc__networker_t *worker, isc__netievent_t *ev0) {
	isc__netievent_tcpconnect_t *ievent =
		(isc__netievent_tcpconnect_t *)ev0;
	isc_nmsocket_t *sock = ievent->sock;
	isc__nm_uvreq_t *req = ievent->req;
	int r;

	UNUSED(worker);

	r = tcp_connect_direct(sock, req);
	if (r != 0) {
		/* We need to issue callbacks ourselves */
		tcp_connect_cb(&req->uv_req.connect, r);
		goto done;
	}

	atomic_store(&sock->connected, true);

done:
	LOCK(&sock->lock);
	SIGNAL(&sock->cond);
	UNLOCK(&sock->lock);
}

static void
tcp_connect_cb(uv_connect_t *uvreq, int status) {
	isc_result_t result;
	isc__nm_uvreq_t *req = (isc__nm_uvreq_t *)uvreq->data;
	isc_nmsocket_t *sock = NULL;
	struct sockaddr_storage ss;
	isc_nmhandle_t *handle = NULL;

	sock = uv_handle_get_data((uv_handle_t *)uvreq->handle);

	REQUIRE(VALID_UVREQ(req));

	if (status != 0) {
		req->cb.connect(NULL, isc__nm_uverr2result(status), req->cbarg);
		isc__nm_uvreq_put(&req, sock);
		return;
	}

	sock = uv_handle_get_data((uv_handle_t *)uvreq->handle);
	isc__nm_incstats(sock->mgr, sock->statsindex[STATID_CONNECT]);
	uv_tcp_getpeername(&sock->uv_handle.tcp, (struct sockaddr *)&ss,
			   &(int){ sizeof(ss) });
	result = isc_sockaddr_fromsockaddr(&sock->peer, (struct sockaddr *)&ss);
	RUNTIME_CHECK(result == ISC_R_SUCCESS);

	handle = isc__nmhandle_get(sock, NULL, NULL);
	req->cb.connect(handle, ISC_R_SUCCESS, req->cbarg);

	isc__nm_uvreq_put(&req, sock);

	atomic_init(&sock->client, true);

	/*
	 * The sock is now attached to the handle.
	 */
	isc__nmsocket_detach(&sock);

	/*
	 * The connect callback should have attached to the handle.
	 * If it didn't, the socket will be closed now.
	 */
	isc_nmhandle_detach(&handle);
}

isc_result_t
isc_nm_tcpconnect(isc_nm_t *mgr, isc_nmiface_t *local, isc_nmiface_t *peer,
		  isc_nm_cb_t cb, void *cbarg, size_t extrahandlesize) {
	isc_nmsocket_t *nsock = NULL, *tmp = NULL;
	isc__netievent_tcpconnect_t *ievent = NULL;
	isc__nm_uvreq_t *req = NULL;
	isc_result_t result = ISC_R_SUCCESS;

	REQUIRE(VALID_NM(mgr));
	REQUIRE(local != NULL);
	REQUIRE(peer != NULL);

	nsock = isc_mem_get(mgr->mctx, sizeof(*nsock));
	isc__nmsocket_init(nsock, mgr, isc_nm_tcpsocket, local);
	nsock->extrahandlesize = extrahandlesize;
	nsock->result = ISC_R_SUCCESS;

	req = isc__nm_uvreq_get(mgr, nsock);
	req->cb.connect = cb;
	req->cbarg = cbarg;
	req->peer = peer->addr;
	req->local = local->addr;

	ievent = isc__nm_get_ievent(mgr, netievent_tcpconnect);
	ievent->sock = nsock;
	ievent->req = req;

	/*
	 * Async callbacks can dereference the socket in the meantime,
	 * we need to hold an additional reference to it.
	 */
	isc__nmsocket_attach(nsock, &tmp);

	if (isc__nm_in_netthread()) {
		nsock->tid = isc_nm_tid();
		isc__nm_async_tcpconnect(&mgr->workers[nsock->tid],
					 (isc__netievent_t *)ievent);
		isc__nm_put_ievent(mgr, ievent);
	} else {
		nsock->tid = isc_random_uniform(mgr->nworkers);
		isc__nm_enqueue_ievent(&mgr->workers[nsock->tid],
				       (isc__netievent_t *)ievent);

		LOCK(&nsock->lock);
		while (!atomic_load(&nsock->connected) &&
		       !atomic_load(&nsock->connect_error)) {
			WAIT(&nsock->cond, &nsock->lock);
		}
		UNLOCK(&nsock->lock);
	}

	if (nsock->result != ISC_R_SUCCESS) {
		result = nsock->result;
		isc__nmsocket_detach(&nsock);
	}

	isc__nmsocket_detach(&tmp);

	return (result);
}

isc_result_t
isc_nm_listentcp(isc_nm_t *mgr, isc_nmiface_t *iface,
		 isc_nm_accept_cb_t accept_cb, void *accept_cbarg,
		 size_t extrahandlesize, int backlog, isc_quota_t *quota,
		 isc_nmsocket_t **sockp) {
	isc_nmsocket_t *nsock = NULL;
	isc_result_t result = ISC_R_SUCCESS;

	REQUIRE(VALID_NM(mgr));

	nsock = isc_mem_get(mgr->mctx, sizeof(*nsock));
	isc__nmsocket_init(nsock, mgr, isc_nm_tcplistener, iface);

	nsock->nchildren = mgr->nworkers;
	atomic_init(&nsock->rchildren, mgr->nworkers);
	nsock->children = isc_mem_get(mgr->mctx,
				      mgr->nworkers * sizeof(*nsock));
	memset(nsock->children, 0, mgr->nworkers * sizeof(*nsock));

	nsock->accept_cb = accept_cb;
	nsock->accept_cbarg = accept_cbarg;
	nsock->extrahandlesize = extrahandlesize;
	nsock->backlog = backlog;
	nsock->result = ISC_R_SUCCESS;
	nsock->fd = -1;
	if (quota != NULL) {
		/*
		 * We don't attach to quota, just assign - to avoid
		 * increasing quota unnecessarily.
		 */
		nsock->pquota = quota;
	}
	isc_quota_cb_init(&nsock->quotacb, quota_accept_cb, nsock);

	for (size_t i = 0; i < mgr->nworkers; i++) {
		sa_family_t sa_family = iface->addr.type.sa.sa_family;

		isc_nmsocket_t *csock = &nsock->children[i];

		isc__nmsocket_init(csock, mgr, isc_nm_tcpsocket, iface);
		csock->parent = nsock;
		csock->tid = i;
		csock->extrahandlesize = extrahandlesize;
		csock->accept_cb = accept_cb;
		csock->accept_cbarg = accept_cbarg;
		csock->backlog = backlog;
		csock->result = ISC_R_SUCCESS;
		csock->pquota = nsock->pquota;
		REQUIRE(csock->parent != NULL);

		if (nsock->fd >= 0) {
			csock->fd = dup(nsock->fd);
		} else {
			csock->fd = socket(sa_family, SOCK_STREAM, 0);
		}
		RUNTIME_CHECK(csock->fd >= 0);

		result = isc__nm_socket_reuse(csock->fd);
		RUNTIME_CHECK(result == ISC_R_SUCCESS ||
			      result == ISC_R_NOTIMPLEMENTED);

		result = isc__nm_socket_reuse_lb(csock->fd);
		RUNTIME_CHECK(result == ISC_R_SUCCESS ||
			      result == ISC_R_NOTIMPLEMENTED);
		if (result == ISC_R_NOTIMPLEMENTED && nsock->fd == -1) {
			nsock->fd = csock->fd;
		}
		(void)isc__nm_socket_incoming_cpu(csock->fd);
		/* TODO: set min mss */
	}

	for (size_t i = 0; i < mgr->nworkers; i++) {
		isc__netievent_tcplisten_t *ievent = NULL;
		isc_nmsocket_t *csock = &nsock->children[i];

		ievent = isc__nm_get_ievent(mgr, netievent_tcplisten);
		ievent->sock = csock;
		isc__nm_enqueue_ievent(&mgr->workers[i],
				       (isc__netievent_t *)ievent);
		LOCK(&nsock->lock);
		while (!atomic_load(&csock->listening) && !atomic_load(&csock->listen_error)) {
			WAIT(&nsock->cond, &nsock->lock);
		}
		UNLOCK(&nsock->lock);
		if (csock->result != ISC_R_SUCCESS) {
			result = csock->result;
			break;
		}
	}

	if (result != ISC_R_SUCCESS) {
		stop_tcp_parent(nsock);
		return (result);
	}

	*sockp = nsock;
	return (ISC_R_SUCCESS);
}

void
isc__nm_async_tcplisten(isc__networker_t *worker, isc__netievent_t *ev0) {
	isc__netievent_tcplisten_t *ievent = (isc__netievent_tcplisten_t *)ev0;
	isc_nmsocket_t *sock = ievent->sock;
	struct sockaddr_storage sname;
	int r, flags = 0, snamelen = sizeof(sname);
	sa_family_t sa_family;
	uv_os_sock_t fd;

	REQUIRE(VALID_NMSOCK(sock));
	REQUIRE(isc__nm_in_netthread());
	REQUIRE(sock->type == isc_nm_tcpsocket);

	r = uv_tcp_init(&worker->loop, &sock->uv_handle.tcp);
	if (r != 0) {
		isc__nm_incstats(sock->mgr, sock->statsindex[STATID_OPENFAIL]);
		/* The socket was never opened, so no need for uv_close() */
		atomic_store(&sock->closed, true);
		sock->result = isc__nm_uverr2result(r);
		atomic_store(&sock->listen_error, true);
		goto done;
	}

	r = uv_tcp_open(&sock->uv_handle.tcp, sock->fd);
	if (r != 0) {
		isc__nm_incstats(sock->mgr, sock->statsindex[STATID_OPENFAIL]);
		sock->result = isc__nm_uverr2result(r);
		atomic_store(&sock->listen_error, true);
		goto done;
	}
	isc__nm_incstats(sock->mgr, sock->statsindex[STATID_OPEN]);

	sa_family = sock->iface->addr.type.sa.sa_family;
	if (sa_family == AF_INET6) {
		flags = UV_TCP_IPV6ONLY;
	}

	r = uv_tcp_bind(&sock->uv_handle.tcp, &sock->iface->addr.type.sa,
			flags);
	if (r == UV_EADDRNOTAVAIL &&
	    uv_fileno(&sock->uv_handle.handle, (uv_os_fd_t *)&fd) == 0 &&
	    isc__nm_socket_freebind(fd, sa_family) == ISC_R_SUCCESS)
	{
		/*
		 * Retry binding with IP_FREEBIND (or equivalent option) if the
		 * address is not available. This helps with IPv6 tentative
		 * addresses which are reported by the route socket, although
		 * named is not yet able to properly bind to them.
		 */
		r = uv_tcp_bind(&sock->uv_handle.tcp,
				&sock->iface->addr.type.sa, flags);
	}

	if (r != 0) {
		isc__nm_incstats(sock->mgr, sock->statsindex[STATID_BINDFAIL]);
		uv_close(&sock->uv_handle.handle, tcp_listenclose_cb);
		sock->result = isc__nm_uverr2result(r);
		atomic_store(&sock->listen_error, true);
		goto done;
	}

	/*
	 * By doing this now, we can find out immediately whether bind()
	 * failed, and quit if so. (uv_bind() uses a delayed error,
	 * initially returning success even if bind() fails, and this
	 * could cause a deadlock later if we didn't check first.)
	 */
	r = uv_tcp_getsockname(&sock->uv_handle.tcp, (struct sockaddr *)&sname,
			       &snamelen);
	if (r != 0) {
		uv_close(&sock->uv_handle.handle, tcp_listenclose_cb);
		sock->result = isc__nm_uverr2result(r);
		atomic_store(&sock->listen_error, true);
		goto done;
	}

	/*
	 * The callback will run in the same thread uv_listen() was called
	 * from, so a race with tcp_connection_cb() isn't possible.
	 */
	r = uv_listen((uv_stream_t *)&sock->uv_handle.tcp, sock->backlog,
		      tcp_connection_cb);
	if (r != 0) {
		isc_log_write(isc_lctx, ISC_LOGCATEGORY_GENERAL,
			      ISC_LOGMODULE_NETMGR, ISC_LOG_ERROR,
			      "uv_listen failed: %s",
			      isc_result_totext(isc__nm_uverr2result(r)));
		uv_close(&sock->uv_handle.handle, tcp_listenclose_cb);
		sock->result = isc__nm_uverr2result(r);
		atomic_store(&sock->listen_error, true);
		goto done;
	}

	uv_handle_set_data(&sock->uv_handle.handle, NULL);
	isc__nmsocket_attach(sock,
			     (isc_nmsocket_t **)&sock->uv_handle.tcp.data);

	atomic_store(&sock->listening, true);

done:
	LOCK(&sock->parent->lock);
	SIGNAL(&sock->parent->cond);
	UNLOCK(&sock->parent->lock);
	return;
}

static void
tcp_connection_cb(uv_stream_t *server, int status) {
	isc_nmsocket_t *sock = uv_handle_get_data((uv_handle_t *)server);
	isc_result_t result;

	REQUIRE(sock->tid == isc_nm_tid());

	if (status != 0) {
		result = isc__nm_uverr2result(status);
		isc_log_write(isc_lctx, ISC_LOGCATEGORY_GENERAL,
			      ISC_LOGMODULE_NETMGR, ISC_LOG_ERROR,
			      "TCP connection failed: %s",
			      isc_result_totext(result));
		return;
	}

	result = accept_connection(sock, NULL);
	if (result != ISC_R_SUCCESS && result != ISC_R_NOCONN) {
		if ((result != ISC_R_QUOTA && result != ISC_R_SOFTQUOTA) ||
		    can_log_tcp_quota()) {
			isc_log_write(isc_lctx, ISC_LOGCATEGORY_GENERAL,
				      ISC_LOGMODULE_NETMGR, ISC_LOG_ERROR,
				      "TCP connection failed: %s",
				      isc_result_totext(result));
		}
	}
}

static void
stop_tcp_child(isc_nmsocket_t *sock) {
	REQUIRE(sock->type == isc_nm_tcpsocket);
	REQUIRE(sock->tid == isc_nm_tid());
	REQUIRE(sock->parent != NULL);

	if (sock->listening) {
		uv_close((uv_handle_t *)&sock->uv_handle.tcp, tcp_listenclose_cb);

		isc__nm_incstats(sock->mgr, sock->statsindex[STATID_CLOSE]);
	} else {
		/* We are in nmthread, so we can call the callback directly */
		tcp_listenclose_direct(sock);
	}
}

static void
stoplistening(isc_nmsocket_t *sock) {
	REQUIRE(sock->type == isc_nm_tcplistener);

	for (int i = 0; i < sock->nchildren; i++) {
		isc__netievent_tcpstop_t *ievent = NULL;
		isc_nmsocket_t *csock = &sock->children[i];

		REQUIRE(VALID_NMSOCK(csock));

		if (isc_nm_tid() == csock->tid) {
			stop_tcp_child(csock);
			continue;
		}

		ievent = isc__nm_get_ievent(sock->mgr, netievent_tcpstop);
		ievent->sock = csock;
		isc__nm_enqueue_ievent(&sock->mgr->workers[i],
				       (isc__netievent_t *)ievent);
	}

	LOCK(&sock->lock);
	while (atomic_load_relaxed(&sock->rchildren) > 0) {
		WAIT(&sock->cond, &sock->lock);
	}
	atomic_store(&sock->closed, true);
	UNLOCK(&sock->lock);

	isc__nmsocket_prep_destroy(sock);
}

static void
stop_tcp_parent(isc_nmsocket_t *sock) {
	REQUIRE(sock->parent == NULL);

	/*
	 * If the manager is interlocked, re-enqueue this as an asynchronous
	 * event. Otherwise, go ahead and stop listening right away.
	 */
	if (!isc__nm_acquire_interlocked(sock->mgr)) {
		isc__netievent_tcpstop_t *ievent =
			isc__nm_get_ievent(sock->mgr, netievent_tcpstop);
		ievent->sock = sock;
		isc__nm_enqueue_ievent(&sock->mgr->workers[sock->tid],
				       (isc__netievent_t *)ievent);
	} else {
		stoplistening(sock);
		isc__nm_drop_interlocked(sock->mgr);
	}
}

void
isc__nm_tcp_stoplistening(isc_nmsocket_t *sock) {
	REQUIRE(!isc__nm_in_netthread());
	REQUIRE(VALID_NMSOCK(sock));
	REQUIRE(sock->type == isc_nm_tcplistener);

	/*
	 * Socket is already closing; there's nothing to do.
	 */
	if (!isc__nmsocket_active(sock)) {
		return;
	}
	/*
	 * Mark it inactive now so that all sends will be ignored
	 * and we won't try to stop listening again.
	 */
	atomic_store(&sock->active, false);

	stop_tcp_parent(sock);
}

void
isc__nm_async_tcpstop(isc__networker_t *worker, isc__netievent_t *ev0) {
	isc__netievent_tcpstop_t *ievent = (isc__netievent_tcpstop_t *)ev0;
	isc_nmsocket_t *sock = ievent->sock;

	UNUSED(worker);

	REQUIRE(isc__nm_in_netthread());
	REQUIRE(VALID_NMSOCK(sock));

	/*
	 * If this is a child socket, stop listening and return.
	 */
	if (sock->parent != NULL) {
		stop_tcp_child(sock);
		return;
	};

	stop_tcp_parent(sock);
}

void
tcp_listenclose_direct(isc_nmsocket_t *sock) {
	REQUIRE(VALID_NMSOCK(sock));
	isc_nmsocket_t *ssock = sock->parent;
	REQUIRE(VALID_NMSOCK(ssock));

	atomic_store(&sock->closed, true);
	atomic_store(&sock->listening, false);
	sock->pquota = NULL;

	LOCK(&ssock->lock);
	atomic_fetch_sub(&ssock->rchildren, 1);
	UNLOCK(&ssock->lock);
	BROADCAST(&ssock->cond);
}

/*
 * This callback is used for closing listening sockets.
 */
static void
tcp_listenclose_cb(uv_handle_t *handle) {
	isc_nmsocket_t *sock = uv_handle_get_data(handle);

	tcp_listenclose_direct(sock);

	isc__nmsocket_detach((isc_nmsocket_t **)&sock->uv_handle.tcp.data);
}

static void
readtimeout_cb(uv_timer_t *handle) {
	isc_nmsocket_t *sock = uv_handle_get_data((uv_handle_t *)handle);
	isc_nm_recv_cb_t cb;
	void *cbarg;

	REQUIRE(VALID_NMSOCK(sock));
	REQUIRE(sock->tid == isc_nm_tid());

	/*
	 * Socket is actively processing something, so restart the timer
	 * and return.
	 */
	if (atomic_load(&sock->processing)) {
		uv_timer_start(handle, readtimeout_cb, sock->read_timeout, 0);
		return;
	}

	/*
	 * Timeout; stop reading and process whatever we have.
	 */
	uv_read_stop(&sock->uv_handle.stream);
	if (sock->quota) {
		isc_quota_detach(&sock->quota);
	}

	cb = sock->recv_cb;
	cbarg = sock->recv_cbarg;
	isc__nmsocket_clearcb(sock);

	if (cb != NULL) {
		cb(sock->statichandle, ISC_R_TIMEDOUT, NULL, cbarg);
	}
}

isc_result_t
isc__nm_tcp_read(isc_nmhandle_t *handle, isc_nm_recv_cb_t cb, void *cbarg) {
	isc_nmsocket_t *sock = NULL;
	isc__netievent_startread_t *ievent = NULL;

	REQUIRE(VALID_NMHANDLE(handle));
	REQUIRE(VALID_NMSOCK(handle->sock));

	sock = handle->sock;

	REQUIRE(sock->tid == isc_nm_tid());
	sock->recv_cb = cb;
	sock->recv_cbarg = cbarg;

	ievent = isc__nm_get_ievent(sock->mgr, netievent_tcpstartread);
	ievent->sock = sock;

	if (sock->tid == isc_nm_tid()) {
		isc__nm_async_tcp_startread(&sock->mgr->workers[sock->tid],
					    (isc__netievent_t *)ievent);
		isc__nm_put_ievent(sock->mgr, ievent);
	} else {
		isc__nm_enqueue_ievent(&sock->mgr->workers[sock->tid],
				       (isc__netievent_t *)ievent);
	}

	return (ISC_R_SUCCESS);
}

/*%<
 * Allocator for TCP read operations. Limited to size 2^16.
 *
 * Note this doesn't actually allocate anything, it just assigns the
 * worker's receive buffer to a socket, and marks it as "in use".
 */
static void
tcp_alloc_cb(uv_handle_t *handle, size_t size, uv_buf_t *buf) {
	isc_nmsocket_t *sock = uv_handle_get_data(handle);
	isc__networker_t *worker = NULL;

	REQUIRE(VALID_NMSOCK(sock));
	REQUIRE(sock->type == isc_nm_tcpsocket);
	REQUIRE(isc__nm_in_netthread());
	REQUIRE(size <= 65536);

	worker = &sock->mgr->workers[sock->tid];
	INSIST(!worker->recvbuf_inuse);

	buf->base = worker->recvbuf;
	buf->len = size;
	worker->recvbuf_inuse = true;
}

void
isc__nm_async_tcp_startread(isc__networker_t *worker, isc__netievent_t *ev0) {
	isc__netievent_startread_t *ievent = (isc__netievent_startread_t *)ev0;
	isc_nmsocket_t *sock = ievent->sock;
	int r;

	REQUIRE(worker->id == isc_nm_tid());
	if (sock->read_timeout != 0) {
		if (!sock->timer_initialized) {
			uv_timer_init(&worker->loop, &sock->timer);
			uv_handle_set_data((uv_handle_t *)&sock->timer, sock);
			sock->timer_initialized = true;
		}
		uv_timer_start(&sock->timer, readtimeout_cb, sock->read_timeout,
			       0);
	}

	r = uv_read_start(&sock->uv_handle.stream, tcp_alloc_cb, read_cb);
	if (r != 0) {
		isc__nm_incstats(sock->mgr, sock->statsindex[STATID_RECVFAIL]);
	}
}

isc_result_t
isc__nm_tcp_pauseread(isc_nmsocket_t *sock) {
	isc__netievent_pauseread_t *ievent = NULL;

	REQUIRE(VALID_NMSOCK(sock));

	if (atomic_load(&sock->readpaused)) {
		return (ISC_R_SUCCESS);
	}

	atomic_store(&sock->readpaused, true);
	ievent = isc__nm_get_ievent(sock->mgr, netievent_tcppauseread);
	ievent->sock = sock;

	if (sock->tid == isc_nm_tid()) {
		isc__nm_async_tcp_pauseread(&sock->mgr->workers[sock->tid],
					    (isc__netievent_t *)ievent);
		isc__nm_put_ievent(sock->mgr, ievent);
	} else {
		isc__nm_enqueue_ievent(&sock->mgr->workers[sock->tid],
				       (isc__netievent_t *)ievent);
	}

	return (ISC_R_SUCCESS);
}

void
isc__nm_async_tcp_pauseread(isc__networker_t *worker, isc__netievent_t *ev0) {
	isc__netievent_pauseread_t *ievent = (isc__netievent_pauseread_t *)ev0;
	isc_nmsocket_t *sock = ievent->sock;

	REQUIRE(VALID_NMSOCK(sock));
	REQUIRE(worker->id == isc_nm_tid());

	if (sock->timer_initialized) {
		uv_timer_stop(&sock->timer);
	}
	uv_read_stop(&sock->uv_handle.stream);
}

isc_result_t
isc__nm_tcp_resumeread(isc_nmsocket_t *sock) {
	isc__netievent_startread_t *ievent = NULL;

	REQUIRE(VALID_NMSOCK(sock));
	REQUIRE(sock->tid == isc_nm_tid());

	if (sock->recv_cb == NULL) {
		return (ISC_R_CANCELED);
	}

	if (!atomic_load(&sock->readpaused)) {
		return (ISC_R_SUCCESS);
	}

	atomic_store(&sock->readpaused, false);

	ievent = isc__nm_get_ievent(sock->mgr, netievent_tcpstartread);
	ievent->sock = sock;

	if (sock->tid == isc_nm_tid()) {
		isc__nm_async_tcp_startread(&sock->mgr->workers[sock->tid],
					    (isc__netievent_t *)ievent);
		isc__nm_put_ievent(sock->mgr, ievent);
	} else {
		isc__nm_enqueue_ievent(&sock->mgr->workers[sock->tid],
				       (isc__netievent_t *)ievent);
	}

	return (ISC_R_SUCCESS);
}

static void
read_cb(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf) {
	isc_nmsocket_t *sock = uv_handle_get_data((uv_handle_t *)stream);
	isc_nm_recv_cb_t cb;
	void *cbarg;

	REQUIRE(VALID_NMSOCK(sock));
	REQUIRE(sock->tid == isc_nm_tid());
	REQUIRE(buf != NULL);

	cb = sock->recv_cb;
	cbarg = sock->recv_cbarg;

	if (nread >= 0) {
		isc_region_t region = { .base = (unsigned char *)buf->base,
					.length = nread };

		if (cb != NULL) {
			cb(sock->statichandle, ISC_R_SUCCESS, &region, cbarg);
		}

		sock->read_timeout = (atomic_load(&sock->keepalive)
					      ? sock->mgr->keepalive
					      : sock->mgr->idle);

		if (sock->timer_initialized && sock->read_timeout != 0) {
			/* The timer will be updated */
			uv_timer_start(&sock->timer, readtimeout_cb,
				       sock->read_timeout, 0);
		}

		isc__nm_free_uvbuf(sock, buf);
		return;
	}

	isc__nm_free_uvbuf(sock, buf);

	/*
	 * This might happen if the inner socket is closing.  It means that
	 * it's detached, so the socket will be closed.
	 */
	if (cb != NULL) {
		isc__nm_incstats(sock->mgr, sock->statsindex[STATID_RECVFAIL]);
		isc__nmsocket_clearcb(sock);
		cb(sock->statichandle, ISC_R_EOF, NULL, cbarg);
	}

	/*
	 * We don't need to clean up now; the socket will be closed and
	 * resources and quota reclaimed when handle is freed in
	 * isc__nm_tcp_close().
	 */
}

static void
quota_accept_cb(isc_quota_t *quota, void *sock0) {
	isc_nmsocket_t *sock = (isc_nmsocket_t *)sock0;
	isc__netievent_tcpaccept_t *ievent = NULL;

	REQUIRE(VALID_NMSOCK(sock));

	/*
	 * Create a tcpaccept event and pass it using the async channel.
	 */
	ievent = isc__nm_get_ievent(sock->mgr, netievent_tcpaccept);
	ievent->sock = sock;
	ievent->quota = quota;
	isc__nm_enqueue_ievent(&sock->mgr->workers[sock->tid],
			       (isc__netievent_t *)ievent);
}

/*
 * This is called after we get a quota_accept_cb() callback.
 */
void
isc__nm_async_tcpaccept(isc__networker_t *worker, isc__netievent_t *ev0) {
	isc_result_t result;
	isc__netievent_tcpaccept_t *ievent = (isc__netievent_tcpaccept_t *)ev0;
	isc_nmsocket_t *sock = ievent->sock;

	REQUIRE(VALID_NMSOCK(sock));
	REQUIRE(worker->id == sock->tid);

	result = accept_connection(ievent->sock, ievent->quota);
	if (result != ISC_R_SUCCESS && result != ISC_R_NOCONN) {
		if ((result != ISC_R_QUOTA && result != ISC_R_SOFTQUOTA) ||
		    can_log_tcp_quota()) {
			isc_log_write(isc_lctx, ISC_LOGCATEGORY_GENERAL,
				      ISC_LOGMODULE_NETMGR, ISC_LOG_ERROR,
				      "TCP connection failed: %s",
				      isc_result_totext(result));
		}
	}

	/*
	 * The socket was attached just before we called isc_quota_attach_cb().
	 */
	isc__nmsocket_detach(&ievent->sock);
}

static isc_result_t
accept_tcp_child(isc_nmsocket_t *csock) {
	int r;
	isc_result_t result;
	struct sockaddr_storage ss;
	isc_sockaddr_t local;
	isc_nm_accept_cb_t accept_cb;
	void *accept_cbarg;
	isc_nmhandle_t *handle;

	r = uv_tcp_getpeername(&csock->uv_handle.tcp, (struct sockaddr *)&ss,
			       &(int){ sizeof(ss) });
	if (r != 0) {
		result = isc__nm_uverr2result(r);
		goto error;
	}

	result = isc_sockaddr_fromsockaddr(&csock->peer, (struct sockaddr *)&ss);
	if (result != ISC_R_SUCCESS) {
		goto error;
	}

	r = uv_tcp_getsockname(&csock->uv_handle.tcp, (struct sockaddr *)&ss,
			       &(int){ sizeof(ss) });
	if (r != 0) {
		result = isc__nm_uverr2result(r);
		goto error;
	}

	result = isc_sockaddr_fromsockaddr(&local, (struct sockaddr *)&ss);
	if (result != ISC_R_SUCCESS) {
		goto error;
	}

	handle = isc__nmhandle_get(csock, NULL, &local);

	INSIST(csock->accept_cb != NULL);
	accept_cb = csock->accept_cb;
	accept_cbarg = csock->accept_cbarg;

	csock->read_timeout = csock->mgr->init;
	accept_cb(handle, ISC_R_SUCCESS, accept_cbarg);

	/*
	 * csock is now attached to the handle.
	 */
	isc__nmsocket_detach(&csock);

	/*
	 * The accept callback should have attached to the handle.
	 * If it didn't, the ssocket will be closed now.
	 */
	isc_nmhandle_detach(&handle);

	return (ISC_R_SUCCESS);

error:
	isc_log_write(isc_lctx, ISC_LOGCATEGORY_GENERAL, ISC_LOGMODULE_NETMGR,
		      ISC_LOG_ERROR, "Accepting TCP connection failed: %s",
		      isc_result_totext(result));

	/*
	 * Detach the quota early to make room for other connections;
	 * otherwise it'd be detached later asynchronously, and clog
	 * the quota unnecessarily.
	 */
	if (csock->quota != NULL) {
		isc_quota_detach(&csock->quota);
	}

	/*
	 * Detach the ssocket properly to make sure uv_close() is called.
	 */
	isc__nmsocket_detach(&csock);

	return (result);

}

static isc_result_t
accept_connection(isc_nmsocket_t *ssock, isc_quota_t *quota) {
	isc_result_t result;
	isc__networker_t *worker = NULL;
	isc_nmsocket_t *csock = NULL;
	int r;

	REQUIRE(VALID_NMSOCK(ssock));

	if (!atomic_load_relaxed(&ssock->active) ||
	    atomic_load_relaxed(&ssock->mgr->closing))
	{
		/* We're closing, bail */
		if (quota != NULL) {
			isc_quota_detach(&quota);
		}
		return (ISC_R_CANCELED);
	}

	/* We can be called directly or as a callback from quota */
	if (ssock->pquota != NULL && quota == NULL) {
		/*
		 * We need to attach to ssock, because it might be queued
		 * waiting for a TCP quota slot.  If so, then we'll detach it
		 * later when the connection is accepted. (XXX: This may be
		 * suboptimal, it might be better not to attach unless
		 * we need to - but we risk a race then.)
		 */
		isc_nmsocket_t *tssock = NULL;
		isc__nmsocket_attach(ssock, &tssock);
		result = isc_quota_attach_cb(ssock->pquota, &quota,
					     &ssock->quotacb);
		if (result == ISC_R_QUOTA) {
			isc__nm_incstats(ssock->mgr,
					 ssock->statsindex[STATID_ACCEPTFAIL]);
			return (result);
		}

		/*
		 * We're under quota, so there's no need to wait;
		 * Detach the ssocket.
		 */
		isc__nmsocket_detach(&tssock);
	}

	isc__nm_incstats(ssock->mgr, ssock->statsindex[STATID_ACCEPT]);

	worker = &ssock->mgr->workers[isc_nm_tid()];

	/* Duplicate the server socket */
	csock = isc_mem_get(ssock->mgr->mctx, sizeof(isc_nmsocket_t));
	isc__nmsocket_init(csock, ssock->mgr, isc_nm_tcpsocket, ssock->iface);
	csock->tid = ssock->tid;
	csock->extrahandlesize = ssock->extrahandlesize;
	isc__nmsocket_attach(ssock, &csock->server);
	csock->accept_cb = ssock->accept_cb;
	csock->accept_cbarg = ssock->accept_cbarg;
	csock->quota = quota;

	uv_tcp_init(&worker->loop, &csock->uv_handle.tcp);

	r = uv_accept(&ssock->uv_handle.stream, &csock->uv_handle.stream);
	if (r != 0) {
		result = isc__nm_uverr2result(r);
		isc__nmsocket_detach(&csock->server);
		uv_close(&csock->uv_handle.handle, tcp_close_cb);
		if (quota != NULL) {
			isc_quota_detach(&quota);
		}
		return (result);
	}

	result = accept_tcp_child(csock);

	return (result);
}

isc_result_t
isc__nm_tcp_send(isc_nmhandle_t *handle, isc_region_t *region, isc_nm_cb_t cb,
		 void *cbarg) {
	isc_nmsocket_t *sock = handle->sock;
	isc__netievent_tcpsend_t *ievent = NULL;
	isc__nm_uvreq_t *uvreq = NULL;

	REQUIRE(sock->type == isc_nm_tcpsocket);

	uvreq = isc__nm_uvreq_get(sock->mgr, sock);
	uvreq->uvbuf.base = (char *)region->base;
	uvreq->uvbuf.len = region->length;
	isc_nmhandle_attach(handle, &uvreq->handle);
	uvreq->cb.send = cb;
	uvreq->cbarg = cbarg;

	if (sock->tid == isc_nm_tid()) {
		/*
		 * If we're in the same thread as the socket we can send the
		 * data directly
		 */
		return (tcp_send_direct(sock, uvreq));
	} else {
		/*
		 * We need to create an event and pass it using async channel
		 */
		ievent = isc__nm_get_ievent(sock->mgr, netievent_tcpsend);
		ievent->sock = sock;
		ievent->req = uvreq;
		isc__nm_enqueue_ievent(&sock->mgr->workers[sock->tid],
				       (isc__netievent_t *)ievent);
		return (ISC_R_SUCCESS);
	}

	return (ISC_R_UNEXPECTED);
}

static void
tcp_send_cb(uv_write_t *req, int status) {
	isc_result_t result = ISC_R_SUCCESS;
	isc__nm_uvreq_t *uvreq = (isc__nm_uvreq_t *)req->data;
	isc_nmsocket_t *sock = NULL;

	REQUIRE(VALID_UVREQ(uvreq));
	REQUIRE(VALID_NMHANDLE(uvreq->handle));

	if (status < 0) {
		result = isc__nm_uverr2result(status);
		isc__nm_incstats(uvreq->sock->mgr,
				 uvreq->sock->statsindex[STATID_SENDFAIL]);
	}

	uvreq->cb.send(uvreq->handle, result, uvreq->cbarg);

	sock = uvreq->handle->sock;
	isc__nm_uvreq_put(&uvreq, sock);
}

/*
 * Handle 'tcpsend' async event - send a packet on the socket
 */
void
isc__nm_async_tcpsend(isc__networker_t *worker, isc__netievent_t *ev0) {
	isc_result_t result;
	isc__netievent_tcpsend_t *ievent = (isc__netievent_tcpsend_t *)ev0;

	REQUIRE(worker->id == ievent->sock->tid);

	if (!atomic_load(&ievent->sock->parent->active)) {
		return;
	}

	result = tcp_send_direct(ievent->sock, ievent->req);
	if (result != ISC_R_SUCCESS) {
		ievent->req->cb.send(ievent->req->handle, result,
				     ievent->req->cbarg);
		isc__nm_uvreq_put(&ievent->req, ievent->req->handle->sock);
	}
}

static isc_result_t
tcp_send_direct(isc_nmsocket_t *sock, isc__nm_uvreq_t *req) {
	int r;

	REQUIRE(sock->tid == isc_nm_tid());
	REQUIRE(sock->type == isc_nm_tcpsocket);
	r = uv_write(&req->uv_req.write, &sock->uv_handle.stream, &req->uvbuf,
		     1, tcp_send_cb);
	if (r < 0) {
		isc__nm_incstats(sock->mgr, sock->statsindex[STATID_SENDFAIL]);
		req->cb.send(NULL, isc__nm_uverr2result(r), req->cbarg);
		isc__nm_uvreq_put(&req, sock);
		return (isc__nm_uverr2result(r));
	}

	return (ISC_R_SUCCESS);
}

static void
tcp_close_cb(uv_handle_t *uvhandle) {
	isc_nmsocket_t *sock = uv_handle_get_data(uvhandle);

	REQUIRE(VALID_NMSOCK(sock));

	isc__nm_incstats(sock->mgr, sock->statsindex[STATID_CLOSE]);
	atomic_store(&sock->closed, true);
	atomic_store(&sock->connected, false);

	isc__nmsocket_prep_destroy(sock);
}

static void
timer_close_cb(uv_handle_t *uvhandle) {
	isc_nmsocket_t *sock = uv_handle_get_data(uvhandle);

	REQUIRE(VALID_NMSOCK(sock));

	if (sock->server != NULL) {
		isc__nmsocket_detach(&sock->server);
	}
	uv_close(&sock->uv_handle.handle, tcp_close_cb);
}

static void
tcp_close_direct(isc_nmsocket_t *sock) {
	REQUIRE(VALID_NMSOCK(sock));
	REQUIRE(sock->tid == isc_nm_tid());
	REQUIRE(sock->type == isc_nm_tcpsocket);
	if (sock->quota != NULL) {
		isc_quota_detach(&sock->quota);
	}
	if (sock->timer_initialized) {
		sock->timer_initialized = false;
		uv_timer_stop(&sock->timer);
		uv_close((uv_handle_t *)&sock->timer, timer_close_cb);
	} else {
		if (sock->server != NULL) {
			isc__nmsocket_detach(&sock->server);
		}
		uv_close(&sock->uv_handle.handle, tcp_close_cb);
	}
}

void
isc__nm_tcp_close(isc_nmsocket_t *sock) {
	REQUIRE(VALID_NMSOCK(sock));
	REQUIRE(sock->type == isc_nm_tcpsocket);

	if (sock->tid == isc_nm_tid()) {
		tcp_close_direct(sock);
	} else {
		/*
		 * We need to create an event and pass it using async channel
		 */
		isc__netievent_tcpclose_t *ievent =
			isc__nm_get_ievent(sock->mgr, netievent_tcpclose);

		ievent->sock = sock;
		isc__nm_enqueue_ievent(&sock->mgr->workers[sock->tid],
				       (isc__netievent_t *)ievent);
	}
}

void
isc__nm_async_tcpclose(isc__networker_t *worker, isc__netievent_t *ev0) {
	isc__netievent_tcpclose_t *ievent = (isc__netievent_tcpclose_t *)ev0;

	REQUIRE(worker->id == ievent->sock->tid);

	tcp_close_direct(ievent->sock);
}

void
isc__nm_tcp_shutdown(isc_nmsocket_t *sock) {
	REQUIRE(VALID_NMSOCK(sock));
	REQUIRE(sock->tid == isc_nm_tid());

	if (sock->type == isc_nm_tcpsocket && sock->statichandle != NULL) {
		isc_nm_recv_cb_t cb;
		void *cbarg;

		cb = sock->recv_cb;
		cbarg = sock->recv_cbarg;
		isc__nmsocket_clearcb(sock);

		if (cb != NULL) {
			cb(sock->statichandle, ISC_R_CANCELED, NULL, cbarg);
		}
	}
}

void
isc__nm_tcp_cancelread(isc_nmhandle_t *handle) {
	isc_nmsocket_t *sock = NULL;

	REQUIRE(VALID_NMHANDLE(handle));

	sock = handle->sock;

	REQUIRE(VALID_NMSOCK(sock));
	REQUIRE(sock->type == isc_nm_tcpsocket);
	REQUIRE(sock->tid == isc_nm_tid());

	if (atomic_load(&sock->client)) {
		isc_nm_recv_cb_t cb;
		void *cbarg;

		cb = sock->recv_cb;
		cbarg = sock->recv_cbarg;
		isc__nmsocket_clearcb(sock);

		cb(handle, ISC_R_EOF, NULL, cbarg);
	}
}
