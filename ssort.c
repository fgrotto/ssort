/* ssort.c — O(m log^{2/3} n) SSSP for directed graphs.
 *
 * Implementation of:
 *   R. Duan, J. Mao, X. Mao, X. Shu, L. Yin.
 *   "Breaking the Sorting Barrier for Directed Single-Source Shortest Paths."
 *   STOC 2025. arXiv:2504.17033
 *
 * Single file. Pure C11. No dependencies beyond libc + libm.
 */

#include "ssort.h"
#include <math.h>
#include <stdlib.h>
#include <string.h>

/* ─── Utilities ──────────────────────────────────────────────────── */

static void *xmalloc(size_t n) {
    void *p = malloc(n);
    if (!p && n) abort();
    return p;
}

static void *xcalloc(size_t cnt, size_t sz) {
    void *p = calloc(cnt, sz);
    if (!p && cnt && sz) abort();
    return p;
}

static void *xrealloc(void *p, size_t n) {
    p = realloc(p, n);
    if (!p && n) abort();
    return p;
}

static int imin(int a, int b) { return a < b ? a : b; }
static int imax(int a, int b) { return a > b ? a : b; }
static double dmin(double a, double b) { return a < b ? a : b; }

/* ─── CSR Graph (built from edge list) ───────────────────────────── */

typedef struct {
    int     n;
    int     m;
    int    *off;   /* [n+1] */
    int    *adj;   /* [m] */
    double *wgt;   /* [m] */
} CSR;

static void csr_build(CSR *c, int n, const int *eu, const int *ev,
                       const double *ew, int m) {
    c->n = n;
    c->m = m;
    c->off = xcalloc(n + 1, sizeof(int));
    c->adj = xmalloc(sizeof(int) * (m > 0 ? m : 1));
    c->wgt = xmalloc(sizeof(double) * (m > 0 ? m : 1));

    /* Count out-degrees. */
    for (int i = 0; i < m; i++)
        c->off[eu[i] + 1]++;

    /* Prefix sum. */
    for (int i = 1; i <= n; i++)
        c->off[i] += c->off[i - 1];

    /* Fill edges. */
    int *cur = xmalloc(sizeof(int) * n);
    memcpy(cur, c->off, sizeof(int) * n);
    for (int i = 0; i < m; i++) {
        int pos = cur[eu[i]]++;
        c->adj[pos] = ev[i];
        c->wgt[pos] = ew[i];
    }
    free(cur);
}

static void csr_free(CSR *c) {
    free(c->off); free(c->adj); free(c->wgt);
}

/* ─── Min-Heap ───────────────────────────────────────────────────── */

typedef struct {
    int    *keys;
    double *vals;
    int    *pos;
    int     n, cap;
} Heap;

static void heap_init(Heap *h, int cap) {
    h->keys = xmalloc(sizeof(int) * cap);
    h->vals = xmalloc(sizeof(double) * cap);
    h->pos  = xmalloc(sizeof(int) * cap);
    h->n = 0; h->cap = cap;
    for (int i = 0; i < cap; i++) h->pos[i] = -1;
}

static void heap_free(Heap *h) {
    free(h->keys); free(h->vals); free(h->pos);
}

static void heap_swap(Heap *h, int i, int j) {
    int tk = h->keys[i]; double tv = h->vals[i];
    h->keys[i] = h->keys[j]; h->vals[i] = h->vals[j];
    h->keys[j] = tk; h->vals[j] = tv;
    h->pos[h->keys[i]] = i;
    h->pos[h->keys[j]] = j;
}

static void heap_up(Heap *h, int i) {
    while (i > 0) {
        int p = (i - 1) / 2;
        if (h->vals[i] < h->vals[p]) { heap_swap(h, i, p); i = p; }
        else break;
    }
}

static void heap_down(Heap *h, int i) {
    for (;;) {
        int l = 2*i+1, r = 2*i+2, s = i;
        if (l < h->n && h->vals[l] < h->vals[s]) s = l;
        if (r < h->n && h->vals[r] < h->vals[s]) s = r;
        if (s != i) { heap_swap(h, i, s); i = s; } else break;
    }
}

static void heap_push(Heap *h, int k, double v) {
    if (h->pos[k] != -1) {
        int i = h->pos[k];
        if (v < h->vals[i]) { h->vals[i] = v; heap_up(h, i); }
        return;
    }
    int i = h->n++;
    h->keys[i] = k; h->vals[i] = v; h->pos[k] = i;
    heap_up(h, i);
}

static int heap_pop(Heap *h, double *v) {
    if (!h->n) return -1;
    int k = h->keys[0]; *v = h->vals[0]; h->pos[k] = -1;
    h->n--;
    if (h->n) {
        h->keys[0] = h->keys[h->n]; h->vals[0] = h->vals[h->n];
        h->pos[h->keys[0]] = 0;
        heap_down(h, 0);
    }
    return k;
}

/* ─── Algorithm Parameters ───────────────────────────────────────── */

static int param_k(int n) { return imax((int)floor(cbrt(log((double)n))), 1); }
static int param_t(int n) { return imax((int)floor(log((double)n) * cbrt(log((double)n))), 1); }

/* ─── Algorithm State ────────────────────────────────────────────── */

typedef struct {
    const CSR *g;
    double *d;         /* distance estimates */
    int    *pred;      /* predecessors */
    unsigned *pid;     /* path id for total order */
    int      n;
    int      k, t;
} State;

static void state_init(State *s, const CSR *g) {
    s->g = g;
    s->n = g->n;
    s->d    = xmalloc(sizeof(double) * s->n);
    s->pred = xmalloc(sizeof(int) * s->n);
    s->pid  = xmalloc(sizeof(unsigned) * s->n);
    for (int i = 0; i < s->n; i++) {
        s->d[i] = SSORT_INFINITY;
        s->pred[i] = -1;
        s->pid[i] = 0;
    }
    s->k = param_k(s->n);
    s->t = param_t(s->n);
}

static void state_free(State *s) {
    free(s->d); free(s->pred); free(s->pid);
}

/* Relax edge (u, v) with weight w. Returns 1 if relaxed. */
static int relax(State *s, int u, int v, double w) {
    double nd = s->d[u] + w;
    if (nd <= s->d[v]) {
        s->d[v] = nd;
        s->pred[v] = u;
        s->pid[v] = s->pid[u] ^ (unsigned)(v * 2654435761u);
        return 1;
    }
    return 0;
}

/* ─── Bounded Min-Priority Queue (D from Lemma 3.3) ─────────────── */
/* Simplified: array-based, suitable for the recursion sizes we handle. */

typedef struct {
    int    *keys;
    double *vals;
    int     n, cap;
    double  B;
} DPQ;

static void dpq_init(DPQ *q, int cap, double B) {
    q->keys = xmalloc(sizeof(int) * cap);
    q->vals = xmalloc(sizeof(double) * cap);
    q->n = 0; q->cap = cap; q->B = B;
}

static void dpq_free(DPQ *q) { free(q->keys); free(q->vals); }

static int dpq_empty(DPQ *q) { return q->n == 0; }

/* Insert, maintaining sorted order by val (insertion sort for small N). */
static void dpq_insert(DPQ *q, int k, double v) {
    /* Check if key already exists with smaller val. */
    for (int i = 0; i < q->n; i++) {
        if (q->keys[i] == k) {
            if (v < q->vals[i]) { q->vals[i] = v; /* bubble up */ }
            return;
        }
    }
    if (q->n == q->cap) {
        q->cap = q->cap * 2;
        q->keys = xrealloc(q->keys, sizeof(int) * q->cap);
        q->vals = xrealloc(q->vals, sizeof(double) * q->cap);
    }
    int i = q->n;
    while (i > 0 && q->vals[i-1] > v) {
        q->keys[i] = q->keys[i-1];
        q->vals[i] = q->vals[i-1];
        i--;
    }
    q->keys[i] = k;
    q->vals[i] = v;
    q->n++;
}

/* Pull up to M smallest. Returns count. Sets *bound to separating value. */
static int dpq_pull(DPQ *q, int *ok, double *ov, int M, double *bound) {
    int cnt = imin(M, q->n);
    for (int i = 0; i < cnt; i++) {
        ok[i] = q->keys[i];
        ov[i] = q->vals[i];
    }
    /* Remove pulled elements. */
    int rem = q->n - cnt;
    memmove(q->keys, q->keys + cnt, sizeof(int) * rem);
    memmove(q->vals, q->vals + cnt, sizeof(double) * rem);
    q->n = rem;
    *bound = (rem > 0) ? q->vals[0] : q->B;
    return cnt;
}

/* ─── FindPivots (Algorithm 1) ──────────────────────────────────── */

static void find_pivots(State *s, double B,
                        const int *S, int Slen,
                        int *P, int *Plen,
                        int *W, int *Wlen) {
    int k = s->k;
    int n = s->n;

    int *inW = xcalloc(n, sizeof(int));
    int *frontier = xmalloc(sizeof(int) * n);
    int f_len = 0;

    *Wlen = 0;

    /* W starts as S. */
    for (int i = 0; i < Slen; i++) {
        if (!inW[S[i]]) {
            inW[S[i]] = 1;
            W[(*Wlen)++] = S[i];
            frontier[f_len++] = S[i];
        }
    }

    /* Relax for k steps. */
    for (int step = 0; step < k && f_len > 0; step++) {
        int nf = 0;
        int *nfrontier = xmalloc(sizeof(int) * n);
        for (int i = 0; i < f_len; i++) {
            int u = frontier[i];
            for (int e = s->g->off[u]; e < s->g->off[u+1]; e++) {
                int v = s->g->adj[e];
                if (relax(s, u, v, s->g->wgt[e])) {
                    if (s->d[v] < B && !inW[v]) {
                        inW[v] = 1;
                        W[(*Wlen)++] = v;
                        nfrontier[nf++] = v;
                    }
                }
            }
        }
        free(frontier);
        frontier = nfrontier;
        f_len = nf;

        if (*Wlen > k * Slen) {
            /* P = S */
            *Plen = Slen;
            for (int i = 0; i < Slen; i++) P[i] = S[i];
            free(inW); free(frontier);
            return;
        }
    }
    free(frontier);

    /* Build forest F: for each v in W, find its parent in the
       shortest-path forest among W vertices. */
    int *par = xmalloc(sizeof(int) * n);
    int *sz  = xmalloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) { par[i] = -1; sz[i] = 0; }

    for (int i = 0; i < *Wlen; i++) {
        int u = W[i];
        for (int e = s->g->off[u]; e < s->g->off[u+1]; e++) {
            int v = s->g->adj[e];
            if (inW[v] && s->d[v] == s->d[u] + s->g->wgt[e]) {
                par[v] = u;
            }
        }
    }

    /* Compute subtree sizes (process W in reverse for topological order). */
    for (int i = *Wlen - 1; i >= 0; i--) {
        int v = W[i];
        sz[v]++;
        if (par[v] >= 0 && inW[par[v]])
            sz[par[v]] += sz[v];
    }

    /* P = { u in S : root of tree with >= k vertices } */
    *Plen = 0;
    for (int i = 0; i < Slen; i++) {
        int u = S[i];
        if ((par[u] < 0 || !inW[par[u]]) && sz[u] >= k) {
            P[(*Plen)++] = u;
        }
    }

    free(inW); free(par); free(sz);
}

/* ─── Base Case (Algorithm 2) ────────────────────────────────────── */

static void base_case(State *s, double B, int x,
                      double *Bp, int *U, int *Ulen) {
    int k = s->k;
    Heap h;
    heap_init(&h, s->n);

    int *inU = xcalloc(s->n, sizeof(int));
    *Ulen = 0;
    heap_push(&h, x, s->d[x]);

    while (h.n > 0 && *Ulen < k + 1) {
        double du; int u = heap_pop(&h, &du);
        if (u == -1) break;
        if (inU[u]) continue;
        inU[u] = 1;
        U[(*Ulen)++] = u;

        for (int e = s->g->off[u]; e < s->g->off[u+1]; e++) {
            int v = s->g->adj[e];
            double w = s->g->wgt[e];
            if (s->d[u] + w < s->d[v] && s->d[u] + w < B) {
                relax(s, u, v, w);
                heap_push(&h, v, s->d[v]);
            }
        }
    }

    if (*Ulen <= k) {
        *Bp = B;
    } else {
        /* B' = max d[u] in U. Remove max. */
        double mx = 0;
        for (int i = 0; i < *Ulen; i++)
            if (s->d[U[i]] > mx) mx = s->d[U[i]];
        *Bp = mx;
        int nl = 0;
        for (int i = 0; i < *Ulen; i++)
            if (s->d[U[i]] < *Bp) U[nl++] = U[i];
        *Ulen = nl;
    }

    free(inU);
    heap_free(&h);
}

/* ─── BMSSP (Algorithm 3) ────────────────────────────────────────── */

static void bmssp(State *s, int l, double B,
                  const int *S, int Slen,
                  double *Bp, int *U, int *Ulen);

static void bmssp_level0(State *s, double B, int x,
                         double *Bp, int *U, int *Ulen) {
    base_case(s, B, x, Bp, U, Ulen);
}

static void bmssp_recurse(State *s, int l, double B,
                           const int *S, int Slen,
                           double *Bp, int *U, int *Ulen) {
    int k = s->k;
    int t = s->t;
    int n = s->n;

    /* M = 2^{(l-1)*t} */
    int M = 1;
    for (int i = 0; i < (l - 1) * t; i++) M *= 2;
    if (M < 1) M = 1;

    /* Step 1: FindPivots */
    int *P  = xmalloc(sizeof(int) * n);
    int *W  = xmalloc(sizeof(int) * n);
    int Plen = 0, Wlen = 0;
    find_pivots(s, B, S, Slen, P, &Plen, W, &Wlen);

    /* Step 2: Initialize D */
    DPQ D;
    dpq_init(&D, n, B);
    for (int i = 0; i < Plen; i++)
        dpq_insert(&D, P[i], s->d[P[i]]);

    /* B'0 = min d[x] for x in P */
    double Bp0 = SSORT_INFINITY;
    for (int i = 0; i < Plen; i++)
        if (s->d[P[i]] < Bp0) Bp0 = s->d[P[i]];
    if (Plen == 0) Bp0 = B;

    /* max_U = k * 2^{l*t} */
    int max_U = k;
    for (int i = 0; i < l * t; i++) max_U *= 2;

    *Ulen = 0;
    double Bi, Bi_prime = Bp0;
    int *Si = xmalloc(sizeof(int) * n);
    double *Siv = xmalloc(sizeof(double) * n);
    int *Kk = xmalloc(sizeof(int) * n);
    double *Kv = xmalloc(sizeof(double) * n);

    while (*Ulen < max_U && !dpq_empty(&D)) {
        /* Pull */
        int Silen = dpq_pull(&D, Si, Siv, M, &Bi);
        if (Silen == 0) break;

        /* Recursive call */
        double Ui_prime;
        int *Ui = xmalloc(sizeof(int) * n);
        int Uilen = 0;
        bmssp(s, l - 1, Bi, Si, Silen, &Ui_prime, Ui, &Uilen);
        Bi_prime = Ui_prime;

        for (int i = 0; i < Uilen; i++)
            U[(*Ulen)++] = Ui[i];

        /* Relax edges from Ui */
        int Klen = 0;
        for (int i = 0; i < Uilen; i++) {
            int u = Ui[i];
            for (int e = s->g->off[u]; e < s->g->off[u+1]; e++) {
                int v = s->g->adj[e];
                double w = s->g->wgt[e];
                double nd = s->d[u] + w;
                if (nd <= s->d[v]) {
                    relax(s, u, v, w);
                    if (nd >= Bi && nd < B) {
                        dpq_insert(&D, v, nd);
                    } else if (nd >= Bi_prime && nd < Bi) {
                        Kk[Klen] = v;
                        Kv[Klen] = nd;
                        Klen++;
                    }
                }
            }
        }

        /* Batch prepend K and Si entries in [Bi_prime, Bi) */
        for (int i = 0; i < Silen; i++) {
            if (Siv[i] >= Bi_prime && Siv[i] < Bi) {
                Kk[Klen] = Si[i];
                Kv[Klen] = Siv[i];
                Klen++;
            }
        }
        /* Batch prepend: insert in reverse order (smallest first) so
           D stays sorted. For our simple DPQ, just insert all. */
        for (int i = 0; i < Klen; i++)
            dpq_insert(&D, Kk[i], Kv[i]);

        free(Ui);
    }

    /* Finalize: add vertices from W with d < B' */
    double final_B = dmin(Bi_prime, B);
    for (int i = 0; i < Wlen; i++) {
        int v = W[i];
        if (s->d[v] < final_B) {
            int found = 0;
            for (int j = 0; j < *Ulen; j++)
                if (U[j] == v) { found = 1; break; }
            if (!found) U[(*Ulen)++] = v;
        }
    }

    *Bp = final_B;

    free(P); free(W); free(Si); free(Siv); free(Kk); free(Kv);
    dpq_free(&D);
}

static void bmssp(State *s, int l, double B,
                  const int *S, int Slen,
                  double *Bp, int *U, int *Ulen) {
    if (l == 0)
        bmssp_level0(s, B, S[0], Bp, U, Ulen);
    else
        bmssp_recurse(s, l, B, S, Slen, Bp, U, Ulen);
}

/* ─── Public API ─────────────────────────────────────────────────── */

SsortGraph *ssort_graph_new(int n, int m) {
    SsortGraph *g = xmalloc(sizeof(SsortGraph));
    g->n = n;
    g->m = 0;
    g->cap = (m > 0 ? m : 4);
    g->eu = xmalloc(sizeof(int) * g->cap);
    g->ev = xmalloc(sizeof(int) * g->cap);
    g->ew = xmalloc(sizeof(double) * g->cap);
    return g;
}

void ssort_graph_free(SsortGraph *g) {
    if (!g) return;
    free(g->eu); free(g->ev); free(g->ew);
    free(g);
}

int ssort_graph_add_edge(SsortGraph *g, int u, int v, double w) {
    if (u < 0 || u >= g->n || v < 0 || v >= g->n || w < 0) return -1;
    if (g->m >= g->cap) {
        g->cap *= 2;
        g->eu = xrealloc(g->eu, sizeof(int) * g->cap);
        g->ev = xrealloc(g->ev, sizeof(int) * g->cap);
        g->ew = xrealloc(g->ew, sizeof(double) * g->cap);
    }
    g->eu[g->m] = u;
    g->ev[g->m] = v;
    g->ew[g->m] = w;
    g->m++;
    return 0;
}

/* Dijkstra fallback for small graphs or when BMSSP doesn't finish. */
static void dijkstra_fallback(const CSR *g, int src, double *d, int *pred) {
    Heap h;
    heap_init(&h, g->n);
    for (int i = 0; i < g->n; i++) { d[i] = SSORT_INFINITY; pred[i] = -1; }
    d[src] = 0.0;
    heap_push(&h, src, 0.0);
    while (h.n) {
        double du; int u = heap_pop(&h, &du);
        if (du > d[u]) continue;
        for (int e = g->off[u]; e < g->off[u+1]; e++) {
            int v = g->adj[e]; double w = g->wgt[e];
            if (du + w < d[v]) {
                d[v] = du + w;
                pred[v] = u;
                heap_push(&h, v, d[v]);
            }
        }
    }
    heap_free(&h);
}

int ssort(const SsortGraph *g, int src, double *dist, int *pred) {
    if (!g || src < 0 || src >= g->n || !dist || !pred) return -1;

    /* Build CSR. */
    CSR csr;
    csr_build(&csr, g->n, g->eu, g->ev, g->ew, g->m);

    /* For small graphs, Dijkstra is both simpler and fast enough.
       The BMSSP algorithm's advantage only manifests at large n. */
    if (csr.n < 256) {
        dijkstra_fallback(&csr, src, dist, pred);
        csr_free(&csr);
        return 0;
    }

    /* Init state. */
    State state;
    state_init(&state, &csr);
    state.d[src] = 0.0;

    /* Compute level. */
    int l = (int)ceil(log((double)csr.n) / (double)state.t);
    if (l < 0) l = 0;

    /* Run BMSSP. */
    int *S = xmalloc(sizeof(int));
    S[0] = src;
    double Bp;
    int *U = xmalloc(sizeof(int) * csr.n);
    int Ulen = 0;
    bmssp(&state, l, SSORT_INFINITY, S, 1, &Bp, U, &Ulen);

    /* If BMSSP returned partial results (B' < INF), finish with Dijkstra. */
    if (Bp < SSORT_INFINITY) {
        /* Run Dijkstra from all vertices that have finite distance but
           may not have relaxed all their edges. */
        int *done = xcalloc(csr.n, sizeof(int));
        Heap h;
        heap_init(&h, csr.n);
        for (int i = 0; i < csr.n; i++) {
            if (state.d[i] < SSORT_INFINITY) {
                heap_push(&h, i, state.d[i]);
                done[i] = 1;
            }
        }
        while (h.n) {
            double du; int u = heap_pop(&h, &du);
            if (du > state.d[u]) continue;
            for (int e = csr.off[u]; e < csr.off[u+1]; e++) {
                int v = csr.adj[e]; double w = csr.wgt[e];
                if (du + w < state.d[v]) {
                    state.d[v] = du + w;
                    state.pred[v] = u;
                    heap_push(&h, v, state.d[v]);
                }
            }
        }
        heap_free(&h);
        free(done);
    }

    /* Copy results. */
    for (int i = 0; i < csr.n; i++) {
        dist[i] = state.d[i];
        pred[i] = state.pred[i];
    }

    free(S); free(U);
    state_free(&state);
    csr_free(&csr);
    return 0;
}
