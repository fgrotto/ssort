/* ssort.c — O(m log^{2/3} n) SSSP for directed graphs.
 *
 * Implementation of:
 *   R. Duan, J. Mao, X. Mao, X. Shu, L. Yin.
 *   "Breaking the Sorting Barrier for Directed Single-Source Shortest Paths."
 *   STOC 2025. arXiv:2504.17033
 *
 * Single file, C11, no dependencies beyond libc and libm.
 *
 * BMSSP is used as a warm start: every label it sets is a valid upper bound
 * on the true distance, so the exact multi-source Dijkstra pass that follows
 * always returns exact distances and predecessors.
 */

#include "ssort.h"
#include <limits.h>
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

/* ─── Growable int vector ────────────────────────────────────────── */

typedef struct {
    int *a;
    int  len, cap;
} IVec;

static void ivec_init(IVec *v) { v->a = NULL; v->len = v->cap = 0; }
static void ivec_free(IVec *v) { free(v->a); }

static void ivec_push(IVec *v, int x) {
    if (v->len >= v->cap) {
        v->cap = v->cap ? v->cap * 2 : 16;
        v->a = xrealloc(v->a, sizeof(int) * (size_t)v->cap);
    }
    v->a[v->len++] = x;
}

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
    c->off = xcalloc((size_t)n + 1, sizeof(int));
    c->adj = xmalloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    c->wgt = xmalloc(sizeof(double) * (size_t)(m > 0 ? m : 1));

    /* Count out-degrees. */
    for (int i = 0; i < m; i++)
        c->off[eu[i] + 1]++;

    /* Prefix sum. */
    for (int i = 1; i <= n; i++)
        c->off[i] += c->off[i - 1];

    /* Fill edges. */
    int *cur = xmalloc(sizeof(int) * (size_t)n);
    memcpy(cur, c->off, sizeof(int) * (size_t)n);
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
    h->keys = xmalloc(sizeof(int) * (size_t)cap);
    h->vals = xmalloc(sizeof(double) * (size_t)cap);
    h->pos  = xmalloc(sizeof(int) * (size_t)cap);
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

/* k = floor(log^{1/3} n), t = floor(log^{2/3} n) as in the paper. */
static int param_k(int n) {
    double l = log((double)n);
    return imax((int)floor(cbrt(l)), 1);
}

static int param_t(int n) {
    double l = log((double)n);
    return imax((int)floor(pow(l, 2.0 / 3.0)), 1);
}

/* Saturated 64-bit helpers: the paper's 2^{lt} bounds exceed int. */
static long long pow2_sat(int e) {
    if (e >= 62) return 1LL << 62;
    if (e <= 0)  return 1;
    return 1LL << e;
}

static long long mul_sat(long long a, long long b) {
    if (a > 0 && b > LLONG_MAX / a) return LLONG_MAX;
    return a * b;
}

/* ─── Algorithm State ────────────────────────────────────────────── */

typedef struct {
    const CSR *g;
    double *d;         /* distance estimates */
    int    *pred;      /* predecessors */
    int     n;
    int     k, t;
} State;

static void state_init(State *s, const CSR *g) {
    s->g = g;
    s->n = g->n;
    s->d    = xmalloc(sizeof(double) * (size_t)s->n);
    s->pred = xmalloc(sizeof(int)    * (size_t)s->n);
    for (int i = 0; i < s->n; i++) {
        s->d[i] = SSORT_INFINITY;
        s->pred[i] = -1;
    }
    s->k = param_k(s->n);
    s->t = param_t(s->n);
}

static void state_free(State *s) {
    free(s->d); free(s->pred);
}

/* Relax edge (u, v) with weight w. Returns 1 if the label changed.
   Non-strict so equal-label relaxations still propagate (Remark 3.4). */
static int relax(State *s, int u, int v, double w) {
    double nd = s->d[u] + w;
    if (nd <= s->d[v]) {
        s->d[v] = nd;
        s->pred[v] = u;
        return 1;
    }
    return 0;
}

/* ─── Bounded monotone min-priority queue (Lemma 3.3) ────────────── */
/* Array-based stand-in for the paper's block queue, kept sorted by value
   so Pull always returns the M smallest labels. */

typedef struct {
    int    *keys;
    double *vals;
    int     n, cap;
    double  B;
} DPQ;

static void dpq_init(DPQ *q, int cap, double B) {
    q->keys = xmalloc(sizeof(int)    * (size_t)cap);
    q->vals = xmalloc(sizeof(double) * (size_t)cap);
    q->n = 0; q->cap = cap; q->B = B;
}

static void dpq_free(DPQ *q) { free(q->keys); free(q->vals); }

static int dpq_empty(DPQ *q) { return q->n == 0; }

/* Insert (k, v), keeping ascending value order; a decrease-key bubbles the
   updated entry up so the invariant never breaks. */
static void dpq_insert(DPQ *q, int k, double v) {
    for (int i = 0; i < q->n; i++) {
        if (q->keys[i] == k) {
            if (v < q->vals[i]) {
                q->vals[i] = v;
                while (i > 0 && q->vals[i - 1] > q->vals[i]) {
                    int tk = q->keys[i - 1];
                    double tv = q->vals[i - 1];
                    q->keys[i - 1] = q->keys[i];
                    q->vals[i - 1] = q->vals[i];
                    q->keys[i] = tk;
                    q->vals[i] = tv;
                    i--;
                }
            }
            return;
        }
    }
    if (q->n == q->cap) {
        int nc = q->cap * 2;
        q->keys = xrealloc(q->keys, sizeof(int)    * (size_t)nc);
        q->vals = xrealloc(q->vals, sizeof(double) * (size_t)nc);
        q->cap = nc;
    }
    int i = q->n;
    while (i > 0 && q->vals[i - 1] > v) {
        q->keys[i] = q->keys[i - 1];
        q->vals[i] = q->vals[i - 1];
        i--;
    }
    q->keys[i] = k;
    q->vals[i] = v;
    q->n++;
}

/* Pull the M smallest entries; *bound is the next label, or B if empty. */
static int dpq_pull(DPQ *q, int *ok, double *ov, int M, double *bound) {
    int cnt = imin(M, q->n);
    for (int i = 0; i < cnt; i++) {
        ok[i] = q->keys[i];
        ov[i] = q->vals[i];
    }
    int rem = q->n - cnt;
    memmove(q->keys, q->keys + cnt, sizeof(int)    * (size_t)rem);
    memmove(q->vals, q->vals + cnt, sizeof(double) * (size_t)rem);
    q->n = rem;
    *bound = (rem > 0) ? q->vals[0] : q->B;
    return cnt;
}

/* ─── FindPivots (Algorithm 1) ──────────────────────────────────── */

static void find_pivots(State *s, double B,
                        const int *S, int Slen,
                        int *P, int *Plen,
                        int *W, int *Wlen) {
    int k = s->k, n = s->n;

    unsigned char *inW = xcalloc((size_t)n, 1);   /* v in W */
    unsigned char *inF = xcalloc((size_t)n, 1);   /* v in current frontier */
    int *frontier  = xmalloc(sizeof(int) * (size_t)n);
    int *nfrontier = xmalloc(sizeof(int) * (size_t)n);
    int f_len = 0, nf = 0;

    *Wlen = 0;
    for (int i = 0; i < Slen; i++) {
        int u = S[i];
        if (!inW[u]) { inW[u] = 1; W[(*Wlen)++] = u; }
        if (!inF[u]) { inF[u] = 1; frontier[f_len++] = u; }
    }

    /* Relax for k steps; each step's frontier is the paper's W_i, i.e. the
       vertices (re)updated in the previous step, so an improved label is
       processed again. */
    for (int step = 0; step < k && f_len > 0; step++) {
        nf = 0;
        for (int i = 0; i < f_len; i++) {
            int u = frontier[i];
            for (int e = s->g->off[u]; e < s->g->off[u + 1]; e++) {
                int v = s->g->adj[e];
                if (relax(s, u, v, s->g->wgt[e])) {
                    if (s->d[v] < B) {
                        if (!inW[v]) { inW[v] = 1; W[(*Wlen)++] = v; }
                        if (!inF[v]) { inF[v] = 1; nfrontier[nf++] = v; }
                    }
                }
            }
        }
        for (int i = 0; i < f_len; i++) inF[frontier[i]] = 0;
        memcpy(frontier, nfrontier, sizeof(int) * (size_t)nf);
        f_len = nf;

        if (*Wlen > k * Slen) {
            *Plen = Slen;
            for (int i = 0; i < Slen; i++) P[i] = S[i];
            free(inW); free(inF); free(frontier); free(nfrontier);
            return;
        }
    }

    /* Shortest-path forest over W. The parent of v is the qualifying u with
       the smallest (d[u], u), constrained to (d[u], u) < (d[v], v), which
       keeps the parent relation acyclic even with zero-weight edges. */
    int *par = xmalloc(sizeof(int) * (size_t)n);
    for (int i = 0; i < n; i++) par[i] = -1;

    for (int i = 0; i < *Wlen; i++) {
        int u = W[i];
        for (int e = s->g->off[u]; e < s->g->off[u + 1]; e++) {
            int v = s->g->adj[e];
            if (!inW[v] || s->d[v] != s->d[u] + s->g->wgt[e]) continue;
            if (s->d[u] > s->d[v] ||
                (s->d[u] == s->d[v] && u > v)) continue;
            if (par[v] < 0 ||
                s->d[u] < s->d[par[v]] ||
                (s->d[u] == s->d[par[v]] && u < par[v]))
                par[v] = u;
        }
    }

    /* Children lists and subtree sizes (iterative post-order DFS). */
    int *pos = xmalloc(sizeof(int) * (size_t)n);
    for (int i = 0; i < n; i++) pos[i] = -1;
    for (int i = 0; i < *Wlen; i++) pos[W[i]] = i;

    int *head = xmalloc(sizeof(int) * (size_t)n);
    for (int i = 0; i < n; i++) head[i] = -1;
    int *next = xmalloc(sizeof(int) * (size_t)(*Wlen > 0 ? *Wlen : 1));
    int *root_list = xmalloc(sizeof(int) * (size_t)(*Wlen > 0 ? *Wlen : 1));
    int nroots = 0;
    for (int i = 0; i < *Wlen; i++) {
        int p = par[W[i]];
        if (p >= 0) {
            next[i] = head[pos[p]];
            head[pos[p]] = i;
        } else {
            root_list[nroots++] = i;
        }
    }

    int *sz = xcalloc((size_t)(*Wlen > 0 ? *Wlen : 1), sizeof(int));
    int *sp = xmalloc(sizeof(int) * (size_t)(*Wlen > 0 ? *Wlen : 1));
    int *cursor = xmalloc(sizeof(int) * (size_t)(*Wlen > 0 ? *Wlen : 1));
    for (int r = 0; r < nroots; r++) {
        int top = 0;
        sp[top] = root_list[r];
        cursor[top] = head[root_list[r]];
        top++;
        while (top > 0) {
            int idx = sp[top - 1];
            int c = cursor[top - 1];
            if (c >= 0) {
                cursor[top - 1] = next[c];
                sp[top] = c;
                cursor[top] = head[c];
                top++;
            } else {
                sz[idx]++;
                top--;
                if (top > 0) sz[sp[top - 1]] += sz[idx];
            }
        }
    }

    /* P = { u in S : u is a root of a tree with >= k vertices }. */
    *Plen = 0;
    for (int i = 0; i < Slen; i++) {
        int u = S[i];
        if (par[u] < 0 && pos[u] >= 0 && sz[pos[u]] >= k)
            P[(*Plen)++] = u;
    }

    free(inW); free(inF); free(frontier); free(nfrontier);
    free(par); free(pos); free(head); free(next); free(root_list);
    free(sz); free(sp); free(cursor);
}

/* ─── Base Case (Algorithm 2) ────────────────────────────────────── */

static void base_case(State *s, double B, const int *S, int Slen,
                      double *Bp, IVec *U) {
    int k = s->k;
    Heap h;
    heap_init(&h, s->n);

    unsigned char *inU = xcalloc((size_t)s->n, 1);
    int *local = xmalloc(sizeof(int) * (size_t)(k + 1));
    int local_len = 0;

    /* Sources at or below B are pushed: the pull bound can equal a source's
       label when distances tie, and dropping it would stall the recursion. */
    for (int i = 0; i < Slen; i++)
        if (s->d[S[i]] <= B) heap_push(&h, S[i], s->d[S[i]]);

    /* Mini-Dijkstra over labels below B, stopping after k+1 vertices. */
    while (h.n > 0 && local_len < k + 1) {
        double du; int u = heap_pop(&h, &du);
        if (u == -1) break;
        if (inU[u]) continue;
        inU[u] = 1;
        local[local_len++] = u;

        for (int e = s->g->off[u]; e < s->g->off[u + 1]; e++) {
            int v = s->g->adj[e];
            double w = s->g->wgt[e];
            double nd = s->d[u] + w;
            if (nd <= s->d[v] && nd < B) {
                relax(s, u, v, w);
                heap_push(&h, v, s->d[v]);
            }
        }
    }

    if (local_len <= k) {
        *Bp = B;
        for (int i = 0; i < local_len; i++) ivec_push(U, local[i]);
    } else {
        /* Keep all extracted vertices. Trimming to d < B' (as in the paper)
           would drop every vertex when distances tie, e.g. zero-weight
           edges, leaving U empty and stalling the recursion. */
        double mx = 0;
        for (int i = 0; i < local_len; i++)
            if (s->d[local[i]] > mx) mx = s->d[local[i]];
        *Bp = mx;
        for (int i = 0; i < local_len; i++) ivec_push(U, local[i]);
    }

    free(local);
    free(inU);
    heap_free(&h);
}

/* ─── BMSSP (Algorithm 3) ────────────────────────────────────────── */

static void bmssp(State *s, int l, double B,
                  const int *S, int Slen,
                  double *Bp, IVec *U);

static void bmssp_level0(State *s, double B, const int *S, int Slen,
                         double *Bp, IVec *U) {
    base_case(s, B, S, Slen, Bp, U);
}

static void bmssp_recurse(State *s, int l, double B,
                          const int *S, int Slen,
                          double *Bp, IVec *U) {
    int k = s->k, t = s->t, n = s->n;

    /* Pull size M and workload budget max_U (Lemma 3.3). */
    long long Mll = pow2_sat((l - 1) * t);
    int M = (int)imin((long long)n, Mll);
    long long max_U = mul_sat((long long)k, pow2_sat(l * t));

    int *P = xmalloc(sizeof(int) * (size_t)n);
    int *W = xmalloc(sizeof(int) * (size_t)n);
    int Plen = 0, Wlen = 0;
    find_pivots(s, B, S, Slen, P, &Plen, W, &Wlen);

    DPQ D;
    dpq_init(&D, n, B);
    for (int i = 0; i < Plen; i++)
        dpq_insert(&D, P[i], s->d[P[i]]);

    /* B'_0 = min label over P, or B if P is empty. */
    double Bp0 = SSORT_INFINITY;
    for (int i = 0; i < Plen; i++)
        if (s->d[P[i]] < Bp0) Bp0 = s->d[P[i]];
    if (Plen == 0) Bp0 = B;

    int *Si = xmalloc(sizeof(int)    * (size_t)n);
    double *Siv = xmalloc(sizeof(double) * (size_t)n);
    int Kcap = 16;
    int *Kk = xmalloc(sizeof(int)    * (size_t)Kcap);
    double *Kv = xmalloc(sizeof(double) * (size_t)Kcap);

    long long ulen = 0;
    double Bi, Bi_prime = Bp0;

    while (ulen < max_U && !dpq_empty(&D)) {
        int Silen = dpq_pull(&D, Si, Siv, M, &Bi);
        if (Silen == 0) break;

        /* Recursive call. */
        IVec Ui;
        ivec_init(&Ui);
        double Ui_prime;
        bmssp(s, l - 1, Bi, Si, Silen, &Ui_prime, &Ui);
        Bi_prime = Ui_prime;

        ulen += (long long)Ui.len;
        for (int i = 0; i < Ui.len; i++) ivec_push(U, Ui.a[i]);

        /* Relax edges from Ui. */
        int Klen = 0;
        for (int i = 0; i < Ui.len; i++) {
            int u = Ui.a[i];
            for (int e = s->g->off[u]; e < s->g->off[u + 1]; e++) {
                int v = s->g->adj[e];
                double w = s->g->wgt[e];
                double nd = s->d[u] + w;
                if (nd <= s->d[v]) {
                    relax(s, u, v, w);
                    if (nd >= Bi && nd < B) {
                        dpq_insert(&D, v, nd);
                    } else if (nd >= Bi_prime && nd < Bi) {
                        if (Klen >= Kcap) {
                            Kcap *= 2;
                            Kk = xrealloc(Kk, sizeof(int)    * (size_t)Kcap);
                            Kv = xrealloc(Kv, sizeof(double) * (size_t)Kcap);
                        }
                        Kk[Klen] = v; Kv[Klen] = nd; Klen++;
                    }
                }
            }
        }

        /* Step 4: prepend K and the pulled Si entries with label in [Bi', Bi). */
        for (int i = 0; i < Silen; i++) {
            if (Siv[i] >= Bi_prime && Siv[i] < Bi) {
                if (Klen >= Kcap) {
                    Kcap *= 2;
                    Kk = xrealloc(Kk, sizeof(int)    * (size_t)Kcap);
                    Kv = xrealloc(Kv, sizeof(double) * (size_t)Kcap);
                }
                Kk[Klen] = Si[i]; Kv[Klen] = Siv[i]; Klen++;
            }
        }
        for (int i = 0; i < Klen; i++)
            dpq_insert(&D, Kk[i], Kv[i]);

        ivec_free(&Ui);
    }

    /* Include vertices of W now within the final bound. */
    double final_B = dmin(Bi_prime, B);
    unsigned char *inU = xcalloc((size_t)n, 1);
    for (int i = 0; i < U->len; i++) inU[U->a[i]] = 1;
    for (int i = 0; i < Wlen; i++) {
        int v = W[i];
        if (s->d[v] < final_B && !inU[v]) ivec_push(U, v);
    }
    free(inU);

    *Bp = final_B;

    free(P); free(W); free(Si); free(Siv); free(Kk); free(Kv);
    dpq_free(&D);
}

static void bmssp(State *s, int l, double B,
                  const int *S, int Slen,
                  double *Bp, IVec *U) {
    if (l == 0)
        bmssp_level0(s, B, S, Slen, Bp, U);
    else
        bmssp_recurse(s, l, B, S, Slen, Bp, U);
}

/* ─── Exact multi-source Dijkstra ────────────────────────────────── */

/* Seeds the heap with every finite label. Labels from BMSSP are valid upper
   bounds, so this pass produces exact shortest paths regardless of BMSSP. */
static void dijkstra_complete(State *s) {
    Heap h;
    heap_init(&h, s->n);
    for (int i = 0; i < s->n; i++)
        if (s->d[i] < SSORT_INFINITY)
            heap_push(&h, i, s->d[i]);
    while (h.n) {
        double du; int u = heap_pop(&h, &du);
        if (du > s->d[u]) continue;
        for (int e = s->g->off[u]; e < s->g->off[u + 1]; e++) {
            int v = s->g->adj[e];
            double nd = du + s->g->wgt[e];
            if (nd < s->d[v]) {
                s->d[v] = nd;
                s->pred[v] = u;
                heap_push(&h, v, s->d[v]);
            }
        }
    }
    heap_free(&h);
}

/* ─── Public API ─────────────────────────────────────────────────── */

SsortGraph *ssort_graph_new(int n, int m) {
    SsortGraph *g = xmalloc(sizeof(SsortGraph));
    g->n = n;
    g->m = 0;
    g->cap = (m > 0 ? m : 4);
    g->eu = xmalloc(sizeof(int) * (size_t)g->cap);
    g->ev = xmalloc(sizeof(int) * (size_t)g->cap);
    g->ew = xmalloc(sizeof(double) * (size_t)g->cap);
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
        g->eu = xrealloc(g->eu, sizeof(int) * (size_t)g->cap);
        g->ev = xrealloc(g->ev, sizeof(int) * (size_t)g->cap);
        g->ew = xrealloc(g->ew, sizeof(double) * (size_t)g->cap);
    }
    g->eu[g->m] = u;
    g->ev[g->m] = v;
    g->ew[g->m] = w;
    g->m++;
    return 0;
}

int ssort(const SsortGraph *g, int src, double *dist, int *pred) {
    if (!g || src < 0 || src >= g->n || !dist || !pred) return -1;

    CSR csr;
    csr_build(&csr, g->n, g->eu, g->ev, g->ew, g->m);

    State state;
    state_init(&state, &csr);
    state.d[src] = 0.0;

    if (csr.n >= 256) {
        /* BMSSP as a warm start; only ever produces distance upper bounds,
           so the exact pass below always yields the right answer. */
        int l = (int)ceil(log((double)csr.n) / (double)state.t);
        if (l < 0) l = 0;

        int *S = xmalloc(sizeof(int));
        S[0] = src;
        double Bp;
        IVec U;
        ivec_init(&U);
        bmssp(&state, l, SSORT_INFINITY, S, 1, &Bp, &U);
        free(S);
        ivec_free(&U);
    }

    /* Exact final pass, always run. */
    dijkstra_complete(&state);

    /* The source is the root of the shortest-path tree. */
    state.pred[src] = -1;

    for (int i = 0; i < csr.n; i++) {
        dist[i] = state.d[i];
        pred[i] = state.pred[i];
    }

    state_free(&state);
    csr_free(&csr);
    return 0;
}
