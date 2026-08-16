/* ssort.c - O(m log^{2/3} n) SSSP for directed graphs.
 *
 * Implementation of:
 *   R. Duan, J. Mao, X. Mao, X. Shu, L. Yin.
 *   "Breaking the Sorting Barrier for Directed Single-Source Shortest Paths."
 *   STOC 2025. arXiv:2504.17033
 *
 * Single file, C11, no dependencies beyond libc and libm.
 *
 * The algorithm is run end-to-end on the constant-degree transformed graph
 * and is exact: the returned U equals T_{<B}(S) and is complete, so no
 * final Dijkstra pass is needed.
 */

#include "ssort.h"
#include <limits.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>

/* --- Utilities ------------------------------------------------------ */

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

static int cmp_int(const void *a, const void *b) {
    int x = *(const int *)a, y = *(const int *)b;
    return (x > y) - (x < y);
}

/* Total-order label of a vertex: (length, #vertices, endpoint id).
   For labels of two distinct vertices the reversed vertex sequences first
   differ at the last vertex (the endpoint), so comparing (len, cnt, id)
   decides. */
typedef struct {
    double len;
    int    cnt;
    int    id;
} Lab;

#define LAB_INF ((Lab){SSORT_INFINITY, INT_MAX, INT_MAX})

static int lab_cmp(const Lab *a, const Lab *b) {
    if (a->len < b->len) return -1;
    if (a->len > b->len) return  1;
    if (a->cnt < b->cnt) return -1;
    if (a->cnt > b->cnt) return  1;
    if (a->id  < b->id)  return -1;
    if (a->id  > b->id)  return  1;
    return 0;
}

static int lab_lt(const Lab *a, const Lab *b) { return lab_cmp(a, b) < 0; }
static int lab_le(const Lab *a, const Lab *b) { return lab_cmp(a, b) <= 0; }
static int lab_ge(const Lab *a, const Lab *b) { return lab_cmp(a, b) >= 0; }

/* --- Growable int vector -------------------------------------------- */

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

/* --- CSR Graph (built from edge list) ------------------------------- */

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

/* --- Constant-Degree Transform ---------------------------------------
 * Replace each original vertex v with a zero-weight cycle of vertices
 * x_{v,w}, one per distinct in/out neighbor w.  For every edge (u,v) of
 * weight w_uv add the edge x_{u,v} -> x_{v,u} of weight w_uv.  Every
 * vertex of the transformed graph then has in/out degree at most 2,
 * n' = O(m), m' = O(m), and distances are preserved: dist[v] equals the
 * distance of any cycle vertex of v (the cycles are zero-weight).
 */

typedef struct {
    CSR  c;          /* transformed graph G' */
    int *canon;      /* [n] original vertex v -> first cycle vertex x_{v,*} (or -1) */
    int *nb_s;       /* [n] slice start into nb_list of sorted distinct neighbors */
    int *nb_len;     /* [n] slice length (distinct neighbor count) */
    int *nb_list;    /* sorted distinct neighbors, concatenated per vertex */
    int *cyc_by_nb;  /* [sum nb_len] neighbor-list entry -> cycle vertex id */
} Transform;

static int transform_cycle_vertex(const Transform *tr, int v, int w);

static void transform_build(const CSR *g, int n, Transform *tr) {
    /* Raw neighbor lists: each edge (u,v) contributes v to u and u to v. */
    int *deg = xcalloc((size_t)n, sizeof(int));
    for (int u = 0; u < n; u++)
        for (int e = g->off[u]; e < g->off[u + 1]; e++) {
            deg[u]++;
            deg[g->adj[e]]++;
        }
    long long tot = 0;
    for (int v = 0; v < n; v++) tot += deg[v];

    int *nb_start = xcalloc((size_t)n + 1, sizeof(int));
    for (int v = 0; v < n; v++) nb_start[v + 1] = nb_start[v] + deg[v];

    int *nbuf = xmalloc(sizeof(int) * (size_t)tot);
    int *cur = xmalloc(sizeof(int) * (size_t)n);
    memcpy(cur, nb_start, sizeof(int) * (size_t)n);
    for (int u = 0; u < n; u++)
        for (int e = g->off[u]; e < g->off[u + 1]; e++) {
            int v = g->adj[e];
            nbuf[cur[u]++] = v;
            nbuf[cur[v]++] = u;
        }
    free(cur);

    /* Sort and dedup each slice. */
    for (int v = 0; v < n; v++) {
        int *base = nbuf + nb_start[v];
        int cnt = deg[v];
        qsort(base, (size_t)cnt, sizeof(int), cmp_int);
        int w = 0;
        for (int i = 0; i < cnt; i++)
            if (i == 0 || base[i] != base[i - 1]) base[w++] = base[i];
        deg[v] = w;
    }

    /* Assign cycle vertex ids: v's cycle vertices are the entries of v's
       deduped neighbor list, in sorted-neighbor order. */
    int n2 = 0;
    for (int v = 0; v < n; v++) n2 += deg[v];

    tr->canon = xmalloc(sizeof(int) * (size_t)n);
    tr->nb_s = nb_start;
    tr->nb_len = deg;
    tr->nb_list = nbuf;
    tr->cyc_by_nb = xmalloc(sizeof(int) * (size_t)(tot > 0 ? tot : 1));
    int gid = 0;
    for (int v = 0; v < n; v++) {
        tr->canon[v] = deg[v] > 0 ? gid : -1;
        for (int i = 0; i < deg[v]; i++) tr->cyc_by_nb[nb_start[v] + i] = gid++;
    }

    /* Edge list of G': zero-weight cycle edges + one inter-vertex edge
       per original edge. */
    long long m2 = (long long)g->m;
    for (int v = 0; v < n; v++)
        if (deg[v] >= 2) m2 += deg[v];

    int *eu = xmalloc(sizeof(int) * (size_t)m2);
    int *ev = xmalloc(sizeof(int) * (size_t)m2);
    double *ew = xmalloc(sizeof(double) * (size_t)m2);
    int idx = 0;
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++) {
            if (deg[v] < 2) break;
            int p = (i + 1) % deg[v];
            eu[idx] = tr->cyc_by_nb[nb_start[v] + i];
            ev[idx] = tr->cyc_by_nb[nb_start[v] + p];
            ew[idx] = 0.0;
            idx++;
        }
    for (int u = 0; u < n; u++)
        for (int e = g->off[u]; e < g->off[u + 1]; e++) {
            int v = g->adj[e];
            eu[idx] = transform_cycle_vertex(tr, u, v);
            ev[idx] = transform_cycle_vertex(tr, v, u);
            ew[idx] = g->wgt[e];
            idx++;
        }
    tr->c.n = n2;
    tr->c.m = (int)m2;
    csr_build(&tr->c, n2, eu, ev, ew, (int)m2);
    free(eu); free(ev); free(ew);
}

static int transform_cycle_vertex(const Transform *tr, int v, int w) {
    /* Cycle vertex x_{v,w}: binary-search w in v's sorted neighbor list. */
    int lo = tr->nb_s[v], hi = tr->nb_s[v] + tr->nb_len[v];
    while (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        if (tr->nb_list[mid] < w) lo = mid + 1;
        else hi = mid;
    }
    return tr->cyc_by_nb[lo];
}

static void transform_free(Transform *tr) {
    csr_free(&tr->c);
    free(tr->canon);
    free(tr->nb_s);
    free(tr->nb_len);
    free(tr->nb_list);
    free(tr->cyc_by_nb);
}

/* --- Min-Heap -------------------------------------------------------- */

typedef struct {
    int    *keys;
    Lab    *vals;
    int    *pos;
    int     n, cap;
} Heap;

static void heap_init(Heap *h, int cap) {
    h->keys = xmalloc(sizeof(int) * (size_t)cap);
    h->vals = xmalloc(sizeof(Lab) * (size_t)cap);
    h->pos  = xmalloc(sizeof(int) * (size_t)cap);
    h->n = 0; h->cap = cap;
    for (int i = 0; i < cap; i++) h->pos[i] = -1;
}

static void heap_free(Heap *h) {
    free(h->keys); free(h->vals); free(h->pos);
}

static void heap_swap(Heap *h, int i, int j) {
    int tk = h->keys[i]; Lab tv = h->vals[i];
    h->keys[i] = h->keys[j]; h->vals[i] = h->vals[j];
    h->keys[j] = tk; h->vals[j] = tv;
    h->pos[h->keys[i]] = i;
    h->pos[h->keys[j]] = j;
}

static void heap_up(Heap *h, int i) {
    while (i > 0) {
        int p = (i - 1) / 2;
        if (lab_lt(&h->vals[i], &h->vals[p])) { heap_swap(h, i, p); i = p; }
        else break;
    }
}

static void heap_down(Heap *h, int i) {
    for (;;) {
        int l = 2*i+1, r = 2*i+2, s = i;
        if (l < h->n && lab_lt(&h->vals[l], &h->vals[s])) s = l;
        if (r < h->n && lab_lt(&h->vals[r], &h->vals[s])) s = r;
        if (s != i) { heap_swap(h, i, s); i = s; } else break;
    }
}

static void heap_push(Heap *h, int k, Lab v) {
    if (h->pos[k] != -1) {
        int i = h->pos[k];
        if (lab_lt(&v, &h->vals[i])) { h->vals[i] = v; heap_up(h, i); }
        return;
    }
    int i = h->n++;
    h->keys[i] = k; h->vals[i] = v; h->pos[k] = i;
    heap_up(h, i);
}

static int heap_pop(Heap *h, Lab *v) {
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

/* --- Algorithm Parameters -------------------------------------------- */

/* k = floor(log^{1/3} n), t = floor(log^{2/3} n).
   Base-2 logarithms: with l = ceil((log2 n)/t) we have l*t >= log2 n, so the
   top-level workload budget k*2^{lt} >= k*n exceeds any possible |U| and the
   top-level call is always a successful execution (U = V). */
static int param_k(int n) {
    double l = log2((double)n);
    return imax((int)floor(cbrt(l)), 1);
}

static int param_t(int n) {
    double l = log2((double)n);
    return imax((int)floor(pow(l, 2.0 / 3.0)), 1);
}

/* Saturated 64-bit helpers: the 2^{lt} bounds exceed int. */
static long long pow2_sat(int e) {
    if (e >= 62) return 1LL << 62;
    if (e <= 0)  return 1;
    return 1LL << e;
}

static long long mul_sat(long long a, long long b) {
    if (a > 0 && b > LLONG_MAX / a) return LLONG_MAX;
    return a * b;
}

/* --- Algorithm State ------------------------------------------------ */

typedef struct {
    const CSR *g;
    double *d;         /* distance estimates */
    int    *pred;      /* predecessors */
    Lab    *lab;       /* total-order labels */
    int    *cnt;       /* number of vertices on the path */
    int     n;
    int     k, t;
} State;

static void state_init(State *s, const CSR *g) {
    s->g = g;
    s->n = g->n;
    s->d    = xmalloc(sizeof(double) * (size_t)s->n);
    s->pred = xmalloc(sizeof(int)    * (size_t)s->n);
    s->lab  = xmalloc(sizeof(Lab)    * (size_t)s->n);
    s->cnt  = xmalloc(sizeof(int)    * (size_t)s->n);
    for (int i = 0; i < s->n; i++) {
        s->d[i] = SSORT_INFINITY;
        s->pred[i] = -1;
        s->lab[i] = LAB_INF;
        s->cnt[i] = 0;
    }
    s->k = param_k(s->n);
    s->t = param_t(s->n);
}

static void state_free(State *s) {
    free(s->d); free(s->pred); free(s->lab); free(s->cnt);
}

/* Relax edge (u, v) with weight w. Always applies the min of the update
   d[v] <- min{d[v], d[u]+w_uv}; a stale tail label (d[u] improved since v
   was last relaxed through u) must still propagate. Returns 1 if the
   relaxation is valid (strictly improves, or the recorded predecessor
   re-relaxes an unchanged label). */
static int relax(State *s, int u, int v, double w) {
    Lab nd;
    nd.len = s->d[u] + w;
    nd.cnt = s->cnt[u] + 1;
    nd.id  = v;
    if (lab_lt(&nd, &s->lab[v])) {
        s->d[v]   = nd.len;
        s->cnt[v] = nd.cnt;
        s->lab[v] = nd;
        s->pred[v] = u;
        return 1;
    }
    if (s->pred[v] == u) return 1;
    return 0;
}

/* --- Bounded monotone min-priority queue ----------------------------- */
/* Block-based bounded monotone min-priority queue: values live in two
   block sequences, D0 (batch-prepends) and D1 (inserts); each block holds
   at most M entries and the sequences stay sorted by value so Pull always
   finds the M smallest labels. */

typedef struct {
    int    key;
    Lab    val;
    int    prev, next;  /* doubly-linked entry list within a block */
    int    blk;         /* block containing this entry */
} DPEnt;

typedef struct {
    int    head, tail;  /* entry list */
    int    len;
    Lab    upper;       /* max value in block (D1: for search) */
    int    prev, next;  /* block doubly-linked list within its sequence */
    int    seq;         /* 0 = D0, 1 = D1 */
} DPBlock;

/* AVL tree over the upper bounds of the non-empty D1 blocks.
   A block's upper never increases after insertion into the tree (Insert only
   adds values no larger than the located block's upper, and uppers are not
   refreshed after deletes), so each block's tree key is fixed. */
typedef struct {
    int b;         /* block id */
    int l, r, p;
    int h;
} AVLNode;

typedef struct {
    AVLNode *n;
    int      cap, next, free;
    int     *nmap;   /* block id -> tree node, -1 */
    int      nmap_cap;
    int      root;
} AVL;

typedef struct {
    int      n, M;
    Lab      B;
    DPEnt   *ent;   int ent_cap, ent_next, ent_free;
    DPBlock *blk;   int blk_cap, blk_next, blk_free;
    int      d0h, d0t;   /* D0 head/tail */
    int      d1h, d1t;   /* D1 head/tail */
    int     *slot;        /* [n] entry id per vertex, -1 */
    int     *tmp;         /* scratch for pull/split */
    int      tmp_cap;
    int     *sel;         /* scratch for select_kth */
    int      sel_cap;
    AVL      avl;         /* D1 upper bounds */
    int      cnt;         /* live entries */
} DPQ;

/* --- AVL over D1 upper bounds -------------------------------------- */

static void avl_grow_nmap(AVL *a, int cap) {
    if (a->nmap_cap >= cap) return;
    int nc = a->nmap_cap ? a->nmap_cap * 2 : 16;
    while (nc < cap) nc *= 2;
    a->nmap = xrealloc(a->nmap, sizeof(int) * (size_t)nc);
    for (int i = a->nmap_cap; i < nc; i++) a->nmap[i] = -1;
    a->nmap_cap = nc;
}

static void avl_grow(AVL *a, int min_nodes) {
    if (a->cap >= min_nodes) return;
    int nc = a->cap ? a->cap * 2 : 16;
    while (nc < min_nodes) nc *= 2;
    a->n = xrealloc(a->n, sizeof(AVLNode) * (size_t)nc);
    a->cap = nc;
}

static int avl_node_alloc(AVL *a) {
    int x;
    if (a->free >= 0) { x = a->free; a->free = a->n[x].l; }
    else {
        if (a->next >= a->cap) avl_grow(a, a->next + 1);
        x = a->next++;
    }
    a->n[x] = (AVLNode){-1, -1, -1, -1, 1};
    return x;
}

static void avl_node_free(AVL *a, int x) {
    a->n[x].l = a->free; a->free = x;
}

/* Is block x's key (upper, id) smaller than block y's key? */
static int avl_key_less(DPQ *q, int x, int y) {
    int c = lab_cmp(&q->blk[x].upper, &q->blk[y].upper);
    if (c) return c < 0;
    return x < y;
}

static void avl_upd(AVL *a, int x) {
    int hl = a->n[x].l >= 0 ? a->n[a->n[x].l].h : 0;
    int hr = a->n[x].r >= 0 ? a->n[a->n[x].r].h : 0;
    a->n[x].h = (hl > hr ? hl : hr) + 1;
}

static void avl_rotl(AVL *a, int *r, int x) {
    int y = a->n[x].r;
    a->n[x].r = a->n[y].l;
    if (a->n[y].l >= 0) a->n[a->n[y].l].p = x;
    a->n[y].p = a->n[x].p;
    if (a->n[y].p < 0) *r = y;
    else if (a->n[a->n[y].p].l == x) a->n[a->n[y].p].l = y;
    else a->n[a->n[y].p].r = y;
    a->n[y].l = x; a->n[x].p = y;
    avl_upd(a, x); avl_upd(a, y);
}

static void avl_rotr(AVL *a, int *r, int x) {
    int y = a->n[x].l;
    a->n[x].l = a->n[y].r;
    if (a->n[y].r >= 0) a->n[a->n[y].r].p = x;
    a->n[y].p = a->n[x].p;
    if (a->n[y].p < 0) *r = y;
    else if (a->n[a->n[y].p].l == x) a->n[a->n[y].p].l = y;
    else a->n[a->n[y].p].r = y;
    a->n[y].r = x; a->n[x].p = y;
    avl_upd(a, x); avl_upd(a, y);
}

static void avl_rebalance(AVL *a, int x) {
    while (x >= 0) {
        avl_upd(a, x);
        int hl = a->n[x].l >= 0 ? a->n[a->n[x].l].h : 0;
        int hr = a->n[x].r >= 0 ? a->n[a->n[x].r].h : 0;
        int bf = hl - hr;
        if (bf > 1) {
            int c = a->n[x].l;
            int chl = a->n[c].l >= 0 ? a->n[a->n[c].l].h : 0;
            int chr = a->n[c].r >= 0 ? a->n[a->n[c].r].h : 0;
            if (chr > chl) avl_rotl(a, &a->root, c);
            avl_rotr(a, &a->root, x);
        } else if (bf < -1) {
            int c = a->n[x].r;
            int chl = a->n[c].l >= 0 ? a->n[a->n[c].l].h : 0;
            int chr = a->n[c].r >= 0 ? a->n[a->n[c].r].h : 0;
            if (chl > chr) avl_rotr(a, &a->root, c);
            avl_rotl(a, &a->root, x);
        }
        x = a->n[x].p;
    }
}

static void avl_insert(DPQ *q, int b) {
    AVL *a = &q->avl;
    int x = avl_node_alloc(a);
    a->n[x].b = b;
    a->nmap[b] = x;
    if (a->root < 0) { a->root = x; return; }
    int y = a->root;
    while (1) {
        if (avl_key_less(q, b, a->n[y].b)) {
            if (a->n[y].l >= 0) y = a->n[y].l;
            else { a->n[y].l = x; a->n[x].p = y; break; }
        } else {
            if (a->n[y].r >= 0) y = a->n[y].r;
            else { a->n[y].r = x; a->n[x].p = y; break; }
        }
    }
    avl_rebalance(a, y);
}

static void avl_delete(DPQ *q, int b) {
    AVL *a = &q->avl;
    int x = a->nmap[b];
    if (x < 0) return;
    a->nmap[b] = -1;
    int z;   /* node to rebalance from */
    if (a->n[x].l >= 0 && a->n[x].r >= 0) {
        /* swap with in-order successor */
        int s = a->n[x].r;
        while (a->n[s].l >= 0) s = a->n[s].l;
        a->n[x].b = a->n[s].b;
        a->nmap[a->n[x].b] = x;
        x = s;
    }
    /* x has at most one child */
    int c = a->n[x].l >= 0 ? a->n[x].l : a->n[x].r;
    z = a->n[x].p;
    if (c >= 0) a->n[c].p = z;
    if (z < 0) a->root = c;
    else if (a->n[z].l == x) a->n[z].l = c;
    else a->n[z].r = c;
    avl_node_free(a, x);
    avl_rebalance(a, z);
}

/* Smallest D1 block whose upper bound is >= v, or -1 if none. */
static int avl_find_ge(DPQ *q, Lab v) {
    AVL *a = &q->avl;
    int x = a->root, best = -1;
    while (x >= 0) {
        if (lab_cmp(&q->blk[a->n[x].b].upper, &v) >= 0) {
            best = a->n[x].b;
            x = a->n[x].l;
        } else {
            x = a->n[x].r;
        }
    }
    return best;
}

/* --- Selection (median-of-medians, O(n)) ----------------------------- */

static int ent_less(DPQ *q, int e1, int e2) {
    int c = lab_cmp(&q->ent[e1].val, &q->ent[e2].val);
    if (c) return c < 0;
    return q->ent[e1].key < q->ent[e2].key;
}

/* Median of the subarray a[lo..lo+len), len in 1..5, sorted in place. */
static int med5(DPQ *q, int *a, int lo, int len) {
    for (int i = lo + 1; i < lo + len; i++) {
        int t = a[i], j = i - 1;
        while (j >= lo && ent_less(q, t, a[j])) { a[j + 1] = a[j]; j--; }
        a[j + 1] = t;
    }
    return a[lo + len / 2];
}

/* Rearranges a[0..n) so a[k] is the k-th smallest entry (0-indexed), by
   (val, key). scratch must hold at least n ints. */
static void select_kth(DPQ *q, int *a, int n, int k, int *scratch) {
    if (n <= 5) {
        med5(q, a, 0, n);
        return;
    }
    int g = 0;
    for (int i = 0; i + 5 <= n; i += 5) scratch[g++] = med5(q, a, i, 5);
    if (n % 5) scratch[g++] = med5(q, a, n - n % 5, n % 5);
    select_kth(q, scratch, g, g / 2, scratch);
    int piv = scratch[g / 2];
    int lt = 0, gt = n - 1, i = 0;
    while (i <= gt) {
        if (ent_less(q, a[i], piv)) { int t = a[i]; a[i] = a[lt]; a[lt] = t; lt++; i++; }
        else if (ent_less(q, piv, a[i])) { int t = a[i]; a[i] = a[gt]; a[gt] = t; gt--; }
        else i++;
    }
    if (k < lt)       select_kth(q, a, lt, k, scratch);
    else if (k > gt)  select_kth(q, a + gt + 1, n - gt - 1, k - gt - 1, scratch);
}

/* --- Pool helpers ---------------------------------------------------- */

static int blk_new(DPQ *q, int seq) {
    int b;
    if (q->blk_free >= 0) { b = q->blk_free; q->blk_free = q->blk[b].next; }
    else {
        if (q->blk_next >= q->blk_cap) {
            q->blk_cap = q->blk_cap ? q->blk_cap * 2 : 8;
            q->blk = xrealloc(q->blk, sizeof(DPBlock) * (size_t)q->blk_cap);
            avl_grow_nmap(&q->avl, q->blk_cap);
        }
        b = q->blk_next++;
    }
    q->blk[b] = (DPBlock){-1, -1, 0, LAB_INF, -1, -1, seq};
    return b;
}

static void blk_free(DPQ *q, int b) {
    q->blk[b].next = q->blk_free; q->blk_free = b;
}

static int ent_new(DPQ *q, int key, Lab val) {
    int e;
    if (q->ent_free >= 0) { e = q->ent_free; q->ent_free = q->ent[e].next; }
    else {
        if (q->ent_next >= q->ent_cap) {
            q->ent_cap = q->ent_cap ? q->ent_cap * 2 : 16;
            if (q->ent_cap < q->n) q->ent_cap = imin(q->n, q->ent_cap);
            q->ent = xrealloc(q->ent, sizeof(DPEnt) * (size_t)q->ent_cap);
        }
        e = q->ent_next++;
    }
    q->ent[e] = (DPEnt){key, val, -1, -1, -1};
    q->slot[key] = e;
    q->cnt++;
    return e;
}

static void ent_free(DPQ *q, int e) {
    q->slot[q->ent[e].key] = -1;
    q->ent[e].next = q->ent_free; q->ent_free = e;
    q->cnt--;
}

/* --- Block/sequence operations -------------------------------------- */

static void blk_append(DPQ *q, int b, int e) {
    DPBlock *bl = &q->blk[b];
    DPEnt   *en = &q->ent[e];
    en->blk = b; en->prev = bl->tail; en->next = -1;
    if (bl->tail >= 0) q->ent[bl->tail].next = e; else bl->head = e;
    bl->tail = e; bl->len++;
}

static void blk_unlink_entry(DPQ *q, int e) {
    DPEnt  *en  = &q->ent[e];
    DPBlock *bl = &q->blk[en->blk];
    if (en->prev >= 0) q->ent[en->prev].next = en->next; else bl->head = en->next;
    if (en->next >= 0) q->ent[en->next].prev = en->prev; else bl->tail = en->prev;
    bl->len--;
}

static void blk_remove_seq(DPQ *q, int b) {
    DPBlock *bl = &q->blk[b];
    if (bl->prev >= 0) q->blk[bl->prev].next = bl->next; else {
        if (bl->seq == 0) q->d0h = bl->next; else q->d1h = bl->next;
    }
    if (bl->next >= 0) q->blk[bl->next].prev = bl->prev; else {
        if (bl->seq == 0) q->d0t = bl->prev; else q->d1t = bl->prev;
    }
}

static void seq_prepend(DPQ *q, int seq, int b) {
    DPBlock *bl = &q->blk[b];
    int *hp = (seq == 0) ? &q->d0h : &q->d1h;
    int *tp = (seq == 0) ? &q->d0t : &q->d1t;
    bl->prev = -1; bl->next = *hp;
    if (*hp >= 0) q->blk[*hp].prev = b;
    *hp = b;
    if (*tp < 0) *tp = b;
}

static void seq_append(DPQ *q, int seq, int b) {
    DPBlock *bl = &q->blk[b];
    bl->next = -1; bl->prev = (seq == 0) ? q->d0t : q->d1t;
    if (bl->prev >= 0) q->blk[bl->prev].next = b;
    if (seq == 0) { q->d0t = b; if (q->d0h < 0) q->d0h = b; }
    else          { q->d1t = b; if (q->d1h < 0) q->d1h = b; }
}

/* Insert block b after block a in the same sequence. If a < 0, prepend. */
static void seq_insert_after(DPQ *q, int a, int b) {
    DPBlock *bl = &q->blk[b];
    if (a < 0) { seq_prepend(q, q->blk[b].seq, b); return; }
    DPBlock *al = &q->blk[a];
    bl->prev = a; bl->next = al->next;
    if (al->next >= 0) q->blk[al->next].prev = b; else {
        if (bl->seq == 0) q->d0t = b; else q->d1t = b;
    }
    al->next = b;
}

/* --- D1 split --------------------------------------------------------- */

static void blk_split(DPQ *q, int b) {
    int n = q->blk[b].len;
    /* collect entry ids */
    if (n + 1 > q->tmp_cap) { q->tmp_cap = n + 16; q->tmp = xrealloc(q->tmp, sizeof(int) * (size_t)q->tmp_cap); }
    if (n > q->sel_cap)     { q->sel_cap = n;     q->sel = xrealloc(q->sel, sizeof(int) * (size_t)q->sel_cap); }
    int cnt = 0;
    for (int e = q->blk[b].head; e >= 0; e = q->ent[e].next) q->tmp[cnt++] = e;
    /* median in O(cnt); elements < median to b1, rest to b2 */
    select_kth(q, q->tmp, cnt, cnt / 2, q->sel);
    int mid = q->tmp[cnt / 2];
    /* save block info before blk_new may realloc q->blk */
    int bp       = q->blk[b].prev;
    int bseq     = q->blk[b].seq;
    Lab old_upper = q->blk[b].upper;
    int b1 = blk_new(q, bseq);
    int b2 = blk_new(q, bseq);
    /* link b1, b2 in place of b */
    avl_delete(q, b);
    blk_remove_seq(q, b);
    blk_free(q, b);
    seq_insert_after(q, bp, b1);
    seq_insert_after(q, b1, b2);
    for (int i = 0; i < cnt; i++)
        blk_append(q, ent_less(q, q->tmp[i], mid) ? b1 : b2, q->tmp[i]);
    q->blk[b1].upper = q->ent[mid].val;
    q->blk[b2].upper = old_upper;
    avl_insert(q, b1);
    avl_insert(q, b2);
}

static void dpq_init(DPQ *q, int n, int M, Lab B) {
    q->n = n; q->M = M; q->B = B;
    q->ent = NULL; q->ent_cap = 0; q->ent_next = 0; q->ent_free = -1;
    q->blk = NULL; q->blk_cap = 0; q->blk_next = 0; q->blk_free = -1;
    q->d0h = q->d0t = -1;
    q->d1h = q->d1t = -1;
    q->slot = xmalloc(sizeof(int) * (size_t)n);
    for (int i = 0; i < n; i++) q->slot[i] = -1;
    q->tmp = NULL; q->tmp_cap = 0;
    q->sel = NULL; q->sel_cap = 0;
    q->avl.n = NULL; q->avl.cap = 0; q->avl.next = 0; q->avl.free = -1;
    q->avl.nmap = NULL; q->avl.nmap_cap = 0; q->avl.root = -1;
    q->cnt = 0;
    /* D1 starts with one empty block at upper B. */
    int b = blk_new(q, 1);
    q->blk[b].upper = B;
    seq_append(q, 1, b);
    avl_insert(q, b);
}

static void dpq_free(DPQ *q) {
    free(q->ent); free(q->blk); free(q->slot); free(q->tmp); free(q->sel);
    free(q->avl.n); free(q->avl.nmap);
}

static int dpq_empty(DPQ *q) { return q->cnt == 0; }

static void dpq_insert(DPQ *q, int k, Lab v) {
    int e = q->slot[k];
    if (e >= 0) {
        if (lab_cmp(&q->ent[e].val, &v) <= 0) return;   /* no improvement */
        int ob = q->ent[e].blk;
        blk_unlink_entry(q, e);               /* delete old */
        if (q->blk[ob].len == 0) {
            blk_remove_seq(q, ob);
            if (q->blk[ob].seq == 1) avl_delete(q, ob);
            blk_free(q, ob);
        }
        ent_free(q, e);
    }
    /* locate D1 block via the AVL: smallest upper >= v */
    int b = avl_find_ge(q, v);
    if (b < 0) {                          /* no upper >= v: new block at tail */
        b = blk_new(q, 1);
        q->blk[b].upper = q->B;
        seq_append(q, 1, b);
        avl_insert(q, b);
    }
    int ne = ent_new(q, k, v);
    blk_append(q, b, ne);
    /* Insert never exceeds the located block's upper (v <= upper), so the
       block upper, hence its AVL key, stays fixed. */
    if (q->blk[b].len > q->M) blk_split(q, b);
}

/* --- BatchPrepend ------------------------------------------------------ */

typedef struct { int key; Lab val; } _BPBe;

static int _bp_cmp_key(const void *a, const void *b) {
    const _BPBe *pa = a, *pb = b;
    if (pa->key != pb->key) return pa->key - pb->key;
    return lab_cmp(&pa->val, &pb->val);
}
static int _bp_cmp_val(const void *a, const void *b) {
    const _BPBe *pa = a, *pb = b;
    int c = lab_cmp(&pa->val, &pb->val);
    if (c) return c;
    return pa->key - pb->key;
}

static void dpq_batch_prepend(DPQ *q, const int *kk, const Lab *kv, int len) {
    if (len == 0) return;
    /* 1. Delete any existing queue entry for each batch key (batch values
          are all < Bi <= min value currently in the queue, so the batch
          value is always an improvement). */
    for (int i = 0; i < len; i++) {
        int e = q->slot[kk[i]];
        if (e >= 0) {
            int ob = q->ent[e].blk;
            blk_unlink_entry(q, e);
            if (q->blk[ob].len == 0) {
                blk_remove_seq(q, ob);
                if (q->blk[ob].seq == 1) avl_delete(q, ob);
                blk_free(q, ob);
            }
            ent_free(q, e);
        }
    }
    /* 2. Dedup within batch: keep smallest value per key. */
    _BPBe *tmp = xmalloc(sizeof(_BPBe) * (size_t)len);
    for (int i = 0; i < len; i++) { tmp[i].key = kk[i]; tmp[i].val = kv[i]; }
    qsort(tmp, (size_t)len, sizeof(_BPBe), _bp_cmp_key);
    int m = 0;
    for (int i = 0; i < len; i++)
        if (i == 0 || tmp[i].key != tmp[i - 1].key) tmp[m++] = tmp[i];
    /* 3. Sort survivors by (val, key). */
    qsort(tmp, (size_t)m, sizeof(_BPBe), _bp_cmp_val);
    /* 4. Chunk into blocks of at most ceil(M/2) and prepend to D0 so that
          blocks end up in ascending order (smallest at the head): build
          from the largest chunk backwards, each seq_prepend puts its block
          at the head. */
    int chunk = (q->M + 1) / 2;
    if (chunk < 1) chunk = 1;
    for (int i = m; i > 0; ) {
        int lo = imax(0, i - chunk);
        int b = blk_new(q, 0);
        Lab mx = LAB_INF;
        for (int j = lo; j < i; j++) {
            int e = ent_new(q, tmp[j].key, tmp[j].val);
            blk_append(q, b, e);
            if (lab_cmp(&tmp[j].val, &mx) > 0) mx = tmp[j].val;
        }
        q->blk[b].upper = mx;
        seq_prepend(q, 0, b);
        i = lo;
    }
    free(tmp);
}

/* --- Pull -------------------------------------------------------------- */

static int dpq_pull(DPQ *q, int *ok, Lab *ov, int M, Lab *bound) {
    if (q->cnt == 0) { *bound = q->B;     return 0; }

    /* Collect a prefix of whole blocks from each sequence separately, stopping
       each sequence once M elements from it have been taken.
       Blocks are globally ordered across a sequence (every element of an
       earlier block is no more than every element of a later block), so the
       prefix of whole blocks contains the M smallest of that sequence; a block
       may overshoot M by up to M-1, hence <= 2M elements per sequence. */
    int cap = 4 * M + 8;
    if (cap > q->tmp_cap) { q->tmp_cap = cap; q->tmp = xrealloc(q->tmp, sizeof(int) * (size_t)q->tmp_cap); }
    if (cap > q->sel_cap) { q->sel_cap = cap; q->sel = xrealloc(q->sel, sizeof(int) * (size_t)q->sel_cap); }
    int n = 0, n0 = 0, n1 = 0;
    for (int bi = q->d0h; bi >= 0 && n0 < M; bi = q->blk[bi].next) {
        for (int e = q->blk[bi].head; e >= 0; e = q->ent[e].next)
            q->tmp[n++] = e, n0++;
    }
    for (int bi = q->d1h; bi >= 0 && n1 < M; bi = q->blk[bi].next) {
        for (int e = q->blk[bi].head; e >= 0; e = q->ent[e].next)
            q->tmp[n++] = e, n1++;
    }

    int cnt;
    if (n <= M) {
        /* All remaining elements were collected: return them all, x = B. */
        cnt = n;
    } else {
        /* Select the M smallest among the collected in O(M). */
        select_kth(q, q->tmp, n, M - 1, q->sel);
        cnt = M;
    }
    for (int i = 0; i < cnt; i++) {
        int e = q->tmp[i];
        ok[i] = q->ent[e].key;
        ov[i] = q->ent[e].val;
    }
    for (int i = 0; i < cnt; i++) {
        int e = q->tmp[i];
        int b = q->ent[e].blk;
        blk_unlink_entry(q, e);
        if (q->blk[b].len == 0) {
            blk_remove_seq(q, b);
            if (q->blk[b].seq == 1) avl_delete(q, b);
            blk_free(q, b);
        }
        ent_free(q, e);
    }
    /* Bound: smallest remaining value sits in a head block (blocks are in
       ascending order), so scanning the head blocks takes O(M). */
    if (q->cnt == 0) { *bound = q->B; return cnt; }
    Lab mn = q->B;
    if (q->d0h >= 0)
        for (int e = q->blk[q->d0h].head; e >= 0; e = q->ent[e].next)
            if (lab_cmp(&q->ent[e].val, &mn) < 0) mn = q->ent[e].val;
    if (q->d1h >= 0)
        for (int e = q->blk[q->d1h].head; e >= 0; e = q->ent[e].next)
            if (lab_cmp(&q->ent[e].val, &mn) < 0) mn = q->ent[e].val;
    *bound = mn;
    return cnt;
}

/* --- FindPivots -------------------------------------------------------- */

static void find_pivots(State *s, Lab B,
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

    /* Relax for k steps; each step's frontier is the set of vertices
       (re)updated in the previous step, so an improved label is processed
       again. */
    for (int step = 0; step < k && f_len > 0; step++) {
        nf = 0;
        for (int i = 0; i < f_len; i++) {
            int u = frontier[i];
            for (int e = s->g->off[u]; e < s->g->off[u + 1]; e++) {
                int v = s->g->adj[e];
                if (relax(s, u, v, s->g->wgt[e])) {
                    if (lab_lt(&s->lab[v], &B)) {
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

    /* Shortest-path forest over W: F = { (Pred[v], v) : v in W, Pred[v] in W }.
       Pred[] is maintained by relax(), so trees follow the recorded
       predecessors directly. */
    int *par = xmalloc(sizeof(int) * (size_t)n);
    for (int i = 0; i < n; i++) par[i] = -1;
    for (int i = 0; i < *Wlen; i++) {
        int v = W[i];
        int p = s->pred[v];
        if (p >= 0 && inW[p]) par[v] = p;
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

/* --- Base Case ---------------------------------------------------------- */

static void base_case(State *s, Lab B, const int *S, int Slen,
                      Lab *Bp, IVec *U) {
    int k = s->k;
    Heap h;
    heap_init(&h, s->n);

    unsigned char *inU = xcalloc((size_t)s->n, 1);
    int *local = xmalloc(sizeof(int) * (size_t)(k + 1));
    int local_len = 0;
    local[0] = -1;

    /* Sources at or below B are pushed: the pull bound can equal a source's
       label when distances tie, and dropping it would stall the recursion. */
    for (int i = 0; i < Slen; i++)
        if (lab_le(&s->lab[S[i]], &B)) heap_push(&h, S[i], s->lab[S[i]]);

    /* Mini-Dijkstra over labels below B, stopping after k+1 vertices. */
    while (h.n > 0 && local_len < k + 1) {
        Lab du; int u = heap_pop(&h, &du);
        if (u == -1) break;
        if (inU[u]) continue;
        inU[u] = 1;
        local[local_len++] = u;

        for (int e = s->g->off[u]; e < s->g->off[u + 1]; e++) {
            int v = s->g->adj[e];
            double w = s->g->wgt[e];
            Lab nd;
            nd.len = s->d[u] + w;
            nd.cnt = s->cnt[u] + 1;
            nd.id  = v;
                /* Non-strict: equal labels still propagate. */
            if (lab_le(&nd, &s->lab[v]) && lab_lt(&nd, &B)) {
                relax(s, u, v, w);
                heap_push(&h, v, s->lab[v]);
            }
        }
    }

    if (local_len <= k) {
        *Bp = B;
        for (int i = 0; i < local_len; i++) ivec_push(U, local[i]);
    } else {
        /* B' = max label over U0 and trim exactly that vertex. The max label
           is unique under the total order (ties on length are broken by the
           vertex count and id), so U keeps the k closest vertices. */
        Lab mx = s->lab[local[0]];
        int mi = 0;
        for (int i = 1; i < local_len; i++)
            if (lab_cmp(&s->lab[local[i]], &mx) > 0) { mx = s->lab[local[i]]; mi = i; }
        *Bp = mx;
        for (int i = 0; i < local_len; i++)
            if (i != mi) ivec_push(U, local[i]);
    }

    free(local);
    free(inU);
    heap_free(&h);
}

/* --- BMSSP -------------------------------------------------------------- */

static void bmssp(State *s, int l, Lab B,
                  const int *S, int Slen,
                  Lab *Bp, IVec *U);

static void bmssp_level0(State *s, Lab B, const int *S, int Slen,
                         Lab *Bp, IVec *U) {
    base_case(s, B, S, Slen, Bp, U);
}

static void bmssp_recurse(State *s, int l, Lab B,
                          const int *S, int Slen,
                          Lab *Bp, IVec *U) {
    int k = s->k, t = s->t, n = s->n;

    /* Pull size M and workload budget max_U. */
    long long Mll = pow2_sat((l - 1) * t);
    int M = (int)imin((long long)n, Mll);
    long long max_U = mul_sat((long long)k, pow2_sat(l * t));

    int *P = xmalloc(sizeof(int) * (size_t)n);
    int *W = xmalloc(sizeof(int) * (size_t)n);
    int Plen = 0, Wlen = 0;
    find_pivots(s, B, S, Slen, P, &Plen, W, &Wlen);

    DPQ D;
    dpq_init(&D, n, M, B);
    for (int i = 0; i < Plen; i++)
        dpq_insert(&D, P[i], s->lab[P[i]]);

    /* B'_0 = min label over P, or B if P is empty. */
    Lab Bp0 = LAB_INF;
    for (int i = 0; i < Plen; i++)
        if (lab_lt(&s->lab[P[i]], &Bp0)) Bp0 = s->lab[P[i]];
    if (Plen == 0) Bp0 = B;

    int *Si = xmalloc(sizeof(int) * (size_t)n);
    Lab *Siv = xmalloc(sizeof(Lab)  * (size_t)n);
    int Kcap = 16;
    int *Kk = xmalloc(sizeof(int) * (size_t)Kcap);
    Lab *Kv = xmalloc(sizeof(Lab) * (size_t)Kcap);

    long long ulen = 0;
    Lab Bi, Bi_prime = Bp0;
    unsigned char *inU = xcalloc((size_t)n, 1);
    int succeeded = 0;

    while (!dpq_empty(&D)) {
        int Silen = dpq_pull(&D, Si, Siv, M, &Bi);
        if (Silen == 0) break;

        /* Drop stale entries of vertices already settled: a vertex becomes
           complete once it enters U, so S_i must be exactly the pulled set
           of incomplete vertices. */
        {
            int w = 0;
            for (int i = 0; i < Silen; i++)
                if (!inU[Si[i]]) { Si[w] = Si[i]; Siv[w] = Siv[i]; w++; }
            Silen = w;
        }
        if (Silen == 0) continue;

        /* Recursive call. */
        IVec Ui;
        ivec_init(&Ui);
        Lab Ui_prime;
        bmssp(s, l - 1, Bi, Si, Silen, &Ui_prime, &Ui);
        Bi_prime = Ui_prime;

        /* U is a set: count and keep each settled vertex once. */
        for (int i = 0; i < Ui.len; i++) {
            int v = Ui.a[i];
            if (inU[v]) continue;
            inU[v] = 1;
            ulen++;
            ivec_push(U, v);
        }

        /* Relax edges from Ui. */
        int Klen = 0;
        for (int i = 0; i < Ui.len; i++) {
            int u = Ui.a[i];
            for (int e = s->g->off[u]; e < s->g->off[u + 1]; e++) {
                int v = s->g->adj[e];
                double w = s->g->wgt[e];
                Lab nd;
                nd.len = s->d[u] + w;
                nd.cnt = s->cnt[u] + 1;
                nd.id  = v;
            /* Non-strict: equal labels still propagate. */
                if (lab_le(&nd, &s->lab[v])) {
                    relax(s, u, v, w);
                    if (lab_ge(&nd, &Bi) && lab_lt(&nd, &B)) {
                        dpq_insert(&D, v, nd);
                    } else if (lab_ge(&nd, &Bi_prime) && lab_lt(&nd, &Bi)) {
                        if (Klen >= Kcap) {
                            Kcap *= 2;
                            Kk = xrealloc(Kk, sizeof(int) * (size_t)Kcap);
                            Kv = xrealloc(Kv, sizeof(Lab) * (size_t)Kcap);
                        }
                        Kk[Klen] = v; Kv[Klen] = nd; Klen++;
                    }
                }
            }
        }

        /* Step 4: prepend K and the pulled Si entries with label in [Bi', Bi). */
        for (int i = 0; i < Silen; i++) {
            if (lab_ge(&Siv[i], &Bi_prime) && lab_lt(&Siv[i], &Bi)) {
                if (Klen >= Kcap) {
                    Kcap *= 2;
                    Kk = xrealloc(Kk, sizeof(int) * (size_t)Kcap);
                    Kv = xrealloc(Kv, sizeof(Lab) * (size_t)Kcap);
                }
                Kk[Klen] = Si[i]; Kv[Klen] = Siv[i]; Klen++;
            }
        }
        dpq_batch_prepend(&D, Kk, Kv, Klen);

        ivec_free(&Ui);

        if (dpq_empty(&D)) { succeeded = 1; break; }
        if (ulen > max_U) break;
    }
    if (dpq_empty(&D)) succeeded = 1;

    /* B' = B on success; on a partial exit it is the current recursion's
       bound B'_i. */
    Lab final_B = succeeded ? B : (lab_lt(&Bi_prime, &B) ? Bi_prime : B);

    /* Include vertices of W now within the final bound. */
    for (int i = 0; i < Wlen; i++) {
        int v = W[i];
        if (lab_lt(&s->lab[v], &final_B) && !inU[v]) { inU[v] = 1; ivec_push(U, v); }
    }

    free(inU);

    *Bp = final_B;

    free(P); free(W); free(Si); free(Siv); free(Kk); free(Kv);
    dpq_free(&D);
}

static void bmssp(State *s, int l, Lab B,
                  const int *S, int Slen,
                  Lab *Bp, IVec *U) {
    if (l == 0)
        bmssp_level0(s, B, S, Slen, Bp, U);
    else
        bmssp_recurse(s, l, B, S, Slen, Bp, U);
}

/* --- Public API ---------------------------------------------------------- */

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

    /* Run the algorithm on the constant-degree transformed graph;
       n' = O(m), m' = O(m), distances are preserved. */
    Transform tr;
    transform_build(&csr, g->n, &tr);

    if (tr.canon[src] < 0) {
        /* Source has no incident edges: only the source is reachable. */
        for (int i = 0; i < g->n; i++) { dist[i] = SSORT_INFINITY; pred[i] = -1; }
        dist[src] = 0.0;
        transform_free(&tr);
        csr_free(&csr);
        return 0;
    }

    State state;
    state_init(&state, &tr.c);
    int s2 = tr.canon[src];
    state.d[s2] = 0.0;
    state.cnt[s2] = 0;
    state.lab[s2] = (Lab){0.0, 0, s2};

    /* The algorithm is exact end-to-end: every reachable vertex ends up
       complete, so no final Dijkstra pass is needed. */
    int l = (int)ceil(log2((double)tr.c.n) / (double)state.t);
    if (l < 0) l = 0;

    int *S = xmalloc(sizeof(int));
    S[0] = s2;
    Lab Bp;
    IVec U;
    ivec_init(&U);
    bmssp(&state, l, LAB_INF, S, 1, &Bp, &U);
    free(S);
    ivec_free(&U);

    /* Back-map distances: dist[v] = dist'[x_{v,*}] for any cycle vertex
       (all cycle vertices of v share the same distance). */
    for (int v = 0; v < g->n; v++) {
        int c = tr.canon[v];
        dist[v] = c >= 0 ? state.d[c] : SSORT_INFINITY;
        pred[v] = -1;
    }

    /* Back-map predecessors: pred[v] is the in-neighbor u minimizing
       (dist[u] + w_uv, cnt[u] + 1).  The minimum equals dist[v] exactly
       (float: dist[u] is shared bit-for-bit by all of u's cycle vertices
       and dist[u]+w_uv is recomputed with the same operands as before). */
    Lab *best = xmalloc(sizeof(Lab) * (size_t)g->n);
    int *bestu = xmalloc(sizeof(int) * (size_t)g->n);
    for (int v = 0; v < g->n; v++) { best[v] = LAB_INF; bestu[v] = -1; }
    for (int u = 0; u < g->n; u++) {
        if (dist[u] == SSORT_INFINITY) continue;
        int cu = tr.canon[u];
        for (int e = csr.off[u]; e < csr.off[u + 1]; e++) {
            int v = csr.adj[e];
            if (v == src || dist[v] == SSORT_INFINITY) continue;
            Lab cand;
            cand.len = dist[u] + csr.wgt[e];
            cand.cnt = state.cnt[cu] + 1;
            cand.id = v;
            if (lab_lt(&cand, &best[v])) { best[v] = cand; bestu[v] = u; }
        }
    }
    for (int v = 0; v < g->n; v++)
        if (bestu[v] >= 0) pred[v] = bestu[v];
    free(best);
    free(bestu);

    state_free(&state);
    transform_free(&tr);
    csr_free(&csr);
    return 0;
}

/* --- DPQ unit test (internal) ------------------------------------------- */

int ssort_dpq_test(void) {
    int n = 20, M = 4;
    Lab B = {100.0, 0, 0};
    DPQ q;
    dpq_init(&q, n, M, B);

    /* batch_prepend several values; Pull returns the M smallest as a set
       (order is unspecified) and a bound separating returned from remaining. */
    int Kk[6] = {10, 5, 15, 3, 8, 12};
    Lab Kv[6] = {{10,0,10}, {5,0,5}, {15,0,15}, {3,0,3}, {8,0,8}, {12,0,12}};
    dpq_batch_prepend(&q, Kk, Kv, 6);
    if (q.cnt != 6) return 1;

    {
        Lab got[8];
        int ngot = 0;
        while (q.cnt > 0) {
            int pk[8]; Lab pv[8]; Lab pb;
            int cnt = dpq_pull(&q, pk, pv, M, &pb);
            if (cnt == 0) return 2;
            if (cnt > M) return 2;
            for (int i = 0; i < cnt; i++) {
                /* every returned value must be < the bound */
                if (!lab_lt(&pv[i], &pb)) return 3;
                got[ngot++] = pv[i];
            }
        }
        if (ngot != 6) return 4;
        Lab expect[6] = {{3,0,3},{5,0,5},{8,0,8},{10,0,10},{12,0,12},{15,0,15}};
        /* multiset equality */
        for (int i = 0; i < 6; i++) {
            int found = 0;
            for (int j = 0; j < 6; j++)
                if (lab_cmp(&got[i], &expect[j]) == 0) { found = 1; expect[j].len = -999.0; break; }
            if (!found) return 4;
        }
    }

    /* insert with decrease-key */
    dpq_free(&q);
    dpq_init(&q, n, M, B);
    dpq_insert(&q, 0, (Lab){50.0, 0, 0});
    dpq_insert(&q, 1, (Lab){30.0, 0, 1});
    dpq_insert(&q, 2, (Lab){40.0, 0, 2});
    if (q.cnt != 3) return 5;

    dpq_insert(&q, 2, (Lab){20.0, 0, 2});
    if (q.cnt != 3) return 6;

    {
        int pk[8]; Lab pv[8]; Lab pb;
        int cnt = dpq_pull(&q, pk, pv, M, &pb);
        if (cnt != 3) return 7;
        int has20 = 0;
        for (int i = 0; i < cnt; i++)
            if (lab_cmp(&pv[i], &(Lab){20,0,2}) == 0) has20 = 1;
        if (!has20) return 7;
    }

    /* batch_prepend + insert interleaving */
    dpq_free(&q);
    dpq_init(&q, n, M, B);
    int K2k[3] = {0, 1, 2};
    Lab K2v[3] = {{5,0,0}, {3,0,1}, {7,0,2}};
    dpq_batch_prepend(&q, K2k, K2v, 3);
    dpq_insert(&q, 3, (Lab){4.0, 0, 3});
    if (q.cnt != 4) return 8;

    {
        int pk[8]; Lab pv[8]; Lab pb;
        int cnt = dpq_pull(&q, pk, pv, M, &pb);
        if (cnt != 4) return 9;
        Lab expect[4] = {{3,0,1},{4,0,3},{5,0,0},{7,0,2}};
        for (int i = 0; i < 4; i++) {
            int found = 0;
            for (int j = 0; j < 4; j++)
                if (lab_cmp(&pv[i], &expect[j]) == 0) { found = 1; expect[j].len = -999.0; break; }
            if (!found) return 9;
        }
    }

    /* pull bound should be correct */
    dpq_free(&q);
    dpq_init(&q, n, M, B);
    int K3k[5] = {0, 1, 2, 3, 4};
    Lab K3v[5] = {{10,0,0}, {20,0,1}, {30,0,2}, {40,0,3}, {50,0,4}};
    dpq_batch_prepend(&q, K3k, K3v, 5);
    {
        int pk[8]; Lab pv[8]; Lab pb;
        int cnt = dpq_pull(&q, pk, pv, M, &pb);
        if (cnt != 4) return 10;
        /* bound must separate: returned all < pb <= remaining */
        for (int i = 0; i < cnt; i++)
            if (!lab_lt(&pv[i], &pb)) return 10;
        if (lab_cmp(&pb, &(Lab){50,0,4}) != 0) return 10;
    }

    dpq_free(&q);
    return 0;
}


