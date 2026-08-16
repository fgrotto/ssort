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
/* Block-based bounded monotone min-priority queue following the paper:
   values live in two block sequences, D0 (batch-prepends) and D1 (inserts);
   each block holds at most M entries and the sequences stay sorted by value
   so Pull always finds the M smallest labels. */

typedef struct {
    int    key;
    double val;
    int    prev, next;  /* doubly-linked entry list within a block */
    int    blk;         /* block containing this entry */
} DPEnt;

typedef struct {
    int    head, tail;  /* entry list */
    int    len;
    double upper;       /* max value in block (D1: for search) */
    int    prev, next;  /* block doubly-linked list within its sequence */
    int    seq;         /* 0 = D0, 1 = D1 */
} DPBlock;

typedef struct {
    int      n, M;
    double   B;
    DPEnt   *ent;   int ent_cap, ent_next, ent_free;
    DPBlock *blk;   int blk_cap, blk_next, blk_free;
    int      d0h, d0t;   /* D0 head/tail */
    int      d1h, d1t;   /* D1 head/tail */
    int     *slot;        /* [n] entry id per vertex, -1 */
    int     *tmp;         /* scratch for pull/split */
    int      tmp_cap;
    int      cnt;         /* live entries */
} DPQ;

/* ─── Pool helpers ──────────────────────────────────────────────── */

static int blk_new(DPQ *q, int seq) {
    int b;
    if (q->blk_free >= 0) { b = q->blk_free; q->blk_free = q->blk[b].next; }
    else {
        if (q->blk_next >= q->blk_cap) {
            q->blk_cap = q->blk_cap ? q->blk_cap * 2 : 8;
            q->blk = xrealloc(q->blk, sizeof(DPBlock) * (size_t)q->blk_cap);
        }
        b = q->blk_next++;
    }
    q->blk[b] = (DPBlock){-1, -1, 0, 0.0, -1, -1, seq};
    return b;
}

static void blk_free(DPQ *q, int b) {
    q->blk[b].next = q->blk_free; q->blk_free = b;
}

static int ent_new(DPQ *q, int key, double val) {
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

/* ─── Block/sequence operations ──────────────────────────────────── */

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

/* ─── D1 split ──────────────────────────────────────────────────── */

static void blk_split(DPQ *q, int b) {
    int n = q->blk[b].len;
    /* collect entry ids */
    if (n + 1 > q->tmp_cap) { q->tmp_cap = n + 16; q->tmp = xrealloc(q->tmp, sizeof(int) * (size_t)q->tmp_cap); }
    int cnt = 0;
    for (int e = q->blk[b].head; e >= 0; e = q->ent[e].next) q->tmp[cnt++] = e;
    /* sort by (val, key) */
    for (int i = 1; i < cnt; i++) {
        int t = q->tmp[i]; double tv = q->ent[t].val; int tk = q->ent[t].key;
        int j = i - 1;
        while (j >= 0 && (q->ent[q->tmp[j]].val > tv ||
               (q->ent[q->tmp[j]].val == tv && q->ent[q->tmp[j]].key > tk))) {
            q->tmp[j + 1] = q->tmp[j]; j--;
        }
        q->tmp[j + 1] = t;
    }
    /* save block info before blk_new may realloc q->blk */
    int bp   = q->blk[b].prev;
    int bseq = q->blk[b].seq;
    /* partition into two blocks */
    int mid = cnt / 2;
    int b1 = blk_new(q, bseq);
    int b2 = blk_new(q, bseq);
    /* link b1, b2 in place of b */
    blk_remove_seq(q, b);
    blk_free(q, b);
    seq_insert_after(q, bp, b1);
    seq_insert_after(q, b1, b2);
    /* relink entries */
    for (int i = 0; i < mid; i++) blk_append(q, b1, q->tmp[i]);
    for (int i = mid; i < cnt; i++) blk_append(q, b2, q->tmp[i]);
    /* set uppers */
    q->blk[b1].upper = q->ent[q->tmp[mid - 1]].val;
    q->blk[b2].upper = q->ent[q->tmp[cnt - 1]].val;
}

static void dpq_init(DPQ *q, int n, int M, double B) {
    q->n = n; q->M = M; q->B = B;
    q->ent = NULL; q->ent_cap = 0; q->ent_next = 0; q->ent_free = -1;
    q->blk = NULL; q->blk_cap = 0; q->blk_next = 0; q->blk_free = -1;
    q->d0h = q->d0t = -1;
    q->d1h = q->d1t = -1;
    q->slot = xmalloc(sizeof(int) * (size_t)n);
    for (int i = 0; i < n; i++) q->slot[i] = -1;
    q->tmp = NULL; q->tmp_cap = 0;
    q->cnt = 0;
    /* D1 starts with one empty block at upper B (paper's initialization). */
    int b = blk_new(q, 1);
    q->blk[b].upper = B;
    seq_append(q, 1, b);
}

static void dpq_free(DPQ *q) {
    free(q->ent); free(q->blk); free(q->slot); free(q->tmp);
}

static int dpq_empty(DPQ *q) { return q->cnt == 0; }

static void dpq_insert(DPQ *q, int k, double v) {
    int e = q->slot[k];
    if (e >= 0) {
        if (q->ent[e].val <= v) return;       /* no improvement */
        blk_unlink_entry(q, e);               /* delete old */
        if (q->blk[q->ent[e].blk].len == 0) {
            blk_remove_seq(q, q->ent[e].blk);
            blk_free(q, q->ent[e].blk);
        }
        ent_free(q, e);
    }
    /* walk D1 to find first block with upper >= v */
    int b = -1;
    for (int bi = q->d1h; bi >= 0; bi = q->blk[bi].next)
        if (q->blk[bi].upper >= v) { b = bi; break; }
    if (b < 0) {                          /* all uppers < v: new block at tail */
        b = blk_new(q, 1);
        q->blk[b].upper = q->B;
        seq_append(q, 1, b);
    }
    int ne = ent_new(q, k, v);
    blk_append(q, b, ne);
    if (v > q->blk[b].upper) q->blk[b].upper = v;
    if (q->blk[b].len > q->M) blk_split(q, b);
}

/* ─── BatchPrepend ──────────────────────────────────────────────── */

typedef struct { int key; double val; } _BPBe;

static int _bp_cmp_key(const void *a, const void *b) {
    const _BPBe *pa = a, *pb = b;
    if (pa->key != pb->key) return pa->key - pb->key;
    return (pa->val > pb->val) - (pa->val < pb->val);
}
static int _bp_cmp_val(const void *a, const void *b) {
    const _BPBe *pa = a, *pb = b;
    if (pa->val != pb->val) return (pa->val > pb->val) - (pa->val < pb->val);
    return pa->key - pb->key;
}

static void dpq_batch_prepend(DPQ *q, const int *kk, const double *kv, int len) {
    if (len == 0) return;
    /* 1. Delete any existing queue entry for each batch key (batch values
          are all < Bi <= min value currently in the queue, so the batch
          value is always an improvement). */
    for (int i = 0; i < len; i++) {
        int e = q->slot[kk[i]];
        if (e >= 0) {
            blk_unlink_entry(q, e);
            if (q->blk[q->ent[e].blk].len == 0) {
                blk_remove_seq(q, q->ent[e].blk);
                blk_free(q, q->ent[e].blk);
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
    /* 4. Chunk into blocks of ≤ M and prepend to D0. */
    for (int i = 0; i < m; ) {
        int b = blk_new(q, 0);
        double mx = -1.0;
        for (int j = 0; j < q->M && i < m; j++, i++) {
            int e = ent_new(q, tmp[i].key, tmp[i].val);
            blk_append(q, b, e);
            if (tmp[i].val > mx) mx = tmp[i].val;
        }
        q->blk[b].upper = mx;
        seq_prepend(q, 0, b);
    }
    free(tmp);
}

/* ─── Pull ───────────────────────────────────────────────────────── */

static int dpq_pull(DPQ *q, int *ok, double *ov, int M, double *bound) {
    if (q->cnt == 0) { *bound = q->B;     return 0;
}

    /* Collect prefix of blocks from D0 and D1 into tmp[]. */
    int need = imin(M, q->cnt);
    int cap = need * 2 + 8;
    if (cap > q->tmp_cap) { q->tmp_cap = cap; q->tmp = xrealloc(q->tmp, sizeof(int) * (size_t)q->tmp_cap); }
    int n = 0;
    /* D0 prefix */
    for (int bi = q->d0h; bi >= 0 && n < need; bi = q->blk[bi].next)
        for (int e = q->blk[bi].head; e >= 0; e = q->ent[e].next) q->tmp[n++] = e;
    /* D1 prefix */
    for (int bi = q->d1h; bi >= 0 && n < need; bi = q->blk[bi].next)
        for (int e = q->blk[bi].head; e >= 0; e = q->ent[e].next) q->tmp[n++] = e;
    /* Select the M smallest among collected (insertion sort, M ≤ n ≤ 2M). */
    /* Use a comparator that reads values from the entry pool. */
    for (int i = 1; i < n; i++) {
        int t = q->tmp[i]; double tv = q->ent[t].val; int tk = q->ent[t].key;
        int j = i - 1;
        while (j >= 0 && (q->ent[q->tmp[j]].val > tv ||
               (q->ent[q->tmp[j]].val == tv && q->ent[q->tmp[j]].key > tk))) {
            q->tmp[j + 1] = q->tmp[j]; j--;
        }
        q->tmp[j + 1] = t;
    }
    int cnt = imin(M, n);
    /* Return selected entries and delete them. */
    for (int i = 0; i < cnt; i++) {
        int e = q->tmp[i];
        ok[i] = q->ent[e].key;
        ov[i] = q->ent[e].val;
    }
    for (int i = 0; i < cnt; i++) {
        int e = q->tmp[i];
        int b = q->ent[e].blk;
        blk_unlink_entry(q, e);
        if (q->blk[b].len == 0) { blk_remove_seq(q, b); blk_free(q, b); }
        ent_free(q, e);
    }
    /* Compute bound: smallest remaining value, or B if empty. */
    if (q->cnt == 0) { *bound = q->B; return cnt; }
    double mn = q->B;
    for (int bi = q->d0h; bi >= 0; bi = q->blk[bi].next)
        for (int e = q->blk[bi].head; e >= 0; e = q->ent[e].next)
            if (q->ent[e].val < mn) mn = q->ent[e].val;
    for (int bi = q->d1h; bi >= 0; bi = q->blk[bi].next)
        for (int e = q->blk[bi].head; e >= 0; e = q->ent[e].next)
            if (q->ent[e].val < mn) mn = q->ent[e].val;
    *bound = mn;
    return cnt;
}

/* ─── FindPivots ────────────────────────────────────────────────── */

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

/* ─── Base Case ──────────────────────────────────────────────────── */

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

/* ─── BMSSP ──────────────────────────────────────────────────────── */

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
    dpq_init(&D, n, M, B);
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
        dpq_batch_prepend(&D, Kk, Kv, Klen);

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

/* ─── DPQ unit test (internal) ──────────────────────────────────── */

int ssort_dpq_test(void) {
    int n = 20, M = 4;
    double B = 100.0;
    DPQ q;
    dpq_init(&q, n, M, B);

    /* batch_prepend several values, pull should return them sorted ascending */
    int Kk[6] = {10, 5, 15, 3, 8, 12};
    double Kv[6] = {10.0, 5.0, 15.0, 3.0, 8.0, 12.0};
    dpq_batch_prepend(&q, Kk, Kv, 6);
    if (q.cnt != 6) return 1;

    double prev = -1.0;
    int total_pulled = 0;
    while (q.cnt > 0) {
        int pk[8]; double pv[8]; double pb;
        int cnt = dpq_pull(&q, pk, pv, M, &pb);
        if (cnt == 0) return 2;
        for (int i = 0; i < cnt; i++) {
            if (pv[i] < prev - 1e-12) return 3;
            prev = pv[i];
            total_pulled++;
        }
    }
    if (total_pulled != 6) return 4;

    /* insert with decrease-key */
    dpq_free(&q);
    dpq_init(&q, n, M, B);
    dpq_insert(&q, 0, 50.0);
    dpq_insert(&q, 1, 30.0);
    dpq_insert(&q, 2, 40.0);
    if (q.cnt != 3) return 5;

    dpq_insert(&q, 2, 20.0);
    if (q.cnt != 3) return 6;

    {
        int pk[8]; double pv[8]; double pb;
        int cnt = dpq_pull(&q, pk, pv, M, &pb);
        if (cnt < 1 || pk[0] != 2 || pv[0] > 20.0 + 1e-12) return 7;
    }

    /* batch_prepend + insert interleaving */
    dpq_free(&q);
    dpq_init(&q, n, M, B);
    int K2k[3] = {0, 1, 2};
    double K2v[3] = {5.0, 3.0, 7.0};
    dpq_batch_prepend(&q, K2k, K2v, 3);
    dpq_insert(&q, 3, 4.0);
    if (q.cnt != 4) return 8;

    {
        int pk[8]; double pv[8]; double pb;
        int cnt = dpq_pull(&q, pk, pv, M, &pb);
        if (cnt < 1 || pk[0] != 1 || pv[0] > 3.0 + 1e-12) return 9;
    }

    /* pull bound should be correct */
    dpq_free(&q);
    dpq_init(&q, n, M, B);
    int K3k[5] = {0, 1, 2, 3, 4};
    double K3v[5] = {10.0, 20.0, 30.0, 40.0, 50.0};
    dpq_batch_prepend(&q, K3k, K3v, 5);
    {
        int pk[8]; double pv[8]; double pb;
        dpq_pull(&q, pk, pv, M, &pb);
        if (pb > 50.0 + 1e-12) return 10;
    }

    dpq_free(&q);
    return 0;
}


