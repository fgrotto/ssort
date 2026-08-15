/* Differential fuzzer: ssort() vs Dijkstra vs Bellman-Ford on the BMSSP path.
 * Usage: fuzz [seed] [iters] [maxn]
 */
#include "ssort.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { int *off, *adj; double *wgt; int n, m; } G;

static G build_g(int n, int *eu, int *ev, double *ew, int m) {
    G g; g.n = n; g.m = m;
    g.off = calloc((size_t)n + 1, sizeof(int));
    g.adj = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    g.wgt = malloc(sizeof(double) * (size_t)(m > 0 ? m : 1));
    for (int i = 0; i < m; i++) g.off[eu[i] + 1]++;
    for (int i = 1; i <= n; i++) g.off[i] += g.off[i - 1];
    int *cur = malloc(sizeof(int) * (size_t)n);
    memcpy(cur, g.off, sizeof(int) * (size_t)n);
    for (int i = 0; i < m; i++) { int p = cur[eu[i]]++; g.adj[p] = ev[i]; g.wgt[p] = ew[i]; }
    free(cur);
    return g;
}

static void free_g(G *g) { free(g->off); free(g->adj); free(g->wgt); }

/* reference Dijkstra, binary heap */
typedef struct { int *keys; double *vals; int *pos; int n, cap; } RH;
static void rh_init(RH *h, int cap) {
    h->keys = malloc(sizeof(int) * (size_t)cap);
    h->vals = malloc(sizeof(double) * (size_t)cap);
    h->pos  = malloc(sizeof(int) * (size_t)cap);
    h->n = 0; h->cap = cap;
    for (int i = 0; i < cap; i++) h->pos[i] = -1;
}
static void rh_free(RH *h) { free(h->keys); free(h->vals); free(h->pos); }
static void rh_swap(RH *h, int i, int j) {
    int tk = h->keys[i]; double tv = h->vals[i];
    h->keys[i] = h->keys[j]; h->vals[i] = h->vals[j];
    h->keys[j] = tk; h->vals[j] = tv;
    h->pos[h->keys[i]] = i; h->pos[h->keys[j]] = j;
}
static void rh_up(RH *h, int i) {
    while (i > 0) { int p = (i - 1) / 2;
        if (h->vals[i] < h->vals[p]) { rh_swap(h, i, p); i = p; } else break; }
}
static void rh_down(RH *h, int i) {
    for (;;) { int l = 2*i+1, r = 2*i+2, s = i;
        if (l < h->n && h->vals[l] < h->vals[s]) s = l;
        if (r < h->n && h->vals[r] < h->vals[s]) s = r;
        if (s != i) { rh_swap(h, i, s); i = s; } else break; }
}
static void rh_push(RH *h, int k, double v) {
    if (h->pos[k] != -1) { int i = h->pos[k];
        if (v < h->vals[i]) { h->vals[i] = v; rh_up(h, i); } return; }
    int i = h->n++;
    h->keys[i] = k; h->vals[i] = v; h->pos[k] = i; rh_up(h, i);
}
static int rh_pop(RH *h, double *v) {
    if (!h->n) return -1;
    int k = h->keys[0]; *v = h->vals[0]; h->pos[k] = -1;
    h->n--;
    if (h->n) { h->keys[0] = h->keys[h->n]; h->vals[0] = h->vals[h->n];
                h->pos[h->keys[0]] = 0; rh_down(h, 0); }
    return k;
}

static void ref_dijkstra(G *g, int src, double *d) {
    for (int i = 0; i < g->n; i++) d[i] = SSORT_INFINITY;
    d[src] = 0.0;
    RH h; rh_init(&h, g->n);
    rh_push(&h, src, 0.0);
    while (h.n) {
        double du; int u = rh_pop(&h, &du);
        if (du > d[u]) continue;
        for (int e = g->off[u]; e < g->off[u + 1]; e++) {
            int v = g->adj[e];
            if (du + g->wgt[e] < d[v]) { d[v] = du + g->wgt[e]; rh_push(&h, v, d[v]); }
        }
    }
    rh_free(&h);
}

/* reference Bellman-Ford (only used for small n) */
static void ref_bellman_ford(G *g, int src, double *d) {
    for (int i = 0; i < g->n; i++) d[i] = SSORT_INFINITY;
    d[src] = 0.0;
    for (int iter = 0; iter < g->n - 1; iter++) {
        int changed = 0;
        for (int u = 0; u < g->n; u++) {
            if (d[u] == SSORT_INFINITY) continue;
            for (int e = g->off[u]; e < g->off[u + 1]; e++) {
                int v = g->adj[e];
                if (d[u] + g->wgt[e] < d[v]) { d[v] = d[u] + g->wgt[e]; changed = 1; }
            }
        }
        if (!changed) break;
    }
}

static unsigned rng_state;
static unsigned rng(void) { return (rng_state = rng_state * 1664525u + 1013904223u); }

static int check(long seed, int iter, int n, int m, int *eu, int *ev, double *ew,
                 double *ds, double *dd, double *db) {
    int bad = 0;
    for (int i = 0; i < n; i++) {
        if (ds[i] != dd[i]) {
            printf("seed=%ld iter=%d n=%d m=%d: MISMATCH vs dijkstra v%d: ssort=%.17g want=%.17g\n",
                   seed, iter, n, m, i, ds[i], dd[i]);
            bad = 1;
        }
        if (db && ds[i] != db[i]) {
            printf("seed=%ld iter=%d n=%d m=%d: MISMATCH vs bf v%d: ssort=%.17g want=%.17g\n",
                   seed, iter, n, m, i, ds[i], db[i]);
            bad = 1;
        }
    }
    if (bad) {
        printf("edges (src=0):\n");
        for (int i = 0; i < m; i++) printf("  %d %d %.17g\n", eu[i], ev[i], ew[i]);
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    long seed = argc > 1 ? atol(argv[1]) : 1;
    int iters = argc > 2 ? atoi(argv[2]) : 60;
    int maxn = argc > 3 ? atoi(argv[3]) : 6000;
    rng_state = (unsigned)seed;
    for (int iter = 0; iter < iters; iter++) {
        int which = rng() % 5;
        int n = which == 0 ? 256 + rng() % 50
            : which == 1 ? 256 + rng() % 300
            : which == 2 ? 500 + rng() % 1000
            : which == 3 ? 3000 + rng() % 1000
            : 4000 + rng() % (maxn > 4000 ? maxn - 4000 : 1);
        int wmode = rng() % 4;
        int m = 0;
        int cap = n * 16 + 16;
        int *eu = malloc(sizeof(int) * (size_t)cap);
        int *ev = malloc(sizeof(int) * (size_t)cap);
        double *ew = malloc(sizeof(double) * (size_t)cap);

        /* sparse-ish random edges plus a few structured patterns */
        int extra = 2 * n + rng() % (3 * n);
        for (int d = 0; d < extra; d++) {
            int u = (int)(rng() % (unsigned)n), v = (int)(rng() % (unsigned)n);
            if (u == v) v = (v + 1) % n;
            double w;
            switch (wmode) {
                case 0: w = 0.0; break;
                case 1: w = (double)(rng() % 3); break;
                case 2: w = (rng() % 1000) / 10.0 + 0.01; break;
                default: w = (double)(1 + rng() % 100000); break;
            }
            eu[m] = u; ev[m] = v; ew[m] = w; m++;
        }
        /* chains with shortcut edges (kills naive two-edge ball stops) */
        for (int i = 1; i < n; i++) {
            if (rng() % 2) { eu[m] = i - 1; ev[m] = i; ew[m] = 0.5 + (rng() % 4) / 10.0; m++; }
        }
        if (rng() % 2 && n > 3) {   /* shortcut over a long chain */
            int a = (int)(rng() % (unsigned)(n / 4));
            int b = (int)(rng() % (unsigned)(n / 4)) + n - n / 4;
            eu[m] = a; ev[m] = b; ew[m] = 0.05; m++;
        }

        SsortGraph *sg = ssort_graph_new(n, m);
        for (int i = 0; i < m; i++) ssort_graph_add_edge(sg, eu[i], ev[i], ew[i]);
        double *ds = malloc(sizeof(double) * (size_t)n);
        int *pred = malloc(sizeof(int) * (size_t)n);
        double *dd = malloc(sizeof(double) * (size_t)n);
        double *db = NULL;
        ssort(sg, 0, ds, pred);

        G g = build_g(n, eu, ev, ew, m);
        ref_dijkstra(&g, 0, dd);
        if (n <= 1200) { db = malloc(sizeof(double) * (size_t)n); ref_bellman_ford(&g, 0, db); }
        int bad = check(seed, iter, n, m, eu, ev, ew, ds, dd, db);
        free_g(&g);
        free(ds); free(dd); free(pred); free(db);
        free(eu); free(ev); free(ew);
        ssort_graph_free(sg);
        if (bad) return 1;
        if (iter % 10 == 0) fprintf(stderr, "iter %d ok (n=%d m=%d)\n", iter, n, m);
    }
    printf("fuzz clean: %d iters\n", iters);
    return 0;
}
