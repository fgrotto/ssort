/* test_ssort.c — hand-written tests with Dijkstra and Bellman-Ford oracles. */

#include "ssort.h"
#include <assert.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TEST(name) static void name(void)
#define RUN(name)                                                             \
    do {                                                                      \
        printf("  %-50s ", #name);                                            \
        name();                                                               \
        puts("ok");                                                           \
    } while (0)
#define ASSERT(cond)                                                          \
    do {                                                                      \
        if (!(cond)) {                                                        \
            fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond);  \
            exit(1);                                                          \
        }                                                                     \
    } while (0)

/* ─── Local CSR for reference implementations ───────────────────── */

typedef struct {
    int n, m;
    int *off, *adj;
    double *wgt;
} LCSR;

static void lcsr_build(LCSR *c, const SsortGraph *g) {
    c->n = g->n; c->m = g->m;
    c->off = calloc(c->n + 1, sizeof(int));
    c->adj = malloc(sizeof(int) * (c->m > 0 ? c->m : 1));
    c->wgt = malloc(sizeof(double) * (c->m > 0 ? c->m : 1));
    for (int i = 0; i < g->m; i++) c->off[g->eu[i] + 1]++;
    for (int i = 1; i <= c->n; i++) c->off[i] += c->off[i-1];
    int *cur = calloc(c->n, sizeof(int));
    memcpy(cur, c->off, sizeof(int) * c->n);
    for (int i = 0; i < g->m; i++) {
        int p = cur[g->eu[i]]++;
        c->adj[p] = g->ev[i];
        c->wgt[p] = g->ew[i];
    }
    free(cur);
}

static void lcsr_free(LCSR *c) { free(c->off); free(c->adj); free(c->wgt); }

/* ─── Reference: Dijkstra (binary heap) ──────────────────────────── */

typedef struct {
    int    *keys;
    double *vals;
    int    *pos;
    int     n, cap;
} RefHeap;

static void rh_init(RefHeap *h, int cap) {
    h->keys = malloc(sizeof(int) * cap);
    h->vals = malloc(sizeof(double) * cap);
    h->pos  = malloc(sizeof(int) * cap);
    h->n = 0; h->cap = cap;
    for (int i = 0; i < cap; i++) h->pos[i] = -1;
}
static void rh_free(RefHeap *h) { free(h->keys); free(h->vals); free(h->pos); }
static void rh_swap(RefHeap *h, int i, int j) {
    int tk = h->keys[i]; double tv = h->vals[i];
    h->keys[i] = h->keys[j]; h->vals[i] = h->vals[j];
    h->keys[j] = tk; h->vals[j] = tv;
    h->pos[h->keys[i]] = i; h->pos[h->keys[j]] = j;
}
static void rh_up(RefHeap *h, int i) {
    while (i > 0) {
        int p = (i - 1) / 2;
        if (h->vals[i] < h->vals[p]) { rh_swap(h, i, p); i = p; } else break;
    }
}
static void rh_down(RefHeap *h, int i) {
    for (;;) {
        int l = 2*i+1, r = 2*i+2, s = i;
        if (l < h->n && h->vals[l] < h->vals[s]) s = l;
        if (r < h->n && h->vals[r] < h->vals[s]) s = r;
        if (s != i) { rh_swap(h, i, s); i = s; } else break;
    }
}
static void rh_push(RefHeap *h, int k, double v) {
    if (h->pos[k] != -1) {
        int i = h->pos[k];
        if (v < h->vals[i]) { h->vals[i] = v; rh_up(h, i); }
        return;
    }
    int i = h->n++;
    h->keys[i] = k; h->vals[i] = v; h->pos[k] = i;
    rh_up(h, i);
}
static int rh_pop(RefHeap *h, double *v) {
    if (!h->n) return -1;
    int k = h->keys[0]; *v = h->vals[0]; h->pos[k] = -1;
    h->n--;
    if (h->n) { h->keys[0] = h->keys[h->n]; h->vals[0] = h->vals[h->n];
                h->pos[h->keys[0]] = 0; rh_down(h, 0); }
    return k;
}

static void ref_dijkstra(const SsortGraph *g, int src, double *dist) {
    LCSR c; lcsr_build(&c, g);
    RefHeap h; rh_init(&h, c.n);
    for (int i = 0; i < c.n; i++) dist[i] = SSORT_INFINITY;
    dist[src] = 0.0;
    rh_push(&h, src, 0.0);
    while (h.n) {
        double du; int u = rh_pop(&h, &du);
        if (du > dist[u]) continue;
        for (int e = c.off[u]; e < c.off[u+1]; e++) {
            int v = c.adj[e]; double w = c.wgt[e];
            if (du + w < dist[v]) { dist[v] = du + w; rh_push(&h, v, dist[v]); }
        }
    }
    rh_free(&h); lcsr_free(&c);
}

/* ─── Reference: Bellman-Ford ────────────────────────────────────── */

static void ref_bellman_ford(const SsortGraph *g, int src, double *dist) {
    LCSR c; lcsr_build(&c, g);
    for (int i = 0; i < c.n; i++) dist[i] = SSORT_INFINITY;
    dist[src] = 0.0;
    for (int iter = 0; iter < c.n - 1; iter++) {
        int changed = 0;
        for (int u = 0; u < c.n; u++) {
            if (dist[u] == SSORT_INFINITY) continue;
            for (int e = c.off[u]; e < c.off[u+1]; e++) {
                int v = c.adj[e]; double w = c.wgt[e];
                if (dist[u] + w < dist[v]) { dist[v] = dist[u] + w; changed = 1; }
            }
        }
        if (!changed) break;
    }
    lcsr_free(&c);
}

/* ─── Helpers ────────────────────────────────────────────────────── */

static void compare_all(const SsortGraph *g,
                        const double *ds, const double *dd, const double *db) {
    for (int i = 0; i < g->n; i++) {
        if (ds[i] != dd[i]) {
            fprintf(stderr, "  MISMATCH vs dijkstra at v%d: ssort=%.6f dij=%.6f\n",
                    i, ds[i], dd[i]);
            exit(1);
        }
        if (ds[i] != db[i]) {
            fprintf(stderr, "  MISMATCH vs bellman-ford at v%d: ssort=%.6f bf=%.6f\n",
                    i, ds[i], db[i]);
            exit(1);
        }
    }
}

/* ─── Tests ──────────────────────────────────────────────────────── */

TEST(test_single_vertex) {
    SsortGraph *g = ssort_graph_new(1, 0);
    double dist[1]; int pred[1];
    ssort(g, 0, dist, pred);
    ASSERT(dist[0] == 0.0);
    ASSERT(pred[0] == -1);
    ssort_graph_free(g);
}

TEST(test_single_edge) {
    SsortGraph *g = ssort_graph_new(2, 1);
    ssort_graph_add_edge(g, 0, 1, 2.5);
    double ds[2], dd[2], db[2]; int pred[2];
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    ref_bellman_ford(g, 0, db);
    compare_all(g, ds, dd, db);
    ASSERT(pred[1] == 0);
    ssort_graph_free(g);
}

TEST(test_diamond) {
    SsortGraph *g = ssort_graph_new(4, 4);
    ssort_graph_add_edge(g, 0, 1, 1.0);
    ssort_graph_add_edge(g, 0, 2, 1.0);
    ssort_graph_add_edge(g, 1, 3, 1.0);
    ssort_graph_add_edge(g, 2, 3, 1.0);
    double ds[4], dd[4], db[4]; int pred[4];
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    ref_bellman_ford(g, 0, db);
    compare_all(g, ds, dd, db);
    ASSERT(ds[3] == 2.0);
    ssort_graph_free(g);
}

TEST(test_chain) {
    SsortGraph *g = ssort_graph_new(5, 4);
    ssort_graph_add_edge(g, 0, 1, 1.0);
    ssort_graph_add_edge(g, 1, 2, 2.0);
    ssort_graph_add_edge(g, 2, 3, 3.0);
    ssort_graph_add_edge(g, 3, 4, 4.0);
    double ds[5], dd[5], db[5]; int pred[5];
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    ref_bellman_ford(g, 0, db);
    compare_all(g, ds, dd, db);
    ASSERT(ds[4] == 10.0);
    ssort_graph_free(g);
}

TEST(test_zero_weight) {
    SsortGraph *g = ssort_graph_new(3, 2);
    ssort_graph_add_edge(g, 0, 1, 0.0);
    ssort_graph_add_edge(g, 1, 2, 0.0);
    double ds[3], dd[3], db[3]; int pred[3];
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    ref_bellman_ford(g, 0, db);
    compare_all(g, ds, dd, db);
    ASSERT(ds[2] == 0.0);
    ssort_graph_free(g);
}

TEST(test_unreachable) {
    SsortGraph *g = ssort_graph_new(4, 2);
    ssort_graph_add_edge(g, 0, 1, 1.0);
    ssort_graph_add_edge(g, 2, 3, 1.0);
    double ds[4], dd[4], db[4]; int pred[4];
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    ref_bellman_ford(g, 0, db);
    compare_all(g, ds, dd, db);
    ASSERT(ds[2] == SSORT_INFINITY);
    ASSERT(ds[3] == SSORT_INFINITY);
    ssort_graph_free(g);
}

TEST(test_star) {
    int n = 5;
    SsortGraph *g = ssort_graph_new(n, n - 1);
    for (int i = 1; i < n; i++)
        ssort_graph_add_edge(g, 0, i, 1.0);
    double ds[5], dd[5], db[5]; int pred[5];
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    ref_bellman_ford(g, 0, db);
    compare_all(g, ds, dd, db);
    ssort_graph_free(g);
}

TEST(test_multi_path) {
    SsortGraph *g = ssort_graph_new(4, 5);
    ssort_graph_add_edge(g, 0, 1, 1.0);
    ssort_graph_add_edge(g, 0, 2, 5.0);
    ssort_graph_add_edge(g, 1, 2, 1.0);
    ssort_graph_add_edge(g, 1, 3, 2.0);
    ssort_graph_add_edge(g, 2, 3, 1.0);
    double ds[4], dd[4], db[4]; int pred[4];
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    ref_bellman_ford(g, 0, db);
    compare_all(g, ds, dd, db);
    ASSERT(ds[2] == 2.0);
    ASSERT(ds[3] == 3.0);
    ssort_graph_free(g);
}

TEST(test_complete_k4) {
    int n = 4;
    SsortGraph *g = ssort_graph_new(n, n * (n - 1));
    double w = 1.0;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
            if (i != j) ssort_graph_add_edge(g, i, j, w++);
    double ds[4], dd[4], db[4]; int pred[4];
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    ref_bellman_ford(g, 0, db);
    compare_all(g, ds, dd, db);
    ssort_graph_free(g);
}

TEST(test_cycle) {
    SsortGraph *g = ssort_graph_new(4, 5);
    ssort_graph_add_edge(g, 0, 1, 1.0);
    ssort_graph_add_edge(g, 1, 2, 1.0);
    ssort_graph_add_edge(g, 2, 3, 1.0);
    ssort_graph_add_edge(g, 3, 1, 1.0);
    ssort_graph_add_edge(g, 0, 3, 5.0);
    double ds[4], dd[4], db[4]; int pred[4];
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    ref_bellman_ford(g, 0, db);
    compare_all(g, ds, dd, db);
    ssort_graph_free(g);
}

TEST(test_dense_small) {
    int n = 20;
    SsortGraph *g = ssort_graph_new(n, 0);
    srand(42);
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
            if (i != j && (rand() % 3 == 0))
                ssort_graph_add_edge(g, i, j, (double)(rand() % 100) / 10.0 + 0.1);
    double *ds = malloc(sizeof(double) * n);
    double *dd = malloc(sizeof(double) * n);
    double *db = malloc(sizeof(double) * n);
    int *pred = malloc(sizeof(int) * n);
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    ref_bellman_ford(g, 0, db);
    compare_all(g, ds, dd, db);
    free(ds); free(dd); free(db); free(pred);
    ssort_graph_free(g);
}

TEST(test_medium_random) {
    int n = 200;
    SsortGraph *g = ssort_graph_new(n, 0);
    srand(123);
    for (int i = 0; i < 800; i++) {
        int u = rand() % n, v = rand() % n;
        if (u != v)
            ssort_graph_add_edge(g, u, v, (double)(rand() % 1000) / 100.0 + 0.01);
    }
    double *ds = malloc(sizeof(double) * n);
    double *dd = malloc(sizeof(double) * n);
    int *pred = malloc(sizeof(int) * n);
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    for (int i = 0; i < n; i++) {
        if (ds[i] != dd[i]) {
            fprintf(stderr, "  MISMATCH at v%d: ssort=%.6f dij=%.6f\n", i, ds[i], dd[i]);
            exit(1);
        }
    }
    free(ds); free(dd); free(pred);
    ssort_graph_free(g);
}

/* ─── BMSSP-path tests (n >= 256 exercises the n>=256 algorithm) ── */

static void check_pred_path(const SsortGraph *g, int src, const double *ds,
                            const int *pred) {
    LCSR c; lcsr_build(&c, g);
    for (int i = 0; i < c.n; i++) {
        if (ds[i] == SSORT_INFINITY) continue;
        if (i == src) { ASSERT(pred[i] == -1); continue; }
        ASSERT(pred[i] >= 0 && pred[i] < c.n);
        /* dist[pred[i]] + w(pred[i],i) == dist[i] must hold */
        int p = pred[i], ok = 0;
        for (int e = c.off[p]; e < c.off[p+1]; e++)
            if (c.adj[e] == i && fabs(ds[p] + c.wgt[e] - ds[i]) < 1e-9)
                ok = 1;
        ASSERT(ok);
    }
    lcsr_free(&c);
}

TEST(test_bmssp_chain2) {
    /* n=257 linear chain with unit weights: equal-label relaxations must
       propagate through the BMSSP path. */
    int n = 257;
    SsortGraph *g = ssort_graph_new(n, n - 1);
    for (int i = 0; i < n - 1; i++) ssort_graph_add_edge(g, i, i + 1, 1.0);
    double *ds = malloc(sizeof(double) * n);
    double *dd = malloc(sizeof(double) * n);
    int *pred = malloc(sizeof(int) * n);
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    compare_all(g, ds, dd, dd);
    ASSERT(ds[n - 1] == (double)(n - 1));
    check_pred_path(g, 0, ds, pred);
    free(ds); free(dd); free(pred);
    ssort_graph_free(g);
}

TEST(test_bmssp_shortcut) {
    /* n=3000 with a short-cut path (0->2->3->1, w1) beating the direct
       edge 0->1 (w10): the BMSSP path must return d[1]=3, d[3]=2. */
    int n = 3000;
    SsortGraph *g = ssort_graph_new(n, 4);
    ssort_graph_add_edge(g, 0, 1, 10.0);
    ssort_graph_add_edge(g, 0, 2, 1.0);
    ssort_graph_add_edge(g, 2, 3, 1.0);
    ssort_graph_add_edge(g, 3, 1, 1.0);
    double *ds = malloc(sizeof(double) * n);
    double *dd = malloc(sizeof(double) * n);
    int *pred = malloc(sizeof(int) * n);
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    compare_all(g, ds, dd, dd);
    ASSERT(ds[1] == 3.0);
    ASSERT(ds[3] == 2.0);
    check_pred_path(g, 0, ds, pred);
    free(ds); free(dd); free(pred);
    ssort_graph_free(g);
}

TEST(test_bmssp_zero_weight) {
    /* All-zero-weight reachable component: distances tie, so this stresses
       the BMSSP tie handling; must terminate and stay exact. */
    int n = 700;
    SsortGraph *g = ssort_graph_new(n, 0);
    for (int i = 1; i < n; i++) ssort_graph_add_edge(g, i - 1, i, 0.0);
    for (int i = 0; i < 2 * n; i++) {
        int u = rand() % n, v = rand() % n;
        if (u != v) ssort_graph_add_edge(g, u, v, 0.0);
    }
    double *ds = malloc(sizeof(double) * n);
    double *dd = malloc(sizeof(double) * n);
    int *pred = malloc(sizeof(int) * n);
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    compare_all(g, ds, dd, dd);
    for (int i = 0; i < n; i++) ASSERT(ds[i] == 0.0);
    check_pred_path(g, 0, ds, pred);
    free(ds); free(dd); free(pred);
    ssort_graph_free(g);
}

TEST(test_bmssp_big_random) {
    /* Random directed graph with varied weights, exercising the full BMSSP
       recursion depth (n large enough for k>=2). */
    int n = 5000;
    SsortGraph *g = ssort_graph_new(n, 0);
    srand(2024);
    for (int i = 0; i < 5 * n; i++) {
        int u = rand() % n, v = rand() % n;
        if (u != v) {
            int wm = rand() % 3;
            double w = wm == 0 ? 0.0
                     : wm == 1 ? (double)(rand() % 3)
                     : (double)(rand() % 100000) / 100.0 + 0.01;
            ssort_graph_add_edge(g, u, v, w);
        }
    }
    double *ds = malloc(sizeof(double) * n);
    double *dd = malloc(sizeof(double) * n);
    int *pred = malloc(sizeof(int) * n);
    ssort(g, 0, ds, pred);
    ref_dijkstra(g, 0, dd);
    compare_all(g, ds, dd, dd);
    check_pred_path(g, 0, ds, pred);
    free(ds); free(dd); free(pred);
    ssort_graph_free(g);
}

/* ─── Main ───────────────────────────────────────────────────────── */

int main(void) {
    puts("ssort tests:");
    RUN(test_single_vertex);
    RUN(test_single_edge);
    RUN(test_diamond);
    RUN(test_chain);
    RUN(test_zero_weight);
    RUN(test_unreachable);
    RUN(test_star);
    RUN(test_multi_path);
    RUN(test_complete_k4);
    RUN(test_cycle);
    RUN(test_dense_small);
    RUN(test_medium_random);
    RUN(test_bmssp_chain2);
    RUN(test_bmssp_shortcut);
    RUN(test_bmssp_zero_weight);
    RUN(test_bmssp_big_random);
    puts("all tests passed.");
    return 0;
}
