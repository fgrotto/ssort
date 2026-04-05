#ifndef SSORT_H
#define SSORT_H

#define SSORT_INFINITY 1e300

typedef struct {
    int     n;        /* vertices, 0-indexed */
    int     m;        /* edges added so far */
    int     cap;      /* allocated capacity for edge arrays */
    int    *eu;       /* edge sources, length cap */
    int    *ev;       /* edge targets, length cap */
    double *ew;       /* edge weights, length cap */
} SsortGraph;

SsortGraph *ssort_graph_new(int n, int m);
void        ssort_graph_free(SsortGraph *g);
int         ssort_graph_add_edge(SsortGraph *g, int u, int v, double w);

/* Compute shortest distances from src. dist and pred must hold n entries.
   Returns 0 on success. dist[v] = SSORT_INFINITY if unreachable. */
int ssort(const SsortGraph *g, int src, double *dist, int *pred);

#endif
