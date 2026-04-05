# ssort

O(m log^{2/3} n) single-source shortest paths for directed graphs
with non-negative real edge weights.

Implementation of the algorithm from:

> R. Duan, J. Mao, X. Mao, X. Shu, L. Yin.
> *Breaking the Sorting Barrier for Directed Single-Source Shortest Paths.*
> STOC 2025. [arXiv:2504.17033](https://arxiv.org/abs/2504.17033)

## Build

    make            # build library and run tests
    make lib        # build libssort.a only
    make test       # build and run tests

## Usage

```c
#include "ssort.h"

SsortGraph *g = ssort_graph_new(4, 4);
ssort_graph_add_edge(g, 0, 1, 1.0);
ssort_graph_add_edge(g, 1, 2, 1.0);
ssort_graph_add_edge(g, 0, 2, 3.0);
ssort_graph_add_edge(g, 2, 3, 1.0);

double dist[4];
int    pred[4];
ssort(g, 0, dist, pred);

ssort_graph_free(g);
```

Link with `-lssort -lm`.

## License

BSD 3-Clause. See [LICENSE](LICENSE).
