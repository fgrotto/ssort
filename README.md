# ssort

Single-source shortest paths (SSSP) for directed graphs with non-negative
real edge weights.

Implementation based on the algorithm from:

> R. Duan, J. Mao, X. Mao, X. Shu, L. Yin.
> *Breaking the Sorting Barrier for Directed Single-Source Shortest Paths.*
> STOC 2025. [arXiv:2504.17033](https://arxiv.org/abs/2504.17033)

## Build

    make            # build libssort.a and run the test suite
    make lib        # build libssort.a only
    make test       # build and run the test suite
    make fuzz       # build and run the differential fuzzer
    make asan       # unit tests + short fuzz run under ASan/UBSan

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
ssort(g, 0, dist, pred);        /* dist[3] == 2.0 */

ssort_graph_free(g);
```

## Correctness

Distances are checked against two independent oracles:

- a binary-heap Dijkstra, and
- Bellman-Ford (also catches negative-weight or float artifacts on small
  graphs).

The test suite forces the BMSSP code path with deep chains, shortcut
graphs, all-zero-weight tie graphs, and graphs with self-loops and parallel
edges. `make fuzz` runs a differential fuzzer over random graphs (up to a
few thousand vertices) comparing against both oracles, and `make asan`
repeats part of that under AddressSanitizer and UndefinedBehaviorSanitizer.

## License

BSD 3-Clause. See [LICENSE](LICENSE).
