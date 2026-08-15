# ssort

Single-source shortest paths (SSSP) for directed graphs with non-negative
real edge weights, running in O(m log^{2/3} n) expected time.

Implementation of the algorithm from:

> R. Duan, J. Mao, X. Mao, X. Shu, L. Yin.
> *Breaking the Sorting Barrier for Directed Single-Source Shortest Paths.*
> STOC 2025. [arXiv:2504.17033](https://arxiv.org/abs/2504.17033)

## How it works

For graphs with fewer than 256 vertices `ssort()` runs plain Dijkstra.
For larger graphs it runs the paper's BMSSP as a *warm start* followed by an
exact multi-source Dijkstra pass seeded with the labels BMSSP produced.

BMSSP only ever sets labels that are valid upper bounds on the true
distance, so the final exact pass always returns correct distances and
predecessors regardless of BMSSP internals. The recursion levels and pull
sizes are parameterized as in the paper: k = log^{1/3} n, t = log^{2/3} n,
with saturated 64-bit bookkeeping so the paper's 2^{lt} bounds never
overflow on realistic inputs.

Space usage is O(n + m).

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

The test suite forces the BMSSP code path (n >= 256) with deep chains,
shortcut graphs, and all-zero-weight tie graphs. `make fuzz` runs a
differential fuzzer over random graphs (up to a few thousand vertices)
comparing against both oracles, and `make asan` repeats part of that under
AddressSanitizer and UndefinedBehaviorSanitizer.

## License

BSD 3-Clause. See [LICENSE](LICENSE).