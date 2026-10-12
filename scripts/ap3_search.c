/*
 * Shortest 3-AP-free sets: for each n, the least N such that some
 * P subset of {0..N-1} with |P| = n contains no 3-term arithmetic progression
 * (equivalently: p_i + p_j = 2 p_k forces i = j = k). This is OEIS A065825
 * (N - 1 here is the largest element, A065825(n) = N).
 *
 * Exact branch and bound, using the subadditivity bound
 * r3(a + b) <= r3(a) + r3(b) on the remaining interval, with r3 values
 * computed bottom-up by this same search.
 *
 * Also reports, for the optimal set found first, |P + P| (the number of
 * Horner terms of the folded claim) and |P + P| - n (cross terms sent).
 *
 * Build: cc -O2 -o ap3_search ap3_search.c
 * Run:   ./ap3_search 30
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 512
static int r3[MAXN + 1]; /* r3[m] = max 3-AP-free subset size of {0..m-1} */
static int set[MAXN], best[MAXN];
static unsigned char in_set[2 * MAXN];
static int target, limitN, found;

static int ok(int x, int k) {
    /* x is larger than all elements; x completes a 3-AP iff 2*p - x in set
     * for some p in set, i.e. (q, p, x) with q = 2p - x. */
    for (int i = 0; i < k; i++) {
        int q = 2 * set[i] - x;
        if (q >= 0 && in_set[q]) return 0;
    }
    return 1;
}

static void dfs(int k, int next) {
    if (found) return;
    if (k == target) { found = 1; memcpy(best, set, sizeof(int) * k); return; }
    for (int x = next; x < limitN; x++) {
        /* bound: elements still placeable in {x..limitN-1} */
        if (k + r3[limitN - x] < target) return;
        if (!ok(x, k)) continue;
        set[k] = x; in_set[x] = 1;
        dfs(k + 1, x + 1);
        in_set[x] = 0;
        if (found) return;
    }
}

int main(int argc, char **argv) {
    int nmax = argc > 1 ? atoi(argv[1]) : 24;
    r3[0] = 0;
    int N = 1;
    printf("n  N(n)  maxelt  |P+P|  cross=|P+P|-n  n(n-1)  n(n-1)/2  set\n");
    for (int n = 1; n <= nmax; n++) {
        for (;; N++) {
            /* r3 values below N are final; try to fit n elements in [0,N) */
            target = n; limitN = N; found = 0;
            memset(in_set, 0, sizeof in_set);
            set[0] = 0; in_set[0] = 1; /* WLOG min element is 0 */
            if (n == 1) found = 1, best[0] = 0;
            else dfs(1, 1);
            if (found) break;
            r3[N] = n - 1; /* fits n-1 (inductively) but not n */
        }
        r3[N] = n;
        /* sumset */
        static unsigned char s[2 * MAXN];
        memset(s, 0, sizeof s);
        int ss = 0;
        for (int i = 0; i < n; i++)
            for (int j = i; j < n; j++)
                if (!s[best[i] + best[j]]) { s[best[i] + best[j]] = 1; ss++; }
        printf("%d  %d  %d  %d  %d  %d  %d  ", n, N, best[n - 1], ss, ss - n,
               n * (n - 1), n * (n - 1) / 2);
        for (int i = 0; i < n; i++) printf("%d%c", best[i], i + 1 < n ? ',' : '\n');
        fflush(stdout);
        N++; /* next n needs strictly larger N */
    }
    return 0;
}
