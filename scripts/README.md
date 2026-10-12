# scripts

Every script used in `../paper.md`, with the exact commands. Outputs are in
`out/`. Python scripts use only the standard library.

| script | what it computes | paper section |
|---|---|---|
| `fold_check.py` | revdot folding under Ragu's, symmetric, and 3-AP-free monomial weights over the Pallas scalar field; honest folds, cross-term counts, and the "shift" forgery when a diagonal monomial collides | 5.2, Prop. 5.1 |
| `ap3_search.c` | exact shortest 3-AP-free sets (OEIS A065825), their sumset size, and cross terms sent | 5.2, table |
| `lagrange_fold.py` | Lagrange (ProtoGalaxy-style) folding of k revdot claims: k-1 cross terms, honest acceptance, rejection of a false claim, and the knowledge extractor from 2k-1 transcripts | 5.3, Props. 5.2, 5.5 |
| `weight_spaces.py` | dims of the weight space U, off-diagonal span O, and rank of the diagonal mod O for five schemes; soundness iff rank = k, cost = dim O | 5.4, Thm 5.3 |
| `layer_cost.py` | constraint and cross-term cost of 1-, 2- and 3-layer folds for each scheme, calibrated on the book's 1276 for (7,19) | 5.6, table |

## commands

Run from this directory.

```sh
python3 -I fold_check.py      | tee out/fold_check.txt
python3 -I lagrange_fold.py   | tee out/lagrange_fold.txt
python3 -I weight_spaces.py   | tee out/weight_spaces.txt  # ~5 s
python3 -I layer_cost.py      | tee out/layer_cost.txt   # optional arg: n

cc -O2 -o "$TMPDIR/ap3_search" ap3_search.c
"$TMPDIR/ap3_search" 27 | tee out/ap3_search.txt         # ~5 minutes to 27
```

`layer_cost.py` hard-codes the `ap3_search` results for k <= 26 (the `AP3`
table at the top); regenerate it from `out/ap3_search.txt` if the search is
extended.
