# prototype

The Lagrange revdot fold of `../paper.md`, Section 5.8, as a module
`lagrange` inside Ragu's `crates/ragu_pcd/src/internal/fold_revdot.rs`.

- `lagrange-fold.patch`: the change, against Ragu commit `526b0e3e` (main,
  2026-10-10). Adds 496 lines, touches no other file.
- `fold_revdot.rs`: the whole file after the patch, for reading.

## apply and run

From a Ragu checkout:

```sh
git checkout -b lagrange-fold-prototype 526b0e3e
git apply ~/codes/dannywillems/ragu-ai-prompt-folding/prototype/lagrange-fold.patch
cargo test -p ragu_pcd --lib fold_revdot
cargo test -p ragu_pcd --lib fold_revdot -- --nocapture gate_count  # 5k-2
```

Checked at the time: the 19 `fold_revdot` tests pass, clippy is clean with
`--all-features` and `--no-default-features`, `RUSTDOCFLAGS="-D warnings"
cargo doc` is clean, and the nightly rustfmt check passes.
