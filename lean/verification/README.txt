The release checks are independent.

1. Run `lake exe cache get` and `lake build Solution Challenge`.
2. Run `lake env lean SolutionAxioms.lean` and compare the output with
   `axioms.txt`.
3. Run `comparator verification/comparator-leankernel.json`.
4. Export `Solution` with `lean4export`, then pipe the compressed export to
   `nanoda_bin verification/nanoda.json`.

The comparator and nanoda receipt files contain their source commit, exact
configuration, command, and input SHA-256. A `pending` status means that the
corresponding independent run has not yet been recorded.
