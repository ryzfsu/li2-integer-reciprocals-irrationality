# Li2(1/n) Lean Release Candidate

This history-free source package is built from commit
`f9768a9c1db0f24ef5cef62a5ada4642e6c89524`. It contains the import closure of
`Solution.lean` (1603 modules) together with the two public theorem files and
the release verification records.

## Reproduce the build

Use the Lean toolchain named by `lean-toolchain` and the Mathlib revision in
`lake-manifest.json`:

```bash
lake exe cache get
lake build Solution Challenge
lake env lean SolutionAxioms.lean
```

Tool versions used for the recorded checks: Lean `v4.35.0-rc4` (see
`lean-toolchain`), lean4export 3.1.0, comparator at upstream commit `ca04cfc`
(built for Lean v4.35.0-rc4), and nanoda 0.4.19 (binary SHA-256
`cbf13950fc4a48f635a0beceeb5ed32dd82568b870cfd081b6391c1f2cf02ba5`).

The last command must report exactly:

```text
'li2_inv_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Comparator and nanoda

The Lean-kernel comparator and nanoda are independent checks. The comparator
configuration is `verification/comparator-leankernel.json`; run it with the
comparator executable after the build:

```bash
comparator verification/comparator-leankernel.json
```

Export the Solution declarations and run nanoda separately:

```bash
BASE="Quot Quot.mk Quot.lift Quot.ind li2_inv_irrational propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String Char optParam autoParam semiOutParam outParam"
lean4export Solution -- $BASE | zstd -T4 -3 -q -o solution.ndjson.zst
# The recorded nanoda receipt used the equivalent export
#   lean4export Solution -- li2_inv_irrational
# whose closure contains the same declarations needed by li2_inv_irrational.
zstd -dc solution.ndjson.zst | nanoda_bin verification/nanoda.json
```

The package records the exact input hashes and commands in
`verification/comparator-receipt.json` and
`verification/nanoda-receipt.json`, together with the recorded results:
nanoda and comparator both passed on the release commit. Comparator also
passed earlier on the first frozen commit, which differs from the release
commit only in the proofs of three declarations, with identical statements.

## Notes on source comments

Some source comments describe the development history and are not updated in
this release, so that every Lean file is byte-identical to the release commit:

- `Li2Lean/V/NegativeTwoSeed.lean`: the comment before `vTwoSeed_matrix_explicit`
  says the determinant "remains a pending input". It is proved in the same file
  (`vTwoSeed_det_zero`, by an explicit LU factorisation modulo 11).
- `Li2Lean/B4/NegativeContourTyped.lean` and `Li2Lean/B4/NegativeContourProducer.lean`:
  comments call the negative contour estimate "open" or "unresolved". The
  interface `HpNegContourProducerInput` is instantiated by
  `hpNegContourInputs_producer` in `Li2Lean/AllN/Producers.lean`, which is part
  of the proof of `li2_inv_irrational`.
- Comments of the form "not yet proved" or "contract" describe structures whose
  fields are supplied by later producers; the final theorem depends only on
  `propext`, `Classical.choice` and `Quot.sound`.

## Source and statement checks

`verification/closure-modules.txt` and `verification/source-closure.txt`
describe the complete Solution import closure. The normalized statement hash
for both `Challenge.lean` and `Solution.lean` is recorded in
`verification/statement-identity.json`.

`RELEASE_NOTES.md` records the certificate differences from v13 and the
alpha-6 erratum.
