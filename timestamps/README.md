# Timestamps

[OpenTimestamps](https://opentimestamps.org) proofs for the assets of release `v1`.
Each proof commits to the SHA-256 of the file below and is anchored in Bitcoin block
970907 (2026-10-11 10:15:48 UTC).

| file | SHA-256 |
|---|---|
| `li2-integer-reciprocals-irrationality-v1.pdf` | `29483760da63387fd7a09fe87ed30a63fca11abd4fa82c2fa1f526a76548748f` |
| `li2-integer-reciprocals-irrationality-v1.tar.gz` | `479a56c60fb5dc1b35c3b938b80fb97092d2045b8cef0ff8db95726e5435e1cf` |

Proofs for the assets of release `v2` (pending Bitcoin confirmation):

| file | SHA-256 |
|---|---|
| `li2-integer-reciprocals-irrationality-v2.pdf` | `29483760da63387fd7a09fe87ed30a63fca11abd4fa82c2fa1f526a76548748f` |
| `li2-integer-reciprocals-irrationality-v2-lean.tar.gz` | `3fd72eff92ec168d0d26cae5ece1e4ecc961ed296302210c353d971b2fab97fa` |
| `li2-integer-reciprocals-irrationality-v2.tar.gz` | `5ea98fcdbf04f01c3e94c3d267907b80f0241110c7dd1f6a83388b3fb593dea2` |

To verify, download the release asset into this directory and run

    pip install opentimestamps-client
    ots verify timestamps/<file>.ots
