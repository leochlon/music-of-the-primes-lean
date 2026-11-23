# The Music of the Primes: review and Lean formalisation

Issues, repairs and Lean proofs for A.&nbsp;M. Masullo's manuscript *The Music of the Primes*, from Hassana Labs.

[Write-up](https://hassana.io/music-of-the-primes/) · [Issues](ISSUES.md) · [Lean map](LEAN_MAP.md) · [Manifest](MANIFEST.tsv) · [Building](#building) · [Citation](#citation)

This repository accompanies our [review of the manuscript](https://hassana.io/music-of-the-primes/). It lists the 44 issues we found, 23 of them not raised in any public review, each with our repair and its status, and the nine results the argument relies on, with what is proved for each. For every item it gives the checked Lean declarations behind it, together with their sources and compiler receipts.

## Contents

| Path | What it is |
|---|---|
| [`ISSUES.md`](ISSUES.md) | The nine results the argument relies on and what is proved for each, then the 44 issues in manuscript order. Each issue has a description, the repair and its status, and a derivation. |
| [`LEAN_MAP.md`](LEAN_MAP.md) | For each result and each issue, the Lean declarations involved: what each proves, the objects it is about, its scope and its hypotheses. |
| [`MANIFEST.tsv`](MANIFEST.tsv) | All 1,302 declarations named in `LEAN_MAP.md`, with their status, source file and compiler receipts. |
| [`lean/`](lean/) | 494 Lean sources and 619 compiler receipts, grouped by area: `spectral`, `nuclearity`, `geometry`, `geometric-trace` and `final-deduction`. Each folder holds one source and its receipts, and its name ends with the first 12 hex digits of the source's SHA-256. |
| `lakefile.lean`, `lake-manifest.json`, `lean-toolchain` | The Lean project: Lean `v4.27.0-rc1` and Mathlib at commit `fdddb3ea2c8c35de4455e033bc2a5df4d3a391ee`. |
| [`LICENSE`](LICENSE), [`CITATION.cff`](CITATION.cff) | Licence and citation. |

Page numbers refer to the manuscript's PDF, whose page numbers match the printed ones.

## Status of a declaration

- **checked** (1,208 declarations): the source compiled with exit code 0, and `#print axioms` for the declaration lists only `propext`, `Classical.choice` and `Quot.sound`.
- **accepted by Lean (linter warnings only)** (25): Lean elaborated the declaration and printed the same three axioms. The compile service rejected the file only because it treats linter warnings, such as an unused `simp` argument, as errors.
- **in a checked file** (69): a definition or auxiliary lemma named in the map that has no `#print axioms` line of its own. It is part of a source file whose receipts are listed.

## Receipts

Each `receipt-<n>.json` records the compile request, the compiled target and theorem, the SHA-256 of the compiled source (`source_sha256`), the exit status, the elapsed time and the compiler output, which contains the `#check` and `#print axioms` lines. The SHA-256 of each source equals the value in its receipts:

```sh
shasum -a 256 lean/<area>/<folder>/<File>.lean
```

## Building

Every source imports only Mathlib. With [elan](https://github.com/leanprover/elan) installed:

```sh
git clone https://github.com/leochlon/music-of-the-primes-lean
cd music-of-the-primes-lean
lake exe cache get
lake env lean lean/<area>/<folder>/<File>.lean
```

Each source is a standalone compilation unit, and different sources may declare the same names, so compile them one at a time.

## Licence

Released under CC BY-NC 4.0; see [`LICENSE`](LICENSE).

## Citation

```bibtex
@misc{hassanalabs2026musicofprimes,
  author = {{Hassana Labs}},
  title  = {The Music of the Primes: review and Lean formalisation},
  year   = {2026},
  month  = nov,
  url    = {https://github.com/leochlon/music-of-the-primes-lean},
  note   = {Review of A. M. Masullo, \emph{The Music of the Primes}}
}
```
