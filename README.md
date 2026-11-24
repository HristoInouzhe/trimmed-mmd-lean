# Lean formalization of "Certifying total-variation contamination by betting on trimmed kernel witnesses"

This repository holds the Lean 4 formalization of the numbered results of the paper *Certifying total-variation
contamination by betting on trimmed kernel witnesses* by Hristo Inouzhe (Annals of Statistics submission). Every
numbered result of the main text and the supplement, 70 in all, is stated in Lean and proved with Mathlib. The code and
data behind the paper's tables and figures are at [github.com/HristoInouzhe/trimmed-mmd](https://github.com/HristoInouzhe/trimmed-mmd).

The map from the paper to the code is [docs/trimmed-mmd-aos.md](docs/trimmed-mmd-aos.md). It has one row for each printed
result, in the order of the paper. Each row gives the result's Lean name or names, what exactly is certified, and the
fidelity card that compares the formal statement with the printed one. The Lean names are declared in
[Papers/TrimmedMMDJMLR/TrimmedMMDJMLR.lean](Papers/TrimmedMMDJMLR/TrimmedMMDJMLR.lean) and
[Papers/TrimmedMMD/TrimmedMMD.lean](Papers/TrimmedMMD/TrimmedMMD.lean). Each one is a theorem whose type is the frozen
statement of the result.

## What "certified" means

A result is certified when four conditions hold:
- its formal statement is frozen, meaning its text is hash-locked in `certify/statements.lock`;
- a Lean theorem proves exactly that statement;
- the proof uses no `sorry` or other escape hatch;
- its axioms are only Lean's standard three: `propext`, `Classical.choice` and `Quot.sound`.

Whether a frozen statement says what the paper says is a separate question. A fidelity review answers it for each
result, and the review is recorded on the result's card in `certify/cards/`. [TRUST.md](TRUST.md) explains both checks
and how the reviews were done.

## Checking it

You need [elan](https://github.com/leanprover/elan). The toolchain and dependencies are pinned in `lean-toolchain` and
`lake-manifest.json`. Then run:

```
lake exe cache get                  # Mathlib's prebuilt files
python3 tools/certify.py check      # builds everything; prints CERTIFIED: <n> targets; statements frozen; axioms within [...]
python3 tools/check_aliases.py      # every paper name is literally a certified theorem under its frozen statement
```

## Where the files come from

The formalization was developed in a larger private repository that formalizes several papers. This repository is a
snapshot of it at commit `2382479`, and the Lean files are copied unchanged. It contains the files that the paper's
results need and everything those files import.

The proofs reuse some lemmas first proved for the author's other projects, so some folders under `StatFormal/Archive/`
come from those formalizations, for example `OTFD`, `RobustEquality` and `ICL`. They are included only because the
proofs here depend on them. Their statements are not results of this paper, and only the targets in
`certify/targets.toml` are certified here.

The other changes are:
- the two pages under `Papers/` keep only the names the paper cites;
- `StatFormal.lean` imports every module of the snapshot;
- `tools/check_aliases.py` names the two pages directly.

## Layout

- `Papers/` holds the paper names (aliases).
- `StatFormal/Archive/` holds the frozen statements (`Statements.lean`) and their proofs, grouped by the batch of work that produced them.
- `StatFormal/Lib/` holds general results used by the proofs.
- `certify/` holds the certified targets, the statement lock, the fidelity cards and the review method.
- `tools/` holds the certification check and the alias check.

## License

Apache License 2.0, the license of Mathlib (see [LICENSE](LICENSE)). Copyright 2026 Hristo Inouzhe.
