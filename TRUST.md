# What "certified" means here

## The claim
Each entry of `certify/targets.toml` gives a paper, a label, a module, a claim, a theorem and a card. For every entry,
`python3 tools/certify.py check` verifies four things.

1. **The statement is frozen.** Each `StatFormal/**/Statements.lean` file is the trusted specification: definitions, and
   claims stated as `Prop`s. Its SHA-256 must match the one recorded in `certify/statements.lock` when it was approved.
   The same holds for every local file it imports, transitively, because a definition used by a claim is part of the
   specification.
2. **There are no escape hatches.** Statement files contain no `sorry`, `axiom`, `opaque`, `implemented_by` or
   `extern`. Proof files contain no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`,
   `debug.skipKernelTC` or `unsafe`.
3. **It builds.** `lake build` succeeds with the pinned toolchain (`lean-toolchain`) and dependencies
   (`lake-manifest.json`).
4. **The theorem proves exactly the frozen claim.** For every target, `example : <claim> := <theorem>` typechecks, so
   the theorem proves the claim itself and not a variant of it. `#print axioms <theorem>` lists only **propext,
   Classical.choice, Quot.sound**, Lean's standard axioms.

On this repository the check prints `CERTIFIED: 197 targets`. The 197 entries cover 191 distinct theorems, because a
few theorems are listed under two labels.

## What it does not claim
The check does not verify that a frozen statement says what the paper says. That is the job of the **fidelity
review**, recorded on each card in `certify/cards/`. A card records:
- the deviations from the printed result (generalization, specialization, conditionalization);
- the junk-value audit (division by zero, `toReal ∞`, `sInf ∅`, `Measure.map` of a non-measurable map, and similar);
- a back-translation of the formal statement into words.

[docs/trimmed-mmd-aos.md](docs/trimmed-mmd-aos.md) states, for each printed result, what exactly is certified.

## AI fidelity audit and automatic approval (disclosure)
An independent AI reviewer (Claude), separate from the agents that drafted the statements, carried out the fidelity
reviews. The written method is `certify/AUDIT_METHOD.md`. It consists of:
- a blind back-translation of each frozen claim;
- a clause-by-clause comparison with the printed result;
- a checklist covering junk values, vacuity, smuggled hypotheses, quantifier order, undeclared stronger hypotheses and
  labels.

**The author decided on 2026-10-21 that a card whose review passes under this method is approved automatically.**
Every such card carries the line `**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**`

The header of `tools/certify.py` describes the statements as written or approved by a human. Here they were drafted and
frozen in the workflow just described, and the author's approval is the automatic one. Thirty-one entries of
`certify/statements.lock` were frozen on 2026-10-13 and 2026-10-14, before that decision, and still carry the note
"author review pending".

## Paper aliases
The files `Papers/<Paper>/<Paper>.lean` give each certified target a stable name of the form
`theorem <alias> : <claim> := <theorem>`. `python3 tools/check_aliases.py` verifies that every alias is literally a
certified (claim, theorem) pair and that every target has an alias.

## Provenance
This repository is a snapshot of the author's development repository at commit `2382479`. Every file under
`StatFormal/` is copied unchanged, and [README.md](README.md) lists the files outside it that differ. The certified
material was produced in batches ("waves"). The most recent waves sit directly under `StatFormal/<Wave>/`, the earlier
ones under `StatFormal/Archive/<Wave>/`, and general results under `StatFormal/Lib/`.

The earlier waves were moved once, from folders directly under `StatFormal/` to `StatFormal/Archive/`. The most recent
waves were written after the move and were never moved. The move changed module paths only: Lean
namespaces and declarations are unchanged. Before carrying any approval over, a script checked that every locked file is
byte-identical to its approved text apart from its import lines. Each moved entry of the lock records the move under
`relocated`. That script and its re-audit are in the development repository.

## Re-verify
```
lake exe cache get && python3 tools/certify.py check && python3 tools/check_aliases.py
```

## Licence
Everything in this repository (Lean sources, cards, tools and these pages) is released under the Apache License 2.0
(`LICENSE`), copyright 2026 Hristo Inouzhe.
