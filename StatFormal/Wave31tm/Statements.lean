import StatFormal.Wave30tz.Statements
import StatFormal.Wave30tx.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31tm: trimmed-mmd (jmlr) **v3 of 2026-11-19**: `cor:alphalo` (the trimmed sample at the split-sample lower bound)

Printed source: `trimmed-mmd/jmlr/v3/` at trimmed-mmd commit `5e51f65` (read-only, read 2026-11-19 from `git show 5e51f65:…`). sha256 of
the files read: `sections/05_trimming.tex` `7ea03da385165072066e03ff1e04827f630fa5a65ef77853d08c89c9349d7b9b`,
`appendix/D_trimming.tex` `848ad1f70127d37d0022d3b4db81e9ad9004e67ffafc34d95769d7357a0ad419`; context `sections/04_split.tex`
`790e687bc511c0c918b821ce8f24e56e6f916f1e9f8fb0516c6baaaa24ea153e` (`prop:loconsistency`, `cor:lower`), `sections/03_analytic.tex`
`f47ebecd68ce035e3b59bf1d50189a89bdd60587498eef7b22bb04f6fce9e220` (`lem:pathconvex`). Printed numbers (`main.aux` of the build of
2026-11-19 18:48): Corollary 17 `cor:alphalo`, Proposition 16 `prop:alphahat`, Proposition 12 `prop:loconsistency`, Corollary 11
`cor:lower`, Lemma 7 `lem:pathconvex`.

* `cor:alphalo` (Corollary 17, "The trimmed sample at the lower bound", `05_trimming.tex:158-165`, proof `D_trimming.tex:447-468`): "Let
  Assumption 1 hold with `0 < α⋆ < 1`, and compute `α̂_lo` at level `δ` as in Proposition 12, on grids fixed in advance whose mesh tends
  to zero, with `log J = o(n∧m)`. Then for every `ε > 0` and `δ′ ∈ (0,1)`, for all `n, m` large enough, with probability at least
  `1−δ−δ′` every `(w,v) ∈ 𝒯_{α̂_lo}` has `MMD(P_n^w, R⋆) ≤ ε` and `MMD(Q_m^v, R⋆) ≤ ε`."
  Here `R⋆ = (P∧Q)/(1−α⋆)` (`05_trimming.tex:124-125`) and `𝒯_α` is the set of minimizers `(w,v)` of (qp) at level `α` on the full
  samples (`05_trimming.tex:12`).

Reuses (imported, not copied): `Wave30tz` (`LoRun`, `IsWitnessRun`, `IsSizedRun`, `LoRun.alphaLo`, `IsGrid`, `gridMesh` — exactly the
hypotheses of the certified `Wave30tz.lo_refining`, the refining-grid clause of Proposition 12), `Wave30tx` (`contactLaw` = `R⋆`, `wEmp`
= `Σ w_iδ_{X_i}`, as in the certified `Wave30tx.alphahat` = Proposition 16), `TrimmedMMD.BangBang` (`capped`, `qp`: `𝒯_α` is the set of
minimizers of `qp` over `capped n α × capped m α`), `TrimmedMMD.ZeroSet.Characteristic` ((A3)), `Wave30tp.sampleLaw`, `Distances.tvDist`.

Encodings:
* (A1)–(A3) as in every trimmed-mmd wave (`H` real complete separable, `φ` strongly measurable, `‖φ‖ ≤ κ`, `Characteristic φ`);
  `α⋆ = TV(P,Q)` with `0 < α⋆ < 1`.
* "compute `α̂_lo` at level `δ` as in Proposition 12, on grids fixed in advance whose mesh tends to zero, with `log J = o(n∧m)`": a fixed
  `δ ∈ (0,1)`, grids `α n m` (deterministic, `IsGrid`) with `J n m` levels, mesh `→ 0` and `log J = o(n∧m)` (in the explicit form of
  `Wave30tz.lo_refining`), and runs `R n m` with `IsWitnessRun φ (α n m) δ λ_max σ²_min` and `IsSizedRun c C₀ B` (batch fractions fixed
  in advance). Proposition 12 as printed in v3 takes `λ_max = ½` and a floor `σ²_min ∈ (0,4]` (`04_split.tex:171`); the claim allows any
  `λ_max ∈ (0,½]` and any floor `σ²_min > 0`, as the certified `Wave30tz.lo_refining` does (generalisation of the print).
* "for all `n, m` large enough, with probability at least `1−δ−δ′`": `∃ N₀, ∀ n m ≥ N₀`, a measurable event of probability
  `≥ 1 − δ − δ′` on which the conclusion holds for every minimizer.
* `MMD(P_n^w, R⋆) = ‖∫φ d(Σ w_iδ_{X_i}) − μ_{R⋆}‖` and likewise for `Q_m^v`.
* Junk values: `capped n a` at `a = α̂_lo`, a grid level `< 1` or `0` (the cap `1/(n(1−a))` is genuine); `contactLaw` divides by
  `1 − α⋆ > 0`; `wEmp` uses `ofReal (w i)` with `w ≥ 0` on `capped`; no `sInf`/`sSup` in the statement.

Not covered (declared): the prose around the corollary (`05_trimming.tex:155-156`, `167-170`): "At the split-sample bound the convexity of
the path does, together with its consistency", "the corollary needs no margin" (true of the claim, which assumes none) and "Under
Assumption 2, Theorem 33 bounds `α⋆ − α̂_lo` explicitly, but as at `α̂` the bound carries no rate unless `Ω` is known" (informal; the bound
on `α⋆ − α̂_lo` is `Wave31tl.lorate_ii`).
FROZEN 2026-11-19 before any proof, after the independent critic's pre-freeze review shared with wave 31tl (`alphalo`:
ACCEPT-WITH-NOTE; the printed proof re-derived step by step, no wrong step; the `Q`-side bound needs `s` chosen for both moduli
`Ω^{P,Q}` and `Ω^{Q,P}`, a nit of the printed proof). Applied: R4 (the `λ_max`, `σ²_min` generalisation of the print declared). No Lean
term changed.
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tm

open StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.ZeroSet

namespace Claims

/-- **`cor:alphalo`** (Corollary 17): under (A1)–(A3) with `0 < α⋆ = TV(P,Q) < 1`, a fixed `δ ∈ (0,1)`, grids fixed in advance with mesh
`→ 0` and `log J = o(n∧m)`, and runs of Proposition 12 (per-level witnesses, `0 < λ_max ≤ ½`, floor `σ²_min > 0`, batch fractions fixed in
advance): for every `ε > 0` and `δ′ ∈ (0,1)` there is `N₀` such that for all `n, m ≥ N₀` there is a measurable event of probability
`≥ 1 − δ − δ′` on which every minimizer `(w,v)` of (qp) at the level `α̂_lo` has `MMD(Σ w_iδ_{X_i}, R⋆) ≤ ε` and
`MMD(Σ v_jδ_{Y_j}, R⋆) ≤ ε`, `R⋆ = (P∧Q)/(1−α⋆)`. -/
def alphalo : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (J : ℕ → ℕ → ℕ) (α : ∀ n m, Fin (J n m) → ℝ) (δ lmax s2 c C0 : ℝ) (Bmax : ℕ)
    (R : ∀ n m : ℕ, LoRun 𝒳 (J n m) n m),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
    (∀ n m, IsGrid (α n m)) →
    (∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → gridMesh (α n m) ≤ η ∧ Real.log (J n m) ≤ η * (min n m : ℕ)) →
    0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 / 2 → 0 < s2 → 0 < c →
    (∀ n m, (R n m).IsWitnessRun φ (α n m) δ lmax s2 ∧ (R n m).IsSizedRun c C0 Bmax) →
      ∀ ε > 0, ∀ δ' : ℝ, 0 < δ' → δ' < 1 → ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m →
        ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ - δ') ≤ sampleLaw P Q n m E ∧
          ∀ z ∈ E, ∀ pr ∈ capped n ((R n m).alphaLo (α n m) δ z.1 z.2) ×ˢ capped m ((R n m).alphaLo (α n m) δ z.1 z.2),
            IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j)))
              (capped n ((R n m).alphaLo (α n m) δ z.1 z.2) ×ˢ capped m ((R n m).alphaLo (α n m) δ z.1 z.2)) pr →
              ‖∫ x, φ x ∂(StatFormal.Wave30tx.wEmp pr.1 z.1) - ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖ ≤ ε ∧
              ‖∫ x, φ x ∂(StatFormal.Wave30tx.wEmp pr.2 z.2) - ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖ ≤ ε

end Claims

end StatFormal.Wave31tm
