import StatFormal.Archive.OTFDR.Statements
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# FROZEN STATEMENTS — otfd R/A, wave 1: `prop:support`, `prop:influence`, `thm:unbalanced` (R) and
# `lem:app-pullback` (A)

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-R_robustness.md`, `otfd-A_sieves.md`):
* R `prop:support`: `otfd/papers/R_robustness/sections/s4_regions.tex:5-17`; `TD` is `eq:TDH`
  (`s2_setting.tex:7-10`: `TD(u;ν) = inf_{v ≠ 0} ν{z : ⟨v, z−u⟩ ≤ 0}`), `β(A;ν) := inf_{u∈A} TD(u;ν)`
  (`s2_setting.tex:74`), `h_A(v) = sup_{u∈A} ⟨v,u⟩`.
* R `prop:influence`: `s85_tuning.tex:47-64`, with the criterion `D̂`, `D`, `Δ` of A `prop:selector`
  (`A_sieves/main.tex:1236-1270`).
* R `thm:unbalanced`: `s8_unbalanced.tex:8-55` (`def:unbalanced`, `eq:unb-kkt`, the theorem), proof
  `appendix_b.tex:128-165`; `eq:oos` `s2_setting.tex:25-28`; `H_{t,D}(e)` `s2_setting.tex:66-67`.
* A `lem:app-pullback`: `A_sieves/supplement.tex:1318-1331`, with `def:app-lipschitz-hypersurface`
  (`supplement.tex:925-936`).

Covered:
* `support`: for a Borel probability `ν` on `ℝ^K` and a nonempty compact `A`,
  `β(A;ν) = inf_{‖v‖=1} ν{X : ⟨X,v⟩ ≥ h_A(v)}`; `support_bounded`: the same for every nonempty
  bounded `A` (reviewer m5: compactness is not needed).
* `influence_bound`: replacing `ℓ` validation curves moves `D̂(θ)` by at most `8Rℓ/n_v`;
  `influence_select`: the contaminated minimiser is a `16Rℓ/n_v`-approximate minimiser of the clean
  criterion; `influence_oracle`: on the event `sup_θ |D̂_clean − D| ≤ Δ`,
  `D(θ̂) ≤ D(θ) + 2Δ + 16Rℓ/n_v` for every `θ`; `influence_oracle_prob`: the same "with probability
  `≥ 1 − γ`", given that event with probability `≥ 1 − γ` (A `prop:selector`(i)), measurable-event form.
* `unbalanced_sup_g_false` (**the printed `sup_u g(u) ≤ G*` is false**): with every hypothesis of the
  theorem in force (`B` exactly the largest unreplaced norm, `δ > 0`), `g(u) ≤ G*` fails for some `u`
  (witness: `E = ℝ`, `n = 1`, `z = 0`, `f = 0`, `ν = ½δ₋₁ + ½δ₁`, `D_ν = 1`, `ε = τ = 1`, `u₀ = 0`,
  `t = D = 1`, `δ = ½`: `g(u) = u²/2`, `G* = 1`, `g(2) = 2`); indeed `g(u) ≥ min_i(½‖u−z_i‖² − f_i)`
  is unbounded.
* `unbalanced_g_ball` (corrected first display, which is all the proof uses):
  `sup_{‖u‖ ≤ D_ν} g(u) ≤ G*`;
* `unbalanced_mass`: `m_k ≤ n⁻¹ exp{−((‖z_k‖−D_ν)²/2 − G*)/(τ+ε)}` for every `‖z_k‖ > D_ν`;
* `unbalanced_displacement`: `‖Q̂(u₀)‖ ≤ B' + ℓ (D B' + ε log(2n) + ε)/t`.
* `pullback`: `P ∈ 𝒫^ℓ(H) ⇒ Π_K#P ∈ 𝒫^ℓ(ℝ^K)` for every `K`.

Not covered (declared):
* `prop:influence`: A `prop:selector`(i) itself (the concentration bound `Δ`); it enters as the event
  hypothesis of `influence_oracle_prob`. **Defect (review m8):** the printed last display
  `D(θ̂) ≤ min D + 2Δ + 16Rℓ/n_v` has no probability qualifier; it holds only on A's
  probability-`(1−γ)` event — `influence_oracle_prob` is the corrected form. Only validation-fold
  contamination is covered (as printed).
* `thm:unbalanced`: existence/uniqueness of the potentials (they enter through `eq:unb-kkt`, as
  `TrimKKT` did for `thm:trimmed`); the closing sentences ("bounded at every point of positive
  depth", "breakdown point `(n−1)/n` or more" — under `def:bp` it is in fact `1`, which is consistent).
* `lem:app-pullback`: nothing; completeness/separability of `H` and completeness of `(e_k)` are unused.

Encodings (see card):
* `ℝ^K` is `EuclideanSpace ℝ (Fin K)` (`prop:support`, `lem:app-pullback`); `thm:unbalanced` and
  `prop:influence` are stated over any real inner-product (resp. normed) space — a generalisation.
* Depths and measures are `ℝ≥0∞`-valued (`⨅` is exact; no `sInf ∅ = 0` junk); `h_A` is `sSup` of the
  image, finite on the nonempty bounded `A` assumed (empty `A` excluded: `inf ∅ = ⊤` vs `ν(ℝ^K) = 1`).
* `prop:influence`: `a_i = Υ F̂_θ(Z_i)` is `Φ θ (Z i)` for an arbitrary map `Φ θ` into the
  `R_Υ`-ball (the property of `Υ` used); `b_j` arbitrary (uncontaminated); "replaced" = `Z' i = Z i`
  off a set `O` of size `ℓ`; "`min_Θ D + …`" is `∀ θ, D θ̂ ≤ D θ + …`.
* `thm:unbalanced`: `g` is defined by the first identity of `eq:unb-kkt` (`gUnb`); the second identity is
  `UnbKKT` (`∫ π(i|u) ν(du) = n⁻¹ e^{−f_i/τ}` with `π` the softmax `piCond` of `eq:oos`, imported from the
  frozen `OTFDR/Statements.lean`); "supported in `{‖u‖ ≤ D_ν}`" is `∀ᵐ u ∂ν, ‖u‖ ≤ D_ν`; `O` = replaced
  indices, `ℓ = |O|`, `O ≠ univ`; `B` is any bound on the unreplaced norms (bounds are monotone in `B`;
  the refutation pins `B` to the max); `δ` is any lower bound in `(0,1]` of `ν(H_{t,D}(e))` over
  unit `e` (bounds are monotone in `δ`; `δ ≤ 1` is automatic when `E ≠ 0`); `D ≥ 0`.
* `lem:app-pullback`: `Π_K x = (⟨e_k, x⟩)_{k<K}` for an orthonormal family `e : ℕ → H` (0-indexed);
  a Lipschitz hypersurface is `{z + τ(z) w : ⟨z,w⟩ = 0}` with `w ≠ 0` and `τ : H → ℝ` Lipschitz
  **on** `(ℝw)^⊥` (equivalent to `τ : (ℝw)^⊥ → ℝ` Lipschitz: values off `(ℝw)^⊥` are irrelevant);
  `𝒫^ℓ` includes the paper's second-moment clause, as `∫⁻ ‖x‖ₑ² < ⊤`.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
Critic notes: `unbalanced_sup_g_false` refutes the LITERAL printed `sup_u g ≤ G*` (s8_unbalanced.tex:43), which is `+∞` for
every instance; the paper's proof (appendix_b.tex:130) bounds the sup over `supp ν` — a scope slip (missing subscript);
`unbalanced_g_ball` (sup over a ball ⊇ supp ν) is the intended statement, slightly strengthened. In `support`, `A ≠ ∅` is needed
(for empty `A` the left side is `⊤` while `sSup ∅ = 0` makes the right side `≤ 1`).
-/

noncomputable section
open MeasureTheory Real Finset
open scoped ENNReal InnerProductSpace

namespace StatFormal.OTFD.Wave1

open StatFormal.OTFDR (piCond Qhat)

/-! ### `prop:support` -/

/-- `eq:TDH`: `TD(u;ν) = inf_{v ≠ 0} ν{z : ⟨v, z − u⟩ ≤ 0}`. -/
def tukeyDepth {K : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin K))) (u : EuclideanSpace ℝ (Fin K)) :
    ℝ≥0∞ :=
  ⨅ (v : EuclideanSpace ℝ (Fin K)) (_ : v ≠ 0), ν {z | ⟪v, z - u⟫_ℝ ≤ 0}

/-- `β(A;ν) := inf_{u∈A} TD(u;ν)`. -/
def regionDepth {K : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin K)))
    (A : Set (EuclideanSpace ℝ (Fin K))) : ℝ≥0∞ :=
  ⨅ u ∈ A, tukeyDepth ν u

/-- The support function `h_A(v) = sup_{u∈A} ⟨v,u⟩`. -/
def supportFn {K : ℕ} (A : Set (EuclideanSpace ℝ (Fin K))) (v : EuclideanSpace ℝ (Fin K)) : ℝ :=
  sSup ((fun u => ⟪v, u⟫_ℝ) '' A)

/-! ### `prop:influence` -/

/-- A `prop:selector`: `D̂ = (2/(n_v m_v)) Σ_{i,j} ‖a_i − b_j‖ − n_v⁻² Σ_{i,i'} ‖a_i − a_{i'}‖
− m_v⁻² Σ_{j,j'} ‖b_j − b_{j'}‖`. -/
def edStat {E : Type*} [NormedAddCommGroup E] {nv mv : ℕ} (a : Fin nv → E) (b : Fin mv → E) : ℝ :=
  2 / (nv * mv) * ∑ i, ∑ j, ‖a i - b j‖ - 1 / (nv : ℝ) ^ 2 * ∑ i, ∑ i', ‖a i - a i'‖
    - 1 / (mv : ℝ) ^ 2 * ∑ j, ∑ j', ‖b j - b j'‖

/-! ### `thm:unbalanced` -/

section Unb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- First identity of `eq:unb-kkt`: `e^{−g(u)/ε} = n⁻¹ Σ_i e^{(f_i − ½‖u−z_i‖²)/ε}`. -/
def gUnb {n : ℕ} (z : Fin n → E) (f : Fin n → ℝ) (ε : ℝ) (u : E) : ℝ :=
  -ε * Real.log (1 / n * ∑ j, Real.exp ((f j - ‖u - z j‖ ^ 2 / 2) / ε))

/-- Second identity of `eq:unb-kkt`: `m_i := ∫ π(i|u) ν(du) = n⁻¹ e^{−f_i/τ}`. -/
structure UnbKKT [MeasurableSpace E] (ν : Measure E) {n : ℕ} (z : Fin n → E) (f : Fin n → ℝ)
    (ε τ : ℝ) : Prop where
  mass : ∀ i, ∫ u, piCond z f ε u i ∂ν = 1 / n * Real.exp (-f i / τ)

/-- `H_{t,D}(e) = {u : ⟨u − u₀, e⟩ ≥ t, ‖u − u₀‖ ≤ D}`. -/
def HtD (u₀ : E) (t D : ℝ) (e : E) : Set E := {u | t ≤ ⟪u - u₀, e⟫_ℝ ∧ ‖u - u₀‖ ≤ D}

end Unb

/-- `G* = ((τ+ε)/ε)(½(D_ν+B)² + ε log n)`. -/
def Gstar (n : ℕ) (ε τ Dν B : ℝ) : ℝ := (τ + ε) / ε * ((Dν + B) ^ 2 / 2 + ε * Real.log n)

/-- `R₀ = D_ν + √(2G* + 2(τ+ε) log(2/δ))`. -/
def R0 (n : ℕ) (ε τ Dν B δ : ℝ) : ℝ :=
  Dν + √(2 * Gstar n ε τ Dν B + 2 * (τ + ε) * Real.log (2 / δ))

/-- `B' = max{B, R₀}`. -/
def Bprime (n : ℕ) (ε τ Dν B δ : ℝ) : ℝ := max B (R0 n ε τ Dν B δ)

/-! ### `lem:app-pullback` -/

section Pull
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `A_w = {z + τ(z) w : z ∈ (ℝw)^⊥}`. -/
def lipHyp (w : H) (τ : H → ℝ) : Set H := {x | ∃ z, ⟪z, w⟫_ℝ = 0 ∧ x = z + τ z • w}

/-- `S` is a Lipschitz hypersurface: `S = A_w` with `w ≠ 0` and `τ` Lipschitz on `(ℝw)^⊥`. -/
def IsLipHyp (S : Set H) : Prop :=
  ∃ w : H, w ≠ 0 ∧ ∃ τ : H → ℝ, (∃ L, LipschitzOnWith L τ {z | ⟪z, w⟫_ℝ = 0}) ∧ S = lipHyp w τ

/-- `𝒫^ℓ(H)` (with the paper's second-moment clause). -/
def PellClass [MeasurableSpace H] (P : Measure H) : Prop :=
  IsProbabilityMeasure P ∧ ∫⁻ x, ‖x‖ₑ ^ 2 ∂P < ⊤ ∧ ∀ S : Set H, IsLipHyp S → P S = 0

/-- `Π_K x = (⟨e_k, x⟩)_{k<K}`. -/
def truncK (e : ℕ → H) (K : ℕ) (x : H) : EuclideanSpace ℝ (Fin K) :=
  WithLp.toLp 2 (fun k : Fin K => ⟪e k, x⟫_ℝ)

end Pull

namespace Claims

/-- R `prop:support`, compact `A` (as printed; `A ≠ ∅` added). -/
def support : Prop :=
  ∀ (K : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν]
    (A : Set (EuclideanSpace ℝ (Fin K))), IsCompact A → A.Nonempty →
      regionDepth ν A = ⨅ (v : EuclideanSpace ℝ (Fin K)) (_ : ‖v‖ = 1),
        ν {X | supportFn A v ≤ ⟪X, v⟫_ℝ}

/-- R `prop:support` for bounded `A` (generalisation, reviewer m5). -/
def support_bounded : Prop :=
  ∀ (K : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν]
    (A : Set (EuclideanSpace ℝ (Fin K))), Bornology.IsBounded A → A.Nonempty →
      regionDepth ν A = ⨅ (v : EuclideanSpace ℝ (Fin K)) (_ : ‖v‖ = 1),
        ν {X | supportFn A v ≤ ⟪X, v⟫_ℝ}

/-- R `prop:influence`, first sentence: `|D̂(θ) − D̂_clean(θ)| ≤ 8R_Υ ℓ/n_v`. -/
def influence_bound : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] (X : Type) (nv mv : ℕ) (R : ℝ) (Φ : X → E)
    (Z Z' : Fin nv → X) (b : Fin mv → E) (O : Finset (Fin nv)),
    (∀ x, ‖Φ x‖ ≤ R) → (∀ i ∉ O, Z' i = Z i) →
      |edStat (fun i => Φ (Z' i)) b - edStat (fun i => Φ (Z i)) b| ≤ 8 * R * O.card / nv

/-- R `prop:influence`, second sentence: `θ̂` is a `16R_Υ ℓ/n_v`-approximate minimiser of
`D̂_clean`. -/
def influence_select : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] (X Θ : Type) (nv mv : ℕ) (R : ℝ) (Φ : Θ → X → E)
    (Z Z' : Fin nv → X) (b : Fin mv → E) (O : Finset (Fin nv)) (θhat : Θ),
    (∀ θ x, ‖Φ θ x‖ ≤ R) → (∀ i ∉ O, Z' i = Z i) →
    (∀ θ, edStat (fun i => Φ θhat (Z' i)) b ≤ edStat (fun i => Φ θ (Z' i)) b) →
      ∀ θ, edStat (fun i => Φ θhat (Z i)) b ≤ edStat (fun i => Φ θ (Z i)) b + 16 * R * O.card / nv

/-- R `prop:influence`, last display, on the event `sup_θ |D̂_clean(θ) − D(θ)| ≤ Δ`. -/
def influence_oracle : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] (X Θ : Type) (nv mv : ℕ) (R Δ : ℝ) (Φ : Θ → X → E)
    (Z Z' : Fin nv → X) (b : Fin mv → E) (O : Finset (Fin nv)) (θhat : Θ) (Dpop : Θ → ℝ),
    (∀ θ x, ‖Φ θ x‖ ≤ R) → (∀ i ∉ O, Z' i = Z i) →
    (∀ θ, edStat (fun i => Φ θhat (Z' i)) b ≤ edStat (fun i => Φ θ (Z' i)) b) →
    (∀ θ, |edStat (fun i => Φ θ (Z i)) b - Dpop θ| ≤ Δ) →
      ∀ θ, Dpop θhat ≤ Dpop θ + 2 * Δ + 16 * R * O.card / nv

/-- R `prop:influence`, last display, corrected: with probability `≥ 1 − γ` whenever A
`prop:selector`(i)'s event `sup_θ |D̂_clean − D| ≤ Δ` has probability `≥ 1 − γ` (measurable-event
form). Everything may depend on the outcome `ω` (training fold, validation draws, contamination). -/
def influence_oracle_prob : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] (X Θ Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    (nv mv ℓ : ℕ) (R Δ γ : ℝ) (Φ : Ω → Θ → X → E) (Z Z' : Ω → Fin nv → X) (b : Ω → Fin mv → E)
    (O : Ω → Finset (Fin nv)) (θhat : Ω → Θ) (Dpop : Ω → Θ → ℝ),
    (∀ ω θ x, ‖Φ ω θ x‖ ≤ R) → (∀ ω, (O ω).card ≤ ℓ) → (∀ ω, ∀ i ∉ O ω, Z' ω i = Z ω i) →
    (∀ ω θ, edStat (fun i => Φ ω (θhat ω) (Z' ω i)) (b ω) ≤
      edStat (fun i => Φ ω θ (Z' ω i)) (b ω)) →
    (∃ S : Set Ω, MeasurableSet S ∧ ENNReal.ofReal (1 - γ) ≤ μ S ∧
      S ⊆ {ω | ∀ θ, |edStat (fun i => Φ ω θ (Z ω i)) (b ω) - Dpop ω θ| ≤ Δ}) →
    ∃ S : Set Ω, MeasurableSet S ∧ ENNReal.ofReal (1 - γ) ≤ μ S ∧
      S ⊆ {ω | ∀ θ, Dpop ω (θhat ω) ≤ Dpop ω θ + 2 * Δ + 16 * R * ℓ / nv}

/-- R `thm:unbalanced`, first display as printed (`sup_u g(u) ≤ G*` over all `u`), is **false**: it
fails under every hypothesis of the theorem, with `B` the largest unreplaced norm. -/
def unbalanced_sup_g_false : Prop :=
  ¬ ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
      (ν : Measure E) [IsProbabilityMeasure ν] (n : ℕ) (z : Fin n → E) (f : Fin n → ℝ)
      (O : Finset (Fin n)) (ε τ Dν B t D δ : ℝ) (u₀ : E),
      0 < ε → 0 < τ → 0 ≤ Dν → (∀ᵐ u ∂ν, ‖u‖ ≤ Dν) →
      (∀ j ∉ O, ‖z j‖ ≤ B) → (∃ j ∉ O, ‖z j‖ = B) → UnbKKT ν z f ε τ →
      0 < t → 0 ≤ D → 0 < δ → δ ≤ 1 → (∀ e : E, ‖e‖ = 1 → ENNReal.ofReal δ ≤ ν (HtD u₀ t D e)) →
        ∀ u, gUnb z f ε u ≤ Gstar n ε τ Dν B

/-- R `thm:unbalanced`, first display corrected: `sup_{‖u‖ ≤ D_ν} g(u) ≤ G*`. -/
def unbalanced_g_ball : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (n : ℕ) (z : Fin n → E) (f : Fin n → ℝ)
    (O : Finset (Fin n)) (ε τ Dν B : ℝ),
    0 < ε → 0 < τ → 0 ≤ Dν → (∀ᵐ u ∂ν, ‖u‖ ≤ Dν) →
    (∃ j, j ∉ O) → (∀ j ∉ O, ‖z j‖ ≤ B) → UnbKKT ν z f ε τ →
      ∀ u, ‖u‖ ≤ Dν → gUnb z f ε u ≤ Gstar n ε τ Dν B

/-- R `thm:unbalanced`, far masses: `m_k ≤ n⁻¹ exp{−((‖z_k‖ − D_ν)²/2 − G*)/(τ+ε)}` for
`‖z_k‖ > D_ν`. -/
def unbalanced_mass : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (n : ℕ) (z : Fin n → E) (f : Fin n → ℝ)
    (O : Finset (Fin n)) (ε τ Dν B : ℝ),
    0 < ε → 0 < τ → 0 ≤ Dν → (∀ᵐ u ∂ν, ‖u‖ ≤ Dν) →
    (∃ j, j ∉ O) → (∀ j ∉ O, ‖z j‖ ≤ B) → UnbKKT ν z f ε τ →
      ∀ k, Dν < ‖z k‖ →
        ∫ u, piCond z f ε u k ∂ν ≤
          1 / n * Real.exp (-((‖z k‖ - Dν) ^ 2 / 2 - Gstar n ε τ Dν B) / (τ + ε))

/-- R `thm:unbalanced`, displacement: `‖Q̂(u₀)‖ ≤ B' + ℓ (D B' + ε log(2n) + ε)/t`, `ℓ = |O|`. -/
def unbalanced_displacement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (n : ℕ) (z : Fin n → E) (f : Fin n → ℝ)
    (O : Finset (Fin n)) (ε τ Dν B t D δ : ℝ) (u₀ : E),
    0 < ε → 0 < τ → 0 ≤ Dν → (∀ᵐ u ∂ν, ‖u‖ ≤ Dν) →
    (∃ j, j ∉ O) → (∀ j ∉ O, ‖z j‖ ≤ B) → UnbKKT ν z f ε τ →
    0 < t → 0 ≤ D → 0 < δ → δ ≤ 1 → (∀ e : E, ‖e‖ = 1 → ENNReal.ofReal δ ≤ ν (HtD u₀ t D e)) →
      ‖Qhat z f ε u₀‖ ≤ Bprime n ε τ Dν B δ +
        O.card * (D * Bprime n ε τ Dν B δ + ε * Real.log (2 * n) + ε) / t

/-- A `lem:app-pullback`: `P ∈ 𝒫^ℓ(H) ⇒ P_K := Π_K#P ∈ 𝒫^ℓ(ℝ^K)` for every `K`. -/
def pullback : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H), Orthonormal ℝ e → ∀ P : Measure H, PellClass P →
      ∀ K : ℕ, PellClass (P.map (truncK e K))

end Claims
end StatFormal.OTFD.Wave1
