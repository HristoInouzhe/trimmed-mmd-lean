import StatFormal.Wave31tq.Statements
import StatFormal.Wave31to.Proofs
import StatFormal.Wave31to.RouteC
import StatFormal.Wave31ti.Proofs

/-!
# Wave 31tq, route X: the common part of Proposition S4.5 and of S4 :371-372 (untrusted proof file)

For a feature map `φ` on a hereditarily Lindelöf Borel space (every finite-dimensional space is one), with `0 < α⋆ < 1`:

* `integral_sub_eq_tv`: if `0 ≤ f ≤ 1` is measurable, `f = 1` on `supp P₀` and `f = 0` on `supp Q₀` (`P₀ ∝ P − P ⊓ Q`,
  `Q₀ ∝ Q − P ⊓ Q`), then `E_P f − E_Q f = α⋆`: `P = (P − P ⊓ Q) + P ⊓ Q`, the supports carry full mass, and
  `(P − P ⊓ Q)(𝒳) = α⋆` (certified `Wave31to.RouteC.mass_sub`);
* `core_b`, part (b) of the claims: such an `f = ⟪g, φ ·⟫` has `err(f) = 0` (certified `Wave31to.newapprox_err`), so
  `ε/‖g‖ ≤ D̄_{α⋆−ε}` (certified `newapproxgen_ii`), `D̄ ≤ D` (`newapproxgen_iii_a`), hence Assumption 5.1 with `γ = 1`,
  `c₀ = 1/‖g‖`; `g ≠ 0` since `supp P₀` is nonempty;
* `core_c`, part (c): if disjoint supports give such a `g`, every limit `s` of `D̄_{α⋆−e}/e` as `e ↓ 0` is positive iff the
  supports are disjoint: "if" by (b) and the certified `Wave31ti.pathconvex_ii` (a linear margin iff `s > 0`), "only if" by
  the certified `Wave31to.newslope_b` (`φ` continuous: meeting supports force `s = 0`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteX

open StatFormal.TrimmedMMD.Unconditional StatFormal.Distances StatFormal.Wave31to

section Core

variable {𝒳 : Type} [TopologicalSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳] [HereditarilyLindelofSpace 𝒳]

/-- `(Q − P ⊓ Q)(𝒳) = α⋆`. -/
theorem mass_sub_right (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (Q - P ⊓ Q) univ = ENNReal.ofReal (tvDist P Q) := by
  rw [inf_comm, StatFormal.Wave31to.RouteC.mass_sub Q P, tvDist_comm]

/-- A `[0,1]`-valued measurable `f` equal to `1` on `supp P₀` and `0` on `supp Q₀` has `E_P f − E_Q f = α⋆`. -/
theorem integral_sub_eq_tv (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {f : 𝒳 → ℝ}
    (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (h1 : ∀ x ∈ (P - P ⊓ Q).support, f x = 1)
    (h0 : ∀ x ∈ (Q - P ⊓ Q).support, f x = 0) :
    (∫ x, f x ∂P) - ∫ x, f x ∂Q = tvDist P Q := by
  have hint : ∀ (μ : Measure 𝒳) [IsFiniteMeasure μ], Integrable f μ := fun μ _ =>
    Integrable.of_bound hfm.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hf x])
  have hP := integral_add_measure (hint (P - P ⊓ Q)) (hint (P ⊓ Q))
  rw [Measure.sub_add_cancel_of_le inf_le_left] at hP
  have hQ := integral_add_measure (hint (Q - P ⊓ Q)) (hint (P ⊓ Q))
  rw [Measure.sub_add_cancel_of_le inf_le_right] at hQ
  have e1 : ∫ x, f x ∂(P - P ⊓ Q) = tvDist P Q := by
    have : f =ᵐ[P - P ⊓ Q] fun _ => 1 := by
      filter_upwards [Measure.support_mem_ae (μ := P - P ⊓ Q)] with x hx using h1 x hx
    rw [integral_congr_ae this, integral_const, smul_eq_mul, mul_one, measureReal_def,
      StatFormal.Wave31to.RouteC.mass_sub, ENNReal.toReal_ofReal (tvDist_nonneg _ _)]
  have e2 : ∫ x, f x ∂(Q - P ⊓ Q) = 0 := by
    have : f =ᵐ[Q - P ⊓ Q] fun _ => 0 := by
      filter_upwards [Measure.support_mem_ae (μ := Q - P ⊓ Q)] with x hx using h0 x hx
    rw [integral_congr_ae this, integral_zero]
  rw [hP, hQ, e1, e2]
  ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- **Part (b)**: a representer `g` of a `[0,1]`-valued function equal to `1` on `supp P₀` and `0` on `supp Q₀` is nonzero and
gives `D̄_{α⋆−ε} ≤ D_{α⋆−ε}`, `ε/‖g‖ ≤ D̄_{α⋆−ε}` on `[0, α⋆]` and Assumption 5.1 with `γ = 1`, `c₀ = 1/‖g‖`. -/
theorem core_b (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hφm : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 < tvDist P Q) (hα1 : tvDist P Q < 1) (g : H)
    (hg : ∀ x, 0 ≤ ⟪g, φ x⟫_ℝ ∧ ⟪g, φ x⟫_ℝ ≤ 1) (hg1 : ∀ x ∈ (P - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 1)
    (hg0 : ∀ x ∈ (Q - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 0) :
    g ≠ 0 ∧ (∀ ε ∈ Icc (0 : ℝ) (tvDist P Q),
        StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - ε) ≤ Dpop φ P Q (tvDist P Q - ε) ∧
        ε / ‖g‖ ≤ StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - ε)) ∧
      StatFormal.Wave31ti.PolyMargin φ P Q (1 / ‖g‖) 1 := by
  have hwm : Measurable (wit φ g) := StatFormal.Wave31to.RouteA.wit_meas hφm g
  have herr : errFn P Q (wit φ g) = 0 := by
    have h := (StatFormal.Wave31to.newapprox_err 𝒳 P Q (wit φ g) hwm hg).1
    rw [h, integral_sub_eq_tv P Q hwm hg hg1 hg0, sub_self]
  have hne : g ≠ 0 := by
    rintro rfl
    have hne0 : P - P ⊓ Q ≠ 0 := by
      intro h0
      have := StatFormal.Wave31to.RouteC.mass_sub P Q
      rw [h0, Measure.coe_zero, Pi.zero_apply] at this
      exact (ENNReal.ofReal_pos.2 hα0).ne this
    obtain ⟨x, hx⟩ := Measure.nonempty_support hne0
    have := hg1 x hx
    simp at this
  have hF : g ∈ Fset φ := hg
  have hii := (StatFormal.Wave31to.newapproxgen_ii 𝒳 H P Q φ κ g hφm hκ hα0 hα1 hF).2 hne
  have hiii := (StatFormal.Wave31to.newapproxgen_iii_a 𝒳 H P Q φ κ hφm hκ hα0 hα1).2
  have hb : ∀ ε ∈ Icc (0 : ℝ) (tvDist P Q),
      StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - ε) ≤ Dpop φ P Q (tvDist P Q - ε) ∧
        ε / ‖g‖ ≤ StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - ε) := fun ε hε =>
    ⟨(hiii ε hε).2.1, by simpa [herr] using hii ε hε⟩
  refine ⟨hne, hb, one_div_pos.2 (norm_pos_iff.2 hne), le_rfl, fun e he => ?_⟩
  rw [Real.rpow_one, one_div_mul_eq_div]
  exact (hb e he).2.trans (hb e he).1

/-- **Part (c)**: if disjoint supports give a separating representer, every limit `s` of `D̄_{α⋆−e}/e` as `e ↓ 0` is positive
iff `supp P₀ ∩ supp Q₀ = ∅` (`φ` continuous). -/
theorem core_c (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hφc : Continuous φ) (hφm : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 < tvDist P Q)
    (hα1 : tvDist P Q < 1)
    (hex : (P - P ⊓ Q).support ∩ (Q - P ⊓ Q).support = ∅ →
      ∃ g : H, (∀ x, 0 ≤ ⟪g, φ x⟫_ℝ ∧ ⟪g, φ x⟫_ℝ ≤ 1) ∧ (∀ x ∈ (P - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 1) ∧
        ∀ x ∈ (Q - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 0)
    (sl : ℝ) (hsl : Tendsto (fun e => StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - e) / e) (𝓝[>] 0) (𝓝 sl)) :
    0 < sl ↔ (P - P ⊓ Q).support ∩ (Q - P ⊓ Q).support = ∅ := by
  constructor
  · intro hpos
    by_contra hne
    have hne' := Set.nonempty_iff_ne_empty.2 hne
    have hlim : Tendsto (fun e => (1 - tvDist P Q + e) * Dpop φ P Q (tvDist P Q - e) / e) (𝓝[>] 0) (𝓝 sl) := by
      refine hsl.congr fun e => ?_
      simp only [StatFormal.Wave31ti.uPath]
      ring
    have h := (StatFormal.Wave31to.newslope_b 𝒳 H P Q φ κ hφm hφc hκ hα0 hα1 hne').1 sl hlim
    linarith
  · intro hdis
    obtain ⟨g, hg, hg1, hg0⟩ := hex hdis
    have hpm := (core_b φ κ P Q hφm hκ hα0 hα1 g hg hg1 hg0).2.2
    exact ((StatFormal.Wave31ti.pathconvex_ii 𝒳 H P Q φ κ hφm hκ hα0 hα1).2.2.1 sl hsl).2.1.1 ⟨_, hpm⟩

end Core

end StatFormal.Wave31tq.RouteX
