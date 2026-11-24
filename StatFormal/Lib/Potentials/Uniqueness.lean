import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.MeasureTheory.Measure.Support
import StatFormal.Lib.Convex.GradientAE

/-!
# Uniqueness of convex potentials up to an additive constant

Library component (potential-level OT limit theory, part 1). Untrusted library code; no frozen
statement is touched.

Brenier's theorem identifies the optimal map `∇u` only `μ`-almost everywhere. To identify the
*potential* `u` itself one needs: two convex functions on an open connected set whose gradients
agree almost everywhere differ by a constant there. This file proves this, and its measure-theoretic
form used in otfd-C (`prop:conditional-potentials`, the paragraph "Two candidate conjugates have
the same gradients on a dense full-source-measure differentiability set ...").

## Main results

* `eqOn_of_ae_hasFDerivAt_zero`: on an open preconnected `U` in a finite-dimensional space, a
  locally Lipschitz `w` with `Dw = 0` at Haar-a.e. point of `U` is constant on `U`. (Fubini along
  lines, `MeasureTheory.ae_ae_add_linearMap_mem_iff`, plus the FTC for absolutely continuous
  functions, `AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`.)
* `ConvexOn.exists_eq_add_const_of_ae_fderiv_eq`: convex `u, φ` on an open convex `U` with
  `Du = Dφ` Haar-a.e. on `U` satisfy `u = φ + C` on `U`.
* `ConvexOn.fderiv_eq_of_ae_fderiv_eq_of_subset_support`: if `Du = Dφ` holds `μ`-a.e. on `U` for
  some measure `μ` with `U ⊆ supp μ` (and both are differentiable `μ`-a.e. on `U`), then
  `Du x = Dφ x` at **every** point `x ∈ U` where both are differentiable (closed-graph argument,
  Rockafellar Thm 25.7 via `StatFormal.Convex.tendsto_fderiv_of_tendsto`).
* `ConvexOn.exists_eq_add_const_of_ae_gradient_eq`: **uniqueness of the Brenier potential up to
  constants**. On a finite-dimensional inner product space, if `μ ≪ ρ` (Haar), `U` is open convex
  with `U ⊆ supp μ`, and `∇u = ∇φ` `μ`-a.e. on `U`, then `u = φ + C` on `U`. No density lower
  bound is needed: full support on `U` suffices.

## References

* R. T. Rockafellar, *Convex Analysis*, Theorems 25.5 and 25.7.
* R. J. McCann, *Existence and uniqueness of monotone measure-preserving maps*, Duke Math. J. 80
  (1995) — uniqueness of the Brenier potential on the interior of a connected support.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology Gradient

namespace StatFormal.Potentials

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- An almost-everywhere property holds on a measurable set of full measure. -/
theorem exists_measurableSet_ae_mem {P : E → Prop} (h : ∀ᵐ z ∂ρ, P z) :
    ∃ s, MeasurableSet s ∧ (∀ z ∈ s, P z) ∧ ∀ᵐ z ∂ρ, z ∈ s := by
  refine ⟨(toMeasurable ρ {z | ¬ P z})ᶜ, (measurableSet_toMeasurable _ _).compl,
    fun z hz => ?_, ?_⟩
  · by_contra hP
    exact hz (subset_toMeasurable _ _ hP)
  · rw [ae_iff]
    simp only [mem_compl_iff, not_not, ofPred_mem_eq, measure_toMeasurable]
    exact ae_iff.1 h

variable [ρ.IsAddHaarMeasure]

/-- **A Lipschitz function with a.e. vanishing derivative is constant on half the ball.** Let
`w` be `K`-Lipschitz on `B(x, r)` with `Dw = 0` at Haar-a.e. point of `B(x, r)`. Then
`w x₂ = w x₁` for all `x₁, x₂ ∈ B(x, r/2)`. Proof: for a.e. `y` near `x₁` the derivative vanishes at
a.e. point of the segment `[y, y + (x₂ - x₁)]` (Fubini along lines), so `t ↦ w (y + t (x₂ - x₁))`
is absolutely continuous with a.e. zero derivative, hence constant; continuity of `w` then
transfers `w (y + x₂ - x₁) = w y` to `y = x₁`. -/
theorem eq_of_lipschitzOnWith_ball {w : E → ℝ} {x : E} {r : ℝ} {K : ℝ≥0}
    (hw : LipschitzOnWith K w (ball x r))
    (hd : ∀ᵐ z ∂ρ, z ∈ ball x r → HasFDerivAt w (0 : E →L[ℝ] ℝ) z)
    {x₁ x₂ : E} (h₁ : x₁ ∈ ball x (r / 2)) (h₂ : x₂ ∈ ball x (r / 2)) : w x₂ = w x₁ := by
  set v : E := x₂ - x₁ with hv
  obtain ⟨s, hsm, hsP, hsae⟩ := exists_measurableSet_ae_mem hd
  let L : ℝ →ₗ[ℝ] E := LinearMap.toSpanSingleton ℝ E v
  have hline : ∀ᵐ y ∂ρ, ∀ᵐ t ∂(volume : Measure ℝ), y + L t ∈ s :=
    (ae_ae_add_linearMap_mem_iff L volume ρ hsm).2 hsae
  have key : ∀ᵐ y ∂ρ, y ∈ ball x₁ (r / 2) → w (y + v) = w y := by
    filter_upwards [hline] with y hy hyb
    have hyB : y ∈ ball x r := by
      rw [mem_ball] at hyb h₁ ⊢
      linarith [dist_triangle y x₁ x]
    have hyvB : y + v ∈ ball x r := by
      rw [mem_ball] at hyb h₂ ⊢
      have : dist (y + v) x₂ = dist y x₁ := by
        rw [hv, dist_eq_norm, dist_eq_norm]; congr 1; abel
      linarith [dist_triangle (y + v) x₂ x]
    have hmaps : MapsTo (fun t : ℝ => y + t • v) (uIcc 0 1) (ball x r) := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact (convex_ball x r).add_smul_mem hyB hyvB ht
    have hac : AbsolutelyContinuousOnInterval (fun t : ℝ => y + t • v) 0 1 :=
      ((contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
        ).absolutelyContinuousOnInterval
    have hgac : AbsolutelyContinuousOnInterval (w ∘ fun t : ℝ => y + t • v) 0 1 :=
      hw.comp_absolutelyContinuousOnInterval hmaps hac
    have hderiv : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIcc (0 : ℝ) 1 →
        HasDerivAt (w ∘ fun t : ℝ => y + t • v) 0 t := by
      filter_upwards [hy] with t ht htI
      have hz : HasFDerivAt w (0 : E →L[ℝ] ℝ) (y + t • v) := by
        refine hsP _ ?_ (hmaps htI)
        simpa [L] using ht
      have hl : HasDerivAt (fun t : ℝ => y + t • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add y
      simpa using hz.comp_hasDerivAt t hl
    obtain ⟨C, hC⟩ := hgac.const_of_ae_hasDerivAt_zero hderiv
    have h0 := hC 0 (by simp)
    have h1 := hC 1 (by simp)
    simp only [Function.comp_apply, one_smul, zero_smul, add_zero] at h0 h1
    rw [h0, h1]
  by_contra hne
  have hr2 : r / 2 ≤ r := by linarith [dist_nonneg.trans_lt (mem_ball.1 h₁)]
  have hx₁B : x₁ ∈ ball x r := ball_subset_ball hr2 h₁
  have hx₂B : x₂ ∈ ball x r := ball_subset_ball hr2 h₂
  have hcont : ContinuousAt (fun y => w (y + v) - w y) x₁ := by
    have hc1 : ContinuousAt w x₁ := (hw.continuousOn).continuousAt (isOpen_ball.mem_nhds hx₁B)
    have hc2 : ContinuousAt w (x₁ + v) := by
      have : x₁ + v = x₂ := by rw [hv]; abel
      rw [this]
      exact (hw.continuousOn).continuousAt (isOpen_ball.mem_nhds hx₂B)
    have hc3 : ContinuousAt (fun y => w (y + v)) x₁ :=
      hc2.comp (f := fun y => y + v) (continuous_id.add continuous_const).continuousAt
    exact hc3.sub hc1
  have hne' : w (x₁ + v) - w x₁ ≠ 0 := by
    have : x₁ + v = x₂ := by rw [hv]; abel
    rw [this]
    exact sub_ne_zero.2 hne
  have hr : 0 < r / 2 := dist_nonneg.trans_lt (mem_ball.1 h₁)
  have hN : {y | w (y + v) - w y ≠ 0} ∩ ball x₁ (r / 2) ∈ 𝓝 x₁ :=
    inter_mem (hcont.eventually (isOpen_ne.mem_nhds hne')) (ball_mem_nhds x₁ hr)
  have hpos := Measure.measure_pos_of_mem_nhds (μ := ρ) hN
  have hzero : ρ ({y | w (y + v) - w y ≠ 0} ∩ ball x₁ (r / 2)) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [key] with y hy hmem
    exact hmem.1 (sub_eq_zero.2 (hy hmem.2))
  exact hpos.ne' hzero

/-- **A locally Lipschitz function with a.e. vanishing derivative on an open preconnected set is
constant there.** Let `E` be finite-dimensional with an additive Haar measure `ρ`, `U ⊆ E` open
and preconnected, and `w : E → ℝ` locally Lipschitz on `U` with `HasFDerivAt w 0 z` for `ρ`-a.e.
`z ∈ U`. Then `w z = w x₀` for all `z, x₀ ∈ U`. -/
theorem eqOn_of_ae_hasFDerivAt_zero {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U)
    {w : E → ℝ} (hw : LocallyLipschitzOn U w)
    (hd : ∀ᵐ z ∂ρ, z ∈ U → HasFDerivAt w (0 : E →L[ℝ] ℝ) z) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∀ z ∈ U, w z = w x₀ := by
  have hloc : ∀ x ∈ U, ∀ᶠ z in 𝓝 x, w z = w x := by
    intro x hx
    obtain ⟨K, t, ht, hK⟩ := hw hx
    rw [hU.nhdsWithin_eq hx] at ht
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 (inter_mem ht (hU.mem_nhds hx))
    have hK' : LipschitzOnWith K w (ball x r) := hK.mono fun z hz => (hrt hz).1
    have hd' : ∀ᵐ z ∂ρ, z ∈ ball x r → HasFDerivAt w (0 : E →L[ℝ] ℝ) z := by
      filter_upwards [hd] with z hz hzb using hz (hrt hzb).2
    filter_upwards [ball_mem_nhds x (half_pos hr)] with z hz
    exact eq_of_lipschitzOnWith_ball hK' hd' (mem_ball_self (half_pos hr)) hz
  have : PreconnectedSpace U := Subtype.preconnectedSpace hUc
  have hlc : IsLocallyConstant (fun z : U => w z) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    exact (continuous_subtype_val.tendsto x).eventually (hloc x x.2)
  intro z hz
  exact hlc.apply_eq_of_preconnectedSpace ⟨z, hz⟩ ⟨x₀, hx₀⟩

/-- **Convex functions with a.e. equal derivatives differ by a constant.** Let `E` be
finite-dimensional with an additive Haar measure `ρ`, `U ⊆ E` open and convex, and `u, φ` convex
on `U` with `fderiv u = fderiv φ` at `ρ`-a.e. point of `U`. Then `u = φ + C` on `U` for some
constant `C`. (Convex functions are locally Lipschitz and differentiable a.e. on open sets.) -/
theorem _root_.ConvexOn.exists_eq_add_const_of_ae_fderiv_eq {U : Set E} (hU : IsOpen U)
    {u φ : E → ℝ} (hu : ConvexOn ℝ U u) (hφ : ConvexOn ℝ U φ)
    (h : ∀ᵐ z ∂ρ, z ∈ U → fderiv ℝ u z = fderiv ℝ φ z) : ∃ C, ∀ z ∈ U, u z = φ z + C := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, by simp⟩
  have hLu := hu.locallyLipschitzOn hU
  have hLφ := hφ.locallyLipschitzOn hU
  have hw : LocallyLipschitzOn U (fun z => u z - φ z) := by
    intro x hx
    obtain ⟨K₁, t₁, ht₁, h₁⟩ := hLu hx
    obtain ⟨K₂, t₂, ht₂, h₂⟩ := hLφ hx
    refine ⟨K₁ + K₂, t₁ ∩ t₂, inter_mem ht₁ ht₂, LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_⟩
    calc dist (u a - φ a) (u b - φ b) ≤ dist (u a) (u b) + dist (φ a) (φ b) :=
          dist_sub_sub_le _ _ _ _
      _ ≤ K₁ * dist a b + K₂ * dist a b :=
          add_le_add (h₁.dist_le_mul a ha.1 b hb.1) (h₂.dist_le_mul a ha.2 b hb.2)
      _ = ((K₁ + K₂ : ℝ≥0) : ℝ) * dist a b := by push_cast; ring
  have hd : ∀ᵐ z ∂ρ, z ∈ U → HasFDerivAt (fun z => u z - φ z) (0 : E →L[ℝ] ℝ) z := by
    filter_upwards [hu.ae_differentiableAt_of_mem (μ := ρ), hφ.ae_differentiableAt_of_mem (μ := ρ),
      h] with z h1 h2 h3 hz
    have := (h1 hz).hasFDerivAt.sub (h2 hz).hasFDerivAt
    rwa [h3 hz, sub_self] at this
  refine ⟨u x₀ - φ x₀, fun z hz => ?_⟩
  have := eqOn_of_ae_hasFDerivAt_zero hU hu.1.isPreconnected hw hd hx₀ z hz
  linarith

omit [ρ.IsAddHaarMeasure] [BorelSpace E] in
/-- **Agreement of gradients on a dense set propagates to every common differentiability
point.** Let `u, φ` be convex on the open set `U`, `μ` a measure with `U ⊆ supp μ`, both `u` and
`φ` differentiable at `μ`-a.e. point of `U`, and `fderiv u = fderiv φ` `μ`-a.e. on `U`. Then
`fderiv u x = fderiv φ x` at every `x ∈ U` where both `u` and `φ` are differentiable. (The good
set is dense in `U`; derivatives of a convex function at nearby differentiability points converge
to the derivative at a differentiability point, Rockafellar Thm 25.7.) -/
theorem _root_.ConvexOn.fderiv_eq_of_ae_fderiv_eq_of_subset_support {U : Set E} (hU : IsOpen U)
    {u φ : E → ℝ} (hu : ConvexOn ℝ U u) (hφ : ConvexOn ℝ U φ) {μ : Measure E}
    (hsupp : U ⊆ μ.support) (hdu : ∀ᵐ z ∂μ, z ∈ U → DifferentiableAt ℝ u z)
    (hdφ : ∀ᵐ z ∂μ, z ∈ U → DifferentiableAt ℝ φ z)
    (h : ∀ᵐ z ∂μ, z ∈ U → fderiv ℝ u z = fderiv ℝ φ z) {x : E} (hx : x ∈ U)
    (hux : DifferentiableAt ℝ u x) (hφx : DifferentiableAt ℝ φ x) :
    fderiv ℝ u x = fderiv ℝ φ x := by
  set D : Set E := {z | z ∈ U ∧ DifferentiableAt ℝ u z ∧ DifferentiableAt ℝ φ z ∧
    fderiv ℝ u z = fderiv ℝ φ z} with hD
  have hDae : ∀ᵐ z ∂μ, z ∈ U → z ∈ D := by
    filter_upwards [hdu, hdφ, h] with z h1 h2 h3 hz using ⟨hz, h1 hz, h2 hz, h3 hz⟩
  have hcl : x ∈ closure D := by
    rw [mem_closure_iff_nhds]
    intro N hN
    have hpos : 0 < μ (N ∩ U) :=
      (Measure.mem_support_iff_forall x).1 (hsupp hx) _ (inter_mem hN (hU.mem_nhds hx))
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    have : μ (N ∩ U) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hDae] with z hz hzNU
      have : z ∈ N ∩ D := ⟨hzNU.1, hz hzNU.2⟩
      rw [hempty] at this
      exact this
    exact hpos.ne' this
  have : (𝓝[D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hxs : Tendsto (fun z : E => z) (𝓝[D] x) (𝓝 x) := tendsto_nhdsWithin_of_tendsto_nhds
    tendsto_id
  have hev : ∀ᶠ z in 𝓝[D] x, z ∈ D := self_mem_nhdsWithin
  have hu' := StatFormal.Convex.tendsto_fderiv_of_tendsto (F := fun _ : E => u) (f := u)
    (l := 𝓝[D] x) hU (Eventually.of_forall fun _ => hu) (fun _ _ => tendsto_const_nhds) hx hux
    hxs (hev.mono fun z hz => hz.2.1)
  have hφ' := StatFormal.Convex.tendsto_fderiv_of_tendsto (F := fun _ : E => φ) (f := φ)
    (l := 𝓝[D] x) hU (Eventually.of_forall fun _ => hφ) (fun _ _ => tendsto_const_nhds) hx hφx
    hxs (hev.mono fun z hz => hz.2.2.1)
  exact tendsto_nhds_unique (hu'.congr' (hev.mono fun z hz => hz.2.2.2)) hφ'

end Normed

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E} [ρ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Equal gradients means equal Fréchet derivatives. -/
theorem fderiv_eq_of_gradient_eq [CompleteSpace E] {u φ : E → ℝ} {z : E} (h : ∇ u z = ∇ φ z) :
    fderiv ℝ u z = fderiv ℝ φ z := by
  simpa [gradient] using congrArg (InnerProductSpace.toDual ℝ E) h

/-- **Uniqueness of the Brenier potential up to an additive constant.** Let `E` be a
finite-dimensional real inner product space with an additive Haar measure `ρ` (e.g. Lebesgue
measure), `μ ≪ ρ` a measure, `U ⊆ E` open and convex with `U ⊆ supp μ`, and `u, φ` convex on `U`
with `∇u = ∇φ` at `μ`-a.e. point of `U` (e.g. two potentials of the same optimal map
`∇u = T = ∇φ` `μ`-a.e.). Then `u = φ + C` on `U` for some constant `C`.

This is the identification step of otfd-C `prop:conditional-potentials` (source law `μ_K` with
convex support `𝒰_K`, `U = int 𝒰_K`); cf. McCann (1995). Only full support of `μ` on `U` is
needed, no lower bound on its density. -/
theorem _root_.ConvexOn.exists_eq_add_const_of_ae_gradient_eq {U : Set E} (hU : IsOpen U)
    {u φ : E → ℝ} (hu : ConvexOn ℝ U u) (hφ : ConvexOn ℝ U φ) {μ : Measure E} (hμ : μ ≪ ρ)
    (hsupp : U ⊆ μ.support) (h : ∀ᵐ z ∂μ, z ∈ U → ∇ u z = ∇ φ z) :
    ∃ C, ∀ z ∈ U, u z = φ z + C := by
  have hdu := hu.ae_differentiableAt_of_mem (μ := ρ)
  have hdφ := hφ.ae_differentiableAt_of_mem (μ := ρ)
  refine hu.exists_eq_add_const_of_ae_fderiv_eq (ρ := ρ) hU hφ ?_
  filter_upwards [hdu, hdφ] with z h1 h2 hz
  exact hu.fderiv_eq_of_ae_fderiv_eq_of_subset_support hU hφ hsupp (hμ.ae_le hdu) (hμ.ae_le hdφ)
    (h.mono fun z hz hzU => fderiv_eq_of_gradient_eq (hz hzU)) hz (h1 hz) (h2 hz)

end Inner

end StatFormal.Potentials
