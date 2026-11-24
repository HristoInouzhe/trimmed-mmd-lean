import StatFormal.Archive.OTFD.Wave19a.Statements
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Route: B `lem:app-subgradient-convergence` (untrusted)

* (a) No compactness argument: for every direction `e` and small `t > 0`,
  `t⟨ξ_n, e⟩ ≤ g_n(u_n + te) − g_n(u_n) → g(u + te) − g(u) ≤ t(⟨∇g(u), e⟩ + ε/2)` (uniform convergence on a
  compact ball, continuity of the convex `g` on the open `C`, differentiability at `u`); with `−e`,
  `⟨ξ_n, e⟩ → ⟨∇g(u), e⟩` for every `e`, hence `ξ_n → ∇g(u)` (finite dimension, orthonormal basis).
* (b) By contradiction, a subsequence with `w_n → w ∈ S`; (a) for `g_n` and for the constant sequence `g` (the
  gradient of a differentiable convex function is a subgradient) gives two limits `∇g(w)`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open Set Filter Topology
open scoped RealInnerProductSpace

namespace StatFormal.OTFD.Wave19a

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The subgradient inequality for the `+∞`-extension. -/
lemma mem_subdiff_extTop {K : ℕ} {C : Set (EuclideanSpace ℝ (Fin K))} {g : EuclideanSpace ℝ (Fin K) → ℝ}
    {x ξ : EuclideanSpace ℝ (Fin K)}
    (h : ξ ∈ TauCeti.subdifferential (innerₗ (EuclideanSpace ℝ (Fin K))) (extTop C g) x) :
    x ∈ C ∧ ∀ y ∈ C, g x + ⟪y - x, ξ⟫ ≤ g y := by
  obtain ⟨-, hT, hineq⟩ := h
  have hx : x ∈ C := by
    by_contra hx; apply hT; simp [extTop, hx]
  refine ⟨hx, fun y hy => ?_⟩
  have := hineq y
  simp only [extTop, hx, hy, if_true, innerₗ_apply_apply] at this
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at this
  exact this

lemma mem_subdiff_extTop_of {K : ℕ} {C : Set (EuclideanSpace ℝ (Fin K))} {g : EuclideanSpace ℝ (Fin K) → ℝ}
    {x ξ : EuclideanSpace ℝ (Fin K)} (hx : x ∈ C) (h : ∀ y ∈ C, g x + ⟪y - x, ξ⟫ ≤ g y) :
    ξ ∈ TauCeti.subdifferential (innerₗ (EuclideanSpace ℝ (Fin K))) (extTop C g) x := by
  refine ⟨by simp [extTop, hx], by simp [extTop, hx], fun y => ?_⟩
  by_cases hy : y ∈ C
  · simp only [extTop, hx, hy, if_true, innerₗ_apply_apply]
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]; exact h y hy
  · simp [extTop, hy]

/-- Directional slopes of a differentiable function. -/
lemma slope_tendsto {g0 : E → ℝ} {u : E} (hd : DifferentiableAt ℝ g0 u) (e : E) :
    Tendsto (fun t : ℝ => (g0 (u + t • e) - g0 u) / t) (𝓝[>] 0) (𝓝 ⟪gradient g0 u, e⟫) := by
  have hp : HasDerivAt (fun t : ℝ => u + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add u
  have hc : HasDerivAt (fun t : ℝ => g0 (u + t • e)) (fderiv ℝ g0 u e) 0 := by
    have := hd.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hp (by simp)
    simpa [Function.comp_def] using this
  have h := hc.tendsto_slope_zero_right
  have hg : fderiv ℝ g0 u e = ⟪gradient g0 u, e⟫ := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [hg] at h
  refine h.congr' (Eventually.of_forall fun t => ?_)
  simp [smul_eq_mul, div_eq_inv_mul]

end General

section Claims
variable {K : ℕ}

/-- The one-sided bound of (a) in a direction `e`. -/
lemma subgrad_upper {C : Set (EuclideanSpace ℝ (Fin K))} {g : ℕ → EuclideanSpace ℝ (Fin K) → ℝ}
    {g0 : EuclideanSpace ℝ (Fin K) → ℝ} {u : EuclideanSpace ℝ (Fin K)} {us ξ : ℕ → EuclideanSpace ℝ (Fin K)}
    (hC : IsOpen C) (hg0 : ConvexOn ℝ C g0)
    (hunif : ∀ S ⊆ C, IsCompact S → TendstoUniformlyOn g g0 atTop S)
    (hu : u ∈ C) (hd : DifferentiableAt ℝ g0 u) (hus : Tendsto us atTop (𝓝 u))
    (hξ : ∀ᶠ n in atTop, ξ n ∈ TauCeti.subdifferential (innerₗ (EuclideanSpace ℝ (Fin K))) (extTop C (g n)) (us n))
    (e : EuclideanSpace ℝ (Fin K)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ⟪ξ n, e⟫ ≤ ⟪gradient g0 u, e⟫ + ε := by
  have hcont := hg0.continuousOn hC
  -- a step `t > 0` with `u + te ∈ C` and a good slope
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), u + t • e ∈ C ∧ (g0 (u + t • e) - g0 u) / t < ⟪gradient g0 u, e⟫ + ε / 2 := by
    refine Eventually.and ?_ ((slope_tendsto hd e).eventually (gt_mem_nhds (by linarith)))
    have : Tendsto (fun t : ℝ => u + t • e) (𝓝 0) (𝓝 u) := by
      have hc : Continuous fun t : ℝ => u + t • e := by fun_prop
      simpa using hc.tendsto 0
    exact nhdsWithin_le_nhds (this (hC.mem_nhds hu))
  obtain ⟨t, ⟨hte, hslope⟩, ht⟩ := (hev.and self_mem_nhdsWithin).exists
  have ht0 : 0 < t := ht
  set v := u + t • e
  -- convergence of `g_n` along `u_n` and `u_n + te`
  have hconv : ∀ {w : EuclideanSpace ℝ (Fin K)} {ws : ℕ → EuclideanSpace ℝ (Fin K)}, w ∈ C →
      Tendsto ws atTop (𝓝 w) → Tendsto (fun n => g n (ws n)) atTop (𝓝 (g0 w)) := by
    intro w ws hw hws
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hC w hw
    have hS : Metric.closedBall w (ρ / 2) ⊆ C :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hU := hunif _ hS (isCompact_closedBall w (ρ / 2))
    refine hU.tendsto_comp ((hcont w hw).mono hS) ?_
    exact tendsto_nhdsWithin_iff.2 ⟨hws, hws.eventually (Metric.closedBall_mem_nhds w (by linarith))⟩
  have hvs : Tendsto (fun n => us n + t • e) atTop (𝓝 v) := hus.add_const _
  have h1 := hconv hte hvs
  have h2 := hconv hu hus
  have hη : 0 < t * ε / 4 := by positivity
  filter_upwards [hξ, (tendsto_order.1 h1).2 _ (show g0 v < g0 v + t * ε / 4 by linarith),
    (tendsto_order.1 h2).1 _ (show g0 u - t * ε / 4 < g0 u by linarith),
    hvs.eventually (hC.mem_nhds hte)] with n hn ha hb hc
  obtain ⟨-, hineq⟩ := mem_subdiff_extTop hn
  have hi := hineq _ hc
  rw [add_sub_cancel_left, inner_smul_left] at hi
  simp only [conj_trivial] at hi
  have hs : g0 v - g0 u < t * (⟪gradient g0 u, e⟫ + ε / 2) := by
    rw [div_lt_iff₀ ht0] at hslope; linarith
  have : t * ⟪e, ξ n⟫ < t * (⟪gradient g0 u, e⟫ + ε) := by nlinarith
  rw [real_inner_comm]
  exact (lt_of_mul_lt_mul_left this ht0.le).le

theorem subgrad_conv_point : Claims.subgrad_conv_point := by
  intro K C g g0 u us ξ hC _ _ hg0 hunif hu hd hus hξ
  have hinner : ∀ e, Tendsto (fun n => ⟪ξ n, e⟫) atTop (𝓝 ⟪gradient g0 u, e⟫) := by
    intro e
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have := subgrad_upper hC hg0 hunif hu hd hus hξ (-e) (ε := (⟪gradient g0 u, e⟫ - a) / 2) (by linarith)
      filter_upwards [this] with n hn
      rw [inner_neg_right, inner_neg_right] at hn; linarith
    · have := subgrad_upper hC hg0 hunif hu hd hus hξ e (ε := (a - ⟪gradient g0 u, e⟫) / 2) (by linarith)
      filter_upwards [this] with n hn
      linarith
  set b := EuclideanSpace.basisFun (Fin K) ℝ
  have hsum : ∀ x : EuclideanSpace ℝ (Fin K), ∑ i, ⟪b i, x⟫ • b i = x := b.sum_repr'
  have : Tendsto (fun n => ∑ i, ⟪b i, ξ n⟫ • b i) atTop (𝓝 (∑ i, ⟪b i, gradient g0 u⟫ • b i)) := by
    refine tendsto_finset_sum _ fun i _ => ?_
    refine Tendsto.smul_const ?_ _
    have h := hinner (b i)
    rw [real_inner_comm (b i) (gradient g0 u)] at h
    exact h.congr fun n => real_inner_comm (b i) (ξ n)
  simpa only [hsum] using this

/-- The gradient of a convex function differentiable at a point of `C` is a subgradient (over `C`). -/
lemma grad_mem_subdiff {C : Set (EuclideanSpace ℝ (Fin K))} {g0 : EuclideanSpace ℝ (Fin K) → ℝ}
    (hg0 : ConvexOn ℝ C g0) {w : EuclideanSpace ℝ (Fin K)} (hw : w ∈ C) (hd : DifferentiableAt ℝ g0 w) :
    gradient g0 w ∈ TauCeti.subdifferential (innerₗ (EuclideanSpace ℝ (Fin K))) (extTop C g0) w := by
  refine mem_subdiff_extTop_of hw fun y hy => ?_
  have hlim := slope_tendsto hd (y - w)
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), (g0 (w + t • (y - w)) - g0 w) / t ≤ g0 y - g0 w := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ⟨ht0, ht1⟩
    rw [div_le_iff₀ ht0]
    have hcv := hg0.2 hw hy (show 0 ≤ 1 - t by linarith) ht0.le (by ring)
    have hpt : (1 - t) • w + t • y = w + t • (y - w) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hpt, smul_eq_mul, smul_eq_mul] at hcv
    linarith
  have := le_of_tendsto hlim hle
  rw [real_inner_comm] at this
  linarith

theorem subgrad_conv_unif : Claims.subgrad_conv_unif := by
  intro K C g g0 O S hC hCc hgc hg0 hunif hO hOC hdiff hSO hS ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  simp only [not_forall, not_le, exists_prop] at hcon
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hcon
  choose w hwS ξ hξ hgap using hφP
  obtain ⟨w0, hw0S, ψ, hψ, hlim⟩ := hS.tendsto_subseq hwS
  have hw0C : w0 ∈ C := hOC (hSO hw0S)
  have hsub : ∀ S' ⊆ C, IsCompact S' → TendstoUniformlyOn (fun k => g (φ (ψ k))) g0 atTop S' := by
    intro S' hS'C hS'
    exact fun s hs => ((hφ.comp hψ).tendsto_atTop).eventually (hunif S' hS'C hS' s hs)
  have hA := subgrad_conv_point K C (fun k => g (φ (ψ k))) g0 w0 (fun k => w (ψ k)) (fun k => ξ (ψ k)) hC hCc
    (fun k => hgc _) hg0 hsub hw0C (hdiff _ (hSO hw0S)) hlim (Eventually.of_forall fun k => hξ (ψ k))
  have hconst : ∀ S' ⊆ C, IsCompact S' → TendstoUniformlyOn (fun _ : ℕ => g0) g0 atTop S' :=
    fun S' _ _ s hs => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hs
  have hB := subgrad_conv_point K C (fun _ => g0) g0 w0 (fun k => w (ψ k)) (fun k => gradient g0 (w (ψ k)))
    hC hCc (fun _ => hg0) hg0 hconst hw0C (hdiff _ (hSO hw0S)) hlim
    (Eventually.of_forall fun k => grad_mem_subdiff hg0 (hOC (hSO (hwS _))) (hdiff _ (hSO (hwS _))))
  have hlim0 : Tendsto (fun k => ‖ξ (ψ k) - gradient g0 (w (ψ k))‖) atTop (𝓝 0) := by
    have := (hA.sub hB).norm
    simpa using this
  have := (tendsto_order.1 hlim0).2 ε hε
  obtain ⟨k, hk⟩ := this.exists
  exact absurd (hgap (ψ k)) (not_lt.2 hk.le)

end Claims

end StatFormal.OTFD.Wave19a
