import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Route (wave L3): normalisation by the infimum (otfd C `prop:conditional-potentials`)

Untrusted route file. C normalises its potentials by `inf_{𝒰_K} χ = 0` (`X(0) = 0` for the
conjugate), whereas the library normalises at a point. For convex functions on a bounded open
convex `V` in finite dimension:
* `bddBelow_image_of_convexOn`: a convex function on `V` is bounded below there;
* `tendsto_of_isGLB`: if `fₙ → φ` locally uniformly on `V`, the infima converge,
  `inf_V fₙ → inf_V φ` (convexity along segments to a fixed interior point controls the boundary);
* `isGLB_image_iff_interior`: for continuous `f` and `U ⊆ cl(int U)`, the infimum over `U` is the
  infimum over `int U`.
-/

open Set Filter Topology Metric

namespace StatFormal.OTFD.WaveL3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isGLB_image_iff_interior {f : E → ℝ} (hf : Continuous f) {U : Set E}
    (hU : U ⊆ closure (interior U)) (c : ℝ) :
    IsGLB (f '' U) c ↔ IsGLB (f '' interior U) c := by
  have h : lowerBounds (f '' U) = lowerBounds (f '' interior U) := by
    ext b
    constructor
    · rintro hb _ ⟨x, hx, rfl⟩
      exact hb ⟨x, interior_subset hx, rfl⟩
    · rintro hb _ ⟨x, hx, rfl⟩
      have hcl : closure (interior U) ⊆ {x | b ≤ f x} :=
        closure_minimal (fun y hy => hb ⟨y, hy, rfl⟩) (isClosed_le continuous_const hf)
      exact hcl (hU hx)
  simp only [IsGLB, h]

variable [FiniteDimensional ℝ E]

/-- A convex function on a bounded open set of a finite-dimensional space is bounded below. -/
theorem bddBelow_image_of_convexOn {V : Set E} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {φ : E → ℝ} (hφ : ConvexOn ℝ V φ) : BddBelow (φ '' V) := by
  rcases V.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hV x₀ hx₀
  obtain ⟨R, hR⟩ := hVb.subset_ball x₀
  have hRpos : 0 < R := by
    have := hR hx₀
    rwa [mem_ball, dist_self] at this
  set B := closedBall x₀ (r / 2) with hB
  have hBV : B ⊆ V := (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hcont : ContinuousOn φ B :=
    hφ.continuousOn_interior.mono (by rw [hV.interior_eq]; exact hBV)
  obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ (r / 2)).bddAbove_image hcont
  set s : ℝ := r / (2 * R) with hs
  have hs0 : 0 < s := by positivity
  refine ⟨((1 + s) * φ x₀ - M) / s, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  set y' : E := x₀ - s • (y - x₀) with hy'
  have hy'B : y' ∈ B := by
    rw [hB, mem_closedBall, dist_eq_norm, hy', sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg hs0.le]
    have hyR : ‖y - x₀‖ < R := by
      have := hR hy
      rwa [mem_ball, dist_eq_norm] at this
    calc s * ‖y - x₀‖ ≤ s * R := mul_le_mul_of_nonneg_left hyR.le hs0.le
      _ = r / 2 := by rw [hs]; field_simp
  have hφy' : φ y' ≤ M := hM ⟨y', hy'B, rfl⟩
  have hcomb : (1 / (1 + s)) • y' + (s / (1 + s)) • y = x₀ := by
    have e1 : y' + s • y = (1 + s) • x₀ := by
      rw [hy', smul_sub, add_smul, one_smul]; abel
    have e2 : (1 / (1 + s)) • y' + (s / (1 + s)) • y = (1 / (1 + s)) • (y' + s • y) := by
      rw [smul_add, smul_smul]; congr 2; ring
    rw [e2, e1, smul_smul, div_mul_cancel₀ _ (by positivity), one_smul]
  have hconv := hφ.2 (hBV hy'B) hy (by positivity : (0 : ℝ) ≤ 1 / (1 + s))
    (by positivity : (0 : ℝ) ≤ s / (1 + s)) (by field_simp)
  rw [hcomb, smul_eq_mul, smul_eq_mul] at hconv
  rw [div_le_iff₀ hs0]
  have h1 : (1 + s) * φ x₀ ≤ φ y' + s * φ y := by
    have := mul_le_mul_of_nonneg_left hconv (by positivity : (0 : ℝ) ≤ 1 + s)
    calc (1 + s) * φ x₀ ≤ (1 + s) * (1 / (1 + s) * φ y' + s / (1 + s) * φ y) := this
      _ = φ y' + s * φ y := by field_simp
  linarith

/-- **Convergence of the infima** under locally uniform convergence of convex functions on a
bounded open convex set. -/
theorem tendsto_of_isGLB {V : Set E} (hV : IsOpen V) (hVc : Convex ℝ V)
    (hVb : Bornology.IsBounded V) {x₀ : E} (hx₀ : x₀ ∈ V) {f : ℕ → E → ℝ} {φ : E → ℝ}
    (hf : ∀ n, ConvexOn ℝ V (f n)) (hlim : TendstoLocallyUniformlyOn f φ atTop V)
    {m : ℕ → ℝ} (hm : ∀ n, IsGLB (f n '' V) (m n)) {m₀ : ℝ} (hm₀ : IsGLB (φ '' V) m₀) :
    Tendsto m atTop (𝓝 m₀) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    set δ := m₀ - a with hδ
    have hδ0 : 0 < δ := by linarith
    have hφx₀ : m₀ ≤ φ x₀ := hm₀.1 ⟨x₀, hx₀, rfl⟩
    set s : ℝ := min (1 / 2) (δ / (4 * (φ x₀ - m₀ + 1))) with hs
    have hs0 : 0 < s := lt_min (by norm_num) (by have : 0 < φ x₀ - m₀ + 1 := by linarith
                                                 positivity)
    have hs1 : s ≤ 1 / 2 := min_le_left _ _
    have hsδ : s * (φ x₀ - m₀) ≤ δ / 4 := by
      have h1 : s ≤ δ / (4 * (φ x₀ - m₀ + 1)) := min_le_right _ _
      have hp : 0 < φ x₀ - m₀ + 1 := by linarith
      calc s * (φ x₀ - m₀) ≤ δ / (4 * (φ x₀ - m₀ + 1)) * (φ x₀ - m₀) :=
            mul_le_mul_of_nonneg_right h1 (by linarith)
        _ ≤ δ / (4 * (φ x₀ - m₀ + 1)) * (φ x₀ - m₀ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = δ / 4 := by field_simp
    set t : ℝ := 1 - s with ht
    have ht0 : 0 ≤ t := by linarith
    set Kc : Set E := (fun u => t • u + s • x₀) '' closure V with hKc
    have hKV : Kc ⊆ V := by
      rintro _ ⟨u, hu, rfl⟩
      have := hVc.combo_closure_interior_mem_interior hu (by rwa [hV.interior_eq]) ht0 hs0
        (by rw [ht]; ring)
      rwa [hV.interior_eq] at this
    have hKcpt : IsCompact Kc :=
      (hVb.isCompact_closure).image (by fun_prop)
    have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hV).1 hlim Kc hKV hKcpt
    set η : ℝ := δ / 16 with hη
    have hη0 : 0 < η := by positivity
    have hx₀K : x₀ ∈ Kc := ⟨x₀, subset_closure hx₀, by simp only [ht, sub_smul, one_smul]; abel⟩
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif η hη0] with n hn
    have hfx₀ : f n x₀ < φ x₀ + η := by
      have := hn x₀ hx₀K
      rw [Real.dist_eq] at this
      linarith [le_abs_self (φ x₀ - f n x₀), neg_abs_le (φ x₀ - f n x₀)]
    set b : ℝ := (m₀ - η - s * (φ x₀ + η)) / t with hb
    have htpos : 0 < t := by linarith
    have hlow : ∀ y ∈ V, b ≤ f n y := by
      intro y hy
      have hv : t • y + s • x₀ ∈ Kc := ⟨y, subset_closure hy, rfl⟩
      have hfv : φ (t • y + s • x₀) - η < f n (t • y + s • x₀) := by
        have := hn _ hv
        rw [Real.dist_eq] at this
        linarith [le_abs_self (φ (t • y + s • x₀) - f n (t • y + s • x₀))]
      have hφv : m₀ ≤ φ (t • y + s • x₀) := hm₀.1 ⟨_, hKV hv, rfl⟩
      have hcv := (hf n).2 hy hx₀ ht0 hs0.le (by rw [ht]; ring)
      rw [smul_eq_mul, smul_eq_mul] at hcv
      rw [hb, div_le_iff₀ htpos]
      nlinarith
    have hbm : b ≤ m n := (hm n).2 (by rintro _ ⟨y, hy, rfl⟩; exact hlow y hy)
    have hab : a < b := by
      rw [hb, lt_div_iff₀ htpos]
      nlinarith
    exact hab.trans_le hbm
  · intro a ha
    obtain ⟨_, ⟨y, hy, rfl⟩, -, hya⟩ := hm₀.exists_between ha
    have hpt : Tendsto (fun n => f n y) atTop (𝓝 (φ y)) := hlim.tendsto_at hy
    filter_upwards [hpt.eventually (gt_mem_nhds hya)] with n hn
    exact ((hm n).1 ⟨y, hy, rfl⟩).trans_lt hn

end StatFormal.OTFD.WaveL3
