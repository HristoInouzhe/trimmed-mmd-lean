import StatFormal.Wave30tx.Statements
import StatFormal.Wave30tx.RouteBasic
import StatFormal.Wave30tn.RoutePop
import StatFormal.Archive.Wave18b.RouteContinuity
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs
import StatFormal.Archive.Wave12c.RouteTrimConsist
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Route: `rem:nearcontact (v2)` (b), the Gaussian kernel (untrusted proof material)

`nearcontact_b_of : Claims.contact → Claims.nearcontact_densities → Claims.nearcontact_b`.

* **Analyticity along lines** (replaces the paper's appeal to Steinwart–Christmann 4.21/4.44): along a line
  `t ↦ x₀ + tv` the Gaussian Gram is `exp(−a(s−t)²)`; `χ(t) = e^{at²}φ(x₀+tv)` has Gram `e^{2ast}`, the same as
  `χ₀(t) = (√((2a)^k/k!) t^k)_k ∈ ℓ²`. A Hahn–Banach extension of `L₀c ↦ ⟨g, Lc⟩` (well defined since the Gram matrices
  agree) gives `⟨g, χ(t)⟩ = Σ_k w_k √((2a)^k/k!) t^k` with `|w_k| ≤ ‖g‖`, a power series of infinite radius; so
  `t ↦ ⟨g, φ(x₀+tv)⟩` is analytic and, by the identity theorem, a witness function constant near one point is constant.
* Weak sequential compactness of the unit ball (sequential Banach–Alaoglu through `toDual`).
* Step 1: `a_α → μ_{R*}` (`ω_c → 0` from `Claims.contact`, `D_α → 0` by the certified Lipschitz bound).
* Step 4 without weak-* compactness in `L^∞`: `∫ g_j f_j dP = ⟨a_j, f_j⟩ → ⟨μ_{R*}, f̄⟩`, and `(1−ε_j)g + ε_j` is an
  `α_j`-trimming density, so the contact density minimises `∫ g f̄ dP`; the bathtub argument of `Wave30tn` gives `f̄ = t̄`
  `P`-a.e. on `{0 < q < p}` (via `Claims.nearcontact_densities`), hence on that open set, hence everywhere; then
  `⟨f_j, f̄⟩ = D_j⁻¹(t̄ − t̄) = 0` (both trimmed embeddings integrate the constant `t̄` against probability densities), so
  `f̄ = 0` — no need for the absence of constants in the Gaussian RKHS.
* Step 5: dominated convergence (in probability), the quantile property (`s_α → 0`), and the window bounds.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace Nat Pointwise

namespace StatFormal.Wave30tx.RNearB

/-! ### The `ℓ²` model of the kernel `exp(bst)` -/

variable {b : ℝ}

/-- `√(b^k/k!) t^k`. -/
def cf (b' t : ℝ) (k : ℕ) : ℝ := Real.sqrt (b' ^ k / k !) * t ^ k

lemma cf_def (t : ℝ) (k : ℕ) : cf b t k = Real.sqrt (b ^ k / k !) * t ^ k := rfl

lemma cf_mul (hb : 0 ≤ b) (s t : ℝ) (k : ℕ) : cf b s k * cf b t k = (b * s * t) ^ k / k ! := by
  unfold cf
  have h : Real.sqrt (b ^ k / k !) * Real.sqrt (b ^ k / k !) = b ^ k / k ! :=
    Real.mul_self_sqrt (by positivity)
  calc Real.sqrt (b ^ k / k !) * s ^ k * (Real.sqrt (b ^ k / k !) * t ^ k)
      = (Real.sqrt (b ^ k / k !) * Real.sqrt (b ^ k / k !)) * (s ^ k * t ^ k) := by ring
    _ = (b * s * t) ^ k / k ! := by rw [h, mul_pow, mul_pow]; ring

lemma hasSum_exp_real (x : ℝ) : HasSum (fun n : ℕ => x ^ n / n !) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

lemma memℓp_cf (hb : 0 ≤ b) (t : ℝ) : Memℓp (cf b t) 2 := by
  refine memℓp_gen ?_
  have : (fun k => ‖cf b t k‖ ^ (2 : ℝ≥0∞).toReal) = fun k => (b * t * t) ^ k / k ! := by
    funext k
    rw [show (2 : ℝ≥0∞).toReal = (2 : ℕ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs, sq_abs, sq,
      cf_mul hb]
  rw [this]
  exact (hasSum_exp_real _).summable

/-- `χ₀(t) = (√(b^k/k!) t^k)_k ∈ ℓ²`. -/
def chi0 (hb : 0 ≤ b) (t : ℝ) : lp (fun _ : ℕ => ℝ) 2 := ⟨cf b t, memℓp_cf hb t⟩

lemma inner_chi0 (hb : 0 ≤ b) (s t : ℝ) : ⟪chi0 hb s, chi0 hb t⟫_ℝ = Real.exp (b * s * t) := by
  have h := lp.hasSum_inner (𝕜 := ℝ) (chi0 hb s) (chi0 hb t)
  have e : ∀ k : ℕ, ⟪(chi0 hb s : ℕ → ℝ) k, (chi0 hb t : ℕ → ℝ) k⟫_ℝ = (b * s * t) ^ k / k ! := by
    intro k
    change ⟪cf b s k, cf b t k⟫_ℝ = _
    rw [RCLike.inner_apply, conj_trivial, mul_comm, cf_mul hb]
  simp_rw [e] at h
  exact h.unique (hasSum_exp_real _)

/-! ### A bounded functional on `ℓ²` representing `t ↦ ⟪g, χ t⟫` -/

lemma inner_lc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ℝ → E) (c c' : ℝ →₀ ℝ) :
    ⟪Finsupp.linearCombination ℝ v c, Finsupp.linearCombination ℝ v c'⟫_ℝ =
      ∑ s ∈ c.support, ∑ t ∈ c'.support, c s * c' t * ⟪v s, v t⟫_ℝ := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, sum_inner]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

lemma norm_lc_eq {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (v : ℝ → E) (w : ℝ → F) (h : ∀ s t, ⟪v s, v t⟫_ℝ = ⟪w s, w t⟫_ℝ) (c : ℝ →₀ ℝ) :
    ‖Finsupp.linearCombination ℝ v c‖ = ‖Finsupp.linearCombination ℝ w c‖ := by
  have h1 := inner_lc v c c
  have h2 := inner_lc w c c
  simp_rw [h] at h1
  rw [← h2, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma exists_functional (hb : 0 ≤ b) (χ : ℝ → H) (hχ : ∀ s t, ⟪χ s, χ t⟫_ℝ = Real.exp (b * s * t)) (g : H) :
    ∃ Λ : StrongDual ℝ (lp (fun _ : ℕ => ℝ) 2), ‖Λ‖ ≤ ‖g‖ ∧ ∀ t, Λ (chi0 hb t) = ⟪g, χ t⟫_ℝ := by
  set L := Finsupp.linearCombination ℝ χ with hL
  set L₀ := Finsupp.linearCombination ℝ (chi0 hb) with hL₀
  have hnorm : ∀ c, ‖L c‖ = ‖L₀ c‖ := norm_lc_eq χ (chi0 hb) (fun s t => by rw [hχ, inner_chi0]) 
  set ψ : (ℝ →₀ ℝ) →ₗ[ℝ] ℝ := (innerSL ℝ g).toLinearMap.comp L with hψ
  have hker : LinearMap.ker L₀ ≤ LinearMap.ker ψ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have : ‖L c‖ = 0 := by rw [hnorm, hc, norm_zero]
    rw [norm_eq_zero] at this
    simp [hψ, this]
  set f₀ : LinearMap.range L₀ →ₗ[ℝ] ℝ :=
    ((LinearMap.ker L₀).liftQ ψ hker).comp L₀.quotKerEquivRange.symm.toLinearMap with hf₀
  have hf₀c : ∀ c, f₀ ⟨L₀ c, LinearMap.mem_range_self L₀ c⟩ = ⟪g, L c⟫_ℝ := by
    intro c
    have e : L₀.quotKerEquivRange.symm ⟨L₀ c, LinearMap.mem_range_self L₀ c⟩ = Submodule.Quotient.mk c := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk _ _).symm
    simp only [hf₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e, Submodule.liftQ_apply, hψ,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply]
  have hbound : ∀ v : LinearMap.range L₀, ‖f₀ v‖ ≤ ‖g‖ * ‖v‖ := by
    rintro ⟨v, c, rfl⟩
    rw [hf₀c, Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hnorm]
    rfl
  set f := f₀.mkContinuous ‖g‖ hbound
  obtain ⟨Λ, hΛ, hΛn⟩ := exists_extension_norm_eq (LinearMap.range L₀) f
  refine ⟨Λ, hΛn ▸ LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _, fun t => ?_⟩
  have h1 : L₀ (Finsupp.single t 1) = chi0 hb t := by simp [hL₀]
  have h2 : L (Finsupp.single t 1) = χ t := by simp [hL]
  have := hΛ ⟨L₀ (Finsupp.single t 1), LinearMap.mem_range_self L₀ _⟩
  simp only [f, LinearMap.mkContinuous_apply, hf₀c, h2] at this
  rw [← this, h1]

lemma series_rep (hb : 0 ≤ b) (χ : ℝ → H) (hχ : ∀ s t, ⟪χ s, χ t⟫_ℝ = Real.exp (b * s * t)) (g : H) :
    ∃ w : ℕ → ℝ, (∀ k, |w k| ≤ ‖g‖) ∧ ∀ t, HasSum (fun k => w k * cf b t k) ⟪g, χ t⟫_ℝ := by
  obtain ⟨Λ, hΛn, hΛ⟩ := exists_functional hb χ hχ g
  refine ⟨fun k => Λ (lp.single 2 k (1 : ℝ)), fun k => ?_, fun t => ?_⟩
  · rw [← Real.norm_eq_abs]
    refine (Λ.le_opNorm _).trans ?_
    rw [lp.norm_single (by norm_num), norm_one, mul_one]
    exact hΛn
  · have h := Λ.hasSum (lp.hasSum_single (p := 2) (by norm_num) (chi0 hb t))
    rw [hΛ] at h
    convert h using 1
    funext k
    change Λ (lp.single 2 k 1) * cf b t k = Λ (lp.single 2 k (cf b t k))
    rw [show cf b t k = cf b t k • (1 : ℝ) by rw [smul_eq_mul, mul_one], lp.single_smul, map_smul, smul_eq_mul,
      smul_eq_mul, mul_one, mul_comm]

lemma analytic_series (hb : 0 ≤ b) {a : ℕ → ℝ} {C : ℝ} (ha : ∀ k, |a k| ≤ C) :
    AnalyticOnNhd ℝ (fun t => ∑' k, a k * cf b t k) univ := by
  set c : ℕ → ℝ := fun k => a k * Real.sqrt (b ^ k / k !) with hc
  have hC : 0 ≤ C := (abs_nonneg _).trans (ha 0)
  have hrad : (FormalMultilinearSeries.ofScalars ℝ c).radius = ⊤ := by
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    refine FormalMultilinearSeries.le_radius_of_bound _ (C * Real.sqrt (Real.exp (b * (r : ℝ) ^ 2))) fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, hc, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hr : (0 : ℝ) ≤ r := r.2
    have e : Real.sqrt (b ^ n / n !) * (r : ℝ) ^ n = Real.sqrt ((b * (r : ℝ) ^ 2) ^ n / n !) := by
      rw [← Real.sqrt_sq (pow_nonneg hr n), ← Real.sqrt_mul (by positivity)]
      congr 1
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 n]
      ring
    calc |a n| * Real.sqrt (b ^ n / n !) * (r : ℝ) ^ n = |a n| * (Real.sqrt (b ^ n / n !) * (r : ℝ) ^ n) := by ring
      _ ≤ C * Real.sqrt (Real.exp (b * (r : ℝ) ^ 2)) := by
        rw [e]
        exact mul_le_mul (ha n) (Real.sqrt_le_sqrt (Real.pow_div_factorial_le_exp (x := b * (r : ℝ) ^ 2) (by positivity) n))
          (Real.sqrt_nonneg _) hC
  have hps := (FormalMultilinearSeries.ofScalars ℝ c).hasFPowerSeriesOnBall (by rw [hrad]; exact ENNReal.zero_lt_top)
  rw [hrad] at hps
  have heq : (fun t => ∑' k, a k * cf b t k) = (FormalMultilinearSeries.ofScalars ℝ c).sum := by
    funext t
    change _ = FormalMultilinearSeries.ofScalarsSum c t
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    refine tsum_congr fun k => ?_
    simp only [hc, cf, smul_eq_mul]
    ring
  rw [heq]
  intro t _
  exact hps.analyticAt_of_mem (by simp [Metric.eball])

/-! ### The Gaussian kernel: witness functions constant on an open set are constant -/

section Gauss

variable {d : ℕ} {Φ : EuclideanSpace ℝ (Fin d) → H} {σ : ℝ}

lemma line_analytic (hG : ∀ x y, ⟪Φ x, Φ y⟫_ℝ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) (g : H)
    (x₀ v : EuclideanSpace ℝ (Fin d)) :
    AnalyticOnNhd ℝ (fun t : ℝ => ⟪g, Φ (x₀ + t • v)⟫_ℝ) univ := by
  set a : ℝ := ‖v‖ ^ 2 / (2 * σ ^ 2) with ha
  have ha0 : 0 ≤ a := by positivity
  set χ : ℝ → H := fun t => Real.exp (a * t ^ 2) • Φ (x₀ + t • v) with hχ
  have hgram : ∀ s t, ⟪χ s, χ t⟫_ℝ = Real.exp (2 * a * s * t) := by
    intro s t
    simp only [hχ, real_inner_smul_left, real_inner_smul_right, hG]
    have e : x₀ + s • v - (x₀ + t • v) = (s - t) • v := by rw [sub_smul]; abel
    rw [e, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [ha]
    by_cases hσ : σ = 0
    · simp [hσ]
    · field_simp
      ring
  obtain ⟨w, hw, hser⟩ := series_rep (by positivity : (0 : ℝ) ≤ 2 * a) χ hgram g
  have hGan := analytic_series (b := 2 * a) (by positivity) hw
  have hfun : (fun t : ℝ => ⟪g, Φ (x₀ + t • v)⟫_ℝ) =
      fun t => Real.exp (-(a * t ^ 2)) * ∑' k, w k * cf (2 * a) t k := by
    funext t
    rw [(hser t).tsum_eq, hχ]
    simp only [real_inner_smul_right]
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  rw [hfun]
  refine AnalyticOnNhd.mul ?_ hGan
  refine AnalyticOnNhd.rexp ?_
  refine AnalyticOnNhd.neg ?_
  exact (analyticOnNhd_const.mul ((analyticOnNhd_id).pow 2))

/-- If `x ↦ ⟪g, Φ x⟫` is constant `c` near `x₀`, it is `c` everywhere (Gaussian Gram). -/
lemma const_of_eventually (hG : ∀ x y, ⟪Φ x, Φ y⟫_ℝ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) (g : H)
    {x₀ : EuclideanSpace ℝ (Fin d)} {c : ℝ} (h : ∀ᶠ x in 𝓝 x₀, ⟪g, Φ x⟫_ℝ = c) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪g, Φ x⟫_ℝ = c := by
  set v := x - x₀
  have hcont : Continuous fun t : ℝ => x₀ + t • v := by fun_prop
  have hev : (fun t : ℝ => ⟪g, Φ (x₀ + t • v)⟫_ℝ) =ᶠ[𝓝 0] fun _ => c := by
    have : Tendsto (fun t : ℝ => x₀ + t • v) (𝓝 0) (𝓝 x₀) := by
      have := hcont.tendsto 0
      simpa using this
    exact this.eventually h
  have heq := (line_analytic hG g x₀ v).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    isPreconnected_univ (mem_univ 0) hev (mem_univ 1)
  simpa [v] using heq

end Gauss

/-! ### Weak sequential compactness of the unit ball -/

lemma weak_subseq [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (u : ℕ → H) (hu : ∀ j, ‖u j‖ ≤ 1) :
    ∃ (ψ : ℕ → ℕ) (ū : H), StrictMono ψ ∧ ∀ h, Tendsto (fun j => ⟪u (ψ j), h⟫_ℝ) atTop (𝓝 ⟪ū, h⟫_ℝ) := by
  set v : ℕ → WeakDual ℝ H := fun j => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u j)) with hvdef
  have hv : ∀ j, v j ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) 1 := by
    intro j
    simp only [hvdef, mem_preimage, Metric.mem_closedBall, dist_zero_right]
    change ‖InnerProductSpace.toDual ℝ H (u j)‖ ≤ 1
    rw [LinearIsometryEquiv.norm_map]
    exact hu j
  obtain ⟨a, -, ψ, hψ, hlim⟩ := WeakDual.isSeqCompact_closedBall (𝕜 := ℝ) (E := H) 0 1 hv
  refine ⟨ψ, (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual a), hψ, fun h => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  have := ((WeakDual.eval_continuous h).tendsto a).comp hlim
  exact this

/-! ### Bathtub uniqueness for a generic minimiser (adapted from `Wave30tn.popthreshold_route`) -/

open StatFormal.TrimmedMMD.ZeroSet (IsTrimDensity) in
lemma bathtub_unique {𝒳 : Type*} [MeasurableSpace 𝒳] (P : Measure 𝒳) [IsProbabilityMeasure P] {Z : 𝒳 → ℝ}
    (hZm : Measurable Z) {K : ℝ} (hZb : ∀ x, |Z x| ≤ K) {α t : ℝ} (hα1 : α < 1) {g : 𝒳 → ℝ}
    (hg : IsTrimDensity P α g)
    (hmin : ∀ g' : 𝒳 → ℝ, IsTrimDensity P α g' → ∫ x, g x * Z x ∂P ≤ ∫ x, g' x * Z x ∂P)
    (ht1 : P.real {x | Z x < t} ≤ 1 - α) (ht2 : 1 - α ≤ P.real {x | Z x ≤ t}) :
    (∀ᵐ x ∂P, Z x < t → g x = 1 / (1 - α)) ∧ (∀ᵐ x ∂P, t < Z x → g x = 0) := by
  have hβ' : 0 < 1 - α := by linarith
  set B := 1 / (1 - α) with hBdef
  have hB0 : 0 < B := by positivity
  set p1 := P.real {x | Z x < t}
  set p2 := P.real {x | Z x = t}
  have hle : P.real {x | Z x ≤ t} = p1 + p2 := by
    have hu : {x | Z x ≤ t} = {x | Z x < t} ∪ {x | Z x = t} := by
      ext x; simp only [mem_ofPred_eq, mem_union, le_iff_lt_or_eq]
    have hdisj : Disjoint {x | Z x < t} {x | Z x = t} := Set.disjoint_left.2 fun x hx hx' => by
      have h1 : Z x < t := hx
      have h2 : Z x = t := hx'
      linarith
    rw [hu, measureReal_union hdisj (measurableSet_eq_fun hZm measurable_const)]
  have hp2 : 0 ≤ p2 := measureReal_nonneg
  have hBp1 : B * p1 ≤ 1 := by rw [hBdef, div_mul_eq_mul_div, one_mul, div_le_one hβ']; exact ht1
  have hBp12 : 1 ≤ B * (p1 + p2) := by rw [hBdef, div_mul_eq_mul_div, one_mul, le_div_iff₀ hβ', one_mul, ← hle]; exact ht2
  -- the bathtub density
  set θ : ℝ := if p2 = 0 then 0 else (1 - B * p1) / p2 with hθdef
  have hθ : 0 ≤ θ ∧ θ ≤ B ∧ B * p1 + θ * p2 = 1 := by
    by_cases h0 : p2 = 0
    · simp only [hθdef, h0, ite_true, mul_zero, add_zero, le_refl, true_and]
      refine ⟨hB0.le, ?_⟩
      rw [h0, add_zero] at hBp12; linarith
    · have hp2' : 0 < p2 := lt_of_le_of_ne hp2 (Ne.symm h0)
      simp only [hθdef, h0, ite_false]
      refine ⟨div_nonneg (by linarith) hp2, ?_, ?_⟩
      · rw [div_le_iff₀ hp2']; nlinarith
      · field_simp; ring
  set gb : 𝒳 → ℝ := fun x => if Z x < t then B else if Z x = t then θ else 0 with hgbdef
  have hgbm : Measurable gb :=
    Measurable.ite (measurableSet_lt hZm measurable_const) measurable_const
      (Measurable.ite (measurableSet_eq_fun hZm measurable_const) measurable_const measurable_const)
  have hgb : IsTrimDensity P α gb := by
    refine ⟨hgbm, fun x => ?_, ?_⟩
    · simp only [gb]; split_ifs <;> constructor <;> linarith [hθ.1, hθ.2.1]
    · have e : gb = fun x => B * ({x | Z x < t}.indicator 1 x) + θ * ({x | Z x = t}.indicator 1 x) := by
        funext x; simp only [gb, Set.indicator, mem_ofPred_eq, Pi.one_apply]
        split_ifs <;> first | (exfalso; linarith) | simp
      simp only [e]
      rw [integral_add (f := fun x => B * {x | Z x < t}.indicator 1 x) (g := fun x => θ * {x | Z x = t}.indicator 1 x)
        ((integrable_const (1 : ℝ)).indicator (measurableSet_lt hZm measurable_const) |>.const_mul _)
        ((integrable_const (1 : ℝ)).indicator (measurableSet_eq_fun hZm measurable_const) |>.const_mul _),
        integral_const_mul, integral_const_mul,
        integral_indicator_one (measurableSet_lt hZm measurable_const),
        integral_indicator_one (measurableSet_eq_fun hZm measurable_const)]
      exact hθ.2.2
  have h1 := hmin gb hgb
  -- integrability
  have hbd : ∀ {g' : 𝒳 → ℝ}, IsTrimDensity P α g' → Integrable (fun x => g' x * Z x) P := fun {g'} hg' =>
    Integrable.of_bound (hg'.1.mul hZm).aestronglyMeasurable (B * K) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (StatFormal.Wave30tn.trimDensity_bound hg' x) (hZb x) (abs_nonneg _) hB0.le)
  have hgi : ∀ {g' : 𝒳 → ℝ}, IsTrimDensity P α g' → Integrable g' P := fun {g'} hg' =>
    Integrable.of_bound hg'.1.aestronglyMeasurable _ (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact StatFormal.Wave30tn.trimDensity_bound hg' x)
  -- the product
  set D : 𝒳 → ℝ := fun x => (g x - gb x) * (Z x - t) with hDdef
  have hDnn : ∀ x, 0 ≤ D x := fun x => by
    simp only [D, gb]
    have hg1 := (hg.2.1 x).1; have hg2 := (hg.2.1 x).2
    split_ifs with h1 h2
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · rw [h2, sub_self, mul_zero]
    · push Not at h1; have : t < Z x := lt_of_le_of_ne h1 (Ne.symm h2)
      exact mul_nonneg (by linarith) (by linarith)
  have hDint : ∫ x, D x ∂P = ∫ x, g x * Z x ∂P - ∫ x, gb x * Z x ∂P := by
    have e : D = fun x => (g x * Z x - gb x * Z x) - t * (g x - gb x) := by funext x; simp only [D]; ring
    simp only [e]
    rw [integral_sub (f := fun x => g x * Z x - gb x * Z x) (g := fun x => t * (g x - gb x))
        ((hbd hg).sub (hbd hgb)) (((hgi hg).sub (hgi hgb)).const_mul t),
      integral_sub (f := fun x => g x * Z x) (g := fun x => gb x * Z x) (hbd hg) (hbd hgb), integral_const_mul,
      integral_sub (f := g) (g := gb) (hgi hg) (hgi hgb), hg.2.2, hgb.2.2]
    ring
  have hDle : ∫ x, D x ∂P ≤ 0 := by rw [hDint]; linarith
  have hDI : Integrable D P := by
    have e : D = fun x => (g x * Z x - gb x * Z x) - t * (g x - gb x) := by funext x; simp only [D]; ring
    rw [e]; exact ((hbd hg).sub (hbd hgb)).sub (((hgi hg).sub (hgi hgb)).const_mul t)
  have hD0 : D =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg hDnn hDI).1
    (le_antisymm hDle (integral_nonneg hDnn))
  refine ⟨?_, ?_⟩
  · filter_upwards [hD0] with x hx hlt
    have hgbx : gb x = B := if_pos hlt
    have hx' : (g x - gb x) * (Z x - t) = 0 := hx
    rw [hgbx] at hx'
    rcases mul_eq_zero.1 hx' with h | h
    · linarith
    rcases mul_eq_zero.1 hx' with h | h
    · linarith
    · exfalso; linarith
  · filter_upwards [hD0] with x hx hgt
    have hn1 : ¬ Z x < t := not_lt.2 hgt.le
    have hn2 : ¬ Z x = t := ne_of_gt hgt
    have hgbx : gb x = 0 := (if_neg hn1).trans (if_neg hn2)
    have hx' : (g x - gb x) * (Z x - t) = 0 := hx
    rw [hgbx, sub_zero] at hx'
    rcases mul_eq_zero.1 hx' with h | h
    · exact h
    · exfalso; linarith


/-! ### Generic facts on the regions and the contact law -/

section Generic

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.Projection
  StatFormal.TrimmedMMD.ZeroSet StatFormal.Foundations.TrimmedMean

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma kappa_nonneg (P : Measure 𝒳) [IsProbabilityMeasure P] {Φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖Φ x‖ ≤ κ) : 0 ≤ κ := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  exact (norm_nonneg _).trans (hκ x₀)

lemma integrable_trim {P : Measure 𝒳} [IsProbabilityMeasure P] {α : ℝ} {g : 𝒳 → ℝ} (hg : IsTrimDensity P α g) :
    Integrable g P :=
  Integrable.of_bound hg.1.aestronglyMeasurable _
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact StatFormal.Wave30tn.trimDensity_bound hg x)

lemma norm_le_of_mem_region (P : Measure 𝒳) [IsProbabilityMeasure P] {Φ : 𝒳 → H} {κ α : ℝ}
    (hκ : ∀ x, ‖Φ x‖ ≤ κ) {a : H} (ha : a ∈ region Φ α P) : ‖a‖ ≤ κ := by
  obtain ⟨g, hgm, hgb, hg1, rfl⟩ := ha
  have hgi : Integrable g P := integrable_trim ⟨hgm, hgb, hg1⟩
  calc ‖∫ x, g x • Φ x ∂P‖ ≤ ∫ x, ‖g x • Φ x‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ x, g x * κ ∂P := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hgi.mul_const κ)
          (ae_of_all _ fun x => ?_)
        change ‖g x • Φ x‖ ≤ g x * κ
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hgb x).1]
        exact mul_le_mul_of_nonneg_left (hκ x) (hgb x).1
    _ = κ := by rw [integral_mul_const, hg1, one_mul]

lemma region_mono {P : Measure 𝒳} {Φ : 𝒳 → H} {α α' : ℝ} (hα : α ≤ α') (hα' : α' < 1) :
    region Φ α P ⊆ region Φ α' P := by
  rintro z ⟨g, hgm, hgb, hg1, rfl⟩
  refine ⟨g, hgm, fun x => ⟨(hgb x).1, (hgb x).2.trans ?_⟩, hg1, rfl⟩
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma norm_integral_le_kappa (R : Measure 𝒳) [IsProbabilityMeasure R] {Φ : 𝒳 → H} {κ : ℝ}
    (hκ : ∀ x, ‖Φ x‖ ≤ κ) : ‖∫ x, Φ x ∂R‖ ≤ κ := by
  have := norm_integral_le_of_norm_le_const (μ := R) (ae_of_all _ hκ)
  rwa [probReal_univ, mul_one] at this

/-- The contact law is a probability measure, absolutely continuous with respect to `P`, with density `≤ β*`. -/
lemma contactLaw_mem (hc : StatFormal.Wave30tx.Claims.contact) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [TopologicalSpace.SeparableSpace H] {Φ : 𝒳 → H} {κ : ℝ}
    (hΦ : StronglyMeasurable Φ) (hκ : ∀ x, ‖Φ x‖ ≤ κ) (hchar : Characteristic Φ)
    (htv1 : StatFormal.Distances.tvDist P Q < 1) :
    StatFormal.Wave30tx.contactLaw P Q ∈ StatFormal.Wave8a.trimSet P (StatFormal.Distances.tvDist P Q) :=
  (hc 𝒳 H P Q Φ κ hΦ hκ hchar htv1).2.2.1.1

/-- The bounded version `g_R = min(dR*/dP, β*)` of the density of the contact law. -/
def gR (P Q : Measure 𝒳) (x : 𝒳) : ℝ :=
  min ((StatFormal.Wave30tx.contactLaw P Q).rnDeriv P x).toReal (1 / (1 - StatFormal.Distances.tvDist P Q))

lemma gR_props {P Q : Measure 𝒳} [IsProbabilityMeasure P]
    (hR : StatFormal.Wave30tx.contactLaw P Q ∈ StatFormal.Wave8a.trimSet P (StatFormal.Distances.tvDist P Q))
    (htv1 : StatFormal.Distances.tvDist P Q < 1) :
    gR P Q =ᵐ[P] (fun x => ((StatFormal.Wave30tx.contactLaw P Q).rnDeriv P x).toReal) ∧
      IsTrimDensity P (StatFormal.Distances.tvDist P Q) (gR P Q) ∧
      ∀ {Φ : 𝒳 → H}, ∫ x, gR P Q x • Φ x ∂P = ∫ x, Φ x ∂(StatFormal.Wave30tx.contactLaw P Q) := by
  obtain ⟨hRp, hac, hle⟩ := hR
  have := hRp
  have hβ0 : 0 ≤ 1 / (1 - StatFormal.Distances.tvDist P Q) := by
    have : 0 < 1 - StatFormal.Distances.tvDist P Q := by linarith
    positivity
  have hae : gR P Q =ᵐ[P] (fun x => ((StatFormal.Wave30tx.contactLaw P Q).rnDeriv P x).toReal) := by
    filter_upwards [hle] with x hx
    exact min_eq_left (ENNReal.toReal_le_of_le_ofReal hβ0 hx)
  refine ⟨hae, ⟨?_, fun x => ⟨le_min ENNReal.toReal_nonneg hβ0, min_le_right _ _⟩, ?_⟩, fun {Φ} => ?_⟩
  · exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.min measurable_const
  · rw [integral_congr_ae hae, Measure.integral_toReal_rnDeriv hac, probReal_univ]
  · rw [← integral_rnDeriv_smul hac]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]

lemma Dpop_nonneg' {Φ : 𝒳 → H} {P Q : Measure 𝒳} {α : ℝ} : 0 ≤ Dpop Φ P Q α :=
  Real.sInf_nonneg (by rintro _ ⟨a, -, b, -, rfl⟩; exact norm_nonneg _)

lemma Dpop_pos (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [TopologicalSpace.SeparableSpace H] {Φ : 𝒳 → H} {κ : ℝ} (hΦ : StronglyMeasurable Φ) (hκ : ∀ x, ‖Φ x‖ ≤ κ)
    (hchar : Characteristic Φ) {α : ℝ} (hα : α ∈ Ico 0 (StatFormal.Distances.tvDist P Q))
    (htv1 : StatFormal.Distances.tvDist P Q < 1) : 0 < Dpop Φ P Q α := by
  refine lt_of_le_of_ne Dpop_nonneg' fun h => ?_
  have := (StatFormal.TrimmedMMD.ZeroSet.zeroeq 𝒳 H P Q Φ κ α hΦ hκ hchar hα.1 (by linarith [hα.2])).1 h.symm
  linarith [hα.2]

/-- Step 1 of the proof of the remark: the trimmed embeddings converge to `μ_{R*}`. -/
lemma emb_tendsto (hc : StatFormal.Wave30tx.Claims.contact) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [TopologicalSpace.SeparableSpace H] {Φ : 𝒳 → H} {κ : ℝ}
    (hΦ : StronglyMeasurable Φ) (hκ : ∀ x, ‖Φ x‖ ≤ κ) (hchar : Characteristic Φ)
    (htv0 : 0 < StatFormal.Distances.tvDist P Q) (htv1 : StatFormal.Distances.tvDist P Q < 1)
    {al : ℕ → ℝ} (hal : ∀ j, al j ∈ Ico 0 (StatFormal.Distances.tvDist P Q))
    (hlim : Tendsto al atTop (𝓝 (StatFormal.Distances.tvDist P Q)))
    {a b : ℕ → H} (ha : ∀ j, a j ∈ region Φ (al j) P) (hb : ∀ j, b j ∈ region Φ (al j) Q)
    (hab : ∀ j, ‖a j - b j‖ = Dpop Φ P Q (al j)) :
    Tendsto (fun j => ‖a j - ∫ x, Φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖) atTop (𝓝 0) := by
  set αs := StatFormal.Distances.tvDist P Q with hαs
  have hcon := hc 𝒳 H P Q Φ κ hΦ hκ hchar htv1
  have hω : Tendsto (StatFormal.Wave30tx.omegaC Φ P Q) (𝓝[>] 0) (𝓝 0) := hcon.2.2.2.2.2
  have hRp : IsProbabilityMeasure (StatFormal.Wave30tx.contactLaw P Q) := hcon.2.2.1.1.1
  have hκ0 := kappa_nonneg P hκ
  set μR := ∫ x, Φ x ∂(StatFormal.Wave30tx.contactLaw P Q)
  have hμR : ‖μR‖ ≤ κ := norm_integral_le_kappa _ hκ
  have hD : ∀ j, 0 < Dpop Φ P Q (al j) := fun j => Dpop_pos P Q hΦ hκ hchar (hal j) htv1
  -- `D_{α_j} → 0`
  have hD0 : Dpop Φ P Q αs = 0 :=
    StatFormal.TrimmedMMD.ZeroSet.zero_of_tv_le 𝒳 H P Q Φ κ αs hΦ hκ htv0.le htv1 le_rfl
  set η := 1 - αs
  have hη0 : 0 < η := by simp only [η]; linarith
  have hη1 : η < 1 := by simp only [η]; linarith
  have hlip : ∀ j, Dpop Φ P Q (al j) ≤ 4 * κ / η ^ 2 * |al j - αs| := by
    intro j
    have := StatFormal.Wave18b.continuity_lip 𝒳 H P Q Φ κ η (al j) αs hΦ hκ hη0 hη1
      ⟨(hal j).1, by simp only [η]; linarith [(hal j).2]⟩ ⟨htv0.le, by simp only [η]; linarith⟩
    rw [hD0, sub_zero, abs_of_pos (hD j)] at this
    exact this
  have hDlim : Tendsto (fun j => Dpop Φ P Q (al j)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hD⟩
    have h1 : Tendsto (fun j => 4 * κ / η ^ 2 * |al j - αs|) atTop (𝓝 0) := by
      have : Tendsto (fun j => |al j - αs|) atTop (𝓝 0) := by
        have := (hlim.sub_const αs).abs
        simpa using this
      simpa using this.const_mul (4 * κ / η ^ 2)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun j => (hD j).le) hlip
  -- `‖a_j − μ_{R*}‖ ≤ ω_c(D_{α_j})`
  have hbound : ∀ j, ‖a j - μR‖ ≤ StatFormal.Wave30tx.omegaC Φ P Q (Dpop Φ P Q (al j)) := by
    intro j
    have haj : a j ∈ region Φ αs P := region_mono (hal j).2.le htv1 (ha j)
    have hbj : b j ∈ region Φ αs Q := region_mono (hal j).2.le htv1 (hb j)
    refine le_csSup ⟨κ + κ, ?_⟩ ⟨a j, haj, ?_, rfl⟩
    · rintro r ⟨a', ha', -, rfl⟩
      exact (norm_sub_le _ _).trans (add_le_add (norm_le_of_mem_region P hκ ha') hμR)
    · refine (Metric.infDist_le_dist_of_mem hbj).trans ?_
      rw [dist_eq_norm, hab j]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hω.comp hDlim)
    (fun j => norm_nonneg _) hbound

lemma integrable_Phi (P : Measure 𝒳) [IsProbabilityMeasure P] {Φ : 𝒳 → H} {κ : ℝ} (hΦ : StronglyMeasurable Φ)
    (hκ : ∀ x, ‖Φ x‖ ≤ κ) : Integrable Φ P :=
  Integrable.of_bound hΦ.aestronglyMeasurable κ (ae_of_all _ hκ)

/-- Step 4 of the proof of the remark: along `α_j ↑ α*` with `f*_{α_j} ⇀ f̄`, the contact density `g_R` minimises
`g ↦ ∫ g ⟨f̄, φ⟩ dP` over the `α*`-trimming densities. -/
lemma limit_min (hc : StatFormal.Wave30tx.Claims.contact) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [TopologicalSpace.SeparableSpace H] {Φ : 𝒳 → H} {κ : ℝ}
    (hΦ : StronglyMeasurable Φ) (hκ : ∀ x, ‖Φ x‖ ≤ κ) (hchar : Characteristic Φ)
    (htv0 : 0 < StatFormal.Distances.tvDist P Q) (htv1 : StatFormal.Distances.tvDist P Q < 1)
    {dstar : ℝ → H}
    (hmin : ∀ α ∈ Ico 0 (StatFormal.Distances.tvDist P Q), IsMinNorm (region Φ α P - region Φ α Q) (dstar α))
    {al : ℕ → ℝ} (hal : ∀ j, al j ∈ Ico 0 (StatFormal.Distances.tvDist P Q))
    (hlim : Tendsto al atTop (𝓝 (StatFormal.Distances.tvDist P Q))) {fbar : H}
    (hw : ∀ h, Tendsto (fun j => ⟪(Dpop Φ P Q (al j))⁻¹ • dstar (al j), h⟫_ℝ) atTop (𝓝 ⟪fbar, h⟫_ℝ))
    {g : 𝒳 → ℝ} (hg : IsTrimDensity P (StatFormal.Distances.tvDist P Q) g) :
    ∫ x, gR P Q x * ⟪fbar, Φ x⟫_ℝ ∂P ≤ ∫ x, g x * ⟪fbar, Φ x⟫_ℝ ∂P := by
  set αs := StatFormal.Distances.tvDist P Q with hαs
  have hD : ∀ j, 0 < Dpop Φ P Q (al j) := fun j => Dpop_pos P Q hΦ hκ hchar (hal j) htv1
  have hDn : ∀ j, ‖dstar (al j)‖ = Dpop Φ P Q (al j) := fun j =>
    (StatFormal.Wave30tx.RBasic.Dpop_eq_norm (hmin (al j) (hal j))).symm
  have hdec : ∀ j, ∃ (gj : 𝒳 → ℝ) (bj : H), IsTrimDensity P (al j) gj ∧ bj ∈ region Φ (al j) Q ∧
      dstar (al j) = ∫ x, gj x • Φ x ∂P - bj := by
    intro j
    obtain ⟨a, ⟨gj, hgm, hgb, hg1, rfl⟩, bj, hbj, he⟩ := (hmin (al j) (hal j)).1
    exact ⟨gj, bj, ⟨hgm, hgb, hg1⟩, hbj, he.symm⟩
  choose gj bj hgj hbj hdj using hdec
  set f : ℕ → H := fun j => (Dpop Φ P Q (al j))⁻¹ • dstar (al j) with hf
  have hfn : ∀ j, ‖f j‖ = 1 := fun j => by
    rw [hf, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hD j), hDn, inv_mul_cancel₀ (hD j).ne']
  have hdf : ∀ j, dstar (al j) = Dpop Φ P Q (al j) • f j := fun j => by
    rw [hf, smul_inv_smul₀ (hD j).ne']
  have hR := contactLaw_mem hc P Q hΦ hκ hchar htv1
  obtain ⟨-, hgRt, hgRint⟩ := gR_props (H := H) hR htv1
  set μR := ∫ x, Φ x ∂(StatFormal.Wave30tx.contactLaw P Q) with hμR
  set A := fun j => ∫ x, gj j x • Φ x ∂P with hA
  -- (4a)
  have hAlim := emb_tendsto hc P Q hΦ hκ hchar htv0 htv1 hal hlim (a := A) (b := bj)
    (fun j => ⟨gj j, (hgj j).1, (hgj j).2.1, (hgj j).2.2, rfl⟩) hbj
    (fun j => by rw [hA]; simp only; rw [← hdj j, hDn])
  have h4a : Tendsto (fun j => ⟪f j, A j⟫_ℝ) atTop (𝓝 ⟪fbar, μR⟫_ℝ) := by
    have e : ∀ j, ⟪f j, A j⟫_ℝ = ⟪f j, A j - μR⟫_ℝ + ⟪f j, μR⟫_ℝ := fun j => by
      rw [inner_sub_right]; ring
    simp_rw [e]
    rw [show ⟪fbar, μR⟫_ℝ = 0 + ⟪fbar, μR⟫_ℝ by ring]
    refine Tendsto.add ?_ (hw μR)
    refine squeeze_zero_norm (fun j => ?_) hAlim
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hfn, one_mul]
  -- the constants `β_j`, `β*`, `ε_j`
  set βs := 1 / (1 - αs) with hβs
  set β : ℕ → ℝ := fun j => 1 / (1 - al j) with hβ
  set ε : ℕ → ℝ := fun j => (βs - β j) / (βs - 1) with hε
  have h1αs : 0 < 1 - αs := by linarith
  have hβs1 : 1 < βs := by rw [hβs, lt_div_iff₀ h1αs]; linarith
  have hβj : ∀ j, 1 ≤ β j ∧ β j ≤ βs := fun j => by
    have h0 := (hal j).1; have h1 := (hal j).2
    have hpos : 0 < 1 - al j := by linarith
    refine ⟨?_, ?_⟩
    · rw [hβ, le_div_iff₀ hpos]; linarith
    · exact one_div_le_one_div_of_le h1αs (by linarith)
  have hε01 : ∀ j, 0 ≤ ε j ∧ ε j ≤ 1 := fun j => by
    have := hβj j
    refine ⟨div_nonneg (by linarith) (by linarith), ?_⟩
    rw [hε, div_le_one (by linarith)]; linarith
  have hεβ : ∀ j, (1 - ε j) * βs + ε j = β j := fun j => by
    have hne : βs - 1 ≠ 0 := by linarith
    calc (1 - ε j) * βs + ε j = βs - ε j * (βs - 1) := by ring
      _ = βs - (βs - β j) := by simp only [hε]; rw [div_mul_cancel₀ _ hne]
      _ = β j := by ring
  -- (4c)
  have hΦi := integrable_Phi P hΦ hκ
  have hgi := integrable_trim hg
  have hgΦ : Integrable (fun x => g x • Φ x) P :=
    StatFormal.Wave30tn.integrable_smul_phi P hΦ hκ hg.1 (StatFormal.Wave30tn.trimDensity_bound hg)
  have h4c : ∀ j, ⟪f j, A j⟫_ℝ ≤ (1 - ε j) * ⟪f j, ∫ x, g x • Φ x ∂P⟫_ℝ + ε j * ⟪f j, ∫ x, Φ x ∂P⟫_ℝ := by
    intro j
    set g' : 𝒳 → ℝ := fun x => (1 - ε j) * g x + ε j with hg'
    have hg't : IsTrimDensity P (al j) g' := by
      refine ⟨(hg.1.const_mul _).add measurable_const, fun x => ⟨?_, ?_⟩, ?_⟩
      · have := (hg.2.1 x).1; have := hε01 j
        change 0 ≤ (1 - ε j) * g x + ε j; nlinarith
      · have hgx := (hg.2.1 x).2
        have he := hε01 j
        change (1 - ε j) * g x + ε j ≤ 1 / (1 - al j)
        have h2 : (1 - ε j) * g x ≤ (1 - ε j) * βs := mul_le_mul_of_nonneg_left hgx (by linarith)
        have h3 := hεβ j
        have h4 : β j = 1 / (1 - al j) := rfl
        linarith
      · simp only [hg']
        rw [integral_add (hgi.const_mul _) (integrable_const _), integral_const_mul, hg.2.2, integral_const,
          probReal_univ, one_smul]
        ring
    have hfoc := StatFormal.Wave30tn.foc P Q hΦ hκ ((hal j).2.trans htv1) (hmin (al j) (hal j)).2 (hgj j)
      (hbj j) (hdj j) hg't
    have hint1 : ∫ x, gj j x * ⟪dstar (al j), Φ x⟫_ℝ ∂P = Dpop Φ P Q (al j) * ⟪f j, A j⟫_ℝ := by
      rw [← inner_integral_smul P hΦ hκ (hgj j).1 (StatFormal.Wave30tn.trimDensity_bound (hgj j)), hdf j,
        real_inner_smul_left]
    have hg'b : ∀ x, |g' x| ≤ 1 / (1 - al j) := StatFormal.Wave30tn.trimDensity_bound hg't
    have hint2 : ∫ x, g' x * ⟪dstar (al j), Φ x⟫_ℝ ∂P = Dpop Φ P Q (al j) *
        ((1 - ε j) * ⟪f j, ∫ x, g x • Φ x ∂P⟫_ℝ + ε j * ⟪f j, ∫ x, Φ x ∂P⟫_ℝ) := by
      rw [← inner_integral_smul P hΦ hκ hg't.1 hg'b, hdf j, real_inner_smul_left]
      congr 1
      have e : (fun x => g' x • Φ x) = fun x => (1 - ε j) • (g x • Φ x) + ε j • Φ x := by
        funext x; simp only [hg', add_smul, smul_smul]
      rw [e, integral_add (f := fun x => (1 - ε j) • (g x • Φ x)) (g := fun x => ε j • Φ x)
        (hgΦ.smul (1 - ε j)) (hΦi.smul (ε j)), integral_smul, integral_smul, inner_add_right,
        real_inner_smul_right, real_inner_smul_right]
    rw [hint1, hint2] at hfoc
    exact le_of_mul_le_mul_left hfoc (hD j)
  -- limits
  have hβlim : Tendsto β atTop (𝓝 βs) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub hlim
    exact tendsto_const_nhds.div this h1αs.ne'
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := βs)).sub hβlim
    rw [sub_self] at this
    simpa [hε, zero_div] using this.div_const (βs - 1)
  have hRHS : Tendsto (fun j => (1 - ε j) * ⟪f j, ∫ x, g x • Φ x ∂P⟫_ℝ + ε j * ⟪f j, ∫ x, Φ x ∂P⟫_ℝ) atTop
      (𝓝 ((1 - 0) * ⟪fbar, ∫ x, g x • Φ x ∂P⟫_ℝ + 0 * ⟪fbar, ∫ x, Φ x ∂P⟫_ℝ)) :=
    ((tendsto_const_nhds.sub hεlim).mul (hw _)).add (hεlim.mul (hw _))
  have hle := le_of_tendsto_of_tendsto' h4a hRHS h4c
  rw [sub_zero, one_mul, zero_mul, add_zero] at hle
  have hgRb : ∀ x, |gR P Q x| ≤ 1 / (1 - αs) := StatFormal.Wave30tn.trimDensity_bound hgRt
  rw [← inner_integral_smul P hΦ hκ hgRt.1 hgRb, ← inner_integral_smul P hΦ hκ hg.1
    (StatFormal.Wave30tn.trimDensity_bound hg), hgRint]
  exact hle

end Generic

/-! ### The Gaussian setting on `ℝ^d` -/

section Euclid

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.Projection
  StatFormal.TrimmedMMD.ZeroSet StatFormal.Foundations.TrimmedMean

variable {d : ℕ}

lemma continuous_of_gauss {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {Φ : EuclideanSpace ℝ (Fin d) → H} {σ : ℝ}
    (hG : ∀ x y, ⟪Φ x, Φ y⟫_ℝ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) : Continuous Φ := by
  have hsq : ∀ x y, ‖Φ y - Φ x‖ ^ 2 = 2 - 2 * Real.exp (-‖y - x‖ ^ 2 / (2 * σ ^ 2)) := by
    intro x y
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hG, hG, hG]
    simp only [sub_self, norm_zero]
    norm_num
    ring
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have e : (fun y => ‖Φ y - Φ x‖) = fun y => Real.sqrt (2 - 2 * Real.exp (-‖y - x‖ ^ 2 / (2 * σ ^ 2))) := by
    funext y; rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [e]
  have hc : Continuous fun y : EuclideanSpace ℝ (Fin d) =>
      Real.sqrt (2 - 2 * Real.exp (-‖y - x‖ ^ 2 / (2 * σ ^ 2))) := by fun_prop
  have := hc.tendsto x
  simpa using this

lemma open_null_empty {p : EuclideanSpace ℝ (Fin d) → ℝ} (hpm : Measurable p) {O : Set (EuclideanSpace ℝ (Fin d))}
    (hO : IsOpen O) (hpos : ∀ x ∈ O, 0 < p x)
    (hnull : (volume.withDensity fun x => ENNReal.ofReal (p x)) O = 0) : O = ∅ := by
  rw [withDensity_apply _ hO.measurableSet,
    lintegral_eq_zero_iff (f := fun x => ENNReal.ofReal (p x)) (ENNReal.measurable_ofReal.comp hpm)] at hnull
  have h := (ae_restrict_iff' hO.measurableSet).1 hnull
  have hvol : volume O = 0 := by
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 h)
    simp only [mem_setOf_eq, Pi.zero_apply]
    intro hcon
    exact (ENNReal.ofReal_pos.2 (hpos x hx)).ne' (hcon hx)
  exact (hO.measure_eq_zero_iff volume).1 hvol

/-- The heart of (b): along `α_j ↑ α*`, every weak limit of `f*_{α_j}` is `0`. -/
lemma weak_limit_zero (hc : StatFormal.Wave30tx.Claims.contact)
    (hd : StatFormal.Wave30tx.Claims.nearcontact_densities)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {Φ : EuclideanSpace ℝ (Fin d) → H} {σ κ : ℝ} {p q : EuclideanSpace ℝ (Fin d) → ℝ} {dstar : ℝ → H}
    (hG : ∀ x y, ⟪Φ x, Φ y⟫_ℝ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2)))
    (hpc : Continuous p) (hqc : Continuous q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (P Q : Measure (EuclideanSpace ℝ (Fin d))) (hP : P = volume.withDensity fun x => ENNReal.ofReal (p x))
    (hQ : Q = volume.withDensity fun x => ENNReal.ofReal (q x)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hΦ : StronglyMeasurable Φ) (hκ : ∀ x, ‖Φ x‖ ≤ κ) (hchar : Characteristic Φ)
    (htv0 : 0 < StatFormal.Distances.tvDist P Q) (htv1 : StatFormal.Distances.tvDist P Q < 1)
    (hne : {x | 0 < q x ∧ q x < p x}.Nonempty)
    (hmin : ∀ α ∈ Ico 0 (StatFormal.Distances.tvDist P Q), IsMinNorm (region Φ α P - region Φ α Q) (dstar α))
    {al : ℕ → ℝ} (hal : ∀ j, al j ∈ Ico 0 (StatFormal.Distances.tvDist P Q))
    (hlim : Tendsto al atTop (𝓝 (StatFormal.Distances.tvDist P Q))) {fbar : H}
    (hw : ∀ h, Tendsto (fun j => ⟪(Dpop Φ P Q (al j))⁻¹ • dstar (al j), h⟫_ℝ) atTop (𝓝 ⟪fbar, h⟫_ℝ)) :
    fbar = 0 := by
  set αs := StatFormal.Distances.tvDist P Q with hαs
  set Z : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ⟪fbar, Φ x⟫_ℝ with hZ
  have hΦc := continuous_of_gauss hG
  have hZc : Continuous Z := continuous_const.inner hΦc
  have hZm : Measurable Z := hZc.measurable
  have hZb : ∀ x, |Z x| ≤ ‖fbar‖ * κ := abs_inner_le hκ fbar
  -- the contact density minimises `∫ g Z dP`
  have hR := contactLaw_mem hc P Q hΦ hκ hchar htv1
  obtain ⟨hgRae, hgRt, -⟩ := gR_props (H := H) hR htv1
  have hminZ : ∀ g', IsTrimDensity P αs g' → ∫ x, gR P Q x * Z x ∂P ≤ ∫ x, g' x * Z x ∂P :=
    fun g' hg' => limit_min hc P Q hΦ hκ hchar htv0 htv1 hmin hal hlim hw hg'
  -- a `(1 − α*)`-quantile of `Z`
  set tbar := StatFormal.Wave12c.quantileAt P Z (1 - αs) with htbar
  have hp0' : 0 < 1 - αs := by linarith
  have hp1' : 1 - αs ≤ 1 := by linarith
  have ht1 : P.real {x | Z x < tbar} ≤ 1 - αs := StatFormal.Wave12c.quantile_lt_le P hZm hZb hp0' hp1'
  have ht2 : 1 - αs ≤ P.real {x | Z x ≤ tbar} := StatFormal.Wave12c.quantile_ge P hZm hZb hp0' hp1'
  obtain ⟨hbt1, hbt2⟩ := bathtub_unique P hZm hZb htv1 hgRt hminZ ht1 ht2
  -- the fractional set is `{0 < q < p}`
  have hpm : Measurable p := hpc.measurable
  have hqm : Measurable q := hqc.measurable
  have hPp : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x)) := hP ▸ inferInstance
  have hQp : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (q x)) := hQ ▸ inferInstance
  have hdd := hd (EuclideanSpace ℝ (Fin d)) volume p q hpm hqm hp0 hq0 hPp hQp
  rw [← hP, ← hQ] at hdd
  obtain ⟨-, hfrac, -⟩ := hdd htv1
  have hFZ : ∀ᵐ x ∂P, (0 < q x ∧ q x < p x) → Z x = tbar := by
    filter_upwards [hfrac, hgRae, hbt1, hbt2] with x hx hxg h1 h2 hF
    have hg := hx.2 hF
    rw [← hxg] at hg
    rcases lt_trichotomy (Z x) tbar with hlt | heq | hgt
    · exact absurd (h1 hlt) (ne_of_lt hg.2)
    · exact heq
    · exact absurd (h2 hgt) (ne_of_gt hg.1)
  -- an open `P`-null set is empty
  set O := {x | 0 < q x ∧ q x < p x} ∩ {x | Z x ≠ tbar} with hO
  have hOo : IsOpen O :=
    ((isOpen_lt continuous_const hqc).inter (isOpen_lt hqc hpc)).inter (isOpen_ne_fun hZc continuous_const)
  have hO0 : P O = 0 := by
    rw [ae_iff] at hFZ
    refine measure_mono_null (fun x hx => ?_) hFZ
    simp only [mem_setOf_eq, not_imp]
    exact ⟨hx.1, hx.2⟩
  have hOe : O = ∅ := open_null_empty hpm hOo (fun x hx => hx.1.1.trans hx.1.2) (hP ▸ hO0)
  have hFc : ∀ x, 0 < q x ∧ q x < p x → Z x = tbar := fun x hx => by
    by_contra hne'
    have : x ∈ O := ⟨hx, hne'⟩
    rw [hOe] at this
    exact this
  -- by analyticity `Z ≡ t̄`
  obtain ⟨x₀, hx₀⟩ := hne
  have hFo : IsOpen {x | 0 < q x ∧ q x < p x} := (isOpen_lt continuous_const hqc).inter (isOpen_lt hqc hpc)
  have hev : ∀ᶠ x in 𝓝 x₀, ⟪fbar, Φ x⟫_ℝ = tbar := Filter.mem_of_superset (hFo.mem_nhds hx₀) fun x hx => hFc x hx
  have hconst : ∀ x, Z x = tbar := fun x => const_of_eventually hG fbar hev x
  -- hence `⟨f*_{α_j}, f̄⟩ = 0`
  have hzero : ∀ j, ⟪(Dpop Φ P Q (al j))⁻¹ • dstar (al j), fbar⟫_ℝ = 0 := by
    intro j
    obtain ⟨a, ⟨ga, hgam, hgab, hga1, rfl⟩, b, ⟨gb, hgbm, hgbb, hgb1, rfl⟩, he⟩ := (hmin (al j) (hal j)).1
    have hIa : ⟪fbar, ∫ x, ga x • Φ x ∂P⟫_ℝ = tbar := by
      rw [inner_integral_smul P hΦ hκ hgam (StatFormal.Wave30tn.trimDensity_bound ⟨hgam, hgab, hga1⟩)]
      simp_rw [show ∀ x, ⟪fbar, Φ x⟫_ℝ = tbar from hconst]
      rw [integral_mul_const, hga1, one_mul]
    have hIb : ⟪fbar, ∫ x, gb x • Φ x ∂Q⟫_ℝ = tbar := by
      rw [inner_integral_smul Q hΦ hκ hgbm (StatFormal.Wave30tn.trimDensity_bound ⟨hgbm, hgbb, hgb1⟩)]
      simp_rw [show ∀ x, ⟪fbar, Φ x⟫_ℝ = tbar from hconst]
      rw [integral_mul_const, hgb1, one_mul]
    rw [← he, real_inner_smul_left, real_inner_comm, inner_sub_right, hIa, hIb, sub_self, mul_zero]
  have hlim0 := hw fbar
  simp_rw [hzero] at hlim0
  have h00 : ⟪fbar, fbar⟫_ℝ = 0 := tendsto_nhds_unique hlim0 tendsto_const_nhds
  exact inner_self_eq_zero.1 h00

end Euclid

/-! ### Step 5: the consequences of weak convergence -/

section Step5

variable {𝒳 : Type*} [MeasurableSpace 𝒳] (P : Measure 𝒳) [IsProbabilityMeasure P] {l : Filter ℝ}
  [l.IsCountablyGenerated] {F : ℝ → 𝒳 → ℝ}

lemma prob_tendsto (hFm : ∀ α, Measurable (F α)) (hpt : ∀ x, Tendsto (fun α => F α x) l (𝓝 0)) {η : ℝ}
    (hη : 0 < η) : Tendsto (fun α => P {x | η ≤ |F α x|}) l (𝓝 0) := by
  have hS : ∀ α, MeasurableSet {x | η ≤ |F α x|} := fun α => measurableSet_le measurable_const (continuous_abs.measurable.comp (hFm α))
  have e : ∀ α, P {x | η ≤ |F α x|} = ∫⁻ x, {x | η ≤ |F α x|}.indicator 1 x ∂P := fun α =>
    (lintegral_indicator_one (hS α)).symm
  simp_rw [e]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _x, (0 : ℝ≥0∞) ∂P by simp]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1) (Eventually.of_forall fun α =>
    (measurable_one.indicator (hS α))) (Eventually.of_forall fun α => ae_of_all _ fun x => ?_) (by simp)
    (ae_of_all _ fun x => ?_)
  · exact Set.indicator_le_self' (fun _ _ => bot_le) x
  · have hev : ∀ᶠ α in l, |F α x| < η := by
      have := (hpt x).abs
      rw [abs_zero] at this
      exact this.eventually (gt_mem_nhds hη)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with α hα
    rw [Set.indicator_of_notMem (by simp only [mem_setOf_eq, not_le]; exact hα)]

lemma quantile_tendsto_zero {αs : ℝ} (h0 : 0 < αs) (h1 : αs < 1) {G : ℝ → 𝒳 → ℝ} {s : ℝ → ℝ}
    (hGm : ∀ α, Measurable (G α))
    (hprob : ∀ η : ℝ, 0 < η → Tendsto (fun α => P {x | η ≤ |G α x|}) (𝓝[<] αs) (𝓝 0))
    (hq : ∀ α ∈ Ico 0 αs, P.real {x | G α x < s α} ≤ 1 - α ∧ 1 - α ≤ P.real {x | G α x ≤ s α}) :
    Tendsto s (𝓝[<] αs) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η := ε / 2 with hηdef
  have hη : 0 < η := by positivity
  set δ0 := min (1 - αs) (αs / 2) with hδ0
  have hδ0p : 0 < δ0 := lt_min (by linarith) (by linarith)
  have hev1 : ∀ᶠ α in 𝓝[<] αs, P {x | η ≤ |G α x|} < ENNReal.ofReal δ0 :=
    (hprob η hη).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ0p))
  have hev2 : ∀ᶠ α in 𝓝[<] αs, α ∈ Ioo (αs / 2) αs := Ioo_mem_nhdsLT (by linarith)
  filter_upwards [hev1, hev2] with α hα1 hα2
  have hαI : α ∈ Ico 0 αs := ⟨by linarith [hα2.1], hα2.2⟩
  obtain ⟨hq1, hq2⟩ := hq α hαI
  set S := {x | η ≤ |G α x|} with hSdef
  have hSm : MeasurableSet S := measurableSet_le measurable_const (continuous_abs.measurable.comp (hGm α))
  have hPS : P.real S < δ0 := ENNReal.toReal_lt_of_lt_ofReal hα1
  rw [Real.dist_eq, sub_zero]
  have hle : |s α| ≤ η := by
    rw [abs_le]
    constructor
    · by_contra hcon
      push_neg at hcon
      have hsub : {x | G α x ≤ s α} ⊆ S := fun x hx => by
        simp only [hSdef, mem_setOf_eq] at hx ⊢
        rw [le_abs]; right; linarith
      have := measureReal_mono hsub (μ := P)
      have : δ0 ≤ 1 - αs := min_le_left _ _
      linarith [hα2.2]
    · by_contra hcon
      push_neg at hcon
      have hsub : Sᶜ ⊆ {x | G α x < s α} := fun x hx => by
        simp only [hSdef, mem_compl_iff, mem_setOf_eq, not_le] at hx ⊢
        have := (abs_lt.1 hx).2; linarith
      have h1 := measureReal_mono hsub (μ := P)
      rw [probReal_compl_eq_one_sub hSm] at h1
      have : δ0 ≤ αs / 2 := min_le_right _ _
      linarith [hα2.1]
  linarith

lemma dens_lower_tendsto {s : ℝ → ℝ} (_hFm : ∀ α, Measurable (F α))
    (hcent : ∀ η : ℝ, 0 < η → Tendsto (fun α => P {x | η ≤ |F α x - s α|}) l (𝓝 0)) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun α => StatFormal.Wave30tx.densLower P (F α) (s α - ρ) (s α + ρ)) l (𝓝 0) := by
  have hpos : ENNReal.ofReal (ρ / 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hb : ∀ α, StatFormal.Wave30tx.densLower P (F α) (s α - ρ) (s α + ρ) ≤
      P {x | ρ / 2 ≤ |F α x - s α|} / ENNReal.ofReal (ρ / 2) := by
    intro α
    refine sSup_le fun c hc => ?_
    have h := hc (Icc (s α + ρ / 2) (s α + ρ)) measurableSet_Icc
      (Icc_subset_Icc (by linarith) le_rfl)
    rw [Real.volume_Icc, show s α + ρ - (s α + ρ / 2) = ρ / 2 by ring] at h
    have hsub : F α ⁻¹' Icc (s α + ρ / 2) (s α + ρ) ⊆ {x | ρ / 2 ≤ |F α x - s α|} := fun x hx => by
      simp only [mem_preimage, mem_Icc] at hx
      simp only [mem_setOf_eq]
      rw [le_abs]; left; linarith [hx.1]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top)).2
      (h.trans (measure_mono hsub))
  have hlim : Tendsto (fun α => P {x | ρ / 2 ≤ |F α x - s α|} / ENNReal.ofReal (ρ / 2)) l (𝓝 0) := by
    have := ENNReal.Tendsto.div_const (hcent (ρ / 2) (by positivity)) (Or.inr hpos)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hb

lemma dens_upper_tendsto {s : ℝ → ℝ} (hFm : ∀ α, Measurable (F α))
    (hcent : ∀ η : ℝ, 0 < η → Tendsto (fun α => P {x | η ≤ |F α x - s α|}) l (𝓝 0)) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun α => StatFormal.Wave30tx.densUpper P (F α) (s α - ρ) (s α + ρ)) l (𝓝 ⊤) := by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro y
  set η := min ρ (1 / (4 * ((y : ℝ) + 1))) with hηdef
  have hy0 : (0 : ℝ) ≤ y := y.2
  have hη : 0 < η := lt_min hρ (by positivity)
  have hηρ : η ≤ ρ := min_le_left _ _
  have hηy : η ≤ 1 / (4 * ((y : ℝ) + 1)) := min_le_right _ _
  have hev : ∀ᶠ α in l, P {x | η ≤ |F α x - s α|} < ENNReal.ofReal (1 / 2) :=
    (hcent η hη).eventually (gt_mem_nhds (by simp))
  filter_upwards [hev] with α hα
  set S := {x | η ≤ |F α x - s α|} with hSdef
  have hSm : MeasurableSet S := measurableSet_le measurable_const (continuous_abs.measurable.comp ((hFm α).sub_const _))
  have hPS : P.real S < 1 / 2 := ENNReal.toReal_lt_of_lt_ofReal hα
  have hsubI : Sᶜ ⊆ F α ⁻¹' Icc (s α - η) (s α + η) := fun x hx => by
    simp only [hSdef, mem_compl_iff, mem_setOf_eq, not_le] at hx
    simp only [mem_preimage, mem_Icc]
    have := abs_lt.1 hx
    constructor <;> linarith
  have hhalf : ENNReal.ofReal (1 / 2) ≤ P (F α ⁻¹' Icc (s α - η) (s α + η)) := by
    refine le_trans ?_ (measure_mono hsubI)
    rw [← ofReal_measureReal, probReal_compl_eq_one_sub hSm]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hlow : ENNReal.ofReal (1 / 2) / ENNReal.ofReal (2 * η) ≤
      StatFormal.Wave30tx.densUpper P (F α) (s α - ρ) (s α + ρ) := by
    refine le_sInf fun C hC => ?_
    have h := hC (Icc (s α - η) (s α + η)) measurableSet_Icc (Icc_subset_Icc (by linarith) (by linarith))
    rw [Real.volume_Icc, show s α + η - (s α - η) = 2 * η by ring] at h
    exact ENNReal.div_le_of_le_mul (hhalf.trans h)
  refine lt_of_lt_of_le ?_ hlow
  rw [← ENNReal.ofReal_div_of_pos (by positivity), ← ENNReal.ofReal_coe_nnreal]
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  have h4 : (y : ℝ) + 1 ≤ 1 / 2 / (2 * η) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hηy (by positivity : (0 : ℝ) ≤ 4 * ((y : ℝ) + 1))
    rw [mul_one_div_cancel (by positivity)] at this
    nlinarith
  linarith

end Step5

/-! ### `rem:nearcontact (v2)` (b) -/

section Final

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.Projection
  StatFormal.TrimmedMMD.ZeroSet

theorem nearcontact_b_of (hc : StatFormal.Wave30tx.Claims.contact)
    (hd : StatFormal.Wave30tx.Claims.nearcontact_densities) : StatFormal.Wave30tx.Claims.nearcontact_b := by
  intro d H _ _ _ _ Φ σ κ p q dstar s _hσ hG hpc hqc hp0 hq0 hPp hQp P Q hΦ hκ hchar htv0 htv1 _hfrac hne hmin
    hquant
  have hPi : IsProbabilityMeasure P := hPp
  have hQi : IsProbabilityMeasure Q := hQp
  set αs := StatFormal.Distances.tvDist P Q with hαs
  set f : ℝ → H := fun α => (Dpop Φ P Q α)⁻¹ • dstar α with hf
  have hfn : ∀ α ∈ Ico 0 αs, ‖f α‖ = 1 := fun α hα => by
    have hD := Dpop_pos P Q hΦ hκ hchar hα htv1
    rw [hf, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hD,
      ← StatFormal.Wave30tx.RBasic.Dpop_eq_norm (hmin α hα), inv_mul_cancel₀ hD.ne']
  -- weak convergence to `0`
  have hweak : ∀ h : H, Tendsto (fun α => ⟪f α, h⟫_ℝ) (𝓝[<] αs) (𝓝 0) := by
    intro h
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    have hI : ∀ᶠ j in atTop, ns j ∈ Ioo 0 αs := hns (Ioo_mem_nhdsLT htv0)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hI
    set c : ℕ → ℝ := fun j => ns (j + N) with hcdef
    have hc' : ∀ j, c j ∈ Ico 0 αs := fun j => ⟨(hN (j + N) (by omega)).1.le, (hN (j + N) (by omega)).2⟩
    have hclim : Tendsto c atTop (𝓝 αs) :=
      (tendsto_add_atTop_iff_nat N).2 (tendsto_nhds_of_tendsto_nhdsWithin hns)
    obtain ⟨ψ, ū, hψ, hwk⟩ := weak_subseq (fun j => f (c j)) (fun j => (hfn _ (hc' j)).le)
    have hū : ū = 0 := weak_limit_zero hc hd hG hpc hqc hp0 hq0 P Q rfl rfl hΦ hκ hchar htv0 htv1 hne hmin
      (al := fun j => c (ψ j)) (fun j => hc' _) (hclim.comp hψ.tendsto_atTop) hwk
    refine ⟨fun j => ψ j + N, ?_⟩
    have := hwk h
    rw [hū, inner_zero_left] at this
    exact this
  -- pointwise convergence and convergence in probability
  have hFm : ∀ α, Measurable (StatFormal.Wave12c.witFn (f α) Φ) := fun α =>
    StatFormal.Wave12c.measurable_witFn hΦ (f α)
  have hpt : ∀ x, Tendsto (fun α => StatFormal.Wave12c.witFn (f α) Φ x) (𝓝[<] αs) (𝓝 0) := fun x =>
    hweak (Φ x)
  have hprob := fun η (hη : (0 : ℝ) < η) => prob_tendsto P hFm hpt hη
  have hs : Tendsto s (𝓝[<] αs) (𝓝 0) :=
    quantile_tendsto_zero P htv0 htv1 hFm hprob fun α hα => hquant α hα
  have hcent : ∀ η : ℝ, 0 < η →
      Tendsto (fun α => P {x | η ≤ |StatFormal.Wave12c.witFn (f α) Φ x - s α|}) (𝓝[<] αs) (𝓝 0) := by
    intro η hη
    have hev : ∀ᶠ α in 𝓝[<] αs, |s α| < η / 2 := by
      have := Metric.tendsto_nhds.1 hs (η / 2) (by positivity)
      filter_upwards [this] with α hα
      rwa [Real.dist_eq, sub_zero] at hα
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hprob (η / 2) (by positivity))
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hev] with α hα
    refine measure_mono fun x hx => ?_
    simp only [mem_setOf_eq] at hx ⊢
    have := abs_sub (StatFormal.Wave12c.witFn (f α) Φ x) (s α)
    linarith
  exact ⟨hfn, hweak, fun η hη => hprob η hη, hs, fun ρ hρ =>
    ⟨dens_lower_tendsto P hFm hcent hρ, dens_upper_tendsto P hFm hcent hρ⟩⟩

end Final

end StatFormal.Wave30tx.RNearB
