import StatFormal.Wave31th.Statements
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option linter.style.longLine false

/-!
# Wave 31th, route: the Gaussian-RKHS facts `gaussian_regular` (untrusted proof file)

Route. Let `φ : ℝ^d → ℋ` have the Gaussian Gram function. Then `‖φ x − φ y‖² = 2 − 2exp(−‖x−y‖²/(2σ²)) ≤ ‖x − y‖²/σ²`, so `φ` is
`1/σ`-Lipschitz and `F_f = ⟨f, φ ·⟩` is `‖f‖/σ`-Lipschitz for every `f ∈ ℋ`. Let `Z₁ = {f | F_f is C¹}` and `Z₂ = {f | F_f → 0 at infinity}`.
Both are closed submodules of `ℋ` (a limit of `f_n ∈ Z₁` has `F_{f_n} → F_f` uniformly and the derivatives are uniformly Cauchy, since
`F_{f_n} − F_{f_m} = F_{f_n − f_m}` is `‖f_n − f_m‖/σ`-Lipschitz; then `hasFDerivAt_of_tendstoUniformly`), both contain every `φ y`
(`F_{φ y}(x) = exp(−‖y−x‖²/(2σ²))`) and every `f` orthogonal to the span of the `φ y` (`F_f = 0`); the span and its orthogonal complement
generate a dense subspace of the complete space `ℋ`, so `Z₁ = Z₂ = ℋ`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31th

open StatFormal.Wave12c

section Gauss

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Gaussian Gram function. -/
def GaussGram (φ : EuclideanSpace ℝ (Fin d) → H) (σ : ℝ) : Prop :=
  ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))

lemma norm_phi_sq_sub {φ : EuclideanSpace ℝ (Fin d) → H} {σ : ℝ} (hg : GaussGram φ σ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖φ x - φ y‖ ^ 2 = 2 - 2 * Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2)) := by
  have hxx := hg x x
  have hyy := hg y y
  have hxy := hg x y
  have hyx := hg y x
  rw [norm_sub_rev y x] at hyx
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right, hxx, hyy, hxy, hyx]
  simp
  ring

lemma phi_lipschitz {φ : EuclideanSpace ℝ (Fin d) → H} {σ : ℝ} (hσ : 0 < σ) (hg : GaussGram φ σ)
    (x y : EuclideanSpace ℝ (Fin d)) : ‖φ x - φ y‖ ≤ ‖x - y‖ / σ := by
  have h1 := norm_phi_sq_sub hg x y
  have h2 : 1 - ‖x - y‖ ^ 2 / (2 * σ ^ 2) ≤ Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2)) := by
    have := Real.add_one_le_exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))
    have e : -‖x - y‖ ^ 2 / (2 * σ ^ 2) = -(‖x - y‖ ^ 2 / (2 * σ ^ 2)) := by ring
    linarith
  have h3 : ‖φ x - φ y‖ ^ 2 ≤ (‖x - y‖ / σ) ^ 2 := by
    rw [h1, div_pow]
    have : ‖x - y‖ ^ 2 / (2 * σ ^ 2) * 2 = ‖x - y‖ ^ 2 / σ ^ 2 := by field_simp
    linarith
  exact le_of_sq_le_sq h3 (by positivity)

lemma norm_phi {φ : EuclideanSpace ℝ (Fin d) → H} {σ : ℝ} (hg : GaussGram φ σ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖φ x‖ = 1 := by
  have h := hg x x
  rw [real_inner_self_eq_norm_sq] at h
  simp at h
  have h0 : 0 ≤ ‖φ x‖ := norm_nonneg _
  rcases h with h | h
  · exact h
  · linarith

/-- `x ↦ ⟨f, φ x⟩` is `‖f‖/σ`-Lipschitz. -/
lemma witFn_lip {φ : EuclideanSpace ℝ (Fin d) → H} {σ : ℝ} (hσ : 0 < σ) (hg : GaussGram φ σ) (f : H)
    (x y : EuclideanSpace ℝ (Fin d)) : |witFn f φ x - witFn f φ y| ≤ ‖f‖ / σ * ‖x - y‖ := by
  have h1 : witFn f φ x - witFn f φ y = ⟪f, φ x - φ y⟫_ℝ := by
    simp [witFn, inner_sub_right]
  rw [h1]
  calc |⟪f, φ x - φ y⟫_ℝ| ≤ ‖f‖ * ‖φ x - φ y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖f‖ * (‖x - y‖ / σ) := by gcongr; exact phi_lipschitz hσ hg x y
    _ = ‖f‖ / σ * ‖x - y‖ := by ring

/-- The derivative of a `C¹` function `x ↦ ⟨f, φ x⟩` has norm at most `‖f‖/σ`. -/
lemma norm_fderiv_witFn_le {φ : EuclideanSpace ℝ (Fin d) → H} {σ : ℝ} (hσ : 0 < σ) (hg : GaussGram φ σ) (f : H)
    (x : EuclideanSpace ℝ (Fin d)) : ‖fderiv ℝ (witFn f φ) x‖ ≤ ‖f‖ / σ := by
  have hK : 0 ≤ ‖f‖ / σ := by positivity
  have hlip : LipschitzWith (‖f‖ / σ).toNNReal (witFn f φ) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.coe_toNNReal _ hK]
    simpa [Real.dist_eq, dist_eq_norm] using witFn_lip hσ hg f a b
  have := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := x)
  rwa [Real.coe_toNNReal _ hK] at this

lemma witFn_add (f g : H) (φ : EuclideanSpace ℝ (Fin d) → H) :
    witFn (f + g) φ = witFn f φ + witFn g φ := by
  funext x; simp [witFn, inner_add_left]

lemma witFn_sub (f g : H) (φ : EuclideanSpace ℝ (Fin d) → H) :
    witFn (f - g) φ = witFn f φ - witFn g φ := by
  funext x; simp [witFn, inner_sub_left]

lemma witFn_smul (c : ℝ) (f : H) (φ : EuclideanSpace ℝ (Fin d) → H) :
    witFn (c • f) φ = c • witFn f φ := by
  funext x; simp [witFn, inner_smul_left]

/-- A closed submodule containing the `φ y` and the orthogonal complement of their span is everything. -/
lemma eq_top_of_closed [CompleteSpace H] (S Z : Submodule ℝ H) (hZ : IsClosed (Z : Set H)) (hS : S ≤ Z)
    (hSo : Sᗮ ≤ Z) : Z = ⊤ := by
  have h1 : (S ⊔ Sᗮ)ᗮ = ⊥ := by
    rw [← Submodule.inf_orthogonal]
    exact Submodule.inf_orthogonal_eq_bot Sᗮ
  have h2 : (S ⊔ Sᗮ).topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.2 h1
  rw [eq_top_iff, ← h2]
  exact Submodule.topologicalClosure_minimal _ (sup_le hS hSo) hZ


section C1

variable [CompleteSpace H] {φ : EuclideanSpace ℝ (Fin d) → H} {σ : ℝ}

/-- The submodule of `f ∈ ℋ` with `x ↦ ⟨f, φ x⟩` of class `C¹`. -/
def C1Sub (φ : EuclideanSpace ℝ (Fin d) → H) : Submodule ℝ H where
  carrier := {f | ContDiff ℝ 1 (witFn f φ)}
  add_mem' := by
    intro f g hf hg
    simp only [mem_ofPred_eq] at *
    rw [witFn_add]; exact hf.add hg
  zero_mem' := by
    simp only [mem_ofPred_eq]
    have : witFn (0 : H) φ = fun _ => 0 := by funext x; simp [witFn]
    rw [this]; exact contDiff_const
  smul_mem' := by
    intro c f hf
    simp only [mem_ofPred_eq] at *
    rw [witFn_smul]; exact hf.const_smul c

omit [CompleteSpace H] in
lemma isClosed_C1Sub (hσ : 0 < σ) (hg : GaussGram φ σ) : IsClosed (C1Sub φ : Set H) := by
  refine IsSeqClosed.isClosed ?_
  intro u f hu hlim
  have hF : ∀ n, ContDiff ℝ 1 (witFn (u n) φ) := fun n => hu n
  set L : ℕ → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :=
    fun n x => fderiv ℝ (witFn (u n) φ) x with hL
  have hHas : ∀ n x, HasFDerivAt (witFn (u n) φ) (L n x) x := fun n x =>
    ((hF n).differentiable one_ne_zero x).hasFDerivAt
  have hcauchy : ∀ n m x, ‖L n x - L m x‖ ≤ ‖u n - u m‖ / σ := by
    intro n m x
    have e : witFn (u n - u m) φ = witFn (u n) φ - witFn (u m) φ := witFn_sub _ _ _
    have h1 : L n x - L m x = fderiv ℝ (witFn (u n - u m) φ) x := by
      rw [e, fderiv_sub (hHas n x).differentiableAt (hHas m x).differentiableAt]
    rw [h1]
    exact norm_fderiv_witFn_le hσ hg _ x
  have hucs : CauchySeq u := hlim.cauchySeq
  have hcs : ∀ x, CauchySeq (fun n => L n x) := by
    intro x
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hucs (ε * σ) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    rw [dist_eq_norm] at h1 ⊢
    calc ‖L m x - L n x‖ ≤ ‖u m - u n‖ / σ := hcauchy m n x
      _ < ε := by rw [div_lt_iff₀ hσ]; exact h1
  choose g' hg' using fun x => cauchySeq_tendsto_of_complete (hcs x)
  have hunif : TendstoUniformly L g' atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hucs (ε * σ / 2) (by positivity)
    filter_upwards [eventually_ge_atTop N] with n hn x
    have hle : ∀ᶠ m in atTop, ‖L n x - L m x‖ ≤ ε / 2 := by
      filter_upwards [eventually_ge_atTop N] with m hm
      have h1 := hN n hn m hm
      rw [dist_eq_norm] at h1
      calc ‖L n x - L m x‖ ≤ ‖u n - u m‖ / σ := hcauchy n m x
        _ ≤ ε / 2 := by rw [div_le_iff₀ hσ]; linarith
    have hlim2 : Tendsto (fun m => ‖L n x - L m x‖) atTop (𝓝 ‖L n x - g' x‖) :=
      (tendsto_const_nhds.sub (hg' x)).norm
    have := le_of_tendsto hlim2 hle
    rw [dist_comm, dist_eq_norm]
    linarith
  have hfg : ∀ x, Tendsto (fun n => witFn (u n) φ x) atTop (𝓝 (witFn f φ x)) := fun x =>
    Filter.Tendsto.inner hlim tendsto_const_nhds
  have hgc : Continuous g' :=
    hunif.continuous (Eventually.of_forall fun n => (hF n).continuous_fderiv one_ne_zero).frequently
  exact contDiff_one_iff_hasFDerivAt.2 ⟨g', hgc, fun x => hasFDerivAt_of_tendstoUniformly hunif hHas hfg x⟩

end C1

section Decay

variable {φ : EuclideanSpace ℝ (Fin d) → H} {σ : ℝ}

/-- The submodule of `f ∈ ℋ` with `⟨f, φ x⟩ → 0` as `‖x‖ → ∞`. -/
def DecaySub (φ : EuclideanSpace ℝ (Fin d) → H) : Submodule ℝ H where
  carrier := {f | Tendsto (witFn f φ) (comap (fun x => ‖x‖) atTop) (𝓝 0)}
  add_mem' := by
    intro f g hf hg
    simp only [mem_ofPred_eq] at *
    rw [witFn_add]
    have := hf.add hg
    rw [add_zero] at this
    exact this
  zero_mem' := by
    simp only [mem_ofPred_eq]
    have : witFn (0 : H) φ = fun _ => 0 := by funext x; simp [witFn]
    rw [this]; exact tendsto_const_nhds
  smul_mem' := by
    intro c f hf
    simp only [mem_ofPred_eq] at *
    rw [witFn_smul]
    have := hf.const_smul c
    rw [smul_zero] at this
    exact this

lemma isClosed_DecaySub (hg : GaussGram φ σ) : IsClosed (DecaySub φ : Set H) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  show Tendsto (witFn f φ) (comap (fun x => ‖x‖) atTop) (𝓝 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, hgZ, hfg⟩ := Metric.mem_closure_iff.1 hf (ε / 2) (by positivity)
  have hgt : Tendsto (witFn g φ) (comap (fun x => ‖x‖) atTop) (𝓝 0) := hgZ
  have hev := (Metric.tendsto_nhds.1 hgt) (ε / 2) (by positivity)
  filter_upwards [hev] with x hx
  have h1 : witFn f φ x = witFn (f - g) φ x + witFn g φ x := by
    simp [witFn, inner_sub_left]
  have h2 : |witFn (f - g) φ x| ≤ ‖f - g‖ := by
    have := abs_real_inner_le_norm (f - g) (φ x)
    rw [norm_phi hg x, mul_one] at this
    exact this
  rw [Real.dist_eq, sub_zero] at hx ⊢
  rw [dist_eq_norm] at hfg
  calc |witFn f φ x| = |witFn (f - g) φ x + witFn g φ x| := by rw [h1]
    _ ≤ |witFn (f - g) φ x| + |witFn g φ x| := abs_add_le _ _
    _ < ε := by linarith

lemma phi_mem_DecaySub (hσ : 0 < σ) (hg : GaussGram φ σ) (y : EuclideanSpace ℝ (Fin d)) :
    φ y ∈ DecaySub φ := by
  show Tendsto (witFn (φ y) φ) (comap (fun x => ‖x‖) atTop) (𝓝 0)
  have e : witFn (φ y) φ = fun x => Real.exp (-(‖y - x‖ ^ 2 / (2 * σ ^ 2))) := by
    funext x; simp only [witFn]; rw [hg y x, neg_div]
  rw [e]
  have h1 : Tendsto (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ - ‖y‖) (comap (fun x => ‖x‖) atTop) atTop :=
    tendsto_atTop_add_const_right _ (-‖y‖) (by simpa using (tendsto_comap : Tendsto (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖) (comap (fun x => ‖x‖) atTop) atTop))
  have h2 : Tendsto (fun x : EuclideanSpace ℝ (Fin d) => ‖y - x‖) (comap (fun x => ‖x‖) atTop) atTop := by
    refine tendsto_atTop_mono (fun x => ?_) h1
    have := norm_sub_norm_le x y
    rw [norm_sub_rev] at this
    exact this
  have h3 := ((tendsto_pow_atTop (two_ne_zero)).comp h2).atTop_div_const (show 0 < 2 * σ ^ 2 by positivity)
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h3)

end Decay

/-- `gaussian_regular` for a fixed feature map. -/
theorem gaussian_regular_of {φ : EuclideanSpace ℝ (Fin d) → H} {σ : ℝ} [CompleteSpace H] (hσ : 0 < σ)
    (hg : GaussGram φ σ) (f : H) :
    ContDiff ℝ 1 (witFn f φ) ∧ Tendsto (witFn f φ) (comap (fun x => ‖x‖) atTop) (𝓝 0) := by
  have hSo : ∀ g ∈ (Submodule.span ℝ (range φ))ᗮ, ∀ x, witFn g φ x = 0 := by
    intro g hg' x
    have := Submodule.mem_orthogonal _ _ |>.1 hg' (φ x) (Submodule.subset_span ⟨x, rfl⟩)
    simpa [witFn, real_inner_comm] using this
  have hrange : ∀ y, φ y ∈ Submodule.span ℝ (range φ) := fun y => Submodule.subset_span ⟨y, rfl⟩
  have hC1 : C1Sub φ = ⊤ := by
    refine eq_top_of_closed (Submodule.span ℝ (range φ)) _ (isClosed_C1Sub hσ hg) ?_ ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨y, rfl⟩
      show ContDiff ℝ 1 (witFn (φ y) φ)
      have e : witFn (φ y) φ = fun x => Real.exp (-(‖y - x‖ ^ 2 / (2 * σ ^ 2))) := by
        funext x; simp only [witFn]; rw [hg y x, neg_div]
      rw [e]
      refine Real.contDiff_exp.comp (contDiff_neg.comp ?_)
      exact ((contDiff_const.sub contDiff_id).norm_sq ℝ).div_const _
    · intro g hg'
      show ContDiff ℝ 1 (witFn g φ)
      have : witFn g φ = fun _ => 0 := funext (hSo g hg')
      rw [this]; exact contDiff_const
  have hDec : DecaySub φ = ⊤ := by
    refine eq_top_of_closed (Submodule.span ℝ (range φ)) _ (isClosed_DecaySub hg) ?_ ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨y, rfl⟩
      exact phi_mem_DecaySub hσ hg y
    · intro g hg'
      show Tendsto (witFn g φ) (comap (fun x => ‖x‖) atTop) (𝓝 0)
      have : witFn g φ = fun _ => 0 := funext (hSo g hg')
      rw [this]; exact tendsto_const_nhds
  have h1 : f ∈ C1Sub φ := by rw [hC1]; trivial
  have h2 : f ∈ DecaySub φ := by rw [hDec]; trivial
  exact ⟨h1, h2⟩

end Gauss

/-- `rem:qdens (v3, every d)`: the Gaussian-RKHS facts, `C¹` and decay. -/
theorem gaussian_regular : Claims.gaussian_regular := by
  intro d H _ _ _ φ σ hσ hg f
  exact gaussian_regular_of hσ hg f

end StatFormal.Wave31th
