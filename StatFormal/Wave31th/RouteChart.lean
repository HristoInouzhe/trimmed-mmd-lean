import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.WithDensity

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Wave 31th, route: the local chart of a level set (untrusted proof file)

Setting: `f : (ι → ℝ) → ℝ` of class `C¹`, a coordinate `i` with `∂_i f(x₀) ≠ 0`. The map `Φ(x) = update x i (f x)` (replace the
`i`-th coordinate by `f x`) has derivative the identity with row `i` replaced by `∇f`, so `det Φ'(x) = ∂_i f(x)` (`det_Φ'`), and is a
`C¹` diffeomorphism near `x₀` (inverse function theorem, `exists_chart`); in these coordinates `f` is the `i`-th coordinate.

`chart_bounds`: if `m |∂_i f| ≤ p ≤ M |∂_i f|` near `x₀`, then for a small chart region `R ∋ x₀` (the preimage under `Φ` of a small
sup-norm box of half-width `ε` around `Φ x₀`) and every Borel `A`,
`m B λ(A ∩ (t−ε,t+ε)) ≤ P(f⁻¹A ∩ R) ≤ M B λ(A ∩ (t−ε,t+ε))`, `P = p·λ`, `t = f x₀`, `B = (2ε)^{|ι|−1}`. Proof: change of variables
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul` with `g = 1`: `λ(Φ '' s) = ∫_s |∂_i f|`), then the box `Φ '' (f⁻¹A ∩ R) = box ∩ {y_i ∈ A}`
has volume `B λ(A ∩ (t−ε,t+ε))`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Function
open scoped ENNReal NNReal

namespace StatFormal.Wave31th.Chart

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The straightening map: replace the `i`-th coordinate by `f x`. -/
def Φ (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ι → ℝ := Function.update x i (f x)

/-- Its derivative: the identity with the row `i` replaced by `f'(x)`. -/
def Φ' (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun j => if j = i then fderiv ℝ f x else ContinuousLinearMap.proj j

lemma Φ_self (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : Φ f i x i = f x := by simp [Φ]

lemma Φ_ne (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) {j : ι} (hj : j ≠ i) : Φ f i x j = x j := by
  simp [Φ, hj]

lemma hasFDerivAt_Φ (f : (ι → ℝ) → ℝ) (i : ι) {x : ι → ℝ} (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (Φ f i) (Φ' f i x) x := by
  rw [hasFDerivAt_pi']
  intro j
  by_cases hj : j = i
  · subst hj
    have e : (fun y => Φ f j y j) = f := funext fun y => Φ_self f j y
    have e2 : (ContinuousLinearMap.proj j).comp (Φ' f j x) = fderiv ℝ f x := by
      simp [Φ']
    rw [e, e2]
    exact hf.hasFDerivAt
  · have e : (fun y => Φ f i y j) = fun y => y j := funext fun y => Φ_ne f i y hj
    have e2 : (ContinuousLinearMap.proj j).comp (Φ' f i x) = ContinuousLinearMap.proj j := by
      simp [Φ', hj]
    rw [e, e2]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j).hasFDerivAt

lemma det_Φ' (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) :
    (Φ' f i x).det = fderiv ℝ f x (Pi.single i 1) := by
  have h1 : (Φ' f i x).det = (LinearMap.toMatrix' (Φ' f i x : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))).det :=
    (LinearMap.det_toMatrix' _).symm
  rw [h1]
  have h2 : LinearMap.toMatrix' (Φ' f i x : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) =
      Matrix.updateRow (1 : Matrix ι ι ℝ) i (fun k => fderiv ℝ f x (Pi.single k 1)) := by
    ext j k
    rw [LinearMap.toMatrix'_apply]
    by_cases hj : j = i
    · subst hj
      simp [Φ', Matrix.updateRow_self, Pi.single_apply]
    · simp [Φ', hj, Matrix.updateRow_ne hj, Matrix.one_apply, Pi.single_apply]
  rw [h2]
  have h3 : (fun k => fderiv ℝ f x (Pi.single k 1)) =
      ∑ k, (fderiv ℝ f x (Pi.single k 1)) • (1 : Matrix ι ι ℝ) k := by
    funext l
    simp [Finset.sum_apply, Matrix.one_apply]
  rw [h3, Matrix.det_updateRow_sum]
  simp

lemma contDiff_Φ {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (i : ι) : ContDiff ℝ 1 (Φ f i) := by
  rw [contDiff_pi]
  intro j
  by_cases hj : j = i
  · subst hj
    have e : (fun y => Φ f j y j) = f := funext fun y => Φ_self f j y
    rw [e]; exact hf
  · have e : (fun y => Φ f i y j) = fun y => y j := funext fun y => Φ_ne f i y hj
    rw [e]; exact contDiff_apply ℝ ℝ j

/-- The inverse function theorem for `Φ` at a point where `∂_i f ≠ 0`. -/
lemma exists_chart {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (i : ι) {x₀ : ι → ℝ}
    (hd : fderiv ℝ f x₀ (Pi.single i 1) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ), x₀ ∈ e.source ∧ (∀ x, e x = Φ f i x) := by
  have hdet : (Φ' f i x₀).det ≠ 0 := by rw [det_Φ']; exact hd
  have hHas : HasFDerivAt (Φ f i) (Φ' f i x₀) x₀ :=
    hasFDerivAt_Φ f i ((hf.differentiable one_ne_zero) x₀)
  have hs : HasStrictFDerivAt (Φ f i) (Φ' f i x₀) x₀ :=
    (contDiff_Φ hf i).contDiffAt.hasStrictFDerivAt' hHas one_ne_zero
  let B := (Φ' f i x₀).toContinuousLinearEquivOfDetNeZero hdet
  have hs' : HasStrictFDerivAt (Φ f i) (B : (ι → ℝ) →L[ℝ] (ι → ℝ)) x₀ := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]; exact hs
  exact ⟨hs'.toOpenPartialHomeomorph (Φ f i), hs'.mem_toOpenPartialHomeomorph_source, fun x => rfl⟩

/-- The volume of the box `ball y₀ ε ∩ {y | y i ∈ A}` in `ι → ℝ`. -/
lemma volume_box (i : ι) (y₀ : ι → ℝ) {ε : ℝ} (hε : 0 < ε) (A : Set ℝ) :
    volume (Metric.ball y₀ ε ∩ {y : ι → ℝ | y i ∈ A}) =
      (∏ j ∈ Finset.univ.erase i, ENNReal.ofReal (2 * ε)) * volume (A ∩ Ioo (y₀ i - ε) (y₀ i + ε)) := by
  set S : ι → Set ℝ := fun j => if j = i then A ∩ Ioo (y₀ j - ε) (y₀ j + ε) else Ioo (y₀ j - ε) (y₀ j + ε) with hS
  have e1 : Metric.ball y₀ ε ∩ {y : ι → ℝ | y i ∈ A} = Set.pi univ S := by
    ext y
    rw [Set.mem_pi, mem_inter_iff, Metric.mem_ball, dist_pi_lt_iff hε]
    simp only [mem_univ, true_implies, Real.dist_eq, abs_lt, mem_ofPred_eq, hS]
    constructor
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj
        simp only [ite_true, mem_inter_iff, mem_Ioo]
        exact ⟨h2, by linarith [(h1 j).1], by linarith [(h1 j).2]⟩
      · simp only [hj, ite_false, mem_Ioo]
        exact ⟨by linarith [(h1 j).1], by linarith [(h1 j).2]⟩
    · intro h
      refine ⟨fun j => ?_, ?_⟩
      · have hj' := h j
        by_cases hj : j = i
        · subst hj
          simp only [ite_true, mem_inter_iff, mem_Ioo] at hj'
          exact ⟨by linarith [hj'.2.1], by linarith [hj'.2.2]⟩
        · simp only [hj, ite_false, mem_Ioo] at hj'
          exact ⟨by linarith [hj'.1], by linarith [hj'.2]⟩
      · have hi' := h i
        simp only [ite_true, mem_inter_iff] at hi'
        exact hi'.1
  have e2 := Finset.mul_prod_erase Finset.univ (fun j => volume (S j)) (Finset.mem_univ i)
  rw [e1, volume_pi_pi, ← e2, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp only [hS, hji, ite_false, Real.volume_Ioo]
    congr 1
    ring
  · simp only [hS, ite_true]

/-- The local chart estimate. -/
theorem chart_bounds {f p : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (i : ι) {x₀ : ι → ℝ}
    (hd : fderiv ℝ f x₀ (Pi.single i 1) ≠ 0)
    {N : Set (ι → ℝ)} (hN : N ∈ 𝓝 x₀) {m M : ℝ} (hm : 0 ≤ m) (hM : 0 ≤ M)
    (hbd : ∀ x ∈ N, m * |fderiv ℝ f x (Pi.single i 1)| ≤ p x ∧ p x ≤ M * |fderiv ℝ f x (Pi.single i 1)|) :
    ∃ (R : Set (ι → ℝ)) (ε : ℝ) (B : ℝ≥0∞), IsOpen R ∧ x₀ ∈ R ∧ R ⊆ N ∧ 0 < ε ∧ 0 < B ∧ B ≠ ∞ ∧
      ∀ A : Set ℝ, MeasurableSet A →
        ENNReal.ofReal m * B * volume (A ∩ Ioo (f x₀ - ε) (f x₀ + ε)) ≤
            (volume.withDensity fun x => ENNReal.ofReal (p x)) (f ⁻¹' A ∩ R) ∧
        (volume.withDensity fun x => ENNReal.ofReal (p x)) (f ⁻¹' A ∩ R) ≤
            ENNReal.ofReal M * B * volume (A ∩ Ioo (f x₀ - ε) (f x₀ + ε)) := by
  obtain ⟨e, hx₀e, he⟩ := exists_chart hf i hd
  have heΦ : (⇑e : (ι → ℝ) → (ι → ℝ)) = Φ f i := funext he
  set V := e.source ∩ interior N with hV
  have hVo : IsOpen V := e.open_source.inter isOpen_interior
  have hx₀V : x₀ ∈ V := ⟨hx₀e, mem_interior_iff_mem_nhds.2 hN⟩
  have hVs : V ⊆ e.source := inter_subset_left
  have hVN : V ⊆ N := fun x hx => interior_subset hx.2
  have himg : IsOpen (Φ f i '' V) := by
    have := e.isOpen_image_of_subset_source hVo hVs
    rwa [heΦ] at this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 himg (Φ f i x₀) ⟨x₀, hx₀V, rfl⟩
  have hΦc : Continuous (Φ f i) := (contDiff_Φ hf i).continuous
  set R := V ∩ Φ f i ⁻¹' Metric.ball (Φ f i x₀) ε with hR
  have hRo : IsOpen R := hVo.inter (Metric.isOpen_ball.preimage hΦc)
  have hx₀R : x₀ ∈ R := ⟨hx₀V, Metric.mem_ball_self hε⟩
  have hRV : R ⊆ V := inter_subset_left
  set B : ℝ≥0∞ := ∏ j ∈ Finset.univ.erase i, ENNReal.ofReal (2 * ε) with hB
  have hBpos : 0 < B := pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun j _ =>
    (ENNReal.ofReal_pos.2 (by positivity)).ne')
  have hBtop : B ≠ ∞ := (ENNReal.prod_lt_top fun j _ => ENNReal.ofReal_lt_top).ne
  refine ⟨R, ε, B, hRo, hx₀R, hRV.trans hVN, hε, hBpos, hBtop, fun A hA => ?_⟩
  set s := f ⁻¹' A ∩ R with hs
  have hsm : MeasurableSet s := (hf.continuous.measurable hA).inter hRo.measurableSet
  have hsV : s ⊆ V := fun x hx => hRV hx.2
  have hinj : InjOn (Φ f i) s := by
    have := e.injOn.mono (hsV.trans hVs)
    rwa [heΦ] at this
  have hder : ∀ x ∈ s, HasFDerivWithinAt (Φ f i) (Φ' f i x) s x := fun x _ =>
    (hasFDerivAt_Φ f i ((hf.differentiable one_ne_zero) x)).hasFDerivWithinAt
  have himS : Φ f i '' s = Metric.ball (Φ f i x₀) ε ∩ {y | y i ∈ A} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxA, hxR⟩, rfl⟩
      refine ⟨hxR.2, ?_⟩
      show Φ f i x i ∈ A
      rw [Φ_self]; exact hxA
    · rintro ⟨hyb, hyA⟩
      obtain ⟨x, hxV, rfl⟩ := hball hyb
      refine ⟨x, ⟨?_, hxV, hyb⟩, rfl⟩
      have : Φ f i x i ∈ A := hyA
      rw [Φ_self] at this
      exact this
  have hjac := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hsm hder hinj (fun _ => 1)
  have hdet : ∀ x, |(Φ' f i x).det| = |fderiv ℝ f x (Pi.single i 1)| := fun x => by rw [det_Φ']
  have hvol : volume (Φ f i '' s) = ∫⁻ x in s, ENNReal.ofReal |fderiv ℝ f x (Pi.single i 1)| := by
    have h1 : ∫⁻ y in Φ f i '' s, (1 : ℝ≥0∞) = volume (Φ f i '' s) := by simp
    rw [← h1, hjac]
    simp [hdet]
  have hbox : volume (Φ f i '' s) = B * volume (A ∩ Ioo (f x₀ - ε) (f x₀ + ε)) := by
    rw [himS, volume_box i _ hε A, Φ_self]
  have hPs : (volume.withDensity fun x => ENNReal.ofReal (p x)) s = ∫⁻ x in s, ENNReal.ofReal (p x) :=
    withDensity_apply _ hsm
  constructor
  · calc ENNReal.ofReal m * B * volume (A ∩ Ioo (f x₀ - ε) (f x₀ + ε))
        = ENNReal.ofReal m * volume (Φ f i '' s) := by rw [hbox, mul_assoc]
      _ = ∫⁻ x in s, ENNReal.ofReal m * ENNReal.ofReal |fderiv ℝ f x (Pi.single i 1)| := by
          rw [hvol, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ∫⁻ x in s, ENNReal.ofReal (p x) := by
          refine setLIntegral_mono' hsm fun x hx => ?_
          rw [← ENNReal.ofReal_mul hm]
          exact ENNReal.ofReal_le_ofReal (hbd x (hVN (hsV hx))).1
      _ = _ := hPs.symm
  · calc (volume.withDensity fun x => ENNReal.ofReal (p x)) s = ∫⁻ x in s, ENNReal.ofReal (p x) := hPs
      _ ≤ ∫⁻ x in s, ENNReal.ofReal M * ENNReal.ofReal |fderiv ℝ f x (Pi.single i 1)| := by
          refine setLIntegral_mono' hsm fun x hx => ?_
          rw [← ENNReal.ofReal_mul hM]
          exact ENNReal.ofReal_le_ofReal (hbd x (hVN (hsV hx))).2
      _ = ENNReal.ofReal M * volume (Φ f i '' s) := by
          rw [hvol, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal M * B * volume (A ∩ Ioo (f x₀ - ε) (f x₀ + ε)) := by rw [hbox, mul_assoc]

end StatFormal.Wave31th.Chart
