import StatFormal.Archive.Wave29d.Statements
import StatFormal.Lib.Lindsay.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Topology.Order.Compact

/-!
# `lem:lindsay`, general mixing space (`lindsay_gen_sandwich`, `lindsay_gen_maximiser`, `lindsay_gen_dirac`)

Untrusted proof file.
1. `ψ_i` is measurable (integral against a kernel) with `0 < ψ_i ≤ e^B`, so `A_i(m) = ∫ ψ_i dm > 0` for every
   probability `m`; Fubini for `m ⊗ₘ κ` gives `∫ e^{φ_i} d(m.bind κ) = A_i(m)`, so `Λ = sup_{m ∈ 𝓜} L(m)`.
2. `∫ D_{m̂} dm = n⁻¹ Σ_i A_i(m)/A_i(m̂)` (linearity) and Jensen for `log` give `L(m) ≤ L(m̂) + log ∫ D_{m̂} dm`.
3. At a maximiser over a convex `𝓜`, along `t m + (1 − t) m̂` the first-order condition
   (`StatFormal.Foundations.Lindsay.foc_of_log_le`) gives `∫ D_{m̂} dm ≤ 1`, with equality at `m̂`.
4. `𝓜 = 𝒫(L)`: `ψ_i` is continuous by the Feller condition, `D_{m̂}` attains its maximum at `y` on the compact `L`,
   `∫ D_{m̂} dm ≤ D_{m̂}(y)`, with equality at `δ_y`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave29d

namespace LindsayGen

open StatFormal.Foundations.Lindsay (log_avg_le foc_of_log_le)

variable {K L : Type*} [MeasurableSpace K] [MeasurableSpace L] {n : ℕ}
  {κ : Kernel L K} {φ : Fin n → K → ℝ}

lemma isFiniteKernel (hS : MixSettingK κ φ) : IsFiniteKernel κ :=
  ⟨⟨1, ENNReal.one_lt_top, fun y => (hS.2.1 y).2⟩⟩

lemma exp_measurable (hS : MixSettingK κ φ) (i : Fin n) : Measurable fun x => Real.exp (φ i x) :=
  (hS.2.2.1 i).exp

lemma exp_integrable (hS : MixSettingK κ φ) (i : Fin n) (y : L) :
    Integrable (fun x => Real.exp (φ i x)) (κ y) := by
  have := isFiniteKernel hS
  obtain ⟨B, hB⟩ := hS.2.2.2
  refine Integrable.of_bound (exp_measurable hS i).aestronglyMeasurable (Real.exp B)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (abs_le.1 (hB i x)).2

lemma psi_measurable (hS : MixSettingK κ φ) (i : Fin n) : Measurable (psiK κ φ i) :=
  (StronglyMeasurable.integral_kernel (κ := κ) (exp_measurable hS i).stronglyMeasurable).measurable

lemma psi_pos (hS : MixSettingK κ φ) (i : Fin n) (y : L) : 0 < psiK κ φ i y := by
  unfold psiK
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) (exp_integrable hS i y)]
  have : Function.support (fun x => Real.exp (φ i x)) = univ :=
    eq_univ_of_forall fun x => (Real.exp_pos _).ne'
  rw [this]
  exact (hS.2.1 y).1

lemma psi_le (hS : MixSettingK κ φ) : ∃ C, 0 < C ∧ ∀ i y, psiK κ φ i y ≤ C := by
  have := isFiniteKernel hS
  obtain ⟨B, hB⟩ := hS.2.2.2
  refine ⟨Real.exp B, Real.exp_pos _, fun i y => ?_⟩
  unfold psiK
  calc ∫ x, Real.exp (φ i x) ∂(κ y) ≤ ∫ _x, Real.exp B ∂(κ y) :=
        integral_mono (exp_integrable hS i y) (integrable_const _)
          (fun x => Real.exp_le_exp.2 (abs_le.1 (hB i x)).2)
    _ = (κ y).real univ * Real.exp B := by rw [integral_const, smul_eq_mul]
    _ ≤ 1 * Real.exp B := by
        gcongr
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (hS.2.1 y).2)
    _ = Real.exp B := one_mul _

lemma psi_integrable (hS : MixSettingK κ φ) (i : Fin n) {m : Measure L} [IsFiniteMeasure m] :
    Integrable (psiK κ φ i) m := by
  obtain ⟨C, -, hC⟩ := psi_le hS
  refine Integrable.of_bound (psi_measurable hS i).aestronglyMeasurable C
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (psi_pos hS i y)]
  exact hC i y

lemma A_pos (hS : MixSettingK κ φ) (i : Fin n) {m : Measure L} [IsProbabilityMeasure m] :
    0 < ∫ y, psiK κ φ i y ∂m := by
  rw [integral_pos_iff_support_of_nonneg (fun y => (psi_pos hS i y).le) (psi_integrable hS i)]
  have : Function.support (psiK κ φ i) = univ := eq_univ_of_forall fun y => (psi_pos hS i y).ne'
  rw [this, measure_univ]
  exact zero_lt_one

lemma A_le (hS : MixSettingK κ φ) {C : ℝ} (hC : ∀ i y, psiK κ φ i y ≤ C) (i : Fin n)
    {m : Measure L} [IsProbabilityMeasure m] : ∫ y, psiK κ φ i y ∂m ≤ C := by
  calc ∫ y, psiK κ φ i y ∂m ≤ ∫ _y, C ∂m :=
        integral_mono (psi_integrable hS i) (integrable_const _) (fun y => hC i y)
    _ = C := by simp

/-- Fubini for the bind: `∫ e^{φ_i} d(m.bind κ) = ∫ ψ_i dm`. -/
lemma integral_bind_eq (hS : MixSettingK κ φ) (i : Fin n) {m : Measure L} [IsProbabilityMeasure m] :
    ∫ x, Real.exp (φ i x) ∂(m.bind κ) = ∫ y, psiK κ φ i y ∂m := by
  have := isFiniteKernel hS
  obtain ⟨B, hB⟩ := hS.2.2.2
  have hf := exp_measurable hS i
  rw [← Measure.snd_compProd, Measure.snd,
    integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]
  rw [Measure.integral_compProd (f := fun p : L × K => Real.exp (φ i p.2))]
  · rfl
  · refine Integrable.of_bound (hf.comp measurable_snd).aestronglyMeasurable (Real.exp B)
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (abs_le.1 (hB i p.2)).2

lemma lambdaK_eq (hS : MixSettingK κ φ) {M : Set (Measure L)} (hM : ∀ m ∈ M, IsProbabilityMeasure m) :
    lambdaK κ φ M = sSup {v | ∃ m ∈ M, v = npmleK κ φ m} := by
  unfold lambdaK
  congr 1
  ext v
  constructor
  · rintro ⟨m, hm, rfl⟩
    have := hM m hm
    exact ⟨m, hm, by simp only [npmleK, integral_bind_eq hS]⟩
  · rintro ⟨m, hm, rfl⟩
    have := hM m hm
    exact ⟨m, hm, by simp only [npmleK, integral_bind_eq hS]⟩

lemma npmle_bdd (hS : MixSettingK κ φ) {M : Set (Measure L)} (hM : ∀ m ∈ M, IsProbabilityMeasure m) :
    BddAbove {v | ∃ m ∈ M, v = npmleK κ φ m} := by
  obtain ⟨C, -, hC⟩ := psi_le hS
  refine ⟨(1 / n : ℝ) * ∑ _i : Fin n, C, ?_⟩
  rintro v ⟨m, hm, rfl⟩
  have := hM m hm
  unfold npmleK
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
  have h1 := Real.log_le_sub_one_of_pos (A_pos hS i (m := m))
  have h2 := A_le hS hC i (m := m)
  linarith

lemma D_integrable (hS : MixSettingK κ φ) (mh : Measure L) {m : Measure L} [IsFiniteMeasure m] :
    Integrable (lindsayDK κ φ mh) m := by
  unfold lindsayDK
  exact (integrable_finset_sum _ fun i _ => (psi_integrable hS i).div_const _).const_mul _

/-- `∫ D_{m̂} dm = n⁻¹ Σ_i A_i(m)/A_i(m̂)`. -/
lemma integral_D (hS : MixSettingK κ φ) (mh : Measure L) {m : Measure L} [IsFiniteMeasure m] :
    ∫ y, lindsayDK κ φ mh y ∂m =
      (1 / n : ℝ) * ∑ i, (∫ y, psiK κ φ i y ∂m) / ∫ y', psiK κ φ i y' ∂mh := by
  unfold lindsayDK
  rw [integral_const_mul, integral_finset_sum _ fun i _ => (psi_integrable hS i).div_const _]
  simp_rw [integral_div]

lemma D_bdd (hS : MixSettingK κ φ) {M : Set (Measure L)} (hM : ∀ m ∈ M, IsProbabilityMeasure m)
    (mh : Measure L) [IsProbabilityMeasure mh] :
    BddAbove {v | ∃ m ∈ M, v = ∫ y, lindsayDK κ φ mh y ∂m} := by
  obtain ⟨C, -, hC⟩ := psi_le hS
  refine ⟨(1 / n : ℝ) * ∑ i, C / ∫ y', psiK κ φ i y' ∂mh, ?_⟩
  rintro v ⟨m, hm, rfl⟩
  have := hM m hm
  rw [integral_D hS mh]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
  exact div_le_div_of_nonneg_right (A_le hS hC i) (A_pos hS i).le

lemma integral_D_pos (hS : MixSettingK κ φ) (mh : Measure L) [IsProbabilityMeasure mh]
    {m : Measure L} [IsProbabilityMeasure m] : 0 < ∫ y, lindsayDK κ φ mh y ∂m := by
  rw [integral_D hS mh]
  have hn : (0 : ℝ) < n := by exact_mod_cast hS.1
  have : 0 < ∑ i, (∫ y, psiK κ φ i y ∂m) / ∫ y', psiK κ φ i y' ∂mh :=
    Finset.sum_pos (fun i _ => div_pos (A_pos hS i) (A_pos hS i)) ⟨⟨0, hS.1⟩, Finset.mem_univ _⟩
  positivity

lemma npmle_sub_le (hS : MixSettingK κ φ) (mh : Measure L) [IsProbabilityMeasure mh]
    (m : Measure L) [IsProbabilityMeasure m] :
    npmleK κ φ m ≤ npmleK κ φ mh + Real.log (∫ y, lindsayDK κ φ mh y ∂m) := by
  have h := log_avg_le hS.1
    (fun i => (∫ y, psiK κ φ i y ∂m) / ∫ y', psiK κ φ i y' ∂mh)
    (fun i => div_pos (A_pos hS i) (A_pos hS i))
  rw [integral_D hS mh]
  simp_rw [Real.log_div (A_pos hS _ (m := m)).ne' (A_pos hS _ (m := mh)).ne'] at h
  unfold npmleK
  rw [Finset.sum_sub_distrib, mul_sub] at h
  linarith

lemma integral_D_self (hS : MixSettingK κ φ) (mh : Measure L) [IsProbabilityMeasure mh] :
    ∫ y, lindsayDK κ φ mh y ∂mh = 1 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hS.1.ne'
  rw [integral_D hS mh]
  simp_rw [div_self (A_pos hS _ (m := mh)).ne']
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

/-- Lindsay's first-order condition at a maximiser over a convex `𝓜`. -/
lemma foc (hS : MixSettingK κ φ) {M : Set (Measure L)} (hM : ∀ m ∈ M, IsProbabilityMeasure m)
    (hconv : MeasConvex M) {mh : Measure L} (hmh : mh ∈ M)
    (hmax : ∀ m ∈ M, npmleK κ φ m ≤ npmleK κ φ mh) {m : Measure L} (hm : m ∈ M) :
    ∫ y, lindsayDK κ φ mh y ∂m ≤ 1 := by
  have := hM mh hmh
  have := hM m hm
  have hn : (0 : ℝ) < n := by exact_mod_cast hS.1
  have hseg : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∑ i, Real.log ((1 - t) * (∫ y, psiK κ φ i y ∂mh) + t * ∫ y, psiK κ φ i y ∂m) ≤
        ∑ i, Real.log (∫ y, psiK κ φ i y ∂mh) := by
    intro t ht0 ht1
    have hmt := hconv m hm mh hmh t ht0.le ht1
    have hA : ∀ i, ∫ y, psiK κ φ i y ∂(ENNReal.ofReal t • m + ENNReal.ofReal (1 - t) • mh) =
        (1 - t) * (∫ y, psiK κ φ i y ∂mh) + t * ∫ y, psiK κ φ i y ∂m := by
      intro i
      rw [integral_add_measure ((psi_integrable hS i).smul_measure ENNReal.ofReal_ne_top)
          ((psi_integrable hS i).smul_measure ENNReal.ofReal_ne_top),
        integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal ht0.le,
        ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]
      ring
    have h := hmax _ hmt
    unfold npmleK at h
    simp_rw [hA] at h
    exact le_of_mul_le_mul_left h (by positivity)
  have h := foc_of_log_le (fun i => ∫ y, psiK κ φ i y ∂m) (fun i => ∫ y, psiK κ φ i y ∂mh)
    (fun i => A_pos hS i) (fun i => A_pos hS i) hseg
  rw [integral_D hS mh]
  calc (1 / n : ℝ) * ∑ i, (∫ y, psiK κ φ i y ∂m) / ∫ y', psiK κ φ i y' ∂mh ≤ (1 / n : ℝ) * n :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 := by field_simp

end LindsayGen

open LindsayGen

theorem lindsay_gen_sandwich : Claims.lindsay_gen_sandwich := by
  intro K L _ _ n κ φ M mh hS hM hmh
  have := hM mh hmh
  rw [lambdaK_eq hS hM]
  refine ⟨le_csSup (npmle_bdd hS hM) ⟨mh, hmh, rfl⟩, csSup_le ⟨_, mh, hmh, rfl⟩ ?_⟩
  rintro v ⟨m, hm, rfl⟩
  have := hM m hm
  refine (npmle_sub_le hS mh m).trans ((add_le_add_iff_left _).2 ?_)
  exact Real.log_le_log (integral_D_pos hS mh) (le_csSup (D_bdd hS hM mh) ⟨m, hm, rfl⟩)

theorem lindsay_gen_maximiser : Claims.lindsay_gen_maximiser := by
  intro K L _ _ n κ φ M mh hS hM hconv hmh hmax
  have := hM mh hmh
  have hsup : lindsaySupK κ φ M mh = 1 := by
    apply le_antisymm
    · exact csSup_le ⟨_, mh, hmh, rfl⟩ (by
        rintro v ⟨m, hm, rfl⟩; exact foc hS hM hconv hmh hmax hm)
    · rw [← integral_D_self hS mh]
      exact le_csSup (D_bdd hS hM mh) ⟨mh, hmh, rfl⟩
  refine ⟨?_, hsup⟩
  have h := lindsay_gen_sandwich K L n κ φ M mh hS hM hmh
  rw [hsup, Real.log_one, add_zero] at h
  exact le_antisymm h.2 h.1

theorem lindsay_gen_dirac : Claims.lindsay_gen_dirac := by
  intro K L _ _ _ _ _ _ _ _ _ n κ φ mh hS hφc hF hmh
  have hpsic : ∀ i, Continuous (psiK κ φ i) := fun i => hF _ (Real.continuous_exp.comp (hφc i))
  have hDc : Continuous (lindsayDK κ φ mh) := by
    unfold lindsayDK
    exact continuous_const.mul (continuous_finsetSum _ fun i _ => (hpsic i).div_const _)
  obtain ⟨y, -, hy⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hDc.continuousOn
  have hy' : ∀ y', lindsayDK κ φ mh y' ≤ lindsayDK κ φ mh y := fun y' =>
    isMaxOn_iff.1 hy y' (mem_univ _)
  refine ⟨y, ?_, hy'⟩
  apply IsGreatest.csSup_eq
  refine ⟨⟨Measure.dirac y, (show IsProbabilityMeasure (Measure.dirac y) from inferInstance), (integral_dirac _ _).symm⟩, ?_⟩
  rintro v ⟨m, hm, rfl⟩
  have : IsProbabilityMeasure m := hm
  calc ∫ y', lindsayDK κ φ mh y' ∂m ≤ ∫ _y', lindsayDK κ φ mh y ∂m :=
        integral_mono (D_integrable hS mh) (integrable_const _) hy'
    _ = lindsayDK κ φ mh y := by simp

end StatFormal.Wave29d
