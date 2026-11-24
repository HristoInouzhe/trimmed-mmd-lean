import StatFormal.Archive.Wave18b.Statements
import StatFormal.Lib.Tax.Tax
import StatFormal.Lib.Strong.Single
import StatFormal.Archive.RobustEquality.Tax.Proofs
import StatFormal.Archive.RobustEquality.CoverageRandom.Proofs

/-!
# Route: robust equality `prop:paired` (untrusted)

* `KL(P‖P) = 0` and `KL(P‖ν) ≥ −log ν(K) ≥ 0` for `ν(K) ≤ 1` give `τ_𝒩(P) = 0`, attained at `P`; then
  `W^P_ε(P̂,P) = OT_ε(P̂,P)` (certified `tax_identity`), so any bound on `OT_ε` is a valid radius; with the
  certified `coverage_random_folds` the random-fold radius is valid.
* Gaussian error: `G_b ∗ G_c = G_{√(b²+c²)}` (characteristic functions, `Measure.ext_of_charFun`), so
  `m₀ ∗ G_{b'} = G_b ∗ (G_c ∗ m₀)`, `c = √(b'² − b²)`; `P = L|_K / L(K)` is the tilt of `ν = L|_K ∈ 𝒩'_b` by `0`, and
  `KL(P‖ν) = −log L(K) ≤ log(1/p_K)` (`Foundations.Strong.klRef_tilted`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace StatFormal.Wave18b

open StatFormal.RobustEquality StatFormal.RobustEquality.Tax StatFormal.RobustEquality.SemidualStrong
  StatFormal.RobustEquality.Semidual StatFormal.Wave4b

lemma klRef_nonneg_ref {K : Type} [MeasurableSpace K] (P ν : Measure K) [IsProbabilityMeasure P]
    [IsFiniteMeasure ν] (h1 : ν univ ≤ 1) : 0 ≤ klRef P ν := by
  rw [StatFormal.Foundations.Tax.klRef_eq_klDiv]
  split_ifs
  · exact le_top
  · have : ν.real univ ≤ 1 := by
      rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1)
    exact EReal.coe_nonneg.2 (by linarith [ENNReal.toReal_nonneg (a := InformationTheory.klDiv P ν)])

lemma tax_zero_of_mem {K : Type} [MeasurableSpace K] {𝒩 : Set (Measure K)} (h𝒩 : RefClass 𝒩)
    (P : Measure K) [IsProbabilityMeasure P] (hP : P ∈ 𝒩) : tax 𝒩 P = 0 := by
  refine le_antisymm ((iInf₂_le P hP).trans_eq (StatFormal.Foundations.Tax.klRef_self P))
    (le_iInf₂ fun ν hν => ?_)
  obtain ⟨hf, -, h1⟩ := h𝒩 ν hν
  exact klRef_nonneg_ref P ν h1

theorem paired_tax_zero : Claims.paired_tax_zero := by
  intro K _ 𝒩H 𝒩 P _ h𝒩 hP hsub
  have h0 := tax_zero_of_mem h𝒩 P (hsub hP)
  exact ⟨h0, by rw [h0, StatFormal.Foundations.Tax.klRef_self]⟩

theorem paired_radius : Claims.paired_radius := by
  intro K _ k ε a c 𝒩H 𝒩 P _ r hs h𝒩 hP hsub hOT
  refine ⟨inferInstance, P, hsub hP, ?_⟩
  rw [tax_identity K k ε a c P P hs, StatFormal.Foundations.Tax.klRef_self, mul_zero, add_zero]
  exact hOT

theorem paired_radius_prob : Claims.paired_radius_prob := by
  intro K Ω _ _ μΩ k ε a c 𝒩H 𝒩 P _ r α hs h𝒩 hP hsub ⟨E, hEm, hEp, hE⟩
  exact ⟨E, hEm, hEp, fun ω hω => paired_radius K k ε a (c ω) 𝒩H 𝒩 P (r ω) (hs ω) h𝒩 hP hsub (hE hω)⟩

theorem paired_coverage : Claims.paired_coverage := by
  intro K _ P _ N V fold n e c B Bc ε a 𝒩H 𝒩 hfold hcomp hc hB hε hBc hosc ha0 ha1 hN h𝒩 hP hsub
  obtain ⟨E, hEm, hEp, hE⟩ := CoverageRandom.coverage_random_folds K P N V fold n e c B Bc ε a hfold hcomp hc
    hB hε hBc hosc ha0 ha1 hN
  refine ⟨E, hEm, hEp, fun X hX => ?_⟩
  have hs : Setting ε (fun _ : Fin N => (1 : ℝ) / N) (fun i => c (X i)) := by
    refine ⟨hε, fun _ => by positivity, ?_, fun i => hc.comp (measurable_const.prodMk measurable_id),
      B, fun i y => hB _ _⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  exact paired_radius K N ε _ _ 𝒩H 𝒩 P _ hs h𝒩 hP hsub (hE hX)

/-! ### Gaussian measurement error -/

section Gauss

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

instance isoN_isProb (σ : ℝ) : IsProbabilityMeasure (isoN E σ) := by
  unfold isoN; infer_instance

lemma charFun_isoN (σ : ℝ) (t : E) :
    charFun (isoN E σ) t = Complex.exp (-((σ ^ 2 * ‖t‖ ^ 2 : ℝ) : ℂ) / 2) := by
  rw [isoN, charFun_map_smul, charFun_stdGaussian, norm_smul]
  congr 1
  push_cast
  rw [mul_pow, Real.norm_eq_abs, ← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  push_cast; ring

lemma isoN_conv (b c : ℝ) : isoN E b ∗ isoN E c = isoN E √(b ^ 2 + c ^ 2) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_conv, charFun_isoN, charFun_isoN, charFun_isoN, ← Complex.exp_add,
    Real.sq_sqrt (by positivity)]
  congr 1
  push_cast; ring

lemma semigroup_split (m0 : Measure E) [IsProbabilityMeasure m0] {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') :
    m0 ∗ isoN E b' = isoN E b ∗ (isoN E √(b' ^ 2 - b ^ 2) ∗ m0) := by
  rw [← Measure.conv_assoc, isoN_conv, Real.sq_sqrt (by nlinarith), Measure.conv_comm]
  congr 2
  rw [show b ^ 2 + (b' ^ 2 - b ^ 2) = b' ^ 2 by ring, Real.sqrt_sq (hb.trans hbb)]

lemma gauss_member (K : Set E) (m0 : Measure E) [IsProbabilityMeasure m0] {b b' : ℝ} (hb : 0 ≤ b)
    (hbb : b ≤ b') : (m0 ∗ isoN E b').restrict K ∈ gaussMixClass E b K :=
  ⟨isoN E √(b' ^ 2 - b ^ 2) ∗ m0, inferInstance, by rw [semigroup_split m0 hb hbb]⟩

lemma klRef_cond_le (K : Set E) (L : Measure E) [IsProbabilityMeasure L] (hK : MeasurableSet K) {pK : ℝ}
    (hpK : 0 < pK) (hLK : ENNReal.ofReal pK ≤ L K) :
    klRef (L[|K]) (L.restrict K) ≤ ((Real.log (1 / pK) : ℝ) : EReal) := by
  set ν := L.restrict K with hν
  have hνu : ν univ = L K := by rw [hν, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  have hne : ν univ ≠ 0 := by
    rw [hνu]; exact (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hpK) hLK).ne'
  have : NeZero ν := ⟨fun h => hne (by rw [h]; rfl)⟩
  have hP : L[|K] = ν.tilted 0 := by
    rw [tilted_zero', hνu, ProbabilityTheory.cond]
  have hkl := StatFormal.Foundations.Strong.klRef_tilted ν (g := fun _ => (0 : ℝ)) measurable_const
    (B := 0) (fun _ => by simp)
  rw [hP]
  rw [show (0 : E → ℝ) = fun _ => (0 : ℝ) from rfl, hkl]
  simp only [integral_zero, Real.exp_zero, integral_const, smul_eq_mul, mul_one, zero_sub]
  apply EReal.coe_le_coe_iff.2
  have hreal : pK ≤ ν.real univ := by
    rw [measureReal_def, hνu]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hLK
  rw [one_div, Real.log_inv]
  exact neg_le_neg (Real.log_le_log hpK hreal)

theorem paired_gauss_tax : Claims.paired_gauss_tax := by
  intro E _ _ _ _ _ K m0 _ b b' pK hK hb hbb hpK hLK
  have hmem := gauss_member K m0 hb hbb
  have hle := klRef_cond_le K (m0 ∗ isoN E b') hK hpK hLK
  exact ⟨⟨_, hmem, hle⟩, (iInf₂_le _ hmem).trans hle⟩

theorem paired_gauss_radius : Claims.paired_gauss_radius := by
  intro E _ _ _ _ _ K m0 _ b b' pK k ε a c r hK hb hbb hpK hLK hs hOT
  have hmem := gauss_member K m0 hb hbb
  have hle := klRef_cond_le K (m0 ∗ isoN E b') hK hpK hLK
  have hne : (m0 ∗ isoN E b') K ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hpK) hLK).ne'
  have hPp : IsProbabilityMeasure ((m0 ∗ isoN E b')[|K]) := cond_isProbabilityMeasure hne
  refine ⟨hPp, _, hmem, ?_⟩
  rw [tax_identity E k ε a c _ _ hs]
  rw [EReal.coe_add, EReal.coe_mul]
  exact add_le_add hOT (StatFormal.Foundations.Tax.coe_mul_le_coe_mul hs.1.le hle)

end Gauss

end StatFormal.Wave18b
