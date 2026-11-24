import StatFormal.Archive.Wave29d.Statements
import StatFormal.Archive.WaveP2c.RouteTaxB

/-!
# Route — robust equality JASA `prop:tax` (b), the resolution class (untrusted)

The paper's proof (`supp_proofs.tex:652-656`): put the mixing law `m_y` of each box on its own copy `{y} × B(y)`, so
that its atoms carry the scale `S(y)`; the per-box bound of the smooth class (certified `box_law` of wave P2c, with the
box-dependent bandwidths `b_k = β s_k(y)`) gives `KL(U_{B(y)} ‖ G_{βs(y)} ∗ m_y) ≤ Σ_k (ϰ(β) + η)`; joint convexity
over the recorded values (`klDiv_finsum_le`), the restriction to `K` (`klRef_restrict`) and `η ↓ 0`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set Finset
open scoped ENNReal NNReal

set_option linter.style.longLine false

namespace StatFormal.Wave29d

open StatFormal.RobustEquality (klRef)
open StatFormal.Wave21a (boxU varkappa)
open StatFormal.WaveP2c (boxSet boxLaw boxMix gaussProd)

theorem tax_res : Claims.tax_res := by
  intro d Y p s β K hp hsum hs hβ hK hBK
  set T := (d : ℝ) * (varkappa β).toReal with hT
  set P := boxMix Y p s with hP
  have hPprob : IsProbabilityMeasure P := by
    refine ⟨?_⟩
    simp only [hP, boxMix, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg hp, hsum, ENNReal.ofReal_one]
  have hPK : P Kᶜ = 0 := by
    simp only [hP, boxMix, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun y hy => ?_
    rw [measure_mono_null (compl_subset_compl.2 (hBK y hy)) (StatFormal.WaveP2c.boxLaw_compl y (s y) (hs y hy)),
      mul_zero]
  have hκ0 : 0 ≤ (varkappa β).toReal := EReal.toReal_nonneg (StatFormal.Wave21a.tax_a_bound _ hβ).1
  have hT0 : 0 ≤ T := by positivity
  have hscale : ∀ y ∈ Y, ∀ k, β * s y k / s y k = β := fun y hy k => by
    field_simp [(hs y hy k).ne']
  have hPsub : P = ∑ i : {y // y ∈ Y}, ENNReal.ofReal (p i) • boxLaw (i : Fin d → ℝ) (s i) := by
    rw [hP, boxMix]; exact (Finset.sum_coe_sort Y (fun y => ENNReal.ofReal (p y) • boxLaw y (s y))).symm
  have key : ∀ η : ℝ, 0 < η →
      StatFormal.RobustEquality.Tax.tax (resClass Y s β K) P ≤ ((T + d * η : ℝ) : EReal) := by
    intro η hη
    have hex : ∀ i : {y // y ∈ Y}, ∃ my : Measure (Fin d → ℝ), IsProbabilityMeasure my ∧
        my (boxSet (i : Fin d → ℝ) (s i))ᶜ = 0 ∧
        klDiv (boxLaw (i : Fin d → ℝ) (s i)) (gaussProd (fun k => β * s i k) ∗ my) ≤
          ∑ k, ENNReal.ofReal ((varkappa (β * s i k / s i k)).toReal + η) :=
      fun i => StatFormal.WaveP2c.box_law (i : Fin d → ℝ) (s i) (fun k => β * s i k) (hs i i.2)
        (fun k => mul_pos hβ (hs i i.2 k)) hη
    choose my hmy hmysupp hmykl using hex
    have : ∀ i, IsProbabilityMeasure (my i) := hmy
    -- the resolution-class member: weights `p`, mixing laws `m_y` on the copies of the boxes
    classical
    set mfun : (Fin d → ℝ) → Measure (Fin d → ℝ) := fun y => if h : y ∈ Y then my ⟨y, h⟩ else Measure.dirac y
      with hmfun
    set ν := (∑ y ∈ Y, ENNReal.ofReal (p y) • (gaussProd (fun k => β * s y k) ∗ mfun y)).restrict K with hν
    have hmem : ν ∈ resClass Y s β K := by
      refine ⟨p, mfun, hp, hsum, fun y hy => ?_, rfl⟩
      simp only [hmfun, dif_pos hy]
      exact ⟨hmy _, hmysupp _⟩
    have htax : StatFormal.RobustEquality.Tax.tax (resClass Y s β K) P ≤ klRef P ν := iInf₂_le _ hmem
    set Q := ∑ y ∈ Y, ENNReal.ofReal (p y) • (gaussProd (fun k => β * s y k) ∗ mfun y) with hQ
    have hQsub : Q = ∑ i : {y // y ∈ Y}, ENNReal.ofReal (p i) • (gaussProd (fun k => β * s i k) ∗ my i) := by
      rw [hQ, ← Finset.sum_coe_sort Y]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hmfun, dif_pos i.2]
    have hgp : ∀ y : Fin d → ℝ, IsProbabilityMeasure (gaussProd (fun k => β * s y k)) := fun y => by
      unfold gaussProd; infer_instance
    have hpsub : ∑ i : {y // y ∈ Y}, p i = 1 := by rw [Finset.sum_coe_sort Y p]; exact hsum
    have hpsub0 : ∀ i : {y // y ∈ Y}, 0 ≤ p i := fun i => hp i i.2
    have hQprob : IsProbabilityMeasure Q := by
      rw [hQsub]
      refine ⟨?_⟩
      simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hpsub0 i, hpsub, ENNReal.ofReal_one]
    rw [hν, StatFormal.WaveP2c.klRef_restrict P _ hK hPK, StatFormal.WaveP2c.klRef_eq_coe_klDiv] at htax
    refine htax.trans ?_
    have hstep := StatFormal.WaveP2c.klDiv_finsum_le (ι := {y // y ∈ Y}) (fun i => ENNReal.ofReal (p i))
      (fun _ => ENNReal.ofReal_ne_top) (fun i => boxLaw (i : Fin d → ℝ) (s i))
      (fun i => gaussProd (fun k => β * s i k) ∗ my i)
    rw [← hPsub, ← hQsub] at hstep
    have hbound : ∑ i : {y // y ∈ Y}, ENNReal.ofReal (p i) *
        klDiv (boxLaw (i : Fin d → ℝ) (s i)) (gaussProd (fun k => β * s i k) ∗ my i) ≤ ENNReal.ofReal (T + d * η) := by
      calc _ ≤ ∑ i : {y // y ∈ Y}, ENNReal.ofReal (p i) * ∑ _k : Fin d, ENNReal.ofReal ((varkappa β).toReal + η) :=
            Finset.sum_le_sum fun i _ => by
              refine mul_le_mul_right ((hmykl i).trans_eq ?_) _
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [hscale i i.2 k]
        _ = ENNReal.ofReal (∑ i : {y // y ∈ Y}, p i * ∑ _k : Fin d, ((varkappa β).toReal + η)) := by
            rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hpsub0 i)
              (Finset.sum_nonneg fun k _ => by linarith)]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [ENNReal.ofReal_mul (hpsub0 i), ENNReal.ofReal_sum_of_nonneg fun k _ => by linarith]
        _ = ENNReal.ofReal (T + d * η) := by
            congr 1
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [← Finset.sum_mul, hpsub, one_mul, hT]; ring
    have h1 := hstep.trans hbound
    calc ((klDiv P Q : ℝ≥0∞) : EReal) ≤ ((ENNReal.ofReal (T + d * η) : ℝ≥0∞) : EReal) :=
          EReal.coe_ennreal_le_coe_ennreal_iff.2 h1
      _ = ((T + d * η : ℝ) : EReal) := by
          rw [EReal.coe_ennreal_ofReal, max_eq_left (by positivity)]
  have hall : ∀ ε : ℝ, 0 < ε →
      StatFormal.RobustEquality.Tax.tax (resClass Y s β K) P ≤ ((T + ε : ℝ) : EReal) := by
    intro ε hε
    refine (key (ε / (d + 1)) (by positivity)).trans (EReal.coe_le_coe_iff.2 ?_)
    have : (d : ℝ) * (ε / (d + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith
  induction h : StatFormal.RobustEquality.Tax.tax (resClass Y s β K) P using EReal.rec with
  | bot => exact bot_le
  | top =>
    have := hall 1 one_pos
    rw [h] at this
    exact absurd this (not_le.2 (EReal.coe_lt_top _))
  | coe t =>
    refine EReal.coe_le_coe_iff.2 (le_of_forall_pos_le_add fun ε hε => ?_)
    have := hall ε hε
    rw [h] at this
    exact EReal.coe_le_coe_iff.1 this

end StatFormal.Wave29d
