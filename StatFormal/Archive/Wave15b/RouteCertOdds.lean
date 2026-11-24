import StatFormal.Archive.Wave15b.Statements
import StatFormal.Archive.RobustEquality.SemidualStrong.Proofs

/-!
# Route: robust equality `lem:cert-odds` (untrusted)

`π_f(i|y) = e_i/Σe` with `e_i = a_i e^{(f_i − c_i(y))/ε}`, and `π(i|y) ∝ e_i d_i`, `d_i = e^{u_i/ε}`. With
`A = Σ_U e`, `B = Σ_{U^c} e`, `A' = Σ_U e d`, `B' = Σ_{U^c} e d` and `σ = e^{−s/ε}`: `φ_s(p_U) = A/(A + Bσ)`,
`π(U|y) = A'/(A' + B')`, and `A B' ≤ A' B σ` termwise (`d_j ≤ d_i σ` for `i ∈ U`, `j ∉ U`). The means: the certified
first-order condition `e^{−f*_i/ε} = ∫ e^{(g_{f*} − c_i)/ε} dP` (`maximiser_foc`) gives `E_P π(i|Y) = a_i`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Finset

namespace StatFormal.Wave15b

open StatFormal.RobustEquality.Semidual (gsoft)
open StatFormal.RobustEquality.SemidualStrong (Jdual Setting)

section Basic

variable {Y : Type*} {k : ℕ}

/-- `S_f(y) = Σ_i a_i e^{(f_i − c_i(y))/ε}`. -/
def sumE (ε : ℝ) (a f : Fin k → ℝ) (c : Fin k → Y → ℝ) (y : Y) : ℝ :=
  ∑ i, a i * Real.exp ((f i - c i y) / ε)

lemma sumE_pos {ε : ℝ} {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) (hk : 0 < k) (f : Fin k → ℝ)
    (c : Fin k → Y → ℝ) (y : Y) : 0 < sumE ε a f c y := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact Finset.sum_pos (fun i _ => mul_pos (ha i) (Real.exp_pos _)) univ_nonempty

lemma piCond_eq {ε : ℝ} (hε : 0 < ε) {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) (hk : 0 < k)
    (f : Fin k → ℝ) (c : Fin k → Y → ℝ) (y : Y) (i : Fin k) :
    piCond ε a f c y i = a i * Real.exp ((f i - c i y) / ε) / sumE ε a f c y := by
  have hS := sumE_pos (ε := ε) ha hk f c y
  unfold piCond gsoft
  have : (f i + -ε * Real.log (∑ i, a i * Real.exp ((f i - c i y) / ε)) - c i y) / ε =
      (f i - c i y) / ε + -Real.log (sumE ε a f c y) := by
    unfold sumE; field_simp; ring
  rw [this, Real.exp_add, Real.exp_neg, Real.exp_log hS]
  ring

lemma piCond_nonneg {ε : ℝ} {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) (f : Fin k → ℝ)
    (c : Fin k → Y → ℝ) (y : Y) (i : Fin k) : 0 ≤ piCond ε a f c y i :=
  mul_nonneg (ha i).le (Real.exp_pos _).le

lemma piCond_sum {ε : ℝ} (hε : 0 < ε) {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) (hk : 0 < k)
    (f : Fin k → ℝ) (c : Fin k → Y → ℝ) (y : Y) : ∑ i, piCond ε a f c y i = 1 := by
  simp only [piCond_eq hε ha hk, ← Finset.sum_div]
  exact div_self (sumE_pos ha hk f c y).ne'

lemma piCond_sumU_le {ε : ℝ} (hε : 0 < ε) {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) (hk : 0 < k)
    (f : Fin k → ℝ) (c : Fin k → Y → ℝ) (y : Y) (U : Finset (Fin k)) :
    ∑ i ∈ U, piCond ε a f c y i ≤ 1 := by
  rw [← piCond_sum hε ha hk f c y]
  exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ U) fun i _ _ => piCond_nonneg ha f c y i

lemma piCond_sumU_pos {ε : ℝ} {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) (f : Fin k → ℝ)
    (c : Fin k → Y → ℝ) (y : Y) {U : Finset (Fin k)} (hU : U.Nonempty) :
    0 < ∑ i ∈ U, piCond ε a f c y i :=
  Finset.sum_pos (fun i _ => mul_pos (ha i) (Real.exp_pos _)) hU

lemma phiOdds_zero {ε p : ℝ} (hp : 0 < p) : phiOdds ε 0 p = p := by
  unfold phiOdds
  rw [neg_zero, zero_div, Real.exp_zero, mul_one]
  have : 1 + (1 - p) / p = 1 / p := by field_simp; ring
  rw [this, one_div, inv_inv]

lemma phiOdds_mono {ε p : ℝ} (hε : 0 < ε) (hp : 0 < p) (hp1 : p ≤ 1) {s s' : ℝ} (h : s ≤ s') :
    phiOdds ε s p ≤ phiOdds ε s' p := by
  unfold phiOdds
  have hq : 0 ≤ (1 - p) / p := div_nonneg (by linarith) hp.le
  have he : Real.exp (-s' / ε) ≤ Real.exp (-s / ε) :=
    Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith) hε.le)
  apply inv_anti₀ (by positivity)
  nlinarith [Real.exp_pos (-s' / ε)]

lemma phiOdds_mem {ε p s : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    0 ≤ phiOdds ε s p ∧ phiOdds ε s p ≤ 1 := by
  unfold phiOdds
  have hq : 0 ≤ (1 - p) / p * Real.exp (-s / ε) :=
    mul_nonneg (div_nonneg (by linarith) hp.le) (Real.exp_pos _).le
  exact ⟨inv_nonneg.2 (by linarith), inv_le_one_of_one_le₀ (by linarith)⟩

end Basic

theorem cert_odds_phi : Claims.cert_odds_phi := by
  intro ε p hε hp hp1
  exact ⟨phiOdds_zero hp, fun s s' h => phiOdds_mono hε hp hp1 h, fun s => phiOdds_mem hp hp1⟩

theorem cert_odds_pointwise : Claims.cert_odds_pointwise := by
  intro Y k ε a fs f c U s y hε ha hU hs hgap
  have hk : 0 < k := by
    obtain ⟨i, -⟩ := hU; exact Fin.pos i
  set e : Fin k → ℝ := fun i => a i * Real.exp ((f i - c i y) / ε) with he_def
  set d : Fin k → ℝ := fun i => Real.exp ((fs i - f i) / ε) with hd_def
  have he : ∀ i, 0 < e i := fun i => mul_pos (ha i) (Real.exp_pos _)
  have hd : ∀ i, 0 < d i := fun i => Real.exp_pos _
  have hed : ∀ i, a i * Real.exp ((fs i - c i y) / ε) = e i * d i := by
    intro i
    simp only [e, d, mul_assoc, ← Real.exp_add]
    congr 2; ring
  set σ := Real.exp (-s / ε)
  have hσ : 0 < σ := Real.exp_pos _
  set A := ∑ i ∈ U, e i
  set B := ∑ i ∈ Uᶜ, e i
  set A' := ∑ i ∈ U, e i * d i
  set B' := ∑ i ∈ Uᶜ, e i * d i
  have hA : 0 < A := Finset.sum_pos (fun i _ => he i) hU
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => (he i).le
  have hA' : 0 < A' := Finset.sum_pos (fun i _ => mul_pos (he i) (hd i)) hU
  have hB' : 0 ≤ B' := Finset.sum_nonneg fun i _ => (mul_pos (he i) (hd i)).le
  -- `p_U = A/(A+B)` and `π(U) = A'/(A'+B')`
  have hSf : sumE ε a f c y = A + B := by
    unfold sumE; exact (Finset.sum_add_sum_compl U e).symm
  have hSfs : sumE ε a fs c y = A' + B' := by
    unfold sumE
    simp only [hed]
    exact (Finset.sum_add_sum_compl U fun i => e i * d i).symm
  have hp : ∑ i ∈ U, piCond ε a f c y i = A / (A + B) := by
    simp only [piCond_eq hε ha hk, ← Finset.sum_div, hSf]
    rfl
  have hπ : ∑ i ∈ U, piCond ε a fs c y i = A' / (A' + B') := by
    simp only [piCond_eq hε ha hk, ← Finset.sum_div, hSfs, hed]
    rfl
  have hphi : phiOdds ε s (A / (A + B)) = A / (A + B * σ) := by
    unfold phiOdds
    have : 1 + (1 - A / (A + B)) / (A / (A + B)) * σ = (A + B * σ) / A := by
      field_simp; ring
    rw [this, inv_div]
  rw [hp, hπ, hphi, div_le_div_iff₀ (by positivity) (by positivity)]
  -- termwise `e_i e_j d_j ≤ e_i d_i e_j σ`
  have hcross : A * B' ≤ A' * B * σ := by
    have h1 : A * B' = ∑ i ∈ U, ∑ j ∈ Uᶜ, e i * (e j * d j) := Finset.sum_mul_sum _ _ _ _
    have h2 : A' * B * σ = ∑ i ∈ U, ∑ j ∈ Uᶜ, e i * d i * e j * σ := by
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
    rw [h1, h2]
    refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
    have hj' : j ∉ U := Finset.mem_compl.1 hj
    have hdj : d j ≤ d i * σ := by
      simp only [d, σ, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have := hgap i hi j hj'
      rw [← add_div, div_le_div_iff_of_pos_right hε]
      linarith
    have := mul_le_mul_of_nonneg_left hdj (mul_nonneg (he i).le (he j).le)
    nlinarith [this]
  nlinarith [hcross]

section Means

variable {Y : Type*} [MeasurableSpace Y] {k : ℕ}

lemma piCond_meas {ε : ℝ} {a : Fin k → ℝ} (f : Fin k → ℝ) {c : Fin k → Y → ℝ}
    (hc : ∀ i, Measurable (c i)) (i : Fin k) : Measurable fun y => piCond ε a f c y i := by
  unfold piCond gsoft
  have hS : Measurable fun y => ∑ l, a l * Real.exp ((f l - c l y) / ε) :=
    Finset.measurable_sum _ fun l _ =>
      ((((measurable_const.sub (hc l)).div_const ε)).exp).const_mul (a l)
  exact ((((measurable_const.add ((Real.measurable_log.comp hS).const_mul (-ε))).sub
    (hc i)).div_const ε).exp).const_mul (a i)

lemma sumU_meas {ε : ℝ} {a : Fin k → ℝ} (f : Fin k → ℝ) {c : Fin k → Y → ℝ}
    (hc : ∀ i, Measurable (c i)) (U : Finset (Fin k)) :
    Measurable fun y => ∑ i ∈ U, piCond ε a f c y i :=
  Finset.measurable_sum _ fun i _ => piCond_meas f hc i

lemma phi_meas {ε s : ℝ} {g : Y → ℝ} (hg : Measurable g) :
    Measurable fun y => phiOdds ε s (g y) := by
  unfold phiOdds
  exact (measurable_const.add (((measurable_const.sub hg).div hg).mul_const _)).inv

lemma integrable_of_unit {P : Measure Y} [IsFiniteMeasure P] {g : Y → ℝ} (hg : Measurable g)
    (h0 : ∀ y, 0 ≤ g y) (h1 : ∀ y, g y ≤ 1) : Integrable g P :=
  Integrable.mono' (integrable_const (1 : ℝ)) hg.aestronglyMeasurable
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 y)]; exact h1 y)

end Means

theorem cert_odds_mean : Claims.cert_odds_mean := by
  intro Y _ k ε a fs f c P _ U s hset hmax hU hs hgap
  obtain ⟨hε, ha, hsum, hc, hB⟩ := hset
  have hk : 0 < k := by
    obtain ⟨i, -⟩ := hU; exact Fin.pos i
  -- (iii): `E_P π(i|Y) = a_i`
  have hfoc := (StatFormal.RobustEquality.SemidualStrong.maximiser_foc Y k ε a c P fs
    ⟨hε, ha, hsum, hc, hB⟩ hmax).1
  have hiii : ∀ i, ∫ y, piCond ε a fs c y i ∂P = a i := by
    intro i
    have : (fun y => piCond ε a fs c y i) =
        fun y => a i * Real.exp (fs i / ε) * Real.exp ((gsoft ε a fs c y - c i y) / ε) := by
      funext y
      unfold piCond
      rw [mul_assoc, ← Real.exp_add]
      congr 2; ring
    rw [this, integral_const_mul, ← hfoc i, mul_assoc, ← Real.exp_add,
      show fs i / ε + -fs i / ε = 0 by ring, Real.exp_zero, mul_one]
  have hint : ∀ (g : Fin k → ℝ) i, Integrable (fun y => piCond ε a g c y i) P := by
    intro g i
    refine integrable_of_unit (piCond_meas g hc i) (fun y => piCond_nonneg ha g c y i) fun y => ?_
    have := piCond_sumU_le hε ha hk g c y {i}
    simpa using this
  have hpU : ∀ y, 0 < ∑ i ∈ U, piCond ε a f c y i := fun y => piCond_sumU_pos ha f c y hU
  have hpU1 : ∀ y, ∑ i ∈ U, piCond ε a f c y i ≤ 1 := fun y => piCond_sumU_le hε ha hk f c y U
  have hphiI : ∀ s', Integrable (fun y => phiOdds ε s' (∑ i ∈ U, piCond ε a f c y i)) P := fun s' =>
    integrable_of_unit (phi_meas (sumU_meas f hc U)) (fun y => (phiOdds_mem (hpU y) (hpU1 y)).1)
      fun y => (phiOdds_mem (hpU y) (hpU1 y)).2
  refine ⟨?_, ?_, ?_⟩
  · unfold mOdds
    calc ∫ y, phiOdds ε s (∑ i ∈ U, piCond ε a f c y i) ∂P
        ≤ ∫ y, ∑ i ∈ U, piCond ε a fs c y i ∂P :=
          integral_mono (hphiI s) (integrable_finset_sum U fun i _ => hint fs i) fun y =>
            cert_odds_pointwise Y k ε a fs f c U s y hε ha hU hs hgap
      _ = ∑ i ∈ U, a i := by
          rw [integral_finset_sum U fun i _ => hint fs i]
          exact Finset.sum_congr rfl fun i _ => hiii i
  · unfold gradJ mOdds
    rw [Finset.sum_sub_distrib, ← integral_finset_sum U fun i _ => hint f i]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    exact (phiOdds_zero (hpU y)).symm
  · unfold mOdds
    exact integral_mono (hphiI 0) (hphiI s) fun y => phiOdds_mono hε (hpU y) (hpU1 y) hs

end StatFormal.Wave15b
