import StatFormal.Archive.Wave26b.Statements
import StatFormal.Archive.ICL.JointFull.Statements
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Route — ICL `cor:iid-consistency`, finite algebra (untrusted)

* `μ_w = Σ_j w_j δ_{z_j}` is a probability law with `∫ f dμ_w = Σ_j w_j f(z_j)`;
  `μ_w^{⊗M} = (w^{⊗M}).map (z ∘ ·)`, so `G^iid_{μ_w} = G^iid(w)` and `ρ_{μ_w} = ρ_w`.
* The product law `t ↦ Π_s w_{t_s}` on `[n]^M` is a probability vector whose one-slot marginal is `w`
  (`Fintype.prod_sum`).
* `0 ≤ KL(w|u_n) ≤ log n` on the simplex.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

namespace StatFormal.Wave26b

open StatFormal.Wave20a (rhoC PhiC)
open StatFormal.ICL.Joint (ProbVec)
open StatFormal.ICL.Diag (klUnif)

variable {Z : Type*} [MeasurableSpace Z]

/-- The weight measure `Σ_j w_j δ_j` on the index set. -/
def wMeas {n : ℕ} (w : Fin n → ℝ) : Measure (Fin n) := ∑ j, ENNReal.ofReal (w j) • Measure.dirac j

lemma wMeas_singleton {n : ℕ} (w : Fin n → ℝ) (j : Fin n) : wMeas w {j} = ENNReal.ofReal (w j) := by
  classical
  simp only [wMeas, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Measure.dirac_apply' _ (measurableSet_singleton j), hb]
  · simp

lemma poolLaw_eq_map {n : ℕ} (z : Fin n → Z) (w : Fin n → ℝ) : poolLaw z w = (wMeas w).map z := by
  have hz : Measurable z := measurable_from_top
  ext s hs
  rw [Measure.map_apply hz hs]
  simp only [poolLaw, wMeas, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.dirac_apply' _ hs, Measure.dirac_apply' _ (hz hs)]
  rfl

lemma univ_wMeas {n : ℕ} {w : Fin n → ℝ} (hw : ProbVec w) : wMeas w univ = 1 := by
  simp only [wMeas, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hw.1 j), hw.2, ENNReal.ofReal_one]

instance wMeas_isFinite {n : ℕ} (w : Fin n → ℝ) : IsFiniteMeasure (wMeas w) := by
  refine ⟨?_⟩
  simp only [wMeas, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul, measure_univ,
    mul_one]
  exact ENNReal.sum_lt_top.2 fun j _ => ENNReal.ofReal_lt_top

lemma poolLaw_isProb {n : ℕ} (z : Fin n → Z) {w : Fin n → ℝ} (hw : ProbVec w) :
    IsProbabilityMeasure (poolLaw z w) := by
  rw [poolLaw_eq_map]
  refine ⟨?_⟩
  rw [Measure.map_apply measurable_from_top MeasurableSet.univ, preimage_univ, univ_wMeas hw]

instance poolLaw_isFinite {n : ℕ} (z : Fin n → Z) (w : Fin n → ℝ) : IsFiniteMeasure (poolLaw z w) := by
  rw [poolLaw_eq_map]; infer_instance

lemma integral_wMeas {n : ℕ} {w : Fin n → ℝ} (hw : ∀ j, 0 ≤ w j) (f : Fin n → ℝ) :
    ∫ j, f j ∂(wMeas w) = ∑ j, w j * f j := by
  rw [integral_fintype (Integrable.of_finite)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.real, wMeas_singleton, ENNReal.toReal_ofReal (hw j), smul_eq_mul]

lemma integral_poolLaw {n : ℕ} (z : Fin n → Z) {w : Fin n → ℝ} (hw : ∀ j, 0 ≤ w j) {f : Z → ℝ}
    (hf : Measurable f) : ∫ x, f x ∂(poolLaw z w) = ∑ j, w j * f (z j) := by
  rw [poolLaw_eq_map, integral_map measurable_from_top.aemeasurable hf.aestronglyMeasurable, integral_wMeas hw]

lemma pi_poolLaw {n M : ℕ} (z : Fin n → Z) (w : Fin n → ℝ) :
    Measure.pi (fun _ : Fin M => poolLaw z w) = (Measure.pi fun _ : Fin M => wMeas w).map (fun t s => z (t s)) := by
  simp only [poolLaw_eq_map]
  rw [Measure.pi_map_pi (fun _ => measurable_from_top.aemeasurable)]

lemma pi_wMeas_singleton {n M : ℕ} (w : Fin n → ℝ) (t : Fin M → Fin n) :
    (Measure.pi fun _ : Fin M => wMeas w) {t} = ∏ s, ENNReal.ofReal (w (t s)) := by
  rw [← Set.univ_pi_singleton, Measure.pi_pi]
  simp only [wMeas_singleton]

lemma integral_pi_poolLaw {n M : ℕ} (z : Fin n → Z) {w : Fin n → ℝ} (hw : ∀ j, 0 ≤ w j)
    {g : (Fin M → Z) → ℝ} (hg : Measurable g) :
    ∫ t, g t ∂(Measure.pi fun _ : Fin M => poolLaw z w) = ∑ t : Fin M → Fin n, (∏ s, w (t s)) * g (z ∘ t) := by
  have hzt : Measurable fun (t : Fin M → Fin n) (s : Fin M) => z (t s) := Measurable.of_discrete
  rw [pi_poolLaw, integral_map hzt.aemeasurable hg.aestronglyMeasurable,
    integral_fintype (Integrable.of_finite)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Measure.real, pi_wMeas_singleton, ENNReal.toReal_prod, smul_eq_mul]
  congr 1
  exact Finset.prod_congr rfl fun s _ => ENNReal.toReal_ofReal (hw _)

lemma gIid_poolLaw {n M : ℕ} (L : Z → (Fin M → Z) → ℝ) (z : Fin n → Z) {w : Fin n → ℝ}
    (hw : ∀ j, 0 ≤ w j) (x : Z) (hL : Measurable (L x)) : gIid L (poolLaw z w) x = gIidPool L z w x := by
  unfold gIid gIidPool
  rw [integral_pi_poolLaw z hw hL]

lemma rhoC_poolLaw {n : ℕ} (Kk : Z → Z → ℝ) (z : Fin n → Z) {w : Fin n → ℝ} (hw : ∀ j, 0 ≤ w j) (x : Z)
    (hK : Measurable (Kk x)) : rhoC Kk (poolLaw z w) x = rhoPool Kk z w x := by
  unfold rhoC rhoPool
  rw [integral_poolLaw z hw hK]

/-! ### The product law on `[n]^M` -/

/-- `Π(t) = Π_s w_{t_s}`. -/
def prodLaw {n M : ℕ} (w : Fin n → ℝ) (t : Fin M → Fin n) : ℝ := ∏ s, w (t s)

lemma prodLaw_probVec {n M : ℕ} {w : Fin n → ℝ} (hw : ProbVec w) : ProbVec (prodLaw (M := M) w) := by
  refine ⟨fun t => Finset.prod_nonneg fun s _ => hw.1 _, ?_⟩
  unfold prodLaw
  rw [← Fintype.prod_sum (fun _ : Fin M => fun j => w j)]
  simp [hw.2]

lemma sum_prodLaw_indicator {n M : ℕ} {w : Fin n → ℝ} (hw : ProbVec w) (s : Fin M) (j : Fin n) :
    ∑ t : Fin M → Fin n, prodLaw w t * (if t s = j then 1 else 0) = w j := by
  classical
  set f : Fin M → Fin n → ℝ := fun s' i => if s' = s then (if i = j then w i else 0) else w i with hf
  have this : ∀ t : Fin M → Fin n, prodLaw w t * (if t s = j then 1 else 0) = ∏ s', f s' (t s') := by
    intro t
    unfold prodLaw
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ s), ← Finset.mul_prod_erase _ _ (Finset.mem_univ s)]
    have he : ∏ x ∈ Finset.univ.erase s, f x (t x) = ∏ x ∈ Finset.univ.erase s, w (t x) :=
      Finset.prod_congr rfl fun s' hs' => by simp [hf, Finset.ne_of_mem_erase hs']
    rw [he]
    simp only [hf, ite_true]
    split_ifs <;> ring
  calc ∑ t : Fin M → Fin n, prodLaw w t * (if t s = j then 1 else 0)
      = ∑ t : Fin M → Fin n, ∏ s', f s' (t s') := Finset.sum_congr rfl fun t _ => this t
    _ = ∏ s', ∑ i, f s' i := (Fintype.prod_sum f).symm
    _ = w j := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ s)]
      have he : ∏ x ∈ Finset.univ.erase s, ∑ i, f x i = 1 := by
        refine Finset.prod_eq_one fun s' hs' => ?_
        simp [hf, Finset.ne_of_mem_erase hs', hw.2]
      rw [he, mul_one]
      simp [hf]

lemma oneSlot_prodLaw {n M : ℕ} (hM : 1 ≤ M) {w : Fin n → ℝ} (hw : ProbVec w) (j : Fin n) :
    StatFormal.ICL.JointFull.oneSlot (prodLaw (M := M) w) j = w j := by
  classical
  unfold StatFormal.ICL.JointFull.oneSlot
  have hcard : ∀ t : Fin M → Fin n, (((Finset.univ.filter fun s => t s = j).card : ℕ) : ℝ) =
      ∑ s, (if t s = j then (1 : ℝ) else 0) := by
    intro t
    rw [Finset.sum_boole]
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  calc (1 / (M : ℝ)) * ∑ t, prodLaw w t * (((Finset.univ.filter fun s => t s = j).card : ℕ) : ℝ)
      = (1 / (M : ℝ)) * ∑ s : Fin M, ∑ t, prodLaw w t * (if t s = j then 1 else 0) := by
        congr 1
        simp_rw [hcard, Finset.mul_sum]
        exact Finset.sum_comm
    _ = (1 / (M : ℝ)) * ∑ s : Fin M, w j := by simp_rw [sum_prodLaw_indicator hw]
    _ = w j := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

omit [MeasurableSpace Z] in
lemma cover_prodLaw {n M : ℕ} (hM : 1 ≤ M) (Kk : Z → Z → ℝ) (z : Fin n → Z) {w : Fin n → ℝ} (hw : ProbVec w)
    (x : Z) :
    StatFormal.ICL.JointFull.cover (fun j x => Kk x (z j)) (prodLaw (M := M) w) x = rhoPool Kk z w x := by
  unfold StatFormal.ICL.JointFull.cover rhoPool
  simp_rw [oneSlot_prodLaw hM hw]

/-! ### `0 ≤ KL(w|u_n) ≤ log n` -/

lemma klUnif_nonneg {n : ℕ} {w : Fin n → ℝ} (hw : ProbVec w) : 0 ≤ klUnif n w := by
  unfold klUnif
  -- `w log(n w) ≥ w − 1/n` (from `log x ≥ 1 − 1/x`)
  have h : ∀ i, w i - 1 / n ≤ w i * Real.log (n * w i) := by
    intro i
    rcases (hw.1 i).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hn : (0 : ℝ) < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; exact (Fin.elim0 i)
        · exact_mod_cast h
      have hx : 0 < (n : ℝ) * w i := mul_pos hn hpos
      have hlog := Real.one_sub_inv_le_log_of_pos hx
      have : w i * (1 - ((n : ℝ) * w i)⁻¹) = w i - 1 / n := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left hlog hpos.le]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h i
  rw [Finset.sum_sub_distrib, hw.2] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have : (n : ℝ) * (1 / n) = 1 := by field_simp
    linarith

lemma klUnif_le_log {n : ℕ} {w : Fin n → ℝ} (hw : ProbVec w) : klUnif n w ≤ Real.log n := by
  unfold klUnif
  have h : ∀ i, w i * Real.log (n * w i) ≤ w i * Real.log n := by
    intro i
    rcases (hw.1 i).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hn : (0 : ℝ) < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; exact (Fin.elim0 i)
        · exact_mod_cast h
      have hw1 : w i ≤ 1 := by
        have := Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)
        rw [hw.2] at this; exact this
      refine mul_le_mul_of_nonneg_left (Real.log_le_log (mul_pos hn hpos) ?_) hpos.le
      nlinarith
  calc ∑ i, w i * Real.log (n * w i) ≤ ∑ i, w i * Real.log n := Finset.sum_le_sum fun i _ => h i
    _ = Real.log n := by rw [← Finset.sum_mul, hw.2, one_mul]

end StatFormal.Wave26b
