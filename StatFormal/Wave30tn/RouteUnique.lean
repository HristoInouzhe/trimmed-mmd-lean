import StatFormal.Wave30tn.Statements
import StatFormal.Archive.Wave30ah.RouteBang
import StatFormal.Archive.TrimmedMMD.BangBang.Proofs

/-!
# Route — wave 30tn: `lem:unique` (untrusted)

* `discM u z = Σ_i u_i δ_{z_i}` (weights through `ofReal`): a probability measure for probability weights, with
  `∫ φ d(discM u z) = Σ u_i φ(z_i)` and, for injective `z`, `discM u z {z_i} = u_i`.
* `weights_eq`: two probability weight vectors on distinct points with the same embedding are equal (A3 + measurable
  singletons).
* `signed_zero`: a signed weight vector `r` with `Σ r = 0` and `Σ r_i φ(z_i) = 0` on distinct points is `0` (split
  `r = r⁺ − r⁻`, equal masses `c`; if `c > 0`, `r^±/c` have the same embedding, so `r⁺ = r⁻`). This is the paper's
  argument, with the two cases of the proof (`D̂ = 0`, two minimisers) as instances on `Fin n ⊕ Fin m`.
* `D̂ > 0`: a minimiser exists (frozen `bangbang_set`); a zero value would give `Σ w_i φ(X_i) = Σ v_j φ(Y_j)`, i.e.
  `signed_zero` for `(w, −v)`, contradicting `Σ w = 1`.
* Singleton: the witness is the same at two minimisers (frozen `bangbang_i`), i.e. `signed_zero` for `(w − w', −(v − v'))`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatFormal.Wave30tn

open StatFormal.TrimmedMMD.BangBang (capped qp)
open StatFormal.TrimmedMMD.ZeroSet (Characteristic)
open StatFormal.Wave30ah (trimSetEmp)

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H] {ι : Type*} [Fintype ι]

/-- The discrete measure `Σ_i u_i δ_{z_i}`. -/
def discM (u : ι → ℝ) (z : ι → 𝒳) : Measure 𝒳 := ∑ i, ENNReal.ofReal (u i) • Measure.dirac (z i)

lemma discM_univ {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (z : ι → 𝒳) :
    discM u z univ = ENNReal.ofReal (∑ i, u i) := by
  simp only [discM, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => hu i]

lemma discM_isProb {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1) (z : ι → 𝒳) :
    IsProbabilityMeasure (discM u z) :=
  ⟨by rw [discM_univ hu, hs, ENNReal.ofReal_one]⟩

lemma integral_discM {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (z : ι → 𝒳) :
    ∫ x, φ x ∂(discM u z) = ∑ i, u i • φ (z i) := by
  unfold discM
  rw [integral_finsetSum_measure fun i _ => ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)]
  simp_rw [integral_smul_measure, integral_dirac' _ _ hφ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_ofReal (hu i)]

lemma discM_singleton [DecidableEq ι] {u : ι → ℝ} {z : ι → 𝒳} (hz : Function.Injective z) (i : ι) :
    discM u z {z i} = ENNReal.ofReal (u i) := by
  simp only [discM, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [Measure.dirac_apply_of_mem (mem_singleton _), mul_one]
  · intro k _ hk
    rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
    simp [Set.indicator, hz.ne hk]
  · simp

/-- (A3) on finitely many distinct points: probability weights are determined by their embedding. -/
lemma weights_eq [DecidableEq ι] {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) (hchar : Characteristic φ) {z : ι → 𝒳}
    (hz : Function.Injective z) {u u' : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (hu' : ∀ i, 0 ≤ u' i)
    (hs : ∑ i, u i = 1) (hs' : ∑ i, u' i = 1) (he : ∑ i, u i • φ (z i) = ∑ i, u' i • φ (z i)) : u = u' := by
  have hM := hchar (discM u z) (discM u' z) (discM_isProb hu hs z) (discM_isProb hu' hs' z)
    (by rw [integral_discM hφ hu, integral_discM hφ hu', he])
  funext i
  have := congrArg (fun μ : Measure 𝒳 => μ {z i}) hM
  simp only [discM_singleton hz] at this
  exact (ENNReal.ofReal_eq_ofReal_iff (hu i) (hu' i)).1 this

/-- (A3) on finitely many distinct points: a signed weight vector of total mass `0` with zero embedding is `0`. -/
lemma signed_zero [DecidableEq ι] {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) (hchar : Characteristic φ) {z : ι → 𝒳}
    (hz : Function.Injective z) {r : ι → ℝ} (hr : ∑ i, r i = 0) (he : ∑ i, r i • φ (z i) = 0) : r = 0 := by
  set rp : ι → ℝ := fun i => max (r i) 0
  set rn : ι → ℝ := fun i => max (-r i) 0
  have hrp : ∀ i, 0 ≤ rp i := fun i => le_max_right _ _
  have hrn : ∀ i, 0 ≤ rn i := fun i => le_max_right _ _
  have hdec : ∀ i, r i = rp i - rn i := fun i => by
    simp only [rp, rn]; rcases le_total 0 (r i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hprod : ∀ i, rp i = 0 ∨ rn i = 0 := fun i => by
    simp only [rp, rn]; rcases le_total 0 (r i) with h | h
    · right; exact max_eq_right (by linarith)
    · left; exact max_eq_right h
  set c := ∑ i, rp i
  have hc : ∑ i, rn i = c := by
    have : ∑ i, r i = ∑ i, rp i - ∑ i, rn i := by rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => hdec i
    linarith
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun i _ => hrp i
  rcases hc0.eq_or_lt with h0 | hpos
  · have hp0 : ∀ i, rp i = 0 := fun i => (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hrp j).1 h0.symm i (Finset.mem_univ _)
    have hn0 : ∀ i, rn i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hrn j).1 (hc.trans h0.symm) i (Finset.mem_univ _)
    funext i; rw [hdec i, hp0 i, hn0 i]; simp
  · have heq := weights_eq hφ hchar hz (u := fun i => rp i / c) (u' := fun i => rn i / c)
      (fun i => div_nonneg (hrp i) hc0) (fun i => div_nonneg (hrn i) hc0)
      (by rw [← Finset.sum_div, div_self hpos.ne']) (by rw [← Finset.sum_div, hc, div_self hpos.ne'])
      (by
        have e1 : ∑ i, r i • φ (z i) = ∑ i, rp i • φ (z i) - ∑ i, rn i • φ (z i) := by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by rw [hdec i, sub_smul]
        have e2 : ∑ i, rp i • φ (z i) = ∑ i, rn i • φ (z i) := by rw [← sub_eq_zero, ← e1, he]
        simp_rw [div_eq_inv_mul, mul_smul, ← Finset.smul_sum, e2])
    funext i
    have := congrFun heq i
    rw [div_left_inj' hpos.ne'] at this
    rw [hdec i, this]; simp

theorem unique_trim_route : Claims.unique_trim := by
  intro 𝒳 H _ _ _ _ _ φ κ n m x y α β hφ hκ hchar hn hm hα0 hα1 hβ0 hβ1 hx hy hxy
  set x' : Fin n → H := φ ∘ x
  set y' : Fin m → H := φ ∘ y
  set S := capped n α ×ˢ capped m β
  set z : Fin n ⊕ Fin m → 𝒳 := Sum.elim x y
  have hz : Function.Injective z := hx.sumElim hy hxy
  obtain ⟨⟨p, hpS, hpmin⟩, -, -⟩ := StatFormal.Wave30ah.bangbang_set H n m x' y' α β hn hm hα0 hα1 hβ0 hβ1
  have hwit := (StatFormal.TrimmedMMD.BangBang.bangbang_i H n m x' y' α β hn hm hα0 hα1 hβ0 hβ1).2
  have hsum : ∀ (w : Fin n → ℝ) (v : Fin m → ℝ), ∑ i, (Sum.elim w (fun j => -v j) : Fin n ⊕ Fin m → ℝ) i • φ (z i) =
      ∑ i, w i • x' i - ∑ j, v j • y' j := fun w v => by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib, z, x', y', Function.comp]
    abel
  have hmass : ∀ (w : Fin n → ℝ) (v : Fin m → ℝ), ∑ i, (Sum.elim w (fun j => -v j) : Fin n ⊕ Fin m → ℝ) i =
      ∑ i, w i - ∑ j, v j := fun w v => by
    rw [Fintype.sum_sum_type]; simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib]; ring
  refine ⟨?_, ⟨p, ?_⟩⟩
  · -- `D̂ > 0`
    have hleast : IsLeast (qp x' y' '' S) (qp x' y' p) :=
      ⟨mem_image_of_mem _ hpS, by rintro _ ⟨p', hp', rfl⟩; exact hpmin hp'⟩
    rw [hleast.csInf_eq]
    refine Real.sqrt_pos.2 (lt_of_le_of_ne (sq_nonneg _) (fun h0 => ?_))
    have hnorm : ∑ i, p.1 i • x' i - ∑ j, p.2 j • y' j = 0 := by
      have : ‖∑ i, p.1 i • x' i - ∑ j, p.2 j • y' j‖ ^ 2 = 0 := h0.symm
      exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this)
    have hr := signed_zero hφ hchar hz (r := Sum.elim p.1 (fun j => -p.2 j))
      (by rw [hmass, hpS.1.2, hpS.2.2]; ring) (by rw [hsum]; exact hnorm)
    have h1 : ∀ i, p.1 i = 0 := fun i => by simpa using congrFun hr (Sum.inl i)
    have := hpS.1.2
    simp only [h1, Finset.sum_const_zero] at this
    exact zero_ne_one this
  · ext p'
    simp only [mem_singleton_iff]
    constructor
    · intro hp'
      have hw := hwit p hpS p' hp'.1 hpmin hp'.2
      have hr := signed_zero hφ hchar hz (r := Sum.elim (fun i => p'.1 i - p.1 i) (fun j => -(p'.2 j - p.2 j)))
        (by rw [hmass, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hpS.1.2, hpS.2.2, hp'.1.1.2, hp'.1.2.2]; ring)
        (by
          rw [hsum]
          simp only [sub_smul, Finset.sum_sub_distrib]
          rw [show ∀ A B C D : H, A - B - (C - D) = (A - C) - (B - D) from fun A B C D => by abel, ← hw, sub_self])
      refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
      · have := congrFun hr (Sum.inl i); simp only [Sum.elim_inl, Pi.zero_apply] at this; linarith
      · have := congrFun hr (Sum.inr j); simp only [Sum.elim_inr, Pi.zero_apply] at this; linarith
    · rintro rfl
      exact ⟨hpS, hpmin⟩

end StatFormal.Wave30tn
