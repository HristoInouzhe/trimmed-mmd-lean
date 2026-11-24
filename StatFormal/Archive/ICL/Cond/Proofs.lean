import StatFormal.Archive.ICL.Cond.Statements
import StatFormal.Archive.ICL.CPS
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Proofs of `lem:cond-osc`, `lem:cond-tilt`, `lem:cond-metric` (untrusted proof file)
-/

noncomputable section
open Finset Real

namespace StatFormal.ICL.Cond

/-! ### Elementary facts about `tanh` -/

lemma tanh_quarter (ω : ℝ) :
    Real.tanh (ω / 4) = (Real.exp (ω / 2) - 1) / (Real.exp (ω / 2) + 1) := by
  have h : Real.exp (ω / 2) = Real.exp (ω / 4) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hp : 0 < Real.exp (ω / 4) := Real.exp_pos _
  rw [Real.tanh_eq, h, Real.exp_neg]
  field_simp

lemma tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  have hd : ∀ y, HasDerivAt (fun y => y * Real.cosh y - Real.sinh y) (y * Real.sinh y) y := by
    intro y
    have := ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub (Real.hasDerivAt_sinh y)
    convert this using 1
    all_goals first
      | (funext z; simp)
      | simp
  have hmono : Monotone (fun y => y * Real.cosh y - Real.sinh y) := by
    apply monotone_of_deriv_nonneg
    · intro y; exact (hd y).differentiableAt
    · intro y
      rw [(hd y).deriv]
      rcases le_total 0 y with h | h
      · exact mul_nonneg h (Real.sinh_nonneg_iff.mpr h)
      · exact mul_nonneg_of_nonpos_of_nonpos h (Real.sinh_nonpos_iff.mpr h)
  have h0 := hmono hx
  simp only [Real.cosh_zero, Real.sinh_zero, zero_mul, sub_zero] at h0
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos x)]
  linarith

/-! ### `lem:cond-osc` (i) on an arbitrary finset -/

lemma abs_eq_max_add (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring

lemma final_ineq (T α u g : ℝ) (hu : 0 < u) (hg : 1 ≤ g) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (h1 : T ≤ (u * g ^ 2 - 1) * α) (h2 : T ≤ (1 - u) * (1 - α)) : T ≤ (g - 1) / (g + 1) := by
  rw [le_div_iff₀ (by linarith)]
  rcases le_or_gt (u * g ^ 2 - 1) 0 with hX | hX
  · have hT : T ≤ 0 := by nlinarith [mul_nonpos_of_nonpos_of_nonneg hX hα0]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hT (by linarith : (0 : ℝ) ≤ g + 1)]
  rcases le_or_gt (1 - u) 0 with hY | hY
  · have hT : T ≤ 0 := by
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hY (by linarith : (0 : ℝ) ≤ 1 - α)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hT (by linarith : (0 : ℝ) ≤ g + 1)]
  have hg1 : 1 < g := by nlinarith
  have e1 := mul_le_mul_of_nonneg_left h1 hY.le
  have e2 := mul_le_mul_of_nonneg_left h2 hX.le
  have key : T * (u * (g ^ 2 - 1)) ≤ u * (g - 1) ^ 2 := by nlinarith [sq_nonneg (u * g - 1)]
  have hpos : 0 < u * (g - 1) := by nlinarith
  nlinarith

lemma osc_fin {ι : Type*} (s : Finset ι) (p q : ι → ℝ) (a ω : ℝ) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hps : ∑ i ∈ s, p i = 1) (hqs : ∑ i ∈ s, q i = 1)
    (hpq : ∀ i ∈ s, (p i = 0 ↔ q i = 0))
    (hlog : ∀ i ∈ s, p i ≠ 0 → a ≤ Real.log (p i / q i) ∧ Real.log (p i / q i) ≤ a + ω) :
    tv1 s p q ≤ Real.tanh (ω / 4) := by
  classical
  obtain ⟨i0, hi0, hpi0⟩ : ∃ i ∈ s, p i ≠ 0 := by
    by_contra h
    push Not at h
    rw [sum_eq_zero h] at hps
    norm_num at hps
  have hω : 0 ≤ ω := by have := hlog i0 hi0 hpi0; linarith
  set u := Real.exp a with hu_def
  set g := Real.exp (ω / 2) with hg_def
  have hu : 0 < u := Real.exp_pos a
  have hg : 1 ≤ g := Real.one_le_exp (by linarith)
  have hug : Real.exp (a + ω) = u * g ^ 2 := by
    rw [hu_def, hg_def, sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hbd : ∀ i ∈ s, p i ≠ 0 → u * q i ≤ p i ∧ p i ≤ u * g ^ 2 * q i := by
    intro i hi hpi
    have hp' : 0 < p i := lt_of_le_of_ne (hp i hi) (Ne.symm hpi)
    have hq' : 0 < q i := lt_of_le_of_ne (hq i hi) (fun h => hpi ((hpq i hi).2 h.symm))
    have hr : 0 < p i / q i := div_pos hp' hq'
    obtain ⟨h1, h2⟩ := hlog i hi hpi
    rw [Real.le_log_iff_exp_le hr, le_div_iff₀ hq'] at h1
    rw [Real.log_le_iff_le_exp hr, div_le_iff₀ hq', hug] at h2
    exact ⟨h1, h2⟩
  set P := ∑ i ∈ s, max (p i - q i) 0 with hP_def
  set Q := ∑ i ∈ s, max (q i - p i) 0 with hQ_def
  set α := ∑ i ∈ s, (if q i < p i then q i else 0) with hα_def
  have htv : tv1 s p q = (1 / 2) * (P + Q) := by
    unfold tv1
    rw [hP_def, hQ_def, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [abs_eq_max_add, neg_sub]
  have hPQ : P - Q = 0 := by
    rw [hP_def, hQ_def, ← sum_sub_distrib]
    have : ∀ i ∈ s, max (p i - q i) 0 - max (q i - p i) 0 = p i - q i := by
      intro i _
      rcases le_total 0 (p i - q i) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    rw [sum_congr rfl this, sum_sub_distrib, hps, hqs, sub_self]
  have hP : P ≤ (u * g ^ 2 - 1) * α := by
    rw [hP_def, hα_def, mul_sum]
    apply sum_le_sum
    intro i hi
    split_ifs with h
    · have hpi : p i ≠ 0 := (by linarith [hq i hi] : (0 : ℝ) < p i).ne'
      obtain ⟨-, h4⟩ := hbd i hi hpi
      rw [max_eq_left (by linarith)]
      linarith
    · rw [max_eq_right (by push Not at h; linarith)]
      simp
  have hQ : Q ≤ (1 - u) * (1 - α) := by
    have h1α : 1 - α = ∑ i ∈ s, (q i - if q i < p i then q i else 0) := by
      rw [sum_sub_distrib, hqs]
    rw [h1α, hQ_def, mul_sum]
    apply sum_le_sum
    intro i hi
    split_ifs with h
    · rw [max_eq_right (by linarith)]
      simp
    · by_cases hpi : p i = 0
      · have := (hpq i hi).1 hpi
        rw [hpi, this]
        simp
      · obtain ⟨h3, -⟩ := hbd i hi hpi
        rw [sub_zero, max_eq_left (by push Not at h; linarith)]
        linarith
  have hα0 : 0 ≤ α := sum_nonneg fun i hi => by
    split_ifs
    · exact hq i hi
    · exact le_rfl
  have hα1 : α ≤ 1 := by
    rw [hα_def, ← hqs]
    apply sum_le_sum
    intro i hi
    split_ifs
    · exact le_rfl
    · exact hq i hi
  have hT : tv1 s p q = P := by rw [htv]; linarith
  rw [tanh_quarter, hT]
  exact final_ineq P α u g hu hg hα0 hα1 hP (by linarith)

/-- `osc` with a log-ratio bound `|log p − log q − K| ≤ R` on the support. -/
lemma osc_logbound {ι : Type*} (s : Finset ι) (p q : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hps : ∑ i ∈ s, p i = 1) (hqs : ∑ i ∈ s, q i = 1)
    (hpq : ∀ i ∈ s, (p i = 0 ↔ q i = 0)) (K R : ℝ)
    (hb : ∀ i ∈ s, p i ≠ 0 → |Real.log (p i) - Real.log (q i) - K| ≤ R) :
    tv1 s p q ≤ Real.tanh (R / 2) := by
  have h := osc_fin s p q (K - R) (2 * R) hp hq hps hqs hpq (by
    intro i hi hpi
    have hqi : q i ≠ 0 := fun h => hpi ((hpq i hi).2 h)
    rw [Real.log_div hpi hqi]
    have := abs_le.mp (hb i hi hpi)
    constructor <;> linarith)
  have e : 2 * R / 4 = R / 2 := by ring
  rwa [e] at h

theorem cond_osc_i : Claims.cond_osc_i := by
  intro N p q a ω hp hq hps hqs hpq hlog
  exact osc_fin univ p q a ω (fun i _ => hp i) (fun i _ => hq i) hps hqs (fun i _ => hpq i)
    (fun i _ => hlog i)

/-! ### `lem:cond-osc` (ii) -/

lemma sum_abs_le_card_mul {ι : Type*} (S : Finset ι) (d : ι → ℝ) (Δ : ℝ)
    (h : ∀ i, |d i| ≤ Δ) : |∑ i ∈ S, d i| ≤ S.card * Δ := by
  calc |∑ i ∈ S, d i| ≤ ∑ i ∈ S, |d i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S, Δ := sum_le_sum fun i _ => h i
    _ = S.card * Δ := by rw [sum_const, nsmul_eq_mul]

lemma iidLaw_sum {n : ℕ} (w : Fin n → ℝ) (M : ℕ) (hw : ∑ j, w j = 1) :
    ∑ j, iidLaw w M j = 1 := by
  unfold iidLaw
  have := Fintype.prod_sum (fun (_ : Fin M) (i : Fin n) => w i)
  rw [← this]
  simp [hw]

theorem cond_osc_ii : Claims.cond_osc_ii := by
  intro n M w w' Δ BL L hM hMn hw hw' hws hws' hΔ hL
  have hn : 0 < n := by omega
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans (hΔ ⟨0, hn⟩)
  have hBL : 0 ≤ BL := (hL ∅).1.trans (hL ∅).2
  -- CPS
  have hD : ∀ v : Fin n → ℝ, (∀ j, 0 < v j) → ∑ j, v j = 1 → StatFormal.ICL.InDeltaM v M := by
    intro v hv hvs
    refine ⟨fun j => (hv j).le, hvs, ?_⟩
    rw [filter_true_of_mem (fun j _ => (hv j).ne'), card_univ, Fintype.card_fin]
    exact hMn
  have hWP := StatFormal.ICL.cps_wellPosed n M w (hD w hw hws)
  have hWP' := StatFormal.ICL.cps_wellPosed n M w' (hD w' hw' hws')
  have hcpspos : ∀ v : Fin n → ℝ, (∀ j, 0 < v j) → 0 < StatFormal.ICL.esym v univ M →
      ∀ S, 0 < StatFormal.ICL.cps v univ M S := fun v hv he S =>
    div_pos (prod_pos fun j _ => hv j) he
  have hcpslog : ∀ v : Fin n → ℝ, (∀ j, 0 < v j) → 0 < StatFormal.ICL.esym v univ M → ∀ S,
      Real.log (StatFormal.ICL.cps v univ M S) =
        ∑ j ∈ S, Real.log (v j) - Real.log (StatFormal.ICL.esym v univ M) := by
    intro v hv he S
    unfold StatFormal.ICL.cps
    rw [Real.log_div (prod_pos fun j _ => hv j).ne' he.ne', Real.log_prod (fun j _ => (hv j).ne')]
  have h1 : tv1 (univ.powersetCard M) (StatFormal.ICL.cps w univ M)
      (StatFormal.ICL.cps w' univ M) ≤ Real.tanh (M * Δ / 2) := by
    refine osc_logbound _ _ _ hWP.2.1 hWP'.2.1 hWP.2.2 hWP'.2.2 ?_
      (Real.log (StatFormal.ICL.esym w' univ M) - Real.log (StatFormal.ICL.esym w univ M))
      (M * Δ) ?_
    · intro S _
      exact ⟨fun h => absurd h (hcpspos w hw hWP.1 S).ne',
        fun h => absurd h (hcpspos w' hw' hWP'.1 S).ne'⟩
    · intro S hS _
      rw [hcpslog w hw hWP.1, hcpslog w' hw' hWP'.1]
      have hc := (mem_powersetCard.mp hS).2
      have := sum_abs_le_card_mul S (fun j => Real.log (w j) - Real.log (w' j)) Δ hΔ
      rw [hc, sum_sub_distrib] at this
      convert this using 2
      ring
  -- i.i.d.
  have hiidpos : ∀ v : Fin n → ℝ, (∀ j, 0 < v j) → ∀ j, 0 < iidLaw v M j :=
    fun v hv j => prod_pos fun k _ => hv (j k)
  have h2 : tv1 univ (iidLaw w M) (iidLaw w' M) ≤ Real.tanh (M * Δ / 2) := by
    refine osc_logbound _ _ _ (fun j _ => (hiidpos w hw j).le) (fun j _ => (hiidpos w' hw' j).le)
      (iidLaw_sum w M hws) (iidLaw_sum w' M hws') ?_ 0 (M * Δ) ?_
    · intro j _
      exact ⟨fun h => absurd h (hiidpos w hw j).ne', fun h => absurd h (hiidpos w' hw' j).ne'⟩
    · intro j _ _
      unfold iidLaw
      rw [Real.log_prod (fun k _ => (hw (j k)).ne'), Real.log_prod (fun k _ => (hw' (j k)).ne'),
        sub_zero, ← sum_sub_distrib]
      have := sum_abs_le_card_mul univ (fun k => Real.log (w (j k)) - Real.log (w' (j k))) Δ
        (fun k => hΔ (j k))
      rwa [card_univ, Fintype.card_fin] at this
  -- G
  have h3 : |StatFormal.ICL.Grisk w M L - StatFormal.ICL.Grisk w' M L| ≤
      BL * Real.tanh (M * Δ / 2) := by
    set p := StatFormal.ICL.cps w univ M
    set q := StatFormal.ICL.cps w' univ M
    have hsum0 : ∑ S ∈ univ.powersetCard M, (p S - q S) = 0 := by
      rw [sum_sub_distrib, hWP.2.2, hWP'.2.2, sub_self]
    have heq : StatFormal.ICL.Grisk w M L - StatFormal.ICL.Grisk w' M L =
        ∑ S ∈ univ.powersetCard M, (p S - q S) * (L S - BL / 2) := by
      have : ∑ S ∈ univ.powersetCard M, (p S - q S) * (L S - BL / 2) =
          ∑ S ∈ univ.powersetCard M, (p S * L S - q S * L S) -
            BL / 2 * ∑ S ∈ univ.powersetCard M, (p S - q S) := by
        rw [mul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun S _ => ?_
        ring
      rw [this, hsum0, mul_zero, sub_zero, sum_sub_distrib]
      rfl
    rw [heq]
    calc |∑ S ∈ univ.powersetCard M, (p S - q S) * (L S - BL / 2)|
        ≤ ∑ S ∈ univ.powersetCard M, |(p S - q S) * (L S - BL / 2)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ S ∈ univ.powersetCard M, |p S - q S| * (BL / 2) := by
          apply sum_le_sum
          intro S _
          rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_le]
          constructor <;> linarith [(hL S).1, (hL S).2]
      _ = BL * tv1 (univ.powersetCard M) p q := by
          unfold tv1
          rw [← sum_mul]
          ring
      _ ≤ BL * Real.tanh (M * Δ / 2) := mul_le_mul_of_nonneg_left h1 hBL
  refine ⟨h1, h2, h3, ?_⟩
  have := tanh_le_self (x := M * Δ / 2) (by positivity)
  have := mul_le_mul_of_nonneg_left this hBL
  linarith

/-! ### `lem:cond-tilt` -/

theorem cond_tilt : Claims.cond_tilt := by
  intro A t t' ϖ ϖ' ϖmin s hϖmin ht hts ht' hts' hϖ hϖ'
  have hZlow : ∀ (r v : Fin A → ℝ), (∀ a, 0 ≤ r a) → ∑ a, r a = 1 → (∀ a, ϖmin ≤ v a) →
      ϖmin ≤ ∑ a, r a * v a := by
    intro r v hr hrs hv
    calc ϖmin = ∑ a, r a * ϖmin := by rw [← sum_mul, hrs, one_mul]
      _ ≤ ∑ a, r a * v a := sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hv a) (hr a)
  have hϖpos : ∀ a, 0 < ϖ a := fun a => hϖmin.trans_le (hϖ a).1
  have hϖpos' : ∀ a, 0 < ϖ' a := fun a => hϖmin.trans_le (hϖ' a).1
  refine ⟨?_, ?_⟩
  · set Z := ∑ a, t a * ϖ a with hZ_def
    set Z' := ∑ a, t' a * ϖ a with hZ'_def
    have hZ : ϖmin ≤ Z := hZlow t ϖ ht hts fun a => (hϖ a).1
    have hZ' : ϖmin ≤ Z' := hZlow t' ϖ ht' hts' fun a => (hϖ a).1
    have hZp : 0 < Z := hϖmin.trans_le hZ
    have hZp' : 0 < Z' := hϖmin.trans_le hZ'
    set D := ∑ a, |t a - t' a| with hD_def
    have hD0 : 0 ≤ D := sum_nonneg fun a _ => abs_nonneg _
    have hZZ : |Z - Z'| ≤ D := by
      rw [hZ_def, hZ'_def, ← sum_sub_distrib]
      calc |∑ a, (t a * ϖ a - t' a * ϖ a)| ≤ ∑ a, |t a * ϖ a - t' a * ϖ a| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ a, |t a - t' a| := by
            apply sum_le_sum
            intro a _
            rw [← sub_mul, abs_mul, abs_of_pos (hϖpos a)]
            exact mul_le_of_le_one_right (abs_nonneg _) (hϖ a).2
    have key : ∀ a, |tilt t ϖ a - tilt t' ϖ a| ≤
        |t a - t' a| / Z + t' a * ϖ a * |Z - Z'| / (Z * Z') := by
      intro a
      have e : tilt t ϖ a - tilt t' ϖ a =
          (t a - t' a) * ϖ a / Z + t' a * ϖ a * (Z' - Z) / (Z * Z') := by
        unfold tilt
        rw [← hZ_def, ← hZ'_def]
        field_simp
        ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_mul, abs_of_pos hZp, abs_of_pos (hϖpos a)]
        apply div_le_div_of_nonneg_right _ hZp.le
        exact mul_le_of_le_one_right (abs_nonneg _) (hϖ a).2
      · rw [abs_div, abs_mul, abs_mul, abs_of_pos (mul_pos hZp hZp'), abs_of_pos (hϖpos a),
          abs_of_nonneg (ht' a), abs_sub_comm]
    calc ∑ a, |tilt t ϖ a - tilt t' ϖ a|
        ≤ ∑ a, (|t a - t' a| / Z + t' a * ϖ a * |Z - Z'| / (Z * Z')) := sum_le_sum fun a _ => key a
      _ = D / Z + |Z - Z'| / Z := by
          rw [sum_add_distrib, ← sum_div, ← sum_div, ← sum_mul, ← hZ'_def, ← hD_def]
          field_simp
      _ ≤ D / Z + D / Z := by gcongr
      _ = 2 * D / Z := by ring
      _ ≤ 2 * D / ϖmin := div_le_div_of_nonneg_left (by positivity) hϖmin hZ
  · intro hs
    set Z := ∑ a, t a * ϖ a with hZ_def
    set Z' := ∑ a, t a * ϖ' a with hZ'_def
    have hZp : 0 < Z := hϖmin.trans_le (hZlow t ϖ ht hts fun a => (hϖ a).1)
    have hZp' : 0 < Z' := hϖmin.trans_le (hZlow t ϖ' ht hts fun a => (hϖ' a).1)
    have hsum1 : ∀ v : Fin A → ℝ, 0 < ∑ a, t a * v a → ∑ a, tilt t v a = 1 := by
      intro v hv
      unfold tilt
      rw [← sum_div, div_self hv.ne']
    have hzero : ∀ v : Fin A → ℝ, (∀ a, 0 < v a) → 0 < ∑ a, t a * v a →
        ∀ a, (tilt t v a = 0 ↔ t a = 0) := by
      intro v hv hZv a
      unfold tilt
      simp [(hv a).ne', hZv.ne']
    have hnn : ∀ v : Fin A → ℝ, (∀ a, 0 < v a) → 0 < ∑ a, t a * v a → ∀ a, 0 ≤ tilt t v a := by
      intro v hv hZv a
      unfold tilt
      exact div_nonneg (mul_nonneg (ht a) (hv a).le) hZv.le
    have hlog : ∀ v : Fin A → ℝ, (∀ a, 0 < v a) → 0 < ∑ a, t a * v a → ∀ a, t a ≠ 0 →
        Real.log (tilt t v a) = Real.log (t a) + Real.log (v a) - Real.log (∑ b, t b * v b) := by
      intro v hv hZv a hta
      unfold tilt
      rw [Real.log_div (mul_ne_zero hta (hv a).ne') hZv.ne', Real.log_mul hta (hv a).ne']
    have h := osc_logbound univ (tilt t ϖ) (tilt t ϖ') (fun a _ => hnn ϖ hϖpos hZp a)
      (fun a _ => hnn ϖ' hϖpos' hZp' a) (hsum1 ϖ hZp) (hsum1 ϖ' hZp')
      (fun a _ => (hzero ϖ hϖpos hZp a).trans (hzero ϖ' hϖpos' hZp' a).symm)
      (Real.log Z' - Real.log Z) s (by
        intro a _ hpa
        have hta : t a ≠ 0 := fun h => hpa ((hzero ϖ hϖpos hZp a).2 h)
        rw [hlog ϖ hϖpos hZp a hta, hlog ϖ' hϖpos' hZp' a hta, ← hZ_def, ← hZ'_def]
        convert hs a using 2
        ring)
    unfold tv1 at h
    linarith

/-! ### `lem:cond-metric` -/

lemma softmax_ratio {n : ℕ} (g g' : Fin n → ℝ) (a μ : ℝ)
    (hg : ∀ k, a ≤ g k - g' k ∧ g k - g' k ≤ a + μ) (j : Fin n) :
    Real.exp (g j) / ∑ k, Real.exp (g k) ≤
      Real.exp μ * (Real.exp (g' j) / ∑ k, Real.exp (g' k)) := by
  have hZ' : 0 < ∑ k, Real.exp (g' k) := sum_pos (fun k _ => Real.exp_pos _) ⟨j, mem_univ j⟩
  have hup : ∀ k, Real.exp (g k) ≤ Real.exp (a + μ) * Real.exp (g' k) := fun k => by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [(hg k).2])
  have hlo : ∀ k, Real.exp a * Real.exp (g' k) ≤ Real.exp (g k) := fun k => by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [(hg k).1])
  have hZ : Real.exp a * ∑ k, Real.exp (g' k) ≤ ∑ k, Real.exp (g k) := by
    rw [mul_sum]; exact sum_le_sum fun k _ => hlo k
  calc Real.exp (g j) / ∑ k, Real.exp (g k)
      ≤ Real.exp (a + μ) * Real.exp (g' j) / (Real.exp a * ∑ k, Real.exp (g' k)) :=
        div_le_div₀ (by positivity) (hup j) (by positivity) hZ
    _ = Real.exp μ * (Real.exp (g' j) / ∑ k, Real.exp (g' k)) := by
        rw [Real.exp_add]; field_simp

lemma log_sub_le_of_le_exp_mul {x y μ : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x ≤ Real.exp μ * y) :
    Real.log x - Real.log y ≤ μ := by
  have := Real.log_le_log hx h
  rw [Real.log_mul (Real.exp_pos μ).ne' hy.ne', Real.log_exp] at this
  linarith

lemma log_sub_le_of_sub_le_mul {x y K : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x - y ≤ K * y) :
    Real.log x - Real.log y ≤ K := by
  rw [← Real.log_div hx.ne' hy.ne']
  calc Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx hy)
    _ = (x - y) / y := by field_simp
    _ ≤ K := by rw [div_le_iff₀ hy]; exact h

lemma eps_one (σ N εmin ε ε' : ℝ) (hσ : 0 < σ) (hN : 0 < N) (hεmin : 0 < εmin)
    (h1 : εmin ≤ ε) (h2 : ε ≤ 1 - εmin) (h3 : εmin ≤ ε') (h4 : ε' ≤ 1 - εmin) :
    Real.log ((1 - ε) * σ + ε / N) - Real.log ((1 - ε') * σ + ε' / N) ≤ |ε - ε'| / εmin := by
  have hNi : 0 < 1 / N := by positivity
  have hx : 0 < (1 - ε) * σ + ε / N := by
    have : 0 ≤ (1 - ε) * σ := mul_nonneg (by linarith) hσ.le
    have : 0 < ε / N := div_pos (by linarith) hN
    linarith
  have hy : 0 < (1 - ε') * σ + ε' / N := by
    have : 0 ≤ (1 - ε') * σ := mul_nonneg (by linarith) hσ.le
    have : 0 < ε' / N := div_pos (by linarith) hN
    linarith
  apply log_sub_le_of_sub_le_mul hx hy
  have hfx : (1 - ε) * σ + ε / N - ((1 - ε') * σ + ε' / N) = (ε - ε') * (1 / N - σ) := by ring
  have hlow : εmin * (σ + 1 / N) ≤ (1 - ε') * σ + ε' / N := by
    have : (1 - ε') * σ + ε' / N - εmin * (σ + 1 / N) =
        (1 - ε' - εmin) * σ + (ε' - εmin) * (1 / N) := by ring
    have : 0 ≤ (1 - ε' - εmin) * σ + (ε' - εmin) * (1 / N) :=
      add_nonneg (mul_nonneg (by linarith) hσ.le) (mul_nonneg (by linarith) hNi.le)
    linarith
  have hab : |1 / N - σ| ≤ σ + 1 / N := abs_le.mpr ⟨by linarith, by linarith⟩
  have e1 : (ε - ε') * (1 / N - σ) ≤ |ε - ε'| * (σ + 1 / N) :=
    calc (ε - ε') * (1 / N - σ) ≤ |(ε - ε') * (1 / N - σ)| := le_abs_self _
      _ = |ε - ε'| * |1 / N - σ| := abs_mul _ _
      _ ≤ |ε - ε'| * (σ + 1 / N) := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
  rw [hfx, div_mul_eq_mul_div, le_div_iff₀ hεmin]
  have e2 := mul_le_mul_of_nonneg_left hlow (abs_nonneg (ε - ε'))
  have e3 := mul_le_mul_of_nonneg_right e1 hεmin.le
  nlinarith

lemma eps_lemma (σ N εmin ε ε' : ℝ) (hσ : 0 < σ) (hN : 0 < N) (hεmin : 0 < εmin)
    (h1 : εmin ≤ ε) (h2 : ε ≤ 1 - εmin) (h3 : εmin ≤ ε') (h4 : ε' ≤ 1 - εmin) :
    |Real.log ((1 - ε) * σ + ε / N) - Real.log ((1 - ε') * σ + ε' / N)| ≤ |ε - ε'| / εmin := by
  rw [abs_sub_le_iff]
  refine ⟨eps_one σ N εmin ε ε' hσ hN hεmin h1 h2 h3 h4, ?_⟩
  rw [abs_sub_comm ε ε']
  exact eps_one σ N εmin ε' ε hσ hN hεmin h3 h4 h1 h2

lemma metric_core {n : ℕ} (j : Fin n) (g g' : Fin n → ℝ) (ε ε' εmin μ a : ℝ) (hεmin : 0 < εmin)
    (h1 : εmin ≤ ε) (h2 : ε ≤ 1 - εmin) (h3 : εmin ≤ ε') (h4 : ε' ≤ 1 - εmin) (hμ : 0 ≤ μ)
    (hg : ∀ k, a ≤ g k - g' k ∧ g k - g' k ≤ a + μ) :
    |Real.log ((1 - ε) * (Real.exp (g j) / ∑ k, Real.exp (g k)) + ε / n) -
      Real.log ((1 - ε') * (Real.exp (g' j) / ∑ k, Real.exp (g' k)) + ε' / n)| ≤
        μ + |ε - ε'| / εmin := by
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr (Fin.pos j)
  set σ := Real.exp (g j) / ∑ k, Real.exp (g k) with hσ_def
  set σ' := Real.exp (g' j) / ∑ k, Real.exp (g' k) with hσ'_def
  have hσ : 0 < σ := div_pos (Real.exp_pos _) (sum_pos (fun k _ => Real.exp_pos _) ⟨j, mem_univ j⟩)
  have hσ' : 0 < σ' :=
    div_pos (Real.exp_pos _) (sum_pos (fun k _ => Real.exp_pos _) ⟨j, mem_univ j⟩)
  have hs1 : σ ≤ Real.exp μ * σ' := softmax_ratio g g' a μ hg j
  have hs2 : σ' ≤ Real.exp μ * σ :=
    softmax_ratio g' g (-a - μ) μ (fun k => ⟨by linarith [(hg k).2], by linarith [(hg k).1]⟩) j
  have hc : 0 < ε / n := div_pos (by linarith) hN
  have hE : 1 ≤ Real.exp μ := Real.one_le_exp hμ
  have hw : ∀ r : ℝ, 0 < r → 0 < (1 - ε) * r + ε / n := fun r hr => by
    have : 0 ≤ (1 - ε) * r := mul_nonneg (by linarith) hr.le
    linarith
  have hmul : ∀ r r' : ℝ, 0 < r' → r ≤ Real.exp μ * r' →
      (1 - ε) * r + ε / n ≤ Real.exp μ * ((1 - ε) * r' + ε / n) := by
    intro r r' hr' h
    have f1 := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 - ε)
    have f2 := mul_le_mul_of_nonneg_right hE hc.le
    nlinarith
  have hA : |Real.log ((1 - ε) * σ + ε / n) - Real.log ((1 - ε) * σ' + ε / n)| ≤ μ := by
    rw [abs_sub_le_iff]
    exact ⟨log_sub_le_of_le_exp_mul (hw σ hσ) (hw σ' hσ') (hmul σ σ' hσ' hs1),
      log_sub_le_of_le_exp_mul (hw σ' hσ') (hw σ hσ) (hmul σ' σ hσ hs2)⟩
  have hB := eps_lemma σ' n εmin ε ε' hσ' hN hεmin h1 h2 h3 h4
  exact (abs_sub_le _ _ _).trans (add_le_add hA hB)

theorem cond_metric : Claims.cond_metric := by
  intro n d xs x diam εmin v τ τ' ε ε' j hεmin _ hdiam _ _ hv hv0 h1 h2 h3 h4
  unfold wRetr
  refine metric_core j (fun k => -(1 / 2) * ∑ l, τ l * (x l - xs k l) ^ 2)
    (fun k => -(1 / 2) * ∑ l, τ' l * (x l - xs k l) ^ 2) ε ε' εmin (diam ^ 2 * v)
    (-(diam ^ 2 * v) / 2) hεmin h1 h2 h3 h4 (mul_nonneg (sq_nonneg _) hv0) ?_
  intro k
  have e : -(1 / 2) * ∑ l, τ l * (x l - xs k l) ^ 2 - -(1 / 2) * ∑ l, τ' l * (x l - xs k l) ^ 2 =
      -(1 / 2) * ∑ l, (τ l - τ' l) * (x l - xs k l) ^ 2 := by
    rw [← mul_sub, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun l _ => ?_
    ring
  have hb : |∑ l, (τ l - τ' l) * (x l - xs k l) ^ 2| ≤ diam ^ 2 * v := by
    calc |∑ l, (τ l - τ' l) * (x l - xs k l) ^ 2| ≤ ∑ l, |(τ l - τ' l) * (x l - xs k l) ^ 2| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, v * (x l - xs k l) ^ 2 := by
          apply sum_le_sum
          intro l _
          rw [abs_mul, abs_of_nonneg (sq_nonneg (x l - xs k l))]
          exact mul_le_mul_of_nonneg_right (hv l) (sq_nonneg _)
      _ = v * ∑ l, (x l - xs k l) ^ 2 := by rw [mul_sum]
      _ ≤ v * diam ^ 2 := mul_le_mul_of_nonneg_left (hdiam k) hv0
      _ = diam ^ 2 * v := by ring
  rw [e]
  have := abs_le.mp hb
  constructor <;> linarith [this.1, this.2]

theorem cond_metric_iso : Claims.cond_metric_iso := by
  intro n d xs x diam εmin s s' ε ε' j hεmin _ hdiam _ _ h1 h2 h3 h4
  unfold wRetr
  have hN : ∀ k, 0 ≤ ∑ l, (x l - xs k l) ^ 2 := fun k => sum_nonneg fun l _ => sq_nonneg _
  have e : ∀ k, -(1 / 2) * ∑ l, s * (x l - xs k l) ^ 2 - -(1 / 2) * ∑ l, s' * (x l - xs k l) ^ 2 =
      (1 / 2) * ((s' - s) * ∑ l, (x l - xs k l) ^ 2) := by
    intro k
    rw [← mul_sum, ← mul_sum]
    ring
  have hμ : 0 ≤ (1 / 2) * diam ^ 2 * |s - s'| := by positivity
  rcases le_total s s' with hss | hss
  · refine metric_core j (fun k => -(1 / 2) * ∑ l, s * (x l - xs k l) ^ 2)
      (fun k => -(1 / 2) * ∑ l, s' * (x l - xs k l) ^ 2) ε ε' εmin
      ((1 / 2) * diam ^ 2 * |s - s'|) 0 hεmin h1 h2 h3 h4 hμ ?_
    intro k
    rw [e k, abs_of_nonpos (by linarith : s - s' ≤ 0)]
    have := mul_le_mul_of_nonneg_left (hdiam k) (by linarith : (0 : ℝ) ≤ s' - s)
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ s' - s) (hN k)
    constructor <;> nlinarith
  · refine metric_core j (fun k => -(1 / 2) * ∑ l, s * (x l - xs k l) ^ 2)
      (fun k => -(1 / 2) * ∑ l, s' * (x l - xs k l) ^ 2) ε ε' εmin
      ((1 / 2) * diam ^ 2 * |s - s'|) (-((1 / 2) * diam ^ 2 * |s - s'|)) hεmin h1 h2 h3 h4 hμ ?_
    intro k
    rw [e k, abs_of_nonneg (by linarith : 0 ≤ s - s')]
    have := mul_le_mul_of_nonpos_left (hdiam k) (by linarith : s' - s ≤ 0)
    have := mul_nonpos_of_nonpos_of_nonneg (by linarith : s' - s ≤ 0) (hN k)
    constructor <;> nlinarith

end StatFormal.ICL.Cond
