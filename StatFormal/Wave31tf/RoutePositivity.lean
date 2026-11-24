import StatFormal.Wave31tf.RouteSimple
import StatFormal.Wave30tu.Full.Route
import StatFormal.Wave31ta.Proofs
import StatFormal.Archive.Wave18b.RouteContinuity
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs

set_option linter.style.longLine false

/-!
# Route: wave 31tf, `n(a)` at the paper's threshold (untrusted)

The paper's `τ_{n,n}(·,δ)` is nondecreasing on `[0,1)` (the certified `Wave30tu.Full.tauFull_threshold` and `Wave31ta.tauV2Cpl_facts`, through
`ValidThreshold`), the path `a ↦ D_a(P,Q)` is continuous on `[0,1)` (certified `Wave18b.continuity_cont`) and zero at `α⋆ = TV(P,Q)` without (A3)
(certified `zero_of_tv_le`), so the generic `n_of_a_generic` applies as soon as `τ_{n,n}(0,δ) > 0` for every `n ≥ 1`. No certified fact gives this
positivity for `δ ∈ (0,1)` (the certified `ratecond_*` are for `δ = e^{−n}` and give `≥ D_φ`), so it is proved here from the definitions, for
`κ > 0`, `D > 0`, `δ ∈ (0,1)`, `n, m ≥ 1`:
* `τ^A(0) ≥ 2κ√s > 0` (`s = 1/n + 1/m`, `e_k ≥ 0`) and `τ^P(0) = v√s + D√(s log(1/δ)/2) ≥ v√s > 0`, `v = √min(κ², D²/2) > 0`;
* `τ^{P'}(0) = inf{t ≥ 0 : Ψ_H(t;1,s,c) ≤ δ}`: the set contains the McDiarmid root `v√s + D√(s log(1/δ)/2)` (nonempty) and every element is
  `≥ v√s/2`: for `t < v√s/2` the McDiarmid term is `1 > δ` (`t < v√s`) and Pinelis' term is `≥ 2e^{−1/4} > 1 > δ` (by the certified
  `pinelis_ineq`, `(x+y)log(1+x/y) − x ≤ x²/y`, the exponent is `≥ −t²/(v²s) > −1/4`);
* the coupled supremum `τ^{cpl}_{P'}(0) = sup_{u ∈ [0,κ²)} τ^{P'}(0; √(κ²−u), √(κ²+u)) ≥` its `u = 0` term `> 0`, the family being bounded above by
  `κ√s + D√(s log(1/δ)/2)` (so the real `⨆` is genuine).
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace StatFormal.Wave31tf

open StatFormal.Wave30tp StatFormal.Wave30ts StatFormal.TrimmedMMD.Unconditional

/-- The McDiarmid root `v√s + D√(s log(1/δ)/2)` has McDiarmid tail exactly `δ` (`β = 1`). -/
lemma psiMcD_root {D v δ : ℝ} {n m : ℕ} (hD : 0 < D) (hv : 0 ≤ v) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    psiMcD D v 1 (sNM n m) (v * √(sNM n m) + D * √(sNM n m * Real.log (1 / δ) / 2)) = δ := by
  have hs : 0 < sNM n m := StatFormal.Wave30tp.sNM_pos hn hm
  have hL : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((one_le_div hδ0).2 hδ1.le)
  have hb : √(1 * v ^ 2 * sNM n m) = v * √(sNM n m) := by
    rw [show 1 * v ^ 2 * sNM n m = (v * √(sNM n m)) ^ 2 by rw [mul_pow, Real.sq_sqrt hs.le]; ring]
    exact Real.sqrt_sq (by positivity)
  have hw : 0 ≤ D * √(sNM n m * Real.log (1 / δ) / 2) := by positivity
  have hsq : (D * √(sNM n m * Real.log (1 / δ) / 2)) ^ 2 = D ^ 2 * (sNM n m * Real.log (1 / δ) / 2) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  unfold psiMcD
  rw [hb, add_sub_cancel_left, max_eq_left hw, hsq]
  have hexp : -2 * (D ^ 2 * (sNM n m * Real.log (1 / δ) / 2)) / (1 ^ 2 * D ^ 2 * sNM n m) = -Real.log (1 / δ) := by
    field_simp
  rw [hexp, Real.exp_neg, Real.exp_log (by positivity)]
  simp

/-- The McDiarmid root is admissible for `τ^{P'}(0)`. -/
lemma psiH_root_le {D v ρ δ : ℝ} {n m : ℕ} (hD : 0 < D) (hv : 0 ≤ v) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    psiH D v ρ 1 (sNM n m) (cNM n m) (v * √(sNM n m) + D * √(sNM n m * Real.log (1 / δ) / 2)) ≤ δ :=
  (min_le_left _ _).trans (psiMcD_root hD hv hδ0 hδ1 hn hm).le

/-- Below `v√s/2` neither term of `Ψ_H(·;1,s,c)` is `≤ δ`. -/
lemma lt_psiH_of_small {D v ρ δ : ℝ} {n m : ℕ} (hv : 0 < v) (hρ : 0 < ρ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < v * √(sNM n m) / 2) :
    δ < psiH D v ρ 1 (sNM n m) (cNM n m) t := by
  have hs : 0 < sNM n m := StatFormal.Wave30tp.sNM_pos hn hm
  have hc : 0 < cNM n m := StatFormal.Wave30tp.cNM_pos hn
  set b := v * √(sNM n m) with hbdef
  have hbpos : 0 < b := by positivity
  have hb : √(1 * v ^ 2 * sNM n m) = b := by
    rw [show 1 * v ^ 2 * sNM n m = b ^ 2 by rw [hbdef, mul_pow, Real.sq_sqrt hs.le]; ring]
    exact Real.sqrt_sq hbpos.le
  have hb2 : 1 * v ^ 2 * sNM n m = b ^ 2 := by rw [hbdef, mul_pow, Real.sq_sqrt hs.le]; ring
  unfold psiH
  refine lt_min ?_ ?_
  · -- McDiarmid: `t < b`, so the exponent is `0` and the tail is `1`
    unfold psiMcD
    rw [hb, max_eq_right (by linarith)]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div, Real.exp_zero]
    exact hδ1
  · -- Pinelis: `2 exp(E)` with `E ≥ −t²/b² > −1/4`
    unfold psiPin
    set a := 1 * ρ * cNM n m with hadef
    have hapos : 0 < a := by positivity
    have hb2pos : 0 < 1 * v ^ 2 * sNM n m := by positivity
    set b2 := 1 * v ^ 2 * sNM n m with hb2def
    have hx : 0 ≤ t / a := by positivity
    have hy : 0 < b2 / a ^ 2 := by positivity
    have hP := StatFormal.Wave30tu.pinelis_ineq (t / a) (b2 / a ^ 2) hx hy
    have e1 : t * a / b2 = (t / a) / (b2 / a ^ 2) := by field_simp
    have e2 : (t / a) ^ 2 / (b2 / a ^ 2) = t ^ 2 / b2 := by field_simp
    rw [e1]
    rw [e2] at hP
    have hE : -(t ^ 2 / b2) ≤ t / a - (t / a + b2 / a ^ 2) * Real.log (1 + t / a / (b2 / a ^ 2)) := by linarith
    have ht2 : t ^ 2 / b2 < 1 / 4 := by
      rw [div_lt_iff₀ hb2pos, hb2]
      have : t ^ 2 < (b / 2) ^ 2 := by
        have : t < b / 2 := by rw [hbdef]; exact ht
        exact pow_lt_pow_left₀ this ht0 two_ne_zero
      nlinarith
    have hexp : (3 : ℝ) / 4 ≤ Real.exp (-(t ^ 2 / b2)) := by
      have := Real.add_one_le_exp (-(t ^ 2 / b2))
      linarith
    have hmono := Real.exp_le_exp.2 hE
    linarith

/-- `τ^{P'}(0,δ) > 0`. -/
lemma tauPs_zero_pos {D v ρ δ : ℝ} {n m : ℕ} (hD : 0 < D) (hv : 0 < v) (hρ : 0 < ρ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : 0 < tauPs D v ρ 0 δ n m := by
  have hs : 0 < sNM n m := StatFormal.Wave30tp.sNM_pos hn hm
  simp only [tauPs, ↓reduceIte]
  have hmem : (v * √(sNM n m) + D * √(sNM n m * Real.log (1 / δ) / 2)) ∈
      {t : ℝ | 0 ≤ t ∧ psiH D v ρ 1 (sNM n m) (cNM n m) t ≤ δ} :=
    ⟨by positivity, psiH_root_le hD hv.le hδ0 hδ1 hn hm⟩
  have hlow : v * √(sNM n m) / 2 ≤ sInf {t : ℝ | 0 ≤ t ∧ psiH D v ρ 1 (sNM n m) (cNM n m) t ≤ δ} := by
    refine le_csInf ⟨_, hmem⟩ fun t ht => ?_
    by_contra hlt
    push Not at hlt
    exact absurd ht.2 (not_le.2 (lt_psiH_of_small hv hρ hδ1 hn hm ht.1 hlt))
  exact lt_of_lt_of_le (by positivity) hlow

/-- `τ^{P'}(0,δ) ≤` the McDiarmid root. -/
lemma tauPs_zero_le {D v ρ δ : ℝ} {n m : ℕ} (hD : 0 < D) (hv : 0 ≤ v) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    tauPs D v ρ 0 δ n m ≤ v * √(sNM n m) + D * √(sNM n m * Real.log (1 / δ) / 2) := by
  have hs : 0 < sNM n m := StatFormal.Wave30tp.sNM_pos hn hm
  simp only [tauPs, ↓reduceIte]
  exact csInf_le ⟨0, fun t ht => ht.1⟩ ⟨by positivity, psiH_root_le hD hv hδ0 hδ1 hn hm⟩

/-- `τ^{cpl}_{P'}(0,δ) > 0` for `κ > 0`. -/
lemma tauCpl_zero_pos {κ D δ : ℝ} {n m : ℕ} (hκ : 0 < κ) (hD : 0 < D) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : 0 < tauCpl D κ 0 δ n m := by
  unfold tauCpl
  have hk2 : (0 : ℝ) < κ ^ 2 := by positivity
  have hbdd : BddAbove (range fun u : Ico (0 : ℝ) (κ ^ 2) =>
      tauPs D (√(κ ^ 2 - (u : ℝ))) (√(κ ^ 2 + (u : ℝ))) 0 δ n m) := by
    refine ⟨κ * √(sNM n m) + D * √(sNM n m * Real.log (1 / δ) / 2), ?_⟩
    rintro _ ⟨u, rfl⟩
    refine (tauPs_zero_le hD (Real.sqrt_nonneg _) hδ0 hδ1 hn hm).trans ?_
    have h1 : √(κ ^ 2 - (u : ℝ)) ≤ κ := Real.sqrt_le_iff.2 ⟨hκ.le, by linarith [u.2.1]⟩
    have := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (sNM n m))
    linarith
  refine lt_of_lt_of_le ?_ (le_ciSup hbdd ⟨0, le_rfl, hk2⟩)
  change 0 < tauPs D (√(κ ^ 2 - 0)) (√(κ ^ 2 + 0)) 0 δ n m
  rw [sub_zero, add_zero, Real.sqrt_sq hκ.le]
  exact tauPs_zero_pos hD hκ hκ hδ0 hδ1 hn hm

/-- `τ^A(0,δ) > 0` for `κ > 0`, `D ≥ 0`. -/
lemma tauA_zero_pos {κ D δ : ℝ} {n m : ℕ} (hκ : 0 < κ) (hD : 0 ≤ D) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    0 < StatFormal.Wave30tr.tauA κ D 0 δ n m := by
  have hs : 0 < sNM n m := StatFormal.Wave30tp.sNM_pos hn hm
  unfold StatFormal.Wave30tr.tauA
  rw [sub_zero, div_one, one_mul]
  have h1 : 0 < 2 * κ * √(sNM n m) := by positivity
  have h2 : 0 ≤ 2 * κ * (StatFormal.Wave30tr.ek n + StatFormal.Wave30tr.ek m) :=
    mul_nonneg (by positivity) (add_nonneg (StatFormal.Wave30tu.Instance.ek_nonneg n) (StatFormal.Wave30tu.Instance.ek_nonneg m))
  have h3 : 0 ≤ D * √(sNM n m * Real.log (1 / δ) / 2) := mul_nonneg hD (Real.sqrt_nonneg _)
  have : 2 * κ * √(sNM n m) + 2 * κ * (StatFormal.Wave30tr.ek n + StatFormal.Wave30tr.ek m) =
      2 * κ * √(sNM n m) + 2 * κ * (StatFormal.Wave30tr.ek n + StatFormal.Wave30tr.ek m) := rfl
  linarith

/-- `τ^P(0,δ) > 0` for `v > 0`, `D ≥ 0`. -/
lemma tauP_zero_pos {D v ρ δ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hv : 0 < v) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    0 < tauP D v ρ 0 δ n m := by
  have hs : 0 < sNM n m := StatFormal.Wave30tp.sNM_pos hn hm
  simp only [tauP, ↓reduceIte]
  have h1 : 0 < v * √(sNM n m) := by positivity
  have h3 : 0 ≤ D * √(sNM n m * Real.log (1 / δ) / 2) := mul_nonneg hD (Real.sqrt_nonneg _)
  linarith

/-- The constant `v = √min(κ², D²/2)` of the paper's `τ` is positive for `κ, D > 0`. -/
lemma v_pos {κ D : ℝ} (hκ : 0 < κ) (hD : 0 < D) : 0 < √(min (κ ^ 2) (D ^ 2 / 2)) :=
  Real.sqrt_pos.2 (lt_min (by positivity) (by positivity))

/-- The paper's `τ_{n,m}(0,δ) > 0` (general kernel). -/
theorem tauFull_zero_pos {κ D δ : ℝ} {n m : ℕ} (hκ : 0 < κ) (hD : 0 < D) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : 0 < StatFormal.Wave30tu.Full.tauFull κ D 0 δ n m := by
  unfold StatFormal.Wave30tu.Full.tauFull
  exact lt_min (tauA_zero_pos hκ hD.le hn hm)
    (lt_min (tauP_zero_pos hD.le (v_pos hκ hD) hn hm) (tauPs_zero_pos hD (v_pos hκ hD) hD hδ0 hδ1 hn hm))

/-- The paper's `τ_{n,m}(0,δ) > 0` (coupled form). -/
theorem tauV2Cpl_zero_pos {κ D δ : ℝ} {n m : ℕ} (hκ : 0 < κ) (hD : 0 < D) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : 0 < StatFormal.Wave31ta.tauV2Cpl κ D 0 δ n m := by
  unfold StatFormal.Wave31ta.tauV2Cpl
  exact lt_min (tauA_zero_pos hκ hD.le hn hm)
    (lt_min (tauP_zero_pos hD.le (v_pos hκ hD) hn hm) (tauCpl_zero_pos hκ hD hδ0 hδ1 hn hm))

/-! ### G7, the instances -/

theorem n_of_a_full : Claims.n_of_a_full := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ hφ hκ hD hκ0 hD0 hδ0 hδ1 htv0 htv1 N
  have hne : Nonempty 𝒳 := nonempty_of_isProbabilityMeasure P
  have hcont : ContinuousOn (Dpop φ P Q) (Icc 0 (StatFormal.Distances.tvDist P Q)) :=
    (StatFormal.Wave18b.continuity_cont 𝒳 H P Q φ κ hφ hκ).mono (fun α hα => ⟨hα.1, hα.2.trans_lt htv1⟩)
  have hzero : Dpop φ P Q (StatFormal.Distances.tvDist P Q) = 0 :=
    StatFormal.TrimmedMMD.ZeroSet.zero_of_tv_le 𝒳 H P Q φ κ _ hφ hκ htv0.le htv1 le_rfl
  exact n_of_a_generic (fun n a => StatFormal.Wave30tu.Full.tauFull κ D a δ n n) (Dpop φ P Q)
    (StatFormal.Distances.tvDist P Q) htv0 htv1
    (fun n hn => (StatFormal.Wave30tu.Full.tauFull_threshold 𝒳 H φ κ D δ n n hne hφ hκ hD hδ0 hδ1 hn hn).1.2.1)
    (fun n hn => tauFull_zero_pos hκ0 hD0 hδ0 hδ1 hn hn) hcont hzero N

theorem n_of_a_cpl : Claims.n_of_a_cpl := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ hφ hκ hD hk0 hdiag hκ0 hD0 hδ0 hδ1 htv0 htv1 N
  have hne : Nonempty 𝒳 := nonempty_of_isProbabilityMeasure P
  have hcont : ContinuousOn (Dpop φ P Q) (Icc 0 (StatFormal.Distances.tvDist P Q)) :=
    (StatFormal.Wave18b.continuity_cont 𝒳 H P Q φ κ hφ hκ).mono (fun α hα => ⟨hα.1, hα.2.trans_lt htv1⟩)
  have hzero : Dpop φ P Q (StatFormal.Distances.tvDist P Q) = 0 :=
    StatFormal.TrimmedMMD.ZeroSet.zero_of_tv_le 𝒳 H P Q φ κ _ hφ hκ htv0.le htv1 le_rfl
  exact n_of_a_generic (fun n a => StatFormal.Wave31ta.tauV2Cpl κ D a δ n n) (Dpop φ P Q)
    (StatFormal.Distances.tvDist P Q) htv0 htv1
    (fun n hn => (StatFormal.Wave31ta.tauV2Cpl_facts 𝒳 H φ κ D δ n n hne hφ hκ hD hk0 hdiag hδ0 hδ1 hn hn).1.2.1)
    (fun n hn => tauV2Cpl_zero_pos hκ0 hD0 hδ0 hδ1 hn hn) hcont hzero N

end StatFormal.Wave31tf
