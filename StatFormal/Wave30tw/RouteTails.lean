import StatFormal.Wave30tw.Statements
import StatFormal.Wave30ts.Proofs
import StatFormal.Wave30tu.Proofs

/-!
# Wave 30tw — route: the tail bounds (untrusted proof material)

* Strictness: McDiarmid's term is strictly decreasing in `t` from every point where it is `< 1`; Pinelis' term (for `a, b² > 0`,
  via its Bennett characterisation `inf_λ`) likewise; hence `Ψ_H`. `Ψ_R`: the product of two-point bounds is `≥ 1`, so every `λ`
  with `e^{−λt}∏ < c < 1` has `λ ≥ −log c / t`, which gives `Ψ_R(t') ≤ e^{−λ₀(t'−t)} Ψ_R(t)` from every `t` with `0 < Ψ_R(t) < 1`.
* Continuity: `Ψ_H` from its formula (junk cases `a = 0`, `b² = 0`, `D = 0` are constants or `2e^{t/a}`); `Ψ_R` in `β > 1` from
  `twoPt(β',l) ≤ ((1−1/β')/(1−1/β)) twoPt(β,l)` (`1 < β ≤ β'`, `l ≥ 0`) and monotonicity in `β`.
* The repair term jumps: `Ψ_R(1;β,(n)) ≥ (1−β⁻¹)^n`, `Ψ_R(t;β,(n)) = 0` for `t > 1`.
-/

noncomputable section
open MeasureTheory Real Set Filter Topology

namespace StatFormal.Wave30tw

open StatFormal.Wave30ts StatFormal.Wave30tp

/-! ### Strictness -/

theorem psiMcD_strict {D v β s' t t' : ℝ} (hs : 0 < s') (htt : t < t') (h1 : psiMcD D v β s' t < 1) :
    psiMcD D v β s' t' < psiMcD D v β s' t := by
  unfold psiMcD at h1 ⊢
  set μ := √(β * v ^ 2 * s')
  set d := β ^ 2 * D ^ 2 * s'
  have hd0 : 0 ≤ d := by positivity
  rw [Real.exp_lt_one_iff] at h1
  have hd : 0 < d := by
    rcases hd0.lt_or_eq with h | h
    · exact h
    · rw [← h, div_zero] at h1; exact absurd h1 (lt_irrefl 0)
  have htμ : 0 < t - μ := by
    by_contra hc
    push Not at hc
    rw [max_eq_right hc] at h1
    simp at h1
  rw [max_eq_left htμ.le, max_eq_left (by linarith : 0 ≤ t' - μ)]
  apply exp_lt_exp.2
  rw [div_lt_div_iff_of_pos_right hd]
  nlinarith

theorem psiPin_strict {a b2 t t' : ℝ} (ha : 0 < a) (hb : 0 < b2) (ht : 0 ≤ t) (htt : t < t')
    (h1 : psiPin a b2 t < 1) : psiPin a b2 t' < psiPin a b2 t := by
  have ht0 : 0 < t := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · subst h
      exfalso
      simp [psiPin] at h1
  obtain ⟨e1, -⟩ := pinE_eq_le ha hb ht
  obtain ⟨e2, l2⟩ := pinE_eq_le ha hb (ht.trans htt.le)
  unfold psiPin
  rw [e1, e2]
  have hl : 0 < lstar a b2 t := by
    unfold lstar
    have : 0 < t * a / b2 := by positivity
    exact div_pos (Real.log_pos (by linarith)) ha
  have h2 := l2 (lstar a b2 t)
  have key : bennG a b2 t' (lstar a b2 t) = bennG a b2 t (lstar a b2 t) - lstar a b2 t * (t' - t) := by
    unfold bennG; ring
  have h3 : bennG a b2 t' (lstar a b2 t') < bennG a b2 t (lstar a b2 t) := by
    have := mul_pos hl (sub_pos.2 htt)
    linarith
  have := exp_lt_exp.2 h3
  linarith

theorem psiH_strict {D v ρbar β s' c' t t' : ℝ} (hρ : 0 ≤ ρbar) (hβ : 0 < β) (hs : 0 < s') (hc : 0 < c')
    (ht : 0 ≤ t) (htt : t < t') (h1 : psiH D v ρbar β s' c' t < 1) :
    psiH D v ρbar β s' c' t' < psiH D v ρbar β s' c' t := by
  unfold psiH at h1 ⊢
  rcases le_total (psiMcD D v β s' t) (psiPin (β * ρbar * c') (β * v ^ 2 * s') t) with hle | hle
  · rw [min_eq_left hle] at h1 ⊢
    exact (min_le_left _ _).trans_lt (psiMcD_strict hs htt h1)
  · rw [min_eq_right hle] at h1 ⊢
    have ha0 : 0 ≤ β * ρbar * c' := by positivity
    have hb0 : 0 ≤ β * v ^ 2 * s' := by positivity
    have ha : 0 < β * ρbar * c' := by
      rcases ha0.lt_or_eq with h | h
      · exact h
      · exact absurd h1 (not_lt.2 (one_le_psiPin_of_junk ha0 ht (Or.inl h.symm)))
    have hb : 0 < β * v ^ 2 * s' := by
      rcases hb0.lt_or_eq with h | h
      · exact h
      · exact absurd h1 (not_lt.2 (one_le_psiPin_of_junk ha0 ht (Or.inr h.symm)))
    exact (min_le_right _ _).trans_lt (psiPin_strict ha hb ht htt h1)

theorem one_le_twoPt {β : ℝ} (hβ : 1 ≤ β) (l : ℝ) : 1 ≤ twoPt β l := by
  unfold twoPt
  have hβ0 : 0 < β := by linarith
  have hb : 0 ≤ β⁻¹ := by positivity
  have hb1 : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hβ
  have h1 := add_one_le_exp (l * (1 - β))
  have h2 := add_one_le_exp l
  have e : β⁻¹ * (l * (1 - β) + 1) + (1 - β⁻¹) * (l + 1) = 1 := by field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left h1 hb, mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 - β⁻¹)]

theorem one_le_prodK {β : ℝ} (hβ : 1 ≤ β) (l : ℝ) (K : List ℕ) :
    1 ≤ (K.map fun k : ℕ => twoPt β (l / (k : ℝ)) ^ k).prod := by
  induction K with
  | nil => simp
  | cons k K ih =>
    simp only [List.map_cons, List.prod_cons]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (one_le_twoPt hβ _)) ih

theorem exp_le_psiRlam {β : ℝ} (hβ : 1 ≤ β) (l t : ℝ) (K : List ℕ) : exp (-(l * t)) ≤ psiRlam β l t K :=
  le_mul_of_one_le_right (exp_pos _).le (one_le_prodK hβ l K)

theorem psiR_strict {β t t' : ℝ} {K : List ℕ} (hβ : 1 ≤ β) (htt : t < t') (h0 : 0 < psiR β t K)
    (h1 : psiR β t K < 1) : psiR β t' K < psiR β t K := by
  set q := psiR β t K with hq
  set c := (1 + q) / 2 with hc
  have hqc : q < c := by rw [hc]; linarith
  have hc1 : c < 1 := by rw [hc]; linarith
  have hc0 : 0 < c := by linarith
  have hlogc : log c < 0 := log_neg hc0 hc1
  obtain ⟨l1, hl1, hl1c⟩ := exists_psiRlam_lt hβ t K hqc
  have ht0 : 0 < t := by
    have h := (exp_le_psiRlam hβ l1 t K).trans_lt hl1c
    have h' : -(l1 * t) < log c := (lt_log_iff_exp_lt hc0).2 h
    by_contra hneg
    push Not at hneg
    have : l1 * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl1.le hneg
    linarith
  set l0 := -log c / t with hl0
  have hl0p : 0 < l0 := div_pos (by linarith) ht0
  set θ := exp (-(l0 * (t' - t))) with hθ
  have hθ0 : 0 < θ := exp_pos _
  have hθ1 : θ < 1 := by
    rw [hθ, Real.exp_lt_one_iff]
    have := mul_pos hl0p (sub_pos.2 htt)
    linarith
  have key : ∀ l, 0 < l → psiRlam β l t K < c → psiR β t' K ≤ θ * psiRlam β l t K := by
    intro l hl hlc
    have h := (exp_le_psiRlam hβ l t K).trans_lt hlc
    have hlt : -(l * t) < log c := (lt_log_iff_exp_lt hc0).2 h
    have hll : l0 ≤ l := by
      rw [hl0, div_le_iff₀ ht0]
      linarith
    refine (psiR_le hβ t' K hl).trans ?_
    unfold psiRlam
    have e : exp (-(l * t')) = exp (-(l * (t' - t))) * exp (-(l * t)) := by
      rw [← exp_add]; ring_nf
    rw [e, mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (exp_pos _).le (prodK_nonneg hβ l K))
    apply exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hll (sub_pos.2 htt).le
    linarith
  have hqθ : q < q / θ := by
    rw [lt_div_iff₀ hθ0]
    nlinarith
  set w := (q + min c (q / θ)) / 2 with hw
  have hmin := lt_min hqc hqθ
  have hqw : q < w := by rw [hw]; linarith
  have hwc : w ≤ c := by
    have : w < min c (q / θ) := by rw [hw]; linarith
    exact (this.trans_le (min_le_left _ _)).le
  have hwθ : θ * w < q := by
    have : w < q / θ := by
      have : w < min c (q / θ) := by rw [hw]; linarith
      exact this.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ hθ0] at this
    linarith
  obtain ⟨l, hl, hlw⟩ := exists_psiRlam_lt hβ t K hqw
  calc psiR β t' K ≤ θ * psiRlam β l t K := key l hl (hlw.trans_le hwc)
    _ ≤ θ * w := mul_le_mul_of_nonneg_left hlw.le hθ0.le
    _ < q := hwθ

/-! ### Continuity of `Ψ_R` in `β` -/

theorem twoPt_le_mul {β β' l : ℝ} (hβ : 1 < β) (hββ : β ≤ β') (hl : 0 ≤ l) :
    twoPt β' l ≤ (1 - β'⁻¹) / (1 - β⁻¹) * twoPt β l := by
  have hβ0 : 0 < β := by linarith
  have hg : 0 < 1 - β⁻¹ := by have := inv_lt_one_of_one_lt₀ hβ; linarith
  have hinv : β'⁻¹ ≤ β⁻¹ := inv_anti₀ hβ0 hββ
  have hr : 1 ≤ (1 - β'⁻¹) / (1 - β⁻¹) := by rw [le_div_iff₀ hg]; linarith
  unfold twoPt
  have he : exp (l * (1 - β')) ≤ exp (l * (1 - β)) := exp_le_exp.2 (by nlinarith)
  have h1 : β'⁻¹ * exp (l * (1 - β')) ≤ β⁻¹ * exp (l * (1 - β)) :=
    mul_le_mul hinv he (exp_pos _).le (by positivity)
  have h2 : β⁻¹ * exp (l * (1 - β)) ≤ (1 - β'⁻¹) / (1 - β⁻¹) * (β⁻¹ * exp (l * (1 - β))) :=
    le_mul_of_one_le_left (by positivity) hr
  have h3 : (1 - β'⁻¹) * exp l = (1 - β'⁻¹) / (1 - β⁻¹) * ((1 - β⁻¹) * exp l) := by
    rw [← mul_assoc, div_mul_cancel₀ _ hg.ne']
  rw [mul_add]
  linarith

theorem prodK_le_mul {β β' l r : ℝ} (hβ : 1 ≤ β) (hββ : β ≤ β') (hr : 0 ≤ r) (hl : 0 ≤ l)
    (h : ∀ x, 0 ≤ x → twoPt β' x ≤ r * twoPt β x) (K : List ℕ) :
    (K.map fun k : ℕ => twoPt β' (l / (k : ℝ)) ^ k).prod ≤
      r ^ K.sum * (K.map fun k : ℕ => twoPt β (l / (k : ℝ)) ^ k).prod := by
  induction K with
  | nil => simp
  | cons k K ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add]
    have hk : twoPt β' (l / (k : ℝ)) ^ k ≤ r ^ k * twoPt β (l / (k : ℝ)) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (twoPt_nonneg (hβ.trans hββ) _) (h _ (div_nonneg hl (Nat.cast_nonneg k))) k
    calc twoPt β' (l / (k : ℝ)) ^ k * (K.map fun k : ℕ => twoPt β' (l / (k : ℝ)) ^ k).prod
        ≤ (r ^ k * twoPt β (l / (k : ℝ)) ^ k) * (r ^ K.sum * (K.map fun k : ℕ => twoPt β (l / (k : ℝ)) ^ k).prod) :=
          mul_le_mul hk ih (prodK_nonneg (hβ.trans hββ) l K)
            (mul_nonneg (pow_nonneg hr _) (pow_nonneg (twoPt_nonneg hβ _) _))
      _ = r ^ k * r ^ K.sum * (twoPt β (l / (k : ℝ)) ^ k * (K.map fun k : ℕ => twoPt β (l / (k : ℝ)) ^ k).prod) := by
          ring

theorem psiR_le_mul {β β' t : ℝ} (hβ : 1 < β) (hββ : β ≤ β') (K : List ℕ) :
    psiR β' t K ≤ ((1 - β'⁻¹) / (1 - β⁻¹)) ^ K.sum * psiR β t K := by
  have hβ0 : 0 < β := by linarith
  have hg : 0 < 1 - β⁻¹ := by have := inv_lt_one_of_one_lt₀ hβ; linarith
  have hinv : β'⁻¹ ≤ β⁻¹ := inv_anti₀ hβ0 hββ
  set r := (1 - β'⁻¹) / (1 - β⁻¹) with hr
  have hr0 : 0 < r := div_pos (by linarith) hg
  have hC : 0 < r ^ K.sum := pow_pos hr0 _
  have : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, mem_Ioi.2 one_pos⟩⟩
  have h : psiR β' t K / r ^ K.sum ≤ psiR β t K := by
    refine le_ciInf fun l => ?_
    rw [div_le_iff₀ hC]
    calc psiR β' t K ≤ psiRlam β' l t K := psiR_le (by linarith) t K l.2
      _ ≤ exp (-((l : ℝ) * t)) * (r ^ K.sum * (K.map fun k : ℕ => twoPt β ((l : ℝ) / (k : ℝ)) ^ k).prod) :=
          mul_le_mul_of_nonneg_left (prodK_le_mul hβ.le hββ hr0.le l.2.le
            (fun x hx => twoPt_le_mul hβ hββ hx) K) (exp_pos _).le
      _ = psiRlam β l t K * r ^ K.sum := by unfold psiRlam; ring
  rwa [div_le_iff₀ hC, mul_comm] at h

theorem psiR_continuousAt {β0 : ℝ} (t : ℝ) (K : List ℕ) (hβ0 : 1 < β0) :
    ContinuousAt (fun β => psiR β t K) β0 := by
  set g : ℝ → ℝ := fun β => 1 - β⁻¹ with hg
  have hg0 : 0 < g β0 := by simp only [hg]; have := inv_lt_one_of_one_lt₀ hβ0; linarith
  have hgc : ContinuousAt g β0 := continuousAt_const.sub (continuousAt_inv₀ (by linarith))
  set N := K.sum
  set p0 := psiR β0 t K with hp0
  have hp0n : 0 ≤ p0 := psiR_nonneg hβ0.le t K
  set U : ℝ → ℝ := fun β => max 1 (g β / g β0) ^ N * p0 with hU
  set L : ℝ → ℝ := fun β => p0 / max 1 (g β0 / g β) ^ N with hL
  have hUc : ContinuousAt U β0 :=
    ((continuousAt_const.max (hgc.div_const _)).pow N).mul continuousAt_const
  have hLc : ContinuousAt L β0 :=
    continuousAt_const.div ((continuousAt_const.max (continuousAt_const.div hgc hg0.ne')).pow N)
      (pow_ne_zero _ (by positivity))
  have hU0 : U β0 = p0 := by simp only [hU, div_self hg0.ne', max_self, one_pow, one_mul]
  have hL0 : L β0 = p0 := by simp only [hL, div_self hg0.ne', max_self, one_pow, div_one]
  have hev : ∀ᶠ β in 𝓝 β0, 1 < β := Ioi_mem_nhds hβ0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hL0 ▸ hLc.tendsto) (hU0 ▸ hUc.tendsto) ?_ ?_
  · filter_upwards [hev] with β hβ
    have hgβ : 0 < g β := by simp only [hg]; have := inv_lt_one_of_one_lt₀ hβ; linarith
    have hM : 1 ≤ max 1 (g β0 / g β) ^ N := one_le_pow₀ (le_max_left _ _)
    simp only [hL]
    rw [div_le_iff₀ (by positivity)]
    rcases le_total β β0 with h | h
    · calc p0 ≤ (g β0 / g β) ^ N * psiR β t K := psiR_le_mul hβ h K
        _ ≤ max 1 (g β0 / g β) ^ N * psiR β t K :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (div_nonneg hg0.le hgβ.le) (le_max_right _ _) N)
              (psiR_nonneg hβ.le t K)
        _ = psiR β t K * max 1 (g β0 / g β) ^ N := mul_comm _ _
    · calc p0 ≤ psiR β t K := psiR_mono_beta hβ0.le h t K
        _ ≤ psiR β t K * max 1 (g β0 / g β) ^ N := le_mul_of_one_le_right (psiR_nonneg hβ.le t K) hM
  · filter_upwards [hev] with β hβ
    have hgβ : 0 < g β := by simp only [hg]; have := inv_lt_one_of_one_lt₀ hβ; linarith
    have hM : 1 ≤ max 1 (g β / g β0) ^ N := one_le_pow₀ (le_max_left _ _)
    simp only [hU]
    rcases le_total β β0 with h | h
    · calc psiR β t K ≤ p0 := psiR_mono_beta hβ.le h t K
        _ ≤ max 1 (g β / g β0) ^ N * p0 := le_mul_of_one_le_left hp0n hM
    · calc psiR β t K ≤ (g β / g β0) ^ N * p0 := psiR_le_mul hβ0 h K
        _ ≤ max 1 (g β / g β0) ^ N * p0 :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (div_nonneg hgβ.le hg0.le) (le_max_right _ _) N) hp0n

/-! ### Continuity of `Ψ_H` -/

section Cont

variable {X : Type*} [TopologicalSpace X]

theorem psiMcD_continuousAt {D s' : ℝ} {B V T : X → ℝ} {x0 : X} (hB : ContinuousAt B x0)
    (hV : ContinuousAt V x0) (hT : ContinuousAt T x0) (hB0 : B x0 ≠ 0) (hs : s' ≠ 0) :
    ContinuousAt (fun x => psiMcD D (V x) (B x) s' (T x)) x0 := by
  by_cases hD : D = 0
  · subst hD
    simp only [psiMcD_D_zero]
    exact continuousAt_const
  · unfold psiMcD
    refine ContinuousAt.rexp (ContinuousAt.div ?_ ?_ ?_)
    · exact continuousAt_const.mul
        (((hT.sub ((hB.mul (hV.pow 2)).mul continuousAt_const).sqrt).max continuousAt_const).pow 2)
    · exact ((hB.pow 2).mul continuousAt_const).mul continuousAt_const
    · exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hB0) (pow_ne_zero 2 hD)) hs

theorem psiPin_continuousAt {A B2 T : X → ℝ} {x0 : X} (hA : ContinuousAt A x0) (hB : ContinuousAt B2 x0)
    (hT : ContinuousAt T x0) (hA0 : 0 < A x0) (hB0 : 0 < B2 x0) (hT0 : 0 ≤ T x0) :
    ContinuousAt (fun x => psiPin (A x) (B2 x) (T x)) x0 := by
  unfold psiPin
  have hlog : 1 + T x0 * A x0 / B2 x0 ≠ 0 := by
    have : 0 ≤ T x0 * A x0 / B2 x0 := by positivity
    linarith
  refine continuousAt_const.mul (ContinuousAt.rexp ?_)
  refine (hT.div hA hA0.ne').sub (((hT.div hA hA0.ne').add (hB.div (hA.pow 2) (pow_ne_zero 2 hA0.ne'))).mul ?_)
  exact (continuousAt_const.add ((hT.mul hA).div hB hB0.ne')).log hlog

/-- `Ψ_H` at constant `v, ρ̄` (any junk case) is continuous in `(β, t)` at `β > 0`, `t ≥ 0`. -/
theorem psiH_continuousAt_const {D v ρbar s' c' : ℝ} {B T : X → ℝ} {x0 : X} (hB : ContinuousAt B x0)
    (hT : ContinuousAt T x0) (hB0 : 0 < B x0) (hT0 : 0 ≤ T x0) (hρ : 0 ≤ ρbar) (hs : 0 < s') (hc : 0 < c') :
    ContinuousAt (fun x => psiH D v ρbar (B x) s' c' (T x)) x0 := by
  unfold psiH
  refine (psiMcD_continuousAt hB continuousAt_const hT hB0.ne' hs.ne').min ?_
  rcases hρ.eq_or_lt with hρ0 | hρ0
  · subst hρ0
    simp only [mul_zero, zero_mul, psiPin_zero_a]
    exact continuousAt_const
  by_cases hv : v = 0
  · subst hv
    have e : ∀ x, B x * (0 : ℝ) ^ 2 * s' = 0 := fun x => by ring
    simp only [e, psiPin_zero_b]
    exact continuousAt_const.mul ((hT.div ((hB.mul continuousAt_const).mul continuousAt_const)
      (mul_pos (mul_pos hB0 hρ0) hc).ne').rexp)
  · have hv2 : 0 < v ^ 2 := by positivity
    exact psiPin_continuousAt ((hB.mul continuousAt_const).mul continuousAt_const)
      ((hB.mul continuousAt_const).mul continuousAt_const) hT (mul_pos (mul_pos hB0 hρ0) hc)
      (mul_pos (mul_pos hB0 hv2) hs) hT0

/-- `Ψ_H` with varying positive constants `v, ρ̄` is continuous. -/
theorem psiH_continuousAt_pos {D s' c' : ℝ} {B V R T : X → ℝ} {x0 : X} (hB : ContinuousAt B x0)
    (hV : ContinuousAt V x0) (hR : ContinuousAt R x0) (hT : ContinuousAt T x0) (hB0 : 0 < B x0) (hV0 : V x0 ≠ 0)
    (hR0 : 0 < R x0) (hT0 : 0 ≤ T x0) (hs : 0 < s') (hc : 0 < c') :
    ContinuousAt (fun x => psiH D (V x) (R x) (B x) s' c' (T x)) x0 := by
  unfold psiH
  have hv2 : 0 < V x0 ^ 2 := by positivity
  exact (psiMcD_continuousAt hB hV hT hB0.ne' hs.ne').min
    (psiPin_continuousAt ((hB.mul hR).mul continuousAt_const) ((hB.mul (hV.pow 2)).mul continuousAt_const) hT
      (mul_pos (mul_pos hB0 hR0) hc) (mul_pos (mul_pos hB0 hv2) hs) hT0)

end Cont

/-! ### Frozen claims on the tails -/

theorem tails_continuous : Claims.tails_continuous := by
  refine ⟨fun D v ρbar s' c' hρ hs hc p hp => ?_, fun t K β hβ => (psiR_continuousAt t K hβ).continuousWithinAt⟩
  exact (psiH_continuousAt_const continuousAt_fst continuousAt_snd hp.1 hp.2 hρ hs hc).continuousWithinAt

theorem tails_strict : Claims.tails_strict :=
  ⟨fun _ _ _ _ _ _ _ _ hρ hβ hs hc ht htt h1 => psiH_strict hρ hβ hs hc ht htt h1,
    fun _ _ _ _ hβ htt h0 h1 => psiR_strict hβ htt h0 h1⟩

theorem psiR_single_gt_one_eq_zero {β t : ℝ} {n : ℕ} (hβ : 1 ≤ β) (ht : 1 < t) : psiR β t [n] = 0 := by
  refine le_antisymm ?_ (psiR_nonneg hβ t [n])
  have hb : ∀ l : ℝ, 0 < l → psiR β t [n] ≤ exp (-(l * (t - 1))) := fun l hl => by
    refine (psiR_le hβ t [n] hl).trans ?_
    unfold psiRlam
    calc exp (-(l * t)) * ([n].map fun k : ℕ => twoPt β (l / (k : ℝ)) ^ k).prod
        ≤ exp (-(l * t)) * exp (l * ([n] : List ℕ).length) :=
          mul_le_mul_of_nonneg_left (prodK_le hβ hl.le [n]) (exp_pos _).le
      _ = exp (-(l * (t - 1))) := by rw [← exp_add]; congr 1; simp; ring
  have hlim : Tendsto (fun l : ℝ => exp (-(l * (t - 1)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const (by linarith))
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with l hl
  exact hb l hl

theorem repair_tail_jump : Claims.repair_tail_jump := by
  intro β n hβ hn
  have hβ0 : 0 < β := by linarith
  have hg : 0 < 1 - β⁻¹ := by have := inv_lt_one_of_one_lt₀ hβ; linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < (1 - β⁻¹) ^ n := pow_pos hg n
  have hlow : (1 - β⁻¹) ^ n ≤ psiR β 1 [n] := by
    have : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, mem_Ioi.2 one_pos⟩⟩
    refine le_ciInf fun l => ?_
    unfold psiRlam
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have h1 : (1 - β⁻¹) * exp ((l : ℝ) / n) ≤ twoPt β ((l : ℝ) / n) := by
      unfold twoPt
      have : 0 ≤ β⁻¹ * exp ((l : ℝ) / n * (1 - β)) := by positivity
      linarith
    have h2 : ((1 - β⁻¹) * exp ((l : ℝ) / n)) ^ n ≤ twoPt β ((l : ℝ) / n) ^ n :=
      pow_le_pow_left₀ (by positivity) h1 n
    rw [mul_pow, ← exp_nat_mul, mul_div_cancel₀ _ hnR.ne'] at h2
    calc (1 - β⁻¹) ^ n = exp (-(l : ℝ)) * ((1 - β⁻¹) ^ n * exp (l : ℝ)) := by
          rw [mul_left_comm, ← exp_add, neg_add_cancel, exp_zero, mul_one]
      _ ≤ exp (-(l : ℝ)) * twoPt β ((l : ℝ) / n) ^ n := mul_le_mul_of_nonneg_left h2 (exp_pos _).le
  have hup : psiR β 1 [n] < 1 := by
    refine (psiR_le hβ.le 1 [n] hnR).trans_lt ?_
    unfold psiRlam
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_self hnR.ne']
    have e : exp (-(n : ℝ)) * twoPt β 1 ^ n = (β⁻¹ * exp (-β) + (1 - β⁻¹)) ^ n := by
      rw [show -(n : ℝ) = n * (-1) by ring, exp_nat_mul, ← mul_pow]
      congr 1
      unfold twoPt
      have e1 : exp (-1) * (β⁻¹ * exp (1 * (1 - β))) = β⁻¹ * exp (-β) := by
        rw [mul_left_comm, ← exp_add]; congr 2; ring
      have e2 : exp (-1) * ((1 - β⁻¹) * exp 1) = 1 - β⁻¹ := by
        rw [mul_left_comm, ← exp_add]; simp
      rw [mul_add, e1, e2]
    rw [e]
    have hb : 0 < β⁻¹ := by positivity
    have hexp : exp (-β) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    exact pow_lt_one₀ (by positivity) (by nlinarith) (by omega)
  have hzero : ∀ t, 1 < t → psiR β t [n] = 0 := fun t ht => psiR_single_gt_one_eq_zero hβ.le ht
  refine ⟨hp, hlow, hup, hzero, fun hc => ?_, fun hs => ?_⟩
  · have h1 : Tendsto (fun t => psiR β t [n]) (𝓝[>] 1) (𝓝 (psiR β 1 [n])) := hc.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t => psiR β t [n]) (𝓝[>] 1) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hzero t ht).symm)
    have := tendsto_nhds_unique h1 h2
    linarith
  · have h2 : (2 : ℝ) ∈ {t | psiR β t [n] < 1} := by
      simp only [mem_ofPred_eq, hzero 2 (by norm_num)]; norm_num
    have h3 : (3 : ℝ) ∈ {t | psiR β t [n] < 1} := by
      simp only [mem_ofPred_eq, hzero 3 (by norm_num)]; norm_num
    have := hs h2 h3 (by norm_num)
    simp only [hzero 2 (by norm_num), hzero 3 (by norm_num)] at this
    exact lt_irrefl 0 this

end StatFormal.Wave30tw
