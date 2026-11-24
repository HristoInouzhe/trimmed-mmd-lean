import StatFormal.Wave30ts.Statements
import StatFormal.Lib.Concentration.Pinelis

/-!
# Route: the tail functions of NOTE §3.3 (deterministic facts)

Untrusted proof material.

* Pinelis' term: junk values (`a = 0` or `b² = 0`) are `≥ 1`; for `a, b² > 0` its exponent is the minimum over `λ` of the
  Bennett exponent `−λt + (b²/a²)(e^{λa} − 1 − λa)` (tangent line of `exp`), hence it is nondecreasing in `a` and `b²` and
  nonincreasing in `t`, and it tends to `0`.
* McDiarmid's term: `≤ 1`, nondecreasing in `β` and `v`, nonincreasing in `t`, explicit `e^{−L}` bound.
* `Ψ_H`: the claims `tails_mono_beta` (first part), `tails_mono_const`, `tails_antitone_t` (first part).
* The two-point bound (convexity of `exp`), `Ψ_R` at fixed `λ` and its infimum.
-/

noncomputable section
open MeasureTheory Real Set Filter Topology

namespace StatFormal.Wave30ts

open StatFormal.Wave30tp

/-! ### Pinelis' term -/

theorem psiPin_zero_a (b2 t : ℝ) : psiPin 0 b2 t = 2 := by simp [psiPin]

theorem psiPin_zero_b (a t : ℝ) : psiPin a 0 t = 2 * exp (t / a) := by simp [psiPin]

theorem psiPin_nonneg (a b2 t : ℝ) : 0 ≤ psiPin a b2 t := by unfold psiPin; positivity

theorem one_le_psiPin_of_junk {a b2 t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (h : a = 0 ∨ b2 = 0) :
    1 ≤ psiPin a b2 t := by
  rcases h with h | h
  · subst h; rw [psiPin_zero_a]; norm_num
  · subst h; rw [psiPin_zero_b]
    have := Real.one_le_exp (div_nonneg ht ha)
    linarith

/-- The Bennett exponent at `λ`. -/
def bennG (a b2 t l : ℝ) : ℝ := -(l * t) + b2 / a ^ 2 * (exp (l * a) - 1 - l * a)

/-- The optimal `λ`. -/
def lstar (a b2 t : ℝ) : ℝ := log (1 + t * a / b2) / a

theorem lstar_nonneg {a b2 t : ℝ} (ha : 0 < a) (hb : 0 < b2) (ht : 0 ≤ t) : 0 ≤ lstar a b2 t :=
  div_nonneg (Real.log_nonneg (by have : 0 ≤ t * a / b2 := by positivity
                                  linarith)) ha.le

/-- The exponent of Pinelis' term is the Bennett exponent at `λ*`, and every `λ` gives a larger value. -/
theorem pinE_eq_le {a b2 t : ℝ} (ha : 0 < a) (hb : 0 < b2) (ht : 0 ≤ t) :
    t / a - (t / a + b2 / a ^ 2) * log (1 + t * a / b2) = bennG a b2 t (lstar a b2 t) ∧
      ∀ l, bennG a b2 t (lstar a b2 t) ≤ bennG a b2 t l := by
  have h1 : 0 < 1 + t * a / b2 := by have : 0 ≤ t * a / b2 := by positivity
                                     linarith
  have hla : lstar a b2 t * a = log (1 + t * a / b2) := by unfold lstar; field_simp
  have hexp : exp (lstar a b2 t * a) = 1 + t * a / b2 := by rw [hla, exp_log h1]
  refine ⟨?_, fun l => ?_⟩
  · unfold bennG
    rw [hexp, hla]
    unfold lstar
    field_simp
    ring
  · unfold bennG
    set ls := lstar a b2 t
    have htan : exp (ls * a) * (1 + (l - ls) * a) ≤ exp (l * a) := by
      have h2 := add_one_le_exp ((l - ls) * a)
      have e : exp (l * a) = exp (ls * a) * exp ((l - ls) * a) := by rw [← exp_add]; ring_nf
      rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le
    rw [hexp] at htan ⊢
    have hc : 0 ≤ b2 / a ^ 2 := by positivity
    have key : b2 / a ^ 2 * ((1 + t * a / b2) * (1 + (l - ls) * a) - (1 + t * a / b2) - (l - ls) * a) =
        (l - ls) * t := by field_simp; ring
    have := mul_le_mul_of_nonneg_left htan hc
    nlinarith

theorem bennG_mono {a a' b2 b2' t l : ℝ} (ha : 0 < a) (haa : a ≤ a') (hb : 0 ≤ b2) (hbb : b2 ≤ b2')
    (hl : 0 ≤ l) : bennG a b2 t l ≤ bennG a' b2' t l := by
  unfold bennG
  have ha' : 0 < a' := ha.trans_le haa
  have h1 := StatFormal.Pinelis.exp_sub_one_sub_le_sq hl ha.le haa ha'
  have hφ' : 0 ≤ exp (l * a') - 1 - l * a' := StatFormal.Pinelis.exp_sub_one_sub_nonneg _
  have h2 : (exp (l * a) - 1 - l * a) / a ^ 2 ≤ (exp (l * a') - 1 - l * a') / a' ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg a')
    calc (exp (l * a) - 1 - l * a) * a' ^ 2 ≤ a ^ 2 / a' ^ 2 * (exp (l * a') - 1 - l * a') * a' ^ 2 := this
      _ = (exp (l * a') - 1 - l * a') * a ^ 2 := by field_simp
  have h3 : b2 / a ^ 2 * (exp (l * a) - 1 - l * a) ≤ b2' / a' ^ 2 * (exp (l * a') - 1 - l * a') := by
    calc b2 / a ^ 2 * (exp (l * a) - 1 - l * a) = b2 * ((exp (l * a) - 1 - l * a) / a ^ 2) := by ring
      _ ≤ b2' * ((exp (l * a') - 1 - l * a') / a' ^ 2) :=
          mul_le_mul hbb h2 (div_nonneg (StatFormal.Pinelis.exp_sub_one_sub_nonneg _) (by positivity))
            (hb.trans hbb)
      _ = b2' / a' ^ 2 * (exp (l * a') - 1 - l * a') := by ring
  linarith

/-- Pinelis' term is nondecreasing in `a` and `b²`. -/
theorem psiPin_mono {a a' b2 b2' t : ℝ} (ha : 0 < a) (haa : a ≤ a') (hb : 0 < b2) (hbb : b2 ≤ b2')
    (ht : 0 ≤ t) : psiPin a b2 t ≤ psiPin a' b2' t := by
  have ha' : 0 < a' := ha.trans_le haa
  have hb' : 0 < b2' := hb.trans_le hbb
  obtain ⟨e1, l1⟩ := pinE_eq_le ha hb ht
  obtain ⟨e2, -⟩ := pinE_eq_le ha' hb' ht
  unfold psiPin
  rw [e1, e2]
  gcongr
  exact (l1 _).trans (bennG_mono ha haa hb.le hbb (lstar_nonneg ha' hb' ht))

/-- Pinelis' term is nonincreasing in `t ≥ 0`. -/
theorem psiPin_antitone {a b2 t t' : ℝ} (ha : 0 < a) (hb : 0 < b2) (ht : 0 ≤ t) (htt : t ≤ t') :
    psiPin a b2 t' ≤ psiPin a b2 t := by
  obtain ⟨e1, -⟩ := pinE_eq_le ha hb ht
  obtain ⟨e2, l2⟩ := pinE_eq_le ha hb (ht.trans htt)
  unfold psiPin
  rw [e1, e2]
  gcongr
  refine (l2 (lstar a b2 t)).trans ?_
  unfold bennG
  have := lstar_nonneg ha hb ht
  nlinarith

/-- Pinelis' term tends to `0`. -/
theorem psiPin_small {a b2 ε : ℝ} (ha : 0 < a) (hb : 0 < b2) (hε : 0 < ε) :
    ∃ T, 0 ≤ T ∧ psiPin a b2 T ≤ ε := by
  set T := max (b2 * (exp 2 - 1) / a) (a * |log (2 / ε)|) with hT
  have hT0 : 0 ≤ T := le_max_of_le_right (mul_nonneg ha.le (abs_nonneg _))
  refine ⟨T, hT0, ?_⟩
  have h1 : exp 2 ≤ 1 + T * a / b2 := by
    have : b2 * (exp 2 - 1) / a ≤ T := le_max_left _ _
    rw [div_le_iff₀ ha] at this
    have : exp 2 - 1 ≤ T * a / b2 := by rw [le_div_iff₀ hb]; linarith
    linarith
  have hlog : 2 ≤ log (1 + T * a / b2) := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (exp_pos _) h1
  have hTa : |log (2 / ε)| ≤ T / a := by
    rw [le_div_iff₀ ha, mul_comm]; exact le_max_right _ _
  have hexpo : T / a - (T / a + b2 / a ^ 2) * log (1 + T * a / b2) ≤ -log (2 / ε) := by
    have hb2 : 0 ≤ b2 / a ^ 2 * log (1 + T * a / b2) := mul_nonneg (by positivity) (by linarith)
    have hT2 : T / a * 2 ≤ T / a * log (1 + T * a / b2) := mul_le_mul_of_nonneg_left hlog (by positivity)
    have := neg_abs_le (log (2 / ε))
    nlinarith [le_abs_self (log (2 / ε))]
  unfold psiPin
  calc 2 * exp (T / a - (T / a + b2 / a ^ 2) * log (1 + T * a / b2)) ≤ 2 * exp (-log (2 / ε)) := by
        gcongr
    _ = ε := by rw [exp_neg, exp_log (by positivity)]; field_simp

/-! ### McDiarmid's term -/

theorem psiMcD_nonneg (D v β s' t : ℝ) : 0 ≤ psiMcD D v β s' t := (exp_pos _).le

theorem psiMcD_le_one {D v β s' t : ℝ} (hs : 0 ≤ s') : psiMcD D v β s' t ≤ 1 := by
  unfold psiMcD
  rw [exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (max (t - √(β * v ^ 2 * s')) 0)])
    (by positivity)

theorem psiMcD_D_zero (v β s' t : ℝ) : psiMcD 0 v β s' t = 1 := by simp [psiMcD]

theorem psiMcD_mono_beta {D v β β' s' t : ℝ} (hβ : 0 < β) (hββ : β ≤ β') (hs : 0 < s') :
    psiMcD D v β s' t ≤ psiMcD D v β' s' t := by
  unfold psiMcD
  apply exp_le_exp.2
  have hm : max (t - √(β' * v ^ 2 * s')) 0 ≤ max (t - √(β * v ^ 2 * s')) 0 := by
    refine max_le_max ?_ le_rfl
    have : √(β * v ^ 2 * s') ≤ √(β' * v ^ 2 * s') := Real.sqrt_le_sqrt (by
      have : 0 ≤ v ^ 2 * s' := by positivity
      nlinarith)
    linarith
  have hm2 : (max (t - √(β' * v ^ 2 * s')) 0) ^ 2 ≤ (max (t - √(β * v ^ 2 * s')) 0) ^ 2 :=
    pow_le_pow_left₀ (le_max_right _ _) hm 2
  rcases eq_or_ne D 0 with hD | hD
  · subst hD; simp
  have hd : 0 < β ^ 2 * D ^ 2 * s' := by positivity
  have hdd : β ^ 2 * D ^ 2 * s' ≤ β' ^ 2 * D ^ 2 * s' := by
    have : β ^ 2 ≤ β' ^ 2 := pow_le_pow_left₀ hβ.le hββ 2
    have : 0 ≤ D ^ 2 * s' := by positivity
    nlinarith
  rw [div_le_div_iff₀ hd (hd.trans_le hdd)]
  have h0 : 0 ≤ (max (t - √(β' * v ^ 2 * s')) 0) ^ 2 := sq_nonneg _
  nlinarith

theorem psiMcD_mono_v {D v v' β s' t : ℝ} (hv : 0 ≤ v) (hvv : v ≤ v') (hβ : 0 ≤ β) (hs : 0 ≤ s') :
    psiMcD D v β s' t ≤ psiMcD D v' β s' t := by
  unfold psiMcD
  apply exp_le_exp.2
  have hm : max (t - √(β * v' ^ 2 * s')) 0 ≤ max (t - √(β * v ^ 2 * s')) 0 := by
    refine max_le_max ?_ le_rfl
    have : √(β * v ^ 2 * s') ≤ √(β * v' ^ 2 * s') := Real.sqrt_le_sqrt (by
      have : v ^ 2 ≤ v' ^ 2 := pow_le_pow_left₀ hv hvv 2
      have : 0 ≤ β * s' := mul_nonneg hβ hs
      nlinarith)
    linarith
  have hm2 := pow_le_pow_left₀ (le_max_right _ _) hm 2
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem psiMcD_antitone {D v β s' t t' : ℝ} (hs : 0 ≤ s') (htt : t ≤ t') :
    psiMcD D v β s' t' ≤ psiMcD D v β s' t := by
  unfold psiMcD
  apply exp_le_exp.2
  have hm : max (t - √(β * v ^ 2 * s')) 0 ≤ max (t' - √(β * v ^ 2 * s')) 0 :=
    max_le_max (by linarith) le_rfl
  have hm2 := pow_le_pow_left₀ (le_max_right _ _) hm 2
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The explicit McDiarmid bound: `t ≥ √(βv²s'') + βD√(s''L/2)` with `s' ≤ s''` gives `≤ e^{−L}`. -/
theorem psiMcD_le_exp {D v β s' s'' t L : ℝ} (hβ : 0 < β) (hD : 0 < D) (hs : 0 < s') (hss : s' ≤ s'')
    (hL : 0 ≤ L) (ht : √(β * v ^ 2 * s'') + β * D * √(s'' * L / 2) ≤ t) :
    psiMcD D v β s' t ≤ exp (-L) := by
  unfold psiMcD
  apply exp_le_exp.2
  have hs'' : 0 < s'' := hs.trans_le hss
  have h1 : √(β * v ^ 2 * s') ≤ √(β * v ^ 2 * s'') := Real.sqrt_le_sqrt (by
    have : 0 ≤ β * v ^ 2 := by positivity
    nlinarith)
  set q := β * D * √(s'' * L / 2) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq2 : q ^ 2 = β ^ 2 * D ^ 2 * (s'' * L / 2) := by
    rw [hq, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hm : q ≤ max (t - √(β * v ^ 2 * s')) 0 := le_max_of_le_left (by linarith)
  have hm2 : q ^ 2 ≤ (max (t - √(β * v ^ 2 * s')) 0) ^ 2 := pow_le_pow_left₀ hq0 hm 2
  have hd : 0 < β ^ 2 * D ^ 2 * s' := by positivity
  rw [div_le_iff₀ hd]
  have : L * s' ≤ L * s'' := mul_le_mul_of_nonneg_left hss hL
  nlinarith

/-! ### `Ψ_H` -/

theorem psiH_nonneg (D v ρbar β s' c' t : ℝ) : 0 ≤ psiH D v ρbar β s' c' t :=
  le_min (psiMcD_nonneg _ _ _ _ _) (psiPin_nonneg _ _ _)

theorem psiH_le_McD (D v ρbar β s' c' t : ℝ) : psiH D v ρbar β s' c' t ≤ psiMcD D v β s' t := min_le_left _ _

theorem psiH_le_Pin (D v ρbar β s' c' t : ℝ) :
    psiH D v ρbar β s' c' t ≤ psiPin (β * ρbar * c') (β * v ^ 2 * s') t := min_le_right _ _

/-- With a junk Pinelis term (`v = 0` or `ρ̄ = 0`), `Ψ_H` is the McDiarmid term. -/
theorem psiH_eq_McD {D v ρbar β s' c' t : ℝ} (hρ : 0 ≤ ρbar) (hβ : 0 ≤ β) (hs : 0 ≤ s') (hc : 0 ≤ c')
    (ht : 0 ≤ t) (h : v = 0 ∨ ρbar = 0) : psiH D v ρbar β s' c' t = psiMcD D v β s' t := by
  refine min_eq_left ((psiMcD_le_one hs).trans (one_le_psiPin_of_junk (by positivity) ht ?_))
  rcases h with h | h
  · right; subst h; ring
  · left; subst h; ring

theorem psiH_mono_beta {D v ρbar β β' s' c' t : ℝ} (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hβ : 1 ≤ β) (hββ : β ≤ β')
    (hs : 0 < s') (hc : 0 < c') (ht : 0 ≤ t) : psiH D v ρbar β s' c' t ≤ psiH D v ρbar β' s' c' t := by
  have hβ0 : 0 < β := by linarith
  by_cases hj : v = 0 ∨ ρbar = 0
  · rw [psiH_eq_McD hρ hβ0.le hs.le hc.le ht hj, psiH_eq_McD hρ (hβ0.le.trans hββ) hs.le hc.le ht hj]
    exact psiMcD_mono_beta hβ0 hββ hs
  push_neg at hj
  have hv0 : 0 < v := lt_of_le_of_ne hv (Ne.symm hj.1)
  have hρ0 : 0 < ρbar := lt_of_le_of_ne hρ (Ne.symm hj.2)
  refine min_le_min (psiMcD_mono_beta hβ0 hββ hs) (psiPin_mono (by positivity) ?_ (by positivity) ?_ ht)
  · have : 0 ≤ ρbar * c' := by positivity
    nlinarith
  · have : 0 ≤ v ^ 2 * s' := by positivity
    nlinarith

theorem psiH_mono_const {D v v' ρbar ρbar' β s' c' t : ℝ} (hv : 0 < v) (hvv : v ≤ v') (hρ : 0 < ρbar)
    (hρρ : ρbar ≤ ρbar') (hβ : 1 ≤ β) (hs : 0 < s') (hc : 0 < c') (ht : 0 ≤ t) :
    psiH D v ρbar β s' c' t ≤ psiH D v' ρbar' β s' c' t := by
  have hβ0 : 0 < β := by linarith
  refine min_le_min (psiMcD_mono_v hv.le hvv hβ0.le hs.le) (psiPin_mono (by positivity) ?_ (by positivity) ?_ ht)
  · have : 0 ≤ β * c' := by positivity
    nlinarith
  · have : v ^ 2 ≤ v' ^ 2 := pow_le_pow_left₀ hv.le hvv 2
    have : 0 ≤ β * s' := by positivity
    nlinarith

theorem psiH_antitone {D v ρbar β s' c' t t' : ℝ} (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hβ : 0 < β) (hs : 0 < s')
    (hc : 0 < c') (ht : 0 ≤ t) (htt : t ≤ t') : psiH D v ρbar β s' c' t' ≤ psiH D v ρbar β s' c' t := by
  by_cases hj : v = 0 ∨ ρbar = 0
  · rw [psiH_eq_McD hρ hβ.le hs.le hc.le ht hj, psiH_eq_McD hρ hβ.le hs.le hc.le (ht.trans htt) hj]
    exact psiMcD_antitone hs.le htt
  push_neg at hj
  have hv0 : 0 < v := lt_of_le_of_ne hv (Ne.symm hj.1)
  have hρ0 : 0 < ρbar := lt_of_le_of_ne hρ (Ne.symm hj.2)
  exact min_le_min (psiMcD_antitone hs.le htt) (psiPin_antitone (by positivity) (by positivity) ht htt)

/-! ### The two-point bound and `Ψ_R` -/

theorem twoPt_nonneg {β : ℝ} (hβ : 1 ≤ β) (l : ℝ) : 0 ≤ twoPt β l := by
  unfold twoPt
  have : 0 < β := by linarith
  have : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hβ
  have : 0 ≤ 1 - β⁻¹ := by linarith
  positivity

theorem twoPt_mono {β β' : ℝ} (hβ : 1 ≤ β) (hββ : β ≤ β') (l : ℝ) : twoPt β l ≤ twoPt β' l := by
  have hβ0 : 0 < β := by linarith
  have hβ'0 : 0 < β' := by linarith
  set θ := β / β' with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hβ'0]; exact hββ
  have hc := (convexOn_exp).2 (mem_univ (l * (1 - β'))) (mem_univ l) hθ0 (by linarith : 0 ≤ 1 - θ)
    (by ring)
  simp only [smul_eq_mul] at hc
  have e : θ * (l * (1 - β')) + (1 - θ) * l = l * (1 - β) := by
    rw [hθ]; field_simp; ring
  rw [e] at hc
  unfold twoPt
  have hb : 0 ≤ β⁻¹ := by positivity
  have h1 : β⁻¹ * exp (l * (1 - β)) ≤ β⁻¹ * (θ * exp (l * (1 - β')) + (1 - θ) * exp l) :=
    mul_le_mul_of_nonneg_left hc hb
  have e2 : β⁻¹ * (θ * exp (l * (1 - β')) + (1 - θ) * exp l) + (1 - β⁻¹) * exp l =
      β'⁻¹ * exp (l * (1 - β')) + (1 - β'⁻¹) * exp l := by
    rw [hθ]; field_simp; ring
  linarith

theorem twoPt_le_exp {β l : ℝ} (hβ : 1 ≤ β) (hl : 0 ≤ l) : twoPt β l ≤ exp l := by
  unfold twoPt
  have : 0 < β := by linarith
  have h1 : exp (l * (1 - β)) ≤ exp l := exp_le_exp.2 (by nlinarith)
  have : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hβ
  have hb : 0 ≤ β⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hb]

/-- The product of `Ψ_R`. -/
theorem prodK_nonneg {β : ℝ} (hβ : 1 ≤ β) (l : ℝ) (K : List ℕ) :
    0 ≤ (K.map fun k : ℕ => twoPt β (l / (k : ℝ)) ^ k).prod := by
  induction K with
  | nil => simp
  | cons k K ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_nonneg (pow_nonneg (twoPt_nonneg hβ _) _) ih

theorem prodK_mono {β β' : ℝ} (hβ : 1 ≤ β) (hββ : β ≤ β') (l : ℝ) (K : List ℕ) :
    (K.map fun k : ℕ => twoPt β (l / (k : ℝ)) ^ k).prod ≤ (K.map fun k : ℕ => twoPt β' (l / (k : ℝ)) ^ k).prod := by
  induction K with
  | nil => simp
  | cons k K ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_le_mul (pow_le_pow_left₀ (twoPt_nonneg hβ _) (twoPt_mono hβ hββ _) _) ih
      (prodK_nonneg hβ l K) (pow_nonneg (twoPt_nonneg (hβ.trans hββ) _) _)

theorem prodK_le {β l : ℝ} (hβ : 1 ≤ β) (hl : 0 ≤ l) (K : List ℕ) :
    (K.map fun k : ℕ => twoPt β (l / (k : ℝ)) ^ k).prod ≤ exp (l * K.length) := by
  induction K with
  | nil => simp
  | cons k K ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    have hk : twoPt β (l / (k : ℝ)) ^ k ≤ exp l := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp [one_le_exp hl]
      · have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
        calc twoPt β (l / (k : ℝ)) ^ k ≤ exp (l / k) ^ k :=
              pow_le_pow_left₀ (twoPt_nonneg hβ _) (twoPt_le_exp hβ (div_nonneg hl hk'.le)) k
          _ = exp l := by rw [← exp_nat_mul]; congr 1; field_simp
    calc twoPt β (l / (k : ℝ)) ^ k * (K.map fun k : ℕ => twoPt β (l / (k : ℝ)) ^ k).prod
        ≤ exp l * exp (l * K.length) := mul_le_mul hk ih (prodK_nonneg hβ l K) (exp_pos _).le
      _ = exp (l * ((K.length + 1 : ℕ) : ℝ)) := by rw [← exp_add]; push_cast; ring_nf

theorem psiRlam_nonneg {β : ℝ} (hβ : 1 ≤ β) (l t : ℝ) (K : List ℕ) : 0 ≤ psiRlam β l t K :=
  mul_nonneg (exp_pos _).le (prodK_nonneg hβ l K)

theorem psiRlam_mono_beta {β β' : ℝ} (hβ : 1 ≤ β) (hββ : β ≤ β') (l t : ℝ) (K : List ℕ) :
    psiRlam β l t K ≤ psiRlam β' l t K :=
  mul_le_mul_of_nonneg_left (prodK_mono hβ hββ l K) (exp_pos _).le

theorem psiRlam_antitone {β l : ℝ} (hβ : 1 ≤ β) (hl : 0 < l) (K : List ℕ) :
    Antitone (fun t => psiRlam β l t K) := fun t t' htt =>
  mul_le_mul_of_nonneg_right (exp_le_exp.2 (by nlinarith)) (prodK_nonneg hβ l K)

theorem psiRlam_bddBelow {β : ℝ} (hβ : 1 ≤ β) (t : ℝ) (K : List ℕ) :
    BddBelow (range fun l : Ioi (0 : ℝ) => psiRlam β l t K) :=
  ⟨0, by rintro _ ⟨l, rfl⟩; exact psiRlam_nonneg hβ _ _ _⟩

theorem psiR_nonneg {β : ℝ} (hβ : 1 ≤ β) (t : ℝ) (K : List ℕ) : 0 ≤ psiR β t K := by
  haveI : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, mem_Ioi.2 one_pos⟩⟩
  exact le_ciInf fun l => psiRlam_nonneg hβ _ _ _

theorem psiR_le {β : ℝ} (hβ : 1 ≤ β) (t : ℝ) (K : List ℕ) {l : ℝ} (hl : 0 < l) :
    psiR β t K ≤ psiRlam β l t K :=
  ciInf_le (psiRlam_bddBelow hβ t K) ⟨l, hl⟩

theorem psiR_mono_beta {β β' : ℝ} (hβ : 1 ≤ β) (hββ : β ≤ β') (t : ℝ) (K : List ℕ) :
    psiR β t K ≤ psiR β' t K := by
  haveI : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, mem_Ioi.2 one_pos⟩⟩
  exact ciInf_mono (psiRlam_bddBelow hβ t K) fun l => psiRlam_mono_beta hβ hββ _ _ _

theorem psiR_antitone {β : ℝ} (hβ : 1 ≤ β) (K : List ℕ) : Antitone (fun t => psiR β t K) := by
  haveI : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, mem_Ioi.2 one_pos⟩⟩
  intro t t' htt
  exact ciInf_mono (psiRlam_bddBelow hβ t' K) fun l => psiRlam_antitone hβ l.2 K htt

theorem exists_psiRlam_lt {β : ℝ} (hβ : 1 ≤ β) (t : ℝ) (K : List ℕ) {c : ℝ} (hc : psiR β t K < c) :
    ∃ l : ℝ, 0 < l ∧ psiRlam β l t K < c := by
  obtain ⟨⟨l, hl⟩, h⟩ := exists_lt_of_ciInf_lt hc
  exact ⟨l, hl, h⟩

/-- `Ψ_R(t;β,K) = 0` once `t ≥ |K| + 1`. -/
theorem psiR_eq_zero {β t : ℝ} (hβ : 1 ≤ β) (K : List ℕ) (ht : (K.length : ℝ) + 1 ≤ t) : psiR β t K = 0 := by
  refine le_antisymm ?_ (psiR_nonneg hβ t K)
  have hb : ∀ l : ℝ, 0 < l → psiR β t K ≤ exp (-l) := fun l hl => by
    refine (psiR_le hβ t K hl).trans ?_
    unfold psiRlam
    calc exp (-(l * t)) * (K.map fun k : ℕ => twoPt β (l / (k : ℝ)) ^ k).prod
        ≤ exp (-(l * t)) * exp (l * K.length) :=
          mul_le_mul_of_nonneg_left (prodK_le hβ hl.le K) (exp_pos _).le
      _ = exp (-(l * t) + l * K.length) := (exp_add _ _).symm
      _ ≤ exp (-l) := exp_le_exp.2 (by nlinarith)
  refine ge_of_tendsto Real.tendsto_exp_neg_atTop_nhds_zero ?_
  filter_upwards [eventually_gt_atTop 0] with l hl
  exact hb l hl

/-! ### The frozen monotonicity claims -/

theorem tails_mono_beta : Claims.tails_mono_beta := by
  refine ⟨fun D v ρbar β β' s' c' t _ hv hρ hβ hββ hs hc ht => psiH_mono_beta hv hρ hβ hββ hs hc ht,
    fun β β' l t K hβ hββ _ => psiRlam_mono_beta hβ hββ l t K,
    fun β β' t K hβ hββ => psiR_mono_beta hβ hββ t K,
    fun D v β β' s' t hβ hββ hs => psiMcD_mono_beta hβ hββ hs,
    fun a a' b2 b2' t ha haa hb hbb ht => psiPin_mono ha haa hb hbb ht,
    fun β β' l hβ hββ => twoPt_mono hβ hββ l⟩

theorem tails_mono_const : Claims.tails_mono_const :=
  fun D v v' ρbar ρbar' β s' c' t _ hv hvv hρ hρρ hβ hs hc ht => psiH_mono_const hv hvv hρ hρρ hβ hs hc ht

theorem tails_antitone_t : Claims.tails_antitone_t :=
  ⟨fun D v ρbar β s' c' _ hv hρ hβ hs hc t ht t' _ htt =>
      psiH_antitone hv hρ (by linarith) hs hc ht htt,
    fun β l K hβ hl => psiRlam_antitone hβ hl K,
    fun β K hβ => psiR_antitone hβ K⟩

end StatFormal.Wave30ts
