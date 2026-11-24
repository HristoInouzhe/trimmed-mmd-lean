import StatFormal.Wave31tu.Statements
import StatFormal.Lib.LaplaceRate.Powers
import StatFormal.Lib.LaplaceRate.Improves

/-!
# Wave 31tu route T: the orders of the terms of `ε_fit` (proof of Theorem S4.19, S4 :1372-1381; untrusted proof material)

With `w = (x/N)^{1/2}` and `u = K^{1/4}w ≤ 1` (`N = n∧m`, `x` the common parameter of the interval events, `K ≥ 1` the window),
for fitting samples of sizes `n′, m′ ≥ N/5` and `π_K ≤ Π/N`:
* `sDev_le`, `rDev_le`, `cx_rDev_le`: `s ≤ 2√5·w`, `r ≤ 10/N`, `c_x·r ≤ 40x/N` (`x ≥ 2`);
* `epsFitI_le`: `ε_fit ≤ coefI·u` in case (i) (the five terms of `prop:lapfitted`);
* `epsFitII_le`: `ε_fit ≤ coefII·u^{8/9}` in case (ii) (the four terms), `u^{8/9} = (K^{1/2}x/N)^{4/9}`;
* `Tbet_le`: `T_bet(J′) ≤ 40·v_min^{−2}{L_δ^{1/2} + (log(2J/η))^{1/2}}/√N` for `J′ ≤ J`, `N_pairs ≥ N/2`, `v²_min ≤ 4`;
* `x_le_five_L`, `K_le`, `u_le`, `u_pow_le`: `x = log(16(M+1)²/η) ≤ 5L_{n,m}`, `K ≤ K₀·log M` and the orders
  `u ≤ √5K₀^{1/4}(log M)^{1/4}L^{1/2}/√N`, `u^{8/9} ≤ (5K₀^{1/2})^{4/9}{(log M)^{1/2}L/N}^{4/9}`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tu.RouteT

open StatFormal.LaplaceRate StatFormal.Wave31tl

section Dev

variable {N c : ℝ} {n' m' : ℕ}

lemma sDev_le (hc : 0 ≤ c) (hN : 0 < N) (hn : N / 5 ≤ n') (hm : N / 5 ≤ m') : sDev c n' m' ≤ 2 * √5 * √(c / N) := by
  unfold sDev
  have h1 := sqrt_div_le_of_fifth hc hN hn
  have h2 := sqrt_div_le_of_fifth hc hN hm
  linarith

lemma sDev_nonneg : 0 ≤ sDev c n' m' := by unfold sDev; positivity

lemma rDev_nonneg : 0 ≤ rDev n' m' := by unfold rDev; positivity

lemma rDev_le (hN : 0 < N) (hn : N / 5 ≤ n') (hm : N / 5 ≤ m') : rDev n' m' ≤ 10 / N := by
  unfold rDev
  have h1 := one_div_le_of_fifth hN hn
  have h2 := one_div_le_of_fifth hN hm
  have : 5 / N + 5 / N = 10 / N := by ring
  linarith

lemma cx_rDev_le (hc : 2 ≤ c) (hN : 0 < N) (hn : N / 5 ≤ n') (hm : N / 5 ≤ m') : cx c * rDev n' m' ≤ 40 * (c / N) := by
  have hr := rDev_le hN hn hm
  unfold cx
  calc (2 * c + 4) * rDev n' m' ≤ (4 * c) * (10 / N) := mul_le_mul (by linarith) hr rDev_nonneg (by linarith)
    _ = 40 * (c / N) := by ring

lemma min_cast_ge (hn : N / 5 ≤ n') (hm : N / 5 ≤ m') : N / 5 ≤ ((min n' m' : ℕ) : ℝ) := by
  rw [Nat.cast_min]; exact le_min hn hm

end Dev

/-- The common facts about `w = √(x/N)` and `u = K^{1/4}w`. -/
lemma w_facts {N c K : ℝ} (hN : 1 ≤ N) (hc : 1 ≤ c) (hK : 1 ≤ K) (hu : K ^ (1 / 4 : ℝ) * √(c / N) ≤ 1) :
    0 ≤ √(c / N) ∧ √(c / N) ≤ K ^ (1 / 4 : ℝ) * √(c / N) ∧ c / N = √(c / N) ^ 2 ∧ √(c / N) ^ 2 ≤ √(c / N) ∧
      1 / N ≤ c / N ∧ 0 ≤ K ^ (1 / 4 : ℝ) * √(c / N) := by
  have hN0 : 0 < N := by linarith
  have hw0 : 0 ≤ √(c / N) := Real.sqrt_nonneg _
  have hK4 : 1 ≤ K ^ (1 / 4 : ℝ) := Real.one_le_rpow hK (by norm_num)
  have hwu : √(c / N) ≤ K ^ (1 / 4 : ℝ) * √(c / N) := le_mul_of_one_le_left hw0 hK4
  have hw1 : √(c / N) ≤ 1 := hwu.trans hu
  refine ⟨hw0, hwu, (Real.sq_sqrt (by positivity)).symm, ?_, div_le_div_of_nonneg_right hc hN0.le, by positivity⟩
  nlinarith

/-- The coefficient of `u` in the bound on `ε_fit`, case (i). -/
def coefI (κ cv A0 A1 Pi : ℝ) : ℝ :=
  24 * (2 * √5 * A0 + 280 + 2 * Pi) / κ + 108 * (2 * √5 * A1) / (κ * √cv) + (72000 / (κ * cv)) ^ (4 / 5 : ℝ) +
    (2 / cv) ^ (20 / 33 : ℝ) * (2 * √5 * A1) ^ (40 / 33 : ℝ) + (5 * (1920 / (κ * cv ^ 2))) ^ (2 / 3 : ℝ)

/-- The coefficient of `u^{8/9}` in the bound on `ε_fit`, case (ii). -/
def coefII (κ cv Pi : ℝ) : ℝ :=
  24 * (10 * √5 + 160 + 2 * Pi) / κ + (240 * √5 / (κ * √cv)) ^ (8 / 9 : ℝ) + (37440 / (κ * cv)) ^ (4 / 5 : ℝ) +
    (5 * (576 / (κ * cv ^ 2))) ^ (2 / 3 : ℝ)

lemma lapA0_nonneg {pbar cs rs : ℝ} (hcr : 0 < cs * rs) : 0 ≤ lapA0 pbar cs rs := by
  unfold lapA0
  have := Real.rpow_pos_of_pos hcr (-(1 / 2 : ℝ))
  positivity

lemma lapA1_nonneg {pbar cs rs : ℝ} (hp : 0 ≤ pbar) (hcr : 0 < cs * rs) : 0 ≤ lapA1 pbar cs rs := by
  unfold lapA1
  have h1 : 0 ≤ (2 * √2 * pbar) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h2 : 0 ≤ (2 * √2 / (cs * rs)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h3 : 0 ≤ (2 : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_nonneg (by norm_num) _
  positivity

lemma coefI_nonneg {κ cv A0 A1 Pi : ℝ} (hκ : 0 < κ) (hcv : 0 < cv) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hPi : 0 ≤ Pi) :
    0 ≤ coefI κ cv A0 A1 Pi := by
  unfold coefI
  have h1 : 0 ≤ (72000 / (κ * cv)) ^ (4 / 5 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h2 : 0 ≤ (2 / cv) ^ (20 / 33 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h3 : 0 ≤ (2 * √5 * A1) ^ (40 / 33 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h4 : 0 ≤ (5 * (1920 / (κ * cv ^ 2))) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have : 0 < √cv := Real.sqrt_pos.2 hcv
  positivity

lemma coefII_nonneg {κ cv Pi : ℝ} (hκ : 0 < κ) (hcv : 0 < cv) (hPi : 0 ≤ Pi) : 0 ≤ coefII κ cv Pi := by
  unfold coefII
  have : 0 < √cv := Real.sqrt_pos.2 hcv
  have h1 : 0 ≤ (240 * √5 / (κ * √cv)) ^ (8 / 9 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h2 : 0 ≤ (37440 / (κ * cv)) ^ (4 / 5 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h3 : 0 ≤ (5 * (576 / (κ * cv ^ 2))) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
  positivity

/-- **`ε_fit ≤ coefI·u`**, case (i). -/
lemma epsFitI_le (P Q : Measure ℝ) {x₀ K pbar cs rs c κ cv Pi N : ℝ} {n' m' : ℕ} (hκ : 0 < κ) (hcv : 0 < cv)
    (hpbar : 0 ≤ pbar) (hcr : 0 < cs * rs) (hPi : 0 ≤ Pi) (hN : 1 ≤ N) (hn : N / 5 ≤ n') (hm : N / 5 ≤ m')
    (hc : 2 ≤ c) (hK : 1 ≤ K) (hu : K ^ (1 / 4 : ℝ) * √(c / N) ≤ 1) (hpi : piK P Q x₀ K ≤ Pi / N) :
    epsFitI κ cv (devA P Q x₀ K pbar cs rs c n' m') (devG pbar cs rs K c n' m') (devB K c n' m') (min n' m') ≤
      coefI κ cv (lapA0 pbar cs rs) (lapA1 pbar cs rs) Pi * (K ^ (1 / 4 : ℝ) * √(c / N)) := by
  have hN0 : 0 < N := by linarith
  obtain ⟨hw0, hwu, hw2, hw2w, hN1, hu0⟩ := w_facts hN (by linarith) hK hu
  set w := √(c / N)
  set u := K ^ (1 / 4 : ℝ) * w with hudef
  set A0 := lapA0 pbar cs rs
  set A1 := lapA1 pbar cs rs
  have hA0 : 0 ≤ A0 := lapA0_nonneg hcr
  have hA1 : 0 ≤ A1 := lapA1_nonneg hpbar hcr
  have hs := sDev_le (c := c) (by linarith) hN0 hn hm
  have hcr' := cx_rDev_le hc hN0 hn hm
  have hK4 : 0 ≤ K ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hK2 : 0 ≤ K ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hsq : u ^ 2 = K ^ (1 / 2 : ℝ) * (c / N) := sq_quarter_sqrt (by linarith) (by positivity)
  have hpi0 : 0 ≤ piK P Q x₀ K := measureReal_nonneg
  have hPiN : Pi / N ≤ Pi * u := by
    have : Pi / N = Pi * (1 / N) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left (by linarith) hPi
  -- the three deviation constants
  have ha : devA P Q x₀ K pbar cs rs c n' m' ≤ (2 * √5 * A0 + 280 + 2 * Pi) * u := by
    unfold devA
    have e1 : A0 * sDev c n' m' ≤ 2 * √5 * A0 * u := by
      calc A0 * sDev c n' m' ≤ A0 * (2 * √5 * w) := mul_le_mul_of_nonneg_left hs hA0
        _ ≤ A0 * (2 * √5 * u) := by gcongr
        _ = 2 * √5 * A0 * u := by ring
    have e2 : 7 * cx c * rDev n' m' ≤ 280 * u := by
      have : 7 * cx c * rDev n' m' = 7 * (cx c * rDev n' m') := by ring
      rw [this]; linarith
    linarith
  have hg : devG pbar cs rs K c n' m' ≤ 2 * √5 * A1 * u := by
    unfold devG
    calc A1 * K ^ (1 / 4 : ℝ) * sDev c n' m' ≤ A1 * K ^ (1 / 4 : ℝ) * (2 * √5 * w) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 2 * √5 * A1 * u := by rw [hudef]; ring
  have hg0 : 0 ≤ devG pbar cs rs K c n' m' := by unfold devG; have := sDev_nonneg (c := c) (n' := n') (m' := m'); positivity
  have hb : devB K c n' m' ≤ 240 * u ^ 2 := by
    unfold devB
    have : 6 * K ^ (1 / 2 : ℝ) * cx c * rDev n' m' = 6 * K ^ (1 / 2 : ℝ) * (cx c * rDev n' m') := by ring
    rw [this, hsq]
    calc 6 * K ^ (1 / 2 : ℝ) * (cx c * rDev n' m') ≤ 6 * K ^ (1 / 2 : ℝ) * (40 * (c / N)) :=
          mul_le_mul_of_nonneg_left hcr' (by positivity)
      _ = 240 * (K ^ (1 / 2 : ℝ) * (c / N)) := by ring
  have hb0 : 0 ≤ devB K c n' m' := by
    unfold devB cx; have := rDev_nonneg (n' := n') (m' := m'); positivity
  have hu1 : u ≤ 1 := hu
  -- the five terms
  have t1 : 24 * devA P Q x₀ K pbar cs rs c n' m' / κ ≤ 24 * (2 * √5 * A0 + 280 + 2 * Pi) / κ * u := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hκ]
    have := mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 24)
    linarith
  have t2 : 108 * devG pbar cs rs K c n' m' / (κ * √cv) ≤ 108 * (2 * √5 * A1) / (κ * √cv) * u := by
    have : 0 < κ * √cv := mul_pos hκ (Real.sqrt_pos.2 hcv)
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right this]
    have := mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ) ≤ 108)
    linarith
  have t3 : (300 * devB K c n' m' / (κ * cv)) ^ (4 / 5 : ℝ) ≤ (72000 / (κ * cv)) ^ (4 / 5 : ℝ) * u := by
    have hb' : 300 * devB K c n' m' / (κ * cv) ≤ 72000 / (κ * cv) * u ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (mul_pos hκ hcv)]
      have := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 300)
      linarith
    calc (300 * devB K c n' m' / (κ * cv)) ^ (4 / 5 : ℝ) ≤ (72000 / (κ * cv) * u ^ 2) ^ (4 / 5 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hb' (by norm_num)
      _ ≤ (72000 / (κ * cv)) ^ (4 / 5 : ℝ) * u ^ (1 : ℝ) :=
          (mul_sq_rpow_le (by positivity) hu0 hu1 (by norm_num) (by norm_num)).2
      _ = (72000 / (κ * cv)) ^ (4 / 5 : ℝ) * u := by rw [Real.rpow_one]
  have t4 : (2 / cv) ^ (20 / 33 : ℝ) * devG pbar cs rs K c n' m' ^ (40 / 33 : ℝ) ≤
      (2 / cv) ^ (20 / 33 : ℝ) * (2 * √5 * A1) ^ (40 / 33 : ℝ) * u := by
    have h := Real.rpow_le_rpow hg0 hg (by norm_num : (0 : ℝ) ≤ 40 / 33)
    have h' : (2 * √5 * A1 * u) ^ (40 / 33 : ℝ) ≤ (2 * √5 * A1) ^ (40 / 33 : ℝ) * u ^ (1 : ℝ) :=
      mul_rpow_le (by positivity) hu0 hu1 (by norm_num) (by norm_num)
    rw [Real.rpow_one] at h'
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.trans h') (Real.rpow_nonneg (by positivity) _)
  have t5 : (1920 / (κ * cv ^ 2 * ((min n' m' : ℕ) : ℝ))) ^ (2 / 3 : ℝ) ≤ (5 * (1920 / (κ * cv ^ 2))) ^ (2 / 3 : ℝ) * u := by
    have e : 1920 / (κ * cv ^ 2 * ((min n' m' : ℕ) : ℝ)) = 1920 / (κ * cv ^ 2) / ((min n' m' : ℕ) : ℝ) := by
      rw [div_div]
    rw [e]
    refine (div_rpow_two_thirds_le (by positivity) hN0 (min_cast_ge hn hm)).trans ?_
    exact mul_le_mul_of_nonneg_left (rpow_neg_two_thirds_le hN (by linarith) hK) (Real.rpow_nonneg (by positivity) _)
  -- collect
  have k : ∀ {T Ci : ℝ}, T ≤ Ci * u → Ci ≤ coefI κ cv A0 A1 Pi → T ≤ coefI κ cv A0 A1 Pi * u :=
    fun h1 h2 => h1.trans (mul_le_mul_of_nonneg_right h2 hu0)
  have hC1 : 0 ≤ 24 * (2 * √5 * A0 + 280 + 2 * Pi) / κ := by positivity
  have hC2 : 0 ≤ 108 * (2 * √5 * A1) / (κ * √cv) := by have : 0 < √cv := Real.sqrt_pos.2 hcv; positivity
  have hC3 : 0 ≤ (72000 / (κ * cv)) ^ (4 / 5 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hC4 : 0 ≤ (2 / cv) ^ (20 / 33 : ℝ) * (2 * √5 * A1) ^ (40 / 33 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  have hC5 : 0 ≤ (5 * (1920 / (κ * cv ^ 2))) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
  unfold epsFitI
  refine max_le (max_le (max_le (max_le (k t1 ?_) (k t2 ?_)) (k t3 ?_)) (k t4 ?_)) (k t5 ?_) <;>
    · unfold coefI; linarith

/-- **`ε_fit ≤ coefII·u^{8/9}`**, case (ii). -/
lemma epsFitII_le (P Q : Measure ℝ) {x₀ K c κ cv Pi N : ℝ} {n' m' : ℕ} (hκ : 0 < κ) (hcv : 0 < cv) (hPi : 0 ≤ Pi)
    (hN : 1 ≤ N) (hn : N / 5 ≤ n') (hm : N / 5 ≤ m') (hc : 2 ≤ c) (hK : 1 ≤ K) (hu : K ^ (1 / 4 : ℝ) * √(c / N) ≤ 1)
    (hpi : piK P Q x₀ K ≤ Pi / N) :
    epsFitII κ cv (devA' P Q x₀ K c n' m') (devG' K c n' m') (devB K c n' m') (min n' m') ≤
      coefII κ cv Pi * (K ^ (1 / 4 : ℝ) * √(c / N)) ^ (8 / 9 : ℝ) := by
  have hN0 : 0 < N := by linarith
  obtain ⟨hw0, hwu, hw2, hw2w, hN1, hu0⟩ := w_facts hN (by linarith) hK hu
  set w := √(c / N)
  set u := K ^ (1 / 4 : ℝ) * w with hudef
  have hu1 : u ≤ 1 := hu
  have hu89 : u ≤ u ^ (8 / 9 : ℝ) := self_le_rpow_of_le_one hu0 hu1 (by norm_num) (by norm_num)
  have hs := sDev_le (c := c) (by linarith) hN0 hn hm
  have hcr' := cx_rDev_le hc hN0 hn hm
  have hK2 : 0 ≤ K ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hsq : u ^ 2 = K ^ (1 / 2 : ℝ) * (c / N) := sq_quarter_sqrt (by linarith) (by positivity)
  have hpi0 : 0 ≤ piK P Q x₀ K := measureReal_nonneg
  have hPiN : Pi / N ≤ Pi * u := by
    have : Pi / N = Pi * (1 / N) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left (by linarith) hPi
  have ha : devA' P Q x₀ K c n' m' ≤ (10 * √5 + 160 + 2 * Pi) * u := by
    unfold devA'
    have e1 : 5 * sDev c n' m' ≤ 10 * √5 * u := by
      have h5 : 0 ≤ √5 := Real.sqrt_nonneg 5
      have : √5 * w ≤ √5 * u := mul_le_mul_of_nonneg_left hwu h5
      linarith
    have e2 : 4 * cx c * rDev n' m' ≤ 160 * u := by
      have : 4 * cx c * rDev n' m' = 4 * (cx c * rDev n' m') := by ring
      rw [this]; linarith
    linarith
  have hg : devG' K c n' m' ≤ 4 * √5 * u := by
    unfold devG'
    calc 2 * K ^ (1 / 4 : ℝ) * sDev c n' m' ≤ 2 * K ^ (1 / 4 : ℝ) * (2 * √5 * w) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 4 * √5 * u := by rw [hudef]; ring
  have hg0 : 0 ≤ devG' K c n' m' := by unfold devG'; have := sDev_nonneg (c := c) (n' := n') (m' := m'); positivity
  have hb : devB K c n' m' ≤ 240 * u ^ 2 := by
    unfold devB
    have : 6 * K ^ (1 / 2 : ℝ) * cx c * rDev n' m' = 6 * K ^ (1 / 2 : ℝ) * (cx c * rDev n' m') := by ring
    rw [this, hsq]
    calc 6 * K ^ (1 / 2 : ℝ) * (cx c * rDev n' m') ≤ 6 * K ^ (1 / 2 : ℝ) * (40 * (c / N)) :=
          mul_le_mul_of_nonneg_left hcr' (by positivity)
      _ = 240 * (K ^ (1 / 2 : ℝ) * (c / N)) := by ring
  have hb0 : 0 ≤ devB K c n' m' := by
    unfold devB cx; have := rDev_nonneg (n' := n') (m' := m'); positivity
  have hsc : 0 < √cv := Real.sqrt_pos.2 hcv
  have t1 : 24 * devA' P Q x₀ K c n' m' / κ ≤ 24 * (10 * √5 + 160 + 2 * Pi) / κ * u ^ (8 / 9 : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hκ]
    have h0 : 0 ≤ 10 * √5 + 160 + 2 * Pi := by positivity
    have := mul_le_mul_of_nonneg_left hu89 h0
    have := mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 24)
    linarith
  have t2 : (60 * devG' K c n' m' / (κ * √cv)) ^ (8 / 9 : ℝ) ≤ (240 * √5 / (κ * √cv)) ^ (8 / 9 : ℝ) * u ^ (8 / 9 : ℝ) := by
    have hg' : 60 * devG' K c n' m' / (κ * √cv) ≤ 240 * √5 / (κ * √cv) * u := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (mul_pos hκ hsc)]
      have := mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ) ≤ 60)
      linarith
    calc (60 * devG' K c n' m' / (κ * √cv)) ^ (8 / 9 : ℝ) ≤ (240 * √5 / (κ * √cv) * u) ^ (8 / 9 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hg' (by norm_num)
      _ ≤ (240 * √5 / (κ * √cv)) ^ (8 / 9 : ℝ) * u ^ (8 / 9 : ℝ) :=
          mul_rpow_le (by positivity) hu0 hu1 (by norm_num) le_rfl
  have t3 : (156 * devB K c n' m' / (κ * cv)) ^ (4 / 5 : ℝ) ≤ (37440 / (κ * cv)) ^ (4 / 5 : ℝ) * u ^ (8 / 9 : ℝ) := by
    have hb' : 156 * devB K c n' m' / (κ * cv) ≤ 37440 / (κ * cv) * u ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (mul_pos hκ hcv)]
      have := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 156)
      linarith
    calc (156 * devB K c n' m' / (κ * cv)) ^ (4 / 5 : ℝ) ≤ (37440 / (κ * cv) * u ^ 2) ^ (4 / 5 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hb' (by norm_num)
      _ ≤ (37440 / (κ * cv)) ^ (4 / 5 : ℝ) * u ^ (8 / 9 : ℝ) :=
          (mul_sq_rpow_le (by positivity) hu0 hu1 (by norm_num) (by norm_num)).2
  have t4 : (576 / (κ * cv ^ 2 * ((min n' m' : ℕ) : ℝ))) ^ (2 / 3 : ℝ) ≤
      (5 * (576 / (κ * cv ^ 2))) ^ (2 / 3 : ℝ) * u ^ (8 / 9 : ℝ) := by
    have e : 576 / (κ * cv ^ 2 * ((min n' m' : ℕ) : ℝ)) = 576 / (κ * cv ^ 2) / ((min n' m' : ℕ) : ℝ) := by
      rw [div_div]
    rw [e]
    refine (div_rpow_two_thirds_le (by positivity) hN0 (min_cast_ge hn hm)).trans ?_
    exact mul_le_mul_of_nonneg_left ((rpow_neg_two_thirds_le hN (by linarith) hK).trans hu89)
      (Real.rpow_nonneg (by positivity) _)
  have k : ∀ {T Ci : ℝ}, T ≤ Ci * u ^ (8 / 9 : ℝ) → Ci ≤ coefII κ cv Pi → T ≤ coefII κ cv Pi * u ^ (8 / 9 : ℝ) :=
    fun h1 h2 => h1.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hu0 _))
  have hC1 : 0 ≤ 24 * (10 * √5 + 160 + 2 * Pi) / κ := by positivity
  have hC2 : 0 ≤ (240 * √5 / (κ * √cv)) ^ (8 / 9 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hC3 : 0 ≤ (37440 / (κ * cv)) ^ (4 / 5 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hC4 : 0 ≤ (5 * (576 / (κ * cv ^ 2))) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
  unfold epsFitII
  refine max_le (max_le (max_le (k t1 ?_) (k t2 ?_)) (k t3 ?_)) (k t4 ?_) <;>
    · unfold coefII; linarith

/-- **`T_bet(J′) ≤ 40·v_min^{−2}{L_δ^{1/2} + (log(2J/η))^{1/2}}/√N`** for `0 < J′ ≤ J`, `N_pairs ≥ N/2`, `v²_min ≤ 4`. -/
lemma Tbet_le {s2 L η J' J N : ℝ} {Np : ℕ} (hs20 : 0 < s2) (hs24 : s2 ≤ 4) (hη0 : 0 < η) (hJ' : 0 < J')
    (hJJ : J' ≤ J) (hN : 0 < N) (hNp : N / 2 ≤ Np) :
    Tbet (1 / 2) s2 L η J' Np ≤ 40 * (s2⁻¹ * (√L + √(Real.log (2 * J / η)))) / √N := by
  have hNp0 : (0 : ℝ) < Np := lt_of_lt_of_le (by positivity) hNp
  have hsN : 0 < √N := Real.sqrt_pos.2 hN
  have hlog : √(Real.log (2 * J' / η)) ≤ √(Real.log (2 * J / η)) := by
    rcases le_or_gt (Real.log (2 * J' / η)) 0 with h | h
    · rw [Real.sqrt_eq_zero'.2 h]; exact Real.sqrt_nonneg _
    · exact Real.sqrt_le_sqrt (Real.log_le_log (by positivity) (by gcongr))
  have h2N : √(2 / (Np : ℝ)) ≤ 2 / √N := by
    rw [show (2 : ℝ) / √N = √(4 / N) by
      rw [Real.sqrt_div' _ hN.le, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_div_iff₀ hNp0 hN]; linarith
  have hss : √s2 ≤ 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hs24
  have hs2pos : 0 < √s2 := Real.sqrt_pos.2 hs20
  have hc1 : 1 + 16 / s2 ≤ 20 * s2⁻¹ := by
    rw [div_eq_mul_inv]
    have : 1 ≤ 4 * s2⁻¹ := by rw [← div_eq_mul_inv, le_div_iff₀ hs20]; linarith
    linarith
  have hc2 : 2 / √s2 ≤ 4 * s2⁻¹ := by
    have e : 2 / √s2 = 2 * √s2 / s2 := by
      rw [div_eq_div_iff hs2pos.ne' hs20.ne']
      rw [mul_assoc, Real.mul_self_sqrt hs20.le]
    rw [e, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by linarith) hs20.le
  unfold Tbet
  have hA : (1 + 16 / s2) * √L + 2 / √s2 * √(Real.log (2 * J' / η)) ≤
      20 * (s2⁻¹ * (√L + √(Real.log (2 * J / η)))) := by
    have hi : 0 ≤ s2⁻¹ := inv_nonneg.2 hs20.le
    have h1 : (1 + 16 / s2) * √L ≤ 20 * s2⁻¹ * √L := mul_le_mul_of_nonneg_right hc1 (Real.sqrt_nonneg _)
    have h2 : 2 / √s2 * √(Real.log (2 * J' / η)) ≤ 4 * s2⁻¹ * √(Real.log (2 * J / η)) :=
      mul_le_mul hc2 hlog (Real.sqrt_nonneg _) (by positivity)
    have h3 : 0 ≤ s2⁻¹ * √(Real.log (2 * J / η)) := by positivity
    linarith
  have hA0 : 0 ≤ (1 + 16 / s2) * √L + 2 / √s2 * √(Real.log (2 * J' / η)) := by positivity
  calc 2 * (1 / 2) * √(2 / (Np : ℝ)) * ((1 + 16 / s2) * √L + 2 / √s2 * √(Real.log (2 * J' / η)))
      ≤ 2 / √N * (20 * (s2⁻¹ * (√L + √(Real.log (2 * J / η))))) := by
        rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul]
        exact mul_le_mul h2N hA hA0 (by positivity)
    _ = 40 * (s2⁻¹ * (√L + √(Real.log (2 * J / η)))) / √N := by ring

/-- `x = log(16(M+1)²/η) ≤ 5·log(M/η)` and `x ≥ 2`, for `M ≥ 10`, `0 < η ≤ 1`. -/
lemma x_facts {M η : ℝ} (hM : 10 ≤ M) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    Real.log (16 * (M + 1) ^ 2 / η) ≤ 5 * Real.log (M / η) ∧ 2 ≤ Real.log (16 * (M + 1) ^ 2 / η) := by
  have hM0 : 0 < M := by linarith
  constructor
  · rw [← Real.log_rpow (by positivity), show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    refine Real.log_le_log (by positivity) ?_
    rw [div_pow, div_le_div_iff₀ hη0 (by positivity)]
    have h1 : η ^ 5 ≤ η := by
      calc η ^ 5 = η * η ^ 4 := by ring
        _ ≤ η * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hη0.le hη1) hη0.le
        _ = η := mul_one η
    have h2 : 16 * (M + 1) ^ 2 ≤ M ^ 5 := by
      have : (M + 1) ^ 2 ≤ 2 * M ^ 2 := by nlinarith
      have : 32 * M ^ 2 ≤ M ^ 5 := by
        have h3 : 32 ≤ M ^ 3 := by nlinarith
        nlinarith [sq_nonneg M]
      nlinarith
    calc 16 * (M + 1) ^ 2 * η ^ 5 ≤ M ^ 5 * η := mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = M ^ 5 * η := rfl
  · rw [Real.le_log_iff_exp_le (by positivity)]
    have he : Real.exp 2 ≤ 9 := by
      have := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [e]; nlinarith [Real.exp_pos 1]
    have : 9 ≤ 16 * (M + 1) ^ 2 / η := by
      rw [le_div_iff₀ hη0]; nlinarith
    linarith

/-- `K = max{1, 1/σ, C′log M/σ} ≤ K₀·log M` with `K₀ = max{1, 1/σ, C′/σ}`, for `log M ≥ 1`. -/
lemma K_le {σ C' lM : ℝ} (hσ : 0 < σ) (hlM : 1 ≤ lM) :
    max 1 (max (1 / σ) (C' * lM / σ)) ≤ max 1 (max (1 / σ) (C' / σ)) * lM := by
  have hK0 : 1 ≤ max 1 (max (1 / σ) (C' / σ)) := le_max_left _ _
  refine max_le ?_ (max_le ?_ ?_)
  · nlinarith
  · have : 1 / σ ≤ max 1 (max (1 / σ) (C' / σ)) := (le_max_left _ _).trans (le_max_right _ _)
    have h1 : 0 ≤ 1 / σ := by positivity
    nlinarith
  · have : C' / σ ≤ max 1 (max (1 / σ) (C' / σ)) := (le_max_right _ _).trans (le_max_right _ _)
    rw [show C' * lM / σ = C' / σ * lM by ring]
    exact mul_le_mul_of_nonneg_right this (by linarith)

/-- The order of `u`: `K^{1/4}√(x/N) ≤ √5·K₀^{1/4}(log M)^{1/4}L^{1/2}/√N` from `K ≤ K₀ log M`, `x ≤ 5L`. -/
lemma u_le {K K₀ lM c L N : ℝ} (hK : 0 ≤ K) (hKK : K ≤ K₀ * lM) (hK₀ : 0 ≤ K₀) (hlM : 0 ≤ lM) (hc0 : 0 ≤ c) (hcL : c ≤ 5 * L)
    (hN : 0 < N) :
    K ^ (1 / 4 : ℝ) * √(c / N) ≤ √5 * K₀ ^ (1 / 4 : ℝ) * (lM ^ (1 / 4 : ℝ) * L ^ (1 / 2 : ℝ) / √N) := by
  have hL : 0 ≤ L := by linarith
  have h1 : K ^ (1 / 4 : ℝ) ≤ K₀ ^ (1 / 4 : ℝ) * lM ^ (1 / 4 : ℝ) := by
    rw [← Real.mul_rpow hK₀ hlM]; exact Real.rpow_le_rpow hK hKK (by norm_num)
  have h2 : √(c / N) ≤ √5 * L ^ (1 / 2 : ℝ) / √N := by
    rw [Real.sqrt_div' _ hN.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num)]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hcL) (Real.sqrt_nonneg _)
  calc K ^ (1 / 4 : ℝ) * √(c / N) ≤ K₀ ^ (1 / 4 : ℝ) * lM ^ (1 / 4 : ℝ) * (√5 * L ^ (1 / 2 : ℝ) / √N) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    _ = √5 * K₀ ^ (1 / 4 : ℝ) * (lM ^ (1 / 4 : ℝ) * L ^ (1 / 2 : ℝ) / √N) := by ring

/-- The order of `u^{8/9}`: `(K^{1/4}√(x/N))^{8/9} ≤ (5K₀^{1/2})^{4/9}{(log M)^{1/2}L/N}^{4/9}`. -/
lemma u_pow_le {K K₀ lM c L N : ℝ} (hK : 0 ≤ K) (hKK : K ≤ K₀ * lM) (hK₀ : 0 ≤ K₀) (hlM : 0 ≤ lM) (hc0 : 0 ≤ c)
    (hcL : c ≤ 5 * L) (hN : 0 < N) :
    (K ^ (1 / 4 : ℝ) * √(c / N)) ^ (8 / 9 : ℝ) ≤ (5 * K₀ ^ (1 / 2 : ℝ)) ^ (4 / 9 : ℝ) * (lM ^ (1 / 2 : ℝ) * L / N) ^ (4 / 9 : ℝ) := by
  have hL : 0 ≤ L := by linarith
  have hu0 : 0 ≤ K ^ (1 / 4 : ℝ) * √(c / N) := by positivity
  have e : (K ^ (1 / 4 : ℝ) * √(c / N)) ^ (8 / 9 : ℝ) = (K ^ (1 / 2 : ℝ) * (c / N)) ^ (4 / 9 : ℝ) := by
    rw [← sq_quarter_sqrt hK (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hu0]; norm_num
  rw [e, ← Real.mul_rpow (by positivity) (by positivity)]
  refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
  have h1 : K ^ (1 / 2 : ℝ) ≤ K₀ ^ (1 / 2 : ℝ) * lM ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow hK₀ hlM]; exact Real.rpow_le_rpow hK hKK (by norm_num)
  have h2 : c / N ≤ 5 * L / N := div_le_div_of_nonneg_right hcL hN.le
  calc K ^ (1 / 2 : ℝ) * (c / N) ≤ K₀ ^ (1 / 2 : ℝ) * lM ^ (1 / 2 : ℝ) * (5 * L / N) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 5 * K₀ ^ (1 / 2 : ℝ) * (lM ^ (1 / 2 : ℝ) * L / N) := by ring

end StatFormal.Wave31tu.RouteT
