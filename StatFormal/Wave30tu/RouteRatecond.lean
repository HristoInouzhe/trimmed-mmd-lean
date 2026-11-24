import StatFormal.Wave30tu.RouteMain

/-!
# Wave 30tu — the rate-condition example and the polynomial case of `thm:rate` (untrusted proof route)

* At `δ = e^{−n}`, `s = 2/n`: `log(1/δ) = n`, so `D√(s log(1/δ)/2) = D`.
* McDiarmid: `exp(−2u²/(β²D²s)) ≤ e^{−n}` forces `u ≥ βD` (`u = (t − √(βv²s))_+`); Pinelis: the exponent is `≥ −t²/b²` by
  `(x+y)log(1+x/y) − x ≤ x²/y` (from `log(1+r) ≤ r`), and the factor 2 makes `t² > n b² = 2βv²` strict.
* Polynomial case: `ε = (t/c₀)^{1/γ}` solves `c₀ε^γ = t`; `r_n(α*,δ/2) ≤ 6κβ√(L/M)` with `L = 1 + log(1/δ) + log(1/δ')`,
  `M = min(n,m)` (`log 4 ≤ 2`), so `t ≤ 24κβ√(L/M)`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tu

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tl

theorem log_one_div_exp (n : ℕ) : Real.log (1 / Real.exp (-(n : ℝ))) = n := by
  rw [one_div, Real.log_inv, Real.log_exp, neg_neg]

theorem s_eq (n : ℕ) : (1 / (n : ℝ) + 1 / (n : ℝ)) = 2 / n := by ring

theorem dterm {n : ℕ} (hn : 1 ≤ n) (D : ℝ) :
    D * √((1 / (n : ℝ) + 1 / (n : ℝ)) * Real.log (1 / Real.exp (-(n : ℝ))) / 2) = D := by
  rw [log_one_div_exp]
  have hn' : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  have : (1 / (n : ℝ) + 1 / (n : ℝ)) * n / 2 = 1 := by field_simp; ring
  rw [this, Real.sqrt_one, mul_one]

theorem s_pos {n : ℕ} (hn : 1 ≤ n) : 0 < 1 / (n : ℝ) + 1 / (n : ℝ) := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem ratecond_closed : Claims.ratecond_closed := by
  intro v D n hv hD hn
  refine ⟨by rw [dterm hn, s_eq], ?_⟩
  have h2 : 0 < 2 / (n : ℝ) := by rw [← s_eq]; exact s_pos hn
  have : 0 < v * √(2 / (n : ℝ)) := mul_pos hv (Real.sqrt_pos.2 h2)
  linarith

theorem ratecond_tauA : Claims.ratecond_tauA := by
  intro κ D e₁ e₂ n hκ hD he1 he2 hn
  refine ⟨dterm hn D, ?_⟩
  have h1 : 0 < 2 * κ * √(1 / (n : ℝ) + 1 / (n : ℝ)) := by
    have := Real.sqrt_pos.2 (s_pos hn); positivity
  have h2 : 0 ≤ 2 * κ * (e₁ + e₂) := by positivity
  linarith

theorem pinelis_ineq : Claims.pinelis_ineq := by
  intro x y hx hy
  have hr : 0 ≤ x / y := div_nonneg hx hy.le
  have hlog : Real.log (1 + x / y) ≤ x / y := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x / y); linarith
  have hxy : 0 ≤ x + y := by linarith
  have h1 : (x + y) * Real.log (1 + x / y) ≤ (x + y) * (x / y) := mul_le_mul_of_nonneg_left hlog hxy
  have heq : (x + y) * (x / y) = x ^ 2 / y + x := by field_simp
  linarith

theorem ratecond_mcd : Claims.ratecond_mcd := by
  intro v D β t n hv hD hβ hn h
  have hs := s_eq n
  have hs0 := s_pos hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold psiMcD at h
  set s := 1 / (n : ℝ) + 1 / (n : ℝ)
  set u := max (t - √(β * v ^ 2 * s)) 0 with hudef
  rcases hD.lt_or_eq with hDpos | hD0
  · have hden : 0 < β ^ 2 * D ^ 2 * s := by positivity
    have h1 := Real.exp_le_exp.1 h
    have h2 : (n : ℝ) * (β ^ 2 * D ^ 2 * s) ≤ 2 * u ^ 2 := by
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ hden] at h1; linarith
    have h3 : (β * D) ^ 2 ≤ u ^ 2 := by
      have : (n : ℝ) * (β ^ 2 * D ^ 2 * s) = 2 * (β * D) ^ 2 := by rw [hs]; field_simp
      nlinarith
    have hu0 : 0 ≤ u := le_max_right _ _
    have hβD : 0 < β * D := by positivity
    have h4 : β * D ≤ u := by
      have := Real.sqrt_le_sqrt h3
      rwa [Real.sqrt_sq hβD.le, Real.sqrt_sq hu0] at this
    have hupos : 0 < u := lt_of_lt_of_le hβD h4
    have hu : u = t - √(β * v ^ 2 * s) := by
      rcases lt_max_iff.1 hupos with h5 | h5
      · exact max_eq_left h5.le
      · exact absurd h5 (lt_irrefl 0)
    linarith
  · have : β ^ 2 * D ^ 2 * s = 0 := by rw [← hD0]; ring
    rw [this, div_zero, Real.exp_zero] at h
    exact absurd h (not_le.2 (Real.exp_lt_one_iff.2 (by linarith)))

theorem ratecond_pin : Claims.ratecond_pin := by
  intro v ρbar β t n hv hρ hβ ht hn h
  have hs := s_eq n
  have hs0 := s_pos hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc0 : 0 < max (1 / (n : ℝ)) (1 / (n : ℝ)) := by rw [max_self]; positivity
  unfold psiPin at h
  set s := 1 / (n : ℝ) + 1 / (n : ℝ)
  set c := max (1 / (n : ℝ)) (1 / (n : ℝ))
  set a := β * ρbar * c with hadef
  set b2 := β * v ^ 2 * s with hbdef
  have ha : 0 < a := by positivity
  have hb : 0 < b2 := by positivity
  have key : ∀ x y : ℝ, 0 ≤ x → 0 < y → -(x ^ 2 / y) ≤ x - (x + y) * Real.log (1 + x / y) := fun x y hx hy => by
    linarith [pinelis_ineq x y hx hy]
  have hE := key (t / a) (b2 / a ^ 2) (div_nonneg ht ha.le) (div_pos hb (by positivity))
  have hxy : t / a / (b2 / a ^ 2) = t * a / b2 := by field_simp
  have hx2 : (t / a) ^ 2 / (b2 / a ^ 2) = t ^ 2 / b2 := by field_simp
  rw [hxy, hx2] at hE
  have h2 : 2 * Real.exp (-(t ^ 2 / b2)) ≤ Real.exp (-(n : ℝ)) :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hE) (by norm_num)).trans h
  have h3 : Real.exp (-(t ^ 2 / b2)) < Real.exp (-(n : ℝ)) := by
    have := Real.exp_pos (-(t ^ 2 / b2)); linarith
  have h4 := Real.exp_lt_exp.1 h3
  have h5 : (n : ℝ) * b2 < t ^ 2 := by
    have : (n : ℝ) < t ^ 2 / b2 := by linarith
    rwa [lt_div_iff₀ hb] at this
  have h6 : (n : ℝ) * b2 = 2 * β * v ^ 2 := by rw [hbdef, hs]; field_simp
  have h7 : 2 * v ^ 2 ≤ 2 * β * v ^ 2 := by nlinarith [sq_nonneg v]
  have h8 : (√2 * v) ^ 2 < t ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; linarith
  by_contra hle
  push_neg at hle
  have := pow_le_pow_left₀ ht hle 2
  linarith

theorem ratecond_sharp : Claims.ratecond_sharp := by
  intro κ ρbar n hκ hρ hn
  have hall : ∀ t : ℝ, 0 ≤ t →
      psiH κ (√2 * κ) ρbar 1 (1 / (n : ℝ) + 1 / (n : ℝ)) (max (1 / (n : ℝ)) (1 / (n : ℝ))) t ≤
        Real.exp (-(n : ℝ)) → √2 * κ < t := by
    intro t ht h
    rcases min_le_iff.1 h with h1 | h1
    · have := ratecond_mcd κ (√2 * κ) 1 t n hκ.le (by positivity) le_rfl hn h1
      have hpos : 0 < √(1 * κ ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ))) := Real.sqrt_pos.2 (by
        have := s_pos hn; positivity)
      linarith
    · exact ratecond_pin κ ρbar 1 t n hκ hρ le_rfl ht hn h1
  have hmem : √(1 * κ ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ))) + 1 * (√2 * κ) ∈
      {t : ℝ | 0 ≤ t ∧ psiH κ (√2 * κ) ρbar 1 (1 / (n : ℝ) + 1 / (n : ℝ)) (max (1 / (n : ℝ)) (1 / (n : ℝ))) t ≤
        Real.exp (-(n : ℝ))} := by
    refine ⟨by positivity, (min_le_left _ _).trans (le_of_eq ?_)⟩
    unfold psiMcD
    congr 1
    have hmax : max (√(1 * κ ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ))) + 1 * (√2 * κ) -
        √(1 * κ ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ)))) 0 = √2 * κ := by
      rw [add_sub_cancel_left, one_mul]; exact max_eq_left (by positivity)
    have hk : (√2 * κ) ^ 2 = 2 * κ ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
    have hn' : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      exact this.ne'
    rw [hmax, hk, s_eq]
    field_simp
  refine ⟨⟨_, hmem⟩, hall, ?_⟩
  unfold sharpZero
  exact le_csInf ⟨_, hmem⟩ fun t ht => (hall t ht.1 ht.2).le

theorem ratecond_zero : Claims.ratecond_zero := by
  intro 𝒳 H _ _ _ _ _ φ κ D n ι s hs τ hφ hκ hD hn hτ
  have hmin : ∀ α ∈ Ico (0 : ℝ) 1, D ≤ s.inf' hs fun i => τ i α := fun α hα =>
    Finset.le_inf' hs _ fun i hi => (hτ i hi).2.trans ((hτ i hi).1 ⟨le_rfl, one_pos⟩ hα hα.1)
  refine ⟨hmin, fun x y => ?_⟩
  have h0 : (0 : ℝ) ∈ crossSet (Demp φ x y) (fun α => s.inf' hs fun i => τ i α) :=
    ⟨⟨le_rfl, one_pos⟩, (Demp_le_D hφ hD hn hn x y ⟨le_rfl, one_pos⟩).trans (hmin 0 ⟨le_rfl, one_pos⟩)⟩
  exact le_antisymm (alphaHat_le_of_mem h0) (alphaHat_nonneg ⟨0, h0⟩)

theorem ratecond_noconv : Claims.ratecond_noconv := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D τ hφ hκ hD hτ htv e he het
  rintro ⟨E, -, hE, hlim⟩
  have hzero : ∀ n, 1 ≤ n → ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin n => Q)) (E n) = 0 := by
    intro n hn
    have hα : ∀ x y : Fin n → 𝒳, alphaHat (Demp φ x y) (τ n) = 0 := fun x y => by
      have h0 : (0 : ℝ) ∈ crossSet (Demp φ x y) (τ n) :=
        ⟨⟨le_rfl, one_pos⟩, (Demp_le_D hφ hD hn hn x y ⟨le_rfl, one_pos⟩).trans (hτ n hn 0 ⟨le_rfl, one_pos⟩)⟩
      exact le_antisymm (alphaHat_le_of_mem h0) (alphaHat_nonneg ⟨0, h0⟩)
    have : E n = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun z hz => ?_
      have h := hE n hz
      simp only [mem_setOf_eq, hα z.1 z.2, zero_sub, abs_neg] at h
      rw [abs_of_nonneg (StatFormal.Distances.tvDist_nonneg P Q)] at h
      linarith
    rw [this, measure_empty]
  have h0 : Tendsto (fun n => ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin n => Q)) (E n))
      atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun n hn => (hzero n hn).symm⟩)
  exact zero_ne_one (tendsto_nhds_unique h0 hlim)

theorem ratecond_gauss : Claims.ratecond_gauss := by
  intro 𝒳 H _ _ _ _ _ φ κ ρbar e₁ e₂ n τP τS τA hφ hκ hD hκ0 hρ he1 he2 hn hPm hP0 hSm hS0 hAm hA0
  have hsq := Real.sqrt_pos.2 (s_pos hn)
  have hP : √2 * κ < τP 0 := by
    rw [hP0, dterm hn]
    have : 0 < κ * √(1 / (n : ℝ) + 1 / (n : ℝ)) := mul_pos hκ0 hsq
    linarith
  have hS : √2 * κ ≤ τS 0 := ((ratecond_sharp κ ρbar n hκ0 hρ hn).2.2).trans hS0
  have hA : √2 * κ < τA 0 := by
    rw [hA0, dterm hn]
    have h1 : 0 < 2 * κ * √(1 / (n : ℝ) + 1 / (n : ℝ)) := by positivity
    have h2 : 0 ≤ 2 * κ * (e₁ + e₂) := by positivity
    linarith
  have z0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, one_pos⟩
  have hmin : ∀ α ∈ Ico (0 : ℝ) 1, √2 * κ ≤ min (min (τP α) (τS α)) (τA α) := fun α hα => by
    have a1 := hPm z0 hα hα.1
    have a2 := hSm z0 hα hα.1
    have a3 := hAm z0 hα hα.1
    simp only [le_min_iff]
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  refine ⟨hmin, fun x y => ?_⟩
  have h0 : (0 : ℝ) ∈ crossSet (Demp φ x y) (fun α => min (min (τP α) (τS α)) (τA α)) :=
    ⟨z0, (Demp_le_D hφ hD hn hn x y z0).trans (hmin 0 z0)⟩
  exact le_antisymm (alphaHat_le_of_mem h0) (alphaHat_nonneg ⟨0, h0⟩)

/-! ### The polynomial case of `thm:rate` -/

theorem log_four_le_two : Real.log 4 ≤ 2 := by
  have h : (4 : ℝ) ≤ Real.exp 2 := by
    have h1 := Real.add_one_le_exp 1
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  exact (Real.log_le_log (by norm_num) h).trans_eq (Real.log_exp 2)

theorem rn_le_rate {κ α d L : ℝ} {M k : ℕ} (hκ : 0 ≤ κ) (hα : α < 1) (hd : 0 < d) (hL1 : 1 ≤ L)
    (hlog : Real.log (4 / d) ≤ 2 * L) (hM : 1 ≤ M) (hMk : M ≤ k) :
    rn κ α (d / 2) k ≤ 6 * (κ / (1 - α)) * √(L / M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hMk' : (M : ℝ) ≤ k := by exact_mod_cast hMk
  have hk' : (0 : ℝ) < k := hM'.trans_le hMk'
  have hβ : 0 ≤ κ / (1 - α) := div_nonneg hκ (by linarith)
  have hlog4 : Real.log (2 / (d / 2)) = Real.log (4 / d) := by congr 1; field_simp; ring
  unfold rn
  rw [hlog4]
  have hLM : 0 ≤ L / M := by positivity
  have e1 : 4 / √(k : ℝ) ≤ 4 * √(L / M) := by
    have h1 : 4 / √(k : ℝ) ≤ 4 / √(M : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hM') (Real.sqrt_le_sqrt hMk')
    have h2 : 4 / √(M : ℝ) = 4 * √(1 / M) := by rw [Real.sqrt_div' 1 hM'.le, Real.sqrt_one]; ring
    have h3 : √(1 / (M : ℝ)) ≤ √(L / M) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hL1 hM'.le)
    linarith
  have e2 : √(2 * Real.log (4 / d) / k) ≤ 2 * √(L / M) := by
    have h1 : 2 * Real.log (4 / d) / k ≤ 4 * (L / M) := by
      rcases le_total 0 (Real.log (4 / d)) with h | h
      · calc 2 * Real.log (4 / d) / k ≤ 2 * Real.log (4 / d) / M :=
              div_le_div_of_nonneg_left (by positivity) hM' hMk'
          _ ≤ 2 * (2 * L) / M := div_le_div_of_nonneg_right (by linarith) hM'.le
          _ = 4 * (L / M) := by ring
      · have : 2 * Real.log (4 / d) / k ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hk'.le
        have : 0 ≤ 4 * (L / M) := by positivity
        linarith
    calc √(2 * Real.log (4 / d) / k) ≤ √(4 * (L / M)) := Real.sqrt_le_sqrt h1
      _ = 2 * √(L / M) := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc κ / (1 - α) * (4 / √(k : ℝ) + √(2 * Real.log (4 / d) / k))
      ≤ κ / (1 - α) * (4 * √(L / M) + 2 * √(L / M)) := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hβ
    _ = 6 * (κ / (1 - α)) * √(L / M) := by ring

theorem log_one_div_nonneg {d : ℝ} (hd0 : 0 < d) (hd1 : d < 1) : 0 ≤ Real.log (1 / d) := by
  rw [one_div, Real.log_inv]
  linarith [Real.log_nonpos hd0.le hd1.le]

theorem log_four_div_eq {d : ℝ} (hd0 : 0 < d) : Real.log (4 / d) = Real.log 4 + Real.log (1 / d) := by
  rw [show (4 : ℝ) / d = 4 * (1 / d) by ring, Real.log_mul (by norm_num) (one_div_pos.2 hd0).ne']

theorem rate_poly : Claims.rate_poly := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ δ' c₀ γ τ τA n m hφ hκ htv hc0 hγ hmarg hδ0 hδ1 hδ'0 hδ'1 hn hm hv hlow ht
  set T := StatFormal.Distances.tvDist P Q
  have hTI := tv_mem_Ico P Q htv
  set t := τ T + τA T with htdef
  have ht0 : 0 ≤ t := add_nonneg (hv.1 T hTI) (hlow.1 T hTI)
  have htc : 0 ≤ t / c₀ := div_nonneg ht0 hc0.le
  set ε := (t / c₀) ^ (1 / γ) with hεdef
  have hε0 : 0 ≤ ε := Real.rpow_nonneg htc _
  have hωε : c₀ * ε ^ γ = t := by
    rw [hεdef, ← Real.rpow_mul htc, one_div, inv_mul_cancel₀ hγ.ne', Real.rpow_one]
    field_simp
  have hεT : ε ≤ T := by
    have h1 : t / c₀ ≤ T ^ γ := by rw [div_le_iff₀ hc0]; linarith
    have h2 := Real.rpow_le_rpow htc h1 (by positivity : (0 : ℝ) ≤ 1 / γ)
    rwa [← Real.rpow_mul hTI.1, mul_one_div_cancel hγ.ne', Real.rpow_one] at h2
  have hmono : StrictMonoOn (fun e : ℝ => c₀ * e ^ γ) (Icc 0 T) := fun a ha b hb hab =>
    mul_lt_mul_of_pos_left (Real.rpow_lt_rpow ha.1 hab hγ) hc0
  obtain ⟨E, hEm, hEp, hE⟩ := two_events hφ hδ0.le hδ'0.le hn hm hv P Q htv hlow
  refine ⟨⟨E, hEm, hEp, fun z hz => ?_⟩, fun hτle hτAle => ?_⟩
  · obtain ⟨h1, h2⟩ :=
      rate_det (ω := fun e : ℝ => c₀ * e ^ γ) P Q htv z (hE z hz).1 (hE z hz).2 hv.2.1 hlow.2.1 hmono hmarg
        ⟨hε0, hεT⟩ hωε
    simp only [mem_setOf_eq]
    rw [abs_le]
    constructor <;> linarith
  · obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
    have hκ0 := kappa_nonneg_of hκ x0
    set L := 1 + Real.log (1 / δ) + Real.log (1 / δ')
    have hl1 := log_one_div_nonneg hδ0 hδ1
    have hl2 := log_one_div_nonneg hδ'0 hδ'1
    have hL1 : 1 ≤ L := by simp only [L]; linarith
    have h4 := log_four_le_two
    have hlogδ : Real.log (4 / δ) ≤ 2 * L := by rw [log_four_div_eq hδ0]; simp only [L]; linarith
    have hlogδ' : Real.log (4 / δ') ≤ 2 * L := by rw [log_four_div_eq hδ'0]; simp only [L]; linarith
    have hM : 1 ≤ min n m := le_min hn hm
    set β := κ / (1 - T)
    have a1 := rn_le_rate hκ0 htv hδ0 hL1 hlogδ hM (min_le_left n m)
    have a2 := rn_le_rate hκ0 htv hδ0 hL1 hlogδ hM (min_le_right n m)
    have a3 := rn_le_rate hκ0 htv hδ'0 hL1 hlogδ' hM (min_le_left n m)
    have a4 := rn_le_rate hκ0 htv hδ'0 hL1 hlogδ' hM (min_le_right n m)
    have htle : t ≤ 24 * β * √(L / (min n m : ℕ)) := by
      have : t ≤ tau κ T δ n m + tau κ T δ' n m := add_le_add hτle hτAle
      simp only [tau] at this
      linarith
    have hfin : t / c₀ ≤ 24 * κ / (c₀ * (1 - T)) * √(L / (min n m : ℕ)) := by
      have h1T : 0 < 1 - T := by linarith
      rw [div_le_iff₀ hc0]
      calc t ≤ 24 * β * √(L / (min n m : ℕ)) := htle
        _ = 24 * κ / (c₀ * (1 - T)) * √(L / (min n m : ℕ)) * c₀ := by
          simp only [β]; field_simp
    exact Real.rpow_le_rpow htc hfin (by positivity)

end StatFormal.Wave30tu
