import StatFormal.Archive.OTFD.Wave12a.Statements
import StatFormal.Archive.OTFD.Wave6b.RouteRegion

/-!
# Route: R `thm:entropic` (and the unconditional `thm:region-breakdown`)

Untrusted proof file.
* `piCond_ratio` is `eq:ratio2` without division: `π_j(u)π_k(v) = π_k(u)π_j(v) e^{−⟨u−v, z_k−z_j⟩/ε}`.
* (a) `weight_le`: if `π_k(u₀) > (n/κ)e^{−(t‖z_k‖−DB)/ε}`, every unreplaced `π_j` is `< κ/n` on `H = H_{t,D}(e)`,
  `e = z_k/‖z_k‖`, so the replaced points carry mass `> (1−κ)δ = ℓ/n` on `H`, against `eq:mass`.
  `phi_bound` is the bound `x min{1, Ce^{−tx/ε}} ≤ ε(log C + 1)/t` (via `e^y ≥ 1 + y`).
* (b) `core_b`: `C(u₀)A(u) ≤ e^{DB/ε}A(u₀)C(u)` on `S`, summed over all pairs (no division, no equal weights
  needed); some `u ∈ S` has `A(u) ≥ η` by `eq:mass`; hence `A(u₀) ≥ γ/(1+γ)`.
* `bp_bracket`: generic bracket of `def:bp` between the two thresholds.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ENNReal Topology

namespace StatFormal.OTFD.Wave12a

open StatFormal.OTFDR (piCond Qhat)
open StatFormal.OTFDR.Lift (Contam Explodes BP)
open StatFormal.OTFD.Wave1 (HtD tukeyDepth regionDepth)
open StatFormal.OTFD.Wave6b (dMinus halfMass IsEntPot entBound EntropicA EntropicB EntSetting regionSup
  piCond_nonneg piCond_le_one)

variable {K : ℕ}

/-! ### Softmax facts -/

section Softmax
variable {n : ℕ} (z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) (ε : ℝ)

lemma denom_pos (hn : 0 < n) (u : EuclideanSpace ℝ (Fin K)) :
    0 < ∑ j, Real.exp ((f j - ‖u - z j‖ ^ 2 / 2) / ε) :=
  Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

lemma piCond_pos (u : EuclideanSpace ℝ (Fin K)) (i : Fin n) : 0 < piCond z f ε u i :=
  div_pos (Real.exp_pos _) (denom_pos z f ε (Fin.pos i) u)

lemma sum_piCond (hn : 0 < n) (u : EuclideanSpace ℝ (Fin K)) : ∑ i, piCond z f ε u i = 1 := by
  unfold piCond
  rw [← Finset.sum_div, div_self (denom_pos z f ε hn u).ne']

lemma sum_compl_piCond (hn : 0 < n) (O : Finset (Fin n)) (u : EuclideanSpace ℝ (Fin K)) :
    ∑ i ∈ O, piCond z f ε u i + ∑ i ∈ Oᶜ, piCond z f ε u i = 1 := by
  rw [Finset.sum_add_sum_compl]; exact sum_piCond z f ε hn u

lemma piCond_ratio (u v : EuclideanSpace ℝ (Fin K)) (j k : Fin n) :
    piCond z f ε u j * piCond z f ε v k =
      piCond z f ε u k * piCond z f ε v j * Real.exp (-⟪u - v, z k - z j⟫_ℝ / ε) := by
  unfold piCond
  have key : Real.exp ((f j - ‖u - z j‖ ^ 2 / 2) / ε) * Real.exp ((f k - ‖v - z k‖ ^ 2 / 2) / ε) =
      Real.exp ((f k - ‖u - z k‖ ^ 2 / 2) / ε) * Real.exp ((f j - ‖v - z j‖ ^ 2 / 2) / ε) *
        Real.exp (-⟪u - v, z k - z j⟫_ℝ / ε) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real]
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [div_mul_div_comm, div_mul_div_comm, div_mul_eq_mul_div, key]

lemma continuous_piCond (i : Fin n) : Continuous fun u : EuclideanSpace ℝ (Fin K) => piCond z f ε u i := by
  have hc : ∀ j, Continuous fun u : EuclideanSpace ℝ (Fin K) => Real.exp ((f j - ‖u - z j‖ ^ 2 / 2) / ε) :=
    fun j => by fun_prop
  exact (hc i).div (continuous_finsetSum _ fun j _ => hc j) fun u => (denom_pos z f ε (Fin.pos i) u).ne'

lemma integrable_piCond (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsFiniteMeasure ν] (i : Fin n) :
    Integrable (fun u => piCond z f ε u i) ν :=
  Integrable.of_bound (continuous_piCond z f ε i).aestronglyMeasurable 1
    (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (piCond_nonneg z f ε u i)]; exact piCond_le_one z f ε u i)

lemma integrable_sum_piCond (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsFiniteMeasure ν] (O : Finset (Fin n)) :
    Integrable (fun u => ∑ i ∈ O, piCond z f ε u i) ν :=
  integrable_finsetSum O fun i _ => integrable_piCond z f ε ν i

lemma mass_sum (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsFiniteMeasure ν] (hf : IsEntPot ν ε z f)
    (O : Finset (Fin n)) : ∫ u, ∑ i ∈ O, piCond z f ε u i ∂ν = O.card / n := by
  rw [integral_finsetSum O fun i _ => integrable_piCond z f ε ν i]
  rw [Finset.sum_congr rfl fun i _ => hf i, Finset.sum_const, nsmul_eq_mul]
  ring

lemma sum_piCond_le_one (O : Finset (Fin n)) (u : EuclideanSpace ℝ (Fin K)) :
    ∑ i ∈ O, piCond z f ε u i ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Finset.eq_empty_of_isEmpty O]
  calc ∑ i ∈ O, piCond z f ε u i ≤ ∑ i, piCond z f ε u i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ O) fun i _ _ => piCond_nonneg z f ε u i
    _ = 1 := sum_piCond z f ε hn u

end Softmax

/-! ### Measurable sets -/

lemma measurableSet_HtD (u₀ e : EuclideanSpace ℝ (Fin K)) (t D : ℝ) : MeasurableSet (HtD u₀ t D e) := by
  have : HtD u₀ t D e = {u | t ≤ ⟪u - u₀, e⟫_ℝ} ∩ {u | ‖u - u₀‖ ≤ D} := rfl
  rw [this]
  exact (measurableSet_le measurable_const (by fun_prop)).inter (measurableSet_le (by fun_prop) measurable_const)

/-! ### Elementary bounds -/

/-- `ρx ≤ ε(log C + 1)/t` whenever `0 ≤ ρ ≤ min{1, C e^{−tx/ε}}`, `C ≥ 1`. -/
lemma phi_bound {x ρ C t ε : ℝ} (hx : 0 ≤ x) (hρ1 : ρ ≤ 1) (ht : 0 < t) (hε : 0 < ε)
    (hC : 1 ≤ C) (hρ : ρ ≤ C * Real.exp (-(t * x) / ε)) : ρ * x ≤ ε * (Real.log C + 1) / t := by
  set a := Real.log C with ha_def
  have ha : 0 ≤ a := Real.log_nonneg hC
  by_cases hxc : x ≤ ε * (a + 1) / t
  · calc ρ * x ≤ 1 * x := mul_le_mul_of_nonneg_right hρ1 hx
      _ ≤ _ := by linarith
  · push_neg at hxc
    set y := t * x / ε - a with hy_def
    have h1 : ε * (a + 1) < t * x := by
      have := (div_lt_iff₀ ht).mp hxc; linarith
    have hy : 1 < y := by
      have : a + 1 < t * x / ε := by rw [lt_div_iff₀ hε]; linarith
      linarith
    have hCe : C * Real.exp (-(t * x) / ε) = Real.exp (-y) := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < C), ← Real.exp_add, ← ha_def]
      congr 1; rw [hy_def]; ring
    have hxy : x = ε * (a + y) / t := by
      rw [hy_def]; field_simp; ring
    have hexp := Real.add_one_le_exp y
    have key : (a + y) * Real.exp (-y) ≤ a + 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos y)]
      nlinarith
    calc ρ * x ≤ Real.exp (-y) * x := mul_le_mul_of_nonneg_right (hCe ▸ hρ) hx
      _ = ε * ((a + y) * Real.exp (-y)) / t := by rw [hxy]; ring
      _ ≤ ε * (a + 1) / t :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left key hε.le) ht.le

/-! ### Setup of (a) -/

section SetupA
variable {n : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν]
  {ℓ : ℕ} {u₀ : EuclideanSpace ℝ (Fin K)} {t D : ℝ}

structure SetupA (ν : Measure (EuclideanSpace ℝ (Fin K))) (n ℓ : ℕ) (u₀ : EuclideanSpace ℝ (Fin K))
    (t D : ℝ) : Prop where
  n_pos : 0 < n
  δ_pos : 0 < (halfMass ν u₀ t D).toReal
  δ_le : ∀ e : EuclideanSpace ℝ (Fin K), ‖e‖ = 1 → (halfMass ν u₀ t D).toReal ≤ ν.real (HtD u₀ t D e)
  t_le_D : t ≤ D
  κ_pos : 0 < kappa n ℓ (halfMass ν u₀ t D).toReal
  κ_le : kappa n ℓ (halfMass ν u₀ t D).toReal ≤ 1
  ℓ_lt : (ℓ : ℝ) < n
  ℓ_eq : (1 - kappa n ℓ (halfMass ν u₀ t D).toReal) * (halfMass ν u₀ t D).toReal = ℓ / n

lemma setupA (hℓ : (ℓ : ℝ) < n * (halfMass ν u₀ t D).toReal) : SetupA ν n ℓ u₀ t D := by
  set δ := (halfMass ν u₀ t D).toReal with hδ
  have hnδ : 0 < (n : ℝ) * δ := lt_of_le_of_lt (Nat.cast_nonneg ℓ) hℓ
  have hδ0 : 0 ≤ δ := ENNReal.toReal_nonneg
  have hn0 : (0 : ℝ) < n := by
    rcases (Nat.cast_nonneg n : (0 : ℝ) ≤ n).eq_or_lt with h | h
    · rw [← h, zero_mul] at hnδ; exact absurd hnδ (lt_irrefl 0)
    · exact h
  have hδpos : 0 < δ := pos_of_mul_pos_right hnδ hn0.le
  have hne : halfMass ν u₀ t D ≠ ⊤ := fun h => by rw [hδ, h] at hδpos; simp at hδpos
  have hlt : halfMass ν u₀ t D < ⊤ := lt_top_iff_ne_top.mpr hne
  obtain ⟨e₁, he₁, -⟩ : ∃ e : EuclideanSpace ℝ (Fin K), ∃ _ : ‖e‖ = 1, ν (HtD u₀ t D e) < ⊤ := by
    unfold halfMass at hlt; simpa only [iInf_lt_iff] using hlt
  have hδle : ∀ e : EuclideanSpace ℝ (Fin K), ‖e‖ = 1 → δ ≤ ν.real (HtD u₀ t D e) := fun e he =>
    ENNReal.toReal_mono (measure_ne_top ν _) (iInf₂_le e he)
  have hδ1 : δ ≤ 1 := (hδle e₁ he₁).trans measureReal_le_one
  have htD : t ≤ D := by
    by_contra hDt
    push_neg at hDt
    have hempty : HtD u₀ t D e₁ = ∅ := by
      ext u
      simp only [HtD, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intro h1
      have h2 : ⟪u - u₀, e₁⟫_ℝ ≤ ‖u - u₀‖ := by
        have := real_inner_le_norm (u - u₀) e₁; rwa [he₁, mul_one] at this
      linarith
    have := hδle e₁ he₁
    rw [hempty, measureReal_empty] at this
    linarith
  have hℓn : (ℓ : ℝ) < n := lt_of_lt_of_le hℓ (by nlinarith)
  have hq : (ℓ : ℝ) / (n * δ) < 1 := by rw [div_lt_one hnδ]; exact hℓ
  have hq0 : 0 ≤ (ℓ : ℝ) / (n * δ) := div_nonneg (Nat.cast_nonneg _) hnδ.le
  refine ⟨by exact_mod_cast hn0, hδpos, hδle, htD, ?_, ?_, hℓn, ?_⟩
  · unfold kappa; linarith
  · unfold kappa; linarith
  · unfold kappa
    rw [← hδ]
    field_simp
    ring

end SetupA

/-! ### (a): the weight bound and the displacement bound -/

section PartA
variable {n : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν]

theorem weight_le {ε : ℝ} (hε : 0 < ε) (z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ)
    (hf : IsEntPot ν ε z f) (O : Finset (Fin n)) {ℓ : ℕ} (hO : O.card ≤ ℓ) {B : ℝ}
    (hB : ∀ j ∉ O, ‖z j‖ ≤ B) (u₀ : EuclideanSpace ℝ (Fin K)) {t D : ℝ} (ht : 0 < t)
    (hℓ : (ℓ : ℝ) < n * (halfMass ν u₀ t D).toReal) (k : Fin n) (hk : k ∈ O) :
    piCond z f ε u₀ k ≤
      n / kappa n ℓ (halfMass ν u₀ t D).toReal * Real.exp (-(t * ‖z k‖ - D * B) / ε) := by
  have hs := setupA ν hℓ
  set δ := (halfMass ν u₀ t D).toReal with hδ
  set κ := kappa n ℓ δ with hκ
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hs.n_pos
  have hD : 0 ≤ D := ht.le.trans hs.t_le_D
  -- an unreplaced index exists, so `B ≥ 0`
  have hB0 : 0 ≤ B := by
    have hcard : O.card < n := by
      have : (O.card : ℝ) < n := lt_of_le_of_lt (by exact_mod_cast hO) hs.ℓ_lt
      exact_mod_cast this
    obtain ⟨j, -, hj⟩ : ∃ j ∈ Finset.univ, j ∉ O := by
      by_contra hcon
      push_neg at hcon
      have : Finset.univ ⊆ O := fun j hj => hcon j hj
      have := Finset.card_le_card this
      simp at this; omega
    exact (norm_nonneg _).trans (hB j hj)
  have hnκ : 1 ≤ (n : ℝ) / κ := by rw [le_div_iff₀ hs.κ_pos]; nlinarith [hs.κ_le]
  set ρ := piCond z f ε u₀ k with hρ
  set Ek := Real.exp (-(t * ‖z k‖ - D * B) / ε) with hEk
  by_cases hz : z k = 0
  · have : 1 ≤ Ek := by
      rw [hEk, hz, norm_zero, mul_zero, zero_sub, neg_neg]
      exact Real.one_le_exp (div_nonneg (mul_nonneg hD hB0) hε.le)
    calc ρ ≤ 1 := piCond_le_one z f ε u₀ k
      _ ≤ n / κ * Ek := by nlinarith
  by_contra hlt
  push_neg at hlt
  have hρpos : 0 < ρ := piCond_pos z f ε u₀ k
  have hzk : 0 < ‖z k‖ := norm_pos_iff.mpr hz
  set e : EuclideanSpace ℝ (Fin K) := ‖z k‖⁻¹ • z k with he_def
  have he : ‖e‖ = 1 := by rw [he_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hzk.ne']
  set H := HtD u₀ t D e with hH
  set q := n * Ek / ρ with hq
  have hqκ : q < κ := by
    rw [hq, div_lt_iff₀ hρpos]
    have := (div_lt_iff₀' hs.κ_pos).mp (by simpa [div_mul_eq_mul_div] using hlt)
    linarith
  -- on `H`, the unreplaced weights are small
  have hsmall : ∀ u ∈ H, 1 - q ≤ ∑ i ∈ O, piCond z f ε u i := by
    intro u hu
    have hj : ∀ j ∈ Oᶜ, piCond z f ε u j ≤ Ek / ρ := by
      intro j hj
      have hjB : ‖z j‖ ≤ B := hB j (Finset.mem_compl.mp hj)
      have hinner : t * ‖z k‖ - D * B ≤ ⟪u - u₀, z k - z j⟫_ℝ := by
        have h1 : ⟪u - u₀, z k⟫_ℝ = ‖z k‖ * ⟪u - u₀, e⟫_ℝ := by
          rw [he_def, inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hzk.ne', one_mul]
        have h2 : t ≤ ⟪u - u₀, e⟫_ℝ := hu.1
        have h3 : ⟪u - u₀, z j⟫_ℝ ≤ D * B := by
          refine (real_inner_le_norm _ _).trans ?_
          exact mul_le_mul hu.2 hjB (norm_nonneg _) hD
        rw [inner_sub_right, h1]
        nlinarith
      have hexp : Real.exp (-⟪u - u₀, z k - z j⟫_ℝ / ε) ≤ Ek := by
        rw [hEk]; apply Real.exp_le_exp.mpr
        exact div_le_div_of_nonneg_right (by linarith) hε.le
      have hr := piCond_ratio z f ε u u₀ j k
      rw [le_div_iff₀ hρpos]
      calc piCond z f ε u j * ρ = piCond z f ε u k * piCond z f ε u₀ j *
            Real.exp (-⟪u - u₀, z k - z j⟫_ℝ / ε) := hr
        _ ≤ 1 * 1 * Ek := by
            apply mul_le_mul (mul_le_mul (piCond_le_one _ _ _ _ _) (piCond_le_one _ _ _ _ _)
              (piCond_nonneg _ _ _ _ _) zero_le_one) hexp (Real.exp_pos _).le (by norm_num)
        _ = Ek := by ring
    have hsumC : ∑ i ∈ Oᶜ, piCond z f ε u i ≤ q := by
      calc ∑ i ∈ Oᶜ, piCond z f ε u i ≤ ∑ _i ∈ Oᶜ, Ek / ρ := Finset.sum_le_sum hj
        _ = (Oᶜ.card : ℝ) * (Ek / ρ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ n * (Ek / ρ) := by
            apply mul_le_mul_of_nonneg_right _ (div_nonneg (Real.exp_pos _).le hρpos.le)
            have := Finset.card_le_univ Oᶜ
            simp only [Fintype.card_fin] at this
            exact_mod_cast this
        _ = q := by rw [hq]; ring
    have := sum_compl_piCond z f ε hs.n_pos O u
    linarith
  -- integrate
  have hHm : MeasurableSet H := measurableSet_HtD u₀ e t D
  have hint := integrable_sum_piCond z f ε ν O
  have hupper : ∫ u, ∑ i ∈ O, piCond z f ε u i ∂ν ≤ ℓ / n := by
    rw [mass_sum z f ε ν hf O]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hO) (Nat.cast_nonneg n)
  have hlower : (1 - q) * ν.real H ≤ ∫ u, ∑ i ∈ O, piCond z f ε u i ∂ν := by
    calc (1 - q) * ν.real H = ∫ _u in H, (1 - q) ∂ν := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ u in H, ∑ i ∈ O, piCond z f ε u i ∂ν :=
          setIntegral_mono_on (integrableOn_const (measure_ne_top _ _)) hint.integrableOn hHm hsmall
      _ ≤ ∫ u, ∑ i ∈ O, piCond z f ε u i ∂ν :=
          setIntegral_le_integral hint (ae_of_all _ fun u =>
            Finset.sum_nonneg fun i _ => piCond_nonneg z f ε u i)
  have hδH : δ ≤ ν.real H := hs.δ_le e he
  have h1q : 1 - κ < 1 - q := by linarith
  have h1κ : 0 ≤ 1 - κ := by linarith [hs.κ_le]
  have : (1 - κ) * δ < (1 - q) * ν.real H := by
    calc (1 - κ) * δ < (1 - q) * δ := mul_lt_mul_of_pos_right h1q hs.δ_pos
      _ ≤ (1 - q) * ν.real H := mul_le_mul_of_nonneg_left hδH (by linarith)
  rw [hs.ℓ_eq] at this
  linarith

theorem displacement_le {ε εhi : ℝ} (hε : 0 < ε) (hεε : ε ≤ εhi) (z : Fin n → EuclideanSpace ℝ (Fin K))
    (f : Fin n → ℝ) (hf : IsEntPot ν ε z f) (O : Finset (Fin n)) {ℓ : ℕ} (hO : O.card ≤ ℓ) {B : ℝ}
    (hB : ∀ j ∉ O, ‖z j‖ ≤ B) (u₀ : EuclideanSpace ℝ (Fin K)) {t D : ℝ} (ht : 0 < t)
    (hℓ : (ℓ : ℝ) < n * (halfMass ν u₀ t D).toReal) :
    ‖Qhat z f ε u₀‖ ≤ entBound n ℓ t D B εhi (halfMass ν u₀ t D).toReal := by
  have hs := setupA ν hℓ
  set δ := (halfMass ν u₀ t D).toReal with hδ
  set κ := kappa n ℓ δ with hκ
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hs.n_pos
  have hD : 0 ≤ D := ht.le.trans hs.t_le_D
  have hB0 : 0 ≤ B := by
    have hcard : O.card < n := by
      have : (O.card : ℝ) < n := lt_of_le_of_lt (by exact_mod_cast hO) hs.ℓ_lt
      exact_mod_cast this
    obtain ⟨j, -, hj⟩ : ∃ j ∈ Finset.univ, j ∉ O := by
      by_contra hcon
      push_neg at hcon
      have : Finset.univ ⊆ O := fun j hj => hcon j hj
      have := Finset.card_le_card this
      simp at this; omega
    exact (norm_nonneg _).trans (hB j hj)
  have hnκ : 1 ≤ (n : ℝ) / κ := by rw [le_div_iff₀ hs.κ_pos]; nlinarith [hs.κ_le]
  have hlog : 0 ≤ Real.log (n / κ) := Real.log_nonneg hnκ
  set c := (D * B + ε * Real.log (n / κ) + ε) / t with hc
  set chi := (D * B + εhi * Real.log (n / κ) + εhi) / t with hchi
  have hcc : c ≤ chi := by
    rw [hc, hchi]; apply div_le_div_of_nonneg_right _ ht.le; nlinarith
  have hc0 : 0 ≤ c := div_nonneg (by positivity) ht.le
  -- each replaced point contributes at most `c`
  have hk : ∀ k ∈ O, piCond z f ε u₀ k * ‖z k‖ ≤ c := by
    intro k hkO
    have hw := weight_le ν hε z f hf O hO hB u₀ ht hℓ k hkO
    set C := n / κ * Real.exp (D * B / ε) with hC
    have hC1 : 1 ≤ C := by
      rw [hC]; nlinarith [Real.one_le_exp (div_nonneg (mul_nonneg hD hB0) hε.le)]
    have hw' : piCond z f ε u₀ k ≤ C * Real.exp (-(t * ‖z k‖) / ε) := by
      rw [hC, mul_assoc, ← Real.exp_add]
      convert hw using 3; ring
    have := phi_bound (norm_nonneg (z k)) (piCond_le_one z f ε u₀ k) ht hε hC1 hw'
    have hlogC : Real.log C = Real.log (n / κ) + D * B / ε := by
      rw [hC, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    rw [hlogC] at this
    calc piCond z f ε u₀ k * ‖z k‖ ≤ ε * (Real.log (n / κ) + D * B / ε + 1) / t := this
      _ = c := by rw [hc]; field_simp; ring
  -- split `Q̂`
  have hsplit : ‖Qhat z f ε u₀‖ ≤ ∑ i ∈ O, piCond z f ε u₀ i * ‖z i‖ + ∑ i ∈ Oᶜ, piCond z f ε u₀ i * ‖z i‖ := by
    unfold Qhat
    rw [Finset.sum_add_sum_compl]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (piCond_nonneg z f ε u₀ i)]
  have hO' : ∑ i ∈ O, piCond z f ε u₀ i * ‖z i‖ ≤ ℓ * c := by
    calc ∑ i ∈ O, piCond z f ε u₀ i * ‖z i‖ ≤ ∑ _i ∈ O, c := Finset.sum_le_sum hk
      _ = O.card * c := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ℓ * c := mul_le_mul_of_nonneg_right (by exact_mod_cast hO) hc0
  have hC' : ∑ i ∈ Oᶜ, piCond z f ε u₀ i * ‖z i‖ ≤ B := by
    calc ∑ i ∈ Oᶜ, piCond z f ε u₀ i * ‖z i‖ ≤ ∑ i ∈ Oᶜ, piCond z f ε u₀ i * B :=
          Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left (hB i (Finset.mem_compl.mp hi)) (piCond_nonneg z f ε u₀ i)
      _ = (∑ i ∈ Oᶜ, piCond z f ε u₀ i) * B := by rw [Finset.sum_mul]
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right (sum_piCond_le_one z f ε Oᶜ u₀) hB0
      _ = B := one_mul B
  have : ‖Qhat z f ε u₀‖ ≤ B + ℓ * chi := by
    nlinarith [mul_le_mul_of_nonneg_left hcc (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  unfold entBound
  rw [hchi] at this
  calc ‖Qhat z f ε u₀‖ ≤ B + ℓ * ((D * B + εhi * Real.log (n / κ) + εhi) / t) := this
    _ = B + ℓ * (D * B + εhi * Real.log (n / (1 - ℓ / (n * δ))) + εhi) / t := by
        rw [hκ, kappa]; ring

end PartA

/-! ### (b): co-located far points -/

section PartB
variable {n : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν]

theorem core_b {ε εlo : ℝ} (hεlo : 0 < εlo) (hεε : εlo ≤ ε) (z : Fin n → EuclideanSpace ℝ (Fin K))
    (f : Fin n → ℝ) (hf : IsEntPot ν ε z f) (O : Finset (Fin n)) (u₀ e : EuclideanSpace ℝ (Fin K))
    {R B D η : ℝ} (hR : 0 ≤ R) (hB0 : 0 ≤ B) (hD : 0 ≤ D) (hη : 0 < η) (he : ‖e‖ = 1)
    (hzO : ∀ k ∈ O, z k = R • e) (hB : ∀ j ∉ O, ‖z j‖ ≤ B)
    (hmass : ν.real {u | 0 < ⟪u - u₀, e⟫_ℝ} + ν.real {u | D < ‖u - u₀‖} + η < O.card / n) :
    R * (η * Real.exp (-(D * B) / εlo) / (1 + η * Real.exp (-(D * B) / εlo))) - B ≤
      ‖Qhat z f ε u₀‖ := by
  have hε : 0 < ε := lt_of_lt_of_le hεlo hεε
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hmass; linarith [measureReal_nonneg (μ := ν) (s := {u | 0 < ⟪u - u₀, e⟫_ℝ}),
        measureReal_nonneg (μ := ν) (s := {u | D < ‖u - u₀‖})]
    · exact h
  set A : EuclideanSpace ℝ (Fin K) → ℝ := fun u => ∑ i ∈ O, piCond z f ε u i with hA
  set C : EuclideanSpace ℝ (Fin K) → ℝ := fun u => ∑ i ∈ Oᶜ, piCond z f ε u i with hC
  have hAC : ∀ u, A u + C u = 1 := fun u => sum_compl_piCond z f ε hn O u
  have hA0 : ∀ u, 0 ≤ A u := fun u => Finset.sum_nonneg fun i _ => piCond_nonneg z f ε u i
  have hC0 : ∀ u, 0 ≤ C u := fun u => Finset.sum_nonneg fun i _ => piCond_nonneg z f ε u i
  -- some `u ∈ S` carries `A(u) ≥ η`
  set P := {u : EuclideanSpace ℝ (Fin K) | 0 < ⟪u - u₀, e⟫_ℝ} with hP
  set F := {u : EuclideanSpace ℝ (Fin K) | D < ‖u - u₀‖} with hF
  have hPm : MeasurableSet P := measurableSet_lt measurable_const (by fun_prop)
  have hFm : MeasurableSet F := measurableSet_lt measurable_const (by fun_prop)
  obtain ⟨u, huS1, huS2, huA⟩ : ∃ u, ⟪u - u₀, e⟫_ℝ ≤ 0 ∧ ‖u - u₀‖ ≤ D ∧ η ≤ A u := by
    by_contra hcon
    push_neg at hcon
    have hpt : ∀ u, A u ≤ P.indicator 1 u + F.indicator 1 u + η := by
      intro u
      by_cases huP : u ∈ P
      · rw [indicator_of_mem huP]
        have : A u ≤ 1 := sum_piCond_le_one z f ε O u
        have : 0 ≤ F.indicator (1 : EuclideanSpace ℝ (Fin K) → ℝ) u :=
          indicator_nonneg (fun _ _ => zero_le_one) u
        simp only [Pi.one_apply]; linarith
      by_cases huF : u ∈ F
      · rw [indicator_of_mem huF]
        have : A u ≤ 1 := sum_piCond_le_one z f ε O u
        have : 0 ≤ P.indicator (1 : EuclideanSpace ℝ (Fin K) → ℝ) u :=
          indicator_nonneg (fun _ _ => zero_le_one) u
        simp only [Pi.one_apply]; linarith
      rw [indicator_of_notMem huP, indicator_of_notMem huF]
      simp only [hP, hF, mem_setOf_eq, not_lt] at huP huF
      linarith [hcon u huP huF]
    have hint := integrable_sum_piCond z f ε ν O
    have hIP : Integrable (fun u => P.indicator (1 : EuclideanSpace ℝ (Fin K) → ℝ) u) ν :=
      (integrable_indicator_iff hPm).mpr (integrableOn_const (measure_ne_top _ _))
    have hIF : Integrable (fun u => F.indicator (1 : EuclideanSpace ℝ (Fin K) → ℝ) u) ν :=
      (integrable_indicator_iff hFm).mpr (integrableOn_const (measure_ne_top _ _))
    have hIPF : Integrable (fun u => P.indicator (1 : EuclideanSpace ℝ (Fin K) → ℝ) u +
        F.indicator (1 : EuclideanSpace ℝ (Fin K) → ℝ) u) ν := hIP.add hIF
    have hI : ∫ u, A u ∂ν ≤ ∫ u, (P.indicator 1 u + F.indicator 1 u + η) ∂ν :=
      integral_mono hint (hIPF.add (integrable_const η)) hpt
    have e1 : ∫ u, (P.indicator (1 : EuclideanSpace ℝ (Fin K) → ℝ) u + F.indicator 1 u + η) ∂ν =
        ν.real P + ν.real F + η := by
      rw [integral_add hIPF (integrable_const η), integral_add hIP hIF,
        integral_indicator_one hPm, integral_indicator_one hFm, integral_const, probReal_univ, one_smul]
    rw [e1] at hI
    have hmassA : ∫ u, A u ∂ν = O.card / n := mass_sum z f ε ν hf O
    rw [hmassA] at hI
    linarith
  -- the odds bound, summed over all pairs
  set G := Real.exp (D * B / εlo) with hG
  have hpair : ∀ k ∈ O, ∀ j ∈ Oᶜ,
      piCond z f ε u₀ j * piCond z f ε u k ≤ piCond z f ε u₀ k * piCond z f ε u j * G := by
    intro k hk j hj
    have hjB : ‖z j‖ ≤ B := hB j (Finset.mem_compl.mp hj)
    have hinner : -(D * B) ≤ ⟪u₀ - u, z k - z j⟫_ℝ := by
      have h1 : ⟪u₀ - u, z k⟫_ℝ = R * -⟪u - u₀, e⟫_ℝ := by
        rw [hzO k hk, inner_smul_right, ← neg_sub u u₀, inner_neg_left]
      have h2 : |⟪u₀ - u, z j⟫_ℝ| ≤ D * B := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [← neg_sub u u₀, norm_neg]
        exact mul_le_mul huS2 hjB (norm_nonneg _) hD
      rw [inner_sub_right, h1]
      have : 0 ≤ R * -⟪u - u₀, e⟫_ℝ := mul_nonneg hR (by linarith)
      linarith [le_abs_self ⟪u₀ - u, z j⟫_ℝ]
    have hexp : Real.exp (-⟪u₀ - u, z k - z j⟫_ℝ / ε) ≤ G := by
      rw [hG]; apply Real.exp_le_exp.mpr
      calc -⟪u₀ - u, z k - z j⟫_ℝ / ε ≤ D * B / ε := div_le_div_of_nonneg_right (by linarith) hε.le
        _ ≤ D * B / εlo := div_le_div_of_nonneg_left (mul_nonneg hD hB0) hεlo hεε
    rw [piCond_ratio z f ε u₀ u j k]
    exact mul_le_mul_of_nonneg_left hexp (mul_nonneg (piCond_nonneg _ _ _ _ _) (piCond_nonneg _ _ _ _ _))
  have hsum : C u₀ * A u ≤ A u₀ * C u * G := by
    have L : C u₀ * A u = ∑ k ∈ O, ∑ j ∈ Oᶜ, piCond z f ε u₀ j * piCond z f ε u k := by
      simp only [hA, hC]; rw [Finset.sum_mul_sum, Finset.sum_comm]
    have Rr : A u₀ * C u * G = ∑ k ∈ O, ∑ j ∈ Oᶜ, piCond z f ε u₀ k * piCond z f ε u j * G := by
      simp only [hA, hC]; rw [Finset.sum_mul_sum, Finset.sum_mul]; simp_rw [Finset.sum_mul]
    rw [L, Rr]
    exact Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun j hj => hpair k hk j hj
  have hGpos : 0 < G := Real.exp_pos _
  have hCu1 : C u ≤ 1 := by linarith [hAC u, hA0 u]
  have hkey : (1 - A u₀) * η ≤ A u₀ * G := by
    have h1 : C u₀ = 1 - A u₀ := by linarith [hAC u₀]
    calc (1 - A u₀) * η ≤ C u₀ * A u := by rw [h1]; exact mul_le_mul_of_nonneg_left huA (by linarith [hC0 u₀])
      _ ≤ A u₀ * C u * G := hsum
      _ ≤ A u₀ * 1 * G := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCu1 (hA0 u₀)) hGpos.le
      _ = A u₀ * G := by ring
  set γ := η * Real.exp (-(D * B) / εlo) with hγ
  have hγG : γ = η / G := by
    rw [hγ, hG, neg_div, Real.exp_neg, ← div_eq_mul_inv]
  have hγpos : 0 < γ := by rw [hγG]; exact div_pos hη hGpos
  have hAlow : γ / (1 + γ) ≤ A u₀ := by
    rw [div_le_iff₀ (by linarith), hγG, div_le_iff₀ hGpos]
    have : A u₀ * (1 + η / G) * G = A u₀ * G + A u₀ * η := by field_simp
    rw [this]; linarith
  -- `‖Q̂(u₀)‖ ≥ A(u₀) R − B`
  have hQ : Qhat z f ε u₀ = (A u₀ * R) • e + ∑ i ∈ Oᶜ, piCond z f ε u₀ i • z i := by
    unfold Qhat
    rw [← Finset.sum_add_sum_compl O]
    congr 1
    rw [Finset.sum_congr rfl fun i hi => by rw [hzO i hi], hA]
    simp only [smul_smul, ← Finset.sum_smul, Finset.sum_mul]
  have hCn : ‖∑ i ∈ Oᶜ, piCond z f ε u₀ i • z i‖ ≤ B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Oᶜ, ‖piCond z f ε u₀ i • z i‖ ≤ ∑ i ∈ Oᶜ, piCond z f ε u₀ i * B := by
          apply Finset.sum_le_sum; intro i hi
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (piCond_nonneg z f ε u₀ i)]
          exact mul_le_mul_of_nonneg_left (hB i (Finset.mem_compl.mp hi)) (piCond_nonneg z f ε u₀ i)
      _ = C u₀ * B := by rw [hC, Finset.sum_mul]
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right (by linarith [hAC u₀, hA0 u₀]) hB0
      _ = B := one_mul B
  have hnormA : ‖(A u₀ * R) • e‖ = A u₀ * R := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hA0 u₀) hR)]
  have htri : ‖(A u₀ * R) • e‖ - ‖∑ i ∈ Oᶜ, piCond z f ε u₀ i • z i‖ ≤ ‖Qhat z f ε u₀‖ := by
    rw [hQ]
    have := norm_sub_le ((A u₀ * R) • e + ∑ i ∈ Oᶜ, piCond z f ε u₀ i • z i) (∑ i ∈ Oᶜ, piCond z f ε u₀ i • z i)
    rw [add_sub_cancel_right] at this
    linarith
  rw [hnormA] at htri
  have : R * (γ / (1 + γ)) ≤ A u₀ * R := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hAlow hR
  linarith

end PartB

/-! ### General forms (data-driven temperature) -/

section General
variable {n : ℕ}

lemma exists_D (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsFiniteMeasure ν] (u₀ : EuclideanSpace ℝ (Fin K))
    {c : ℝ} (hc : 0 < c) : ∃ D : ℝ, 0 ≤ D ∧ ν.real {u | D < ‖u - u₀‖} < c := by
  set s : ℕ → Set (EuclideanSpace ℝ (Fin K)) := fun N => {u | (N : ℝ) < ‖u - u₀‖} with hs
  have hanti : Antitone s := fun N M hNM u hu =>
    lt_of_le_of_lt (by exact_mod_cast hNM) (show (M : ℝ) < ‖u - u₀‖ from hu)
  have hinter : ⋂ N, s N = ∅ := by
    ext u
    simp only [hs, mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    exact exists_nat_ge ‖u - u₀‖
  have ht := tendsto_measure_iInter_atTop (μ := ν)
    (fun N => (measurableSet_lt measurable_const (by fun_prop)).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at ht
  obtain ⟨N, hN⟩ := ((tendsto_order.1 ht).2 (ENNReal.ofReal c) (by simpa using hc)).exists
  exact ⟨N, Nat.cast_nonneg N, ENNReal.toReal_lt_of_lt_ofReal hN⟩

/-- The replaced indices. -/
def replaced (Z Z' : Fin n → EuclideanSpace ℝ (Fin K)) : Finset (Fin n) :=
  by classical exact Finset.univ.filter fun i => Z' i ≠ Z i

lemma mem_replaced {Z Z' : Fin n → EuclideanSpace ℝ (Fin K)} {i : Fin n} :
    i ∈ replaced Z Z' ↔ Z' i ≠ Z i := by
  classical
  unfold replaced; simp

lemma card_replaced {Z Z' : Fin n → EuclideanSpace ℝ (Fin K)} {ℓ : ℕ} (h : Z' ∈ Contam Z ℓ) :
    (replaced Z Z').card ≤ ℓ := by
  have : ((replaced Z Z' : Finset (Fin n)) : Set (Fin n)) = {i | Z' i ≠ Z i} := by
    ext i; simp [mem_replaced]
  rw [← Set.ncard_coe_finset, this]; exact h

theorem bounded_gen (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν]
    (εsel : (Fin n → EuclideanSpace ℝ (Fin K)) → ℝ) (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ)
    (hset : ∀ Z', 0 < εsel Z' ∧ IsEntPot ν (εsel Z') Z' (fsel Z')) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (ℓ : ℕ) (u₀ : EuclideanSpace ℝ (Fin K)) {t D εhi : ℝ} (ht : 0 < t)
    (hℓ : (ℓ : ℝ) < n * (halfMass ν u₀ t D).toReal) (Z' : Fin n → EuclideanSpace ℝ (Fin K))
    (hZ' : Z' ∈ Contam Z ℓ) (hhi : εsel Z' ≤ εhi) (B : ℝ) (hB : ∀ j, Z' j = Z j → ‖Z' j‖ ≤ B) :
    ‖Qhat Z' (fsel Z') (εsel Z') u₀‖ ≤ entBound n ℓ t D B εhi (halfMass ν u₀ t D).toReal :=
  displacement_le ν (hset Z').1 hhi Z' (fsel Z') (hset Z').2 (replaced Z Z') (card_replaced hZ')
    (fun j hj => hB j (by_contra fun h => hj (mem_replaced.mpr h))) u₀ ht hℓ

/-- The contaminated sample: the points of `O` moved to `R e`. -/
def plant (O : Finset (Fin n)) (R : ℝ) (e : EuclideanSpace ℝ (Fin K)) (Z : Fin n → EuclideanSpace ℝ (Fin K)) :
    Fin n → EuclideanSpace ℝ (Fin K) :=
  fun i => if i ∈ O then R • e else Z i

lemma plant_mem (O : Finset (Fin n)) (R : ℝ) (e : EuclideanSpace ℝ (Fin K)) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    {k : Fin n} (hk : k ∈ O) : plant O R e Z k = R • e := by
  unfold plant; rw [if_pos hk]

lemma plant_notMem (O : Finset (Fin n)) (R : ℝ) (e : EuclideanSpace ℝ (Fin K)) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    {k : Fin n} (hk : k ∉ O) : plant O R e Z k = Z k := by
  unfold plant; rw [if_neg hk]

lemma plant_contam (O : Finset (Fin n)) (R : ℝ) (e : EuclideanSpace ℝ (Fin K)) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    {ℓ : ℕ} (hO : O.card ≤ ℓ) : plant O R e Z ∈ Contam Z ℓ := by
  change {i | plant O R e Z i ≠ Z i}.ncard ≤ ℓ
  have hsub : {i | plant O R e Z i ≠ Z i} ⊆ (O : Set (Fin n)) := by
    intro i hi
    by_contra hiO
    exact hi (plant_notMem O R e Z hiO)
  calc {i | plant O R e Z i ≠ Z i}.ncard ≤ (O : Set (Fin n)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet O)
    _ ≤ ℓ := by rw [Set.ncard_coe_finset]; exact hO

theorem unbounded_gen (hn : 1 ≤ n) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν]
    (εsel : (Fin n → EuclideanSpace ℝ (Fin K)) → ℝ) (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ)
    (hset : ∀ Z', IsEntPot ν (εsel Z') Z' (fsel Z')) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (ℓ : ℕ)
    (u₀ : EuclideanSpace ℝ (Fin K)) {εlo : ℝ} (hεlo : 0 < εlo) (hlo : ∀ Z' ∈ Contam Z ℓ, εlo ≤ εsel Z')
    (hd : (n : ℝ≥0∞) * dMinus ν u₀ < ℓ) (M : ℝ) :
    ∃ Z' ∈ Contam Z ℓ, M < ‖Qhat Z' (fsel Z') (εsel Z') u₀‖ := by
  classical
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnpos : 0 < n := hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  obtain ⟨e, he, hlt⟩ : ∃ e : EuclideanSpace ℝ (Fin K), ∃ _ : ‖e‖ = 1,
      (n : ℝ≥0∞) * ν {u | 0 < ⟪u - u₀, e⟫_ℝ} < ℓ := by
    unfold dMinus at hd
    simp only [ENNReal.mul_iInf_of_ne hn0 (ENNReal.natCast_ne_top n), iInf_lt_iff] at hd
    exact hd
  set P := {u : EuclideanSpace ℝ (Fin K) | 0 < ⟪u - u₀, e⟫_ℝ} with hP
  have hreal : (n : ℝ) * ν.real P < ℓ := by
    have := (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (measure_ne_top ν P))
      (ENNReal.natCast_ne_top ℓ)).mpr hlt
    simpa [ENNReal.toReal_mul, measureReal_def] using this
  by_cases hℓn : n ≤ ℓ
  · -- every point replaced
    set R := |M| + 1
    refine ⟨fun _ => R • e, ?_, ?_⟩
    · change {i | R • e ≠ Z i}.ncard ≤ ℓ
      exact (Set.ncard_le_card _).trans (by simpa using hℓn)
    · have hQ : Qhat (fun _ : Fin n => R • e) (fsel fun _ => R • e) (εsel fun _ => R • e) u₀ = R • e := by
        unfold Qhat
        rw [← Finset.sum_smul, sum_piCond _ _ _ hnpos, one_smul]
      rw [hQ, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < R)]
      linarith [le_abs_self M]
  push_neg at hℓn
  set g := (ℓ : ℝ) / n - ν.real P with hg
  have hgpos : 0 < g := by
    rw [hg, sub_pos, lt_div_iff₀ hnr]; linarith
  obtain ⟨D, hD, hDF⟩ := exists_D ν u₀ (half_pos hgpos)
  set η := g / 4 with hη
  have hηpos : 0 < η := by positivity
  set O : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb hℓn.le) with hO
  have hOcard : O.card = ℓ := by simp [hO]
  set B := ∑ i, ‖Z i‖ with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => norm_nonneg _
  set γ := η * Real.exp (-(D * B) / εlo) with hγ
  have hγpos : 0 < γ := mul_pos hηpos (Real.exp_pos _)
  obtain ⟨R, hR0, hRγ⟩ : ∃ R : ℝ, 0 ≤ R ∧ R * (γ / (1 + γ)) = |M| + B + 1 := by
    refine ⟨(|M| + B + 1) * (1 + γ) / γ,
      div_nonneg (mul_nonneg (by linarith [abs_nonneg M]) (by linarith)) hγpos.le, ?_⟩
    field_simp
  have hZ'c : plant O R e Z ∈ Contam Z ℓ := plant_contam O R e Z hOcard.le
  refine ⟨plant O R e Z, hZ'c, ?_⟩
  have hzO : ∀ k ∈ O, plant O R e Z k = R • e := fun k hk => plant_mem O R e Z hk
  have hBj : ∀ j ∉ O, ‖plant O R e Z j‖ ≤ B := fun j hj => by
    rw [plant_notMem O R e Z hj]
    exact Finset.single_le_sum (f := fun i => ‖Z i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have hmass : ν.real P + ν.real {u | D < ‖u - u₀‖} + η < O.card / n := by
    rw [hOcard]
    have : (ℓ : ℝ) / n = ν.real P + g := by rw [hg]; ring
    rw [this, hη]; linarith
  have := core_b ν hεlo (hlo _ hZ'c) (plant O R e Z) (fsel (plant O R e Z)) (hset _) O u₀ e hR0 hB0 hD hηpos he
    hzO hBj hmass
  rw [← hγ, hRγ] at this
  linarith [le_abs_self M]

open Classical in
lemma bp_bracket {X Y : Type*} [Norm Y] (hn : 1 ≤ n) (S : (Fin n → X) → Y) (Z : Fin n → X) {b₁ b₂ : ℝ}
    (hb₂ : 0 ≤ b₂) (hlow : ∀ ℓ : ℕ, (ℓ : ℝ) < n * b₁ → ¬ Explodes S Z ℓ)
    (hup : ∀ ℓ : ℕ, (n : ℝ) * b₂ < ℓ → Explodes S Z ℓ) :
    b₁ ≤ BP S Z ∧ BP S Z ≤ b₂ + 1 / n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set ℓ₀ := ⌊(n : ℝ) * b₂⌋₊ + 1 with hℓ₀
  have hℓ₀gt : (n : ℝ) * b₂ < ℓ₀ := by rw [hℓ₀]; push_cast; exact Nat.lt_floor_add_one _
  have hℓ₀le : (ℓ₀ : ℝ) ≤ n * b₂ + 1 := by
    rw [hℓ₀]; push_cast; linarith [Nat.floor_le (mul_nonneg hnr.le hb₂)]
  have hex : ∃ ℓ, 1 ≤ ℓ ∧ Explodes S Z ℓ := ⟨ℓ₀, by omega, hup ℓ₀ hℓ₀gt⟩
  have hBP : BP S Z = (Nat.find hex : ℝ) / n := by
    unfold BP; simp only [hex, ↓reduceDIte]
  obtain ⟨_, hfind⟩ := Nat.find_spec hex
  have hfind_le : Nat.find hex ≤ ℓ₀ := Nat.find_min' hex ⟨by omega, hup ℓ₀ hℓ₀gt⟩
  refine ⟨?_, ?_⟩
  · rw [hBP, le_div_iff₀ hnr]
    by_contra hcon
    push_neg at hcon
    exact hlow _ (by linarith) hfind
  · rw [hBP, div_le_iff₀ hnr]
    have : ((Nat.find hex : ℕ) : ℝ) ≤ ℓ₀ := by exact_mod_cast hfind_le
    have h1 : (b₂ + 1 / n) * n = n * b₂ + 1 := by field_simp
    rw [h1]; linarith

lemma dPlus_le_dMinus (ν : Measure (EuclideanSpace ℝ (Fin K))) (u₀ : EuclideanSpace ℝ (Fin K)) :
    dPlus ν u₀ ≤ dMinus ν u₀ :=
  iSup₂_le fun _t ht => iSup_le fun _D => Wave6b.halfMass_le_dMinus ν u₀ ht

theorem bp_point (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (hK : 0 < K) (hn : 1 ≤ n)
    (εsel : (Fin n → EuclideanSpace ℝ (Fin K)) → ℝ) (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ)
    (hset : ∀ Z', 0 < εsel Z' ∧ IsEntPot ν (εsel Z') Z' (fsel Z')) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (u₀ : EuclideanSpace ℝ (Fin K)) {εlo εhi : ℝ} (hεlo : 0 < εlo)
    (hrange : ∀ Z', εlo ≤ εsel Z' ∧ εsel Z' ≤ εhi) :
    (dPlus ν u₀).toReal ≤ BP (fun Z' => Qhat Z' (fsel Z') (εsel Z') u₀) Z ∧
      BP (fun Z' => Qhat Z' (fsel Z') (εsel Z') u₀) Z ≤ (dMinus ν u₀).toReal + 1 / n := by
  have hdm1 : dMinus ν u₀ ≤ 1 := Wave6b.dMinus_le_one ν hK u₀
  have hdmtop : dMinus ν u₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hdm1
  have hdptop : dPlus ν u₀ ≠ ⊤ := ne_top_of_le_ne_top hdmtop (dPlus_le_dMinus ν u₀)
  refine bp_bracket hn _ Z ENNReal.toReal_nonneg ?_ ?_
  · intro ℓ hℓ
    have hE : (ℓ : ℝ≥0∞) < n * dPlus ν u₀ := by
      rw [← ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top ℓ)
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hdptop)]
      simpa [ENNReal.toReal_mul] using hℓ
    unfold dPlus at hE
    simp only [ENNReal.mul_iSup, lt_iSup_iff] at hE
    obtain ⟨t, ht, D, hlt⟩ := hE
    have hhm : halfMass ν u₀ t D ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (Wave6b.halfMass_le_one ν hK u₀ t D)
    have hreal : (ℓ : ℝ) < n * (halfMass ν u₀ t D).toReal := by
      have := (ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top ℓ)
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hhm)).mpr hlt
      simpa [ENNReal.toReal_mul] using this
    intro hex
    apply hex
    refine ⟨entBound n ℓ t D (∑ i, ‖Z i‖) εhi (halfMass ν u₀ t D).toReal, ?_⟩
    rintro _ ⟨Z', hZ', rfl⟩
    exact bounded_gen ν εsel fsel hset Z ℓ u₀ ht hreal Z' hZ' (hrange Z').2 _ fun j hj => by
      rw [hj]; exact Finset.single_le_sum (f := fun i => ‖Z i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  · intro ℓ hℓ
    have hE : (n : ℝ≥0∞) * dMinus ν u₀ < ℓ := by
      rw [← ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hdmtop)
        (ENNReal.natCast_ne_top ℓ)]
      simpa [ENNReal.toReal_mul] using hℓ
    rintro ⟨M, hM⟩
    obtain ⟨Z', hZ', hlt⟩ := unbounded_gen hn ν εsel fsel (fun Z' => (hset Z').2) Z ℓ u₀ hεlo
      (fun Z' _ => (hrange Z').1) hE M
    have := hM ⟨Z', hZ', rfl⟩
    linarith

end General

/-! ### The claims -/

theorem entropic_weight : Claims.entropic_weight := by
  intro K n ν _ ε fsel Z ℓ u₀ t D hset ht hℓ Z' hZ' B hB k hk
  exact le_min (piCond_le_one _ _ _ _ _)
    (weight_le ν hset.1 Z' (fsel Z') (hset.2.2 Z') (replaced Z Z') (card_replaced hZ')
      (fun j hj => hB j (by_contra fun h => hj (mem_replaced.mpr h))) u₀ ht hℓ k (mem_replaced.mpr hk))

theorem entropic_displacement : Claims.entropic_displacement := by
  intro K n ν _ ε fsel Z hset ℓ u₀ t D ht hℓ Z' hZ' B hB
  exact bounded_gen ν (fun _ => ε) fsel (fun Z' => ⟨hset.1, hset.2.2 Z'⟩) Z ℓ u₀ ht hℓ Z' hZ' le_rfl B hB

theorem entropic_unbounded : Claims.entropic_unbounded := by
  intro K n ν _ ε fsel Z hn hset ℓ u₀ hd M
  exact unbounded_gen hn ν (fun _ => ε) fsel hset.2.2 Z ℓ u₀ hset.1 (fun _ _ => le_rfl) hd M

theorem entropic_bp_lower : Claims.entropic_bp_lower := by
  intro K n ν _ ε fsel Z u₀ hK hn hset
  exact (bp_point ν hK hn (fun _ => ε) fsel (fun Z' => ⟨hset.1, hset.2.2 Z'⟩) Z u₀ hset.1
    (fun _ => ⟨le_rfl, le_rfl⟩)).1

theorem entropic_bp_upper : Claims.entropic_bp_upper := by
  intro K n ν _ ε fsel Z u₀ hK hn hset
  exact (bp_point ν hK hn (fun _ => ε) fsel (fun Z' => ⟨hset.1, hset.2.2 Z'⟩) Z u₀ hset.1
    (fun _ => ⟨le_rfl, le_rfl⟩)).2

theorem dplus_eq_dminus : Claims.dplus_eq_dminus := by
  intro K ν u₀
  have h1 : dPlus ν u₀ = Wave6b.betaPlus ν {u₀} := by
    unfold dPlus Wave6b.betaPlus
    simp only [mem_singleton_iff, iInf_iInf_eq_left]
  rw [h1, Wave6b.betaPlus_eq K ν {u₀} isCompact_singleton]
  simp only [mem_singleton_iff, iInf_iInf_eq_left]

theorem entropic_ac : Claims.entropic_ac := by
  intro K ν u₀ hac
  exact ⟨dplus_eq_dminus K ν u₀, Wave6b.dMinus_eq_tukey ν hac u₀⟩

theorem entropic_displacement_data : Claims.entropic_displacement_data := by
  intro K n ν _ εsel fsel Z ℓ u₀ t D εhi hset ht hℓ Z' hZ' hhi B hB
  exact bounded_gen ν εsel fsel hset.2 Z ℓ u₀ ht hℓ Z' hZ' hhi B hB

theorem entropic_unbounded_data : Claims.entropic_unbounded_data := by
  intro K n ν _ εsel fsel Z ℓ u₀ εlo hn hset hεlo hlo hd M
  exact unbounded_gen hn ν εsel fsel (fun Z' => (hset.2 Z').2) Z ℓ u₀ hεlo hlo hd M

theorem entropic_bp_data : Claims.entropic_bp_data := by
  intro K n ν _ εsel fsel Z u₀ εlo εhi hK hn hset hεlo hrange
  exact bp_point ν hK hn εsel fsel hset.2 Z u₀ hεlo hrange

theorem region_bounded_unconditional : Claims.region_bounded_unconditional := by
  intro K n ν _ ε fsel Z A ℓ hK hset hA hℓ
  exact Wave6b.region_bounded K n ν ε fsel Z A ℓ hK hset (entropic_displacement K n ν ε fsel Z hset) hA hℓ

theorem region_unbounded_unconditional : Claims.region_unbounded_unconditional := by
  intro K n ν _ ε fsel Z A ℓ hK hn hset hA hAne hℓ
  exact Wave6b.region_unbounded K n ν ε fsel Z A ℓ hK hset (entropic_unbounded K n ν ε fsel Z hn hset) hA
    hAne hℓ

theorem region_bp_general_unconditional : Claims.region_bp_general_unconditional := by
  intro K n ν _ ε fsel Z A hK hn hset hA hAne
  exact Wave6b.region_bp_general K n ν ε fsel Z A hK hn hset (entropic_displacement K n ν ε fsel Z hset)
    (entropic_unbounded K n ν ε fsel Z hn hset) hA hAne

theorem region_bp_unconditional : Claims.region_bp_unconditional := by
  intro K n ν _ ε fsel Z A hK hn hac hset hA hAne
  exact Wave6b.region_bp K n ν ε fsel Z A hK hn hac hset (entropic_displacement K n ν ε fsel Z hset)
    (entropic_unbounded K n ν ε fsel Z hn hset) hA hAne

end StatFormal.OTFD.Wave12a
