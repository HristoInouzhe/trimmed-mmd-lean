import StatFormal.Wave30tr.RouteDet
import StatFormal.Lib.Concentration.Symmetrization2
import StatFormal.Wave30tp.RouteMcDiarmid2
import StatFormal.Wave30tp.RouteLevel
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs

/-!
# Route: Steps 2–3 of Theorem A and the assembly (untrusted proof material)

* Parameters `θ = (f, t, t') ∈ thParams H κ` (`‖f‖ ≤ 1`, `|t|, |t'| ≤ κ`); the signed joint deviation
  `jdev s z θ = s[(P_n − P)(⟨−f,φ⟩ − t)₊ + (Q_m − Q)(⟨f,φ⟩ − t')₊]` (`s = −1`: the NOTE's `Z`, `s = 1`: its `Z⁻`).
* Measurability: the supremum is taken over a countable dense `T₀ ⊆ thParams` (`H` separable); `θ ↦ jdev s z θ` is
  continuous, so the bound on `T₀` extends to `thParams` (`jdev_le_of_iSup`).
* **Step 2** (`integral_iSup_jdev_le`): two-sample symmetrisation (`Lib/Concentration/Symmetrization2`), then
  coordinatewise contraction over `Fin n ⊕ Fin m` with the maps `u ↦ s·u₊` (`Lib/Concentration/ContractionCoord`), then
  `sup_f ⟨f, v⟩ ≤ ‖v‖`, `sup_t (−t S) ≤ κ|S|`, `E‖∑σ_k u_k‖ ≤ √∑‖u_k‖² ≤ κ√s` and `E|σ_1+⋯+σ_n| = n e_n` (marginal of
  the joint sign vector): `E sup_{T₀} jdev ≤ 2κ√s + 2κ(e_n + e_m)`.
* **Step 3** (`prob_event`): one McDiarmid on the joint sample (`Wave30tp.mcdiarmid_two_sample`) with bounded differences
  `D/n`, `D/m`; the case `D = 0` (`φ` constant, `jdev ≡ 0`) separately.
* Assembly: Step 1 (`RouteDet.setDist_region_le`) with (source, target) = (empirical, population) on `E⁺`
  (`s = −1`) and = (population, empirical) on `E⁻` (`s = 1`), `S = τ_A(0,δ)`; `TV ≤ α ⇒ D_α = 0` is the certified
  `ZeroSet.zero_of_tv_le`; the two-sided form uses the certified union bound `TrimmedMMD.event_prob`.
-/

noncomputable section
open MeasureTheory Set Finset

namespace StatFormal.Wave30tr

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.Concentration

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### The constants `e_k` -/

theorem ek_eq_radE (k : ℕ) : ek k = radE (fun σ : Fin k → Bool => |∑ i, rsign (σ i)|) / k := rfl

theorem ek_nonneg (k : ℕ) : 0 ≤ ek k := by
  rw [ek_eq_radE]; exact div_nonneg (radE_nonneg fun σ => abs_nonneg _) (Nat.cast_nonneg _)

theorem mul_ek {k : ℕ} (hk : k ≠ 0) :
    (k : ℝ) * ek k = radE (fun σ : Fin k → Bool => |∑ i, rsign (σ i)|) := by
  have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  rw [ek_eq_radE]; field_simp

/-! ### Parameters and the joint deviation -/

/-- `{(f, t, t') : ‖f‖ ≤ 1, |t| ≤ κ, |t'| ≤ κ}`. -/
def thParams (H : Type*) [NormedAddCommGroup H] (κ : ℝ) : Set (H × ℝ × ℝ) :=
  {θ | ‖θ.1‖ ≤ 1 ∧ |θ.2.1| ≤ κ ∧ |θ.2.2| ≤ κ}

/-- `(−f, t)`: the parameter of `(⟨−f, φ⟩ − t)₊`. -/
def pX (θ : H × ℝ × ℝ) : H × ℝ := (-θ.1, θ.2.1)

/-- `(f, t')`: the parameter of `(⟨f, φ⟩ − t')₊`. -/
def pY (θ : H × ℝ × ℝ) : H × ℝ := (θ.1, θ.2.2)

variable {φ : 𝒳 → H} {κ : ℝ}

omit [InnerProductSpace ℝ H] in
theorem pX_mem {θ : H × ℝ × ℝ} (h : θ ∈ thParams H κ) : pX θ ∈ tmParams H κ :=
  ⟨by simp only [pX, norm_neg]; exact h.1, h.2.1⟩

omit [InnerProductSpace ℝ H] in
theorem pY_mem {θ : H × ℝ × ℝ} (h : θ ∈ thParams H κ) : pY θ ∈ tmParams H κ := ⟨h.1, h.2.2⟩

omit [InnerProductSpace ℝ H] in
theorem continuous_pX : Continuous (pX (H := H)) :=
  (continuous_fst.neg).prodMk (continuous_fst.comp continuous_snd)

omit [InnerProductSpace ℝ H] in
theorem continuous_pY : Continuous (pY (H := H)) :=
  continuous_fst.prodMk (continuous_snd.comp continuous_snd)

/-- The signed joint deviation `s[(P_n − P)(⟨−f,φ⟩ − t)₊ + (Q_m − Q)(⟨f,φ⟩ − t')₊]`. -/
def jdev (P Q : Measure 𝒳) (φ : 𝒳 → H) (s : ℝ) {n m : ℕ} (z : (Fin n → 𝒳) × (Fin m → 𝒳))
    (θ : H × ℝ × ℝ) : ℝ :=
  s * (empDev P (gTM φ) n z.1 (pX θ) + empDev Q (gTM φ) m z.2 (pY θ))

variable (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
theorem jdev_eq {T : Type*} (θ : T → H × ℝ × ℝ) (s : ℝ) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) (t : T) :
    jdev P Q φ s z (θ t) =
      empDev P (fun t y => s * gTM φ (pX (θ t)) y) n z.1 t +
        empDev Q (fun t y => s * gTM φ (pY (θ t)) y) m z.2 t := by
  simp only [jdev, empDev, integral_const_mul, ← Finset.mul_sum]; ring

theorem continuous_jdev (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (s : ℝ) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) : Continuous fun θ : H × ℝ × ℝ => jdev P Q φ s z θ :=
  continuous_const.mul
    (((continuous_empDev_tm P hφ hκ z.1).comp continuous_pX).add
      ((continuous_empDev_tm Q hφ hκ z.2).comp continuous_pY))

theorem abs_jdev_le (hκ : ∀ x, ‖φ x‖ ≤ κ) {s : ℝ} (hs : |s| = 1) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) {θ : H × ℝ × ℝ} (hθ : θ ∈ thParams H κ) :
    |jdev P Q φ s z θ| ≤ 2 * (2 * κ) + 2 * (2 * κ) := by
  have h1 : |empDev P (fun _ : Unit => gTM φ (pX θ)) n z.1 ()| ≤ 2 * (2 * κ) :=
    abs_empDev_le P (fun _ y => abs_gTM_le hκ (pX_mem hθ) y) z.1 ()
  have h2 : |empDev Q (fun _ : Unit => gTM φ (pY θ)) m z.2 ()| ≤ 2 * (2 * κ) :=
    abs_empDev_le Q (fun _ y => abs_gTM_le hκ (pY_mem hθ) y) z.2 ()
  unfold jdev
  rw [abs_mul, hs, one_mul]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
theorem measurable_jdev (hφ : StronglyMeasurable φ) (s : ℝ) {n m : ℕ} (θ : H × ℝ × ℝ) :
    Measurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => jdev P Q φ s z θ :=
  (((measurable_empDev P (measurable_gTM hφ) n (pX θ)).comp measurable_fst).add
    ((measurable_empDev Q (measurable_gTM hφ) m (pY θ)).comp measurable_snd)).const_mul s

/-- The bound on a countable dense subset extends to all parameters. -/
theorem jdev_le_of_iSup (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {s : ℝ} (hs : |s| = 1)
    (T₀ : Set (H × ℝ × ℝ)) (hT₀ : T₀ ⊆ thParams H κ) (hdense : thParams H κ ⊆ closure T₀) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) {c : ℝ} (hz : ⨆ θ : T₀, jdev P Q φ s z θ.1 ≤ c) :
    ∀ θ ∈ thParams H κ, jdev P Q φ s z θ ≤ c := by
  have hb : BddAbove (Set.range fun θ : T₀ => jdev P Q φ s z θ.1) :=
    bddAbove_of_abs_le fun θ => abs_jdev_le P Q hκ hs z (hT₀ θ.2)
  have hcl : closure T₀ ⊆ {θ | jdev P Q φ s z θ ≤ c} :=
    closure_minimal (fun θ hθ => (le_ciSup hb ⟨θ, hθ⟩).trans hz)
      (isClosed_le (continuous_jdev P Q hφ hκ s z) continuous_const)
  exact fun θ hθ => hcl (hdense hθ)

/-! ### Step 2: the expectation -/

/-- Pointwise Rademacher bound: `E_σ sup_θ [n⁻¹∑σ_i s(⟨−f,φ(x_i)⟩−t)₊ + m⁻¹∑σ'_j s(⟨f,φ(y_j)⟩−t')₊]
≤ κ√s + κ(e_n + e_m)`. -/
theorem radAvg2_le (T₀ : Set (H × ℝ × ℝ)) [Nonempty T₀] (hT₀ : T₀ ⊆ thParams H κ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) {s : ℝ} (hs : |s| = 1) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    radAvg2 (fun (θ : T₀) y => s * gTM φ (pX θ.1) y) (fun (θ : T₀) y => s * gTM φ (pY θ.1) y) n m z ≤
      κ * √(StatFormal.Wave30tp.sNM n m) + κ * (ek n + ek m) := by
  obtain ⟨θ₀⟩ := ‹Nonempty T₀›
  have hκ0 : 0 ≤ κ := (abs_nonneg _).trans (hT₀ θ₀.2).2.1
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
  have hninv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)
  have hminv : (m : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm)
  set a : T₀ → Fin n ⊕ Fin m → ℝ := fun θ k =>
    Sum.elim (fun i => (n : ℝ)⁻¹ * (inner ℝ (-θ.1.1) (φ (z.1 i)) - θ.1.2.1))
      (fun j => (m : ℝ)⁻¹ * (inner ℝ θ.1.1 (φ (z.2 j)) - θ.1.2.2)) k with ha_def
  have ha : ∀ θ k, |a θ k| ≤ 2 * κ := by
    intro θ k
    cases k with
    | inl i =>
      simp only [ha_def, Sum.elim_inl]
      rw [abs_mul, abs_of_pos (inv_pos.2 hnpos)]
      have := abs_inner_sub_le hκ (pX_mem (hT₀ θ.2)) (z.1 i)
      calc (n : ℝ)⁻¹ * |inner ℝ (-θ.1.1) (φ (z.1 i)) - θ.1.2.1| ≤ 1 * (2 * κ) :=
            mul_le_mul hninv this (abs_nonneg _) zero_le_one
        _ = 2 * κ := one_mul _
    | inr j =>
      simp only [ha_def, Sum.elim_inr]
      rw [abs_mul, abs_of_pos (inv_pos.2 hmpos)]
      have := abs_inner_sub_le hκ (pY_mem (hT₀ θ.2)) (z.2 j)
      calc (m : ℝ)⁻¹ * |inner ℝ θ.1.1 (φ (z.2 j)) - θ.1.2.2| ≤ 1 * (2 * κ) :=
            mul_le_mul hminv this (abs_nonneg _) zero_le_one
        _ = 2 * κ := one_mul _
  set φk : Fin n ⊕ Fin m → ℝ → ℝ := fun _ u => s * max u 0 with hφk_def
  have hφk : ∀ k x y, |φk k x - φk k y| ≤ |x - y| := by
    intro k x y
    simp only [hφk_def]
    rw [← mul_sub, abs_mul, hs, one_mul]
    exact abs_max_sub_max_le_abs x y 0
  have hmx : ∀ c u : ℝ, 0 ≤ c → max (c * u) 0 = c * max u 0 := fun c u hc => by
    rw [mul_max_of_nonneg _ _ hc, mul_zero]
  have hrw : ∀ (σ : Fin n ⊕ Fin m → Bool) (θ : T₀),
      (n : ℝ)⁻¹ * ∑ i, rsign (σ (Sum.inl i)) * (s * gTM φ (pX θ.1) (z.1 i)) +
        (m : ℝ)⁻¹ * ∑ j, rsign (σ (Sum.inr j)) * (s * gTM φ (pY θ.1) (z.2 j)) =
      ∑ k, rsign (σ k) * φk k (a θ k) := by
    intro σ θ
    rw [Fintype.sum_sum_type, Finset.mul_sum, Finset.mul_sum]
    simp only [ha_def, hφk_def, Sum.elim_inl, Sum.elim_inr, gTM, pX, pY,
      hmx _ _ (inv_nonneg.2 hnpos.le), hmx _ _ (inv_nonneg.2 hmpos.le)]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> ring
  have hcontr := signE_iSup_contraction a ha φk hφk
  set u : Fin n ⊕ Fin m → H :=
    Sum.elim (fun i => -((n : ℝ)⁻¹ • φ (z.1 i))) (fun j => (m : ℝ)⁻¹ • φ (z.2 j)) with hu_def
  have hlin : ∀ σ : Fin n ⊕ Fin m → Bool, (⨆ θ, ∑ k, rsign (σ k) * a θ k) ≤
      ‖∑ k, rsign (σ k) • u k‖ + κ * ((n : ℝ)⁻¹ * |∑ i, rsign (σ (Sum.inl i))|) +
        κ * ((m : ℝ)⁻¹ * |∑ j, rsign (σ (Sum.inr j))|) := by
    intro σ
    refine ciSup_le fun θ => ?_
    have hθ := hT₀ θ.2
    have hidX : ∑ i, rsign (σ (Sum.inl i)) * a θ (Sum.inl i) =
        inner ℝ θ.1.1 (∑ i, rsign (σ (Sum.inl i)) • u (Sum.inl i)) -
          θ.1.2.1 * ((n : ℝ)⁻¹ * ∑ i, rsign (σ (Sum.inl i))) := by
      rw [inner_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ha_def, hu_def, Sum.elim_inl, real_inner_smul_right, inner_neg_right, inner_neg_left]
      ring
    have hidY : ∑ j, rsign (σ (Sum.inr j)) * a θ (Sum.inr j) =
        inner ℝ θ.1.1 (∑ j, rsign (σ (Sum.inr j)) • u (Sum.inr j)) -
          θ.1.2.2 * ((m : ℝ)⁻¹ * ∑ j, rsign (σ (Sum.inr j))) := by
      rw [inner_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [ha_def, hu_def, Sum.elim_inr, real_inner_smul_right]
      ring
    have hid : ∑ k, rsign (σ k) * a θ k =
        inner ℝ θ.1.1 (∑ k, rsign (σ k) • u k) - θ.1.2.1 * ((n : ℝ)⁻¹ * ∑ i, rsign (σ (Sum.inl i))) -
          θ.1.2.2 * ((m : ℝ)⁻¹ * ∑ j, rsign (σ (Sum.inr j))) := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, inner_add_right, hidX, hidY]
      ring
    rw [hid]
    have h1 : inner ℝ θ.1.1 (∑ k, rsign (σ k) • u k) ≤ ‖∑ k, rsign (σ k) • u k‖ := by
      refine (real_inner_le_norm _ _).trans ?_
      calc ‖θ.1.1‖ * ‖∑ k, rsign (σ k) • u k‖ ≤ 1 * ‖∑ k, rsign (σ k) • u k‖ := by
            gcongr; exact hθ.1
        _ = _ := one_mul _
    have hshift : ∀ (t c : ℝ), |t| ≤ κ → -(t * c) ≤ κ * |c| := fun t c ht => by
      refine (neg_le_abs _).trans ?_
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    have h2 := hshift θ.1.2.1 ((n : ℝ)⁻¹ * ∑ i, rsign (σ (Sum.inl i))) hθ.2.1
    have h3 := hshift θ.1.2.2 ((m : ℝ)⁻¹ * ∑ j, rsign (σ (Sum.inr j))) hθ.2.2
    rw [abs_mul, abs_of_pos (inv_pos.2 hnpos)] at h2
    rw [abs_mul, abs_of_pos (inv_pos.2 hmpos)] at h3
    linarith
  have hball : signE (fun σ : Fin n ⊕ Fin m → Bool => ‖∑ k, rsign (σ k) • u k‖) ≤
      κ * √(StatFormal.Wave30tp.sNM n m) := by
    refine (signE_norm_sum_le u).trans ?_
    have hsum : ∑ k, ‖u k‖ ^ 2 ≤ κ ^ 2 * StatFormal.Wave30tp.sNM n m := by
      rw [Fintype.sum_sum_type]
      have e1 : ∑ i : Fin n, ‖u (Sum.inl i)‖ ^ 2 ≤ κ ^ 2 * (1 / (n : ℝ)) := by
        calc ∑ i : Fin n, ‖u (Sum.inl i)‖ ^ 2 ≤ ∑ _i : Fin n, ((n : ℝ)⁻¹ * κ) ^ 2 := by
              refine Finset.sum_le_sum fun i _ => ?_
              simp only [hu_def, Sum.elim_inl, norm_neg, norm_smul, Real.norm_eq_abs,
                abs_of_pos (inv_pos.2 hnpos)]
              exact pow_le_pow_left₀ (by positivity)
                (mul_le_mul_of_nonneg_left (hκ _) (inv_nonneg.2 hnpos.le)) 2
          _ = κ ^ 2 * (1 / (n : ℝ)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp
      have e2 : ∑ j : Fin m, ‖u (Sum.inr j)‖ ^ 2 ≤ κ ^ 2 * (1 / (m : ℝ)) := by
        calc ∑ j : Fin m, ‖u (Sum.inr j)‖ ^ 2 ≤ ∑ _j : Fin m, ((m : ℝ)⁻¹ * κ) ^ 2 := by
              refine Finset.sum_le_sum fun j _ => ?_
              simp only [hu_def, Sum.elim_inr, norm_smul, Real.norm_eq_abs,
                abs_of_pos (inv_pos.2 hmpos)]
              exact pow_le_pow_left₀ (by positivity)
                (mul_le_mul_of_nonneg_left (hκ _) (inv_nonneg.2 hmpos.le)) 2
          _ = κ ^ 2 * (1 / (m : ℝ)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp
      unfold StatFormal.Wave30tp.sNM
      linarith
    calc √(∑ k, ‖u k‖ ^ 2) ≤ √(κ ^ 2 * StatFormal.Wave30tp.sNM n m) := Real.sqrt_le_sqrt hsum
      _ = κ * √(StatFormal.Wave30tp.sNM n m) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ0]
  have hX : signE (fun σ : Fin n ⊕ Fin m → Bool => |∑ i, rsign (σ (Sum.inl i))|) = n * ek n := by
    rw [signE_comp_inl (fun σ : Fin n → Bool => |∑ i, rsign (σ i)|), signE_eq_radE, mul_ek hn]
  have hY : signE (fun σ : Fin n ⊕ Fin m → Bool => |∑ j, rsign (σ (Sum.inr j))|) = m * ek m := by
    rw [signE_comp_inr (fun σ : Fin m → Bool => |∑ j, rsign (σ j)|), signE_eq_radE, mul_ek hm]
  unfold radAvg2
  simp_rw [hrw]
  calc signE (fun σ => ⨆ θ : T₀, ∑ k, rsign (σ k) * φk k (a θ k))
      ≤ signE (fun σ => ⨆ θ : T₀, ∑ k, rsign (σ k) * a θ k) := hcontr
    _ ≤ signE (fun σ : Fin n ⊕ Fin m → Bool => ‖∑ k, rsign (σ k) • u k‖ +
          κ * ((n : ℝ)⁻¹ * |∑ i, rsign (σ (Sum.inl i))|) +
          κ * ((m : ℝ)⁻¹ * |∑ j, rsign (σ (Sum.inr j))|)) := signE_mono hlin
    _ = signE (fun σ : Fin n ⊕ Fin m → Bool => ‖∑ k, rsign (σ k) • u k‖) +
          κ * ((n : ℝ)⁻¹ * signE (fun σ : Fin n ⊕ Fin m → Bool => |∑ i, rsign (σ (Sum.inl i))|)) +
          κ * ((m : ℝ)⁻¹ * signE (fun σ : Fin n ⊕ Fin m → Bool => |∑ j, rsign (σ (Sum.inr j))|)) := by
        rw [signE_add, signE_add, signE_const_mul, signE_const_mul, signE_const_mul, signE_const_mul]
    _ ≤ κ * √(StatFormal.Wave30tp.sNM n m) + κ * (ek n + ek m) := by
        rw [hX, hY]
        have key1 : κ * (n : ℝ)⁻¹ * (n * ek n) = κ * ek n := by field_simp
        have key2 : κ * ((m : ℝ)⁻¹ * (m * ek m)) = κ * ek m := by field_simp
        linarith [key1, key2]

/-- **Step 2**: `E sup_{T₀} jdev ≤ 2κ√s + 2κ(e_n + e_m)`. -/
theorem integral_iSup_jdev_le (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (T₀ : Set (H × ℝ × ℝ)) [Countable T₀] [Nonempty T₀] (hT₀ : T₀ ⊆ thParams H κ) {s : ℝ}
    (hs : |s| = 1) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    ∫ z, ⨆ θ : T₀, jdev P Q φ s z θ.1 ∂(StatFormal.Wave30tp.sampleLaw P Q n m) ≤
      2 * (κ * √(StatFormal.Wave30tp.sNM n m) + κ * (ek n + ek m)) := by
  set g₁ : T₀ → 𝒳 → ℝ := fun θ y => s * gTM φ (pX θ.1) y with hg₁
  set g₂ : T₀ → 𝒳 → ℝ := fun θ y => s * gTM φ (pY θ.1) y with hg₂
  have hm₁ : ∀ θ, Measurable (g₁ θ) := fun θ => (measurable_gTM hφ _).const_mul _
  have hm₂ : ∀ θ, Measurable (g₂ θ) := fun θ => (measurable_gTM hφ _).const_mul _
  have hB₁ : ∀ θ y, |g₁ θ y| ≤ 2 * κ := fun θ y => by
    simp only [hg₁]; rw [abs_mul, hs, one_mul]; exact abs_gTM_le hκ (pX_mem (hT₀ θ.2)) y
  have hB₂ : ∀ θ y, |g₂ θ y| ≤ 2 * κ := fun θ y => by
    simp only [hg₂]; rw [abs_mul, hs, one_mul]; exact abs_gTM_le hκ (pY_mem (hT₀ θ.2)) y
  have hsym := integral_iSup_empDev2_le P Q hm₁ hm₂ hB₁ hB₂ hn hm
  have heq : ∀ z : (Fin n → 𝒳) × (Fin m → 𝒳), (⨆ θ : T₀, jdev P Q φ s z θ.1) =
      ⨆ θ : T₀, (empDev P g₁ n z.1 θ + empDev Q g₂ m z.2 θ) := fun z => by
    congr 1; funext θ; exact jdev_eq P Q (fun θ : T₀ => θ.1) s z θ
  simp_rw [heq]
  refine hsym.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have hint : Integrable (radAvg2 g₁ g₂ n m)
      ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) := by
    refine Integrable.of_bound (measurable_radAvg2 hm₁ hm₂ n m).aestronglyMeasurable
      (2 * κ + 2 * κ) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    refine abs_signE_le fun σ => abs_ciSup_le fun θ => (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact abs_mean_le hn fun i => by rw [abs_mul, abs_rsign, one_mul]; exact hB₁ _ _
    · exact abs_mean_le hm fun j => by rw [abs_mul, abs_rsign, one_mul]; exact hB₂ _ _
  have := integral_mono hint (integrable_const (κ * √(StatFormal.Wave30tp.sNM n m) + κ * (ek n + ek m)))
    fun z => radAvg2_le T₀ hT₀ hκ hs hn hm z
  rwa [integral_const, probReal_univ, one_smul] at this

/-! ### Step 3: McDiarmid on the joint sample -/

omit [MeasurableSpace 𝒳] in
theorem abs_gTM_sub_pts {D : ℝ} (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D)
    {p : H × ℝ} (hp : ‖p.1‖ ≤ 1) (a b : 𝒳) : |gTM φ p b - gTM φ p a| ≤ D := by
  refine (abs_max_sub_max_le_abs _ _ 0).trans ?_
  have e : inner ℝ p.1 (φ b) - p.2 - (inner ℝ p.1 (φ a) - p.2) = inner ℝ p.1 (φ b - φ a) := by
    rw [inner_sub_right]; ring
  rw [e]
  refine (abs_real_inner_le_norm _ _).trans ?_
  calc ‖p.1‖ * ‖φ b - φ a‖ ≤ 1 * D := mul_le_mul hp (hD b a) (norm_nonneg _) zero_le_one
    _ = D := one_mul D

/-- **Step 3**: the event `{sup_{T₀} jdev ≤ τ_A(0,δ)}` has probability `≥ 1 − δ`. -/
theorem prob_event (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {D : ℝ}
    (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (T₀ : Set (H × ℝ × ℝ)) [Countable T₀] [Nonempty T₀]
    (hT₀ : T₀ ⊆ thParams H κ) {s : ℝ} (hs : |s| = 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ENNReal.ofReal (1 - δ) ≤ StatFormal.Wave30tp.sampleLaw P Q n m
      {z | ⨆ θ : T₀, jdev P Q φ s z θ.1 ≤ tauA κ D 0 δ n m} := by
  obtain ⟨θ₀⟩ := ‹Nonempty T₀›
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (abs_nonneg _).trans (hT₀ θ₀.2).2.1
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x₀ x₀)
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.1 hm
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hsp := StatFormal.Wave30tp.sNM_pos hn hm
  have hL := StatFormal.Wave30tp.log_inv_nonneg hδ0 hδ1
  set S := StatFormal.Wave30tp.sNM n m with hS
  set M := κ * √S + κ * (ek n + ek m) with hM
  set ε := D * √(S * Real.log (1 / δ) / 2) with hε
  have htau : tauA κ D 0 δ n m = 2 * M + ε := by
    simp only [tauA, sub_zero, div_one, one_mul, hM, hε, hS]; ring
  set F : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun z => ⨆ θ : T₀, jdev P Q φ s z θ.1 with hF
  have hFm : Measurable F := Measurable.iSup fun θ => measurable_jdev P Q hφ s θ.1
  have hM0 : 0 ≤ M := by
    have := ek_nonneg n; have := ek_nonneg m; positivity
  set E := {z | F z ≤ tauA κ D 0 δ n m} with hE
  have hEm : MeasurableSet E := measurableSet_le hFm measurable_const
  rcases hD0.eq_or_lt with hDe | hDpos
  · -- `D = 0`: `φ` is constant and the deviation vanishes
    subst hDe
    have hφc : ∀ x, φ x = φ x₀ := fun x => by
      have := hD x x₀; rw [norm_le_zero_iff, sub_eq_zero] at this; exact this
    have hdev0 : ∀ {k : ℕ} (μ : Measure 𝒳) [IsProbabilityMeasure μ] (x : Fin k → 𝒳) (p : H × ℝ),
        k ≠ 0 → empDev μ (gTM φ) k x p = 0 := by
      intro k μ _ x p hk
      have hc : ∀ y, gTM φ p y = gTM φ p x₀ := fun y => by simp only [gTM, hφc y]
      have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
      simp only [empDev, hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        integral_const, probReal_univ, one_smul]
      field_simp
      ring
    have hall : E = univ := by
      refine eq_univ_of_forall fun z => ?_
      simp only [hE, hF, mem_ofPred_eq, jdev, hdev0 P z.1 _ hn0, hdev0 Q z.2 _ hm0, add_zero,
        mul_zero, ciSup_const]
      rw [htau]; simp only [hε, zero_mul, add_zero]; linarith
    rw [hall, measure_univ]
    exact ENNReal.ofReal_le_one.2 (by linarith)
  · -- `D > 0`: McDiarmid
    have hbX : ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳) (i : Fin n) (b : 𝒳),
        |F (Function.update x i b, y) - F (x, y)| ≤ D / n := by
      intro x y i b
      refine abs_iSup_sub_iSup_le (bddAbove_of_abs_le fun θ => abs_jdev_le P Q hκ hs _ (hT₀ θ.2))
        (bddAbove_of_abs_le fun θ => abs_jdev_le P Q hκ hs _ (hT₀ θ.2)) fun θ => ?_
      simp only [jdev]
      rw [← mul_sub, add_sub_add_right_eq_sub, empDev_update_sub, abs_mul, hs, one_mul, abs_mul,
        abs_inv, Nat.abs_cast, div_eq_inv_mul]
      have hp : ‖(pX θ.1).1‖ ≤ 1 := by simp only [pX, norm_neg]; exact (hT₀ θ.2).1
      exact mul_le_mul_of_nonneg_left (abs_gTM_sub_pts hD hp _ _) (inv_nonneg.2 hnpos.le)
    have hbY : ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳) (j : Fin m) (b : 𝒳),
        |F (x, Function.update y j b) - F (x, y)| ≤ D / m := by
      intro x y j b
      refine abs_iSup_sub_iSup_le (bddAbove_of_abs_le fun θ => abs_jdev_le P Q hκ hs _ (hT₀ θ.2))
        (bddAbove_of_abs_le fun θ => abs_jdev_le P Q hκ hs _ (hT₀ θ.2)) fun θ => ?_
      simp only [jdev]
      rw [← mul_sub, add_sub_add_left_eq_sub, empDev_update_sub, abs_mul, hs, one_mul, abs_mul,
        abs_inv, Nat.abs_cast, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (abs_gTM_sub_pts hD (hT₀ θ.2).1 _ _) (inv_nonneg.2 hmpos.le)
    have hε0 : 0 ≤ ε := by positivity
    have hmcd := StatFormal.Wave30tp.mcdiarmid_two_sample P Q F hFm (by positivity) (by positivity)
      hbX hbY hε0
    have hexp : -ε ^ 2 / (2 * ((n * (D / n) ^ 2 + m * (D / m) ^ 2) / 4)) = -Real.log (1 / δ) := by
      have h1 : (n : ℝ) * (D / n) ^ 2 + m * (D / m) ^ 2 = D ^ 2 * S := by
        rw [hS]; unfold StatFormal.Wave30tp.sNM; field_simp
      rw [h1, hε, mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
      ring
    rw [hexp, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv] at hmcd
    have hint := integral_iSup_jdev_le P Q hφ hκ T₀ hT₀ hs hn0 hm0
    have hsub : Eᶜ ⊆ {z | ε ≤ F z - ∫ w, F w ∂(StatFormal.Wave30tp.sampleLaw P Q n m)} := by
      intro z hz
      simp only [hE, mem_compl_iff, mem_ofPred_eq, not_le] at hz ⊢
      rw [htau] at hz
      have : (∫ w, F w ∂(StatFormal.Wave30tp.sampleLaw P Q n m)) ≤ 2 * M := hint
      linarith
    have hc : (StatFormal.Wave30tp.sampleLaw P Q n m).real Eᶜ ≤ δ := (measureReal_mono hsub).trans hmcd
    rw [probReal_compl_eq_one_sub hEm] at hc
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### Assembly -/

theorem bracket_emp [CompleteSpace H] (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) {f : H} {q q' : ℝ} (hf : ‖f‖ ≤ 1) (hq : |q| ≤ κ)
    (hq' : |q'| ≤ κ) :
    ∫ x, gTM φ (-f, q) x ∂(empirical z.1) = (n : ℝ)⁻¹ * ∑ i, gTM φ (-f, q) (z.1 i) ∧
    ∫ x, gTM φ (f, q') x ∂(empirical z.2) = (m : ℝ)⁻¹ * ∑ j, gTM φ (f, q') (z.2 j) := by
  have h1 : ((-f, q) : H × ℝ) ∈ tmParams H κ := ⟨by rw [norm_neg]; exact hf, hq⟩
  have h2 : ((f, q') : H × ℝ) ∈ tmParams H κ := ⟨hf, hq'⟩
  exact ⟨integral_empirical z.1 (measurable_gTM hφ _).stronglyMeasurable (abs_gTM_le hκ h1),
    integral_empirical z.2 (measurable_gTM hφ _).stronglyMeasurable (abs_gTM_le hκ h2)⟩

theorem tauA_eq_mul {κ D α δ : ℝ} {n m : ℕ} : tauA κ D α δ n m = 1 / (1 - α) * tauA κ D 0 δ n m := by
  simp only [tauA, sub_zero, div_one, one_mul]

/-- Theorem A, the core: the events `E⁺ = {sup_{T₀} jdev (−1) ≤ τ_A(0,δ)}`, `E⁻ = {sup_{T₀} jdev 1 ≤ τ_A(0,δ)}`. -/
theorem thmA_core {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] {φ : 𝒳 → H} {κ D : ℝ} (P Q : Measure 𝒳)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {δ : ℝ} {n m : ℕ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ∃ Eplus Eminus : Set ((Fin n → 𝒳) × (Fin m → 𝒳)),
      MeasurableSet Eplus ∧ ENNReal.ofReal (1 - δ) ≤ StatFormal.Wave30tp.sampleLaw P Q n m Eplus ∧
      MeasurableSet Eminus ∧ ENNReal.ofReal (1 - δ) ≤ StatFormal.Wave30tp.sampleLaw P Q n m Eminus ∧
      (∀ z ∈ Eplus, ∀ α ∈ Ico (0 : ℝ) 1,
        Demp φ z.1 z.2 α ≤ Dpop φ P Q α + tauA κ D α δ n m ∧
        (StatFormal.Distances.tvDist P Q ≤ α → Demp φ z.1 z.2 α ≤ tauA κ D α δ n m)) ∧
      (∀ z ∈ Eminus, ∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α - tauA κ D α δ n m ≤ Demp φ z.1 z.2 α) := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x₀)
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.1 hm
  obtain ⟨T₀, hT₀, hcount, hdense⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (thParams H κ)).exists_countable_dense_subset
  have h0 : ((0 : H), (0 : ℝ), (0 : ℝ)) ∈ thParams H κ := ⟨by simp, by simp [hκ0], by simp [hκ0]⟩
  have hne : T₀.Nonempty := closure_nonempty_iff.1 ⟨_, hdense h0⟩
  have : Nonempty T₀ := hne.to_subtype
  have : Countable T₀ := hcount.to_subtype
  have hs1 : |(1 : ℝ)| = 1 := abs_one
  have hsm : |(-1 : ℝ)| = 1 := by simp
  refine ⟨{z | ⨆ θ : T₀, jdev P Q φ (-1) z θ.1 ≤ tauA κ D 0 δ n m},
    {z | ⨆ θ : T₀, jdev P Q φ 1 z θ.1 ≤ tauA κ D 0 δ n m},
    measurableSet_le (Measurable.iSup fun θ => measurable_jdev P Q hφ _ θ.1) measurable_const,
    prob_event P Q hφ hκ hD T₀ hT₀ hsm hδ0 hδ1 hn hm,
    measurableSet_le (Measurable.iSup fun θ => measurable_jdev P Q hφ _ θ.1) measurable_const,
    prob_event P Q hφ hκ hD T₀ hT₀ hs1 hδ0 hδ1 hn hm, ?_, ?_⟩
  · intro z hz α hα
    haveI := isProbabilityMeasure_empirical hn0 z.1
    haveI := isProbabilityMeasure_empirical hm0 z.2
    have hall := jdev_le_of_iSup P Q hφ hκ hsm T₀ hT₀ hdense z hz
    have hmain : Demp φ z.1 z.2 α ≤ Dpop φ P Q α + tauA κ D α δ n m := by
      rw [tauA_eq_mul]
      refine setDist_region_le (empirical z.1) (empirical z.2) P Q hφ hκ hα.1 hα.2 ?_
      intro f q q' hf hq hq'
      have hb := bracket_emp hφ hκ z hf hq hq'
      have := hall (f, q, q') ⟨hf, hq, hq'⟩
      simp only [jdev, empDev, pX, pY] at this
      rw [hb.1, hb.2]
      linarith
    refine ⟨hmain, fun htv => ?_⟩
    have h0 : Dpop φ P Q α = 0 :=
      StatFormal.TrimmedMMD.ZeroSet.zero_of_tv_le 𝒳 H P Q φ κ α hφ hκ hα.1 hα.2 htv
    rw [h0, zero_add] at hmain
    exact hmain
  · intro z hz α hα
    haveI := isProbabilityMeasure_empirical hn0 z.1
    haveI := isProbabilityMeasure_empirical hm0 z.2
    have hall := jdev_le_of_iSup P Q hφ hκ hs1 T₀ hT₀ hdense z hz
    have hmain : Dpop φ P Q α ≤ Demp φ z.1 z.2 α + tauA κ D α δ n m := by
      rw [tauA_eq_mul]
      refine setDist_region_le P Q (empirical z.1) (empirical z.2) hφ hκ hα.1 hα.2 ?_
      intro f q q' hf hq hq'
      have hb := bracket_emp hφ hκ z hf hq hq'
      have := hall (f, q, q') ⟨hf, hq, hq'⟩
      simp only [jdev, empDev, pX, pY] at this
      rw [hb.1, hb.2]
      linarith
    linarith

end StatFormal.Wave30tr
