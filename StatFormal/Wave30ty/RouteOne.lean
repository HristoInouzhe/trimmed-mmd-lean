import StatFormal.Wave30ty.RouteBasic

set_option linter.style.longLine false

/-!
# Route: `lem:hinge (v2)`, one sample (untrusted proof material)

As in `RouteTwo`, one supremum `Z1c c` for a sign `c` (`|c| ≤ 1`): `Z = Z1c (−1)`, `Z⁻ = Z1c 1`.
* the bracket `(P_n − P)(c h¹_p)` is bounded on the class and Lipschitz in `p = (v, a)`: measurability over a countable dense subset;
* expectation: one-sample signed symmetrisation (`integral_iSup_empDev_le`), coordinatewise contraction over `Fin n` with the
  maps `w ↦ c n⁻¹ ψ_{X_i}(n w)`, the linear bound `r‖Σσ_i(−n⁻¹φ(X_i))‖ + ρ₁|σ̄|`, `E‖·‖ ≤ κ√(1/n)`;
* tail: McDiarmid for one i.i.d. sample (`TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences_fin`) with differences
  `Δ₁/n` when `Δ₁²/n > 0`; when `Δ₁ = 0` every `h` is constant and `Z1c ≡ 0`.
-/

noncomputable section
open MeasureTheory Set Finset
open scoped InnerProductSpace NNReal

namespace StatFormal.Wave30ty.ROne

open StatFormal.Wave30ty StatFormal.Wave30ty.RBasic StatFormal.Concentration StatFormal.Wave30tr

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `c · h¹_{v,a}` indexed by `p = (v, a)`. -/
def G (c : ℝ) (ψ : 𝒳 → ℝ → ℝ) (φ : 𝒳 → H) (p : H × ℝ) (y : 𝒳) : ℝ := c * hOne ψ φ p.1 p.2 y

/-- `sup_{(v,a)} (P_n − P)(c h¹_{v,a})`. -/
def Z1c (P : Measure 𝒳) (φ : 𝒳 → H) (ψ : 𝒳 → ℝ → ℝ) (r ρ₁ c : ℝ) {n : ℕ} (x : Fin n → 𝒳) : ℝ :=
  ⨆ p : hingePar1 (H := H) r ρ₁, empDev P (G c ψ φ) n x p.1

theorem hingeZ1_eq (P : Measure 𝒳) (φ : 𝒳 → H) (ψ : 𝒳 → ℝ → ℝ) (r ρ₁ : ℝ) {n : ℕ} (x : Fin n → 𝒳) :
    hingeZ1 P φ ψ r ρ₁ x = Z1c P φ ψ r ρ₁ (-1) x := by
  unfold hingeZ1 Z1c
  congr 1; funext p
  simp only [empDev, G, devPop, neg_one_mul, integral_neg, Finset.sum_neg_distrib]
  ring

theorem hingeZ1m_eq (P : Measure 𝒳) (φ : 𝒳 → H) (ψ : 𝒳 → ℝ → ℝ) (r ρ₁ : ℝ) {n : ℕ} (x : Fin n → 𝒳) :
    hingeZ1m P φ ψ r ρ₁ x = Z1c P φ ψ r ρ₁ 1 x := by
  unfold hingeZ1m Z1c
  congr 1; funext p
  simp only [empDev, G, devEmp, one_mul]

section Class

variable {ψ : 𝒳 → ℝ → ℝ} {φ : 𝒳 → H} {κ c : ℝ}

theorem measurable_G (hψ : IsHingeMap ψ) (hφ : StronglyMeasurable φ) (p : H × ℝ) :
    Measurable (G c ψ φ p) := (measurable_hOne hψ hφ p.1 p.2).const_mul c

omit [MeasurableSpace 𝒳] in
theorem abs_G_le (hc : |c| ≤ 1) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x w, |ψ x w| ≤ C + |w|) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (p : H × ℝ) (y : 𝒳) : |G c ψ φ p y| ≤ C + (|p.2| + κ * ‖p.1‖) := by
  unfold G
  rw [abs_mul]
  have h := abs_hOne_le hC hκ p.1 p.2 y
  have h0 : 0 ≤ |hOne ψ φ p.1 p.2 y| := abs_nonneg _
  nlinarith [abs_nonneg c]

theorem integrable_G (P : Measure 𝒳) [IsFiniteMeasure P] (hc : |c| ≤ 1) (hψ : IsHingeMap ψ)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x w, |ψ x w| ≤ C + |w|) (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (p : H × ℝ) : Integrable (G c ψ φ p) P :=
  Integrable.of_bound (measurable_G hψ hφ p).aestronglyMeasurable _
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact abs_G_le hc hC0 hC hκ p y)

theorem abs_G_sub (hc : |c| ≤ 1) (hψ : IsHingeMap ψ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ)
    (p p' : H × ℝ) (y : 𝒳) : |G c ψ φ p y - G c ψ φ p' y| ≤ (1 + κ) * dist p p' := by
  unfold G
  rw [← mul_sub, abs_mul]
  have h := abs_hOne_sub hψ hκ p.1 p'.1 p.2 p'.2 y
  have hd1 : ‖p.1 - p'.1‖ ≤ dist p p' := by
    rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_left _ _
  have hd2 : |p.2 - p'.2| ≤ dist p p' := by
    rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_right _ _
  have h3 : κ * ‖p.1 - p'.1‖ ≤ κ * dist p p' := mul_le_mul_of_nonneg_left hd1 hκ0
  have h0 : 0 ≤ |hOne ψ φ p.1 p.2 y - hOne ψ φ p'.1 p'.2 y| := abs_nonneg _
  nlinarith [abs_nonneg c]

omit [MeasurableSpace 𝒳] [InnerProductSpace ℝ H] in
theorem zero_mem {r ρ₁ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) : ((0 : H), (0 : ℝ)) ∈ hingePar1 (H := H) r ρ₁ := by
  refine ⟨by simpa using hr, by simpa using h1⟩

omit [MeasurableSpace 𝒳] in
theorem abs_G_le_par (hc : |c| ≤ 1) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x w, |ψ x w| ≤ C + |w|)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ : ℝ} {p : H × ℝ} (hp : p ∈ hingePar1 (H := H) r ρ₁)
    (y : 𝒳) : |G c ψ φ p y| ≤ C + (ρ₁ + κ * r) := by
  have h := abs_G_le hc hC0 hC hκ p y
  have := hp.2
  have : κ * ‖p.1‖ ≤ κ * r := mul_le_mul_of_nonneg_left hp.1 hκ0
  linarith

variable (P : Measure 𝒳) [IsProbabilityMeasure P]

theorem abs_br_le (hc : |c| ≤ 1) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x w, |ψ x w| ≤ C + |w|)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ : ℝ} {n : ℕ} (x : Fin n → 𝒳) {p : H × ℝ}
    (hp : p ∈ hingePar1 (H := H) r ρ₁) : |empDev P (G c ψ φ) n x p| ≤ 2 * (C + (ρ₁ + κ * r)) :=
  abs_empDev_single P (abs_G_le_par hc hC0 hC hκ hκ0 hp) x

theorem br_lip (hc : |c| ≤ 1) (hψ : IsHingeMap ψ) (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {n : ℕ} (x : Fin n → 𝒳) (p p' : H × ℝ) :
    dist (empDev P (G c ψ φ) n x p) (empDev P (G c ψ φ) n x p') ≤ (2 * (1 + κ)) * dist p p' := by
  obtain ⟨C, hC0, hC⟩ := growth hψ
  rw [Real.dist_eq, empDev_sub_eq P (integrable_G P hc hψ hC0 hC hφ hκ p) (integrable_G P hc hψ hC0 hC hφ hκ p')]
  have h1 := abs_empDev_single P (h := fun y => G c ψ φ p y - G c ψ φ p' y)
    (fun y => abs_G_sub hc hψ hκ hκ0 p p' y) x
  linarith

theorem continuous_br (hc : |c| ≤ 1) (hψ : IsHingeMap ψ) (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {n : ℕ} (x : Fin n → 𝒳) :
    Continuous fun p : H × ℝ => empDev P (G c ψ φ) n x p :=
  (LipschitzWith.of_dist_le' fun p p' => br_lip P hc hψ hφ hκ hκ0 x p p').continuous

theorem bdd_br (hc : |c| ≤ 1) (hψ : IsHingeMap ψ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ : ℝ} {n : ℕ}
    (x : Fin n → 𝒳) :
    BddAbove (Set.range fun p : hingePar1 (H := H) r ρ₁ => empDev P (G c ψ φ) n x p.1) := by
  obtain ⟨C, hC0, hC⟩ := growth hψ
  exact bddAbove_of_abs_le fun p => abs_br_le P hc hC0 hC hκ hκ0 x p.2

theorem Z1c_eq_iSup (hc : |c| ≤ 1) (hψ : IsHingeMap ψ) (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) {n : ℕ}
    (T₀ : Set (H × ℝ)) [Nonempty T₀] (hT₀ : T₀ ⊆ hingePar1 (H := H) r ρ₁)
    (hdense : hingePar1 (H := H) r ρ₁ ⊆ closure T₀) (x : Fin n → 𝒳) :
    Z1c P φ ψ r ρ₁ c x = ⨆ t : T₀, empDev P (G c ψ φ) n x t.1 := by
  obtain ⟨C, hC0, hC⟩ := growth hψ
  have : Nonempty (hingePar1 (H := H) r ρ₁) := ⟨⟨_, zero_mem hr h1⟩⟩
  have hb0 : BddAbove (Set.range fun t : T₀ => empDev P (G c ψ φ) n x t.1) :=
    bddAbove_of_abs_le fun t => abs_br_le P hc hC0 hC hκ hκ0 x (hT₀ t.2)
  unfold Z1c
  refine le_antisymm (ciSup_le fun p => ?_) (ciSup_le fun t => ?_)
  · have hcl : closure T₀ ⊆ {q | empDev P (G c ψ φ) n x q ≤ ⨆ t : T₀, empDev P (G c ψ φ) n x t.1} :=
      closure_minimal (fun q hq => le_ciSup hb0 ⟨q, hq⟩)
        (isClosed_le (continuous_br P hc hψ hφ hκ hκ0 x) continuous_const)
    exact hcl (hdense p.2)
  · exact le_ciSup (bdd_br P hc hψ hκ hκ0 x) ⟨t.1, hT₀ t.2⟩

omit [MeasurableSpace 𝒳] [InnerProductSpace ℝ H] [IsProbabilityMeasure P] in
theorem exists_dense [TopologicalSpace.SeparableSpace H] (r ρ₁ : ℝ) :
    ∃ T₀ : Set (H × ℝ), T₀ ⊆ hingePar1 (H := H) r ρ₁ ∧ T₀.Countable ∧ hingePar1 (H := H) r ρ₁ ⊆ closure T₀ :=
  (TopologicalSpace.IsSeparable.of_separableSpace _).exists_countable_dense_subset

theorem measurable_Z1c [TopologicalSpace.SeparableSpace H] (hc : |c| ≤ 1) (hψ : IsHingeMap ψ)
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁)
    {n : ℕ} : Measurable fun x : Fin n → 𝒳 => Z1c P φ ψ r ρ₁ c x := by
  obtain ⟨T₀, hT₀, hcount, hdense⟩ := exists_dense (H := H) r ρ₁
  have hne : T₀.Nonempty := closure_nonempty_iff.1 ⟨_, hdense (zero_mem hr h1)⟩
  have : Nonempty T₀ := hne.to_subtype
  have : Countable T₀ := hcount.to_subtype
  have heq : (fun x : Fin n → 𝒳 => Z1c P φ ψ r ρ₁ c x) = fun x => ⨆ t : T₀, empDev P (G c ψ φ) n x t.1 := by
    funext x; exact Z1c_eq_iSup P hc hψ hφ hκ hκ0 hr h1 T₀ hT₀ hdense x
  rw [heq]
  exact Measurable.iSup fun t => measurable_empDev P (fun p => measurable_G (c := c) hψ hφ p) n t.1

theorem abs_Z1c_le (hc : |c| ≤ 1) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x w, |ψ x w| ≤ C + |w|)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) {n : ℕ} (x : Fin n → 𝒳) :
    |Z1c P φ ψ r ρ₁ c x| ≤ 2 * (C + (ρ₁ + κ * r)) := by
  have : Nonempty (hingePar1 (H := H) r ρ₁) := ⟨⟨_, zero_mem hr h1⟩⟩
  exact abs_ciSup_le fun p => abs_br_le P hc hC0 hC hκ hκ0 x p.2

theorem integrable_Z1c [TopologicalSpace.SeparableSpace H] (hc : |c| ≤ 1) (hψ : IsHingeMap ψ)
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁)
    (n : ℕ) : Integrable (fun x => Z1c P φ ψ r ρ₁ c x) (Measure.pi fun _ : Fin n => P) := by
  obtain ⟨C, hC0, hC⟩ := growth hψ
  refine Integrable.of_bound (measurable_Z1c P hc hψ hφ hκ hκ0 hr h1).aestronglyMeasurable
    (2 * (C + (ρ₁ + κ * r))) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_Z1c_le P hc hC0 hC hκ hκ0 hr h1 x

end Class

/-! ### The expectation -/

/-- Pointwise Rademacher bound after contraction: `E_σ sup_{T₀} n⁻¹∑σ_i c h¹(x_i) ≤ rκ√(1/n) + ρ₁e_n`. -/
theorem radAvg_hinge_le {ψ : 𝒳 → ℝ → ℝ} {φ : 𝒳 → H} {κ c : ℝ} (hc : |c| ≤ 1) (hψ : IsHingeMap ψ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ : ℝ} (hr : 0 ≤ r)
    (T₀ : Set (H × ℝ)) [Nonempty T₀] (hT₀ : T₀ ⊆ hingePar1 (H := H) r ρ₁) {n : ℕ} (hn : n ≠ 0)
    (x : Fin n → 𝒳) :
    radAvg (fun (t : T₀) y => G c ψ φ t.1 y) n x ≤ r * κ * √(1 / (n : ℝ)) + ρ₁ * ek n := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hninv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)
  set a : T₀ → Fin n → ℝ := fun t i => (n : ℝ)⁻¹ * (t.1.2 - ⟪t.1.1, φ (x i)⟫_ℝ) with ha_def
  set ψ' : Fin n → ℝ → ℝ := fun i w => c * ((n : ℝ)⁻¹ * ψ (x i) (n * w)) with hψ_def
  set B : ℝ := ρ₁ + κ * r with hB
  have ha : ∀ t i, |a t i| ≤ B := by
    intro t i
    have hp := hT₀ t.2
    have hv : |⟪t.1.1, φ (x i)⟫_ℝ| ≤ κ * r :=
      (abs_inner_le hκ _ (x i)).trans (mul_le_mul_of_nonneg_left hp.1 hκ0)
    simp only [ha_def]
    rw [abs_mul, abs_of_pos (inv_pos.2 hnpos)]
    have h1 : |t.1.2 - ⟪t.1.1, φ (x i)⟫_ℝ| ≤ B := by
      refine (abs_sub _ _).trans ?_
      have := hp.2; rw [hB]; linarith
    calc (n : ℝ)⁻¹ * |t.1.2 - ⟪t.1.1, φ (x i)⟫_ℝ| ≤ 1 * B :=
          mul_le_mul hninv h1 (abs_nonneg _) zero_le_one
      _ = B := one_mul B
  have hψ' : ∀ i u w, |ψ' i u - ψ' i w| ≤ |u - w| := by
    intro i u w
    simp only [hψ_def]
    rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hnpos)]
    have h := lip hψ (x i) (n * u) (n * w)
    rw [show (n : ℝ) * u - n * w = n * (u - w) by ring, abs_mul, abs_of_pos hnpos] at h
    have h' : (n : ℝ)⁻¹ * |ψ (x i) (n * u) - ψ (x i) (n * w)| ≤ |u - w| := by
      calc (n : ℝ)⁻¹ * |ψ (x i) (n * u) - ψ (x i) (n * w)| ≤ (n : ℝ)⁻¹ * (n * |u - w|) :=
            mul_le_mul_of_nonneg_left h (inv_nonneg.2 hnpos.le)
        _ = |u - w| := by field_simp
    have h0 : 0 ≤ (n : ℝ)⁻¹ * |ψ (x i) (n * u) - ψ (x i) (n * w)| := by positivity
    nlinarith [abs_nonneg c, abs_nonneg (u - w)]
  have hrw : ∀ (σ : Fin n → Bool) (t : T₀),
      (n : ℝ)⁻¹ * ∑ i, rsign (σ i) * G c ψ φ t.1 (x i) = ∑ i, rsign (σ i) * ψ' i (a t i) := by
    intro σ t
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hψ_def, ha_def, G, hOne]
    rw [mul_inv_cancel_left₀ hnpos.ne']
    ring
  have hcontr := signE_iSup_contraction a ha ψ' hψ'
  set u : Fin n → H := fun i => -((n : ℝ)⁻¹ • φ (x i)) with hu_def
  have hlin : ∀ σ : Fin n → Bool, (⨆ t, ∑ i, rsign (σ i) * a t i) ≤
      r * ‖∑ i, rsign (σ i) • u i‖ + ρ₁ * ((n : ℝ)⁻¹ * |∑ i, rsign (σ i)|) := by
    intro σ
    refine ciSup_le fun t => ?_
    have hp := hT₀ t.2
    have hid : ∑ i, rsign (σ i) * a t i =
        ⟪t.1.1, ∑ i, rsign (σ i) • u i⟫_ℝ + t.1.2 * ((n : ℝ)⁻¹ * ∑ i, rsign (σ i)) := by
      rw [inner_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ha_def, hu_def, real_inner_smul_right, inner_neg_right]
      ring
    rw [hid]
    have h1 : ⟪t.1.1, ∑ i, rsign (σ i) • u i⟫_ℝ ≤ r * ‖∑ i, rsign (σ i) • u i‖ :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hp.1 (norm_nonneg _))
    have h2 : t.1.2 * ((n : ℝ)⁻¹ * ∑ i, rsign (σ i)) ≤ ρ₁ * ((n : ℝ)⁻¹ * |∑ i, rsign (σ i)|) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hnpos)]
      exact mul_le_mul_of_nonneg_right hp.2 (by positivity)
    linarith
  have hball : signE (fun σ : Fin n → Bool => ‖∑ i, rsign (σ i) • u i‖) ≤ κ * √(1 / (n : ℝ)) := by
    refine (signE_norm_sum_le u).trans ?_
    have hsum : ∑ i, ‖u i‖ ^ 2 ≤ κ ^ 2 * (1 / (n : ℝ)) := by
      calc ∑ i : Fin n, ‖u i‖ ^ 2 ≤ ∑ _i : Fin n, ((n : ℝ)⁻¹ * κ) ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            simp only [hu_def, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hnpos)]
            exact pow_le_pow_left₀ (by positivity)
              (mul_le_mul_of_nonneg_left (hκ _) (inv_nonneg.2 hnpos.le)) 2
        _ = κ ^ 2 * (1 / (n : ℝ)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    calc √(∑ i, ‖u i‖ ^ 2) ≤ √(κ ^ 2 * (1 / (n : ℝ))) := Real.sqrt_le_sqrt hsum
      _ = κ * √(1 / (n : ℝ)) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ0]
  have hX : signE (fun σ : Fin n → Bool => |∑ i, rsign (σ i)|) = n * ek n := by
    rw [signE_eq_radE, mul_ek hn]
  unfold radAvg
  rw [← signE_eq_radE]
  simp_rw [hrw]
  calc signE (fun σ => ⨆ t : T₀, ∑ i, rsign (σ i) * ψ' i (a t i))
      ≤ signE (fun σ => ⨆ t : T₀, ∑ i, rsign (σ i) * a t i) := hcontr
    _ ≤ signE (fun σ : Fin n → Bool => r * ‖∑ i, rsign (σ i) • u i‖ +
          ρ₁ * ((n : ℝ)⁻¹ * |∑ i, rsign (σ i)|)) := signE_mono hlin
    _ = r * signE (fun σ : Fin n → Bool => ‖∑ i, rsign (σ i) • u i‖) +
          ρ₁ * ((n : ℝ)⁻¹ * signE (fun σ : Fin n → Bool => |∑ i, rsign (σ i)|)) := by
        rw [signE_add, signE_const_mul, signE_const_mul, signE_const_mul]
    _ ≤ r * κ * √(1 / (n : ℝ)) + ρ₁ * ek n := by
        rw [hX]
        have key : (n : ℝ)⁻¹ * (n * ek n) = ek n := by field_simp
        rw [key]
        have := mul_le_mul_of_nonneg_left hball hr
        nlinarith

theorem integral_Z1c_le (P : Measure 𝒳) [IsProbabilityMeasure P] [TopologicalSpace.SeparableSpace H]
    {ψ : 𝒳 → ℝ → ℝ} {φ : 𝒳 → H} {κ c : ℝ} (hc : |c| ≤ 1) (hψ : IsHingeMap ψ) (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) {n : ℕ} (hn : n ≠ 0) :
    ∫ x, Z1c P φ ψ r ρ₁ c x ∂(Measure.pi fun _ : Fin n => P) ≤ 2 * (r * κ * √(1 / (n : ℝ)) + ρ₁ * ek n) := by
  obtain ⟨C, hC0, hC⟩ := growth hψ
  obtain ⟨T₀, hT₀, hcount, hdense⟩ := exists_dense (H := H) r ρ₁
  have hne : T₀.Nonempty := closure_nonempty_iff.1 ⟨_, hdense (zero_mem hr h1)⟩
  have : Nonempty T₀ := hne.to_subtype
  have : Countable T₀ := hcount.to_subtype
  set g : T₀ → 𝒳 → ℝ := fun t y => G c ψ φ t.1 y with hg
  have hm : ∀ t, Measurable (g t) := fun t => measurable_G hψ hφ t.1
  set B : ℝ := C + (ρ₁ + κ * r) with hB
  have hBg : ∀ t y, |g t y| ≤ B := fun t y => abs_G_le_par hc hC0 hC hκ hκ0 (hT₀ t.2) y
  have hsym := integral_iSup_empDev_le P hm hBg hn
  have heq : ∀ x : Fin n → 𝒳, Z1c P φ ψ r ρ₁ c x = ⨆ t : T₀, empDev P g n x t := by
    intro x
    rw [Z1c_eq_iSup P hc hψ hφ hκ hκ0 hr h1 T₀ hT₀ hdense x]
    rfl
  simp_rw [heq]
  refine hsym.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have hint : Integrable (radAvg g n) (Measure.pi fun _ : Fin n => P) := by
    refine Integrable.of_bound (measurable_radAvg hm n).aestronglyMeasurable B (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    exact abs_radAvg_le hBg hn x
  have := integral_mono hint (integrable_const (r * κ * √(1 / (n : ℝ)) + ρ₁ * ek n))
    fun x => radAvg_hinge_le hc hψ hκ hκ0 hr T₀ hT₀ hn x
  rwa [integral_const, probReal_univ, one_smul] at this

/-! ### The tail -/

section Tail

variable (P : Measure 𝒳) [IsProbabilityMeasure P] {ψ : 𝒳 → ℝ → ℝ} {φ : 𝒳 → H} {κ c : ℝ}

theorem Z1c_update (hc : |c| ≤ 1) (hψ : IsHingeMap ψ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ)
    {r ρ₁ Δ₁ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁)
    (hΔ₁ : ∀ p ∈ hingePar1 (H := H) r ρ₁, ∀ x x' : 𝒳, |hOne ψ φ p.1 p.2 x - hOne ψ φ p.1 p.2 x'| ≤ Δ₁)
    {n : ℕ} (x : Fin n → 𝒳) (i : Fin n) (b : 𝒳) :
    |Z1c P φ ψ r ρ₁ c (Function.update x i b) - Z1c P φ ψ r ρ₁ c x| ≤ Δ₁ / n := by
  have : Nonempty (hingePar1 (H := H) r ρ₁) := ⟨⟨_, zero_mem hr h1⟩⟩
  have hnn : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  refine abs_iSup_sub_iSup_le (bdd_br P hc hψ hκ hκ0 _) (bdd_br P hc hψ hκ hκ0 _) fun p => ?_
  rw [empDev_update_sub, abs_mul, abs_inv, Nat.abs_cast, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ hnn
  simp only [G]
  rw [← mul_sub, abs_mul]
  have hd := hΔ₁ p.1 p.2 b (x i)
  have h0 : 0 ≤ |hOne ψ φ (↑p : H × ℝ).1 (↑p : H × ℝ).2 b - hOne ψ φ (↑p : H × ℝ).1 (↑p : H × ℝ).2 (x i)| :=
    abs_nonneg _
  nlinarith [abs_nonneg c]

theorem tail_Z1c [TopologicalSpace.SeparableSpace H] (hc : |c| ≤ 1) (hψ : IsHingeMap ψ)
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ Δ₁ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁)
    {n : ℕ} (hn : 1 ≤ n)
    (hΔ₁ : ∀ p ∈ hingePar1 (H := H) r ρ₁, ∀ x x' : 𝒳, |hOne ψ φ p.1 p.2 x - hOne ψ φ p.1 p.2 x'| ≤ Δ₁)
    (hV : 0 < Δ₁ ^ 2 / n) {χ : ℝ} (hχ : 0 < χ) :
    TailAtLeast (Measure.pi fun _ : Fin n => P) (fun x => Z1c P φ ψ r ρ₁ c x) (√(χ * (Δ₁ ^ 2 / n) / 2)) χ := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have hΔ₁0 : 0 ≤ Δ₁ := (abs_nonneg _).trans (hΔ₁ _ (zero_mem hr h1) x₀ x₀)
  set F : (Fin n → 𝒳) → ℝ := fun x => Z1c P φ ψ r ρ₁ c x with hF
  have hFm : Measurable F := measurable_Z1c P hc hψ hφ hκ hκ0 hr h1
  set V : ℝ := Δ₁ ^ 2 / n with hVdef
  set ε : ℝ := √(χ * V / 2) with hε
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  have hc0 : 0 ≤ Δ₁ / n := by positivity
  have htail := (TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences_fin P F hFm (Δ₁ / n)
    (fun x i b => Z1c_update P hc hψ hκ hκ0 hr h1 hΔ₁ x i b)).measure_ge_le hε0
  have hcoe : (((n : ℝ≥0) * ((Δ₁ / n).toNNReal / 2) ^ 2 : ℝ≥0) : ℝ) = n * (Δ₁ / n) ^ 2 / 4 := by
    push_cast [Real.coe_toNNReal _ hc0]; ring
  rw [hcoe] at htail
  have hexp : -ε ^ 2 / (2 * (n * (Δ₁ / n) ^ 2 / 4)) = -χ := by
    have e1 : (n : ℝ) * (Δ₁ / n) ^ 2 / 4 = V / 4 := by rw [hVdef]; field_simp
    rw [e1, hε, Real.sq_sqrt (by positivity)]
    field_simp
    norm_num
  rw [hexp] at htail
  unfold TailAtLeast
  change (Measure.pi fun _ : Fin n => P) {x | (∫ w, F w ∂(Measure.pi fun _ : Fin n => P)) + ε ≤ F x} ≤ _
  have hsub : {x | (∫ w, F w ∂(Measure.pi fun _ : Fin n => P)) + ε ≤ F x} ⊆
      {x | ε ≤ F x - ∫ w, F w ∂(Measure.pi fun _ : Fin n => P)} := by
    intro x hx; simp only [mem_ofPred_eq] at hx ⊢; linarith
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal ((measureReal_mono hsub).trans htail)

theorem Z1c_eq_zero (_hc : |c| ≤ 1) (_hψ : IsHingeMap ψ) (_hκ : ∀ x, ‖φ x‖ ≤ κ) (_hκ0 : 0 ≤ κ)
    {r ρ₁ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) {n : ℕ} (hn : n ≠ 0)
    (hΔ₁ : ∀ p ∈ hingePar1 (H := H) r ρ₁, ∀ x x' : 𝒳, |hOne ψ φ p.1 p.2 x - hOne ψ φ p.1 p.2 x'| ≤ 0)
    (x : Fin n → 𝒳) : Z1c P φ ψ r ρ₁ c x = 0 := by
  have : Nonempty (hingePar1 (H := H) r ρ₁) := ⟨⟨_, zero_mem hr h1⟩⟩
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have hzero : ∀ p : hingePar1 (H := H) r ρ₁, empDev P (G c ψ φ) n x p.1 = 0 := by
    intro p
    have hk := const_of_osc (hΔ₁ p.1 p.2) x₀
    exact empDev_const P (g := G c ψ φ) (t := p.1) (K := c * hOne ψ φ p.1.1 p.1.2 x₀)
      (fun y => by simp only [G, hk y]) hn x
  unfold Z1c
  simp only [hzero, ciSup_const]

theorem tail_strict_Z1c [TopologicalSpace.SeparableSpace H] (hc : |c| ≤ 1) (hψ : IsHingeMap ψ)
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ Δ₁ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁)
    {n : ℕ} (hn : 1 ≤ n)
    (hΔ₁ : ∀ p ∈ hingePar1 (H := H) r ρ₁, ∀ x x' : 𝒳, |hOne ψ φ p.1 p.2 x - hOne ψ φ p.1 p.2 x'| ≤ Δ₁)
    {χ : ℝ} (hχ : 0 < χ) :
    TailMoreThan (Measure.pi fun _ : Fin n => P) (fun x => Z1c P φ ψ r ρ₁ c x) (√(χ * (Δ₁ ^ 2 / n) / 2)) χ := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hA0 : 0 ≤ Δ₁ ^ 2 / n := by positivity
  rcases hA0.lt_or_eq with hV | hV
  · have h := tail_Z1c P hc hψ hφ hκ hκ0 hr h1 hn hΔ₁ hV hχ
    unfold TailAtLeast at h
    unfold TailMoreThan
    refine le_trans (measure_mono fun z hz => ?_) h
    simp only [mem_ofPred_eq] at hz ⊢
    exact hz.le
  · have hd1 : Δ₁ = 0 := by
      rcases div_eq_zero_iff.1 hV.symm with h | h
      · exact pow_eq_zero_iff two_ne_zero |>.1 h
      · exact absurd h hnpos.ne'
    have hZ0 : ∀ x : Fin n → 𝒳, Z1c P φ ψ r ρ₁ c x = 0 := fun x =>
      Z1c_eq_zero P hc hψ hκ hκ0 hr h1 (by omega) (fun p hp x x' => hd1 ▸ hΔ₁ p hp x x') x
    unfold TailMoreThan
    simp only [hZ0, integral_zero, zero_add]
    refine le_trans (measure_mono (t := ∅) fun ω hω => ?_) (by rw [measure_empty]; exact zero_le)
    simp only [mem_ofPred_eq] at hω
    exact absurd hω (not_lt.2 (Real.sqrt_nonneg _))

end Tail

end StatFormal.Wave30ty.ROne
