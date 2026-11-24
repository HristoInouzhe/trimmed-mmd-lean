import StatFormal.Wave30ty.RouteBasic
import StatFormal.Wave30tp.RouteMcDiarmid2

set_option linter.style.longLine false

/-!
# Route: `lem:hinge (v2)`, two samples (untrusted proof material)

One supremum `Zc c` for a sign `c` (`|c| ≤ 1`) covers both `Z` (`c = −1`: `(P − P_n)h = (P_n − P)(−h)`) and `Z⁻` (`c = 1`).
* the bracket `brc c z p = (P_n − P)(c h¹_p) + (Q_m − Q)(c h²_p)` is bounded on `𝒮` and Lipschitz in `p` for every sample, so the
  supremum over `𝒮` is a supremum over a countable dense subset (`H × ℝ × ℝ` separable): measurability, integrability;
* expectation: two-sample signed symmetrisation (`integral_iSup_empDev2_le`), coordinatewise contraction
  (`signE_iSup_contraction`) with the sample-dependent 1-Lipschitz maps `w ↦ c n⁻¹ ψ¹_{X_i}(n w)`, `w ↦ c m⁻¹ ψ²_{Y_j}(m w)`, then
  the linear bound `r‖S_σ‖ + ρ₁|σ̄| + ρ₂|σ̄'|` and `E‖S_σ‖ ≤ κ√s`;
* tail: two-sample McDiarmid (`Wave30tp.mcdiarmid_two_sample`) with differences `Δ₁/n`, `Δ₂/m` when `Δ₁²/n + Δ₂²/m > 0`; when it
  is `0`, every `h` is constant in the point and `Zc ≡ 0`.
-/

noncomputable section
open MeasureTheory Set Finset
open scoped InnerProductSpace

namespace StatFormal.Wave30ty.RTwo

open StatFormal.Wave30ty StatFormal.Wave30ty.RBasic StatFormal.Concentration StatFormal.Wave30tp
  StatFormal.Wave30tr

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `c · h¹_{v,a}` indexed by `p = (v, a, b)`. -/
def G1 (c : ℝ) (ψ : 𝒳 → ℝ → ℝ) (φ : 𝒳 → H) (p : H × ℝ × ℝ) (y : 𝒳) : ℝ := c * hOne ψ φ p.1 p.2.1 y

/-- `c · h²_{v,b}` indexed by `p = (v, a, b)`. -/
def G2 (c : ℝ) (ψ : 𝒳 → ℝ → ℝ) (φ : 𝒳 → H) (p : H × ℝ × ℝ) (y : 𝒳) : ℝ := c * hTwo ψ φ p.1 p.2.2 y

/-- The bracket `(P_n − P)(c h¹_p) + (Q_m − Q)(c h²_p)`. -/
def brc (P Q : Measure 𝒳) (φ : 𝒳 → H) (ψ₁ ψ₂ : 𝒳 → ℝ → ℝ) (c : ℝ) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) (p : H × ℝ × ℝ) : ℝ :=
  empDev P (G1 c ψ₁ φ) n z.1 p + empDev Q (G2 c ψ₂ φ) m z.2 p

/-- `sup_𝒮` of the bracket. -/
def Zc (P Q : Measure 𝒳) (φ : 𝒳 → H) (ψ₁ ψ₂ : 𝒳 → ℝ → ℝ) (r ρ₁ ρ₂ c : ℝ) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) : ℝ :=
  ⨆ p : hingePar (H := H) r ρ₁ ρ₂, brc P Q φ ψ₁ ψ₂ c z p.1

theorem hingeZ_eq (P Q : Measure 𝒳) (φ : 𝒳 → H) (ψ₁ ψ₂ : 𝒳 → ℝ → ℝ) (r ρ₁ ρ₂ : ℝ) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) : hingeZ P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ z = Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ (-1) z := by
  unfold hingeZ Zc
  congr 1; funext p
  simp only [brc, empDev, G1, G2, devPop, neg_one_mul, integral_neg, Finset.sum_neg_distrib]
  ring

theorem hingeZm_eq (P Q : Measure 𝒳) (φ : 𝒳 → H) (ψ₁ ψ₂ : 𝒳 → ℝ → ℝ) (r ρ₁ ρ₂ : ℝ) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) : hingeZm P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ z = Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ 1 z := by
  unfold hingeZm Zc
  congr 1; funext p
  simp only [brc, empDev, G1, G2, devEmp, one_mul]

section Class

variable {ψ₁ ψ₂ : 𝒳 → ℝ → ℝ} {φ : 𝒳 → H} {κ c : ℝ}

theorem measurable_G1 (hψ : IsHingeMap ψ₁) (hφ : StronglyMeasurable φ) (p : H × ℝ × ℝ) :
    Measurable (G1 c ψ₁ φ p) := (measurable_hOne hψ hφ p.1 p.2.1).const_mul c

theorem measurable_G2 (hψ : IsHingeMap ψ₂) (hφ : StronglyMeasurable φ) (p : H × ℝ × ℝ) :
    Measurable (G2 c ψ₂ φ p) := (measurable_hTwo hψ hφ p.1 p.2.2).const_mul c

omit [MeasurableSpace 𝒳] in
theorem abs_G1_le (hc : |c| ≤ 1) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x w, |ψ₁ x w| ≤ C + |w|) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (p : H × ℝ × ℝ) (y : 𝒳) : |G1 c ψ₁ φ p y| ≤ C + (|p.2.1| + κ * ‖p.1‖) := by
  unfold G1
  rw [abs_mul]
  have h := abs_hOne_le hC hκ p.1 p.2.1 y
  have h0 : 0 ≤ |hOne ψ₁ φ p.1 p.2.1 y| := abs_nonneg _
  nlinarith [abs_nonneg c]

omit [MeasurableSpace 𝒳] in
theorem abs_G2_le (hc : |c| ≤ 1) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x w, |ψ₂ x w| ≤ C + |w|) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (p : H × ℝ × ℝ) (y : 𝒳) : |G2 c ψ₂ φ p y| ≤ C + (|p.2.2| + κ * ‖p.1‖) := by
  unfold G2
  rw [abs_mul]
  have h := abs_hTwo_le hC hκ p.1 p.2.2 y
  have h0 : 0 ≤ |hTwo ψ₂ φ p.1 p.2.2 y| := abs_nonneg _
  nlinarith [abs_nonneg c]

theorem integrable_G1 (P : Measure 𝒳) [IsFiniteMeasure P] (hc : |c| ≤ 1) (hψ : IsHingeMap ψ₁)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x w, |ψ₁ x w| ≤ C + |w|) (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (p : H × ℝ × ℝ) : Integrable (G1 c ψ₁ φ p) P :=
  Integrable.of_bound (measurable_G1 hψ hφ p).aestronglyMeasurable _
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact abs_G1_le hc hC0 hC hκ p y)

theorem integrable_G2 (Q : Measure 𝒳) [IsFiniteMeasure Q] (hc : |c| ≤ 1) (hψ : IsHingeMap ψ₂)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x w, |ψ₂ x w| ≤ C + |w|) (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (p : H × ℝ × ℝ) : Integrable (G2 c ψ₂ φ p) Q :=
  Integrable.of_bound (measurable_G2 hψ hφ p).aestronglyMeasurable _
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact abs_G2_le hc hC0 hC hκ p y)

theorem abs_G1_sub (hc : |c| ≤ 1) (hψ : IsHingeMap ψ₁) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ)
    (p p' : H × ℝ × ℝ) (y : 𝒳) : |G1 c ψ₁ φ p y - G1 c ψ₁ φ p' y| ≤ (1 + κ) * dist p p' := by
  unfold G1
  rw [← mul_sub, abs_mul]
  have h := abs_hOne_sub hψ hκ p.1 p'.1 p.2.1 p'.2.1 y
  have hd1 : ‖p.1 - p'.1‖ ≤ dist p p' := by
    rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_left _ _
  have hd2 : |p.2.1 - p'.2.1| ≤ dist p p' := by
    rw [← Real.dist_eq, Prod.dist_eq, Prod.dist_eq]; exact (le_max_left _ _).trans (le_max_right _ _)
  have h3 : κ * ‖p.1 - p'.1‖ ≤ κ * dist p p' := mul_le_mul_of_nonneg_left hd1 hκ0
  have h0 : 0 ≤ |hOne ψ₁ φ p.1 p.2.1 y - hOne ψ₁ φ p'.1 p'.2.1 y| := abs_nonneg _
  nlinarith [abs_nonneg c]

theorem abs_G2_sub (hc : |c| ≤ 1) (hψ : IsHingeMap ψ₂) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ)
    (p p' : H × ℝ × ℝ) (y : 𝒳) : |G2 c ψ₂ φ p y - G2 c ψ₂ φ p' y| ≤ (1 + κ) * dist p p' := by
  unfold G2
  rw [← mul_sub, abs_mul]
  have h := abs_hTwo_sub hψ hκ p.1 p'.1 p.2.2 p'.2.2 y
  have hd1 : ‖p.1 - p'.1‖ ≤ dist p p' := by
    rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_left _ _
  have hd2 : |p.2.2 - p'.2.2| ≤ dist p p' := by
    rw [← Real.dist_eq, Prod.dist_eq, Prod.dist_eq]; exact (le_max_right _ _).trans (le_max_right _ _)
  have h3 : κ * ‖p.1 - p'.1‖ ≤ κ * dist p p' := mul_le_mul_of_nonneg_left hd1 hκ0
  have h0 : 0 ≤ |hTwo ψ₂ φ p.1 p.2.2 y - hTwo ψ₂ φ p'.1 p'.2.2 y| := abs_nonneg _
  nlinarith [abs_nonneg c]

omit [MeasurableSpace 𝒳] [InnerProductSpace ℝ H] in
theorem zero_mem {r ρ₁ ρ₂ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) (h2 : 0 ≤ ρ₂) :
    ((0 : H), (0 : ℝ), (0 : ℝ)) ∈ hingePar (H := H) r ρ₁ ρ₂ := by
  refine ⟨by simpa using hr, by simpa using h1, by simpa using h2⟩

omit [MeasurableSpace 𝒳] in
theorem abs_G1_le_par (hc : |c| ≤ 1) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x w, |ψ₁ x w| ≤ C + |w|)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ ρ₂ : ℝ} {p : H × ℝ × ℝ} (hp : p ∈ hingePar (H := H) r ρ₁ ρ₂)
    (y : 𝒳) : |G1 c ψ₁ φ p y| ≤ C + (ρ₁ + κ * r) := by
  have h := abs_G1_le hc hC0 hC hκ p y
  have := hp.2.1
  have : κ * ‖p.1‖ ≤ κ * r := mul_le_mul_of_nonneg_left hp.1 hκ0
  linarith

omit [MeasurableSpace 𝒳] in
theorem abs_G2_le_par (hc : |c| ≤ 1) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x w, |ψ₂ x w| ≤ C + |w|)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ ρ₂ : ℝ} {p : H × ℝ × ℝ} (hp : p ∈ hingePar (H := H) r ρ₁ ρ₂)
    (y : 𝒳) : |G2 c ψ₂ φ p y| ≤ C + (ρ₂ + κ * r) := by
  have h := abs_G2_le hc hC0 hC hκ p y
  have := hp.2.2
  have : κ * ‖p.1‖ ≤ κ * r := mul_le_mul_of_nonneg_left hp.1 hκ0
  linarith

variable (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

theorem abs_brc_le (hc : |c| ≤ 1) {C₁ C₂ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₁ : ∀ x w, |ψ₁ x w| ≤ C₁ + |w|)
    (hC₂0 : 0 ≤ C₂) (hC₂ : ∀ x w, |ψ₂ x w| ≤ C₂ + |w|) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ)
    {r ρ₁ ρ₂ : ℝ} {n m : ℕ} (z : (Fin n → 𝒳) × (Fin m → 𝒳)) {p : H × ℝ × ℝ}
    (hp : p ∈ hingePar (H := H) r ρ₁ ρ₂) :
    |brc P Q φ ψ₁ ψ₂ c z p| ≤ 2 * (C₁ + (ρ₁ + κ * r)) + 2 * (C₂ + (ρ₂ + κ * r)) := by
  unfold brc
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact abs_empDev_single P (abs_G1_le_par hc hC₁0 hC₁ hκ hκ0 hp) z.1
  · exact abs_empDev_single Q (abs_G2_le_par hc hC₂0 hC₂ hκ hκ0 hp) z.2

theorem brc_lip (hc : |c| ≤ 1) (hψ₁ : IsHingeMap ψ₁) (hψ₂ : IsHingeMap ψ₂) (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {n m : ℕ} (z : (Fin n → 𝒳) × (Fin m → 𝒳)) (p p' : H × ℝ × ℝ) :
    dist (brc P Q φ ψ₁ ψ₂ c z p) (brc P Q φ ψ₁ ψ₂ c z p') ≤ (4 * (1 + κ)) * dist p p' := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := growth hψ₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := growth hψ₂
  rw [Real.dist_eq]
  have e : brc P Q φ ψ₁ ψ₂ c z p - brc P Q φ ψ₁ ψ₂ c z p' =
      (empDev P (G1 c ψ₁ φ) n z.1 p - empDev P (G1 c ψ₁ φ) n z.1 p') +
        (empDev Q (G2 c ψ₂ φ) m z.2 p - empDev Q (G2 c ψ₂ φ) m z.2 p') := by
    unfold brc; ring
  rw [e, empDev_sub_eq P (integrable_G1 P hc hψ₁ hC₁0 hC₁ hφ hκ p) (integrable_G1 P hc hψ₁ hC₁0 hC₁ hφ hκ p'),
    empDev_sub_eq Q (integrable_G2 Q hc hψ₂ hC₂0 hC₂ hφ hκ p) (integrable_G2 Q hc hψ₂ hC₂0 hC₂ hφ hκ p')]
  refine (abs_add_le _ _).trans ?_
  have h1 := abs_empDev_single P (h := fun y => G1 c ψ₁ φ p y - G1 c ψ₁ φ p' y)
    (fun y => abs_G1_sub hc hψ₁ hκ hκ0 p p' y) z.1
  have h2 := abs_empDev_single Q (h := fun y => G2 c ψ₂ φ p y - G2 c ψ₂ φ p' y)
    (fun y => abs_G2_sub hc hψ₂ hκ hκ0 p p' y) z.2
  linarith

theorem continuous_brc (hc : |c| ≤ 1) (hψ₁ : IsHingeMap ψ₁) (hψ₂ : IsHingeMap ψ₂) (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {n m : ℕ} (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    Continuous fun p : H × ℝ × ℝ => brc P Q φ ψ₁ ψ₂ c z p :=
  (LipschitzWith.of_dist_le' fun p p' => brc_lip P Q hc hψ₁ hψ₂ hφ hκ hκ0 z p p').continuous

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
theorem measurable_brc (hψ₁ : IsHingeMap ψ₁) (hψ₂ : IsHingeMap ψ₂) (hφ : StronglyMeasurable φ) {n m : ℕ}
    (p : H × ℝ × ℝ) : Measurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => brc P Q φ ψ₁ ψ₂ c z p :=
  ((measurable_empDev P (fun t => measurable_G1 (c := c) hψ₁ hφ t) n p).comp measurable_fst).add
    ((measurable_empDev Q (fun t => measurable_G2 (c := c) hψ₂ hφ t) m p).comp measurable_snd)

theorem bdd_brc (hc : |c| ≤ 1) (hψ₁ : IsHingeMap ψ₁) (hψ₂ : IsHingeMap ψ₂) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hκ0 : 0 ≤ κ) {r ρ₁ ρ₂ : ℝ} {n m : ℕ} (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    BddAbove (Set.range fun p : hingePar (H := H) r ρ₁ ρ₂ => brc P Q φ ψ₁ ψ₂ c z p.1) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := growth hψ₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := growth hψ₂
  exact bddAbove_of_abs_le fun p => abs_brc_le P Q hc hC₁0 hC₁ hC₂0 hC₂ hκ hκ0 z p.2

/-- The supremum over `𝒮` equals the supremum over a dense subset. -/
theorem Zc_eq_iSup (hc : |c| ≤ 1) (hψ₁ : IsHingeMap ψ₁) (hψ₂ : IsHingeMap ψ₂) (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ ρ₂ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) (h2 : 0 ≤ ρ₂) {n m : ℕ}
    (T₀ : Set (H × ℝ × ℝ)) [Nonempty T₀] (hT₀ : T₀ ⊆ hingePar (H := H) r ρ₁ ρ₂)
    (hdense : hingePar (H := H) r ρ₁ ρ₂ ⊆ closure T₀) (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c z = ⨆ t : T₀, brc P Q φ ψ₁ ψ₂ c z t.1 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := growth hψ₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := growth hψ₂
  have : Nonempty (hingePar (H := H) r ρ₁ ρ₂) := ⟨⟨_, zero_mem hr h1 h2⟩⟩
  have hb0 : BddAbove (Set.range fun t : T₀ => brc P Q φ ψ₁ ψ₂ c z t.1) :=
    bddAbove_of_abs_le fun t => abs_brc_le P Q hc hC₁0 hC₁ hC₂0 hC₂ hκ hκ0 z (hT₀ t.2)
  unfold Zc
  refine le_antisymm (ciSup_le fun p => ?_) (ciSup_le fun t => ?_)
  · have hcl : closure T₀ ⊆ {q | brc P Q φ ψ₁ ψ₂ c z q ≤ ⨆ t : T₀, brc P Q φ ψ₁ ψ₂ c z t.1} :=
      closure_minimal (fun q hq => le_ciSup hb0 ⟨q, hq⟩)
        (isClosed_le (continuous_brc P Q hc hψ₁ hψ₂ hφ hκ hκ0 z) continuous_const)
    exact hcl (hdense p.2)
  · exact le_ciSup (bdd_brc P Q hc hψ₁ hψ₂ hκ hκ0 z) ⟨t.1, hT₀ t.2⟩

omit [MeasurableSpace 𝒳] [InnerProductSpace ℝ H] in
theorem exists_dense [TopologicalSpace.SeparableSpace H] (r ρ₁ ρ₂ : ℝ) :
    ∃ T₀ : Set (H × ℝ × ℝ), T₀ ⊆ hingePar (H := H) r ρ₁ ρ₂ ∧ T₀.Countable ∧
      hingePar (H := H) r ρ₁ ρ₂ ⊆ closure T₀ :=
  (TopologicalSpace.IsSeparable.of_separableSpace _).exists_countable_dense_subset

theorem measurable_Zc [TopologicalSpace.SeparableSpace H] (hc : |c| ≤ 1) (hψ₁ : IsHingeMap ψ₁)
    (hψ₂ : IsHingeMap ψ₂) (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ ρ₂ : ℝ}
    (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) (h2 : 0 ≤ ρ₂) {n m : ℕ} :
    Measurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c z := by
  obtain ⟨T₀, hT₀, hcount, hdense⟩ := exists_dense (H := H) r ρ₁ ρ₂
  have hne : T₀.Nonempty := closure_nonempty_iff.1 ⟨_, hdense (zero_mem hr h1 h2)⟩
  have : Nonempty T₀ := hne.to_subtype
  have : Countable T₀ := hcount.to_subtype
  have heq : (fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c z) =
      fun z => ⨆ t : T₀, brc P Q φ ψ₁ ψ₂ c z t.1 := by
    funext z; exact Zc_eq_iSup P Q hc hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2 T₀ hT₀ hdense z
  rw [heq]
  exact Measurable.iSup fun t => measurable_brc P Q hψ₁ hψ₂ hφ t.1

theorem abs_Zc_le (hc : |c| ≤ 1) {C₁ C₂ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₁ : ∀ x w, |ψ₁ x w| ≤ C₁ + |w|)
    (hC₂0 : 0 ≤ C₂) (hC₂ : ∀ x w, |ψ₂ x w| ≤ C₂ + |w|) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ)
    {r ρ₁ ρ₂ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) (h2 : 0 ≤ ρ₂) {n m : ℕ} (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    |Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c z| ≤ 2 * (C₁ + (ρ₁ + κ * r)) + 2 * (C₂ + (ρ₂ + κ * r)) := by
  have : Nonempty (hingePar (H := H) r ρ₁ ρ₂) := ⟨⟨_, zero_mem hr h1 h2⟩⟩
  exact abs_ciSup_le fun p => abs_brc_le P Q hc hC₁0 hC₁ hC₂0 hC₂ hκ hκ0 z p.2

theorem integrable_Zc [TopologicalSpace.SeparableSpace H] (hc : |c| ≤ 1) (hψ₁ : IsHingeMap ψ₁)
    (hψ₂ : IsHingeMap ψ₂) (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ ρ₂ : ℝ}
    (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) (h2 : 0 ≤ ρ₂) (n m : ℕ) :
    Integrable (fun z => Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c z) (sampleLaw P Q n m) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := growth hψ₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := growth hψ₂
  refine Integrable.of_bound (measurable_Zc P Q hc hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2).aestronglyMeasurable
    (2 * (C₁ + (ρ₁ + κ * r)) + 2 * (C₂ + (ρ₂ + κ * r))) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  exact abs_Zc_le P Q hc hC₁0 hC₁ hC₂0 hC₂ hκ hκ0 hr h1 h2 z

end Class

/-! ### The expectation -/

/-- Pointwise Rademacher bound after contraction:
`E_σ sup_{T₀} [n⁻¹∑σ_i c h¹(x_i) + m⁻¹∑σ'_j c h²(y_j)] ≤ rκ√s + ρ₁e_n + ρ₂e_m`. -/
theorem radAvg2_hinge_le {ψ₁ ψ₂ : 𝒳 → ℝ → ℝ} {φ : 𝒳 → H} {κ c : ℝ} (hc : |c| ≤ 1) (hψ₁ : IsHingeMap ψ₁)
    (hψ₂ : IsHingeMap ψ₂) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {r ρ₁ ρ₂ : ℝ} (hr : 0 ≤ r)
    (T₀ : Set (H × ℝ × ℝ)) [Nonempty T₀] (hT₀ : T₀ ⊆ hingePar (H := H) r ρ₁ ρ₂) {n m : ℕ} (hn : n ≠ 0)
    (hm : m ≠ 0) (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    radAvg2 (fun (t : T₀) y => G1 c ψ₁ φ t.1 y) (fun (t : T₀) y => G2 c ψ₂ φ t.1 y) n m z ≤
      r * κ * √(sNM n m) + ρ₁ * ek n + ρ₂ * ek m := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
  have hninv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)
  have hminv : (m : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm)
  set a : T₀ → Fin n ⊕ Fin m → ℝ := fun t k =>
    Sum.elim (fun i => (n : ℝ)⁻¹ * (t.1.2.1 - ⟪t.1.1, φ (z.1 i)⟫_ℝ))
      (fun j => (m : ℝ)⁻¹ * (⟪t.1.1, φ (z.2 j)⟫_ℝ - t.1.2.2)) k with ha_def
  set ψ : Fin n ⊕ Fin m → ℝ → ℝ := fun k w =>
    Sum.elim (fun i => c * ((n : ℝ)⁻¹ * ψ₁ (z.1 i) (n * w)))
      (fun j => c * ((m : ℝ)⁻¹ * ψ₂ (z.2 j) (m * w))) k with hψ_def
  set B : ℝ := ρ₁ + ρ₂ + 2 * κ * r with hB
  have ha : ∀ t k, |a t k| ≤ B := by
    intro t k
    have hp := hT₀ t.2
    have hv : ∀ x, |⟪t.1.1, φ x⟫_ℝ| ≤ κ * r := fun x =>
      (abs_inner_le hκ _ x).trans (mul_le_mul_of_nonneg_left hp.1 hκ0)
    have hρ₂ : 0 ≤ ρ₂ := (abs_nonneg _).trans hp.2.2
    have hρ₁ : 0 ≤ ρ₁ := (abs_nonneg _).trans hp.2.1
    cases k with
    | inl i =>
      simp only [ha_def, Sum.elim_inl]
      rw [abs_mul, abs_of_pos (inv_pos.2 hnpos)]
      have h1 : |t.1.2.1 - ⟪t.1.1, φ (z.1 i)⟫_ℝ| ≤ B := by
        refine (abs_sub _ _).trans ?_
        have := hp.2.1; have := hv (z.1 i); rw [hB]; nlinarith
      calc (n : ℝ)⁻¹ * |t.1.2.1 - ⟪t.1.1, φ (z.1 i)⟫_ℝ| ≤ 1 * B :=
            mul_le_mul hninv h1 (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    | inr j =>
      simp only [ha_def, Sum.elim_inr]
      rw [abs_mul, abs_of_pos (inv_pos.2 hmpos)]
      have h1 : |⟪t.1.1, φ (z.2 j)⟫_ℝ - t.1.2.2| ≤ B := by
        refine (abs_sub _ _).trans ?_
        have := hp.2.2; have := hv (z.2 j); rw [hB]; nlinarith
      calc (m : ℝ)⁻¹ * |⟪t.1.1, φ (z.2 j)⟫_ℝ - t.1.2.2| ≤ 1 * B :=
            mul_le_mul hminv h1 (abs_nonneg _) zero_le_one
        _ = B := one_mul B
  have hψ : ∀ k x y, |ψ k x - ψ k y| ≤ |x - y| := by
    intro k x y
    cases k with
    | inl i =>
      simp only [hψ_def, Sum.elim_inl]
      rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hnpos)]
      have h := lip hψ₁ (z.1 i) (n * x) (n * y)
      rw [show (n : ℝ) * x - n * y = n * (x - y) by ring, abs_mul, abs_of_pos hnpos] at h
      have h' : (n : ℝ)⁻¹ * |ψ₁ (z.1 i) (n * x) - ψ₁ (z.1 i) (n * y)| ≤ |x - y| := by
        calc (n : ℝ)⁻¹ * |ψ₁ (z.1 i) (n * x) - ψ₁ (z.1 i) (n * y)| ≤ (n : ℝ)⁻¹ * (n * |x - y|) :=
              mul_le_mul_of_nonneg_left h (inv_nonneg.2 hnpos.le)
          _ = |x - y| := by field_simp
      have h0 : 0 ≤ (n : ℝ)⁻¹ * |ψ₁ (z.1 i) (n * x) - ψ₁ (z.1 i) (n * y)| := by positivity
      nlinarith [abs_nonneg c, abs_nonneg (x - y)]
    | inr j =>
      simp only [hψ_def, Sum.elim_inr]
      rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hmpos)]
      have h := lip hψ₂ (z.2 j) (m * x) (m * y)
      rw [show (m : ℝ) * x - m * y = m * (x - y) by ring, abs_mul, abs_of_pos hmpos] at h
      have h' : (m : ℝ)⁻¹ * |ψ₂ (z.2 j) (m * x) - ψ₂ (z.2 j) (m * y)| ≤ |x - y| := by
        calc (m : ℝ)⁻¹ * |ψ₂ (z.2 j) (m * x) - ψ₂ (z.2 j) (m * y)| ≤ (m : ℝ)⁻¹ * (m * |x - y|) :=
              mul_le_mul_of_nonneg_left h (inv_nonneg.2 hmpos.le)
          _ = |x - y| := by field_simp
      have h0 : 0 ≤ (m : ℝ)⁻¹ * |ψ₂ (z.2 j) (m * x) - ψ₂ (z.2 j) (m * y)| := by positivity
      nlinarith [abs_nonneg c, abs_nonneg (x - y)]
  have hrw : ∀ (σ : Fin n ⊕ Fin m → Bool) (t : T₀),
      (n : ℝ)⁻¹ * ∑ i, rsign (σ (Sum.inl i)) * G1 c ψ₁ φ t.1 (z.1 i) +
        (m : ℝ)⁻¹ * ∑ j, rsign (σ (Sum.inr j)) * G2 c ψ₂ φ t.1 (z.2 j) =
      ∑ k, rsign (σ k) * ψ k (a t k) := by
    intro σ t
    rw [Fintype.sum_sum_type, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hψ_def, ha_def, Sum.elim_inl, G1, hOne]
      rw [mul_inv_cancel_left₀ hnpos.ne']
      ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hψ_def, ha_def, Sum.elim_inr, G2, hTwo]
      rw [mul_inv_cancel_left₀ hmpos.ne']
      ring
  have hcontr := signE_iSup_contraction a ha ψ hψ
  set u : Fin n ⊕ Fin m → H :=
    Sum.elim (fun i => -((n : ℝ)⁻¹ • φ (z.1 i))) (fun j => (m : ℝ)⁻¹ • φ (z.2 j)) with hu_def
  have hlin : ∀ σ : Fin n ⊕ Fin m → Bool, (⨆ t, ∑ k, rsign (σ k) * a t k) ≤
      r * ‖∑ k, rsign (σ k) • u k‖ + ρ₁ * ((n : ℝ)⁻¹ * |∑ i, rsign (σ (Sum.inl i))|) +
        ρ₂ * ((m : ℝ)⁻¹ * |∑ j, rsign (σ (Sum.inr j))|) := by
    intro σ
    refine ciSup_le fun t => ?_
    have hp := hT₀ t.2
    have hidX : ∑ i, rsign (σ (Sum.inl i)) * a t (Sum.inl i) =
        ⟪t.1.1, ∑ i, rsign (σ (Sum.inl i)) • u (Sum.inl i)⟫_ℝ +
          t.1.2.1 * ((n : ℝ)⁻¹ * ∑ i, rsign (σ (Sum.inl i))) := by
      rw [inner_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ha_def, hu_def, Sum.elim_inl, real_inner_smul_right, inner_neg_right]
      ring
    have hidY : ∑ j, rsign (σ (Sum.inr j)) * a t (Sum.inr j) =
        ⟪t.1.1, ∑ j, rsign (σ (Sum.inr j)) • u (Sum.inr j)⟫_ℝ -
          t.1.2.2 * ((m : ℝ)⁻¹ * ∑ j, rsign (σ (Sum.inr j))) := by
      rw [inner_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [ha_def, hu_def, Sum.elim_inr, real_inner_smul_right]
      ring
    have hid : ∑ k, rsign (σ k) * a t k =
        ⟪t.1.1, ∑ k, rsign (σ k) • u k⟫_ℝ + t.1.2.1 * ((n : ℝ)⁻¹ * ∑ i, rsign (σ (Sum.inl i))) -
          t.1.2.2 * ((m : ℝ)⁻¹ * ∑ j, rsign (σ (Sum.inr j))) := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, inner_add_right, hidX, hidY]
      ring
    rw [hid]
    have h1 : ⟪t.1.1, ∑ k, rsign (σ k) • u k⟫_ℝ ≤ r * ‖∑ k, rsign (σ k) • u k‖ :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hp.1 (norm_nonneg _))
    have h2 : t.1.2.1 * ((n : ℝ)⁻¹ * ∑ i, rsign (σ (Sum.inl i))) ≤
        ρ₁ * ((n : ℝ)⁻¹ * |∑ i, rsign (σ (Sum.inl i))|) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hnpos)]
      exact mul_le_mul_of_nonneg_right hp.2.1 (by positivity)
    have h3 : -(t.1.2.2 * ((m : ℝ)⁻¹ * ∑ j, rsign (σ (Sum.inr j)))) ≤
        ρ₂ * ((m : ℝ)⁻¹ * |∑ j, rsign (σ (Sum.inr j))|) := by
      refine (neg_le_abs _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hmpos)]
      exact mul_le_mul_of_nonneg_right hp.2.2 (by positivity)
    linarith
  have hball : signE (fun σ : Fin n ⊕ Fin m → Bool => ‖∑ k, rsign (σ k) • u k‖) ≤ κ * √(sNM n m) := by
    refine (signE_norm_sum_le u).trans ?_
    have hsum : ∑ k, ‖u k‖ ^ 2 ≤ κ ^ 2 * sNM n m := by
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
      unfold sNM
      linarith
    calc √(∑ k, ‖u k‖ ^ 2) ≤ √(κ ^ 2 * sNM n m) := Real.sqrt_le_sqrt hsum
      _ = κ * √(sNM n m) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ0]
  have hX : signE (fun σ : Fin n ⊕ Fin m → Bool => |∑ i, rsign (σ (Sum.inl i))|) = n * ek n := by
    rw [signE_comp_inl (fun σ : Fin n → Bool => |∑ i, rsign (σ i)|), signE_eq_radE, mul_ek hn]
  have hY : signE (fun σ : Fin n ⊕ Fin m → Bool => |∑ j, rsign (σ (Sum.inr j))|) = m * ek m := by
    rw [signE_comp_inr (fun σ : Fin m → Bool => |∑ j, rsign (σ j)|), signE_eq_radE, mul_ek hm]
  unfold radAvg2
  simp_rw [hrw]
  calc signE (fun σ => ⨆ t : T₀, ∑ k, rsign (σ k) * ψ k (a t k))
      ≤ signE (fun σ => ⨆ t : T₀, ∑ k, rsign (σ k) * a t k) := hcontr
    _ ≤ signE (fun σ : Fin n ⊕ Fin m → Bool => r * ‖∑ k, rsign (σ k) • u k‖ +
          ρ₁ * ((n : ℝ)⁻¹ * |∑ i, rsign (σ (Sum.inl i))|) +
          ρ₂ * ((m : ℝ)⁻¹ * |∑ j, rsign (σ (Sum.inr j))|)) := signE_mono hlin
    _ = r * signE (fun σ : Fin n ⊕ Fin m → Bool => ‖∑ k, rsign (σ k) • u k‖) +
          ρ₁ * ((n : ℝ)⁻¹ * signE (fun σ : Fin n ⊕ Fin m → Bool => |∑ i, rsign (σ (Sum.inl i))|)) +
          ρ₂ * ((m : ℝ)⁻¹ * signE (fun σ : Fin n ⊕ Fin m → Bool => |∑ j, rsign (σ (Sum.inr j))|)) := by
        rw [signE_add, signE_add, signE_const_mul, signE_const_mul, signE_const_mul, signE_const_mul,
          signE_const_mul]
    _ ≤ r * κ * √(sNM n m) + ρ₁ * ek n + ρ₂ * ek m := by
        rw [hX, hY]
        have key1 : (n : ℝ)⁻¹ * (n * ek n) = ek n := by field_simp
        have key2 : (m : ℝ)⁻¹ * (m * ek m) = ek m := by field_simp
        rw [key1, key2]
        have := mul_le_mul_of_nonneg_left hball hr
        nlinarith

theorem integral_Zc_le (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [TopologicalSpace.SeparableSpace H] {ψ₁ ψ₂ : 𝒳 → ℝ → ℝ} {φ : 𝒳 → H} {κ c : ℝ} (hc : |c| ≤ 1)
    (hψ₁ : IsHingeMap ψ₁) (hψ₂ : IsHingeMap ψ₂) (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hκ0 : 0 ≤ κ) {r ρ₁ ρ₂ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) (h2 : 0 ≤ ρ₂) {n m : ℕ} (hn : n ≠ 0)
    (hm : m ≠ 0) :
    ∫ z, Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c z ∂(sampleLaw P Q n m) ≤
      2 * (r * κ * √(sNM n m) + ρ₁ * ek n + ρ₂ * ek m) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := growth hψ₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := growth hψ₂
  obtain ⟨T₀, hT₀, hcount, hdense⟩ := exists_dense (H := H) r ρ₁ ρ₂
  have hne : T₀.Nonempty := closure_nonempty_iff.1 ⟨_, hdense (zero_mem hr h1 h2)⟩
  have : Nonempty T₀ := hne.to_subtype
  have : Countable T₀ := hcount.to_subtype
  set g₁ : T₀ → 𝒳 → ℝ := fun t y => G1 c ψ₁ φ t.1 y with hg₁
  set g₂ : T₀ → 𝒳 → ℝ := fun t y => G2 c ψ₂ φ t.1 y with hg₂
  have hm₁ : ∀ t, Measurable (g₁ t) := fun t => measurable_G1 hψ₁ hφ t.1
  have hm₂ : ∀ t, Measurable (g₂ t) := fun t => measurable_G2 hψ₂ hφ t.1
  set B : ℝ := (C₁ + (ρ₁ + κ * r)) + (C₂ + (ρ₂ + κ * r)) with hB
  have hA₁ : 0 ≤ C₁ + (ρ₁ + κ * r) := by positivity
  have hA₂ : 0 ≤ C₂ + (ρ₂ + κ * r) := by positivity
  have hB₁ : ∀ t y, |g₁ t y| ≤ B := fun t y => by
    have := abs_G1_le_par hc hC₁0 hC₁ hκ hκ0 (hT₀ t.2) y; simp only [hg₁, hB]; linarith
  have hB₂ : ∀ t y, |g₂ t y| ≤ B := fun t y => by
    have := abs_G2_le_par hc hC₂0 hC₂ hκ hκ0 (hT₀ t.2) y; simp only [hg₂, hB]; linarith
  have hsym := integral_iSup_empDev2_le P Q hm₁ hm₂ hB₁ hB₂ hn hm
  have heq : ∀ z : (Fin n → 𝒳) × (Fin m → 𝒳), Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c z =
      ⨆ t : T₀, (empDev P g₁ n z.1 t + empDev Q g₂ m z.2 t) := by
    intro z
    rw [Zc_eq_iSup P Q hc hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2 T₀ hT₀ hdense z]
    rfl
  simp_rw [heq]
  refine hsym.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have hint : Integrable (radAvg2 g₁ g₂ n m)
      ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) := by
    refine Integrable.of_bound (measurable_radAvg2 hm₁ hm₂ n m).aestronglyMeasurable
      (B + B) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    refine abs_signE_le fun σ => abs_ciSup_le fun θ => (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact abs_mean_le hn fun i => by rw [abs_mul, abs_rsign, one_mul]; exact hB₁ _ _
    · exact abs_mean_le hm fun j => by rw [abs_mul, abs_rsign, one_mul]; exact hB₂ _ _
  have := integral_mono hint
    (integrable_const (r * κ * √(sNM n m) + ρ₁ * ek n + ρ₂ * ek m))
    fun z => radAvg2_hinge_le hc hψ₁ hψ₂ hκ hκ0 hr T₀ hT₀ hn hm z
  rwa [integral_const, probReal_univ, one_smul] at this

/-! ### The tail -/

section Tail

variable (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {ψ₁ ψ₂ : 𝒳 → ℝ → ℝ} {φ : 𝒳 → H} {κ c : ℝ}

theorem Zc_update_X (hc : |c| ≤ 1) (hψ₁ : IsHingeMap ψ₁) (hψ₂ : IsHingeMap ψ₂) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hκ0 : 0 ≤ κ) {r ρ₁ ρ₂ Δ₁ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) (h2 : 0 ≤ ρ₂)
    (hΔ₁ : ∀ p ∈ hingePar (H := H) r ρ₁ ρ₂, ∀ x x' : 𝒳, |hOne ψ₁ φ p.1 p.2.1 x - hOne ψ₁ φ p.1 p.2.1 x'| ≤ Δ₁)
    {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (i : Fin n) (b : 𝒳) :
    |Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c (Function.update x i b, y) - Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c (x, y)| ≤ Δ₁ / n := by
  have : Nonempty (hingePar (H := H) r ρ₁ ρ₂) := ⟨⟨_, zero_mem hr h1 h2⟩⟩
  have hnn : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  refine abs_iSup_sub_iSup_le (bdd_brc P Q hc hψ₁ hψ₂ hκ hκ0 _) (bdd_brc P Q hc hψ₁ hψ₂ hκ hκ0 _)
    fun p => ?_
  simp only [brc]
  rw [add_sub_add_right_eq_sub, empDev_update_sub, abs_mul, abs_inv, Nat.abs_cast, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ hnn
  simp only [G1]
  rw [← mul_sub, abs_mul]
  have hd := hΔ₁ p.1 p.2 b (x i)
  have h0 : 0 ≤ |hOne ψ₁ φ (↑p : H × ℝ × ℝ).1 (↑p : H × ℝ × ℝ).2.1 b -
      hOne ψ₁ φ (↑p : H × ℝ × ℝ).1 (↑p : H × ℝ × ℝ).2.1 (x i)| := abs_nonneg _
  nlinarith [abs_nonneg c]

theorem Zc_update_Y (hc : |c| ≤ 1) (hψ₁ : IsHingeMap ψ₁) (hψ₂ : IsHingeMap ψ₂) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hκ0 : 0 ≤ κ) {r ρ₁ ρ₂ Δ₂ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) (h2 : 0 ≤ ρ₂)
    (hΔ₂ : ∀ p ∈ hingePar (H := H) r ρ₁ ρ₂, ∀ y y' : 𝒳, |hTwo ψ₂ φ p.1 p.2.2 y - hTwo ψ₂ φ p.1 p.2.2 y'| ≤ Δ₂)
    {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (j : Fin m) (b : 𝒳) :
    |Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c (x, Function.update y j b) - Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c (x, y)| ≤ Δ₂ / m := by
  have : Nonempty (hingePar (H := H) r ρ₁ ρ₂) := ⟨⟨_, zero_mem hr h1 h2⟩⟩
  have hmm : (0 : ℝ) ≤ (m : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  refine abs_iSup_sub_iSup_le (bdd_brc P Q hc hψ₁ hψ₂ hκ hκ0 _) (bdd_brc P Q hc hψ₁ hψ₂ hκ hκ0 _)
    fun p => ?_
  simp only [brc]
  rw [add_sub_add_left_eq_sub, empDev_update_sub, abs_mul, abs_inv, Nat.abs_cast, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ hmm
  simp only [G2]
  rw [← mul_sub, abs_mul]
  have hd := hΔ₂ p.1 p.2 b (y j)
  have h0 : 0 ≤ |hTwo ψ₂ φ (↑p : H × ℝ × ℝ).1 (↑p : H × ℝ × ℝ).2.2 b -
      hTwo ψ₂ φ (↑p : H × ℝ × ℝ).1 (↑p : H × ℝ × ℝ).2.2 (y j)| := abs_nonneg _
  nlinarith [abs_nonneg c]

/-- The printed (non-strict) tail when `Δ₁²/n + Δ₂²/m > 0`. -/
theorem tail_Zc [TopologicalSpace.SeparableSpace H] (hc : |c| ≤ 1) (hψ₁ : IsHingeMap ψ₁)
    (hψ₂ : IsHingeMap ψ₂) (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ)
    {r ρ₁ ρ₂ Δ₁ Δ₂ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) (h2 : 0 ≤ ρ₂) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hΔ₁ : ∀ p ∈ hingePar (H := H) r ρ₁ ρ₂, ∀ x x' : 𝒳, |hOne ψ₁ φ p.1 p.2.1 x - hOne ψ₁ φ p.1 p.2.1 x'| ≤ Δ₁)
    (hΔ₂ : ∀ p ∈ hingePar (H := H) r ρ₁ ρ₂, ∀ y y' : 𝒳, |hTwo ψ₂ φ p.1 p.2.2 y - hTwo ψ₂ φ p.1 p.2.2 y'| ≤ Δ₂)
    (hV : 0 < Δ₁ ^ 2 / n + Δ₂ ^ 2 / m) {χ : ℝ} (hχ : 0 < χ) :
    TailAtLeast (sampleLaw P Q n m) (fun z => Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c z)
      (√(χ * (Δ₁ ^ 2 / n + Δ₂ ^ 2 / m) / 2)) χ := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have hΔ₁0 : 0 ≤ Δ₁ := (abs_nonneg _).trans (hΔ₁ _ (zero_mem hr h1 h2) x₀ x₀)
  have hΔ₂0 : 0 ≤ Δ₂ := (abs_nonneg _).trans (hΔ₂ _ (zero_mem hr h1 h2) x₀ x₀)
  set F : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun z => Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c z with hF
  have hFm : Measurable F := measurable_Zc P Q hc hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2
  set V : ℝ := Δ₁ ^ 2 / n + Δ₂ ^ 2 / m with hVdef
  set ε : ℝ := √(χ * V / 2) with hε
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  have hmcd := StatFormal.Wave30tp.mcdiarmid_two_sample P Q F hFm (cX := Δ₁ / n) (cY := Δ₂ / m)
    (by positivity) (by positivity)
    (fun x y i b => Zc_update_X P Q hc hψ₁ hψ₂ hκ hκ0 hr h1 h2 hΔ₁ x y i b)
    (fun x y j b => Zc_update_Y P Q hc hψ₁ hψ₂ hκ hκ0 hr h1 h2 hΔ₂ x y j b) hε0
  have hexp : -ε ^ 2 / (2 * ((n * (Δ₁ / n) ^ 2 + m * (Δ₂ / m) ^ 2) / 4)) = -χ := by
    have e1 : ((n : ℝ) * (Δ₁ / n) ^ 2 + m * (Δ₂ / m) ^ 2) / 4 = V / 4 := by
      rw [hVdef]; field_simp
    rw [e1, hε, Real.sq_sqrt (by positivity)]
    field_simp
    norm_num
  rw [hexp] at hmcd
  unfold TailAtLeast
  have hset : {z | (∫ w, F w ∂(sampleLaw P Q n m)) + ε ≤ F z} =
      {z | ε ≤ F z - ∫ w, F w ∂(sampleLaw P Q n m)} := by
    ext z; simp only [mem_ofPred_eq]; constructor <;> intro h <;> linarith
  change sampleLaw P Q n m {z | (∫ w, F w ∂(sampleLaw P Q n m)) + ε ≤ F z} ≤ _
  rw [hset, ← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hmcd

/-- When `Δ₁²/n + Δ₂²/m = 0`, every `h` is constant in the point and `Zc ≡ 0`. -/
theorem Zc_eq_zero (_hc : |c| ≤ 1) (_hψ₁ : IsHingeMap ψ₁) (_hψ₂ : IsHingeMap ψ₂) (_hκ : ∀ x, ‖φ x‖ ≤ κ)
    (_hκ0 : 0 ≤ κ) {r ρ₁ ρ₂ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) (h2 : 0 ≤ ρ₂) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (hΔ₁ : ∀ p ∈ hingePar (H := H) r ρ₁ ρ₂, ∀ x x' : 𝒳, |hOne ψ₁ φ p.1 p.2.1 x - hOne ψ₁ φ p.1 p.2.1 x'| ≤ 0)
    (hΔ₂ : ∀ p ∈ hingePar (H := H) r ρ₁ ρ₂, ∀ y y' : 𝒳, |hTwo ψ₂ φ p.1 p.2.2 y - hTwo ψ₂ φ p.1 p.2.2 y'| ≤ 0)
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) : Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c z = 0 := by
  have : Nonempty (hingePar (H := H) r ρ₁ ρ₂) := ⟨⟨_, zero_mem hr h1 h2⟩⟩
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have hzero : ∀ p : hingePar (H := H) r ρ₁ ρ₂, brc P Q φ ψ₁ ψ₂ c z p.1 = 0 := by
    intro p
    have hk1 := const_of_osc (hΔ₁ p.1 p.2) x₀
    have hk2 := const_of_osc (hΔ₂ p.1 p.2) x₀
    unfold brc
    rw [empDev_const P (g := G1 c ψ₁ φ) (t := p.1) (K := c * hOne ψ₁ φ p.1.1 p.1.2.1 x₀)
        (fun y => by simp only [G1, hk1 y]) hn z.1,
      empDev_const Q (g := G2 c ψ₂ φ) (t := p.1) (K := c * hTwo ψ₂ φ p.1.1 p.1.2.2 x₀)
        (fun y => by simp only [G2, hk2 y]) hm z.2, add_zero]
  unfold Zc
  simp only [hzero, ciSup_const]

/-- The strict tail, with no condition on `Δ₁, Δ₂` beyond the oscillation bounds. -/
theorem tail_strict_Zc [TopologicalSpace.SeparableSpace H] (hc : |c| ≤ 1) (hψ₁ : IsHingeMap ψ₁)
    (hψ₂ : IsHingeMap ψ₂) (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ)
    {r ρ₁ ρ₂ Δ₁ Δ₂ : ℝ} (hr : 0 ≤ r) (h1 : 0 ≤ ρ₁) (h2 : 0 ≤ ρ₂) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hΔ₁ : ∀ p ∈ hingePar (H := H) r ρ₁ ρ₂, ∀ x x' : 𝒳, |hOne ψ₁ φ p.1 p.2.1 x - hOne ψ₁ φ p.1 p.2.1 x'| ≤ Δ₁)
    (hΔ₂ : ∀ p ∈ hingePar (H := H) r ρ₁ ρ₂, ∀ y y' : 𝒳, |hTwo ψ₂ φ p.1 p.2.2 y - hTwo ψ₂ φ p.1 p.2.2 y'| ≤ Δ₂)
    {χ : ℝ} (hχ : 0 < χ) :
    TailMoreThan (sampleLaw P Q n m) (fun z => Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c z)
      (√(χ * (Δ₁ ^ 2 / n + Δ₂ ^ 2 / m) / 2)) χ := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have hΔ₁0 : 0 ≤ Δ₁ := (abs_nonneg _).trans (hΔ₁ _ (zero_mem hr h1 h2) x₀ x₀)
  have hΔ₂0 : 0 ≤ Δ₂ := (abs_nonneg _).trans (hΔ₂ _ (zero_mem hr h1 h2) x₀ x₀)
  have hA0 : 0 ≤ Δ₁ ^ 2 / n := by positivity
  have hB0 : 0 ≤ Δ₂ ^ 2 / m := by positivity
  rcases (add_nonneg hA0 hB0).lt_or_eq with hV | hV
  · have h := tail_Zc P Q hc hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2 hn hm hΔ₁ hΔ₂ hV hχ
    unfold TailAtLeast at h
    unfold TailMoreThan
    refine le_trans (measure_mono fun z hz => ?_) h
    simp only [mem_ofPred_eq] at hz ⊢
    exact hz.le
  · have hA : Δ₁ ^ 2 / n = 0 := by linarith
    have hB : Δ₂ ^ 2 / m = 0 := by linarith
    have hd1 : Δ₁ = 0 := by
      rcases div_eq_zero_iff.1 hA with h | h
      · exact pow_eq_zero_iff two_ne_zero |>.1 h
      · exact absurd h hnpos.ne'
    have hd2 : Δ₂ = 0 := by
      rcases div_eq_zero_iff.1 hB with h | h
      · exact pow_eq_zero_iff two_ne_zero |>.1 h
      · exact absurd h hmpos.ne'
    have hZ0 : ∀ z : (Fin n → 𝒳) × (Fin m → 𝒳), Zc P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ c z = 0 := fun z =>
      Zc_eq_zero P Q hc hψ₁ hψ₂ hκ hκ0 hr h1 h2 (by omega) (by omega)
        (fun p hp x x' => hd1 ▸ hΔ₁ p hp x x') (fun p hp y y' => hd2 ▸ hΔ₂ p hp y y') z
    unfold TailMoreThan
    simp only [hZ0, integral_zero, zero_add]
    refine le_trans (measure_mono (t := ∅) fun ω hω => ?_) (by rw [measure_empty]; exact zero_le)
    simp only [mem_ofPred_eq] at hω
    exact absurd hω (not_lt.2 (Real.sqrt_nonneg _))

end Tail

end StatFormal.Wave30ty.RTwo
