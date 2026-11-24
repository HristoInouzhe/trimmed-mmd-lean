import StatFormal.Wave30tx.Statements
import StatFormal.Wave30tr.RouteEvents

/-!
# Route: `lem:localmod (v2)` (untrusted proof material)

The class `𝓗(r)` is parametrised by `p = (f, t, u) ∈ rampPar` and `h₁ = G1 p`, `h₂ = G2 p`.
* Pointwise Lipschitz bounds `|G1 p − G1 p'| ≤ |t − t'| + κ‖f − f'‖` (and for `G2`), hence `|h₁| ≤ 2κr + λ₁`,
  `|h₂| ≤ 2κr + λ₂` on the class, and `p ↦ rampDev z p` is Lipschitz, so the supremum is attained on a countable dense
  subset (`H × ℝ × ℝ` separable): measurability.
* Expectation: `rampDev = (P_n − P)(−h₁) + (Q_m − Q)(−h₂)`, two-sample symmetrisation (`integral_iSup_empDev2_le`),
  coordinatewise contraction (`signE_iSup_contraction`) with the sample-dependent 1-Lipschitz maps
  `w ↦ −n⁻¹[(c_i + nw)₊ − (c_i)₊]`, then the linear bound `r‖S_σ‖ + (κr+λ₁)|σ̄_X| + (κr+λ₂)|σ̄_Y|`.
* Tail: two-sample McDiarmid (`Wave30tp.mcdiarmid_two_sample`) with differences `2(2κr+λ₁)/n`, `2(2κr+λ₂)/m`, and
  Minkowski's inequality in `ℝ²`.
-/

noncomputable section
open MeasureTheory Set Finset
open scoped InnerProductSpace

namespace StatFormal.Wave30tx.RLocal

open StatFormal.Wave30tx StatFormal.Concentration StatFormal.Wave12c StatFormal.Wave30tp StatFormal.Wave30tr

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `h₁ = (t − f)₊ − (t* − f*)₊` at `p = (f, t, u)`. -/
def G1 (φ : 𝒳 → H) (fstar : H) (tstar : ℝ) (p : H × ℝ × ℝ) (x : 𝒳) : ℝ :=
  max (p.2.1 - witFn p.1 φ x) 0 - max (tstar - witFn fstar φ x) 0

/-- `h₂ = (f − u)₊ − (f* − u*)₊` at `p = (f, t, u)`. -/
def G2 (φ : 𝒳 → H) (fstar : H) (ustar : ℝ) (p : H × ℝ × ℝ) (y : 𝒳) : ℝ :=
  max (witFn p.1 φ y - p.2.2) 0 - max (witFn fstar φ y - ustar) 0

theorem rampDev_eq (P Q : Measure 𝒳) (φ : 𝒳 → H) (fstar : H) (tstar ustar : ℝ) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) (p : H × ℝ × ℝ) :
    rampDev P Q φ fstar tstar ustar z p =
      popDev P z.1 (G1 φ fstar tstar p) + popDev Q z.2 (G2 φ fstar ustar p) := rfl

omit [MeasurableSpace 𝒳] [InnerProductSpace ℝ H] in
theorem norm_fst_le_dist (p p' : H × ℝ × ℝ) : ‖p.1 - p'.1‖ ≤ dist p p' := by
  rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_left _ _

omit [MeasurableSpace 𝒳] [InnerProductSpace ℝ H] in
theorem abs_snd_fst_le_dist (p p' : H × ℝ × ℝ) : |p.2.1 - p'.2.1| ≤ dist p p' := by
  rw [← Real.dist_eq, Prod.dist_eq, Prod.dist_eq]
  exact (le_max_left _ _).trans (le_max_right _ _)

omit [MeasurableSpace 𝒳] [InnerProductSpace ℝ H] in
theorem abs_snd_snd_le_dist (p p' : H × ℝ × ℝ) : |p.2.2 - p'.2.2| ≤ dist p p' := by
  rw [← Real.dist_eq, Prod.dist_eq, Prod.dist_eq]
  exact (le_max_right _ _).trans (le_max_right _ _)

omit [MeasurableSpace 𝒳] in
theorem abs_inner_phi_le {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (v : H) (x : 𝒳) :
    |⟪v, φ x⟫_ℝ| ≤ κ * ‖v‖ :=
  (abs_real_inner_le_norm _ _).trans (by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hκ x) (norm_nonneg _))

omit [MeasurableSpace 𝒳] in
theorem abs_G1_sub_le {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (fstar : H) (tstar : ℝ)
    (p p' : H × ℝ × ℝ) (x : 𝒳) :
    |G1 φ fstar tstar p x - G1 φ fstar tstar p' x| ≤ |p.2.1 - p'.2.1| + κ * ‖p.1 - p'.1‖ := by
  have e : G1 φ fstar tstar p x - G1 φ fstar tstar p' x =
      max (p.2.1 - witFn p.1 φ x) 0 - max (p'.2.1 - witFn p'.1 φ x) 0 := by unfold G1; ring
  rw [e]
  refine (abs_max_sub_max_le_abs _ _ 0).trans ?_
  have e2 : p.2.1 - witFn p.1 φ x - (p'.2.1 - witFn p'.1 φ x) = (p.2.1 - p'.2.1) - ⟪p.1 - p'.1, φ x⟫_ℝ := by
    simp only [witFn, inner_sub_left]; ring
  rw [e2]
  refine (abs_sub _ _).trans ?_
  linarith [abs_inner_phi_le hκ (p.1 - p'.1) x]

omit [MeasurableSpace 𝒳] in
theorem abs_G2_sub_le {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (fstar : H) (ustar : ℝ)
    (p p' : H × ℝ × ℝ) (y : 𝒳) :
    |G2 φ fstar ustar p y - G2 φ fstar ustar p' y| ≤ |p.2.2 - p'.2.2| + κ * ‖p.1 - p'.1‖ := by
  have e : G2 φ fstar ustar p y - G2 φ fstar ustar p' y =
      max (witFn p.1 φ y - p.2.2) 0 - max (witFn p'.1 φ y - p'.2.2) 0 := by unfold G2; ring
  rw [e]
  refine (abs_max_sub_max_le_abs _ _ 0).trans ?_
  have e2 : witFn p.1 φ y - p.2.2 - (witFn p'.1 φ y - p'.2.2) = ⟪p.1 - p'.1, φ y⟫_ℝ - (p.2.2 - p'.2.2) := by
    simp only [witFn, inner_sub_left]; ring
  rw [e2]
  refine (abs_sub _ _).trans ?_
  linarith [abs_inner_phi_le hκ (p.1 - p'.1) y]

omit [MeasurableSpace 𝒳] in
theorem G1_star (φ : 𝒳 → H) (fstar : H) (tstar ustar : ℝ) (x : 𝒳) :
    G1 φ fstar tstar (fstar, tstar, ustar) x = 0 := by unfold G1; simp

omit [MeasurableSpace 𝒳] in
theorem G2_star (φ : 𝒳 → H) (fstar : H) (tstar ustar : ℝ) (y : 𝒳) :
    G2 φ fstar ustar (fstar, tstar, ustar) y = 0 := by unfold G2; simp

theorem measurable_G1 {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) (fstar : H) (tstar : ℝ) (p : H × ℝ × ℝ) :
    Measurable (G1 φ fstar tstar p) := by
  have h1 : Measurable (witFn p.1 φ) := (stronglyMeasurable_const.inner hφ).measurable
  have h2 : Measurable (witFn fstar φ) := (stronglyMeasurable_const.inner hφ).measurable
  exact ((measurable_const.sub h1).max measurable_const).sub ((measurable_const.sub h2).max measurable_const)

theorem measurable_G2 {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) (fstar : H) (ustar : ℝ) (p : H × ℝ × ℝ) :
    Measurable (G2 φ fstar ustar p) := by
  have h1 : Measurable (witFn p.1 φ) := (stronglyMeasurable_const.inner hφ).measurable
  have h2 : Measurable (witFn fstar φ) := (stronglyMeasurable_const.inner hφ).measurable
  exact ((h1.sub measurable_const).max measurable_const).sub ((h2.sub measurable_const).max measurable_const)

/-! ### `popDev` -/

theorem popDev_eq_neg_empDev (P : Measure 𝒳) {n : ℕ} (x : Fin n → 𝒳) (h : 𝒳 → ℝ) :
    popDev P x h = empDev P (fun (_ : Unit) y => -h y) n x () := by
  unfold popDev empDev
  rw [integral_neg]
  simp only [Finset.sum_neg_distrib]
  ring

theorem popDev_sub (P : Measure 𝒳) {n : ℕ} (x : Fin n → 𝒳) {h h' : 𝒳 → ℝ} (hh : Integrable h P)
    (hh' : Integrable h' P) : popDev P x h - popDev P x h' = popDev P x (fun y => h y - h' y) := by
  unfold popDev
  rw [integral_sub hh hh', Finset.sum_sub_distrib]
  ring

theorem abs_popDev_le (P : Measure 𝒳) [IsProbabilityMeasure P] {n : ℕ} (hn : n ≠ 0) (x : Fin n → 𝒳)
    {h : 𝒳 → ℝ} {L : ℝ} (hL : ∀ y, |h y| ≤ L) : |popDev P x h| ≤ 2 * L := by
  unfold popDev
  have h1 : |∫ y, h y ∂P| ≤ L := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := h) (C := L)
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hL y)
    simpa [Real.norm_eq_abs] using this
  have h2 := abs_mean_le hn (c := fun i => h (x i)) (fun i => hL (x i))
  refine (abs_sub _ _).trans ?_
  linarith

theorem measurable_popDev (P : Measure 𝒳) {n : ℕ} {h : 𝒳 → ℝ} (hh : Measurable h) :
    Measurable fun x : Fin n → 𝒳 => popDev P x h :=
  measurable_const.sub ((Finset.measurable_fun_sum _ fun i _ => hh.comp (measurable_pi_apply i)).const_mul _)

theorem popDev_update_sub (P : Measure 𝒳) {n : ℕ} (x : Fin n → 𝒳) (i : Fin n) (b : 𝒳) (h : 𝒳 → ℝ) :
    popDev P (Function.update x i b) h - popDev P x h = -((n : ℝ)⁻¹ * (h b - h (x i))) := by
  rw [popDev_eq_neg_empDev, popDev_eq_neg_empDev]
  rw [empDev_update_sub]
  ring

/-! ### The class: bounds, Lipschitz continuity, the dense subclass -/

omit [InnerProductSpace ℝ H] in
theorem kappa_nonneg (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) : 0 ≤ κ := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  exact (norm_nonneg _).trans (hκ x₀)

omit [MeasurableSpace 𝒳] [InnerProductSpace ℝ H] in
theorem star_mem (fstar : H) (tstar ustar : ℝ) {κ r l1 l2 : ℝ} (hκ0 : 0 ≤ κ) (hr : 0 ≤ r) (hl1 : 0 ≤ l1)
    (hl2 : 0 ≤ l2) : (fstar, tstar, ustar) ∈ rampPar fstar tstar ustar κ r l1 l2 := by
  refine ⟨by simpa using hr, by simp; positivity, by simp; positivity⟩

omit [MeasurableSpace 𝒳] in
theorem abs_G1_le {φ : 𝒳 → H} {κ : ℝ} (fstar : H) (tstar ustar : ℝ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ)
    {r l1 l2 : ℝ} {p : H × ℝ × ℝ} (hp : p ∈ rampPar fstar tstar ustar κ r l1 l2) (x : 𝒳) :
    |G1 φ fstar tstar p x| ≤ 2 * κ * r + l1 := by
  have h := abs_G1_sub_le hκ fstar tstar p (fstar, tstar, ustar) x
  rw [G1_star, sub_zero] at h
  have h1 : κ * ‖p.1 - fstar‖ ≤ κ * r := mul_le_mul_of_nonneg_left hp.1 hκ0
  have h2 := hp.2.1
  simp only at h
  linarith

omit [MeasurableSpace 𝒳] in
theorem abs_G2_le {φ : 𝒳 → H} {κ : ℝ} (fstar : H) (tstar ustar : ℝ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ)
    {r l1 l2 : ℝ} {p : H × ℝ × ℝ} (hp : p ∈ rampPar fstar tstar ustar κ r l1 l2) (y : 𝒳) :
    |G2 φ fstar ustar p y| ≤ 2 * κ * r + l2 := by
  have h := abs_G2_sub_le hκ fstar ustar p (fstar, tstar, ustar) y
  rw [G2_star, sub_zero] at h
  have h1 : κ * ‖p.1 - fstar‖ ≤ κ * r := mul_le_mul_of_nonneg_left hp.1 hκ0
  have h2 := hp.2.2
  simp only at h
  linarith

theorem integrable_G1 (P : Measure 𝒳) [IsFiniteMeasure P] {φ : 𝒳 → H} {κ : ℝ} (fstar : H) (tstar ustar : ℝ)
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (p : H × ℝ × ℝ) : Integrable (G1 φ fstar tstar p) P := by
  refine Integrable.of_bound (measurable_G1 hφ fstar tstar p).aestronglyMeasurable
    (|p.2.1 - tstar| + κ * ‖p.1 - fstar‖) (ae_of_all _ fun x => ?_)
  have h := abs_G1_sub_le hκ fstar tstar p (fstar, tstar, ustar) x
  rw [G1_star, sub_zero] at h
  rw [Real.norm_eq_abs]; exact h

theorem integrable_G2 (Q : Measure 𝒳) [IsFiniteMeasure Q] {φ : 𝒳 → H} {κ : ℝ} (fstar : H) (tstar ustar : ℝ)
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (p : H × ℝ × ℝ) : Integrable (G2 φ fstar ustar p) Q := by
  refine Integrable.of_bound (measurable_G2 hφ fstar ustar p).aestronglyMeasurable
    (|p.2.2 - ustar| + κ * ‖p.1 - fstar‖) (ae_of_all _ fun y => ?_)
  have h := abs_G2_sub_le hκ fstar ustar p (fstar, tstar, ustar) y
  rw [G2_star, sub_zero] at h
  rw [Real.norm_eq_abs]; exact h

section Class

variable (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ : ℝ}
  (fstar : H) (tstar ustar : ℝ)

theorem abs_rampDev_le (hκ : ∀ x, ‖φ x‖ ≤ κ) {r l1 l2 : ℝ} {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) {p : H × ℝ × ℝ} (hp : p ∈ rampPar fstar tstar ustar κ r l1 l2) :
    |rampDev P Q φ fstar tstar ustar z p| ≤ 2 * (2 * κ * r + l1) + 2 * (2 * κ * r + l2) := by
  have hκ0 := kappa_nonneg P hκ
  rw [rampDev_eq]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact abs_popDev_le P hn z.1 (abs_G1_le fstar tstar ustar hκ hκ0 hp)
  · exact abs_popDev_le Q hm z.2 (abs_G2_le fstar tstar ustar hκ hκ0 hp)

theorem rampDev_lip (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) (p p' : H × ℝ × ℝ) :
    dist (rampDev P Q φ fstar tstar ustar z p) (rampDev P Q φ fstar tstar ustar z p') ≤
      (4 * (1 + κ)) * dist p p' := by
  have hκ0 := kappa_nonneg P hκ
  rw [Real.dist_eq, rampDev_eq, rampDev_eq]
  have e : popDev P z.1 (G1 φ fstar tstar p) + popDev Q z.2 (G2 φ fstar ustar p) -
      (popDev P z.1 (G1 φ fstar tstar p') + popDev Q z.2 (G2 φ fstar ustar p')) =
      popDev P z.1 (fun y => G1 φ fstar tstar p y - G1 φ fstar tstar p' y) +
        popDev Q z.2 (fun y => G2 φ fstar ustar p y - G2 φ fstar ustar p' y) := by
    rw [← popDev_sub P z.1 (integrable_G1 P fstar tstar ustar hφ hκ p)
        (integrable_G1 P fstar tstar ustar hφ hκ p'),
      ← popDev_sub Q z.2 (integrable_G2 Q fstar tstar ustar hφ hκ p)
        (integrable_G2 Q fstar tstar ustar hφ hκ p')]
    ring
  rw [e]
  have hd1 := norm_fst_le_dist p p'
  have hd2 := abs_snd_fst_le_dist p p'
  have hd3 := abs_snd_snd_le_dist p p'
  have hb1 : ∀ y, |G1 φ fstar tstar p y - G1 φ fstar tstar p' y| ≤ (1 + κ) * dist p p' := fun y => by
    have := abs_G1_sub_le hκ fstar tstar p p' y
    have : κ * ‖p.1 - p'.1‖ ≤ κ * dist p p' := mul_le_mul_of_nonneg_left hd1 hκ0
    nlinarith
  have hb2 : ∀ y, |G2 φ fstar ustar p y - G2 φ fstar ustar p' y| ≤ (1 + κ) * dist p p' := fun y => by
    have := abs_G2_sub_le hκ fstar ustar p p' y
    have : κ * ‖p.1 - p'.1‖ ≤ κ * dist p p' := mul_le_mul_of_nonneg_left hd1 hκ0
    nlinarith
  refine (abs_add_le _ _).trans ?_
  have h1 := abs_popDev_le P hn z.1 hb1
  have h2 := abs_popDev_le Q hm z.2 hb2
  linarith

theorem continuous_rampDev (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {n m : ℕ} (hn : n ≠ 0)
    (hm : m ≠ 0) (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    Continuous fun p : H × ℝ × ℝ => rampDev P Q φ fstar tstar ustar z p :=
  (LipschitzWith.of_dist_le' fun p p' => rampDev_lip P Q fstar tstar ustar hφ hκ hn hm z p p').continuous

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
theorem measurable_rampDev (hφ : StronglyMeasurable φ) {n m : ℕ} (p : H × ℝ × ℝ) :
    Measurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => rampDev P Q φ fstar tstar ustar z p :=
  ((measurable_popDev P (measurable_G1 hφ fstar tstar p)).comp measurable_fst).add
    ((measurable_popDev Q (measurable_G2 hφ fstar ustar p)).comp measurable_snd)

theorem bdd_rampDev (hκ : ∀ x, ‖φ x‖ ≤ κ) {r l1 l2 : ℝ} {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    BddAbove (Set.range fun p : rampPar fstar tstar ustar κ r l1 l2 => rampDev P Q φ fstar tstar ustar z p.1) :=
  bddAbove_of_abs_le fun p => abs_rampDev_le P Q fstar tstar ustar hκ hn hm z p.2

/-- The supremum over the class equals the supremum over a dense subclass. -/
theorem Zloc_eq_iSup (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {r l1 l2 : ℝ} (hr : 0 ≤ r)
    (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (T₀ : Set (H × ℝ × ℝ)) [Nonempty T₀]
    (hT₀ : T₀ ⊆ rampPar fstar tstar ustar κ r l1 l2) (hdense : rampPar fstar tstar ustar κ r l1 l2 ⊆ closure T₀)
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    Zloc P Q φ fstar tstar ustar κ r l1 l2 z = ⨆ t : T₀, rampDev P Q φ fstar tstar ustar z t.1 := by
  have hκ0 := kappa_nonneg P hκ
  have : Nonempty (rampPar fstar tstar ustar κ r l1 l2) :=
    ⟨⟨_, star_mem fstar tstar ustar hκ0 hr hl1 hl2⟩⟩
  have hb0 : BddAbove (Set.range fun t : T₀ => rampDev P Q φ fstar tstar ustar z t.1) :=
    bddAbove_of_abs_le fun t => abs_rampDev_le P Q fstar tstar ustar hκ hn hm z (hT₀ t.2)
  unfold Zloc
  refine le_antisymm (ciSup_le fun p => ?_) (ciSup_le fun t => ?_)
  · have hcl : closure T₀ ⊆ {q | rampDev P Q φ fstar tstar ustar z q ≤
        ⨆ t : T₀, rampDev P Q φ fstar tstar ustar z t.1} :=
      closure_minimal (fun q hq => le_ciSup hb0 ⟨q, hq⟩)
        (isClosed_le (continuous_rampDev P Q fstar tstar ustar hφ hκ hn hm z) continuous_const)
    exact hcl (hdense p.2)
  · exact le_ciSup (bdd_rampDev P Q fstar tstar ustar hκ hn hm z) ⟨t.1, hT₀ t.2⟩

end Class

/-! ### The expectation -/

omit [MeasurableSpace 𝒳] in
/-- Pointwise Rademacher bound after contraction: `E_σ sup_{T₀} [n⁻¹∑σ_i(−h₁)(x_i) + m⁻¹∑σ'_j(−h₂)(y_j)]
≤ κr√s + (κr+λ₁)e_n + (κr+λ₂)e_m`. -/
theorem radAvg2_ramp_le {φ : 𝒳 → H} {κ : ℝ} (fstar : H) (tstar ustar : ℝ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hκ0 : 0 ≤ κ) {r l1 l2 : ℝ} (hr : 0 ≤ r) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2) (T₀ : Set (H × ℝ × ℝ))
    [Nonempty T₀] (hT₀ : T₀ ⊆ rampPar fstar tstar ustar κ r l1 l2) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    radAvg2 (fun (t : T₀) y => -G1 φ fstar tstar t.1 y) (fun (t : T₀) y => -G2 φ fstar ustar t.1 y) n m z ≤
      κ * r * √(sNM n m) + (κ * r + l1) * ek n + (κ * r + l2) * ek m := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
  have hninv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)
  have hminv : (m : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm)
  set c : Fin n → ℝ := fun i => tstar - witFn fstar φ (z.1 i) with hc
  set d : Fin m → ℝ := fun j => witFn fstar φ (z.2 j) - ustar with hd
  set a : T₀ → Fin n ⊕ Fin m → ℝ := fun t k =>
    Sum.elim (fun i => (n : ℝ)⁻¹ * ((t.1.2.1 - tstar) - ⟪t.1.1 - fstar, φ (z.1 i)⟫_ℝ))
      (fun j => (m : ℝ)⁻¹ * (⟪t.1.1 - fstar, φ (z.2 j)⟫_ℝ - (t.1.2.2 - ustar))) k with ha_def
  set ψ : Fin n ⊕ Fin m → ℝ → ℝ := fun k w =>
    Sum.elim (fun i => -((n : ℝ)⁻¹ * (max (c i + n * w) 0 - max (c i) 0)))
      (fun j => -((m : ℝ)⁻¹ * (max (d j + m * w) 0 - max (d j) 0))) k with hψ_def
  set B : ℝ := 2 * κ * r + l1 + l2 with hB
  have ha : ∀ t k, |a t k| ≤ B := by
    intro t k
    have hp := hT₀ t.2
    have hv : ∀ x, |⟪t.1.1 - fstar, φ x⟫_ℝ| ≤ κ * r := fun x =>
      (abs_inner_phi_le hκ _ x).trans (mul_le_mul_of_nonneg_left hp.1 hκ0)
    cases k with
    | inl i =>
      simp only [ha_def, Sum.elim_inl]
      rw [abs_mul, abs_of_pos (inv_pos.2 hnpos)]
      have h1 : |(t.1.2.1 - tstar) - ⟪t.1.1 - fstar, φ (z.1 i)⟫_ℝ| ≤ B := by
        refine (abs_sub _ _).trans ?_
        have := hp.2.1; have := hv (z.1 i); rw [hB]; nlinarith
      calc (n : ℝ)⁻¹ * |(t.1.2.1 - tstar) - ⟪t.1.1 - fstar, φ (z.1 i)⟫_ℝ| ≤ 1 * B :=
            mul_le_mul hninv h1 (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    | inr j =>
      simp only [ha_def, Sum.elim_inr]
      rw [abs_mul, abs_of_pos (inv_pos.2 hmpos)]
      have h1 : |⟪t.1.1 - fstar, φ (z.2 j)⟫_ℝ - (t.1.2.2 - ustar)| ≤ B := by
        refine (abs_sub _ _).trans ?_
        have := hp.2.2; have := hv (z.2 j); rw [hB]; nlinarith
      calc (m : ℝ)⁻¹ * |⟪t.1.1 - fstar, φ (z.2 j)⟫_ℝ - (t.1.2.2 - ustar)| ≤ 1 * B :=
            mul_le_mul hminv h1 (abs_nonneg _) zero_le_one
        _ = B := one_mul B
  have hψ : ∀ k x y, |ψ k x - ψ k y| ≤ |x - y| := by
    intro k x y
    cases k with
    | inl i =>
      simp only [hψ_def, Sum.elim_inl]
      rw [show -((n : ℝ)⁻¹ * (max (c i + n * x) 0 - max (c i) 0)) - -((n : ℝ)⁻¹ * (max (c i + n * y) 0 - max (c i) 0))
          = -((n : ℝ)⁻¹ * (max (c i + n * x) 0 - max (c i + n * y) 0)) by ring, abs_neg, abs_mul,
        abs_of_pos (inv_pos.2 hnpos)]
      have h := abs_max_sub_max_le_abs (c i + n * x) (c i + n * y) 0
      rw [show c i + n * x - (c i + n * y) = n * (x - y) by ring, abs_mul, abs_of_pos hnpos] at h
      calc (n : ℝ)⁻¹ * |max (c i + n * x) 0 - max (c i + n * y) 0| ≤ (n : ℝ)⁻¹ * (n * |x - y|) :=
            mul_le_mul_of_nonneg_left h (inv_nonneg.2 hnpos.le)
        _ = |x - y| := by field_simp
    | inr j =>
      simp only [hψ_def, Sum.elim_inr]
      rw [show -((m : ℝ)⁻¹ * (max (d j + m * x) 0 - max (d j) 0)) - -((m : ℝ)⁻¹ * (max (d j + m * y) 0 - max (d j) 0))
          = -((m : ℝ)⁻¹ * (max (d j + m * x) 0 - max (d j + m * y) 0)) by ring, abs_neg, abs_mul,
        abs_of_pos (inv_pos.2 hmpos)]
      have h := abs_max_sub_max_le_abs (d j + m * x) (d j + m * y) 0
      rw [show d j + m * x - (d j + m * y) = m * (x - y) by ring, abs_mul, abs_of_pos hmpos] at h
      calc (m : ℝ)⁻¹ * |max (d j + m * x) 0 - max (d j + m * y) 0| ≤ (m : ℝ)⁻¹ * (m * |x - y|) :=
            mul_le_mul_of_nonneg_left h (inv_nonneg.2 hmpos.le)
        _ = |x - y| := by field_simp
  have hrw : ∀ (σ : Fin n ⊕ Fin m → Bool) (t : T₀),
      (n : ℝ)⁻¹ * ∑ i, rsign (σ (Sum.inl i)) * -G1 φ fstar tstar t.1 (z.1 i) +
        (m : ℝ)⁻¹ * ∑ j, rsign (σ (Sum.inr j)) * -G2 φ fstar ustar t.1 (z.2 j) =
      ∑ k, rsign (σ k) * ψ k (a t k) := by
    intro σ t
    rw [Fintype.sum_sum_type, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hψ_def, ha_def, Sum.elim_inl]
      have key : c i + (n : ℝ) * ((n : ℝ)⁻¹ * ((t.1.2.1 - tstar) - ⟪t.1.1 - fstar, φ (z.1 i)⟫_ℝ)) =
          t.1.2.1 - witFn t.1.1 φ (z.1 i) := by
        rw [← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul]
        simp only [hc, witFn, inner_sub_left]; ring
      rw [key]
      simp only [hc, G1]
      ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hψ_def, ha_def, Sum.elim_inr]
      have key : d j + (m : ℝ) * ((m : ℝ)⁻¹ * (⟪t.1.1 - fstar, φ (z.2 j)⟫_ℝ - (t.1.2.2 - ustar))) =
          witFn t.1.1 φ (z.2 j) - t.1.2.2 := by
        rw [← mul_assoc, mul_inv_cancel₀ hmpos.ne', one_mul]
        simp only [hd, witFn, inner_sub_left]; ring
      rw [key]
      simp only [hd, G2]
      ring
  have hcontr := signE_iSup_contraction a ha ψ hψ
  set u : Fin n ⊕ Fin m → H :=
    Sum.elim (fun i => -((n : ℝ)⁻¹ • φ (z.1 i))) (fun j => (m : ℝ)⁻¹ • φ (z.2 j)) with hu_def
  have hlin : ∀ σ : Fin n ⊕ Fin m → Bool, (⨆ t, ∑ k, rsign (σ k) * a t k) ≤
      r * ‖∑ k, rsign (σ k) • u k‖ + (κ * r + l1) * ((n : ℝ)⁻¹ * |∑ i, rsign (σ (Sum.inl i))|) +
        (κ * r + l2) * ((m : ℝ)⁻¹ * |∑ j, rsign (σ (Sum.inr j))|) := by
    intro σ
    refine ciSup_le fun t => ?_
    have hp := hT₀ t.2
    have hidX : ∑ i, rsign (σ (Sum.inl i)) * a t (Sum.inl i) =
        ⟪t.1.1 - fstar, ∑ i, rsign (σ (Sum.inl i)) • u (Sum.inl i)⟫_ℝ +
          (t.1.2.1 - tstar) * ((n : ℝ)⁻¹ * ∑ i, rsign (σ (Sum.inl i))) := by
      rw [inner_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ha_def, hu_def, Sum.elim_inl, real_inner_smul_right, inner_neg_right]
      ring
    have hidY : ∑ j, rsign (σ (Sum.inr j)) * a t (Sum.inr j) =
        ⟪t.1.1 - fstar, ∑ j, rsign (σ (Sum.inr j)) • u (Sum.inr j)⟫_ℝ -
          (t.1.2.2 - ustar) * ((m : ℝ)⁻¹ * ∑ j, rsign (σ (Sum.inr j))) := by
      rw [inner_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [ha_def, hu_def, Sum.elim_inr, real_inner_smul_right]
      ring
    have hid : ∑ k, rsign (σ k) * a t k =
        ⟪t.1.1 - fstar, ∑ k, rsign (σ k) • u k⟫_ℝ + (t.1.2.1 - tstar) * ((n : ℝ)⁻¹ * ∑ i, rsign (σ (Sum.inl i))) -
          (t.1.2.2 - ustar) * ((m : ℝ)⁻¹ * ∑ j, rsign (σ (Sum.inr j))) := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, inner_add_right, hidX, hidY]
      ring
    rw [hid]
    have h1 : ⟪t.1.1 - fstar, ∑ k, rsign (σ k) • u k⟫_ℝ ≤ r * ‖∑ k, rsign (σ k) • u k‖ :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hp.1 (norm_nonneg _))
    have h2 : (t.1.2.1 - tstar) * ((n : ℝ)⁻¹ * ∑ i, rsign (σ (Sum.inl i))) ≤
        (κ * r + l1) * ((n : ℝ)⁻¹ * |∑ i, rsign (σ (Sum.inl i))|) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hnpos)]
      exact mul_le_mul_of_nonneg_right hp.2.1 (by positivity)
    have h3 : -((t.1.2.2 - ustar) * ((m : ℝ)⁻¹ * ∑ j, rsign (σ (Sum.inr j)))) ≤
        (κ * r + l2) * ((m : ℝ)⁻¹ * |∑ j, rsign (σ (Sum.inr j))|) := by
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
          (κ * r + l1) * ((n : ℝ)⁻¹ * |∑ i, rsign (σ (Sum.inl i))|) +
          (κ * r + l2) * ((m : ℝ)⁻¹ * |∑ j, rsign (σ (Sum.inr j))|)) := signE_mono hlin
    _ = r * signE (fun σ : Fin n ⊕ Fin m → Bool => ‖∑ k, rsign (σ k) • u k‖) +
          (κ * r + l1) * ((n : ℝ)⁻¹ * signE (fun σ : Fin n ⊕ Fin m → Bool => |∑ i, rsign (σ (Sum.inl i))|)) +
          (κ * r + l2) * ((m : ℝ)⁻¹ * signE (fun σ : Fin n ⊕ Fin m → Bool => |∑ j, rsign (σ (Sum.inr j))|)) := by
        rw [signE_add, signE_add, signE_const_mul, signE_const_mul, signE_const_mul, signE_const_mul,
          signE_const_mul]
    _ ≤ κ * r * √(sNM n m) + (κ * r + l1) * ek n + (κ * r + l2) * ek m := by
        rw [hX, hY]
        have key1 : (n : ℝ)⁻¹ * (n * ek n) = ek n := by field_simp
        have key2 : (m : ℝ)⁻¹ * (m * ek m) = ek m := by field_simp
        rw [key1, key2]
        have := mul_le_mul_of_nonneg_left hball hr
        nlinarith

theorem rampDev_star (P Q : Measure 𝒳) (φ : 𝒳 → H) (fstar : H) (tstar ustar : ℝ) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    rampDev P Q φ fstar tstar ustar z (fstar, tstar, ustar) = 0 := by
  rw [rampDev_eq]
  simp only [popDev, G1_star, G2_star, integral_zero, Finset.sum_const_zero, mul_zero, sub_zero, add_zero]

section Main

variable (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ : ℝ}
  (fstar : H) (tstar ustar : ℝ)

omit [InnerProductSpace ℝ H] in
theorem exists_dense [TopologicalSpace.SeparableSpace H] (r l1 l2 : ℝ) :
    ∃ T₀ : Set (H × ℝ × ℝ), T₀ ⊆ rampPar fstar tstar ustar κ r l1 l2 ∧ T₀.Countable ∧
      rampPar fstar tstar ustar κ r l1 l2 ⊆ closure T₀ :=
  (TopologicalSpace.IsSeparable.of_separableSpace _).exists_countable_dense_subset

theorem measurable_Zloc [TopologicalSpace.SeparableSpace H] (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    {r l1 l2 : ℝ} (hr : 0 ≤ r) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    Measurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => Zloc P Q φ fstar tstar ustar κ r l1 l2 z := by
  have hκ0 := kappa_nonneg P hκ
  obtain ⟨T₀, hT₀, hcount, hdense⟩ := exists_dense fstar tstar ustar (κ := κ) r l1 l2
  have hne : T₀.Nonempty := closure_nonempty_iff.1 ⟨_, hdense (star_mem fstar tstar ustar hκ0 hr hl1 hl2)⟩
  have : Nonempty T₀ := hne.to_subtype
  have : Countable T₀ := hcount.to_subtype
  have heq : (fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => Zloc P Q φ fstar tstar ustar κ r l1 l2 z) =
      fun z => ⨆ t : T₀, rampDev P Q φ fstar tstar ustar z t.1 := by
    funext z; exact Zloc_eq_iSup P Q fstar tstar ustar hφ hκ hr hl1 hl2 hn hm T₀ hT₀ hdense z
  rw [heq]
  exact Measurable.iSup fun t => measurable_rampDev P Q fstar tstar ustar hφ t.1

theorem abs_Zloc_le (hκ : ∀ x, ‖φ x‖ ≤ κ) {r l1 l2 : ℝ} (hr : 0 ≤ r) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2)
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    |Zloc P Q φ fstar tstar ustar κ r l1 l2 z| ≤ 2 * (2 * κ * r + l1) + 2 * (2 * κ * r + l2) := by
  have hκ0 := kappa_nonneg P hκ
  have : Nonempty (rampPar fstar tstar ustar κ r l1 l2) :=
    ⟨⟨_, star_mem fstar tstar ustar hκ0 hr hl1 hl2⟩⟩
  exact abs_ciSup_le fun p => abs_rampDev_le P Q fstar tstar ustar hκ hn hm z p.2

theorem integral_Zloc_le [TopologicalSpace.SeparableSpace H] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) {r l1 l2 : ℝ} (hr : 0 ≤ r) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2) {n m : ℕ} (hn : n ≠ 0)
    (hm : m ≠ 0) :
    ∫ z, Zloc P Q φ fstar tstar ustar κ r l1 l2 z ∂(sampleLaw P Q n m) ≤
      2 * (κ * r * √(sNM n m) + (κ * r + l1) * ek n + (κ * r + l2) * ek m) := by
  have hκ0 := kappa_nonneg P hκ
  obtain ⟨T₀, hT₀, hcount, hdense⟩ := exists_dense fstar tstar ustar (κ := κ) r l1 l2
  have hne : T₀.Nonempty := closure_nonempty_iff.1 ⟨_, hdense (star_mem fstar tstar ustar hκ0 hr hl1 hl2)⟩
  have : Nonempty T₀ := hne.to_subtype
  have : Countable T₀ := hcount.to_subtype
  set g₁ : T₀ → 𝒳 → ℝ := fun t y => -G1 φ fstar tstar t.1 y with hg₁
  set g₂ : T₀ → 𝒳 → ℝ := fun t y => -G2 φ fstar ustar t.1 y with hg₂
  have hm₁ : ∀ t, Measurable (g₁ t) := fun t => (measurable_G1 hφ fstar tstar t.1).neg
  have hm₂ : ∀ t, Measurable (g₂ t) := fun t => (measurable_G2 hφ fstar ustar t.1).neg
  set B : ℝ := 2 * κ * r + l1 + l2 with hB
  have hB₁ : ∀ t y, |g₁ t y| ≤ B := fun t y => by
    simp only [hg₁, abs_neg]; have := abs_G1_le fstar tstar ustar hκ hκ0 (hT₀ t.2) y; linarith
  have hB₂ : ∀ t y, |g₂ t y| ≤ B := fun t y => by
    simp only [hg₂, abs_neg]; have := abs_G2_le fstar tstar ustar hκ hκ0 (hT₀ t.2) y; linarith
  have hsym := integral_iSup_empDev2_le P Q hm₁ hm₂ hB₁ hB₂ hn hm
  have heq : ∀ z : (Fin n → 𝒳) × (Fin m → 𝒳), Zloc P Q φ fstar tstar ustar κ r l1 l2 z =
      ⨆ t : T₀, (empDev P g₁ n z.1 t + empDev Q g₂ m z.2 t) := by
    intro z
    rw [Zloc_eq_iSup P Q fstar tstar ustar hφ hκ hr hl1 hl2 hn hm T₀ hT₀ hdense z]
    congr 1; funext t
    rw [rampDev_eq, popDev_eq_neg_empDev, popDev_eq_neg_empDev]
    rfl
  simp_rw [heq]
  refine hsym.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have hninv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)
  have hint : Integrable (radAvg2 g₁ g₂ n m)
      ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) := by
    refine Integrable.of_bound (measurable_radAvg2 hm₁ hm₂ n m).aestronglyMeasurable
      (B + B) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    refine abs_signE_le fun σ => abs_ciSup_le fun θ => (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact abs_mean_le hn fun i => by rw [abs_mul, abs_rsign, one_mul]; exact hB₁ _ _
    · exact abs_mean_le hm fun j => by rw [abs_mul, abs_rsign, one_mul]; exact hB₂ _ _
  have := integral_mono hint
    (integrable_const (κ * r * √(sNM n m) + (κ * r + l1) * ek n + (κ * r + l2) * ek m))
    fun z => radAvg2_ramp_le fstar tstar ustar hκ hκ0 hr hl1 hl2 T₀ hT₀ hn hm z
  rwa [integral_const, probReal_univ, one_smul] at this

end Main

/-- Minkowski's inequality in `ℝ²`, in the form used for the McDiarmid radius. -/
theorem sqrt_mink {A a b u v : ℝ} (hA : 0 ≤ A) (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    √((A + a) ^ 2 * u + (A + b) ^ 2 * v) ≤ A * √(u + v) + √(a ^ 2 * u + b ^ 2 * v) := by
  have hX : 0 ≤ a ^ 2 * u + b ^ 2 * v := by positivity
  have hcs : a * u + b * v ≤ √(u + v) * √(a ^ 2 * u + b ^ 2 * v) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    nlinarith [mul_nonneg (mul_nonneg hu hv) (sq_nonneg (a - b))]
  have hR : 0 ≤ A * √(u + v) + √(a ^ 2 * u + b ^ 2 * v) := by positivity
  calc √((A + a) ^ 2 * u + (A + b) ^ 2 * v) ≤ √((A * √(u + v) + √(a ^ 2 * u + b ^ 2 * v)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have h1 := Real.sq_sqrt (show 0 ≤ u + v by positivity)
        have h2 := Real.sq_sqrt hX
        have h3 := mul_le_mul_of_nonneg_left hcs hA
        have e : (A * √(u + v) + √(a ^ 2 * u + b ^ 2 * v)) ^ 2 =
            A ^ 2 * (u + v) + 2 * (A * (√(u + v) * √(a ^ 2 * u + b ^ 2 * v))) + (a ^ 2 * u + b ^ 2 * v) := by
          rw [add_sq, mul_pow, h1, h2]; ring
        rw [e]
        nlinarith
    _ = A * √(u + v) + √(a ^ 2 * u + b ^ 2 * v) := Real.sqrt_sq hR

/-! ### The tail -/

theorem prob_Zloc (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ : ℝ}
    (fstar : H) (tstar ustar : ℝ) [TopologicalSpace.SeparableSpace H] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) {r l1 l2 : ℝ} (hr : 0 ≤ r) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2) {n m : ℕ} (hn : 1 ≤ n)
    (hm : 1 ≤ m) {χ : ℝ} (hχ : 0 < χ) :
    ENNReal.ofReal (1 - Real.exp (-χ)) ≤ sampleLaw P Q n m
      {z | Zloc P Q φ fstar tstar ustar κ r l1 l2 z ≤ κ * r * Lloc χ n m + Mloc l1 l2 χ n m} := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.1 hm
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hκ0 := kappa_nonneg P hκ
  have : Nonempty (rampPar fstar tstar ustar κ r l1 l2) :=
    ⟨⟨_, star_mem fstar tstar ustar hκ0 hr hl1 hl2⟩⟩
  set F : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun z => Zloc P Q φ fstar tstar ustar κ r l1 l2 z with hF
  have hFm : Measurable F := measurable_Zloc P Q fstar tstar ustar hφ hκ hr hl1 hl2 hn0 hm0
  set A1 : ℝ := 2 * κ * r + l1 with hA1
  set A2 : ℝ := 2 * κ * r + l2 with hA2
  have hA10 : 0 ≤ A1 := by positivity
  have hA20 : 0 ≤ A2 := by positivity
  have hs0 : 0 ≤ sNM n m := (sNM_pos hn hm).le
  set RHS : ℝ := κ * r * Lloc χ n m + Mloc l1 l2 χ n m with hRHS
  have hRHS0 : 0 ≤ RHS := by
    have := ek_nonneg n; have := ek_nonneg m
    simp only [hRHS, Lloc, Mloc]; positivity
  set S := {z | F z ≤ RHS} with hSdef
  have hSm : MeasurableSet S := measurableSet_le hFm measurable_const
  by_cases hdeg : A1 = 0 ∧ A2 = 0
  · have hall : S = univ := by
      refine eq_univ_of_forall fun z => ?_
      have := abs_Zloc_le P Q fstar tstar ustar hκ hr hl1 hl2 hn0 hm0 z
      rw [← hA1, ← hA2, hdeg.1, hdeg.2] at this
      show F z ≤ RHS
      have := (le_abs_self (F z)).trans this
      linarith
    rw [hall, measure_univ]
    exact ENNReal.ofReal_le_one.2 (by linarith [Real.exp_pos (-χ)])
  · set W : ℝ := A1 ^ 2 / n + A2 ^ 2 / m with hW
    have hWpos : 0 < W := by
      rcases not_and_or.1 hdeg with h | h
      · have : 0 < A1 ^ 2 / n := div_pos (by positivity) hnpos
        have : 0 ≤ A2 ^ 2 / m := by positivity
        linarith
      · have : 0 < A2 ^ 2 / m := div_pos (by positivity) hmpos
        have : 0 ≤ A1 ^ 2 / n := by positivity
        linarith
    set cX : ℝ := 2 * A1 / n with hcX
    set cY : ℝ := 2 * A2 / m with hcY
    have hbX : ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳) (i : Fin n) (b : 𝒳),
        |F (Function.update x i b, y) - F (x, y)| ≤ cX := by
      intro x y i b
      refine abs_iSup_sub_iSup_le (bdd_rampDev P Q fstar tstar ustar hκ hn0 hm0 _)
        (bdd_rampDev P Q fstar tstar ustar hκ hn0 hm0 _) fun p => ?_
      rw [rampDev_eq, rampDev_eq]
      dsimp only
      rw [add_sub_add_right_eq_sub, popDev_update_sub, abs_neg, abs_mul, abs_inv, Nat.abs_cast,
        hcX, div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hnpos.le)
      have h1 := abs_G1_le fstar tstar ustar hκ hκ0 p.2 b
      have h2 := abs_G1_le fstar tstar ustar hκ hκ0 p.2 (x i)
      refine (abs_sub _ _).trans ?_
      linarith
    have hbY : ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳) (j : Fin m) (b : 𝒳),
        |F (x, Function.update y j b) - F (x, y)| ≤ cY := by
      intro x y j b
      refine abs_iSup_sub_iSup_le (bdd_rampDev P Q fstar tstar ustar hκ hn0 hm0 _)
        (bdd_rampDev P Q fstar tstar ustar hκ hn0 hm0 _) fun p => ?_
      rw [rampDev_eq, rampDev_eq]
      dsimp only
      rw [add_sub_add_left_eq_sub, popDev_update_sub, abs_neg, abs_mul, abs_inv, Nat.abs_cast,
        hcY, div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hmpos.le)
      have h1 := abs_G2_le fstar tstar ustar hκ hκ0 p.2 b
      have h2 := abs_G2_le fstar tstar ustar hκ hκ0 p.2 (y j)
      refine (abs_sub _ _).trans ?_
      linarith
    set ε : ℝ := √(2 * χ * W) with hε
    have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
    have hmcd := StatFormal.Wave30tp.mcdiarmid_two_sample P Q F hFm (by positivity) (by positivity)
      hbX hbY hε0
    have hexp : -ε ^ 2 / (2 * ((n * cX ^ 2 + m * cY ^ 2) / 4)) = -χ := by
      have h1 : ((n : ℝ) * cX ^ 2 + m * cY ^ 2) / 4 = W := by
        rw [hcX, hcY, hW]; field_simp; ring
      rw [h1, hε, Real.sq_sqrt (by positivity)]
      field_simp
    rw [hexp] at hmcd
    have hEZ : (∫ w, F w ∂(sampleLaw P Q n m)) ≤
        2 * (κ * r * √(sNM n m) + (κ * r + l1) * ek n + (κ * r + l2) * ek m) :=
      integral_Zloc_le P Q fstar tstar ustar hφ hκ hr hl1 hl2 hn0 hm0
    have hχ2 : 0 ≤ 2 * χ := by positivity
    have hsqW : √W ≤ 2 * κ * r * √(sNM n m) + √(l1 ^ 2 / n + l2 ^ 2 / m) := by
      have h := sqrt_mink (A := 2 * κ * r) (a := l1) (b := l2) (u := 1 / (n : ℝ)) (v := 1 / (m : ℝ))
        (by positivity) hl1 hl2 (by positivity) (by positivity)
      have e1 : W = (2 * κ * r + l1) ^ 2 * (1 / (n : ℝ)) + (2 * κ * r + l2) ^ 2 * (1 / (m : ℝ)) := by
        rw [hW, hA1, hA2]; ring
      have e2 : l1 ^ 2 / (n : ℝ) + l2 ^ 2 / m = l1 ^ 2 * (1 / (n : ℝ)) + l2 ^ 2 * (1 / (m : ℝ)) := by ring
      rw [e1, e2]
      unfold sNM
      exact h
    have hεle : ε ≤ √(2 * χ) * (2 * κ * r * √(sNM n m)) + √(2 * χ) * √(l1 ^ 2 / n + l2 ^ 2 / m) := by
      rw [hε, Real.sqrt_mul hχ2, ← mul_add]
      exact mul_le_mul_of_nonneg_left hsqW (Real.sqrt_nonneg _)
    have hLe : κ * r * Lloc χ n m = 2 * κ * r * √(sNM n m) + 2 * κ * r * (ek n + ek m) +
        2 * κ * r * (√(2 * χ) * √(sNM n m)) := by
      unfold Lloc; rw [Real.sqrt_mul hχ2]; ring
    have hMe : Mloc l1 l2 χ n m = 2 * (l1 * ek n + l2 * ek m) + √(2 * χ) * √(l1 ^ 2 / n + l2 ^ 2 / m) := by
      unfold Mloc; rw [Real.sqrt_mul hχ2]
    have hbound : (∫ w, F w ∂(sampleLaw P Q n m)) + ε ≤ RHS := by
      rw [hRHS, hLe, hMe]
      nlinarith
    have hsub : Sᶜ ⊆ {z | ε ≤ F z - ∫ w, F w ∂(sampleLaw P Q n m)} := by
      intro z hz
      simp only [hSdef, mem_compl_iff, mem_ofPred_eq, not_le] at hz ⊢
      linarith
    have hc : (sampleLaw P Q n m).real Sᶜ ≤ Real.exp (-χ) := (measureReal_mono hsub).trans hmcd
    rw [probReal_compl_eq_one_sub hSm] at hc
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### `lem:localmod (v2)` -/

theorem localmod : StatFormal.Wave30tx.Claims.localmod := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ fstar tstar ustar r l1 l2 n m hφ hκ hr hl1 hl2 hn hm
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.1 hm
  have hκ0 := kappa_nonneg P hκ
  have : Nonempty (rampPar fstar tstar ustar κ r l1 l2) :=
    ⟨⟨_, star_mem fstar tstar ustar hκ0 hr hl1 hl2⟩⟩
  have hZm := measurable_Zloc P Q fstar tstar ustar hφ hκ hr hl1 hl2 hn0 hm0
  refine ⟨hZm, fun z => ?_, fun z p hp => ?_, fun z => ?_, ?_,
    integral_Zloc_le P Q fstar tstar ustar hφ hκ hr hl1 hl2 hn0 hm0,
    fun χ hχ => prob_Zloc P Q fstar tstar ustar hφ hκ hr hl1 hl2 hn hm hχ⟩
  · -- nonnegativity: the parameter `(f*, t*, u*)`
    have h := le_ciSup (bdd_rampDev P Q fstar tstar ustar hκ hn0 hm0 z)
      ⟨_, star_mem fstar tstar ustar hκ0 hr hl1 hl2⟩
    rw [rampDev_star] at h
    exact h
  · exact le_ciSup (bdd_rampDev P Q fstar tstar ustar hκ hn0 hm0 z) ⟨p, hp⟩
  · -- monotonicity in the radius
    intro r₁ hr₁ r₂ hr₂ h12
    have hr₁' : (0 : ℝ) ≤ r₁ := hr₁
    have : Nonempty (rampPar fstar tstar ustar κ r₁ l1 l2) :=
      ⟨⟨_, star_mem fstar tstar ustar hκ0 hr₁' hl1 hl2⟩⟩
    refine ciSup_le fun p => ?_
    have hp := p.2
    have hsub : p.1 ∈ rampPar fstar tstar ustar κ r₂ l1 l2 := by
      have hk : κ * r₁ ≤ κ * r₂ := mul_le_mul_of_nonneg_left h12 hκ0
      exact ⟨hp.1.trans h12, hp.2.1.trans (by linarith), hp.2.2.trans (by linarith)⟩
    exact le_ciSup (bdd_rampDev P Q fstar tstar ustar hκ hn0 hm0 z) ⟨p.1, hsub⟩
  · -- integrability
    refine Integrable.of_bound hZm.aestronglyMeasurable (2 * (2 * κ * r + l1) + 2 * (2 * κ * r + l2))
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    exact abs_Zloc_le P Q fstar tstar ustar hκ hr hl1 hl2 hn0 hm0 z

end StatFormal.Wave30tx.RLocal
