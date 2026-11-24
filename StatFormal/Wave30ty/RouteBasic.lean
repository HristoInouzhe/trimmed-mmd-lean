import StatFormal.Wave30ty.Statements
import StatFormal.Lib.Concentration.Symmetrization2
import StatFormal.Lib.Concentration.EmpiricalProcess

set_option linter.style.longLine false

/-!
# Route: basic facts for `lem:hinge (v2)` (untrusted proof material)

* the maps `ψ_x`: Lipschitz bound, growth `|ψ_x(w)| ≤ C + |w|`, measurability of `h¹`, `h²`;
* `h¹`, `h²`: bounds and Lipschitz dependence on the parameter (`|v(x) − v'(x)| ≤ κ‖v − v'‖`);
* `empDev` of a single function: bound, difference of two parameters, constant functions;
* the constants `e_k` (`radE` form) and `s`.
-/

noncomputable section
open MeasureTheory Set Finset
open scoped InnerProductSpace

namespace StatFormal.Wave30ty.RBasic

open StatFormal.Wave30ty StatFormal.Concentration StatFormal.Wave30tp StatFormal.Wave30tr

/-! ### Constants -/

theorem ek_eq_radE (k : ℕ) : ek k = radE (fun σ : Fin k → Bool => |∑ i, rsign (σ i)|) / k := rfl

theorem ek_nonneg (k : ℕ) : 0 ≤ ek k := by
  rw [ek_eq_radE]; exact div_nonneg (radE_nonneg fun σ => abs_nonneg _) (Nat.cast_nonneg _)

theorem mul_ek {k : ℕ} (hk : k ≠ 0) :
    (k : ℝ) * ek k = radE (fun σ : Fin k → Bool => |∑ i, rsign (σ i)|) := by
  have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  rw [ek_eq_radE]; field_simp

theorem sNM_pos {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) : 0 < sNM n m := by
  unfold sNM
  have : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  positivity

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### The maps `ψ_x` -/

theorem lip (hψ : IsHingeMap ψ) (x : 𝒳) (u w : ℝ) : |ψ x u - ψ x w| ≤ |u - w| := by
  have := (hψ.1 x).dist_le_mul u w
  simpa [Real.dist_eq] using this

theorem growth (hψ : IsHingeMap ψ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : 𝒳) w, |ψ x w| ≤ C + |w| := by
  obtain ⟨C, hC⟩ := hψ.2.2
  refine ⟨max C 0, le_max_right _ _, fun x w => ?_⟩
  have h1 := lip hψ x w 0
  rw [sub_zero] at h1
  have h2 := abs_sub_abs_le_abs_sub (ψ x w) (ψ x 0)
  linarith [hC x, le_max_left C 0]

omit [MeasurableSpace 𝒳] in
theorem abs_inner_le {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (v : H) (x : 𝒳) :
    |⟪v, φ x⟫_ℝ| ≤ κ * ‖v‖ :=
  (abs_real_inner_le_norm _ _).trans (by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hκ x) (norm_nonneg _))

theorem measurable_hOne (hψ : IsHingeMap ψ) {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) (v : H) (a : ℝ) :
    Measurable (hOne ψ φ v a) := by
  have h1 : Measurable fun x => ⟪v, φ x⟫_ℝ := (stronglyMeasurable_const.inner hφ).measurable
  have h2 : Measurable fun x => (x, a - ⟪v, φ x⟫_ℝ) := measurable_id.prodMk (measurable_const.sub h1)
  exact hψ.2.1.comp h2

theorem measurable_hTwo (hψ : IsHingeMap ψ) {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) (v : H) (b : ℝ) :
    Measurable (hTwo ψ φ v b) := by
  have h1 : Measurable fun x => ⟪v, φ x⟫_ℝ := (stronglyMeasurable_const.inner hφ).measurable
  have h2 : Measurable fun x => (x, ⟪v, φ x⟫_ℝ - b) := measurable_id.prodMk (h1.sub measurable_const)
  exact hψ.2.1.comp h2

omit [MeasurableSpace 𝒳] in
theorem abs_hOne_le {ψ : 𝒳 → ℝ → ℝ} {C : ℝ} (hC : ∀ x w, |ψ x w| ≤ C + |w|) {φ : 𝒳 → H} {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (v : H) (a : ℝ) (x : 𝒳) : |hOne ψ φ v a x| ≤ C + (|a| + κ * ‖v‖) := by
  unfold hOne
  refine (hC x _).trans ?_
  have := abs_sub a ⟪v, φ x⟫_ℝ
  have := abs_inner_le hκ v x
  linarith

omit [MeasurableSpace 𝒳] in
theorem abs_hTwo_le {ψ : 𝒳 → ℝ → ℝ} {C : ℝ} (hC : ∀ x w, |ψ x w| ≤ C + |w|) {φ : 𝒳 → H} {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (v : H) (b : ℝ) (y : 𝒳) : |hTwo ψ φ v b y| ≤ C + (|b| + κ * ‖v‖) := by
  unfold hTwo
  refine (hC y _).trans ?_
  have := abs_sub ⟪v, φ y⟫_ℝ b
  have := abs_inner_le hκ v y
  linarith

theorem abs_hOne_sub (hψ : IsHingeMap ψ) {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (v v' : H) (a a' : ℝ)
    (x : 𝒳) : |hOne ψ φ v a x - hOne ψ φ v' a' x| ≤ |a - a'| + κ * ‖v - v'‖ := by
  unfold hOne
  refine (lip hψ x _ _).trans ?_
  have e : a - ⟪v, φ x⟫_ℝ - (a' - ⟪v', φ x⟫_ℝ) = (a - a') - ⟪v - v', φ x⟫_ℝ := by
    rw [inner_sub_left]; ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  have := abs_inner_le hκ (v - v') x
  linarith

theorem abs_hTwo_sub (hψ : IsHingeMap ψ) {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (v v' : H) (b b' : ℝ)
    (y : 𝒳) : |hTwo ψ φ v b y - hTwo ψ φ v' b' y| ≤ |b - b'| + κ * ‖v - v'‖ := by
  unfold hTwo
  refine (lip hψ y _ _).trans ?_
  have e : ⟪v, φ y⟫_ℝ - b - (⟪v', φ y⟫_ℝ - b') = ⟪v - v', φ y⟫_ℝ - (b - b') := by
    rw [inner_sub_left]; ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  have := abs_inner_le hκ (v - v') y
  linarith

/-! ### `empDev` of single functions -/

theorem abs_empDev_single (P : Measure 𝒳) [IsProbabilityMeasure P] {h : 𝒳 → ℝ} {L : ℝ}
    (hL : ∀ y, |h y| ≤ L) {n : ℕ} (x : Fin n → 𝒳) :
    |(n : ℝ)⁻¹ * ∑ i, h (x i) - ∫ y, h y ∂P| ≤ 2 * L :=
  abs_empDev_le P (g := fun (_ : Unit) => h) (fun _ y => hL y) x ()

theorem empDev_sub_eq (P : Measure 𝒳) {T : Type*} {g : T → 𝒳 → ℝ} {t t' : T} (h1 : Integrable (g t) P)
    (h2 : Integrable (g t') P) {n : ℕ} (x : Fin n → 𝒳) :
    empDev P g n x t - empDev P g n x t' =
      (n : ℝ)⁻¹ * ∑ i, (g t (x i) - g t' (x i)) - ∫ y, (g t y - g t' y) ∂P := by
  simp only [empDev]
  rw [integral_sub h1 h2, Finset.sum_sub_distrib]
  ring

theorem empDev_const (P : Measure 𝒳) [IsProbabilityMeasure P] {T : Type*} {g : T → 𝒳 → ℝ} {t : T} {K : ℝ}
    (hK : ∀ y, g t y = K) {n : ℕ} (hn : n ≠ 0) (x : Fin n → 𝒳) : empDev P g n x t = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp only [empDev, hK, integral_const, probReal_univ, one_smul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- If `|h(x) − h(x')| ≤ 0` for all points, `h` is constant. -/
theorem const_of_osc {h : 𝒳 → ℝ} (hosc : ∀ x x', |h x - h x'| ≤ 0) (x₀ : 𝒳) : ∀ y, h y = h x₀ := by
  intro y
  have := hosc y x₀
  have := abs_nonneg (h y - h x₀)
  have : |h y - h x₀| = 0 := by linarith
  rw [abs_eq_zero, sub_eq_zero] at this
  exact this

end StatFormal.Wave30ty.RBasic
