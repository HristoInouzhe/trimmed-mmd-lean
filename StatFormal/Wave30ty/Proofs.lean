import StatFormal.Wave30ty.RouteTwo
import StatFormal.Wave30ty.RouteOne

set_option linter.style.longLine false

/-!
# Proofs — wave 30ty (untrusted; each theorem has the type of its frozen claim)

Routes: `RouteBasic` (the maps `ψ_x`, the hinge functions, `empDev` of single functions, `e_k`), `RouteTwo` (two samples: one
supremum `Zc c` with `Z = Zc (−1)`, `Z⁻ = Zc 1`; measurability over a countable dense subset, symmetrisation, coordinatewise
contraction, two-sample McDiarmid, the degenerate case `Zc ≡ 0`), `RouteOne` (the same for one sample, McDiarmid for one i.i.d.
sample).
-/

namespace StatFormal.Wave30ty

open MeasureTheory

private theorem kappa_nonneg {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] (P : Measure 𝒳)
    [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) : 0 ≤ κ := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  exact (norm_nonneg _).trans (hκ x₀)

private theorem abs_neg_one_le : |(-1 : ℝ)| ≤ 1 := by norm_num

private theorem abs_one_le : |(1 : ℝ)| ≤ 1 := by norm_num

theorem hinge : Claims.hinge := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ ψ₁ ψ₂ r ρ₁ ρ₂ n m hφ hκ hψ₁ hψ₂ hr h1 h2 hn hm
  have hκ0 := kappa_nonneg P hκ
  have hn0 : n ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  simp only [RTwo.hingeZ_eq, RTwo.hingeZm_eq]
  exact ⟨RTwo.measurable_Zc P Q abs_neg_one_le hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2,
    RTwo.measurable_Zc P Q abs_one_le hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2,
    RTwo.integrable_Zc P Q abs_neg_one_le hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2 n m,
    RTwo.integrable_Zc P Q abs_one_le hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2 n m,
    RTwo.integral_Zc_le P Q abs_neg_one_le hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2 hn0 hm0,
    RTwo.integral_Zc_le P Q abs_one_le hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2 hn0 hm0⟩

theorem hinge_tail : Claims.hinge_tail := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ ψ₁ ψ₂ r ρ₁ ρ₂ Δ₁ Δ₂ n m hφ hκ hψ₁ hψ₂ hr h1 h2 hn hm hΔ₁ hΔ₂ hV χ hχ
  have hκ0 := kappa_nonneg P hκ
  simp only [RTwo.hingeZ_eq, RTwo.hingeZm_eq]
  exact ⟨RTwo.tail_Zc P Q abs_neg_one_le hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2 hn hm hΔ₁ hΔ₂ hV hχ,
    RTwo.tail_Zc P Q abs_one_le hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2 hn hm hΔ₁ hΔ₂ hV hχ⟩

theorem hinge_tail_strict : Claims.hinge_tail_strict := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ ψ₁ ψ₂ r ρ₁ ρ₂ Δ₁ Δ₂ n m hφ hκ hψ₁ hψ₂ hr h1 h2 hn hm hΔ₁ hΔ₂ χ hχ
  have hκ0 := kappa_nonneg P hκ
  simp only [RTwo.hingeZ_eq, RTwo.hingeZm_eq]
  exact ⟨RTwo.tail_strict_Zc P Q abs_neg_one_le hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2 hn hm hΔ₁ hΔ₂ hχ,
    RTwo.tail_strict_Zc P Q abs_one_le hψ₁ hψ₂ hφ hκ hκ0 hr h1 h2 hn hm hΔ₁ hΔ₂ hχ⟩

theorem hinge1 : Claims.hinge1 := by
  intro 𝒳 H _ _ _ _ P _ φ κ ψ₁ r ρ₁ n hφ hκ hψ₁ hr h1 hn
  have hκ0 := kappa_nonneg P hκ
  have hn0 : n ≠ 0 := by omega
  simp only [ROne.hingeZ1_eq, ROne.hingeZ1m_eq]
  exact ⟨ROne.measurable_Z1c P abs_neg_one_le hψ₁ hφ hκ hκ0 hr h1,
    ROne.measurable_Z1c P abs_one_le hψ₁ hφ hκ hκ0 hr h1,
    ROne.integrable_Z1c P abs_neg_one_le hψ₁ hφ hκ hκ0 hr h1 n,
    ROne.integrable_Z1c P abs_one_le hψ₁ hφ hκ hκ0 hr h1 n,
    ROne.integral_Z1c_le P abs_neg_one_le hψ₁ hφ hκ hκ0 hr h1 hn0,
    ROne.integral_Z1c_le P abs_one_le hψ₁ hφ hκ hκ0 hr h1 hn0⟩

theorem hinge1_tail : Claims.hinge1_tail := by
  intro 𝒳 H _ _ _ _ P _ φ κ ψ₁ r ρ₁ Δ₁ n hφ hκ hψ₁ hr h1 hn hΔ₁ hV χ hχ
  have hκ0 := kappa_nonneg P hκ
  simp only [ROne.hingeZ1_eq, ROne.hingeZ1m_eq]
  exact ⟨ROne.tail_Z1c P abs_neg_one_le hψ₁ hφ hκ hκ0 hr h1 hn hΔ₁ hV hχ,
    ROne.tail_Z1c P abs_one_le hψ₁ hφ hκ hκ0 hr h1 hn hΔ₁ hV hχ⟩

theorem hinge1_tail_strict : Claims.hinge1_tail_strict := by
  intro 𝒳 H _ _ _ _ P _ φ κ ψ₁ r ρ₁ Δ₁ n hφ hκ hψ₁ hr h1 hn hΔ₁ χ hχ
  have hκ0 := kappa_nonneg P hκ
  simp only [ROne.hingeZ1_eq, ROne.hingeZ1m_eq]
  exact ⟨ROne.tail_strict_Z1c P abs_neg_one_le hψ₁ hφ hκ hκ0 hr h1 hn hΔ₁ hχ,
    ROne.tail_strict_Z1c P abs_one_le hψ₁ hφ hκ hκ0 hr h1 hn hΔ₁ hχ⟩

/-- The zero map is a hinge map. -/
private theorem isHingeMap_zero : IsHingeMap (fun (_ : Unit) (_ : ℝ) => (0 : ℝ)) :=
  ⟨fun _ => (LipschitzWith.const (0 : ℝ)).weaken (by norm_num), measurable_const, 0, by simp⟩

/-- Counterexample: `𝒳 = Unit`, `𝓗 = ℝ`, `φ = 0`, `ψ¹ = ψ² ≡ 0`, `P = Q = δ_()`, `n = m = 1`, `r = ρ = Δ = 0`, `χ = 1`; then
`Z ≡ 0` and the event `{Z ≥ E Z + 0}` is everything, of probability `1 > e^{−1}`. -/
theorem hinge_tail_printed_false : Claims.hinge_tail_printed_false := by
  have hexp : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  constructor
  · intro h
    have := h Unit ℝ (Measure.dirac ()) (Measure.dirac ()) (fun _ => 0) 0 (fun _ _ => 0) (fun _ _ => 0)
      0 0 0 0 0 1 1 stronglyMeasurable_const (by simp) isHingeMap_zero isHingeMap_zero le_rfl le_rfl le_rfl
      le_rfl le_rfl (by intros; simp [hOne]) (by intros; simp [hTwo]) 1 one_pos
    obtain ⟨h1, -⟩ := this
    unfold TailAtLeast at h1
    have hZ : (fun z : (Fin 1 → Unit) × (Fin 1 → Unit) =>
        hingeZ (Measure.dirac ()) (Measure.dirac ()) (fun _ => (0 : ℝ)) (fun _ _ => 0) (fun _ _ => 0) 0 0 0 z)
        = fun _ => 0 := by
      funext z; simp [hingeZ, devPop, hOne, hTwo]
    rw [hZ] at h1
    have hset : {ω : (Fin 1 → Unit) × (Fin 1 → Unit) |
        (∫ w, (fun _ => (0 : ℝ)) w ∂(StatFormal.Wave30tp.sampleLaw (Measure.dirac ()) (Measure.dirac ()) 1 1)) +
          √(1 * ((0 : ℝ) ^ 2 / ((1 : ℕ) : ℝ) + (0 : ℝ) ^ 2 / ((1 : ℕ) : ℝ)) / 2) ≤ (fun _ => (0 : ℝ)) ω} = Set.univ := by
      ext ω; simp
    rw [hset, measure_univ] at h1
    have := (ENNReal.one_le_ofReal).1 h1
    linarith
  · intro h
    have := h Unit ℝ (Measure.dirac ()) (fun _ => 0) 0 (fun _ _ => 0)
      0 0 0 1 stronglyMeasurable_const (by simp) isHingeMap_zero le_rfl le_rfl le_rfl
      (by intros; simp [hOne]) 1 one_pos
    obtain ⟨h1, -⟩ := this
    unfold TailAtLeast at h1
    have hZ : (fun x : Fin 1 → Unit =>
        hingeZ1 (Measure.dirac ()) (fun _ => (0 : ℝ)) (fun _ _ => 0) 0 0 x) = fun _ => 0 := by
      funext z; simp [hingeZ1, devPop, hOne]
    rw [hZ] at h1
    have hset : {ω : Fin 1 → Unit |
        (∫ w, (fun _ => (0 : ℝ)) w ∂(Measure.pi fun _ : Fin 1 => Measure.dirac ())) +
          √(1 * ((0 : ℝ) ^ 2 / ((1 : ℕ) : ℝ)) / 2) ≤ (fun _ => (0 : ℝ)) ω} = Set.univ := by
      ext ω; simp
    rw [hset, measure_univ] at h1
    have := (ENNReal.one_le_ofReal).1 h1
    linarith

end StatFormal.Wave30ty
