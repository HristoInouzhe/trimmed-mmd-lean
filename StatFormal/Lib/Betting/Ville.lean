import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Ville's inequality on a finite horizon

Library component (untrusted library code: no `Statements.lean` is involved).

## Main result

* `ville_finite`: for a nonnegative supermartingale `(K_t)_{t ∈ ℕ}` with respect to a filtration `𝒢` on a finite
  measure space, every horizon `N` and every level `a > 0`,
  `a · μ{∃ t ≤ N, K_t ≥ a} ≤ E K_0`;
* `ville_finite_le`: the same, divided by `a`, as a bound on `μ` in `ℝ≥0∞`.

## Proof

Optional stopping (Mathlib `Submartingale.expected_stoppedValue_mono`, applied to `−K`) at the bounded stopping
time `τ = min{t ≤ N : K_t ≥ a} ∧ N` (Mathlib `hittingBtwn`) gives `E K_τ ≤ E K_0`; on `{∃ t ≤ N, K_t ≥ a}` we have
`K_τ ≥ a` (`stoppedValue_hittingBtwn_mem`), and Markov's inequality concludes.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatFormal.Betting

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Ville's inequality on a finite horizon**: `a · μ{∃ t ≤ N, a ≤ K_t} ≤ E K_0` for a nonnegative
supermartingale `K` and `a > 0`. -/
theorem ville_finite [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {K : ℕ → Ω → ℝ}
    (hK : Supermartingale K 𝒢 μ) (hnn : ∀ t ω, 0 ≤ K t ω) (N : ℕ) {a : ℝ} (ha : 0 < a) :
    a * μ.real {ω | ∃ t ≤ N, a ≤ K t ω} ≤ ∫ ω, K 0 ω ∂μ := by
  classical
  set π : Ω → WithTop ℕ := fun ω => ((hittingBtwn K {y : ℝ | a ≤ y} 0 N ω : ℕ) : WithTop ℕ)
    with hπdef
  have hπ : IsStoppingTime 𝒢 π :=
    hK.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hsub : Submartingale (-K) 𝒢 μ := hK.neg
  have hle : (fun _ => ((0 : ℕ) : WithTop ℕ)) ≤ π := fun ω => by
    simp only [hπdef]
    exact_mod_cast Nat.zero_le _
  have hbdd : ∀ ω, π ω ≤ N := fun ω => by
    simp only [hπdef]
    exact_mod_cast hittingBtwn_le (u := K) (s := {y : ℝ | a ≤ y}) (n := 0) (m := N) ω
  have hmono := hsub.expected_stoppedValue_mono (isStoppingTime_const 𝒢 0) hπ hle hbdd
  rw [stoppedValue_const] at hmono
  have hneg : stoppedValue (-K) π = fun ω => -stoppedValue K π ω := rfl
  rw [hneg, integral_neg] at hmono
  have hneg0 : (-K) 0 = fun ω => -K 0 ω := rfl
  rw [hneg0, integral_neg] at hmono
  have hEτ : ∫ ω, stoppedValue K π ω ∂μ ≤ ∫ ω, K 0 ω ∂μ := by linarith
  -- integrability of the stopped value
  have hint : Integrable (stoppedValue K π) μ := by
    have h := hsub.integrable_stoppedValue hπ hbdd
    have : stoppedValue K π = -stoppedValue (-K) π := by
      funext ω; simp [stoppedValue]
    rw [this]; exact h.neg
  -- Markov
  have hmarkov : a * μ.real {ω | a ≤ stoppedValue K π ω} ≤ ∫ ω, stoppedValue K π ω ∂μ :=
    mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => hnn _ ω) hint a
  have hsubset : {ω | ∃ t ≤ N, a ≤ K t ω} ⊆ {ω | a ≤ stoppedValue K π ω} := by
    intro ω hω
    obtain ⟨t, htN, ht⟩ := hω
    have hmem : stoppedValue K (fun ω ↦ (hittingBtwn K {y : ℝ | a ≤ y} 0 N ω : ℕ)) ω ∈
        {y : ℝ | a ≤ y} :=
      stoppedValue_hittingBtwn_mem ⟨t, ⟨Nat.zero_le _, htN⟩, ht⟩
    exact hmem
  have hmeas : μ.real {ω | ∃ t ≤ N, a ≤ K t ω} ≤ μ.real {ω | a ≤ stoppedValue K π ω} :=
    measureReal_mono hsubset
  calc a * μ.real {ω | ∃ t ≤ N, a ≤ K t ω} ≤ a * μ.real {ω | a ≤ stoppedValue K π ω} :=
        mul_le_mul_of_nonneg_left hmeas ha.le
    _ ≤ ∫ ω, stoppedValue K π ω ∂μ := hmarkov
    _ ≤ ∫ ω, K 0 ω ∂μ := hEτ

/-- **Ville's inequality on a finite horizon**, measure form: `μ{∃ t ≤ N, a ≤ K_t} ≤ E K_0 / a`. -/
theorem ville_finite_le [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {K : ℕ → Ω → ℝ}
    (hK : Supermartingale K 𝒢 μ) (hnn : ∀ t ω, 0 ≤ K t ω) (N : ℕ) {a : ℝ} (ha : 0 < a) :
    μ {ω | ∃ t ≤ N, a ≤ K t ω} ≤ ENNReal.ofReal ((∫ ω, K 0 ω ∂μ) / a) := by
  have h := ville_finite hK hnn N ha
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ ha]; linarith

end StatFormal.Betting
