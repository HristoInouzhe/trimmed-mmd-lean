import StatFormal.Lib.LocalLower.Bump
import StatFormal.Lib.Distances.Product
import StatFormal.Wave31tn.RouteKL

/-!
# The chi-square of the bump and Le Cam's two-point step with a randomization (library, untrusted)

For a probability measure `μ`, disjoint measurable `A, B`, `0 < π ≤ min{μ(A), μ(B)}` and `h ∈ [0,1]`, the bump law
`μ_h = bumpFac·μ`, `bumpFac = 1 + (hπ/μ(A))·1_A − (hπ/μ(B))·1_B`, has

* `klDiv_bumpFac_le`: `KL(μ_h‖μ) ≤ χ²(μ_h‖μ) = a²μ(A) + b²μ(B)` (`KL ≤ χ²`, the certified 31tn `RouteKL.klDiv_le_of_withDensity`);
* `tvDist_pi_bumpFac_le`: `TV(μ_h^n, μ^n) ≤ √(n·KL/2) ≤ h√(nπ)`, as `χ² = (hπ)²{1/μ(A) + 1/μ(B)} ≤ 2h²π` (Pinsker and
  tensorisation, `Distances.tvDist_pi_le_sqrt_klDiv`);
* `withDensity_bump`: `bump f·ν = bumpFac·(f·ν)`;
* `lecam_randomized`: Le Cam's step for a statistic of the data and an independent randomization: if `T > t₀` has probability at
  most `δ` under `μ₀ ⊗ ρ` and `TV(μ₁, μ₀) ≤ c`, then `T ≤ t₀` has probability at least `1 − δ − c` under `μ₁ ⊗ ρ`.

The argument is that of the proof of Proposition 5.10 (`prop:lower2pt`) of the trimmed-mmd paper, formalized in 31tn (`RouteS1`,
`RouteKL`); see Tsybakov, *Introduction to Nonparametric Estimation*, §2.4 (Pinsker, `KL ≤ χ²`) and Lemma 2.1 (Le Cam).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter InformationTheory
open scoped ENNReal

namespace StatFormal.LocalLower

variable {α : Type*} [MeasurableSpace α] {f : α → ℝ} {A B : Set α} {a b : ℝ}

/-- The bump factor `1 + a·1_A − b·1_B`, so that `bump f A B a b = f · bumpFac A B a b`. -/
def bumpFac (A B : Set α) (a b : ℝ) (z : α) : ℝ :=
  1 + a * A.indicator (fun _ => (1 : ℝ)) z - b * B.indicator (fun _ => (1 : ℝ)) z

omit [MeasurableSpace α] in
theorem bump_eq_mul (f : α → ℝ) (A B : Set α) (a b : ℝ) (z : α) : bump f A B a b z = f z * bumpFac A B a b z := rfl

theorem measurable_bumpFac (hA : MeasurableSet A) (hB : MeasurableSet B) : Measurable (bumpFac A B a b) := by
  unfold bumpFac
  exact (measurable_const.add (measurable_const.mul (measurable_const.indicator hA))).sub
    (measurable_const.mul (measurable_const.indicator hB))

theorem bumpFac_nonneg (hAB : Disjoint A B) (ha : 0 ≤ a) (hb : b ≤ 1) (z : α) : 0 ≤ bumpFac A B a b z := by
  have := bump_nonneg (f := fun _ => (1 : ℝ)) hAB (fun _ => zero_le_one) ha hb z
  rwa [bump_eq_mul, one_mul] at this

/-- `bump f·ν = bumpFac·(f·ν)` for a measurable density `f ≥ 0`. -/
theorem withDensity_bump {ν : Measure α} (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z) (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    (ν.withDensity fun x => ENNReal.ofReal (bump f A B a b x)) =
      (ν.withDensity fun x => ENNReal.ofReal (f x)).withDensity fun x => ENNReal.ofReal (bumpFac A B a b x) := by
  rw [← withDensity_mul _ hf.ennreal_ofReal (measurable_bumpFac hA hB).ennreal_ofReal]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [bump_eq_mul, ENNReal.ofReal_mul (hf0 x)]

/-- **`KL ≤ χ²` for the bump**: `KL(bumpFac·μ ‖ μ) ≤ a²μ(A) + b²μ(B)` (`(bumpFac − 1)² = a²1_A + b²1_B`). -/
theorem klDiv_bumpFac_le {μ : Measure α} [IsFiniteMeasure μ] (hAB : Disjoint A B) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (ha : 0 ≤ a) (hb : b ≤ 1)
    [IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (bumpFac A B a b x))] :
    klDiv (μ.withDensity fun x => ENNReal.ofReal (bumpFac A B a b x)) μ ≤
      ENNReal.ofReal (a ^ 2 * μ.real A + b ^ 2 * μ.real B) := by
  refine (StatFormal.Wave31tn.RouteKL.klDiv_le_of_withDensity (measurable_bumpFac hA hB)
    (bumpFac_nonneg hAB ha hb) rfl).trans_eq ?_
  have hfun : (fun x => ENNReal.ofReal ((bumpFac A B a b x - 1) ^ 2)) =
      fun x => A.indicator (fun _ => ENNReal.ofReal (a ^ 2)) x + B.indicator (fun _ => ENNReal.ofReal (b ^ 2)) x := by
    funext x
    by_cases hxA : x ∈ A
    · have hxB : x ∉ B := Set.disjoint_left.1 hAB hxA
      simp [bumpFac, hxA, hxB]
    · by_cases hxB : x ∈ B
      · simp [bumpFac, hxA, hxB]
      · simp [bumpFac, hxA, hxB]
  rw [hfun, lintegral_add_left ((measurable_const.indicator hA)), lintegral_indicator_const hA,
    lintegral_indicator_const hB, ← ofReal_measureReal (μ := μ) (s := A), ← ofReal_measureReal (μ := μ) (s := B),
    ← ENNReal.ofReal_mul (sq_nonneg a), ← ENNReal.ofReal_mul (sq_nonneg b),
    ← ENNReal.ofReal_add (mul_nonneg (sq_nonneg a) measureReal_nonneg) (mul_nonneg (sq_nonneg b) measureReal_nonneg)]

/-- `χ²` of the bump with `a = hπ/μ(A)`, `b = hπ/μ(B)`: `a²μ(A) + b²μ(B) ≤ 2h²π`. -/
theorem chiSq_bump_le {π h PA PB : ℝ} (hπ : 0 < π) (hπA : π ≤ PA) (hπB : π ≤ PB) :
    (h * π / PA) ^ 2 * PA + (h * π / PB) ^ 2 * PB ≤ 2 * h ^ 2 * π := by
  have hPA : 0 < PA := hπ.trans_le hπA
  have hPB : 0 < PB := hπ.trans_le hπB
  have e1 : (h * π / PA) ^ 2 * PA = h ^ 2 * π * (π / PA) := by field_simp
  have e2 : (h * π / PB) ^ 2 * PB = h ^ 2 * π * (π / PB) := by field_simp
  have i1 : π / PA ≤ 1 := (div_le_one hPA).2 hπA
  have i2 : π / PB ≤ 1 := (div_le_one hPB).2 hπB
  have hn : 0 ≤ h ^ 2 * π := mul_nonneg (sq_nonneg h) hπ.le
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left i1 hn, mul_le_mul_of_nonneg_left i2 hn]

/-- **The `n`-sample total variation of the bump**: `TV(μ_h^n, μ^n) ≤ h√(nπ)` for `μ_h = bumpFac·μ` with `a = hπ/μ(A)`,
`b = hπ/μ(B)`, `0 < π ≤ min{μ(A), μ(B)}`, `h ∈ [0,1]` (Pinsker, tensorisation, `KL ≤ χ² ≤ 2h²π`). -/
theorem tvDist_pi_bumpFac_le {μ : Measure α} [IsProbabilityMeasure μ] (hAB : Disjoint A B) (hA : MeasurableSet A)
    (hB : MeasurableSet B) {π h : ℝ} (hπ : 0 < π) (hπA : π ≤ μ.real A) (hπB : π ≤ μ.real B) (h0 : 0 ≤ h) (h1 : h ≤ 1)
    [IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (bumpFac A B (h * π / μ.real A) (h * π / μ.real B) x))]
    (n : ℕ) :
    StatFormal.Distances.tvDist
        (Measure.pi fun _ : Fin n => μ.withDensity fun x => ENNReal.ofReal (bumpFac A B (h * π / μ.real A) (h * π / μ.real B) x))
        (Measure.pi fun _ : Fin n => μ) ≤ h * √(n * π) := by
  have hPA : 0 < μ.real A := hπ.trans_le hπA
  have hPB : 0 < μ.real B := hπ.trans_le hπB
  have hb1 : h * π / μ.real B ≤ 1 := by
    rw [div_le_one hPB]; nlinarith
  have hkl := klDiv_bumpFac_le (μ := μ) hAB hA hB (a := h * π / μ.real A) (b := h * π / μ.real B)
    (by positivity) hb1
  set X := (h * π / μ.real A) ^ 2 * μ.real A + (h * π / μ.real B) ^ 2 * μ.real B with hX
  have hX0 : 0 ≤ X := by positivity
  have hX2 : X ≤ 2 * h ^ 2 * π := chiSq_bump_le hπ hπA hπB
  have hne := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  have hle := ENNReal.toReal_le_of_le_ofReal hX0 hkl
  refine (StatFormal.Distances.tvDist_pi_le_sqrt_klDiv _ _ n hne).trans ?_
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc √(n * (klDiv _ μ).toReal / 2) ≤ √(n * (2 * h ^ 2 * π) / 2) :=
        Real.sqrt_le_sqrt (by gcongr; exact hle.trans hX2)
    _ = h * √(n * π) := by
        rw [show (n : ℝ) * (2 * h ^ 2 * π) / 2 = h ^ 2 * (n * π) by ring, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq h0]

/-- **Le Cam's step with an independent randomization**: if `T > t₀` has probability at most `δ` under `μ₀ ⊗ ρ` and
`TV(μ₁, μ₀) ≤ c`, then `T ≤ t₀` has probability at least `1 − δ − c` under `μ₁ ⊗ ρ` (the common factor `ρ` does not increase
the total variation). Adapted from the certified 31tn `RouteS1.lecam_step`. -/
theorem lecam_randomized {β Ξ : Type*} [MeasurableSpace β] [MeasurableSpace Ξ] {μ₀ μ₁ : Measure β}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] (ρ : Measure Ξ) [IsProbabilityMeasure ρ] {T : β × Ξ → ℝ}
    (hT : Measurable T) {t₀ δ c : ℝ} (hval : (μ₀.prod ρ).real {z | t₀ < T z} ≤ δ)
    (hc : StatFormal.Distances.tvDist μ₁ μ₀ ≤ c) : 1 - δ - c ≤ (μ₁.prod ρ).real {z | T z ≤ t₀} := by
  have hA : MeasurableSet {z : β × Ξ | T z ≤ t₀} := measurableSet_le hT measurable_const
  have h0 : 1 - δ ≤ (μ₀.prod ρ).real {z | T z ≤ t₀} := by
    have hcompl : {z : β × Ξ | T z ≤ t₀} = {z | t₀ < T z}ᶜ := by ext z; simp
    rw [hcompl, probReal_compl_eq_one_sub (measurableSet_lt measurable_const hT)]
    linarith
  have h1 := StatFormal.Distances.measureReal_ge_sub_tvDist (μ := μ₁.prod ρ) (ν := μ₀.prod ρ) hA
  have h2 := StatFormal.Distances.tvDist_prod_left_le (μ := μ₁) (ν := μ₀) ρ
  linarith

end StatFormal.LocalLower
