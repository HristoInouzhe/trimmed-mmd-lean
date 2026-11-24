import StatFormal.Lib.FnCert.Level
import StatFormal.Lib.PaperRun.Fitting

set_option linter.style.longLine false

/-!
# The betting error of the certificate: the constant and the fractions (library)

Library component (untrusted).

* `epsN_le_of_C`: Lemma 5's tail `ε_N(ϱ)` (`Wave30tz.epsN`) at the excess `ϱ = C N^{−1/2}` does not depend on `N`
  (`ϱ√(NL/2) = C√(L/2)`), and it is at most `ε` once `C√(L/2) ≥ L + 16L/σ²_min + √((4L/σ²_min) log(1/ε))` (any `α ∈ [0,1)`);
* `betC`, `betC_spec`: such a constant depending only on `δ`, `η`, `J`, `σ²_min` (with `ε = η/(J+1)`), also `≥ √(8L)` so that
  `C N^{−1/2} < 1` forces `N > 8L`, the sample-size condition of the certified `Wave30tz.bet_power_frac` at `λ_max = 1/2`;
* `ge_of_measure_compl_le`: `P(Eᶜ) ≤ η` gives `P(E) ≥ 1 − η`;
* `isFracRule_frozen`, `rejects_frozen_iff`: admissible fractions stay admissible with batch 0 frozen at `(x₀, y₀)`, and the
  certificate with frozen fractions at `(x, y)` is the certificate at `(withBatchZero x₀ x, withBatchZero y₀ y)` (for a fixed ramp);
* `isFracRule_fracFormula`: the fractions of `eq:fractions` with every pair bet on (`Wave31tr.fracFormula`, a prior rule `v₀`) are
  admissible with cap `λ_max`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.FnCert

open StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tp

/-- Lemma 5's tail at the excess `C/√N` is at most `ε` for a large enough `C` (independent of `N`). -/
theorem epsN_le_of_C {s2 α L C ε : ℝ} {N : ℕ} (hs2 : 0 < s2) (hL : 0 < L) (hα0 : 0 ≤ α) (hα1 : α < 1) (hN : 1 ≤ N)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hC : L + 16 * L / s2 + √(4 * L / s2 * Real.log (1 / ε)) ≤ C * √(L / 2)) :
    epsN s2 α L N (C / √(N : ℝ)) ≤ ε := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < √(N : ℝ) := Real.sqrt_pos.2 hNpos
  have hkey : C / √(N : ℝ) * √(N * L / 2) = C * √(L / 2) := by
    rw [show (N : ℝ) * L / 2 = N * (L / 2) by ring, Real.sqrt_mul hNpos.le]
    field_simp
  have hlog : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε0]; linarith)
  set Y := √(4 * L / s2 * Real.log (1 / ε)) with hY
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hC4 : 4 * L * (1 + α) ^ 2 / s2 ≤ 16 * L / s2 := by
    apply div_le_div_of_nonneg_right _ hs2.le
    have : (1 + α) ^ 2 ≤ 4 := by nlinarith
    nlinarith
  have hX : Y ≤ C / √(N : ℝ) * √(N * L / 2) - L - 4 * L * (1 + α) ^ 2 / s2 := by rw [hkey]; linarith
  have hmax : Y ≤ max (C / √(N : ℝ) * √(N * L / 2) - L - 4 * L * (1 + α) ^ 2 / s2) 0 := hX.trans (le_max_left _ _)
  have hsq : Y ^ 2 ≤ (max (C / √(N : ℝ) * √(N * L / 2) - L - 4 * L * (1 + α) ^ 2 / s2) 0) ^ 2 :=
    pow_le_pow_left₀ hY0 hmax 2
  have hY2 : Y ^ 2 = 4 * L / s2 * Real.log (1 / ε) := Real.sq_sqrt (by positivity)
  have hk : 0 ≤ s2 / (4 * L) := by positivity
  have hprod : Real.log (1 / ε) ≤
      s2 / (4 * L) * (max (C / √(N : ℝ) * √(N * L / 2) - L - 4 * L * (1 + α) ^ 2 / s2) 0) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hsq hk
    rw [hY2] at h1
    have e : s2 / (4 * L) * (4 * L / s2 * Real.log (1 / ε)) = Real.log (1 / ε) := by field_simp
    linarith
  unfold epsN
  calc Real.exp (-(s2 / (4 * L)) * (max (C / √(N : ℝ) * √(N * L / 2) - L - 4 * L * (1 + α) ^ 2 / s2) 0) ^ 2)
      ≤ Real.exp (-Real.log (1 / ε)) := Real.exp_le_exp.2 (by linarith)
    _ = ε := by rw [Real.log_div one_ne_zero hε0.ne', Real.log_one, zero_sub, neg_neg, Real.exp_log hε0]

/-- The betting constant: `max{√(8L), (L + 16L/σ²_min + √((4L/σ²_min) log((J+1)/η)))/√(L/2)}`, `L = log(1/δ)`. -/
def betC (δ η s2 : ℝ) (J : ℕ) : ℝ :=
  max (√(8 * Real.log (1 / δ)))
    ((Real.log (1 / δ) + 16 * Real.log (1 / δ) / s2 +
        √(4 * Real.log (1 / δ) / s2 * Real.log (1 / (η / ((J : ℝ) + 1))))) / √(Real.log (1 / δ) / 2))

theorem betC_spec {δ η s2 : ℝ} (J : ℕ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ betC δ η s2 J ∧ √(8 * Real.log (1 / δ)) ≤ betC δ η s2 J ∧
      Real.log (1 / δ) + 16 * Real.log (1 / δ) / s2 + √(4 * Real.log (1 / δ) / s2 * Real.log (1 / (η / ((J : ℝ) + 1)))) ≤
        betC δ η s2 J * √(Real.log (1 / δ) / 2) := by
  have hL : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hs : 0 < √(Real.log (1 / δ) / 2) := Real.sqrt_pos.2 (by positivity)
  refine ⟨(Real.sqrt_nonneg _).trans (le_max_left _ _), le_max_left _ _, ?_⟩
  have h := mul_le_mul_of_nonneg_right (le_max_right (√(8 * Real.log (1 / δ)))
    ((Real.log (1 / δ) + 16 * Real.log (1 / δ) / s2 +
        √(4 * Real.log (1 / δ) / s2 * Real.log (1 / (η / ((J : ℝ) + 1))))) / √(Real.log (1 / δ) / 2))) hs.le
  rw [div_mul_cancel₀ _ hs.ne'] at h
  exact h

/-- `P(Eᶜ) ≤ η` gives `P(E) ≥ 1 − η` (probability measure, measurable `E`). -/
theorem ge_of_measure_compl_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {E : Set Ω}
    (hE : MeasurableSet E) {η : ℝ} (hη : 0 ≤ η) (h : μ Eᶜ ≤ ENNReal.ofReal η) : ENNReal.ofReal (1 - η) ≤ μ E := by
  have h1 : μ E = 1 - μ Eᶜ := by rw [prob_compl_eq_one_sub hE, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  rw [h1, ENNReal.ofReal_sub _ hη, ENNReal.ofReal_one]
  exact tsub_le_tsub_left h 1

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {n m N : ℕ}
  {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)} {B : Fin N → Finset (Fin m)}

/-- Admissible fractions stay admissible with batch 0 frozen at `(x₀, y₀)`. -/
theorem isFracRule_frozen {α c : ℝ} {lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}
    (hlam : IsFracRule lx ly bat α c lam) (x₀ : Fin n → 𝒳) (y₀ : Fin m → 𝒳) :
    IsFracRule lx ly bat α c (fun k x y => lam k (withBatchZero lx x₀ x) (withBatchZero ly y₀ y)) := by
  have hlamB : IsBatchBetRule (U := Unit) lx ly bat α c (fun k _ => lam k) := hlam
  have hφ : Measurable fun p : Unit × ((Fin n → 𝒳) × (Fin m → 𝒳)) =>
      ((((), (withBatchZero lx x₀ p.2.1, withBatchZero ly y₀ p.2.2)) : Unit × ((Fin n → 𝒳) × (Fin m → 𝒳)))) :=
    measurable_const.prodMk (((measurable_withBatchZero lx x₀).comp measurable_snd.fst).prodMk
      ((measurable_withBatchZero ly y₀).comp measurable_snd.snd))
  intro k
  exact ⟨(hlamB k).1.comp ((hφ.comp measurable_fst).prodMk measurable_snd), fun _ x y z => (hlamB k).2.1 () _ _ z,
    fun _ x x' y y' hx hy => (hlamB k).2.2 () _ _ _ _ (withBatchZero_agree hx) (withBatchZero_agree hy)⟩

omit [MeasurableSpace 𝒳] in
/-- The certificate with frozen fractions at `(x, y)` is the certificate at `(withBatchZero x₀ x, withBatchZero y₀ y)`, for a fixed
ramp `f`. -/
theorem rejects_frozen_iff (hpair : IsBatchPairing lx ly bat A B) {α δ : ℝ}
    {lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ} (f : 𝒳 → ℝ) (x₀ x : Fin n → 𝒳) (y₀ y : Fin m → 𝒳) :
    rejects (fun k x y => lam k (withBatchZero lx x₀ x) (withBatchZero ly y₀ y)) (fun _ _ _ => f) bat A B α δ x y ↔
      rejects lam (fun _ _ _ => f) bat A B α δ (withBatchZero lx x₀ x) (withBatchZero ly y₀ y) := by
  have e : seqZ (U := Unit) (fun _ _ _ _ => f) bat A B () (withBatchZero lx x₀ x) (withBatchZero ly y₀ y) =
      seqZ (U := Unit) (fun _ _ _ _ => f) bat A B () x y := by
    funext k
    exact pairZ_withBatchZero hpair f k x₀ x y₀ y
  change betReject (fun k => lam k (withBatchZero lx x₀ x) (withBatchZero ly y₀ y)) α δ
      (seqZ (U := Unit) (fun _ _ _ _ => f) bat A B () x y) ↔
    betReject (fun k => lam k (withBatchZero lx x₀ x) (withBatchZero ly y₀ y)) α δ
      (seqZ (U := Unit) (fun _ _ _ _ => f) bat A B () (withBatchZero lx x₀ x) (withBatchZero ly y₀ y))
  rw [e]

/-- The fractions of `eq:fractions` with every pair bet on (a prior rule `v₀`, a function of the earlier batches, valued in
`[0,4]`) are admissible at level `α ≥ 0` with cap `λ_max ≥ 0`. -/
theorem isFracRule_fracFormula {lmax α L s2 w0 : ℝ} (hl : 0 ≤ lmax) (hα : 0 ≤ α)
    {s0 : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ}
    (hs0m : ∀ b, Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => s0 b p.1 p.2)
    (hs0d : ∀ b x x' y y', (∀ i, lx i < b → x i = x' i) → (∀ j, ly j < b → y j = y' j) → s0 b x y = s0 b x' y')
    {lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}
    (heq : ∀ (k : Fin N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : Fin k → ℝ),
      lam k x y z = StatFormal.Wave31tr.fracFormula lmax α L N s2 w0 (s0 (bat k) x y) (fun _ => 1) z) :
    IsFracRule lx ly bat α lmax lam := by
  intro k
  have e : (fun p : (Unit × ((Fin n → 𝒳) × (Fin m → 𝒳))) × (Fin k → ℝ) => lam k p.1.2.1 p.1.2.2 p.2) =
      fun p => StatFormal.Wave31tr.fracFormula lmax α L N s2 w0 (s0 (bat k) p.1.2.1 p.1.2.2) (fun _ => 1) p.2 :=
    funext fun p => heq k _ _ _
  refine ⟨?_, fun _ x y z => ?_, fun _ x x' y y' hx hy => ?_⟩
  · change Measurable (fun p : (Unit × ((Fin n → 𝒳) × (Fin m → 𝒳))) × (Fin k → ℝ) => lam k p.1.2.1 p.1.2.2 p.2)
    rw [e]
    exact PaperRun.measurable_fracFormula lmax α L N s2 w0 ((hs0m (bat k)).comp (measurable_snd.comp measurable_fst))
      measurable_const measurable_snd
  · change 0 ≤ lam k x y z ∧ lam k x y z ≤ lmax / (1 + α)
    rw [heq k x y z]
    exact ⟨PaperRun.fracFormula_nonneg L N s2 w0 hl hα _ _ _, PaperRun.fracFormula_le_cap lmax α L N s2 w0 _ _ _⟩
  · change lam k x y = lam k x' y'
    funext z
    rw [heq k x y z, heq k x' y' z, hs0d (bat k) x x' y y' hx hy]

end StatFormal.FnCert
