import StatFormal.Lib.Concentration.Rademacher
import TauCeti.Probability.McDiarmid
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Empirical processes over a class: bounded differences and McDiarmid tails

Library component (concentration, part 4). Untrusted library code.

## Setting and measurability device

`g : T → X → ℝ` is a class of measurable functions with `|g t x| ≤ B`; the sample is
`x : Fin n → X` under `Measure.pi (fun _ : Fin n => P)`;
`empDev P g n x t = n⁻¹ ∑ g t (xᵢ) − ∫ g t dP` is `(Pₙ − P) g_t`.

**Device (a): `T` countable** (and nonempty). Then `x ↦ ⨆ t, f t x` is measurable
(`Measurable.iSup`), and all suprema are finite because of the uniform bound. Uncountable classes
are handled downstream by exhibiting a countable `T₀` with the same supremum for every sample
(see `TrimmedClass.lean`).

## Main results

* `mcdiarmid_tail`: generic McDiarmid tail for `F` with bounded differences `c > 0`:
  w.p. `≥ 1 − δ`, `F ≤ E F + c √(n log(1/δ)/2)`;
* `iSup_tail`: the same for `F = ⨆ t, f t` (bounded differences pass to suprema);
* `iSup_abs_empDev_tail` (deliverable 3): w.p. `≥ 1 − δ`,
  `sup_t |(Pₙ − P) g_t| ≤ E sup_t |(Pₙ − P) g_t| + B √(2 log(1/δ)/n)`;
  `iSup_empDev_tail`: the one-sided version.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

namespace StatFormal.Concentration

variable {X : Type*} [MeasurableSpace X]

/-- `(Pₙ − P) g_t` for the sample `x`. -/
def empDev {T : Type*} (P : Measure X) (g : T → X → ℝ) (n : ℕ) (x : Fin n → X) (t : T) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, g t (x i) - ∫ y, g t y ∂P

theorem measurable_empDev {T : Type*} (P : Measure X) {g : T → X → ℝ}
    (hg : ∀ t, Measurable (g t)) (n : ℕ) (t : T) :
    Measurable fun x : Fin n → X => empDev P g n x t :=
  ((Finset.measurable_fun_sum _ fun i _ => (hg t).comp (measurable_pi_apply i)).const_mul
    _).sub_const _

theorem empDev_update_sub {T : Type*} (P : Measure X) (g : T → X → ℝ) {n : ℕ}
    (x : Fin n → X) (i : Fin n) (b : X) (t : T) :
    empDev P g n (Function.update x i b) t - empDev P g n x t =
      (n : ℝ)⁻¹ * (g t b - g t (x i)) := by
  simp only [empDev]
  rw [sub_sub_sub_cancel_right, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Function.update_of_ne hj]
  · simp

theorem abs_empDev_update_sub_le {T : Type*} (P : Measure X) {g : T → X → ℝ} {B : ℝ}
    (hB : ∀ t y, |g t y| ≤ B) {n : ℕ} (x : Fin n → X) (i : Fin n) (b : X) (t : T) :
    |empDev P g n (Function.update x i b) t - empDev P g n x t| ≤ 2 * B / n := by
  rw [empDev_update_sub, abs_mul, abs_inv, Nat.abs_cast, div_eq_inv_mul]
  gcongr
  refine (abs_sub _ _).trans ?_
  linarith [hB t b, hB t (x i)]

theorem abs_empDev_le {T : Type*} (P : Measure X) [IsProbabilityMeasure P] {g : T → X → ℝ}
    {B : ℝ} (hB : ∀ t y, |g t y| ≤ B) {n : ℕ} (x : Fin n → X) (t : T) :
    |empDev P g n x t| ≤ 2 * B := by
  have hB0 : 0 ≤ B := by
    obtain ⟨y⟩ := nonempty_of_isProbabilityMeasure P
    exact (abs_nonneg _).trans (hB t y)
  have h1 : |(n : ℝ)⁻¹ * ∑ i, g t (x i)| ≤ B := by
    rw [abs_mul, abs_inv, Nat.abs_cast]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [hB0]
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
      calc (n : ℝ)⁻¹ * |∑ i, g t (x i)| ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, B := by
            gcongr; exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => hB t _)
        _ = B := by simp [Finset.sum_const]; field_simp
  have h2 : |∫ y, g t y ∂P| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := g t) (C := B)
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hB t y)
    simpa [Real.norm_eq_abs] using this
  simp only [empDev]
  refine (abs_sub _ _).trans ?_
  linarith

/-- Bounded differences pass to suprema. -/
theorem abs_iSup_sub_iSup_le {T : Type*} [Nonempty T] {f g : T → ℝ} {c : ℝ}
    (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g)) (h : ∀ t, |f t - g t| ≤ c) :
    |(⨆ t, f t) - ⨆ t, g t| ≤ c := by
  rw [abs_le]
  constructor
  · have : (⨆ t, g t) ≤ (⨆ t, f t) + c := ciSup_le fun t => by
      have := le_ciSup hf t; have := (abs_le.1 (h t)).1; linarith
    linarith
  · have : (⨆ t, f t) ≤ (⨆ t, g t) + c := ciSup_le fun t => by
      have := le_ciSup hg t; have := (abs_le.1 (h t)).2; linarith
    linarith

variable {β : Type*} [MeasurableSpace β]

/-- **Generic McDiarmid tail.** If `F` has bounded differences `c > 0`, then with probability at
least `1 − δ` (`0 < δ ≤ 1`), `F ≤ E F + c √(n log(1/δ)/2)`. -/
theorem mcdiarmid_tail (ν : Measure β) [IsProbabilityMeasure ν] {n : ℕ} (hn : n ≠ 0)
    (F : (Fin n → β) → ℝ) (hF : Measurable F) {c : ℝ} (hc : 0 < c)
    (hosc : ∀ x i b, |F (Function.update x i b) - F x| ≤ c) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin n => ν).real
      {x | F x ≤ (∫ y, F y ∂Measure.pi fun _ : Fin n => ν) + c * √(n * log (1 / δ) / 2)} := by
  set Pn := Measure.pi fun _ : Fin n => ν
  set E := ∫ y, F y ∂Pn
  set ε := c * √(n * log (1 / δ) / 2) with hε
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hL : 0 ≤ log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hε0 : 0 ≤ ε := by positivity
  set Bad := {x | E + ε < F x} with hBad
  have hBm : MeasurableSet Bad := measurableSet_lt measurable_const hF
  have hcompl : {x | F x ≤ E + ε} = Badᶜ := by ext x; simp [hBad, not_lt]
  rw [hcompl, probReal_compl_eq_one_sub hBm]
  suffices Pn.real Bad ≤ δ by linarith
  have hsub : Bad ⊆ {x | ε ≤ F x - E} := by
    intro x hx
    simp only [hBad, Set.mem_ofPred_eq] at hx ⊢
    linarith
  have htail := (TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences_fin ν F hF c
    hosc).measure_ge_le hε0
  have hcoe : (((n : ℝ≥0) * (c.toNNReal / 2) ^ 2 : ℝ≥0) : ℝ) = n * c ^ 2 / 4 := by
    push_cast [Real.coe_toNNReal _ hc.le]; ring
  rw [hcoe] at htail
  have hexp : -ε ^ 2 / (2 * (n * c ^ 2 / 4)) = -log (1 / δ) := by
    rw [hε, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  rw [hexp, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv] at htail
  exact (measureReal_mono hsub).trans htail

/-- McDiarmid tail for a supremum over a countable class with uniformly bounded differences. -/
theorem iSup_tail (ν : Measure β) [IsProbabilityMeasure ν] {T : Type*} [Countable T]
    [Nonempty T] {n : ℕ} (hn : n ≠ 0) (f : T → (Fin n → β) → ℝ) (hf : ∀ t, Measurable (f t))
    {C : ℝ} (hC : ∀ t x, |f t x| ≤ C) {c : ℝ} (hc : 0 < c)
    (hosc : ∀ t x i b, |f t (Function.update x i b) - f t x| ≤ c) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin n => ν).real
      {x | ⨆ t, f t x ≤ (∫ y, ⨆ t, f t y ∂Measure.pi fun _ : Fin n => ν) +
        c * √(n * log (1 / δ) / 2)} :=
  mcdiarmid_tail ν hn (fun x => ⨆ t, f t x) (Measurable.iSup hf) hc
    (fun x i b => abs_iSup_sub_iSup_le (bddAbove_of_abs_le fun t => hC t _)
      (bddAbove_of_abs_le fun t => hC t _) fun t => hosc t x i b) hδ0 hδ1

theorem two_mul_div_mul_sqrt {B L : ℝ} {n : ℕ} (hn : n ≠ 0) (hL : 0 ≤ L) :
    2 * B / n * √(n * L / 2) = B * √(2 * L / n) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have : 2 * L / n = (2 / n) ^ 2 * (n * L / 2) := by field_simp
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  ring

/-- **Deliverable 3 (two-sided)**: for a countable class with `|g t| ≤ B`, `B > 0`, with
probability `≥ 1 − δ`, `sup_t |(Pₙ − P)g_t| ≤ E sup_t |(Pₙ − P)g_t| + B √(2 log(1/δ)/n)`. -/
theorem iSup_abs_empDev_tail (P : Measure X) [IsProbabilityMeasure P] {T : Type*} [Countable T]
    [Nonempty T] {g : T → X → ℝ} (hg : ∀ t, Measurable (g t)) {B : ℝ} (hB : ∀ t y, |g t y| ≤ B)
    (hBpos : 0 < B) {n : ℕ} (hn : n ≠ 0) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin n => P).real
      {x | ⨆ t, |empDev P g n x t| ≤
        (∫ y, ⨆ t, |empDev P g n y t| ∂Measure.pi fun _ : Fin n => P) +
          B * √(2 * log (1 / δ) / n)} := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hL : 0 ≤ log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have h := iSup_tail P hn (fun t x => |empDev P g n x t|)
    (fun t => (measurable_empDev P hg n t).norm) (C := 2 * B)
    (fun t x => by rw [abs_abs]; exact abs_empDev_le P hB x t) (c := 2 * B / n)
    (by positivity) (fun t x i b => (abs_abs_sub_abs_le _ _).trans
      (abs_empDev_update_sub_le P hB x i b t)) hδ0 hδ1
  rwa [two_mul_div_mul_sqrt hn hL] at h

/-- One-sided version of `iSup_abs_empDev_tail`. -/
theorem iSup_empDev_tail (P : Measure X) [IsProbabilityMeasure P] {T : Type*} [Countable T]
    [Nonempty T] {g : T → X → ℝ} (hg : ∀ t, Measurable (g t)) {B : ℝ} (hB : ∀ t y, |g t y| ≤ B)
    (hBpos : 0 < B) {n : ℕ} (hn : n ≠ 0) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin n => P).real
      {x | ⨆ t, empDev P g n x t ≤
        (∫ y, ⨆ t, empDev P g n y t ∂Measure.pi fun _ : Fin n => P) +
          B * √(2 * log (1 / δ) / n)} := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hL : 0 ≤ log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have h := iSup_tail P hn (fun t x => empDev P g n x t)
    (fun t => measurable_empDev P hg n t) (C := 2 * B)
    (fun t x => abs_empDev_le P hB x t) (c := 2 * B / n)
    (by positivity) (fun t x i b => abs_empDev_update_sub_le P hB x i b t) hδ0 hδ1
  rwa [two_mul_div_mul_sqrt hn hL] at h

end StatFormal.Concentration
