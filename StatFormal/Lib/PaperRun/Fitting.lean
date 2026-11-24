import StatFormal.Lib.PaperRun.QPMeas
import StatFormal.Wave30tz.RouteElem

/-!
# Fitting samples, ramps and the fractions `eq:fractions` (library)

Library component (untrusted).

* `measurable_fitSample`, `fitSample_congr`: the fitting sample of batch `b` (`Wave30tz.fitSample`, the observations of the batches
  before `b` in index order) is a measurable function of the sample and depends only on the observations with label `< b`;
* `ramp_apply`, `ramp_mem_Icc`: the ramp `(clip f − u)/(t − u)` takes values in `[0,1]` when `u < t`;
* `measurable_fracFormula`, `fracFormula_nonneg`, `fracFormula_le_cap`, `fracFormula_le_lamHi`: the fraction of `eq:fractions` with
  indicator weights (`Wave31tr.fracFormula`) is measurable in the prior, the indicators and the past, lies in
  `[0, λ_max/(1+α)]`, and below `λ̄_N` (floor `v²_min > 0`);
* `fracFormula_indicator`: with the indicator weights of a set `S` of earlier pairs it is the `S`-form of the certified
  `Wave30tz.fractions_bounds`, hence `lamLo_le_fracFormula`: above `λ_N` for pasts in `[−1,1]`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Finset

namespace StatFormal.PaperRun

open StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.Wave31tr

section Fit

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The fitting sample is a measurable function of the sample (a coordinate selection). -/
theorem measurable_fitSample {p : ℕ} (l : Fin p → ℕ) (b : ℕ) : Measurable fun x : Fin p → 𝒳 => fitSample l b x :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- The fitting sample of batch `b` depends only on the observations with label `< b`. -/
theorem fitSample_congr {p : ℕ} (l : Fin p → ℕ) (b : ℕ) {x x' : Fin p → 𝒳} (h : ∀ i, l i < b → x i = x' i) :
    fitSample l b x = fitSample l b x' := by
  classical
  funext k
  unfold fitSample
  apply h
  have := Finset.orderEmbOfFin_mem (Finset.univ.filter fun i => l i < b) rfl k
  exact (Finset.mem_filter.mp this).2

end Fit

/-- The ramp, unfolded. -/
theorem ramp_apply {𝒳 : Type*} (f : 𝒳 → ℝ) (t u : ℝ) (z : 𝒳) :
    ramp f t u z = (min (max (f z) u) t - u) / (t - u) := rfl

/-- The ramp between `u < t` takes values in `[0,1]`. -/
theorem ramp_mem_Icc {𝒳 : Type*} (f : 𝒳 → ℝ) {t u : ℝ} (h : u < t) (z : 𝒳) : ramp f t u z ∈ Icc (0 : ℝ) 1 := by
  rw [ramp_apply]
  have h1 : u ≤ min (max (f z) u) t := le_min (le_max_right _ _) h.le
  have h2 : min (max (f z) u) t ≤ t := min_le_right _ _
  have hpos : 0 < t - u := by linarith
  exact ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).mpr (by linarith)⟩

section Frac

variable (lmax α L : ℝ) (N : ℕ) (s2 w0 : ℝ)

/-- The fraction formula is measurable in the prior, the indicator weights and the past. -/
theorem measurable_fracFormula {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {s0 : Ω → ℝ} {e z : Ω → Fin k → ℝ}
    (hs0 : Measurable s0) (he : Measurable e) (hz : Measurable z) :
    Measurable fun ω => fracFormula lmax α L N s2 w0 (s0 ω) (e ω) (z ω) := by
  unfold fracFormula
  simp only [← Finset.sum_filter]
  fun_prop

theorem fracFormula_nonneg {lmax α : ℝ} (hl : 0 ≤ lmax) (hα : 0 ≤ α) {k : ℕ} (s0 : ℝ) (e z : Fin k → ℝ) :
    0 ≤ fracFormula lmax α L N s2 w0 s0 e z :=
  le_min (div_nonneg hl (by linarith)) (Real.sqrt_nonneg _)

theorem fracFormula_le_cap {k : ℕ} (s0 : ℝ) (e z : Fin k → ℝ) :
    fracFormula lmax α L N s2 w0 s0 e z ≤ lmax / (1 + α) := min_le_left _ _

/-- The fraction is at most `λ̄_N` (the floor `max(v²_min, ·) ≥ v²_min > 0`), for every past. -/
theorem fracFormula_le_lamHi {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 1 ≤ N) {s2 : ℝ} (hs2 : 0 < s2) {k : ℕ} (s0 : ℝ)
    (e z : Fin k → ℝ) : fracFormula lmax α L N s2 w0 s0 e z ≤ lamHi lmax α L s2 N := by
  unfold fracFormula lamHi
  refine min_le_min le_rfl (Real.sqrt_le_sqrt ?_)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  exact div_le_div_of_nonneg_left (by linarith) (mul_pos hN' hs2) (mul_le_mul_of_nonneg_left (le_max_left _ _) hN'.le)

/-- `Σ_i 1{i ∈ S} f_i = Σ_{i ∈ S} f_i`. -/
theorem sum_indicator_mul {k : ℕ} (S : Finset (Fin k)) (f : Fin k → ℝ) :
    ∑ i, (if i ∈ S then (1 : ℝ) else 0) * f i = ∑ i ∈ S, f i := by
  calc ∑ i, (if i ∈ S then (1 : ℝ) else 0) * f i = ∑ i, if i ∈ S then f i else 0 :=
        Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    _ = ∑ i ∈ Finset.univ ∩ S, f i := Finset.sum_ite_mem _ _ _
    _ = ∑ i ∈ S, f i := by rw [Finset.univ_inter]

/-- `Σ_i 1{i ∈ S} = |S|`. -/
theorem sum_indicator_one {k : ℕ} (S : Finset (Fin k)) : ∑ i, (if i ∈ S then (1 : ℝ) else 0) = S.card := by
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- With the indicator weights of a set `S` of earlier pairs, the fraction is the `S`-form of `eq:fractions` (sums and counts over
the pairs bet on), as in the certified `Wave30tz.fractions_bounds`. -/
theorem fracFormula_indicator {k : ℕ} (s0 : ℝ) (S : Finset (Fin k)) (z : Fin k → ℝ) :
    fracFormula lmax α L N s2 w0 s0 (fun l => if l ∈ S then 1 else 0) z =
      min (lmax / (1 + α)) (√(2 * L / (N * max s2 ((w0 * s0 + ∑ i ∈ S, (z i - α - (∑ l ∈ S.filter (· < i), (z l - α)) /
        (w0 + (S.filter (· < i)).card)) ^ 2) / (w0 + S.card))))) := by
  unfold fracFormula
  have hnum : ∀ i : Fin k, (∑ l, if l < i then (if l ∈ S then (1 : ℝ) else 0) * (z l - α) else 0) =
      ∑ l ∈ S.filter (· < i), (z l - α) := fun i => by
    rw [Finset.sum_filter, ← sum_indicator_mul S]
    exact Finset.sum_congr rfl fun l _ => by split_ifs <;> simp
  have hden : ∀ i : Fin k, (∑ l, if l < i then (if l ∈ S then (1 : ℝ) else 0) else 0) =
      ((S.filter (· < i)).card : ℝ) := fun i => by
    rw [← Finset.sum_boole, ← sum_indicator_mul S]
    exact Finset.sum_congr rfl fun l _ => by split_ifs <;> simp
  simp only [hnum, hden]
  rw [sum_indicator_mul S, sum_indicator_one S]

/-- **Lower fraction bound** (from the certified `Wave30tz.fractions_bounds`): with indicator weights of any set `S`, `w₀ > 0`, prior
`s₀ ∈ [0,4]`, `α ∈ [0,1)`, `v²_min > 0`, `L ≥ 0` and a past in `[−1,1]`, the fraction is at least `λ_N`. -/
theorem lamLo_le_fracFormula {k : ℕ} (s0 : ℝ) (S : Finset (Fin k)) (z : Fin k → ℝ) (hw0 : 0 < w0) (hs00 : 0 ≤ s0)
    (hs04 : s0 ≤ 4) (hα0 : 0 ≤ α) (hα1 : α < 1) (hz : ∀ i, z i ∈ Icc (-1 : ℝ) 1) (hs2 : 0 < s2) (hL : 0 ≤ L) :
    lamLo lmax α L s2 N ≤ fracFormula lmax α L N s2 w0 s0 (fun l => if l ∈ S then 1 else 0) z := by
  rw [fracFormula_indicator]
  exact ((fractions_bounds_route k z S w0 s0 α s2 lmax L N hw0 hs00 hs04 hα0 hα1 hz hs2 hL).2.2 _ rfl).2.2.1

end Frac

end StatFormal.PaperRun
