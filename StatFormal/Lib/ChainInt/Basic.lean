import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Step functions on a grid (untrusted helper for `thm:cert-chain`, `Γ_int`)

For a grid `s : Fin (S + 1) → ℝ` with `s 0 = 0`, the cells `[s_g, s_{g+1})` (the last one `[s_S, ∞)`) cover
`[0, ∞)`; `stepH s c = Σ_g c_g 𝟏_{cell g}`. For `c ≥ 0`, `a ≥ 0`, `a ≤ T'`:
`a ∫_0^1 stepH(a t) dt ≤ Σ_g c_g max(0, min(s_{g+1}, T') − max(s_g, 0))` (with `min(∞, T') = T'`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.Foundations.ChainInt

variable {S : ℕ}

/-- The cell `[s_g, s_{g+1})`, `[s_S, ∞)` for the last grid point. -/
def cell (s : Fin (S + 1) → ℝ) (g : Fin (S + 1)) : Set ℝ :=
  if h : (g : ℕ) + 1 < S + 1 then Ico (s g) (s ⟨(g : ℕ) + 1, h⟩) else Ici (s g)

/-- `Σ_g c_g 𝟏_{cell g}`. -/
def stepH (s : Fin (S + 1) → ℝ) (c : Fin (S + 1) → ℝ) (v : ℝ) : ℝ :=
  ∑ g, c g * (cell s g).indicator 1 v

/-- `max(0, min(s_{g+1}, T) − max(s_g, 0))`, `s_{S+1} = ∞` (the same expression as the draft's `segLen`). -/
def segL (s : Fin (S + 1) → ℝ) (t : ℝ) (g : Fin (S + 1)) : ℝ :=
  max 0 (min (if h : (g : ℕ) + 1 < S + 1 then s ⟨(g : ℕ) + 1, h⟩ else t) t - max (s g) 0)

variable {s : Fin (S + 1) → ℝ} {c : Fin (S + 1) → ℝ}

lemma measurableSet_cell (g : Fin (S + 1)) : MeasurableSet (cell s g) := by
  unfold cell; split_ifs
  · exact measurableSet_Ico
  · exact measurableSet_Ici

lemma measurable_stepH : Measurable (stepH s c) :=
  Finset.measurable_sum _ fun g _ => (measurable_const.indicator (measurableSet_cell g)).const_mul _

lemma abs_term_le (g : Fin (S + 1)) (v : ℝ) : |c g * (cell s g).indicator 1 v| ≤ |c g| := by
  rw [abs_mul]
  by_cases hv : v ∈ cell s g
  · simp [Set.indicator_of_mem hv]
  · simp [Set.indicator_of_notMem hv]

lemma abs_stepH_le (v : ℝ) : |stepH s c v| ≤ ∑ g, |c g| := by
  unfold stepH
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun g _ => abs_term_le g v)

lemma stepH_nonneg (hc : ∀ g, 0 ≤ c g) (v : ℝ) : 0 ≤ stepH s c v :=
  Finset.sum_nonneg fun g _ => mul_nonneg (hc g) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

lemma le_stepH (hc : ∀ g, 0 ≤ c g) {v : ℝ} {g0 : Fin (S + 1)} (hv : v ∈ cell s g0) : c g0 ≤ stepH s c v := by
  unfold stepH
  have := Finset.single_le_sum (f := fun g => c g * (cell s g).indicator 1 v)
    (fun g _ => mul_nonneg (hc g) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) (Finset.mem_univ g0)
  simpa [Set.indicator_of_mem hv] using this

/-- The cells cover `[0, ∞)` when `s_0 = 0`. -/
lemma exists_cell (hs0 : s 0 = 0) {v : ℝ} (hv : 0 ≤ v) : ∃ g, s g ≤ v ∧ v ∈ cell s g := by
  set F := Finset.univ.filter (fun g : Fin (S + 1) => s g ≤ v) with hFdef
  have hF : F.Nonempty := ⟨0, by simp [F, hs0, hv]⟩
  have hg0 : s (F.max' hF) ≤ v := (Finset.mem_filter.1 (F.max'_mem hF)).2
  refine ⟨F.max' hF, hg0, ?_⟩
  unfold cell
  split_ifs with h
  · refine ⟨hg0, ?_⟩
    by_contra hle
    push Not at hle
    have hm : (⟨(F.max' hF : ℕ) + 1, h⟩ : Fin (S + 1)) ∈ F := by simp [F, hle]
    have := F.le_max' _ hm
    rw [Fin.le_def] at this
    simp at this
  · exact hg0

lemma integrableOn_of_bdd {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ x, |f x| ≤ C) {A : Set ℝ}
    (hA : volume A ≠ ⊤) : IntegrableOn f A :=
  Measure.integrableOn_of_bounded hA hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)

lemma integrableOn_stepH_comp (a : ℝ) {A : Set ℝ} (hA : volume A ≠ ⊤) :
    IntegrableOn (fun t => stepH s c (a * t)) A :=
  integrableOn_of_bdd (measurable_stepH.comp (measurable_const.mul measurable_id))
    (fun t => abs_stepH_le (a * t)) hA

lemma intervalIntegrable_stepH_comp (a x y : ℝ) :
    IntervalIntegrable (fun t => stepH s c (a * t)) volume x y :=
  (intervalIntegrable_iff).2 (integrableOn_stepH_comp a (by simp [Real.volume_uIoc]))

lemma integral_stepH_le (hc : ∀ g, 0 ≤ c g) {T T' : ℝ} (hT : 0 ≤ T) (hTT : T ≤ T') :
    ∫ v in (0 : ℝ)..T, stepH s c v ≤ ∑ g, c g * segL s T' g := by
  rw [intervalIntegral.integral_of_le hT]
  unfold stepH
  rw [integral_finsetSum _ (fun g _ => ?_)]
  · refine Finset.sum_le_sum fun g _ => ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (hc g)
    rw [integral_indicator_one (measurableSet_cell g), measureReal_restrict_apply (measurableSet_cell g)]
    have hsub : cell s g ∩ Ioc 0 T ⊆
        Icc (max (s g) 0) (min (if h : (g : ℕ) + 1 < S + 1 then s ⟨(g : ℕ) + 1, h⟩ else T') T') := by
      intro x ⟨hx1, hx2⟩
      obtain ⟨hx0, hxT⟩ := hx2
      unfold cell at hx1
      split_ifs at hx1 ⊢ with h
      · obtain ⟨h1, h2⟩ := hx1
        exact ⟨max_le h1 hx0.le, le_min h2.le (hxT.trans hTT)⟩
      · exact ⟨max_le hx1 hx0.le, le_min (hxT.trans hTT) (hxT.trans hTT)⟩
    refine (measureReal_mono hsub (by simp)).trans ?_
    rw [Real.volume_real_Icc]
    unfold segL
    rw [max_comm]
  · exact (integrableOn_of_bdd (C := |c g|)
      ((measurable_const.indicator (measurableSet_cell g)).const_mul _)
      (fun v => abs_term_le g v) (by simp)).integrable

lemma segL_nonneg (t : ℝ) (g : Fin (S + 1)) : 0 ≤ segL s t g := le_max_left _ _

/-- `a ∫_0^1 stepH(a t) dt ≤ Σ_g c_g segL(T')` for `0 ≤ a ≤ T'`, `c ≥ 0`. -/
lemma mul_integral_stepH_comp_le (hc : ∀ g, 0 ≤ c g) {a T' : ℝ} (ha : 0 ≤ a) (haT : a ≤ T') :
    a * ∫ t in (0 : ℝ)..1, stepH s c (a * t) ≤ ∑ g, c g * segL s T' g := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h, zero_mul]
    exact Finset.sum_nonneg fun g _ => mul_nonneg (hc g) (segL_nonneg _ _)
  · rw [intervalIntegral.integral_comp_mul_left (fun v => stepH s c v) h.ne', mul_zero, mul_one, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ h.ne', one_mul]
    exact integral_stepH_le hc ha haT

end StatFormal.Foundations.ChainInt
