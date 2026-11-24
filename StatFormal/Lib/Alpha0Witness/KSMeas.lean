import StatFormal.Wave30tz.Statements
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measurability of `KS⁺` of a jointly measurable family (library)

Library component (untrusted). `KS⁺_{P,Q}(f) = sup_{x ∈ ℝ} {P(f > x) − Q(f > x)}` (`Wave30tz.ksPlus`), `P, Q` finite measures.

* `bddAbove_tail_sub`: the tail differences are bounded above by `P(univ)`;
* `tendsto_measureReal_lt`: right-continuity of `x ↦ P(f > x)` (continuity of measure from below along `{f > x + 1/(k+1)}`);
* `ksPlus_eq_iSup_rat`: for measurable `f`, `KS⁺(f)` is the supremum over the rationals (squeeze each real `x` from the right by
  rationals `r_k ∈ (x, x + 1/(k+1))`);
* `measurable_ksPlus`: **`ω ↦ KS⁺_{P,Q}(F ω)` is measurable** when `(ω, z) ↦ F ω z` is jointly measurable (each `ω ↦ P(F ω > q)`
  is measurable by `measurable_measure_prodMk_left`; countable supremum, `Measurable.iSup`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Alpha0Witness

open StatFormal.Wave30tz

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- `P(f > x) − Q(f > x) ≤ P(univ)`. -/
theorem tail_sub_le (P Q : Measure 𝒳) [IsFiniteMeasure P] (f : 𝒳 → ℝ) (x : ℝ) :
    P.real {z | x < f z} - Q.real {z | x < f z} ≤ P.real univ := by
  have h1 : P.real {z | x < f z} ≤ P.real univ := measureReal_mono (subset_univ _)
  have h2 : 0 ≤ Q.real {z | x < f z} := measureReal_nonneg
  linarith

/-- The tail differences are bounded above, along any family of levels. -/
theorem bddAbove_tail_sub (P Q : Measure 𝒳) [IsFiniteMeasure P] (f : 𝒳 → ℝ) {ι : Type*} (r : ι → ℝ) :
    BddAbove (range fun i => P.real {z | r i < f z} - Q.real {z | r i < f z}) :=
  ⟨P.real univ, by rintro _ ⟨i, rfl⟩; exact tail_sub_le P Q f (r i)⟩

/-- **Right-continuity of the tail**: `P(f > x + 1/(k+1)) → P(f > x)` (no measurability needed). -/
theorem tendsto_measureReal_lt (P : Measure 𝒳) [IsFiniteMeasure P] (f : 𝒳 → ℝ) (x : ℝ) :
    Tendsto (fun k : ℕ => P.real {z | x + 1 / ((k : ℝ) + 1) < f z}) atTop (𝓝 (P.real {z | x < f z})) := by
  set s : ℕ → Set 𝒳 := fun k => {z | x + 1 / ((k : ℝ) + 1) < f z} with hs
  have hmono : Monotone s := by
    intro k l hkl z hz
    simp only [hs, Set.mem_ofPred_eq] at hz ⊢
    have : 1 / ((l : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkl 1)
    linarith
  have hU : (⋃ k, s k) = {z | x < f z} := by
    ext z
    simp only [hs, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk⟩
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    · intro hz
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hz)
      exact ⟨k, by linarith⟩
  have h := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hU] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top P _)).comp h

/-- **`KS⁺` is a supremum over the rationals** for measurable `f` (right-continuity of the tails). -/
theorem ksPlus_eq_iSup_rat (P Q : Measure 𝒳) [IsFiniteMeasure P] [IsFiniteMeasure Q] (f : 𝒳 → ℝ) :
    ksPlus P Q f = ⨆ q : ℚ, (P.real {z | (q : ℝ) < f z} - Q.real {z | (q : ℝ) < f z}) := by
  unfold ksPlus
  apply le_antisymm
  · refine ciSup_le fun x => ?_
    have hr : ∀ k : ℕ, ∃ r : ℚ, x < r ∧ (r : ℝ) < x + 1 / ((k : ℝ) + 1) := fun k =>
      exists_rat_btwn (by have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
                          linarith)
    choose r hr1 hr2 using hr
    have hle : ∀ k : ℕ, P.real {z | x + 1 / ((k : ℝ) + 1) < f z} - Q.real {z | x < f z} ≤
        ⨆ q : ℚ, (P.real {z | (q : ℝ) < f z} - Q.real {z | (q : ℝ) < f z}) := by
      intro k
      have h1 : P.real {z | x + 1 / ((k : ℝ) + 1) < f z} ≤ P.real {z | ((r k : ℚ) : ℝ) < f z} :=
        measureReal_mono fun z hz => by simp only [Set.mem_ofPred_eq] at hz ⊢; linarith [hr2 k]
      have h2 : Q.real {z | ((r k : ℚ) : ℝ) < f z} ≤ Q.real {z | x < f z} :=
        measureReal_mono fun z hz => by simp only [Set.mem_ofPred_eq] at hz ⊢; linarith [hr1 k]
      have h3 := le_ciSup (bddAbove_tail_sub P Q f (fun q : ℚ => (q : ℝ))) (r k)
      linarith
    exact le_of_tendsto' ((tendsto_measureReal_lt P f x).sub_const _) hle
  · exact ciSup_le fun q => le_ciSup (bddAbove_tail_sub P Q f (fun x : ℝ => x)) (q : ℝ)

/-- **Measurability of `KS⁺` of a jointly measurable family**: `ω ↦ KS⁺_{P,Q}(F ω)` is measurable. -/
theorem measurable_ksPlus {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure 𝒳) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {F : Ω → 𝒳 → ℝ} (hF : Measurable fun p : Ω × 𝒳 => F p.1 p.2) : Measurable fun ω => ksPlus P Q (F ω) := by
  have e : (fun ω => ksPlus P Q (F ω)) =
      fun ω => ⨆ q : ℚ, (P.real {z | (q : ℝ) < F ω z} - Q.real {z | (q : ℝ) < F ω z}) :=
    funext fun ω => ksPlus_eq_iSup_rat P Q (F ω)
  rw [e]
  refine Measurable.iSup fun q => ?_
  have hs : MeasurableSet {p : Ω × 𝒳 | (q : ℝ) < F p.1 p.2} := measurableSet_lt measurable_const hF
  have hP : Measurable fun ω => P (Prod.mk ω ⁻¹' {p : Ω × 𝒳 | (q : ℝ) < F p.1 p.2}) :=
    measurable_measure_prodMk_left hs
  have hQ : Measurable fun ω => Q (Prod.mk ω ⁻¹' {p : Ω × 𝒳 | (q : ℝ) < F p.1 p.2}) :=
    measurable_measure_prodMk_left hs
  exact hP.ennreal_toReal.sub hQ.ennreal_toReal

end StatFormal.Alpha0Witness
