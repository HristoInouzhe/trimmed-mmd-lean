import StatFormal.Lib.TrimmedMean.Asymp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Moments.Variance

/-!
# A positive density near the quantile gives a unique quantile and a non-degenerate variance (library)

`AssDens P h p q` (the printed `ass:split`, one side): `q` is a `p`-quantile of the law of `h` under `P`
(`P(h < q) ≤ p ≤ P(h ≤ q)`) and on a neighbourhood `(q − ε, q + ε)` that law has a Lebesgue density `ρ > 0`
(`P(h ∈ (a, b]) = ∫_{(a,b]} ρ` for `q − ε < a`, `b < q + ε`).

* `AssDens.uq`: then `q` is the unique `p`-quantile (`UQ`);
* `AssDens.var_pos`: if `p < 1`, `Var_P((q − h)_+) > 0`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.Foundations.TrimmedMean

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {P : Measure 𝒳} [IsProbabilityMeasure P]

/-- The density form of `ass:split` at level `p` (one side). -/
def AssDens (P : Measure 𝒳) (h : 𝒳 → ℝ) (p q : ℝ) : Prop :=
  P.real {x | h x < q} ≤ p ∧ p ≤ P.real {x | h x ≤ q} ∧
    ∃ ε > 0, ∃ ρ : ℝ → ℝ, Measurable ρ ∧ (∀ t ∈ Ioo (q - ε) (q + ε), 0 < ρ t) ∧
      ∀ a b, q - ε < a → b < q + ε → P {x | h x ∈ Ioc a b} = ∫⁻ t in Ioc a b, ENNReal.ofReal (ρ t)

lemma AssDens.mass_pos {h : 𝒳 → ℝ} {p q : ℝ} (hA : AssDens P h p q) :
    ∃ ε > 0, ∀ a b, q - ε < a → a < b → b < q + ε → 0 < P.real {x | h x ∈ Ioc a b} := by
  obtain ⟨-, -, ε, hε, ρ, hρm, hρ, hd⟩ := hA
  refine ⟨ε, hε, fun a b ha hab hb => ?_⟩
  rw [measureReal_def, ENNReal.toReal_pos_iff]
  refine ⟨?_, measure_lt_top _ _⟩
  rw [hd a b ha hb, lintegral_pos_iff_support hρm.ennreal_ofReal]
  rw [Measure.restrict_apply' measurableSet_Ioc]
  have hsub : Ioc a b ⊆ Function.support (fun t => ENNReal.ofReal (ρ t)) ∩ Ioc a b := fun t ht => by
    refine ⟨?_, ht⟩
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hρ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_pos.2 (by linarith)

theorem AssDens.uq {h : 𝒳 → ℝ} (hm : Measurable h) {p q : ℝ} (hA : AssDens P h p q) : UQ P h p q := by
  obtain ⟨ε, hε, hpos⟩ := hA.mass_pos
  obtain ⟨h1, h2, -⟩ := hA
  have hms : ∀ a b : ℝ, MeasurableSet {x | h x ∈ Ioc a b} := fun a b => hm measurableSet_Ioc
  refine ⟨h1, h2, fun d hd => ?_, fun d hd => ?_⟩
  · set d' := min d (ε / 2)
    have hd' : 0 < d' := lt_min hd (by linarith)
    have hd'1 : d' ≤ d := min_le_left _ _
    have hd'2 : d' ≤ ε / 2 := min_le_right _ _
    have hI := hpos (q - d') (q - d' / 2) (by linarith) (by linarith) (by linarith)
    have hdisj : Disjoint {x | h x ≤ q - d'} {x | h x ∈ Ioc (q - d') (q - d' / 2)} :=
      Set.disjoint_left.2 fun x hx1 hx2 => by
        simp only [mem_setOf_eq, mem_Ioc] at hx1 hx2; linarith [hx2.1]
    have hsub : {x | h x ≤ q - d'} ∪ {x | h x ∈ Ioc (q - d') (q - d' / 2)} ⊆ {x | h x < q} := by
      intro x hx
      rcases hx with hx | hx
      · simp only [mem_setOf_eq] at hx ⊢; linarith
      · simp only [mem_setOf_eq, mem_Ioc] at hx ⊢; linarith [hx.2]
    have e := measureReal_union (μ := P) hdisj (hms _ _) (measure_ne_top _ _) (measure_ne_top _ _)
    have hle := measureReal_mono (μ := P) hsub (measure_ne_top _ _)
    have hle2 : P.real {x | h x < q - d} ≤ P.real {x | h x ≤ q - d'} :=
      measureReal_mono (fun x hx => by simp only [mem_setOf_eq] at hx ⊢; linarith) (measure_ne_top _ _)
    linarith
  · set d' := min d (ε / 2)
    have hd' : 0 < d' := lt_min hd (by linarith)
    have hd'1 : d' ≤ d := min_le_left _ _
    have hd'2 : d' ≤ ε / 2 := min_le_right _ _
    have hI := hpos q (q + d') (by linarith) (by linarith) (by linarith)
    have hdisj : Disjoint {x | h x ≤ q} {x | h x ∈ Ioc q (q + d')} :=
      Set.disjoint_left.2 fun x hx1 hx2 => by
        simp only [mem_setOf_eq, mem_Ioc] at hx1 hx2; linarith [hx2.1]
    have hsub : {x | h x ≤ q} ∪ {x | h x ∈ Ioc q (q + d')} ⊆ {x | h x ≤ q + d} := by
      intro x hx
      rcases hx with hx | hx
      · simp only [mem_setOf_eq] at hx ⊢; linarith
      · simp only [mem_setOf_eq, mem_Ioc] at hx ⊢; linarith [hx.2]
    have e := measureReal_union (μ := P) hdisj (hms _ _) (measure_ne_top _ _) (measure_ne_top _ _)
    have hle := measureReal_mono (μ := P) hsub (measure_ne_top _ _)
    linarith

lemma exists_mem_of_ae_eq {S : Set 𝒳} (hS : 0 < P.real S) {g : 𝒳 → ℝ} {c : ℝ} (hg : ∀ᵐ x ∂P, g x = c) :
    ∃ x ∈ S, g x = c := by
  by_contra hc
  push_neg at hc
  have : P S = 0 := measure_mono_null (fun x hx => hc x hx) (ae_iff.1 hg)
  rw [measureReal_def, this, ENNReal.toReal_zero] at hS
  exact lt_irrefl _ hS

theorem AssDens.var_pos {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) {p q : ℝ}
    (hA : AssDens P h p q) (hp : p < 1) : 0 < Var[fun x => max (q - h x) 0; P] := by
  obtain ⟨ε, hε, hpos⟩ := hA.mass_pos
  obtain ⟨h1, -, -⟩ := hA
  set g : 𝒳 → ℝ := fun x => max (q - h x) 0
  have hgm : Measurable g := (hm.const_sub q).max measurable_const
  have hgb : ∀ x, ‖g x‖ ≤ |q| + |B| := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by positivity)
    have := le_abs_self q; have := neg_abs_le (h x); have := (hB x).trans (le_abs_self B); linarith
  have hmem : MemLp g 2 P := MemLp.of_bound hgm.aestronglyMeasurable _ (ae_of_all _ hgb)
  rcases (variance_nonneg g P).eq_or_lt with h0 | h0
  · exfalso
    have hev : evariance g P = 0 := by rw [← ofReal_variance hmem, ← h0, ENNReal.ofReal_zero]
    have hae := (evariance_eq_zero_iff hgm.aemeasurable).1 hev
    -- on `{h ≥ q}` (mass `≥ 1 − p > 0`), `g = 0`
    have hS1 : 0 < P.real {x | q ≤ h x} := by
      have : {x | q ≤ h x} = {x | h x < q}ᶜ := by ext x; simp
      rw [this, probReal_compl_eq_one_sub (measurableSet_lt hm measurable_const)]
      linarith
    obtain ⟨x1, hx1, hgx1⟩ := exists_mem_of_ae_eq hS1 hae
    have hc0 : P[g] = 0 := by
      rw [← hgx1]; simp only [g]; rw [max_eq_right]; simp only [mem_setOf_eq] at hx1; linarith
    -- on `(q − ε/2, q − ε/4]` (positive mass), `g ≥ ε/4 > 0`
    have hS2 := hpos (q - ε / 2) (q - ε / 4) (by linarith) (by linarith) (by linarith)
    obtain ⟨x2, hx2, hgx2⟩ := exists_mem_of_ae_eq hS2 hae
    simp only [mem_setOf_eq, mem_Ioc] at hx2
    have : 0 < g x2 := lt_of_lt_of_le (by linarith [hx2.2]) (le_max_left _ _)
    rw [hgx2, hc0] at this
    exact lt_irrefl _ this
  · exact h0

end StatFormal.Foundations.TrimmedMean
