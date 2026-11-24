import StatFormal.Lib.Distances.TV
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The bump perturbation of a density (library, untrusted)

For a density `f ≥ 0` with respect to a measure `ν`, disjoint measurable sets `A, B` and weights `a, b ≥ 0`, the *bump*
`f·(1 + a·1_A − b·1_B)` moves mass from `B` to `A`. With `μ = f·ν`, `a·μ(A) = b·μ(B)` and `b ≤ 1` it is again the density of a
probability measure when `μ` is one (in Lemma S4.28 of the trimmed-mmd supplement, `a = hπ/μ(A)`, `b = hπ/μ(B)` with
`π = min{μ(A), μ(B)}`, `h ∈ [0,1]`).

* `bump`, `bump_eq`, `bump_of_mem_left`, `bump_of_mem_right`, `bump_of_not_mem`, `bump_nonneg`, `le_bump`, `bump_le`,
  `bump_le_two_mul`, `abs_bump_sub_le`, `measurable_bump`, `integrable_bump`: pointwise facts;
* `measureReal_withDensity_ofReal`: `(f·ν)(S) = ∫_S f dν` (real form); `withDensity_pos_of_pos_on`;
* `measureReal_bump`: `(bump·ν)(S) = μ(S) + a·μ(S ∩ A) − b·μ(S ∩ B)`;
* `isProbabilityMeasure_bump`: the bump law is a probability measure when `μ` is one and `a·μ(A) = b·μ(B)`;
* `integral_posPart_bump`: if `g ≤ f` a.e. on `A` and `f ≤ g` a.e. on `B`, then `∫(bump − g)₊ = ∫(f − g)₊ + a∫_A f`;
* `ae_condR_bump`: `c·w·(f + g) ≤ |f − g|` a.e. gives `(c/2)·w·(bump + g) ≤ |bump − g|` a.e. (`a ≤ 1`, the same signs);
* `setLIntegral_abs_bump_sub_le`: `∫⁻_S |bump − g| ≤ ∫⁻_S |f − g| + a·μ(S ∩ A) + b·μ(S ∩ B)`.

Two-point perturbations of a density of this kind are standard in lower bounds (Tsybakov, *Introduction to Nonparametric
Estimation*, §2.3); this one keeps the density unchanged off `A ∪ B`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace StatFormal.LocalLower

variable {α : Type*}

/-- The bump `f·(1 + a·1_A − b·1_B)` of a density `f`: the mass `a·∫_A f` is added on `A`, `b·∫_B f` is removed on `B`. -/
def bump (f : α → ℝ) (A B : Set α) (a b : ℝ) (z : α) : ℝ :=
  f z * (1 + a * A.indicator (fun _ => (1 : ℝ)) z - b * B.indicator (fun _ => (1 : ℝ)) z)

variable {f g : α → ℝ} {A B : Set α} {a b : ℝ}

/-- `bump = f + a·1_A f − b·1_B f`. -/
theorem bump_eq (f : α → ℝ) (A B : Set α) (a b : ℝ) :
    bump f A B a b = fun z => f z + a * A.indicator f z - b * B.indicator f z := by
  funext z
  by_cases hA : z ∈ A <;> by_cases hB : z ∈ B <;> simp [bump, hA, hB] <;> ring

/-- On `A`, the bump is `f·(1 + a)`. -/
theorem bump_of_mem_left (hAB : Disjoint A B) {z : α} (hz : z ∈ A) : bump f A B a b z = f z * (1 + a) := by
  have hzB : z ∉ B := Set.disjoint_left.1 hAB hz
  simp [bump, hz, hzB]

/-- On `B`, the bump is `f·(1 − b)`. -/
theorem bump_of_mem_right (hAB : Disjoint A B) {z : α} (hz : z ∈ B) : bump f A B a b z = f z * (1 - b) := by
  have hzA : z ∉ A := Set.disjoint_right.1 hAB hz
  simp [bump, hz, hzA]

/-- Off `A ∪ B`, the bump is `f`. -/
theorem bump_of_not_mem {z : α} (hA : z ∉ A) (hB : z ∉ B) : bump f A B a b z = f z := by
  simp [bump, hA, hB]

/-- The bump is nonnegative when `f ≥ 0`, `a ≥ 0` and `b ≤ 1`. -/
theorem bump_nonneg (hAB : Disjoint A B) (hf0 : ∀ z, 0 ≤ f z) (ha : 0 ≤ a) (hb : b ≤ 1) (z : α) : 0 ≤ bump f A B a b z := by
  by_cases hA : z ∈ A
  · rw [bump_of_mem_left hAB hA]; exact mul_nonneg (hf0 z) (by linarith)
  · by_cases hB : z ∈ B
    · rw [bump_of_mem_right hAB hB]; exact mul_nonneg (hf0 z) (by linarith)
    · rw [bump_of_not_mem hA hB]; exact hf0 z

/-- Off `B` the bump is at least `f` (`a ≥ 0`). -/
theorem le_bump (hAB : Disjoint A B) (hf0 : ∀ z, 0 ≤ f z) (ha : 0 ≤ a) {z : α} (hz : z ∉ B) : f z ≤ bump f A B a b z := by
  by_cases hA : z ∈ A
  · rw [bump_of_mem_left hAB hA]; nlinarith [hf0 z]
  · rw [bump_of_not_mem hA hz]

/-- Off `A` the bump is at most `f` (`b ≥ 0`). -/
theorem bump_le (hAB : Disjoint A B) (hf0 : ∀ z, 0 ≤ f z) (hb : 0 ≤ b) {z : α} (hz : z ∉ A) : bump f A B a b z ≤ f z := by
  by_cases hB : z ∈ B
  · rw [bump_of_mem_right hAB hB]; nlinarith [hf0 z]
  · rw [bump_of_not_mem hz hB]

/-- The bump is at most `2f` (`a ≤ 1`, `b ≥ 0`). -/
theorem bump_le_two_mul (hAB : Disjoint A B) (hf0 : ∀ z, 0 ≤ f z) (ha : a ≤ 1) (hb : 0 ≤ b) (z : α) :
    bump f A B a b z ≤ 2 * f z := by
  by_cases hA : z ∈ A
  · rw [bump_of_mem_left hAB hA]; nlinarith [hf0 z]
  · have := bump_le (a := a) hAB hf0 hb hA; linarith [hf0 z]

/-- `|bump − g| ≤ |f − g| + a·1_A f + b·1_B f`. -/
theorem abs_bump_sub_le (hAB : Disjoint A B) (hf0 : ∀ z, 0 ≤ f z) (ha : 0 ≤ a) (hb : 0 ≤ b) (z : α) :
    |bump f A B a b z - g z| ≤ |f z - g z| + a * A.indicator f z + b * B.indicator f z := by
  by_cases hA : z ∈ A
  · have hB : z ∉ B := Set.disjoint_left.1 hAB hA
    rw [bump_of_mem_left hAB hA]
    simp only [indicator_of_mem hA, indicator_of_notMem hB, mul_zero, add_zero]
    calc |f z * (1 + a) - g z| = |(f z - g z) + a * f z| := by ring_nf
      _ ≤ |f z - g z| + |a * f z| := abs_add_le _ _
      _ = |f z - g z| + a * f z := by rw [abs_of_nonneg (mul_nonneg ha (hf0 z))]
  · by_cases hB : z ∈ B
    · rw [bump_of_mem_right hAB hB]
      simp only [indicator_of_mem hB, indicator_of_notMem hA, mul_zero, add_zero]
      calc |f z * (1 - b) - g z| = |(f z - g z) + -(b * f z)| := by ring_nf
        _ ≤ |f z - g z| + |-(b * f z)| := abs_add_le _ _
        _ = |f z - g z| + b * f z := by rw [abs_neg, abs_of_nonneg (mul_nonneg hb (hf0 z))]
    · rw [bump_of_not_mem hA hB]
      simp [indicator_of_notMem hA, indicator_of_notMem hB]

variable [MeasurableSpace α]

theorem measurable_bump (hf : Measurable f) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measurable (bump f A B a b) := by
  unfold bump
  exact hf.mul ((measurable_const.add (measurable_const.mul (measurable_const.indicator hA))).sub
    (measurable_const.mul (measurable_const.indicator hB)))

theorem integrable_bump {ν : Measure α} (hf : Integrable f ν) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Integrable (bump f A B a b) ν := by
  rw [bump_eq]
  exact (hf.add ((hf.indicator hA).const_mul a)).sub ((hf.indicator hB).const_mul b)

/-- `(f·ν)(S) = ∫_S f dν` for an integrable density `f ≥ 0` (real form). -/
theorem measureReal_withDensity_ofReal {ν : Measure α} (hf : Integrable f ν) (hf0 : ∀ x, 0 ≤ f x) {S : Set α}
    (hS : MeasurableSet S) : (ν.withDensity fun x => ENNReal.ofReal (f x)).real S = ∫ x in S, f x ∂ν := by
  rw [measureReal_def, withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_of_all _ hf0),
    ENNReal.toReal_ofReal (setIntegral_nonneg hS fun x _ => hf0 x)]

/-- A density positive on a set of positive measure gives the set positive mass. -/
theorem withDensity_pos_of_pos_on {ν : Measure α} (hf : Measurable f) {S : Set α} (hS : MeasurableSet S)
    (hpos : ∀ x ∈ S, 0 < f x) (hνS : 0 < ν S) : 0 < (ν.withDensity fun x => ENNReal.ofReal (f x)) S := by
  rw [withDensity_apply _ hS, setLIntegral_pos_iff hf.ennreal_ofReal]
  refine hνS.trans_le (measure_mono fun x hx => ⟨?_, hx⟩)
  simp [Function.mem_support, hpos x hx]

/-- **The bump law on a set**: `(bump·ν)(S) = μ(S) + a·μ(S ∩ A) − b·μ(S ∩ B)`, `μ = f·ν`. -/
theorem measureReal_bump {ν : Measure α} (hf : Integrable f ν) (hf0 : ∀ z, 0 ≤ f z) (hAB : Disjoint A B)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (ha : 0 ≤ a) (hb : b ≤ 1) {S : Set α} (hS : MeasurableSet S) :
    (ν.withDensity fun x => ENNReal.ofReal (bump f A B a b x)).real S =
      (ν.withDensity fun x => ENNReal.ofReal (f x)).real S +
        a * (ν.withDensity fun x => ENNReal.ofReal (f x)).real (S ∩ A) -
        b * (ν.withDensity fun x => ENNReal.ofReal (f x)).real (S ∩ B) := by
  rw [measureReal_withDensity_ofReal (integrable_bump hf hA hB) (bump_nonneg hAB hf0 ha hb) hS,
    measureReal_withDensity_ofReal hf hf0 hS, measureReal_withDensity_ofReal hf hf0 (hS.inter hA),
    measureReal_withDensity_ofReal hf hf0 (hS.inter hB)]
  simp only [bump_eq]
  have h1 : IntegrableOn f S ν := hf.integrableOn
  have h2 : IntegrableOn (fun z => a * A.indicator f z) S ν := ((hf.indicator hA).const_mul a).integrableOn
  have h3 : IntegrableOn (fun z => b * B.indicator f z) S ν := ((hf.indicator hB).const_mul b).integrableOn
  have h12 : IntegrableOn (fun z => f z + a * A.indicator f z) S ν := h1.add h2
  rw [integral_sub h12 h3, integral_add h1 h2, integral_const_mul, integral_const_mul,
    setIntegral_indicator hA, setIntegral_indicator hB]

/-- **The bump law is a probability measure** when `μ = f·ν` is one, `a ≥ 0`, `b ≤ 1` and `a·μ(A) = b·μ(B)`. -/
theorem isProbabilityMeasure_bump {ν : Measure α} (hf : Integrable f ν) (hf0 : ∀ z, 0 ≤ f z) (hAB : Disjoint A B)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (ha : 0 ≤ a) (hb : b ≤ 1)
    [hμ : IsProbabilityMeasure (ν.withDensity fun x => ENNReal.ofReal (f x))]
    (hab : a * (ν.withDensity fun x => ENNReal.ofReal (f x)).real A =
      b * (ν.withDensity fun x => ENNReal.ofReal (f x)).real B) :
    IsProbabilityMeasure (ν.withDensity fun x => ENNReal.ofReal (bump f A B a b x)) := by
  have hreal := measureReal_bump hf hf0 hAB hA hB ha hb MeasurableSet.univ
  have h1 : (ν.withDensity fun x => ENNReal.ofReal (f x)).real univ = 1 := probReal_univ
  rw [univ_inter, univ_inter, h1, hab, add_sub_cancel_right] at hreal
  have hfin : (ν.withDensity fun x => ENNReal.ofReal (bump f A B a b x)) univ ≠ ∞ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (integrable_bump hf hA hB).lintegral_lt_top.ne
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_toReal hfin]
  rw [measureReal_def] at hreal
  rw [hreal, ENNReal.ofReal_one]

/-- **The positive part against another density**: if `g ≤ f` a.e. on `A` and `f ≤ g` a.e. on `B`, then
`∫(bump − g)₊ = ∫(f − g)₊ + a·∫_A f` (the bump moves mass into the part of `A` where `f` already dominates, and out of the part
of `B` where `g` dominates). -/
theorem integral_posPart_bump {ν : Measure α} (hf : Integrable f ν) (hg : Integrable g ν) (hf0 : ∀ z, 0 ≤ f z)
    (hAB : Disjoint A B) (hA : MeasurableSet A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsA : ∀ᵐ x ∂ν, x ∈ A → g x ≤ f x) (hsB : ∀ᵐ x ∂ν, x ∈ B → f x ≤ g x) :
    ∫ x, max (bump f A B a b x - g x) 0 ∂ν = ∫ x, max (f x - g x) 0 ∂ν + a * ∫ x in A, f x ∂ν := by
  have hpt : ∀ᵐ x ∂ν, max (bump f A B a b x - g x) 0 = max (f x - g x) 0 + a * A.indicator f x := by
    filter_upwards [hsA, hsB] with x hxA hxB
    by_cases hA' : x ∈ A
    · rw [bump_of_mem_left hAB hA', indicator_of_mem hA']
      have h1 := hxA hA'
      have h2 : 0 ≤ a * f x := mul_nonneg ha (hf0 x)
      rw [max_eq_left (by nlinarith), max_eq_left (by linarith)]
      ring
    · rw [indicator_of_notMem hA', mul_zero, add_zero]
      by_cases hB' : x ∈ B
      · rw [bump_of_mem_right hAB hB']
        have h1 := hxB hB'
        have h2 : 0 ≤ b * f x := mul_nonneg hb (hf0 x)
        rw [max_eq_right (by nlinarith), max_eq_right (by linarith)]
      · rw [bump_of_not_mem hA' hB']
  have hi1 : Integrable (fun x => max (f x - g x) 0) ν := (hf.sub hg).pos_part
  have hi2 : Integrable (fun x => a * A.indicator f x) ν := (hf.indicator hA).const_mul a
  rw [integral_congr_ae hpt, integral_add hi1 hi2, integral_const_mul, integral_indicator hA]

/-- **The local condition survives with half the constant**: if `c·w·(f + g) ≤ |f − g|` a.e. (`c ≥ 0`, `w ≥ 0`), `g ≤ f` a.e. on
`A` and `f ≤ g` a.e. on `B`, then `(c/2)·w·(bump + g) ≤ |bump − g|` a.e. for `a ∈ [0,1]`, `b ≥ 0` (on `A`, `|bump − g| ≥ |f − g|`
and `bump + g ≤ 2(f + g)`; on `B`, `|bump − g| ≥ |f − g|` and `bump ≤ f`). -/
theorem ae_condR_bump {ν : Measure α} (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z) (hAB : Disjoint A B) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hb : 0 ≤ b) {c : ℝ} {w : α → ℝ} (hc : 0 ≤ c) (hw : ∀ x, 0 ≤ w x)
    (hsA : ∀ᵐ x ∂ν, x ∈ A → g x ≤ f x) (hsB : ∀ᵐ x ∂ν, x ∈ B → f x ≤ g x)
    (h : ∀ᵐ x ∂ν, c * w x * (f x + g x) ≤ |f x - g x|) :
    ∀ᵐ x ∂ν, c / 2 * w x * (bump f A B a b x + g x) ≤ |bump f A B a b x - g x| := by
  filter_upwards [hsA, hsB, h] with x hxA hxB hx
  have hcw : 0 ≤ c * w x := mul_nonneg hc (hw x)
  have hfx := hf0 x
  have hgx := hg0 x
  by_cases hA' : x ∈ A
  · rw [bump_of_mem_left hAB hA']
    have h1 := hxA hA'
    have e1 : |f x - g x| = f x - g x := abs_of_nonneg (by linarith)
    have e2 : |f x * (1 + a) - g x| = f x * (1 + a) - g x := abs_of_nonneg (by nlinarith)
    rw [e1] at hx
    rw [e2]
    have h3 : f x * (1 + a) + g x ≤ 2 * (f x + g x) := by nlinarith
    have h4 : c / 2 * w x * (f x * (1 + a) + g x) ≤ c / 2 * w x * (2 * (f x + g x)) :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg (div_nonneg hc two_pos.le) (hw x))
    have h5 : c / 2 * w x * (2 * (f x + g x)) = c * w x * (f x + g x) := by ring
    nlinarith
  · by_cases hB' : x ∈ B
    · rw [bump_of_mem_right hAB hB']
      have h1 := hxB hB'
      have e1 : |f x - g x| = g x - f x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      have e2 : |f x * (1 - b) - g x| = g x - f x * (1 - b) := by
        rw [abs_sub_comm]; exact abs_of_nonneg (by nlinarith)
      rw [e1] at hx
      rw [e2]
      have h3 : f x * (1 - b) + g x ≤ f x + g x := by nlinarith
      have h4 : c / 2 * w x * (f x * (1 - b) + g x) ≤ c / 2 * w x * (f x + g x) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg (div_nonneg hc two_pos.le) (hw x))
      have h5 : c / 2 * w x * (f x + g x) ≤ c * w x * (f x + g x) := by
        have : 0 ≤ c * w x * (f x + g x) := mul_nonneg hcw (by linarith)
        nlinarith
      nlinarith
    · rw [bump_of_not_mem hA' hB']
      have : 0 ≤ c * w x * (f x + g x) := mul_nonneg hcw (by linarith)
      nlinarith

/-- **The `|f − g|` mass of the bump on a set**: `∫⁻_S |bump − g| ≤ ∫⁻_S |f − g| + a·μ(S ∩ A) + b·μ(S ∩ B)`, `μ = f·ν`. -/
theorem setLIntegral_abs_bump_sub_le {ν : Measure α} (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ z, 0 ≤ f z)
    (hAB : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) (ha : 0 ≤ a) (hb : 0 ≤ b) {S : Set α}
    (hS : MeasurableSet S) :
    ∫⁻ x in S, ENNReal.ofReal |bump f A B a b x - g x| ∂ν ≤
      ∫⁻ x in S, ENNReal.ofReal |f x - g x| ∂ν +
        ENNReal.ofReal a * (ν.withDensity fun x => ENNReal.ofReal (f x)) (S ∩ A) +
        ENNReal.ofReal b * (ν.withDensity fun x => ENNReal.ofReal (f x)) (S ∩ B) := by
  have hpt : ∀ x, ENNReal.ofReal |bump f A B a b x - g x| ≤
      ENNReal.ofReal |f x - g x| + ENNReal.ofReal a * A.indicator (fun x => ENNReal.ofReal (f x)) x +
        ENNReal.ofReal b * B.indicator (fun x => ENNReal.ofReal (f x)) x := by
    intro x
    have hiA : ENNReal.ofReal (a * A.indicator f x) = ENNReal.ofReal a * A.indicator (fun x => ENNReal.ofReal (f x)) x := by
      by_cases hx : x ∈ A <;> simp [hx, ENNReal.ofReal_mul ha]
    have hiB : ENNReal.ofReal (b * B.indicator f x) = ENNReal.ofReal b * B.indicator (fun x => ENNReal.ofReal (f x)) x := by
      by_cases hx : x ∈ B <;> simp [hx, ENNReal.ofReal_mul hb]
    have hnA : 0 ≤ a * A.indicator f x := mul_nonneg ha (indicator_nonneg (fun z _ => hf0 z) x)
    have hnB : 0 ≤ b * B.indicator f x := mul_nonneg hb (indicator_nonneg (fun z _ => hf0 z) x)
    rw [← hiA, ← hiB, ← ENNReal.ofReal_add (abs_nonneg _) hnA, ← ENNReal.ofReal_add (by positivity) hnB]
    exact ENNReal.ofReal_le_ofReal (abs_bump_sub_le hAB hf0 ha hb x)
  have hm1 : Measurable fun x => ENNReal.ofReal |f x - g x| := by fun_prop
  have hm2 : Measurable fun x => ENNReal.ofReal a * A.indicator (fun x => ENNReal.ofReal (f x)) x :=
    measurable_const.mul (hf.ennreal_ofReal.indicator hA)
  have hm3 : Measurable fun x => ENNReal.ofReal b * B.indicator (fun x => ENNReal.ofReal (f x)) x :=
    measurable_const.mul (hf.ennreal_ofReal.indicator hB)
  have hm12 : Measurable fun x => ENNReal.ofReal |f x - g x| +
      ENNReal.ofReal a * A.indicator (fun x => ENNReal.ofReal (f x)) x := hm1.add hm2
  refine (lintegral_mono hpt).trans_eq ?_
  rw [lintegral_add_left hm12, lintegral_add_left hm1,
    lintegral_const_mul _ (hf.ennreal_ofReal.indicator hA), lintegral_const_mul _ (hf.ennreal_ofReal.indicator hB),
    lintegral_indicator hA, lintegral_indicator hB, Measure.restrict_restrict hA, Measure.restrict_restrict hB,
    withDensity_apply _ (hS.inter hA), withDensity_apply _ (hS.inter hB), inter_comm A S, inter_comm B S]

end StatFormal.LocalLower
