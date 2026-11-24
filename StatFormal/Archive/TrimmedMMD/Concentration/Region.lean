import StatFormal.Archive.TrimmedMMD.Concentration.Statements
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Trimmed regions: CVaR bounds and the Hausdorff reduction (helpers, untrusted)

For a probability measure `Q`, `α ∈ [0,1)`, `β = 1/(1−α)` and a unit direction `f`, write
`Y = ⟪f, φ ·⟫` and `A_Q(t) = t + β E_Q (Y − t)₊`.

* `integral_mul_le_cvar` (`eq:cvar`, easy half): every admissible weight `g` has
  `E_Q[g Y] ≤ A_Q(t)` for every `t`.
* `exists_cvar_witness` (`eq:cvar` attainment + `lem:tcompact`): there are `q ∈ [−κ, κ]` and an
  admissible `g` with `E_Q[g Y] = A_Q(q)` (upper-tail quantile construction, with a fractional
  weight on the atom `{Y = q}`).
* `infDist_region_le` (`eq:hormander`, the `≤` half, via the projection onto the closed convex
  hull): if `E_{Q₁}(Y−q)₊ − E_{Q₂}(Y−q)₊ ≤ S` for all `‖f‖ ≤ 1, |q| ≤ κ`, then every point of
  `region φ α Q₁` is within `β S` of `region φ α Q₂`.
* `hausdorffDist_region_le` (`eq:reduction`): with both one-sided bounds,
  `d_H(region φ α Q₁, region φ α Q₂) ≤ β S`.
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.TrimmedMMD.Concentration

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Real-valued CVaR facts -/

theorem integral_mul_le_cvar (Q : Measure 𝒳) [IsProbabilityMeasure Q] {Y : 𝒳 → ℝ}
    (hY : Measurable Y) {κ : ℝ} (hYb : ∀ x, |Y x| ≤ κ) {β : ℝ} {g : 𝒳 → ℝ} (hg : Measurable g)
    (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ β) (hg1 : ∫ x, g x ∂Q = 1) (t : ℝ) :
    ∫ x, g x * Y x ∂Q ≤ t + β * ∫ x, max (Y x - t) 0 ∂Q := by
  have hβ0 : 0 ≤ β := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure Q
    exact (hgb x).1.trans (hgb x).2
  have hgI : Integrable g Q := Integrable.of_bound hg.aestronglyMeasurable β
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hgb x).1]; exact (hgb x).2)
  have hmI : Integrable (fun x => max (Y x - t) 0) Q :=
    Integrable.of_bound ((hY.sub_const t).max measurable_const).aestronglyMeasurable (κ + |t|)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        have hκ0 : 0 ≤ κ := (abs_nonneg _).trans (hYb x)
        refine max_le ?_ (by linarith [abs_nonneg t])
        linarith [le_abs_self (Y x), hYb x, neg_abs_le t])
  have hgYI : Integrable (fun x => g x * Y x) Q :=
    Integrable.of_bound (hg.mul hY).aestronglyMeasurable (β * κ)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hgb x).1]
        exact mul_le_mul (hgb x).2 (hYb x) (abs_nonneg _) hβ0)
  calc ∫ x, g x * Y x ∂Q ≤ ∫ x, (t * g x + β * max (Y x - t) 0) ∂Q := by
        refine integral_mono hgYI ((hgI.const_mul t).add (hmI.const_mul β)) fun x => ?_
        have h1 : g x * (Y x - t) ≤ g x * max (Y x - t) 0 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (hgb x).1
        have h2 : g x * max (Y x - t) 0 ≤ β * max (Y x - t) 0 :=
          mul_le_mul_of_nonneg_right (hgb x).2 (le_max_right _ _)
        simp only
        nlinarith
    _ = t + β * ∫ x, max (Y x - t) 0 ∂Q := by
        rw [integral_add (hgI.const_mul t) (hmI.const_mul β), integral_const_mul,
          integral_const_mul, hg1, mul_one]

theorem exists_cvar_witness (Q : Measure 𝒳) [IsProbabilityMeasure Q] {Y : 𝒳 → ℝ}
    (hY : Measurable Y) {κ : ℝ} (hYb : ∀ x, |Y x| ≤ κ) {β : ℝ} (hβ : 1 ≤ β) :
    ∃ q : ℝ, |q| ≤ κ ∧ ∃ g : 𝒳 → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ β) ∧
      ∫ x, g x ∂Q = 1 ∧ ∫ x, g x * Y x ∂Q = q + β * ∫ x, max (Y x - q) 0 ∂Q := by
  have hβ0 : 0 < β := by linarith
  have hYl : ∀ x, -κ ≤ Y x := fun x => (abs_le.1 (hYb x)).1
  have hYu : ∀ x, Y x ≤ κ := fun x => (abs_le.1 (hYb x)).2
  set S : Set ℝ := {t | t ∈ Icc (-κ) κ ∧ 1 / β ≤ Q.real {x | t ≤ Y x}} with hSdef
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure Q
    exact (abs_nonneg _).trans (hYb x)
  have hmS : -κ ∈ S := by
    refine ⟨⟨le_rfl, by linarith⟩, ?_⟩
    have : {x | -κ ≤ Y x} = univ := eq_univ_of_forall hYl
    rw [this, probReal_univ, div_le_one hβ0]; exact hβ
  have hSbdd : BddAbove S := ⟨κ, fun t ht => ht.1.2⟩
  have hSne : S.Nonempty := ⟨_, hmS⟩
  set q := sSup S with hqdef
  have hq1 : -κ ≤ q := le_csSup hSbdd hmS
  have hq2 : q ≤ κ := csSup_le hSne fun t ht => ht.1.2
  have hmeas : ∀ t, MeasurableSet {x | t ≤ Y x} := fun t => measurableSet_le measurable_const hY
  have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  -- (i) `Q(Y ≥ q) ≥ 1/β`
  have hG : 1 / β ≤ Q.real {x | q ≤ Y x} := by
    have hset : {x | q ≤ Y x} = ⋂ k : ℕ, {x | q - 1 / ((k : ℝ) + 1) ≤ Y x} := by
      ext x
      simp only [mem_setOf_eq, mem_iInter]
      constructor
      · intro h k; linarith [hpos k]
      · intro h
        by_contra hlt
        rw [not_le] at hlt
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
        linarith [h k]
    have hanti : Antitone fun k : ℕ => {x | q - 1 / ((k : ℝ) + 1) ≤ Y x} := by
      intro i j hij x hx
      simp only [mem_setOf_eq] at hx ⊢
      have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
        gcongr
      linarith
    have hlim := hanti.measure_iInter (μ := Q) (fun k => (hmeas _).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
    have hk : ∀ k : ℕ, ENNReal.ofReal (1 / β) ≤ Q {x | q - 1 / ((k : ℝ) + 1) ≤ Y x} := by
      intro k
      rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
      change 1 / β ≤ Q.real _
      have hlt : q - 1 / ((k : ℝ) + 1) < sSup S := by linarith [hpos k]
      obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hSne hlt
      exact hs.2.trans (measureReal_mono fun x hx => by
        simp only [mem_setOf_eq] at hx ⊢; linarith)
    have : ENNReal.ofReal (1 / β) ≤ Q {x | q ≤ Y x} := by rw [hset, hlim]; exact le_iInf hk
    rwa [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)] at this
  -- (ii) `Q(Y > q) ≤ 1/β`
  have hF : Q.real {x | q < Y x} ≤ 1 / β := by
    have hset : {x | q < Y x} = ⋃ k : ℕ, {x | q + 1 / ((k : ℝ) + 1) ≤ Y x} := by
      ext x
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · intro h
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 h)
        exact ⟨k, by linarith⟩
      · rintro ⟨k, hk⟩; linarith [hpos k]
    have hmono : Monotone fun k : ℕ => {x | q + 1 / ((k : ℝ) + 1) ≤ Y x} := by
      intro i j hij x hx
      simp only [mem_setOf_eq] at hx ⊢
      have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
        gcongr
      linarith
    have hlim := hmono.measure_iUnion (μ := Q)
    have hk : ∀ k : ℕ, Q {x | q + 1 / ((k : ℝ) + 1) ≤ Y x} ≤ ENNReal.ofReal (1 / β) := by
      intro k
      rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)]
      change Q.real _ ≤ 1 / β
      have hqt : q < q + 1 / ((k : ℝ) + 1) := by linarith [hpos k]
      by_cases htk : q + 1 / ((k : ℝ) + 1) ≤ κ
      · have hnot : q + 1 / ((k : ℝ) + 1) ∉ S := fun ht =>
          (not_le.2 hqt) (le_csSup hSbdd ht)
        have : ¬ (1 / β ≤ Q.real {x | q + 1 / ((k : ℝ) + 1) ≤ Y x}) := fun h =>
          hnot ⟨⟨by linarith, htk⟩, h⟩
        exact (not_le.1 this).le
      · have : {x | q + 1 / ((k : ℝ) + 1) ≤ Y x} = ∅ :=
          eq_empty_of_forall_notMem fun x hx => htk (le_trans hx (hYu x))
        rw [this, measureReal_empty]; positivity
    have : Q {x | q < Y x} ≤ ENNReal.ofReal (1 / β) := by rw [hset, hlim]; exact iSup_le hk
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) this
  -- the weight
  set A := {x | q < Y x} with hAdef
  set Bs := {x | Y x = q} with hBdef
  have hA : MeasurableSet A := measurableSet_lt measurable_const hY
  have hBs : MeasurableSet Bs := measurableSet_eq_fun hY measurable_const
  set F := Q.real A with hFdef
  set m := Q.real Bs with hmdef
  have hGsplit : Q.real {x | q ≤ Y x} = F + m := by
    have hun : {x | q ≤ Y x} = A ∪ Bs := by
      ext x
      simp only [hAdef, hBdef, mem_setOf_eq, mem_union]
      constructor
      · intro h; rcases h.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr h.symm
      · rintro (h | h)
        · exact h.le
        · exact h.ge
    have hdisj : Disjoint A Bs := disjoint_left.2 fun x hx1 hx2 => by
      simp only [hAdef, hBdef, mem_setOf_eq] at hx1 hx2; linarith
    rw [hun, measureReal_union hdisj hBs]
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hβF : β * F ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hF hβ0.le
    rwa [mul_one_div_cancel hβ0.ne'] at this
  have hβG : 1 ≤ β * (F + m) := by
    have := mul_le_mul_of_nonneg_left (hGsplit ▸ hG) hβ0.le
    rwa [mul_one_div_cancel hβ0.ne'] at this
  set c : ℝ := if m = 0 then 0 else (1 - β * F) / m with hcdef
  have hcm : c * m = 1 - β * F := by
    by_cases h : m = 0
    · simp only [hcdef, h, if_true, zero_mul]
      rw [h, add_zero] at hβG
      linarith
    · simp only [hcdef, h, if_false]
      field_simp
  have hc0 : 0 ≤ c := by
    by_cases h : m = 0
    · simp [hcdef, h]
    · simp only [hcdef, h, if_false]
      exact div_nonneg (by linarith) hm0
  have hcβ : c ≤ β := by
    by_cases h : m = 0
    · simp only [hcdef, h, if_true]; linarith
    · simp only [hcdef, h, if_false]
      rw [div_le_iff₀ (lt_of_le_of_ne hm0 (Ne.symm h))]
      nlinarith
  set g : 𝒳 → ℝ := fun x => A.indicator (fun _ => β) x + Bs.indicator (fun _ => c) x with hgdef
  have hYI : Integrable Y Q := Integrable.of_bound hY.aestronglyMeasurable κ
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hYb x)
  refine ⟨q, abs_le.2 ⟨hq1, hq2⟩, g, ?_, ?_, ?_, ?_⟩
  · exact (measurable_const.indicator hA).add (measurable_const.indicator hBs)
  · intro x
    by_cases h1 : q < Y x
    · have h2 : ¬ Y x = q := ne_of_gt h1
      have hxA : x ∈ A := h1
      have hxB : x ∉ Bs := h2
      simp only [hgdef, indicator_of_mem hxA, indicator_of_notMem hxB, add_zero]
      exact ⟨hβ0.le, le_rfl⟩
    · have hxA : x ∉ A := h1
      by_cases h2 : Y x = q
      · have hxB : x ∈ Bs := h2
        simp only [hgdef, indicator_of_notMem hxA, indicator_of_mem hxB, zero_add]
        exact ⟨hc0, hcβ⟩
      · have hxB : x ∉ Bs := h2
        simp only [hgdef, indicator_of_notMem hxA, indicator_of_notMem hxB, add_zero]
        exact ⟨le_rfl, hβ0.le⟩
  · rw [integral_add ((integrable_const β).indicator hA) ((integrable_const c).indicator hBs),
      integral_indicator_const _ hA, integral_indicator_const _ hBs, smul_eq_mul, smul_eq_mul]
    linarith [hcm]
  · have hpt : (fun x => g x * Y x) =
        fun x => A.indicator (fun x => β * Y x) x + Bs.indicator (fun _ => c * q) x := by
      funext x
      by_cases h1 : q < Y x
      · have hxA : x ∈ A := h1
        have hxB : x ∉ Bs := ne_of_gt h1
        simp only [hgdef, indicator_of_mem hxA, indicator_of_notMem hxB, add_zero]
      · have hxA : x ∉ A := h1
        by_cases h2 : Y x = q
        · have hxB : x ∈ Bs := h2
          simp only [hgdef, indicator_of_notMem hxA, indicator_of_mem hxB, zero_add]
          rw [h2]
        · have hxB : x ∉ Bs := h2
          simp only [hgdef, indicator_of_notMem hxA, indicator_of_notMem hxB, add_zero,
            zero_mul]
    have hpt2 : (fun x => max (Y x - q) 0) = fun x => A.indicator (fun x => Y x - q) x := by
      funext x
      by_cases h1 : q < Y x
      · have hxA : x ∈ A := h1
        rw [indicator_of_mem hxA, max_eq_left (sub_pos.2 h1).le]
      · have hxA : x ∉ A := h1
        rw [indicator_of_notMem hxA, max_eq_right (sub_nonpos.2 (not_lt.1 h1))]
    rw [hpt, hpt2, integral_add ((hYI.const_mul β).indicator hA)
      ((integrable_const _).indicator hBs), integral_indicator hA, integral_indicator hA,
      integral_indicator_const _ hBs, integral_const_mul,
      integral_sub hYI.integrableOn (integrable_const q), setIntegral_const, smul_eq_mul,
      smul_eq_mul]
    linear_combination q * hcm

/-! ### Regions -/

variable {φ : 𝒳 → H} {κ α : ℝ}

theorem integrable_smul_of_bound (Q : Measure 𝒳) [IsFiniteMeasure Q] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) {g : 𝒳 → ℝ} (hg : Measurable g) {β : ℝ}
    (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ β) : Integrable (fun x => g x • φ x) Q :=
  Integrable.of_bound (hg.stronglyMeasurable.smul hφ).aestronglyMeasurable (β * κ)
    (ae_of_all _ fun x => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hgb x).1]
      exact mul_le_mul (hgb x).2 (hκ x) (norm_nonneg _) ((hgb x).1.trans (hgb x).2))

theorem inner_integral_smul (Q : Measure 𝒳) [IsFiniteMeasure Q] [CompleteSpace H]
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {g : 𝒳 → ℝ} (hg : Measurable g) {β : ℝ}
    (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ β) (f : H) :
    inner ℝ f (∫ x, g x • φ x ∂Q) = ∫ x, g x * inner ℝ f (φ x) ∂Q := by
  rw [← integral_inner (integrable_smul_of_bound Q hφ hκ hg hgb) f]
  congr 1; funext x; rw [real_inner_smul_right]

theorem region_nonempty (Q : Measure 𝒳) [IsProbabilityMeasure Q] (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (region φ α Q).Nonempty := by
  refine ⟨∫ x, (1 : ℝ) • φ x ∂Q, fun _ => 1, measurable_const, fun _ => ⟨zero_le_one, ?_⟩,
    by simp, rfl⟩
  rw [le_div_iff₀ (by linarith)]; linarith

theorem region_convex (Q : Measure 𝒳) [IsFiniteMeasure Q] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) : Convex ℝ (region φ α Q) := by
  rintro _ ⟨g₁, hg₁, hb₁, hi₁, rfl⟩ _ ⟨g₂, hg₂, hb₂, hi₂, rfl⟩ a b ha hb hab
  have hI₁ := integrable_smul_of_bound Q hφ hκ hg₁ hb₁
  have hI₂ := integrable_smul_of_bound Q hφ hκ hg₂ hb₂
  have hgI : ∀ {g : 𝒳 → ℝ}, Measurable g → (∀ x, 0 ≤ g x ∧ g x ≤ 1 / (1 - α)) →
      Integrable g Q := fun {g} hg hb => Integrable.of_bound hg.aestronglyMeasurable (1 / (1 - α))
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]; exact (hb x).2)
  refine ⟨fun x => a * g₁ x + b * g₂ x, (hg₁.const_mul a).add (hg₂.const_mul b), fun x => ?_,
    ?_, ?_⟩
  · have h1 := hb₁ x; have h2 := hb₂ x
    constructor
    · exact add_nonneg (mul_nonneg ha h1.1) (mul_nonneg hb h2.1)
    · calc a * g₁ x + b * g₂ x ≤ a * (1 / (1 - α)) + b * (1 / (1 - α)) := by gcongr <;> tauto
        _ = 1 / (1 - α) := by rw [← add_mul, hab, one_mul]
  · rw [integral_add ((hgI hg₁ hb₁).const_mul a) ((hgI hg₂ hb₂).const_mul b), integral_const_mul,
      integral_const_mul, hi₁, hi₂, mul_one, mul_one, hab]
  · have e : ∀ x, (a * g₁ x + b * g₂ x) • φ x = a • (g₁ x • φ x) + b • (g₂ x • φ x) :=
      fun x => by rw [add_smul, smul_smul, smul_smul]
    simp_rw [e]
    rw [integral_add (f := fun x => a • (g₁ x • φ x)) (g := fun x => b • (g₂ x • φ x))
      (hI₁.smul a) (hI₂.smul b), integral_smul, integral_smul]

/-! ### The reduction -/

/-- One-sided `eq:hormander` + `eq:cvar` + `lem:tcompact`. -/
theorem infDist_region_le [CompleteSpace H] (Q₁ Q₂ : Measure 𝒳) [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure Q₂] (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ (f : H) (q : ℝ), ‖f‖ ≤ 1 → |q| ≤ κ →
      ∫ x, max (inner ℝ f (φ x) - q) 0 ∂Q₁ - ∫ x, max (inner ℝ f (φ x) - q) 0 ∂Q₂ ≤ S)
    {a : H} (ha : a ∈ region φ α Q₁) :
    Metric.infDist a (region φ α Q₂) ≤ 1 / (1 - α) * S := by
  set β := 1 / (1 - α) with hβdef
  have hβ1 : 1 ≤ β := by rw [hβdef, le_div_iff₀ (by linarith)]; linarith
  have hβ0 : 0 ≤ β := by linarith
  set K := closure (region φ α Q₂) with hK
  have hKne : K.Nonempty := (region_nonempty Q₂ hα0 hα1).closure
  have hKconv : Convex ℝ K := (region_convex Q₂ hφ hκ).closure
  have hKcomp : IsComplete K := isClosed_closure.isComplete
  obtain ⟨v, hvK, hv⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKcomp hKconv a
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hKconv hvK).1 hv
  rw [← Metric.infDist_closure]
  refine (Metric.infDist_le_dist_of_mem hvK).trans ?_
  rw [dist_eq_norm]
  by_cases hav : a - v = 0
  · rw [hav, norm_zero]; positivity
  have hnpos : 0 < ‖a - v‖ := norm_pos_iff.2 hav
  set f : H := ‖a - v‖⁻¹ • (a - v) with hfdef
  have hf1 : ‖f‖ ≤ 1 := by
    rw [hfdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnpos.ne']
  set Y : 𝒳 → ℝ := fun x => inner ℝ f (φ x) with hYdef
  have hYm : Measurable Y := (stronglyMeasurable_const.inner hφ).measurable
  have hYb : ∀ x, |Y x| ≤ κ := fun x =>
    (abs_real_inner_le_norm _ _).trans (by
      calc ‖f‖ * ‖φ x‖ ≤ 1 * κ := mul_le_mul hf1 (hκ x) (norm_nonneg _) zero_le_one
        _ = κ := one_mul κ)
  obtain ⟨q, hq, g₂, hg₂, hb₂, hi₂, hval₂⟩ := exists_cvar_witness Q₂ hYm hYb hβ1
  set b := ∫ x, g₂ x • φ x ∂Q₂ with hbdef
  have hbR : b ∈ region φ α Q₂ := ⟨g₂, hg₂, hb₂, hi₂, rfl⟩
  have hbv := hvi b (subset_closure hbR)
  obtain ⟨g₁, hg₁, hb₁, hi₁, rfl⟩ := ha
  have hfa : inner ℝ f (∫ x, g₁ x • φ x ∂Q₁) ≤ q + β * ∫ x, max (Y x - q) 0 ∂Q₁ := by
    rw [inner_integral_smul Q₁ hφ hκ hg₁ hb₁ f]
    exact integral_mul_le_cvar Q₁ hYm hYb hg₁ hb₁ hi₁ q
  have hfb : inner ℝ f b = q + β * ∫ x, max (Y x - q) 0 ∂Q₂ := by
    rw [hbdef, inner_integral_smul Q₂ hφ hκ hg₂ hb₂ f]; exact hval₂
  have hdiff : inner ℝ f (∫ x, g₁ x • φ x ∂Q₁ - b) ≤ β * S := by
    rw [inner_sub_right]
    have := hS f q hf1 hq
    have h3 : β * (∫ x, max (Y x - q) 0 ∂Q₁ - ∫ x, max (Y x - q) 0 ∂Q₂) ≤ β * S :=
      mul_le_mul_of_nonneg_left this hβ0
    linarith
  -- `‖a − v‖² ≤ ⟪a − v, a − b⟫ = ‖a − v‖ ⟪f, a − b⟫`
  set a := ∫ x, g₁ x • φ x ∂Q₁
  have hsq : ‖a - v‖ ^ 2 ≤ inner ℝ (a - v) (a - b) := by
    have : inner ℝ (a - v) (a - b) = inner ℝ (a - v) (a - v) - inner ℝ (a - v) (b - v) := by
      rw [← inner_sub_right]; congr 1; abel
    rw [this, real_inner_self_eq_norm_sq]; linarith
  have hfab : inner ℝ (a - v) (a - b) = ‖a - v‖ * inner ℝ f (a - b) := by
    rw [hfdef, real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul]
  rw [hfab] at hsq
  have : ‖a - v‖ ≤ inner ℝ f (a - b) := by
    rw [pow_two] at hsq
    exact le_of_mul_le_mul_left hsq hnpos
  linarith

/-- **`eq:reduction`** for two arbitrary probability measures. -/
theorem hausdorffDist_region_le [CompleteSpace H] (Q₁ Q₂ : Measure 𝒳) [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure Q₂] (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ (f : H) (q : ℝ), ‖f‖ ≤ 1 → |q| ≤ κ →
      |∫ x, max (inner ℝ f (φ x) - q) 0 ∂Q₁ - ∫ x, max (inner ℝ f (φ x) - q) 0 ∂Q₂| ≤ S) :
    Metric.hausdorffDist (region φ α Q₁) (region φ α Q₂) ≤ 1 / (1 - α) * S := by
  have hβ0 : 0 ≤ 1 / (1 - α) := by
    have : 0 < 1 - α := by linarith
    positivity
  refine Metric.hausdorffDist_le_of_infDist (mul_nonneg hβ0 hS0) (fun a ha => ?_) fun b hb => ?_
  · exact infDist_region_le Q₁ Q₂ hφ hκ hα0 hα1 hS0
      (fun f q hf hq => (le_abs_self _).trans (hS f q hf hq)) ha
  · exact infDist_region_le Q₂ Q₁ hφ hκ hα0 hα1 hS0
      (fun f q hf hq => by
        have := hS f q hf hq
        rw [abs_sub_comm] at this
        exact (le_abs_self _).trans this) hb

end StatFormal.TrimmedMMD.Concentration
