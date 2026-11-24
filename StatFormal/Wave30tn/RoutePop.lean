import StatFormal.Wave30tn.Statements
import StatFormal.Lib.TrimmedMean.Population

/-!
# Route — wave 30tn: `lem:popthreshold` (untrusted)

1. First-order condition: for every trimming density `g'`, the point `∫((1−s)g + s g') φ dP − b` lies in
   `𝒞_α(P) − 𝒞_β(Q)` (`s ∈ (0,1]`), so `‖d‖² ≤ ‖d + s(a' − a)‖²` and `⟨d, a' − a⟩ ≥ 0`; by the reproducing property
   `∫ g' Z dP ≥ ∫ g Z dP`, `Z = ⟨d, φ⟩` (`foc`).
2. The bathtub density `ḡ = β̄ 1{Z < t} + θ 1{Z = t}` (`θ` fixing `∫ ḡ = 1`, `0 ≤ θ ≤ β̄` by the quantile property) is a
   trimming density; `(g − ḡ)(Z − t) ≥ 0` pointwise and its integral is `∫ gZ − ∫ ḡZ ≤ 0` by step 1, so it vanishes a.e.
   (instead of the paper's mass-transfer contradiction).
3. On `{Z < t}` this forces `g = β̄`, on `{Z > t}` it forces `g = 0`, `P`-a.e. The hypothesis `dist > 0` is not used.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace Pointwise

namespace StatFormal.Wave30tn

open StatFormal.TrimmedMMD.Concentration (region)
open StatFormal.TrimmedMMD.ZeroSet (IsTrimDensity)
open StatFormal.Foundations.TrimmedMean (inner_integral_smul measurable_inner_comp abs_inner_le)

/-- If `‖d‖² ≤ ‖d + s v‖²` for every `s ∈ (0,1]`, then `⟨d, v⟩ ≥ 0`. -/
lemma inner_nonneg_of_min {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {d v : H}
    (h : ∀ s : ℝ, 0 < s → s ≤ 1 → ‖d‖ ^ 2 ≤ ‖d + s • v‖ ^ 2) : 0 ≤ ⟪d, v⟫ := by
  by_contra hc
  push Not at hc
  set c := ⟪d, v⟫
  set N := ‖v‖ ^ 2
  have hN : 0 ≤ N := sq_nonneg _
  set s := min 1 (-c / (N + 1))
  have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) (by linarith))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsN : s * N ≤ -c := by
    have h1 : s ≤ -c / (N + 1) := min_le_right _ _
    have h2 : s * N ≤ -c / (N + 1) * N := mul_le_mul_of_nonneg_right h1 hN
    have h3 : -c / (N + 1) * N ≤ -c := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have key := h s hs0 hs1
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at key
  have : 0 ≤ s * (2 * c + s * N) := by nlinarith
  have := (mul_nonneg_iff_of_pos_left hs0).1 this
  linarith

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma trimDensity_bound {P : Measure 𝒳} {α : ℝ} {g : 𝒳 → ℝ} (hg : IsTrimDensity P α g) :
    ∀ x, |g x| ≤ 1 / (1 - α) := fun x => by rw [abs_of_nonneg (hg.2.1 x).1]; exact (hg.2.1 x).2

lemma integrable_smul_phi (P : Measure 𝒳) [IsFiniteMeasure P] {φ : 𝒳 → H} {κ : ℝ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) {g : 𝒳 → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C) :
    Integrable (fun x => g x • φ x) P :=
  Integrable.of_bound (hg.stronglyMeasurable.smul hφ).aestronglyMeasurable (C * κ) (ae_of_all _ fun x => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hgC x) (hκ x) (norm_nonneg _) ((abs_nonneg _).trans (hgC x)))

/-- Step 1: `g` minimises `g' ↦ ∫ g' Z dP` over the trimming densities. -/
lemma foc (P : Measure 𝒳) [IsProbabilityMeasure P] (Q : Measure 𝒳) {φ : 𝒳 → H} {κ α β : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα1 : α < 1) {d b : H} {g : 𝒳 → ℝ}
    (hmin : ∀ z ∈ region φ α P - region φ β Q, ‖d‖ ≤ ‖z‖) (hg : IsTrimDensity P α g)
    (hb : b ∈ region φ β Q) (hd : d = ∫ x, g x • φ x ∂P - b) {g' : 𝒳 → ℝ} (hg' : IsTrimDensity P α g') :
    ∫ x, g x * ⟪d, φ x⟫ ∂P ≤ ∫ x, g' x * ⟪d, φ x⟫ ∂P := by
  have hβ : 0 < 1 - α := by linarith
  set a := ∫ x, g x • φ x ∂P
  set a' := ∫ x, g' x • φ x ∂P
  have hI := integrable_smul_phi P hφ hκ hg.1 (trimDensity_bound hg)
  have hI' := integrable_smul_phi P hφ hκ hg'.1 (trimDensity_bound hg')
  have hstep : ∀ s : ℝ, 0 < s → s ≤ 1 → ‖d‖ ^ 2 ≤ ‖d + s • (a' - a)‖ ^ 2 := by
    intro s hs0 hs1
    set gs : 𝒳 → ℝ := fun x => (1 - s) * g x + s * g' x
    have hgs : IsTrimDensity P α gs := by
      refine ⟨(hg.1.const_mul _).add (hg'.1.const_mul _), fun x => ⟨?_, ?_⟩, ?_⟩
      · have := (hg.2.1 x).1; have := (hg'.2.1 x).1
        change 0 ≤ (1 - s) * g x + s * g' x; nlinarith
      · have := (hg.2.1 x).2; have := (hg'.2.1 x).2
        change (1 - s) * g x + s * g' x ≤ 1 / (1 - α); nlinarith
      · have hgi : Integrable g P := Integrable.of_bound hg.1.aestronglyMeasurable _
          (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact trimDensity_bound hg x)
        have hgi' : Integrable g' P := Integrable.of_bound hg'.1.aestronglyMeasurable _
          (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact trimDensity_bound hg' x)
        simp only [gs]
        rw [integral_add (hgi.const_mul _) (hgi'.const_mul _), integral_const_mul, integral_const_mul,
          hg.2.2, hg'.2.2]
        ring
    have hmem : ∫ x, gs x • φ x ∂P ∈ region φ α P := ⟨gs, hgs.1, hgs.2.1, hgs.2.2, rfl⟩
    have heq : ∫ x, gs x • φ x ∂P = a + s • (a' - a) := by
      have e : (fun x => gs x • φ x) = fun x => (1 - s) • (g x • φ x) + s • (g' x • φ x) := by
        funext x; simp only [gs, add_smul, smul_smul]
      rw [e, integral_add (f := fun x => (1 - s) • (g x • φ x)) (g := fun x => s • (g' x • φ x))
        (hI.smul (1 - s)) (hI'.smul s), integral_smul, integral_smul]
      simp only [a, a', smul_sub, sub_smul, one_smul]; abel
    have := hmin _ (Set.sub_mem_sub hmem hb)
    rw [heq, show a + s • (a' - a) - b = d + s • (a' - a) by rw [hd]; abel] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have h0 := inner_nonneg_of_min hstep
  rw [inner_sub_right] at h0
  rw [← inner_integral_smul P hφ hκ hg.1 (trimDensity_bound hg) d,
    ← inner_integral_smul P hφ hκ hg'.1 (trimDensity_bound hg') d]
  linarith

theorem popthreshold_route : Claims.popthreshold := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ α β t d a b g hφ hκ hα0 hα1 hβ0 hβ1 _hdist hmin hg ha hb hd ht1 ht2
  subst ha
  set Z : 𝒳 → ℝ := fun x => ⟪d, φ x⟫ with hZdef
  have hZm : Measurable Z := measurable_inner_comp hφ d
  have hZb : ∀ x, |Z x| ≤ ‖d‖ * κ := abs_inner_le hκ d
  have hβ' : 0 < 1 - α := by linarith
  set B := 1 / (1 - α) with hBdef
  have hB0 : 0 < B := by positivity
  set p1 := P.real {x | Z x < t}
  set p2 := P.real {x | Z x = t}
  have hle : P.real {x | Z x ≤ t} = p1 + p2 := by
    have hu : {x | Z x ≤ t} = {x | Z x < t} ∪ {x | Z x = t} := by
      ext x; simp only [mem_ofPred_eq, mem_union, le_iff_lt_or_eq]
    have hdisj : Disjoint {x | Z x < t} {x | Z x = t} := Set.disjoint_left.2 fun x hx hx' => by
      have h1 : Z x < t := hx
      have h2 : Z x = t := hx'
      linarith
    rw [hu, measureReal_union hdisj (measurableSet_eq_fun hZm measurable_const)]
  have hp2 : 0 ≤ p2 := measureReal_nonneg
  have hBp1 : B * p1 ≤ 1 := by rw [hBdef, div_mul_eq_mul_div, one_mul, div_le_one hβ']; exact ht1
  have hBp12 : 1 ≤ B * (p1 + p2) := by rw [hBdef, div_mul_eq_mul_div, one_mul, le_div_iff₀ hβ', one_mul, ← hle]; exact ht2
  -- the bathtub density
  set θ : ℝ := if p2 = 0 then 0 else (1 - B * p1) / p2 with hθdef
  have hθ : 0 ≤ θ ∧ θ ≤ B ∧ B * p1 + θ * p2 = 1 := by
    by_cases h0 : p2 = 0
    · simp only [hθdef, h0, ite_true, mul_zero, add_zero, le_refl, true_and]
      refine ⟨hB0.le, ?_⟩
      rw [h0, add_zero] at hBp12; linarith
    · have hp2' : 0 < p2 := lt_of_le_of_ne hp2 (Ne.symm h0)
      simp only [hθdef, h0, ite_false]
      refine ⟨div_nonneg (by linarith) hp2, ?_, ?_⟩
      · rw [div_le_iff₀ hp2']; nlinarith
      · field_simp; ring
  set gb : 𝒳 → ℝ := fun x => if Z x < t then B else if Z x = t then θ else 0 with hgbdef
  have hgbm : Measurable gb :=
    Measurable.ite (measurableSet_lt hZm measurable_const) measurable_const
      (Measurable.ite (measurableSet_eq_fun hZm measurable_const) measurable_const measurable_const)
  have hgb : IsTrimDensity P α gb := by
    refine ⟨hgbm, fun x => ?_, ?_⟩
    · simp only [gb]; split_ifs <;> constructor <;> linarith [hθ.1, hθ.2.1]
    · have e : gb = fun x => B * ({x | Z x < t}.indicator 1 x) + θ * ({x | Z x = t}.indicator 1 x) := by
        funext x; simp only [gb, Set.indicator, mem_ofPred_eq, Pi.one_apply]
        split_ifs <;> first | (exfalso; linarith) | simp
      simp only [e]
      rw [integral_add (f := fun x => B * {x | Z x < t}.indicator 1 x) (g := fun x => θ * {x | Z x = t}.indicator 1 x)
        ((integrable_const (1 : ℝ)).indicator (measurableSet_lt hZm measurable_const) |>.const_mul _)
        ((integrable_const (1 : ℝ)).indicator (measurableSet_eq_fun hZm measurable_const) |>.const_mul _),
        integral_const_mul, integral_const_mul,
        integral_indicator_one (measurableSet_lt hZm measurable_const),
        integral_indicator_one (measurableSet_eq_fun hZm measurable_const)]
      exact hθ.2.2
  -- step 1 at `ḡ`
  have h1 := foc P Q hφ hκ hα1 hmin hg hb hd hgb
  -- integrability
  have hbd : ∀ {g' : 𝒳 → ℝ}, IsTrimDensity P α g' → Integrable (fun x => g' x * Z x) P := fun {g'} hg' =>
    Integrable.of_bound (hg'.1.mul hZm).aestronglyMeasurable (B * (‖d‖ * κ)) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (trimDensity_bound hg' x) (hZb x) (abs_nonneg _) hB0.le)
  have hgi : ∀ {g' : 𝒳 → ℝ}, IsTrimDensity P α g' → Integrable g' P := fun {g'} hg' =>
    Integrable.of_bound hg'.1.aestronglyMeasurable _ (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact trimDensity_bound hg' x)
  -- the product
  set D : 𝒳 → ℝ := fun x => (g x - gb x) * (Z x - t) with hDdef
  have hDnn : ∀ x, 0 ≤ D x := fun x => by
    simp only [D, gb]
    have hg1 := (hg.2.1 x).1; have hg2 := (hg.2.1 x).2
    split_ifs with h1 h2
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · rw [h2, sub_self, mul_zero]
    · push Not at h1; have : t < Z x := lt_of_le_of_ne h1 (Ne.symm h2)
      exact mul_nonneg (by linarith) (by linarith)
  have hDint : ∫ x, D x ∂P = ∫ x, g x * Z x ∂P - ∫ x, gb x * Z x ∂P := by
    have e : D = fun x => (g x * Z x - gb x * Z x) - t * (g x - gb x) := by funext x; simp only [D]; ring
    simp only [e]
    rw [integral_sub (f := fun x => g x * Z x - gb x * Z x) (g := fun x => t * (g x - gb x))
        ((hbd hg).sub (hbd hgb)) (((hgi hg).sub (hgi hgb)).const_mul t),
      integral_sub (f := fun x => g x * Z x) (g := fun x => gb x * Z x) (hbd hg) (hbd hgb), integral_const_mul,
      integral_sub (f := g) (g := gb) (hgi hg) (hgi hgb), hg.2.2, hgb.2.2]
    ring
  have hDle : ∫ x, D x ∂P ≤ 0 := by rw [hDint]; linarith
  have hDI : Integrable D P := by
    have e : D = fun x => (g x * Z x - gb x * Z x) - t * (g x - gb x) := by funext x; simp only [D]; ring
    rw [e]; exact ((hbd hg).sub (hbd hgb)).sub (((hgi hg).sub (hgi hgb)).const_mul t)
  have hD0 : D =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg hDnn hDI).1
    (le_antisymm hDle (integral_nonneg hDnn))
  refine ⟨?_, ?_⟩
  · filter_upwards [hD0] with x hx hlt
    have hgbx : gb x = B := if_pos hlt
    have hx' : (g x - gb x) * (Z x - t) = 0 := hx
    rw [hgbx] at hx'
    rcases mul_eq_zero.1 hx' with h | h
    · linarith
    · exfalso; linarith
  · filter_upwards [hD0] with x hx hgt
    have hn1 : ¬ Z x < t := not_lt.2 hgt.le
    have hn2 : ¬ Z x = t := ne_of_gt hgt
    have hgbx : gb x = 0 := (if_neg hn1).trans (if_neg hn2)
    have hx' : (g x - gb x) * (Z x - t) = 0 := hx
    rw [hgbx, sub_zero] at hx'
    rcases mul_eq_zero.1 hx' with h | h
    · exact h
    · exfalso; linarith

end StatFormal.Wave30tn
