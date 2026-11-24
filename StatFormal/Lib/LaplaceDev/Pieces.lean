import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.EMetricSpace.BoundedVariation
import StatFormal.Lib.LaplaceDev.Arith

set_option linter.style.longLine false

/-!
# Set-integral pieces for deviation bounds on the line (library, untrusted)

General facts about a pair of laws `μ̃, μ` on `ℝ` (an empirical law and its population law in the application) used to
assemble a deviation bound `|∫ f d(μ̃ − μ)|` from bounds on intervals (trimmed-mmd, Lemma S4.25):

* `IntervalDev μ̃ μ ε ζ`: every interval `I` has `|μ̃(I) − μ(I)| ≤ (2μ(I)ε)^{1/2} + ζ` (the event of Lemma S4.23, `ε = x/n`,
  `ζ = c_x/n`); `LocalDev μ̃ μ ε ζ`: the localized deviation bound of Lemma S4.24 for every bounded interval and every
  `[0,1]`-valued `h` continuous on its closure, in terms of any bound `V` on its variation there;
* `integrable_of_bdd`, `abs_setIntegral_le`: bounded continuous functions are integrable for finite measures, and
  `|∫_S h dν| ≤ C ν(S)` when `|h| ≤ C`;
* `eVariationOn_const_sub_le`, `eVariationOn_sub_const_le`: `V(c − f) ≤ V(f)`, `V(f − c) ≤ V(f)`;
* `integral_eq_Ioi_add_Iic`, `setIntegral_Ioi_split`, `setIntegral_Iic_split`, `integral_window_split`: the splits of the line
  at `x₀` into `(x₀, x₀+w]`, `(x₀+w, x₀+K]`, `(x₀+K, ∞)` and `(x₀−w, x₀]`, `[x₀−K, x₀−w]`, `(−∞, x₀−K)`, and into the window
  `[x₀−K, x₀+K]` and the two half-lines off it;
* `setOf_lt_abs_sub`, `tails_le`: `{|z − x₀| > K}` is the union of the two half-lines, and on the interval event
  `μ̃(L₁) + μ(L₁) + μ̃(L₂) + μ(L₂) ≤ 2μ(|z − x₀| > K) + 2ε^{1/2} + 2ζ`, using `(2u)^{1/2} + (2v)^{1/2} ≤ 2(u+v)^{1/2}`.
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.LaplaceDev

/-- The interval deviation event in general form: `|μ̃(I) − μ(I)| ≤ (2μ(I)ε)^{1/2} + ζ` for every interval `I`
(`I.OrdConnected`). With `ε = x/n`, `ζ = c_x/n` it is the event of Lemma S4.23 of trimmed-mmd. -/
def IntervalDev (μt μ : Measure ℝ) (ε ζ : ℝ) : Prop :=
  ∀ I : Set ℝ, I.OrdConnected → |μt.real I - μ.real I| ≤ √(2 * μ.real I * ε) + ζ

/-- The localized deviation bound in general form (the conclusion of Lemma S4.24 of trimmed-mmd): for every bounded interval
`I`, every `h : ℝ → [0,1]` continuous on `Ī` and every bound `V ≥ 0` of its variation on `Ī`,
`|∫_I h d(μ̃ − μ)| ≤ (2(V+1)(∫_I h dμ)ε)^{1/2} + (V+1)ζ`. -/
def LocalDev (μt μ : Measure ℝ) (ε ζ : ℝ) : Prop :=
  ∀ (I : Set ℝ) (h : ℝ → ℝ) (V : ℝ), I.OrdConnected → Bornology.IsBounded I → (∀ z, 0 ≤ h z ∧ h z ≤ 1) →
    ContinuousOn h (closure I) → 0 ≤ V → eVariationOn h (closure I) ≤ ENNReal.ofReal V →
      |(∫ z in I, h z ∂μt) - ∫ z in I, h z ∂μ| ≤ √(2 * (V + 1) * (∫ z in I, h z ∂μ) * ε) + (V + 1) * ζ

section Pieces

variable {ν : Measure ℝ}

/-- A continuous function bounded by `C` is integrable for a finite measure. -/
theorem integrable_of_bdd [IsFiniteMeasure ν] {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ z, |f z| ≤ C) :
    Integrable f ν :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hC z)

/-- `|∫_S h dν| ≤ C ν(S)` when `|h| ≤ C`, for a finite measure. -/
theorem abs_setIntegral_le [IsFiniteMeasure ν] {f : ℝ → ℝ} {C : ℝ} (hC : ∀ z, |f z| ≤ C) (S : Set ℝ) :
    |∫ z in S, f z ∂ν| ≤ C * ν.real S := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := ν) (s := S) (f := f) (measure_lt_top ν S)
    (fun z _ => by rw [Real.norm_eq_abs]; exact hC z)
  rwa [Real.norm_eq_abs] at h

/-- `|∫_S h dν₁ − ∫_S h dν₂| ≤ ν₁(S) + ν₂(S)` when `|h| ≤ 1`. -/
theorem abs_setIntegral_sub_le {ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] {f : ℝ → ℝ}
    (hC : ∀ z, |f z| ≤ 1) (S : Set ℝ) :
    |(∫ z in S, f z ∂ν₁) - ∫ z in S, f z ∂ν₂| ≤ ν₁.real S + ν₂.real S := by
  have h1 := abs_setIntegral_le (ν := ν₁) hC S
  have h2 := abs_setIntegral_le (ν := ν₂) hC S
  calc |(∫ z in S, f z ∂ν₁) - ∫ z in S, f z ∂ν₂| ≤ |∫ z in S, f z ∂ν₁| + |∫ z in S, f z ∂ν₂| := abs_sub _ _
    _ ≤ _ := by linarith

/-- `V_s(c − f) ≤ V_s(f)`. -/
theorem eVariationOn_const_sub_le (f : ℝ → ℝ) (c : ℝ) (s : Set ℝ) :
    eVariationOn (fun z => c - f z) s ≤ eVariationOn f s := by
  have hL : LipschitzWith 1 (fun y : ℝ => c - y) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, show c - x - (c - y) = -(x - y) by ring, abs_neg]
  have h : eVariationOn (fun z => c - f z) s ≤ ((1 : NNReal) : ENNReal) * eVariationOn f s :=
    (hL.lipschitzOnWith (s := univ)).comp_eVariationOn_le (g := f) (s := s) (mapsTo_univ _ _)
  simpa using h

/-- `V_s(f − c) ≤ V_s(f)`. -/
theorem eVariationOn_sub_const_le (f : ℝ → ℝ) (c : ℝ) (s : Set ℝ) :
    eVariationOn (fun z => f z - c) s ≤ eVariationOn f s := by
  have hL : LipschitzWith 1 (fun y : ℝ => y - c) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, show x - c - (y - c) = x - y by ring]
  have h : eVariationOn (fun z => f z - c) s ≤ ((1 : NNReal) : ENNReal) * eVariationOn f s :=
    (hL.lipschitzOnWith (s := univ)).comp_eVariationOn_le (g := f) (s := s) (mapsTo_univ _ _)
  simpa using h

/-- `∫ f = ∫_{(x₀,∞)} f + ∫_{(−∞,x₀]} f`. -/
theorem integral_eq_Ioi_add_Iic [IsFiniteMeasure ν] {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ z, |f z| ≤ C)
    (x₀ : ℝ) : ∫ z, f z ∂ν = ∫ z in Ioi x₀, f z ∂ν + ∫ z in Iic x₀, f z ∂ν := by
  rw [← integral_add_compl measurableSet_Ioi (integrable_of_bdd hf hC), compl_Ioi]

/-- The split of `(x₀, ∞)` into `(x₀, x₀+w]`, `(x₀+w, x₀+K]` and `(x₀+K, ∞)` (`0 ≤ w ≤ K`). -/
theorem setIntegral_Ioi_split [IsFiniteMeasure ν] {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ} (hC : ∀ z, |h z| ≤ C)
    {x₀ w K : ℝ} (hw : 0 ≤ w) (hwK : w ≤ K) :
    ∫ z in Ioi x₀, h z ∂ν = ∫ z in Ioc x₀ (x₀ + w), h z ∂ν + ∫ z in Ioc (x₀ + w) (x₀ + K), h z ∂ν +
      ∫ z in Ioi (x₀ + K), h z ∂ν := by
  have hi := integrable_of_bdd (ν := ν) hh hC
  have e1 : Ioi x₀ = Ioc x₀ (x₀ + w) ∪ (Ioc (x₀ + w) (x₀ + K) ∪ Ioi (x₀ + K)) := by
    rw [Ioc_union_Ioi_eq_Ioi (by linarith), Ioc_union_Ioi_eq_Ioi (by linarith)]
  have d1 : Disjoint (Ioc (x₀ + w) (x₀ + K)) (Ioi (x₀ + K)) :=
    Set.disjoint_left.2 fun z h1 h2 => by rw [mem_Ioc] at h1; rw [mem_Ioi] at h2; linarith [h1.2]
  have d2 : Disjoint (Ioc x₀ (x₀ + w)) (Ioc (x₀ + w) (x₀ + K) ∪ Ioi (x₀ + K)) :=
    Set.disjoint_left.2 fun z h1 h2 => by
      rw [mem_Ioc] at h1
      rcases h2 with h2 | h2
      · rw [mem_Ioc] at h2; linarith [h1.2, h2.1]
      · rw [mem_Ioi] at h2; linarith [h1.2]
  rw [e1, setIntegral_union d2 (measurableSet_Ioc.union measurableSet_Ioi) hi.integrableOn hi.integrableOn,
    setIntegral_union d1 measurableSet_Ioi hi.integrableOn hi.integrableOn, add_assoc]

/-- The split of `(−∞, x₀]` into `(x₀−w, x₀]`, `[x₀−K, x₀−w]` and `(−∞, x₀−K)` (`0 ≤ w ≤ K`). -/
theorem setIntegral_Iic_split [IsFiniteMeasure ν] {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ} (hC : ∀ z, |h z| ≤ C)
    {x₀ w K : ℝ} (hw : 0 ≤ w) (hwK : w ≤ K) :
    ∫ z in Iic x₀, h z ∂ν = ∫ z in Ioc (x₀ - w) x₀, h z ∂ν + ∫ z in Icc (x₀ - K) (x₀ - w), h z ∂ν +
      ∫ z in Iio (x₀ - K), h z ∂ν := by
  have hi := integrable_of_bdd (ν := ν) hh hC
  have e1 : Iic x₀ = (Iio (x₀ - K) ∪ Icc (x₀ - K) (x₀ - w)) ∪ Ioc (x₀ - w) x₀ := by
    rw [Iio_union_Icc_eq_Iic (by linarith), Iic_union_Ioc_eq_Iic (by linarith)]
  have d1 : Disjoint (Iio (x₀ - K)) (Icc (x₀ - K) (x₀ - w)) :=
    Set.disjoint_left.2 fun z h1 h2 => by rw [mem_Iio] at h1; rw [mem_Icc] at h2; linarith [h2.1]
  have d2 : Disjoint (Iio (x₀ - K) ∪ Icc (x₀ - K) (x₀ - w)) (Ioc (x₀ - w) x₀) :=
    Set.disjoint_left.2 fun z h1 h2 => by
      rw [mem_Ioc] at h2
      rcases h1 with h1 | h1
      · rw [mem_Iio] at h1; linarith [h2.1]
      · rw [mem_Icc] at h1; linarith [h1.2, h2.1]
  rw [e1, setIntegral_union d2 measurableSet_Ioc hi.integrableOn hi.integrableOn,
    setIntegral_union d1 measurableSet_Icc hi.integrableOn hi.integrableOn]
  ring

/-- The split of the line into the window `[x₀−K, x₀+K]` and the half-lines `(−∞, x₀−K)`, `(x₀+K, ∞)` (`K ≥ 0`). -/
theorem integral_window_split [IsFiniteMeasure ν] {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ z, |f z| ≤ C)
    {x₀ K : ℝ} (hK : 0 ≤ K) :
    ∫ z, f z ∂ν = ∫ z in Icc (x₀ - K) (x₀ + K), f z ∂ν + ∫ z in Iio (x₀ - K), f z ∂ν + ∫ z in Ioi (x₀ + K), f z ∂ν := by
  have hi := integrable_of_bdd (ν := ν) hf hC
  have e1 : (Ioi (x₀ + K))ᶜ = Iio (x₀ - K) ∪ Icc (x₀ - K) (x₀ + K) := by
    rw [compl_Ioi, Iio_union_Icc_eq_Iic (by linarith)]
  have d1 : Disjoint (Iio (x₀ - K)) (Icc (x₀ - K) (x₀ + K)) :=
    Set.disjoint_left.2 fun z h1 h2 => by rw [mem_Iio] at h1; rw [mem_Icc] at h2; linarith [h2.1]
  rw [← integral_add_compl measurableSet_Ioi hi, e1,
    setIntegral_union d1 measurableSet_Icc hi.integrableOn hi.integrableOn]
  ring

/-- `{z | K < |z − x₀|} = (−∞, x₀−K) ∪ (x₀+K, ∞)`. -/
theorem setOf_lt_abs_sub (x₀ K : ℝ) : {z : ℝ | K < |z - x₀|} = Iio (x₀ - K) ∪ Ioi (x₀ + K) := by
  ext z
  change K < |z - x₀| ↔ z ∈ Iio (x₀ - K) ∪ Ioi (x₀ + K)
  simp only [mem_union, mem_Iio, mem_Ioi, lt_abs]
  constructor
  · rintro (h | h)
    · right; linarith
    · left; linarith
  · rintro (h | h)
    · right; linarith
    · left; linarith

/-- On the interval event, the two half-lines off the window carry `μ̃(L₁) + μ(L₁) + μ̃(L₂) + μ(L₂) ≤ 2π + 2ε^{1/2} + 2ζ`,
`π = μ(|z − x₀| > K)`. -/
theorem tails_le {μt μ : Measure ℝ} [IsProbabilityMeasure μt] [IsProbabilityMeasure μ] {ε ζ : ℝ}
    (hI : IntervalDev μt μ ε ζ) (x₀ : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    μt.real (Iio (x₀ - K)) + μ.real (Iio (x₀ - K)) + (μt.real (Ioi (x₀ + K)) + μ.real (Ioi (x₀ + K))) ≤
      2 * μ.real {z | K < |z - x₀|} + 2 * √ε + 2 * ζ := by
  have hL := (abs_le.1 (hI (Iio (x₀ - K)) ordConnected_Iio)).2
  have hR := (abs_le.1 (hI (Ioi (x₀ + K)) ordConnected_Ioi)).2
  have ha : 0 ≤ μ.real (Iio (x₀ - K)) := measureReal_nonneg
  have hb : 0 ≤ μ.real (Ioi (x₀ + K)) := measureReal_nonneg
  have hd : Disjoint (Iio (x₀ - K)) (Ioi (x₀ + K)) :=
    Set.disjoint_left.2 fun z h1 h2 => by rw [mem_Iio] at h1; rw [mem_Ioi] at h2; linarith
  have hπ : μ.real {z | K < |z - x₀|} = μ.real (Iio (x₀ - K)) + μ.real (Ioi (x₀ + K)) := by
    rw [setOf_lt_abs_sub, measureReal_union hd measurableSet_Ioi]
  have hab : μ.real (Iio (x₀ - K)) + μ.real (Ioi (x₀ + K)) ≤ 1 := hπ ▸ measureReal_le_one
  have hsq : √(2 * μ.real (Iio (x₀ - K)) * ε) + √(2 * μ.real (Ioi (x₀ + K)) * ε) ≤ 2 * √ε := by
    rw [Real.sqrt_mul (by positivity) ε, Real.sqrt_mul (by positivity) ε]
    have h1 := sqrt_two_mul_add_sqrt_two_mul_le ha hb
    have h2 : √(μ.real (Iio (x₀ - K)) + μ.real (Ioi (x₀ + K))) ≤ 1 := Real.sqrt_le_one.mpr hab
    have h3 := Real.sqrt_nonneg ε
    nlinarith
  linarith

end Pieces

end StatFormal.LaplaceDev
