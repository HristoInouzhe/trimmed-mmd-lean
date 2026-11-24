import StatFormal.Wave31tr.Statements
import StatFormal.Lib.ExcessRamp.Bathtub
import StatFormal.Lib.ExcessRamp.Part
import StatFormal.Wave30tn.Proofs
import StatFormal.Archive.TrimmedMMD.Concentration.Region
import StatFormal.Archive.TrimmedMMD.Unconditional.Proofs

/-!
# Wave 31tr route (E1): the setting of Proposition 5.10 and Lemmas S4.17–S4.18 (untrusted)

The closest parts `P′ = (1−α)g·P` and `Q′ = (1−α)h·Q` of the nearest points `a = ∫ gφ dP`, `b = ∫ hφ dQ`, as the frozen
`trimMeasure P (fun x => (1 − α) * g x)`:

* `part_le`, `part_real_univ`, `part_finite`, `integral_part`, `inner_part`: `P′ ≤ P`, mass `1 − α`, `∫ f dP′ = ∫ (1−α)g f dP`,
  `∫ ⟪v, φ⟫ dP′ = (1−α)⟪v, a⟫`;
* `part_threshold_P`, `part_threshold_Q`: the bathtub conditions (Lemma S4.17 (b)) from the certified `Wave30tn.popthreshold`
  (for `Q` applied to `(Q, P, b − a)`, an `α`-quantile `u` of `f⋆(Y)` giving the `(1−α)`-quantile `−‖a−b‖u` of `⟪b − a, φ(Y)⟫`);
* `parts_inner_diff`: `∫ f⋆ dP′ − ∫ f⋆ dQ′ = (1−α)‖a − b‖`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31tr.RouteExcess

open StatFormal.Wave30tq StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.ZeroSet

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Basic facts on the witness direction -/

/-- `setDist` is symmetric. -/
lemma setDist_comm (A B : Set H) : setDist A B = setDist B A := by
  unfold setDist
  congr 1
  ext r
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨b, hb, a, ha, norm_sub_rev _ _⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨b, hb, a, ha, norm_sub_rev _ _⟩

/-- The unit direction has norm one. -/
lemma norm_dir {e : H} (he : 0 < ‖e‖) : ‖‖e‖⁻¹ • e‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ he.ne']

/-- `⟪e, z⟫ = ‖e‖ ⟪‖e‖⁻¹ e, z⟫`. -/
lemma inner_eq_norm_mul_dir {e : H} (he : 0 < ‖e‖) (z : H) : ⟪e, z⟫_ℝ = ‖e‖ * ⟪‖e‖⁻¹ • e, z⟫_ℝ := by
  rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ he.ne', one_mul]

/-- The witness function is measurable. -/
lemma measurable_wit {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) (v : H) : Measurable fun x => ⟪v, φ x⟫_ℝ :=
  (stronglyMeasurable_const.inner hφ).measurable

/-- The witness function of a unit direction is bounded by `κ`. -/
lemma abs_wit_le {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {v : H} (hv : ‖v‖ = 1) (x : 𝒳) :
    |⟪v, φ x⟫_ℝ| ≤ κ :=
  (abs_real_inner_le_norm _ _).trans (by rw [hv, one_mul]; exact hκ x)

/-- A nearest pair `‖a − b‖ = D_α` is a minimal-norm element of `𝒞_α(P) − 𝒞_α(Q)`. -/
lemma min_norm_of_nearest {φ : 𝒳 → H} {P Q : Measure 𝒳} {α : ℝ} {a b : H} (hab : ‖a - b‖ = Dpop φ P Q α) :
    ∀ z ∈ region φ α P - region φ α Q, ‖a - b‖ ≤ ‖z‖ := by
  rintro _ ⟨a', ha', b', hb', rfl⟩
  rw [hab]; exact setDist_le_norm ha' hb'

/-! ### The closest parts -/

section Part

variable {P : Measure 𝒳} [IsProbabilityMeasure P] {α : ℝ} {g : 𝒳 → ℝ}

lemma part_dens_nonneg (hα1 : α < 1) (hg : IsTrimDensity P α g) (x : 𝒳) : 0 ≤ (1 - α) * g x :=
  mul_nonneg (by linarith) (hg.2.1 x).1

lemma part_dens_le_one (hα1 : α < 1) (hg : IsTrimDensity P α g) (x : 𝒳) : (1 - α) * g x ≤ 1 := by
  have h := (hg.2.1 x).2
  have h1 : 0 < 1 - α := by linarith
  calc (1 - α) * g x ≤ (1 - α) * (1 / (1 - α)) := mul_le_mul_of_nonneg_left h h1.le
    _ = 1 := by field_simp

/-- The closest part is a part: `P′ ≤ P`. -/
lemma part_le (hα1 : α < 1) (hg : IsTrimDensity P α g) : (trimMeasure P fun x => (1 - α) * g x) ≤ P :=
  StatFormal.ExcessRamp.withDensity_ofReal_le P (part_dens_le_one hα1 hg)

lemma part_finite (hα1 : α < 1) (hg : IsTrimDensity P α g) :
    IsFiniteMeasure (trimMeasure P fun x => (1 - α) * g x) :=
  isFiniteMeasure_of_le P (part_le hα1 hg)

/-- The closest part has mass `1 − α`. -/
lemma part_real_univ (hα1 : α < 1) (hg : IsTrimDensity P α g) :
    (trimMeasure P fun x => (1 - α) * g x).real univ = 1 - α := by
  rw [trimMeasure, StatFormal.ExcessRamp.withDensity_ofReal_real_univ P (hg.1.const_mul (1 - α))
    (part_dens_nonneg hα1 hg) (part_dens_le_one hα1 hg), integral_const_mul, hg.2.2, mul_one]

/-- Integrals against the closest part. -/
lemma integral_part (hα1 : α < 1) (hg : IsTrimDensity P α g) (f : 𝒳 → ℝ) :
    ∫ x, f x ∂(trimMeasure P fun x => (1 - α) * g x) = ∫ x, (1 - α) * g x * f x ∂P :=
  StatFormal.ExcessRamp.integral_withDensity_ofReal P (hg.1.const_mul (1 - α)) (part_dens_nonneg hα1 hg) f

/-- `∫ ⟪v, φ⟫ dP′ = (1−α)⟪v, ∫ gφ dP⟫`. -/
lemma inner_part [CompleteSpace H] {φ : 𝒳 → H} {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hα1 : α < 1) (hg : IsTrimDensity P α g) (v : H) :
    ∫ x, ⟪v, φ x⟫_ℝ ∂(trimMeasure P fun x => (1 - α) * g x) = (1 - α) * ⟪v, ∫ x, g x • φ x ∂P⟫_ℝ := by
  rw [integral_part hα1 hg, inner_integral_smul P hφ hκ hg.1 hg.2.1 v, ← integral_const_mul]
  congr 1; funext x; ring

end Part

/-! ### The bathtub conditions (Lemma S4.17 (b)) -/

/-- The bathtub conditions for `P′` at a `(1−α)`-quantile `t` of `f⋆(X)`: `P′ = P` on `{f⋆ < t}` and `P′({f⋆ > t}) = 0`. -/
theorem part_threshold_P [CompleteSpace H] {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {φ : 𝒳 → H} {κ α : ℝ} {a b : H} {g : 𝒳 → ℝ} {t : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hD : 0 < Dpop φ P Q α) (hg : IsTrimDensity P α g) (ha : a = ∫ x, g x • φ x ∂P)
    (hb : b ∈ region φ α Q) (hab : ‖a - b‖ = Dpop φ P Q α)
    (ht : IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) t) :
    (trimMeasure P fun x => (1 - α) * g x).restrict {x | ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ < t} =
        P.restrict {x | ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ < t} ∧
      (trimMeasure P fun x => (1 - α) * g x) {x | t < ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ} = 0 := by
  set c := ‖a - b‖ with hc
  set F : 𝒳 → ℝ := fun x => ⟪c⁻¹ • (a - b), φ x⟫_ℝ with hF
  have hc0 : 0 < c := hab ▸ hD
  have hFm : Measurable F := measurable_wit hφ _
  have key : ∀ x, ⟪a - b, φ x⟫_ℝ = c * F x := fun x => inner_eq_norm_mul_dir hc0 (φ x)
  have hS1 : {x | ⟪a - b, φ x⟫_ℝ < c * t} = {x | F x < t} := by
    ext x; simp only [mem_ofPred_eq, key, mul_lt_mul_iff_right₀ hc0]
  have hS2 : {x | ⟪a - b, φ x⟫_ℝ ≤ c * t} = {x | F x ≤ t} := by
    ext x; simp only [mem_ofPred_eq, key, mul_le_mul_iff_right₀ hc0]
  obtain ⟨h1, h2⟩ := StatFormal.Wave30tn.popthreshold 𝒳 H P Q φ κ α α (c * t) (a - b) a b g hφ hκ hα0 hα1 hα0 hα1
    hD (min_norm_of_nearest hab) hg ha hb rfl (by rw [hS1]; exact ht.1) (by rw [hS2]; exact ht.2)
  have hm1 : MeasurableSet {x | F x < t} := measurableSet_lt hFm measurable_const
  have hm2 : MeasurableSet {x | t < F x} := measurableSet_lt measurable_const hFm
  have h1α : (1 - α) ≠ 0 := by linarith
  refine ⟨?_, ?_⟩
  · rw [trimMeasure, restrict_withDensity hm1]
    have hae : (fun x => ENNReal.ofReal ((1 - α) * g x)) =ᵐ[P.restrict {x | F x < t}] 1 := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hm1]
      filter_upwards [h1] with x hx hxS
      have hxS' : ⟪a - b, φ x⟫_ℝ < c * t := by rw [key]; exact mul_lt_mul_of_pos_left hxS hc0
      rw [hx hxS', Pi.one_apply, mul_one_div_cancel h1α, ENNReal.ofReal_one]
    rw [withDensity_congr_ae hae, withDensity_one]
  · rw [trimMeasure, withDensity_apply _ hm2]
    have hae : ∀ᵐ x ∂P, x ∈ {x | t < F x} → ENNReal.ofReal ((1 - α) * g x) = 0 := by
      filter_upwards [h2] with x hx hxS
      have hxS' : c * t < ⟪a - b, φ x⟫_ℝ := by rw [key]; exact mul_lt_mul_of_pos_left hxS hc0
      rw [hx hxS', mul_zero, ENNReal.ofReal_zero]
    rw [setLIntegral_congr_fun_ae hm2 hae, lintegral_zero]

/-- The bathtub conditions for `Q′` at an `α`-quantile `u` of `f⋆(Y)`: `Q′ = Q` on `{f⋆ > u}` and `Q′({f⋆ < u}) = 0`. -/
theorem part_threshold_Q [CompleteSpace H] {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {φ : 𝒳 → H} {κ α : ℝ} {a b : H} {h : 𝒳 → ℝ} {u : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hD : 0 < Dpop φ P Q α) (hh : IsTrimDensity Q α h) (hb : b = ∫ y, h y • φ y ∂Q)
    (ha : a ∈ region φ α P) (hab : ‖a - b‖ = Dpop φ P Q α)
    (hu : IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α u) :
    (trimMeasure Q fun y => (1 - α) * h y).restrict {y | u < ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ} =
        Q.restrict {y | u < ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ} ∧
      (trimMeasure Q fun y => (1 - α) * h y) {y | ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ < u} = 0 := by
  have hmin : ∀ z ∈ region φ α Q - region φ α P, ‖b - a‖ ≤ ‖z‖ := by
    rintro _ ⟨b', hb', a', ha', rfl⟩
    rw [norm_sub_rev b a, norm_sub_rev b' a']
    exact min_norm_of_nearest hab _ ⟨a', ha', b', hb', rfl⟩
  set c := ‖a - b‖ with hc
  set F : 𝒳 → ℝ := fun x => ⟪c⁻¹ • (a - b), φ x⟫_ℝ with hF
  have hc0 : 0 < c := hab ▸ hD
  have hFm : Measurable F := measurable_wit hφ _
  have key : ∀ x, ⟪b - a, φ x⟫_ℝ = -c * F x := fun x => by
    rw [← neg_sub, inner_neg_left, inner_eq_norm_mul_dir hc0 (φ x)]; ring
  have hS1 : {x | ⟪b - a, φ x⟫_ℝ < -c * u} = {x | u < F x} := by
    ext x; simp only [mem_ofPred_eq, key, neg_mul, neg_lt_neg_iff, mul_lt_mul_iff_right₀ hc0]
  have hS2 : {x | ⟪b - a, φ x⟫_ℝ ≤ -c * u} = {x | u ≤ F x} := by
    ext x; simp only [mem_ofPred_eq, key, neg_mul, neg_le_neg_iff, mul_le_mul_iff_right₀ hc0]
  have hm0 : MeasurableSet {x | F x ≤ u} := measurableSet_le hFm measurable_const
  have hm1 : MeasurableSet {x | u < F x} := measurableSet_lt measurable_const hFm
  have hm2 : MeasurableSet {x | F x < u} := measurableSet_lt hFm measurable_const
  have hq1 : Q.real {x | u < F x} ≤ 1 - α := by
    have : {x | u < F x} = {x | F x ≤ u}ᶜ := by ext x; simp
    rw [this, probReal_compl_eq_one_sub hm0]; linarith [hu.2]
  have hq2 : 1 - α ≤ Q.real {x | u ≤ F x} := by
    have : {x | u ≤ F x} = {x | F x < u}ᶜ := by ext x; simp
    rw [this, probReal_compl_eq_one_sub hm2]; linarith [hu.1]
  have hD' : 0 < setDist (region φ α Q) (region φ α P) := by rw [setDist_comm]; exact hD
  obtain ⟨h1, h2⟩ := StatFormal.Wave30tn.popthreshold 𝒳 H Q P φ κ α α (-c * u) (b - a) b a h hφ hκ hα0 hα1 hα0 hα1
    hD' hmin hh hb ha rfl (by rw [hS1]; exact hq1) (by rw [hS2]; exact hq2)
  have h1α : (1 - α) ≠ 0 := by linarith
  refine ⟨?_, ?_⟩
  · rw [trimMeasure, restrict_withDensity hm1]
    have hae : (fun x => ENNReal.ofReal ((1 - α) * h x)) =ᵐ[Q.restrict {x | u < F x}] 1 := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hm1]
      filter_upwards [h1] with x hx hxS
      have hxS' : ⟪b - a, φ x⟫_ℝ < -c * u := by
        rw [key, neg_mul, neg_mul, neg_lt_neg_iff]; exact mul_lt_mul_of_pos_left hxS hc0
      rw [hx hxS', Pi.one_apply, mul_one_div_cancel h1α, ENNReal.ofReal_one]
    rw [withDensity_congr_ae hae, withDensity_one]
  · rw [trimMeasure, withDensity_apply _ hm2]
    have hae : ∀ᵐ x ∂Q, x ∈ {x | F x < u} → ENNReal.ofReal ((1 - α) * h x) = 0 := by
      filter_upwards [h2] with x hx hxS
      have hxS' : -c * u < ⟪b - a, φ x⟫_ℝ := by
        rw [key, neg_mul, neg_mul, neg_lt_neg_iff]; exact mul_lt_mul_of_pos_left hxS hc0
      rw [hx hxS', mul_zero, ENNReal.ofReal_zero]
    rw [setLIntegral_congr_fun_ae hm2 hae, lintegral_zero]

/-- `∫ f⋆ dP′ − ∫ f⋆ dQ′ = (1−α)‖a − b‖`. -/
theorem parts_inner_diff [CompleteSpace H] {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {φ : 𝒳 → H} {κ α : ℝ} {a b : H} {g h : 𝒳 → ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hα1 : α < 1) (hg : IsTrimDensity P α g) (ha : a = ∫ x, g x • φ x ∂P) (hh : IsTrimDensity Q α h)
    (hb : b = ∫ y, h y • φ y ∂Q) (hab0 : 0 < ‖a - b‖) :
    (∫ x, ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ ∂(trimMeasure P fun x => (1 - α) * g x)) -
        (∫ y, ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ ∂(trimMeasure Q fun y => (1 - α) * h y)) = (1 - α) * ‖a - b‖ := by
  rw [inner_part hφ hκ hα1 hg, inner_part hφ hκ hα1 hh, ← ha, ← hb, ← mul_sub, ← inner_sub_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

end StatFormal.Wave31tr.RouteExcess
