import StatFormal.Wave30tp.Statements
import StatFormal.Lib.Concentration.HilbertMean
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Route: NOTE Lemma P1 (moments and ranges) and the §1 kernel constants

Untrusted proof material. Densities: `R = a · P` gives `∫ g dR = ∫ a g dP` (`integral_withDensity_eq_integral_smul`,
`ENNReal.ofReal = coe ∘ toNNReal`). `tr Cov_R ≤ D²/2` by the bias–variance identity
`E_R‖φ − φ(x)‖² = tr Cov_R + ‖μ_R − φ(x)‖²` integrated once more in `x`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped InnerProductSpace

namespace StatFormal.Wave30tp

section Density

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

theorem integral_of_isDensityLe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R P : Measure 𝒳} {α : ℝ} {a : 𝒳 → ℝ} (ha : IsDensityLe R P α a) (g : 𝒳 → E) :
    ∫ x, g x ∂R = ∫ x, a x • g x ∂P := by
  obtain ⟨ham, hab, hR⟩ := ha
  have hmeas : Measurable fun x => (a x).toNNReal := measurable_real_toNNReal.comp ham
  have h := integral_withDensity_eq_integral_smul (μ := P) hmeas g
  have hfun : (fun x => ((a x).toNNReal : ENNReal)) = fun x => ENNReal.ofReal (a x) := rfl
  rw [hfun, ← hR] at h
  rw [h]
  congr 1; ext x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (hab x).1]

theorem integral_density_eq_one {R P : Measure 𝒳} [IsProbabilityMeasure R] {α : ℝ} {a : 𝒳 → ℝ}
    (ha : IsDensityLe R P α a) : ∫ x, a x ∂P = 1 := by
  have h := integral_of_isDensityLe ha (fun _ => (1 : ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, one_smul] at h
  exact h.symm

theorem one_le_beta {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) : 1 ≤ 1 / (1 - α) := by
  rw [le_div_iff₀ (by linarith)]; linarith

end Density

section Hilbert

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem norm_integral_le_bound {R : Measure 𝒳} [IsProbabilityMeasure R] {φ : 𝒳 → H} {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) : ‖∫ y, φ y ∂R‖ ≤ κ :=
  StatFormal.Concentration.norm_integral_le_of_bound hκ

theorem bddAbove_dev {R : Measure 𝒳} [IsProbabilityMeasure R] {φ : 𝒳 → H} {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) : BddAbove (range fun x => ‖φ x - ∫ y, φ y ∂R‖) :=
  ⟨2 * κ, by
    rintro _ ⟨x, rfl⟩
    exact (norm_sub_le _ _).trans (by linarith [hκ x, norm_integral_le_bound (R := R) hκ])⟩

theorem le_rhoR {R : Measure 𝒳} [IsProbabilityMeasure R] {φ : 𝒳 → H} {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (x : 𝒳) : ‖φ x - ∫ y, φ y ∂R‖ ≤ rhoR φ R :=
  le_ciSup (bddAbove_dev hκ) x

theorem rhoR_le {R : Measure 𝒳} [IsProbabilityMeasure R] {φ : 𝒳 → H} {c : ℝ}
    (h : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ c) : rhoR φ R ≤ c := by
  have : Nonempty 𝒳 := nonempty_of_isProbabilityMeasure R
  exact ciSup_le h

theorem rhoR_nonneg {R : Measure 𝒳} [IsProbabilityMeasure R] {φ : 𝒳 → H} {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) : 0 ≤ rhoR φ R := by
  obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure R
  exact (norm_nonneg _).trans (le_rhoR hκ x)

/-- `‖φ(x) − μ_R‖ ≤ D` for every bound `D` on the oscillation of `φ`. -/
theorem norm_sub_integral_le {R : Measure 𝒳} [IsProbabilityMeasure R] {φ : 𝒳 → H}
    (hφ : StronglyMeasurable φ) {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {D : ℝ}
    (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (x : 𝒳) : ‖φ x - ∫ y, φ y ∂R‖ ≤ D := by
  have hint := StatFormal.Concentration.integrable_of_bound (P := R) hφ hκ
  have : φ x - ∫ y, φ y ∂R = ∫ y, (φ x - φ y) ∂R := by
    rw [integral_sub (integrable_const _) hint, integral_const, probReal_univ, one_smul]
  rw [this]
  simpa using norm_integral_le_of_norm_le_const (μ := R) (ae_of_all _ fun y => hD x y)

theorem trCov_eq {R : Measure 𝒳} [IsProbabilityMeasure R] {φ : 𝒳 → H} (hφ : StronglyMeasurable φ)
    {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) :
    trCov φ R = ∫ y, ‖φ y‖ ^ 2 ∂R - ‖∫ y, φ y ∂R‖ ^ 2 :=
  StatFormal.Concentration.integral_norm_sub_integral_sq hφ hκ

theorem integral_norm_sq_le {R : Measure 𝒳} [IsProbabilityMeasure R] {φ : 𝒳 → H} {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) : ∫ y, ‖φ y‖ ^ 2 ∂R ≤ κ ^ 2 := by
  calc ∫ y, ‖φ y‖ ^ 2 ∂R ≤ ∫ _y, κ ^ 2 ∂R :=
        integral_mono_of_nonneg (ae_of_all _ fun y => by positivity) (integrable_const _)
          (ae_of_all _ fun y => pow_le_pow_left₀ (norm_nonneg _) (hκ y) 2)
    _ = κ ^ 2 := by simp

theorem trCov_nonneg (φ : 𝒳 → H) (R : Measure 𝒳) : 0 ≤ trCov φ R :=
  integral_nonneg fun _ => by positivity

/-- Bias–variance: `E_R‖φ − φ(x)‖² = tr Cov_R(φ) + ‖μ_R − φ(x)‖²`. -/
theorem integral_norm_sub_point_sq {R : Measure 𝒳} [IsProbabilityMeasure R] {φ : 𝒳 → H}
    (hφ : StronglyMeasurable φ) {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (x : 𝒳) :
    ∫ y, ‖φ y - φ x‖ ^ 2 ∂R = trCov φ R + ‖∫ y, φ y ∂R - φ x‖ ^ 2 := by
  set ψ : 𝒳 → H := fun y => φ y - φ x
  have hψ : StronglyMeasurable ψ := hφ.sub stronglyMeasurable_const
  have hψb : ∀ y, ‖ψ y‖ ≤ 2 * κ := fun y =>
    (norm_sub_le _ _).trans (by linarith [hκ y, hκ x])
  have h := StatFormal.Concentration.integral_norm_sub_integral_sq (P := R) hψ hψb
  have hint := StatFormal.Concentration.integrable_of_bound (P := R) hφ hκ
  have hmean : ∫ y, ψ y ∂R = ∫ y, φ y ∂R - φ x := by
    simp only [ψ]
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
  have hcent : ∀ y, ψ y - ∫ z, ψ z ∂R = φ y - ∫ z, φ z ∂R := fun y => by
    rw [hmean]; simp only [ψ]; abel
  simp_rw [hcent] at h
  rw [hmean] at h
  change trCov φ R = ∫ y, ‖ψ y‖ ^ 2 ∂R - _ at h
  linarith

theorem trCov_le_half_sq {R : Measure 𝒳} [IsProbabilityMeasure R] {φ : 𝒳 → H}
    (hφ : StronglyMeasurable φ) {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {D : ℝ}
    (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) : trCov φ R ≤ D ^ 2 / 2 := by
  have hD0 : 0 ≤ D := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure R
    exact (norm_nonneg _).trans (hD x x)
  have hpt : ∀ x, trCov φ R + ‖∫ y, φ y ∂R - φ x‖ ^ 2 ≤ D ^ 2 := fun x => by
    rw [← integral_norm_sub_point_sq hφ hκ x]
    calc ∫ y, ‖φ y - φ x‖ ^ 2 ∂R ≤ ∫ _y, D ^ 2 ∂R :=
          integral_mono_of_nonneg (ae_of_all _ fun y => by positivity) (integrable_const _)
            (ae_of_all _ fun y => pow_le_pow_left₀ (norm_nonneg _) (hD y x) 2)
      _ = D ^ 2 := by simp
  have hint2 : Integrable (fun x => ‖∫ y, φ y ∂R - φ x‖ ^ 2) R :=
    Integrable.of_bound ((stronglyMeasurable_const.sub hφ).norm.pow 2).aestronglyMeasurable ((2 * κ) ^ 2)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _)
          ((norm_sub_le _ _).trans (by linarith [hκ x, norm_integral_le_bound (R := R) hκ])) 2)
  have hint : ∫ x, (trCov φ R + ‖∫ y, φ y ∂R - φ x‖ ^ 2) ∂R ≤ D ^ 2 := by
    calc ∫ x, (trCov φ R + ‖∫ y, φ y ∂R - φ x‖ ^ 2) ∂R ≤ ∫ _x, D ^ 2 ∂R :=
          integral_mono ((integrable_const _).add hint2) (integrable_const _) hpt
      _ = D ^ 2 := by simp
  rw [integral_add (integrable_const _) hint2, integral_const, probReal_univ, one_smul] at hint
  have hsame : ∫ x, ‖∫ y, φ y ∂R - φ x‖ ^ 2 ∂R = trCov φ R := by
    unfold trCov; congr 1; ext x; rw [norm_sub_rev]
  rw [hsame] at hint
  linarith

/-- `⟪φ x, μ_R⟫ = ∫ k(x,y) dR(y)`. -/
theorem inner_integral {R : Measure 𝒳} [IsProbabilityMeasure R] {φ : 𝒳 → H} (hφ : StronglyMeasurable φ)
    {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (x : 𝒳) :
    ⟪φ x, ∫ y, φ y ∂R⟫_ℝ = ∫ y, ⟪φ x, φ y⟫_ℝ ∂R :=
  (integral_inner (StatFormal.Concentration.integrable_of_bound hφ hκ) (φ x)).symm

end Hilbert

/-- Two weights in `[0, β]`: `‖p u − q u'‖ ≤ β D` when `‖u‖, ‖u'‖, ‖u − u'‖ ≤ D` (convexity, vertex values). -/
theorem norm_smul_sub_smul_le_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u u' : E)
    {p q β D : ℝ} (hp0 : 0 ≤ p) (hpβ : p ≤ β) (hq0 : 0 ≤ q) (hqβ : q ≤ β) (hu : ‖u‖ ≤ D) (hu' : ‖u'‖ ≤ D)
    (huu : ‖u - u'‖ ≤ D) : ‖p • u - q • u'‖ ≤ β * D := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hu
  rcases le_total q p with h | h
  · have e : p • u - q • u' = q • (u - u') + (p - q) • u := by
      rw [smul_sub, sub_smul]; abel
    rw [e]
    calc ‖q • (u - u') + (p - q) • u‖ ≤ ‖q • (u - u')‖ + ‖(p - q) • u‖ := norm_add_le _ _
      _ = q * ‖u - u'‖ + (p - q) * ‖u‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hq0,
            abs_of_nonneg (by linarith)]
      _ ≤ q * D + (p - q) * D :=
          add_le_add (mul_le_mul_of_nonneg_left huu hq0) (mul_le_mul_of_nonneg_left hu (by linarith))
      _ = p * D := by ring
      _ ≤ β * D := mul_le_mul_of_nonneg_right hpβ hD0
  · have e : p • u - q • u' = p • (u - u') - (q - p) • u' := by
      rw [smul_sub, sub_smul]; abel
    rw [e]
    calc ‖p • (u - u') - (q - p) • u'‖ ≤ ‖p • (u - u')‖ + ‖(q - p) • u'‖ := norm_sub_le _ _
      _ = p * ‖u - u'‖ + (q - p) * ‖u'‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp0,
            abs_of_nonneg (by linarith)]
      _ ≤ p * D + (q - p) * D :=
          add_le_add (mul_le_mul_of_nonneg_left huu hp0) (mul_le_mul_of_nonneg_left hu' (by linarith))
      _ = q * D := by ring
      _ ≤ β * D := mul_le_mul_of_nonneg_right hqβ hD0

/-! ### The claims -/

theorem plugin_moments_i : Claims.plugin_moments_i := by
  intro 𝒳 H _ _ _ _ φ κ α P R _ _ a hφ hκ hα0 hα1 ha
  set μR := ∫ z, φ z ∂R
  set β := 1 / (1 - α)
  have hint := StatFormal.Concentration.integrable_of_bound (P := R) hφ hκ
  refine ⟨?_, ?_, ?_⟩
  · rw [← integral_of_isDensityLe ha (fun x => φ x - μR), integral_sub hint (integrable_const _),
      integral_const, probReal_univ, one_smul, sub_self]
  · have hmb : ∀ x, ‖φ x - μR‖ ^ 2 ≤ (2 * κ) ^ 2 := fun x =>
      pow_le_pow_left₀ (norm_nonneg _)
        ((norm_sub_le _ _).trans (by linarith [hκ x, norm_integral_le_bound (R := R) hκ])) 2
    have hsm : StronglyMeasurable fun x => ‖φ x - μR‖ ^ 2 :=
      (hφ.sub stronglyMeasurable_const).norm.pow 2
    obtain ⟨ham, hab, hR⟩ := ha
    have hβ0 : 0 ≤ β := by positivity
    have i1 : Integrable (fun x => ‖a x • (φ x - μR)‖ ^ 2) P :=
      Integrable.of_bound ((ham.stronglyMeasurable.smul (hφ.sub stronglyMeasurable_const)).norm.pow 2
        ).aestronglyMeasurable ((β * (2 * κ)) ^ 2) (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (hab x).1, mul_pow]
          rw [mul_pow]
          exact mul_le_mul (pow_le_pow_left₀ (hab x).1 (hab x).2 2) (hmb x) (by positivity)
            (by positivity))
    have i2 : Integrable (fun x => β * (a x * ‖φ x - μR‖ ^ 2)) P :=
      (Integrable.of_bound (ham.stronglyMeasurable.mul hsm).aestronglyMeasurable (β * (2 * κ) ^ 2)
        (ae_of_all _ fun x => by
          change ‖a x * ‖φ x - μR‖ ^ 2‖ ≤ β * (2 * κ) ^ 2
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hab x).1 (by positivity))]
          exact mul_le_mul (hab x).2 (hmb x) (by positivity) hβ0)).const_mul β
    calc ∫ x, ‖a x • (φ x - μR)‖ ^ 2 ∂P ≤ ∫ x, β * (a x * ‖φ x - μR‖ ^ 2) ∂P := by
          refine integral_mono i1 i2 fun x => ?_
          simp only
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hab x).1, mul_pow]
          have : a x ^ 2 ≤ β * a x := by nlinarith [(hab x).1, (hab x).2]
          nlinarith [sq_nonneg ‖φ x - μR‖]
      _ = β * trCov φ R := by
          rw [integral_const_mul]
          congr 1
          unfold trCov
          rw [integral_of_isDensityLe ⟨ham, hab, hR⟩ (fun x => ‖φ x - ∫ y, φ y ∂R‖ ^ 2)]
          rfl
  · intro v hv
    exact mul_le_mul_of_nonneg_left (hv R inferInstance) (by positivity)

theorem plugin_moments_ii : Claims.plugin_moments_ii := by
  intro 𝒳 H _ _ _ _ φ κ α P R _ _ a hφ hκ hα0 hα1 ha
  set μR := ∫ z, φ z ∂R
  set β := 1 / (1 - α)
  obtain ⟨ham, hab, -⟩ := ha
  have hβ0 : 0 ≤ β := by positivity
  refine ⟨fun x => ?_, fun D hD x x' => ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hab x).1]
    exact mul_le_mul (hab x).2 (le_rhoR hκ x) (norm_nonneg _) hβ0
  · have hu : ‖φ x - μR‖ ≤ D := norm_sub_integral_le hφ hκ hD x
    have hu' : ‖φ x' - μR‖ ≤ D := norm_sub_integral_le hφ hκ hD x'
    have huu : ‖(φ x - μR) - (φ x' - μR)‖ ≤ D := by rw [sub_sub_sub_cancel_right]; exact hD x x'
    exact norm_smul_sub_smul_le_mul _ _ (hab x).1 (hab x).2 (hab x').1 (hab x').2 hu hu' huu

theorem plugin_moments_iii : Claims.plugin_moments_iii := by
  intro 𝒳 _ α P R _ _ a hα0 hα1 ha
  set β := 1 / (1 - α) with hβ
  have hβ1 : 1 ≤ β := one_le_beta hα0 hα1
  have hβ0 : 0 < β := by linarith
  have h1 := integral_density_eq_one ha
  obtain ⟨ham, hab, -⟩ := ha
  have hai : Integrable a P := Integrable.of_bound ham.aestronglyMeasurable β
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hab x).1]; exact (hab x).2)
  have hmean : ∫ x, (1 - a x) ∂P = 0 := by
    rw [integral_sub (integrable_const _) hai, integral_const, probReal_univ, h1]; simp
  refine ⟨hmean, fun x => ⟨by linarith [(hab x).2], by linarith [(hab x).1]⟩, ?_, ?_⟩
  · have hm : MemLp (fun x => 1 - a x) 2 P :=
      MemLp.of_bound (measurable_const.sub ham).aestronglyMeasurable β (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hab x).1, (hab x).2])
    rw [variance_eq_sub hm]
    have hm1 : P[fun x => 1 - a x] = 0 := hmean
    rw [hm1]
    have hsq : Integrable (fun x => (1 - a x) ^ 2) P := hm.integrable_sq
    have hpt : ∀ x, (1 - a x) ^ 2 ≤ 1 - 2 * a x + β * a x := fun x => by
      nlinarith [(hab x).1, (hab x).2]
    have jv1 : Integrable (fun x => 1 - 2 * a x) P := (integrable_const 1).sub (hai.const_mul 2)
    have jv : Integrable (fun x => 1 - 2 * a x + β * a x) P := jv1.add (hai.const_mul β)
    have := integral_mono hsq jv hpt
    rw [integral_add jv1 (hai.const_mul β),
      integral_sub (integrable_const 1) (hai.const_mul 2), integral_const_mul, integral_const_mul, h1]
      at this
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at this
    have e : P[(fun x => 1 - a x) ^ 2] = ∫ x, (1 - a x) ^ 2 ∂P := by simp [Pi.pow_apply]
    rw [e]
    nlinarith
  · intro l hl
    -- chord bound for `y ↦ e^{l y}` on `[1 − β, 1]`, with weight `θ = a/β` on the left end
    have hpt : ∀ x, exp (l * (1 - a x)) ≤
        (a x / β) * exp (l * (1 - β)) + (1 - a x / β) * exp l := fun x => by
      have hθ0 : 0 ≤ a x / β := div_nonneg (hab x).1 hβ0.le
      have hθ1 : a x / β ≤ 1 := by rw [div_le_one hβ0]; exact (hab x).2
      have hc := (convexOn_exp).2 (Set.mem_univ (l * (1 - β))) (Set.mem_univ l) hθ0
        (by linarith : 0 ≤ 1 - a x / β) (by ring)
      simp only [smul_eq_mul] at hc
      have harg : a x / β * (l * (1 - β)) + (1 - a x / β) * l = l * (1 - a x) := by
        field_simp; ring
      rw [harg] at hc
      exact hc
    have hie : Integrable (fun x => exp (l * (1 - a x))) P :=
      Integrable.of_bound
        (measurable_exp.comp (measurable_const.mul (measurable_const.sub ham))).aestronglyMeasurable
        (exp l) (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
          exact exp_le_exp.2 (by nlinarith [(hab x).1]))
    have hθi : Integrable (fun x => a x / β) P := hai.div_const β
    have j1 : Integrable (fun x => a x / β * exp (l * (1 - β))) P := hθi.mul_const _
    have j2 : Integrable (fun x => (1 - a x / β) * exp l) P :=
      ((integrable_const 1).sub hθi).mul_const _
    have j3 : Integrable (fun x => 1 - a x / β) P := (integrable_const 1).sub hθi
    have j12 : Integrable (fun x => a x / β * exp (l * (1 - β)) + (1 - a x / β) * exp l) P := j1.add j2
    refine (integral_mono hie j12 hpt).trans (le_of_eq ?_)
    rw [integral_add j1 j2, integral_mul_const, integral_mul_const,
      integral_sub (integrable_const 1) hθi, integral_div, h1]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    rw [hβ]
    field_simp

theorem plugin_moments_iv : Claims.plugin_moments_iv := by
  intro 𝒳 H _ _ _ _ φ κ R _ hφ hκ
  refine ⟨fun D hD => ⟨rhoR_le (norm_sub_integral_le hφ hκ hD), le_min ?_ (trCov_le_half_sq hφ hκ hD)⟩,
    fun hk hdiag => ?_⟩
  · rw [trCov_eq hφ hκ]
    linarith [integral_norm_sq_le (R := R) hκ, sq_nonneg ‖∫ y, φ y ∂R‖]
  · have hsq : ∀ x, ‖φ x‖ ^ 2 = κ ^ 2 := fun x => by rw [← real_inner_self_eq_norm_sq]; exact hdiag x
    refine ⟨?_, ?_⟩
    · rw [trCov_eq hφ hκ]
      simp_rw [hsq]; simp
    · set μR := ∫ y, φ y ∂R
      have hpt : ∀ x, ‖φ x - μR‖ ≤ √(κ ^ 2 + ‖μR‖ ^ 2) := fun x => by
        apply Real.le_sqrt_of_sq_le
        rw [norm_sub_sq_real, hsq]
        have : 0 ≤ ⟪φ x, μR⟫_ℝ := by
          rw [inner_integral hφ hκ x]
          exact integral_nonneg fun y => hk x y
        linarith
      have h1 := rhoR_le (R := R) hpt
      have h0 := rhoR_nonneg (R := R) hκ
      calc rhoR φ R ^ 2 ≤ (√(κ ^ 2 + ‖μR‖ ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = κ ^ 2 + ‖μR‖ ^ 2 := Real.sq_sqrt (by positivity)

theorem kernel_consts : Claims.kernel_consts := by
  intro 𝒳 H _ _ _ _ φ κ D hφ hκ hD
  refine ⟨⟨hD, Real.sqrt_nonneg _, fun R _ => ?_, fun R _ x => norm_sub_integral_le hφ hκ hD x⟩,
    fun x x' => (norm_sub_le _ _).trans (by linarith [hκ x, hκ x']), fun hk hdiag x x' => ?_⟩
  · rw [Real.sq_sqrt (le_min (sq_nonneg _) (by positivity))]
    exact (plugin_moments_iv 𝒳 H φ κ R hφ hκ).1 D hD |>.2
  · have hsq : ∀ x, ‖φ x‖ ^ 2 = κ ^ 2 := fun x => by rw [← real_inner_self_eq_norm_sq]; exact hdiag x
    have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x)
    have h2 : ‖φ x - φ x'‖ ^ 2 ≤ 2 * κ ^ 2 := by
      rw [norm_sub_sq_real, hsq, hsq]; linarith [hk x x']
    calc ‖φ x - φ x'‖ ≤ √(2 * κ ^ 2) := Real.le_sqrt_of_sq_le h2
      _ = √2 * κ := by rw [Real.sqrt_mul' _ (sq_nonneg κ), Real.sqrt_sq hκ0]

end StatFormal.Wave30tp
