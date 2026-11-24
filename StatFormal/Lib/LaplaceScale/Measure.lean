import StatFormal.Lib.TVMeasure.Basic
import StatFormal.Lib.Distances.TV
import StatFormal.Wave31tq.Statements
import StatFormal.Wave30tp.Statements
import StatFormal.Archive.TrimmedMMD.Unconditional.Statements
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Laws under a measurable equivalence and under the rescaling `x ↦ x/σ` of the line (library, untrusted)

General facts on a measurable equivalence `e : α ≃ᵐ β` (any measurable spaces):

* `map_withDensity_equiv`: `(ρ.withDensity f).map e = (ρ.map e).withDensity (f ∘ e.symm)`;
* `absPQ_map_equiv`: the total variation measure of `P − Q` is carried by `e`: `|e_*P − e_*Q| = e_*|P − Q|` (through densities
  with respect to `P + Q`, Mathlib's Radon–Nikodym theorem, and `TVMeasure.totalVariation_eq_withDensity_abs`);
* `region_map_equiv`, `Dpop_map_equiv`: the trimmed kernel-mean regions, hence the trimmed distance `D_α`, are unchanged when the
  laws are carried by `e` and the feature map by `e⁻¹` (`ψ ∘ e = φ`): a trimming function `g` of `e_*P` is `g' ∘ e⁻¹` for the
  trimming function `g' = g ∘ e` of `P` (change of variables for Bochner integrals along `e`);
* `sampleLaw_map`: the law of the transformed two-sample `(f(X_i))_i, (f(Y_j))_j` is the two-sample law of `f_*P, f_*Q`.

On the real line, for `σ > 0`, the rescaling `x ↦ x/σ` (`scaleEquiv`):

* `map_div_withDensity`: the law with density `f` goes to the law with density `u ↦ σ f(σu)`;
* `ae_comp_mul`: a property holding Lebesgue-a.e. holds a.e. along `u ↦ σu` (`σ ≠ 0`; `volume((σ·)⁻¹'S) = |σ|⁻¹ volume(S)`).

Reference: the change-of-variables formula for image measures and densities (e.g. Bogachev, *Measure Theory*, Vol. I, §3.6);
the Jordan decomposition (Halmos, *Measure Theory*, §29).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.LaplaceScale

section Equiv

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A law with a density, carried by a measurable equivalence `e`, has the density `f ∘ e⁻¹` with respect to the image of the
reference measure. (Copied from `StatFormal.Foundations.GaussianEOTd.map_withDensity_equiv`, `Lib/GaussianEOTd/Measure.lean`.) -/
theorem map_withDensity_equiv (ρ : Measure α) (e : α ≃ᵐ β) (f : α → ℝ≥0∞) :
    (ρ.withDensity f).map e = (ρ.map e).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [e.map_apply, withDensity_apply _ (e.measurable hs), withDensity_apply _ hs, e.restrict_map, lintegral_map_equiv]
  refine lintegral_congr fun x => ?_
  simp

/-- The total variation measure `|P − Q|` is carried by a measurable equivalence: `|e_*P − e_*Q| = e_*|P − Q|` (finite `P, Q`);
stated for any `f` with `⇑e = f`. -/
theorem absPQ_map_equiv (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] (e : α ≃ᵐ β) {f : α → β} (hf : ⇑e = f) :
    StatFormal.Wave31tq.absPQ (P.map f) (Q.map f) = (StatFormal.Wave31tq.absPQ P Q).map f := by
  subst hf
  have hpm : Measurable fun x => (P.rnDeriv (P + Q) x).toReal := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hqm : Measurable fun x => (Q.rnDeriv (P + Q) x).toReal := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hp0 : ∀ x, 0 ≤ (P.rnDeriv (P + Q) x).toReal := fun _ => ENNReal.toReal_nonneg
  have hq0 : ∀ x, 0 ≤ (Q.rnDeriv (P + Q) x).toReal := fun _ => ENNReal.toReal_nonneg
  have hP := TVMeasure.eq_withDensity_add_left P Q
  have hQ := TVMeasure.eq_withDensity_add_right P Q
  have hPe : P.map e = ((P + Q).map e).withDensity
      (fun y => ENNReal.ofReal ((P.rnDeriv (P + Q) (e.symm y)).toReal)) := by
    conv_lhs => rw [hP]
    rw [map_withDensity_equiv]
    rfl
  have hQe : Q.map e = ((P + Q).map e).withDensity
      (fun y => ENNReal.ofReal ((Q.rnDeriv (P + Q) (e.symm y)).toReal)) := by
    conv_lhs => rw [hQ]
    rw [map_withDensity_equiv]
    rfl
  unfold StatFormal.Wave31tq.absPQ
  rw [TVMeasure.totalVariation_eq_withDensity_abs (hpm.comp e.symm.measurable) (hqm.comp e.symm.measurable)
      (fun _ => hp0 _) (fun _ => hq0 _) hPe hQe,
    TVMeasure.totalVariation_eq_withDensity_abs hpm hqm hp0 hq0 hP hQ, map_withDensity_equiv]
  rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The trimmed kernel-mean region is unchanged when the law is carried by a measurable equivalence `e` and the feature map by
`e⁻¹`: `𝒞_α(ψ; e_*P) = 𝒞_α(φ; P)` when `ψ ∘ e = φ` (stated for any `f` with `⇑e = f`). -/
theorem region_map_equiv (e : α ≃ᵐ β) {f : α → β} (hf : ⇑e = f) {φ : α → H} {ψ : β → H} (hψ : ∀ x, ψ (f x) = φ x)
    (a : ℝ) (P : Measure α) :
    StatFormal.TrimmedMMD.Concentration.region ψ a (P.map f) = StatFormal.TrimmedMMD.Concentration.region φ a P := by
  subst hf
  ext z
  simp only [StatFormal.TrimmedMMD.Concentration.region, mem_ofPred_eq, integral_map_equiv]
  constructor
  · rintro ⟨g, hg, hb, h1, hz⟩
    refine ⟨g ∘ e, hg.comp e.measurable, fun x => hb (e x), h1, ?_⟩
    rw [hz]
    simp only [Function.comp_apply, hψ]
  · rintro ⟨g, hg, hb, h1, hz⟩
    refine ⟨g ∘ e.symm, hg.comp e.symm.measurable, fun y => hb _, ?_, ?_⟩
    · simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using h1
    · rw [hz]
      simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply, hψ]

/-- The trimmed distance `D_α(P, Q)` is unchanged when both laws are carried by a measurable equivalence `e` and the feature
map by `e⁻¹` (`ψ ∘ e = φ`). -/
theorem Dpop_map_equiv (e : α ≃ᵐ β) {f : α → β} (hf : ⇑e = f) {φ : α → H} {ψ : β → H} (hψ : ∀ x, ψ (f x) = φ x)
    (P Q : Measure α) (a : ℝ) :
    StatFormal.TrimmedMMD.Unconditional.Dpop ψ (P.map f) (Q.map f) a = StatFormal.TrimmedMMD.Unconditional.Dpop φ P Q a := by
  simp only [StatFormal.TrimmedMMD.Unconditional.Dpop, region_map_equiv e hf hψ]

end Equiv

section Sample

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The two-sample law of the image laws `f_*P, f_*Q` is the image of the two-sample law of `P, Q` under the coordinatewise map
(`P, Q` and their images σ-finite). -/
theorem sampleLaw_map (P Q : Measure α) [SigmaFinite P] [SigmaFinite Q] {f : α → β} (hf : Measurable f)
    [SigmaFinite (P.map f)] [SigmaFinite (Q.map f)] (n m : ℕ) :
    StatFormal.Wave30tp.sampleLaw (P.map f) (Q.map f) n m =
      (StatFormal.Wave30tp.sampleLaw P Q n m).map (fun z => ((fun i => f (z.1 i)), (fun j => f (z.2 j)))) := by
  unfold StatFormal.Wave30tp.sampleLaw
  rw [← Measure.pi_map_pi (μ := fun _ : Fin n => P) (f := fun _ => f) (fun _ => hf.aemeasurable),
    ← Measure.pi_map_pi (μ := fun _ : Fin m => Q) (f := fun _ => f) (fun _ => hf.aemeasurable),
    Measure.map_prod_map _ _ (by fun_prop : Measurable fun (x : Fin n → α) (i : Fin n) => f (x i))
      (by fun_prop : Measurable fun (y : Fin m → α) (j : Fin m) => f (y j))]
  rfl

end Sample

section Scale

/-- The rescaling `x ↦ x/σ` of the line, `σ ≠ 0`, as a measurable equivalence (inverse `u ↦ σu`). -/
def scaleEquiv (σ : ℝ) (hσ : σ ≠ 0) : ℝ ≃ᵐ ℝ where
  toFun x := x / σ
  invFun u := σ * u
  left_inv x := by simp only; field_simp
  right_inv u := by simp only; field_simp
  measurable_toFun := measurable_id.div_const σ
  measurable_invFun := measurable_id.const_mul σ

@[simp] theorem coe_scaleEquiv (σ : ℝ) (hσ : σ ≠ 0) : ⇑(scaleEquiv σ hσ) = fun x => x / σ := rfl

@[simp] theorem scaleEquiv_symm_apply (σ : ℝ) (hσ : σ ≠ 0) (u : ℝ) : (scaleEquiv σ hσ).symm u = σ * u := rfl

/-- Lebesgue measure under `x ↦ x/σ`, `σ > 0`: `σ · volume`. -/
theorem map_volume_div {σ : ℝ} (hσ : 0 < σ) :
    (volume : Measure ℝ).map (fun x => x / σ) = ENNReal.ofReal σ • volume := by
  have h := Real.map_volume_mul_right (inv_ne_zero hσ.ne')
  simp only [inv_inv, abs_of_pos hσ] at h
  have e : (fun x : ℝ => x / σ) = (· * σ⁻¹) := by
    funext x
    rw [div_eq_mul_inv]
  rw [e, h]

/-- Rescaling a law with a density: for `σ > 0`, the image under `x ↦ x/σ` of the law with density `f` (with respect to
Lebesgue measure) has the density `u ↦ σ f(σu)`. -/
theorem map_div_withDensity {σ : ℝ} (hσ : 0 < σ) (f : ℝ → ℝ) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).map (fun x => x / σ) =
      volume.withDensity (fun u => ENNReal.ofReal (σ * f (σ * u))) := by
  rw [← coe_scaleEquiv σ hσ.ne', map_withDensity_equiv, coe_scaleEquiv, map_volume_div hσ, withDensity_smul_measure,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext u
  simp only [Function.comp_apply, scaleEquiv_symm_apply, Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_mul hσ.le]

/-- A property holding Lebesgue-almost everywhere holds almost everywhere along `u ↦ σu`, `σ ≠ 0`. -/
theorem ae_comp_mul {σ : ℝ} (hσ : σ ≠ 0) {p : ℝ → Prop} (h : ∀ᵐ x ∂volume, p x) : ∀ᵐ u ∂volume, p (σ * u) := by
  rw [ae_iff] at h ⊢
  have e : {u : ℝ | ¬ p (σ * u)} = (σ * ·) ⁻¹' {x | ¬ p x} := rfl
  rw [e, Real.volume_preimage_mul_left hσ, h, mul_zero]

end Scale

end StatFormal.LaplaceScale
