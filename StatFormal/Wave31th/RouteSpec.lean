import StatFormal.Wave31th.RouteCore
import StatFormal.Wave31tc.Statements

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Wave 31th, route: the `d = 1` specialisation check (untrusted proof file)

The frozen `Claims.qdens_euclid` at `d = 1` implies the frozen, certified `StatFormal.Wave31tc.Claims.qdens_univariate` (`rem:qdens (v3)`, `d = 1`):
transport along `x ↦ x 0 : EuclideanSpace ℝ (Fin 1) ≃ ℝ` (volume preserving, carrying the filter `comap ‖·‖ atTop` to `atBot ⊔ atTop` and
`fderiv ℝ (h ∘ e) x ≠ 0` to `deriv h (x 0) ≠ 0`). This is the formal content of "the statement specialises to the certified `d = 1`
statements of Wave 31tc"; it is not a target (the earlier claim is certified in its own wave).
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave31th

abbrev E1 := EuclideanSpace ℝ (Fin 1)

/-- `x ↦ x 0 : ℝ^1 ≃ ℝ` as a measurable equivalence. -/
def e1 : E1 ≃ᵐ ℝ := (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

theorem e1_apply (x : E1) : e1 x = x 0 := rfl

theorem e1_mp : MeasurePreserving e1 (volume : Measure E1) (volume : Measure ℝ) :=
  (volume_preserving_funUnique (Fin 1) ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1))

theorem norm_e1 (x : E1) : ‖x‖ = |e1 x| := by
  rw [EuclideanSpace.norm_eq]
  simp [e1_apply, Real.sqrt_sq_eq_abs]

theorem decay_transport (h : ℝ → ℝ) (h1 : Tendsto h atTop (𝓝 0)) (h2 : Tendsto h atBot (𝓝 0)) :
    Tendsto (h ∘ e1) (comap (fun x : E1 => ‖x‖) atTop) (𝓝 0) := by
  have hh : Tendsto h (comap abs atTop) (𝓝 0) := by
    rw [comap_abs_atTop]
    exact tendsto_sup.mpr ⟨h2, h1⟩
  have hπ : Tendsto e1 (comap (fun x : E1 => ‖x‖) atTop) (comap abs atTop) := by
    rw [tendsto_comap_iff]
    have : (abs ∘ e1 : E1 → ℝ) = fun x => ‖x‖ := by
      funext x; simp [Function.comp, norm_e1]
    rw [this]
    exact tendsto_comap
  exact hh.comp hπ

theorem fderiv_transport (h : ℝ → ℝ) (hd : Differentiable ℝ h) (x : E1) (hne : deriv h (e1 x) ≠ 0) :
    fderiv ℝ (h ∘ e1) x ≠ 0 := by
  let π : E1 →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hπ : ∀ y, π y = e1 y := fun y => rfl
  have hfun : (h ∘ e1) = h ∘ π := by funext y; simp [hπ]
  have hder : HasFDerivAt (h ∘ π) ((fderiv ℝ h (π x)).comp π) x :=
    (hd (π x)).hasFDerivAt.comp x π.hasFDerivAt
  rw [hfun, hder.fderiv]
  intro hz
  have := congrArg (fun L => L (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) hz
  simp [π] at this
  exact hne this

/-- `qdens_euclid` at `d = 1` implies the certified univariate claim of Wave 31tc. -/
theorem qdens_univariate_of_euclid (hE : Claims.qdens_euclid) :
    StatFormal.Wave31tc.Claims.qdens_univariate := by
  intro h p U t hC hTop hBot ht hex hder hU hLU hpc hpos
  have hd : Differentiable ℝ h := hC.differentiable (by norm_num)
  have hf : ContDiff ℝ 1 (h ∘ e1) := by
    have : (h ∘ e1) = h ∘ (EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ) := rfl
    rw [this]
    exact ContDiff.comp (g := h) (f := ⇑(EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ)) hC
      (ContinuousLinearMap.contDiff (EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ))
  have e1cont : Continuous e1 := (EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ).continuous
  obtain ⟨r, c, C, hr, hc, hcC, g, hg, hb, hA⟩ := hE 1 (h ∘ e1) (p ∘ e1) (e1 ⁻¹' U) t hf
    (decay_transport h hTop hBot) ht
    (by obtain ⟨x, hx⟩ := hex; exact ⟨e1.symm x, by simpa using hx⟩)
    (fun x hx => fderiv_transport h hd x (hder _ hx))
    (hU.preimage e1cont) (fun x hx => hLU hx)
    (hpc.comp e1cont.continuousOn (fun x hx => hx)) (fun x hx => hpos _ hx)
  refine ⟨r, c, C, hr, hc, hcC, g, hg, hb, fun A hA' hAs => ?_⟩
  have h1 := hA A hA' hAs
  rw [← h1]
  have hmeasB : MeasurableSet (h ⁻¹' A) := hC.continuous.measurable hA'
  have hmeasB' : MeasurableSet ((h ∘ e1) ⁻¹' A) := hmeasB.preimage e1.measurable
  rw [MeasureTheory.withDensity_apply _ hmeasB, MeasureTheory.withDensity_apply _ hmeasB']
  have key := e1_mp.setLIntegral_comp_preimage_emb e1.measurableEmbedding
    (fun y => ENNReal.ofReal (p y)) (h ⁻¹' A)
  exact key.symm

/-- The `d = 1` instance of the certified claim reproves `Wave31tc.Claims.qdens_univariate`. -/
example : StatFormal.Wave31tc.Claims.qdens_univariate := qdens_univariate_of_euclid qdens_euclid

end StatFormal.Wave31th
