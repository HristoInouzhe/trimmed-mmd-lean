import StatFormal.Archive.Wave29t.Statements
import StatFormal.Archive.Wave29q.RouteMixture
import StatFormal.Archive.Wave29q.RouteStatic
import StatFormal.Lib.SchrodingerPath.Exists

/-!
# Route — `lem:equiv` in general and the unconditional `prop:mixture` (untrusted)

* `equiv_static`: `IsStaticBridge ε μ ν = IsStaticMin (refPlan ε μ) μ ν` (definitional); library
  `static_exists_iff`/`static_unique` (Tau Ceti existence: `L¹`-Cauchy minimising sequence; uniqueness: strict
  convexity of `KL`), `R₀₁` a probability measure.
* `equiv_bridge`: the value identity by data processing (`klDiv_map_le`) and the `h`-transform (`klDiv_htrans`);
  existence through the certified frozen `mixture_exists`; uniqueness through `mixture_bridge` (endpoint laws are static
  minimisers, hence equal) and `mixture_exists` (bridges with equal endpoint laws coincide).
* `equiv_static_ac`: `KL(μ ⊗ ν ‖ R₀₁) < ∞` by the frozen `mixture_static` (`KL(μ ⊗ ν ‖ μ ⊗ ν) = 0`), and the frozen
  `mixture_static_plan` (static minimisers = `IsEntPlan`).
* `mixture_bridge_uncond`: the above with the frozen `mixture_bridge`, `mixture_static` (`eq:calib`) and
  `mixture_static_plan`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave29t

open StatFormal.SchrodingerPath
open StatFormal.WaveP3b (sqCost IsEntPlan)
open StatFormal.Wave29q (IsBrownianRef IsPathCoupling IsSchrodingerBridge refPlan IsStaticBridge bridgeLaw
  isCoupling_map isPathCoupling_htrans isProbabilityMeasure_of_coupling ref_facts)

lemma isStaticBridge_iff (ε : ℝ) (μ ν : Measure ℝ) (π : Measure (ℝ × ℝ)) :
    IsStaticBridge ε μ ν π ↔ IsStaticMin (refPlan ε μ) μ ν π := Iff.rfl

theorem equiv_static : Claims.equiv_static := by
  intro ε μ ν _ hμ
  exact ⟨static_exists_iff, fun π π' h h' => static_unique h h'⟩

/-- The dynamic value is the static value. -/
lemma dyn_value {Ω : Type} [MeasurableSpace Ω] {ε : ℝ} (hε : 0 ≤ ε) {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} {R : Measure Ω} (hR : IsBrownianRef ε μ X R) :
    (⨅ (Q : Measure Ω) (_ : IsPathCoupling X μ ν Q), klDiv Q R) = schroedingerValue (refPlan ε μ) μ ν := by
  obtain ⟨hRp, -, hRY⟩ := ref_facts hε hR
  have h0 : Measurable (X 0) := hR.1 0 ⟨le_rfl, zero_le_one⟩
  have h1 : Measurable (X 1) := hR.1 1 ⟨zero_le_one, le_rfl⟩
  have hY : Measurable (fun ω => (X 0 ω, X 1 ω)) := h0.prodMk h1
  apply le_antisymm
  · apply le_schroedingerValue
    intro π hπ
    by_cases hk : klDiv π (refPlan ε μ) = ∞
    · rw [hk]; exact le_top
    have hac : π ≪ R.map (fun ω => (X 0 ω, X 1 ω)) := by rw [hRY]; exact (klDiv_ne_top_iff.1 hk).1
    have := isProbabilityMeasure_of_coupling hπ
    calc (⨅ (Q : Measure Ω) (_ : IsPathCoupling X μ ν Q), klDiv Q R)
        ≤ klDiv (htrans R (fun ω => (X 0 ω, X 1 ω)) π) R := iInf₂_le _ (isPathCoupling_htrans h0 h1 hπ hac)
      _ = klDiv π (refPlan ε μ) := by rw [klDiv_htrans hY hac, hRY]
  · refine le_iInf₂ fun Q hQ => ?_
    obtain ⟨hQp, hQ0, hQ1⟩ := hQ
    refine (schroedingerValue_le_klDiv (isCoupling_map h0 h1 hQ0 hQ1) _).trans ?_
    rw [← hRY]; exact klDiv_map_le Q R hY

theorem equiv_bridge : Claims.equiv_bridge := by
  intro Ω _ ε μ ν X R hε hμ hR
  have hval := dyn_value (ν := ν) hε.le hR
  have hPval : ∀ P : Measure Ω, IsSchrodingerBridge X R μ ν P → klDiv P R = schroedingerValue (refPlan ε μ) μ ν :=
    fun P hP => hval ▸ le_antisymm (le_iInf₂ hP.2.2) (iInf₂_le P hP.1)
  refine ⟨hval, ⟨fun ⟨P, hP⟩ => hPval P hP ▸ hP.2.1, fun h => ?_⟩, fun P P' hP hP' => ?_, hPval⟩
  · obtain ⟨π, hπ⟩ := static_exists_iff.2 h
    obtain ⟨P, hP, -⟩ := (StatFormal.Wave29q.mixture_exists Ω ε μ ν X R hε hμ hR).1 π hπ
    exact ⟨P, hP⟩
  · have s := (StatFormal.Wave29q.mixture_bridge Ω ε μ ν X R P hε hμ hR hP).2.1
    have s' := (StatFormal.Wave29q.mixture_bridge Ω ε μ ν X R P' hε hμ hR hP').2.1
    exact (StatFormal.Wave29q.mixture_exists Ω ε μ ν X R hε hμ hR).2 P P' hP hP' (static_unique s s')

lemma static_finite {ε : ℝ} {μ ν : Measure ℝ} {q : ℝ → ℝ} (hε : 0 < ε) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y)
    (hνq : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hlog : Integrable (fun y => Real.log (q y)) ν)
    (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ) (hν2 : Integrable (fun y : ℝ => y ^ 2) ν) :
    schroedingerValue (refPlan ε μ) μ ν ≠ ∞ := by
  have hprod : IsCoupling (μ.prod ν) μ ν := ⟨Measure.fst_prod, Measure.snd_prod⟩
  have h := (StatFormal.Wave29q.mixture_static ε μ ν q hε inferInstance inferInstance hq hq0 hνq hlog hμ2 hν2
    (μ.prod ν) hprod).1.2 (by rw [klDiv_self]; exact ENNReal.zero_ne_top)
  exact ne_top_of_le_ne_top h (schroedingerValue_le_klDiv hprod _)

theorem equiv_static_ac : Claims.equiv_static_ac := by
  intro ε μ ν q hε hμ hν hq hq0 hνq hlog hμ2 hν2
  have hS := static_finite hε hq hq0 hνq hlog hμ2 hν2
  obtain ⟨hETC, hiff⟩ := StatFormal.Wave29q.mixture_static_plan ε μ ν q hε hμ hν hq hq0 hνq hlog hμ2 hν2
  obtain ⟨π, hπ⟩ := static_exists_iff.2 hS
  have huniq : ∀ π', IsStaticBridge ε μ ν π' → π' = π := fun π' h' => static_unique h' hπ
  refine ⟨hS, hETC, ⟨π, hπ, huniq⟩, π, (hiff π).1 hπ, fun π' h' => huniq π' ((hiff π').2 h')⟩

theorem mixture_bridge_uncond : Claims.mixture_bridge_uncond := by
  intro Ω _ ε μ ν q X R hε hμ hν hq hq0 hνq hlog hμ2 hν2 hR
  have hS := static_finite hε hq hq0 hνq hlog hμ2 hν2
  obtain ⟨-, hex, huniq, -⟩ := equiv_bridge Ω ε μ ν X R hε hμ hR
  obtain ⟨P₀, hP₀⟩ := hex.2 hS
  obtain ⟨hETC, hiff⟩ := StatFormal.Wave29q.mixture_static_plan ε μ ν q hε hμ hν hq hq0 hνq hlog hμ2 hν2
  refine ⟨(StatFormal.Wave29q.mixture_bridge Ω ε μ ν X R P₀ hε hμ hR hP₀).1,
    ⟨P₀, hP₀, fun P hP => huniq P P₀ hP hP₀⟩, fun P hP => ?_⟩
  obtain ⟨-, hstat, hkl, hdens, htime⟩ := StatFormal.Wave29q.mixture_bridge Ω ε μ ν X R P hε hμ hR hP
  set π := P.map (fun ω => (X 0 ω, X 1 ω))
  have hEnt : IsEntPlan ε μ ν π := (hiff π).1 hstat
  refine ⟨hstat, hkl, hEnt, hdens, hETC, ?_, htime⟩
  -- `eq:calib`
  have hπc : IsCoupling π μ ν := hstat.1
  have hfin := (StatFormal.Wave29q.mixture_static ε μ ν q hε hμ hν hq hq0 hνq hlog hμ2 hν2 π hπc)
  have hk : klDiv π (μ.prod ν) ≠ ∞ := hfin.1.1 hstat.2.1
  have hεt : ((ε.toNNReal : ℝ≥0∞)) ≠ ∞ := ENNReal.coe_ne_top
  have hεr : ((ε.toNNReal : ℝ≥0∞)).toReal = ε := by simp [hε.le]
  have hsq : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) π := integrable_sq_sub_of_coupling hπc hμ2 hν2
  have hc : ∫⁻ z, sqCost z ∂π = ENNReal.ofReal (∫ z, (z.1 - z.2) ^ 2 / 2 ∂π) := lintegral_halfSq hsq
  rw [hkl, hfin.2 hk, ← hEnt.2, hc, ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hεt hk),
    ENNReal.toReal_mul, hεr, ENNReal.toReal_ofReal (integral_nonneg fun z => by positivity)]

/-! ### Non-vacuity (route lemmas, not targets) -/

/-- `ν = N(0,1)` satisfies the `ass:ac`/`𝒫₂` hypotheses of `equiv_static_ac` and `mixture_bridge_uncond`. -/
theorem acHyps_gauss :
    Measurable (gaussianPDFReal 0 (1 : ℝ).toNNReal) ∧ (∀ y, 0 ≤ gaussianPDFReal 0 (1 : ℝ).toNNReal y) ∧
      gaussianReal 0 (1 : ℝ).toNNReal =
        volume.withDensity (fun y => ENNReal.ofReal (gaussianPDFReal 0 (1 : ℝ).toNNReal y)) ∧
      Integrable (fun y => Real.log (gaussianPDFReal 0 (1 : ℝ).toNNReal y)) (gaussianReal 0 (1 : ℝ).toNNReal) ∧
      Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 (1 : ℝ).toNNReal) := by
  have hv : (1 : ℝ).toNNReal ≠ 0 := by simp
  have h2 : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 (1 : ℝ).toNNReal) := by
    have := (memLp_two_iff_integrable_sq_norm (f := id) aestronglyMeasurable_id).1
      (IsGaussian.memLp_two_id (μ := gaussianReal 0 (1 : ℝ).toNNReal))
    simpa [Real.norm_eq_abs, sq_abs] using this
  refine ⟨measurable_gaussianPDFReal 0 _, fun y => gaussianPDFReal_nonneg 0 _ y,
    gaussianReal_of_var_ne_zero 0 hv, ?_, h2⟩
  have e : (fun y => Real.log (gaussianPDFReal 0 (1 : ℝ).toNNReal y)) =
      fun y : ℝ => -(Real.log (2 * Real.pi * 1) / 2) - y ^ 2 / (2 * 1) := by
    funext y; exact log_gaussPDF_zero one_pos y
  rw [e]
  exact (integrable_const _).sub (h2.div_const _)

/-- With `μ = ν = N(0,1)` and the frozen wave 29q witness reference, `mixture_bridge_uncond` yields a Schrödinger bridge
at every `ε > 0`: every premise of `equiv_bridge` and `mixture_bridge_uncond` is satisfiable. -/
theorem bridge_exists_witness {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Measure (ℝ × ℝ × ℝ),
      IsBrownianRef ε (gaussianReal 0 (1 : ℝ).toNNReal) (refWitness 1)
          (StatFormal.Wave29q.refMeasure ε (gaussianReal 0 (1 : ℝ).toNNReal)) ∧
        IsSchrodingerBridge (refWitness 1) (StatFormal.Wave29q.refMeasure ε (gaussianReal 0 (1 : ℝ).toNNReal))
          (gaussianReal 0 (1 : ℝ).toNNReal) (gaussianReal 0 (1 : ℝ).toNNReal) P := by
  obtain ⟨hq, hq0, hν, hlog, h2⟩ := acHyps_gauss
  have hR := StatFormal.Wave29q.isBrownianRef_refMeasure hε.le (gaussianReal 0 (1 : ℝ).toNNReal)
  obtain ⟨-, ⟨P, hP, -⟩, -⟩ := mixture_bridge_uncond _ ε _ _ _ (refWitness 1) _ hε inferInstance inferInstance hq hq0 hν
    hlog h2 h2 hR
  exact ⟨P, hR, hP⟩

end StatFormal.Wave29t
