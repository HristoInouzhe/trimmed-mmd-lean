import StatFormal.Archive.Wave29t.RouteMixtureD
import StatFormal.Lib.SchrodingerPathD.Static

/-!
# Route — `lem:equiv` static half in `ℝᵈ` and the unconditional `prop:mixture` in `ℝᵈ` (untrusted)

`refPlanD = refPD`, `isoGauss = isoG` and the frozen Wave 29g `sqCostD = halfSqD` by definition; the library
`klDiv_refPD` (the Lebesgue density `∏ᵢ φ_ε(uᵢ)` of `N(0, εI)`, `μ ⊗ ν = R₀₁.withDensity (q(y)/p_ε(y − x))`) and
`static_iff_entropicD` give the static claims; with `mixtureD_bridge`, `equiv_bridge_d` (routes) they give
`mixtureD_uncond`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave29t

open StatFormal.SchrodingerPath StatFormal.SchrodingerPathD

local notation "E" d => EuclideanSpace ℝ (Fin d)

lemma refPlanD_eq_refPD {d : ℕ} (ε : ℝ) (μ : Measure (E d)) : refPlanD ε μ = refPD ε μ := rfl

lemma sqCostD_eq_halfSqD {d : ℕ} : (StatFormal.Wave29g.sqCostD : (E d) × (E d) → ℝ≥0∞) = halfSqD := rfl

theorem equiv_static_calib_d : Claims.equiv_static_calib_d := by
  intro d ε μ ν q hε hμ hν hq hq0 hνq hlog hμ2 hν2 π hπ
  rw [refPlanD_eq_refPD]
  exact klDiv_refPD hε hνq hq hq0 hlog hμ2 hν2 hπ

lemma static_finiteD {d : ℕ} {ε : ℝ} {μ ν : Measure (E d)} {q : (E d) → ℝ} (hε : 0 < ε) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y)
    (hνq : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hlog : Integrable (fun y => Real.log (q y)) ν)
    (hμ2 : Integrable (fun x : E d => ‖x‖ ^ 2) μ) (hν2 : Integrable (fun y : E d => ‖y‖ ^ 2) ν) :
    schroedingerValue (refPlanD ε μ) μ ν ≠ ∞ := by
  have hprod : IsCoupling (μ.prod ν) μ ν := ⟨Measure.fst_prod, Measure.snd_prod⟩
  have h := (klDiv_refPD hε hνq hq hq0 hlog hμ2 hν2 hprod).1.2 (by rw [klDiv_self]; exact ENNReal.zero_ne_top)
  exact ne_top_of_le_ne_top h (schroedingerValue_le_klDiv hprod _)

lemma static_iff_entD {d : ℕ} {ε : ℝ} {μ ν : Measure (E d)} {q : (E d) → ℝ} (hε : 0 < ε) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y)
    (hνq : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hlog : Integrable (fun y => Real.log (q y)) ν)
    (hμ2 : Integrable (fun x : E d => ‖x‖ ^ 2) μ) (hν2 : Integrable (fun y : E d => ‖y‖ ^ 2) ν) :
    entropicTransportCost StatFormal.Wave29g.sqCostD ε.toNNReal μ ν ≠ ∞ ∧
      ∀ π : Measure ((E d) × (E d)), IsStaticBridgeD ε μ ν π ↔ StatFormal.Wave29g.IsEntPlanD ε μ ν π := by
  obtain ⟨hne, hiff⟩ := static_iff_entropicD hε hνq hq hq0 hlog hμ2 hν2
  rw [sqCostD_eq_halfSqD]
  refine ⟨hne, fun π => ?_⟩
  unfold IsStaticBridgeD StatFormal.Wave29g.IsEntPlanD
  rw [sqCostD_eq_halfSqD, refPlanD_eq_refPD]
  exact hiff π

theorem equiv_static_ac_d : Claims.equiv_static_ac_d := by
  intro d ε μ ν q hε hμ hν hq hq0 hνq hlog hμ2 hν2
  have hS := static_finiteD hε hq hq0 hνq hlog hμ2 hν2
  obtain ⟨hETC, hiff⟩ := static_iff_entD hε hq hq0 hνq hlog hμ2 hν2
  obtain ⟨π, hπ⟩ := static_exists_iff.2 hS
  have huniq : ∀ π', IsStaticBridgeD ε μ ν π' → π' = π := fun π' h' => static_unique h' hπ
  exact ⟨hS, hETC, hiff, ⟨π, hπ, huniq⟩, π, (hiff π).1 hπ, fun π' h' => huniq π' ((hiff π').2 h')⟩

theorem mixtureD_uncond : Claims.mixtureD_uncond := by
  intro Ω _ d ε μ ν q X R hε hμ hν hq hq0 hνq hlog hμ2 hν2 hR
  have hS := static_finiteD hε hq hq0 hνq hlog hμ2 hν2
  obtain ⟨-, hex, huniq, -⟩ := equiv_bridge_d Ω d ε μ ν X R hε hμ hR
  obtain ⟨P₀, hP₀⟩ := hex.2 hS
  obtain ⟨hETC, hiff⟩ := static_iff_entD hε hq hq0 hνq hlog hμ2 hν2
  refine ⟨(mixtureD_bridge Ω d ε μ ν X R P₀ hε hμ hR hP₀).1,
    ⟨P₀, hP₀, fun P hP => huniq P P₀ hP hP₀⟩, fun P hP => ?_⟩
  obtain ⟨-, hstat, hkl, hdens, htime⟩ := mixtureD_bridge Ω d ε μ ν X R P hε hμ hR hP
  set π := P.map (fun ω => (X 0 ω, X 1 ω))
  have hEnt : StatFormal.Wave29g.IsEntPlanD ε μ ν π := (hiff π).1 hstat
  refine ⟨hstat, hkl, hEnt, hdens, hETC, ?_, htime⟩
  have hπc : IsCoupling π μ ν := hstat.1
  have hfin := klDiv_refPD hε hνq hq hq0 hlog hμ2 hν2 hπc
  rw [← refPlanD_eq_refPD] at hfin
  have hk : klDiv π (μ.prod ν) ≠ ∞ := hfin.1.1 hstat.2.1
  have hεt : ((ε.toNNReal : ℝ≥0∞)) ≠ ∞ := ENNReal.coe_ne_top
  have hεr : ((ε.toNNReal : ℝ≥0∞)).toReal = ε := by simp [hε.le]
  have hsq := integrable_normsq_sub_of_coupling hπc hμ2 hν2
  have hc : ∫⁻ z, StatFormal.Wave29g.sqCostD z ∂π = ENNReal.ofReal (∫ z, ‖z.1 - z.2‖ ^ 2 / 2 ∂π) :=
    lintegral_halfSqD hsq
  rw [hkl, hfin.2 hk, ← hEnt.2, hc, ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hεt hk),
    ENNReal.toReal_mul, hεr, ENNReal.toReal_ofReal (integral_nonneg fun z => by positivity)]

/-! ### Non-vacuity of the `ass:ac` hypotheses in `ℝᵈ` (route lemmas, not targets) -/

/-- `ν = N(0, I_d)` satisfies every target hypothesis of `equiv_static_calib_d`, `equiv_static_ac_d`, `mixtureD_uncond`
(Lebesgue density `q = p₁`, `log q ∈ L¹(ν)`, `‖y‖² ∈ L¹(ν)`). -/
theorem acHyps_isoG (d : ℕ) :
    Measurable (gdens d 1) ∧ (∀ y, 0 ≤ gdens d 1 y) ∧
      isoGauss d 1 = volume.withDensity (fun y => ENNReal.ofReal (gdens d 1 y)) ∧
      Integrable (fun y => Real.log (gdens d 1 y)) (isoGauss d 1) ∧
      Integrable (fun y : E d => ‖y‖ ^ 2) (isoGauss d 1) := by
  have h2 : Integrable (fun y : E d => ‖y‖ ^ 2) (isoGauss d 1) := by
    unfold isoGauss
    exact (memLp_two_iff_integrable_sq_norm (f := id) aestronglyMeasurable_id).1 IsGaussian.memLp_two_id
  refine ⟨measurable_gdens 1, fun y => (gdens_pos one_pos y).le, isoG_eq_withDensity one_pos, ?_, h2⟩
  have e : (fun y => Real.log (gdens d 1 y)) =
      fun y : E d => -(d * Real.log (2 * Real.pi * 1) / 2) - ‖y‖ ^ 2 / (2 * 1) := by
    funext y; exact log_gdens one_pos y
  rw [e]
  exact (integrable_const _).sub (h2.div_const _)

/-- With `μ = ν = N(0, I_d)` and the witness reference, the unconditional claim yields a Schrödinger bridge: every
premise of `mixtureD_bridge`, `mixtureD_exists`, `equiv_bridge_d` and `mixtureD_uncond` is satisfiable, in every
dimension `d`, at every `ε > 0`. -/
theorem bridgeD_exists_witness (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Measure ((E d) × (E d) × (E d)),
      IsBrownianRefD ε (isoGauss d 1) witnessD (refMeasureD ε (isoGauss d 1)) ∧
      IsSchrodingerBridgeD witnessD (refMeasureD ε (isoGauss d 1)) (isoGauss d 1) (isoGauss d 1) P := by
  obtain ⟨hq, hq0, hν, hlog, h2⟩ := acHyps_isoG d
  have hR := isBrownianRefD_witness hε.le (isoGauss d 1)
  obtain ⟨-, ⟨P, hP, -⟩, -⟩ := mixtureD_uncond _ d ε (isoGauss d 1) (isoGauss d 1) (gdens d 1) witnessD _ hε
    inferInstance inferInstance hq hq0 hν hlog h2 h2 hR
  exact ⟨P, hR, hP⟩

end StatFormal.Wave29t
