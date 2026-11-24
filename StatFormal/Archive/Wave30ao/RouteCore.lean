import StatFormal.Archive.Wave30ao.Statements
import StatFormal.Lib.DiffEntropy.Gauss
import StatFormal.Archive.Wave29t.Proofs

/-!
# Route — the printed differential-entropy normalisation versus the certified plan-level identities (untrusted)

`logDensity`, `diffEnt`, `HasFiniteEnt` are the library `llr · volume`, `relEnt · volume`, `FiniteEnt · volume` by
definition; on `ℝᵈ × ℝᵈ`, `volume = volume.prod volume` by definition. With the library chain rule
(`klDiv_prod_eq`, `finiteEnt_of_klDiv`), the Gaussian negative-part bounds and the certified
`SchrodingerPathD.klDiv_refPD` (= Wave 29t `equiv_static_calib_d`), every coupling `π` of `𝒫₂` marginals with finite
entropy satisfies `entObj ε π = ε KL(π‖R₀₁) − ε Ent(μ) − (εd/2) log(2πε)`, and both sides are `⊤` otherwise; so the
printed minimisers are the static minimisers of Wave 29t, and the certified `equiv_static_ac_d`, `equiv_bridge_d`,
`mixtureD_bridge` give the claims.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter TauCeti InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave30ao

open StatFormal.DiffEntropy
open StatFormal.Wave29t (isoGauss IsBrownianRefD IsSchrodingerBridgeD refPlanD IsStaticBridgeD bridgeLawD)
open StatFormal.Wave29g (sqCostD IsEntPlanD)

local notation "E" d => EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

lemma volume_prodE : (volume : Measure ((E d) × (E d))) = (volume : Measure (E d)).prod volume := rfl

lemma isProb_of_coupling {μ ν : Measure (E d)} [IsProbabilityMeasure μ] {π : Measure ((E d) × (E d))}
    (hπ : IsCoupling π μ ν) : IsProbabilityMeasure π := by
  have h : π.map Prod.fst = μ := hπ.fst_eq
  have : IsProbabilityMeasure (π.map Prod.fst) := by rw [h]; infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

section Fixed

variable {μ ν : Measure (E d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (hμ2 : Integrable (fun x : E d => ‖x‖ ^ 2) μ) (hν2 : Integrable (fun y : E d => ‖y‖ ^ 2) ν)
include hμ2 hν2

/-- Encoding-free finiteness (part (3) of the task): `Ent(π) > −∞` for a coupling of `𝒫₂` marginals forces all three
entropies finite. -/
lemma finite_of_coupling {π : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν) (hac : π ≪ volume)
    (hpos : Integrable (fun z => max (logDensity π z) 0) π) :
    HasFiniteEnt π ∧ HasFiniteEnt μ ∧ HasFiniteEnt ν := by
  have : IsProbabilityMeasure π := isProb_of_coupling hπ
  have h1 : π.map Prod.fst = μ := hπ.fst_eq
  have h2 : π.map Prod.snd = ν := hπ.snd_eq
  have hac' : π ≪ (volume : Measure (E d)).prod volume := hac
  exact finiteEnt_marginals h1 h2 hac' hpos
    (negPart_integrable_P2_prod hac' (integrable_comp_fst h1 hμ2) (integrable_comp_snd h2 hν2))
    (negPart_integrable_P2 (h1 ▸ ac_fst_of_ac hac') hμ2) (negPart_integrable_P2 (h2 ▸ ac_snd_of_ac hac') hν2)

lemma cost_int {π : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν) :
    Integrable (fun z : (E d) × (E d) => ‖z.1 - z.2‖ ^ 2) π :=
  StatFormal.SchrodingerPathD.integrable_normsq_sub_of_coupling hπ hμ2 hν2

lemma entObj_of_fin (ε : ℝ) {π : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν) (hf : HasFiniteEnt π) :
    entObj ε π = (((∫ z, ‖z.1 - z.2‖ ^ 2 / 2 ∂π) - ε * diffEnt π : ℝ) : EReal) := by
  rw [entObj, if_pos ⟨hf, cost_int hμ2 hν2 hπ⟩]

omit hμ2 hν2 in
lemma entObj_of_not (ε : ℝ) {π : Measure ((E d) × (E d))} (hf : ¬ HasFiniteEnt π) : entObj ε π = ⊤ := by
  rw [entObj, if_neg (fun h => hf h.1)]

lemma entObj_eq_top_iff (ε : ℝ) {π : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν) :
    entObj ε π = ⊤ ↔ ¬ HasFiniteEnt π := by
  refine ⟨fun h hf => ?_, entObj_of_not ε⟩
  rw [entObj_of_fin hμ2 hν2 ε hπ hf] at h
  exact EReal.coe_ne_top _ h

omit [IsProbabilityMeasure μ] hμ2 hν2 in
lemma q_of_fin (hν : HasFiniteEnt ν) :
    Measurable (fun y => (ν.rnDeriv volume y).toReal) ∧ (∀ y, 0 ≤ (ν.rnDeriv volume y).toReal) ∧
      ν = volume.withDensity (fun y => ENNReal.ofReal ((ν.rnDeriv volume y).toReal)) ∧
      Integrable (fun y => Real.log ((ν.rnDeriv volume y).toReal)) ν ∧
      ∫ y, Real.log ((ν.rnDeriv volume y).toReal) ∂ν = -diffEnt ν := by
  refine ⟨(Measure.measurable_rnDeriv _ _).ennreal_toReal, fun y => ENNReal.toReal_nonneg, ?_, hν.2, ?_⟩
  · conv_lhs => rw [← Measure.withDensity_rnDeriv_eq ν volume hν.1]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ν volume] with y hy
    rw [ENNReal.ofReal_toReal hy.ne]
  · simp [diffEnt, logDensity]

omit hμ2 hν2 in
/-- `KL(π‖μ⊗ν) = −Ent π + Ent μ + Ent ν`. -/
lemma kl_mn (hμ : HasFiniteEnt μ) (hν : HasFiniteEnt ν) {π : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν)
    (hf : HasFiniteEnt π) :
    klDiv π (μ.prod ν) ≠ ∞ ∧ (klDiv π (μ.prod ν)).toReal = -diffEnt π + diffEnt μ + diffEnt ν := by
  have : IsProbabilityMeasure π := isProb_of_coupling hπ
  exact klDiv_prod_eq (l₁ := volume) (l₂ := volume) hπ.fst_eq hπ.snd_eq hf hμ hν

omit hμ2 hν2 in
lemma fin_of_kl (hμ : HasFiniteEnt μ) (hν : HasFiniteEnt ν) {π : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν)
    (hkl : klDiv π (μ.prod ν) ≠ ∞) : HasFiniteEnt π := by
  have : IsProbabilityMeasure π := isProb_of_coupling hπ
  exact finiteEnt_of_klDiv (l₁ := volume) (l₂ := volume) hπ.fst_eq hπ.snd_eq hkl hμ hν

/-- The proof display of `lem:equiv`, multiplied by `ε`. -/
lemma kl_ref {ε : ℝ} (hε : 0 < ε) (hμ : HasFiniteEnt μ) (hν : HasFiniteEnt ν) {π : Measure ((E d) × (E d))}
    (hπ : IsCoupling π μ ν) :
    (HasFiniteEnt π → klDiv π (refPlanD ε μ) ≠ ∞ ∧
      ε * (klDiv π (refPlanD ε μ)).toReal = ∫ z, ‖z.1 - z.2‖ ^ 2 / 2 ∂π - ε * diffEnt π + ε * diffEnt μ +
        ε * d * Real.log (2 * Real.pi * ε) / 2) ∧
    (¬ HasFiniteEnt π → klDiv π (refPlanD ε μ) = ∞) := by
  obtain ⟨hq, hq0, hνq, hlog, hint⟩ := q_of_fin hν
  have K := StatFormal.SchrodingerPathD.klDiv_refPD hε hνq hq hq0 hlog hμ2 hν2 hπ
  have hR : refPlanD ε μ = StatFormal.SchrodingerPathD.refPD ε μ := rfl
  rw [hR]
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · obtain ⟨h1, h2⟩ := kl_mn hμ hν hπ hf
    refine ⟨K.1.2 h1, ?_⟩
    rw [K.2 h1, h2, hint]
    ring
  · by_contra h
    exact hf (fin_of_kl hμ hν hπ (K.1.1 h))

/-- `entObj` is monotone in `KL(·‖R₀₁)`. -/
lemma entObj_le_iff {ε : ℝ} (hε : 0 < ε) (hμ : HasFiniteEnt μ) (hν : HasFiniteEnt ν)
    {π π' : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν) (hπ' : IsCoupling π' μ ν) (hf : HasFiniteEnt π) :
    entObj ε π ≤ entObj ε π' ↔ klDiv π (refPlanD ε μ) ≤ klDiv π' (refPlanD ε μ) := by
  obtain ⟨k1, k2⟩ := (kl_ref hμ2 hν2 hε hμ hν hπ).1 hf
  by_cases hf' : HasFiniteEnt π'
  · obtain ⟨k1', k2'⟩ := (kl_ref hμ2 hν2 hε hμ hν hπ').1 hf'
    rw [entObj_of_fin hμ2 hν2 ε hπ hf, entObj_of_fin hμ2 hν2 ε hπ' hf', EReal.coe_le_coe_iff,
      ← ENNReal.toReal_le_toReal k1 k1']
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · rw [entObj_of_not ε hf', (kl_ref hμ2 hν2 hε hμ hν hπ').2 hf']
    simp

/-- The printed minimisers are the static minimisers of Wave 29t. -/
lemma printed_iff_static {ε : ℝ} (hε : 0 < ε) (hμ : HasFiniteEnt μ) (hν : HasFiniteEnt ν)
    (π : Measure ((E d) × (E d))) : IsPrintedPlan ε μ ν π ↔ IsStaticBridgeD ε μ ν π := by
  constructor
  · rintro ⟨hπ, hne, hmin⟩
    have hf : HasFiniteEnt π := by
      by_contra h; exact hne (entObj_of_not ε h)
    refine ⟨hπ, ((kl_ref hμ2 hν2 hε hμ hν hπ).1 hf).1, fun π' hπ' => ?_⟩
    exact (entObj_le_iff hμ2 hν2 hε hμ hν hπ hπ' hf).1 (hmin π' hπ')
  · rintro ⟨hπ, hne, hmin⟩
    have hf : HasFiniteEnt π := by
      by_contra h; exact hne ((kl_ref hμ2 hν2 hε hμ hν hπ).2 h)
    refine ⟨hπ, (entObj_eq_top_iff hμ2 hν2 ε hπ).not.2 (not_not.2 hf), fun π' hπ' => ?_⟩
    exact (entObj_le_iff hμ2 hν2 hε hμ hν hπ hπ' hf).2 (hmin π' hπ')

/-- The certified Wave 29t `equiv_static_ac_d` at `q = dν/dLeb`. -/
lemma static_ac {ε : ℝ} (hε : 0 < ε) (hν : HasFiniteEnt ν) :
    schroedingerValue (refPlanD ε μ) μ ν ≠ ∞ ∧ entropicTransportCost sqCostD ε.toNNReal μ ν ≠ ∞ ∧
      (∀ π : Measure ((E d) × (E d)), IsStaticBridgeD ε μ ν π ↔ IsEntPlanD ε μ ν π) ∧
      (∃! π : Measure ((E d) × (E d)), IsStaticBridgeD ε μ ν π) ∧
      ∃! π : Measure ((E d) × (E d)), IsEntPlanD ε μ ν π := by
  obtain ⟨hq, hq0, hνq, hlog, -⟩ := q_of_fin hν
  exact StatFormal.Wave29t.equiv_static_ac_d d ε μ ν _ hε inferInstance inferInstance hq hq0 hνq hlog hμ2 hν2

lemma exists_unique_printed {ε : ℝ} (hε : 0 < ε) (hμ : HasFiniteEnt μ) (hν : HasFiniteEnt ν) :
    ∃! π : Measure ((E d) × (E d)), IsPrintedPlan ε μ ν π := by
  obtain ⟨-, -, -, h, -⟩ := static_ac hμ2 hν2 hε hν
  simpa only [printed_iff_static hμ2 hν2 hε hμ hν] using h

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] hμ2 hν2 in
lemma entCost_eq_of_printed {ε : ℝ} {π : Measure ((E d) × (E d))} (h : IsPrintedPlan ε μ ν π) :
    entCost ε μ ν = entObj ε π :=
  le_antisymm (iInf₂_le π h.1) (le_iInf₂ fun π' hπ' => h.2.2 π' hπ')

lemma fin_of_cost {ε : ℝ} (h : entCost ε μ ν < ⊤) : HasFiniteEnt μ ∧ HasFiniteEnt ν := by
  simp only [entCost, iInf_lt_iff] at h
  obtain ⟨π, hπ, hlt⟩ := h
  have hf : HasFiniteEnt π := by
    by_contra hn; rw [entObj_of_not ε hn] at hlt; exact lt_irrefl _ hlt
  exact (finite_of_coupling hμ2 hν2 hπ hf.1 hf.2.pos_part).2

lemma cost_of_fin {ε : ℝ} (hμ : HasFiniteEnt μ) (hν : HasFiniteEnt ν) : entCost ε μ ν < ⊤ := by
  have hc := isCoupling_prod μ ν
  have hf : HasFiniteEnt (μ.prod ν) := fin_of_kl hμ hν hc (by rw [klDiv_self]; exact ENNReal.zero_ne_top)
  refine lt_of_le_of_lt (iInf₂_le (μ.prod ν) hc) ?_
  rw [entObj_of_fin hμ2 hν2 ε hc hf]
  exact EReal.coe_lt_top _

end Fixed

end StatFormal.Wave30ao
