import StatFormal.Archive.Wave30az.Statements
import StatFormal.Archive.SBFairness.Decay.Proofs
import StatFormal.Archive.Wave30ao.Proofs

/-!
# Route — SB `thm:decay` caveat: `G_ε ≥ W₂(R₀,R₁)`, and equality at `ε > 0` for equal groups

1. At `t = 0` the bridge marginal is the first marginal, so the certified `decay` at `t = 0` is `W₂(R₀,R₁)² ≤ G_ε²`.
2. Equal groups: the printed plan is unique (certified `sharp_printed`, finite entropies from `cost_finite_iff`), the
   diagonal gluing `(X₀, X₀, X₁)` has zero cost, so `G_ε² = 0 = W₂(R,R)²`.
3. The refutation instantiates 2 at `R = ν = N(0, I_1)`, `ε = 1`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set TauCeti
open scoped ENNReal

namespace StatFormal.Wave30az

open StatFormal.SBFairness.Decay (Gsq IsGluing bridge)
open StatFormal.Wave30ao (entCost IsPrintedPlan HasFiniteEnt)

local notation "Eu" d => EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

lemma bridge_zero (π : Measure ((Eu d) × (Eu d))) (ε : ℝ) : bridge π ε 0 = π.fst := by
  have hf : (fun p : ((Eu d) × (Eu d)) × (Eu d) =>
      (1 - 0 : ℝ) • p.1.1 + (0 : ℝ) • p.1.2 + Real.sqrt (ε * 0 * (1 - 0)) • p.2) =
      Prod.fst ∘ Prod.fst := by
    funext p; simp
  rw [bridge, hf, ← Measure.map_map measurable_fst measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul, Measure.fst]

lemma isProb_coupling {μ ν : Measure (Eu d)} [IsProbabilityMeasure μ] {π : Measure ((Eu d) × (Eu d))}
    (hπ : IsCoupling π μ ν) : IsProbabilityMeasure π := by
  have h : π.map Prod.fst = μ := hπ.fst_eq
  have : IsProbabilityMeasure (π.map Prod.fst) := by rw [h]; infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

theorem decay_ge_W2 : Claims.decay_ge_W2 := by
  intro d ε R₀ R₁ ν π₀ π₁ _ _ h₀ h₁
  have := isProb_coupling h₀.1
  have := isProb_coupling h₁.1
  have hsnd : π₀.snd = π₁.snd := by rw [h₀.1.snd_eq, h₁.1.snd_eq]
  have hd := StatFormal.SBFairness.Decay.decay d π₀ π₁ 0 0 hsnd le_rfl ⟨le_rfl, zero_le_one⟩
  rw [bridge_zero, bridge_zero, h₀.1.fst_eq, h₁.1.fst_eq] at hd
  simpa using hd

/-- The diagonal gluing has zero cost. -/
lemma Gsq_self (π : Measure ((Eu d) × (Eu d))) : Gsq π π = 0 := by
  refine le_antisymm ?_ (zero_le)
  have hg : Measurable fun p : (Eu d) × (Eu d) => (p.1, p.1, p.2) := by fun_prop
  have hglue : IsGluing (π.map fun p : (Eu d) × (Eu d) => (p.1, p.1, p.2)) π π := by
    constructor
    · rw [Measure.map_map (by fun_prop) hg]
      exact Measure.map_id
    · rw [Measure.map_map (by fun_prop) hg]
      exact Measure.map_id
  unfold Gsq
  refine (iInf₂_le (f := fun (Γ : Measure ((Eu d) × (Eu d) × (Eu d))) (_ : IsGluing Γ π π) =>
    ∫⁻ q, edist q.1 q.2.1 ^ 2 ∂Γ) _ hglue).trans ?_
  rw [lintegral_map (by fun_prop) hg]
  simp

theorem decay_equal_groups : Claims.decay_equal_groups := by
  intro d ε R ν π₀ π₁ hε _ _ hR2 hν2 hc h₀ h₁
  obtain ⟨hR, hν⟩ := ((StatFormal.Wave30ao.cost_finite_iff d ε R ν hε inferInstance inferInstance hR2 hν2).1).1 hc
  obtain ⟨huniq, -⟩ := StatFormal.Wave30ao.sharp_printed d ε R ν hε inferInstance inferInstance hR2 hν2 hR hν
  have heq : π₀ = π₁ := huniq.unique h₀ h₁
  have hW : wassersteinEDist 2 R R = 0 :=
    wassersteinEDist_self_of_measurable_edist (StatFormal.SBFairness.Decay.measurable_edist_E d) 2 R
  subst heq
  refine ⟨rfl, Gsq_self π₀, hW, ?_⟩
  rw [Gsq_self, hW]
  simp

open StatFormal.Wave29t (isoGauss acHyps_isoG) in
theorem decay_eq_refuted : Claims.decay_eq_refuted := by
  intro H
  obtain ⟨hq, hq0, hνq, hlog, hν2⟩ := acHyps_isoG 1
  have hνac : isoGauss 1 1 ≪ volume := by rw [hνq]; exact withDensity_absolutelyContinuous _ _
  have hνf : HasFiniteEnt (isoGauss 1 1) := by
    refine ⟨hνac, hlog.congr ?_⟩
    have h := Measure.rnDeriv_withDensity (volume : Measure (Eu 1)) hq.ennreal_ofReal
    rw [← hνq] at h
    filter_upwards [hνac.ae_le h] with y hy
    simp [StatFormal.Wave30ao.logDensity, hy, ENNReal.toReal_ofReal (hq0 y)]
  have hc : entCost 1 (isoGauss 1 1) (isoGauss 1 1) < ⊤ :=
    ((StatFormal.Wave30ao.cost_finite_iff 1 1 _ _ one_pos inferInstance inferInstance hν2 hν2).1).2 ⟨hνf, hνf⟩
  obtain ⟨⟨π, hπ, -⟩, -⟩ :=
    StatFormal.Wave30ao.sharp_printed 1 1 _ _ one_pos inferInstance inferInstance hν2 hν2 hνf hνf
  exact H 1 1 _ _ _ π π one_pos inferInstance inferInstance inferInstance hν2 hν2 hν2 hc hc hπ hπ
    (decay_equal_groups 1 1 _ _ π π one_pos inferInstance inferInstance hν2 hν2 hc hπ hπ).2.2.2

end StatFormal.Wave30az
