import StatFormal.Archive.Wave30ao.RouteClaims
import StatFormal.Archive.Wave30r.Proofs

/-!
# Route — `lem:sharp` for the printed plan (untrusted)

The printed plan is the Wave 29g `IsEntPlanD` plan (`convention_printed`), whose cost `sqCostD = ofReal(‖x−y‖²/2)` is
the Wave 30r `halfQuadCost = ‖x−y‖ₑ²/2`; the certified Wave 30r route skeleton `sharp_of_cost` and the library
`EntropicPlan.entropicPlan_eq_withDensity` then apply.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter TauCeti InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave30ao

open StatFormal.DiffEntropy
open StatFormal.Wave29g (sqCostD IsEntPlanD)

local notation "E" d => EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

lemma sqCostD_eq_half : (sqCostD : (E d) × (E d) → ℝ≥0∞) = StatFormal.Wave30r.halfQuadCost := by
  funext z
  simp only [sqCostD, StatFormal.Wave30r.halfQuadCost, StatFormal.Wave8a.quadCost]
  rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm,
    ENNReal.ofReal_ofNat]

lemma hasFiniteMoment_of_int {ρ : Measure (E d)} [IsProbabilityMeasure ρ]
    (h : Integrable (fun x : E d => ‖x‖ ^ 2) ρ) : HasFiniteMoment 2 ρ := by
  rw [StatFormal.Foundations.EntropicPlan.hasFiniteMoment_two_iff]
  have := h.2
  simp only [HasFiniteIntegral, enorm_pow, enorm_norm] at this
  exact this.ne

lemma not_dirac {ν : Measure (E d)} (hd : 0 < d) (hν : ν ≪ volume) (y : E d) : ν ≠ Measure.dirac y := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  intro h
  have h0 : ν {y} = 0 := hν (measure_singleton y)
  rw [h, Measure.dirac_apply_of_mem (Set.mem_singleton y)] at h0
  exact one_ne_zero h0

theorem sharp_printed : Claims.sharp_printed := by
  intro d ε R ν hε hR hν hR2 hν2 hRf hνf
  obtain ⟨-, -, -, hiff, -⟩ := convention_printed d ε R ν hε hR hν hR2 hν2 hRf hνf
  have hR2' := hasFiniteMoment_of_int hR2
  have hν2' := hasFiniteMoment_of_int hν2
  have hcP : ∫⁻ z, sqCostD z ∂(R.prod ν) ≠ ∞ := by
    rw [sqCostD_eq_half]; exact StatFormal.Wave30r.lintegral_halfQuadCost_ne_top hR2' hν2'
  have hcm : Measurable (sqCostD : (E d) × (E d) → ℝ≥0∞) := by
    rw [sqCostD_eq_half]; exact StatFormal.Wave30r.measurable_halfQuadCost
  have hε' : ε.toNNReal ≠ 0 := by simpa using hε
  obtain ⟨h1, h2⟩ := StatFormal.Wave30r.sharp_of_cost hcm hcP hν2' hε'
  have hsharp : ∀ (π : Measure ((E d) × (E d))) (T : (E d) → E d), IsPrintedPlan ε R ν π →
      StatFormal.Wave8a.IsBaryProj π T → (R.map T = ν ↔ ∃ y, ν = Measure.dirac y) :=
    fun π T hπ hT => h2 π T ((hiff π).1 hπ) hT
  refine ⟨?_, fun π hπ => ?_, hsharp, fun hd π T hπ hT hpush => ?_⟩
  · obtain ⟨π, hπ, hu⟩ := h1
    exact ⟨π, (hiff π).2 hπ, fun σ hσ => hu σ ((hiff σ).1 hσ)⟩
  · obtain ⟨hc, ho⟩ := (hiff π).1 hπ
    exact StatFormal.Foundations.EntropicPlan.entropicPlan_eq_withDensity hε' hcP hc ho
  · obtain ⟨y, hy⟩ := (hsharp π T hπ hT).1 hpush
    exact not_dirac hd hνf.1 y hy

end StatFormal.Wave30ao
