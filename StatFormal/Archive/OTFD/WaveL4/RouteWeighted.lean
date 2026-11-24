import StatFormal.Archive.OTFD.WaveL4.RouteClaims
import StatFormal.Archive.OTFD.WaveL4.RouteBridge

/-!
# Route (wave L4): the C limits under the verbatim discrete assumption

Untrusted route file. `WeightedFit` (C `ass:conditional-oos` with `eq:weighted-hard-gap`) gives an
`InexactFit` with gaps `ζ_n / 2` (`RouteBridge.weighted_gap_plan_form` at every `n`, the plans and
defects chosen per `n`; per `ω` in the transfer claims); the `_weighted` claims are the `_inexact`
ones applied to it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL4

open StatFormal.OTFD.WaveL1 StatFormal.OTFD.WaveL3

theorem inexactFit_of_weightedFit : Claims.inexactFit_of_weightedFit := by
  intro K μ P U α ν χn g ζ hUc hW
  obtain ⟨hα, hν, hζ0, hζ, hdat, hg⟩ := hW
  have hex : ∀ n, ∃ (π : ProbabilityMeasure (Euc K × Euc K)) (d : Euc K × Euc K → ℝ),
      (π : Measure (Euc K × Euc K)).fst = α n ∧ (π : Measure (Euc K × Euc K)).snd = ν n ∧
      (α n : Measure (Euc K)) Uᶜ = 0 ∧ ConvexOn ℝ univ (χn n) ∧ Measurable d ∧
      ∫⁻ z, ENNReal.ofReal (d z) ∂(π : Measure (Euc K × Euc K)) ≤ ENNReal.ofReal (ζ n / 2) ∧
      ∀ᵐ z ∂(π : Measure (Euc K × Euc K)), ∀ x ∈ U, χn n z.1 + ⟪z.2, x - z.1⟫ ≤ χn n x + d z := by
    intro n
    obtain ⟨m, N, β, ug, w, Z, f, hβ0, hβ1, hw0, hw1, hug, hαn, hνn, hχn, hgap⟩ := hdat n
    obtain ⟨hconv, π, d, hfst, hsnd, hdm, hint, hineq⟩ :=
      weighted_gap_plan_form K m N β ug w Z f U (ζ n) hβ0 hβ1 hw0 hw1 hUc hug hgap
    refine ⟨π, d, by rw [hfst, hαn], by rw [hsnd, hνn], ?_, by rw [hχn]; exact hconv, hdm, hint,
      Eventually.of_forall fun z x hx => by rw [hχn]; exact hineq z x hx⟩
    rw [hαn, Measure.finsetSum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hUc.isClosed.measurableSet.compl]
    simp [hug j]
  choose π d hfst hsnd hαU hconv hdm hint hineq using hex
  refine ⟨π, d, hα, hν, hfst, hsnd, hαU, hconv, fun n => div_nonneg (hζ0 n) zero_le_two, ?_, hdm,
    hint, hineq, hg⟩
  simpa using hζ.div_const 2

theorem cond_potentials_weighted : Claims.cond_potentials_weighted := by
  intro K μ P U Q α ν χn g ζ hR hP1 hQ hmap hcm hW
  obtain ⟨π, d, hF⟩ := inexactFit_of_weightedFit K μ P U α ν χn g ζ hR.2.2.1 hW
  exact cond_potentials_inexact K μ P U Q α ν π χn g _ d hR hP1 hQ hmap hcm hF

theorem cond_maps_ae_weighted : Claims.cond_maps_ae_weighted := by
  intro K μ P U χ Q Qn α ν χn g ζ hR hP1 hQ hmap hχ hQχ hW hg hQn
  obtain ⟨π, d, hF⟩ := inexactFit_of_weightedFit K μ P U α ν χn g ζ hR.2.2.1 hW
  exact cond_maps_ae_inexact K μ P U χ Q Qn α ν π χn g _ d hR hP1 hQ hmap hχ hQχ hF hg hQn

theorem cond_band_one_sided_weighted : Claims.cond_band_one_sided_weighted := by
  intro K 𝒯 μ P U A χ Q Qn α ν χn g ζ e R EK hR hP1 hQ hmap hχ hQχ hW hg hQn hA hRb he
  obtain ⟨π, d, hF⟩ := inexactFit_of_weightedFit K μ P U α ν χn g ζ hR.2.2.1 hW
  exact cond_band_one_sided_inexact K 𝒯 μ P U A χ Q Qn α ν π χn g _ d e R EK hR hP1 hQ hmap hχ hQχ
    hF hg hQn hA hRb he

theorem cond_test_coverage_weighted : Claims.cond_test_coverage_weighted := by
  intro K 𝒯 μ P U A χ Q Qn α ν χn g ζ m e Ue Le R EK p κ hR hP1 hQ hmap hχ hQχ hW hg hQn hA hRb he
    hp hκ hband
  obtain ⟨π, d, hF⟩ := inexactFit_of_weightedFit K μ P U α ν χn g ζ hR.2.2.1 hW
  exact cond_test_coverage_inexact K 𝒯 μ P U A χ Q Qn α ν π χn g _ d m e Ue Le R EK p κ hR hP1 hQ
    hmap hχ hQχ hF hg hQn hA hRb he hp hκ hband

variable {K : ℕ}

/-- Per-realisation choice of the plans and defects. -/
theorem exists_plans_of_weightedFit {Ω : Type} {μ P' : ProbabilityMeasure (Euc K)}
    {U : Set (Euc K)} (hU : IsCompact U) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K))
    (χn g : ℕ → Ω → Euc K → ℝ) (ζ : ℕ → Ω → ℝ) :
    ∃ (π : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K)) (d : ℕ → Ω → Euc K × Euc K → ℝ),
      ∀ ω, WeightedFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => χn n ω) (fun n => g n ω)
          (fun n => ζ n ω) →
        InexactFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => π n ω) (fun n => χn n ω)
          (fun n => g n ω) (fun n => ζ n ω / 2) (fun n => d n ω) := by
  have hex : ∀ ω, ∃ (πω : ℕ → ProbabilityMeasure (Euc K × Euc K)) (dω : ℕ → Euc K × Euc K → ℝ),
      WeightedFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => χn n ω) (fun n => g n ω)
          (fun n => ζ n ω) →
        InexactFit μ P' U (fun n => α n ω) (fun n => ν n ω) πω (fun n => χn n ω)
          (fun n => g n ω) (fun n => ζ n ω / 2) dω := by
    intro ω
    by_cases h : WeightedFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => χn n ω)
      (fun n => g n ω) (fun n => ζ n ω)
    · obtain ⟨πω, dω, hF⟩ := inexactFit_of_weightedFit K μ P' U _ _ _ _ _ hU h
      exact ⟨πω, dω, fun _ => hF⟩
    · exact ⟨fun _ => ⟨Measure.dirac 0, inferInstance⟩, fun _ _ => 0, fun h' => absurd h' h⟩
  choose πf df hπf using hex
  exact ⟨fun n ω => πf ω n, fun n ω => df ω n, hπf⟩

theorem cond_transfer_consistency_weighted : Claims.cond_transfer_consistency_weighted := by
  intro K Ω _ P μ P' U DF Z F Fh χ' Q' Qh α ν χn g ζ hR hZ hF hmapZ hZD hrank hχ' hQ' hP1 hQm
    hmap hfit hQh
  obtain ⟨π, d, hπ⟩ := exists_plans_of_weightedFit (μ := μ) (P' := P') hR.2.2.1 α ν χn g ζ
  exact cond_transfer_consistency_inexact K Ω P μ P' U DF Z F Fh χ' Q' Qh α ν π χn g
    (fun n ω => ζ n ω / 2) d hR hZ hF hmapZ hZD hrank hχ' hQ' hP1 hQm hmap
    (by filter_upwards [hfit] with ω ⟨hW, hg⟩ using ⟨hπ ω hW, hg⟩) hQh

theorem cond_transfer_consistency_prob_weighted :
    Claims.cond_transfer_consistency_prob_weighted := by
  intro K Ω _ P _ μ P' U DF Z F Fh χ' Q' Qh α ν χn g ζ hR hZ hF hmapZ hZD hrank hχ' hQ' hP1 hQm
    hmap hfit hQh hmeas
  obtain ⟨π, d, hπ⟩ := exists_plans_of_weightedFit (μ := μ) (P' := P') hR.2.2.1 α ν χn g ζ
  exact cond_transfer_consistency_prob_inexact K Ω P μ P' U DF Z F Fh χ' Q' Qh α ν π χn g
    (fun n ω => ζ n ω / 2) d hR hZ hF hmapZ hZD hrank hχ' hQ' hP1 hQm hmap
    (by filter_upwards [hfit] with ω ⟨hW, hg⟩ using ⟨hπ ω hW, hg⟩) hQh hmeas

end StatFormal.OTFD.WaveL4
