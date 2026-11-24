import StatFormal.Archive.Wave30ao.RouteCore

/-!
# Route — the wave 30ao claims (untrusted)
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

theorem cost_finite_iff : Claims.cost_finite_iff := by
  intro d ε μ ν hε hμ hν hμ2 hν2
  refine ⟨⟨fin_of_cost hμ2 hν2, fun h => cost_of_fin hμ2 hν2 h.1 h.2⟩,
    fun π hπ hac hpos => finite_of_coupling hμ2 hν2 hπ hac hpos, fun π hπ => ?_⟩
  rw [entObj_eq_top_iff hμ2 hν2 ε hπ]
  constructor
  · intro hn h; exact hn (finite_of_coupling hμ2 hν2 hπ h.1 h.2).1
  · intro hn hf; exact hn ⟨hf.1, hf.2.pos_part⟩

theorem equiv_display_printed : Claims.equiv_display_printed := by
  intro d ε μ ν hε hμ hν hμ2 hν2 hc π hπ
  obtain ⟨hμf, hνf⟩ := fin_of_cost hμ2 hν2 hc
  obtain ⟨K1, K2⟩ := kl_ref hμ2 hν2 hε hμf hνf hπ
  refine ⟨fun hf => ⟨(K1 hf).1, ?_⟩, K2⟩
  have h := (K1 hf).2
  rw [integral_div] at h
  field_simp
  linear_combination 2 * h

theorem equiv_printed : Claims.equiv_printed := by
  intro Ω _ d ε μ ν X R hε hμ hν hμ2 hν2 hc hR
  obtain ⟨hμf, hνf⟩ := fin_of_cost hμ2 hν2 hc
  obtain ⟨hsv, -, -, -, -⟩ := static_ac hμ2 hν2 hε hνf
  obtain ⟨-, hex, huniq, -⟩ := StatFormal.Wave29t.equiv_bridge_d Ω d ε μ ν X R hε hμ hR
  obtain ⟨π₀, hπ₀, -⟩ := exists_unique_printed hμ2 hν2 hε hμf hνf
  have hcost := entCost_eq_of_printed hπ₀
  have hf₀ : HasFiniteEnt π₀ := by
    by_contra h; exact hπ₀.2.1 (entObj_of_not ε h)
  rw [hcost, entObj_of_fin hμ2 hν2 ε hπ₀.1 hf₀]
  refine ⟨EReal.coe_ne_bot _, hμf, exists_unique_printed hμ2 hν2 hε hμf hνf,
    ⟨(hex.2 hsv).choose, (hex.2 hsv).choose_spec, fun P hP => huniq P _ hP (hex.2 hsv).choose_spec⟩,
    fun P hP => ?_⟩
  obtain ⟨-, hst, hkl, ⟨g, hg, -, hPg⟩, ht⟩ := StatFormal.Wave29t.mixtureD_bridge Ω d ε μ ν X R P hε hμ hR hP
  have hpr : IsPrintedPlan ε μ ν (P.map (fun ω => (X 0 ω, X 1 ω))) :=
    (printed_iff_static hμ2 hν2 hε hμf hνf _).2 hst
  have heq : P.map (fun ω => (X 0 ω, X 1 ω)) = π₀ :=
    (exists_unique_printed hμ2 hν2 hε hμf hνf).unique hpr hπ₀
  refine ⟨hpr, ?_, ⟨g, hg, hPg⟩, fun t htt => (ht t htt).1, ?_⟩
  · rw [heq, entObj_of_fin hμ2 hν2 ε hπ₀.1 hf₀]
  · rw [hkl, heq, ((kl_ref hμ2 hν2 hε hμf hνf hπ₀.1).1 hf₀).2, EReal.toReal_coe]

theorem repair_premise : Claims.repair_premise := by
  intro d ε Rs ν hε hRs hν hR2 hν2
  have iff : (∀ s, entCost ε (Rs s) ν < ⊤) ↔ (∀ s, HasFiniteEnt (Rs s)) ∧ HasFiniteEnt ν := by
    constructor
    · intro h
      exact ⟨fun s => (@fin_of_cost d (Rs s) ν (hRs s) hν (hR2 s) hν2 ε (h s)).1,
        (@fin_of_cost d (Rs 0) ν (hRs 0) hν (hR2 0) hν2 ε (h 0)).2⟩
    · rintro ⟨h1, h2⟩ s
      exact @cost_of_fin d (Rs s) ν (hRs s) hν (hR2 s) hν2 ε (h1 s) h2
  refine ⟨iff, fun h => ?_⟩
  obtain ⟨hRf, hνf⟩ := iff.1 h
  obtain ⟨hq, hq0, hνq, hlog, hint⟩ := q_of_fin hνf
  refine ⟨⟨_, hq, hq0, hνq, hlog, hint⟩, fun s => ?_⟩
  obtain ⟨hsv, hetc, -, -, -⟩ := @static_ac d (Rs s) ν (hRs s) hν (hR2 s) hν2 ε hε hνf
  refine ⟨hsv, hetc, fun Ω _ X R hR => ?_⟩
  obtain ⟨-, hex, huniq, -⟩ := StatFormal.Wave29t.equiv_bridge_d Ω d ε (Rs s) ν X R hε (hRs s) hR
  exact ⟨(hex.2 hsv).choose, (hex.2 hsv).choose_spec, fun P hP => huniq P _ hP (hex.2 hsv).choose_spec⟩

theorem mixture_printed : Claims.mixture_printed := by
  intro Ω _ d ε μ ν X R hε hμ hν hμ2 hν2 hc hR
  obtain ⟨hμf, hνf⟩ := fin_of_cost hμ2 hν2 hc
  obtain ⟨hsv, -, -, -, -⟩ := static_ac hμ2 hν2 hε hνf
  obtain ⟨-, hex, huniq, -⟩ := StatFormal.Wave29t.equiv_bridge_d Ω d ε μ ν X R hε hμ hR
  refine ⟨⟨(hex.2 hsv).choose, (hex.2 hsv).choose_spec, fun P hP => huniq P _ hP (hex.2 hsv).choose_spec⟩,
    fun π P hπ hP t htt => ?_⟩
  obtain ⟨-, hst, -, -, ht⟩ := StatFormal.Wave29t.mixtureD_bridge Ω d ε μ ν X R P hε hμ hR hP
  have heq : P.map (fun ω => (X 0 ω, X 1 ω)) = π :=
    (exists_unique_printed hμ2 hν2 hε hμf hνf).unique ((printed_iff_static hμ2 hν2 hε hμf hνf _).2 hst) hπ
  obtain ⟨-, h2, h3⟩ := ht t htt
  rw [heq] at h2 h3
  exact ⟨h2, h3⟩

theorem convention_printed : Claims.convention_printed := by
  intro d ε μ ν hε hμ hν hμ2 hν2 hμf hνf
  obtain ⟨-, -, hiff, -, -⟩ := static_ac hμ2 hν2 hε hνf
  refine ⟨fun π hπ => ⟨fun hf => (kl_mn hμf hνf hπ hf).1, fin_of_kl hμf hνf hπ⟩,
    fun π hπ hf => (kl_mn hμf hνf hπ hf).2, fun π hπ hf => ?_,
    fun π => (printed_iff_static hμ2 hν2 hε hμf hνf π).trans (hiff π), exists_unique_printed hμ2 hν2 hε hμf hνf⟩
  rw [(kl_mn hμf hνf hπ hf).2]
  ring

theorem plan_literal : Claims.plan_literal := by
  intro d ε μ ν hε hμ hν hμ2 hν2
  refine ⟨fun hc => ?_, fun hn π hπ => ?_⟩
  · obtain ⟨hμf, hνf⟩ := fin_of_cost hμ2 hν2 hc
    exact exists_unique_printed hμ2 hν2 hε hμf hνf
  · by_contra h
    have hf : HasFiniteEnt π := by
      by_contra h'; exact h (entObj_of_not ε h')
    exact hn (finite_of_coupling hμ2 hν2 hπ hf.1 hf.2.pos_part).2

theorem cost_atom : Claims.cost_atom := by
  intro d ε μ ν hd _ hμ hν hat
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hnac : ∀ π : Measure ((E d) × (E d)), IsCoupling π μ ν → ¬ π ≪ volume := by
    intro π hπ hac
    have hac' : π ≪ (volume : Measure (E d)).prod volume := hac
    have h1 : μ ≪ volume := hπ.fst_eq ▸ ac_fst_of_ac hac'
    have h2 : ν ≪ volume := hπ.snd_eq ▸ ac_snd_of_ac hac'
    rcases hat with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact ha (h1 (measure_singleton a))
    · exact hb (h2 (measure_singleton b))
  refine ⟨hnac, ?_⟩
  simp only [entCost, iInf_eq_top]
  intro π hπ
  exact entObj_of_not ε (fun hf => hnac π hπ hf.1)

end StatFormal.Wave30ao
