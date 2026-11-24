import StatFormal.Archive.OTFD.Wave22a.Statements
import StatFormal.Archive.OTFD.Scale.Route
import TauCeti.MeasureTheory.OptimalTransport.Brenier

/-!
# Route — otfd A `lem:T-stability`, the "in particular" (untrusted)

* `Υ#ν = Υ#μ ⇒ ν = μ`: `μ` and hence `ν` live on `D = {c_K(g) < 1}`, where `S ∘ Υ = id` with `S` continuous on the open
  ball `𝔹`; for open `A`, `ν(A) = ν(Υ⁻¹(𝔹 ∩ S⁻¹A)) = (Υ#ν)(𝔹 ∩ S⁻¹A)`, and open sets determine finite Borel measures;
* then `G#P_K = μ_K`, and `F`, `G` are a.e. gradients of convex functions pushing `P_K` to `μ_K`: both are optimal
  transport maps (Knott–Smith, Tau Ceti), and Brenier's uniqueness (`P_K ≪` Haar) gives `G = F` `P_K`-a.e.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.Wave22a

open StatFormal.OTFD.Scale

theorem t_stability_push : Claims.t_stability_push := by
  intro E _ _ _ _ _ μ _ g hg h ν _ hνμ
  have hgc : Continuous g := hg.continuous
  have hups : Continuous (ups μ g) := continuous_ups hg h
  set D : Set E := {r | cK μ g (g r) < 1}
  set Bl : Set E := {w | g w < 1}
  have hBo : IsOpen Bl := isOpen_lt hgc continuous_const
  have hpre : ups μ g ⁻¹' Bl = D := by
    ext r; simp only [mem_preimage, Bl, D, mem_setOf_eq, g_ups hg h]
  have hμD : μ D = 1 := measure_ups_ball hg h
  have hνD : ν D = 1 := by
    have := congrArg (fun m : Measure E => m Bl) hνμ
    rw [Measure.map_apply hups.measurable hBo.measurableSet,
      Measure.map_apply hups.measurable hBo.measurableSet, hpre, hμD] at this
    exact this
  have hDm : MeasurableSet D := by
    rw [← hpre]; exact hBo.measurableSet.preimage hups.measurable
  have hνc : ν Dᶜ = 0 := by rw [measure_compl hDm (measure_ne_top _ _), hνD, measure_univ, tsub_self]
  have hμc : μ Dᶜ = 0 := by rw [measure_compl hDm (measure_ne_top _ _), hμD, measure_univ, tsub_self]
  have hS := continuousOn_Sinv hg h
  have hopen : ∀ A : Set E, IsOpen A → ν A = μ A := by
    intro A hA
    set BA : Set E := Bl ∩ Sinv μ g ⁻¹' A
    have hBA : IsOpen BA := hS.isOpen_inter_preimage hBo hA
    have hpreA : ups μ g ⁻¹' BA ∩ D = A ∩ D := by
      ext r
      simp only [BA, mem_inter_iff, mem_preimage, Bl, D, mem_setOf_eq, g_ups hg h]
      constructor
      · rintro ⟨⟨_, hrA⟩, hrD⟩
        rw [S_ups hg h hrD] at hrA
        exact ⟨hrA, hrD⟩
      · rintro ⟨hrA, hrD⟩
        exact ⟨⟨hrD, by rw [S_ups hg h hrD]; exact hrA⟩, hrD⟩
    have key : ∀ (m : Measure E), m Dᶜ = 0 → m A = (m.map (ups μ g)) BA := fun m hm => by
      rw [Measure.map_apply hups.measurable hBA.measurableSet, ← measure_inter_conull hm,
        ← measure_inter_conull (s := ups μ g ⁻¹' BA) hm, hpreA]
    rw [key ν hνc, key μ hμc, hνμ]
  refine ext_of_generate_finite {s : Set E | IsOpen s} ?_ isPiSystem_isOpen
    (fun s hs => hopen s hs) (by simp)
  exact (BorelSpace.measurable_eq).trans rfl

lemma grad_mem_subdiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {φ : E → ℝ} (hφ : ConvexOn ℝ univ φ) {x y : E} (hxy : HasGradientAt φ y x) :
    y ∈ TauCeti.subdifferential (innerₗ E) (fun x => (φ x : EReal)) x := by
  have hfun : (fun x' => ((φ x' : EReal)).toReal) = φ := funext fun _ => EReal.toReal_coe _
  have hconv : Convex ℝ {p : E × ℝ | ((φ p.1 : EReal)) ≤ (p.2 : EReal)} := by
    have := hφ.convex_epigraph
    simp only [mem_univ, true_and] at this
    simpa only [EReal.coe_le_coe_iff] using this
  have := TauCeti.gradient_toReal_mem_subdifferential (f := fun x => (φ x : EReal)) hconv
    (fun _ => EReal.coe_ne_bot _) (EReal.coe_ne_top _) (by rw [hfun]; exact hxy.differentiableAt)
  rwa [hfun, hxy.gradient] at this

theorem t_stability_eq : Claims.t_stability_eq := by
  intro K ρ _ μ _ g P _ F G hg h hμ2 hPρ hP2 hF hG hPF ⟨φF, hφF, hgF⟩ ⟨φG, hφG, hgG⟩ hpush
  have hPG : P.map G = μ := by
    have : IsProbabilityMeasure (P.map G) := inferInstance
    exact t_stability_push _ μ g hg h (P.map G) hpush
  set c : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)
  have hlawF : ProbabilityTheory.HasLaw F μ P := ⟨hF.aemeasurable, hPF⟩
  have hlawG : ProbabilityTheory.HasLaw G μ P := ⟨hG.aemeasurable, hPG⟩
  have hoptF : TauCeti.IsKantorovichOptimalTransportMap c P μ F :=
    TauCeti.isKantorovichOptimalTransportMap_of_ae_mem_subdifferential hP2 hμ2 hlawF
      (hgF.mono fun x hx => grad_mem_subdiff hφF hx)
  have hoptG : TauCeti.IsKantorovichOptimalTransportMap c P μ G :=
    TauCeti.isKantorovichOptimalTransportMap_of_ae_mem_subdifferential hP2 hμ2 hlawG
      (hgG.mono fun x hx => grad_mem_subdiff hφG hx)
  have hc : Continuous c :=
    ENNReal.continuous_ofReal.comp (((continuous_fst.sub continuous_snd).norm.pow 2).div_const 2)
  have hfin : TauCeti.transportCost c P μ ≠ ∞ := by
    have hcoup := (TauCeti.isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hlawF
      hc.measurable.aemeasurable).1 hoptF
    rw [← hcoup.lintegral_eq, (TauCeti.isCoupling_graphPlan hlawF).lintegral_norm_sub_sq_div_two hP2 hμ2]
    exact ENNReal.ofReal_ne_top
  obtain ⟨u, -, -, -, -, -, -, huniq⟩ :=
    TauCeti.exists_isKantorovichOptimalTransportMap_gradient (ρ := ρ) hPρ hfin
  exact (huniq G hoptG).trans (huniq F hoptF).symm

end StatFormal.OTFD.Wave22a
