import StatFormal.Archive.OTFD.WaveL8.Statements
import StatFormal.Archive.OTFD.WaveL8.RouteGeneral
import StatFormal.Archive.OTFD.WaveL3.RouteCondClaims
import StatFormal.Archive.OTFD.WaveL4.RouteWeighted
import StatFormal.Archive.Wave24e.RouteCondRankUncond

/-!
# Route (wave L8): C `prop:conditional-potentials` and its limits without the target's first moment

Untrusted route file. Each theorem is the frozen route of the same name (`OTFD/WaveL3/RouteCond{,Claims}`,
`OTFD/WaveL4/Route{Inexact,Claims,Weighted}`, `Wave24e/RouteCondRankUncond`), copied mechanically with the first
moment `Mom1 P ≠ ∞` (`hP1`, `hm1`) deleted from every hypothesis list and call. Its only use was the uniqueness
`brenierUniq_of_bdd_source … hP1 …` inside `cond_core` / `cond_core_inexact`, now replaced by the moment-free
`RouteGeneral.brenierUniq_general` (Lipschitz-null source `μ_K ≪ Leb`, any target). Calls between the copied
theorems are redirected to the wave-L8 copies; everything else is the certified original.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace StatFormal.OTFD.WaveL8

section OTFD_WaveL3_RouteCond

open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.WaveL1
open StatFormal.OTFD.WaveL3
variable {K : ℕ}

theorem cond_core {μ P : ProbabilityMeasure (Euc K)} {U : Set (Euc K)} {Q : Euc K → Euc K}
    {α ν : ℕ → ProbabilityMeasure (Euc K)} {π : ℕ → ProbabilityMeasure (Euc K × Euc K)}
    {χn g : ℕ → Euc K → ℝ} (hR : RefLaw (μ : Measure (Euc K)) U)
    (hQ : Measurable Q) (hmap : (μ : Measure (Euc K)).map Q = P) (hcm : IsCMMapAE (μ : Measure (Euc K)) Q)
    (hF : HardFit μ P U α ν π χn g) :
    ∃ φ : Euc K → ℝ, ConvexOn ℝ (interior U) φ ∧ Q =ᵐ[(μ : Measure (Euc K))] gradient φ ∧
      IsGLB (φ '' interior U) 0 ∧
      ∀ c : ℕ → ℝ, (∀ n, IsGLB (χn n '' U) (c n)) → ∀ S ⊆ interior U, IsCompact S →
        TendstoUniformlyOn (fun n u => χn n u - c n) φ atTop S := by
  have hne := interior_nonempty_of_refLaw hR
  obtain ⟨hac, hU, hUk, hUc, hsupp⟩ := hR
  obtain ⟨hα, hν, hfst, hsnd, hχc, hsub, -⟩ := hF
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨M, hM⟩ := refLaw_ball hUk hUc
  have hint := StatFormal.OTFD.Wave22b.ae_mem_interior hac hU hUc
  have hintc : (μ : Measure (Euc K)) (interior U)ᶜ = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hint.mono fun _ h h' => h' h)
  -- 1. uniqueness of cyclically monotone couplings, plan convergence
  have huniq := StatFormal.OTFD.WaveL8.brenierUniq_general (lipNull_of_ac (ρ := volume) hac) hQ hmap hcm
  set G : ProbabilityMeasure (Euc K × Euc K) := μ.map (fun x => (x, Q x)) with hGdef
  have hG : (G : Measure (Euc K × Euc K)) = Graph (μ : Measure (Euc K)) Q := rfl
  have hcmπ : ∀ n, CMConc (π n : Measure (Euc K × Euc K)) := fun n =>
    cmConc_of_ae (cycMon_subgradGraph (χn n)) (hsub n)
  have hπ : Tendsto π atTop (𝓝 G) := tendsto_of_cmConc huniq hα hν hfst hsnd hcmπ hG
  have hGfst : (G : Measure (Euc K × Euc K)).fst = μ := by rw [hG]; exact graph_fst hQ
  -- 2. limit potential (library), normalised at `x₀`
  set us : ℕ → Euc K → ℝ := fun n u => χn n u - χn n x₀ with hus
  have hconv : ∀ n, ConvexOn ℝ (interior U) (us n) := fun n =>
    convexOn_sub_const ((hχc n).subset (subset_univ _) hU.interior) _
  have hpot : ∀ n, StatFormal.Potentials.IsPotentialOn (interior U) (us n)
      (π n : Measure (Euc K × Euc K)) := by
    intro n
    refine StatFormal.Potentials.isPotentialOn_of_ae isOpen_interior
      ((continuous_of_convexOn_univ (hχc n)).sub continuous_const).continuousOn ?_
    filter_upwards [hsub n] with z hz _ x _
    have := hz x
    change χn n z.1 - χn n x₀ + ⟪z.2, x - z.1⟫ ≤ χn n x - χn n x₀
    linarith
  obtain ⟨φ, hφc, hφ0, -, hφae, hφlim⟩ :=
    StatFormal.Potentials.exists_tendstoLocallyUniformlyOn_potential (ρ := volume)
      isOpen_interior hx₀ hπ (by rw [hGfst]; exact hac) (by rw [hGfst]; exact hintc)
      (by rw [hGfst]; exact hsupp) (Eventually.of_forall hconv) (Eventually.of_forall hpot)
      (a := 0) (by simp [hus])
  -- 3. the gradient is the population map
  have hQφ : Q =ᵐ[(μ : Measure (Euc K))] gradient φ := by
    have h1 : ∀ᵐ z ∂(G : Measure (Euc K × Euc K)), z.1 ∈ interior U → z.2 = gradient φ z.1 := hφae
    rw [hG, Graph] at h1
    have h2 := ae_of_ae_map (measurable_id.prodMk hQ).aemeasurable h1
    filter_upwards [h2, hint] with x hx hxU using hx hxU
  -- 4. normalisation by the infimum
  have hbdd := bddBelow_image_of_convexOn isOpen_interior (hUk.isBounded.subset interior_subset) hφc
  set m₀ := sInf (φ '' interior U) with hm₀def
  have hm₀ : IsGLB (φ '' interior U) m₀ := isGLB_csInf (Set.Nonempty.image φ ⟨x₀, hx₀⟩) hbdd
  refine ⟨fun u => φ u - m₀, convexOn_sub_const hφc m₀, by rwa [gradient_sub_const'], ?_, ?_⟩
  · simpa using isGLB_sub_const hm₀ m₀
  intro c hc S hSU hSc
  have hcl := subset_closure_interior hU ⟨x₀, hx₀⟩
  have hcint : ∀ n, IsGLB (us n '' interior U) (c n - χn n x₀) := fun n =>
    isGLB_sub_const ((isGLB_image_iff_interior (continuous_of_convexOn_univ (hχc n)) hcl _).1 (hc n)) _
  have hd : Tendsto (fun n => c n - χn n x₀) atTop (𝓝 m₀) :=
    tendsto_of_isGLB isOpen_interior hU.interior (hUk.isBounded.subset interior_subset) hx₀ hconv
      hφlim hcint hm₀
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_interior).1 hφlim S hSU hSc
  rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
  intro ε hε
  have hd' := Metric.tendsto_atTop.1 hd (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := hd'
  filter_upwards [hunif (ε / 2) (half_pos hε), eventually_ge_atTop N] with n hn hnN u hu
  have h1 := hn u hu
  have h2 := hN n hnN
  rw [Real.dist_eq] at h1 h2 ⊢
  simp only [hus] at h1
  have e : φ u - m₀ - (χn n u - c n) = (φ u - (χn n u - χn n x₀)) + ((c n - χn n x₀) - m₀) := by ring
  rw [e]
  calc |φ u - (χn n u - χn n x₀) + (c n - χn n x₀ - m₀)|
      ≤ |φ u - (χn n u - χn n x₀)| + |c n - χn n x₀ - m₀| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := add_halves ε

end OTFD_WaveL3_RouteCond

section OTFD_WaveL3_RouteCondClaims

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.WaveL1
open StatFormal.OTFD.WaveL3
variable {K : ℕ}

theorem cond_potentials : StatFormal.OTFD.WaveL8.Claims.cond_potentials := by
  intro K μ P U Q α ν π χn g hR hQ hmap hcm hF
  obtain ⟨φ, hφc, hQφ, hφ0, hconvg⟩ := StatFormal.OTFD.WaveL8.cond_core hR hQ hmap hcm hF
  refine ⟨⟨φ, hφc, hQφ, hφ0⟩, fun χ hχc hQχ hχ0 c hc S hSU hSc => ?_⟩
  obtain ⟨C, hC⟩ := ConvexOn.exists_eq_add_const_of_ae_gradient_eq (ρ := volume) isOpen_interior
    hχc hφc hR.1 hR.2.2.2.2 (by filter_upwards [hQχ, hQφ] with z h1 h2 _; rw [← h1, ← h2])
  have hC1 : C ≤ 0 := hχ0.2 (by
    rintro _ ⟨z, hz, rfl⟩
    have := hφ0.1 ⟨z, hz, rfl⟩
    rw [hC z hz]
    linarith)
  have hC2 : -C ≤ 0 := hφ0.2 (by
    rintro _ ⟨z, hz, rfl⟩
    have := hχ0.1 ⟨z, hz, rfl⟩
    rw [hC z hz] at this
    linarith)
  have heq : EqOn φ χ S := fun u hu => by rw [hC u (hSU hu)]; linarith
  have h1 := (hconvg c hc S hSU hSc).congr_right heq
  refine ⟨h1, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff] at h1 ⊢
  intro ε hε
  filter_upwards [h1 (ε / 2) (half_pos hε), hF.2.2.2.2.2.2 (ε / 4) (by positivity)] with n hn hg u hu
  have a1 := hn u hu
  have a2 := hg u (interior_subset (hSU hu))
  rw [Real.dist_eq] at a1 ⊢
  have e : χ u - (g n u - c n) = (χ u - (χn n u - c n)) - (g n u - χn n u) := by ring
  rw [e]
  calc |χ u - (χn n u - c n) - (g n u - χn n u)|
      ≤ |χ u - (χn n u - c n)| + |g n u - χn n u| := abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le a1 (by linarith)
    _ = ε := add_halves ε

theorem premise_of_hardFit {μ P : ProbabilityMeasure (Euc K)} {U : Set (Euc K)} {Q : Euc K → Euc K}
    {α ν : ℕ → ProbabilityMeasure (Euc K)} {π : ℕ → ProbabilityMeasure (Euc K × Euc K)}
    {χn g : ℕ → Euc K → ℝ} {χ : Euc K → ℝ} {m : ℝ} (hR : RefLaw (μ : Measure (Euc K)) U)
    (hQ : Measurable Q) (hmap : (μ : Measure (Euc K)).map Q = P)
    (hχ : ConvexOn ℝ (interior U) χ) (hQχ : Q =ᵐ[(μ : Measure (Euc K))] gradient χ)
    (hm : IsGLB (χ '' interior U) m) (hF : HardFit μ P U α ν π χn g) :
    ∀ S ⊆ interior U, IsCompact S →
      TendstoUniformlyOn (fun n u => g n u - sInf (χn n '' U)) (fun u => χ u - m) atTop S := by
  intro S hSU hSc
  have hcm := isCMMapAE_of_gradient hR.1 hR.2.1 hR.2.2.2.1 hχ hQχ
  have hUne : U.Nonempty := (interior_nonempty_of_refLaw hR).mono interior_subset
  exact ((StatFormal.OTFD.WaveL8.cond_potentials K μ P U Q α ν π χn g hR hQ hmap hcm hF).2 (fun u => χ u - m)
    (convexOn_sub_const hχ m) (by rwa [gradient_sub_const'])
    (by simpa using isGLB_sub_const hm m) (fun n => sInf (χn n '' U))
    (fun n => exists_isGLB_of_convexOn_univ hR.2.2.1 hUne (hF.2.2.2.2.1 n)) S hSU hSc).2

theorem cond_maps_ae_plans : StatFormal.OTFD.WaveL8.Claims.cond_maps_ae_plans := by
  intro K μ P U χ Q Qn α ν π χn g hR hQ hmap hχ hQχ hF hg hQn
  obtain ⟨m, hm⟩ := exists_isGLB_pop hR hχ
  have h := StatFormal.OTFD.Wave22b.cond_maps_ae K μ U (fun u => χ u - m)
    (fun n u => g n u - sInf (χn n '' U)) Q Qn hR.1 hR.2.1 hR.2.2.2.1 (convexOn_sub_const hχ m)
    (fun n => convexOn_sub_const (hg n) _) (StatFormal.OTFD.WaveL8.premise_of_hardFit hR hQ hmap hχ hQχ hm hF)
    (by rwa [gradient_sub_const']) (fun n u hu => mem_subdiff_extTop_sub _ (hQn n u hu))
  filter_upwards [h] with u ⟨h1, h2, h3⟩
  exact ⟨h1, differentiableAt_of_sub_const h2, h3⟩

theorem cond_band_one_sided_plans : StatFormal.OTFD.WaveL8.Claims.cond_band_one_sided_plans := by
  intro K 𝒯 μ P U A χ Q Qn α ν π χn g e R EK hR hQ hmap hχ hQχ hF hg hQn hA hRb he
  obtain ⟨m, hm⟩ := exists_isGLB_pop hR hχ
  exact StatFormal.OTFD.Wave22b.cond_band_one_sided_potentials K 𝒯 μ U A (fun u => χ u - m)
    (fun n u => g n u - sInf (χn n '' U)) Q Qn e R EK hR.1 hR.2.1 hR.2.2.2.1
    (convexOn_sub_const hχ m) (fun n => convexOn_sub_const (hg n) _)
    (StatFormal.OTFD.WaveL8.premise_of_hardFit hR hQ hmap hχ hQχ hm hF) (by rwa [gradient_sub_const'])
    (fun n u hu => mem_subdiff_extTop_sub _ (hQn n u hu)) hA hRb he

theorem cond_test_coverage_plans : StatFormal.OTFD.WaveL8.Claims.cond_test_coverage_plans := by
  intro K 𝒯 μ P U A χ Q Qn α ν π χn g m e Ue Le R EK p κ hR hQ hmap hχ hQχ hF hg hQn hA hRb he hp
    hκ hband
  obtain ⟨m₀, hm₀⟩ := exists_isGLB_pop hR hχ
  exact StatFormal.OTFD.Wave22b.cond_test_coverage_potentials K 𝒯 μ U A (fun u => χ u - m₀)
    (fun n u => g n u - sInf (χn n '' U)) Q Qn m e Ue Le R EK p κ hR.1 hR.2.1 hR.2.2.2.1
    (convexOn_sub_const hχ m₀) (fun n => convexOn_sub_const (hg n) _)
    (StatFormal.OTFD.WaveL8.premise_of_hardFit hR hQ hmap hχ hQχ hm₀ hF) (by rwa [gradient_sub_const'])
    (fun n u hu => mem_subdiff_extTop_sub _ (hQn n u hu)) hQ hA hRb he hp hκ hband

theorem cond_transfer_consistency_plans : StatFormal.OTFD.WaveL8.Claims.cond_transfer_consistency_plans := by
  intro K Ω _ P μ P' U DF Z F Fh χ' Q' Qh α ν π χn g hR hZ hF hmapZ hZD hrank hχ' hQ' hQm hmap
    hfit hQh
  obtain ⟨m, hm⟩ := exists_isGLB_pop hR hχ'
  have hpot : ∀ᵐ ω ∂P, (∀ n, ConvexOn ℝ (interior U) (fun u => g n ω u - sInf (χn n ω '' U))) ∧
      ∀ S ⊆ interior U, IsCompact S → TendstoUniformlyOn
        (fun n => fun u => g n ω u - sInf (χn n ω '' U)) (fun u => χ' u - m) atTop S := by
    filter_upwards [hfit] with ω ⟨hFω, hgω⟩
    exact ⟨fun n => convexOn_sub_const (hgω n) _,
      StatFormal.OTFD.WaveL8.premise_of_hardFit hR hQm hmap hχ' hQ' hm hFω⟩
  have h := StatFormal.OTFD.Wave22b.cond_transfer_consistency K Ω P μ U DF Z F Fh
    (fun u => χ' u - m) (fun n ω u => g n ω u - sInf (χn n ω '' U)) Q' Qh hR.1 hR.2.1 hR.2.2.2.1
    hZ hF hmapZ hZD hrank (convexOn_sub_const hχ' m) (by rwa [gradient_sub_const']) hpot
    (fun n ω u hu => mem_subdiff_extTop_sub _ (hQh n ω u hu))
  filter_upwards [h] with ω ⟨h1, h2, h3, h4⟩
  rw [gradient_sub_const'] at h3
  exact ⟨h1, differentiableAt_of_sub_const h2, h3, h4⟩

theorem cond_transfer_consistency_prob_plans : StatFormal.OTFD.WaveL8.Claims.cond_transfer_consistency_prob_plans := by
  intro K Ω _ P _ μ P' U DF Z F Fh χ' Q' Qh α ν π χn g hR hZ hF hmapZ hZD hrank hχ' hQ' hQm hmap
    hfit hQh hmeas
  have h := StatFormal.OTFD.WaveL8.cond_transfer_consistency_plans K Ω P μ P' U DF Z F Fh χ' Q' Qh α ν π χn g hR hZ hF hmapZ
    hZD hrank hχ' hQ' hQm hmap hfit hQh
  exact tendstoInMeasure_of_tendsto_ae hmeas (h.mono fun ω hω => hω.2.2.2)

end OTFD_WaveL3_RouteCondClaims

section OTFD_WaveL4_RouteInexact

open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.WaveL1 StatFormal.OTFD.WaveL3
open StatFormal.OTFD.WaveL4
variable {K : ℕ}

theorem cond_core_inexact {μ P : ProbabilityMeasure (Euc K)} {U : Set (Euc K)}
    {Q : Euc K → Euc K} {α ν : ℕ → ProbabilityMeasure (Euc K)}
    {π : ℕ → ProbabilityMeasure (Euc K × Euc K)} {χn g : ℕ → Euc K → ℝ} {ζ : ℕ → ℝ}
    {d : ℕ → Euc K × Euc K → ℝ} (hR : RefLaw (μ : Measure (Euc K)) U)
    (hQ : Measurable Q)
    (hmap : (μ : Measure (Euc K)).map Q = P) (hcm : IsCMMapAE (μ : Measure (Euc K)) Q)
    (hF : InexactFit μ P U α ν π χn g ζ d) :
    ∃ φ : Euc K → ℝ, ConvexOn ℝ (interior U) φ ∧ Q =ᵐ[(μ : Measure (Euc K))] gradient φ ∧
      IsGLB (φ '' interior U) 0 ∧
      ∀ c : ℕ → ℝ, (∀ n, IsGLB (χn n '' U) (c n)) → ∀ S ⊆ interior U, IsCompact S →
        TendstoUniformlyOn (fun n u => χn n u - c n) φ atTop S := by
  have hne := interior_nonempty_of_refLaw hR
  have hap := approxSubgrad_of_inexactFit hF hR.2.2.1.isClosed.measurableSet
  obtain ⟨hac, hU, hUk, hUc, hsupp⟩ := hR
  obtain ⟨hα, hν, hfst, hsnd, -, hχc, -⟩ := hF
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨M, hM⟩ := refLaw_ball hUk hUc
  have hint := StatFormal.OTFD.Wave22b.ae_mem_interior hac hU hUc
  have hintc : (μ : Measure (Euc K)) (interior U)ᶜ = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hint.mono fun _ h h' => h' h)
  -- 1. uniqueness of cyclically monotone couplings, plan convergence
  have huniq := StatFormal.OTFD.WaveL8.brenierUniq_general (lipNull_of_ac (ρ := volume) hac) hQ hmap hcm
  set G : ProbabilityMeasure (Euc K × Euc K) := μ.map (fun x => (x, Q x)) with hGdef
  have hG : (G : Measure (Euc K × Euc K)) = Graph (μ : Measure (Euc K)) Q := rfl
  have hπ : Tendsto π atTop (𝓝 G) := tendsto_of_approx huniq hα hν hfst hsnd hap hG
  have hGfst : (G : Measure (Euc K × Euc K)).fst = μ := by rw [hG]; exact graph_fst hQ
  -- 2. limit potential (approximate library), normalised at `x₀`
  set us : ℕ → Euc K → ℝ := fun n u => χn n u - χn n x₀ with hus
  have hconv : ∀ n, ConvexOn ℝ (interior U) (us n) := fun n =>
    convexOn_sub_const ((hχc n).subset (subset_univ _) hU.interior) _
  have hpot : ApproxPot atTop (interior U) us π := by
    intro δ hδ c hc
    filter_upwards [hap δ hδ c hc] with n hn V hV hcV
    obtain ⟨z, hzV, -, hz⟩ := hn V hV hcV
    refine ⟨z, hzV, fun _ x hx => ?_⟩
    have := hz x (interior_subset hx)
    simp only [hus]
    linarith
  obtain ⟨φ, hφc, hφ0, -, hφae, hφlim⟩ :=
    exists_tendstoLocallyUniformlyOn_potential_approx (ρ := volume)
      isOpen_interior hx₀ hπ (by rw [hGfst]; exact hac) (by rw [hGfst]; exact hintc)
      (by rw [hGfst]; exact hsupp) (Eventually.of_forall hconv) hpot
      (a := 0) (by simp [hus])
  -- 3. the gradient is the population map
  have hQφ : Q =ᵐ[(μ : Measure (Euc K))] gradient φ := by
    have h1 : ∀ᵐ z ∂(G : Measure (Euc K × Euc K)), z.1 ∈ interior U → z.2 = gradient φ z.1 := hφae
    rw [hG, Graph] at h1
    have h2 := ae_of_ae_map (measurable_id.prodMk hQ).aemeasurable h1
    filter_upwards [h2, hint] with x hx hxU using hx hxU
  -- 4. normalisation by the infimum
  have hbdd := bddBelow_image_of_convexOn isOpen_interior (hUk.isBounded.subset interior_subset) hφc
  set m₀ := sInf (φ '' interior U) with hm₀def
  have hm₀ : IsGLB (φ '' interior U) m₀ := isGLB_csInf (Set.Nonempty.image φ ⟨x₀, hx₀⟩) hbdd
  refine ⟨fun u => φ u - m₀, convexOn_sub_const hφc m₀, by rwa [gradient_sub_const'], ?_, ?_⟩
  · simpa using isGLB_sub_const hm₀ m₀
  intro c hc S hSU hSc
  have hcl := subset_closure_interior hU ⟨x₀, hx₀⟩
  have hcint : ∀ n, IsGLB (us n '' interior U) (c n - χn n x₀) := fun n =>
    isGLB_sub_const ((isGLB_image_iff_interior (continuous_of_convexOn_univ (hχc n)) hcl _).1 (hc n)) _
  have hd : Tendsto (fun n => c n - χn n x₀) atTop (𝓝 m₀) :=
    tendsto_of_isGLB isOpen_interior hU.interior (hUk.isBounded.subset interior_subset) hx₀ hconv
      hφlim hcint hm₀
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_interior).1 hφlim S hSU hSc
  rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
  intro ε hε
  have hd' := Metric.tendsto_atTop.1 hd (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := hd'
  filter_upwards [hunif (ε / 2) (half_pos hε), eventually_ge_atTop N] with n hn hnN u hu
  have h1 := hn u hu
  have h2 := hN n hnN
  rw [Real.dist_eq] at h1 h2 ⊢
  simp only [hus] at h1
  have e : φ u - m₀ - (χn n u - c n) = (φ u - (χn n u - χn n x₀)) + ((c n - χn n x₀) - m₀) := by ring
  rw [e]
  calc |φ u - (χn n u - χn n x₀) + (c n - χn n x₀ - m₀)|
      ≤ |φ u - (χn n u - χn n x₀)| + |c n - χn n x₀ - m₀| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := add_halves ε

end OTFD_WaveL4_RouteInexact

section OTFD_WaveL4_RouteClaims

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.WaveL1 StatFormal.OTFD.WaveL3
open StatFormal.OTFD.WaveL4
variable {K : ℕ}

theorem cond_potentials_inexact : StatFormal.OTFD.WaveL8.Claims.cond_potentials_inexact := by
  intro K μ P U Q α ν π χn g ζ d hR hQ hmap hcm hF
  obtain ⟨φ, hφc, hQφ, hφ0, hconvg⟩ := StatFormal.OTFD.WaveL8.cond_core_inexact hR hQ hmap hcm hF
  refine ⟨⟨φ, hφc, hQφ, hφ0⟩, fun χ hχc hQχ hχ0 c hc S hSU hSc => ?_⟩
  obtain ⟨C, hC⟩ := ConvexOn.exists_eq_add_const_of_ae_gradient_eq (ρ := volume) isOpen_interior
    hχc hφc hR.1 hR.2.2.2.2 (by filter_upwards [hQχ, hQφ] with z h1 h2 _; rw [← h1, ← h2])
  have hC1 : C ≤ 0 := hχ0.2 (by
    rintro _ ⟨z, hz, rfl⟩
    have := hφ0.1 ⟨z, hz, rfl⟩
    rw [hC z hz]
    linarith)
  have hC2 : -C ≤ 0 := hφ0.2 (by
    rintro _ ⟨z, hz, rfl⟩
    have := hχ0.1 ⟨z, hz, rfl⟩
    rw [hC z hz] at this
    linarith)
  have heq : EqOn φ χ S := fun u hu => by rw [hC u (hSU hu)]; linarith
  have h1 := (hconvg c hc S hSU hSc).congr_right heq
  refine ⟨h1, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff] at h1 ⊢
  intro ε hε
  filter_upwards [h1 (ε / 2) (half_pos hε), hF.2.2.2.2.2.2.2.2.2.2.2 (ε / 4) (by positivity)]
    with n hn hg u hu
  have a1 := hn u hu
  have a2 := hg u (interior_subset (hSU hu))
  rw [Real.dist_eq] at a1 ⊢
  have e : χ u - (g n u - c n) = (χ u - (χn n u - c n)) - (g n u - χn n u) := by ring
  rw [e]
  calc |χ u - (χn n u - c n) - (g n u - χn n u)|
      ≤ |χ u - (χn n u - c n)| + |g n u - χn n u| := abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le a1 (by linarith)
    _ = ε := add_halves ε

theorem premise_of_inexactFit {μ P : ProbabilityMeasure (Euc K)} {U : Set (Euc K)}
    {Q : Euc K → Euc K} {α ν : ℕ → ProbabilityMeasure (Euc K)}
    {π : ℕ → ProbabilityMeasure (Euc K × Euc K)} {χn g : ℕ → Euc K → ℝ} {ζ : ℕ → ℝ}
    {d : ℕ → Euc K × Euc K → ℝ} {χ : Euc K → ℝ} {m : ℝ} (hR : RefLaw (μ : Measure (Euc K)) U)
    (hQ : Measurable Q)
    (hmap : (μ : Measure (Euc K)).map Q = P)
    (hχ : ConvexOn ℝ (interior U) χ) (hQχ : Q =ᵐ[(μ : Measure (Euc K))] gradient χ)
    (hm : IsGLB (χ '' interior U) m) (hF : InexactFit μ P U α ν π χn g ζ d) :
    ∀ S ⊆ interior U, IsCompact S →
      TendstoUniformlyOn (fun n u => g n u - sInf (χn n '' U)) (fun u => χ u - m) atTop S := by
  intro S hSU hSc
  have hcm := isCMMapAE_of_gradient hR.1 hR.2.1 hR.2.2.2.1 hχ hQχ
  have hUne : U.Nonempty := (interior_nonempty_of_refLaw hR).mono interior_subset
  exact ((StatFormal.OTFD.WaveL8.cond_potentials_inexact K μ P U Q α ν π χn g ζ d hR hQ hmap hcm hF).2
    (fun u => χ u - m) (convexOn_sub_const hχ m) (by rwa [gradient_sub_const'])
    (by simpa using isGLB_sub_const hm m) (fun n => sInf (χn n '' U))
    (fun n => exists_isGLB_of_convexOn_univ hR.2.2.1 hUne (hF.2.2.2.2.2.1 n)) S hSU hSc).2

theorem cond_maps_ae_inexact : StatFormal.OTFD.WaveL8.Claims.cond_maps_ae_inexact := by
  intro K μ P U χ Q Qn α ν π χn g ζ d hR hQ hmap hχ hQχ hF hg hQn
  obtain ⟨m, hm⟩ := exists_isGLB_pop hR hχ
  have h := StatFormal.OTFD.Wave22b.cond_maps_ae K μ U (fun u => χ u - m)
    (fun n u => g n u - sInf (χn n '' U)) Q Qn hR.1 hR.2.1 hR.2.2.2.1 (convexOn_sub_const hχ m)
    (fun n => convexOn_sub_const (hg n) _) (StatFormal.OTFD.WaveL8.premise_of_inexactFit hR hQ hmap hχ hQχ hm hF)
    (by rwa [gradient_sub_const']) (fun n u hu => mem_subdiff_extTop_sub _ (hQn n u hu))
  filter_upwards [h] with u ⟨h1, h2, h3⟩
  exact ⟨h1, differentiableAt_of_sub_const h2, h3⟩

theorem cond_band_one_sided_inexact : StatFormal.OTFD.WaveL8.Claims.cond_band_one_sided_inexact := by
  intro K 𝒯 μ P U A χ Q Qn α ν π χn g ζ d e R EK hR hQ hmap hχ hQχ hF hg hQn hA hRb he
  obtain ⟨m, hm⟩ := exists_isGLB_pop hR hχ
  exact StatFormal.OTFD.Wave22b.cond_band_one_sided_potentials K 𝒯 μ U A (fun u => χ u - m)
    (fun n u => g n u - sInf (χn n '' U)) Q Qn e R EK hR.1 hR.2.1 hR.2.2.2.1
    (convexOn_sub_const hχ m) (fun n => convexOn_sub_const (hg n) _)
    (StatFormal.OTFD.WaveL8.premise_of_inexactFit hR hQ hmap hχ hQχ hm hF) (by rwa [gradient_sub_const'])
    (fun n u hu => mem_subdiff_extTop_sub _ (hQn n u hu)) hA hRb he

theorem cond_test_coverage_inexact : StatFormal.OTFD.WaveL8.Claims.cond_test_coverage_inexact := by
  intro K 𝒯 μ P U A χ Q Qn α ν π χn g ζ d m e Ue Le R EK p κ hR hQ hmap hχ hQχ hF hg hQn hA
    hRb he hp hκ hband
  obtain ⟨m₀, hm₀⟩ := exists_isGLB_pop hR hχ
  exact StatFormal.OTFD.Wave22b.cond_test_coverage_potentials K 𝒯 μ U A (fun u => χ u - m₀)
    (fun n u => g n u - sInf (χn n '' U)) Q Qn m e Ue Le R EK p κ hR.1 hR.2.1 hR.2.2.2.1
    (convexOn_sub_const hχ m₀) (fun n => convexOn_sub_const (hg n) _)
    (StatFormal.OTFD.WaveL8.premise_of_inexactFit hR hQ hmap hχ hQχ hm₀ hF) (by rwa [gradient_sub_const'])
    (fun n u hu => mem_subdiff_extTop_sub _ (hQn n u hu)) hQ hA hRb he hp hκ hband

theorem cond_transfer_consistency_inexact : StatFormal.OTFD.WaveL8.Claims.cond_transfer_consistency_inexact := by
  intro K Ω _ P μ P' U DF Z F Fh χ' Q' Qh α ν π χn g ζ d hR hZ hF hmapZ hZD hrank hχ' hQ' hQm
    hmap hfit hQh
  obtain ⟨m, hm⟩ := exists_isGLB_pop hR hχ'
  have hpot : ∀ᵐ ω ∂P, (∀ n, ConvexOn ℝ (interior U) (fun u => g n ω u - sInf (χn n ω '' U))) ∧
      ∀ S ⊆ interior U, IsCompact S → TendstoUniformlyOn
        (fun n => fun u => g n ω u - sInf (χn n ω '' U)) (fun u => χ' u - m) atTop S := by
    filter_upwards [hfit] with ω ⟨hFω, hgω⟩
    exact ⟨fun n => convexOn_sub_const (hgω n) _,
      StatFormal.OTFD.WaveL8.premise_of_inexactFit hR hQm hmap hχ' hQ' hm hFω⟩
  have h := StatFormal.OTFD.Wave22b.cond_transfer_consistency K Ω P μ U DF Z F Fh
    (fun u => χ' u - m) (fun n ω u => g n ω u - sInf (χn n ω '' U)) Q' Qh hR.1 hR.2.1 hR.2.2.2.1
    hZ hF hmapZ hZD hrank (convexOn_sub_const hχ' m) (by rwa [gradient_sub_const']) hpot
    (fun n ω u hu => mem_subdiff_extTop_sub _ (hQh n ω u hu))
  filter_upwards [h] with ω ⟨h1, h2, h3, h4⟩
  rw [gradient_sub_const'] at h3
  exact ⟨h1, differentiableAt_of_sub_const h2, h3, h4⟩

theorem cond_transfer_consistency_prob_inexact : StatFormal.OTFD.WaveL8.Claims.cond_transfer_consistency_prob_inexact := by
  intro K Ω _ P _ μ P' U DF Z F Fh χ' Q' Qh α ν π χn g ζ d hR hZ hF hmapZ hZD hrank hχ' hQ' hQm
    hmap hfit hQh hmeas
  have h := StatFormal.OTFD.WaveL8.cond_transfer_consistency_inexact K Ω P μ P' U DF Z F Fh χ' Q' Qh α ν π χn g ζ d hR hZ
    hF hmapZ hZD hrank hχ' hQ' hQm hmap hfit hQh
  exact tendstoInMeasure_of_tendsto_ae hmeas (h.mono fun ω hω => hω.2.2.2)

end OTFD_WaveL4_RouteClaims

section OTFD_WaveL4_RouteWeighted

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.WaveL1 StatFormal.OTFD.WaveL3
open StatFormal.OTFD.WaveL4
variable {K : ℕ}

theorem cond_potentials_weighted : StatFormal.OTFD.WaveL8.Claims.cond_potentials_weighted := by
  intro K μ P U Q α ν χn g ζ hR hQ hmap hcm hW
  obtain ⟨π, d, hF⟩ := inexactFit_of_weightedFit K μ P U α ν χn g ζ hR.2.2.1 hW
  exact StatFormal.OTFD.WaveL8.cond_potentials_inexact K μ P U Q α ν π χn g _ d hR hQ hmap hcm hF

theorem cond_maps_ae_weighted : StatFormal.OTFD.WaveL8.Claims.cond_maps_ae_weighted := by
  intro K μ P U χ Q Qn α ν χn g ζ hR hQ hmap hχ hQχ hW hg hQn
  obtain ⟨π, d, hF⟩ := inexactFit_of_weightedFit K μ P U α ν χn g ζ hR.2.2.1 hW
  exact StatFormal.OTFD.WaveL8.cond_maps_ae_inexact K μ P U χ Q Qn α ν π χn g _ d hR hQ hmap hχ hQχ hF hg hQn

theorem cond_band_one_sided_weighted : StatFormal.OTFD.WaveL8.Claims.cond_band_one_sided_weighted := by
  intro K 𝒯 μ P U A χ Q Qn α ν χn g ζ e R EK hR hQ hmap hχ hQχ hW hg hQn hA hRb he
  obtain ⟨π, d, hF⟩ := inexactFit_of_weightedFit K μ P U α ν χn g ζ hR.2.2.1 hW
  exact StatFormal.OTFD.WaveL8.cond_band_one_sided_inexact K 𝒯 μ P U A χ Q Qn α ν π χn g _ d e R EK hR hQ hmap hχ hQχ
    hF hg hQn hA hRb he

theorem cond_test_coverage_weighted : StatFormal.OTFD.WaveL8.Claims.cond_test_coverage_weighted := by
  intro K 𝒯 μ P U A χ Q Qn α ν χn g ζ m e Ue Le R EK p κ hR hQ hmap hχ hQχ hW hg hQn hA hRb he
    hp hκ hband
  obtain ⟨π, d, hF⟩ := inexactFit_of_weightedFit K μ P U α ν χn g ζ hR.2.2.1 hW
  exact StatFormal.OTFD.WaveL8.cond_test_coverage_inexact K 𝒯 μ P U A χ Q Qn α ν π χn g _ d m e Ue Le R EK p κ hR hQ
    hmap hχ hQχ hF hg hQn hA hRb he hp hκ hband

theorem cond_transfer_consistency_weighted : StatFormal.OTFD.WaveL8.Claims.cond_transfer_consistency_weighted := by
  intro K Ω _ P μ P' U DF Z F Fh χ' Q' Qh α ν χn g ζ hR hZ hF hmapZ hZD hrank hχ' hQ' hQm
    hmap hfit hQh
  obtain ⟨π, d, hπ⟩ := exists_plans_of_weightedFit (μ := μ) (P' := P') hR.2.2.1 α ν χn g ζ
  exact StatFormal.OTFD.WaveL8.cond_transfer_consistency_inexact K Ω P μ P' U DF Z F Fh χ' Q' Qh α ν π χn g
    (fun n ω => ζ n ω / 2) d hR hZ hF hmapZ hZD hrank hχ' hQ' hQm hmap
    (by filter_upwards [hfit] with ω ⟨hW, hg⟩ using ⟨hπ ω hW, hg⟩) hQh

theorem cond_transfer_consistency_prob_weighted :
    StatFormal.OTFD.WaveL8.Claims.cond_transfer_consistency_prob_weighted := by
  intro K Ω _ P _ μ P' U DF Z F Fh χ' Q' Qh α ν χn g ζ hR hZ hF hmapZ hZD hrank hχ' hQ' hQm
    hmap hfit hQh hmeas
  obtain ⟨π, d, hπ⟩ := exists_plans_of_weightedFit (μ := μ) (P' := P') hR.2.2.1 α ν χn g ζ
  exact StatFormal.OTFD.WaveL8.cond_transfer_consistency_prob_inexact K Ω P μ P' U DF Z F Fh χ' Q' Qh α ν π χn g
    (fun n ω => ζ n ω / 2) d hR hZ hF hmapZ hZD hrank hχ' hQ' hQm hmap
    (by filter_upwards [hfit] with ω ⟨hW, hg⟩ using ⟨hπ ω hW, hg⟩) hQh hmeas

end OTFD_WaveL4_RouteWeighted

section Wave24e_RouteCondRankUncond

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.Wave23c (lagPot lagPiece)
open StatFormal.Wave24e
variable {K : ℕ}

theorem cond_rank_consistency_uncond : StatFormal.OTFD.WaveL8.Claims.cond_rank_consistency_uncond := by
  intro K n M ε R z f u g μ P U Q α ν ζ ρ hRef hQ hQP hCM hW hα hgrid hε hεlog hcol hz hρ
  have hpot := StatFormal.OTFD.WaveL8.cond_potentials_weighted K μ P U Q α ν
    (fun k => lagPot (z k) (f k)) (fun k => lagPot (z k) (f k)) ζ hRef hQ hQP hCM hW
  refine ⟨hpot.1, fun χ hχ hQχ hglb => ?_⟩
  have hne : (interior U).Nonempty := StatFormal.OTFD.WaveL3.interior_nonempty_of_refLaw hRef
  obtain ⟨-, hUc, hUk, -, hsupp⟩ := hRef
  have hcl := StatFormal.OTFD.WaveL3.subset_closure_interior hUc hne
  have hUne : U.Nonempty := hne.mono interior_subset
  have hR : 0 ≤ R := le_trans (norm_nonneg _) (hz 0 0)
  -- the Laguerre potentials are `R`-Lipschitz
  have hlip : ∀ k w w', lagPot (z k) (f k) w ≤ lagPot (z k) (f k) w' + R * ‖w - w'‖ :=
    fun k w w' => lagPot_le_add (f k) (hz k) w w'
  have hcont : ∀ k, Continuous (lagPot (z k) (f k)) := fun k =>
    StatFormal.OTFD.WaveL4.continuous_of_le_add_mul (hlip k)
  set c : ℕ → ℝ := fun k => sInf (lagPot (z k) (f k) '' U) with hcdef
  have hc : ∀ k, IsGLB (lagPot (z k) (f k) '' U) (c k) := fun k =>
    isGLB_csInf (hUne.image _) (hUk.bddBelow_image (hcont k).continuousOn)
  have hconvS : ∀ S ⊆ interior U, IsCompact S →
      TendstoUniformlyOn (fun k w => lagPot (z k) (f k) w - c k) χ atTop S := fun S hS hSc =>
    (hpot.2 χ hχ hQχ hglb c hc S hS hSc).1
  obtain ⟨B₀, hB₀⟩ := hUk.isBounded.subset_closedBall 0
  set B := max B₀ 0
  have hB : ∀ w ∈ U, ‖w‖ ≤ B := fun w hw => by
    have := hB₀ hw
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  set X : EuclideanSpace ℝ (Fin K) → ℝ := fun y' => sSup ((fun w => ⟪w, y'⟫ - χ w) '' interior U) with hXdef
  have hχ0 : ∀ w ∈ interior U, 0 ≤ χ w := fun w hw => hglb.1 ⟨w, hw, rfl⟩
  have hXbdd : ∀ y, BddAbove ((fun w => ⟪w, y⟫ - χ w) '' interior U) := fun y => by
    refine ⟨B * ‖y‖, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h1 := real_inner_le_norm w y
    have h2 := hB w (interior_subset hw)
    have h3 := hχ0 w hw
    nlinarith [norm_nonneg y]
  have hle_X : ∀ y, ∀ w ∈ interior U, ⟪w, y⟫ - χ w ≤ X y := fun y w hw =>
    le_csSup (hXbdd y) ⟨w, hw, rfl⟩
  have hcbdd : ∀ k y, BddAbove ((fun w => ⟪w, y⟫ - lagPot (z k) (f k) w) '' U) := fun k y => by
    refine ⟨B * ‖y‖ - c k, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h1 := real_inner_le_norm w y
    have h2 := hB w hw
    have h3 := (hc k).1 ⟨w, hw, rfl⟩
    nlinarith [norm_nonneg y]
  -- Step 4: `X_n + c_n → X` pointwise
  have hX : ∀ y, Tendsto (fun k => contConj (z k) (f k) U y - -c k) atTop (𝓝 (X y)) := by
    intro y
    rw [Metric.tendsto_nhds]
    intro η hη
    -- lower bound
    obtain ⟨_, ⟨w₀, hw₀, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (hne.image _)
      (show X y - η / 2 < X y by linarith)
    have hpt : Tendsto (fun k => lagPot (z k) (f k) w₀ - c k) atTop (𝓝 (χ w₀)) :=
      (hconvS {w₀} (singleton_subset_iff.2 hw₀) isCompact_singleton).tendsto_at rfl
    have hlow : ∀ᶠ k in atTop, X y - η < contConj (z k) (f k) U y + c k := by
      filter_upwards [(Metric.tendsto_nhds.1 hpt) (η / 2) (half_pos hη)] with k hk
      rw [Real.dist_eq] at hk
      have : ⟪w₀, y⟫ - lagPot (z k) (f k) w₀ ≤ contConj (z k) (f k) U y :=
        le_csSup (hcbdd k y) ⟨w₀, interior_subset hw₀, rfl⟩
      have := (abs_lt.1 hk).2
      simp only at hlt
      linarith
    -- upper bound: shrink `U` towards `c₀ ∈ int U`
    obtain ⟨c₀, hc₀⟩ := hne
    set L := ‖y‖ + R
    have hL : 0 ≤ L := add_nonneg (norm_nonneg _) hR
    set s : ℝ := min (1 / 2) (η / (4 * (L * (2 * B) + 1)))
    have hden : 0 < 4 * (L * (2 * B) + 1) := by positivity
    have hs0 : 0 < s := lt_min (by norm_num) (div_pos hη hden)
    have hs1 : s ≤ 1 / 2 := min_le_left _ _
    have hsη : L * (2 * B) * s ≤ η / 4 := by
      have h1 : s ≤ η / (4 * (L * (2 * B) + 1)) := min_le_right _ _
      have h2 : L * (2 * B) * s ≤ L * (2 * B) * (η / (4 * (L * (2 * B) + 1))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : L * (2 * B) * (η / (4 * (L * (2 * B) + 1))) ≤ η / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ hden (by norm_num)]
        nlinarith [hη.le, mul_nonneg hL (mul_nonneg (zero_le_two) hB0)]
      linarith
    set sh : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K) := fun w => s • c₀ + (1 - s) • w
    have hshc : Continuous sh := by fun_prop
    have hSsub : sh '' U ⊆ interior U := by
      rintro _ ⟨w, hw, rfl⟩
      exact hUc.combo_interior_self_mem_interior hc₀ hw hs0 (by linarith) (by ring)
    have hSc : IsCompact (sh '' U) := hUk.image hshc
    have hunif := (Metric.tendstoUniformlyOn_iff.1 (hconvS _ hSsub hSc)) (η / 4) (by linarith)
    have hup : ∀ᶠ k in atTop, contConj (z k) (f k) U y + c k ≤ X y + 3 * η / 4 := by
      filter_upwards [hunif] with k hk
      have : contConj (z k) (f k) U y ≤ X y + 3 * η / 4 - c k := by
        refine csSup_le (hUne.image _) ?_
        rintro _ ⟨w, hw, rfl⟩
        have hw' : sh w ∈ sh '' U := ⟨w, hw, rfl⟩
        have h1 := hk (sh w) hw'
        rw [Real.dist_eq, abs_lt] at h1
        have h2 := hle_X y (sh w) (hSsub hw')
        have hdiff : w - sh w = s • (w - c₀) := by
          simp only [sh, smul_sub, sub_smul, one_smul]; abel
        have hnd : ‖w - sh w‖ ≤ s * (2 * B) := by
          rw [hdiff, norm_smul, Real.norm_of_nonneg hs0.le]
          refine mul_le_mul_of_nonneg_left ?_ hs0.le
          have := norm_sub_le w c₀
          have := hB w hw
          have := hB c₀ (interior_subset hc₀)
          linarith
        have h3 := hlip k (sh w) w
        have h4 : ⟪w, y⟫ ≤ ⟪sh w, y⟫ + ‖y‖ * ‖w - sh w‖ := by
          have := real_inner_le_norm (w - sh w) y
          rw [inner_sub_left] at this
          rw [mul_comm]; linarith
        rw [norm_sub_rev] at h3
        have h5 : L * ‖w - sh w‖ ≤ L * (s * (2 * B)) := mul_le_mul_of_nonneg_left hnd hL
        have h6 : L * ‖w - sh w‖ = ‖y‖ * ‖w - sh w‖ + R * ‖w - sh w‖ := by simp only [L]; ring
        nlinarith
      linarith
    filter_upwards [hlow, hup] with k h1 h2
    rw [Real.dist_eq, sub_neg_eq_add, abs_lt]
    constructor <;> linarith
  -- Step 3: grid density with `δ_k = sup_{w ∈ U} min_j ‖w − u_j‖`
  set D : ℕ → EuclideanSpace ℝ (Fin K) → ℝ := fun k w =>
    Finset.univ.inf' Finset.univ_nonempty fun j => ‖w - u k j‖ with hDdef
  set δ : ℕ → ℝ := fun k => sSup (D k '' U) with hδdef
  have hDle : ∀ k w j, D k w ≤ ‖w - u k j‖ := fun k w j =>
    Finset.inf'_le (fun j => ‖w - u k j‖) (Finset.mem_univ j)
  have hDbdd : ∀ k, BddAbove (D k '' U) := fun k => by
    refine ⟨2 * B, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hDle k w 0
    have h2 := norm_sub_le w (u k 0)
    have h3 := hB w hw
    have h4 := hB (u k 0) (hgrid k 0)
    linarith
  have hdense : ∀ k, ∀ w ∈ U, ∃ j, ‖w - u k j‖ ≤ δ k := by
    intro k w hw
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty fun j => ‖w - u k j‖
    exact ⟨j, hj ▸ le_csSup (hDbdd k) ⟨w, hw, rfl⟩⟩
  have hδ : Tendsto δ atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨w₁, hw₁⟩ := hUne
    have hev := eventually_grid_dense hW.1 hα hUk hcl hsupp (half_pos hη)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun k hk => ?_⟩
    have hδ0 : 0 ≤ δ k := by
      have : D k w₁ ≤ δ k := le_csSup (hDbdd k) ⟨w₁, hw₁, rfl⟩
      have : 0 ≤ D k w₁ := Finset.le_inf' _ _ fun j _ => norm_nonneg _
      linarith
    have hδη : δ k ≤ η / 2 := by
      refine csSup_le ⟨_, ⟨w₁, hw₁, rfl⟩⟩ ?_
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨j, hj⟩ := hN k hk w hw
      exact (hDle k w j).trans hj.le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hδ0]
    linarith
  exact cond_rank_consistency K n M ε δ R z f u g U X (fun k => -c k) ρ hε hεlog hδ hcol hz hgrid hdense hX hρ

end Wave24e_RouteCondRankUncond

end StatFormal.OTFD.WaveL8
