import StatFormal.Archive.OTFD.WaveL3.RouteCond

/-!
# Route (wave L3): C claims — `prop:conditional-potentials` and the unconditional wave-22b limits

Untrusted route file. `cond_potentials` from `RouteCond.cond_core` plus uniqueness of potentials up
to constants (library `ConvexOn.exists_eq_add_const_of_ae_gradient_eq`). The discharge claims feed
the certified wave-22b theorems with the `inf`-normalised fitted potentials `g_n − inf_U χ_n` and the
normalised population potential `χ − inf χ` (subgradients and gradients are unchanged by constants).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL3

open StatFormal.OTFD.WaveL1

theorem cond_potentials : Claims.cond_potentials := by
  intro K μ P U Q α ν π χn g hR hP1 hQ hmap hcm hF
  obtain ⟨φ, hφc, hQφ, hφ0, hconvg⟩ := cond_core hR hP1 hQ hmap hcm hF
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

variable {K : ℕ}

/-- A convex function on the interior of `U` (`RefLaw`) has an infimum there. -/
theorem exists_isGLB_pop {μ : ProbabilityMeasure (Euc K)} {U : Set (Euc K)} {χ : Euc K → ℝ}
    (hR : RefLaw (μ : Measure (Euc K)) U) (hχ : ConvexOn ℝ (interior U) χ) :
    ∃ m, IsGLB (χ '' interior U) m :=
  ⟨_, isGLB_csInf ((interior_nonempty_of_refLaw hR).image χ)
    (bddBelow_image_of_convexOn isOpen_interior (hR.2.2.1.isBounded.subset interior_subset) hχ)⟩

/-- **The discharged premise**: the `inf`-normalised fitted potentials converge to the normalised
population potential uniformly on compact subsets of `int U`. -/
theorem premise_of_hardFit {μ P : ProbabilityMeasure (Euc K)} {U : Set (Euc K)} {Q : Euc K → Euc K}
    {α ν : ℕ → ProbabilityMeasure (Euc K)} {π : ℕ → ProbabilityMeasure (Euc K × Euc K)}
    {χn g : ℕ → Euc K → ℝ} {χ : Euc K → ℝ} {m : ℝ} (hR : RefLaw (μ : Measure (Euc K)) U)
    (hP1 : Mom1 (P : Measure (Euc K)) ≠ ∞) (hQ : Measurable Q) (hmap : (μ : Measure (Euc K)).map Q = P)
    (hχ : ConvexOn ℝ (interior U) χ) (hQχ : Q =ᵐ[(μ : Measure (Euc K))] gradient χ)
    (hm : IsGLB (χ '' interior U) m) (hF : HardFit μ P U α ν π χn g) :
    ∀ S ⊆ interior U, IsCompact S →
      TendstoUniformlyOn (fun n u => g n u - sInf (χn n '' U)) (fun u => χ u - m) atTop S := by
  intro S hSU hSc
  have hcm := isCMMapAE_of_gradient hR.1 hR.2.1 hR.2.2.2.1 hχ hQχ
  have hUne : U.Nonempty := (interior_nonempty_of_refLaw hR).mono interior_subset
  exact ((cond_potentials K μ P U Q α ν π χn g hR hP1 hQ hmap hcm hF).2 (fun u => χ u - m)
    (convexOn_sub_const hχ m) (by rwa [gradient_sub_const'])
    (by simpa using isGLB_sub_const hm m) (fun n => sInf (χn n '' U))
    (fun n => exists_isGLB_of_convexOn_univ hR.2.2.1 hUne (hF.2.2.2.2.1 n)) S hSU hSc).2

theorem differentiableAt_of_sub_const {χ : Euc K → ℝ} {m : ℝ} {u : Euc K}
    (h : DifferentiableAt ℝ (fun v => χ v - m) u) : DifferentiableAt ℝ χ u := by
  simpa using h.add_const m

theorem cond_maps_ae_plans : Claims.cond_maps_ae_plans := by
  intro K μ P U χ Q Qn α ν π χn g hR hP1 hQ hmap hχ hQχ hF hg hQn
  obtain ⟨m, hm⟩ := exists_isGLB_pop hR hχ
  have h := StatFormal.OTFD.Wave22b.cond_maps_ae K μ U (fun u => χ u - m)
    (fun n u => g n u - sInf (χn n '' U)) Q Qn hR.1 hR.2.1 hR.2.2.2.1 (convexOn_sub_const hχ m)
    (fun n => convexOn_sub_const (hg n) _) (premise_of_hardFit hR hP1 hQ hmap hχ hQχ hm hF)
    (by rwa [gradient_sub_const']) (fun n u hu => mem_subdiff_extTop_sub _ (hQn n u hu))
  filter_upwards [h] with u ⟨h1, h2, h3⟩
  exact ⟨h1, differentiableAt_of_sub_const h2, h3⟩

theorem cond_band_one_sided_plans : Claims.cond_band_one_sided_plans := by
  intro K 𝒯 μ P U A χ Q Qn α ν π χn g e R EK hR hP1 hQ hmap hχ hQχ hF hg hQn hA hRb he
  obtain ⟨m, hm⟩ := exists_isGLB_pop hR hχ
  exact StatFormal.OTFD.Wave22b.cond_band_one_sided_potentials K 𝒯 μ U A (fun u => χ u - m)
    (fun n u => g n u - sInf (χn n '' U)) Q Qn e R EK hR.1 hR.2.1 hR.2.2.2.1
    (convexOn_sub_const hχ m) (fun n => convexOn_sub_const (hg n) _)
    (premise_of_hardFit hR hP1 hQ hmap hχ hQχ hm hF) (by rwa [gradient_sub_const'])
    (fun n u hu => mem_subdiff_extTop_sub _ (hQn n u hu)) hA hRb he

theorem cond_test_coverage_plans : Claims.cond_test_coverage_plans := by
  intro K 𝒯 μ P U A χ Q Qn α ν π χn g m e Ue Le R EK p κ hR hP1 hQ hmap hχ hQχ hF hg hQn hA hRb he hp
    hκ hband
  obtain ⟨m₀, hm₀⟩ := exists_isGLB_pop hR hχ
  exact StatFormal.OTFD.Wave22b.cond_test_coverage_potentials K 𝒯 μ U A (fun u => χ u - m₀)
    (fun n u => g n u - sInf (χn n '' U)) Q Qn m e Ue Le R EK p κ hR.1 hR.2.1 hR.2.2.2.1
    (convexOn_sub_const hχ m₀) (fun n => convexOn_sub_const (hg n) _)
    (premise_of_hardFit hR hP1 hQ hmap hχ hQχ hm₀ hF) (by rwa [gradient_sub_const'])
    (fun n u hu => mem_subdiff_extTop_sub _ (hQn n u hu)) hQ hA hRb he hp hκ hband

theorem cond_transfer_consistency_plans : Claims.cond_transfer_consistency_plans := by
  intro K Ω _ P μ P' U DF Z F Fh χ' Q' Qh α ν π χn g hR hZ hF hmapZ hZD hrank hχ' hQ' hP1 hQm hmap
    hfit hQh
  obtain ⟨m, hm⟩ := exists_isGLB_pop hR hχ'
  have hpot : ∀ᵐ ω ∂P, (∀ n, ConvexOn ℝ (interior U) (fun u => g n ω u - sInf (χn n ω '' U))) ∧
      ∀ S ⊆ interior U, IsCompact S → TendstoUniformlyOn
        (fun n => fun u => g n ω u - sInf (χn n ω '' U)) (fun u => χ' u - m) atTop S := by
    filter_upwards [hfit] with ω ⟨hFω, hgω⟩
    exact ⟨fun n => convexOn_sub_const (hgω n) _,
      premise_of_hardFit hR hP1 hQm hmap hχ' hQ' hm hFω⟩
  have h := StatFormal.OTFD.Wave22b.cond_transfer_consistency K Ω P μ U DF Z F Fh
    (fun u => χ' u - m) (fun n ω u => g n ω u - sInf (χn n ω '' U)) Q' Qh hR.1 hR.2.1 hR.2.2.2.1
    hZ hF hmapZ hZD hrank (convexOn_sub_const hχ' m) (by rwa [gradient_sub_const']) hpot
    (fun n ω u hu => mem_subdiff_extTop_sub _ (hQh n ω u hu))
  filter_upwards [h] with ω ⟨h1, h2, h3, h4⟩
  rw [gradient_sub_const'] at h3
  exact ⟨h1, differentiableAt_of_sub_const h2, h3, h4⟩

theorem cond_transfer_consistency_prob_plans : Claims.cond_transfer_consistency_prob_plans := by
  intro K Ω _ P _ μ P' U DF Z F Fh χ' Q' Qh α ν π χn g hR hZ hF hmapZ hZD hrank hχ' hQ' hP1 hQm hmap
    hfit hQh hmeas
  have h := cond_transfer_consistency_plans K Ω P μ P' U DF Z F Fh χ' Q' Qh α ν π χn g hR hZ hF hmapZ
    hZD hrank hχ' hQ' hP1 hQm hmap hfit hQh
  exact tendstoInMeasure_of_tendsto_ae hmeas (h.mono fun ω hω => hω.2.2.2)

end StatFormal.OTFD.WaveL3
