import StatFormal.Archive.OTFD.WaveL3.Statements
import StatFormal.Archive.OTFD.WaveL3.RouteUniq
import StatFormal.Archive.OTFD.WaveL3.RouteNorm
import StatFormal.Lib.Potentials.LocalBound
import StatFormal.Lib.Potentials.Uniqueness
import StatFormal.Archive.OTFD.Wave22b.RouteConvex

/-!
# Route (wave L3): C `prop:conditional-potentials` for exact hard fits

Untrusted route file. The chain:
1. `RefLaw`: `μ_K ≪ Leb` is null on Lipschitz hypersurfaces (`lipNull_of_ac`) and carried by a ball;
   the target has a first moment, so cyclically monotone couplings of `(μ_K, P)` are unique
   (`brenierUniq_of_bdd_source`).
2. The fitted plans are carried by the subdifferential graphs of `χ_n`, hence cyclically monotone;
   their marginals converge weakly, so `π_n ⇀ (Id × Q)#μ_K` (wave L1 `tendsto_of_cmConc`).
3. Library `exists_tendstoLocallyUniformlyOn_potential`: the potentials normalised at a point
   `x₀ ∈ int 𝒰_K` converge locally uniformly on `int 𝒰_K` to a convex `φ` with `∇φ = Q` a.e.
4. `RouteNorm`: the infima converge, so the `inf`-normalised potentials converge to `φ − inf φ`;
   library uniqueness up to constants identifies every normalised population potential with it.
5. Transfer to `g_n` (uniform closeness).
-/

open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL3

open StatFormal.OTFD.WaveL1

variable {K : ℕ}

/-! ### Auxiliary facts -/

theorem convexOn_sub_const {s : Set (Euc K)} {f : Euc K → ℝ} (hf : ConvexOn ℝ s f) (c : ℝ) :
    ConvexOn ℝ s (fun u => f u - c) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  have h := hf.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have e : a * (f x - c) + b * (f y - c) = a * f x + b * f y - c := by
    linear_combination (-c) * hab
  rw [e]
  linarith

theorem gradient_sub_const' (f : Euc K → ℝ) (c : ℝ) :
    gradient (fun u => f u - c) = gradient f := by
  funext x
  simp only [gradient, fderiv_sub_const]

theorem isGLB_sub_const {s : Set (Euc K)} {f : Euc K → ℝ} {m : ℝ} (h : IsGLB (f '' s) m) (c : ℝ) :
    IsGLB ((fun u => f u - c) '' s) (m - c) := by
  constructor
  · rintro _ ⟨u, hu, rfl⟩
    have := h.1 ⟨u, hu, rfl⟩
    simp only
    linarith
  · intro b hb
    have : b + c ≤ m := h.2 (by
      rintro _ ⟨u, hu, rfl⟩
      have := hb ⟨u, hu, rfl⟩
      simp only at this
      linarith)
    linarith

/-- Subgradients do not see additive constants. -/
theorem mem_subdiff_extTop_sub {C : Set (Euc K)} {g : Euc K → ℝ} {u ξ : Euc K} (c : ℝ)
    (h : ξ ∈ TauCeti.subdifferential (innerₗ (Euc K)) (StatFormal.OTFD.Wave19a.extTop C g) u) :
    ξ ∈ TauCeti.subdifferential (innerₗ (Euc K))
      (StatFormal.OTFD.Wave19a.extTop C (fun v => g v - c)) u := by
  obtain ⟨hu, hineq⟩ := StatFormal.OTFD.Wave19a.mem_subdiff_extTop h
  exact StatFormal.OTFD.Wave19a.mem_subdiff_extTop_of hu fun y hy => by
    have := hineq y hy
    linarith

/-- Subdifferential graphs relative to a set are cyclically monotone. -/
theorem cycMon_subgradGraphOn (V : Set (Euc K)) (f : Euc K → ℝ) :
    CycMon {z : Euc K × Euc K | z.1 ∈ V ∧ ∀ x ∈ V, f z.1 + ⟪z.2, x - z.1⟫ ≤ f x} := by
  intro m z hz
  have h : ∀ i, ⟪(z i).2, (z (finRotate m i)).1 - (z i).1⟫ ≤
      f (z (finRotate m i)).1 - f (z i).1 := fun i => by
    have := (hz i).2 (z (finRotate m i)).1 (hz (finRotate m i)).1
    linarith
  calc ∑ i, ⟪(z i).2, (z (finRotate m i)).1 - (z i).1⟫
      ≤ ∑ i, (f (z (finRotate m i)).1 - f (z i).1) := Finset.sum_le_sum fun i _ => h i
    _ = 0 := by
      rw [Finset.sum_sub_distrib, Equiv.sum_comp (finRotate m) (fun i => f (z i).1), sub_self]

/-- A map that is `μ`-a.e. the gradient of a convex function on `int U` is `μ`-a.e. cyclically
monotone (`μ ≪ Leb` carried by the convex `U`). -/
theorem isCMMapAE_of_gradient {μ : Measure (Euc K)} {U : Set (Euc K)} {χ : Euc K → ℝ}
    {Q : Euc K → Euc K} (hac : μ ≪ volume) (hU : Convex ℝ U) (hUc : μ Uᶜ = 0)
    (hχ : ConvexOn ℝ (interior U) χ) (hQ : Q =ᵐ[μ] gradient χ) : IsCMMapAE μ Q := by
  set S0 : Set (Euc K) := {u | u ∈ interior U ∧ DifferentiableAt ℝ χ u ∧ Q u = gradient χ u}
  have hS0 : ∀ᵐ u ∂μ, u ∈ S0 := StatFormal.OTFD.Wave22b.ae_good hac hU hUc hχ hQ
  set S : Set (Euc K) := (toMeasurable μ S0ᶜ)ᶜ
  have hSS0 : S ⊆ S0 := compl_subset_comm.1 (subset_toMeasurable μ S0ᶜ)
  refine ⟨S, (measurableSet_toMeasurable μ S0ᶜ).compl, ?_, ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hS0
  · refine cycMon_mono (cycMon_subgradGraphOn (interior U) χ) ?_
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨hxU, hd, hQx⟩ := hSS0 hx
    simp only at hy hxU ⊢
    refine ⟨hxU, fun x' hx' => ?_⟩
    rw [hy, hQx]
    exact StatFormal.Potentials.add_inner_gradient_le hχ hxU hd hx'

theorem refLaw_ball {μ : Measure (Euc K)} {U : Set (Euc K)} (hU : IsCompact U) (hUc : μ Uᶜ = 0) :
    ∃ M, μ (Metric.closedBall 0 M)ᶜ = 0 := by
  obtain ⟨M, hM⟩ := hU.isBounded.subset_closedBall 0
  exact ⟨M, measure_mono_null (compl_subset_compl.2 hM) hUc⟩

theorem interior_nonempty_of_refLaw {μ : ProbabilityMeasure (Euc K)} {U : Set (Euc K)}
    (h : RefLaw (μ : Measure (Euc K)) U) : (interior U).Nonempty := by
  obtain ⟨hac, hU, -, hUc, -⟩ := h
  have hint := StatFormal.OTFD.Wave22b.ae_mem_interior hac hU hUc
  have : (ae (μ : Measure (Euc K))).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  exact hint.exists

theorem continuous_of_convexOn_univ {f : Euc K → ℝ} (hf : ConvexOn ℝ univ f) : Continuous f := by
  have := hf.continuousOn_interior
  rw [interior_univ] at this
  exact continuousOn_univ.1 this

theorem subset_closure_interior {U : Set (Euc K)} (hU : Convex ℝ U) (hne : (interior U).Nonempty) :
    U ⊆ closure (interior U) := by
  rw [hU.closure_interior_eq_closure_of_nonempty_interior hne]
  exact subset_closure

/-- The infimum over `U` of a finite convex function exists. -/
theorem exists_isGLB_of_convexOn_univ {U : Set (Euc K)} (hUk : IsCompact U) (hne : U.Nonempty)
    {f : Euc K → ℝ} (hf : ConvexOn ℝ univ f) : IsGLB (f '' U) (sInf (f '' U)) :=
  isGLB_csInf (hne.image f) (hUk.bddBelow_image (continuous_of_convexOn_univ hf).continuousOn)

/-! ### The core chain -/

/-- **C `prop:conditional-potentials`, existence and convergence** (exact hard fits). -/
theorem cond_core {μ P : ProbabilityMeasure (Euc K)} {U : Set (Euc K)} {Q : Euc K → Euc K}
    {α ν : ℕ → ProbabilityMeasure (Euc K)} {π : ℕ → ProbabilityMeasure (Euc K × Euc K)}
    {χn g : ℕ → Euc K → ℝ} (hR : RefLaw (μ : Measure (Euc K)) U) (hP1 : Mom1 (P : Measure (Euc K)) ≠ ∞)
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
  have huniq := brenierUniq_of_bdd_source (lipNull_of_ac (ρ := volume) hac) hM hP1 hQ hmap hcm
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

end StatFormal.OTFD.WaveL3
