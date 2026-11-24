import StatFormal.Archive.OTFD.WaveL4.Statements
import StatFormal.Archive.OTFD.WaveL4.RouteApprox
import StatFormal.Archive.OTFD.WaveL3.RouteCondClaims
import StatFormal.Archive.OTFD.WaveL1.RouteCM

/-!
# Route (wave L4): C `prop:conditional-potentials` for inexact hard fits (`ζ_n → 0`)

Untrusted route file. The chain of wave L3 (`RouteCond.cond_core`) with the exact subgradient
concentration of the fitted plans replaced by its approximate form:
1. `approxSubgrad_of_inexactFit` (Markov): the `π_n`-mass of the pairs `(u, z)` that are not
   `δ`-subgradient pairs of `χ_n` relative to `U` is at most `ζ_n / δ → 0`. So, for all `δ, c > 0`,
   eventually every open set of `π_n`-mass `> c` contains a `δ`-subgradient pair (`ApproxSubgrad`).
2. `cycMon_support_of_tendsto_approx`: weak limits of such plans have cyclically monotone supports
   (a violation `Σ⟨y_i, x_{i+1} − x_i⟩ = s > 0` at support points persists on neighbourhoods,
   which eventually contain `δ`-subgradient pairs with `δ = s/(2(m+1))`, whose cycle sum is
   `≤ mδ < s/2`). With uniqueness of cyclically monotone couplings of `(μ_K, P)` (wave L3) the
   whole sequence converges: `π_n ⇀ (Id × Q)#μ_K` (`tendsto_of_approx`).
3. The approximate potential library (`RouteApprox`) gives the limit potential and the locally
   uniform convergence; the normalisation and the transfer to `g_n` are as in wave L3.
-/

open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

set_option linter.style.longLine false

namespace StatFormal.OTFD.WaveL4

open StatFormal.OTFD.WaveL1 StatFormal.OTFD.WaveL3

variable {K : ℕ}

/-- **Approximate relative subgradient concentration** along a filter: for all `δ > 0`, `c > 0`,
eventually every open set of `π_i`-mass `> c` contains `(x, y)` with `x ∈ W` and `y` a
`δ`-subgradient of `f_i` at `x` relative to `W`. -/
def ApproxSubgrad {ι : Type*} (l : Filter ι) (W : Set (Euc K)) (f : ι → Euc K → ℝ)
    (πs : ι → ProbabilityMeasure (Euc K × Euc K)) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ c : ℝ≥0∞, 0 < c → ∀ᶠ i in l, ∀ V : Set (Euc K × Euc K), IsOpen V →
    c < (πs i).toMeasure V → ∃ z ∈ V, z.1 ∈ W ∧ ∀ x ∈ W, f i z.1 + ⟪z.2, x - z.1⟫ ≤ f i x + δ

theorem ApproxSubgrad.mono {ι : Type*} {l l' : Filter ι} {W : Set (Euc K)} {f : ι → Euc K → ℝ}
    {πs : ι → ProbabilityMeasure (Euc K × Euc K)} (h : ApproxSubgrad l W f πs) (hl : l' ≤ l) :
    ApproxSubgrad l' W f πs :=
  fun δ hδ c hc => hl (h δ hδ c hc)

/-- **Cyclical monotonicity of supports of weak limits of approximately subgradient-concentrated
plans.** -/
theorem cycMon_support_of_tendsto_approx {ι : Type*} {l : Filter ι} [l.NeBot] {W : Set (Euc K)}
    {f : ι → Euc K → ℝ} {πs : ι → ProbabilityMeasure (Euc K × Euc K)}
    {π : ProbabilityMeasure (Euc K × Euc K)} (hπ : Tendsto πs l (𝓝 π))
    (hap : ApproxSubgrad l W f πs) : CycMon (π : Measure (Euc K × Euc K)).support := by
  intro m z hmem
  by_contra hlt
  rw [not_le] at hlt
  set F : (Fin m → Euc K × Euc K) → ℝ := fun w ↦ ∑ i, ⟪(w i).2, (w (finRotate m i)).1 - (w i).1⟫
    with hFdef
  have hF : Continuous F := continuous_finsetSum _ fun i _ ↦
    ((continuous_apply i).snd).inner
      (((continuous_apply (finRotate m i)).fst).sub ((continuous_apply i).fst))
  set s : ℝ := F z with hs
  have hopen : IsOpen {w | s / 2 < F w} := isOpen_lt continuous_const hF
  obtain ⟨V, hV, hVsub⟩ := isOpen_pi_iff'.1 hopen z (by simp only [mem_setOf_eq]; linarith)
  have hpos : ∀ i, 0 < (π : Measure (Euc K × Euc K)) (V i) := fun i ↦
    (Measure.mem_support_iff_forall _).1 (hmem i) _ ((hV i).1.mem_nhds (hV i).2)
  set δ : ℝ := s / (2 * ((m : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hev : ∀ᶠ j in l, ∀ i, ∃ w ∈ V i, w.1 ∈ W ∧
      ∀ x ∈ W, f j w.1 + ⟪w.2, x - w.1⟫ ≤ f j x + δ :=
    eventually_all.2 fun i ↦ eventually_exists_of_approx (hap δ hδ) hπ (hV i).1 (hpos i)
  obtain ⟨j, hj⟩ := hev.exists
  choose w hwV hwW hwineq using hj
  have hw : s / 2 < F w := hVsub fun i _ ↦ hwV i
  have hle : F w ≤ m * δ := by
    have h : ∀ i, ⟪(w i).2, (w (finRotate m i)).1 - (w i).1⟫ ≤
        f j (w (finRotate m i)).1 - f j (w i).1 + δ := fun i => by
      have := hwineq i _ (hwW (finRotate m i)); linarith
    calc F w ≤ ∑ i, (f j (w (finRotate m i)).1 - f j (w i).1 + δ) :=
          Finset.sum_le_sum fun i _ => h i
      _ = m * δ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Equiv.sum_comp (finRotate m) (fun i => f j (w i).1), sub_self, zero_add]
          simp
  have hmδ : (m : ℝ) * δ < s / 2 := by
    rw [hδdef]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- **Plan convergence for approximately subgradient-concentrated plans** (wave L1
`tendsto_of_cmConc` with cyclical monotonicity of the limit from `ApproxSubgrad`). -/
theorem tendsto_of_approx {P μ : ProbabilityMeasure (Euc K)} {F : Euc K → Euc K}
    {α ν : ℕ → ProbabilityMeasure (Euc K)} {π : ℕ → ProbabilityMeasure (Euc K × Euc K)}
    {G : ProbabilityMeasure (Euc K × Euc K)} {W : Set (Euc K)} {f : ℕ → Euc K → ℝ}
    (huniq : BrenierUniq (P : Measure (Euc K)) μ F)
    (hα : Tendsto α atTop (𝓝 P)) (hν : Tendsto ν atTop (𝓝 μ))
    (hfst : ∀ n, (π n : Measure (Euc K × Euc K)).fst = α n)
    (hsnd : ∀ n, (π n : Measure (Euc K × Euc K)).snd = ν n)
    (hap : ApproxSubgrad atTop W f π)
    (hG : (G : Measure (Euc K × Euc K)) = Graph (P : Measure (Euc K)) F) :
    Tendsto π atTop (𝓝 G) := by
  by_contra hnot
  obtain ⟨U, hU, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hnot
  set lb : Filter ℕ := atTop ⊓ 𝓟 {n | π n ∉ U}
  have hne : lb.NeBot := frequently_mem_iff_neBot.mp hfreq
  have hlb : lb ≤ atTop := inf_le_left
  have hcoup : ∀ n, IsCoupling (π n : Measure (Euc K × Euc K)) (α n) (ν n) := fun n ↦
    ⟨hfst n, hsnd n⟩
  obtain ⟨l', σ, hne', hle, hconv, hσ⟩ := exists_isCoupling_tendsto_of_isTightMeasureSet
    (l := lb)
    ⟨univ, univ_mem, (isTightMeasureSet_range_of_tendsto hα).subset
      (by rintro - ⟨i, -, rfl⟩; exact mem_range_self i)⟩
    ⟨univ, univ_mem, (isTightMeasureSet_range_of_tendsto hν).subset
      (by rintro - ⟨i, -, rfl⟩; exact mem_range_self i)⟩
    (hα.mono_left hlb) (hν.mono_left hlb) (Eventually.of_forall hcoup)
  have := hne'
  have hσcm : CMConc (σ : Measure (Euc K × Euc K)) :=
    ⟨_, Measure.isClosed_support.measurableSet,
      cycMon_support_of_tendsto_approx hconv (hap.mono (hle.trans hlb)),
      Measure.measure_compl_support⟩
  have hσG : σ = G := by
    apply Subtype.ext
    change (σ : Measure (Euc K × Euc K)) = (G : Measure (Euc K × Euc K))
    rw [hG]
    exact huniq _ inferInstance hσ.fst_eq hσ.snd_eq hσcm
  rw [hσG] at hconv
  have hout : ∀ᶠ n in l', π n ∉ U :=
    (eventually_inf_principal.2 (Eventually.of_forall fun _ h ↦ h)).filter_mono hle
  exact ((hconv.eventually (mem_of_superset hU fun _ h ↦ h)).and hout).exists.elim
    fun _ h ↦ h.2 h.1

/-- **Markov step**: an inexact hard fit is approximately subgradient-concentrated. -/
theorem approxSubgrad_of_inexactFit {μ P : ProbabilityMeasure (Euc K)} {U : Set (Euc K)}
    {α ν : ℕ → ProbabilityMeasure (Euc K)} {π : ℕ → ProbabilityMeasure (Euc K × Euc K)}
    {χn g : ℕ → Euc K → ℝ} {ζ : ℕ → ℝ} {d : ℕ → Euc K × Euc K → ℝ}
    (hF : InexactFit μ P U α ν π χn g ζ d) (hUm : MeasurableSet U) :
    ApproxSubgrad atTop U χn π := by
  obtain ⟨-, -, hfst, -, hαU, -, -, hζ, hdm, hdint, hae, -⟩ := hF
  intro δ hδ c hc
  have hδ0 : ENNReal.ofReal δ ≠ 0 := (ENNReal.ofReal_pos.2 hδ).ne'
  have hlim : Tendsto (fun n => ENNReal.ofReal (ζ n) / ENNReal.ofReal δ) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.div_const (ENNReal.tendsto_ofReal hζ) (Or.inr hδ0)
    simpa using this
  filter_upwards [hlim.eventually (gt_mem_nhds hc)] with n hn V _ hcV
  by_contra hno
  have hsub : V ⊆ {z | ENNReal.ofReal δ ≤ ENNReal.ofReal (d n z)} ∪
      {z | ¬ (z.1 ∈ U ∧ ∀ x ∈ U, χn n z.1 + ⟪z.2, x - z.1⟫ ≤ χn n x + d n z)} := by
    intro z hz
    by_contra hz'
    simp only [mem_union, mem_ofPred_eq, not_or, not_le, not_not] at hz'
    obtain ⟨h1, h2U, h2⟩ := hz'
    have hdz : d n z < δ := ((ENNReal.ofReal_lt_ofReal_iff hδ).1 h1)
    exact hno ⟨z, hz, h2U, fun x hx => by linarith [h2 x hx]⟩
  have hnull : (π n : Measure (Euc K × Euc K))
      {z | ¬ (z.1 ∈ U ∧ ∀ x ∈ U, χn n z.1 + ⟪z.2, x - z.1⟫ ≤ χn n x + d n z)} = 0 := by
    have h0 : (π n : Measure (Euc K × Euc K)).fst Uᶜ = 0 := by rw [hfst n]; exact hαU n
    rw [Measure.fst_apply hUm.compl] at h0
    have h1 : ∀ᵐ z ∂(π n : Measure (Euc K × Euc K)), z.1 ∈ U :=
      (measure_eq_zero_iff_ae_notMem.1 h0).mono fun z hz => by simpa using hz
    exact measure_eq_zero_iff_ae_notMem.2 (by
      filter_upwards [h1, hae n] with z h1 h2 h3 using h3 ⟨h1, h2⟩)
  have hmark : (π n : Measure (Euc K × Euc K)) {z | ENNReal.ofReal δ ≤ ENNReal.ofReal (d n z)} ≤
      ENNReal.ofReal (ζ n) / ENNReal.ofReal δ :=
    (meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp (hdm n)).aemeasurable hδ0
      ENNReal.ofReal_ne_top).trans (ENNReal.div_le_div_right (hdint n) _)
  have hV := (measure_mono (μ := (π n : Measure (Euc K × Euc K))) hsub).trans (measure_union_le _ _)
  rw [hnull, add_zero] at hV
  exact (lt_irrefl c) ((hcV.trans_le (hV.trans hmark)).trans hn)

/-- **C `prop:conditional-potentials`, existence and convergence, for inexact hard fits.** -/
theorem cond_core_inexact {μ P : ProbabilityMeasure (Euc K)} {U : Set (Euc K)}
    {Q : Euc K → Euc K} {α ν : ℕ → ProbabilityMeasure (Euc K)}
    {π : ℕ → ProbabilityMeasure (Euc K × Euc K)} {χn g : ℕ → Euc K → ℝ} {ζ : ℕ → ℝ}
    {d : ℕ → Euc K × Euc K → ℝ} (hR : RefLaw (μ : Measure (Euc K)) U)
    (hP1 : Mom1 (P : Measure (Euc K)) ≠ ∞) (hQ : Measurable Q)
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
  have huniq := brenierUniq_of_bdd_source (lipNull_of_ac (ρ := volume) hac) hM hP1 hQ hmap hcm
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

end StatFormal.OTFD.WaveL4
