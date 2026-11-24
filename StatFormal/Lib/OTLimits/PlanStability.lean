import TauCeti.MeasureTheory.OptimalTransport.Stability
import TauCeti.MeasureTheory.OptimalTransport.Duality.SchachermayerTeichmann
import TauCeti.MeasureTheory.OptimalTransport.Existence.Basic

/-!
# Stability of optimal transport plans and of optimal costs (Villani, Theorem 5.20)

Library component (OT limit theory, part 1). Untrusted library code; no frozen statement is
touched.

Tau Ceti's `TauCeti/MeasureTheory/OptimalTransport/Stability.lean` reduces stability to two
*assumed* hypotheses: the liminf bound (automatic for a lower semicontinuous cost) and an upper
bound on the moving optimal values (`TauCeti.HasRecoveryPlans`, or an explicit `limsup`
inequality). This file **discharges the upper bound** for continuous finite costs, by the
cyclical-monotonicity route of Villani's proof: supports of optimal plans are `c`-cyclically
monotone (Gangbo–McCann, `TauCeti.IsOptimalCoupling.isCyclicallyMonotone_support`), this passes
to weak limits (`isCyclicallyMonotone_support_of_tendsto`, new here), and a coupling concentrated
on a `c`-cyclically monotone set is optimal for a finite-valued cost on Polish spaces
(Schachermayer–Teichmann, `TauCeti.IsCoupling.isOptimalCoupling_of_isCyclicallyMonotone`).
No integrability of the cost against the limit is needed for the plan statements.

Costs are `c : X × Y → ℝ≥0∞` as in Tau Ceti; "continuous and finite" means `Continuous c` and
`∀ z, c z ≠ ∞` (i.e. a continuous real cost `≥ 0`; a cost bounded below reduces to this by adding
a constant, which changes neither optimal plans nor convergence). Weak convergence is
convergence in Mathlib's topology on `ProbabilityMeasure`.

## Main results

* `isCyclicallyMonotone_support_of_tendsto`: if `πᵢ → π` weakly (any nontrivial filter, on a
  pseudo-metrizable hereditarily Lindelöf product) and the supports of the `πᵢ` are eventually
  `c`-cyclically monotone for a continuous `c`, then so is the support of `π`.
* `isOptimalCoupling_of_tendsto_of_continuous` (**Villani Thm 5.20, plans**): on Polish spaces,
  for a continuous finite cost, if `μᵢ → μ`, `νᵢ → ν`, `πᵢ` is optimal for `(μᵢ, νᵢ)` with
  finite optimal cost, and `πᵢ → π`, then `π` is optimal for `(μ, ν)`.
* `exists_subseq_tendsto_isOptimalCoupling`: sequences of such optimal plans have a subsequence
  converging weakly to an optimal plan of the limit problem.
* `tendsto_of_forall_isOptimalCoupling_eq` (**uniqueness ⇒ convergence**): if the limit problem
  has a unique optimal plan `π₀`, the whole sequence `πₙ` converges weakly to `π₀`.
* `tendsto_lintegral_of_le_add`: generalised dominated convergence along weakly converging
  couplings: `c ≤ a(x) + b(y)` with `a, b` continuous and `∫ a dμᵢ → ∫ a dμ < ∞`,
  `∫ b dνᵢ → ∫ b dν < ∞` gives `∫ c dπᵢ → ∫ c dπ`.
* `tendsto_transportCost_of_le_add` (**Villani Thm 5.20, values**): under the same domination
  (uniform integrability of the cost through the marginals; for `|x − y|^p` this is
  `Wₚ`-convergence), the optimal costs converge: `C(μₙ, νₙ) → C(μ, ν)`.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Theorem 5.20 and Corollary 5.23.
* W. Schachermayer, J. Teichmann, *Characterization of optimal transport plans for the
  Monge–Kantorovich problem*, Proc. AMS 137 (2009), Theorem 1.
-/

open Filter MeasureTheory Set TauCeti
open scoped ENNReal Topology

namespace StatFormal.OTLimits

/-- **Positive mass on an open set persists along weak convergence.** If probability measures
`πᵢ` on a pseudo-metrizable space converge weakly to `π` along any filter and `π U > 0` for an
open `U`, then eventually `πᵢ U > 0` (portmanteau, open-set half, via weak lower
semicontinuity of `π ↦ π U`). -/
theorem eventually_pos_measure_of_tendsto {ι Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [TopologicalSpace.PseudoMetrizableSpace Ω] {l : Filter ι}
    {πs : ι → ProbabilityMeasure Ω} {π : ProbabilityMeasure Ω} (hπ : Tendsto πs l (𝓝 π))
    {U : Set Ω} (hU : IsOpen U) (hpos : 0 < π.toMeasure U) :
    ∀ᶠ i in l, 0 < (πs i).toMeasure U := by
  let : PseudoMetricSpace Ω := TopologicalSpace.pseudoMetrizableSpacePseudoMetric Ω
  have hlsc := lowerSemicontinuous_lintegral_probabilityMeasure (Ω := Ω)
    (hU.lowerSemicontinuous_indicator (y := (1 : ℝ≥0∞)) zero_le_one)
  have h0 := hlsc π 0 (by simpa [lintegral_indicator hU.measurableSet] using hpos)
  filter_upwards [hπ.eventually h0] with i hi
  simpa [lintegral_indicator hU.measurableSet] using hi

section Support

variable {ι X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace (X × Y)]
  [TopologicalSpace.PseudoMetrizableSpace (X × Y)] [HereditarilyLindelofSpace (X × Y)]

/-- **Cyclical monotonicity of supports passes to weak limits.** Let `c : X × Y → ℝ≥0∞` be
continuous and let probability plans `πᵢ` converge weakly to `π` along a nontrivial filter, on a
pseudo-metrizable, hereditarily Lindelöf product (e.g. a product of Polish spaces). If the
topological supports of the `πᵢ` are eventually `c`-cyclically monotone, so is the support of
`π`.

Proof: a strict violation at finitely many support points of `π` persists on a product of open
neighbourhoods (continuity of `c`); each neighbourhood carries `π`-mass, hence eventually
`πᵢ`-mass, hence meets the support of `πᵢ` — contradicting its cyclical monotonicity. This is
the support step of Villani, *Optimal Transport*, proof of Theorem 5.20. -/
theorem isCyclicallyMonotone_support_of_tendsto {l : Filter ι} [l.NeBot] {c : X × Y → ℝ≥0∞}
    (hc : Continuous c) {πs : ι → ProbabilityMeasure (X × Y)} {π : ProbabilityMeasure (X × Y)}
    (hπ : Tendsto πs l (𝓝 π))
    (hcm : ∀ᶠ i in l, IsCyclicallyMonotone c (πs i).toMeasure.support) :
    IsCyclicallyMonotone c π.toMeasure.support := by
  intro n x y hmem σ
  by_contra hlt
  rw [not_le] at hlt
  set F : (Fin n → X × Y) → ℝ≥0∞ := fun z ↦ ∑ i, c ((z i).1, (z (σ i)).2) with hFdef
  set G : (Fin n → X × Y) → ℝ≥0∞ := fun z ↦ ∑ i, c ((z i).1, (z i).2) with hGdef
  have hF : Continuous F := continuous_finsetSum _ fun i _ ↦
    hc.comp (((continuous_apply i).fst).prodMk ((continuous_apply (σ i)).snd))
  have hG : Continuous G := continuous_finsetSum _ fun i _ ↦
    hc.comp (((continuous_apply i).fst).prodMk ((continuous_apply i).snd))
  have hopen : IsOpen {z | F z < G z} := isOpen_lt hF hG
  obtain ⟨U, hU, hUsub⟩ := isOpen_pi_iff'.1 hopen (fun i ↦ (x i, y i)) hlt
  have hpos : ∀ i, 0 < π.toMeasure (U i) := fun i ↦
    (Measure.mem_support_iff_forall _).1 (hmem i) _ ((hU i).1.mem_nhds (hU i).2)
  have hev : ∀ᶠ j in l, ∀ i, 0 < (πs j).toMeasure (U i) :=
    eventually_all.2 fun i ↦ eventually_pos_measure_of_tendsto hπ (hU i).1 (hpos i)
  obtain ⟨j, hj, hjcm⟩ := (hev.and hcm).exists
  choose w hwU hws using fun i ↦ Measure.nonempty_inter_support_of_pos (hj i)
  have hw : F w < G w := hUsub fun i _ ↦ hwU i
  exact (hjcm n (fun i ↦ (w i).1) (fun i ↦ (w i).2) (fun i ↦ hws i) σ).not_gt hw

end Support

section Domination

/-- An `ℝ≥0∞` bookkeeping lemma: if `A i + G i = S i`, `S i → s < ∞`, `a + g = s` and
`g ≤ liminf G`, then `limsup A ≤ a`. -/
theorem limsup_le_of_add_eq {ι : Type*} {l : Filter ι} {A G S : ι → ℝ≥0∞} {a g s : ℝ≥0∞}
    (hS : Tendsto S l (𝓝 s)) (hs : s ≠ ∞) (hsum : ∀ᶠ i in l, A i + G i = S i)
    (hsum' : a + g = s) (hg : g ≤ liminf G l) : limsup A l ≤ a := by
  have hg_top : g ≠ ∞ := ne_top_of_le_ne_top hs (hsum' ▸ le_add_self)
  have key : ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ∞ → limsup A l + g ≤ s + ε := by
    intro ε hε hεtop
    have hsε : s + ε ≠ ∞ := ENNReal.add_ne_top.2 ⟨hs, hεtop⟩
    have hev : ∀ᶠ i in l, A i ≤ (s + ε) - G i := by
      filter_upwards [hsum, hS.eventually (gt_mem_nhds (ENNReal.lt_add_right hs hε.ne'))]
        with i hi hi'
      have hle : A i + G i ≤ s + ε := hi.trans_le hi'.le
      exact (ENNReal.cancel_of_ne (ne_top_of_le_ne_top hsε (le_add_self.trans hle))
        ).le_tsub_of_add_le_right hle
    have hL : limsup A l ≤ (s + ε) - g :=
      calc limsup A l ≤ limsup (fun i ↦ (s + ε) - G i) l := limsup_le_limsup hev
        _ = (s + ε) - liminf G l := ENNReal.limsup_const_sub _ _ hsε
        _ ≤ (s + ε) - g := tsub_le_tsub le_rfl hg
    exact add_le_of_le_tsub_right_of_le
      ((hsum' ▸ le_add_self : g ≤ s).trans le_self_add) hL
  have h1 : limsup A l + g ≤ s := ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦
    key ε (by exact_mod_cast hε) ENNReal.coe_ne_top
  rw [← hsum'] at h1
  exact (ENNReal.add_le_add_iff_right hg_top).1 h1

/-- **Generalised dominated convergence along weak convergence.** On a pseudo-metrizable space
with measurable opens, let `c ≤ F` be continuous `ℝ≥0∞`-valued functions with `c` finite. If
probability measures `πᵢ → π` weakly along a filter and `∫ F dπᵢ → ∫ F dπ < ∞`, then
`∫ c dπᵢ → ∫ c dπ`. (Weak lower semicontinuity applied to `c` and to the continuous `F − c`.) -/
theorem tendsto_lintegral_of_le_of_tendsto {ι Ω : Type*} [TopologicalSpace Ω]
    [MeasurableSpace Ω] [OpensMeasurableSpace Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
    {l : Filter ι} {c F : Ω → ℝ≥0∞} (hc : Continuous c) (hctop : ∀ z, c z ≠ ∞)
    (hF : Continuous F) (hcF : ∀ z, c z ≤ F z) {πs : ι → ProbabilityMeasure Ω}
    {π : ProbabilityMeasure Ω} (hπ : Tendsto πs l (𝓝 π))
    (hFlim : Tendsto (fun i ↦ ∫⁻ z, F z ∂(πs i).toMeasure) l (𝓝 (∫⁻ z, F z ∂π.toMeasure)))
    (hFfin : ∫⁻ z, F z ∂π.toMeasure ≠ ∞) :
    Tendsto (fun i ↦ ∫⁻ z, c z ∂(πs i).toMeasure) l (𝓝 (∫⁻ z, c z ∂π.toMeasure)) := by
  let : PseudoMetricSpace Ω := TopologicalSpace.pseudoMetrizableSpacePseudoMetric Ω
  set g : Ω → ℝ≥0∞ := fun z ↦ F z - c z with hgdef
  have hgc : Continuous g := ENNReal.continuousOn_sub.comp_continuous (hF.prodMk hc)
    fun z h ↦ hctop z (congrArg Prod.snd h)
  have hsplit : ∀ ρ : Measure Ω, ∫⁻ z, c z ∂ρ + ∫⁻ z, g z ∂ρ = ∫⁻ z, F z ∂ρ := by
    intro ρ
    rw [← lintegral_add_left hc.measurable]
    exact lintegral_congr fun z ↦ add_tsub_cancel_of_le (hcF z)
  have hle := le_liminf_lintegral_of_tendsto_probabilityMeasure hc.lowerSemicontinuous hπ
  refine tendsto_of_le_liminf_of_limsup_le hle ?_
  exact limsup_le_of_add_eq (G := fun i ↦ ∫⁻ z, g z ∂(πs i).toMeasure) hFlim hFfin
    (Eventually.of_forall fun i ↦ hsplit _) (hsplit _)
    (le_liminf_lintegral_of_tendsto_probabilityMeasure hgc.lowerSemicontinuous hπ)

variable {ι X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  [OpensMeasurableSpace (X × Y)] [TopologicalSpace.PseudoMetrizableSpace (X × Y)]
  {c : X × Y → ℝ≥0∞} {a : X → ℝ≥0∞} {b : Y → ℝ≥0∞}

/-- **Generalised dominated convergence along weakly converging couplings.** Let
`c : X × Y → ℝ≥0∞` be continuous and finite, dominated by `a(x) + b(y)` with `a`, `b`
continuous. Let `πᵢ` (eventually couplings of `μᵢ`, `νᵢ`) converge weakly along a filter to a
coupling `π` of `μ`, `ν`, and suppose `∫ a dμᵢ → ∫ a dμ < ∞` and `∫ b dνᵢ → ∫ b dν < ∞`. Then
`∫ c dπᵢ → ∫ c dπ`.

Lower bound: weak lower semicontinuity of `π ↦ ∫ c dπ`. Upper bound: the same applied to the
continuous nonnegative `a ⊕ b − c`, whose integrals are the converging marginal integrals minus
`∫ c dπᵢ`. This is the uniform-integrability step of Villani, Theorem 5.20 / Lemma 4.3. -/
theorem tendsto_lintegral_of_le_add {l : Filter ι} (hc : Continuous c) (hctop : ∀ z, c z ≠ ∞)
    (ha : Continuous a) (hb : Continuous b) (hcab : ∀ z, c z ≤ a z.1 + b z.2)
    {μs : ι → ProbabilityMeasure X} {νs : ι → ProbabilityMeasure Y} {μ : ProbabilityMeasure X}
    {ν : ProbabilityMeasure Y} {πs : ι → ProbabilityMeasure (X × Y)}
    {π : ProbabilityMeasure (X × Y)}
    (hπs : ∀ᶠ i in l, IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure)
    (hπc : IsCoupling π.toMeasure μ.toMeasure ν.toMeasure) (hπ : Tendsto πs l (𝓝 π))
    (hμa : Tendsto (fun i ↦ ∫⁻ x, a x ∂(μs i).toMeasure) l (𝓝 (∫⁻ x, a x ∂μ.toMeasure)))
    (hμa' : ∫⁻ x, a x ∂μ.toMeasure ≠ ∞)
    (hνb : Tendsto (fun i ↦ ∫⁻ y, b y ∂(νs i).toMeasure) l (𝓝 (∫⁻ y, b y ∂ν.toMeasure)))
    (hνb' : ∫⁻ y, b y ∂ν.toMeasure ≠ ∞) :
    Tendsto (fun i ↦ ∫⁻ z, c z ∂(πs i).toMeasure) l (𝓝 (∫⁻ z, c z ∂π.toMeasure)) := by
  have hsplit : ∀ {ρ : Measure (X × Y)} {α : Measure X} {β : Measure Y}, IsCoupling ρ α β →
      ∫⁻ z, a z.1 + b z.2 ∂ρ = ∫⁻ x, a x ∂α + ∫⁻ y, b y ∂β := by
    intro ρ α β hρ
    have := hρ.lintegral_add_split ha.measurable hb.measurable 0
    simpa using this
  refine tendsto_lintegral_of_le_of_tendsto (F := fun z : X × Y ↦ a z.1 + b z.2) hc hctop
    (by fun_prop) hcab hπ ?_ ?_
  · rw [hsplit hπc]
    exact (hμa.add hνb).congr' (hπs.mono fun i hi ↦ (hsplit hi).symm)
  · rw [hsplit hπc]
    exact ENNReal.add_ne_top.2 ⟨hμa', hνb'⟩

omit [TopologicalSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y] [OpensMeasurableSpace Y]
  [OpensMeasurableSpace (X × Y)] [TopologicalSpace.PseudoMetrizableSpace (X × Y)] in
/-- **Split bound on the transport cost.** If `c (x, y) ≤ a x + b y` with `a`, `b` measurable,
then `C(μ, ν) ≤ ∫ a dμ + ∫ b dν` for probability measures (test the product coupling). -/
theorem transportCost_le_add (hcab : ∀ z, c z ≤ a z.1 + b z.2) (ha : Measurable a)
    (hb : Measurable b) (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y)
    [IsProbabilityMeasure ν] :
    transportCost c μ ν ≤ ∫⁻ x, a x ∂μ + ∫⁻ y, b y ∂ν := by
  refine (transportCost_le_lintegral (isCoupling_prod μ ν) c).trans ?_
  refine (lintegral_mono fun z ↦ (hcab z).trans_eq (zero_add _).symm).trans_eq ?_
  rw [show (fun z : X × Y ↦ 0 + (a z.1 + b z.2)) =
      fun z ↦ (0 : X × Y → ℝ≥0∞) z + a z.1 + b z.2 from funext fun z ↦ by simp,
    (isCoupling_prod μ ν).lintegral_add_split ha hb]
  simp

end Domination

section Polish

variable {ι X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {c : X × Y → ℝ≥0∞} {μs : ι → ProbabilityMeasure X} {νs : ι → ProbabilityMeasure Y}
  {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} {πs : ι → ProbabilityMeasure (X × Y)}

/-- **Weak limits of optimal plans are optimal** (Villani, *Optimal Transport: Old and New*,
Theorem 5.20). Let `X`, `Y` be Polish, `c : X × Y → ℝ≥0∞` continuous and finite everywhere. Along
a nontrivial filter, let `μᵢ → μ` and `νᵢ → ν` weakly, let `πᵢ` be eventually optimal plans for
`(c, μᵢ, νᵢ)` whose optimal costs are eventually finite, and let `πᵢ → π` weakly. Then `π` is an
optimal plan for `(c, μ, ν)`.

No bound on the costs is needed beyond eventual finiteness (the limit problem may even have
infinite value, in which case every coupling is optimal). -/
theorem isOptimalCoupling_of_tendsto_of_continuous {l : Filter ι} [l.NeBot] (hc : Continuous c)
    (hctop : ∀ z, c z ≠ ∞) (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν))
    (hopt : ∀ᶠ i in l,
      IsOptimalCoupling c (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure)
    (hfin : ∀ᶠ i in l, transportCost c (μs i).toMeasure (νs i).toMeasure ≠ ∞)
    {π : ProbabilityMeasure (X × Y)} (hπ : Tendsto πs l (𝓝 π)) :
    IsOptimalCoupling c π.toMeasure μ.toMeasure ν.toMeasure := by
  have hcoup : IsCoupling π.toMeasure μ.toMeasure ν.toMeasure :=
    isCoupling_of_tendsto (hopt.mono fun i hi ↦ hi.toIsCoupling) hπ hμ hν
  have hcm : IsCyclicallyMonotone c π.toMeasure.support :=
    isCyclicallyMonotone_support_of_tendsto hc hπ <| (hopt.and hfin).mono fun i hi ↦
      hi.1.isCyclicallyMonotone_support hc hi.2
  exact hcoup.isOptimalCoupling_of_isCyclicallyMonotone hc.measurable hctop hcm
    π.toMeasure.support_mem_ae


/-- Tightness of a weakly convergent sequence on a Polish space, in the tail form used by the
Tau Ceti compactness theorem, along any filter on `ℕ`. -/
private theorem exists_isTightMeasureSet_image {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] {l : Filter ℕ} {ρs : ℕ → ProbabilityMeasure Z}
    {ρ : ProbabilityMeasure Z} (hρ : Tendsto ρs atTop (𝓝 ρ)) :
    ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (ρs i).toMeasure) '' s) :=
  ⟨univ, univ_mem, (isTightMeasureSet_range_of_tendsto hρ).subset
    (by rintro - ⟨i, -, rfl⟩; exact mem_range_self i)⟩

variable {μs : ℕ → ProbabilityMeasure X} {νs : ℕ → ProbabilityMeasure Y}
  {πs : ℕ → ProbabilityMeasure (X × Y)}

/-- **Optimal plans have a subsequence converging to an optimal plan.** On Polish spaces, for a
continuous finite cost, if `μₙ → μ` and `νₙ → ν` weakly and `πₙ` are eventually optimal for
`(μₙ, νₙ)` with eventually finite optimal cost, there are a strictly increasing `φ` and an
optimal plan `π` for `(μ, ν)` with `π_{φ n} → π` weakly. (Tightness from Prokhorov, optimality
of the limit from `isOptimalCoupling_of_tendsto_of_continuous`.) -/
theorem exists_subseq_tendsto_isOptimalCoupling (hc : Continuous c) (hctop : ∀ z, c z ≠ ∞)
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hopt : ∀ᶠ n in atTop,
      IsOptimalCoupling c (πs n).toMeasure (μs n).toMeasure (νs n).toMeasure)
    (hfin : ∀ᶠ n in atTop, transportCost c (μs n).toMeasure (νs n).toMeasure ≠ ∞) :
    ∃ (π : ProbabilityMeasure (X × Y)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (πs ∘ φ) atTop (𝓝 π) ∧
        IsOptimalCoupling c π.toMeasure μ.toMeasure ν.toMeasure := by
  obtain ⟨l', π, hne, hle, hconv, -⟩ := exists_isCoupling_tendsto_of_isTightMeasureSet
    (exists_isTightMeasureSet_image hμ) (exists_isTightMeasureSet_image hν) hμ hν
    (hopt.mono fun n hn ↦ hn.toIsCoupling)
  have := hne
  have hπ := isOptimalCoupling_of_tendsto_of_continuous hc hctop (hμ.mono_left hle)
    (hν.mono_left hle) (hopt.filter_mono hle) (hfin.filter_mono hle) hconv
  obtain ⟨φ, hφ, hφconv⟩ := (hconv.mapClusterPt.mono hle).tendsto_subseq
  exact ⟨π, φ, hφ, hφconv, hπ⟩

/-- **Uniqueness of the limiting optimal plan gives convergence of the whole sequence**
(Villani, Theorem 5.20, last assertion). Under the hypotheses of
`exists_subseq_tendsto_isOptimalCoupling`, if every optimal plan of `(c, μ, ν)` equals `π₀`, then
`πₙ → π₀` weakly. -/
theorem tendsto_of_forall_isOptimalCoupling_eq (hc : Continuous c) (hctop : ∀ z, c z ≠ ∞)
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hopt : ∀ᶠ n in atTop,
      IsOptimalCoupling c (πs n).toMeasure (μs n).toMeasure (νs n).toMeasure)
    (hfin : ∀ᶠ n in atTop, transportCost c (μs n).toMeasure (νs n).toMeasure ≠ ∞)
    {π₀ : ProbabilityMeasure (X × Y)}
    (huniq : ∀ π : ProbabilityMeasure (X × Y),
      IsOptimalCoupling c π.toMeasure μ.toMeasure ν.toMeasure → π = π₀) :
    Tendsto πs atTop (𝓝 π₀) := by
  by_contra hnot
  obtain ⟨U, hU, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hnot
  set lb : Filter ℕ := atTop ⊓ 𝓟 {n | πs n ∉ U}
  have hne : lb.NeBot := frequently_mem_iff_neBot.mp hfreq
  have hlb : lb ≤ atTop := inf_le_left
  obtain ⟨l', π, hne', hle, hconv, -⟩ := exists_isCoupling_tendsto_of_isTightMeasureSet
    (l := lb) (exists_isTightMeasureSet_image hμ) (exists_isTightMeasureSet_image hν)
    (hμ.mono_left hlb) (hν.mono_left hlb) ((hopt.filter_mono hlb).mono fun n hn ↦ hn.toIsCoupling)
  have := hne'
  have hπ := isOptimalCoupling_of_tendsto_of_continuous hc hctop (hμ.mono_left (hle.trans hlb))
    (hν.mono_left (hle.trans hlb)) (hopt.filter_mono (hle.trans hlb))
    (hfin.filter_mono (hle.trans hlb)) hconv
  rw [huniq π hπ] at hconv
  have hout : ∀ᶠ n in l', πs n ∉ U :=
    (eventually_inf_principal.2 (Eventually.of_forall fun _ h ↦ h)).filter_mono hle
  exact ((hconv.eventually (mem_of_superset hU fun _ h ↦ h)).and hout).exists.elim
    fun _ h ↦ h.2 h.1


/-- **Convergence of the optimal costs** (Villani, Theorem 5.20, with the integrability
condition of his Theorem 5.20/Lemma 4.3 in split form). Let `X`, `Y` be Polish and
`c : X × Y → ℝ≥0∞` continuous and finite, with `c (x, y) ≤ a x + b y` for continuous `a`, `b`.
If `μₙ → μ`, `νₙ → ν` weakly and the marginal integrals converge to finite limits,
`∫ a dμₙ → ∫ a dμ < ∞` and `∫ b dνₙ → ∫ b dν < ∞`, then the optimal costs converge:
`C(μₙ, νₙ) → C(μ, ν)`.

For `c = d^p` with `a = 2^{p-1} d(x₀, ·)^p` and `b` likewise, the hypothesis is convergence of
`p`-th moments, i.e. `Wₚ`-convergence of the marginals. -/
theorem tendsto_transportCost_of_le_add (hc : Continuous c) (hctop : ∀ z, c z ≠ ∞)
    {a : X → ℝ≥0∞} {b : Y → ℝ≥0∞} (ha : Continuous a) (hb : Continuous b)
    (hcab : ∀ z, c z ≤ a z.1 + b z.2) (hμ : Tendsto μs atTop (𝓝 μ))
    (hν : Tendsto νs atTop (𝓝 ν))
    (hμa : Tendsto (fun n ↦ ∫⁻ x, a x ∂(μs n).toMeasure) atTop (𝓝 (∫⁻ x, a x ∂μ.toMeasure)))
    (hμa' : ∫⁻ x, a x ∂μ.toMeasure ≠ ∞)
    (hνb : Tendsto (fun n ↦ ∫⁻ y, b y ∂(νs n).toMeasure) atTop (𝓝 (∫⁻ y, b y ∂ν.toMeasure)))
    (hνb' : ∫⁻ y, b y ∂ν.toMeasure ≠ ∞) :
    Tendsto (fun n ↦ transportCost c (μs n).toMeasure (νs n).toMeasure) atTop
      (𝓝 (transportCost c μ.toMeasure ν.toMeasure)) := by
  refine tendsto_of_le_liminf_of_limsup_le
    (transportCost_le_liminf_transportCost_of_lowerSemicontinuous hc.lowerSemicontinuous hμ hν) ?_
  -- Optimal plans of the moving problems.
  have hex : ∀ n, ∃ π : ProbabilityMeasure (X × Y),
      IsOptimalCoupling c π.toMeasure (μs n).toMeasure (νs n).toMeasure := fun n ↦ by
    obtain ⟨π, hπ⟩ := exists_isOptimalCoupling (μs n).toMeasure (νs n).toMeasure
      hc.lowerSemicontinuous
    exact ⟨⟨π, hπ.toIsCoupling.isProbabilityMeasure⟩, hπ⟩
  choose ρs hρs using hex
  -- The moving optimal values are eventually finite.
  have hfin : ∀ᶠ n in atTop, transportCost c (μs n).toMeasure (νs n).toMeasure ≠ ∞ := by
    filter_upwards [(hμa.add hνb).eventually
      (gt_mem_nhds (ENNReal.lt_add_right (ENNReal.add_ne_top.2 ⟨hμa', hνb'⟩) one_ne_zero))]
      with n hn
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hμa', hνb'⟩,
      ENNReal.one_ne_top⟩) ((transportCost_le_add hcab ha.measurable hb.measurable _ _).trans hn.le)
  by_contra hcon
  obtain ⟨r, hr₁, hr₂⟩ := exists_between (not_le.mp hcon)
  have hfreq : ∃ᶠ n in atTop, r < transportCost c (μs n).toMeasure (νs n).toMeasure :=
    frequently_lt_of_lt_limsup (by isBoundedDefault) hr₂
  set lb : Filter ℕ := atTop ⊓ 𝓟 {n | r < transportCost c (μs n).toMeasure (νs n).toMeasure}
  have hne : lb.NeBot := frequently_mem_iff_neBot.mp hfreq
  have hlb : lb ≤ atTop := inf_le_left
  obtain ⟨l', π, hne', hle, hconv, -⟩ := exists_isCoupling_tendsto_of_isTightMeasureSet
    (l := lb) (exists_isTightMeasureSet_image hμ) (exists_isTightMeasureSet_image hν)
    (hμ.mono_left hlb) (hν.mono_left hlb)
    (Eventually.of_forall fun n ↦ (hρs n).toIsCoupling)
  have := hne'
  have hle' : l' ≤ atTop := hle.trans hlb
  have hπ := isOptimalCoupling_of_tendsto_of_continuous hc hctop (hμ.mono_left hle')
    (hν.mono_left hle') (Eventually.of_forall hρs) (hfin.filter_mono hle') hconv
  have hlim := tendsto_lintegral_of_le_add hc hctop ha hb hcab
    (Eventually.of_forall fun n ↦ (hρs n).toIsCoupling) hπ.toIsCoupling hconv
    (hμa.mono_left hle') hμa' (hνb.mono_left hle') hνb'
  rw [hπ.lintegral_eq] at hlim
  have hbig : ∀ᶠ n in l', r < ∫⁻ z, c z ∂(ρs n).toMeasure :=
    (eventually_inf_principal.2 (Eventually.of_forall fun n hn ↦
      (hρs n).lintegral_eq ▸ hn)).filter_mono hle
  obtain ⟨n, hn₁, hn₂⟩ := ((hlim.eventually (gt_mem_nhds hr₁)).and hbig).exists
  exact lt_asymm hn₁ hn₂

/-- The same as `isOptimalCoupling_of_tendsto_of_continuous`, with the plans assumed to be
couplings concentrated on `c`-cyclically monotone sets (the form used in the otfd papers)
instead of optimal; the two are equivalent for finite costs by Schachermayer–Teichmann. -/
theorem isOptimalCoupling_of_tendsto_of_isCyclicallyMonotone {ι : Type*}
    {μs : ι → ProbabilityMeasure X}
    {νs : ι → ProbabilityMeasure Y} {πs : ι → ProbabilityMeasure (X × Y)} {S : ι → Set (X × Y)}
    {l : Filter ι} [l.NeBot] (hc : Continuous c) (hctop : ∀ z, c z ≠ ∞)
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν))
    (hcoup : ∀ᶠ i in l, IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure)
    (hS : ∀ᶠ i in l, IsCyclicallyMonotone c (S i))
    (hπS : ∀ᶠ i in l, ∀ᵐ z ∂(πs i).toMeasure, z ∈ S i)
    (hfin : ∀ᶠ i in l, transportCost c (μs i).toMeasure (νs i).toMeasure ≠ ∞)
    {π : ProbabilityMeasure (X × Y)} (hπ : Tendsto πs l (𝓝 π)) :
    IsOptimalCoupling c π.toMeasure μ.toMeasure ν.toMeasure :=
  isOptimalCoupling_of_tendsto_of_continuous hc hctop hμ hν
    ((hcoup.and (hS.and hπS)).mono fun _ h ↦
      h.1.isOptimalCoupling_of_isCyclicallyMonotone hc.measurable hctop h.2.1 h.2.2) hfin hπ

end Polish

end StatFormal.OTLimits
