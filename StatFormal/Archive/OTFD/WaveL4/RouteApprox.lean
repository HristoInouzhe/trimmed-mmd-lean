import StatFormal.Lib.Potentials.LocalBound

/-!
# Route (wave L4): stability of approximate potentials (`ε`-subgradient concentration)

Untrusted route file. The library `Foundations/Potentials` proves stability of potentials for plans
whose *supports* lie in the subdifferential graphs of the potentials (`IsPotentialOn`). For C's
inexact hard fits (semi-dual gap `ζ_n → 0`) the plans are only *approximately* concentrated on the
subdifferential graphs: the mass of the pairs `(u, z)` at which `z` fails to be a `δ`-subgradient
tends to zero for every fixed `δ > 0`. This is `ApproxPot`:

  for all `δ > 0` and `c > 0`, eventually every open `V` with `π_i V > c` contains a point `(x, y)`
  with `y` a `δ`-subgradient of `u_i` at `x` (relative to `U`).

Every use of `IsPotentialOn` in the library proofs is "an open set of positive limit mass contains a
support point of `π_i`, at which the subgradient inequality holds"; with `ApproxPot` the positive
limit mass `π V` gives `π_i V > π V / 2` eventually (portmanteau), hence a point with the
`δ`-inequality, and `δ` is chosen as a fraction of the target accuracy. So the library's chain
(local bounds, closedness of the plan–potential relation, identification by uniqueness, existence
of the limit potential) goes through verbatim with `δ`-slacks. The limit potential is an *exact*
potential of the limit plan.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology Gradient InnerProductSpace

namespace StatFormal.OTFD.WaveL4

/-- **Positive mass above a threshold persists along weak convergence** (portmanteau, open sets). -/
theorem eventually_lt_measure_of_tendsto {ι Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [TopologicalSpace.PseudoMetrizableSpace Ω] {l : Filter ι}
    {πs : ι → ProbabilityMeasure Ω} {π : ProbabilityMeasure Ω} (hπ : Tendsto πs l (𝓝 π))
    {V : Set Ω} (hV : IsOpen V) {c : ℝ≥0∞} (hc : c < π.toMeasure V) :
    ∀ᶠ i in l, c < (πs i).toMeasure V := by
  let : PseudoMetricSpace Ω := TopologicalSpace.pseudoMetrizableSpacePseudoMetric Ω
  have hlsc := TauCeti.lowerSemicontinuous_lintegral_probabilityMeasure (Ω := Ω)
    (hV.lowerSemicontinuous_indicator (y := (1 : ℝ≥0∞)) zero_le_one)
  have h0 := hlsc π c (by simpa [lintegral_indicator hV.measurableSet] using hc)
  filter_upwards [hπ.eventually h0] with i hi
  simpa [lintegral_indicator hV.measurableSet] using hi

/-- **Good points in sets of positive limit mass.** If, for every `c > 0`, eventually every open
set of `π_i`-mass `> c` contains a point with property `R i`, and `π_i → π` with `π V > 0`, then
eventually `V` contains a point with property `R i`. -/
theorem eventually_exists_of_approx {ι Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [TopologicalSpace.PseudoMetrizableSpace Ω] {l : Filter ι}
    {πs : ι → ProbabilityMeasure Ω} {π : ProbabilityMeasure Ω} {R : ι → Ω → Prop}
    (h : ∀ c : ℝ≥0∞, 0 < c → ∀ᶠ i in l, ∀ V : Set Ω, IsOpen V → c < (πs i).toMeasure V →
      ∃ z ∈ V, R i z)
    (hπ : Tendsto πs l (𝓝 π)) {V : Set Ω} (hV : IsOpen V) (hpos : 0 < π.toMeasure V) :
    ∀ᶠ i in l, ∃ z ∈ V, R i z := by
  have hne : π.toMeasure V ≠ 0 := hpos.ne'
  have htop : π.toMeasure V ≠ ∞ := measure_ne_top _ _
  filter_upwards [h (π.toMeasure V / 2) (ENNReal.half_pos hne),
    eventually_lt_measure_of_tendsto hπ hV (ENNReal.half_lt_self hne htop)] with i h1 h2
  exact h1 V hV h2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Approximate potentials along a filter**: for every `δ > 0` and `c > 0`, eventually every
open set of `π_i`-mass `> c` contains a point `(x, y)` with `y` a `δ`-subgradient of `u_i` at `x`
relative to `U` (when `x ∈ U`). Exact potentials (`IsPotentialOn`) are approximate potentials. -/
def ApproxPot {ι : Type*} (l : Filter ι) (U : Set E) (us : ι → E → ℝ)
    (πs : ι → ProbabilityMeasure (E × E)) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ c : ℝ≥0∞, 0 < c → ∀ᶠ i in l, ∀ V : Set (E × E), IsOpen V →
    c < (πs i).toMeasure V → ∃ z ∈ V, z.1 ∈ U → ∀ x ∈ U, us i z.1 + ⟪z.2, x - z.1⟫_ℝ ≤ us i x + δ

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem ApproxPot.mono {ι : Type*} {l l' : Filter ι} {U : Set E} {us : ι → E → ℝ}
    {πs : ι → ProbabilityMeasure (E × E)} (h : ApproxPot l U us πs) (hl : l' ≤ l) :
    ApproxPot l' U us πs :=
  fun δ hδ c hc => hl (h δ hδ c hc)

omit [BorelSpace E] in
/-- Exact potentials are approximate potentials. -/
theorem approxPot_of_isPotentialOn {ι : Type*} {l : Filter ι} {U : Set E} {us : ι → E → ℝ}
    {πs : ι → ProbabilityMeasure (E × E)}
    (h : ∀ᶠ i in l, StatFormal.Potentials.IsPotentialOn U (us i) (πs i).toMeasure) :
    ApproxPot l U us πs := by
  intro δ hδ c hc
  filter_upwards [h] with i hi V _ hV
  obtain ⟨z, hzV, hzs⟩ := Measure.nonempty_inter_support_of_pos (hc.trans hV)
  exact ⟨z, hzV, fun hzU x hx => by have := hi z hzs hzU x hx; linarith⟩

/-- `eventually_exists_of_approx` for approximate potentials. -/
theorem ApproxPot.eventually_exists {ι : Type*} {l : Filter ι} {U : Set E} {us : ι → E → ℝ}
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (h : ApproxPot l U us πs) (hπ : Tendsto πs l (𝓝 π)) {δ : ℝ} (hδ : 0 < δ) {V : Set (E × E)}
    (hV : IsOpen V) (hpos : 0 < π.toMeasure V) :
    ∀ᶠ i in l, ∃ z ∈ V, z.1 ∈ U → ∀ x ∈ U, us i z.1 + ⟪z.2, x - z.1⟫_ℝ ≤ us i x + δ :=
  eventually_exists_of_approx (h δ hδ) hπ hV hpos

/-- **Eventual upper bound for normalised approximate potentials** (the library's
`eventually_le_of_tendsto_plan` with `δ = 1`). -/
theorem eventually_le_of_tendsto_plan_approx {ι : Type*} {l : Filter ι} {U : Set E}
    (hU : IsOpen U) {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hsupp : U ⊆ π.toMeasure.fst.support)
    {us : ι → E → ℝ} (hconv : ∀ᶠ i in l, ConvexOn ℝ U (us i)) (hpot : ApproxPot l U us πs)
    {x₀ : E} (hx₀ : x₀ ∈ U) {a : ℝ} (hnorm : Tendsto (fun i => us i x₀) l (𝓝 a))
    {p : E} (hp : p ∈ U) : ∃ M, ∀ᶠ i in l, us i p ≤ M := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU p hp
  set r : ℝ := ε / 3 with hrdef
  have hr : 0 < r := by positivity
  obtain ⟨W, hWfin, hWball, hW⟩ := StatFormal.Potentials.exists_finite_net_neg E
  set c : E → E := fun w => p + r • w with hc
  have hcball : ∀ w ∈ W, dist (c w) p ≤ r := by
    intro w hw
    have hw1 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.1 (hWball hw)
    rw [hc, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have hmass : ∀ w ∈ W, ∃ n : ℕ,
      0 < π.toMeasure (ball (c w) (r / 4) ×ˢ ball (0 : E) n) := by
    intro w hw
    have hcU : c w ∈ U := hεU (mem_ball.2 ((hcball w hw).trans_lt (by linarith)))
    have hpos : 0 < π.toMeasure.fst (ball (c w) (r / 4)) :=
      (Measure.mem_support_iff_forall _).1 (hsupp hcU) _ (ball_mem_nhds _ (by positivity))
    rw [Measure.fst_apply measurableSet_ball] at hpos
    by_contra hcon
    push Not at hcon
    have hunion : Prod.fst ⁻¹' ball (c w) (r / 4) =
        ⋃ n : ℕ, ball (c w) (r / 4) ×ˢ ball (0 : E) n := by
      ext z
      simp only [mem_preimage, mem_iUnion, mem_prod, mem_ball_zero_iff]
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_gt ‖z.2‖
        exact ⟨n, hz, hn⟩
      · rintro ⟨n, hz, -⟩; exact hz
    rw [hunion, measure_iUnion_null fun n => le_antisymm (hcon n) zero_le] at hpos
    exact lt_irrefl _ hpos
  choose! n hn using hmass
  set N : ℝ := ∑ w ∈ hWfin.toFinset, (n w : ℝ) with hN
  have hnN : ∀ w ∈ W, (n w : ℝ) ≤ N := fun w hw =>
    Finset.single_le_sum (f := fun w => (n w : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      (hWfin.mem_toFinset.2 hw)
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hev : ∀ᶠ i in l, ∀ w ∈ W, ∃ z ∈ ball (c w) (r / 4) ×ˢ ball (0 : E) (n w),
      z.1 ∈ U → ∀ x ∈ U, us i z.1 + ⟪z.2, x - z.1⟫_ℝ ≤ us i x + 1 :=
    (eventually_all_finite hWfin).2 fun w hw =>
      hpot.eventually_exists hπ one_pos (isOpen_ball.prod isOpen_ball) (hn w hw)
  refine ⟨a + 2 + N * (‖x₀ - p‖ + 2 * r), ?_⟩
  filter_upwards [hev, hconv, hnorm.eventually (gt_mem_nhds (lt_add_one a))]
    with i hi hci hai
  choose! z hzA hzs using hi
  have hz1 : ∀ w ∈ W, dist (z w).1 (c w) < r / 4 := fun w hw => (hzA w hw).1
  have hz2 : ∀ w ∈ W, ‖(z w).2‖ < n w := fun w hw => mem_ball_zero_iff.1 (hzA w hw).2
  have hzp : ∀ w ∈ W, dist (z w).1 p < 2 * r := fun w hw => by
    linarith [dist_triangle (z w).1 (c w) p, hz1 w hw, hcball w hw]
  have hzU : ∀ w ∈ W, (z w).1 ∈ U := fun w hw =>
    hεU (mem_ball.2 ((hzp w hw).trans (by linarith)))
  have hval : ∀ w ∈ W, us i (z w).1 ≤ a + 2 + N * (‖x₀ - p‖ + 2 * r) := by
    intro w hw
    have h1 := hzs w hw (hzU w hw) x₀ hx₀
    have h2 : -⟪(z w).2, x₀ - (z w).1⟫_ℝ ≤ ‖(z w).2‖ * ‖x₀ - (z w).1‖ := by
      have := abs_real_inner_le_norm (z w).2 (x₀ - (z w).1)
      linarith [neg_abs_le ⟪(z w).2, x₀ - (z w).1⟫_ℝ]
    have h3 : ‖x₀ - (z w).1‖ ≤ ‖x₀ - p‖ + 2 * r := by
      have := norm_sub_le_norm_sub_add_norm_sub x₀ p (z w).1
      rw [← dist_eq_norm p, dist_comm] at this
      linarith [hzp w hw]
    have h4 : ‖(z w).2‖ * ‖x₀ - (z w).1‖ ≤ N * (‖x₀ - p‖ + 2 * r) :=
      mul_le_mul ((hz2 w hw).le.trans (hnN w hw)) h3 (norm_nonneg _) hN0
    linarith
  have hhull : p ∈ convexHull ℝ ((fun w => (z w).1) '' W) := by
    refine StatFormal.Potentials.mem_convexHull_of_near_net hWfin hW hr fun w hw => ?_
    rw [← dist_eq_norm]
    exact (hz1 w hw).le
  obtain ⟨y, ⟨w, hw, rfl⟩, hy⟩ :=
    hci.exists_ge_of_mem_convexHull (by rintro _ ⟨w, hw, rfl⟩; exact hzU w hw) hhull
  exact hy.trans (hval w hw)

/-- **Eventual two-sided bound for normalised approximate potentials** (the library's
`eventually_abs_le_of_tendsto_plan`; the lower bound is pure convexity). -/
theorem eventually_abs_le_of_tendsto_plan_approx {ι : Type*} {l : Filter ι} {U : Set E}
    (hU : IsOpen U) {πs : ι → ProbabilityMeasure (E × E)}
    {π : ProbabilityMeasure (E × E)} (hπ : Tendsto πs l (𝓝 π))
    (hsupp : U ⊆ π.toMeasure.fst.support)
    {us : ι → E → ℝ} (hconv : ∀ᶠ i in l, ConvexOn ℝ U (us i)) (hpot : ApproxPot l U us πs)
    {x₀ : E} (hx₀ : x₀ ∈ U) {a : ℝ} (hnorm : Tendsto (fun i => us i x₀) l (𝓝 a))
    {p : E} (hp : p ∈ U) : ∃ M, ∀ᶠ i in l, |us i p| ≤ M := by
  obtain ⟨M₁, hM₁⟩ := eventually_le_of_tendsto_plan_approx hU hπ hsupp hconv hpot hx₀ hnorm hp
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set ε : ℝ := δ / (2 * (‖x₀ - p‖ + 1)) with hεdef
  have hε : 0 < ε := by positivity
  set q : E := x₀ + ε • (x₀ - p) with hq
  have hqU : q ∈ U := by
    refine hδU (mem_ball.2 ?_)
    rw [hq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have h1 : ε * ‖x₀ - p‖ ≤ ε * (‖x₀ - p‖ + 1) := by nlinarith
    have h2 : ε * (‖x₀ - p‖ + 1) = δ / 2 := by
      rw [hεdef]; field_simp
    linarith
  obtain ⟨M₂, hM₂⟩ := eventually_le_of_tendsto_plan_approx hU hπ hsupp hconv hpot hx₀ hnorm hqU
  set α : ℝ := (1 + ε)⁻¹ with hα
  set β : ℝ := ε * (1 + ε)⁻¹ with hβ
  have hα0 : 0 < α := by positivity
  have hβ0 : 0 < β := by positivity
  have hαβ : α + β = 1 := by rw [hα, hβ]; field_simp
  have hcomb : α • q + β • p = x₀ := by
    have hαε : α + α * ε = 1 := by rw [hα]; field_simp
    calc α • q + β • p = (α + α * ε) • x₀ + (β - α * ε) • p := by
          rw [hq]; simp only [smul_add, smul_sub, smul_smul, add_smul, sub_smul]; abel
      _ = x₀ := by
          rw [hαε, show β - α * ε = 0 by rw [hα, hβ]; ring, zero_smul, one_smul, add_zero]
  refine ⟨max M₁ (-(((a - 1) - α * M₂) / β)), ?_⟩
  filter_upwards [hM₁, hM₂, hconv, hnorm.eventually (lt_mem_nhds (sub_one_lt a))]
    with i h1 h2 hci hai
  have hJ := hci.2 hqU hp hα0.le hβ0.le hαβ
  rw [hcomb, smul_eq_mul, smul_eq_mul] at hJ
  have hlow : ((a - 1) - α * M₂) / β ≤ us i p := by
    rw [div_le_iff₀ hβ0]
    nlinarith
  exact abs_le.2 ⟨by linarith [le_max_right M₁ (-(((a - 1) - α * M₂) / β))],
    h1.trans (le_max_left _ _)⟩

/-- **Limits of approximate potentials are exact potentials of the limit plan** (the library's
`isPotentialOn_of_tendsto` with slack `δ = ε/4`). -/
theorem isPotentialOn_of_tendsto_approx {ι : Type*} {l : Filter ι} [l.NeBot] {U : Set E}
    (hU : IsOpen U) {us : ι → E → ℝ} {u : E → ℝ} (hconv : ∀ᶠ i in l, ConvexOn ℝ U (us i))
    (hlim : ∀ x ∈ U, Tendsto (fun i => us i x) l (𝓝 (u x)))
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hpot : ApproxPot l U us πs) :
    StatFormal.Potentials.IsPotentialOn U u π.toMeasure := by
  intro z hz hzU x hx
  have hu : ConvexOn ℝ U u := StatFormal.Convex.convexOn_of_tendsto hconv hlim
  have hcu : ContinuousAt u z.1 := (hu.continuousOn hU).continuousAt (hU.mem_nhds hzU)
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hzU)
  have hunif := StatFormal.Convex.tendstoUniformlyOn_of_tendsto hU hconv hlim hrU
    (isCompact_closedBall z.1 r)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set h : E × E → ℝ := fun w => u w.1 + ⟪w.2, x - w.1⟫_ℝ with hh
  have hcont : ContinuousAt h z :=
    (hcu.comp continuousAt_fst).add
      (continuous_snd.inner (continuous_const.sub continuous_fst)).continuousAt
  have hε4 : 0 < ε / 4 := by positivity
  have hN : {w | h z - ε / 4 < h w} ∩ Prod.fst ⁻¹' ball z.1 r ∈ 𝓝 z :=
    inter_mem (hcont.eventually (isOpen_Ioi.mem_nhds (by simp only [mem_Ioi]; linarith)))
      (continuous_fst.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr))
  obtain ⟨V, hVsub, hVo, hzV⟩ := _root_.mem_nhds_iff.1 hN
  have hpos : 0 < π.toMeasure V := (Measure.mem_support_iff_forall z).1 hz _ (hVo.mem_nhds hzV)
  obtain ⟨i, ⟨w, hwV, hws⟩, hiu, hix⟩ :=
    ((hpot.eventually_exists hπ hε4 hVo hpos).and
      ((Metric.tendstoUniformlyOn_iff.1 hunif (ε / 4) hε4).and
        ((hlim x hx).eventually (Metric.ball_mem_nhds _ hε4)))).exists
  have hwN := hVsub hwV
  have hw1 : w.1 ∈ closedBall z.1 r := ball_subset_closedBall hwN.2
  have hineq := hws (hrU hw1) x hx
  have h1 := hiu w.1 hw1
  rw [Real.dist_eq] at h1 hix
  have hwlt : h z - ε / 4 < h w := hwN.1
  simp only [hh] at hwlt
  have := abs_lt.1 h1
  have := abs_lt.1 hix
  linarith

/-- **Stability of normalised approximate potentials** (the library's `tendsto_of_tendsto_plan`). -/
theorem tendsto_of_tendsto_plan_approx {ι : Type*} {l : Filter ι} {ρ : Measure E}
    [ρ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) {x₀ : E} (hx₀ : x₀ ∈ U)
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hμ : π.toMeasure.fst ≪ ρ) (hUc : π.toMeasure.fst Uᶜ = 0)
    (hsupp : U ⊆ π.toMeasure.fst.support)
    {us : ι → E → ℝ} (hconv : ∀ᶠ i in l, ConvexOn ℝ U (us i)) (hpot : ApproxPot l U us πs)
    {a : ℝ} (hnorm : Tendsto (fun i => us i x₀) l (𝓝 a))
    {φ : E → ℝ} (hφ : ConvexOn ℝ U φ)
    (hpφ : StatFormal.Potentials.IsPotentialOn U φ π.toMeasure) :
    ∀ x ∈ U, Tendsto (fun i => us i x) l (𝓝 (φ x - φ x₀ + a)) := by
  have hbdd : ∀ x ∈ U, ∃ M, ∀ᶠ i in l, |us i x| ≤ M := fun _ hp =>
    eventually_abs_le_of_tendsto_plan_approx hU hπ hsupp hconv hpot hx₀ hnorm hp
  intro x hx
  rw [tendsto_iff_ultrafilter]
  intro 𝒰 h𝒰
  obtain ⟨g, hlimg⟩ := StatFormal.Potentials.exists_tendsto_ultrafilter hbdd 𝒰 h𝒰
  have hconv' : ∀ᶠ i in (𝒰 : Filter ι), ConvexOn ℝ U (us i) := h𝒰 hconv
  have hgc : ConvexOn ℝ U g := StatFormal.Convex.convexOn_of_tendsto hconv' hlimg
  have hgpot : StatFormal.Potentials.IsPotentialOn U g π.toMeasure :=
    isPotentialOn_of_tendsto_approx hU hconv' hlimg (hπ.mono_left h𝒰) (hpot.mono h𝒰)
  obtain ⟨C, hC⟩ := StatFormal.Potentials.exists_eq_add_const_of_isPotentialOn hU hgc hφ hμ hUc
    hsupp hgpot hpφ
  have hg0 : g x₀ = a := tendsto_nhds_unique (hlimg x₀ hx₀) (hnorm.mono_left h𝒰)
  have hCa : C = a - φ x₀ := by have := hC x₀ hx₀; linarith
  have hgx : g x = φ x - φ x₀ + a := by rw [hC x hx, hCa]; ring
  rw [← hgx]
  exact hlimg x hx

/-- **Existence of the limit potential and convergence to it, for approximate potentials** (the
library's `exists_tendstoLocallyUniformlyOn_potential`). -/
theorem exists_tendstoLocallyUniformlyOn_potential_approx {ι : Type*} {l : Filter ι} [l.NeBot]
    {ρ : Measure E} [ρ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) {x₀ : E} (hx₀ : x₀ ∈ U)
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hμ : π.toMeasure.fst ≪ ρ) (hUc : π.toMeasure.fst Uᶜ = 0)
    (hsupp : U ⊆ π.toMeasure.fst.support)
    {us : ι → E → ℝ} (hconv : ∀ᶠ i in l, ConvexOn ℝ U (us i)) (hpot : ApproxPot l U us πs)
    {a : ℝ} (hnorm : Tendsto (fun i => us i x₀) l (𝓝 a)) :
    ∃ φ : E → ℝ, ConvexOn ℝ U φ ∧ φ x₀ = a ∧
      StatFormal.Potentials.IsPotentialOn U φ π.toMeasure ∧
      (∀ᵐ z ∂π.toMeasure, z.1 ∈ U → z.2 = ∇ φ z.1) ∧ TendstoLocallyUniformlyOn us φ l U := by
  have hbdd : ∀ x ∈ U, ∃ M, ∀ᶠ i in l, |us i x| ≤ M := fun _ hp =>
    eventually_abs_le_of_tendsto_plan_approx hU hπ hsupp hconv hpot hx₀ hnorm hp
  obtain ⟨g, hlimg⟩ :=
    StatFormal.Potentials.exists_tendsto_ultrafilter hbdd (Ultrafilter.of l) (Ultrafilter.of_le l)
  have h𝒰 : (Ultrafilter.of l : Filter ι) ≤ l := Ultrafilter.of_le l
  have hgc : ConvexOn ℝ U g := StatFormal.Convex.convexOn_of_tendsto (h𝒰 hconv) hlimg
  have hgpot : StatFormal.Potentials.IsPotentialOn U g π.toMeasure :=
    isPotentialOn_of_tendsto_approx hU (h𝒰 hconv) hlimg (hπ.mono_left h𝒰) (hpot.mono h𝒰)
  have hg0 : g x₀ = a := tendsto_nhds_unique (hlimg x₀ hx₀) (hnorm.mono_left h𝒰)
  have hlim := tendsto_of_tendsto_plan_approx hU hx₀ hπ hμ hUc hsupp hconv hpot hnorm hgc hgpot
  have hlim' : ∀ x ∈ U, Tendsto (fun i => us i x) l (𝓝 (g x)) := fun x hx => by
    have := hlim x hx
    rwa [hg0, sub_add_cancel] at this
  exact ⟨g, hgc, hg0, hgpot,
    StatFormal.Potentials.ae_snd_eq_gradient_of_isPotentialOn hU hgc hμ hgpot,
    StatFormal.Convex.tendstoLocallyUniformlyOn_of_tendsto hU hconv hlim'⟩

end StatFormal.OTFD.WaveL4
