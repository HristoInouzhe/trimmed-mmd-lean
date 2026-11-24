import StatFormal.Archive.Wave25b.Statements
import StatFormal.Archive.Wave25b.RouteHardMain
import StatFormal.Lib.ConvexH.SubgradLimit
import StatFormal.Archive.OTFD.WaveL6.Proofs

/-!
# Route (wave 25b): A `thm:app-ghs-stability` (i), (ii) (untrusted)

GHS's Thm 3.1(i) with moving marginals `P_n ⇀ P`, `Q_n ⇀ Q`. Plan stability (frozen `plan_stab_a_uncond`) gives
`γ_n ⇀ (Id × 𝔽)#P`. At `x ∈ int (supp P)`, Gâteaux point of `ψ`, and `t, r > 0` small, the open set
`A = {(x', y') : x' ∈ B(x − t h, r), ⟪y', h⟫ > ⟪𝔽 x, h⟫ − 3ε}` has positive limit mass (the subgradient inequality of
`ψ` at `P`-a.e. `x' ∈ B(x − t h, r)` and the Gâteaux quotient), so by the portmanteau theorem `γ_n(A) > 0` eventually,
and `A` contains a pair `(x', y') ∈ ∂ψ_n` with `‖y'‖ ≤ M`. Monotonicity of `∂ψ_n` against `(x_n, y_n)` gives the lower
bound; `±h` and compactness give the uniform statement, and the common compact range gives the norm form (as in the
library `ConvexH/SubgradLimit`, whose fixed-marginal results are used for `⟪𝔽 x_k, h⟫ → ⟪𝔽 x, h⟫`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave25b

open StatFormal.OTFD.WaveL1 (CycMon CMConc IsCMMapAE Graph LipNull Mom2 Euc)
open StatFormal.OTFD.WaveL3 (Mom1)
open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Wave22a (IsSubgrad)
open StatFormal.ConvexH (Subgrad tendsto_twoPoint norm_le_of_subgrad subgrad_of_hasLineDerivAt
  tendsto_inner_of_subgrad)

section Mono
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem subgradOn_mono {D : Set H} {f : H → ℝ} {x y x' y' : H} (h1 : IsSubgradOn D f x y)
    (h2 : IsSubgradOn D f x' y') : 0 ≤ ⟪y - y', x - x'⟫ := by
  have a := h1.2 x' h2.1
  have b := h2.2 x h1.1
  have e1 : ⟪y', x - x'⟫ = -⟪y', x' - x⟫ := by rw [← inner_neg_right, neg_sub]
  have e2 : ⟪y, x - x'⟫ = -⟪y, x' - x⟫ := by rw [← inner_neg_right, neg_sub]
  rw [inner_sub_left]
  linarith

theorem cycMon_subgradOn (D : Set H) (f : H → ℝ) : CycMon {p : H × H | IsSubgradOn D f p.1 p.2} := by
  intro m z hz
  have hle : ∀ i, ⟪(z i).2, (z (finRotate m i)).1 - (z i).1⟫ ≤ f (z (finRotate m i)).1 - f (z i).1 := by
    intro i
    have := (hz i).2 _ (hz (finRotate m i)).1
    linarith
  refine (Finset.sum_le_sum fun i _ => hle i).trans (le_of_eq ?_)
  rw [Finset.sum_sub_distrib, Equiv.sum_comp (finRotate m) (fun i => f (z i).1), sub_self]

end Mono

section Seq
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

/-- **Lower bound with moving marginals.** -/
theorem eventually_le_inner_plans (P : ProbabilityMeasure H) {F : H → H} (hFm : Measurable F)
    (γ : ℕ → ProbabilityMeasure (H × H)) {D : ℕ → Set H} {f : ℕ → H → ℝ} {ψ : H → ℝ} {M L : ℝ}
    (hγΓ : ∀ n, ∀ᵐ p ∂(γ n : Measure (H × H)), IsSubgradOn (D n) (f n) p.1 p.2)
    (hγM : ∀ n, ∀ᵐ p ∂(γ n : Measure (H × H)), ‖p.2‖ ≤ M)
    (hlim : Tendsto γ atTop (𝓝 (P.map fun x => (x, F x))))
    (hF : ∀ᵐ x ∂(P : Measure H), Subgrad ψ x (F x)) (hL : ∀ a b, |ψ a - ψ b| ≤ L * ‖a - b‖) (hL0 : 0 ≤ L)
    {x h : H} (hx : x ∈ interior (P : Measure H).support) (hd : HasLineDerivAt ℝ ψ ⟪F x, h⟫ x h)
    {xn yn : ℕ → H} (hxn : Tendsto xn atTop (𝓝 x)) (hyn : ∀ᶠ n in atTop, IsSubgradOn (D n) (f n) (xn n) (yn n))
    (hynM : ∀ᶠ n in atTop, ‖yn n‖ ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ⟪F x, h⟫ - 4 * ε ≤ ⟪yn n, h⟫ := by
  set c := ⟪F x, h⟫ with hcdef
  have hM0 : 0 ≤ M := by
    obtain ⟨n, hn⟩ := hynM.exists
    exact (norm_nonneg _).trans hn
  have hsupp : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + (-t) • h ∈ (P : Measure H).support := by
    have hc : Tendsto (fun t : ℝ => x + (-t) • h) (𝓝 0) (𝓝 x) := by
      have : Continuous fun t : ℝ => x + (-t) • h := by fun_prop
      simpa using this.tendsto 0
    exact (hc.mono_left nhdsWithin_le_nhds).eventually
      (mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset)
  obtain ⟨t, htD, hta, ht0⟩ :=
    (((tendsto_twoPoint hd).eventually (Metric.ball_mem_nhds c hε)).and
      (hsupp.and self_mem_nhdsWithin)).exists
  set a := x + (-t) • h with ha
  have ht0' : (0 : ℝ) < t := ht0
  set r := ε * t / (2 * L + 4 * M + 1) with hr
  have hden : 0 < 2 * L + 4 * M + 1 := by linarith
  have hr0 : 0 < r := div_pos (mul_pos hε ht0') hden
  have hrle : (2 * L + 4 * M) * r ≤ ε * t := by
    rw [hr, mul_div_assoc', div_le_iff₀ hden]
    nlinarith [mul_pos hε ht0']
  have hB : 0 < (P : Measure H) (ball a r) :=
    (Measure.mem_support_iff_forall a).1 hta _ (ball_mem_nhds a hr0)
  have hDt : |(ψ a - ψ (x + (-(2 * t)) • h)) / t - c| < ε := by
    have := mem_ball.mp htD; rwa [Real.dist_eq] at this
  have hA : t * ((ψ a - ψ (x + (-(2 * t)) • h)) / t) = ψ a - ψ (x + (-(2 * t)) • h) := by field_simp
  have hquot : t * (c - ε) ≤ ψ a - ψ (x + (-(2 * t)) • h) := by
    rw [← hA]; exact mul_le_mul_of_nonneg_left (by linarith [(abs_lt.mp hDt).1]) ht0'.le
  -- the open set
  set A : Set (H × H) := {p | p.1 ∈ ball a r ∧ c - 3 * ε < ⟪p.2, h⟫} with hAdef
  have hAopen : IsOpen A := by
    have hAeq : A = (Prod.fst ⁻¹' ball a r) ∩ {p : H × H | c - 3 * ε < ⟪p.2, h⟫} := rfl
    rw [hAeq]
    exact (isOpen_ball.preimage continuous_fst).inter
      (isOpen_lt continuous_const (continuous_snd.inner continuous_const))
  -- the limit mass of `A`
  have hgood : ∀ x' ∈ ball a r, Subgrad ψ x' (F x') → c - 3 * ε < ⟪F x', h⟫ := by
    intro x' hx' hs
    have s1 := hs (x' - t • h)
    rw [sub_sub_cancel_left, inner_neg_right, real_inner_smul_right] at s1
    have hx'r : ‖x' - a‖ < r := by rw [← dist_eq_norm]; exact mem_ball.mp hx'
    have l1 := (abs_le.mp (hL x' a)).1
    have l2 := (abs_le.mp (hL (x' - t • h) (x + (-(2 * t)) • h))).2
    have hpt : x' - t • h - (x + (-(2 * t)) • h) = x' - a := by
      rw [ha]; simp only [neg_smul, mul_smul, two_smul]; abel
    rw [hpt] at l2
    have hLr := mul_le_mul_of_nonneg_left hx'r.le hL0
    have key : t * (c - 2 * ε) ≤ t * ⟪F x', h⟫ := by nlinarith
    have : c - 2 * ε ≤ ⟪F x', h⟫ := le_of_mul_le_mul_left key ht0'
    linarith
  have hlimA : 0 < ((P.map fun x => (x, F x) : ProbabilityMeasure (H × H)) : Measure (H × H)) A := by
    have hgm : Measurable fun x => (x, F x) := measurable_id.prodMk hFm
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply hgm hAopen.measurableSet]
    refine lt_of_lt_of_le hB ?_
    have h0 : (P : Measure H) {y | ¬ Subgrad ψ y (F y)} = 0 := ae_iff.mp hF
    calc (P : Measure H) (ball a r) ≤ (P : Measure H) ((fun x => (x, F x)) ⁻¹' A ∪ {y | ¬ Subgrad ψ y (F y)}) := by
          refine measure_mono fun y hy => ?_
          by_cases hs : Subgrad ψ y (F y)
          · exact Or.inl ⟨hy, hgood y hy hs⟩
          · exact Or.inr hs
      _ ≤ _ := (measure_union_le _ _).trans (by rw [h0, add_zero])
  have hev : ∀ᶠ n in atTop, 0 < (γ n : Measure (H × H)) A := by
    have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hAopen
    exact eventually_lt_of_lt_liminf (lt_of_lt_of_le hlimA hle)
  filter_upwards [hev, hxn.eventually (Metric.ball_mem_nhds x hr0), hyn, hynM] with n hn hxr hyn' hynM'
  -- a good pair in `A`
  obtain ⟨p, hpA, hpΓ, hpM⟩ : ∃ p ∈ A, IsSubgradOn (D n) (f n) p.1 p.2 ∧ ‖p.2‖ ≤ M := by
    by_contra hcon
    push Not at hcon
    have hsub : A ⊆ {p | ¬ IsSubgradOn (D n) (f n) p.1 p.2} ∪ {p | ¬ ‖p.2‖ ≤ M} := by
      intro p hp
      by_cases h1 : IsSubgradOn (D n) (f n) p.1 p.2
      · exact Or.inr (not_le.mpr (hcon p hp h1))
      · exact Or.inl h1
    have h1 : (γ n : Measure (H × H)) {p | ¬ IsSubgradOn (D n) (f n) p.1 p.2} = 0 := ae_iff.mp (hγΓ n)
    have h2 : (γ n : Measure (H × H)) {p | ¬ ‖p.2‖ ≤ M} = 0 := ae_iff.mp (hγM n)
    have := (measure_mono (μ := (γ n : Measure (H × H))) hsub).trans (measure_union_le _ _)
    rw [h1, h2, add_zero] at this
    exact absurd hn (not_lt.mpr this)
  obtain ⟨hp1, hp2⟩ := hpA
  have hmono := subgradOn_mono hyn' hpΓ
  -- algebra
  set w := xn n - p.1 - t • h with hw
  have hp1r : ‖p.1 - a‖ ≤ r := by rw [← dist_eq_norm]; exact (mem_ball.mp hp1).le
  have hxnr : ‖xn n - x‖ ≤ r := by rw [← dist_eq_norm]; exact (mem_ball.mp hxr).le
  have hw' : ‖w‖ ≤ 2 * r := by
    have : w = (xn n - x) - (p.1 - a) := by rw [hw, ha, neg_smul]; abel
    rw [this]
    exact (norm_sub_le _ _).trans (by linarith)
  have e1 : ⟪yn n - p.2, xn n - p.1⟫ = t * ⟪yn n, h⟫ - t * ⟪p.2, h⟫ + ⟪yn n - p.2, w⟫ := by
    have : xn n - p.1 = t • h + w := by rw [hw]; abel
    rw [this, inner_add_right, inner_smul_right, inner_sub_left]
    ring
  have b1 : |⟪yn n - p.2, w⟫| ≤ 2 * M * (2 * r) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul ((norm_sub_le _ _).trans (by linarith)) hw'
      (norm_nonneg _) (by linarith))
  have h5 : t * (c - 4 * ε) ≤ t * ⟪yn n, h⟫ := by
    nlinarith [abs_le.mp b1, mul_le_mul_of_nonneg_left hp2.le ht0'.le]
  exact le_of_mul_le_mul_left h5 ht0'

/-- **Sequential two-sided form.** -/
theorem tendsto_inner_plans (P : ProbabilityMeasure H) {F : H → H} (hFm : Measurable F)
    (γ : ℕ → ProbabilityMeasure (H × H)) {D : ℕ → Set H} {f : ℕ → H → ℝ} {ψ : H → ℝ} {M L : ℝ}
    (hγΓ : ∀ n, ∀ᵐ p ∂(γ n : Measure (H × H)), IsSubgradOn (D n) (f n) p.1 p.2)
    (hγM : ∀ n, ∀ᵐ p ∂(γ n : Measure (H × H)), ‖p.2‖ ≤ M)
    (hlim : Tendsto γ atTop (𝓝 (P.map fun x => (x, F x))))
    (hF : ∀ᵐ x ∂(P : Measure H), Subgrad ψ x (F x)) (hL : ∀ a b, |ψ a - ψ b| ≤ L * ‖a - b‖) (hL0 : 0 ≤ L)
    {x : H} (hx : x ∈ interior (P : Measure H).support) (hd : ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v)
    {xn yn : ℕ → H} (hxn : Tendsto xn atTop (𝓝 x)) (hyn : ∀ᶠ n in atTop, IsSubgradOn (D n) (f n) (xn n) (yn n))
    (hynM : ∀ᶠ n in atTop, ‖yn n‖ ≤ M) (h : H) :
    Tendsto (fun n => ⟪yn n, h⟫) atTop (𝓝 ⟪F x, h⟫) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    have hε : 0 < (⟪F x, h⟫ - b) / 8 := by linarith
    filter_upwards [eventually_le_inner_plans P hFm γ hγΓ hγM hlim hF hL hL0 hx (hd h) hxn hyn hynM hε]
      with n hn
    linarith
  · intro b hb
    have hε : 0 < (b - ⟪F x, h⟫) / 8 := by linarith
    filter_upwards [eventually_le_inner_plans P hFm γ hγΓ hγM hlim hF hL hL0 hx (hd (-h)) hxn hyn hynM hε]
      with n hn
    rw [inner_neg_right, inner_neg_right] at hn
    linarith

/-- `⟪𝔽 x_k, h⟫ → ⟪𝔽 x, h⟫` along `x_k → x` inside `𝒦₀` (fixed-marginal library result with `f_n = ψ`). -/
theorem tendsto_inner_F (P : Measure H) {F : H → H} {ψ : H → ℝ} {L : ℝ}
    (hF : ∀ᵐ x ∂P, Subgrad ψ x (F x)) (hL : ∀ a b, |ψ a - ψ b| ≤ L * ‖a - b‖) (hL0 : 0 ≤ L)
    (hψ : ConvexOn ℝ univ ψ) {K₀ : Set H} (hKs : K₀ ⊆ interior P.support)
    (hd : ∀ x ∈ K₀, ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v) {x : H} (hx : x ∈ K₀)
    {xn : ℕ → H} (hxK : ∀ n, xn n ∈ K₀) (hxn : Tendsto xn atTop (𝓝 x)) (h : H) :
    Tendsto (fun n => ⟪F (xn n), h⟫) atTop (𝓝 ⟪F x, h⟫) := by
  have hconst : ∀ δ : ℝ, 0 < δ → Tendsto (fun _ : ℕ => P {y | δ ≤ ‖F y - F y‖}) atTop (𝓝 0) := by
    intro δ hδ
    have : {y | δ ≤ ‖F y - F y‖} = (∅ : Set H) := by ext y; simp [not_le.mpr hδ]
    simp only [this, measure_empty]
    exact tendsto_const_nhds
  exact tendsto_inner_of_subgrad P (f := fun _ => ψ) (G := fun _ => F)
    (fun _ _ _ hy => norm_le_of_subgrad hL hy) (fun _ => hF) hF hL hL0 hconst
    (hKs hx) (hd x hx) hxn (yn := fun n => F (xn n))
    (fun n => subgrad_of_hasLineDerivAt hψ (hd _ (hxK n))) h

/-- The core hypotheses, as one structure. -/
structure GHSCore (P : ProbabilityMeasure H) (F : H → H) (γ : ℕ → ProbabilityMeasure (H × H))
    (D : ℕ → Set H) (f : ℕ → H → ℝ) (ψ : H → ℝ) (M L : ℝ) (N₀ : ℕ) (K₀ : Set H) : Prop where
  hFm : Measurable F
  hγΓ : ∀ n, ∀ᵐ p ∂(γ n : Measure (H × H)), IsSubgradOn (D n) (f n) p.1 p.2
  hγM : ∀ n, ∀ᵐ p ∂(γ n : Measure (H × H)), ‖p.2‖ ≤ M
  hlim : Tendsto γ atTop (𝓝 (P.map fun x => (x, F x)))
  hF : ∀ᵐ x ∂(P : Measure H), Subgrad ψ x (F x)
  hL : ∀ a b, |ψ a - ψ b| ≤ L * ‖a - b‖
  hψ : ConvexOn ℝ univ ψ
  hK : IsCompact K₀
  hKs : K₀ ⊆ interior (P : Measure H).support
  hd : ∀ x ∈ K₀, ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v
  hbd : ∀ n, N₀ ≤ n → ∀ x ∈ K₀, ∀ y, IsSubgradOn (D n) (f n) x y → ‖y‖ ≤ M

/-- Along a subsequence of pairs over `𝒦₀`, `⟪y_k − 𝔽 x_k, h⟫ → 0`. -/
theorem GHSCore.tendsto_sub {P : ProbabilityMeasure H} {F : H → H} {γ : ℕ → ProbabilityMeasure (H × H)}
    {D : ℕ → Set H} {f : ℕ → H → ℝ} {ψ : H → ℝ} {M L : ℝ} {N₀ : ℕ} {K₀ : Set H}
    (hc : GHSCore P F γ D f ψ M L N₀ K₀) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) {x : H} (hx : x ∈ K₀)
    {xn yn : ℕ → H} (hxK : ∀ n, xn n ∈ K₀) (hxn : Tendsto xn atTop (𝓝 x))
    (hyn : ∀ n, IsSubgradOn (D (k n)) (f (k n)) (xn n) (yn n)) (h : H) :
    Tendsto (fun n => ⟪yn n - F (xn n), h⟫) atTop (𝓝 0) := by
  have hL0 : 0 ≤ max L 0 := le_max_right _ _
  have hL' : ∀ a b, |ψ a - ψ b| ≤ max L 0 * ‖a - b‖ := fun a b =>
    (hc.hL a b).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h1 := tendsto_inner_plans P hc.hFm (γ ∘ k) (D := D ∘ k) (f := f ∘ k) (fun n => hc.hγΓ (k n))
    (fun n => hc.hγM (k n)) (hc.hlim.comp hk) hc.hF hL' hL0 (hc.hKs hx) (hc.hd x hx) hxn
    (Eventually.of_forall hyn)
    ((hk.eventually_ge_atTop N₀).mono fun n hn => hc.hbd _ hn _ (hxK n) _ (hyn n)) h
  have h2 := tendsto_inner_F (P : Measure H) hc.hF hL' hL0 hc.hψ hc.hKs hc.hd hx hxK hxn h
  have := h1.sub h2
  simp only [sub_self] at this
  refine this.congr fun n => ?_
  rw [inner_sub_left]

/-- **Uniform weak convergence** on `𝒦₀`. -/
theorem GHSCore.eventually_abs_inner_le {P : ProbabilityMeasure H} {F : H → H}
    {γ : ℕ → ProbabilityMeasure (H × H)} {D : ℕ → Set H} {f : ℕ → H → ℝ} {ψ : H → ℝ} {M L : ℝ} {N₀ : ℕ}
    {K₀ : Set H} (hc : GHSCore P F γ D f ψ M L N₀ K₀) (h : H) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K₀, ∀ y, IsSubgradOn (D n) (f n) x y → |⟪y - F x, h⟫| ≤ ε := by
  by_contra hcon
  rw [not_eventually] at hcon
  have hc' : ∃ᶠ n in atTop, ∃ x ∈ K₀, ∃ y, IsSubgradOn (D n) (f n) x y ∧ ε < |⟪y - F x, h⟫| := by
    refine hcon.mono fun n hn => ?_
    push Not at hn
    exact hn
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hc'
  choose xs hxs ys hys hlt using hP
  obtain ⟨x, hx, φ', hφ', hlim⟩ := hc.hK.tendsto_subseq hxs
  have hk : Tendsto (φ ∘ φ') atTop atTop := (hφ.comp hφ').tendsto_atTop
  have ht := hc.tendsto_sub hk hx (fun n => hxs (φ' n)) hlim (yn := fun n => ys (φ' n))
    (fun n => hys (φ' n)) h
  obtain ⟨n, hn⟩ := (ht.eventually (Metric.ball_mem_nhds 0 hε)).exists
  rw [Real.dist_eq, sub_zero] at hn
  exact absurd (hlt (φ' n)) (not_lt.mpr hn.le)

/-- **Norm upgrade** under a common compact range (eventually in `n`). -/
theorem GHSCore.eventually_norm_le {P : ProbabilityMeasure H} {F : H → H}
    {γ : ℕ → ProbabilityMeasure (H × H)} {D : ℕ → Set H} {f : ℕ → H → ℝ} {ψ : H → ℝ} {M L : ℝ} {N₀ : ℕ}
    {K₀ : Set H} (hc : GHSCore P F γ D f ψ M L N₀ K₀) {C : Set H} (hC : IsCompact C)
    (hrange : ∀ n, N₀ ≤ n → ∀ x ∈ K₀, ∀ y, IsSubgradOn (D n) (f n) x y → y ∈ C) (hFC : ∀ x ∈ K₀, F x ∈ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K₀, ∀ y, IsSubgradOn (D n) (f n) x y → ‖y - F x‖ ≤ ε := by
  by_contra hcon
  rw [not_eventually] at hcon
  have hc' : ∃ᶠ n in atTop, N₀ ≤ n ∧ ∃ x ∈ K₀, ∃ y, IsSubgradOn (D n) (f n) x y ∧ ε < ‖y - F x‖ := by
    refine (hcon.and_eventually (eventually_ge_atTop N₀)).mono fun n hn => ⟨hn.2, ?_⟩
    have := hn.1
    push Not at this
    exact this
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hc'
  choose hN xs hxs ys hys hlt using hP
  obtain ⟨x, hx, φ', hφ', hlim⟩ := hc.hK.tendsto_subseq hxs
  set z : ℕ → H := fun n => ys (φ' n) - F (xs (φ' n)) with hz
  have hzC : ∀ n, z n ∈ (fun p : H × H => p.1 - p.2) '' (C ×ˢ C) := fun n =>
    ⟨(ys (φ' n), F (xs (φ' n))), ⟨hrange _ (hN _) _ (hxs _) _ (hys _), hFC _ (hxs _)⟩, rfl⟩
  obtain ⟨z0, -, φ'', hφ'', hzlim⟩ := ((hC.prod hC).image continuous_sub).tendsto_subseq hzC
  have hk : Tendsto (φ ∘ φ') atTop atTop := (hφ.comp hφ').tendsto_atTop
  have hinner : ∀ v, ⟪z0, v⟫ = 0 := by
    intro v
    have ht := hc.tendsto_sub hk hx (fun n => hxs (φ' n)) hlim (yn := fun n => ys (φ' n))
      (fun n => hys (φ' n)) v
    have h1 := ht.comp hφ''.tendsto_atTop
    have h2 : Tendsto (fun n => ⟪z (φ'' n), v⟫) atTop (𝓝 ⟪z0, v⟫) :=
      Filter.Tendsto.inner hzlim tendsto_const_nhds
    exact tendsto_nhds_unique h2 h1
  have hz0 : z0 = 0 := by
    have := hinner z0
    rwa [inner_self_eq_zero] at this
  rw [hz0] at hzlim
  obtain ⟨n, hn⟩ := (hzlim.eventually (Metric.ball_mem_nhds 0 hε)).exists
  rw [dist_zero_right] at hn
  exact absurd (hlt (φ' (φ'' n))) (not_lt.mpr hn.le)

end Seq

end StatFormal.Wave25b
