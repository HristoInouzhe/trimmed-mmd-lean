import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Local-uniform weak convergence of subgradients in a Hilbert space

Library component (untrusted; no `Statements.lean` involved).

An infinite-dimensional substitute for Rockafellar, *Convex Analysis*, Thm 24.5, driven by
**convergence in measure of selections** instead of pointwise convergence of the functions.

Setting: `fₙ : H → ℝ` with uniformly bounded subgradients (`‖y‖ ≤ M` for every subgradient of every
`fₙ`), measurable-free selections `Gₙ` that are `P`-a.e. subgradients of `fₙ`, a limit `ψ` that is
`L`-Lipschitz with a `P`-a.e. subgradient selection `F`, and `Gₙ → F` in `P`-measure. Then at every
point `x ∈ int (supp P)` where `ψ` is Gâteaux differentiable with gradient `F x`,
every sequence of subgradient pairs `(xₙ, yₙ)` of `fₙ` with `xₙ → x` has `⟪yₙ, h⟫ → ⟪F x, h⟫`
(`tendsto_inner_of_subgrad`), and uniformly on strongly compact sets (`eventually_abs_inner_le`);
under a common strongly compact range the convergence is in norm (`eventually_norm_le`).

## Proof (monotonicity, no potentials)

For `t > 0`, `r > 0` small, the ball `B = B(x − t h, r)` has positive `P`-mass. For `n` large the
set where `‖Gₙ − F‖ ≥ δ` has `P`-mass `< P(B)`, so some `x' ∈ B` has `Gₙ(x') ∈ ∂fₙ(x')`,
`F(x') ∈ ∂ψ(x')`, `‖Gₙ(x') − F(x')‖ < δ`. Monotonicity of `∂fₙ` (`⟪yₙ − Gₙ x', xₙ − x'⟫ ≥ 0`), the
subgradient inequality of `ψ` at `x'` toward `x' − t h`, and the Lipschitz bound give
`t⟪yₙ, h⟫ ≥ ψ(x − t h) − ψ(x − 2t h) − 2Lr − tδ‖h‖ − 2M(‖xₙ − x‖ + r)`, and
`(ψ(x − t h) − ψ(x − 2t h))/t → ⟪F x, h⟫` (Gâteaux). Applying this to `±h` gives the limit.
-/

open Set Filter MeasureTheory Metric
open scoped Topology InnerProductSpace RealInnerProductSpace ENNReal

namespace StatFormal.ConvexH

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `y` is a (global) subgradient of `f` at `x`. -/
def Subgrad (f : H → ℝ) (x y : H) : Prop := ∀ z, f x + ⟪y, z - x⟫ ≤ f z

/-- Subgradients of an `L`-Lipschitz function are bounded by `max L 0`. -/
theorem norm_le_of_subgrad {f : H → ℝ} {L : ℝ} (hL : ∀ a b, |f a - f b| ≤ L * ‖a - b‖)
    {x y : H} (hy : Subgrad f x y) : ‖y‖ ≤ max L 0 := by
  have h1 := hy (x + y)
  have h2 := hL (x + y) x
  simp only [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h1 h2
  have h3 := (abs_le.mp h2).2
  rcases (norm_nonneg y).eq_or_lt with h0 | h0
  · rw [← h0]; exact le_max_right _ _
  · have : ‖y‖ ≤ L := by nlinarith
    exact this.trans (le_max_left _ _)

/-- A Gâteaux gradient of a convex function is a subgradient. -/
theorem subgrad_of_hasLineDerivAt {ψ : H → ℝ} (hψ : ConvexOn ℝ univ ψ) {x g : H}
    (hg : ∀ v, HasLineDerivAt ℝ ψ ⟪g, v⟫ x v) : Subgrad ψ x g := by
  intro z
  have hlim := (hg (z - x)).tendsto_slope_zero_right
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (ψ (x + t • (z - x)) - ψ x) ≤ ψ z - ψ x := by
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hc := hψ.2 (mem_univ x) (mem_univ z) (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le
      (by ring : (1 - t) + t = 1)
    have hx : (1 - t) • x + t • z = x + t • (z - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hx, smul_eq_mul] at hc
    simp only [smul_eq_mul] at hc ⊢
    rw [inv_mul_le_iff₀ ht0]
    nlinarith
  have := le_of_tendsto hlim hle
  linarith

/-- The pointwise inequality behind the main theorem. -/
theorem key_ineq {f ψ : H → ℝ} {M L t r δ : ℝ} {x h xn yn x' g Fx' : H}
    (hL : ∀ a b, |ψ a - ψ b| ≤ L * ‖a - b‖) (hL0 : 0 ≤ L) (ht : 0 < t)
    (hyn : Subgrad f xn yn) (hg : Subgrad f x' g) (hF : Subgrad ψ x' Fx')
    (hynM : ‖yn‖ ≤ M) (hgM : ‖g‖ ≤ M) (hδ : ‖g - Fx'‖ ≤ δ) (hx' : ‖x' - (x + (-t) • h)‖ ≤ r) :
    ψ (x + (-t) • h) - ψ (x + (-(2 * t)) • h) - 2 * L * r - t * δ * ‖h‖ - 2 * M * (‖xn - x‖ + r)
      ≤ t * ⟪yn, h⟫ := by
  -- monotonicity
  have m1 := hyn x'
  have m2 := hg xn
  have hmono : ⟪g, xn - x'⟫ ≤ ⟪yn, xn - x'⟫ := by
    have : ⟪yn, x' - xn⟫ = -⟪yn, xn - x'⟫ := by rw [← inner_neg_right, neg_sub]
    linarith
  set w := xn - x' - t • h with hw
  have hw' : ‖w‖ ≤ ‖xn - x‖ + r := by
    have : w = (xn - x) - (x' - (x + (-t) • h)) := by rw [hw, neg_smul]; abel
    rw [this]
    exact (norm_sub_le _ _).trans (by linarith)
  have e1 : ⟪yn, xn - x'⟫ = t * ⟪yn, h⟫ + ⟪yn, w⟫ := by
    rw [hw]; simp only [inner_sub_right, real_inner_smul_right]; ring
  have e2 : ⟪g, xn - x'⟫ = t * ⟪g, h⟫ + ⟪g, w⟫ := by
    rw [hw]; simp only [inner_sub_right, real_inner_smul_right]; ring
  have b1 : |⟪yn, w⟫| ≤ M * (‖xn - x‖ + r) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul hynM hw' (norm_nonneg _) ((norm_nonneg _).trans hynM))
  have b2 : |⟪g, w⟫| ≤ M * (‖xn - x‖ + r) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul hgM hw' (norm_nonneg _) ((norm_nonneg _).trans hgM))
  -- `g ≈ F x'`
  have b3 : ⟪Fx', h⟫ - δ * ‖h‖ ≤ ⟪g, h⟫ := by
    have : |⟪g - Fx', h⟫| ≤ δ * ‖h‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))
    rw [inner_sub_left] at this
    linarith [(abs_le.mp this).1]
  -- subgradient of `ψ` at `x'` toward `x' − t h`
  have s1 := hF (x' - t • h)
  rw [sub_sub_cancel_left, inner_neg_right, real_inner_smul_right] at s1
  -- Lipschitz comparisons
  have l1 := (abs_le.mp (hL x' (x + (-t) • h))).1
  have l2 := (abs_le.mp (hL (x' - t • h) (x + (-(2 * t)) • h))).2
  have hpt : x' - t • h - (x + (-(2 * t)) • h) = x' - (x + (-t) • h) := by
    simp only [neg_smul, mul_smul, two_smul]; abel
  rw [hpt] at l2
  have hLr := mul_le_mul_of_nonneg_left hx' hL0
  nlinarith [mul_le_mul_of_nonneg_left b3 ht.le, abs_le.mp b1, abs_le.mp b2]

/-- The Gâteaux difference quotient `(ψ(x − t h) − ψ(x − 2t h))/t → ⟪F x, h⟫` as `t → 0⁺`. -/
theorem tendsto_twoPoint {ψ : H → ℝ} {x h : H} {c : ℝ} (hd : HasLineDerivAt ℝ ψ c x h) :
    Tendsto (fun t : ℝ => (ψ (x + (-t) • h) - ψ (x + (-(2 * t)) • h)) / t) (𝓝[>] 0) (𝓝 c) := by
  have hS := hd.tendsto_slope_zero
  have hneg : ∀ a : ℝ, 0 < a → Tendsto (fun t : ℝ => -(a * t)) (𝓝[>] 0) (𝓝[≠] 0) := by
    intro a ha
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ => -(a * t)) (𝓝 0) (𝓝 (-(a * 0))) :=
        ((continuous_const.mul continuous_id).neg).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      simp only [mem_compl_iff, mem_singleton_iff, neg_eq_zero]
      exact (mul_pos ha ht).ne'
  have h1 := hS.comp (hneg 1 one_pos)
  have h2 := hS.comp (hneg 2 two_pos)
  have hlim := (h2.const_mul 2).sub h1
  have hc : 2 * c - c = c := by ring
  rw [hc] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  simp only [Function.comp, smul_eq_mul, one_mul]
  field_simp
  ring

/-- **Lower bound.** Along subgradient pairs `(xₙ, yₙ)` of `fₙ` with `xₙ → x`,
eventually `⟪F x, h⟫ − 4ε ≤ ⟪yₙ, h⟫`. -/
theorem eventually_le_inner [MeasurableSpace H] (P : Measure H) {f : ℕ → H → ℝ} {G : ℕ → H → H}
    {ψ : H → ℝ} {F : H → H} {M L : ℝ}
    (hM : ∀ n x y, Subgrad (f n) x y → ‖y‖ ≤ M)
    (hG : ∀ n, ∀ᵐ x ∂P, Subgrad (f n) x (G n x)) (hF : ∀ᵐ x ∂P, Subgrad ψ x (F x))
    (hL : ∀ a b, |ψ a - ψ b| ≤ L * ‖a - b‖) (hL0 : 0 ≤ L)
    (hconv : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {x | δ ≤ ‖G n x - F x‖}) atTop (𝓝 0))
    {x h : H} (hx : x ∈ interior P.support) (hd : HasLineDerivAt ℝ ψ ⟪F x, h⟫ x h)
    {xn yn : ℕ → H} (hxn : Tendsto xn atTop (𝓝 x)) (hyn : ∀ n, Subgrad (f n) (xn n) (yn n))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n in atTop, ⟪F x, h⟫ - 4 * ε ≤ ⟪yn n, h⟫ := by
  set c := ⟪F x, h⟫ with hcdef
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 _ _ (hyn 0))
  -- choose `t`
  have hsupp : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + (-t) • h ∈ P.support := by
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
    rw [hr, mul_div_assoc']
    rw [div_le_iff₀ hden]
    nlinarith [mul_pos hε ht0']
  have hB : 0 < P (ball a r) := (Measure.mem_support_iff_forall a).1 hta _ (ball_mem_nhds a hr0)
  set δ := ε / (‖h‖ + 1) with hδdef
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  have hδh : δ * ‖h‖ ≤ ε := by
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg h]
  filter_upwards [hxn.eventually (Metric.ball_mem_nhds x hr0),
    (hconv δ hδ0).eventually (gt_mem_nhds hB)] with n hn hbad
  -- a good point of the ball
  obtain ⟨x', hx'B, hx'G, hx'F, hx'δ⟩ : ∃ x' ∈ ball a r, Subgrad (f n) x' (G n x') ∧
      Subgrad ψ x' (F x') ∧ ¬ δ ≤ ‖G n x' - F x'‖ := by
    by_contra hcon
    push Not at hcon
    have hsub : ball a r ⊆ {y | ¬ Subgrad (f n) y (G n y)} ∪ {y | ¬ Subgrad ψ y (F y)} ∪
        {y | δ ≤ ‖G n y - F y‖} := by
      intro y hy
      by_cases h1 : Subgrad (f n) y (G n y)
      · by_cases h2 : Subgrad ψ y (F y)
        · exact Or.inr (hcon y hy h1 h2)
        · exact Or.inl (Or.inr h2)
      · exact Or.inl (Or.inl h1)
    have h0G : P {y | ¬ Subgrad (f n) y (G n y)} = 0 := ae_iff.mp (hG n)
    have h0F : P {y | ¬ Subgrad ψ y (F y)} = 0 := ae_iff.mp hF
    have := (measure_mono (μ := P) hsub).trans ((measure_union_le (μ := P) _ _).trans
      (add_le_add_left (measure_union_le (μ := P) _ _) _))
    rw [h0G, h0F, zero_add, zero_add] at this
    exact absurd hbad (not_lt.mpr this)
  have hx'r : ‖x' - a‖ ≤ r := by rw [← dist_eq_norm]; exact (mem_ball.mp hx'B).le
  have hk := key_ineq (f := f n) hL hL0 ht0' (hyn n) hx'G hx'F (hM _ _ _ (hyn n))
    (hM _ _ _ hx'G) (not_le.mp hx'δ).le hx'r
  have hxr : ‖xn n - x‖ ≤ r := by rw [← dist_eq_norm]; exact (mem_ball.mp hn).le
  have hDt : |(ψ a - ψ (x + (-(2 * t)) • h)) / t - c| < ε := by
    have := mem_ball.mp htD; rwa [Real.dist_eq] at this
  have hA : t * ((ψ a - ψ (x + (-(2 * t)) • h)) / t) = ψ a - ψ (x + (-(2 * t)) • h) := by
    field_simp
  have h1 := (abs_lt.mp hDt).1
  have h2 : t * (c - ε) ≤ ψ a - ψ (x + (-(2 * t)) • h) := by
    rw [← hA]; exact mul_le_mul_of_nonneg_left (by linarith) ht0'.le
  have h3 : t * δ * ‖h‖ ≤ t * ε := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hδh ht0'.le
  have h4 : M * ‖xn n - x‖ ≤ M * r := mul_le_mul_of_nonneg_left hxr hM0
  have h5 : t * (c - 4 * ε) ≤ t * ⟪yn n, h⟫ := by nlinarith
  exact le_of_mul_le_mul_left h5 ht0'

/-- **Sequential form (infinite-dimensional Rockafellar 24.5, weak).** -/
theorem tendsto_inner_of_subgrad [MeasurableSpace H] (P : Measure H) {f : ℕ → H → ℝ}
    {G : ℕ → H → H} {ψ : H → ℝ} {F : H → H} {M L : ℝ}
    (hM : ∀ n x y, Subgrad (f n) x y → ‖y‖ ≤ M)
    (hG : ∀ n, ∀ᵐ x ∂P, Subgrad (f n) x (G n x)) (hF : ∀ᵐ x ∂P, Subgrad ψ x (F x))
    (hL : ∀ a b, |ψ a - ψ b| ≤ L * ‖a - b‖) (hL0 : 0 ≤ L)
    (hconv : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {x | δ ≤ ‖G n x - F x‖}) atTop (𝓝 0))
    {x : H} (hx : x ∈ interior P.support) (hd : ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v)
    {xn yn : ℕ → H} (hxn : Tendsto xn atTop (𝓝 x)) (hyn : ∀ n, Subgrad (f n) (xn n) (yn n))
    (h : H) : Tendsto (fun n => ⟪yn n, h⟫) atTop (𝓝 ⟪F x, h⟫) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    have hε : 0 < (⟪F x, h⟫ - b) / 8 := by linarith
    filter_upwards [eventually_le_inner P hM hG hF hL hL0 hconv hx (hd h) hxn hyn hε] with n hn
    linarith
  · intro b hb
    have hε : 0 < (b - ⟪F x, h⟫) / 8 := by linarith
    filter_upwards [eventually_le_inner P hM hG hF hL hL0 hconv hx (hd (-h)) hxn hyn hε] with n hn
    rw [inner_neg_right, inner_neg_right] at hn
    linarith

/-- Differences along a reindexed sequence: for `xₙ → x ∈ K₀` (all `xₙ ∈ K₀`), `k → ∞` and
`yₙ ∈ ∂f_{k n}(xₙ)`, `⟪yₙ − F xₙ, h⟫ → 0`. -/
theorem tendsto_inner_sub [MeasurableSpace H] (P : Measure H) {f : ℕ → H → ℝ}
    {G : ℕ → H → H} {ψ : H → ℝ} {F : H → H} {M L : ℝ}
    (hM : ∀ n x y, Subgrad (f n) x y → ‖y‖ ≤ M)
    (hG : ∀ n, ∀ᵐ x ∂P, Subgrad (f n) x (G n x)) (hF : ∀ᵐ x ∂P, Subgrad ψ x (F x))
    (hL : ∀ a b, |ψ a - ψ b| ≤ L * ‖a - b‖) (hL0 : 0 ≤ L) (hψ : ConvexOn ℝ univ ψ)
    (hconv : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {x | δ ≤ ‖G n x - F x‖}) atTop (𝓝 0))
    {K₀ : Set H} (hKs : K₀ ⊆ interior P.support)
    (hd : ∀ x ∈ K₀, ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) {x : H} (hx : x ∈ K₀)
    {xn yn : ℕ → H} (hxK : ∀ n, xn n ∈ K₀) (hxn : Tendsto xn atTop (𝓝 x))
    (hyn : ∀ n, Subgrad (f (k n)) (xn n) (yn n)) (h : H) :
    Tendsto (fun n => ⟪yn n - F (xn n), h⟫) atTop (𝓝 0) := by
  have h1 := tendsto_inner_of_subgrad P (f := fun n => f (k n)) (G := fun n => G (k n))
    (fun n => hM (k n)) (fun n => hG (k n)) hF hL hL0 (fun δ hδ => (hconv δ hδ).comp hk)
    (hKs hx) (hd x hx) hxn hyn h
  have hconst : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun _ : ℕ => P {y | δ ≤ ‖F y - F y‖}) atTop (𝓝 0) := by
    intro δ hδ
    have : {y | δ ≤ ‖F y - F y‖} = (∅ : Set H) := by
      ext y; simp [not_le.mpr hδ]
    simp only [this, measure_empty]
    exact tendsto_const_nhds
  have h2 := tendsto_inner_of_subgrad P (f := fun _ => ψ) (G := fun _ => F)
    (fun _ _ _ hy => norm_le_of_subgrad hL hy) (fun _ => hF) hF hL hL0 hconst
    (hKs hx) (hd x hx) hxn (yn := fun n => F (xn n))
    (fun n => subgrad_of_hasLineDerivAt hψ (hd _ (hxK n))) h
  have := h1.sub h2
  simp only [sub_self] at this
  refine this.congr fun n => ?_
  rw [inner_sub_left]

/-- **Local-uniform weak convergence** on a strongly compact `K₀ ⊆ int (supp P)` of Gâteaux points:
`sup {|⟪y − F x, h⟫| : x ∈ K₀, y ∈ ∂fₙ(x)} → 0`, written without `sSup`. -/
theorem eventually_abs_inner_le [MeasurableSpace H] (P : Measure H) {f : ℕ → H → ℝ}
    {G : ℕ → H → H} {ψ : H → ℝ} {F : H → H} {M L : ℝ}
    (hM : ∀ n x y, Subgrad (f n) x y → ‖y‖ ≤ M)
    (hG : ∀ n, ∀ᵐ x ∂P, Subgrad (f n) x (G n x)) (hF : ∀ᵐ x ∂P, Subgrad ψ x (F x))
    (hL : ∀ a b, |ψ a - ψ b| ≤ L * ‖a - b‖) (hL0 : 0 ≤ L) (hψ : ConvexOn ℝ univ ψ)
    (hconv : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {x | δ ≤ ‖G n x - F x‖}) atTop (𝓝 0))
    {K₀ : Set H} (hK : IsCompact K₀) (hKs : K₀ ⊆ interior P.support)
    (hd : ∀ x ∈ K₀, ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v) (h : H) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K₀, ∀ y, Subgrad (f n) x y → |⟪y - F x, h⟫| ≤ ε := by
  by_contra hc
  rw [not_eventually] at hc
  have hc' : ∃ᶠ n in atTop, ∃ x ∈ K₀, ∃ y, Subgrad (f n) x y ∧ ε < |⟪y - F x, h⟫| := by
    refine hc.mono fun n hn => ?_
    push Not at hn
    exact hn
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hc'
  choose xs hxs ys hys hlt using hP
  obtain ⟨x, hx, φ', hφ', hlim⟩ := hK.tendsto_subseq hxs
  have hk : Tendsto (φ ∘ φ') atTop atTop := (hφ.comp hφ').tendsto_atTop
  have ht := tendsto_inner_sub P hM hG hF hL hL0 hψ hconv hKs hd hk hx (fun n => hxs (φ' n))
    hlim (yn := fun n => ys (φ' n)) (fun n => hys (φ' n)) h
  obtain ⟨n, hn⟩ := (ht.eventually (Metric.ball_mem_nhds 0 hε)).exists
  rw [Real.dist_eq, sub_zero] at hn
  exact absurd (hlt (φ' n)) (not_lt.mpr hn.le)

/-- **Norm upgrade** under a common strongly compact range (`eq:common-compact-range`):
`sup {‖y − F x‖ : x ∈ K₀, y ∈ ∂fₙ(x)} → 0`. -/
theorem eventually_norm_le [MeasurableSpace H] (P : Measure H) {f : ℕ → H → ℝ}
    {G : ℕ → H → H} {ψ : H → ℝ} {F : H → H} {M L : ℝ}
    (hM : ∀ n x y, Subgrad (f n) x y → ‖y‖ ≤ M)
    (hG : ∀ n, ∀ᵐ x ∂P, Subgrad (f n) x (G n x)) (hF : ∀ᵐ x ∂P, Subgrad ψ x (F x))
    (hL : ∀ a b, |ψ a - ψ b| ≤ L * ‖a - b‖) (hL0 : 0 ≤ L) (hψ : ConvexOn ℝ univ ψ)
    (hconv : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {x | δ ≤ ‖G n x - F x‖}) atTop (𝓝 0))
    {K₀ : Set H} (hK : IsCompact K₀) (hKs : K₀ ⊆ interior P.support)
    (hd : ∀ x ∈ K₀, ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v)
    {C : Set H} (hC : IsCompact C) (hrange : ∀ n x y, x ∈ K₀ → Subgrad (f n) x y → y ∈ C)
    (hFC : ∀ x ∈ K₀, F x ∈ C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K₀, ∀ y, Subgrad (f n) x y → ‖y - F x‖ ≤ ε := by
  by_contra hc
  rw [not_eventually] at hc
  have hc' : ∃ᶠ n in atTop, ∃ x ∈ K₀, ∃ y, Subgrad (f n) x y ∧ ε < ‖y - F x‖ := by
    refine hc.mono fun n hn => ?_
    push Not at hn
    exact hn
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hc'
  choose xs hxs ys hys hlt using hP
  obtain ⟨x, hx, φ', hφ', hlim⟩ := hK.tendsto_subseq hxs
  set z : ℕ → H := fun n => ys (φ' n) - F (xs (φ' n)) with hz
  have hzC : ∀ n, z n ∈ (fun p : H × H => p.1 - p.2) '' (C ×ˢ C) := fun n =>
    ⟨(ys (φ' n), F (xs (φ' n))), ⟨hrange _ _ _ (hxs _) (hys _), hFC _ (hxs _)⟩, rfl⟩
  obtain ⟨z0, -, φ'', hφ'', hzlim⟩ :=
    ((hC.prod hC).image continuous_sub).tendsto_subseq hzC
  have hk : Tendsto (φ ∘ φ') atTop atTop := (hφ.comp hφ').tendsto_atTop
  have hinner : ∀ v, ⟪z0, v⟫ = 0 := by
    intro v
    have ht := tendsto_inner_sub P hM hG hF hL hL0 hψ hconv hKs hd hk hx (fun n => hxs (φ' n))
      hlim (yn := fun n => ys (φ' n)) (fun n => hys (φ' n)) v
    have h1 := ht.comp hφ''.tendsto_atTop
    have h2 : Tendsto (fun n => ⟪z (φ'' n), v⟫) atTop (𝓝 ⟪z0, v⟫) :=
      (Filter.Tendsto.inner hzlim tendsto_const_nhds)
    exact tendsto_nhds_unique h2 h1
  have hz0 : z0 = 0 := by
    have := hinner z0
    rwa [inner_self_eq_zero] at this
  rw [hz0] at hzlim
  obtain ⟨n, hn⟩ := (hzlim.eventually (Metric.ball_mem_nhds 0 hε)).exists
  rw [dist_zero_right] at hn
  exact absurd (hlt (φ' (φ'' n))) (not_lt.mpr hn.le)

omit [InnerProductSpace ℝ H] in
/-- Markov: `L²(P)` convergence `∫ ‖Gₙ − F‖² → 0` gives convergence in `P`-measure. -/
theorem tendsto_meas_of_lintegral_sq [MeasurableSpace H] {P : Measure H} {G : ℕ → H → H}
    {F : H → H} (hmeas : ∀ n, AEMeasurable (fun x => ‖G n x - F x‖ₑ ^ 2) P)
    (h : Tendsto (fun n => ∫⁻ x, ‖G n x - F x‖ₑ ^ 2 ∂P) atTop (𝓝 0)) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {x | δ ≤ ‖G n x - F x‖}) atTop (𝓝 0) := by
  intro δ hδ
  have hc : ENNReal.ofReal (δ ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hbd : ∀ n, P {x | δ ≤ ‖G n x - F x‖} ≤
      (∫⁻ x, ‖G n x - F x‖ₑ ^ 2 ∂P) / ENNReal.ofReal (δ ^ 2) := by
    intro n
    refine (measure_mono ?_).trans (meas_ge_le_lintegral_div (hmeas n) hc ENNReal.ofReal_ne_top)
    intro x (hx : δ ≤ ‖G n x - F x‖)
    show ENNReal.ofReal (δ ^ 2) ≤ ‖G n x - F x‖ₑ ^ 2
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hδ.le hx 2)
  have h0 : Tendsto (fun n => (∫⁻ x, ‖G n x - F x‖ₑ ^ 2 ∂P) / ENNReal.ofReal (δ ^ 2)) atTop
      (𝓝 0) := by
    have := ENNReal.Tendsto.div_const h (Or.inr hc)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun n => zero_le) hbd

end StatFormal.ConvexH
