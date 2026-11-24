import StatFormal.Wave31tr.Statements
import StatFormal.Wave31tq.Statements
import StatFormal.Wave31tl.Statements
import StatFormal.Wave31to.Statements
import StatFormal.Wave31tn.Statements
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Basic.Real.ENatENNReal
import Mathlib.Probability.Distributions.Gaussian.Real

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31tu: the near-parametric rate with the Laplace kernel (trimmed-mmd, Annals of Statistics version)

Printed source: `~/projects/tmmd-aos-brief/fullstack/NEW_STATEMENTS_31tu.md` (v3.2: v3, F1 at trimmed-mmd `b3125cf`, re-hashed at `1fbc8df`,
with the critic's text note c1 applied; copy in `certify/sources/tmmd-aos-NEW_STATEMENTS-wave31tu.md`). Paper: trimmed-mmd `aos/` at
`1fbc8df` (line numbers of that commit; printed numbers of `aos/main.aux`, `aos/supplement.aux`). Plan: `PLAN_31tu.md`. Composed on the
certified waves (30tz, 30tq, 30tv, 31ti, 31tl, 31tn, 31to, 31tp) and on the frozen waves 31tq (`absPQ`, `IsCross`, `ExpTail`) and 31tr
(`IsPaperRun`, `IsGenuineQuantileRule`, `lowQ`, `highQ`), imported, not copied; no textbook bridge.

Claim list (draft numbers Y1–Y26; 40 claims):
classical library (block L): `banach_indicatrix_le`, `banach_indicatrix` (Y1, Banach's indicatrix theorem), `layer_cake01` (Y2),
`laplace_h1`, `laplace_h1_char` (Y3, the `H¹` form of the Laplace RKHS and eq:laphone), `lap_intervals` (Y4, Lemma S4.23), `lap_bv` (Y5,
Lemma S4.24);
the proof section §S4.12 (block P): `lap_err` (Y6, eq:laperr), `lap_const` (Y7), `condR_facts` (Y8, eq:condR), `lap_ratio` (Y9, Lemma S4.20),
`lap_clip` (Y10, Lemma S4.21), `lap_pop` (Y11, eq:lappop), `lap_compare` (Y12, Lemma S4.22), `lap_dev` (Y13, Lemma S4.25), `own_ramp`,
`lap_own` (Y14, Lemma S4.26), `lap_fitted`, `lap_fitted_fraction` (Y15, Proposition S4.27), `lap_bets` (Y16), `lap_rescale` (Y17);
the theorems: `laplace_const_i`, `laplace_const_ii` (Y18 (G)), `laplace_const_pr_i`, `laplace_const_pr_ii` (Y18 (Pr), Theorem S4.19),
`laplace_rate_i`, `laplace_rate_ii`, `laplace_rate_improves` (Y19, Theorem 5.11 and §5 :240-243);
the local lower bound and the readings: `lap_local`, `lap_local_Q`, `lap_local_c`, `lap_local_d`, `lower2pt_not_cross` (Y20, Lemma S4.28),
`local_rate` (Y21), `laplace_rate_grid` (Y22), `sims_condR` (Y23), `genuine_paperrun`, `genuine_run_exists` (Y24, the paper's run);
block R: `newrates_ii_exp` (Y25, Proposition S4.8(ii)), `newrates_iii_gauss` (Y26, Proposition S4.8(iii)).

Encodings (declared; details in the source's §A and §F): the Laplace kernel `e^{−|x−y|/σ}` as a feature map `φ : ℝ → H` into a complete
separable real inner-product space with that Gram function (`IsLaplaceFeature`); the printed lemmas of §S4.12 at `σ = 1` where printed so
(Y13, Y15), scale-free lemmas for every `σ`, the theorems for every `σ` (D1); "the hypotheses of Proposition 5.5" are 31tq's
`IsCross P Q p q x₀ ℓ₀ ∧ 0 < p x₀ ∧ ExpTail P Q x₀`; functions of the RKHS as `wit φ g` for every representer `g` (D4); genuine-quantile cut
points plain or own-term, the choice free per level and batch (`GenuineCuts`, D2); the run of Theorem S4.19 is `IsGenuineRun ∧
IsDefaultRun` (the frozen `IsWitnessRun` with genuine-quantile cuts); "`C` depends only on …" both as the uniform form (G) and, under the
printed hypotheses, with `∃ C` before the feature space and map (Pr) (D3, B1); "with the pooled points pairwise distinct" as "no `X` equals a
`Y`" (D14); intervals as `OrdConnected` sets (D10); "with probability at least `1 − p`" = a measurable event of probability `≥ ofReal(1 − p)`
inside the claimed set; "for samples of comparable size" as `n∨m ≤ (n∧m)^k` (D15).
Junk values: every `rpow` base is `≥ 0` where read; negative exponents only at positive bases; divisions by quantities proved or assumed
positive in the read range (`κ₀, c_V`, `n′∧m′ ≥ 1`, `qpVal > 0`, `ĝ > 0`, `P(A₁), P(B₁) > 0`); `ordStat` only at ranks in `[1, n′]`;
`oscFn` only of bounded functions; `log(n∧m)` in Y25/Y26 only for `n∧m ≥ n₀` chosen by the prover; `Measure.map` only of continuous maps;
`ENNReal.ofReal` of a negative number is `0` (a true, weaker bound).

FROZEN 2026-11-23 after the independent critic's reviews (`CRITIC_31tu.md` NOT READY, B1–B3 applied; `CRITIC_31tu_v2.md` READY TO FREEZE;
coordinated F1 `CRITIC_F1_b3125cf.md` READY TO FREEZE; diff-only re-check `CRITIC_F1b_1fbc8df.md` READY TO FREEZE, text note c1 applied
before hashing). Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu

open StatFormal StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.Wave30tp StatFormal.Wave31tl
  StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.Wave31tq

/-! ### New definitions of Wave31tu -/

section Defs

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Laplace Gram function: `⟪φ x, φ y⟫ = e^{−|x−y|/σ}`. -/
def IsLaplaceFeature (σ : ℝ) (φ : ℝ → H) : Prop := ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)

/-- `ExpTail` with its constant named. -/
def ExpTailWith (P Q : Measure ℝ) [IsFiniteMeasure P] [IsFiniteMeasure Q] (x₀ C' : ℝ) : Prop :=
  0 < C' ∧ ∀ t : ℝ, 0 < t → absPQ P Q {x | t < |x - x₀|} ≤ ENNReal.ofReal (C' * Real.exp (-t / C'))

/-- Theorem 5.11 (ii): `(P+Q)({|x − x₀| > t}) ≤ C′e^{−t/C′}`. -/
def SumTail (P Q : Measure ℝ) (x₀ C' : ℝ) : Prop :=
  0 < C' ∧ ∀ t : ℝ, 0 < t → (P + Q) {x | t < |x - x₀|} ≤ ENNReal.ofReal (C' * Real.exp (-t / C'))

/-- `eq:condR`: `|p − q| ≥ c⋆ min(r⋆, |x − x₀|)(p + q)` a.e., `r⋆ ∈ (0,1]` (`rs`), `c⋆ > 0` (`cs`). -/
def CondR (p q : ℝ → ℝ) (x₀ rs cs : ℝ) : Prop :=
  0 < rs ∧ rs ≤ 1 ∧ 0 < cs ∧ ∀ᵐ x ∂volume, cs * min rs |x - x₀| * (p x + q x) ≤ |p x - q x|

/-- The two-sided bound of Proposition 5.5 at `s = 1`: `c₁ε^{5/4} ≤ D_{α⋆−ε} ≤ c₂ε^{5/4}` on `(0, ε₀]`, `0 < c₁ ≤ c₂`, `0 < ε₀ ≤ α⋆`. -/
def TwoSided54 (φ : ℝ → H) (P Q : Measure ℝ) (c₁ c₂ ε₀ : ℝ) : Prop :=
  0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < ε₀ ∧ ε₀ ≤ Distances.tvDist P Q ∧
    ∀ ε ∈ Ioc (0 : ℝ) ε₀, c₁ * ε ^ (5 / 4 : ℝ) ≤ Dpop φ P Q (Distances.tvDist P Q - ε) ∧
      Dpop φ P Q (Distances.tvDist P Q - ε) ≤ c₂ * ε ^ (5 / 4 : ℝ)

/-- `L(f) = ∫ f d(P − Q)`. -/
def linL (P Q : Measure 𝒳) (f : 𝒳 → ℝ) : ℝ := (∫ x, f x ∂P) - ∫ x, f x ∂Q

/-- `err(f) = α⋆ − L(f)` (S4 :1093). -/
def errL (P Q : Measure 𝒳) (f : 𝒳 → ℝ) : ℝ := Distances.tvDist P Q - linL P Q f

/-- `ρ₀ = (1−α⋆)c₁/(2^{5/4}c₂)`. -/
def rho0 (αs c₁ c₂ : ℝ) : ℝ := (1 - αs) * c₁ / (2 ^ (5 / 4 : ℝ) * c₂)
/-- `c_V = (1−α⋆)c₁(ε₀/α⋆)^{5/4}`. -/
def cV (αs c₁ ε₀ : ℝ) : ℝ := (1 - αs) * c₁ * (ε₀ / αs) ^ (5 / 4 : ℝ)
/-- `κ₀ = min{ρ₀, (1−α⋆)c₁(ε₀/2)^{5/4}/(2α⋆)}`. -/
def kappa0 (αs c₁ c₂ ε₀ : ℝ) : ℝ := min (rho0 αs c₁ c₂) ((1 - αs) * c₁ * (ε₀ / 2) ^ (5 / 4 : ℝ) / (2 * αs))

/-- `c_x = 2x + 4`. -/
def cx (c : ℝ) : ℝ := 2 * c + 4

/-- The event of `lem:lapintervals` with parameter `x = c`: every interval `I` has `|P̃(I) − P(I)| ≤ {2P(I)c/n}^{1/2} + c_x/n`. -/
def IntervalEvent (P : Measure ℝ) {n : ℕ} (x : Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ I : Set ℝ, I.OrdConnected → |(empirical x).real I - P.real I| ≤ √(2 * P.real I * c / n) + cx c / n

/-- `s_{n,m} = (x/n)^{1/2} + (x/m)^{1/2}`. -/
def sDev (c : ℝ) (n m : ℕ) : ℝ := √(c / n) + √(c / m)
/-- `r_{n,m} = 1/n + 1/m`. -/
def rDev (n m : ℕ) : ℝ := 1 / (n : ℝ) + 1 / (m : ℝ)
/-- `π_K = (P+Q)({|z − x₀| > K})`. -/
def piK (P Q : Measure ℝ) (x₀ K : ℝ) : ℝ := (P + Q).real {z | K < |z - x₀|}
/-- `a′`, `ϖ′`, `b` of `lem:lapdev` (a). -/
def devA' (P Q : Measure ℝ) (x₀ K c : ℝ) (n m : ℕ) : ℝ := 5 * sDev c n m + 4 * cx c * rDev n m + 2 * piK P Q x₀ K
def devG' (K c : ℝ) (n m : ℕ) : ℝ := 2 * K ^ (1 / 4 : ℝ) * sDev c n m
def devB (K c : ℝ) (n m : ℕ) : ℝ := 6 * K ^ (1 / 2 : ℝ) * cx c * rDev n m
/-- `A₀`, `A₁` of `lem:lapdev` (b). -/
def lapA0 (pbar cs rs : ℝ) : ℝ := 4 + 2 * √(2 * pbar) + 4 * (cs * rs) ^ (-(1 / 2 : ℝ))
def lapA1 (pbar cs rs : ℝ) : ℝ :=
  2 * ((2 * √2 * pbar) ^ (1 / 2 : ℝ) + 2 ^ (1 / 5 : ℝ) * (2 * √2 / (cs * rs)) ^ (1 / 2 : ℝ))
def devA (P Q : Measure ℝ) (x₀ K pbar cs rs c : ℝ) (n m : ℕ) : ℝ :=
  lapA0 pbar cs rs * sDev c n m + 7 * cx c * rDev n m + 2 * piK P Q x₀ K
def devG (pbar cs rs K c : ℝ) (n m : ℕ) : ℝ := lapA1 pbar cs rs * K ^ (1 / 4 : ℝ) * sDev c n m

/-- `ε_fit` of `prop:lapfitted`, case (i). -/
def epsFitI (κ₀ cv a ϖ b : ℝ) (nm : ℕ) : ℝ :=
  max (max (max (max (24 * a / κ₀) (108 * ϖ / (κ₀ * √cv))) ((300 * b / (κ₀ * cv)) ^ (4 / 5 : ℝ)))
    ((2 / cv) ^ (20 / 33 : ℝ) * ϖ ^ (40 / 33 : ℝ))) ((1920 / (κ₀ * cv ^ 2 * nm)) ^ (2 / 3 : ℝ))

/-- `ε_fit` of `prop:lapfitted`, case (ii). -/
def epsFitII (κ₀ cv a' ϖ' b : ℝ) (nm : ℕ) : ℝ :=
  max (max (max (24 * a' / κ₀) ((60 * ϖ' / (κ₀ * √cv)) ^ (8 / 9 : ℝ))) ((156 * b / (κ₀ * cv)) ^ (4 / 5 : ℝ)))
    ((576 / (κ₀ * cv ^ 2 * nm)) ^ (2 / 3 : ℝ))

/-- The fitted witness `f̂(z) = ⟪f̂, φ z⟫`. -/
def fitF (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) (z : 𝒳) : ℝ :=
  ⟪witness φ x y w v, φ z⟫_ℝ
/-- `t̂ = f̂(X)_{(⌈n(1−α)⌉)}`. -/
def tHat (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) (α : ℝ) : ℝ :=
  ordStat (fun i => fitF φ x y w v (x i)) ⌈(n : ℝ) * (1 - α)⌉₊
/-- `û = f̂(Y)_{(⌊mα⌋+1)}`. -/
def uHat (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) (α : ℝ) : ℝ :=
  ordStat (fun j => fitF φ x y w v (y j)) (⌊(m : ℝ) * α⌋₊ + 1)

/-- Genuine-quantile cut points of the fitted witness, plain or own-term (Theorem S4.19). -/
def GenuineCuts (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) (α t u : ℝ) : Prop :=
  (IsEmpQuantile (fun i => fitF φ x y w v (x i)) (1 - α) t ∧ IsEmpQuantile (fun j => fitF φ x y w v (y j)) α u) ∨
    (IsEmpQuantile (ownX φ x y w v) (1 - α) t ∧ IsEmpQuantile (ownY φ x y w v) α u)

/-- The per-level rule of Theorem S4.19: as the frozen `IsWitnessRamp`, with genuine-quantile cut points (plain or own-term) in place of
(cutrank). -/
def IsGenuineRamp (φ : 𝒳 → H) (α : ℝ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (has : Prop) (g : 𝒳 → ℝ) : Prop :=
  (n = 0 ∨ m = 0 → ¬ has) ∧
  (1 ≤ n → 1 ≤ m → ∃ w v, IsQPMin φ α x y w v ∧
    (qpVal φ x y w v = 0 → ¬ has) ∧
    (0 < qpVal φ x y w v → ∃ t u, GenuineCuts φ x y w v α t u ∧ (has ↔ u < t) ∧
      (has → g = ramp (fitF φ x y w v) t u)))

/-- The run of Theorem S4.19: `IsWitnessRun` with `IsGenuineRamp` in place of `IsWitnessRamp`. -/
def IsGenuineRun {J n m : ℕ} (R : LoRun 𝒳 J n m) (φ : 𝒳 → H) (α : Fin J → ℝ) (δ lmax s2 : ℝ) : Prop :=
  R.IsAdmissible α lmax ∧
  (∀ j (k : Fin R.N) x y, IsGenuineRamp φ (α j) (fitSample R.lx (R.bat k) x) (fitSample R.ly (R.bat k) y)
    (R.has j (R.bat k) x y) (R.g j (R.bat k) x y)) ∧
  ∀ j (k : Fin R.N) x y z,
    R.lam j k x y z ≤ lamHi lmax (α j) (Real.log (1 / δ)) s2 R.N ∧
    (R.has j (R.bat k) x y → (∀ l, z l ∈ Icc (-1 : ℝ) 1) →
      lamLo lmax (α j) (Real.log (1 / δ)) s2 R.N ≤ R.lam j k x y z) ∧
    (¬ R.has j (R.bat k) x y → R.lam j k x y z = 0)

end Defs

/-- `H¹` (continuous representative): locally absolutely continuous, `f, f′ ∈ L²`. -/
def IsH1 (f : ℝ → ℝ) : Prop := (∀ a b, AbsolutelyContinuousOnInterval f a b) ∧ MemLp f 2 ∧ MemLp (deriv f) 2

/-- `(1/(2σ)) ∫ (f² + σ² f′²)` in `[0,∞]`. -/
def h1Laplace (σ : ℝ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * σ)) * ∫⁻ x, ENNReal.ofReal (f x ^ 2 + σ ^ 2 * deriv f x ^ 2)

/-- Banach's counting function `N(s) = #{x ∈ [a,b] : h(x) = s}` in `[0,∞]`. -/
def levelCount (h : ℝ → ℝ) (a b s : ℝ) : ℝ≥0∞ := ENat.toENNReal ({x | x ∈ Icc a b ∧ h x = s} : Set ℝ).encard

/-- The density of `P_h` in `lem:laplocal`. -/
def bumpDens (p : ℝ → ℝ) (A B : Set ℝ) (PA PB π hh : ℝ) (z : ℝ) : ℝ :=
  p z * (1 + hh * π / PA * A.indicator (fun _ => (1 : ℝ)) z - hh * π / PB * B.indicator (fun _ => (1 : ℝ)) z)


namespace Claims

/-- Y1(a), S4 :1220-1222 (Banach's indicatrix theorem, the half used by `lem:lapbv`): for `h` continuous on `[a,b]`, the
counting function `N(s) = #{x ∈ [a,b] : h x = s}` is measurable and `∫⁻ N ≤ V_{[a,b]}(h)`. -/
def banach_indicatrix_le : Prop :=
  ∀ (h : ℝ → ℝ) (a b : ℝ), a ≤ b → ContinuousOn h (Icc a b) →
    Measurable (levelCount h a b) ∧ ∫⁻ s, levelCount h a b s ≤ eVariationOn h (Icc a b)

/-- Y1(b), S4 :1220-1222 (Banach's indicatrix theorem, the printed equality): `∫⁻ N(s) ds = V_{[a,b]}(h)`. -/
def banach_indicatrix : Prop :=
  ∀ (h : ℝ → ℝ) (a b : ℝ), a ≤ b → ContinuousOn h (Icc a b) →
    ∫⁻ s, levelCount h a b s = eVariationOn h (Icc a b)

/-- Y2, S4 :1218-1219: the layer cake for `[0,1]`-valued functions, `∫ h dμ = ∫_0^1 μ{h > s} ds`. -/
def layer_cake01 : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (μ : Measure 𝒳) [IsFiniteMeasure μ] (h : 𝒳 → ℝ),
    AEMeasurable h μ → (∀ x, 0 ≤ h x ∧ h x ≤ 1) → ∫ x, h x ∂μ = ∫ s in (0 : ℝ)..1, μ.real {x | s < h x}

/-- Y3 (a), (c), S4 :1039-1048: the `H¹` form of the Laplace RKHS on `ℝ` (`h1Laplace σ (wit φ g) ≤ ‖g‖²`, with equality on the closed
span of `φ(ℝ)`) and `eq:laphone` (`|f| ≤ ‖f‖`, `∫_a^b|f′| ≤ √(2(b−a)/σ)‖f‖`, the variation bound, `f → 0` at infinity, `osc f ≤ 1 ⇒ |f| ≤ 1`). -/
def laplace_h1 : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (σ : ℝ) (φ : ℝ → H),
    0 < σ → IsLaplaceFeature σ φ →
      (∀ g : H, IsH1 (Wave31to.wit φ g) ∧ h1Laplace σ (Wave31to.wit φ g) ≤ ENNReal.ofReal (‖g‖ ^ 2) ∧
        (g ∈ (Submodule.span ℝ (Set.range φ)).topologicalClosure →
          h1Laplace σ (Wave31to.wit φ g) = ENNReal.ofReal (‖g‖ ^ 2))) ∧
      (∀ g : H, (∀ x, |Wave31to.wit φ g x| ≤ ‖g‖) ∧
        (∀ a b : ℝ, a ≤ b → ∫ x in a..b, |deriv (Wave31to.wit φ g) x| ≤ √(2 * (b - a) / σ) * ‖g‖) ∧
        (∀ a b : ℝ, a ≤ b → eVariationOn (Wave31to.wit φ g) (Icc a b) ≤ ENNReal.ofReal (√(2 * (b - a) / σ) * ‖g‖)) ∧
        Tendsto (Wave31to.wit φ g) (cocompact ℝ) (𝓝 0) ∧
        (Wave31to.oscFn (Wave31to.wit φ g) ≤ 1 → ∀ x, |Wave31to.wit φ g x| ≤ 1))

/-- Y3 (b), S4 :1039-1041: the `H¹` identification — every continuous `H¹` function is represented, with least representer norm
`h1Laplace σ f` (printed only; decision D11). -/
def laplace_h1_char : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (σ : ℝ) (φ : ℝ → H),
    0 < σ → IsLaplaceFeature σ φ →
      ∀ f : ℝ → ℝ, Continuous f →
        ((∃ g : H, ∀ x, ⟪g, φ x⟫_ℝ = f x) ↔ IsH1 f) ∧
        (IsH1 f → ∃ g₀ : H, (∀ x, ⟪g₀, φ x⟫_ℝ = f x) ∧ ENNReal.ofReal (‖g₀‖ ^ 2) = h1Laplace σ f ∧
          ∀ g : H, (∀ x, ⟪g, φ x⟫_ℝ = f x) → ‖g₀‖ ≤ ‖g‖)

/-- Y9, `lem:lapratio` (Lemma S4.20, S4 :1075-1086), for every measurable space and bounded feature map. -/
def lap_ratio : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (α : ℝ) (g : H),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → g ≠ 0 → Wave31to.oscFn (Wave31to.wit φ g) ≤ 1 →
      (linL P Q (Wave31to.wit φ g) - α) / ‖g‖ ≤ Wave31ti.uPath φ P Q α ∧
      (Distances.tvDist P Q < 1 → ∀ e ∈ Icc (0 : ℝ) (Distances.tvDist P Q),
        (e - errL P Q (Wave31to.wit φ g)) / ‖g‖ ≤ Wave31ti.uPath φ P Q (Distances.tvDist P Q - e))

/-- Y10, `lem:lapclip` (Lemma S4.21, S4 :1088-1132): the fitted Laplace witness clips itself. -/
def lap_clip : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (σ : ℝ) (φ : ℝ → H) (n m : ℕ) (x : Fin n → ℝ) (y : Fin m → ℝ) (α : ℝ) (w : Fin n → ℝ) (v : Fin m → ℝ),
    0 < σ → IsLaplaceFeature σ φ → 1 ≤ n → 1 ≤ m → (∀ i j, x i ≠ y j) → 0 < α → α < 1 → IsQPMin φ α x y w v →
      let F := fitF φ x y w v
      let t := tHat φ x y w v α
      let u := uHat φ x y w v α
      let D := qpVal φ x y w v
      let φh := (t - u)⁻¹ • witness φ x y w v
      0 < D ∧ D = Demp φ x y α ∧ (∀ z, u ≤ F z ∧ F z ≤ t) ∧ Wave31to.oscFn F = t - u ∧ 0 < t - u ∧
      (∀ r : ℕ, ⌈(n : ℝ) * (1 - α)⌉₊ ≤ r → r ≤ n → ordStat (fun i => F (x i)) r = t) ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ ⌊(m : ℝ) * α⌋₊ + 1 → ordStat (fun j => F (y j)) r = u) ∧
      (∀ q, IsEmpQuantile (fun i => F (x i)) (1 - α) q → q = t) ∧
      (∀ q, IsEmpQuantile (fun j => F (y j)) α q → q = u) ∧
      ramp F t u = (fun z => (F z - u) / (t - u)) ∧
      Wave31to.oscFn (Wave31to.wit φ φh) = 1 ∧ ‖φh‖ = 1 / (t - u) ∧ 1 / 2 ≤ ‖φh‖ ∧
      (∀ g' : H, (∀ z, ⟪g', φ z⟫_ℝ = Wave31to.wit φ φh z) → ‖φh‖ ≤ ‖g'‖) ∧
      linL (empirical x) (empirical y) (Wave31to.wit φ φh) - α = (1 - α) * D * ‖φh‖ ∧
      (∀ g' : H, g' ≠ 0 → Wave31to.oscFn (Wave31to.wit φ g') ≤ 1 →
        (linL (empirical x) (empirical y) (Wave31to.wit φ g') - α) / ‖g'‖ ≤
          (linL (empirical x) (empirical y) (Wave31to.wit φ φh) - α) / ‖φh‖) ∧
      (∀ r : ℕ, ⌈(n : ℝ) * (1 - α)⌉₊ ≤ r → r ≤ n →
        t - 1 / (n * ((1 - α) * D)) ≤ ordStat (ownX φ x y w v) r ∧ ordStat (ownX φ x y w v) r ≤ t) ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ ⌊(m : ℝ) * α⌋₊ + 1 →
        u ≤ ordStat (ownY φ x y w v) r ∧ ordStat (ownY φ x y w v) r ≤ u + 1 / (m * ((1 - α) * D))) ∧
      (∀ q, IsEmpQuantile (ownX φ x y w v) (1 - α) q → t - 1 / (n * ((1 - α) * D)) ≤ q ∧ q ≤ t) ∧
      (∀ q, IsEmpQuantile (ownY φ x y w v) α q → u ≤ q ∧ q ≤ u + 1 / (m * ((1 - α) * D)))

/-- Y4, `lem:lapintervals` (Lemma S4.23, S4 :1188-1205): (a) the event holds with probability `≥ 1 − η′` at
`x = log(2(n+1)²/η′)`; (b) the events weaken as `x` grows (S4 :1351-1352); (c) the pooled points are a.s. pairwise distinct (S4 :1088-1089). -/
def lap_intervals : Prop :=
  (∀ (P : Measure ℝ) [IsProbabilityMeasure P] [NullSingletonClass P] (n : ℕ) (η' : ℝ), 1 ≤ n → 0 < η' → η' < 1 →
    ∃ E : Set (Fin n → ℝ), MeasurableSet E ∧ ENNReal.ofReal (1 - η') ≤ (Measure.pi fun _ : Fin n => P) E ∧
      E ⊆ {x | IntervalEvent P x (Real.log (2 * ((n : ℝ) + 1) ^ 2 / η'))}) ∧
  (∀ (P : Measure ℝ) (n : ℕ) (x : Fin n → ℝ) (c c' : ℝ), 0 ≤ c → c ≤ c' → IntervalEvent P x c → IntervalEvent P x c') ∧
  (∀ (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [NullSingletonClass P] [NullSingletonClass Q]
    (n m : ℕ),
    sampleLaw P Q n m {z | ¬ (Function.Injective z.1 ∧ Function.Injective z.2 ∧ ∀ i j, z.1 i ≠ z.2 j)} = 0)

/-- Y5, `lem:lapbv` (Lemma S4.24, S4 :1207-1225): localized deviation for functions of bounded variation. -/
def lap_bv : Prop :=
  ∀ (P : Measure ℝ) [IsProbabilityMeasure P] (n : ℕ) (x : Fin n → ℝ) (c : ℝ), 1 ≤ n → 0 ≤ c → IntervalEvent P x c →
    ∀ (I : Set ℝ) (h : ℝ → ℝ) (V : ℝ), I.OrdConnected → Bornology.IsBounded I → (∀ z, 0 ≤ h z ∧ h z ≤ 1) →
      ContinuousOn h (closure I) → 0 ≤ V → eVariationOn h (closure I) ≤ ENNReal.ofReal V →
        |(∫ z in I, h z ∂(empirical x)) - ∫ z in I, h z ∂P| ≤
          √(2 * (V + 1) * (∫ z in I, h z ∂P) * c / n) + (V + 1) * cx c / n

/-- Y13, `lem:lapdev` (Lemma S4.25, S4 :1227-1275), at `σ = 1` as printed: (a) without, (b) with condition (5.1). -/
def lap_dev : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : ℝ → H)
    (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n m : ℕ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (x₀ c K : ℝ) (g : H),
    IsLaplaceFeature 1 φ → 1 ≤ n → 1 ≤ m → Real.log 8 ≤ c → IntervalEvent P x c → IntervalEvent Q y c → 1 ≤ K →
    Wave31to.oscFn (Wave31to.wit φ g) ≤ 1 →
      let Δ := linL (empirical x) (empirical y) (Wave31to.wit φ g) - linL P Q (Wave31to.wit φ g)
      let N := max ‖g‖ (1 / 2)
      |Δ| ≤ devA' P Q x₀ K c n m + devG' K c n m * N ^ (1 / 2 : ℝ) + devB K c n m * N ∧
      ∀ (p q : ℝ → ℝ) (ℓ₀ rs cs pbar : ℝ), IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → CondR p q x₀ rs cs →
        (∀ z ∈ Icc (x₀ - rs) (x₀ + rs), p z + q z ≤ pbar) →
          0 < errL P Q (Wave31to.wit φ g) ∧
          |Δ| ≤ devA P Q x₀ K pbar cs rs c n m +
            devG pbar cs rs K c n m * N ^ (1 / 2 : ℝ) * errL P Q (Wave31to.wit φ g) ^ (3 / 10 : ℝ) + devB K c n m * N

/-- Y16, the betting paragraph of the proof of Theorem S4.19 (S4 :1037-1038, :1354-1366): the bets are those of Theorem S4.3. -/
def lap_bets : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h0 ε ϱ : ℝ) (R : LoRun 𝒳 J n m) (E : Set ((Fin n → 𝒳) × (Fin m → 𝒳))),
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < η → η < 1 → 0 < h0 → GapsGe α h0 → 0 < ε → 1 ≤ R.N →
    R.IsAdmissible α (1 / 2) →
    (∀ j (k : Fin R.N) x y z, R.lam j k x y z ≤ lamHi (1 / 2) (α j) (Real.log (1 / δ)) s2 R.N ∧
      (R.has j (R.bat k) x y → (∀ l, z l ∈ Icc (-1 : ℝ) 1) →
        lamLo (1 / 2) (α j) (Real.log (1 / δ)) s2 R.N ≤ R.lam j k x y z)) →
    MeasurableSet E → sampleLaw P Q n m Eᶜ ≤ ENNReal.ofReal (η / 2) →
    Tbet (1 / 2) s2 (Real.log (1 / δ)) η (Jeps J ε h0) R.N ≤ ϱ →
    (∀ z ∈ E, ∀ j, α j ≤ Distances.tvDist P Q - ε → ∀ k : Fin R.N,
      R.has j (R.bat k) z.1 z.2 ∧
        α j + ϱ * ((Distances.tvDist P Q - α j) / ε) ≤ condMean P Q (R.g j) R.bat z.1 z.2 k) →
      sampleLaw P Q n m {z | R.alphaLo α δ z.1 z.2 < gridFloor α (Distances.tvDist P Q - ε)} ≤ ENNReal.ofReal η

/-- Y18 (G), `thm:laplaceconst` (Theorem S4.19) (i), S4 :989-1018: `C` depends only on the printed list. -/
def laplace_const_i : Prop :=
  ∀ (σ αs c₁ c₂ ε₀ C' cs rs pbar : ℝ), 0 < σ → 0 < αs → αs < 1 → 0 < c₁ → c₁ ≤ c₂ → 0 < ε₀ → ε₀ ≤ αs →
    0 < C' → 0 < cs → 0 < rs → rs ≤ 1 → 0 ≤ pbar →
    ∃ C : ℝ, 0 < C ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (φ : ℝ → H) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ)
      (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h : ℝ) (R : LoRun ℝ J n m),
      IsLaplaceFeature σ φ → IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTailWith P Q x₀ C' →
      Distances.tvDist P Q = αs → TwoSided54 φ P Q c₁ c₂ ε₀ → CondR p q x₀ rs cs →
      (∀ z ∈ Icc (x₀ - rs) (x₀ + rs), p z + q z ≤ pbar) →
      IsGrid α → (∀ j, 0 < α j) → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < η → η < 1 →
      IsGenuineRun R φ α δ (1 / 2) s2 → IsDefaultRun R → 10 ≤ min n m → MeshBelowLe α αs h →
        ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
          E ⊆ {z | αs - h - C * ((Real.log ((max n m : ℕ) : ℝ)) ^ (1 / 4 : ℝ) *
                    (Real.log (((max n m : ℕ) : ℝ) / η)) ^ (1 / 2 : ℝ) +
                  s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η)))) / √((min n m : ℕ) : ℝ) ≤
                R.alphaLo α δ z.1 z.2 ∧ R.alphaLo α δ z.1 z.2 ≤ αs}

/-- Y19 (i), `thm:laplacerate` (Theorem 5.11) (i), §5 :293-318, printed `O` form, `∃ C` before `H, φ` (B1). -/
def laplace_rate_i : Prop :=
  ∀ (σ : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ rs cs : ℝ),
    0 < σ → IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ → CondR p q x₀ rs cs →
    ∃ C : ℝ, 0 < C ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (φ : ℝ → H), IsLaplaceFeature σ φ →
      ∀ (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h : ℝ) (R : LoRun ℝ J n m),
      IsGrid α → (∀ j, 0 < α j) → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < η → η < 1 →
      IsGenuineRun R φ α δ (1 / 2) s2 → IsDefaultRun R → 10 ≤ min n m →
      MeshBelowLe α (Distances.tvDist P Q) h →
        ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
          E ⊆ {z | Distances.tvDist P Q - h - C * ((Real.log (((max n m : ℕ) : ℝ) / η)) ^ (3 / 4 : ℝ) / √((min n m : ℕ) : ℝ) +
                  s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) / √((min n m : ℕ) : ℝ)) ≤
                R.alphaLo α δ z.1 z.2 ∧ R.alphaLo α δ z.1 z.2 ≤ Distances.tvDist P Q}

/-- Y20 (a), `lem:laplocal` (Lemma S4.28, S4 :1386-1414), first sample (`p̄` only in a conditional conjunct). -/
def lap_local : Prop :=
  ∀ (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ rs cs r C' δ : ℝ),
    IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTailWith P Q x₀ C' → CondR p q x₀ rs cs → 0 < r → r ≤ rs →
    ContinuousOn p (Icc (x₀ - 2 * r) (x₀ + 2 * r)) → ContinuousOn q (Icc (x₀ - 2 * r) (x₀ + 2 * r)) →
    (∀ z ∈ Icc (x₀ - 2 * r) (x₀ + 2 * r), 0 < p z ∧ 0 < q z) →
    let A₁ := Ioo (x₀ + r) (x₀ + 2 * r)
    let B₁ := Ioo (x₀ - 2 * r) (x₀ - r)
    let πh := min (P.real A₁) (P.real B₁)
    0 < πh ∧ ∀ hh ∈ Icc (0 : ℝ) 1,
      let ph := bumpDens p A₁ B₁ (P.real A₁) (P.real B₁) πh hh
      let Ph := volume.withDensity (fun z => ENNReal.ofReal (ph z))
      (∀ z, 0 ≤ ph z) ∧
      (∀ S : Set ℝ, MeasurableSet S →
        Ph.real S = P.real S + hh * πh * (P.real (S ∩ A₁) / P.real A₁ - P.real (S ∩ B₁) / P.real B₁)) ∧
      ∃ _ : IsProbabilityMeasure Ph,
        Distances.tvDist Ph Q = Distances.tvDist P Q + hh * πh ∧ Distances.tvDist Ph P = hh * πh ∧
        IsCross Ph Q ph q x₀ ℓ₀ ∧ 0 < ph x₀ ∧ ExpTailWith Ph Q x₀ (C' + 2 * r + 2 * Real.exp 1) ∧
        CondR ph q x₀ rs (cs / 2) ∧
        (∀ pbar : ℝ, (∀ z ∈ Icc (x₀ - rs) (x₀ + rs), p z + q z ≤ pbar) →
          ∀ z ∈ Icc (x₀ - rs) (x₀ + rs), ph z + q z ≤ 2 * pbar) ∧
        ∀ (n m : ℕ) (Ξ : Type) [MeasurableSpace Ξ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
          (T : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ),
          Measurable T → ((sampleLaw P Q n m).prod ρ).real {z | Distances.tvDist P Q < T z} ≤ δ →
            1 - δ - hh * √(n * πh) ≤
              ((sampleLaw Ph Q n m).prod ρ).real {z | hh * πh ≤ Distances.tvDist Ph Q - T z}

/-- Y20 (b), `lem:laplocal`: the second sample (`Q` moved from `A₁` to `B₁`, `m`, `π′`). -/
def lap_local_Q : Prop :=
  ∀ (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ rs cs r C' δ : ℝ),
    IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTailWith P Q x₀ C' → CondR p q x₀ rs cs → 0 < r → r ≤ rs →
    ContinuousOn p (Icc (x₀ - 2 * r) (x₀ + 2 * r)) → ContinuousOn q (Icc (x₀ - 2 * r) (x₀ + 2 * r)) →
    (∀ z ∈ Icc (x₀ - 2 * r) (x₀ + 2 * r), 0 < p z ∧ 0 < q z) →
    let A₁ := Ioo (x₀ + r) (x₀ + 2 * r)
    let B₁ := Ioo (x₀ - 2 * r) (x₀ - r)
    let πq := min (Q.real A₁) (Q.real B₁)
    0 < πq ∧ ∀ hh ∈ Icc (0 : ℝ) 1,
      let qh := bumpDens q B₁ A₁ (Q.real B₁) (Q.real A₁) πq hh
      let Qh := volume.withDensity (fun z => ENNReal.ofReal (qh z))
      (∀ z, 0 ≤ qh z) ∧
      (∀ S : Set ℝ, MeasurableSet S →
        Qh.real S = Q.real S + hh * πq * (Q.real (S ∩ B₁) / Q.real B₁ - Q.real (S ∩ A₁) / Q.real A₁)) ∧
      ∃ _ : IsProbabilityMeasure Qh,
        Distances.tvDist P Qh = Distances.tvDist P Q + hh * πq ∧ Distances.tvDist Qh Q = hh * πq ∧
        IsCross P Qh p qh x₀ ℓ₀ ∧ ExpTailWith P Qh x₀ (C' + 2 * r + 2 * Real.exp 1) ∧ CondR p qh x₀ rs (cs / 2) ∧
        (∀ pbar : ℝ, (∀ z ∈ Icc (x₀ - rs) (x₀ + rs), p z + q z ≤ pbar) →
          ∀ z ∈ Icc (x₀ - rs) (x₀ + rs), p z + qh z ≤ 2 * pbar) ∧
        ∀ (n m : ℕ) (Ξ : Type) [MeasurableSpace Ξ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
          (T : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ),
          Measurable T → ((sampleLaw P Q n m).prod ρ).real {z | Distances.tvDist P Q < T z} ≤ δ →
            1 - δ - hh * √(m * πq) ≤
              ((sampleLaw P Qh n m).prod ρ).real {z | hh * πq ≤ Distances.tvDist P Qh - T z}

/-- Y20 (c), S4 :1416-1417: the choice `h = (1−δ)/(2(nπ)^{1/2})`. -/
def lap_local_c : Prop :=
  ∀ (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ rs cs r C' δ : ℝ),
    IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTailWith P Q x₀ C' → CondR p q x₀ rs cs → 0 < r → r ≤ rs →
    ContinuousOn p (Icc (x₀ - 2 * r) (x₀ + 2 * r)) → ContinuousOn q (Icc (x₀ - 2 * r) (x₀ + 2 * r)) →
    (∀ z ∈ Icc (x₀ - 2 * r) (x₀ + 2 * r), 0 < p z ∧ 0 < q z) → 0 ≤ δ → δ < 1 →
    let A₁ := Ioo (x₀ + r) (x₀ + 2 * r)
    let B₁ := Ioo (x₀ - 2 * r) (x₀ - r)
    let πh := min (P.real A₁) (P.real B₁)
    ∀ (n m : ℕ), 1 / 4 ≤ n * πh →
      let hh := (1 - δ) / (2 * √(n * πh))
      let Ph := volume.withDensity (fun z => ENNReal.ofReal (bumpDens p A₁ B₁ (P.real A₁) (P.real B₁) πh hh z))
      hh ∈ Icc (0 : ℝ) 1 ∧
      ∀ (Ξ : Type) [MeasurableSpace Ξ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ] (T : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ),
        Measurable T → ((sampleLaw P Q n m).prod ρ).real {z | Distances.tvDist P Q < T z} ≤ δ →
          (1 - δ) / 2 ≤ ((sampleLaw Ph Q n m).prod ρ).real
            {z | (1 - δ) / 2 * √(πh / n) ≤ Distances.tvDist Ph Q - T z}

/-- Y20 (d), S4 :1417-1418: "The constants of Proposition 5.5 for `(P_h,Q)` exist" (constants before `H, φ`). -/
def lap_local_d : Prop :=
  ∀ (σ : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ rs cs r C' : ℝ),
    0 < σ → IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTailWith P Q x₀ C' → CondR p q x₀ rs cs → 0 < r → r ≤ rs →
    ContinuousOn p (Icc (x₀ - 2 * r) (x₀ + 2 * r)) → ContinuousOn q (Icc (x₀ - 2 * r) (x₀ + 2 * r)) →
    (∀ z ∈ Icc (x₀ - 2 * r) (x₀ + 2 * r), 0 < p z ∧ 0 < q z) →
    let A₁ := Ioo (x₀ + r) (x₀ + 2 * r)
    let B₁ := Ioo (x₀ - 2 * r) (x₀ - r)
    let πh := min (P.real A₁) (P.real B₁)
    ∀ hh ∈ Icc (0 : ℝ) 1,
      let Ph := volume.withDensity (fun z => ENNReal.ofReal (bumpDens p A₁ B₁ (P.real A₁) (P.real B₁) πh hh z))
      ∃ c₁ c₂ ε₀ : ℝ, ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [TopologicalSpace.SeparableSpace H] (φ : ℝ → H), IsLaplaceFeature σ φ → TwoSided54 φ Ph Q c₁ c₂ ε₀

/-- Y20 (e), S4 :1383-1384: no pair `((1−b)R + bP₀, (1−c)R + cQ₀)` with disjoint supports and Lebesgue densities crosses as in
Proposition 5.5. -/
def lower2pt_not_cross : Prop :=
  ∀ (R P₀ Q₀ : Measure ℝ) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀] [IsProbabilityMeasure Q₀] (SR SP SQ : Set ℝ)
    (b c : ℝ) (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ),
    MeasurableSet SR → MeasurableSet SP → MeasurableSet SQ → Disjoint SR SP → Disjoint SR SQ → Disjoint SP SQ →
    R SRᶜ = 0 → P₀ SPᶜ = 0 → Q₀ SQᶜ = 0 → 0 < b → b < 1 → 0 < c → c < 1 →
      ¬ (IsCross (Wave31tn.mixAt R P₀ b) (Wave31tn.mixAt R Q₀ c) p q x₀ ℓ₀ ∧ 0 < p x₀)

/-- Y21, S4 :1024-1026, :1383: every valid lower bound has an error of order `(n∧m)^{−1/2}` near each pair covered by Theorem 5.11(i). -/
def local_rate : Prop :=
  ∀ (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ rs cs δ : ℝ),
    IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ → CondR p q x₀ rs cs → 0 ≤ δ → δ < 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ min n m →
      ∀ (Ξ : Type) [MeasurableSpace Ξ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ] (T : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ),
        Measurable T → ((sampleLaw P Q n m).prod ρ).real {z | Distances.tvDist P Q < T z} ≤ δ →
        ∃ (P' Q' : Measure ℝ) (p' q' : ℝ → ℝ) (rs' cs' : ℝ),
          ∃ _ : IsProbabilityMeasure P', ∃ _ : IsProbabilityMeasure Q',
            IsCross P' Q' p' q' x₀ ℓ₀ ∧ 0 < p' x₀ ∧ ExpTail P' Q' x₀ ∧ CondR p' q' x₀ rs' cs' ∧
            Distances.tvDist P' P + Distances.tvDist Q' Q ≤ C / √((min n m : ℕ) : ℝ) ∧
            (1 - δ) / 2 ≤ ((sampleLaw P' Q' n m).prod ρ).real
              {z | c / √((min n m : ℕ) : ℝ) ≤ Distances.tvDist P' Q' - T z}

/-- Y25, `prop:newrates` (Proposition S4.8) (ii), S4 :470-487, uniform form (`n₀` before everything the printed list does not name). -/
def newrates_ii_exp : Prop :=
  ∀ (κ αs c' ε₀ b η δ s2 c : ℝ), 0 < κ → 0 < c' → 0 < ε₀ → ε₀ ≤ αs → αs < 1 → 0 < b → 0 < η → η < 1 →
    0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 2 * c' < c →
    ∃ n₀ : ℕ, ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (ω : ℝ → ℝ) (J n m : ℕ) (α : Fin J → ℝ) (h : ℝ) (R : LoRun 𝒳 J n m),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Distances.tvDist P Q = αs →
      MonotoneOn ω (Icc 0 αs) → (∀ e ∈ Icc (0 : ℝ) αs, 0 ≤ ω e) →
      (∀ e ∈ Icc (0 : ℝ) αs, ω e ≤ Wave31ti.uPath φ P Q (αs - e)) →
      (∀ e ∈ Ioc (0 : ℝ) ε₀, Real.exp (-c' / e) ≤ ω e) →
      IsGrid α → 1 ≤ J → (J : ℝ) ≤ ((min n m : ℕ) : ℝ) ^ b → R.IsWitnessRun φ α δ (1 / 2) s2 → IsDefaultRun R →
      n₀ ≤ min n m → MeshBelowLe α αs h →
        ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
          E ⊆ {z | αs - h - c / Real.log ((min n m : ℕ) : ℝ) ≤ R.alphaLo α δ z.1 z.2 ∧ R.alphaLo α δ z.1 z.2 ≤ αs}

/-- Y6, S4 :1048-1056: `L`, `err`, `eq:laperr` and `0 ≤ err ≤ 2`. -/
def lap_err : Prop :=
  ∀ (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (f : ℝ → ℝ),
    Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) → Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
    Measurable f → (∃ C, ∀ x, |f x| ≤ C) → Wave31to.oscFn f ≤ 1 →
      errL P Q f = Distances.tvDist P Q * (1 - Wave31to.oscFn f) + (∫ x, ((⨆ z, f z) - f x) * max (p x - q x) 0) +
          ∫ x, (f x - ⨅ z, f z) * max (q x - p x) 0 ∧
      0 ≤ Distances.tvDist P Q * (1 - Wave31to.oscFn f) ∧ 0 ≤ ∫ x, ((⨆ z, f z) - f x) * max (p x - q x) 0 ∧
      0 ≤ ∫ x, (f x - ⨅ z, f z) * max (q x - p x) 0 ∧ 0 ≤ errL P Q f ∧ errL P Q f ≤ 2 ∧
      ((∀ x, 0 ≤ f x ∧ f x ≤ 1) → errL P Q f = Wave31to.errFn P Q f)

/-- Y7, S4 :1061-1071: the constants `ρ₀`, `c_V`, `κ₀` and their roles. -/
def lap_const : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (κ : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (c₁ c₂ ε₀ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Distances.tvDist P Q < 1 → TwoSided54 φ P Q c₁ c₂ ε₀ →
      let αs := Distances.tvDist P Q
      0 < rho0 αs c₁ c₂ ∧ rho0 αs c₁ c₂ < 1 ∧ 0 < kappa0 αs c₁ c₂ ε₀ ∧ kappa0 αs c₁ c₂ ε₀ < 1 ∧ 0 < cV αs c₁ ε₀ ∧
      MonotoneOn (fun e => Wave31ti.uPath φ P Q (αs - e)) (Icc 0 αs) ∧
      (∀ e ∈ Icc (0 : ℝ) αs, (1 - αs) * Dpop φ P Q (αs - e) ≤ Wave31ti.uPath φ P Q (αs - e) ∧
        Wave31ti.uPath φ P Q (αs - e) ≤ Dpop φ P Q (αs - e)) ∧
      (∀ e ∈ Ioc (0 : ℝ) αs, cV αs c₁ ε₀ * e ^ (5 / 4 : ℝ) ≤ Wave31ti.uPath φ P Q (αs - e)) ∧
      (∀ e ∈ Ioo (0 : ℝ) (ε₀ / 2), rho0 αs c₁ c₂ * Wave31ti.uPath φ P Q (αs - 2 * e) ≤ Wave31ti.uPath φ P Q (αs - e))

/-- Y11, S4 :1134-1143, :1342-1344: the population ramp, `eq:lappop` and the order of `g⋆`. -/
def lap_pop : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (σ : ℝ) (φ : ℝ → H) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (ε : ℝ) (a b : H) (t u : ℝ),
    0 < σ → IsLaplaceFeature σ φ → 0 < ε → ε < Distances.tvDist P Q → Distances.tvDist P Q < 1 →
    a ∈ region φ (Distances.tvDist P Q - ε) P → b ∈ region φ (Distances.tvDist P Q - ε) Q →
    ‖a - b‖ = Dpop φ P Q (Distances.tvDist P Q - ε) →
    IsLeast {q | IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - (Distances.tvDist P Q - ε)) q} t →
    IsGreatest {q | IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (Distances.tvDist P Q - ε) q} u →
      let α := Distances.tvDist P Q - ε
      let f := ‖a - b‖⁻¹ • (a - b)
      let φs := (t - u)⁻¹ • f
      0 < Dpop φ P Q α ∧ 0 < t - u ∧
      Wave31to.oscFn (Wave31to.wit φ φs) ≤ 1 ∧ ‖φs‖ = 1 / (t - u) ∧
      (∀ g' : H, (∀ z, ⟪g', φ z⟫_ℝ = Wave31to.wit φ φs z) → ‖φs‖ ≤ ‖g'‖) ∧
      linL P Q (Wave31to.wit φ φs) - α =
        (∫ z, ramp (Wave31to.wit φ f) t u z ∂P) - (∫ z, ramp (Wave31to.wit φ f) t u z ∂Q) - α ∧
      (∫ z, ramp (Wave31to.wit φ f) t u z ∂P) - (∫ z, ramp (Wave31to.wit φ f) t u z ∂Q) - α =
        Wave31ti.uPath φ P Q α / (t - u) ∧
      Wave31ti.uPath φ P Q α / (t - u) ≤ ε ∧ Wave31ti.uPath φ P Q α / ε ≤ t - u ∧ errL P Q (Wave31to.wit φ φs) ≤ ε ∧
      t - u ≤ Wave31to.oscFn (Wave31to.wit φ f) ∧ Wave31to.oscFn (Wave31to.wit φ f) ≤ 2 ∧
      ∀ c₁ c₂ ε₀ : ℝ, TwoSided54 φ P Q c₁ c₂ ε₀ →
        ‖φs‖ ≤ (cV (Distances.tvDist P Q) c₁ ε₀)⁻¹ * ε ^ (-(1 / 4 : ℝ)) ∧
        cV (Distances.tvDist P Q) c₁ ε₀ * ε ^ (1 / 4 : ℝ) ≤ t - u ∧
        (2 * ε ≤ ε₀ → t - u ≤ c₂ * (2 * ε) ^ (5 / 4 : ℝ) / ε)

/-- Y12, `lem:lapcompare` (Lemma S4.22, S4 :1145-1182). -/
def lap_compare : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (σ : ℝ) (φ : ℝ → H) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (c₁ c₂ ε₀ ε : ℝ) (a b : H)
    (t u : ℝ) (n m : ℕ) (x : Fin n → ℝ) (y : Fin m → ℝ) (w : Fin n → ℝ) (v : Fin m → ℝ),
    0 < σ → IsLaplaceFeature σ φ → Distances.tvDist P Q < 1 → TwoSided54 φ P Q c₁ c₂ ε₀ → 0 < ε →
    ε < Distances.tvDist P Q →
    a ∈ region φ (Distances.tvDist P Q - ε) P → b ∈ region φ (Distances.tvDist P Q - ε) Q →
    ‖a - b‖ = Dpop φ P Q (Distances.tvDist P Q - ε) →
    IsLeast {q | IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - (Distances.tvDist P Q - ε)) q} t →
    IsGreatest {q | IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (Distances.tvDist P Q - ε) q} u →
    1 ≤ n → 1 ≤ m → (∀ i j, x i ≠ y j) → IsQPMin φ (Distances.tvDist P Q - ε) x y w v →
      let α := Distances.tvDist P Q - ε
      let φs := (t - u)⁻¹ • (‖a - b‖⁻¹ • (a - b))
      let gh := tHat φ x y w v α - uHat φ x y w v α
      let φh := gh⁻¹ • witness φ x y w v
      let Δ := fun g : H => linL (empirical x) (empirical y) (Wave31to.wit φ g) - linL P Q (Wave31to.wit φ g)
      let V := Wave31ti.uPath φ P Q α
      let Dh := (1 - α) * qpVal φ x y w v
      let Th := errL P Q (Wave31to.wit φ φh)
      let yy := V + (t - u) * Δ φs
      let e := (∫ z, ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α) z ∂P) -
        (∫ z, ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α) z ∂Q) - α
      let κ := kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀
      (e = ε - Th ∧ e + Δ φh = Dh * ‖φh‖ ∧ yy ≤ Dh ∧ ‖φh‖ * yy + Th ≤ ε + Δ φh) ∧
      (0 < κ * ε - |Δ φs| - Δ φh → κ * ε - |Δ φs| - Δ φh ≤ e) ∧
      (|Δ φs| ≤ κ * ε / 4 → V / 2 ≤ yy ∧ cV (Distances.tvDist P Q) c₁ ε₀ * ε ^ (5 / 4 : ℝ) / 2 ≤ V / 2)

/-- Y14, `lem:lapown` (Lemma S4.26), general part: a ramp with cut points moved inward. -/
def own_ramp : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (ψ : 𝒳 → ℝ)
    (ao bo : ℝ), Measurable ψ → (∀ z, 0 ≤ ψ z ∧ ψ z ≤ 1) → 0 ≤ ao → 0 ≤ bo → ao + bo < 1 →
      linL P Q ψ - max ao bo * errL P Q ψ / (1 - ao - bo) ≤
        linL P Q (fun z => min 1 (max 0 ((ψ z - ao) / (1 - ao - bo))))

/-- Y14, `lem:lapown` (Lemma S4.26, S4 :1277-1291), printed form. -/
def lap_own : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (σ : ℝ) (φ : ℝ → H) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n m : ℕ) (x : Fin n → ℝ)
    (y : Fin m → ℝ) (α : ℝ) (w : Fin n → ℝ) (v : Fin m → ℝ) (tt uu : ℝ),
    0 < σ → IsLaplaceFeature σ φ → 1 ≤ n → 1 ≤ m → (∀ i j, x i ≠ y j) → 0 < α → α < 1 → IsQPMin φ α x y w v →
      let t := tHat φ x y w v α
      let u := uHat φ x y w v α
      let D := (1 - α) * qpVal φ x y w v
      (u ≤ uu → uu < tt → tt ≤ t →
        (uu - u) / (t - u) + (t - tt) / (t - u) < 1 ∧
        ramp (fitF φ x y w v) tt uu = (fun z => min 1 (max 0 ((ramp (fitF φ x y w v) t u z - (uu - u) / (t - u)) /
          (1 - (uu - u) / (t - u) - (t - tt) / (t - u))))) ∧
        linL P Q (ramp (fitF φ x y w v) t u) - max ((uu - u) / (t - u)) ((t - tt) / (t - u)) *
            errL P Q (ramp (fitF φ x y w v) t u) / (1 - (uu - u) / (t - u) - (t - tt) / (t - u)) ≤
          linL P Q (ramp (fitF φ x y w v) tt uu)) ∧
      (IsEmpQuantile (ownX φ x y w v) (1 - α) tt → IsEmpQuantile (ownY φ x y w v) α uu →
        u ≤ uu ∧ tt ≤ t ∧ (uu - u) / (t - u) ≤ 1 / (m * D * (t - u)) ∧ (t - tt) / (t - u) ≤ 1 / (n * D * (t - u)))

/-- Y15 (a), (b), `prop:lapfitted` (Proposition S4.27, S4 :1293-1344), at `σ = 1` as printed. -/
def lap_fitted : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ)
    (x₀ ℓ₀ c₁ c₂ ε₀ c K : ℝ) (n m : ℕ) (x : Fin n → ℝ) (y : Fin m → ℝ),
    IsLaplaceFeature 1 φ → IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → TwoSided54 φ P Q c₁ c₂ ε₀ → Distances.tvDist P Q < 1 →
    1 ≤ n → 1 ≤ m → (∀ i j, x i ≠ y j) → Real.log 8 ≤ c → 1 ≤ K → IntervalEvent P x c → IntervalEvent Q y c →
      let αs := Distances.tvDist P Q
      let κ := kappa0 αs c₁ c₂ ε₀
      let cv := cV αs c₁ ε₀
      (∀ (rs cs pbar : ℝ), CondR p q x₀ rs cs → (∀ z ∈ Icc (x₀ - rs) (x₀ + rs), p z + q z ≤ pbar) →
        ∀ ε, epsFitI κ cv (devA P Q x₀ K pbar cs rs c n m) (devG pbar cs rs K c n m) (devB K c n m) (min n m) ≤ ε →
          ε < αs → ∀ w v, IsQPMin φ (αs - ε) x y w v →
            (∀ t u, GenuineCuts φ x y w v (αs - ε) t u → u < t ∧
              κ * ε / 2 ≤ (∫ z, ramp (fitF φ x y w v) t u z ∂P) - (∫ z, ramp (fitF φ x y w v) t u z ∂Q) - (αs - ε)) ∧
            cv * ε ^ (1 / 4 : ℝ) / 24 ≤ tHat φ x y w v (αs - ε) - uHat φ x y w v (αs - ε) ∧
            (2 * ε ≤ αs → tHat φ x y w v (αs - ε) - uHat φ x y w v (αs - ε) ≤ Wave31ti.uPath φ P Q (αs - 2 * ε) / ε)) ∧
      (∀ ε, epsFitII κ cv (devA' P Q x₀ K c n m) (devG' K c n m) (devB K c n m) (min n m) ≤ ε → ε < αs →
        ∀ w v, IsQPMin φ (αs - ε) x y w v → ∀ t u, GenuineCuts φ x y w v (αs - ε) t u → u < t ∧
          κ * ε / 2 ≤ (∫ z, ramp (fitF φ x y w v) t u z ∂P) - (∫ z, ramp (fitF φ x y w v) t u z ∂Q) - (αs - ε))

/-- Y18 (G), `thm:laplaceconst` (Theorem S4.19) (ii), S4 :989-1018. -/
def laplace_const_ii : Prop :=
  ∀ (σ αs c₁ c₂ ε₀ C' : ℝ), 0 < σ → 0 < αs → αs < 1 → 0 < c₁ → c₁ ≤ c₂ → 0 < ε₀ → ε₀ ≤ αs → 0 < C' →
    ∃ C : ℝ, 0 < C ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (φ : ℝ → H) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ)
      (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h : ℝ) (R : LoRun ℝ J n m),
      IsLaplaceFeature σ φ → IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → SumTail P Q x₀ C' →
      Distances.tvDist P Q = αs → TwoSided54 φ P Q c₁ c₂ ε₀ →
      IsGrid α → (∀ j, 0 < α j) → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < η → η < 1 →
      IsGenuineRun R φ α δ (1 / 2) s2 → IsDefaultRun R → 10 ≤ min n m → MeshBelowLe α αs h →
        ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
          E ⊆ {z | αs - h - C * (((Real.log ((max n m : ℕ) : ℝ)) ^ (1 / 2 : ℝ) *
                    Real.log (((max n m : ℕ) : ℝ) / η) / ((min n m : ℕ) : ℝ)) ^ (4 / 9 : ℝ) +
                  s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) / √((min n m : ℕ) : ℝ)) ≤
                R.alphaLo α δ z.1 z.2 ∧ R.alphaLo α δ z.1 z.2 ≤ αs}

/-- Y17, S4 :1038-1039: rescaling the data by `1/σ`. -/
def lap_rescale : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (σ : ℝ) (φ : ℝ → H), 0 < σ → IsLaplaceFeature σ φ →
    IsLaplaceFeature 1 (fun u => φ (σ * u)) ∧
    (∀ (n m : ℕ) (x : Fin n → ℝ) (y : Fin m → ℝ) (α : ℝ) (w : Fin n → ℝ) (v : Fin m → ℝ),
      (IsQPMin φ α x y w v ↔ IsQPMin (fun u => φ (σ * u)) α (fun i => x i / σ) (fun j => y j / σ) w v) ∧
      qpVal φ x y w v = qpVal (fun u => φ (σ * u)) (fun i => x i / σ) (fun j => y j / σ) w v ∧
      (∀ z, fitF φ x y w v z = fitF (fun u => φ (σ * u)) (fun i => x i / σ) (fun j => y j / σ) w v (z / σ)) ∧
      ownX φ x y w v = ownX (fun u => φ (σ * u)) (fun i => x i / σ) (fun j => y j / σ) w v ∧
      ownY φ x y w v = ownY (fun u => φ (σ * u)) (fun i => x i / σ) (fun j => y j / σ) w v) ∧
    ∀ (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ C' rs cs pbar : ℝ),
      IsCross P Q p q x₀ ℓ₀ →
      IsCross (P.map (fun x => x / σ)) (Q.map (fun x => x / σ)) (fun u => σ * p (σ * u)) (fun u => σ * q (σ * u))
          (x₀ / σ) (σ ^ 2 * ℓ₀) ∧
      Distances.tvDist (P.map (fun x => x / σ)) (Q.map (fun x => x / σ)) = Distances.tvDist P Q ∧
      (∀ α, Dpop (fun u => φ (σ * u)) (P.map (fun x => x / σ)) (Q.map (fun x => x / σ)) α = Dpop φ P Q α) ∧
      (ExpTailWith P Q x₀ C' → ExpTailWith (P.map (fun x => x / σ)) (Q.map (fun x => x / σ)) (x₀ / σ) (max C' (C' / σ))) ∧
      (SumTail P Q x₀ C' → SumTail (P.map (fun x => x / σ)) (Q.map (fun x => x / σ)) (x₀ / σ) (max C' (C' / σ))) ∧
      (CondR p q x₀ rs cs → CondR (fun u => σ * p (σ * u)) (fun u => σ * q (σ * u)) (x₀ / σ) (min 1 (rs / σ)) (cs * σ)) ∧
      ((∀ z ∈ Icc (x₀ - rs) (x₀ + rs), p z + q z ≤ pbar) →
        ∀ z ∈ Icc (x₀ / σ - min 1 (rs / σ)) (x₀ / σ + min 1 (rs / σ)), σ * p (σ * z) + σ * q (σ * z) ≤ σ * pbar) ∧
      ∀ n m : ℕ, sampleLaw (P.map (fun x => x / σ)) (Q.map (fun x => x / σ)) n m =
        (sampleLaw P Q n m).map (fun z => ((fun i => z.1 i / σ), (fun j => z.2 j / σ)))

/-- Y8, `eq:condR` around the theorem (§5 :324-325; abs :12-13; §1 :85-86; S4 :1071-1073). -/
def condR_facts : Prop :=
  ∀ (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ),
    IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ →
      ((∃ rs cs, CondR p q x₀ rs cs) ↔
        ∀ r > 0, ∃ c > 0, ∀ᵐ x ∂volume, r ≤ |x - x₀| → c * (p x + q x) ≤ |p x - q x|) ∧
      ∀ rs cs, CondR p q x₀ rs cs →
        (∀ rs' ∈ Ioc 0 rs, CondR p q x₀ rs' cs) ∧
        (∃ rs' ∈ Ioc 0 rs, ∃ pbar : ℝ, ∀ z ∈ Icc (x₀ - rs') (x₀ + rs'), p z + q z ≤ pbar) ∧
        (∀ᵐ x ∂volume, rs ≤ |x - x₀| → p x + q x ≤ |p x - q x| / (cs * rs)) ∧
        (∀ a b : ℝ, a < b → (∀ᵐ x ∂volume, x ∈ Ioo a b → p x = q x) → ∀ᵐ x ∂volume, x ∈ Ioo a b → p x + q x = 0) ∧
        ∀ C', ExpTailWith P Q x₀ C' →
          (∀ t, rs ≤ t → (P + Q) {x | t < |x - x₀|} ≤ ENNReal.ofReal (C' * Real.exp (-t / C') / (cs * rs))) ∧
          ∃ C'', SumTail P Q x₀ C''

/-- Y23, S6 :157, :167-168: the two simulated pairs satisfy `eq:condR`. -/
def sims_condR : Prop :=
  (∃ rs cs, CondR (ProbabilityTheory.gaussianPDFReal 1 1) (ProbabilityTheory.gaussianPDFReal (-1) 1) 0 rs cs) ∧
  ∃ rs cs, CondR (fun x => 0.8 * ProbabilityTheory.gaussianPDFReal 0 1 x + 0.2 * ProbabilityTheory.gaussianPDFReal 1.5 1 x)
    (fun x => 0.8 * ProbabilityTheory.gaussianPDFReal 0 1 x + 0.2 * ProbabilityTheory.gaussianPDFReal (-1.5) 1 x) 0 rs cs

/-- Y26, `prop:newrates` (Proposition S4.8) (iii), S4 :484-485; §5 :243-246, abs :9-10, §1 :82-83. -/
def newrates_iii_gauss : Prop :=
  ∀ (σ : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ b η δ s2 c : ℝ),
    0 < σ → IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ →
    ExpTail P Q x₀ → 0 < b → 0 < η → η < 1 → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → Real.pi ^ 2 * σ ^ 2 * ℓ₀ / 4 < c →
    ∃ n₀ : ℕ, ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (φ : ℝ → H), (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) →
      ∀ (J n m : ℕ) (α : Fin J → ℝ) (h : ℝ) (R : LoRun ℝ J n m),
      IsGrid α → 1 ≤ J → (J : ℝ) ≤ ((min n m : ℕ) : ℝ) ^ b → R.IsWitnessRun φ α δ (1 / 2) s2 → IsDefaultRun R →
      n₀ ≤ min n m → MeshBelowLe α (Distances.tvDist P Q) h →
        ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
          E ⊆ {z | Distances.tvDist P Q - h - c / Real.log ((min n m : ℕ) : ℝ) ≤ R.alphaLo α δ z.1 z.2 ∧
              R.alphaLo α δ z.1 z.2 ≤ Distances.tvDist P Q}

/-- Y22, the abstract/§1/§5 readings (abs :11-13; §1 :84-88; §5 :8-10, :322-323): a grid of mesh `(n∧m)^{−1/2}` with at most
`n∧m` levels. -/
def laplace_rate_grid : Prop :=
  ∀ (σ : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ rs cs δ s2 η : ℝ),
    0 < σ → IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ → CondR p q x₀ rs cs →
    0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < η → η < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (φ : ℝ → H), IsLaplaceFeature σ φ →
      ∀ (J n m : ℕ) (α : Fin J → ℝ) (R : LoRun ℝ J n m),
      IsGrid α → (∀ j, 0 < α j) → 1 ≤ J → J ≤ min n m → IsGenuineRun R φ α δ (1 / 2) s2 → IsDefaultRun R →
      10 ≤ min n m → MeshBelowLe α (Distances.tvDist P Q) (1 / √((min n m : ℕ) : ℝ)) →
        ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
          E ⊆ {z | Distances.tvDist P Q - C * (Real.log (((max n m : ℕ) : ℝ) / η)) ^ (3 / 4 : ℝ) / √((min n m : ℕ) : ℝ) ≤
                R.alphaLo α δ z.1 z.2 ∧ R.alphaLo α δ z.1 z.2 ≤ Distances.tvDist P Q}

/-- Y18 (Pr), `thm:laplaceconst` (i) under the printed hypotheses, `∃ C` before `H, φ` (B1). -/
def laplace_const_pr_i : Prop :=
  ∀ (σ : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ rs cs : ℝ),
    0 < σ → IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ → CondR p q x₀ rs cs →
    ∃ C : ℝ, 0 < C ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (φ : ℝ → H), IsLaplaceFeature σ φ →
      ∀ (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h : ℝ) (R : LoRun ℝ J n m),
      IsGrid α → (∀ j, 0 < α j) → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < η → η < 1 →
      IsGenuineRun R φ α δ (1 / 2) s2 → IsDefaultRun R → 10 ≤ min n m → MeshBelowLe α (Distances.tvDist P Q) h →
        ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
          E ⊆ {z | Distances.tvDist P Q - h - C * ((Real.log ((max n m : ℕ) : ℝ)) ^ (1 / 4 : ℝ) *
                    (Real.log (((max n m : ℕ) : ℝ) / η)) ^ (1 / 2 : ℝ) +
                  s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η)))) / √((min n m : ℕ) : ℝ) ≤
                R.alphaLo α δ z.1 z.2 ∧ R.alphaLo α δ z.1 z.2 ≤ Distances.tvDist P Q}

/-- Y18 (Pr), `thm:laplaceconst` (ii) under the printed hypotheses. -/
def laplace_const_pr_ii : Prop :=
  ∀ (σ : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ C' : ℝ),
    0 < σ → IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ → SumTail P Q x₀ C' →
    ∃ C : ℝ, 0 < C ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (φ : ℝ → H), IsLaplaceFeature σ φ →
      ∀ (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h : ℝ) (R : LoRun ℝ J n m),
      IsGrid α → (∀ j, 0 < α j) → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < η → η < 1 →
      IsGenuineRun R φ α δ (1 / 2) s2 → IsDefaultRun R → 10 ≤ min n m → MeshBelowLe α (Distances.tvDist P Q) h →
        ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
          E ⊆ {z | Distances.tvDist P Q - h - C * (((Real.log ((max n m : ℕ) : ℝ)) ^ (1 / 2 : ℝ) *
                    Real.log (((max n m : ℕ) : ℝ) / η) / ((min n m : ℕ) : ℝ)) ^ (4 / 9 : ℝ) +
                  s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) / √((min n m : ℕ) : ℝ)) ≤
                R.alphaLo α δ z.1 z.2 ∧ R.alphaLo α δ z.1 z.2 ≤ Distances.tvDist P Q}

/-- Y19 (ii), `thm:laplacerate` (Theorem 5.11) (ii), printed `O` form, `∃ C` before `H, φ`. -/
def laplace_rate_ii : Prop :=
  ∀ (σ : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ C' : ℝ),
    0 < σ → IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ → SumTail P Q x₀ C' →
    ∃ C : ℝ, 0 < C ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (φ : ℝ → H), IsLaplaceFeature σ φ →
      ∀ (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h : ℝ) (R : LoRun ℝ J n m),
      IsGrid α → (∀ j, 0 < α j) → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < η → η < 1 →
      IsGenuineRun R φ α δ (1 / 2) s2 → IsDefaultRun R → 10 ≤ min n m → MeshBelowLe α (Distances.tvDist P Q) h →
        ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
          E ⊆ {z | Distances.tvDist P Q - h - C * ((Real.log (((max n m : ℕ) : ℝ) / η)) ^ (2 / 3 : ℝ) *
                    ((min n m : ℕ) : ℝ) ^ (-(4 / 9 : ℝ)) +
                  s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) / √((min n m : ℕ) : ℝ)) ≤
                R.alphaLo α δ z.1 z.2 ∧ R.alphaLo α δ z.1 z.2 ≤ Distances.tvDist P Q}

/-- Y19 (c), §5 :240-243: "Theorem 5.7 guarantees at least … `(n∧m)^{−2/5}` for the Laplace kernel, which Theorem 5.11
improves to `(n∧m)^{−1/2}`, up to powers of `log(n∨m)`, under one more condition, for samples of comparable size". (c1) the bounds of
Theorem 5.11 (any constant `C`) are at most `C₀(log(n∨m))^{3/4}(n∧m)^{−1/2}` (i) and `C₀(log(n∨m))^{2/3}(n∧m)^{−4/9}` (ii) for fixed
`δ, η, v²_min, J`; (c2) the sense of "improves": for samples of comparable size, read as `n∨m ≤ (n∧m)^k` (D15), both are
`o((n∧m)^{−2/5})`. -/
def laplace_rate_improves : Prop :=
  (∀ (C δ s2 η : ℝ) (J : ℕ), 0 < C → 0 < δ → δ < 1 → 0 < s2 → 0 < η → η < 1 → 1 ≤ J →
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n m : ℕ, 10 ≤ min n m →
      C * ((Real.log (((max n m : ℕ) : ℝ) / η)) ^ (3 / 4 : ℝ) / √((min n m : ℕ) : ℝ) +
          s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) / √((min n m : ℕ) : ℝ)) ≤
        C₀ * (Real.log ((max n m : ℕ) : ℝ)) ^ (3 / 4 : ℝ) / √((min n m : ℕ) : ℝ) ∧
      C * ((Real.log (((max n m : ℕ) : ℝ) / η)) ^ (2 / 3 : ℝ) * ((min n m : ℕ) : ℝ) ^ (-(4 / 9 : ℝ)) +
          s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) / √((min n m : ℕ) : ℝ)) ≤
        C₀ * (Real.log ((max n m : ℕ) : ℝ)) ^ (2 / 3 : ℝ) * ((min n m : ℕ) : ℝ) ^ (-(4 / 9 : ℝ))) ∧
  ∀ (k C δ s2 η : ℝ) (J : ℕ), 1 ≤ k → 0 < δ → δ < 1 → 0 < s2 → 0 < η → η < 1 → 1 ≤ J →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ min n m → ((max n m : ℕ) : ℝ) ≤ ((min n m : ℕ) : ℝ) ^ k →
      C * ((Real.log (((max n m : ℕ) : ℝ) / η)) ^ (3 / 4 : ℝ) / √((min n m : ℕ) : ℝ) +
          s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) / √((min n m : ℕ) : ℝ)) ≤
        ε * ((min n m : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) ∧
      C * ((Real.log (((max n m : ℕ) : ℝ) / η)) ^ (2 / 3 : ℝ) * ((min n m : ℕ) : ℝ) ^ (-(4 / 9 : ℝ)) +
          s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) / √((min n m : ℕ) : ℝ)) ≤
        ε * ((min n m : ℕ) : ℝ) ^ (-(2 / 5 : ℝ))

/-- Y15 (c), §5 :290-291, S4 :1034-1036: the fitted ramp keeps a fixed fraction of the population excess. -/
def lap_fitted_fraction : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ)
    (x₀ ℓ₀ c₁ c₂ ε₀ c K ε : ℝ) (n m : ℕ) (x : Fin n → ℝ) (y : Fin m → ℝ) (w : Fin n → ℝ) (v : Fin m → ℝ)
    (t u : ℝ) (a b : H) (ts us : ℝ),
    IsLaplaceFeature 1 φ → IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → TwoSided54 φ P Q c₁ c₂ ε₀ → Distances.tvDist P Q < 1 →
    1 ≤ n → 1 ≤ m → (∀ i j, x i ≠ y j) → Real.log 8 ≤ c → 1 ≤ K → IntervalEvent P x c → IntervalEvent Q y c →
    ((∃ rs cs pbar : ℝ, CondR p q x₀ rs cs ∧ (∀ z ∈ Icc (x₀ - rs) (x₀ + rs), p z + q z ≤ pbar) ∧
        epsFitI (kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀) (cV (Distances.tvDist P Q) c₁ ε₀)
          (devA P Q x₀ K pbar cs rs c n m) (devG pbar cs rs K c n m) (devB K c n m) (min n m) ≤ ε) ∨
      epsFitII (kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀) (cV (Distances.tvDist P Q) c₁ ε₀)
        (devA' P Q x₀ K c n m) (devG' K c n m) (devB K c n m) (min n m) ≤ ε) →
    ε < Distances.tvDist P Q → IsQPMin φ (Distances.tvDist P Q - ε) x y w v →
    GenuineCuts φ x y w v (Distances.tvDist P Q - ε) t u →
    a ∈ region φ (Distances.tvDist P Q - ε) P → b ∈ region φ (Distances.tvDist P Q - ε) Q →
    ‖a - b‖ = Dpop φ P Q (Distances.tvDist P Q - ε) →
    IsLeast {q' | IsQuantileAt P (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) (1 - (Distances.tvDist P Q - ε)) q'} ts →
    IsGreatest {q' | IsQuantileAt Q (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) (Distances.tvDist P Q - ε) q'} us →
      kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ / 2 *
          ((∫ z, ramp (Wave31to.wit φ (‖a - b‖⁻¹ • (a - b))) ts us z ∂P) -
            (∫ z, ramp (Wave31to.wit φ (‖a - b‖⁻¹ • (a - b))) ts us z ∂Q) - (Distances.tvDist P Q - ε)) ≤
        (∫ z, ramp (fitF φ x y w v) t u z ∂P) - (∫ z, ramp (fitF φ x y w v) t u z ∂Q) - (Distances.tvDist P Q - ε)

/-- Y24 (a), §4 :60-68, S3 :105-111: the paper's run (Wave 31tr `IsPaperRun`) with genuine-quantile rules `qt` (X side, at `1−α`)
and `qu` (Y side, at `α`) and the default batches is a genuine-quantile run, own-term branch (`‖φ x‖ ≤ κ` as in 31tr T5). -/
def genuine_paperrun : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : ℝ → H) (κ : ℝ) (J n m : ℕ) (α : Fin J → ℝ)
    (δ s2 w0 : ℝ) (v0 : Fin J → ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ)
    (cxx cyy : ℕ → ℕ) (R : LoRun ℝ J n m),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsGrid α → (∀ j, 0 < α j) → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < w0 →
    Wave31tr.IsGenuineQuantileRule qt → Wave31tr.IsGenuineQuantileRule qu →
    NearestCuts n (cxx 1) (cxx 2) → NearestCuts m (cyy 1) (cyy 2) →
    Wave31tr.IsPaperRun R φ α δ (1 / 2) s2 w0 v0 qt qu 2 cxx cyy → IsGenuineRun R φ α δ (1 / 2) s2 ∧ IsDefaultRun R

/-- Y24 (c), S3 :181-182, §7 :20-22: the printed run exists (cut rules `lowQ`, `highQ`, `w₀ = 20`, `v₀² ≡ 1`, `λ_max = ½`,
nearest-integer boundaries) and is a genuine-quantile run with the default batches. -/
def genuine_run_exists : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : ℝ → H) (κ : ℝ) (J n m : ℕ) (α : Fin J → ℝ)
    (δ s2 : ℝ) (cxx cyy : ℕ → ℕ), StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsGrid α → (∀ j, 0 < α j) → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 →
      NearestCuts n (cxx 1) (cxx 2) → NearestCuts m (cyy 1) (cyy 2) →
      ∃ R : LoRun ℝ J n m, Wave31tr.IsPaperRun R φ α δ (1 / 2) s2 20 (fun _ _ _ _ => (1 : ℝ)) Wave31tr.lowQ Wave31tr.highQ 2 cxx cyy ∧
        IsGenuineRun R φ α δ (1 / 2) s2 ∧ IsDefaultRun R

end Claims

end StatFormal.Wave31tu
