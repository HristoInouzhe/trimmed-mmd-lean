import StatFormal.Archive.OTFD.Wave5a.Statements
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# FROZEN STATEMENTS — otfd wave 13b (QUEUE rows 113–115): A `prop:rt-radial` (constants and the two
# polar integrals), R `thm:compact`, R `thm:cauchy`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-A_sieves.md` and `otfd-R_robustness.md`; current
text after the 2026-10-14 corrections; paths under `otfd/papers/`):
* A `prop:rt-radial` (`A_sieves/main.tex:1493-1527`), proof `A_sieves/supplement.tex:4391-4512` (Step 5 bound (b),
  Step 6 polar integral, "Assembling"), with `θ_* = min(θ,1−θ)` (`A_sieves/main.tex:1380`) and the polar integral of
  `rem:rt-radial-sharp` (proof `A_sieves/supplement.tex:4514-4545`).
* R `thm:compact` (`R_robustness/sections/s3_infinite.tex:11-16`), proof `R_robustness/sections/appendix_a.tex:117-157`,
  with `eq:TDH` (`R_robustness/sections/s2_setting.tex:8-10`), `D_α` (`s3_infinite.tex:8`) and `lem:convex`
  (`appendix_a.tex:8-22`).
* R `thm:cauchy` (`R_robustness/sections/s3_infinite.tex:86-108`), proof `R_robustness/sections/appendix_a.tex:268-319`.
Reuses the frozen `OTFD/Wave1/Statements.lean` (`tukeyDepth`) and `OTFD/Wave5a/Statements.lean` (`depthRegion`),
imported, not copied, and Mathlib's `cauchyMeasure` (location, scale `γ : ℝ≥0`; the standard law is
`cauchyMeasure 0 1`).

Covered:
* `prop:rt-radial`, the explicit constants: `rt_radial_cphi` (`0 < c_φ < 0.233`), `rt_radial_kappa_half`
  (`κ_{1/2} = (8/3)(√2−1)`, the first entry of the minimum), `rt_radial_chalf` (`C_{1/2} = κ_{1/2} + c_φθ_*^{-2}` at
  `θ = 1/2` and `C_{1/2} < 2.04`), `rt_radial_consts` (for every `θ ∈ (0,1)`: `c_φ/τ_θ ≤ θ_*^{-2}`,
  `κ_θ ≤ (2/3)(√2−1)θ_*^{-2}` with `(2/3)(√2−1) < 0.277`, and `κ_θ + c_φθ_*^{-2} ≤ θ_*^{-2}`),
  `rt_radial_in_particular` (the two displayed bounds imply the "in particular" `min` bound), and the two polar
  integrals over `[0,1]²`: `rt_radial_polar_G` (`E[R²R'²/(R²+R'²)^{3/2}] = (2/3)(arsinh 1 − 2^{-1/2})`, Step 6) and
  `rt_radial_polar_L` (`E[RR'/φ(R,R')] = (2/3)(√2−1)`, `rem:rt-radial-sharp`).
* `thm:compact`: `compact_region` (`D_α(μ)` compact and convex), `compact_interior` (empty interior when `dim 𝓗 = ∞`),
  `compact_sigma` (`{TD > 0} = ⋃_{m≥1} D_{1/m}`, σ-compact).
* `thm:cauchy` (i): `cauchy_summable` (`Σ_k s_k²C_k² < ∞` a.s.), `cauchy_hasSum` (the series `Σ s_kC_ke_k` converges
  in `𝓗` to `X` a.s.), `cauchy_law` (`X` is a.e.-measurable and `μ` a probability measure); (ii) `cauchy_proj`;
  (iii) `cauchy_depth`; (iv) `cauchy_regions` (the regions are the bricks, which are compact), `cauchy_union_dense`,
  `cauchy_union_null`, and in dimension `K`: `cauchy_depth_K`, `cauchy_region_K`, `cauchy_coverage`
  (`eq:cauchy-coverage`).

Not covered (declared):
* `prop:rt-radial`: the displayed two-sided bound on `𝓔_K(P,Q) − 𝓓_φ(ϱ^P_K, ϱ^Q_K)` itself, the `K^{-1/2}` bound, the
  same-depth clause `0 ≤ 𝓔_K ≤ (κ_θ + c_φθ_*^{-2})/K` and the mirror-alternative clause (they need the pooled
  monotone rank map `F^Λ_K`, the spherical reference `μ°_K`, `E θθᵀ = I/K` and the Laplace representation of `φ⁻¹`);
  the improper integrals of Step 5 (`∫_0^∞(1−e^{−t})²t^{−5/2}dt = (8√π/3)(√2−1)`, `∫_0^∞t^{−1/2}e^{−2tR²}dt`);
  sharpness (`rem:rt-radial-sharp`: `Kc_K² → 2/π` and the `O(K^{-3/2})` remainder). Only the numbers and the two
  elementary double integrals are certified; `rt_radial_in_particular` certifies the deduction of the `min` bound
  from the two displayed bounds, not the bounds.
* `thm:compact`: nothing omitted. The positive-depth set is written with `m ≥ 1`, as printed
  (the queue note's `m ≥ 2` gives the same union, since `D_1 ⊆ D_{1/2}`).
* `thm:cauchy`: "dense in the support of `μ`" is proved as density in all of `𝓗` (stronger, since `supp μ ⊆ 𝓗`);
  the identity `supp μ = 𝓗` is not stated. The Kallenberg citation (three-series theorem) is not used.

Encodings (see card):
* `prop:rt-radial`: `2^{-1/2}` is `Real.rpow 2 (−1/2)`; `θ_*^{-2}` is `1/θ_*²`; `τ_θ = θ(1−θ)`; every claim assumes
  `0 < θ < 1`, so no `x/0`. `E` over independent `R, R' ~ Unif(0,1)` is the iterated interval integral over
  `[0,1]²`; the integrands are `0/0 = 0` at the single point `(0,0)` (Lebesgue-null). `0.233`, `2.04`, `0.277` are
  decimal literals in `ℝ`. `rt_radial_in_particular` takes `Δ = 𝓔_K − 𝓓_φ` as an arbitrary real and `K ∈ ℕ`, `K ≥ 1`.
* `thm:compact`: `𝓗` is any real inner-product space that is complete and separable, with its Borel σ-algebra;
  `TD_𝓗 = tdH` is `eq:TDH` verbatim (`ℝ≥0∞`-valued, `inf` over `v ≠ 0`; the Wave 1 `tukeyDepth` is the same formula
  on `ℝ^K`); `D_α = depthRegionH μ α = {u : α ≤ TD(u;μ)}` with `α : ℝ≥0∞`. Generalisation: compactness and
  convexity are claimed for **every** `α > 0` and in **every** dimension (the paper: `α ∈ (0,½]`, `dim 𝓗 = ∞`);
  "infinite-dimensional" is `¬ FiniteDimensional ℝ 𝓗`, used only for the empty interior. `D_{1/m}` is
  `depthRegionH μ (m : ℝ≥0∞)⁻¹`.
* `thm:cauchy`: `(C_k)_{k∈ℕ}` i.i.d. standard Cauchy on a probability space `(Ω, P)` is `IsCauchyFamily P C`
  (`iIndepFun` and `HasLaw (C k) (cauchyMeasure 0 1)`); `(e_k)` is a `HilbertBasis ℕ ℝ 𝓗` (indices from `0`, the
  paper's `k` is our `k+1`), `x_k = ⟪e_k, x⟫`. `X = cauchyX b s C` is `b.repr.symm (s_kC_k(ω))_k` on the event
  `Σ_k (s_kC_k)² < ∞` and `0` off it (a `P`-null set by `cauchy_summable`, so `μ = P.map X` does not depend on the
  junk value); `μ` is a genuine probability by `cauchy_law`. `σ(v) = sigmaS b s v` is a `tsum`, shown summable and
  positive in `cauchy_proj` (no junk tsum); the scale fed to `cauchyMeasure` is `σ(v).toNNReal`, faithful as
  `σ(v) > 0`. `‖x‖_{∞,s} = normInfS b s x = ⨆_k ofReal(|x_k|/s_k) ∈ [0,∞]`; `arctan ∞ = π/2` is `arctanE`.
  Depths are `ℝ≥0∞` (`ENNReal.ofReal` of `1/2 − arctan(·)/π ∈ [0, 1/2]`). The bricks are `cauchyBrick b s c`,
  `c = Real.cot(πα)` (`= 0` at `α = 1/2`). "Union over `α > 0`" is over `α ∈ (0, ½]`, as in (iv). The projected law
  is `μ_K = μ.map Π_K`, `Π_K x = (x_0, …, x_{K−1}) ∈ EuclideanSpace ℝ (Fin K)` (`projK`, continuous linear), with the
  frozen `tukeyDepth` and `depthRegion` on `ℝ^K`. `cauchy_depth_K` needs `K ≥ 1` (at `K = 0` the depth is the empty
  infimum `⊤`); `cauchy_region_K` and `cauchy_coverage` hold at `K = 0` as well.
* All claims quantify the sample space and the Hilbert space over `Type` (universe 0), as elsewhere in the repo.

Critic notes:
* `prop:rt-radial` constants hold as printed: `c_φ = 0.23236…`, `κ_{1/2} = 1.10457…`, `C_{1/2} = 2.03399…`;
  `C_{1/2}` simplifies to `(16 arsinh 1 − 8)/3` because `(16/3)·2^{-1/2} = (8/3)√2`. `κ_{1/2}` is the first entry
  (`1.10457 < √2`). The "in particular" clause uses `τ_θ ≥ θ_*²` and `τ_θ ≥ θ_*/2`, both checked.
* `thm:compact`: the route does not follow the printed proof (coordinate quantiles, `lem:divergence`, ℓ² tails). It
  uses tightness (a finite Borel measure on a Polish space is inner regular): with `μ(Kᶜ) < α` for a compact `K`,
  Hahn–Banach separation puts `D_α` inside the closed convex hull of `K`, which is compact. This gives every `α > 0`
  and every dimension at once.
* `thm:cauchy` holds as printed. (i) uses `E Σ_k min(1, s_k²C_k²) ≤ (4/π)Σ_k s_k` (Tonelli; `P(|C| > M) ≤ 2/(πM)`,
  `E[C²; |C| ≤ M] ≤ 2M/π`), not the three-series theorem. (ii) uses Tau Ceti's Cauchy characteristic function and
  dominated convergence along the a.s. convergent partial sums.
* Critic (2026-10-14): ACCEPT-WITH-NOTE. `prop:rt-radial`: the constants are defined exactly as printed and agree with
  the proof (c_φ = 0.232356, κ_{1/2} = 1.104569, C_{1/2} = 2.033992; both double integrals checked numerically); the
  `𝓔_K` bound, Step 5's improper integrals and sharpness are NOT covered. `thm:compact`: the generalisation to every
  `α > 0` and any dimension is genuine (the printed proof never uses `α ≤ ½`). `thm:cauchy`: `HasSum` is stronger than
  the printed convergence; density in all of 𝓗 matches the paper's own proof. Paper notes: R `lem:convex` proof claims
  `{t : g_v(t) ≥ α} = [q_v, ∞)` with `q_v ∈ ℝ` for every `α > 0`, false for `α ≥ 1` (Gaussian, `α = 1`: empty set);
  the conclusion survives (S2, DEFECTS #49). `thm:compact`'s union `⋃_{m≥1}` includes `D_1`, outside `α ∈ (0,½]`;
  harmless since `D_1 ⊆ D_{1/2}` (S4, DEFECTS #50).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ENNReal NNReal

namespace StatFormal.OTFD.Wave13b

open StatFormal.OTFD.Wave1 (tukeyDepth)
open StatFormal.OTFD.Wave5a (depthRegion)

/-! ### A `prop:rt-radial`: constants -/

/-- `c_φ = (4/3)(arsinh 1 − 2^{-1/2})`. -/
def cPhi : ℝ := 4 / 3 * (Real.arsinh 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))

/-- `τ_θ = θ(1 − θ)`. -/
def tauT (θ : ℝ) : ℝ := θ * (1 - θ)

/-- `θ_* = min(θ, 1 − θ)`. -/
def thetaStar (θ : ℝ) : ℝ := min θ (1 - θ)

/-- `κ_θ = min{(√2 − 1)/(6τ_θ²), 1/(2√2 τ_θ)}`. -/
def kappaT (θ : ℝ) : ℝ := min ((Real.sqrt 2 - 1) / (6 * tauT θ ^ 2)) (1 / (2 * Real.sqrt 2 * tauT θ))

/-- `C_{1/2} = (8/3)(√2 − 1) + (16/3)(arsinh 1 − 2^{-1/2})`. -/
def cHalf : ℝ := 8 / 3 * (Real.sqrt 2 - 1) + 16 / 3 * (Real.arsinh 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))

/-! ### R `thm:compact`: depth on a Hilbert space -/

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- `eq:TDH`: `TD(u;μ) = inf_{v ≠ 0} μ{z : ⟨v, z − u⟩ ≤ 0}`. -/
def tdH (μ : Measure H) (u : H) : ℝ≥0∞ := ⨅ (v : H) (_ : v ≠ 0), μ {z | ⟪v, z - u⟫_ℝ ≤ 0}

/-- `D_α(μ) = {u : TD(u;μ) ≥ α}`. -/
def depthRegionH (μ : Measure H) (α : ℝ≥0∞) : Set H := {u | α ≤ tdH μ u}

end Hilbert

/-! ### R `thm:cauchy` -/

section Cauchy
variable {Ω : Type*} [MeasurableSpace Ω] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `(C_k)_k` i.i.d. standard Cauchy. -/
def IsCauchyFamily (P : Measure Ω) (C : ℕ → Ω → ℝ) : Prop :=
  iIndepFun C P ∧ ∀ k, HasLaw (C k) (cauchyMeasure 0 1) P

open scoped Classical in
/-- `X = Σ_k s_k C_k e_k`: `b.repr.symm (s_k C_k(ω))_k` when `(s_k C_k(ω))_k ∈ ℓ²`, else `0` (a null event). -/
def cauchyX (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ) (C : ℕ → Ω → ℝ) (ω : Ω) : H :=
  if h : Summable (fun k => ‖s k * C k ω‖ ^ (2 : ℝ≥0∞).toReal) then
    b.repr.symm ⟨fun k => s k * C k ω, memℓp_gen h⟩
  else 0

/-- `σ(v) = Σ_k |v_k| s_k`. -/
def sigmaS (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ) (v : H) : ℝ := ∑' k, |⟪b k, v⟫_ℝ| * s k

/-- `‖x‖_{∞,s} = sup_k |x_k|/s_k ∈ [0, ∞]`. -/
def normInfS (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ) (x : H) : ℝ≥0∞ :=
  ⨆ k, ENNReal.ofReal (|⟪b k, x⟫_ℝ| / s k)

/-- `arctan` on `[0, ∞]`, with `arctan ∞ = π/2`. -/
def arctanE (r : ℝ≥0∞) : ℝ := if r = ⊤ then Real.pi / 2 else Real.arctan r.toReal

/-- The brick `{x : |x_k| ≤ c s_k ∀ k}`. -/
def cauchyBrick (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ) (c : ℝ) : Set H := {x | ∀ k, |⟪b k, x⟫_ℝ| ≤ c * s k}

/-- `Π_K x = (x_0, …, x_{K−1})`. -/
def projK (b : HilbertBasis ℕ ℝ H) (K : ℕ) (x : H) : EuclideanSpace ℝ (Fin K) :=
  WithLp.toLp 2 fun i : Fin K => ⟪b i, x⟫_ℝ

end Cauchy

namespace Claims

/-! ### `prop:rt-radial` -/

/-- `0 < c_φ < 0.233`. -/
def rt_radial_cphi : Prop := 0 < cPhi ∧ cPhi < 0.233

/-- `κ_{1/2} = (8/3)(√2 − 1)` (the first entry of the minimum). -/
def rt_radial_kappa_half : Prop := kappaT (1 / 2) = 8 / 3 * (Real.sqrt 2 - 1)

/-- `C_{1/2} = κ_{1/2} + c_φ θ_*^{-2}` at `θ = 1/2`, and `C_{1/2} < 2.04`. -/
def rt_radial_chalf : Prop :=
  cHalf = kappaT (1 / 2) + cPhi / thetaStar (1 / 2) ^ 2 ∧ cHalf < 2.04

/-- The constant comparisons behind the "in particular" clause, for every `θ ∈ (0,1)`. -/
def rt_radial_consts : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 →
    cPhi / tauT θ ≤ 1 / thetaStar θ ^ 2 ∧
    kappaT θ ≤ 2 / 3 * (Real.sqrt 2 - 1) / thetaStar θ ^ 2 ∧ 2 / 3 * (Real.sqrt 2 - 1) < 0.277 ∧
    kappaT θ + cPhi / thetaStar θ ^ 2 ≤ 1 / thetaStar θ ^ 2

/-- "In particular": the two displayed bounds on `Δ = 𝓔_K − 𝓓_φ` give
`|Δ| ≤ min{(θ(1−θ))^{-1}(2K)^{-1/2}, θ_*^{-2}K^{-1}}`. -/
def rt_radial_in_particular : Prop :=
  ∀ (θ : ℝ) (K : ℕ) (Δ : ℝ), 0 < θ → θ < 1 → 1 ≤ K →
    -(cPhi / (tauT θ * K)) ≤ Δ → Δ ≤ (kappaT θ + cPhi / thetaStar θ ^ 2) / K →
    |Δ| ≤ 1 / (tauT θ * Real.sqrt (2 * K)) →
      |Δ| ≤ min (1 / (tauT θ * Real.sqrt (2 * K))) (1 / (thetaStar θ ^ 2 * K))

/-- Step 6: `E[R²R'²/(R²+R'²)^{3/2}] = (2/3)(arsinh 1 − 2^{-1/2})` for `R, R'` i.i.d. `Unif(0,1)`. -/
def rt_radial_polar_G : Prop :=
  (∫ r in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, r ^ 2 * t ^ 2 / (r ^ 2 + t ^ 2) ^ (3 / 2 : ℝ)) =
    2 / 3 * (Real.arsinh 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))

/-- `rem:rt-radial-sharp`: `E[RR'/φ(R,R')] = (2/3)(√2 − 1)`. -/
def rt_radial_polar_L : Prop :=
  (∫ r in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, r * t / Real.sqrt (r ^ 2 + t ^ 2)) = 2 / 3 * (Real.sqrt 2 - 1)

/-! ### `thm:compact` -/

/-- `D_α(μ)` is compact and convex, for every Borel probability `μ` and every `α > 0`. -/
def compact_region : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ] (α : ℝ≥0∞), 0 < α →
      IsCompact (depthRegionH μ α) ∧ Convex ℝ (depthRegionH μ α)

/-- In infinite dimension `D_α(μ)` has empty interior. -/
def compact_interior : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ] (α : ℝ≥0∞), ¬ FiniteDimensional ℝ H → 0 < α →
      interior (depthRegionH μ α) = ∅

/-- `{u : TD(u;μ) > 0} = ⋃_{m≥1} D_{1/m}(μ)`, and it is σ-compact. -/
def compact_sigma : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ],
      {u | 0 < tdH μ u} = (⋃ (m : ℕ) (_ : 1 ≤ m), depthRegionH μ (m : ℝ≥0∞)⁻¹) ∧
        IsSigmaCompact {u | 0 < tdH μ u}

/-! ### `thm:cauchy` -/

/-- (i) `Σ_k s_k² C_k² < ∞` almost surely. -/
def cauchy_summable : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (C : ℕ → Ω → ℝ) (s : ℕ → ℝ),
    IsCauchyFamily P C → (∀ k, 0 < s k) → Summable s →
      ∀ᵐ ω ∂P, Summable fun k => (s k * C k ω) ^ 2

/-- (i) the series `Σ_k s_k C_k e_k` converges in `𝓗` to `X` almost surely. -/
def cauchy_hasSum : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (C : ℕ → Ω → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ),
    IsCauchyFamily P C → (∀ k, 0 < s k) → Summable s →
      ∀ᵐ ω ∂P, HasSum (fun k => (s k * C k ω) • b k) (cauchyX b s C ω)

/-- (i) `X` is a random element of `𝓗` and `μ` is a Borel probability measure. -/
def cauchy_law : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (C : ℕ → Ω → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ),
    IsCauchyFamily P C → (∀ k, 0 < s k) → Summable s →
      AEMeasurable (cauchyX b s C) P ∧ IsProbabilityMeasure (P.map (cauchyX b s C))

/-- (ii) For `v ≠ 0`, `⟨v, X⟩ ~ Cauchy(0, σ(v))` with `σ(v) = Σ_k |v_k| s_k ∈ (0, ∞)`. -/
def cauchy_proj : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (C : ℕ → Ω → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ),
    IsCauchyFamily P C → (∀ k, 0 < s k) → Summable s → ∀ v : H, v ≠ 0 →
      Summable (fun k => |⟪b k, v⟫_ℝ| * s k) ∧ 0 < sigmaS b s v ∧
        HasLaw (fun ω => ⟪v, cauchyX b s C ω⟫_ℝ) (cauchyMeasure 0 (sigmaS b s v).toNNReal) P

/-- (iii) `TD(x;μ) = 1/2 − arctan(‖x‖_{∞,s})/π` for every `x ∈ 𝓗`. -/
def cauchy_depth : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (C : ℕ → Ω → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ),
    IsCauchyFamily P C → (∀ k, 0 < s k) → Summable s → ∀ x : H,
      tdH (P.map (cauchyX b s C)) x = ENNReal.ofReal (1 / 2 - arctanE (normInfS b s x) / Real.pi)

/-- (iv) For `α ∈ (0, ½]`, `D_α(μ)` is the brick `{|x_k| ≤ cot(πα) s_k ∀ k}`, and the brick is compact. -/
def cauchy_regions : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (C : ℕ → Ω → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ),
    IsCauchyFamily P C → (∀ k, 0 < s k) → Summable s → ∀ α : ℝ, 0 < α → α ≤ 1 / 2 →
      depthRegionH (P.map (cauchyX b s C)) (ENNReal.ofReal α) = cauchyBrick b s (Real.cot (Real.pi * α)) ∧
        IsCompact (cauchyBrick b s (Real.cot (Real.pi * α)))

/-- (iv) The union of the depth regions over `α ∈ (0, ½]` is dense (in `𝓗`, hence in `supp μ`). -/
def cauchy_union_dense : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (C : ℕ → Ω → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ),
    IsCauchyFamily P C → (∀ k, 0 < s k) → Summable s →
      Dense (⋃ α ∈ Ioc (0 : ℝ) (1 / 2), depthRegionH (P.map (cauchyX b s C)) (ENNReal.ofReal α))

/-- (iv) The union of the depth regions over `α ∈ (0, ½]` is `μ`-null. -/
def cauchy_union_null : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (C : ℕ → Ω → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ),
    IsCauchyFamily P C → (∀ k, 0 < s k) → Summable s →
      P.map (cauchyX b s C)
        (⋃ α ∈ Ioc (0 : ℝ) (1 / 2), depthRegionH (P.map (cauchyX b s C)) (ENNReal.ofReal α)) = 0

/-- (iv) In dimension `K ≥ 1`: `TD(u;μ_K) = 1/2 − arctan(max_{k<K} |u_k|/s_k)/π`. -/
def cauchy_depth_K : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (C : ℕ → Ω → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ),
    IsCauchyFamily P C → (∀ k, 0 < s k) → Summable s → ∀ K : ℕ, 1 ≤ K → ∀ u : EuclideanSpace ℝ (Fin K),
      tukeyDepth ((P.map (cauchyX b s C)).map (projK b K)) u =
        ENNReal.ofReal (1 / 2 - arctanE (⨆ i : Fin K, ENNReal.ofReal (|u i| / s i)) / Real.pi)

/-- (iv) In dimension `K`: `D_α(μ_K) = {u : |u_k| ≤ cot(πα) s_k, k < K}` for `α ∈ (0, ½]`. -/
def cauchy_region_K : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (C : ℕ → Ω → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ),
    IsCauchyFamily P C → (∀ k, 0 < s k) → Summable s → ∀ (K : ℕ) (α : ℝ), 0 < α → α ≤ 1 / 2 →
      depthRegion ((P.map (cauchyX b s C)).map (projK b K)) (ENNReal.ofReal α) =
        {u | ∀ i : Fin K, |u i| ≤ Real.cot (Real.pi * α) * s i}

/-- `eq:cauchy-coverage`: `μ_K(D_α(μ_K)) = (1 − 2α)^K` for `α ∈ (0, ½)`. -/
def cauchy_coverage : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (C : ℕ → Ω → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ),
    IsCauchyFamily P C → (∀ k, 0 < s k) → Summable s → ∀ (K : ℕ) (α : ℝ), 0 < α → α < 1 / 2 →
      ((P.map (cauchyX b s C)).map (projK b K))
          (depthRegion ((P.map (cauchyX b s C)).map (projK b K)) (ENNReal.ofReal α)) =
        ENNReal.ofReal ((1 - 2 * α) ^ K)

end Claims
end StatFormal.OTFD.Wave13b
