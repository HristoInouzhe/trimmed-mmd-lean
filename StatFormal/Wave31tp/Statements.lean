import StatFormal.Wave31tg.Statements
import StatFormal.Wave30tj.Statements
import StatFormal.Archive.Wave8a.Statements
import StatFormal.Archive.Wave12c.Statements
import StatFormal.Archive.TrimmedMMD.Unconditional.Statements
import StatFormal.Archive.TrimmedMMD.ZeroSet.Statements
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.RingTheory.Polynomial.Basic

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31tp: the classical Fourier/RKHS library behind trimmed-mmd (Annals of Statistics version), §5.2 and §S4

Printed source: `~/projects/tmmd-aos-brief/fullstack/NEW_STATEMENTS_31tp.md` (v2 after the independent critic `CRITIC_31tp.md`, with the
re-check notes n1–n4 applied; copy in `certify/sources/tmmd-aos-NEW_STATEMENTS-wave31tp.md`). Paper: trimmed-mmd `aos/` at `c8058c0`
(`sections/05_rates.tex` sha256 d4b6fe12293f…, `supplement/S4_rates.tex` 1632f5261e36…, `supplement/S5_trimming.tex` 6bb834eb323c…).
Design: `PLAN.md`; gaps closed: GAPS A13 (the Fourier setting eq:newnative, eq:newbochner), B1 (`ContainsSmoothCompact`, Wave31tg),
C4 (C^∞ in Remark S5.6), E3 (characteristic), and the library halves of A5, A8, A10, A11, A12.

General library claims (any finite-dimensional real inner-product space `V`, Mathlib's `𝓕` with `𝐞 t = e^{2πit}`), not tied to the
paper; the paper's angular convention `ĝ(ω) = 𝓕 g (ω/2π)` enters only in Wave 31tq. Claim list (draft numbers L1–L30):
F (Fourier): `plancherel` (L1), `ft2_ae` (L2), `ftMeas_facts` (L3), `taylor_cexp` (L4), `moment_decay` (L5), `dilate_facts` (L6),
`laplacian_fourier` (L7), `mollify_smooth`, `mollify_cont` (L8), `sobolev_smooth_finite` (L9), `translation_plancherel`,
`translation_indicator` (L10), `jball_facts`, `jball_one` (L11);
K (kernels): `gram_iso`, `gram_rep`, `gram_mmd`, `rkhs_canonical` (L12), `bochner_integrable` (L13), `gram_profile` (L14),
`fourier_feature`, `feature_exists` (L15), `mmd_fourier` (L16), `native_incl` (L17), `native_char` (L18), `sobolev_incl`,
`containsSmoothCompact_of_spec` (L19), `bandlimited`, `bandlimited_gauss` (L20), `gauss_spec`, `laplace_spec` (L21), `matern_facts`,
`matern_one` (L22), `gauss_moments` (L23), `rkhs_smooth`, `gauss_smooth` (L24), `characteristic_spec` (L25), `rkhs_vanish` (L26);
S, P: `support_density`, `gaussMix_facts`, `gaussMix_distinct` (L27), `moment_poly`, `moment_poly_scale` (L28);
composed: `matern_interpolation_free` (L29, closes the bridge of Wave31tg), `gauss_regular_smooth` (L30, strengthens Wave31th).

Encodings (declared): "positive definite" (`IsPosDefFun`) is the Bochner–Rudin notion, which Wendland (Def. 6.1) calls positive
semi-definite; Wendland's strict notion is `Wave31tg.StrictlyPDOn`. "f ∈ ℋ" is the house encoding: `g : H` represents `f` when
`∀ x, ⟪g, φ x⟫_ℝ = f x`. The Matérn kernels are defined by their spectral density (`besselPot`, `maternK`; M. L. Stein 1999 §2.7,
Rasmussen–Williams 2006 eq. 4.15); the closed form with the Bessel function `K_ν` is not formalised (Mathlib has no `K_ν`).
Junk values: `ft2` is `0` off L²; `nativeN`, `sobolevS` are `ℝ≥0∞` lower integrals (`0/0 = 0`, `x/0 = ⊤`); every `rpow` base is positive;
`(2 * N - 1).doubleFactorial` at `N = 0` is `0‼ = 1 = (−1)!!`.

FROZEN 2026-11-21 after the independent critic's review (v1 NOT READY, 5 blocking items applied; re-check of v2 READY TO FREEZE, notes
n1–n4 applied). Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ContDiff Matrix

namespace StatFormal.Wave31tp

section Defs

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

open scoped Classical in
/-- `ft2 f`: a representative of Mathlib's unitary L² Fourier transform of `f` (`Lp.fourierTransformₗᵢ`); junk `0` off L². -/
def ft2 (f : V → ℂ) : V → ℂ :=
  if h : MemLp f 2 volume then ⇑(𝓕 (h.toLp f) : Lp ℂ 2 (volume : Measure V)) else 0

/-- The spectral density of a real profile: the real part of its (integral) Fourier transform. -/
def specDens (k₀ : V → ℝ) (ξ : V) : ℝ := (𝓕 (fun x => (k₀ x : ℂ)) ξ).re

/-- The native-space functional `∫ |𝓕₂ f|² / 𝓕 k₀` in `[0, ∞]`. -/
def nativeN (k₀ : V → ℝ) (f : V → ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ, ‖ft2 f ξ‖ₑ ^ 2 / ENNReal.ofReal (specDens k₀ ξ)

/-- The Sobolev functional `∫ |𝓕₂ f|² (1 + 4π²‖ξ‖²)^s` in `[0, ∞]` (the paper's weight `(1+|ω|²)^s` at `ω = 2πξ`). -/
def sobolevS (s : ℝ) (f : V → ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ, ‖ft2 f ξ‖ₑ ^ 2 * ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s)

/-- Dilation of a complex function, `w^{-d} b(x/w)`, `d = finrank`. -/
def dilate (w : ℝ) (b : V → ℂ) (x : V) : ℂ := (((w ^ Module.finrank ℝ V)⁻¹ : ℝ) : ℂ) * b (w⁻¹ • x)

/-- Dilation of a real function, `w^{-d} b(x/w)`. -/
def dilateR (w : ℝ) (b : V → ℝ) (x : V) : ℝ := (w ^ Module.finrank ℝ V)⁻¹ * b (w⁻¹ • x)

/-- The indicator of `E` convolved with `b`. -/
def mollify (E : Set V) (b : V → ℝ) : V → ℝ :=
  convolution (E.indicator fun _ => (1 : ℝ)) b (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- The spectral measure `ψ · vol`. -/
def specMeas (ψ : V → ℝ) : Measure V := volume.withDensity fun ξ => ENNReal.ofReal (ψ ξ)

open scoped Classical in
/-- The Fourier feature map `x ↦ [ξ ↦ 𝐞(−⟪x, ξ⟫)] ∈ L²(ψ · vol; ℂ)` (total; the branch is taken whenever `ψ · vol` is finite). -/
def fourierFeature (ψ : V → ℝ) (x : V) : Lp ℂ 2 (specMeas ψ) :=
  if h : MemLp (fun ξ => (𝐞 (-⟪x, ξ⟫_ℝ) : ℂ)) 2 (specMeas ψ) then h.toLp _ else 0

/-- The kernel of a spectral density, `k_ψ(z) = ∫ ψ(ξ) cos(2π⟪z, ξ⟫) dξ`. -/
def kSpec (ψ : V → ℝ) (z : V) : ℝ := ∫ ξ, ψ ξ * Real.cos (2 * Real.pi * ⟪z, ξ⟫_ℝ)

/-- Bessel-potential (Matérn) profile `G_s` by Gaussian subordination. -/
def besselPot (s : ℝ) (x : V) : ℝ :=
  (Real.Gamma s)⁻¹ * ∫ t in Ioi (0 : ℝ), t ^ (s - 1) * Real.exp (-t) *
    (4 * Real.pi * t) ^ (-(Module.finrank ℝ V : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))

/-- The Matérn profile of smoothness `ν = s − d/2`, variance factor `a`, length-scale `ℓ`: `a · G_s(x/ℓ)`. -/
def maternK (s a ℓ : ℝ) (x : V) : ℝ := a * besselPot s (ℓ⁻¹ • x)

end Defs

/-- The Fourier transform of a measure, `ftMeas μ ξ = ∫ 𝐞(−⟪x, ξ⟫) dμ(x)`. -/
def ftMeas {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] (μ : Measure V) (ξ : V) : ℂ :=
  ∫ x, (𝐞 (-⟪x, ξ⟫_ℝ) : ℂ) ∂μ

/-- Positive definite functions (Bochner–Rudin; Wendland's "positive semi-definite"): `Σ_{i,j} c_i conj(c_j) k(x_i − x_j)` is a
nonnegative real for every finite family. -/
def IsPosDefFun {V : Type*} [AddGroup V] (k₀ : V → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → V) (c : Fin n → ℂ),
    (∑ i, ∑ j, c i * starRingEnd ℂ (c j) * k₀ (x i - x j)).im = 0 ∧
      0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) * k₀ (x i - x j)).re

/-- The ball-averaged cosine `j_d(y) = vol(B)⁻¹ ∫_B cos(y v₁) dv` on `ℝ^d`. -/
def jBall (d : ℕ) [NeZero d] (y : ℝ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal⁻¹ *
    ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, Real.cos (y * v 0)

/-- The density of the Gaussian mixture `Σ wᵢ N(mᵢ, Bᵢ)` on `ℝ^d`. -/
def gaussMixDens {d n : ℕ} (w : Fin n → ℝ) (m : Fin n → EuclideanSpace ℝ (Fin d)) (B : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, w i * ((√((2 * Real.pi) ^ d * (B i).det))⁻¹ *
    Real.exp (-(WithLp.ofLp (x - m i) ⬝ᵥ (B i)⁻¹ *ᵥ WithLp.ofLp (x - m i)) / 2))

/-- The Gaussian mixture law `Σ wᵢ • N(mᵢ, Bᵢ)`. -/
def gaussMix {d n : ℕ} (w : Fin n → ℝ) (m : Fin n → EuclideanSpace ℝ (Fin d)) (B : Fin n → Matrix (Fin d) (Fin d) ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  ∑ i, ENNReal.ofReal (w i) • ProbabilityTheory.multivariateGaussian (m i) (B i)

namespace Claims

/-! ### Block F — Fourier analysis on `V` -/

/-- L1. Plancherel's identity for the integral transform on L¹ ∩ L², with polarization (Rudin RCA 9.13; Stein–Weiss I.2.1). -/
def plancherel : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f g : V → ℂ), Integrable f → MemLp f 2 → Integrable g → MemLp g 2 →
      MemLp (𝓕 f) 2 ∧ ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∧
        ∫ ξ, 𝓕 f ξ * starRingEnd ℂ (𝓕 g ξ) = ∫ x, f x * starRingEnd ℂ (g x)

/-- L2. The L² transform agrees with the integral transform on L¹ ∩ L² (both directions). -/
def ft2_ae : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : V → ℂ), Integrable f → ∀ hf : MemLp f 2,
      ft2 f =ᵐ[volume] 𝓕 f ∧
        (⇑(𝓕⁻ (hf.toLp f) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) =ᵐ[volume] 𝓕⁻ f

/-- L3. Fourier transforms of finite measures: continuity, bounds, densities, uniqueness. -/
def ftMeas_facts : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      Continuous (ftMeas μ) ∧ (∀ ξ, ‖ftMeas μ ξ‖ ≤ μ.real univ) ∧ ftMeas μ 0 = (μ.real univ : ℂ) ∧
        (∀ f : V → ℝ, (∀ x, 0 ≤ f x) → Integrable f →
          μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) → ftMeas μ = 𝓕 (fun x => (f x : ℂ))) ∧
        (ftMeas μ = ftMeas ν → μ = ν)

/-- L4. The Taylor bound `|e^{it} − Σ_{j<N} (it)^j/j!| ≤ |t|^N/N!`. -/
def taylor_cexp : Prop :=
  ∀ (t : ℝ) (N : ℕ),
    ‖Complex.exp (t * Complex.I) - ∑ j ∈ Finset.range N, ((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)‖ ≤
      |t| ^ N / N.factorial

/-- L5. eq:newmomentdecay: Fourier transforms of measures with matching moments on `[x₀ − W, x₀ + W]`. -/
def moment_decay : Prop :=
  ∀ (ρ₁ ρ₂ : Measure ℝ) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (x₀ W : ℝ) (N : ℕ), 0 ≤ W → 1 ≤ N →
    ρ₁ (Icc (x₀ - W) (x₀ + W))ᶜ = 0 → ρ₂ (Icc (x₀ - W) (x₀ + W))ᶜ = 0 →
    (∀ j < N, ∫ x, (x - x₀) ^ j ∂ρ₁ = ∫ x, (x - x₀) ^ j ∂ρ₂) →
    ∀ ξ : ℝ, ‖ftMeas ρ₁ ξ - ftMeas ρ₂ ξ‖ ≤
      (ρ₁.real univ + ρ₂.real univ) * min 1 ((2 * Real.pi * |ξ| * W) ^ N / N.factorial)

/-- L6. Dilations: `𝓕 (w^{-d} b(·/w)) (ξ) = 𝓕 b (w ξ)`, and `‖𝓕 b‖ ≤ ‖b‖₁`. -/
def dilate_facts : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (b : V → ℂ) (w : ℝ), Integrable b → 0 < w →
      Integrable (dilate w b) ∧ ∫ x, dilate w b x = ∫ x, b x ∧ (∀ ξ, 𝓕 (dilate w b) ξ = 𝓕 b (w • ξ)) ∧
        ∀ ξ, ‖𝓕 b ξ‖ ≤ ∫ x, ‖b x‖

/-- L7. `𝓕 (Δ^m b)(ξ) = (−4π²‖ξ‖²)^m 𝓕 b(ξ)` for `b ∈ C_c^∞`, and the resulting decay bound. -/
def laplacian_fourier : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (b : V → ℂ) (m : ℕ), ContDiff ℝ ∞ b → HasCompactSupport b →
      (∀ ξ, 𝓕 ((Laplacian.laplacian : (V → ℂ) → (V → ℂ))^[m] b) ξ =
          (((-4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ m : ℝ) : ℂ) * 𝓕 b ξ) ∧
        ∀ ξ, ξ ≠ 0 → ‖𝓕 b ξ‖ ≤
          (∫ x, ‖((Laplacian.laplacian : (V → ℂ) → (V → ℂ))^[m] b) x‖) * ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)⁻¹) ^ m

/-- L8 (a). Mollified indicators with a smooth compactly supported mollifier. -/
def mollify_smooth : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (E : Set V) (b : V → ℝ) (w : ℝ), MeasurableSet E → Bornology.IsBounded E → ContDiff ℝ ∞ b → (∀ x, 0 ≤ b x) →
      ∫ x, b x = 1 → Function.support b ⊆ Metric.closedBall 0 1 → 0 < w →
        ContDiff ℝ ∞ (mollify E (dilateR w b)) ∧ HasCompactSupport (mollify E (dilateR w b)) ∧
        (∀ x, 0 ≤ mollify E (dilateR w b) x ∧ mollify E (dilateR w b) x ≤ 1) ∧
        (∀ x, Metric.closedBall x w ⊆ E → mollify E (dilateR w b) x = 1) ∧
        (∀ x, Metric.closedBall x w ∩ E = ∅ → mollify E (dilateR w b) x = 0) ∧
        Integrable (mollify E (dilateR w b)) ∧ MemLp (mollify E (dilateR w b)) 2 ∧
        ∀ ξ, 𝓕 (fun x => (mollify E (dilateR w b) x : ℂ)) ξ =
          𝓕 (fun x => ((E.indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ)) ξ * 𝓕 (fun x => (b x : ℂ)) (w • ξ)

/-- L8 (b). Indicators of finite-measure sets convolved with a bounded continuous probability density. -/
def mollify_cont : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (E : Set V) (b : V → ℝ), MeasurableSet E → volume E ≠ ⊤ → Continuous b → (∃ C, ∀ x, |b x| ≤ C) → Integrable b →
      (∀ x, 0 ≤ b x) → ∫ x, b x = 1 →
        Continuous (mollify E b) ∧ Integrable (mollify E b) ∧ MemLp (mollify E b) 2 ∧
        (∀ x, 0 ≤ mollify E b x ∧ mollify E b x ≤ 1) ∧
        ∀ ξ, 𝓕 (fun x => (mollify E b x : ℂ)) ξ =
          𝓕 (fun x => ((E.indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ)) ξ * 𝓕 (fun x => (b x : ℂ)) ξ

/-- L9. Smooth compactly supported functions have finite Sobolev functionals of every order. -/
def sobolev_smooth_finite : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (g : V → ℂ) (s : ℝ), ContDiff ℝ ∞ g → HasCompactSupport g → sobolevS s g < ⊤

/-- L10 (first part). Translations: `∫ |𝓕 f|² |𝐞(⟪h,ξ⟫) − 1|² = ‖f(· + h) − f‖₂²` on L¹ ∩ L². -/
def translation_plancherel : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : V → ℂ) (h : V), Integrable f → MemLp f 2 →
      ∫ ξ, ‖𝓕 f ξ‖ ^ 2 * ‖(𝐞 ⟪h, ξ⟫_ℝ : ℂ) - 1‖ ^ 2 = ∫ x, ‖f (x + h) - f x‖ ^ 2

/-- L10 (second part). For an indicator, the L² modulus is the measure of a symmetric difference. -/
def translation_indicator : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (E : Set V) (h : V), MeasurableSet E → volume E ≠ ⊤ →
      ∫ x, ‖E.indicator (fun _ => (1 : ℂ)) (x + h) - E.indicator (fun _ => (1 : ℂ)) x‖ ^ 2 =
          (volume (symmDiff E ((· + h) ⁻¹' E))).toReal ∧
        (volume (symmDiff E ((· + h) ⁻¹' E))).toReal = (volume (symmDiff E ((· - h) ⁻¹' E))).toReal

/-- L11 (first part). The ball-averaged cosine `j_d`: continuity, evenness, `j_d(0) = 1`, `|j_d| ≤ 1`, `j_d < 1` off `0`, decay,
`sup_{y ≥ 1} j_d(y) < 1`, and the rotation identity on every `V` of dimension `d`. -/
def jball_facts : Prop :=
  ∀ (d : ℕ) [NeZero d],
    Continuous (jBall d) ∧ (∀ y, jBall d (-y) = jBall d y) ∧ jBall d 0 = 1 ∧ (∀ y, |jBall d y| ≤ 1) ∧
    (∀ y, y ≠ 0 → jBall d y < 1) ∧ Tendsto (jBall d) (cocompact ℝ) (𝓝 0) ∧ BddAbove (jBall d '' Ici 1) ∧
    sSup (jBall d '' Ici 1) < 1 ∧
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V],
      Module.finrank ℝ V = d → ∀ (r : ℝ) (ξ : V), 0 < r →
        (volume (Metric.ball (0 : V) r)).toReal⁻¹ * ∫ h in Metric.ball (0 : V) r, Real.cos ⟪h, ξ⟫_ℝ = jBall d (r * ‖ξ‖)

/-- L11 (second part). In dimension one, `j₁(y) = sin y / y` and `c₁ = 1 − sin 1`. -/
def jball_one : Prop :=
  (∀ y : ℝ, y ≠ 0 → jBall 1 y = Real.sin y / y) ∧ 1 - sSup (jBall 1 '' Ici 1) = 1 - Real.sin 1

/-! ### Block K — translation-invariant kernels and their RKHS -/

/-- L12 (a). Equal Gram functions give a linear isometry of the closed span of `φ(𝒳)` carrying `φ` to `φ′`. -/
def gram_iso : Prop :=
  ∀ (𝒳 H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H'] (φ : 𝒳 → H) (φ' : 𝒳 → H'),
    (∀ x y, ⟪φ x, φ y⟫_ℝ = ⟪φ' x, φ' y⟫_ℝ) →
      ∃ U : (Submodule.span ℝ (Set.range φ)).topologicalClosure →ₗᵢ[ℝ] H',
        ∀ x (hx : φ x ∈ (Submodule.span ℝ (Set.range φ)).topologicalClosure), U ⟨φ x, hx⟩ = φ' x

/-- L12 (b). Equal Gram functions: every representer for `φ` has one for `φ′` of no larger norm. -/
def gram_rep : Prop :=
  ∀ (𝒳 H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H'] (φ : 𝒳 → H) (φ' : 𝒳 → H'),
    (∀ x y, ⟪φ x, φ y⟫_ℝ = ⟪φ' x, φ' y⟫_ℝ) →
      ∀ g : H, ∃ g' : H', ‖g'‖ ≤ ‖g‖ ∧ ∀ x, ⟪g', φ' x⟫_ℝ = ⟪g, φ x⟫_ℝ

/-- L12 (c). MMD, `dTrim`, `Dpop` and `Demp` depend only on the Gram function. -/
def gram_mmd : Prop :=
  ∀ (𝒳 H H' : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H'] (φ : 𝒳 → H) (φ' : 𝒳 → H') (κ : ℝ),
    (∀ x y, ⟪φ x, φ y⟫_ℝ = ⟪φ' x, φ' y⟫_ℝ) → StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
      (∀ (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (u v : 𝒳 → ℝ), Measurable u → Measurable v →
          (∃ C, ∀ x, |u x| ≤ C) → (∃ C, ∀ x, |v x| ≤ C) →
          ‖∫ x, u x • φ x ∂μ - ∫ x, v x • φ x ∂ν‖ = ‖∫ x, u x • φ' x ∂μ - ∫ x, v x • φ' x ∂ν‖) ∧
      StronglyMeasurable φ' ∧ (∀ x, ‖φ' x‖ ≤ κ) ∧
      (∀ (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (α : ℝ),
          StatFormal.Wave30tj.mmd φ P Q = StatFormal.Wave30tj.mmd φ' P Q ∧
          StatFormal.Wave8a.dTrim φ P Q α = StatFormal.Wave8a.dTrim φ' P Q α ∧
          StatFormal.TrimmedMMD.Unconditional.Dpop φ P Q α = StatFormal.TrimmedMMD.Unconditional.Dpop φ' P Q α) ∧
      ∀ (n m : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (α : ℝ),
        StatFormal.TrimmedMMD.Unconditional.Demp φ x y α = StatFormal.TrimmedMMD.Unconditional.Demp φ' x y α

/-- L12 (d). Mathlib's RKHS: the canonical feature map `x ↦ kerFun H x 1` reproduces `H`, and every feature map with the same kernel
represents exactly the functions of `H`, with minimal norm the RKHS norm. -/
def rkhs_canonical : Prop :=
  ∀ (𝒳 H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [RKHS ℝ H 𝒳 ℝ],
    (∀ (f : H) (x : 𝒳), ⟪f, RKHS.kerFun H x (1 : ℝ)⟫_ℝ = f x) ∧
    (∀ x y : 𝒳, ⟪RKHS.kerFun H x (1 : ℝ), RKHS.kerFun H y (1 : ℝ)⟫_ℝ = RKHS.kernel H y x (1 : ℝ)) ∧
    Dense (Submodule.span ℝ (Set.range fun x : 𝒳 => RKHS.kerFun H x (1 : ℝ)) : Set H) ∧
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H'] (φ' : 𝒳 → H'),
      (∀ x y, ⟪φ' x, φ' y⟫_ℝ = RKHS.kernel H y x (1 : ℝ)) →
      ∀ u : 𝒳 → ℝ, ((∃ g' : H', ∀ x, ⟪g', φ' x⟫_ℝ = u x) ↔ ∃ f : H, ⇑f = u) ∧
        ∀ f : H, ⇑f = u → ∃ g₀ : H', (∀ x, ⟪g₀, φ' x⟫_ℝ = u x) ∧ ‖g₀‖ = ‖f‖ ∧
          ∀ g' : H', (∀ x, ⟪g', φ' x⟫_ℝ = u x) → ‖g₀‖ ≤ ‖g'‖

/-- L13. The integrable case of Bochner's theorem (Rudin, *Fourier Analysis on Groups*, §1.4 and §1.5). -/
def bochner_integrable : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (k₀ : V → ℂ), Continuous k₀ → Integrable k₀ → IsPosDefFun k₀ →
      (∀ z, k₀ (-z) = starRingEnd ℂ (k₀ z)) ∧ (k₀ 0).im = 0 ∧ (∀ z, ‖k₀ z‖ ≤ (k₀ 0).re) ∧
      (∀ ξ, (𝓕 k₀ ξ).im = 0 ∧ 0 ≤ (𝓕 k₀ ξ).re) ∧ Integrable (𝓕 k₀) ∧ ∫ ξ, 𝓕 k₀ ξ = k₀ 0 ∧ 𝓕⁻ (𝓕 k₀) = k₀

/-- L14. Gram profiles `⟪φ x, φ y⟫ = k₀(x − y)`: evenness, bounds, positive definiteness, continuity, the real even spectral
density and (with L13) its nonnegativity, integrability and the inversion formula. -/
def gram_profile : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : V → H) (k₀ : V → ℝ),
    (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) →
      (∀ z, k₀ (-z) = k₀ z) ∧ (∀ z, |k₀ z| ≤ k₀ 0) ∧ (∀ x y, ‖φ x - φ y‖ ^ 2 = 2 * (k₀ 0 - k₀ (x - y))) ∧
      IsPosDefFun (fun z => (k₀ z : ℂ)) ∧ ((Continuous φ ↔ ContinuousAt k₀ 0) ∧ (ContinuousAt k₀ 0 ↔ Continuous k₀)) ∧
      (Integrable k₀ →
        (∀ ξ, 𝓕 (fun x => (k₀ x : ℂ)) ξ = ((∫ x, k₀ x * Real.cos (2 * Real.pi * ⟪x, ξ⟫_ℝ) : ℝ) : ℂ)) ∧
        ∀ ξ, specDens k₀ (-ξ) = specDens k₀ ξ) ∧
      (Integrable k₀ → Continuous k₀ →
        (∀ ξ, 0 ≤ specDens k₀ ξ) ∧ Integrable (specDens k₀) ∧ ∫ ξ, specDens k₀ ξ = k₀ 0 ∧
        ∀ z, k₀ z = ∫ ξ, specDens k₀ ξ * Real.cos (2 * Real.pi * ⟪z, ξ⟫_ℝ))

/-- L15 (first part). The Fourier feature map of a spectral density `ψ ≥ 0` into `L²(ψ · vol; ℂ)` (real structure
`MeasureTheory.L2.innerProductSpace`); its kernel sees only the even part `ψ_e` of `ψ`. -/
def fourier_feature : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (ψ : V → ℝ), Measurable ψ → (∀ ξ, 0 ≤ ψ ξ) → Integrable ψ →
      CompleteSpace (Lp ℂ 2 (specMeas ψ)) ∧ TopologicalSpace.SeparableSpace (Lp ℂ 2 (specMeas ψ)) ∧
      Continuous (fourierFeature ψ) ∧
      (∀ x, (fourierFeature ψ x : V → ℂ) =ᵐ[specMeas ψ] fun ξ => (𝐞 (-⟪x, ξ⟫_ℝ) : ℂ)) ∧
      (∀ x y, ⟪fourierFeature ψ x, fourierFeature ψ y⟫_ℝ = kSpec ψ (x - y)) ∧
      Continuous (kSpec ψ) ∧ (∀ z, kSpec ψ (-z) = kSpec ψ z) ∧ (∀ z, |kSpec ψ z| ≤ kSpec ψ 0) ∧ kSpec ψ 0 = ∫ ξ, ψ ξ ∧
      (∀ z, (kSpec ψ z : ℂ) = 𝓕 (fun ξ => (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ)) z ∧
            (kSpec ψ z : ℂ) = 𝓕⁻ (fun ξ => (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ)) z) ∧
      (Integrable (kSpec ψ) →
        (𝓕 (fun z => (kSpec ψ z : ℂ)) =ᵐ[volume] fun ξ => (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ)) ∧
        (Continuous ψ → ∀ ξ, 𝓕 (fun z => (kSpec ψ z : ℂ)) ξ = (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ)))

/-- L15 (existence). Every continuous, integrable, positive definite real profile has the Fourier feature map of its spectral
density as a feature map. -/
def feature_exists : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (k₀ : V → ℝ), Continuous k₀ → Integrable k₀ → IsPosDefFun (fun z => (k₀ z : ℂ)) →
      Continuous (specDens k₀) ∧ (∀ ξ, specDens k₀ (-ξ) = specDens k₀ ξ) ∧ (∀ ξ, 0 ≤ specDens k₀ ξ) ∧
      Integrable (specDens k₀) ∧ kSpec (specDens k₀) = k₀ ∧
      ∀ x y, ⟪fourierFeature (specDens k₀) x, fourierFeature (specDens k₀) y⟫_ℝ = k₀ (x - y)

/-- L16. eq:newbochner: the MMD of a translation-invariant feature map in Fourier form and as a double integral. -/
def mmd_fourier : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : V → H) (k₀ : V → ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) →
      Continuous φ ∧ StronglyMeasurable φ ∧ (∀ x, ‖φ x‖ = √(k₀ 0)) ∧
      ∀ (μ₁ μ₂ : Measure V) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂],
        Integrable (fun ξ => specDens k₀ ξ * ‖ftMeas μ₁ ξ - ftMeas μ₂ ξ‖ ^ 2) ∧
        ‖∫ x, φ x ∂μ₁ - ∫ x, φ x ∂μ₂‖ ^ 2 = ∫ ξ, specDens k₀ ξ * ‖ftMeas μ₁ ξ - ftMeas μ₂ ξ‖ ^ 2 ∧
        ‖∫ x, φ x ∂μ₁ - ∫ x, φ x ∂μ₂‖ ^ 2 =
          (∫ x, ∫ y, k₀ (x - y) ∂μ₁ ∂μ₁) - 2 * (∫ x, ∫ y, k₀ (x - y) ∂μ₂ ∂μ₁) + ∫ x, ∫ y, k₀ (x - y) ∂μ₂ ∂μ₂

/-- L17. eq:newnative, the inclusion with `≤` (Wendland Thm 10.12, one half), and the integral form of `nativeN` on L¹ ∩ L². -/
def native_incl : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : V → H) (k₀ : V → ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) →
      ∀ f : V → ℝ,
        (Continuous f → MemLp f 2 → nativeN k₀ (fun x => (f x : ℂ)) < ⊤ →
          ∃ g : H, (∀ x, ⟪g, φ x⟫_ℝ = f x) ∧ ENNReal.ofReal (‖g‖ ^ 2) ≤ nativeN k₀ (fun x => (f x : ℂ))) ∧
        (Integrable f → MemLp f 2 →
          nativeN k₀ (fun x => (f x : ℂ)) = ∫⁻ ξ, ‖𝓕 (fun x => (f x : ℂ)) ξ‖ₑ ^ 2 / ENNReal.ofReal (specDens k₀ ξ))

/-- L18. eq:newnative with `=` (Wendland Thm 10.12): the represented functions are exactly the continuous L² functions with finite
native functional, and the minimal norm is its square root. -/
def native_char : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : V → H) (k₀ : V → ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) →
      (∀ g : H, Continuous (fun x => ⟪g, φ x⟫_ℝ) ∧ MemLp (fun x => ⟪g, φ x⟫_ℝ) 2 ∧
        nativeN k₀ (fun x => ((⟪g, φ x⟫_ℝ : ℝ) : ℂ)) ≤ ENNReal.ofReal (‖g‖ ^ 2) ∧
        (g ∈ (Submodule.span ℝ (Set.range φ)).topologicalClosure →
          nativeN k₀ (fun x => ((⟪g, φ x⟫_ℝ : ℝ) : ℂ)) = ENNReal.ofReal (‖g‖ ^ 2))) ∧
      ∀ f : V → ℝ, Continuous f →
        ((∃ g : H, ∀ x, ⟪g, φ x⟫_ℝ = f x) ↔ (MemLp f 2 ∧ nativeN k₀ (fun x => (f x : ℂ)) < ⊤)) ∧
        ((∃ g : H, ∀ x, ⟪g, φ x⟫_ℝ = f x) →
          ∃ g₀ : H, (∀ x, ⟪g₀, φ x⟫_ℝ = f x) ∧ ENNReal.ofReal (‖g₀‖ ^ 2) = nativeN k₀ (fun x => (f x : ℂ)) ∧
            ∀ g : H, (∀ x, ⟪g, φ x⟫_ℝ = f x) → ‖g₀‖ ≤ ‖g‖)

/-- L19 (a). A spectral lower bound `c (1 + 4π²‖ξ‖²)^{−s}` puts the Sobolev functions in the RKHS (Wendland Cor 10.13). -/
def sobolev_incl : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : V → H) (k₀ : V → ℝ) (c s : ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < c →
    (∀ ξ, c * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) ≤ specDens k₀ ξ) →
      ∀ f : V → ℝ, Continuous f → MemLp f 2 → sobolevS s (fun x => (f x : ℂ)) < ⊤ →
        ∃ g : H, (∀ x, ⟪g, φ x⟫_ℝ = f x) ∧
          ENNReal.ofReal (‖g‖ ^ 2) ≤ sobolevS s (fun x => (f x : ℂ)) / ENNReal.ofReal c

/-- L19 (b). The bridge of Wave 31tg holds: with a spectral lower bound, every smooth compactly supported function is represented. -/
def containsSmoothCompact_of_spec : Prop :=
  ∀ (d : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : EuclideanSpace ℝ (Fin d) → H) (k₀ : EuclideanSpace ℝ (Fin d) → ℝ) (c s : ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < c →
    (∀ ξ, c * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) ≤ specDens k₀ ξ) →
      StatFormal.Wave31tg.ContainsSmoothCompact φ

/-- L20 (a). Band-limited functions are represented, with `‖g‖² ≤ ‖f‖₂² / m` when the spectral density is `≥ m` on the band. -/
def bandlimited : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : V → H) (k₀ : V → ℝ) (Ω m : ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 ≤ Ω → 0 < m →
    (∀ ξ, ‖ξ‖ ≤ Ω → m ≤ specDens k₀ ξ) →
      ∀ f : V → ℝ, Continuous f → MemLp f 2 → (∀ᵐ ξ ∂volume, Ω < ‖ξ‖ → ft2 (fun x => (f x : ℂ)) ξ = 0) →
        ∃ g : H, (∀ x, ⟪g, φ x⟫_ℝ = f x) ∧ ‖g‖ ^ 2 ≤ (∫ x, f x ^ 2) / m

/-- L20 (b). eq:newbandlim for the Gaussian kernel on `V` (Steinwart–Hush–Scovel 2006, the elementary half). -/
def bandlimited_gauss : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : V → H) (σ Ω : ℝ),
    0 < σ → 0 ≤ Ω → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) →
      ∀ f : V → ℝ, Continuous f → MemLp f 2 → (∀ᵐ ξ ∂volume, Ω < ‖ξ‖ → ft2 (fun x => (f x : ℂ)) ξ = 0) →
        ∃ g : H, (∀ x, ⟪g, φ x⟫_ℝ = f x) ∧
          ‖g‖ ^ 2 ≤ (2 * Real.pi * σ ^ 2) ^ (-(Module.finrank ℝ V : ℝ) / 2) *
            Real.exp (2 * Real.pi ^ 2 * σ ^ 2 * Ω ^ 2) * ∫ x, f x ^ 2

/-- L21 (a). The Gaussian profile and its Fourier transform. -/
def gauss_spec : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (σ : ℝ), 0 < σ →
      Continuous (fun x : V => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧ Integrable (fun x : V => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧
      ∀ ξ, 𝓕 (fun x : V => ((Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) : ℝ) : ℂ)) ξ =
        (((2 * Real.pi * σ ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) * Real.exp (-2 * Real.pi ^ 2 * σ ^ 2 * ‖ξ‖ ^ 2) : ℝ) : ℂ)

/-- L21 (b). The Laplace kernel on `ℝ`: `𝓕 e^{−|x|} (ξ) = 2/(1 + 4π²ξ²)`. -/
def laplace_spec : Prop :=
  Continuous (fun x : ℝ => Real.exp (-|x|)) ∧ Integrable (fun x : ℝ => Real.exp (-|x|)) ∧
    ∀ ξ : ℝ, 𝓕 (fun x : ℝ => ((Real.exp (-|x|) : ℝ) : ℂ)) ξ = ((2 / (1 + 4 * Real.pi ^ 2 * ξ ^ 2) : ℝ) : ℂ)

/-- L22 (main). Matérn (Bessel-potential) profiles `G_s`, `s > d/2`, and the family `a · G_s(·/ℓ)` with its spectral bounds. -/
def matern_facts : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (s : ℝ), (Module.finrank ℝ V : ℝ) / 2 < s →
      (∀ x : V, IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-t) *
          (4 * Real.pi * t) ^ (-(Module.finrank ℝ V : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))) (Ioi 0)) ∧
      Continuous (besselPot (V := V) s) ∧ (∀ x : V, 0 < besselPot s x) ∧ (∀ x : V, besselPot s x ≤ besselPot s (0 : V)) ∧
      Integrable (besselPot (V := V) s) ∧ ∫ x, besselPot (V := V) s x = 1 ∧
      (∀ ξ : V, 𝓕 (fun x : V => (besselPot s x : ℂ)) ξ = (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) : ℝ) : ℂ)) ∧
      ∀ a ℓ : ℝ, 0 < a → 0 < ℓ →
        Continuous (maternK (V := V) s a ℓ) ∧ (∀ x : V, 0 < maternK s a ℓ x) ∧ Integrable (maternK (V := V) s a ℓ) ∧
        (∀ ξ : V, 𝓕 (fun x : V => (maternK s a ℓ x : ℂ)) ξ =
          ((a * ℓ ^ Module.finrank ℝ V * (1 + 4 * Real.pi ^ 2 * ℓ ^ 2 * ‖ξ‖ ^ 2) ^ (-s) : ℝ) : ℂ)) ∧
        ∀ ξ : V,
          a * ℓ ^ Module.finrank ℝ V * (max 1 (ℓ ^ 2)) ^ (-s) * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) ≤ specDens (maternK s a ℓ) ξ ∧
          specDens (maternK s a ℓ) ξ ≤
            a * ℓ ^ Module.finrank ℝ V * (max 1 (ℓ ^ 2)⁻¹) ^ s * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s)

/-- L22 (ν = ½). On `ℝ`, `G₁(x) = e^{−|x|}/2`. -/
def matern_one : Prop :=
  ∀ x : ℝ, besselPot (V := ℝ) 1 x = Real.exp (-|x|) / 2

/-- L23. Moments of the Gaussian spectral density on `ℝ`: `∫ (2πξ)^{2N} 𝓕k₀ = (2N−1)!! σ^{−2N}`. -/
def gauss_moments : Prop :=
  ∀ (σ : ℝ) (N : ℕ), 0 < σ →
    Integrable (fun ξ : ℝ => (2 * Real.pi * ξ) ^ (2 * N) * specDens (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) ξ) ∧
    ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ (2 * N) * specDens (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) ξ =
      ((2 * N - 1).doubleFactorial : ℝ) * σ⁻¹ ^ (2 * N)

/-- L24 (a). Spectral moments of order `2m` make every represented function `C^m`. -/
def rkhs_smooth : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : V → H) (k₀ : V → ℝ) (m : ℕ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) →
    Integrable (fun ξ => ‖ξ‖ ^ (2 * m) * specDens k₀ ξ) →
      ∀ g : H, ContDiff ℝ m (fun x => ⟪g, φ x⟫_ℝ)

/-- L24 (b). Gaussian RKHS functions are `C^∞` (Steinwart–Christmann Cor 4.36). -/
def gauss_smooth : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : V → H) (σ : ℝ),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) →
      ∀ g : H, ContDiff ℝ ∞ (fun x => ⟪g, φ x⟫_ℝ)

/-- L25. A spectral density positive a.e. makes the feature map characteristic (on finite measures, hence (A3)) and strictly
positive definite. -/
def characteristic_spec : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : V → H) (k₀ : V → ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → (∀ᵐ ξ ∂volume, 0 < specDens k₀ ξ) →
      (∀ (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν], ∫ x, φ x ∂μ = ∫ x, φ x ∂ν → μ = ν) ∧
      StatFormal.TrimmedMMD.ZeroSet.Characteristic φ ∧ StatFormal.Wave31tg.StrictlyPDOn φ Set.univ

/-- L26. Represented functions of an integrable profile vanish at infinity (Riemann–Lebesgue). -/
def rkhs_vanish : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : V → H) (k₀ : V → ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) →
      ∀ g : H, Tendsto (fun x => ⟪g, φ x⟫_ℝ) (comap (fun x => ‖x‖) atTop) (𝓝 0)

/-! ### Block S — supports and analytic densities; Block P — polynomials -/

/-- L27 (a). The support of a measure with a density continuous on an open set `U` is, inside `U`, the closure of `{p > 0}`. -/
def support_density : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (U : Set V) (p : V → ℝ), IsOpen U → ContinuousOn p U → (∀ x ∈ U, 0 ≤ p x) →
      ∀ x ∈ U, (x ∈ (volume.withDensity (fun y => ENNReal.ofReal (U.indicator p y))).support ↔
        x ∈ closure {y | y ∈ U ∧ 0 < p y})

/-- L27 (b). Finite mixtures of nondegenerate Gaussian laws on `ℝ^d` have the explicit density, which is real-analytic and positive. -/
def gaussMix_facts : Prop :=
  ∀ (d n : ℕ) (w : Fin n → ℝ) (m : Fin n → EuclideanSpace ℝ (Fin d)) (B : Fin n → Matrix (Fin d) (Fin d) ℝ),
    (∀ i, 0 < w i) → ∑ i, w i = 1 → (∀ i, (B i).PosDef) →
      gaussMix w m B = volume.withDensity (fun x => ENNReal.ofReal (gaussMixDens w m B x)) ∧
      AnalyticOnNhd ℝ (gaussMixDens w m B) univ ∧ ∀ x, 0 < gaussMixDens w m B x

/-- L27 (c). Two distinct finite Gaussian mixtures have densities that differ somewhere in every nonempty open set. -/
def gaussMix_distinct : Prop :=
  ∀ (d n n' : ℕ) (w : Fin n → ℝ) (m : Fin n → EuclideanSpace ℝ (Fin d)) (B : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (w' : Fin n' → ℝ) (m' : Fin n' → EuclideanSpace ℝ (Fin d)) (B' : Fin n' → Matrix (Fin d) (Fin d) ℝ),
    (∀ i, 0 < w i) → ∑ i, w i = 1 → (∀ i, (B i).PosDef) → (∀ i, 0 < w' i) → ∑ i, w' i = 1 → (∀ i, (B' i).PosDef) →
      gaussMix w m B ≠ gaussMix w' m' B' →
      ∀ U : Set (EuclideanSpace ℝ (Fin d)), IsOpen U → U.Nonempty → ∃ x ∈ U, gaussMixDens w m B x ≠ gaussMixDens w' m' B' x

/-- L28 (a). Moment matching: for `T > 0`, `N ≥ 1`, every moment vector is matched by exactly one polynomial of degree `< N`. -/
def moment_poly : Prop :=
  ∀ (T : ℝ) (N : ℕ), 0 < T → 1 ≤ N → ∀ M : Fin N → ℝ,
    ∃! G : Polynomial ℝ, G.degree < N ∧ ∀ j : Fin N, ∫ t in (-T)..T, t ^ (j : ℕ) * G.eval t = M j

/-- L28 (b). The scaling between `[−T, T]` and `[−1, 1]`. -/
def moment_poly_scale : Prop :=
  ∀ (T : ℝ) (G : Polynomial ℝ) (j : ℕ), 0 < T →
    ∫ v in (-1 : ℝ)..1, v ^ j * (T * G.eval (T * v)) = T⁻¹ ^ j * ∫ t in (-T)..T, t ^ j * G.eval t ∧
    ∫ v in (-1 : ℝ)..1, |T * G.eval (T * v)| = ∫ t in (-T)..T, |G.eval t|

/-! ### Composed claims -/

/-- L29. The Matérn sentence of Example 5.2 (main :54-56, S4 :27-32) without the bridge: for a Matérn profile `a · G_s(·/ℓ)`, or
any continuous integrable profile with a spectral lower bound, some `g` takes the values `0, 1, −1` on separated sets. -/
def matern_interpolation_free : Prop :=
  ∀ (d : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : EuclideanSpace ℝ (Fin d) → H) (k₀ : EuclideanSpace ℝ (Fin d) → ℝ),
    (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) →
    ((∃ s a ℓ : ℝ, (d : ℝ) / 2 < s ∧ 0 < a ∧ 0 < ℓ ∧ k₀ = maternK s a ℓ) ∨
      (Continuous k₀ ∧ Integrable k₀ ∧ ∃ c s : ℝ, 0 < c ∧ ∀ ξ, c * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) ≤ specDens k₀ ξ)) →
    ∀ (SR SP SQ : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ),
      Bornology.IsBounded SP → Bornology.IsBounded SQ → 0 < ε →
      (∀ x ∈ SR, ∀ y ∈ SP, ε ≤ dist x y) → (∀ x ∈ SR, ∀ y ∈ SQ, ε ≤ dist x y) → (∀ x ∈ SP, ∀ y ∈ SQ, ε ≤ dist x y) →
        ∃ g : H, (∀ x ∈ SR, ⟪g, φ x⟫_ℝ = 0) ∧ (∀ x ∈ SP, ⟪g, φ x⟫_ℝ = 1) ∧ (∀ x ∈ SQ, ⟪g, φ x⟫_ℝ = -1)

/-- L30. Remark S5.6: for the Gaussian kernel on `ℝ^d`, every RKHS function (the witness `d⋆` included) is `C^∞` and vanishes at
infinity; strengthens the certified `Wave31th.gaussian_regular` (`C¹`). -/
def gauss_regular_smooth : Prop :=
  ∀ (d : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : EuclideanSpace ℝ (Fin d) → H) (σ : ℝ),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) →
      ∀ f : H, ContDiff ℝ ∞ (StatFormal.Wave12c.witFn f φ) ∧
        Tendsto (StatFormal.Wave12c.witFn f φ) (comap (fun x => ‖x‖) atTop) (𝓝 0)

end Claims

end StatFormal.Wave31tp
