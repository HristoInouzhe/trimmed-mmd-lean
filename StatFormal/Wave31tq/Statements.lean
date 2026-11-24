import StatFormal.Wave31tp.Statements
import StatFormal.Wave31to.Statements
import StatFormal.Wave31ti.Statements
import StatFormal.Wave31tl.Statements
import StatFormal.Wave30tq.Statements
import StatFormal.Wave30tz.Statements
import StatFormal.Wave30tr.Statements
import StatFormal.Wave30tp.Statements
import Mathlib.Probability.Distributions.Gaussian.Real

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31tq: the Fourier-analytic results of trimmed-mmd (Annals of Statistics version)

Printed source: `~/projects/tmmd-aos-brief/fullstack/NEW_STATEMENTS_31tq.md` (v3, F1 at trimmed-mmd `b3125cf`, re-hashed at `1fbc8df`;
copy in `certify/sources/tmmd-aos-NEW_STATEMENTS-wave31tq.md`). Paper: trimmed-mmd `aos/` at `1fbc8df` (line numbers of that commit;
printed numbers of `aos/main.aux`, `aos/supplement.aux`). Plan: `PLAN_31tq.md`. Composed on the certified classical library of Wave 31tp
(L1–L30) with no textbook bridge.

Claim list (draft numbers Q1–Q29; Q13, Q23 and the parts `newsobolev_cor_rate`, `rate_sobolev`, `exact_sobolev_A`, `rate_gauss_A`,
`rate_gauss_split` dropped with their printed text):
setting and dictionary: `tv_density` (Q1), `spectral_angular` (Q2), `native_angular` (Q3, eq:newnative), `bochner_angular` (Q4,
eq:newbochner), `sobolev_angular` (Q5), `sobolev_needs` (Q6), `kernel_instances` (Q7);
touching contaminations: `newgammaone`, `newgammaone_smooth` (Q8, Prop S4.5 and S4 :371-372);
Sobolev kernels: `translation_intervals` (Q9), `newsobnorm` (Q10, Lemma S4.9), `newsobolev_thm` (Q11, Thm S4.10),
`newsobolev_cor_bounded`, `newsobolev_cor_line`, `newsobolev_cor_OP` (Q12, Cor S4.11);
Gaussian kernel: `bandlimited_angular` (Q14, eq:newbandlim), `bbar_even`, `bandB_facts` (Q15), `newgaussstep` (Q16, Lemma S4.12),
`newgauss_thm`, `newgauss_thm_rho` (Q17, Thm S4.13 and S4 :739-741);
explicit trimmings: `momentdecay_angular` (Q18, eq:newmomentdecay), `newupperone` (Q19, Prop S4.14), `newmoments` (Q20, Prop S4.15);
main-text propositions: `newsobolev`, `newsobolev_E1`, `newsobolev_upper_small` (Q21, Prop 5.5), `newgauss`, `newgauss_margin` (Q22,
Prop 5.6), `sharp_line` (Q24);
rates and the converse: `rate_sobolev_split`, `converse_poly`, `lower_sobolev_A`, `slow_gauss_A` (Q25);
compositions and instances: `excess_sobolev` (Q26, Prop 5.10(ii) under Prop 5.5), `laplace_instances` (Q27), `simulated_pairs` (Q28),
`halfspace_geometry`, `halfspace_pair` (Q29, non-vacuity of Thm S4.10 and Cor S4.11 case 1 in every dimension).

Encodings (declared; details in the source's §A): the paper's angular Fourier transform `ĝ(ξ) = ∫ g e^{−i⟨ξ,x⟩} = 𝓕 g (ξ/2π)` (`ftA`,
`ft2A`, `ftMeasA`, `kHat`, `nativeA`, `sobolevA`); kernels `k(x,y) = k₀(x−y)` as feature maps with Gram `k₀(x−y)` into a complete real
inner-product space (positive definiteness, continuity and boundedness of `φ` are then theorems); separability of `H` assumed exactly in
the claims whose routes use a frozen claim that needs it; "P, Q have densities p, q" = measurable nonnegative `p, q` with
`P = vol.withDensity (ofReal ∘ p)`; `|P − Q|` is Mathlib's total variation of `P − Q` (`absPQ`); signed measures through their Jordan
parts (`ftSigned`, `sMoment`); the rescaled path `D̄_α = (1−α)D_α` is the frozen `Wave31ti.uPath`; "for all small ε" =
`∃ ε₀, 0 < ε₀ ∧ ε₀ ≤ α⋆ ∧ ∀ ε ∈ Ioc 0 ε₀`; "with probability at least 1 − p" = a measurable event of probability `≥ ofReal (1 − p)`;
the split-sample bound `α̂` is `R.alphaLo α δ` for the runs of the certified `Wave31tl.same_rate`; the analytic estimator with `τ^A` alone
is `alphaHat (Demp φ) (tauA κ D · δ n m)`.
Junk values: every `rpow` base is positive where it is read (`|v|^{−2s}` at `v = 0` is a null set); `log` only of arguments `> 1` in the
read range; `sSup` only of nonempty bounded sets; `ft2A` only on L² functions, under `∫⁻` or a.e.; `bandH`, `bandB` take their continuous
values `1/(4π)` at `±π`, where the printed formulas read `0/0`; `bbarE b Ω ⊤ = 0` (`b̄(∞) = 0`); `infDist x (frontier G)` is never read
with `frontier G = ∅` (that forces `P = Q`); `ENNReal.ofReal` of a negative number is `0` (a true, weaker bound).
Declared extra hypotheses (harmless): `0 ≤ Π_ρ`, `0 ≤ V_ρ` in Q11–Q12 (critic B1); `0 < C` in Q19 and Q20(a); `0 < C′` in `ExpTail`.
Freeze-time encodings of the approved prose (the critic-checked scratch shapes are copied verbatim, with `CrossPair` written as
`IsCross … ∧ 0 < p x₀` and the inlined `|P − Q|((x₀ + ρ/2, ∞))`, `‖Δ^m b‖_{L¹}` written as `tailPlus`, `lapC`): Q1 is (a) ∧ (b) under one
name; Q12's two cases do not assume the mollifier `b` and the integer `m` of Theorem S4.10 (neither is in the conclusion: a stronger
statement); Q20 states the main part, (a) and (b) as one claim with `T_N, w_N` chosen before the kernel; Q15(c) takes `ĥ′` as the derivative
of `ĥ = ftA bandH` itself on `(−1/2, 1/2)`; Q7(c) adds positive definiteness of the profile written on `ℝ` (`x²` for `‖x‖²`); Q28 takes the
shift `N(±a, 1)` for every `a > 0` and writes the mixture weights as `ℝ≥0` scalars (the same measures as the `ℝ≥0∞` scalars of the prose,
so that the finite-measure instances of `ExpTail` are found), with the conjuncts that the mixtures are probability measures (needed to
instantiate Props 5.5, 5.6); Q29(b) is (G2) for every `w₀ > 0`, in the form of Theorem S4.10's hypothesis.

FROZEN 2026-11-23 after the independent critic's reviews (`CRITIC_31tq.md` NOT READY, B1 applied; `CRITIC_31tq_v2.md` READY TO FREEZE;
coordinated F1 `CRITIC_F1_b3125cf.md` READY TO FREEZE; diff-only re-check `CRITIC_F1b_1fbc8df.md`: READY TO FREEZE, no text note for 31tq).
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section

open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal NNReal InnerProductSpace ContDiff

namespace StatFormal.Wave31tq

open StatFormal StatFormal.Wave31tp StatFormal.TrimmedMMD.Unconditional

section Defs

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The paper's (angular) Fourier transform `ĝ(ξ) = ∫ g(x) e^{−i⟨ξ,x⟩} dx = 𝓕 g (ξ/2π)` (S4 :309). -/
def ftA (g : V → ℂ) (ξ : V) : ℂ := 𝓕 g ((2 * Real.pi)⁻¹ • ξ)

/-- The angular L² transform `f̂ = 𝓕₂ f (·/2π)` (eq:newnative; junk `0` off L², as `ft2`). -/
def ft2A (f : V → ℂ) (ξ : V) : ℂ := ft2 f ((2 * Real.pi)⁻¹ • ξ)

/-- `k̂₀(ξ)`, the angular spectral density (the real part; `k̂₀` is real, Q2). -/
def kHat (k₀ : V → ℝ) (ξ : V) : ℝ := (ftA (fun x => (k₀ x : ℂ)) ξ).re

/-- The right side of eq:newnative, `(2π)^{−d} ∫ |f̂|² / k̂₀`, in `[0, ∞]`. -/
def nativeA (k₀ : V → ℝ) (f : V → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ Module.finrank ℝ V)⁻¹ * ∫⁻ ξ, ‖ft2A f ξ‖ₑ ^ 2 / ENNReal.ofReal (kHat k₀ ξ)

/-- `‖f‖²_{H^s} = (2π)^{−d} ∫ |f̂|² (1 + |ξ|²)^s` in `[0, ∞]` (S4 :530). -/
def sobolevA (s : ℝ) (f : V → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ Module.finrank ℝ V)⁻¹ *
    ∫⁻ ξ, ‖ft2A f ξ‖ₑ ^ 2 * ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s)

/-- `C_b = ‖Δ^m b‖_{L¹}` (Lemma S4.9), with the real Laplacian of `V → ℝ`. -/
def lapC (m : ℕ) (b : V → ℝ) : ℝ := ∫ x, |((Laplacian.laplacian : (V → ℝ) → (V → ℝ))^[m] b) x|

end Defs

/-- `ν̂(ξ) = ∫ e^{−i⟨ξ,x⟩} dν(x)` for a measure (S4 :317). -/
def ftMeasA {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] (μ : Measure V) (ξ : V) : ℂ :=
  ftMeas μ ((2 * Real.pi)⁻¹ • ξ)

/-- `|P − Q|`, the total variation measure of `P − Q` (main :83). -/
def absPQ {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsFiniteMeasure P] [IsFiniteMeasure Q] : Measure 𝒳 :=
  (P.toSignedMeasure - Q.toSignedMeasure).totalVariation

/-- `T(ρ) = |P − Q|(V ∖ B_{ρ−1})`, `B_ρ` the open ball of radius `ρ` about the centre `c₀` (S4 :583-584). -/
def tailOut {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] (P Q : Measure V) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (c₀ : V) (ρ : ℝ) : ℝ :=
  (absPQ P Q (Metric.ball c₀ (ρ - 1))ᶜ).toReal

/-- `T₊(ρ) = |P − Q|((x₀ + ρ, ∞))` (S4 :675). -/
def tailPlus (P Q : Measure ℝ) [IsFiniteMeasure P] [IsFiniteMeasure Q] (x₀ ρ : ℝ) : ℝ :=
  (absPQ P Q (Ioi (x₀ + ρ))).toReal

/-- The laws of Proposition 5.5 except `p(x₀) > 0` and the tails: densities `p, q`, continuous near `x₀`, `p ≥ q` a.e. on `(x₀, ∞)`,
`p ≤ q` a.e. on `(−∞, x₀)`, `p − q` differentiable at `x₀` with derivative `ℓ₀ > 0`. -/
def IsCross (P Q : Measure ℝ) (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ) : Prop :=
  Measurable p ∧ Measurable q ∧ (∀ x, 0 ≤ p x) ∧ (∀ x, 0 ≤ q x) ∧
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧ Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) ∧
    (∃ r > 0, ContinuousOn p (Ioo (x₀ - r) (x₀ + r)) ∧ ContinuousOn q (Ioo (x₀ - r) (x₀ + r))) ∧
    (∀ᵐ x ∂volume, x₀ < x → q x ≤ p x) ∧ (∀ᵐ x ∂volume, x < x₀ → p x ≤ q x) ∧
    HasDerivAt (fun x => p x - q x) ℓ₀ x₀ ∧ 0 < ℓ₀

/-- The exponential-tail hypothesis of Proposition 5.5: `|P − Q|({|x − x₀| > t}) ≤ C′ e^{−t/C′}` for some `C′ > 0` and all `t > 0`. -/
def ExpTail (P Q : Measure ℝ) [IsFiniteMeasure P] [IsFiniteMeasure Q] (x₀ : ℝ) : Prop :=
  ∃ C' : ℝ, 0 < C' ∧ ∀ t : ℝ, 0 < t → absPQ P Q {x | t < |x - x₀|} ≤ ENNReal.ofReal (C' * Real.exp (-t / C'))

/-- The Fourier transform of a signed measure on `ℝ` through its Jordan parts. -/
def ftSigned (ν : SignedMeasure ℝ) (ξ : ℝ) : ℂ :=
  ftMeasA ν.toJordanDecomposition.posPart ξ - ftMeasA ν.toJordanDecomposition.negPart ξ

/-- `∫ (x − x₀)^j dν` through the Jordan parts. -/
def sMoment (ν : SignedMeasure ℝ) (x₀ : ℝ) (j : ℕ) : ℝ :=
  (∫ x, (x - x₀) ^ j ∂ν.toJordanDecomposition.posPart) - ∫ x, (x - x₀) ^ j ∂ν.toJordanDecomposition.negPart

/-- `c_d = 1 − sup_{y ≥ 1} j_d(y)` (Lemma S4.9). -/
def cJ (d : ℕ) [NeZero d] : ℝ := 1 - sSup (jBall d '' Ici 1)

/-- `C_{d,s,b}` of Lemma S4.9. -/
def sobConst (cd s Cb : ℝ) (m : ℕ) : ℝ :=
  2 ^ (3 * s) / (2 * cd) * (1 / (1 - (2 : ℝ) ^ (1 - 2 * s)) + Cb ^ 2 / (1 - (2 : ℝ) ^ (-(4 * m + 1 - 2 * s))))

/-- `b̄(t) = ∫_t^∞ b`. -/
def bbar (b : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in Ioi t, b x

/-- `b̄(Ω r₀)` with `r₀ ∈ (0, ∞]` (`b̄(∞) = 0`). -/
def bbarE (b : ℝ → ℝ) (Ω : ℝ) (r₀ : ℝ≥0∞) : ℝ := if r₀ = ⊤ then 0 else bbar b (Ω * r₀.toReal)

/-- `h(t) = cos(t/2)/(π² − t²)`, with its continuous value `1/(4π)` at `±π`. -/
def bandH (t : ℝ) : ℝ := if t ^ 2 = Real.pi ^ 2 then 1 / (4 * Real.pi) else Real.cos (t / 2) / (Real.pi ^ 2 - t ^ 2)

/-- The band-limited density `b(t) = 4π cos²(t/2)/(π² − t²)²`, with its continuous value `1/(4π)` at `±π`. -/
def bandB (t : ℝ) : ℝ := if t ^ 2 = Real.pi ^ 2 then 1 / (4 * Real.pi) else
  4 * Real.pi * Real.cos (t / 2) ^ 2 / (Real.pi ^ 2 - t ^ 2) ^ 2

namespace Claims

/-! ### B. Setting and dictionary -/

/-- Q1 `tv_density` (main :57-58, :81-85; S4 :302-304, :609-610). (a) On any measurable space: `|P − Q| = |p − q|·(P + Q)` with the
frozen densities w.r.t. `P + Q`, the frozen `errFn` is the printed `err(f) = ∫ |1_A − f| d|P − Q|`, `|P − Q|(𝒳) = 2α⋆`,
`|P − Q| = (P − P ∧ Q) + (Q − P ∧ Q)` (= `α⋆(P₀ + Q₀)`) and `(P ∧ Q)(𝒳) = 1 − α⋆`. (b) For Lebesgue densities on `V`: `|P − Q|`,
`P ∧ Q`, `P − P ∧ Q` have densities `|p − q|`, `min(p, q)`, `(p − q)₊`, `α⋆ = ∫ (p − q)₊`, and `err(f) = ∫ |1_G − f| |p − q|` for any
`G` with `q ≤ p` a.e. on `G` and `p ≤ q` a.e. off `G`. -/
def tv_density : Prop :=
  (∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    absPQ P Q = (P + Q).withDensity
        (fun x => ENNReal.ofReal |StatFormal.Wave31to.densP P Q x - StatFormal.Wave31to.densQ P Q x|) ∧
    (∀ f : 𝒳 → ℝ, Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      StatFormal.Wave31to.errFn P Q f =
        ∫ x, |(StatFormal.Wave31to.setA P Q).indicator (fun _ => (1 : ℝ)) x - f x| ∂(absPQ P Q)) ∧
    absPQ P Q univ = ENNReal.ofReal (2 * StatFormal.Distances.tvDist P Q) ∧
    absPQ P Q = (P - P ⊓ Q) + (Q - P ⊓ Q) ∧
    (P ⊓ Q) univ = ENNReal.ofReal (1 - StatFormal.Distances.tvDist P Q)) ∧
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (P Q : Measure V) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : V → ℝ),
    Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) → Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
      absPQ P Q = volume.withDensity (fun x => ENNReal.ofReal |p x - q x|) ∧
      P ⊓ Q = volume.withDensity (fun x => ENNReal.ofReal (min (p x) (q x))) ∧
      P - P ⊓ Q = volume.withDensity (fun x => ENNReal.ofReal (max (p x - q x) 0)) ∧
      StatFormal.Distances.tvDist P Q = ∫ x, max (p x - q x) 0 ∧
      ∀ (G : Set V) (f : V → ℝ), MeasurableSet G → Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
        (∀ᵐ x ∂volume, x ∈ G → q x ≤ p x) → (∀ᵐ x ∂volume, x ∉ G → p x ≤ q x) →
          StatFormal.Wave31to.errFn P Q f = ∫ x, |G.indicator (fun _ => (1 : ℝ)) x - f x| * |p x - q x|

/-- Q2 `spectral_angular` (S4 :308-310): for `k₀` continuous, integrable and positive definite, `k̂₀` is real, nonnegative, integrable
and `k₀(z) = (2π)^{−d} ∫ k̂₀(ξ) e^{iξ·z} dξ`; and every feature map with Gram `k₀(x − y)` makes `k₀` positive definite. -/
def spectral_angular : Prop :=
  (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (k₀ : V → ℝ), Continuous k₀ → Integrable k₀ → IsPosDefFun (fun z => (k₀ z : ℂ)) →
      (∀ ξ, (ftA (fun x => (k₀ x : ℂ)) ξ).im = 0 ∧ 0 ≤ kHat k₀ ξ) ∧ Integrable (kHat k₀) ∧
      ∀ z, (k₀ z : ℂ) = ((((2 * Real.pi) ^ Module.finrank ℝ V)⁻¹ : ℝ) : ℂ) *
        ∫ ξ, (kHat k₀ ξ : ℂ) * Complex.exp (Complex.I * (⟪ξ, z⟫_ℝ : ℂ))) ∧
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : V → H) (k₀ : V → ℝ),
    (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → IsPosDefFun (fun z => (k₀ z : ℂ))

/-- Q3 `native_angular` (eq:newnative as printed, S4 :310-316): (a) the dictionary `nativeA = nativeN`, `sobolevA = sobolevS`,
`k̂₀(ξ) = specDens k₀ (ξ/2π)`; (b) every represented function is continuous, in L², with `(2π)^{−d}∫|f̂|²/k̂₀ ≤ ‖g‖²`, equality on the
closed span; (c) a continuous `f` is represented iff it is in L² with finite native functional, and the least representer norm is its
square root (the printed `‖f‖²_ℋ = (2π)^{−d} ∫ |f̂|²/k̂₀`). -/
def native_angular : Prop :=
  (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V],
    (∀ k₀ : V → ℝ, nativeA k₀ = nativeN k₀) ∧ (∀ s : ℝ, sobolevA (V := V) s = sobolevS s) ∧
    ∀ (k₀ : V → ℝ) (ξ : V), kHat k₀ ξ = specDens k₀ ((2 * Real.pi)⁻¹ • ξ)) ∧
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : V → H) (k₀ : V → ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) →
      (∀ g : H, Continuous (fun x => ⟪g, φ x⟫_ℝ) ∧ MemLp (fun x => ⟪g, φ x⟫_ℝ) 2 ∧
        nativeA k₀ (fun x => ((⟪g, φ x⟫_ℝ : ℝ) : ℂ)) ≤ ENNReal.ofReal (‖g‖ ^ 2) ∧
        (g ∈ (Submodule.span ℝ (Set.range φ)).topologicalClosure →
          nativeA k₀ (fun x => ((⟪g, φ x⟫_ℝ : ℝ) : ℂ)) = ENNReal.ofReal (‖g‖ ^ 2))) ∧
      ∀ f : V → ℝ, Continuous f →
        ((∃ g : H, ∀ x, ⟪g, φ x⟫_ℝ = f x) ↔ (MemLp f 2 ∧ nativeA k₀ (fun x => (f x : ℂ)) < ⊤)) ∧
        ((∃ g : H, ∀ x, ⟪g, φ x⟫_ℝ = f x) →
          ∃ g₀ : H, (∀ x, ⟪g₀, φ x⟫_ℝ = f x) ∧ ENNReal.ofReal (‖g₀‖ ^ 2) = nativeA k₀ (fun x => (f x : ℂ)) ∧
            ∀ g : H, (∀ x, ⟪g, φ x⟫_ℝ = f x) → ‖g₀‖ ≤ ‖g‖)

/-- Q4 `bochner_angular` (eq:newbochner as printed, S4 :317-322): for finite measures `μ₁, μ₂` (`ν = μ₁ − μ₂`),
`‖∫φ dν‖² = ∫∫ k₀(x − y) dν dν = (2π)^{−d} ∫ |ν̂|² k̂₀`, the double integral expanded bilinearly. -/
def bochner_angular : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : V → H) (k₀ : V → ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) →
      ∀ (μ₁ μ₂ : Measure V) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂],
        Integrable (fun ξ => kHat k₀ ξ * ‖ftMeasA μ₁ ξ - ftMeasA μ₂ ξ‖ ^ 2) ∧
        ‖∫ x, φ x ∂μ₁ - ∫ x, φ x ∂μ₂‖ ^ 2 =
          (∫ x, ∫ y, k₀ (x - y) ∂μ₁ ∂μ₁) - 2 * (∫ x, ∫ y, k₀ (x - y) ∂μ₂ ∂μ₁) + ∫ x, ∫ y, k₀ (x - y) ∂μ₂ ∂μ₂ ∧
        ‖∫ x, φ x ∂μ₁ - ∫ x, φ x ∂μ₂‖ ^ 2 =
          ((2 * Real.pi) ^ Module.finrank ℝ V)⁻¹ * ∫ ξ, kHat k₀ ξ * ‖ftMeasA μ₁ ξ - ftMeasA μ₂ ξ‖ ^ 2

/-- Q5 `sobolev_angular` (S4 :530-533, :32-33; §1 :82; main :105-109): under `k̂₀(ξ) ≥ c(1 + |ξ|²)^{−s}`: (a) every continuous L² `f`
with `‖f‖_{H^s} < ∞` is represented with `‖f‖²_ℋ ≤ ‖f‖²_{H^s}/c`; (b) the kernel is characteristic (on finite measures, hence (A3)) and
strictly positive definite; (c) with also `k̂₀ ≤ C(1 + |ξ|²)^{−s}`, the RKHS is `H^s` with an equivalent norm; (d) the Matérn profiles
satisfy (c)'s hypotheses with `c = aℓ^d max(1, ℓ²)^{−s}`, `C = aℓ^d max(1, ℓ^{−2})^s`. -/
def sobolev_angular : Prop :=
  (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : V → H) (k₀ : V → ℝ) (c s : ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < c →
    (∀ ξ, c * (1 + ‖ξ‖ ^ 2) ^ (-s) ≤ kHat k₀ ξ) →
      (∀ f : V → ℝ, Continuous f → MemLp f 2 → sobolevA s (fun x => (f x : ℂ)) < ⊤ →
        ∃ g : H, (∀ x, ⟪g, φ x⟫_ℝ = f x) ∧
          ENNReal.ofReal (‖g‖ ^ 2) ≤ sobolevA s (fun x => (f x : ℂ)) / ENNReal.ofReal c) ∧
      ((∀ (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν], ∫ x, φ x ∂μ = ∫ x, φ x ∂ν → μ = ν) ∧
        StatFormal.TrimmedMMD.ZeroSet.Characteristic φ ∧ StatFormal.Wave31tg.StrictlyPDOn φ Set.univ) ∧
      ∀ C : ℝ, (∀ ξ, kHat k₀ ξ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-s)) →
        ∀ f : V → ℝ, Continuous f →
          ((∃ g : H, ∀ x, ⟪g, φ x⟫_ℝ = f x) ↔ (MemLp f 2 ∧ sobolevA s (fun x => (f x : ℂ)) < ⊤)) ∧
          ((∃ g : H, ∀ x, ⟪g, φ x⟫_ℝ = f x) →
            ∃ g₀ : H, (∀ x, ⟪g₀, φ x⟫_ℝ = f x) ∧ (∀ g : H, (∀ x, ⟪g, φ x⟫_ℝ = f x) → ‖g₀‖ ≤ ‖g‖) ∧
              sobolevA s (fun x => (f x : ℂ)) / ENNReal.ofReal C ≤ ENNReal.ofReal (‖g₀‖ ^ 2) ∧
              ENNReal.ofReal (‖g₀‖ ^ 2) ≤ sobolevA s (fun x => (f x : ℂ)) / ENNReal.ofReal c)) ∧
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (s a ℓ : ℝ), (Module.finrank ℝ V : ℝ) / 2 < s → 0 < a → 0 < ℓ →
      Continuous (maternK (V := V) s a ℓ) ∧ Integrable (maternK (V := V) s a ℓ) ∧
      ∀ ξ : V, a * ℓ ^ Module.finrank ℝ V * (max 1 (ℓ ^ 2)) ^ (-s) * (1 + ‖ξ‖ ^ 2) ^ (-s) ≤ kHat (maternK s a ℓ) ξ ∧
        kHat (maternK s a ℓ) ξ ≤ a * ℓ ^ Module.finrank ℝ V * (max 1 (ℓ ^ 2)⁻¹) ^ s * (1 + ‖ξ‖ ^ 2) ^ (-s)

/-- Q6 `sobolev_needs` (S4 :1026-1027, "in `ℝ^d` the margin that Theorem S4.10 gives a transversal crossing guarantees at best
`(n∧m)^{−2/(d+3)}`, as a Sobolev kernel needs `s > d/2`"): for `d ≥ 1`, a lower spectral bound `c(1 + |ξ|²)^{−s}` forces `s > d/2`, hence
`(d+3)/4 < (2s+3)/4` and the rate exponent `2/(2s+3) < 2/(d+3)`. -/
def sobolev_needs : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (k₀ : V → ℝ) (c s : ℝ), 0 < Module.finrank ℝ V → Continuous k₀ → Integrable k₀ →
    IsPosDefFun (fun z => (k₀ z : ℂ)) → 0 < c → (∀ ξ, c * (1 + ‖ξ‖ ^ 2) ^ (-s) ≤ kHat k₀ ξ) →
      (Module.finrank ℝ V : ℝ) / 2 < s ∧ ((Module.finrank ℝ V : ℝ) + 3) / 4 < (2 * s + 3) / 4 ∧
      2 / (2 * s + 3) < 2 / ((Module.finrank ℝ V : ℝ) + 3)

/-- Q7 `kernel_instances` (main :108-109, :131; S4 :376-377, :657, :794-795): (a) the Laplace profile `e^{−|x|/σ}` on `ℝ`:
`k̂₀(ξ) = 2σ/(1 + σ²ξ²)`, Prop 5.5's two-sided bound with `s = 1` and Prop S4.14's bound `k̂₀ ≤ (2/σ)|ξ|^{−2}`; (b) the Matérn profiles:
`k̂₀(ξ) = aℓ^d(1 + ℓ²|ξ|²)^{−s}`; (c) the Gaussian profile: `k̂₀(ξ) = (2πσ²)^{d/2} e^{−σ²|ξ|²/2}`, on `ℝ` `= √(2π)σe^{−σ²ξ²/2}`, with
`M_{2N} = (2π)^{−1} ∫ ξ^{2N} k̂₀ = (2N−1)!! σ^{−2N}`; all three positive definite. -/
def kernel_instances : Prop :=
  (∀ σ : ℝ, 0 < σ →
    Continuous (fun x : ℝ => Real.exp (-|x| / σ)) ∧ Integrable (fun x : ℝ => Real.exp (-|x| / σ)) ∧
    IsPosDefFun (fun z : ℝ => ((Real.exp (-|z| / σ) : ℝ) : ℂ)) ∧
    (∀ ξ : ℝ, kHat (fun x : ℝ => Real.exp (-|x| / σ)) ξ = 2 * σ / (1 + σ ^ 2 * ξ ^ 2)) ∧
    (∀ ξ : ℝ, 2 * σ * min 1 (σ ^ 2)⁻¹ * (1 + ξ ^ 2) ^ (-(1 : ℝ)) ≤ kHat (fun x : ℝ => Real.exp (-|x| / σ)) ξ ∧
      kHat (fun x : ℝ => Real.exp (-|x| / σ)) ξ ≤ 2 * σ * max 1 (σ ^ 2)⁻¹ * (1 + ξ ^ 2) ^ (-(1 : ℝ))) ∧
    ∀ ξ : ℝ, ξ ≠ 0 → kHat (fun x : ℝ => Real.exp (-|x| / σ)) ξ ≤ 2 / σ * |ξ| ^ (-2 * (1 : ℝ))) ∧
  (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (s a ℓ : ℝ), (Module.finrank ℝ V : ℝ) / 2 < s → 0 < a → 0 < ℓ →
      IsPosDefFun (fun z : V => (maternK s a ℓ z : ℂ)) ∧
      ∀ ξ : V, kHat (maternK s a ℓ) ξ = a * ℓ ^ Module.finrank ℝ V * (1 + ℓ ^ 2 * ‖ξ‖ ^ 2) ^ (-s)) ∧
  (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (σ : ℝ), 0 < σ →
      IsPosDefFun (fun z : V => ((Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)) : ℝ) : ℂ)) ∧
      ∀ ξ : V, kHat (fun x : V => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ξ =
        (2 * Real.pi * σ ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) * Real.exp (-(σ ^ 2 * ‖ξ‖ ^ 2 / 2))) ∧
  ∀ σ : ℝ, 0 < σ →
    IsPosDefFun (fun z : ℝ => ((Real.exp (-z ^ 2 / (2 * σ ^ 2)) : ℝ) : ℂ)) ∧
    (∀ ξ : ℝ, kHat (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) ξ =
      √(2 * Real.pi) * σ * Real.exp (-(σ ^ 2 * ξ ^ 2 / 2))) ∧
    ∀ N : ℕ, Integrable (fun ξ : ℝ => ξ ^ (2 * N) * kHat (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) ξ) ∧
      (2 * Real.pi)⁻¹ * ∫ ξ : ℝ, ξ ^ (2 * N) * kHat (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) ξ =
        ((2 * N - 1).doubleFactorial : ℝ) * σ⁻¹ ^ (2 * N)

/-! ### C. Touching contaminations: disjoint supports -/

/-- Q8 `newgammaone` (Proposition S4.5, S4 :374-382): a Sobolev-type kernel on `ℝ^d` (`s > d/2`), `0 < α⋆ < 1`, `supp P₀` compact:
(a) disjoint supports give `f ∈ ℋ`, `0 ≤ f ≤ 1`, `f = 1` on `supp P₀`, `f = 0` on `supp Q₀`; (b) every such `f` gives
`D ≥ D̄_{α⋆−ε} ≥ ε/‖f‖_ℋ` on `[0, α⋆]` and Assumption 5.1 with `γ = 1`, `c₀ = 1/‖f‖_ℋ`; (c) the slope of `D̄` at `α⋆` is positive iff the
supports are disjoint. -/
def newgammaone : Prop :=
  ∀ (d : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V], Module.finrank ℝ V = d →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (φ : V → H) (k₀ : V → ℝ) (c s : ℝ) (P Q : Measure V) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
      Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < c → (d : ℝ) / 2 < s →
      (∀ ξ, c * (1 + ‖ξ‖ ^ 2) ^ (-s) ≤ kHat k₀ ξ) →
      0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 → IsCompact (P - P ⊓ Q).support →
        ((P - P ⊓ Q).support ∩ (Q - P ⊓ Q).support = ∅ →
          ∃ g : H, (∀ x, 0 ≤ ⟪g, φ x⟫_ℝ ∧ ⟪g, φ x⟫_ℝ ≤ 1) ∧ (∀ x ∈ (P - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 1) ∧
            ∀ x ∈ (Q - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 0) ∧
        (∀ g : H, (∀ x, 0 ≤ ⟪g, φ x⟫_ℝ ∧ ⟪g, φ x⟫_ℝ ≤ 1) → (∀ x ∈ (P - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 1) →
            (∀ x ∈ (Q - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 0) →
          g ≠ 0 ∧ (∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
            StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤
              Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ∧
            ε / ‖g‖ ≤ StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε)) ∧
          StatFormal.Wave31ti.PolyMargin φ P Q (1 / ‖g‖) 1) ∧
        ∀ sl : ℝ, Tendsto (fun e => StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - e) / e)
            (𝓝[>] 0) (𝓝 sl) →
          (0 < sl ↔ (P - P ⊓ Q).support ∩ (Q - P ⊓ Q).support = ∅)

/-- Q8 `newgammaone_smooth` (E10, S4 :371-372, "When supp P₀ is compact, the bound is an equivalence for continuous kernels whose RKHS
contains the smooth functions with compact support"): (a)–(c) of `newgammaone` for every continuous, bounded feature map on `ℝ^d`
whose RKHS contains the smooth compactly supported functions. -/
def newgammaone_smooth : Prop :=
  ∀ (d : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : EuclideanSpace ℝ (Fin d) → H) (κ : ℝ) (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    Continuous φ → StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Wave31tg.ContainsSmoothCompact φ →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 → IsCompact (P - P ⊓ Q).support →
      ((P - P ⊓ Q).support ∩ (Q - P ⊓ Q).support = ∅ →
        ∃ g : H, (∀ x, 0 ≤ ⟪g, φ x⟫_ℝ ∧ ⟪g, φ x⟫_ℝ ≤ 1) ∧ (∀ x ∈ (P - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 1) ∧
          ∀ x ∈ (Q - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 0) ∧
      (∀ g : H, (∀ x, 0 ≤ ⟪g, φ x⟫_ℝ ∧ ⟪g, φ x⟫_ℝ ≤ 1) → (∀ x ∈ (P - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 1) →
          (∀ x ∈ (Q - P ⊓ Q).support, ⟪g, φ x⟫_ℝ = 0) →
        g ≠ 0 ∧ (∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
          StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤
            Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ∧
          ε / ‖g‖ ≤ StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε)) ∧
        StatFormal.Wave31ti.PolyMargin φ P Q (1 / ‖g‖) 1) ∧
      ∀ sl : ℝ, Tendsto (fun e => StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - e) / e)
          (𝓝[>] 0) (𝓝 sl) →
        (0 < sl ↔ (P - P ⊓ Q).support ∩ (Q - P ⊓ Q).support = ∅)

/-! ### D. Sobolev kernels -/

/-- Q9 `translation_intervals` (S4 :533-535, the `ℝ` part): for a union `E` of `N` intervals (of any type; disjointness not needed),
`Leb(E △ (E + h)) ≤ 2N|h|`. -/
def translation_intervals : Prop :=
  ∀ (N : ℕ) (I : Fin N → Set ℝ), (∀ i, (I i).OrdConnected) → ∀ h : ℝ,
    volume (symmDiff (⋃ i, I i) ((· - h) ⁻¹' (⋃ i, I i))) ≤ ENNReal.ofReal (2 * N * |h|)

/-- Q10 `newsobnorm` (Lemma S4.9, S4 :537-549): `c_d > 0`, `0 ≤ f_w ≤ 1`, `f_w ∈ C_c^∞`, and for `0 < w ≤ 1`
`‖f_w‖²_{H^s} ≤ 2^s Leb(E) + C_{d,s,b} Π w^{1−2s}`, for every `m` with `4m > 2s − 1`. -/
def newsobnorm : Prop :=
  ∀ (d : ℕ) [NeZero d] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V], Module.finrank ℝ V = d →
    ∀ (s Per : ℝ) (E : Set V) (b : V → ℝ) (m : ℕ), 1 / 2 < s → MeasurableSet E → Bornology.IsBounded E →
      (∀ h : V, volume (symmDiff E ((· - h) ⁻¹' E)) ≤ ENNReal.ofReal (Per * ‖h‖)) →
      ContDiff ℝ ∞ b → (∀ x, 0 ≤ b x) → ∫ x, b x = 1 → Function.support b ⊆ Metric.closedBall 0 1 →
      2 * s - 1 < 4 * m →
        0 < cJ d ∧ ∀ w : ℝ, 0 < w →
          (∀ x, 0 ≤ mollify E (dilateR w b) x ∧ mollify E (dilateR w b) x ≤ 1) ∧
          ContDiff ℝ ∞ (mollify E (dilateR w b)) ∧ HasCompactSupport (mollify E (dilateR w b)) ∧
          (w ≤ 1 → sobolevA s (fun x => (mollify E (dilateR w b) x : ℂ)) ≤
            ENNReal.ofReal (2 ^ s * (volume E).toReal + sobConst (cJ d) s (lapC m b) m * Per * w ^ (1 - 2 * s)))

/-- Q11 `newsobolev_thm` (Theorem S4.10, S4 :586-603), with the B1 guards `0 ≤ Π_ρ`, `0 ≤ V_ρ`: `f_w ∈ ℋ` with
`‖f_w‖²_ℋ ≤ B/c` (printed in the proof), `0 ≤ f_w ≤ 1`, `err(f_w) ≤ ℓV_ρw^{r+1} + T(ρ)`, and
`D ≥ D̄_{α⋆−ε} ≥ c^{1/2}{ε − ℓV_ρw^{r+1} − T(ρ)}₊/B^{1/2}` on `[0, α⋆]`, `B = 2^s Leb(B_ρ) + C_{d,s,b}Π_ρw^{1−2s}`. -/
def newsobolev_thm : Prop :=
  ∀ (d : ℕ) [NeZero d] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V], Module.finrank ℝ V = d →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (φ : V → H) (k₀ : V → ℝ) (c s : ℝ) (P Q : Measure V) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : V → ℝ)
      (G : Set V) (c₀ : V) (ρ r ℓ w₀ Piρ Vρ : ℝ) (b : V → ℝ) (m : ℕ),
      Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < c → (d : ℝ) / 2 < s →
      (∀ ξ, c * (1 + ‖ξ‖ ^ 2) ^ (-s) ≤ kHat k₀ ξ) →
      Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
      P = volume.withDensity (fun x => ENNReal.ofReal (p x)) → Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
      0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      IsOpen G → (∀ᵐ x ∂volume, x ∈ G → q x ≤ p x) → (∀ᵐ x ∂volume, x ∉ G → p x ≤ q x) →
      1 ≤ ρ → 0 < r → 0 < ℓ → 0 < w₀ → w₀ ≤ 1 → 0 ≤ Piρ → 0 ≤ Vρ →
      (∀ h : V, volume (symmDiff (G ∩ Metric.ball c₀ ρ) ((· - h) ⁻¹' (G ∩ Metric.ball c₀ ρ))) ≤ ENNReal.ofReal (Piρ * ‖h‖)) →
      (∀ t ∈ Ioc (0 : ℝ) w₀, volume {x | x ∈ Metric.ball c₀ ρ ∧ Metric.infDist x (frontier G) ≤ t} ≤ ENNReal.ofReal (Vρ * t)) →
      (∀ᵐ x ∂volume, x ∈ Metric.ball c₀ ρ → Metric.infDist x (frontier G) ≤ w₀ →
        |p x - q x| ≤ ℓ * Metric.infDist x (frontier G) ^ r) →
      ContDiff ℝ ∞ b → (∀ x, 0 ≤ b x) → ∫ x, b x = 1 → Function.support b ⊆ Metric.closedBall 0 1 → 2 * s - 1 < 4 * m →
        ∀ w ∈ Ioc (0 : ℝ) w₀,
          let f := mollify (G ∩ Metric.ball c₀ ρ) (dilateR w b)
          let B := 2 ^ s * (volume (Metric.ball c₀ ρ)).toReal + sobConst (cJ d) s (lapC m b) m * Piρ * w ^ (1 - 2 * s)
          (∃ g : H, (∀ x, ⟪g, φ x⟫_ℝ = f x) ∧ ‖g‖ ^ 2 ≤ B / c) ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
          StatFormal.Wave31to.errFn P Q f ≤ ℓ * Vρ * w ^ (r + 1) + tailOut P Q c₀ ρ ∧
          ∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
            StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤
              Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ∧
            √c * max (ε - ℓ * Vρ * w ^ (r + 1) - tailOut P Q c₀ ρ) 0 / √B ≤
              StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε)

/-- Q12 `newsobolev_cor_bounded` (Corollary S4.11, case `T(ρ) = 0`): in the setting of Theorem S4.10 (B1 guards included) with
`|P − Q|` vanishing off `B_{ρ−1}`, `γ = 1 + (2s−1)/{2(r+1)}`: `D̄_{α⋆−ε} ≥ c₁ε^γ` for `ε ≤ ε₁`, Assumption 5.1 with this `γ`, and
`1/(2γ) = (r+1)/{2(r+1)+2s−1}`, `= 2/(2s+3)` at `r = 1`. (The mollifier `b` of the theorem is not in the conclusion and is not assumed.) -/
def newsobolev_cor_bounded : Prop :=
  ∀ (d : ℕ) [NeZero d] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V], Module.finrank ℝ V = d →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (φ : V → H) (k₀ : V → ℝ) (c s : ℝ) (P Q : Measure V) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : V → ℝ)
      (G : Set V) (c₀ : V) (ρ r ℓ w₀ Piρ Vρ : ℝ),
      Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < c → (d : ℝ) / 2 < s →
      (∀ ξ, c * (1 + ‖ξ‖ ^ 2) ^ (-s) ≤ kHat k₀ ξ) →
      Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
      P = volume.withDensity (fun x => ENNReal.ofReal (p x)) → Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
      0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      IsOpen G → (∀ᵐ x ∂volume, x ∈ G → q x ≤ p x) → (∀ᵐ x ∂volume, x ∉ G → p x ≤ q x) →
      1 ≤ ρ → 0 < r → 0 < ℓ → 0 < w₀ → w₀ ≤ 1 → 0 ≤ Piρ → 0 ≤ Vρ →
      (∀ h : V, volume (symmDiff (G ∩ Metric.ball c₀ ρ) ((· - h) ⁻¹' (G ∩ Metric.ball c₀ ρ))) ≤ ENNReal.ofReal (Piρ * ‖h‖)) →
      (∀ t ∈ Ioc (0 : ℝ) w₀, volume {x | x ∈ Metric.ball c₀ ρ ∧ Metric.infDist x (frontier G) ≤ t} ≤ ENNReal.ofReal (Vρ * t)) →
      (∀ᵐ x ∂volume, x ∈ Metric.ball c₀ ρ → Metric.infDist x (frontier G) ≤ w₀ →
        |p x - q x| ≤ ℓ * Metric.infDist x (frontier G) ^ r) →
      tailOut P Q c₀ ρ = 0 →
        let γ := 1 + (2 * s - 1) / (2 * (r + 1))
        (∃ c₁ ε₁ : ℝ, 0 < c₁ ∧ 0 < ε₁ ∧ ε₁ ≤ StatFormal.Distances.tvDist P Q ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₁,
            c₁ * ε ^ γ ≤ StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε)) ∧
        (∃ cm : ℝ, StatFormal.Wave31ti.PolyMargin φ P Q cm γ) ∧
        1 / (2 * γ) = (r + 1) / (2 * (r + 1) + 2 * s - 1) ∧ (r = 1 → 1 / (2 * γ) = 2 / (2 * s + 3))

/-- Q12 `newsobolev_cor_line` (Corollary S4.11, case `d = 1`, `G = (x₀, ∞)`, balls centred at `x₀`, (G3) for every `ρ` with the same
`ℓ, w₀`, `T(ρ) ≤ C_Te^{−ρ/a}`): the same conclusion as `newsobolev_cor_bounded`. -/
def newsobolev_cor_line : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (k₀ : ℝ → ℝ) (c s : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ)
    (x₀ r ℓ w₀ CT a : ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < c → 1 / 2 < s →
    (∀ ξ, c * (1 + ξ ^ 2) ^ (-s) ≤ kHat k₀ ξ) →
    Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) → Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
    (∀ᵐ x ∂volume, x₀ < x → q x ≤ p x) → (∀ᵐ x ∂volume, x ≤ x₀ → p x ≤ q x) →
    0 < r → 0 < ℓ → 0 < w₀ → w₀ ≤ 1 →
    (∀ᵐ x ∂volume, |x - x₀| ≤ w₀ → |p x - q x| ≤ ℓ * |x - x₀| ^ r) →
    0 < CT → 0 < a → (∀ ρ : ℝ, 1 ≤ ρ → tailOut P Q x₀ ρ ≤ CT * Real.exp (-ρ / a)) →
      let γ := 1 + (2 * s - 1) / (2 * (r + 1))
      (∃ c₁ ε₁ : ℝ, 0 < c₁ ∧ 0 < ε₁ ∧ ε₁ ≤ StatFormal.Distances.tvDist P Q ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₁,
          c₁ * ε ^ γ ≤ StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε)) ∧
      (∃ cm : ℝ, StatFormal.Wave31ti.PolyMargin φ P Q cm γ) ∧
      1 / (2 * γ) = (r + 1) / (2 * (r + 1) + 2 * s - 1) ∧ (r = 1 → 1 / (2 * γ) = 2 / (2 * s + 3))

/-- Q12 `newsobolev_cor_OP` (Corollary S4.11, "Hence", S4 :628-630, :646-647): for the split-sample `α̂` computed as in Theorem 5.7 (runs
of `same_rate`) on a grid of `J` levels fixed in advance with mesh `h` below `α⋆`, for fixed `J`: `α̂ ≥ α⋆ − h − O_P((n∧m)^{−1/(2γ)})`,
one-sided, with probability `≥ 1 − η`, given the corollary's margin. -/
def newsobolev_cor_OP : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (c₀ γ : ℝ) (J : ℕ) (δ s2 : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ → StatFormal.Distances.tvDist P Q < 1 →
    1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 →
      ∀ η : ℝ, 0 < η → η < 1 → ∃ (C : ℝ) (n₀ : ℕ), ∀ (n m : ℕ) (α : Fin J → ℝ)
        (R : StatFormal.Wave30tz.LoRun 𝒳 J n m) (h : ℝ), n₀ ≤ min n m →
        StatFormal.Wave30tz.IsGrid α → R.IsWitnessRun φ α δ (1 / 2) s2 → StatFormal.Wave31tl.IsDefaultRun R →
        StatFormal.Wave31tl.MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
          ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
            ENNReal.ofReal (1 - η) ≤ StatFormal.Wave30tp.sampleLaw P Q n m E ∧
            E ⊆ {z | StatFormal.Distances.tvDist P Q - h - C * ((min n m : ℕ) : ℝ) ^ (-(1 / (2 * γ))) ≤
                R.alphaLo α δ z.1 z.2}

/-! ### E. The Gaussian kernel -/

/-- Q14 `bandlimited_angular` (eq:newbandlim as printed, S4 :656-664): for the Gaussian kernel on `ℝ`, every continuous L² `f` whose
transform vanishes outside `[−Ω, Ω]` is represented with `‖f‖²_ℋ ≤ e^{σ²Ω²/2}/((2π)^{1/2}σ) ‖f‖²_{L²}`. -/
def bandlimited_angular : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : ℝ → H) (σ Ω : ℝ),
    0 < σ → 0 ≤ Ω → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) →
      ∀ f : ℝ → ℝ, Continuous f → MemLp f 2 → (∀ᵐ ξ ∂volume, Ω < |ξ| → ft2A (fun x => (f x : ℂ)) ξ = 0) →
        ∃ g : H, (∀ x, ⟪g, φ x⟫_ℝ = f x) ∧
          ‖g‖ ^ 2 ≤ Real.exp (σ ^ 2 * Ω ^ 2 / 2) / (√(2 * Real.pi) * σ) * ∫ x, f x ^ 2

/-- Q15 `bbar_even` (S4 :664-666, :674): for an even probability density `b`, `b̄ ≤ 1/2` on `[0, ∞)`, `b̄` is nonincreasing there and
`b̄(∞) = 0`. -/
def bbar_even : Prop :=
  ∀ b : ℝ → ℝ, Measurable b → (∀ t, 0 ≤ b t) → ∫ t, b t = 1 → (∀ t, b (-t) = b t) →
    (∀ t, 0 ≤ t → bbar b t ≤ 1 / 2) ∧ AntitoneOn (bbar b) (Ici 0) ∧ Tendsto (bbar b) atTop (𝓝 0)

/-- Q15 `bandB_facts` (S4 :664-670): the density `b = 4π cos²(t/2)/(π² − t²)²`. (a) `h = cos(t/2)/(π² − t²)` is continuous, integrable,
square integrable, `ĥ = cos(πξ)` on `[−1/2, 1/2]` and `0` elsewhere, `‖h‖²_{L²} = 1/(4π)`, `b = h²/‖h‖²`; (b) `b` is a continuous, bounded,
even probability density with `b̂` real, `b̂ = 0` off `[−1, 1]`, `b̂ = (2π)^{−1}·4π·(ĥ ⋆ ĥ)`; (c) `m₂ = ∫ t²b = π² = ∫|ĥ′|²/∫|ĥ|²`;
(d) for `t ≥ 2^{1/2}π`: `t² − π² ≥ t²/2`, `b(t) ≤ 16πt^{−4}`, `b̄(t) ≤ 16π/(3t³)`. -/
def bandB_facts : Prop :=
  (Continuous bandH ∧ Integrable bandH ∧ Integrable (fun t => bandH t ^ 2) ∧
    (∀ ξ : ℝ, |ξ| ≤ 1 / 2 → ftA (fun t => (bandH t : ℂ)) ξ = (Real.cos (Real.pi * ξ) : ℂ)) ∧
    (∀ ξ : ℝ, 1 / 2 < |ξ| → ftA (fun t => (bandH t : ℂ)) ξ = 0) ∧
    ∫ t, bandH t ^ 2 = 1 / (4 * Real.pi) ∧ bandB = fun t => bandH t ^ 2 / ∫ u, bandH u ^ 2) ∧
  (Continuous bandB ∧ BddAbove (Set.range bandB) ∧ (∀ t, bandB (-t) = bandB t) ∧ (∀ t, 0 ≤ bandB t) ∧
    Integrable bandB ∧ ∫ t, bandB t = 1 ∧ (∀ ξ : ℝ, (ftA (fun t => (bandB t : ℂ)) ξ).im = 0) ∧
    (∀ ξ : ℝ, 1 < |ξ| → ftA (fun t => (bandB t : ℂ)) ξ = 0) ∧
    ∀ ξ : ℝ, ftA (fun t => (bandB t : ℂ)) ξ =
      (((2 * Real.pi)⁻¹ * (4 * Real.pi) : ℝ) : ℂ) *
        ∫ η : ℝ, ftA (fun t => (bandH t : ℂ)) η * ftA (fun t => (bandH t : ℂ)) (ξ - η)) ∧
  (Integrable (fun t => t ^ 2 * bandB t) ∧ ∫ t, t ^ 2 * bandB t = Real.pi ^ 2 ∧
    (∀ ξ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2),
      HasDerivAt (ftA (fun t => (bandH t : ℂ))) ((-(Real.pi * Real.sin (Real.pi * ξ)) : ℝ) : ℂ) ξ) ∧
    Real.pi ^ 2 = (∫ ξ in (-(1 / 2) : ℝ)..(1 / 2), ‖deriv (ftA (fun t => (bandH t : ℂ))) ξ‖ ^ 2) /
      ∫ ξ : ℝ, ‖ftA (fun t => (bandH t : ℂ)) ξ‖ ^ 2) ∧
  ∀ t : ℝ, √2 * Real.pi ≤ t →
    t ^ 2 / 2 ≤ t ^ 2 - Real.pi ^ 2 ∧ bandB t ≤ 16 * Real.pi / t ^ 4 ∧ bbar bandB t ≤ 16 * Real.pi / (3 * t ^ 3)

/-- Q16 `newgaussstep` (Lemma S4.12, S4 :677-684, setting :664-666, :672-675): for `Ω, ρ > 0`, `f = 1_{(x₀,x₀+ρ)} ∗ b_Ω` lies in `ℋ`
with `‖f‖²_ℋ ≤ ρe^{σ²Ω²/2}/{(2π)^{1/2}σ}`, `0 ≤ f ≤ 1`, and `err(f) ≤ ℓm₂/(2Ω²) + 2T₊(ρ/2) + 2α⋆{b̄(Ωr₀) + b̄(Ωρ/2)}`. -/
def newgaussstep : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : ℝ → H) (σ : ℝ)
    (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q b : ℝ → ℝ) (x₀ ℓ : ℝ) (r₀ : ℝ≥0∞),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) →
    Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) → Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
    (∀ᵐ x ∂volume, x₀ < x → q x ≤ p x) → (∀ᵐ x ∂volume, x < x₀ → p x ≤ q x) → 0 < ℓ → 0 < r₀ →
    (∀ᵐ x ∂volume, ENNReal.ofReal |x - x₀| ≤ r₀ → |p x - q x| ≤ ℓ * |x - x₀|) →
    Measurable b → (∀ t, 0 ≤ b t) → ∫ t, b t = 1 → (∀ t, b (-t) = b t) →
    (∀ ξ : ℝ, 1 < |ξ| → ftA (fun t => (b t : ℂ)) ξ = 0) → Integrable (fun t => t ^ 2 * b t) →
      ∀ Ω ρ : ℝ, 0 < Ω → 0 < ρ →
        (∃ g : H, (∀ x, ⟪g, φ x⟫_ℝ = mollify (Ioo x₀ (x₀ + ρ)) (dilateR Ω⁻¹ b) x) ∧
          ‖g‖ ^ 2 ≤ ρ * Real.exp (σ ^ 2 * Ω ^ 2 / 2) / (√(2 * Real.pi) * σ)) ∧
        (∀ x, 0 ≤ mollify (Ioo x₀ (x₀ + ρ)) (dilateR Ω⁻¹ b) x ∧ mollify (Ioo x₀ (x₀ + ρ)) (dilateR Ω⁻¹ b) x ≤ 1) ∧
        StatFormal.Wave31to.errFn P Q (mollify (Ioo x₀ (x₀ + ρ)) (dilateR Ω⁻¹ b)) ≤
          ℓ * (∫ t, t ^ 2 * b t) / (2 * Ω ^ 2) + 2 * tailPlus P Q x₀ (ρ / 2) +
            2 * StatFormal.Distances.tvDist P Q * (bbarE b Ω r₀ + bbar b (Ω * ρ / 2))

/-- Q17 `newgauss_thm` (Theorem S4.13, S4 :705-711; and S4 :739-741): under the condition on `ρ`,
`D ≥ D̄_{α⋆−ε} ≥ ((1−θ)ε/2){(2π)^{1/2}σ/ρ}^{1/2} exp(−σ²ℓm₂/(8θε))`, and the same lower bound holds for `ω_ℋ(ε)` (`xiH`). -/
def newgauss_thm : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (σ : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q b : ℝ → ℝ)
    (x₀ ℓ : ℝ) (r₀ : ℝ≥0∞),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) →
    Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) → Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
    (∀ᵐ x ∂volume, x₀ < x → q x ≤ p x) → (∀ᵐ x ∂volume, x < x₀ → p x ≤ q x) → 0 < ℓ → 0 < r₀ →
    (∀ᵐ x ∂volume, ENNReal.ofReal |x - x₀| ≤ r₀ → |p x - q x| ≤ ℓ * |x - x₀|) →
    Measurable b → (∀ t, 0 ≤ b t) → ∫ t, b t = 1 → (∀ t, b (-t) = b t) →
    (∀ ξ : ℝ, 1 < |ξ| → ftA (fun t => (b t : ℂ)) ξ = 0) → Integrable (fun t => t ^ 2 * b t) →
      ∀ θ ε ρ : ℝ, 0 < θ → θ < 1 → 0 < ε → ε ≤ StatFormal.Distances.tvDist P Q → 0 < ρ →
        let m₂ := ∫ t, t ^ 2 * b t
        let Ω := √(ℓ * m₂ / (2 * θ * ε))
        2 * tailPlus P Q x₀ (ρ / 2) +
            2 * StatFormal.Distances.tvDist P Q * (bbarE b Ω r₀ + bbar b (Ω * ρ / 2)) ≤ (1 - θ) * ε / 2 →
          StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤
              Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ∧
            (1 - θ) * ε / 2 * √(√(2 * Real.pi) * σ / ρ) * Real.exp (-(σ ^ 2 * ℓ * m₂ / (8 * θ * ε))) ≤
              StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ∧
            (1 - θ) * ε / 2 * √(√(2 * Real.pi) * σ / ρ) * Real.exp (-(σ ^ 2 * ℓ * m₂ / (8 * θ * ε))) ≤
              StatFormal.Wave31to.xiH φ P Q ε

/-- Q17 `newgauss_thm_rho` (Theorem S4.13, S4 :711-715): with `b` the density of Q15 (`m₂ = π²`) and `T₊(t) ≤ C_Te^{−t/a}`,
(a) `ρ_ε = max{2, 2a log(8C_T/((1−θ)ε))}` satisfies the condition for all small `ε`, and
(b) `log{1/D̄_{α⋆−ε}} ≤ σ²ℓπ²/(8θε) + log(1/ε) + O(log log(1/ε))`. -/
def newgauss_thm_rho : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (σ : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ)
    (x₀ ℓ : ℝ) (r₀ : ℝ≥0∞) (CT a θ : ℝ),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) →
    Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) → Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
    (∀ᵐ x ∂volume, x₀ < x → q x ≤ p x) → (∀ᵐ x ∂volume, x < x₀ → p x ≤ q x) → 0 < ℓ → 0 < r₀ →
    (∀ᵐ x ∂volume, ENNReal.ofReal |x - x₀| ≤ r₀ → |p x - q x| ≤ ℓ * |x - x₀|) →
    0 < CT → 0 < a → (∀ t : ℝ, 0 < t → tailPlus P Q x₀ t ≤ CT * Real.exp (-t / a)) →
    0 < θ → θ < 1 → 0 < StatFormal.Distances.tvDist P Q →
      (∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ ε ∈ Ioc (0 : ℝ) (min ε₂ (StatFormal.Distances.tvDist P Q)),
        let ρ := max 2 (2 * a * Real.log (8 * CT / ((1 - θ) * ε)))
        let Ω := √(ℓ * Real.pi ^ 2 / (2 * θ * ε))
        2 * tailPlus P Q x₀ (ρ / 2) +
            2 * StatFormal.Distances.tvDist P Q * (bbarE bandB Ω r₀ + bbar bandB (Ω * ρ / 2)) ≤ (1 - θ) * ε / 2) ∧
      ∃ C ε₃ : ℝ, 0 < ε₃ ∧ ε₃ < Real.exp (-1) ∧ ε₃ ≤ StatFormal.Distances.tvDist P Q ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₃,
        0 < StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ∧
        Real.log (1 / StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε)) ≤
          σ ^ 2 * ℓ * Real.pi ^ 2 / (8 * θ * ε) + Real.log (1 / ε) + C * Real.log (Real.log (1 / ε))

/-! ### F. Explicit trimmings and sharpness -/

/-- Q18 `momentdecay_angular` (eq:newmomentdecay as printed, S4 :749-756): (a) for `ν` with support in `[x₀ − W, x₀ + W]` and vanishing
moments of order `< N`, `|ν̂(ξ)| ≤ |ν| min{1, (|ξ|W)^N/N!}`; (b) `ν̂` of `P′ − Q′` is the difference of the transforms. -/
def momentdecay_angular : Prop :=
  (∀ (ν : SignedMeasure ℝ) (x₀ W : ℝ) (N : ℕ), 0 ≤ W → 1 ≤ N →
    ν.totalVariation (Icc (x₀ - W) (x₀ + W))ᶜ = 0 → (∀ j < N, sMoment ν x₀ j = 0) →
      ∀ ξ : ℝ, ‖ftSigned ν ξ‖ ≤ (ν.totalVariation univ).toReal * min 1 ((|ξ| * W) ^ N / N.factorial)) ∧
  ∀ (P' Q' : Measure ℝ) [IsFiniteMeasure P'] [IsFiniteMeasure Q'],
    ftSigned (P'.toSignedMeasure - Q'.toSignedMeasure) = fun ξ => ftMeasA P' ξ - ftMeasA Q' ξ

/-- Q19 `newupperone` (Proposition S4.14, S4 :758-766): for `k̂₀(ξ) ≤ C|ξ|^{−2s}`, `s ∈ (1/2, 3/2)`, and `p − q` vanishing exactly to order
`r` at `x₀` from both sides, `D̄_{α⋆−ε} ≤ 2εW_ε^{s−1/2}{(C/2π)(2/(3−2s) + 2/(2s−1))}^{1/2}` for `0 < ε ≤ ℓ′r₀^{r+1}/(r+1)`,
`W_ε = {(r+1)ε/ℓ′}^{1/(r+1)}`; with the printed integral. -/
def newupperone : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : ℝ → H) (k₀ : ℝ → ℝ) (C s : ℝ)
    (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ' r r₀ : ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < C → 1 / 2 < s → s < 3 / 2 →
    (∀ ξ : ℝ, ξ ≠ 0 → kHat k₀ ξ ≤ C * |ξ| ^ (-2 * s)) →
    Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) → Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
    0 < ℓ' → 0 < r → 0 < r₀ →
    (∀ᵐ x ∂volume, x ∈ Ioo x₀ (x₀ + r₀) → ℓ' * (x - x₀) ^ r ≤ p x - q x) →
    (∀ᵐ x ∂volume, x ∈ Ioo (x₀ - r₀) x₀ → ℓ' * (x₀ - x) ^ r ≤ q x - p x) →
      ∀ ε ∈ Ioc (0 : ℝ) (ℓ' * r₀ ^ (r + 1) / (r + 1)),
        let W := ((r + 1) * ε / ℓ') ^ (1 / (r + 1))
        ε ≤ StatFormal.Distances.tvDist P Q ∧
        StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤
          2 * ε * W ^ (s - 1 / 2) * √(C / (2 * Real.pi) * (2 / (3 - 2 * s) + 2 / (2 * s - 1))) ∧
        ∫ ξ : ℝ, min 1 (ξ ^ 2 * W ^ 2) * |ξ| ^ (-2 * s) = W ^ (2 * s - 1) * (2 / (3 - 2 * s) + 2 / (2 * s - 1))

/-- Q20 `newmoments` (Proposition S4.15, S4 :782-797): for every `N ≥ 1` there are `T_N ≥ 1`, `w_N > 0` and, for `0 < w ≤ w_N`, trimmings
`P′ ≤ P`, `Q′ ≤ Q` of mass `1 − α⋆ + ε(w)`, `ε(w) ≥ ℓ₀w²/8`, whose difference `ν` has `|ν| ≤ 2ℓ₀w²`, support in `[x₀ − T_Nw, x₀ + T_Nw]`
and vanishing moments of order `< N`; consequently, with `w = (8ε/ℓ₀)^{1/2}`: (a) for `k̂₀ ≤ C(1 + ξ²)^{−s}`, `N > s − 1/2`,
`D̄_{α⋆−ε} ≤ 2ℓ₀w²(T_Nw)^{s−1/2}{CI_{N,s}/(2π)}^{1/2} ≤ Kε^{(2s+3)/4}`; (b) for `M_{2N} < ∞`,
`D̄_{α⋆−ε} ≤ 2ℓ₀w²(T_Nw)^N M_{2N}^{1/2}/N! ≤ Kε^{1+N/2}`. -/
def newmoments : Prop :=
  ∀ (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ r₀ ℓ₀ : ℝ),
    Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) → Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
    0 < r₀ → ContinuousOn p (Ioo (x₀ - r₀) (x₀ + r₀)) → ContinuousOn q (Ioo (x₀ - r₀) (x₀ + r₀)) →
    HasDerivAt (fun x => p x - q x) ℓ₀ x₀ → 0 < ℓ₀ → p x₀ = q x₀ → 0 < p x₀ →
      ∀ N : ℕ, 1 ≤ N → ∃ TN wN : ℝ, 1 ≤ TN ∧ 0 < wN ∧
        (∀ w ∈ Ioc (0 : ℝ) wN,
          ∃ (P' Q' : FiniteMeasure ℝ) (e : ℝ), (P' : Measure ℝ) ≤ P ∧ (Q' : Measure ℝ) ≤ Q ∧
            ℓ₀ * w ^ 2 / 8 ≤ e ∧ (P' : Measure ℝ) univ = ENNReal.ofReal (1 - StatFormal.Distances.tvDist P Q + e) ∧
            (Q' : Measure ℝ) univ = ENNReal.ofReal (1 - StatFormal.Distances.tvDist P Q + e) ∧
            ((P' : Measure ℝ).toSignedMeasure - (Q' : Measure ℝ).toSignedMeasure).totalVariation univ ≤
              ENNReal.ofReal (2 * ℓ₀ * w ^ 2) ∧
            ((P' : Measure ℝ).toSignedMeasure - (Q' : Measure ℝ).toSignedMeasure).totalVariation
              (Icc (x₀ - TN * w) (x₀ + TN * w))ᶜ = 0 ∧
            ∀ j < N, sMoment ((P' : Measure ℝ).toSignedMeasure - (Q' : Measure ℝ).toSignedMeasure) x₀ j = 0) ∧
        (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
          (φ : ℝ → H) (k₀ : ℝ → ℝ) (C s : ℝ),
          Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < C → 1 / 2 < s → s - 1 / 2 < (N : ℝ) →
          (∀ ξ, kHat k₀ ξ ≤ C * (1 + ξ ^ 2) ^ (-s)) →
            Integrable (fun v : ℝ => min 1 (v ^ (2 * N) / (N.factorial : ℝ) ^ 2) * |v| ^ (-2 * s)) ∧
            ∃ K : ℝ, ∀ ε ∈ Ioc (0 : ℝ) (ℓ₀ * wN ^ 2 / 8),
              let w := √(8 * ε / ℓ₀)
              let I := ∫ v : ℝ, min 1 (v ^ (2 * N) / (N.factorial : ℝ) ^ 2) * |v| ^ (-2 * s)
              StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤
                2 * ℓ₀ * w ^ 2 * (TN * w) ^ (s - 1 / 2) * √(C * I / (2 * Real.pi)) ∧
              2 * ℓ₀ * w ^ 2 * (TN * w) ^ (s - 1 / 2) * √(C * I / (2 * Real.pi)) ≤ K * ε ^ ((2 * s + 3) / 4)) ∧
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
          (φ : ℝ → H) (k₀ : ℝ → ℝ),
          Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) →
          Integrable (fun ξ : ℝ => ξ ^ (2 * N) * kHat k₀ ξ) →
            ∃ K : ℝ, ∀ ε ∈ Ioc (0 : ℝ) (ℓ₀ * wN ^ 2 / 8),
              let w := √(8 * ε / ℓ₀)
              let M := (2 * Real.pi)⁻¹ * ∫ ξ : ℝ, ξ ^ (2 * N) * kHat k₀ ξ
              StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤
                2 * ℓ₀ * w ^ 2 * (TN * w) ^ N * √M / (N.factorial : ℝ) ∧
              2 * ℓ₀ * w ^ 2 * (TN * w) ^ N * √M / (N.factorial : ℝ) ≤ K * ε ^ (1 + (N : ℝ) / 2)

/-! ### G. The main-text propositions -/

/-- Q21 `newsobolev` (Proposition 5.5, main :105-117): for a Sobolev kernel of order `s > 1/2` on `ℝ` and the laws of Prop 5.5,
`0 < α⋆ < 1` and `c₁ε^{(2s+3)/4} ≤ D_{α⋆−ε} ≤ c₂ε^{(2s+3)/4}` for all small `ε`. -/
def newsobolev : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (k₀ : ℝ → ℝ) (c C s : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < c → 1 / 2 < s →
    (∀ ξ, c * (1 + ξ ^ 2) ^ (-s) ≤ kHat k₀ ξ ∧ kHat k₀ ξ ≤ C * (1 + ξ ^ 2) ^ (-s)) →
    IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ →
      0 < StatFormal.Distances.tvDist P Q ∧ StatFormal.Distances.tvDist P Q < 1 ∧
      ∃ c₁ c₂ ε₀ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < ε₀ ∧ ε₀ ≤ StatFormal.Distances.tvDist P Q ∧
        ∀ ε ∈ Ioc (0 : ℝ) ε₀,
          c₁ * ε ^ ((2 * s + 3) / 4) ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ∧
          Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤ c₂ * ε ^ ((2 * s + 3) / 4)

/-- Q21 `newsobolev_E1` (main :119-120): under Prop 5.5's hypotheses Assumption 5.1 holds with `γ = (2s+3)/4` and with no smaller
exponent. -/
def newsobolev_E1 : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (k₀ : ℝ → ℝ) (c C s : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < c → 1 / 2 < s →
    (∀ ξ, c * (1 + ξ ^ 2) ^ (-s) ≤ kHat k₀ ξ ∧ kHat k₀ ξ ≤ C * (1 + ξ ^ 2) ^ (-s)) →
    IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ →
      (∃ c₀ : ℝ, StatFormal.Wave31ti.PolyMargin φ P Q c₀ ((2 * s + 3) / 4)) ∧
      ∀ γ' c₀' : ℝ, γ' < (2 * s + 3) / 4 → ¬ StatFormal.Wave31ti.PolyMargin φ P Q c₀' γ'

/-- Q21 `newsobolev_upper_small` (S4 :841-842, "For s < 3/2 and α⋆ < 1, Proposition S4.14 with r = 1 already gives the upper bound,
without p(x₀) > 0"): for `s ∈ (1/2, 3/2)`, the upper spectral bound and the crossing laws (no `p(x₀) > 0`, no lower spectral bound, no
tails), `D̄_{α⋆−ε} ≤ c₂ε^{(2s+3)/4}` for small `ε`, and if `α⋆ < 1`, `D_{α⋆−ε} ≤ c₂(1−α⋆)^{−1}ε^{(2s+3)/4}`. -/
def newsobolev_upper_small : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (k₀ : ℝ → ℝ) (C s : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 1 / 2 < s → s < 3 / 2 →
    (∀ ξ, kHat k₀ ξ ≤ C * (1 + ξ ^ 2) ^ (-s)) → IsCross P Q p q x₀ ℓ₀ →
      ∃ c₂ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ StatFormal.Distances.tvDist P Q ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₀,
        StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤ c₂ * ε ^ ((2 * s + 3) / 4) ∧
        (StatFormal.Distances.tvDist P Q < 1 →
          Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤
            c₂ * (1 - StatFormal.Distances.tvDist P Q)⁻¹ * ε ^ ((2 * s + 3) / 4))

/-- Q22 `newgauss` (Proposition 5.6, main :128-136): for the Gaussian kernel and the laws of Prop 5.5, for every `c > π²σ²ℓ₀/8` and
`N ≥ 1`, `exp(−c/ε) ≤ D_{α⋆−ε} ≤ C_Nε^N` for `0 < ε ≤ ε₀`. -/
def newgauss : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (σ : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) →
    IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ →
      ∀ c : ℝ, Real.pi ^ 2 * σ ^ 2 * ℓ₀ / 8 < c → ∀ N : ℕ, 1 ≤ N →
        ∃ ε₀ CN : ℝ, 0 < ε₀ ∧ ε₀ ≤ StatFormal.Distances.tvDist P Q ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₀,
          Real.exp (-c / ε) ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ∧
          Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤ CN * ε ^ N

/-- Q22 `newgauss_margin` (main :138, :257-258): (a) the path leaves zero faster than every power; (c) a margin of exponential type holds
on `(0, α⋆]`. -/
def newgauss_margin : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (σ : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) →
    IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ →
      (∀ N : ℕ, Tendsto (fun ε => Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) / ε ^ N) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ c : ℝ, Real.pi ^ 2 * σ ^ 2 * ℓ₀ / 8 < c → ∃ c'' : ℝ, 0 < c'' ∧
        ∀ ε ∈ Ioc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
          c'' * Real.exp (-c / ε) ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε)

/-- Q24 `sharp_line` (main :124-126, "sharp on the line at least when s < 3/2"): for `s ∈ (1/2, 3/2)` and `p − q` vanishing exactly to
order `r` at `x₀`, `c₁ε^γ ≤ D̄_{α⋆−ε} ≤ c₂ε^γ` with `γ = 1 + (2s−1)/{2(r+1)}`; Assumption 5.1 holds with this `γ` and no smaller one. -/
def sharp_line : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (k₀ : ℝ → ℝ) (c C s : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p q : ℝ → ℝ) (x₀ r w₀ ℓ' ℓ CT a : ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < c → 0 < C → 1 / 2 < s → s < 3 / 2 →
    (∀ ξ, c * (1 + ξ ^ 2) ^ (-s) ≤ kHat k₀ ξ) → (∀ ξ : ℝ, ξ ≠ 0 → kHat k₀ ξ ≤ C * |ξ| ^ (-2 * s)) →
    Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) → Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
    (∀ᵐ x ∂volume, x₀ < x → q x ≤ p x) → (∀ᵐ x ∂volume, x < x₀ → p x ≤ q x) →
    0 < r → 0 < w₀ → w₀ ≤ 1 → 0 < ℓ' → ℓ' ≤ ℓ →
    (∀ᵐ x ∂volume, |x - x₀| < w₀ → ℓ' * |x - x₀| ^ r ≤ |p x - q x| ∧ |p x - q x| ≤ ℓ * |x - x₀| ^ r) →
    0 < CT → 0 < a → (∀ ρ : ℝ, 1 ≤ ρ → tailOut P Q x₀ ρ ≤ CT * Real.exp (-ρ / a)) →
      let γ := 1 + (2 * s - 1) / (2 * (r + 1))
      (∃ c₁ c₂ ε₁ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < ε₁ ∧ ε₁ ≤ StatFormal.Distances.tvDist P Q ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₁,
          c₁ * ε ^ γ ≤ StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ∧
          StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤ c₂ * ε ^ γ) ∧
      (∃ c₀ : ℝ, StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ) ∧
      ∀ γ' c₀' : ℝ, γ' < γ → ¬ StatFormal.Wave31ti.PolyMargin φ P Q c₀' γ'

/-! ### H. Rates under Propositions 5.5 and 5.6 and the converse -/

/-- Q25 (b) `rate_sobolev_split` (main :240-242): under Prop 5.5's hypotheses, Theorem 5.7 guarantees at least the rate
`(n∧m)^{−2/(2s+3)}` up to the mesh, for every run of `same_rate`, with probability `≥ 1 − δ − η`. -/
def rate_sobolev_split : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (k₀ : ℝ → ℝ) (c C s κ : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ) (J : ℕ) (δ s2 η : ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < c → 1 / 2 < s →
    (∀ ξ, c * (1 + ξ ^ 2) ^ (-s) ≤ kHat k₀ ξ ∧ kHat k₀ ξ ≤ C * (1 + ξ ^ 2) ^ (-s)) →
    IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ → (∀ x, ‖φ x‖ ≤ κ) →
    1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < η → η < 1 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (n m : ℕ) (α : Fin J → ℝ) (R : StatFormal.Wave30tz.LoRun ℝ J n m) (h : ℝ),
        StatFormal.Wave30tz.IsGrid α → R.IsWitnessRun φ α δ (1 / 2) s2 → StatFormal.Wave31tl.IsDefaultRun R →
        1 ≤ n → 1 ≤ m → StatFormal.Wave31tl.MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
          ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
            ENNReal.ofReal (1 - δ - η) ≤ StatFormal.Wave30tp.sampleLaw P Q n m E ∧
            E ⊆ {z | StatFormal.Distances.tvDist P Q - h - K * ((min n m : ℕ) : ℝ) ^ (-(2 / (2 * s + 3))) ≤
                R.alphaLo α δ z.1 z.2 ∧ R.alphaLo α δ z.1 z.2 ≤ StatFormal.Distances.tvDist P Q}

/-- Q25 (c1) `converse_poly` (S4 :847-849, :882-884 in general form): an upper bound `D_{α⋆−ε} ≤ c₂ε^γ` on `(0, ε₀]` gives, with probability
`≥ 1 − δ′`, `α⋆ − α̂_an^A ≥ min{α⋆, ε₀, (g_{n,m}/c₂)^{1/γ}}`. -/
def converse_poly : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ δ' c₂ γ ε₀ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    0 < δ → δ < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m → 0 < c₂ → 0 < γ → 0 < ε₀ → ε₀ ≤ StatFormal.Distances.tvDist P Q →
    (∀ ε ∈ Ioc (0 : ℝ) ε₀, Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤ c₂ * ε ^ γ) →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ') ≤ StatFormal.Wave30tp.sampleLaw P Q n m E ∧
        ∀ z ∈ E, min (StatFormal.Distances.tvDist P Q) (min ε₀ ((StatFormal.Wave31to.gNM D δ δ' n m / c₂) ^ (1 / γ))) ≤
          StatFormal.Distances.tvDist P Q -
            StatFormal.TrimmedMMD.alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tr.tauA κ D α δ n m)

/-- Q25 (c3) `lower_sobolev_A` (S4 :882-885; main :246-248, Sobolev half): under Prop 5.5's hypotheses the error of `α̂_an^A` is at least
of order `(n∧m)^{−2/(2s+3)}` with probability `≥ 1 − δ′`. -/
def lower_sobolev_A : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (k₀ : ℝ → ℝ) (c C s κ D δ δ' : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < c → 1 / 2 < s →
    (∀ ξ, c * (1 + ξ ^ 2) ^ (-s) ≤ kHat k₀ ξ ∧ kHat k₀ ξ ≤ C * (1 + ξ ^ 2) ^ (-s)) →
    IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ →
    (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 0 < δ → δ < δ' → δ' < 1 →
      ∃ (C₁ : ℝ) (n₀ : ℕ), 0 < C₁ ∧ ∀ n m : ℕ, n₀ ≤ min n m →
        ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ') ≤ StatFormal.Wave30tp.sampleLaw P Q n m E ∧
          E ⊆ {z | C₁ * ((min n m : ℕ) : ℝ) ^ (-(2 / (2 * s + 3))) ≤ StatFormal.Distances.tvDist P Q -
                StatFormal.TrimmedMMD.alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tr.tauA κ D α δ n m)}

/-- Q25 (e) `slow_gauss_A` (S4 :885-887; main :246-249, Gaussian half): under Prop 5.6's hypotheses, `α⋆ − α̂_an^A ≥ c(n∧m)^{−1/(2N)}`
with probability `≥ 1 − δ′` for every `N` and `n∧m` large, so the error is not `O((n∧m)^{−a})` for any `a > 0` (for every `C`,
eventually, `α⋆ − α̂_an^A > C(n∧m)^{−a}` with probability `≥ 1 − δ′`). -/
def slow_gauss_A : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (σ κ D δ δ' : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) →
    IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ →
    (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 0 < δ → δ < δ' → δ' < 1 →
      (∀ N : ℕ, 1 ≤ N → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n m : ℕ, n₀ ≤ min n m →
        ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ') ≤ StatFormal.Wave30tp.sampleLaw P Q n m E ∧
          E ⊆ {z | c * ((min n m : ℕ) : ℝ) ^ (-(1 / (2 * (N : ℝ)))) ≤ StatFormal.Distances.tvDist P Q -
                StatFormal.TrimmedMMD.alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tr.tauA κ D α δ n m)}) ∧
      ∀ a C : ℝ, 0 < a → 0 < C → ∃ n₀ : ℕ, ∀ n m : ℕ, n₀ ≤ min n m →
        ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ') ≤ StatFormal.Wave30tp.sampleLaw P Q n m E ∧
          E ⊆ {z | C * ((min n m : ℕ) : ℝ) ^ (-a) < StatFormal.Distances.tvDist P Q -
                StatFormal.TrimmedMMD.alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tr.tauA κ D α δ n m)}

/-! ### H2. Compositions with 31tr and instances -/

/-- Q26 `excess_sobolev` (Proposition 5.10(ii), main :280-282, "this holds under the hypotheses of Proposition 5.5"; proof S4 :963-964):
the two-sided bound with `γ = (2s+3)/4` and, at `α = α⋆ − ε` with `ε ≤ ε₀/2`, the excess of the population ramp at the printed cuts
`u⋆ < t⋆` lies in `[(1−α⋆)c₁ε/(2^γc₂), ε]`. -/
def excess_sobolev : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (k₀ : ℝ → ℝ) (c C s : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ),
    Continuous k₀ → Integrable k₀ → (∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) → 0 < c → 1 / 2 < s →
    (∀ ξ, c * (1 + ξ ^ 2) ^ (-s) ≤ kHat k₀ ξ ∧ kHat k₀ ξ ≤ C * (1 + ξ ^ 2) ^ (-s)) →
    IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ →
      ∃ c₁ c₂ ε₀ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < ε₀ ∧ ε₀ ≤ StatFormal.Distances.tvDist P Q ∧
        (∀ ε ∈ Ioc (0 : ℝ) ε₀,
          c₁ * ε ^ ((2 * s + 3) / 4) ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ∧
          Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤ c₂ * ε ^ ((2 * s + 3) / 4)) ∧
        ∀ ε ∈ Ioc (0 : ℝ) (ε₀ / 2), ∀ (a b : H) (tS uS : ℝ),
          a ∈ StatFormal.TrimmedMMD.Concentration.region φ (StatFormal.Distances.tvDist P Q - ε) P →
          b ∈ StatFormal.TrimmedMMD.Concentration.region φ (StatFormal.Distances.tvDist P Q - ε) Q →
          ‖a - b‖ = Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) →
          IsLeast {t | StatFormal.Wave30tq.IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ)
            (1 - (StatFormal.Distances.tvDist P Q - ε)) t} tS →
          IsGreatest {u | StatFormal.Wave30tq.IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ)
            (StatFormal.Distances.tvDist P Q - ε) u} uS →
            (1 - StatFormal.Distances.tvDist P Q) * c₁ * ε / (2 ^ ((2 * s + 3) / 4) * c₂) ≤
                (∫ x, StatFormal.Wave30tq.ramp (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) tS uS x ∂P) -
                (∫ x, StatFormal.Wave30tq.ramp (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) tS uS x ∂Q) -
                (StatFormal.Distances.tvDist P Q - ε) ∧
            (∫ x, StatFormal.Wave30tq.ramp (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) tS uS x ∂P) -
                (∫ x, StatFormal.Wave30tq.ramp (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) tS uS x ∂Q) -
                (StatFormal.Distances.tvDist P Q - ε) ≤ ε

/-- Q27 `laplace_instances` (main :108-109, :119-120, :241-242, :256-259; S6 :173-175): for the Laplace kernel `e^{−|x−y|/σ}` and the
laws of Prop 5.5: (a) Assumption 5.1 with `γ = 5/4` and no smaller exponent; (b) the split-sample rate `(n∧m)^{−2/5}` up to the mesh;
(c) the excess of Prop 5.10(ii) at `γ = 5/4`; (d) the error of `α̂_an^A` is at least of order `(n∧m)^{−2/5}`. -/
def laplace_instances : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (σ : ℝ) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) → IsCross P Q p q x₀ ℓ₀ → 0 < p x₀ → ExpTail P Q x₀ →
      ((∃ c₀, StatFormal.Wave31ti.PolyMargin φ P Q c₀ (5 / 4)) ∧
        ∀ γ' c₀', γ' < 5 / 4 → ¬ StatFormal.Wave31ti.PolyMargin φ P Q c₀' γ') ∧
      (∀ (J : ℕ) (δ s2 η : ℝ), 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < η → η < 1 →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ (n m : ℕ) (α : Fin J → ℝ) (R : StatFormal.Wave30tz.LoRun ℝ J n m) (h : ℝ),
          StatFormal.Wave30tz.IsGrid α → R.IsWitnessRun φ α δ (1 / 2) s2 → StatFormal.Wave31tl.IsDefaultRun R →
          1 ≤ n → 1 ≤ m → StatFormal.Wave31tl.MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
            ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
              ENNReal.ofReal (1 - δ - η) ≤ StatFormal.Wave30tp.sampleLaw P Q n m E ∧
              E ⊆ {z | StatFormal.Distances.tvDist P Q - h - K * ((min n m : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) ≤
                  R.alphaLo α δ z.1 z.2 ∧ R.alphaLo α δ z.1 z.2 ≤ StatFormal.Distances.tvDist P Q}) ∧
      (∃ c₁ c₂ ε₀ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < ε₀ ∧ ε₀ ≤ StatFormal.Distances.tvDist P Q ∧
        (∀ ε ∈ Ioc (0 : ℝ) ε₀,
          c₁ * ε ^ (5 / 4 : ℝ) ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ∧
          Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤ c₂ * ε ^ (5 / 4 : ℝ)) ∧
        ∀ ε ∈ Ioc (0 : ℝ) (ε₀ / 2), ∀ (a b : H) (tS uS : ℝ),
          a ∈ StatFormal.TrimmedMMD.Concentration.region φ (StatFormal.Distances.tvDist P Q - ε) P →
          b ∈ StatFormal.TrimmedMMD.Concentration.region φ (StatFormal.Distances.tvDist P Q - ε) Q →
          ‖a - b‖ = Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) →
          IsLeast {t | StatFormal.Wave30tq.IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ)
            (1 - (StatFormal.Distances.tvDist P Q - ε)) t} tS →
          IsGreatest {u | StatFormal.Wave30tq.IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ)
            (StatFormal.Distances.tvDist P Q - ε) u} uS →
            (1 - StatFormal.Distances.tvDist P Q) * c₁ * ε / (2 ^ (5 / 4 : ℝ) * c₂) ≤
                (∫ x, StatFormal.Wave30tq.ramp (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) tS uS x ∂P) -
                (∫ x, StatFormal.Wave30tq.ramp (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) tS uS x ∂Q) -
                (StatFormal.Distances.tvDist P Q - ε) ∧
            (∫ x, StatFormal.Wave30tq.ramp (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) tS uS x ∂P) -
                (∫ x, StatFormal.Wave30tq.ramp (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) tS uS x ∂Q) -
                (StatFormal.Distances.tvDist P Q - ε) ≤ ε) ∧
      ∀ (D δ δ' : ℝ), (∀ x x', ‖φ x - φ x'‖ ≤ D) → 0 < δ → δ < δ' → δ' < 1 →
        ∃ (C₁ : ℝ) (n₀ : ℕ), 0 < C₁ ∧ ∀ n m : ℕ, n₀ ≤ min n m →
          ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
            ENNReal.ofReal (1 - δ') ≤ StatFormal.Wave30tp.sampleLaw P Q n m E ∧
            E ⊆ {z | C₁ * ((min n m : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) ≤ StatFormal.Distances.tvDist P Q -
                  StatFormal.TrimmedMMD.alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tr.tauA 1 D α δ n m)}

/-- Q28 `simulated_pairs` (S6 :157-168; main :264-265): (a) the shift `N(±a, 1)` crosses at `0` with `ℓ₀ = 2aφ₁(a)`, `p(0) > 0` and
exponential tails; (b) the mixtures `0.8N(0,1) + 0.2N(±μ,1)` are probability laws crossing at `0` with `ℓ₀ = 0.4μφ₁(μ)`, `p(0) > 0` and
exponential tails. -/
def simulated_pairs : Prop :=
  (∀ a : ℝ, 0 < a →
    IsCross (ProbabilityTheory.gaussianReal a 1) (ProbabilityTheory.gaussianReal (-a) 1)
        (ProbabilityTheory.gaussianPDFReal a 1) (ProbabilityTheory.gaussianPDFReal (-a) 1) 0
        (2 * a * ProbabilityTheory.gaussianPDFReal 0 1 a) ∧
      0 < ProbabilityTheory.gaussianPDFReal a 1 0 ∧
      ExpTail (ProbabilityTheory.gaussianReal a 1) (ProbabilityTheory.gaussianReal (-a) 1) 0) ∧
  ∀ μ : ℝ, 0 < μ →
    IsProbabilityMeasure ((0.8 : ℝ≥0) • ProbabilityTheory.gaussianReal 0 1 + (0.2 : ℝ≥0) • ProbabilityTheory.gaussianReal μ 1) ∧
    IsProbabilityMeasure ((0.8 : ℝ≥0) • ProbabilityTheory.gaussianReal 0 1 + (0.2 : ℝ≥0) • ProbabilityTheory.gaussianReal (-μ) 1) ∧
    IsCross ((0.8 : ℝ≥0) • ProbabilityTheory.gaussianReal 0 1 + (0.2 : ℝ≥0) • ProbabilityTheory.gaussianReal μ 1)
        ((0.8 : ℝ≥0) • ProbabilityTheory.gaussianReal 0 1 + (0.2 : ℝ≥0) • ProbabilityTheory.gaussianReal (-μ) 1)
        (fun x => 0.8 * ProbabilityTheory.gaussianPDFReal 0 1 x + 0.2 * ProbabilityTheory.gaussianPDFReal μ 1 x)
        (fun x => 0.8 * ProbabilityTheory.gaussianPDFReal 0 1 x + 0.2 * ProbabilityTheory.gaussianPDFReal (-μ) 1 x) 0
        (0.4 * μ * ProbabilityTheory.gaussianPDFReal 0 1 μ) ∧
      0 < 0.8 * ProbabilityTheory.gaussianPDFReal 0 1 0 + 0.2 * ProbabilityTheory.gaussianPDFReal μ 1 0 ∧
      ExpTail ((0.8 : ℝ≥0) • ProbabilityTheory.gaussianReal 0 1 + (0.2 : ℝ≥0) • ProbabilityTheory.gaussianReal μ 1)
        ((0.8 : ℝ≥0) • ProbabilityTheory.gaussianReal 0 1 + (0.2 : ℝ≥0) • ProbabilityTheory.gaussianReal (-μ) 1) 0

/-- Q29 `halfspace_geometry` (non-vacuity of (G1)–(G3) in every dimension): for the half-space `G = {⟨x, e⟩ > a}` and `ρ ≥ 1`,
(G1) with `Π_ρ = (2ρ)^{d−1} + 2d·vol(B(0,1))ρ^{d−1}`, (G2) with `V_ρ = 2(2ρ)^{d−1}` for every `w₀`, and `dist(x, ∂G) = |⟨x, e⟩ − a|`. -/
def halfspace_geometry : Prop :=
  ∀ (d : ℕ) [NeZero d] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V], Module.finrank ℝ V = d →
    ∀ (e : V) (a : ℝ) (c₀ : V) (ρ : ℝ), ‖e‖ = 1 → 1 ≤ ρ →
      (∀ h : V, volume (symmDiff ({x : V | a < ⟪x, e⟫_ℝ} ∩ Metric.ball c₀ ρ)
          ((· - h) ⁻¹' ({x : V | a < ⟪x, e⟫_ℝ} ∩ Metric.ball c₀ ρ))) ≤
        ENNReal.ofReal (((2 * ρ) ^ (d - 1) + 2 * d * (volume (Metric.ball (0 : V) 1)).toReal * ρ ^ (d - 1)) * ‖h‖)) ∧
      (∀ w₀ : ℝ, 0 < w₀ → ∀ t ∈ Ioc (0 : ℝ) w₀,
        volume {x | x ∈ Metric.ball c₀ ρ ∧ Metric.infDist x (frontier {x : V | a < ⟪x, e⟫_ℝ}) ≤ t} ≤
          ENNReal.ofReal (2 * (2 * ρ) ^ (d - 1) * t)) ∧
      ∀ x : V, Metric.infDist x (frontier {x : V | a < ⟪x, e⟫_ℝ}) = |⟪x, e⟫_ℝ - a|

/-- Q29 `halfspace_pair` (c): an explicit pair of densities crossing on a hyperplane through the centre, with `|P − Q|` carried by the
unit ball: all hypotheses of Theorem S4.10 and Corollary S4.11 case 1 hold with (a)–(b) at `ρ = 2` and any kernel of the setting. -/
def halfspace_pair : Prop :=
  ∀ (d : ℕ) [NeZero d] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V], Module.finrank ℝ V = d →
    ∀ (e : V) (a : ℝ) (c₀ : V), ‖e‖ = 1 → ⟪c₀, e⟫_ℝ = a →
      let η : ℝ := (2 * (volume (Metric.ball (0 : V) 2)).toReal)⁻¹
      let u : V → ℝ := fun x => (volume (Metric.ball c₀ 2)).toReal⁻¹ * (Metric.ball c₀ 2).indicator (fun _ => (1 : ℝ)) x
      let w : V → ℝ := fun x => η * (⟪x, e⟫_ℝ - a) * (Metric.ball c₀ 1).indicator (fun _ => (1 : ℝ)) x
      let G : Set V := {x | a < ⟪x, e⟫_ℝ}
      let P : Measure V := volume.withDensity (fun x => ENNReal.ofReal (u x + w x))
      let Q : Measure V := volume.withDensity (fun x => ENNReal.ofReal (u x - w x))
      Measurable (fun x => u x + w x) ∧ Measurable (fun x => u x - w x) ∧ (∀ x, 0 ≤ u x + w x) ∧ (∀ x, 0 ≤ u x - w x) ∧
      P univ = 1 ∧ Q univ = 1 ∧
      (∀ x ∈ G, u x - w x ≤ u x + w x) ∧ (∀ x ∉ G, u x + w x ≤ u x - w x) ∧
      (∀ x, |(u x + w x) - (u x - w x)| ≤ 2 * η * Metric.infDist x (frontier G)) ∧
      (∀ x, x ∉ Metric.ball c₀ 1 → w x = 0) ∧
      0 < StatFormal.Distances.tvDist P Q ∧ StatFormal.Distances.tvDist P Q < 1

end Claims

end StatFormal.Wave31tq
