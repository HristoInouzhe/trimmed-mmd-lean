import StatFormal.Archive.OTFD.Wave1.Statements
import StatFormal.Archive.RobustEquality.SemidualStrong.Statements
import StatFormal.Archive.Wave18a.Statements
import StatFormal.Archive.RobustEquality.Paper2.Seminorm.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# FROZEN STATEMENTS — wave 20a (QUEUE rows 209–211, 213–217): otfd A `lem:app-block-Pl`, `lem:rt-depth-laplace`;
# otfd B `lem:app-esssup-subgradients`; robust equality JASA `lem:cert-coarse`, `prop:cs-cells`; paper 2
# `prop:structured`, `prop:translation`; ICL `lem:phi`

Sources (verbatim in `lean-formalisation/inventory/extracted/{otfd-A_sieves,otfd-B_bands,robust-equality-jasa,
robust-equality-paper2,context-distribution-icl}.md`; CURRENT text after the 2026-10-13/14/15 corrections; JASA and
paper 2 paths under `robust-equality-outcomes-under-distribution-shift/`):
* A `lem:app-block-Pl` (`otfd/papers/A_sieves/supplement.tex:945-955`, proof `:957-993`), with
  `def:app-lipschitz-hypersurface` (`:931-943`; `𝒫^ℓ(H)` with the paper's second-moment clause).
* A `lem:rt-depth-laplace` (`otfd/papers/A_sieves/supplement.tex:5517-5530`, proof `:4544-4577`), with
  `φ(r,s) = (r²+s²)^{1/2}` and `𝒟_φ(a,b) = 2Eφ(A,B) − Eφ(A,A') − Eφ(B,B')` (`A_sieves/main.tex:1499-1501`).
* B `lem:app-esssup-subgradients` (`otfd/papers/B_bands/supplement.tex:1967-1976`, proof `:1978-1991`).
* JASA `lem:cert-coarse` (`jasa/supp_calibration.tex:508-512`, proof `:514-519`), `OT_ε` as in the frozen
  `SemidualStrong.OTdisc` (quadratic cost `c_i(y) = |x_i − y|²`).
* JASA `prop:cs-cells` (`jasa/supp_common_shift.tex:198-219`, proof `:221-228`), with `def:cs-set` (`:97-115`), the
  slice terms `f^θ_h, c^θ, Δ_θ, T^θ_s, R^{𝒩_θ}_min` (`:128-139`), `thm:cs-certificate` (`:141-164`, frozen Wave 4b) and
  `cor:cs-translation` (`:169-187`, frozen Wave 18a).
* paper 2 `prop:structured` (`paper2/main.tex:361-377`, proof `paper2/app_proofs.tex:100-116`), with `thm:seminorm`
  (`main.tex:330-346`, frozen `Paper2.Seminorm`) and `lem:delta-inf` (`main.tex:297-302`).
* paper 2 `prop:translation` (`paper2/main.tex:615-623`, proof `paper2/app_proofs.tex:245-252`).
* ICL `lem:phi` (`context-distribution-ICL/paper/v3/sections/04_selector.tex:16-26`, setting `:4-14`; proof
  `supp/proofs_main.tex:6-19`).
Imports the frozen `OTFD/Wave1` (`IsLipHyp`, `PellClass`), `RobustEquality/SemidualStrong` (`OTdisc`; through it
`Semidual`: `muDisc`), `Wave18a` (`linRule`, `affT`; through it `Wave4b`: `nominal`, `RefClass`, `Fstruct`,
`sqrtTPull`, and `Certificate`: `centre`) and `RobustEquality/Paper2/Seminorm` (`Deltafin`, `T0`) statements, not
copied; Mathlib and Tau Ceti (`TauCeti.wassersteinEDist`) otherwise. No `Foundations` file.

Covered:
* `lem:app-block-Pl`: `app_block_Pl_null` (`P(X ∈ A) = 0` for every Lipschitz hypersurface), `app_block_Pl_class`
  (with `E‖X‖² < ∞`, `𝓛(X) ∈ 𝒫^ℓ(H)`).
* `lem:rt-depth-laplace`: `rt_depth_L2` (`1 − L_a ∈ L²(κ)`), `rt_depth_laplace` (the Laplace representation, with
  integrability), `rt_depth_metric` (`𝒟 ≥ 0`, symmetric, `𝒟(a,a) = 0`, triangle inequality for `𝒟^{1/2}`),
  `rt_depth_eq_zero` (`𝒟 = 0 ⇔ a = b`), `rt_depth_W1` (`𝒟 ≤ 2W₁`), `rt_depth_continuous` (joint weak continuity on laws
  in `[0,1]`), `rt_depth_W1_iff` (`𝒟(a_K,b_K) → 0 ⇔ W₁(a_K,b_K) → 0` on laws in `[0,1]`).
* `lem:app-esssup-subgradients`: `app_esssup_subgradients`.
* `lem:cert-coarse`: `cert_coarse`.
* `prop:cs-cells`: (i) `cs_cells_coupling`, `cs_cells_nominal`, `cs_cells_linear`; (ii) `cs_cells_T`; (iii)
  `cs_cells_cover`; (iv) `cs_cells_segment`.
* `prop:structured`: `structured_value` (Wasserstein and anisotropic balls), `structured_cells`, `structured_convex`.
* `prop:translation`: `translation_identity`, (i) `translation_mean`, (ii) `translation_sup`.
* `lem:phi`: (i) `phi_convex`, `phi_same_coverage`; (ii) `phi_first_variation`; (iii) `phi_kl`; (iv) `phi_continuous`.

Not covered (declared):
* `prop:structured`: **max-sliced balls** (not of the form `eq:BN`; their exact groupwise term `√β_s|w|` is not
  formalised); `Θ` compact and `θ ↦ (A_θ, b_θ)` continuous are replaced by: any nonempty `Θ` (value), bounded cells
  `sup_{θ∈Θ_j} ‖A_θ − A_{θ_j}‖ < ∞` (convex certificate).
* `prop:translation` (iii) (`δ ∼ N(0,C)`: needs the `χ²_k` law of `δᵀC⁺δ`, not in Mathlib).
* `prop:cs-cells`: the reweighting family (b)/(c) (the paper: "valid but not implemented"); the remark that (iii)
  converges to the supremum as the cells shrink.
* `lem:phi`: the reduction from `μ` to its one-slot marginal `ν = Π̄_μ` (all claims are stated in `ν`), the
  Lindsay/NPMLE remark and the equivalence condition after the proof.
* `lem:app-esssup-subgradients`: Rockafellar 25.5/25.6 themselves (the route argues directly).
* `lem:rt-depth-laplace`: `rem:rt-depth-converse` (not this target).

Encodings (to be checked by the critic):
* Block: `H` a real separable Hilbert space (`CompleteSpace`, `SecondCountableTopology`, Borel), infinite-dimensional
  through `f : HilbertBasis ℕ ℝ H` (paper: `(f_k)_{k≥1}`, 0-indexed here); `P_N x = Σ_{k<N} ⟨f_k,x⟩ f_k` (`projN`);
  "for infinitely many `N`" is `∀ M, ∃ N ≥ M`; (a) `IndepFun (P_N X) ((I − P_N)X)`; (b) `law((⟨X,f_k⟩)_{k<N}) ≪ volume` on
  `EuclideanSpace ℝ (Fin N)` (`Measure.map` of a measurable map, `BorelSpace`); Lipschitz hypersurfaces are the frozen
  `IsLipHyp` (`τ` Lipschitz on `(ℝw)^⊥`, `w ≠ 0`; not assumed measurable: they are closed); `E‖X‖² < ∞` is
  `∫⁻ ‖X‖ₑ² < ⊤`; `𝒫^ℓ(H)` is the frozen `PellClass` (probability, finite second moment, null on hypersurfaces).
* Depth: laws `a` are Borel probability measures on `ℝ` with `a((−∞,0)) = 0` and `∫|x| da < ∞` (`DepthLaw`);
  `L_a(t) = ∫ e^{−tx²} da` (`lapT`); `Eφ(A,B) = ∫ φ d(a ⊗ b)` (`Ephi`, independent copies; integrable since
  `φ(r,s) ≤ |r| + |s|`); `L²(κ)`-membership is `IntegrableOn ((1 − L_a)² t^{−3/2}) (0,∞)` (the constant `(2√π)⁻¹` is
  irrelevant); the identity is stated with the explicit integral; `W₁` is `wassersteinEDist 1` (`ℝ≥0∞`; `𝒟` enters as
  `ENNReal.ofReal`, faithful since `𝒟 ≥ 0`); "laws supported in `[0,1]`" is `lawsUnit` (`a([0,1]ᶜ) = 0`) inside
  `ProbabilityMeasure ℝ` with Mathlib's weak topology; joint continuity is `ContinuousOn` on `lawsUnit ×ˢ lawsUnit`;
  the `W₁`-equivalence is for sequences `K ↦ (a_K, b_K)`.
* Esssup: `ℝ^K = EuclideanSpace ℝ (Fin K)`, Lebesgue = `volume`; "convex and finite on an open set" is
  `ConvexOn ℝ U χ` with `U` open (so `U` is convex — a specialisation: convexity on a non-convex open set is not
  defined); `∂χ(w)` is the set of subgradients relative to `U` (`subdiffOn`; equals the usual subdifferential at an
  interior point); the left side is a `⨆` in `EReal`; `⟨v, ∇χ(u)⟩` is `gradDir` (`⊥` off the differentiability set,
  which is Lebesgue- hence `ν`-null); the essential supremum is Mathlib `essSup` on `ν.restrict N` (`EReal`); "support
  contains a neighbourhood of `w`" is `∃ V ∈ 𝓝 w, V ⊆ ν.support`.
* cert-coarse: centre `μ = Σ_i a_i δ_{x_i}` as labelled atoms (frozen `OTdisc`, `a_i > 0`, `Σ a_i = 1`); clusters are
  the fibres of a surjection `σ : Fin k → Fin r` (non-empty `I_z`); `w_z`, `x̄_z`, `v_z`, `D_r` are `clW`, `clBar`,
  `clVar`, `clD` (`w_z > 0`, no `x/0`); `K` any measurable space observed through a bounded measurable feature map
  `φ : K → ℝ^d` (paper: `K ⊂ ℝ^d` compact, `φ = id`; generalisation), `c_i(y) = ‖x_i − φ(y)‖²`; any probability `P`.
* cs-cells: centres are the uniform `centre` of the frozen `Certificate`; `Δ_θ` is the frozen `nominal`
  (`W₂` of pushforwards, Tau Ceti); `𝔗_θ` any measurable map in (i)–(iii) (paper: affine; generalisation) and
  `affT A b` in the linear form, the rule `linRule w b₀`; `M_s` the uncentred second-moment matrix
  `n_s⁻¹ Σ_i x_i x_iᵀ`, `‖v‖_{M_s} = (n_s⁻¹Σ⟨v,x_i⟩²)^{1/2}`; (i) is stated one-sided for all `θ, θ'` (hence `|·|`);
  (ii)–(iii) for a generic bounded measurable cost `c` (paper: `‖·−·‖²` on `K_Θ`); the bounds `f̄_j, c̲_j, c̄_j` are
  hypotheses on the (anchor, reference) pairs `(x_i, z)`; `T^θ_s` is the frozen `sqrtTPull` (`⨆_ν √T`, `ℝ≥0∞`);
  `T̄` is `Tgen`/`sqrtTgen` (same formula with `f̄, c̲` and radius `R̄ + β`); the floors are `floorGen` (`EReal` `⨅`;
  the radius hypotheses are equalities `r = floor + β` in `EReal`); references in `RefClass` (`0 < ν(K) ≤ 1`);
  `F_Θ` is the frozen `Fstruct` with transported references `(𝔗_θ)_#𝒩_s`; `max_j` is `⨆ j : Fin J`; (iv)
  `clipVertex` is `max t₁ (min t₂ (−⟨u,Bu⟩/‖Bu‖²))` (for `Bu = 0` the junk vertex `0` is harmless: `c^t` is constant).
* Paper 2: covariates in a real inner-product space `E` (complete where adjoints are used; generalises `ℝ^d`);
  weighted centres `ProbW`; `Δ` is the frozen `Deltafin` (coupling form `min_γ Σγ_ij⟨w, x⁰_i − x¹_j⟩²`, `lem:delta-inf`);
  the structured certified worst case is `certStruct = ⨆_θ ⨅_{λ₀,λ₁>0} (Δ_θ + √T⁰_0 + √T⁰_1)²` (`ℝ≥0∞`) with the frozen
  `T0` (`ε = 0`, full-support reference, cost `‖G_s(x − x₀)‖²`) at the transported centres `A_θx_i + b_θ`;
  Wasserstein balls are `G_s = I`, anisotropic `G_s = M_s^{−1/2}`, so `N_s = √β_s‖(G_s⁻¹)ᵀw‖`; `|v|_{Σ_s}` is `smNorm`
  about a common point `p`; `|M_γ^{1/2}v|` is `gamNorm`; `L_j` is `Lcell` (`ℝ≥0∞`); "seminorm" is Mathlib `Seminorm`
  and "convex certificate" is a real convex `Cb` equal to the cell bound and dominating `certStruct`.
  Translation: the realised disparity is `Δ` (coupling form) of the translated centres, squared; (i) `δ = δ₀ − δ₁`
  square-integrable on a probability space, `Eδ = 0`, `wᵀCw = covarianceBilin(law δ)(w,w)`; (ii) the ellipsoid
  `{δ ∈ range C : δᵀC⁺δ ≤ β}` is `{Cu : ⟨u,Cu⟩ ≤ β}` for a positive operator `C` (`δᵀC⁺δ = ⟨u,Cu⟩`), `|C^{1/2}w| =
  √⟨w,Cw⟩`; "the supremum is" is `IsGreatest` (attained).
* ICL: `𝒵` any measurable space; `K` jointly measurable with values in `[K_min, K_max]`, `K_min > 0` (`KernelBounds`);
  `ν` and `P₀` probability measures; `ρ_ν = ∫ K(·,z')dν`, `Φ(ν) = −∫ log ρ_ν dP₀` (Bochner, genuine: `log ρ_ν` is bounded
  measurable); mixtures use `ENNReal.ofReal` weights; "all minimizers" is minimisers over any mixture-closed class `𝒞`
  of probability marginals (all of `𝒫(𝒵)`, or the pool); the first variation is the right derivative at `t = 0`
  (`HasDerivWithinAt` on `[0,1]`) of `t ↦ Φ((1−t)ν + tδ_{z'})`; (iii) densities w.r.t. a σ-finite `λ`, `K⋆ν =
  ρ_ν λ`, `KL` is Mathlib `klDiv` (asserted `≠ ⊤`, then `toReal`), the constant is `∫ p₀ log p₀ dλ` (integrable: finite
  entropy); (iv) `𝒵` compact metric Borel, continuity on `ProbabilityMeasure 𝒵` (weak topology), minimiser exists.

Critic notes:
* All 28 claims are proved in `Wave20a/Route{Block,DepthSqrt,Depth,DepthInj,DepthCont,Esssup,Coarse,Cells,
  Structured,Translation,Phi,PhiKL}.lean` (axioms: propext, Classical.choice, Quot.sound). Routes reuse the certified
  `SemidualStrong.strong_duality` and the untrusted Foundations library `SemiDiscrete/Dual` (`cert_coarse`), the
  certified Wave 4b `cs_certificate` and Wave 18a `cs_translation_nominal` (`cs_cells_*`), the certified
  `Paper2.Seminorm.seminorm_wass` (`structured_value`); Tau Ceti (couplings, `W_p` triangle inequality, weak + moment
  convergence ⇒ `W_p` convergence) and Mathlib (Rademacher, Stone–Weierstrass separation, Prokhorov, Lévy–Prokhorov)
  otherwise — routes only.
* Proof routes differ from the papers where convenient: cert-coarse is proved by duality (Jensen in each cluster), not
  by primal gluing; esssup directly via Rademacher and monotonicity of subgradients (no Rockafellar 25.6); `𝒟 = 0 ⇒
  a = b` via a separating subalgebra of `{e^{−ty}}` (no Feller citation).
* `structured_*`/`translation_*` use the coupling form of `Δ`; its equality with `W₂(h_#P̂₀, h_#P̂₁)` (`lem:delta-inf`) is
  NOT certified (frozen `Seminorm` critic note), so "realised disparity" means the coupling form.
* `lem:phi` (iii): with `K ≥ K_min > 0` and `∫K(z,z')λ(dz) = 1`, necessarily `λ(𝒵) ≤ 1/K_min` (e.g. not Lebesgue on
  `ℝ^d`); the hypotheses are consistent (e.g. `K ≡ 1`, `λ` a probability).
* `prop:cs-cells` (ii) needs only `c̲ ≤ c^θ` in the integrand and `c^θ ≤ c̄` in the floor (no continuity, any bounded
  measurable cost and maps); (iii) needs the floor-plus-budget radius at each `θ`.
* No statement of the eight results was found false. Observations: `lem:app-esssup-subgradients` should say "convex
  open set"; `prop:structured`'s seminorm claim for `L_j` needs finite `L_j` (compactness and continuity of `θ ↦ A_θ`,
  stated in the proof, not in the proposition); `prop:translation` (ii)'s supremum is attained.
* Critic (2026-10-15): ACCEPT-WITH-NOTE, all 28 TRUE. block-Pl: `HilbertBasis ℕ` matches A's setting; hypothesis (b)'s
  `Measure.map` is genuine (measurable `X`, continuous coordinates). esssup: convexity of `U` costs nothing (take
  `U = int dom χ`). cert-coarse/cs-cells/phi generalisations are genuine; reweighting appears only in a remark.
  structured: coupling-form `Δ` suffices (`Deltafin = W₂` for uniform weights via Wave9a `nw_*`, `delta_inf_empirical`).
  Paper S3 (DEFECTS #67): paper2 `prop:structured` needs `θ ↦ A_θ` continuous (or bounded on cells) for the
  seminorm claim — `d = 1`, `Θ = [0,1]`, `A_0 = 1`, `A_θ = 1/θ`: `Δ ≡ 0` but `L_1(w) = ∞`. ICL `lem:phi`(iii):
  `K ≥ K_min > 0` forces `λ(𝒵) ≤ 1/K_min` (no defect; hypotheses consistent for finite references).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave20a

/-! ### otfd A `lem:app-block-Pl` -/

section Block
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `P_N x = Σ_{k<N} ⟨f_k, x⟩ f_k`, the orthogonal projection onto `E_N = span(f_0, …, f_{N−1})`. -/
def projN (f : HilbertBasis ℕ ℝ H) (N : ℕ) (x : H) : H := ∑ k : Fin N, ⟪f k, x⟫ • f k

/-- The coordinates `(⟨x, f_k⟩)_{k<N}` in `ℝ^N`. -/
def coordN (f : HilbertBasis ℕ ℝ H) (N : ℕ) (x : H) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun k : Fin N => ⟪x, f k⟫)

/-- The block hypotheses at `N`: (a) `P_N X ⫫ (I − P_N) X`; (b) the first `N` coordinates of `X` have a
Lebesgue density on `ℝ^N`. -/
def BlockHyp [MeasurableSpace H] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : HilbertBasis ℕ ℝ H)
    (X : Ω → H) (N : ℕ) : Prop :=
  IndepFun (fun ω => projN f N (X ω)) (fun ω => X ω - projN f N (X ω)) P ∧
    P.map (fun ω => coordN f N (X ω)) ≪ volume

end Block

/-! ### otfd A `lem:rt-depth-laplace` -/

section Depth

/-- `L_a(t) = E e^{−tA²}`, `A ∼ a`. -/
def lapT (a : Measure ℝ) (t : ℝ) : ℝ := ∫ x, Real.exp (-(t * x ^ 2)) ∂a

/-- `φ(r,s) = (r² + s²)^{1/2}`. -/
def phiR (r s : ℝ) : ℝ := √(r ^ 2 + s ^ 2)

/-- `E φ(A,B)` for independent `A ∼ a`, `B ∼ b`. -/
def Ephi (a b : Measure ℝ) : ℝ := ∫ z, phiR z.1 z.2 ∂(a.prod b)

/-- `𝒟_φ(a,b) = 2Eφ(A,B) − Eφ(A,A') − Eφ(B,B')`. -/
def Dphi (a b : Measure ℝ) : ℝ := 2 * Ephi a b - Ephi a a - Ephi b b

/-- A Borel probability law on `[0,∞)` with a finite first moment. -/
def DepthLaw (a : Measure ℝ) : Prop :=
  IsProbabilityMeasure a ∧ a (Iio 0) = 0 ∧ Integrable id a

/-- Borel probability laws on `ℝ` supported in `[0,1]` (`a([0,1]ᶜ) = 0`), with the weak topology of
`ProbabilityMeasure ℝ`. -/
def lawsUnit : Set (ProbabilityMeasure ℝ) := {a | (a : Measure ℝ) (Icc 0 1)ᶜ = 0}

end Depth

/-! ### otfd B `lem:app-esssup-subgradients` -/

section Esssup
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Subgradients of `χ` at `w` relative to `U`: `χ(y) ≥ χ(w) + ⟨ξ, y − w⟩` for `y ∈ U`. -/
def subdiffOn (U : Set E) (χ : E → ℝ) (w : E) : Set E := {ξ | ∀ y ∈ U, χ w + ⟪ξ, y - w⟫ ≤ χ y}

open Classical in
/-- `u ↦ ⟨v, ∇χ(u)⟩` at differentiability points, `⊥` elsewhere (in `EReal`). -/
def gradDir [CompleteSpace E] (χ : E → ℝ) (v u : E) : EReal :=
  if DifferentiableAt ℝ χ u then ((⟪v, gradient χ u⟫ : ℝ) : EReal) else ⊥

end Esssup

/-! ### robust equality JASA `lem:cert-coarse` -/

section Coarse
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k r : ℕ}

/-- Cluster weight `w_z = a(I_z)`, `I_z = σ⁻¹{z}`. -/
def clW (σ : Fin k → Fin r) (a : Fin k → ℝ) (z : Fin r) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => σ i = z), a i

/-- Cluster barycentre `x̄_z = Σ_{i ∈ I_z} (a_i/w_z) x_i`. -/
def clBar (σ : Fin k → Fin r) (a : Fin k → ℝ) (x : Fin k → E) (z : Fin r) : E :=
  (clW σ a z)⁻¹ • ∑ i ∈ Finset.univ.filter (fun i => σ i = z), a i • x i

/-- Cluster variance `v_z = Σ_{i ∈ I_z} (a_i/w_z) |x_i − x̄_z|²`. -/
def clVar (σ : Fin k → Fin r) (a : Fin k → ℝ) (x : Fin k → E) (z : Fin r) : ℝ :=
  (clW σ a z)⁻¹ * ∑ i ∈ Finset.univ.filter (fun i => σ i = z), a i * ‖x i - clBar σ a x z‖ ^ 2

/-- `D_r = Σ_z w_z v_z`. -/
def clD (σ : Fin k → Fin r) (a : Fin k → ℝ) (x : Fin k → E) : ℝ := ∑ z, clW σ a z * clVar σ a x z

end Coarse

/-! ### robust equality JASA `prop:cs-cells` -/

section Cells
variable {K : Type} [MeasurableSpace K] {n : ℕ}

/-- The slice term at a reference with generic pair functions `f, c` and radius `r`:
`λr + λε n⁻¹ Σ_i log E_ν exp{(f(x_i,·) − λ c(x_i,·))/(λε)}`. -/
def Tgen (x : Fin n → K) (f c : K → K → ℝ) (ε r lam : ℝ) (ν : Measure K) : ℝ :=
  lam * r + lam * ε * ((n : ℝ)⁻¹ * ∑ i, Real.log (∫ z, Real.exp
    ((f (x i) z - lam * c (x i) z) / (lam * ε)) ∂ν))

/-- `√T̄ = ⨆_{ν ∈ 𝒩} √(T_gen)` in `ℝ≥0∞`. -/
def sqrtTgen (x : Fin n → K) (f c : K → K → ℝ) (ε r lam : ℝ) (N : Set (Measure K)) : ℝ≥0∞ :=
  ⨆ ν ∈ N, ENNReal.ofReal (√(Tgen x f c ε r lam ν))

/-- The floor `−ε sup_{ν ∈ 𝒩} n⁻¹ Σ_i log E_ν e^{−c(x_i,·)/ε}`, as an `EReal` infimum (`⊤` for empty `𝒩`). -/
def floorGen (x : Fin n → K) (c : K → K → ℝ) (ε : ℝ) (N : Set (Measure K)) : EReal :=
  ⨅ ν ∈ N, ((-ε * ((n : ℝ)⁻¹ * ∑ i, Real.log (∫ z, Real.exp (-c (x i) z / ε) ∂ν)) : ℝ) : EReal)

/-- The clipped vertex `clip(−⟨u,Bu⟩/‖Bu‖², t₁, t₂)`. -/
def clipVertex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (B : E →L[ℝ] E) (u : E)
    (t₁ t₂ : ℝ) : ℝ :=
  max t₁ (min t₂ (-⟪u, B u⟫ / ‖B u‖ ^ 2))

end Cells

/-! ### robust equality paper 2 `prop:structured` and `prop:translation` -/

section Paper2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n₀ n₁ : ℕ}

open StatFormal.RobustEquality.Paper2.Seminorm

/-- `√t` of an extended real, in `ℝ≥0∞` (`√⊤ = ⊤`, negative values give `0`). -/
def sqrtE (t : EReal) : ℝ≥0∞ := t.toENNReal ^ (1 / 2 : ℝ)

/-- The certified worst case of the structured model with Wasserstein/anisotropic differential balls
(`ε = 0`, cost `‖G_s(x − x₀)‖²`, budget `β_s`) around the transported centres `𝔗_θ P̂_s`, `𝔗_θ x = A_θ x + b_θ`:
`sup_θ inf_{λ₀,λ₁>0} (Δ_θ(w) + √T^θ_0(w,λ₀) + √T^θ_1(w,λ₁))²`. -/
def certStruct [CompleteSpace E] {Θ : Type*} (G₀ G₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ)
    (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (A : Θ → E →L[ℝ] E) (b : Θ → E) (w : E) :
    ℝ≥0∞ :=
  ⨆ θ, ⨅ (l₀ : Set.Ioi (0 : ℝ)) (l₁ : Set.Ioi (0 : ℝ)),
    (ENNReal.ofReal (Deltafin a₀ (fun i => A θ (x₀ i) + b θ) a₁ (fun j => A θ (x₁ j) + b θ) w) +
      sqrtE (T0 G₀ β₀ a₀ (fun i => A θ (x₀ i) + b θ) w l₀) +
      sqrtE (T0 G₁ β₁ a₁ (fun j => A θ (x₁ j) + b θ) w l₁)) ^ 2

/-- `|v|_Σ = (Σ_i a_i ⟨v, x_i − p⟩²)^{1/2}`, `Σ` the second-moment matrix of `Σ_i a_i δ_{x_i}` about `p`. -/
def smNorm {n : ℕ} (a : Fin n → ℝ) (x : Fin n → E) (p v : E) : ℝ := √(∑ i, a i * ⟪v, x i - p⟫ ^ 2)

/-- `|M_γ^{1/2} v| = (Σ_{ij} γ_{ij} ⟨v, x⁰_i − x¹_j⟩²)^{1/2}`, `M_γ = E_γ (X − Y)(X − Y)ᵀ`. -/
def gamNorm (γ : Fin n₀ → Fin n₁ → ℝ) (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (v : E) : ℝ :=
  √(∑ i, ∑ j, γ i j * ⟪v, x₀ i - x₁ j⟫ ^ 2)

/-- The transport polytope `Π(a₀, a₁)`. -/
def Polytope (a₀ : Fin n₀ → ℝ) (a₁ : Fin n₁ → ℝ) : Set (Fin n₀ → Fin n₁ → ℝ) :=
  {γ | (∀ i j, 0 ≤ γ i j) ∧ (∀ i, ∑ j, γ i j = a₀ i) ∧ ∀ j, ∑ i, γ i j = a₁ j}

/-- `L_j(w) = Σ_s sup_{θ ∈ Θ_j} |(A_θ − A_{θ_j})ᵀ w|_{Σ_s}` (in `ℝ≥0∞`). -/
def Lcell [CompleteSpace E] {Θ : Type*} (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ)
    (x₁ : Fin n₁ → E) (p : E) (A : Θ → E →L[ℝ] E) (cell : Set Θ) (θj : Θ) (w : E) : ℝ≥0∞ :=
  (⨆ θ ∈ cell, ENNReal.ofReal (smNorm a₀ x₀ p (ContinuousLinearMap.adjoint (A θ - A θj) w))) +
    ⨆ θ ∈ cell, ENNReal.ofReal (smNorm a₁ x₁ p (ContinuousLinearMap.adjoint (A θ - A θj) w))

/-- The mean `m = Σ_i a_i x_i` of a weighted centre. -/
def meanC {n : ℕ} (a : Fin n → ℝ) (x : Fin n → E) : E := ∑ i, a i • x i

/-- `g(w) = ⟨w, m₀ − m₁⟩`. -/
def gapW (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (w : E) : ℝ :=
  ⟪w, meanC a₀ x₀ - meanC a₁ x₁⟫

/-- The realised disparity `Δ(w)²` after translating group `0` by `δ₀` and group `1` by `δ₁`. -/
def realised (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (w δ₀ δ₁ : E) : ℝ :=
  Deltafin a₀ (fun i => x₀ i + δ₀) a₁ (fun j => x₁ j + δ₁) w ^ 2

/-- The ellipsoid `{δ ∈ range C : δᵀ C⁺ δ ≤ β} = {C u : ⟨u, C u⟩ ≤ β}`. -/
def ellip (C : E →L[ℝ] E) (β : ℝ) : Set E := {δ | ∃ u, δ = C u ∧ ⟪u, C u⟫ ≤ β}

/-- Standing hypotheses on a weighted centre: `a_i ≥ 0`, `Σ a_i = 1`. -/
def ProbW {n : ℕ} (a : Fin n → ℝ) : Prop := (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1

end Paper2

/-! ### ICL `lem:phi` -/

section Phi
variable {Z : Type*} [MeasurableSpace Z]

/-- Coverage `ρ_ν(z) = ∫ K(z,z') dν(z')`. -/
def rhoC (Kk : Z → Z → ℝ) (ν : Measure Z) (z : Z) : ℝ := ∫ z', Kk z z' ∂ν

/-- The coverage functional `Φ(ν) = −∫ log ρ_ν dP₀`. -/
def PhiC (Kk : Z → Z → ℝ) (P₀ ν : Measure Z) : ℝ := -∫ z, Real.log (rhoC Kk ν z) ∂P₀

/-- `K` jointly measurable with values in `[K_min, K_max]`, `0 < K_min`. -/
def KernelBounds (Kk : Z → Z → ℝ) (Kmin Kmax : ℝ) : Prop :=
  0 < Kmin ∧ Measurable (Function.uncurry Kk) ∧ ∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax

end Phi

namespace Claims

open StatFormal.RobustEquality StatFormal.RobustEquality.Semidual StatFormal.RobustEquality.SemidualStrong
open StatFormal.RobustEquality.Certificate StatFormal.Wave4b StatFormal.Wave18a
open StatFormal.RobustEquality.Paper2.Seminorm

/-! #### otfd A `lem:app-block-Pl` -/

/-- If, for infinitely many `N`, `P_N X ⫫ (I − P_N)X` and the first `N` coordinates have a Lebesgue density,
then `P(X ∈ A) = 0` for every Lipschitz hypersurface `A`. -/
def app_block_Pl_null : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : HilbertBasis ℕ ℝ H) (X : Ω → H),
    Measurable X → (∀ M : ℕ, ∃ N, M ≤ N ∧ BlockHyp P f X N) →
      ∀ S : Set H, StatFormal.OTFD.Wave1.IsLipHyp S → P {ω | X ω ∈ S} = 0

/-- If moreover `E‖X‖² < ∞`, then `𝓛(X) ∈ 𝒫^ℓ(H)` (with A's second-moment clause). -/
def app_block_Pl_class : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : HilbertBasis ℕ ℝ H) (X : Ω → H),
    Measurable X → (∀ M : ℕ, ∃ N, M ≤ N ∧ BlockHyp P f X N) → ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂P < ⊤ →
      StatFormal.OTFD.Wave1.PellClass (P.map X)

/-! #### otfd A `lem:rt-depth-laplace` -/

/-- `1 − L_a ∈ L²(κ)`, `κ(dt) = (2√π)⁻¹ t^{−3/2} dt` on `(0,∞)`. -/
def rt_depth_L2 : Prop :=
  ∀ a : Measure ℝ, DepthLaw a →
    IntegrableOn (fun t => (1 - lapT a t) ^ 2 * t ^ (-(3 / 2 : ℝ))) (Ioi 0)

/-- `𝒟_φ(a,b) = (2√π)⁻¹ ∫_0^∞ (L_a(t) − L_b(t))² t^{−3/2} dt` (`= ‖(1−L_a) − (1−L_b)‖²_{L²(κ)}`), the integrand
being integrable. -/
def rt_depth_laplace : Prop :=
  ∀ a b : Measure ℝ, DepthLaw a → DepthLaw b →
    IntegrableOn (fun t => (lapT a t - lapT b t) ^ 2 * t ^ (-(3 / 2 : ℝ))) (Ioi 0) ∧
    Dphi a b = (2 * √Real.pi)⁻¹ * ∫ t in Ioi 0, (lapT a t - lapT b t) ^ 2 * t ^ (-(3 / 2 : ℝ))

/-- `𝒟_φ ≥ 0`, symmetric, `𝒟_φ(a,a) = 0`, and `𝒟_φ^{1/2}` satisfies the triangle inequality. -/
def rt_depth_metric : Prop :=
  ∀ a b c : Measure ℝ, DepthLaw a → DepthLaw b → DepthLaw c →
    0 ≤ Dphi a b ∧ Dphi a b = Dphi b a ∧ Dphi a a = 0 ∧ √(Dphi a c) ≤ √(Dphi a b) + √(Dphi b c)

/-- `𝒟_φ(a,b) = 0` if and only if `a = b` (so `𝒟_φ^{1/2}` is a metric on these laws). -/
def rt_depth_eq_zero : Prop :=
  ∀ a b : Measure ℝ, DepthLaw a → DepthLaw b → (Dphi a b = 0 ↔ a = b)

/-- `𝒟_φ(a,b) ≤ 2 W₁(a,b)`. -/
def rt_depth_W1 : Prop :=
  ∀ a b : Measure ℝ, DepthLaw a → DepthLaw b →
    ENNReal.ofReal (Dphi a b) ≤ 2 * wassersteinEDist 1 a b

/-- On laws supported in `[0,1]`, `𝒟_φ` is jointly continuous for weak convergence. -/
def rt_depth_continuous : Prop :=
  ContinuousOn (fun p : ProbabilityMeasure ℝ × ProbabilityMeasure ℝ => Dphi (p.1 : Measure ℝ) (p.2 : Measure ℝ))
    (lawsUnit ×ˢ lawsUnit)

/-- On laws supported in `[0,1]`, `𝒟_φ(a_K,b_K) → 0` if and only if `W₁(a_K,b_K) → 0`. -/
def rt_depth_W1_iff : Prop :=
  ∀ a b : ℕ → ProbabilityMeasure ℝ, (∀ K, a K ∈ lawsUnit) → (∀ K, b K ∈ lawsUnit) →
    (Tendsto (fun K => Dphi (a K : Measure ℝ) (b K : Measure ℝ)) atTop (𝓝 0) ↔
      Tendsto (fun K => wassersteinEDist 1 (a K : Measure ℝ) (b K : Measure ℝ)) atTop (𝓝 0))

/-! #### otfd B `lem:app-esssup-subgradients` -/

/-- `sup_{ξ ∈ ∂χ(w)} ⟨v, ξ⟩ ≤ ν-ess sup_{u ∈ N} ⟨v, ∇χ(u)⟩`. -/
def app_esssup_subgradients : Prop :=
  ∀ (K : ℕ) (χ : EuclideanSpace ℝ (Fin K) → ℝ) (U : Set (EuclideanSpace ℝ (Fin K)))
    (w : EuclideanSpace ℝ (Fin K)) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν],
    IsOpen U → ConvexOn ℝ U χ → w ∈ U → ν ≪ volume → (∃ V ∈ 𝓝 w, V ⊆ ν.support) →
    ∀ (v : EuclideanSpace ℝ (Fin K)) (N : Set (EuclideanSpace ℝ (Fin K))), N ∈ 𝓝 w → N ⊆ U →
      ⨆ ξ ∈ subdiffOn U χ w, ((⟪v, ξ⟫ : ℝ) : EReal) ≤ essSup (gradDir χ v) (ν.restrict N)

/-! #### robust equality JASA `lem:cert-coarse` -/

/-- `OT_ε(μ,P) ≤ OT_ε(μ̄_r,P) + D_r` for every `P` (quadratic cost). -/
def cert_coarse : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (d k r : ℕ) (φ : K → EuclideanSpace ℝ (Fin d))
    (x : Fin k → EuclideanSpace ℝ (Fin d)) (a : Fin k → ℝ) (σ : Fin k → Fin r) (ε : ℝ)
    (P : Measure K) [IsProbabilityMeasure P],
    0 < ε → (∀ i, 0 < a i) → ∑ i, a i = 1 → Function.Surjective σ → Measurable φ → (∃ R, ∀ y, ‖φ y‖ ≤ R) →
      OTdisc ε a (fun i y => ‖x i - φ y‖ ^ 2) P ≤
        OTdisc ε (clW σ a) (fun z y => ‖clBar σ a x z - φ y‖ ^ 2) P + ((clD σ a x : ℝ) : EReal)

/-! #### robust equality JASA `prop:cs-cells` -/

/-- (i) `W₂(g#μ, g'#μ) ≤ (E_μ|g − g'|²)^{1/2}`. -/
def cs_cells_coupling : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (μ : Measure K) [IsProbabilityMeasure μ] (g g' : K → ℝ),
    Measurable g → Measurable g' →
      wassersteinEDist 2 (μ.map g) (μ.map g') ≤ (∫⁻ x, ‖g x - g' x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)

/-- (i) `Δ_θ(h) ≤ Δ_{θ'}(h) + Σ_s (E_{P̂_s}|h∘𝔗_θ − h∘𝔗_{θ'}|²)^{1/2}` (both orders, by symmetry). -/
def cs_cells_nominal : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n₀ n₁ : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (h : K → ℝ)
    (T T' : K → K),
    0 < n₀ → 0 < n₁ → Measurable h → Measurable T → Measurable T' →
      nominal (fun i => T (x₀ i)) (fun i => T (x₁ i)) h ≤
        nominal (fun i => T' (x₀ i)) (fun i => T' (x₁ i)) h +
          ((∫⁻ x, ‖h (T x) - h (T' x)‖ₑ ^ (2 : ℝ) ∂centre x₀) ^ (1 / 2 : ℝ) +
            (∫⁻ x, ‖h (T x) - h (T' x)‖ₑ ^ (2 : ℝ) ∂centre x₁) ^ (1 / 2 : ℝ))

/-- (i), linear rule and affine maps: `Δ_θ ≤ Δ_{θ'} + Σ_s ‖(A_θ − A_{θ'})ᵀ w‖_{M_s}`, any translations. -/
def cs_cells_linear : Prop :=
  ∀ (d n₀ n₁ : ℕ) (x₀ : Fin n₀ → EuclideanSpace ℝ (Fin d)) (x₁ : Fin n₁ → EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin d)) (b₀ : ℝ)
    (A A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (b b' : EuclideanSpace ℝ (Fin d)),
    0 < n₀ → 0 < n₁ →
      nominal (fun i => affT A b (x₀ i)) (fun i => affT A b (x₁ i)) (linRule w b₀) ≤
        nominal (fun i => affT A' b' (x₀ i)) (fun i => affT A' b' (x₁ i)) (linRule w b₀) +
          (ENNReal.ofReal √((n₀ : ℝ)⁻¹ * ∑ i, ⟪ContinuousLinearMap.adjoint (A - A') w, x₀ i⟫ ^ 2) +
            ENNReal.ofReal √((n₁ : ℝ)⁻¹ * ∑ i, ⟪ContinuousLinearMap.adjoint (A - A') w, x₁ i⟫ ^ 2))

/-- (ii) cell bound for one group: with `f̄ ≥ f^θ_h`, `c̲ ≤ c^θ ≤ c̄` on the (anchor, reference) pairs,
`r_s(θ) = R^{𝒩_θ}_min + β` and `R̄ = R_min(c̄)`: `√T^θ_s(h,λ) ≤ √T̄_s(λ)` (`T̄`: `f̄, c̲` and radius `R̄ + β`). -/
def cs_cells_T : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (𝔗 : K → K)
    (fb cl cu : K → K → ℝ) (ε lam β r rb : ℝ) (N : Set (Measure K)),
    0 < n → 0 < ε → 0 < lam → RefClass N →
    Measurable (Function.uncurry c) → (∃ B, ∀ a b, |c a b| ≤ B) → Measurable h → (∃ H, ∀ z, |h z| ≤ H) →
    Measurable 𝔗 → (∀ i, Measurable (fb (x i))) → (∀ i, Measurable (cl (x i))) → (∀ i, Measurable (cu (x i))) →
    (∃ B, ∀ i z, |fb (x i) z| ≤ B ∧ |cl (x i) z| ≤ B ∧ |cu (x i) z| ≤ B) →
    (∀ i z, (h (𝔗 z) - h (𝔗 (x i))) ^ 2 ≤ fb (x i) z) →
    (∀ i z, cl (x i) z ≤ c (𝔗 (x i)) (𝔗 z) ∧ c (𝔗 (x i)) (𝔗 z) ≤ cu (x i) z) →
    (r : EReal) = floorGen x (fun x₀ z => c (𝔗 x₀) (𝔗 z)) ε N + (β : EReal) →
    (rb : EReal) = floorGen x cu ε N + (β : EReal) →
      sqrtTPull x c h 𝔗 ε r lam N ≤ sqrtTgen x fb cl ε rb lam N

/-- (iii) for a finite cover `Θ = ⋃_j Θ_j`, `θ_j ∈ Θ_j`, multipliers `λ_{s,j} > 0`:
`F_Θ(h) ≤ max_j (Δ_{θ_j}(h) + L_j + √T̄_{0,j}(λ_{0,j}) + √T̄_{1,j}(λ_{1,j}))²`. -/
def cs_cells_cover : Prop :=
  ∀ (K Θ : Type) [MeasurableSpace K] (n₀ n₁ J : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (c : K → K → ℝ)
    (ε β₀ β₁ : ℝ) (r₀ r₁ : Θ → ℝ) (𝔗 : Θ → K → K) (h : K → ℝ) (N₀ N₁ : Set (Measure K))
    (cell : Fin J → Set Θ) (θc : Fin J → Θ) (L : Fin J → ℝ≥0∞) (fb cl cu : Fin J → K → K → ℝ)
    (rb₀ rb₁ lam₀ lam₁ : Fin J → ℝ),
    0 < n₀ → 0 < n₁ → 0 < ε →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    Measurable h → (∃ H, ∀ z, |h z| ≤ H) → (∀ θ, Measurable (𝔗 θ)) → RefClass N₀ → RefClass N₁ →
    (∀ θ, ∃ j, θ ∈ cell j) → (∀ j, θc j ∈ cell j) → (∀ j, 0 < lam₀ j ∧ 0 < lam₁ j) →
    (∀ j, ∀ θ ∈ cell j,
      (∫⁻ x, ‖h (𝔗 θ x) - h (𝔗 (θc j) x)‖ₑ ^ (2 : ℝ) ∂centre x₀) ^ (1 / 2 : ℝ) +
        (∫⁻ x, ‖h (𝔗 θ x) - h (𝔗 (θc j) x)‖ₑ ^ (2 : ℝ) ∂centre x₁) ^ (1 / 2 : ℝ) ≤ L j) →
    (∀ j y, Measurable (fb j y) ∧ Measurable (cl j y) ∧ Measurable (cu j y)) →
    (∀ j, ∃ B, ∀ y z, |fb j y z| ≤ B ∧ |cl j y z| ≤ B ∧ |cu j y z| ≤ B) →
    (∀ j, ∀ θ ∈ cell j, ∀ z,
      (∀ i, (h (𝔗 θ z) - h (𝔗 θ (x₀ i))) ^ 2 ≤ fb j (x₀ i) z ∧
        cl j (x₀ i) z ≤ c (𝔗 θ (x₀ i)) (𝔗 θ z) ∧ c (𝔗 θ (x₀ i)) (𝔗 θ z) ≤ cu j (x₀ i) z) ∧
      (∀ i, (h (𝔗 θ z) - h (𝔗 θ (x₁ i))) ^ 2 ≤ fb j (x₁ i) z ∧
        cl j (x₁ i) z ≤ c (𝔗 θ (x₁ i)) (𝔗 θ z) ∧ c (𝔗 θ (x₁ i)) (𝔗 θ z) ≤ cu j (x₁ i) z)) →
    (∀ θ, (r₀ θ : EReal) = floorGen x₀ (fun y z => c (𝔗 θ y) (𝔗 θ z)) ε N₀ + (β₀ : EReal)) →
    (∀ θ, (r₁ θ : EReal) = floorGen x₁ (fun y z => c (𝔗 θ y) (𝔗 θ z)) ε N₁ + (β₁ : EReal)) →
    (∀ j, (rb₀ j : EReal) = floorGen x₀ (cu j) ε N₀ + (β₀ : EReal)) →
    (∀ j, (rb₁ j : EReal) = floorGen x₁ (cu j) ε N₁ + (β₁ : EReal)) →
      Fstruct x₀ x₁ c ε 𝔗 r₀ r₁ (fun θ => (fun ν => ν.map (𝔗 θ)) '' N₀)
          (fun θ => (fun ν => ν.map (𝔗 θ)) '' N₁) h ≤
        ⨆ j, (nominal (fun i => 𝔗 (θc j) (x₀ i)) (fun i => 𝔗 (θc j) (x₁ i)) h + L j +
          sqrtTgen x₀ (fb j) (cl j) ε (rb₀ j) (lam₀ j) N₀ +
          sqrtTgen x₁ (fb j) (cl j) ε (rb₁ j) (lam₁ j) N₁) ^ 2

/-- (iv) the segment `A_t = I + tB`, linear rule: `f^t = ((w + tBᵀw)ᵀu)²` and `c^t = ‖u + tBu‖²` are bounded by
their endpoint values on `[t₁,t₂]`, `c^t` is the quadratic `‖u‖² + 2t uᵀBu + t²‖Bu‖²`, minimised over `[t₁,t₂]` at
the clipped vertex. -/
def cs_cells_segment : Prop :=
  ∀ (d : ℕ) (w u : EuclideanSpace ℝ (Fin d)) (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (t₁ t₂ t : ℝ), t₁ ≤ t → t ≤ t₂ →
      ⟪w + t • ContinuousLinearMap.adjoint B w, u⟫ ^ 2 ≤
          max (⟪w + t₁ • ContinuousLinearMap.adjoint B w, u⟫ ^ 2) (⟪w + t₂ • ContinuousLinearMap.adjoint B w, u⟫ ^ 2) ∧
      ‖u + t • B u‖ ^ 2 ≤ max (‖u + t₁ • B u‖ ^ 2) (‖u + t₂ • B u‖ ^ 2) ∧
      ‖u + t • B u‖ ^ 2 = ‖u‖ ^ 2 + 2 * t * ⟪u, B u⟫ + t ^ 2 * ‖B u‖ ^ 2 ∧
      t₁ ≤ clipVertex B u t₁ t₂ ∧ clipVertex B u t₁ t₂ ≤ t₂ ∧
      ‖u + clipVertex B u t₁ t₂ • B u‖ ^ 2 ≤ ‖u + t • B u‖ ^ 2

/-! #### robust equality paper 2 `prop:structured` -/

/-- The certified worst case does not depend on `b_θ` and equals `(sup_θ Δ(A_θᵀ w) + N₀(w) + N₁(w))²`,
`N_s(w) = √β_s ‖(G_s⁻¹)ᵀ w‖` (Wasserstein: `G_s = I`; anisotropic `M_s`: `G_s = M_s^{−1/2}`). -/
def structured_value : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (Θ : Type) [Nonempty Θ]
    (n₀ n₁ : ℕ) (G₀ G₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ)
    (x₁ : Fin n₁ → E) (A : Θ → E →L[ℝ] E) (b : Θ → E) (w : E),
    0 ≤ β₀ → 0 ≤ β₁ → ProbW a₀ → ProbW a₁ →
      certStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A b w =
        ((⨆ θ, ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A θ) w))) +
          ENNReal.ofReal (√β₀ * ‖ContinuousLinearMap.adjoint (G₀.symm : E →L[ℝ] E) w‖) +
          ENNReal.ofReal (√β₁ * ‖ContinuousLinearMap.adjoint (G₁.symm : E →L[ℝ] E) w‖)) ^ 2

/-- Cell bound: `sup_θ Δ(A_θᵀ w) ≤ max_j {Δ(A_{θ_j}ᵀ w) + L_j(w)}`, `Σ_s` about any common point `p`. -/
def structured_cells : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (Θ : Type)
    (n₀ n₁ J : ℕ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E)
    (A : Θ → E →L[ℝ] E) (cell : Fin J → Set Θ) (θc : Fin J → Θ) (p w : E),
    ProbW a₀ → ProbW a₁ → (∀ θ, ∃ j, θ ∈ cell j) → (∀ j, θc j ∈ cell j) →
      ⨆ θ, ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A θ) w)) ≤
        ⨆ j, (ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w)) +
          Lcell a₀ x₀ a₁ x₁ p A (cell j) (θc j) w)

/-- Every `L_j` is a seminorm (bounded cell), and for fixed couplings `γ_j` the cell bound
`max_j (|M_{γ_j}^{1/2} A_{θ_j}ᵀ w| + L_j(w) + N₀(w) + N₁(w))²` is a convex function of `w` that dominates the
certified worst case. -/
def structured_convex : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (Θ : Type)
    (n₀ n₁ J : ℕ) (G₀ G₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ)
    (x₁ : Fin n₁ → E) (A : Θ → E →L[ℝ] E) (b : Θ → E) (cell : Fin J → Set Θ) (θc : Fin J → Θ) (p : E)
    (γ : Fin J → Fin n₀ → Fin n₁ → ℝ),
    0 ≤ β₀ → 0 ≤ β₁ → ProbW a₀ → ProbW a₁ → (∀ θ, ∃ j, θ ∈ cell j) → (∀ j, θc j ∈ cell j) →
    (∃ C, ∀ j, ∀ θ ∈ cell j, ‖A θ - A (θc j)‖ ≤ C) → (∀ j, γ j ∈ Polytope a₀ a₁) →
      (∀ j, ∃ S : Seminorm ℝ E, ∀ w, ENNReal.ofReal (S w) = Lcell a₀ x₀ a₁ x₁ p A (cell j) (θc j) w) ∧
      ∃ Cb : E → ℝ, ConvexOn ℝ univ Cb ∧
        (∀ w, ENNReal.ofReal (Cb w) =
          ⨆ j, (ENNReal.ofReal (gamNorm (γ j) x₀ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w)) +
            Lcell a₀ x₀ a₁ x₁ p A (cell j) (θc j) w +
            ENNReal.ofReal (√β₀ * ‖ContinuousLinearMap.adjoint (G₀.symm : E →L[ℝ] E) w‖) +
            ENNReal.ofReal (√β₁ * ‖ContinuousLinearMap.adjoint (G₁.symm : E →L[ℝ] E) w‖)) ^ 2) ∧
        ∀ w, certStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A b w ≤ ENNReal.ofReal (Cb w)

/-! #### robust equality paper 2 `prop:translation` -/

/-- The realised disparity is `Δ(w)² − g(w)² + (g(w) + ⟨w, δ⟩)²`, `δ = δ₀ − δ₁`. -/
def translation_identity : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ : ℕ) (a₀ : Fin n₀ → ℝ)
    (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (w δ₀ δ₁ : E),
    ProbW a₀ → ProbW a₁ →
      realised a₀ x₀ a₁ x₁ w δ₀ δ₁ =
        Deltafin a₀ x₀ a₁ x₁ w ^ 2 - gapW a₀ x₀ a₁ x₁ w ^ 2 + (gapW a₀ x₀ a₁ x₁ w + ⟪w, δ₀ - δ₁⟫) ^ 2

/-- (i) if `E δ = 0` (square-integrable), the expected realised disparity is `Δ(w)² + wᵀ C w`, `C = Cov(δ)`. -/
def translation_mean : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n₀ n₁ : ℕ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ)
    (x₁ : Fin n₁ → E) (w : E) (δ₀ δ₁ : Ω → E),
    ProbW a₀ → ProbW a₁ → Measurable δ₀ → Measurable δ₁ → MemLp (fun ω => δ₀ ω - δ₁ ω) 2 P →
    ∫ ω, (δ₀ ω - δ₁ ω) ∂P = 0 →
      ∫ ω, realised a₀ x₀ a₁ x₁ w (δ₀ ω) (δ₁ ω) ∂P =
        Deltafin a₀ x₀ a₁ x₁ w ^ 2 + covarianceBilin (P.map (fun ω => δ₀ ω - δ₁ ω)) w w

/-- (ii) over the ellipsoid `{δ ∈ range C : δᵀC⁺δ ≤ β}` the supremum is attained and equals
`Δ² − g² + (|g| + √β |C^{1/2}w|)² ≤ (Δ + √β |C^{1/2}w|)²`. -/
def translation_sup : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (w : E) (C : E →L[ℝ] E) (β : ℝ),
    ProbW a₀ → ProbW a₁ → C.IsPositive → 0 ≤ β →
      IsGreatest {v | ∃ δ₀ δ₁ : E, δ₀ - δ₁ ∈ ellip C β ∧ v = realised a₀ x₀ a₁ x₁ w δ₀ δ₁}
          (Deltafin a₀ x₀ a₁ x₁ w ^ 2 - gapW a₀ x₀ a₁ x₁ w ^ 2 +
            (|gapW a₀ x₀ a₁ x₁ w| + √β * √⟪w, C w⟫) ^ 2) ∧
        Deltafin a₀ x₀ a₁ x₁ w ^ 2 - gapW a₀ x₀ a₁ x₁ w ^ 2 + (|gapW a₀ x₀ a₁ x₁ w| + √β * √⟪w, C w⟫) ^ 2 ≤
          (Deltafin a₀ x₀ a₁ x₁ w + √β * √⟪w, C w⟫) ^ 2

/-! #### ICL `lem:phi` -/

/-- (i) `Φ` is convex in the marginal `ν`. -/
def phi_convex : Prop :=
  ∀ (Z : Type) [MeasurableSpace Z] (Kk : Z → Z → ℝ) (Kmin Kmax : ℝ) (P₀ ν₁ ν₂ : Measure Z)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (t : ℝ),
    KernelBounds Kk Kmin Kmax → 0 ≤ t → t ≤ 1 →
      PhiC Kk P₀ (ENNReal.ofReal (1 - t) • ν₁ + ENNReal.ofReal t • ν₂) ≤
        (1 - t) * PhiC Kk P₀ ν₁ + t * PhiC Kk P₀ ν₂

/-- (i) all minimisers over a convex class `𝒞` of probability marginals (e.g. all of `𝒫(𝒵)`, or the pool
marginals `Σ_j (π_j/M) δ_{z_j}`) have the same coverage, `P₀`-a.s. -/
def phi_same_coverage : Prop :=
  ∀ (Z : Type) [MeasurableSpace Z] (Kk : Z → Z → ℝ) (Kmin Kmax : ℝ) (P₀ : Measure Z) [IsProbabilityMeasure P₀]
    (C : Set (Measure Z)) (ν₁ ν₂ : Measure Z),
    KernelBounds Kk Kmin Kmax → (∀ ν ∈ C, IsProbabilityMeasure ν) →
    (∀ μ ∈ C, ∀ μ' ∈ C, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ENNReal.ofReal (1 - t) • μ + ENNReal.ofReal t • μ' ∈ C) →
    ν₁ ∈ C → ν₂ ∈ C → (∀ ν ∈ C, PhiC Kk P₀ ν₁ ≤ PhiC Kk P₀ ν) → (∀ ν ∈ C, PhiC Kk P₀ ν₂ ≤ PhiC Kk P₀ ν) →
      rhoC Kk ν₁ =ᵐ[P₀] rhoC Kk ν₂

/-- (ii) the first variation in the direction `δ_{z'} − ν` is `1 − ∫ K(z,z') ρ(z)⁻¹ dP₀(z)`. -/
def phi_first_variation : Prop :=
  ∀ (Z : Type) [MeasurableSpace Z] (Kk : Z → Z → ℝ) (Kmin Kmax : ℝ) (P₀ ν : Measure Z)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure ν] (z' : Z),
    KernelBounds Kk Kmin Kmax →
      HasDerivWithinAt (fun t : ℝ => PhiC Kk P₀ (ENNReal.ofReal (1 - t) • ν + ENNReal.ofReal t • Measure.dirac z'))
        (1 - ∫ z, Kk z z' / rhoC Kk ν z ∂P₀) (Icc 0 1) 0

/-- (iii) if each `K(·,z')` is a probability density w.r.t. a σ-finite `λ` and `P₀ = p₀ λ` has finite entropy,
`Φ(ν) = KL(P₀ ‖ K⋆ν) − ∫ p₀ log p₀ dλ`. -/
def phi_kl : Prop :=
  ∀ (Z : Type) [MeasurableSpace Z] (Kk : Z → Z → ℝ) (Kmin Kmax : ℝ) (P₀ ν lam : Measure Z)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure ν] [SigmaFinite lam] (p₀ : Z → ℝ),
    KernelBounds Kk Kmin Kmax → (∀ z', ∫ z, Kk z z' ∂lam = 1) → Measurable p₀ → (∀ z, 0 ≤ p₀ z) →
    P₀ = lam.withDensity (fun z => ENNReal.ofReal (p₀ z)) → Integrable (fun z => p₀ z * Real.log (p₀ z)) lam →
      InformationTheory.klDiv P₀ (lam.withDensity (fun z => ENNReal.ofReal (rhoC Kk ν z))) ≠ ⊤ ∧
      (InformationTheory.klDiv P₀ (lam.withDensity (fun z => ENNReal.ofReal (rhoC Kk ν z)))).toReal =
        PhiC Kk P₀ ν + ∫ z, p₀ z * Real.log (p₀ z) ∂lam

/-- (iv) for compact `𝒵` and continuous `K`, `Φ` is weakly continuous on `𝒫(𝒵)` and a minimiser exists. -/
def phi_continuous : Prop :=
  ∀ (Z : Type) [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (Kk : Z → Z → ℝ) (Kmin Kmax : ℝ) (P₀ : Measure Z) [IsProbabilityMeasure P₀],
    KernelBounds Kk Kmin Kmax → Continuous (Function.uncurry Kk) →
      Continuous (fun ν : ProbabilityMeasure Z => PhiC Kk P₀ (ν : Measure Z)) ∧
      ∃ νs : ProbabilityMeasure Z, ∀ ν : ProbabilityMeasure Z,
        PhiC Kk P₀ (νs : Measure Z) ≤ PhiC Kk P₀ (ν : Measure Z)

end Claims

end StatFormal.Wave20a
