import StatFormal.Archive.RobustEquality.Semidual.Statements
import StatFormal.Archive.Wave23a.Statements
import StatFormal.Archive.OTFD.Conformal.Statements
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# FROZEN STATEMENTS — wave 24b (QUEUE rows 303, 306): otfd G `prop:blindspot` (b) (and the fitted part of (c)),
# `thm:rates` at a fixed finite reference (deterministic core and the `1/n` rate)

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-G_geodesic.md`; current text checked 2026-10-15):
* G `thm:rates` (`otfd/papers/G_geodesic/main.tex:855-878`), proof `app:rates` (`appendix.tex:626-715`, up to the
  paragraph *Quantiles*), with `def:ranks` (`main.tex:512-526`), `eq:estimators` (`main.tex:846-852`) and
  `ass:bounded` (`main.tex:276-278`).
* G `prop:blindspot` (`main.tex:975-1032`), proof of (b), (c) (`appendix.tex:401-426`), with `lem:reduction`
  (`appendix.tex:299-374`) and `prop:test` (`main.tex:931-955`).
Imports the frozen `RobustEquality.Semidual` (`gsoft`), `Wave23a` (`IsSchrodinger`) and `OTFD.Conformal` (`unif`)
statements, not copied; Mathlib otherwise.

Covered:
* `thm:rates` (reference draws held fixed: `μ = Σ_j b_j δ_{V_j}`): `rates_strong_concavity` (strong concavity of the
  semi-dual in gradient form, modulus `ε⁻¹ e^{−(L+c̄)/ε}` on potentials of oscillation `≤ L`), `rates_dual_gradient`
  (`dualGrad` is the derivative of `J_Q` along lines), `rates_potential` (population first-order condition
  `∫ p_{f*}(j,·) dP = 1`, and `Var_b(f̂ − f*) ≤ ε² e^{4c̄/ε} Σ_j b_j Δ_j²` in terms of the dual-gradient deviation
  `Δ_j = 1 − ∫ p_{f*}(j,·) dQ`, any probability `Q`), `rates_rank_uniform` (`sup_y` conditional-mean error
  `≤ 2U e^{8c̄/ε} (Σ_j b_j Δ_j²)^{1/2}` for labels bounded by `U`), and the rates, with errors measurable in the
  sample and `P`-integrable: `rates_rank` (`E∫‖F̂ − F_ε‖² dP ≤ K_ε/n` and the same for `|ϱ̂ − ϱ_ε|`),
  `rates_radial` (`R̂`), `rates_cost` (`κ̂`, constant `K_ε c̄²`), with the explicit `K_ε = 4 e^{18c̄/ε}`.
* `prop:blindspot` (b), flat space, exact pooled plan, every `n`, `n'`, `r`: `blindspot_test_grp`,
  `blindspot_test_mc` (statistics of the labels and the fitted ranks and radial ranks: the `p`-value is
  measurable, has the same law as when every curve has law `P₁`, and `P(p ≤ α) ≤ α`), `blindspot_cost_grp`,
  `blindspot_cost_mc` (statistics also involving the fitted costs, under equal laws of `(ξ(X), ‖ζ(X)‖)`).
  `blindspot_fit_factor` ((b)–(c), fitted part): for reference draws in `S`, the pooled fit equals the fit of the
  projected curves `ξ(X_i)`, the costs shifted by `½‖ζ(X_i)‖²`.

Not covered (declared):
* `thm:rates`: the `1/r` term (the population reference `μ` of `def:reference` is not atomic, so `F_ε` there is the
  rank of a continuous–continuous entropic problem; the two-sample Rigollet–Stromme analysis, the reference
  concentration and `lem:stratified`'s `2/r` for Algorithm 1 are not formalised — here `F_ε` is the population rank
  for the fixed draws); the quantile clause (Fréchet barycentres on Hadamard and spherical `M`, `α_ρ = 2ρ cot 2ρ`;
  not even its flat case); the remark that the bounds are dimension-free is visible only in the explicit constant.
* `prop:blindspot`: (a) (population plans: general `μ` needs Nutz's Gibbs form; the Foundations semi-discrete theory
  needs bounded costs, so not even finite `μ` with the unbounded quadratic cost) and the injectivity of `Φ_S`; the
  first sentence of (c) (population costs, `E‖ζ‖²`); (d) curved `M`; (e) Borsuk–Ulam; (f) full rank; Sinkhorn
  iterates stopped at a tolerance (the paper says (b) is for the exact plan).

Encodings (to be checked by the critic):
* rates: reference atoms `j : Fin k` with weights `b_j > 0`, `Σ b = 1` (any weights: `1/r`, or the atoms of
  stratified/antithetic draws once drawn) and labels `V_j` in a real normed space `E`, `‖V_j‖ ≤ 1`; data space `K`
  any measurable space, `P` a probability law; costs `c_j = c_s(V_j, ·)` measurable with `0 ≤ c_j ≤ c̄` on all of
  `K` (paper: on `supp μ × supp P`, `c̄ = ½(s+B)²` under `ass:bounded`; any upper bound `c̄` is allowed, and `K`
  may be taken to be a full-measure set). The reference potential is any maximiser of the semi-dual
  `J_Q(f) = Σ_j b_j f_j + ∫ g_f dQ` (`semiDual`, `IsMaxDual`; `g_f = gsoft` is the canonical data potential; a
  maximiser exists and is the potential of the plan by Foundations/SemiDiscrete strong duality and first-order
  conditions); `π_f(j|y) = condRef`, `F = condMean` with `ψ_j = V_j`, `R` with `‖V_j‖`, `κ` with `c_j`;
  `F̂` uses any maximiser `f̂(x)` of `J_{P_n}`, `P_n = empLaw x` (`= eq:estimators` at a fixed reference). The
  sample is `Measure.pi`; `E` is the lower Lebesgue integral of `ofReal` of the error, which is proved measurable
  in the sample and `P`-integrable in `y` (so it is the true expectation). Strong concavity is stated as strong
  monotonicity of `dualGrad_j = b_j − ∫ π_f(j|·) dQ`, which `rates_dual_gradient` identifies with `∂J_Q/∂f_j`.
  `Δ_j = dualGrad_j(f*)/b_j` for `Q = P_n` is the paper's reference coordinate of `∇Φ(f*, g*)` (the data
  coordinate vanishes for the semi-dual). `Var_b(h) = varW b h` (the paper's `L²(μ_r)` norm after the constant
  normalisation). `K_ε` is made explicit (the paper only asserts existence).
* blindspot: `M = ℝ^q`, so curves and tangent fields live in one separable real inner-product space `H`
  (`SecondCountableTopology`, Borel), `E_m(sv) = m + sv`, `c_s(v, x) = ½‖m + sv − x‖²`; `S` any subspace with an
  orthogonal projection (`HasOrthogonalProjection`, e.g. finite-dimensional), `Π = S.starProjection`,
  `ξ(x) = Π(x − m)`, `ζ(x) = (x − m) − ξ(x)`; the unit-ball and non-degeneracy hypotheses on `μ` are not needed
  for (b). Pooled sample `x : Fin N → H` with independent coordinates of laws `Q_i` (`Measure.pi`) such that
  `ξ_# Q_i = ξ_# P₁` (paper: `Q_i ∈ {P₁, P₂}`, `ξ_# P₁ = ξ_# P₂`; this is a generalisation); the comparison law
  has every coordinate `P₁`. Reference draws: any law `ν` on `(Fin r → H)` carried by `S^r`, independent of the
  data (product measure; covers i.i.d. draws and Algorithm 1). The exact plan between `μ_r` and the pooled
  empirical law is a solution of the frozen `Wave23a.IsSchrodinger` (`a = 1/N`, `b = 1/r`, `u_j = m + sV_j`);
  `fitW` reads its conditional weights through a choice of solution (one exists, and the weights do not depend on
  the choice — proved; the `else 0` branch is unreachable for `ε, N, r > 0`). Fitted rank, radial rank and cost
  are in-sample conditional means (`fitRanks`, `fitRanksCost`); signs and (calibrated) depths are measurable
  functions of these vectors, so they are covered by `T`. Labels `lab : Fin N → Bool` are fixed (any labels); the
  statistic `T(labels, fit)` is measurable in the fit for each label vector and invariant under simultaneous
  re-indexing by `σ ∈ 𝒢` (any subgroup of permutations; the paper uses all of them); relabelling permutes the
  labels and keeps the pooled fit (`pvalGrp`: whole group; `pvalMC`: `g_1..g_B` i.i.d. `unif 𝒢`, independent).
  "Same law" is equality of `Measure.map` (the `p`-value is proved measurable, so not the junk value); the level
  bound holds for every real `α`.

Critic notes:
* All 12 claims are proved in `Wave24b/Route{Softmax,Sharp,FOC,SolF,Rates,RatesExp,Gradient,Blind,BlindTest,
  BlindClaims,BlindMC}.lean` (axioms: propext, Classical.choice, Quot.sound). Routes reuse Foundations/SemiDiscrete
  (`exists_max_Jdual`, `foc_Jdual`, `foc_Jdual'`, `integral_empMeasure`), Foundations/Exchangeable
  (`grp_test_valid`, `mc_test_valid`, `relabel`, `pi_map_comp_perm`) and Foundations/Concentration
  (`integral_norm_meanDev_sq`). Uniqueness of the discrete potentials is reproved for arbitrary cost matrices
  (from the strong monotonicity of the softmax), and the measurability of the pooled fit comes from a Lusin–Souslin
  argument (closed graph of the normalised potential), not from the continuity of the plan used in the paper.
* Constants (critic, 2026-10-15). The paper's modulus `ε⁻¹ e^{−(2L+c̄)/ε}` (`appendix.tex:647-656`) is for the
  two-potential dual `Φ(f, g)` on `S_L = {‖f‖_∞, ‖g‖_∞ ≤ L, P_n(g) = 0}`, with `L = 3c̄`, i.e. `ε⁻¹ e^{−7c̄/ε}`; it
  re-derives correctly (the density exponent `f ⊕ g − c` is `≥ −2L − c̄`; the cross term vanishes), as do
  `osc f*, osc g* ≤ c̄`, `‖g*‖_∞ ≤ c̄`, `‖f*‖_∞ ≤ 2c̄`, `|ĝ| ≤ 2c̄`, `‖f̄‖_∞ ≤ 3c̄`, `‖ḡ‖_∞ ≤ 2c̄` (`:638-646`).
  The draft first stated the semi-dual modulus as `ε⁻¹ e^{−(3L+c̄)/ε}` (a proof artefact of a two-point tilt
  bound); it is now the sharp `ε⁻¹ e^{−(L+c̄)/ε}` for oscillation `≤ L` (mean value theorem along the segment,
  `Var_{π_t} ≥ e^{−(L+c̄)/ε} Var_b`, `RouteSharp`), and the downstream constants follow: `e^{4c̄/ε}` (was `8`),
  `2U e^{8c̄/ε}` (was `10`), `K_ε = 4 e^{18c̄/ε}` (was `22`). At the potentials (`osc ≤ c̄`) the modulus is
  `ε⁻¹ e^{−2c̄/ε}`, better than the paper's `ε⁻¹ e^{−7c̄/ε}`; the paper only asserts that some `K_ε` exists, so
  no claim is weaker than the paper.
* No statement was found false. Observations: (1) (b) holds for any reference law on `S^r`, with no unit-ball or
  non-degeneracy condition and no moments, and for non-identically distributed curves with the projected law of
  `P₁`; (2) at a fixed finite reference the rank error is bounded uniformly in `y`, not only in `L²(P)`.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory Finset
open scoped ENNReal

namespace StatFormal.Wave24b

open StatFormal.RobustEquality.Semidual (gsoft)

/-! ### `thm:rates`: the semi-discrete problem at a fixed finite reference -/

section Rates

variable {K : Type*} [MeasurableSpace K] {k n : ℕ}

/-- The semi-dual `J_Q(f) = Σ_j b_j f_j + ∫ g_f dQ`, `g_f = gsoft` the soft-min (canonical) data potential. -/
def semiDual (ε : ℝ) (b : Fin k → ℝ) (c : Fin k → K → ℝ) (Q : Measure K) (f : Fin k → ℝ) : ℝ :=
  ∑ j, b j * f j + ∫ y, gsoft ε b f c y ∂Q

/-- `f` maximises the semi-dual `J_Q` (a reference potential of the entropic plan between `μ = Σ_j b_j δ_{V_j}`
and `Q`). -/
def IsMaxDual (ε : ℝ) (b : Fin k → ℝ) (c : Fin k → K → ℝ) (Q : Measure K) (f : Fin k → ℝ) : Prop :=
  ∀ f', semiDual ε b c Q f' ≤ semiDual ε b c Q f

/-- The empirical law `P_n = n⁻¹ Σ_i δ_{x_i}`. -/
def empLaw (x : Fin n → K) : Measure K :=
  ∑ i, ((n : ℝ≥0∞)⁻¹) • Measure.dirac (x i)

/-- The conditional reference law `π_f(j | y) = b_j e^{(f_j − c_j(y))/ε} / Σ_l b_l e^{(f_l − c_l(y))/ε}`. -/
def condRef (ε : ℝ) (b f : Fin k → ℝ) (c : Fin k → K → ℝ) (y : K) (j : Fin k) : ℝ :=
  b j * Real.exp ((f j - c j y) / ε) / ∑ l, b l * Real.exp ((f l - c l y) / ε)

/-- Conditional mean of the labels `ψ_j(y)`: `Σ_j π_f(j | y) ψ_j(y)` (rank `ψ_j = V_j`, radial rank `ψ_j = ‖V_j‖`,
transport cost `ψ_j = c_j`). -/
def condMean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ε : ℝ) (b f : Fin k → ℝ)
    (c : Fin k → K → ℝ) (ψ : Fin k → K → E) (y : K) : E :=
  ∑ j, condRef ε b f c y j • ψ j y

/-- The coordinate `∂J_Q/∂f_j = b_j − ∫ π_f(j | ·) dQ` of the semi-dual gradient. -/
def dualGrad (ε : ℝ) (b : Fin k → ℝ) (c : Fin k → K → ℝ) (Q : Measure K) (f : Fin k → ℝ) (j : Fin k) : ℝ :=
  b j - ∫ y, condRef ε b f c y j ∂Q

/-- The plan density `p_f(j, y) = e^{(f_j + g_f(y) − c_j(y))/ε} = π_f(j | y)/b_j`. -/
def gibbsD (ε : ℝ) (b f : Fin k → ℝ) (c : Fin k → K → ℝ) (j : Fin k) (y : K) : ℝ :=
  Real.exp ((f j + gsoft ε b f c y - c j y) / ε)

/-- The dual-gradient deviation `Δ_j = 1 − ∫ p_f(j, ·) dQ` (`= dualGrad / b_j`). -/
def dualDev (ε : ℝ) (b : Fin k → ℝ) (c : Fin k → K → ℝ) (Q : Measure K) (f : Fin k → ℝ) (j : Fin k) : ℝ :=
  1 - ∫ y, gibbsD ε b f c j y ∂Q

/-- `Var_b(h) = Σ_j b_j (h_j − Σ_l b_l h_l)²`. -/
def varW (b h : Fin k → ℝ) : ℝ :=
  ∑ j, b j * (h j - ∑ l, b l * h l) ^ 2

/-- Standing hypotheses: `ε > 0`, reference weights `b_j > 0` summing to one, measurable costs with
`0 ≤ c_j ≤ c̄`. -/
def RatesHyp (ε cbar : ℝ) (b : Fin k → ℝ) (c : Fin k → K → ℝ) : Prop :=
  0 < ε ∧ (∀ j, 0 < b j) ∧ ∑ j, b j = 1 ∧ (∀ j, Measurable (c j)) ∧ ∀ j y, 0 ≤ c j y ∧ c j y ≤ cbar

end Rates

/-! ### `prop:blindspot` (b): pooled fits in flat space -/

section Blind

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

open Classical in
/-- Conditional weights `π̂(j | X_i)` of the exact entropic plan between `μ_r = r⁻¹ Σ_j δ_{V_j}` and the pooled
empirical law `N⁻¹ Σ_i δ_{X_i}`, cost `c_s(v, x) = ½‖m + s v − x‖²`, temperature `ε`: for a solution `(f, g)` of the
Schrödinger system (frozen `Wave23a.IsSchrodinger` with `u_j = m + s V_j`),
`π̂(j | X_i) = r⁻¹ e^{(f_i + g_j − c_s(V_j, X_i))/ε}`. -/
def fitW (ε s : ℝ) (m : H) {N r : ℕ} (x : Fin N → H) (V : Fin r → H) (i : Fin N) (j : Fin r) : ℝ :=
  if h : ∃ f g, StatFormal.Wave23a.IsSchrodinger ε (fun _ => ((N : ℝ))⁻¹) x (fun _ => ((r : ℝ))⁻¹)
      (fun l => m + s • V l) f g then
    ((r : ℝ))⁻¹ * Real.exp ((h.choose i + h.choose_spec.choose j - ‖(m + s • V j) - x i‖ ^ 2 / 2) / ε)
  else 0

/-- Fitted rank and radial rank of the pooled curves: `(F̂(X_i), R̂(X_i)) = (Σ_j π̂(j|X_i) V_j, Σ_j π̂(j|X_i) ‖V_j‖)`. -/
def fitRanks (ε s : ℝ) (m : H) {N r : ℕ} (x : Fin N → H) (V : Fin r → H) : Fin N → H × ℝ :=
  fun i => (∑ j, fitW ε s m x V i j • V j, ∑ j, fitW ε s m x V i j * ‖V j‖)

/-- Fitted rank, radial rank and transport cost `κ̂(X_i) = Σ_j π̂(j|X_i) c_s(V_j, X_i)` of the pooled curves. -/
def fitRanksCost (ε s : ℝ) (m : H) {N r : ℕ} (x : Fin N → H) (V : Fin r → H) : Fin N → H × ℝ × ℝ :=
  fun i => (∑ j, fitW ε s m x V i j • V j, ∑ j, fitW ε s m x V i j * ‖V j‖,
    ∑ j, fitW ε s m x V i j * (‖(m + s • V j) - x i‖ ^ 2 / 2))

/-- Whole-group permutation `p`-value of a statistic `T(labels, fit)`: `#{σ ∈ 𝒢 : T(lab ∘ σ, y) ≥ T(lab, y)}/|𝒢|`
(the labels are permuted, the pooled fit `y` is kept). -/
def pvalGrp {Y : Type*} {N : ℕ} (𝒢 : Subgroup (Equiv.Perm (Fin N))) [Fintype 𝒢]
    (T : (Fin N → Bool) → (Fin N → Y) → ℝ) (lab : Fin N → Bool) (y : Fin N → Y) : ℝ :=
  ((univ.filter fun σ : 𝒢 => T lab y ≤ T (lab ∘ (σ : Equiv.Perm (Fin N))) y).card : ℝ) / Fintype.card 𝒢

/-- Monte-Carlo permutation `p`-value `(1 + #{b : T(lab ∘ g_b, y) ≥ T(lab, y)})/(B + 1)`. -/
def pvalMC {Y : Type*} {N B : ℕ} {𝒢 : Subgroup (Equiv.Perm (Fin N))}
    (T : (Fin N → Bool) → (Fin N → Y) → ℝ) (lab : Fin N → Bool) (y : Fin N → Y) (g : Fin B → 𝒢) : ℝ :=
  (1 + ((univ.filter fun b : Fin B => T lab y ≤ T (lab ∘ ((g b : 𝒢) : Equiv.Perm (Fin N))) y).card : ℝ)) / (B + 1)

end Blind

namespace Claims

/-! #### `thm:rates` -/

/-- Strong concavity of the semi-dual (gradient form): if `osc f, osc f' ≤ L`, then
`⟨∇J_Q(f) − ∇J_Q(f'), f' − f⟩ ≥ ε⁻¹ e^{−(L + c̄)/ε} Var_b(f' − f)`. -/
def rates_strong_concavity : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε cbar L : ℝ) (b : Fin k → ℝ) (c : Fin k → K → ℝ)
    (Q : Measure K) [IsProbabilityMeasure Q] (f f' : Fin k → ℝ),
    RatesHyp ε cbar b c → (∀ j l, f j - f l ≤ L) → (∀ j l, f' j - f' l ≤ L) →
      Real.exp (-(L + cbar) / ε) / ε * varW b (f' - f) ≤
        ∑ j, (f' j - f j) * (dualGrad ε b c Q f j - dualGrad ε b c Q f' j)

/-- `dualGrad` is the gradient of the semi-dual: `d/dt J_Q(f + t h)|_{t=0} = Σ_j h_j ∂J_Q/∂f_j`. -/
def rates_dual_gradient : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε cbar : ℝ) (b : Fin k → ℝ) (c : Fin k → K → ℝ)
    (Q : Measure K) [IsProbabilityMeasure Q] (f h : Fin k → ℝ),
    RatesHyp ε cbar b c →
      HasDerivAt (fun t : ℝ => semiDual ε b c Q (f + t • h)) (∑ j, h j * dualGrad ε b c Q f j) 0

/-- Potential error bound: for maximisers `f*` of `J_P` and `f̂` of `J_Q` (`Q = P_n` in the theorem, any probability
law here), `∫ p_{f*}(j, ·) dP = 1` and `Var_b(f̂ − f*) ≤ ε² e^{4c̄/ε} Σ_j b_j Δ_j²`, `Δ_j = 1 − ∫ p_{f*}(j, ·) dQ`. -/
def rates_potential : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε cbar : ℝ) (b : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P Q : Measure K) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (fstar fhat : Fin k → ℝ),
    RatesHyp ε cbar b c → IsMaxDual ε b c P fstar → IsMaxDual ε b c Q fhat →
      (∀ j, ∫ y, gibbsD ε b fstar c j y ∂P = 1) ∧
        varW b (fhat - fstar) ≤ ε ^ 2 * Real.exp (4 * cbar / ε) * ∑ j, b j * dualDev ε b c Q fstar j ^ 2

/-- Uniform conditional-mean error: for labels `‖ψ_j(y)‖ ≤ U`, every `y`,
`‖Σ_j (π_{f̂} − π_{f*})(j | y) ψ_j(y)‖ ≤ 2U e^{8c̄/ε} (Σ_j b_j Δ_j²)^{1/2}`. -/
def rates_rank_uniform : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε cbar U : ℝ) (b : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P Q : Measure K) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (fstar fhat : Fin k → ℝ)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ψ : Fin k → K → E),
    RatesHyp ε cbar b c → IsMaxDual ε b c P fstar → IsMaxDual ε b c Q fhat → (∀ j y, ‖ψ j y‖ ≤ U) →
      ∀ y, ‖condMean ε b fhat c ψ y - condMean ε b fstar c ψ y‖ ≤
        2 * U * Real.exp (8 * cbar / ε) * Real.sqrt (∑ j, b j * dualDev ε b c Q fstar j ^ 2)

/-- `thm:rates`, ranks and rank radius, at a fixed finite reference `μ = Σ_j b_j δ_{V_j}`, `‖V_j‖ ≤ 1`: for `X_1..X_n`
i.i.d. `P` and any choice `f̂(X)` of maximisers of `J_{P_n}`, the errors are measurable in the sample and
`E ∫ ‖F̂ − F_ε‖² dP ≤ 4 e^{18c̄/ε}/n`, `E ∫ |‖F̂‖ − ‖F_ε‖|² dP ≤ 4 e^{18c̄/ε}/n`. -/
def rates_rank : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k n : ℕ) (ε cbar : ℝ) (b : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P : Measure K) [IsProbabilityMeasure P] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Fin k → E) (fstar : Fin k → ℝ) (fhat : (Fin n → K) → Fin k → ℝ),
    RatesHyp ε cbar b c → 0 < n → (∀ j, ‖V j‖ ≤ 1) → IsMaxDual ε b c P fstar →
    (∀ x, IsMaxDual ε b c (empLaw x) (fhat x)) →
      (∀ x, Integrable (fun y => ‖condMean ε b (fhat x) c (fun j _ => V j) y -
          condMean ε b fstar c (fun j _ => V j) y‖ ^ 2) P) ∧
      (∀ x, Integrable (fun y => (‖condMean ε b (fhat x) c (fun j _ => V j) y‖ -
          ‖condMean ε b fstar c (fun j _ => V j) y‖) ^ 2) P) ∧
      (Measurable fun x => ∫ y, ‖condMean ε b (fhat x) c (fun j _ => V j) y -
          condMean ε b fstar c (fun j _ => V j) y‖ ^ 2 ∂P) ∧
      (Measurable fun x => ∫ y, (‖condMean ε b (fhat x) c (fun j _ => V j) y‖ -
          ‖condMean ε b fstar c (fun j _ => V j) y‖) ^ 2 ∂P) ∧
      ∫⁻ x, ENNReal.ofReal (∫ y, ‖condMean ε b (fhat x) c (fun j _ => V j) y -
          condMean ε b fstar c (fun j _ => V j) y‖ ^ 2 ∂P) ∂(Measure.pi fun _ : Fin n => P) ≤
        ENNReal.ofReal (4 * Real.exp (18 * cbar / ε) / n) ∧
      ∫⁻ x, ENNReal.ofReal (∫ y, (‖condMean ε b (fhat x) c (fun j _ => V j) y‖ -
          ‖condMean ε b fstar c (fun j _ => V j) y‖) ^ 2 ∂P) ∂(Measure.pi fun _ : Fin n => P) ≤
        ENNReal.ofReal (4 * Real.exp (18 * cbar / ε) / n)

/-- `thm:rates`, radial rank `R̂ = Σ_j π̂(j|·) ‖V_j‖`: `E ∫ |R̂ − R_ε|² dP ≤ 4 e^{18c̄/ε}/n`. -/
def rates_radial : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k n : ℕ) (ε cbar : ℝ) (b : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P : Measure K) [IsProbabilityMeasure P] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Fin k → E) (fstar : Fin k → ℝ) (fhat : (Fin n → K) → Fin k → ℝ),
    RatesHyp ε cbar b c → 0 < n → (∀ j, ‖V j‖ ≤ 1) → IsMaxDual ε b c P fstar →
    (∀ x, IsMaxDual ε b c (empLaw x) (fhat x)) →
      (∀ x, Integrable (fun y => (condMean ε b (fhat x) c (fun j _ => ‖V j‖) y -
          condMean ε b fstar c (fun j _ => ‖V j‖) y) ^ 2) P) ∧
      (Measurable fun x => ∫ y, (condMean ε b (fhat x) c (fun j _ => ‖V j‖) y -
          condMean ε b fstar c (fun j _ => ‖V j‖) y) ^ 2 ∂P) ∧
      ∫⁻ x, ENNReal.ofReal (∫ y, (condMean ε b (fhat x) c (fun j _ => ‖V j‖) y -
          condMean ε b fstar c (fun j _ => ‖V j‖) y) ^ 2 ∂P) ∂(Measure.pi fun _ : Fin n => P) ≤
        ENNReal.ofReal (4 * Real.exp (18 * cbar / ε) / n)

/-- `thm:rates`, transport cost `κ̂ = Σ_j π̂(j|·) c_j`: `E ∫ |κ̂ − κ_ε|² dP ≤ 4 c̄² e^{18c̄/ε}/n` (`K_ε` times `c̄²`). -/
def rates_cost : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k n : ℕ) (ε cbar : ℝ) (b : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P : Measure K) [IsProbabilityMeasure P] (fstar : Fin k → ℝ) (fhat : (Fin n → K) → Fin k → ℝ),
    RatesHyp ε cbar b c → 0 < n → IsMaxDual ε b c P fstar → (∀ x, IsMaxDual ε b c (empLaw x) (fhat x)) →
      (∀ x, Integrable (fun y => (condMean ε b (fhat x) c c y - condMean ε b fstar c c y) ^ 2) P) ∧
      (Measurable fun x => ∫ y, (condMean ε b (fhat x) c c y - condMean ε b fstar c c y) ^ 2 ∂P) ∧
      ∫⁻ x, ENNReal.ofReal (∫ y, (condMean ε b (fhat x) c c y - condMean ε b fstar c c y) ^ 2 ∂P)
          ∂(Measure.pi fun _ : Fin n => P) ≤
        ENNReal.ofReal (4 * cbar ^ 2 * Real.exp (18 * cbar / ε) / n)

/-! #### `prop:blindspot` (b) -/

/-- `prop:blindspot` (b)–(c), the pooled fit itself: if the reference draws lie in `S`, the fitted ranks and radial
ranks of the pooled curves are those of the projected curves `ξ(X_i) = Π(X_i − m)` (base point `0`), and the
fitted costs are theirs plus `½‖ζ(X_i)‖²`, `ζ(x) = (x − m) − ξ(x)`; so every fitted quantity is a function of
`(ξ(X_i), ‖ζ(X_i)‖)_i` and the reference draws. -/
def blindspot_fit_factor : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (S : Submodule ℝ H) [S.HasOrthogonalProjection]
    (m : H) (s ε : ℝ) (N r : ℕ) (x : Fin N → H) (V : Fin r → H),
    0 < ε → 0 < N → 0 < r → (∀ j, V j ∈ S) →
      fitRanks ε s m x V = fitRanks ε s 0 (fun i => S.starProjection (x i - m)) V ∧
      ∀ i, fitRanksCost ε s m x V i =
        ((fitRanksCost ε s 0 (fun i => S.starProjection (x i - m)) V i).1,
          (fitRanksCost ε s 0 (fun i => S.starProjection (x i - m)) V i).2.1,
          (fitRanksCost ε s 0 (fun i => S.starProjection (x i - m)) V i).2.2 +
            ‖(x i - m) - S.starProjection (x i - m)‖ ^ 2 / 2)

/-- `prop:blindspot` (b), rank statistics, whole group: if every curve's law has the projection law
`ξ_# Q_i = ξ_# P₁`, `ξ(x) = Π(x − m)`, and the reference draws (any law `ν`, independent of the data) lie in `S`,
then the `p`-value of any re-indexing-invariant statistic of the labels and the pooled fitted ranks and radial ranks
is measurable, has the same law as when every curve has law `P₁`, and `P(p ≤ α) ≤ α`. -/
def blindspot_test_grp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] (S : Submodule ℝ H) [S.HasOrthogonalProjection] (m : H) (s ε : ℝ) (N r : ℕ)
    (P₁ : Measure H) [IsProbabilityMeasure P₁] (Q : Fin N → Measure H) [∀ i, IsProbabilityMeasure (Q i)]
    (ν : Measure (Fin r → H)) [IsProbabilityMeasure ν] (𝒢 : Subgroup (Equiv.Perm (Fin N))) [Fintype 𝒢]
    (T : (Fin N → Bool) → (Fin N → H × ℝ) → ℝ) (lab : Fin N → Bool),
    0 < ε → 0 < N → 0 < r → (∀ᵐ V ∂ν, ∀ j, V j ∈ S) → (∀ l, Measurable (T l)) →
    (∀ σ ∈ 𝒢, ∀ l y, T (l ∘ σ) (y ∘ σ) = T l y) →
    (∀ i, (Q i).map (fun x => S.starProjection (x - m)) = P₁.map (fun x => S.starProjection (x - m))) →
      (Measurable fun ω : (Fin N → H) × (Fin r → H) => pvalGrp 𝒢 T lab (fitRanks ε s m ω.1 ω.2)) ∧
      ((Measure.pi Q).prod ν).map (fun ω => pvalGrp 𝒢 T lab (fitRanks ε s m ω.1 ω.2)) =
        ((Measure.pi fun _ : Fin N => P₁).prod ν).map (fun ω => pvalGrp 𝒢 T lab (fitRanks ε s m ω.1 ω.2)) ∧
      ∀ α : ℝ, ((Measure.pi Q).prod ν) {ω | pvalGrp 𝒢 T lab (fitRanks ε s m ω.1 ω.2) ≤ α} ≤ ENNReal.ofReal α

/-- `prop:blindspot` (b), rank statistics, Monte Carlo: as `blindspot_test_grp`, with `g_1..g_B` i.i.d. uniform on
`𝒢`, independent of the data and of the reference draws. -/
def blindspot_test_mc : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] (S : Submodule ℝ H) [S.HasOrthogonalProjection] (m : H) (s ε : ℝ) (N r B : ℕ)
    (P₁ : Measure H) [IsProbabilityMeasure P₁] (Q : Fin N → Measure H) [∀ i, IsProbabilityMeasure (Q i)]
    (ν : Measure (Fin r → H)) [IsProbabilityMeasure ν] (𝒢 : Subgroup (Equiv.Perm (Fin N))) [Fintype 𝒢]
    [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (T : (Fin N → Bool) → (Fin N → H × ℝ) → ℝ) (lab : Fin N → Bool),
    0 < ε → 0 < N → 0 < r → (∀ᵐ V ∂ν, ∀ j, V j ∈ S) → (∀ l, Measurable (T l)) →
    (∀ σ ∈ 𝒢, ∀ l y, T (l ∘ σ) (y ∘ σ) = T l y) →
    (∀ i, (Q i).map (fun x => S.starProjection (x - m)) = P₁.map (fun x => S.starProjection (x - m))) →
      (Measurable fun ω : ((Fin N → H) × (Fin r → H)) × (Fin B → 𝒢) =>
          pvalMC T lab (fitRanks ε s m ω.1.1 ω.1.2) ω.2) ∧
      (((Measure.pi Q).prod ν).prod (Measure.pi fun _ : Fin B => StatFormal.OTFD.Conformal.unif 𝒢)).map
          (fun ω => pvalMC T lab (fitRanks ε s m ω.1.1 ω.1.2) ω.2) =
        (((Measure.pi fun _ : Fin N => P₁).prod ν).prod
            (Measure.pi fun _ : Fin B => StatFormal.OTFD.Conformal.unif 𝒢)).map
          (fun ω => pvalMC T lab (fitRanks ε s m ω.1.1 ω.1.2) ω.2) ∧
      ∀ α : ℝ, (((Measure.pi Q).prod ν).prod (Measure.pi fun _ : Fin B => StatFormal.OTFD.Conformal.unif 𝒢))
          {ω | pvalMC T lab (fitRanks ε s m ω.1.1 ω.1.2) ω.2 ≤ α} ≤ ENNReal.ofReal α

/-- `prop:blindspot` (b), statistics that also involve the fitted transport costs, whole group: the same conclusions
when every curve's law has the law of `(ξ(X), ‖ζ(X)‖)`, `ζ(x) = (x − m) − ξ(x)`, of `P₁`. -/
def blindspot_cost_grp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] (S : Submodule ℝ H) [S.HasOrthogonalProjection] (m : H) (s ε : ℝ) (N r : ℕ)
    (P₁ : Measure H) [IsProbabilityMeasure P₁] (Q : Fin N → Measure H) [∀ i, IsProbabilityMeasure (Q i)]
    (ν : Measure (Fin r → H)) [IsProbabilityMeasure ν] (𝒢 : Subgroup (Equiv.Perm (Fin N))) [Fintype 𝒢]
    (T : (Fin N → Bool) → (Fin N → H × ℝ × ℝ) → ℝ) (lab : Fin N → Bool),
    0 < ε → 0 < N → 0 < r → (∀ᵐ V ∂ν, ∀ j, V j ∈ S) → (∀ l, Measurable (T l)) →
    (∀ σ ∈ 𝒢, ∀ l y, T (l ∘ σ) (y ∘ σ) = T l y) →
    (∀ i, (Q i).map (fun x => (S.starProjection (x - m), ‖(x - m) - S.starProjection (x - m)‖)) =
      P₁.map (fun x => (S.starProjection (x - m), ‖(x - m) - S.starProjection (x - m)‖))) →
      (Measurable fun ω : (Fin N → H) × (Fin r → H) => pvalGrp 𝒢 T lab (fitRanksCost ε s m ω.1 ω.2)) ∧
      ((Measure.pi Q).prod ν).map (fun ω => pvalGrp 𝒢 T lab (fitRanksCost ε s m ω.1 ω.2)) =
        ((Measure.pi fun _ : Fin N => P₁).prod ν).map (fun ω => pvalGrp 𝒢 T lab (fitRanksCost ε s m ω.1 ω.2)) ∧
      ∀ α : ℝ, ((Measure.pi Q).prod ν) {ω | pvalGrp 𝒢 T lab (fitRanksCost ε s m ω.1 ω.2) ≤ α} ≤
        ENNReal.ofReal α

/-- `prop:blindspot` (b), statistics that also involve the fitted transport costs, Monte Carlo. -/
def blindspot_cost_mc : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] (S : Submodule ℝ H) [S.HasOrthogonalProjection] (m : H) (s ε : ℝ) (N r B : ℕ)
    (P₁ : Measure H) [IsProbabilityMeasure P₁] (Q : Fin N → Measure H) [∀ i, IsProbabilityMeasure (Q i)]
    (ν : Measure (Fin r → H)) [IsProbabilityMeasure ν] (𝒢 : Subgroup (Equiv.Perm (Fin N))) [Fintype 𝒢]
    [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (T : (Fin N → Bool) → (Fin N → H × ℝ × ℝ) → ℝ) (lab : Fin N → Bool),
    0 < ε → 0 < N → 0 < r → (∀ᵐ V ∂ν, ∀ j, V j ∈ S) → (∀ l, Measurable (T l)) →
    (∀ σ ∈ 𝒢, ∀ l y, T (l ∘ σ) (y ∘ σ) = T l y) →
    (∀ i, (Q i).map (fun x => (S.starProjection (x - m), ‖(x - m) - S.starProjection (x - m)‖)) =
      P₁.map (fun x => (S.starProjection (x - m), ‖(x - m) - S.starProjection (x - m)‖))) →
      (Measurable fun ω : ((Fin N → H) × (Fin r → H)) × (Fin B → 𝒢) =>
          pvalMC T lab (fitRanksCost ε s m ω.1.1 ω.1.2) ω.2) ∧
      (((Measure.pi Q).prod ν).prod (Measure.pi fun _ : Fin B => StatFormal.OTFD.Conformal.unif 𝒢)).map
          (fun ω => pvalMC T lab (fitRanksCost ε s m ω.1.1 ω.1.2) ω.2) =
        (((Measure.pi fun _ : Fin N => P₁).prod ν).prod
            (Measure.pi fun _ : Fin B => StatFormal.OTFD.Conformal.unif 𝒢)).map
          (fun ω => pvalMC T lab (fitRanksCost ε s m ω.1.1 ω.1.2) ω.2) ∧
      ∀ α : ℝ, (((Measure.pi Q).prod ν).prod (Measure.pi fun _ : Fin B => StatFormal.OTFD.Conformal.unif 𝒢))
          {ω | pvalMC T lab (fitRanksCost ε s m ω.1.1 ω.1.2) ω.2 ≤ α} ≤ ENNReal.ofReal α

end Claims

end StatFormal.Wave24b
