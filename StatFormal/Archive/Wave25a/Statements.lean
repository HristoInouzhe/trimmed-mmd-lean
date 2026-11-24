import StatFormal.Archive.OTFD.Wave13b.Statements
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.Basic
import StatFormal.Archive.Wave15b.Statements
import StatFormal.Archive.Wave20a.Statements
import StatFormal.Archive.Wave20b.Statements
import StatFormal.Archive.OTFD.WaveL1.Statements
import StatFormal.Archive.OTFD.Wave22b.Statements
import StatFormal.Archive.Wave21b.Statements
import StatFormal.Archive.Wave15a.Statements
import StatFormal.Archive.Wave23c.Statements

/-!
# FROZEN STATEMENTS — wave 25a (untouched results of COVERAGE.md outside the in-progress waves): otfd R `thm:rates`
# (a)–(d); SB `prop:corrected`; robust equality JASA `thm:cert-chain`, `prop:ad-population` (core); otfd T
# `thm:pop-sieve` (reconstruction clause)

Sources (verbatim in `lean-formalisation/inventory/extracted/{otfd-R_robustness,data-fairness-repair,
robust-equality-jasa,otfd-T_tangent}.md`; current text, 2026-10-16):
* otfd R `thm:rates` (`otfd/papers/R_robustness/sections/s3_infinite.tex:131-166`, proof `appendix_a.tex:323-397`),
  with `def:beta` (`s3_infinite.tex:112-129`), `thm:cauchy` (`eq:cauchy-coverage`) and `thm:elliptical` (frozen).
* SB `prop:corrected` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:837-851`, proof `:3104-3122`), with
  `def:corrected` (`:806-817`).
* JASA `thm:cert-chain` (`robust-equality-outcomes-under-distribution-shift/jasa/supp_calibration.tex:540-557`, proof
  `:559-570`), with `lem:cert-structure` (`:475-481`), `lem:cert-odds` (`:489-494`), `eq:layer` (`:503-506`),
  `lem:cert-coarse` (`:508-512`), `lem:cert-betting` (`:521-527`) and the construction of `m̲_g`, `Ḡ`, `s̄`, `s_max`
  (`:534-538`).
* JASA `prop:ad-population` (`supp_calibration.tex:365-373`, proof `:374-388`), with `lem:ad-linear` (`:250-261`),
  `prop:ad-identity` (`:276-281`), `thm:ad-oracle` (`:330-348`).
* otfd T `thm:pop-sieve` (`otfd/papers/T_tangent/sec_tangent_theory.tex:252-267`, proof `app_proofs.tex:100-114`), with
  `ass:model` (`:89-95`), `eq:Hembed` (`:62-66`) and `lem:exp` (frozen Wave 22b).
Imports the frozen statements of `OTFD/Wave13b` (`IsCauchyFamily`, `cauchyX`, `projK`; through it `OTFD/Wave1`
`tukeyDepth`, `OTFD/Wave5a` `betaStar`, `depthRegion`), `Wave23c` (`EllSetting`, `ellLaw`, `cmNorm`), `Wave15b` (`mOdds`;
through it the robust-equality `Semidual`/`SemidualStrong` `gsoft`, `OTdisc`, `Jdual`, `Setting`), `Wave20a` (`clW`,
`clBar`, `clD`), `Wave20b` (`confSet`, `Predictable`), `Wave21b`/`Wave9a` (`rhoN`, `FW`, `GridCond`, `geomGrid`, `rThr`,
`empMean`, `empSd`), `Wave15a` (`omegaMod`), `OTFD/WaveL1` (`IsCMMapAE`, `Euc`; `PellClass`, `truncK` from `OTFD/Wave1`,
`embed` from `OTFD/Wave8b`), `OTFD/Wave22b` (`LengthBound`, `Lb`), not copied; Mathlib (`IsGaussian`, `variance`)
otherwise. New definitions: `meanV`, `covM`, `corrMap` (SB); `chainSet`, `osc`, `sBar`, `gBar`, `chainGamma`,
`chainOsc` (cert-chain).

Covered:
* `thm:rates`: (a) `rates_products` (`β*_K(p) ≤ (1 − p^{1/K})/2 ≤ log(1/p)/(2K)` for independent atomless coordinates);
  (b) `rates_cauchy` (equality for the projected Cauchy product, and the supremum is attained); (c) `rates_uniform`
  (`β*_K(p) ≤ e^{−K/12}` for `K > 18 log(1/p)`, uniform products); (d) `rates_gaussian` — CONDITIONAL on the
  Laurent–Massart lower tail of `χ²_K` (`β*_K(p) ≤ exp(−K/2 + √(K log(1/p)))`, `K > 4 log(1/p)`, mean `0`).
* `prop:corrected`: `corrected_moments` (mean `m_ν`, covariance `V_ν`, any `T(X) ∈ L²`), `corrected_gaussian` (Gaussian
  `R_s`, `ν` and affine `T^ε_s`: `(T̃^ε_s)#R_s = ν`, hence exact parity, for each group).
* `thm:cert-chain`: `chain_gap` (deterministic core: on the event that all lower confidence bounds hold,
  `Gap_P(f̂) ≤ Γ` and `osc(f* − f̂) ≤ max_𝒞 Σ s̄ 𝟏{Ḡ ≥ 0}`), `chain_prob` (both, simultaneously, with probability
  `≥ 1 − δ`, from the per-bound level `δ/((2^r − 2)(S + 1))`), `chain_ot` (`OT_ε(μ, P) ≤ D_r + ⟨w, f̂⟩ + UCB_B + Γ` with
  probability `≥ 1 − δ − δ'`, through the frozen `lem:cert-coarse` and `lem:cert-betting`).
* `prop:ad-population`: `ad_population_core` (on the event that the Bernstein and Maurer–Pontil bounds hold, up to
  additive slacks `η₁, η₂ ≥ 0`, for every `f ∈ F_W`: `ρ̂_N − Θ(P) ≤ ω_P(s₄) + 5.4 b̄ s₄ + η₁ + η₂√(2s)` for `m ≥ 20`; the
  constant is checked; the slacks make the core usable on the paper's event, which controls only a `1/m`-net).
* `thm:pop-sieve`: `pop_sieve_reconstruct` ("Under `eq:Hembed`, exponential reconstructions converge in mean squared
  `D_∞`", from the frozen `integrated_quantile_uncond` and `exp_bounds_embed`).

Not covered (declared):
* `thm:rates` (d) with a general mean `m` (affine equivariance; only `m = 0`), and the Laurent–Massart inequality itself
  (hypothesis); (e) elliptical with `E W < ∞` and (f) Student `t_ν` (need the Student tail bounds of `cor:gaussian-t`,
  in progress in wave 24e, and Laurent–Massart).
* `prop:corrected`: that the entropic barycentric projection of the Gaussian plan is affine (`lem:dplan`, OT
  identification not formalised; the claim takes `T` affine); "deterministic, as smooth as `T^ε_s`, defined everywhere"
  (immediate from the formula); the informal last sentence (higher-moment residual).
* `thm:cert-chain`: the `Γ_int` variant; the `O(2^r r)` dynamic programme; the Chernoff–Hoeffding validity of each
  lower confidence bound (its failure probability is the hypothesis of `chain_prob`, `chain_ot`).
* `prop:ad-population`: the probability statement (Bernstein and Maurer–Pontil per `f`, the `1/m`-net of `F_W` of size
  `(1 + Wm)^{k−1}`, the union bound giving `1 − e^{−L}`, and the net-to-`F_W` transfer: `g_f`, `σ_f`, `sd_{P̂_m}(g_f)` are
  1-Lipschitz in `f` for the sup norm, so the hypotheses hold with `η₁ = 2/m + √(2L'/m)/m`, `η₂ = 2/m`, in place of the
  paper's `4/m`), the corollary with
  `k log(1 + Wm) ≤ C₀ log(1/α)` and the lower bound (`thm:ad-lower`, frozen).
* `thm:pop-sieve`: `eq:popQ` and the forward limit themselves (verbatim the frozen `integrated_quantile_uncond`,
  `sieve_strong_limit_uncond`; not restated), the existence parenthetical (frozen `app_block_Pl_class`, Wave 20a), the
  `H_0` / `D_2` clause.

Encodings (to be checked by the critic):
* rates: `ℝ^K = EuclideanSpace ℝ (Fin K)`, `K ≥ 1`; the frozen `tukeyDepth`, `depthRegion` (`D_α = {TD ≥ α}`, `α ∈ [0,∞]`)
  and `betaStar` (`sSup` in `[0,∞]`, no junk); a product law is a probability `μ` whose coordinate maps are independent
  (`iIndepFun`) with atomless marginals (`NullSingletonClass`); `Unif[−h_k, h_k] = (2h_k)⁻¹ Leb|_{[−h_k,h_k]}`. (b) uses the
  frozen projected Cauchy product `(P.map cauchyX).map (projK b K)`. (d): `μ_K = 𝓛(G)`, `G` a centred Gaussian on `ℝ^K`
  with injective covariance (frozen `EllSetting` with `W ≡ 1`; the frozen `ellLaw` with `W ≡ 1` is `𝓛(G)`); the
  Laurent–Massart hypothesis is written for `‖G‖_CM² = ‖Σ^{-1/2} G‖² ∼ χ²_K`: `P(‖G‖_CM ≤ √(K − 2√(Kt))) ≤ e^{−t}`, every
  `t ≥ 0` (Laurent–Massart 2000, Lemma 1; for `K − 2√(Kt) < 0` the event is `{G = 0}`, null).
* corrected: `E_R[T(X)] = meanV`, `Cov_R(T(X)) = covM` (Bochner integrals; `T ∈ L²(R)` assumed, so no junk); `V_ν^{1/2}`
  is any symmetric `Vh` with `Vh² = V` and `P_s^{-1/2}` any symmetric `Ph` with `Ph P_s Ph = I` (GENERALISATION: the
  principal roots are instances; `Ph P_s Ph = I` forces `P_s ≻ 0`, the paper's hypothesis); "Gaussian" is Mathlib's
  `IsGaussian`; `T^ε_s(x) = Mx + c` (affine, the Gaussian case of `lem:dplan`); `m_ν = meanV ν id`, `V_ν = covM ν id`.
  Each group is one instance (the claim for `s ∈ {0,1}` is the conjunction).
* cert-chain: the coarse problem is the frozen semi-dual setting (`Setting ε w c`: `w_z > 0`, `Σ w = 1`, bounded
  measurable costs); `f*` any maximiser of `J_P`; `Gap_P(f̂) = OT_ε − J_P(f̂)` in `EReal`; maximal chains are the chains
  `U_l = σ({0..l−1})` of permutations `σ` (every maximal chain is one); `m_s(U)` is the frozen `mOdds`; the grid is any
  `s : Fin (S+1) → ℝ` with `s_0 = 0` (monotonicity not needed: GENERALISATION); `s̄(U) = min(s_max, min{s_g : g ≥ 1,
  m̲_g(U) > w(U)})` (`fold min`); `s_max = b_X + osc f̂` for any `b_X ≥ sup_y (c_z(y) − c_{z'}(y))` (the paper's `b_X` is
  the least one: GENERALISATION); `osc u = max u − min u`. Events: lower bounds are measurable functions of `ω` only
  through the hypothesis that each failure set is measurable with the stated probability; the conclusion is a
  measurable event of the stated probability on which the bounds hold. `chain_ot`: fine fold `x_i ∈ ℝ^d`, `a_i > 0`,
  quadratic cost `|x − φ(y)|²` (as frozen in `cert_coarse`), clusters `σ` surjective, `UCB_B` via any lower bound `b` of
  the betting confidence set (the frozen `cert_betting` form, avoiding `sInf` junk); `δ, δ' > 0`.
* ad-population: the frozen `rhoN`, `FW`, `GridCond`, `omegaMod` (`EReal`), `OTdisc`; `σ_f = √(Var_P g_f)` (Mathlib
  `variance`); `P̂_m g_f = empMean`, `sd_{P̂_m} = empSd` (`1/m` normalisation, so the Maurer–Pontil bound, proved for
  the `1/(m−1)` version, implies the hypothesis); `s = γ r`, `r = log(N/α)/m`; `b̄` any upper bound of `H(f) − g_f` on
  `F_W × K`; `m ≥ 20`.
* pop-sieve: the frozen `integrated_quantile_uncond` setting (`ν ∈ 𝒫^ℓ(H)` with `ν(B̄(0,B)) = 1`, `μ` with
  `μ(B̄(0,B_μ)) = 1`, `Q_ν`, `Q_K` Borel and a.e. cyclically monotone pushing `μ → ν`, `μ_K → ν_K`); fields `ι : H →ₗ (T → V)`
  with `‖(ιx)(t)‖ ≤ Λ‖x‖` (`eq:Hembed`, `Λ ≥ 0`); `D_∞(Exp v, Exp w) = sup_t d_M(Ex t (v t), Ex t (w t))` in `[0,∞]` with
  `Ex`, `D` and `LengthBound` as in the frozen `lem:exp`; `L_{ΛB} < ∞` assumed (`exp_Lb_finite` supplies it on compact
  `T`); the mean is a lower integral (no measurability needed), and the second conjunct gives measurable majorants (the
  outer integral), so the conclusion is not weakened when `D_∞` is not measurable.

Notes:
* No statement was found false. Manuscript notes: (i) `thm:rates`(d) is stated for `N(m, Σ_K)`; only `m = 0` is
  formalised (the reduction is affine equivariance). (ii) `prop:corrected` holds for every symmetric pair of roots, and
  its moment part for every `T(X) ∈ L²` (not only the barycentric map). (iii) `thm:cert-chain`'s grid needs no
  monotonicity and any `b_X ≥ max(c_z − c_{z'})` works. (iv) `prop:ad-population`: `√(20/19) + 4 + 1/3 ≈ 5.36 ≤ 5.4`,
  confirmed; its Bernstein step needs the net points in `F_W` (range `≤ b̄`), and an internal `1/m`-net of `F_W` has
  at most `(1 + 2Wm)^{k−1}` points, not `(1 + Wm)^{k−1}` (or keep the cube net and enlarge `b̄` by `2/m`). (v)
  COVERAGE.md undercounts: T `theory:217`, `theory:374`, `supp:669`, `supp:814`, `toolkit:401`, B
  `prop:certified-band-weighted` (as `cor:certified-band-rate (weighted_slack)`), B `prop:calibrations` (labelled
  `otfd A` in wave 24d) are certified under other labels, and paper 2 `prop:uniform` is the certified JASA claim.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave25a

open StatFormal.OTFD.Wave1 (tukeyDepth)
open StatFormal.OTFD.Wave5a (betaStar depthRegion)
open StatFormal.OTFD.Wave13b (IsCauchyFamily cauchyX projK)
open StatFormal.RobustEquality.Semidual (gsoft)
open StatFormal.RobustEquality.SemidualStrong (OTdisc Jdual Setting)
open StatFormal.Wave15b (mOdds)
open StatFormal.Wave20a (clW clBar clD)
open StatFormal.Wave20b (confSet Predictable)

/-! ### SB `prop:corrected` (objects) -/

section Corrected
variable {d : ℕ}

/-- The mean `E_R[T(X)]` of `T(X)`, `X ∼ R`, on `ℝ^d = EuclideanSpace ℝ (Fin d)`. -/
def meanV (R : Measure (EuclideanSpace ℝ (Fin d))) (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  ∫ x, T x ∂R

/-- The covariance matrix `Cov_R(T(X))_{ij} = E_R[(T_i − E T_i)(T_j − E T_j)]`. -/
def covM (R : Measure (EuclideanSpace ℝ (Fin d))) (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∫ x, (T x i - meanV R T i) * (T x j - meanV R T j) ∂R

/-- The moment-corrected map `T̃(x) = m + A (T(x) − E_R[T(X)])` (`eq:corrected` with `A = V^{1/2} P^{-1/2}`). -/
def corrMap (R : Measure (EuclideanSpace ℝ (Fin d))) (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (m : EuclideanSpace ℝ (Fin d)) (A : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  m + WithLp.toLp 2 (A.mulVec (WithLp.ofLp (T x - meanV R T)))

end Corrected

/-! ### robust equality JASA `thm:cert-chain` (objects) -/

section Chain
variable {r S : ℕ}

/-- The `l`-th set `U_l = σ({0, …, l−1})` of the maximal chain `U_1 ⊂ ⋯ ⊂ U_{r−1}` (`|U_l| = l`) defined by the
permutation `σ` of the `r` coarse atoms; every maximal chain of the subset lattice is of this form. -/
def chainSet (σ : Equiv.Perm (Fin r)) (l : ℕ) : Finset (Fin r) :=
  Finset.univ.filter fun i => ((σ.symm i : Fin r) : ℕ) < l

/-- `osc(u) = max_i u_i − min_i u_i`. -/
def osc (u : Fin r → ℝ) : ℝ := (⨆ i, u i) - ⨅ i, u i

/-- `s̄(U)`: the smallest grid point `s_g`, `g ≥ 1`, with `m̲_g(U) > w(U)`, capped at `s_max` (`= s_max` if there is
none). -/
def sBar (s : Fin (S + 1) → ℝ) (mlow : Fin (S + 1) → Finset (Fin r) → ℝ) (w : Fin r → ℝ) (smax : ℝ)
    (U : Finset (Fin r)) : ℝ :=
  (Finset.univ.filter fun g : Fin (S + 1) => 1 ≤ (g : ℕ) ∧ ∑ i ∈ U, w i < mlow g U).fold min smax s

/-- `Ḡ(U) = w(U) − m̲_0(U)`. -/
def gBar (mlow : Fin (S + 1) → Finset (Fin r) → ℝ) (w : Fin r → ℝ) (U : Finset (Fin r)) : ℝ :=
  ∑ i ∈ U, w i - mlow 0 U

/-- The chain certificate `Γ = max_𝒞 Σ_{U ∈ 𝒞} s̄(U) Ḡ(U)_+` over the maximal chains. -/
def chainGamma (s : Fin (S + 1) → ℝ) (mlow : Fin (S + 1) → Finset (Fin r) → ℝ) (w : Fin r → ℝ) (smax : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun σ : Equiv.Perm (Fin r) =>
    ∑ l ∈ Finset.Ioo 0 r, sBar s mlow w smax (chainSet σ l) * max 0 (gBar mlow w (chainSet σ l))

/-- The oscillation certificate `max_𝒞 Σ_{U ∈ 𝒞} s̄(U) 𝟏{Ḡ(U) ≥ 0}`. -/
def chainOsc (s : Fin (S + 1) → ℝ) (mlow : Fin (S + 1) → Finset (Fin r) → ℝ) (w : Fin r → ℝ) (smax : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun σ : Equiv.Perm (Fin r) =>
    ∑ l ∈ Finset.Ioo 0 r, if 0 ≤ gBar mlow w (chainSet σ l) then sBar s mlow w smax (chainSet σ l) else 0

end Chain

namespace Claims

/-! ### otfd R `thm:rates` -/

/-- (a) All products: if the coordinates of `μ_K` are independent with atomless marginals, then
`β*_K(p; μ_K) ≤ (1 − p^{1/K})/2 ≤ log(1/p)/(2K)`. -/
def rates_products : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ] (p : ℝ),
    1 ≤ K → 0 < p → p < 1 →
    iIndepFun (fun (k : Fin K) (z : EuclideanSpace ℝ (Fin K)) => z k) μ →
    (∀ k : Fin K, NullSingletonClass (μ.map fun z => z k)) →
      betaStar μ (ENNReal.ofReal p) ≤ ENNReal.ofReal ((1 - p ^ (1 / (K : ℝ))) / 2) ∧
        (1 - p ^ (1 / (K : ℝ))) / 2 ≤ Real.log (1 / p) / (2 * K)

/-- (b) Cauchy products: for the projected Cauchy product `μ_K = Π_K#μ`, `β*_K(p) = (1 − p^{1/K})/2` exactly, and
the supremum is attained (`μ_K(D_{β*}) ≥ p`). -/
def rates_cauchy : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (C : ℕ → Ω → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (s : ℕ → ℝ),
    IsCauchyFamily P C → (∀ k, 0 < s k) → Summable s → ∀ (K : ℕ) (p : ℝ), 1 ≤ K → 0 < p → p < 1 →
      betaStar ((P.map (cauchyX b s C)).map (projK b K)) (ENNReal.ofReal p) =
          ENNReal.ofReal ((1 - p ^ (1 / (K : ℝ))) / 2) ∧
        ENNReal.ofReal p ≤ ((P.map (cauchyX b s C)).map (projK b K))
          (depthRegion ((P.map (cauchyX b s C)).map (projK b K)) (ENNReal.ofReal ((1 - p ^ (1 / (K : ℝ))) / 2)))

/-- (c) Uniform products: if the coordinates of `μ_K` are independent with `k`-th marginal `Unif[−h_k, h_k]`
(`h_k > 0`), then `β*_K(p; μ_K) ≤ e^{−K/12}` for every `K > 18 log(1/p)`. -/
def rates_uniform : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ] (h : Fin K → ℝ) (p : ℝ),
    (∀ k, 0 < h k) → 0 < p → p < 1 → 18 * Real.log (1 / p) < K →
    iIndepFun (fun (k : Fin K) (z : EuclideanSpace ℝ (Fin K)) => z k) μ →
    (∀ k : Fin K, μ.map (fun z => z k) =
      ENNReal.ofReal (1 / (2 * h k)) • volume.restrict (Icc (-h k) (h k))) →
      betaStar μ (ENNReal.ofReal p) ≤ ENNReal.ofReal (Real.exp (-(K : ℝ) / 12))

open StatFormal.Wave23c (EllSetting ellLaw cmNorm) in
/-- (d) Gaussian, CONDITIONAL on the Laurent–Massart lower tail of `χ²_K` (written for `‖G‖²_CM`, which is `χ²_K`
for a centred Gaussian `G` with invertible covariance on `ℝ^K`): for `μ_K = N(0, Σ_K)` (mean `0`) and every
`K > 4 log(1/p)`, `β*_K(p; μ_K) ≤ exp(−K/2 + √(K log(1/p)))`. -/
def rates_gaussian : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (G : Ω → EuclideanSpace ℝ (Fin K)) (p : ℝ),
    1 ≤ K → 0 < p → p < 1 → 4 * Real.log (1 / p) < K → EllSetting Pr G (fun _ => 1) →
    (∀ t : ℝ, 0 ≤ t → Pr {ω | cmNorm Pr G (G ω) ≤ ((√(K - 2 * √(K * t)) : ℝ) : EReal)} ≤
      ENNReal.ofReal (Real.exp (-t))) →
      betaStar (ellLaw Pr G (fun _ => 1)) (ENNReal.ofReal p) ≤
        ENNReal.ofReal (Real.exp (-(K : ℝ) / 2 + √(K * Real.log (1 / p))))

/-! ### SB `prop:corrected` -/

/-- Moment matching: for a map `T` with `T(X) ∈ L²(R)`, any symmetric square root `V^{1/2}` of `V` and any symmetric
`P^{-1/2}` with `P^{-1/2} P P^{-1/2} = I`, `P = Cov_R(T(X))`, the corrected map has mean `m` and covariance `V`. -/
def corrected_moments : Prop :=
  ∀ (d : ℕ) (R : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure R]
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d))
    (V Vh Ph : Matrix (Fin d) (Fin d) ℝ),
    MemLp T 2 R → Vh.transpose = Vh → Vh * Vh = V → Ph.transpose = Ph → Ph * covM R T * Ph = 1 →
      meanV R (corrMap R T m (Vh * Ph)) = m ∧ covM R (corrMap R T m (Vh * Ph)) = V

/-- Gaussian exactness: if the group law `R` and the target `ν` are Gaussian and `T` is affine (the barycentric
projection of the Gaussian entropic plan), the corrected map pushes `R` exactly onto `ν`
(`m = m_ν`, `V = V_ν`). -/
def corrected_gaussian : Prop :=
  ∀ (d : ℕ) (R ν : Measure (EuclideanSpace ℝ (Fin d))) [IsGaussian R] [IsGaussian ν]
    (M : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (c : EuclideanSpace ℝ (Fin d))
    (Vh Ph : Matrix (Fin d) (Fin d) ℝ),
    Vh.transpose = Vh → Vh * Vh = covM ν id → Ph.transpose = Ph → Ph * covM R (fun x => M x + c) * Ph = 1 →
      R.map (corrMap R (fun x => M x + c) (meanV ν id) (Vh * Ph)) = ν

/-! ### robust equality JASA `thm:cert-chain` -/

/-- Deterministic core: on the event that every lower confidence bound holds (`m̲_g(U) ≤ m_{s_g}(U)` for every
nonempty proper `U` and grid point), `Gap_P(f̂) = OT_ε(μ̄_r, P) − J_P(f̂) ≤ Γ` and `osc(f* − f̂) ≤ max_𝒞 Σ s̄ 𝟏{Ḡ ≥ 0}`,
with `s_max = b_X + osc f̂` and `b_X ≥ c_z(y) − c_{z'}(y)` for all `z, z', y`. -/
def chain_gap : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (r S : ℕ) (ε : ℝ) (w : Fin r → ℝ) (c : Fin r → K → ℝ) (P : Measure K)
    [IsProbabilityMeasure P] (fs fh : Fin r → ℝ) (s : Fin (S + 1) → ℝ) (mlow : Fin (S + 1) → Finset (Fin r) → ℝ)
    (bX : ℝ),
    Setting ε w c → (∀ g, Jdual ε w c P g ≤ Jdual ε w c P fs) → s 0 = 0 → (∀ i j y, c i y - c j y ≤ bX) →
    (∀ g U, U.Nonempty → U ≠ Finset.univ → mlow g U ≤ mOdds ε (s g) w fh c P U) →
      OTdisc ε w c P - (Jdual ε w c P fh : EReal) ≤ (chainGamma s mlow w (bX + osc fh) : EReal) ∧
        osc (fun i => fs i - fh i) ≤ chainOsc s mlow w (bX + osc fh)

/-- With probability at least `1 − δ`, simultaneously: if each lower confidence bound `m̲_g(U)` (a random variable on
`Ω`, the `B`-part of the fold; `f̂` fixed, fitted on `A`) fails, `m̲_g(U) > m_{s_g}(U)`, on a measurable event of
probability at most `δ/((2^r − 2)(S + 1))`, then on a measurable event of probability `≥ 1 − δ` both bounds of
`chain_gap` hold. -/
def chain_prob : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (r S : ℕ) (ε : ℝ)
    (w : Fin r → ℝ) (c : Fin r → K → ℝ) (P : Measure K) [IsProbabilityMeasure P] (fs fh : Fin r → ℝ)
    (s : Fin (S + 1) → ℝ) (mlow : Ω → Fin (S + 1) → Finset (Fin r) → ℝ) (bX δ : ℝ),
    Setting ε w c → (∀ g, Jdual ε w c P g ≤ Jdual ε w c P fs) → s 0 = 0 → (∀ i j y, c i y - c j y ≤ bX) → 0 < δ →
    (∀ g U, U.Nonempty → U ≠ Finset.univ →
      MeasurableSet {ω | mOdds ε (s g) w fh c P U < mlow ω g U} ∧
        Pr {ω | mOdds ε (s g) w fh c P U < mlow ω g U} ≤ ENNReal.ofReal (δ / ((2 ^ r - 2) * (S + 1)))) →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ Pr E ∧ ∀ ω ∈ E,
        OTdisc ε w c P - (Jdual ε w c P fh : EReal) ≤ (chainGamma s (mlow ω) w (bX + osc fh) : EReal) ∧
          osc (fun i => fs i - fh i) ≤ chainOsc s (mlow ω) w (bX + osc fh)

/-- "Consequently": for the fine fold `μ = Σ_i a_i δ_{x_i}` (quadratic cost `|x_i − φ(y)|²`), its clustering `σ` with
weights `w = clW`, barycentres `x̄_z` and `D_r = clD`, the chain lower bounds of `chain_prob` (level `δ`) and the betting
bound of `lem:cert-betting` on `ĝ = g_{f̂}` (level `δ'`, `B`-sample `Y_j` iid `P`): on a measurable event of probability
`≥ 1 − δ − δ'`, `OT_ε(μ, P) ≤ D_r + ⟨w, f̂⟩ + UCB_B + Γ` for every lower bound `b` of the betting confidence set
(`UCB_B = ū − (ū − ℓ) b`). -/
def chain_ot : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (d k r S m : ℕ) (φ : K → EuclideanSpace ℝ (Fin d)) (x : Fin k → EuclideanSpace ℝ (Fin d)) (a : Fin k → ℝ)
    (σ : Fin k → Fin r) (ε : ℝ) (P : Measure K) [IsProbabilityMeasure P] (fs fh : Fin r → ℝ)
    (s : Fin (S + 1) → ℝ) (mlow : Ω → Fin (S + 1) → Finset (Fin r) → ℝ) (bX δ δ' ub lb : ℝ)
    (Yb : Fin m → Ω → K) (bet : Fin m → (Fin m → K) → ℝ),
    0 < ε → (∀ i, 0 < a i) → ∑ i, a i = 1 → Function.Surjective σ → Measurable φ → (∃ R, ∀ y, ‖φ y‖ ≤ R) →
    (∀ g, Jdual ε (clW σ a) (fun z y => ‖clBar σ a x z - φ y‖ ^ 2) P g ≤
      Jdual ε (clW σ a) (fun z y => ‖clBar σ a x z - φ y‖ ^ 2) P fs) →
    s 0 = 0 → (∀ z z' y, ‖clBar σ a x z - φ y‖ ^ 2 - ‖clBar σ a x z' - φ y‖ ^ 2 ≤ bX) → 0 < δ →
    (∀ g U, U.Nonempty → U ≠ Finset.univ →
      MeasurableSet {ω | mOdds ε (s g) (clW σ a) fh (fun z y => ‖clBar σ a x z - φ y‖ ^ 2) P U < mlow ω g U} ∧
        Pr {ω | mOdds ε (s g) (clW σ a) fh (fun z y => ‖clBar σ a x z - φ y‖ ^ 2) P U < mlow ω g U} ≤
          ENNReal.ofReal (δ / ((2 ^ r - 2) * (S + 1)))) →
    (∀ j, Measurable (Yb j)) → iIndepFun Yb Pr → (∀ j, Pr.map (Yb j) = P) →
    (∀ y, lb ≤ gsoft ε (clW σ a) fh (fun z y => ‖clBar σ a x z - φ y‖ ^ 2) y ∧
      gsoft ε (clW σ a) fh (fun z y => ‖clBar σ a x z - φ y‖ ^ 2) y ≤ ub) → lb < ub → 0 < δ' →
    (∀ j, Measurable (bet j)) → Predictable bet → (∀ j y, 0 ≤ bet j y ∧ bet j y ≤ 0.9) →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ - δ') ≤ Pr E ∧ ∀ ω ∈ E,
        ∀ b ∈ lowerBounds (confSet (fun j => bet j fun i => Yb i ω)
            (fun j => (ub - gsoft ε (clW σ a) fh (fun z y => ‖clBar σ a x z - φ y‖ ^ 2) (Yb j ω)) / (ub - lb)) δ'),
          OTdisc ε a (fun i y => ‖x i - φ y‖ ^ 2) P ≤
            ((clD σ a x + ∑ z, clW σ a z * fh z + (ub - (ub - lb) * b) +
              chainGamma s (mlow ω) (clW σ a) (bX + osc fh) : ℝ) : EReal)

/-! ### otfd T `thm:pop-sieve` (reconstruction clause) -/

open StatFormal.OTFD.Wave22b (LengthBound Lb) in
/-- "Under `eq:Hembed`, exponential reconstructions converge in mean squared `D_∞`": in the setting of `eq:popQ` (data
law `ν ∈ 𝒫^ℓ(H)` supported in `B̄_H(0, B)`, reference `μ` boundedly supported, `Q_ν` and the `Q_K` monotone maps), for
fields `ι : H → (T → V)` with `sup_t ‖(ιx)(t)‖ ≤ Λ‖x‖_H` (`eq:Hembed`), an exponential `Ex` with the length bound and
`L_{ΛB} < ∞`, `∫ D_∞(Exp(ι ι_K Q_K Π_K u), Exp(ι Q_ν u))² dμ(u) → 0`, `D_∞ = sup_t d_M`; and, since `D_∞` need not be
measurable for an abstract `Ex`, the same holds for the outer integral: there are measurable `μ`-a.e. majorants of
`D_∞²` whose integrals tend to `0`. -/
def pop_sieve_reconstruct : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (T V W M : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [PseudoEMetricSpace M]
    (e : ℕ → H) (ν μ : ProbabilityMeasure H) (Q : H → H) (B Bμ Λ : ℝ)
    (QK : (K : ℕ) → StatFormal.OTFD.WaveL1.Euc K → StatFormal.OTFD.WaveL1.Euc K)
    (Ex : T → V → M) (D : T → V → V →L[ℝ] W) (ι : H →ₗ[ℝ] (T → V)),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    StatFormal.OTFD.Wave1.PellClass (ν : Measure H) → (ν : Measure H) (Metric.closedBall 0 B)ᶜ = 0 →
    (μ : Measure H) (Metric.closedBall 0 Bμ)ᶜ = 0 →
    Measurable Q → (μ : Measure H).map Q = ν → StatFormal.OTFD.WaveL1.IsCMMapAE (μ : Measure H) Q →
    (∀ K, Measurable (QK K)) →
    (∀ K, ((μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)).map (QK K) =
      (ν : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) →
    (∀ K, StatFormal.OTFD.WaveL1.IsCMMapAE ((μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) (QK K)) →
    LengthBound Ex D → 0 ≤ Λ → (∀ x t, ‖ι x t‖ ≤ Λ * ‖x‖) → Lb D (Λ * B) ≠ ⊤ →
      Tendsto (fun K => ∫⁻ u, (⨆ t, edist
          (Ex t (ι (StatFormal.OTFD.Wave8b.embed e K (QK K (StatFormal.OTFD.Wave1.truncK e K u))) t))
          (Ex t (ι (Q u) t))) ^ 2 ∂(μ : Measure H)) atTop (𝓝 0) ∧
        ∃ g : ℕ → H → ℝ≥0∞, (∀ K, Measurable (g K)) ∧
          (∀ K, ∀ᵐ u ∂(μ : Measure H), (⨆ t, edist
            (Ex t (ι (StatFormal.OTFD.Wave8b.embed e K (QK K (StatFormal.OTFD.Wave1.truncK e K u))) t))
            (Ex t (ι (Q u) t))) ^ 2 ≤ g K u) ∧
          Tendsto (fun K => ∫⁻ u, g K u ∂(μ : Measure H)) atTop (𝓝 0)

/-! ### robust equality JASA `prop:ad-population` (deterministic core) -/

open StatFormal.Wave9a (FW rhoN) in
open StatFormal.Wave21b (GridCond geomGrid rThr empMean empSd) in
open StatFormal.Wave15a (omegaMod) in
/-- On the event that, for every `f ∈ F_W`, the Bernstein bound `P̂_m g_f − P g_f ≤ σ_f √(2L'/m) + b̄L'/(3m) + η₁` and the
Maurer–Pontil bound `sd_{P̂_m}(g_f) ≤ σ_f + b̄ √(2L'/(m−1)) + η₂` hold (`σ_f = sd_P g_f`; slacks `η₁, η₂ ≥ 0`, which
absorb the transfer from a `1/m`-net of `F_W` to all of `F_W`), and the grid condition holds for every `f ∈ F_W`,
`m ≥ 20`: `ρ̂_N − Θ(P) ≤ ω_P(s₄) + 5.4 b̄ s₄ + η₁ + η₂ √(2s)`, `s = γr`, `s₄ = (√s + √(L'/m))²`, `b̄ ≥ H(f) − g_f` on
`F_W × K` (with `η₁ = η₂ = 0`: the bound of `prop:ad-population` without its net term `4/m`). -/
def ad_population_core : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k m N : ℕ) (ε α γ bbar L' η₁ η₂ : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (H : (Fin k → ℝ) → ℝ) (P : Measure K) [IsProbabilityMeasure P] (y : Fin m → K),
    Setting ε a c → 20 ≤ m → 0 < N → 0 < α → α < 1 → 1 < γ → 0 ≤ L' → 0 ≤ η₁ → 0 ≤ η₂ →
    (∀ f ∈ FW c, ∀ z, gsoft ε a f c z ≤ H f) → (∀ f ∈ FW c, ∀ z, H f - gsoft ε a f c z ≤ bbar) →
    (∀ f ∈ FW c, GridCond N α γ (H f) (gsoft ε a f c) y) →
    (∀ f ∈ FW c, empMean (gsoft ε a f c) y - ∫ z, gsoft ε a f c z ∂P ≤
      √(variance (gsoft ε a f c) P) * √(2 * L' / m) + bbar * L' / (3 * m) + η₁) →
    (∀ f ∈ FW c, empSd (gsoft ε a f c) y ≤ √(variance (gsoft ε a f c) P) + bbar * √(2 * L' / (m - 1)) + η₂) →
      rhoN ε α a c H (geomGrid γ N) y - OTdisc ε a c P ≤
        omegaMod ε a c P ((√(γ * rThr N m α) + √(L' / m)) ^ 2) +
          ((5.4 * bbar * (√(γ * rThr N m α) + √(L' / m)) ^ 2 + η₁ + η₂ * √(2 * (γ * rThr N m α)) : ℝ) : EReal)

end Claims
end StatFormal.Wave25a
