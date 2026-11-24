import StatFormal.Archive.RobustEquality.SemidualStrong.Statements
import StatFormal.Archive.RobustEquality.AllPairs.Statements
import StatFormal.Archive.Wave25a.Statements
import StatFormal.Archive.Wave19b.Statements
import StatFormal.Archive.WaveP2c.Statements
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# FROZEN STATEMENTS — wave 29d: robust equality JASA, remaining partial coverage
# (`thm:loc-lower` (i), (ii); `lem:lindsay` for a general mixing space, the free end, the bathtub;
# `thm:cert-chain` `Γ_int` and the dynamic programme; `thm:ep-limit0` (i) density bounds and the free class
# `ε log n`; `prop:tax` (b) the resolution class)

Sources (current text of 2026-10-17, `robust-equality-outcomes-under-distribution-shift/jasa/`):
* `thm:loc-lower` (`supp_proofs.tex:569-586`, proof `:588-604`), with the fold notation of `supp_proofs.tex:35-45`
  (`μ = Σ_{i≤k} a_i δ_{x_i}`, `c_i = c(x_i, ·)`, `g_f`, `J_Q`, `D̄`), `lem:semidual` (`:63-105`, frozen) and the envelope
  `σ̃² = ½ E D̄(X, X')²` (`supp_proofs.tex:564-566`).
* `lem:lindsay` (`supp_proofs.tex:385-395`, proof `:397-404`), with `ass:mixture` (`:225-230`), the likelihoods `ψ_i`
  (`:269-272`, Step 2 of the proof of `prop:strong`), `Λ^𝒩_s = max_m n⁻¹ Σ_i log ∫ ψ_i dm` (`:296-297`) and the
  reference convention (`:14-23`).
* `thm:cert-chain` (`supp_calibration.tex:548-569`, proof `:571-585`), with `eq:layer` (`:503-506`), `lem:cert-odds`
  (`:489-501`) and the construction of `m̲_g`, `Ḡ`, `s̄`, `s_max` (`:529-536`).
* `thm:ep-limit0` (i), density bounds and free class (`supp_eps.tex:177-191`, proof `:209-216`).
* `prop:tax` (b), resolution class (`supp_proofs.tex:636-646`, proof `:648-657`), with the recording hypothesis `H_J`
  and the corrected definition of `𝒩^res_β` (`supp_proofs.tex:626-633`, mixing over the disjoint union `L_rec` of the
  closed boxes; DEFECTS #98).
Imports the frozen `RobustEquality/Semidual` (`gsoft`, `muDisc`), `RobustEquality/SemidualStrong` (`OTdisc`, `Jdual`,
`Setting`), `RobustEquality/AllPairs` (`Dbar`), `Wave25a` (`chainSet`, `osc`, `sBar`, `gBar`, `chainGamma`,
`chainOsc`; through it `Wave15b` `mOdds`, `Wave20a` `clW`, `clBar`, `clD`, `Wave20b` `confSet`, `Predictable`) and
`Wave19b` (`floorW`), `WaveP2c` (`boxSet`, `boxMix`, `gaussProd`; through it `Wave21a` `varkappa`) and
`RobustEquality/Tax` (`tax`) statements, not copied; Mathlib otherwise. New definitions: `canonGap`, `twoPt`, `lowPt`, `highPt`,
`cTwo` (loc-lower); `psiK`, `npmleK`, `lambdaK`, `lindsayDK`, `lindsaySupK`, `MixSettingK`, `MeasConvex`, `densClass`,
`phiRule` (lindsay); `segLen`, `aBar`, `chainGammaInt`, `dpVal`, `gammaTerm`, `oscTerm`, `intTerm` (cert-chain); `resClass`
(tax).

Covered:
* `thm:loc-lower` (the frozen RobustEquality/Lower `twopoint` is `eq:twopoint`):
  `loclower_unseen` ((i): over `𝔓 = 𝒫(K)`, with probability `≥ ½ − δ` under `P₀`, `ρ̂ − OT_ε(μ, P₀) ≥ (1 − 2^{−1/m}) G₀`,
  and `(1 − 2^{−1/m}) G₀ ≥ (log 2) G₀/m − (log 2)² G₀/m²`, the `O(m^{−2})` made explicit);
  `loclower_instab_var` ((ii), first assertion: `g̃₀(−R) = g̃₀(R)` and `Var_{P₀} g̃₀(Y) = 0`, for every maximiser of
  `J_{P₀}`), `loclower_instab` ((ii), the excess bound for every `κ ∈ (0, m/2]`), `loclower_envelope` ((ii), last
  clause: `σ̃ = 2R²`).
* `lem:lindsay`, general mixing space (the frozen Wave 9a covers finite `L`): `lindsay_gen_sandwich`
  (`L(m̂) ≤ Λ ≤ L(m̂) + log sup_{m ∈ 𝓜} ∫ D_{m̂} dm`, any measurable `L`, any `𝓜 ⊆ 𝒫(L)`), `lindsay_gen_maximiser`
  (equality throughout at a maximiser over a convex `𝓜`), `lindsay_gen_dirac` (`𝓜 = 𝒫(L)`, `L` compact metric,
  Feller kernel, continuous exponents: the supremum is `D_{m̂}(y)` at a point `y ∈ L`, i.e. attained at `δ_y`; the free
  end is `L = K`, `κ = δ`), `lindsay_bathtub` (the density-bounded class `{ν ∈ 𝒫(K) : dν/dLeb ≤ M}`, `K ⊂ ℝ^d` compact:
  if `D_{m̂}` has no level set of positive measure there is `θ` with `Leb(K ∩ {D_{m̂} > θ}) = 1/M`, and the supremum is
  the bathtub value `M ∫_{K ∩ {D_{m̂} > θ}} D_{m̂} dLeb`, attained at `M·Leb|_{K ∩ {D > θ}}`);
  `lindsay_attain_refuted` (REFUTATION, critic 2026-10-20: the attainment clause "a point `y ∈ L` when `𝓜 = 𝒫(L)`
  (for the free end, a point of `K`)" fails for the Conventions' bounded measurable rules `h`; `K = L = [−1, 1]`, free
  end, one anchor `x₀ = 0`).
* `thm:cert-chain` (the frozen Wave 25a covers `Γ`, the oscillation bound, the union bound and the `OT_ε` bound):
  `certchain_int_gap` (deterministic core: `Gap_P(f̂) ≤ Γ_int` on the event that all lower bounds hold, increasing
  grid), `certchain_int_le` (`Γ_int ≤ Γ`, for lower bounds nondecreasing along the grid — see Encodings),
  `certchain_int_prob` (with probability `≥ 1 − δ`), `certchain_int_ot` (`OT_ε(μ, P) ≤ D_r + ⟨w, f̂⟩ + UCB_B + Γ_int`
  with probability `≥ 1 − δ − δ'`), `certchain_dp` (the subset-lattice dynamic programme
  `V(∅) = 0`, `V(U) = t(U) + max_{i ∈ U} V(U ∖ {i})` returns exactly `Γ`, the oscillation certificate and `Γ_int` at
  `U = [r]`).
* `thm:ep-limit0` (i), density bounds: `eplimit_density` (for `ν = q·Leb|_K` with `q_min ≤ q ≤ q_max` on `K`,
  `vol(B̄(x, s) ∩ K) ≥ κ s^d` for `x ∈ K`, `s ≤ s₀`, anchors in `K`, and `0 < ε ≤ s₀²`:
  `(d/2) ε log(1/(πε)) − ε log q_max ≤ R_ε ≤ (d/2) ε log(1/ε) + ε(1 + log(1/(q_min κ)))`); `eplimit_free_logn` (free
  class, first bound: `R^{𝒫(K)}_ε ≤ OT_ε(P̂, P̂) ≤ ε log n`, any bounded cost vanishing on the diagonal).
* `prop:tax` (b), resolution class: `tax_res` (`τ_{𝒩^res_β}(P) ≤ d ϰ(β)` under `H_J` with finitely many recorded boxes;
  the smooth-class half is the frozen WaveP2c `tax_b_smooth`).

Not covered (declared):
* `thm:loc-lower`: the remark after the proof (the modulus `ω_P`; studied in `sec:ad`, frozen elsewhere).
* `lem:lindsay`: Bauer's maximum principle for a general convex weakly closed `𝓜 ⊆ 𝒫(L)` with `L` infinite (needs the
  weak-* topology of `𝒫(L)` inside a locally convex space; the finite-`L` version is the frozen Wave 9a
  `lindsay_extreme`). The cases the lemma lists are all covered: `𝒫(L)` (`lindsay_gen_dirac`), the density-bounded
  class (`lindsay_bathtub`), dictionaries (`lindsay_dirac`, frozen).
* `thm:cert-chain`: the Chernoff–Hoeffding validity of each lower bound (the hypothesis, as in the frozen Wave 25a);
  the step count `O(2^r r)` of the dynamic programme (a statement about the cost of a memoised evaluation, which a
  mathematical recursion does not carry; the earlier draft's conjuncts `|2^{[r]}| = 2^r`, `Σ_U |U| = r 2^{r−1}` were
  Mathlib facts about `Finset` cardinalities unconnected to `dpVal` and were dropped by the critic).
* `thm:ep-limit0`: the second free-class bound `(d/2) ε log(1/ε) + ε(1 + log(vol K/κ))` (needs the primal
  coupling `P̂ ⊗ K^ε` and its relative entropy), "`R_ε = (d/2) ε log(1/ε) + O(ε)` uniformly in the centre" (immediate
  from `eplimit_density`, not restated), (ii) and the (iii) infima and disparities.
* `cor:cs-translation`: nothing new. The corollary is about affine maps only; the reweighting family (b) belongs to
  `thm:cs-certificate` (whose frozen card declares it), so the corollary is fully covered by the frozen Wave 18a.
* `prop:ep-gauss`: nothing new. The Gaussian integral is the frozen WaveP1c `ep_gauss_kernel`, `ep_gauss_T`; with the
  frozen Wave 11a `gauss_*` the proposition is fully covered.

Encodings (to be checked by the critic):
* Folds as in the frozen `SemidualStrong` (labelled atoms `Fin k`, weights `a`, bounded measurable `c_i` on any
  measurable `K`: a generalisation of compact `K`, continuous `c`); `Θ(Q) = OTdisc ε a c Q` (`EReal`, finite under
  `Setting`, so `OT + t ≤ ρ̂` is `ρ̂ − OT ≥ t`). A valid bound over `𝔓 = 𝒫(K)`: `ρ̂` measurable,
  `P^m[OT_ε(μ, P) ≤ ρ̂] ≥ 1 − δ` for every probability `P` (the same form as the frozen `twopoint`).
* `loclower_unseen`: the canonical potential is `g̃₀ = g_{f*}` for any maximiser `f*` of `J_{P₀}` (maximisers differ
  by constants, which leave `G₀` unchanged); `G₀ = sup_K g̃₀ − E_{P₀} g̃₀` (`canonGap`, `⨆` in `ℝ` of a function bounded
  above, `K ≠ ∅`): the printed `max_K` when `K` is compact and `c` continuous, so the claim with the supremum is the
  stronger one. `2^{−1/m}` is `rpow`; `m ≥ 1`.
* `loclower_instab*`: `K = [−R, R]` as the subtype `Icc (−R) R`, `R > 0`, atoms `x_0 = −R`, `x_1 = R`, `a = (½, ½)`,
  `c_i(y) = (x_i − y)²` (`cTwo`), `P₀ = ½δ_{−R} + ½δ_R` (`twoPt`, the same law as `μ` on the labels). The variance is
  Mathlib's `variance` (genuine: `g̃₀` is bounded), and the equality `g̃₀(−R) = g̃₀(R)` is stated alongside. `σ̃² =
  ½ E D̄(X, X')²` with the frozen `Dbar` (`max_i |c_i(y) − c_i(y')|`), `X, X'` i.i.d. `P₀`.
* `lindsay_*`: `L` any measurable space, `κ` a Mathlib `Kernel L K` (measurable in `y`) with `0 < κ(y, K) ≤ 1`, the
  exponents `φ_i = φ(x_i, ·) = (f_h − λc)(x_i, ·)/(λε)` any bounded measurable functions, `n ≥ 1` (`MixSettingK`);
  `ν_m = m.bind κ`; `ψ_i(y) = ∫ e^{φ_i} dκ_y` (`psiK`); `L(m) = n⁻¹ Σ_i log ∫ ψ_i dm` (`npmleK`);
  `Λ = sup_{m ∈ 𝓜} n⁻¹ Σ_i log ∫ e^{φ_i} dν_m` (`lambdaK`, the printed `Λ^𝒩_s` with `𝒩 = {ν_m}`, before Fubini);
  `D_{m̂} = n⁻¹ Σ_i ψ_i/∫ ψ_i dm̂` (`lindsayDK`); `sup_{m ∈ 𝓜} ∫ D_{m̂} dm` (`lindsaySupK`). `lindsay_attain_refuted`:
  `φ_i = (f_h − λc)(x_i, ·)/(λε)` with `f_h(x₀, x) = (h(x) − h(x₀))²`, `c = |·|²` (`phiRule`, `K = [−1, 1]` as the
  subtype `Icc (−1) 1`); the negated universal ranges over all bounded measurable `h`, `λ, ε > 0` and `m̂ ∈ 𝒫(K)`, with
  `κ = Kernel.id` (`ass:mixture` holds: `L = K` compact metric, `κ(y, K) = 1`, Feller); a junk `sSup` (unbounded set,
  value `0`) cannot rescue attainment since `D_{m̂} > 0`, and the proof treats that case separately. `𝓜` is a set of probability
  measures; convexity is `MeasConvex` (closed under `θm + (1−θ)m'`). `lindsay_gen_dirac`: `L` compact metric with its
  Borel σ-algebra, `K` compact with its Borel σ-algebra, the Feller condition of `ass:mixture` ("`y ↦ ∫ g dκ_y`
  continuous for every continuous `g`"), and CONTINUOUS exponents: `ψ_i` is continuous only then (the source: Step 2 of
  `prop:strong`, "under Assumption ass:mixture and continuity of `h`"; see the manuscript notes). `lindsay_bathtub`:
  `K ⊂ ℝ^d = EuclideanSpace ℝ (Fin d)` compact, `κ = Kernel.id` (`ν_m = m`, `ψ_i = e^{φ_i}`), the class `densClass K M =
  {ν ∈ 𝒫(ℝ^d) : ν ≤ M · Leb|_K}` (so `ν(Kᶜ) = 0`), `m̂` in the class; "no level set of positive measure":
  `Leb(K ∩ {D = t}) = 0` for every `t`; the value attained (`IsGreatest`) and equal to `lindsaySupK`.
* `certchain_*`: the objects of the frozen Wave 25a. The grid is strictly increasing with `s_0 = 0`, `s_{S+1} = ∞`;
  `|[s_g, s_{g+1}) ∩ [0, t]| = max(0, min(s_{g+1}, t) − max(s_g, 0))` (`segLen`, with `min(∞, t) = t`);
  `Ā(U) = Σ_g (w(U) − m̲_g(U))_+ |[s_g, s_{g+1}) ∩ [0, s̄(U)]|` (`aBar`); `Γ_int = max_𝒞 Σ_{U ∈ 𝒞} Ā(U)`
  (`chainGammaInt`, maximal chains as permutations, as in `chainGamma`). `certchain_int_le` assumes
  `m̲_0(U) ≤ m̲_g(U)` for all `g` (CONDITIONALISATION, see the manuscript notes: the paper's Chernoff–Hoeffding bounds
  are monotone in the data and the data `φ_{s_g}(π_{f̂}(U|Y_j))` increase with `g`, so it holds for the paper's
  construction; for arbitrary lower bounds `Γ_int ≤ Γ` can fail) and `s_max ≥ 0` (true for `s_max = b_X + osc f̂`).
  `dpVal T U` is the recursion `V(∅) = 0`, `V(U) = T(U) + max_{i ∈ U} V(U ∖ {i})` (well founded on `|U|`); the terms
  `gammaTerm`, `oscTerm`, `intTerm` are the chain summands on nonempty proper `U` and `0` on `[r]`.
* `eplimit_density`: `ℝ^d = EuclideanSpace ℝ (Fin d)`, `c = |·|²`, the frozen `floorW` (`R_ε = −ε Σ_i a_i log ∫ e^{−c_i/ε}
  dν`) with anchors `x_i ∈ K`; `ν = (Leb|_K).withDensity q`, `q` measurable, `q_min ≤ q ≤ q_max` on `K`, `q_min > 0`
  (the lower bound uses only `q ≤ q_max`, the upper only `q ≥ q_min`; both assumed, as printed). The ball is closed
  (the hypothesis with the open ball implies it, so the claim is the stronger one). `eplimit_free_logn`: labelled
  atoms with uniform weights `1/n` (the empirical centre), `Q = P̂` as `Σ_j n⁻¹ δ_{x_j}`, `R^{𝒫(K)}_ε` as `⨅` over
  probability measures in `EReal`; the cost any bounded measurable `c_i` with `c_i(x_i) = 0` (generalisation of `dist²`).
* `tax_res`: `ℝ^d = Fin d → ℝ`, the WaveP2c recording model (finitely supported recording law, `boxMix`); a mixing law
  on `L_rec = ⊔_{y ∈ Y} {y} × B(y)` is `Σ_y w_y δ_y ⊗ m_y` (`w ∈ 𝒫(Y)`, `m_y ∈ 𝒫(B(y))`), and the atom `(y, y')` carries
  `N(y', β² S(y)²) = G_{βs(y)} ∗ δ_{y'}` (`gaussProd`), so the reference is `(Σ_y w_y G_{βs(y)} ∗ m_y)|_K` (`resClass`);
  `ϰ` the frozen `varkappa` (finite, `≥ 0`, so `toReal` is exact).

Junk audit: `OTdisc` is finite under `Setting` (frozen strong duality), so the `EReal` sums are genuine; `canonGap` is
an `iSup` in `ℝ` of a function bounded above (`g_f ≤ B − min f`) over a nonempty type; `2^{−1/m}` with `m ≥ 1`;
`√(κ/2)`, `√(κ/m)` of positive numbers; `variance` of a bounded function (finite `evariance`). `lambdaK`, `lindsaySupK`
are `sSup` of nonempty sets (`m̂ ∈ 𝓜`) bounded above (`φ` bounded, `κ(y, K) ≤ 1`, `∫ ψ_i dm̂ ≥ e^{−B} ∫ κ(y, K) dm̂(y) >
0`); every `log` has a positive argument and every integrand is bounded measurable, hence integrable for finite
measures. `densClass` members are probability measures; `M > 0`, `1/M`. `segLen` is a genuine length (`max 0`).
`floorW`: positive integrals (`q ≥ q_min > 0` on `K`, `vol(B̄ ∩ K) > 0`), so no `log 0`. No `Measure.map` of a
non-measurable map; no `toReal`; no `sInf ∅`.

Proof notes (author of the draft, 2026-10-17): all 16 claims are proved in `Wave29d/Route{LocLower,LocLowerTwo,Lindsay,
Bathtub,ChainInt,ChainDP,EpLimitDensity,EpLimitFree,TaxRes}.lean` (`#print axioms`: propext, Classical.choice,
Quot.sound), on the new libraries `Foundations/{Bathtub,Lindsay,ChainInt}/Basic.lean`, the certified RobustEquality
`Semidual`, `SemidualStrong`, `Lower` routes, `Foundations/Distances`, Wave 15b, 19b, 25a, P2c routes and Tau Ceti.
* `loclower_unseen`: per `z`, `P₁ = (1−η)P₀ + ηδ_z` dominates `(1−η)P₀`, so `P₁^m ≥ ½P₀^m` and
  `P₀^m[OT(P₁) ≤ ρ̂] ≥ 1 − 2δ`; the frozen subgradient gives `OT(P₁) ≥ OT(P₀) + η(g̃₀(z) − E g̃₀)`; continuity from above
  along a maximising sequence of `z` gives the supremum; `|e^x − 1 − x| ≤ x²`.
* `loclower_instab*`: `OT(P_t) ≥ J_{P_t}(4R², 0) ≥ 4R² t`; `OT(P₀) = max J ≤ ε log 2` (drop one exponential per soft-min);
  Pinsker + tensorisation, `KL(P₀‖P_t) ≤ KL(B₀‖B_t) = −½ log(1 − 4t²) ≤ 4t²` through the two-point map from `Fin 2`;
  the first-order condition at label `0` forces `k(u₁² − u₀²) = 0`; the envelope by evaluation.
* `lindsay_gen_*`: Fubini for `m.bind κ` (`compProd`), Jensen for `log`, the right derivative of
  `t ↦ L((1−t)m̂ + tm)` at `0`; Dirac: `ψ_i` continuous by the Feller condition, `D` attains its maximum on compact `L`.
  `lindsay_bathtub`: level-set intermediate value (continuity from above and below, null level sets), the bathtub
  inequality `∫ D dν ≤ θ + ∫ (D − θ)_+ dν ≤ θ + M ∫_K (D − θ)_+`.
* `certchain_int_*`: `J(f*) − J(f̂) ≤ ∫_0^1 φ` (`sub_le_integral_of_hasDeriv_right_of_le`, derivative from the frozen
  `cert_structure_ii_grad`), the derivative bounded by Abel summation and `lem:cert-odds` at `f_t` (the plan `π_{f_t}` is
  the tilt of `π_{f̂}`) by the step function `Σ_g (w − m̲_g)_+ 𝟏_{[s_g, s_{g+1})}`, then a change of variables per level.
  The union bound and the `OT_ε` consequence are the frozen `chain_prob`/`chain_ot` arguments. `certchain_dp`: chains
  of `U` ↔ permutations with `σ({0..|U|−1}) = U` (swap construction); `certchain_int_le`: the cell lengths sum to `s̄`.
* `eplimit_density`: restrict to `B̄(x, √ε) ∩ K` (exponent `≥ −1`) for the upper bound on `R_ε`; extend to `ℝ^d` and the
  Gaussian integral `(πε)^{d/2}` for the lower bound. `eplimit_free_logn`: strong duality and
  `g_f(x_j) ≤ ε log n − f_j`. `tax_res`: the WaveP2c per-box bound with box-dependent bandwidths `β s_k(y)`
  (`ϰ(βs_k/s_k) = ϰ(β)`), joint convexity over the boxes, restriction to `K`, `η ↓ 0`.
* No tautology: no conclusion is among the hypotheses; existence of `θ` is proved (`lindsay_bathtub`), and the objects
  of the claims are the paper's (no copy of a frozen claim).
* Observations / manuscript notes: (1) `thm:loc-lower`(i): domination gives `P₀^m[excess ≥ (1−2^{−1/m})G₀] ≥ 1 − 2δ`,
  better than the printed `½ − δ` for `δ < ½` (the TV step is not needed); `max_K` may be replaced by `sup_K` (no
  compactness or continuity needed), and `O(m^{−2})` is at most `(log 2)² G₀/m²`. (2) `thm:loc-lower`(ii): the variance
  vanishes for EVERY maximiser (not only the symmetric one), and validity is used only at the alternatives `P_t`.
  (3) `lem:lindsay`: attainment at a point of `L` needs `ψ_i` continuous, i.e. a continuous rule `h`; the lemma states
  only `ass:mixture`, while `ψ_i` is defined in Step 2 of `prop:strong` "under Assumption ass:mixture and continuity of
  `h`". With the Conventions' bounded measurable `h` attainment can fail (`K = L = [−1,1]`, free end, one anchor
  `x₀ = 0`, `h(0) = 0`, `h(y)² = λy² + 1 − |y|` for `y ≠ 0`: then `φ(0, ·) < 1/(λε)` everywhere with supremum
  `1/(λε)`, so `sup_m ∫ D dm` is not attained); suggest adding "for continuous `h`" to the attainment clause. The
  sandwich and the maximiser equality need neither compactness nor continuity. (4) `thm:cert-chain`: `Γ_int ≤ Γ` uses
  `m̲_g ≥ m̲_0`, true for the Chernoff–Hoeffding bounds of the construction (monotone in the data, and
  `φ_{s_g} ≥ φ_{s_0}`) but not for arbitrary lower bounds; worth one clause. `certchain_int_gap` needs only `s_0 = 0`
  (the `StrictMono` hypothesis is unused there; it is used by `certchain_int_le`). (5) `cor:cs-translation` is fully
  covered (its "reweighting family (b)" gap is `thm:cs-certificate`'s); `prop:ep-gauss` is fully covered by WaveP1c and
  Wave 11a.
* Critic (2026-10-20): (a) note (3) is a genuine defect of the printed `lem:lindsay` (and of the main-text sentence
  "the supremum is attained at an extreme point of `𝓜` — a point of `K` at the free end"), now certified as
  `lindsay_attain_refuted`; the sandwich (the operational part) is unaffected. (b) Note (4) is not a defect: the
  theorem is stated for the construction preceding it (Chernoff–Hoeffding bounds at a common level for the means of
  `φ_{s_g}(π_{f̂}(U|Y))`, pointwise nondecreasing in `s`), for which `m̲_0 ≤ m̲_g`; the proof omits this one-line
  justification. (c) The `1 − 2δ` strengthening of (i) is correct and optional. (d) `certchain_dp` reduced to the three
  DP identities (the counts were tautologies about the subset lattice).

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave29d

open StatFormal.RobustEquality.Semidual (gsoft muDisc)
open StatFormal.RobustEquality.SemidualStrong (OTdisc Jdual Setting)
open StatFormal.RobustEquality.AllPairs (Dbar)
open StatFormal.Wave25a (chainSet osc sBar gBar chainGamma chainOsc)
open StatFormal.Wave15b (mOdds)
open StatFormal.Wave20a (clW clBar clD)
open StatFormal.Wave20b (confSet Predictable)
open StatFormal.Wave19b (floorW)

/-! ### `thm:loc-lower` (objects) -/

section LocLower

/-- `G₀ = sup_K g̃₀ − E_{P₀} g̃₀` for the potential `g̃₀ = g_{f*}` of `f*`. -/
def canonGap {K : Type*} [MeasurableSpace K] {k : ℕ} (ε : ℝ) (a fs : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P₀ : Measure K) : ℝ :=
  (⨆ y, gsoft ε a fs c y) - ∫ y, gsoft ε a fs c y ∂P₀

/-- The point `−R` of `K = [−R, R]`. -/
def lowPt (R : ℝ) (hR : 0 ≤ R) : Icc (-R) R := ⟨-R, by constructor <;> linarith⟩

/-- The point `R` of `K = [−R, R]`. -/
def highPt (R : ℝ) (hR : 0 ≤ R) : Icc (-R) R := ⟨R, by constructor <;> linarith⟩

/-- `P₀ = ½ δ_{−R} + ½ δ_R` on `K = [−R, R]`. -/
def twoPt (R : ℝ) (hR : 0 ≤ R) : Measure (Icc (-R) R) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (lowPt R hR) + (1 / 2 : ℝ≥0∞) • Measure.dirac (highPt R hR)

/-- The costs `c_i(y) = (x_i − y)²` of the fold `μ = ½δ_{−R} + ½δ_R` (atoms `x_0 = −R`, `x_1 = R`). -/
def cTwo (R : ℝ) (i : Fin 2) (y : Icc (-R) R) : ℝ := (![-R, R] i - (y : ℝ)) ^ 2

end LocLower

/-! ### `lem:lindsay` (objects, general mixing space) -/

section Lindsay

variable {K L : Type*} [MeasurableSpace K] [MeasurableSpace L] {n : ℕ}

/-- The likelihoods `ψ_i(y) = ∫ e^{φ(x_i, ·)} dκ(y, ·)`. -/
def psiK (κ : Kernel L K) (φ : Fin n → K → ℝ) (i : Fin n) (y : L) : ℝ :=
  ∫ x, Real.exp (φ i x) ∂(κ y)

/-- `L(m) = n⁻¹ Σ_i log ∫ ψ_i dm`. -/
def npmleK (κ : Kernel L K) (φ : Fin n → K → ℝ) (m : Measure L) : ℝ :=
  (1 / n : ℝ) * ∑ i, Real.log (∫ y, psiK κ φ i y ∂m)

/-- `Λ^𝒩_s = sup_{ν ∈ 𝒩} E_{x₀ ∼ P̂_s} log E_{x ∼ ν} e^{φ(x₀, x)}`, `𝒩 = {ν_m = ∫ κ(y, ·) m(dy) : m ∈ 𝓜}`. -/
def lambdaK (κ : Kernel L K) (φ : Fin n → K → ℝ) (M : Set (Measure L)) : ℝ :=
  sSup {v | ∃ m ∈ M, v = (1 / n : ℝ) * ∑ i, Real.log (∫ x, Real.exp (φ i x) ∂(m.bind κ))}

/-- `D_{m̂} = n⁻¹ Σ_i ψ_i / ∫ ψ_i dm̂`. -/
def lindsayDK (κ : Kernel L K) (φ : Fin n → K → ℝ) (mh : Measure L) (y : L) : ℝ :=
  (1 / n : ℝ) * ∑ i, psiK κ φ i y / ∫ y', psiK κ φ i y' ∂mh

/-- `sup_{m ∈ 𝓜} ∫ D_{m̂} dm`. -/
def lindsaySupK (κ : Kernel L K) (φ : Fin n → K → ℝ) (M : Set (Measure L)) (mh : Measure L) : ℝ :=
  sSup {v | ∃ m ∈ M, v = ∫ y, lindsayDK κ φ mh y ∂m}

/-- The standing hypotheses (`ass:mixture` without the topology): `n ≥ 1` anchors, `0 < κ(y, K) ≤ 1`, bounded
measurable exponents. -/
def MixSettingK (κ : Kernel L K) (φ : Fin n → K → ℝ) : Prop :=
  0 < n ∧ (∀ y, 0 < κ y univ ∧ κ y univ ≤ 1) ∧ (∀ i, Measurable (φ i)) ∧ ∃ B, ∀ i x, |φ i x| ≤ B

/-- Convexity of a set of mixing laws: closed under `θ m + (1 − θ) m'`, `θ ∈ [0, 1]`. -/
def MeasConvex (M : Set (Measure L)) : Prop :=
  ∀ m ∈ M, ∀ m' ∈ M, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ENNReal.ofReal θ • m + ENNReal.ofReal (1 - θ) • m' ∈ M

/-- The density-bounded class `{ν ∈ 𝒫(K) : dν/dLeb ≤ M}`, `K ⊂ ℝ^d`. -/
def densClass {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (M : ℝ) : Set (Measure (EuclideanSpace ℝ (Fin d))) :=
  {ν | IsProbabilityMeasure ν ∧ ν ≤ ENNReal.ofReal M • volume.restrict K}

/-- The exponents of a rule `h` on `K ⊆ ℝ` at anchors `x_i` (`K = A ⊆ ℝ`): `φ_i(x) = (f_h − λc)(x_i, x)/(λε)` with
`f_h(x₀, x) = (h(x) − h(x₀))²` and `c(x₀, x) = |x₀ − x|²`. -/
def phiRule {A : Set ℝ} (h : A → ℝ) (lam ε : ℝ) (x : Fin n → A) (i : Fin n) (y : A) : ℝ :=
  ((h y - h (x i)) ^ 2 - lam * ((x i : ℝ) - y) ^ 2) / (lam * ε)

end Lindsay

/-! ### `prop:tax` (b): the resolution class (objects) -/

section TaxRes

variable {d : ℕ}

/-- The resolution class `𝒩^res_β = {∫_{L_rec} N(y', β²S(y)²)|_K m(dy, dy') : m ∈ 𝒫(L_rec)}`, `L_rec = ⊔_{y ∈ Y} {y} × B(y)`:
a mixing law on the disjoint union of the closed boxes is `Σ_y w_y δ_y ⊗ m_y` with `w ∈ 𝒫(Y)` and `m_y ∈ 𝒫(B(y))`, and the
atom `(y, y')` carries the kernel `N(y', β² S(y)²) = G_{βs(y)} ∗ δ_{y'}` (`S(y) = diag(s_k(y))`). -/
def resClass (Y : Finset (Fin d → ℝ)) (s : (Fin d → ℝ) → Fin d → ℝ) (β : ℝ) (K : Set (Fin d → ℝ)) :
    Set (Measure (Fin d → ℝ)) :=
  {ν | ∃ (w : (Fin d → ℝ) → ℝ) (m : (Fin d → ℝ) → Measure (Fin d → ℝ)), (∀ y ∈ Y, 0 ≤ w y) ∧ ∑ y ∈ Y, w y = 1 ∧
    (∀ y ∈ Y, IsProbabilityMeasure (m y) ∧ m y (StatFormal.WaveP2c.boxSet y (s y))ᶜ = 0) ∧
    ν = (∑ y ∈ Y, ENNReal.ofReal (w y) •
      (StatFormal.WaveP2c.gaussProd (fun k => β * s y k) ∗ m y)).restrict K}

end TaxRes

/-! ### `thm:cert-chain` (objects) -/

section Chain

variable {r S : ℕ}

/-- `|[s_g, s_{g+1}) ∩ [0, t]| = max(0, min(s_{g+1}, t) − max(s_g, 0))`, with `s_{S+1} = ∞`. -/
def segLen (s : Fin (S + 1) → ℝ) (t : ℝ) (g : Fin (S + 1)) : ℝ :=
  max 0 (min (if h : (g : ℕ) + 1 < S + 1 then s ⟨(g : ℕ) + 1, h⟩ else t) t - max (s g) 0)

/-- `Ā(U) = Σ_g (w(U) − m̲_g(U))_+ |[s_g, s_{g+1}) ∩ [0, s̄(U)]|`. -/
def aBar (s : Fin (S + 1) → ℝ) (mlow : Fin (S + 1) → Finset (Fin r) → ℝ) (w : Fin r → ℝ) (smax : ℝ)
    (U : Finset (Fin r)) : ℝ :=
  ∑ g, max 0 (∑ i ∈ U, w i - mlow g U) * segLen s (sBar s mlow w smax U) g

/-- `Γ_int = max_𝒞 Σ_{U ∈ 𝒞} Ā(U)` over the maximal chains. -/
def chainGammaInt (s : Fin (S + 1) → ℝ) (mlow : Fin (S + 1) → Finset (Fin r) → ℝ) (w : Fin r → ℝ) (smax : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun σ : Equiv.Perm (Fin r) =>
    ∑ l ∈ Finset.Ioo 0 r, aBar s mlow w smax (chainSet σ l)

/-- The dynamic programme over the subset lattice: `V(∅) = 0`, `V(U) = T(U) + max_{i ∈ U} V(U ∖ {i})`. -/
def dpVal (T : Finset (Fin r) → ℝ) (U : Finset (Fin r)) : ℝ :=
  if h : U.Nonempty then T U + U.attach.sup' (Finset.attach_nonempty_iff.2 h) fun i => dpVal T (U.erase i.1)
  else 0
termination_by U.card
decreasing_by exact Finset.card_erase_lt_of_mem i.2

/-- The summand of `Γ` on a nonempty proper `U` (`0` on `[r]`). -/
def gammaTerm (s : Fin (S + 1) → ℝ) (mlow : Fin (S + 1) → Finset (Fin r) → ℝ) (w : Fin r → ℝ) (smax : ℝ)
    (U : Finset (Fin r)) : ℝ :=
  if U = Finset.univ then 0 else sBar s mlow w smax U * max 0 (gBar mlow w U)

/-- The summand of the oscillation certificate (`0` on `[r]`). -/
def oscTerm (s : Fin (S + 1) → ℝ) (mlow : Fin (S + 1) → Finset (Fin r) → ℝ) (w : Fin r → ℝ) (smax : ℝ)
    (U : Finset (Fin r)) : ℝ :=
  if U = Finset.univ then 0 else if 0 ≤ gBar mlow w U then sBar s mlow w smax U else 0

/-- The summand of `Γ_int` (`0` on `[r]`). -/
def intTerm (s : Fin (S + 1) → ℝ) (mlow : Fin (S + 1) → Finset (Fin r) → ℝ) (w : Fin r → ℝ) (smax : ℝ)
    (U : Finset (Fin r)) : ℝ :=
  if U = Finset.univ then 0 else aBar s mlow w smax U

end Chain

namespace Claims

/-! ### `thm:loc-lower` -/

/-- (i) Unseen mass: over `𝔓 = 𝒫(K)`, with probability at least `½ − δ` under `P₀`,
`ρ̂ − OT_ε(μ, P₀) ≥ (1 − 2^{−1/m}) G₀`, and `(1 − 2^{−1/m}) G₀ ≥ (log 2) G₀/m − (log 2)² G₀/m²`. -/
def loclower_unseen : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k m : ℕ) (ε δ : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (ρ : (Fin m → K) → ℝ) (P₀ : Measure K) [IsProbabilityMeasure P₀] (fs : Fin k → ℝ),
    Setting ε a c → 0 < m → Measurable ρ →
    (∀ P : Measure K, IsProbabilityMeasure P →
      1 - δ ≤ (Measure.pi fun _ : Fin m => P).real {y | OTdisc ε a c P ≤ (ρ y : EReal)}) →
    (∀ f, Jdual ε a c P₀ f ≤ Jdual ε a c P₀ fs) →
      1 / 2 - δ ≤ (Measure.pi fun _ : Fin m => P₀).real
          {y | OTdisc ε a c P₀ + (((1 - (2 : ℝ) ^ (-(1 : ℝ) / m)) * canonGap ε a fs c P₀ : ℝ) : EReal) ≤
            (ρ y : EReal)} ∧
        Real.log 2 * canonGap ε a fs c P₀ / m - Real.log 2 ^ 2 * canonGap ε a fs c P₀ / (m : ℝ) ^ 2 ≤
          (1 - (2 : ℝ) ^ (-(1 : ℝ) / m)) * canonGap ε a fs c P₀

/-- (ii), first assertion: for `K = [−R, R]`, `μ = P₀ = ½(δ_{−R} + δ_R)`, every maximiser `f*` of `J_{P₀}` has
`g̃₀(−R) = g̃₀(R)`, so `Var_{P₀} g̃₀(Y) = 0`. -/
def loclower_instab_var : Prop :=
  ∀ (R ε : ℝ) (hR : 0 < R) (fs : Fin 2 → ℝ), 0 < ε →
    (∀ f, Jdual ε (fun _ => 1 / 2) (cTwo R) (twoPt R hR.le) f ≤ Jdual ε (fun _ => 1 / 2) (cTwo R) (twoPt R hR.le) fs) →
      gsoft ε (fun _ => 1 / 2) fs (cTwo R) (lowPt R hR.le) = gsoft ε (fun _ => 1 / 2) fs (cTwo R) (highPt R hR.le) ∧
        variance (fun y => gsoft ε (fun _ => 1 / 2) fs (cTwo R) y) (twoPt R hR.le) = 0

/-- (ii) Instability: over `𝔓 = 𝒫([−R, R])`, for every `κ ∈ (0, m/2]`, with probability at least `1 − δ − √(κ/2)`
under `P₀`, `ρ̂ − OT_ε(μ, P₀) ≥ 2R² √(κ/m) − ε log 2`. -/
def loclower_instab : Prop :=
  ∀ (R ε δ κ : ℝ) (hR : 0 < R) (m : ℕ) (ρ : (Fin m → Icc (-R) R) → ℝ),
    0 < ε → Measurable ρ →
    (∀ P : Measure (Icc (-R) R), IsProbabilityMeasure P →
      1 - δ ≤ (Measure.pi fun _ : Fin m => P).real
        {y | OTdisc ε (fun _ => 1 / 2) (cTwo R) P ≤ (ρ y : EReal)}) →
    0 < κ → κ ≤ m / 2 →
      1 - δ - √(κ / 2) ≤ (Measure.pi fun _ : Fin m => twoPt R hR.le).real
        {y | OTdisc ε (fun _ => 1 / 2) (cTwo R) (twoPt R hR.le) +
            ((2 * R ^ 2 * √(κ / m) - ε * Real.log 2 : ℝ) : EReal) ≤ (ρ y : EReal)}

/-- (ii), last clause: the envelope `σ̃ = √(½ E D̄(X, X')²) = 2R²`, `X, X'` i.i.d. `P₀`. -/
def loclower_envelope : Prop :=
  ∀ (R : ℝ) (hR : 0 < R),
    √((1 / 2) * ∫ y, ∫ y', Dbar (cTwo R) y y' ^ 2 ∂(twoPt R hR.le) ∂(twoPt R hR.le)) = 2 * R ^ 2

/-! ### `lem:lindsay`, general mixing space -/

/-- `L(m̂) ≤ Λ^𝒩_s ≤ L(m̂) + log sup_{m ∈ 𝓜} ∫ D_{m̂} dm`, any measurable `L`, any `𝓜 ⊆ 𝒫(L)`. -/
def lindsay_gen_sandwich : Prop :=
  ∀ (K L : Type) [MeasurableSpace K] [MeasurableSpace L] (n : ℕ) (κ : Kernel L K) (φ : Fin n → K → ℝ)
    (M : Set (Measure L)) (mh : Measure L),
    MixSettingK κ φ → (∀ m ∈ M, IsProbabilityMeasure m) → mh ∈ M →
      npmleK κ φ mh ≤ lambdaK κ φ M ∧ lambdaK κ φ M ≤ npmleK κ φ mh + Real.log (lindsaySupK κ φ M mh)

/-- Equality throughout at a maximiser of `L` over a convex `𝓜`: `Λ^𝒩_s = L(m̂)` and the supremum is `1`. -/
def lindsay_gen_maximiser : Prop :=
  ∀ (K L : Type) [MeasurableSpace K] [MeasurableSpace L] (n : ℕ) (κ : Kernel L K) (φ : Fin n → K → ℝ)
    (M : Set (Measure L)) (mh : Measure L),
    MixSettingK κ φ → (∀ m ∈ M, IsProbabilityMeasure m) → MeasConvex M → mh ∈ M →
    (∀ m ∈ M, npmleK κ φ m ≤ npmleK κ φ mh) →
      lambdaK κ φ M = npmleK κ φ mh ∧ lindsaySupK κ φ M mh = 1

/-- `𝓜 = 𝒫(L)`, `L` compact metric, Feller kernel, continuous exponents: the supremum is attained at a Dirac mass,
`sup_{m ∈ 𝒫(L)} ∫ D_{m̂} dm = D_{m̂}(y) = max_L D_{m̂}` for some `y ∈ L`. -/
def lindsay_gen_dirac : Prop :=
  ∀ (K L : Type) [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
    [MetricSpace L] [CompactSpace L] [MeasurableSpace L] [BorelSpace L] [Nonempty L]
    (n : ℕ) (κ : Kernel L K) (φ : Fin n → K → ℝ) (mh : Measure L),
    MixSettingK κ φ → (∀ i, Continuous (φ i)) →
    (∀ g : K → ℝ, Continuous g → Continuous fun y => ∫ x, g x ∂(κ y)) → IsProbabilityMeasure mh →
      ∃ y : L, lindsaySupK κ φ {m | IsProbabilityMeasure m} mh = lindsayDK κ φ mh y ∧
        ∀ y', lindsayDK κ φ mh y' ≤ lindsayDK κ φ mh y

/-- The bathtub value for the density-bounded class `{ν ∈ 𝒫(K) : dν/dLeb ≤ M}` (`κ = δ`): if `D_{m̂}` has no level
set of positive measure, there is `θ` with `Leb(K ∩ {D_{m̂} > θ}) = 1/M`, and
`sup_ν ∫ D_{m̂} dν = M ∫_{K ∩ {D_{m̂} > θ}} D_{m̂} dLeb`, attained at `ν = M · Leb|_{K ∩ {D_{m̂} > θ}}`. -/
def lindsay_bathtub : Prop :=
  ∀ (d n : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (φ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (M : ℝ)
    (mh : Measure (EuclideanSpace ℝ (Fin d))),
    MixSettingK (Kernel.id) φ → IsCompact K → 0 < M → mh ∈ densClass K M →
    (∀ t : ℝ, volume (K ∩ {x | lindsayDK Kernel.id φ mh x = t}) = 0) →
      ∃ θ : ℝ, volume (K ∩ {x | θ < lindsayDK Kernel.id φ mh x}) = ENNReal.ofReal (1 / M) ∧
        IsGreatest {v | ∃ ν ∈ densClass K M, v = ∫ y, lindsayDK Kernel.id φ mh y ∂ν}
          (M * ∫ x in K ∩ {x | θ < lindsayDK Kernel.id φ mh x}, lindsayDK Kernel.id φ mh x) ∧
        ENNReal.ofReal M • volume.restrict (K ∩ {x | θ < lindsayDK Kernel.id φ mh x}) ∈ densClass K M ∧
        lindsaySupK Kernel.id φ (densClass K M) mh =
          M * ∫ x in K ∩ {x | θ < lindsayDK Kernel.id φ mh x}, lindsayDK Kernel.id φ mh x

/-- REFUTATION of the attainment clause of `lem:lindsay` ("a point `y ∈ L` when `𝓜 = 𝒫(L)` (for the free end, a point
of `K`)") for the rules of the Conventions (bounded measurable `h`): it fails for `K = L = [−1, 1]`, the free end
(`κ = δ`, `𝓜 = 𝒫(K)`), one anchor `x₀ = 0`. The negated statement quantifies over every bounded measurable `h`, every
`λ, ε > 0` and every `m̂ ∈ 𝒫(K)`; all remaining hypotheses of `ass:mixture` hold for `κ = δ` on the compact metric
`[−1, 1]`. Witness: `h(0) = 0`, `h(y) = √(y² + 1 − |y|)` otherwise, `λ = ε = 1`, `m̂ = δ₀`: then `D_{m̂} = e^{φ}`
with `φ(0) = 0`, `φ(y) = 1 − |y|` for `y ≠ 0`, whose supremum `e` is not attained. -/
def lindsay_attain_refuted : Prop :=
  ¬ ∀ (h : Icc (-1 : ℝ) 1 → ℝ) (lam ε : ℝ) (mh : Measure (Icc (-1 : ℝ) 1)),
      Measurable h → (∃ H, ∀ x, |h x| ≤ H) → 0 < lam → 0 < ε → IsProbabilityMeasure mh →
        ∃ y, lindsaySupK Kernel.id (phiRule h lam ε fun _ : Fin 1 => ⟨0, by norm_num⟩) {m | IsProbabilityMeasure m} mh =
          lindsayDK Kernel.id (phiRule h lam ε fun _ : Fin 1 => ⟨0, by norm_num⟩) mh y

/-! ### `thm:cert-chain`: `Γ_int` and the dynamic programme -/

/-- Deterministic core of the integral form: on the event that every lower confidence bound holds, for a strictly
increasing grid with `s_0 = 0`, `Gap_P(f̂) = OT_ε(μ̄_r, P) − J_P(f̂) ≤ Γ_int`. -/
def certchain_int_gap : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (r S : ℕ) (ε : ℝ) (w : Fin r → ℝ) (c : Fin r → K → ℝ) (P : Measure K)
    [IsProbabilityMeasure P] (fs fh : Fin r → ℝ) (s : Fin (S + 1) → ℝ) (mlow : Fin (S + 1) → Finset (Fin r) → ℝ)
    (bX : ℝ),
    Setting ε w c → (∀ g, Jdual ε w c P g ≤ Jdual ε w c P fs) → s 0 = 0 → StrictMono s →
    (∀ i j y, c i y - c j y ≤ bX) →
    (∀ g U, U.Nonempty → U ≠ Finset.univ → mlow g U ≤ mOdds ε (s g) w fh c P U) →
      OTdisc ε w c P - (Jdual ε w c P fh : EReal) ≤ (chainGammaInt s mlow w (bX + osc fh) : EReal)

/-- `Γ_int ≤ Γ`, for lower bounds nondecreasing along the grid (`m̲_0(U) ≤ m̲_g(U)`) and `s_max ≥ 0`. -/
def certchain_int_le : Prop :=
  ∀ (r S : ℕ) (s : Fin (S + 1) → ℝ) (mlow : Fin (S + 1) → Finset (Fin r) → ℝ) (w : Fin r → ℝ) (smax : ℝ),
    0 < r → s 0 = 0 → StrictMono s → 0 ≤ smax → (∀ g U, mlow 0 U ≤ mlow g U) →
      chainGammaInt s mlow w smax ≤ chainGamma s mlow w smax

/-- With probability at least `1 − δ`: `Gap_P(f̂) ≤ Γ_int` (lower bounds and failure probabilities as in the frozen
`chain_prob`). -/
def certchain_int_prob : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (r S : ℕ) (ε : ℝ)
    (w : Fin r → ℝ) (c : Fin r → K → ℝ) (P : Measure K) [IsProbabilityMeasure P] (fs fh : Fin r → ℝ)
    (s : Fin (S + 1) → ℝ) (mlow : Ω → Fin (S + 1) → Finset (Fin r) → ℝ) (bX δ : ℝ),
    Setting ε w c → (∀ g, Jdual ε w c P g ≤ Jdual ε w c P fs) → s 0 = 0 → StrictMono s →
    (∀ i j y, c i y - c j y ≤ bX) → 0 < δ →
    (∀ g U, U.Nonempty → U ≠ Finset.univ →
      MeasurableSet {ω | mOdds ε (s g) w fh c P U < mlow ω g U} ∧
        Pr {ω | mOdds ε (s g) w fh c P U < mlow ω g U} ≤ ENNReal.ofReal (δ / ((2 ^ r - 2) * (S + 1)))) →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ Pr E ∧ ∀ ω ∈ E,
        OTdisc ε w c P - (Jdual ε w c P fh : EReal) ≤ (chainGammaInt s (mlow ω) w (bX + osc fh) : EReal)

/-- "The same holds with `Γ` replaced by `Γ_int`": `OT_ε(μ, P) ≤ D_r + ⟨w, f̂⟩ + UCB_B + Γ_int` with probability
`≥ 1 − δ − δ'` (the setting of the frozen `chain_ot`, increasing grid). -/
def certchain_int_ot : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (d k r S m : ℕ) (φ : K → EuclideanSpace ℝ (Fin d)) (x : Fin k → EuclideanSpace ℝ (Fin d)) (a : Fin k → ℝ)
    (σ : Fin k → Fin r) (ε : ℝ) (P : Measure K) [IsProbabilityMeasure P] (fs fh : Fin r → ℝ)
    (s : Fin (S + 1) → ℝ) (mlow : Ω → Fin (S + 1) → Finset (Fin r) → ℝ) (bX δ δ' ub lb : ℝ)
    (Yb : Fin m → Ω → K) (bet : Fin m → (Fin m → K) → ℝ),
    0 < ε → (∀ i, 0 < a i) → ∑ i, a i = 1 → Function.Surjective σ → Measurable φ → (∃ R, ∀ y, ‖φ y‖ ≤ R) →
    (∀ g, Jdual ε (clW σ a) (fun z y => ‖clBar σ a x z - φ y‖ ^ 2) P g ≤
      Jdual ε (clW σ a) (fun z y => ‖clBar σ a x z - φ y‖ ^ 2) P fs) →
    s 0 = 0 → StrictMono s → (∀ z z' y, ‖clBar σ a x z - φ y‖ ^ 2 - ‖clBar σ a x z' - φ y‖ ^ 2 ≤ bX) → 0 < δ →
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
              chainGammaInt s (mlow ω) (clW σ a) (bX + osc fh) : ℝ) : EReal)

/-- "Both maxima are computed exactly by dynamic programming over the subset lattice": the recursion `dpVal`
(`V(∅) = 0`, `V(U) = T(U) + max_{i ∈ U} V(U ∖ {i})`) returns `Γ`, the oscillation certificate and `Γ_int` at `U = [r]`.
The step count `O(2^r r)` is not formalised (see Not covered). -/
def certchain_dp : Prop :=
  ∀ (r S : ℕ) (s : Fin (S + 1) → ℝ) (mlow : Fin (S + 1) → Finset (Fin r) → ℝ) (w : Fin r → ℝ) (smax : ℝ),
    0 < r →
      dpVal (gammaTerm s mlow w smax) Finset.univ = chainGamma s mlow w smax ∧
        dpVal (oscTerm s mlow w smax) Finset.univ = chainOsc s mlow w smax ∧
        dpVal (intTerm s mlow w smax) Finset.univ = chainGammaInt s mlow w smax

/-! ### `thm:ep-limit0` (i): density bounds -/

/-- For `ν = q · Leb|_K` with `q_min ≤ q ≤ q_max` on `K`, `vol(B̄(x, s) ∩ K) ≥ κ s^d` (`x ∈ K`, `0 < s ≤ s₀`), anchors in
`K` and `0 < ε ≤ s₀²`: `(d/2) ε log(1/(πε)) − ε log q_max ≤ R_ε ≤ (d/2) ε log(1/ε) + ε(1 + log(1/(q_min κ)))`. -/
def eplimit_density : Prop :=
  ∀ (d k : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (a : Fin k → ℝ) (x : Fin k → EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin d) → ℝ) (qmin qmax κ s₀ ε : ℝ),
    MeasurableSet K → (∀ i, 0 < a i) → ∑ i, a i = 1 → (∀ i, x i ∈ K) → Measurable q →
    0 < qmin → (∀ z ∈ K, qmin ≤ q z ∧ q z ≤ qmax) → 0 < κ → 0 < s₀ →
    (∀ z ∈ K, ∀ t, 0 < t → t ≤ s₀ → ENNReal.ofReal (κ * t ^ d) ≤ volume (Metric.closedBall z t ∩ K)) →
    0 < ε → ε ≤ s₀ ^ 2 →
      d / 2 * ε * Real.log (1 / (Real.pi * ε)) - ε * Real.log qmax ≤
          floorW ε a (fun i z => ‖x i - z‖ ^ 2) ((volume.restrict K).withDensity fun z => ENNReal.ofReal (q z)) ∧
        floorW ε a (fun i z => ‖x i - z‖ ^ 2) ((volume.restrict K).withDensity fun z => ENNReal.ofReal (q z)) ≤
          d / 2 * ε * Real.log (1 / ε) + ε * (1 + Real.log (1 / (qmin * κ)))

/-- (i), free class, first bound: for the centre `P̂ = n⁻¹ Σ_i δ_{x_i}` and any bounded measurable cost with
`c(x_i, x_i) = 0` (e.g. `dist²`), `R^{𝒫(K)}_ε = inf_{Q ∈ 𝒫(K)} OT_ε(P̂, Q) ≤ ε log n`, the infimum being bounded by
`OT_ε(P̂, P̂)`. -/
def eplimit_free_logn : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (ε : ℝ) (x : Fin n → K) (c : Fin n → K → ℝ),
    0 < n → 0 < ε → (∀ i, Measurable (c i)) → (∃ B, ∀ i y, |c i y| ≤ B) → (∀ i, c i (x i) = 0) →
      OTdisc ε (fun _ => 1 / (n : ℝ)) c (∑ j, ENNReal.ofReal (1 / (n : ℝ)) • Measure.dirac (x j)) ≤
          ((ε * Real.log n : ℝ) : EReal) ∧
        (⨅ Q ∈ {Q : Measure K | IsProbabilityMeasure Q}, OTdisc ε (fun _ => 1 / (n : ℝ)) c Q) ≤
          ((ε * Real.log n : ℝ) : EReal)

/-! ### `prop:tax` (b), the resolution class -/

/-- Under `H_J` (finitely many recorded boxes `B(y) ⊆ K`, recording law `Σ_y p_y δ_y`), `τ_{𝒩^res_β}(P) ≤ d ϰ(β)`. -/
def tax_res : Prop :=
  ∀ (d : ℕ) (Y : Finset (Fin d → ℝ)) (p : (Fin d → ℝ) → ℝ) (s : (Fin d → ℝ) → Fin d → ℝ) (β : ℝ)
    (K : Set (Fin d → ℝ)),
    (∀ y ∈ Y, 0 ≤ p y) → ∑ y ∈ Y, p y = 1 → (∀ y ∈ Y, ∀ k, 0 < s y k) → 0 < β → MeasurableSet K →
    (∀ y ∈ Y, StatFormal.WaveP2c.boxSet y (s y) ⊆ K) →
      StatFormal.RobustEquality.Tax.tax (resClass Y s β K) (StatFormal.WaveP2c.boxMix Y p s) ≤
        ((d * (StatFormal.Wave21a.varkappa β).toReal : ℝ) : EReal)

end Claims
end StatFormal.Wave29d
