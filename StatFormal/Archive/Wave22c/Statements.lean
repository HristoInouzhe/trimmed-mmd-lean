import StatFormal.Archive.Wave17a.Statements
import StatFormal.Archive.Wave18b.Statements
import StatFormal.Archive.Wave4b.Statements
import StatFormal.Archive.TrimmedMMD.ZeroSet.Statements
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# FROZEN STATEMENTS — wave 22c (QUEUE rows 242, 243, 260–265): NN `cor:tube-threshold`, `thm:tube-singleton`,
# `thm:comb`, `prop:refined-offset`, `thm:average-tube`, `thm:tube-dilute`; SB `prop:mixture`
# (with `eq:gaussmarg`); TM `thm:split`

Sources (verbatim in `lean-formalisation/inventory/extracted/{proliferation-nns,data-fairness-repair,trimmed-mmd}.md`;
current text after the 2026-10-13/14/15 corrections):
* NN `thm:comb` (`proliferation-and-geometry-in-nns/paper_revised.tex:715-729`), with `eq:moment` (`:709`, frozen
  `NNFibers.eq_moment`) and `lem:factmom` (`:731-745`).
* NN `prop:refined-offset` (`paper_revised.tex:1050-1064`, proof `:1066-1079`), with `eq:tube-notation`, `eq:eta-q`
  (`:983-997`), `eq:marked-pgf-asymptotic` (`:1009`) and `prop:average-offset-penalty` (`:1029-1035`).
* NN `thm:average-tube` (`paper_revised.tex:1125-1137`, proof `:1922-1930`), with `lem:codim-blockcount` (frozen
  `Wave1.codim_blockcount`) and `lem:tube-reduction` (`:1892-1920`).
* NN `cor:tube-threshold` (`paper_revised.tex:1139-1156`, proof `:1932-1942`).
* NN `thm:tube-dilute` (`paper_revised.tex:1221-1236`, proof `:1944-2034`), with `eq:kappa`, `eq:aq-ym-wm`
  (`:1198-1205`).
* NN `thm:tube-singleton` (`paper_revised.tex:1246-1268`, proof `:2036-2120`), with `eq:singleton-factorization`.
* SB `prop:mixture` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:456-470`) and `eq:gaussmarg`
  (`thm:gaussian`, `:2474-2490`).
* TM `thm:split` (`trimmed-mmd/paper.tex:1162-1176`), with `lem:separation` (frozen `Wave17a.separation`),
  `eq:splitstat` (`:1140-1151`) and `eq:tvintersect` (frozen `ZeroSet.tvintersect`).
Imports the frozen `Wave17a` (`ncChiSq`, `isoGauss`, `sepVal`; through it `NNFibers/Wave1`: `Neuron`, `LabPart`, and
`NNFibers`: `T`, `bell`), `Wave18b` (`SB.muSB`; through it `SBFairness`: `cEps`, `v`, `kappa`), `Wave4b`
(`endpointMixture1`) and `TrimmedMMD/ZeroSet` (`tvDist`, `Concentration.region`) statements, not copied; Mathlib
otherwise. No `Foundations` file is imported directly.

Covered:
* `thm:comb`: `lambertW_exists_unique` (`W(x)e^{W(x)} = x` has exactly one positive root for `x > 0`),
  `lambertW_asymp` (`W → ∞`, `W(x)/log x → 1`, `W(x) = log x − log log x + o(1)`), `comb_moment_ratio` (the exact
  identity `T(r,m)/T(k,m) = E[(K_m)_r]/E[(K_m)_k]` at every `m ≥ k`, where `T(k,m) > 0`), `comb` — CONDITIONAL on `lem:factmom` at
  `s = r, k` (hypothesis): `T(r,m)/T(k,m) ∼ (W(m)/m)^{k−r}` and `∼ (log m/m)^{k−r}`.
* `prop:refined-offset`: `refined_offset_identity` (the exact identity of the proof:
  `∏_i (e^{z_i w_m} − 1)/(e^{w_m} − 1) = (w_m/m)^{η_q} Π_q(m)`), `refined_offset_limits` (`Π_q → 1`, `Ξ_q → 1`,
  `(Ξ_q − 1) log m → −Σ_i γ_i e^{β_i}`, i.e. `Ξ_q − 1 = −Θ(1/log m)` when `Σγ_i > 0`), `refined_implies_average`
  (`eq:refined-offset` ⇒ `eq:average-exp-lambda`).
* `thm:average-tube`: `tube_U_balanced` (exact: for `d_in = d_out = d`, `U_q(m) = t^{d(m+q)/2}/Γ(d(m+q)/2+1) ·
  T(q,m) · E_U[e^{−λ_s/2}]`), `average_tube` — CONDITIONAL on `lem:tube-reduction` (first claim) and
  `prop:average-offset-penalty` (hypotheses): `eq:average-tube-asymptotic`.
* `cor:tube-threshold`: `tube_threshold` — CONDITIONAL on the same two hypotheses for `q = r, k` and on
  `lem:factmom` at `s = r, k`: `eq:H-tube-asymptotic`, `eq:Q-tube-asymptotic`, and the trichotomy.
* `thm:tube-dilute`: `dilute_saddle` (`w̃_m ∼ (1+κ) log m`, unconditional), `tube_dilute` — CONDITIONAL on
  `eq:Q-tube-dilute` (hypothesis): `log Q^tube = −Ẽ_{r,k} log m + O(log log m)` and the dichotomy.
* `thm:tube-singleton`: `singleton_count` (exactly `(m)_q` all-singleton pieces), `singleton_zeta` (`e^{−λ_s/2} = ζ_q`
  on each of them), `singleton_factorization` (`eq:singleton-factorization` with `Φ_q ≥ 1`), `tube_singleton` —
  CONDITIONAL on `lem:tube-reduction` (`eq:Qtube-is-Uratio`) and on `log Φ_r − log Φ_k → 0` (the proof's hardest
  step, as `Φ_r/Φ_k → 1`): `eq:Q-tube-singleton`, `Q^tube → ∞`, the exponent is `> 0`, and `|κ| ≥ 3/2`.
* SB `prop:mixture`: `mixture_convolution` (`eq:mixture` ⇔ `eq:convolution` for any coupling, in any finite-dimensional
  Euclidean space), `mixture_convolution_one` (`d = 1`, with the frozen `Wave4b.endpointMixture1`).
* SB `eq:gaussmarg`: `gaussPlan_marginals` (the Gaussian plan is a coupling of `N(a,σ²)` and `N(b,τ²)`),
  `gaussPlan_cov` (its cross-covariance is `c`),
  `gaussmarg_endpoint` (the endpoint mixture of the Gaussian plan with cross-covariance `c_ε` is
  `N(m_s(t), v_s(t))` = frozen `muSB`), and the PARTIAL DISCHARGES `noisefree_bridge_exact_plan`, `noisefree_limits_plan`
  (frozen Wave 18b `noisefree_bridge_exact`, `noisefree_limits` with `muSB` replaced by the endpoint mixture of the
  Gaussian entropic plan).
* TM `thm:split`: `split_null_nonpos` (under `H_{0,α}`: `TV(P,Q) ≤ α`, the population statistic
  `sep(f; 𝒞_α(P), 𝒞_α(Q)) ≤ 0` for EVERY `f`; contrapositive: a positive population statistic certifies
  `TV > α`), `split_level` — CONDITIONAL on the one-sided coverage of the lower confidence limit (hypothesis):
  asymptotic level `δ`, and rejection on the coverage event certifies `TV(P,Q) > α`.

Not covered (declared):
* `thm:comb`: `lem:factmom` itself (Harper's real-rootedness and the Moser–Wyman Bell asymptotic; hypothesis).
* `prop:refined-offset`: the expansion `eq:refined-offset` itself (marked-block saddle point and the tilted-law
  `E_z[1/N_i]` step; only the step "refined ⇒ average" and the factors are stated); the rate statement for `Π_q − 1`
  (`−Σ_i(w_m/m)^{z_i} + O(·)`, unspecified remainder; `Π_q ≡ 1` when every `z_i = 1`).
* `thm:average-tube`: `lem:tube-reduction` (the Poisson-mixture sandwich `eq:noncentral-sandwich` for `ncChiSq`) and
  `prop:average-offset-penalty` (needs `lem:marked-block-transform`); both are hypotheses.
* `thm:tube-dilute`: `eq:Q-tube-dilute` itself (Steps 1–4 of the proof: exponential tilt and saddle point).
* `thm:tube-singleton`: the bound `|log Φ_r − log Φ_k| = O(m^{1−|κ|})` (Stirling bound, MLR domination) and
  `lem:tube-reduction` (hypotheses); the remarks after the theorem.
* SB `prop:mixture`: the path-space content (the Schrödinger bridge `P*_ε` is the mixture of Brownian bridges over
  `π*_ε`; `μ^ε_t` is taken as the law in `eq:mixture`, the TRIAGE plan); the identification of `π*_ε(N(a,σ²),
  N(a⋆,τ²))` with the Gaussian plan of cross-covariance `c_ε` (only the algebraic root is frozen: `lem_gaussplan_root`).
  So `eq:gaussmarg` and the Wave 18b discharge are relative to these two identifications.
* TM `thm:split`: asymptotic normality of `T̂` and bootstrap consistency (`ass:split`); they deliver the coverage
  hypothesis of `split_level`. The empirical trimmed-mean form of `T̂` (`lem:trimmedmean`, frozen elsewhere).

Encodings (to be checked by the critic):
* Lambert `W` is any function with `IsLambertW` (`W(x) > 0`, `W(x)e^{W(x)} = x` for `x > 0`); by
  `lambertW_exists_unique` such `W` exist and agree on `(0,∞)`; `w_m = W(m)`, `a_m = m/w_m`.
* `K_m`: `P(K_m = q) = #{partitions of [m] with q blocks}/B_m` (frozen `bell`); `E[(K_m)_s] = factMoment s m`.
* A representative `θ*_q` is `θs : Fin q → Neuron d_in d_out` (frozen); `‖ω_i‖² = Σ_k ω_{ik}²`; `β_i, γ_i, z_i, η_q`
  as in `eq:tube-notation`, `eq:eta-q` (`betaW`, `gammaW`, `zW`, `etaQ`); `σ > 0` wherever used.
* Pieces are the frozen `LabPart q m` (`|LabPart| = T(q,m)`, certified); `U_{q,m}` uniform (sum / `T(q,m)`); for a
  piece `Γ = (π, ι)`: `N_i = |ι(i)|` (`copyNum`, `≥ 1`), `K = |π|` (`groupCount`), `λ_s/2 = Σ_i (β_i N_i + γ_i/N_i)`
  (`halfLam`, `eq:lambda-s`), `c_s = (m + q − K) d_in + K d_out` (`codimS`, `eq:codim-K`, no ℕ truncation since
  `K ≤ m`).
* `t = δ²/(2σ²)`; `F_{χ²_c(λ)}(2t)` is the frozen `ncChiSq c λ` evaluated on `Iic (δ²/σ²)`; `Ḡ_q(m) = Gbar`,
  `ρ(a) = t^a/Γ(a+1)` (`rhoG`, `rpow`, `t > 0`), `U_q(m) = Ubar`, `Q^tube_{r,k} = T(r,m)/T(k,m)·Ḡ_r/Ḡ_k` (`Qtube`).
  Divisions by `T(q,m)` or `Ḡ_k` are junk only for finitely many `m` (`m < q`, resp. before `Ḡ_k > 0`), which
  asymptotic statements do not see; every hypothesis/conclusion `∼` has an eventually positive right side.
* `∼` is `Asymptotics.IsEquivalent atTop` on `ℕ`; `O(log log m)` is `IsBigO atTop`; `→ ∞` is `Tendsto · atTop atTop`.
* Dilute: `κ = (d_out − d_in)/2`, `a_q = (m d_in + q d_out)/2`, `y_m = (t/a_r)^κ`, `w̃_m = W(m/y_m)`,
  `Ẽ = (2 + d_out − d_in)/2 · (Δ + η_r − η_k) − Δ d_out/2`, `d_in ≥ 1`.
* Singleton: `ζ_q = exp(−Σ_i(β_i + γ_i))`; `ρ_q(K) = rhoK` (shape `c_s/2` at group count `K`); `V_q(ℓ)` the sum of
  `e^{−λ_s/2}` over pieces with `K = m − ℓ`; `θ_q(ℓ) = ρ_q(m−ℓ)/ρ_q(m)`; `Φ_q = Σ_{ℓ ≤ m} θ_q(ℓ)V_q(ℓ)/V_q(0)`
  (`PhiS`, as printed); the paper's `a_q(m) = (q d_in + m d_out)/2` is `c_s/2` at `K = m`.
* SB: `(X₀, X₁) ∼ π` any coupling (a random vector `X : Ω → E × E` with law `π`), `Z ∼ N(0,I)` independent of it:
  `stdGaussian E` (Mathlib), resp. `gaussianReal 0 1`; `N(0, s²I) = isoGauss E s` (frozen, `s = √(εt(1−t))`);
  `ε ≥ 0`, `t ∈ [0,1]`. The Gaussian plan `gaussPlan a σ b τ c` is the law of
  `(a + σU, b + (c/σ)U + √(τ² − c²/σ²) V)`, `U, V` iid `N(0,1)` (cross-covariance `c`; a coupling when `|c| ≤ στ`).
* TM: frozen `region φ α P` (= `𝒞_{α,k}(P)`), `sepVal` (`EReal`), `tvDist`; `ℋ` complete (Bochner integrals
  genuine), `φ` strongly measurable and bounded (`ass:regularity`), `α ∈ [0,1)`; `f̂ = f` is any fixed element (the
  first fold is held fixed); the second-fold law along the sequence `n` (sizes `n₂, m₂ → ∞`) is `μ n` on a sample
  space `Ω`, `T̂_δ = Tlo n`; the coverage hypothesis is measurable events `E n` with `T̂_δ ≤ sep(f; …)` on `E n` and
  `liminf μ_n(E n) ≥ 1 − δ` (as "for every `η > 0`, eventually `≥ 1 − δ − η`"); the rejection region `{T̂_δ > 0}` is
  bounded in outer measure (no measurability needed).

Critic notes:
* All 25 claims are proved in `Wave22c/Route{Asymp,Comb,Refined,Tube,Threshold,Dilute,Singleton,Mixture,Split}.lean`
  (axioms: propext, Classical.choice, Quot.sound). Routes reuse the certified `NNFibers.eq_moment`,
  `stirlingSecond_card`, `Wave1.card_labPart`, `T_pos`, `ZeroSet.exists_common_of_tvDist_le`,
  `integral_smul_eq_withDensity` and Wave 18b `noisefree_bridge_exact`, `noisefree_limits`; the Gamma-ratio asymptotic
  `Γ(x+α)/(Γ(x)x^α) → 1` (Wendel, via Mathlib's Hölder/log-convexity inequality) is proved in `RouteAsymp`.
* CONDITIONAL claims (`comb`, `average_tube`, `tube_threshold`, `tube_dilute`, `tube_singleton`, `split_level`) take the
  paper's unproved analytic inputs as hypotheses on the frozen/defined objects; their conclusions are the printed
  displays. `tube_threshold` composes the same primitive hypotheses as `average_tube` and `comb` (not their conclusions).
* No statement was found false. Observation (`prop:refined-offset`): `Π_q − 1 = −Σ_i(w_m/m)^{z_i} + O(·)` omits the
  `+q·w_m/m` from `(1 − w_m/m)^{−q}`, which is of the same order when some `z_i = 1` (`ω_i = 0`); if every `z_i = 1`
  then `Π_q ≡ 1`. Only the limits are stated here. `thm:split`'s certification direction needs neither `‖f‖ ≤ 1` nor a
  characteristic kernel (any `f`, generalisation).
* Critic (2026-10-15): ACCEPT-WITH-NOTE, all 25 TRUE, none tautological. Conditional claims and their uncertified
  inputs: comb (`lem:factmom`); average_tube / tube_threshold (`lem:tube-reduction`, `prop:average-offset-penalty`);
  tube_dilute (its own main display `eq:Q-tube-dilute` — only the log algebra and `dilute_saddle` are certified);
  tube_singleton (`lem:tube-reduction`, `Φ_r/Φ_k → 1`); split_level (asymptotic normality, bootstrap). The noisefree
  result is a PARTIAL discharge of Wave18b: still conditional on (1) path-space `prop:mixture`, (2) `π*_ε` being the
  Gaussian plan with cross-covariance `c_ε`, (3) `π*_0` comonotone. Paper S4 (DEFECTS #73): `prop:refined-offset`'s
  display `Π_q − 1 = −Σ(w/m)^{z_i} + O(·)` fails when `q = 1` and `ω_1 = 0` (exponential activation, `a_1 ≠ 0`:
  `Π_1 ≡ 1`); the decay is like `(log m/m)^{z_i}`.
Hash-lock: frozen 2026-10-15 (author sign-off pending).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics Finset
open scoped ENNReal NNReal

namespace StatFormal.Wave22c

open StatFormal.NNFibers StatFormal.NNFibers.Wave1

/-! ### NN: Lambert function, block-count moments -/

/-- `W` is a Lambert function on `(0,∞)`: `W(x) > 0` and `W(x) e^{W(x)} = x` for every `x > 0`. -/
def IsLambertW (W : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → 0 < W x ∧ W x * Real.exp (W x) = x

/-- `#{partitions of [m] with q blocks}` (`= S(m,q)`, frozen `stirlingSecond_card`). -/
def nBlocks (m q : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin m))))).filter
    (fun P => P.parts.card = q) |>.card

/-- `E[(K_m)_s] = Σ_q (q)_s P(K_m = q)`, `P(K_m = q) = #{q blocks}/B_m` (`B_m ≥ 1`). -/
def factMoment (s m : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (m + 1), ((q.descFactorial s : ℕ) : ℝ) * ((nBlocks m q : ℝ) / (bell m : ℝ))

/-! ### NN: the tube surrogate -/

/-- `β_i = ‖ω_i‖²/(2σ²)`. -/
def betaW {din dout q : ℕ} (σ : ℝ) (θs : Fin q → Neuron din dout) (i : Fin q) : ℝ :=
  (∑ k, (θs i).1 k ^ 2) / (2 * σ ^ 2)

/-- `γ_i = ‖a_i‖²/(2σ²)`. -/
def gammaW {din dout q : ℕ} (σ : ℝ) (θs : Fin q → Neuron din dout) (i : Fin q) : ℝ :=
  (∑ k, (θs i).2 k ^ 2) / (2 * σ ^ 2)

/-- `z_i = e^{−β_i} ∈ (0,1]`. -/
def zW {din dout q : ℕ} (σ : ℝ) (θs : Fin q → Neuron din dout) (i : Fin q) : ℝ :=
  Real.exp (-betaW σ θs i)

/-- `η_q = Σ_i (1 − z_i)` (`eq:eta-q`). -/
def etaQ {din dout q : ℕ} (σ : ℝ) (θs : Fin q → Neuron din dout) : ℝ :=
  ∑ i, (1 - zW σ θs i)

/-- `Π_q(m) = ∏_i (1 − (w/m)^{z_i}) / (1 − w/m)^q`, `w = W(m)`. -/
def PiQ {din dout q : ℕ} (W : ℝ → ℝ) (σ : ℝ) (θs : Fin q → Neuron din dout) (m : ℕ) : ℝ :=
  (∏ i, (1 - (W m / m) ^ zW σ θs i)) / (1 - W m / m) ^ q

/-- `Ξ_q(m) = exp(−Σ_i γ_i/(z_i w))`, `w = W(m)`. -/
def XiQ {din dout q : ℕ} (W : ℝ → ℝ) (σ : ℝ) (θs : Fin q → Neuron din dout) (m : ℕ) : ℝ :=
  Real.exp (-∑ i, gammaW σ θs i / (zW σ θs i * W m))

/-- The copy number `N_i = |ι(i)|` of the `i`-th distinguished block of a piece. -/
def copyNum {q m : ℕ} (Γ : LabPart q m) (i : Fin q) : ℕ := ((Γ.2 i : Finset (Fin m))).card

/-- The group count `K = |π|` of a piece. -/
def groupCount {q m : ℕ} (Γ : LabPart q m) : ℕ := Γ.1.parts.card

/-- `λ_s/2 = Σ_i (β_i N_i + γ_i/N_i)` (`eq:lambda-s` with `eq:tube-notation`). -/
def halfLam {din dout q m : ℕ} (σ : ℝ) (θs : Fin q → Neuron din dout) (Γ : LabPart q m) : ℝ :=
  ∑ i, (betaW σ θs i * copyNum Γ i + gammaW σ θs i / copyNum Γ i)

/-- `E_{U_{q,m}}[e^{−λ_s/2}]`. -/
def avgOffset {din dout q : ℕ} (σ : ℝ) (θs : Fin q → Neuron din dout) (m : ℕ) : ℝ :=
  (∑ Γ : LabPart q m, Real.exp (-halfLam σ θs Γ)) / (T q m : ℝ)

/-- `c_s = (m + q − K) d_in + K d_out` (`eq:codim-K`). -/
def codimS (din dout : ℕ) {q m : ℕ} (Γ : LabPart q m) : ℕ :=
  (m + q - groupCount Γ) * din + groupCount Γ * dout

/-- `t = δ²/(2σ²)`. -/
def tubeT (δ σ : ℝ) : ℝ := δ ^ 2 / (2 * σ ^ 2)

/-- `ρ(a) = t^a / Γ(a+1)`. -/
def rhoG (t a : ℝ) : ℝ := t ^ a / Real.Gamma (a + 1)

/-- `ρ_q(K)`: `ρ` at the Gamma shape `c_s/2` of a piece with group count `K`. -/
def rhoK (din dout q m : ℕ) (δ σ : ℝ) (K : ℕ) : ℝ :=
  rhoG (tubeT δ σ) ((((m + q - K) * din + K * dout : ℕ) : ℝ) / 2)

/-- `Ḡ_q(m) = E_{U_{q,m}}[F_{χ²_{c_s}(λ_s)}(2t)]`. -/
def Gbar (din dout : ℕ) {q : ℕ} (δ σ : ℝ) (θs : Fin q → Neuron din dout) (m : ℕ) : ℝ :=
  (∑ Γ : LabPart q m,
      (StatFormal.Wave17a.ncChiSq (codimS din dout Γ) (2 * halfLam σ θs Γ)).real (Iic (δ ^ 2 / σ ^ 2))) /
    (T q m : ℝ)

/-- `U_q(m) = Σ_Γ e^{−λ_Γ/2} ρ_q(K(Γ))` (`lem:tube-reduction`). -/
def Ubar (din dout : ℕ) {q : ℕ} (δ σ : ℝ) (θs : Fin q → Neuron din dout) (m : ℕ) : ℝ :=
  ∑ Γ : LabPart q m, Real.exp (-halfLam σ θs Γ) * rhoK din dout q m δ σ (groupCount Γ)

/-- `Q^tube_{r,k}(m) = T(r,m)/T(k,m) · Ḡ_r(m)/Ḡ_k(m)`. -/
def Qtube (din dout : ℕ) {r k : ℕ} (δ σ : ℝ) (θr : Fin r → Neuron din dout) (θk : Fin k → Neuron din dout)
    (m : ℕ) : ℝ :=
  (T r m : ℝ) / (T k m : ℝ) * (Gbar din dout δ σ θr m / Gbar din dout δ σ θk m)

/-- `E_{r,k} = Δ(1 − d/2) + η_r − η_k`. -/
def Erk (d : ℕ) {r k : ℕ} (σ : ℝ) (θr : Fin r → Neuron d d) (θk : Fin k → Neuron d d) : ℝ :=
  ((k : ℝ) - r) * (1 - (d : ℝ) / 2) + etaQ σ θr - etaQ σ θk

/-- `κ = (d_out − d_in)/2` (`eq:kappa`). -/
def kappaD (din dout : ℕ) : ℝ := ((dout : ℝ) - din) / 2

/-- `a_q = (m d_in + q d_out)/2` (`eq:aq-ym-wm`). -/
def aShape (din dout q m : ℕ) : ℝ := ((m : ℝ) * din + (q : ℝ) * dout) / 2

/-- `y_m = (t/a_r)^κ`. -/
def yM (din dout r : ℕ) (δ σ : ℝ) (m : ℕ) : ℝ := (tubeT δ σ / aShape din dout r m) ^ kappaD din dout

/-- `w̃_m = W(m/y_m)`. -/
def wTilde (W : ℝ → ℝ) (din dout r : ℕ) (δ σ : ℝ) (m : ℕ) : ℝ := W ((m : ℝ) / yM din dout r δ σ m)

/-- `Ẽ_{r,k} = (2 + d_out − d_in)/2 · (Δ + η_r − η_k) − Δ d_out/2` (`eq:Etilde`). -/
def Etilde (din dout : ℕ) {r k : ℕ} (σ : ℝ) (θr : Fin r → Neuron din dout) (θk : Fin k → Neuron din dout) : ℝ :=
  (2 + (dout : ℝ) - din) / 2 * (((k : ℝ) - r) + etaQ σ θr - etaQ σ θk) - ((k : ℝ) - r) * dout / 2

/-- `ζ_q = exp(−Σ_i(β_i + γ_i))` (`eq:zeta-q`). -/
def zetaQ {din dout q : ℕ} (σ : ℝ) (θs : Fin q → Neuron din dout) : ℝ :=
  Real.exp (-∑ i, (betaW σ θs i + gammaW σ θs i))

/-- `V_q(ℓ) = Σ_{Γ : K(Γ) = m − ℓ} e^{−λ_Γ/2}`. -/
def Vq {din dout q : ℕ} (σ : ℝ) (θs : Fin q → Neuron din dout) (m ℓ : ℕ) : ℝ :=
  ∑ Γ ∈ (Finset.univ : Finset (LabPart q m)).filter (fun Γ => groupCount Γ = m - ℓ), Real.exp (-halfLam σ θs Γ)

/-- `Φ_q(m) = Σ_{ℓ ≤ m} θ_q(ℓ) V_q(ℓ)/V_q(0)`, `θ_q(ℓ) = ρ_q(m−ℓ)/ρ_q(m)` (`eq:singleton-factorization`). -/
def PhiS (din dout : ℕ) {q : ℕ} (δ σ : ℝ) (θs : Fin q → Neuron din dout) (m : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.range (m + 1),
    rhoK din dout q m δ σ (m - ℓ) / rhoK din dout q m δ σ m * (Vq σ θs m ℓ / Vq σ θs m 0)

/-! ### SB: the Gaussian plan -/

/-- The Gaussian coupling with means `(a, b)`, variances `(σ², τ²)` and cross-covariance `c`: the law of
`(a + σU, b + (c/σ)U + √(τ² − c²/σ²) V)`, `U, V` iid `N(0,1)`. -/
def gaussPlan (a σ b τ c : ℝ) : Measure (ℝ × ℝ) :=
  ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
    fun u => (a + σ * u.1, b + c / σ * u.1 + √(τ ^ 2 - (c / σ) ^ 2) * u.2)

namespace Claims

open StatFormal.Wave17a (ncChiSq isoGauss sepVal)
open StatFormal.TrimmedMMD.Concentration (region)

/-! #### NN `thm:comb` -/

/-- `W(x)e^{W(x)} = x` has exactly one positive solution for every `x > 0`. -/
def lambertW_exists_unique : Prop :=
  ∀ x : ℝ, 0 < x → ∃! w : ℝ, 0 < w ∧ w * Real.exp w = x

/-- `W(x) → ∞`, `W(x)/log x → 1` and `W(x) = log x − log log x + o(1)` as `x → ∞`. -/
def lambertW_asymp : Prop :=
  ∀ W : ℝ → ℝ, IsLambertW W →
    Tendsto W atTop atTop ∧ Tendsto (fun x => W x / Real.log x) atTop (𝓝 1) ∧
      Tendsto (fun x => W x - (Real.log x - Real.log (Real.log x))) atTop (𝓝 0)

/-- The exact identity of the proof: `T(r,m)/T(k,m) = E[(K_m)_r]/E[(K_m)_k]` for every `m ≥ k`
(both denominators positive). -/
def comb_moment_ratio : Prop :=
  ∀ r k m : ℕ, k ≤ m → (T r m : ℝ) / (T k m : ℝ) = factMoment r m / factMoment k m

/-- `thm:comb`, CONDITIONAL on `lem:factmom` at `s = r` and `s = k` (`E[(K_m)_s] ∼ (m/W(m))^s`):
`T(r,m)/T(k,m) ∼ (W(m)/m)^{k−r}` and `T(r,m)/T(k,m) ∼ (log m/m)^{k−r}`. -/
def comb : Prop :=
  ∀ (W : ℝ → ℝ) (r k : ℕ), IsLambertW W → 1 ≤ r → r < k →
    (fun m : ℕ => factMoment r m) ~[atTop] (fun m : ℕ => ((m : ℝ) / W m) ^ r) →
    (fun m : ℕ => factMoment k m) ~[atTop] (fun m : ℕ => ((m : ℝ) / W m) ^ k) →
      (fun m : ℕ => (T r m : ℝ) / (T k m : ℝ)) ~[atTop] (fun m : ℕ => (W m / m) ^ (k - r)) ∧
        (fun m : ℕ => (T r m : ℝ) / (T k m : ℝ)) ~[atTop] (fun m : ℕ => (Real.log m / m) ^ (k - r))

/-! #### NN `prop:refined-offset` -/

/-- The exact identity of the proof: with `e^{−w_m} = w_m/m`,
`∏_i (e^{z_i w_m} − 1)/(e^{w_m} − 1) = (w_m/m)^{η_q} Π_q(m)` for every `m ≥ 1`. -/
def refined_offset_identity : Prop :=
  ∀ (W : ℝ → ℝ) (din dout q : ℕ) (σ : ℝ) (θs : Fin q → Neuron din dout) (m : ℕ), IsLambertW W → 0 < σ → 1 ≤ m →
    ∏ i, (Real.exp (zW σ θs i * W m) - 1) / (Real.exp (W m) - 1) =
      (W m / m) ^ etaQ σ θs * PiQ W σ θs m

/-- Both correction factors tend to `1`, and `Ξ_q(m) − 1 = −Θ(1/log m)` with constant `Σ_i γ_i e^{β_i}`:
`(Ξ_q(m) − 1) log m → −Σ_i γ_i e^{β_i}`. -/
def refined_offset_limits : Prop :=
  ∀ (W : ℝ → ℝ) (din dout q : ℕ) (σ : ℝ) (θs : Fin q → Neuron din dout), IsLambertW W → 0 < σ →
    Tendsto (PiQ W σ θs) atTop (𝓝 1) ∧ Tendsto (XiQ W σ θs) atTop (𝓝 1) ∧
      Tendsto (fun m : ℕ => (XiQ W σ θs m - 1) * Real.log m) atTop
        (𝓝 (-∑ i, gammaW σ θs i * Real.exp (betaW σ θs i)))

/-- `eq:refined-offset` implies `eq:average-exp-lambda`. -/
def refined_implies_average : Prop :=
  ∀ (W : ℝ → ℝ) (din dout q : ℕ) (σ : ℝ) (θs : Fin q → Neuron din dout), IsLambertW W → 0 < σ →
    (fun m : ℕ => avgOffset σ θs m) ~[atTop]
        (fun m : ℕ => (W m / m) ^ etaQ σ θs * PiQ W σ θs m * XiQ W σ θs m) →
      (fun m : ℕ => avgOffset σ θs m) ~[atTop] (fun m : ℕ => (W m / m) ^ etaQ σ θs)

/-! #### NN `thm:average-tube` -/

/-- For `d_in = d_out = d` the shape is deterministic: `U_q(m) = t^{d(m+q)/2}/Γ(d(m+q)/2+1) · T(q,m) · E_U[e^{−λ_s/2}]`. -/
def tube_U_balanced : Prop :=
  ∀ (d q : ℕ) (δ σ : ℝ) (θs : Fin q → Neuron d d) (m : ℕ),
    Ubar d d δ σ θs m =
      rhoG (tubeT δ σ) ((d : ℝ) * (m + q) / 2) * (T q m : ℝ) * avgOffset σ θs m

/-- `thm:average-tube`, CONDITIONAL on `lem:tube-reduction` (first claim: `Ḡ_q ∼ e^{−t} U_q/T(q,m)`) and
`prop:average-offset-penalty` (`E_U[e^{−λ_s/2}] ∼ (w_m/m)^{η_q}`):
`Ḡ_q(m) ∼ e^{−t} t^{c_q(m)/2}/Γ(c_q(m)/2+1) · (w_m/m)^{η_q}`, `c_q(m) = d(m+q)`. -/
def average_tube : Prop :=
  ∀ (W : ℝ → ℝ) (d q : ℕ) (δ σ : ℝ) (θs : Fin q → Neuron d d), IsLambertW W → 1 ≤ d → 0 < δ → 0 < σ →
    (fun m : ℕ => Gbar d d δ σ θs m) ~[atTop]
        (fun m : ℕ => Real.exp (-tubeT δ σ) * Ubar d d δ σ θs m / (T q m : ℝ)) →
    (fun m : ℕ => avgOffset σ θs m) ~[atTop] (fun m : ℕ => (W m / m) ^ etaQ σ θs) →
      (fun m : ℕ => Gbar d d δ σ θs m) ~[atTop]
        (fun m : ℕ => Real.exp (-tubeT δ σ) * rhoG (tubeT δ σ) ((d : ℝ) * (m + q) / 2) * (W m / m) ^ etaQ σ θs)

/-! #### NN `cor:tube-threshold` -/

/-- `cor:tube-threshold`, CONDITIONAL on `lem:tube-reduction` (first claim) and `prop:average-offset-penalty` for
`q = r, k`, and on `lem:factmom` at `s = r, k`: `eq:H-tube-asymptotic`, `eq:Q-tube-asymptotic`, and the trichotomy
(`E_{r,k} > 0 ⇒ Q^tube → 0`; `E_{r,k} ≤ 0 ⇒ Q^tube → ∞`). -/
def tube_threshold : Prop :=
  ∀ (W : ℝ → ℝ) (d r k : ℕ) (δ σ : ℝ) (θr : Fin r → Neuron d d) (θk : Fin k → Neuron d d),
    IsLambertW W → 1 ≤ d → 1 ≤ r → r < k → 0 < δ → 0 < σ →
    (fun m : ℕ => Gbar d d δ σ θr m) ~[atTop]
        (fun m : ℕ => Real.exp (-tubeT δ σ) * Ubar d d δ σ θr m / (T r m : ℝ)) →
    (fun m : ℕ => Gbar d d δ σ θk m) ~[atTop]
        (fun m : ℕ => Real.exp (-tubeT δ σ) * Ubar d d δ σ θk m / (T k m : ℝ)) →
    (fun m : ℕ => avgOffset σ θr m) ~[atTop] (fun m : ℕ => (W m / m) ^ etaQ σ θr) →
    (fun m : ℕ => avgOffset σ θk m) ~[atTop] (fun m : ℕ => (W m / m) ^ etaQ σ θk) →
    (fun m : ℕ => factMoment r m) ~[atTop] (fun m : ℕ => ((m : ℝ) / W m) ^ r) →
    (fun m : ℕ => factMoment k m) ~[atTop] (fun m : ℕ => ((m : ℝ) / W m) ^ k) →
      (fun m : ℕ => Gbar d d δ σ θr m / Gbar d d δ σ θk m) ~[atTop]
          (fun m : ℕ => ((d : ℝ) * σ ^ 2 / δ ^ 2) ^ ((d : ℝ) * ((k : ℝ) - r) / 2) *
            (m : ℝ) ^ ((d : ℝ) * ((k : ℝ) - r) / 2) * (W m / m) ^ (etaQ σ θr - etaQ σ θk)) ∧
        (fun m : ℕ => Qtube d d δ σ θr θk m) ~[atTop]
          (fun m : ℕ => ((d : ℝ) * σ ^ 2 / δ ^ 2) ^ ((d : ℝ) * ((k : ℝ) - r) / 2) *
            W m ^ ((d : ℝ) * ((k : ℝ) - r) / 2) * (W m / m) ^ Erk d σ θr θk) ∧
        (0 < Erk d σ θr θk → Tendsto (fun m : ℕ => Qtube d d δ σ θr θk m) atTop (𝓝 0)) ∧
        (Erk d σ θr θk ≤ 0 → Tendsto (fun m : ℕ => Qtube d d δ σ θr θk m) atTop atTop)

/-! #### NN `thm:tube-dilute` -/

/-- The displaced saddle: for `κ > −1` (`d_in < d_out + 2`), `w̃_m ∼ (1 + κ) log m`. -/
def dilute_saddle : Prop :=
  ∀ (W : ℝ → ℝ) (din dout r : ℕ) (δ σ : ℝ), IsLambertW W → 1 ≤ din → din < dout + 2 → 0 < δ → 0 < σ →
    (fun m : ℕ => wTilde W din dout r δ σ m) ~[atTop] (fun m : ℕ => (1 + kappaD din dout) * Real.log m)

/-- `thm:tube-dilute`, CONDITIONAL on `eq:Q-tube-dilute`
(`Q^tube ∼ (a_r/t)^{Δ d_out/2} (y_m w̃_m/m)^{Δ+η_r−η_k}`): `log Q^tube = −Ẽ_{r,k} log m + O(log log m)`, hence
`Q^tube → 0` if `Ẽ > 0` and `Q^tube → ∞` if `Ẽ < 0`. -/
def tube_dilute : Prop :=
  ∀ (W : ℝ → ℝ) (din dout r k : ℕ) (δ σ : ℝ) (θr : Fin r → Neuron din dout) (θk : Fin k → Neuron din dout),
    IsLambertW W → 1 ≤ din → din < dout + 2 → r < k → 0 < δ → 0 < σ →
    (fun m : ℕ => Qtube din dout δ σ θr θk m) ~[atTop]
        (fun m : ℕ => (aShape din dout r m / tubeT δ σ) ^ (((k : ℝ) - r) * dout / 2) *
          (yM din dout r δ σ m * wTilde W din dout r δ σ m / m) ^ (((k : ℝ) - r) + etaQ σ θr - etaQ σ θk)) →
      (fun m : ℕ => Real.log (Qtube din dout δ σ θr θk m) + Etilde din dout σ θr θk * Real.log m) =O[atTop]
          (fun m : ℕ => Real.log (Real.log m)) ∧
        (0 < Etilde din dout σ θr θk → Tendsto (fun m : ℕ => Qtube din dout δ σ θr θk m) atTop (𝓝 0)) ∧
        (Etilde din dout σ θr θk < 0 → Tendsto (fun m : ℕ => Qtube din dout δ σ θr θk m) atTop atTop)

/-! #### NN `thm:tube-singleton` -/

/-- There are exactly `(m)_q` all-singleton pieces (`K = m`). -/
def singleton_count : Prop :=
  ∀ q m : ℕ, ((Finset.univ : Finset (LabPart q m)).filter (fun Γ => groupCount Γ = m)).card = m.descFactorial q

/-- On an all-singleton piece every copy number is `1` and `e^{−λ_s/2} = ζ_q`. -/
def singleton_zeta : Prop :=
  ∀ (din dout q m : ℕ) (σ : ℝ) (θs : Fin q → Neuron din dout) (Γ : LabPart q m), groupCount Γ = m →
    (∀ i, copyNum Γ i = 1) ∧ Real.exp (-halfLam σ θs Γ) = zetaQ σ θs

/-- `eq:singleton-factorization`: `U_q(m) = (m)_q ζ_q ρ_q(m) Φ_q(m)` with `Φ_q(m) ≥ 1`, for `q ≤ m`. -/
def singleton_factorization : Prop :=
  ∀ (din dout q m : ℕ) (δ σ : ℝ) (θs : Fin q → Neuron din dout), q ≤ m → 0 < δ → 0 < σ →
    Ubar din dout δ σ θs m =
        (m.descFactorial q : ℝ) * zetaQ σ θs * rhoK din dout q m δ σ m * PhiS din dout δ σ θs m ∧
      1 ≤ PhiS din dout δ σ θs m

/-- `thm:tube-singleton`, CONDITIONAL on `lem:tube-reduction` (`Q^tube ∼ U_r/U_k`, `eq:Qtube-is-Uratio`) and on the
proof's cancellation step `Φ_r/Φ_k → 1`: for `d_in > d_out + 2`, `d_out ≥ 1`,
`Q^tube ∼ (ζ_r/ζ_k)(d_out σ²/δ²)^{Δ d_in/2} m^{Δ(d_in/2−1)}`, the exponent is positive, `Q^tube → ∞`, and
`|κ| ≥ 3/2`. -/
def tube_singleton : Prop :=
  ∀ (din dout r k : ℕ) (δ σ : ℝ) (θr : Fin r → Neuron din dout) (θk : Fin k → Neuron din dout),
    dout + 2 < din → 1 ≤ dout → r < k → 0 < δ → 0 < σ →
    (fun m : ℕ => Qtube din dout δ σ θr θk m) ~[atTop]
        (fun m : ℕ => Ubar din dout δ σ θr m / Ubar din dout δ σ θk m) →
    Tendsto (fun m : ℕ => PhiS din dout δ σ θr m / PhiS din dout δ σ θk m) atTop (𝓝 1) →
      (fun m : ℕ => Qtube din dout δ σ θr θk m) ~[atTop]
          (fun m : ℕ => zetaQ σ θr / zetaQ σ θk * ((dout : ℝ) * σ ^ 2 / δ ^ 2) ^ (((k : ℝ) - r) * din / 2) *
            (m : ℝ) ^ (((k : ℝ) - r) * ((din : ℝ) / 2 - 1))) ∧
        0 < ((k : ℝ) - r) * ((din : ℝ) / 2 - 1) ∧
        Tendsto (fun m : ℕ => Qtube din dout δ σ θr θk m) atTop atTop ∧
        3 / 2 ≤ |kappaD din dout|

/-! #### SB `prop:mixture` and `eq:gaussmarg` -/

/-- `eq:mixture` ⇔ `eq:convolution` for any coupling: if `(X₀,X₁) ∼ π` and `Z ∼ N(0,I)` is independent of
`(X₀,X₁)`, the law of `(1−t)X₀ + tX₁ + √(εt(1−t)) Z` is `ρ_t ∗ N(0, εt(1−t) I)`, `ρ_t` the law of `(1−t)X₀ + tX₁`. -/
def mixture_convolution : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → E × E) (Z : Ω → E) (ε t : ℝ),
    Measurable X → Measurable Z → IndepFun X Z P → P.map Z = stdGaussian E → 0 ≤ ε → t ∈ Icc (0 : ℝ) 1 →
      P.map (fun ω => (1 - t) • (X ω).1 + t • (X ω).2 + √(ε * t * (1 - t)) • Z ω) =
        ((P.map X).map fun p => (1 - t) • p.1 + t • p.2) ∗ isoGauss E (√(ε * t * (1 - t)))

/-- `d = 1`: the law in `eq:mixture` is the frozen `endpointMixture1 ε t π` (`eq:convolution`, Mathlib's
`N(0, εt(1−t))`), `π` the law of `(X₀, X₁)`. -/
def mixture_convolution_one : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ × ℝ) (Z : Ω → ℝ) (ε t : ℝ),
    Measurable X → Measurable Z → IndepFun X Z P → P.map Z = gaussianReal 0 1 → 0 ≤ ε → t ∈ Icc (0 : ℝ) 1 →
      P.map (fun ω => (1 - t) * (X ω).1 + t * (X ω).2 + √(ε * t * (1 - t)) * Z ω) =
        StatFormal.Wave4b.endpointMixture1 ε t (P.map X)

/-- The Gaussian plan is a coupling of `N(a, σ²)` and `N(b, τ²)` when `|c| ≤ στ`. -/
def gaussPlan_marginals : Prop :=
  ∀ a σ b τ c : ℝ, 0 < σ → 0 < τ → |c| ≤ σ * τ →
    (gaussPlan a σ b τ c).map Prod.fst = gaussianReal a (σ ^ 2).toNNReal ∧
      (gaussPlan a σ b τ c).map Prod.snd = gaussianReal b (τ ^ 2).toNNReal

/-- The Gaussian plan has cross-covariance `c`: `∫ (x − a)(y − b) d(gaussPlan a σ b τ c) = c`. -/
def gaussPlan_cov : Prop :=
  ∀ a σ b τ c : ℝ, 0 < σ → 0 < τ → |c| ≤ σ * τ →
    ∫ p, (p.1 - a) * (p.2 - b) ∂(gaussPlan a σ b τ c) = c

/-- `eq:gaussmarg` from the endpoint mixture: for the Gaussian plan with cross-covariance `c_ε(σ,τ)` between
`N(a,σ²)` and `N(a⋆,τ²)`, `ρ_t ∗ N(0,εt(1−t)) = N((1−t)a + ta⋆, v(t))` (the frozen `muSB`), every `ε ≥ 0`,
`t ∈ [0,1]`. -/
def gaussmarg_endpoint : Prop :=
  ∀ ε σ τ a astar t : ℝ, 0 ≤ ε → 0 < σ → 0 < τ → t ∈ Icc (0 : ℝ) 1 →
    |StatFormal.SBFairness.cEps ε σ τ| ≤ σ * τ ∧
      StatFormal.Wave4b.endpointMixture1 ε t (gaussPlan a σ astar τ (StatFormal.SBFairness.cEps ε σ τ)) =
        StatFormal.Wave18b.muSB ε σ τ a astar t

/-- PARTIAL DISCHARGE (relative to path-space `prop:mixture`, `π*_ε` Gaussian, `π*_0` comonotone) of Wave 18b's `eq:gaussmarg` hypothesis in `noisefree_bridge_exact`: the same exact formula with
`μ^ε_{s,t}` the endpoint mixture of the Gaussian entropic plan (cross-covariance `c_ε`, resp. `c_0 = στ`). -/
def noisefree_bridge_exact_plan : Prop :=
  ∀ ε σ τ a astar t : ℝ, 0 < ε → 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    TauCeti.wassersteinEDist 2
        (StatFormal.Wave4b.endpointMixture1 ε t (gaussPlan a σ astar τ (StatFormal.SBFairness.cEps ε σ τ)))
        (StatFormal.Wave4b.endpointMixture1 0 t (gaussPlan a σ astar τ (StatFormal.SBFairness.cEps 0 σ τ))) =
      ENNReal.ofReal (t * (1 - t) * (StatFormal.SBFairness.kappa ε σ τ - 2 * σ * τ) /
        (√(StatFormal.SBFairness.v ε σ τ t) + √(StatFormal.SBFairness.v 0 σ τ t)))

/-- PARTIAL DISCHARGE (relative to path-space `prop:mixture`, `π*_ε` Gaussian, `π*_0` comonotone) of Wave 18b's `eq:gaussmarg` hypothesis in `noisefree_limits` (first limit): with the endpoint
mixtures of the Gaussian entropic plans, `W₂(μ^ε_{s,t}, μ^0_{s,t})/σ⁴ → 1/(8σ_sτ g t(1−t))`, `σ² = εt(1−t)`. -/
def noisefree_limits_plan : Prop :=
  ∀ σ τ a astar t : ℝ, 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    Tendsto (fun ε => (TauCeti.wassersteinEDist 2
        (StatFormal.Wave4b.endpointMixture1 ε t (gaussPlan a σ astar τ (StatFormal.SBFairness.cEps ε σ τ)))
        (StatFormal.Wave4b.endpointMixture1 0 t (gaussPlan a σ astar τ (StatFormal.SBFairness.cEps 0 σ τ)))).toReal /
          (ε * t * (1 - t)) ^ 2) (𝓝[>] 0)
      (𝓝 (1 / (8 * σ * τ * StatFormal.SBFairness.geo σ τ t * (t * (1 - t)))))

/-! #### TM `thm:split` -/

/-- The certification direction of `thm:split`: under `H_{0,α}` (`TV(P,Q) ≤ α`), the population split statistic
`sep(f; 𝒞_α(P), 𝒞_α(Q)) = inf_{a ∈ 𝒞_α(P)}⟨f,a⟩ − sup_{b ∈ 𝒞_α(Q)}⟨f,b⟩` is `≤ 0` for every `f`. -/
def split_null_nonpos : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      StatFormal.Distances.tvDist P Q ≤ α → ∀ f : H, sepVal f (region φ α P) (region φ α Q) ≤ 0

/-- `thm:split`, CONDITIONAL on one-sided asymptotic coverage of the lower limit `T̂_δ` of the population
statistic (what asymptotic normality and the bootstrap deliver): the rule "reject if `T̂_δ > 0`" has asymptotic
level `δ` under `H_{0,α}`, and on the coverage event rejection certifies `TV(P,Q) > α`. -/
def split_level : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α δ : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : ℕ → Measure Ω) (Tlo : ℕ → Ω → ℝ) (E : ℕ → Set Ω),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → (∀ n, IsProbabilityMeasure (μ n)) →
    (∀ n, MeasurableSet (E n)) →
    (∀ n, ∀ ω ∈ E n, ((Tlo n ω : ℝ) : EReal) ≤ sepVal f (region φ α P) (region φ α Q)) →
    (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ (μ n).real (E n)) →
      (StatFormal.Distances.tvDist P Q ≤ α →
          ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, μ n {ω | 0 < Tlo n ω} ≤ ENNReal.ofReal (δ + η)) ∧
        (∀ n, ∀ ω ∈ E n, 0 < Tlo n ω → α < StatFormal.Distances.tvDist P Q)

end Claims

end StatFormal.Wave22c
