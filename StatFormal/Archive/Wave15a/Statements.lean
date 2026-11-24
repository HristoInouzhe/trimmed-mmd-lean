import StatFormal.Archive.RobustEquality.SemidualStrong.Statements
import StatFormal.Archive.TrimmedMMD.ZeroSet.Statements
import StatFormal.Archive.TrimmedMMD.BangBang.Statements
import StatFormal.Archive.NNFibers.Wave1.Statements
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.Filter.Basic

/-!
# FROZEN STATEMENTS — wave 15a (QUEUE rows 135–142): robust equality JASA `prop:ad-identity`, `prop:ep-mcgap`;
# TM `prop:upper`, `cor:marginderived`, `lem:nullbound`, `lem:qpstability`; ICL `prop:diag-identity`;
# NN `lem:min-reduced` (already certified as `NNFibers.Wave1.Claims.min_reduced`; extended, not duplicated)

Sources (verbatim in `lean-formalisation/inventory/extracted/robust-equality-jasa.md`, `trimmed-mmd.md`,
`context-distribution-icl.md`, `proliferation-nns.md`; current text after the 2026-10-13/14 corrections):
* robust equality `prop:ad-identity` (`robust-equality-outcomes-under-distribution-shift/jasa/supp_calibration.tex:275-280`,
  proof `:282-285`), with `def:ad-moduli` (`:217-224`: `Λ_P(φ;r)`, `ω_P(r)`, `ω^far_P(η)`), `Gap_Q(f) := Θ(Q) − J_Q(f)`
  (`supp_proofs.tex:43`) and the canonical potential `g̃ = g_{f*}` (`supp_proofs.tex:66-71`, `lem:semidual`(i)).
* robust equality `prop:ep-mcgap` (`jasa/supp_eps.tex:359-369`, proof `:371-374`), with the estimator `T̂⁺` of the frozen
  `prop:mc` (`RobustEquality/Statements.lean`, `jasa/main.tex:556`).
* TM `prop:upper` (`trimmed-mmd/paper.tex:1206-1215`, proof `supplement.tex:435-441`), with `ass:margin`
  (`paper.tex:1006-1011`) and `α* = TV(P,Q)` (`paper.tex:105`).
* TM `cor:marginderived` (`paper.tex:1328-1343`, proof `supplement.tex:521-530`), with `thm:interp` (`paper.tex:1314-1322`),
  `ass:smooth` (`:1298-1303`) and the caveat in the paragraph after it (`:1354-1359`).
* TM `lem:nullbound` (`paper.tex:739-749`, proof `supplement.tex:147-160`).
* TM `lem:qpstability` (`supplement.tex:1129-1135`, proof `:1136-1143`), with `eq:qp` (`paper.tex:605-616`).
* ICL `prop:diag-identity` (`context-distribution-ICL/paper/v3/supp/alternatives.tex:51-56`, proof `:58-61`), with
  `F_cov(μ) = E_{Q_μ}[G_μ(Z)]`, `dQ_μ/dP₀ ∝ ρ_μ⁻¹` (`:11-15`).
* NN `lem:min-reduced` (`proliferation-and-geometry-in-nns/paper_revised.tex:506-518`) and the remark on
  "functionally minimal" vs "structurally reduced" (`:361-366`: "For some activations these notions coincide …, but not
  in general").
Reuses the frozen `RobustEquality` (`That`), `RobustEquality/Semidual{,Strong}` (`gsoft`, `OTdisc`, `Jdual`, `Setting`),
`TrimmedMMD/{Concentration,Unconditional,ZeroSet,BangBang}` (`region`, `empirical`, `Dpop`, `Demp`, `IsTrimDensity`,
`capped`) and `NNFibers/Wave1` (`Neuron`, `net`, `FunctionallyMinimal`) statements, imported, not copied. No
`Foundations` library file is imported directly (`StatFormal.Distances.tvDist` comes in through the frozen
`ZeroSet`/`SemidualStrong` statements).

Covered:
* `prop:ad-identity`: `ad_identity` (`Θ(P₁) − Θ(P) = sup_f {(P₁ − P)g_f − Gap_P(f)}`, both values finite, as an `IsLUB`);
  `ad_identity_omega` (`ω_P(r) = sup_f {Λ_P(g_f; r) − Gap_P(f)}`, `r ≥ 0`); `ad_identity_far` (`ω^far_P(η) =
  sup_f {η(sup_K g_f − P g_f) − Gap_P(f)}` and `≥ η G₀`, `η ∈ [0,1]`, for every maximiser `f*`, so for the canonical one).
* `prop:ep-mcgap`: `ep_mcgap` (probability reference, almost surely, simultaneously over `λ ∈ Λ`); `ep_mcgap_sure`
  (every realisation, when the envelope dominates on all of `K`); `ep_mcgap_subprob` (`0 < ν(K) ≤ 1`, draws from
  `ν/ν(K)`, mean multiplied by `ν(K)`, the frozen `prop_mc_subprob` estimator).
* `prop:upper`: `prop_upper`; `omegaInv_spec` (the encoding `omegaInv` is the paper's inverse with its boundary extension).
* `cor:marginderived`: `marginderived` (the display, for each `α`), `marginderived_power` (the power-form margin
  condition `ω(ε) = c₀ ε^{1/θ}`).
* `lem:nullbound`: `nullbound`.
* `lem:qpstability`: `qpstability`; `qp_value_exists` (the value of `eq:qp` is a genuine minimum).
* `prop:diag-identity`: `diag_identity_formula`, `diag_identity`.
* `lem:min-reduced` (extension): `exp_minimal_iff_reduced` (for `σ = exp` the two notions coincide);
  `tanh_reduced_not_minimal` ("but not in general": a reduced `tanh` parameter that is not minimal).

Not covered (declared):
* `prop:ad-identity`: nothing of the proposition; the interpretation paragraph after it (`:287-290`) is a remark.
* `prop:ep-mcgap`: the Status paragraph (`:376-383`: "can beat … by at most …", the computational remarks (a)–(c)).
* `cor:marginderived`: `thm:interp` itself ("known", Sobolev interpolation; not in Mathlib) — it enters as a hypothesis
  (`InterpBound`, its conclusion for the optimal pair), so `ass:smooth` and `θ = t/(s+t)` are not encoded; the
  existence of the optimal pair (`lem:attainment`) is likewise a hypothesis; "`γ = (s+t)/t` always exceeds 1".
* `lem:qpstability`: its use in `thm:rffjoint` (`:1145-1157`).
* `lem:min-reduced`: the lemma itself is the certified `NNFibers.Wave1.Claims.min_reduced` (not re-stated).

Encodings (to be checked by the critic):
* `prop:ad-identity`: `Θ(Q) = OT_ε(μ, Q)` is the frozen `OTdisc` (an `EReal` infimum over couplings), `J_Q` the frozen
  `Jdual`, `g_f` the frozen `gsoft`; the setting is the frozen `Setting` (any measurable `K`, bounded measurable `c_i`;
  the paper's compact `K`, continuous `c` is a case). `Gap_P(f) = t − J_P(f)` with `t` the (proved finite) value
  `Θ(P)`. `Λ_P`, `ω_P`, `ω^far_P` are `EReal` suprema (`lamMod`, `omegaMod`, `omegaFar`) over probability measures `P₁`
  with Mathlib's `klDiv P P₁ ≤ ofReal r` (for probability measures this is the paper's `KL(P‖P₁)`), resp. over `z ∈ K`
  with `(1−η)P + ηδ_z` built with `ENNReal.ofReal` weights (`mixDirac`); `sup_K g_f` is unfolded as an inner `⨆ z`,
  legitimate since `η ≥ 0`. No `⊤ − ⊤`: only finite reals are subtracted in `EReal`.
* `prop:ep-mcgap`: `φ_λ(x_i, ·) = f_h(x_i,·) − λc(x_i,·)` is an arbitrary function `φ λ i : K → ℝ`, `U^{(i)} =
  e^{φ_λ(x_i,·)/(λε)}`, `R_i = e^{e_λ(x_i)/(λε)}`; "`e_λ ≥ sup_{S_ν}[…]`" is encoded as `φ_λ ≤ e_λ` `ν`-a.e. (what the proof
  uses; `S_ν` has full `ν`-measure). `T̂⁺` is the frozen `That` with `r = R_ε + β`, `L = n|Λ|`; `T^env_0(λ) = λ(R₀+β) +
  n⁻¹ Σ_i e_λ(x_i)` (`tEnv`, anchors `x_1, …, x_n`, `P̂` their empirical law); `t = tCorr`. `R_ε`, `R₀`, `β` are arbitrary
  reals (only their appearance matters). The draws `X_{ij}` are measurable with law `ν`; no independence is needed.
* `prop:upper`: `MarginCond` is `ass:margin` at `α* = TV(P,Q)` (`tvDist`), with the `ε = 0` instance dropped (it reads
  `D ≥ 0`, automatic, and would evaluate `D` at `α = 1` when `TV = 1`). `ω⁻¹` with the boundary extension is `omegaInv
  ω α* u = sup{ε ∈ [0, α*] : ω(ε) ≤ u}` (the set contains `0` for `u ≥ 0`, so no `sSup ∅` junk where it is used,
  `Ď ≥ D ≥ 0`); `omegaInv_spec` proves it is the paper's inverse. Regularity: `φ` strongly measurable and bounded
  (`ass:regularity`; characteristicness is not needed). `D_{α,k}` is the frozen `Dpop` (`sInf` over nonempty regions).
* `cor:marginderived`: an optimal trimmed pair is a pair of trimming densities (`IsTrimDensity`, `P* = g_P·P`) whose
  MMD (`trimMMD`) equals `D_{α,k}(P,Q)`; "`ass:smooth` holds for it with `L'`" is replaced by the conclusion of
  `thm:interp` for that pair (`InterpBound`, constants `|𝒳| = V`, `A_k = A`, `L'`, `θ`, all `> 0`; `θ ∈ (0,1)` is not
  needed). `0 ≤ α ≤ TV(P,Q)`, `α < 1` (at `α = TV = 1` the display is `0/0`). The power form takes the hypothesis for
  every such `α` with the same constants and concludes `MarginCond` with `ω(ε) = c₀ ε^{1/θ}` (`marginC0`, `rpow`).
* `lem:nullbound`: "surely" is "for every sample `x : Fin n → 𝒳`, `y : Fin m → 𝒳`"; `P_n` is the frozen `empirical`,
  `D̂ = Demp`, `d_H` is Mathlib's `Metric.hausdorffDist` (finite here: the regions are nonempty and bounded, so the
  `⊤ ↦ 0` junk of `hausdorffDist` never applies — and it could only make the claim harder).
* `lem:qpstability`: the Gram triples are arbitrary real matrices (PSD not needed), the caps may differ on the two
  sides (`α`, `β`; the paper's `eq:qp` has `α = β`), `‖·‖_max ≤ ε` is entrywise; "the values" are `IsLeast` of
  `qpVals` over the frozen capped simplices, and `qp_value_exists` shows they exist (`n, m ≥ 1`, `α, β ∈ [0,1)`).
* `prop:diag-identity`: the sample is `Fin n`, `P₀` uniform, `ρ_w(z_i) = Σ_j K(z_i,z_j) w_j` (`covW`), `F_cov` as the
  self-normalised average (`fcov`); `G_i(w) = G i w` arbitrary. The limit is along any filter `l` on any index type,
  with `w > 0` (needed for `ρ⁻¹`; the simplex constraint is not needed), the other coordinates eventually `≥ c > 0`, and
  `|G_i| ≤ B` (the hypothesis the proof uses, "because the `G_i` are bounded").
* NN: `Reduced θ` (pairwise distinct incoming weights, nonzero outgoing weights) is the paper's "structurally reduced";
  "functionally minimal" is the frozen `FunctionallyMinimal`.

Critic notes:
* `prop:ad-identity` holds as printed (given `lem:semidual`(i), the frozen, certified strong duality); `ω^far ≥ ηG₀`
  holds for every maximiser `f*`, not only the canonical one (all maximisers have the same `J_P`).
* `prop:ep-mcgap`: "for every realisation of the draws" is false literally (QUEUE note): the bound `e_λ ≥ sup_{S_ν}`
  controls `U` only on `S_ν`; a draw outside `S_ν` (a null event) can have `Ū > R` and break the upper bound (e.g.
  `ν = δ₀`, `φ(x) = x`, `e = 0`, a realisation `X = 1`). It holds almost surely (`ep_mcgap`), and surely when the
  envelope dominates on all of `K` (`ep_mcgap_sure`). Suggested fix: "almost surely" (or `e_λ ≥ sup_K`). The proof
  silently uses `Ū ≥ 0` (true: `U > 0`).
* `prop:upper` holds as printed; with the `sup`-form of `ω⁻¹` neither continuity nor strict monotonicity of `ω` is
  used (they serve only to identify `omegaInv` with the inverse).
* `cor:marginderived` holds as printed, conditionally on `thm:interp` for the optimal pair. Caveat (T4-9, the paper's
  own caveat paragraph): optimal trimmings have bang-bang densities (`lem:trimmedmean`), so `p* − q*` is typically
  discontinuous and `p* − q* ∈ H^t` uniformly in `α` forces `t < 1/2`; the hypothesis is rarely verifiable.
* `lem:nullbound`, `lem:qpstability`, `prop:diag-identity` hold as printed (the last needs the `G_i` bounded, which the
  proof uses but the statement leaves implicit; suggested fix: "if the `G_i` are bounded and …").
* NN: `lem:min-reduced` is certified; its converse holds for `exp` (via the coefficient identity behind the frozen
  `prop:exp-ident`, `Wave12c`) and fails for `tanh` (`tanh(x) + tanh(−x) = 0`), matching the paper's remark.
* Proof routes: `Wave15a/Route{AdIdentity,McGap,TM,Small}.lean`, all 17 claims (`Wave15a/Proofs.lean` checks each
  against its claim). The routes reuse the untrusted `RobustEquality/SemidualStrong/Proofs`, `TrimmedMMD/{ZeroSet,
  Unconditional}/Proofs`, `Wave4b/Proofs` (`prop:deletionfloor`) and `Wave12c/RouteExpIdent` — routes only.

* Critic (2026-10-14): ACCEPT / ACCEPT-WITH-NOTE, all TRUE. ad-identity: the EReal moduli are never empty (`P₁ = P`
  admissible), so no `⊥`. ep-mcgap: the "every realisation" counterexample needs a draw outside `S_ν` (a null set);
  the bound holds for every realisation in `S_ν` — paper S4 wording ("every realisation of the draws in `S_ν`, hence
  a.s.", DEFECTS #56); `ep_mcgap_sure` needs no measure (taking `K := S_ν` gives the in-support reading). TM:
  `InterpBound` is exactly `thm:interp`'s conclusion for `(g_P·P, g_Q·Q)` (implied by the paper's hypothesis);
  `marginderived` is conditional on it. ICL diag-identity: the statement omits "`G_i` bounded" (S3: `n = 2`, `G₁ ≡ 0`,
  `G₂(w) = 1/w₁`, `w = (s, 1−s)` gives `F_cov − G₁ ≡ 1`), and the formula holds with `w` the one-slot marginal (S4:
  for `M ≥ 2` it differs, e.g. `w = (½,¼,¼)`, `M = 2` gives `2/5`) — DEFECTS #57. NN: the tanh pair uses the sign
  symmetry, so it does not show "not even after quotienting" (a one-unit witness `ω = 0`, `a = 1` would).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InformationTheory Topology
open scoped ENNReal

namespace StatFormal.Wave15a

open StatFormal.RobustEquality.Semidual StatFormal.RobustEquality.SemidualStrong

/-! ### REO `prop:ad-identity` -/

section AdIdentity

variable {K : Type*} [MeasurableSpace K]

/-- `Λ_P(φ; r) = sup{(P₁ − P)φ : P₁ ∈ 𝒫(K), KL(P‖P₁) ≤ r}` (in `EReal`, no `sSup` junk). -/
def lamMod (P : Measure K) (φ : K → ℝ) (r : ℝ) : EReal :=
  ⨆ (P₁ : Measure K) (_ : IsProbabilityMeasure P₁) (_ : klDiv P P₁ ≤ ENNReal.ofReal r),
    ((∫ y, φ y ∂P₁ - ∫ y, φ y ∂P : ℝ) : EReal)

/-- `ω_P(r) = sup{Θ(P₁) − Θ(P) : P₁ ∈ 𝒫(K), KL(P‖P₁) ≤ r}`, `Θ = OT_ε(μ, ·)` (in `EReal`). -/
def omegaMod {k : ℕ} (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (P : Measure K) (r : ℝ) : EReal :=
  ⨆ (P₁ : Measure K) (_ : IsProbabilityMeasure P₁) (_ : klDiv P P₁ ≤ ENNReal.ofReal r),
    (OTdisc ε a c P₁ - OTdisc ε a c P)

/-- The contaminated law `(1 − η)P + ηδ_z`. -/
def mixDirac (P : Measure K) (η : ℝ) (z : K) : Measure K :=
  ENNReal.ofReal (1 - η) • P + ENNReal.ofReal η • Measure.dirac z

/-- `ω^far_P(η) = sup_{z ∈ K} {Θ((1 − η)P + ηδ_z) − Θ(P)}` (in `EReal`). -/
def omegaFar {k : ℕ} (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (P : Measure K) (η : ℝ) : EReal :=
  ⨆ z : K, (OTdisc ε a c (mixDirac P η z) - OTdisc ε a c P)

end AdIdentity

/-! ### REO `prop:ep-mcgap` -/

/-- The certified `ε = 0` value `T^env_0(λ) = λ(R₀ + β) + E_{P̂} e_λ` (anchors `x_1, …, x_n`). -/
def tEnv {n : ℕ} (lam R0 β : ℝ) (e : Fin n → ℝ) : ℝ :=
  lam * (R0 + β) + (1 / (n : ℝ)) * ∑ i, e i

/-- The Monte-Carlo correction `t = √(log(n|Λ|/α_MC)/(2m))`. -/
def tCorr (n m L : ℕ) (α : ℝ) : ℝ :=
  √(Real.log ((n : ℝ) * L / α) / (2 * m))

/-! ### TM `prop:upper`, `cor:marginderived` -/

section Margin

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `ω⁻¹(u)` with the boundary extension `ω⁻¹(u) = α*` for `u ≥ ω(α*)`:
`sup{ε ∈ [0, α*] : ω(ε) ≤ u}` (nonempty for `u ≥ 0 = ω(0)`, bounded by `α*`). -/
def omegaInv (ω : ℝ → ℝ) (αs u : ℝ) : ℝ :=
  sSup {e | e ∈ Icc 0 αs ∧ ω e ≤ u}

/-- `ass:margin` at `α* = TV(P,Q)`: `ω : [0, α*] → [0, ∞)` strictly increasing, continuous, `ω(0) = 0`,
and `D_{α*−ε,k}(P,Q) ≥ ω(ε)` for `ε ∈ (0, α*]` (at `ε = 0` the condition reads `D ≥ 0`). -/
def MarginCond (φ : 𝒳 → H) (P Q : Measure 𝒳) (ω : ℝ → ℝ) : Prop :=
  StrictMonoOn ω (Icc 0 (StatFormal.Distances.tvDist P Q)) ∧
  ContinuousOn ω (Icc 0 (StatFormal.Distances.tvDist P Q)) ∧ ω 0 = 0 ∧
  (∀ e ∈ Icc 0 (StatFormal.Distances.tvDist P Q), 0 ≤ ω e) ∧
  ∀ e ∈ Ioc 0 (StatFormal.Distances.tvDist P Q),
    ω e ≤ StatFormal.TrimmedMMD.Unconditional.Dpop φ P Q (StatFormal.Distances.tvDist P Q - e)

/-- `MMD_k(P*, Q*) = ‖μ_{P*} − μ_{Q*}‖` for the trimmings `P* = g_P·P`, `Q* = g_Q·Q`. -/
def trimMMD (φ : 𝒳 → H) (P Q : Measure 𝒳) (gP gQ : 𝒳 → ℝ) : ℝ :=
  ‖∫ x, gP x • φ x ∂P - ∫ x, gQ x • φ x ∂Q‖

/-- The conclusion of `thm:interp` for the pair `(g_P·P, g_Q·Q)`:
`TV(P*, Q*) ≤ ½ |𝒳|^{1/2} A_k^θ L'^{1−θ} MMD_k(P*, Q*)^θ`. -/
def InterpBound (φ : 𝒳 → H) (P Q : Measure 𝒳) (gP gQ : 𝒳 → ℝ) (V A L θ : ℝ) : Prop :=
  StatFormal.Distances.tvDist (P.withDensity fun x => ENNReal.ofReal (gP x))
      (Q.withDensity fun x => ENNReal.ofReal (gQ x)) ≤
    1 / 2 * √V * A ^ θ * L ^ (1 - θ) * trimMMD φ P Q gP gQ ^ θ

/-- The right-hand side of `cor:marginderived`. -/
def marginLB (tv α V A L θ : ℝ) : ℝ :=
  1 / A * (2 * (tv - α) / (√V * (1 - α) * L ^ (1 - θ))) ^ (1 / θ)

/-- `c₀ = A_k⁻¹ (2/(|𝒳|^{1/2} L'^{1−θ}))^{1/θ}`. -/
def marginC0 (V A L θ : ℝ) : ℝ :=
  1 / A * (2 / (√V * L ^ (1 - θ))) ^ (1 / θ)

end Margin

/-! ### TM `lem:qpstability` -/

/-- Objective of `eq:qp` in Gram form: `wᵀK_XX w + vᵀK_YY v − 2 wᵀK_XY v`. -/
def qpGram {n m : ℕ} (Kxx : Fin n → Fin n → ℝ) (Kyy : Fin m → Fin m → ℝ) (Kxy : Fin n → Fin m → ℝ)
    (w : Fin n → ℝ) (v : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, w i * w j * Kxx i j + ∑ i, ∑ j, v i * v j * Kyy i j - 2 * ∑ i, ∑ j, w i * v j * Kxy i j

/-- Values of `eq:qp` over `Δ_α(n) × Δ_β(m)`. -/
def qpVals {n m : ℕ} (Kxx : Fin n → Fin n → ℝ) (Kyy : Fin m → Fin m → ℝ) (Kxy : Fin n → Fin m → ℝ)
    (α β : ℝ) : Set ℝ :=
  {s | ∃ w ∈ StatFormal.TrimmedMMD.BangBang.capped n α, ∃ v ∈ StatFormal.TrimmedMMD.BangBang.capped m β,
    s = qpGram Kxx Kyy Kxy w v}

/-! ### ICL `prop:diag-identity` -/

/-- Coverage of the sample point `z_i` by the one-slot marginal `w`: `ρ_w(z_i) = Σ_j K(z_i, z_j) w_j`. -/
def covW {n : ℕ} (Kk : Fin n → Fin n → ℝ) (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, Kk i j * w j

/-- `F_cov(w) = E_{Q_w}[G_w(Z)]`, `dQ_w/dP₀ ∝ ρ_w⁻¹`, `P₀` uniform on the sample. -/
def fcov {n : ℕ} (Kk : Fin n → Fin n → ℝ) (G : Fin n → (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) : ℝ :=
  (∑ i, (1 / (n : ℝ)) * (covW Kk w i)⁻¹ * G i w) / ∑ i, (1 / (n : ℝ)) * (covW Kk w i)⁻¹

/-- The identity kernel on the sample. -/
def idKer (n : ℕ) : Fin n → Fin n → ℝ := fun i j => if i = j then 1 else 0

/-! ### NN `lem:min-reduced` (extension) -/

/-- Structurally reduced: pairwise distinct incoming weights and nonzero outgoing weights. -/
def Reduced {din dout q : ℕ} (θ : Fin q → StatFormal.NNFibers.Wave1.Neuron din dout) : Prop :=
  Function.Injective (fun i => (θ i).1) ∧ ∀ i, (θ i).2 ≠ 0

namespace Claims

/-! #### REO `prop:ad-identity` -/

/-- `Θ(P₁) − Θ(P) = sup_f {(P₁ − P)g_f − Gap_P(f)}` (both values finite; `Gap_P(f) = Θ(P) − J_P(f)`). -/
def ad_identity : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P P₁ : Measure K) [IsProbabilityMeasure P] [IsProbabilityMeasure P₁],
    Setting ε a c →
      ∃ t t₁ : ℝ, OTdisc ε a c P = t ∧ OTdisc ε a c P₁ = t₁ ∧
        IsLUB (Set.range fun f : Fin k → ℝ =>
            (∫ y, gsoft ε a f c y ∂P₁ - ∫ y, gsoft ε a f c y ∂P) - (t - Jdual ε a c P f))
          (t₁ - t)

/-- `ω_P(r) = sup_f {Λ_P(g_f; r) − Gap_P(f)}`. -/
def ad_identity_omega : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P : Measure K) [IsProbabilityMeasure P] (r : ℝ),
    Setting ε a c → 0 ≤ r →
      ∃ t : ℝ, OTdisc ε a c P = t ∧
        omegaMod ε a c P r =
          ⨆ f : Fin k → ℝ, (lamMod P (gsoft ε a f c) r - ((t - Jdual ε a c P f : ℝ) : EReal))

/-- `ω^far_P(η) = sup_f {η(sup_K g_f − P g_f) − Gap_P(f)} ≥ η G₀`, `G₀ = sup_K g̃ − P g̃`, `g̃ = g_{f*}`. -/
def ad_identity_far : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P : Measure K) [IsProbabilityMeasure P] (η : ℝ),
    Setting ε a c → 0 ≤ η → η ≤ 1 →
      ∃ t : ℝ, OTdisc ε a c P = t ∧
        omegaFar ε a c P η =
          (⨆ (f : Fin k → ℝ) (z : K),
            ((η * (gsoft ε a f c z - ∫ y, gsoft ε a f c y ∂P) - (t - Jdual ε a c P f) : ℝ) : EReal)) ∧
        ∀ fs : Fin k → ℝ, (∀ f, Jdual ε a c P f ≤ Jdual ε a c P fs) → ∀ z : K,
          ((η * (gsoft ε a fs c z - ∫ y, gsoft ε a fs c y ∂P) : ℝ) : EReal) ≤ omegaFar ε a c P η

/-! #### REO `prop:ep-mcgap` -/

/-- `prop:ep-mcgap`, probability reference: almost surely (draws `X_{ij} ∼ ν`), for every `λ ∈ Λ`,
`λ(R_ε − R₀ − ε log(1/t)) ≤ T̂⁺_ε(λ; R_ε + β) − T^env_0(λ) ≤ λ(R_ε − R₀ + ε log(1 + t))`, with
`U^{(i)} = e^{φ_λ(x_i,·)/(λε)}`, range `R_i = e^{e_λ(x_i)/(λε)}` and `φ_λ ≤ e_λ` `ν`-a.e. -/
def ep_mcgap : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (ν : Measure K) [IsProbabilityMeasure ν]
    (P : Measure Ω) [IsProbabilityMeasure P] (n m : ℕ) (Λ : Finset ℝ) (φ : ℝ → Fin n → K → ℝ)
    (e : ℝ → Fin n → ℝ) (X : Fin n → Fin m → Ω → K) (ε Rε R0 β α : ℝ),
    0 < n → 0 < m → Λ.Nonempty → (∀ lam ∈ Λ, 0 < lam) → 0 < ε → 0 < α → α < 1 →
    (∀ lam ∈ Λ, ∀ i, ∀ᵐ x ∂ν, φ lam i x ≤ e lam i) →
    (∀ i j, Measurable (X i j)) → (∀ i j, P.map (X i j) = ν) →
      ∀ᵐ ω ∂P, ∀ lam ∈ Λ,
        lam * (Rε - R0 - ε * Real.log (1 / tCorr n m Λ.card α)) ≤
          StatFormal.RobustEquality.That n m (fun i x => Real.exp (φ lam i x / (lam * ε)))
              (fun i => Real.exp (e lam i / (lam * ε))) X lam ε (Rε + β) (n * Λ.card) α ω -
            tEnv lam R0 β (e lam) ∧
        StatFormal.RobustEquality.That n m (fun i x => Real.exp (φ lam i x / (lam * ε)))
              (fun i => Real.exp (e lam i / (lam * ε))) X lam ε (Rε + β) (n * Λ.card) α ω -
            tEnv lam R0 β (e lam) ≤
          lam * (Rε - R0 + ε * Real.log (1 + tCorr n m Λ.card α))

/-- `prop:ep-mcgap`, literally "every realisation": surely (every `ω`), when the envelope dominates on all of
`K` (`φ_λ(x_i, ·) ≤ e_λ(x_i)` everywhere, e.g. `S_ν = K`); no law on the draws is needed. -/
def ep_mcgap_sure : Prop :=
  ∀ (K Ω : Type) (n m : ℕ) (Λ : Finset ℝ) (φ : ℝ → Fin n → K → ℝ)
    (e : ℝ → Fin n → ℝ) (X : Fin n → Fin m → Ω → K) (ε Rε R0 β α : ℝ),
    0 < n → 0 < m → Λ.Nonempty → (∀ lam ∈ Λ, 0 < lam) → 0 < ε → 0 < α → α < 1 →
    (∀ lam ∈ Λ, ∀ i x, φ lam i x ≤ e lam i) →
      ∀ ω : Ω, ∀ lam ∈ Λ,
        lam * (Rε - R0 - ε * Real.log (1 / tCorr n m Λ.card α)) ≤
          StatFormal.RobustEquality.That n m (fun i x => Real.exp (φ lam i x / (lam * ε)))
              (fun i => Real.exp (e lam i / (lam * ε))) X lam ε (Rε + β) (n * Λ.card) α ω -
            tEnv lam R0 β (e lam) ∧
        StatFormal.RobustEquality.That n m (fun i x => Real.exp (φ lam i x / (lam * ε)))
              (fun i => Real.exp (e lam i / (lam * ε))) X lam ε (Rε + β) (n * Λ.card) α ω -
            tEnv lam R0 β (e lam) ≤
          lam * (Rε - R0 + ε * Real.log (1 + tCorr n m Λ.card α))

/-- `prop:ep-mcgap` for a sub-probability reference (`0 < ν(K) ≤ 1`): draws from `ν/ν(K)`, Monte-Carlo
mean multiplied by `ν(K)` (the estimator of the frozen `prop_mc_subprob`). -/
def ep_mcgap_subprob : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (ν : Measure K) [IsFiniteMeasure ν]
    (P : Measure Ω) [IsProbabilityMeasure P] (n m : ℕ) (Λ : Finset ℝ) (φ : ℝ → Fin n → K → ℝ)
    (e : ℝ → Fin n → ℝ) (X : Fin n → Fin m → Ω → K) (ε Rε R0 β α : ℝ),
    0 < n → 0 < m → Λ.Nonempty → (∀ lam ∈ Λ, 0 < lam) → 0 < ε → 0 < α → α < 1 →
    ν Set.univ ≠ 0 → ν Set.univ ≤ 1 →
    (∀ lam ∈ Λ, ∀ i, ∀ᵐ x ∂ν, φ lam i x ≤ e lam i) →
    (∀ i j, Measurable (X i j)) → (∀ i j, P.map (X i j) = (ν Set.univ)⁻¹ • ν) →
      ∀ᵐ ω ∂P, ∀ lam ∈ Λ,
        lam * (Rε - R0 - ε * Real.log (1 / tCorr n m Λ.card α)) ≤
          (lam * (Rε + β) + lam * ε / n * ∑ i, Real.log ((ν Set.univ).toReal *
              ((1 / (m : ℝ)) * ∑ j, Real.exp (φ lam i (X i j ω) / (lam * ε))) +
              Real.exp (e lam i / (lam * ε)) * tCorr n m Λ.card α)) - tEnv lam R0 β (e lam) ∧
        (lam * (Rε + β) + lam * ε / n * ∑ i, Real.log ((ν Set.univ).toReal *
              ((1 / (m : ℝ)) * ∑ j, Real.exp (φ lam i (X i j ω) / (lam * ε))) +
              Real.exp (e lam i / (lam * ε)) * tCorr n m Λ.card α)) - tEnv lam R0 β (e lam) ≤
          lam * (Rε - R0 + ε * Real.log (1 + tCorr n m Λ.card α))

/-! #### TM `prop:upper`, `cor:marginderived` -/

/-- `prop:upper`: under `ass:margin` (at `α* = TV(P,Q)`), for every `α ∈ [0,1)` and every `Ď ≥ D_{α,k}(P,Q)`,
`TV(P,Q) ≤ α + ω⁻¹(Ď)`. -/
def prop_upper : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ : ℝ)
    (ω : ℝ → ℝ) (α Dc : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → MarginCond φ P Q ω → 0 ≤ α → α < 1 →
    StatFormal.TrimmedMMD.Unconditional.Dpop φ P Q α ≤ Dc →
      StatFormal.Distances.tvDist P Q ≤ α + omegaInv ω (StatFormal.Distances.tvDist P Q) Dc

/-- The encoding `omegaInv` is the paper's extended inverse: on `[0, ω(α*)]` it inverts `ω`, and it equals
`α*` on `[ω(α*), ∞)`. -/
def omegaInv_spec : Prop :=
  ∀ (ω : ℝ → ℝ) (αs : ℝ), 0 ≤ αs → StrictMonoOn ω (Icc 0 αs) → ContinuousOn ω (Icc 0 αs) → ω 0 = 0 →
    (∀ u ∈ Icc 0 (ω αs), omegaInv ω αs u ∈ Icc 0 αs ∧ ω (omegaInv ω αs u) = u) ∧
    (∀ u, ω αs ≤ u → omegaInv ω αs u = αs)

/-- `cor:marginderived`, display: if an optimal trimmed pair `(P*_α, Q*_α)` (genuine trimmings whose MMD is
`D_{α,k}(P,Q)`) satisfies the conclusion of `thm:interp` with constants `|𝒳|, A_k, L', θ`, then
`D_{α,k}(P,Q) ≥ A_k⁻¹ (2(TV − α)/(|𝒳|^{1/2}(1−α)L'^{1−θ}))^{1/θ}`, for `0 ≤ α ≤ TV(P,Q)`, `α < 1`. -/
def marginderived : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ : ℝ)
    (α V A L θ : ℝ) (gP gQ : 𝒳 → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < V → 0 < A → 0 < L → 0 < θ →
    0 ≤ α → α ≤ StatFormal.Distances.tvDist P Q → α < 1 →
    StatFormal.TrimmedMMD.ZeroSet.IsTrimDensity P α gP → StatFormal.TrimmedMMD.ZeroSet.IsTrimDensity Q α gQ →
    trimMMD φ P Q gP gQ = StatFormal.TrimmedMMD.Unconditional.Dpop φ P Q α →
    InterpBound φ P Q gP gQ V A L θ →
      marginLB (StatFormal.Distances.tvDist P Q) α V A L θ ≤
        StatFormal.TrimmedMMD.Unconditional.Dpop φ P Q α

/-- `cor:marginderived`, last sentence: if for every `α ∈ [0, TV(P,Q)]`, `α < 1`, an optimal trimmed pair
satisfies `thm:interp` with the same (`α`-free) constants, then `ass:margin` holds in the power form
`ω(ε) = c₀ ε^γ`, `γ = 1/θ`. -/
def marginderived_power : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ : ℝ)
    (V A L θ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < V → 0 < A → 0 < L → 0 < θ →
    (∀ α, 0 ≤ α → α ≤ StatFormal.Distances.tvDist P Q → α < 1 →
      ∃ gP gQ : 𝒳 → ℝ, StatFormal.TrimmedMMD.ZeroSet.IsTrimDensity P α gP ∧
        StatFormal.TrimmedMMD.ZeroSet.IsTrimDensity Q α gQ ∧
        trimMMD φ P Q gP gQ = StatFormal.TrimmedMMD.Unconditional.Dpop φ P Q α ∧
        InterpBound φ P Q gP gQ V A L θ) →
      MarginCond φ P Q (fun e => marginC0 V A L θ * e ^ (1 / θ))

/-! #### TM `lem:nullbound` -/

/-- `lem:nullbound`: under `H_{0,α}` (`TV(P,Q) ≤ α`), surely (every sample),
`D̂_{α,k} ≤ d_H(𝒞_{α,k}(P_n), 𝒞_{α,k}(P)) + d_H(𝒞_{α,k}(Q_m), 𝒞_{α,k}(Q))`. -/
def nullbound : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 1 ≤ n → 1 ≤ m →
    StatFormal.Distances.tvDist P Q ≤ α →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        StatFormal.TrimmedMMD.Unconditional.Demp φ x y α ≤
          Metric.hausdorffDist (StatFormal.TrimmedMMD.Concentration.region φ α
              (StatFormal.TrimmedMMD.Concentration.empirical x))
            (StatFormal.TrimmedMMD.Concentration.region φ α P) +
          Metric.hausdorffDist (StatFormal.TrimmedMMD.Concentration.region φ α
              (StatFormal.TrimmedMMD.Concentration.empirical y))
            (StatFormal.TrimmedMMD.Concentration.region φ α Q)

/-! #### TM `lem:qpstability` -/

/-- The value of `eq:qp` is attained (so "the value" is a genuine minimum, for every Gram triple). -/
def qp_value_exists : Prop :=
  ∀ (n m : ℕ) (Kxx : Fin n → Fin n → ℝ) (Kyy : Fin m → Fin m → ℝ) (Kxy : Fin n → Fin m → ℝ) (α β : ℝ),
    1 ≤ n → 1 ≤ m → 0 ≤ α → α < 1 → 0 ≤ β → β < 1 →
      ∃ s, IsLeast (qpVals Kxx Kyy Kxy α β) s

/-- `lem:qpstability`: entrywise `ε`-close Gram triples give `eq:qp` values within `4ε`. -/
def qpstability : Prop :=
  ∀ (n m : ℕ) (Kxx Kxx' : Fin n → Fin n → ℝ) (Kyy Kyy' : Fin m → Fin m → ℝ)
    (Kxy Kxy' : Fin n → Fin m → ℝ) (α β ε s s' : ℝ),
    (∀ i j, |Kxx i j - Kxx' i j| ≤ ε) → (∀ i j, |Kyy i j - Kyy' i j| ≤ ε) →
    (∀ i j, |Kxy i j - Kxy' i j| ≤ ε) →
    IsLeast (qpVals Kxx Kyy Kxy α β) s → IsLeast (qpVals Kxx' Kyy' Kxy' α β) s' →
      |s - s'| ≤ 4 * ε

/-! #### ICL `prop:diag-identity` -/

/-- With `K = I` on the sample, `F_cov(w) = Σ_i G_i(w) w_i⁻¹ / Σ_i w_i⁻¹` (positive `w`). -/
def diag_identity_formula : Prop :=
  ∀ (n : ℕ) (G : Fin n → (Fin n → ℝ) → ℝ) (w : Fin n → ℝ), (∀ i, 0 < w i) →
    fcov (idKer n) G w = (∑ i, G i w * (w i)⁻¹) / ∑ i, (w i)⁻¹

/-- `prop:diag-identity`: if `w_{i₀} → 0` while the other coordinates stay bounded away from zero, and the
`G_i` stay bounded, then `F_cov(w) − G_{i₀}(w) → 0` (identity kernel; any filter). -/
def diag_identity : Prop :=
  ∀ (n : ℕ) (ι : Type) (l : Filter ι) (G : Fin n → (Fin n → ℝ) → ℝ) (w : ι → Fin n → ℝ) (i₀ : Fin n)
    (B c : ℝ),
    (∀ x i, 0 < w x i) → 0 < c → (∀ᶠ x in l, ∀ i, i ≠ i₀ → c ≤ w x i) →
    Tendsto (fun x => w x i₀) l (𝓝 0) → (∀ x i, |G i (w x)| ≤ B) →
      Tendsto (fun x => fcov (idKer n) G (w x) - G i₀ (w x)) l (𝓝 0)

/-! #### NN `lem:min-reduced` (extension of the certified `NNFibers.Wave1.Claims.min_reduced`) -/

/-- For `σ = exp` the two notions coincide: functionally minimal `⇔` structurally reduced. -/
def exp_minimal_iff_reduced : Prop :=
  ∀ (din dout q : ℕ) (θ : Fin q → StatFormal.NNFibers.Wave1.Neuron din dout),
    StatFormal.NNFibers.Wave1.FunctionallyMinimal Real.exp θ ↔ Reduced θ

/-- "… but not in general": for `tanh` a structurally reduced parameter need not be functionally minimal
(the converse of `lem:min-reduced` fails). -/
def tanh_reduced_not_minimal : Prop :=
  ∃ θ : Fin 2 → StatFormal.NNFibers.Wave1.Neuron 1 1,
    Reduced θ ∧ ¬ StatFormal.NNFibers.Wave1.FunctionallyMinimal Real.tanh θ

end Claims
end StatFormal.Wave15a
