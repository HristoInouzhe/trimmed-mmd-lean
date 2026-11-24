import StatFormal.Archive.Wave15a.Statements
import StatFormal.Archive.Wave24f.Statements
import StatFormal.Archive.OTFD.Wave17b.Statements
import StatFormal.Archive.Wave23d.Statements
import StatFormal.Archive.TrimmedMMD.ZeroSet.Statements
import StatFormal.Archive.Wave24c.Statements
import StatFormal.Archive.Wave23a.Statements
import StatFormal.Archive.OTFD.Wave5a.Statements
import StatFormal.Archive.OTFD.Scale.Statements

/-!
# FROZEN STATEMENTS — wave P1a (`PARTIAL_AUDIT.md`, Wave 1a: discharges by already-certified claims): TM
# `cor:marginderived`, `thm:consistency` (ii); otfd A `lem:app-chain-rule`, `prop:T-proxy` (asymptotic sentence);
# NN `thm:average-tube`, `cor:tube-threshold` (partial discharges)

Sources (verbatim in `lean-formalisation/inventory/extracted/{trimmed-mmd,otfd-A_sieves,proliferation-nns}.md`; current
text read 2026-10-16):
* TM `cor:marginderived` (`trimmed-mmd/paper.tex:1328-1343`), with `ass:smooth` (`:1298-1303`) and `thm:interp`
  (`:1314-1322`). Frozen partial claims: Wave 15a `marginderived`, `marginderived_power` (conditional on `InterpBound`,
  the conclusion of `thm:interp` for the optimal pair); `thm:interp` itself is the certified Wave 24f `interp_bound`.
* TM `thm:consistency` (ii) (`trimmed-mmd/paper.tex:966-981`). Frozen partial claim: `TrimmedMMD.consistency_ii`
  (conditional on the concentration events and on the properties of an abstract `D`); certified inputs:
  `TrimmedMMD.Unconditional.events` (the events, from `uniform_alpha`), `ZeroSet.zero_of_tv_le`, `ZeroSet.zeroeq`.
* A `lem:app-chain-rule` (`otfd/papers/A_sieves/supplement.tex:1340-1353`, proof `:1355-1385`), with
  `lem:app-pullback` (`:1325-1338`). Frozen partial claim: Wave 17b `chain_ae` (conditional on a Borel `G` that is a
  Gâteaux gradient of `φ_K` `P_K`-a.e., i.e. on Zajíček's theorem); certified inputs: Wave 23d `cm_gateaux`
  (`lem:app-cm-plans` (iii)), Wave 1 `pullback`.
* A `prop:T-proxy` (`otfd/papers/A_sieves/main.tex:1287-1295`, proof `supplement.tex:4984-5000`), the sentence "Hence,
  if `β_𝓑 → 0` in probability and `log|Θ| = o(n)`, the selected candidate is asymptotically as good as the best one
  in `Θ` for the probability-scale risk, and it is consistent whenever one of the candidates is", with `Ĉ_Υ`, `𝓡_𝒜`,
  `β_𝓑` (`main.tex:1276-1285`) and `lem:T-risk` (`supplement.tex:4937-4951`). Frozen partial claim: Wave 5a
  `tproxy_oracle` (the oracle inequality only); certified inputs: `OTFD.Scale.t_risk`, `OTFD.Scale.ups_ball`.
* NN `thm:average-tube` (`proliferation-and-geometry-in-nns/paper_revised.tex:1125-1137`), `cor:tube-threshold`
  (`:1139-1158`), proof `:1934-1950`, with `lem:marked-block-transform` (`:1001-1019`), `prop:average-offset-penalty`
  (`:1029-1035`), `lem:tube-reduction` (`:1892-1932`). Frozen partial claims: Wave 22c `average_tube`, Wave 23a
  `tube_threshold_discharged`; certified input: Wave 24c `average_offset_penalty`.
Imports the frozen statements of `Wave15a` (`trimMMD`, `InterpBound`, `marginLB`, `marginC0`, `MarginCond`),
`Wave24f` (`InterpHyp`, `sobNorm`; through it `OTFD/WaveL1.Euc`, `LipNull`), `OTFD/Wave17b` (`liftPot`, `liftGrad`,
`toE`), `Wave23d` (`subdiff`, `gatGrad`), `TrimmedMMD/ZeroSet` (`IsTrimDensity`, `Characteristic`; through it
`Unconditional`: `Dpop`, `Demp`), `Wave24c` (`markedPGF`), `Wave23a` (`HarperRep`; through it `Wave22c`), `OTFD/Wave5a`
(`msq`) and `OTFD/Scale` (`IsGauge`, `ScaleHyp`, `ups`), not copied.

Covered:
* `cor:marginderived`: `marginderived_smooth` (the display, with `InterpBound` replaced by `ass:smooth` for the optimal
  pair and the kernel comparison defining `A_k`, i.e. by the hypotheses of `thm:interp`; `|𝒳| = vol(X)`,
  `θ = t/(s+t)`), `marginderived_power_smooth` (the power form `ω(ε) = c₀ε^{1/θ}`, same replacement, `L'`, `X`, `s`,
  `t`, `A_k` independent of `α`).
* `thm:consistency` (ii): `consistency_ii_tv` (at the paper's `α* = TV(P,Q) ∈ (0,1)`, characteristic kernel, on a
  measurable event of probability `≥ 1 − δ`; `N` depends on `P, Q, φ, κ, δ, ε` only).
* `lem:app-chain-rule`, `P`-a.e. part: `chain_ae_pell` (for `P ∈ 𝒫^ℓ(H)`, `e` orthonormal, `φ_K` finite convex
  Lipschitz and any Borel selection `G` of `∂φ_K` with `G#P_K = μ_K`: the four conclusions of `chain_ae`).
* `prop:T-proxy`, asymptotic sentence: `tproxy_asymp` ("asymptotically as good as the best one": for every `η > 0`,
  with probability `→ 1`, every minimiser satisfies `𝓡(θ̂)^{1/2} ≤ 𝓡(θ)^{1/2} + η` for all `θ`), `tproxy_consistent`
  ("consistent whenever one of the candidates is": `𝓡(θ̂) → 0` and `F̂_θ̂ → F_K` in `P_K`-probability, in probability).
* (Removed by the coordinator: `average_tube_marked`, `tube_threshold_marked` were compositions of two certified claims — chain flattening, no progress; NN tube results remain conditional on SADDLE/Harper inputs.) Former entry: PARTIAL DISCHARGES
  (chain flattening only): the premise `prop:average-offset-penalty` is replaced by `eq:marked-pgf-asymptotic` on
  `(0,1]^q` (via the certified `average_offset_penalty`). The new premise is the paper's own display (restricted to
  `(0,1]^q`, so no stronger than printed) but is logically *stronger* than the one it replaces (it implies it, by
  Wave 24c), so each claim is a corollary of two certified claims: the effective open inputs (first claim of
  `lem:tube-reduction`, `eq:marked-pgf-asymptotic`; Harper, Moser–Wyman for the corollary) are unchanged, and the
  gain is that one claim now carries exactly those inputs.

Not covered (declared):
* `cor:marginderived`: the existence of the optimal pair (`lem:attainment`) stays a hypothesis as in Wave 15a (the
  paper hypothesises `ass:smooth` *for* that pair); "`γ = (s+t)/t` always exceeds 1" (a remark).
* `thm:consistency` (ii): nothing.
* `lem:app-chain-rule`: the existence of `φ_K` and of its Lipschitz representative (`cor:app-ghs-lipschitz`, GHS/McCann
  in `ℝ^K`): `φ_K`, `L` and the selection `G` enter as data with the stated properties.
* `prop:T-proxy`: "in probability over the training fold" — as in `tproxy_oracle` the candidates `F̂^𝒜_θ` are fixed
  (conditionally on `𝒜`); "neither statement needs a moment" is reflected by the absence of moment hypotheses.
* `thm:average-tube`, `cor:tube-threshold`: the first claim of `lem:tube-reduction` (`Ḡ_q ∼ e^{−t}U_q/T(q,m)`, a
  tilted-law bounded-convergence argument; only its last step `tube_gamma_shape` is certified) and
  `eq:marked-pgf-asymptotic` (saddle point) remain hypotheses; for the corollary also Harper and Moser–Wyman (as in
  Wave 23a). Wave 24c `tube_reduction_ratio` does not remove a premise here: it derives the ratio form from the same
  first claim, which both frozen claims already take.

Encodings (to be checked by the critic):
* `cor:marginderived`: `𝒳 ⊆ ℝ^d` is `Euc d`; "`P, Q` have densities" is `P = p·λ`, `Q = q·λ` (`withDensity`, `p, q`
  measurable, `≥ 0`); the optimal pair is `(g_P·P, g_Q·Q)` with Lebesgue densities `g_P p`, `g_Q q`; "`supp ⊆ 𝒳`" for the
  pair is `g_P p = g_Q q = 0` off a measurable `X` of finite volume (paper: bounded, which implies it), `|𝒳| = vol(X)`;
  `f ∈ L²(ℝ^d; ℂ)` is a representative of `g_P p − g_Q q`; `‖·‖_{H^σ}` is the frozen `sobNorm` (`[0, ∞]`, so both
  Sobolev bounds are `≤ ofReal`, no `toReal` junk); `A_k` is any `A > 0` with `‖p* − q*‖_{H^{−s}} ≤ A_k MMD_k(P*, Q*)`,
  `MMD_k(P*, Q*)` being the frozen `trimMMD`. `|𝒳| > 0` is proved, not assumed (Wave 15a assumes `0 < V`).
* `thm:consistency` (ii): the setting of `ZeroSet.consistency_tv`; the probability statement is a measurable event of
  probability `≥ 1 − δ` inside `{α* − ε ≤ α̂ ≤ α*}` (as in the unconditional (i)).
* `lem:app-chain-rule`: `𝒫^ℓ(H)` is the frozen `PellClass` (probability, finite second moment, null on Lipschitz
  hypersurfaces); "globally Lipschitz representative" is `|φ x − φ z| ≤ L‖x − z‖`; "`∇φ_K#P_K = μ_K`" is a Borel `G`
  with `G(z) ∈ ∂φ_K(z)` `P_K`-a.e. (frozen Wave 23d `subdiff`, the real-valued subdifferential) and `G#P_K = μ_K`
  (generalisation: `G = ∇φ_K` is an instance, and every such `G` equals `∇φ_K` `P_K`-a.e.). The conclusion is that
  of `chain_ae` verbatim.
* `prop:T-proxy`: a sequence of problems indexed by `n`, each on its own probability space `(Ω_n, P_n)`, with finite
  `Θ_n`, fixed candidates `F̂_{n,θ} : E → E` (Borel), held-out fold `𝓑 = Fin m_n`, `Z_{n,i}` independent with law
  `P_K`, arbitrary pilot values `b_{n,i}` (`= ΥF̂^𝓑_0(Z_i)` in the paper); `E` any finite-dimensional normed space
  (`ℝ^K`) and `Υ = ups` (frozen, under `IsGauge`, `ScaleHyp`), `R_Υ` any `R` with `g(w) ≤ 1 ⇒ ‖w‖ ≤ R`;
  `𝓡(θ) = riskA` (Bochner integral of a bounded measurable function, not junk), `Ĉ_Υ = msq (ΥF̂_θ(Z)) b`,
  `β_𝓑 = msq b (ΥF_K(Z))`. "`log|Θ| = o(n)`" is `log|Θ_n|/m_n → 0` together with `m_n → ∞` (`|𝓑| ≍ n`). "`β_𝓑 → 0` in
  probability" is `P_n{β > η} → 0` (outer measure, so `b` need not be measurable). "With probability `→ 1`" is: for
  every `γ > 0`, eventually there is a measurable event of probability `≥ 1 − γ` on which the statement holds for
  **every** minimiser `θ̂` (no measurable selection). Convergence in `P_K`-probability is
  `P_K{‖F̂ − F_K‖ > η} → 0` (as in `t_risk`); "one of the candidates is consistent" is a choice `θ*_n ∈ Θ_n` with
  `F̂_{n,θ*_n} → F_K` in `P_K`-probability.
* NN: the frozen Wave 22c objects; `markedPGF` is the frozen Wave 24c one, the premise exactly the one of
  `average_offset_penalty`.

Critic notes:
* All claims are mechanical diffs of the frozen partial claims: `marginderived{,_power}_smooth` replace `InterpBound`
  (and `0 < V`, `V`, `θ`) by the hypotheses of `thm:interp`; `consistency_ii_tv` replaces the abstract `D`, its three
  properties and the events by `Dpop` at `α* = TV` with A3; `chain_ae_pell` replaces "`G` is `P_K`-a.e. a Gâteaux
  gradient" (and `IsProbabilityMeasure P`) by `PellClass P`, orthonormal `e`, Lipschitz `φ`, `G ∈ ∂φ` a.e.;
  `average_tube_marked`, `tube_threshold_marked` replace the `avgOffset` premises by the marked-pgf premises.
* Proof routes: `WaveP1a/Route{Margin,Consistency,Chain,Proxy,Tube}.lean` (`WaveP1a/Proofs.lean` checks each claim);
  axioms propext, Classical.choice, Quot.sound. Routes reuse the certified Wave 15a `marginderived{,_power}`, Wave 24f
  `interp_bound`, `TrimmedMMD.consistency_ii`, `event_prob`, `Unconditional.events`, `ZeroSet.{zero_of_tv_le,zeroeq}`,
  Wave 17b `chain_ae`, Wave 23d `cm_gateaux`, Wave 1 `pullback`, Wave 5a `tproxy_oracle`, `Scale.{t_risk,ups_ball}`,
  Wave 22c `average_tube`, Wave 23a `tube_threshold_discharged`, Wave 24c `average_offset_penalty` — routes only.
* Manuscripts: no statement found false. `thm:consistency` (ii) uses A3 only for `D > 0` below `TV`; `prop:T-proxy`'s
  sentence is a statement given `𝒜` (candidates fixed); `|𝓑| → ∞` is automatic from `|𝓑| ≍ n`.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics
open scoped ENNReal InnerProductSpace

namespace StatFormal.WaveP1a

open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.OTFD.Scale (IsGauge ScaleHyp ups)

/-! ### TM `cor:marginderived` -/

/-- `ass:smooth` for the optimal pair `(g_P·P, g_Q·Q)` of densities `g_P p`, `g_Q q`: both vanish off `X`, and
`f ∈ L²` is a representative of `g_P p − g_Q q` with `‖g_P p − g_Q q‖_{H^t} ≤ L`. -/
def SmoothPair {d : ℕ} (p q gP gQ : Euc d → ℝ) (X : Set (Euc d)) (f : Lp ℂ 2 (volume : Measure (Euc d)))
    (t L : ℝ) : Prop :=
  (∀ x ∉ X, gP x * p x = 0 ∧ gQ x * q x = 0) ∧
    (f : Euc d → ℂ) =ᵐ[volume] (fun x => ((gP x * p x - gQ x * q x : ℝ) : ℂ)) ∧
    StatFormal.Wave24f.sobNorm t f ≤ ENNReal.ofReal L

/-! ### otfd A `prop:T-proxy` -/

section Proxy
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- The probability-scale risk `𝓡(G) = E‖ΥG(Z) − ΥF_K(Z)‖²`, `Z ∼ P_K`. -/
def riskA (μ : Measure E) (g : E → ℝ) (PK : Measure E) (FK G : E → E) : ℝ :=
  ∫ z, ‖ups μ g (G z) - ups μ g (FK z)‖ ^ 2 ∂PK

/-- The cross-fitted proxy `Ĉ_Υ(G) = |𝓑|⁻¹ Σ_{i∈𝓑} ‖ΥG(Z_i) − b_i‖²`. -/
def proxyC {m : ℕ} (μ : Measure E) (g : E → ℝ) (G : E → E) (z : Fin m → E) (b : Fin m → E) : ℝ :=
  StatFormal.OTFD.Wave5a.msq (fun i => ups μ g (G (z i))) b

/-- The pilot's in-sample error `β_𝓑 = |𝓑|⁻¹ Σ_{i∈𝓑} ‖b_i − ΥF_K(Z_i)‖²`. -/
def betaB {m : ℕ} (μ : Measure E) (g : E → ℝ) (FK : E → E) (z : Fin m → E) (b : Fin m → E) : ℝ :=
  StatFormal.OTFD.Wave5a.msq b (fun i => ups μ g (FK (z i)))

end Proxy

namespace Claims

/-! #### TM `cor:marginderived` -/

/-- `cor:marginderived`, display, with `InterpBound` DISCHARGED by the certified `thm:interp`: if `P = p·λ`,
`Q = q·λ` on `ℝ^d`, `(g_P·P, g_Q·Q)` is an optimal trimmed pair, `ass:smooth` holds for it (support in `X`,
`‖p* − q*‖_{H^t} ≤ L'`) and `‖p* − q*‖_{H^{−s}} ≤ A_k MMD_k(P*, Q*)`, then
`D_{α,k}(P,Q) ≥ A_k⁻¹ (2(TV − α)/(|X|^{1/2}(1−α)L'^{1−θ}))^{1/θ}`, `θ = t/(s+t)`. -/
def marginderived_smooth : Prop :=
  ∀ (d : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure (Euc d)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : Euc d → H) (κ : ℝ)
    (p q : Euc d → ℝ) (X : Set (Euc d)) (f : Lp ℂ 2 (volume : Measure (Euc d))) (α s t A L : ℝ)
    (gP gQ : Euc d → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < A → 0 < L → 0 < s → 0 < t →
    Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) → Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
    MeasurableSet X → volume X < ∞ →
    0 ≤ α → α ≤ StatFormal.Distances.tvDist P Q → α < 1 →
    StatFormal.TrimmedMMD.ZeroSet.IsTrimDensity P α gP → StatFormal.TrimmedMMD.ZeroSet.IsTrimDensity Q α gQ →
    StatFormal.Wave15a.trimMMD φ P Q gP gQ = StatFormal.TrimmedMMD.Unconditional.Dpop φ P Q α →
    SmoothPair p q gP gQ X f t L →
    StatFormal.Wave24f.sobNorm (-s) f ≤ ENNReal.ofReal (A * StatFormal.Wave15a.trimMMD φ P Q gP gQ) →
      StatFormal.Wave15a.marginLB (StatFormal.Distances.tvDist P Q) α (volume X).toReal A L (t / (s + t)) ≤
        StatFormal.TrimmedMMD.Unconditional.Dpop φ P Q α

/-- `cor:marginderived`, last sentence, with `InterpBound` DISCHARGED: if for every `α ∈ [0, TV(P,Q)]`, `α < 1`, an
optimal trimmed pair satisfies `ass:smooth` and the kernel comparison with the same (`α`-free) `X, s, t, A_k, L'`,
then `ass:margin` holds in the power form `ω(ε) = c₀ ε^{1/θ}`, `θ = t/(s+t)`. -/
def marginderived_power_smooth : Prop :=
  ∀ (d : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure (Euc d)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : Euc d → H) (κ : ℝ)
    (p q : Euc d → ℝ) (X : Set (Euc d)) (s t A L : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < A → 0 < L → 0 < s → 0 < t →
    Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) → Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
    MeasurableSet X → volume X < ∞ →
    (∀ α, 0 ≤ α → α ≤ StatFormal.Distances.tvDist P Q → α < 1 →
      ∃ (gP gQ : Euc d → ℝ) (f : Lp ℂ 2 (volume : Measure (Euc d))),
        StatFormal.TrimmedMMD.ZeroSet.IsTrimDensity P α gP ∧ StatFormal.TrimmedMMD.ZeroSet.IsTrimDensity Q α gQ ∧
        StatFormal.Wave15a.trimMMD φ P Q gP gQ = StatFormal.TrimmedMMD.Unconditional.Dpop φ P Q α ∧
        SmoothPair p q gP gQ X f t L ∧
        StatFormal.Wave24f.sobNorm (-s) f ≤ ENNReal.ofReal (A * StatFormal.Wave15a.trimMMD φ P Q gP gQ)) →
      StatFormal.Wave15a.MarginCond φ P Q
        (fun e => StatFormal.Wave15a.marginC0 (volume X).toReal A L (t / (s + t)) * e ^ (1 / (t / (s + t))))

/-! #### TM `thm:consistency` (ii) -/

/-- `thm:consistency` (ii), unconditional, at the paper's `α* = TV(P,Q)`: under A3, if `0 < TV(P,Q) < 1`, then for
every `ε ∈ (0, α*]` there is `N` such that for all `n, m ≥ N` (and `≥ 1`), `α* − ε ≤ α̂ ≤ α*` on a measurable event of
probability `≥ 1 − δ`. -/
def consistency_ii_tv : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.TrimmedMMD.ZeroSet.Characteristic φ →
    0 < κ → 0 < δ → δ < 1 →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
    ∀ ε ∈ Ioc (0 : ℝ) (StatFormal.Distances.tvDist P Q), ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | StatFormal.TrimmedMMD.alphaHat (StatFormal.TrimmedMMD.Unconditional.Demp φ z.1 z.2)
              (fun α => StatFormal.TrimmedMMD.tau κ α δ n m) ∈
            Icc (StatFormal.Distances.tvDist P Q - ε) (StatFormal.Distances.tvDist P Q)}

/-! #### otfd A `lem:app-chain-rule` -/

/-- `lem:app-chain-rule`, `P`-a.e. part, with the Zajíček premise DISCHARGED (certified `lem:app-cm-plans` (iii) and
`lem:app-pullback`): for `P ∈ 𝒫^ℓ(H)`, orthonormal `e`, `φ_K` finite convex `L`-Lipschitz and a Borel selection `G`
of `∂φ_K` (`P_K`-a.e.) with `G#P_K = μ_K`: `P`-a.e. the gradients of `ψ_K` are exactly `ι_K G(Π_K x)`, this map
pushes `P` to `ι_K#μ_K`, and `(Id × ∇ψ_K)#P` couples `P` and `ι_K#μ_K` with support in `∂ψ_K`. -/
def chain_ae_pell : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (e : ℕ → H) (K : ℕ) (φ : EuclideanSpace ℝ (Fin K) → ℝ) (L : ℝ)
    (P : Measure H) (μK : Measure (EuclideanSpace ℝ (Fin K)))
    (G : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    Orthonormal ℝ e → StatFormal.OTFD.Wave1.PellClass P → ConvexOn ℝ univ φ →
    (∀ x z, |φ x - φ z| ≤ L * ‖x - z‖) → Measurable G →
    (∀ᵐ z ∂(P.map (StatFormal.OTFD.Wave1.truncK e K)), G z ∈ StatFormal.Wave23d.subdiff φ z) →
    (P.map (StatFormal.OTFD.Wave1.truncK e K)).map G = μK →
      Measurable (StatFormal.OTFD.Wave17b.liftGrad e K G) ∧
      (∀ᵐ x ∂P, ∀ g : H, StatFormal.OTFD.Wave13a.IsGatGrad (StatFormal.OTFD.Wave17b.liftPot e K φ) x g ↔
        g = StatFormal.OTFD.Wave17b.liftGrad e K G x) ∧
      P.map (StatFormal.OTFD.Wave17b.liftGrad e K G) = μK.map (StatFormal.OTFD.Wave13a.liftK e K) ∧
      StatFormal.OTFD.Wave13a.GradPushes (StatFormal.OTFD.Wave17b.liftPot e K φ) P
        (μK.map (StatFormal.OTFD.Wave13a.liftK e K)) ∧
      StatFormal.OTFD.Wave13a.IsCoupling (P.map fun x => (x, StatFormal.OTFD.Wave17b.liftGrad e K G x)) P
        (μK.map (StatFormal.OTFD.Wave13a.liftK e K)) ∧
      (P.map fun x => (x, StatFormal.OTFD.Wave17b.liftGrad e K G x)).support ⊆
        StatFormal.OTFD.Wave13a.subdiff (StatFormal.OTFD.Wave17b.liftPot e K φ)

/-! #### otfd A `prop:T-proxy`, asymptotic sentence -/

/-- `prop:T-proxy`, "asymptotically as good as the best one": if `β_𝓑 → 0` in probability, `|𝓑| → ∞` and
`log|Θ| = o(|𝓑|)`, then for every `η > 0`, with probability `→ 1`, every minimiser `θ̂` of `Ĉ_Υ` satisfies
`𝓡(θ̂)^{1/2} ≤ 𝓡(θ)^{1/2} + η` for all `θ ∈ Θ`. -/
def tproxy_asymp : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (g : E → ℝ) (R : ℝ),
    IsGauge g → ScaleHyp μ g → (∀ w, g w ≤ 1 → ‖w‖ ≤ R) →
    ∀ (PK : Measure E) [IsProbabilityMeasure PK] (FK : E → E) (Θ : ℕ → Type) [∀ n, Fintype (Θ n)]
      [∀ n, Nonempty (Θ n)] (Fh : ∀ n, Θ n → E → E) (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)]
      (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)] (m : ℕ → ℕ) (Z : ∀ n, Fin (m n) → Ω n → E)
      (b : ∀ n, Fin (m n) → Ω n → E),
      Measurable FK → PK.map FK = μ → (∀ n θ, Measurable (Fh n θ)) →
      (∀ n, 0 < m n) → (∀ n i, Measurable (Z n i)) → (∀ n, iIndepFun (Z n) (P n)) →
      (∀ n i, (P n).map (Z n i) = PK) →
      Tendsto m atTop atTop → Tendsto (fun n => Real.log (Fintype.card (Θ n)) / m n) atTop (𝓝 0) →
      (∀ η > 0, Tendsto (fun n => P n {ω | η < betaB μ g FK (fun i => Z n i ω) (fun i => b n i ω)})
        atTop (𝓝 0)) →
        ∀ η > 0, ∀ γ > 0, ∀ᶠ n in atTop, ∃ S : Set (Ω n), MeasurableSet S ∧ ENNReal.ofReal (1 - γ) ≤ P n S ∧
          ∀ ω ∈ S, ∀ θhat : Θ n,
            (∀ θ, proxyC μ g (Fh n θhat) (fun i => Z n i ω) (fun i => b n i ω) ≤
              proxyC μ g (Fh n θ) (fun i => Z n i ω) (fun i => b n i ω)) →
            ∀ θ, √(riskA μ g PK FK (Fh n θhat)) ≤ √(riskA μ g PK FK (Fh n θ)) + η

/-- `prop:T-proxy`, "consistent whenever one of the candidates is": under the hypotheses of `tproxy_asymp`, if
`F̂_{θ*_n} → F_K` in `P_K`-probability for some `θ*_n ∈ Θ_n`, then with probability `→ 1` every minimiser `θ̂` has
`𝓡(θ̂) ≤ ε` and `P_K{‖F̂_θ̂ − F_K‖ > η} ≤ ε` (`ε, η > 0` arbitrary). -/
def tproxy_consistent : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (g : E → ℝ) (R : ℝ),
    IsGauge g → ScaleHyp μ g → (∀ w, g w ≤ 1 → ‖w‖ ≤ R) →
    ∀ (PK : Measure E) [IsProbabilityMeasure PK] (FK : E → E) (Θ : ℕ → Type) [∀ n, Fintype (Θ n)]
      [∀ n, Nonempty (Θ n)] (Fh : ∀ n, Θ n → E → E) (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)]
      (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)] (m : ℕ → ℕ) (Z : ∀ n, Fin (m n) → Ω n → E)
      (b : ∀ n, Fin (m n) → Ω n → E) (θs : ∀ n, Θ n),
      Measurable FK → PK.map FK = μ → (∀ n θ, Measurable (Fh n θ)) →
      (∀ n, 0 < m n) → (∀ n i, Measurable (Z n i)) → (∀ n, iIndepFun (Z n) (P n)) →
      (∀ n i, (P n).map (Z n i) = PK) →
      Tendsto m atTop atTop → Tendsto (fun n => Real.log (Fintype.card (Θ n)) / m n) atTop (𝓝 0) →
      (∀ η > 0, Tendsto (fun n => P n {ω | η < betaB μ g FK (fun i => Z n i ω) (fun i => b n i ω)})
        atTop (𝓝 0)) →
      (∀ η > 0, Tendsto (fun n => PK.real {z | η < ‖Fh n (θs n) z - FK z‖}) atTop (𝓝 0)) →
        ∀ η > 0, ∀ ε > 0, ∀ γ > 0, ∀ᶠ n in atTop, ∃ S : Set (Ω n), MeasurableSet S ∧
          ENNReal.ofReal (1 - γ) ≤ P n S ∧
          ∀ ω ∈ S, ∀ θhat : Θ n,
            (∀ θ, proxyC μ g (Fh n θhat) (fun i => Z n i ω) (fun i => b n i ω) ≤
              proxyC μ g (Fh n θ) (fun i => Z n i ω) (fun i => b n i ω)) →
            riskA μ g PK FK (Fh n θhat) ≤ ε ∧ PK.real {z | η < ‖Fh n θhat z - FK z‖} ≤ ε

end Claims
end StatFormal.WaveP1a
