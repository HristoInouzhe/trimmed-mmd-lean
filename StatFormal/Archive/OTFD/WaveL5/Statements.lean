import StatFormal.Archive.OTFD.WaveL2.Statements
import StatFormal.Archive.OTFD.WaveL3.Statements
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# FROZEN STATEMENTS — otfd wave L5 (discharges of wave L2): energy-distance identifiability in a separable Hilbert
# space, A `thm:rt-coherent` (`𝓔_∞ > 0`, `S_Λ(K) → 0`, `𝓔_K ≥ 𝓔_∞/2 > 0` eventually, consistency for all large `K`),
# GHS Lemma 4.3 (a.e. inverse of `𝔽_Λ`), A `prop:rt-lift`(ii) with the injectivity derived

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-A_sieves.md`; current text of
`otfd/papers/A_sieves/`):
* `thm:rt-coherent` (`main.tex:1479-1491`) with its proof (`supplement.tex:4360-4394`: "Positivity of the limit" uses
  Lyons 2013 and GHS Lemma 4.3 `𝕢_Λ ∘ 𝔽_Λ = Id` `Λ`-a.e.; "Levels" uses `thm:rt-fixedK`) and the setting paragraph
  (`main.tex:1378-1402`: `𝓔_∞(P, Q) = 𝒟_H(𝔽_Λ#P, 𝔽_Λ#Q)`, "the energy distance `𝒟` is nonnegative and vanishes only
  for equal laws, in `ℝ^K` and in any separable Hilbert space").
* `def:ghs-rank` (`main.tex:722-737`: `μ ∈ 𝒫^ℓ(H)` boundedly supported, `𝔽_P` the `P`-a.e. unique gradient of a convex
  function pushing `P` to `μ`, `𝕢_P = 𝔽_P⁻¹`) and `lem:app-cm-plans`(viii) (`supplement.tex:1460-1474`, GHS Lemma 4.3).
* `prop:integrated-sieve-strong` (`main.tex:800-821`) applied to `Λ` (as in the proof of `thm:rt-coherent`).
* `prop:rt-lift`(ii) (`supplement.tex:5558-5570`) with its proof (`supplement.tex:5034-5046`: head map Brenier between
  absolutely continuous laws, tail maps `t_k = G_{U_k}^{-1} ∘ G_{Λ,k}` strictly increasing where the `k`-th marginal of
  `Λ_T` has positive density).
* The frozen wave-L2 claims (`OTFD/WaveL2/Statements.lean`) `ed_nonneg`, `ed_eq_zero_iff` (finite dimension),
  `rt_coherent_consistent` (conditional on `0 < 𝓔_K`), `rt_lift_sep` (conditional on the injectivity of the lift), and
  the frozen wave-22a `rt_coherent_eventually` (conditional on `S_Λ(K) → 0` and `𝓔_∞ > 0`).
Imports the frozen `OTFD/WaveL2` (`FixedKSetting`, `critVal`, `rankEnergy`, `pool`; through it `OTFD/Wave22a` `mix`,
`energyD`, `IsConvGradAE`, `headT`, `liftMap`, `OTFD/Ranks` `IsMin`) and `OTFD/WaveL3` (through it `OTFD/WaveL1`
`IsCMMapAE`, `LipNull`, `Mom2`, `Euc`, `OTFD/Wave1` `PellClass`, `truncK`, `OTFD/Wave8b` `embed`) statements, not copied.
Mathlib otherwise (`cdf`, `withDensity`). One new definition, `popTail` (the population tail map).

Covered:
* Energy distance on a separable real Hilbert space: `ed_nonneg_H`, `ed_eq_zero_iff_H` (the frozen `energyD`; finite
  first moments; Lyons 2013). Generalise the frozen `ed_nonneg`, `ed_eq_zero_iff` (`FiniteDimensional` replaced by
  second countability, plus completeness for the identifiability).
* GHS Lemma 4.3 / A `lem:app-cm-plans`(viii): `ghs_inverse_H` (a Borel `𝕢`, `μ`-a.e. cyclically monotone, `𝕢#μ = P`,
  with `𝕢 ∘ 𝔽 = Id` `P`-a.e. and `𝔽 ∘ 𝕢 = Id` `μ`-a.e.; `P`, `μ` null on Lipschitz hypersurfaces with second moments).
* `thm:rt-coherent`: `rt_coherent_Einf_pos` (`𝓔_∞(P, Q) > 0 ⇔ P ≠ Q`), `rt_coherent_sieve_limit`
  (`S_Λ(K)² = ∫‖ι_K F_K Π_K − 𝔽_Λ‖² dΛ → 0`), `rt_coherent_eventually_pos` (eventually `𝓔_∞/2 ≤ 𝓔_K` and `0 < 𝓔_K`, with
  `𝓔_K = 𝒟(F_K#P_K, F_K#Q_K)` on `ℝ^K`), `rt_coherent_consistent_large_K` (there is `K₁` such that every fixed-`K`
  rank-energy test with `K ≥ K₁` is consistent: the frozen `rt_coherent_consistent` at `P_K, Q_K, μ_K, F_K` with its
  premise `0 < 𝓔_K` discharged).
* `prop:rt-lift`(ii): `rt_lift_sep_density` (the frozen `rt_lift_sep` with the tail maps the population tail maps
  `q_j ∘ G_{Λ,j}` and the two injectivity premises replaced by the paper's assumptions: Brenier head map between
  absolutely continuous laws, tail marginals with positive densities on open intervals carrying them, reference
  quantiles strictly increasing on `(0, 1)`).

Not covered (declared):
* `thm:rt-coherent`, the displayed bound `|𝓔_K − 𝓔_∞| ≤ 4(θ^{−1/2} + (1−θ)^{−1/2}) S_Λ(K)`: already the frozen wave-22a
  `rt_coherent_bound`; `Λ ∈ 𝒫^ℓ(H)`: the frozen wave-22a `rt_coherent_pell`. Not restated.
* GHS hypotheses: none remains a premise. The two infinite-dimensional facts that the library
  `Foundations/EnergyHilbert` kept as hypotheses — (a) `𝔽_Λ` optimal and the unique optimal plan between `Λ` and `μ`
  (GHS Hilbert Brenier–McCann), (b) `𝔽_Λ` injective on a `Λ`-conull set (GHS Lemma 4.3) — are derived in the routes
  from the certified wave-L3 uniqueness/existence (`brenier_uniq_H`, `brenier_exists_H`, AGS 6.2.10), under
  `P, Q ∈ 𝒫^ℓ(H)` (with A's second moments) and `μ` null on Lipschitz hypersurfaces.
* Moments (restriction vs GHS, not vs A's `thm:rt-coherent`): A's `𝒫^ℓ(H)` includes a finite second moment
  (`def:app-lipschitz-hypersurface`), used here through `PellClass`; GHS's class has none. The identifiability claims
  assume first moments only. `ghs_inverse_H` assumes `m₂(P), m₂(μ) < ∞`: a restriction in `P` (A `lem:app-cm-plans`(viii)
  uses no moment of `P`; the moment-free case needs McCann/GHS uniqueness without an integrable cost, see the frozen
  wave-L3 "Not covered") and a generalisation in `μ` ((viii) assumes `μ` boundedly supported). The restriction is
  immaterial where A uses (viii) (`A = Λ ∈ 𝒫^ℓ(H)`, which has A's second moment).
* References: the claims are stated for any reference `μ` carried by a closed ball, null on Lipschitz hypersurfaces
  where the inverse is needed (`rt_coherent_Einf_pos`, `_eventually_pos`, `_consistent_large_K`), with the coherent
  truncations `μ_K = Π_K#μ` (generalisation of the cubic and ball laws, which satisfy both: A `lem:app-references-Pl`).
  `rt_coherent_sieve_limit` needs no Lipschitz-nullity of `μ`.
* `prop:rt-lift`(ii): `Λ_T ≪ Leb` is used only through its head marginal `Λ_K ≪ Leb` and the tail densities
  (generalisation); `m₂(Λ_K) < ∞`, `m₂(μ_K) < ∞` are added (Tau Ceti's Brenier theorem; restriction, automatic for the
  bounded references), and the integrability of the lifted map under `P_T`, `Q_T` is kept from the frozen `rt_lift_sep`.
  The reference quantile `q_j` is any measurable function strictly increasing on `(0, 1)` (generalisation of the
  quantile function of an atomless reference marginal with interval support).
* `lem:app-cm-plans`(viii), the remaining clauses: the transpose identity `(𝔽 × Id)#P = (Id × 𝕢)#μ` (immediate from
  `𝕢 ∘ 𝔽 = Id` `P`-a.e. and `𝔽#P = μ`), the `μ`-a.e. uniqueness of `𝕢`, the Borel sets `E, E'` with `𝔽 : E → E'`
  bijective, and "every `∇χ` with `∇χ#μ = A` equals `𝕢` `μ`-a.e." (that is the frozen wave-L3 `brenier_uniq_H_swap`,
  with second moments) are not restated.
* `rt_coherent_consistent_large_K` inherits the wave-L2 encoding of `thm:rt-fixedK` at each level (restriction):
  `Λ_K ≪ Leb` and `IsConvGradAE` (`P, Q ∈ 𝒫^ℓ(H)` does not give `Λ_K ≪ Leb`; at levels where it fails the claim
  says nothing), bounded grids with weak convergence (weaker than `W₂`, a generalisation).

Encodings (to be checked by the critic):
* `H : Type` a separable real Hilbert space with its Borel σ-algebra; `e` an orthonormal basis (`Orthonormal ℝ e`, dense
  span); `Π_K = truncK e K`, `ι_K = embed e K` (frozen). `𝒫^ℓ(H)` is the frozen `PellClass` (probability, finite second
  moment, null on Lipschitz hypersurfaces); `μ ∈ 𝒫^ℓ(H)` boundedly supported is `LipNull μ` and `μ(B̄(0, M)ᶜ) = 0` (the
  second moment follows). `Λ = mix θ P Q` (frozen).
* `𝔽_Λ` is any Borel `g` with `g#Λ = μ` that is `Λ`-a.e. cyclically monotone (frozen `IsCMMapAE`, the wave-L1/L3
  encoding of the Brenier map; by Rockafellar `Λ`-a.e. a subgradient selection of a convex function, so the paper's
  `∇ψ̃` qualifies). It is not assumed bounded everywhere (a Borel version is arbitrary off a `Λ`-null set; boundedness
  `‖g‖ ≤ M` holds `Λ`-a.e. from `g#Λ = μ`). `𝓔_∞ = energyD (P.map g) (Q.map g)`.
* `F^Λ_K` is a family `FK K : ℝ^K → ℝ^K`, Borel, `FK K#Λ_K = μ_K`, `Λ_K`-a.e. cyclically monotone (`IsCMMapAE`, for every
  `K`, as in the frozen `sieve_strong_limit_uncond`); at a tested level `K` the frozen `FixedKSetting` additionally
  requires `IsConvGradAE` and `Λ_K ≪ Leb` (the wave-L2 encoding). `𝓔_K = energyD ((P.map Π_K).map (FK K)) …` (the
  `ℝ^K` form used by `FixedKSetting`; the frozen wave-22a `rt_coherent_eventually` has the `H`-embedded form, equal by
  isometry). `S_Λ(K)² = ∫⁻ ‖ι_K F_K Π_K x − g x‖² dΛ` (lower integral, as in the frozen `sieve_strong_limit_uncond`).
* `rt_coherent_consistent_large_K`: `∃ K₁, ∀ K ≥ K₁`, for every probability space, sample sizes, grids, measurable
  selection rule of optimal assignments and `α ∈ (0, 1)` satisfying the frozen `FixedKSetting` at level `K` for
  `(Π_K#P, Π_K#Q, Π_K#μ, FK K)`, the conclusion of the frozen `rt_coherent_consistent` (measurable rejection events,
  probability `→ 1`). `K₁` depends on `P, Q, θ, M, μ, e, FK, g` only (not on `α`, the grids or the sample).
* `popTail θ P Q q j = q j ∘ cdf (Λ.map x_j)`: `cdf` of a probability measure (`Λ.map x_j` is one), no junk. Tail
  densities: `Λ.map x_j = Leb.withDensity f_j` with `f_j > 0` on the open interval `I_j` (`IsOpen`, `OrdConnected`) and
  `Λ{x_j ∉ I_j} = 0`.

Critic notes:
* All 8 claims are proved in `OTFD/WaveL5/Route{Bridge,ED,Coherent,Lift}.lean`, checked in `OTFD/WaveL5/Proofs.lean`
  (`#print axioms`: propext, Classical.choice, Quot.sound). Routes use the untrusted library
  `Foundations/EnergyHilbert` (Lyons identifiability via Gaussian MMD, `rt_coherent_Einf_pos`, `rt_coherent_eventually_pos`,
  `energyD_sieveMap`, `rt_lift_sep_derived`), `Foundations/Potentials/HilbertUniqueness`, and the certified routes of
  waves L2 (`rt_coherent_consistent`, `rt_lift_sep`), L3 (`brenierUniq_of_lipNull`, `exists_brenierMap_of_lipNull`,
  `sieve_strong_limit_uncond`) and 22a (`rt_coherent_eventually`, `rt_fixedK_laws`) — routes only.
* Proof of (b) (`ghs_inverse_H`): `brenier_exists_H` for `(μ, P)` gives `𝕢`; the transposed graph `(𝕢 × Id)#μ` is a
  coupling of `(P, μ)` concentrated on a cyclically monotone set, so by `brenier_uniq_H` it is `(Id × 𝔽)#P`; the graph
  sets `{𝕢(y) = x}`, `{𝔽(x) = y}` have full mass under both. (a) is derived from AGS 6.2.10 (unique optimal plan) and
  `cmConc_graph` (the graph of `𝔽_Λ` is that plan).
* No tautology: every conclusion (a positivity, an identity of laws, an a.e. inverse, a limit, an eventual bound, a
  consistency) is absent from the hypotheses; no premise mentions `𝓔_K`, `𝓔_∞` or `S_Λ`. Nonvacuity: `𝔽_Λ` and `F_K`
  exist (frozen `brenier_exists_H` in `H` and in `ℝ^K`), `FixedKSetting` is satisfiable (frozen wave-L2 note).
* No statement of the paper was found false. `thm:rt-coherent` uses `𝕢_Λ ∘ 𝔽_Λ = Id` (GHS Lemma 4.3, A
  `lem:app-cm-plans`(viii)), which needs the reference `μ` itself null on Lipschitz hypersurfaces. This is not a gap:
  the theorem fixes "`μ` the cubic or the ball law of `subsec:pullback`", which lie in `𝒫^ℓ(H)` by
  `lem:app-references-Pl`, as `subsec:pullback` says ("where `μ ∈ 𝒫^ℓ(H)` is boundedly supported (both constructions
  below qualify …)"). `LipNull μ` here is the generalisation to any such reference; `rt_coherent_sieve_limit` does not
  need it.
* Critic (2026-10-15): ACCEPT, documentation fixed only. Mechanical diff: `rt_coherent_consistent_large_K` is the frozen
  `rt_coherent_consistent` at `(Π_K#P, Π_K#Q, Π_K#μ, FK K)` with `0 < 𝓔_K` ↦ the `thm:rt-coherent` hypotheses and
  `P ≠ Q`, under `∃ K₁, ∀ K ≥ K₁` placed before the sample, grids and `α`; `rt_coherent_eventually_pos` is the frozen
  wave-22a `rt_coherent_eventually` with `S_Λ(K) → 0`, `𝓔_∞ > 0` and the everywhere bounds ↦ the same hypotheses (in
  the paper's `ℝ^K` form of `𝓔_K`), concluding also `0 < 𝓔_K`; `rt_lift_sep_density` is the frozen `rt_lift_sep` with
  `t ↦ popTail θ P Q q` and `SK`, `InjOn` ↦ Brenier head map, tail densities, `q_j` strictly increasing; the `_H`
  energy claims are the frozen `ed_*` with `FiniteDimensional` ↦ second countability (and completeness). Objects are
  the imported frozen ones plus `popTail`. Junk: every `energyD` is of laws with first moments (assumed, or carried by
  `B̄(0, M)` since `g#Λ = μ`, `F_K#Λ_K = μ_K` and `P, Q ≤ Λ/θ_*`; the lift by the integrability premise); every
  `Measure.map` is of a measurable map; events are closed-ball complements or preimages of open sets; `cdf` is of a
  probability measure; `S_Λ` is a lower integral. Not tautological (the `⇐` of each iff is the content; the `⇒` is
  `𝒟(ν, ν) = 0`). Nonvacuity: `H = ℓ²`, `P = N(0, C)`, `Q = N(m, C)` (`C` injective trace class, `m ≠ 0`), `μ` the
  cubic law (`lem:app-references-Pl`), `g`, `F_K` by Brenier (`Λ_K` a Gaussian mixture, `≪ Leb`); for the lift
  `K = m = 1`, `P = Q` standard Gaussian, `μ_K = Λ_K`, `F_K = Id`, `q_j = id`, `I_j = ℝ`; for `ghs_inverse_H`
  `P = μ = Unif[0, 1]` on `ℝ`, `𝔽 = Id`.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL5

open StatFormal.OTFD.WaveL2 (FixedKSetting critVal rankEnergy pool)
open StatFormal.OTFD.Wave22a (mix energyD IsConvGradAE headT liftMap)
open StatFormal.OTFD.WaveL1 (IsCMMapAE LipNull Mom2 Euc)
open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.OTFD.Ranks (IsMin)

/-- The population tail map `t_j = q_j ∘ G_{Λ,j}`: the reference quantile `q_j` after the distribution function of
the `j`-th tail marginal of `Λ = θP + (1−θ)Q`. -/
def popTail {K m : ℕ} (θ : ℝ) (P Q : Measure (EuclideanSpace ℝ (Fin K ⊕ Fin m))) (q : Fin m → ℝ → ℝ) (j : Fin m) :
    ℝ → ℝ :=
  q j ∘ cdf ((mix θ P Q).map fun x => x (Sum.inr j))

namespace Claims

/-! #### Energy distance in a separable Hilbert space -/

/-- `𝒟(ν, ν') ≥ 0` for laws with finite first moments on a separable real inner product space. -/
def ed_nonneg_H : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] (ν ν' : Measure H) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'],
    Integrable id ν → Integrable id ν' → 0 ≤ energyD ν ν'

/-- `𝒟(ν, ν') = 0` only for equal laws (finite first moments, separable real Hilbert space; Lyons 2013). -/
def ed_eq_zero_iff_H : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (ν ν' : Measure H) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'],
    Integrable id ν → Integrable id ν' → (energyD ν ν' = 0 ↔ ν = ν')

/-! #### GHS Lemma 4.3: the a.e. inverse of the Hilbert rank map -/

/-- `P, μ` null on Lipschitz hypersurfaces with finite second moments, `𝔽` Borel, `P`-a.e. cyclically monotone,
`𝔽#P = μ` ⇒ there is a Borel `𝕢`, `μ`-a.e. cyclically monotone, with `𝕢#μ = P`, `𝕢 ∘ 𝔽 = Id` `P`-a.e. and
`𝔽 ∘ 𝕢 = Id` `μ`-a.e. -/
def ghs_inverse_H : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : Measure H) [IsProbabilityMeasure P] [IsProbabilityMeasure μ] (F : H → H),
    LipNull P → Mom2 P ≠ ∞ → LipNull μ → Mom2 μ ≠ ∞ →
    Measurable F → P.map F = μ → IsCMMapAE P F →
      ∃ G : H → H, Measurable G ∧ μ.map G = P ∧ IsCMMapAE μ G ∧
        (∀ᵐ x ∂P, G (F x) = x) ∧ ∀ᵐ u ∂μ, F (G u) = u

/-! #### `thm:rt-coherent` -/

/-- `𝓔_∞(P, Q) = 𝒟_H(𝔽_Λ#P, 𝔽_Λ#Q) > 0` iff `P ≠ Q`, for `P, Q ∈ 𝒫^ℓ(H)` and a boundedly supported reference
`μ ∈ 𝒫^ℓ(H)`. -/
def rt_coherent_Einf_pos : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P Q μ : Measure H) [IsProbabilityMeasure μ] (θ M : ℝ) (g : H → H),
    0 < θ → θ < 1 → PellClass P → PellClass Q → LipNull μ → μ (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable g → (mix θ P Q).map g = μ → IsCMMapAE (mix θ P Q) g →
      (0 < energyD (P.map g) (Q.map g) ↔ P ≠ Q)

/-- `prop:integrated-sieve-strong` applied to `Λ`: `S_Λ(K)² = ∫ ‖ι_K F^Λ_K Π_K x − 𝔽_Λ x‖² dΛ → 0` for a coherent
boundedly supported reference (`μ_K = Π_K#μ`) and a complete orthonormal basis. -/
def rt_coherent_sieve_limit : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P Q μ : Measure H) [IsProbabilityMeasure μ] (θ M : ℝ) (g : H → H)
    (FK : (K : ℕ) → Euc K → Euc K),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    0 < θ → θ < 1 → PellClass P → PellClass Q → μ (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable g → (mix θ P Q).map g = μ → IsCMMapAE (mix θ P Q) g →
    (∀ K, Measurable (FK K)) → (∀ K, ((mix θ P Q).map (truncK e K)).map (FK K) = μ.map (truncK e K)) →
    (∀ K, IsCMMapAE ((mix θ P Q).map (truncK e K)) (FK K)) →
      Tendsto (fun K => ∫⁻ x, ‖embed e K (FK K (truncK e K x)) - g x‖ₑ ^ 2 ∂(mix θ P Q)) atTop (𝓝 0)

/-- "Hence there is `K_1` with `𝓔_K ≥ 𝓔_∞/2` for `K ≥ K_1`", with `S_Λ(K) → 0` and `𝓔_∞ > 0` derived: for
`P ≠ Q`, eventually `𝓔_∞/2 ≤ 𝓔_K = 𝒟(F_K#P_K, F_K#Q_K)` and `𝓔_K > 0`. -/
def rt_coherent_eventually_pos : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P Q μ : Measure H) [IsProbabilityMeasure μ] (θ M : ℝ) (g : H → H)
    (FK : (K : ℕ) → Euc K → Euc K),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    0 < θ → θ < 1 → PellClass P → PellClass Q → LipNull μ → μ (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable g → (mix θ P Q).map g = μ → IsCMMapAE (mix θ P Q) g →
    (∀ K, Measurable (FK K)) → (∀ K, ((mix θ P Q).map (truncK e K)).map (FK K) = μ.map (truncK e K)) →
    (∀ K, IsCMMapAE ((mix θ P Q).map (truncK e K)) (FK K)) → P ≠ Q →
      ∀ᶠ K in atTop,
        energyD (P.map g) (Q.map g) / 2 ≤
            energyD ((P.map (truncK e K)).map (FK K)) ((Q.map (truncK e K)).map (FK K)) ∧
          0 < energyD ((P.map (truncK e K)).map (FK K)) ((Q.map (truncK e K)).map (FK K))

/-- `thm:rt-coherent`, last clause: for `P ≠ Q` there is `K₁` such that every fixed-`K` rank-energy test with
`K ≥ K₁` (any grids and measurable selection of optimal assignments satisfying the fixed-`K` setting for
`(Π_K#P, Π_K#Q, Π_K#μ, F_K)`) is consistent: the frozen `rt_coherent_consistent` without its premise `0 < 𝓔_K`. -/
def rt_coherent_consistent_large_K : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P Q μ : Measure H) [IsProbabilityMeasure μ] (θ M : ℝ) (g : H → H)
    (FK : (K : ℕ) → Euc K → Euc K),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    0 < θ → θ < 1 → PellClass P → PellClass Q → LipNull μ → μ (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable g → (mix θ P Q).map g = μ → IsCMMapAE (mix θ P Q) g →
    (∀ K, Measurable (FK K)) → (∀ K, ((mix θ P Q).map (truncK e K)).map (FK K) = μ.map (truncK e K)) →
    (∀ K, IsCMMapAE ((mix θ P Q).map (truncK e K)) (FK K)) → P ≠ Q →
      ∃ K₁ : ℕ, ∀ K, K₁ ≤ K →
        ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (R : ℝ)
          (Z W : ℕ → Ω → Euc K) (n₁ n₂ : ℕ → ℕ) (u : ∀ ν, Fin (n₁ ν + n₂ ν) → Euc K)
          (sel : ∀ ν, (Fin (n₁ ν + n₂ ν) → Euc K) → Equiv.Perm (Fin (n₁ ν + n₂ ν))) (α : ℝ),
          FixedKSetting K Pr (P.map (truncK e K)) (Q.map (truncK e K)) (μ.map (truncK e K)) θ R (FK K)
            Z W n₁ n₂ u →
          0 < α → α < 1 → (∀ ν z, IsMin (u ν) z (sel ν z)) → (∀ ν h, MeasurableSet {z | sel ν z = h}) →
            (∀ ν, MeasurableSet {ω | critVal (rankEnergy (n₁ ν) (n₂ ν)) (u ν) α <
              rankEnergy (n₁ ν) (n₂ ν) (u ν ∘ ⇑(sel ν (pool (n₁ ν) (n₂ ν) Z W ω)))}) ∧
            Tendsto (fun ν => Pr {ω | critVal (rankEnergy (n₁ ν) (n₂ ν)) (u ν) α <
              rankEnergy (n₁ ν) (n₂ ν) (u ν ∘ ⇑(sel ν (pool (n₁ ν) (n₂ ν) Z W ω)))}) atTop (𝓝 1)

/-! #### `prop:rt-lift` (ii) -/

/-- `prop:rt-lift`(ii) with the injectivity of the lift derived: head map the Brenier map between `Λ_K ≪ Leb` and
`μ_K ≪ Leb`, tail maps the population tail maps `q_j ∘ G_{Λ,j}` (`q_j` strictly increasing on `(0, 1)`, the `j`-th
tail marginal of `Λ` with a density positive on an open interval `I_j` carrying it); then, for integrable lifted
maps, the lifted rank laws have positive energy distance iff `P_T ≠ Q_T`, whatever `K`. -/
def rt_lift_sep_density : Prop :=
  ∀ (K m : ℕ) (P Q : Measure (EuclideanSpace ℝ (Fin K ⊕ Fin m))) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (θ : ℝ) (FK : Euc K → Euc K) (μK : Measure (Euc K)) [IsProbabilityMeasure μK] (q : Fin m → ℝ → ℝ)
    (f : Fin m → ℝ → ℝ≥0∞) (I : Fin m → Set ℝ),
    0 < θ → θ < 1 → Measurable FK →
    MemLp id 2 ((mix θ P Q).map headT) → MemLp id 2 μK → (mix θ P Q).map headT ≪ volume → μK ≪ volume →
    ((mix θ P Q).map headT).map FK = μK → IsConvGradAE ((mix θ P Q).map headT) FK →
    (∀ j, Measurable (q j)) → (∀ j, StrictMonoOn (q j) (Ioo 0 1)) →
    (∀ j, Measurable (f j)) → (∀ j, (mix θ P Q).map (fun x => x (Sum.inr j)) = volume.withDensity (f j)) →
    (∀ j, IsOpen (I j)) → (∀ j, (I j).OrdConnected) → (∀ j, ∀ x ∈ I j, 0 < f j x) →
    (∀ j, mix θ P Q {x | x (Sum.inr j) ∉ I j} = 0) →
    Integrable (liftMap FK (popTail θ P Q q)) P → Integrable (liftMap FK (popTail θ P Q q)) Q →
      (0 < energyD (P.map (liftMap FK (popTail θ P Q q))) (Q.map (liftMap FK (popTail θ P Q q))) ↔ P ≠ Q)

end Claims

end StatFormal.OTFD.WaveL5
