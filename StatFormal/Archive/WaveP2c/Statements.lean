import StatFormal.Archive.Wave11a.Statements
import StatFormal.Archive.Wave14a.Statements
import StatFormal.Archive.Wave25a.Statements
import StatFormal.Archive.Wave21a.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave P2c (partial-audit wave 2d, REO medium): robust equality JASA `thm:ghost` (general clause),
# `cor:dominated` (i) unconditional, `thm:ep-cert0` (ii), `prop:ad-population` (probability statement), `prop:tax` (b)
# (smooth class) and (c) unconditional

Sources (current text of `robust-equality-outcomes-under-distribution-shift/jasa/`, read 2026-10-16; JASA
`prop:ad-population` as corrected 2026-10-16, DEFECTS #90 applied):
* `thm:ghost` (`main.tex:465-472`, proof `supp_proofs.tex:454-472`); `cor:dominated` (`supp_proofs.tex:495-510`).
* `thm:ep-cert0` (`supp_eps.tex:64-97`, proof (ii) `:105-113`), `def:ep-member` (`:40-55`).
* `prop:ad-population` (`supp_calibration.tex:365-373`, proof `:374-388`), with `def:ad-rho`, `thm:ad-oracle`,
  `lem:ad-linear`, `prop:ad-identity`.
* `prop:tax` (`supp_proofs.tex:633-643`, proof (b) `:650-654`), `H_J` (`:628-631`), `𝒩_b = {(G_b ∗ m)|_K : m ∈ 𝒫(K)}`
  (`supp_proofs.tex:342`).
Frozen objects reused (imported, not copied): Wave 11a `GhostAt`/`GhostGeneral`, `aN`, `FinSupp`, `defMix`,
`freeClass`, `dom_valid`; RobustEquality `Tax` (`ballN`, `tax`), `SemidualStrong` (`OTdisc`, `Setting`, `Jdual`);
Wave 14a `T0`, `lagr`; Wave 9a `FW`, `rhoN`; Wave 21b `GridCond`, `geomGrid`, `rThr`; Wave 15a `omegaMod`; Wave 21a
`boxU`, `varkappa`, `tax_c`. New definitions: `kerValue`, `kerCost`, `Feasible0`, `twoPoint` (ep-cert0); `boxLaw`,
`boxSet`, `boxMix`, `gaussProd`, `smoothClass` (tax).

Covered:
* `ghost_general`: the frozen `GhostGeneral` (general clause of `thm:ghost` in every setting), unfolded (`Iff.rfl`
  with `GhostGeneral`, checked in `Proofs.lean`). A DISCHARGE, not a restatement: `GhostGeneral` is a frozen definition,
  never a target, entered only as a sufficient condition for the `GhostAt` premise of the frozen `dom_valid`; the route
  also proves `GhostGeneral` itself (`ghostGeneral_holds`).
* `dom_valid_uncond`: the frozen `dom_valid` with its `GhostAt` premise deleted (mechanical diff: one line).
* `ep_cert0_ii`: `inf_{λ≥0} T⁰(λ)` (attained) `= sup` over feasible kernels (attained), attained by a Markov kernel with
  at most two atoms per anchor. SPECIALISATION: `P̂` is an empirical centre `n⁻¹Σδ_{x_i}` (ties allowed, so rational
  weights), not an arbitrary finitely supported `Σ a_i δ_{x_i}`; this is the case the certificate is used for.
* `ad_population`: the probability statement with the paper's constants `L' = L + log 2 + (k−1) log(1+2Wm)`, `5.4 b̄ s₄`,
  `4/m`, probability `≥ 1 − e^{−L}`, under the printed hypotheses only (no regularity of `H`).
* `tax_b_smooth`: (b) for the smooth class with bandwidths `b_k`; `tax_c_smooth`: (c) with the (b)-hypothesis of the
  frozen `tax_c` discharged. SPECIALISATION: a finitely supported recording law (finitely many boxes), not a general
  `P^rec`; the rounding-box data have finitely many recorded values in the compact `K`.

Not covered (declared):
* `prop:tax`(b), resolution class `τ_{𝒩^res_β}(P) ≤ dϰ(β)`: the printed class mixes `N(y', β²S(y')²)` over mixing points
  `y' ∈ K`, but `S` is defined only at recorded values. Under the natural extension (`S(y')` = side lengths of the box
  whose interior contains `y'`, interiors disjoint) the bound holds: mixing laws on the open boxes approach `ϰ(β)`
  (the per-box KL is continuous under shrinking the mixing law into the interior), so "every term is `ϰ(β)`" holds up to
  an arbitrary `δ > 0`; under an arbitrary extension it is unsupported. Imprecise, not formalised. With a constant `S` it
  is `tax_b_smooth` at `b = βs`.
* `thm:classcoverage` (TAXB): the jitter step (jittered held-out points i.i.d. `P_s` under `H_J`) needs the sampling model,
  and the membership step needs attainment of the tax for `𝒩_b` (weak compactness, Prokhorov + lsc of `KL`); the tax
  events `T_s` are now supplied by `tax_c_smooth`. Not discharged.
* `prop:ad-population`: the "Hence" corollary and the median lower bound (`thm:ad-lower`, frozen elsewhere).
* `thm:ghost`: "independent randomisation in `r̂` changes nothing" (`r̂` is a measurable function of the sample).

Encodings (to be checked by the critic):
* ghost: as the frozen `GhostAt` (labelled centre `n⁻¹Σδ_{x_i}`, bounded jointly measurable cost, finite references,
  outer-measure validity hypothesis, measurable-event conclusion).
* ep-cert0: anchors labelled (`P̂ = centre x`, ties allowed); any metric space `𝒦` with Borel σ-algebra; `S` a compact
  nonempty set (`S_ν` for a measure on compact `K`); `c = dist²`; kernels `Γ : Fin n → Measure 𝒦` (probability, `Γ_i(Sᶜ) = 0`,
  `n⁻¹Σ_i ∫ dist(y,x_i)² dΓ_i ≤ r`, value `n⁻¹Σ_i ∫ (h y − h x_i)² dΓ_i`: integrands bounded on `S`, no junk); the inf is
  `IsLeast` of `T⁰ '' [0, ∞)`, the sup `IsGreatest`; `R₀ = n⁻¹ Σ infDist(x_i, S)²` (`S ≠ ∅`, so `infDist` is genuine); the
  two-point kernel is `θ(x₀)δ_{u(x₀)} + (1 − θ(x₀))δ_{v(x₀)}`, a function of the anchor point (a Markov kernel).
* ad-population: as the frozen `ad_population_core`; `W` any bound of all `c_i − c_j` (the paper's max is one), `b̄` any
  bound of `H(f) − g_f` on `F_W × K`; no regularity of `H` (the paper's proof uses "`H` is 1-Lipschitz", which the
  proposition does not assume; the route avoids it); the grid condition is a property of the sample, so the event `E` carries
  "grid ⇒ bound".
* tax: `ℝ^d = Fin d → ℝ` (product σ-algebra = Borel); the recording law is finitely supported, `P^rec = Σ_{y∈Y} p_y δ_y`
  (recorded values on the lattice in compact `K`); `U_{B(y)} = ⊗_k (boxU ∘ (u ↦ y_k + s_k(y)u)⁻¹)`, `B(y) ⊆ K`;
  `G_b = ⊗_k N(0, b_k²)`; `𝒩_b` with mixing laws `m ∈ 𝒫(ℝ^d)`, `m(Kᶜ) = 0`; `ϰ` is the frozen `EReal` `varkappa`, finite and
  `≥ 0` for positive arguments (certified `tax_a_bound`), so `toReal` is exact; in (c) the recorded sample lives on the
  lattice (`{y // y ∈ Y}`), `g = Σ_k ϰ(b_k/s_k(·))`, range hypothesis over the lattice.

Critic notes:
* `thm:ghost` holds as printed in every setting of `GhostGeneral` (any measurable `K` with measurable singletons, any
  finite references); the route needs no weak topology: resampling from the ghost law `empOn Y` (`Y ∈ K^{n+m}`),
  the birthday bound and permutation invariance give `P[r̂(Y_{1:n}) < OT(Ŷ_{1:n}, empOn Y) + εa] ≤ α + n²/(n+m)`, and one
  shared semi-dual potential plus the held-out Hoeffding bound give `OT(x̂,P) ≤ OT(x̂, empOn Y) + nB_c/(n+m) +
  B_c√(log(1/δ)/(2m))` outside probability `δ`. The paper's step "weak continuity of `OT_ε(P̂,·)`" (uncertified
  `lem:semidual`(iv)) is not needed.
* `thm:ep-cert0`(ii) holds on any metric space; the route avoids Danskin: limits of maximisers at `λ_k ↓ λ*` (`↑ λ*`) give
  costs `≤ r` (`≥ r`), and the mixture with cost exactly `r` attains `T⁰(λ*)`; the attaining kernel uses one `θ` for all
  anchors.
* `prop:ad-population`: constants confirmed (`√(20/19) + 4 + 1/3 ≤ 5.4`, net `(1+2Wm)^{k−1}`, `2|net|e^{−L'} = e^{−L}`,
  transfer `2/m + 2/m`); the Maurer–Pontil step is the UPPER tail of `sd_{P̂_m}` (second half of MP Thm 10), proved
  here (`RouteMPUpper`), the library having only the lower tail. Paper notes: (1) the proof's "`H` is 1-Lipschitz" is
  not a hypothesis (`def:ad-rho` allows any certified bound, e.g. adaptive branch and bound; it holds for
  `H = sup_K g_f` and fixed-cell bounds) but is not needed: transfer the Bernstein/Maurer–Pontil inequalities themselves
  from the net (`sd` is 1-Lipschitz in sup norm), slack `(2 + 2√(2s₄))/m ≤ 4/m` when `s₄ ≤ 1/2`, and `ρ̂_N − Θ ≤ b̄ ≤
  5.4 b̄ s₄` when `s₄ > 1/2`; (2) the "Hence" corollary does not follow from the bound: `4/m` is not
  `O(b̄ log(N/α)/m)` when `b̄ log(N/α)` is small, and `log 2` is not `O(log(N/α))` for `N = 1`, `α → 1` (no
  counterexample found; both sides scale with the cost, `4/m` does not).
* `prop:tax`(b), smooth class, holds as printed; the projection of mixing atoms onto `[−½,½]` (`prop:tax`(a) proof)
  is formalised (Gaussian-convolution density), as are tensorization, scale invariance and joint convexity.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace StatFormal.WaveP2c

open StatFormal.RobustEquality.Tax StatFormal.RobustEquality.SemidualStrong StatFormal.Wave11a

section EpCert0

variable {𝒦 : Type*} [MetricSpace 𝒦] [MeasurableSpace 𝒦]

/-- The value `E_{P̂} E_{Γ_{x₀}} f_h = n⁻¹ Σ_i ∫ (h(y) − h(x_i))² dΓ_i(y)` of a labelled kernel `Γ`. -/
def kerValue {n : ℕ} (x : Fin n → 𝒦) (h : 𝒦 → ℝ) (Γ : Fin n → Measure 𝒦) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, ∫ y, (h y - h (x i)) ^ 2 ∂(Γ i)

/-- The transport cost `E_{P̂} E_{Γ_{x₀}} c = n⁻¹ Σ_i ∫ dist(y, x_i)² dΓ_i(y)` of a labelled kernel `Γ`. -/
def kerCost {n : ℕ} (x : Fin n → 𝒦) (Γ : Fin n → Measure 𝒦) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, ∫ y, dist y (x i) ^ 2 ∂(Γ i)

/-- `Γ` is feasible for the primal of `thm:ep-cert0`(ii): probability kernels carried by `S` with budget `≤ r`. -/
def Feasible0 {n : ℕ} (x : Fin n → 𝒦) (S : Set 𝒦) (r : ℝ) (Γ : Fin n → Measure 𝒦) : Prop :=
  (∀ i, IsProbabilityMeasure (Γ i)) ∧ (∀ i, Γ i Sᶜ = 0) ∧ kerCost x Γ ≤ r

/-- The Markov kernel `x₀ ↦ θ(x₀) δ_{u(x₀)} + (1 − θ(x₀)) δ_{v(x₀)}` read at the labelled anchors. -/
def twoPoint {n : ℕ} (θ : 𝒦 → ℝ) (u v : 𝒦 → 𝒦) (x : Fin n → 𝒦) : Fin n → Measure 𝒦 :=
  fun i => ENNReal.ofReal (θ (x i)) • Measure.dirac (u (x i)) + ENNReal.ofReal (1 - θ (x i)) • Measure.dirac (v (x i))

end EpCert0

section TaxB

variable {d : ℕ}

/-- The uniform law on the box `B(y) = ∏_k [y_k − σ_k/2, y_k + σ_k/2]`: `⊗_k` of `U[−½,½]` pushed by `u ↦ y_k + σ_k u`. -/
def boxLaw (y σ : Fin d → ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun k => StatFormal.Wave21a.boxU.map fun u => y k + σ k * u

/-- The box `B(y) = ∏_k [y_k − σ_k/2, y_k + σ_k/2]`. -/
def boxSet (y σ : Fin d → ℝ) : Set (Fin d → ℝ) := Set.pi Set.univ fun k => Set.Icc (y k - σ k / 2) (y k + σ k / 2)

/-- The population of the recording hypothesis `H_J` with a finitely supported recording law `Σ_{y∈Y} p_y δ_y`
(recorded values on a lattice in the compact `K`) and side lengths `s(y)`: `P = Σ_y p_y U_{B(y)}`. -/
def boxMix (Y : Finset (Fin d → ℝ)) (p : (Fin d → ℝ) → ℝ) (s : (Fin d → ℝ) → Fin d → ℝ) : Measure (Fin d → ℝ) :=
  ∑ y ∈ Y, ENNReal.ofReal (p y) • boxLaw y (s y)

/-- `G_b = N(0, diag(b_k²))` on `ℝ^d`. -/
def gaussProd (b : Fin d → ℝ) : Measure (Fin d → ℝ) := Measure.pi fun k => gaussianReal 0 ((b k) ^ 2).toNNReal

/-- The smooth class with bandwidths `b_k` along the coordinates, `𝒩_b = {(G_b ∗ m)|_K : m ∈ 𝒫(K)}`. -/
def smoothClass (b : Fin d → ℝ) (K : Set (Fin d → ℝ)) : Set (Measure (Fin d → ℝ)) :=
  {ν | ∃ m : Measure (Fin d → ℝ), IsProbabilityMeasure m ∧ m Kᶜ = 0 ∧ ν = (gaussProd b ∗ m).restrict K}

end TaxB

namespace Claims

/-! ### JASA `thm:ghost`, general clause -/

/-- **`thm:ghost`, general clause** (the frozen Wave 11a `GhostGeneral`, unfolded): if a measurable radius `r̂` covers
every finitely supported population at level `1 − α`, then for every population `P`,
`Pr_P[r̂ ≥ OT_ε(P̂, P) + ε a_𝒩] ≥ 1 − α` (measurable-event convention). -/
def ghost_general : Prop :=
  ∀ (K : Type) [MeasurableSpace K] [MeasurableSingletonClass K] (n : ℕ) (ε α : ℝ) (cost : K → K → ℝ)
    (𝒩 : Set (Measure K)) (r : (Fin n → K) → EReal),
    0 < n → 0 < ε → Measurable (Function.uncurry cost) → (∃ B, ∀ x0 y, |cost x0 y| ≤ B) →
    (∀ ν ∈ 𝒩, IsFiniteMeasure ν) → Measurable r →
    (∀ Q : Measure K, IsProbabilityMeasure Q → FinSupp Q →
      ENNReal.ofReal (1 - α) ≤ (Measure.pi fun _ : Fin n => Q)
        {x | Q ∈ ballN 𝒩 ε (fun _ => (1 : ℝ) / n) (fun i => cost (x i)) (r x)}) →
    ∀ P : Measure K, IsProbabilityMeasure P →
      ∃ E : Set (Fin n → K), MeasurableSet E ∧
        E ⊆ {x | OTdisc ε (fun _ => (1 : ℝ) / n) (fun i => cost (x i)) P + (ε : EReal) * aN 𝒩 ≤ r x} ∧
        ENNReal.ofReal (1 - α) ≤ (Measure.pi fun _ : Fin n => P) E

/-! ### JASA `cor:dominated` (i), unconditional -/

/-- **`cor:dominated` (i)** (the frozen Wave 11a `dom_valid` with its `GhostAt` premise removed): a radius valid for
`𝒩_κ` over the finitely supported laws, minus `ε log(1/κ)`, is a valid radius for the free class at every population. -/
def dom_valid_uncond : Prop :=
  ∀ (K : Type) [MeasurableSpace K] [MeasurableSingletonClass K] (n : ℕ) (ε α κ : ℝ) (cost : K → K → ℝ)
    (ν₀ : Measure K) [IsFiniteMeasure ν₀] (r : (Fin n → K) → EReal),
    0 < n → 0 < ε → 0 < κ → κ ≤ 1 → ν₀ Set.univ ≤ 1 → (∀ y, ν₀ {y} = 0) →
    Measurable (Function.uncurry cost) → (∃ B, ∀ x0 y, |cost x0 y| ≤ B) → Measurable r →
    (∀ Q : Measure K, IsProbabilityMeasure Q → FinSupp Q →
      ENNReal.ofReal (1 - α) ≤ (Measure.pi fun _ : Fin n => Q)
        {x | Q ∈ ballN (defMix ν₀ κ) ε (fun _ => (1 : ℝ) / n) (fun i => cost (x i)) (r x)}) →
    ∀ P : Measure K, IsProbabilityMeasure P →
      ∃ E : Set (Fin n → K), MeasurableSet E ∧
        E ⊆ {x | P ∈ ballN freeClass ε (fun _ => (1 : ℝ) / n) (fun i => cost (x i))
          (r x - ((ε * Real.log (1 / κ) : ℝ) : EReal))} ∧
        ENNReal.ofReal (1 - α) ≤ (Measure.pi fun _ : Fin n => P) E

/-! ### JASA `thm:ep-cert0` (ii) -/

/-- **`thm:ep-cert0` (ii)**: for a finitely supported centre (labelled anchors), a compact support `S ≠ ∅`, a
continuous `h` and `r > R₀ = n⁻¹ Σ_i dist²(x_i, S)`, `inf_{λ≥0} T⁰(λ)` (attained) equals the supremum of
`E_{P̂} E_Γ f_h` over the kernels carried by `S` with `E_{P̂} E_Γ c ≤ r` (attained), and it is attained by a Markov
kernel charging at most two points per anchor. -/
def ep_cert0_ii : Prop :=
  ∀ (𝒦 : Type) [MetricSpace 𝒦] [MeasurableSpace 𝒦] [BorelSpace 𝒦] (n : ℕ) (x : Fin n → 𝒦) (S : Set 𝒦)
    (h : 𝒦 → ℝ) (r : ℝ),
    0 < n → IsCompact S → S.Nonempty → Continuous h → (n : ℝ)⁻¹ * ∑ i, Metric.infDist (x i) S ^ 2 < r →
      ∃ V : ℝ, IsLeast (StatFormal.Wave14a.T0 x S h r '' Set.Ici 0) V ∧
        IsGreatest {w | ∃ Γ : Fin n → Measure 𝒦, Feasible0 x S r Γ ∧ w = kerValue x h Γ} V ∧
        ∃ (θ : 𝒦 → ℝ) (u v : 𝒦 → 𝒦), (∀ i, 0 ≤ θ (x i) ∧ θ (x i) ≤ 1 ∧ u (x i) ∈ S ∧ v (x i) ∈ S) ∧
          Feasible0 x S r (twoPoint θ u v x) ∧ kerValue x h (twoPoint θ u v x) = V

/-! ### JASA `prop:ad-population`, the probability statement -/

open StatFormal.RobustEquality.Semidual (gsoft) in
open StatFormal.Wave9a (FW rhoN) in
open StatFormal.Wave21b (GridCond geomGrid rThr) in
open StatFormal.Wave15a (omegaMod) in
/-- **`prop:ad-population`** (the probability statement; the frozen Wave 25a `ad_population_core` is its deterministic
core on the event): `W` bounds every `c_i − c_j`, `b̄` bounds `H(f) − g_f` on `F_W × K` and `H(f) ≥ sup_K g_f` (no
regularity of `H`); `L' = L + log 2 + (k − 1) log(1 + 2Wm)`, `s = γr`, `s₄ = (√s + √(L'/m))²`, `m ≥ 20`.
Then there is a measurable event of `P^m`-probability at least `1 − e^{−L}` on which, whenever the grid condition holds
for every `f ∈ F_W`, `ρ̂_N − Θ(P) ≤ ω_P(s₄) + 5.4 b̄ s₄ + 4/m`. -/
def ad_population : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k m N : ℕ) (ε α γ bbar W L : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (H : (Fin k → ℝ) → ℝ) (P : Measure K) [IsProbabilityMeasure P],
    Setting ε a c → 20 ≤ m → 0 < N → 0 < α → α < 1 → 1 < γ → 0 < L →
    (∀ i j y, c i y - c j y ≤ W) →
    (∀ f ∈ FW c, ∀ z, gsoft ε a f c z ≤ H f) → (∀ f ∈ FW c, ∀ z, H f - gsoft ε a f c z ≤ bbar) →
      ∃ E : Set (Fin m → K), MeasurableSet E ∧
        ENNReal.ofReal (1 - Real.exp (-L)) ≤ (Measure.pi fun _ : Fin m => P) E ∧
        ∀ y ∈ E, (∀ f ∈ FW c, GridCond N α γ (H f) (gsoft ε a f c) y) →
          rhoN ε α a c H (geomGrid γ N) y - OTdisc ε a c P ≤
            omegaMod ε a c P ((√(γ * rThr N m α) +
                √((L + Real.log 2 + ((k : ℝ) - 1) * Real.log (1 + 2 * W * m)) / m)) ^ 2) +
              ((5.4 * bbar * (√(γ * rThr N m α) +
                √((L + Real.log 2 + ((k : ℝ) - 1) * Real.log (1 + 2 * W * m)) / m)) ^ 2 + 4 / m : ℝ) : EReal)

/-! ### JASA `prop:tax` (b), the smooth class -/

/-- **`prop:tax` (b), smooth class**: under `H_J` with a finitely supported recording law and boxes `B(y) ⊆ K`,
`τ_{𝒩_b}(P) ≤ E_{y∼P^rec} Σ_k ϰ(b_k/s_k(y))` (`ϰ` the frozen Wave 21a `varkappa`, finite for positive arguments by the
certified `tax_a_bound`, so `toReal` is exact). -/
def tax_b_smooth : Prop :=
  ∀ (d : ℕ) (Y : Finset (Fin d → ℝ)) (p : (Fin d → ℝ) → ℝ) (s : (Fin d → ℝ) → Fin d → ℝ) (b : Fin d → ℝ)
    (K : Set (Fin d → ℝ)),
    (∀ y ∈ Y, 0 ≤ p y) → ∑ y ∈ Y, p y = 1 → (∀ y ∈ Y, ∀ k, 0 < s y k) → (∀ k, 0 < b k) → MeasurableSet K →
    (∀ y ∈ Y, boxSet y (s y) ⊆ K) →
      tax (smoothClass b K) (boxMix Y p s) ≤
        ((∑ y ∈ Y, p y * ∑ k, (StatFormal.Wave21a.varkappa (b k / s y k)).toReal : ℝ) : EReal)

/-- **`prop:tax` (c), with (b) discharged** (the frozen Wave 21a `tax_c` at `g(y) = Σ_k ϰ(b_k/s_k(y))`, its
hypothesis `τ_𝒩(P) ≤ E_{P^rec} g` supplied by `tax_b_smooth`): `n` i.i.d. recorded values from the recording law on
the lattice `Y`, an a priori range `[g₋, g₊]` of `g` over `Y`, then with probability `≥ 1 − a`,
`τ_{𝒩_b}(P) ≤ ḡ + (g₊ − g₋)√(log(1/a)/(2n))`. -/
def tax_c_smooth : Prop :=
  ∀ (d : ℕ) (Y : Finset (Fin d → ℝ)) (p : (Fin d → ℝ) → ℝ) (s : (Fin d → ℝ) → Fin d → ℝ) (b : Fin d → ℝ)
    (K : Set (Fin d → ℝ)) (gm gp a : ℝ) (n : ℕ),
    (∀ y ∈ Y, 0 ≤ p y) → ∑ y ∈ Y, p y = 1 → (∀ y ∈ Y, ∀ k, 0 < s y k) → (∀ k, 0 < b k) → MeasurableSet K →
    (∀ y ∈ Y, boxSet y (s y) ⊆ K) → 0 < n → 0 < a → a ≤ 1 →
    (∀ y ∈ Y, gm ≤ ∑ k, (StatFormal.Wave21a.varkappa (b k / s y k)).toReal ∧
      ∑ k, (StatFormal.Wave21a.varkappa (b k / s y k)).toReal ≤ gp) →
      ∃ E : Set (Fin n → {y // y ∈ Y}), MeasurableSet E ∧
        ENNReal.ofReal (1 - a) ≤ Measure.pi (fun _ : Fin n =>
          ∑ i : {y // y ∈ Y}, ENNReal.ofReal (p i) • Measure.dirac i) E ∧
        E ⊆ {w | tax (smoothClass b K) (boxMix Y p s) ≤
          (((1 / (n : ℝ)) * ∑ j, ∑ k, (StatFormal.Wave21a.varkappa (b k / s (w j) k)).toReal +
            (gp - gm) * √(Real.log (1 / a) / (2 * n)) : ℝ) : EReal)}

end Claims
end StatFormal.WaveP2c
