import StatFormal.Lib.Distances.TV
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# FROZEN STATEMENTS — wave 10b (QUEUE rows 90–92): otfd C `thm:cond-cal-impossible`,
# C `prop:coordinate-obstruction`; robust equality JASA `prop:cs-void`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-C_conditional.md`,
`robust-equality-jasa.md`; current text after the 2026-10-14 corrections):
* C `thm:cond-cal-impossible` (`otfd/papers/C_conditional/main.tex:866-886`), proof
  `supplement.tex:1925-1975` (Steps 1–5 and "Sharpness"), with the "Conventions" paragraph
  (`supplement.tex:1896-1908`: internal randomization `ξ` independent of everything, Borel band sets,
  measurable coverage set and band graph at the fixed `t`), `lem:supp-small-cells` (`:1911-1914`) and
  `rem:supp-impossible-scope` (`:1977-1993`: coverage is used only at `t`, in integrated form, for the laws
  `Q^{G,M}`).
* C `prop:coordinate-obstruction` (`supplement.tex:352-389`, proof `:391-447`), with the setting of
  `subsec:supp-coordinate` (`:232-266`: `ν_X`, `P_C` Borel probability laws on `ℝ^q`, `D = supp P_C` compact,
  continuous potentials, the inverse out-of-sample weights `eq:inverse-oos-weights`, second form, and the
  localized law `P^ν_{K,ε,r} = ∫_D P_{K,c} w_ε(c | r) P_C(dc)`) and the Brenier potential (`:268-276`).
* robust equality JASA `prop:cs-void`
  (`robust-equality-outcomes-under-distribution-shift/jasa/supp_common_shift.tex:38-62`, proof `:64-79`),
  with `P_sκ := ∫ κ(x, ·) P_s(dx)` (`:35-36`), `c(x,y) = |x − y|²`, `K` compact (file header).
Reuses the frozen `Foundations/Distances/TV.lean` (`tvDist`, a locked import) and Tau Ceti's `wassersteinEDist`.

Covered:
* `thm:cond-cal-impossible`: `cond_cal_impossible` (for every law `P` and `P_X`-a.e. `x` with `P_X{x} = 0`,
  `P{leb B̂(t | x) = ∞} ≥ 1 − α` and `E leb B̂(t | x) = ∞`), `cond_cal_sharp` ("the constant `1 − α` cannot be
  improved": the randomized all-or-nothing band has conditional coverage exactly `1 − α` under every law, and
  infinite width with probability exactly `1 − α`).
* `prop:coordinate-obstruction`: `coord_select_iff` ((a): unique maximiser of `g_{0,r}` on `D` ⇔ `β_X`
  differentiable at `r`), `coord_select_max` ((a): the maximiser is `T_X(r) = ∇β_X(r) ∈ D`), `coord_select_ae`
  ((a): Lebesgue-a.e. `r`), `coord_concentration` ((b): `δ_a > 0`, `P_C(U_a) > 0`, the bound
  `eq:raw-query-concentration` whenever `‖φ_ε − φ₀‖_{∞,D} ≤ δ_a/4`, and for all small `ε`), `coord_limit` ((c):
  `W₁(P^ν_{K,ε,r}, P_{K,T_X(r)}) → 0`), `coord_raw_query` ((c) at `r = x ∈ D`: the limit is
  `W₁(P_{K,T_X(x)}, P_{K,x})`, positive exactly when `P_{K,T_X(x)} ≠ P_{K,x}`), `coord_forward` ((d), first
  sentence).
* `prop:cs-void`: `cs_void_kernel` ((i): a common Markov kernel reaches every pair `(Q₀, Q₁)`), `cs_void_sup`
  ((i): `sup_κ W₂²(h#P₀κ, h#P₁κ) = (sup_K h − inf_K h)²`), `cs_void_dirac` ((i): the value is the supremum over
  point masses), `cs_void_reweight` ((ii)), `cs_void_pooled` ((iii), as an equality of the two sets of pairs),
  `cs_void_tv` ((iv): `sup_κ W₂²(h#P₀κ, h#P₁κ) = TV(P₀,P₁)(sup_K h − inf_K h)²` for arbitrary `P₀, P₁`).

Not covered (declared):
* `thm:cond-cal-impossible`: the remark after the theorem that the condition on `t` cannot be dropped, and the
  conditional-law form of the hypothesis (only its integrated form, which the proof uses, is stated).
* `prop:coordinate-obstruction`: the pointer to `lem:ref-potential-limit` (L3; the uniform convergence is a
  hypothesis, per the queue note); in (a) "if `ν_X` is absolutely continuous, `T_X` is the Brenier map,
  `T_X#ν_X = P_C`" (Brenier–McCann, cited; needs the optimal plan and the duality attainment); in (d) the
  second sentence (`r_x = ∇β_X^*(x)` exists for `P_C`-a.e. `x` when `ν_X, P_C` are absolutely continuous: needs
  the conjugate `β_X^*`, its a.e. differentiability on `conv D` and the optimal plan). The Example and
  `rem:coordinate-obstruction-quadratic`.
* `prop:cs-void`: the closing sentence on empirical laws (mutual singularity with probability one), which is
  commentary.

Encodings (see card):
* `thm:cond-cal-impossible`: covariates in `ℝ^q = Fin q → ℝ` (Borel). The curve space is any real vector space
  `𝒴` with a σ-algebra and a linear evaluation `ev : 𝒴 →ₗ (𝒯 → ℝ)` (`ev y s = y(s)`; injectivity, i.e. `𝒴` being
  a space *of* functions, is not required — a generalisation); the standing measurability is
  `y ↦ ev y s` measurable for every `s` and `(y,w) ↦ y + w φ` measurable for every `φ`. The procedure is
  `B : (Fin n → ℝ^q × 𝒴) → Ξ → 𝒯 → ℝ^q → Set ℝ` (`BandProc`); the internal randomization is any probability
  space `(Ξ, ν)` (the paper's `Unif(0,1)` is a case; `cond_cal_sharp` uses `Ξ = [0,1]` with Lebesgue measure).
  The Conventions' measurability is two hypotheses: the coverage set `coverSet` and the band graph at `t`
  (`bandGraph`) are measurable. The joint law is `(P^n ⊗ ν) ⊗ P` (`jointLaw`; the new pair is independent of
  the data). Conditional coverage ("`P(Y ∈ B̂(·|X) | X = x) ≥ 1 − α` for `P_X`-a.e. `x`") is stated in its
  integrated form (`CondCoverage`): `(1 − α) P_X(G) ≤ P{X ∈ G, Y ∈ B̂(·|X)}` for every Borel `G` and every law
  `P` (equivalent to the a.e. bound on the conditional expectation given `X`, without conditional laws on the
  curve space; the queue note). `leb` is `volume` on `ℝ` in `ℝ≥0∞` (so `= ∞` is meaningful); `E` is a lower
  integral. Events: `∃` measurable `E ⊆ event` with `(P^n ⊗ ν)(E) ≥ 1 − α`. `cond_cal_sharp` assumes
  `𝒯` nonempty (the theorem fixes `t ∈ 𝒯`; with `𝒯 = ∅` every band covers vacuously and the exact
  coverage `1 − α` fails).
* `prop:coordinate-obstruction`: `ℝ^q = EuclideanSpace ℝ (Fin q)`; `D = supp P_C` compact is `IsCompactSupport`
  (`D` compact, `P_C(Dᶜ) = 0`, every open set meeting `D` has positive mass). The potentials are a family
  `φ : ℝ → ℝ^q → ℝ` (`φ ε = φ_ε`), each continuous on `D`, and `φ₀` continuous on `D` with `φ_ε → φ₀`
  uniformly on `D` as `ε ↓ 0` (`TendstoUniformlyOn … (𝓝[>] 0) D`). Neither the Schrödinger system nor the
  conjugacy/optimality of `(ψ₀, φ₀)` is assumed (a generalisation: the proof uses neither; `ν_X` enters only the
  declared Brenier clause). `β_X(r) = sSup {⟨r,c⟩ − ½(‖c‖² − φ₀(c)) : c ∈ D}` (`brenierPot`, a maximum of a
  continuous function over a nonempty compact set: no junk), `T_X(r) = ∇β_X(r)` (Mathlib `gradient`; used only
  where `β_X` is differentiable). `g_{0,r} = gPot φ₀ r`; `F_a`, `δ_a`, `U_a` are `farSet`, `gapA`, `nearSet`
  (the maxima are `sSup` of images of nonempty compact sets). The weights are the second form of
  `eq:inverse-oos-weights` (`oosWeight`, a ratio with positive denominator `∫_D e^{…} dP_C`); the localized law
  is `((P_C|_D) · w_ε(· | r)).bind κ` (`locLaw`) for a Markov kernel `κ : ℝ^q → ℝ^k` (the version `c ↦ P_{K,c}`).
  "`Z ∈ B̄(0,R)` a.s." is read on the version: `κ c (B̄(0,R)ᶜ) = 0` for `c ∈ D`. `W₁` is Tau Ceti's
  `wassersteinEDist 1` (in `ℝ≥0∞`); "`W₁`-continuous at `c₀` relative to `D`" is
  `Tendsto (c ↦ W₁(κ c, κ c₀)) (𝓝[D] c₀) (𝓝 0)`.
* `prop:cs-void`: `K` is any measurable space (generalising the compact `K`); a common kernel is a Mathlib
  Markov kernel `κ : Kernel K K`, `P_sκ = P_s.bind κ`; `W₂` is Tau Ceti's `wassersteinEDist 2` on `ℝ`, squared;
  `h` measurable and bounded (`BddAbove`/`BddBelow` of the range), `sup_K h − inf_K h = osc h` (`⨆`/`⨅` in `ℝ` of a
  bounded nonempty range: no junk); the suprema over kernels are `⨆` in `ℝ≥0∞`. In (ii) `w` is real, measurable,
  `≥ 0`, with `Q_s = w · P_s` (`withDensity`). In (iii) the cost is any `c : K → K → ℝ≥0∞` (generalising
  `|x − y|²`), `E_{P}E_κ c = ∫⁻∫⁻ c(x,y) κ(x,dy) P(dx)` (`kernelCost`), weights `π₀ + π₁ = 1` and budget `r` in
  `ℝ≥0∞`; the claim is the equality of the set of pairs produced by common kernels under the pooled budget and
  the set of pairs `(P₀κ₀, P₁κ₁)` under the split budget (the printed "produces every pair" is `⊇`; `⊆` is
  trivial). `TV` is `tvDist` (`sup_A |P₀(A) − P₁(A)|`).

Critic notes:
* `thm:cond-cal-impossible` holds as printed (with the Conventions' measurability added to the statement, as
  the queue note asks). The proof follows the supplement except Step 4: instead of the dyadic partition of
  `lem:supp-small-cells` it uses a countable basis of `ℝ^q` (every `x` with `P_X{x} = 0` lies in basis sets of
  arbitrarily small mass), so the lemma is not needed.
* `prop:coordinate-obstruction` (a)–(c) and the first sentence of (d) hold as printed under the frozen
  hypotheses; they use only the continuity of `φ₀, φ_ε` on `D`, the uniform convergence and `D = supp P_C`.
* `prop:cs-void` holds as printed (incl. (iv) added after J5). The lower bound of (iv) uses the two-point
  kernel on an arbitrary measurable `A` (masses differ by `|P₀(A) − P₁(A)|`) and takes the supremum over `A`,
  which is `TV` by definition, so the Hahn set of the printed proof is not needed; (i) is (iv) with `TV = 1`.
* No statement of the three items looks wrong; no counterexample was needed. The only additions are hypotheses
  the text keeps outside the statements (the Conventions' measurability for `thm:cond-cal-impossible`, the
  uniform convergence for `prop:coordinate-obstruction`, as the queue notes ask).
* Proof routes: `Wave10b/Route{CondCal,Coordinate,CsVoid}.lean`, all 15 claims (`Wave10b/Proofs.lean`),
  standard axioms `propext, Classical.choice, Quot.sound` only. (c) uses Tau Ceti's Kantorovich–Rubinstein
  duality `wassersteinEDist_one_eq_iSup`; (iv) uses `Foundations/Distances/W2TV` (maximal coupling).

* Critic (2026-10-14): ACCEPT-WITH-NOTE. `CondCoverage` (integrated over Borel `G'`) is equivalent to the paper's
  conditional-coverage hypothesis; `Nonempty 𝒯` is necessary for the exact sharpness claim. `tvDist` (locked import)
  is `⨆ A measurable, |μ.real A − ν.real A|`, genuine TV. `coordinate-obstruction`: dropping conjugacy is a genuine
  generalisation; "`Z ∈ B̄(0,R)` a.s." is read for every `c ∈ D` — costless for `coord_limit`, `coord_forward`
  (change the version on a null set), but `coord_raw_query` then excludes raw queries in a `P_C`-null set (the
  `∀ᵐ c ∂P_C` form is left for later). `cs_void_dirac` covers the "point masses" parenthetical together with
  `cs_void_kernel`.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory TauCeti Set Filter Topology ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave10b

open StatFormal.Distances

/-! ### C `thm:cond-cal-impossible` -/

section CondCal

/-- A band procedure, possibly randomized, from `n` pairs: `B d ξ s x ⊆ ℝ` is the band at time `s` and
covariate `x` computed from the data `d` and the internal randomization `ξ`. -/
abbrev BandProc (q n : ℕ) (𝒯 𝒴 Ξ : Type) : Type :=
  (Fin n → (Fin q → ℝ) × 𝒴) → Ξ → 𝒯 → (Fin q → ℝ) → Set ℝ

variable {q n : ℕ} {𝒯 𝒴 Ξ : Type}

/-- The coverage set `{(d, ξ, x, y) : y(s) ∈ B̂_{d,ξ}(s | x) for all s}`. -/
def coverSet [AddCommGroup 𝒴] [Module ℝ 𝒴] (ev : 𝒴 →ₗ[ℝ] (𝒯 → ℝ)) (B : BandProc q n 𝒯 𝒴 Ξ) :
    Set (((Fin n → (Fin q → ℝ) × 𝒴) × Ξ) × ((Fin q → ℝ) × 𝒴)) :=
  {z | ∀ s, ev z.2.2 s ∈ B z.1.1 z.1.2 s z.2.1}

/-- The band graph at time `t`: `{(d, ξ, x, v) : v ∈ B̂_{d,ξ}(t | x)}`. -/
def bandGraph (B : BandProc q n 𝒯 𝒴 Ξ) (t : 𝒯) :
    Set ((((Fin n → (Fin q → ℝ) × 𝒴) × Ξ) × (Fin q → ℝ)) × ℝ) :=
  {z | z.2 ∈ B z.1.1.1 z.1.1.2 t z.1.2}

/-- The law of the data `D ~ P^n` and the internal randomization `ξ ~ ν`. -/
def dataLaw [MeasurableSpace 𝒴] [MeasurableSpace Ξ] (n : ℕ) (ν : Measure Ξ)
    (P : Measure ((Fin q → ℝ) × 𝒴)) : Measure ((Fin n → (Fin q → ℝ) × 𝒴) × Ξ) :=
  (Measure.pi fun _ : Fin n => P).prod ν

/-- The joint law of `(D, ξ)` and an independent new pair `(X, Y) ~ P`. -/
def jointLaw [MeasurableSpace 𝒴] [MeasurableSpace Ξ] (n : ℕ) (ν : Measure Ξ)
    (P : Measure ((Fin q → ℝ) × 𝒴)) :
    Measure (((Fin n → (Fin q → ℝ) × 𝒴) × Ξ) × ((Fin q → ℝ) × 𝒴)) :=
  (dataLaw n ν P).prod P

/-- Conditional coverage `P(Y ∈ B̂(· | X) | X) ≥ 1 − α` `P_X`-a.s., for every law `P`, in integrated form:
`(1 − α) P_X(G) ≤ P{X ∈ G, Y ∈ B̂(· | X)}` for every Borel `G`. -/
def CondCoverage [AddCommGroup 𝒴] [Module ℝ 𝒴] [MeasurableSpace 𝒴] [MeasurableSpace Ξ] (α : ℝ)
    (ν : Measure Ξ) (ev : 𝒴 →ₗ[ℝ] (𝒯 → ℝ)) (B : BandProc q n 𝒯 𝒴 Ξ) : Prop :=
  ∀ P : Measure ((Fin q → ℝ) × 𝒴), IsProbabilityMeasure P → ∀ G : Set (Fin q → ℝ), MeasurableSet G →
    ENNReal.ofReal (1 - α) * P.map Prod.fst G ≤
      jointLaw n ν P {z | z.2.1 ∈ G ∧ z ∈ coverSet ev B}

end CondCal

/-! ### C `prop:coordinate-obstruction` -/

section Coordinate

variable {q : ℕ}

/-- `g_{0,r}(c) = φ₀(c) − ‖r − c‖²`. -/
def gPot (φ₀ : EuclideanSpace ℝ (Fin q) → ℝ) (r c : EuclideanSpace ℝ (Fin q)) : ℝ :=
  φ₀ c - ‖r - c‖ ^ 2

/-- The Brenier potential `β_X(r) = max_{c ∈ D} {⟨r,c⟩ − ½(‖c‖² − φ₀(c))}`. -/
def brenierPot (D : Set (EuclideanSpace ℝ (Fin q))) (φ₀ : EuclideanSpace ℝ (Fin q) → ℝ)
    (r : EuclideanSpace ℝ (Fin q)) : ℝ :=
  sSup ((fun c => ⟪r, c⟫_ℝ - (‖c‖ ^ 2 - φ₀ c) / 2) '' D)

/-- The selected covariate `T_X(r) = ∇β_X(r)`. -/
def brenierMap (D : Set (EuclideanSpace ℝ (Fin q))) (φ₀ : EuclideanSpace ℝ (Fin q) → ℝ)
    (r : EuclideanSpace ℝ (Fin q)) : EuclideanSpace ℝ (Fin q) :=
  gradient (brenierPot D φ₀) r

/-- `F_a = {c ∈ D : ‖c − T_X(r)‖ ≥ a}`. -/
def farSet (D : Set (EuclideanSpace ℝ (Fin q))) (φ₀ : EuclideanSpace ℝ (Fin q) → ℝ)
    (r : EuclideanSpace ℝ (Fin q)) (a : ℝ) : Set (EuclideanSpace ℝ (Fin q)) :=
  {c | c ∈ D ∧ a ≤ ‖c - brenierMap D φ₀ r‖}

/-- `δ_a = max_D g_{0,r} − max_{F_a} g_{0,r}`. -/
def gapA (D : Set (EuclideanSpace ℝ (Fin q))) (φ₀ : EuclideanSpace ℝ (Fin q) → ℝ)
    (r : EuclideanSpace ℝ (Fin q)) (a : ℝ) : ℝ :=
  sSup (gPot φ₀ r '' D) - sSup (gPot φ₀ r '' farSet D φ₀ r a)

/-- `U_a = {c ∈ D : g_{0,r}(c) > max_D g_{0,r} − δ_a/4}`. -/
def nearSet (D : Set (EuclideanSpace ℝ (Fin q))) (φ₀ : EuclideanSpace ℝ (Fin q) → ℝ)
    (r : EuclideanSpace ℝ (Fin q)) (a : ℝ) : Set (EuclideanSpace ℝ (Fin q)) :=
  {c | c ∈ D ∧ sSup (gPot φ₀ r '' D) - gapA D φ₀ r a / 4 < gPot φ₀ r c}

/-- The inverse out-of-sample weights, second form of `eq:inverse-oos-weights`:
`w_ε(c | r) = e^{(φ_ε(c) − ‖r−c‖²)/ε} / ∫_D e^{(φ_ε(c') − ‖r−c'‖²)/ε} dP_C(c')`. -/
def oosWeight (PC : Measure (EuclideanSpace ℝ (Fin q))) (D : Set (EuclideanSpace ℝ (Fin q)))
    (φ : EuclideanSpace ℝ (Fin q) → ℝ) (ε : ℝ) (r c : EuclideanSpace ℝ (Fin q)) : ℝ :=
  Real.exp ((φ c - ‖r - c‖ ^ 2) / ε) / ∫ c' in D, Real.exp ((φ c' - ‖r - c'‖ ^ 2) / ε) ∂PC

/-- The localized law `P^ν_{K,ε,r} = ∫_D P_{K,c} w_ε(c | r) P_C(dc)`. -/
def locLaw {k : ℕ} (PC : Measure (EuclideanSpace ℝ (Fin q))) (D : Set (EuclideanSpace ℝ (Fin q)))
    (κ : Kernel (EuclideanSpace ℝ (Fin q)) (EuclideanSpace ℝ (Fin k)))
    (φ : EuclideanSpace ℝ (Fin q) → ℝ) (ε : ℝ) (r : EuclideanSpace ℝ (Fin q)) :
    Measure (EuclideanSpace ℝ (Fin k)) :=
  ((PC.restrict D).withDensity fun c => ENNReal.ofReal (oosWeight PC D φ ε r c)).bind κ

/-- `D = supp P_C`, compact: `P_C(Dᶜ) = 0` and every open set meeting `D` has positive mass. -/
def IsCompactSupport (PC : Measure (EuclideanSpace ℝ (Fin q))) (D : Set (EuclideanSpace ℝ (Fin q))) :
    Prop :=
  IsCompact D ∧ PC Dᶜ = 0 ∧ ∀ c ∈ D, ∀ U : Set (EuclideanSpace ℝ (Fin q)), IsOpen U → c ∈ U → 0 < PC U

end Coordinate

/-! ### JASA `prop:cs-void` -/

section CsVoid

variable {K : Type*} [MeasurableSpace K]

/-- `sup_K h − inf_K h`. -/
def osc (h : K → ℝ) : ℝ := (⨆ x, h x) - ⨅ x, h x

/-- `E_P E_κ c = ∫∫ c(x, y) κ(x, dy) P(dx)`. -/
def kernelCost (c : K → K → ℝ≥0∞) (P : Measure K) (κ : Kernel K K) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, c x y ∂(κ x) ∂P

end CsVoid

namespace Claims

/-! #### C `thm:cond-cal-impossible` -/

/-- `thm:cond-cal-impossible`: under distribution-free conditional coverage, for every law `P` and
`P_X`-a.e. `x` with `P_X{x} = 0`, `P{leb B̂(t | x) = ∞} ≥ 1 − α` and `E leb B̂(t | x) = ∞`. -/
def cond_cal_impossible : Prop :=
  ∀ (q n : ℕ) (𝒯 𝒴 Ξ : Type) [AddCommGroup 𝒴] [Module ℝ 𝒴] [MeasurableSpace 𝒴] [MeasurableSpace Ξ]
    (ev : 𝒴 →ₗ[ℝ] (𝒯 → ℝ)) (ν : Measure Ξ) [IsProbabilityMeasure ν] (B : BandProc q n 𝒯 𝒴 Ξ)
    (α : ℝ) (t : 𝒯),
    0 < α → α < 1 →
    (∀ s, Measurable fun y : 𝒴 => ev y s) → (∀ φ : 𝒴, Measurable fun p : 𝒴 × ℝ => p.1 + p.2 • φ) →
    MeasurableSet (coverSet ev B) → MeasurableSet (bandGraph B t) →
    CondCoverage α ν ev B → (∃ φ : 𝒴, ev φ t ≠ 0) →
    ∀ P : Measure ((Fin q → ℝ) × 𝒴), IsProbabilityMeasure P →
      ∀ᵐ x ∂(P.map Prod.fst), P.map Prod.fst {x} = 0 →
        (∃ E : Set ((Fin n → (Fin q → ℝ) × 𝒴) × Ξ), MeasurableSet E ∧
            E ⊆ {e | volume (B e.1 e.2 t x) = ∞} ∧ ENNReal.ofReal (1 - α) ≤ dataLaw n ν P E) ∧
          ∫⁻ e, volume (B e.1 e.2 t x) ∂(dataLaw n ν P) = ∞

/-- `thm:cond-cal-impossible`, "the constant `1 − α` cannot be improved": the randomized all-or-nothing band
(`ℝ` with probability `1 − α`, empty otherwise; `ξ ~ Unif[0,1]`) is a measurable procedure with conditional
coverage exactly `1 − α` under every law, and its width at every `t` and `x` is infinite with probability
exactly `1 − α`. -/
def cond_cal_sharp : Prop :=
  ∀ (q n : ℕ) (𝒯 𝒴 : Type) [Nonempty 𝒯] [AddCommGroup 𝒴] [Module ℝ 𝒴] [MeasurableSpace 𝒴]
    (ev : 𝒴 →ₗ[ℝ] (𝒯 → ℝ)) (α : ℝ),
    0 < α → α < 1 →
    ∃ B : BandProc q n 𝒯 𝒴 unitInterval,
      MeasurableSet (coverSet ev B) ∧ (∀ t, MeasurableSet (bandGraph B t)) ∧
      CondCoverage α volume ev B ∧
      (∀ P : Measure ((Fin q → ℝ) × 𝒴), IsProbabilityMeasure P → ∀ G : Set (Fin q → ℝ),
        MeasurableSet G →
          jointLaw n volume P {z | z.2.1 ∈ G ∧ z ∈ coverSet ev B} =
            ENNReal.ofReal (1 - α) * P.map Prod.fst G) ∧
      ∀ P : Measure ((Fin q → ℝ) × 𝒴), IsProbabilityMeasure P → ∀ (t : 𝒯) (x : Fin q → ℝ),
        dataLaw n volume P {e | volume (B e.1 e.2 t x) = ∞} = ENNReal.ofReal (1 - α)

/-! #### C `prop:coordinate-obstruction` -/

/-- (a): `g_{0,r}` has a unique maximiser on `D` iff `β_X` is differentiable at `r`. -/
def coord_select_iff : Prop :=
  ∀ (q : ℕ) (D : Set (EuclideanSpace ℝ (Fin q))) (φ₀ : EuclideanSpace ℝ (Fin q) → ℝ)
    (r : EuclideanSpace ℝ (Fin q)),
    IsCompact D → D.Nonempty → ContinuousOn φ₀ D →
      ((∃! c, c ∈ D ∧ IsMaxOn (gPot φ₀ r) D c) ↔ DifferentiableAt ℝ (brenierPot D φ₀) r)

/-- (a): at a point of differentiability the maximiser is `T_X(r) = ∇β_X(r) ∈ D`. -/
def coord_select_max : Prop :=
  ∀ (q : ℕ) (D : Set (EuclideanSpace ℝ (Fin q))) (φ₀ : EuclideanSpace ℝ (Fin q) → ℝ)
    (r : EuclideanSpace ℝ (Fin q)),
    IsCompact D → D.Nonempty → ContinuousOn φ₀ D → DifferentiableAt ℝ (brenierPot D φ₀) r →
      brenierMap D φ₀ r ∈ D ∧ IsMaxOn (gPot φ₀ r) D (brenierMap D φ₀ r)

/-- (a): `β_X` is differentiable at Lebesgue-almost every `r`. -/
def coord_select_ae : Prop :=
  ∀ (q : ℕ) (D : Set (EuclideanSpace ℝ (Fin q))) (φ₀ : EuclideanSpace ℝ (Fin q) → ℝ),
    IsCompact D → D.Nonempty → ContinuousOn φ₀ D →
      ∀ᵐ r ∂(volume : Measure (EuclideanSpace ℝ (Fin q))), DifferentiableAt ℝ (brenierPot D φ₀) r

/-- (b): `δ_a > 0`, `P_C(U_a) > 0`, and `∫_{F_a} w_ε(c | r) dP_C ≤ e^{−δ_a/(4ε)}/P_C(U_a)` whenever
`‖φ_ε − φ₀‖_{∞,D} ≤ δ_a/4`, in particular for all small `ε`. -/
def coord_concentration : Prop :=
  ∀ (q : ℕ) (PC : Measure (EuclideanSpace ℝ (Fin q))) [IsProbabilityMeasure PC]
    (D : Set (EuclideanSpace ℝ (Fin q))) (φ₀ : EuclideanSpace ℝ (Fin q) → ℝ)
    (φ : ℝ → EuclideanSpace ℝ (Fin q) → ℝ) (r : EuclideanSpace ℝ (Fin q)) (a : ℝ),
    IsCompactSupport PC D → ContinuousOn φ₀ D → (∀ ε, 0 < ε → ContinuousOn (φ ε) D) →
    TendstoUniformlyOn φ φ₀ (𝓝[>] 0) D → DifferentiableAt ℝ (brenierPot D φ₀) r → 0 < a →
    (farSet D φ₀ r a).Nonempty →
      0 < gapA D φ₀ r a ∧ 0 < PC (nearSet D φ₀ r a) ∧
      (∀ ε, 0 < ε → (∀ c ∈ D, |φ ε c - φ₀ c| ≤ gapA D φ₀ r a / 4) →
        ∫ c in farSet D φ₀ r a, oosWeight PC D (φ ε) ε r c ∂PC ≤
          Real.exp (-(gapA D φ₀ r a) / (4 * ε)) / PC.real (nearSet D φ₀ r a)) ∧
      ∀ᶠ ε in 𝓝[>] 0, ∫ c in farSet D φ₀ r a, oosWeight PC D (φ ε) ε r c ∂PC ≤
          Real.exp (-(gapA D φ₀ r a) / (4 * ε)) / PC.real (nearSet D φ₀ r a)

/-- (c): `W₁(P^ν_{K,ε,r}, P_{K,T_X(r)}) → 0` as `ε ↓ 0`. -/
def coord_limit : Prop :=
  ∀ (q k : ℕ) (PC : Measure (EuclideanSpace ℝ (Fin q))) [IsProbabilityMeasure PC]
    (D : Set (EuclideanSpace ℝ (Fin q))) (φ₀ : EuclideanSpace ℝ (Fin q) → ℝ)
    (φ : ℝ → EuclideanSpace ℝ (Fin q) → ℝ)
    (κ : Kernel (EuclideanSpace ℝ (Fin q)) (EuclideanSpace ℝ (Fin k))) [IsMarkovKernel κ]
    (r : EuclideanSpace ℝ (Fin q)) (R : ℝ),
    IsCompactSupport PC D → ContinuousOn φ₀ D → (∀ ε, 0 < ε → ContinuousOn (φ ε) D) →
    TendstoUniformlyOn φ φ₀ (𝓝[>] 0) D → DifferentiableAt ℝ (brenierPot D φ₀) r →
    (∀ c ∈ D, κ c (Metric.closedBall 0 R)ᶜ = 0) →
    Tendsto (fun c => wassersteinEDist 1 (κ c) (κ (brenierMap D φ₀ r))) (𝓝[D] (brenierMap D φ₀ r)) (𝓝 0) →
      Tendsto (fun ε => wassersteinEDist 1 (locLaw PC D κ (φ ε) ε r) (κ (brenierMap D φ₀ r)))
        (𝓝[>] 0) (𝓝 0)

/-- (c) at the raw query `r = x ∈ D`: `W₁(P^ν_{K,ε,x}, P_{K,x}) → W₁(P_{K,T_X(x)}, P_{K,x})`, which is positive
exactly when `P_{K,T_X(x)} ≠ P_{K,x}`. -/
def coord_raw_query : Prop :=
  ∀ (q k : ℕ) (PC : Measure (EuclideanSpace ℝ (Fin q))) [IsProbabilityMeasure PC]
    (D : Set (EuclideanSpace ℝ (Fin q))) (φ₀ : EuclideanSpace ℝ (Fin q) → ℝ)
    (φ : ℝ → EuclideanSpace ℝ (Fin q) → ℝ)
    (κ : Kernel (EuclideanSpace ℝ (Fin q)) (EuclideanSpace ℝ (Fin k))) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin q)) (R : ℝ),
    IsCompactSupport PC D → ContinuousOn φ₀ D → (∀ ε, 0 < ε → ContinuousOn (φ ε) D) →
    TendstoUniformlyOn φ φ₀ (𝓝[>] 0) D → DifferentiableAt ℝ (brenierPot D φ₀) x → x ∈ D →
    (∀ c ∈ D, κ c (Metric.closedBall 0 R)ᶜ = 0) →
    Tendsto (fun c => wassersteinEDist 1 (κ c) (κ (brenierMap D φ₀ x))) (𝓝[D] (brenierMap D φ₀ x)) (𝓝 0) →
      Tendsto (fun ε => wassersteinEDist 1 (locLaw PC D κ (φ ε) ε x) (κ x)) (𝓝[>] 0)
          (𝓝 (wassersteinEDist 1 (κ (brenierMap D φ₀ x)) (κ x))) ∧
        (0 < wassersteinEDist 1 (κ (brenierMap D φ₀ x)) (κ x) ↔ κ (brenierMap D φ₀ x) ≠ κ x)

/-- (d), first sentence: at a reference coordinate `r_x` with `T_X(r_x) = x`, `W₁(P^ν_{K,ε,r_x}, P_{K,x}) → 0`
whenever `c ↦ P_{K,c}` is `W₁`-continuous at `x` relative to `D`. -/
def coord_forward : Prop :=
  ∀ (q k : ℕ) (PC : Measure (EuclideanSpace ℝ (Fin q))) [IsProbabilityMeasure PC]
    (D : Set (EuclideanSpace ℝ (Fin q))) (φ₀ : EuclideanSpace ℝ (Fin q) → ℝ)
    (φ : ℝ → EuclideanSpace ℝ (Fin q) → ℝ)
    (κ : Kernel (EuclideanSpace ℝ (Fin q)) (EuclideanSpace ℝ (Fin k))) [IsMarkovKernel κ]
    (x rx : EuclideanSpace ℝ (Fin q)) (R : ℝ),
    IsCompactSupport PC D → ContinuousOn φ₀ D → (∀ ε, 0 < ε → ContinuousOn (φ ε) D) →
    TendstoUniformlyOn φ φ₀ (𝓝[>] 0) D → DifferentiableAt ℝ (brenierPot D φ₀) rx →
    brenierMap D φ₀ rx = x → (∀ c ∈ D, κ c (Metric.closedBall 0 R)ᶜ = 0) →
    Tendsto (fun c => wassersteinEDist 1 (κ c) (κ x)) (𝓝[D] x) (𝓝 0) →
      Tendsto (fun ε => wassersteinEDist 1 (locLaw PC D κ (φ ε) ε rx) (κ x)) (𝓝[>] 0) (𝓝 0)

/-! #### JASA `prop:cs-void` -/

/-- (i): for mutually singular `P₀, P₁`, every pair `(Q₀, Q₁)` is `(P₀κ, P₁κ)` for a common Markov kernel. -/
def cs_void_kernel : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (P₀ P₁ Q₀ Q₁ : Measure K) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁],
    P₀ ⟂ₘ P₁ → ∃ κ : Kernel K K, IsMarkovKernel κ ∧ P₀.bind κ = Q₀ ∧ P₁.bind κ = Q₁

/-- (i): for mutually singular `P₀, P₁` and bounded measurable `h`,
`sup_κ W₂²(h#P₀κ, h#P₁κ) = (sup_K h − inf_K h)²`. -/
def cs_void_sup : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (P₀ P₁ : Measure K) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h : K → ℝ),
    P₀ ⟂ₘ P₁ → Measurable h → BddAbove (range h) → BddBelow (range h) →
      ⨆ (κ : Kernel K K) (_ : IsMarkovKernel κ),
          wassersteinEDist 2 ((P₀.bind κ).map h) ((P₁.bind κ).map h) ^ 2 = ENNReal.ofReal (osc h ^ 2)

/-- (i), "attained or approached by point masses": the supremum over pairs of point masses
`(δ_{x₊}, δ_{x₋})` of `W₂²(h#δ_{x₊}, h#δ_{x₋})` is `(sup_K h − inf_K h)²`. -/
def cs_void_dirac : Prop :=
  ∀ (K : Type) [MeasurableSpace K] [Nonempty K] (h : K → ℝ),
    Measurable h → BddAbove (range h) → BddBelow (range h) →
      ⨆ (xp : K) (xm : K),
          wassersteinEDist 2 ((Measure.dirac xp).map h) ((Measure.dirac xm).map h) ^ 2 =
        ENNReal.ofReal (osc h ^ 2)

/-- (ii): for mutually singular `P₀, P₁` and `Q_s ≪ P_s`, one measurable `w ≥ 0` has `dQ_s = w dP_s`, `s = 0, 1`. -/
def cs_void_reweight : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (P₀ P₁ Q₀ Q₁ : Measure K) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁],
    P₀ ⟂ₘ P₁ → Q₀ ≪ P₀ → Q₁ ≪ P₁ →
      ∃ w : K → ℝ, Measurable w ∧ (∀ x, 0 ≤ w x) ∧
        P₀.withDensity (fun x => ENNReal.ofReal (w x)) = Q₀ ∧
        P₁.withDensity (fun x => ENNReal.ofReal (w x)) = Q₁

/-- (iii): for mutually singular `P₀, P₁`, the pairs `(P₀κ, P₁κ)` produced by common kernels with pooled budget
`π₀ E_{P₀}E_κ c + π₁ E_{P₁}E_κ c ≤ r` are exactly the pairs `(P₀κ₀, P₁κ₁)` with
`π₀ E_{P₀}E_{κ₀} c + π₁ E_{P₁}E_{κ₁} c ≤ r`. -/
def cs_void_pooled : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (P₀ P₁ : Measure K) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (c : K → K → ℝ≥0∞) (π₀ π₁ r : ℝ≥0∞),
    P₀ ⟂ₘ P₁ → π₀ + π₁ = 1 →
      {Q : Measure K × Measure K | ∃ κ : Kernel K K, IsMarkovKernel κ ∧
          π₀ * kernelCost c P₀ κ + π₁ * kernelCost c P₁ κ ≤ r ∧ Q = (P₀.bind κ, P₁.bind κ)} =
        {Q | ∃ κ₀ κ₁ : Kernel K K, IsMarkovKernel κ₀ ∧ IsMarkovKernel κ₁ ∧
          π₀ * kernelCost c P₀ κ₀ + π₁ * kernelCost c P₁ κ₁ ≤ r ∧ Q = (P₀.bind κ₀, P₁.bind κ₁)}

/-- (iv): for arbitrary `P₀, P₁` and bounded measurable `h`,
`sup_κ W₂²(h#P₀κ, h#P₁κ) = TV(P₀, P₁)(sup_K h − inf_K h)²`. -/
def cs_void_tv : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (P₀ P₁ : Measure K) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h : K → ℝ),
    Measurable h → BddAbove (range h) → BddBelow (range h) →
      ⨆ (κ : Kernel K K) (_ : IsMarkovKernel κ),
          wassersteinEDist 2 ((P₀.bind κ).map h) ((P₁.bind κ).map h) ^ 2 =
        ENNReal.ofReal (tvDist P₀ P₁ * osc h ^ 2)

end Claims
end StatFormal.Wave10b
