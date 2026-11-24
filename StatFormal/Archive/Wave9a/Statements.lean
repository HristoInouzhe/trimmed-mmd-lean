import StatFormal.Archive.RobustEquality.SemidualStrong.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Matrix.Mul

/-!
# FROZEN STATEMENTS — wave 9a (QUEUE rows 80–82): robust equality JASA `thm:ad-valid`, paper 2
# `lem:delta-inf`, JASA `lem:lindsay`

Sources (verbatim in `lean-formalisation/inventory/extracted/robust-equality-jasa.md`,
`robust-equality-paper2.md`; current text after the 2026-10-13/14 corrections; paths under
`robust-equality-outcomes-under-distribution-shift/`):
* JASA `thm:ad-valid` (`jasa/supp_calibration.tex:310-314`, proof `:316-324`), with `def:ad-rho`
  (`:290-303`: grid `θ_1 = 1 > θ_2 = θ_1/γ > … > θ_N`, `r = log(N/α)/m`, `H(f) ≥ sup_K g_f` computed from `(f, μ, K)`
  only, `z_j(t) = (φ(Y_j) − t)/(H − t)`, `F̂_t(θ) = m⁻¹ Σ_j log(1 − θ z_j(t))`,
  `U_N(φ) = sup{t < H : max_l F̂_t(θ_l) < r}`, `ρ̂_N = sup_{f ∈ F_W} {⟨a,f⟩ + U_N(g_f)}`), the fold setting of
  `sec:ad` (`:206-211`: `Θ = OT_ε(μ, P)`, `Y_1, …, Y_m` i.i.d. `P`, `μ` fixed) and `lem:semidual` (frozen).
* paper 2 `lem:delta-inf` (`paper2/main.tex:296-303`, proof `paper2/app_proofs.tex:34-46`), with the setting of
  `paper2/main.tex:213-216` (centres `P̂_s` empirical on `n_s` labelled points, `h` measurable).
* JASA `lem:lindsay` (`jasa/supp_proofs.tex:385-395`, proof `:397-404`), with `ass:mixture`
  (`supp_proofs.tex:225-230`), `Λ^𝒩_s` (`main.tex:349-352`) and the reference convention
  (`supp_proofs.tex:14-23`: a reference is a measure with `0 < ν(K) ≤ 1`).
Reuses the frozen `RobustEquality/Semidual/Statements.lean` (`gsoft`, `muDisc`) and
`RobustEquality/SemidualStrong/Statements.lean` (`OTdisc`, `Jdual`, `Setting`), imported, not copied.

Covered:
* `thm:ad-valid`: `ad_valid_core` (for every bounded measurable `φ ≤ H` and every `P`,
  `P^m[Pφ ≤ U_N(φ)] ≥ 1 − α`: the Markov bound on the `N` test products and the union over the grid),
  `ad_valid` (`P^m[ρ̂_N ≥ Θ(P)] ≥ 1 − α` for every `P`), `ad_valid_dominating` ("and so is every
  `ρ̃ ≥ ⟨a,f*⟩ + U_N(g_{f*})`", for any maximiser `f*` of `J_P` and any `H ≥ sup_K g_{f*}`).
* `lem:delta-inf`: `delta_le_coupling` (general laws: `W_2²(h#μ₀, h#μ₁) ≤ E_γ{h(X) − h(Y)}²` for every
  `γ ∈ Π(μ₀,μ₁)`, the "minimum is at least `W_2²`" half), `nw_mem`, `nw_vertex`, `nw_optimal` (empirical
  centres: the lifted north-west-corner / quantile coupling lies in the transport polytope, is a vertex of it, and
  minimises `E_γ{h(X) − h(Y)}²` over it, for every sorting of the projections, ties broken arbitrarily),
  `delta_inf_empirical` (empirical centres: `W_2²(h#P̂₀, h#P̂₁)` equals that minimum, so the minimum over couplings
  is attained at the vertex), `nw_coupling` (the vertex, as the measure `Σ_ij γ_ij δ_{(x_i,y_j)}`, lies in
  `Π(P̂₀, P̂₁)` with the same cost: links the label polytope to measure couplings), `linear_cost` (`E_γ⟨w, X − Y⟩² = wᵀM_γw`, so `Δ(w)² = min_γ wᵀM_γw` for empirical
  centres by `delta_inf_empirical` with `h = ⟨w,·⟩`).
* `lem:lindsay` (finite `L`): `lindsay_sandwich` (`L(m̂) ≤ Λ ≤ L(m̂) + log sup_{m ∈ 𝓜} ∫ D_{m̂} dm`),
  `lindsay_maximiser` (equality throughout at a maximiser over a convex `𝓜`: `Λ = L(m̂)` and the supremum is `1`),
  `lindsay_extreme` (the supremum is attained at an extreme point of a closed convex `𝓜`), `lindsay_dirac` (for
  `𝓜 = 𝒫(L)`, at a point `y ∈ L`; with `L` a dictionary of `J` references this is "the largest of `J` numbers").

Not covered (declared):
* `thm:ad-valid`: the branch-and-bound computation of `H(f)` (only `H(f) ≥ sup_K g_f` is used); measurability of
  `ρ̂_N` (event convention); the remark after the proof (no union bound over potentials, computational price).
* `lem:delta-inf`: the "≤" half for general laws `μ₀, μ₁` (the lift through regular conditional laws, which needs
  disintegration/gluing; the queue note allows declaring it), hence attainment for general laws; the
  existence of a sorting permutation (`Tuple.sort`) is not restated.
* `lem:lindsay`: a general compact metric `L` with a Feller kernel (only finite `L`, the queue's core); the bathtub
  value for the density-bounded class; Bauer's principle beyond finite dimension.

Encodings (see card):
* `thm:ad-valid`: the sample is `y : Fin m → K` under `Measure.pi (fun _ => P)` (i.i.d. `P`). `max_l F̂_t(θ_l) < r`
  is written `∀ l, ∏_j (1 − θ_l z_j(t)) < exp(m r)` (`testProd`, `profileUB`): equal to the printed condition
  because `exp(m F̂_t(θ)) = ∏_j(1 − θ z_j(t))` (the paper's display after `def:ad-rho`), and it avoids Lean's
  `log 0 = 0` (a zero factor makes `F̂ = −∞ < r`, and the product `0 < exp(m r)`). `U_N` is `sSup` in `ℝ` of a set
  bounded above by `H` and never empty (as `t → −∞` each product tends to `∏_j(1 − θ_l) ≤ 1 < N/α`), so it
  is the printed supremum; the proofs exhibit an element and never use `sSup ∅ = 0`.
  The grid is any `θ ∈ [0,1]^N` (a generalisation of the geometric grid with `θ_1 = 1`; validity uses only
  `θ_l ∈ [0,1]`). `H(f)` is a deterministic function of `f` (`H : ℝ^k → ℝ`), with `g_f ≤ H(f)` on `K` for
  `f ∈ F_W`. `F_W = {f : f_i − f_j ≤ sup_K(c_i − c_j)}` is written with every upper bound `B'` of `c_i − c_j`, as in
  the frozen `maximiser_foc`. `ρ̂_N` is a supremum in `EReal` (`⊤` allowed, no junk). `Θ(P) = OTdisc ε a c P`
  (frozen), and the standing setting is the frozen `Setting` (`ε > 0`, `a_i > 0`, `Σ a_i = 1`, bounded measurable
  `c_i`). `0 < α < 1`, `m, N ≥ 1`. Events: `∃` measurable `E ⊆ event` with `P^m(E) ≥ 1 − α`.
* `lem:delta-inf`: `W_2` is Tau Ceti's `wassersteinEDist 2` on `ℝ` (infimum over couplings, in `ℝ≥0∞`), squared;
  `h#μ = μ.map h` with `h` measurable; `Π(μ₀,μ₁)` is Tau Ceti's `IsCoupling`; `E_γ{…}²` is a lower integral of
  `ofReal` (no integrability junk). An empirical centre is `Σ_i n⁻¹ δ_{x_i}` over labelled atoms `x : Fin n → K`
  (`empMeas`, ties allowed); the transport polytope is the set of real `n₀ × n₁` arrays with nonnegative entries,
  row sums `1/n₀` and column sums `1/n₁` (`transportPoly`), a vertex is a member of `extremePoints ℝ`, and the cost
  is `Σ_ij γ_ij (h(x_i) − h(y_j))²` (`projCost`). A sorting is a permutation `σ` with `h ∘ x ∘ σ` monotone (`σ k` is
  the label of rank `k`); the quantile coupling in rank coordinates is the overlap length of the quantile cells
  `[k/n₀,(k+1)/n₀]` and `[l/n₁,(l+1)/n₁]` (`nwSorted`, the north-west-corner rule for uniform weights), lifted to labels
  by `nwLift σ₀ σ₁ i j = nwSorted (σ₀⁻¹ i) (σ₁⁻¹ j)`. Linear rules: covariates in `ℝ^d` (`Fin d → ℝ`),
  `M_γ = Σ_ij γ_ij (x_i − y_j)(x_i − y_j)ᵀ` (`secondMoment`), `h_w = ⟨w,·⟩` (`dotProduct`).
* `lem:lindsay`: `L` is a finite nonempty type `ι` (discrete topology); a mixing law is a vector of the standard
  simplex, `𝓜 ⊆ probSimplex ι` (weakly closed = closed); the kernel is a family `κ_y` of finite measures on `K` with
  `0 < κ_y(K) ≤ 1`, `ν_m = Σ_y m_y κ_y` (`mixRef`), and `φ_i = φ(x_i, ·)` (`φ = (f_h − λc)/(λε)`) is any bounded
  measurable function per anchor, `n ≥ 1` anchors. `ψ_i(y) = ∫ e^{φ_i} dκ_y` (`psiLik`),
  `L(m) = n⁻¹ Σ_i log Σ_y m_y ψ_i(y)` (`npmleObj`), `Λ = sup_{m ∈ 𝓜} n⁻¹ Σ_i log ∫ e^{φ_i} dν_m` (`lambdaN`, the
  printed `Λ^𝒩_s` with `𝒩 = {ν_m : m ∈ 𝓜}`), `D_{m̂} = n⁻¹ Σ_i ψ_i/∫ψ_i dm̂` (`lindsayD`),
  `sup_{m ∈ 𝓜} ∫ D_{m̂} dm` (`lindsaySup`). Suprema are `sSup` in `ℝ` of nonempty sets bounded above under the
  hypotheses (`φ` bounded, `L` finite), and `L(m̂) > −∞` holds automatically (`ψ_i > 0`). `lindsay_sandwich` drops
  convexity and closedness of `𝓜` (not used); `lindsay_extreme` keeps them.

Critic notes:
* `thm:ad-valid` holds as printed. The case `t₀ = H` (`φ = H` `P`-a.s.) is handled as in the paper: then every
  factor is `1 − θ_l ∈ [0,1]` and the admissible set is `(−∞, H)`.
* `lem:delta-inf` holds as printed for empirical centres; the "≤" half for general laws is declared.
* `lem:lindsay` holds as printed for finite `L`.
* Critic (2026-10-14): ACCEPT-WITH-NOTES, all claims true. (1) The ad-valid test written as products is exactly
  the paper's test: a zero factor corresponds to `F̂ = −∞ < r`. (2) The admissible set may contain its endpoint,
  so it is "`(−∞, U_N]` or `(−∞, U_N)`" rather than the printed `(−∞, U_N)` (a wording nit; the bound is
  unaffected). (3) The general-law lift of `lem:delta-inf` is declared; the paper applies the lemma only to
  empirical centres (`thm:alternating`, `prop:nominal`, `prop:jointmin`), which are covered.
* Proof routes: `Wave9a/Route{AdValid,DeltaLP,DeltaW2,DeltaCoupling,Lindsay}.lean`, all 14 claims (`Wave9a/Proofs.lean`),
  standard axioms `propext, Classical.choice, Quot.sound` only. `nw_*` reuse Tau Ceti's monotone transport matrices.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory TauCeti Set
open scoped ENNReal Matrix

namespace StatFormal.Wave9a

open StatFormal.RobustEquality.Semidual StatFormal.RobustEquality.SemidualStrong

/-! ### JASA `thm:ad-valid` -/

section AdValid

variable {K : Type*}

/-- The test product `∏_j (1 − θ z_j(t))`, `z_j(t) = (φ(Y_j) − t)/(H − t)`; it equals `exp(m F̂_t(θ))`. -/
def testProd {m : ℕ} (φ : K → ℝ) (H t θ : ℝ) (y : Fin m → K) : ℝ :=
  ∏ j, (1 - θ * ((φ (y j) - t) / (H - t)))

/-- The profile `K_inf` bound `U_N(φ) = sup{t < H : max_l F̂_t(θ_l) < r}`, `r = log(N/α)/m`, written with
`exp(m F̂_t(θ_l)) = ∏_j (1 − θ_l z_j(t))`. -/
def profileUB {m N : ℕ} (α H : ℝ) (θ : Fin N → ℝ) (φ : K → ℝ) (y : Fin m → K) : ℝ :=
  sSup {t | t < H ∧ ∀ l, testProd φ H t (θ l) y < Real.exp (m * (Real.log (N / α) / m))}

/-- `F_W = {f : f_i − f_j ≤ sup_K (c_i − c_j)}`. -/
def FW {k : ℕ} (c : Fin k → K → ℝ) : Set (Fin k → ℝ) :=
  {f | ∀ i j (B' : ℝ), (∀ y, c i y - c j y ≤ B') → f i - f j ≤ B'}

/-- `ρ̂_N = sup_{f ∈ F_W} {⟨a,f⟩ + U_N(g_f)}`, with the certified bound `H(f) ≥ sup_K g_f`. -/
def rhoN {k m N : ℕ} (ε α : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (H : (Fin k → ℝ) → ℝ)
    (θ : Fin N → ℝ) (y : Fin m → K) : EReal :=
  ⨆ f ∈ FW c, (((∑ i, a i * f i) + profileUB α (H f) θ (gsoft ε a f c) y : ℝ) : EReal)

end AdValid

/-! ### paper 2 `lem:delta-inf` -/

section DeltaInf

variable {K : Type*}

/-- The transport polytope of two empirical centres on `n₀`, `n₁` labelled atoms. -/
def transportPoly (n₀ n₁ : ℕ) : Set (Fin n₀ → Fin n₁ → ℝ) :=
  {γ | (∀ i j, 0 ≤ γ i j) ∧ (∀ i, ∑ j, γ i j = 1 / n₀) ∧ ∀ j, ∑ i, γ i j = 1 / n₁}

/-- `E_γ {h(X) − h(Y)}² = Σ_ij γ_ij (h(x_i) − h(y_j))²`. -/
def projCost {n₀ n₁ : ℕ} (h : K → ℝ) (x : Fin n₀ → K) (y : Fin n₁ → K)
    (γ : Fin n₀ → Fin n₁ → ℝ) : ℝ :=
  ∑ i, ∑ j, γ i j * (h (x i) - h (y j)) ^ 2

/-- The quantile (north-west corner) coupling of uniform weights in rank coordinates: the length of the overlap
of the quantile cells `[k/n₀, (k+1)/n₀]` and `[l/n₁, (l+1)/n₁]`. -/
def nwSorted (n₀ n₁ : ℕ) (k : Fin n₀) (l : Fin n₁) : ℝ :=
  max 0 (min (((k : ℕ) + 1 : ℝ) / n₀) (((l : ℕ) + 1 : ℝ) / n₁) -
    max ((k : ℕ) / (n₀ : ℝ)) ((l : ℕ) / (n₁ : ℝ)))

/-- The lift to the covariates: atoms are paired in the order of their projections (`σ k` = label of rank `k`). -/
def nwLift {n₀ n₁ : ℕ} (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁)) :
    Fin n₀ → Fin n₁ → ℝ :=
  fun i j => nwSorted n₀ n₁ (σ₀.symm i) (σ₁.symm j)

/-- The empirical centre `n⁻¹ Σ_i δ_{x_i}` of labelled atoms. -/
def empMeas [MeasurableSpace K] {n : ℕ} (x : Fin n → K) : Measure K :=
  ∑ i, ENNReal.ofReal (1 / n) • Measure.dirac (x i)

/-- The measure `Σ_ij γ_ij δ_{(x_i, y_j)}` on `K × K` of a label plan `γ`. -/
def planMeas [MeasurableSpace K] {n₀ n₁ : ℕ} (x : Fin n₀ → K) (y : Fin n₁ → K)
    (γ : Fin n₀ → Fin n₁ → ℝ) : Measure (K × K) :=
  ∑ i, ∑ j, ENNReal.ofReal (γ i j) • Measure.dirac (x i, y j)

/-- `M_γ = E_γ (X − Y)(X − Y)ᵀ` for empirical centres in `ℝ^d`. -/
def secondMoment {d n₀ n₁ : ℕ} (x : Fin n₀ → Fin d → ℝ) (y : Fin n₁ → Fin d → ℝ)
    (γ : Fin n₀ → Fin n₁ → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ i, ∑ j, γ i j • Matrix.vecMulVec (x i - y j) (x i - y j)

end DeltaInf

/-! ### JASA `lem:lindsay` (finite `L`) -/

section Lindsay

variable {K : Type*} [MeasurableSpace K] {ι : Type*} [Fintype ι] {n : ℕ}

/-- Mixing laws on the finite `L`: probability vectors. -/
def probSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {m | (∀ y, 0 ≤ m y) ∧ ∑ y, m y = 1}

/-- The mixture reference `ν_m = ∫ κ(y, ·) m(dy) = Σ_y m_y κ_y`. -/
def mixRef (κ : ι → Measure K) (m : ι → ℝ) : Measure K :=
  ∑ y, ENNReal.ofReal (m y) • κ y

/-- The likelihoods `ψ_i(y) = ∫ e^{φ(x_i,·)} dκ(y,·)`. -/
def psiLik (κ : ι → Measure K) (φ : Fin n → K → ℝ) (i : Fin n) (y : ι) : ℝ :=
  ∫ x, Real.exp (φ i x) ∂(κ y)

/-- `L(m) = n⁻¹ Σ_i log ∫ ψ_i dm`. -/
def npmleObj (κ : ι → Measure K) (φ : Fin n → K → ℝ) (m : ι → ℝ) : ℝ :=
  (1 / n : ℝ) * ∑ i, Real.log (∑ y, m y * psiLik κ φ i y)

/-- `Λ^𝒩_s = sup_{ν ∈ 𝒩} E_{x₀ ∼ P̂_s} log E_{x∼ν} e^{φ(x₀,x)}`, `𝒩 = {ν_m : m ∈ 𝓜}`. -/
def lambdaN (κ : ι → Measure K) (φ : Fin n → K → ℝ) (M : Set (ι → ℝ)) : ℝ :=
  sSup {v | ∃ m ∈ M, v = (1 / n : ℝ) * ∑ i, Real.log (∫ x, Real.exp (φ i x) ∂(mixRef κ m))}

/-- `D_{m̂} = n⁻¹ Σ_i ψ_i / ∫ ψ_i dm̂`. -/
def lindsayD (κ : ι → Measure K) (φ : Fin n → K → ℝ) (mh : ι → ℝ) (y : ι) : ℝ :=
  (1 / n : ℝ) * ∑ i, psiLik κ φ i y / (∑ y', mh y' * psiLik κ φ i y')

/-- `sup_{m ∈ 𝓜} ∫ D_{m̂} dm`. -/
def lindsaySup (κ : ι → Measure K) (φ : Fin n → K → ℝ) (M : Set (ι → ℝ)) (mh : ι → ℝ) : ℝ :=
  sSup {v | ∃ m ∈ M, v = ∑ y, m y * lindsayD κ φ mh y}

/-- The standing hypotheses on the kernel and the exponents (`ass:mixture`, finite `L`). -/
def MixSetting (κ : ι → Measure K) (φ : Fin n → K → ℝ) : Prop :=
  0 < n ∧ (∀ y, IsFiniteMeasure (κ y)) ∧ (∀ y, 0 < κ y univ ∧ κ y univ ≤ 1) ∧
    (∀ i, Measurable (φ i)) ∧ ∃ B, ∀ i x, |φ i x| ≤ B

end Lindsay

namespace Claims

/-- `thm:ad-valid`, core: `P^m[Pφ ≤ U_N(φ)] ≥ 1 − α` for every bounded measurable `φ ≤ H` and every `P`. -/
def ad_valid_core : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (P : Measure K) [IsProbabilityMeasure P] (m N : ℕ) (α H B : ℝ)
    (θ : Fin N → ℝ) (φ : K → ℝ),
    0 < m → 0 < N → 0 < α → α < 1 → (∀ l, 0 ≤ θ l ∧ θ l ≤ 1) →
    Measurable φ → (∀ x, |φ x| ≤ B) → (∀ x, φ x ≤ H) →
      ∃ E : Set (Fin m → K), MeasurableSet E ∧ E ⊆ {y | ∫ x, φ x ∂P ≤ profileUB α H θ φ y} ∧
        ENNReal.ofReal (1 - α) ≤ Measure.pi (fun _ : Fin m => P) E

/-- `thm:ad-valid`: `P^m[ρ̂_N ≥ Θ(P)] ≥ 1 − α` for every `P ∈ 𝒫(K)`. -/
def ad_valid : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k m N : ℕ) (ε α : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P : Measure K) [IsProbabilityMeasure P] (H : (Fin k → ℝ) → ℝ) (θ : Fin N → ℝ),
    Setting ε a c → 0 < m → 0 < N → 0 < α → α < 1 → (∀ l, 0 ≤ θ l ∧ θ l ≤ 1) →
    (∀ f ∈ FW c, ∀ y, gsoft ε a f c y ≤ H f) →
      ∃ E : Set (Fin m → K), MeasurableSet E ∧ E ⊆ {y | OTdisc ε a c P ≤ rhoN ε α a c H θ y} ∧
        ENNReal.ofReal (1 - α) ≤ Measure.pi (fun _ : Fin m => P) E

/-- `thm:ad-valid`, last clause: every `ρ̃ ≥ ⟨a,f*⟩ + U_N(g_{f*})` is valid, `f*` a maximiser of `J_P`. -/
def ad_valid_dominating : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k m N : ℕ) (ε α : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P : Measure K) [IsProbabilityMeasure P] (fs : Fin k → ℝ) (H : ℝ) (θ : Fin N → ℝ)
    (ρ : (Fin m → K) → EReal),
    Setting ε a c → 0 < m → 0 < N → 0 < α → α < 1 → (∀ l, 0 ≤ θ l ∧ θ l ≤ 1) →
    (∀ f, Jdual ε a c P f ≤ Jdual ε a c P fs) → (∀ y, gsoft ε a fs c y ≤ H) →
    (∀ y, (((∑ i, a i * fs i) + profileUB α H θ (gsoft ε a fs c) y : ℝ) : EReal) ≤ ρ y) →
      ∃ E : Set (Fin m → K), MeasurableSet E ∧ E ⊆ {y | OTdisc ε a c P ≤ ρ y} ∧
        ENNReal.ofReal (1 - α) ≤ Measure.pi (fun _ : Fin m => P) E

/-- `lem:delta-inf`, first clause, "≥" half, any laws: `W_2²(h#μ₀, h#μ₁) ≤ E_γ{h(X) − h(Y)}²`. -/
def delta_le_coupling : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (μ₀ μ₁ : Measure K) (h : K → ℝ) (γ : Measure (K × K)),
    Measurable h → IsCoupling γ μ₀ μ₁ →
      wassersteinEDist 2 (μ₀.map h) (μ₁.map h) ^ 2 ≤ ∫⁻ z, ENNReal.ofReal ((h z.1 - h z.2) ^ 2) ∂γ

/-- `lem:delta-inf`, empirical centres: the lifted quantile coupling lies in the transport polytope. -/
def nw_mem : Prop :=
  ∀ (n₀ n₁ : ℕ) (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁)),
    0 < n₀ → 0 < n₁ → nwLift σ₀ σ₁ ∈ transportPoly n₀ n₁

/-- `lem:delta-inf`, empirical centres: the lifted quantile coupling is a vertex of the transport polytope. -/
def nw_vertex : Prop :=
  ∀ (n₀ n₁ : ℕ) (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁)),
    0 < n₀ → 0 < n₁ → nwLift σ₀ σ₁ ∈ (transportPoly n₀ n₁).extremePoints ℝ

/-- `lem:delta-inf`, empirical centres: for every sorting of the projections (ties broken arbitrarily), the lifted
quantile coupling minimises `E_γ{h(X) − h(Y)}²` over the transport polytope. -/
def nw_optimal : Prop :=
  ∀ (K : Type) (n₀ n₁ : ℕ) (h : K → ℝ) (x : Fin n₀ → K) (y : Fin n₁ → K)
    (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁)),
    0 < n₀ → 0 < n₁ → Monotone (h ∘ x ∘ σ₀) → Monotone (h ∘ y ∘ σ₁) →
      ∀ γ ∈ transportPoly n₀ n₁, projCost h x y (nwLift σ₀ σ₁) ≤ projCost h x y γ

/-- `lem:delta-inf`, empirical centres: the lifted quantile coupling, as a measure on `K × K`, is a coupling of
`P̂₀` and `P̂₁` (Tau Ceti `IsCoupling`) whose cost `E_γ{h(X) − h(Y)}²` is `projCost` of the label plan. -/
def nw_coupling : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n₀ n₁ : ℕ) (h : K → ℝ) (x : Fin n₀ → K) (y : Fin n₁ → K)
    (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁)),
    0 < n₀ → 0 < n₁ → Measurable h →
      IsCoupling (planMeas x y (nwLift σ₀ σ₁)) (empMeas x) (empMeas y) ∧
        ∫⁻ z, ENNReal.ofReal ((h z.1 - h z.2) ^ 2) ∂(planMeas x y (nwLift σ₀ σ₁)) =
          ENNReal.ofReal (projCost h x y (nwLift σ₀ σ₁))

/-- `lem:delta-inf`, empirical centres: `W_2²(h#P̂₀, h#P̂₁)` is the cost of the lifted quantile coupling (hence the
minimum over the transport polytope, by `nw_mem` and `nw_optimal`). -/
def delta_inf_empirical : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n₀ n₁ : ℕ) (h : K → ℝ) (x : Fin n₀ → K) (y : Fin n₁ → K)
    (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁)),
    0 < n₀ → 0 < n₁ → Measurable h → Monotone (h ∘ x ∘ σ₀) → Monotone (h ∘ y ∘ σ₁) →
      wassersteinEDist 2 ((empMeas x).map h) ((empMeas y).map h) ^ 2 =
        ENNReal.ofReal (projCost h x y (nwLift σ₀ σ₁))

/-- `lem:delta-inf`, linear rules: `E_γ⟨w, X − Y⟩² = wᵀ M_γ w`. -/
def linear_cost : Prop :=
  ∀ (d n₀ n₁ : ℕ) (x : Fin n₀ → Fin d → ℝ) (y : Fin n₁ → Fin d → ℝ) (w : Fin d → ℝ)
    (γ : Fin n₀ → Fin n₁ → ℝ),
    projCost (fun z => w ⬝ᵥ z) x y γ = w ⬝ᵥ (secondMoment x y γ *ᵥ w)

/-- `lem:lindsay`: `L(m̂) ≤ Λ^𝒩_s ≤ L(m̂) + log sup_{m ∈ 𝓜} ∫ D_{m̂} dm` (finite `L`). -/
def lindsay_sandwich : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (ι : Type) [Fintype ι] (n : ℕ) (κ : ι → Measure K)
    (φ : Fin n → K → ℝ) (M : Set (ι → ℝ)) (mh : ι → ℝ),
    MixSetting κ φ → M ⊆ probSimplex ι → mh ∈ M →
      npmleObj κ φ mh ≤ lambdaN κ φ M ∧
        lambdaN κ φ M ≤ npmleObj κ φ mh + Real.log (lindsaySup κ φ M mh)

/-- `lem:lindsay`: equality throughout at a maximiser of `L` over a convex `𝓜`. -/
def lindsay_maximiser : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (ι : Type) [Fintype ι] (n : ℕ) (κ : ι → Measure K)
    (φ : Fin n → K → ℝ) (M : Set (ι → ℝ)) (mh : ι → ℝ),
    MixSetting κ φ → M ⊆ probSimplex ι → Convex ℝ M → mh ∈ M →
    (∀ m ∈ M, npmleObj κ φ m ≤ npmleObj κ φ mh) →
      lambdaN κ φ M = npmleObj κ φ mh ∧ lindsaySup κ φ M mh = 1

/-- `lem:lindsay`: the supremum on the right is attained at an extreme point of `𝓜`. -/
def lindsay_extreme : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (ι : Type) [Fintype ι] (n : ℕ) (κ : ι → Measure K)
    (φ : Fin n → K → ℝ) (M : Set (ι → ℝ)) (mh : ι → ℝ),
    MixSetting κ φ → M ⊆ probSimplex ι → Convex ℝ M → IsClosed M → mh ∈ M →
      ∃ m ∈ M.extremePoints ℝ, lindsaySup κ φ M mh = ∑ y, m y * lindsayD κ φ mh y

/-- `lem:lindsay`: for `𝓜 = 𝒫(L)` the supremum is attained at a point `y ∈ L` (a Dirac mass). -/
def lindsay_dirac : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (ι : Type) [Fintype ι] (n : ℕ) (κ : ι → Measure K)
    (φ : Fin n → K → ℝ) (mh : ι → ℝ),
    MixSetting κ φ → mh ∈ probSimplex ι →
      ∃ y, lindsaySup κ φ (probSimplex ι) mh = lindsayD κ φ mh y ∧
        ∀ y', lindsayD κ φ mh y' ≤ lindsayD κ φ mh y

end Claims
end StatFormal.Wave9a
