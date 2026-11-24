import StatFormal.Archive.RobustEquality.Certificate.Statements
import StatFormal.Archive.TrimmedMMD.Projection.Statements
import StatFormal.Archive.TrimmedMMD.Concentration.Statements
import StatFormal.Archive.TrimmedMMD.BangBang.Statements
import StatFormal.Archive.TrimmedMMD.ZeroSet.Statements
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Probability.CDF

/-!
# FROZEN STATEMENTS — wave 4b (QUEUE rows 39, 41, 42, 43)

Sources (verbatim in `lean-formalisation/inventory/extracted/robust-equality-paper2.md`,
`data-fairness-repair.md`, `trimmed-mmd.md`):
* robust equality, paper 2 `thm:certificate` (`robust-equality-outcomes-under-distribution-shift/
  paper2/main.tex:254-260`), with `eq:BN` (`:220-225`), structured sets `𝒮_Θ` (`:234-238`), `eq:F`
  (`:240-243`), `eq:T` (`:246-251`); and the JASA structured certificate `thm:cs-certificate`
  (`jasa/supp_common_shift.tex:141-151`, `def:cs-set` `:95-112`, transported classes
  `𝒩_θ = {𝔗_θ ν}`), which is the same slice argument;
* Schrödinger-bridge repair `cor:smoothing` (`data-fairness-repair/
  schrodinger_bridge_fairness_repair.tex:479-491`), with `eq:convolution` (`:466-469`);
* trimmed MMD `prop:witnessstab` (`trimmed-mmd/paper.tex:1536-1570`, `eq:etadef`, `eq:witnessstab`)
  and `prop:deletionfloor` (`paper.tex:2147-2157`, with `eq:trimset` `:75-83`).

Covered:
* `certificate_independent`: `F(h) ≤ F̄(h;λ)` for independent sets `B^𝒩(P̂_s; r_s)` (classes of
  references, `ε > 0`), the recalled certificate, in squared form;
* `certificate_structured`: the "slice by slice" clause, `F_Θ(h) ≤ sup_θ F̄_θ(h;λ)`, with
  `Δ_θ`, `T^θ_s` computed on the transported centres `𝔗_θ P̂_s`, slice classes `𝒩_s(θ)` and
  radii `r_s(θ)` (any `Θ`, any maps `𝔗_θ : K → K`);
* `cs_slice_T` and `cs_certificate` (JASA `thm:cs-certificate`): for the transported class
  `𝒩_θ = {𝔗_θ#ν : ν ∈ 𝒩}` the slice term equals the pulled-back formula of the paper
  (`f^θ_h`, `c^θ`), and `F_Θ(h) ≤ sup_θ inf_{λ₀,λ₁>0} (Δ_θ + √T^θ_0 + √T^θ_1)²`;
* `smoothing_density`: `μ_t = ρ_t ∗ N(0, εt(1−t) I_d)` has a continuous density `ρ` with
  `0 < ρ ≤ (2πεt(1−t))^{-d/2}` everywhere, for any probability plan on `ℝ^d × ℝ^d`;
* `smoothing_density_one`, `smoothing_cdf`: the same for `d = 1` with Mathlib's `gaussianReal`,
  and `F_{μ_t}` is continuous, strictly increasing, with range exactly `(0,1)` (a bijection
  `ℝ → (0,1)`);
* `witnessstab`: on one measurable event of probability `≥ 1 − δ`, every empirical witness
  satisfies `|D̂ − D| ≤ η`, `‖d̂ − d*‖ ≤ η + √(2η min(D,D̂) + η²) ≤ √(2ηD) + 2η`, and
  `sup_x |d̂(x) − d*(x)| ≤ κ‖d̂ − d*‖`;
* `deletionfloor`, `deletionfloor_conf`: `TV(P',Q') ≥ (TV(P,Q) − α)/(1 − α)`; for any
  `L ≤ TV(P,Q)` the floor `(L−α)/(1−α)` holds, and `P' = Q'` forces `α ≥ L`.

Not covered (declared):
* row 39: the `ε = 0` reading of `eq:T` (`T⁰`, sup over `supp ν`), anisotropic sets, `K = ℝ^d`
  for linear rules, the equivalence of the `lem:kernel` witness with the entropic-OT ball
  (inherited from the frozen certificate);
* row 41: `C^∞` and bounded derivatives of `ρ`, smoothness of `F_{μ_t}` and of `F^{-1}_{μ_t}`;
  for `d ≥ 2` the Gaussian is the explicit Lebesgue density, not Mathlib's `multivariateGaussian`;
* row 42: the rate `O_P((n∧m)^{-1/4})` (`eq:witnessrate`), `D ≤ 2κ`, existence/uniqueness of
  `d*` (the claim is for every minimum-norm `d*`; existence needs closedness of `𝒞_{α,k}(P)`);
* row 43: the probabilistic wording "with that confidence" beyond the deterministic implication
  `L ≤ TV(P,Q) ⇒ …` (which holds on whatever event `L` is valid).

Encodings:
* row 39: frozen `Certificate` setting (`centre`, `KernelWitness`, `Tref1`; cost `c` bounded
  measurable nonnegative; references finite with `0 < ν(K) ≤ 1`, `RefClass`). `Q ∈ B^𝒩(P̂;r)` is
  `InBall`: `Q` a probability measure with a `lem:kernel` witness at some `ν ∈ 𝒩`. All
  quantities in `ℝ≥0∞`: `W₂ = wassersteinEDist 2`; `√T^𝒩_s := ⨆_{ν∈𝒩} ofReal √(T^{ν}_s)` (for
  `λε > 0`, `T^𝒩 = sup_ν T^{ν}`; an unbounded sup gives `⊤`, a trivially true bound, not a junk
  `0`); `F` and `F_Θ` are `⨆` over admissible pairs (empty sets give `0`, so non-emptiness is not
  assumed). The transported centre `𝔗_θ P̂_s` is the empirical law of the points `𝔗_θ x_i`.
  `Θ` is any type (paper: compact), `λ` fixed across slices as printed in paper 2.
* row 41: `ρ_t = plan.map ((x,y) ↦ (1−t)x + ty)` for an arbitrary probability measure `plan`
  (marginals and `𝒫₂` are not used); `∗` is Mathlib's `Measure.conv`; `ℝ^d` is
  `EuclideanSpace ℝ (Fin d)` with its `volume`; `N(0, v I_d)` is `gaussianIso d v`, the measure with
  density `(2πv)^{-d/2} exp(−‖z‖²/(2v))`; for `d = 1`, `gaussianReal 0 v`. "Has a density `ρ`
  that is strictly positive … `‖ρ‖_∞ ≤ …`" is "equals `volume.withDensity ρ` for a continuous `ρ`
  with these pointwise bounds". `F_{μ_t}` is Mathlib's `cdf`.
* row 42: frozen `Concentration` setting (`region`, `empirical`, `rn`), samples
  `(X, Y) ∼ P^{⊗n} ⊗ Q^{⊗m}`; `η_{n,m} = r_n(α,δ/2) + r_m(β,δ/2)` (`etaNM`; `rn` has
  `log(2/δ)`, so this is `eq:etadef`); the empirical witness is `d̂ = Σ w_i φ(X_i) − Σ v_j φ(Y_j)`
  at any minimiser `(w,v)` of the frozen `BangBang.qp` over the capped simplices
  (`prop:bangbang`(i)); `d*` is any `IsMinNorm` element of `𝒞_{α,k}(P) − 𝒞_{β,k}(Q)`;
  `d(x) = ⟨d, φ(x)⟩`. Added hypothesis: singletons of `𝒳` are measurable (otherwise
  `𝒞(P_n)` can be smaller than the QP's feasible set). "With probability `≥ 1−δ`" = a measurable
  event of probability `≥ 1 − δ`.
* row 43: `R_α(P)` = `P.withDensity g` with the frozen `ZeroSet.IsTrimDensity`; `TV` is
  `Distances.tvDist`; `α ∈ [0,1)` so the division is by a positive number.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes
`Wave4b/Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
Critic notes: `deletionfloor_conf` is a faithful encoding (event transfer `{L ≤ TV} ⊆ {every repair has TV(P′,Q′) ≥ (L−α)/(1−α)}`,
universal in the repair, so data-dependent repairs are covered; "with that confidence" follows by monotonicity) — not a weakening.
`witnessstab` needs `MeasurableSingletonClass` (with the trivial σ-algebra `𝒞(P_n)` is a point while the QP ranges over the capped
simplex) and takes the minimum-norm element as given (existence = `lem:attainment`, not proved here).
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set
open scoped ENNReal NNReal Pointwise

namespace StatFormal.Wave4b

/-! ## Robust equality, paper 2 `thm:certificate` and JASA `thm:cs-certificate` -/

section RobustEquality
open StatFormal.RobustEquality.Certificate

variable {K : Type} [MeasurableSpace K]

/-- A class of admissible references: finite measures with `0 < ν(K) ≤ 1`. -/
def RefClass (N : Set (Measure K)) : Prop :=
  ∀ ν ∈ N, IsFiniteMeasure ν ∧ ν Set.univ ≠ 0 ∧ ν Set.univ ≤ 1

/-- `Q ∈ B^𝒩(P̂; r)` (`eq:BN`), via the `lem:kernel` witness at some reference `ν ∈ 𝒩`. -/
def InBall {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (ε r : ℝ) (N : Set (Measure K))
    (Q : Measure K) : Prop :=
  IsProbabilityMeasure Q ∧ ∃ ν ∈ N, KernelWitness x c ε r ν Q

/-- `√T^𝒩_s(h,λ) = ⨆_{ν ∈ 𝒩} √(T^{ν}_s(h,λ))` in `ℝ≥0∞` (`eq:T`). -/
def sqrtT {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (ε r lam : ℝ)
    (N : Set (Measure K)) : ℝ≥0∞ :=
  ⨆ ν ∈ N, ENNReal.ofReal (√(Tref1 x c h ε r lam ν))

/-- Nominal disparity `Δ(h) = W₂(h#P̂₀, h#P̂₁)`. -/
def nominal {n₀ n₁ : ℕ} (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (h : K → ℝ) : ℝ≥0∞ :=
  wassersteinEDist 2 ((centre x₀).map h) ((centre x₁).map h)

/-- `F̄(h;λ) = (Δ(h) + √T₀(h,λ₀) + √T₁(h,λ₁))²`. -/
def Fbar {n₀ n₁ : ℕ} (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (c : K → K → ℝ) (ε r₀ r₁ : ℝ)
    (N₀ N₁ : Set (Measure K)) (h : K → ℝ) (lam₀ lam₁ : ℝ) : ℝ≥0∞ :=
  (nominal x₀ x₁ h + sqrtT x₀ c h ε r₀ lam₀ N₀ + sqrtT x₁ c h ε r₁ lam₁ N₁) ^ 2

/-- `F(h) = sup_{(Q₀,Q₁) ∈ B₀ × B₁} W₂²(h#Q₀, h#Q₁)` for independent sets (`eq:F`). -/
def Findep {n₀ n₁ : ℕ} (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (c : K → K → ℝ) (ε r₀ r₁ : ℝ)
    (N₀ N₁ : Set (Measure K)) (h : K → ℝ) : ℝ≥0∞ :=
  ⨆ (Q₀ : Measure K) (Q₁ : Measure K)
    (_ : InBall x₀ c ε r₀ N₀ Q₀ ∧ InBall x₁ c ε r₁ N₁ Q₁),
    wassersteinEDist 2 (Q₀.map h) (Q₁.map h) ^ 2

/-- `F_Θ(h)`: the supremum over the structured set
`𝒮_Θ = ⋃_θ B^{𝒩₀(θ)}(𝔗_θ P̂₀; r₀(θ)) × B^{𝒩₁(θ)}(𝔗_θ P̂₁; r₁(θ))`. -/
def Fstruct {Θ : Type} {n₀ n₁ : ℕ} (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (c : K → K → ℝ)
    (ε : ℝ) (𝔗 : Θ → K → K) (r₀ r₁ : Θ → ℝ) (N₀ N₁ : Θ → Set (Measure K)) (h : K → ℝ) :
    ℝ≥0∞ :=
  ⨆ (Q₀ : Measure K) (Q₁ : Measure K)
    (_ : ∃ θ, InBall (fun i => 𝔗 θ (x₀ i)) c ε (r₀ θ) (N₀ θ) Q₀ ∧
      InBall (fun i => 𝔗 θ (x₁ i)) c ε (r₁ θ) (N₁ θ) Q₁),
    wassersteinEDist 2 (Q₀.map h) (Q₁.map h) ^ 2

/-- JASA's slice term at a reference `ν` in original coordinates:
`λr + λε n⁻¹ Σ_i log E_ν exp{(f^θ_h(x_i,·) − λ c^θ(x_i,·))/(λε)}`, with
`f^θ_h(x₀,x) = (h(𝔗x) − h(𝔗x₀))²`, `c^θ(x₀,x) = c(𝔗x₀, 𝔗x)`. -/
def TrefPull {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (𝔗 : K → K) (ε r lam : ℝ)
    (ν : Measure K) : ℝ :=
  lam * r + lam * ε * ((n : ℝ)⁻¹ * ∑ i, Real.log (∫ z, Real.exp
    (((h (𝔗 z) - h (𝔗 (x i))) ^ 2 - lam * c (𝔗 (x i)) (𝔗 z)) / (lam * ε)) ∂ν))

/-- `√T^θ_s(h,λ) = ⨆_{ν ∈ 𝒩} √(T^θ_s)` with the pulled-back formula (JASA). -/
def sqrtTPull {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (𝔗 : K → K) (ε r lam : ℝ)
    (N : Set (Measure K)) : ℝ≥0∞ :=
  ⨆ ν ∈ N, ENNReal.ofReal (√(TrefPull x c h 𝔗 ε r lam ν))

end RobustEquality

/-! ## Schrödinger-bridge repair `cor:smoothing` -/

section Smoothing

/-- Density of `N(0, v I_d)` on `ℝ^d`: `(2πv)^{-d/2} exp(−‖z‖²/(2v))`. -/
def gaussDensity (d : ℕ) (v : ℝ) (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (2 * Real.pi * v) ^ (-(d : ℝ) / 2) * Real.exp (-(‖z‖ ^ 2) / (2 * v))

/-- `N(0, v I_d)` as a measure on `ℝ^d`. -/
def gaussianIso (d : ℕ) (v : ℝ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  volume.withDensity (fun z => ENNReal.ofReal (gaussDensity d v z))

/-- `eq:convolution`: `μ_t = ρ_t ∗ N(0, εt(1−t) I_d)`, `ρ_t` the law of `(1−t)X₀ + tX₁`,
`(X₀,X₁) ∼ plan`. -/
def endpointMixture (d : ℕ) (ε t : ℝ) (plan : Measure (EuclideanSpace ℝ (Fin d) ×
    EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (plan.map (fun p => (1 - t) • p.1 + t • p.2)) ∗ gaussianIso d (ε * t * (1 - t))

/-- `eq:convolution` in dimension one, with Mathlib's Gaussian `N(0, εt(1−t))`. -/
def endpointMixture1 (ε t : ℝ) (plan : Measure (ℝ × ℝ)) : Measure ℝ :=
  (plan.map (fun p => (1 - t) * p.1 + t * p.2)) ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal

end Smoothing

/-! ## Trimmed MMD `prop:witnessstab` -/

section Witness

/-- `eq:etadef`: `η_{n,m}(α,β,δ) = r_n(α,δ/2) + r_m(β,δ/2)`. -/
def etaNM (κ α β δ : ℝ) (n m : ℕ) : ℝ :=
  StatFormal.TrimmedMMD.rn κ α (δ / 2) n + StatFormal.TrimmedMMD.rn κ β (δ / 2) m

/-- The empirical witness `Σ w_i φ(x_i) − Σ v_j φ(y_j)` at weights `p = (w,v)`. -/
def witness {𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H)
    {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (p : (Fin n → ℝ) × (Fin m → ℝ)) : H :=
  ∑ i, p.1 i • φ (x i) - ∑ j, p.2 j • φ (y j)

end Witness

namespace Claims

open StatFormal.RobustEquality.Certificate StatFormal.TrimmedMMD.Concentration
  StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.Projection StatFormal.TrimmedMMD.ZeroSet

/-! ### Robust equality (paper 2 `thm:certificate`, JASA `thm:cs-certificate`) -/

/-- Paper 2 `thm:certificate`, independent sets: `F(h) ≤ F̄(h;λ)` for every bounded measurable
rule and every `λ₀, λ₁ > 0`. -/
def certificate_independent : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n₀ n₁ : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K)
    (c : K → K → ℝ) (ε r₀ r₁ lam₀ lam₁ : ℝ) (h : K → ℝ) (N₀ N₁ : Set (Measure K)),
    0 < n₀ → 0 < n₁ → 0 < ε → 0 < lam₀ → 0 < lam₁ →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    Measurable h → (∃ H, ∀ z, |h z| ≤ H) → RefClass N₀ → RefClass N₁ →
      Findep x₀ x₁ c ε r₀ r₁ N₀ N₁ h ≤ Fbar x₀ x₁ c ε r₀ r₁ N₀ N₁ h lam₀ lam₁

/-- Paper 2 `thm:certificate`, structured sets ("slice by slice"):
`F_Θ(h) ≤ sup_θ F̄_θ(h;λ)`, `Δ_θ`, `T^θ_s` on the transported centres and slice classes. -/
def certificate_structured : Prop :=
  ∀ (K Θ : Type) [MeasurableSpace K] (n₀ n₁ : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K)
    (c : K → K → ℝ) (ε lam₀ lam₁ : ℝ) (r₀ r₁ : Θ → ℝ) (𝔗 : Θ → K → K) (h : K → ℝ)
    (N₀ N₁ : Θ → Set (Measure K)),
    0 < n₀ → 0 < n₁ → 0 < ε → 0 < lam₀ → 0 < lam₁ →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    Measurable h → (∃ H, ∀ z, |h z| ≤ H) → (∀ θ, RefClass (N₀ θ)) → (∀ θ, RefClass (N₁ θ)) →
      Fstruct x₀ x₁ c ε 𝔗 r₀ r₁ N₀ N₁ h ≤
        ⨆ θ, Fbar (fun i => 𝔗 θ (x₀ i)) (fun i => 𝔗 θ (x₁ i)) c ε (r₀ θ) (r₁ θ) (N₀ θ) (N₁ θ)
          h lam₀ lam₁

/-- JASA `thm:cs-certificate`, change of variables: at the transported reference `𝔗#ν` the slice
term on the transported centre is the pulled-back formula. -/
def cs_slice_T : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ)
    (𝔗 : K → K) (ε r lam : ℝ) (ν : Measure K),
    Measurable (Function.uncurry c) → Measurable h → Measurable 𝔗 →
      Tref1 (fun i => 𝔗 (x i)) c h ε r lam (ν.map 𝔗) = TrefPull x c h 𝔗 ε r lam ν

/-- JASA `thm:cs-certificate`, consequence: with transported classes `𝒩_θ = {𝔗_θ#ν : ν ∈ 𝒩_s}`,
`F_Θ(h) ≤ sup_θ inf_{λ₀,λ₁>0} (Δ_θ(h) + √T^θ₀ + √T^θ₁)²`. -/
def cs_certificate : Prop :=
  ∀ (K Θ : Type) [MeasurableSpace K] (n₀ n₁ : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K)
    (c : K → K → ℝ) (ε : ℝ) (r₀ r₁ : Θ → ℝ) (𝔗 : Θ → K → K) (h : K → ℝ)
    (N₀ N₁ : Set (Measure K)),
    0 < n₀ → 0 < n₁ → 0 < ε →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    Measurable h → (∃ H, ∀ z, |h z| ≤ H) → (∀ θ, Measurable (𝔗 θ)) →
    RefClass N₀ → RefClass N₁ →
      Fstruct x₀ x₁ c ε 𝔗 r₀ r₁ (fun θ => (fun ν => ν.map (𝔗 θ)) '' N₀)
          (fun θ => (fun ν => ν.map (𝔗 θ)) '' N₁) h ≤
        ⨆ θ, ⨅ (lam₀ : ℝ) (_ : 0 < lam₀) (lam₁ : ℝ) (_ : 0 < lam₁),
          (nominal (fun i => 𝔗 θ (x₀ i)) (fun i => 𝔗 θ (x₁ i)) h +
            sqrtTPull x₀ c h (𝔗 θ) ε (r₀ θ) lam₀ N₀ + sqrtTPull x₁ c h (𝔗 θ) ε (r₁ θ) lam₁ N₁) ^ 2

/-! ### Schrödinger-bridge repair (`cor:smoothing`) -/

/-- `cor:smoothing`, `ℝ^d`: `μ_t` has a continuous density with `0 < ρ ≤ (2πεt(1−t))^{-d/2}`. -/
def smoothing_density : Prop :=
  ∀ (d : ℕ) (ε t : ℝ) (plan : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure plan], 0 < ε → 0 < t → t < 1 →
      ∃ ρ : EuclideanSpace ℝ (Fin d) → ℝ, Continuous ρ ∧
        endpointMixture d ε t plan = volume.withDensity (fun y => ENNReal.ofReal (ρ y)) ∧
        ∀ y, 0 < ρ y ∧ ρ y ≤ (2 * Real.pi * (ε * t * (1 - t))) ^ (-(d : ℝ) / 2)

/-- `cor:smoothing`, `d = 1` with Mathlib's Gaussian: continuous density,
`0 < ρ ≤ (2πεt(1−t))^{-1/2}`. -/
def smoothing_density_one : Prop :=
  ∀ (ε t : ℝ) (plan : Measure (ℝ × ℝ)) [IsProbabilityMeasure plan], 0 < ε → 0 < t → t < 1 →
    ∃ ρ : ℝ → ℝ, Continuous ρ ∧
      endpointMixture1 ε t plan = volume.withDensity (fun y => ENNReal.ofReal (ρ y)) ∧
      ∀ y, 0 < ρ y ∧ ρ y ≤ (2 * Real.pi * (ε * t * (1 - t))) ^ (-(1 : ℝ) / 2)

/-- `cor:smoothing`, `d = 1`: `F_{μ_t}` is a continuous strictly increasing bijection
`ℝ → (0,1)`. -/
def smoothing_cdf : Prop :=
  ∀ (ε t : ℝ) (plan : Measure (ℝ × ℝ)) [IsProbabilityMeasure plan], 0 < ε → 0 < t → t < 1 →
    StrictMono (cdf (endpointMixture1 ε t plan)) ∧ Continuous (cdf (endpointMixture1 ε t plan)) ∧
      Set.range (cdf (endpointMixture1 ε t plan)) = Ioo 0 1

/-! ### Trimmed MMD (`prop:witnessstab`, `prop:deletionfloor`) -/

/-- `prop:witnessstab`: on one measurable event of probability `≥ 1 − δ`, every empirical witness
`d̂` (any minimiser of `eq:qp`) and every minimum-norm `d*` of `𝒞_{α,k}(P) − 𝒞_{β,k}(Q)` satisfy
`eq:witnessstab` and the sup-norm bound. -/
def witnessstab : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H)
    (κ α β δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 0 ≤ β → β < 1 → 1 ≤ n → 1 ≤ m →
    0 < δ → δ < 1 →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤
          ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | ∀ (p : (Fin n → ℝ) × (Fin m → ℝ)) (dstar : H),
          p ∈ capped n α ×ˢ capped m β →
          IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m β) p →
          IsMinNorm (region φ α P - region φ β Q) dstar →
            |‖witness φ z.1 z.2 p‖ - ‖dstar‖| ≤ etaNM κ α β δ n m ∧
            ‖witness φ z.1 z.2 p - dstar‖ ≤ etaNM κ α β δ n m +
              √(2 * etaNM κ α β δ n m * min ‖dstar‖ ‖witness φ z.1 z.2 p‖ +
                etaNM κ α β δ n m ^ 2) ∧
            etaNM κ α β δ n m + √(2 * etaNM κ α β δ n m * min ‖dstar‖ ‖witness φ z.1 z.2 p‖ +
                etaNM κ α β δ n m ^ 2) ≤
              √(2 * etaNM κ α β δ n m * ‖dstar‖) + 2 * etaNM κ α β δ n m ∧
            ∀ x, |inner ℝ (witness φ z.1 z.2 p) (φ x) - inner ℝ dstar (φ x)| ≤
              κ * ‖witness φ z.1 z.2 p - dstar‖}

/-- `prop:deletionfloor`: for `P' ∈ R_α(P)`, `Q' ∈ R_α(Q)`, `TV(P',Q') ≥ (TV(P,Q) − α)/(1 − α)`. -/
def deletionfloor : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (α : ℝ) (gP gQ : 𝒳 → ℝ), 0 ≤ α → α < 1 →
    IsTrimDensity P α gP → IsTrimDensity Q α gQ →
      (StatFormal.Distances.tvDist P Q - α) / (1 - α) ≤
        StatFormal.Distances.tvDist (P.withDensity fun x => ENNReal.ofReal (gP x))
          (Q.withDensity fun x => ENNReal.ofReal (gQ x))

/-- `prop:deletionfloor`, consequences: for any `L ≤ TV(P,Q)`, every deletion repair leaves
`TV(P',Q') ≥ (L − α)/(1 − α)`, and identical repaired groups force `α ≥ L`. -/
def deletionfloor_conf : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (α L : ℝ) (gP gQ : 𝒳 → ℝ), 0 ≤ α → α < 1 →
    IsTrimDensity P α gP → IsTrimDensity Q α gQ → L ≤ StatFormal.Distances.tvDist P Q →
      (L - α) / (1 - α) ≤
        StatFormal.Distances.tvDist (P.withDensity fun x => ENNReal.ofReal (gP x))
          (Q.withDensity fun x => ENNReal.ofReal (gQ x)) ∧
      (P.withDensity (fun x => ENNReal.ofReal (gP x)) =
          Q.withDensity (fun x => ENNReal.ofReal (gQ x)) → L ≤ α)

end Claims

end StatFormal.Wave4b
