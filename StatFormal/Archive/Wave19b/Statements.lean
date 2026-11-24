import StatFormal.Archive.Wave17a.Statements
import StatFormal.Archive.RobustEquality.Tax.Statements
import StatFormal.Archive.RobustEquality.Strong.Statements
import StatFormal.Archive.Wave18a.Statements
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# FROZEN STATEMENTS — wave 19b (QUEUE rows 204–208, 212): robust equality JASA `lem:fl-identities`,
# `thm:fl-coverage`, `prop:ep-nested`, `lem:sc-proj`, `lem:cert-structure`; NN `lem:noncentral`

Sources (verbatim in `lean-formalisation/inventory/extracted/robust-equality-jasa.md`, `proliferation-nns.md`; current
text after the 2026-10-13/14/15 corrections; JASA paths under `robust-equality-outcomes-under-distribution-shift/jasa/`):
* JASA `lem:fl-identities` (`supp_calibration.tex:56-68`, proof `:70-76`), with `eq:floorid` and the Gibbs kernel
  `K^ν` (`supp_proofs.tex:185-196`), the floor `ρ_ν` and the reference convention `0 < ν(K) ≤ 1`
  (`supp_proofs.tex:15-33`), `T^{{ν}}` = `eq:T` at one reference (frozen `Certificate.Tref1`).
* JASA `thm:fl-coverage` (`supp_calibration.tex:143-155`, proof `:157-162`), with `lem:fl-price` (`:84-91`),
  `prop:fl-radius` (`:119-141`) and `thm:certificate` (`main.tex`, frozen `Certificate.certificate`).
* JASA `prop:ep-nested` (`supp_eps.tex:149-158`, proof `:160-170`), with `G^ν_ε`, `R_ε`, `T_ε` (file header
  `supp_eps.tex:6-16`) and `def:ep-member`, `T^0` of `thm:ep-cert0` (`:40-59`, `:65-71`).
* JASA `lem:sc-proj` (`supp_spectrum_cases.tex:58-66`, proof `:68-73`).
* JASA `lem:cert-structure` (`supp_calibration.tex:474-480`, proof `:482-486`), with `g_f`, `J_Q`, `Gap_Q`
  (`supp_proofs.tex:35-45`).
* NN `lem:noncentral` (`proliferation-and-geometry-in-nns/paper_revised.tex:1804-1811`, proof `:1813-1820`).
Imports the frozen `Wave17a` (`ncChiSq`, `isoGauss`), `Wave18a` (`jitterPrice`), `RobustEquality/Tax` (`Wdisc`; through it `SemidualStrong`:
`OTdisc`, `Jdual`, `Setting`; `Semidual`: `gsoft`, `muDisc`; base: `klRef`) and `RobustEquality/Strong` (`floorRef`;
through it `Certificate`: `Tref1`, `centre`, `KernelWitness`) statements, not copied; Mathlib and Tau Ceti
(`TauCeti.wassersteinEDist`) otherwise. No `Foundations` file.

Covered:
* `lem:fl-identities`: (i) `fl_identities_i` (`W^ν_ε(μ,Q) = ρ_ν + ε inf_{γ∈Π(μ,Q)} KL(γ‖μ⊗K^ν)`, `EReal`),
  `fl_identities_i_dp` (`≥ ρ_ν + ε KL(Q‖μK^ν)`); (ii) `fl_identities_ii` (`T^{{ν}}(h,λ) = λ(r − ρ_λ)`),
  `fl_identities_ii_mono` (`ρ_λ` nondecreasing on `(0,∞)`, `ρ_λ ≤ ρ_ν`, `ρ_λ → ρ_ν`), `fl_identities_linear`
  (`ρ_{|w|²} = ρ_⊥`; the three-term decomposition for the actual `W = W^ν_ε(μ,P)`; directional gap `ρ_ν − ρ_⊥ ≥ 0`),
  `fl_identities_excess` (population excess `W − ρ_ν ≥ 0`, bounded cost).
* `thm:fl-coverage`: `fl_coverage` — CONDITIONAL: `prop:fl-radius` is ASSUMED (hypothesis), not proved.
* `prop:ep-nested`: (i) `ep_nested_G` (`G^ν_{ε'} ≤ G^ν_ε`), `ep_nested_G0` (`G^ν_0 ≤ G^ν_ε`), `ep_nested_balls`
  (`𝓑_ε ⊆ 𝓑_{ε'} ⊆ 𝓑_0`), `ep_nested_floor` (`R_0 ≤ R_{ε'} ≤ R_ε`); (ii) `ep_nested_T` (`T_ε ≤ T_{ε'} ≤ T^0`, and the
  optimised certificate); (iii) `ep_nested_F`.
* `lem:sc-proj`: `sc_proj` (both inequalities).
* `lem:cert-structure`: `cert_structure_i`, `cert_structure_ii_grad`, `cert_structure_ii_gap`, `cert_structure_iii`.
* NN `lem:noncentral`: `noncentral` (the law), `noncentral_minnorm` (the minimum-norm point `z₀` exists, is unique in
  `A ∩ V^⊥`, and `‖z₀‖ = dist(0, A)`), `noncentral_decomp` (the proof's `dist(X, A) = ‖X_⊥ − z₀‖`). This EXTENDS the
  certified Wave 17a core `noncentral_tube_affine` (CDF at `δ > 0` with `λ = dist(0,V)²/σ²`): equality of laws, with
  the paper's `‖z₀‖`; the route reuses that certified theorem.

Not covered (declared):
* **`prop:fl-radius` (assumed).** `fl_coverage` takes it as a hypothesis; it is not formalised (it rests on
  `prop:fl-negent` and `thm:coverage-general`; QUEUE estimate 10–15 d).
* fl-identities: the remark after the lemma ("of order `ε` times an entropy at scale `√ε`", heuristic).
* fl-coverage: `lem:fl-price` itself (certified in frozen Wave 18a; its `jitterPrice` is imported); the construction of `μ^θ_s` (fold points
  with `R` jitters), `ν^θ_s`, `r̂^θ_s` (any data-dependent discrete centres, references and radii are allowed); the
  `H_J` remark and the mortgage numbers.
* ep-nested: the identification of the closed-form floors with `min G^ν_ε` (`eq:floorid`) and `R_0 = min G^ν_0`;
  `ess sup_ν g = sup_{S_ν} g` for continuous `g` (only `≤` is used); the status paragraph after the proof.
* sc-proj: the three-step lower-bound procedure and Table numbers after the lemma.
* NN: the Poisson-mixture CDF and `eq:smalltube-noncentral` after the proof.

Encodings (to be checked by the critic):
* Centres are labelled atoms `μ = Σ_i a_i δ_i` on `Fin k` with costs `c_i = c(x_i,·)` (`muDisc`, frozen `Wdisc`,
  `OTdisc`); `(ii)` and `ep_nested_T` use the uniform centre of `Tref1`/`floorRef`. `K^ν_i = ν.tilted(−c_i/ε)` (Mathlib
  `tilted`: density `e^{−c_i/ε}/∫e^{−c_i/ε}dν`, genuine since `ν ≠ 0`, `c` bounded); `μ⊗K^ν = Σ_i a_i δ_i ⊗ K^ν_i`
  (`gibbsJoint`), `μK^ν = Σ_i a_i K^ν_i` (`gibbsMix`); `ρ_ν` weighted is `floorW` (`= floorRef` for `a_i = 1/n`).
  References: any finite `ν ≠ 0` in (i) (paper: `ν(K) ≤ 1`, generalisation); `ν(K) ≤ 1` where it is needed
  (ep-nested). KL is the frozen `klRef`, `inf` is `sInf` in `EReal` (`⊤` for no finite-KL coupling).
* `ρ_λ` (`rhoLam`), `ρ_⊥` (`rhoPerp`) with `P^⊥_w v = v − (⟨w,v⟩/|w|²)w` (`perpW`, `w ≠ 0`); the linear rule is
  `⟨w,·⟩ + b` and `c = ‖· − ·‖²` on `ℝ^d` (no boundedness needed: pointwise identities); the decomposition is stated
  for every real `W` (the paper's `W = W^ν_ε(μ,P)` whenever it is finite; it is an algebraic identity).
* fl-coverage: `ℝ^d = EuclideanSpace ℝ (Fin d)`; groups `s ∈ Fin 2`; grid `𝒢` a nonempty `Fintype`; the cost `c` is any
  bounded measurable `c ≥ 0` (paper: `‖·−·‖²` on the box `C_E`); `P_s ∗ U_θ` is Mathlib's `Measure.conv`; `π_h(U)` is
  the frozen `StatFormal.Wave18a.jitterPrice` (`ℝ≥0∞`); `prop:fl-radius` at level `α/(2|𝒢|)` is the hypothesis: measurable `Ev θ s` with
  `Pr(Ev θ s) ≥ 1 − α/(2|𝒢|)` on which `P_s ∗ U_θ` has a `lem:kernel` witness (`KernelWitness`, as in the frozen
  `prop:uniform`) for the centre `centre (x θ s ω)`, reference `ν θ s ω` (`0 < ν(K) ≤ 1`) and radius `r θ s ω`;
  `√F̄^θ = Δ^θ + √T^θ_0 + √T^θ_1` (non-squared form of the frozen certificate), `W₂` Tau Ceti's `wassersteinEDist 2`.
* ep-nested: `K` a second-countable metric Borel space (paper: compact `K ⊂ ℝ^d`), `c = dist²` bounded via `Setting`;
  `S_ν = ν.support` (Mathlib; `ν(S_νᶜ) = 0`); `G^ν_0(Q) = W₂²(P̂,Q)` if `Q(S_νᶜ) = 0`, else `⊤` (`G0`, `ℝ≥0∞ → EReal`
  coercion); `R_ε` is the closed form `floorW`, `R_0 = Σ a_i dist²(x_i,S_ν)` (`floorZero`; `S_ν ≠ ∅` when `ν ≠ 0`);
  `T_ε = Tref1` at `ε`, `T^0` (`T0`) uses `⨆_{z∈S_ν}` in `EReal` (no junk: not `⊥` for `ν ≠ 0`, bounded above);
  `h` only bounded measurable (paper: continuous; generalisation); `F_ε` is `worstDisp`, a `⨆` of `W₂²` in `ℝ≥0∞` over
  the two balls (`0` for an empty ball).
* sc-proj: `Π` is given by its defining property (`Π y ∈ K`, `‖y − Πy‖ = dist(y,K)`), its measurability is proved;
  the coupling is a probability `γ` on `Fin k × ℝ^d` with first marginal `μ` (`x_i ∈ K`), `law(X) = γ.map snd`,
  `(X₀,ΠX) = γ.map (id × Π)`; `I(X₀;X) = KL(γ‖μ⊗law X)` (`klRef`, probability reference); `E c(X₀,X) < ∞` is a
  hypothesis (integrability; Bochner junk otherwise); `ε ≥ 0`.
* cert-structure: `π_f(i|y) = postW` (positive), `KL` on labels `klFin` (only applied to positive vectors), `Gap_P(f) =
  OTdisc − J_P(f)` in `EReal` (finite by strong duality); `∇J_P(f)` is the Fréchet derivative `Σ_i gradJ_i e_i^*` on
  `Fin k → ℝ` (`HasFDerivAt`); `f*` any maximiser of `J_P`.
* NN: `N(0,σ²I)` is the frozen `isoGauss E σ` on a finite-dimensional real inner product space; `χ²_c(λ)` the frozen
  `ncChiSq`; `V = A.direction`, `x_⊥ = (V^⊥).starProjection x`; codimension `finrank E − finrank V` (genuine);
  `dist(X,A)` is `Metric.infDist`; the law is `Measure.map` of a continuous map.

Critic notes:
* All 21 claims are proved in `Wave19b/Route{FlIdentities,FlLambda,FlCoverage,EpNested,ScProj,CertStructure,
  Noncentral}.lean` (axioms: propext, Classical.choice, Quot.sound). Routes reuse the untrusted Foundations libraries
  `Tax/Tax` (`klRef_eq_klDiv`, `coe_mul_le_coe_mul`), `SemiDiscrete/{Primal,Convex,Dual}` (`foc_Jdual`,
  `Theta_eq_Jdual'`, `lse_ge`), the certified `Certificate.certificate`, `SemidualStrong.setting_hyp`, the certified Wave 18a
  `fl_price_bound` and the certified Wave 17a `noncentral_tube_affine` — routes only.
* Critic (2026-10-15): ACCEPT, all 21 TRUE. Junk-value fix: `fl_identities_linear` takes `P` a probability law with
  `E‖X‖² < ∞`, so `W = W^ν_ε(μ,P)` is a genuine value; `ep_nested_F` takes `h` measurable.
* (ii), `ii_mono` and `linear` specialise to the uniform centre `n⁻¹Σδ_{x_i}`, as the frozen `Tref1` does.
* `fl_coverage` is CONDITIONAL twice: on `prop:fl-radius` (assumed) and on the `lem:kernel` equivalence (ball
  membership as a `KernelWitness`), inherited from the frozen `prop:uniform`. The uniform centre covers the paper's
  construction when `w_v = |I_v|/n` (each fold point carrying `R` jitters).
* Paper S3: in `thm:fl-coverage`/`lem:fl-price` rules must be defined and bounded on `K + E ⊆ C_E`, and the
  certificate is applied over `𝒫(C_E)`, not `𝒫(K)` (here: rules on `ℝ^d`, bounded).
* Paper S4: `lem:fl-identities` says "discrete centre", but `T^{{ν}}` (`eq:T`) is defined only for uniform labelled
  centres; (i) is stated for weighted centres, (ii) for uniform ones.
* No statement of the six results was found false. Observations: ep-nested (ii)–(iii) need neither continuity of `h`
  nor `ess sup = sup` (only `ν(S_νᶜ) = 0`); fl-identities (i) needs neither `ν(K) ≤ 1` nor normalisation of `ν`;
  `thm:fl-coverage` is CONDITIONAL on `prop:fl-radius` (not certified, rated 10–15 d).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave19b

open StatFormal.RobustEquality StatFormal.RobustEquality.Semidual StatFormal.RobustEquality.SemidualStrong

/-! ### JASA `lem:fl-identities` -/

section FlIdentities
variable {K : Type*} [MeasurableSpace K] {k : ℕ}

/-- The Gibbs kernel `K^ν_i(dz) = e^{−c_i(z)/ε} ν(dz) / ∫ e^{−c_i/ε} dν` (`eq:floorid`). -/
def gibbsK (ε : ℝ) (c : Fin k → K → ℝ) (ν : Measure K) (i : Fin k) : Measure K :=
  ν.tilted fun z => -c i z / ε

/-- `μ ⊗ K^ν = Σ_i a_i δ_i ⊗ K^ν_i` on labels × `K`. -/
def gibbsJoint (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (ν : Measure K) : Measure (Fin k × K) :=
  ∑ i, ENNReal.ofReal (a i) • (Measure.dirac i).prod (gibbsK ε c ν i)

/-- `μK^ν = Σ_i a_i K^ν_i`, the second marginal of `μ ⊗ K^ν`. -/
def gibbsMix (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (ν : Measure K) : Measure K :=
  ∑ i, ENNReal.ofReal (a i) • gibbsK ε c ν i

/-- The floor `ρ_ν = −ε Σ_i a_i log ∫ e^{−c_i/ε} dν` for the weighted centre `μ = Σ_i a_i δ_i`. -/
def floorW (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (ν : Measure K) : ℝ :=
  -ε * ∑ i, a i * Real.log (∫ z, Real.exp (-c i z / ε) ∂ν)

/-- `ρ_λ = −ε n⁻¹ Σ_i log ∫ exp(f_h(x_i,·)/(λε) − c(x_i,·)/ε) dν`, `f_h(x₀,x) = (h(x) − h(x₀))²`. -/
def rhoLam {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (ε lam : ℝ) (ν : Measure K) : ℝ :=
  -ε * ((n : ℝ)⁻¹ * ∑ i, Real.log (∫ z, Real.exp ((h z - h (x i)) ^ 2 / (lam * ε) - c (x i) z / ε) ∂ν))

/-- `P^⊥_w v = v − (⟨w,v⟩/|w|²) w`, the projection orthogonal to `w`. -/
def perpW {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (w v : E) : E :=
  v - (⟪w, v⟫ / ‖w‖ ^ 2) • w

/-- `ρ_⊥ = −ε n⁻¹ Σ_i log ∫ e^{−‖P^⊥_w(z − x_i)‖²/ε} dν(z)`. -/
def rhoPerp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] {n : ℕ}
    (x : Fin n → E) (w : E) (ε : ℝ) (ν : Measure E) : ℝ :=
  -ε * ((n : ℝ)⁻¹ * ∑ i, Real.log (∫ z, Real.exp (-‖perpW w (z - x i)‖ ^ 2 / ε) ∂ν))

end FlIdentities

/-! ### JASA `thm:fl-coverage`: `π_h(U)` is the frozen `StatFormal.Wave18a.jitterPrice` (`lem:fl-price`). -/

/-! ### JASA `prop:ep-nested` -/

section EpNested
variable {K : Type*} [MetricSpace K] [MeasurableSpace K] {k : ℕ}

/-- The weighted centre `P̂ = Σ_i a_i δ_{x_i}` as a law on `K`. -/
def centreW (a : Fin k → ℝ) (x : Fin k → K) : Measure K := (muDisc a).map x

/-- `G^ν_0(Q) = W₂²(P̂, Q) + ι_{S_ν}(Q)` (`def:ep-member`), `S_ν = supp ν`. -/
def G0 (a : Fin k → ℝ) (x : Fin k → K) (ν Q : Measure K) : EReal :=
  if Q (ν.support)ᶜ = 0 then ((wassersteinEDist 2 (centreW a x) Q ^ 2 : ℝ≥0∞) : EReal) else ⊤

/-- The `ε = 0` floor `R_0 = E_{x₀∼P̂} dist²(x₀, S_ν)`. -/
def floorZero (a : Fin k → ℝ) (x : Fin k → K) (ν : Measure K) : ℝ :=
  ∑ i, a i * Metric.infDist (x i) ν.support ^ 2

/-- `T^0(λ; r) = λ r + E_{x₀∼P̂} sup_{x ∈ S_ν} [f_h(x₀,x) − λ c(x₀,x)]`, in `EReal`. -/
def T0 {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (r lam : ℝ) (ν : Measure K) : EReal :=
  ((lam * r : ℝ) : EReal) +
    (((n : ℝ)⁻¹ : ℝ) : EReal) * ∑ i, ⨆ z ∈ ν.support, (((h z - h (x i)) ^ 2 - lam * c (x i) z : ℝ) : EReal)

/-- `𝓑^ν_ε(r) = {Q ∈ 𝒫(K) : G^ν_ε(Q) ≤ r}`, `G^ν_ε(Q) = W^ν_ε(P̂, Q)`. -/
def ballEps (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (ν : Measure K) (r : ℝ) : Set (Measure K) :=
  {Q | IsProbabilityMeasure Q ∧ StatFormal.RobustEquality.Tax.Wdisc ε a c ν Q ≤ (r : EReal)}

/-- `𝓑^ν_0(r) = {Q ∈ 𝒫(K) : G^ν_0(Q) ≤ r}`. -/
def ball0 (a : Fin k → ℝ) (x : Fin k → K) (ν : Measure K) (r : ℝ) : Set (Measure K) :=
  {Q | IsProbabilityMeasure Q ∧ G0 a x ν Q ≤ (r : EReal)}

/-- The worst-case disparity `sup_{Q_0 ∈ 𝓑_0, Q_1 ∈ 𝓑_1} W₂²(h#Q_0, h#Q_1)`, in `ℝ≥0∞`. -/
def worstDisp (B₀ B₁ : Set (Measure K)) (h : K → ℝ) : ℝ≥0∞ :=
  ⨆ Q₀ ∈ B₀, ⨆ Q₁ ∈ B₁, wassersteinEDist 2 (Q₀.map h) (Q₁.map h) ^ 2

end EpNested

/-! ### JASA `lem:cert-structure` -/

section CertStructure
variable {K : Type*} [MeasurableSpace K] {k : ℕ}

/-- The posterior `π_f(i | y) = a_i e^{(f_i + g_f(y) − c_i(y))/ε}`. -/
def postW (ε : ℝ) (a f : Fin k → ℝ) (c : Fin k → K → ℝ) (i : Fin k) (y : K) : ℝ :=
  a i * Real.exp ((f i + gsoft ε a f c y - c i y) / ε)

/-- `KL(p ‖ q) = Σ_i p_i log(p_i/q_i)` on labels (used for positive vectors only). -/
def klFin (p q : Fin k → ℝ) : ℝ := ∑ i, p i * Real.log (p i / q i)

/-- `∇J_P(f) = a − E_P π_f(· | Y)`. -/
def gradJ (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (P : Measure K) (f : Fin k → ℝ) : Fin k → ℝ :=
  fun i => a i - ∫ y, postW ε a f c i y ∂P

end CertStructure

namespace Claims

open StatFormal.RobustEquality.Certificate StatFormal.RobustEquality.Strong
open StatFormal.Wave17a (ncChiSq isoGauss)

local notation "Wdisc" => StatFormal.RobustEquality.Tax.Wdisc

/-! #### JASA `lem:fl-identities` -/

/-- (i), identity: `W^ν_ε(μ, Q) = ρ_ν + ε inf_{γ ∈ Π(μ,Q)} KL(γ ‖ μ ⊗ K^ν)`. -/
def fl_identities_i : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (ν Q : Measure K) [IsFiniteMeasure ν] [IsProbabilityMeasure Q],
    Setting ε a c → ν Set.univ ≠ 0 →
      Wdisc ε a c ν Q = (floorW ε a c ν : EReal) + (ε : EReal) *
        sInf {v | ∃ γ : Measure (Fin k × K), IsProbabilityMeasure γ ∧ γ.map Prod.fst = muDisc a ∧
          γ.map Prod.snd = Q ∧ v = klRef γ (gibbsJoint ε a c ν)}

/-- (i), data processing onto the second coordinate: `W^ν_ε(μ, Q) ≥ ρ_ν + ε KL(Q ‖ μK^ν)`. -/
def fl_identities_i_dp : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (ν Q : Measure K) [IsFiniteMeasure ν] [IsProbabilityMeasure Q],
    Setting ε a c → ν Set.univ ≠ 0 →
      (floorW ε a c ν : EReal) + (ε : EReal) * klRef Q (gibbsMix ε a c ν) ≤ Wdisc ε a c ν Q

/-- (ii), identity: `T^{{ν}}(h, λ) = λ (r − ρ_λ)` for every rule and `λ > 0`. -/
def fl_identities_ii : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ)
    (ε r lam : ℝ) (ν : Measure K), 0 < ε → 0 < lam →
      Tref1 x c h ε r lam ν = lam * (r - rhoLam x c h ε lam ν)

/-- (ii), monotonicity: `λ ↦ ρ_λ` is nondecreasing on `(0, ∞)`, `ρ_λ ≤ ρ_ν`, and `ρ_λ → ρ_ν` as `λ → ∞`. -/
def fl_identities_ii_mono : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ)
    (ε : ℝ) (ν : Measure K) [IsFiniteMeasure ν],
    0 < n → 0 < ε → Measurable (Function.uncurry c) → (∃ B, ∀ a b, |c a b| ≤ B) →
    Measurable h → (∃ H, ∀ z, |h z| ≤ H) → ν Set.univ ≠ 0 →
      MonotoneOn (fun lam => rhoLam x c h ε lam ν) (Ioi 0) ∧
        (∀ lam, 0 < lam → rhoLam x c h ε lam ν ≤ floorRef x c ε ν) ∧
        Tendsto (fun lam => rhoLam x c h ε lam ν) atTop (𝓝 (floorRef x c ε ν))

/-- (ii), linear rule `h = ⟨w,·⟩ + b`, `c = ‖· − ·‖²`, `λ = |w|²`: `ρ_{|w|²} = ρ_⊥`; for the actual
`W = W^ν_ε(μ, P)` (when finite, `μ = n⁻¹Σδ_{x_i}`), `T(h, |w|²) = |w|²[(r − W) + (W − ρ_ν) + (ρ_ν − ρ_⊥)]`, and the
directional gap is nonnegative, `ρ_⊥ ≤ ρ_ν`. -/
def fl_identities_linear : Prop :=
  ∀ (d n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (w : EuclideanSpace ℝ (Fin d)) (b ε r W : ℝ)
    (ν P : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν] [IsProbabilityMeasure P],
    0 < n → 0 < ε → w ≠ 0 → ν Set.univ ≠ 0 → Integrable (fun z => ‖z‖ ^ 2) P →
    Wdisc ε (fun _ => (n : ℝ)⁻¹) (fun i z => ‖z - x i‖ ^ 2) ν P = (W : EReal) →
      rhoLam x (fun x₀ z => ‖z - x₀‖ ^ 2) (fun z => ⟪w, z⟫ + b) ε (‖w‖ ^ 2) ν = rhoPerp x w ε ν ∧
      Tref1 x (fun x₀ z => ‖z - x₀‖ ^ 2) (fun z => ⟪w, z⟫ + b) ε r (‖w‖ ^ 2) ν =
        ‖w‖ ^ 2 * ((r - W) + (W - floorRef x (fun x₀ z => ‖z - x₀‖ ^ 2) ε ν) +
          (floorRef x (fun x₀ z => ‖z - x₀‖ ^ 2) ε ν - rhoPerp x w ε ν)) ∧
      rhoPerp x w ε ν ≤ floorRef x (fun x₀ z => ‖z - x₀‖ ^ 2) ε ν

/-- (ii), the population excess is nonnegative: `ρ_ν ≤ W^ν_ε(μ, P)` (bounded cost, `Setting`). -/
def fl_identities_excess : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (ν P : Measure K) [IsFiniteMeasure ν] [IsProbabilityMeasure P],
    Setting ε a c → ν Set.univ ≠ 0 → (floorW ε a c ν : EReal) ≤ Wdisc ε a c ν P

/-! #### JASA `thm:fl-coverage` -/

/-- `thm:fl-coverage`, with `prop:fl-radius` as the hypothesis (one measurable event of probability
`≥ 1 − α/(2|𝒢|)` per group and grid point, on which `P_s ∗ U_θ` lies in the ball, `lem:kernel` witness):
with probability `≥ 1 − α`, for every `θ ∈ 𝒢`, every bounded measurable rule and every `λ_0, λ_1 > 0`,
`W₂(h#P_0, h#P_1) ≤ √F̄^θ(h; λ) + 2π_h(U_θ)`, `√F̄^θ = Δ^θ(h) + √T^θ_0 + √T^θ_1`. -/
def fl_coverage : Prop :=
  ∀ (d : ℕ) (Ω G : Type) [MeasurableSpace Ω] [Fintype G] [Nonempty G] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (K : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) (ε α : ℝ)
    (U : G → Measure (EuclideanSpace ℝ (Fin d))) [∀ θ, IsProbabilityMeasure (U θ)]
    (n : G → Fin 2 → ℕ) (x : ∀ θ s, Ω → Fin (n θ s) → EuclideanSpace ℝ (Fin d))
    (r : G → Fin 2 → Ω → ℝ) (ν : G → Fin 2 → Ω → Measure (EuclideanSpace ℝ (Fin d)))
    (P : Fin 2 → Measure (EuclideanSpace ℝ (Fin d))) [∀ s, IsProbabilityMeasure (P s)]
    (Ev : G → Fin 2 → Set Ω),
    0 < ε → 0 < α → α < 1 → (∀ θ s, 0 < n θ s) →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    (∀ θ s ω, IsFiniteMeasure (ν θ s ω) ∧ ν θ s ω Set.univ ≠ 0 ∧ ν θ s ω Set.univ ≤ 1) →
    (∀ s, P s Kᶜ = 0) →
    (∀ θ s, MeasurableSet (Ev θ s)) →
    (∀ θ s, ENNReal.ofReal (1 - α / (2 * Fintype.card G)) ≤ Pr (Ev θ s)) →
    (∀ θ s, ∀ ω ∈ Ev θ s, KernelWitness (x θ s ω) c ε (r θ s ω) (ν θ s ω) (P s ∗ U θ)) →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ Pr E ∧
        ∀ ω ∈ E, ∀ (θ : G) (h : EuclideanSpace ℝ (Fin d) → ℝ) (lam : Fin 2 → ℝ),
          Measurable h → (∃ H, ∀ z, |h z| ≤ H) → (∀ s, 0 < lam s) →
            wassersteinEDist 2 ((P 0).map h) ((P 1).map h) ≤
              wassersteinEDist 2 ((centre (x θ 0 ω)).map h) ((centre (x θ 1 ω)).map h) +
                ENNReal.ofReal √(Tref1 (x θ 0 ω) c h ε (r θ 0 ω) (lam 0) (ν θ 0 ω)) +
                ENNReal.ofReal √(Tref1 (x θ 1 ω) c h ε (r θ 1 ω) (lam 1) (ν θ 1 ω)) +
                2 * StatFormal.Wave18a.jitterPrice K h (U θ)

/-! #### JASA `prop:ep-nested` -/

/-- (i): `G^ν_{ε'} ≤ G^ν_ε` on `𝒫(K)` for `0 < ε' ≤ ε` (`ν(K) ≤ 1`). -/
def ep_nested_G : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε ε' : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (ν Q : Measure K) [IsFiniteMeasure ν] [IsProbabilityMeasure Q],
    0 < ε' → ε' ≤ ε → (∀ i, 0 ≤ a i) → ∑ i, a i = 1 → ν Set.univ ≤ 1 →
      Wdisc ε' a c ν Q ≤ Wdisc ε a c ν Q

/-- (i), `ε' = 0`: `G^ν_0 ≤ G^ν_ε` on `𝒫(K)` (`c = dist²`, `ν(K) ≤ 1`). -/
def ep_nested_G0 : Prop :=
  ∀ (K : Type) [MetricSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (x : Fin k → K) (ν Q : Measure K) [IsFiniteMeasure ν]
    [IsProbabilityMeasure Q],
    Setting ε a (fun i z => dist (x i) z ^ 2) → ν Set.univ ≤ 1 →
      G0 a x ν Q ≤ Wdisc ε a (fun i z => dist (x i) z ^ 2) ν Q

/-- (i), the balls: `𝓑^ν_ε(r) ⊆ 𝓑^ν_{ε'}(r) ⊆ 𝓑^ν_0(r)` for `0 < ε' ≤ ε` (`c = dist²`). -/
def ep_nested_balls : Prop :=
  ∀ (K : Type) [MetricSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (k : ℕ) (ε ε' r : ℝ) (a : Fin k → ℝ) (x : Fin k → K) (ν : Measure K) [IsFiniteMeasure ν],
    Setting ε' a (fun i z => dist (x i) z ^ 2) → ε' ≤ ε → ν Set.univ ≤ 1 →
      ballEps ε a (fun i z => dist (x i) z ^ 2) ν r ⊆ ballEps ε' a (fun i z => dist (x i) z ^ 2) ν r ∧
        ballEps ε' a (fun i z => dist (x i) z ^ 2) ν r ⊆ ball0 a x ν r

/-- (i), the floors: `R_0 ≤ R_{ε'} ≤ R_ε` for `0 < ε' ≤ ε` (`c = dist²`, `0 < ν(K) ≤ 1`). -/
def ep_nested_floor : Prop :=
  ∀ (K : Type) [MetricSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (k : ℕ) (ε ε' : ℝ) (a : Fin k → ℝ) (x : Fin k → K) (ν : Measure K) [IsFiniteMeasure ν],
    Setting ε' a (fun i z => dist (x i) z ^ 2) → ε' ≤ ε → ν Set.univ ≠ 0 → ν Set.univ ≤ 1 →
      floorZero a x ν ≤ floorW ε' a (fun i z => dist (x i) z ^ 2) ν ∧
        floorW ε' a (fun i z => dist (x i) z ^ 2) ν ≤ floorW ε a (fun i z => dist (x i) z ^ 2) ν

/-- (ii): `T_ε(λ; r) ≤ T_{ε'}(λ; r) ≤ T^0(λ; r)` for every `λ > 0` and `0 < ε' ≤ ε`; hence the optimised
groupwise certificate `inf_{λ>0} T_ε(λ; r)` is nondecreasing as `ε ↓ 0`. -/
def ep_nested_T : Prop :=
  ∀ (K : Type) [MetricSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (ε ε' r : ℝ) (ν : Measure K)
    [IsFiniteMeasure ν],
    0 < n → 0 < ε' → ε' ≤ ε → Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) →
    (∃ B, ∀ a b, c a b ≤ B) → Measurable h → (∃ H, ∀ z, |h z| ≤ H) → ν Set.univ ≠ 0 →
    ν Set.univ ≤ 1 →
      (∀ lam, 0 < lam →
        Tref1 x c h ε r lam ν ≤ Tref1 x c h ε' r lam ν ∧ (Tref1 x c h ε' r lam ν : EReal) ≤ T0 x c h r lam ν) ∧
      (⨅ lam ∈ Ioi (0 : ℝ), (Tref1 x c h ε r lam ν : EReal)) ≤ ⨅ lam ∈ Ioi (0 : ℝ), (Tref1 x c h ε' r lam ν : EReal)

/-- (iii): the worst-case disparity `F_ε(r_0, r_1)` is nondecreasing as `ε ↓ 0` and bounded by `F_0(r_0, r_1)`. -/
def ep_nested_F : Prop :=
  ∀ (K : Type) [MetricSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (k₀ k₁ : ℕ) (ε ε' r₀ r₁ : ℝ) (a₀ : Fin k₀ → ℝ) (a₁ : Fin k₁ → ℝ) (x₀ : Fin k₀ → K) (x₁ : Fin k₁ → K)
    (ν₀ ν₁ : Measure K) [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] (h : K → ℝ), Measurable h →
    Setting ε' a₀ (fun i z => dist (x₀ i) z ^ 2) → Setting ε' a₁ (fun i z => dist (x₁ i) z ^ 2) → ε' ≤ ε →
    ν₀ Set.univ ≤ 1 → ν₁ Set.univ ≤ 1 →
      worstDisp (ballEps ε a₀ (fun i z => dist (x₀ i) z ^ 2) ν₀ r₀) (ballEps ε a₁ (fun i z => dist (x₁ i) z ^ 2) ν₁ r₁) h ≤
          worstDisp (ballEps ε' a₀ (fun i z => dist (x₀ i) z ^ 2) ν₀ r₀)
            (ballEps ε' a₁ (fun i z => dist (x₁ i) z ^ 2) ν₁ r₁) h ∧
        worstDisp (ballEps ε' a₀ (fun i z => dist (x₀ i) z ^ 2) ν₀ r₀)
            (ballEps ε' a₁ (fun i z => dist (x₁ i) z ^ 2) ν₁ r₁) h ≤
          worstDisp (ball0 a₀ x₀ ν₀ r₀) (ball0 a₁ x₁ ν₁ r₁) h

/-! #### JASA `lem:sc-proj` -/

/-- `lem:sc-proj`: for `K` closed convex with Euclidean projection `Π`, a coupling `γ` of the centre
`μ = Σ_i a_i δ_{x_i}` (`x_i ∈ K`) and `law(X)`, with `E c(X₀,X) < ∞`:
`OT_ε(μ, law ΠX) ≤ E c(X₀,ΠX) + ε I(X₀;ΠX) ≤ E c(X₀,X) + ε I(X₀;X)`. -/
def sc_proj : Prop :=
  ∀ (d k : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : Fin k → EuclideanSpace ℝ (Fin d)) (a : Fin k → ℝ) (ε : ℝ)
    (γ : Measure (Fin k × EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure γ],
    IsClosed K → Convex ℝ K → (∀ y, proj y ∈ K) → (∀ y, ‖y - proj y‖ = Metric.infDist y K) →
    (∀ i, x i ∈ K) → (∀ i, 0 < a i) → ∑ i, a i = 1 → 0 ≤ ε → γ.map Prod.fst = muDisc a →
    Integrable (fun p => ‖x p.1 - p.2‖ ^ 2) γ →
      OTdisc ε a (fun i y => ‖x i - y‖ ^ 2) ((γ.map Prod.snd).map proj) ≤
          ((∫ p, ‖x p.1 - p.2‖ ^ 2 ∂(γ.map fun p => (p.1, proj p.2)) : ℝ) : EReal) +
            (ε : EReal) * klRef (γ.map fun p => (p.1, proj p.2)) ((muDisc a).prod ((γ.map Prod.snd).map proj)) ∧
        ((∫ p, ‖x p.1 - p.2‖ ^ 2 ∂(γ.map fun p => (p.1, proj p.2)) : ℝ) : EReal) +
            (ε : EReal) * klRef (γ.map fun p => (p.1, proj p.2)) ((muDisc a).prod ((γ.map Prod.snd).map proj)) ≤
          ((∫ p, ‖x p.1 - p.2‖ ^ 2 ∂γ : ℝ) : EReal) + (ε : EReal) * klRef γ ((muDisc a).prod (γ.map Prod.snd))

/-! #### JASA `lem:cert-structure` -/

/-- (i): `Gap_P(f) = Θ(P) − J_P(f) = ε E_P KL(π(·|Y) ‖ π_f(·|Y))`, `π = π_{f*}`, `f*` a maximiser of `J_P`. -/
def cert_structure_i : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P : Measure K) [IsProbabilityMeasure P] (fs f : Fin k → ℝ),
    Setting ε a c → (∀ g, Jdual ε a c P g ≤ Jdual ε a c P fs) →
      OTdisc ε a c P - (Jdual ε a c P f : EReal) =
        ((ε * ∫ y, klFin (fun i => postW ε a fs c i y) (fun i => postW ε a f c i y) ∂P : ℝ) : EReal)

/-- (ii), gradient: `∇J_P(f) = a − E_P π_f(·|Y)` (Fréchet derivative), and it sums to zero. -/
def cert_structure_ii_grad : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P : Measure K) [IsProbabilityMeasure P] (f : Fin k → ℝ),
    Setting ε a c →
      HasFDerivAt (Jdual ε a c P)
          (∑ i, gradJ ε a c P f i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i) f ∧
        ∑ i, gradJ ε a c P f i = 0

/-- (ii), gap: `0 ≤ Gap_P(f) ≤ ⟨∇J_P(f), f* − f⟩`. -/
def cert_structure_ii_gap : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P : Measure K) [IsProbabilityMeasure P] (fs f : Fin k → ℝ),
    Setting ε a c → (∀ g, Jdual ε a c P g ≤ Jdual ε a c P fs) →
      0 ≤ OTdisc ε a c P - (Jdual ε a c P f : EReal) ∧
        OTdisc ε a c P - (Jdual ε a c P f : EReal) ≤ ((∑ i, gradJ ε a c P f i * (fs i - f i) : ℝ) : EReal)

/-- (iii): `E_P π(i | Y) = a_i`. -/
def cert_structure_iii : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (P : Measure K) [IsProbabilityMeasure P] (fs : Fin k → ℝ),
    Setting ε a c → (∀ g, Jdual ε a c P g ≤ Jdual ε a c P fs) →
      ∀ i, ∫ y, postW ε a fs c i y ∂P = a i

/-! #### NN `lem:noncentral` -/

/-- The minimum-norm point: a nonempty affine subspace `A = z₀ + V` has exactly one point `z₀ ∈ V^⊥`, and
it has the least norm, `‖z₀‖ = dist(0, A)`. -/
def noncentral_minnorm : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : AffineSubspace ℝ E), (A : Set E).Nonempty →
      (∃! z₀, z₀ ∈ A ∧ z₀ ∈ A.directionᗮ) ∧
        ∀ z₀, z₀ ∈ A → z₀ ∈ A.directionᗮ → (∀ y ∈ A, ‖z₀‖ ≤ ‖y‖) ∧ ‖z₀‖ = Metric.infDist 0 (A : Set E)

/-- The proof's decomposition: `dist(x, A) = ‖x_⊥ − z₀‖`, `x_⊥` the orthogonal projection onto `V^⊥`. -/
def noncentral_decomp : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : AffineSubspace ℝ E) (z₀ : E), z₀ ∈ A → z₀ ∈ A.directionᗮ →
      ∀ x, Metric.infDist x (A : Set E) = ‖(A.directionᗮ).starProjection x - z₀‖

/-- `lem:noncentral`: for `X ∼ N(0, σ²I)` and `A = z₀ + V` of codimension `c`, `z₀ ∈ V^⊥`,
`dist(X, A)²/σ² ∼ χ²_c(‖z₀‖²/σ²)` (equality of laws on `ℝ`). -/
def noncentral : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (A : AffineSubspace ℝ E) (z₀ : E) (σ : ℝ),
    z₀ ∈ A → z₀ ∈ A.directionᗮ → 0 < σ →
      (isoGauss E σ).map (fun x => Metric.infDist x (A : Set E) ^ 2 / σ ^ 2) =
        ncChiSq (Module.finrank ℝ E - Module.finrank ℝ A.direction) (‖z₀‖ ^ 2 / σ ^ 2)

end Claims

end StatFormal.Wave19b
