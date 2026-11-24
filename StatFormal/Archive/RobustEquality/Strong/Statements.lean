import StatFormal.Archive.RobustEquality.Certificate.Statements
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# FROZEN STATEMENTS — robust equality (JASA): `prop:strong`(ii), finitely supported mixing laws

Sources (verbatim in `inventory/extracted/robust-equality-jasa.md`): `prop:strong`
(`jasa/main.tex:376-390`), with `eq:T` and `thm:certificate` (`main.tex:343-363`) and `lem:kernel`
(`main.tex:265-272`); supplement `supp_proofs.tex`: references with `0 < ν(K) ≤ 1`, labelled
centres, `G_ν`, `ρ_ν` (`:14-33`); `eq:floorid` (`:185-196`); `ass:mixture` and the
finite-dictionary remark (`:225-238`); proof of `prop:strong` (`:240-303`): `Ψ^ν` and
`T = sup_ν Ψ^ν` (`:241-242`), (ii) Step 1 (`:252-267`, branch `λ* = 0` at `:264-267`), Step 2
(`:268-281`).

Covered:
* `strong_single` ((ii) Step 1, every radius): `inf_{λ>0} Ψ^ν(λ) = v_ν(r)` in `EReal` for every
  `r` (both sides `⊥` below the floor `ρ_ν`, the paper's `sup ∅ = −∞`);
* `strong_single_boundary` (the branch `λ* = 0`): if `0` is a supergradient of `v_ν` at `r`
  (`v_ν(t) ≤ v_ν(r)` for all `t`), then `v_ν(r) ≤ Ψ^ν(λ) ≤ v_ν(r) + λ (r − ρ_ν)` for every
  `λ > 0`, hence `Ψ^ν(λ) → v_ν(r)` as `λ ↓ 0`;
* `strong_single_dichotomy`: for `r > ρ_ν`, either some `λ > 0` attains `Ψ^ν(λ) = v_ν(r)`
  (`λ* > 0`), or `Ψ^ν(λ) → v_ν(r)` as `λ ↓ 0` (`λ* = 0`);
* `strong_mix` (**`prop:strong`(ii)**, `L` finite): for finite references `κ_1, …, κ_L` with
  `κ_l(K) > 0` and any nonempty convex closed `M ⊆ Δ_L`,
  `inf_{λ>0} sup_{m ∈ M} Ψ^{ν_m}(λ) = sup_{m ∈ M} v_{ν_m}(r)` in `EReal`, for every `r`;
* `strong_mix_finite` ("since `r_s > R_min` the value is finite"): if `ρ_{ν_m} ≤ r` for some
  `m ∈ M`, the common value is neither `⊥` nor `⊤`.
Not covered (declared): `prop:strong`(i) (convexity of `T^N`, slope `r − R_min` at `∞`) and (iii)
(rate-distortion / Blahut–Arimoto form); (ii) for an infinite mixing space `L` (Feller kernel,
weakly closed `M ⊆ 𝒫(L)`, continuous `h`); the identification `v_ν(r) = E_{P̂} ess sup_ν f_h` in
the branch `λ* = 0`; the remark that (ii) can fail for a bare finite dictionary
(`supp_proofs.tex:236-237`); the equivalence of `lem:kernel` with the entropic-OT ball.

Encodings (see card):
* `T^N_s(h,λ)` is encoded as in `supp_proofs.tex:241-242`, by `sup_{m ∈ M} Ψ^{ν_m}(λ)` in `EReal`,
  with `Ψ^ν = Tref1` of the frozen `Certificate` statements; for `λ > 0` this is
  `λ r + λ ε Λ^N_s(h,λ)` of `eq:T` (an increasing affine map commutes with the supremum);
* the class is `ν_m = Σ_l m_l κ_l` (`mixRef`, coefficients `ENNReal.ofReal m_l`) for `m` in a set
  `M ⊆ Δ_L` (`simplex`): `ass:mixture` with `L` finite (every kernel is then Feller, and weak
  closedness of `M ⊆ 𝒫(L)` is closedness in `ℝ^L`); `M = Δ_L` is the hull of a finite dictionary;
* the kernels of `lem:kernel` are labelled (`Γ : Fin n → Measure K`, one probability law per
  anchor, ties allowed, `supp_proofs.tex:25-27`); their budget `G_ν` is `budget`, in `EReal`, with
  the paper's KL `klRef`; `v_ν(t)` is `couplingValue`, an `EReal` supremum (`sup ∅ = ⊥`);
* generalisation: the paper's `ν(K) ≤ 1`, `κ(y,K) ≤ 1`, continuity of `h`, `c = ‖x − x'‖²`,
  compact `K` and `r_s > R^N_min` are dropped — `K` is any measurable space, references are finite
  with `ν(K) ≠ 0`, `c ≥ 0` is bounded and jointly measurable, `h` is bounded measurable, `r ∈ ℝ`;
* `r > R^N_min = inf_{m ∈ M} ρ_{ν_m}` is replaced in `strong_mix_finite` by the weaker
  `∃ m ∈ M, ρ_{ν_m} ≤ r` (`r > R_min` gives some `m` with `ρ_m < r`);
* "`0` is a supergradient of `v_ν` at `r`" (the paper's `λ* = 0`) is `∀ t, v_ν(t) ≤ v_ν(r)`;
  "`λ ↓ 0`" is the filter `𝓝[>] 0`.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes
`Strong/Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.RobustEquality.Strong

open StatFormal.RobustEquality StatFormal.RobustEquality.Certificate

variable {K : Type} [MeasurableSpace K] {n L : ℕ}

/-- The probability simplex `Δ_L = {m : m_l ≥ 0, Σ_l m_l = 1}`. -/
def simplex (L : ℕ) : Set (Fin L → ℝ) := {m | (∀ l, 0 ≤ m l) ∧ ∑ l, m l = 1}

/-- The mixture `ν_m = Σ_l m_l κ_l`. -/
def mixRef (κ : Fin L → Measure K) (m : Fin L → ℝ) : Measure K :=
  ∑ l, ENNReal.ofReal (m l) • κ l

/-- The budget `n⁻¹ Σ_i (E_{Γ_i} c(x_i,·) + ε KL(Γ_i‖ν))` of `lem:kernel`. -/
def budget (x : Fin n → K) (c : K → K → ℝ) (ε : ℝ) (ν : Measure K) (Γ : Fin n → Measure K) :
    EReal :=
  ((n : ℝ)⁻¹ : EReal) * ∑ i, (((∫ z, c (x i) z ∂(Γ i) : ℝ) : EReal) + (ε : EReal) * klRef (Γ i) ν)

/-- The coupling objective `n⁻¹ Σ_i E_{Γ_i} f_h(x_i, ·)`. -/
def primal (x : Fin n → K) (h : K → ℝ) (Γ : Fin n → Measure K) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, ∫ z, (h z - h (x i)) ^ 2 ∂(Γ i)

/-- The kernels of `lem:kernel` with budget at most `r`. -/
def Adm (x : Fin n → K) (c : K → K → ℝ) (ε r : ℝ) (ν : Measure K) : Set (Fin n → Measure K) :=
  {Γ | (∀ i, IsProbabilityMeasure (Γ i)) ∧ budget x c ε ν Γ ≤ (r : EReal)}

/-- The value `v_ν(t) = sup {n⁻¹ Σ_i E_{Γ_i} f_h(x_i,·) : budget ≤ t}` (`sup ∅ = ⊥`). -/
def couplingValue (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (ε t : ℝ) (ν : Measure K) :
    EReal :=
  ⨆ Γ ∈ Adm x c ε t ν, (primal x h Γ : EReal)

/-- The floor `ρ_ν = −ε n⁻¹ Σ_i log ∫ e^{−c(x_i,·)/ε} dν`. -/
def floorRef (x : Fin n → K) (c : K → K → ℝ) (ε : ℝ) (ν : Measure K) : ℝ :=
  -ε * ((n : ℝ)⁻¹ * ∑ i, Real.log (∫ z, Real.exp (-(c (x i) z) / ε) ∂ν))

namespace Claims

/-- `prop:strong`(ii), Step 1, single reference, every radius: `inf_{λ>0} Ψ^ν(λ) = v_ν(r)`. -/
def strong_single : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ)
    (ε r : ℝ) (ν : Measure K) [IsFiniteMeasure ν],
    0 < n → 0 < ε → Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) →
    (∃ B, ∀ a b, c a b ≤ B) → Measurable h → (∃ H, ∀ z, |h z| ≤ H) → ν Set.univ ≠ 0 →
      (⨅ lam ∈ Ioi (0 : ℝ), (Tref1 x c h ε r lam ν : EReal)) = couplingValue x c h ε r ν

/-- `prop:strong`(ii), Step 1, the `λ* = 0` branch: if `0` is a supergradient of `v_ν` at `r`, then
`v_ν(r) ≤ Ψ^ν(λ) ≤ v_ν(r) + λ (r − ρ_ν)` for every `λ > 0`, and `Ψ^ν(λ) → v_ν(r)` as `λ ↓ 0`. -/
def strong_single_boundary : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ)
    (ε r : ℝ) (ν : Measure K) [IsFiniteMeasure ν],
    0 < n → 0 < ε → Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) →
    (∃ B, ∀ a b, c a b ≤ B) → Measurable h → (∃ H, ∀ z, |h z| ≤ H) → ν Set.univ ≠ 0 →
    (∀ t : ℝ, couplingValue x c h ε t ν ≤ couplingValue x c h ε r ν) →
      (∀ lam : ℝ, 0 < lam →
          couplingValue x c h ε r ν ≤ (Tref1 x c h ε r lam ν : EReal) ∧
          (Tref1 x c h ε r lam ν : EReal) ≤
            couplingValue x c h ε r ν + ((lam * (r - floorRef x c ε ν) : ℝ) : EReal)) ∧
        Tendsto (fun lam => (Tref1 x c h ε r lam ν : EReal)) (𝓝[>] 0)
          (𝓝 (couplingValue x c h ε r ν))

/-- `prop:strong`(ii), Step 1, above the floor: the dual infimum is attained at some `λ > 0`, or
it is the limit as `λ ↓ 0`. -/
def strong_single_dichotomy : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ)
    (ε r : ℝ) (ν : Measure K) [IsFiniteMeasure ν],
    0 < n → 0 < ε → Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) →
    (∃ B, ∀ a b, c a b ≤ B) → Measurable h → (∃ H, ∀ z, |h z| ≤ H) → ν Set.univ ≠ 0 →
    floorRef x c ε ν < r →
      (∃ lam : ℝ, 0 < lam ∧ (Tref1 x c h ε r lam ν : EReal) = couplingValue x c h ε r ν) ∨
        Tendsto (fun lam => (Tref1 x c h ε r lam ν : EReal)) (𝓝[>] 0)
          (𝓝 (couplingValue x c h ε r ν))

/-- **`prop:strong`(ii)** for finitely supported mixing laws, every radius:
`inf_{λ>0} sup_{m ∈ M} Ψ^{ν_m}(λ) = sup_{m ∈ M} v_{ν_m}(r)`. -/
def strong_mix : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n L : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ)
    (ε r : ℝ) (κ : Fin L → Measure K) [∀ l, IsFiniteMeasure (κ l)] (M : Set (Fin L → ℝ)),
    0 < n → 0 < ε → Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) →
    (∃ B, ∀ a b, c a b ≤ B) → Measurable h → (∃ H, ∀ z, |h z| ≤ H) →
    (∀ l, κ l Set.univ ≠ 0) → M ⊆ simplex L → Convex ℝ M → IsClosed M → M.Nonempty →
      (⨅ lam ∈ Ioi (0 : ℝ), ⨆ m ∈ M, (Tref1 x c h ε r lam (mixRef κ m) : EReal)) =
        ⨆ m ∈ M, couplingValue x c h ε r (mixRef κ m)

/-- `prop:strong`(ii), finiteness: if some `m ∈ M` has `ρ_{ν_m} ≤ r`, the value is a real. -/
def strong_mix_finite : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n L : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ)
    (ε r : ℝ) (κ : Fin L → Measure K) [∀ l, IsFiniteMeasure (κ l)] (M : Set (Fin L → ℝ)),
    0 < n → 0 < ε → Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) →
    (∃ B, ∀ a b, c a b ≤ B) → Measurable h → (∃ H, ∀ z, |h z| ≤ H) →
    (∀ l, κ l Set.univ ≠ 0) → M ⊆ simplex L → (∃ m ∈ M, floorRef x c ε (mixRef κ m) ≤ r) →
      (⨆ m ∈ M, couplingValue x c h ε r (mixRef κ m)) ≠ ⊥ ∧
        (⨆ m ∈ M, couplingValue x c h ε r (mixRef κ m)) ≠ ⊤

end Claims
end StatFormal.RobustEquality.Strong
