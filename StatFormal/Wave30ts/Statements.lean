import StatFormal.Wave30tp.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30ts: trimmed-mmd (JMLR revision), the sharper inversion of Theorem P (NOTE §3.3) and Pinelis

Printed source: `trimmed-mmd/explore/sharper_threshold/NOTE.md` §3.3 "Sharper inversion of the same tails (still a theorem)"
(read-only research note for the JMLR revision; frozen from the snapshot read 2026-11-08, sha256
`b6f1aab476e51d1aba9b146074cbe93bbaae7311638a485d0f9cd8511565d284`, lines 335–388; the same file that wave 30tp recorded at
the end of its run; labels are to be remapped to the paper's when the JMLR text is revised). Implementation:
`explore/sharper_threshold/thresholds.py` (`_pinelis_tail`, `_mcd_tail`, `_hilbert_tail`, `_two_point_log_mgf`,
`_chernoff_tail`, `_root`, `hilbert_quantile`, `repair_quantile`, `tau_P`, `tau_P_coupled`, `tau_new`).
* §3.3 (`:337-348`): "Define, for `s' ∈ {s, 1/n, 1/m}` with matching `c' ∈ {c, 1/n, 1/m}`,
  `Ψ_H(t;β,s',c') = min{ e^{−2(t−√(βv²s'))_+²/(β²D_φ²s')}, 2exp(t/a − (t/a + b²/a²) log(1 + ta/b²)) }`, `a = βρ̄c'`,
  `b² = βv²s'`, the second term being Pinelis' Bennett-type bound for martingales in a `(2,1)`-smooth (= Hilbert) space
  (Pinelis 1994, Ann. Probab. 22, Theorem 3.4; `D = 1` for Hilbert spaces, §2), applied to the martingale of partial sums of
  the independent mean-zero `η_k` with `‖η_k‖ ≤ a` (Lemma P1(ii)) and `Σ_k E‖η_k‖² ≤ b²`".
* §3.3 (`:350-355`): "`Ψ_R(t;β,K) = inf_{λ>0} e^{−λt} ∏_{k∈K} [β⁻¹e^{λ(1−β)/k} + (1−β⁻¹)e^{λ/k}]^k`,
  `K ∈ {{n},{m},{n,m}}`, the Chernoff bound with the two-point MGF of Lemma P1(iii) (any `λ` gives a valid bound, so an inexact
  numerical minimizer only makes it larger)."
* §3.3 (`:356-365`): "Let `t_1(β,δ_1)` be the smallest `t` with `Ψ_H(t;β,s,c) + Ψ_H(t;β,1/n,1/n) + Ψ_H(t;β,1/m,1/m) ≤ δ_1`,
  `t_2(β,δ_2)` the smallest `t` with `Ψ_R(t;β,{n}) + Ψ_R(t;β,{m}) + Ψ_R(t;β,{n,m}) ≤ δ_2`, and
  `τ_{P'}(α,δ) = min_{f∈F} [t_1(β,fδ) + ρ̄ t_2(β,(1−f)δ)]`, `F = {0.5,0.6,0.7,0.8,0.9}` fixed in advance, and
  `τ_{P'}(0,δ) = inf{t : Ψ_H(t;1,s,c) ≤ δ}`. The proof of Theorem P goes through verbatim (for each `α` the minimizing `f` is a
  deterministic choice). Each tail function is pointwise nondecreasing in `β` (McDiarmid: mean and proxy increase;
  Bennett/Pinelis: increasing in `a` and `b²`; two-point MGF: the law of `W` on `{1−β,1}` is a mean-preserving spread as `β`
  grows), so `τ_{P'}` is nondecreasing … The implementation adds `10⁻⁶` to each root."
* §3.3 (`:373-380`), "Coupled constants": "For kernels with `k ≥ 0` and `k(x,x) ≡ κ²`, Lemma P1(iv) gives, with
  `u = ‖μ_R‖² ∈ [0,κ²]` unknown, `v² = κ² − u` and `ρ̄² = κ² + u`. … `τ^{cpl}_{P'} = sup_u τ_{P'}(·; v² = κ² − u, ρ̄ = √(κ²+u))`
  is valid; since every tail is nondecreasing in `(v², ρ̄)`, on a cell `[u_j,u_{j+1}]` the threshold is at most its value at
  `(κ² − u_j, √(κ²+u_{j+1}))`, and the maximum over a 20-cell grid is a rigorous upper bound on the supremum."
* §3.3 (`:382-385`), **Corollary C**: "`τ_new = min{τ_A, τ_P, τ_{P'}, τ^{cpl}_{P'}}` (the last only for `k ≥ 0`, constant
  diagonal) is a valid, uniform, nondecreasing threshold; for each `α` the minimizer is a deterministic choice, so the level is
  `δ`, and Lemma 1 gives one event for all `α`."
* References (`:873`): "Pinelis (1994) … Theorem 3.4: if `‖d_j‖_∞ ≤ a` and `‖s_2‖_∞ ≤ b/D` then
  `Pr(f* ≥ r) ≤ 2exp(r/a − (r/a + b²/a²) ln(1 + ra/b²))`; Hilbert spaces are `(2,1)`-smooth (§2)." Checked against the arXiv
  text 1208.2200 (Theorems 3.1 and 3.4, `s_2 = (Σ_j E_{j−1}‖d_j‖²)^{1/2}`, `a, b > 0`, `r ≥ 0`, separable `X`).

Reuses (imported, not copied) the frozen wave 30tp (`sNM`, `cNM`, `tauP`, `KernelConsts`, `sampleLaw`) and through it
`TrimmedMMD` (`Demp`, `alphaHat`) and `StatFormal.Distances.tvDist`.

Encodings (see card `certify/cards/wave30ts.md`):
* Setting as in wave 30tp: `H` a real Hilbert space, `φ` strongly measurable and bounded, `D, v, ρ̄` kernel constants
  (`KernelConsts`), samples `P^{⊗n} ⊗ Q^{⊗m}` (`sampleLaw`), `D̂_α = Demp`, `β = 1/(1−α)`, `s = sNM`, `c = cNM`.
* The printed tail functions are `psiMcD`, `psiPin`, `psiH` (`Ψ_H`), `twoPt` (the bracket of `Ψ_R`), `psiRlam` (`Ψ_R` at a
  fixed `λ`) and `psiR` (`Ψ_R`, the infimum over `λ > 0`, a real `⨅` of a family bounded below by `0` for `β ≥ 1`); `K` is a
  list (Correction 2).
* **Validity is frozen for every admissible choice** (the form the software uses): any `t₁ ≥ 0` with the three-event `Ψ_H` sum
  `≤ δ₁` and any `t₂ ≥ 0` with the three-event `Ψ_R` sum `≤ δ₂` (at any fixed `λ`'s, or with the infimum) give
  `Pr(D̂_α > t₁ + ρ̄t₂) ≤ δ₁ + δ₂`. The printed "smallest root", the root `+10⁻⁶` and every root of an inexact minimizer are
  admissible choices.
* **Correction 1 (`t ≥ 0`).** Admissibility is over `t ≥ 0`, as in Pinelis' theorem (`r ≥ 0`) and in the code (`_pinelis_tail`
  returns 1 for `t ≤ 0`; roots are searched in `[0, hi]`). The printed `inf{t : Ψ_H(t;1,s,c) ≤ δ}` without `t ≥ 0` is false:
  for `t ∈ (−b²/a, 0)` the printed Pinelis term is defined and tiny (Gaussian kernel, `n = m = 300`: `Ψ_H(−0.7) ≈ 6·10⁻²⁰`), so
  the literal infimum is negative and `Pr(D̂₀ > τ) = 1`.
* **Correction 2 (`K` is a list).** `∏_{k∈K}` is a product over a **list** of sample sizes: `K = [n], [m], [n, m]` (one factor
  per sample, also when `n = m`; the code passes the tuple `(n, m)`). Read as a set, `{n, m} = {n}` when `n = m` and the bound is
  false: `n = m = 1`, `β = 2`, `t = 1.5` give `Ψ_R(t;β,{1}) = 0` while `Pr((1−S_X) + (1−S_Y) ≥ 1.5) = 1/4`.
* The literal thresholds are also frozen: `rootH` (`t_1`) and `rootR` (`t_2`) are `sInf` of the admissible sets, `tauPs` is
  `τ_{P'}` (the minimum over `F`, written out, `F = {1/2, 3/5, 7/10, 4/5, 9/10}`), `tauCpl` is `τ^{cpl}_{P'}` (a real `⨆`), and
  `tauGrid` is the maximum over grid cells of `τ_{P'}` at cell constants. An empty admissible set gives the junk `sInf ∅ = 0`;
  the claims about these thresholds hold in that case too (it happens only for a constant feature map, where `D̂_α = 0`).
* **Correction 3 (coupled supremum over `u ∈ [0, κ²)`).** At `u = κ²` the printed constants give `v = 0`, i.e. `b² = 0` in
  Pinelis' term (division by `b²`; Pinelis assumes `b > 0`), and the printed formula is undefined. The supremum is taken over
  `u ∈ [0, κ²)`, where every printed formula is defined (`v, ρ̄ > 0` for `κ > 0`). With Lean's junk value at `u = κ²` (Pinelis
  term `≥ 2`, so `Ψ_H` = McDiarmid alone) the supremum over `[0, κ²]` would exceed the printed 20-cell grid maximum
  (`κ = 1`, `D = √2`, `n = m = 50`, `α = 0.5`, `δ = 0.05`, computed numerically: `1.540` vs `1.454`). The common trimming with `‖μ_R‖² = κ²` is
  handled in the proof (then `tr Cov_R(φ) = 0` and `A = B = 0` a.s.).
* The coupled validity is encoded as in wave 30tp: every `t ≥ 0` above all the `τ_{P'}(…; u)`, `u ∈ [0,κ²)`, is valid
  (`coupled_sharp`); the literal `tauCpl` is also stated.
* `IsValidThreshold φ n m δ τ`: `Pr(D̂_α > τ(α)) ≤ δ` for every `α ∈ [0,1)` and every pair with `TV ≤ α` ("valid, uniform");
  `OneEvent φ n m δ τ P Q`: the one-event conclusion of wave 30tp's `plugin_one_event` for the threshold `τ`.
* Corollary C is stated on a nonempty `𝒳` (otherwise `KernelConsts` holds for negative `D, ρ̄` and `τ_P` can be negative).
* Pinelis' Theorems 3.1 and 3.4 are frozen in the special case used: independent summands (a product measure; a martingale
  difference sequence for its natural filtration with deterministic conditional variances) and the final sum `‖Σ η_i‖` in place
  of the maximal function `f*` (declared specialisation); `H` need not be separable.

Not covered (declared): Theorem A and its `τ_A` (it enters Corollary C as a hypothesis: valid and nondecreasing); the numerical
claims ("Gain about 11–14%", "we also checked this on a 91-point grid", the §4 table, "at every α and n we computed …
`τ_A` never is"); the "mean-preserving spread" itself (only its consequence, `twoPt` nondecreasing in `β`, is stated); the
floating-point correctness of `thresholds.py` (that its returned values are admissible).
FROZEN 2026-11-08 after an independent critic's pre-freeze review (18 drafted claims, none false; applied: corrections 1–3
declared, `coupled_sharp` over `[0,κ²)` with `t ≥ 0`, new `tauCpl`, `coupled_cpl`, `coupled_grid_bound`, Corollary C for the
supremum and for the grid). Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace

namespace StatFormal.Wave30ts

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
open StatFormal.Wave30tp

/-! ### The tail functions of §3.3 -/

/-- The McDiarmid term of `Ψ_H`: `exp(−2 (t − √(β v² s'))_+² / (β² D² s'))`. -/
def psiMcD (D v β s' t : ℝ) : ℝ :=
  Real.exp (-2 * (max (t - √(β * v ^ 2 * s')) 0) ^ 2 / (β ^ 2 * D ^ 2 * s'))

/-- Pinelis' Bennett-type tail: `2 exp(t/a − (t/a + b²/a²) log(1 + t a / b²))` (`b2` is `b²`). -/
def psiPin (a b2 t : ℝ) : ℝ :=
  2 * Real.exp (t / a - (t / a + b2 / a ^ 2) * Real.log (1 + t * a / b2))

/-- `Ψ_H(t; β, s', c') = min{McDiarmid, Pinelis with a = β ρ̄ c', b² = β v² s'}`. -/
def psiH (D v ρbar β s' c' t : ℝ) : ℝ :=
  min (psiMcD D v β s' t) (psiPin (β * ρbar * c') (β * v ^ 2 * s') t)

/-- The three-event Hilbert sum `Ψ_H(t;β,s,c) + Ψ_H(t;β,1/n,1/n) + Ψ_H(t;β,1/m,1/m)`. -/
def psiH3 (D v ρbar β t : ℝ) (n m : ℕ) : ℝ :=
  psiH D v ρbar β (sNM n m) (cNM n m) t + psiH D v ρbar β (1 / (n : ℝ)) (1 / (n : ℝ)) t +
    psiH D v ρbar β (1 / (m : ℝ)) (1 / (m : ℝ)) t

/-- The two-point MGF bound `β⁻¹ e^{l(1−β)} + (1 − β⁻¹) e^{l}`. -/
def twoPt (β l : ℝ) : ℝ := β⁻¹ * Real.exp (l * (1 - β)) + (1 - β⁻¹) * Real.exp l

/-- `Ψ_R` at a fixed `λ = l`: `e^{−l t} ∏_{k ∈ K} [twoPt β (l/k)]^k`, `K` a list of sample sizes. -/
def psiRlam (β l t : ℝ) (K : List ℕ) : ℝ :=
  Real.exp (-(l * t)) * (K.map fun k : ℕ => twoPt β (l / (k : ℝ)) ^ k).prod

/-- `Ψ_R(t; β, K) = inf_{λ > 0} e^{−λt} ∏_{k∈K} [β⁻¹e^{λ(1−β)/k} + (1−β⁻¹)e^{λ/k}]^k`. -/
def psiR (β t : ℝ) (K : List ℕ) : ℝ := ⨅ l : Ioi (0 : ℝ), psiRlam β l t K

/-- The three-event repair sum `Ψ_R(t;β,{n}) + Ψ_R(t;β,{m}) + Ψ_R(t;β,{n,m})`. -/
def psiR3 (β t : ℝ) (n m : ℕ) : ℝ := psiR β t [n] + psiR β t [m] + psiR β t [n, m]

/-! ### The thresholds of §3.3 -/

/-- `t_1(β, δ₁)`: the smallest (infimum) `t ≥ 0` with three-event Hilbert sum `≤ δ₁`. -/
def rootH (D v ρbar β δ1 : ℝ) (n m : ℕ) : ℝ := sInf {t : ℝ | 0 ≤ t ∧ psiH3 D v ρbar β t n m ≤ δ1}

/-- `t_2(β, δ₂)`: the smallest (infimum) `t ≥ 0` with three-event repair sum `≤ δ₂`. -/
def rootR (β δ2 : ℝ) (n m : ℕ) : ℝ := sInf {t : ℝ | 0 ≤ t ∧ psiR3 β t n m ≤ δ2}

/-- `t_1(β, fδ) + ρ̄ t_2(β, (1−f)δ)`, `β = 1/(1−α)`. -/
def tauSplit (D v ρbar α δ f : ℝ) (n m : ℕ) : ℝ :=
  rootH D v ρbar (1 / (1 - α)) (f * δ) n m + ρbar * rootR (1 / (1 - α)) ((1 - f) * δ) n m

/-- `τ_{P'}(α, δ)`: `inf{t ≥ 0 : Ψ_H(t;1,s,c) ≤ δ}` at `α = 0`, and `min_{f ∈ F} [t_1(β,fδ) + ρ̄ t_2(β,(1−f)δ)]` with
`F = {0.5, 0.6, 0.7, 0.8, 0.9}` for `0 < α < 1`. -/
def tauPs (D v ρbar α δ : ℝ) (n m : ℕ) : ℝ :=
  if α = 0 then sInf {t : ℝ | 0 ≤ t ∧ psiH D v ρbar 1 (sNM n m) (cNM n m) t ≤ δ}
  else min (tauSplit D v ρbar α δ (1 / 2) n m) (min (tauSplit D v ρbar α δ (3 / 5) n m)
    (min (tauSplit D v ρbar α δ (7 / 10) n m) (min (tauSplit D v ρbar α δ (4 / 5) n m)
      (tauSplit D v ρbar α δ (9 / 10) n m))))

/-- The grid form of `τ^{cpl}_{P'}`: the maximum (with `0`) over cells `j < J` of `τ_{P'}(α,δ; v_j, ρ̄_j)`. -/
def tauGrid (D : ℝ) (v ρ : ℕ → ℝ) (J : ℕ) (α δ : ℝ) (n m : ℕ) : ℝ :=
  ((List.range J).map fun j => tauPs D (v j) (ρ j) α δ n m).foldr max 0

/-- The coupled threshold `τ^{cpl}_{P'}(α,δ) = sup_{u ∈ [0,κ²)} τ_{P'}(α,δ; v = √(κ² − u), ρ̄ = √(κ² + u))` (a real `⨆`; the
family is bounded above by `τ_{P'}(α,δ; |κ|, √2|κ|)`, and the index set is empty only for `κ = 0`). -/
def tauCpl (D κ α δ : ℝ) (n m : ℕ) : ℝ :=
  ⨆ u : Ico (0 : ℝ) (κ ^ 2), tauPs D (√(κ ^ 2 - (u : ℝ))) (√(κ ^ 2 + (u : ℝ))) α δ n m

section Predicates

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `τ` is a valid, uniform threshold at level `δ`: for every `α ∈ [0,1)` and **every** pair of probability measures with
`TV(P,Q) ≤ α`, `Pr(D̂_α > τ(α)) ≤ δ` under `P^{⊗n} ⊗ Q^{⊗m}`. -/
def IsValidThreshold (φ : 𝒳 → H) (n m : ℕ) (δ : ℝ) (τ : ℝ → ℝ) : Prop :=
  ∀ α ∈ Ico (0 : ℝ) 1, ∀ P Q : Measure 𝒳, IsProbabilityMeasure P → IsProbabilityMeasure Q →
    StatFormal.Distances.tvDist P Q ≤ α → sampleLaw P Q n m {z | τ α < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal δ

/-- The one-event conclusion (Lemma 1 as used in Theorem P) for the threshold `τ` and the pair `(P, Q)`: a measurable event of
probability `≥ 1 − δ` on which `D̂_α ≤ τ(α)` for every `α ∈ [0,1)` with `TV(P,Q) ≤ α`, `α̂ ≤ TV(P,Q)` when `TV(P,Q) < 1`, and
every rejected level `α ∈ [0,1)` (`τ(α) < D̂_α`) is `< TV(P,Q)`. -/
def OneEvent (φ : 𝒳 → H) (n m : ℕ) (δ : ℝ) (τ : ℝ → ℝ) (P Q : Measure 𝒳) : Prop :=
  ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m E ∧
    ∀ z ∈ E,
      (∀ α ∈ Ico (0 : ℝ) 1, StatFormal.Distances.tvDist P Q ≤ α → Demp φ z.1 z.2 α ≤ τ α) ∧
      (StatFormal.Distances.tvDist P Q < 1 → alphaHat (Demp φ z.1 z.2) τ ≤ StatFormal.Distances.tvDist P Q) ∧
      (∀ α ∈ Ico (0 : ℝ) 1, τ α < Demp φ z.1 z.2 α → α < StatFormal.Distances.tvDist P Q)

end Predicates

namespace Claims

/-! ### Pinelis (1994), Theorems 3.1 and 3.4, Hilbert case (`D = 1`), independent summands -/

/-- **Pinelis (1994) Theorem 3.1**, Hilbert space (`(2,1)`-smooth, `D = 1`), independent summands, final sum: for independent
mean-zero `η_i` (coordinates of a product measure) with `E e^{λ‖η_i‖} < ∞`, `λ > 0` and `r ≥ 0`:
`Pr(‖Σ_i η_i‖ ≥ r) ≤ 2e^{−λr} ∏_i [1 + E(e^{λ‖η_i‖} − 1 − λ‖η_i‖)] ≤ 2 exp(−λr + Σ_i E(e^{λ‖η_i‖} − 1 − λ‖η_i‖))`. -/
def pinelis_mgf : Prop :=
  ∀ (ι H : Type) [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (η : ∀ i, Ω i → H) (l r : ℝ),
    (∀ i, StronglyMeasurable (η i)) → (∀ i, Integrable (fun ω => Real.exp (l * ‖η i ω‖)) (μ i)) →
    (∀ i, ∫ ω, η i ω ∂(μ i) = 0) → 0 < l → 0 ≤ r →
      Measure.pi μ {ω | r ≤ ‖∑ i, η i (ω i)‖} ≤
          ENNReal.ofReal (2 * Real.exp (-(l * r)) *
            ∏ i, (1 + ∫ ω, (Real.exp (l * ‖η i ω‖) - 1 - l * ‖η i ω‖) ∂(μ i))) ∧
        2 * Real.exp (-(l * r)) * ∏ i, (1 + ∫ ω, (Real.exp (l * ‖η i ω‖) - 1 - l * ‖η i ω‖) ∂(μ i)) ≤
          2 * Real.exp (-(l * r) + ∑ i, ∫ ω, (Real.exp (l * ‖η i ω‖) - 1 - l * ‖η i ω‖) ∂(μ i))

/-- **Pinelis (1994) Theorem 3.4**, Hilbert space (`D = 1`), independent summands, final sum: for independent mean-zero `η_i`
with `‖η_i‖ ≤ a` a.s., `Σ_i E‖η_i‖² ≤ b²`, `a > 0`, `b² > 0` and `r ≥ 0`:
`Pr(‖Σ_i η_i‖ ≥ r) ≤ 2 exp(r/a − (r/a + b²/a²) log(1 + ra/b²))`. -/
def pinelis : Prop :=
  ∀ (ι H : Type) [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (η : ∀ i, Ω i → H) (a b2 r : ℝ),
    (∀ i, StronglyMeasurable (η i)) → (∀ i, ∫ ω, η i ω ∂(μ i) = 0) → (∀ i, ∀ᵐ ω ∂(μ i), ‖η i ω‖ ≤ a) →
    ∑ i, ∫ ω, ‖η i ω‖ ^ 2 ∂(μ i) ≤ b2 → 0 < a → 0 < b2 → 0 ≤ r →
      Measure.pi μ {ω | r ≤ ‖∑ i, η i (ω i)‖} ≤ ENNReal.ofReal (psiPin a b2 r)

/-! ### §3.3: validity for admissible choices -/

/-- **NOTE §3.3**, "the proof of Theorem P goes through verbatim". For kernel constants `D, v, ρ̄`, `α ∈ [0,1)`, `n, m ≥ 1`,
every pair with `TV(P,Q) ≤ α`, every `t₁ ≥ 0` with `Ψ_H(t₁;β,s,c) + Ψ_H(t₁;β,1/n,1/n) + Ψ_H(t₁;β,1/m,1/m) ≤ δ₁`, every
`t₂ ≥ 0` and all `λ₁, λ₂, λ₃ > 0` with `Ψ_R^{λ₁}(t₂;β,{n}) + Ψ_R^{λ₂}(t₂;β,{m}) + Ψ_R^{λ₃}(t₂;β,{n,m}) ≤ δ₂`:
`Pr(D̂_α > t₁ + ρ̄ t₂) ≤ δ₁ + δ₂`. -/
def sharp_level : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D v ρbar : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α δ1 δ2 t1 t2 l1 l2 l3 : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → KernelConsts φ D v ρbar →
    0 ≤ α → α < 1 → 1 ≤ n → 1 ≤ m → StatFormal.Distances.tvDist P Q ≤ α →
    0 ≤ t1 → 0 ≤ t2 → 0 < l1 → 0 < l2 → 0 < l3 →
    psiH3 D v ρbar (1 / (1 - α)) t1 n m ≤ δ1 →
    psiRlam (1 / (1 - α)) l1 t2 [n] + psiRlam (1 / (1 - α)) l2 t2 [m] + psiRlam (1 / (1 - α)) l3 t2 [n, m] ≤ δ2 →
      sampleLaw P Q n m {z | t1 + ρbar * t2 < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal (δ1 + δ2)

/-- **NOTE §3.3**, the same with the printed `Ψ_R` (the infimum over `λ > 0`): every `t₂ ≥ 0` with
`Ψ_R(t₂;β,{n}) + Ψ_R(t₂;β,{m}) + Ψ_R(t₂;β,{n,m}) ≤ δ₂`. -/
def sharp_level_inf : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D v ρbar : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α δ1 δ2 t1 t2 : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → KernelConsts φ D v ρbar →
    0 ≤ α → α < 1 → 1 ≤ n → 1 ≤ m → StatFormal.Distances.tvDist P Q ≤ α →
    0 ≤ t1 → 0 ≤ t2 → psiH3 D v ρbar (1 / (1 - α)) t1 n m ≤ δ1 → psiR3 (1 / (1 - α)) t2 n m ≤ δ2 →
      sampleLaw P Q n m {z | t1 + ρbar * t2 < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal (δ1 + δ2)

/-- **NOTE §3.3**, `α = 0`: every `t ≥ 0` with `Ψ_H(t;1,s,c) ≤ δ` has `Pr(D̂_0 > t) ≤ δ` for every pair with `TV(P,Q) ≤ 0`. -/
def sharp_level_zero : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D v ρbar : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (δ t : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → KernelConsts φ D v ρbar →
    1 ≤ n → 1 ≤ m → StatFormal.Distances.tvDist P Q ≤ 0 →
    0 ≤ t → psiH D v ρbar 1 (sNM n m) (cNM n m) t ≤ δ →
      sampleLaw P Q n m {z | t < Demp φ z.1 z.2 0} ≤ ENNReal.ofReal δ

/-! ### §3.3: the tail functions are monotone -/

/-- **NOTE §3.3**, "each tail function is pointwise nondecreasing in `β`", with the printed reasons: `Ψ_H(t;β,s',c')`
(for `D, v, ρ̄ ≥ 0`, `s', c' > 0`, `t ≥ 0`), `Ψ_R` at every fixed `λ > 0` and `Ψ_R` itself are nondecreasing in `β ≥ 1`;
the McDiarmid term is nondecreasing in `β > 0`; Pinelis' term is nondecreasing in `a` and in `b²` (`a, b² > 0`, `t ≥ 0`);
the two-point bound is nondecreasing in `β ≥ 1` (mean-preserving spread) at every `l`. -/
def tails_mono_beta : Prop :=
  (∀ D v ρbar β β' s' c' t : ℝ, 0 ≤ D → 0 ≤ v → 0 ≤ ρbar → 1 ≤ β → β ≤ β' → 0 < s' → 0 < c' → 0 ≤ t →
      psiH D v ρbar β s' c' t ≤ psiH D v ρbar β' s' c' t) ∧
    (∀ (β β' l t : ℝ) (K : List ℕ), 1 ≤ β → β ≤ β' → 0 < l → psiRlam β l t K ≤ psiRlam β' l t K) ∧
    (∀ (β β' t : ℝ) (K : List ℕ), 1 ≤ β → β ≤ β' → psiR β t K ≤ psiR β' t K) ∧
    (∀ D v β β' s' t : ℝ, 0 < β → β ≤ β' → 0 < s' → psiMcD D v β s' t ≤ psiMcD D v β' s' t) ∧
    (∀ a a' b2 b2' t : ℝ, 0 < a → a ≤ a' → 0 < b2 → b2 ≤ b2' → 0 ≤ t → psiPin a b2 t ≤ psiPin a' b2' t) ∧
    (∀ β β' l : ℝ, 1 ≤ β → β ≤ β' → twoPt β l ≤ twoPt β' l)

/-- **NOTE §3.3**, coupled constants, "every tail is nondecreasing in `(v², ρ̄)`": `Ψ_H` is nondecreasing in `v > 0` and in
`ρ̄ > 0` (for `D ≥ 0`, `β ≥ 1`, `s', c' > 0`, `t ≥ 0`); `Ψ_R` does not involve `(v, ρ̄)`. -/
def tails_mono_const : Prop :=
  ∀ D v v' ρbar ρbar' β s' c' t : ℝ, 0 ≤ D → 0 < v → v ≤ v' → 0 < ρbar → ρbar ≤ ρbar' → 1 ≤ β → 0 < s' → 0 < c' →
    0 ≤ t → psiH D v ρbar β s' c' t ≤ psiH D v' ρbar' β s' c' t

/-- The tails are nonincreasing in `t ≥ 0` (so the admissible sets of `t_1`, `t_2` are up-sets: any `t` above the smallest
root, e.g. the implementation's root `+ 10⁻⁶`, is admissible). For `D, v, ρ̄ ≥ 0`, `β ≥ 1`, `s', c' > 0`: `Ψ_H`; for
`β ≥ 1`: `Ψ_R` at every `λ > 0` and `Ψ_R`. -/
def tails_antitone_t : Prop :=
  (∀ D v ρbar β s' c' : ℝ, 0 ≤ D → 0 ≤ v → 0 ≤ ρbar → 1 ≤ β → 0 < s' → 0 < c' →
      AntitoneOn (fun t => psiH D v ρbar β s' c' t) (Ici 0)) ∧
    (∀ (β l : ℝ) (K : List ℕ), 1 ≤ β → 0 < l → Antitone (fun t => psiRlam β l t K)) ∧
    (∀ (β : ℝ) (K : List ℕ), 1 ≤ β → Antitone (fun t => psiR β t K))

/-! ### §3.3: the threshold `τ_{P'}` -/

/-- **NOTE §3.3**, level of `τ_{P'}` (smallest roots, minimum over `F`): for kernel constants, `α ∈ [0,1)`, `δ ∈ (0,1)`,
`n, m ≥ 1` and every pair with `TV(P,Q) ≤ α`, `Pr(D̂_α > τ_{P'}(α,δ)) ≤ δ`. -/
def sharp_tau_level : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D v ρbar : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → KernelConsts φ D v ρbar →
    0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → StatFormal.Distances.tvDist P Q ≤ α →
      sampleLaw P Q n m {z | tauPs D v ρbar α δ n m < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal δ

/-- **NOTE §3.3**, "so `τ_{P'}` is nondecreasing": for `D, v, ρ̄ ≥ 0`, `δ ∈ (0,1)`, `n, m ≥ 1`, `τ_{P'}(·,δ)` is nonnegative and
nondecreasing on `[0,1)`. -/
def sharp_tau_monotone : Prop :=
  ∀ (D v ρbar δ : ℝ) (n m : ℕ), 0 ≤ D → 0 ≤ v → 0 ≤ ρbar → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    MonotoneOn (fun α => tauPs D v ρbar α δ n m) (Ico 0 1) ∧ ∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ tauPs D v ρbar α δ n m

/-- **NOTE §3.3** with Lemma 1: for every pair, a measurable event of probability `≥ 1 − δ` on which `D̂_α ≤ τ_{P'}(α,δ)`
for every `α ∈ [0,1)` with `TV(P,Q) ≤ α`, every rejected level is `< TV(P,Q)`, and (when `TV(P,Q) < 1`) `α̂ ≤ TV(P,Q)`. -/
def sharp_tau_one_event : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D v ρbar : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → KernelConsts φ D v ρbar →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m E ∧
        ∀ z ∈ E,
          (∀ α ∈ Ico (0 : ℝ) 1, StatFormal.Distances.tvDist P Q ≤ α →
            Demp φ z.1 z.2 α ≤ tauPs D v ρbar α δ n m) ∧
          (StatFormal.Distances.tvDist P Q < 1 →
            alphaHat (Demp φ z.1 z.2) (fun α => tauPs D v ρbar α δ n m) ≤ StatFormal.Distances.tvDist P Q) ∧
          (∀ α ∈ Ico (0 : ℝ) 1, tauPs D v ρbar α δ n m < Demp φ z.1 z.2 α → α < StatFormal.Distances.tvDist P Q)

/-! ### §3.3: coupled constants -/

/-- **NOTE §3.3**, coupled constants, "`τ^{cpl}_{P'} = sup_u τ_{P'}(·; v² = κ² − u, ρ̄ = √(κ²+u))` is valid": for a kernel with
`k ≥ 0` and `k(x,x) ≡ κ²`, any bound `D` on `‖φ(x) − φ(x')‖`, `α ∈ [0,1)`, `δ ∈ (0,1)`, `n, m ≥ 1` and every pair with
`TV(P,Q) ≤ α`: every `t ≥ 0` with `t ≥ τ_{P'}(α,δ; v = √(κ²−u), ρ̄ = √(κ²+u))` for all `u ∈ [0,κ²)` has `Pr(D̂_α > t) ≤ δ`. -/
def coupled_sharp : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D t : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
    (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) →
    0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → StatFormal.Distances.tvDist P Q ≤ α →
    0 ≤ t → (∀ u ∈ Ico (0 : ℝ) (κ ^ 2), tauPs D (√(κ ^ 2 - u)) (√(κ ^ 2 + u)) α δ n m ≤ t) →
      sampleLaw P Q n m {z | t < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal δ

/-- **NOTE §3.3**, the coupled threshold itself: for a kernel with `k ≥ 0` and `k(x,x) ≡ κ²`, any bound `D`, `δ ∈ (0,1)` and
`n, m ≥ 1`, `τ^{cpl}_{P'}` (`tauCpl`) is a valid uniform threshold, nonnegative and nondecreasing on `[0,1)`, and gives one
event for every pair. -/
def coupled_cpl : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
    (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) → 0 ≤ D →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      IsValidThreshold φ n m δ (fun α => tauCpl D κ α δ n m) ∧
      MonotoneOn (fun α => tauCpl D κ α δ n m) (Ico 0 1) ∧ (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ tauCpl D κ α δ n m) ∧
      ∀ P Q : Measure 𝒳, IsProbabilityMeasure P → IsProbabilityMeasure Q →
        OneEvent φ n m δ (fun α => tauCpl D κ α δ n m) P Q

/-- **NOTE §3.3**, "since every tail is nondecreasing in `(v², ρ̄)`, on a cell `[u_j,u_{j+1}]` the threshold is at most its
value at `(κ² − u_j, √(κ²+u_{j+1}))`": `τ_{P'}` is nondecreasing in `(v, ρ̄)` (for `D ≥ 0`, `0 < v ≤ v'`, `0 < ρ̄ ≤ ρ̄'`,
`α ∈ [0,1)`, `δ ∈ (0,1)`, `n, m ≥ 1`). -/
def coupled_tau_mono : Prop :=
  ∀ (D v v' ρbar ρbar' α δ : ℝ) (n m : ℕ), 0 ≤ D → 0 < v → v ≤ v' → 0 < ρbar → ρbar ≤ ρbar' →
    0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      tauPs D v ρbar α δ n m ≤ tauPs D v' ρbar' α δ n m

/-- The uniform grid `u_j = jκ²/J`, `j = 0, …, J`, (`J ≥ 1`; the implementation takes `J = 20`) covers `[0, κ²]` by the cells
`[u_j, u_{j+1}]`, `j < J`. -/
def uniform_grid_cover : Prop :=
  ∀ (κ : ℝ) (J : ℕ), 1 ≤ J → ∀ u ∈ Icc (0 : ℝ) (κ ^ 2), ∃ j < J,
    (j : ℝ) * κ ^ 2 / J ≤ u ∧ u ≤ ((j : ℝ) + 1) * κ ^ 2 / J

/-- **NOTE §3.3**, "the maximum over a 20-cell grid is a rigorous upper bound on the supremum": for the uniform grid with
`J ≥ 1` cells and the printed corners `v_j = √(κ² − u_j)`, `ρ̄_j = √(κ² + u_{j+1})`, `u_j = jκ²/J`, every
`τ_{P'}(α,δ; √(κ²−u), √(κ²+u))`, `u ∈ [0,κ²)`, and hence `τ^{cpl}_{P'}(α,δ)`, is at most the grid maximum (for `D ≥ 0`,
`α ∈ [0,1)`, `δ ∈ (0,1)`, `n, m ≥ 1`). -/
def coupled_grid_bound : Prop :=
  ∀ (D κ α δ : ℝ) (J n m : ℕ), 0 ≤ D → 1 ≤ J → 0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    (∀ u ∈ Ico (0 : ℝ) (κ ^ 2), tauPs D (√(κ ^ 2 - u)) (√(κ ^ 2 + u)) α δ n m ≤
      tauGrid D (fun j => √(κ ^ 2 - (j : ℝ) * κ ^ 2 / J)) (fun j => √(κ ^ 2 + ((j : ℝ) + 1) * κ ^ 2 / J)) J α δ n m) ∧
    tauCpl D κ α δ n m ≤
      tauGrid D (fun j => √(κ ^ 2 - (j : ℝ) * κ ^ 2 / J)) (fun j => √(κ ^ 2 + ((j : ℝ) + 1) * κ ^ 2 / J)) J α δ n m

/-- **NOTE §3.3** (`thresholds.tau_P_coupled`), the grid threshold is valid: for a kernel with `k ≥ 0` and `k(x,x) ≡ κ²`, any
bound `D`, cells `[lo_j, hi_j]`, `j < J`, covering `[0,κ²]`, and cell constants with `v_j ≥ 0`, `v_j² ≥ κ² − lo_j` and
`ρ̄_j ≥ min(√(κ² + hi_j), D)` (the printed corners and the implementation's `min(·, D_φ)` corners are such choices):
`Pr(D̂_α > max_j τ_{P'}(α,δ; v_j, ρ̄_j)) ≤ δ` for `α ∈ [0,1)`, `δ ∈ (0,1)`, `n, m ≥ 1` and every pair with `TV(P,Q) ≤ α`. -/
def coupled_grid_level : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D : ℝ) (J : ℕ) (lo hi v ρ : ℕ → ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (α δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
    (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) →
    (∀ u ∈ Icc (0 : ℝ) (κ ^ 2), ∃ j < J, lo j ≤ u ∧ u ≤ hi j) →
    (∀ j < J, 0 ≤ v j ∧ κ ^ 2 - lo j ≤ v j ^ 2 ∧ min (√(κ ^ 2 + hi j)) D ≤ ρ j) →
    0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → StatFormal.Distances.tvDist P Q ≤ α →
      sampleLaw P Q n m {z | tauGrid D v ρ J α δ n m < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal δ

/-- The grid threshold is nonnegative and nondecreasing in `α` on `[0,1)` (for `D ≥ 0`, `v_j, ρ̄_j ≥ 0`, `δ ∈ (0,1)`,
`n, m ≥ 1`), and for a kernel and grid as in `coupled_grid_level` it gives one event for every pair. -/
def coupled_grid_one_event : Prop :=
  (∀ (D : ℝ) (J : ℕ) (v ρ : ℕ → ℝ) (δ : ℝ) (n m : ℕ), 0 ≤ D → (∀ j < J, 0 ≤ v j ∧ 0 ≤ ρ j) → 0 < δ → δ < 1 →
      1 ≤ n → 1 ≤ m →
      MonotoneOn (fun α => tauGrid D v ρ J α δ n m) (Ico 0 1) ∧ ∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ tauGrid D v ρ J α δ n m) ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D : ℝ) (J : ℕ) (lo hi v ρ : ℕ → ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
    (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) →
    (∀ u ∈ Icc (0 : ℝ) (κ ^ 2), ∃ j < J, lo j ≤ u ∧ u ≤ hi j) →
    (∀ j < J, 0 ≤ v j ∧ κ ^ 2 - lo j ≤ v j ^ 2 ∧ min (√(κ ^ 2 + hi j)) D ≤ ρ j) →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      OneEvent φ n m δ (fun α => tauGrid D v ρ J α δ n m) P Q

/-! ### §3.3: Corollary C -/

/-- **NOTE Corollary C** (general kernel, nonempty `𝒳`). Given a threshold `τ_A` that is nonnegative, nondecreasing on `[0,1)`
and valid (Theorem A, not formalised here), `τ_new = min{τ_A, τ_P, τ_{P'}}` is valid and uniform, nonnegative and
nondecreasing on `[0,1)`, and gives one event for every pair. -/
def corollary_C : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [Nonempty 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D v ρbar : ℝ) (τA : ℝ → ℝ) (δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → KernelConsts φ D v ρbar →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τA α) → MonotoneOn τA (Ico 0 1) → IsValidThreshold φ n m δ τA →
      IsValidThreshold φ n m δ (fun α => min (τA α) (min (tauP D v ρbar α δ n m) (tauPs D v ρbar α δ n m))) ∧
      MonotoneOn (fun α => min (τA α) (min (tauP D v ρbar α δ n m) (tauPs D v ρbar α δ n m))) (Ico 0 1) ∧
      (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ min (τA α) (min (tauP D v ρbar α δ n m) (tauPs D v ρbar α δ n m))) ∧
      ∀ P Q : Measure 𝒳, IsProbabilityMeasure P → IsProbabilityMeasure Q →
        OneEvent φ n m δ (fun α => min (τA α) (min (tauP D v ρbar α δ n m) (tauPs D v ρbar α δ n m))) P Q

/-- **NOTE Corollary C** (kernel with `k ≥ 0` and `k(x,x) ≡ κ²`, nonempty `𝒳`): the same for
`τ_new = min{τ_A, τ_P, τ_{P'}, τ^{cpl}_{P'}}` with the printed supremum `τ^{cpl}_{P'}` (`tauCpl`). -/
def corollary_C_coupled : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [Nonempty 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D v ρbar : ℝ) (τA : ℝ → ℝ) (δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → KernelConsts φ D v ρbar →
    (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τA α) → MonotoneOn τA (Ico 0 1) → IsValidThreshold φ n m δ τA →
      IsValidThreshold φ n m δ (fun α => min (τA α) (min (tauP D v ρbar α δ n m)
        (min (tauPs D v ρbar α δ n m) (tauCpl D κ α δ n m)))) ∧
      MonotoneOn (fun α => min (τA α) (min (tauP D v ρbar α δ n m)
        (min (tauPs D v ρbar α δ n m) (tauCpl D κ α δ n m)))) (Ico 0 1) ∧
      (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ min (τA α) (min (tauP D v ρbar α δ n m)
        (min (tauPs D v ρbar α δ n m) (tauCpl D κ α δ n m)))) ∧
      ∀ P Q : Measure 𝒳, IsProbabilityMeasure P → IsProbabilityMeasure Q →
        OneEvent φ n m δ (fun α => min (τA α) (min (tauP D v ρbar α δ n m)
          (min (tauPs D v ρbar α δ n m) (tauCpl D κ α δ n m)))) P Q

/-- **NOTE Corollary C** as implemented (`thresholds.tau_new` with `tau_P_coupled`, kernel with `k ≥ 0` and `k(x,x) ≡ κ²`,
nonempty `𝒳`): the same for `τ_new = min{τ_A, τ_P, τ_{P'}, τ_grid}` with the grid threshold of a grid as in
`coupled_grid_level`. -/
def corollary_C_grid : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [Nonempty 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D v ρbar : ℝ) (J : ℕ) (lo hi vg ρg : ℕ → ℝ) (τA : ℝ → ℝ) (δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → KernelConsts φ D v ρbar →
    (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) →
    (∀ u ∈ Icc (0 : ℝ) (κ ^ 2), ∃ j < J, lo j ≤ u ∧ u ≤ hi j) →
    (∀ j < J, 0 ≤ vg j ∧ κ ^ 2 - lo j ≤ vg j ^ 2 ∧ min (√(κ ^ 2 + hi j)) D ≤ ρg j) →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τA α) → MonotoneOn τA (Ico 0 1) → IsValidThreshold φ n m δ τA →
      IsValidThreshold φ n m δ (fun α => min (τA α) (min (tauP D v ρbar α δ n m)
        (min (tauPs D v ρbar α δ n m) (tauGrid D vg ρg J α δ n m)))) ∧
      MonotoneOn (fun α => min (τA α) (min (tauP D v ρbar α δ n m)
        (min (tauPs D v ρbar α δ n m) (tauGrid D vg ρg J α δ n m)))) (Ico 0 1) ∧
      (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ min (τA α) (min (tauP D v ρbar α δ n m)
        (min (tauPs D v ρbar α δ n m) (tauGrid D vg ρg J α δ n m)))) ∧
      ∀ P Q : Measure 𝒳, IsProbabilityMeasure P → IsProbabilityMeasure Q →
        OneEvent φ n m δ (fun α => min (τA α) (min (tauP D v ρbar α δ n m)
          (min (tauPs D v ρbar α δ n m) (tauGrid D vg ρg J α δ n m)))) P Q

end Claims
end StatFormal.Wave30ts
