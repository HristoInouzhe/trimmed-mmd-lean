import StatFormal.Wave30tz.Statements
import StatFormal.Wave31tl.Statements
import StatFormal.Wave31to.Statements
import StatFormal.Wave31tn.Statements
import StatFormal.Wave31tm.Statements
import StatFormal.Wave31tc.Statements
import StatFormal.Wave30tu.Crossing.Statements
import StatFormal.Wave31ta.Statements
import StatFormal.Wave30tr.Statements
import StatFormal.Wave31tp.Statements
import Mathlib.Probability.Independence.Basic

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31tr: the non-Fourier gaps of trimmed-mmd (Annals of Statistics version)

Printed source: `~/projects/tmmd-aos-brief/fullstack/NEW_STATEMENTS_31tr.md` (v5.1 with the critic's text notes n1, c2, c3 applied;
copy in `certify/sources/tmmd-aos-NEW_STATEMENTS-wave31tr.md`). Paper: trimmed-mmd `aos/` at `1fbc8df` (line numbers of that
commit; printed numbers of `aos/main.aux`, `aos/supplement.aux`). Plan: `PLAN_31tr.md`; gaps closed: GAPS C1 (the paper's own run),
B2, C2, C3, C5 (split-sample half), C7, D1–D4, D8, D9, A12, E7, E9, E14, E15, E18, the sweep's group (A), Proposition 5.10 and
Lemmas S4.17–S4.18, and the procedure-level sentences new at `b3125cf` (T47–T57).

Claim list (draft numbers T1–T57; T21, T22(a), T23, T30, T43, T44 dropped with their printed text):
C1, the paper's run: `genuine_rules`, `printed_cuts`, `npQuantile_rule`, `ordStat_facts` (T1); `printedPairing_exists`,
`printedPairing_batch`, `printedPairing_default` (T2); `qp_measurable_argmin` (T3); `paperRun_exists`, `paperRun_exists_printed` (T4),
`paperRun_exists_fractions` (existence conjunct of T7, T12); `paperRun_admissible` (T5); `paperRun_betting`, `paperRun_betting_cond`
(T6); `paper_lo_consistency`, `paper_lo_refining` (T7); `paper_lorate_O`, `paper_same_rate` (T8); `paper_lorate_i`, `paper_lorate_ii`,
`paper_lorate_nologJ`, `paper_lorate_general` (T9); `paper_newrates_i_a`, `paper_newrates_i_b` (T10); `paper_minimax_ii` (T11);
`paper_alphalo` (T12). Each of T6–T12 is `genuine_rules ∧ <existence at lowQ/highQ, v₀ ≡ 1> ∧ <every paper run with quantile rules>`.
B2: `gauss_qdens_formula`, `gauss_qdens_Q_Qprime` (T13). C2: `alpha0_uniform` (T14), `alpha0_fit_uniform_as` (T15),
`ksPlus_locally_constant`, `ex_ks_stable` (T16), `alpha0_reject_le`, `alpha0_inconsistent`, `alpha0_gate` (T17). C3: `fw_gap`,
`fw_exact` (T18), `fitted_ramp_fw` (T19), `lo_lower_bound_fw`, `lo_consistency_fw` (T20). C5: `same_quantile` (T22(b)). C7:
`dbar_le_D_le` (T24), `margin_dbar_factor` (T25), `any_threshold_converse` (T26). D4: `bangbang_aos` (T27). E: `tv_one_sided_ks`,
`ks_lower_confidence` (T28), `contact_densities`, `contact_gauss_mix`, `minimax_class_apart` (T29), `default_pairs_three_quarters` (T31).
Sweep (A): `house_encoding` (T32), `witness_unique` (T33), `contam_equiv`, `trimming_removal`, `different_fractions` (T34),
`kernel_constants` (T35), `regions_nested` (T36), `bathtub_quantiles` (T37).
Proposition 5.10, Lemmas S4.17–S4.18: `excess_bathtub` (T38), `excess_identity` (T39), `excess_i` (T40), `excess_ii` (T41),
`excess_laplace`, `laplace_green` (T42), each of T38–T42 as (G) ∧ (Pr); `oscillation_blind` (T45); `fncert_drift_err`, `fncert_upper`,
`fncert_rejected_upper`, `fncert_betting_error` (T46).
New at `b3125cf`: `laplace_qdens_fails`, `finite_support_not_qdens`, `margin_without_qdens` (T47); `alg_prior` (T48(c); T48(a), (b),
(d) are rows); `kernel_run_valid`, `median_bandwidth`, `kernel_profiles` (T49); `averaged_evalue`, `bound_summaries` (T50(b)–(d));
`trimming_at_lower` (T51); `propensity_core` (T52); `tv_pushforward` (T53); `upper_end` (T54); `margin_eps0` (T55); `taup_jump`,
`taup_welldefined`, `taup_valid_bound`, `taup_consistent_below` (T56); `bayes_risk` (T57).

Encodings (declared; details in the source's "Common setting"): `nb` batches bet on (printed `B`); boundaries `cutLabel`/`IsBoundaries`;
the printed pairing in a decidable form (`IsPrintedPairing`, guarded for one-sided empty batches); two cut rules, `qt` on the `X` side
at `1−α` and `qu` on the `Y` side at `α`, printed `lowQ`/`highQ`, the universal parts over every `IsQuantileRule` (within one rank,
`eq:cutrank`); the QP selection required only on nonempty fitting sides; `eq:fractions` with indicator weights (`fracFormula`); the
index order is an order fixed in advance (equivalent in law for i.i.d. data); `IsKernelRun` is the run as computed at the kernel level
(measurable parameter space, no positive definiteness); `IsFWPoint` the Frank–Wolfe point of relative gap `ρ`; densities nonnegative
and measurable where a density is meant; laws on `[0,1]` are laws on `ℝ` carried by `[0,1]`.
Junk values: `ordStat` only at ranks in `[1,k]`; `ownX`, `ownY`, `witness`, `kwit` divide by `D̂`, read only where `D̂ > 0`; `ramp`
divides by `t − u`, read only where `u < t`; `fracFormula` divides by `N·max(v²_min, ·)` with `v²_min > 0` and by `w₀ + |S| > 0`;
`sSup`/`sInf` only of nonempty bounded sets (stated per claim); `ENNReal.ofReal` of a negative number is `0` (a true, weaker bound).

FROZEN 2026-11-22 after the independent critic's reviews (`CRITIC_31tr.md`, `_v2`–`_v4`, `CRITIC_F1_b3125cf.md`; diff-only re-check
`CRITIC_F1b_1fbc8df.md`: READY TO FREEZE, text notes n1, c2, c3 applied before hashing). Hashed in `certify/statements.lock` (with its
imports); AI agents must not edit this file.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr

open StatFormal StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tz StatFormal.Wave31tl StatFormal.Wave30tp
  StatFormal.Wave31to StatFormal.Wave31tn StatFormal.Wave31tm
  StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.ZeroSet StatFormal.TrimmedMMD.BangBang
  StatFormal.Wave30tx StatFormal.TrimmedMMD

-- DEFS-BEGIN
/-- The batch of index `i` for interior boundaries `c 1 ≤ ⋯ ≤ c nb` (batch `b` is `[c b, c (b+1))`, `c 0 = 0`, `c (nb+1) = n`). -/
def cutLabel (nb : ℕ) (c : ℕ → ℕ) (i : ℕ) : ℕ := ((Finset.Icc 1 nb).filter fun b => c b ≤ i).card

/-- Interior boundaries: nondecreasing on `{1, …, nb}`, each at most the sample size. -/
def IsBoundaries (nb n : ℕ) (c : ℕ → ℕ) : Prop := MonotoneOn c (Set.Icc 1 nb) ∧ ∀ b ∈ Set.Icc 1 nb, c b ≤ n

/-- The printed pairing (S3 :105-111), in a decidable form: `N = Σ_b min(n_b, m_b)`; pairs numbered batch by batch (`bat` monotone,
values in `[1, nb]`); in a batch with `n_b ≤ m_b` the `X`-blocks are the singletons of the batch, each used once, and the `Y`-blocks are
order-convex (consecutive) subsets of the batch partitioning it, with sizes differing by at most one; the mirror otherwise. A batch
with an empty side gives no pair (`N_b = min(n_b, m_b) = 0`): the block clauses are guarded by `1 ≤ n_b` (resp. `1 ≤ m_b`) (critic P1). -/
def IsPrintedPairing {n m N : ℕ} (nb : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ)
    (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) : Prop :=
  N = ∑ b ∈ Finset.Icc 1 nb, min (batchCount lx b) (batchCount ly b) ∧ Monotone bat ∧
  (∀ k, 1 ≤ bat k ∧ bat k ≤ nb) ∧
  (∀ b ∈ Finset.Icc 1 nb, (Finset.univ.filter fun k => bat k = b).card = min (batchCount lx b) (batchCount ly b)) ∧
  ∀ b ∈ Finset.Icc 1 nb,
    (1 ≤ batchCount lx b → batchCount lx b ≤ batchCount ly b →
      (∀ k, bat k = b → ∃ i, lx i = b ∧ A k = {i}) ∧
      (∀ i, lx i = b → (Finset.univ.filter fun k => bat k = b ∧ A k = {i}).card = 1) ∧
      (∀ k, bat k = b → ∀ j ∈ B k, ly j = b) ∧
      (∀ j, ly j = b → (Finset.univ.filter fun k => bat k = b ∧ j ∈ B k).card = 1) ∧
      (∀ k, bat k = b → ∀ j j' j'' : Fin m, j ∈ B k → j'' ∈ B k → j ≤ j' → j' ≤ j'' → j' ∈ B k) ∧
      (∀ k k', bat k = b → bat k' = b → (B k).card ≤ (B k').card + 1)) ∧
    (1 ≤ batchCount ly b → batchCount ly b < batchCount lx b →
      (∀ k, bat k = b → ∃ j, ly j = b ∧ B k = {j}) ∧
      (∀ j, ly j = b → (Finset.univ.filter fun k => bat k = b ∧ B k = {j}).card = 1) ∧
      (∀ k, bat k = b → ∀ i ∈ A k, lx i = b) ∧
      (∀ i, lx i = b → (Finset.univ.filter fun k => bat k = b ∧ i ∈ A k).card = 1) ∧
      (∀ k, bat k = b → ∀ i i' i'' : Fin n, i ∈ A k → i'' ∈ A k → i ≤ i' → i' ≤ i'' → i' ∈ A k) ∧
      (∀ k k', bat k = b → bat k' = b → (A k).card ≤ (A k').card + 1))

section Defs

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A quantile rule: measurable in the values, and within one rank of the quantile (`eq:cutrank`). -/
def IsQuantileRule (q : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) : Prop :=
  (∀ k p, Measurable fun h : Fin k → ℝ => q k h p) ∧
  ∀ (k : ℕ) (h : Fin k → ℝ) (p : ℝ), 1 ≤ k → 0 ≤ p → p ≤ 1 →
    q k h p ∈ Icc (ordStat h (rkLo k p)) (ordStat h (rkHi k p))

/-- X2 (shared with 31tu): a genuine-quantile rule, measurable in the values and, for `k ≥ 1`, `p ∈ [0,1]`, returning a genuine empirical
`p`-quantile (`#{h_i < q} ≤ kp ≤ #{h_i ≤ q}`) in the range of the values (S3 :106-108 "a genuine empirical `(1−α)`-quantile"). -/
def IsGenuineQuantileRule (q : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) : Prop :=
  (∀ k p, Measurable fun h : Fin k → ℝ => q k h p) ∧
  ∀ (k : ℕ) (h : Fin k → ℝ) (p : ℝ), 1 ≤ k → 0 ≤ p → p ≤ 1 →
    IsEmpQuantile h p (q k h p) ∧ (∃ i, h i ≤ q k h p) ∧ (∃ i, q k h p ≤ h i)

/-- The smallest empirical `p`-quantile `h_(max(1,⌈kp⌉))` (§4 :61-63: `t̂_b`, "their `⌈n_{<b}(1−α)⌉`-th order statistic"). -/
def lowQ (k : ℕ) (h : Fin k → ℝ) (p : ℝ) : ℝ := ordStat h (max 1 ⌈(k : ℝ) * p⌉₊)

/-- The largest empirical `p`-quantile `h_(min(k,⌊kp⌋+1))` (§4 :63-64: `û_b`, "the `(⌊m_{<b}α⌋+1)`-th"). -/
def highQ (k : ℕ) (h : Fin k → ℝ) (p : ℝ) : ℝ := ordStat h (min k (⌊(k : ℝ) * p⌋₊ + 1))

/-- The `v₀²` rule of `eq:fractions`: measurable, in `[0,4]`, a function of the batches before `b`. -/
def IsPriorRule {J n m : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ)
    (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) : Prop :=
  ∀ j b, Measurable (fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => v0 j b p.1 p.2) ∧ (∀ x y, v0 j b x y ∈ Icc (0 : ℝ) 4) ∧
    ∀ x x' y y', (∀ i, lx i < b → x i = x' i) → (∀ j', ly j' < b → y j' = y' j') → v0 j b x y = v0 j b x' y'

/-- A measurable selection of exact minimizers of `eq:qp`. -/
def IsQPSel (φ : 𝒳 → H) (α : ℝ) {n m : ℕ}
    (σ : (Fin n → 𝒳) × (Fin m → 𝒳) → (Fin n → ℝ) × (Fin m → ℝ)) : Prop :=
  Measurable σ ∧ ∀ p, IsQPMin φ α p.1 p.2 (σ p).1 (σ p).2

/-- `eq:fractions` with indicator weights `e l ∈ {0,1}` (pair `l` bet on). -/
def fracFormula (lmax α L : ℝ) (N : ℕ) (s2 w0 s0 : ℝ) {k : ℕ} (e z : Fin k → ℝ) : ℝ :=
  min (lmax / (1 + α)) (√(2 * L / (N * max s2
    ((w0 * s0 + ∑ i, e i * (z i - α - (∑ l, if l < i then e l * (z l - α) else 0) /
        (w0 + ∑ l, if l < i then e l else 0)) ^ 2) / (w0 + ∑ i, e i)))))

open Classical in
/-- The paper's run (§4.2, S3 :97-159, Algorithm S1), with the B1 guard: the QP selection is required only on nonempty fitting sides.
v5: `t̂ = qt n_{<b} (own-term X values) (1−α)`, `û = qu m_{<b} (own-term Y values) α`; the printed rules are `qt = lowQ`, `qu = highQ`. -/
def IsPaperRun {J n m : ℕ} (R : LoRun 𝒳 J n m) (φ : 𝒳 → H) (α : Fin J → ℝ) (δ lmax s2 w0 : ℝ)
    (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ)
    (nb : ℕ) (cx cy : ℕ → ℕ) : Prop :=
  IsBoundaries nb n cx ∧ IsBoundaries nb m cy ∧
  (∀ i : Fin n, R.lx i = cutLabel nb cx i) ∧ (∀ j : Fin m, R.ly j = cutLabel nb cy j) ∧
  IsPrintedPairing nb R.lx R.ly R.bat R.A R.B ∧ IsPriorRule R.lx R.ly v0 ∧
  ∃ σ : (j : Fin J) → (b : ℕ) → (Fin (fitCard R.lx b) → 𝒳) × (Fin (fitCard R.ly b) → 𝒳) →
        (Fin (fitCard R.lx b) → ℝ) × (Fin (fitCard R.ly b) → ℝ),
    (∀ j b, 1 ≤ fitCard R.lx b → 1 ≤ fitCard R.ly b → IsQPSel φ (α j) (σ j b)) ∧
    (∀ (j : Fin J) (b : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳),
      (R.has j b x y ↔
        (1 ≤ fitCard R.lx b ∧ 1 ≤ fitCard R.ly b ∧
          0 < qpVal φ (fitSample R.lx b x) (fitSample R.ly b y) (σ j b (fitSample R.lx b x, fitSample R.ly b y)).1
            (σ j b (fitSample R.lx b x, fitSample R.ly b y)).2 ∧
          qu (fitCard R.ly b) (ownY φ (fitSample R.lx b x) (fitSample R.ly b y)
              (σ j b (fitSample R.lx b x, fitSample R.ly b y)).1 (σ j b (fitSample R.lx b x, fitSample R.ly b y)).2) (α j) <
            qt (fitCard R.lx b) (ownX φ (fitSample R.lx b x) (fitSample R.ly b y)
              (σ j b (fitSample R.lx b x, fitSample R.ly b y)).1 (σ j b (fitSample R.lx b x, fitSample R.ly b y)).2) (1 - α j))) ∧
      R.g j b x y = if R.has j b x y then
          ramp (fun z => ⟪witness φ (fitSample R.lx b x) (fitSample R.ly b y)
              (σ j b (fitSample R.lx b x, fitSample R.ly b y)).1 (σ j b (fitSample R.lx b x, fitSample R.ly b y)).2, φ z⟫_ℝ)
            (qt (fitCard R.lx b) (ownX φ (fitSample R.lx b x) (fitSample R.ly b y)
              (σ j b (fitSample R.lx b x, fitSample R.ly b y)).1 (σ j b (fitSample R.lx b x, fitSample R.ly b y)).2) (1 - α j))
            (qu (fitCard R.ly b) (ownY φ (fitSample R.lx b x) (fitSample R.ly b y)
              (σ j b (fitSample R.lx b x, fitSample R.ly b y)).1 (σ j b (fitSample R.lx b x, fitSample R.ly b y)).2) (α j))
        else fun _ => 0) ∧
    ∀ (j : Fin J) (k : Fin R.N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : Fin k → ℝ),
      R.lam j k x y z = if R.has j (R.bat k) x y then
          fracFormula lmax (α j) (Real.log (1 / δ)) R.N s2 w0 (v0 j (R.bat k) x y)
            (fun l : Fin k => if R.has j (R.bat (Fin.castLE k.isLt.le l)) x y then 1 else 0) z
        else 0

end Defs
-- DEFS-END

section Extra

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Batch fractions fixed in advance: `0 = π 0 < π 1 < ⋯ < π nb < π (nb+1) = 1` (S3 :99-101). -/
def IsFractions (nb : ℕ) (π : ℕ → ℝ) : Prop :=
  π 0 = 0 ∧ π (nb + 1) = 1 ∧ StrictMonoOn π (Set.Icc 0 (nb + 1))

/-- Interior boundaries within one of `π b · n` (any rounding, "at these fractions of its size"). -/
def BoundariesNear (nb : ℕ) (π : ℕ → ℝ) (n : ℕ) (c : ℕ → ℕ) : Prop :=
  ∀ b ∈ Set.Icc 1 nb, |(c b : ℝ) - π b * n| ≤ 1

/-- The population variance `k⁻¹Σ(v_i − v̄)²` (numpy's `var`, `ddof = 0`). -/
def empVar {k : ℕ} (v : Fin k → ℝ) : ℝ := (∑ i, (v i - (∑ l, v l) / k) ^ 2) / k

open Classical in
/-- Algorithm S1's initial variance on a batch that is bet on: `max{s_X² + s_Y² n_[b]/m_[b], 10⁻⁴}` (mirrored if `n_[b] > m_[b]`), with
`s_X², s_Y²` the variances of the ramp `ψ_b` at the fitting `X`'s and `Y`'s; `1` on a batch that is not bet on (never read there). -/
def algPrior {J n m : ℕ} (R : LoRun 𝒳 J n m) (j : Fin J) (b : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) : ℝ :=
  if R.has j b x y then
    max (if (batchCount R.lx b : ℝ) ≤ batchCount R.ly b then
          empVar (fun i => R.g j b x y (fitSample R.lx b x i)) +
            empVar (fun i => R.g j b x y (fitSample R.ly b y i)) * batchCount R.lx b / batchCount R.ly b
        else
          empVar (fun i => R.g j b x y (fitSample R.ly b y i)) +
            empVar (fun i => R.g j b x y (fitSample R.lx b x i)) * batchCount R.ly b / batchCount R.lx b)
      (1 / 10000)
  else 1

/-- The wealth of level `j` at the horizon `N` (no stopping): `K_N = ∏_{k<N}(1 + λ_k(Z_k − α_j))`. -/
def hzWealth {J n m : ℕ} (R : LoRun 𝒳 J n m) (α : Fin J → ℝ) (j : Fin J) (x : Fin n → 𝒳) (y : Fin m → 𝒳) : ℝ :=
  wealth (fun k => R.lam j k x y) (α j) (seqZ (U := Unit) (fun b _ => R.g j b) R.bat R.A R.B () x y) R.N

/-! #### T49, kernel level (v5.1) -/

/-- Kernel-level value of `eq:qp` at weights `(w, v)`: `√(max 0 (wᵀK_XX w − 2wᵀK_XY v + vᵀK_YY v))` (the norm of the difference of
embeddings for a positive semidefinite kernel; the `max 0` only makes it total). -/
def kqpVal (kf : 𝒳 → 𝒳 → ℝ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) : ℝ :=
  √(max 0 ((∑ i, ∑ i', w i * w i' * kf (x i) (x i')) - 2 * (∑ i, ∑ j, w i * v j * kf (x i) (y j)) +
    ∑ j, ∑ j', v j * v j' * kf (y j) (y j')))

/-- The kernel-level witness `f̂(z) = D̂⁻¹(Σ w_i k(x_i,z) − Σ v_j k(y_j,z))`. -/
def kwit (kf : 𝒳 → 𝒳 → ℝ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) (z : 𝒳) : ℝ :=
  (kqpVal kf x y w v)⁻¹ * ((∑ i, w i * kf (x i) z) - ∑ j, v j * kf (y j) z)

/-- Algorithm S1 line 9: `h̃_i = f̂(X_i) − w_i k(X_i,X_i)/D̂`. -/
def kownX (kf : 𝒳 → 𝒳 → ℝ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) (i : Fin n) : ℝ :=
  kwit kf x y w v (x i) - w i * kf (x i) (x i) / kqpVal kf x y w v

/-- Algorithm S1 line 9: `h̃′_j = f̂(Y_j) + v_j k(Y_j,Y_j)/D̂`. -/
def kownY (kf : 𝒳 → 𝒳 → ℝ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) (j : Fin m) : ℝ :=
  kwit kf x y w v (y j) + v j * kf (y j) (y j) / kqpVal kf x y w v

open Classical in
/-- T49 (a), v5.1: the run as computed, at the kernel level. A measurable parameter space `Θ`, a kernel family `k θ`, a parameter `θh b`
computed from the batches before `b` (bandwidth, scales), and any measurable capped weights selected from `(θ, fitting sample)` (an exact
minimizer, or the solver's output). No positive definiteness and no feature map. Otherwise as `IsPaperRun`. -/
def IsKernelRun {Θ : Type*} [MeasurableSpace Θ] {J n m : ℕ} (R : LoRun 𝒳 J n m) (kf : Θ → 𝒳 → 𝒳 → ℝ)
    (θh : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → Θ) (α : Fin J → ℝ) (δ lmax s2 w0 : ℝ)
    (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ)
    (nb : ℕ) (cx cy : ℕ → ℕ) : Prop :=
  IsBoundaries nb n cx ∧ IsBoundaries nb m cy ∧
  (∀ i : Fin n, R.lx i = cutLabel nb cx i) ∧ (∀ j : Fin m, R.ly j = cutLabel nb cy j) ∧
  IsPrintedPairing nb R.lx R.ly R.bat R.A R.B ∧ IsPriorRule R.lx R.ly v0 ∧
  (∀ b, Measurable (fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => θh b p.1 p.2) ∧
      ∀ x x' y y', (∀ i, R.lx i < b → x i = x' i) → (∀ j', R.ly j' < b → y j' = y' j') → θh b x y = θh b x' y') ∧
  ∃ σ : (j : Fin J) → (b : ℕ) → Θ × ((Fin (fitCard R.lx b) → 𝒳) × (Fin (fitCard R.ly b) → 𝒳)) →
        (Fin (fitCard R.lx b) → ℝ) × (Fin (fitCard R.ly b) → ℝ),
    (∀ j b, 1 ≤ fitCard R.lx b → 1 ≤ fitCard R.ly b →
      Measurable (σ j b) ∧ ∀ p, IsCapped (α j) (σ j b p).1 ∧ IsCapped (α j) (σ j b p).2) ∧
    (∀ (j : Fin J) (b : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳),
      (R.has j b x y ↔
        (1 ≤ fitCard R.lx b ∧ 1 ≤ fitCard R.ly b ∧
          0 < kqpVal (kf (θh b x y)) (fitSample R.lx b x) (fitSample R.ly b y) (σ j b (θh b x y, (fitSample R.lx b x, fitSample R.ly b y))).1
            (σ j b (θh b x y, (fitSample R.lx b x, fitSample R.ly b y))).2 ∧
          qu (fitCard R.ly b) (kownY (kf (θh b x y)) (fitSample R.lx b x) (fitSample R.ly b y)
              (σ j b (θh b x y, (fitSample R.lx b x, fitSample R.ly b y))).1 (σ j b (θh b x y, (fitSample R.lx b x, fitSample R.ly b y))).2) (α j) <
            qt (fitCard R.lx b) (kownX (kf (θh b x y)) (fitSample R.lx b x) (fitSample R.ly b y)
              (σ j b (θh b x y, (fitSample R.lx b x, fitSample R.ly b y))).1 (σ j b (θh b x y, (fitSample R.lx b x, fitSample R.ly b y))).2) (1 - α j))) ∧
      R.g j b x y = if R.has j b x y then
          ramp (kwit (kf (θh b x y)) (fitSample R.lx b x) (fitSample R.ly b y)
              (σ j b (θh b x y, (fitSample R.lx b x, fitSample R.ly b y))).1 (σ j b (θh b x y, (fitSample R.lx b x, fitSample R.ly b y))).2)
            (qt (fitCard R.lx b) (kownX (kf (θh b x y)) (fitSample R.lx b x) (fitSample R.ly b y)
              (σ j b (θh b x y, (fitSample R.lx b x, fitSample R.ly b y))).1 (σ j b (θh b x y, (fitSample R.lx b x, fitSample R.ly b y))).2) (1 - α j))
            (qu (fitCard R.ly b) (kownY (kf (θh b x y)) (fitSample R.lx b x) (fitSample R.ly b y)
              (σ j b (θh b x y, (fitSample R.lx b x, fitSample R.ly b y))).1 (σ j b (θh b x y, (fitSample R.lx b x, fitSample R.ly b y))).2) (α j))
        else fun _ => 0) ∧
    ∀ (j : Fin J) (k : Fin R.N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : Fin k → ℝ),
      R.lam j k x y z = if R.has j (R.bat k) x y then
          fracFormula lmax (α j) (Real.log (1 / δ)) R.N s2 w0 (v0 j (R.bat k) x y)
            (fun l : Fin k => if R.has j (R.bat (Fin.castLE k.isLt.le l)) x y then 1 else 0) z
        else 0


end Extra

section T49b

/-- The `k × k` ordered pair distances `ρ(z_a, z_b)`, indexed by `Fin (k*k)`. -/
def pairDist {E : Type*} (ρ : E → E → ℝ) {k : ℕ} (z : Fin k → E) : Fin (k * k) → ℝ :=
  fun p => ρ (z (finProdFinEquiv.symm p).1) (z (finProdFinEquiv.symm p).2)

open Classical in
/-- The number of zero pair distances. -/
def zeroCount {N : ℕ} (d : Fin N → ℝ) : ℕ := (Finset.univ.filter fun p => d p = 0).card

/-- The median heuristic (`kernels.py:21-41`): numpy's median of the positive distances `ρ(z_a, z_b)`, `a < b`, and `1` when all
vanish. Each positive distance appears twice among the ordered pairs, so the average of the order statistics of ranks `c + N/2` and
`c + N/2 + 1` (`c` zeros, `N` positives) is that median. -/
def medianBw {E : Type*} (ρ : E → E → ℝ) {k : ℕ} (z : Fin k → E) : ℝ :=
  if zeroCount (pairDist ρ z) = k * k then 1 else
    (ordStat (pairDist ρ z) (zeroCount (pairDist ρ z) + (k * k - zeroCount (pairDist ρ z)) / 2) +
      ordStat (pairDist ρ z) (zeroCount (pairDist ρ z) + (k * k - zeroCount (pairDist ρ z)) / 2 + 1)) / 2

/-- The Euclidean distance after dividing coordinate `i` by `s i` (the batch-0 standardization; the mean cancels in differences). -/
def scaledDist {d : ℕ} (s : Fin d → ℝ) (x y : Fin d → ℝ) : ℝ := √(∑ i, ((x i - y i) / s i) ^ 2)

/-- The Laplace profile `exp(−‖(x−y)/s‖/σ)` at `θ = (σ, s)` (`|σ|` makes it total; equal to the printed kernel for `σ > 0`). -/
def lapK {d : ℕ} (θ : ℝ × (Fin d → ℝ)) (x y : Fin d → ℝ) : ℝ := Real.exp (-(scaledDist θ.2 x y) / |θ.1|)

/-- The Gaussian profile `exp(−‖(x−y)/s‖²/(2σ²))` at `θ = (σ, s)`. -/
def gaussK {d : ℕ} (θ : ℝ × (Fin d → ℝ)) (x y : Fin d → ℝ) : ℝ := Real.exp (-(scaledDist θ.2 x y) ^ 2 / (2 * θ.1 ^ 2))

/-- The batch-0 scales: the coordinatewise standard deviation (divisor `k`) of the pooled batch-0 points, `1` where it vanishes
(`splitting.py`: `sd[sd == 0] = 1.0`). -/
def b0Scale {d k : ℕ} (z : Fin k → Fin d → ℝ) (i : Fin d) : ℝ :=
  if empVar (fun l => z l i) = 0 then 1 else √(empVar (fun l => z l i))

end T49b

section BlockR

/-- numpy's `array_split` of `M` items into `K` consecutive blocks (T2 (a)): block `l` (0-based) starts at
`l⌊M/K⌋ + min(l, M mod K)`, so the first `M mod K` blocks have `⌊M/K⌋ + 1` items and the others `⌊M/K⌋`. Junk: ℕ division and
`%` by `K = 0` give `0` and `M`; it is read only for `1 ≤ K ≤ M` (a batch with `1 ≤ n_b ≤ m_b`, or the mirror). -/
def splitStart (M K l : ℕ) : ℕ := l * (M / K) + min l (M % K)

variable {𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The empirical separation of a direction `f` (T18, S3 :359-360): `s = min_{w′} Σ w′_i ⟨f, φ x_i⟩ − max_{v′} Σ v′_j ⟨f, φ y_j⟩`,
the minimum and the maximum over the capped simplices `Δ_α(n)`, `Δ_α(m)` of `eq:qp`. Junk guard: written with `sInf`/`sSup` of the
images; these sets are nonempty, compact and bounded exactly when `n, m ≥ 1` and `0 ≤ α < 1`, which any capped pair forces
(`IsCapped α w` with `Σ w_i = 1` and `w_i ≤ 1/(n(1−α))` is impossible otherwise), and `fwSep` is read only at a capped pair. -/
def fwSep (φ : 𝒳 → H) (α : ℝ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (f : H) : ℝ :=
  sInf ((fun w' : Fin n → ℝ => ∑ i, w' i * ⟪f, φ (x i)⟫_ℝ) '' {w' | IsCapped α w'}) -
    sSup ((fun v' : Fin m → ℝ => ∑ j, v' j * ⟪f, φ (y j)⟫_ℝ) '' {v' | IsCapped α v'})

/-- A Frank–Wolfe point of `eq:qp` with relative gap `ρ` (S3 :358-360): `w, v` are capped and, with `e = Σ w_i φ(x_i) − Σ v_j φ(y_j)`,
every capped `(w′, v′)` has `2⟨e, e⟩ − 2⟨e, e′⟩ ≤ ρ‖e‖²` (`e′` the difference at `(w′, v′)`): the Frank–Wolfe gap of `F = ‖e‖²` is at
most `ρ d²`, `d = ‖e‖`. An exact minimizer is an `IsFWPoint φ α 0` (T18 (c)). -/
def IsFWPoint (φ : 𝒳 → H) (α ρ : ℝ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) : Prop :=
  IsCapped α w ∧ IsCapped α v ∧
    ∀ (w' : Fin n → ℝ) (v' : Fin m → ℝ), IsCapped α w' → IsCapped α v' →
      2 * ⟪wsum φ x w - wsum φ y v, wsum φ x w - wsum φ y v⟫_ℝ -
          2 * ⟪wsum φ x w - wsum φ y v, wsum φ x w' - wsum φ y v'⟫_ℝ ≤
        ρ * ‖wsum φ x w - wsum φ y v‖ ^ 2

/-- The frozen `Wave30tz.IsWitnessRamp` with `IsQPMin φ α` replaced by `IsFWPoint φ α ρ` (T20, S3 :358-360); otherwise a verbatim
copy: an empty side gives no bet; otherwise, for some Frank–Wolfe point `(w, v)`, no bet if `D̂ = 0`, and if `D̂ > 0`, for some cut
points satisfying (C) for the own-term values, the rule bets iff `t > u`, and then `g` is the ramp of `f̂` between `u` and `t`.
Junk: `witness`, `ownX`, `ownY` divide by `D̂ = qpVal`, read only when `D̂ > 0`; `ramp` divides by `t − u`, read only when `u < t`. -/
def IsWitnessRampFW (φ : 𝒳 → H) (α ρ : ℝ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (has : Prop) (g : 𝒳 → ℝ) : Prop :=
  (n = 0 ∨ m = 0 → ¬ has) ∧
  (1 ≤ n → 1 ≤ m → ∃ w v, IsFWPoint φ α ρ x y w v ∧
    (qpVal φ x y w v = 0 → ¬ has) ∧
    (0 < qpVal φ x y w v → ∃ t u, CutsC α (ownX φ x y w v) (ownY φ x y w v) t u ∧ (has ↔ u < t) ∧
      (has → g = ramp (fun z => ⟪witness φ x y w v, φ z⟫_ℝ) t u)))

/-- The frozen `Wave30tz.LoRun.IsWitnessRun` with `IsWitnessRamp` replaced by `IsWitnessRampFW ρ` (T20); otherwise a verbatim copy
(admissible; per-level Frank–Wolfe witness ramps on the fitting sample of every batch that holds a pair; the fraction bounds of
`eq:fractions` with floor `s2 = v²_min`, `L = log(1/δ)`). Not in the `LoRun` namespace, so it is applied as
`IsWitnessRunFW R φ α δ lmax s2 ρ`. -/
def IsWitnessRunFW [MeasurableSpace 𝒳] {J n m : ℕ} (R : LoRun 𝒳 J n m) (φ : 𝒳 → H) (α : Fin J → ℝ) (δ lmax s2 ρ : ℝ) : Prop :=
  R.IsAdmissible α lmax ∧
  (∀ j (k : Fin R.N) x y, IsWitnessRampFW φ (α j) ρ (fitSample R.lx (R.bat k) x) (fitSample R.ly (R.bat k) y)
    (R.has j (R.bat k) x y) (R.g j (R.bat k) x y)) ∧
  ∀ j (k : Fin R.N) x y z,
    R.lam j k x y z ≤ lamHi lmax (α j) (Real.log (1 / δ)) s2 R.N ∧
    (R.has j (R.bat k) x y → (∀ l, z l ∈ Icc (-1 : ℝ) 1) →
      lamLo lmax (α j) (Real.log (1 / δ)) s2 R.N ≤ R.lam j k x y z) ∧
    (¬ R.has j (R.bat k) x y → R.lam j k x y z = 0)

end BlockR

section DraftE

/-- T45 (S4 :1531-1532): the law `Q_ν` on `ℝ` with Lebesgue density `(1 + ς(ν x))·1_{[0,1]}(x)`. For `|ς| = 1`, measurable, 1-periodic
and of mean zero on `[0,1]`, and `ν ≥ 1`, it is a probability measure carried by `[0,1]` with density in `{0, 2}` (T45 (a)); no junk
value arises (`ENNReal.ofReal` of a nonnegative density). For `ν = 0` it is not a law in general, and it is only used for `ν ≥ 1`
(or along `ν → ∞`). -/
def oscLaw (ς : ℝ → ℝ) (ν : ℕ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal ((Icc (0 : ℝ) 1).indicator (fun z => 1 + ς ((ν : ℝ) * z)) x)

end DraftE

section BlockM

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The witness at the uniform weights, `(n⁻¹Σφ(x_i) − m⁻¹Σφ(y_j))/D̂` (`0` when `D̂ = 0`): by T14 the `α = 0` witness `f̂_0` of the
sample when `n, m ≥ 1`. Junk when `n = 0` or `m = 0` (weights `1/0 = 0`); read there only as a measurable function. -/
def alphaZeroWit (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) : H :=
  StatFormal.Wave30tz.witness φ x y (fun _ => 1 / (n : ℝ)) (fun _ => 1 / (m : ℝ))

/-- `f̂_{0,b}(z) = ⟪f̂_0(fitting sample of batch b), φ z⟫`, the `α = 0` witness of the fitting sample of batch `b` as a function. -/
def alphaZeroFn (φ : 𝒳 → H) {n m : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ) (b : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : 𝒳) : ℝ :=
  ⟪alphaZeroWit φ (fitSample lx b x) (fitSample ly b y), φ z⟫_ℝ

open Classical in
/-- The gated fractions of the printed device (S3 :364-368): `λ′_k = λ_k · 1{KS⁺_{P,Q}(f̂_{0,bat k}) ≤ α}` for pairs `k < N`, `λ_k`
otherwise (never read). -/
def ksGate (P Q : Measure 𝒳) (φ : 𝒳 → H) {n m N : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (α : ℝ)
    (lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ) :
    (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ :=
  fun k x y z =>
    if hk : k < N then
      (if ksPlus P Q (alphaZeroFn φ lx ly (bat ⟨k, hk⟩) x y) ≤ α then lam k x y z else 0)
    else lam k x y z

/-- The 24 atoms of the example of S3 :369-377: `{−100, 0, ½, 300} ∪ {20 + 10i : 1 ≤ i ≤ 20}`. -/
def exAtoms : Finset ℝ :=
  {-100, 0, 1 / 2, 300} ∪ (Finset.Icc (1 : ℕ) 20).image (fun i : ℕ => 20 + 10 * (i : ℝ))

/-- `t_k = √(log(2/δ)/(2k))`, the one-sided Massart radius at level `δ/2` (T28 (b); used only at `k ≥ 1`). -/
def ksRadius (δ : ℝ) (k : ℕ) : ℝ := √(Real.log (2 / δ) / (2 * k))

/-- T46: the ramp of every batch (and level) is the one function `f̂ = F(batch 0)` (batch 0 = `fitSample · 1`). -/
def fnRamp {n m : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ)
    (F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ) :
    ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ :=
  fun _ x y => F (fitSample lx 1 x) (fitSample ly 1 y)

/-- T46: `Δ = E_P f̂ − E_Q f̂`, a function of batch 0 (Bochner integrals of a bounded measurable function in the claims). -/
def fnDrift (P Q : Measure 𝒳) {n m : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ)
    (F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) : ℝ :=
  (∫ z, F (fitSample lx 1 x) (fitSample ly 1 y) z ∂P) - ∫ z, F (fitSample lx 1 x) (fitSample ly 1 y) z ∂Q

/-- T46: `α̂` of the single-function certificate, `eq:downclosed` over the levels' rejections (`0` if `H_{0,α_1}` is not rejected). -/
def fnAlpha {n m N J : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n))
    (B : Fin N → Finset (Fin m)) (F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ)
    (lam : Fin J → (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ) (α : Fin J → ℝ) (δ : ℝ)
    (x : Fin n → 𝒳) (y : Fin m → 𝒳) : ℝ :=
  StatFormal.TrimmedMMD.Lower.alphaLo α fun j => rejects (lam j) (fnRamp lx ly F) bat A B (α j) δ x y

end BlockM



namespace Claims

/-- T1 (b), v5 (X2): the printed rules are genuine-quantile rules, and every genuine-quantile rule is a quantile rule (`eq:cutrank`,
S3 :241-247 "as do the empirical quantiles in the range of the values"). -/
def genuine_rules : Prop :=
  IsGenuineQuantileRule lowQ ∧ IsGenuineQuantileRule highQ ∧
    ∀ q : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ, IsGenuineQuantileRule q → IsQuantileRule q

/-- T1 (d), v5: at a level `α ∈ [0,1)` the printed ranks lie in `[1, k]`, the guards of `lowQ`/`highQ` are inactive, and these are the
smallest `(1−α)`-quantile and the largest `α`-quantile (§4 :61-64, Algorithm S1 line 10). -/
def printed_cuts : Prop :=
  ∀ (k : ℕ) (h : Fin k → ℝ) (α : ℝ), 1 ≤ k → 0 ≤ α → α < 1 →
    1 ≤ ⌈(k : ℝ) * (1 - α)⌉₊ ∧ ⌈(k : ℝ) * (1 - α)⌉₊ ≤ k ∧ ⌊(k : ℝ) * α⌋₊ + 1 ≤ k ∧
    lowQ k h (1 - α) = ordStat h ⌈(k : ℝ) * (1 - α)⌉₊ ∧ highQ k h α = ordStat h (⌊(k : ℝ) * α⌋₊ + 1) ∧
    IsLeast {q | IsEmpQuantile h (1 - α) q} (lowQ k h (1 - α)) ∧
    IsGreatest {q | IsEmpQuantile h α q} (highQ k h α)

/-- T4 (a), v5: the paper's run exists for every pair of cut rules, prior rule and boundaries. -/
def paperRun_exists : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (J n m : ℕ) (α : Fin J → ℝ) (δ lmax s2 w0 : ℝ)
    (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ),
    StronglyMeasurable φ → (∀ j, 0 ≤ α j ∧ α j < 1) → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 → 0 < s2 → 0 < w0 →
    IsBoundaries nb n cx → IsBoundaries nb m cy →
    IsPriorRule (fun i : Fin n => cutLabel nb cx i) (fun j : Fin m => cutLabel nb cy j) v0 →
      ∃ R : LoRun 𝒳 J n m, IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy

/-- T4 (b), v5: the printed instance (`nb = 2`, nearest-integer boundaries, `λ_max = ½`, `w₀ = 20`, the cut rules `lowQ`, `highQ`)
exists for all sizes (with `v₀ ≡ 1`; with Algorithm S1's prior by T48). -/
def paperRun_exists_printed : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 : ℝ),
    StronglyMeasurable φ → (∀ j, 0 ≤ α j ∧ α j < 1) → 0 < δ → δ < 1 → 0 < s2 →
      ∃ (R : LoRun 𝒳 J n m) (cx cy : ℕ → ℕ), NearestCuts n (cx 1) (cx 2) ∧ NearestCuts m (cy 1) (cy 2) ∧
        IsPaperRun R φ α δ (1 / 2) s2 20 (fun _ _ _ _ => 1) lowQ highQ 2 cx cy

/-! ### T7 / T12 — families of paper runs at fractions fixed in advance exist -/

/-- T7, T12 (S3 :99 "batch fractions fixed in advance", "at these fractions of its size"; §4 :146-157; §6 :106-113), the existence
conjunct: for `nb ≥ 1` fractions `IsFractions nb π`, grids `α n m` with levels in `[0,1)`, levels `δ n m ∈ (0,1)` (fixed `J, α, δ`
are the constant case), `λ_max ∈ (0,1]`, `v²_min > 0`, `w₀ > 0`, there is a family of paper runs, one for every `(n, m)`, with
boundaries within one of `π_b n`, `π_b m` (`BoundariesNear`), the printed cut rules `qt = lowQ`, `qu = highQ`, and the prior `v₀ ≡ 1`. -/
def paperRun_exists_fractions : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (J : ℕ → ℕ → ℕ) (α : ∀ n m : ℕ, Fin (J n m) → ℝ) (δ : ℕ → ℕ → ℝ) (lmax s2 w0 : ℝ) (nb : ℕ) (π : ℕ → ℝ),
    StronglyMeasurable φ → (∀ n m j, 0 ≤ α n m j ∧ α n m j < 1) → (∀ n m, 0 < δ n m ∧ δ n m < 1) →
    0 < lmax → lmax ≤ 1 → 0 < s2 → 0 < w0 → 1 ≤ nb → IsFractions nb π →
      ∃ (R : ∀ n m : ℕ, LoRun 𝒳 (J n m) n m) (cx cy : ℕ → ℕ → ℕ → ℕ), ∀ n m : ℕ,
        BoundariesNear nb π n (cx n m) ∧ BoundariesNear nb π m (cy n m) ∧
        IsPaperRun (R n m) φ (α n m) (δ n m) lmax s2 w0 (fun _ _ _ _ => 1) lowQ highQ nb (cx n m) (cy n m)

/-- T5, v5: a paper run with quantile rules `qt`, `qu` is admissible and a witness run; with the printed batches it is a default run;
at fractions fixed in advance (any rounding, `nb ≥ 1`) it is sized with `c = min_b (π_{b+1} − π_b)`, `C₀ = 2`, `B = nb`. -/
def paperRun_admissible : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ : ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ lmax s2 w0 : ℝ)
    (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ)
    (R : LoRun 𝒳 J n m),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsGrid α → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 → 0 < s2 → 0 < w0 →
    IsQuantileRule qt → IsQuantileRule qu → IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy →
      R.IsAdmissible α lmax ∧ R.IsWitnessRun φ α δ lmax s2 ∧
      (nb = 2 → NearestCuts n (cx 1) (cx 2) → NearestCuts m (cy 1) (cy 2) → IsDefaultRun R) ∧
      (∀ π : ℕ → ℝ, 1 ≤ nb → IsFractions nb π → BoundariesNear nb π n cx → BoundariesNear nb π m cy →
        R.IsSizedRun (⨅ b : Fin (nb + 1), (π (b + 1) - π b)) 2 nb)

/-- T6 (iii)–(iv), v5: Theorem 4.2 at every true null level and Corollary 4.3 for every paper run. Form of T6–T12 (non-vacuous at the printed rule): `genuine_rules ∧ paperRun_exists_printed ∧` the universal statement. -/
def paperRun_betting : Prop :=
  genuine_rules ∧ paperRun_exists_printed ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (J n m : ℕ) (α : Fin J → ℝ) (δ lmax s2 w0 : ℝ)
    (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ)
    (R : LoRun 𝒳 J n m),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsGrid α → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 → 0 < s2 → 0 < w0 →
    IsQuantileRule qt → IsQuantileRule qu → IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy →
      (∀ j, StatFormal.Distances.tvDist P Q ≤ α j →
        sampleLaw P Q n m {ω | rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2} ≤ ENNReal.ofReal δ) ∧
      sampleLaw P Q n m {ω | StatFormal.Distances.tvDist P Q < R.alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal δ

/-! ### T6 (i), (ii), (v) — Theorem 4.2 conditionally on batch 0, and Corollary 4.3's second sentence, for every paper run -/

/-- T6 (i), (ii), (v) (§4 :88-99 `thm:betting`, :122-135 `cor:lower`), v5: for every paper run (binders and hypotheses of
`paperRun_betting`, whose shape covers (iii)–(iv)): (i) at every level with `TV(P,Q) ≤ α_j`, for every value `(x₀, y₀)` of batch 0
(`withBatchZero`: batch 0 fixed, the other batches drawn from `P^{⊗n} ⊗ Q^{⊗m}`), `P(max_{k≤N} K_k ≥ 1/δ | batch 0) ≤ δ`; (ii) the
same as a conditional expectation, almost surely, in the certified `thm_betting_condexp` form at `U = Unit`, `ν = dirac ()` (the
rejection event is measurable and its conditional probability given `σ(batch 0)` is `≤ δ` a.s.); (v) for every pair, the event
"`H_{0,α̂}` is rejected (`α̂` is a grid level whose test rejected) and `TV(P,Q) ≤ α̂`" is measurable with probability `≤ δ`
(the certified `cor_lower_v2`, transported from `Unit × sample` to the sample space). Form of T6–T12 (non-vacuous at the printed rule): `genuine_rules ∧ paperRun_exists_printed ∧` the universal statement. -/
def paperRun_betting_cond : Prop :=
  genuine_rules ∧ paperRun_exists_printed ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (J n m : ℕ) (α : Fin J → ℝ) (δ lmax s2 w0 : ℝ)
    (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ)
    (R : LoRun 𝒳 J n m),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsGrid α → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 → 0 < s2 → 0 < w0 →
    IsQuantileRule qt → IsQuantileRule qu → IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy →
      (∀ j, StatFormal.Distances.tvDist P Q ≤ α j → ∀ (x₀ : Fin n → 𝒳) (y₀ : Fin m → 𝒳),
        sampleLaw P Q n m {ω | rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ
          (withBatchZero R.lx x₀ ω.1) (withBatchZero R.ly y₀ ω.2)} ≤ ENNReal.ofReal δ) ∧
      (∀ j, StatFormal.Distances.tvDist P Q ≤ α j →
        MeasurableSet {ω : Unit × ((Fin n → 𝒳) × (Fin m → 𝒳)) |
          rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.2.1 ω.2.2} ∧
        condExp (MeasurableSpace.comap (batchZero (𝒳 := 𝒳) (U := Unit) R.lx R.ly) inferInstance)
            ((Measure.dirac ()).prod (sampleLaw P Q n m))
            (Set.indicator {ω : Unit × ((Fin n → 𝒳) × (Fin m → 𝒳)) |
              rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.2.1 ω.2.2} fun _ => (1 : ℝ))
          ≤ᵐ[(Measure.dirac ()).prod (sampleLaw P Q n m)] fun _ => δ) ∧
      MeasurableSet {ω : (Fin n → 𝒳) × (Fin m → 𝒳) |
        (∃ j, R.alphaLo α δ ω.1 ω.2 = α j ∧ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2) ∧
          StatFormal.Distances.tvDist P Q ≤ R.alphaLo α δ ω.1 ω.2} ∧
      sampleLaw P Q n m {ω |
        (∃ j, R.alphaLo α δ ω.1 ω.2 = α j ∧ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2) ∧
          StatFormal.Distances.tvDist P Q ≤ R.alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal δ

/-- T47 (a) (Remark S5.5, last sentence; §6 :9-12): Laplace kernel on `ℝ`, `0 < α < α⋆ < 1`: the law of `d⋆(X)` has an atom of mass
at least `α` at its unique `(1−α)`-quantile, so (Q) fails there for every `r > 0`, `c`, `C`. -/
def laplace_qdens_fails : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (σ : ℝ) (φ : ℝ → H) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (α : ℝ) (a b : H),
    0 < σ → StronglyMeasurable φ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) → Characteristic φ →
    0 < α → α < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
    a ∈ region φ α P → b ∈ region φ α Q → ‖a - b‖ = Dpop φ P Q α →
      ∃ t : ℝ, α ≤ (P {x | ⟪a - b, φ x⟫_ℝ = t}).toReal ∧
        (∀ q, IsQuantileAt P (fun x => ⟪a - b, φ x⟫_ℝ) (1 - α) q ↔ q = t) ∧
        ∀ r c C : ℝ, 0 < r → ¬ StatFormal.Wave12c.QDensity P (fun x => ⟪a - b, φ x⟫_ℝ) t r c C

/-- T47 (b) (§6 :46-47): a law of finite support violates (Q) at every cut, for every witness. -/
def finite_support_not_qdens : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] (P : Measure 𝒳) [IsProbabilityMeasure P] (S : Finset 𝒳)
    (f : 𝒳 → ℝ) (t r c C : ℝ), Measurable f → P (↑S : Set 𝒳)ᶜ = 0 → 0 < r → 0 < c →
      ¬ StatFormal.Wave12c.QDensity P f t r c C

/-- T48 (c) (Algorithm S1; S3 :153-154 "Algorithm S1 gives ours"): on every paper run, Algorithm S1's initial variance is a prior rule
with values in `[10⁻⁴, ½]` on the batches bet on, and the run with that prior (same bets and ramps) is again a paper run. -/
def alg_prior : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ : ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ lmax s2 w0 : ℝ)
    (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ)
    (R : LoRun 𝒳 J n m),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsGrid α → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 → 0 < s2 → 0 < w0 →
    IsQuantileRule qt → IsQuantileRule qu → IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy →
      IsPriorRule R.lx R.ly (algPrior R) ∧
      (∀ j b x y, R.has j b x y → algPrior R j b x y ∈ Icc (1 / 10000 : ℝ) (1 / 2)) ∧
      ∃ R' : LoRun 𝒳 J n m, R'.has = R.has ∧ R'.g = R.g ∧
        IsPaperRun R' φ α δ lmax s2 w0 (algPrior R) qt qu nb cx cy

/-- T50 (b) (§7 :147-149, Table 2 caption, §8 :24-25): wealths at the horizon of admissible runs on the same data are e-values under
`H_{0,α_j}`; their average reaches `1/δ` with probability at most `δ` (Markov); the grid read upward on the averaged test is a
`δ`-level lower bound. -/
def averaged_evalue : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (S J n m : ℕ) (α : Fin J → ℝ) (δ lmax : ℝ) (R : Fin S → LoRun 𝒳 J n m),
    1 ≤ S → IsGrid α → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 → (∀ s, (R s).IsAdmissible α lmax) →
      (∀ j s, StatFormal.Distances.tvDist P Q ≤ α j →
        ∫⁻ ω, ENNReal.ofReal (hzWealth (R s) α j ω.1 ω.2) ∂(sampleLaw P Q n m) ≤ 1) ∧
      (∀ j, StatFormal.Distances.tvDist P Q ≤ α j →
        sampleLaw P Q n m {ω | 1 / δ ≤ (∑ s, hzWealth (R s) α j ω.1 ω.2) / S} ≤ ENNReal.ofReal δ) ∧
      sampleLaw P Q n m {ω | StatFormal.Distances.tvDist P Q <
        StatFormal.TrimmedMMD.Lower.alphaLo α (fun j => 1 / δ ≤ (∑ s, hzWealth (R s) α j ω.1 ω.2) / S)} ≤
          ENNReal.ofReal δ

/-- T50 (c)–(d) (§7 :151, :154; S6 :83-84; Table 2 caption): the larger of two `δ`-level lower bounds is a `2δ`-level bound, and the
bound read on an initial segment of a grid fixed in advance is at most the bound of the whole grid. -/
def bound_summaries : Prop :=
  (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (A B : Ω → ℝ) (a δ : ℝ),
      μ {ω | a < A ω} ≤ ENNReal.ofReal δ → μ {ω | a < B ω} ≤ ENNReal.ofReal δ →
        μ {ω | a < max (A ω) (B ω)} ≤ ENNReal.ofReal (2 * δ)) ∧
  ∀ (J J' : ℕ) (α : Fin J' → ℝ) (rej : Fin J' → Prop) (h : J ≤ J'), (∀ j, 0 ≤ α j) →
    StatFormal.TrimmedMMD.Lower.alphaLo (fun j : Fin J => α (Fin.castLE h j)) (fun j => rej (Fin.castLE h j)) ≤
      StatFormal.TrimmedMMD.Lower.alphaLo α rej

/-- T53 (S6 :191, :117): total variation can only shrink under a measurable map; and `ψ = 1{p > q}` has drift `α⋆`, the largest of
any `[0,1]`-valued function. -/
def tv_pushforward : Prop :=
  (∀ (𝒳 𝒴 : Type) [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (f : 𝒳 → 𝒴), Measurable f →
        StatFormal.Distances.tvDist (P.map f) (Q.map f) ≤ StatFormal.Distances.tvDist P Q) ∧
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : 𝒳 → ℝ),
    Measurable p → Measurable q → P = (P + Q).withDensity (fun x => ENNReal.ofReal (p x)) →
    Q = (P + Q).withDensity (fun x => ENNReal.ofReal (q x)) →
      (P {x | q x < p x}).toReal - (Q {x | q x < p x}).toReal = StatFormal.Distances.tvDist P Q ∧
      ∀ ψ : 𝒳 → ℝ, Measurable ψ → (∀ x, ψ x ∈ Icc (0 : ℝ) 1) →
        (∫ x, ψ x ∂P) - ∫ x, ψ x ∂Q ≤ StatFormal.Distances.tvDist P Q

/-- T54 (main :351-354): a known polynomial margin gives an upper end: `α⋆ ≤ α + (Ď/c₀)^{1/γ}` for every `Ď ≥ D_α(P,Q)`. -/
def upper_end : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) (P Q : Measure 𝒳)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (c₀ γ α Dc : ℝ),
    StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ → 0 ≤ α → α < 1 → Dpop φ P Q α ≤ Dc →
      StatFormal.Distances.tvDist P Q ≤ α + (Dc / c₀) ^ (1 / γ)

/-- T55 (main :28-29): the margin on `(0, ε₀]` suffices, with `c₀(ε₀/α⋆)^γ` in place of `c₀`. -/
def margin_eps0 : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : 𝒳 → H) (κ : ℝ)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (c₀ γ ε₀ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < c₀ → 1 ≤ γ → 0 < ε₀ → ε₀ ≤ StatFormal.Distances.tvDist P Q →
    (∀ ε ∈ Icc (0 : ℝ) ε₀, c₀ * ε ^ γ ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε)) →
      StatFormal.Wave31ti.PolyMargin φ P Q (c₀ * (ε₀ / StatFormal.Distances.tvDist P Q) ^ γ) γ

/-- T8 (lorate_O, Theorem 5.7): the certified claim with `IsWitnessRun` replaced by the paper run (v5 cut rules `qt`, `qu`). Form of T6–T12 (non-vacuous at the printed rule): `genuine_rules ∧ paperRun_exists_printed ∧` the universal statement. -/
def paper_lorate_O : Prop :=
  genuine_rules ∧ paperRun_exists_printed ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (c₀ γ : ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h : ℝ) (R : LoRun 𝒳 J n m) (w0 : ℝ) (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ → StatFormal.Distances.tvDist P Q < 1 →
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < w0 → IsQuantileRule qt → IsQuantileRule qu → IsPaperRun R φ α δ (1 / 2) s2 w0 v0 qt qu nb cx cy → (nb = 2 ∧ NearestCuts n (cx 1) (cx 2) ∧ NearestCuts m (cy 1) (cy 2)) →
    1 ≤ n → 1 ≤ m → 0 < η → η < 1 → MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
        E ⊆ {ω | StatFormal.Distances.tvDist P Q - h -
              (1000 * κ / (c₀ * (1 - StatFormal.Distances.tvDist P Q) * s2) *
                √((1 + Real.log (1 / δ) + Real.log (J / η)) / ((min n m : ℕ) : ℝ))) ^ (1 / γ) ≤
                R.alphaLo α δ ω.1 ω.2 ∧
            R.alphaLo α δ ω.1 ω.2 ≤ StatFormal.Distances.tvDist P Q}

/-- T8 (same_rate, main :146-147): the certified claim with `IsWitnessRun` replaced by the paper run (v5 cut rules `qt`, `qu`). Form of T6–T12 (non-vacuous at the printed rule): `genuine_rules ∧ paperRun_exists_printed ∧` the universal statement. -/
def paper_same_rate : Prop :=
  genuine_rules ∧ paperRun_exists_printed ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (c₀ γ : ℝ) (J : ℕ) (δ s2 η : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ → StatFormal.Distances.tvDist P Q < 1 →
    1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < η → η < 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (n m : ℕ) (α : Fin J → ℝ) (R : LoRun 𝒳 J n m) (w0 : ℝ) (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ) (h : ℝ),
        IsGrid α → 0 < w0 → IsQuantileRule qt → IsQuantileRule qu → IsPaperRun R φ α δ (1 / 2) s2 w0 v0 qt qu nb cx cy → (nb = 2 ∧ NearestCuts n (cx 1) (cx 2) ∧ NearestCuts m (cy 1) (cy 2)) → 1 ≤ n → 1 ≤ m →
        MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
          ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
            ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
            E ⊆ {ω | StatFormal.Distances.tvDist P Q - h - C * ((min n m : ℕ) : ℝ) ^ (-(1 / (2 * γ))) ≤
                    R.alphaLo α δ ω.1 ω.2 ∧
                R.alphaLo α δ ω.1 ω.2 ≤ StatFormal.Distances.tvDist P Q}

/-- T9 (lorate_i): the certified claim with `IsWitnessRun` replaced by the paper run (v5 cut rules `qt`, `qu`). Form of T6–T12 (non-vacuous at the printed rule): `genuine_rules ∧ paperRun_exists_printed ∧` the universal statement. -/
def paper_lorate_i : Prop :=
  genuine_rules ∧ paperRun_exists_printed ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (c₀ γ : ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h0 ε : ℝ) (R : LoRun 𝒳 J n m) (w0 : ℝ) (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ) (B : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ →
    StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ → StatFormal.Distances.tvDist P Q < 1 →
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < w0 → IsQuantileRule qt → IsQuantileRule qu → IsPaperRun R φ α δ (1 / 2) s2 w0 v0 qt qu nb cx cy →
    (∀ k, R.bat k ≤ B) → 1 ≤ fitCard R.lx 1 → 1 ≤ fitCard R.ly 1 → rOne R.lx R.ly ≤ 1 → 1 ≤ R.N →
    0 < η → η < 1 → 0 < h0 → GapsGe α h0 → 0 < ε → ε ≤ StatFormal.Distances.tvDist P Q →
    beta (StatFormal.Distances.tvDist P Q) * max (Tfit κ Dφ η (rOne R.lx R.ly) B)
        (Tbet Dφ s2 (Real.log (1 / δ)) η (Jeps J ε h0) R.N) ≤ c₀ * ε ^ γ →
      sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < gridFloor α (StatFormal.Distances.tvDist P Q - ε)} ≤
        ENNReal.ofReal η

/-- T9 (lorate_ii): the certified claim with `IsWitnessRun` replaced by the paper run (v5 cut rules `qt`, `qu`). Form of T6–T12 (non-vacuous at the printed rule): `genuine_rules ∧ paperRun_exists_printed ∧` the universal statement. -/
def paper_lorate_ii : Prop :=
  genuine_rules ∧ paperRun_exists_printed ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (c₀ γ : ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h : ℝ) (R : LoRun 𝒳 J n m) (w0 : ℝ) (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ) (B : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ →
    StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ → StatFormal.Distances.tvDist P Q < 1 →
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < w0 → IsQuantileRule qt → IsQuantileRule qu → IsPaperRun R φ α δ (1 / 2) s2 w0 v0 qt qu nb cx cy →
    (∀ k, R.bat k ≤ B) → 1 ≤ fitCard R.lx 1 → 1 ≤ fitCard R.ly 1 → rOne R.lx R.ly ≤ 1 → 1 ≤ R.N →
    0 < η → η < 1 → MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
        E ⊆ {ω | StatFormal.Distances.tvDist P Q - h -
              (tNM κ Dφ (StatFormal.Distances.tvDist P Q) s2 δ η (rOne R.lx R.ly) B J R.N / c₀) ^ (1 / γ) ≤
                R.alphaLo α δ ω.1 ω.2 ∧
            R.alphaLo α δ ω.1 ω.2 ≤ StatFormal.Distances.tvDist P Q}

/-- T9 (lorate_nologJ): the certified claim with `IsWitnessRun` replaced by the paper run (v5 cut rules `qt`, `qu`). Form of T6–T12 (non-vacuous at the printed rule): `genuine_rules ∧ paperRun_exists_printed ∧` the universal statement. -/
def paper_lorate_nologJ : Prop :=
  genuine_rules ∧ paperRun_exists_printed ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (c₀ γ : ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h0 h : ℝ) (R : LoRun 𝒳 J n m) (w0 : ℝ) (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ) (B : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ →
    StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ → StatFormal.Distances.tvDist P Q < 1 →
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < w0 → IsQuantileRule qt → IsQuantileRule qu → IsPaperRun R φ α δ (1 / 2) s2 w0 v0 qt qu nb cx cy →
    (∀ k, R.bat k ≤ B) → 1 ≤ fitCard R.lx 1 → 1 ≤ fitCard R.ly 1 → rOne R.lx R.ly ≤ 1 → 1 ≤ R.N →
    0 < η → η < 1 → 0 < h0 → GapsGe α h0 → MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
    (beta (StatFormal.Distances.tvDist P Q) * max (Tfit κ Dφ η (rOne R.lx R.ly) B)
        (Tbet Dφ s2 (Real.log (1 / δ)) η 4 R.N) / c₀) ^ (1 / γ) ≤ h0 →
      Jeps J ((beta (StatFormal.Distances.tvDist P Q) * max (Tfit κ Dφ η (rOne R.lx R.ly) B)
        (Tbet Dφ s2 (Real.log (1 / δ)) η 4 R.N) / c₀) ^ (1 / γ)) h0 ≤ 4 ∧
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
        E ⊆ {ω | StatFormal.Distances.tvDist P Q - h -
              (beta (StatFormal.Distances.tvDist P Q) * max (Tfit κ Dφ η (rOne R.lx R.ly) B)
                (Tbet Dφ s2 (Real.log (1 / δ)) η 4 R.N) / c₀) ^ (1 / γ) ≤ R.alphaLo α δ ω.1 ω.2 ∧
            R.alphaLo α δ ω.1 ω.2 ≤ StatFormal.Distances.tvDist P Q}

/-- T9 (lorate_general): the certified claim with `IsWitnessRun` replaced by the paper run (v5 cut rules `qt`, `qu`). Form of T6–T12 (non-vacuous at the printed rule): `genuine_rules ∧ paperRun_exists_printed ∧` the universal statement. -/
def paper_lorate_general : Prop :=
  genuine_rules ∧ paperRun_exists_printed ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (ω : ℝ → ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h e : ℝ) (R : LoRun 𝒳 J n m) (w0 : ℝ) (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ) (B : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ →
    StatFormal.Wave30tu.Margin φ P Q ω → StatFormal.Distances.tvDist P Q < 1 →
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < w0 → IsQuantileRule qt → IsQuantileRule qu → IsPaperRun R φ α δ (1 / 2) s2 w0 v0 qt qu nb cx cy →
    (∀ k, R.bat k ≤ B) → 1 ≤ fitCard R.lx 1 → 1 ≤ fitCard R.ly 1 → rOne R.lx R.ly ≤ 1 → 1 ≤ R.N →
    0 < η → η < 1 → MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
    e ∈ Icc 0 (StatFormal.Distances.tvDist P Q) →
    ω e = tNM κ Dφ (StatFormal.Distances.tvDist P Q) s2 δ η (rOne R.lx R.ly) B J R.N →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
        E ⊆ {z | StatFormal.Distances.tvDist P Q - h - e ≤ R.alphaLo α δ z.1 z.2 ∧
            R.alphaLo α δ z.1 z.2 ≤ StatFormal.Distances.tvDist P Q}

/-- T10 (Prop S4.8(i): newrates_ii_a): the certified claim with `IsWitnessRun` replaced by the paper run (v5 cut rules `qt`, `qu`). Form of T6–T12 (non-vacuous at the printed rule): `genuine_rules ∧ paperRun_exists_printed ∧` the universal statement. -/
def paper_newrates_i_a : Prop :=
  genuine_rules ∧ paperRun_exists_printed ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (ω : ℝ → ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h0 ε : ℝ) (R : LoRun 𝒳 J n m) (w0 : ℝ) (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ) (B : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ → 0 < κ →
    MonotoneOn ω (Icc 0 (StatFormal.Distances.tvDist P Q)) →
    (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q), 0 ≤ ω e) →
    (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
      ω e ≤ StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - e)) →
    StatFormal.Distances.tvDist P Q < 1 →
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < w0 → IsQuantileRule qt → IsQuantileRule qu → IsPaperRun R φ α δ (1 / 2) s2 w0 v0 qt qu nb cx cy →
    (∀ k, R.bat k ≤ B) → 1 ≤ fitCard R.lx 1 → 1 ≤ fitCard R.ly 1 → rOne R.lx R.ly ≤ 1 → 1 ≤ R.N →
    0 < η → η < 1 → 0 < h0 → GapsGe α h0 → 0 < ε → ε ≤ StatFormal.Distances.tvDist P Q →
    beta (StatFormal.Distances.tvDist P Q) * max (Tfit κ Dφ η (rOne R.lx R.ly) B)
        (Tbet Dφ s2 (Real.log (1 / δ)) η (Jeps J ε h0) R.N) ≤ ω ε →
      sampleLaw P Q n m {z | R.alphaLo α δ z.1 z.2 < gridFloor α (StatFormal.Distances.tvDist P Q - ε)} ≤
        ENNReal.ofReal η

/-- T10 (Prop S4.8(i): newrates_ii_b): the certified claim with `IsWitnessRun` replaced by the paper run (v5 cut rules `qt`, `qu`). Form of T6–T12 (non-vacuous at the printed rule): `genuine_rules ∧ paperRun_exists_printed ∧` the universal statement. -/
def paper_newrates_i_b : Prop :=
  genuine_rules ∧ paperRun_exists_printed ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (ω : ℝ → ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h : ℝ) (R : LoRun 𝒳 J n m) (w0 : ℝ) (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ) (B : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ →
    MonotoneOn ω (Icc 0 (StatFormal.Distances.tvDist P Q)) →
    (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q), 0 ≤ ω e) →
    (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
      ω e ≤ StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - e)) →
    StatFormal.Distances.tvDist P Q < 1 →
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → 0 < w0 → IsQuantileRule qt → IsQuantileRule qu → IsPaperRun R φ α δ (1 / 2) s2 w0 v0 qt qu nb cx cy →
    (∀ k, R.bat k ≤ B) → 1 ≤ fitCard R.lx 1 → 1 ≤ fitCard R.ly 1 → rOne R.lx R.ly ≤ 1 → 1 ≤ R.N →
    0 < η → η < 1 → MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
        E ⊆ {z | StatFormal.Distances.tvDist P Q - h -
              genInv ω (StatFormal.Distances.tvDist P Q)
                (tNM κ Dφ (StatFormal.Distances.tvDist P Q) s2 δ η (rOne R.lx R.ly) B J R.N) ≤
                R.alphaLo α δ z.1 z.2 ∧
            R.alphaLo α δ z.1 z.2 ≤ StatFormal.Distances.tvDist P Q}

/-- T11 (Cor 5.9(ii): minimax_iii): the certified claim with `IsWitnessRun` replaced by the paper run (v5 cut rules `qt`, `qu`). Form of T6–T12 (non-vacuous at the printed rule): `genuine_rules ∧ paperRun_exists_printed ∧` the universal statement. -/
def paper_minimax_ii : Prop :=
  genuine_rules ∧ paperRun_exists_printed ∧
  ∀ (κ Dφ a₁ c₀ s2 δ η : ℝ), 0 < a₁ → a₁ < 1 → 0 < c₀ → 0 < s2 → s2 ≤ 4 → 0 < δ → δ < 1 → 0 < η → η < 1 →
    ∃ C N₁ : ℝ, ∀ (a₀ : ℝ) (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (n m : ℕ) (P Q : Measure 𝒳)
      (R : LoRun 𝒳 (rootLevels (min n m)) n m) (w0 : ℝ) (v0 : Fin (rootLevels (min n m)) → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ →
      0 < a₀ → a₀ < a₁ → max N₁ 10 ≤ ((min n m : ℕ) : ℝ) → InM φ a₀ a₁ c₀ P Q →
      0 < w0 → IsQuantileRule qt → IsQuantileRule qu → IsPaperRun R φ (rootGrid (min n m)) δ (1 / 2) s2 w0 v0 qt qu nb cx cy → (nb = 2 ∧ NearestCuts n (cx 1) (cx 2) ∧ NearestCuts m (cy 1) (cy 2)) →
        sampleLaw P Q n m {ω | StatFormal.Distances.tvDist P Q < R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2} ≤
          ENNReal.ofReal δ ∧
        sampleLaw P Q n m {ω | C / √((min n m : ℕ) : ℝ) <
            StatFormal.Distances.tvDist P Q - R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2} ≤ ENNReal.ofReal η

/-- T7 (lo_consistency): the certified claim with `IsWitnessRun` replaced by the paper run (v5 cut rules `qt`, `qu`). Form of T6–T12 (non-vacuous at the printed rule): `genuine_rules ∧ paperRun_exists_fractions ∧` the universal statement. -/
def paper_lo_consistency : Prop :=
  genuine_rules ∧ paperRun_exists_fractions ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (J : ℕ) (α : Fin J → ℝ) (δ lmax s2 : ℝ) (R : ∀ n m : ℕ, LoRun 𝒳 J n m) (w0 : ℝ) (v0 : ∀ n m : ℕ, Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : ℕ → ℕ → (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (π : ℕ → ℝ) (cx cy : ℕ → ℕ → ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Characteristic φ → IsGrid α →
    0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 / 2 → 0 < s2 →
    0 < w0 → 1 ≤ nb → IsFractions nb π → (∀ n m, IsQuantileRule (qt n m) ∧ IsQuantileRule (qu n m) ∧ IsPaperRun (R n m) φ α δ lmax s2 w0 (v0 n m) (qt n m) (qu n m) nb (cx n m) (cy n m) ∧ BoundariesNear nb π n (cx n m) ∧ BoundariesNear nb π m (cy n m)) →
      (∀ n m, sampleLaw P Q n m
          {ω | gridBelow α (StatFormal.Distances.tvDist P Q) < (R n m).alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal δ) ∧
      (∀ ε > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → sampleLaw P Q n m
          {ω | (R n m).alphaLo α δ ω.1 ω.2 < gridBelow α (StatFormal.Distances.tvDist P Q)} ≤ ENNReal.ofReal ε) ∧
      ((∀ j, α j ≠ StatFormal.Distances.tvDist P Q) → ∀ ε > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → sampleLaw P Q n m
          {ω | gridBelow α (StatFormal.Distances.tvDist P Q) < (R n m).alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal ε)

/-- T7 (lo_refining): the certified claim with `IsWitnessRun` replaced by the paper run (v5 cut rules `qt`, `qu`). Form of T6–T12 (non-vacuous at the printed rule): `genuine_rules ∧ paperRun_exists_fractions ∧` the universal statement. -/
def paper_lo_refining : Prop :=
  genuine_rules ∧ paperRun_exists_fractions ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (J : ℕ → ℕ → ℕ) (α : ∀ n m, Fin (J n m) → ℝ) (δ : ℕ → ℕ → ℝ) (δbar lmax s2 : ℝ)
    (R : ∀ n m : ℕ, LoRun 𝒳 (J n m) n m) (w0 : ℝ) (v0 : ∀ n m : ℕ, Fin (J n m) → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : ℕ → ℕ → (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (π : ℕ → ℝ) (cx cy : ℕ → ℕ → ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Characteristic φ →
    (∀ n m, IsGrid (α n m)) →
    (∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → gridMesh (α n m) ≤ η ∧ Real.log (J n m) ≤ η * (min n m : ℕ)) →
    (∀ n m, 0 < δ n m ∧ δ n m < 1) → δbar < 1 →
    (∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → δ n m ≤ δbar ∧ Real.log (1 / δ n m) ≤ η * (min n m : ℕ)) →
    0 < lmax → lmax ≤ 1 / 2 → 0 < s2 →
    0 < w0 → 1 ≤ nb → IsFractions nb π → (∀ n m, IsQuantileRule (qt n m) ∧ IsQuantileRule (qu n m) ∧ IsPaperRun (R n m) φ (α n m) (δ n m) lmax s2 w0 (v0 n m) (qt n m) (qu n m) nb (cx n m) (cy n m) ∧ BoundariesNear nb π n (cx n m) ∧ BoundariesNear nb π m (cy n m)) →
      ∀ ε > 0, ∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m →
        sampleLaw P Q n m {ω | ε < |(R n m).alphaLo (α n m) (δ n m) ω.1 ω.2 - StatFormal.Distances.tvDist P Q|} ≤
          ENNReal.ofReal η

/-- T12 (Cor 6.3: alphalo): the certified claim with `IsWitnessRun` replaced by the paper run (v5 cut rules `qt`, `qu`). Form of T6–T12 (non-vacuous at the printed rule): `genuine_rules ∧ paperRun_exists_fractions ∧` the universal statement. -/
def paper_alphalo : Prop :=
  genuine_rules ∧ paperRun_exists_fractions ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (J : ℕ → ℕ → ℕ) (α : ∀ n m, Fin (J n m) → ℝ) (δ lmax s2 : ℝ)
    (R : ∀ n m : ℕ, LoRun 𝒳 (J n m) n m) (w0 : ℝ) (v0 : ∀ n m : ℕ, Fin (J n m) → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : ℕ → ℕ → (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (π : ℕ → ℝ) (cx cy : ℕ → ℕ → ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
    (∀ n m, IsGrid (α n m)) →
    (∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → gridMesh (α n m) ≤ η ∧ Real.log (J n m) ≤ η * (min n m : ℕ)) →
    0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 / 2 → 0 < s2 →
    0 < w0 → 1 ≤ nb → IsFractions nb π → (∀ n m, IsQuantileRule (qt n m) ∧ IsQuantileRule (qu n m) ∧ IsPaperRun (R n m) φ (α n m) δ lmax s2 w0 (v0 n m) (qt n m) (qu n m) nb (cx n m) (cy n m) ∧ BoundariesNear nb π n (cx n m) ∧ BoundariesNear nb π m (cy n m)) →
      ∀ ε > 0, ∀ δ' : ℝ, 0 < δ' → δ' < 1 → ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m →
        ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ - δ') ≤ sampleLaw P Q n m E ∧
          ∀ z ∈ E, ∀ pr ∈ capped n ((R n m).alphaLo (α n m) δ z.1 z.2) ×ˢ capped m ((R n m).alphaLo (α n m) δ z.1 z.2),
            IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j)))
              (capped n ((R n m).alphaLo (α n m) δ z.1 z.2) ×ˢ capped m ((R n m).alphaLo (α n m) δ z.1 z.2)) pr →
              ‖∫ x, φ x ∂(StatFormal.Wave30tx.wEmp pr.1 z.1) - ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖ ≤ ε ∧
              ‖∫ x, φ x ∂(StatFormal.Wave30tx.wEmp pr.2 z.2) - ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q)‖ ≤ ε

/-- T34 (c) (S1 :25-26, §2 :40): laws that lose fractions `α₁`, `α₂` and agree on what remains have `α₁ ∨ α₂ ≥ α⋆`. -/
def different_fractions : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q R : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R] (α₁ α₂ : ℝ), 0 ≤ α₁ → α₁ < 1 → 0 ≤ α₂ → α₂ < 1 →
    ENNReal.ofReal (1 - α₁) • R ≤ P → ENNReal.ofReal (1 - α₂) • R ≤ Q →
      StatFormal.Distances.tvDist P Q ≤ max α₁ α₂

/-- T51 (§6 :102-103): the bound of Proposition 6.2 at any valid lower bound `α̃` (measurable, `P(α̃ > α⋆) ≤ δ`): on
`E ∩ {α̃ ≤ α⋆}`, of probability at least `1 − δ − 2δ'`. -/
def trimming_at_lower : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ δ' : ℝ) (n m : ℕ) (αt : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
    0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m → Measurable αt → (∀ z, 0 ≤ αt z) →
    sampleLaw P Q n m {z | StatFormal.Distances.tvDist P Q < αt z} ≤ ENNReal.ofReal δ →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - 2 * δ') ≤ sampleLaw P Q n m (E ∩ {z | αt z ≤ StatFormal.Distances.tvDist P Q}) ∧
        ∀ z ∈ E, αt z ≤ StatFormal.Distances.tvDist P Q → ∀ pr ∈ capped n (αt z) ×ˢ capped m (αt z),
          IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n (αt z) ×ˢ capped m (αt z)) pr →
            ‖∫ x, φ x ∂(wEmp pr.1 z.1) - ∫ x, φ x ∂(contactLaw P Q)‖ ≤
                rn κ (StatFormal.Distances.tvDist P Q) δ' n + omegaC φ P Q (Demp φ z.1 z.2 (αt z) +
                  rn κ (StatFormal.Distances.tvDist P Q) δ' n + rn κ (StatFormal.Distances.tvDist P Q) δ' m) ∧
              ‖∫ x, φ x ∂(wEmp pr.2 z.2) - ∫ x, φ x ∂(contactLaw P Q)‖ ≤
                rn κ (StatFormal.Distances.tvDist P Q) δ' m + omegaC φ Q P (Demp φ z.1 z.2 (αt z) +
                  rn κ (StatFormal.Distances.tvDist P Q) δ' n + rn κ (StatFormal.Distances.tvDist P Q) δ' m)

/-- T52 (§7 :170-175): with the pooled density `ρ = πp + (1−π)q` and the propensity score `e = πp/ρ`,
`min(p,q) = ρ min{e/π, (1−e)/(1−π)}` where `ρ > 0`, and `α⋆` is the total variation between the laws of `e(X)` in the two arms. -/
def propensity_core : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : 𝒳 → ℝ) (π : ℝ),
    Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) → 0 < π → π < 1 →
    P = (P + Q).withDensity (fun x => ENNReal.ofReal (p x)) → Q = (P + Q).withDensity (fun x => ENNReal.ofReal (q x)) →
      (∀ x, 0 < π * p x + (1 - π) * q x → min (p x) (q x) = (π * p x + (1 - π) * q x) *
          min ((π * p x / (π * p x + (1 - π) * q x)) / π) ((1 - π * p x / (π * p x + (1 - π) * q x)) / (1 - π))) ∧
      StatFormal.Distances.tvDist (P.map fun x => if π * p x + (1 - π) * q x = 0 then 0 else π * p x / (π * p x + (1 - π) * q x))
          (Q.map fun x => if π * p x + (1 - π) * q x = 0 then 0 else π * p x / (π * p x + (1 - π) * q x)) =
        StatFormal.Distances.tvDist P Q

/-- T56 (a) (§3 :49-50): `τ^P` jumps up at `0+`. -/
def taup_jump : Prop :=
  ∀ (D v ρbar δ : ℝ) (n m : ℕ), 0 < D → 0 ≤ v → 0 ≤ ρbar → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    ∃ c, StatFormal.Wave30tp.tauP D v ρbar 0 δ n m < c ∧
      ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), c ≤ StatFormal.Wave30tp.tauP D v ρbar α δ n m

/-- T56 (c) (§3 :92-93): `α̂_an` at `τ = τ^P` is well defined: the crossing set is nonempty for every sample when `D > 0`. -/
def taup_welldefined : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 0 < D → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        (crossSet (Demp φ x y) (fun α => StatFormal.Wave30tp.tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m)).Nonempty

/-- T56 (d) (§3 :93-97): at `τ = τ^P`, on one event of probability at least `1 − δ`, `α̂_an ≤ α⋆`, every rejected level lies below
`α⋆`, and every grid read upward gives a bound at most `α⋆`. -/
def taup_valid_bound : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m E ∧
        ∀ z ∈ E,
          alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tp.tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m) ≤
              StatFormal.Distances.tvDist P Q ∧
            (∀ α ∈ Ico (0 : ℝ) 1, StatFormal.Wave30tp.tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m < Demp φ z.1 z.2 α →
              α < StatFormal.Distances.tvDist P Q) ∧
            ∀ (J : ℕ) (α : Fin J → ℝ), IsGrid α →
              StatFormal.TrimmedMMD.Lower.alphaLo α (fun j =>
                StatFormal.Wave30tp.tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D (α j) δ n m < Demp φ z.1 z.2 (α j)) ≤
                  StatFormal.Distances.tvDist P Q

/-- T56 (e) (§3 :97-100): at `τ = τ^P`, under (A1)–(A3), `P(α̂_an < α) → 0` for every `α < α⋆`. -/
def taup_consistent_below : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → D ≤ 2 * κ → Characteristic φ →
    StatFormal.Distances.tvDist P Q < 1 → 0 < δ → δ < 1 →
      ∀ α ∈ Ico (0 : ℝ) (StatFormal.Distances.tvDist P Q), ∀ ε > 0, ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m →
        sampleLaw P Q n m {z | alphaHat (Demp φ z.1 z.2)
          (fun a => StatFormal.Wave30tp.tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D a δ n m) < α} ≤ ENNReal.ofReal ε

/-- T57 (§1 :106-107): the Bayes risk with equal priors is `(1 − TV)/2`, so `(1 − α̃)/2` is an upper confidence bound on it. -/
def bayes_risk : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    (⨅ A : {A : Set 𝒳 // MeasurableSet A}, ((P (A.1)ᶜ).toReal + (Q A.1).toReal) / 2) =
        (1 - StatFormal.Distances.tvDist P Q) / 2 ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (αt : Ω → ℝ) (δ : ℝ),
        μ {ω | StatFormal.Distances.tvDist P Q < αt ω} ≤ ENNReal.ofReal δ →
          μ {ω | (1 - αt ω) / 2 < ⨅ A : {A : Set 𝒳 // MeasurableSet A}, ((P (A.1)ᶜ).toReal + (Q A.1).toReal) / 2} ≤
            ENNReal.ofReal δ

/-- T49 (a) (§4 :170-173, S3 :199-200, §7 :126-127), v5.1, kernel level: the run as computed is admissible, so Theorem 4.2 and Corollary
4.3 hold for it. No positive definiteness, no bound on the kernel, no feature map. -/
def kernel_run_valid : Prop :=
  ∀ (𝒳 Θ : Type) [MeasurableSpace 𝒳] [MeasurableSpace Θ] (J n m : ℕ) (kf : Θ → 𝒳 → 𝒳 → ℝ)
    (θh : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → Θ) (α : Fin J → ℝ) (δ lmax s2 w0 : ℝ)
    (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (nb : ℕ) (cx cy : ℕ → ℕ)
    (R : LoRun 𝒳 J n m),
    Measurable (fun p : Θ × 𝒳 × 𝒳 => kf p.1 p.2.1 p.2.2) → IsGrid α → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 →
    0 < s2 → 0 < w0 → IsQuantileRule qt → IsQuantileRule qu → IsKernelRun R kf θh α δ lmax s2 w0 v0 qt qu nb cx cy →
      R.IsAdmissible α lmax ∧
      ∀ (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
        (∀ j, StatFormal.Distances.tvDist P Q ≤ α j →
          sampleLaw P Q n m {ω | rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2} ≤ ENNReal.ofReal δ) ∧
        sampleLaw P Q n m {ω | StatFormal.Distances.tvDist P Q < R.alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal δ

/-- T49 (b) (i), v5.1: the median heuristic is a measurable, positive function of the points it is computed on. -/
def median_bandwidth : Prop :=
  ∀ (E : Type) [MeasurableSpace E] (ρ : E → E → ℝ) (k : ℕ), Measurable (fun p : E × E => ρ p.1 p.2) →
    (∀ a b, 0 ≤ ρ a b) → (∀ a b, ρ a b = ρ b a) → (∀ a, ρ a a = 0) →
      Measurable (fun z : Fin k → E => medianBw ρ z) ∧ ∀ z : Fin k → E, 0 < medianBw ρ z

/-- T49 (b) (ii)–(iii), v5.1: the Laplace and Gaussian profiles with bandwidth and scales are jointly measurable in `(θ, x, y)` and
take values in `[0,1]`; the scaled distance is measurable; the batch-0 scales are measurable and positive. -/
def kernel_profiles : Prop :=
  ∀ d : ℕ,
    Measurable (fun p : (ℝ × (Fin d → ℝ)) × (Fin d → ℝ) × (Fin d → ℝ) => lapK p.1 p.2.1 p.2.2) ∧
    Measurable (fun p : (ℝ × (Fin d → ℝ)) × (Fin d → ℝ) × (Fin d → ℝ) => gaussK p.1 p.2.1 p.2.2) ∧
    (∀ (θ : ℝ × (Fin d → ℝ)) (x y : Fin d → ℝ), 0 ≤ lapK θ x y ∧ lapK θ x y ≤ 1) ∧
    (∀ (θ : ℝ × (Fin d → ℝ)) (x y : Fin d → ℝ), 0 ≤ gaussK θ x y ∧ gaussK θ x y ≤ 1) ∧
    (∀ s : Fin d → ℝ, Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => scaledDist s p.1 p.2)) ∧
    (∀ s : Fin d → ℝ, ∀ a b, 0 ≤ scaledDist s a b ∧ scaledDist s a b = scaledDist s b a ∧ scaledDist s a a = 0) ∧
    ∀ k : ℕ, Measurable (fun z : Fin k → Fin d → ℝ => b0Scale z) ∧ ∀ (z : Fin k → Fin d → ℝ) i, 0 < b0Scale z i

/-- T47 (b), existence (v5.1): the margin does not imply (Q). A finitely supported pair of Example 5.2 on three points (basis feature
map) satisfies Assumption 5.1 with `γ = 1`, and (Q) fails for it at every cut and for every witness. -/
def margin_without_qdens : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧
    StatFormal.Wave31ti.PolyMargin (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ))
      ((1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1)
      ((1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 2) c₀ 1 ∧
    ∀ (f : Fin 3 → ℝ) (t r c C : ℝ), 0 < r → 0 < c →
      ¬ StatFormal.Wave12c.QDensity ((1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1) f t r c C

/-! ### T1 — quantile rules and order statistics -/

/-- T1 (a) (S3 :241-247, "and their linear interpolations"; S6 :36, :86): numpy's linearly interpolated quantile `npQuantile` is a
quantile rule: measurable in the values for every `k, p`, and for `k ≥ 1`, `p ∈ [0,1]` within one rank of the quantile
(`[h_(ι⁻(k,p)), h_(ι⁺(k,p))]`, `eq:cutrank`). -/
def npQuantile_rule : Prop :=
  IsQuantileRule (fun (k : ℕ) (h : Fin k → ℝ) (p : ℝ) => npQuantile h p)

/-- T1 (c) (S3 :241-247; §4 :61-64, Algorithm S1 line 10): for `1 ≤ r ≤ k` the order statistic `h ↦ h_(r)` (`ordStat h r`) is
measurable, indeed 1-Lipschitz for the sup norm (the metric of `Fin k → ℝ`), and `h_(r) ≤ v ↔ r ≤ #{i : h_i ≤ v}`. Junk guard:
`ordStat` is an `sInf`, of a nonempty set bounded below exactly when `1 ≤ r ≤ k` (at `r = 0` it is `sInf univ = 0`). -/
def ordStat_facts : Prop :=
  ∀ k r : ℕ, 1 ≤ r → r ≤ k →
    Measurable (fun h : Fin k → ℝ => ordStat h r) ∧ LipschitzWith 1 (fun h : Fin k → ℝ => ordStat h r) ∧
    ∀ (h : Fin k → ℝ) (v : ℝ), ordStat h r ≤ v ↔ r ≤ (Finset.univ.filter fun i => h i ≤ v).card

/-! ### T2 — the printed batches and pairing -/

/-- T2 (a) (§4 :54-58, :70-74; S3 :99-103, :113-119; Algorithm S1 lines 1–2): for `nb ≥ 1` and any boundaries, a printed pairing of
the batches `cutLabel nb cx`, `cutLabel nb cy` exists; numpy's `array_split` gives one: in batch `b ∈ [1, nb]` with `1 ≤ n_b ≤ m_b`,
`X` number `l` of the batch (index `cx b + l`, the batch being `[cx b, cx (b+1))`) is paired with the `Y` block
`[l⌊m_b/n_b⌋ + min(l, m_b mod n_b), (l+1)⌊m_b/n_b⌋ + min(l+1, m_b mod n_b))` of the batch (offset `cy b`), the pairs numbered in the
order of the batches and, inside batch `b`, in that order (pair `Σ_{b′<b} min(n_{b′}, m_{b′}) + l`); the mirror if `1 ≤ m_b < n_b`.
A batch with an empty side has no pair (`l < min(n_b, m_b)` is then empty; the count clause of `IsPrintedPairing`). -/
def printedPairing_exists : Prop :=
  ∀ (nb n m : ℕ) (cx cy : ℕ → ℕ), 1 ≤ nb → IsBoundaries nb n cx → IsBoundaries nb m cy →
    ∃ (N : ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)),
      IsPrintedPairing nb (fun i : Fin n => cutLabel nb cx i) (fun j : Fin m => cutLabel nb cy j) bat A B ∧
      ∀ b ∈ Finset.Icc 1 nb, ∀ l : ℕ,
        l < min (batchCount (fun i : Fin n => cutLabel nb cx i) b) (batchCount (fun j : Fin m => cutLabel nb cy j) b) →
        ∃ k : Fin N,
          (k : ℕ) = (∑ b' ∈ Finset.Ico 1 b, min (batchCount (fun i : Fin n => cutLabel nb cx i) b')
            (batchCount (fun j : Fin m => cutLabel nb cy j) b')) + l ∧
          bat k = b ∧
          (batchCount (fun i : Fin n => cutLabel nb cx i) b ≤ batchCount (fun j : Fin m => cutLabel nb cy j) b →
            (∀ i : Fin n, i ∈ A k ↔ (i : ℕ) = cx b + l) ∧
            ∀ j : Fin m, j ∈ B k ↔
              cy b + splitStart (batchCount (fun j : Fin m => cutLabel nb cy j) b) (batchCount (fun i : Fin n => cutLabel nb cx i) b) l ≤ (j : ℕ) ∧
              (j : ℕ) < cy b + splitStart (batchCount (fun j : Fin m => cutLabel nb cy j) b)
                (batchCount (fun i : Fin n => cutLabel nb cx i) b) (l + 1)) ∧
          (batchCount (fun j : Fin m => cutLabel nb cy j) b < batchCount (fun i : Fin n => cutLabel nb cx i) b →
            (∀ j : Fin m, j ∈ B k ↔ (j : ℕ) = cy b + l) ∧
            ∀ i : Fin n, i ∈ A k ↔
              cx b + splitStart (batchCount (fun i : Fin n => cutLabel nb cx i) b) (batchCount (fun j : Fin m => cutLabel nb cy j) b) l ≤ (i : ℕ) ∧
              (i : ℕ) < cx b + splitStart (batchCount (fun i : Fin n => cutLabel nb cx i) b)
                (batchCount (fun j : Fin m => cutLabel nb cy j) b) (l + 1))

/-- T2 (b) (S3 :113-119; closes the declared instance gap of `wave30tv.md:44-46`): for `nb ≥ 1` and any boundaries, every printed
pairing is a batch pairing (`Wave30tv.IsBatchPairing`) of the labels `cutLabel nb cx`, `cutLabel nb cy`, with
`N = Σ_{b=1}^{nb} min(n_b, m_b)`, every `bat k ∈ [1, nb]`, exactly `min(n_b, m_b)` pairs in batch `b` (none in a batch with an empty
side), and nonempty blocks. -/
def printedPairing_batch : Prop :=
  ∀ (nb n m N : ℕ) (cx cy : ℕ → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)),
    1 ≤ nb → IsBoundaries nb n cx → IsBoundaries nb m cy →
    IsPrintedPairing nb (fun i : Fin n => cutLabel nb cx i) (fun j : Fin m => cutLabel nb cy j) bat A B →
      IsBatchPairing (fun i : Fin n => cutLabel nb cx i) (fun j : Fin m => cutLabel nb cy j) bat A B ∧
      N = ∑ b ∈ Finset.Icc 1 nb,
        min (batchCount (fun i : Fin n => cutLabel nb cx i) b) (batchCount (fun j : Fin m => cutLabel nb cy j) b) ∧
      (∀ k, 1 ≤ bat k ∧ bat k ≤ nb) ∧
      (∀ b ∈ Finset.Icc 1 nb, (Finset.univ.filter fun k => bat k = b).card =
        min (batchCount (fun i : Fin n => cutLabel nb cx i) b) (batchCount (fun j : Fin m => cutLabel nb cy j) b)) ∧
      (∀ b, (batchCount (fun i : Fin n => cutLabel nb cx i) b = 0 ∨ batchCount (fun j : Fin m => cutLabel nb cy j) b = 0) →
        ∀ k, bat k ≠ b) ∧
      ∀ k, (A k).Nonempty ∧ (B k).Nonempty

/-- T2 (c) (§4 :54-56; S4 :286 "boundaries at the nearest integers to `n/4` and `n/2`"): with `nb = 2` and nearest-integer
boundaries (any tie-breaking, any `n, m`), `cutLabel 2 cx = defaultLabel cx₁ cx₂` (and likewise for `y`), a printed pairing of these
labels has `N = defaultPairs`, and so a run with these labels and a printed pairing satisfies `IsDefaultRun`. -/
def printedPairing_default : Prop :=
  ∀ (n m N : ℕ) (cx cy : ℕ → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)),
    NearestCuts n (cx 1) (cx 2) → NearestCuts m (cy 1) (cy 2) →
      (∀ i : ℕ, cutLabel 2 cx i = defaultLabel (cx 1) (cx 2) i) ∧ (∀ j : ℕ, cutLabel 2 cy j = defaultLabel (cy 1) (cy 2) j) ∧
      (IsPrintedPairing 2 (fun i : Fin n => cutLabel 2 cx i) (fun j : Fin m => cutLabel 2 cy j) bat A B →
        N = defaultPairs (fun i : Fin n => cutLabel 2 cx i) (fun j : Fin m => cutLabel 2 cy j)) ∧
      ∀ (𝒳 : Type) (J : ℕ) (R : LoRun 𝒳 J n m), (∀ i : Fin n, R.lx i = cutLabel 2 cx i) →
        (∀ j : Fin m, R.ly j = cutLabel 2 cy j) → IsPrintedPairing 2 R.lx R.ly R.bat R.A R.B → IsDefaultRun R

/-! ### T3 — measurable exact minimizers of `eq:qp` -/

/-- T3 (§2 :176-182 `eq:qp`; Prop 4.4 "an exact minimizer of `eq:qp` at each level", §4 :148-149; Aliprantis–Border Thm 18.19):
for `α ∈ [0,1)` and `n, m ≥ 1` there is a measurable selection `σ` of exact minimizers (`IsQPSel`); for every such selection
`(x, y) ↦ qpVal φ x y σ(x,y)` is measurable and equals `D̂_α = Demp φ x y α`; and the two library encodings of `eq:qp` agree:
`IsCapped α ↔ BangBang.capped`, `BangBang.qp (φ ∘ x) (φ ∘ y) (w, v) = qpVal φ x y w v ^ 2`, and `IsQPMin` is minimality of
`BangBang.qp` on `capped × capped`. -/
def qp_measurable_argmin : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (α : ℝ) (n m : ℕ),
    StronglyMeasurable φ → 0 ≤ α → α < 1 → 1 ≤ n → 1 ≤ m →
      (∃ σ : (Fin n → 𝒳) × (Fin m → 𝒳) → (Fin n → ℝ) × (Fin m → ℝ), IsQPSel φ α σ) ∧
      (∀ σ : (Fin n → 𝒳) × (Fin m → 𝒳) → (Fin n → ℝ) × (Fin m → ℝ), IsQPSel φ α σ →
        Measurable (fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => qpVal φ p.1 p.2 (σ p).1 (σ p).2) ∧
        ∀ p : (Fin n → 𝒳) × (Fin m → 𝒳), qpVal φ p.1 p.2 (σ p).1 (σ p).2 = Demp φ p.1 p.2 α) ∧
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ),
        (IsCapped α w ↔ w ∈ capped n α) ∧ (IsCapped α v ↔ v ∈ capped m α) ∧
        qp (fun i => φ (x i)) (fun j => φ (y j)) (w, v) = qpVal φ x y w v ^ 2 ∧
        (IsQPMin φ α x y w v ↔ (w, v) ∈ capped n α ×ˢ capped m α ∧
          IsMinOn (qp (fun i => φ (x i)) (fun j => φ (y j))) (capped n α ×ˢ capped m α) (w, v))

/-! ### T14 — at `α = 0` the fit has uniform weights -/

/-- T14 (S3 :363-364, "Witnesses `f̂_{0,b}` fitted at `α = 0` have uniform weights"): for `n, m ≥ 1` and any `φ`, the capped simplex
`Δ_0(n)` is the single point `(1/n, …, 1/n)`; the exact minimizers of `eq:qp` at `α = 0` are exactly the uniform pair; at it
`D̂_0 = ‖n⁻¹Σφ(x_i) − m⁻¹Σφ(y_j)‖` and the witness is `(n⁻¹Σφ(x_i) − m⁻¹Σφ(y_j))/D̂_0`, `0` if `D̂_0 = 0`. With `φ` strongly
measurable (needed for the integrals to be meaningful: Bochner integrals of a non-measurable map are the junk `0`) also
`Demp φ x y 0 = D̂_0 = MMD(P_n, Q_m) = ‖∫ φ dP_n − ∫ φ dQ_m‖`. -/
def alpha0_uniform : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (n m : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳), 1 ≤ n → 1 ≤ m →
      {w : Fin n → ℝ | IsCapped 0 w} = {fun _ => 1 / (n : ℝ)} ∧
      (∀ (w : Fin n → ℝ) (v : Fin m → ℝ),
        IsQPMin φ 0 x y w v ↔ w = (fun _ => 1 / (n : ℝ)) ∧ v = fun _ => 1 / (m : ℝ)) ∧
      qpVal φ x y (fun _ => 1 / (n : ℝ)) (fun _ => 1 / (m : ℝ)) =
        ‖(n : ℝ)⁻¹ • ∑ i, φ (x i) - (m : ℝ)⁻¹ • ∑ j, φ (y j)‖ ∧
      witness φ x y (fun _ => 1 / (n : ℝ)) (fun _ => 1 / (m : ℝ)) =
        ‖(n : ℝ)⁻¹ • ∑ i, φ (x i) - (m : ℝ)⁻¹ • ∑ j, φ (y j)‖⁻¹ • ((n : ℝ)⁻¹ • ∑ i, φ (x i) - (m : ℝ)⁻¹ • ∑ j, φ (y j)) ∧
      (‖(n : ℝ)⁻¹ • ∑ i, φ (x i) - (m : ℝ)⁻¹ • ∑ j, φ (y j)‖ = 0 →
        witness φ x y (fun _ => 1 / (n : ℝ)) (fun _ => 1 / (m : ℝ)) = 0) ∧
      (StronglyMeasurable φ →
        Demp φ x y 0 = ‖(n : ℝ)⁻¹ • ∑ i, φ (x i) - (m : ℝ)⁻¹ • ∑ j, φ (y j)‖ ∧
        ‖(∫ z, φ z ∂(empirical x)) - ∫ z, φ z ∂(empirical y)‖ =
          ‖(n : ℝ)⁻¹ • ∑ i, φ (x i) - (m : ℝ)⁻¹ • ∑ j, φ (y j)‖)

/-! ### T18–T20 — the Frank–Wolfe variant (S3 :358-360) -/

/-- T18 (a), (b) (S3 :359-360, "as the gap is `2d² − 2ds` for the empirical separation `s` of its witness"): for capped `(w, v)`
with `d = ‖e‖ = qpVal > 0`, `f̂ = e/d = witness` and `s = fwSep` (over the capped simplices): (a) the maximum over capped `(w′, v′)`
of `2⟨e, e⟩ − 2⟨e, e′⟩` (the Frank–Wolfe gap of `F = ‖e‖²`) is `2d² − 2ds`; (b) `IsFWPoint ρ` holds iff `s ≥ (1 − ρ/2)d`, and
`s ≤ D̂_α ≤ d`; and `s` is the printed separation `sep(f̂; 𝒞_α(P_n), 𝒞_α(Q_m))` (the frozen `Wave17a.sepVal`). `φ` strongly
measurable and `ℋ` complete (the common setting) make `D̂_α = Demp` and the regions meaningful. -/
def fw_gap : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (α ρ : ℝ) (n m : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ),
    StronglyMeasurable φ → IsCapped α w → IsCapped α v → 0 < qpVal φ x y w v →
      IsGreatest {g : ℝ | ∃ (w' : Fin n → ℝ) (v' : Fin m → ℝ), IsCapped α w' ∧ IsCapped α v' ∧
          g = 2 * ⟪wsum φ x w - wsum φ y v, wsum φ x w - wsum φ y v⟫_ℝ -
            2 * ⟪wsum φ x w - wsum φ y v, wsum φ x w' - wsum φ y v'⟫_ℝ}
        (2 * qpVal φ x y w v ^ 2 - 2 * qpVal φ x y w v * fwSep φ α x y (witness φ x y w v)) ∧
      (IsFWPoint φ α ρ x y w v ↔ (1 - ρ / 2) * qpVal φ x y w v ≤ fwSep φ α x y (witness φ x y w v)) ∧
      fwSep φ α x y (witness φ x y w v) ≤ Demp φ x y α ∧ Demp φ x y α ≤ qpVal φ x y w v ∧
      StatFormal.Wave17a.sepVal (witness φ x y w v) (region φ α (empirical x)) (region φ α (empirical y)) =
        ((fwSep φ α x y (witness φ x y w v) : ℝ) : EReal)

/-- T18 (c) (S3 :358-360): an exact minimizer of `eq:qp` is an `IsFWPoint 0`, with `s = d`; hence every `IsWitnessRun` is an
`IsWitnessRunFW 0` (FW runs exist, by T4–T5). Both hold for every `φ` (no measurability is used). -/
def fw_exact : Prop :=
  (∀ (𝒳 H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) (α : ℝ) (n m : ℕ)
      (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ),
      IsQPMin φ α x y w v → IsFWPoint φ α 0 x y w v ∧ fwSep φ α x y (witness φ x y w v) = qpVal φ x y w v) ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) (J n m : ℕ)
    (α : Fin J → ℝ) (δ lmax s2 : ℝ) (R : LoRun 𝒳 J n m),
    R.IsWitnessRun φ α δ lmax s2 → IsWitnessRunFW R φ α δ lmax s2 0

/-- T19 (S3 :358-360, "serves with `(1−ρ/2)D̲` for `D̲`"): the certified `Wave30tz.fitted_ramp` (Lemma 4) with `IsQPMin` replaced by
`IsFWPoint ρ`, `0 ≤ ρ < 1`, its hypothesis `βZ⁻ < D_α` replaced by `βZ⁻ < (1−ρ/2)D_α`, and `D_α` replaced by `(1−ρ/2)D_α` in `Θ`
(`fitTheta α ((1−ρ/2)D_α) Z Z⁻ κ Δ_φ r ≤ θ(f̂; t, u)` and the excess bound); the other conclusions (`D̂ ≥ D_α − βZ⁻ > 0` at the
point, `t − u ≤ Δ_φ`, `θ ≤ t − u`) unchanged. -/
def fitted_ramp_fw : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ Dφ α ρ : ℝ) (n m : ℕ)
    (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → 0 ≤ α → α < 1 → 1 ≤ n → 1 ≤ m →
    0 ≤ ρ → ρ < 1 → IsFWPoint φ α ρ x y w v →
    beta α * StatFormal.Wave30ty.hingeZm P Q φ hingePos hingePos 1 κ κ (x, y) < (1 - ρ / 2) * Dpop φ P Q α →
      Dpop φ P Q α - beta α * StatFormal.Wave30ty.hingeZm P Q φ hingePos hingePos 1 κ κ (x, y) ≤ qpVal φ x y w v ∧
      0 < qpVal φ x y w v ∧
      ∀ t u, CutsC α (ownX φ x y w v) (ownY φ x y w v) t u →
        t - u ≤ Dφ ∧ theta P Q α (fun z => ⟪witness φ x y w v, φ z⟫_ℝ) t u ≤ t - u ∧
        fitTheta α ((1 - ρ / 2) * Dpop φ P Q α) (StatFormal.Wave30ty.hingeZ P Q φ hingePos hingePos 1 κ κ (x, y))
            (StatFormal.Wave30ty.hingeZm P Q φ hingePos hingePos 1 κ κ (x, y)) κ Dφ (1 / n + 1 / m) ≤
          theta P Q α (fun z => ⟪witness φ x y w v, φ z⟫_ℝ) t u ∧
        (0 < fitTheta α ((1 - ρ / 2) * Dpop φ P Q α) (StatFormal.Wave30ty.hingeZ P Q φ hingePos hingePos 1 κ κ (x, y))
            (StatFormal.Wave30ty.hingeZm P Q φ hingePos hingePos 1 κ κ (x, y)) κ Dφ (1 / n + 1 / m) →
          u < t ∧
          fitTheta α ((1 - ρ / 2) * Dpop φ P Q α) (StatFormal.Wave30ty.hingeZ P Q φ hingePos hingePos 1 κ κ (x, y))
              (StatFormal.Wave30ty.hingeZm P Q φ hingePos hingePos 1 κ κ (x, y)) κ Dφ (1 / n + 1 / m) / (beta α * Dφ) ≤
            (∫ z, ramp (fun z => ⟪witness φ x y w v, φ z⟫_ℝ) t u z ∂P) -
              (∫ z, ramp (fun z => ⟪witness φ x y w v, φ z⟫_ℝ) t u z ∂Q) - α)

/-- T20 (a) (S3 :358-360): the certified `Wave30tz.lo_lower_bound` for runs with `IsWitnessRunFW ρ`, `0 ≤ ρ < 1`, with its
hypothesis `d ≤ D_{α_i}` replaced by `d ≤ (1−ρ/2)D_{α_i}`; all else, including the conclusion, as certified. -/
def lo_lower_bound_fw : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (J n m : ℕ) (α : Fin J → ℝ) (δ lmax s2 ρ : ℝ) (R : LoRun 𝒳 J n m) (Bmax : ℕ) (i : Fin J)
    (d r : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) →
    IsGrid α → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 / 2 → 0 < s2 → s2 ≤ 4 → 0 ≤ ρ → ρ < 1 →
    IsWitnessRunFW R φ α δ lmax s2 ρ →
    (∀ k, R.bat k ≤ Bmax) → (∀ k, 1 ≤ fitCard R.lx (R.bat k) ∧ 1 ≤ fitCard R.ly (R.bat k)) →
    (∀ k, 1 / (fitCard R.lx (R.bat k) : ℝ) + 1 / (fitCard R.ly (R.bat k) : ℝ) ≤ r) →
    0 < d → d ≤ (1 - ρ / 2) * Dpop φ P Q (α i) →
    beta (α i) * Dφ * r ≤ d / 8 → beta (α i) ^ 2 * κ ^ 2 * r ≤ 7 * d ^ 2 / 64 →
    Real.log (1 / δ) * (1 + α i) ^ 2 / (2 * lmax ^ 2) ≤ R.N →
      sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < α i} ≤
        ENNReal.ofReal (2 * Bmax * Real.exp (-(2 * (max (d / (8 * beta (α i)) - 2 * (1 + √2) * κ * √r) 0) ^ 2 /
            (Dφ ^ 2 * r))) + J * epsN s2 (α i) (Real.log (1 / δ)) R.N (d / (2 * beta (α i) * Dφ)))

/-- T20 (b) (S3 :358-360; the printed three sentences of `prop:loconsistency`, §4 :146-157): the certified `Wave30tz.lo_consistency`
for families of `IsWitnessRunFW ρ ∧ IsSizedRun` runs, `0 ≤ ρ < 1`; all else as certified. -/
def lo_consistency_fw : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (J : ℕ) (α : Fin J → ℝ) (δ lmax s2 c C0 ρ : ℝ) (Bmax : ℕ) (R : ∀ n m : ℕ, LoRun 𝒳 J n m),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Characteristic φ → IsGrid α →
    0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 / 2 → 0 < s2 → 0 < c → 0 ≤ ρ → ρ < 1 →
    (∀ n m, IsWitnessRunFW (R n m) φ α δ lmax s2 ρ ∧ (R n m).IsSizedRun c C0 Bmax) →
      (∀ n m, sampleLaw P Q n m
          {ω | gridBelow α (StatFormal.Distances.tvDist P Q) < (R n m).alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal δ) ∧
      (∀ ε > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → sampleLaw P Q n m
          {ω | (R n m).alphaLo α δ ω.1 ω.2 < gridBelow α (StatFormal.Distances.tvDist P Q)} ≤ ENNReal.ofReal ε) ∧
      ((∀ j, α j ≠ StatFormal.Distances.tvDist P Q) → ∀ ε > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → sampleLaw P Q n m
          {ω | gridBelow α (StatFormal.Distances.tvDist P Q) < (R n m).alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal ε)

/-! ### T22 (b) — the two parts of Corollary 5.9 concern the same quantile -/

/-- T22 (b) (main :220-222, "and with `η < (1−δ)/2` the two parts concern the same quantile of the error"): for `κ, Δ_φ`,
`0 < a₁ < 1`, `c₀ > 0`, `v²_min ∈ (0,4]`, `δ, η ∈ (0,1)` with `η < (1−δ)/2` there are `C, N₁` (those of `minimax_iii`, Cor 5.9 (ii);
uniform in `a₀`, as there) such that for every `a₀ ∈ (0, a₁)`, every (A1)–(A2) feature map with `‖φ‖ ≤ κ`, `‖φx − φx′‖ ≤ Δ_φ ≤ 2κ`,
three points with `f(x₁) = 1`, `f(x₂) = 0`, `f(x₃) = −1`, `c₀ ≤ 1/‖f‖`, all `n, m` with `N = n∧m ≥ max(N₁, 10, c_lo²/(a₁−a₀)²)`
and every run with `IsWitnessRun φ (rootGrid N) δ (1/2) v²_min ∧ IsDefaultRun` (the paper's run, T11), the error
`e = TV(P,Q) − α̂` has: `P(e > C N^{-1/2}) ≤ η` at every `(P,Q) ∈ 𝓜(a₀,a₁,c₀)`; at some `(P,Q) ∈ 𝓜`, `P(e > r) > η` for every
`r < c_lo N^{-1/2}`; and `c_lo ≤ C`. So the worst-case upper `η`-quantile of `e` lies in `[c_lo N^{-1/2}, C N^{-1/2}]` (stated
without `sInf`). -/
def same_quantile : Prop :=
  ∀ (κ Dφ a₁ c₀ s2 δ η : ℝ), 0 < a₁ → a₁ < 1 → 0 < c₀ → 0 < s2 → s2 ≤ 4 → 0 < δ → δ < 1 → 0 < η → η < 1 →
    η < (1 - δ) / 2 →
    ∃ C N₁ : ℝ, ∀ (a₀ : ℝ) (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (x₁ x₂ x₃ : 𝒳) (f : H) (n m : ℕ)
      (R : LoRun 𝒳 (rootLevels (min n m)) n m),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ →
      ⟪f, φ x₁⟫_ℝ = 1 → ⟪f, φ x₂⟫_ℝ = 0 → ⟪f, φ x₃⟫_ℝ = -1 → 0 < a₀ → a₀ < a₁ → c₀ ≤ 1 / ‖f‖ →
      max (max N₁ 10) (clo δ a₀ ^ 2 / (a₁ - a₀) ^ 2) ≤ ((min n m : ℕ) : ℝ) →
      R.IsWitnessRun φ (rootGrid (min n m)) δ (1 / 2) s2 → IsDefaultRun R →
        (∀ P Q : Measure 𝒳, InM φ a₀ a₁ c₀ P Q →
          sampleLaw P Q n m {ω | C / √((min n m : ℕ) : ℝ) <
            StatFormal.Distances.tvDist P Q - R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2} ≤ ENNReal.ofReal η) ∧
        (∃ P Q : Measure 𝒳, InM φ a₀ a₁ c₀ P Q ∧ ∀ r : ℝ, r < clo δ a₀ / √((min n m : ℕ) : ℝ) →
          ENNReal.ofReal η < sampleLaw P Q n m {ω | r <
            StatFormal.Distances.tvDist P Q - R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2}) ∧
        clo δ a₀ ≤ C

/-! ### T31 — the pairs number about `¾ min(n,m)` -/

/-- T31 (§4 :73, "The pairs of both batches … number about `¾ min(n,m)`"): for the batches of §4.2 (nearest-integer boundaries to
`n/4, n/2` and `m/4, m/2`, any tie-breaking, any `n, m`), `|defaultPairs − ¾ min(n,m)| ≤ 3/2`. -/
def default_pairs_three_quarters : Prop :=
  ∀ (n m b₁ b₂ c₁ c₂ : ℕ), NearestCuts n b₁ b₂ → NearestCuts m c₁ c₂ →
    |(defaultPairs (fun i : Fin n => defaultLabel b₁ b₂ i) (fun j : Fin m => defaultLabel c₁ c₂ j) : ℝ) -
      3 / 4 * ((min n m : ℕ) : ℝ)| ≤ 3 / 2

/-! ### C7: two short remarks of §S4 (T24, T25) -/

/-- T24 (S4 :306): under (A1), for probability measures with `α⋆ = TV(P,Q) < 1` and every `α ∈ [0, α⋆]`,
`D̄_α ≤ D_α(P,Q) ≤ D̄_α/(1−α⋆)`, where `D̄_α = (1−α)D_α` is the rescaled path `Wave31ti.uPath`. -/
def dbar_le_D_le : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 → 0 ≤ α →
    α ≤ StatFormal.Distances.tvDist P Q →
      StatFormal.Wave31ti.uPath φ P Q α ≤ Dpop φ P Q α ∧
        Dpop φ P Q α ≤ StatFormal.Wave31ti.uPath φ P Q α / (1 - StatFormal.Distances.tvDist P Q)

/-- T25 (both bullets) (S4 :509-512; Proposition S4.8 part (i) against Theorem S4.3): a polynomial margin of `D` with `α⋆ < 1` gives the margin
`ω(ε) = (1−α⋆)c₀ε^γ` of `D̄` required by `Wave31to.Claims.newrates_ii_b` (nondecreasing and nonnegative on `[0, α⋆]`, and
`ω(ε) ≤ D̄_{α⋆−ε} = (1−α⋆+ε)D_{α⋆−ε}`); at this `ω`, `ω^←(t) = min{α⋆, (1−α⋆)^{-1/γ}(t/c₀)^{1/γ}}` for every `t ≥ 0`, so the error
term `(t_{n,m}/c₀)^{1/γ}` of `lorate_ii` is divided by `(1−α⋆)^{1/γ}`, i.e. multiplied by `(1−α⋆)^{-1/γ} ≥ 1` ("loses a factor
`(1−α⋆)^{1/γ}`"). -/
def margin_dbar_factor : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) (P Q : Measure 𝒳)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (c₀ γ : ℝ),
    StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ → StatFormal.Distances.tvDist P Q < 1 →
      MonotoneOn (fun e : ℝ => (1 - StatFormal.Distances.tvDist P Q) * c₀ * e ^ γ)
          (Icc 0 (StatFormal.Distances.tvDist P Q)) ∧
        (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
          0 ≤ (1 - StatFormal.Distances.tvDist P Q) * c₀ * e ^ γ ∧
            (1 - StatFormal.Distances.tvDist P Q) * c₀ * e ^ γ ≤
              StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - e) ∧
            StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - e) =
              (1 - StatFormal.Distances.tvDist P Q + e) * Dpop φ P Q (StatFormal.Distances.tvDist P Q - e)) ∧
        (∀ t : ℝ, 0 ≤ t →
          StatFormal.Wave31to.genInv (fun e => (1 - StatFormal.Distances.tvDist P Q) * c₀ * e ^ γ)
              (StatFormal.Distances.tvDist P Q) t =
            min (StatFormal.Distances.tvDist P Q)
              ((1 - StatFormal.Distances.tvDist P Q) ^ (-1 / γ) * (t / c₀) ^ (1 / γ))) ∧
        1 ≤ (1 - StatFormal.Distances.tvDist P Q) ^ (-1 / γ)

/-! ### Library-type printed facts of §1, §2, S1, S5 (T33, T34 (a)–(b), T36, T37) -/

open scoped Pointwise in
/-- T33 (existence and uniqueness) (§2 :196-197, §6 :17-19, S5 :45-47): under (A1)–(A2), for probability measures `P, Q` and `α ∈ [0,1)`, the set
`𝒞_α(P) − 𝒞_α(Q)` is nonempty, convex and compact; it has exactly one element `d⋆` of minimal norm (the population witness); and
`‖d⋆‖ = D_α(P,Q)` with `d⋆ = a⋆ − b⋆`, `a⋆ ∈ 𝒞_α(P)`, `b⋆ ∈ 𝒞_α(Q)` (nearest points). -/
def witness_unique : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      (region φ α P - region φ α Q).Nonempty ∧ Convex ℝ (region φ α P - region φ α Q) ∧
        IsCompact (region φ α P - region φ α Q) ∧
        (∃! d : H, StatFormal.TrimmedMMD.Projection.IsMinNorm (region φ α P - region φ α Q) d) ∧
        ∀ d : H, StatFormal.TrimmedMMD.Projection.IsMinNorm (region φ α P - region φ α Q) d →
          ‖d‖ = Dpop φ P Q α ∧ ∃ a ∈ region φ α P, ∃ b ∈ region φ α Q, d = a - b

/-- T34 (a) (§2 :28-34 `eq:contam`, §1 :11-13): for probability measures `P, Q` and `α ∈ [0,1]`, `TV(P,Q) ≤ α` iff there are probability
measures `R, P₀, Q₀` with `P = (1−α)R + αP₀` and `Q = (1−α)R + αQ₀` ("or, equivalently", with `eq:tvintersect`); hence
`α⋆ = TV(P,Q)` is the least such `α` ("the smallest such `α`"), and it is attained. -/
def contam_equiv : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    (∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      (StatFormal.Distances.tvDist P Q ≤ α ↔
        ∃ R P₀ Q₀ : Measure 𝒳, IsProbabilityMeasure R ∧ IsProbabilityMeasure P₀ ∧ IsProbabilityMeasure Q₀ ∧
          P = ENNReal.ofReal (1 - α) • R + ENNReal.ofReal α • P₀ ∧
          Q = ENNReal.ofReal (1 - α) • R + ENNReal.ofReal α • Q₀)) ∧
    IsLeast {α : ℝ | 0 ≤ α ∧ α ≤ 1 ∧
        ∃ R P₀ Q₀ : Measure 𝒳, IsProbabilityMeasure R ∧ IsProbabilityMeasure P₀ ∧ IsProbabilityMeasure Q₀ ∧
          P = ENNReal.ofReal (1 - α) • R + ENNReal.ofReal α • P₀ ∧
          Q = ENNReal.ofReal (1 - α) • R + ENNReal.ofReal α • Q₀}
      (StatFormal.Distances.tvDist P Q)

/-- T34 (b) (§1 :19-22, S1 :17-26): for `α ∈ [0,1)`, the laws with a density at most `(1−α)⁻¹` with respect to `P` (`IsTrimDensity`) are
exactly the laws `(P − ν)/(1 − ν(𝒳))` for measures `ν ≤ P` with `ν(𝒳) ≤ α` ("obtained from `P` by removing at most a fraction `α` of
its mass, possibly only partially at each point, and renormalizing"); `P − ν` is `Measure.sub`, and `1 − ν(𝒳) ≥ 1 − α > 0`. -/
def trimming_removal : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P : Measure 𝒳) [IsProbabilityMeasure P] (α : ℝ), 0 ≤ α → α < 1 →
    ∀ μ : Measure 𝒳,
      (∃ g : 𝒳 → ℝ, IsTrimDensity P α g ∧ μ = P.withDensity (fun x => ENNReal.ofReal (g x))) ↔
        ∃ ν : Measure 𝒳, ν ≤ P ∧ ν.real univ ≤ α ∧ μ = (ENNReal.ofReal (1 - ν.real univ))⁻¹ • (P - ν)

/-- T36 (a)–(c) (§2 :85-86, :116-118): under (A1), for probability measures `P, Q`: (a) `𝒞_α(P) ⊆ 𝒞_{α′}(P)` for `0 ≤ α ≤ α′ < 1`; (b)
`𝒞_0(P) = {μ_P}` ("the regions grow with `α` from the single point `μ_P`"); (c) `α ↦ D_α(P,Q)` is nonincreasing on `[0,1)` ("It is
nonincreasing, because the regions are nested"). -/
def regions_nested : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
      (∀ α α' : ℝ, 0 ≤ α → α ≤ α' → α' < 1 → region φ α P ⊆ region φ α' P) ∧
        region φ 0 P = {∫ x, φ x ∂P} ∧
        AntitoneOn (fun α => Dpop φ P Q α) (Ico 0 1)

/-- T37 (a)–(b) (§2 :150-154, S5 :69-73): for a probability measure `R`, a bounded measurable `f` and `α ∈ [0,1)`, `β = (1−α)⁻¹`: (a) `t`
maximizes `t ↦ t − βE_R(t − f)_+` iff `R(f < t) ≤ 1 − α ≤ R(f ≤ t)`; (b) `u` minimizes `u ↦ u + βE_R(f − u)_+` iff
`R(f < u) ≤ α ≤ R(f ≤ u)` ("so its maximizers are the `t` with `R(f<t) ≤ 1−α ≤ R(f≤t)` …; likewise the minimizers in `U_R` are the
`α`-quantiles"). -/
def bathtub_quantiles : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (R : Measure 𝒳) [IsProbabilityMeasure R] (f : 𝒳 → ℝ) (α : ℝ),
    Measurable f → (∃ C, ∀ x, |f x| ≤ C) → 0 ≤ α → α < 1 →
      (∀ t : ℝ, IsMaxOn (fun s : ℝ => s - 1 / (1 - α) * ∫ x, max (s - f x) 0 ∂R) univ t ↔
          IsQuantileAt R f (1 - α) t) ∧
        ∀ u : ℝ, IsMinOn (fun s : ℝ => s + 1 / (1 - α) * ∫ x, max (f x - s) 0 ∂R) univ u ↔
          IsQuantileAt R f α u

/-! ### Proposition 5.10 and Lemmas S4.17, S4.18: the excess of the population ramp (T38–T42) -/

/-- T38 (a)–(b), (G) ∧ (Pr) (Lemma S4.17 `lem:excessbathtub`, S4 :900-906; setting S4 :892-898), with the closest parts `P′ = (1−α)g·P`, `Q′ = (1−α)h·Q`
(`Wave30tq.trimMeasure`) for representing trimming densities `g`, `h` of the nearest points `a`, `b`:
(a) every measure `P″ ≤ P` has `∫ f⋆ dP″ ≥ ∫ f⋆ dP′ + t{P″(𝒳) − (1−α)}`, and every `Q″ ≤ Q` has `∫ f⋆ dQ″ ≤ ∫ f⋆ dQ′ + u{Q″(𝒳) − (1−α)}`;
(b) `P′ = P` on `{f⋆ < t}`, `P′({f⋆ > t}) = 0`, `Q′ = Q` on `{f⋆ > u}`, `Q′({f⋆ < u}) = 0` (as restrictions).
(G) any representing densities and any quantiles `t`, `u`, no (A3); (Pr) the printed `t⋆` (least), `u⋆` (greatest), Assumption 2.1,
`0 < α⋆ < 1`, `0 ≤ α < α⋆`. -/
def excess_bathtub : Prop :=
  (∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (φ : 𝒳 → H) (κ α : ℝ) (a b : H) (g h : 𝒳 → ℝ) (t u : ℝ),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 0 < Dpop φ P Q α →
      IsTrimDensity P α g → a = ∫ x, g x • φ x ∂P → IsTrimDensity Q α h → b = ∫ y, h y • φ y ∂Q →
      ‖a - b‖ = Dpop φ P Q α →
      IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) t →
      IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α u →
        (∀ P'' : Measure 𝒳, P'' ≤ P →
          (∫ x, ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ ∂(trimMeasure P fun x => (1 - α) * g x)) +
              t * (P''.real univ - (1 - α)) ≤
            ∫ x, ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ ∂P'') ∧
        (∀ Q'' : Measure 𝒳, Q'' ≤ Q →
          ∫ y, ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ ∂Q'' ≤
            (∫ y, ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ ∂(trimMeasure Q fun y => (1 - α) * h y)) +
              u * (Q''.real univ - (1 - α))) ∧
        (trimMeasure P fun x => (1 - α) * g x).restrict {x | ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ < t} =
          P.restrict {x | ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ < t} ∧
        (trimMeasure P fun x => (1 - α) * g x) {x | t < ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ} = 0 ∧
        (trimMeasure Q fun y => (1 - α) * h y).restrict {y | u < ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ} =
          Q.restrict {y | u < ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ} ∧
        (trimMeasure Q fun y => (1 - α) * h y) {y | ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ < u} = 0) ∧
  (∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (φ : 𝒳 → H) (κ α : ℝ) (a b : H) (g h : 𝒳 → ℝ) (t u : ℝ),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
      0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      0 ≤ α → α < StatFormal.Distances.tvDist P Q →
      a ∈ region φ α P → b ∈ region φ α Q → ‖a - b‖ = Dpop φ P Q α →
      IsLeast {q | IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) q} t →
      IsGreatest {q | IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α q} u →
      IsTrimDensity P α g → a = ∫ x, g x • φ x ∂P → IsTrimDensity Q α h → b = ∫ y, h y • φ y ∂Q →
        (∀ P'' : Measure 𝒳, P'' ≤ P →
          (∫ x, ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ ∂(trimMeasure P fun x => (1 - α) * g x)) +
              t * (P''.real univ - (1 - α)) ≤
            ∫ x, ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ ∂P'') ∧
        (∀ Q'' : Measure 𝒳, Q'' ≤ Q →
          ∫ y, ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ ∂Q'' ≤
            (∫ y, ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ ∂(trimMeasure Q fun y => (1 - α) * h y)) +
              u * (Q''.real univ - (1 - α))) ∧
        (trimMeasure P fun x => (1 - α) * g x).restrict {x | ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ < t} =
          P.restrict {x | ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ < t} ∧
        (trimMeasure P fun x => (1 - α) * g x) {x | t < ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ} = 0 ∧
        (trimMeasure Q fun y => (1 - α) * h y).restrict {y | u < ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ} =
          Q.restrict {y | u < ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ} ∧
        (trimMeasure Q fun y => (1 - α) * h y) {y | ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ < u} = 0)

/-- T39, (G) ∧ (Pr) (Lemma S4.18 `lem:excessid`, S4 :929-935): the excess identity
`E_Pψ − E_Qψ − α = {D̄_α + ∫(u − f⋆)_+ dP + ∫(f⋆ − t)_+ dQ}/(t − u)`, `D̄_α = (1−α)D_α` (`Wave31ti.uPath`), `ψ = ramp f⋆ t u`.
(G) any quantiles `u < t`, no (A3); (Pr) at the printed `u⋆ < t⋆`. -/
def excess_identity : Prop :=
  (∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (φ : 𝒳 → H) (κ α : ℝ) (a b : H) (t u : ℝ),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 0 < Dpop φ P Q α →
      a ∈ region φ α P → b ∈ region φ α Q → ‖a - b‖ = Dpop φ P Q α →
      IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) t →
      IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α u → u < t →
        (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
            (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - α =
          (StatFormal.Wave31ti.uPath φ P Q α + (∫ x, max (u - ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) 0 ∂P) +
              ∫ y, max (⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ - t) 0 ∂Q) / (t - u)) ∧
  (∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (φ : 𝒳 → H) (κ α : ℝ) (a b : H) (t u : ℝ),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
      0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      0 ≤ α → α < StatFormal.Distances.tvDist P Q →
      a ∈ region φ α P → b ∈ region φ α Q → ‖a - b‖ = Dpop φ P Q α →
      IsLeast {q | IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) q} t →
      IsGreatest {q | IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α q} u →
        (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
            (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - α =
          (StatFormal.Wave31ti.uPath φ P Q α + (∫ x, max (u - ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) 0 ∂P) +
              ∫ y, max (⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ - t) 0 ∂Q) / (t - u))

/-- T40 (i-1), (i-2), (Pr-0), (G) ∧ (Pr) (Proposition 5.10 `prop:excess` (i), main :278-279; main :253-255, :275-276; proof S4 :953-957):
(i-1) `E_Pψ − E_Qψ − α ≥ (1−α)D_α/(t − u)`; (i-2) for every `α′ ∈ [0,1)`, `(1−α′)D_{α′} ≥ (1−α)D_α − (t − u)(α′ − α)` ("the line
through the point of the path at `α` with slope `−(t⋆−u⋆)` lies below the path"). (G) any quantiles (`u < t` for (i-1), where the ramp
is used); (Pr) at the printed `t⋆`, `u⋆`, with the conjunct (Pr-0) `t⋆ − u⋆ ≥ D_α > 0` (main :275-276, "so that `t⋆−u⋆ ≥ D_α > 0`
(Lemma S3.4 of the supplement)"). -/
def excess_i : Prop :=
  (∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (φ : 𝒳 → H) (κ α : ℝ) (a b : H) (t u : ℝ),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 0 < Dpop φ P Q α →
      a ∈ region φ α P → b ∈ region φ α Q → ‖a - b‖ = Dpop φ P Q α →
      IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) t →
      IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α u →
        (u < t →
          (1 - α) * Dpop φ P Q α / (t - u) ≤
            (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
              (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - α) ∧
        ∀ α' ∈ Ico (0 : ℝ) 1, (1 - α) * Dpop φ P Q α - (t - u) * (α' - α) ≤ (1 - α') * Dpop φ P Q α') ∧
  (∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (φ : 𝒳 → H) (κ α : ℝ) (a b : H) (t u : ℝ),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
      0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      0 ≤ α → α < StatFormal.Distances.tvDist P Q →
      a ∈ region φ α P → b ∈ region φ α Q → ‖a - b‖ = Dpop φ P Q α →
      IsLeast {q | IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) q} t →
      IsGreatest {q | IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α q} u →
        (Dpop φ P Q α ≤ t - u ∧ 0 < Dpop φ P Q α) ∧
        (1 - α) * Dpop φ P Q α / (t - u) ≤
            (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
              (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - α ∧
        ∀ α' ∈ Ico (0 : ℝ) 1, (1 - α) * Dpop φ P Q α - (t - u) * (α' - α) ≤ (1 - α') * Dpop φ P Q α')

/-- T41, (G) ∧ (Pr) (Proposition 5.10 `prop:excess` (ii), main :280-282; main :256-257; proof S4 :959-964): let `0 < α⋆ < 1`, `γ > 0`,
`c₁, c₂ > 0`, `0 < ε₀ ≤ α⋆` with `c₁ε^γ ≤ D_{α⋆−ε}(P,Q) ≤ c₂ε^γ` for `0 < ε ≤ ε₀`. Then for every `ε ∈ (0, ε₀/2]`, at
`α = α⋆ − ε`, `(1 − α⋆)c₁ε/(2^γ c₂) ≤ E_Pψ − E_Qψ − α ≤ ε` (the upper bound: `Wave30tv.Claims.lem_ramp_iii`). (G) any quantiles
`u < t`, no (A3); (Pr) at the printed `t⋆`, `u⋆` under Assumption 2.1. Encoding: `γ > 0`. The instance "under the hypotheses of
Proposition 5.5" is a composition owned by 31tq. -/
def excess_ii : Prop :=
  (∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (φ : 𝒳 → H) (κ γ c₁ c₂ ε₀ ε : ℝ) (a b : H) (t u : ℝ),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
      0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      0 < γ → 0 < c₁ → 0 < c₂ → 0 < ε₀ → ε₀ ≤ StatFormal.Distances.tvDist P Q →
      (∀ e : ℝ, 0 < e → e ≤ ε₀ →
        c₁ * e ^ γ ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - e) ∧
          Dpop φ P Q (StatFormal.Distances.tvDist P Q - e) ≤ c₂ * e ^ γ) →
      0 < ε → ε ≤ ε₀ / 2 →
      a ∈ region φ (StatFormal.Distances.tvDist P Q - ε) P → b ∈ region φ (StatFormal.Distances.tvDist P Q - ε) Q →
      ‖a - b‖ = Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) →
      IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - (StatFormal.Distances.tvDist P Q - ε)) t →
      IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (StatFormal.Distances.tvDist P Q - ε) u → u < t →
        (1 - StatFormal.Distances.tvDist P Q) * c₁ * ε / (2 ^ γ * c₂) ≤
            (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
              (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - (StatFormal.Distances.tvDist P Q - ε) ∧
          (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
              (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - (StatFormal.Distances.tvDist P Q - ε) ≤ ε) ∧
  (∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (φ : 𝒳 → H) (κ γ c₁ c₂ ε₀ ε : ℝ) (a b : H) (t u : ℝ),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
      0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      0 < γ → 0 < c₁ → 0 < c₂ → 0 < ε₀ → ε₀ ≤ StatFormal.Distances.tvDist P Q →
      (∀ e : ℝ, 0 < e → e ≤ ε₀ →
        c₁ * e ^ γ ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - e) ∧
          Dpop φ P Q (StatFormal.Distances.tvDist P Q - e) ≤ c₂ * e ^ γ) →
      0 < ε → ε ≤ ε₀ / 2 →
      a ∈ region φ (StatFormal.Distances.tvDist P Q - ε) P → b ∈ region φ (StatFormal.Distances.tvDist P Q - ε) Q →
      ‖a - b‖ = Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) →
      IsLeast {q | IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - (StatFormal.Distances.tvDist P Q - ε)) q} t →
      IsGreatest {q | IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (StatFormal.Distances.tvDist P Q - ε) q} u →
        (1 - StatFormal.Distances.tvDist P Q) * c₁ * ε / (2 ^ γ * c₂) ≤
            (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
              (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - (StatFormal.Distances.tvDist P Q - ε) ∧
          (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
              (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - (StatFormal.Distances.tvDist P Q - ε) ≤ ε)

/-- T42 (a)–(c), (G) ∧ (Pr) (Proposition 5.10 `prop:excess` (iii), main :283-284; proof S4 :966-975; remark S4 :978-979): for the Laplace kernel
on `ℝ` (`⟪φ x, φ y⟫ = e^{−|x−y|/σ}`, `σ > 0`): (a) `u ≤ f⋆(x) ≤ t` for every `x ∈ ℝ`; (b) the first inequality of (i) is an equality,
`E_Pψ − E_Qψ − α = (1−α)D_α/(t − u)`; (c) "the witness is therefore flat on the set it trims from each law", `P({f⋆ = t}) ≥ α` and
`Q({f⋆ = u}) ≥ α`. (G) any quantiles `u < t`, no (A3); (Pr) at the printed `u⋆ < t⋆` under Assumption 2.1. `‖φ x‖ = 1` follows from
the Gram function, so no bound `κ` is assumed (as in `laplace_qdens_fails`). -/
def excess_laplace : Prop :=
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (σ : ℝ) (φ : ℝ → H) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (α : ℝ) (a b : H) (t u : ℝ),
      0 < σ → StronglyMeasurable φ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) →
      0 ≤ α → α < 1 → 0 < Dpop φ P Q α →
      a ∈ region φ α P → b ∈ region φ α Q → ‖a - b‖ = Dpop φ P Q α →
      IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) t →
      IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α u → u < t →
        (∀ x : ℝ, u ≤ ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ ∧ ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ ≤ t) ∧
        (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
            (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - α =
          (1 - α) * Dpop φ P Q α / (t - u) ∧
        α ≤ P.real {x | ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ = t} ∧
        α ≤ Q.real {y | ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ = u}) ∧
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (σ : ℝ) (φ : ℝ → H) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (α : ℝ) (a b : H) (t u : ℝ),
      0 < σ → StronglyMeasurable φ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) → Characteristic φ →
      0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      0 ≤ α → α < StatFormal.Distances.tvDist P Q →
      a ∈ region φ α P → b ∈ region φ α Q → ‖a - b‖ = Dpop φ P Q α →
      IsLeast {q | IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) q} t →
      IsGreatest {q | IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α q} u →
        (∀ x : ℝ, u ≤ ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ ∧ ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ ≤ t) ∧
        (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
            (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - α =
          (1 - α) * Dpop φ P Q α / (t - u) ∧
        α ≤ P.real {x | ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ = t} ∧
        α ≤ Q.real {y | ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ = u})

/-- T42 (d) (library; S4 :967, "`(1 − σ²∂²_x)e^{−|x|/σ} = 2σδ₀` in the sense of distributions"): for `σ > 0`, every `C²` function
`ψ : ℝ → ℝ` with compact support has `∫ e^{−|x|/σ}(ψ(x) − σ²ψ″(x)) dx = 2σψ(0)`; and the discrete form used by the proof of (iii):
with `k(x,y) = e^{−|x−y|/σ}`, for all `x, y` and `h > 0`, `k(x+h,y) + k(x−h,y) − 2k(x,y) ≤ 2(cosh(h/σ) − 1)k(x,y)`, with equality when
`|x − y| ≥ h`. -/
def laplace_green : Prop :=
  ∀ σ : ℝ, 0 < σ →
    (∀ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      ∫ x, Real.exp (-|x| / σ) * (ψ x - σ ^ 2 * deriv (deriv ψ) x) = 2 * σ * ψ 0) ∧
    ∀ x y h : ℝ, 0 < h →
      Real.exp (-|x + h - y| / σ) + Real.exp (-|x - h - y| / σ) - 2 * Real.exp (-|x - y| / σ) ≤
          2 * (Real.cosh (h / σ) - 1) * Real.exp (-|x - y| / σ) ∧
        (h ≤ |x - y| →
          Real.exp (-|x + h - y| / σ) + Real.exp (-|x - h - y| / σ) - 2 * Real.exp (-|x - y| / σ) =
            2 * (Real.cosh (h / σ) - 1) * Real.exp (-|x - y| / σ))

/-! ### A fixed kernel is blind to fast oscillation (T45) -/

/-- T45 (a)–(c) (S4 :1531-1537; main :349-351): for any kernel satisfying (A1)–(A2), with `𝒳 = ℝ` and laws carried by `[0,1]` (as
`Wave31ta.Density2`; a kernel given on `[0,1]` only extends to `ℝ` by `φ(x) := φ(min(max(x,0),1))` with the same constants), the uniform law
`P_u = λ|_{[0,1]}` and `Q_ν = oscLaw ς ν` (density `1 + ς(ν·)` on `[0,1]`) for a measurable 1-periodic `ς` with `∫₀¹ς = 0` and `|ς| = 1`:
(a) for every integer `ν ≥ 1`, `Q_ν` is a probability measure and `TV(P_u, Q_ν) = ½`; (b) `‖μ_{Q_ν} − μ_{P_u}‖ → 0` as `ν → ∞`
(Riemann–Lebesgue for Bochner integrals); (c) `D_α(P_u, Q_ν) ≤ MMD(P_u, Q_ν) = ‖μ_{P_u} − μ_{Q_ν}‖` (`Wave30tj.mmd`) for every
`α ∈ [0,1)` and `ν ≥ 1`, and `sup_{α ∈ [0,1)} D_α(P_u, Q_ν) → 0` (stated uniformly in `α`, without an `iSup`). -/
def oscillation_blind : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (κ : ℝ) (ς : ℝ → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    Measurable ς → Function.Periodic ς 1 → ∫ x in (0 : ℝ)..1, ς x = 0 → (∀ x, |ς x| = 1) →
      (∀ ν : ℕ, 1 ≤ ν → IsProbabilityMeasure (oscLaw ς ν) ∧
          StatFormal.Distances.tvDist (volume.restrict (Icc (0 : ℝ) 1)) (oscLaw ς ν) = 1 / 2) ∧
        Filter.Tendsto (fun ν : ℕ => ‖∫ x, φ x ∂(oscLaw ς ν) - ∫ x, φ x ∂(volume.restrict (Icc (0 : ℝ) 1))‖)
          Filter.atTop (nhds 0) ∧
        (∀ ν : ℕ, 1 ≤ ν → ∀ α ∈ Ico (0 : ℝ) 1,
          Dpop φ (volume.restrict (Icc (0 : ℝ) 1)) (oscLaw ς ν) α ≤
            ‖∫ x, φ x ∂(volume.restrict (Icc (0 : ℝ) 1)) - ∫ x, φ x ∂(oscLaw ς ν)‖) ∧
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν → ∀ α ∈ Ico (0 : ℝ) 1,
          Dpop φ (volume.restrict (Icc (0 : ℝ) 1)) (oscLaw ς ν) α ≤ ε

/-! ### T13 — Remark S5.5 at `d = 1` for the Gaussian kernel -/

/-- T13 (a) (S5 :274-284, proof :286-295): `qdens_formula` for the Gaussian kernel on `ℝ`, with no hypothesis on the witness: for
`⟪φ x, φ y⟫ = exp(−(x−y)²/(2σ²))`, `σ > 0`, any `g ∈ ℋ` and `h = ⟪g, φ ·⟫`, the conclusions of `Wave31tc.Claims.qdens_formula` hold
(its hypotheses "`h` is `C¹`" and "`h → 0` at `±∞`" discharged). -/
def gauss_qdens_formula : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (σ : ℝ) (φ : ℝ → H) (g : H)
    (p : ℝ → ℝ) (U : Set ℝ) (t : ℝ),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) →
    t ≠ 0 → (∃ x, StatFormal.Wave12c.witFn g φ x = t) →
    (∀ x, StatFormal.Wave12c.witFn g φ x = t → deriv (StatFormal.Wave12c.witFn g φ) x ≠ 0) →
    IsOpen U → {x | StatFormal.Wave12c.witFn g φ x = t} ⊆ U → ContinuousOn p U →
    (∀ x, StatFormal.Wave12c.witFn g φ x = t → 0 < p x) →
      {x | StatFormal.Wave12c.witFn g φ x = t}.Finite ∧
      ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ c ≤ C ∧
        (∀ x, StatFormal.Wave12c.witFn g φ x ∈ Icc (t - r) (t + r) → deriv (StatFormal.Wave12c.witFn g φ) x ≠ 0) ∧
        (∀ s ∈ Icc (t - r) (t + r), {x | StatFormal.Wave12c.witFn g φ x = s}.Finite ∧
          c ≤ StatFormal.Wave31tc.levelDens (StatFormal.Wave12c.witFn g φ) p s ∧
          StatFormal.Wave31tc.levelDens (StatFormal.Wave12c.witFn g φ) p s ≤ C) ∧
        ContinuousOn (StatFormal.Wave31tc.levelDens (StatFormal.Wave12c.witFn g φ) p) (Icc (t - r) (t + r)) ∧
        ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (t - r) (t + r) →
          (volume.withDensity fun x => ENNReal.ofReal (p x)) (StatFormal.Wave12c.witFn g φ ⁻¹' A) =
            ∫⁻ s in A, ENNReal.ofReal (StatFormal.Wave31tc.levelDens (StatFormal.Wave12c.witFn g φ) p s)

/-- T13 (b) (S5 :274-284): `qdens_Q_Qprime` for the Gaussian kernel on `ℝ` and any `d⋆ ∈ ℋ`: if `P = p·λ` satisfies the level-set
conditions at `t_α ≠ 0` and `Q = q·λ` at `u_α ≠ 0`, then (Q) and (Q′) hold with one common half-width (`Wave31tc.Claims.qdens_Q_Qprime`
with its `C¹` and decay hypotheses discharged). -/
def gauss_qdens_Q_Qprime : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (σ : ℝ) (φ : ℝ → H) (dstar : H)
    (p q : ℝ → ℝ) (U V : Set ℝ) (tα uα : ℝ),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) →
    tα ≠ 0 → (∃ x, StatFormal.Wave12c.witFn dstar φ x = tα) →
    (∀ x, StatFormal.Wave12c.witFn dstar φ x = tα → deriv (StatFormal.Wave12c.witFn dstar φ) x ≠ 0) →
    IsOpen U → {x | StatFormal.Wave12c.witFn dstar φ x = tα} ⊆ U → ContinuousOn p U →
    (∀ x, StatFormal.Wave12c.witFn dstar φ x = tα → 0 < p x) →
    uα ≠ 0 → (∃ y, StatFormal.Wave12c.witFn dstar φ y = uα) →
    (∀ y, StatFormal.Wave12c.witFn dstar φ y = uα → deriv (StatFormal.Wave12c.witFn dstar φ) y ≠ 0) →
    IsOpen V → {y | StatFormal.Wave12c.witFn dstar φ y = uα} ⊆ V → ContinuousOn q V →
    (∀ y, StatFormal.Wave12c.witFn dstar φ y = uα → 0 < q y) →
      ∃ rQ cf Cf cf' : ℝ, 0 < rQ ∧ 0 < cf ∧ cf ≤ Cf ∧ 0 < cf' ∧
        StatFormal.Wave12c.QDensity (volume.withDensity fun x => ENNReal.ofReal (p x))
          (StatFormal.Wave12c.witFn dstar φ) tα rQ cf Cf ∧
        StatFormal.Wave12c.QDensityLower (volume.withDensity fun y => ENNReal.ofReal (q y))
          (StatFormal.Wave12c.witFn dstar φ) uα rQ cf'

/-! ### T15–T17 — the witness fitted at `α = 0` -/

/-- T15 (S3 :364, "… and tend to `f₀` uniformly, almost surely"): `X₁, X₂, …` pairwise independent with law `P`, `Y₁, Y₂, …` pairwise
independent with law `Q` (no assumption between the sequences), `ℋ` complete separable (Borel), `φ` strongly measurable, `‖φ‖ ≤ κ`,
`MMD(P,Q) > 0`. Almost surely, the witness of every exact minimizer of `eq:qp` at `α = 0` on the prefixes `X_{1:n}`, `Y_{1:m}` tends to
`f₀ = ⟪(μ_P − μ_Q)/‖μ_P − μ_Q‖, φ ·⟫` uniformly on `𝒳` as `n, m → ∞`; and so do the witnesses fitted on prefixes of sizes
`a(n,m), b(n,m) → ∞` (the fitting samples of the batches). -/
def alpha0_fit_uniform_as : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (Ω : Type) [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X Y : ℕ → Ω → 𝒳) (φ : 𝒳 → H) (κ : ℝ),
    (∀ i, Measurable (X i)) → (∀ j, Measurable (Y j)) →
    Pairwise (fun i j => ProbabilityTheory.IndepFun (X i) (X j) ℙ) →
    Pairwise (fun i j => ProbabilityTheory.IndepFun (Y i) (Y j) ℙ) →
    (∀ i, ℙ.map (X i) = P) → (∀ j, ℙ.map (Y j) = Q) →
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < ‖(∫ x, φ x ∂P) - ∫ x, φ x ∂Q‖ →
      ∀ᵐ ω ∂ℙ,
        (∀ ε > 0, ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m →
          ∀ (w : Fin n → ℝ) (v : Fin m → ℝ),
            IsQPMin φ 0 (fun i : Fin n => X i ω) (fun j : Fin m => Y j ω) w v →
              ∀ z, |⟪StatFormal.Wave30tz.witness φ (fun i : Fin n => X i ω) (fun j : Fin m => Y j ω) w v, φ z⟫_ℝ -
                ⟪(‖(∫ x, φ x ∂P) - ∫ x, φ x ∂Q‖)⁻¹ • ((∫ x, φ x ∂P) - ∫ x, φ x ∂Q), φ z⟫_ℝ| ≤ ε) ∧
        ∀ (a b : ℕ → ℕ → ℕ), (∀ K : ℕ, ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m → K ≤ a n m ∧ K ≤ b n m) →
          ∀ ε > 0, ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m →
            ∀ (w : Fin (a n m) → ℝ) (v : Fin (b n m) → ℝ),
              IsQPMin φ 0 (fun i : Fin (a n m) => X i ω) (fun j : Fin (b n m) => Y j ω) w v →
                ∀ z, |⟪StatFormal.Wave30tz.witness φ (fun i : Fin (a n m) => X i ω) (fun j : Fin (b n m) => Y j ω) w v,
                    φ z⟫_ℝ -
                  ⟪(‖(∫ x, φ x ∂P) - ∫ x, φ x ∂Q‖)⁻¹ • ((∫ x, φ x ∂P) - ∫ x, φ x ∂Q), φ z⟫_ℝ| ≤ ε

/-- T16 (a) (S3 :374-377): for laws concentrated on a finite set `S` (measurable singletons), `f₀` measurable and injective on `S`, and
`0 < g₀` at most every gap `|f₀ a − f₀ b|` (`a ≠ b ∈ S`), every measurable `f` within `g₀/2` of `f₀` on `S` has `KS⁺(f) = KS⁺(f₀)`. -/
def ksPlus_locally_constant : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (S : Finset 𝒳) (f₀ : 𝒳 → ℝ) (g₀ : ℝ),
    P (↑S : Set 𝒳)ᶜ = 0 → Q (↑S : Set 𝒳)ᶜ = 0 → Measurable f₀ → Set.InjOn f₀ ↑S → 0 < g₀ →
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → g₀ ≤ |f₀ a - f₀ b|) →
      ∀ f : 𝒳 → ℝ, Measurable f → (∀ a ∈ S, |f a - f₀ a| < g₀ / 2) → ksPlus P Q f = ksPlus P Q f₀

/-- T16 (b) (S3 :374-377, "So the 24 values of `f₀` are distinct … and `KS⁺(f̂_{0,b}) = KS⁺(f₀) = 0.4` once `f̂_{0,b}` is uniformly within
half the smallest gap of these values"): `f₀ = exWitness exP exQ` takes 24 distinct values on the 24 atoms, `KS⁺(f₀) = 2/5`, and every
`f` within `g₀/2` of `f₀` on the atoms, for any `0 < g₀` at most every gap (the smallest gap is one), has `KS⁺(f) = 2/5`. -/
def ex_ks_stable : Prop :=
  exAtoms.card = 24 ∧ Set.InjOn (exWitness exP exQ) ↑exAtoms ∧ ksPlus exP exQ (exWitness exP exQ) = 2 / 5 ∧
    ∀ g₀ : ℝ, 0 < g₀ → (∀ a ∈ exAtoms, ∀ b ∈ exAtoms, a ≠ b → g₀ ≤ |exWitness exP exQ a - exWitness exP exQ b|) →
      ∀ f : ℝ → ℝ, (∀ a ∈ exAtoms, |f a - exWitness exP exQ a| < g₀ / 2) → ksPlus exP exQ f = 2 / 5

/-- T17 (a) (S3 :377, "so every level `α ≥ 0.4` is rejected with probability at most `δ + o(1)`"): the laws `exP`, `exQ`, any feature map
`φ : ℝ → ℋ` (complete separable) with the Gaussian Gram (`σ = 1`), runs with `IsAdmissible α λ_max` and `IsSizedRun c C₀ B` (`c > 0`)
whose ramp at every batch holding a pair with nonempty fitting sides is `h_b ∘ f̂_{0,b}` for some nondecreasing `h_b : ℝ → [0,1]` (any
cut points). For every level `α_j ≥ 2/5` and `ε > 0`, eventually `P(reject H_{0,α_j}) ≤ δ + ε`. -/
def alpha0_reject_le : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (J : ℕ) (α : Fin J → ℝ) (δ lmax c C0 : ℝ) (Bmax : ℕ) (R : ∀ n m : ℕ, LoRun ℝ J n m),
    (∀ a x, ⟪φ a, φ x⟫_ℝ = Real.exp (-(a - x) ^ 2 / 2)) → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 → 0 < c →
    (∀ n m, (R n m).IsAdmissible α lmax ∧ (R n m).IsSizedRun c C0 Bmax) →
    (∀ (n m : ℕ) (j : Fin J) (k : Fin (R n m).N) (x : Fin n → ℝ) (y : Fin m → ℝ),
      1 ≤ fitCard (R n m).lx ((R n m).bat k) → 1 ≤ fitCard (R n m).ly ((R n m).bat k) →
        ∃ h : ℝ → ℝ, Monotone h ∧ (∀ s, h s ∈ Icc (0 : ℝ) 1) ∧
          (R n m).g j ((R n m).bat k) x y = fun z => h (alphaZeroFn φ (R n m).lx (R n m).ly ((R n m).bat k) x y z)) →
      ∀ j, 2 / 5 ≤ α j → ∀ ε > 0, ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m →
        sampleLaw exP exQ n m {ω | rejects ((R n m).lam j) ((R n m).g j) (R n m).bat (R n m).A (R n m).B (α j) δ ω.1 ω.2} ≤
          ENNReal.ofReal (δ + ε)

/-- T17 (b) (S3 :377, §4 :162-165 "need not be consistent"): under the hypotheses of (a) on a grid, `α⋆ = 3/5`, and for a level
`α_i ∈ [2/5, 3/5)`, eventually `P(α̂ ≥ α_i) ≤ δ + ε`; hence `P(α̂ ≥ α_i)` does not tend to `1` (the lower bound is not consistent),
although `α_i < α⋆`. -/
def alpha0_inconsistent : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ℝ → H) (J : ℕ) (α : Fin J → ℝ) (δ lmax c C0 : ℝ) (Bmax : ℕ) (R : ∀ n m : ℕ, LoRun ℝ J n m),
    (∀ a x, ⟪φ a, φ x⟫_ℝ = Real.exp (-(a - x) ^ 2 / 2)) → IsGrid α → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 → 0 < c →
    (∀ n m, (R n m).IsAdmissible α lmax ∧ (R n m).IsSizedRun c C0 Bmax) →
    (∀ (n m : ℕ) (j : Fin J) (k : Fin (R n m).N) (x : Fin n → ℝ) (y : Fin m → ℝ),
      1 ≤ fitCard (R n m).lx ((R n m).bat k) → 1 ≤ fitCard (R n m).ly ((R n m).bat k) →
        ∃ h : ℝ → ℝ, Monotone h ∧ (∀ s, h s ∈ Icc (0 : ℝ) 1) ∧
          (R n m).g j ((R n m).bat k) x y = fun z => h (alphaZeroFn φ (R n m).lx (R n m).ly ((R n m).bat k) x y z)) →
      StatFormal.Distances.tvDist exP exQ = 3 / 5 ∧
      ∀ i, 2 / 5 ≤ α i → α i < 3 / 5 →
        (∀ ε > 0, ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m →
          sampleLaw exP exQ n m {ω | α i ≤ (R n m).alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal (δ + ε)) ∧
        ¬ (∀ ε > 0, ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m →
          ENNReal.ofReal (1 - ε) ≤ sampleLaw exP exQ n m {ω | α i ≤ (R n m).alphaLo α δ ω.1 ω.2})

/-- T17 (c) (S3 :364-368, the printed predictability step): for runs whose ramp at every batch holding a pair is `h_b ∘ f̂_{0,b}`
(`h_b` nondecreasing, `[0,1]`-valued), fixed laws `P, Q` and (A1)–(A2): for every batch `b`, `(x, y) ↦ KS⁺_{P,Q}(f̂_{0,b}(x, y))` is
measurable and a function of the batches before `b`; the gated fractions `λ′ = λ·1{KS⁺(f̂_{0,bat k}) ≤ α}` are admissible; the
certificate with `λ′` coincides with the one with `λ` on `{max_b KS⁺(f̂_{0,b}) ≤ α}`; the certificate with `λ′` rejects `H_{0,α}` with
probability at most `δ` (its wealth is a nonnegative supermartingale); hence the one with `λ` rejects with probability at most
`δ + P(max_b KS⁺(f̂_{0,b}) > α)`, for every pair. -/
def alpha0_gate : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n m N : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m))
    (α δ c : ℝ) (g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ)
    (lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsBatchPairing lx ly bat A B → 0 ≤ α → 0 < δ → δ < 1 → 0 < c → c ≤ 1 →
    IsFitRule lx ly bat g → IsFracRule lx ly bat α c lam →
    (∀ (k : Fin N) (x : Fin n → 𝒳) (y : Fin m → 𝒳), ∃ h : ℝ → ℝ, Monotone h ∧ (∀ s, h s ∈ Icc (0 : ℝ) 1) ∧
      g (bat k) x y = fun z => h (alphaZeroFn φ lx ly (bat k) x y z)) →
      (∀ b : ℕ, Measurable (fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => ksPlus P Q (alphaZeroFn φ lx ly b p.1 p.2)) ∧
        ∀ (x x' : Fin n → 𝒳) (y y' : Fin m → 𝒳), (∀ i, lx i < b → x i = x' i) → (∀ j, ly j < b → y j = y' j) →
          ksPlus P Q (alphaZeroFn φ lx ly b x y) = ksPlus P Q (alphaZeroFn φ lx ly b x' y')) ∧
      IsFracRule lx ly bat α c (ksGate P Q φ lx ly bat α lam) ∧
      (∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), (∀ k : Fin N, ksPlus P Q (alphaZeroFn φ lx ly (bat k) x y) ≤ α) →
        (∀ k : Fin N, fracAt (ksGate P Q φ lx ly bat α lam) g bat A B x y k = fracAt lam g bat A B x y k) ∧
        (rejects (ksGate P Q φ lx ly bat α lam) g bat A B α δ x y ↔ rejects lam g bat A B α δ x y)) ∧
      sampleLaw P Q n m {ω | rejects (ksGate P Q φ lx ly bat α lam) g bat A B α δ ω.1 ω.2} ≤ ENNReal.ofReal δ ∧
      sampleLaw P Q n m {ω | rejects lam g bat A B α δ ω.1 ω.2} ≤
        ENNReal.ofReal δ + sampleLaw P Q n m {ω | ∃ k : Fin N, α < ksPlus P Q (alphaZeroFn φ lx ly (bat k) ω.1 ω.2)}

/-! ### T26 — the any-threshold converse -/

/-- T26 (S4 :876-879, "For any threshold `τ`, valid and nondecreasing, the same argument gives `α̂_an ≤ α⋆ − ε` on `E⁺` whenever …"):
(A1)–(A2), `‖φ x − φ x′‖ ≤ D`, `α⋆ < 1`, `δ′ ∈ (0,1)`, `n, m ≥ 1`. One measurable event `E⁺` of probability `≥ 1 − δ′` serves every
`τ : ℝ → ℝ` (no validity or monotonicity needed): on `E⁺`, for every `ε ∈ [0, α⋆]` with `D_{α⋆−ε} + τ^A(α⋆−ε, δ′) ≤ τ(α⋆−ε)`,
`α̂_an = alphaHat(D̂, τ) ≤ α⋆ − ε`. -/
def any_threshold_converse : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (δ' : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
      ∃ Eplus : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet Eplus ∧
        ENNReal.ofReal (1 - δ') ≤ sampleLaw P Q n m Eplus ∧
        ∀ (τ : ℝ → ℝ), ∀ z ∈ Eplus, ∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
          Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) +
              StatFormal.Wave30tr.tauA κ D (StatFormal.Distances.tvDist P Q - ε) δ' n m ≤
            τ (StatFormal.Distances.tvDist P Q - ε) →
          alphaHat (Demp φ z.1 z.2) τ ≤ StatFormal.Distances.tvDist P Q - ε

/-! ### T27 — `prop:bangbang` in the AoS wording -/

open Classical in
open scoped Pointwise in
/-- T27 (§2 :203-220): `prop:bangbang` in the AoS wording. Parts (i), (iii) and the first sentence are those of `Wave31ta.bangbang_v2`
verbatim; (ii) reads with `t̂_n ∈ (−∞, +∞]` the `(n_α+1)`-th smallest of the `d̂(X_i)` if `n_α = ⌊n(1−α)⌋ < n` and `+∞` if `n_α = n`
(`EReal`): `w_i = β/n` (`= cap n α`) when `d̂(X_i) < t̂_n`, `w_i = 0` when `d̂(X_i) > t̂_n`, and the ties share
`1 − (β/n)#{i : d̂(X_i) < t̂_n}`; symmetrically with `ŝ_m ∈ [−∞, +∞)` the `(m_α+1)`-th largest of the `d̂(Y_j)` (`−∞` if `m_α = m`). At
`n_α = n` the tie clause is the true empty statement, not omitted. `d̂ = Σ w_iφ(X_i) − Σ v_jφ(Y_j)` unnormalized (`Wave4b.witness`). -/
def bangbang_aos : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (α : ℝ) (n m : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳),
    StronglyMeasurable φ → 0 ≤ α → α < 1 → 1 ≤ n → 1 ≤ m →
      let T : Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
        {p | p ∈ capped n α ×ˢ capped m α ∧
          IsMinOn (qp (fun i => φ (x i)) (fun j => φ (y j))) (capped n α ×ˢ capped m α) p}
      (T.Nonempty ∧ Convex ℝ T ∧ IsCompact T) ∧
      (∀ p ∈ T, StatFormal.TrimmedMMD.Projection.IsMinNorm (region φ α (empirical x) - region φ α (empirical y))
          (StatFormal.Wave4b.witness φ x y p) ∧
        ‖StatFormal.Wave4b.witness φ x y p‖ = Demp φ x y α) ∧
      (∀ p ∈ T, ∀ p' ∈ T, StatFormal.Wave4b.witness φ x y p = StatFormal.Wave4b.witness φ x y p') ∧
      (0 < Demp φ x y α → ∀ p ∈ T,
        let dx : Fin n → ℝ := fun i => ⟪StatFormal.Wave4b.witness φ x y p, φ (x i)⟫_ℝ
        let dy : Fin m → ℝ := fun j => ⟪StatFormal.Wave4b.witness φ x y p, φ (y j)⟫_ℝ
        let tn : EReal := if kfloor n α < n then ((ord dx (kfloor n α) : ℝ) : EReal) else ⊤
        let sm : EReal := if kfloor m α < m then ((ord dy (m - kfloor m α - 1) : ℝ) : EReal) else ⊥
        (∀ i, ((dx i : ℝ) : EReal) < tn → p.1 i = cap n α) ∧
        (∀ i, tn < ((dx i : ℝ) : EReal) → p.1 i = 0) ∧
        ∑ i ∈ Finset.univ.filter (fun i => ((dx i : ℝ) : EReal) = tn), p.1 i =
          1 - cap n α * (Finset.univ.filter (fun i => ((dx i : ℝ) : EReal) < tn)).card ∧
        (∀ j, sm < ((dy j : ℝ) : EReal) → p.2 j = cap m α) ∧
        (∀ j, ((dy j : ℝ) : EReal) < sm → p.2 j = 0) ∧
        ∑ j ∈ Finset.univ.filter (fun j => ((dy j : ℝ) : EReal) = sm), p.2 j =
          1 - cap m α * (Finset.univ.filter (fun j => sm < ((dy j : ℝ) : EReal))).card) ∧
      (Demp φ x y α = 0 →
        T = {p | p ∈ capped n α ×ˢ capped m α ∧ ∑ i, p.1 i • φ (x i) = ∑ j, p.2 j • φ (y j)})

/-! ### T28 — `TV` is a one-sided Kolmogorov distance -/

/-- T28 (a) (main :320-322, §1 :86-88): `P, Q` on `ℝ` with Lebesgue densities `p, q`, `p ≥ q` a.e. on `(x₀, ∞)` and `p ≤ q` a.e. on
`(−∞, x₀)` (the sign hypotheses of `prop:newsobolev`). Then `TV(P,Q) = P((x₀,∞)) − Q((x₀,∞)) = F_Q(x₀) − F_P(x₀)
= sup_x {Q((−∞,x]) − P((−∞,x])} = KS⁺_{P,Q}(id)`. -/
def tv_one_sided_ks : Prop :=
  ∀ (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : ℝ → ℝ) (x₀ : ℝ),
    Measurable p → Measurable q →
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) → Q = volume.withDensity (fun x => ENNReal.ofReal (q x)) →
    (∀ᵐ x ∂volume, x₀ < x → q x ≤ p x) → (∀ᵐ x ∂volume, x < x₀ → p x ≤ q x) →
      StatFormal.Distances.tvDist P Q = P.real (Ioi x₀) - Q.real (Ioi x₀) ∧
      StatFormal.Distances.tvDist P Q = Q.real (Iic x₀) - P.real (Iic x₀) ∧
      StatFormal.Distances.tvDist P Q = ⨆ x : ℝ, (Q.real (Iic x) - P.real (Iic x)) ∧
      StatFormal.Distances.tvDist P Q = ksPlus P Q id

/-- T28 (b) (main :320-322 "which the one-sided Kolmogorov–Smirnov statistic bounds from below at the rate `(n∧m)^{−1/2}`, with no
condition on the likelihood ratio and no logarithmic factor"; §1 :86-87): for every pair on `ℝ`, `n, m ≥ 1`, `δ ∈ (0,1)`, with
`K̂ = KS⁺_{P_n,Q_m}(id)`, `t_k = √(log(2/δ)/(2k))` and `L̂ = K̂ − t_n − t_m`: `P(L̂ ≤ KS⁺) ≥ 1 − δ`; `KS⁺ ≤ TV` always (so `L̂` is a valid
lower confidence bound on `TV` for every pair); with probability `≥ 1 − 2δ`, `L̂ ≤ KS⁺ ≤ L̂ + 2(t_n + t_m)`; and the error term is at most
`4√(log(2/δ)/2) (n∧m)^{−1/2}` (no factor in `n, m` beyond `(n∧m)^{−1/2}`). Under (a), `KS⁺ = TV`. -/
def ks_lower_confidence : Prop :=
  ∀ (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n m : ℕ) (δ : ℝ),
    1 ≤ n → 1 ≤ m → 0 < δ → δ < 1 →
      (∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m E ∧
        ∀ ω ∈ E, ksPlus (empirical ω.1) (empirical ω.2) id - ksRadius δ n - ksRadius δ m ≤ ksPlus P Q id) ∧
      ksPlus P Q id ≤ StatFormal.Distances.tvDist P Q ∧
      (∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m E ∧
        ∀ ω ∈ E, ksPlus (empirical ω.1) (empirical ω.2) id - ksRadius δ n - ksRadius δ m ≤
          StatFormal.Distances.tvDist P Q) ∧
      (∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧ ENNReal.ofReal (1 - 2 * δ) ≤ sampleLaw P Q n m E ∧
        ∀ ω ∈ E, ksPlus (empirical ω.1) (empirical ω.2) id - ksRadius δ n - ksRadius δ m ≤ ksPlus P Q id ∧
          ksPlus P Q id ≤ ksPlus (empirical ω.1) (empirical ω.2) id - ksRadius δ n - ksRadius δ m +
            2 * (ksRadius δ n + ksRadius δ m)) ∧
      2 * (ksRadius δ n + ksRadius δ m) ≤ 4 * √(Real.log (2 / δ) / 2) / √((min n m : ℕ) : ℝ)

/-! ### T29 — Proposition 5.3's last sentence and the class of `cor:minimax` -/

/-- T29 (a) (main :68-70; §1 :80-82, main :33-35): `𝒳 = U` a connected open subset of `ℝ^d` (subtype, Borel sets), `P ≠ Q` probability
measures on `U` with Lebesgue densities `p, q` continuous (and nonnegative) on `U`, `{x ∈ U : p(x) = q(x)}` with empty interior. Then
`supp P₀ ∩ supp Q₀ ≠ ∅` (`P₀ = P − P⊓Q`, `Q₀ = Q − P⊓Q`, supports in `U`). Hence, if `α⋆ < 1`, for every continuous (A1)–(A2) feature
map the limit of `(1−α⋆+ε)D_{α⋆−ε}/ε` as `ε ↓ 0`, where it exists, is `0`, and no `c₀` gives `PolyMargin φ P Q c₀ 1` (the conclusion of
`Wave31to.Claims.newslope_b`). -/
def contact_densities : Prop :=
  ∀ (d : ℕ) (U : Set (EuclideanSpace ℝ (Fin d))) (p q : EuclideanSpace ℝ (Fin d) → ℝ) (P Q : Measure ↥U)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    IsOpen U → IsConnected U → ContinuousOn p U → ContinuousOn q U → (∀ x ∈ U, 0 ≤ p x) → (∀ x ∈ U, 0 ≤ q x) →
    P = (Measure.comap Subtype.val volume).withDensity (fun x => ENNReal.ofReal (p x)) →
    Q = (Measure.comap Subtype.val volume).withDensity (fun x => ENNReal.ofReal (q x)) →
    P ≠ Q → interior {x | x ∈ U ∧ p x = q x} = ∅ →
      ((P - P ⊓ Q).support ∩ (Q - P ⊓ Q).support).Nonempty ∧
      (StatFormal.Distances.tvDist P Q < 1 →
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
          (φ : ↥U → H) (κ : ℝ), StronglyMeasurable φ → Continuous φ → (∀ x, ‖φ x‖ ≤ κ) →
            (∀ s : ℝ, Filter.Tendsto (fun e => (1 - StatFormal.Distances.tvDist P Q + e) *
                Dpop φ P Q (StatFormal.Distances.tvDist P Q - e) / e) (nhdsWithin 0 (Set.Ioi 0)) (nhds s) → s = 0) ∧
            ¬ ∃ c₀ : ℝ, StatFormal.Wave31ti.PolyMargin φ P Q c₀ 1)

/-- T29 (b) (main :68-70): two finite mixtures of nondegenerate Gaussian laws on `ℝ^d` that are different measures satisfy (a) with
`U = ℝ^d` (probability measures with the continuous nonnegative densities `gaussMixDens`, equal densities on no open set), their
`α⋆ < 1`, and so the conclusions of (a) hold. -/
def contact_gauss_mix : Prop :=
  ∀ (d n n' : ℕ) (w : Fin n → ℝ) (μ : Fin n → EuclideanSpace ℝ (Fin d)) (S : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (w' : Fin n' → ℝ) (μ' : Fin n' → EuclideanSpace ℝ (Fin d)) (S' : Fin n' → Matrix (Fin d) (Fin d) ℝ),
    (∀ i, 0 < w i) → ∑ i, w i = 1 → (∀ i, (S i).PosDef) → (∀ i, 0 < w' i) → ∑ i, w' i = 1 → (∀ i, (S' i).PosDef) →
    StatFormal.Wave31tp.gaussMix w μ S ≠ StatFormal.Wave31tp.gaussMix w' μ' S' →
      IsProbabilityMeasure (StatFormal.Wave31tp.gaussMix w μ S) ∧ IsProbabilityMeasure (StatFormal.Wave31tp.gaussMix w' μ' S') ∧
      StatFormal.Wave31tp.gaussMix w μ S =
        volume.withDensity (fun x => ENNReal.ofReal (StatFormal.Wave31tp.gaussMixDens w μ S x)) ∧
      StatFormal.Wave31tp.gaussMix w' μ' S' =
        volume.withDensity (fun x => ENNReal.ofReal (StatFormal.Wave31tp.gaussMixDens w' μ' S' x)) ∧
      Continuous (StatFormal.Wave31tp.gaussMixDens w μ S) ∧ Continuous (StatFormal.Wave31tp.gaussMixDens w' μ' S') ∧
      (∀ x, 0 ≤ StatFormal.Wave31tp.gaussMixDens w μ S x) ∧ (∀ x, 0 ≤ StatFormal.Wave31tp.gaussMixDens w' μ' S' x) ∧
      interior {x | StatFormal.Wave31tp.gaussMixDens w μ S x = StatFormal.Wave31tp.gaussMixDens w' μ' S' x} = ∅ ∧
      StatFormal.Distances.tvDist (StatFormal.Wave31tp.gaussMix w μ S) (StatFormal.Wave31tp.gaussMix w' μ' S') < 1 ∧
      ((StatFormal.Wave31tp.gaussMix w μ S - StatFormal.Wave31tp.gaussMix w μ S ⊓ StatFormal.Wave31tp.gaussMix w' μ' S').support ∩
        (StatFormal.Wave31tp.gaussMix w' μ' S' -
          StatFormal.Wave31tp.gaussMix w μ S ⊓ StatFormal.Wave31tp.gaussMix w' μ' S').support).Nonempty ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
        (φ : EuclideanSpace ℝ (Fin d) → H) (κ : ℝ), StronglyMeasurable φ → Continuous φ → (∀ x, ‖φ x‖ ≤ κ) →
          (∀ s : ℝ, Filter.Tendsto (fun e =>
              (1 - StatFormal.Distances.tvDist (StatFormal.Wave31tp.gaussMix w μ S) (StatFormal.Wave31tp.gaussMix w' μ' S') + e) *
                Dpop φ (StatFormal.Wave31tp.gaussMix w μ S) (StatFormal.Wave31tp.gaussMix w' μ' S')
                  (StatFormal.Distances.tvDist (StatFormal.Wave31tp.gaussMix w μ S) (StatFormal.Wave31tp.gaussMix w' μ' S') - e) / e)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds s) → s = 0) ∧
          ¬ ∃ c₀ : ℝ, StatFormal.Wave31ti.PolyMargin φ (StatFormal.Wave31tp.gaussMix w μ S) (StatFormal.Wave31tp.gaussMix w' μ' S') c₀ 1

/-- T29 (c) (E9; main :222-224 "for a continuous kernel its contaminations are apart (Proposition 5.3)"): with a continuous (A1)–(A2)
feature map, every pair of the class `𝓜(a₀, a₁, c₀)` of `cor:minimax` (`0 < a₀`, `a₁ < 1`) has `supp P₀ ∩ supp Q₀ = ∅`; in particular,
on a connected open `𝒳 = U ⊆ ℝ^d`, no pair as in (a) belongs to `𝓜`. -/
def minimax_class_apart : Prop :=
  (∀ (𝒳 H : Type) [TopologicalSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ a₀ a₁ c₀ : ℝ) (P Q : Measure 𝒳),
      StronglyMeasurable φ → Continuous φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < a₀ → a₁ < 1 → InM φ a₀ a₁ c₀ P Q →
        (P - P ⊓ Q).support ∩ (Q - P ⊓ Q).support = ∅) ∧
  ∀ (d : ℕ) (U : Set (EuclideanSpace ℝ (Fin d))) (p q : EuclideanSpace ℝ (Fin d) → ℝ) (P Q : Measure ↥U)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : ↥U → H) (κ a₀ a₁ c₀ : ℝ),
    IsOpen U → IsConnected U → ContinuousOn p U → ContinuousOn q U → (∀ x ∈ U, 0 ≤ p x) → (∀ x ∈ U, 0 ≤ q x) →
    P = (Measure.comap Subtype.val volume).withDensity (fun x => ENNReal.ofReal (p x)) →
    Q = (Measure.comap Subtype.val volume).withDensity (fun x => ENNReal.ofReal (q x)) →
    P ≠ Q → interior {x | x ∈ U ∧ p x = q x} = ∅ →
    StronglyMeasurable φ → Continuous φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < a₀ → a₁ < 1 → ¬ InM φ a₀ a₁ c₀ P Q

/-! ### T32 — Assumption 2.1 gives the house encoding -/

/-- T32 (§2 :57-61, S1 :6 "By (A1) and (A2) …, `φ` is weakly measurable with `‖φ‖ ≤ κ`, hence Bochner integrable by Pettis' theorem, so
`E_P[gφ]` is well defined for bounded measurable `g`"): for any feature map `φ : 𝒳 → ℋ` into a real complete separable inner-product
space (Borel) whose Gram function `k(x,x′) = ⟪φ x, φ x′⟫` satisfies (A1) (`x ↦ k(x,x′)` measurable for every `x′`, `k(x,x) ≤ κ²`,
`κ ≥ 0`), `φ` is Borel measurable and strongly measurable with `‖φ x‖ ≤ κ`, and `g • φ` is Bochner integrable for every probability `P`
and bounded measurable `g`. In particular the canonical feature map `x ↦ k(x,·)` of an RKHS (Mathlib's `RKHS`, real-valued) satisfying
(A1)–(A2) satisfies the standing hypotheses "`φ` strongly measurable, `‖φ‖ ≤ κ`" of every certified trimmed-mmd claim. -/
def house_encoding : Prop :=
  (∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] (φ : 𝒳 → H) (κ : ℝ),
      0 ≤ κ → (∀ x', Measurable fun x => ⟪φ x, φ x'⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ ≤ κ ^ 2) →
        Measurable φ ∧ StronglyMeasurable φ ∧ (∀ x, ‖φ x‖ ≤ κ) ∧
        ∀ (P : Measure 𝒳) [IsProbabilityMeasure P] (g : 𝒳 → ℝ) (C : ℝ), Measurable g → (∀ x, |g x| ≤ C) →
          Integrable (fun x => g x • φ x) P) ∧
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H 𝒳 ℝ] (κ : ℝ),
    0 ≤ κ → (∀ x', Measurable fun x => RKHS.kernel H x x' (1 : ℝ)) → (∀ x, RKHS.kernel H x x (1 : ℝ) ≤ κ ^ 2) →
      StronglyMeasurable (fun x => RKHS.kerFun H x (1 : ℝ)) ∧ ∀ x, ‖RKHS.kerFun H x (1 : ℝ)‖ ≤ κ

/-! ### T35 — the constants of the Gaussian and the Laplace kernels -/

/-- T35 (§2 :47-50, "The Laplace kernel … and the Gaussian kernel … on `ℝ^d`, of bandwidth `σ`, both have `κ = 1` and `Δ_φ = √2`"): for
`d ≥ 1`, `σ > 0`, `g(r) = exp(−r²/(2σ²))` (Gaussian) or `g(r) = exp(−r/σ)` (Laplace), and any `φ : ℝ^d → ℋ` with
`⟪φ x, φ y⟫ = g(‖x − y‖)`: `‖φ x‖ = 1`; `‖φ x − φ y‖² = 2 − 2g(‖x−y‖) < 2`; `sup ‖φ x − φ y‖ = √2` (`IsLUB`), not attained.
Non-vacuity (docstring only, to keep 31tr independent of 31tp/31ts): a Gaussian feature map exists by 31tp L15 (Fourier feature map),
a Laplace one on `ℝ` by T42's explicit `L²` map, and on `ℝ^d` by Gaussian subordination (31ts U6(b)). -/
def kernel_constants : Prop :=
  ∀ (d : ℕ) (σ : ℝ) (g : ℝ → ℝ), 1 ≤ d → 0 < σ →
    (g = (fun r => Real.exp (-r ^ 2 / (2 * σ ^ 2))) ∨ g = (fun r => Real.exp (-r / σ))) →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : EuclideanSpace ℝ (Fin d) → H),
      (∀ x y, ⟪φ x, φ y⟫_ℝ = g ‖x - y‖) →
        (∀ x, ‖φ x‖ = 1) ∧
        (∀ x y, ‖φ x - φ y‖ ^ 2 = 2 - 2 * g ‖x - y‖ ∧ ‖φ x - φ y‖ ^ 2 < 2) ∧
        IsLUB (Set.range fun pr : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => ‖φ pr.1 - φ pr.2‖) (√2) ∧
        ∀ x y, ‖φ x - φ y‖ < √2

/-! ### T46 — a bound certified for a fitted function (§8 :9-12) -/

/-- T46 (a) (§8 :9-10, "`E_P f̂ − E_Q f̂ = α⋆ − err(f̂)`"): for a jointly measurable `[0,1]`-valued `F` of (batch 0, point), at every
sample `Δ = E_P f̂ − E_Q f̂ = α⋆ − err(f̂)`, `f̂ = F(batch 0)`, `err = Wave31to.errFn` (the certified `newapprox_err`). -/
def fncert_drift_err : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n m : ℕ)
    (lx : Fin n → ℕ) (ly : Fin m → ℕ) (F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ),
    Measurable (fun p : ((Fin (fitCard lx 1) → 𝒳) × (Fin (fitCard ly 1) → 𝒳)) × 𝒳 => F p.1.1 p.1.2 p.2) →
    (∀ u v z, F u v z ∈ Icc (0 : ℝ) 1) →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        fnDrift P Q lx ly F x y = StatFormal.Distances.tvDist P Q - errFn P Q (F (fitSample lx 1 x) (fitSample ly 1 y))

/-- T46 (b) (§8 :9-11, "certifies at most `E_P f̂ − E_Q f̂` …, except with probability `δ`, so a plug-in classifier falls short of `α⋆` by
at least `err(f̂)`, unless the bound is zero"): the single-function certificate (ramp `f̂ = F(batch 0)` at every batch and level; any
batch pairing; any admissible fractions with cap `c ≤ 1`; a grid `0 ≤ α_1 < ⋯ < α_J` read upward, `δ ∈ (0,1)`) has
`P(α̂ > max{Δ, 0}) ≤ δ`, conditionally on batch 0 (for every value of batch 0) and unconditionally. -/
def fncert_upper : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n m N J : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m))
    (α : Fin J → ℝ) (δ c : ℝ) (F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ)
    (lam : Fin J → (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ),
    IsBatchPairing lx ly bat A B → 0 < δ → δ < 1 → 0 < c → c ≤ 1 → StrictMono α → (∀ j, 0 ≤ α j) →
    Measurable (fun p : ((Fin (fitCard lx 1) → 𝒳) × (Fin (fitCard ly 1) → 𝒳)) × 𝒳 => F p.1.1 p.1.2 p.2) →
    (∀ u v z, F u v z ∈ Icc (0 : ℝ) 1) → (∀ j, IsFracRule lx ly bat (α j) c (lam j)) →
      (∀ (x₀ : Fin n → 𝒳) (y₀ : Fin m → 𝒳),
        sampleLaw P Q n m {ω | max (fnDrift P Q lx ly F x₀ y₀) 0 <
            fnAlpha lx ly bat A B F lam α δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)} ≤ ENNReal.ofReal δ) ∧
      sampleLaw P Q n m {ω | max (fnDrift P Q lx ly F ω.1 ω.2) 0 < fnAlpha lx ly bat A B F lam α δ ω.1 ω.2} ≤
        ENNReal.ofReal δ

/-- T46 (c) (§8 :9-11, "certifies at most `E_P f̂ − E_Q f̂` …, except with probability `δ`"): in the setting of (b),
`P(H_{0,α̂} is rejected ∧ Δ ≤ α̂) ≤ δ` ("`H_{0,α̂}` is rejected": `α̂` is a grid level whose test rejected, as in `Wave31ta.cor_lower_v2`),
conditionally on batch 0 and unconditionally. -/
def fncert_rejected_upper : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n m N J : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m))
    (α : Fin J → ℝ) (δ c : ℝ) (F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ)
    (lam : Fin J → (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ),
    IsBatchPairing lx ly bat A B → 0 < δ → δ < 1 → 0 < c → c ≤ 1 → StrictMono α → (∀ j, 0 ≤ α j) →
    Measurable (fun p : ((Fin (fitCard lx 1) → 𝒳) × (Fin (fitCard ly 1) → 𝒳)) × 𝒳 => F p.1.1 p.1.2 p.2) →
    (∀ u v z, F u v z ∈ Icc (0 : ℝ) 1) → (∀ j, IsFracRule lx ly bat (α j) c (lam j)) →
      (∀ (x₀ : Fin n → 𝒳) (y₀ : Fin m → 𝒳),
        sampleLaw P Q n m {ω |
          (∃ j, fnAlpha lx ly bat A B F lam α δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2) = α j ∧
            rejects (lam j) (fnRamp lx ly F) bat A B (α j) δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)) ∧
          fnDrift P Q lx ly F x₀ y₀ ≤
            fnAlpha lx ly bat A B F lam α δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)} ≤ ENNReal.ofReal δ) ∧
      sampleLaw P Q n m {ω |
        (∃ j, fnAlpha lx ly bat A B F lam α δ ω.1 ω.2 = α j ∧ rejects (lam j) (fnRamp lx ly F) bat A B (α j) δ ω.1 ω.2) ∧
        fnDrift P Q lx ly F ω.1 ω.2 ≤ fnAlpha lx ly bat A B F lam α δ ω.1 ω.2} ≤ ENNReal.ofReal δ

/-- T46 (d) (§8 :11-12, "and by at most `err(f̂)` plus the mesh of the grid and a betting error of order `(n∧m)^{−1/2}`"): add to (b) the
fractions of `eq:fractions` (`λ_max = ½`, any `w₀ > 0`, a prior rule `v₀² ∈ [0,4]`, floor `v²_min ∈ (0,4]`, every pair bet on), and a
mesh `h ≥ 0` of the grid below `Δ`. There is `C ≥ 0`, depending only on `δ`, `η`, `J` and `v_min` (`∃ C` before everything else), such
that, given batch 0 (for every value), with probability at least `1 − η`, `α̂ ≥ Δ − h − C N^{−1/2}` (`N ≥ 1` pairs), hence
`α⋆ − α̂ ≤ err(f̂) + h + C N^{−1/2}`; the same unconditionally when the mesh bound holds at every value of `Δ`. Last conjunct: for the
single split `π = (0, ½, 1)` (`nb = 1`, the printed pairing, boundaries within one of `n/2`, `m/2`),
`N = min(n_[1], m_[1]) ≥ (n∧m)/2 − 1`. -/
def fncert_betting_error : Prop :=
  (∀ (δ η s2 : ℝ) (J : ℕ), 0 < δ → δ < 1 → 0 < η → η < 1 → 0 < s2 → s2 ≤ 4 →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
        (n m N : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n))
        (B : Fin N → Finset (Fin m)) (α : Fin J → ℝ) (w0 h : ℝ)
        (F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ)
        (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ)
        (lam : Fin J → (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ),
        IsBatchPairing lx ly bat A B → StrictMono α → (∀ j, 0 ≤ α j) →
        Measurable (fun p : ((Fin (fitCard lx 1) → 𝒳) × (Fin (fitCard ly 1) → 𝒳)) × 𝒳 => F p.1.1 p.1.2 p.2) →
        (∀ u v z, F u v z ∈ Icc (0 : ℝ) 1) → 0 < w0 → IsPriorRule lx ly v0 →
        (∀ (j : Fin J) (k : Fin N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : Fin k → ℝ),
          lam j k x y z = fracFormula (1 / 2) (α j) (Real.log (1 / δ)) N s2 w0 (v0 j (bat k) x y) (fun _ => 1) z) →
        0 ≤ h → 1 ≤ N →
          (∀ (x₀ : Fin n → 𝒳) (y₀ : Fin m → 𝒳), MeshBelowLe α (fnDrift P Q lx ly F x₀ y₀) h →
            ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧ ENNReal.ofReal (1 - η) ≤ sampleLaw P Q n m E ∧
              ∀ ω ∈ E,
                fnDrift P Q lx ly F x₀ y₀ - h - C / √(N : ℝ) ≤
                    fnAlpha lx ly bat A B F lam α δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2) ∧
                  StatFormal.Distances.tvDist P Q -
                      fnAlpha lx ly bat A B F lam α δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2) ≤
                    errFn P Q (F (fitSample lx 1 x₀) (fitSample ly 1 y₀)) + h + C / √(N : ℝ)) ∧
          ((∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), MeshBelowLe α (fnDrift P Q lx ly F x y) h) →
            ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧ ENNReal.ofReal (1 - η) ≤ sampleLaw P Q n m E ∧
              ∀ ω ∈ E,
                fnDrift P Q lx ly F ω.1 ω.2 - h - C / √(N : ℝ) ≤ fnAlpha lx ly bat A B F lam α δ ω.1 ω.2 ∧
                  StatFormal.Distances.tvDist P Q - fnAlpha lx ly bat A B F lam α δ ω.1 ω.2 ≤
                    errFn P Q (F (fitSample lx 1 ω.1) (fitSample ly 1 ω.2)) + h + C / √(N : ℝ))) ∧
  ∀ (n m N : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m))
    (cx cy : ℕ → ℕ),
    IsBoundaries 1 n cx → IsBoundaries 1 m cy → (∀ i : Fin n, lx i = cutLabel 1 cx i) → (∀ j : Fin m, ly j = cutLabel 1 cy j) →
    IsPrintedPairing 1 lx ly bat A B →
    BoundariesNear 1 (fun b => (b : ℝ) / 2) n cx → BoundariesNear 1 (fun b => (b : ℝ) / 2) m cy →
      N = min (batchCount lx 1) (batchCount ly 1) ∧ ((min n m : ℕ) : ℝ) / 2 - 1 ≤ N

end Claims

end StatFormal.Wave31tr
