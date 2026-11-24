import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# FROZEN STATEMENTS — otfd R: breakdown of the lift (`prop:lift`)

Source: `otfd/papers/R_robustness/sections/s7_pipeline.tex:15-35` (`prop:lift` and its proof), the tails
`s7_pipeline.tex:8-13`, the breakdown point `s2_setting.tex:53-58` (`def:bp`, contamination set
`𝔠_ℓ(𝒵)` at l.48-52). Implementation consulted: `otfd/package/src/otfd/ranks/lift.py:43-80`
(`DualTailMap`, population sd) and `otfd/experiments/R_robustness/runs/run_common.py:110-118`
(`robust_tail`: `torch.median`, i.e. the *lower* median, for both the median and the MAD).

Covered:
* `bp_lift_min`: for **any** head and tail estimators, `BP(Q̂^lift(u)) = min{BP(head), BP(tail)}` (the
  structural fact behind (c));
* `lift_a`: (a), quadratic (mean/sd) tail: `BP(Q̂^lift(u)) = 1/n` at every `u`;
* `lift_b`: (b), separable tail: `BP(Q̂^lift(u)) ≤ min{F_k(u_k), 1 − F_k(u_k)} + 1/n` for every tail
  coordinate `k` (equivalently, for the minimum over `k > K`);
* `lift_c`: (c), robust (median/MAD) tail, midpoint median for even `n`:
  `BP(Q̂^lift(u)) = min{BP(head), ⌊(n+1)/2⌋/n}`;
* `lift_c_lower`: (c) with the lower median (and lower-median MAD), as implemented with `torch.median`:
  the same value. So the finite-sample parity question (DEFECTS #31) is settled: under `def:bp`
  (explosion only) the MAD's implosion and its parity never matter, and both median conventions give
  `⌊(n+1)/2⌋`.
Not covered (declared): the head itself (`thm:entropic`) — the head enters as an arbitrary estimator,
its breakdown point `BP(head)` is an input of (c); the heuristic tail of (b) ("of the order of the inverse
number of tail coordinates"); the package's separable tail interpolates empirical quantiles at plotting
positions `(i+½)/n` (`np.interp`), not the generalised inverse used here; the `1e-12` clamps on sd/MAD;
reference levels `F_k(u_k) = 0` (the generalised inverse is `−∞` there: not a real-valued estimator).

Encodings:
* a sample is `Z : Fin n → X × (Fin J → ℝ)`: head coordinates in an arbitrary type `X` (generalises
  `ℝ^K`), `J` tail coordinates; replacing a curve replaces both parts. `𝔠_ℓ(Z)` = samples differing from
  `Z` in at most `ℓ` indices (`Set.ncard`);
* the head is an arbitrary map `H : (Fin n → X) → Y` into a normed group `Y` (its value at the fixed
  `u_{≤K}`); the tail estimators are `(Fin n → Fin J → ℝ) → Fin J → ℝ` (value at the fixed `u_{>K}`);
  `Y × ℝ^J` and `ℝ^J` carry Mathlib's sup norms (equivalent to Euclidean: boundedness is unchanged);
* `def:bp`: `sup ‖S(Z̃)‖ = ∞` is `¬ BddAbove`; `BP = Nat.find/n`, and `1` if no `ℓ ≥ 1` explodes;
* the quadratic tail is `ū_k + u_k · sd(z_k) · s_k` with `s_k = 1/sd(U_k)` an arbitrary real (sign free),
  `sd` the population sd; the robust tail is `med(z_k) + u_k · s_k · MAD(z_k)` (any real `s_k`, which absorbs
  the 1.4826 normalisation and the reference scale); `MAD(z) = med_i |z_i − med z|`;
* order statistic of rank `r` is `inf{x : r ≤ #{i : z_i ≤ x}}`; the median is the average of the ranks
  `⌊(n+1)/2⌋` and `⌊n/2⌋+1` (they coincide for odd `n`), the lower median is rank `⌊(n+1)/2⌋`; the separable
  tail at level `p_k = F_k(u_k) ∈ (0,1]` is the generalised inverse `inf{x : p_k ≤ F̂_k(x)}`;
* junk audit: `n ≥ 1` (no `x/0`), `0 < p_k` (no `sInf` of an unbounded set), ranks in `[1,n]`, `J ≥ 1`
  in (a) and (c) (with no tail the lift is the head).
Hash-lock: DRAFT, not yet in `certify/statements.lock`; on approval this becomes `Lift/Statements.lean`.
Critic notes: DEFECTS #31 (MAD parity) is not a defect — def:bp counts explosion only. The paper's proof of (c) has a cosmetic\ngap: the explosion at ℓ = ⌊(n+1)/2⌋ needs a choice of sign (with c = −1 one-sided contamination can cancel, e.g. n = 2).
-/

noncomputable section
open Finset

namespace StatFormal.OTFDR.Lift

/-- `𝔠_ℓ(𝒵)`: samples obtained from `Z` by replacing at most `ℓ` entries. -/
def Contam {X : Type*} {n : ℕ} (Z : Fin n → X) (ℓ : ℕ) : Set (Fin n → X) :=
  {Z' | {i | Z' i ≠ Z i}.ncard ≤ ℓ}

/-- `sup_{Z̃ ∈ 𝔠_ℓ(Z)} ‖S(Z̃)‖ = ∞`. -/
def Explodes {X Y : Type*} [Norm Y] {n : ℕ} (S : (Fin n → X) → Y) (Z : Fin n → X) (ℓ : ℕ) : Prop :=
  ¬ BddAbove ((fun Z' => ‖S Z'‖) '' Contam Z ℓ)

open Classical in
/-- `def:bp`: `BP(S; Z) = (1/n) min{ℓ ≥ 1 : sup_{𝔠_ℓ(Z)} ‖S‖ = ∞}`, and `1` if there is no such `ℓ`. -/
def BP {X Y : Type*} [Norm Y] {n : ℕ} (S : (Fin n → X) → Y) (Z : Fin n → X) : ℝ :=
  if h : ∃ ℓ, 1 ≤ ℓ ∧ Explodes S Z ℓ then (Nat.find h : ℝ) / n else 1

/-- The lift `Q̂^lift(u) = (Q̂_head(u_{≤K}), T(u_{>K}))` as an estimator of the full sample. -/
def lift {X Y : Type*} {n J : ℕ} (H : (Fin n → X) → Y) (T : (Fin n → Fin J → ℝ) → Fin J → ℝ) :
    (Fin n → X × (Fin J → ℝ)) → Y × (Fin J → ℝ) :=
  fun Z => (H (fun i => (Z i).1), T (fun i => (Z i).2))

section Stats
variable {n : ℕ}

/-- Sample mean. -/
def mean (w : Fin n → ℝ) : ℝ := (∑ i, w i) / n

/-- Population standard deviation (as in `DualTailMap.fit`). -/
def sd (w : Fin n → ℝ) : ℝ := Real.sqrt ((∑ i, (w i - mean w) ^ 2) / n)

/-- Order statistic of rank `r`: `inf{x : r ≤ #{i : w_i ≤ x}}`. -/
def ordStat (w : Fin n → ℝ) (r : ℕ) : ℝ := sInf {x | r ≤ (univ.filter (fun i => w i ≤ x)).card}

/-- Empirical quantile (generalised inverse of the empirical cdf) at level `p`. -/
def quantile (w : Fin n → ℝ) (p : ℝ) : ℝ :=
  sInf {x | p ≤ ((univ.filter (fun i => w i ≤ x)).card : ℝ) / n}

/-- Median: average of the order statistics of ranks `⌊(n+1)/2⌋` and `⌊n/2⌋ + 1`. -/
def median (w : Fin n → ℝ) : ℝ := (ordStat w ((n + 1) / 2) + ordStat w (n / 2 + 1)) / 2

/-- Lower median: order statistic of rank `⌊(n+1)/2⌋` (`torch.median`). -/
def lowerMedian (w : Fin n → ℝ) : ℝ := ordStat w ((n + 1) / 2)

/-- Median absolute deviation `med_i |w_i − med w|`. -/
def mad (w : Fin n → ℝ) : ℝ := median (fun i => |w i - median w|)

/-- MAD with the lower median throughout. -/
def lowerMad (w : Fin n → ℝ) : ℝ := lowerMedian (fun i => |w i - lowerMedian w|)

end Stats

section Tails
variable {n J : ℕ}

/-- Quadratic tail at `u`: `T_k = mean(z_k) + u_k · sd(z_k) · s_k` (`s_k = 1/sd(U_k)`). -/
def quadTail (s u : Fin J → ℝ) (W : Fin n → Fin J → ℝ) : Fin J → ℝ :=
  fun k => mean (fun i => W i k) + u k * sd (fun i => W i k) * s k

/-- Separable tail at `u`: `T_k = F̂_k^{-1}(p_k)` with `p_k = F_k(u_k)`. -/
def sepTail (p : Fin J → ℝ) (W : Fin n → Fin J → ℝ) : Fin J → ℝ :=
  fun k => quantile (fun i => W i k) (p k)

/-- Robust tail at `u`: `T_k = med(z_k) + u_k · s_k · MAD(z_k)`. -/
def robTail (s u : Fin J → ℝ) (W : Fin n → Fin J → ℝ) : Fin J → ℝ :=
  fun k => median (fun i => W i k) + u k * s k * mad (fun i => W i k)

/-- Robust tail with the lower median (implementation). -/
def robTailLower (s u : Fin J → ℝ) (W : Fin n → Fin J → ℝ) : Fin J → ℝ :=
  fun k => lowerMedian (fun i => W i k) + u k * s k * lowerMad (fun i => W i k)

end Tails

namespace Claims

/-- The lift breaks down exactly when its head or its tail does. -/
def bp_lift_min : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup Y] (n J : ℕ) (H : (Fin n → X) → Y)
    (T : (Fin n → Fin J → ℝ) → Fin J → ℝ) (Z : Fin n → X × (Fin J → ℝ)),
    BP (lift H T) Z = min (BP H (fun i => (Z i).1)) (BP T (fun i => (Z i).2))

/-- `prop:lift` (a): with the quadratic tail, `BP(Q̂^lift(u)) = 1/n` at every `u`. -/
def lift_a : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup Y] (n J : ℕ) (H : (Fin n → X) → Y) (s u : Fin J → ℝ)
    (Z : Fin n → X × (Fin J → ℝ)), 1 ≤ n → 1 ≤ J →
    BP (lift H (quadTail s u)) Z = 1 / n

/-- `prop:lift` (b): with the separable tail at levels `p_k = F_k(u_k) ∈ (0,1]`,
`BP(Q̂^lift(u)) ≤ min{p_k, 1 − p_k} + 1/n` for every tail coordinate `k`. -/
def lift_b : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup Y] (n J : ℕ) (H : (Fin n → X) → Y) (p : Fin J → ℝ)
    (Z : Fin n → X × (Fin J → ℝ)), 1 ≤ n → (∀ k, 0 < p k ∧ p k ≤ 1) →
    ∀ k, BP (lift H (sepTail p)) Z ≤ min (p k) (1 - p k) + 1 / n

/-- `prop:lift` (c): with the robust tail, `BP(Q̂^lift(u)) = min{BP(Q̂_head(u_{≤K})), ⌊(n+1)/2⌋/n}`. -/
def lift_c : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup Y] (n J : ℕ) (H : (Fin n → X) → Y) (s u : Fin J → ℝ)
    (Z : Fin n → X × (Fin J → ℝ)), 1 ≤ n → 1 ≤ J →
    BP (lift H (robTail s u)) Z = min (BP H (fun i => (Z i).1)) ((((n + 1) / 2 : ℕ) : ℝ) / n)

/-- `prop:lift` (c) for the implemented robust tail (lower median and lower-median MAD). -/
def lift_c_lower : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup Y] (n J : ℕ) (H : (Fin n → X) → Y) (s u : Fin J → ℝ)
    (Z : Fin n → X × (Fin J → ℝ)), 1 ≤ n → 1 ≤ J →
    BP (lift H (robTailLower s u)) Z = min (BP H (fun i => (Z i).1)) ((((n + 1) / 2 : ℕ) : ℝ) / n)

end Claims
end StatFormal.OTFDR.Lift
