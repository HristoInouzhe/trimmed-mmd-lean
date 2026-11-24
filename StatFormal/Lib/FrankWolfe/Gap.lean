import Mathlib.Analysis.InnerProductSpace.Basic
import StatFormal.Archive.Wave17a.Statements

/-!
# The Frank–Wolfe gap of `‖a − b‖²` over a product of sets (library)

Library component (untrusted). `H` a real inner-product space; `a : ι → H`, `b : κ → H` parametrize two sets
`a '' S`, `b '' T` (for the paper: `S`, `T` capped simplices, `a`, `b` the weighted sums of the features). At a point
`(a i₀, b j₀)` with `e = a i₀ − b j₀`, `d = ‖e‖ > 0` and `f = e/d`, the Frank–Wolfe gap of `F(i, j) = ‖a i − b j‖²` is the
largest linearized decrease `2⟪e, e⟫ − 2⟪e, a i − b j⟫` over `(i, j) ∈ S × T`. Writing `μ = min_S ⟪f, a ·⟫` and
`M = max_T ⟪f, b ·⟫` (when attained):

* `inner_eq_norm_mul_inner_normalize`: `⟪e, c⟫ = d · ⟪e/d, c⟫`;
* `isGreatest_fwGap`: the gap is `2d² − 2d(μ − M)` (attained at the two extreme points);
* `fwGap_le_iff`: the gap is at most `ρ d²` iff `μ − M ≥ (1 − ρ/2) d` (the Frank–Wolfe stopping criterion as a separation
  inequality);
* `sepVal_eq_of_extremes`: `sep(f; A, B) = inf_A ⟪f,·⟫ − sup_B ⟪f,·⟫` (the frozen `Wave17a.sepVal`, in `EReal`) is the real
  number `μ − M` when the infimum and the supremum are attained.
-/

set_option linter.style.longLine false

noncomputable section
open Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.FrankWolfe

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- For `‖e‖ > 0`: `⟪e, c⟫ = ‖e‖ · ⟪‖e‖⁻¹ • e, c⟫`. -/
lemma inner_eq_norm_mul_inner_normalize {e : H} (he : 0 < ‖e‖) (c : H) :
    ⟪e, c⟫_ℝ = ‖e‖ * ⟪‖e‖⁻¹ • e, c⟫_ℝ := by
  rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ he.ne', one_mul]

variable {ι κ : Type*} {a : ι → H} {b : κ → H} {S : Set ι} {T : Set κ}

/-- **The Frank–Wolfe gap of `‖a − b‖²`.** For `e` with `‖e‖ > 0` and `f = e/‖e‖`, if `⟪f, a ·⟫` attains its minimum `μ` on
`S` and `⟪f, b ·⟫` its maximum `M` on `T`, the largest value of `2⟪e, e⟫ − 2⟪e, a i − b j⟫` over `i ∈ S`, `j ∈ T` is
`2‖e‖² − 2‖e‖(μ − M)`. -/
theorem isGreatest_fwGap {e : H} (he : 0 < ‖e‖) {μ M : ℝ}
    (hμ : IsLeast ((fun i => ⟪‖e‖⁻¹ • e, a i⟫_ℝ) '' S) μ)
    (hM : IsGreatest ((fun j => ⟪‖e‖⁻¹ • e, b j⟫_ℝ) '' T) M) :
    IsGreatest {g : ℝ | ∃ i j, i ∈ S ∧ j ∈ T ∧ g = 2 * ⟪e, e⟫_ℝ - 2 * ⟪e, a i - b j⟫_ℝ}
      (2 * ‖e‖ ^ 2 - 2 * ‖e‖ * (μ - M)) := by
  have hval : ∀ i j, 2 * ⟪e, e⟫_ℝ - 2 * ⟪e, a i - b j⟫_ℝ =
      2 * ‖e‖ ^ 2 - 2 * ‖e‖ * (⟪‖e‖⁻¹ • e, a i⟫_ℝ - ⟪‖e‖⁻¹ • e, b j⟫_ℝ) := by
    intro i j
    rw [real_inner_self_eq_norm_sq, inner_sub_right, inner_eq_norm_mul_inner_normalize he (a i),
      inner_eq_norm_mul_inner_normalize he (b j)]
    ring
  obtain ⟨i₀, hi₀, hμi⟩ := hμ.1
  obtain ⟨j₀, hj₀, hMj⟩ := hM.1
  refine ⟨⟨i₀, j₀, hi₀, hj₀, ?_⟩, ?_⟩
  · rw [hval, ← hμi, ← hMj]
  · rintro g ⟨i, j, hi, hj, rfl⟩
    have h1 : μ ≤ ⟪‖e‖⁻¹ • e, a i⟫_ℝ := hμ.2 ⟨i, hi, rfl⟩
    have h2 : ⟪‖e‖⁻¹ • e, b j⟫_ℝ ≤ M := hM.2 ⟨j, hj, rfl⟩
    rw [hval]
    have : μ - M ≤ ⟪‖e‖⁻¹ • e, a i⟫_ℝ - ⟪‖e‖⁻¹ • e, b j⟫_ℝ := by linarith
    nlinarith

/-- **The Frank–Wolfe criterion as a separation inequality.** Under the hypotheses of `isGreatest_fwGap`, the gap is at most
`ρ‖e‖²` at every `(i, j) ∈ S × T` iff `μ − M ≥ (1 − ρ/2)‖e‖`. -/
theorem fwGap_le_iff {e : H} (he : 0 < ‖e‖) {μ M : ℝ}
    (hμ : IsLeast ((fun i => ⟪‖e‖⁻¹ • e, a i⟫_ℝ) '' S) μ)
    (hM : IsGreatest ((fun j => ⟪‖e‖⁻¹ • e, b j⟫_ℝ) '' T) M) (ρ : ℝ) :
    (∀ i j, i ∈ S → j ∈ T → 2 * ⟪e, e⟫_ℝ - 2 * ⟪e, a i - b j⟫_ℝ ≤ ρ * ‖e‖ ^ 2) ↔
      (1 - ρ / 2) * ‖e‖ ≤ μ - M := by
  have hG := isGreatest_fwGap he hμ hM
  constructor
  · intro h
    obtain ⟨i, j, hi, hj, hg⟩ := hG.1
    have h1 := h i j hi hj
    rw [← hg] at h1
    have h2 : 0 ≤ 2 * ‖e‖ * ((μ - M) - (1 - ρ / 2) * ‖e‖) := by nlinarith
    have h3 := nonneg_of_mul_nonneg_right h2 (by positivity : 0 < 2 * ‖e‖)
    linarith
  · intro h i j hi hj
    have h1 := hG.2 ⟨i, j, hi, hj, rfl⟩
    have h2 : 2 * ‖e‖ * ((1 - ρ / 2) * ‖e‖) ≤ 2 * ‖e‖ * (μ - M) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    nlinarith

/-- An attained infimum, read in `EReal`: `⨅ a ∈ A, ⟪f, a⟫ = μ` when `μ` is the least value of `⟪f, ·⟫` on `A`. -/
lemma iInf_inner_eq_of_isLeast {f : H} {A : Set H} {μ : ℝ} (hμ : IsLeast ((fun a => ⟪f, a⟫_ℝ) '' A) μ) :
    (⨅ a ∈ A, ((⟪f, a⟫_ℝ : ℝ) : EReal)) = (μ : EReal) := by
  obtain ⟨a₀, ha₀, rfl⟩ := hμ.1
  refine le_antisymm (iInf₂_le a₀ ha₀) (le_iInf₂ fun a ha => ?_)
  exact EReal.coe_le_coe_iff.2 (hμ.2 ⟨a, ha, rfl⟩)

/-- An attained supremum, read in `EReal`. -/
lemma iSup_inner_eq_of_isGreatest {f : H} {B : Set H} {M : ℝ} (hM : IsGreatest ((fun b => ⟪f, b⟫_ℝ) '' B) M) :
    (⨆ b ∈ B, ((⟪f, b⟫_ℝ : ℝ) : EReal)) = (M : EReal) := by
  obtain ⟨b₀, hb₀, rfl⟩ := hM.1
  refine le_antisymm (iSup₂_le fun b hb => ?_) (le_iSup₂ (f := fun b _ => ((⟪f, b⟫_ℝ : ℝ) : EReal)) b₀ hb₀)
  exact EReal.coe_le_coe_iff.2 (hM.2 ⟨b, hb, rfl⟩)

/-- **The separation at attained extremes.** If `⟪f, ·⟫` attains its infimum `μ` on `A` and its supremum `M` on `B`, the
separation `sep(f; A, B) = inf_A ⟪f, ·⟫ − sup_B ⟪f, ·⟫` (`Wave17a.sepVal`, in `EReal`) is the real number `μ − M`. -/
theorem sepVal_eq_of_extremes {f : H} {A B : Set H} {μ M : ℝ} (hμ : IsLeast ((fun a => ⟪f, a⟫_ℝ) '' A) μ)
    (hM : IsGreatest ((fun b => ⟪f, b⟫_ℝ) '' B) M) :
    StatFormal.Wave17a.sepVal f A B = (((μ - M : ℝ)) : EReal) := by
  unfold StatFormal.Wave17a.sepVal
  rw [iInf_inner_eq_of_isLeast hμ, iSup_inner_eq_of_isGreatest hM, EReal.coe_sub]

end StatFormal.FrankWolfe
