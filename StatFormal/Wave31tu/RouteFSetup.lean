import StatFormal.Wave31tu.Statements
import StatFormal.Wave31tr.Proofs
import StatFormal.Lib.ExcessRamp.Quantile
import StatFormal.Lib.Alpha0Witness.Gram

set_option linter.style.longLine false

/-!
# Wave31tu, chunk F: the setting of Proposition S4.27 (`prop:lapfitted`, S4 :1293-1300)

* `laplace1_facts`: a feature map with the Gram function `e^{−|x−y|}` is continuous, strongly measurable and has `‖φ x‖ ≤ 1`
  (library `Alpha0Witness.continuous_of_gram`);
* `exists_pop_objects`: the population objects of `eq:lappop` exist at every level `α ∈ [0,1)`: nearest points `a ∈ 𝒞_α(P)`,
  `b ∈ 𝒞_α(Q)` with `‖a − b‖ = D_α` (certified 31tr T33 `witness_unique`), the least `(1−α)`-quantile `t⋆` and the greatest
  `α`-quantile `u⋆` of `f⋆ = (a − b)/‖a − b‖` (library `ExcessRamp.exists_isLeast_quantile`, `exists_isGreatest_quantile`);
* `devG_nonneg`, `devG'_nonneg`, `devB_nonneg`, `pbar_nonneg`: the constants `ϖ`, `ϖ′`, `b` of Lemma S4.25 are nonnegative.
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteF

open StatFormal StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.TrimmedMMD.Concentration
  StatFormal.TrimmedMMD.Unconditional StatFormal.Wave31tq

/-- A feature map with the Laplace Gram function `e^{−|x−y|}` is continuous, strongly measurable and of norm at most one. -/
theorem laplace1_facts {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {φ : ℝ → H}
    (hφ : IsLaplaceFeature 1 φ) : Continuous φ ∧ StronglyMeasurable φ ∧ ∀ x, ‖φ x‖ ≤ 1 := by
  have hk : (fun p : ℝ × ℝ => ⟪φ p.1, φ p.2⟫_ℝ) = fun p => Real.exp (-|p.1 - p.2| / 1) :=
    funext fun p => hφ p.1 p.2
  have hc : Continuous φ := StatFormal.Alpha0Witness.continuous_of_gram (by rw [hk]; fun_prop)
  refine ⟨hc, hc.stronglyMeasurable, fun x => ?_⟩
  have h : ‖φ x‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hφ, sub_self, abs_zero, neg_zero, zero_div, Real.exp_zero]
  nlinarith [norm_nonneg (φ x)]

/-- `‖‖d‖⁻¹ • d‖ ≤ 1`. -/
theorem norm_normalize_le {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (d : H) : ‖‖d‖⁻¹ • d‖ ≤ 1 := by
  rw [norm_smul, norm_inv, norm_norm]
  by_cases h : ‖d‖ = 0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

/-- **The population objects exist** (the setting of `eq:lappop`): nearest points of the two regions at the level `α` and the
extreme quantiles of the normalized population witness. -/
theorem exists_pop_objects {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] {φ : ℝ → H} (hφ : IsLaplaceFeature 1 φ) (P Q : Measure ℝ) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ (a b : H) (t u : ℝ), a ∈ region φ α P ∧ b ∈ region φ α Q ∧ ‖a - b‖ = Dpop φ P Q α ∧
      IsLeast {q | IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) q} t ∧
      IsGreatest {q | IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α q} u := by
  obtain ⟨hc, hsm, hκ⟩ := laplace1_facts hφ
  obtain ⟨-, -, -, ⟨d, hd, -⟩, hall⟩ := StatFormal.Wave31tr.witness_unique ℝ H P Q φ 1 α hsm hκ hα0 hα1
  obtain ⟨hnorm, a, ha, b, hb, rfl⟩ := hall d hd
  set F : ℝ → ℝ := fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ with hF
  have hFm : Measurable F := (continuous_const.inner hc).measurable
  have hFb : ∀ x, |F x| ≤ 1 := fun x => by
    calc |F x| ≤ ‖‖a - b‖⁻¹ • (a - b)‖ * ‖φ x‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * 1 := mul_le_mul (norm_normalize_le _) (hκ x) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  obtain ⟨t, ht⟩ := StatFormal.ExcessRamp.exists_isLeast_quantile P hFm hFb (p := 1 - α) (by linarith) (by linarith)
  obtain ⟨u, hu⟩ := StatFormal.ExcessRamp.exists_isGreatest_quantile Q hFm hFb (p := α) hα0 hα1
  exact ⟨a, b, t, u, ha, hb, hnorm, ht, hu⟩

/-- `p̄ ≥ 0`: it bounds `p + q ≥ 0` at `x₀`. -/
theorem pbar_nonneg {p q : ℝ → ℝ} {x₀ rs pbar : ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (hrs : 0 ≤ rs)
    (hpbar : ∀ z ∈ Icc (x₀ - rs) (x₀ + rs), p z + q z ≤ pbar) : 0 ≤ pbar :=
  le_trans (add_nonneg (hp x₀) (hq x₀)) (hpbar x₀ ⟨by linarith, by linarith⟩)

/-- `ϖ = A₁K^{1/4}s_{n,m} ≥ 0`. -/
theorem devG_nonneg {pbar cs rs K c : ℝ} {n m : ℕ} (hpbar : 0 ≤ pbar) (hcs : 0 < cs) (hrs : 0 < rs) (hK : 0 ≤ K) :
    0 ≤ devG pbar cs rs K c n m := by
  unfold devG lapA1 sDev
  have h1 : 0 ≤ (2 * √2 * pbar) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h2 : 0 ≤ (2 * √2 / (cs * rs)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h3 : 0 ≤ (2 : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h4 : 0 ≤ K ^ (1 / 4 : ℝ) := Real.rpow_nonneg hK _
  positivity

/-- `ϖ′ = 2K^{1/4}s_{n,m} ≥ 0`. -/
theorem devG'_nonneg {K c : ℝ} {n m : ℕ} (hK : 0 ≤ K) : 0 ≤ devG' K c n m := by
  unfold devG' sDev
  have h4 : 0 ≤ K ^ (1 / 4 : ℝ) := Real.rpow_nonneg hK _
  positivity

/-- `b = 6K^{1/2}c_x r_{n,m} ≥ 0` for `x ≥ 0`. -/
theorem devB_nonneg {K c : ℝ} {n m : ℕ} (hK : 0 ≤ K) (hc : 0 ≤ c) : 0 ≤ devB K c n m := by
  unfold devB cx rDev
  have h4 : 0 ≤ K ^ (1 / 2 : ℝ) := Real.rpow_nonneg hK _
  positivity

end StatFormal.Wave31tu.RouteF
