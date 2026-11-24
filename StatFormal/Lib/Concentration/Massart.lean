import StatFormal.Lib.Concentration.Rademacher
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Massart's finite-class lemma

Library component (concentration, part 7). Untrusted library code. Conventions of
`Rademacher.lean`: `σ` uniform on `{±1}ᵐ` via the exact average `radE`.

For a finite nonempty `V ⊆ ℝᵐ` (a `Finset (Fin m → ℝ)`) with `∑ᵢ vᵢ² ≤ R²` for all `v ∈ V`:

* `radE_sup_le_massart`: `E_σ max_{v∈V} ∑ σᵢ vᵢ ≤ R √(2 log |V|)`;
* `radE_sup_abs_le_massart`: `E_σ max_{v∈V} |∑ σᵢ vᵢ| ≤ R √(2 log (2|V|))` (via `V ∪ −V`).

Route: Jensen `exp(λ E max) ≤ E exp(λ max) ≤ ∑_v E exp(λ ∑ σᵢ vᵢ)`, the exact product formula
`E exp(λ ∑ σᵢ vᵢ) = ∏ cosh(λ vᵢ) ≤ exp(λ² ‖v‖²/2)` (Hoeffding per coordinate,
`Real.cosh_le_exp_half_sq`), then optimise `λ`; degenerate cases (`R = 0` or `|V| = 1`) by
letting `λ → ∞` or `λ → 0`.
-/

noncomputable section
open Finset Real

namespace StatFormal.Concentration

variable {m : ℕ}

/-- `∑ σᵢ vᵢ`. -/
def rsum (v : Fin m → ℝ) (σ : Fin m → Bool) : ℝ := ∑ i, rsign (σ i) * v i

theorem radE_exp_rsum (v : Fin m → ℝ) (l : ℝ) :
    radE (fun σ => exp (l * rsum v σ)) = ∏ i, cosh (l * v i) := by
  have hσ : ∀ σ : Fin m → Bool, exp (l * rsum v σ) = ∏ i, exp (l * (rsign (σ i) * v i)) := by
    intro σ; rw [rsum, mul_sum, Real.exp_sum]
  unfold radE
  simp_rw [hσ]
  rw [← Fintype.prod_sum (fun i (b : Bool) => exp (l * (rsign b * v i)))]
  have h2 : ∀ i, ∑ b : Bool, exp (l * (rsign b * v i)) = 2 * cosh (l * v i) := by
    intro i
    rw [Fintype.sum_bool, Real.cosh_eq]
    simp only [rsign_true, rsign_false, one_mul, neg_one_mul, mul_neg]
    ring
  simp_rw [h2]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

theorem radE_exp_rsum_le (v : Fin m → ℝ) (l : ℝ) :
    radE (fun σ => exp (l * rsum v σ)) ≤ exp (l ^ 2 * (∑ i, v i ^ 2) / 2) := by
  rw [radE_exp_rsum]
  calc ∏ i, cosh (l * v i) ≤ ∏ i, exp ((l * v i) ^ 2 / 2) :=
        Finset.prod_le_prod₀ (fun i _ => (cosh_pos _).le) fun i _ => cosh_le_exp_half_sq _
    _ = exp (l ^ 2 * (∑ i, v i ^ 2) / 2) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum, Finset.sum_div]
        exact sum_congr rfl fun i _ => by ring

theorem exp_radE_le (F : (Fin m → Bool) → ℝ) : exp (radE F) ≤ radE (fun σ => exp (F σ)) := by
  unfold radE
  have hw : ∑ _σ : Fin m → Bool, ((2 : ℝ) ^ m)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_signs]
    field_simp
  have := convexOn_exp.map_sum_le (t := univ) (w := fun _ => ((2 : ℝ) ^ m)⁻¹) (p := F)
    (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
  simpa [smul_eq_mul, mul_sum] using this

/-- **Massart's finite-class lemma.** -/
theorem radE_sup_le_massart (V : Finset (Fin m → ℝ)) (hV : V.Nonempty) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ v ∈ V, ∑ i, v i ^ 2 ≤ R ^ 2) :
    radE (fun σ => V.sup' hV (fun v => rsum v σ)) ≤ R * √(2 * log V.card) := by
  set M := radE (fun σ => V.sup' hV (fun v => rsum v σ)) with hM
  have hcard : (0 : ℝ) < V.card := Nat.cast_pos.2 hV.card_pos
  set L := log (V.card : ℝ) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hV.card_pos)
  have key : ∀ l : ℝ, 0 < l → l * M ≤ L + l ^ 2 * R ^ 2 / 2 := by
    intro l hl
    have h1 : exp (l * M) ≤ (V.card : ℝ) * exp (l ^ 2 * R ^ 2 / 2) := by
      calc exp (l * M) = exp (radE (fun σ => l * V.sup' hV (fun v => rsum v σ))) := by
            rw [radE_const_mul]
        _ ≤ radE (fun σ => exp (l * V.sup' hV (fun v => rsum v σ))) := exp_radE_le _
        _ ≤ radE (fun σ => ∑ v ∈ V, exp (l * rsum v σ)) := radE_mono fun σ => by
            obtain ⟨v, hv, hvmax⟩ := V.exists_mem_eq_sup' hV (fun v => rsum v σ)
            rw [hvmax]
            exact single_le_sum (f := fun v => exp (l * rsum v σ))
              (fun v _ => (exp_pos _).le) hv
        _ = ∑ v ∈ V, radE (fun σ => exp (l * rsum v σ)) := radE_sum _ _
        _ ≤ ∑ _v ∈ V, exp (l ^ 2 * R ^ 2 / 2) := sum_le_sum fun v hv =>
            (radE_exp_rsum_le v l).trans (exp_le_exp.2 (by
              have := hR v hv
              have hl2 : 0 ≤ l ^ 2 := sq_nonneg l
              nlinarith))
        _ = (V.card : ℝ) * exp (l ^ 2 * R ^ 2 / 2) := by rw [sum_const, nsmul_eq_mul]
    have := Real.log_le_log (exp_pos _) h1
    rwa [Real.log_exp, Real.log_mul hcard.ne' (exp_pos _).ne', Real.log_exp] at this
  by_cases hRL : 0 < R ∧ 0 < L
  · obtain ⟨hR, hLp⟩ := hRL
    set s := √(2 * L) with hs
    have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
    have hs2 : s ^ 2 = 2 * L := Real.sq_sqrt (by linarith)
    have h := key (s / R) (div_pos hspos hR)
    have hrhs : L + (s / R) ^ 2 * R ^ 2 / 2 = s ^ 2 := by
      rw [div_pow]; field_simp; linarith
    rw [hrhs, div_mul_eq_mul_div, div_le_iff₀ hR] at h
    have : s * M ≤ s * (R * s) := by nlinarith
    exact le_of_mul_le_mul_left this hspos
  · have hrhs : R * √(2 * L) = 0 := by
      rcases not_and_or.1 hRL with h | h
      · have : R = 0 := le_antisymm (not_lt.1 h) hR0
        simp [this]
      · have : L = 0 := le_antisymm (not_lt.1 h) hL0
        simp [this]
    rw [hrhs]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    rcases not_and_or.1 hRL with h | h
    · have hR' : R = 0 := le_antisymm (not_lt.1 h) hR0
      have hl : 0 < (L + 1) / ε := by positivity
      have := key _ hl
      rw [hR'] at this
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
        add_zero] at this
      rw [div_mul_eq_mul_div, div_le_iff₀ hε] at this
      nlinarith
    · have hL' : L = 0 := le_antisymm (not_lt.1 h) hL0
      have hl : 0 < ε / (R ^ 2 + 1) := by positivity
      have := key _ hl
      rw [hL', zero_add, div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
      have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
      have : ε * M ≤ ε * ε := by
        have h3 : (ε / (R ^ 2 + 1)) ^ 2 * R ^ 2 / 2 * (R ^ 2 + 1) ≤ ε * ε := by
          rw [div_pow]
          have hpos : 0 < R ^ 2 + 1 := by positivity
          rw [show ε ^ 2 / (R ^ 2 + 1) ^ 2 * R ^ 2 / 2 * (R ^ 2 + 1) =
            ε ^ 2 * (R ^ 2 / (R ^ 2 + 1)) / 2 by field_simp]
          have : R ^ 2 / (R ^ 2 + 1) ≤ 1 := by rw [div_le_one hpos]; linarith
          nlinarith [sq_nonneg ε]
        linarith
      exact le_of_mul_le_mul_left this hε

/-- **Massart, absolute-value form** (apply the lemma to `V ∪ −V`). -/
theorem radE_sup_abs_le_massart (V : Finset (Fin m → ℝ)) (hV : V.Nonempty) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ v ∈ V, ∑ i, v i ^ 2 ≤ R ^ 2) :
    radE (fun σ => V.sup' hV (fun v => |rsum v σ|)) ≤ R * √(2 * log (2 * V.card)) := by
  classical
  set V' := V ∪ V.image (fun v => -v) with hV'def
  have hV' : V'.Nonempty := hV.mono subset_union_left
  have hR' : ∀ v ∈ V', ∑ i, v i ^ 2 ≤ R ^ 2 := by
    intro v hv
    rcases mem_union.1 hv with hv | hv
    · exact hR v hv
    · obtain ⟨w, hw, rfl⟩ := mem_image.1 hv
      simpa using hR w hw
  have hneg : ∀ (v : Fin m → ℝ) (σ : Fin m → Bool), rsum (-v) σ = -rsum v σ := fun v σ => by
    simp [rsum, sum_neg_distrib]
  have hpt : ∀ σ, V.sup' hV (fun v => |rsum v σ|) ≤ V'.sup' hV' (fun v => rsum v σ) := by
    intro σ
    refine sup'_le hV _ fun v hv => ?_
    rcases le_total 0 (rsum v σ) with h | h
    · rw [abs_of_nonneg h]
      exact le_sup' (fun v => rsum v σ) (mem_union_left _ hv)
    · rw [abs_of_nonpos h, ← hneg]
      exact le_sup' (fun v => rsum v σ) (mem_union_right _ (mem_image_of_mem _ hv))
  refine (radE_mono hpt).trans ((radE_sup_le_massart V' hV' hR0 hR').trans ?_)
  have hc : (V'.card : ℝ) ≤ 2 * V.card := by
    have h1 : V'.card ≤ V.card + (V.image fun v => -v).card := card_union_le _ _
    have h2 := card_image_le (s := V) (f := fun v => -v)
    have : V'.card ≤ 2 * V.card := by omega
    exact_mod_cast this
  have hc0 : (0 : ℝ) < V'.card := Nat.cast_pos.2 hV'.card_pos
  gcongr

end StatFormal.Concentration
