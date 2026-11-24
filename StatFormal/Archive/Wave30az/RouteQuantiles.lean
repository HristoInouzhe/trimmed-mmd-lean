import StatFormal.Archive.Wave30az.Statements
import StatFormal.Archive.Wave30h.RouteQuantiles
import StatFormal.Archive.Wave30h.Proofs

/-!
# Route — SB journal `lem:quantiles` at the endpoints `u ∈ {0, 1}`

* The printed `F^{-1}(0) = inf{x : F(x) ≥ 0} = inf ℝ = −∞`, so `Q̃_n(0) − F^{-1}(0) = +∞`; the printed bound over
  `[0,1]` fails already for `F = U[0,1]`, `n = 1`.
* `Q̃_n(1) = X_(n)`, `Q̃_n(0) = X_(1)` (all clamps saturate); with `|F(X_(j+1)) − (j+1)/n| ≤ ε` (certified Wave 30h) and
  `(y − x)/L ≤ F(y) − F(x)` on `[a, b]`: `b − X_(n) ≤ Lε`, `X_(1) − a ≤ L(ε + 1/n)`.
* On `(0,1)` the certified `quantiles_quant`; `{x : u ≤ F(x)} = [F^{-1}(u), ∞)` for `u ∈ (0,1)`, `= [b, ∞)` for `u = 1`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace StatFormal.Wave30az

open StatFormal.Wave30h (AssMarg empCdf interpQuant ordStat clamp01)

lemma sInf_coe_Ici (q : ℝ) : sInf ((fun x : ℝ => (x : EReal)) '' Ici q) = (q : EReal) := by
  refine le_antisymm (sInf_le ⟨q, Set.self_mem_Ici, rfl⟩) (le_sInf ?_)
  rintro _ ⟨y, hy, rfl⟩
  exact EReal.coe_le_coe_iff.2 hy

theorem quantiles_zero_printed : Claims.quantiles_zero_printed := by
  intro F _ n x
  have hset : {x : ℝ | (0 : ℝ) ≤ cdf F x} = univ := eq_univ_of_forall fun x => cdf_nonneg F x
  have hbot : quantE F 0 = ⊥ := by
    unfold quantE
    rw [hset, sInf_eq_bot]
    intro b hb
    obtain ⟨r, -, hr⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    exact ⟨(r : EReal), ⟨r, mem_univ _, rfl⟩, hr⟩
  refine ⟨hbot, ?_⟩
  rw [hbot]
  simp

theorem quantiles_printed_refuted : Claims.quantiles_printed_refuted := by
  intro H
  set F : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1) with hF
  haveI : IsProbabilityMeasure F := ⟨by rw [hF, Measure.restrict_apply_univ, Real.volume_Icc]; simp⟩
  have hA : AssMarg 1 0 1 F := by
    refine ⟨one_pos, one_pos, ?_, ?_⟩
    · simp [hF]
    · simp [hF]
  have hx : ∀ i : Fin 1, (fun _ : Fin 1 => (0 : ℝ)) i ∈ Icc (0 : ℝ) 1 := fun _ => ⟨le_rfl, zero_le_one⟩
  have hε : ∀ t, |empCdf (fun _ : Fin 1 => (0 : ℝ)) t - cdf F t| ≤ 1 := by
    intro t
    have h1 : 0 ≤ empCdf (fun _ : Fin 1 => (0 : ℝ)) t := by unfold empCdf; positivity
    have h2 : empCdf (fun _ : Fin 1 => (0 : ℝ)) t ≤ 1 := by
      unfold empCdf
      rw [Nat.cast_one, div_one]
      exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
    rw [abs_le]
    constructor <;> linarith [cdf_nonneg F t, cdf_le_one F t]
  have h := (H F 1 0 1 1 (fun _ => 0) 1 hA le_rfl hx hε 0 ⟨le_rfl, zero_le_one⟩).1
  rw [(quantiles_zero_printed F 1 (fun _ => 0)).2] at h
  exact absurd h (not_le.2 (EReal.coe_lt_top _))

section Closed

variable {n : ℕ} (x : Fin n → ℝ)

lemma interpQuant_one (hn : 1 ≤ n) : interpQuant x 1 = ordStat x (n - 1) := by
  unfold interpQuant
  have hc : ∀ j ∈ Finset.range (n - 1), clamp01 ((n : ℝ) * 1 - (j + 1 / 2)) = 1 := by
    intro j hj
    rw [Finset.mem_range] at hj
    apply StatFormal.Wave30h.clamp01_of_one_le
    have : (j : ℝ) + 1 ≤ n - 1 := by
      have : j + 1 ≤ n - 1 := hj
      have h' : ((j + 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub hn] at h'
      push_cast at h'
      linarith
    linarith
  rw [Finset.sum_congr rfl fun j hj => by rw [hc j hj, mul_one]]
  rw [Finset.sum_range_sub (fun j => ordStat x j)]
  ring

lemma interpQuant_zero : interpQuant x 0 = ordStat x 0 := by
  unfold interpQuant
  have hc : ∀ j ∈ Finset.range (n - 1), clamp01 ((n : ℝ) * 0 - (j + 1 / 2)) = 0 := by
    intro j _
    apply StatFormal.Wave30h.clamp01_of_nonpos
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  rw [Finset.sum_congr rfl fun j hj => by rw [hc j hj, mul_zero]]
  simp

end Closed

theorem quantiles_closed : Claims.quantiles_closed := by
  intro F _ L a b n x ε hA hn hx hε
  have hL : (0 : ℝ) < L := hA.1
  have hab : a < b := hA.2.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcl := hA.continuous_cdf
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε 0)
  have hslack : L * ε ≤ L * (ε + 2 / n) := by
    have : 0 ≤ 2 / (n : ℝ) := by positivity
    nlinarith
  -- the level set at `u = 1`
  have hset1 : {y : ℝ | (1 : ℝ) ≤ cdf F y} = Ici b := by
    ext y
    simp only [mem_setOf_eq, mem_Ici]
    constructor
    · intro hy
      by_contra hlt
      push_neg at hlt
      rcases lt_or_ge y a with hya | hya
      · have := monotone_cdf F hya.le
        rw [hA.cdf_left] at this
        linarith
      · have := hA.le_cdf_sub hya hlt.le le_rfl
        rw [hA.cdf_right] at this
        have : 0 < (L : ℝ)⁻¹ * (b - y) := mul_pos (inv_pos.2 hL) (by linarith)
        linarith
    · intro hy
      have := monotone_cdf F hy
      rw [hA.cdf_right] at this
      exact this
  have hq1 : F.quantile 1 = b := by
    rw [Measure.quantile_def, hset1, csInf_Ici]
  have hquantE : ∀ u ∈ Ioc (0 : ℝ) 1, quantE F u = ((F.quantile u : ℝ) : EReal) := by
    intro u hu
    unfold quantE
    rcases lt_or_eq_of_le hu.2 with hu1 | rfl
    · rw [Measure.setOf_le_cdf_eq_Ici F hu.1 hu1, sInf_coe_Ici]
    · rw [hset1, sInf_coe_Ici, hq1]
  -- order statistics at the ends
  have hmax : ordStat x (n - 1) ∈ Icc a b := StatFormal.Wave30h.ordStat_mem x hx (n - 1) (by omega)
  have hmin : ordStat x 0 ∈ Icc a b := StatFormal.Wave30h.ordStat_mem x hx 0 (by omega)
  have hc1 := StatFormal.Wave30h.abs_cdf_ordStat_sub hcl x hε (n - 1) (by omega)
  have hc0 := StatFormal.Wave30h.abs_cdf_ordStat_sub hcl x hε 0 (by omega)
  have hnm : ((n - 1 : ℕ) : ℝ) + 1 = n := by rw [Nat.cast_sub hn]; push_cast; ring
  rw [hnm, div_self hn0.ne'] at hc1
  rw [Nat.cast_zero, zero_add] at hc0
  have hend1 : |interpQuant x 1 - b| ≤ L * (ε + 2 / n) := by
    rw [interpQuant_one x hn]
    have h1 := hA.le_cdf_sub hmax.1 hmax.2 le_rfl
    rw [hA.cdf_right] at h1
    rw [inv_mul_le_iff₀ hL] at h1
    rw [abs_le] at hc1
    rw [abs_of_nonpos (by linarith [hmax.2])]
    have : L * (1 - cdf F (ordStat x (n - 1))) ≤ L * ε := mul_le_mul_of_nonneg_left (by linarith) hL.le
    linarith
  refine ⟨hquantE, hq1, ?_, ?_, ?_⟩
  · intro u hu
    rcases lt_or_eq_of_le hu.2 with hu1 | rfl
    · exact StatFormal.Wave30h.quantiles_quant F L a b n x ε hA hn hx hε u ⟨hu.1, hu1⟩
    · rw [hq1]; exact hend1
  · intro u hu
    have h := hA.abs_sub_quantile_le (x := a) ⟨le_rfl, hab.le⟩ hu
    rw [hA.cdf_left, zero_sub, abs_neg, abs_of_pos hu.1, abs_sub_comm] at h
    exact h
  · rw [interpQuant_zero x]
    have h0 := hA.le_cdf_sub le_rfl hmin.1 hmin.2
    rw [hA.cdf_left, sub_zero, inv_mul_le_iff₀ hL] at h0
    rw [abs_le] at hc0
    rw [abs_of_nonneg (by linarith [hmin.1])]
    have h2 : L * cdf F (ordStat x 0) ≤ L * (ε + 1 / n) := mul_le_mul_of_nonneg_left (by linarith) hL.le
    have h3 : L * (ε + 1 / n) ≤ L * (ε + 2 / n) := by
      apply mul_le_mul_of_nonneg_left _ hL.le
      have : 1 / (n : ℝ) ≤ 2 / n := div_le_div_of_nonneg_right (by norm_num) hn0.le
      linarith
    linarith

end StatFormal.Wave30az
