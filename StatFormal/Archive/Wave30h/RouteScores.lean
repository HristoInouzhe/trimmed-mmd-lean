import StatFormal.Archive.Wave30h.RouteRelDev
import StatFormal.Lib.NormalScores.Bound
import StatFormal.Lib.NormalScores.Atomless

/-!
# Route — `lem:scores` (untrusted)

For a fixed sample `x` on the event of `lem:reldev` for the uniforms `F(x_i)`:
* `F`-a.e. `y` has `F(y) ∈ (0,1)` and `F_n(y) = G_n(F(y))` (`NormalScores.ae_cdf_mem_Ioo`, `ae_le_iff_cdf_le`);
* `|F̃_n(y) − F(y)| ≤ |F̃_n − F_n| + |G_n(U) − U| ≤ 2√(m(U) log n / n) + 6 log n / n`, `U = F(y)`;
* the pointwise bound `NormalScores.sq_le_bF` (clipping is `1`-Lipschitz and fixes `U` in the bulk), the
  probability integral transform `lintegral_comp_cdf` and the integral bound `lintegral_bF_le`
  (`≤ 2700 (log n)²/n` on the event).
The event is the reldev event pulled back through `ω ↦ (F(X_j ω))_j`, whose law is the uniform product
(independence and the probability integral transform).

`scores_mse_of_interp` assumes the deterministic interpolation bound `|F̃_n − F_n| ≤ 1/n`, proved in
`Scores.abs_interpCdf_sub_empCdf_le` (`F_n ≤ F̃_n ≤ F_n + 1/n`: the ramps exceed the steps of `F_n` only on the open
gap containing `t`, by at most `1`); `scores_mse` is unconditional.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave30h

open StatFormal.Wave9b (BigOP)
open StatFormal.Wave24f (stdPhiInv)
open StatFormal.NormalScores

namespace Scores

lemma clipN_mem {n : ℕ} (hn : 1 ≤ n) (w : ℝ) : clipN n w ∈ Icc (1 / (2 * n : ℝ)) (1 - 1 / (2 * n)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : 1 / (2 * n : ℝ) ≤ 1 - 1 / (2 * n) := by
    have : 1 / (2 * n : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  unfold clipN
  exact ⟨le_min (le_max_right _ _) hc, min_le_right _ _⟩

lemma clipN_eq {n : ℕ} {u : ℝ} (hu : u ∈ Icc (1 / (2 * n : ℝ)) (1 - 1 / (2 * n))) : clipN n u = u := by
  unfold clipN; rw [max_eq_left hu.1, min_eq_left hu.2]

lemma abs_clipN_sub (n : ℕ) (w u : ℝ) : |clipN n w - clipN n u| ≤ |w - u| := by
  unfold clipN
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ (by simp))
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le le_rfl (by simp))

lemma empCdf_cdf {n : ℕ} (F : Measure ℝ) (x : Fin n → ℝ) (y : ℝ)
    (hy : ∀ i, (x i ≤ y ↔ cdf F (x i) ≤ cdf F y)) :
    empCdf x y = empCdf (fun i => cdf F (x i)) (cdf F y) := by
  unfold empCdf
  congr 3
  exact Finset.filter_congr fun i _ => hy i

/-- The deterministic bound on the reldev event. -/
lemma det_bound {n : ℕ} (hn : 3 ≤ n) (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (x : Fin n → ℝ) (hI : ∀ t, |interpCdf x t - empCdf x t| ≤ 1 / n)
    (hE : ∀ t ∈ Icc (0 : ℝ) 1, |empCdf (fun i => cdf F (x i)) t - t| ≤
      2 * Real.sqrt (t * (1 - t) * Real.log n / n) + 5 * Real.log n / n) :
    ∫⁻ y, ENNReal.ofReal ((stdPhiInv (clipN n (interpCdf x y)) - stdPhiInv (cdf F y)) ^ 2) ∂F ≤
      ENNReal.ofReal (2700 * (Real.log n ^ 2 / n)) := by
  have hb : Measurable fun u => ENNReal.ofReal (bF n (mm u)) :=
    ENNReal.measurable_ofReal.comp ((measurable_bF n).comp measurable_mm)
  calc ∫⁻ y, ENNReal.ofReal ((stdPhiInv (clipN n (interpCdf x y)) - stdPhiInv (cdf F y)) ^ 2) ∂F
      ≤ ∫⁻ y, ENNReal.ofReal (bF n (mm (cdf F y))) ∂F := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_cdf_mem_Ioo F, ae_le_iff_cdf_le F x] with y hy1 hy2
        refine ENNReal.ofReal_le_ofReal ?_
        set U := cdf F y with hU
        set W := interpCdf x y with hW
        have hU01 : U ∈ Icc (0 : ℝ) 1 := ⟨hy1.1.le, hy1.2.le⟩
        have hG := hE U hU01
        rw [← empCdf_cdf F x y hy2] at hG
        have hψ : U * (1 - U) * Real.log n / n ≤ mm U * aN n := by
          have hL : 0 ≤ Real.log n / n := by
            have := one_le_log' hn; positivity
          have h1 : U * (1 - U) ≤ mm U :=
            le_min (by nlinarith [hy1.1, hy1.2]) (by nlinarith [hy1.1, hy1.2])
          calc U * (1 - U) * Real.log n / n = U * (1 - U) * (Real.log n / n) := by ring
            _ ≤ mm U * (Real.log n / n) := mul_le_mul_of_nonneg_right h1 hL
            _ = mm U * aN n := rfl
        have hWU : |W - U| ≤ 2 * √(mm U * aN n) + 6 * aN n := by
          have h1 := hI y
          have h2 : |W - U| ≤ |W - empCdf x y| + |empCdf x y - U| := abs_sub_le _ _ _
          have h3 : √(U * (1 - U) * Real.log n / n) ≤ √(mm U * aN n) := Real.sqrt_le_sqrt hψ
          have h4 := inv_le_aN hn
          have h5 : 5 * Real.log n / n = 5 * aN n := by unfold aN; ring
          linarith
        have hn1 : 1 ≤ n := by omega
        exact sq_le_bF hn hy1 hWU (clipN_mem hn1 W) fun hUin => by
          calc |clipN n W - U| = |clipN n W - clipN n U| := by rw [clipN_eq hUin]
            _ ≤ |W - U| := abs_clipN_sub n W U
    _ = ∫⁻ u in Icc (0 : ℝ) 1, ENNReal.ofReal (bF n (mm u)) := lintegral_comp_cdf F hb
    _ ≤ _ := lintegral_bF_le hn

/-- The law of `(F(X_j))_{j<n}` is the uniform product. -/
lemma map_cdf_sample (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F] {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hXm : ∀ j, Measurable (X j))
    (hind : iIndepFun X P) (hlaw : ∀ j, P.map (X j) = F) (n : ℕ) :
    P.map (fun ω (j : Fin n) => cdf F (X j ω)) = Measure.pi fun _ : Fin n => volume.restrict (Icc (0 : ℝ) 1) := by
  have hind' : iIndepFun (fun (j : Fin n) => cdf F ∘ X j) P :=
    (hind.precomp Fin.val_injective).comp (fun _ => cdf F) (fun _ => measurable_cdf' F)
  have := hind'.map_fun_eq_pi_map (fun (j : Fin n) => ((measurable_cdf' F).comp (hXm (j : ℕ))).aemeasurable)
  refine this.trans ?_
  congr 1; funext j
  rw [← Measure.map_map (measurable_cdf' F) (hXm j), hlaw, Measure.cdf_map_eq_volume_restrict]

/-! ### The interpolation bound `F_n ≤ F̃_n ≤ F_n + 1/n` -/

lemma ordStat_mono {n : ℕ} (x : Fin n → ℝ) {j k : ℕ} (hjk : j ≤ k) (hk : k < n) :
    ordStat x j ≤ ordStat x k := by
  unfold ordStat
  rw [dif_pos (lt_of_le_of_lt hjk hk), dif_pos hk]
  exact Tuple.monotone_sort x (show (⟨j, lt_of_le_of_lt hjk hk⟩ : Fin n) ≤ ⟨k, hk⟩ from hjk)

lemma card_filter_eq_sum {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    ((Finset.univ.filter fun i => x i ≤ t).card : ℝ) =
      ∑ j ∈ Finset.range n, (if ordStat x j ≤ t then (1 : ℝ) else 0) := by
  rw [Finset.natCast_card_filter, ← Equiv.sum_comp (Tuple.sort x),
    ← Fin.sum_univ_eq_sum_range (fun j => if ordStat x j ≤ t then (1 : ℝ) else 0) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ordStat, i.2]

/-- The gap `ramp(a, b, t) − 1{b ≤ t}` lies in `[0, 1]` and vanishes unless `a < t < b`. -/
lemma ramp_gap {a b t : ℝ} (hab : a ≤ b) :
    ramp a b t - (if b ≤ t then 1 else 0) ∈ Icc (0 : ℝ) 1 ∧
      (ramp a b t - (if b ≤ t then 1 else 0) ≠ 0 → a < t ∧ t < b) := by
  unfold ramp clamp01
  by_cases h : a < b
  · rw [if_pos h]
    have hba : 0 < b - a := by linarith
    by_cases hbt : b ≤ t
    · rw [if_pos hbt]
      have hq : 1 ≤ (t - a) / (b - a) := by rw [one_le_div hba]; linarith
      rw [min_eq_right hq, max_eq_right zero_le_one, sub_self]
      exact ⟨⟨le_rfl, zero_le_one⟩, fun h => absurd rfl h⟩
    · rw [if_neg hbt, sub_zero]
      refine ⟨⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩, fun hne => ⟨?_, not_le.1 hbt⟩⟩
      by_contra hta
      have hq : (t - a) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le
      exact hne (max_eq_left ((min_le_left _ _).trans hq))
  · rw [if_neg h, sub_self]
    exact ⟨⟨le_rfl, zero_le_one⟩, fun h => absurd rfl h⟩

/-- **The interpolation bound** `|F̃_n(t) − F_n(t)| ≤ 1/n` (indeed `F_n ≤ F̃_n ≤ F_n + 1/n`). -/
theorem abs_interpCdf_sub_empCdf_le {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ) (t : ℝ) :
    |interpCdf x t - empCdf x t| ≤ 1 / n := by
  set s := ordStat x with hs
  set d : ℕ → ℝ := fun j => ramp (s j) (s (j + 1)) t - (if s (j + 1) ≤ t then 1 else 0) with hd
  have hemp : empCdf x t = ((if s 0 ≤ t then (1 : ℝ) else 0) +
      ∑ j ∈ Finset.range (n - 1), (if s (j + 1) ≤ t then (1 : ℝ) else 0)) / n := by
    unfold empCdf
    rw [card_filter_eq_sum]
    congr 1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ', add_comm, Nat.add_sub_cancel]
  have hdiff : interpCdf x t - empCdf x t = (∑ j ∈ Finset.range (n - 1), d j) / n := by
    rw [hemp, interpCdf, ← sub_div]
    congr 1
    simp only [hd, Finset.sum_sub_distrib]
    ring
  have hmem : ∀ j ∈ Finset.range (n - 1), j + 1 < n := fun j hj => by
    simp only [Finset.mem_range] at hj; omega
  have hgap : ∀ j ∈ Finset.range (n - 1), d j ∈ Icc (0 : ℝ) 1 ∧ (d j ≠ 0 → s j < t ∧ t < s (j + 1)) :=
    fun j hj => ramp_gap (ordStat_mono x (Nat.le_succ j) (hmem j hj))
  have hsum : ∑ j ∈ Finset.range (n - 1), d j ∈ Icc (0 : ℝ) 1 := by
    refine ⟨Finset.sum_nonneg fun j hj => (hgap j hj).1.1, ?_⟩
    by_cases h : ∃ j0 ∈ Finset.range (n - 1), d j0 ≠ 0
    · obtain ⟨j0, hj0, hd0⟩ := h
      rw [Finset.sum_eq_single j0 (fun j hj hne => ?_) (fun h => absurd hj0 h)]
      · exact (hgap j0 hj0).1.2
      · by_contra hdj
        obtain ⟨h1, h2⟩ := (hgap j hj).2 hdj
        obtain ⟨h3, h4⟩ := (hgap j0 hj0).2 hd0
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have := ordStat_mono x (show j + 1 ≤ j0 by omega) (by have := hmem j0 hj0; omega)
          linarith
        · have := ordStat_mono x (show j0 + 1 ≤ j by omega) (by have := hmem j hj; omega)
          linarith
    · push_neg at h
      rw [Finset.sum_eq_zero h]
      norm_num
  rw [hdiff, abs_of_nonneg (div_nonneg hsum.1 (Nat.cast_nonneg _))]
  exact div_le_div_of_nonneg_right hsum.2 (Nat.cast_nonneg _)

end Scores

open Scores in
/-- **`lem:scores`**, conditional on the deterministic interpolation bound `|F̃_n − F_n| ≤ 1/n`. -/
theorem scores_mse_of_interp
    (hI : ∀ (n : ℕ) (x : Fin n → ℝ) (t : ℝ), 1 ≤ n → |interpCdf x t - empCdf x t| ≤ 1 / n) :
    Claims.scores_mse := by
  intro F _ _ Ω _ P _ X hXm hind hlaw η hη
  refine ⟨2700, max 3 ⌈4 / η⌉₊, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := le_of_max_le_left hn
  have hnη : ⌈4 / η⌉₊ ≤ n := le_of_max_le_right hn
  obtain ⟨E, hEm, hEP, hEb⟩ := reldev_bound n hn3
  set Y : Ω → Fin n → ℝ := fun ω j => cdf F (X j ω) with hY
  have hYm : Measurable Y := Measurable.of_eval fun (j : Fin n) => (measurable_cdf' F).comp (hXm (j : ℕ))
  refine ⟨Y ⁻¹' E, hYm hEm, ?_, fun ω hω => ?_⟩
  · rw [← Measure.map_apply hYm hEm, hY, map_cdf_sample F P X hXm hind hlaw n]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hEP
    have hnR : (0 : ℝ) < n := by have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
                                 linarith
    have h1 : 4 / η ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnη)
    have h2 : 4 / (n : ℝ) ≤ η := by
      rw [div_le_iff₀ hnR]; rw [div_le_iff₀ hη] at h1; linarith
    linarith
  · exact det_bound hn3 F (fun j => X j ω) (fun t => hI n _ t (by omega)) (hEb _ hω)

open Scores in
/-- **`lem:scores`.** -/
theorem scores_mse : Claims.scores_mse :=
  scores_mse_of_interp fun _ x t hn => abs_interpCdf_sub_empCdf_le hn x t

end StatFormal.Wave30h
