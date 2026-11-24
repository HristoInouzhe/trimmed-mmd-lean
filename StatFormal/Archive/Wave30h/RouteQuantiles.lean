import StatFormal.Archive.Wave30h.RouteOP
import TauCeti.Probability.Quantile

/-!
# Route — `lem:quantiles`, deterministic part (untrusted)

* Order statistics (`Tuple.sort`): `ordStat_mono`, the count `n F_n(t) = Σ_{j<n} 1{X_{(j+1)} ≤ t}`.
* `empCdf_le_interpCdf`, `interpCdf_le_empCdf_add`: `F_n ≤ F̃_n ≤ F_n + 1/n` (each ramp lies between the indicators
  of its two endpoints), whence `quantiles_cdf`.
* `ass:marg`: the cdf `G` is continuous, `(y − x)/L ≤ G(y) − G(x)` on `[a, b]`, `G(F⁻¹(u)) = u`, `F⁻¹(u) ∈ [a, b]`,
  and `|x − F⁻¹(w)| ≤ L|G(x) − w|` for `x ∈ [a, b]`.
* `abs_cdf_ordStat_sub`: `|G(X_{(j+1)}) − (j+1)/n| ≤ ε` (continuity of `G`; no "no ties" needed).
* Abel summation (`abel_bound`): `Q̃_n(u) − F⁻¹(u)` is a convex combination of `X_{(j+1)} − F⁻¹(u)` over the `j`
  with `|u − (j+1)/n| < 3/(2n)`, whence `quantiles_quant`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave30h

/-! ### Order statistics -/

section OrderStats
variable {n : ℕ} (x : Fin n → ℝ)

lemma ordStat_eq (j : ℕ) (hj : j < n) : ordStat x j = x (Tuple.sort x ⟨j, hj⟩) := by
  simp [ordStat, hj]

lemma ordStat_mono {i j : ℕ} (hij : i ≤ j) (hj : j < n) : ordStat x i ≤ ordStat x j := by
  rw [ordStat_eq x i (lt_of_le_of_lt hij hj), ordStat_eq x j hj]
  exact Tuple.monotone_sort x (show (⟨i, lt_of_le_of_lt hij hj⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)

lemma ordStat_mem {S : Set ℝ} (hx : ∀ i, x i ∈ S) (j : ℕ) (hj : j < n) : ordStat x j ∈ S := by
  rw [ordStat_eq x j hj]; exact hx _

/-- `n F_n(t) = Σ_{j<n} 1{X_{(j+1)} ≤ t}`. -/
lemma card_le_eq_sum (t : ℝ) :
    ((Finset.univ.filter fun i => x i ≤ t).card : ℝ) =
      ∑ j ∈ Finset.range n, (if ordStat x j ≤ t then (1 : ℝ) else 0) := by
  rw [Finset.sum_range, Finset.card_filter]
  push_cast
  rw [← Equiv.sum_comp (Tuple.sort x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ordStat_eq x i i.isLt]

lemma empCdf_eq (t : ℝ) :
    empCdf x t = (∑ j ∈ Finset.range n, (if ordStat x j ≤ t then (1 : ℝ) else 0)) / n := by
  rw [empCdf, card_le_eq_sum]

end OrderStats

/-! ### Ramps and the interpolated cdf -/

lemma clamp01_nonneg (z : ℝ) : 0 ≤ clamp01 z := le_max_left _ _

lemma clamp01_le_one (z : ℝ) : clamp01 z ≤ 1 := max_le zero_le_one (min_le_right _ _)

lemma clamp01_of_one_le {z : ℝ} (hz : 1 ≤ z) : clamp01 z = 1 := by
  simp [clamp01, min_eq_right hz]

lemma clamp01_of_nonpos {z : ℝ} (hz : z ≤ 0) : clamp01 z = 0 := by
  simp only [clamp01]; exact max_eq_left ((min_le_left _ _).trans hz)

lemma pos_of_clamp01_pos {z : ℝ} (hz : 0 < clamp01 z) : 0 < z := by
  by_contra h; push_neg at h; rw [clamp01_of_nonpos h] at hz; exact lt_irrefl _ hz

lemma lt_one_of_clamp01_lt_one {z : ℝ} (hz : clamp01 z < 1) : z < 1 := by
  by_contra h; push_neg at h; rw [clamp01_of_one_le h] at hz; exact lt_irrefl _ hz

lemma clamp01_mono : Monotone clamp01 := fun _ _ h => max_le_max le_rfl (min_le_min h le_rfl)

lemma ramp_bounds {a b t : ℝ} (hab : a ≤ b) :
    (if b ≤ t then (1 : ℝ) else 0) ≤ ramp a b t ∧ ramp a b t ≤ (if a ≤ t then (1 : ℝ) else 0) := by
  unfold ramp
  rcases hab.lt_or_eq with hlt | heq
  · rw [if_pos hlt]
    have hba : 0 < b - a := by linarith
    constructor
    · split_ifs with hbt
      · rw [clamp01_of_one_le]; rw [le_div_iff₀ hba]; linarith
      · exact clamp01_nonneg _
    · split_ifs with hat
      · exact clamp01_le_one _
      · rw [clamp01_of_nonpos]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le
  · subst heq; simp

section Interp
variable {n : ℕ} (x : Fin n → ℝ)

lemma interp_num_bounds (hn : 1 ≤ n) (t : ℝ) :
    ∑ j ∈ Finset.range n, (if ordStat x j ≤ t then (1 : ℝ) else 0) ≤
        (if ordStat x 0 ≤ t then (1 : ℝ) else 0) +
          ∑ j ∈ Finset.range (n - 1), ramp (ordStat x j) (ordStat x (j + 1)) t ∧
      (if ordStat x 0 ≤ t then (1 : ℝ) else 0) +
          ∑ j ∈ Finset.range (n - 1), ramp (ordStat x j) (ordStat x (j + 1)) t ≤
        1 + ∑ j ∈ Finset.range n, (if ordStat x j ≤ t then (1 : ℝ) else 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hr : ∀ j ∈ Finset.range m, (if ordStat x (j + 1) ≤ t then (1 : ℝ) else 0) ≤
      ramp (ordStat x j) (ordStat x (j + 1)) t ∧
      ramp (ordStat x j) (ordStat x (j + 1)) t ≤ (if ordStat x j ≤ t then (1 : ℝ) else 0) := by
    intro j hj
    exact ramp_bounds (ordStat_mono x (Nat.le_succ j) (by simp at hj; omega))
  constructor
  · rw [Finset.sum_range_succ']
    rw [add_comm]
    exact add_le_add_right (Finset.sum_le_sum fun j hj => (hr j hj).1) _
  · calc (if ordStat x 0 ≤ t then (1 : ℝ) else 0) +
          ∑ j ∈ Finset.range m, ramp (ordStat x j) (ordStat x (j + 1)) t
        ≤ 1 + ∑ j ∈ Finset.range m, (if ordStat x j ≤ t then (1 : ℝ) else 0) := by
          gcongr with j hj
          · split_ifs <;> norm_num
          · exact (hr j hj).2
      _ ≤ 1 + ∑ j ∈ Finset.range (m + 1), (if ordStat x j ≤ t then (1 : ℝ) else 0) := by
          refine add_le_add le_rfl ?_
          rw [Finset.sum_range_succ]
          refine le_add_of_nonneg_right ?_
          split_ifs <;> norm_num

lemma empCdf_le_interpCdf (hn : 1 ≤ n) (t : ℝ) : empCdf x t ≤ interpCdf x t := by
  rw [empCdf_eq, interpCdf]
  exact div_le_div_of_nonneg_right (interp_num_bounds x hn t).1 (by positivity)

lemma interpCdf_le_empCdf_add (hn : 1 ≤ n) (t : ℝ) : interpCdf x t ≤ empCdf x t + 1 / n := by
  rw [empCdf_eq, interpCdf, ← add_div, add_comm _ (1 : ℝ)]
  exact div_le_div_of_nonneg_right (interp_num_bounds x hn t).2 (by positivity)

lemma abs_interpCdf_sub_empCdf (hn : 1 ≤ n) (t : ℝ) : |interpCdf x t - empCdf x t| ≤ 1 / n := by
  rw [abs_le]
  constructor <;> linarith [empCdf_le_interpCdf x hn t, interpCdf_le_empCdf_add x hn t,
    show (0 : ℝ) ≤ 1 / n by positivity]

end Interp

theorem quantiles_cdf : Claims.quantiles_cdf := by
  intro F _ n x ε hn hε t
  calc |interpCdf x t - cdf F t| ≤ |interpCdf x t - empCdf x t| + |empCdf x t - cdf F t| :=
        abs_sub_le _ _ _
    _ ≤ 1 / n + ε := add_le_add (abs_interpCdf_sub_empCdf x hn t) (hε t)
    _ = ε + 1 / n := add_comm _ _

/-! ### `ass:marg` -/

section Marg
variable {F : Measure ℝ} [IsProbabilityMeasure F] {L : ℝ≥0} {a b : ℝ}

lemma cdf_sub_eq {x y : ℝ} (hxy : x ≤ y) : cdf F y - cdf F x = F.real (Ioc x y) := by
  have hm : F (Ioc x y) = ENNReal.ofReal (cdf F y - cdf F x) := by
    have := (cdf F).measure_Ioc x y; rwa [measure_cdf] at this
  rw [measureReal_def, hm, ENNReal.toReal_ofReal (sub_nonneg.2 (monotone_cdf F hxy))]

lemma AssMarg.cdf_sub_le (h : AssMarg L a b F) {x y : ℝ} (hxy : x ≤ y) :
    cdf F y - cdf F x ≤ L * (y - x) := by
  obtain ⟨-, -, -, hup⟩ := h
  rw [cdf_sub_eq hxy]
  have h1 : F (Ioc x y) ≤ (L : ℝ≥0∞) * volume (Ioc x y) := by
    refine (hup _).trans ?_
    rw [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)
  rw [Real.volume_Ioc] at h1
  have h2 : F (Ioc x y) ≤ ENNReal.ofReal (L * (y - x)) := by
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg L), ENNReal.ofReal_coe_nnreal]; exact h1
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg L.2 (by linarith)) h2

lemma AssMarg.le_cdf_sub (h : AssMarg L a b F) {x y : ℝ} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    (L : ℝ)⁻¹ * (y - x) ≤ cdf F y - cdf F x := by
  obtain ⟨hL, -, hlow, -⟩ := h
  rw [cdf_sub_eq hxy]
  have hsub : Ioc x y ⊆ Icc a b := fun z hz => ⟨hax.trans hz.1.le, hz.2.trans hyb⟩
  have h1 : ENNReal.ofReal (L : ℝ)⁻¹ * volume (Ioc x y) ≤ F (Ioc x y) := by
    have := hlow (Ioc x y)
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_Ioc,
      Set.inter_eq_left.2 hsub] at this
    exact this
  rw [Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity)] at h1
  rw [measureReal_def]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h1

lemma AssMarg.continuous_cdf (h : AssMarg L a b F) : Continuous (cdf F) := by
  refine (LipschitzWith.of_dist_le_mul fun x y => ?_).continuous (K := L)
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total x y with hxy | hxy
  · rw [abs_sub_comm, abs_of_nonneg (by linarith [monotone_cdf F hxy]), abs_sub_comm,
      abs_of_nonneg (by linarith)]
    exact h.cdf_sub_le hxy
  · rw [abs_of_nonneg (by linarith [monotone_cdf F hxy]), abs_of_nonneg (by linarith)]
    exact h.cdf_sub_le hxy

lemma AssMarg.cdf_left (h : AssMarg L a b F) : cdf F a = 0 := by
  obtain ⟨-, -, -, hup⟩ := h
  have h1 : F (Iic a) = 0 := by
    refine le_antisymm ((hup _).trans ?_) zero_le
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_Iic]
    have : Iic a ∩ Icc a b ⊆ {a} := fun z hz => le_antisymm hz.1 hz.2.1
    rw [measure_mono_null this (Real.volume_singleton)]; simp
  rw [cdf_eq_real, measureReal_def, h1]; simp

lemma AssMarg.cdf_right (h : AssMarg L a b F) : cdf F b = 1 := by
  obtain ⟨-, -, -, hup⟩ := h
  have h1 : F (Iic b)ᶜ = 0 := by
    refine le_antisymm ((hup _).trans ?_) zero_le
    rw [Measure.smul_apply, smul_eq_mul, compl_Iic, Measure.restrict_apply measurableSet_Ioi]
    have : Ioi b ∩ Icc a b = ∅ := by
      ext z; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_empty_iff_false, iff_false]
      intro ⟨h1, _, h2⟩; linarith
    rw [this]; simp
  rw [cdf_eq_real, measureReal_def, prob_compl_eq_zero_iff measurableSet_Iic |>.1 h1]; simp

lemma AssMarg.quantile_mem (h : AssMarg L a b F) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    F.quantile u ∈ Icc a b := by
  constructor
  · by_contra hlt; push_neg at hlt
    have h1 : u ≤ cdf F (F.quantile u) := Measure.le_cdf_quantile F hu.2
    have h2 : cdf F (F.quantile u) ≤ cdf F a := monotone_cdf F hlt.le
    rw [h.cdf_left] at h2; linarith [hu.1]
  · exact (Measure.quantile_le_iff F hu.1 hu.2).2 (by rw [h.cdf_right]; exact hu.2.le)

lemma AssMarg.cdf_quantile (h : AssMarg L a b F) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    cdf F (F.quantile u) = u := by
  refine le_antisymm ?_ (Measure.le_cdf_quantile F hu.2)
  have hc := h.continuous_cdf.continuousAt (x := F.quantile u)
  refine le_of_tendsto (x := 𝓝[<] (F.quantile u)) (hc.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact ((Measure.lt_quantile_iff F hu.1 hu.2).1 hz).le

/-- `|x − F⁻¹(w)| ≤ L |G(x) − w|` for `x ∈ [a, b]`, `w ∈ (0, 1)`. -/
lemma AssMarg.abs_sub_quantile_le (h : AssMarg L a b F) {x w : ℝ} (hx : x ∈ Icc a b) (hw : w ∈ Ioo (0 : ℝ) 1) :
    |x - F.quantile w| ≤ L * |cdf F x - w| := by
  have hq := h.quantile_mem hw
  have hcq := h.cdf_quantile hw
  have hL : (0 : ℝ) < L := h.1
  rcases le_total x (F.quantile w) with hxq | hxq
  · have := h.le_cdf_sub hx.1 hxq hq.2
    rw [hcq] at this
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith [monotone_cdf F hxq, hcq])]
    rw [inv_mul_le_iff₀ hL] at this; linarith
  · have := h.le_cdf_sub hq.1 hxq hx.2
    rw [hcq] at this
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith [monotone_cdf F hxq, hcq])]
    rw [inv_mul_le_iff₀ hL] at this; linarith

lemma AssMarg.quantile_lipschitzOn (h : AssMarg L a b F) : LipschitzOnWith L F.quantile (Ioo 0 1) := by
  refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
  rw [Real.dist_eq, Real.dist_eq]
  have := h.abs_sub_quantile_le (h.quantile_mem hu) hv
  rwa [h.cdf_quantile hu] at this

end Marg

/-! ### `|G(X_{(j+1)}) − (j+1)/n| ≤ ε` -/

lemma abs_cdf_ordStat_sub {F : Measure ℝ} [IsProbabilityMeasure F] (hc : Continuous (cdf F)) {n : ℕ}
    (x : Fin n → ℝ) {ε : ℝ} (hε : ∀ t, |empCdf x t - cdf F t| ≤ ε) (j : ℕ) (hj : j < n) :
    |cdf F (ordStat x j) - (j + 1) / n| ≤ ε := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlow : ((j : ℝ) + 1) / n ≤ empCdf x (ordStat x j) := by
    rw [empCdf_eq]
    refine div_le_div_of_nonneg_right ?_ hn.le
    calc ((j : ℝ) + 1) = ∑ i ∈ Finset.range (j + 1), (1 : ℝ) := by simp
      _ = ∑ i ∈ Finset.range (j + 1), (if ordStat x i ≤ ordStat x j then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [if_pos (ordStat_mono x (by simp at hi; omega) hj)]
      _ ≤ ∑ i ∈ Finset.range n, (if ordStat x i ≤ ordStat x j then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega)) ?_
          intro i _ _; split_ifs <;> norm_num
  have hbelow : ∀ z < ordStat x j, empCdf x z ≤ j / n := by
    intro z hz
    rw [empCdf_eq]
    refine div_le_div_of_nonneg_right ?_ hn.le
    calc ∑ i ∈ Finset.range n, (if ordStat x i ≤ z then (1 : ℝ) else 0)
        ≤ ∑ i ∈ Finset.range j, (1 : ℝ) := by
          rw [← Finset.sum_range_add_sum_Ico _ (show j ≤ n by omega)]
          have h0 : ∑ i ∈ Finset.Ico j n, (if ordStat x i ≤ z then (1 : ℝ) else 0) = 0 := by
            refine Finset.sum_eq_zero fun i hi => ?_
            simp only [Finset.mem_Ico] at hi
            rw [if_neg (not_le.2 (hz.trans_le (ordStat_mono x hi.1 hi.2)))]
          rw [h0, add_zero]
          exact Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
      _ = j := by simp
  rw [abs_le]
  constructor
  · have := hε (ordStat x j); rw [abs_le] at this; linarith
  · have hup : cdf F (ordStat x j) ≤ j / n + ε := by
      refine le_of_tendsto (x := 𝓝[<] (ordStat x j)) (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have := hε z; rw [abs_le] at this
      linarith [hbelow z hz]
    have : (j : ℝ) / n ≤ (j + 1) / n := div_le_div_of_nonneg_right (by linarith) hn.le
    linarith

/-! ### Abel summation -/

/-- Weights of the Abel summation `a₀ + Σ_{j<m} (a_{j+1} − a_j) c_j = Σ_{j≤m} w_j a_j`. -/
def abelW (c : ℕ → ℝ) (m j : ℕ) : ℝ := (if j = 0 then 1 else c (j - 1)) - (if j < m then c j else 0)

lemma abel_eq (a c : ℕ → ℝ) (m : ℕ) :
    a 0 + ∑ j ∈ Finset.range m, (a (j + 1) - a j) * c j = ∑ j ∈ Finset.range (m + 1), a j * abelW c m j := by
  induction m with
  | zero => simp [abelW]
  | succ m ih =>
    have hw : ∀ j ∈ Finset.range (m + 1), a j * abelW c (m + 1) j =
        a j * abelW c m j - (if j = m then a m * c m else 0) := by
      intro j hj
      simp only [Finset.mem_range] at hj
      unfold abelW
      by_cases hjm : j = m
      · subst hjm; simp; split_ifs <;> ring
      · have : j < m := by omega
        simp [this, hjm, show j < m + 1 by omega]
    rw [Finset.sum_range_succ, ← add_assoc, ih, Finset.sum_range_succ (fun j => a j * abelW c (m + 1) j) (m + 1),
      Finset.sum_congr rfl hw, Finset.sum_sub_distrib, Finset.sum_ite_eq' (Finset.range (m + 1)) m,
      if_pos (Finset.self_mem_range_succ m)]
    have hlast : abelW c (m + 1) (m + 1) = c m := by simp [abelW]
    rw [hlast]; ring

lemma abelW_nonneg {c : ℕ → ℝ} (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1) (hanti : ∀ j, c (j + 1) ≤ c j)
    (m j : ℕ) : 0 ≤ abelW c m j := by
  unfold abelW
  split_ifs with h1 h2 h2
  · linarith [hc1 j]
  · norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; linarith [hanti k]
  · linarith [hc0 (j - 1)]

lemma abelW_ne_zero_left {c : ℕ → ℝ} (hc0 : ∀ j, 0 ≤ c j) (hanti : ∀ j, c (j + 1) ≤ c j) {m j : ℕ}
    (hw : abelW c m j ≠ 0) (hj : 1 ≤ j) : 0 < c (j - 1) := by
  by_contra hle
  push_neg at hle
  have h1 : c (j - 1) = 0 := le_antisymm hle (hc0 _)
  have h2 : c j = 0 := le_antisymm (by have := hanti (j - 1); rw [show j - 1 + 1 = j by omega] at this; linarith) (hc0 _)
  apply hw; unfold abelW
  rw [if_neg (by omega), h1]
  split_ifs <;> simp [h2]

lemma abelW_ne_zero_right {c : ℕ → ℝ} (hc1 : ∀ j, c j ≤ 1) (hanti : ∀ j, c (j + 1) ≤ c j) {m j : ℕ}
    (hw : abelW c m j ≠ 0) (hjm : j < m) : c j < 1 := by
  by_contra hle
  push_neg at hle
  have h1 : c j = 1 := le_antisymm (hc1 j) hle
  apply hw; unfold abelW
  rw [if_pos hjm, h1]
  split_ifs with h0
  · ring
  · have : c (j - 1) = 1 := le_antisymm (hc1 _) (by
      have := hanti (j - 1); rw [show j - 1 + 1 = j by omega, h1] at this; exact this)
    rw [this]; ring

lemma sum_abelW (c : ℕ → ℝ) (m : ℕ) : ∑ j ∈ Finset.range (m + 1), abelW c m j = 1 := by
  have := abel_eq (fun _ => 1) c m
  simp only [sub_self, zero_mul, Finset.sum_const_zero, add_zero, one_mul] at this
  exact this.symm

lemma abel_bound (a c : ℕ → ℝ) (m : ℕ) (B : ℝ) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (hanti : ∀ j, c (j + 1) ≤ c j) (hB : ∀ j ≤ m, abelW c m j ≠ 0 → |a j| ≤ B) :
    |a 0 + ∑ j ∈ Finset.range m, (a (j + 1) - a j) * c j| ≤ B := by
  rw [abel_eq]
  calc |∑ j ∈ Finset.range (m + 1), a j * abelW c m j| ≤ ∑ j ∈ Finset.range (m + 1), |a j * abelW c m j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (m + 1), B * abelW c m j := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [abs_mul, abs_of_nonneg (abelW_nonneg hc0 hc1 hanti m j)]
        by_cases hw : abelW c m j = 0
        · simp [hw]
        · exact mul_le_mul_of_nonneg_right (hB j (by simp at hj; omega) hw) (abelW_nonneg hc0 hc1 hanti m j)
    _ = B := by rw [← Finset.mul_sum, sum_abelW, mul_one]

/-! ### `lem:quantiles`, quantile part -/

theorem quantiles_quant : Claims.quantiles_quant := by
  intro F _ L a b n x ε hM hn hx hε u hu
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set c : ℕ → ℝ := fun j => clamp01 (n * u - (j + 1 / 2)) with hc_def
  have hc0 : ∀ j, 0 ≤ c j := fun j => clamp01_nonneg _
  have hc1 : ∀ j, c j ≤ 1 := fun j => clamp01_le_one _
  have hanti : ∀ j, c (j + 1) ≤ c j := fun j => clamp01_mono (by push_cast; linarith)
  have hrepr : interpQuant x u - F.quantile u =
      (fun j => ordStat x j - F.quantile u) 0 +
        ∑ j ∈ Finset.range (n - 1), ((fun j => ordStat x j - F.quantile u) (j + 1) -
          (fun j => ordStat x j - F.quantile u) j) * c j := by
    simp only [interpQuant, hc_def, sub_sub_sub_cancel_right]; ring
  rw [hrepr]
  refine abel_bound (fun j => ordStat x j - F.quantile u) c (n - 1) (L * (ε + 2 / n)) hc0 hc1 hanti
    fun j hj hw => ?_
  have hjn : j < n := by omega
  -- the weight is nonzero only when `|nu − (j+1)| < 3/2`
  have hloc : |u - (j + 1) / n| ≤ 2 / n := by
    have hlo : (j : ℝ) - 1 / 2 < n * u := by
      by_cases hj0 : j = 0
      · subst hj0; simp; nlinarith [hu.1]
      · have hpos := pos_of_clamp01_pos (abelW_ne_zero_left hc0 hanti hw (by omega))
        rw [Nat.cast_sub (by omega)] at hpos; push_cast at hpos; linarith
    have hhi : n * u < (j : ℝ) + 3 / 2 := by
      by_cases hjm : j < n - 1
      · have := lt_one_of_clamp01_lt_one (abelW_ne_zero_right hc1 hanti hw hjm); linarith
      · have hj' : (j : ℝ) + 1 = n := by
          have : j = n - 1 := by omega
          rw [this, Nat.cast_sub (by omega)]; push_cast; ring
        nlinarith [hu.2]
    have key : |(n : ℝ) * u - (j + 1)| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    have : u - (j + 1) / n = ((n : ℝ) * u - (j + 1)) / n := by field_simp
    rw [this, abs_div, abs_of_pos hnpos]
    exact div_le_div_of_nonneg_right key hnpos.le
  have hyj := ordStat_mem x hx j hjn
  have hG := abs_cdf_ordStat_sub hM.continuous_cdf x hε j hjn
  calc |ordStat x j - F.quantile u| ≤ L * |cdf F (ordStat x j) - u| := hM.abs_sub_quantile_le hyj hu
    _ ≤ L * (ε + 2 / n) := by
        gcongr
        calc |cdf F (ordStat x j) - u| ≤ |cdf F (ordStat x j) - (j + 1) / n| + |(j + 1) / n - u| :=
              abs_sub_le _ _ _
          _ ≤ ε + 2 / n := add_le_add hG (by rw [abs_sub_comm]; exact hloc)

end StatFormal.Wave30h
