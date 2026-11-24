import StatFormal.Lib.HalfSpace.Geometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Ring.GeomSum

/-!
# Volumes of slabs and ball shells; the translation bound of a half-ball (library, untrusted)

Let `V` be a real inner-product space of dimension `d = finrank ℝ V ≥ 1`, `e` a unit vector, `ω_d = vol(B(0,1))`.

* `volume_slab_inter_ball_le`: a slab `{l ≤ ⟪x, e⟫ ≤ u}` meets the ball `B(c, ρ)` in a set of volume `≤ (u − l)(2ρ)^{d−1}`:
  complete `e` to an orthonormal basis `b` with `b₀ = e` (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`); the
  coordinates `x ↦ (⟪b_i, x⟫)_i` preserve volume (`OrthonormalBasis.measurePreserving_repr`, `PiLp.volume_preserving_ofLp`) and
  map the set into the box `[l, u] × ∏_{i ≥ 1} (⟪b_i, c⟫ − ρ, ⟪b_i, c⟫ + ρ)` (Cauchy–Schwarz), of volume `(u − l)(2ρ)^{d−1}`
  (`volume_pi_pi`);
* `pow_le_pow_sub_add`: `ρ^n ≤ (ρ − t)^n + n ρ^{n−1} t` for `0 ≤ t ≤ ρ` (the geometric sum `geom_sum₂_mul`);
* `volume_ball_diff_ball_le`: `vol(B(c, ρ) ∖ B(c + h, ρ)) ≤ d ω_d ρ^{d−1} ‖h‖`: the shell `B(c, ρ) ∖ B(c, ρ − ‖h‖)` contains it
  and has volume `ω_d (ρ^d − (ρ − ‖h‖)^d)` when `‖h‖ ≤ ρ`; when `‖h‖ > ρ`, `ω_d ρ^d ≤ d ω_d ρ^{d−1} ‖h‖`;
* `volume_symmDiff_halfball_le` ((G1) for half-balls): for `G = {a < ⟪x, e⟫}` and `E = G ∩ B(c, ρ)`,
  `vol(E △ (E + h)) ≤ ((2ρ)^{d−1} + 2 d ω_d ρ^{d−1}) ‖h‖`, from `E △ (E + h) ⊆ ((G △ (G + h)) ∩ B) ∪ (B ∖ (B + h)) ∪ ((B + h) ∖ B)`;
* `volume_near_hyperplane_le` ((G2) for half-balls): `vol{x ∈ B(c, ρ) : dist(x, ∂G) ≤ t} ≤ 2(2ρ)^{d−1} t`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Metric Module
open scoped InnerProductSpace RealInnerProductSpace symmDiff ENNReal

namespace StatFormal.HalfSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- **Slab inside a ball**: `vol({l ≤ ⟪x, e⟫ ≤ u} ∩ B(c, ρ)) ≤ (u − l)(2ρ)^{d−1}` for a unit vector `e`. -/
theorem volume_slab_inter_ball_le {e : V} (he : ‖e‖ = 1) (l u : ℝ) (c : V) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume ({x : V | l ≤ ⟪x, e⟫_ℝ ∧ ⟪x, e⟫_ℝ ≤ u} ∩ ball c ρ) ≤
      ENNReal.ofReal ((u - l) * (2 * ρ) ^ (finrank ℝ V - 1)) := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hd : 0 < finrank ℝ V := Module.finrank_pos_iff_exists_ne_zero.2 ⟨e, he0⟩
  obtain ⟨n, hn⟩ : ∃ n, finrank ℝ V = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hd).symm⟩
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ) (E := V)
    (ι := Fin (n + 1)) (v := fun _ => e) (s := {0}) (by rw [Fintype.card_fin, hn]) (by
      refine ⟨fun i => ?_, fun i j hij => ?_⟩
      · exact he
      · exact absurd (Subtype.ext ((mem_singleton_iff.1 i.2).trans (mem_singleton_iff.1 j.2).symm)) hij)
  have hb0 : b 0 = e := hb 0 rfl
  let T : V → (Fin (n + 1) → ℝ) := fun x => WithLp.ofLp (b.repr x)
  have hT : MeasurePreserving T volume volume := (PiLp.volume_preserving_ofLp _).comp b.measurePreserving_repr
  have hTi : ∀ x i, T x i = ⟪b i, x⟫_ℝ := fun x i => b.repr_apply_apply x i
  let S : Fin (n + 1) → Set ℝ := fun i => if i = 0 then Icc l u else Ioo (⟪b i, c⟫_ℝ - ρ) (⟪b i, c⟫_ℝ + ρ)
  have hsub : {x : V | l ≤ ⟪x, e⟫_ℝ ∧ ⟪x, e⟫_ℝ ≤ u} ∩ ball c ρ ⊆ T ⁻¹' Set.pi univ S := by
    rintro x ⟨⟨h1, h2⟩, hx⟩
    simp only [mem_preimage, mem_pi, mem_univ, true_implies]
    intro i
    rw [hTi]
    by_cases hi : i = 0
    · subst hi
      simp only [S, if_pos rfl, mem_Icc, hb0]
      exact ⟨by rwa [real_inner_comm], by rwa [real_inner_comm]⟩
    · simp only [S, if_neg hi, mem_Ioo]
      have hlt : |⟪b i, x⟫_ℝ - ⟪b i, c⟫_ℝ| < ρ := by
        rw [← inner_sub_right]
        calc |⟪b i, x - c⟫_ℝ| ≤ ‖b i‖ * ‖x - c‖ := abs_real_inner_le_norm _ _
          _ = ‖x - c‖ := by rw [b.orthonormal.1 i, one_mul]
          _ < ρ := by rwa [← dist_eq_norm, ← mem_ball]
      rw [abs_lt] at hlt
      constructor <;> linarith
  have hSm : MeasurableSet (Set.pi univ S) := MeasurableSet.univ_pi fun i => by
    by_cases hi : i = 0
    · simp only [S, if_pos hi]; exact measurableSet_Icc
    · simp only [S, if_neg hi]; exact measurableSet_Ioo
  calc volume ({x : V | l ≤ ⟪x, e⟫_ℝ ∧ ⟪x, e⟫_ℝ ≤ u} ∩ ball c ρ) ≤ volume (T ⁻¹' Set.pi univ S) := measure_mono hsub
    _ = volume (Set.pi univ S) := hT.measure_preimage hSm.nullMeasurableSet
    _ = ∏ i, volume (S i) := volume_pi_pi S
    _ = ENNReal.ofReal (u - l) * ENNReal.ofReal (2 * ρ) ^ n := by
      rw [Fin.prod_univ_succ]
      congr 1
      · simp [S, Real.volume_Icc]
      · rw [Finset.prod_congr rfl (g := fun _ => ENNReal.ofReal (2 * ρ)), Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        intro i _
        simp only [S, if_neg (Fin.succ_ne_zero i), Real.volume_Ioo]
        congr 1; ring
    _ = ENNReal.ofReal ((u - l) * (2 * ρ) ^ (finrank ℝ V - 1)) := by
      rw [hn, Nat.add_sub_cancel, ENNReal.ofReal_mul' (by positivity : (0 : ℝ) ≤ (2 * ρ) ^ n),
        ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * ρ)]

/-- `ρ^n ≤ (ρ − t)^n + n ρ^{n−1} t` for `0 ≤ t ≤ ρ`. -/
theorem pow_le_pow_sub_add (n : ℕ) {ρ t : ℝ} (ht : 0 ≤ t) (htρ : t ≤ ρ) :
    ρ ^ n ≤ (ρ - t) ^ n + n * ρ ^ (n - 1) * t := by
  have hr : 0 ≤ ρ - t := by linarith
  have key := geom_sum₂_mul ρ (ρ - t) n
  have hsum : ∑ i ∈ Finset.range n, ρ ^ i * (ρ - t) ^ (n - 1 - i) ≤ n * ρ ^ (n - 1) := by
    calc ∑ i ∈ Finset.range n, ρ ^ i * (ρ - t) ^ (n - 1 - i) ≤ ∑ _i ∈ Finset.range n, ρ ^ (n - 1) :=
          Finset.sum_le_sum fun i hi => by
            have hi' : i ≤ n - 1 := by have := Finset.mem_range.1 hi; omega
            calc ρ ^ i * (ρ - t) ^ (n - 1 - i) ≤ ρ ^ i * ρ ^ (n - 1 - i) := by
                  gcongr
                  · exact pow_nonneg (by linarith) _
                  · linarith
              _ = ρ ^ (n - 1) := by rw [← pow_add]; congr 1; omega
      _ = n * ρ ^ (n - 1) := by simp
  have hk : ρ - (ρ - t) = t := by ring
  rw [hk] at key
  nlinarith [mul_le_mul_of_nonneg_right hsum ht]

/-- **Ball shells**: `vol(B(c, ρ) ∖ B(c + h, ρ)) ≤ d ω_d ρ^{d−1} ‖h‖`, `ω_d = vol(B(0,1))`, `d = finrank ℝ V ≥ 1`. -/
theorem volume_ball_diff_ball_le [Nontrivial V] (c h : V) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (ball c ρ \ ball (c + h) ρ) ≤
      ENNReal.ofReal (finrank ℝ V * (volume (ball (0 : V) 1)).toReal * ρ ^ (finrank ℝ V - 1) * ‖h‖) := by
  set d := finrank ℝ V with hd_def
  have hd : 1 ≤ d := Module.finrank_pos
  set ω := (volume (ball (0 : V) 1)).toReal with hω
  have hω0 : 0 ≤ ω := ENNReal.toReal_nonneg
  have hB1 : volume (ball (0 : V) 1) = ENNReal.ofReal ω := (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  have hball : ∀ r, 0 ≤ r → volume (ball c r) = ENNReal.ofReal (r ^ d * ω) := fun r hr => by
    rw [Measure.addHaar_ball volume c hr, hB1, ← ENNReal.ofReal_mul (pow_nonneg hr _)]
  set t := ‖h‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg h
  have hpow : ρ ^ d = ρ * ρ ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  rcases le_or_gt t ρ with htρ | htρ
  · have hsub : ball c (ρ - t) ⊆ ball c ρ := ball_subset_ball (by linarith)
    have hsub2 : ball c ρ \ ball (c + h) ρ ⊆ ball c ρ \ ball c (ρ - t) := by
      intro x ⟨hx1, hx2⟩
      refine ⟨hx1, fun hx3 => hx2 ?_⟩
      rw [mem_ball] at hx3 ⊢
      calc dist x (c + h) ≤ dist x c + dist c (c + h) := dist_triangle _ _ _
        _ = dist x c + t := by rw [dist_eq_norm c (c + h), sub_add_cancel_left, norm_neg]
        _ < ρ - t + t := by linarith
        _ = ρ := by ring
    refine (measure_mono hsub2).trans ?_
    rw [measure_sdiff_le_iff_le_add measurableSet_ball.nullMeasurableSet hsub measure_ball_lt_top.ne,
      hball ρ hρ, hball (ρ - t) (by linarith), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := pow_le_pow_sub_add d ht0 htρ
    nlinarith
  · refine (measure_mono sdiff_subset).trans ?_
    rw [hball ρ hρ]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hp : 0 ≤ ρ ^ (d - 1) := pow_nonneg hρ _
    rw [hpow]
    have e1 := mul_le_mul_of_nonneg_right htρ.le hp
    have e2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hp ht0)
    have : ρ * ρ ^ (d - 1) ≤ d * ρ ^ (d - 1) * t := by nlinarith
    nlinarith

/-- **(G1) for a half-ball**: `vol(E △ (E + h)) ≤ ((2ρ)^{d−1} + 2 d ω_d ρ^{d−1}) ‖h‖` for `E = {a < ⟪x, e⟫} ∩ B(c, ρ)`. -/
theorem volume_symmDiff_halfball_le {e : V} (he : ‖e‖ = 1) (a : ℝ) (c : V) {ρ : ℝ} (hρ : 0 ≤ ρ) (h : V) :
    volume (symmDiff ({x : V | a < ⟪x, e⟫_ℝ} ∩ ball c ρ) ((· - h) ⁻¹' ({x : V | a < ⟪x, e⟫_ℝ} ∩ ball c ρ))) ≤
      ENNReal.ofReal (((2 * ρ) ^ (finrank ℝ V - 1) +
        2 * finrank ℝ V * (volume (ball (0 : V) 1)).toReal * ρ ^ (finrank ℝ V - 1)) * ‖h‖) := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have : Nontrivial V := ⟨⟨e, 0, he0⟩⟩
  set d := finrank ℝ V
  set ω := (volume (ball (0 : V) 1)).toReal
  have hω0 : 0 ≤ ω := ENNReal.toReal_nonneg
  have hpre : (· - h) ⁻¹' ({x : V | a < ⟪x, e⟫_ℝ} ∩ ball c ρ) =
      (· - h) ⁻¹' {x : V | a < ⟪x, e⟫_ℝ} ∩ ball (c + h) ρ := by
    rw [preimage_inter]
    congr 1
    ext x
    simp only [mem_preimage, mem_ball, dist_eq_norm]
    rw [show x - h - c = x - (c + h) by abel]
  rw [hpre]
  have hsub := symmDiff_inter_subset {x : V | a < ⟪x, e⟫_ℝ} ((· - h) ⁻¹' {x : V | a < ⟪x, e⟫_ℝ}) (ball c ρ)
    (ball (c + h) ρ)
  have hslab : symmDiff {x : V | a < ⟪x, e⟫_ℝ} ((· - h) ⁻¹' {x : V | a < ⟪x, e⟫_ℝ}) ∩ ball c ρ ⊆
      {x | min a (a + ⟪h, e⟫_ℝ) ≤ ⟪x, e⟫_ℝ ∧ ⟪x, e⟫_ℝ ≤ max a (a + ⟪h, e⟫_ℝ)} ∩ ball c ρ :=
    inter_subset_inter_left _ (symmDiff_halfspace_subset e h a)
  have h1 := (measure_mono hslab).trans (volume_slab_inter_ball_le he (min a (a + ⟪h, e⟫_ℝ))
    (max a (a + ⟪h, e⟫_ℝ)) c hρ)
  rw [max_sub_min_add] at h1
  have h2 := volume_ball_diff_ball_le c h hρ
  have h3 : volume (ball (c + h) ρ \ ball c ρ) ≤ ENNReal.ofReal (d * ω * ρ ^ (d - 1) * ‖h‖) := by
    have := volume_ball_diff_ball_le (c + h) (-h) hρ
    rwa [add_neg_cancel_right, norm_neg] at this
  have hhe : |⟪h, e⟫_ℝ| ≤ ‖h‖ := by
    calc |⟪h, e⟫_ℝ| ≤ ‖h‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ = ‖h‖ := by rw [he, mul_one]
  calc volume (symmDiff ({x : V | a < ⟪x, e⟫_ℝ} ∩ ball c ρ) ((· - h) ⁻¹' {x : V | a < ⟪x, e⟫_ℝ} ∩ ball (c + h) ρ))
      ≤ volume (symmDiff {x : V | a < ⟪x, e⟫_ℝ} ((· - h) ⁻¹' {x : V | a < ⟪x, e⟫_ℝ}) ∩ ball c ρ) +
          volume (ball c ρ \ ball (c + h) ρ) + volume (ball (c + h) ρ \ ball c ρ) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
    _ ≤ ENNReal.ofReal (|⟪h, e⟫_ℝ| * (2 * ρ) ^ (d - 1)) + ENNReal.ofReal (d * ω * ρ ^ (d - 1) * ‖h‖) +
          ENNReal.ofReal (d * ω * ρ ^ (d - 1) * ‖h‖) := add_le_add (add_le_add h1 h2) h3
    _ = ENNReal.ofReal (|⟪h, e⟫_ℝ| * (2 * ρ) ^ (d - 1) + d * ω * ρ ^ (d - 1) * ‖h‖ + d * ω * ρ ^ (d - 1) * ‖h‖) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
      refine ENNReal.ofReal_le_ofReal ?_
      have : |⟪h, e⟫_ℝ| * (2 * ρ) ^ (d - 1) ≤ ‖h‖ * (2 * ρ) ^ (d - 1) :=
        mul_le_mul_of_nonneg_right hhe (by positivity)
      nlinarith

/-- **(G2) for a half-ball**: `vol{x ∈ B(c, ρ) : dist(x, ∂G) ≤ t} ≤ 2(2ρ)^{d−1} t` for `G = {a < ⟪x, e⟫}`, `t ≥ 0`. -/
theorem volume_near_hyperplane_le {e : V} (he : ‖e‖ = 1) (a : ℝ) (c : V) {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ) :
    volume {x | x ∈ ball c ρ ∧ infDist x (frontier {x : V | a < ⟪x, e⟫_ℝ}) ≤ t} ≤
      ENNReal.ofReal (2 * (2 * ρ) ^ (finrank ℝ V - 1) * t) := by
  have hsub : {x | x ∈ ball c ρ ∧ infDist x (frontier {x : V | a < ⟪x, e⟫_ℝ}) ≤ t} ⊆
      {x : V | a - t ≤ ⟪x, e⟫_ℝ ∧ ⟪x, e⟫_ℝ ≤ a + t} ∩ ball c ρ := by
    rintro x ⟨hx, hxt⟩
    rw [infDist_frontier_halfspace he, abs_le] at hxt
    exact ⟨⟨by linarith, by linarith⟩, hx⟩
  refine (measure_mono hsub).trans ((volume_slab_inter_ball_le he _ _ c hρ).trans (le_of_eq ?_))
  congr 1; ring

end StatFormal.HalfSpace
