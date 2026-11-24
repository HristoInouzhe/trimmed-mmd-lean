import StatFormal.Archive.TrimmedMMD.Projection.Statements
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Proofs: projection stability (trimmed-MMD supplement)
-/

noncomputable section
open Real Set Metric Filter Topology
open scoped Pointwise

namespace StatFormal.TrimmedMMD.Projection

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Approximate nearest points from an extended-Hausdorff bound. -/
theorem near_of_hausdorff {C C' : Set E} {η : ℝ} (hη : 0 ≤ η)
    (h : hausdorffEDist C C' ≤ ENNReal.ofReal η)
    {x : E} (hx : x ∈ C) {ε : ℝ} (hε : 0 < ε) : ∃ y ∈ C', ‖x - y‖ < η + ε := by
  have hlt : hausdorffEDist C C' < ENNReal.ofReal (η + ε) :=
    lt_of_le_of_lt h ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
  obtain ⟨y, hy, hxy⟩ := exists_edist_lt_of_hausdorffEDist_lt hx hlt
  exact ⟨y, hy, by rw [← dist_eq_norm]; exact edist_lt_ofReal.1 hxy⟩

/-- A value bounded by `g ε` for every `ε > 0` is bounded by `g 0` if `g` is continuous at `0`. -/
theorem le_of_forall_pos_cont {a : ℝ} {g : ℝ → ℝ} (hg : ContinuousAt g 0)
    (h : ∀ ε > 0, a ≤ g ε) : a ≤ g 0 :=
  ge_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall (s := Set.Ioi 0) fun ε hε => h ε hε)

/-- Variational inequality for the minimum-norm point: `⟪p, q - p⟫ ≥ 0`. -/
theorem inner_nonneg_of_minNorm {C : Set E} {p : E} (hC : Convex ℝ C) (hp : IsMinNorm C p) :
    ∀ q ∈ C, 0 ≤ inner ℝ p (q - p) := by
  have : Nonempty C := ⟨⟨p, hp.1⟩⟩
  have heq : ‖(0 : E) - p‖ = ⨅ w : C, ‖(0 : E) - w‖ := by
    apply le_antisymm
    · exact le_ciInf fun w => by simpa using hp.2 w w.2
    · refine ciInf_le ?_ (⟨p, hp.1⟩ : C)
      refine ⟨0, ?_⟩
      rintro _ ⟨w, rfl⟩
      exact norm_nonneg _
  intro q hq
  have := (norm_eq_iInf_iff_real_inner_le_zero hC hp.1).1 heq q hq
  rw [zero_sub, inner_neg_left] at this
  linarith

/-- `eq:qgrowth`: `‖q − p‖² ≤ ‖q‖² − ‖p‖²` on a convex set. -/
theorem qgrowth {C : Set E} {p : E} (hC : Convex ℝ C) (hp : IsMinNorm C p) {q : E} (hq : q ∈ C) :
    ‖q - p‖ ^ 2 ≤ ‖q‖ ^ 2 - ‖p‖ ^ 2 := by
  have h := inner_nonneg_of_minNorm hC hp q hq
  have hexp : ‖q‖ ^ 2 = ‖p‖ ^ 2 + 2 * inner ℝ p (q - p) + ‖q - p‖ ^ 2 := by
    have := norm_add_sq_real p (q - p)
    rw [add_sub_cancel] at this
    linarith
  linarith

/-- Part (i): `‖p'‖ ≤ ‖p‖ + η`. -/
theorem norm_le_add {C C' : Set E} {p p' : E} {η : ℝ} (hη : 0 ≤ η)
    (h : hausdorffEDist C C' ≤ ENNReal.ofReal η) (hp : IsMinNorm C p) (hp' : IsMinNorm C' p') :
    ‖p'‖ ≤ ‖p‖ + η := by
  have key : ∀ ε > 0, ‖p'‖ ≤ ‖p‖ + η + ε := by
    intro ε hε
    obtain ⟨y, hy, hxy⟩ := near_of_hausdorff hη h hp.1 hε
    have := hp'.2 y hy
    have : ‖y‖ ≤ ‖p‖ + ‖p - y‖ := by
      calc ‖y‖ = ‖p - (p - y)‖ := by abel_nf
        _ ≤ ‖p‖ + ‖p - y‖ := norm_sub_le _ _
    linarith
  exact le_of_forall_pos_le_add fun ε hε => by linarith [key ε hε]

/-- One half of part (ii): `‖p − p'‖ ≤ η + √((D' + η)² − D²)`. -/
theorem dist_le_half {C C' : Set E} {p p' : E} {η : ℝ} (hη : 0 ≤ η) (hC : Convex ℝ C)
    (h : hausdorffEDist C' C ≤ ENNReal.ofReal η) (hp : IsMinNorm C p) (hp' : IsMinNorm C' p') :
    ‖p - p'‖ ≤ η + √((‖p'‖ + η) ^ 2 - ‖p‖ ^ 2) := by
  let g : ℝ → ℝ := fun ε => η + ε + √((‖p'‖ + η + ε) ^ 2 - ‖p‖ ^ 2)
  have hg : ContinuousAt g 0 := by fun_prop
  have key : ∀ ε > 0, ‖p - p'‖ ≤ g ε := by
    intro ε hε
    obtain ⟨c, hc, hpc⟩ := near_of_hausdorff hη h hp'.1 hε
    have hcn : ‖c‖ ≤ ‖p'‖ + η + ε := by
      have : ‖c‖ ≤ ‖p'‖ + ‖p' - c‖ := by
        calc ‖c‖ = ‖p' - (p' - c)‖ := by abel_nf
          _ ≤ ‖p'‖ + ‖p' - c‖ := norm_sub_le _ _
      linarith
    have hq := qgrowth hC hp hc
    have hcp : ‖c - p‖ ≤ √((‖p'‖ + η + ε) ^ 2 - ‖p‖ ^ 2) := by
      rw [show ‖c - p‖ = √(‖c - p‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
      apply Real.sqrt_le_sqrt
      have : ‖c‖ ^ 2 ≤ (‖p'‖ + η + ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcn 2
      linarith
    calc ‖p - p'‖ ≤ ‖p' - c‖ + ‖c - p‖ := by
          calc ‖p - p'‖ = ‖(c - p') - (c - p)‖ := by abel_nf
            _ ≤ ‖c - p'‖ + ‖c - p‖ := norm_sub_le _ _
            _ = ‖p' - c‖ + ‖c - p‖ := by rw [norm_sub_rev]
      _ ≤ g ε := by simp only [g]; linarith
  have := le_of_forall_pos_cont hg key
  simpa [g] using this

theorem lem_projstab : Claims.lem_projstab := by
  intro E _ _ _ C C' p p' η _ _ hC hC' _ _ hη h hp hp'
  have h' : hausdorffEDist C' C ≤ ENNReal.ofReal η := by rwa [hausdorffEDist_comm]
  have h1 := norm_le_add hη h hp hp'
  have h2 := norm_le_add hη h' hp' hp
  have hi : |‖p‖ - ‖p'‖| ≤ η := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have ha := dist_le_half hη hC h' hp hp'
  have hb : ‖p - p'‖ ≤ η + √((‖p‖ + η) ^ 2 - ‖p'‖ ^ 2) := by
    rw [norm_sub_rev]; exact dist_le_half hη hC' h hp' hp
  have hii : ‖p - p'‖ ≤ η + min (√((‖p'‖ + η) ^ 2 - ‖p‖ ^ 2)) (√((‖p‖ + η) ^ 2 - ‖p'‖ ^ 2)) := by
    rcases min_choice (√((‖p'‖ + η) ^ 2 - ‖p‖ ^ 2)) (√((‖p‖ + η) ^ 2 - ‖p'‖ ^ 2)) with hm | hm <;>
      rw [hm] <;> assumption
  -- (iii): the better radicand is at most 2η·min(D,D') + η²
  have hmin : min (√((‖p'‖ + η) ^ 2 - ‖p‖ ^ 2)) (√((‖p‖ + η) ^ 2 - ‖p'‖ ^ 2)) ≤
      √(2 * η * min ‖p‖ ‖p'‖ + η ^ 2) := by
    rcases le_total ‖p‖ ‖p'‖ with hle | hle
    · rw [min_eq_left hle]
      refine le_trans (min_le_right _ _) (Real.sqrt_le_sqrt ?_)
      nlinarith [norm_nonneg p]
    · rw [min_eq_right hle]
      refine le_trans (min_le_left _ _) (Real.sqrt_le_sqrt ?_)
      nlinarith [norm_nonneg p']
  have hiii : ‖p - p'‖ ≤ η + √(2 * η * min ‖p‖ ‖p'‖ + η ^ 2) := by linarith
  have hsq : η + √(2 * η * min ‖p‖ ‖p'‖ + η ^ 2) ≤ √(2 * η * min ‖p‖ ‖p'‖) + 2 * η := by
    have hx : 0 ≤ 2 * η * min ‖p‖ ‖p'‖ := by
      have := le_min (norm_nonneg p) (norm_nonneg p'); positivity
    have : √(2 * η * min ‖p‖ ‖p'‖ + η ^ 2) ≤ √(2 * η * min ‖p‖ ‖p'‖) + η := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg (2 * η * min ‖p‖ ‖p'‖)]
    linarith
  exact ⟨hi, hii, hiii, hsq⟩

/-- Local sharpness on a convex set is global. -/
theorem sharp_global {C : Set E} {p : E} {θ ρ : ℝ} (hC : Convex ℝ C) (hpC : p ∈ C) (hρ : 0 < ρ)
    (hs : IsSharp C p θ ρ) : ∀ q ∈ C, ‖p‖ + θ * ‖q - p‖ ≤ ‖q‖ := by
  intro q hq
  by_cases hqp : q = p
  · subst hqp; simp
  have hd : 0 < ‖q - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hqp)
  set t := min 1 (ρ / ‖q - p‖) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos hρ hd)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hqt : p + t • (q - p) ∈ C := by
    have := hC hpC hq (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
    convert this using 1
    simp only [smul_sub]; module
  have hnear : ‖(p + t • (q - p)) - p‖ ≤ ρ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    calc t * ‖q - p‖ ≤ ρ / ‖q - p‖ * ‖q - p‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hd.le
      _ = ρ := div_mul_cancel₀ _ hd.ne'
  have hsh := hs _ hqt hnear
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hsh
  have hconv : ‖p + t • (q - p)‖ ≤ (1 - t) * ‖p‖ + t * ‖q‖ := by
    calc ‖p + t • (q - p)‖ = ‖(1 - t) • p + t • q‖ := by congr 1; module
      _ ≤ ‖(1 - t) • p‖ + ‖t • q‖ := norm_add_le _ _
      _ = (1 - t) * ‖p‖ + t * ‖q‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
          abs_of_pos ht0]
  have : t * (‖p‖ + θ * ‖q - p‖) ≤ t * ‖q‖ := by nlinarith
  exact le_of_mul_le_mul_left this ht0

theorem prop_sharprate_global : Claims.prop_sharprate_global := by
  intro E _ _ _ C C' p p' η θ ρ _ _ hC hC' _ _ hη h hp hp' hθ _ hρ hs
  have h' : hausdorffEDist C' C ≤ ENNReal.ofReal η := by rwa [hausdorffEDist_comm]
  have hglob := sharp_global hC hp.1 hρ hs
  have hD := norm_le_add hη h hp hp'
  let g : ℝ → ℝ := fun ε => η + ε + (2 * η + ε) / θ
  have hg : ContinuousAt g 0 := by fun_prop
  have key : ∀ ε > 0, ‖p - p'‖ ≤ g ε := by
    intro ε hε
    obtain ⟨c, hc, hpc⟩ := near_of_hausdorff hη h' hp'.1 hε
    have hcn : ‖c‖ ≤ ‖p'‖ + η + ε := by
      have : ‖c‖ ≤ ‖p'‖ + ‖p' - c‖ := by
        calc ‖c‖ = ‖p' - (p' - c)‖ := by abel_nf
          _ ≤ ‖p'‖ + ‖p' - c‖ := norm_sub_le _ _
      linarith
    have hs' := hglob c hc
    have hcp : ‖c - p‖ ≤ (2 * η + ε) / θ := by
      rw [le_div_iff₀ hθ]; nlinarith
    calc ‖p - p'‖ ≤ ‖p' - c‖ + ‖c - p‖ := by
          calc ‖p - p'‖ = ‖(c - p') - (c - p)‖ := by abel_nf
            _ ≤ ‖c - p'‖ + ‖c - p‖ := norm_sub_le _ _
            _ = ‖p' - c‖ + ‖c - p‖ := by rw [norm_sub_rev]
      _ ≤ g ε := by simp only [g]; linarith
  have := le_of_forall_pos_cont hg key
  simp only [g] at this
  have : η + 0 + (2 * η + 0) / θ = (1 + 2 / θ) * η := by field_simp; ring
  linarith

theorem prop_sharprate : Claims.prop_sharprate := by
  intro E _ _ _ C C' p p' η θ ρ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 _
  exact prop_sharprate_global E C C' p p' η θ ρ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem sharprate_proof_step_false : Claims.sharprate_proof_step_false := by
  intro h
  have := h 0 1 1 (le_refl _) zero_le_one zero_le_one (by norm_num)
  have h4 : √((1 + 1) ^ 2 - (0:ℝ) ^ 2) = 2 := by
    rw [show ((1:ℝ) + 1) ^ 2 - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h1 : √(2 * 1 * (0:ℝ) + 1 ^ 2) = 1 := by norm_num
  rw [h4, h1] at this
  norm_num at this

theorem ratioregime_limit : Claims.ratioregime_limit := by
  intro η _
  have hc : Continuous (fun D : ℝ => √(2 * η * D) + 2 * η) := by fun_prop
  have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ici 0))
  simpa using this

/-! ## Minkowski sums -/

theorem hausdorffDist_neg (B B' : Set E) : hausdorffDist (-B) (-B') = hausdorffDist B B' := by
  rw [← image_neg_eq_neg, ← image_neg_eq_neg]
  exact hausdorffDist_image isometry_neg

theorem hausdorffDist_add_le {A A' B B' : Set E} (hA : A.Nonempty) (hA' : A'.Nonempty)
    (hB : B.Nonempty) (hB' : B'.Nonempty) (bA : Bornology.IsBounded A)
    (bA' : Bornology.IsBounded A') (bB : Bornology.IsBounded B) (bB' : Bornology.IsBounded B') :
    hausdorffDist (A + B) (A' + B') ≤ hausdorffDist A A' + hausdorffDist B B' := by
  have hAA := hausdorffEDist_ne_top_of_nonempty_of_bounded hA hA' bA bA'
  have hBB := hausdorffEDist_ne_top_of_nonempty_of_bounded hB hB' bB bB'
  apply le_of_forall_pos_le_add
  intro ε hε
  have hr : 0 ≤ hausdorffDist A A' + hausdorffDist B B' + ε := by
    have := hausdorffDist_nonneg (s := A) (t := A'); have := hausdorffDist_nonneg (s := B) (t := B')
    linarith
  apply hausdorffDist_le_of_mem_dist hr
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    obtain ⟨a', ha', haa⟩ := exists_dist_lt_of_hausdorffDist_lt ha
      (lt_add_of_pos_right (hausdorffDist A A') (half_pos hε)) hAA
    obtain ⟨b', hb', hbb⟩ := exists_dist_lt_of_hausdorffDist_lt hb
      (lt_add_of_pos_right (hausdorffDist B B') (half_pos hε)) hBB
    refine ⟨a' + b', Set.add_mem_add ha' hb', ?_⟩
    calc dist (a + b) (a' + b') ≤ dist a a' + dist b b' := dist_add_add_le _ _ _ _
      _ ≤ _ := by linarith
  · rintro _ ⟨a', ha', b', hb', rfl⟩
    obtain ⟨a, ha, haa⟩ := exists_dist_lt_of_hausdorffDist_lt' ha'
      (lt_add_of_pos_right (hausdorffDist A A') (half_pos hε)) hAA
    obtain ⟨b, hb, hbb⟩ := exists_dist_lt_of_hausdorffDist_lt' hb'
      (lt_add_of_pos_right (hausdorffDist B B') (half_pos hε)) hBB
    refine ⟨a + b, Set.add_mem_add ha hb, ?_⟩
    calc dist (a' + b') (a + b) ≤ dist a' a + dist b' b := dist_add_add_le _ _ _ _
      _ = dist a a' + dist b b' := by rw [dist_comm a', dist_comm b']
      _ ≤ _ := by linarith

theorem lem_minkhaus : Claims.lem_minkhaus := by
  intro E _ _ A A' B B' hA hA' hB hB' bA bA' bB bB'
  have hneg := hausdorffDist_neg B B'
  refine ⟨hausdorffDist_add_le hA hA' hB hB' bA bA' bB bB', hneg, ?_⟩
  rw [sub_eq_add_neg A B, sub_eq_add_neg A' B', ← hneg]
  exact hausdorffDist_add_le hA hA' hB.neg hB'.neg bA bA' bB.neg bB'.neg

end StatFormal.TrimmedMMD.Projection

namespace StatFormal.TrimmedMMD.Projection

theorem ratioregime_limit_mid : Claims.ratioregime_limit_mid := by
  intro η _
  have hc : Continuous (fun D : ℝ => η + √(2 * η * D + η ^ 2)) := by fun_prop
  have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ici 0))
  have h0 : η + √(2 * η * 0 + η ^ 2) = 2 * η := by
    rw [mul_zero, zero_add, Real.sqrt_sq (by assumption)]; ring
  rwa [h0] at this

end StatFormal.TrimmedMMD.Projection
