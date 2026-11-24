import StatFormal.Archive.Wave24g.Statements

/-!
# Route — SB `cor:field-local` refutation, the deterministic gap (untrusted)

Elementary facts about `Q_b`, `F_b` and `ℝ¹`, a two-set lower bound for `W₂` (for every coupling,
`a² μ(A) ≤ ∫ d² dπ + a² ν(B)` when `A` and `Bᶜ` are `a`-separated) and the lower bound
`W₂((F_b)_#μ_b, (F_b)_#μ_b(· − δ)) ≥ δ^{3/4}/100`: with `t = √δ`, the reference puts mass `3t/16` on
`I = [½ − 3t/32, ½ + 3t/32]`, the shifted image puts mass `≤ t/16` on the `t/32`-neighbourhood `J` of `I`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set Filter
open scoped ENNReal NNReal Topology

namespace StatFormal.Wave24g

/-! ### `Q_b`, `F_b` -/

lemma clamp01_of_mem {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : clamp01 u = u := by
  unfold clamp01; rw [min_eq_left hu.2, max_eq_right hu.1]

lemma clamp01_mem (u : ℝ) : clamp01 u ∈ Icc (0 : ℝ) 1 := by
  unfold clamp01; exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

lemma Qb_of_mem {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : Qb u = (2 * u - 1) * |2 * u - 1| := by
  unfold Qb; rw [clamp01_of_mem hu]

lemma abs_Qb_le (u : ℝ) : |Qb u| ≤ 1 := by
  unfold Qb
  have h := clamp01_mem u
  have h1 : |2 * clamp01 u - 1| ≤ 1 := abs_le.2 ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [abs_mul, abs_abs]
  nlinarith [abs_nonneg (2 * clamp01 u - 1)]

lemma Qb_neg_of_lt {u : ℝ} (hu0 : 0 ≤ u) (hu : u < 1 / 2) : Qb u = -(1 - 2 * u) ^ 2 := by
  rw [Qb_of_mem ⟨hu0, by linarith⟩, abs_of_neg (by linarith)]; ring

lemma Qb_nonneg_of_ge {u : ℝ} (hu : 1 / 2 ≤ u) (hu1 : u ≤ 1) : Qb u = (2 * u - 1) ^ 2 := by
  rw [Qb_of_mem ⟨by linarith, hu1⟩, abs_of_nonneg (by linarith)]; ring

lemma Fb_of_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : Fb x = (1 + Real.sqrt x) / 2 := by
  unfold Fb
  rw [min_eq_left hx1, max_eq_right hx, show max 0 (min (-x) 1) = 0 from
    max_eq_left (le_trans (min_le_left _ _) (by linarith)), Real.sqrt_zero, sub_zero]

lemma Fb_of_nonpos {x : ℝ} (hx : x ≤ 0) (hx1 : -1 ≤ x) : Fb x = (1 - Real.sqrt (-x)) / 2 := by
  unfold Fb
  rw [min_eq_left (show -x ≤ 1 by linarith), max_eq_right (show (0 : ℝ) ≤ -x by linarith),
    show max 0 (min x 1) = 0 from max_eq_left (le_trans (min_le_left _ _) hx), Real.sqrt_zero, add_zero]

lemma Fb_Qb {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : Fb (Qb u) = u := by
  rcases lt_or_ge u (1 / 2) with h | h
  · rw [Qb_neg_of_lt hu.1 h, Fb_of_nonpos (by nlinarith) (by nlinarith [hu.1]), neg_neg,
      Real.sqrt_sq (by linarith)]
    ring
  · rw [Qb_nonneg_of_ge h hu.2, Fb_of_nonneg (by positivity) (by nlinarith [hu.2]),
      Real.sqrt_sq (by linarith)]
    ring

lemma continuous_clamp01 : Continuous clamp01 := by
  unfold clamp01; fun_prop

lemma continuous_Qb : Continuous Qb := by
  unfold Qb; have := continuous_clamp01; fun_prop

lemma continuous_Fb : Continuous Fb := by
  unfold Fb
  exact ((continuous_const.add (Real.continuous_sqrt.comp (continuous_const.max
    (continuous_id.min continuous_const)))).sub (Real.continuous_sqrt.comp (continuous_const.max
    (continuous_neg.min continuous_const)))).div_const _

lemma abs_clamp01_sub (u w : ℝ) : |clamp01 u - clamp01 w| ≤ |u - w| := by
  unfold clamp01
  rw [max_comm 0 (min u 1), max_comm 0 (min w 1)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
  simp

lemma abs_mul_abs_sub (a b : ℝ) : abs (a * |a| - b * |b|) ≤ (|a| + |b|) * |a - b| := by
  rcases abs_cases a with ⟨ha, ha0⟩ | ⟨ha, ha0⟩ <;> rcases abs_cases b with ⟨hb, hb0⟩ | ⟨hb, hb0⟩ <;>
    rw [ha, hb]
  · rw [show a * a - b * b = (a + b) * (a - b) by ring, abs_mul, abs_of_nonneg (by linarith)]
  · rw [abs_le]; constructor <;> cases abs_cases (a - b) <;> nlinarith
  · rw [abs_le]; constructor <;> cases abs_cases (a - b) <;> nlinarith
  · rw [show a * -a - b * -b = -((a + b) * (a - b)) by ring, abs_neg, abs_mul,
      abs_of_nonpos (show a + b ≤ 0 by linarith)]
    nlinarith [abs_nonneg (a - b)]

lemma abs_Qb_sub (u w : ℝ) : |Qb u - Qb w| ≤ 4 * |u - w| := by
  unfold Qb
  have hu := clamp01_mem u
  have hw := clamp01_mem w
  have h1 : |2 * clamp01 u - 1| ≤ 1 := abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h2 : |2 * clamp01 w - 1| ≤ 1 := abs_le.2 ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have h3 : |(2 * clamp01 u - 1) - (2 * clamp01 w - 1)| ≤ 2 * |u - w| := by
    rw [show (2 * clamp01 u - 1) - (2 * clamp01 w - 1) = 2 * (clamp01 u - clamp01 w) by ring, abs_mul,
      abs_two]
    exact mul_le_mul_of_nonneg_left (abs_clamp01_sub u w) zero_le_two
  refine (abs_mul_abs_sub _ _).trans ?_
  calc (|2 * clamp01 u - 1| + |2 * clamp01 w - 1|) * |(2 * clamp01 u - 1) - (2 * clamp01 w - 1)|
      ≤ 2 * (2 * |u - w|) := mul_le_mul (by linarith) h3 (abs_nonneg _) zero_le_two
    _ = 4 * |u - w| := by ring

/-! ### `ℝ¹` -/

@[simp] lemma toE1_apply (t : ℝ) (i : Fin 1) : toE1 t i = t := rfl

lemma dist_E1 (x y : E1) : dist x y = |x 0 - y 0| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.sqrt_sq_eq_abs, Real.dist_eq, abs_abs]

lemma edist_E1 (x y : E1) : edist x y = ENNReal.ofReal |x 0 - y 0| := by
  rw [edist_dist, dist_E1]

lemma continuous_toE1 : Continuous toE1 :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_id)

lemma measurable_toE1 : Measurable toE1 := continuous_toE1.measurable

lemma continuous_coord : Continuous fun x : E1 => x 0 :=
  (continuous_apply 0).comp (PiLp.continuous_ofLp 2 _)

lemma measurable_coord : Measurable fun x : E1 => x 0 := continuous_coord.measurable

lemma continuous_SbE : Continuous SbE := continuous_toE1.comp (continuous_Fb.comp continuous_coord)

lemma continuous_QbE : Continuous QbE := continuous_toE1.comp (continuous_Qb.comp continuous_coord)

lemma measurable_SbE : Measurable SbE := continuous_SbE.measurable

lemma measurable_QbE : Measurable QbE := continuous_QbE.measurable

@[simp] lemma add_E1_apply (x y : E1) : (x + y) 0 = x 0 + y 0 := rfl

lemma measurableSet_coord {s : Set ℝ} (hs : MeasurableSet s) : MeasurableSet {x : E1 | x 0 ∈ s} :=
  measurable_coord hs

lemma lipschitz_QbE : LipschitzWith 4 QbE := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_E1, dist_E1]
  simp only [QbE, toE1_apply, NNReal.coe_ofNat]
  exact abs_Qb_sub _ _

/-! ### The measures -/

instance : IsProbabilityMeasure unif01 :=
  ⟨by simp [unif01, Real.volume_Icc]⟩

instance : IsProbabilityMeasure gammaU := by unfold gammaU; infer_instance

instance : IsProbabilityMeasure muB := by unfold muB; infer_instance

instance (δ : ℝ) (μ : Measure E1) [IsProbabilityMeasure μ] : IsProbabilityMeasure (shiftLaw δ μ) := by
  unfold shiftLaw; infer_instance

lemma unif01_apply (s : Set ℝ) : unif01 s = volume (s ∩ Icc 0 1) :=
  Measure.restrict_apply' measurableSet_Icc

lemma unif01_map_apply {f : ℝ → E1} (hf : Measurable f) {S : Set E1} (hS : MeasurableSet S) :
    unif01.map f S = volume (f ⁻¹' S ∩ Icc 0 1) := by
  rw [Measure.map_apply hf hS, unif01_apply]

lemma toE1_add (a b : ℝ) : toE1 a + toE1 b = toE1 (a + b) := rfl

lemma muB_map_SbE : muB.map SbE = gammaU := by
  unfold muB gammaU
  rw [Measure.map_map measurable_SbE (measurable_toE1.comp continuous_Qb.measurable)]
  refine Measure.map_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  simp [SbE, Fb_Qb hu]

lemma shiftLaw_muB (δ : ℝ) : shiftLaw δ muB = unif01.map fun u => toE1 (Qb u + δ) := by
  unfold shiftLaw muB
  rw [Measure.map_map (measurable_add_const _) (measurable_toE1.comp continuous_Qb.measurable)]
  rfl

lemma shiftLaw_muB_map_SbE (δ : ℝ) :
    (shiftLaw δ muB).map SbE = unif01.map fun u => toE1 (Fb (Qb u + δ)) := by
  rw [shiftLaw_muB, Measure.map_map (f := fun u => toE1 (Qb u + δ)) measurable_SbE
    (measurable_toE1.comp (continuous_Qb.measurable.add_const _))]
  rfl

/-! ### A two-set lower bound for `W₂` -/

lemma w2_two_set {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] {μ ν : Measure X} {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (a b : ℝ≥0∞) (hsep : ∀ x ∈ A, ∀ y, y ∉ B → a ≤ edist x y)
    (hνB : a ^ 2 * ν B ≠ ⊤) (hb : b ^ 2 + a ^ 2 * ν B ≤ a ^ 2 * μ A) :
    b ≤ wassersteinEDist 2 μ ν := by
  refine le_wassersteinEDist fun π hπ => ?_
  have hd : Measurable fun z : X × X => edist z.1 z.2 := measurable_edist
  have hpt : ∀ z : X × X, a ^ 2 * (Prod.fst ⁻¹' A).indicator 1 z ≤
      edist z.1 z.2 ^ 2 + a ^ 2 * (Prod.snd ⁻¹' B).indicator 1 z := by
    intro z
    by_cases h1 : z.1 ∈ A
    · by_cases h2 : z.2 ∈ B
      · simp [h1, h2]
      · have := hsep _ h1 _ h2
        simp only [Set.indicator, mem_preimage, h1, h2, ite_true, ite_false, Pi.one_apply, mul_one,
          mul_zero, add_zero]
        gcongr
    · simp [h1]
  have h1 : ∫⁻ z, a ^ 2 * (Prod.fst ⁻¹' A).indicator 1 z ∂π = a ^ 2 * μ A := by
    rw [lintegral_const_mul _ (measurable_one.indicator (measurable_fst hA)),
      lintegral_indicator_one (measurable_fst hA), ← Measure.fst_apply hA, hπ.fst_eq]
  have h2 : ∫⁻ z, a ^ 2 * (Prod.snd ⁻¹' B).indicator 1 z ∂π = a ^ 2 * ν B := by
    rw [lintegral_const_mul _ (measurable_one.indicator (measurable_snd hB)),
      lintegral_indicator_one (measurable_snd hB), ← Measure.snd_apply hB, hπ.snd_eq]
  have hint : a ^ 2 * μ A ≤ ∫⁻ z, edist z.1 z.2 ^ 2 ∂π + a ^ 2 * ν B := by
    rw [← h1, ← h2]
    calc ∫⁻ z, a ^ 2 * (Prod.fst ⁻¹' A).indicator 1 z ∂π
        ≤ ∫⁻ z, (edist z.1 z.2 ^ 2 + a ^ 2 * (Prod.snd ⁻¹' B).indicator 1 z) ∂π := lintegral_mono hpt
      _ = _ := lintegral_add_right _
          (measurable_const.mul (measurable_one.indicator (measurable_snd hB)))
  have hsq : b ^ 2 ≤ ∫⁻ z, edist z.1 z.2 ^ 2 ∂π :=
    (ENNReal.add_le_add_iff_right hνB).1 (hb.trans hint)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hd.aestronglyMeasurable]
  simp only [enorm_eq_self, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc b = (b ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num
    _ ≤ _ := ENNReal.rpow_le_rpow hsq (by norm_num)

/-! ### The gap -/

lemma Fb_eq_of_nonneg {z : ℝ} (hz : 0 ≤ z) : Fb z = (1 + Real.sqrt (min z 1)) / 2 := by
  unfold Fb
  rw [max_eq_right (le_min hz zero_le_one),
    max_eq_left (min_le_of_left_le (neg_nonpos.2 hz)), Real.sqrt_zero, sub_zero]

lemma Fb_eq_of_nonpos {z : ℝ} (hz : z ≤ 0) : Fb z = (1 - Real.sqrt (min (-z) 1)) / 2 := by
  unfold Fb
  rw [max_eq_left (min_le_of_left_le hz), max_eq_right (le_min (neg_nonneg.2 hz) zero_le_one),
    Real.sqrt_zero, add_zero]

/-- `|F_b(z) − ½| ≤ t/8` forces `|z| ≤ t²/16` (for `t ≤ 1`). -/
lemma abs_le_of_Fb_mem {z t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (h : Fb z ∈ Icc (1 / 2 - t / 8) (1 / 2 + t / 8)) : |z| ≤ t ^ 2 / 16 := by
  have key : ∀ m : ℝ, 0 ≤ m → Real.sqrt m ≤ t / 4 → m ≤ t ^ 2 / 16 := fun m hm hs => by
    nlinarith [Real.sq_sqrt hm, Real.sqrt_nonneg m]
  rcases le_or_gt 0 z with hz | hz
  · rw [Fb_eq_of_nonneg hz] at h
    have hm := key (min z 1) (le_min hz zero_le_one) (by linarith [h.2])
    rw [abs_of_nonneg hz]
    rcases le_or_gt z 1 with hz1 | hz1
    · rwa [min_eq_left hz1] at hm
    · rw [min_eq_right hz1.le] at hm; nlinarith
  · rw [Fb_eq_of_nonpos hz.le] at h
    have hm := key (min (-z) 1) (le_min (by linarith) zero_le_one) (by linarith [h.1])
    rw [abs_of_neg hz]
    rcases le_or_gt (-z) 1 with hz1 | hz1
    · rwa [min_eq_left hz1] at hm
    · rw [min_eq_right hz1.le] at hm; nlinarith

/-- The preimage of `J` under `u ↦ F_b(Q_b(u) + δ)` inside `[0,1]` has length `t/16`. -/
lemma preimage_J_subset {δ t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hδ : δ = t ^ 2) :
    (fun u => Fb (Qb u + δ)) ⁻¹' Icc (1 / 2 - t / 8) (1 / 2 + t / 8) ∩ Icc 0 1 ⊆
      Icc ((1 - 17 * t / 16) / 2) ((1 - 15 * t / 16) / 2) := by
  rintro u ⟨hJ, hu⟩
  have hz := abs_le_of_Fb_mem ht ht1 hJ
  rw [abs_le] at hz
  rcases lt_or_ge u (1 / 2) with h | h
  · rw [Qb_neg_of_lt hu.1 h] at hz
    have hw : 0 < 1 - 2 * u := by linarith
    have hup : 1 - 2 * u ≤ 17 * t / 16 := by
      by_contra hc; push Not at hc; nlinarith [mul_lt_mul'' hc hc (by positivity) (by positivity)]
    have hlo : 15 * t / 16 ≤ 1 - 2 * u := by
      by_contra hc; push Not at hc; nlinarith [mul_lt_mul'' hc hc hw.le hw.le]
    exact ⟨by linarith, by linarith⟩
  · rw [Qb_nonneg_of_ge h hu.2] at hz
    nlinarith [sq_nonneg (2 * u - 1)]

lemma rpow_three_quarters_sq {δ t : ℝ} (ht : 0 ≤ t) (hδ : δ = t ^ 2) : (δ ^ (3 / 4 : ℝ)) ^ 2 = t ^ 3 := by
  rw [hδ, ← Real.rpow_two t, ← Real.rpow_mul ht, ← Real.rpow_natCast, ← Real.rpow_mul ht,
    ← Real.rpow_natCast]
  norm_num

/-- The core bound, `W₂(Unif[0,1], (u ↦ F_b(Q_b u + δ))_#Unif[0,1]) ≥ δ^{3/4}/100`. -/
lemma gap_core {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal (δ ^ (3 / 4 : ℝ) / 100) ≤
      wassersteinEDist 2 gammaU (unif01.map fun u => toE1 (Fb (Qb u + δ))) := by
  set t := Real.sqrt δ with ht_def
  have ht : 0 < t := Real.sqrt_pos.2 hδ
  have htδ : δ = t ^ 2 := (Real.sq_sqrt hδ.le).symm
  have ht1 : t ≤ 1 := by rw [ht_def]; exact Real.sqrt_le_one.mpr hδ1
  have hG : Measurable fun u => toE1 (Fb (Qb u + δ)) :=
    measurable_toE1.comp ((continuous_Fb.comp (continuous_Qb.add continuous_const)).measurable)
  have hA := measurableSet_coord (measurableSet_Icc (a := 1 / 2 - 3 * t / 32) (b := 1 / 2 + 3 * t / 32))
  have hB := measurableSet_coord (measurableSet_Icc (a := 1 / 2 - t / 8) (b := 1 / 2 + t / 8))
  have hμA : gammaU {x : E1 | x 0 ∈ Icc (1 / 2 - 3 * t / 32) (1 / 2 + 3 * t / 32)} =
      ENNReal.ofReal (3 * t / 16) := by
    unfold gammaU
    rw [unif01_map_apply measurable_toE1 hA]
    have : toE1 ⁻¹' {x : E1 | x 0 ∈ Icc (1 / 2 - 3 * t / 32) (1 / 2 + 3 * t / 32)} ∩ Icc 0 1 =
        Icc (1 / 2 - 3 * t / 32) (1 / 2 + 3 * t / 32) := by
      ext u
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, toE1_apply, mem_Icc]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, by linarith [h.1], by linarith [h.2]⟩
    rw [this, Real.volume_Icc]; congr 1; ring
  have hνB : (unif01.map fun u => toE1 (Fb (Qb u + δ))) {y : E1 | y 0 ∈ Icc (1 / 2 - t / 8) (1 / 2 + t / 8)} ≤
      ENNReal.ofReal (t / 16) := by
    rw [unif01_map_apply hG hB]
    calc volume ((fun u => toE1 (Fb (Qb u + δ))) ⁻¹' {y : E1 | y 0 ∈ Icc (1 / 2 - t / 8) (1 / 2 + t / 8)} ∩ Icc 0 1)
        ≤ volume (Icc ((1 - 17 * t / 16) / 2) ((1 - 15 * t / 16) / 2)) :=
          measure_mono (preimage_J_subset ht ht1 htδ)
      _ = ENNReal.ofReal (t / 16) := by rw [Real.volume_Icc]; congr 1; ring
  refine w2_two_set hA hB (ENNReal.ofReal (t / 32)) _ ?_ ?_ ?_
  · intro x hx y hy
    simp only [mem_ofPred_eq, mem_Icc, not_and_or, not_le] at hx hy
    rw [edist_E1]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases hy with hy | hy
    · exact le_abs.2 (Or.inl (by linarith [hx.1]))
    · exact le_abs.2 (Or.inr (by linarith [hx.2]))
  · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hνB)
  · rw [hμA]
    calc ENNReal.ofReal (δ ^ (3 / 4 : ℝ) / 100) ^ 2 + ENNReal.ofReal (t / 32) ^ 2 *
          (unif01.map fun u => toE1 (Fb (Qb u + δ))) {y : E1 | y 0 ∈ Icc (1 / 2 - t / 8) (1 / 2 + t / 8)}
        ≤ ENNReal.ofReal (δ ^ (3 / 4 : ℝ) / 100) ^ 2 + ENNReal.ofReal (t / 32) ^ 2 * ENNReal.ofReal (t / 16) := by
          gcongr
      _ = ENNReal.ofReal ((δ ^ (3 / 4 : ℝ) / 100) ^ 2 + (t / 32) ^ 2 * (t / 16)) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity)]
      _ ≤ ENNReal.ofReal ((t / 32) ^ 2 * (3 * t / 16)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_pow, rpow_three_quarters_sq ht.le htδ]
          have : 0 < t ^ 3 := by positivity
          nlinarith
      _ = ENNReal.ofReal (t / 32) ^ 2 * ENNReal.ofReal (3 * t / 16) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]

theorem field_local_gap_lower : Claims.field_local_gap_lower := by
  intro δ hδ hδ1
  rw [muB_map_SbE, shiftLaw_muB_map_SbE]
  exact gap_core hδ hδ1

end StatFormal.Wave24g
