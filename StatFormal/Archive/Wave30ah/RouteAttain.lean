import StatFormal.Archive.Wave30ah.Statements
import StatFormal.Archive.Wave30z.RouteRay
import StatFormal.Archive.Wave11b.RouteAttain

/-!
# Route — wave 30ah: attainment in `thm:boundary` (i), (ii), the nearest pair, and the sign of the limit (untrusted)

* `H` is lower semicontinuous on `𝔹_r` for EVERY continuous path `v`: `H(f) = β min_{t ∈ q(f)} v(f, t)` with
  `q(f)` the argmin set of the jointly continuous `cvObj`; along `f_n → f`, minimisers `t_n ∈ q(f_n)` have a
  limit point `t` (compact `[−κ, κ]`), `t ∈ q(f)` (closed graph), so `H(f) ≤ β v(f, t) = lim H(f_n)`.
* So `L(g) = c_P H_P(−g) + c_Q H_Q(g)` is lsc (`c ≥ 0`) and attains its minimum on any nonempty compact set:
  `G*` (closed in the compact `𝔹_r`, `g ↦ −h_A(−g) − h_B(g)` continuous) and `K° ∩ 𝔹_r` (closed, contains `0`).
* the nearest pair is Wave 11b `exists_attain_Dpop`; the sign of the limit of (ii) is `H(0) = 0` a.s.
  (Wave 30z `Hfun_smul` with `c = 0` under the a.s. linear consistency `ae_linCons`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30ah

open StatFormal.TrimmedMMD.Concentration (region empirical)
open StatFormal.TrimmedMMD.Unconditional (setDist Dpop Demp)
open StatFormal.Wave30v (supFun supportFn Ball ballNeg polarSet coneHull continuous_ballNeg)
open StatFormal.Wave30z

section LSC
variable {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {φ : 𝒳 → E} {κ α : ℝ}

lemma continuous_cvObj_joint (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (μ : Measure 𝒳) [IsFiniteMeasure μ] :
    Continuous fun p : E × ℝ => cvObj φ α μ p.1 p.2 :=
  continuous_snd.add (continuous_const.mul (continuous_integral_hinge hφ hκ μ))

/-- `|H(f)| ≤ β ‖v‖`. -/
lemma abs_Hfun_le (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα1 : α < 1) (μ : Measure 𝒳)
    [IsProbabilityMeasure μ] (side : Idx1 E κ → Idx2 E κ) (v : C(Idx2 E κ, ℝ)) (f : Ball E) :
    |Hfun φ α μ κ side v f| ≤ 1 / (1 - α) * ‖v‖ := by
  have hκ0 := kappa_nonneg hκ μ
  have hβ : 0 ≤ 1 / (1 - α) := le_of_lt (one_div_pos.2 (by linarith))
  have hne := (argminSet_nonempty hφ hκ hκ0 α μ (f : E)).image fun t => v (side (f, t))
  have hb : ∀ y ∈ (fun t => v (side (f, t))) '' argminSet φ α μ κ (f : E), |y| ≤ ‖v‖ := by
    rintro _ ⟨t, -, rfl⟩; exact v.norm_coe_le_norm _
  have hbdd : BddBelow ((fun t => v (side (f, t))) '' argminSet φ α μ κ (f : E)) :=
    ⟨-‖v‖, fun y hy => (abs_le.1 (hb y hy)).1⟩
  have h1 : -‖v‖ ≤ sInf ((fun t => v (side (f, t))) '' argminSet φ α μ κ (f : E)) :=
    le_csInf hne fun y hy => (abs_le.1 (hb y hy)).1
  obtain ⟨y, hy⟩ := hne
  have h2 : sInf ((fun t => v (side (f, t))) '' argminSet φ α μ κ (f : E)) ≤ ‖v‖ :=
    (csInf_le hbdd hy).trans (abs_le.1 (hb y hy)).2
  unfold Hfun
  rw [abs_mul, abs_of_nonneg hβ]
  exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨h1, h2⟩) hβ

/-- Lower semicontinuity of `f ↦ H(f)` for every continuous path. -/
lemma lsc_Hfun (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα1 : α < 1) (μ : Measure 𝒳)
    [IsProbabilityMeasure μ] (side : Idx1 E κ → Idx2 E κ) (hside : Continuous side) (v : C(Idx2 E κ, ℝ)) :
    LowerSemicontinuous (Hfun φ α μ κ side v) := by
  have hκ0 := kappa_nonneg hκ μ
  have hβ : 0 < 1 / (1 - α) := one_div_pos.2 (by linarith)
  have hvc : Continuous fun p : Ball E × Icc (-κ) κ => v (side p) := v.continuous.comp hside
  intro f y hy
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨fs, hfs, hfsy⟩ := exists_seq_forall_of_frequently hcon
  simp only [not_lt] at hfsy
  -- minimisers along the sequence
  have hmin : ∀ n, ∃ t ∈ argminSet φ α μ κ (fs n : E), Hfun φ α μ κ side v (fs n) = 1 / (1 - α) * v (side (fs n, t)) := by
    intro n
    obtain ⟨t, ht, he, -⟩ := argminSet_attain (α := α) hφ hκ hκ0 μ (fs n : E) (fun t => v (side (fs n, t)))
      (hvc.comp (continuous_const.prodMk continuous_id))
    exact ⟨t, ht, by unfold Hfun; rw [← he]⟩
  choose ts hts hHts using hmin
  obtain ⟨t, -, ψ, hψ, htsψ⟩ := (isCompact_univ (X := Icc (-κ) κ)).tendsto_subseq (x := ts) fun n => mem_univ _
  have hfsψ : Tendsto (fs ∘ ψ) atTop (𝓝 f) := hfs.comp hψ.tendsto_atTop
  have hpair : Tendsto (fun n => ((fs ∘ ψ) n, (ts ∘ ψ) n)) atTop (𝓝 (f, t)) := hfsψ.prodMk_nhds htsψ
  -- the limit point is a minimiser at `f`
  have hcv := continuous_cvObj_joint (α := α) hφ hκ μ
  have hcvc : Continuous fun p : Ball E × Icc (-κ) κ => cvObj φ α μ (p.1 : E) (p.2 : ℝ) :=
    hcv.comp ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
  have htmem : t ∈ argminSet φ α μ κ (f : E) := by
    rw [mem_argminSet_iff]
    intro t'
    have hc' : Continuous fun p : Ball E × Icc (-κ) κ => cvObj φ α μ (p.1 : E) (t' : ℝ) :=
      hcv.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_const)
    have h1 := (hcvc.tendsto _).comp hpair
    have h2 := (hc'.tendsto _).comp hpair
    exact le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun n => (mem_argminSet_iff.1 (hts (ψ n))) t')
  -- the bound
  have hlim : Tendsto (fun n => 1 / (1 - α) * v (side ((fs ∘ ψ) n, (ts ∘ ψ) n))) atTop
      (𝓝 (1 / (1 - α) * v (side (f, t)))) :=
    ((hvc.tendsto _).comp hpair).const_mul _
  have hle : 1 / (1 - α) * v (side (f, t)) ≤ y :=
    le_of_tendsto hlim (Eventually.of_forall fun n => by
      have := hfsy (ψ n); rw [hHts (ψ n)] at this; exact this)
  have hHf : Hfun φ α μ κ side v f ≤ 1 / (1 - α) * v (side (f, t)) := by
    unfold Hfun
    refine mul_le_mul_of_nonneg_left ?_ hβ.le
    have hK : IsCompact (argminSet φ α μ κ (f : E)) := (isClosed_argminSet hφ hκ μ (f : E)).isCompact
    exact csInf_le (hK.image (hvc.comp (continuous_const.prodMk continuous_id))).bddBelow ⟨t, htmem, rfl⟩
  linarith

/-- The functional `L(g) = c_P H_P(−g) + c_Q H_Q(g)` is lsc for `c_P, c_Q ≥ 0`. -/
lemma lsc_negBoundaryLim (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα1 : α < 1)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {cP cQ : ℝ} (hcP : 0 ≤ cP) (hcQ : 0 ≤ cQ)
    (v : C(Idx2 E κ, ℝ)) : LowerSemicontinuous fun g => -boundaryLim φ α P Q κ cP cQ v g := by
  have h1 : LowerSemicontinuous fun g : Ball E => cP * Hfun φ α P κ Sum.inl v (ballNeg g) :=
    (continuous_const_mul cP).comp_lowerSemicontinuous
      ((lsc_Hfun hφ hκ hα1 P Sum.inl continuous_inl v).comp continuous_ballNeg)
      (fun a b hab => mul_le_mul_of_nonneg_left hab hcP)
  have h2 : LowerSemicontinuous fun g : Ball E => cQ * Hfun φ α Q κ Sum.inr v g :=
    (continuous_const_mul cQ).comp_lowerSemicontinuous (lsc_Hfun hφ hκ hα1 Q Sum.inr continuous_inr v)
      (fun a b hab => mul_le_mul_of_nonneg_left hab hcQ)
  have := h1.add h2
  convert this using 2 with g
  simp only [boundaryLim]; ring

/-- Attainment of the supremum of `boundaryLim` over a nonempty compact set. -/
lemma exists_isGreatest_boundaryLim (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα1 : α < 1)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {cP cQ : ℝ} (hcP : 0 ≤ cP) (hcQ : 0 ≤ cQ)
    (v : C(Idx2 E κ, ℝ)) {S : Set (Ball E)} (hne : S.Nonempty) (hS : IsCompact S) :
    ∃ g ∈ S, IsGreatest (boundaryLim φ α P Q κ cP cQ v '' S) (boundaryLim φ α P Q κ cP cQ v g) ∧
      sSup (boundaryLim φ α P Q κ cP cQ v '' S) = boundaryLim φ α P Q κ cP cQ v g := by
  obtain ⟨g, hg, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hS
    ((lsc_negBoundaryLim hφ hκ hα1 P Q hcP hcQ v).lowerSemicontinuousOn S)
  have hG : IsGreatest (boundaryLim φ α P Q κ cP cQ v '' S) (boundaryLim φ α P Q κ cP cQ v g) := by
    refine ⟨⟨g, hg, rfl⟩, ?_⟩
    rintro _ ⟨g', hg', rfl⟩
    have := hmin hg'
    simp only [mem_ofPred_eq] at this
    linarith
  exact ⟨g, hg, hG, hG.csSup_eq⟩

lemma isCompact_ball_set {S : Set (Ball E)} (hS : IsClosed S) : IsCompact S := by
  have : CompactSpace (Ball E) := isCompact_iff_compactSpace.1 (isCompact_closedBall (0 : E) 1)
  exact hS.isCompact

lemma isClosed_Gstar (hκ : ∀ x, ‖φ x‖ ≤ κ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hα0 : 0 ≤ α) (hα1 : α < 1) : IsClosed (Gstar φ α P Q) := by
  have hA := continuous_supportFn (isBounded_region P (φ := φ) (α := α) hκ) (region_nonempty P hα0 hα1)
  have hB := continuous_supportFn (isBounded_region Q (φ := φ) (α := α) hκ) (region_nonempty Q hα0 hα1)
  have hF : Continuous fun g : Ball E => -supportFn (region φ α P) (-(g : E)) - supportFn (region φ α Q) (g : E) :=
    (hA.comp continuous_subtype_val.neg).neg.sub (hB.comp continuous_subtype_val)
  have : Gstar φ α P Q = ⋂ g' : Ball E, {g : Ball E | -supportFn (region φ α P) (-(g' : E)) - supportFn (region φ α Q) (g' : E) ≤
      -supportFn (region φ α P) (-(g : E)) - supportFn (region φ α Q) (g : E)} := by
    ext g; simp only [Gstar, mem_iInter, mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun g' => isClosed_le continuous_const hF

lemma isClosed_polar_ball (K : Set E) : IsClosed {g : Ball E | (g : E) ∈ polarSet K} := by
  have : {g : Ball E | (g : E) ∈ polarSet K} = ⋂ x ∈ K, {g : Ball E | ⟪(g : E), x⟫ ≤ 0} := by
    ext g; simp [polarSet]
  rw [this]
  exact isClosed_biInter fun x _ => isClosed_le (continuous_subtype_val.inner continuous_const) continuous_const

end LSC

theorem boundary_max_every : Claims.boundary_max_every := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ cP cQ v hφ hκ hα0 hα1 hcP hcQ
  have hne := Gstar_nonempty hφ hκ hα0 hα1 P Q
  have hK := isCompact_ball_set (isClosed_Gstar hκ P Q hα0 hα1)
  exact ⟨hne, hK, exists_isGreatest_boundaryLim hφ hκ hα1 P Q hcP hcQ v hne hK⟩

theorem boundary_max_contact : Claims.boundary_max_contact := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ cP cQ v hφ hκ hα0 hα1 hcP hcQ
  intro S
  have hne : S.Nonempty := ⟨⟨0, mem_closedBall_self zero_le_one⟩, fun x _ => by
    show ⟪(0 : E), x⟫ ≤ 0; rw [inner_zero_left]⟩
  have hK : IsCompact S := isCompact_ball_set (isClosed_polar_ball _)
  exact ⟨hne, hK, exists_isGreatest_boundaryLim hφ hκ hα1 P Q hcP hcQ v hne hK⟩

theorem boundary_nearest : Claims.boundary_nearest := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ hφ hκ hα0 hα1
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact StatFormal.Wave11b.exists_attain_Dpop hφ hκ hα0 hα1

theorem boundary_contact_nonneg : Claims.boundary_contact_nonneg := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ cP cQ Ω' _ μ' _ 𝔾 hφ hκ hα0 hα1 h𝔾
  filter_upwards [ae_linCons h𝔾] with ω' hL
  set v := 𝔾 ω'
  set K := closure (coneHull (region φ α Q - region φ α P))
  let g0 : Ball E := ⟨0, mem_closedBall_self zero_le_one⟩
  have hH0 : ∀ g : Ball E, (g : E) = 0 → boundaryLim φ α P Q κ cP cQ v g = 0 := by
    intro g hg
    have h1 := Hfun_smul hφ hκ hα0 hα1 P Sum.inl continuous_inl v (relProp_inl v hL) (ballNeg g) (ballNeg g)
      le_rfl zero_le_one (by change -(g : E) = (0 : ℝ) • -(g : E); rw [hg, zero_smul, neg_zero])
    have h2 := Hfun_smul hφ hκ hα0 hα1 Q Sum.inr continuous_inr v (relProp_inr v hL) g g
      le_rfl zero_le_one (by rw [hg, zero_smul])
    unfold boundaryLim; rw [h1, h2]; ring
  have h0mem : g0 ∈ {g : Ball E | (g : E) ∈ polarSet K} := fun x _ => by
    show ⟪(0 : E), x⟫ ≤ 0; rw [inner_zero_left]
  have hbdd : BddAbove (boundaryLim φ α P Q κ cP cQ v '' {g : Ball E | (g : E) ∈ polarSet K}) := by
    refine ⟨|cP| * (1 / (1 - α) * ‖v‖) + |cQ| * (1 / (1 - α) * ‖v‖), ?_⟩
    rintro _ ⟨g, -, rfl⟩
    have h1 := abs_Hfun_le hφ hκ hα1 P Sum.inl v (ballNeg g)
    have h2 := abs_Hfun_le hφ hκ hα1 Q Sum.inr v g
    have e1 := mul_le_mul (le_refl |cP|) h1 (abs_nonneg _) (abs_nonneg _)
    have e2 := mul_le_mul (le_refl |cQ|) h2 (abs_nonneg _) (abs_nonneg _)
    rw [← abs_mul] at e1 e2
    simp only [boundaryLim]
    have := neg_abs_le (cP * Hfun φ α P κ Sum.inl v (ballNeg g))
    have := neg_abs_le (cQ * Hfun φ α Q κ Sum.inr v g)
    linarith
  refine ⟨?_, fun hK0 => ?_⟩
  · rw [← hH0 g0 rfl]; exact le_csSup hbdd ⟨g0, h0mem, rfl⟩
  · have hS : {g : Ball E | (g : E) ∈ polarSet K} = {g0} := by
      ext g; simp only [mem_ofPred_eq, mem_singleton_iff]
      rw [hK0]; constructor
      · intro h; exact Subtype.ext h
      · intro h; rw [h]; rfl
    rw [hS, image_singleton, csSup_singleton, hH0 g0 rfl]

end StatFormal.Wave30ah
