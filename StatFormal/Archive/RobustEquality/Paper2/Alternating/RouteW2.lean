import StatFormal.Archive.RobustEquality.Paper2.Alternating.RouteVertex
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Route: `W₂²(h#P̂₀, h#P̂₁)` is the minimum over the transport polytope (finite centres)

Paper 2, `lem:delta-inf` (`paper2/main.tex:296`), first sentence, for finitely supported laws and any
measurable rule `h`: with Tau Ceti's `wassersteinEDist`,
`W₂(h#P̂₀, h#P̂₁) = (min_{γ ∈ Π(P̂₀, P̂₁)} Σ γ_ij (h(x⁰_i) − h(x¹_j))²)^{1/2}`.

* `≤`: a plan `γ` of the atoms gives the coupling `Σ γ_ij δ_{(h x⁰_i, h x¹_j)}` of the projected laws;
* `≥`: a coupling `π` of the projected laws is concentrated on the finite grid of projected values;
  splitting each cell mass `π{(s,t)}` over the atoms projecting to `s` and to `t` in proportion to
  their weights gives a plan of the atoms with the same cost (the lift of the paper's proof).
-/

noncomputable section
open Finset MeasureTheory TauCeti
open scoped ENNReal

namespace StatFormal.RobustEquality.Paper2.Alternating.Route

variable {n₀ n₁ : ℕ}

/-- The finitely supported law `Σ_i a_i δ_{x_i}`. -/
def centre {K : Type*} [MeasurableSpace K] {n : ℕ} (a : Fin n → ℝ) (x : Fin n → K) : Measure K :=
  ∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)

lemma sum_smul_dirac_apply {K ι : Type*} [MeasurableSpace K] [Fintype ι] (c : ι → ℝ≥0∞)
    (z : ι → K) {S : Set K} (hS : MeasurableSet S) :
    (∑ i, c i • Measure.dirac (z i)) S = ∑ i, c i * S.indicator 1 (z i) := by
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul]

lemma centre_apply {K : Type*} [MeasurableSpace K] {n : ℕ} (a : Fin n → ℝ) (x : Fin n → K)
    {S : Set K} (hS : MeasurableSet S) :
    centre a x S = ∑ i, ENNReal.ofReal (a i) * S.indicator 1 (x i) :=
  sum_smul_dirac_apply _ _ hS

lemma map_centre {K : Type*} [MeasurableSpace K] {n : ℕ} (a : Fin n → ℝ) (x : Fin n → K)
    {h : K → ℝ} (hh : Measurable h) : (centre a x).map h = centre a (fun i => h (x i)) := by
  ext S hS
  rw [Measure.map_apply hh hS, centre_apply _ _ (hh hS), centre_apply _ _ hS]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hx : h (x i) ∈ S
  · simp [Set.indicator_apply, hx]
  · simp [Set.indicator_apply, hx]

lemma centre_univ {K : Type*} [MeasurableSpace K] {n : ℕ} {a : Fin n → ℝ} (x : Fin n → K)
    (h0 : ∀ i, 0 ≤ a i) (h1 : ∑ i, a i = 1) : centre a x Set.univ = 1 := by
  rw [centre_apply _ _ MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => h0 i), h1, ENNReal.ofReal_one]

lemma centre_finite {K : Type*} [MeasurableSpace K] {n : ℕ} {a : Fin n → ℝ} (x : Fin n → K)
    (h0 : ∀ i, 0 ≤ a i) (h1 : ∑ i, a i = 1) : IsFiniteMeasure (centre a x) :=
  ⟨by rw [centre_univ x h0 h1]; exact ENNReal.one_lt_top⟩

/-- Weight of the atoms projecting to `s`. -/
def wt {n : ℕ} (a : Fin n → ℝ) (u : Fin n → ℝ) (s : ℝ) : ℝ := ∑ i ∈ univ.filter (fun i => u i = s), a i

lemma centre_singleton {n : ℕ} {a : Fin n → ℝ} (u : Fin n → ℝ) (h0 : ∀ i, 0 ≤ a i) (s : ℝ) :
    centre a u {s} = ENNReal.ofReal (wt a u s) := by
  rw [centre_apply _ _ (measurableSet_singleton s), wt,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => h0 i), Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : u i = s
  · simp [h]
  · simp [h, Set.indicator_apply]

lemma wt_nonneg {n : ℕ} {a : Fin n → ℝ} (u : Fin n → ℝ) (h0 : ∀ i, 0 ≤ a i) (s : ℝ) :
    0 ≤ wt a u s := Finset.sum_nonneg fun i _ => h0 i

lemma le_wt {n : ℕ} {a : Fin n → ℝ} (u : Fin n → ℝ) (h0 : ∀ i, 0 ≤ a i) (i : Fin n) :
    a i ≤ wt a u (u i) :=
  Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)

/-- Splitting a function of the projection over the fibres. -/
lemma fiber_sum {n : ℕ} (w : Fin n → ℝ) (f : Fin n → ℝ) (H : ℝ → ℝ)
    (hH : ∀ s, wt w f s = 0 → H s = 0) :
    ∑ i, w i * H (f i) / wt w f (f i) = ∑ s ∈ univ.image f, H s := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := univ.image f)
    (fun i _ => Finset.mem_image_of_mem f (Finset.mem_univ i))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_congr rfl (g := fun i => w i * H s / wt w f s)
    (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), ← Finset.sum_div, ← Finset.sum_mul]
  change wt w f s * H s / wt w f s = H s
  by_cases hW : wt w f s = 0
  · simp [hW, hH s hW]
  · field_simp

lemma edist_sq (s t : ℝ) : (‖edist s t‖ₑ) ^ ((2 : ℝ≥0∞).toReal) = ENNReal.ofReal ((s - t) ^ 2) := by
  rw [enorm_eq_self, edist_dist, Real.dist_eq, ENNReal.toReal_ofNat,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  congr 1
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]

/-! ### Upper bound: a plan of the atoms is a coupling of the projected laws -/

section Upper

variable {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ}

/-- The coupling of the projected laws induced by a plan of the atoms. -/
def planMeasure (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ) (γ : Fin n₀ → Fin n₁ → ℝ) : Measure (ℝ × ℝ) :=
  ∑ q : Fin n₀ × Fin n₁, ENNReal.ofReal (γ q.1 q.2) • Measure.dirac (u q.1, v q.2)

lemma planMeasure_isCoupling (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ) {γ : Fin n₀ → Fin n₁ → ℝ}
    (hγ : γ ∈ Plans a₀ a₁) : IsCoupling (planMeasure u v γ) (centre a₀ u) (centre a₁ v) := by
  refine isCoupling_of_measure_prod_univ_of_measure_univ_prod (fun S hS => ?_) (fun T hT => ?_)
  · rw [planMeasure, sum_smul_dirac_apply _ _ (hS.prod MeasurableSet.univ), centre_apply _ _ hS,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∀ j, (S ×ˢ Set.univ).indicator (1 : ℝ × ℝ → ℝ≥0∞) (u i, v j) = S.indicator 1 (u i) := by
      intro j; by_cases h : u i ∈ S <;> simp [Set.indicator_apply, h]
    simp only [this]
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hγ.1 i j), hγ.2.1 i]
  · rw [planMeasure, sum_smul_dirac_apply _ _ (MeasurableSet.univ.prod hT), centre_apply _ _ hT,
      Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ∀ i, (Set.univ ×ˢ T).indicator (1 : ℝ × ℝ → ℝ≥0∞) (u i, v j) = T.indicator 1 (v j) := by
      intro i; by_cases h : v j ∈ T <;> simp [Set.indicator_apply, h]
    simp only [this]
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hγ.1 i j), hγ.2.2 j]

lemma pcost_nonneg (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ) {γ : Fin n₀ → Fin n₁ → ℝ}
    (hγ : ∀ i j, 0 ≤ γ i j) : 0 ≤ pcost u v γ :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hγ i j) (sq_nonneg _)

lemma eLpNorm_planMeasure (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ) {γ : Fin n₀ → Fin n₁ → ℝ}
    (hγ : ∀ i j, 0 ≤ γ i j) :
    eLpNorm (fun z : ℝ × ℝ => edist z.1 z.2) 2 (planMeasure u v γ) =
      ENNReal.ofReal (√(pcost u v γ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    measurable_edist.aestronglyMeasurable, planMeasure,
    lintegral_finset_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  simp only [edist_sq]
  rw [Finset.sum_congr rfl (fun q _ => (ENNReal.ofReal_mul (hγ q.1 q.2)).symm),
    ← ENNReal.ofReal_sum_of_nonneg (fun q _ => mul_nonneg (hγ q.1 q.2) (sq_nonneg _)),
    ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg
      (Finset.sum_nonneg fun q _ => mul_nonneg (hγ q.1 q.2) (sq_nonneg _)) (by norm_num),
    Real.sqrt_eq_rpow, pcost, Fintype.sum_prod_type]

end Upper

/-! ### Lower bound: a coupling of the projected laws lifts to a plan of the atoms -/

section Lower

variable {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ}
variable (h00 : ∀ i, 0 ≤ a₀ i) (h01 : ∑ i, a₀ i = 1) (h10 : ∀ j, 0 ≤ a₁ j)
  (h11 : ∑ j, a₁ j = 1)

lemma centre_compl_image {n : ℕ} {a : Fin n → ℝ} (u : Fin n → ℝ) :
    centre a u ((↑(univ.image u) : Set ℝ)ᶜ) = 0 := by
  rw [centre_apply _ _ (Finset.measurableSet _).compl]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : u i ∈ (↑(univ.image u) : Set ℝ) := by simp
  simp [Set.indicator_apply, this]

include h00 h01 h10 h11 in
theorem lift_coupling (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ) {π : Measure (ℝ × ℝ)}
    (hπ : IsCoupling π (centre a₀ u) (centre a₁ v)) :
    ∃ γ ∈ Plans a₀ a₁, eLpNorm (fun z : ℝ × ℝ => edist z.1 z.2) 2 π =
      ENNReal.ofReal (√(pcost u v γ)) := by
  classical
  haveI := centre_finite u h00 h01
  haveI : IsFiniteMeasure π := hπ.isFiniteMeasure
  set U := univ.image u with hU
  set V := univ.image v with hV
  -- `π` is concentrated on the grid `U × V`
  have hnull : π ((↑(U ×ˢ V) : Set (ℝ × ℝ))ᶜ) = 0 := by
    have hsub : ((↑(U ×ˢ V) : Set (ℝ × ℝ))ᶜ) ⊆
        ((↑U : Set ℝ)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ (↑V : Set ℝ)ᶜ) := by
      intro p hp
      simp only [Finset.coe_product, Set.mem_compl_iff, Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, trivial⟩
      · exact Or.inr ⟨trivial, hp⟩
    refine le_antisymm ((measure_mono hsub).trans ((measure_union_le _ _).trans ?_)) bot_le
    rw [hπ.measure_prod_univ (Finset.measurableSet _).compl,
      hπ.measure_univ_prod (Finset.measurableSet _).compl, centre_compl_image, centre_compl_image,
      add_zero]
  have hrestr : π.restrict (↑(U ×ˢ V)) = π := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    exact hnull
  have hint : ∀ g : ℝ × ℝ → ℝ≥0∞, ∫⁻ p, g p ∂π = ∑ p ∈ U ×ˢ V, g p * π {p} := by
    intro g
    conv_lhs => rw [← hrestr]
    exact lintegral_finset _ _
  have hmeas : ∀ S : Set (ℝ × ℝ), MeasurableSet S → π S = ∑ p ∈ U ×ˢ V, S.indicator 1 p * π {p} := by
    intro S hS
    rw [← hint, lintegral_indicator_one hS]
  -- real masses
  set m : ℝ → ℝ → ℝ := fun s t => (π {(s, t)}).toReal with hm
  have hm0 : ∀ s t, 0 ≤ m s t := fun s t => ENNReal.toReal_nonneg
  have hmof : ∀ s t, π {(s, t)} = ENNReal.ofReal (m s t) := fun s t =>
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  -- row and column masses
  have hrow : ∀ s ∈ U, ∑ t ∈ V, m s t = wt a₀ u s := by
    intro s hs
    have h1 := hπ.measure_prod_univ (measurableSet_singleton s)
    rw [hmeas _ ((measurableSet_singleton s).prod MeasurableSet.univ), Finset.sum_product,
      centre_singleton u h00] at h1
    have h2 : ∀ s' ∈ U, ∑ t ∈ V, ({s} ×ˢ Set.univ).indicator (1 : ℝ × ℝ → ℝ≥0∞) (s', t) *
        π {(s', t)} = if s' = s then ∑ t ∈ V, π {(s, t)} else 0 := by
      intro s' _
      by_cases h : s' = s
      · subst h; simp [Set.indicator_apply]
      · simp [Set.indicator_apply, h]
    rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq' U s, if_pos hs] at h1
    have h3 := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_sum (fun t _ => measure_ne_top _ _),
      ENNReal.toReal_ofReal (wt_nonneg u h00 s)] at h3
    exact h3
  have hcol : ∀ t ∈ V, ∑ s ∈ U, m s t = wt a₁ v t := by
    intro t ht
    have h1 := hπ.measure_univ_prod (measurableSet_singleton t)
    rw [hmeas _ (MeasurableSet.univ.prod (measurableSet_singleton t)), Finset.sum_product,
      centre_singleton v h10] at h1
    have h2 : ∀ s ∈ U, ∑ t' ∈ V, (Set.univ ×ˢ {t}).indicator (1 : ℝ × ℝ → ℝ≥0∞) (s, t') *
        π {(s, t')} = π {(s, t)} := by
      intro s _
      rw [Finset.sum_eq_single_of_mem t ht]
      · simp [Set.indicator_apply]
      · intro t' _ h; simp [Set.indicator_apply, h]
    rw [Finset.sum_congr rfl h2] at h1
    have h3 := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_sum (fun s _ => measure_ne_top _ _),
      ENNReal.toReal_ofReal (wt_nonneg v h10 t)] at h3
    exact h3
  have hmA : ∀ s t, m s t ≤ wt a₀ u s := by
    intro s t
    have h1 : π {(s, t)} ≤ π ({s} ×ˢ Set.univ) := measure_mono (by simp)
    rw [hπ.measure_prod_univ (measurableSet_singleton s), centre_singleton u h00] at h1
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 h1 |>.trans
      (by rw [ENNReal.toReal_ofReal (wt_nonneg u h00 s)])
  have hmB : ∀ s t, m s t ≤ wt a₁ v t := by
    intro s t
    have h1 : π {(s, t)} ≤ π (Set.univ ×ˢ {t}) := measure_mono (by simp)
    rw [hπ.measure_univ_prod (measurableSet_singleton t), centre_singleton v h10] at h1
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 h1 |>.trans
      (by rw [ENNReal.toReal_ofReal (wt_nonneg v h10 t)])
  have hA0 : ∀ s t, wt a₀ u s = 0 → m s t = 0 := fun s t h =>
    le_antisymm ((hmA s t).trans h.le) (hm0 s t)
  have hB0 : ∀ s t, wt a₁ v t = 0 → m s t = 0 := fun s t h =>
    le_antisymm ((hmB s t).trans h.le) (hm0 s t)
  -- the lifted plan
  set γ : Fin n₀ → Fin n₁ → ℝ := fun i j =>
    a₀ i * a₁ j * m (u i) (v j) / (wt a₀ u (u i) * wt a₁ v (v j)) with hγdef
  have hγrow : ∀ i j, γ i j = a₀ i / wt a₀ u (u i) * (a₁ j * m (u i) (v j) / wt a₁ v (v j)) := by
    intro i j; simp only [hγdef]; ring
  have hγcol : ∀ i j, γ i j = a₁ j / wt a₁ v (v j) * (a₀ i * m (u i) (v j) / wt a₀ u (u i)) := by
    intro i j; simp only [hγdef]; ring
  have hplan : γ ∈ Plans a₀ a₁ := by
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · simp only [hγdef]
      exact div_nonneg (mul_nonneg (mul_nonneg (h00 i) (h10 j)) (hm0 _ _))
        (mul_nonneg (wt_nonneg u h00 _) (wt_nonneg v h10 _))
    · simp only [hγrow]
      rw [← Finset.mul_sum]
      have := fiber_sum a₁ v (fun t => m (u i) t) (fun t ht => hB0 _ _ ht)
      simp only [mul_div_assoc] at this ⊢
      rw [this, hrow _ (Finset.mem_image_of_mem u (Finset.mem_univ i))]
      by_cases hW : wt a₀ u (u i) = 0
      · have h0 : a₀ i = 0 := le_antisymm ((le_wt u h00 i).trans hW.le) (h00 i)
        simp [hW, h0]
      · field_simp
    · simp only [hγcol]
      rw [← Finset.mul_sum]
      have := fiber_sum a₀ u (fun s => m s (v j)) (fun s hs => hA0 _ _ hs)
      simp only [mul_div_assoc] at this ⊢
      rw [this, hcol _ (Finset.mem_image_of_mem v (Finset.mem_univ j))]
      by_cases hW : wt a₁ v (v j) = 0
      · have h0 : a₁ j = 0 := le_antisymm ((le_wt v h10 j).trans hW.le) (h10 j)
        simp [hW, h0]
      · field_simp
  refine ⟨γ, hplan, ?_⟩
  -- the cost
  have hcost : pcost u v γ = ∑ s ∈ U, ∑ t ∈ V, m s t * (s - t) ^ 2 := by
    have step1 : ∀ i, ∑ j, γ i j * (u i - v j) ^ 2 =
        a₀ i / wt a₀ u (u i) * ∑ t ∈ V, m (u i) t * (u i - t) ^ 2 := by
      intro i
      have := fiber_sum a₁ v (fun t => m (u i) t * (u i - t) ^ 2)
        (fun t ht => by simp [hB0 _ _ ht])
      rw [← this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hγrow]; ring
    rw [pcost, Finset.sum_congr rfl (fun i _ => step1 i)]
    have := fiber_sum a₀ u (fun s => ∑ t ∈ V, m s t * (s - t) ^ 2)
      (fun s hs => Finset.sum_eq_zero fun t _ => by simp [hA0 _ _ hs])
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    measurable_edist.aestronglyMeasurable, hint, Finset.sum_product]
  simp only [edist_sq, hmof]
  rw [Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl
      (fun t _ => (ENNReal.ofReal_mul (sq_nonneg (s - t))).symm))]
  rw [Finset.sum_congr rfl (fun s _ => (ENNReal.ofReal_sum_of_nonneg
      (fun t _ => mul_nonneg (sq_nonneg (s - t)) (hm0 s t))).symm),
    ← ENNReal.ofReal_sum_of_nonneg (fun s _ => Finset.sum_nonneg
      (fun t _ => mul_nonneg (sq_nonneg (s - t)) (hm0 s t))),
    ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun s _ =>
      Finset.sum_nonneg fun t _ => mul_nonneg (sq_nonneg (s - t)) (hm0 s t)) (by norm_num),
    Real.sqrt_eq_rpow, hcost]
  congr 2
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  ring

end Lower

/-! ### The identity -/

section Identity

variable {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ}
variable (h00 : ∀ i, 0 ≤ a₀ i) (h01 : ∑ i, a₀ i = 1) (h10 : ∀ j, 0 ≤ a₁ j)
  (h11 : ∑ j, a₁ j = 1)

include h00 h01 h10 h11 in
theorem pcost_isLeast_exists (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ) :
    ∃ c, IsLeast (pcost u v '' Plans a₀ a₁) c := by
  obtain ⟨γ, hq⟩ := quantile_exists h00 h01 h10 h11 u v
  exact ⟨pcost u v γ, ⟨γ, hq.1, rfl⟩, by
    rintro _ ⟨γ', hγ', rfl⟩; exact quantile_optimal h00 h01 h10 h11 hq γ' hγ'⟩

include h00 h01 h10 h11 in
theorem W2_projected (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ) {c : ℝ}
    (hc : IsLeast (pcost u v '' Plans a₀ a₁) c) :
    wassersteinEDist 2 (centre a₀ u) (centre a₁ v) = ENNReal.ofReal (√c) := by
  obtain ⟨⟨γ, hγ, rfl⟩, hlow⟩ := hc
  apply le_antisymm
  · refine (wassersteinEDist_le (planMeasure_isCoupling u v hγ) 2).trans_eq ?_
    exact eLpNorm_planMeasure u v hγ.1
  · refine le_iInf₂ fun π hπ => ?_
    obtain ⟨γ', hγ', heq⟩ := lift_coupling h00 h01 h10 h11 u v hπ
    rw [heq]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hlow ⟨γ', hγ', rfl⟩))

end Identity

end StatFormal.RobustEquality.Paper2.Alternating.Route
