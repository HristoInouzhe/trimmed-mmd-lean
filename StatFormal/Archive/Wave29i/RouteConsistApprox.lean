import StatFormal.Archive.Wave29i.RouteConsistPool

/-!
# Route — ICL `cor:consistency`, the approximation step (untrusted)

* Quantiser on a `δ`-net `z` of `supp P₀`: the cells `A_i = B(z_i, δ) \ ⋃_{j<i} B(z_j, δ)` (Wave 26b), the index map
  `x ↦ i` with `x ∈ A_i` (measurable), `q(x) = z_{i(x)}`: `d(q x, x) < δ` on `supp P₀`, and for a distinct pool
  `q x = q y ⇒ d(x, y) < 2δ`; `μ ∘ q⁻¹ = μ_w` with `w_i = μ(A_i)`.
* Along such quantisers with `δ_k → 0`, `R(μ ∘ q_k⁻¹) → R(μ)` for every admissible `μ` (the Foundations stability
  of `Π_μ`, for the risk with `f = L(x; ·)` and for the coverage with `f = K(x, t_s)`; dominated convergence in the
  query), and `μ ∘ q_k⁻¹ = μ_{w_k}` with `w_k ∈ Δ^(M)` eventually.
* Hence on the almost-sure pool event (distinct, in `supp P₀`, eventually dense; nested pools),
  `limsup_n inf_{Δ^(M)} R(μ_w) ≤ R⋆`: `consist_approx`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

namespace StatFormal.Wave29i

open StatFormal.Wave11b (distinctSet ctxLaw Admissible jSwor collision)
open StatFormal.Wave26b (poolLaw riskIid wMeas)
open StatFormal.Wave20a (rhoC PhiC)
open StatFormal.ICL (InDeltaM)
open StatFormal.ICL.Joint (ProbVec)
open StatFormal.Foundations.SworLaw

variable {Z : Type} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

namespace ConsistR

/-! ### The quantiser on a net -/

section Quant
variable {n : ℕ}

/-- The cells `A_i = B(z_i, δ) \ ⋃_{j<i} B(z_j, δ)`. -/
def qCell (z : Fin n → Z) (δ : ℝ) : Fin n → Set Z := disjointed fun i => Metric.ball (z i) δ

open Classical in
/-- The cell index of `x` (`i₀` off the cells). -/
def qIdx (z : Fin n → Z) (δ : ℝ) (i0 : Fin n) (x : Z) : Fin n :=
  if h : ∃ i, x ∈ qCell z δ i then Classical.choose h else i0

lemma qCell_measurable (z : Fin n → Z) (δ : ℝ) (i : Fin n) : MeasurableSet (qCell z δ i) :=
  StatFormal.Wave26b.measurableSet_disjointed_fin (fun _ => measurableSet_ball) i

lemma qCell_eq_of_mem {z : Fin n → Z} {δ : ℝ} {x : Z} {i j : Fin n} (hi : x ∈ qCell z δ i)
    (hj : x ∈ qCell z δ j) : i = j := by
  by_contra hne
  exact Set.disjoint_left.1 (disjoint_disjointed (fun i => Metric.ball (z i) δ) hne) hi hj

lemma qIdx_of_mem {z : Fin n → Z} {δ : ℝ} {i0 i : Fin n} {x : Z} (hx : x ∈ qCell z δ i) : qIdx z δ i0 x = i := by
  have h : ∃ i, x ∈ qCell z δ i := ⟨i, hx⟩
  unfold qIdx; rw [dif_pos h]
  exact qCell_eq_of_mem (Classical.choose_spec h) hx

lemma measurable_qIdx (z : Fin n → Z) (δ : ℝ) (i0 : Fin n) : Measurable (qIdx z δ i0) := by
  refine measurable_to_countable' fun i => ?_
  have hA := qCell_measurable z δ
  have h : qIdx z δ i0 ⁻¹' {i} = qCell z δ i ∪ ((⋃ j, qCell z δ j)ᶜ ∩ {_x | i0 = i}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_iUnion, not_exists, Set.mem_setOf_eq]
    by_cases hx : ∃ j, x ∈ qCell z δ j
    · obtain ⟨j, hj⟩ := hx
      rw [qIdx_of_mem hj]
      constructor
      · rintro rfl; exact Or.inl hj
      · rintro (hi | ⟨hno, _⟩)
        · exact qCell_eq_of_mem hj hi
        · exact absurd hj (hno j)
    · push_neg at hx
      have hq : qIdx z δ i0 x = i0 := by
        unfold qIdx; rw [dif_neg (by push_neg; exact hx)]
      rw [hq]
      constructor
      · intro h'; exact Or.inr ⟨hx, h'⟩
      · rintro (hi | ⟨_, h'⟩)
        · exact absurd hi (hx i)
        · exact h'
  rw [h]
  exact (hA i).union ((MeasurableSet.iUnion hA).compl.inter (MeasurableSet.const _))

lemma mem_qCell_of_cover {z : Fin n → Z} {δ : ℝ} {x : Z} (hx : ∃ i, dist x (z i) < δ) : ∃ i, x ∈ qCell z δ i := by
  obtain ⟨i, hi⟩ := hx
  have : x ∈ ⋃ i, Metric.ball (z i) δ := mem_iUnion.2 ⟨i, Metric.mem_ball.2 hi⟩
  rw [← iUnion_disjointed] at this
  exact mem_iUnion.1 this

lemma dist_qIdx_lt {z : Fin n → Z} {δ : ℝ} {i0 : Fin n} {x : Z} (hx : ∃ i, dist x (z i) < δ) :
    dist x (z (qIdx z δ i0 x)) < δ := by
  obtain ⟨i, hi⟩ := mem_qCell_of_cover hx
  rw [qIdx_of_mem hi]
  exact Metric.mem_ball.1 (disjointed_subset _ i hi)

/-- `μ ∘ q⁻¹ = μ_w` with `w_i = μ(A_i)`. -/
lemma map_quantiser (μ : Measure Z) [IsProbabilityMeasure μ] (z : Fin n → Z) (δ : ℝ) (i0 : Fin n) :
    ∃ w : Fin n → ℝ, ProbVec w ∧ μ.map (fun x => z (qIdx z δ i0 x)) = poolLaw z w := by
  have hm := measurable_qIdx z δ i0
  refine ⟨fun i => μ.real (qIdx z δ i0 ⁻¹' {i}), ⟨fun i => measureReal_nonneg, ?_⟩, ?_⟩
  · rw [sum_measureReal_preimage_singleton _ fun i _ => hm (measurableSet_singleton i)]
    simp
  · rw [StatFormal.Wave26b.poolLaw_eq_map]
    have h1 : μ.map (fun x => z (qIdx z δ i0 x)) = (μ.map (qIdx z δ i0)).map z :=
      (Measure.map_map measurable_from_top hm).symm
    rw [h1]
    congr 1
    refine Measure.ext_of_singleton fun i => ?_
    rw [Measure.map_apply hm (measurableSet_singleton i), StatFormal.Wave26b.wMeas_singleton, ofReal_measureReal]

end Quant

/-! ### `R` along quantisers -/

lemma abs_log_le_of_mem {a b y : ℝ} (ha : 0 < a) (hy : a ≤ y ∧ y ≤ b) :
    |Real.log y| ≤ max |Real.log a| |Real.log b| := by
  have h1 := Real.log_le_log ha hy.1
  have h2 := Real.log_le_log (ha.trans_le hy.1) hy.2
  rw [abs_le]
  constructor
  · have := neg_abs_le (Real.log a); have := le_max_left |Real.log a| |Real.log b|; linarith
  · have := le_abs_self (Real.log b); have := le_max_right |Real.log a| |Real.log b|; linarith

theorem consistRisk_tendsto_quantise {M : ℕ} (hM : 1 ≤ M) {L : Z → (Fin M → Z) → ℝ} {Kk : Z → Z → ℝ}
    {BL Kmin Kmax : ℝ} (lcov : ℝ)
    (hL : ContinuousOn (fun p : Z × (Fin M → Z) => L p.1 p.2) (univ ×ˢ distinctSet M))
    (hLb : ∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) (hK : Continuous (Function.uncurry Kk)) (hKmin : 0 < Kmin)
    (hKb : ∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax) (P₀ : Measure Z) [IsProbabilityMeasure P₀]
    (μ : Measure Z) [IsProbabilityMeasure μ] {S : Set Z} (hS : MeasurableSet S) (hμS : μ Sᶜ = 0)
    (hpos : 0 < Measure.pi (fun _ : Fin M => μ) (distinctSet M)) {q : ℕ → Z → Z} {δ : ℕ → ℝ}
    (hq : IsQuantiser S q δ) :
    Tendsto (fun k => consistRisk L Kk lcov P₀ (μ.map (q k))) atTop (𝓝 (consistRisk L Kk lcov P₀ μ)) := by
  have hev := eventually_pos_quantise (M := M) μ hS hμS hq hpos
  have hG : ∀ x, Tendsto (fun k => consistG L (μ.map (q k)) x) atTop (𝓝 (consistG L μ x)) := fun x =>
    tendsto_integral_cond_quantise μ hS hμS hq hpos (continuousOn_slot hL x) (C := BL)
      (fun t => by rw [abs_of_nonneg (hLb x t).1]; exact (hLb x t).2)
  have hρ : ∀ x, Tendsto (fun k => rhoC Kk (consistMarg (μ.map (q k)) M) x) atTop
      (𝓝 (rhoC Kk (consistMarg μ M) x)) := by
    intro x
    have hKx : Continuous fun z' => Kk x z' := hK.comp (Continuous.prodMk continuous_const continuous_id)
    have e : ∀ k, rhoC Kk (consistMarg (μ.map (q k)) M) x =
        (M : ℝ)⁻¹ * ∑ s : Fin M, ∫ t, Kk x (t s) ∂(ctxLaw (μ.map (q k)) M) := fun k =>
      integral_consistMarg _ M hKx
    rw [show (fun k => rhoC Kk (consistMarg (μ.map (q k)) M) x) =
      fun k => (M : ℝ)⁻¹ * ∑ s : Fin M, ∫ t, Kk x (t s) ∂(ctxLaw (μ.map (q k)) M) from funext e]
    unfold rhoC
    rw [integral_consistMarg _ M hKx]
    refine Tendsto.const_mul _ (tendsto_finset_sum _ fun s _ => ?_)
    exact tendsto_integral_cond_quantise μ hS hμS hq hpos (f := fun t => Kk x (t s)) (C := Kmax)
      (hKx.comp (continuous_apply s)).continuousOn
      (fun t => by rw [abs_of_pos (hKmin.trans_le (hKb x _).1)]; exact (hKb x _).2)
  unfold consistRisk
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)
  · refine tendsto_integral_filter_of_dominated_convergence (fun _ => BL) ?_ ?_ (integrable_const _)
      (Eventually.of_forall hG)
    · exact Eventually.of_forall fun k => (continuous_consistG hL hLb (μ.map (q k))).aestronglyMeasurable
    · filter_upwards [hev] with k hk
      haveI := ctxLaw_isProb (μ := μ.map (q k)) hk
      exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (consistG_mem hLb _ x).1]; exact (consistG_mem hLb _ x).2
  · unfold PhiC
    refine Tendsto.neg ?_
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => max |Real.log Kmin| |Real.log Kmax|) ?_ ?_
      (integrable_const _) ?_
    · exact Eventually.of_forall fun k => (Real.measurable_log.comp
        (StatFormal.Wave26b.continuous_rhoC hK hKb hKmin _).measurable).aestronglyMeasurable
    · filter_upwards [hev] with k hk
      haveI := ctxLaw_isProb (μ := μ.map (q k)) hk
      haveI := consistMarg_univ (μ.map (q k)) hM
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs]
      exact abs_log_le_of_mem hKmin (StatFormal.Wave26b.rhoC_mem hK hKb (consistMarg (μ.map (q k)) M) x)
    · haveI := ctxLaw_isProb hpos
      haveI := consistMarg_univ μ hM
      refine Eventually.of_forall fun x => ?_
      have hm := StatFormal.Wave26b.rhoC_mem hK hKb (consistMarg μ M) x
      exact ((Real.continuousAt_log (hKmin.trans_le hm.1).ne').tendsto).comp (hρ x)

/-- `w ∈ Δ^(M)` as soon as `μ_w^{⊗M}(D_M) > 0` (distinct pool). -/
lemma inDeltaM_of_pos {n M : ℕ} {z : Fin n → Z} (hz : Function.Injective z) {w : Fin n → ℝ} (hw : ProbVec w)
    (h : 0 < Measure.pi (fun _ : Fin M => poolLaw z w) (distinctSet M)) : InDeltaM w M := by
  classical
  refine ⟨hw.1, hw.2, ?_⟩
  rw [pi_poolLaw_eq, distinctSet_eq, sum_dirac_apply _ _ (measurableSet_injective M)] at h
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  have hind : {t' : Fin M → Z | Function.Injective t'}.indicator (1 : (Fin M → Z) → ℝ≥0∞) (z ∘ t) ≠ 0 :=
    right_ne_zero_of_mul ht
  have htinj : Function.Injective t := by
    by_contra hni
    exact hind (indicator_of_notMem (fun h' => hni (Function.Injective.of_comp h')) _)
  have hprod : ∏ s, ENNReal.ofReal (w (t s)) ≠ 0 := left_ne_zero_of_mul ht
  have hpos : ∀ s, w (t s) ≠ 0 := by
    intro s hs
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ s) (by rw [hs, ENNReal.ofReal_zero]))
  have hsub : Finset.univ.image t ⊆ Finset.univ.filter fun j => w j ≠ 0 := by
    intro j hj
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hj
    simp [hpos s]
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ htinj, Finset.card_univ, Fintype.card_fin] at this
  exact this

/-- The approximation step for one admissible `μ`: on a distinct pool in `supp P₀`, eventually dense, all large
pools carry `w ∈ Δ^(M)` with `R(μ_w) ≤ R(μ) + ε`. -/
lemma approx_pool_swor {M : ℕ} (hM : 1 ≤ M) {L : Z → (Fin M → Z) → ℝ} {Kk : Z → Z → ℝ} {BL Kmin Kmax : ℝ}
    (lcov : ℝ) (hL : ContinuousOn (fun p : Z × (Fin M → Z) => L p.1 p.2) (univ ×ˢ distinctSet M))
    (hLb : ∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) (hK : Continuous (Function.uncurry Kk)) (hKmin : 0 < Kmin)
    (hKb : ∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax) (P₀ : Measure Z) [IsProbabilityMeasure P₀]
    (μ : Measure Z) (hadm : Admissible P₀ M μ) (z : ℕ → Z) (hzinj : Function.Injective z)
    (hdense : ∀ δ > 0, ∃ N, ∀ x ∈ P₀.support, ∃ i < N, dist x (z i) < δ) :
    ∀ ε > 0, ∃ N₀, ∀ n ≥ N₀, ∃ w : Fin n → ℝ, InDeltaM w M ∧
      consistRisk L Kk lcov P₀ (poolLaw (fun i : Fin n => z i) w) ≤ consistRisk L Kk lcov P₀ μ + ε := by
  intro ε hε
  obtain ⟨hμp, hμS, hpos⟩ := hadm
  haveI := hμp
  by_contra hcon
  push_neg at hcon
  have hk : ∀ k : ℕ, ∃ n : ℕ, ∃ _ : 0 < n,
      (∀ w : Fin n → ℝ, InDeltaM w M →
        consistRisk L Kk lcov P₀ μ + ε < consistRisk L Kk lcov P₀ (poolLaw (fun i : Fin n => z i) w)) ∧
      ∀ x ∈ P₀.support, ∃ i : Fin n, dist x (z i) < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨N, hN⟩ := hdense (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨n, hnN, hbad⟩ := hcon (N + 1)
    refine ⟨n, by omega, hbad, fun x hx => ?_⟩
    obtain ⟨i, hi, hd⟩ := hN x hx
    exact ⟨⟨i, by omega⟩, hd⟩
  choose n hn hbad hcov using hk
  set q : ℕ → Z → Z := fun k x =>
    (fun i : Fin (n k) => z i) (qIdx (fun i : Fin (n k) => z i) (1 / ((k : ℝ) + 1)) ⟨0, hn k⟩ x) with hqdef
  have hq : IsQuantiser P₀.support q (fun k => 1 / ((k : ℝ) + 1)) := by
    refine ⟨fun k => (show Measurable ((fun i : Fin (n k) => z i) ∘
      qIdx (fun i : Fin (n k) => z i) (1 / ((k : ℝ) + 1)) ⟨0, hn k⟩) from
        measurable_from_top.comp (measurable_qIdx _ _ _)), tendsto_one_div_add_atTop_nhds_zero_nat,
      fun k x hx => ?_, fun k x hx y hy hxy => ?_⟩
    · rw [dist_comm]; exact (dist_qIdx_lt (hcov k x hx)).le
    · have hinj : Function.Injective fun i : Fin (n k) => z i := fun a b h => Fin.ext (hzinj h)
      have hidx := hinj hxy
      have h1 := dist_qIdx_lt (i0 := ⟨0, hn k⟩) (hcov k x hx)
      have h2 := dist_qIdx_lt (i0 := ⟨0, hn k⟩) (hcov k y hy)
      rw [← hidx] at h2
      have := dist_triangle_right x y (z (qIdx (fun i : Fin (n k) => z i) (1 / ((k : ℝ) + 1)) ⟨0, hn k⟩ x))
      linarith
  have hS : MeasurableSet P₀.support := Measure.isClosed_support.measurableSet
  have hlim := consistRisk_tendsto_quantise hM lcov hL hLb hK hKmin hKb P₀ μ hS hμS hpos hq
  have hpev := eventually_pos_quantise (M := M) μ hS hμS hq hpos
  obtain ⟨k, hk1, hk2⟩ := ((hlim.eventually (gt_mem_nhds (show consistRisk L Kk lcov P₀ μ <
    consistRisk L Kk lcov P₀ μ + ε by linarith))).and hpev).exists
  obtain ⟨w, hw, hmap⟩ := map_quantiser μ (fun i : Fin (n k) => z i) (1 / ((k : ℝ) + 1)) ⟨0, hn k⟩
  have hinj : Function.Injective fun i : Fin (n k) => z i := fun a b h => Fin.ext (hzinj h)
  have hqk : μ.map (q k) = poolLaw (fun i : Fin (n k) => z i) w := hmap
  rw [hqk] at hk1 hk2
  have hΔ := inDeltaM_of_pos hinj hw hk2
  exact absurd (hbad k w hΔ) (not_lt.2 hk1.le)

end ConsistR

open ConsistR

theorem consist_approx : Claims.consist_approx := by
  intro Z Ω₀ _ _ _ _ _ P₀ _ Q _ Zs M L Kk BL Kmin Kmax lcov Rstar hM hat hL hLb hsym hK hKmin hKb hlcov hZm hZi
    hZl hglb
  have hatQ : ∀ i x, Q.map (Zs i) {x} = 0 := fun i x => by rw [hZl i]; exact hat x
  filter_upwards [StatFormal.Wave26b.ae_pool_dense hZm hZi hZl, ae_injective_of_iIndep hZm hZi hatQ]
    with ω₀ hω₀ hinj
  intro ε hε
  obtain ⟨c, ⟨μ, hadm, rfl⟩, -, hc⟩ := hglb.exists_between (show Rstar < Rstar + ε / 2 by linarith)
  obtain ⟨N₀, hN₀⟩ := approx_pool_swor hM lcov hL hLb hK hKmin hKb P₀ μ hadm (fun i => Zs i ω₀) hinj hω₀.2
    (ε / 2) (by linarith)
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨w, hw, hle⟩ := hN₀ n hn
  exact ⟨w, hw, by linarith⟩

end StatFormal.Wave29i
