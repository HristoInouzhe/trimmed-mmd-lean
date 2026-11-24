import StatFormal.Archive.Wave30da.Statements
import StatFormal.Archive.Wave30cq.RouteBoundary
import StatFormal.Archive.Wave30z.RouteVertex
import StatFormal.Lib.Donsker.Fidi
import StatFormal.Lib.Donsker.TwoSampleCLT

/-!
# Route — wave 30da: `cor:boundary-linear`, `G_P` a function of `𝔾_P`, independence, chi-bar-square (untrusted)

* Independence of the two copies (`wda_indep`): the law of `𝔾` on `C(Idx2)` equals the push-forward of
  `law(𝔾_P) ⊗ law(𝔾_Q)` under the gluing map `C(Idx1)² → C(Idx2)` (`measure_ext_of_linEval`: every
  `Σ u_i v(z_i)` splits into a left and a right sum, Gaussian with the additive variance `gpVar`, and
  `N(0,a) ∗ N(0,b) = N(0,a+b)`).
* `v ↦ H(v)(f)` is `β`-Lipschitz in the sup norm (`wda_sInf_le`), so `F_P`, `F_Q` built from finitely many values of
  `H_P`, `H_Q` are continuous.
* General factorisation: an orthonormal basis `e_j` of `S = span(K° ∩ 𝔹)`, each `e_j = Σ_i a_{ji} g_{ji}` with
  `g_{ji} ∈ K° ∩ 𝔹`; `F_P(w) = Σ_j (Σ_i a_{ji} (−H_P^w(−g_{ji}))) e_j` equals a.s. `Σ_j ⟨e_j, G_P⟩ e_j`, which has the
  same inner products as `G_P` with every vector of `S ⊇ K°`.
* (a): `F_P(w) = −H_P^w(−ν) ν` directly (wave 30cq construction); (b): frozen `boundary_vertex` + the general form.
* Chi-bar-square: `‖Π_{K°} x‖ = dist(x, K)` (frozen Moreau), and `dist(σx, K) = σ dist(x, K)` on a cone.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30da

open StatFormal.TrimmedMMD.Concentration (region)
open StatFormal.TrimmedMMD.Unconditional (Demp)
open StatFormal.Wave30v (Ball ballNeg polarSet coneHull)
open StatFormal.Wave30z
open StatFormal.Foundations.Donsker (linEval continuous_linEval measure_ext_of_linEval tendstoInDistribution_congr_limit)

attribute [local instance] Metric.metricSpaceSum

section Cont
variable {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma wda_sInf_le {κ : ℝ} {T : Type*} (S : Set T) (e : T → Idx2 E κ) (v w : C(Idx2 E κ, ℝ)) :
    sInf ((fun t => v (e t)) '' S) ≤ sInf ((fun t => w (e t)) '' S) + dist v w := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS, dist_nonneg]
  · have hbdd : BddBelow ((fun t => v (e t)) '' S) := ⟨-‖v‖, by
      rintro _ ⟨t, -, rfl⟩
      have h1 := v.norm_coe_le_norm (e t)
      rw [Real.norm_eq_abs] at h1
      have := neg_abs_le (v (e t))
      linarith⟩
    have : sInf ((fun t => v (e t)) '' S) - dist v w ≤ sInf ((fun t => w (e t)) '' S) := by
      refine le_csInf (hS.image _) ?_
      rintro _ ⟨t, ht, rfl⟩
      have h1 : sInf ((fun t => v (e t)) '' S) ≤ v (e t) := csInf_le hbdd ⟨t, ht, rfl⟩
      have h2 : dist (v (e t)) (w (e t)) ≤ dist v w := ContinuousMap.dist_apply_le_dist _
      rw [Real.dist_eq] at h2
      have := le_abs_self (v (e t) - w (e t))
      linarith
    linarith

lemma wda_continuous_sInf {κ : ℝ} {T : Type*} (S : Set T) (e : T → Idx2 E κ) :
    Continuous (fun v : C(Idx2 E κ, ℝ) => sInf ((fun t => v (e t)) '' S)) :=
  (LipschitzWith.of_le_add (fun v w => wda_sInf_le S e v w)).continuous

lemma wda_continuous_Hfun (φ : 𝒳 → E) (α : ℝ) (μ : Measure 𝒳) (κ : ℝ) (side : Idx1 E κ → Idx2 E κ) (f : Ball E) :
    Continuous (fun v : C(Idx2 E κ, ℝ) => Hfun φ α μ κ side v f) := by
  unfold Hfun
  exact continuous_const.mul (wda_continuous_sInf _ (fun t => side (f, t)))

/-- The fold `Idx1 ⊕ Idx1 → Idx1`. -/
def wdaFold (κ : ℝ) : C(Idx2 E κ, Idx1 E κ) := ⟨Sum.elim id id, continuous_id.sumElim continuous_id⟩

lemma wda_HfunL (φ : 𝒳 → E) (α : ℝ) (μ : Measure 𝒳) (κ : ℝ) (v : C(Idx2 E κ, ℝ)) (f : Ball E) :
    Hfun φ α μ κ Sum.inl ((leftPath v).comp (wdaFold κ)) f = Hfun φ α μ κ Sum.inl v f := rfl

lemma wda_HfunR (φ : 𝒳 → E) (α : ℝ) (μ : Measure 𝒳) (κ : ℝ) (v : C(Idx2 E κ, ℝ)) (f : Ball E) :
    Hfun φ α μ κ Sum.inr ((rightPath v).comp (wdaFold κ)) f = Hfun φ α μ κ Sum.inr v f := rfl

lemma wda_contL (φ : 𝒳 → E) (α : ℝ) (μ : Measure 𝒳) (κ : ℝ) (f : Ball E) :
    Continuous (fun w : C(Idx1 E κ, ℝ) => Hfun φ α μ κ Sum.inl (w.comp (wdaFold κ)) f) :=
  (wda_continuous_Hfun φ α μ κ Sum.inl f).comp (ContinuousMap.continuous_precomp _)

lemma wda_contR (φ : 𝒳 → E) (α : ℝ) (μ : Measure 𝒳) (κ : ℝ) (f : Ball E) :
    Continuous (fun w : C(Idx1 E κ, ℝ) => Hfun φ α μ κ Sum.inr (w.comp (wdaFold κ)) f) :=
  (wda_continuous_Hfun φ α μ κ Sum.inr f).comp (ContinuousMap.continuous_precomp _)

/-- Gluing two paths on `Idx1` into one path on `Idx1 ⊕ Idx1`. -/
def wdaGlue (κ : ℝ) (p : C(Idx1 E κ, ℝ) × C(Idx1 E κ, ℝ)) : C(Idx2 E κ, ℝ) :=
  ⟨Sum.elim p.1 p.2, p.1.continuous.sumElim p.2.continuous⟩

lemma wda_continuous_glue (κ : ℝ) : Continuous (wdaGlue (E := E) κ) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun p q => ?_).continuous
  rw [NNReal.coe_one, one_mul, Prod.dist_eq]
  refine (ContinuousMap.dist_le (le_max_of_le_left dist_nonneg)).2 fun z => ?_
  rcases z with a | b
  · exact (ContinuousMap.dist_apply_le_dist (f := p.1) (g := q.1) a).trans (le_max_left _ _)
  · exact (ContinuousMap.dist_apply_le_dist (f := p.2) (g := q.2) b).trans (le_max_right _ _)

lemma wda_continuous_leftPath (κ : ℝ) : Continuous (leftPath : C(Idx2 E κ, ℝ) → C(Idx1 E κ, ℝ)) :=
  ContinuousMap.continuous_precomp _

lemma wda_continuous_rightPath (κ : ℝ) : Continuous (rightPath : C(Idx2 E κ, ℝ) → C(Idx1 E κ, ℝ)) :=
  ContinuousMap.continuous_precomp _

/-- The two copies of the limit process are independent. -/
lemma wda_indep {φ : 𝒳 → E} {κ : ℝ} {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {𝔾 : Ω' → C(Idx2 E κ, ℝ)}
    (h : IsLimitGP φ P Q 1 1 κ μ' 𝔾) :
    IndepFun (fun ω => leftPath (𝔾 ω)) (fun ω => rightPath (𝔾 ω)) μ' := by
  have hLc := wda_continuous_leftPath (E := E) κ
  have hRc := wda_continuous_rightPath (E := E) κ
  have hL : AEMeasurable (fun ω => leftPath (𝔾 ω)) μ' := hLc.measurable.comp_aemeasurable h.1
  have hR : AEMeasurable (fun ω => rightPath (𝔾 ω)) μ' := hRc.measurable.comp_aemeasurable h.1
  rw [indepFun_iff_map_prod_eq_prod_map_map hL hR]
  set πL := μ'.map (fun ω => leftPath (𝔾 ω)) with hπLdef
  set πR := μ'.map (fun ω => rightPath (𝔾 ω)) with hπRdef
  have : IsProbabilityMeasure πL := inferInstance
  have : IsProbabilityMeasure πR := inferInstance
  have : IsProbabilityMeasure (μ'.map 𝔾) := inferInstance
  have hg := wda_continuous_glue (E := E) κ
  have : IsProbabilityMeasure ((πL.prod πR).map (wdaGlue κ)) := inferInstance
  have key : μ'.map 𝔾 = (πL.prod πR).map (wdaGlue κ) := by
    refine measure_ext_of_linEval _ _ fun p z u => ?_
    rw [AEMeasurable.map_map_of_aemeasurable (continuous_linEval z u).measurable.aemeasurable h.1,
      Measure.map_map (continuous_linEval z u).measurable hg.measurable]
    have h1 : μ'.map (linEval z u ∘ 𝔾) = gaussianReal 0 (gpVar φ P Q 1 1 z u).toNNReal := h.2 p z u
    rw [h1]
    set w : Fin p → Idx1 E κ := fun i => Sum.elim id id (z i) with hw
    set uL : Fin p → ℝ := fun i => Sum.elim (fun _ => u i) (fun _ => 0) (z i) with huL
    set uR : Fin p → ℝ := fun i => Sum.elim (fun _ => 0) (fun _ => u i) (z i) with huR
    have hdec : linEval z u ∘ wdaGlue κ =
        (fun x : ℝ × ℝ => x.1 + x.2) ∘ Prod.map (linEval w uL) (linEval w uR) := by
      funext q
      simp only [Function.comp_apply, linEval, Prod.map, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases hz : z i with a | b
      · simp [w, uL, uR, hz, wdaGlue]
      · simp [w, uL, uR, hz, wdaGlue]
    have hmL := (continuous_linEval w uL).measurable
    have hmR := (continuous_linEval w uR).measurable
    rw [hdec, ← Measure.map_map (measurable_add (M := ℝ)) (hmL.prodMap hmR),
      ← Measure.map_prod_map _ _ hmL hmR]
    have hπL : πL.map (linEval w uL) =
        gaussianReal 0 (gpVar φ P Q 1 1 (fun i => Sum.inl (w i)) uL).toNNReal := by
      rw [hπLdef, AEMeasurable.map_map_of_aemeasurable hmL.aemeasurable hL]
      exact h.2 p (fun i => Sum.inl (w i)) uL
    have hπR : πR.map (linEval w uR) =
        gaussianReal 0 (gpVar φ P Q 1 1 (fun i => Sum.inr (w i)) uR).toNNReal := by
      rw [hπRdef, AEMeasurable.map_map_of_aemeasurable hmR.aemeasurable hR]
      exact h.2 p (fun i => Sum.inr (w i)) uR
    rw [hπL, hπR]
    have hconv := @gaussianReal_conv_gaussianReal 0 0
      (gpVar φ P Q 1 1 (fun i => Sum.inl (w i)) uL).toNNReal (gpVar φ P Q 1 1 (fun i => Sum.inr (w i)) uR).toNNReal
    unfold Measure.conv at hconv
    rw [hconv, zero_add, StatFormal.Wave30ah.gpVar_inl, StatFormal.Wave30ah.gpVar_inr,
      ← Real.toNNReal_add (variance_nonneg _ _) (variance_nonneg _ _)]
    congr 2
    unfold gpVar
    rw [one_pow, one_mul, one_mul]
    congr 1
    · congr 1
      funext x
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases hz : z i with a | b
      · simp [w, uL, hz, hingeP]
      · simp [w, uL, hz, hingeP]
    · congr 1
      funext x
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases hz : z i with a | b
      · simp [w, uR, hz, hingeQ]
      · simp [w, uR, hz, hingeQ]
  have hsplit : Measurable (fun v : C(Idx2 E κ, ℝ) => (leftPath v, rightPath v)) :=
    (hLc.prodMk hRc).measurable
  have hid : (fun v : C(Idx2 E κ, ℝ) => (leftPath v, rightPath v)) ∘ wdaGlue κ = id := by
    funext q
    exact Prod.ext (ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => rfl)
  calc μ'.map (fun ω => (leftPath (𝔾 ω), rightPath (𝔾 ω)))
      = (μ'.map 𝔾).map (fun v => (leftPath v, rightPath v)) :=
        (AEMeasurable.map_map_of_aemeasurable hsplit.aemeasurable h.1).symm
    _ = ((πL.prod πR).map (wdaGlue κ)).map (fun v => (leftPath v, rightPath v)) := by rw [key]
    _ = πL.prod πR := by rw [Measure.map_map hsplit hg.measurable, hid, Measure.map_id]

end Cont

section Factor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma wda_polar_cone (C : Set E) : ∀ c : ℝ, 0 ≤ c → ∀ g ∈ polarSet C, c • g ∈ polarSet C := by
  intro c hc g hg x hx
  rw [real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos hc (hg x hx)

/-- Every element of a cone lies in the span of its part in the unit ball. -/
lemma wda_mem_span {K : Set E} (hK : ∀ c : ℝ, 0 ≤ c → ∀ g ∈ K, c • g ∈ K) {g : E} (hg : g ∈ K) :
    g ∈ Submodule.span ℝ {x : E | x ∈ K ∧ ‖x‖ ≤ 1} := by
  by_cases h0 : g = 0
  · rw [h0]; exact Submodule.zero_mem _
  · have hn : 0 < ‖g‖ := norm_pos_iff.2 h0
    have hmem : ‖g‖⁻¹ • g ∈ {x : E | x ∈ K ∧ ‖x‖ ≤ 1} :=
      ⟨hK _ (inv_nonneg.2 hn.le) g hg, by rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hn.le), inv_mul_cancel₀ hn.ne']⟩
    have := Submodule.smul_mem _ ‖g‖ (Submodule.subset_span hmem)
    rwa [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] at this

/-- The abstract factorisation: from a.s. values `A ω g = ⟨g, G ω⟩` on `K ∩ 𝔹`, given as continuous functionals
`a g (Y ω)` of a path `Y ω`, build a continuous `F` with `⟨g, F (Y ω)⟩ = ⟨g, G ω⟩` a.s. for every `g ∈ K`. -/
lemma wda_factor_core {K : Set E} (hK : ∀ c : ℝ, 0 ≤ c → ∀ g ∈ K, c • g ∈ K) {W Ω' : Type*} [TopologicalSpace W]
    [MeasurableSpace Ω'] {μ' : Measure Ω'} (Y : Ω' → W) (G : Ω' → E) (a : Ball E → W → ℝ)
    (ha : ∀ g, Continuous (a g)) (hG : ∀ᵐ ω ∂μ', ∀ g : Ball E, (g : E) ∈ K → a g (Y ω) = ⟪(g : E), G ω⟫) :
    ∃ F : W → E, Continuous F ∧ ∀ᵐ ω ∂μ', ∀ g ∈ K, ⟪g, F (Y ω)⟫ = ⟪g, G ω⟫ := by
  classical
  set s : Set E := {x : E | x ∈ K ∧ ‖x‖ ≤ 1}
  set S := Submodule.span ℝ s
  let b := stdOrthonormalBasis ℝ S
  have hrep : ∀ j, ∃ (N : ℕ) (c : Fin N → ℝ) (g : Fin N → s), ∑ i, c i • (g i : E) = (b j : E) :=
    fun j => Submodule.mem_span_set'.1 (b j).2
  choose N c gg hgg using hrep
  let toBall : s → Ball E := fun x => ⟨x.1, mem_closedBall_zero_iff.2 x.2.2⟩
  let coef : Fin (Module.finrank ℝ S) → W → ℝ := fun j y => ∑ i, c j i * a (toBall (gg j i)) y
  refine ⟨fun y => ∑ j, coef j y • (b j : E), ?_, ?_⟩
  · refine continuous_finsetSum _ fun j _ => Continuous.smul ?_ continuous_const
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (ha _)
  · filter_upwards [hG] with ω hω
    have hcoef : ∀ j, coef j (Y ω) = ⟪(b j : E), G ω⟫ := by
      intro j
      simp only [coef]
      rw [← hgg j, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hω (toBall (gg j i)) (gg j i).2.1, real_inner_smul_left]
    intro g hg
    have hgS : g ∈ S := wda_mem_span hK hg
    have hexp : g = ∑ j, ⟪(b j : E), g⟫ • (b j : E) := by
      have := congrArg (fun x : S => (x : E)) (b.sum_repr' ⟨g, hgS⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at this
      exact this.symm
    simp only [hcoef]
    rw [inner_sum]
    conv_rhs => rw [hexp, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right, real_inner_smul_left, real_inner_comm g (b j : E)]
    ring

end Factor

theorem boundary_linear_factor : Claims.boundary_linear_factor := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ Ω _ μ _ ξ η n m r cP cQ Ω' _ μ' _ 𝔾 GP GQ hφ hκ hα0 hα1 hS hSc h𝔾 hAB hlin
  set K := polarSet (closure (coneHull (region φ α Q - region φ α P))) with hKdef
  have hK := wda_polar_cone (closure (coneHull (region φ α Q - region φ α P)))
  obtain ⟨FP, hFP, hagP⟩ := wda_factor_core hK (fun ω => leftPath (𝔾 ω)) GP
    (fun g w => -Hfun φ α P κ Sum.inl (w.comp (wdaFold κ)) (ballNeg g)) (fun g => (wda_contL φ α P κ _).neg)
    (by
      filter_upwards [hlin] with ω hω g hg
      rw [wda_HfunL, (hω g hg).1, inner_neg_left, neg_neg])
  obtain ⟨FQ, hFQ, hagQ⟩ := wda_factor_core hK (fun ω => rightPath (𝔾 ω)) GQ
    (fun g w => Hfun φ α Q κ Sum.inr (w.comp (wdaFold κ)) g) (fun g => wda_contR φ α Q κ _)
    (by
      filter_upwards [hlin] with ω hω g hg
      rw [wda_HfunR, (hω g hg).2])
  have hagree : ∀ᵐ ω' ∂μ', ∀ g ∈ K, ⟪g, FP (leftPath (𝔾 ω'))⟫ = ⟪g, GP ω'⟫ ∧
      ⟪g, FQ (rightPath (𝔾 ω'))⟫ = ⟪g, GQ ω'⟫ := by
    filter_upwards [hagP, hagQ] with ω h1 h2 g hg
    exact ⟨h1 g hg, h2 g hg⟩
  have hhyp : ∀ᵐ ω' ∂μ', ∀ g : Ball E, (g : E) ∈ K →
      Hfun φ α P κ Sum.inl (𝔾 ω') (ballNeg g) = ⟪-(g : E), FP (leftPath (𝔾 ω'))⟫ ∧
        Hfun φ α Q κ Sum.inr (𝔾 ω') g = ⟪(g : E), FQ (rightPath (𝔾 ω'))⟫ := by
    filter_upwards [hlin, hagree] with ω hω hag g hg
    refine ⟨?_, ?_⟩
    · rw [(hω g hg).1, inner_neg_left, inner_neg_left, (hag g hg).1]
    · rw [(hω g hg).2, (hag g hg).2]
  refine ⟨FP, FQ, hFP, hFQ, hhyp, hagree, ?_, ?_⟩
  · intro _ _
    exact (wda_indep h𝔾).comp hFP.measurable hFQ.measurable
  · exact (StatFormal.Wave30z.boundary_linear 𝒳 E φ κ α P Q Ω μ ξ η n m r cP cQ Ω' μ' 𝔾 _ _
      hφ hκ hα0 hα1 hS hSc h𝔾 hAB hhyp).1

theorem boundary_ray_factor : Claims.boundary_ray_factor := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ Ω _ μ _ ξ η n m r cP cQ Ω' _ μ' _ 𝔾 ν hφ hκ hα0 hα1 hS hSc h𝔾 hne hν hK
  have hH := (StatFormal.Wave30ah.boundary_Hprops 𝒳 E φ κ α P Q Ω' μ' 𝔾 hφ hκ hα0 hα1 h𝔾).1
  set FP : C(Idx1 E κ, ℝ) → E := fun w => (-Hfun φ α P κ Sum.inl (w.comp (wdaFold κ)) (ballNeg ν)) • (ν : E)
  set FQ : C(Idx1 E κ, ℝ) → E := fun w => Hfun φ α Q κ Sum.inr (w.comp (wdaFold κ)) ν • (ν : E)
  have hFP : Continuous FP := (wda_contL φ α P κ _).neg.smul continuous_const
  have hFQ : Continuous FQ := (wda_contR φ α Q κ _).smul continuous_const
  have hnorm : ⟪(ν : E), (ν : E)⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hν]; norm_num
  have hhyp : ∀ᵐ ω' ∂μ', ∀ g : Ball E,
      (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))) →
      Hfun φ α P κ Sum.inl (𝔾 ω') (ballNeg g) = ⟪-(g : E), FP (leftPath (𝔾 ω'))⟫ ∧
        Hfun φ α Q κ Sum.inr (𝔾 ω') g = ⟪(g : E), FQ (rightPath (𝔾 ω'))⟫ := by
    filter_upwards [hH] with ω' hω'
    intro g hg
    rw [hK] at hg
    obtain ⟨c, hc0, hgc⟩ := hg
    have hc1 : c ≤ 1 := by
      have h := g.2
      rw [mem_closedBall_zero_iff, hgc, norm_smul, hν, mul_one, Real.norm_of_nonneg hc0] at h
      exact h
    have h1 := (hω'.2 (ballNeg ν) (ballNeg g) c hc0 hc1 (by simp [ballNeg, hgc])).1
    have h2 := (hω'.2 ν g c hc0 hc1 hgc).2
    simp only [FP, FQ, wda_HfunL, wda_HfunR]
    refine ⟨?_, ?_⟩
    · rw [h1, hgc]
      simp only [inner_neg_left, inner_smul_left, inner_smul_right, hnorm, RCLike.conj_to_real]
      ring
    · rw [h2, hgc]
      simp only [inner_smul_left, inner_smul_right, hnorm, RCLike.conj_to_real]
      ring
  refine ⟨FP, FQ, hFP, hFQ, fun ω' => ⟨rfl, rfl⟩, hhyp, ?_, ?_⟩
  · intro _ _
    exact (wda_indep h𝔾).comp hFP.measurable hFQ.measurable
  · exact (StatFormal.Wave30z.boundary_linear 𝒳 E φ κ α P Q Ω μ ξ η n m r cP cQ Ω' μ' 𝔾 _ _
      hφ hκ hα0 hα1 hS hSc h𝔾 hne hhyp).1

theorem boundary_vertex_factor : Claims.boundary_vertex_factor := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ Ω _ μ _ ξ η n m r cP cQ Ω' _ μ' _ 𝔾 J xs ps j0 U J' ys qs j0' U'
    hφ hκ hα0 hα1 hS hSc h𝔾 hAB hps hP hj0 hU1 hU2 hdirP hqs hQ hj0' hU1' hU2' hdirQ
  obtain ⟨GP, GQ, hlin, hlaw, -⟩ := StatFormal.Wave30z.boundary_vertex 𝒳 E φ κ α P Q Ω μ ξ η n m r cP cQ Ω' μ' 𝔾
    J xs ps j0 U J' ys qs j0' U' hφ hκ hα0 hα1 hS hSc h𝔾 hAB hps hP hj0 hU1 hU2 hdirP hqs hQ hj0' hU1' hU2' hdirQ
  obtain ⟨FP, FQ, hFP, hFQ, hhyp, hagree, hind, hlim⟩ := boundary_linear_factor 𝒳 E φ κ α P Q Ω μ ξ η n m r cP cQ
    Ω' μ' 𝔾 GP GQ hφ hκ hα0 hα1 hS hSc h𝔾 hAB hlin
  refine ⟨FP, FQ, hFP, hFQ, hhyp, fun p f g u w hf hg => ?_, hind, hlim⟩
  rw [← hlaw p f g u w hf hg]
  refine Measure.map_congr ?_
  filter_upwards [hagree] with ω hω
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_neg_left, inner_neg_left, (hω (f i) (hf i)).1]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hω (g i) (hg i)).2]

section ChiBar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma wda_infDist_smul_le {K : Set E} (hne : K.Nonempty) (hK : ∀ c : ℝ, 0 ≤ c → ∀ v ∈ K, c • v ∈ K)
    {c : ℝ} (hc : 0 < c) (x : E) : infDist (c • x) K ≤ c * infDist x K := by
  refine le_of_forall_gt_imp_ge_of_dense fun t ht => ?_
  have h1 : infDist x K < t / c := by rw [lt_div_iff₀ hc]; linarith
  obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff hne).1 h1
  refine ((infDist_lt_iff hne).2 ⟨c • y, hK c hc.le y hy, ?_⟩).le
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hc]
  rw [lt_div_iff₀ hc] at hxy
  linarith

lemma wda_infDist_smul {K : Set E} (hne : K.Nonempty) (hK : ∀ c : ℝ, 0 ≤ c → ∀ v ∈ K, c • v ∈ K)
    {c : ℝ} (hc : 0 ≤ c) (x : E) : infDist (c • x) K = c * infDist x K := by
  rcases hc.eq_or_lt with rfl | hc
  · obtain ⟨y, hy⟩ := hne
    have h0 : (0 : E) ∈ K := by simpa using hK 0 le_rfl y hy
    simp [infDist_zero_of_mem h0]
  · refine le_antisymm (wda_infDist_smul_le hne hK hc x) ?_
    have := wda_infDist_smul_le hne hK (inv_pos.2 hc) (c • x)
    rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
    have h2 := mul_le_mul_of_nonneg_left this hc.le
    rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at h2

end ChiBar

theorem boundary_chibar : Claims.boundary_chibar := by
  intro 𝒳 E _ _ _ _ _ _ φ κ α P Q _ _ Ω _ μ _ ξ η n m r cP cQ Ω' _ μ' _ 𝔾 GP GQ σ hφ hκ hα0 hα1 hS hSc h𝔾 hAB
    hlin hσ hlaw
  obtain ⟨hc, hmoreau⟩ := StatFormal.Wave30z.boundary_linear 𝒳 E φ κ α P Q Ω μ ξ η n m r cP cQ Ω' μ' 𝔾 GP GQ
    hφ hκ hα0 hα1 hS hSc h𝔾 hAB hlin
  set K := closure (coneHull (region φ α Q - region φ α P)) with hKdef
  have hKcone : ∀ c : ℝ, 0 ≤ c → ∀ v ∈ K, c • v ∈ K := StatFormal.Wave30v.cone_closure_coneHull _
  have hKne : K.Nonempty := by
    obtain ⟨z, hzA, hzB⟩ := hAB
    exact ⟨0, subset_closure ⟨0, le_rfl, z - z, Set.sub_mem_sub hzB hzA, by simp⟩⟩
  set W : Ω' → E := fun ω' => cP • GP ω' - cQ • GQ ω'
  have hW : AEMeasurable W μ' := hlaw.aemeasurable
  set G : E → ℝ := fun x => infDist x K ^ 2
  have hGc : Continuous G := (continuous_infDist_pt K).pow 2
  have hsq := hc.continuous_comp (continuous_pow 2 : Continuous (fun y : ℝ => y ^ 2))
  have hlimEq : (fun x : E => σ ^ 2 * ‖metricProj (polarSet K) x‖ ^ 2) = fun x => σ ^ 2 * G x := by
    funext x; simp only [G, hmoreau x]
  refine tendstoInDistribution_congr_limit hsq ?_ ?_
  · rw [hlimEq]; exact (continuous_const.mul hGc).measurable.aemeasurable
  · have e1 : ((fun y : ℝ => y ^ 2) ∘ fun ω' => ‖metricProj (polarSet K) (cP • GP ω' - cQ • GQ ω')‖) = G ∘ W := by
      funext ω'; simp only [Function.comp_apply, G, W, hmoreau]
    rw [e1, hlimEq, ← AEMeasurable.map_map_of_aemeasurable hGc.measurable.aemeasurable hW, hlaw.map_eq,
      Measure.map_map hGc.measurable (measurable_const_smul σ)]
    congr 1
    funext x
    simp only [Function.comp_apply, G, wda_infDist_smul hKne hKcone hσ x]
    ring

end StatFormal.Wave30da
