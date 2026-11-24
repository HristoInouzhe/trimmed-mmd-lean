import StatFormal.Archive.Wave30z.RouteLimit

/-!
# Route — wave 30z `cor:boundary-linear` (a) (untrusted)

* `ae_linear_consistent`: almost surely the limit process respects every exact linear relation of the indexing
  functions: if `Var[Σ u_i ℓ^P_{z_i}] + Var[Σ u_i ℓ^Q_{z_i}] = 0` then `Σ u_i 𝔾(z_i) = 0` (each relation holds a.s.
  since the law is `N(0, 0) = δ₀`; a countable dense set of relations, and continuity of the paths).
* positive homogeneity of `H` on `[0, 1]`-multiples: `q(cf) ⊇ c q(f)`, and every point of `q(cf)` is related to a
  point of `q(f)` by an exact affine identity of hinges (`c > 0`; the case `t/c < −κ` forces `α = 0`); `H(0) = 0`.
* on a ray `K° = ℝ₊ν`, `sup_{c ∈ [0,1]} c X = X_+`; with unique quantiles `X` is a centred Gaussian
  (the two-point law of `𝔾`) and `N(0, σ²)(−∞, 0] = 1/2` by symmetry and absence of atoms.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30z

open StatFormal.TrimmedMMD.Concentration (region empirical)
open StatFormal.TrimmedMMD.Unconditional (setDist Dpop Demp)
open StatFormal.Wave30v (supFun Ball ballNeg polarSet coneHull supportFn)
open StatFormal.Foundations.Donsker

attribute [local instance] Metric.metricSpaceSum

lemma variance_fun_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ) :
    Var[fun _ => c; μ] = 0 := by
  have := variance_const_add (μ := μ) (X := fun _ => (0 : ℝ)) aestronglyMeasurable_const c
  simp only [add_zero] at this
  rw [this]
  exact variance_zero μ

section Consistent
variable {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {φ : 𝒳 → E} {κ : ℝ} {P Q : Measure 𝒳}

/-- The a.s. linear consistency property of a path. -/
def LinCons (φ : 𝒳 → E) (P Q : Measure 𝒳) (κ : ℝ) (v : C(Idx2 E κ, ℝ)) : Prop :=
  ∀ (p : ℕ) (z : Fin p → Idx2 E κ) (u : Fin p → ℝ), gpVar φ P Q 1 1 z u = 0 → ∑ i, u i * v (z i) = 0

lemma ae_linCons {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {𝔾 : Ω' → C(Idx2 E κ, ℝ)} (h𝔾 : IsLimitGP φ P Q 1 1 κ μ' 𝔾) : ∀ᵐ ω' ∂μ', LinCons φ P Q κ (𝔾 ω') := by
  -- for each `p`, a countable dense set of exact relations
  have hD : ∀ p : ℕ, ∃ D : Set {zu : (Fin p → Idx2 E κ) × (Fin p → ℝ) // gpVar φ P Q 1 1 zu.1 zu.2 = 0},
      D.Countable ∧ Dense D := fun p => TopologicalSpace.exists_countable_dense _
  choose D hDc hDd using hD
  have hpt : ∀ p (d : {zu : (Fin p → Idx2 E κ) × (Fin p → ℝ) // gpVar φ P Q 1 1 zu.1 zu.2 = 0}),
      ∀ᵐ ω' ∂μ', ∑ i, d.1.2 i * 𝔾 ω' (d.1.1 i) = 0 := by
    intro p d
    have hlaw := h𝔾.2 p d.1.1 d.1.2
    rw [d.2, Real.toNNReal_zero, gaussianReal_zero_var] at hlaw
    have hm : AEMeasurable (fun ω' => ∑ i, d.1.2 i * 𝔾 ω' (d.1.1 i)) μ' :=
      (continuous_linEval d.1.1 d.1.2).measurable.comp_aemeasurable h𝔾.1
    have : ∀ᵐ y ∂(μ'.map fun ω' => ∑ i, d.1.2 i * 𝔾 ω' (d.1.1 i)), y = 0 := by
      rw [hlaw, ae_dirac_eq]; exact Filter.eventually_pure.2 rfl
    exact ae_of_ae_map hm this
  have hall : ∀ᵐ ω' ∂μ', ∀ p, ∀ d ∈ D p, ∑ i, d.1.2 i * 𝔾 ω' (d.1.1 i) = 0 := by
    rw [ae_all_iff]
    intro p
    exact (ae_ball_iff (hDc p)).2 fun d _ => hpt p d
  filter_upwards [hall] with ω' hω' p z u hzu
  set v := 𝔾 ω'
  let F : {zu : (Fin p → Idx2 E κ) × (Fin p → ℝ) // gpVar φ P Q 1 1 zu.1 zu.2 = 0} → ℝ :=
    fun d => ∑ i, d.1.2 i * v (d.1.1 i)
  have hF : Continuous F := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((continuous_apply i).comp (continuous_snd.comp continuous_subtype_val)).mul
      (v.continuous.comp ((continuous_apply i).comp (continuous_fst.comp continuous_subtype_val)))
  have hcl : IsClosed {d | F d = 0} := isClosed_eq hF continuous_const
  have hsub : D p ⊆ {d | F d = 0} := fun d hd => hω' p d hd
  have := (hDd p).closure_eq ▸ hcl.closure_subset_iff.2 hsub
  exact this (mem_univ (⟨(z, u), hzu⟩ : {zu : (Fin p → Idx2 E κ) × (Fin p → ℝ) // gpVar φ P Q 1 1 zu.1 zu.2 = 0}))

end Consistent

section Homog
variable {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {φ : 𝒳 → E} {κ α : ℝ}

lemma hinge_smul {c : ℝ} (hc : 0 ≤ c) (f : E) (t : ℝ) (x : 𝒳) :
    hinge φ (c • f) (c * t) x = c * hinge φ f t x := by
  unfold hinge
  rw [real_inner_smul_left, ← mul_sub, mul_max_of_nonneg _ _ hc, mul_zero]

lemma cvObj_smul (μ : Measure 𝒳) {c : ℝ} (hc : 0 ≤ c) (f : E) (t : ℝ) :
    cvObj φ α μ (c • f) (c * t) = c * cvObj φ α μ f t := by
  unfold cvObj
  simp_rw [hinge_smul hc, integral_const_mul]
  ring

lemma mem_Icc_mul {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hκ0 : 0 ≤ κ) (t : Icc (-κ) κ) : c * (t : ℝ) ∈ Icc (-κ) κ := by
  obtain ⟨h1, h2⟩ := t.2
  constructor <;> nlinarith

lemma mem_argmin_smul (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (μ : Measure 𝒳) [IsProbabilityMeasure μ] {f : E} (hf : ‖f‖ ≤ 1) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {t : Icc (-κ) κ} (ht : t ∈ argminSet φ α μ κ f) :
    (⟨c * t, mem_Icc_mul hc0.le hc1 hκ0 t⟩ : Icc (-κ) κ) ∈ argminSet φ α μ κ (c • f) := by
  rw [mem_argminSet_iff] at ht ⊢
  intro t''
  have e1 : (t'' : ℝ) = c * ((t'' : ℝ) / c) := by field_simp
  have h1 : cvObj φ α μ (c • f) t'' = c * cvObj φ α μ f ((t'' : ℝ) / c) := by
    rw [← cvObj_smul μ hc0.le, ← e1]
  obtain ⟨t₀, h₀⟩ := exists_Icc_cvObj_le hφ hκ hκ0 hα0 hα1 μ hf ((t'' : ℝ) / c)
  show cvObj φ α μ (c • f) (c * t) ≤ _
  rw [cvObj_smul μ hc0.le, h1]
  exact mul_le_mul_of_nonneg_left ((ht t₀).trans h₀) hc0.le

lemma argmin_smul_rel (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (μ : Measure 𝒳) [IsProbabilityMeasure μ] {f : E} (hf : ‖f‖ ≤ 1) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {t : Icc (-κ) κ} (ht : t ∈ argminSet φ α μ κ (c • f)) :
    ∃ t' ∈ argminSet φ α μ κ f, ∃ d : ℝ, ∀ x, hinge φ (c • f) t x = c * hinge φ f t' x + d := by
  rw [mem_argminSet_iff] at ht
  set s : ℝ := (t : ℝ) / c with hs
  have hts : (t : ℝ) = c * s := by rw [hs]; field_simp
  have key : ∀ t'' : Icc (-κ) κ, cvObj φ α μ f s ≤ cvObj φ α μ f t'' := by
    intro t''
    have h1 := ht ⟨c * t'', mem_Icc_mul hc0.le hc1 hκ0 t''⟩
    simp only at h1
    rw [hts, cvObj_smul μ hc0.le, cvObj_smul μ hc0.le] at h1
    exact le_of_mul_le_mul_left h1 hc0
  have hY := fun x => abs_le.1 (abs_inner_le_of_norm_le hκ hf x)
  have hβ : 1 ≤ 1 / (1 - α) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hYi : Integrable (fun x => ⟪f, φ x⟫) μ :=
    Integrable.of_bound (stronglyMeasurable_const.inner hφ).aestronglyMeasurable κ
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_inner_le_of_norm_le hκ hf x)
  by_cases hsI : s ∈ Icc (-κ) κ
  · refine ⟨⟨s, hsI⟩, ?_, 0, fun x => ?_⟩
    · rw [mem_argminSet_iff]; exact key
    · rw [hts, hinge_smul hc0.le, add_zero]
  · rcases not_and_or.1 hsI with hlo | hhi
    · -- `s < −κ`: forces `β = 1`
      have hlo : s < -κ := lt_of_not_ge hlo
      have e1 : ∀ x, hinge φ f s x = ⟪f, φ x⟫ - s := fun x => by
        unfold hinge; exact max_eq_left (by linarith [(hY x).1])
      have e2 : ∀ x, hinge φ f (-κ) x = ⟪f, φ x⟫ + κ := fun x => by
        unfold hinge; rw [sub_neg_eq_add]; exact max_eq_left (by linarith [(hY x).1])
      have hcs : cvObj φ α μ f s = s + 1 / (1 - α) * ((∫ x, ⟪f, φ x⟫ ∂μ) - s) := by
        unfold cvObj; simp_rw [e1]; rw [integral_sub hYi (integrable_const s)]; simp
      have hck : cvObj φ α μ f (-κ) = -κ + 1 / (1 - α) * ((∫ x, ⟪f, φ x⟫ ∂μ) + κ) := by
        unfold cvObj; simp_rw [e2]; rw [integral_add hYi (integrable_const κ)]; simp
      have hk := key ⟨-κ, by constructor <;> linarith⟩
      simp only at hk
      rw [hcs, hck] at hk
      have hβ1 : 1 / (1 - α) = 1 := by nlinarith
      have hmin : (⟨-κ, by constructor <;> linarith⟩ : Icc (-κ) κ) ∈ argminSet φ α μ κ f := by
        rw [mem_argminSet_iff]
        intro t''
        show cvObj φ α μ f (-κ) ≤ _
        have := key t''
        rw [hcs] at this
        rw [hck]
        rw [hβ1] at this ⊢
        linarith
      refine ⟨_, hmin, -c * κ - t, fun x => ?_⟩
      simp only
      rw [e2, hts]
      unfold hinge
      rw [real_inner_smul_left]
      rw [max_eq_left (by nlinarith [(hY x).1])]
      ring
    · -- `s > κ` is impossible
      exfalso
      have hhi : κ < s := lt_of_not_ge hhi
      have e1 : ∀ x, hinge φ f s x = 0 := fun x => by
        unfold hinge; exact max_eq_right (by linarith [(hY x).2])
      have e2 : ∀ x, hinge φ f κ x = 0 := fun x => by
        unfold hinge; exact max_eq_right (by linarith [(hY x).2])
      have hk := key ⟨κ, by constructor <;> linarith⟩
      simp only [cvObj, e1, e2, integral_zero, mul_zero, add_zero] at hk
      linarith

/-- The relation property of a path on one copy (`side`) w.r.t. the hinge class. -/
def RelProp (φ : 𝒳 → E) (κ : ℝ) (side : Idx1 E κ → Idx2 E κ) (v : C(Idx2 E κ, ℝ)) : Prop :=
  ∀ (a b : Idx1 E κ) (l d : ℝ), (∀ x, hinge φ (a.1 : E) a.2 x = l * hinge φ (b.1 : E) b.2 x + d) →
    v (side a) = l * v (side b)

/-- Positive homogeneity of `H` on `[0, 1]`-multiples. -/
lemma Hfun_smul (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (μ : Measure 𝒳) [IsProbabilityMeasure μ] (side : Idx1 E κ → Idx2 E κ) (hside : Continuous side)
    (v : C(Idx2 E κ, ℝ)) (hR : RelProp φ κ side v) (f g : Ball E) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hgf : (g : E) = c • (f : E)) : Hfun φ α μ κ side v g = c * Hfun φ α μ κ side v f := by
  have hκ0 := kappa_nonneg hκ μ
  have hf : ‖(f : E)‖ ≤ 1 := mem_closedBall_zero_iff.1 f.2
  have hcont : ∀ h : Ball E, Continuous fun t : Icc (-κ) κ => v (side (h, t)) := fun h =>
    v.continuous.comp (hside.comp (continuous_const.prodMk continuous_id))
  unfold Hfun
  rcases hc0.lt_or_eq with hc0 | hc0
  · -- `c > 0`
    have hq : argminSet φ α μ κ (g : E) = argminSet φ α μ κ (c • (f : E)) := by rw [hgf]
    obtain ⟨tf, htf, hef, hlef⟩ := argminSet_attain hφ hκ hκ0 μ (f : E) _ (hcont f)
    have hne := argminSet_nonempty hφ hκ hκ0 α μ (g : E)
    have hbdd : BddBelow ((fun t => v (side (g, t))) '' argminSet φ α μ κ (g : E)) :=
      ((isClosed_argminSet hφ hκ μ (g : E)).isCompact.image (hcont g)).bddBelow
    have hle : sInf ((fun t => v (side (g, t))) '' argminSet φ α μ κ (g : E)) ≤
        c * sInf ((fun t => v (side (f, t))) '' argminSet φ α μ κ (f : E)) := by
      have hmem : (⟨c * tf, mem_Icc_mul hc0.le hc1 hκ0 tf⟩ : Icc (-κ) κ) ∈ argminSet φ α μ κ (g : E) := by
        rw [hq]; exact mem_argmin_smul hφ hκ hκ0 hα0 hα1 μ hf hc0 hc1 htf
      refine (csInf_le hbdd ⟨_, hmem, rfl⟩).trans (le_of_eq ?_)
      rw [← hef]
      exact hR (g, _) (f, tf) c 0 fun x => by simp only; rw [hgf, hinge_smul hc0.le, add_zero]
    have hge : c * sInf ((fun t => v (side (f, t))) '' argminSet φ α μ κ (f : E)) ≤
        sInf ((fun t => v (side (g, t))) '' argminSet φ α μ κ (g : E)) := by
      refine le_csInf (hne.image _) ?_
      rintro _ ⟨t, ht, rfl⟩
      rw [hq] at ht
      obtain ⟨t', ht', d, hd⟩ := argmin_smul_rel hφ hκ hκ0 hα0 hα1 μ hf hc0 hc1 ht
      have := hR (g, t) (f, t') c d fun x => by simp only; rw [hgf]; exact hd x
      show _ ≤ v (side (g, t))
      rw [this]
      exact mul_le_mul_of_nonneg_left (hlef t' ht') hc0.le
    rw [le_antisymm hle hge]; ring
  · -- `c = 0`: `g = 0`, `H(0) = 0`
    subst hc0
    have hg0 : (g : E) = 0 := by rw [hgf, zero_smul]
    have hzero : ∀ t : Icc (-κ) κ, v (side (g, t)) = 0 := by
      intro t
      have := hR (g, t) (g, t) 0 (max (-(t : ℝ)) 0) fun x => by
        simp only [zero_mul, zero_add]; unfold hinge; rw [hg0, inner_zero_left, zero_sub]
      rw [this, zero_mul]
    have hne := argminSet_nonempty hφ hκ hκ0 α μ (g : E)
    have himg : (fun t => v (side (g, t))) '' argminSet φ α μ κ (g : E) = {0} := by
      ext y; constructor
      · rintro ⟨t, -, rfl⟩; exact hzero t
      · intro hy; obtain ⟨t, ht⟩ := hne; exact ⟨t, ht, (hzero t).trans hy.symm⟩
    rw [himg, csInf_singleton]; ring

end Homog

section Ray
variable {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {φ : 𝒳 → E} {κ : ℝ} {P Q : Measure 𝒳}

lemma relProp_inl [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (v : C(Idx2 E κ, ℝ))
    (hL : LinCons φ P Q κ v) : RelProp φ κ Sum.inl v := by
  intro a b l d hrel
  have h := hL 2 ![Sum.inl a, Sum.inl b] ![1, -l] ?_
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    linarith
  · unfold gpVar
    have e1 : (fun w => ∑ i, (![1, -l] : Fin 2 → ℝ) i * hingeP φ ((![Sum.inl a, Sum.inl b] : Fin 2 → Idx2 E κ) i) w) =
        fun _ => d := by
      funext w
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hingeP, Sum.elim_inl, hrel w]
      ring
    have e2 : (fun w => ∑ i, (![1, -l] : Fin 2 → ℝ) i * hingeQ φ ((![Sum.inl a, Sum.inl b] : Fin 2 → Idx2 E κ) i) w) =
        fun _ => 0 := by
      funext w
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hingeQ, Sum.elim_inl]
      ring
    rw [e1, e2, variance_fun_const, variance_fun_const]; ring

lemma relProp_inr [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (v : C(Idx2 E κ, ℝ))
    (hL : LinCons φ P Q κ v) : RelProp φ κ Sum.inr v := by
  intro a b l d hrel
  have h := hL 2 ![Sum.inr a, Sum.inr b] ![1, -l] ?_
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    linarith
  · unfold gpVar
    have e1 : (fun w => ∑ i, (![1, -l] : Fin 2 → ℝ) i * hingeP φ ((![Sum.inr a, Sum.inr b] : Fin 2 → Idx2 E κ) i) w) =
        fun _ => 0 := by
      funext w
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hingeP, Sum.elim_inr]
      ring
    have e2 : (fun w => ∑ i, (![1, -l] : Fin 2 → ℝ) i * hingeQ φ ((![Sum.inr a, Sum.inr b] : Fin 2 → Idx2 E κ) i) w) =
        fun _ => d := by
      funext w
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hingeQ, Sum.elim_inr, hrel w]
      ring
    rw [e1, e2, variance_fun_const, variance_fun_const]; ring

/-- The half-mass of a centred Gaussian on `(−∞, 0]`. -/
lemma gaussianReal_Iic_zero {v : NNReal} (hv : v ≠ 0) : gaussianReal 0 v (Iic 0) = 1 / 2 := by
  have hs := nullSingletonClass_gaussianReal (μ := 0) hv
  set G := gaussianReal 0 v
  have hsym : G (Iic 0) = G (Ici 0) := by
    have h := gaussianReal_map_neg (μ := (0 : ℝ)) (v := v)
    rw [neg_zero] at h
    have : G (Ici 0) = (G.map fun x => -x) (Ici 0) := by rw [h]
    rw [this, Measure.map_apply measurable_neg measurableSet_Ici]
    congr 1; ext x; simp
  have hIci : G (Ioi 0) = G (Ici 0) := measure_congr Ioi_ae_eq_Ici
  have hsum : G (Iic 0) + G (Ioi 0) = 1 := by
    rw [← measure_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi, Iic_union_Ioi, measure_univ]
  rw [hIci, ← hsym] at hsum
  rw [ENNReal.eq_div_iff two_ne_zero ENNReal.ofNat_ne_top, two_mul, hsum]

theorem boundary_ray : Claims.boundary_ray := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ Ω _ μ _ ξ η n m r cP cQ Ω' _ μ' _ 𝔾 ν hφ hκ hα0 hα1 hS hSc h𝔾 hAB hν hray
  obtain ⟨-, -, hc⟩ := boundary_contact 𝒳 E φ κ α P Q Ω μ ξ η n m r cP cQ Ω' μ' 𝔾 hφ hκ hα0 hα1 hS hSc h𝔾 hAB
  set K := closure (coneHull (region φ α Q - region φ α P)) with hKdef
  have hbL : ∀ v, LinCons φ P Q κ v → ∀ (g : Ball E) (c : ℝ), 0 ≤ c → c ≤ 1 → (g : E) = c • (ν : E) →
      boundaryLim φ α P Q κ cP cQ v g = c * boundaryLim φ α P Q κ cP cQ v ν := by
    intro v hL g c hc0 hc1 hg
    have h1 := Hfun_smul hφ hκ hα0 hα1 P Sum.inl continuous_inl v (relProp_inl v hL) (ballNeg ν) (ballNeg g)
      hc0 hc1 (by change -(g : E) = c • -(ν : E); rw [hg, smul_neg])
    have h2 := Hfun_smul hφ hκ hα0 hα1 Q Sum.inr continuous_inr v (relProp_inr v hL) ν g hc0 hc1 hg
    simp only [boundaryLim, h1, h2]; ring
  have hmemK : ∀ g : Ball E, (g : E) ∈ polarSet K ↔ ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ (g : E) = c • (ν : E) := by
    intro g; rw [hray]; constructor
    · rintro ⟨c, hc, hg⟩
      refine ⟨c, hc, ?_, hg⟩
      have := mem_closedBall_zero_iff.1 g.2
      rwa [hg, norm_smul, hν, Real.norm_eq_abs, abs_of_nonneg hc, mul_one] at this
    · rintro ⟨c, hc, -, hg⟩; exact ⟨c, hc, hg⟩
  have hae : ∀ᵐ ω' ∂μ', sSup (boundaryLim φ α P Q κ cP cQ (𝔾 ω') '' {g : Ball E | (g : E) ∈ polarSet K}) =
      max (boundaryLim φ α P Q κ cP cQ (𝔾 ω') ν) 0 := by
    filter_upwards [ae_linCons h𝔾] with ω' hL
    set X := boundaryLim φ α P Q κ cP cQ (𝔾 ω') ν with hXdef
    have hbound : ∀ y ∈ boundaryLim φ α P Q κ cP cQ (𝔾 ω') '' {g : Ball E | (g : E) ∈ polarSet K}, y ≤ max X 0 := by
      rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, hc0, hc1, hgc⟩ := (hmemK g).1 hg
      rw [hbL _ hL g c hc0 hc1 hgc]
      rcases le_total 0 X with hX | hX
      · rw [max_eq_left hX]; nlinarith
      · rw [max_eq_right hX]; nlinarith
    have hνmem : ν ∈ {g : Ball E | (g : E) ∈ polarSet K} :=
      (hmemK ν).2 ⟨1, zero_le_one, le_rfl, (one_smul _ _).symm⟩
    let g0 : Ball E := ⟨0, mem_closedBall_self zero_le_one⟩
    have h0mem : g0 ∈ {g : Ball E | (g : E) ∈ polarSet K} :=
      (hmemK g0).2 ⟨0, le_rfl, zero_le_one, (zero_smul _ _).symm⟩
    have h0val : boundaryLim φ α P Q κ cP cQ (𝔾 ω') g0 = 0 := by
      rw [hbL _ hL g0 0 le_rfl zero_le_one (zero_smul _ _).symm, zero_mul]
    have hbdd : BddAbove (boundaryLim φ α P Q κ cP cQ (𝔾 ω') '' {g : Ball E | (g : E) ∈ polarSet K}) :=
      ⟨max X 0, hbound⟩
    refine le_antisymm (csSup_le ⟨_, ν, hνmem, rfl⟩ hbound) (max_le (le_csSup hbdd ⟨ν, hνmem, rfl⟩) ?_)
    rw [← h0val]; exact le_csSup hbdd ⟨g0, h0mem, rfl⟩
  have h1 := tendstoInDistribution_congr_limit hc (hc.aemeasurable_limit.congr hae) (Measure.map_congr hae)
  refine ⟨h1, fun tP sQ htP hsQ => ?_⟩
  intro σ2
  set β := 1 / (1 - α) with hβ
  let z : Fin 2 → Idx2 E κ := ![Sum.inl (ballNeg ν, tP), Sum.inr (ν, sQ)]
  let u : Fin 2 → ℝ := ![-cP * β, -cQ * β]
  have hX : ∀ v : C(Idx2 E κ, ℝ), boundaryLim φ α P Q κ cP cQ v ν = ∑ i, u i * v (z i) := by
    intro v
    have hP' : argminSet φ α P κ ((ballNeg ν : Ball E) : E) = {tP} := htP
    simp only [boundaryLim, Hfun, hP', hsQ, Set.image_singleton, csInf_singleton, Fin.sum_univ_two, z, u,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hvar : gpVar φ P Q 1 1 z u = σ2 := by
    unfold gpVar
    have e1 : (fun w => ∑ i, u i * hingeP φ (z i) w) = fun w => (-cP * β) * hinge φ (-(ν : E)) tP w := by
      funext w
      simp only [Fin.sum_univ_two, z, u, Matrix.cons_val_zero, Matrix.cons_val_one, hingeP, Sum.elim_inl,
        Sum.elim_inr, mul_zero, add_zero]
      rfl
    have e2 : (fun w => ∑ i, u i * hingeQ φ (z i) w) = fun w => (-cQ * β) * hinge φ (ν : E) sQ w := by
      funext w
      simp only [Fin.sum_univ_two, z, u, Matrix.cons_val_zero, Matrix.cons_val_one, hingeQ, Sum.elim_inl,
        Sum.elim_inr, mul_zero, zero_add]
    rw [e1, e2, variance_const_mul, variance_const_mul]
    show _ = (1 / (1 - α)) ^ 2 * (cP ^ 2 * Var[hinge φ (-(ν : E)) tP; P] + cQ ^ 2 * Var[hinge φ (ν : E) sQ; Q])
    rw [← hβ]; ring
  have hXm : AEMeasurable (fun ω' => ∑ i, u i * 𝔾 ω' (z i)) μ' :=
    (continuous_linEval z u).measurable.comp_aemeasurable h𝔾.1
  have hmax : Measurable fun x : ℝ => max x 0 := (continuous_id.max continuous_const).measurable
  have hlaw : μ'.map (fun ω' => max (boundaryLim φ α P Q κ cP cQ (𝔾 ω') ν) 0) =
      (gaussianReal 0 σ2.toNNReal).map (fun x : ℝ => max x 0) := by
    have : (fun ω' => max (boundaryLim φ α P Q κ cP cQ (𝔾 ω') ν) 0) =
        (fun x : ℝ => max x 0) ∘ (fun ω' => ∑ i, u i * 𝔾 ω' (z i)) := by
      funext ω'; simp only [Function.comp, hX]
    rw [this, ← AEMeasurable.map_map_of_aemeasurable hmax.aemeasurable hXm, h𝔾.2 2 z u, hvar]
  refine ⟨tendstoInDistribution_congr_limit h1 hmax.aemeasurable hlaw, fun hσ => ?_⟩
  rw [Measure.map_apply hmax (measurableSet_singleton 0)]
  have : (fun x : ℝ => max x 0) ⁻¹' {0} = Iic 0 := by
    ext x; simp only [mem_preimage, mem_singleton_iff, mem_Iic]
    constructor
    · intro h; rw [← h]; exact le_max_left _ _
    · intro h; exact max_eq_right h
  rw [this]
  exact gaussianReal_Iic_zero (by simpa using hσ)

end Ray

end StatFormal.Wave30z
