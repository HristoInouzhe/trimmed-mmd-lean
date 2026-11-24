import StatFormal.Archive.Wave30z.RouteRay

/-!
# Route — wave 30z `cor:boundary-linear` (b), a nondegenerate vertex contact of discrete laws (untrusted)

`P = Σ_j p_j δ_{x_j}`, `f ∈ −K° \ {0}` (P side; Q side `f ∈ K°`), `Y_j = ⟨f, φ(x_j)⟩`, `t_f = Y_{j₀}`.
* Quantiles: `cv(t) = t + β Σ_j p_j (Y_j − t)_+`; for `t > t_f`, `cv(t) − cv(t_f) ≥ (t − t_f)(1 − β Σ_U p_j) > 0`;
  for `t < t_f`, `cv(t) − cv(t_f) ≥ (t_f − t)(β(Σ_U p_j + p_{j₀}) − 1) > 0` (the atoms above `t_f` are exactly `U`).
  So `q(f) = {t_f}` and `H_P(f) = β 𝔾(f, t_f)`; `H_P(0) = 0` (the hinge at `f = 0` is constant).
* At the atoms `ℓ_{f,t_f}(x_j) = ⟨f, ψ_j⟩`, `ψ_j = (φ(x_j) − φ(x_{j₀})) 𝟙{j ∈ U}` (`vertexVec`), linear in `f`; and
  `Var_P h = discVar p (h(x_·))`. Hence every linear relation `Σ a_i f_i = 0` in `D = −K° ∩ 𝔹` gives a combination of
  hinges vanishing at all atoms, of variance `0`, and a.s. (`ae_linCons`) `Σ a_i 𝔾(f_i, t_{f_i}) = 0`.
* Linear algebra: a function on `D` respecting all linear relations is the restriction of a linear functional
  (factor `Finsupp.linearCombination` through its kernel, left inverse of the injective quotient map), whose Riesz
  representative is `G_P` (`= 0` off the a.s. event). The law of `Σ u_i⟨−f_i, G_P⟩ + Σ w_i⟨g_i, G_Q⟩` is that of a
  finite combination of `𝔾` (normalise `f_i` into `𝔹`), Gaussian by `IsLimitGP`, with variance through `discVar`.
* The limit: `boundary_linear`.
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

section Discrete
variable {𝒳 : Type*} [MeasurableSpace 𝒳] {J : ℕ}

lemma integrable_diracSum (xs : Fin J → 𝒳) (ps : Fin J → ℝ) {h : 𝒳 → ℝ} (hh : Measurable h) :
    Integrable h (∑ j, ENNReal.ofReal (ps j) • Measure.dirac (xs j)) := by
  refine integrable_finsetSum_measure.2 fun j _ => ?_
  exact (integrable_dirac' hh.stronglyMeasurable enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

lemma integral_diracSum (xs : Fin J → 𝒳) {ps : Fin J → ℝ} (hps : ∀ j, 0 ≤ ps j) {h : 𝒳 → ℝ}
    (hh : Measurable h) :
    ∫ w, h w ∂(∑ j, ENNReal.ofReal (ps j) • Measure.dirac (xs j)) = ∑ j, ps j * h (xs j) := by
  rw [integral_finsetSum_measure fun j _ =>
    (integrable_dirac' hh.stronglyMeasurable enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul_measure, integral_dirac' _ _ hh.stronglyMeasurable, ENNReal.toReal_ofReal (hps j),
    smul_eq_mul]

lemma variance_diracSum (xs : Fin J → 𝒳) {ps : Fin J → ℝ} (hps : ∀ j, 0 ≤ ps j) {μ : Measure 𝒳}
    [IsProbabilityMeasure μ] (hμ : μ = ∑ j, ENNReal.ofReal (ps j) • Measure.dirac (xs j)) {h : 𝒳 → ℝ}
    (hh : Measurable h) : Var[h; μ] = discVar ps (fun j => h (xs j)) := by
  have hh2 : Measurable fun w => h w ^ 2 := hh.pow_const 2
  have hm2 : MemLp h 2 μ := by
    rw [memLp_two_iff_integrable_sq hh.aestronglyMeasurable, hμ]
    exact integrable_diracSum xs ps hh2
  rw [variance_eq_sub hm2]
  have e1 : ∫ w, (h ^ 2) w ∂μ = ∑ j, ps j * h (xs j) ^ 2 := by
    rw [hμ]; exact integral_diracSum xs hps hh2
  have e2 : ∫ w, h w ∂μ = ∑ j, ps j * h (xs j) := by rw [hμ]; exact integral_diracSum xs hps hh
  rw [e1, e2]; rfl

lemma discVar_mul (ps : Fin J → ℝ) (c : ℝ) (a : Fin J → ℝ) :
    discVar ps (fun j => c * a j) = c ^ 2 * discVar ps a := by
  unfold discVar
  have h1 : ∑ j, ps j * (c * a j) ^ 2 = c ^ 2 * ∑ j, ps j * a j ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ j, ps j * (c * a j) = c * ∑ j, ps j * a j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2]; ring

lemma discVar_zero (ps : Fin J → ℝ) : discVar ps (fun _ => 0) = 0 := by simp [discVar]

end Discrete

section Vertex
variable {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] {J : ℕ}

/-- The strict vertex condition at `f`: `⟨f, φ(x_j)⟩ > ⟨f, φ(x_{j₀})⟩` on `U`, `<` off `U ∪ {j₀}`. -/
def VertexCond (φ : 𝒳 → E) (xs : Fin J → 𝒳) (j0 : Fin J) (U : Finset (Fin J)) (f : E) : Prop :=
  (∀ j ∈ U, ⟪f, φ (xs j0)⟫ < ⟪f, φ (xs j)⟫) ∧ (∀ j, j ∉ U → j ≠ j0 → ⟪f, φ (xs j)⟫ < ⟪f, φ (xs j0)⟫)

omit [MeasurableSpace 𝒳] in
lemma hinge_vertex {φ : 𝒳 → E} {xs : Fin J → 𝒳} {j0 : Fin J} {U : Finset (Fin J)} {f : E}
    (hf : f = 0 ∨ VertexCond φ xs j0 U f) (j : Fin J) :
    hinge φ f ⟪f, φ (xs j0)⟫ (xs j) = ⟪f, vertexVec φ xs j0 U j⟫ := by
  rcases hf with rfl | ⟨hf1, hf2⟩
  · simp [hinge]
  · unfold hinge vertexVec
    by_cases hj : j ∈ U
    · rw [if_pos hj, inner_sub_right, max_eq_left (by linarith [hf1 j hj])]
    · rw [if_neg hj, inner_zero_right]
      apply max_eq_right
      by_cases h : j = j0
      · rw [h]; linarith
      · linarith [hf2 j hj h]

lemma cvObj_vertex_lt {φ : 𝒳 → E} (hφ : StronglyMeasurable φ) {α : ℝ} (hα1 : α < 1) {μ : Measure 𝒳}
    {xs : Fin J → 𝒳} {ps : Fin J → ℝ} (hps : ∀ j, 0 ≤ ps j)
    (hμ : μ = ∑ j, ENNReal.ofReal (ps j) • Measure.dirac (xs j)) {j0 : Fin J} {U : Finset (Fin J)}
    (hj0 : j0 ∉ U) (hU1 : ∑ j ∈ U, ps j < 1 - α) (hU2 : 1 - α < ∑ j ∈ U, ps j + ps j0) {f : E}
    (hf : VertexCond φ xs j0 U f) {t : ℝ} (ht : t ≠ ⟪f, φ (xs j0)⟫) :
    cvObj φ α μ f ⟪f, φ (xs j0)⟫ < cvObj φ α μ f t := by
  obtain ⟨hf1, hf2⟩ := hf
  set c := ⟪f, φ (xs j0)⟫ with hc
  set Y : Fin J → ℝ := fun j => ⟪f, φ (xs j)⟫ with hY
  have hcv : ∀ s, cvObj φ α μ f s = s + 1 / (1 - α) * ∑ j, ps j * max (Y j - s) 0 := by
    intro s; unfold cvObj; rw [hμ, integral_diracSum xs hps (measurable_hinge hφ f s)]; rfl
  rw [hcv, hcv]
  have hβ : 0 < 1 / (1 - α) := div_pos one_pos (by linarith)
  have hYc : ∀ j, j ∉ U → Y j ≤ c := fun j hj => by
    by_cases h : j = j0
    · rw [h]
    · exact (hf2 j hj h).le
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · have key : ∀ j, ps j * max (Y j - c) 0 + (c - t) * (if j ∈ insert j0 U then ps j else 0) ≤
        ps j * max (Y j - t) 0 := by
      intro j
      by_cases hj : j ∈ insert j0 U
      · rw [if_pos hj]
        have hYj : c ≤ Y j := by
          rcases Finset.mem_insert.1 hj with h | hjU
          · rw [h]
          · exact (hf1 j hjU).le
        rw [max_eq_left (by linarith), max_eq_left (by linarith)]
        nlinarith [hps j]
      · rw [if_neg hj]
        have hjU : j ∉ U := fun h => hj (Finset.mem_insert_of_mem h)
        rw [max_eq_right (by linarith [hYc j hjU]), mul_zero, mul_zero, zero_add]
        exact mul_nonneg (hps j) (le_max_right _ _)
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => key j
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_insert hj0] at hsum
    have hS : 1 < 1 / (1 - α) * (ps j0 + ∑ j ∈ U, ps j) := by
      rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ (by linarith)]; linarith
    have h1 := mul_le_mul_of_nonneg_left hsum hβ.le
    have h2 : 0 < (c - t) * (1 / (1 - α) * (ps j0 + ∑ j ∈ U, ps j) - 1) := mul_pos (by linarith) (by linarith)
    nlinarith
  · have key : ∀ j, ps j * max (Y j - c) 0 - (t - c) * (if j ∈ U then ps j else 0) ≤
        ps j * max (Y j - t) 0 := by
      intro j
      by_cases hj : j ∈ U
      · rw [if_pos hj, max_eq_left (by linarith [hf1 j hj])]
        have := mul_le_mul_of_nonneg_left (le_max_left (Y j - t) 0) (hps j)
        nlinarith
      · rw [if_neg hj, max_eq_right (by linarith [hYc j hj]), mul_zero, mul_zero, sub_zero]
        exact mul_nonneg (hps j) (le_max_right _ _)
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => key j
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter] at hsum
    have hS : 1 / (1 - α) * ∑ j ∈ U, ps j < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]; exact hU1
    have h1 := mul_le_mul_of_nonneg_left hsum hβ.le
    have h2 : 0 < (t - c) * (1 - 1 / (1 - α) * ∑ j ∈ U, ps j) := mul_pos (by linarith) (by linarith)
    nlinarith

/-- `q(f) = {t_f}` at a nondegenerate vertex. -/
lemma argminSet_vertex {φ : 𝒳 → E} (hφ : StronglyMeasurable φ) {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hκ0 : -κ ≤ κ) {α : ℝ} (hα1 : α < 1) {μ : Measure 𝒳}
    {xs : Fin J → 𝒳} {ps : Fin J → ℝ} (hps : ∀ j, 0 ≤ ps j)
    (hμ : μ = ∑ j, ENNReal.ofReal (ps j) • Measure.dirac (xs j)) {j0 : Fin J} {U : Finset (Fin J)}
    (hj0 : j0 ∉ U) (hU1 : ∑ j ∈ U, ps j < 1 - α) (hU2 : 1 - α < ∑ j ∈ U, ps j + ps j0) {f : E}
    (hf1 : ‖f‖ ≤ 1) (hf : VertexCond φ xs j0 U f) :
    argminSet φ α μ κ f = {projIcc (-κ) κ hκ0 ⟪f, φ (xs j0)⟫} := by
  have hmem : ⟪f, φ (xs j0)⟫ ∈ Icc (-κ) κ := abs_le.1 (abs_inner_le_of_norm_le hκ hf1 (xs j0))
  rw [projIcc_of_mem hκ0 hmem]
  ext t
  rw [mem_singleton_iff, mem_argminSet_iff]
  constructor
  · intro h
    by_contra hne
    have hne' : (t : ℝ) ≠ ⟪f, φ (xs j0)⟫ := fun h' => hne (Subtype.ext h')
    have h1 := h ⟨_, hmem⟩
    have h2 := cvObj_vertex_lt hφ hα1 hps hμ hj0 hU1 hU2 hf hne'
    simp only at h1
    linarith
  · rintro rfl t'
    by_cases h : (t' : ℝ) = ⟪f, φ (xs j0)⟫
    · exact le_of_eq (by rw [h])
    · exact (cvObj_vertex_lt hφ hα1 hps hμ hj0 hU1 hU2 hf h).le

end Vertex

section LinAlg
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A function respecting every linear relation on `D` is the restriction of `⟨·, G⟩` for some `G`. -/
lemma exists_inner_eq_of_relations (D : Set E) (w : E → ℝ)
    (hw : ∀ (p : ℕ) (e : Fin p → E) (a : Fin p → ℝ), (∀ i, e i ∈ D) → ∑ i, a i • e i = 0 →
      ∑ i, a i * w (e i) = 0) :
    ∃ G : E, ∀ e ∈ D, ⟪e, G⟫ = w e := by
  classical
  let A : (D →₀ ℝ) →ₗ[ℝ] E := Finsupp.linearCombination ℝ (fun d : D => (d : E))
  let B : (D →₀ ℝ) →ₗ[ℝ] ℝ := Finsupp.linearCombination ℝ (fun d : D => w d)
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro m hm
    rw [LinearMap.mem_ker] at hm ⊢
    simp only [A, B, Finsupp.linearCombination_apply, Finsupp.sum] at hm ⊢
    set s := m.support
    have c1 : ∑ i : Fin s.card, m (s.equivFin.symm i) • (((s.equivFin.symm i : s) : D) : E) =
        ∑ d ∈ s, m d • (d : E) :=
      (Equiv.sum_comp s.equivFin.symm (fun x : s => m x • ((x : D) : E))).trans
        (Finset.sum_coe_sort s (fun d => m d • (d : E)))
    have c2 : ∑ i : Fin s.card, m (s.equivFin.symm i) * w (((s.equivFin.symm i : s) : D) : E) =
        ∑ d ∈ s, m d * w (d : E) :=
      (Equiv.sum_comp s.equivFin.symm (fun x : s => m x * w ((x : D) : E))).trans
        (Finset.sum_coe_sort s (fun d => m d * w (d : E)))
    have h1 := hw s.card (fun i => ((s.equivFin.symm i : s) : D)) (fun i => m (s.equivFin.symm i))
      (fun i => ((s.equivFin.symm i : s) : D).2) (c1.trans hm)
    rw [c2] at h1
    simpa [smul_eq_mul] using h1
  let Abar := (LinearMap.ker A).liftQ A le_rfl
  have hinj : LinearMap.ker Abar = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  obtain ⟨g, hg⟩ := Abar.exists_leftInverse_of_injective hinj
  let C : E →ₗ[ℝ] ℝ := ((LinearMap.ker A).liftQ B hker).comp g
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap C), fun e he => ?_⟩
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
  have hA : A (Finsupp.single ⟨e, he⟩ 1) = e := by simp [A]
  have hAb : A (Finsupp.single ⟨e, he⟩ 1) =
      Abar (Submodule.mkQ (LinearMap.ker A) (Finsupp.single ⟨e, he⟩ 1)) := rfl
  have : C e = B (Finsupp.single ⟨e, he⟩ 1) := by
    rw [show C e = C (A (Finsupp.single ⟨e, he⟩ 1)) by rw [hA], hAb]
    show (LinearMap.ker A).liftQ B hker ((g.comp Abar) _) = _
    rw [hg, LinearMap.id_apply]
    rfl
  rw [this]; simp [B]

end LinAlg

section Points
variable {𝒳 E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Classical in
/-- `e` as a point of the unit ball (`0` if `‖e‖ > 1`, never used there). -/
def ballOf (e : E) : Ball E := if h : ‖e‖ ≤ 1 then ⟨e, mem_closedBall_zero_iff.2 h⟩ else ⟨0, by simp⟩

omit [InnerProductSpace ℝ E] in
lemma ballOf_coe {e : E} (h : ‖e‖ ≤ 1) : (ballOf e : E) = e := by simp [ballOf, h]

/-- The index point `(e, t_e)`, `t_e = ⟨e, φ(x₀)⟩` (clamped to `[−κ, κ]`, a no-op for `‖e‖ ≤ 1`). -/
def ptL (φ : 𝒳 → E) (κ : ℝ) (hκ0 : -κ ≤ κ) (x0 : 𝒳) (e : E) : Idx1 E κ :=
  (ballOf e, projIcc (-κ) κ hκ0 ⟪e, φ x0⟫)

lemma ptL_hinge {φ : 𝒳 → E} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : -κ ≤ κ) (x0 : 𝒳) {e : E} (he : ‖e‖ ≤ 1)
    (x : 𝒳) : hinge φ ((ptL φ κ hκ0 x0 e).1 : E) (ptL φ κ hκ0 x0 e).2 x = hinge φ e ⟪e, φ x0⟫ x := by
  have hmem := abs_le.1 (abs_inner_le_of_norm_le hκ he x0)
  simp only [ptL, ballOf_coe he, projIcc_of_mem hκ0 hmem]

lemma smul_normalize (x : E) : ‖x‖ • (‖x‖⁻¹ • x) = x := by
  by_cases h : x = 0
  · simp [h]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_smul]

lemma norm_normalize_le (x : E) : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
  rw [norm_smul, norm_inv, norm_norm]
  by_cases h : x = 0
  · simp [h]
  · rw [inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

end Points

section Relations
variable {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {φ : 𝒳 → E} {κ : ℝ} {P Q : Measure 𝒳} [IsProbabilityMeasure P]
  [IsProbabilityMeasure Q] {v : C(Idx2 E κ, ℝ)}

lemma linCons_zero_inl (hv : LinCons φ P Q κ v) (a : Ball E) (ha : (a : E) = 0) (t : Icc (-κ) κ) :
    v (Sum.inl (a, t)) = 0 := by
  have := hv 1 ![Sum.inl (a, t)] ![1] ?_
  · simpa using this
  · unfold gpVar
    have h1 : (fun w => ∑ i, (![1] : Fin 1 → ℝ) i * hingeP φ ((![Sum.inl (a, t)] : Fin 1 → Idx2 E κ) i) w) =
        fun _ => max (-(t : ℝ)) 0 := by
      funext w; simp [hingeP, hinge, ha]
    have h2 : (fun w => ∑ i, (![1] : Fin 1 → ℝ) i * hingeQ φ ((![Sum.inl (a, t)] : Fin 1 → Idx2 E κ) i) w) =
        fun _ => 0 := by
      funext w; simp [hingeQ]
    rw [h1, h2, variance_fun_const, variance_fun_const]; ring

lemma linCons_zero_inr (hv : LinCons φ P Q κ v) (a : Ball E) (ha : (a : E) = 0) (t : Icc (-κ) κ) :
    v (Sum.inr (a, t)) = 0 := by
  have := hv 1 ![Sum.inr (a, t)] ![1] ?_
  · simpa using this
  · unfold gpVar
    have h1 : (fun w => ∑ i, (![1] : Fin 1 → ℝ) i * hingeP φ ((![Sum.inr (a, t)] : Fin 1 → Idx2 E κ) i) w) =
        fun _ => 0 := by
      funext w; simp [hingeP]
    have h2 : (fun w => ∑ i, (![1] : Fin 1 → ℝ) i * hingeQ φ ((![Sum.inr (a, t)] : Fin 1 → Idx2 E κ) i) w) =
        fun _ => max (-(t : ℝ)) 0 := by
      funext w; simp [hingeQ, hinge, ha]
    rw [h1, h2, variance_fun_const, variance_fun_const]; ring

variable {J : ℕ}

/-- A linear relation in `D ⊆ 𝔹` (vertex directions) gives an a.s. relation of the `P`-copy of `𝔾`. -/
lemma relP (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : -κ ≤ κ) {xs : Fin J → 𝒳}
    {ps : Fin J → ℝ} (hps : ∀ j, 0 ≤ ps j) (hP : P = ∑ j, ENNReal.ofReal (ps j) • Measure.dirac (xs j))
    {j0 : Fin J} {U : Finset (Fin J)} {D : Set E}
    (hD : ∀ e ∈ D, ‖e‖ ≤ 1 ∧ (e = 0 ∨ VertexCond φ xs j0 U e)) (hv : LinCons φ P Q κ v) (p : ℕ)
    (e : Fin p → E) (a : Fin p → ℝ) (he : ∀ i, e i ∈ D) (h0 : ∑ i, a i • e i = 0) :
    ∑ i, a i * v (Sum.inl (ptL φ κ hκ0 (xs j0) (e i))) = 0 := by
  apply hv p (fun i => Sum.inl (ptL φ κ hκ0 (xs j0) (e i))) a
  unfold gpVar
  have h1 : (fun w => ∑ i, a i * hingeP φ ((fun i => (Sum.inl (ptL φ κ hκ0 (xs j0) (e i)) : Idx2 E κ)) i) w) =
      fun w => ∑ i, a i * hinge φ (e i) ⟪e i, φ (xs j0)⟫ w := by
    funext w; refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hingeP, Sum.elim_inl]; rw [ptL_hinge hκ hκ0 _ (hD _ (he i)).1]
  have h2 : (fun w => ∑ i, a i * hingeQ φ ((fun i => (Sum.inl (ptL φ κ hκ0 (xs j0) (e i)) : Idx2 E κ)) i) w) =
      fun _ => 0 := by
    funext w; simp [hingeQ]
  have hmeas : Measurable fun w => ∑ i, a i * hinge φ (e i) ⟪e i, φ (xs j0)⟫ w :=
    Finset.measurable_sum _ fun i _ => (measurable_hinge hφ _ _).const_mul _
  rw [h1, h2, variance_fun_const, variance_diracSum xs hps hP hmeas]
  have h3 : (fun j => ∑ i, a i * hinge φ (e i) ⟪e i, φ (xs j0)⟫ (xs j)) = fun _ => 0 := by
    funext j
    have h4 : ∀ i, a i * hinge φ (e i) ⟪e i, φ (xs j0)⟫ (xs j) = a i * ⟪e i, vertexVec φ xs j0 U j⟫ :=
      fun i => by rw [hinge_vertex (hD _ (he i)).2 j]
    rw [Finset.sum_congr rfl fun i _ => h4 i]
    rw [show ∑ i, a i * ⟪e i, vertexVec φ xs j0 U j⟫ = ⟪∑ i, a i • e i, vertexVec φ xs j0 U j⟫ by
      rw [sum_inner]; simp_rw [real_inner_smul_left], h0, inner_zero_left]
  rw [h3, discVar_zero]; ring

/-- The `Q`-copy version of `relP`. -/
lemma relQ (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : -κ ≤ κ) {ys : Fin J → 𝒳}
    {qs : Fin J → ℝ} (hqs : ∀ j, 0 ≤ qs j) (hQ : Q = ∑ j, ENNReal.ofReal (qs j) • Measure.dirac (ys j))
    {j0 : Fin J} {U : Finset (Fin J)} {D : Set E}
    (hD : ∀ e ∈ D, ‖e‖ ≤ 1 ∧ (e = 0 ∨ VertexCond φ ys j0 U e)) (hv : LinCons φ P Q κ v) (p : ℕ)
    (e : Fin p → E) (a : Fin p → ℝ) (he : ∀ i, e i ∈ D) (h0 : ∑ i, a i • e i = 0) :
    ∑ i, a i * v (Sum.inr (ptL φ κ hκ0 (ys j0) (e i))) = 0 := by
  apply hv p (fun i => Sum.inr (ptL φ κ hκ0 (ys j0) (e i))) a
  unfold gpVar
  have h1 : (fun w => ∑ i, a i * hingeQ φ ((fun i => (Sum.inr (ptL φ κ hκ0 (ys j0) (e i)) : Idx2 E κ)) i) w) =
      fun w => ∑ i, a i * hinge φ (e i) ⟪e i, φ (ys j0)⟫ w := by
    funext w; refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hingeQ, Sum.elim_inr]; rw [ptL_hinge hκ hκ0 _ (hD _ (he i)).1]
  have h2 : (fun w => ∑ i, a i * hingeP φ ((fun i => (Sum.inr (ptL φ κ hκ0 (ys j0) (e i)) : Idx2 E κ)) i) w) =
      fun _ => 0 := by
    funext w; simp [hingeP]
  have hmeas : Measurable fun w => ∑ i, a i * hinge φ (e i) ⟪e i, φ (ys j0)⟫ w :=
    Finset.measurable_sum _ fun i _ => (measurable_hinge hφ _ _).const_mul _
  rw [h1, h2, variance_fun_const, variance_diracSum ys hqs hQ hmeas]
  have h3 : (fun j => ∑ i, a i * hinge φ (e i) ⟪e i, φ (ys j0)⟫ (ys j)) = fun _ => 0 := by
    funext j
    have h4 : ∀ i, a i * hinge φ (e i) ⟪e i, φ (ys j0)⟫ (ys j) = a i * ⟪e i, vertexVec φ ys j0 U j⟫ :=
      fun i => by rw [hinge_vertex (hD _ (he i)).2 j]
    rw [Finset.sum_congr rfl fun i _ => h4 i]
    rw [show ∑ i, a i * ⟪e i, vertexVec φ ys j0 U j⟫ = ⟪∑ i, a i • e i, vertexVec φ ys j0 U j⟫ by
      rw [sum_inner]; simp_rw [real_inner_smul_left], h0, inner_zero_left]
  rw [h3, discVar_zero]; ring

/-- `H_P(−g) = β 𝔾(−g, t_{−g})` for `g ∈ K° ∩ 𝔹` (`0` at `g = 0`). -/
lemma HfunP_vertex (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : -κ ≤ κ) {α : ℝ} (hα1 : α < 1)
    {xs : Fin J → 𝒳} {ps : Fin J → ℝ} (hps : ∀ j, 0 ≤ ps j)
    (hP : P = ∑ j, ENNReal.ofReal (ps j) • Measure.dirac (xs j)) {j0 : Fin J} {U : Finset (Fin J)}
    (hj0 : j0 ∉ U) (hU1 : ∑ j ∈ U, ps j < 1 - α) (hU2 : 1 - α < ∑ j ∈ U, ps j + ps j0) {Kp : Set E}
    (hvert : ∀ g ∈ Kp, g ≠ 0 → VertexCond φ xs j0 U (-g)) (hv : LinCons φ P Q κ v) (g : Ball E)
    (hg : (g : E) ∈ Kp) :
    Hfun φ α P κ Sum.inl v (ballNeg g) = 1 / (1 - α) * v (Sum.inl (ptL φ κ hκ0 (xs j0) (-(g : E)))) := by
  have hg1 : ‖-(g : E)‖ ≤ 1 := by rw [norm_neg]; exact mem_closedBall_zero_iff.1 g.2
  have hb : ballOf (-(g : E)) = ballNeg g := Subtype.ext (ballOf_coe hg1)
  unfold Hfun
  by_cases h0 : (g : E) = 0
  · have hz : ∀ t, v (Sum.inl (ballNeg g, t)) = 0 := fun t =>
      linCons_zero_inl hv _ (by simp [ballNeg, h0]) t
    obtain ⟨t0, ht0⟩ := argminSet_nonempty hφ hκ (by linarith) α P ((ballNeg g : Ball E) : E)
    have himg : (fun t => v (Sum.inl (ballNeg g, t))) '' argminSet φ α P κ ((ballNeg g : Ball E) : E) = {0} := by
      ext y; simp only [mem_image, mem_singleton_iff]
      constructor
      · rintro ⟨t, -, rfl⟩; exact hz t
      · rintro rfl; exact ⟨t0, ht0, hz t0⟩
    rw [himg, csInf_singleton]
    simp only [ptL, hb, hz, mul_zero]
  · have hargs : argminSet φ α P κ ((ballNeg g : Ball E) : E) =
        {projIcc (-κ) κ hκ0 ⟪-(g : E), φ (xs j0)⟫} :=
      argminSet_vertex hφ hκ hκ0 hα1 hps hP hj0 hU1 hU2 hg1 (hvert _ hg h0)
    rw [hargs, image_singleton, csInf_singleton]
    simp only [ptL, hb]

/-- `H_Q(g) = β 𝔾(g, s_g)` for `g ∈ K° ∩ 𝔹` (`0` at `g = 0`). -/
lemma HfunQ_vertex (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : -κ ≤ κ) {α : ℝ} (hα1 : α < 1)
    {ys : Fin J → 𝒳} {qs : Fin J → ℝ} (hqs : ∀ j, 0 ≤ qs j)
    (hQ : Q = ∑ j, ENNReal.ofReal (qs j) • Measure.dirac (ys j)) {j0 : Fin J} {U : Finset (Fin J)}
    (hj0 : j0 ∉ U) (hU1 : ∑ j ∈ U, qs j < 1 - α) (hU2 : 1 - α < ∑ j ∈ U, qs j + qs j0) {Kp : Set E}
    (hvert : ∀ g ∈ Kp, g ≠ 0 → VertexCond φ ys j0 U g) (hv : LinCons φ P Q κ v) (g : Ball E)
    (hg : (g : E) ∈ Kp) :
    Hfun φ α Q κ Sum.inr v g = 1 / (1 - α) * v (Sum.inr (ptL φ κ hκ0 (ys j0) (g : E))) := by
  have hg1 : ‖(g : E)‖ ≤ 1 := mem_closedBall_zero_iff.1 g.2
  have hb : ballOf (g : E) = g := Subtype.ext (ballOf_coe hg1)
  unfold Hfun
  by_cases h0 : (g : E) = 0
  · have hz : ∀ t, v (Sum.inr (g, t)) = 0 := fun t => linCons_zero_inr hv _ h0 t
    obtain ⟨t0, ht0⟩ := argminSet_nonempty hφ hκ (by linarith) α Q (g : E)
    have himg : (fun t => v (Sum.inr (g, t))) '' argminSet φ α Q κ (g : E) = {0} := by
      ext y; simp only [mem_image, mem_singleton_iff]
      constructor
      · rintro ⟨t, -, rfl⟩; exact hz t
      · rintro rfl; exact ⟨t0, ht0, hz t0⟩
    rw [himg, csInf_singleton]
    simp only [ptL, hb, hz, mul_zero]
  · have hargs : argminSet φ α Q κ (g : E) = {projIcc (-κ) κ hκ0 ⟪(g : E), φ (ys j0)⟫} :=
      argminSet_vertex hφ hκ hκ0 hα1 hqs hQ hj0 hU1 hU2 hg1 (hvert _ hg h0)
    rw [hargs, image_singleton, csInf_singleton]
    simp only [ptL, hb]

end Relations

theorem boundary_vertex : Claims.boundary_vertex := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ Ω _ μ _ ξ η n m r cP cQ Ω' _ μ' _ 𝔾 J xs ps j0 U J' ys qs j0' U'
    hφ hκ hα0 hα1 hS hSc h𝔾 hAB hps hP hj0 hU1 hU2 hvP hqs hQ hj0' hU1' hU2' hvQ
  set Kp := polarSet (closure (coneHull (region φ α Q - region φ α P))) with hKp
  have hκ0 : -κ ≤ κ := by have := kappa_nonneg hκ P; linarith
  set β := 1 / (1 - α) with hβ
  have hvP' : ∀ g ∈ Kp, g ≠ 0 → VertexCond φ xs j0 U (-g) := fun g hg h0 => hvP g hg h0
  have hvQ' : ∀ g ∈ Kp, g ≠ 0 → VertexCond φ ys j0' U' g := fun g hg h0 => hvQ g hg h0
  have hsmul : ∀ c : ℝ, 0 ≤ c → ∀ x ∈ Kp, c • x ∈ Kp := fun c hc x hx s hs => by
    rw [real_inner_smul_left]; exact mul_nonpos_of_nonneg_of_nonpos hc (hx s hs)
  let DP : Set E := {e | ‖e‖ ≤ 1 ∧ -e ∈ Kp}
  let DQ : Set E := {e | ‖e‖ ≤ 1 ∧ e ∈ Kp}
  have hDP : ∀ e ∈ DP, ‖e‖ ≤ 1 ∧ (e = 0 ∨ VertexCond φ xs j0 U e) := by
    rintro e ⟨he1, he2⟩
    refine ⟨he1, ?_⟩
    by_cases h : e = 0
    · exact Or.inl h
    · right; have := hvP' (-e) he2 (neg_ne_zero.2 h); rwa [neg_neg] at this
  have hDQ : ∀ e ∈ DQ, ‖e‖ ≤ 1 ∧ (e = 0 ∨ VertexCond φ ys j0' U' e) := by
    rintro e ⟨he1, he2⟩
    refine ⟨he1, ?_⟩
    by_cases h : e = 0
    · exact Or.inl h
    · exact Or.inr (hvQ' e he2 h)
  have hGP : ∀ ω', LinCons φ P Q κ (𝔾 ω') → ∃ G : E, ∀ e ∈ DP,
      ⟪e, G⟫ = β * 𝔾 ω' (Sum.inl (ptL φ κ hκ0 (xs j0) e)) := by
    intro ω' hv
    refine exists_inner_eq_of_relations DP _ fun p e a he h0 => ?_
    have := relP hφ hκ hκ0 hps hP hDP hv p e a he h0
    calc ∑ i, a i * (β * 𝔾 ω' (Sum.inl (ptL φ κ hκ0 (xs j0) (e i))))
        = β * ∑ i, a i * 𝔾 ω' (Sum.inl (ptL φ κ hκ0 (xs j0) (e i))) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have hGQ : ∀ ω', LinCons φ P Q κ (𝔾 ω') → ∃ G : E, ∀ e ∈ DQ,
      ⟪e, G⟫ = β * 𝔾 ω' (Sum.inr (ptL φ κ hκ0 (ys j0') e)) := by
    intro ω' hv
    refine exists_inner_eq_of_relations DQ _ fun p e a he h0 => ?_
    have := relQ hφ hκ hκ0 hqs hQ hDQ hv p e a he h0
    calc ∑ i, a i * (β * 𝔾 ω' (Sum.inr (ptL φ κ hκ0 (ys j0') (e i))))
        = β * ∑ i, a i * 𝔾 ω' (Sum.inr (ptL φ κ hκ0 (ys j0') (e i))) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [this, mul_zero]
  choose! GP hGP' using hGP
  choose! GQ hGQ' using hGQ
  have hlin : ∀ᵐ ω' ∂μ', ∀ g : Ball E, (g : E) ∈ Kp →
      Hfun φ α P κ Sum.inl (𝔾 ω') (ballNeg g) = ⟪-(g : E), GP ω'⟫ ∧
        Hfun φ α Q κ Sum.inr (𝔾 ω') g = ⟪(g : E), GQ ω'⟫ := by
    filter_upwards [ae_linCons h𝔾] with ω' hv g hg
    have hg1 : ‖(g : E)‖ ≤ 1 := mem_closedBall_zero_iff.1 g.2
    constructor
    · rw [HfunP_vertex hφ hκ hκ0 hα1 hps hP hj0 hU1 hU2 hvP' hv g hg,
        hGP' ω' hv (-(g : E)) ⟨by rwa [norm_neg], by rwa [neg_neg]⟩]
    · rw [HfunQ_vertex hφ hκ hκ0 hα1 hqs hQ hj0' hU1' hU2' hvQ' hv g hg, hGQ' ω' hv (g : E) ⟨hg1, hg⟩]
  refine ⟨GP, GQ, hlin, ?_, (boundary_linear 𝒳 E φ κ α P Q Ω μ ξ η n m r cP cQ Ω' μ' 𝔾 GP GQ hφ hκ hα0 hα1
    hS hSc h𝔾 hAB hlin).1⟩
  intro p f g u w hf hg
  have hnf : ∀ i, ‖-f i‖⁻¹ • -f i ∈ DP := fun i => ⟨norm_normalize_le _, by
    rw [← smul_neg, neg_neg]; exact hsmul _ (inv_nonneg.2 (norm_nonneg _)) _ (hf i)⟩
  have hng : ∀ i, ‖g i‖⁻¹ • g i ∈ DQ := fun i =>
    ⟨norm_normalize_le _, hsmul _ (inv_nonneg.2 (norm_nonneg _)) _ (hg i)⟩
  let Z : Fin (p + p) → Idx2 E κ :=
    Fin.append (fun i => Sum.inl (ptL φ κ hκ0 (xs j0) (‖-f i‖⁻¹ • -f i)))
      (fun i => Sum.inr (ptL φ κ hκ0 (ys j0') (‖g i‖⁻¹ • g i)))
  let Uc : Fin (p + p) → ℝ := Fin.append (fun i => u i * ‖-f i‖ * β) (fun i => w i * ‖g i‖ * β)
  have hae : (fun ω' => ∑ i, u i * ⟪-f i, GP ω'⟫ + ∑ i, w i * ⟪g i, GQ ω'⟫) =ᵐ[μ']
      fun ω' => ∑ k, Uc k * 𝔾 ω' (Z k) := by
    filter_upwards [ae_linCons h𝔾] with ω' hv
    rw [Fin.sum_univ_add]
    simp only [Z, Uc, Fin.append_left, Fin.append_right]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
    · have e1 : ⟪-f i, GP ω'⟫ = ‖-f i‖ * ⟪‖-f i‖⁻¹ • -f i, GP ω'⟫ := by
        rw [← real_inner_smul_left, smul_normalize]
      rw [e1, hGP' ω' hv _ (hnf i)]; ring
    · have e1 : ⟪g i, GQ ω'⟫ = ‖g i‖ * ⟪‖g i‖⁻¹ • g i, GQ ω'⟫ := by
        rw [← real_inner_smul_left, smul_normalize]
      rw [e1, hGQ' ω' hv _ (hng i)]; ring
  rw [Measure.map_congr hae, h𝔾.2 (p + p) Z Uc]
  congr 2
  unfold gpVar
  have hPf : (fun x => ∑ k, Uc k * hingeP φ (Z k) x) =
      fun x => ∑ i, u i * ‖-f i‖ * β * hinge φ (‖-f i‖⁻¹ • -f i) ⟪‖-f i‖⁻¹ • -f i, φ (xs j0)⟫ x := by
    funext x
    rw [Fin.sum_univ_add]
    simp only [Z, Uc, Fin.append_left, Fin.append_right, hingeP, Sum.elim_inl, Sum.elim_inr, mul_zero,
      Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ptL_hinge hκ hκ0 _ (hnf i).1]
  have hQf : (fun x => ∑ k, Uc k * hingeQ φ (Z k) x) =
      fun x => ∑ i, w i * ‖g i‖ * β * hinge φ (‖g i‖⁻¹ • g i) ⟪‖g i‖⁻¹ • g i, φ (ys j0')⟫ x := by
    funext x
    rw [Fin.sum_univ_add]
    simp only [Z, Uc, Fin.append_left, Fin.append_right, hingeQ, Sum.elim_inl, Sum.elim_inr, mul_zero,
      Finset.sum_const_zero, zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ptL_hinge hκ hκ0 _ (hng i).1]
  have hmP : Measurable
      (fun x => ∑ i, u i * ‖-f i‖ * β * hinge φ (‖-f i‖⁻¹ • -f i) ⟪‖-f i‖⁻¹ • -f i, φ (xs j0)⟫ x) :=
    Finset.measurable_sum _ fun i _ => (measurable_hinge hφ _ _).const_mul _
  have hmQ : Measurable
      (fun x => ∑ i, w i * ‖g i‖ * β * hinge φ (‖g i‖⁻¹ • g i) ⟪‖g i‖⁻¹ • g i, φ (ys j0')⟫ x) :=
    Finset.measurable_sum _ fun i _ => (measurable_hinge hφ _ _).const_mul _
  rw [hPf, hQf, variance_diracSum xs hps hP hmP, variance_diracSum ys hqs hQ hmQ]
  have hPa : (fun j => ∑ i, u i * ‖-f i‖ * β *
        hinge φ (‖-f i‖⁻¹ • -f i) ⟪‖-f i‖⁻¹ • -f i, φ (xs j0)⟫ (xs j)) =
      fun j => β * ∑ i, u i * ⟪-f i, vertexVec φ xs j0 U j⟫ := by
    funext j; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [hinge_vertex (hDP _ (hnf i)).2 j]
    have : ‖-f i‖ * ⟪‖-f i‖⁻¹ • -f i, vertexVec φ xs j0 U j⟫ = ⟪-f i, vertexVec φ xs j0 U j⟫ := by
      rw [← real_inner_smul_left, smul_normalize]
    rw [← this]; ring
  have hQa : (fun j => ∑ i, w i * ‖g i‖ * β *
        hinge φ (‖g i‖⁻¹ • g i) ⟪‖g i‖⁻¹ • g i, φ (ys j0')⟫ (ys j)) =
      fun j => β * ∑ i, w i * ⟪g i, vertexVec φ ys j0' U' j⟫ := by
    funext j; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [hinge_vertex (hDQ _ (hng i)).2 j]
    have : ‖g i‖ * ⟪‖g i‖⁻¹ • g i, vertexVec φ ys j0' U' j⟫ = ⟪g i, vertexVec φ ys j0' U' j⟫ := by
      rw [← real_inner_smul_left, smul_normalize]
    rw [← this]; ring
  rw [hPa, hQa, discVar_mul, discVar_mul]; ring

end StatFormal.Wave30z
