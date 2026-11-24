import StatFormal.Archive.Wave30z.RouteDual
import StatFormal.Archive.Wave30z.RouteMoreau
import StatFormal.Lib.Donsker.TwoSample
import StatFormal.Lib.Donsker.Nets

/-!
# Route — wave 30z `thm:boundary` (b), (i), (ii) and `cor:boundary-linear` (untrusted)

* (b) `boundary_donsker`: the general two-sample Donsker theorem (`Foundations/Donsker/TwoSample`) for the classes
  `hingeP`, `hingeQ` on the joint index `Idx2 = (𝔹_r × [−κ,κ]) ⊕ (𝔹_r × [−κ,κ])` (exponential nets: volume argument,
  products, disjoint unions; bounded by `2κ + 1`, Lipschitz with constant `3κ + 1` in the disjoint-union metric), and
  uniqueness of laws on `C(Idx2, ℝ)` from their finite-dimensional Gaussian laws.
* (i) `boundary_every`: `r_k(Γ_k − Γ) = Λ(V_k)` with the continuous linear `Λ v (g,t,s) = −β v(left(−g,t)) − β v(right(g,s))`;
  the frozen-route sup-functional delta method `boundary_sup_limit` (Wave 30v) gives
  `r_k(D̂ − D) ⇒ sup_{Θ₀} Λ(𝕍)`, `Θ₀ = argmax Γ`; with `𝕍 = S 𝔾` (`S` multiplies the left copy by `c_P`, the
  right copy by `c_Q`), the deterministic identity `sup_{Θ₀} Λ(S v) = sup_{g ∈ G*} {−c_P H_P(−g) − c_Q H_Q(g)}`
  (`Θ₀ = {(g,t,s) : g ∈ G*, t ∈ q_P(−g), s ∈ q_Q(g)}`, minima attained on the compact quantile sets).
* (ii) `boundary_contact`: `D = 0`, `G* = (B − A)° ∩ 𝔹 = K° ∩ 𝔹`, tangent cones from Wave 30v.
* `boundary_linear`: the limit is a.s. `sup_{K° ∩ 𝔹} ⟨g, c_P G_P − c_Q G_Q⟩ = dist(·, K) = ‖Π_{K°}(·)‖`
  (Wave 30v `boundary_polar_infDist`, Moreau `metricProj_polar_norm`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30z

open StatFormal.TrimmedMMD.Concentration (region empirical)
open StatFormal.TrimmedMMD.Unconditional (setDist Dpop Demp)
open StatFormal.Wave30v (supFun Ball ballNeg polarSet coneHull supportFn tanCone argmaxSet supDeriv)
open StatFormal.Foundations.Donsker

attribute [local instance] Metric.metricSpaceSum

section Index
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma hasExpNets_Idx1 (κ : ℝ) : HasExpNets (Idx1 E κ) :=
  (hasExpNets_of_isBounded (S := closedBall (0 : E) 1) isBounded_closedBall).prod
    (hasExpNets_of_isBounded (S := Icc (-κ) κ) (isBounded_Icc (-κ) κ))

lemma hasExpNets_Idx2 (κ : ℝ) : HasExpNets (Idx2 E κ) :=
  (hasExpNets_Idx1 κ).sum (hasExpNets_Idx1 κ)

end Index

section Classes
variable {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {φ : 𝒳 → E} {κ : ℝ}

lemma abs_hinge_idx_le (hκ : ∀ x, ‖φ x‖ ≤ κ) (z : Idx1 E κ) (w : 𝒳) : |hinge φ (z.1 : E) z.2 w| ≤ 2 * κ :=
  abs_hinge_le hκ (mem_closedBall_zero_iff.1 z.1.2) (abs_le.2 ⟨z.2.2.1, z.2.2.2⟩) w

lemma abs_hinge_idx_sub_le (hκ : ∀ x, ‖φ x‖ ≤ κ) (z z' : Idx1 E κ) (w : 𝒳) :
    |hinge φ (z.1 : E) z.2 w - hinge φ (z'.1 : E) z'.2 w| ≤ (κ + 1) * dist z z' := by
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ w)
  have h := abs_hinge_sub_le hκ (z.1 : E) (z'.1 : E) z.2 z'.2 w
  have h1 : ‖(z.1 : E) - (z'.1 : E)‖ ≤ dist z z' := by
    rw [← dist_eq_norm]; exact (Subtype.dist_eq z.1 z'.1).symm.le.trans (by rw [Prod.dist_eq]; exact le_max_left _ _)
  have h2 : |(z.2 : ℝ) - (z'.2 : ℝ)| ≤ dist z z' := by
    rw [← Real.dist_eq]; exact (Subtype.dist_eq z.2 z'.2).symm.le.trans (by rw [Prod.dist_eq]; exact le_max_right _ _)
  nlinarith [mul_le_mul_of_nonneg_left h1 hκ0]

lemma one_le_dist_inl_inr (a b : Idx1 E κ) : 1 ≤ dist (Sum.inl a : Idx2 E κ) (Sum.inr b) :=
  Metric.Sum.one_le_dist_inl_inr

lemma isLipClass_hingeP (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) :
    IsLipClass (hingeP φ (κ := κ)) (2 * κ + 1) (3 * κ + 1) where
  meas z := by
    rcases z with z | z
    · exact measurable_hinge hφ _ _
    · exact measurable_const
  bound z w := by
    have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ w)
    rcases z with z | z
    · exact (abs_hinge_idx_le hκ z w).trans (by linarith)
    · simp [hingeP]; linarith
  lip z z' w := by
    have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ w)
    rcases z with z | z <;> rcases z' with z' | z'
    · exact (abs_hinge_idx_sub_le hκ z z' w).trans
        (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
    · have h1 := one_le_dist_inl_inr z z'
      simp only [hingeP, Sum.elim_inl, Sum.elim_inr, sub_zero]
      calc |hinge φ (z.1 : E) z.2 w| ≤ 2 * κ := abs_hinge_idx_le hκ z w
        _ ≤ (3 * κ + 1) * 1 := by linarith
        _ ≤ (3 * κ + 1) * dist (Sum.inl z : Idx2 E κ) (Sum.inr z') :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
    · have h1 := one_le_dist_inl_inr z' z
      rw [dist_comm] at h1
      simp only [hingeP, Sum.elim_inl, Sum.elim_inr, zero_sub, abs_neg]
      calc |hinge φ (z'.1 : E) z'.2 w| ≤ 2 * κ := abs_hinge_idx_le hκ z' w
        _ ≤ (3 * κ + 1) * 1 := by linarith
        _ ≤ (3 * κ + 1) * dist (Sum.inr z : Idx2 E κ) (Sum.inl z') :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
    · simp only [hingeP, Sum.elim_inr, sub_self, abs_zero]
      exact mul_nonneg (by linarith) dist_nonneg

lemma isLipClass_hingeQ (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) :
    IsLipClass (hingeQ φ (κ := κ)) (2 * κ + 1) (3 * κ + 1) where
  meas z := by
    rcases z with z | z
    · exact measurable_const
    · exact measurable_hinge hφ _ _
  bound z w := by
    have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ w)
    rcases z with z | z
    · simp [hingeQ]; linarith
    · exact (abs_hinge_idx_le hκ z w).trans (by linarith)
  lip z z' w := by
    have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ w)
    rcases z with z | z <;> rcases z' with z' | z'
    · simp only [hingeQ, Sum.elim_inl, sub_self, abs_zero]
      exact mul_nonneg (by linarith) dist_nonneg
    · have h1 := one_le_dist_inl_inr z z'
      simp only [hingeQ, Sum.elim_inl, Sum.elim_inr, zero_sub, abs_neg]
      calc |hinge φ (z'.1 : E) z'.2 w| ≤ 2 * κ := abs_hinge_idx_le hκ z' w
        _ ≤ (3 * κ + 1) * 1 := by linarith
        _ ≤ (3 * κ + 1) * dist (Sum.inl z : Idx2 E κ) (Sum.inr z') :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
    · have h1 := one_le_dist_inl_inr z' z
      rw [dist_comm] at h1
      simp only [hingeQ, Sum.elim_inl, Sum.elim_inr, sub_zero]
      calc |hinge φ (z.1 : E) z.2 w| ≤ 2 * κ := abs_hinge_idx_le hκ z w
        _ ≤ (3 * κ + 1) * 1 := by linarith
        _ ≤ (3 * κ + 1) * dist (Sum.inr z : Idx2 E κ) (Sum.inl z') :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
    · exact (abs_hinge_idx_sub_le hκ z z' w).trans
        (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)

end Classes

section Proc
variable {X 𝒳 : Type*} [MeasurableSpace 𝒳] [PseudoMetricSpace X]

lemma abs_oneTerm_le {P : Measure 𝒳} [IsProbabilityMeasure P] {h : 𝒳 → ℝ} {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ w, |h w| ≤ b) (n : ℕ) (r : ℝ) (x : ℕ → 𝒳) : |oneTerm h P n r x| ≤ 2 * |r| * b := by
  have h1 : |(∑ i ∈ Finset.range n, h (x i)) / n| ≤ b := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [hb0]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [abs_div, abs_of_pos hn', div_le_iff₀ hn']
      calc |∑ i ∈ Finset.range n, h (x i)| ≤ ∑ i ∈ Finset.range n, |h (x i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range n, b := Finset.sum_le_sum fun i _ => hb _
        _ = b * n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have h2 : |∫ w, h w ∂P| ≤ b := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := h) (C := b) (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs]; exact hb w)
    simpa using this
  unfold oneTerm
  rw [abs_mul]
  calc |r| * |(∑ i ∈ Finset.range n, h (x i)) / n - ∫ w, h w ∂P|
      ≤ |r| * (b + b) := mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2)) (abs_nonneg _)
    _ = 2 * |r| * b := by ring

lemma continuous_tsProc {F G : X → 𝒳 → ℝ} {B L : ℝ} (hF : IsLipClass F B L) (hG : IsLipClass G B L) (hL : 0 ≤ L)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n m : ℕ) (r : ℝ) (x y : ℕ → 𝒳) :
    Continuous (tsProc F G P Q n m r x y) := by
  have hiF := fun z => integrable_of_abs_le (P := P) (hF.meas z) (hF.bound z)
  have hiG := fun z => integrable_of_abs_le (P := Q) (hG.meas z) (hG.bound z)
  refine (LipschitzWith.of_dist_le_mul (K := (4 * |r| * L).toNNReal) fun z z' => ?_).continuous
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  have heq : tsProc F G P Q n m r x y z - tsProc F G P Q n m r x y z' =
      oneTerm (fun w => F z w - F z' w) P n r x + oneTerm (fun w => G z w - G z' w) Q m r y := by
    simp only [tsProc_eq]
    rw [← oneTerm_sub P (hiF z) (hiF z'), ← oneTerm_sub Q (hiG z) (hiG z')]
    ring
  rw [heq]
  have hd : 0 ≤ L * dist z z' := mul_nonneg hL dist_nonneg
  have h1 := abs_oneTerm_le (P := P) hd (fun w => hF.lip z z' w) n r x
  have h2 := abs_oneTerm_le (P := Q) hd (fun w => hG.lip z z' w) m r y
  calc |oneTerm (fun w => F z w - F z' w) P n r x + oneTerm (fun w => G z w - G z' w) Q m r y|
      ≤ 2 * |r| * (L * dist z z') + 2 * |r| * (L * dist z z') := (abs_add_le _ _).trans (add_le_add h1 h2)
    _ = 4 * |r| * L * dist z z' := by ring

end Proc

section Donsker

theorem boundary_donsker : Claims.boundary_donsker := by
  intro 𝒳 E _ _ _ _ φ κ P Q _ _ Ω _ μ _ ξ η n m r cP cQ V hφ hκ hS hSc hV
  obtain ⟨hξ, hη, hiξ, hiη, hlξ, hlη, hind⟩ := hS
  obtain ⟨hn1, hm1, hn, hm, hr, -, hrn, hrm⟩ := hSc
  have hκ0 := kappa_nonneg hκ P
  obtain ⟨ν, hν, hνf⟩ := donsker_twoSample (hasExpNets_Idx2 (E := E) κ) μ P Q ξ η hξ hη hiξ hiη hlξ hlη hind
    (isLipClass_hingeP hφ hκ) (isLipClass_hingeQ hφ hκ) (by linarith) (by linarith) n m hn1 hm1 hn hm r hr cP cQ
    hrn hrm V (fun k ω z => hV k ω z)
  have hlaw : ∀ (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
      (𝕍 : Ω' → C(Idx2 E κ, ℝ)), IsLimitGP φ P Q cP cQ κ μ' 𝕍 → μ'.map 𝕍 = (ν : Measure C(Idx2 E κ, ℝ)) := by
    intro Ω' _ μ' _ 𝕍 h𝕍
    refine measure_ext_of_linEval _ _ fun p z u => ?_
    rw [AEMeasurable.map_map_of_aemeasurable (continuous_linEval z u).measurable.aemeasurable h𝕍.1, hνf p z u]
    exact h𝕍.2 p z u
  refine ⟨⟨ν, measurable_id.aemeasurable, fun p z u => ?_⟩, fun ν₁ ν₂ h1 h2 => ?_, fun Ω' _ μ' _ 𝕍 h𝕍 => ?_⟩
  · exact hνf p z u
  · have e1 := hlaw _ (ν₁ : Measure C(Idx2 E κ, ℝ)) id h1
    have e2 := hlaw _ (ν₂ : Measure C(Idx2 E κ, ℝ)) id h2
    rw [Measure.map_id] at e1 e2
    exact Subtype.ext (e1.trans e2.symm)
  · refine tendstoInDistribution_congr_limit hν h𝕍.1 ?_
    rw [Measure.map_id, hlaw Ω' μ' 𝕍 h𝕍]

end Donsker

section Maps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The scaling function: `c_P` on the left copy, `c_Q` on the right copy. -/
def scaleFun (κ cP cQ : ℝ) : C(Idx2 E κ, ℝ) :=
  ⟨Sum.elim (fun _ => cP) (fun _ => cQ), continuous_const.sumElim continuous_const⟩

/-- `θ = (g, t, s) ↦ left(−g, t)`. -/
def tau1 (κ : ℝ) : C(Theta E κ, Idx2 E κ) :=
  ⟨fun θ => Sum.inl (ballNeg θ.1, θ.2.1),
    continuous_inl.comp ((StatFormal.Wave30v.continuous_ballNeg.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd))⟩

/-- `θ = (g, t, s) ↦ right(g, s)`. -/
def tau2 (κ : ℝ) : C(Theta E κ, Idx2 E κ) :=
  ⟨fun θ => Sum.inr (θ.1, θ.2.2), continuous_inr.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))⟩

/-- `Λ v (g, t, s) = −β v(left(−g, t)) − β v(right(g, s))`. -/
def LamMap (α κ : ℝ) (v : C(Idx2 E κ, ℝ)) : C(Theta E κ, ℝ) :=
  (-(1 / (1 - α))) • v.comp (tau1 κ) - (1 / (1 - α)) • v.comp (tau2 κ)

lemma LamMap_apply (α κ : ℝ) (v : C(Idx2 E κ, ℝ)) (θ : Theta E κ) :
    LamMap α κ v θ = -(1 / (1 - α)) * v (Sum.inl (ballNeg θ.1, θ.2.1)) - 1 / (1 - α) * v (Sum.inr (θ.1, θ.2.2)) := by
  simp [LamMap, tau1, tau2]

lemma continuous_LamMap (α κ : ℝ) : Continuous (LamMap (E := E) α κ) := by
  show Continuous fun v : C(Idx2 E κ, ℝ) => (-(1 / (1 - α))) • v.comp (tau1 κ) - (1 / (1 - α)) • v.comp (tau2 κ)
  exact ((ContinuousMap.continuous_precomp (Z := ℝ) (tau1 (E := E) κ)).const_smul (-(1 / (1 - α)) : ℝ)).sub
    ((ContinuousMap.continuous_precomp (Z := ℝ) (tau2 (E := E) κ)).const_smul (1 / (1 - α) : ℝ))

lemma scaleFun_mul_apply (κ cP cQ : ℝ) (v : C(Idx2 E κ, ℝ)) (z : Idx2 E κ) :
    ((scaleFun κ cP cQ * v : C(Idx2 E κ, ℝ)) z) = Sum.elim (fun _ => cP) (fun _ => cQ) z * v z := rfl

end Maps

section Identity
variable {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {φ : 𝒳 → E} {κ α : ℝ}

lemma isClosed_argminSet (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (μ : Measure 𝒳) [IsFiniteMeasure μ]
    (f : E) : IsClosed (argminSet φ α μ κ f) := by
  have hc : Continuous fun t : Icc (-κ) κ => cvObj φ α μ f t :=
    (continuous_cvObj hφ hκ α μ f).comp continuous_subtype_val
  have : argminSet φ α μ κ f = ⋂ t' : Icc (-κ) κ, {t : Icc (-κ) κ | cvObj φ α μ f t ≤ cvObj φ α μ f t'} := by
    ext t; simp only [mem_iInter, mem_ofPred_eq]; exact mem_argminSet_iff
  rw [this]
  exact isClosed_iInter fun t' => isClosed_le hc continuous_const

lemma argminSet_attain (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) (μ : Measure 𝒳)
    [IsFiniteMeasure μ] (f : E) (a : Icc (-κ) κ → ℝ) (ha : Continuous a) :
    ∃ t ∈ argminSet φ α μ κ f, a t = sInf (a '' argminSet φ α μ κ f) ∧
      ∀ t' ∈ argminSet φ α μ κ f, sInf (a '' argminSet φ α μ κ f) ≤ a t' := by
  have hK : IsCompact (argminSet φ α μ κ f) := (isClosed_argminSet hφ hκ μ f).isCompact
  have hKi : IsCompact (a '' argminSet φ α μ κ f) := hK.image ha
  have hne := (argminSet_nonempty hφ hκ hκ0 α μ f).image a
  obtain ⟨t, ht, he⟩ := hKi.sInf_mem hne
  exact ⟨t, ht, he, fun t' ht' => csInf_le hKi.bddBelow ⟨t', ht', rfl⟩⟩

variable [FiniteDimensional ℝ E]

lemma supFun_dualTrim (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (μ ν : Measure 𝒳) (Γ : C(Theta E κ, ℝ)) (hΓ : ∀ θ, Γ θ = dualTrim φ α μ ν θ)
    (hG : IsGreatest (range (dualTrim φ α μ ν (κ := κ))) (setDist (region φ α μ) (region φ α ν))) :
    supFun Γ = setDist (region φ α μ) (region φ α ν) := by
  have : (Γ : Theta E κ → ℝ) = dualTrim φ α μ ν := funext hΓ
  unfold supFun; rw [this]; exact hG.csSup_eq

/-- The deterministic identity: `sup_{Θ₀} Λ(S v) = sup_{g ∈ G*} {−c_P H_P(−g) − c_Q H_Q(g)}`. -/
lemma supDeriv_Lam_scale (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (Γ : C(Theta E κ, ℝ))
    (hΓ : ∀ θ, Γ θ = dualTrim φ α P Q θ) {cP cQ : ℝ} (hcP : 0 ≤ cP) (hcQ : 0 ≤ cQ) (v : C(Idx2 E κ, ℝ)) :
    supDeriv Γ (LamMap α κ (scaleFun κ cP cQ * v)) = sSup (boundaryLim φ α P Q κ cP cQ v '' Gstar φ α P Q) := by
  have hκ0 := kappa_nonneg hκ P
  have hβ : 0 < 1 / (1 - α) := by apply div_pos one_pos; linarith
  set β := 1 / (1 - α) with hβdef
  have hsup : supFun Γ = Dpop φ P Q α :=
    supFun_dualTrim hφ hκ hα0 hα1 P Q Γ hΓ (isGreatest_dualTrim hφ hκ hα0 hα1 P Q)
  have hmem : ∀ θ, θ ∈ argmaxSet Γ ↔ (θ.1 ∈ Gstar φ α P Q ∧
      θ.2.1 ∈ argminSet φ α P κ (-(θ.1 : E)) ∧ θ.2.2 ∈ argminSet φ α Q κ (θ.1 : E)) := by
    intro θ
    rw [← dualTrim_eq_Dpop_iff hφ hκ hα0 hα1 P Q θ, ← hΓ θ, ← hsup]
    rfl
  set W := LamMap α κ (scaleFun κ cP cQ * v) with hWdef
  have hW : ∀ θ : Theta E κ, W θ = -β * (cP * v (Sum.inl (ballNeg θ.1, θ.2.1))) - β * (cQ * v (Sum.inr (θ.1, θ.2.2))) := by
    intro θ; rw [hWdef, LamMap_apply]; rfl
  have haP : ∀ g : Ball E, Continuous fun t : Icc (-κ) κ => v (Sum.inl (ballNeg g, t)) := fun g =>
    v.continuous.comp (continuous_inl.comp (continuous_const.prodMk continuous_id))
  have haQ : ∀ g : Ball E, Continuous fun t : Icc (-κ) κ => v (Sum.inr (g, t)) := fun g =>
    v.continuous.comp (continuous_inr.comp (continuous_const.prodMk continuous_id))
  have hbL : ∀ g : Ball E, boundaryLim φ α P Q κ cP cQ v g =
      -cP * (β * sInf ((fun t => v (Sum.inl (ballNeg g, t))) '' argminSet φ α P κ (-(g : E)))) -
        cQ * (β * sInf ((fun t => v (Sum.inr (g, t))) '' argminSet φ α Q κ (g : E))) := fun g => rfl
  have hnormv : ∀ z, -‖v‖ ≤ v z := fun z => by
    have := StatFormal.Wave30v.apply_le_norm (-v) z
    rw [norm_neg, ContinuousMap.neg_apply] at this; linarith
  have hbdd : BddAbove (boundaryLim φ α P Q κ cP cQ v '' Gstar φ α P Q) := by
    refine ⟨cP * (β * ‖v‖) + cQ * (β * ‖v‖), ?_⟩
    rintro _ ⟨g, -, rfl⟩
    obtain ⟨t, ht, he, -⟩ := argminSet_attain hφ hκ hκ0 P (-(g : E)) _ (haP g)
    obtain ⟨s, hs, hse, -⟩ := argminSet_attain hφ hκ hκ0 Q (g : E) _ (haQ g)
    rw [hbL g, ← he, ← hse]
    have h1 := hnormv (Sum.inl (ballNeg g, t))
    have h2 := hnormv (Sum.inr (g, s))
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hcP hβ.le), mul_le_mul_of_nonneg_left h2 (mul_nonneg hcQ hβ.le)]
  have hbddW : BddAbove (W '' argmaxSet Γ) :=
    ⟨‖W‖, by rintro _ ⟨θ, -, rfl⟩; exact StatFormal.Wave30v.apply_le_norm W θ⟩
  have hGne := Gstar_nonempty hφ hκ hα0 hα1 P Q (E := E)
  unfold supDeriv
  apply le_antisymm
  · obtain ⟨g, hg⟩ := hGne
    obtain ⟨t, ht, -, -⟩ := argminSet_attain hφ hκ hκ0 P (-(g : E)) _ (haP g)
    obtain ⟨s, hs, -, -⟩ := argminSet_attain hφ hκ hκ0 Q (g : E) _ (haQ g)
    refine csSup_le ⟨_, (g, t, s), (hmem _).2 ⟨hg, ht, hs⟩, rfl⟩ ?_
    rintro _ ⟨θ, hθ, rfl⟩
    obtain ⟨hg', ht', hs'⟩ := (hmem θ).1 hθ
    refine le_trans ?_ (le_csSup hbdd ⟨θ.1, hg', rfl⟩)
    obtain ⟨t0, -, -, hle⟩ := argminSet_attain hφ hκ hκ0 P (-(θ.1 : E)) _ (haP θ.1)
    obtain ⟨s0, -, -, hle'⟩ := argminSet_attain hφ hκ hκ0 Q (θ.1 : E) _ (haQ θ.1)
    have e1 := hle _ ht'
    have e2 := hle' _ hs'
    rw [hW θ, hbL θ.1]
    nlinarith [mul_le_mul_of_nonneg_left e1 (mul_nonneg hcP hβ.le), mul_le_mul_of_nonneg_left e2 (mul_nonneg hcQ hβ.le)]
  · refine csSup_le (hGne.image _) ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨t, ht, he, -⟩ := argminSet_attain hφ hκ hκ0 P (-(g : E)) _ (haP g)
    obtain ⟨s, hs, hse, -⟩ := argminSet_attain hφ hκ hκ0 Q (g : E) _ (haQ g)
    refine le_trans (le_of_eq ?_) (le_csSup hbddW ⟨(g, t, s), (hmem _).2 ⟨hg, ht, hs⟩, rfl⟩)
    rw [hW, hbL g, ← he, ← hse]
    ring

end Identity

section Every

lemma gpVar_scale {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : 𝒳 → E) (P Q : Measure 𝒳) (cP cQ κ : ℝ) {p : ℕ} (z : Fin p → Idx2 E κ) (u : Fin p → ℝ) :
    gpVar φ P Q 1 1 z (fun i => u i * Sum.elim (fun _ => cP) (fun _ => cQ) (z i)) = gpVar φ P Q cP cQ z u := by
  unfold gpVar
  have hP : (fun w => ∑ i, u i * Sum.elim (fun _ => cP) (fun _ => cQ) (z i) * hingeP φ (z i) w) =
      fun w => cP * ∑ i, u i * hingeP φ (z i) w := by
    funext w; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases z i with y | y <;> simp [hingeP] <;> ring
  have hQ : (fun w => ∑ i, u i * Sum.elim (fun _ => cP) (fun _ => cQ) (z i) * hingeQ φ (z i) w) =
      fun w => cQ * ∑ i, u i * hingeQ φ (z i) w := by
    funext w; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases z i with y | y <;> simp [hingeQ] <;> ring
  rw [hP, hQ, variance_const_mul, variance_const_mul]
  ring

/-- The scaled process `S 𝔾` is the limit process with scales `c_P, c_Q`. -/
lemma isLimitGP_scale {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {φ : 𝒳 → E} {P Q : Measure 𝒳} {cP cQ κ : ℝ} {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {𝔾 : Ω' → C(Idx2 E κ, ℝ)} (h : IsLimitGP φ P Q 1 1 κ μ' 𝔾) :
    IsLimitGP φ P Q cP cQ κ μ' (fun ω => scaleFun κ cP cQ * 𝔾 ω) := by
  refine ⟨(continuous_const.mul continuous_id : Continuous fun v : C(Idx2 E κ, ℝ) => scaleFun κ cP cQ * v).measurable.comp_aemeasurable h.1, fun p z u => ?_⟩
  have e : (fun ω => ∑ i, u i * (scaleFun κ cP cQ * 𝔾 ω : C(Idx2 E κ, ℝ)) (z i)) =
      fun ω => ∑ i, (u i * Sum.elim (fun _ => cP) (fun _ => cQ) (z i)) * 𝔾 ω (z i) := by
    funext ω; refine Finset.sum_congr rfl fun i _ => ?_
    rw [scaleFun_mul_apply]; ring
  rw [e, h.2 p z _, gpVar_scale]

theorem boundary_every : Claims.boundary_every := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ Ω _ μ _ ξ η n m r cP cQ Ω' _ μ' _ 𝔾 hφ hκ hα0 hα1 hS hSc h𝔾
  have hS' := hS
  have hSc' := hSc
  obtain ⟨hξ, hη, hiξ, hiη, hlξ, hlη, hind⟩ := hS
  obtain ⟨hn1, hm1, hn, hm, hr, hrt, hrn, hrm⟩ := hSc
  have hκ0 := kappa_nonneg hκ P
  refine ⟨Gstar_nonempty hφ hκ hα0 hα1 P Q, fun hD a ha b hb hab g =>
    Gstar_eq_singleton hφ hκ hα0 hα1 P Q hD ha hb hab g, ?_⟩
  have hcP : 0 ≤ cP := ge_of_tendsto' hrn fun k => div_nonneg (hr k).le (Real.sqrt_nonneg _)
  have hcQ : 0 ≤ cQ := ge_of_tendsto' hrm fun k => div_nonneg (hr k).le (Real.sqrt_nonneg _)
  -- the empirical process as a random continuous function
  let V : ℕ → Ω → C(Idx2 E κ, ℝ) := fun k ω =>
    ⟨tsProc (hingeP φ) (hingeQ φ) P Q (n k) (m k) (r k) (fun i => ξ i ω) (fun j => η j ω),
      continuous_tsProc (isLipClass_hingeP hφ hκ) (isLipClass_hingeQ hφ hκ) (by linarith) P Q _ _ _ _ _⟩
  obtain ⟨-, -, hconv⟩ := boundary_donsker 𝒳 E φ κ P Q Ω μ ξ η n m r cP cQ V hφ hκ hS' hSc' (fun k ω z => rfl)
  have hV := hconv Ω' μ' _ (isLimitGP_scale (cP := cP) (cQ := cQ) h𝔾)
  -- the dual objectives
  have hfin : ∀ k (ω : Ω), IsProbabilityMeasure (empirical fun i : Fin (n k) => ξ i ω) ∧
      IsProbabilityMeasure (empirical fun j : Fin (m k) => η j ω) := fun k ω =>
    ⟨isProbabilityMeasure_empirical _ (hn1 k), isProbabilityMeasure_empirical _ (hm1 k)⟩
  let Γ : C(Theta E κ, ℝ) := ⟨dualTrim φ α P Q, continuous_dualTrim hφ hκ α P Q⟩
  let Γk : ℕ → Ω → C(Theta E κ, ℝ) := fun k ω =>
    ⟨dualTrim φ α (empirical fun i : Fin (n k) => ξ i ω) (empirical fun j : Fin (m k) => η j ω),
      @continuous_dualTrim _ _ _ _ _ φ hφ κ hκ α _ _ (by have := (hfin k ω).1; infer_instance) (by have := (hfin k ω).2; infer_instance)⟩
  have hkey : ∀ k ω, LamMap α κ (V k ω) = r k • (Γk k ω - Γ) := by
    intro k ω
    ext θ
    have hg1 : ‖(θ.1 : E)‖ ≤ 1 := mem_closedBall_zero_iff.1 θ.1.2
    have hg1' : ‖-(θ.1 : E)‖ ≤ 1 := by rw [norm_neg]; exact hg1
    have ht : |(θ.2.1 : ℝ)| ≤ κ := abs_le.2 ⟨θ.2.1.2.1, θ.2.1.2.2⟩
    have hs : |(θ.2.2 : ℝ)| ≤ κ := abs_le.2 ⟨θ.2.2.2.1, θ.2.2.2.2⟩
    have e1 := integral_empirical (fun i : Fin (n k) => ξ i ω) (measurable_hinge hφ (-(θ.1 : E)) θ.2.1)
      (abs_hinge_le hκ hg1' ht)
    have e2 := integral_empirical (fun j : Fin (m k) => η j ω) (measurable_hinge hφ (θ.1 : E) θ.2.2)
      (abs_hinge_le hκ hg1 hs)
    rw [Fin.sum_univ_eq_sum_range (fun i => hinge φ (-(θ.1 : E)) θ.2.1 (ξ i ω))] at e1
    rw [Fin.sum_univ_eq_sum_range (fun j => hinge φ (θ.1 : E) θ.2.2 (η j ω))] at e2
    rw [LamMap_apply]
    simp only [V, Γk, Γ, ContinuousMap.coe_mk, ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul,
      tsProc, hingeP, hingeQ, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, zero_div, integral_zero,
      sub_zero, mul_zero, add_zero, zero_add, dualTrim, e1, e2]
    have : (ballNeg θ.1 : E) = -(θ.1 : E) := rfl
    rw [this]
    ring
  have hW : TendstoInDistribution (fun k ω => r k • (Γk k ω - Γ)) atTop
      (fun ω' => LamMap α κ (scaleFun κ cP cQ * 𝔾 ω')) (fun _ => μ) μ' := by
    have := hV.continuous_comp (continuous_LamMap (E := E) α κ)
    simp only [Function.comp_def, hkey] at this
    exact this
  have : Nonempty (Theta E κ) :=
    ⟨(⟨0, mem_closedBall_self zero_le_one⟩, ⟨-κ, by constructor <;> linarith⟩, ⟨-κ, by constructor <;> linarith⟩)⟩
  have h := StatFormal.Wave30v.boundary_sup_limit (Theta E κ) Ω Ω' μ μ' Γ Γk _ r hr hrt hW
  have hdual := boundary_dual 𝒳 E φ κ α hφ hκ hα0 hα1
  have e1 : (fun k ω => r k * (supFun (Γk k ω) - supFun Γ)) = fun k ω =>
      r k * (Demp φ (fun i : Fin (n k) => ξ i ω) (fun j : Fin (m k) => η j ω) α - Dpop φ P Q α) := by
    funext k ω
    rw [supFun_dualTrim hφ hκ hα0 hα1 _ _ (Γk k ω) (fun θ => rfl) (hdual.2 _ _ _ _ (hn1 k) (hm1 k)),
      supFun_dualTrim hφ hκ hα0 hα1 P Q Γ (fun θ => rfl) (hdual.1 P Q)]
    rfl
  have e2 : (fun ω' => supDeriv Γ (LamMap α κ (scaleFun κ cP cQ * 𝔾 ω'))) =
      fun ω' => sSup (boundaryLim φ α P Q κ cP cQ (𝔾 ω') '' Gstar φ α P Q) := by
    funext ω'
    exact supDeriv_Lam_scale hφ hκ hα0 hα1 P Q Γ (fun θ => rfl) hcP hcQ (𝔾 ω')
  rw [e1, e2] at h
  exact h

end Every

section Contact

theorem boundary_contact : Claims.boundary_contact := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ Ω _ μ _ ξ η n m r cP cQ Ω' _ μ' _ 𝔾 hφ hκ hα0 hα1 hS hSc h𝔾 hAB
  obtain ⟨z, hzA, hzB⟩ := hAB
  have hD : Dpop φ P Q α = 0 := by
    refine le_antisymm ?_ (StatFormal.Wave30v.le_setDist ⟨z, hzA⟩ ⟨z, hzB⟩ fun a _ b _ => norm_nonneg _)
    have := StatFormal.Wave30v.setDist_le' hzA hzB
    rwa [sub_self, norm_zero] at this
  obtain ⟨-, -, h3⟩ := boundary_every 𝒳 E φ κ α P Q Ω μ ξ η n m r cP cQ Ω' μ' 𝔾 hφ hκ hα0 hα1 hS hSc h𝔾
  have hpol : ∀ g : Ball E, g ∈ Gstar φ α P Q ↔
      (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))) := by
    intro g
    rw [StatFormal.Wave30v.polarSet_closure_coneHull]
    exact Gstar_iff_polar hφ hκ hα0 hα1 P Q ⟨z, hzA, hzB⟩ g
  refine ⟨fun w hw => ?_, hpol, ?_⟩
  · exact (StatFormal.Wave30v.boundary_tangent_cone E (region φ α P) (region φ α Q) w
      (convex_region P hφ hκ) (convex_region Q hφ hκ) hw.1 hw.2).symm
  · have hset : Gstar φ α P Q = {g : Ball E | (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P)))} :=
      Set.ext hpol
    rw [hset, hD] at h3
    simpa only [sub_zero] using h3

theorem boundary_linear : Claims.boundary_linear := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ Ω _ μ _ ξ η n m r cP cQ Ω' _ μ' _ 𝔾 GP GQ hφ hκ hα0 hα1 hS hSc h𝔾 hAB hlin
  obtain ⟨-, -, hc⟩ := boundary_contact 𝒳 E φ κ α P Q Ω μ ξ η n m r cP cQ Ω' μ' 𝔾 hφ hκ hα0 hα1 hS hSc h𝔾 hAB
  set K := closure (coneHull (region φ α Q - region φ α P)) with hKdef
  have hAne := region_nonempty P hα0 hα1 (φ := φ)
  have hBne := region_nonempty Q hα0 hα1 (φ := φ)
  have hKne : K.Nonempty := by
    obtain ⟨a, ha⟩ := hAne; obtain ⟨b, hb⟩ := hBne
    exact ⟨0, subset_closure ⟨0, le_rfl, b - a, Set.sub_mem_sub hb ha, by simp⟩⟩
  have hKcl : IsClosed K := isClosed_closure
  have hKcv : Convex ℝ K :=
    (StatFormal.Wave30v.convex_coneHull ((convex_region Q hφ hκ).sub (convex_region P hφ hκ))).closure
  have hKcone := StatFormal.Wave30v.cone_closure_coneHull (region φ α Q - region φ α P)
  have hmoreau := fun x => metricProj_polar_norm E K hKne hKcl hKcv hKcone x
  refine ⟨?_, hmoreau⟩
  have hae : (fun ω' => sSup (boundaryLim φ α P Q κ cP cQ (𝔾 ω') '' {g : Ball E | (g : E) ∈ polarSet K})) =ᵐ[μ']
      fun ω' => ‖metricProj (polarSet K) (cP • GP ω' - cQ • GQ ω')‖ := by
    filter_upwards [hlin] with ω' hω'
    set x := cP • GP ω' - cQ • GQ ω'
    have himg : boundaryLim φ α P Q κ cP cQ (𝔾 ω') '' {g : Ball E | (g : E) ∈ polarSet K} =
        (fun g : E => ⟪g, x⟫) '' (polarSet K ∩ closedBall 0 1) := by
      ext y
      constructor
      · rintro ⟨g, hg, rfl⟩
        refine ⟨g, ⟨hg, g.2⟩, ?_⟩
        obtain ⟨h1, h2⟩ := hω' g hg
        simp only [boundaryLim, h1, h2, x, inner_sub_right, inner_smul_right, inner_neg_left]
        ring
      · rintro ⟨g, ⟨hg, hb⟩, rfl⟩
        refine ⟨⟨g, hb⟩, hg, ?_⟩
        obtain ⟨h1, h2⟩ := hω' ⟨g, hb⟩ hg
        simp only [boundaryLim, h1, h2, x, inner_sub_right, inner_smul_right, inner_neg_left]
        ring
    rw [himg, StatFormal.Wave30v.boundary_polar_infDist E K hKne hKcl hKcv hKcone x, hmoreau x]
  exact tendstoInDistribution_congr_limit hc (hc.aemeasurable_limit.congr hae) (Measure.map_congr hae)

end Contact

end StatFormal.Wave30z
