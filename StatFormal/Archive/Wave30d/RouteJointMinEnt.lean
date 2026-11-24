import StatFormal.Archive.Wave30d.Statements
import StatFormal.Lib.GibbsUnbounded.Basic
import StatFormal.Archive.Wave28e.RouteJointMin

/-!
# Route (wave 30d) — paper 2 `prop:jointmin`: entropic sets (`ε > 0`) on an unbounded `K = E` (untrusted)

* `jointmin_ent_group`: for `Q` in the entropic set, a near-optimal coupling `γ` (finite cost and KL), the anchor-wise
  Gibbs bound with an UNBOUNDED exponent `Foundations/GibbsUnbounded.coupling_gibbs` (truncation of `f`, anchor-wise
  normalisation, monotone convergence), the budget `E_γ c + ε KL ≤ r + δ`, and Tau Ceti's
  `W₂²(h#P̂, h#Q) ≤ ∫ (h(x') − h(x))² dγ`; `δ ↓ 0`.
* `jointmin_ent_cert`: the `W₂` triangle inequality on `ℝ` (as in the frozen Wave 28e route `cert_aniso`).
* `jointmin_ent_upper`, `jointmin_ent_inf`: the certified `lem:delta-inf` through the Wave 28e route `delta_plan`,
  `delta_attained`; finiteness at `λ_s = ‖(G_s⁻¹)ᵀ w‖² + 1`, where the exponent is `≤ 0` (Wave 28e `inner_sq_le`), so
  `T_s ≤ λ_s r_s`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti InformationTheory
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave30d

open StatFormal.RobustEquality.Paper2.Seminorm StatFormal.Wave20a
open StatFormal.RobustEquality.Paper2.Alternating (centre)
open StatFormal.Foundations.GibbsUnbounded

/-- From `A ≤ T + δ` for every `δ > 0` to `A ≤ T` (`A ∈ [0, ∞]`, `T ∈ EReal`). -/
lemma ereal_le_of_forall_add {A : ℝ≥0∞} {T : EReal} (h : ∀ δ : ℝ, 0 < δ → (A : EReal) ≤ T + (δ : EReal)) :
    (A : EReal) ≤ T := by
  induction T using EReal.rec with
  | bot =>
      have h1 := h 1 one_pos
      rw [EReal.bot_add, le_bot_iff] at h1
      exact absurd h1 (EReal.coe_ennreal_ne_bot A)
  | top => exact le_top
  | coe t =>
      have hA : A ≠ ⊤ := by
        intro hA
        have h1 := h 1 one_pos
        rw [hA, EReal.coe_ennreal_top, ← EReal.coe_add, top_le_iff] at h1
        exact EReal.coe_ne_top _ h1
      rw [← EReal.coe_ennreal_toReal hA] at h ⊢
      rw [EReal.coe_le_coe_iff]
      by_contra hc
      push_neg at hc
      have h2 := h ((A.toReal - t) / 2) (by linarith)
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h2
      linarith

lemma measurable_inner_left' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (w : E) : Measurable fun z : E => ⟪w, z⟫ :=
  (continuous_const.inner continuous_id).measurable

lemma edist_inner_sq' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (w a b : E) :
    edist ⟪w, a⟫ ⟪w, b⟫ ^ (2 : ℝ) = ENNReal.ofReal (⟪w, b - a⟫ ^ 2) := by
  rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two,
    sq_abs, inner_sub_right]
  congr 1; ring

lemma inner_sq_le' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (G : E ≃L[ℝ] E)
    (w u : E) {l : ℝ} (hv : ‖ContinuousLinearMap.adjoint (G.symm : E →L[ℝ] E) w‖ ^ 2 ≤ l) :
    ⟪w, u⟫ ^ 2 ≤ l * ‖G u‖ ^ 2 := by
  rw [StatFormal.RobustEquality.Paper2.Route.inner_eq_adj G w u]
  set v := ContinuousLinearMap.adjoint (G.symm : E →L[ℝ] E) w
  have h := abs_real_inner_le_norm v (G u)
  have h2 : (inner ℝ v (G u)) ^ 2 ≤ (‖v‖ * ‖G u‖) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith [sq_nonneg ‖G u‖]

section Group

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E]
  [BorelSpace E]

lemma isProb_of_coupling {n : ℕ} {a : Fin n → ℝ} (ha : ProbW a) (x : Fin n → E) {Q : Measure E}
    {γ : Measure (E × E)} (hγ : IsCoupling γ (centre a x) Q) : IsProbabilityMeasure γ := by
  constructor
  have h := congrArg (fun μ : Measure E => μ Set.univ) hγ.fst_eq
  simp only [Measure.fst, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at h
  rw [h]
  exact centre_univ' ha.1 ha.2 x

theorem jointmin_ent_group : Claims.jointmin_ent_group := by
  intro E _ _ _ _ _ n G ε r ν _ a x w l Q ha hε hr hl hQ
  obtain ⟨hQp, hinf⟩ := hQ
  have hh := measurable_inner_left' (E := E) w
  set τ := l * ε with hτ_def
  have hτ : 0 < τ := mul_pos hl hε
  set f : E × E → ℝ := fun z => ⟪w, z.2 - z.1⟫ ^ 2 with hf_def
  set c : E × E → ℝ := fun z => ‖G (z.2 - z.1)‖ ^ 2 with hc_def
  have hfm : Measurable f := (by fun_prop : Continuous f).measurable
  have hcm : Measurable c := by
    have : Continuous c := (continuous_norm.comp (G.continuous.comp (continuous_snd.sub continuous_fst))).pow 2
    exact this.measurable
  refine ereal_le_of_forall_add fun δ hδ => ?_
  set d : ℝ := δ / l with hd
  have hd0 : 0 < d := div_pos hδ hl
  -- a near-optimal coupling
  have hlt : (⨅ (γ : Measure (E × E)) (_ : IsCoupling γ (centre a x) Q),
      (∫⁻ z, ENNReal.ofReal (‖G (z.2 - z.1)‖ ^ 2) ∂γ + ENNReal.ofReal ε * klDiv γ ((centre a x).prod ν))) <
      ENNReal.ofReal (r + d) :=
    lt_of_le_of_lt hinf (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by linarith, by linarith⟩)
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hcpl, hval⟩ := iInf_lt_iff.1 hγ
  have : IsProbabilityMeasure γ := isProb_of_coupling ha x hcpl
  have hC : ∫⁻ z, ENNReal.ofReal (c z) ∂γ ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_top_of_lt hval) le_self_add
  have hεK : ENNReal.ofReal ε * klDiv γ ((centre a x).prod ν) ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_top_of_lt hval) le_add_self
  have hK : klDiv γ ((centre a x).prod ν) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simp [hε])] at hεK
    exact hεK rfl
  have hfst : γ.map Prod.fst = centre a x := hcpl.fst_eq
  have hG := coupling_gibbs ha.1 ha.2 x ν hfm hcm (fun z => sq_nonneg _) (fun z => sq_nonneg _) hl hτ γ hfst hC hK
  -- the budget in real form
  set Cr := (∫⁻ z, ENNReal.ofReal (c z) ∂γ).toReal
  set Kr := (klDiv γ ((centre a x).prod ν)).toReal
  have hbud : Cr + ε * Kr ≤ r + d := by
    have h1 : ∫⁻ z, ENNReal.ofReal (c z) ∂γ + ENNReal.ofReal ε * klDiv γ ((centre a x).prod ν) =
        ENNReal.ofReal (Cr + ε * Kr) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (mul_nonneg hε.le ENNReal.toReal_nonneg),
        ENNReal.ofReal_mul hε.le, ENNReal.ofReal_toReal hC, ENNReal.ofReal_toReal hK]
    rw [h1] at hval
    exact ((ENNReal.ofReal_lt_ofReal_iff'.1 hval).1).le
  -- `W₂² ≤ ∫ f dγ`
  have hπ : IsCoupling (γ.map (Prod.map (fun z : E => ⟪w, z⟫) fun z : E => ⟪w, z⟫))
      ((centre a x).map fun z => ⟪w, z⟫) (Q.map fun z => ⟪w, z⟫) := by
    constructor
    · rw [Measure.fst, Measure.map_map measurable_fst (hh.prodMap hh), ← hcpl.fst_eq, Measure.fst,
        Measure.map_map hh measurable_fst]
      rfl
    · rw [Measure.snd, Measure.map_map measurable_snd (hh.prodMap hh), ← hcpl.snd_eq, Measure.snd,
        Measure.map_map hh measurable_snd]
      rfl
  have hdR : Measurable fun z : ℝ × ℝ => edist z.1 z.2 := measurable_edist
  have hW := wassersteinEDist_rpow_le_lintegral hdR (p := 2) two_ne_zero ENNReal.ofNat_ne_top hπ
  rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num, lintegral_map (hdR.pow_const _) (hh.prodMap hh)] at hW
  have hW2 : wassersteinEDist 2 ((centre a x).map fun z => ⟪w, z⟫) (Q.map fun z => ⟪w, z⟫) ^ 2 ≤
      ∫⁻ z, ENNReal.ofReal (f z) ∂γ := by
    rw [← ENNReal.rpow_natCast, show ((2 : ℕ) : ℝ) = 2 by norm_num]
    refine hW.trans (le_of_eq (lintegral_congr fun z => ?_))
    simp only [Prod.map_fst, Prod.map_snd, hf_def]
    exact edist_inner_sq' w z.1 z.2
  -- assemble
  have hT : Tent G ε ν a x r w l = ((l * r : ℝ) : EReal) + ((τ : ℝ) : EReal) * ∑ i, ((a i : ℝ) : EReal) *
      ENNReal.log (∫⁻ y, ENNReal.ofReal (Real.exp ((f (x i, y) - l * c (x i, y)) / τ)) ∂ν) := rfl
  calc ((wassersteinEDist 2 ((centre a x).map fun z => ⟪w, z⟫) (Q.map fun z => ⟪w, z⟫) ^ 2 : ℝ≥0∞) : EReal)
      ≤ ((∫⁻ z, ENNReal.ofReal (f z) ∂γ : ℝ≥0∞) : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.2 hW2
    _ ≤ ((l * Cr + τ * Kr : ℝ) : EReal) + (τ : EReal) * ∑ i, ((a i : ℝ) : EReal) *
          ENNReal.log (∫⁻ y, ENNReal.ofReal (Real.exp ((f (x i, y) - l * c (x i, y)) / τ)) ∂ν) := hG
    _ ≤ ((l * r + δ : ℝ) : EReal) + (τ : EReal) * ∑ i, ((a i : ℝ) : EReal) *
          ENNReal.log (∫⁻ y, ENNReal.ofReal (Real.exp ((f (x i, y) - l * c (x i, y)) / τ)) ∂ν) := by
        refine add_le_add (EReal.coe_le_coe_iff.2 ?_) le_rfl
        have : l * (Cr + ε * Kr) ≤ l * (r + d) := mul_le_mul_of_nonneg_left hbud hl.le
        have e : l * (r + d) = l * r + δ := by rw [hd, mul_add, mul_div_cancel₀ _ hl.ne']
        rw [hτ_def]; nlinarith
    _ = Tent G ε ν a x r w l + (δ : EReal) := by
        rw [hT, EReal.coe_add, add_assoc, add_comm (δ : EReal), ← add_assoc]

lemma wass_le_sqrtE {n : ℕ} (G : E ≃L[ℝ] E) {ε r : ℝ} (ν : Measure E) [IsProbabilityMeasure ν] {a : Fin n → ℝ}
    (ha : ProbW a) (x : Fin n → E) (w : E) {l : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) (hl : 0 < l) {Q : Measure E}
    (hQ : Q ∈ entBall G ε ν a x r) :
    wassersteinEDist 2 ((centre a x).map fun z => ⟪w, z⟫) (Q.map fun z => ⟪w, z⟫) ≤
      sqrtE (Tent G ε ν a x r w l) := by
  have h := jointmin_ent_group E n G ε r ν a x w l Q ha hε hr hl hQ
  have h2 := EReal.toENNReal_le_toENNReal h
  rw [EReal.toENNReal_coe] at h2
  have h3 := ENNReal.rpow_le_rpow h2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num,
    ENNReal.rpow_one] at h3
  exact h3

theorem jointmin_ent_cert : Claims.jointmin_ent_cert := by
  intro E _ _ _ _ _ n₀ n₁ G₀ G₁ ε r₀ r₁ ν₀ ν₁ _ _ a₀ x₀ a₁ x₁ w l₀ l₁ Q₀ Q₁ h₀ h₁ hε hr₀ hr₁ hl₀ hl₁ hQ₀ hQ₁
  have hd : Measurable fun z : ℝ × ℝ => edist z.1 z.2 := measurable_edist
  have hh := measurable_inner_left' (E := E) w
  have : IsProbabilityMeasure (centre a₀ x₀) := centre_isProb' h₀.1 h₀.2 x₀
  have : IsProbabilityMeasure (centre a₁ x₁) := centre_isProb' h₁.1 h₁.2 x₁
  have : IsProbabilityMeasure ((centre a₀ x₀).map fun z => ⟪w, z⟫) :=
    (Measure.isProbabilityMeasure_map_iff hh.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure ((centre a₁ x₁).map fun z => ⟪w, z⟫) :=
    (Measure.isProbabilityMeasure_map_iff hh.aemeasurable).2 inferInstance
  have t1 := wassersteinEDist_triangle hd (p := 2) (by norm_num) (Q₀.map fun z => ⟪w, z⟫)
    ((centre a₀ x₀).map fun z => ⟪w, z⟫) (Q₁.map fun z => ⟪w, z⟫)
  have t2 := wassersteinEDist_triangle hd (p := 2) (by norm_num) ((centre a₀ x₀).map fun z => ⟪w, z⟫)
    ((centre a₁ x₁).map fun z => ⟪w, z⟫) (Q₁.map fun z => ⟪w, z⟫)
  have c0 := wass_le_sqrtE G₀ ν₀ h₀ x₀ w hε hr₀ hl₀ hQ₀
  have c1 := wass_le_sqrtE G₁ ν₁ h₁ x₁ w hε hr₁ hl₁ hQ₁
  rw [wassersteinEDist_comm hd] at c0
  calc wassersteinEDist 2 (Q₀.map fun z => ⟪w, z⟫) (Q₁.map fun z => ⟪w, z⟫)
      ≤ wassersteinEDist 2 (Q₀.map fun z => ⟪w, z⟫) ((centre a₀ x₀).map fun z => ⟪w, z⟫) +
          (wassersteinEDist 2 ((centre a₀ x₀).map fun z => ⟪w, z⟫) ((centre a₁ x₁).map fun z => ⟪w, z⟫) +
            wassersteinEDist 2 ((centre a₁ x₁).map fun z => ⟪w, z⟫) (Q₁.map fun z => ⟪w, z⟫)) :=
        t1.trans (add_le_add le_rfl t2)
    _ ≤ sqrtE (Tent G₀ ε ν₀ a₀ x₀ r₀ w l₀) +
          (wassersteinEDist 2 ((centre a₀ x₀).map fun z => ⟪w, z⟫) ((centre a₁ x₁).map fun z => ⟪w, z⟫) +
            sqrtE (Tent G₁ ε ν₁ a₁ x₁ r₁ w l₁)) := by gcongr
    _ = _ := by ring

end Group

theorem jointmin_ent_upper : Claims.jointmin_ent_upper := by
  intro E _ _ _ _ _ _ n₀ n₁ G₀ G₁ ε r₀ r₁ ν₀ ν₁ _ _ a₀ x₀ a₁ x₁ w Rh η l₀ l₁ γ h₀ h₁ hε hr₀ hr₁ hRh hη hl₀ hl₁ hγ
  obtain ⟨γs, hγs, hW, -, hle⟩ := StatFormal.Wave28e.delta_plan h₀ h₁ x₀ x₁ w
  unfold jointObjEnt
  gcongr
  refine iSup₂_le fun Q₀ hQ₀ => iSup₂_le fun Q₁ hQ₁ => ?_
  have h := jointmin_ent_cert E n₀ n₁ G₀ G₁ ε r₀ r₁ ν₀ ν₁ a₀ x₀ a₁ x₁ w l₀ l₁ Q₀ Q₁ h₀ h₁ hε hr₀ hr₁ hl₀ hl₁ hQ₀ hQ₁
  rw [hW] at h
  have h' := h.trans (add_le_add_three (ENNReal.ofReal_le_ofReal (hle γ hγ)) le_rfl le_rfl)
  exact pow_le_pow_left₀ zero_le h' 2

section Finite

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]

/-- At `λ ≥ ‖(G⁻¹)ᵀ w‖²` the exponent is `≤ 0`, so `T(w, λ) ≤ λ r < ⊤`. -/
lemma Tent_ne_top (G : E ≃L[ℝ] E) {ε : ℝ} (hε : 0 < ε) (ν : Measure E) [IsProbabilityMeasure ν] {n : ℕ}
    {a : Fin n → ℝ} (ha : ProbW a) (x : Fin n → E) (r : ℝ) (w : E) {l : ℝ} (hl : 0 < l)
    (hv : ‖ContinuousLinearMap.adjoint (G.symm : E →L[ℝ] E) w‖ ^ 2 ≤ l) :
    Tent G ε ν a x r w l ≠ ⊤ := by
  have hlog : ∀ i, ENNReal.log (∫⁻ z, ENNReal.ofReal (Real.exp ((⟪w, z - x i⟫ ^ 2 - l * ‖G (z - x i)‖ ^ 2) /
      (l * ε))) ∂ν) ≤ 0 := fun i => by
    rw [ENNReal.log_le_zero_iff]
    calc ∫⁻ z, ENNReal.ofReal (Real.exp ((⟪w, z - x i⟫ ^ 2 - l * ‖G (z - x i)‖ ^ 2) / (l * ε))) ∂ν
        ≤ ∫⁻ _z, 1 ∂ν := lintegral_mono fun z => by
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg ?_
            (mul_pos hl hε).le))
          linarith [inner_sq_le' G w (z - x i) hv]
      _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
  have hsum : ∑ i, ((a i : ℝ) : EReal) * ENNReal.log (∫⁻ z, ENNReal.ofReal (Real.exp
      ((⟪w, z - x i⟫ ^ 2 - l * ‖G (z - x i)‖ ^ 2) / (l * ε))) ∂ν) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    calc ((a i : ℝ) : EReal) * _ ≤ ((a i : ℝ) : EReal) * 0 :=
          mul_le_mul_of_nonneg_left (hlog i) (EReal.coe_nonneg.2 (ha.1 i))
      _ = 0 := mul_zero _
  have hle : Tent G ε ν a x r w l ≤ ((l * r : ℝ) : EReal) := by
    unfold Tent
    calc ((l * r : ℝ) : EReal) + ((l * ε : ℝ) : EReal) * _ ≤ ((l * r : ℝ) : EReal) + ((l * ε : ℝ) : EReal) * 0 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (EReal.coe_nonneg.2 (mul_pos hl hε).le))
      _ = _ := by rw [mul_zero, add_zero]
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hle

lemma sqrtE_ne_top {t : EReal} (ht : t ≠ ⊤) : sqrtE t ≠ ⊤ := by
  unfold sqrtE
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (EReal.toENNReal_ne_top_iff.2 ht)

end Finite

theorem jointmin_ent_inf : Claims.jointmin_ent_inf := by
  intro E _ _ _ _ n₀ n₁ G₀ G₁ ε r₀ r₁ ν₀ ν₁ _ _ a₀ x₀ a₁ x₁ w Rh η h₀ h₁ hε hη
  obtain ⟨γs, hγs, heq, hle⟩ := StatFormal.Wave28e.delta_attained h₀ h₁ x₀ x₁ w
  refine ⟨iInf_congr fun l₀ => iInf_congr fun l₁ => ?_, ?_⟩
  · refine le_antisymm ?_ (le_iInf fun γ => ?_)
    · refine iInf_le_of_le ⟨γs, hγs⟩ (le_of_eq ?_)
      unfold jointObjEnt penObjEnt
      rw [heq]
    · unfold jointObjEnt penObjEnt
      gcongr
      exact hle γ γ.2
  · set L₀ : ℝ := ‖ContinuousLinearMap.adjoint (G₀.symm : E →L[ℝ] E) w‖ ^ 2 + 1
    set L₁ : ℝ := ‖ContinuousLinearMap.adjoint (G₁.symm : E →L[ℝ] E) w‖ ^ 2 + 1
    have hL₀ : 0 < L₀ := by positivity
    have hL₁ : 0 < L₁ := by positivity
    refine lt_of_le_of_lt (iInf_le_of_le ⟨L₀, hL₀⟩ (iInf_le _ ⟨L₁, hL₁⟩)) ?_
    have s0 := sqrtE_ne_top (Tent_ne_top G₀ hε ν₀ h₀ x₀ r₀ w hL₀ (by linarith))
    have s1 := sqrtE_ne_top (Tent_ne_top G₁ hε ν₁ h₁ x₁ r₁ w hL₁ (by linarith))
    unfold penObjEnt
    refine ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_⟩
    refine ENNReal.pow_lt_top ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, s0.lt_top⟩, s1.lt_top⟩

end StatFormal.Wave30d
