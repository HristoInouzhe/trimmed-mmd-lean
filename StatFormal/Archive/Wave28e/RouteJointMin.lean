import StatFormal.Archive.Wave28e.Statements
import StatFormal.Archive.Wave20a.RouteStructured
import StatFormal.Archive.RobustEquality.Paper2.Alternating.Proofs

/-!
# Route (wave 28e) — paper 2 `prop:jointmin`: anisotropic and structured sets on the whole space (untrusted)

* `T⁰_s(w, λ) = λβ + (0 if ‖(G⁻¹)ᵀw‖² ≤ λ else ⊤)` (the certified `Paper2.Seminorm` route: `T0_eq`, `sup_quad`).
* Groupwise certificate for the linear rule: for `Q` in the anisotropic set and `λ ≥ ‖(G⁻¹)ᵀw‖²`,
  `⟪w, x' − x⟫² ≤ λ‖G(x' − x)‖²` pointwise, so a near-optimal coupling gives `W₂²(h#P̂, h#Q) ≤ λβ`.
* `W₂` triangle inequality on `ℝ` and the certified `lem:delta-inf` (`delta_inf_W2`): `Δ ≤ |M_γ^{1/2} w|`.
* Infima: the certified Wave 20a route (`iInf_sqrtT0`, `structured_value`, `structured_cells`, `deltafin_affine`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave28e

open StatFormal.RobustEquality.Paper2.Seminorm StatFormal.Wave20a

section Group

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma T0_cases (G : E ≃L[ℝ] E) (β : ℝ) {n : ℕ} {a : Fin n → ℝ} (ha : ProbW a) (x : Fin n → E) (w : E)
    {l : ℝ} (hl : 0 < l) :
    T0 G β a x w l = ((l * β : ℝ) : EReal) +
      if ‖ContinuousLinearMap.adjoint (G.symm : E →L[ℝ] E) w‖ ^ 2 ≤ l then 0 else ⊤ := by
  rw [T0_eq G β ha.1 ha.2 x w hl]
  unfold StatFormal.RobustEquality.Paper2.Route.T0full
  rw [StatFormal.RobustEquality.Paper2.Route.sup_quad G w hl]

lemma sqrtE_T0_le (G : E ≃L[ℝ] E) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {a : Fin n → ℝ} (ha : ProbW a)
    (x : Fin n → E) (w : E) {l : ℝ} (hl : 0 < l)
    (hv : ‖ContinuousLinearMap.adjoint (G.symm : E →L[ℝ] E) w‖ ^ 2 ≤ l) :
    sqrtE (T0 G β a x w l) = ENNReal.ofReal √(l * β) := by
  rw [T0_cases G β ha x w hl]
  simp only [hv, ↓reduceIte, add_zero]
  exact sqrtE_coe (mul_nonneg hl.le hβ)

lemma sqrtE_T0_gt (G : E ≃L[ℝ] E) (β : ℝ) {n : ℕ} {a : Fin n → ℝ} (ha : ProbW a)
    (x : Fin n → E) (w : E) {l : ℝ} (hl : 0 < l)
    (hv : ¬ ‖ContinuousLinearMap.adjoint (G.symm : E →L[ℝ] E) w‖ ^ 2 ≤ l) :
    sqrtE (T0 G β a x w l) = ⊤ := by
  rw [T0_cases G β ha x w hl]
  simp only [hv, ↓reduceIte, EReal.coe_add_top, sqrtE_top]

variable [MeasurableSpace E] [BorelSpace E]

open StatFormal.RobustEquality.Paper2.Alternating (centre) in
lemma centre_isProb {n : ℕ} {a : Fin n → ℝ} (ha : ProbW a) (x : Fin n → E) :
    IsProbabilityMeasure (centre a x) :=
  ⟨StatFormal.RobustEquality.Paper2.Alternating.Route.centre_univ x ha.1 ha.2⟩

lemma measurable_inner_left (w : E) : Measurable fun z : E => ⟪w, z⟫ :=
  (continuous_const.inner continuous_id).measurable

lemma edist_inner_sq (w a b : E) :
    edist ⟪w, a⟫ ⟪w, b⟫ ^ (2 : ℝ) = ENNReal.ofReal (⟪w, b - a⟫ ^ 2) := by
  rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two,
    sq_abs, inner_sub_right]
  congr 1; ring

lemma inner_sq_le (G : E ≃L[ℝ] E) (w u : E) {l : ℝ}
    (hv : ‖ContinuousLinearMap.adjoint (G.symm : E →L[ℝ] E) w‖ ^ 2 ≤ l) :
    ⟪w, u⟫ ^ 2 ≤ l * ‖G u‖ ^ 2 := by
  rw [StatFormal.RobustEquality.Paper2.Route.inner_eq_adj G w u]
  set v := ContinuousLinearMap.adjoint (G.symm : E →L[ℝ] E) w
  have h := abs_real_inner_le_norm v (G u)
  have h2 : (inner ℝ v (G u)) ^ 2 ≤ (‖v‖ * ‖G u‖) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith [sq_nonneg ‖G u‖]

open StatFormal.RobustEquality.Paper2.Alternating (centre) in
/-- **Groupwise certificate**, linear rule, anisotropic set on the whole space:
`W₂²(h_w#P̂, h_w#Q) ≤ λβ` for `λ ≥ ‖(G⁻¹)ᵀw‖²`. -/
theorem cert_group_sq (G : E ≃L[ℝ] E) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {a : Fin n → ℝ} (x : Fin n → E)
    (w : E) {l : ℝ} (hl : 0 < l) (hv : ‖ContinuousLinearMap.adjoint (G.symm : E →L[ℝ] E) w‖ ^ 2 ≤ l)
    {Q : Measure E} (hQ : Q ∈ anisoBall G a x β) :
    wassersteinEDist 2 ((centre a x).map fun z => ⟪w, z⟫) (Q.map fun z => ⟪w, z⟫) ^ (2 : ℝ) ≤
      ENNReal.ofReal (l * β) := by
  obtain ⟨hQp, hinf⟩ := hQ
  have hh := measurable_inner_left w
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  set d : ℝ := (δ : ℝ) / l with hd
  have hd0 : 0 < d := by positivity
  have hlt : (⨅ (γ : Measure (E × E)) (_ : IsCoupling γ (centre a x) Q),
      ∫⁻ z, ENNReal.ofReal (‖G (z.2 - z.1)‖ ^ 2) ∂γ) < ENNReal.ofReal (β + d) := by
    refine lt_of_le_of_lt hinf ?_
    exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by linarith, by linarith⟩
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hcpl, hcost⟩ := iInf_lt_iff.1 hγ
  -- the pushforward plan couples `h#P̂` and `h#Q`
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
  have h1 := wassersteinEDist_rpow_le_lintegral hdR (p := 2) two_ne_zero ENNReal.ofNat_ne_top hπ
  rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num, lintegral_map (hdR.pow_const _) (hh.prodMap hh)] at h1
  refine h1.trans ?_
  calc ∫⁻ z, edist (Prod.map (fun z : E => ⟪w, z⟫) (fun z : E => ⟪w, z⟫) z).1
          (Prod.map (fun z : E => ⟪w, z⟫) (fun z : E => ⟪w, z⟫) z).2 ^ (2 : ℝ) ∂γ
        ≤ ∫⁻ z, ENNReal.ofReal l * ENNReal.ofReal (‖G (z.2 - z.1)‖ ^ 2) ∂γ := by
          refine lintegral_mono fun z => ?_
          simp only [Prod.map_fst, Prod.map_snd]
          rw [edist_inner_sq, ← ENNReal.ofReal_mul hl.le]
          exact ENNReal.ofReal_le_ofReal (inner_sq_le G w _ hv)
      _ = ENNReal.ofReal l * ∫⁻ z, ENNReal.ofReal (‖G (z.2 - z.1)‖ ^ 2) ∂γ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal l * ENNReal.ofReal (β + d) := by gcongr
      _ = ENNReal.ofReal (l * β) + δ := by
          rw [← ENNReal.ofReal_mul hl.le, mul_add, hd, mul_div_cancel₀ _ hl.ne',
            ENNReal.ofReal_add (mul_nonneg hl.le hβ) δ.coe_nonneg, ENNReal.ofReal_coe_nnreal]

open StatFormal.RobustEquality.Paper2.Alternating (centre) in
/-- `W₂(h_w#P̂, h_w#Q) ≤ √T⁰(w, λ)` for every `λ > 0`. -/
theorem cert_group (G : E ≃L[ℝ] E) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {a : Fin n → ℝ} (ha : ProbW a)
    (x : Fin n → E) (w : E) {l : ℝ} (hl : 0 < l) {Q : Measure E} (hQ : Q ∈ anisoBall G a x β) :
    wassersteinEDist 2 ((centre a x).map fun z => ⟪w, z⟫) (Q.map fun z => ⟪w, z⟫) ≤
      sqrtE (T0 G β a x w l) := by
  by_cases hv : ‖ContinuousLinearMap.adjoint (G.symm : E →L[ℝ] E) w‖ ^ 2 ≤ l
  · rw [sqrtE_T0_le G hβ ha x w hl hv]
    have h := cert_group_sq G hβ x w hl hv hQ
    have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hl.le hβ) (by norm_num), ← Real.sqrt_eq_rpow] at h2
    exact h2
  · rw [sqrtE_T0_gt G β ha x w hl hv]; exact le_top

end Group

section Delta

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] {n₀ n₁ : ℕ}

lemma pcost_inner (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (w : E) (γ : Fin n₀ → Fin n₁ → ℝ) :
    StatFormal.RobustEquality.Paper2.Alternating.pcost (fun i => ⟪w, x₀ i⟫) (fun j => ⟪w, x₁ j⟫) γ =
      ∑ i, ∑ j, γ i j * ⟪w, x₀ i - x₁ j⟫ ^ 2 := by
  unfold StatFormal.RobustEquality.Paper2.Alternating.pcost
  simp_rw [inner_sub_right]

open StatFormal.RobustEquality.Paper2.Alternating (centre) in
/-- `lem:delta-inf` for the linear rule: an optimal plan `γ⋆`, `W₂(h_w#P̂₀, h_w#P̂₁) = Δ(w) = |M_{γ⋆}^{1/2} w|`, and
`Δ(w) ≤ |M_γ^{1/2} w|` for every plan. -/
lemma delta_plan {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ} (h₀ : ProbW a₀) (h₁ : ProbW a₁) (x₀ : Fin n₀ → E)
    (x₁ : Fin n₁ → E) (w : E) :
    ∃ γs ∈ Polytope a₀ a₁,
      wassersteinEDist 2 ((centre a₀ x₀).map fun z => ⟪w, z⟫) ((centre a₁ x₁).map fun z => ⟪w, z⟫) =
          ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ w) ∧
        gamNorm γs x₀ x₁ w = Deltafin a₀ x₀ a₁ x₁ w ∧
        ∀ γ ∈ Polytope a₀ a₁, Deltafin a₀ x₀ a₁ x₁ w ≤ gamNorm γ x₀ x₁ w := by
  obtain ⟨⟨c, hc⟩, hW⟩ := StatFormal.RobustEquality.Paper2.Alternating.delta_inf_W2 E n₀ n₁ a₀ x₀ a₁ x₁
    (fun z => ⟪w, z⟫) (measurable_inner_left w) h₀.1 h₀.2 h₁.1 h₁.2
  have hWc := hW c hc
  obtain ⟨γs, hγs, hpc⟩ := hc.1
  have hgam : ∀ γ, gamNorm γ x₀ x₁ w =
      √(StatFormal.RobustEquality.Paper2.Alternating.pcost (fun i => ⟪w, x₀ i⟫) (fun j => ⟪w, x₁ j⟫) γ) := by
    intro γ; rw [pcost_inner]; rfl
  have hD : Deltafin a₀ x₀ a₁ x₁ w = √c := by
    unfold Deltafin
    congr 1
    have hc' : IsLeast (Set.range fun γ : {γ : Fin n₀ → Fin n₁ → ℝ | (∀ i j, 0 ≤ γ i j) ∧
        (∀ i, ∑ j, γ i j = a₀ i) ∧ ∀ j, ∑ i, γ i j = a₁ j} =>
        ∑ i, ∑ j, (γ : Fin n₀ → Fin n₁ → ℝ) i j * ⟪w, x₀ i - x₁ j⟫ ^ 2) c := by
      have e : (Set.range fun γ : {γ : Fin n₀ → Fin n₁ → ℝ | (∀ i j, 0 ≤ γ i j) ∧
          (∀ i, ∑ j, γ i j = a₀ i) ∧ ∀ j, ∑ i, γ i j = a₁ j} =>
          ∑ i, ∑ j, (γ : Fin n₀ → Fin n₁ → ℝ) i j * ⟪w, x₀ i - x₁ j⟫ ^ 2) =
          StatFormal.RobustEquality.Paper2.Alternating.pcost (fun i => ⟪w, x₀ i⟫) (fun j => ⟪w, x₁ j⟫) ''
            StatFormal.RobustEquality.Paper2.Alternating.Plans a₀ a₁ := by
        ext t
        constructor
        · rintro ⟨γ, rfl⟩; exact ⟨γ, γ.2, pcost_inner x₀ x₁ w γ⟩
        · rintro ⟨γ, hγ, rfl⟩; exact ⟨⟨γ, hγ⟩, (pcost_inner x₀ x₁ w γ).symm⟩
      rw [e]; exact hc
    exact IsLeast.csInf_eq hc'
  refine ⟨γs, hγs, by rw [hWc, hD], by rw [hgam, hpc, hD], fun γ hγ => ?_⟩
  rw [hD, hgam]
  exact Real.sqrt_le_sqrt (hc.2 ⟨γ, hγ, rfl⟩)

end Delta

/-! ### Independent anisotropic sets -/

section Aniso

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] {n₀ n₁ : ℕ}

open StatFormal.RobustEquality.Paper2.Alternating (centre) in
/-- The certificate for independent anisotropic sets on `K = E` and a linear rule:
`W₂(h_w#Q₀, h_w#Q₁) ≤ Δ(w) + √T⁰₀ + √T⁰₁` with `Δ(w) = W₂(h_w#P̂₀, h_w#P̂₁)`. -/
theorem cert_aniso (G₀ G₁ : E ≃L[ℝ] E) {β₀ β₁ : ℝ} (hβ₀ : 0 ≤ β₀) (hβ₁ : 0 ≤ β₁) {a₀ : Fin n₀ → ℝ}
    {a₁ : Fin n₁ → ℝ} (h₀ : ProbW a₀) (h₁ : ProbW a₁) (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (w : E)
    {l₀ l₁ : ℝ} (hl₀ : 0 < l₀) (hl₁ : 0 < l₁) {Q₀ Q₁ : Measure E} (hQ₀ : Q₀ ∈ anisoBall G₀ a₀ x₀ β₀)
    (hQ₁ : Q₁ ∈ anisoBall G₁ a₁ x₁ β₁) :
    wassersteinEDist 2 (Q₀.map fun z => ⟪w, z⟫) (Q₁.map fun z => ⟪w, z⟫) ≤
      wassersteinEDist 2 ((centre a₀ x₀).map fun z => ⟪w, z⟫) ((centre a₁ x₁).map fun z => ⟪w, z⟫) +
        sqrtE (T0 G₀ β₀ a₀ x₀ w l₀) + sqrtE (T0 G₁ β₁ a₁ x₁ w l₁) := by
  have hh := measurable_inner_left (E := E) w
  have hd : Measurable fun z : ℝ × ℝ => edist z.1 z.2 := measurable_edist
  have : IsProbabilityMeasure (centre a₀ x₀) := centre_isProb h₀ x₀
  have : IsProbabilityMeasure (centre a₁ x₁) := centre_isProb h₁ x₁
  have : IsProbabilityMeasure ((centre a₀ x₀).map fun z => ⟪w, z⟫) :=
    (Measure.isProbabilityMeasure_map_iff hh.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure ((centre a₁ x₁).map fun z => ⟪w, z⟫) :=
    (Measure.isProbabilityMeasure_map_iff hh.aemeasurable).2 inferInstance
  have t1 := wassersteinEDist_triangle hd (p := 2) (by norm_num) (Q₀.map fun z => ⟪w, z⟫)
    ((centre a₀ x₀).map fun z => ⟪w, z⟫) (Q₁.map fun z => ⟪w, z⟫)
  have t2 := wassersteinEDist_triangle hd (p := 2) (by norm_num) ((centre a₀ x₀).map fun z => ⟪w, z⟫)
    ((centre a₁ x₁).map fun z => ⟪w, z⟫) (Q₁.map fun z => ⟪w, z⟫)
  have c0 := cert_group G₀ hβ₀ h₀ x₀ w hl₀ hQ₀
  have c1 := cert_group G₁ hβ₁ h₁ x₁ w hl₁ hQ₁
  rw [wassersteinEDist_comm hd] at c0
  calc wassersteinEDist 2 (Q₀.map fun z => ⟪w, z⟫) (Q₁.map fun z => ⟪w, z⟫)
      ≤ wassersteinEDist 2 (Q₀.map fun z => ⟪w, z⟫) ((centre a₀ x₀).map fun z => ⟪w, z⟫) +
          (wassersteinEDist 2 ((centre a₀ x₀).map fun z => ⟪w, z⟫) ((centre a₁ x₁).map fun z => ⟪w, z⟫) +
            wassersteinEDist 2 ((centre a₁ x₁).map fun z => ⟪w, z⟫) (Q₁.map fun z => ⟪w, z⟫)) :=
        t1.trans (add_le_add le_rfl t2)
    _ ≤ sqrtE (T0 G₀ β₀ a₀ x₀ w l₀) +
          (wassersteinEDist 2 ((centre a₀ x₀).map fun z => ⟪w, z⟫) ((centre a₁ x₁).map fun z => ⟪w, z⟫) +
            sqrtE (T0 G₁ β₁ a₁ x₁ w l₁)) := by gcongr
    _ = _ := by ring

theorem jointmin_aniso_upper : Claims.jointmin_aniso_upper := by
  intro E _ _ _ _ _ n₀ n₁ G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ w Rh η l₀ l₁ γ h₀ h₁ hβ₀ hβ₁ hRh hη hl₀ hl₁ hγ
  obtain ⟨γs, hγs, hW, -, hle⟩ := delta_plan h₀ h₁ x₀ x₁ w
  unfold jointObjAniso
  gcongr
  refine iSup₂_le fun Q₀ hQ₀ => iSup₂_le fun Q₁ hQ₁ => ?_
  have h := cert_aniso G₀ G₁ hβ₀ hβ₁ h₀ h₁ x₀ x₁ w hl₀ hl₁ hQ₀ hQ₁
  rw [hW] at h
  have h' := h.trans (add_le_add_three (ENNReal.ofReal_le_ofReal (hle γ hγ)) le_rfl le_rfl)
  exact pow_le_pow_left₀ zero_le h' 2

/-- `X + ⨅ s₀ + ⨅ s₁ = ⨅ ⨅ (X + s₀ + s₁)` and the square commutes with `⨅`. -/
lemma iInf_two_sq (X : ℝ≥0∞) (s₀ s₁ : Set.Ioi (0 : ℝ) → ℝ≥0∞) :
    (⨅ l₀, ⨅ l₁, (X + s₀ l₀ + s₁ l₁) ^ 2) = (X + (⨅ l, s₀ l) + (⨅ l, s₁ l)) ^ 2 := by
  have e : X + (⨅ l, s₀ l) + (⨅ l, s₁ l) = ⨅ l₀, ⨅ l₁, (X + s₀ l₀ + s₁ l₁) := by
    rw [ENNReal.add_iInf (a := X), ENNReal.iInf_add]
    exact iInf_congr fun l₀ => by rw [ENNReal.add_iInf]
  rw [e, iInf_sq]
  exact iInf_congr fun l₀ => by rw [iInf_sq]

lemma iInf_affine {ι κ : Sort*} (c m : ℝ≥0∞) (hm0 : m ≠ 0) (hm : m ≠ ⊤) (f : ι → κ → ℝ≥0∞) :
    (⨅ i, ⨅ k, (c + m * f i k)) = c + m * ⨅ i, ⨅ k, f i k := by
  rw [ENNReal.mul_iInf_of_ne hm0 hm, ENNReal.add_iInf]
  exact iInf_congr fun i => by rw [ENNReal.mul_iInf_of_ne hm0 hm, ENNReal.add_iInf]

end Aniso

/-- The minimum over the polytope is attained (no measurable structure needed). -/
lemma delta_attained {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {n₀ n₁ : ℕ}
    {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ} (h₀ : ProbW a₀) (h₁ : ProbW a₁) (x₀ : Fin n₀ → E)
    (x₁ : Fin n₁ → E) (w : E) :
    ∃ γs ∈ Polytope a₀ a₁, gamNorm γs x₀ x₁ w = Deltafin a₀ x₀ a₁ x₁ w ∧
      ∀ γ ∈ Polytope a₀ a₁, Deltafin a₀ x₀ a₁ x₁ w ≤ gamNorm γ x₀ x₁ w := by
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨γs, hγs, -, h1, h2⟩ := delta_plan h₀ h₁ x₀ x₁ w
  exact ⟨γs, hγs, h1, h2⟩

theorem jointmin_aniso_inf : Claims.jointmin_aniso_inf := by
  intro E _ _ _ _ n₀ n₁ G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ w Rh η h₀ h₁ hβ₀ hβ₁ hη
  obtain ⟨γs, hγs, heq, hle⟩ := delta_attained h₀ h₁ x₀ x₁ w
  have hm0 : ENNReal.ofReal η ≠ 0 := by simp [hη]
  refine ⟨iInf_congr fun l₀ => iInf_congr fun l₁ => ?_, ?_⟩
  · refine le_antisymm ?_ (le_iInf fun γ => ?_)
    · refine iInf_le_of_le ⟨γs, hγs⟩ (le_of_eq ?_)
      unfold jointObjAniso penObjAniso
      rw [heq]
    · unfold jointObjAniso penObjAniso
      gcongr
      exact hle γ γ.2
  · unfold penObjAniso
    rw [iInf_affine _ _ hm0 ENNReal.ofReal_ne_top, iInf_two_sq, iInf_sqrtT0 G₀ hβ₀ h₀ x₀ w,
      iInf_sqrtT0 G₁ hβ₁ h₁ x₁ w]

/-! ### Structured sets with a finite cell cover -/

lemma sup_add_sq {ι : Sort*} [Nonempty ι] (Y : ι → ℝ≥0∞) (s₀ s₁ : ℝ≥0∞) :
    ((⨆ j, Y j) + s₀ + s₁) ^ 2 = ⨆ j, (Y j + s₀ + s₁) ^ 2 := by
  rw [ENNReal.iSup_add, ENNReal.iSup_add, iSup_sq]

section Struct

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {n₀ n₁ : ℕ}

/-- `T⁰` does not depend on the centre's atoms. -/
lemma T0_centre (G : E ≃L[ℝ] E) (β : ℝ) {n : ℕ} {a : Fin n → ℝ} (ha : ProbW a) (x y : Fin n → E) (w : E)
    {l : ℝ} (hl : 0 < l) : T0 G β a x w l = T0 G β a y w l := by
  rw [T0_cases G β ha x w hl, T0_cases G β ha y w hl]

theorem jointmin_struct_upper : Claims.jointmin_struct_upper := by
  intro E _ _ _ _ _ Θ n₀ n₁ J G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A b cell θc p w Rh η l₀ l₁ γ h₀ h₁ hβ₀ hβ₁ hRh hη
    hl₀ hl₁ hcov hθc hγ
  unfold worstStruct jointObjStruct
  gcongr
  set s₀ := sqrtE (T0 G₀ β₀ a₀ x₀ w l₀)
  set s₁ := sqrtE (T0 G₁ β₁ a₁ x₁ w l₁)
  -- each slice
  have hslice : ∀ θ, StatFormal.Wave19b.worstDisp (anisoBall G₀ a₀ (fun i => A θ (x₀ i) + b θ) β₀)
      (anisoBall G₁ a₁ (fun j => A θ (x₁ j) + b θ) β₁) (fun z => ⟪w, z⟫) ≤
      (ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A θ) w)) + s₀ + s₁) ^ 2 := by
    intro θ
    obtain ⟨-, -, hW, -, -⟩ := delta_plan h₀ h₁ (fun i => A θ (x₀ i) + b θ) (fun j => A θ (x₁ j) + b θ) w
    rw [deltafin_affine] at hW
    refine iSup₂_le fun Q₀ hQ₀ => iSup₂_le fun Q₁ hQ₁ => ?_
    have h := cert_aniso G₀ G₁ hβ₀ hβ₁ h₀ h₁ _ _ w hl₀ hl₁ hQ₀ hQ₁
    rw [hW, T0_centre G₀ β₀ h₀ _ x₀ w hl₀, T0_centre G₁ β₁ h₁ _ x₁ w hl₁] at h
    exact pow_le_pow_left₀ zero_le h 2
  rcases isEmpty_or_nonempty (Fin J) with hJ | hJ
  · have hΘ : IsEmpty Θ := ⟨fun θ => by obtain ⟨j, -⟩ := hcov θ; exact hJ.elim j⟩
    simp
  have hcells := StatFormal.Wave20a.structured_cells E Θ n₀ n₁ J a₀ x₀ a₁ x₁ A cell θc p w h₀ h₁ hcov hθc
  have hgam : ∀ j, ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w)) ≤
      ENNReal.ofReal (gamNorm (γ j) x₀ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w)) := by
    intro j
    obtain ⟨-, -, -, hle⟩ := delta_attained h₀ h₁ x₀ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w)
    exact ENNReal.ofReal_le_ofReal (hle (γ j) (hγ j))
  calc (⨆ θ, StatFormal.Wave19b.worstDisp (anisoBall G₀ a₀ (fun i => A θ (x₀ i) + b θ) β₀)
        (anisoBall G₁ a₁ (fun j => A θ (x₁ j) + b θ) β₁) (fun z => ⟪w, z⟫))
      ≤ ⨆ θ, (ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A θ) w)) + s₀ + s₁) ^ 2 :=
        iSup_mono hslice
    _ ≤ ((⨆ θ, ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A θ) w))) + s₀ + s₁) ^ 2 :=
        iSup_le fun θ => pow_le_pow_left₀ zero_le (add_le_add_three (le_iSup (fun θ =>
          ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A θ) w))) θ) le_rfl le_rfl) 2
    _ ≤ ((⨆ j, (ENNReal.ofReal (gamNorm (γ j) x₀ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w)) +
          Lcell a₀ x₀ a₁ x₁ p A (cell j) (θc j) w)) + s₀ + s₁) ^ 2 := by
        gcongr
        exact hcells.trans (iSup_mono fun j => add_le_add (hgam j) le_rfl)
    _ = _ := sup_add_sq _ _ _

theorem jointmin_struct_inf : Claims.jointmin_struct_inf := by
  intro E _ _ _ _ Θ n₀ n₁ J G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A b cell θc p w Rh η h₀ h₁ hβ₀ hβ₁ hη hcov hθc
  have hm0 : ENNReal.ofReal η ≠ 0 := by simp [hη]
  set N₀ := ENNReal.ofReal (√β₀ * ‖ContinuousLinearMap.adjoint (G₀.symm : E →L[ℝ] E) w‖)
  set N₁ := ENNReal.ofReal (√β₁ * ‖ContinuousLinearMap.adjoint (G₁.symm : E →L[ℝ] E) w‖)
  set D : Fin J → ℝ≥0∞ := fun j => ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w))
  set L : Fin J → ℝ≥0∞ := fun j => Lcell a₀ x₀ a₁ x₁ p A (cell j) (θc j) w
  -- the optimal couplings, cell by cell
  have hopt : ∀ j, ∃ γs ∈ Polytope a₀ a₁,
      gamNorm γs x₀ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w) =
        Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w) ∧
      ∀ γ ∈ Polytope a₀ a₁, Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w) ≤
        gamNorm γ x₀ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w) :=
    fun j => delta_attained h₀ h₁ x₀ x₁ _
  choose γs hγs heq hle using hopt
  have hγinf : ∀ l₀ l₁ : ℝ, (⨅ γ : Fin J → Polytope a₀ a₁,
      jointObjStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A cell θc p w Rh η l₀ l₁ (fun j => γ j)) =
      ENNReal.ofReal Rh + ENNReal.ofReal η * ⨆ j, (D j + L j + sqrtE (T0 G₀ β₀ a₀ x₀ w l₀) +
        sqrtE (T0 G₁ β₁ a₁ x₁ w l₁)) ^ 2 := by
    intro l₀ l₁
    refine le_antisymm ?_ (le_iInf fun γ => ?_)
    · refine iInf_le_of_le (fun j => ⟨γs j, hγs j⟩) (le_of_eq ?_)
      unfold jointObjStruct
      simp only [heq, D, L]
    · unfold jointObjStruct
      gcongr with j
      exact ENNReal.ofReal_le_ofReal (hle j _ (γ j).2)
  have hNe : Nonempty (Set.Ioi (0 : ℝ)) := ⟨⟨1, Set.mem_Ioi.2 one_pos⟩⟩
  have hval : (⨅ (lam₀ : Set.Ioi (0 : ℝ)) (lam₁ : Set.Ioi (0 : ℝ)) (γ : Fin J → Polytope a₀ a₁),
      jointObjStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A cell θc p w Rh η lam₀ lam₁ (fun j => γ j)) =
      ENNReal.ofReal Rh + ENNReal.ofReal η * ⨆ j, (D j + L j + N₀ + N₁) ^ 2 := by
    simp_rw [hγinf]
    rcases isEmpty_or_nonempty (Fin J) with hJ | hJ
    · simp
    · simp_rw [← sup_add_sq]
      rw [iInf_affine _ _ hm0 ENNReal.ofReal_ne_top, iInf_two_sq, iInf_sqrtT0 G₀ hβ₀ h₀ x₀ w,
        iInf_sqrtT0 G₁ hβ₁ h₁ x₁ w]
  refine ⟨hval, ?_⟩
  rw [hval]
  gcongr
  rcases isEmpty_or_nonempty Θ with hΘ | hΘ
  · unfold certStruct; simp
  have hJ : Nonempty (Fin J) := by
    obtain ⟨θ⟩ := hΘ; obtain ⟨j, -⟩ := hcov θ; exact ⟨j⟩
  rw [StatFormal.Wave20a.structured_value E Θ n₀ n₁ G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A b w hβ₀ hβ₁ h₀ h₁,
    ← sup_add_sq]
  gcongr
  exact StatFormal.Wave20a.structured_cells E Θ n₀ n₁ J a₀ x₀ a₁ x₁ A cell θc p w h₀ h₁ hcov hθc

end Struct

end StatFormal.Wave28e
