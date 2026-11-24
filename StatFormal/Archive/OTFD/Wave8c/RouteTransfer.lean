import StatFormal.Archive.OTFD.Wave8c.Statements

/-!
# Route: C `prop:cond-transfer` (i)–(iii)

* (i)–(ii): pure measure theory from the four defining properties of the rank pairs.
* Uniqueness of McCann maps (`gradMap_ae_eq`): a subgradient selection is a Kantorovich-optimal map (Tau Ceti), its
  graph plan is the unique optimal plan for an absolutely continuous source with finite second moments, and equal
  graph plans give a.e. equal maps.
* (iii): affine maps `z ↦ Bz + e` with `B` symmetric positive semidefinite are subgradient selections of a convex
  quadratic, so `F_x = A⁻¹(· − b)` and `Q_{x'} = b' + A'·` a.e.; the spectrum through the generalised Rayleigh quotient
  `c = (w*A'w)/(w*Aw)`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open scoped InnerProductSpace ENNReal RealInnerProductSpace

namespace StatFormal.OTFD.Wave8c

/-! ### (i)–(ii) -/

section Pairs
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

lemma rankPair_ae_FQ {μ P : Measure E} {F Q : E → E} (h : IsRankPair μ P F Q) {ν : Measure E} {G : E → E}
    (hG : AEMeasurable G ν) (hGmap : ν.map G = μ) : ∀ᵐ z ∂ν, F (Q (G z)) = G z := by
  have h' : ∀ᵐ u ∂(ν.map G), F (Q u) = u := by rw [hGmap]; exact h.2.2.2.2.1
  exact ae_of_ae_map hG h'

end Pairs

theorem transfer_push_rank : Claims.transfer_push_rank := by
  intro K μ Px Px' Fx Qx Fx' Qx' h h'
  obtain ⟨hF, hQ, hQmap, hFmap, -, -⟩ := h
  refine ⟨?_, rankPair_ae_FQ h' hF.aemeasurable hFmap⟩
  rw [show (fun z => Qx' (Fx z)) = Qx' ∘ Fx from rfl, ← Measure.map_map h'.2.1 hF, hFmap, h'.2.2.1]

theorem transfer_unique : Claims.transfer_unique := by
  intro K μ Px Px' Fx Qx Fx' Qx' S h h' hS hSmap hSrank
  have hQF : ∀ᵐ y ∂(Px.map S), Qx' (Fx' y) = y := by rw [hSmap]; exact h'.2.2.2.2.2
  filter_upwards [ae_of_ae_map hS.aemeasurable hQF, hSrank] with z h1 h2
  rw [← h1, h2]

theorem transfer_cocycle : Claims.transfer_cocycle := by
  intro K μ Px Px' Px'' Fx Qx Fx' Qx' Fx'' Qx'' h h' h''
  refine ⟨h.2.2.2.2.2, ?_⟩
  filter_upwards [rankPair_ae_FQ h' h.1.aemeasurable h.2.2.2.1] with z hz
  rw [hz]

/-! ### Uniqueness of McCann maps -/

section Unique
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma measurable_quadCost : Measurable (quadCost : E × E → ℝ≥0∞) := by
  unfold quadCost; fun_prop

/-- A McCann map with finite second moments is a Kantorovich-optimal map. -/
lemma IsGradMap.isOptimal {α β : Measure E} [IsFiniteMeasure α] {T : E → E} (hT : IsGradMap α β T)
    (h2α : MemLp id 2 α) (h2β : MemLp id 2 β) :
    TauCeti.IsKantorovichOptimalTransportMap quadCost α β T := by
  obtain ⟨hTm, hTmap, φ, hφ⟩ := hT
  exact TauCeti.isKantorovichOptimalTransportMap_of_ae_mem_subdifferential h2α h2β
    ⟨hTm.aemeasurable, hTmap⟩ hφ

/-- **Uniqueness of McCann maps**: two subgradient selections pushing an absolutely continuous `α` to `β`
(finite second moments) agree `α`-a.e. -/
theorem gradMap_ae_eq {ρ : Measure E} [ρ.IsAddHaarMeasure] {α β : Measure E} [IsProbabilityMeasure α]
    (hα : α ≪ ρ) (h2α : MemLp id 2 α) (h2β : MemLp id 2 β) {T S : E → E} (hT : IsGradMap α β T)
    (hS : IsGradMap α β S) : T =ᵐ[α] S := by
  haveI : MeasurableEq E := ⟨isClosed_diagonal.measurableSet⟩
  have hTl : HasLaw T β α := ⟨hT.1.aemeasurable, hT.2.1⟩
  have hSl : HasLaw S β α := ⟨hS.1.aemeasurable, hS.2.1⟩
  have hoT := (TauCeti.isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hTl
    measurable_quadCost.aemeasurable).1 (hT.isOptimal h2α h2β)
  have hoS := (TauCeti.isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hSl
    measurable_quadCost.aemeasurable).1 (hS.isOptimal h2α h2β)
  have hfin : TauCeti.transportCost quadCost α β ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (TauCeti.transportCost_le_lintegral (TauCeti.isCoupling_graphPlan hTl) _)
    change ∫⁻ z : E × E, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) ∂(TauCeti.graphPlan T α) ≠ ⊤
    rw [(TauCeti.isCoupling_graphPlan hTl).lintegral_norm_sub_sq_div_two h2α h2β]
    exact ENNReal.ofReal_ne_top
  have heq := hoT.unique hα hoS hfin
  have h1 := TauCeti.ae_snd_eq_graphPlan hS.1.aemeasurable (μ := α)
  rw [← heq] at h1
  exact (TauCeti.ae_snd_eq_graphPlan_iff hT.1.aemeasurable hS.1.aemeasurable).1 h1

end Unique


/-! ### Linear algebra on `ℝ^K` -/

section Lin
variable {K : ℕ}

lemma continuous_mvec (A : Matrix (Fin K) (Fin K) ℝ) : Continuous (mvec A) :=
  (Matrix.toEuclideanLin A).continuous_of_finiteDimensional

lemma measurable_mvec (A : Matrix (Fin K) (Fin K) ℝ) : Measurable (mvec A) :=
  (continuous_mvec A).measurable

lemma mvec_mul (A B : Matrix (Fin K) (Fin K) ℝ) (u : EuclideanSpace ℝ (Fin K)) :
    mvec (A * B) u = mvec A (mvec B u) := by
  simp [mvec]

lemma mvec_add (A : Matrix (Fin K) (Fin K) ℝ) (x y : EuclideanSpace ℝ (Fin K)) :
    mvec A (x + y) = mvec A x + mvec A y := map_add (Matrix.toEuclideanLin A) x y

lemma mvec_sub (A : Matrix (Fin K) (Fin K) ℝ) (x y : EuclideanSpace ℝ (Fin K)) :
    mvec A (x - y) = mvec A x - mvec A y := map_sub (Matrix.toEuclideanLin A) x y

lemma mvec_neg (A : Matrix (Fin K) (Fin K) ℝ) (x : EuclideanSpace ℝ (Fin K)) :
    mvec A (-x) = -mvec A x := map_neg (Matrix.toEuclideanLin A) x

lemma mvec_smul (A : Matrix (Fin K) (Fin K) ℝ) (c : ℝ) (x : EuclideanSpace ℝ (Fin K)) :
    mvec A (c • x) = c • mvec A x := map_smul (Matrix.toEuclideanLin A) c x

lemma mvec_one (u : EuclideanSpace ℝ (Fin K)) : mvec (1 : Matrix (Fin K) (Fin K) ℝ) u = u := by
  simp [mvec]

lemma inner_mvec (A : Matrix (Fin K) (Fin K) ℝ) (x y : EuclideanSpace ℝ (Fin K)) :
    ⟪x, mvec A y⟫ = WithLp.ofLp x ⬝ᵥ (A *ᵥ WithLp.ofLp y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simp [mvec, Matrix.toLpLin_apply]

lemma inner_mvec_symm {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian) (x y : EuclideanSpace ℝ (Fin K)) :
    ⟪x, mvec A y⟫ = ⟪mvec A x, y⟫ := by
  have := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) x y
  simpa [mvec] using this.symm

lemma inner_mvec_nonneg {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.PosSemidef) (x : EuclideanSpace ℝ (Fin K)) :
    0 ≤ ⟪x, mvec A x⟫ := by
  rw [inner_mvec]
  simpa using hA.dotProduct_mulVec_nonneg (WithLp.ofLp x)

lemma det_ne_zero_of_posDef {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.PosDef) : A.det ≠ 0 :=
  hA.det_pos.ne'

lemma mvec_inv_mul {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.det ≠ 0) (u : EuclideanSpace ℝ (Fin K)) :
    mvec A⁻¹ (mvec A u) = u := by
  rw [← mvec_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA), mvec_one]

lemma mvec_mul_inv {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.det ≠ 0) (u : EuclideanSpace ℝ (Fin K)) :
    mvec A (mvec A⁻¹ u) = u := by
  rw [← mvec_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), mvec_one]

/-- `z ↦ Bz + e` with `B` symmetric positive semidefinite is the gradient of `½⟨z,Bz⟩ + ⟨e,z⟩`. -/
lemma affine_mem_subdiff {B : Matrix (Fin K) (Fin K) ℝ} (hB : B.PosSemidef) (e z : EuclideanSpace ℝ (Fin K)) :
    mvec B z + e ∈ TauCeti.subdifferential (innerₗ (EuclideanSpace ℝ (Fin K)))
      (fun z => ((⟪z, mvec B z⟫ / 2 + ⟪e, z⟫ : ℝ) : EReal)) z := by
  refine ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _, fun z' => ?_⟩
  rw [innerₗ_apply_apply, ← EReal.coe_add, EReal.coe_le_coe_iff]
  obtain ⟨d, rfl⟩ : ∃ d, z' = z + d := ⟨z' - z, by abel⟩
  have hsym := inner_mvec_symm hB.isHermitian z d
  have hnn := inner_mvec_nonneg hB d
  have hexp : ⟪z + d, mvec B (z + d)⟫ = ⟪z, mvec B z⟫ + ⟪z, mvec B d⟫ + ⟪d, mvec B z⟫ + ⟪d, mvec B d⟫ := by
    rw [mvec_add, inner_add_left, inner_add_right, inner_add_right]; ring
  rw [add_sub_cancel_left, hexp, inner_add_right, inner_add_right]
  have h4 := real_inner_comm (mvec B z) d
  have h5 := real_inner_comm e d
  linarith

end Lin

section GradAffine
variable {K : ℕ}

lemma isGradMap_affine (α : Measure (EuclideanSpace ℝ (Fin K))) {B : Matrix (Fin K) (Fin K) ℝ}
    (hB : B.PosSemidef) (e : EuclideanSpace ℝ (Fin K)) :
    IsGradMap α (α.map fun z => mvec B z + e) fun z => mvec B z + e :=
  ⟨(measurable_mvec B).add_const e, rfl, _, Eventually.of_forall fun z => affine_mem_subdiff hB e z⟩

lemma memLp_map_affine {μ : Measure (EuclideanSpace ℝ (Fin K))} [IsFiniteMeasure μ] (h2 : MemLp id 2 μ)
    (B : Matrix (Fin K) (Fin K) ℝ) (e : EuclideanSpace ℝ (Fin K)) :
    MemLp id 2 (μ.map fun z => mvec B z + e) := by
  have hm : Measurable fun z => mvec B z + e := (measurable_mvec B).add_const e
  rw [memLp_map_measure_iff aestronglyMeasurable_id hm.aemeasurable]
  have h1 : MemLp (mvec B ∘ id) 2 μ :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)).comp_memLp' h2
  exact h1.add (memLp_const e)

lemma ac_map_affine {μ : Measure (EuclideanSpace ℝ (Fin K))} (hμ : μ ≪ volume) {B : Matrix (Fin K) (Fin K) ℝ}
    (hB : B.det ≠ 0) (e : EuclideanSpace ℝ (Fin K)) : (μ.map fun z => mvec B z + e) ≪ volume := by
  have hm : Measurable fun z => mvec B z + e := (measurable_mvec B).add_const e
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
  rw [Measure.map_apply hm hs]
  apply hμ
  have : (fun z => mvec B z + e) ⁻¹' s = (Matrix.toEuclideanLin B) ⁻¹' ((fun y => y + e) ⁻¹' s) := rfl
  rw [this, Measure.addHaar_preimage_linearMap volume (by simpa using hB), measure_preimage_add_right, h0,
    mul_zero]

end GradAffine

theorem affine_formula : Claims.affine_formula := by
  intro K μ _ b b' A A' Fx Qx' hμ h2 hA hA' hF hQ
  have hdA := det_ne_zero_of_posDef hA
  have haff : affineMap b A = fun z => mvec A z + b := by funext z; simp [affineMap, add_comm]
  have haff' : affineMap b' A' = fun z => mvec A' z + b' := by funext z; simp [affineMap, add_comm]
  set Px := μ.map (affineMap b A) with hPx
  haveI : IsProbabilityMeasure Px := inferInstance
  have hPxac : Px ≪ volume := by rw [hPx, haff]; exact ac_map_affine hμ hdA b
  have h2Px : MemLp id 2 Px := by rw [hPx, haff]; exact memLp_map_affine h2 A b
  -- the rank map
  set F0 : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K) := fun z => mvec A⁻¹ z + -mvec A⁻¹ b with hF0
  have hF0meas : Measurable F0 := (measurable_mvec _).add_const _
  have hF0map : Px.map F0 = μ := by
    rw [hPx, Measure.map_map hF0meas (by rw [haff]; fun_prop)]
    convert Measure.map_id using 2
    funext u
    simp [F0, affineMap, mvec_add, mvec_inv_mul hdA]
  have hF0grad : IsGradMap Px μ F0 := by
    have := isGradMap_affine Px hA.inv.posSemidef (-mvec A⁻¹ b)
    rwa [← hF0, hF0map] at this
  have hFae : Fx =ᵐ[Px] F0 := gradMap_ae_eq hPxac h2Px h2 hF hF0grad
  -- the quantile map at `x'`
  have hQ0grad : IsGradMap μ (μ.map (affineMap b' A')) fun u => mvec A' u + b' := by
    rw [haff']; exact isGradMap_affine μ hA'.posSemidef b'
  have h2Px' : MemLp id 2 (μ.map (affineMap b' A')) := by rw [haff']; exact memLp_map_affine h2 A' b'
  have hQae : Qx' =ᵐ[μ] fun u => mvec A' u + b' := gradMap_ae_eq hμ h2 h2Px' hQ hQ0grad
  have hQae' : ∀ᵐ z ∂Px, Qx' (F0 z) = mvec A' (F0 z) + b' := by
    rw [← hF0map] at hQae; exact ae_of_ae_map hF0meas.aemeasurable hQae
  filter_upwards [hFae, hQae'] with z h1 h3
  rw [h1, h3, mvec_mul, add_comm (mvec A' (F0 z))]
  congr 2
  simp [F0, mvec_sub, sub_eq_add_neg]


/-! ### Spectrum and symmetry of `A'A⁻¹` -/

section Spec
variable {K : ℕ}

lemma rayleigh_pos {A A' : Matrix (Fin K) (Fin K) ℝ} (hA : A.PosDef) (hA' : A'.PosDef) {v : Fin K → ℝ}
    (hv : v ≠ 0) {c : ℝ} (h : (A' * A⁻¹) *ᵥ v = c • v) : 0 < c := by
  have hdA := det_ne_zero_of_posDef hA
  set w := A⁻¹ *ᵥ v with hw
  have hAw : A *ᵥ w = v := by
    rw [hw, mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdA), one_mulVec]
  have hw0 : w ≠ 0 := by intro h0; apply hv; rw [← hAw, h0, mulVec_zero]
  have h' : A' *ᵥ w = c • (A *ᵥ w) := by rw [hAw, ← h, hw, mulVec_mulVec]
  have hq := hA.dotProduct_mulVec_pos hw0
  have hq' := hA'.dotProduct_mulVec_pos hw0
  simp only [star_trivial] at hq hq'
  rw [h', dotProduct_smul, smul_eq_mul] at hq'
  by_contra hc
  push_neg at hc
  nlinarith

lemma cquad {B : Matrix (Fin K) (Fin K) ℝ} (hB : B.IsHermitian) (w : Fin K → ℂ) :
    star w ⬝ᵥ (B.map (algebraMap ℝ ℂ) *ᵥ w) =
      (((fun i => (w i).re) ⬝ᵥ (B *ᵥ fun i => (w i).re) +
        (fun i => (w i).im) ⬝ᵥ (B *ᵥ fun i => (w i).im) : ℝ) : ℂ) := by
  have hsym : ∀ i j, B j i = B i j := fun i j => by
    have := congr_fun (congr_fun hB i) j
    simpa [Matrix.conjTranspose_apply] using this
  apply Complex.ext
  · simp [dotProduct, mulVec, Finset.mul_sum, Complex.mul_re, Finset.sum_add_distrib]
  · simp [dotProduct, mulVec, Finset.mul_sum, Complex.mul_im, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun x x_1 => (w x).im * (B x x_1 * (w x_1).re))]
    rw [add_neg_eq_zero]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym j i]; ring

lemma cquad_pos {B : Matrix (Fin K) (Fin K) ℝ} (hB : B.PosDef) {w : Fin K → ℂ} (hw : w ≠ 0) :
    0 < (fun i => (w i).re) ⬝ᵥ (B *ᵥ fun i => (w i).re) +
      (fun i => (w i).im) ⬝ᵥ (B *ᵥ fun i => (w i).im) := by
  have h1 := hB.posSemidef.dotProduct_mulVec_nonneg (fun i => (w i).re)
  have h2 := hB.posSemidef.dotProduct_mulVec_nonneg (fun i => (w i).im)
  simp only [star_trivial] at h1 h2
  by_cases hx : (fun i => (w i).re) = 0
  · have hy : (fun i => (w i).im) ≠ 0 := by
      intro hy; apply hw; funext i
      apply Complex.ext
      · simpa using congr_fun hx i
      · simpa using congr_fun hy i
    have := hB.dotProduct_mulVec_pos hy
    simp only [star_trivial] at this
    linarith
  · have := hB.dotProduct_mulVec_pos hx
    simp only [star_trivial] at this
    linarith

lemma transpose_eq_self {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian) : Aᵀ = A := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq

end Spec

theorem affine_spectrum : Claims.affine_spectrum := by
  intro K A A' hA hA' c hc
  have hdA := det_ne_zero_of_posDef hA
  set f := algebraMap ℝ ℂ
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hc
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hc
  rw [Algebra.algebraMap_eq_smul_one, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hv0
  set w := (A⁻¹).map f *ᵥ v with hw
  have hAw : A.map f *ᵥ w = v := by
    rw [hw, mulVec_mulVec, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdA),
      Matrix.map_one f (map_zero f) (map_one f), one_mulVec]
  have hw0 : w ≠ 0 := by intro h0; apply hv; rw [← hAw, h0, mulVec_zero]
  have h' : A'.map f *ᵥ w = c • (A.map f *ᵥ w) := by
    rw [hAw, hv0, hw, mulVec_mulVec, Matrix.map_mul]
  have hq := cquad hA.isHermitian w
  have hq' := cquad hA'.isHermitian w
  rw [h', dotProduct_smul, hq, smul_eq_mul] at hq'
  have hp := cquad_pos hA hw0
  have hp' := cquad_pos hA' hw0
  set q := (fun i => (w i).re) ⬝ᵥ (A *ᵥ fun i => (w i).re) +
    (fun i => (w i).im) ⬝ᵥ (A *ᵥ fun i => (w i).im)
  set q' := (fun i => (w i).re) ⬝ᵥ (A' *ᵥ fun i => (w i).re) +
    (fun i => (w i).im) ⬝ᵥ (A' *ᵥ fun i => (w i).im)
  have hc' : c = ((q' / q : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, eq_div_iff (by exact_mod_cast hp.ne'), hq']
  rw [hc']
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  exact div_pos hp' hp

theorem affine_symm_iff_comm : Claims.affine_symm_iff_comm := by
  intro K A A' hA hA'
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_posDef hA)
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, transpose_eq_self hA.isHermitian,
    transpose_eq_self hA'.isHermitian]
  constructor
  · intro h
    calc A * A' = A * (A' * A⁻¹) * A := by
          rw [Matrix.mul_assoc A (A' * A⁻¹) A, Matrix.mul_assoc A' A⁻¹ A, Matrix.nonsing_inv_mul _ hu,
            Matrix.mul_one]
      _ = A * (A⁻¹ * A') * A := by rw [h]
      _ = A' * A := by rw [← Matrix.mul_assoc A A⁻¹ A', Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  · intro h
    calc A⁻¹ * A' = A⁻¹ * (A' * A) * A⁻¹ := by
          rw [Matrix.mul_assoc A⁻¹ (A' * A) A⁻¹, Matrix.mul_assoc A' A A⁻¹, Matrix.mul_nonsing_inv _ hu,
            Matrix.mul_one]
      _ = A⁻¹ * (A * A') * A⁻¹ := by rw [h]
      _ = A' * A⁻¹ := by rw [← Matrix.mul_assoc A⁻¹ A A', Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

theorem affine_symm_posdef : Claims.affine_symm_posdef := by
  intro K A A' hA hA' hL
  have hH : (A' * A⁻¹).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hL
  rw [hH.posDef_iff_eigenvalues_pos]
  intro i
  refine rayleigh_pos hA hA' ?_ (hH.mulVec_eigenvectorBasis i)
  intro h0
  have hne : hH.eigenvectorBasis i ≠ 0 := (hH.eigenvectorBasis).orthonormal.ne_zero i
  apply hne
  ext j
  simpa using congr_fun h0 j

/-! ### (iv) location–scale -/

section LocScale
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma subdiff_affine_scale {φ : E → EReal} {x y : E}
    (hy : y ∈ TauCeti.subdifferential (innerₗ E) φ x) {c : ℝ} (hc : 0 < c) (b : E) :
    c • y + b ∈ TauCeti.subdifferential (innerₗ E)
      (fun x => (c : EReal) * φ x + ((⟪b, x⟫ : ℝ) : EReal)) x := by
  obtain ⟨hb, ht, hineq⟩ := hy
  obtain ⟨r, hr⟩ : ∃ r : ℝ, φ x = r := ⟨(φ x).toReal, (EReal.coe_toReal ht hb).symm⟩
  refine ⟨?_, ?_, fun x' => ?_⟩
  · simp only [hr, ← EReal.coe_mul, ← EReal.coe_add]; exact EReal.coe_ne_bot _
  · simp only [hr, ← EReal.coe_mul, ← EReal.coe_add]; exact EReal.coe_ne_top _
  have hx' := hineq x'
  simp only [innerₗ_apply_apply] at hx' ⊢
  rw [hr] at hx' ⊢
  generalize φ x' = t at hx' ⊢
  induction t using EReal.rec with
  | bot => exact absurd hx' (by rw [← EReal.coe_add]; exact not_le.mpr (EReal.bot_lt_coe _))
  | top =>
    rw [EReal.coe_mul_top_of_pos hc, EReal.top_add_coe]; exact le_top
  | coe t =>
    rw [← EReal.coe_add] at hx'
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add,
      EReal.coe_le_coe_iff] at *
    rw [inner_add_right, inner_smul_right]
    have h1 : ⟪b, x'⟫ = ⟪b, x⟫ + ⟪x' - x, b⟫ := by
      rw [inner_sub_left, real_inner_comm b x', real_inner_comm b x]; ring
    rw [h1]
    nlinarith

end LocScale

theorem locscale_formula : Claims.locscale_formula := by
  intro K μ Px _ _ b c Fx Qx Qx' hμ hPx h2μ h2Px hc hF hQ hRP hQ'
  set P' := Px.map fun z => b + c • z
  have hQm : Measurable Qx := hQ.1
  set Q1 : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K) := fun u => c • Qx u + b
  have hQ1 : IsGradMap μ P' Q1 := by
    obtain ⟨-, hQmap, φ, hφ⟩ := hQ
    refine ⟨(hQm.const_smul c).add_const b, ?_, _, hφ.mono fun u hu => subdiff_affine_scale hu hc b⟩
    rw [show Q1 = (fun z => b + c • z) ∘ Qx by funext u; simp [Q1, add_comm],
      ← Measure.map_map (by fun_prop) hQm, hQmap]
  have h2P' : MemLp id 2 P' := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)]
    exact (memLp_const b).add (h2Px.const_smul c)
  have hae : Qx' =ᵐ[μ] Q1 := gradMap_ae_eq hμ h2μ h2P' hQ' hQ1
  rw [← hRP.2.2.2.1] at hae
  filter_upwards [ae_of_ae_map hRP.1.aemeasurable hae, hRP.2.2.2.2.2] with z h1 h2
  rw [h1]; simp only [Q1, h2, add_comm]

/-! ### (iii) optimality iff symmetry -/

section Optimal
variable {K : ℕ}

lemma interior_support_nonempty {μ : Measure (EuclideanSpace ℝ (Fin K))} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hc : Convex ℝ μ.support) : (interior μ.support).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hfr : frontier μ.support = μ.support := by
    rw [frontier, Measure.isClosed_support.closure_eq, h, diff_empty]
  have h0 : volume μ.support = 0 := by rw [← hfr]; exact hc.addHaar_frontier volume
  have h1 : μ μ.support = 0 := hμ h0
  have h2 : μ μ.supportᶜ = 0 := Measure.measure_compl_support
  have : μ univ = 0 := by rw [← union_compl_self μ.support]; exact measure_union_null h1 h2
  simp at this

lemma mem_support_graphPlan {P : Measure (EuclideanSpace ℝ (Fin K))}
    {T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)} (hT : Continuous T)
    {z : EuclideanSpace ℝ (Fin K)} (hz : z ∈ P.support) : (z, T z) ∈ (TauCeti.graphPlan T P).support := by
  rw [Measure.mem_support_iff_forall]
  intro W hW
  obtain ⟨W', hW'W, hW'o, hzW'⟩ := mem_nhds_iff.1 hW
  have hg : Continuous fun x => (x, T x) := continuous_id.prodMk hT
  refine lt_of_lt_of_le ?_ (measure_mono hW'W)
  rw [TauCeti.graphPlan_def, Measure.map_apply hg.measurable hW'o.measurableSet]
  exact (Measure.mem_support_iff_forall z).1 hz _ ((hW'o.preimage hg).mem_nhds hzW')

lemma subdiff_toReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u : E → EReal}
    {x x' y : E} (hy : y ∈ TauCeti.subdifferential (innerₗ E) u x) (hx' : u x' ≠ ⊤) :
    (u x).toReal + ⟪x' - x, y⟫ ≤ (u x').toReal := by
  obtain ⟨hb, ht, h⟩ := hy
  have h1 := h x'
  rw [innerₗ_apply_apply] at h1
  have hb' : u x' ≠ ⊥ := by
    intro hbot
    rw [hbot, le_bot_iff, EReal.add_eq_bot_iff] at h1
    rcases h1 with h1 | h1
    · exact hb h1
    · exact EReal.coe_ne_bot _ h1
  rw [← EReal.coe_toReal ht hb, ← EReal.coe_toReal hx' hb', ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
  exact h1

/-- An affine map that is optimal from a law whose support has interior has a symmetric linear part. -/
lemma symm_of_optimal {P P' : Measure (EuclideanSpace ℝ (Fin K))} [IsProbabilityMeasure P]
    (h2 : MemLp id 2 P) (h2' : MemLp id 2 P') {O : Set (EuclideanSpace ℝ (Fin K))} (hO : IsOpen O)
    (hOne : O.Nonempty) (hOs : O ⊆ P.support) (L : Matrix (Fin K) (Fin K) ℝ) (e : EuclideanSpace ℝ (Fin K))
    (hT : TauCeti.IsKantorovichOptimalTransportMap quadCost P P' fun z => mvec L z + e) : Lᵀ = L := by
  set Lc : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K) :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin L)
  set T0 : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K) := fun z => mvec L z + e
  have hT0c : Continuous T0 := (continuous_mvec L).add continuous_const
  have hTl : HasLaw T0 P' P := hT.toHasLaw
  have hopt := (TauCeti.isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hTl
    measurable_quadCost.aemeasurable).1 hT
  have hfin : TauCeti.transportCost quadCost P P' ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (TauCeti.transportCost_le_lintegral (TauCeti.isCoupling_graphPlan hTl) _)
    change ∫⁻ z : _ × _, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) ∂(TauCeti.graphPlan T0 P) ≠ ⊤
    rw [(TauCeti.isCoupling_graphPlan hTl).lintegral_norm_sub_sq_div_two h2 h2']
    exact ENNReal.ofReal_ne_top
  obtain ⟨u, -, -, -, -, hsupp⟩ := hopt.exists_support_subset_subdifferential hfin
  have hsub : ∀ y ∈ O, T0 y ∈ TauCeti.subdifferential (innerₗ _) u y := fun y hy =>
    hsupp (mem_support_graphPlan hT0c (hOs hy))
  have hfinu : ∀ y ∈ O, u y ≠ ⊤ := fun y hy => (hsub y hy).2.1
  set g := fun z => (u z).toReal
  have hderiv : ∀ y ∈ O, HasFDerivAt g (innerSL ℝ (T0 y)) y := by
    intro y hy
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.IsBigO.trans_isLittleO (g := fun h => ‖h‖ ^ 2) ?_
      (Asymptotics.isLittleO_norm_pow_id one_lt_two)
    refine Asymptotics.IsBigO.of_bound ‖Lc‖ ?_
    have hev : ∀ᶠ h in 𝓝 (0 : EuclideanSpace ℝ (Fin K)), y + h ∈ O := by
      have : Tendsto (fun h => y + h) (𝓝 0) (𝓝 y) := by
        simpa using (tendsto_const_nhds (x := y)).add (tendsto_id (x := 𝓝 (0 : EuclideanSpace ℝ (Fin K))))
      exact this (hO.mem_nhds hy)
    filter_upwards [hev] with h hh
    have h1 := subdiff_toReal (hsub y hy) (hfinu (y + h) hh)
    have h2 := subdiff_toReal (hsub (y + h) hh) (hfinu y hy)
    rw [add_sub_cancel_left] at h1
    have hyh : y - (y + h) = -h := by abel
    rw [hyh] at h2
    have hT0 : T0 (y + h) = T0 y + mvec L h := by simp only [T0, mvec_add]; abel
    rw [hT0, inner_add_right, inner_neg_left, inner_neg_left] at h2
    have hb : ⟪h, mvec L h⟫ ≤ ‖Lc‖ * ‖h‖ ^ 2 := by
      calc ⟪h, mvec L h⟫ ≤ ‖h‖ * ‖Lc h‖ := real_inner_le_norm _ _
        _ ≤ ‖h‖ * (‖Lc‖ * ‖h‖) := by gcongr; exact Lc.le_opNorm h
        _ = ‖Lc‖ * ‖h‖ ^ 2 := by ring
    have hnn : 0 ≤ ‖Lc‖ * ‖h‖ ^ 2 := by positivity
    have hc := real_inner_comm h (T0 y)
    rw [innerSL_apply_apply, Real.norm_eq_abs, norm_pow, norm_norm, abs_le]
    simp only [g]
    constructor <;> nlinarith
  obtain ⟨x0, hx0⟩ := hOne
  have hf : ∀ᶠ y in 𝓝 x0, HasFDerivAt g (innerSL ℝ (T0 y)) y :=
    Filter.eventually_of_mem (hO.mem_nhds hx0) hderiv
  have hx : HasFDerivAt (fun y => innerSL ℝ (T0 y)) ((innerSL ℝ).comp Lc) x0 :=
    (innerSL ℝ).hasFDerivAt.comp x0 (Lc.hasFDerivAt.add_const e)
  have hsym := second_derivative_symmetric_of_eventually hf hx
  ext i j
  have := hsym (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at this
  have hLc : ∀ x, Lc x = mvec L x := fun x => rfl
  rw [hLc, hLc, ← real_inner_comm (mvec L (EuclideanSpace.single j 1)) (EuclideanSpace.single i 1),
    ← real_inner_comm (mvec L (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1),
    inner_mvec, inner_mvec] at this
  simpa [Lc, mulVec, dotProduct, Pi.single_apply] using this

end Optimal

theorem affine_optimal_iff : Claims.affine_optimal_iff := by
  intro K μ _ b b' A A' Fx Qx' hμ h2 hconv hA hA' hF hQ
  have hdA := det_ne_zero_of_posDef hA
  have haff : affineMap b A = fun z => mvec A z + b := by funext z; simp [affineMap, add_comm]
  have haff' : affineMap b' A' = fun z => mvec A' z + b' := by funext z; simp [affineMap, add_comm]
  set L := A' * A⁻¹
  set e := b' - mvec L b
  set Px := μ.map (affineMap b A) with hPx
  have h2Px : MemLp id 2 Px := by rw [hPx, haff]; exact memLp_map_affine h2 A b
  have h2Px' : MemLp id 2 (μ.map (affineMap b' A')) := by rw [haff']; exact memLp_map_affine h2 A' b'
  have hform := affine_formula K μ b b' A A' Fx Qx' hμ h2 hA hA' hF hQ
  have hform' : (fun z => Qx' (Fx z)) =ᵐ[Px] fun z => mvec L z + e := by
    filter_upwards [hform] with z hz
    rw [hz, mvec_sub]; simp only [e]; abel
  have hmapT0 : Px.map (fun z => mvec L z + e) = μ.map (affineMap b' A') := by
    rw [hPx, Measure.map_map ((measurable_mvec L).add_const e) (by rw [haff]; fun_prop)]
    congr 1
    funext u
    simp only [Function.comp, affineMap, e, mvec_add, mvec_sub, L, mvec_mul, mvec_inv_mul hdA]
    abel
  constructor
  · intro hT
    have hT0 := hT.congr hform'.symm
    -- an open set inside `supp P_x`
    obtain ⟨u0, hu0⟩ := interior_support_nonempty hμ hconv
    set O := (fun z => mvec A⁻¹ (z - b)) ⁻¹' interior μ.support
    have hOo : IsOpen O :=
      isOpen_interior.preimage ((continuous_mvec _).comp (continuous_id.sub continuous_const))
    have hOne : O.Nonempty := ⟨mvec A u0 + b, by simp [O, mvec_inv_mul hdA, hu0]⟩
    have hOs : O ⊆ Px.support := by
      intro z hz
      rw [Measure.mem_support_iff_forall]
      intro W hW
      obtain ⟨W', hW'W, hW'o, hzW'⟩ := mem_nhds_iff.1 hW
      have hc : Continuous (affineMap b A) := by rw [haff]; exact (continuous_mvec A).add continuous_const
      refine lt_of_lt_of_le ?_ (measure_mono hW'W)
      rw [hPx, Measure.map_apply hc.measurable hW'o.measurableSet]
      have hzu : affineMap b A (mvec A⁻¹ (z - b)) = z := by
        simp [affineMap, mvec_mul_inv hdA]
      refine (Measure.mem_support_iff_forall _).1 (interior_subset hz) _
        ((hW'o.preimage hc).mem_nhds ?_)
      simp only [mem_preimage, hzu]; exact hzW'
    exact symm_of_optimal h2Px h2Px' hOo hOne hOs L e hT0
  · intro hL
    have hLpd := affine_symm_posdef K A A' hA hA' hL
    have hg := isGradMap_affine Px hLpd.posSemidef e
    rw [hmapT0] at hg
    exact (hg.isOptimal h2Px h2Px').congr hform'

end StatFormal.OTFD.Wave8c
