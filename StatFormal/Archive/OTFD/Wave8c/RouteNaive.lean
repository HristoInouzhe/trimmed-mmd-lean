import StatFormal.Archive.OTFD.Wave8c.RouteTransfer
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Route: B `lem:naive-law`

* `ω_{K−1} = K·vol(B) = 2π^{K/2}/Γ(K/2)` is Mathlib's sphere mass (`toSphere_apply_univ`, `volume_ball`).
* Polar coordinates (`measurePreserving_homeomorphUnitSphereProd`): `Rθ` has density
  `1{0<‖x‖≤1}/(ω‖x‖^{K−1})`; a linear image has density `|det L| f(Lu)`, with `‖L u‖ = ‖u‖_{M}`, `|det L| = √det M`.
* (a) and (c) follow from the density, which depends on `M` only and is `G`-invariant (`|det G| = 1`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Matrix Metric
open scoped InnerProductSpace ENNReal RealInnerProductSpace

namespace StatFormal.OTFD.Wave8c

variable {K : ℕ}

/-! ### Algebra of `‖·‖_M` -/

lemma norm_sq_eq_dot (v : EuclideanSpace ℝ (Fin K)) : ‖v‖ ^ 2 = WithLp.ofLp v ⬝ᵥ WithLp.ofLp v := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]; simp

lemma mnorm_eq_norm {M L : Matrix (Fin K) (Fin K) ℝ} (hL : Lᵀ * L = M) (u : EuclideanSpace ℝ (Fin K)) :
    mnorm M u = ‖mvec L u‖ := by
  rw [mnorm, ← hL, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, ← Real.sqrt_sq (norm_nonneg _),
    norm_sq_eq_dot]
  simp [mvec, Matrix.toLpLin_apply]

lemma mnorm_nonneg (M : Matrix (Fin K) (Fin K) ℝ) (u : EuclideanSpace ℝ (Fin K)) : 0 ≤ mnorm M u :=
  Real.sqrt_nonneg _

lemma det_L_ne_zero {M L : Matrix (Fin K) (Fin K) ℝ} (hM : M.PosDef) (hL : Lᵀ * L = M) : L.det ≠ 0 := by
  intro h
  have := hM.det_pos
  rw [← hL, det_mul, det_transpose, h, mul_zero] at this
  exact lt_irrefl _ this

lemma abs_det_L {M L : Matrix (Fin K) (Fin K) ℝ} (hL : Lᵀ * L = M) : |L.det| = Real.sqrt M.det := by
  rw [← hL, det_mul, det_transpose, ← sq, Real.sqrt_sq_eq_abs]

lemma mnorm_mvec_G {M G : Matrix (Fin K) (Fin K) ℝ} (hG : Gᵀ * M * G = M) (u : EuclideanSpace ℝ (Fin K)) :
    mnorm M (mvec G u) = mnorm M u := by
  unfold mnorm
  congr 1
  conv_rhs => rw [← hG]
  simp [mvec, Matrix.toLpLin_apply, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

lemma det_G_abs {M G : Matrix (Fin K) (Fin K) ℝ} (hM : M.PosDef) (hG : Gᵀ * M * G = M) : |G.det| = 1 := by
  have h := congr_arg Matrix.det hG
  rw [det_mul, det_mul, det_transpose] at h
  have hM0 := hM.det_pos.ne'
  have : G.det ^ 2 = 1 := by
    have : G.det * G.det * M.det = 1 * M.det := by linarith [h]
    have := mul_right_cancel₀ hM0 this
    nlinarith [this]
  have h2 : |G.det| ^ 2 = 1 := by rw [sq_abs]; exact this
  nlinarith [abs_nonneg G.det, sq_nonneg (|G.det| - 1)]

/-! ### `ω_{K−1}` -/

lemma omega_pos (hK : 1 ≤ K) : 0 < omega K := by
  unfold omega
  have : 0 < (K : ℝ) / 2 := by have : (1 : ℝ) ≤ K := by exact_mod_cast hK
                               linarith
  exact div_pos (mul_pos two_pos (Real.rpow_pos_of_pos Real.pi_pos _)) (Real.Gamma_pos_of_pos this)

theorem omega_sphere : Claims.omega_sphere := by
  intro K hK
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  rw [Measure.toSphere_apply_univ, EuclideanSpace.volume_ball, finrank_euclideanSpace_fin]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  have hK0 : (K : ℝ) / 2 ≠ 0 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    positivity
  have hG : Real.Gamma ((K : ℝ) / 2 + 1) = (K : ℝ) / 2 * Real.Gamma ((K : ℝ) / 2) := Real.Gamma_add_one hK0
  have hsq : Real.sqrt Real.pi ^ K = Real.pi ^ ((K : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]; ring_nf
  have hGpos : 0 < Real.Gamma ((K : ℝ) / 2) := Real.Gamma_pos_of_pos (by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hG, hsq, omega]
  congr 1
  field_simp

/-! ### Polar coordinates and the law of `Rθ` -/

lemma polar_lintegral (hK : 1 ≤ K) (g : EuclideanSpace ℝ (Fin K) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x, g x = ∫⁻ θ, (∫⁻ r in Ioi (0 : ℝ), g (r • (θ : EuclideanSpace ℝ (Fin K))) *
      ENNReal.ofReal (r ^ (K - 1)) ∂volume) ∂(volume : Measure (EuclideanSpace ℝ (Fin K))).toSphere := by
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ (Fin K)) := inferInstance
  set h := homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin K))
  have h1 : ∫⁻ x, g x ∂(volume : Measure (EuclideanSpace ℝ (Fin K))) =
      ∫⁻ x : ({(0 : EuclideanSpace ℝ (Fin K))}ᶜ : Set (EuclideanSpace ℝ (Fin K))), g x ∂(volume.comap Subtype.val) := by
    rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
  have hG0 : Measurable fun p : sphere (0 : EuclideanSpace ℝ (Fin K)) 1 × Ioi (0 : ℝ) => p.2.1 • (p.1 : EuclideanSpace ℝ (Fin K)) := by fun_prop
  have hG : Measurable fun p : sphere (0 : EuclideanSpace ℝ (Fin K)) 1 × Ioi (0 : ℝ) => g (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin K))) := hg.comp hG0
  have h2 := (Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure (EuclideanSpace ℝ (Fin K)))).lintegral_comp_emb
      h.measurableEmbedding (fun p => g (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin K))))
  have h3 : ∀ a : ({(0 : EuclideanSpace ℝ (Fin K))}ᶜ : Set (EuclideanSpace ℝ (Fin K))), g a = g ((h a).2.1 • ((h a).1 : EuclideanSpace ℝ (Fin K))) := by
    intro a
    conv_lhs => rw [← h.symm_apply_apply a]
    rw [homeomorphUnitSphereProd_symm_apply_coe]
  rw [h1, lintegral_congr (fun a => h3 a), h2, lintegral_prod _ hG.aemeasurable]
  congr 1; funext θ
  rw [Measure.volumeIoiPow, finrank_euclideanSpace_fin]
  have hd : Measurable fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ (K - 1)) :=
    (measurable_subtype_coe.pow_const _).ennreal_ofReal
  have hm : Measurable fun y : Ioi (0 : ℝ) => g (y.1 • (θ : EuclideanSpace ℝ (Fin K))) :=
    hg.comp (measurable_subtype_coe.smul_const _)
  change ∫⁻ y : Ioi (0 : ℝ), g (y.1 • (θ : EuclideanSpace ℝ (Fin K))) ∂_ = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hm,
    ← lintegral_subtype_comap measurableSet_Ioi
      (fun r => g (r • (θ : EuclideanSpace ℝ (Fin K))) * ENNReal.ofReal (r ^ (K - 1)))]
  congr 1; funext r; simp [mul_comm]

instance : IsProbabilityMeasure unifRadius := ⟨by simp [unifRadius]⟩

instance : SFinite (sphereUnif K) := by unfold sphereUnif; infer_instance

/-- The density of `Rθ`. -/
def rthetaDensity (K : ℕ) (x : EuclideanSpace ℝ (Fin K)) : ℝ≥0∞ :=
  Set.indicator {x | 0 < ‖x‖ ∧ ‖x‖ ≤ 1} (fun x => ENNReal.ofReal (1 / (omega K * ‖x‖ ^ (K - 1)))) x

lemma measurable_rthetaDensity : Measurable (rthetaDensity K) := by
  refine Measurable.indicator ?_ ?_
  · exact (measurable_const.div ((measurable_const.mul (measurable_norm.pow_const _)))).ennreal_ofReal
  · exact (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_le measurable_norm measurable_const)

lemma sphereUnif_lintegral (F : EuclideanSpace ℝ (Fin K) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ θ, F θ ∂sphereUnif K =
      ((volume : Measure (EuclideanSpace ℝ (Fin K))).toSphere univ)⁻¹ *
        ∫⁻ θ, F (θ : EuclideanSpace ℝ (Fin K)) ∂(volume : Measure (EuclideanSpace ℝ (Fin K))).toSphere := by
  rw [sphereUnif, lintegral_smul_measure, lintegral_map hF measurable_subtype_coe, smul_eq_mul]

lemma rtheta_law (hK : 1 ≤ K) :
    (unifRadius.prod (sphereUnif K)).map (fun p => p.1 • p.2) = volume.withDensity (rthetaDensity K) := by
  set E := EuclideanSpace ℝ (Fin K)
  have hω := omega_pos hK
  have hmeas : Measurable fun p : ℝ × E => p.1 • p.2 := measurable_fst.smul measurable_snd
  ext S hS
  have hpre : MeasurableSet ((fun p : ℝ × E => p.1 • p.2) ⁻¹' S) := hmeas hS
  rw [Measure.map_apply hmeas hS, Measure.prod_apply_symm hpre,
    sphereUnif_lintegral _ (measurable_measure_prodMk_right hpre), omega_sphere K hK,
    withDensity_apply _ hS, ← lintegral_indicator hS,
    polar_lintegral hK _ (measurable_rthetaDensity.indicator hS)]
  rw [← ENNReal.ofReal_inv_of_pos hω, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1; funext θ
  have hθ : ‖(θ : E)‖ = 1 := by simp
  set T := (fun r : ℝ => r • (θ : E)) ⁻¹' S
  have hT : MeasurableSet T := (measurable_id.smul_const _) hS
  have hTeq : (fun x : ℝ => (x, (θ : E))) ⁻¹' ((fun p : ℝ × E => p.1 • p.2) ⁻¹' S) = T := rfl
  rw [hTeq, unifRadius, Measure.restrict_apply hT]
  have hpt : EqOn (fun r : ℝ => S.indicator (rthetaDensity K) (r • (θ : E)) * ENNReal.ofReal (r ^ (K - 1)))
      ((T ∩ Iic 1).indicator fun _ => ENNReal.ofReal (omega K)⁻¹) (Ioi 0) := by
    intro r hr
    dsimp only
    have hr0 : 0 < r := hr
    have hn : ‖r • (θ : E)‖ = r := by rw [norm_smul, hθ, mul_one, Real.norm_of_nonneg hr0.le]
    by_cases hS' : r • (θ : E) ∈ S
    · by_cases h1 : r ≤ 1
      · have hpow : 0 < r ^ (K - 1) := pow_pos hr0 _
        rw [indicator_of_mem hS', indicator_of_mem (show r ∈ T ∩ Iic 1 from ⟨hS', h1⟩), rthetaDensity,
          indicator_of_mem (show r • (θ : E) ∈ {x : E | 0 < ‖x‖ ∧ ‖x‖ ≤ 1} from
            ⟨by rw [hn]; exact hr0, by rw [hn]; exact h1⟩), hn,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
      · rw [indicator_of_notMem (show r ∉ T ∩ Iic 1 from fun h => h1 h.2), indicator_of_mem hS',
          rthetaDensity, indicator_of_notMem (by rintro ⟨-, hm⟩; rw [hn] at hm; exact h1 hm), zero_mul]
    · rw [indicator_of_notMem hS', indicator_of_notMem (show r ∉ T ∩ Iic 1 from fun h => hS' h.1), zero_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_indicator_const (hT.inter measurableSet_Iic),
    Measure.restrict_apply (hT.inter measurableSet_Iic)]
  congr 2
  ext r; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]; tauto

/-! ### Linear images of densities -/

lemma withDensity_map_mvec {P : Matrix (Fin K) (Fin K) ℝ} (hP : P.det ≠ 0)
    {d : EuclideanSpace ℝ (Fin K) → ℝ≥0∞} (hd : Measurable d) :
    (volume.withDensity d).map (mvec P) =
      volume.withDensity (fun y => ENNReal.ofReal |(P.det)⁻¹| * d (mvec P⁻¹ y)) := by
  ext S hS
  rw [Measure.map_apply (measurable_mvec P) hS, withDensity_apply _ (measurable_mvec P hS),
    withDensity_apply _ hS]
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin K))).map (mvec P) =
      ENNReal.ofReal |(P.det)⁻¹| • volume := by
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar volume (f := Matrix.toEuclideanLin P)
      (by simpa using hP)
    simpa using this
  set F := S.indicator (fun y => d (mvec P⁻¹ y))
  have hF : Measurable F := (hd.comp (measurable_mvec _)).indicator hS
  have key : ∫⁻ x, F (mvec P x) = ENNReal.ofReal |(P.det)⁻¹| * ∫⁻ y, F y := by
    rw [← lintegral_map hF (measurable_mvec P), hvol, lintegral_smul_measure, smul_eq_mul]
  have hL : ∫⁻ x in mvec P ⁻¹' S, d x = ∫⁻ x, F (mvec P x) := by
    rw [← lintegral_indicator (measurable_mvec P hS)]
    congr 1; funext x
    by_cases hx : mvec P x ∈ S <;> simp [F, hx, mvec_inv_mul hP]
  rw [hL, key, ← lintegral_indicator hS, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1; funext y; simp only [F, Set.indicator]; split_ifs <;> simp

lemma sphereUnif_zero : sphereUnif 0 = 0 := by
  have : (volume : Measure (EuclideanSpace ℝ (Fin 0))).toSphere = 0 :=
    (Measure.toSphere_eq_zero_iff_finrank _).2 (by simp)
  simp [sphereUnif, this]

lemma naiveLaw_zero (L : Matrix (Fin 0) (Fin 0) ℝ) : naiveLaw L = 0 := by
  simp [naiveLaw, sphereUnif_zero]

lemma naiveDensity_congr (M : Matrix (Fin K) (Fin K) ℝ) {a b : EuclideanSpace ℝ (Fin K)}
    (h : mnorm M a = mnorm M b) : naiveDensity M a = naiveDensity M b := by
  simp only [naiveDensity, Set.indicator, mem_setOf_eq, h]

lemma measurable_naiveDensity (M L : Matrix (Fin K) (Fin K) ℝ) (hL : Lᵀ * L = M) :
    Measurable (naiveDensity M) := by
  have hm : Measurable (mnorm M) := by
    rw [show mnorm M = fun u => ‖mvec L u‖ from funext (mnorm_eq_norm hL)]
    exact (continuous_norm.comp (continuous_mvec L)).measurable
  refine Measurable.indicator ?_ ?_
  · exact (measurable_const.div ((measurable_const.mul (hm.pow_const _)))).ennreal_ofReal
  · exact (measurableSet_lt measurable_const hm).inter (measurableSet_le hm measurable_const)

theorem naiveLaw_eq {M L : Matrix (Fin K) (Fin K) ℝ} (hK : 1 ≤ K) (hM : M.PosDef) (hL : Lᵀ * L = M) :
    naiveLaw L = volume.withDensity (naiveDensity M) := by
  have hdL := det_L_ne_zero hM hL
  have hu : IsUnit L.det := isUnit_iff_ne_zero.mpr hdL
  have hdLi : (L⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hdL
  rw [naiveLaw, show (fun p : ℝ × EuclideanSpace ℝ (Fin K) => mvec L⁻¹ (p.1 • p.2)) =
      mvec L⁻¹ ∘ fun p => p.1 • p.2 from rfl,
    ← Measure.map_map (g := mvec L⁻¹) (f := fun p : ℝ × EuclideanSpace ℝ (Fin K) => p.1 • p.2)
      (measurable_mvec _) (measurable_fst.smul measurable_snd), rtheta_law hK,
    withDensity_map_mvec hdLi measurable_rthetaDensity, Matrix.nonsing_inv_nonsing_inv _ hu,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_inv, abs_det_L hL]
  congr 1; funext y
  rw [rthetaDensity, naiveDensity]
  by_cases h : 0 < mnorm M y ∧ mnorm M y ≤ 1
  · rw [indicator_of_mem (show mvec L y ∈ _ from by
        show 0 < ‖mvec L y‖ ∧ ‖mvec L y‖ ≤ 1; rwa [← mnorm_eq_norm hL]),
      indicator_of_mem (show y ∈ {v | 0 < mnorm M v ∧ mnorm M v ≤ 1} from h), ← mnorm_eq_norm hL,
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 1; ring
  · rw [indicator_of_notMem (show mvec L y ∉ _ from by
        show ¬(0 < ‖mvec L y‖ ∧ ‖mvec L y‖ ≤ 1); rwa [← mnorm_eq_norm hL]),
      indicator_of_notMem (show y ∉ {v | 0 < mnorm M v ∧ mnorm M v ≤ 1} from h), mul_zero]

theorem naive_density : Claims.naive_density := by
  intro K M L hK hM hL
  rw [naiveLaw_eq hK hM hL]
  exact ⟨withDensity_absolutelyContinuous _ _, rfl⟩

theorem naive_indep : Claims.naive_indep := by
  intro K M L L' hM hL hL'
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · rw [naiveLaw_zero, naiveLaw_zero]
  · rw [naiveLaw_eq hK hM hL, naiveLaw_eq hK hM hL']

theorem naive_invariant : Claims.naive_invariant := by
  intro K M L G hM hL hG
  refine ⟨?_, mnorm_mvec_G hG⟩
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · rw [naiveLaw_zero, Measure.map_zero]
  have hdG : |G.det| = 1 := det_G_abs hM hG
  have hG0 : G.det ≠ 0 := by intro h; rw [h, abs_zero] at hdG; exact zero_ne_one hdG
  rw [naiveLaw_eq hK hM hL, withDensity_map_mvec hG0 (measurable_naiveDensity M L hL), abs_inv, hdG,
    inv_one, ENNReal.ofReal_one]
  congr 1; funext y
  rw [one_mul]
  apply naiveDensity_congr
  rw [← mnorm_mvec_G hG (mvec G⁻¹ y), mvec_mul_inv hG0]

theorem naive_norm : Claims.naive_norm := by
  intro K M L hM hL r θ hr hθ
  rw [mnorm_eq_norm hL, mvec_mul_inv (det_L_ne_zero hM hL), norm_smul, hθ, mul_one, Real.norm_of_nonneg hr]

theorem naive_orth_iff : Claims.naive_orth_iff := by
  intro K M L G hM hL
  have hu : IsUnit L.det := isUnit_iff_ne_zero.mpr (det_L_ne_zero hM hL)
  have huT : IsUnit Lᵀ.det := by rwa [det_transpose]
  subst hL
  constructor
  · intro h
    refine ⟨L * G * L⁻¹, ?_, ?_⟩
    · rw [Matrix.mem_orthogonalGroup_iff', Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_nonsing_inv]
      calc Lᵀ⁻¹ * (Gᵀ * Lᵀ) * (L * G * L⁻¹) = Lᵀ⁻¹ * (Gᵀ * (Lᵀ * L) * G) * L⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = Lᵀ⁻¹ * (Lᵀ * L) * L⁻¹ := by rw [h]
        _ = 1 := by
            rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ huT, Matrix.one_mul, Matrix.mul_nonsing_inv _ hu]
    · simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left (h := hu)]
  · rintro ⟨O, hO, rfl⟩
    rw [Matrix.mem_orthogonalGroup_iff'] at hO
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
    calc Lᵀ * (Oᵀ * Lᵀ⁻¹) * (Lᵀ * L) * (L⁻¹ * O * L) = Lᵀ * (Oᵀ * (Lᵀ⁻¹ * Lᵀ) * (L * L⁻¹) * O) * L := by
          simp only [Matrix.mul_assoc]
      _ = Lᵀ * L := by
          rw [Matrix.nonsing_inv_mul _ huT, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.mul_one, hO,
            Matrix.mul_one]

/-! ### (b): the radius and the calibration -/

lemma sphereUnif_univ (hK : 1 ≤ K) : sphereUnif K univ = 1 := by
  have hω := omega_pos hK
  rw [sphereUnif, Measure.smul_apply, Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    preimage_univ, smul_eq_mul, omega_sphere K hK]
  exact ENNReal.inv_mul_cancel (by simpa using hω) ENNReal.ofReal_ne_top

lemma sphereUnif_prob (hK : 1 ≤ K) : IsProbabilityMeasure (sphereUnif K) := ⟨sphereUnif_univ hK⟩

lemma sphereUnif_ae_norm : ∀ᵐ θ ∂sphereUnif K, ‖θ‖ = 1 := by
  unfold sphereUnif
  refine Measure.ae_smul_measure ?_ _
  rw [ae_map_iff measurable_subtype_coe.aemeasurable
    (measurableSet_eq_fun measurable_norm measurable_const)]
  exact Eventually.of_forall fun θ => by simp

lemma measurable_mnorm {M L : Matrix (Fin K) (Fin K) ℝ} (hL : Lᵀ * L = M) : Measurable (mnorm M) := by
  rw [show mnorm M = fun u => ‖mvec L u‖ from funext (mnorm_eq_norm hL)]
  exact (continuous_norm.comp (continuous_mvec L)).measurable

lemma continuous_mnorm {M L : Matrix (Fin K) (Fin K) ℝ} (hL : Lᵀ * L = M) : Continuous (mnorm M) := by
  rw [show mnorm M = fun u => ‖mvec L u‖ from funext (mnorm_eq_norm hL)]
  exact continuous_norm.comp (continuous_mvec L)

theorem naive_norm_law : Claims.naive_norm_law := by
  intro K M L hK hM hL
  haveI := sphereUnif_prob hK
  have hdL := det_L_ne_zero hM hL
  have hsm : Measurable fun p : ℝ × EuclideanSpace ℝ (Fin K) => mvec L⁻¹ (p.1 • p.2) :=
    (measurable_mvec _).comp (measurable_fst.smul measurable_snd)
  rw [naiveLaw, Measure.map_map (measurable_mnorm hL) hsm]
  have hae : (mnorm M ∘ fun p : ℝ × EuclideanSpace ℝ (Fin K) => mvec L⁻¹ (p.1 • p.2))
      =ᵐ[unifRadius.prod (sphereUnif K)] Prod.fst := by
    have h1 : ∀ᵐ p ∂(unifRadius.prod (sphereUnif K)), p.1 ∈ Ioc (0 : ℝ) 1 :=
      Measure.quasiMeasurePreserving_fst.ae (by unfold unifRadius; exact ae_restrict_mem measurableSet_Ioc)
    have h2 : ∀ᵐ p ∂(unifRadius.prod (sphereUnif K)), ‖p.2‖ = 1 :=
      Measure.quasiMeasurePreserving_snd.ae sphereUnif_ae_norm
    filter_upwards [h1, h2] with p hp1 hp2
    simp only [Function.comp, mnorm_eq_norm hL, mvec_mul_inv hdL, norm_smul, hp2, mul_one,
      Real.norm_of_nonneg hp1.1.le]
  rw [Measure.map_congr hae, Measure.map_fst_prod, measure_univ, one_smul]

lemma naiveLaw_ball {M L : Matrix (Fin K) (Fin K) ℝ} (hK : 1 ≤ K) (hM : M.PosDef) (hL : Lᵀ * L = M)
    {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) : naiveLaw L {u | mnorm M u ≤ τ} = ENNReal.ofReal τ := by
  have h := naive_norm_law K M L hK hM hL
  have : (naiveLaw L).map (mnorm M) (Iic τ) = unifRadius (Iic τ) := by rw [h]
  rw [Measure.map_apply (measurable_mnorm hL) measurableSet_Iic] at this
  rw [show {u | mnorm M u ≤ τ} = mnorm M ⁻¹' Iic τ from rfl, this, unifRadius,
    Measure.restrict_apply measurableSet_Iic]
  have : Iic τ ∩ Ioc 0 1 = Ioc 0 τ := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioc]; constructor
    · rintro ⟨h, h', -⟩; exact ⟨h', h⟩
    · rintro ⟨h', h⟩; exact ⟨h, h', h.trans h1⟩
  rw [this, Real.volume_Ioc, sub_zero]

theorem naive_calibration : Claims.naive_calibration := by
  intro K M L hK hM hL
  haveI := sphereUnif_prob hK
  have hdL := det_L_ne_zero hM hL
  have hω := omega_pos hK
  haveI : IsProbabilityMeasure (naiveLaw L) := by unfold naiveLaw; infer_instance
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hsupp : (naiveLaw L).support = {u | mnorm M u ≤ 1} := by
    apply subset_antisymm
    · refine Measure.support_subset_of_isClosed
        (isClosed_le (continuous_mnorm hL) continuous_const) ?_
      have hmeas : MeasurableSet {u | mnorm M u ≤ 1} := measurable_mnorm hL measurableSet_Iic
      rw [mem_ae_iff, measure_compl hmeas (measure_ne_top _ _), naiveLaw_ball hK hM hL zero_le_one le_rfl,
        measure_univ, ENNReal.ofReal_one, tsub_self]
    · intro u hu
      rw [Measure.mem_support_iff_forall]
      intro U hU
      obtain ⟨U', hU'U, hU'o, huU'⟩ := _root_.mem_nhds_iff.1 hU
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU'o u huU'
      set V := U' ∩ {v | mnorm M v < 1}
      have hVo : IsOpen V := hU'o.inter (isOpen_lt (continuous_mnorm hL) continuous_const)
      -- a point `t • u`, `t < 1`, of `V`
      set s := min (ε / (2 * (‖u‖ + 1))) (1 / 2)
      have hs0 : 0 < s := lt_min (by positivity) (by norm_num)
      have hs1 : s ≤ 1 / 2 := min_le_right _ _
      have hsε : s ≤ ε / (2 * (‖u‖ + 1)) := min_le_left _ _
      have hVne : V.Nonempty := by
        refine ⟨(1 - s) • u, hball ?_, ?_⟩
        · rw [Metric.mem_ball, dist_eq_norm, show (1 - s) • u - u = -(s • u) by
            rw [sub_smul, one_smul]; abel, norm_neg, norm_smul, Real.norm_of_nonneg hs0.le]
          calc s * ‖u‖ ≤ ε / (2 * (‖u‖ + 1)) * ‖u‖ := by gcongr
            _ < ε := by
              rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg u]
        · show mnorm M ((1 - s) • u) < 1
          rw [mnorm_eq_norm hL, mvec_smul, norm_smul, ← mnorm_eq_norm hL,
            Real.norm_of_nonneg (by linarith)]
          have : mnorm M u ≤ 1 := hu
          nlinarith [mnorm_nonneg M u]
      have hVpos : 0 < volume (V \ {0}) := by
        rw [measure_diff_null (measure_singleton 0)]; exact hVo.measure_pos volume hVne
      set c := ENNReal.ofReal (Real.sqrt M.det / omega K)
      have hc : c ≠ 0 := by
        simp only [c, ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact div_pos (Real.sqrt_pos.2 hM.det_pos) hω
      have hlow : ∀ x ∈ V \ {0}, c ≤ naiveDensity M x := by
        rintro x ⟨⟨-, hx1⟩, hx0⟩
        have hx1 : mnorm M x < 1 := hx1
        have hxpos : 0 < mnorm M x := by
          rw [mnorm_eq_norm hL, norm_pos_iff]
          intro h; apply hx0
          rw [mem_singleton_iff, ← mvec_inv_mul hdL x, h]
          exact map_zero (Matrix.toEuclideanLin L⁻¹)
        rw [naiveDensity, indicator_of_mem (show x ∈ {v | 0 < mnorm M v ∧ mnorm M v ≤ 1} from
          ⟨hxpos, hx1.le⟩)]
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (mul_pos hω (pow_pos hxpos _))
        exact mul_le_of_le_one_right hω.le (pow_le_one₀ hxpos.le hx1.le)
      have hVm : MeasurableSet V := hVo.measurableSet
      calc 0 < c * volume (V \ {0}) := ENNReal.mul_pos hc hVpos.ne'
        _ = ∫⁻ x in V \ {0}, c := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ x in V \ {0}, naiveDensity M x := setLIntegral_mono (measurable_naiveDensity M L hL) hlow
        _ ≤ ∫⁻ x in V, naiveDensity M x := lintegral_mono_set diff_subset
        _ = naiveLaw L V := by rw [naiveLaw_eq hK hM hL, withDensity_apply _ hVm]
        _ ≤ naiveLaw L U := measure_mono (inter_subset_left.trans hU'U)
  exact ⟨fun u hu => ⟨mnorm_nonneg M u, by rw [hsupp] at hu; exact hu⟩,
    fun τ h0 h1 => naiveLaw_ball hK hM hL h0 h1, hsupp⟩

/-! ### (d), `K = 1` -/

lemma omega_one : omega 1 = 2 := by
  rw [omega, Nat.cast_one, Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow]
  field_simp

theorem naive_one_dim : Claims.naive_one_dim := by
  intro M L hM hL
  set m := M 0 0 with hmdef
  have hm : 0 < m := hM.diag_pos
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hdet : M.det = m := Matrix.det_unique M
  have hmn : ∀ u : EuclideanSpace ℝ (Fin 1), mnorm M u = Real.sqrt m * |u 0| := by
    intro u
    rw [mnorm, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hm.le]
    congr 1
    simp [dotProduct, mulVec, hmdef]; ring
  rw [naiveLaw_eq le_rfl hM hL]
  have he : MeasurePreserving (fun u : EuclideanSpace ℝ (Fin 1) => u 0) volume volume :=
    (volume_preserving_funUnique (Fin 1) ℝ).comp (PiLp.volume_preserving_ofLp (Fin 1))
  set g : ℝ → ℝ≥0∞ := Set.indicator {t | 0 < Real.sqrt m * |t| ∧ Real.sqrt m * |t| ≤ 1}
    (fun _ => ENNReal.ofReal (Real.sqrt m / 2))
  have hg : Measurable g := by
    refine Measurable.indicator measurable_const ?_
    have hc : Measurable fun t : ℝ => Real.sqrt m * |t| := measurable_const.mul continuous_abs.measurable
    exact (measurableSet_lt measurable_const hc).inter (measurableSet_le hc measurable_const)
  have hnd : ∀ u, naiveDensity M u = g (u 0) := by
    intro u
    simp only [naiveDensity, g, Set.indicator, mem_setOf_eq, hmn, hdet, omega_one, Nat.sub_self, pow_zero,
      mul_one]
  ext S hS
  have hpre : MeasurableSet ((fun u : EuclideanSpace ℝ (Fin 1) => u 0) ⁻¹' S) := he.measurable hS
  rw [Measure.map_apply he.measurable hS, withDensity_apply _ hpre, Measure.smul_apply,
    Measure.restrict_apply hS, smul_eq_mul, ← lintegral_indicator hpre]
  have hcomp : ∀ u, ((fun u : EuclideanSpace ℝ (Fin 1) => u 0) ⁻¹' S).indicator (naiveDensity M) u =
      S.indicator g (u 0) := by
    intro u; by_cases h : u 0 ∈ S <;> simp [Set.indicator, h, hnd]
  rw [lintegral_congr hcomp, he.lintegral_comp (hg.indicator hS),
    ← lintegral_indicator_const (hS.inter measurableSet_Icc)]
  apply lintegral_congr_ae
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with t ht
  have ht0 : t ≠ 0 := ht
  have hpos : 0 < Real.sqrt m * |t| := mul_pos hsm (abs_pos.2 ht0)
  have hiff : Real.sqrt m * |t| ≤ 1 ↔ t ∈ Icc (-(1 / Real.sqrt m)) (1 / Real.sqrt m) := by
    rw [mem_Icc, ← abs_le, le_div_iff₀ hsm, mul_comm]
  by_cases htS : t ∈ S
  · by_cases hb : Real.sqrt m * |t| ≤ 1
    · rw [indicator_of_mem htS]; simp only [g]
      rw [indicator_of_mem (show t ∈ {t | 0 < Real.sqrt m * |t| ∧ Real.sqrt m * |t| ≤ 1}
        from ⟨hpos, hb⟩), indicator_of_mem (show t ∈ S ∩ _ from ⟨htS, hiff.1 hb⟩)]
    · rw [indicator_of_mem htS]; simp only [g]
      rw [indicator_of_notMem (show t ∉ {t | 0 < Real.sqrt m * |t| ∧ Real.sqrt m * |t| ≤ 1}
        from fun h => hb h.2), indicator_of_notMem (show t ∉ S ∩ _ from fun h => hb (hiff.2 h.2))]
  · rw [indicator_of_notMem htS, indicator_of_notMem (show t ∉ S ∩ _ from fun h => htS h.1)]

end StatFormal.OTFD.Wave8c
