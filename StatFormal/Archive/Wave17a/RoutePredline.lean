import StatFormal.Archive.Wave17a.Statements

/-!
# Route: robust equality paper2 `prop:predline` (untrusted)

* (i) Two triangle inequalities for `W₂` on `ℝ` (Tau Ceti, standard Borel) and `W₂ ≤ √β_s` from `W₂² ≤ β_s`.
* Constant rules push every law to `δ_c`, and `W₂(δ_c, δ_c) = 0`.
* (iii) The coupling `(⟨w,X⟩, ⟨w,X'⟩)_#π` has cost `E_π⟨w, X' − X⟩² = wᵀMw`.
* Budget `1`: with `P^past = δ₀` every coupling is supported on `{0} × ℝ²`, so its anisotropic cost is
  `E_{P^now} xᵀ(2I)x = 2 > 1`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Filter Topology Set
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace StatFormal.Wave17a

lemma measurable_edist_real : Measurable fun z : ℝ × ℝ => edist z.1 z.2 := continuous_edist.measurable

lemma ennreal_le_sqrt_of_sq_le {x : ℝ≥0∞} {β : ℝ} (hβ : 0 ≤ β) (h : x ^ 2 ≤ ENNReal.ofReal β) :
    x ≤ ENNReal.ofReal (Real.sqrt β) := by
  have : ENNReal.ofReal β = ENNReal.ofReal (Real.sqrt β) ^ 2 := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hβ]
  rw [this] at h
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h

theorem predline_certificate : Claims.predline_certificate := by
  intro d Θ C₀ C₁ h β₀ β₁ Q₀ Q₁ hh hC₀ hC₁ hQ₀ hQ₁ hβ₀ hβ₁ ⟨θ, h0, h1⟩
  have : IsProbabilityMeasure ((C₀ θ).map h) := ⟨by rw [Measure.map_apply hh MeasurableSet.univ]; simp⟩
  have : IsProbabilityMeasure ((C₁ θ).map h) := ⟨by rw [Measure.map_apply hh MeasurableSet.univ]; simp⟩
  have s0 := ennreal_le_sqrt_of_sq_le hβ₀ h0
  have s1 := ennreal_le_sqrt_of_sq_le hβ₁ h1
  have hd := measurable_edist_real
  have tri : TauCeti.wassersteinEDist 2 (Q₀.map h) (Q₁.map h) ≤
      TauCeti.wassersteinEDist 2 ((C₀ θ).map h) ((C₁ θ).map h) + ENNReal.ofReal (Real.sqrt β₀) +
        ENNReal.ofReal (Real.sqrt β₁) := by
    calc TauCeti.wassersteinEDist 2 (Q₀.map h) (Q₁.map h)
        ≤ TauCeti.wassersteinEDist 2 (Q₀.map h) ((C₀ θ).map h) +
            TauCeti.wassersteinEDist 2 ((C₀ θ).map h) (Q₁.map h) :=
          TauCeti.wassersteinEDist_triangle hd (by norm_num) _ _ _
      _ ≤ TauCeti.wassersteinEDist 2 (Q₀.map h) ((C₀ θ).map h) +
            (TauCeti.wassersteinEDist 2 ((C₀ θ).map h) ((C₁ θ).map h) +
              TauCeti.wassersteinEDist 2 ((C₁ θ).map h) (Q₁.map h)) :=
          add_le_add_right (TauCeti.wassersteinEDist_triangle hd (by norm_num) _ _ _) _
      _ ≤ ENNReal.ofReal (Real.sqrt β₀) +
            (TauCeti.wassersteinEDist 2 ((C₀ θ).map h) ((C₁ θ).map h) + ENNReal.ofReal (Real.sqrt β₁)) := by
          rw [TauCeti.wassersteinEDist_comm hd 2 (Q₀.map h)]
          gcongr
      _ = _ := by ring
  refine pow_le_pow_left₀ bot_le (tri.trans ?_) 2
  gcongr
  exact le_iSup (fun θ => TauCeti.wassersteinEDist 2 ((C₀ θ).map h) ((C₁ θ).map h)) θ

lemma map_const_prob {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ) :
    μ.map (fun _ => c) = Measure.dirac c := by
  rw [Measure.map_const, measure_univ, one_smul]

theorem predline_constant : Claims.predline_constant := by
  intro d Θ C₀ C₁ c Q₀ Q₁ hC₀ hC₁ hQ₀ hQ₁
  refine ⟨by rw [map_const_prob, map_const_prob, TauCeti.wassersteinEDist_self], ?_⟩
  refine le_antisymm (iSup_le fun θ => ?_) bot_le
  rw [map_const_prob, map_const_prob, TauCeti.wassersteinEDist_self]

theorem predline_constrained : Claims.predline_constrained := by
  intro Δ β₀ β₁ δ hΔ hβ₀ hβ₁ hδ
  have hs : 0 ≤ Δ + Real.sqrt β₀ + Real.sqrt β₁ := by positivity
  constructor
  · intro hle
    have := Real.sqrt_le_sqrt hle
    rw [Real.sqrt_sq hs] at this
    linarith
  · intro hle
    have h2 : Δ + Real.sqrt β₀ + Real.sqrt β₁ ≤ Real.sqrt δ := by linarith
    calc (Δ + Real.sqrt β₀ + Real.sqrt β₁) ^ 2 ≤ Real.sqrt δ ^ 2 := pow_le_pow_left₀ hs h2 2
      _ = δ := Real.sq_sqrt hδ

theorem predline_penalised_not_shift : Claims.predline_penalised_not_shift := by
  refine ⟨![0, 3 / 2], ![1, 0], 1, 1, one_pos, one_pos, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · intro k
    by_cases hk : k = 3
    · refine ⟨1, ?_⟩; subst hk; norm_num
    · refine ⟨0, ?_⟩; norm_num; intro h; apply hk; linarith
  · intro i; fin_cases i <;> norm_num
  · norm_num

/-! ### (iii) -/

lemma inner_euc {d : ℕ} (w u : EuclideanSpace ℝ (Fin d)) : ⟪w, u⟫ = ∑ i, w i * u i := by
  simp [PiLp.inner_apply, mul_comm]

theorem predline_lookback : Claims.predline_lookback := by
  intro d π M hπ hint hM w
  set g : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ × ℝ := fun z => (⟪w, z.1⟫, ⟪w, z.2⟫)
  have hg : Measurable g :=
    ((continuous_const.inner continuous_fst).prodMk (continuous_const.inner continuous_snd)).measurable
  have hcoup : TauCeti.IsCoupling (π.map g) ((π.map Prod.fst).map fun x => ⟪w, x⟫)
      ((π.map Prod.snd).map fun x => ⟪w, x⟫) := by
    have hw : Measurable fun x : EuclideanSpace ℝ (Fin d) => ⟪w, x⟫ :=
      (continuous_const.inner continuous_id).measurable
    constructor
    · rw [Measure.fst, Measure.map_map measurable_fst hg, Measure.map_map hw measurable_fst]; rfl
    · rw [Measure.snd, Measure.map_map measurable_snd hg, Measure.map_map hw measurable_snd]; rfl
  have hle := TauCeti.wassersteinEDist_rpow_le_lintegral (p := 2) measurable_edist_real (by norm_num) (by norm_num) hcoup
  have h2 : ((2 : ℝ≥0∞).toReal) = (2 : ℕ) := by norm_num
  rw [h2] at hle
  simp only [ENNReal.rpow_natCast] at hle
  rw [lintegral_map (measurable_edist_real.pow_const _) hg] at hle
  refine hle.trans (le_of_eq ?_)
  -- the cost
  have hfun : (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => (⟪w, z.2 - z.1⟫) ^ 2) =
      fun z => ∑ i, ∑ j, w i * w j * ((z.2 - z.1) i * (z.2 - z.1) j) := by
    funext z
    rw [inner_euc, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hintg : Integrable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => (⟪w, z.2 - z.1⟫) ^ 2) π := by
    rw [hfun]
    exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hint i j).const_mul _
  have hpt : ∀ z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      edist (g z).1 (g z).2 ^ 2 = ENNReal.ofReal ((⟪w, z.2 - z.1⟫) ^ 2) := by
    intro z
    simp only [g, edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, inner_sub_right]
    congr 1; ring
  refine Eq.trans (lintegral_congr fun z => hpt z) ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hintg (ae_of_all _ fun z => sq_nonneg _)]
  congr 1
  rw [hfun, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hint i j).const_mul _]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => (hint i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, ← hM i j]
  simp only [WithLp.ofLp]
  ring

/-! ### Budget one -/

local notation "E2" => EuclideanSpace ℝ (Fin 2)

lemma dirac_marginal_ae {γ : Measure (E2 × E2)} {x₀ : E2} (h : γ.map Prod.fst = Measure.dirac x₀) :
    ∀ᵐ z ∂γ, z.1 = x₀ := by
  have : ∀ᵐ x ∂(γ.map Prod.fst), x = x₀ := by rw [h, ae_dirac_eq]; exact Filter.eventually_pure.2 rfl
  exact ae_of_ae_map measurable_fst.aemeasurable this

theorem predline_budget_one_excludes : Claims.predline_budget_one_excludes := by
  set e₁ : E2 := EuclideanSpace.single 0 1
  set e₂ : E2 := EuclideanSpace.single 1 1
  set π : Measure (E2 × E2) := (2⁻¹ : ℝ≥0∞) • (Measure.dirac ((0 : E2), e₁) + Measure.dirac ((0 : E2), e₂))
  set M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal fun _ => 1 / 2
  have hπ : IsProbabilityMeasure π := by
    constructor
    simp only [π, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [← two_mul, mul_one]; exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  have hfst : π.map Prod.fst = Measure.dirac (0 : E2) := by
    rw [Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_add _ _ measurable_fst,
      Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_fst, ← two_smul ℝ≥0∞, smul_smul,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_smul]
  have hsnd : π.map Prod.snd = (2⁻¹ : ℝ≥0∞) • (Measure.dirac e₁ + Measure.dirac e₂) := by
    rw [Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_add _ _ measurable_snd,
      Measure.map_dirac' measurable_snd, Measure.map_dirac' measurable_snd]
  have hintd : ∀ (i j : Fin 2) (x : E2 × E2),
      Integrable (fun z : E2 × E2 => (z.2 - z.1) i * (z.2 - z.1) j) (Measure.dirac x) :=
    fun i j x => integrable_dirac (a := x) (f := fun z : E2 × E2 => (z.2 - z.1) i * (z.2 - z.1) j)
      (by simpa using ENNReal.mul_lt_top enorm_lt_top enorm_lt_top)
  have hint : ∀ i j, Integrable (fun z : E2 × E2 => (z.2 - z.1) i * (z.2 - z.1) j) π := by
    intro i j
    exact ((hintd i j _).add_measure (hintd i j _)).smul_measure (by norm_num)
  have hMij : ∀ i j, M i j = ∫ z, (z.2 - z.1) i * (z.2 - z.1) j ∂π := by
    intro i j
    rw [integral_smul_measure, integral_add_measure (hintd i j _) (hintd i j _), integral_dirac, integral_dirac]
    fin_cases i <;> fin_cases j <;> simp [M, e₁, e₂, Matrix.diagonal] <;> norm_num
  refine ⟨π, M, hπ, ?_, hint, hMij, ?_⟩
  · exact Matrix.PosDef.diagonal fun _ => by norm_num
  · intro hin
    unfold StatFormal.RobustEquality.Quick.InAniso at hin
    rw [hfst, hsnd] at hin
    -- every coupling of `δ₀` and `P^now` costs `2`
    have hinv : M⁻¹ = Matrix.diagonal fun _ => 2 := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext _; norm_num
    have hcost : ∀ x : E2, StatFormal.RobustEquality.Quick.cM M 0 x = 2 * (x 0 ^ 2 + x 1 ^ 2) := by
      intro x
      simp only [StatFormal.RobustEquality.Quick.cM, hinv, sub_zero, dotProduct, Matrix.mulVec_diagonal,
        Fin.sum_univ_two]
      simp only [WithLp.equiv, Equiv.coe_fn_mk]
      ring
    have hlow : ∀ γ : Measure (E2 × E2), TauCeti.IsCoupling γ (Measure.dirac 0)
        ((2⁻¹ : ℝ≥0∞) • (Measure.dirac e₁ + Measure.dirac e₂)) →
        ENNReal.ofReal 2 ≤ ∫⁻ z, ENNReal.ofReal (StatFormal.RobustEquality.Quick.cM M z.1 z.2) ∂γ := by
      intro γ hγ
      have hae := dirac_marginal_ae (x₀ := 0) hγ.fst_eq
      have hcont : Measurable fun x : E2 => ENNReal.ofReal (StatFormal.RobustEquality.Quick.cM M 0 x) := by
        simp_rw [hcost]
        exact ENNReal.measurable_ofReal.comp (by fun_prop)
      rw [lintegral_congr_ae (by filter_upwards [hae] with z hz; rw [hz])]
      have hmap := lintegral_map hcont measurable_snd (μ := γ)
      beta_reduce at hmap
      rw [← hmap, ← Measure.snd, hγ.snd_eq]
      rw [lintegral_smul_measure, lintegral_add_measure, lintegral_dirac, lintegral_dirac, hcost, hcost]
      simp only [e₁, e₂, PiLp.single_apply]
      norm_num
      rw [show (4:ℝ≥0∞) = 2 * 2 by norm_num, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
        one_mul]
    have : ENNReal.ofReal 2 ≤ ENNReal.ofReal 1 := by
      refine le_trans (le_iInf₂ fun γ hγ => hlow γ hγ) hin
    rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)] at this
    norm_num at this

end StatFormal.Wave17a
