import StatFormal.Archive.Wave23d.Statements

/-!
# Route — robust-equality paper 2 `prop:repair` (untrusted)

* (i) Triangle inequality for `W₂` (Tau Ceti) twice; an optimal coupling `π` of `(μ_s, μ_s')` (attainment on `ℝ`)
  is admissible in `ω_s(σ_s)`, and `(T_s × T_s)#π` couples the pushforwards. `ω ≤ Lip·σ` pointwise.
* (ii) For atomless `μ_s`, `F_s#μ_s` is uniform (probability integral transform), so `T_s#μ_s = g_s#U` with `g_s`
  monotone on `(0,1)`, whose quantile is `g_s` a.e.; the one-dimensional quantile formula gives
  `Δ_T = ‖g_0 − g_1‖_{L²(0,1)} = ℓ‖q_0 − q_1‖ = ℓΔ`.
* (iii) `ω` and `Lip` are suprema of seminorms of `T`, linear in the values; for nondecreasing maps
  `Δ_T = ‖T_0∘q_0 − T_1∘q_1‖_{L²(0,1)}`, a seminorm. The fixed-multiplier counterexample: `√(1/4 + (d² − 1)_+)` at
  `d = 1, 2, 3`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal

namespace StatFormal.Wave23d

lemma edist_real (x y : ℝ) : edist x y = ENNReal.ofReal |x - y| := by
  rw [edist_dist, Real.dist_eq]

lemma measurable_edist_real : Measurable fun z : ℝ × ℝ => edist z.1 z.2 :=
  measurable_fst.edist measurable_snd

/-! ### (i) -/

lemma edist_le_lip (T : ℝ → ℝ) (x y : ℝ) : edist (T x) (T y) ≤ lipConst T * edist x y := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hxy)
  have h1 : ENNReal.ofReal (|T x - T y| / |x - y|) ≤ lipConst T :=
    le_iSup₂_of_le (f := fun x y => ⨆ (_ : x ≠ y), ENNReal.ofReal (|T x - T y| / |x - y|)) x y
      (le_iSup_of_le hxy le_rfl)
  rw [edist_real, edist_real]
  calc ENNReal.ofReal |T x - T y| = ENNReal.ofReal (|T x - T y| / |x - y|) * ENNReal.ofReal |x - y| := by
        rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hpos.ne']
    _ ≤ lipConst T * ENNReal.ofReal |x - y| := mul_le_mul_left h1 _

lemma eLpNorm_edist_eq {T : ℝ → ℝ} (hT : Measurable T) (π : Measure (ℝ × ℝ)) :
    eLpNorm (fun z : ℝ × ℝ => edist (T z.1) (T z.2)) 2 π = eLpNorm (fun z : ℝ × ℝ => T z.1 - T z.2) 2 π := by
  simp_rw [edist_eq_enorm_sub]
  exact eLpNorm_enorm (fun z : ℝ × ℝ => T z.1 - T z.2)
    ((hT.comp measurable_fst).sub (hT.comp measurable_snd)).aestronglyMeasurable

lemma fst_map_prodMap' (π : Measure (ℝ × ℝ)) {T S : ℝ → ℝ} (hT : Measurable T) (hS : Measurable S) :
    (π.map (Prod.map T S)).fst = π.fst.map T := by
  rw [Measure.fst, Measure.map_map measurable_fst (hT.prodMap hS), Measure.fst, Measure.map_map hT measurable_fst]; rfl

lemma snd_map_prodMap' (π : Measure (ℝ × ℝ)) {T S : ℝ → ℝ} (hT : Measurable T) (hS : Measurable S) :
    (π.map (Prod.map T S)).snd = π.snd.map S := by
  rw [Measure.snd, Measure.map_map measurable_snd (hT.prodMap hS), Measure.snd, Measure.map_map hS measurable_snd]; rfl

lemma lip_bound_coupling (T : ℝ → ℝ) (π : Measure (ℝ × ℝ)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcost : eLpNorm (fun z : ℝ × ℝ => edist z.1 z.2) 2 π ≤ ENNReal.ofReal σ) :
    eLpNorm (fun z : ℝ × ℝ => edist (T z.1) (T z.2)) 2 π ≤ lipConst T * ENNReal.ofReal σ := by
  by_cases hL : lipConst T = ⊤
  · rcases hσ.eq_or_lt with rfl | hσpos
    · rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero] at hcost
      rw [eLpNorm_eq_zero_iff two_ne_zero] at hcost
      have : (fun z : ℝ × ℝ => edist (T z.1) (T z.2)) =ᵐ[π] 0 := by
        filter_upwards [hcost] with z hz
        simp only [Pi.zero_apply, edist_eq_zero] at hz ⊢
        rw [hz]
      rw [eLpNorm_congr_ae this, eLpNorm_zero]; exact zero_le
    · rw [hL, ENNReal.top_mul (ENNReal.ofReal_pos.2 hσpos).ne']; exact le_top
  · have hLip : LipschitzWith (lipConst T).toNNReal T := by
      intro x y
      rw [ENNReal.coe_toNNReal hL]; exact edist_le_lip T x y
    have hTm : Measurable T := hLip.continuous.measurable
    calc eLpNorm (fun z : ℝ × ℝ => edist (T z.1) (T z.2)) 2 π
        ≤ eLpNorm (fun z : ℝ × ℝ => (lipConst T).toReal • (z.1 - z.2)) 2 π := by
          refine eLpNorm_mono_enorm ((hTm.comp measurable_fst).edist (hTm.comp measurable_snd)).aestronglyMeasurable
            fun z => ?_
          rw [enorm_eq_self, smul_eq_mul, Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
            ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hL, ← edist_real]
          exact edist_le_lip T z.1 z.2
      _ = lipConst T * eLpNorm (fun z : ℝ × ℝ => edist z.1 z.2) 2 π := by
          rw [show (fun z : ℝ × ℝ => (lipConst T).toReal • (z.1 - z.2)) =
              (lipConst T).toReal • (fun z : ℝ × ℝ => z.1 - z.2) from rfl, eLpNorm_const_smul,
            Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hL]
          congr 1
          have := eLpNorm_edist_eq measurable_id π
          simpa using this.symm
      _ ≤ lipConst T * ENNReal.ofReal σ := by gcongr

theorem repair_omega_le_lip_thm : Claims.repair_omega_le_lip := by
  intro μ G σ T hσ
  unfold omegaMod
  exact iSup₂_le fun π ⟨_, _, _, hcost⟩ => lip_bound_coupling T π hσ hcost

/-- `W₂(T#μ, T#μ') ≤ ω_μ(σ)` when `W₂(μ, μ') ≤ σ`. -/
lemma w2_map_le_omega (μ μ' : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] {T : ℝ → ℝ}
    (hT : Measurable T) {σ : ℝ} (h : wassersteinEDist 2 μ μ' ≤ ENNReal.ofReal σ) :
    wassersteinEDist 2 (μ.map T) (μ'.map T) ≤ omegaMod μ univ σ T := by
  obtain ⟨π, hπ, hopt⟩ := exists_isCoupling_eLpNorm_eq_wassersteinEDist (p := 2) two_ne_zero ENNReal.ofNat_ne_top
    μ μ' ⟨μ.prod μ', ⟨Measure.fst_prod, Measure.snd_prod⟩⟩
  have hπp : IsProbabilityMeasure π := by
    constructor; rw [← Measure.fst_univ, hπ.fst_eq, measure_univ]
  have hcoup : IsCoupling (π.map (Prod.map T T)) (μ.map T) (μ'.map T) := by
    constructor
    · rw [fst_map_prodMap' _ hT hT, hπ.fst_eq]
    · rw [snd_map_prodMap' _ hT hT, hπ.snd_eq]
  refine (wassersteinEDist_le hcoup 2).trans ?_
  rw [eLpNorm_map_measure measurable_edist_real.aestronglyMeasurable (hT.prodMap hT).aemeasurable]
  unfold omegaMod
  refine le_iSup₂_of_le (f := fun (π : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure π ∧ π.fst = μ ∧
      π (univ ×ˢ (univ : Set ℝ)ᶜ) = 0 ∧ eLpNorm (fun z : ℝ × ℝ => edist z.1 z.2) 2 π ≤ ENNReal.ofReal σ) =>
      eLpNorm (fun z : ℝ × ℝ => edist (T z.1) (T z.2)) 2 π) π ⟨hπp, hπ.fst_eq, by simp, hopt.trans_le h⟩ ?_
  exact le_rfl

theorem repair_cert_thm : Claims.repair_cert := by
  intro μ₀ μ₁ μ₀' μ₁' _ _ _ _ T₀ T₁ σ₀ σ₁ hT₀ hT₁ _ _ h₀ h₁
  have hd := measurable_edist_real
  have t1 := wassersteinEDist_triangle hd one_le_two (μ₀'.map T₀) (μ₀.map T₀) (μ₁'.map T₁)
  have t2 := wassersteinEDist_triangle hd one_le_two (μ₀.map T₀) (μ₁.map T₁) (μ₁'.map T₁)
  have e0 : wassersteinEDist 2 (μ₀'.map T₀) (μ₀.map T₀) ≤ omegaMod μ₀ univ σ₀ T₀ := by
    rw [wassersteinEDist_comm hd]; exact w2_map_le_omega μ₀ μ₀' hT₀ h₀
  have e1 := w2_map_le_omega μ₁ μ₁' hT₁ h₁
  calc wassersteinEDist 2 (μ₀'.map T₀) (μ₁'.map T₁)
      ≤ wassersteinEDist 2 (μ₀'.map T₀) (μ₀.map T₀) + wassersteinEDist 2 (μ₀.map T₀) (μ₁'.map T₁) := t1
    _ ≤ omegaMod μ₀ univ σ₀ T₀ + (wassersteinEDist 2 (μ₀.map T₀) (μ₁.map T₁) + omegaMod μ₁ univ σ₁ T₁) :=
        add_le_add e0 (t2.trans (add_le_add le_rfl e1))
    _ = _ := by ring

/-! ### (ii) -/

/-- The uniform law on `(0, 1)`. -/
abbrev unifI : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

instance : IsProbabilityMeasure unifI := ⟨by simp [unifI]⟩

/-- For `g` monotone on `(0,1)`: `W₂(g₀#U, g₁#U) = ‖g₀ − g₁‖_{L²(0,1)}`. -/
lemma w2_map_unif {g₀ g₁ : ℝ → ℝ} (h₀ : MonotoneOn g₀ (Ioo 0 1)) (h₁ : MonotoneOn g₁ (Ioo 0 1)) :
    wassersteinEDist 2 (unifI.map g₀) (unifI.map g₁) = eLpNorm (fun t => g₀ t - g₁ t) 2 unifI := by
  rw [wassersteinEDist_eq_eLpNorm_quantile_sub one_le_two]
  refine eLpNorm_congr_ae ?_
  filter_upwards [Measure.quantile_map_volume_Ioo_ae h₀, Measure.quantile_map_volume_Ioo_ae h₁] with t ht₀ ht₁
  rw [ht₀, ht₁]

theorem repair_partial_delta_thm : Claims.repair_partial_delta := by
  intro μ₀ μ₁ _ _ _ _ π₀ π₁ ℓ hπ₀ hπ₁ hℓ hℓ1
  intro qB T₀ T₁
  set g₀ : ℝ → ℝ := fun t => ℓ * μ₀.quantile t + (1 - ℓ) * qB t
  set g₁ : ℝ → ℝ := fun t => ℓ * μ₁.quantile t + (1 - ℓ) * qB t
  have hqB : MonotoneOn qB (Ioo 0 1) := fun x hx y hy hxy => by
    have h0 := Measure.monotoneOn_quantile μ₀ hx hy hxy
    have h1 := Measure.monotoneOn_quantile μ₁ hx hy hxy
    simp only [qB]; nlinarith
  have hmono : ∀ μ : Measure ℝ, MonotoneOn (fun t => ℓ * μ.quantile t + (1 - ℓ) * qB t) (Ioo 0 1) :=
    fun μ x hx y hy hxy => by
      have h0 := Measure.monotoneOn_quantile μ hx hy hxy
      have h1 := hqB hx hy hxy
      have : 0 ≤ 1 - ℓ := by linarith
      nlinarith
  have hqBm : Measurable qB :=
    ((Measure.measurable_quantile μ₀).const_mul _).add ((Measure.measurable_quantile μ₁).const_mul _)
  have hgm : ∀ μ : Measure ℝ, Measurable (fun t => ℓ * μ.quantile t + (1 - ℓ) * qB t) :=
    fun μ => ((Measure.measurable_quantile μ).const_mul _).add (hqBm.const_mul _)
  have hmap : ∀ μ : Measure ℝ, IsProbabilityMeasure μ → NullSingletonClass μ →
      μ.map (fun y => ℓ * μ.quantile (cdf μ y) + (1 - ℓ) * qB (cdf μ y)) =
        unifI.map (fun t => ℓ * μ.quantile t + (1 - ℓ) * qB t) := by
    intro μ _ _
    have hc : Measurable (cdf μ) := (cdf μ).mono.measurable
    rw [show (fun y => ℓ * μ.quantile (cdf μ y) + (1 - ℓ) * qB (cdf μ y)) =
        (fun t => ℓ * μ.quantile t + (1 - ℓ) * qB t) ∘ cdf μ from rfl,
      ← Measure.map_map (hgm μ) hc, Measure.cdf_map_eq_volume_restrict, unifI, Measure.restrict_congr_set Ioo_ae_eq_Icc]
  show wassersteinEDist 2 (μ₀.map T₀) (μ₁.map T₁) = _
  rw [show T₀ = (fun y => ℓ * μ₀.quantile (cdf μ₀ y) + (1 - ℓ) * qB (cdf μ₀ y)) from rfl,
    show T₁ = (fun y => ℓ * μ₁.quantile (cdf μ₁ y) + (1 - ℓ) * qB (cdf μ₁ y)) from rfl,
    hmap μ₀ inferInstance inferInstance, hmap μ₁ inferInstance inferInstance, w2_map_unif (hmono μ₀) (hmono μ₁),
    wassersteinEDist_eq_eLpNorm_quantile_sub one_le_two μ₀ μ₁]
  have e : (fun t => (ℓ * μ₀.quantile t + (1 - ℓ) * qB t) - (ℓ * μ₁.quantile t + (1 - ℓ) * qB t)) =
      ℓ • (fun t => μ₀.quantile t - μ₁.quantile t) := by
    ext t; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hℓ]

theorem repair_root_affine_thm : Claims.repair_root_affine := by
  intro S Δ σ ζ root
  have key : ∀ ℓ, root ℓ = ℓ * (Δ + ∑ s, σ s) + (1 - ℓ) * ∑ s, σ s * ζ s := by
    intro ℓ
    simp only [root, Finset.mul_sum, mul_add]
    rw [add_assoc]; congr 1
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun s _ => ?_; ring
  refine ⟨fun ℓ => ?_, ?_⟩
  · rw [key ℓ, key 0, key 1]; ring
  · rw [key 0, key 1]
    have : ∑ s, σ s * (ζ s - 1) = ∑ s, σ s * ζ s - ∑ s, σ s := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => ?_; ring
    rw [this]; constructor <;> intro h <;> linarith

/-! ### (iii) convexity in the values -/

lemma ext_comb {N : ℕ} (ext : (Fin N → ℝ) →ₗ[ℝ] (ℝ → ℝ)) (t t' : Fin N → ℝ) (a b : ℝ) (x : ℝ) :
    ext (a • t + b • t') x = a * ext t x + b * ext t' x := by
  simp [map_add, map_smul]

theorem repair_convex_omega_thm : Claims.repair_convex_omega := by
  intro N ext μ G σ hext t t' a b ha hb hab
  unfold omegaMod
  refine iSup₂_le fun π hπ => ?_
  have h1 : eLpNorm (fun z : ℝ × ℝ => edist (ext t z.1) (ext t z.2)) 2 π ≤
      ⨆ (π : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure π ∧ π.fst = μ ∧ π (univ ×ˢ Gᶜ) = 0 ∧
        eLpNorm (fun z : ℝ × ℝ => edist z.1 z.2) 2 π ≤ ENNReal.ofReal σ),
        eLpNorm (fun z : ℝ × ℝ => edist (ext t z.1) (ext t z.2)) 2 π :=
    le_iSup₂_of_le (f := fun (π : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure π ∧ π.fst = μ ∧ π (univ ×ˢ Gᶜ) = 0 ∧
        eLpNorm (fun z : ℝ × ℝ => edist z.1 z.2) 2 π ≤ ENNReal.ofReal σ) =>
        eLpNorm (fun z : ℝ × ℝ => edist (ext t z.1) (ext t z.2)) 2 π) π hπ le_rfl
  have h2 : eLpNorm (fun z : ℝ × ℝ => edist (ext t' z.1) (ext t' z.2)) 2 π ≤
      ⨆ (π : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure π ∧ π.fst = μ ∧ π (univ ×ˢ Gᶜ) = 0 ∧
        eLpNorm (fun z : ℝ × ℝ => edist z.1 z.2) 2 π ≤ ENNReal.ofReal σ),
        eLpNorm (fun z : ℝ × ℝ => edist (ext t' z.1) (ext t' z.2)) 2 π :=
    le_iSup₂_of_le (f := fun (π : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure π ∧ π.fst = μ ∧ π (univ ×ˢ Gᶜ) = 0 ∧
        eLpNorm (fun z : ℝ × ℝ => edist z.1 z.2) 2 π ≤ ENNReal.ofReal σ) =>
        eLpNorm (fun z : ℝ × ℝ => edist (ext t' z.1) (ext t' z.2)) 2 π) π hπ le_rfl
  rw [eLpNorm_edist_eq (hext t)] at h1
  rw [eLpNorm_edist_eq (hext t')] at h2
  rw [eLpNorm_edist_eq (hext _)]
  have e : (fun z : ℝ × ℝ => ext (a • t + b • t') z.1 - ext (a • t + b • t') z.2) =
      a • (fun z : ℝ × ℝ => ext t z.1 - ext t z.2) + b • (fun z : ℝ × ℝ => ext t' z.1 - ext t' z.2) := by
    ext z; simp only [ext_comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e]
  calc eLpNorm (a • (fun z : ℝ × ℝ => ext t z.1 - ext t z.2) + b • (fun z : ℝ × ℝ => ext t' z.1 - ext t' z.2)) 2 π
      ≤ eLpNorm (a • (fun z : ℝ × ℝ => ext t z.1 - ext t z.2)) 2 π +
          eLpNorm (b • (fun z : ℝ × ℝ => ext t' z.1 - ext t' z.2)) 2 π := eLpNorm_add_le one_le_two
    _ = ENNReal.ofReal a * eLpNorm (fun z : ℝ × ℝ => ext t z.1 - ext t z.2) 2 π +
          ENNReal.ofReal b * eLpNorm (fun z : ℝ × ℝ => ext t' z.1 - ext t' z.2) 2 π := by
        rw [eLpNorm_const_smul, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ _ := by gcongr

theorem repair_convex_lip_thm : Claims.repair_convex_lip := by
  intro N ext t t' a b ha hb hab
  unfold lipConst
  refine iSup_le fun x => iSup_le fun y => iSup_le fun hxy => ?_
  have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hxy)
  have l1 : ENNReal.ofReal (|ext t x - ext t y| / |x - y|) ≤
      ⨆ (x : ℝ) (y : ℝ) (_ : x ≠ y), ENNReal.ofReal (|ext t x - ext t y| / |x - y|) :=
    le_iSup₂_of_le (f := fun x y => ⨆ (_ : x ≠ y), ENNReal.ofReal (|ext t x - ext t y| / |x - y|)) x y
      (le_iSup_of_le hxy le_rfl)
  have l2 : ENNReal.ofReal (|ext t' x - ext t' y| / |x - y|) ≤
      ⨆ (x : ℝ) (y : ℝ) (_ : x ≠ y), ENNReal.ofReal (|ext t' x - ext t' y| / |x - y|) :=
    le_iSup₂_of_le (f := fun x y => ⨆ (_ : x ≠ y), ENNReal.ofReal (|ext t' x - ext t' y| / |x - y|)) x y
      (le_iSup_of_le hxy le_rfl)
  have hbound : |ext (a • t + b • t') x - ext (a • t + b • t') y| / |x - y| ≤
      a * (|ext t x - ext t y| / |x - y|) + b * (|ext t' x - ext t' y| / |x - y|) := by
    rw [ext_comb, ext_comb, mul_div_assoc', mul_div_assoc', ← add_div,
      div_le_div_iff_of_pos_right hpos]
    calc |a * ext t x + b * ext t' x - (a * ext t y + b * ext t' y)|
        = |a * (ext t x - ext t y) + b * (ext t' x - ext t' y)| := by ring_nf
      _ ≤ |a * (ext t x - ext t y)| + |b * (ext t' x - ext t' y)| := abs_add_le _ _
      _ = a * |ext t x - ext t y| + b * |ext t' x - ext t' y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  calc ENNReal.ofReal (|ext (a • t + b • t') x - ext (a • t + b • t') y| / |x - y|)
      ≤ ENNReal.ofReal (a * (|ext t x - ext t y| / |x - y|) + b * (|ext t' x - ext t' y| / |x - y|)) :=
        ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal a * ENNReal.ofReal (|ext t x - ext t y| / |x - y|) +
          ENNReal.ofReal b * ENNReal.ofReal (|ext t' x - ext t' y| / |x - y|) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
    _ ≤ _ := by gcongr

/-- For nondecreasing `T, S`: `W₂(T#μ₀, S#μ₁) = ‖T∘q₀ − S∘q₁‖_{L²(0,1)}`. -/
lemma w2_monotone_maps (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] {T S : ℝ → ℝ}
    (hT : Monotone T) (hS : Monotone S) :
    wassersteinEDist 2 (μ₀.map T) (μ₁.map S) =
      eLpNorm (fun t => T (μ₀.quantile t) - S (μ₁.quantile t)) 2 unifI := by
  have e : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] {R : ℝ → ℝ}, Monotone R →
      μ.map R = unifI.map (R ∘ μ.quantile) := by
    intro μ _ R hR
    conv_lhs => rw [← Measure.map_quantile_volume_Ioo μ]
    rw [Measure.map_map hR.measurable (Measure.measurable_quantile μ)]
  rw [e μ₀ hT, e μ₁ hS, w2_map_unif (hT.comp_monotoneOn (Measure.monotoneOn_quantile μ₀))
    (hS.comp_monotoneOn (Measure.monotoneOn_quantile μ₁))]
  rfl

theorem repair_convex_delta_thm : Claims.repair_convex_delta := by
  intro N ext μ₀ μ₁ _ _ t₀ t₁ t₀' t₁' a b h₀ h₁ h₀' h₁' ha hb hab
  have hcomb : ∀ {u u' : Fin N → ℝ}, Monotone (ext u) → Monotone (ext u') → Monotone (ext (a • u + b • u')) := by
    intro u u' hu hu' x y hxy
    rw [ext_comb, ext_comb]
    have := hu hxy; have := hu' hxy
    nlinarith
  refine ⟨hcomb h₀ h₀', ?_⟩
  rw [w2_monotone_maps μ₀ μ₁ (hcomb h₀ h₀') (hcomb h₁ h₁'), w2_monotone_maps μ₀ μ₁ h₀ h₁,
    w2_monotone_maps μ₀ μ₁ h₀' h₁']
  have e : (fun t => ext (a • t₀ + b • t₀') (μ₀.quantile t) - ext (a • t₁ + b • t₁') (μ₁.quantile t)) =
      a • (fun t => ext t₀ (μ₀.quantile t) - ext t₁ (μ₁.quantile t)) +
        b • (fun t => ext t₀' (μ₀.quantile t) - ext t₁' (μ₁.quantile t)) := by
    ext x; simp only [ext_comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e]
  refine (eLpNorm_add_le one_le_two).trans (le_of_eq ?_)
  rw [eLpNorm_const_smul, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
    abs_of_nonneg ha, abs_of_nonneg hb]

/-! ### (iii) the fixed-multiplier caveat -/

theorem repair_sqrt_envelope_not_convex_thm : Claims.repair_sqrt_envelope_not_convex := by
  intro hconv
  have key : ∀ d : ℝ, envFix (Measure.dirac 0) {0, 1} 1 (1 / 2) (fun y => d * y) = 1 / 4 + max 0 (d ^ 2 - 1) := by
    intro d
    have : Nonempty ({0, 1} : Finset ℝ) := ⟨⟨0, by simp⟩⟩
    unfold envFix
    rw [integral_dirac]
    congr 1
    · norm_num
    · apply le_antisymm
      · refine ciSup_le fun y => ?_
        rcases Finset.mem_insert.1 y.2 with h | h
        · rw [h]; simp
        · rw [Finset.mem_singleton.1 h]; simp
      · refine max_le ?_ ?_
        · refine le_trans (le_of_eq ?_) (le_ciSup (Set.finite_range _).bddAbove ⟨0, by simp⟩)
          simp
        · refine le_trans (le_of_eq ?_) (le_ciSup (Set.finite_range _).bddAbove ⟨1, by simp⟩)
          simp
  have h := hconv.2 (mem_univ (1 : ℝ)) (mem_univ (3 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, key] at h
  norm_num at h
  -- `h : √(13/4) ≤ (1/2) √(1/4) + (1/2) √(33/4)`; contradiction since `2√13 > 1 + √33`
  have h13 : √(13 / 4 : ℝ) = √13 / 2 := by
    rw [Real.sqrt_div' 13 (by norm_num : (0:ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h1 : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h33 : √(33 / 4 : ℝ) = √33 / 2 := by
    rw [Real.sqrt_div' 33 (by norm_num : (0:ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h4 : √(4 : ℝ) = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4] at h
  have a2 := Real.sq_sqrt (show (0:ℝ) ≤ 13 by norm_num)
  have c2 := Real.sq_sqrt (show (0:ℝ) ≤ 33 by norm_num)
  have a0 := Real.sqrt_nonneg 13
  have c0 := Real.sqrt_nonneg 33
  have h' : 2 * √13 ≤ 1 + √33 := by linarith
  have hsq := mul_self_le_mul_self (by positivity) h'
  have hc9 : 9 ≤ √33 := by nlinarith
  nlinarith

end StatFormal.Wave23d
