import StatFormal.Wave30tx.RouteBasic
import StatFormal.Archive.Wave11b.RouteAttain
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs

/-!
# Route: `lem:contact (v2)` and the density form of the fractional set (untrusted proof material)

* `withDensity_inf`: `μ.withDensity f ⊓ μ.withDensity g = μ.withDensity (min f g)` (split a set along `{f ≤ g}`).
* `inf_eq_withDensity`, `inf_univ`: `P ⊓ Q = (P+Q).withDensity (min (dP/dρ) (dQ/dρ))`, of mass `1 − TV(P,Q)`
  (`Distances.tvDist_eq_one_sub_integral_min`).
* `contactLaw_mem`, `eq_contactLaw`: `R*` is a common `α*`-trimming, and the only one (`R ≤ β*P`, `R ≤ β*Q` give
  `β*⁻¹R ≤ P ⊓ Q`; equal masses).
* `contact_compact`: totally bounded (bounded simple approximations of `φ` in `L¹(P)`, `StronglyMeasurable.approxBounded`, and a
  compact box in finitely many coordinates) and closed (`Wave11b.attain_closed`).
* `contact`: the intersection by `Wave11b.attain_common` and uniqueness; `ω_c → 0` by the minimum of `infDist · 𝒞_{α*}(Q)` on the
  compact set `𝒞_{α*}(P) ∩ {‖a − μ_{R*}‖ ≥ η}`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace Pointwise

namespace StatFormal.Wave30tx.RContact

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.ZeroSet
  StatFormal.Distances

section Measures

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

theorem withDensity_inf (μ : Measure 𝒳) {f g : 𝒳 → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    μ.withDensity f ⊓ μ.withDensity g = μ.withDensity (fun x => min (f x) (g x)) := by
  refine le_antisymm ?_ (le_inf (withDensity_mono (ae_of_all _ fun x => min_le_left _ _))
    (withDensity_mono (ae_of_all _ fun x => min_le_right _ _)))
  rw [Measure.le_iff]
  intro s hs
  set t := {x | f x ≤ g x}
  have ht : MeasurableSet t := measurableSet_le hf hg
  rw [← measure_inter_add_sdiff s ht, ← measure_inter_add_sdiff (μ := μ.withDensity _) s ht]
  refine add_le_add ?_ ?_
  · refine (Measure.le_iff'.1 (inf_le_left : μ.withDensity f ⊓ μ.withDensity g ≤ μ.withDensity f) (s ∩ t)).trans ?_
    rw [withDensity_apply _ (hs.inter ht), withDensity_apply _ (hs.inter ht)]
    refine le_of_eq (setLIntegral_congr_fun (hs.inter ht) fun x hx => ?_)
    exact (min_eq_left hx.2).symm
  · refine (Measure.le_iff'.1 (inf_le_right : μ.withDensity f ⊓ μ.withDensity g ≤ μ.withDensity g) (s \ t)).trans ?_
    rw [withDensity_apply _ (hs.diff ht), withDensity_apply _ (hs.diff ht)]
    refine le_of_eq (setLIntegral_congr_fun (hs.diff ht) fun x hx => ?_)
    have : ¬ f x ≤ g x := hx.2
    exact (min_eq_right (le_of_not_ge this)).symm

theorem inf_eq_withDensity (P Q : Measure 𝒳) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    P ⊓ Q = (P + Q).withDensity (fun x => min (P.rnDeriv (P + Q) x) (Q.rnDeriv (P + Q) x)) := by
  have hP : P ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQ : Q ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  have h := withDensity_inf (P + Q) (Measure.measurable_rnDeriv P (P + Q)) (Measure.measurable_rnDeriv Q (P + Q))
  rw [Measure.withDensity_rnDeriv_eq P (P + Q) hP, Measure.withDensity_rnDeriv_eq Q (P + Q) hQ] at h
  exact h

theorem inf_univ (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (P ⊓ Q) univ = ENNReal.ofReal (1 - tvDist P Q) := by
  have hP : P ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQ : Q ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  rw [tvDist_eq_one_sub_integral_min (P + Q) hP hQ, sub_sub_cancel, inf_eq_withDensity,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hpi : Integrable (fun x => (P.rnDeriv (P + Q) x).toReal) (P + Q) := Measure.integrable_toReal_rnDeriv
  have hmi : Integrable (fun x => min (P.rnDeriv (P + Q) x).toReal (Q.rnDeriv (P + Q) x).toReal) (P + Q) := by
    refine hpi.mono' ((Measure.measurable_rnDeriv _ _).ennreal_toReal.min
      (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
    exact min_le_left _ _
  rw [ofReal_integral_eq_lintegral_ofReal hmi (ae_of_all _ fun x => le_min ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg)]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top P (P + Q), Measure.rnDeriv_lt_top Q (P + Q)] with x h1 h2
  rw [← ENNReal.toReal_min h1.ne h2.ne, ENNReal.ofReal_toReal (min_lt_iff.2 (Or.inl h1)).ne]

theorem smul_le_smul_measure {μ ν : Measure 𝒳} (h : μ ≤ ν) (c : ℝ≥0∞) : c • μ ≤ c • ν := by
  rw [Measure.le_iff]
  intro s _
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  gcongr

theorem eq_of_le_of_univ {μ ν : Measure 𝒳} [IsFiniteMeasure ν] (h : μ ≤ ν) (hu : μ univ = ν univ) :
    μ = ν := by
  ext s hs
  refine le_antisymm (h s) ?_
  have h1 := measure_add_measure_compl (μ := μ) hs
  have h2 := measure_add_measure_compl (μ := ν) hs
  have hc : μ sᶜ ≤ ν sᶜ := h sᶜ
  have : ν s + ν sᶜ ≤ μ s + ν sᶜ := by
    rw [h2, ← hu, ← h1]; gcongr
  exact (ENNReal.add_le_add_iff_right (measure_ne_top ν sᶜ)).1 this

/-- `β* = (1 − α*)⁻¹` as an extended real. -/
theorem contactLaw_eq (P Q : Measure 𝒳) :
    StatFormal.Wave30tx.contactLaw P Q = ENNReal.ofReal (1 / (1 - tvDist P Q)) • (P ⊓ Q) := rfl

theorem contactLaw_comm (P Q : Measure 𝒳) :
    StatFormal.Wave30tx.contactLaw Q P = StatFormal.Wave30tx.contactLaw P Q := by
  simp only [StatFormal.Wave30tx.contactLaw, tvDist_comm Q P, inf_comm]

variable (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

theorem contactLaw_univ (htv : tvDist P Q < 1) : StatFormal.Wave30tx.contactLaw P Q univ = 1 := by
  rw [contactLaw_eq, Measure.smul_apply, inf_univ, smul_eq_mul, ← ENNReal.ofReal_mul (by
    have : 0 < 1 - tvDist P Q := by linarith
    positivity)]
  have : 0 < 1 - tvDist P Q := by linarith
  rw [one_div, inv_mul_cancel₀ this.ne', ENNReal.ofReal_one]

instance isFiniteMeasure_inf : IsFiniteMeasure (P ⊓ Q) := isFiniteMeasure_of_le P inf_le_left

theorem contactLaw_isProb (htv : tvDist P Q < 1) : IsProbabilityMeasure (StatFormal.Wave30tx.contactLaw P Q) :=
  ⟨contactLaw_univ P Q htv⟩

/-- `R*` is an `α*`-trimming of `P`. -/
theorem contactLaw_mem_trimSet (htv : tvDist P Q < 1) :
    StatFormal.Wave30tx.contactLaw P Q ∈ StatFormal.Wave8a.trimSet P (tvDist P Q) := by
  have := contactLaw_isProb P Q htv
  refine ⟨inferInstance, ?_, ?_⟩
  · exact (Measure.absolutelyContinuous_of_le inf_le_left).smul_left _
  · have h1 : (P ⊓ Q).rnDeriv P ≤ᵐ[P] 1 := Measure.rnDeriv_le_one_of_le inf_le_left
    have h2 := Measure.rnDeriv_smul_left_of_ne_top (P ⊓ Q) P
      (r := ENNReal.ofReal (1 / (1 - tvDist P Q))) ENNReal.ofReal_ne_top
    filter_upwards [h1, h2] with x hx1 hx2
    rw [contactLaw_eq, hx2, Pi.smul_apply, smul_eq_mul]
    calc ENNReal.ofReal (1 / (1 - tvDist P Q)) * (P ⊓ Q).rnDeriv P x
        ≤ ENNReal.ofReal (1 / (1 - tvDist P Q)) * 1 := by gcongr; exact hx1
      _ = _ := mul_one _

/-- A member of `trimSet P α` is bounded by `(1−α)⁻¹ P`. -/
theorem le_smul_of_mem_trimSet {α : ℝ} {R : Measure 𝒳} (hR : R ∈ StatFormal.Wave8a.trimSet P α) :
    R ≤ ENNReal.ofReal (1 / (1 - α)) • P := by
  obtain ⟨hRp, hac, hle⟩ := hR
  rw [← Measure.withDensity_rnDeriv_eq R P hac, ← withDensity_const]
  exact withDensity_mono hle

/-- `R*` is the only common `α*`-trimming. -/
theorem eq_contactLaw (htv : tvDist P Q < 1) {R : Measure 𝒳}
    (hRP : R ∈ StatFormal.Wave8a.trimSet P (tvDist P Q)) (hRQ : R ∈ StatFormal.Wave8a.trimSet Q (tvDist P Q)) :
    R = StatFormal.Wave30tx.contactLaw P Q := by
  have : IsProbabilityMeasure R := hRP.1
  have := contactLaw_isProb P Q htv
  set c := ENNReal.ofReal (1 / (1 - tvDist P Q)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Ne, ENNReal.ofReal_eq_zero, not_le]
    have : 0 < 1 - tvDist P Q := by linarith
    positivity
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hP := smul_le_smul_measure (le_smul_of_mem_trimSet P hRP) c⁻¹
  have hQ := smul_le_smul_measure (le_smul_of_mem_trimSet Q hRQ) c⁻¹
  rw [← hc, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul] at hP hQ
  have hle : R ≤ StatFormal.Wave30tx.contactLaw P Q := by
    have := smul_le_smul_measure (le_inf hP hQ) c
    rwa [smul_smul, ENNReal.mul_inv_cancel hc0 hct, one_smul] at this
  exact eq_of_le_of_univ hle (by rw [measure_univ, measure_univ])

end Measures

section Regions

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The embedding of an `α`-trimming lies in the region. -/
theorem mem_region_of_trimSet (P : Measure 𝒳) [IsProbabilityMeasure P] (φ : 𝒳 → H) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {R : Measure 𝒳} (hR : R ∈ StatFormal.Wave8a.trimSet P α) :
    ∫ x, φ x ∂R ∈ region φ α P := by
  obtain ⟨hRp, hac, hle⟩ := hR
  have hB : 0 < 1 / (1 - α) := by have : 0 < 1 - α := by linarith
                                  positivity
  set g : 𝒳 → ℝ := fun x => min (R.rnDeriv P x).toReal (1 / (1 - α)) with hg
  have hgm : Measurable g := (Measure.measurable_rnDeriv R P).ennreal_toReal.min measurable_const
  have hae : ∀ᵐ x ∂P, g x = (R.rnDeriv P x).toReal := by
    filter_upwards [hle] with x hx
    exact min_eq_left (ENNReal.toReal_le_of_le_ofReal hB.le hx)
  refine ⟨g, hgm, fun x => ⟨le_min ENNReal.toReal_nonneg hB.le, min_le_right _ _⟩, ?_, ?_⟩
  · rw [integral_congr_ae hae, Measure.integral_toReal_rnDeriv hac, probReal_univ]
  · have h2 : ∫ x, g x • φ x ∂P = ∫ x, (R.rnDeriv P x).toReal • φ x ∂P :=
      integral_congr_ae (hae.mono fun x hx => by simp only [hx])
    rw [h2, integral_rnDeriv_smul hac]

/-- The trimmed regions are totally bounded. -/
theorem totallyBounded_region (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ α : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα1 : α < 1) : TotallyBounded (region φ α P) := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x₀)
  have h1α : 0 < 1 - α := by linarith
  set B := 1 / (1 - α) with hBdef
  have hB : 0 < B := by positivity
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set s := hφ.approxBounded κ with hs
  have hconv : Tendsto (fun n => ∫ x, ‖φ x - s n x‖ ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := P) (F := fun n x => ‖φ x - s n x‖)
      (f := fun _ => (0 : ℝ)) (fun _ => 2 * κ)
      (fun n => (hφ.sub (s n).stronglyMeasurable).norm.aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_norm]
        refine (norm_sub_le _ _).trans ?_
        linarith [hκ x, StronglyMeasurable.norm_approxBounded_le hφ hκ0 n x])
      (ae_of_all _ fun x => by
        have := ((hφ.tendsto_approxBounded_of_norm_le (hκ x)).const_sub (φ x)).norm
        simpa using this)
    simpa using h
  have hpos : 0 < ε / (2 * B) := by positivity
  obtain ⟨N, hN⟩ := (hconv.eventually (gt_mem_nhds hpos)).exists
  set S := s N with hSdef
  set L : (S.range → ℝ) → H := fun c => ∑ v : S.range, c v • (v : H) with hLdef
  have hL : Continuous L := by
    simp only [hLdef]
    exact continuous_finsetSum _ fun v _ => (continuous_apply v).smul continuous_const
  set box : Set (S.range → ℝ) := Set.pi univ fun _ => Icc (0 : ℝ) 1 with hbox
  have hboxc : IsCompact box := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨t, htf, ht⟩ := Metric.totallyBounded_iff.1 (hboxc.image hL).totallyBounded (ε / 2) (by positivity)
  refine ⟨t, htf, ?_⟩
  rintro z ⟨g, hgm, hgb, hg1, rfl⟩
  have hgi : Integrable g P := Integrable.of_mem_Icc 0 B hgm.aemeasurable (ae_of_all _ fun x => hgb x)
  set c : S.range → ℝ := fun v => ∫ x, ({y | S y = (v : H)}.indicator g) x ∂P with hcdef
  have hfib : ∀ v : H, MeasurableSet {y | S y = v} := fun v => S.measurableSet_fiber v
  have hci : ∀ v : S.range, Integrable ({y | S y = (v : H)}.indicator g) P :=
    fun v => hgi.indicator (hfib v)
  have hcbox : c ∈ box := by
    intro v _
    refine ⟨integral_nonneg fun x => ?_, ?_⟩
    · by_cases hx : x ∈ {y | S y = (v : H)}
      · rw [Set.indicator_of_mem hx]; exact (hgb x).1
      · simp [Set.indicator_of_notMem hx]
    · rw [← hg1]
      refine integral_mono (hci v) hgi fun x => ?_
      by_cases hx : x ∈ {y | S y = (v : H)}
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]; exact (hgb x).1
  have hpt : ∀ x, g x • S x = ∑ v : S.range, ({y | S y = (v : H)}.indicator g x) • (v : H) := by
    intro x
    rw [Finset.sum_eq_single (⟨S x, S.mem_range_self x⟩ : S.range)]
    · rw [Set.indicator_of_mem (show x ∈ {y | S y = S x} from rfl)]
    · intro v _ hv
      have : x ∉ {y | S y = (v : H)} := fun h => hv (Subtype.ext h.symm)
      rw [Set.indicator_of_notMem this, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hLc : L c = ∫ x, g x • S x ∂P := by
    simp_rw [hpt]
    rw [integral_finsetSum _ fun v _ => (hci v).smul_const _]
    simp only [hLdef, hcdef]
    refine Finset.sum_congr rfl fun v _ => (integral_smul_const _ _).symm
  have hgφ : Integrable (fun x => g x • φ x) P := integrable_smul_of_bound hφ hκ hgi
  have hgS : Integrable (fun x => g x • S x) P :=
    integrable_smul_of_bound (S.stronglyMeasurable) (fun x => StronglyMeasurable.norm_approxBounded_le hφ hκ0 N x) hgi
  have hdist : ‖∫ x, g x • φ x ∂P - L c‖ < ε / 2 := by
    rw [hLc, ← integral_sub hgφ hgS]
    have hn : Integrable (fun x => ‖φ x - S x‖) P := by
      refine Integrable.of_bound (hφ.sub S.stronglyMeasurable).norm.aestronglyMeasurable (2 * κ)
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_norm]
      refine (norm_sub_le _ _).trans ?_
      linarith [hκ x, StronglyMeasurable.norm_approxBounded_le hφ hκ0 N x]
    calc ‖∫ x, (g x • φ x - g x • S x) ∂P‖ ≤ ∫ x, ‖g x • φ x - g x • S x‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ x, B * ‖φ x - S x‖ ∂P := by
          refine integral_mono (hgφ.sub hgS).norm (hn.const_mul B) fun x => ?_
          rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hgb x).1]
          exact mul_le_mul_of_nonneg_right (hgb x).2 (norm_nonneg _)
      _ = B * ∫ x, ‖φ x - S x‖ ∂P := integral_const_mul _ _
      _ < B * (ε / (2 * B)) := mul_lt_mul_of_pos_left hN hB
      _ = ε / 2 := by field_simp
  obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.1 (ht ⟨c, hcbox, rfl⟩)
  refine Set.mem_iUnion₂.2 ⟨y, hyt, ?_⟩
  rw [Metric.mem_ball] at hy ⊢
  rw [dist_eq_norm] at hy ⊢
  calc ‖∫ x, g x • φ x ∂P - y‖ ≤ ‖∫ x, g x • φ x ∂P - L c‖ + ‖L c - y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hdist hy
    _ = ε := by ring

end Regions

theorem contact_compact : StatFormal.Wave30tx.Claims.contact_compact := by
  intro 𝒳 H _ _ _ _ _ P _ φ κ α hφ hκ hα0 hα1
  exact (totallyBounded_region P hφ hκ hα1).isCompact_of_isClosed
    (StatFormal.Wave11b.attain_closed 𝒳 H P φ κ α hφ hκ hα0 hα1)

theorem contact : StatFormal.Wave30tx.Claims.contact := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ hφ hκ hchar htv
  set T := tvDist P Q with hTdef
  have hT0 : 0 ≤ T := tvDist_nonneg P Q
  have htv' : tvDist Q P < 1 := by rwa [tvDist_comm]
  have hmemP := contactLaw_mem_trimSet P Q htv
  have hmemQ : StatFormal.Wave30tx.contactLaw P Q ∈ StatFormal.Wave8a.trimSet Q T := by
    have := contactLaw_mem_trimSet Q P htv'
    rwa [contactLaw_comm, tvDist_comm Q P] at this
  set μs := ∫ x, φ x ∂(StatFormal.Wave30tx.contactLaw P Q) with hμs
  have hinter : region φ T P ∩ region φ T Q = {μs} := by
    ext z
    constructor
    · intro hz
      obtain ⟨R, hR, hRz⟩ := StatFormal.Wave11b.attain_common 𝒳 H P Q φ κ T hφ hκ hchar hT0 htv z hz
      rw [eq_contactLaw P Q htv hR.1 hR.2] at hRz
      exact hRz.symm
    · rintro rfl
      exact ⟨mem_region_of_trimSet P φ hT0 htv hmemP, mem_region_of_trimSet Q φ hT0 htv hmemQ⟩
  refine ⟨⟨⟨inf_le_left, inf_le_right⟩, fun μ hμ => le_inf hμ.1 hμ.2⟩, inf_univ P Q, ⟨hmemP, hmemQ⟩,
    fun R hR => eq_contactLaw P Q htv hR.1 hR.2, hinter, ?_⟩
  -- `ω_c(ε) → 0`
  set C := region φ T P with hC
  set CQ := region φ T Q with hCQ
  have hCc : IsCompact C := contact_compact 𝒳 H P φ κ T hφ hκ hT0 htv
  have hCQc : IsClosed CQ := StatFormal.Wave11b.attain_closed 𝒳 H Q φ κ T hφ hκ hT0 htv
  have hCQne : CQ.Nonempty := ⟨μs, (hinter.symm ▸ mem_singleton μs : μs ∈ C ∩ CQ).2⟩
  have hω0 : ∀ ε, 0 ≤ StatFormal.Wave30tx.omegaC φ P Q ε :=
    fun ε => Real.sSup_nonneg fun r ⟨a, _, _, hr⟩ => hr ▸ norm_nonneg _
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  set K := C ∩ {a | η / 2 ≤ ‖a - μs‖} with hK
  have hKc : IsCompact K :=
    hCc.inter_right (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
  -- a positive gap `ε₀` such that `infDist a CQ < ε₀` forces `‖a − μ_{R*}‖ < η/2` on `C`
  obtain ⟨ε₀, hε₀, hgap⟩ : ∃ ε₀ > 0, ∀ a ∈ C, Metric.infDist a CQ < ε₀ → ‖a - μs‖ < η / 2 := by
    by_cases hKne : K.Nonempty
    · obtain ⟨a₀, ha₀, hmin⟩ := hKc.exists_isMinOn hKne (Metric.continuous_infDist_pt CQ).continuousOn
      refine ⟨Metric.infDist a₀ CQ, ?_, fun a ha hd => ?_⟩
      · rcases (Metric.infDist_nonneg (x := a₀) (s := CQ)).lt_or_eq with h | h
        · exact h
        · exfalso
          have hmem : a₀ ∈ CQ := (hCQc.mem_iff_infDist_zero hCQne).2 h.symm
          have : a₀ ∈ C ∩ CQ := ⟨ha₀.1, hmem⟩
          rw [hinter, mem_singleton_iff] at this
          have h2 := ha₀.2
          simp only [mem_ofPred_eq, this, sub_self, norm_zero] at h2
          linarith
      · by_contra hc
        push Not at hc
        have := hmin ⟨ha, hc⟩
        simp only [mem_ofPred_eq] at this
        linarith
    · refine ⟨1, one_pos, fun a ha _ => ?_⟩
      by_contra hc
      push Not at hc
      exact hKne ⟨a, ha, hc⟩
  refine ⟨ε₀, hε₀, fun {ε} hε hdist => ?_⟩
  have hε' : ε < ε₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε] at hdist; exact hdist
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hω0 ε)]
  refine lt_of_le_of_lt (Real.sSup_le ?_ (by positivity)) (half_lt_self hη)
  rintro r ⟨a, ha, hd, rfl⟩
  exact (hgap a ha (lt_of_le_of_lt hd hε')).le

theorem nearcontact_densities : StatFormal.Wave30tx.Claims.nearcontact_densities := by
  intro 𝒳 _ μ _ p q hp hq hp0 hq0 hPp hQp P Q βs htv
  have hT0 : 0 ≤ tvDist P Q := tvDist_nonneg P Q
  have h1 : 0 < 1 - tvDist P Q := by linarith
  have hβ : 0 < βs := by simp only [βs]; positivity
  set c := ENNReal.ofReal βs with hc
  set h : 𝒳 → ℝ := fun x => βs * min (p x) (q x) / p x with hh
  have hhm : Measurable h := (measurable_const.mul (hp.min hq)).div hp
  have hh0 : ∀ x, 0 ≤ h x := fun x => div_nonneg (mul_nonneg hβ.le (le_min (hp0 x) (hq0 x))) (hp0 x)
  -- `R* = P.withDensity h`
  have hR : StatFormal.Wave30tx.contactLaw P Q = P.withDensity (fun x => ENNReal.ofReal (h x)) := by
    rw [contactLaw_eq, withDensity_inf μ hp.ennreal_ofReal hq.ennreal_ofReal,
      ← withDensity_smul _ (hp.ennreal_ofReal.min hq.ennreal_ofReal),
      ← withDensity_mul μ hp.ennreal_ofReal hhm.ennreal_ofReal]
    congr 1
    funext x
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (hp0 x)]
    have hmin : min (ENNReal.ofReal (p x)) (ENNReal.ofReal (q x)) = ENNReal.ofReal (min (p x) (q x)) :=
      (Monotone.map_min (fun a b hab => ENNReal.ofReal_le_ofReal hab)).symm
    rw [hmin, ← ENNReal.ofReal_mul hβ.le]
    congr 1
    rcases (hp0 x).lt_or_eq with hpx | hpx
    · simp only [hh]; field_simp
    · simp only [hh, ← hpx, div_zero, mul_zero]
      rw [min_eq_left (hq0 x), mul_zero]
  have hrn : ∀ᵐ x ∂P, ((StatFormal.Wave30tx.contactLaw P Q).rnDeriv P x).toReal = h x := by
    rw [hR]
    filter_upwards [Measure.rnDeriv_withDensity P hhm.ennreal_ofReal] with x hx
    rw [hx, ENNReal.toReal_ofReal (hh0 x)]
  have hpos : ∀ᵐ x ∂P, 0 < p x := by
    rw [ae_iff]
    have hset : {x | ¬ 0 < p x} = {x | p x ≤ 0} := by ext x; simp
    rw [hset]
    show (μ.withDensity fun x => ENNReal.ofReal (p x)) {x | p x ≤ 0} = 0
    rw [withDensity_apply _ (measurableSet_le hp measurable_const)]
    refine (setLIntegral_congr_fun (measurableSet_le hp measurable_const) fun x hx => ?_).trans
      (lintegral_zero)
    exact ENNReal.ofReal_eq_zero.2 hx
  refine ⟨hrn, ?_, ?_⟩
  · filter_upwards [hrn, hpos] with x hx hpx
    rw [hx]
    simp only [hh]
    rcases le_total (p x) (q x) with hpq | hqp
    · rw [min_eq_left hpq, mul_div_assoc, div_self hpx.ne', mul_one]
      constructor
      · rintro ⟨_, h⟩; exact absurd h (lt_irrefl _)
      · rintro ⟨_, h⟩; linarith
    · rw [min_eq_right hqp]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · by_contra hq'
          push Not at hq'
          have : q x = 0 := le_antisymm hq' (hq0 x)
          rw [this, mul_zero, zero_div] at h1
          exact lt_irrefl _ h1
        · rw [div_lt_iff₀ hpx] at h2
          nlinarith
      · rintro ⟨h1, h2⟩
        exact ⟨by positivity, by rw [div_lt_iff₀ hpx]; nlinarith⟩
  · filter_upwards [hrn] with x hx hpx hpq
    rw [hx]
    simp only [hh]
    rw [min_eq_left hpq, mul_div_assoc, div_self hpx.ne', mul_one]

end StatFormal.Wave30tx.RContact
