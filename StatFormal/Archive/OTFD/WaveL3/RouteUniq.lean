import StatFormal.Archive.OTFD.WaveL3.RouteBrenierH
import TauCeti.MeasureTheory.OptimalTransport.Duality.SchachermayerTeichmann
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# Route (wave L3): uniqueness of cyclically monotone couplings under a pairing bound

Untrusted route file. Generalises the library proof of
`StatFormal.Potentials.exists_eq_graphPlan_of_lipNull` (AGS Thm 6.2.10) from finite second
moments to any **integrable pairing bound** `|⟪x, y⟫| ≤ a(x) + b(y)` on closed sets `A × B`
carrying the marginals: the cost `c = (a(x) + b(y) − ⟪x, y⟫)₊` is finite and continuous, a
cyclically monotone (paper form) coupling is `c`-cyclically monotone on `A × B`, hence
`c`-optimal (Schachermayer–Teichmann, Tau Ceti); the sum of two such couplings is optimal, its
support (cut to `A × B`) is a monotone set, single-valued off a union of countably many Lipschitz
hypersurfaces (library), so both couplings are the same graph plan.

Instances: bounded target with a first moment of the source (`a = D‖x‖`, `b = 0`), bounded source
with a first moment of the target (`a = 0`, `b = D‖y‖`; otfd C, `W₁` targets). In finite
dimension, laws `≪` Lebesgue are null on Lipschitz hypersurfaces (`lipNull_of_ac`, Fubini along
lines).
-/

open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL3

open StatFormal.OTFD.WaveL1

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- The shifted pairing cost `(a(x) + b(y) − ⟪x, y⟫)₊`. -/
noncomputable def bcost (a b : H → ℝ) : H × H → ℝ≥0∞ :=
  fun z => ENNReal.ofReal (a z.1 + b z.2 - ⟪z.1, z.2⟫)

theorem continuous_bcost {a b : H → ℝ} (ha : Continuous a) (hb : Continuous b) :
    Continuous (bcost a b) :=
  ENNReal.continuous_ofReal.comp (((ha.comp continuous_fst).add (hb.comp continuous_snd)).sub
    (continuous_fst.inner continuous_snd))

variable {A B : Set H} {a b : H → ℝ}

theorem bcost_arg_nonneg (hab : ∀ x ∈ A, ∀ y ∈ B, |⟪x, y⟫| ≤ a x + b y) {x y : H} (hx : x ∈ A)
    (hy : y ∈ B) : 0 ≤ a x + b y - ⟪x, y⟫ := by
  have := hab x hx y hy
  have := le_abs_self ⟪x, y⟫
  linarith

/-- A cyclically monotone set inside `A × B` is `c`-cyclically monotone. -/
theorem isCyclicallyMonotone_bcost (hab : ∀ x ∈ A, ∀ y ∈ B, |⟪x, y⟫| ≤ a x + b y)
    {Γ : Set (H × H)} (hΓ : CycMon Γ) (hΓAB : Γ ⊆ A ×ˢ B) :
    IsCyclicallyMonotone (bcost a b) Γ := by
  have hpair := isCyclicallyMonotone_norm_sub_sq_div_two_iff_forall_sum_inner_le.1
    (isCyclicallyMonotone_of_cycMon hΓ)
  intro n x y hxy σ
  have hA : ∀ i, x i ∈ A := fun i => (hΓAB (hxy i)).1
  have hB : ∀ i, y i ∈ B := fun i => (hΓAB (hxy i)).2
  simp only [bcost]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => bcost_arg_nonneg hab (hA i) (hB i)),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => bcost_arg_nonneg hab (hA i) (hB (σ i)))]
  apply ENNReal.ofReal_le_ofReal
  have h1 := hpair n x y hxy σ
  have h2 : ∑ i, b (y (σ i)) = ∑ i, b (y i) := Equiv.sum_comp σ (fun i => b (y i))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith

theorem ae_mem_prod {π : Measure (H × H)} {μ ν : Measure H} (hπ : IsCoupling π μ ν)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0) :
    ∀ᵐ z ∂π, z ∈ A ×ˢ B := by
  have h1 : π (Prod.fst ⁻¹' Aᶜ) = 0 := by rw [← Measure.fst_apply hA.compl, hπ.fst_eq, hμA]
  have h2 : π (Prod.snd ⁻¹' Bᶜ) = 0 := by rw [← Measure.snd_apply hB.compl, hπ.snd_eq, hνB]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1, measure_eq_zero_iff_ae_notMem.1 h2]
    with z hz1 hz2
  exact ⟨by simpa using hz1, by simpa using hz2⟩

theorem lintegral_bcost_le {π : Measure (H × H)} {μ ν : Measure H} (hπ : IsCoupling π μ ν)
    (hab : ∀ x ∈ A, ∀ y ∈ B, |⟪x, y⟫| ≤ a x + b y) (hAB : ∀ᵐ z ∂π, z ∈ A ×ˢ B)
    (ha : Measurable a) (hb : Measurable b) :
    ∫⁻ z, bcost a b z ∂π ≤
      2 * ∫⁻ x, ENNReal.ofReal (a x) ∂μ + 2 * ∫⁻ y, ENNReal.ofReal (b y) ∂ν := by
  have hle : ∀ᵐ z ∂π, bcost a b z ≤
      2 * ENNReal.ofReal (a z.1) + 2 * ENNReal.ofReal (b z.2) := by
    filter_upwards [hAB] with z hz
    have h0 := hab z.1 hz.1 z.2 hz.2
    have h1 := neg_abs_le ⟪z.1, z.2⟫
    calc bcost a b z ≤ ENNReal.ofReal (2 * a z.1 + 2 * b z.2) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ ENNReal.ofReal (2 * a z.1) + ENNReal.ofReal (2 * b z.2) := ENNReal.ofReal_add_le
      _ = _ := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
          norm_num
  refine (lintegral_mono_ae hle).trans_eq ?_
  rw [lintegral_add_left (f := fun z : H × H => 2 * ENNReal.ofReal (a z.1)) (by fun_prop),
    lintegral_const_mul 2 (f := fun z : H × H => ENNReal.ofReal (a z.1)) (by fun_prop),
    lintegral_const_mul 2 (f := fun z : H × H => ENNReal.ofReal (b z.2)) (by fun_prop),
    ← hπ.fst_eq, ← hπ.snd_eq, Measure.fst, Measure.snd,
    lintegral_map ha.ennreal_ofReal measurable_fst, lintegral_map hb.ennreal_ofReal measurable_snd]

/-- **Uniqueness of cyclically monotone couplings under an integrable pairing bound**, for a
source null on Lipschitz hypersurfaces. -/
theorem eq_of_cmConc_of_bound {μ ν : Measure H} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ S : Set H, StatFormal.Potentials.IsLipGraph S → μ S = 0) (hAc : IsClosed A)
    (hBc : IsClosed B) (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0) (ha : Continuous a) (hb : Continuous b)
    (hab : ∀ x ∈ A, ∀ y ∈ B, |⟪x, y⟫| ≤ a x + b y)
    (hai : ∫⁻ x, ENNReal.ofReal (a x) ∂μ ≠ ∞) (hbi : ∫⁻ y, ENNReal.ofReal (b y) ∂ν ≠ ∞)
    {π₁ π₂ : Measure (H × H)} (h₁ : IsCoupling π₁ μ ν) (h₂ : IsCoupling π₂ μ ν)
    (hc₁ : CMConc π₁) (hc₂ : CMConc π₂) : π₁ = π₂ := by
  set c := bcost a b with hcdef
  have hcc : Continuous c := continuous_bcost ha hb
  have hAB : ∀ π, IsCoupling π μ ν → ∀ᵐ z ∂π, z ∈ A ×ˢ B := fun π hπ =>
    ae_mem_prod hπ hAc.measurableSet hBc.measurableSet hμA hνB
  have hopt : ∀ π, IsCoupling π μ ν → CMConc π → IsOptimalCoupling c π μ ν := by
    intro π hπ ⟨Γ, _, hΓ, hΓ0⟩
    refine hπ.isOptimalCoupling_of_isCyclicallyMonotone hcc.measurable
      (fun z => ENNReal.ofReal_ne_top)
      (isCyclicallyMonotone_bcost hab (cycMon_mono hΓ inter_subset_left) inter_subset_right) ?_
    filter_upwards [hAB π hπ, measure_eq_zero_iff_ae_notMem.1 hΓ0] with z hz hz'
    exact ⟨Set.notMem_compl_iff.1 hz', hz⟩
  have hfin : ∀ π, IsCoupling π μ ν → ∫⁻ z, c z ∂π ≠ ∞ := fun π hπ =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top hai,
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top hbi⟩)
      (lintegral_bcost_le hπ hab (hAB π hπ) ha.measurable hb.measurable)
  have o₁ := hopt π₁ h₁ hc₁
  have o₂ := hopt π₂ h₂ hc₂
  have hsum := o₁.add o₂
  have hfin' : transportCost c (μ + μ) (ν + ν) ≠ ∞ := by
    rw [← hsum.lintegral_eq, lintegral_add_measure]
    exact ENNReal.add_ne_top.2 ⟨hfin π₁ h₁, hfin π₂ h₂⟩
  have hcm := hsum.isCyclicallyMonotone_support hcc hfin'
  set Γ := (π₁ + π₂).support ∩ A ×ˢ B with hΓdef
  have hΓm : MeasurableSet Γ :=
    (Measure.isClosed_support.inter (hAc.prod hBc)).measurableSet
  have hmono : StatFormal.Potentials.IsMonotoneSet Γ := by
    intro p hp q hq
    have hsw := (hcm.mono (inter_subset_left : Γ ⊆ _)).add_le_add_swap
      (x₁ := p.1) (y₁ := p.2) (x₂ := q.1) (y₂ := q.2) hp hq
    have n1 := bcost_arg_nonneg hab hp.2.1 hp.2.2
    have n2 := bcost_arg_nonneg hab hq.2.1 hq.2.2
    have n3 := bcost_arg_nonneg hab hp.2.1 hq.2.2
    have n4 := bcost_arg_nonneg hab hq.2.1 hp.2.2
    simp only [hcdef, bcost] at hsw
    rw [← ENNReal.ofReal_add n1 n2, ← ENNReal.ofReal_add n3 n4,
      ENNReal.ofReal_le_ofReal_iff (add_nonneg n3 n4)] at hsw
    have e : ⟪p.2 - q.2, p.1 - q.1⟫ =
        ⟪p.1, p.2⟫ + ⟪q.1, q.2⟫ - ⟪p.1, q.2⟫ - ⟪q.1, p.2⟫ := by
      simp only [inner_sub_left, inner_sub_right, real_inner_comm p.1, real_inner_comm q.1]
      ring
    rw [e]
    linarith
  have hM := StatFormal.Potentials.measure_multivaluedSet_eq_zero hμ hmono
  have hae : ∀ᵐ z ∂(π₁ + π₂), z ∈ (π₁ + π₂).support := Measure.support_mem_ae
  have : IsFiniteMeasure π₁ := h₁.isFiniteMeasure
  have : IsFiniteMeasure π₂ := h₂.isFiniteMeasure
  have hae₁ : ∀ᵐ z ∂π₁, z ∈ Γ := by
    filter_upwards [ae_mono (Measure.le_add_right le_rfl) hae, hAB π₁ h₁] with z h h' using ⟨h, h'⟩
  have hae₂ : ∀ᵐ z ∂π₂, z ∈ Γ := by
    filter_upwards [ae_mono (Measure.le_add_left le_rfl) hae, hAB π₂ h₂] with z h h' using ⟨h, h'⟩
  obtain ⟨T, -, hπT, hTΓ⟩ := StatFormal.Potentials.exists_eq_graphPlan_of_ae_mem h₁ hΓm hae₁ hM
  obtain ⟨T', -, hπT', hTΓ'⟩ := StatFormal.Potentials.exists_eq_graphPlan_of_ae_mem h₂ hΓm hae₂ hM
  have hTT' : T =ᵐ[μ] T' := by
    filter_upwards [hTΓ, hTΓ', measure_eq_zero_iff_ae_notMem.1 hM] with x h1 h2 hx
    by_contra hne
    exact hx ⟨_, _, h1, h2, hne⟩
  rw [hπT, hπT', graphPlan_congr hTT']

/-- `BrenierUniq` from the pairing bound. -/
theorem brenierUniq_of_bound {μ ν : Measure H} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ S : Set H, StatFormal.Potentials.IsLipGraph S → μ S = 0) (hAc : IsClosed A)
    (hBc : IsClosed B) (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0) (ha : Continuous a) (hb : Continuous b)
    (hab : ∀ x ∈ A, ∀ y ∈ B, |⟪x, y⟫| ≤ a x + b y)
    (hai : ∫⁻ x, ENNReal.ofReal (a x) ∂μ ≠ ∞) (hbi : ∫⁻ y, ENNReal.ofReal (b y) ∂ν ≠ ∞)
    {F : H → H} (hF : Measurable F) (hmap : μ.map F = ν) (hcm : IsCMMapAE μ F) :
    BrenierUniq μ ν F := fun π _ hfst hsnd hcmπ =>
  eq_of_cmConc_of_bound hμ hAc hBc hμA hνB ha hb hab hai hbi ⟨hfst, hsnd⟩
    (isCoupling_graph hF hmap) hcmπ (cmConc_graph hF hcm)

theorem nonneg_of_ball {μ : Measure H} [IsProbabilityMeasure μ] {D : ℝ}
    (h : μ (Metric.closedBall 0 D)ᶜ = 0) : 0 ≤ D := by
  by_contra hD
  rw [Metric.closedBall_eq_empty.2 (not_le.1 hD), compl_empty, measure_univ] at h
  exact one_ne_zero h

theorem lintegral_ofReal_mul_norm (ν : Measure H) {D : ℝ} (hD : 0 ≤ D) :
    ∫⁻ y, ENNReal.ofReal (D * ‖y‖) ∂ν = ENNReal.ofReal D * ∫⁻ y, ‖y‖ₑ ∂ν := by
  simp_rw [ENNReal.ofReal_mul hD, ofReal_norm_eq_enorm]
  exact lintegral_const_mul _ measurable_enorm

/-- **Bounded source, first moment of the target** (otfd C: `μ_K` carried by a ball, `W₁`
targets): uniqueness of cyclically monotone couplings. -/
theorem brenierUniq_of_bdd_source {μ ν : Measure H} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : LipNull μ) {D : ℝ} (hμD : μ (Metric.closedBall 0 D)ᶜ = 0)
    (hν1 : ∫⁻ y, ‖y‖ₑ ∂ν ≠ ∞) {F : H → H} (hF : Measurable F) (hmap : μ.map F = ν)
    (hcm : IsCMMapAE μ F) : BrenierUniq μ ν F := by
  have hD := nonneg_of_ball hμD
  refine brenierUniq_of_bound (a := fun _ => 0) (b := fun y => D * ‖y‖) (lipGraph_null hμ)
    Metric.isClosed_closedBall isClosed_univ hμD
    (by simp) continuous_const (continuous_const.mul continuous_norm)
    (fun x hx y _ => ?_) (by simp) ?_ hF hmap hcm
  · rw [Metric.mem_closedBall, dist_zero_right] at hx
    calc |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
      _ ≤ D * ‖y‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      _ = 0 + D * ‖y‖ := by ring
  · rw [lintegral_ofReal_mul_norm ν hD]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hν1

/-- **Bounded target, first moment of the source** (otfd A `lem:plan-stability-H` with `supp μ`
bounded): uniqueness of cyclically monotone couplings. -/
theorem brenierUniq_of_bdd_target {P μ : Measure H} [IsProbabilityMeasure P]
    [IsProbabilityMeasure μ] (hP : LipNull P) {D : ℝ} (hμD : μ (Metric.closedBall 0 D)ᶜ = 0)
    (hP1 : ∫⁻ x, ‖x‖ₑ ∂P ≠ ∞) {F : H → H} (hF : Measurable F) (hmap : P.map F = μ)
    (hcm : IsCMMapAE P F) : BrenierUniq P μ F := by
  have hD := nonneg_of_ball hμD
  refine brenierUniq_of_bound (a := fun x => D * ‖x‖) (b := fun _ => 0) (lipGraph_null hP)
    isClosed_univ Metric.isClosed_closedBall
    (by simp) hμD (continuous_const.mul continuous_norm) continuous_const
    (fun x _ y hy => ?_) ?_ (by simp) hF hmap hcm
  · rw [Metric.mem_closedBall, dist_zero_right] at hy
    calc |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
      _ ≤ ‖x‖ * D := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ = D * ‖x‖ + 0 := by ring
  · rw [lintegral_ofReal_mul_norm P hD]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP1

end General

section FD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Lipschitz hypersurfaces are Haar-null** in finite dimension (Fubini along the direction
`w`: each line `y + ℝ w` meets `A_w(τ)` in at most one point). -/
theorem addHaar_lipGraph_eq_zero (ρ : Measure E) [ρ.IsAddHaarMeasure] {S : Set E}
    (hS : StatFormal.Potentials.IsLipGraph S) : ρ S = 0 := by
  obtain ⟨w, hw, τ, ⟨L, hτ⟩, rfl⟩ := hS
  set c : ℝ := ‖w‖ ^ 2 with hc
  have hc0 : c ≠ 0 := by have := norm_pos_iff.2 hw; positivity
  set a : E → ℝ := fun x => ⟪x, w⟫ / c with ha
  set pr : E → E := fun x => x - a x • w with hpr
  have hpr_w : ∀ x, ⟪pr x, w⟫ = 0 := by
    intro x
    simp only [hpr, ha, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hacont : Continuous a := (continuous_id.inner continuous_const).div_const _
  have hprcont : Continuous pr := continuous_id.sub (hacont.smul continuous_const)
  have hτpr : Continuous fun x => τ (pr x) :=
    hτ.continuousOn.comp_continuous hprcont fun x => hpr_w x
  set T : Set E := {x | a x = τ (pr x)} with hT
  have hTc : IsClosed T := isClosed_eq hacont hτpr
  have hsub : StatFormal.Potentials.lipGraph w τ ⊆ T := by
    rintro x ⟨z, hz, rfl⟩
    have h1 : a (z + τ z • w) = τ z := by
      simp only [ha, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hz]
      field_simp
      rw [hc]; ring
    have h2 : pr (z + τ z • w) = z := by simp only [hpr, h1]; abel
    show a (z + τ z • w) = τ (pr (z + τ z • w))
    rw [h1, h2]
  refine measure_mono_null hsub ?_
  let Lw : ℝ →ₗ[ℝ] E := LinearMap.toSpanSingleton ℝ E w
  have hline : ∀ y : E, ∀ᵐ t ∂(volume : Measure ℝ), y + Lw t ∈ Tᶜ := by
    intro y
    have hsing : {t : ℝ | y + Lw t ∈ T} ⊆ {τ (pr y) - a y} := by
      intro t ht
      have hat : a (y + t • w) = a y + t := by
        simp only [ha, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp
        rw [hc]
      have hprt : pr (y + t • w) = pr y := by
        simp only [hpr, hat, add_smul]; abel
      have ht' : a (y + t • w) = τ (pr (y + t • w)) := ht
      rw [hat, hprt] at ht'
      simp only [mem_singleton_iff]
      linarith
    have h0 : (volume : Measure ℝ) {t : ℝ | y + Lw t ∈ T} = 0 :=
      measure_mono_null hsing (measure_singleton _)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with t ht
    exact ht
  have := ae_mem_of_ae_add_linearMap_mem Lw volume ρ hTc.measurableSet.compl hline
  exact measure_eq_zero_iff_ae_notMem.2 (this.mono fun _ h => h)

/-- A law absolutely continuous w.r.t. a Haar measure is null on Lipschitz hypersurfaces. -/
theorem lipNull_of_ac {ρ : Measure E} [ρ.IsAddHaarMeasure] {μ : Measure E} (hμ : μ ≪ ρ) :
    LipNull μ := fun S hS => hμ (addHaar_lipGraph_eq_zero ρ hS)

end FD

end StatFormal.OTFD.WaveL3
