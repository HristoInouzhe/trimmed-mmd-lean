import StatFormal.Archive.Wave29l.Statements
import StatFormal.Archive.Wave29l.RouteBootSE
import StatFormal.Lib.Bootstrap.Percentile

/-!
# Route — TM `thm:split` with the percentile bootstrap (untrusted)

* `split_boot_clt`: `Foundations/Bootstrap/{CharFun,Clt,CltProb}` — characteristic functions of the bootstrap law
  of the root factorise over the two independent resamples and over the draws; the triangular-array limit
  `tendsto_cAvg_pow`, the duality remainder bound and Lévy's continuity theorem give the sequential bootstrap CLT,
  made uniform by contradiction and turned into convergence in probability by the plug-in consistency of Wave 29i.
* `split_perc_check` (route, not a target): frozen `Wave29i.split_asymp_normal` + `split_boot_clt` + frozen
  `Wave22c.split_level` ⇒ `split_boot_percentile` (`Foundations/Bootstrap/Percentile`: counting replicates below
  `T₀` on the event `√n(T₀ − T̂) ≥ σ(θ − z)`); `split_boot_percentile` is that route applied to the certified
  theorems.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatFormal.Wave29l

open StatFormal.Foundations.Bootstrap StatFormal.Foundations.TrimmedMean StatFormal.Foundations.CLT
open StatFormal.TrimmedMMD.BangBang
open StatFormal.Wave17a (sepVal)
open StatFormal.TrimmedMMD.Concentration (region)

lemma splitBootCdf_eq (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) (t : ℝ) :
    splitBootCdf n m α vx vy t = bAvg (fun p => if bootRoot n m α vx vy p ≤ t then (1 : ℝ) else 0) := by
  have hc : (Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) : ℝ) = (n : ℝ) ^ n * (m : ℝ) ^ m := by
    simp [Fintype.card_prod]
  unfold splitBootCdf bAvg
  rw [hc, Fintype.sum_prod_type]
  rfl

lemma splitBootPerc_eq (n m : ℕ) (α δ : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) :
    splitBootPerc n m α δ vx vy = percLo n m α δ vx vy := by
  have hc : (Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) : ℝ) = (n : ℝ) ^ n * (m : ℝ) ^ m := by
    simp [Fintype.card_prod]
  unfold splitBootPerc percLo fOrd
  rw [hc]
  rfl

section Meas

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {X Y : ℕ → Ω → 𝒳}

lemma measurable_percLo (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i)) {h : 𝒳 → ℝ}
    (hm : Measurable h) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (δ : ℝ) (m : ℕ → ℕ) (n : ℕ) :
    Measurable fun ω => percLo n (m n) α δ (smp X h n ω) (smp Y h (m n) ω) := by
  unfold percLo
  exact measurable_fOrd _ fun p => ((measurable_trimLo (n := n) hα0 hα1).comp
    (measurable_pi_iff.2 fun i => hm.comp (hXm (p.1 i)))).sub
      ((measurable_trimUp (n := m n) hα0 hα1).comp (measurable_pi_iff.2 fun j => hm.comp (hYm (p.2 j))))

end Meas

theorem split_boot_clt : Claims.split_boot_clt := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' α q q' κ f Ω _ μ _ X Y m hφ hκ hα0 hα1 hP hQ hXm hYm hXi hYi hXl hYl hκ0 hmr hσ t
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  have hm := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  refine tendstoInMeasure_of_tip0 ((tip0_bootCdf hX hY hm hB hα0 hα1 hκ0 hmr hP hQ hσ t).congr
    (Eventually.of_forall fun n ω => ?_))
  unfold splitBootCdfn
  rw [splitBootCdf_eq]
  rfl

/-- `δ = Φ(Ioi z)` lies in `(0, 1)`. -/
lemma delta_mem {δ z : ℝ} (hz : (gaussianReal 0 1).real (Ioi z) = δ) : 0 < δ ∧ δ < 1 := by
  constructor
  · rw [← hz]
    refine (gaussian_Icc_pos (show z + 1 < z + 2 by linarith)).trans_le (measureReal_mono ?_)
    intro x hx; simp only [Set.mem_Icc, Set.mem_Ioi] at hx ⊢; linarith [hx.1]
  · have h1 : (gaussianReal 0 1).real (Iic z) = 1 - δ := by
      rw [← hz, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]; ring
    have h2 : 0 < (gaussianReal 0 1).real (Iic z) :=
      (gaussian_Icc_pos (show z - 2 < z - 1 by linarith)).trans_le (measureReal_mono fun x hx => by
        simp only [Set.mem_Icc, Set.mem_Iic] at hx ⊢; linarith [hx.2])
    linarith

/-- Route check (not a target): the frozen asymptotic normality `Wave29i.split_asymp_normal`, the bootstrap CLT
`split_boot_clt` and the frozen conditional `Wave22c.split_level` give the percentile certificate. -/
theorem split_perc_check : StatFormal.Wave29i.Claims.split_asymp_normal → Claims.split_boot_clt →
    StatFormal.Wave22c.Claims.split_level → Claims.split_boot_percentile := by
  intro hAN hBC hlevel 𝒳 H _ _ _ _ P Q _ _ φ κ' α q q' κ δ z f Ω _ μ _ X Y m hφ hκ hα0 hα1 hAP hAQ hXm hYm hXi hYi
    hXY hXl hYl hκ0 hmr hz
  have hm := measurable_inner_comp hφ f
  have hP : UQ P (fun x => ⟪f, φ x⟫) (1 - α) q := AssDens.uq hm hAP
  have hQ : UQ Q (fun x => ⟪f, φ x⟫) α q' := AssDens.uq hm hAQ
  have hσ := StatFormal.Wave29i.sigma2_pos (Q := Q) (q' := q') hm (abs_inner_le hκ f) hα0 hα1 hκ0 hAP
  obtain ⟨hδ0, hδ1⟩ := delta_mem hz
  obtain ⟨T₀, hsep, hTD⟩ := hAN 𝒳 H P Q φ κ' α q q' κ f Ω μ X Y m hφ hκ hα0.le hα1 hP hQ hXm hYm hXi hYi hXY hXl
    hYl hκ0 hmr
  have hboot : ∀ t, TIP0 μ (fun n ω => bAvg (fun p => if bootRoot n (m n) α (smp X (fun x => ⟪f, φ x⟫) n ω)
      (smp Y (fun x => ⟪f, φ x⟫) (m n) ω) p ≤ t then (1 : ℝ) else 0) -
        (gaussianReal 0 (sigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ).toNNReal).real (Set.Iic t)) := by
    intro t ε hε
    have h := (tendstoInMeasure_iff_norm.1 (hBC 𝒳 H P Q φ κ' α q q' κ f Ω μ X Y m hφ hκ hα0.le hα1 hP hQ hXm hYm
      hXi hYi hXl hYl hκ0 hmr hσ t)) ε hε
    refine h.congr fun n => ?_
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs]
    unfold splitBootCdfn
    rw [splitBootCdf_eq]
    rfl
  have hcov := perc_coverage_of (h := fun x => ⟪f, φ x⟫) (X := X) (Y := Y) (μ := μ)
    (tendsto_atTop_of_ratio hκ0 hmr) hσ hTD hboot hδ0 hδ1 hz
  have hset : ∀ n, {ω | ((splitBootPercn φ f X Y m α δ n ω : ℝ) : EReal) ≤ sepVal f (region φ α P) (region φ α Q)} =
      {ω | percLo n (m n) α δ (smp X (fun x => ⟪f, φ x⟫) n ω) (smp Y (fun x => ⟪f, φ x⟫) (m n) ω) ≤ T₀} := fun n => by
    ext ω
    simp only [Set.mem_ofPred_eq, hsep, EReal.coe_le_coe_iff]
    unfold splitBootPercn
    rw [splitBootPerc_eq]
    rfl
  have h1 : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real {ω |
      ((splitBootPercn φ f X Y m α δ n ω : ℝ) : EReal) ≤ sepVal f (region φ α P) (region φ α Q)} := fun η hη => by
    filter_upwards [hcov η hη] with n hn
    rw [hset n]; exact hn
  have hEm : ∀ n, MeasurableSet {ω | ((splitBootPercn φ f X Y m α δ n ω : ℝ) : EReal) ≤
      sepVal f (region φ α P) (region φ α Q)} := fun n => by
    rw [hset n]
    exact measurableSet_le (measurable_percLo hXm hYm hm hα0.le hα1 δ m n) measurable_const
  obtain ⟨a, b⟩ := hlevel 𝒳 H P Q φ κ' α δ f Ω (fun _ => μ) (splitBootPercn φ f X Y m α δ)
    (fun n => {ω | ((splitBootPercn φ f X Y m α δ n ω : ℝ) : EReal) ≤ sepVal f (region φ α P) (region φ α Q)})
    hφ hκ hα0.le hα1 (fun _ => inferInstance) hEm (fun n ω hω => hω) h1
  exact ⟨h1, a, fun n ω hω hpos => b n ω hω hpos⟩

theorem split_boot_percentile : Claims.split_boot_percentile :=
  split_perc_check StatFormal.Wave29i.split_asymp_normal split_boot_clt StatFormal.Wave22c.split_level

end StatFormal.Wave29l
