import StatFormal.Archive.ICL.JointFull.Route

/-!
# Proofs: ICL `thm:joint` with the coverage term (untrusted proof file)

Route (the paper's, `supp/proofs_main.tex:90-118`): `|J_m − J_pool| ≤ D_A + λ_cov D_Φ` with
`D_A = max_t |(P_m − P_0) L_t|` (linearity in the law) and `D_Φ` the coverage deviation over a
countable dense subset of the simplex (continuity in `w̄`); `E D_A ≤ 4 B_L √(2M log n/m)`
(symmetrisation + Massart), `E D_Φ ≤ 4 (K_max/K_min) √(2 log(2n)/m)` (symmetrisation +
absolute-value contraction + vertices + Massart); one McDiarmid on `D_A + λ_cov D_Φ` with bounded
differences `(B_L + λ_cov log(K_max/K_min))/m`; the sample is transported to `μ^{⊗m}` by
independence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Finset

namespace StatFormal.ICL.JointFull

open StatFormal.ICL.Joint StatFormal.Concentration

theorem joint_full : Claims.joint_full := by
  intro Z Ω _ _ P _ μ _ n M m L k BL Kmin Kmax lcov δ X hn hM hm hδ0 hδ1 hlcov hK hLm hLb
    hkm hkb hXm hind hlaw
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.1 hm
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hn1 : 1 ≤ n := by omega
  haveI : Nonempty (Fin M → Fin n) := ⟨fun _ => ⟨0, by omega⟩⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨z₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hKle : Kmin ≤ Kmax := (hkb ⟨0, by omega⟩ z₀).1.trans (hkb ⟨0, by omega⟩ z₀).2
  have hlr : 0 ≤ log (Kmax / Kmin) := Real.log_nonneg (by rw [le_div_iff₀ hK]; linarith)
  have hB0 : 0 ≤ BL := (hLb (Classical.arbitrary _) z₀).1.trans (hLb (Classical.arbitrary _) z₀).2
  have hLB : ∀ j z, |L j z| ≤ BL := fun j z => by
    rw [abs_of_nonneg (hLb j z).1]; exact (hLb j z).2
  -- countable dense subset of the simplex
  have hsimp_ne : (simplex n).Nonempty := by
    refine ⟨fun _ => 1 / n, fun _ => by positivity, ?_⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  obtain ⟨T₀, hT₀, hcount, hdense⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (simplex n)).exists_countable_dense_subset
  have hne : T₀.Nonempty := closure_nonempty_iff.1 (hsimp_ne.mono hdense)
  haveI : Nonempty T₀ := hne.to_subtype
  haveI : Countable T₀ := hcount.to_subtype
  set g₀ : T₀ → Z → ℝ := fun b => gcov k Kmin b.1 with hg₀
  have hg₀m : ∀ b, Measurable (g₀ b) := fun b => measurable_gcov hkm Kmin b.1
  have hg₀b : ∀ b z, 0 ≤ g₀ b z ∧ g₀ b z ≤ log (Kmax / Kmin) := fun b z =>
    gcov_mem hK hkb (hT₀ b.2) z
  have hg₀B : ∀ b z, |g₀ b z| ≤ log (Kmax / Kmin) := fun b z => by
    rw [abs_of_nonneg (hg₀b b z).1]; exact (hg₀b b z).2
  -- the statistic
  set DA : (Fin m → Z) → ℝ := fun zs => ⨆ t, |empDev μ L m zs t| with hDA
  set DΦ : (Fin m → Z) → ℝ := fun zs => ⨆ b, |empDev μ g₀ m zs b| with hDΦ
  set F : (Fin m → Z) → ℝ := fun zs => DA zs + lcov * DΦ zs with hFdef
  have hDAm : Measurable DA := Measurable.iSup fun t =>
    continuous_abs.measurable.comp (measurable_empDev μ hLm m t)
  have hDΦm : Measurable DΦ := Measurable.iSup fun b =>
    continuous_abs.measurable.comp (measurable_empDev μ hg₀m m b)
  have hFm : Measurable F := hDAm.add (hDΦm.const_mul lcov)
  set c := (BL + lcov * log (Kmax / Kmin)) / m with hcdef
  have hc : 0 ≤ c := by positivity
  have hosc : ∀ zs i b, |F (Function.update zs i b) - F zs| ≤ c := by
    intro zs i b
    have h1 := abs_iSup_abs_empDev_update_le μ (g := L) hLb zs i b
    have h2 := abs_iSup_abs_empDev_update_le μ (g := g₀) hg₀b zs i b
    have : F (Function.update zs i b) - F zs =
        (DA (Function.update zs i b) - DA zs) +
          lcov * (DΦ (Function.update zs i b) - DΦ zs) := by
      simp only [hFdef]; ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hlcov]
    have h3 := mul_le_mul_of_nonneg_left h2 hlcov
    rw [hcdef, add_div, mul_div_assoc]
    linarith
  have hmc := mcdiarmid_tail_nonneg μ hm0 F hFm hc hosc hδ0 hδ1.le
  set A := {zs | F zs ≤ (∫ y, F y ∂Measure.pi fun _ : Fin m => μ) +
    c * √(m * log (1 / δ) / 2)} with hAdef
  have hAm : MeasurableSet A := measurableSet_le hFm measurable_const
  have hXv : Measurable fun ω (i : Fin m) => X i ω := measurable_pi_iff.2 hXm
  refine ⟨(fun ω i => X i ω) ⁻¹' A, hXv hAm, ?_, fun ω hω law hlawp => ?_⟩
  · rw [← Measure.map_apply hXv hAm, map_sample_eq_pi P μ X hXm hind hlaw]
    exact hmc
  -- the expectation of the statistic
  have hDAb : ∀ zs, |DA zs| ≤ 2 * BL := fun zs => abs_ciSup_le fun t => by
    rw [abs_abs]; exact abs_empDev_le μ hLB zs t
  have hDΦb : ∀ zs, |DΦ zs| ≤ 2 * log (Kmax / Kmin) := fun zs => abs_ciSup_le fun b => by
    rw [abs_abs]; exact abs_empDev_le μ hg₀B zs b
  have hDAi : Integrable DA (Measure.pi fun _ : Fin m => μ) :=
    Integrable.of_bound hDAm.aestronglyMeasurable _ (ae_of_all _ fun zs => hDAb zs)
  have hDΦi : Integrable DΦ (Measure.pi fun _ : Fin m => μ) :=
    Integrable.of_bound hDΦm.aestronglyMeasurable _ (ae_of_all _ fun zs => hDΦb zs)
  have hEF : (∫ y, F y ∂Measure.pi fun _ : Fin m => μ) ≤
      4 * BL * √(2 * M * Real.log n / m) +
        4 * lcov * (Kmax / Kmin) * √(2 * Real.log (2 * n) / m) := by
    have hsplit : (∫ y, F y ∂Measure.pi fun _ : Fin m => μ) =
        (∫ y, DA y ∂Measure.pi fun _ : Fin m => μ) +
          lcov * ∫ y, DΦ y ∂Measure.pi fun _ : Fin m => μ := by
      rw [← integral_const_mul, ← integral_add hDAi (hDΦi.const_mul lcov)]
    rw [hsplit]
    have h1 := integral_iSup_risk_le μ hn hM hm0 L hLm hLb
    have h2 := integral_iSup_cov_le μ hK hkb hkm hn1 hm0 T₀ hT₀
    have h3 := mul_le_mul_of_nonneg_left h2 hlcov
    have e1 : (∫ y, DA y ∂Measure.pi fun _ : Fin m => μ) =
        ∫ zs, ⨆ t, |empDev μ L m zs t| ∂(Measure.pi fun _ : Fin m => μ) := rfl
    have e2 : (∫ y, DΦ y ∂Measure.pi fun _ : Fin m => μ) =
        ∫ zs, ⨆ b : T₀, |empDev μ (fun b : T₀ => gcov k Kmin b.1) m zs b|
          ∂(Measure.pi fun _ : Fin m => μ) := rfl
    rw [e1, e2]
    nlinarith
  have htail : c * √(m * log (1 / δ) / 2) =
      (BL + lcov * log (Kmax / Kmin)) * √(log (1 / δ) / (2 * m)) := by
    have hL : 0 ≤ log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
    have : √(m * log (1 / δ) / 2) = m * √(log (1 / δ) / (2 * m)) := by
      rw [show (m : ℝ) * log (1 / δ) / 2 = (m : ℝ) ^ 2 * (log (1 / δ) / (2 * m)) by
        field_simp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hmR.le]
    rw [this, hcdef]
    field_simp
  -- pathwise bound
  set zs : Fin m → Z := fun i => X i ω
  have hω' : F zs ≤ (∫ y, F y ∂Measure.pi fun _ : Fin m => μ) + c * √(m * log (1 / δ) / 2) := hω
  have hrisk : |devJ μ m L law zs| ≤ DA zs := abs_devJ_le_iSup μ L hLb law hlawp zs
  have hw := oneSlot_mem hM hlawp
  have hcov : -(1 / (m : ℝ)) * ∑ i, Real.log (cover k law (zs i)) +
      ∫ z, Real.log (cover k law z) ∂μ = -empDev μ (gcov k Kmin) m zs (oneSlot law) :=
    empDev_log_rho μ hK hkb hkm hm0 hw zs
  have hcovb : |empDev μ (gcov k Kmin) m zs (oneSlot law)| ≤ DΦ zs :=
    abs_empDev_le_iSup_dense μ hK hkb hkm hm0 T₀ hT₀ hdense hw zs
  have hdev : |devFull μ L k lcov law zs| ≤ F zs := by
    unfold devFull
    rw [hcov]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hlcov, abs_neg]
    have := mul_le_mul_of_nonneg_left hcovb hlcov
    simp only [hFdef]
    linarith
  change |devFull μ L k lcov law zs| ≤ _
  rw [htail] at hω'
  linarith

end StatFormal.ICL.JointFull
