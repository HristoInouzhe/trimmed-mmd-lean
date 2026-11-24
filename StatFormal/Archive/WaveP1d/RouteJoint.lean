import StatFormal.Archive.WaveP1d.Statements
import StatFormal.Archive.ICL.JointFull.Route

/-!
# Route: ICL `thm:joint`, laws on `M`-subsets with the coverage term (untrusted)

The route of the frozen `ICL/JointFull` proof with the index set of `M`-subsets: linearity in the law reduces the risk
deviation to the `C(n,M)` functions `L(·; z_S)` (symmetrisation + Massart: `E D_A ≤ 2B_L√(2 log(2C(n,M))/m)`), the
one-slot marginal `Π̄_j = M⁻¹Σ_S Π(S)1{j∈S}` lies in the simplex, so the certified coverage bounds (contraction,
countable dense subset of the simplex, Massart over `2n` vectors) apply verbatim, and one McDiarmid inequality on
`D_A + λ_cov D_Φ` gives the tail.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Real Finset

namespace StatFormal.WaveP1d

namespace RouteJoint

open StatFormal.ICL.Joint StatFormal.ICL.JointFull StatFormal.Concentration

theorem oneSlotSub_mem {n M : ℕ} (hM : 1 ≤ M) {law : {S : Finset (Fin n) // S.card = M} → ℝ}
    (hlaw : ProbVec law) : oneSlotSub law ∈ simplex n := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨fun j => mul_nonneg (by positivity) (sum_nonneg fun S _ =>
    mul_nonneg (hlaw.1 S) (by split_ifs <;> norm_num)), ?_⟩
  unfold oneSlotSub
  rw [← mul_sum, Finset.sum_comm]
  have hc : ∀ S : {S : Finset (Fin n) // S.card = M}, ∑ j, law S * (if j ∈ S.1 then (1 : ℝ) else 0) =
      law S * M := by
    intro S
    rw [← mul_sum, sum_boole, filter_mem_eq_inter, univ_inter, S.2]
  simp_rw [hc]
  rw [← sum_mul, hlaw.2, one_mul, one_div, inv_mul_cancel₀ hMR.ne']

theorem integral_iSup_risk_sub_le {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {n M m : ℕ} (hMn : M ≤ n) (hm : m ≠ 0)
    (L : {S : Finset (Fin n) // S.card = M} → Z → ℝ) (hLm : ∀ j, Measurable (L j)) {B : ℝ}
    (hB : ∀ j z, 0 ≤ L j z ∧ L j z ≤ B) :
    ∫ zs, ⨆ t, |empDev μ L m zs t| ∂(Measure.pi fun _ : Fin m => μ) ≤
      2 * B * √(2 * Real.log (2 * (n.choose M : ℝ)) / m) := by
  have hne : Nonempty {S : Finset (Fin n) // S.card = M} := by
    obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := M)
      (by rw [card_univ, Fintype.card_fin]; exact hMn)
    exact ⟨⟨S, hS⟩⟩
  have hB' : ∀ j z, |L j z| ≤ B := fun j z => by
    rw [abs_of_nonneg (hB j z).1]; exact (hB j z).2
  have hB0 : 0 ≤ B := by
    obtain ⟨z⟩ := nonempty_of_isProbabilityMeasure μ
    obtain ⟨j⟩ := hne
    exact (hB j z).1.trans (hB j z).2
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
  have hsym := integral_iSup_abs_empDev_le μ hLm hB' hm
  have hcardι : (Fintype.card {S : Finset (Fin n) // S.card = M} : ℝ) = (n.choose M : ℝ) := by
    rw [Fintype.card_subtype, show (univ.filter fun S : Finset (Fin n) => S.card = M) =
      powersetCard M univ by ext S; simp [mem_powersetCard], card_powersetCard, card_univ,
      Fintype.card_fin]
  set K := B * √(2 * Real.log (2 * (n.choose M : ℝ))) / √m with hK
  have hrad : ∀ zs : Fin m → Z,
      radE (fun σ => ⨆ t, |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * L t (zs i)|) ≤ K := by
    intro zs
    have := radE_iSup_abs_finite_le hm L hB0 hB' zs
    rwa [hcardι] at this
  have hint : ∫ zs, radE (fun σ => ⨆ t, |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * L t (zs i)|)
      ∂(Measure.pi fun _ : Fin m => μ) ≤ K := by
    have := integral_mono_of_nonneg (μ := Measure.pi fun _ : Fin m => μ)
      (f := fun zs => radE (fun σ => ⨆ t, |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * L t (zs i)|))
      (g := fun _ => K)
      (ae_of_all _ fun zs => radE_nonneg fun σ =>
        le_ciSup_of_le (bddAbove_of_abs_le
          (f := fun t : {S : Finset (Fin n) // S.card = M} =>
            |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * L t (zs i)|)
          (C := B) fun t => by
          rw [abs_abs]
          exact abs_mean_le hm fun i => abs_rsign_mul_le hB' (σ i) t (zs i))
          (Classical.arbitrary _) (abs_nonneg _))
      (integrable_const K) (ae_of_all _ hrad)
    rwa [integral_const, probReal_univ, one_smul] at this
  have hK2 : 2 * K = 2 * B * √(2 * Real.log (2 * (n.choose M : ℝ)) / m) := by
    rw [hK, Real.sqrt_div' _ hmpos.le]; ring
  linarith

end RouteJoint

open RouteJoint StatFormal.ICL.Joint StatFormal.ICL.JointFull StatFormal.Concentration

theorem joint_full_subsets : Claims.joint_full_subsets := by
  intro Z Ω _ _ P _ μ _ n M m L k BL Kmin Kmax lcov δ X hn hM hMn hm hδ0 hδ1 hlcov hK hLm hLb
    hkm hkb hXm hind hlaw
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.1 hm
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hn1 : 1 ≤ n := by omega
  have : Nonempty {S : Finset (Fin n) // S.card = M} := by
    obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := M)
      (by rw [card_univ, Fintype.card_fin]; exact hMn)
    exact ⟨⟨S, hS⟩⟩
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
      2 * BL * √(2 * Real.log (2 * (n.choose M : ℝ)) / m) +
        4 * lcov * (Kmax / Kmin) * √(2 * Real.log (2 * n) / m) := by
    have hsplit : (∫ y, F y ∂Measure.pi fun _ : Fin m => μ) =
        (∫ y, DA y ∂Measure.pi fun _ : Fin m => μ) +
          lcov * ∫ y, DΦ y ∂Measure.pi fun _ : Fin m => μ := by
      rw [← integral_const_mul, ← integral_add hDAi (hDΦi.const_mul lcov)]
    rw [hsplit]
    have h1 := integral_iSup_risk_sub_le μ hMn hm0 L hLm hLb
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
  have hw := oneSlotSub_mem hM hlawp
  have hcov : -(1 / (m : ℝ)) * ∑ i, Real.log (coverSub k law (zs i)) +
      ∫ z, Real.log (coverSub k law z) ∂μ = -empDev μ (gcov k Kmin) m zs (oneSlotSub law) :=
    empDev_log_rho μ hK hkb hkm hm0 hw zs
  have hcovb : |empDev μ (gcov k Kmin) m zs (oneSlotSub law)| ≤ DΦ zs :=
    abs_empDev_le_iSup_dense μ hK hkb hkm hm0 T₀ hT₀ hdense hw zs
  have hdev : |devFullSub μ L k lcov law zs| ≤ F zs := by
    unfold devFullSub
    rw [hcov]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hlcov, abs_neg]
    have := mul_le_mul_of_nonneg_left hcovb hlcov
    simp only [hFdef]
    linarith
  change |devFullSub μ L k lcov law zs| ≤ _
  rw [htail] at hω'
  linarith

end StatFormal.WaveP1d
