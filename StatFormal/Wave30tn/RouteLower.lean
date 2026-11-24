import StatFormal.Wave30tn.RouteSplitFS
import StatFormal.Archive.Wave30at.RouteLower
import StatFormal.Archive.Wave30dd.Proofs
import StatFormal.Archive.Wave30da.Proofs

/-!
# Route — wave 30tn: `cor:lower` (finite-sample clause, general regime) and two clauses of `thm:split` (untrusted)

* `cor_lower_fs_route`: the frozen `downclosed_pathwise` puts `{α̂_lo > TV}` inside the rejection at the first grid
  level `j₀` with `TV ≤ α_{j₀}` (a deterministic index), whose probability is `≤ δ` by `prop:splitfs`; or the event is
  empty.
* `cor_lower_boot_any_route`, `cor_lower_split_any_route`: the wave-30at `lower_generic` with the frozen general-regime
  level clauses (`split_level_bootstrap_any`, `split_zero_level_bootstrap_any`, `split_level_any`,
  `split_zero_level_any`).
* `split_normal_ass_route`: the premises of the frozen `split_normal_any` from `ass:split` (library `AssDens.uq`,
  `AssDens.var_pos`, the wave-30da mirror `wda_var_pos_up`), and positivity of `σ_{n,m}`.
* `split_witness_zero_route`: with `f = 0` every value is `0`; every trimmed mean, bootstrap replicate, order statistic
  and the plug-in variance is then `0` (an `sInf`/`sSup` of a subset of `{0}`, an `iSup`/`iInf` of the constant `0`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatFormal.Wave30tn

open StatFormal.Wave29i (splitTrimLo splitTrimUp splitSE splitVarLo splitQuantLo splitOrdStat splitAss)
open StatFormal.Wave29l (splitBootRep splitBootMean splitBootVar splitBootSE splitBootPerc)
open StatFormal.TrimmedMMD.Lower (alphaLo)
open StatFormal.Foundations.TrimmedMean (AssDens measurable_inner_comp abs_inner_le)

theorem cor_lower_fs_route : Claims.cor_lower_fs := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ δ J α f Ω _ μ _ X Y n m hφ hκ hf hmono hα hδ0 hδ1 hXm hYm hXi hYi hXl hYl hn hm
  set tv := StatFormal.Distances.tvDist P Q with htvdef
  have htv : 0 ≤ tv := StatFormal.Distances.tvDist_nonneg P Q
  set rej : Ω → Fin J → Prop := fun ω j => 2 * κ * (1 - α j)⁻¹ * (dkwRad n δ + dkwRad m δ) <
    splitTrimLo n (α j) (fun i => ⟪f j, φ (X i ω)⟫) - splitTrimUp m (α j) (fun i => ⟪f j, φ (Y i ω)⟫) with hrej
  change μ {ω | tv < alphaLo α (rej ω)} ≤ ENNReal.ofReal δ
  by_cases hex : ∃ j₀ : Fin J, tv ≤ α j₀ ∧ ∀ i < j₀, α i < tv
  · obtain ⟨j₀, hj₀, hj₀'⟩ := hex
    have hsub : {ω | tv < alphaLo α (rej ω)} ⊆ {ω | rej ω j₀} := fun ω hω =>
      (StatFormal.TrimmedMMD.Lower.downclosed_pathwise J α (rej ω) tv htv hω).2 j₀ hj₀ hj₀'
    refine (measure_mono hsub).trans ?_
    obtain ⟨T, -, -, hlev⟩ := splitfs_route 𝒳 H P Q φ κ (α j₀) δ (f j₀) Ω μ X Y n m hφ hκ (hf j₀) (hα j₀).1
      (hα j₀).2 hδ0 hδ1 hXm hYm hXi hYi hXl hYl hn hm
    exact hlev hj₀
  · have hempty : {ω | tv < alphaLo α (rej ω)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hω
      exact hex (StatFormal.TrimmedMMD.Lower.downclosed_pathwise J α (rej ω) tv htv hω).1
    rw [hempty, measure_empty]
    exact zero_le

theorem cor_lower_boot_any_route : Claims.cor_lower_boot_any := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' δ z J α f q q' Ω _ μ _ X Y n m hφ hκ' hmono hα hass hX hY hiX hiY
    hXY hPX hQY hn1 hm1 hn hm hz
  refine StatFormal.Wave30at.lower_generic μ α (StatFormal.Distances.tvDist_nonneg P Q)
    (by rw [← hz]; exact measureReal_nonneg) _ fun j hj η hη => ?_
  rcases (hα j).1.lt_or_eq with hpos | hzero
  · obtain ⟨h1, h2⟩ := hass j hpos
    exact (StatFormal.Wave30dd.split_level_bootstrap_any 𝒳 H P Q φ κ' (α j) (q j) (q' j) δ z (f j)
      Ω μ X Y n m hφ hκ' hpos (hα j).2 h1 h2 hX hY hiX hiY hXY hPX hQY hn1 hm1 hn hm hz).2.1 hj η hη
  · have h0 := (StatFormal.Wave30dd.split_zero_level_bootstrap_any 𝒳 H P Q φ κ' δ z (f j) Ω μ X Y n m hφ hκ'
      hX hY hiX hiY hXY hPX hQY hn1 hm1 hn hm hz).2.1 (by rw [hzero]; exact hj) η hη
    simpa only [← hzero] using h0

theorem cor_lower_split_any_route : Claims.cor_lower_split_any := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' δ z J α f q q' Ω _ μ _ X Y n m hφ hκ' hmono hα hass hX hY hiX hiY
    hXY hPX hQY hn1 hm1 hn hm hz
  refine StatFormal.Wave30at.lower_generic μ α (StatFormal.Distances.tvDist_nonneg P Q)
    (by rw [← hz]; exact measureReal_nonneg) _ fun j hj η hη => ?_
  rcases (hα j).1.lt_or_eq with hpos | hzero
  · obtain ⟨h1, h2⟩ := hass j hpos
    exact (StatFormal.Wave30da.split_level_any 𝒳 H P Q φ κ' (α j) (q j) (q' j) δ z (f j)
      Ω μ X Y n m hφ hκ' hpos (hα j).2 h1 h2 hX hY hiX hiY hXY hPX hQY hn1 hm1 hn hm hz).2.1 hj η hη
  · have h0 := (StatFormal.Wave30dd.split_zero_level_any 𝒳 H P Q φ κ' δ z (f j) Ω μ X Y n m hφ hκ'
      hX hY hiX hiY hXY hPX hQY hn1 hm1 hn hm hz).2.1 (by rw [hzero]; exact hj) η hη
    simpa only [← hzero] using h0

/-- Under `ass:split` at `α ∈ (0,1)` both influence variances are positive. -/
lemma vars_pos_of_ass {𝒳 : Type} [MeasurableSpace 𝒳] {P Q : Measure 𝒳} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {h : 𝒳 → ℝ} (hhm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) {α q q' : ℝ}
    (hα0 : 0 < α) (hP : splitAss P h (1 - α) q) (hQ : splitAss Q h α q') :
    0 < Var[fun x => max (q - h x) 0; P] ∧ 0 < Var[fun x => max (h x - q') 0; Q] := by
  have hP' : AssDens P h (1 - α) q := hP
  have hQ' : AssDens Q h α q' := hQ
  exact ⟨AssDens.var_pos hhm hB hP' (by linarith), StatFormal.Wave30da.wda_var_pos_up hhm hB hQ' hα0⟩

theorem split_normal_ass_route : Claims.split_normal_ass := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' α q q' f Ω _ μ _ X Y n m hφ hκ hα0 hα1 hP hQ hXm hYm hXi hYi hXY hXl hYl
    hn1 hm1 hn hm
  have hhm := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  obtain ⟨ha, hb⟩ := vars_pos_of_ass hhm hB hα0 hP hQ
  refine ⟨fun a b ha1 hb1 => ?_, ?_⟩
  · have : (0 : ℝ) < a := by exact_mod_cast ha1
    have : (0 : ℝ) < b := by exact_mod_cast hb1
    exact div_pos (Real.sqrt_pos.2 (by positivity)) (by linarith)
  · exact StatFormal.Wave30da.split_normal_any 𝒳 H P Q φ κ' α q q' f Ω μ X Y n m hφ hκ hα0.le hα1
      (AssDens.uq hhm hP) (AssDens.uq hhm hQ) ha hb hXm hYm hXi hYi hXY hXl hYl hn1 hm1 hn hm

/-! ### `f̂ = 0` -/

lemma sInf_sub_zero {S : Set ℝ} (h : S ⊆ {0}) : sInf S = 0 := by
  rcases subset_singleton_iff_eq.1 h with h | h <;> simp [h]

lemma sSup_sub_zero {S : Set ℝ} (h : S ⊆ {0}) : sSup S = 0 := by
  rcases subset_singleton_iff_eq.1 h with h | h <;> simp [h]

lemma trimLo_zeros (n : ℕ) (α : ℝ) : splitTrimLo n α (fun _ => 0) = 0 :=
  sInf_sub_zero (by rintro _ ⟨w, -, rfl⟩; simp)

lemma trimUp_zeros (n : ℕ) (α : ℝ) : splitTrimUp n α (fun _ => 0) = 0 :=
  sSup_sub_zero (by rintro _ ⟨w, -, rfl⟩; simp)

lemma bootRep_zeros (n m : ℕ) (α : ℝ) (I : Fin n → Fin n) (J : Fin m → Fin m) :
    splitBootRep n m α (fun _ => 0) (fun _ => 0) I J = 0 := by
  unfold splitBootRep
  rw [show ((fun _ : Fin n => (0 : ℝ)) ∘ I) = fun _ => 0 from rfl,
    show ((fun _ : Fin m => (0 : ℝ)) ∘ J) = fun _ => 0 from rfl, trimLo_zeros, trimUp_zeros, sub_zero]

lemma bootSE_zeros (n m : ℕ) (α : ℝ) : splitBootSE n m α (fun _ => 0) (fun _ => 0) = 0 := by
  unfold splitBootSE splitBootVar splitBootMean
  simp [bootRep_zeros]

lemma varLo_zeros (n : ℕ) (α : ℝ) : splitVarLo n α (fun _ => 0) = 0 := by
  have hq : splitQuantLo n α (fun _ => 0) = 0 := by
    unfold splitQuantLo splitOrdStat
    simp
  unfold splitVarLo
  rw [hq]; simp

lemma perc_zeros (n m : ℕ) (α δ : ℝ) : splitBootPerc n m α δ (fun _ => 0) (fun _ => 0) = 0 := by
  unfold splitBootPerc
  simp [bootRep_zeros]

theorem split_witness_zero_route : Claims.split_witness_zero := by
  intro 𝒳 H _ _ φ α δ z Ω X Y n m ω _ _
  simp only [inner_zero_left]
  have h1 := trimLo_zeros n α
  have h2 := trimUp_zeros m α
  have h3 := bootSE_zeros n m α
  have h4 : splitSE n m α (fun _ => 0) (fun _ => 0) = 0 := by
    unfold splitSE
    rw [show (fun j : Fin m => -(fun _ => (0 : ℝ)) j) = fun _ => 0 from funext fun _ => neg_zero,
      varLo_zeros, varLo_zeros]
    simp
  have h5 := perc_zeros n m α δ
  refine ⟨by rw [h1, h2, sub_zero], h3, ?_, ?_, ?_⟩
  · rw [h1, h2, h3]; simp
  · rw [h1, h2, h4]; simp
  · rw [h5]; exact lt_irrefl 0

end StatFormal.Wave30tn
