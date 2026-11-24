import StatFormal.Wave31tr.Statements
import StatFormal.Lib.FnCert.TauP
import StatFormal.Lib.FnCert.Grid
import StatFormal.Wave30tp.Proofs
import StatFormal.Wave30tu.Proofs
import StatFormal.Wave30tr.Proofs
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs
import StatFormal.Wave30tl.RouteCrossing

/-!
# Wave 31tr, chunk M4: T56, the analytic estimator at `τ = τ^P` (untrusted route)

* (a) `taup_jump`: `c = v√s + D√(s log(6/δ)/2)` exceeds `τ^P(0)` and bounds `τ^P(α)` below on `(0,1)` (`FnCert.tauP_jump_lower`).
* (c) `taup_welldefined`: `τ^P(α) ≥ D` at some `α ∈ [1/2,1)` (`FnCert.exists_tauP_ge`, `ρ̄ = D > 0`), and `D̂_α ≤ D` always (the
  certified `Wave30tu.Demp_le_Dphi`), so that `α` is in the crossing set.
* (d) `taup_valid_bound`: the certified `Wave30tp.plugin_one_event` with the kernel constants of `Wave30tp.kernel_consts`; the grid read
  upward is at most `α⋆` because every rejected grid level is below `α⋆` (`FnCert.alphaLo_le_of_forall`).
* (e) `taup_consistent_below`: `D_α > 0` (the certified `zeroeq`, `α < α⋆`); `τ^A(α,δ′) + τ^P(α) → 0` as `n, m → ∞`
  (`FnCert.tendsto_tauA`, `tendsto_tauP`), so eventually below `D_α`; on the lower event `E⁻` of the certified `Wave30tr.thmA` at
  `δ′ = min(ε, 1/2)`, `D̂_α ≥ D_α − τ^A > τ^P(α)`, and the up-set property (`D̂` nonincreasing, `τ^P` nondecreasing on `[0,1)`) puts
  every crossing level at or above `α`, while the crossing set is nonempty (`D ≥ D̂_α > 0`, part (c)); hence `α̂_an ≥ α` on `E⁻`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave31tr.RouteCert

open StatFormal.Wave30tp StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional

theorem taup_jump_route : Claims.taup_jump := by
  intro D v ρbar δ n m hD hv hρ hδ0 hδ1 hn hm
  refine ⟨v * √(sNM n m) + D * √(sNM n m * Real.log (6 / δ) / 2), FnCert.tauP_zero_lt_jump hD hδ0 hδ1 hn hm, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with α hα
  exact FnCert.tauP_jump_lower hD.le hv hρ hδ0 hδ1 hα.1 hα.2 n m

theorem taup_welldefined_route : Claims.taup_welldefined := by
  intro 𝒳 H _ _ _ _ _ φ κ D δ n m hφ hκ hD hD0 hδ0 hδ1 hn hm x y
  obtain ⟨α, hα, hτ⟩ := FnCert.exists_tauP_ge (v := √(min (κ ^ 2) (D ^ 2 / 2))) hD0.le (Real.sqrt_nonneg _) hD0.le hδ0 hδ1 hn hm
  have hα' : α ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hα.1], hα.2⟩
  exact ⟨α, hα', (StatFormal.Wave30tu.Demp_le_Dphi 𝒳 H φ κ D n m hφ hκ hD hn hm x y α hα').trans hτ⟩

theorem taup_valid_bound_route : Claims.taup_valid_bound := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ n m hφ hκ hD hTV hδ0 hδ1 hn hm
  have hK := (StatFormal.Wave30tp.kernel_consts 𝒳 H φ κ D hφ hκ hD).1
  obtain ⟨E, hE, hPE, hz⟩ :=
    StatFormal.Wave30tp.plugin_one_event 𝒳 H φ κ D _ D P Q δ n m hφ hκ hK hδ0 hδ1 hn hm
  refine ⟨E, hE, hPE, fun z hzE => ⟨(hz z hzE).2.1 hTV, (hz z hzE).2.2, fun J α hgrid => ?_⟩⟩
  exact FnCert.alphaLo_le_of_forall (StatFormal.Distances.tvDist_nonneg P Q)
    fun j hj => (hz z hzE).2.2 (α j) ⟨(hgrid.2 j).1, (hgrid.2 j).2⟩ hj

theorem taup_consistent_below_route : Claims.taup_consistent_below := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ hφ hκ hD hD2κ hchar hTV hδ0 hδ1 α hα ε hε
  set v := √(min (κ ^ 2) (D ^ 2 / 2)) with hv
  set δ' := min ε (1 / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min hε (by norm_num)
  have hδ'1 : δ' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hα1 : α < 1 := lt_trans hα.2 hTV
  have hαI : α ∈ Ico (0 : ℝ) 1 := ⟨hα.1, hα1⟩
  -- `D_α > 0`
  have hd : 0 < Dpop φ P Q α := by
    have h0 := StatFormal.TrimmedMMD.ZeroSet.zeroeq 𝒳 H P Q φ κ α hφ hκ hchar hα.1 hα1
    have hne : Dpop φ P Q α ≠ 0 := fun h => absurd (h0.1 h) (not_le.2 hα.2)
    exact lt_of_le_of_ne (StatFormal.WaveP1a.setDist_nonneg' _ _) hne.symm
  -- both thresholds tend to zero
  have hlim := (FnCert.tendsto_tauA κ D α δ').add (FnCert.tendsto_tauP D v D α δ)
  rw [add_zero, Filter.prod_atTop_atTop_eq] at hlim
  obtain ⟨a, ha⟩ := Filter.eventually_atTop_prod_self'.1 (hlim.eventually (gt_mem_nhds hd))
  refine ⟨max a 1, fun n m hn hm => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hsmall := ha n (le_trans (le_max_left _ _) hn) m (le_trans (le_max_left _ _) hm)
  simp only at hsmall
  obtain ⟨-, Em, -, -, hEm, hPEm, -, hzEm⟩ :=
    StatFormal.Wave30tr.thmA 𝒳 H φ κ D P Q δ' n m hφ hκ hD hδ'0 hδ'1 hn1 hm1
  haveI : IsProbabilityMeasure (sampleLaw P Q n m) := by unfold sampleLaw; infer_instance
  have hsub : {z : (Fin n → 𝒳) × (Fin m → 𝒳) | alphaHat (Demp φ z.1 z.2)
      (fun a => tauP D v D a δ n m) < α} ⊆ Emᶜ := by
    intro z hz hzE
    have hlow := hzEm z hzE α hαI
    have hgt : tauP D v D α δ n m < Demp φ z.1 z.2 α := by linarith
    have hDle := StatFormal.Wave30tu.Demp_le_Dphi 𝒳 H φ κ D n m hφ hκ hD hn1 hm1 z.1 z.2 α hαI
    have hD0 : 0 ≤ D := (StatFormal.Wave30tl.Demp_nonneg φ z.1 z.2 α).trans hDle
    have hmono := StatFormal.Wave30tp.plugin_monotone D v D δ n m hD0 (Real.sqrt_nonneg _) hD0 hδ0 hδ1 hn1 hm1
    have hDpos : 0 < D := lt_of_lt_of_le (lt_of_le_of_lt (hmono.2 α hαI) hgt) hDle
    have hne := taup_welldefined_route 𝒳 H φ κ D δ n m hφ hκ hD hDpos hδ0 hδ1 hn1 hm1 z.1 z.2
    have hanti := StatFormal.Wave30tl.Demp_antitoneOn φ hn1 hm1 z.1 z.2
    have hge : α ≤ alphaHat (Demp φ z.1 z.2) (fun a => tauP D v D a δ n m) := by
      refine le_csInf hne fun b hb => ?_
      by_contra hlt
      push Not at hlt
      have h1 : Demp φ z.1 z.2 α ≤ Demp φ z.1 z.2 b := hanti hb.1 hαI hlt.le
      have h2 : tauP D v D b δ n m ≤ tauP D v D α δ n m := hmono.1 hb.1 hαI hlt.le
      have h3 := hb.2
      simp only at h3
      linarith
    exact absurd hz (not_lt.2 hge)
  calc sampleLaw P Q n m {z | alphaHat (Demp φ z.1 z.2) (fun a => tauP D v D a δ n m) < α}
      ≤ sampleLaw P Q n m Emᶜ := measure_mono hsub
    _ ≤ ENNReal.ofReal δ' := FnCert.measure_compl_le_of_ge hEm hδ'0.le hPEm
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (min_le_left _ _)

end StatFormal.Wave31tr.RouteCert
