import StatFormal.Wave30tl.RouteConfset
import StatFormal.Wave30tl.Revision.Statements

/-!
# Wave 30tl, revision — revised `cor:confset` and the interval sentence after `cor:upperfs` (untrusted proof route)

`confset_ci` is `core_onEvent` (the revised printed proof). Width: `τ` is nondecreasing and `ω^←` monotone, and
`ω^←(ω ε) ≤ ε` for strictly increasing `ω`. `alphaHi_le`: evaluate the infimum at `α = α̂`, where `D̂_{α̂} ≤ τ(α̂)`
(`lem:crossing`, attainment).
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tl.Revision

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tl

theorem confset_ci : Claims.confset_ci := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ ω n m hφ hκ htv hmar hδ0 hδ1 hn hm
  obtain ⟨E, hEm, hEp, hE⟩ := exists_event P Q hφ hκ hδ0 hδ1 hn hm
  exact ⟨E, hEm, hEp, fun z hz => core_onEvent P Q hφ hκ htv hmar hδ0 hδ1 hn hm z (hE z hz)⟩

theorem confset_width : Claims.confset_width := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ ω n m hφ hκ htv hmar hδ0 hδ1 hn hm
  obtain ⟨E, hEm, hEp, hE⟩ := exists_event P Q hφ hκ hδ0 hδ1 hn hm
  refine ⟨E, hEm, hEp, fun z hz => ?_⟩
  obtain ⟨hle, hup⟩ := core_onEvent P Q hφ hκ htv hmar hδ0 hδ1 hn hm z (hE z hz)
  have hκ0 : 0 ≤ κ := kappa_nonneg_of hκ (z.1 ⟨0, hn⟩)
  have htau := tau_mono hκ0 hle htv δ n m
  refine ⟨hle, hup, htau, fun ε hε hωε => ?_⟩
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hε.2.trans htv.le⟩
  calc omegaGen ω (2 * tau κ (alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m)) δ n m)
      ≤ omegaGen ω (2 * tau κ (StatFormal.Distances.tvDist P Q) δ n m) := omegaGen_mono ω (by linarith)
    _ = omegaGen ω (ω ε) := by rw [hωε]
    _ ≤ ε := omegaGen_apply_le hmar.1 hε1

theorem alphaHi_le_det {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {φ : 𝒳 → H} {κ δ : ℝ} {ω : ℝ → ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    alphaHi ω (fun α => Demp φ x y α + tau κ α δ n m) ≤
      alphaHat (Demp φ x y) (fun α => tau κ α δ n m) +
        omegaGen ω (2 * tau κ (alphaHat (Demp φ x y) (fun α => tau κ α δ n m)) δ n m) := by
  have hmem := alphaHat_mem_crossSet hφ hκ hδ0 hδ1 hn hm x y
  refine (csInf_le (alphaHi_bddBelow _ _) ⟨_, hmem.1, rfl⟩).trans ?_
  have h2 : Demp φ x y (alphaHat (Demp φ x y) (fun α => tau κ α δ n m)) +
      tau κ (alphaHat (Demp φ x y) (fun α => tau κ α δ n m)) δ n m ≤
      2 * tau κ (alphaHat (Demp φ x y) (fun α => tau κ α δ n m)) δ n m := by
    have := hmem.2; simp only at this; linarith
  have := omegaGen_mono ω h2
  simp only
  linarith

theorem alphaHi_le : Claims.alphaHi_le := by
  intro 𝒳 H _ _ _ _ _ φ κ δ ω n m hφ hκ hδ0 hδ1 hn hm x y
  exact alphaHi_le_det hφ hκ hδ0 hδ1 hn hm x y

theorem upperfs_interval : Claims.upperfs_interval := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ ω n m hφ hκ htv hmar hδ0 hδ1 hn hm
  obtain ⟨E, hEm, hEp, hE⟩ := exists_event P Q hφ hκ hδ0 hδ1 hn hm
  refine ⟨E, hEm, hEp, fun z hz => ?_⟩
  have hDc : ∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α ≤ Demp φ z.1 z.2 α + tau κ α δ n m := fun α hα => by
    have := (abs_le.1 (hE z hz α hα)).1
    linarith
  exact ⟨hDc, (core_onEvent P Q hφ hκ htv hmar hδ0 hδ1 hn hm z (hE z hz)).1,
    upperfs_onEvent P Q hmar htv hDc, alphaHi_le_det hφ hκ hδ0 hδ1 hn hm z.1 z.2⟩

end StatFormal.Wave30tl.Revision
