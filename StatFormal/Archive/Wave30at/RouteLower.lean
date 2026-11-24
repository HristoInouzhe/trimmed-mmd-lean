import StatFormal.Archive.Wave30at.Statements
import StatFormal.Archive.TrimmedMMD.Lower.Proofs
import StatFormal.Archive.Wave29i.Proofs
import StatFormal.Archive.Wave29w.Proofs
import StatFormal.Archive.Wave29l.Proofs
import StatFormal.Archive.Wave30d.Proofs

/-!
# Route (wave 30at): trimmed MMD `cor:lower` with `thm:split` discharged (untrusted)

The certified `downclosed_pathwise` puts `{α̂_lo > TV}` inside the rejection of the FIRST grid level `j₀` with
`TV ≤ α_{j₀}` (a deterministic index), or makes it empty when there is none. At that level the null holds, so the
certified level clause of `thm:split` (plug-in SE: `split_level_discharged`, `split_zero_level`; bootstrap SE:
`split_level_bootstrap`, `split_zero_level_bootstrap`; percentile bootstrap: `split_boot_percentile`,
`split_zero_boot_percentile`; `α_{j₀} > 0`, resp. `= 0`) gives `P(reject) ≤ δ + η` eventually, for every `η > 0`;
monotonicity of the (outer) measure and of `limsup` finish.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave30at

open StatFormal.Wave29i (splitStat splitSEn splitAss)
open StatFormal.Wave29l (splitBootSEn splitBootPercn)
open StatFormal.TrimmedMMD.Lower (alphaLo)

/-- The generic step: per-level asymptotic validity at every true null gives asymptotic validity of `α̂_lo`. -/
lemma lower_generic {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {J : ℕ} (α : Fin J → ℝ) {tv δ : ℝ}
    (htv : 0 ≤ tv) (hδ : 0 ≤ δ) (rej : ℕ → Ω → Fin J → Prop)
    (hlev : ∀ j, tv ≤ α j → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, μ {ω | rej n ω j} ≤ ENNReal.ofReal (δ + η)) :
    limsup (fun n => μ {ω | tv < alphaLo α (rej n ω)}) atTop ≤ ENNReal.ofReal δ := by
  set A : ℕ → Set Ω := fun n => {ω | tv < alphaLo α (rej n ω)}
  change limsup (fun n => μ (A n)) atTop ≤ ENNReal.ofReal δ
  by_cases hex : ∃ j₀ : Fin J, tv ≤ α j₀ ∧ ∀ i < j₀, α i < tv
  · obtain ⟨j₀, hj₀, hj₀'⟩ := hex
    have hsub : ∀ n, A n ⊆ {ω | rej n ω j₀} := fun n ω hω =>
      ((StatFormal.TrimmedMMD.Lower.downclosed_pathwise J α (rej n ω) tv htv hω).2 j₀ hj₀ hj₀')
    have hbound : ∀ η : ℝ, 0 < η → limsup (fun n => μ (A n)) atTop ≤ ENNReal.ofReal (δ + η) := by
      intro η hη
      refine limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [hlev j₀ hj₀ η hη] with n hn
      exact (measure_mono (hsub n)).trans hn
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    calc limsup (fun n => μ (A n)) atTop ≤ ENNReal.ofReal (δ + (ε : ℝ)) :=
          hbound (ε : ℝ) (by exact_mod_cast hε)
      _ = ENNReal.ofReal δ + ε := by
        rw [ENNReal.ofReal_add hδ ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  · have hempty : ∀ n, A n = ∅ := fun n => by
      ext ω
      simp only [mem_empty_iff_false, iff_false]
      intro hω
      exact hex ((StatFormal.TrimmedMMD.Lower.downclosed_pathwise J α (rej n ω) tv htv hω).1)
    simp only [hempty, measure_empty]
    exact (limsup_const_bot (f := atTop)).le.trans bot_le

theorem cor_lower_split : Claims.cor_lower_split := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' κ δ z J α f q q' Ω _ μ _ X Y m hφ hκ' hmono hα hass hX hY hiX hiY
    hXY hPX hQY hκ hm hz
  refine lower_generic μ α (StatFormal.Distances.tvDist_nonneg P Q) (by rw [← hz]; exact measureReal_nonneg)
    _ fun j hj η hη => ?_
  rcases (hα j).1.lt_or_eq with hpos | hzero
  · obtain ⟨h1, h2⟩ := hass j hpos
    exact (StatFormal.Wave29i.split_level_discharged 𝒳 H P Q φ κ' (α j) (q j) (q' j) κ δ z (f j)
      Ω μ X Y m hφ hκ' hpos (hα j).2 h1 h2 hX hY hiX hiY hXY hPX hQY hκ hm hz).2.1 hj η hη
  · have h0 := (StatFormal.Wave29w.split_zero_level 𝒳 H P Q φ κ' κ δ z (f j) Ω μ X Y m hφ hκ'
      hX hY hiX hiY hXY hPX hQY hκ hm hz).2.1 (by rw [hzero]; exact hj) η hη
    simpa only [← hzero] using h0

theorem cor_lower_boot : Claims.cor_lower_boot := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' κ δ z J α f q q' Ω _ μ _ X Y m hφ hκ' hmono hα hass hX hY hiX hiY
    hXY hPX hQY hκ hm hz
  refine lower_generic μ α (StatFormal.Distances.tvDist_nonneg P Q) (by rw [← hz]; exact measureReal_nonneg)
    _ fun j hj η hη => ?_
  rcases (hα j).1.lt_or_eq with hpos | hzero
  · obtain ⟨h1, h2⟩ := hass j hpos
    exact (StatFormal.Wave29l.split_level_bootstrap 𝒳 H P Q φ κ' (α j) (q j) (q' j) κ δ z (f j)
      Ω μ X Y m hφ hκ' hpos (hα j).2 h1 h2 hX hY hiX hiY hXY hPX hQY hκ hm hz).2.1 hj η hη
  · have h0 := (StatFormal.Wave30d.split_zero_level_bootstrap 𝒳 H P Q φ κ' κ δ z (f j) Ω μ X Y m hφ hκ'
      hX hY hiX hiY hXY hPX hQY hκ hm hz).2.1 (by rw [hzero]; exact hj) η hη
    simpa only [← hzero] using h0

theorem cor_lower_perc : Claims.cor_lower_perc := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' κ δ z J α f q q' Ω _ μ _ X Y m hφ hκ' hmono hα hass hX hY hiX hiY
    hXY hPX hQY hκ hm hz
  refine lower_generic μ α (StatFormal.Distances.tvDist_nonneg P Q) (by rw [← hz]; exact measureReal_nonneg)
    _ fun j hj η hη => ?_
  rcases (hα j).1.lt_or_eq with hpos | hzero
  · obtain ⟨h1, h2⟩ := hass j hpos
    exact (StatFormal.Wave29l.split_boot_percentile 𝒳 H P Q φ κ' (α j) (q j) (q' j) κ δ z (f j)
      Ω μ X Y m hφ hκ' hpos (hα j).2 h1 h2 hX hY hiX hiY hXY hPX hQY hκ hm hz).2.1 hj η hη
  · have h0 := (StatFormal.Wave30d.split_zero_boot_percentile 𝒳 H P Q φ κ' κ δ z (f j) Ω μ X Y m hφ hκ'
      hX hY hiX hiY hXY hPX hQY hκ hm hz).2.1 (by rw [hzero]; exact hj) η hη
    simpa only [← hzero] using h0

end StatFormal.Wave30at
