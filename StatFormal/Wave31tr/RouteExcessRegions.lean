import StatFormal.Wave31tr.RouteExcess
import StatFormal.Wave30tx.Proofs
import StatFormal.Lib.ExcessRamp.MinNorm

/-!
# Wave 31tr route (E1): the population witness and the regions (T24, T33, T36) (untrusted)

* `witness_unique_route` (T33): `𝒞_α(P) − 𝒞_α(Q)` is nonempty, convex (differences of convex sets) and compact (the image of
  `𝒞_α(P) × 𝒞_α(Q)` under subtraction, the certified `Wave30tx.contact_compact`); a minimum of the norm exists on the compact set;
  two minima coincide (library `ExcessRamp.minNorm_unique`, first-order optimality along segments); a minimum is `a − b` with `‖a − b‖ = setDist = D_α`;
* `dbar_le_D_le_route` (T24): `0 ≤ D_α`, `1 − α⋆ ≤ 1 − α ≤ 1`;
* `regions_nested_route` (T36): the proved route lemmas `Wave30tz.Lower.region_mono_alpha`, `Wave30tz.dpop_antitone`, and at
  `α = 0` a density `0 ≤ g ≤ 1` with `∫ g dP = 1` is `1` `P`-a.e.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31tr.RouteExcess

open StatFormal.Wave30tq StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.ZeroSet StatFormal.TrimmedMMD.Projection

/-! ### T33 -/

theorem witness_unique_route : Claims.witness_unique := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α hφ hκ hα0 hα1
  set A := region φ α P with hA
  set B := region φ α Q with hB
  have hAne : A.Nonempty := region_nonempty P hα0 hα1
  have hBne : B.Nonempty := region_nonempty Q hα0 hα1
  have hne : (A - B).Nonempty := hAne.sub hBne
  have hconv : Convex ℝ (A - B) := (region_convex P hφ hκ).sub (region_convex Q hφ hκ)
  have hAc : IsCompact A := StatFormal.Wave30tx.contact_compact 𝒳 H P φ κ α hφ hκ hα0 hα1
  have hBc : IsCompact B := StatFormal.Wave30tx.contact_compact 𝒳 H Q φ κ α hφ hκ hα0 hα1
  have himg : A - B = (fun p : H × H => p.1 - p.2) '' (A ×ˢ B) := by
    ext z
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  have hcomp : IsCompact (A - B) := by
    rw [himg]; exact (hAc.prod hBc).image continuous_sub
  -- every minimum is a nearest pair at distance `D_α`
  have hval : ∀ d : H, IsMinNorm (A - B) d → ‖d‖ = Dpop φ P Q α ∧ ∃ a ∈ A, ∃ b ∈ B, d = a - b := by
    intro d hd
    obtain ⟨a, ha, b, hb, hdab⟩ := hd.1
    refine ⟨le_antisymm ?_ ?_, a, ha, b, hb, hdab.symm⟩
    · obtain ⟨a₀, ha₀⟩ := hAne
      obtain ⟨b₀, hb₀⟩ := hBne
      refine le_csInf ⟨_, a₀, ha₀, b₀, hb₀, rfl⟩ ?_
      rintro _ ⟨a', ha', b', hb', rfl⟩
      exact hd.2 _ ⟨a', ha', b', hb', rfl⟩
    · rw [← hdab]; exact setDist_le_norm ha hb
  refine ⟨hne, hconv, hcomp, ?_, hval⟩
  obtain ⟨d, hdmem, hdmin⟩ := hcomp.exists_isMinOn hne continuous_norm.continuousOn
  exact ⟨d, ⟨hdmem, fun q hq => hdmin hq⟩, fun q hq =>
    StatFormal.ExcessRamp.minNorm_unique hconv hq.1 hq.2 hdmem fun x hx => hdmin hx⟩

/-! ### T24 -/

theorem dbar_le_D_le_route : Claims.dbar_le_D_le := by
  intro 𝒳 H _ _ _ _ φ κ P Q _ _ α _ _ htv1 hα0 hαtv
  have hD := dpop_nonneg φ P Q α
  have h1 : 0 < 1 - StatFormal.Distances.tvDist P Q := by linarith
  refine ⟨?_, ?_⟩
  · rw [StatFormal.Wave31ti.uPath]
    nlinarith
  · rw [StatFormal.Wave31ti.uPath, le_div_iff₀ h1]
    nlinarith

/-! ### T36 -/

theorem regions_nested_route : Claims.regions_nested := by
  intro 𝒳 H _ _ _ _ φ κ P Q _ _ hφ hκ
  refine ⟨fun α α' _ hle h1 => StatFormal.Wave30tz.Lower.region_mono_alpha φ P hle h1, ?_, ?_⟩
  · ext z
    simp only [mem_singleton_iff]
    constructor
    · rintro ⟨g, hgm, hgb, hgi, rfl⟩
      have hb1 : ∀ x, g x ≤ 1 := fun x => by simpa using (hgb x).2
      have hint : Integrable g P := Integrable.of_mem_Icc 0 1 hgm.aemeasurable (ae_of_all _ fun x => ⟨(hgb x).1, hb1 x⟩)
      have hnn : 0 ≤ fun x => 1 - g x := fun x => by simp only [Pi.zero_apply]; linarith [hb1 x]
      have hzero : ∫ x, (1 - g x) ∂P = 0 := by
        rw [integral_sub (integrable_const 1) hint, hgi, integral_const, probReal_univ, one_smul, sub_self]
      have hae := (integral_eq_zero_iff_of_nonneg hnn ((integrable_const 1).sub hint)).1 hzero
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      have : g x = 1 := by simp only [Pi.zero_apply] at hx; linarith
      rw [this, one_smul]
    · rintro rfl
      refine ⟨fun _ => 1, measurable_const, fun _ => ⟨zero_le_one, by norm_num⟩, by simp, ?_⟩
      simp only [one_smul]
  · intro α hα α' hα' hle
    exact StatFormal.Wave30tz.dpop_antitone 𝒳 H φ κ P Q α α' hφ hκ hα.1 hle hα'.2

end StatFormal.Wave31tr.RouteExcess
