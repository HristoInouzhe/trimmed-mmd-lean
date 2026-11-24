import StatFormal.Wave31tm.Statements
import StatFormal.Wave31tl.RouteClaims
import StatFormal.Wave30tx.Proofs
import StatFormal.Wave31ti.Proofs
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs
import StatFormal.Archive.TrimmedMMD.Unconditional.Proofs

/-!
# Wave 31tm route: `cor:alphalo` (untrusted proof material)

The printed proof (`D_trimming.tex:447-468`), with certified ingredients:
* the event `E` of Proposition 16 at level `δ′/3`: the product of the `cor:uniform` events (certified
  `TrimmedMMD.Concentration.uniform_alpha`), probability `≥ 1 − 2δ′/3`; on it, for every level `a ≤ α⋆` and every minimizer,
  `MMD ≤ r_n + Ω(D̂_a + r_n + r_m)` (`Wave30tx.RAlpha.bound_on_event`, the route of the certified `Wave30tx.alphahat`), and
  `D̂_a ≤ D_a + r_n + r_m` (`Unconditional.abs_Demp_sub_Dpop_le`, `r_n(a,·) ≤ r_n(α⋆,·)`);
* `D_a ≤ D₀(α⋆ − a)/(α⋆(1−α⋆))` (certified `Wave31ti.pathconvex_ii`), `D₀ > 0` (certified `ZeroSet.zeroeq`, (A3));
* `P(|α̂_lo − α⋆| > s α⋆(1−α⋆)/D₀) ≤ δ′/3` for `n, m` large (certified `Wave30tz.lo_refining`);
* `P(α̂_lo > α⋆) ≤ δ` (`cor:lower`, certified `Wave30tz.lo_upper`);
* `Ω^{P,Q}(x), Ω^{Q,P}(x) → 0` as `x ↓ 0` (certified `Wave30tx.contact`), `Ω` nondecreasing, `s` with `s ≤ ε/2` and `Ω(3s) < ε/2`
  for both moduli, `r_n, r_m < s/2` for `n, m` large (`Wave30tu.rn_tendsto`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave31tm

open StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.ZeroSet
open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

/-- **Corollary 17** (`cor:alphalo`). -/
theorem alphalo_route : Claims.alphalo := by
  intro 𝒳 H _ _ _ _ _ φ κ P Q _ _ J α δ lmax s2 c C0 Bmax R hφ hκ hchar htv0 htv1 hgrid hmesh hδ0 hδ1 hl0 hl12 hs20
    hc hRuns ε hε δ' hδ'0 hδ'1
  classical
  set αs := StatFormal.Distances.tvDist P Q with hαsdef
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
  have hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ 2 * κ := fun x x' => (norm_sub_le _ _).trans (by linarith [hκ x, hκ x'])
  have htv1' : StatFormal.Distances.tvDist Q P < 1 := by rwa [StatFormal.Distances.tvDist_comm]
  -- `D₀ > 0`
  have hD0 : 0 < Dpop φ P Q 0 := by
    have h := StatFormal.TrimmedMMD.ZeroSet.zeroeq 𝒳 H P Q φ κ 0 hφ hκ hchar le_rfl (by norm_num)
    have hne : Dpop φ P Q 0 ≠ 0 := fun h0 => absurd (h.1 h0) (not_le.2 htv0)
    exact lt_of_le_of_ne (Limits.Dpop_nonneg φ P Q 0) (Ne.symm hne)
  -- the two moduli
  obtain ⟨-, -, -, -, -, hωPQ⟩ := StatFormal.Wave30tx.RContact.contact 𝒳 H P Q φ κ hφ hκ hchar htv1
  obtain ⟨-, -, -, -, -, hωQP⟩ := StatFormal.Wave30tx.RContact.contact 𝒳 H Q P φ κ hφ hκ hchar htv1'
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), StatFormal.Wave30tx.omegaC φ P Q x < ε / 2 ∧
      StatFormal.Wave30tx.omegaC φ Q P x < ε / 2 :=
    (hωPQ.eventually (gt_mem_nhds (half_pos hε))).and (hωQP.eventually (gt_mem_nhds (half_pos hε)))
  obtain ⟨s0, hs0, hs0'⟩ : ∃ s0 > (0 : ℝ), ∀ x : ℝ, 0 < x → x < s0 →
      StatFormal.Wave30tx.omegaC φ P Q x < ε / 2 ∧ StatFormal.Wave30tx.omegaC φ Q P x < ε / 2 := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨r, hr, h⟩ := hev
    exact ⟨r, hr, fun x hx0 hxr => h (by rw [Real.dist_eq, sub_zero, abs_of_pos hx0]; exact hxr) hx0⟩
  set s := min (s0 / 4) (ε / 2) with hsdef
  have hs : 0 < s := lt_min (by positivity) (by positivity)
  have hsε : s ≤ ε / 2 := min_le_right _ _
  have h3s : 3 * s < s0 := by have := min_le_left (s0 / 4) (ε / 2); linarith
  obtain ⟨hω1, hω2⟩ := hs0' (3 * s) (by positivity) h3s
  -- the radii at level `δ′/3`
  set d := δ' / 3 with hddef
  have hd0 : 0 < d := by positivity
  have hd1 : d < 1 := by linarith
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1
    ((StatFormal.Wave30tu.rn_tendsto κ αs d).eventually (gt_mem_nhds (half_pos hs)))
  -- consistency of `α̂_lo` (Proposition 12, refining grids)
  have hαs0 : 0 ≤ αs := htv0.le
  have h1α : 0 < 1 - αs := by linarith
  set s' := s * αs * (1 - αs) / Dpop φ P Q 0 with hs'def
  have hs' : 0 < s' := by positivity
  obtain ⟨N2, hN2⟩ := StatFormal.Wave30tz.lo_refining 𝒳 H φ κ (2 * κ) P Q J α (fun _ _ => δ) δ lmax s2 c C0 Bmax R
    hφ hκ hDφ hchar hgrid hmesh (fun _ _ => ⟨hδ0, hδ1⟩) hδ1
    (fun η hη => by
      obtain ⟨N, hN⟩ := Limits.const_small (Real.log (1 / δ)) η hη
      exact ⟨N, fun n m hn hm => ⟨le_rfl, hN n m hn hm⟩⟩)
    hl0 hl12 hs20 hc hRuns s' hs' d hd0
  refine ⟨max (max N1 N2) 1, fun n m hn hm => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hmN1 : N1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hmN2 : N2 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hrn : rn κ αs d n < s / 2 := hN1 n hnN1
  have hrm : rn κ αs d m < s / 2 := hN1 m hmN1
  have := Limits.sampleLaw_isProb P Q n m
  -- the event of Proposition 16 at level `δ′/3`
  obtain ⟨EX, hEXm, hEXp, hEX⟩ := StatFormal.TrimmedMMD.Concentration.uniform_alpha 𝒳 H P φ κ d n hφ hκ hn1 hd0 hd1
  obtain ⟨EY, hEYm, hEYp, hEY⟩ := StatFormal.TrimmedMMD.Concentration.uniform_alpha 𝒳 H Q φ κ d m hφ hκ hm1 hd0 hd1
  set E1 : Set ((Fin n → 𝒳) × (Fin m → 𝒳)) := EX ×ˢ EY with hE1def
  have hE1m : MeasurableSet E1 := hEXm.prod hEYm
  have hE1p : ENNReal.ofReal (1 - 2 * d) ≤ sampleLaw P Q n m E1 := by
    rw [sampleLaw, hE1def, Measure.prod_prod]
    have h1 : ENNReal.ofReal (1 - d) ≤ (Measure.pi fun _ : Fin n => P) EX :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hEXp
    have h2 : ENNReal.ofReal (1 - d) ≤ (Measure.pi fun _ : Fin m => Q) EY :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hEYp
    calc ENNReal.ofReal (1 - 2 * d) ≤ ENNReal.ofReal ((1 - d) * (1 - d)) := ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = ENNReal.ofReal (1 - d) * ENNReal.ofReal (1 - d) := ENNReal.ofReal_mul (by linarith)
      _ ≤ _ := mul_le_mul' h1 h2
  -- the upper side and the consistency event
  obtain ⟨hmeas, hup⟩ := StatFormal.Wave31tl.Route.upper_le P Q (hgrid n m) hδ0 hδ1 hl0 (by linarith) (hRuns n m).1.1
  set U := {z : (Fin n → 𝒳) × (Fin m → 𝒳) | (R n m).alphaLo (α n m) δ z.1 z.2 ≤ αs} with hUdef
  have hUm : MeasurableSet U := measurableSet_le hmeas measurable_const
  have hUp : ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m U := by
    refine StatFormal.Wave31tl.Route.ofReal_one_sub_le _ hUm hδ0.le (le_trans (measure_mono fun z hz => ?_) hup)
    simp only [hUdef, mem_compl_iff, mem_setOf_eq, not_le] at hz ⊢; exact hz
  set A := {z : (Fin n → 𝒳) × (Fin m → 𝒳) | |(R n m).alphaLo (α n m) δ z.1 z.2 - αs| ≤ s'} with hAdef
  have hAm : MeasurableSet A := measurableSet_le (continuous_abs.measurable.comp (hmeas.sub measurable_const)) measurable_const
  have hAp : ENNReal.ofReal (1 - d) ≤ sampleLaw P Q n m A := by
    refine StatFormal.Wave31tl.Route.ofReal_one_sub_le _ hAm hd0.le (le_trans (measure_mono fun z hz => ?_)
      (hN2 n m hnN2 hmN2))
    simp only [hAdef, mem_compl_iff, mem_setOf_eq, not_le] at hz ⊢; exact hz
  refine ⟨(E1 ∩ U) ∩ A, (hE1m.inter hUm).inter hAm, ?_, ?_⟩
  · have h1 := StatFormal.Wave31tl.Route.ofReal_le_inter (sampleLaw P Q n m) hUm hE1p hUp
    have h2 := StatFormal.Wave31tl.Route.ofReal_le_inter (sampleLaw P Q n m) hAm h1 hAp
    rwa [show 1 - 2 * d + (1 - δ) - 1 + (1 - d) - 1 = 1 - δ - δ' by rw [hddef]; ring] at h2
  · rintro z ⟨⟨hzE, hzU⟩, hzA⟩ pr hpr hmin
    set a := (R n m).alphaLo (α n m) δ z.1 z.2 with hadef
    have ha0 : 0 ≤ a := Limits.run_alphaLo_nonneg (R n m) (hgrid n m) δ z.1 z.2
    have haU : a ≤ αs := hzU
    have ha1 : a < 1 := lt_of_le_of_lt haU htv1
    have hzx : ∀ β ∈ Ico (0 : ℝ) 1,
        Metric.hausdorffDist (region φ β (empirical z.1)) (region φ β P) ≤ rn κ β d n :=
      fun β hβ => hEX hzE.1 β hβ.1 hβ.2
    have hzy : ∀ β ∈ Ico (0 : ℝ) 1,
        Metric.hausdorffDist (region φ β (empirical z.2)) (region φ β Q) ≤ rn κ β d m :=
      fun β hβ => hEY hzE.2 β hβ.1 hβ.2
    obtain ⟨hbP, hbQ⟩ := StatFormal.Wave30tx.RAlpha.bound_on_event P Q hφ hκ htv1 hn1 hm1 z hzx hzy ⟨ha0, haU⟩ hpr hmin
    -- `D̂_a ≤ D_a + r_n + r_m`
    have hDemp : Demp φ z.1 z.2 a ≤ Dpop φ P Q a + rn κ αs d n + rn κ αs d m := by
      have h := abs_Demp_sub_Dpop_le (P := P) (Q := Q) hκ ha0 ha1 (by omega) (by omega) z.1 z.2
      have h1 := hzx a ⟨ha0, ha1⟩
      have h2 := hzy a ⟨ha0, ha1⟩
      have h3 := StatFormal.Wave30tx.RAlpha.rn_mono_alpha (δ := d) hκ0 haU htv1 n
      have h4 := StatFormal.Wave30tx.RAlpha.rn_mono_alpha (δ := d) hκ0 haU htv1 m
      have := (abs_le.1 h).2
      linarith
    -- `D_a ≤ D₀(α⋆ − a)/(α⋆(1−α⋆)) ≤ s`
    have hDa : Dpop φ P Q a ≤ s := by
      have hpc := (StatFormal.Wave31ti.pathconvex_ii 𝒳 H P Q φ κ hφ hκ htv0 htv1).2.2.2 (αs - a) ⟨by linarith, by linarith⟩
      rw [sub_sub_cancel] at hpc
      have hzA' : |a - αs| ≤ s' := hzA
      have hgap : αs - a ≤ s' := by have := (abs_le.1 hzA').1; linarith
      refine hpc.trans ?_
      rw [div_le_iff₀ (by positivity)]
      calc Dpop φ P Q 0 * (αs - a) ≤ Dpop φ P Q 0 * s' := mul_le_mul_of_nonneg_left hgap hD0.le
        _ = s * (αs * (1 - αs)) := by rw [hs'def]; field_simp
    have harg : Demp φ z.1 z.2 a + rn κ αs d n + rn κ αs d m ≤ 3 * s := by linarith
    have hΩP := StatFormal.Wave30tx.RAlpha.omegaC_mono P Q hφ hκ htv1 harg
    have hΩQ := StatFormal.Wave30tx.RAlpha.omegaC_mono Q P hφ hκ htv1' harg
    constructor
    · linarith
    · linarith

end StatFormal.Wave31tm
