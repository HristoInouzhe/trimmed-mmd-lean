import StatFormal.Wave31tr.RouteRun
import StatFormal.Wave31tr.RouteRunWit
import StatFormal.Wave31tr.RouteRunExists
import StatFormal.Wave30tz.Proofs
import StatFormal.Wave31tl.Proofs
import StatFormal.Wave31to.Proofs
import StatFormal.Wave31tn.Proofs
import StatFormal.Wave31tm.Proofs

/-!
# Wave 31tr, chunk A2, T7–T12: the certified consistency and rate results for the paper's run (untrusted route)

Proves `Claims.paper_lo_consistency`, `paper_lo_refining` (T7), `paper_lorate_O`, `paper_same_rate` (T8), `paper_lorate_i`,
`paper_lorate_ii`, `paper_lorate_nologJ`, `paper_lorate_general` (T9), `paper_newrates_i_a`, `paper_newrates_i_b` (T10),
`paper_minimax_ii` (T11) and `paper_alphalo` (T12). Each is `genuine_rules ∧ <existence> ∧ <universal>`:
* the first two conjuncts are chunk A1's `genuine_rules_route` and `paperRun_exists_printed_route` (resp.
  `paperRun_exists_fractions_route` for T7, T12);
* the universal conjunct is T5 (`paperRun_admissible_route`, through `paper_T5`): every paper run with quantile rules is a
  witness run (part (b)), a default run under the printed batches (part (c)) and a sized run at fractions fixed in advance with
  `c = min_b (π_{b+1} − π_b)`, `C₀ = 2`, `B = nb` (part (d)); composed with the certified claims `Wave30tz.lo_consistency`,
  `lo_refining`, `Wave31tl.lorate_O`, `same_rate`, `lorate_i`, `lorate_ii`, `lorate_nologJ`, `lorate_general`,
  `Wave31to.newrates_ii_a`, `newrates_ii_b`, `Wave31tn.minimax_iii` (same `C, N₁`; the grid `rootGrid N` is a grid for
  `N ≥ 1` by `Wave31tn.RouteS3iii.rootGrid_isGrid`) and `Wave31tm.alphalo`. The sized constant is positive
  (`fracGap_pos`): the fractions are strictly increasing and the infimum over the finite `Fin (nb+1)` is attained.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tr.RouteRunThm

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tz StatFormal.Wave30tp StatFormal.Wave31tl
  StatFormal.Wave31tr.RouteRun

/-- T5 (`paperRun_admissible`) with implicit arguments. -/
theorem paper_T5 {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {φ : 𝒳 → H} {κ : ℝ} {J n m : ℕ} {α : Fin J → ℝ} {δ lmax s2 w0 : ℝ}
    {v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ} {qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ} {nb : ℕ}
    {cx cy : ℕ → ℕ} {R : LoRun 𝒳 J n m}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hgrid : IsGrid α) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hl0 : 0 < lmax)
    (hl1 : lmax ≤ 1) (hs2 : 0 < s2) (hw0 : 0 < w0) (hqt : IsQuantileRule qt) (hqu : IsQuantileRule qu)
    (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) :
    R.IsAdmissible α lmax ∧ R.IsWitnessRun φ α δ lmax s2 ∧
      (nb = 2 → NearestCuts n (cx 1) (cx 2) → NearestCuts m (cy 1) (cy 2) → IsDefaultRun R) ∧
      (∀ π : ℕ → ℝ, 1 ≤ nb → IsFractions nb π → BoundariesNear nb π n cx → BoundariesNear nb π m cy →
        R.IsSizedRun (⨅ b : Fin (nb + 1), (π (b + 1) - π b)) 2 nb) :=
  paperRun_admissible_route 𝒳 H φ κ J n m α δ lmax s2 w0 v0 qt qu nb cx cy R hφ hκ hgrid hδ0 hδ1 hl0 hl1 hs2 hw0 hqt hqu hP

/-- The sized constant `c = min_{0 ≤ b ≤ nb} (π_{b+1} − π_b)` of fractions fixed in advance is positive. -/
theorem fracGap_pos {nb : ℕ} {π : ℕ → ℝ} (hπ : IsFractions nb π) : 0 < ⨅ b : Fin (nb + 1), (π (b + 1) - π b) := by
  obtain ⟨b, hb⟩ := Finite.ciInf_mem (fun b : Fin (nb + 1) => π (b + 1) - π b)
  rw [← hb]
  have := hπ.2.2 (show (b : ℕ) ∈ Set.Icc 0 (nb + 1) from ⟨by omega, by omega⟩)
    (show (b : ℕ) + 1 ∈ Set.Icc 0 (nb + 1) from ⟨by omega, by have := b.isLt; omega⟩) (by omega)
  change 0 < π ((b : ℕ) + 1) - π b
  linarith

/-! ### T7 — Proposition 4.4 -/

theorem paper_lo_consistency_route : Claims.paper_lo_consistency := by
  refine ⟨genuine_rules_route, paperRun_exists_fractions_route, ?_⟩
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ J α δ lmax s2 R w0 v0 qt qu nb π cx cy hφ hκ hD hchar hgrid hδ0 hδ1 hl0 hl1 hs2 hw0
    hnb hπ hR
  refine StatFormal.Wave30tz.lo_consistency 𝒳 H φ κ Dφ P Q J α δ lmax s2 (⨅ b : Fin (nb + 1), (π (b + 1) - π b)) 2 nb R
    hφ hκ hD hchar hgrid hδ0 hδ1 hl0 hl1 hs2 (fracGap_pos hπ) fun n m => ?_
  obtain ⟨hqt, hqu, hP, hbx, hby⟩ := hR n m
  have h5 := paper_T5 hφ hκ hgrid hδ0 hδ1 hl0 (by linarith) hs2 hw0 hqt hqu hP
  exact ⟨h5.2.1, h5.2.2.2 π hnb hπ hbx hby⟩

theorem paper_lo_refining_route : Claims.paper_lo_refining := by
  refine ⟨genuine_rules_route, paperRun_exists_fractions_route, ?_⟩
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ J α δ δbar lmax s2 R w0 v0 qt qu nb π cx cy hφ hκ hD hchar hgrid hmesh hδ hδbar
    hδlog hl0 hl1 hs2 hw0 hnb hπ hR
  refine StatFormal.Wave30tz.lo_refining 𝒳 H φ κ Dφ P Q J α δ δbar lmax s2 (⨅ b : Fin (nb + 1), (π (b + 1) - π b)) 2 nb R
    hφ hκ hD hchar hgrid hmesh hδ hδbar hδlog hl0 hl1 hs2 (fracGap_pos hπ) fun n m => ?_
  obtain ⟨hqt, hqu, hP, hbx, hby⟩ := hR n m
  have h5 := paper_T5 hφ hκ (hgrid n m) (hδ n m).1 (hδ n m).2 hl0 (by linarith) hs2 hw0 hqt hqu hP
  exact ⟨h5.2.1, h5.2.2.2 π hnb hπ hbx hby⟩

/-! ### T8 — Theorem 5.7 and "the same rate" -/

theorem paper_lorate_O_route : Claims.paper_lorate_O := by
  refine ⟨genuine_rules_route, paperRun_exists_printed_route, ?_⟩
  intro 𝒳 H _ _ _ _ _ φ κ P Q _ _ c₀ γ J n m α δ s2 η h R w0 v0 qt qu nb cx cy hφ hκ hpm htv hgrid hJ hδ0 hδ1 hs20 hs24
    hw0 hqt hqu hP hdef hn hm hη0 hη1 hmesh
  have h5 := paper_T5 hφ hκ hgrid hδ0 hδ1 (by norm_num) (by norm_num) hs20 hw0 hqt hqu hP
  exact StatFormal.Wave31tl.lorate_O 𝒳 H φ κ P Q c₀ γ J n m α δ s2 η h R hφ hκ hpm htv hgrid hJ hδ0 hδ1 hs20 hs24 h5.2.1
    (h5.2.2.1 hdef.1 hdef.2.1 hdef.2.2) hn hm hη0 hη1 hmesh

theorem paper_same_rate_route : Claims.paper_same_rate := by
  refine ⟨genuine_rules_route, paperRun_exists_printed_route, ?_⟩
  intro 𝒳 H _ _ _ _ _ φ κ P Q _ _ c₀ γ J δ s2 η hφ hκ hpm htv hJ hδ0 hδ1 hs20 hs24 hη0 hη1
  obtain ⟨C, hC0, hC⟩ := StatFormal.Wave31tl.same_rate 𝒳 H φ κ P Q c₀ γ J δ s2 η hφ hκ hpm htv hJ hδ0 hδ1 hs20 hs24 hη0 hη1
  refine ⟨C, hC0, fun n m α R w0 v0 qt qu nb cx cy h hgrid hw0 hqt hqu hP hdef hn hm hmesh => ?_⟩
  have h5 := paper_T5 hφ hκ hgrid hδ0 hδ1 (by norm_num) (by norm_num) hs20 hw0 hqt hqu hP
  exact hC n m α R h hgrid h5.2.1 (h5.2.2.1 hdef.1 hdef.2.1 hdef.2.2) hn hm hmesh

/-! ### T9 — Theorem S4.3 -/

theorem paper_lorate_i_route : Claims.paper_lorate_i := by
  refine ⟨genuine_rules_route, paperRun_exists_printed_route, ?_⟩
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ c₀ γ J n m α δ s2 η h0 ε R w0 v0 qt qu nb cx cy B hφ hκ hD hD2 hpm htv hgrid hJ hδ0
    hδ1 hs20 hs24 hw0 hqt hqu hP hbat hfit1 hfit2 hr1 hN hη0 hη1 hh0 hgaps hε0 hε1 hcond
  have h5 := paper_T5 hφ hκ hgrid hδ0 hδ1 (by norm_num) (by norm_num) hs20 hw0 hqt hqu hP
  exact StatFormal.Wave31tl.lorate_i 𝒳 H φ κ Dφ P Q c₀ γ J n m α δ s2 η h0 ε R B hφ hκ hD hD2 hpm htv hgrid hJ hδ0 hδ1
    hs20 hs24 h5.2.1 hbat hfit1 hfit2 hr1 hN hη0 hη1 hh0 hgaps hε0 hε1 hcond

theorem paper_lorate_ii_route : Claims.paper_lorate_ii := by
  refine ⟨genuine_rules_route, paperRun_exists_printed_route, ?_⟩
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ c₀ γ J n m α δ s2 η h R w0 v0 qt qu nb cx cy B hφ hκ hD hD2 hpm htv hgrid hJ hδ0
    hδ1 hs20 hs24 hw0 hqt hqu hP hbat hfit1 hfit2 hr1 hN hη0 hη1 hmesh
  have h5 := paper_T5 hφ hκ hgrid hδ0 hδ1 (by norm_num) (by norm_num) hs20 hw0 hqt hqu hP
  exact StatFormal.Wave31tl.lorate_ii 𝒳 H φ κ Dφ P Q c₀ γ J n m α δ s2 η h R B hφ hκ hD hD2 hpm htv hgrid hJ hδ0 hδ1
    hs20 hs24 h5.2.1 hbat hfit1 hfit2 hr1 hN hη0 hη1 hmesh

theorem paper_lorate_nologJ_route : Claims.paper_lorate_nologJ := by
  refine ⟨genuine_rules_route, paperRun_exists_printed_route, ?_⟩
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ c₀ γ J n m α δ s2 η h0 h R w0 v0 qt qu nb cx cy B hφ hκ hD hD2 hpm htv hgrid hJ
    hδ0 hδ1 hs20 hs24 hw0 hqt hqu hP hbat hfit1 hfit2 hr1 hN hη0 hη1 hh0 hgaps hmesh hcond
  have h5 := paper_T5 hφ hκ hgrid hδ0 hδ1 (by norm_num) (by norm_num) hs20 hw0 hqt hqu hP
  exact StatFormal.Wave31tl.lorate_nologJ 𝒳 H φ κ Dφ P Q c₀ γ J n m α δ s2 η h0 h R B hφ hκ hD hD2 hpm htv hgrid hJ hδ0
    hδ1 hs20 hs24 h5.2.1 hbat hfit1 hfit2 hr1 hN hη0 hη1 hh0 hgaps hmesh hcond

theorem paper_lorate_general_route : Claims.paper_lorate_general := by
  refine ⟨genuine_rules_route, paperRun_exists_printed_route, ?_⟩
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ ω J n m α δ s2 η h e R w0 v0 qt qu nb cx cy B hφ hκ hD hD2 hmargin htv hgrid hJ
    hδ0 hδ1 hs20 hs24 hw0 hqt hqu hP hbat hfit1 hfit2 hr1 hN hη0 hη1 hmesh he hωe
  have h5 := paper_T5 hφ hκ hgrid hδ0 hδ1 (by norm_num) (by norm_num) hs20 hw0 hqt hqu hP
  exact StatFormal.Wave31tl.lorate_general 𝒳 H φ κ Dφ P Q ω J n m α δ s2 η h e R B hφ hκ hD hD2 hmargin htv hgrid hJ
    hδ0 hδ1 hs20 hs24 h5.2.1 hbat hfit1 hfit2 hr1 hN hη0 hη1 hmesh he hωe

/-! ### T10 — Proposition S4.8 (i) -/

theorem paper_newrates_i_a_route : Claims.paper_newrates_i_a := by
  refine ⟨genuine_rules_route, paperRun_exists_printed_route, ?_⟩
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ ω J n m α δ s2 η h0 ε R w0 v0 qt qu nb cx cy B hφ hκ hD hD2 hκ0 hmono hnn hle htv
    hgrid hJ hδ0 hδ1 hs20 hs24 hw0 hqt hqu hP hbat hfit1 hfit2 hr1 hN hη0 hη1 hh0 hgaps hε0 hε1 hcond
  have h5 := paper_T5 hφ hκ hgrid hδ0 hδ1 (by norm_num) (by norm_num) hs20 hw0 hqt hqu hP
  exact StatFormal.Wave31to.newrates_ii_a 𝒳 H φ κ Dφ P Q ω J n m α δ s2 η h0 ε R B hφ hκ hD hD2 hκ0 hmono hnn hle htv
    hgrid hJ hδ0 hδ1 hs20 hs24 h5.2.1 hbat hfit1 hfit2 hr1 hN hη0 hη1 hh0 hgaps hε0 hε1 hcond

theorem paper_newrates_i_b_route : Claims.paper_newrates_i_b := by
  refine ⟨genuine_rules_route, paperRun_exists_printed_route, ?_⟩
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ ω J n m α δ s2 η h R w0 v0 qt qu nb cx cy B hφ hκ hD hD2 hmono hnn hle htv hgrid
    hJ hδ0 hδ1 hs20 hs24 hw0 hqt hqu hP hbat hfit1 hfit2 hr1 hN hη0 hη1 hmesh
  have h5 := paper_T5 hφ hκ hgrid hδ0 hδ1 (by norm_num) (by norm_num) hs20 hw0 hqt hqu hP
  exact StatFormal.Wave31to.newrates_ii_b 𝒳 H φ κ Dφ P Q ω J n m α δ s2 η h R B hφ hκ hD hD2 hmono hnn hle htv hgrid
    hJ hδ0 hδ1 hs20 hs24 h5.2.1 hbat hfit1 hfit2 hr1 hN hη0 hη1 hmesh

/-! ### T11 — Corollary 5.9 (ii) -/

theorem paper_minimax_ii_route : Claims.paper_minimax_ii := by
  refine ⟨genuine_rules_route, paperRun_exists_printed_route, ?_⟩
  intro κ Dφ a₁ c₀ s2 δ η ha1 ha11 hc0 hs20 hs24 hδ0 hδ1 hη0 hη1
  obtain ⟨C, N₁, hC⟩ := StatFormal.Wave31tn.minimax_iii κ Dφ a₁ c₀ s2 δ η ha1 ha11 hc0 hs20 hs24 hδ0 hδ1 hη0 hη1
  refine ⟨C, N₁, ?_⟩
  intro a₀ 𝒳 H _ _ _ _ _ φ n m P Q R w0 v0 qt qu nb cx cy hφ hκ hD hD2 ha0 ha01 hN hM hw0 hqt hqu hP hdef
  have hN1 : 1 ≤ min n m := by
    have : (10 : ℝ) ≤ ((min n m : ℕ) : ℝ) := (le_max_right N₁ 10).trans hN
    exact_mod_cast (show (1 : ℝ) ≤ ((min n m : ℕ) : ℝ) by linarith)
  have hgrid := StatFormal.Wave31tn.RouteS3iii.rootGrid_isGrid hN1
  have h5 := paper_T5 hφ hκ hgrid hδ0 hδ1 (by norm_num) (by norm_num) hs20 hw0 hqt hqu hP
  exact hC a₀ 𝒳 H φ n m P Q R hφ hκ hD hD2 ha0 ha01 hN hM h5.2.1 (h5.2.2.1 hdef.1 hdef.2.1 hdef.2.2)

/-! ### T12 — Corollary 6.3 -/

theorem paper_alphalo_route : Claims.paper_alphalo := by
  refine ⟨genuine_rules_route, paperRun_exists_fractions_route, ?_⟩
  intro 𝒳 H _ _ _ _ _ φ κ P Q _ _ J α δ lmax s2 R w0 v0 qt qu nb π cx cy hφ hκ hchar htv0 htv1 hgrid hmesh hδ0 hδ1 hl0
    hl1 hs2 hw0 hnb hπ hR
  refine StatFormal.Wave31tm.alphalo 𝒳 H φ κ P Q J α δ lmax s2 (⨅ b : Fin (nb + 1), (π (b + 1) - π b)) 2 nb R hφ hκ
    hchar htv0 htv1 hgrid hmesh hδ0 hδ1 hl0 hl1 hs2 (fracGap_pos hπ) fun n m => ?_
  obtain ⟨hqt, hqu, hP, hbx, hby⟩ := hR n m
  have h5 := paper_T5 hφ hκ (hgrid n m) hδ0 hδ1 hl0 (by linarith) hs2 hw0 hqt hqu hP
  exact ⟨h5.2.1, h5.2.2.2 π hnb hπ hbx hby⟩

end StatFormal.Wave31tr.RouteRunThm
