import StatFormal.Wave31tr.RouteRun
import StatFormal.Wave31tr.RouteRunWit
import StatFormal.Wave31tr.RouteRunExists
import StatFormal.Wave30tz.RouteUpper
import StatFormal.Wave30tv.Proofs
import StatFormal.Wave31ta.RouteSmall
import StatFormal.Lib.PaperRunThm.UnitProd

/-!
# Wave 31tr, chunk A2, T6: Theorem 4.2 and Corollary 4.3 for the paper's run (untrusted route)

Proves `Claims.paperRun_betting` and `Claims.paperRun_betting_cond`. Each is `genuine_rules ∧ paperRun_exists_printed ∧` a
universal statement over paper runs. The first two conjuncts are chunk A1's `genuine_rules_route` and
`paperRun_exists_printed_route`; the universal one is T5 (a) (`paperRun_isAdmissible`: a paper run with quantile rules is
admissible) composed with the certified claims of wave 30tv (`thm_betting_cond`, `thm_betting_condexp`, `thm_betting` through
`Wave30tz.Upper.reject_le_delta`, `cor_lower`) and wave 31ta (`cor_lower_v2`), all at `U = Unit`, `ν = dirac ()`.

The transport from `Unit × sample` to the sample space is `StatFormal.Lib.PaperRunThm.UnitProd`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tr.RouteRunThm

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tz StatFormal.Wave30tp StatFormal.Wave31tr.RouteRun
  StatFormal.PaperRunThm

/-- **T6 (iii)–(iv)**: Theorem 4.2 at every true null level and Corollary 4.3 for every paper run. -/
theorem paperRun_betting_route : Claims.paperRun_betting := by
  refine ⟨genuine_rules_route, paperRun_exists_printed_route, ?_⟩
  intro 𝒳 H _ _ _ _ φ κ P Q _ _ J n m α δ lmax s2 w0 v0 qt qu nb cx cy R hφ _ hgrid hδ0 hδ1 hl0 hl1 _ _ hqt hqu hP
  obtain ⟨hpair, hfit, hfrac⟩ := paperRun_isAdmissible hP hφ hqt hqu hl0 (fun j => (hgrid.2 j).1)
  refine ⟨fun j hTV => Upper.reject_le_delta P Q hpair (hgrid.2 j).1 hδ0 hδ1 hl0 hl1 (hfit j) (hfrac j) hTV, ?_⟩
  have h := StatFormal.Wave30tv.cor_lower 𝒳 Unit P Q (Measure.dirac ()) n m R.N J R.lx R.ly R.bat R.A R.B α δ lmax
    (fun j b _ => R.g j b) (fun j k _ => R.lam j k) hpair hδ0 hδ1 hl0 hl1 (fun j => (hgrid.2 j).1) hfit hfrac
  refine (dirac_prod_unit_set ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))
    {ω | StatFormal.Distances.tvDist P Q < R.alphaLo α δ ω.1 ω.2} _ ?_).symm.trans_le h
  exact fun ω => Iff.rfl

/-- **T6 (i), (ii), (v)**: Theorem 4.2 conditionally on batch 0 (pathwise and as a conditional expectation) and the second
sentence of Corollary 4.3, for every paper run. -/
theorem paperRun_betting_cond_route : Claims.paperRun_betting_cond := by
  refine ⟨genuine_rules_route, paperRun_exists_printed_route, ?_⟩
  intro 𝒳 H _ _ _ _ φ κ P Q _ _ J n m α δ lmax s2 w0 v0 qt qu nb cx cy R hφ _ hgrid hδ0 hδ1 hl0 hl1 _ _ hqt hqu hP
  obtain ⟨hpair, hfit, hfrac⟩ := paperRun_isAdmissible hP hφ hqt hqu hl0 (fun j => (hgrid.2 j).1)
  have hv2 := StatFormal.Wave31ta.cor_lower_v2 𝒳 Unit P Q (Measure.dirac ()) n m R.N J R.lx R.ly R.bat R.A R.B α δ lmax
    (fun j b _ => R.g j b) (fun j k _ => R.lam j k) hpair hδ0 hδ1 hl0 hl1 hgrid.1 (fun j => (hgrid.2 j).1) hfit hfrac
  obtain ⟨hmeas, hprob, -⟩ := hv2
  set S : Set ((Fin n → 𝒳) × (Fin m → 𝒳)) := {ω |
    (∃ j, R.alphaLo α δ ω.1 ω.2 = α j ∧ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2) ∧
      StatFormal.Distances.tvDist P Q ≤ R.alphaLo α δ ω.1 ω.2} with hS
  have hSm : MeasurableSet S := by
    refine measurableSet_of_unit_set S _ ?_ hmeas
    exact fun ω => Iff.rfl
  have hSp : sampleLaw P Q n m S ≤ ENNReal.ofReal δ := by
    refine (dirac_prod_unit_set ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) S _ ?_).symm.trans_le
      hprob
    exact fun ω => Iff.rfl
  refine ⟨fun j hTV x₀ y₀ => ?_, fun j hTV => ?_, hSm, hSp⟩
  · exact StatFormal.Wave30tv.thm_betting_cond 𝒳 Unit P Q n m R.N R.lx R.ly R.bat R.A R.B (α j) δ lmax
      (fun b _ => R.g j b) (fun k _ => R.lam j k) hpair (hgrid.2 j).1 hδ0 hδ1 hl0 hl1 (hfit j) (hfrac j) hTV () x₀ y₀
  · exact StatFormal.Wave30tv.thm_betting_condexp 𝒳 Unit P Q (Measure.dirac ()) n m R.N R.lx R.ly R.bat R.A R.B (α j) δ
      lmax (fun b _ => R.g j b) (fun k _ => R.lam j k) hpair (hgrid.2 j).1 hδ0 hδ1 hl0 hl1 (hfit j) (hfrac j) hTV

end StatFormal.Wave31tr.RouteRunThm
