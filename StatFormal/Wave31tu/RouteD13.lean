import StatFormal.Wave31tu.RouteDAux
import StatFormal.Wave31tu.RouteDErr

set_option linter.style.longLine false

/-!
# Wave31tu, chunk D: Y13 `lap_dev` (Lemma S4.25 `lem:lapdev`, S4 :1227-1275, at `σ = 1`)

`lap_dev_of (h3 : Claims.laplace_h1) (h5 : Claims.lap_bv) (h6 : Claims.lap_err) : Claims.lap_dev`.

Route (printed, constants re-derived; status file `STATUS_31tu_D.md` step 1): `Δ(φ) = ∫φ d(P̃ − P) − ∫φ d(Q̃ − Q)`, each bounded one
sample at a time by `LaplaceDev.one_sample_a` (the window `W = [x₀−K, x₀+K]`, Lemma S4.24 on `W` with `V_W ≤ 2K^{1/2}N`, the event
on `W` and on the half-lines off `W`) and `LaplaceDev.one_sample_b` (`R₊ = (x₀,∞)` split into `I₁ = (x₀, x₀+w]`, `I₂ = (x₀+w, x₀+K]`
and `(x₀+K,∞)`, and the mirror `R₋`; `w = min(r⋆, T^{2/5})`; `P(I₁) ≤ p̄w` and `∫_{I₂}h dP ≤ T/(c⋆w)` from (5.1), the signs of
`IsCross` and eq:laperr, `RouteD.dens_bounds`), with the constants collected by `LaplaceDev.collect_a`, `collect_b`. The event
enters through `IntervalEvent`, Lemma S4.24 through `Claims.lap_bv` (Y5), `eq:laphone` through `Claims.laplace_h1` (Y3) and
eq:laperr through `Claims.lap_err` (Y6); `T > 0` is `RouteD.errL_pos`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteD

open StatFormal StatFormal.TrimmedMMD.Concentration StatFormal.LaplaceDev StatFormal.Wave31tq

/-- The rpow forms of the frozen constants in square-root form. -/
theorem rpow_forms {K N x : ℝ} (hK : 0 ≤ K) (hx : 0 ≤ x) :
    K ^ (1 / 4 : ℝ) = √(√K) ∧ N ^ (1 / 2 : ℝ) = √N ∧ K ^ (1 / 2 : ℝ) = √K ∧ x ^ (-(1 / 2 : ℝ)) = 1 / √x :=
  ⟨(sqrt_sqrt_eq_rpow hK).symm, (Real.sqrt_eq_rpow N).symm, (Real.sqrt_eq_rpow K).symm, rpow_neg_half_eq hx⟩

/-- Y13 `lap_dev` (Lemma S4.25, S4 :1227-1275). -/
theorem lap_dev_of (h3 : Claims.laplace_h1) (h5 : Claims.lap_bv) (h6 : Claims.lap_err) : Claims.lap_dev := by
  intro H _ _ _ φ P Q _ _ n m x y x₀ c K g hφ hn hm hc hEx hEy hK hosc
  dsimp only
  have := isProbabilityMeasure_empirical (by omega : n ≠ 0) x
  have := isProbabilityMeasure_empirical (by omega : m ≠ 0) y
  have hc0 : 0 ≤ c := le_trans (Real.log_pos (by norm_num : (1 : ℝ) < 8)).le hc
  have hK0 : (0 : ℝ) ≤ K := by linarith
  set f := Wave31to.wit φ g with hfdef
  set N := max ‖g‖ (1 / 2) with hNdef
  have hN0 : 0 ≤ N := le_trans (by norm_num) (le_max_right ‖g‖ (1 / 2))
  obtain ⟨hfc, hf1, hvar⟩ := wit_facts h3 hφ g hosc (le_max_left ‖g‖ (1 / 2))
  have hIx := intervalDev_of hEx
  have hIy := intervalDev_of hEy
  have hbx := localDev_of h5 hn hc0 hEx
  have hby := localDev_of h5 hm hc0 hEy
  have hεn : 0 ≤ c / n := div_nonneg hc0 (Nat.cast_nonneg n)
  have hεm : 0 ≤ c / m := div_nonneg hc0 (Nat.cast_nonneg m)
  have hcx : 0 ≤ cx c := by unfold cx; linarith
  have hζn : 0 ≤ cx c / n := div_nonneg hcx (Nat.cast_nonneg n)
  have hζm : 0 ≤ cx c / m := div_nonneg hcx (Nat.cast_nonneg m)
  -- `Δ` splits into the two samples
  have hΔ : |linL (empirical x) (empirical y) f - linL P Q f| ≤
      |(∫ z, f z ∂(empirical x)) - ∫ z, f z ∂P| + |(∫ z, f z ∂(empirical y)) - ∫ z, f z ∂Q| := by
    have e : linL (empirical x) (empirical y) f - linL P Q f =
        ((∫ z, f z ∂(empirical x)) - ∫ z, f z ∂P) - ((∫ z, f z ∂(empirical y)) - ∫ z, f z ∂Q) := by
      unfold linL; ring
    rw [e]; exact abs_sub _ _
  have hpiK : piK P Q x₀ K = P.real {z | K < |z - x₀|} + Q.real {z | K < |z - x₀|} := by
    unfold piK; exact measureReal_add_apply
  obtain ⟨hK4, hN2, hK2, -⟩ := rpow_forms (N := N) (x := 1) hK0 zero_le_one
  refine ⟨?_, ?_⟩
  · -- (a)
    have hPa := (one_sample_a hIx hbx hεn hfc hf1 hosc hN0 hvar x₀ hK).trans (collect_a hεn hζn hN0 hK)
    have hQa := (one_sample_a hIy hby hεm hfc hf1 hosc hN0 hvar x₀ hK).trans (collect_a hεm hζm hN0 hK)
    refine hΔ.trans ((add_le_add hPa hQa).trans (le_of_eq ?_))
    simp only [devA', devG', devB, sDev, rDev]
    rw [hpiK, hK4, hN2, hK2]
    ring
  · -- (b)
    intro p q ℓ₀ rs cs pbar hcross hpx hcond hpbar
    have hT := errL_pos h6 hcross hpx hfc hf1 hosc
    refine ⟨hT, ?_⟩
    obtain ⟨T, hTdef⟩ : ∃ T, T = errL P Q f := ⟨_, rfl⟩
    rw [← hTdef] at hT ⊢
    obtain ⟨hpm, hqm, hp0, hq0, hP, hQ, -, hsR, hsL, -, -⟩ := hcross
    obtain ⟨hid, hT0, hAnn, hBnn, -, hT2, -⟩ := h6 P Q p q f hpm hqm hp0 hq0 hP hQ hfc.measurable ⟨1, hf1⟩ hosc
    rw [← hTdef] at hid hT2
    obtain ⟨hmf, hfM, -, -, hMm1⟩ := bdd_facts hf1 hosc
    have hfM' : ∀ z, 0 ≤ (⨆ y, f y) - f z ∧ (⨆ y, f y) - f z ≤ 1 :=
      fun z => ⟨sub_nonneg.2 (hfM z), by linarith [hmf z]⟩
    have hfm' : ∀ z, 0 ≤ f z - (⨅ y, f y) ∧ f z - (⨅ y, f y) ≤ 1 :=
      fun z => ⟨sub_nonneg.2 (hmf z), by linarith [hfM z]⟩
    have hA : ∫ z, ((⨆ y, f y) - f z) * max (p z - q z) 0 ≤ T := by linarith
    have hB : ∫ z, (f z - ⨅ y, f y) * max (q z - p z) 0 ≤ T := by linarith
    obtain ⟨hpi, -⟩ := StatFormal.BandLimited.integrable_and_integral_of_density hpm hp0 hP
    obtain ⟨hqi, -⟩ := StatFormal.BandLimited.integrable_and_integral_of_density hqm hq0 hQ
    have hrs : 0 < rs := hcond.1
    have hrs1 : rs ≤ 1 := hcond.2.1
    have hcs : 0 < cs := hcond.2.2.1
    have hpbar0 : 0 ≤ pbar := le_trans (add_nonneg (hp0 x₀) (hq0 x₀)) (hpbar x₀ ⟨by linarith, by linarith⟩)
    obtain ⟨w, hw⟩ : ∃ w, w = min rs (T ^ (2 / 5 : ℝ)) := ⟨_, rfl⟩
    have hw0 : 0 < w := hw ▸ width_pos hT hrs
    have hwr : w ≤ rs := hw ▸ width_le T rs
    have hw1 : w ≤ 1 := hwr.trans hrs1
    obtain ⟨h1Rp, h1Lp, h2Rp, h2Lp⟩ := dens_bounds (ρ := p) (K := K) hpi hqi hpm hp0 hp0 hq0
      (fun z => le_add_of_nonneg_right (hq0 z)) hcond hpbar hw0 hwr hsR hsL hfc hfM' hfm' hA hB
    obtain ⟨h1Rq, h1Lq, h2Rq, h2Lq⟩ := dens_bounds (ρ := q) (K := K) hpi hqi hqm hq0 hp0 hq0
      (fun z => le_add_of_nonneg_left (hp0 z)) hcond hpbar hw0 hwr hsR hsL hfc hfM' hfm' hA hB
    rw [← hP] at h1Rp h1Lp h2Rp h2Lp
    rw [← hQ] at h1Rq h1Lq h2Rq h2Lq
    have hPb := one_sample_b hIx hbx hεn hfc hf1 hosc hN0 hvar x₀ hK hw0 hw1 h1Rp h1Lp h2Rp h2Lp
    have hQb := one_sample_b hIy hby hεm hfc hf1 hosc hN0 hvar x₀ hK hw0 hw1 h1Rq h1Lq h2Rq h2Lq
    have hCn := collect_b (π := P.real {z | K < |z - x₀|}) hεn hζn hN0 hK hT hT2 hrs hrs1 hcs hpbar0
    have hCm := collect_b (π := Q.real {z | K < |z - x₀|}) hεm hζm hN0 hK hT hT2 hrs hrs1 hcs hpbar0
    rw [← hw] at hCn hCm
    obtain ⟨-, -, -, hcr⟩ := rpow_forms (N := N) (x := cs * rs) hK0 (mul_pos hcs hrs).le
    refine hΔ.trans ((add_le_add (hPb.trans hCn) (hQb.trans hCm)).trans (le_of_eq ?_))
    simp only [devA, devG, devB, lapA0, lapA1, sDev, rDev]
    rw [hpiK, hK4, hN2, hK2, hcr, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    ring

end StatFormal.Wave31tu.RouteD
