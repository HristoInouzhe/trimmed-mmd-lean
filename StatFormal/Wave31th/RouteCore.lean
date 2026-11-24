import StatFormal.Wave31th.RouteCorePi
import StatFormal.Wave31th.RouteGauss
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Wave 31th, route: the core on `EuclideanSpace ℝ (Fin d)` and the claims (untrusted proof file)

`qdens_euclid` from `core_pi` (the core on `Fin d → ℝ`) by the volume-preserving linear equivalence `EuclideanSpace ℝ (Fin d) ≃L (Fin d → ℝ)`:
the band `{|f − t| ≤ |t|/2}` is compact (`f → 0` at infinity, `t ≠ 0`), the derivative of `f ∘ e⁻¹` does not vanish on the level set (hence one
partial derivative does not), and `P(f⁻¹A) = P'((f ∘ e⁻¹)⁻¹A)` by the change of variables for the equivalence. The three Gaussian claims then
follow from `qdens_euclid` and `gaussian_regular` (the witness `x ↦ ⟨d⋆, φ x⟩` is `C¹` and decays), one half-width being the minimum of
the two (`QDensity_mono'`).
-/

noncomputable section
open MeasureTheory Set Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31th

open StatFormal.Wave12c StatFormal.Wave30tx StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration
  StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.Projection

/-- The thin band `{|f − t| ≤ |t|/2}` is compact when `f → 0` at infinity and `t ≠ 0`. -/
lemma band_compact_euclid {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {t : ℝ} (hc : Continuous f)
    (hT : Tendsto f (comap (fun x => ‖x‖) atTop) (𝓝 0)) (ht : t ≠ 0) :
    IsCompact {x | |f x - t| ≤ |t| / 2} := by
  have hpos : 0 < |t| / 2 := by
    have : 0 < |t| := abs_pos.2 ht
    positivity
  have hev := hT.eventually (Metric.ball_mem_nhds 0 hpos)
  rw [eventually_comap, eventually_atTop] at hev
  obtain ⟨R, hR⟩ := hev
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (by fun_prop) continuous_const
  refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin d))) (r := R)).subset ?_
  intro x hx
  have hx' : |f x - t| ≤ |t| / 2 := hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  push Not at hlt
  have h2 := hR ‖x‖ hlt.le x rfl
  rw [Real.dist_eq, sub_zero] at h2
  have h1 := abs_sub_abs_le_abs_sub t (f x)
  rw [abs_sub_comm] at h1
  have h3 : 0 < |t| := abs_pos.2 ht
  linarith

/-- A nonzero continuous linear functional on `Fin d → ℝ` does not vanish on every basis vector. -/
lemma exists_coord_ne {d : ℕ} {L : (Fin d → ℝ) →L[ℝ] ℝ} (hL : L ≠ 0) :
    ∃ i, L (Pi.single i 1) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hL
  ext w
  have hw : w = ∑ i, w i • (Pi.single i 1 : Fin d → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hw, map_sum]
  simp [hcon]

/-- `rem:qdens (v3, every d)`: the geometric core in every dimension. -/
theorem qdens_euclid : Claims.qdens_euclid := by
  intro d f p U t hf hT ht hne hd hU hLU hp hpos
  set e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (Fin d → ℝ) := EuclideanSpace.equiv (Fin d) ℝ with he
  set f' : (Fin d → ℝ) → ℝ := f ∘ e.symm with hf'
  set p' : (Fin d → ℝ) → ℝ := p ∘ e.symm with hp'
  set U' : Set (Fin d → ℝ) := e.symm ⁻¹' U with hU'
  have hf'd : ContDiff ℝ 1 f' := hf.comp e.symm.contDiff
  have htpos : 0 < |t| / 2 := by
    have : 0 < |t| := abs_pos.2 ht
    positivity
  have hband : IsCompact {y | |f' y - t| ≤ |t| / 2} := by
    have := (band_compact_euclid hf.continuous hT ht).image e.continuous
    convert this using 1
    ext y
    constructor
    · intro hy
      exact ⟨e.symm y, hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      show |f (e.symm (e x)) - t| ≤ |t| / 2
      simpa using hx
  have hne' : ∃ y, f' y = t := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨e x, by simpa [hf'] using hx⟩
  have hd' : ∀ y, f' y = t → ∃ i, fderiv ℝ f' y (Pi.single i 1) ≠ 0 := by
    intro y hy
    have hx : f (e.symm y) = t := hy
    have hne0 := hd (e.symm y) hx
    have hfd : fderiv ℝ f' y = (fderiv ℝ f (e.symm y)).comp
        (e.symm : (Fin d → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin d)) := by
      have h1 : HasFDerivAt f (fderiv ℝ f (e.symm y)) (e.symm y) :=
        ((hf.differentiable one_ne_zero) _).hasFDerivAt
      exact (h1.comp y e.symm.hasFDerivAt).fderiv
    refine exists_coord_ne ?_
    rw [hfd]
    intro h0
    apply hne0
    ext v
    have := congrArg (fun L => L (e v)) h0
    simpa using this
  have hU'o : IsOpen U' := hU.preimage e.symm.continuous
  have hLU' : {y | f' y = t} ⊆ U' := fun y hy => hLU (show f (e.symm y) = t from hy)
  have hp' : ContinuousOn p' U' := hp.comp e.symm.continuous.continuousOn (fun y hy => hy)
  have hpos' : ∀ y, f' y = t → 0 < p' y := fun y hy => hpos _ (show f (e.symm y) = t from hy)
  obtain ⟨r, c, C, hr, hc, hcC, g, hgm, hbd, hg⟩ :=
    Chart.core_pi hf'd htpos hband hne' hd' hU'o hLU' hp' hpos'
  refine ⟨r, c, C, hr, hc, hcC, g, hgm, hbd, fun A hA hAI => ?_⟩
  have hmp : MeasurePreserving (@WithLp.ofLp 2 (Fin d → ℝ)) volume volume := PiLp.volume_preserving_ofLp (Fin d)
  have hemb : MeasurableEmbedding (@WithLp.ofLp 2 (Fin d → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
  have hm1 : MeasurableSet (f ⁻¹' A) := hf.continuous.measurable hA
  have hm2 : MeasurableSet (f' ⁻¹' A) := hf'd.continuous.measurable hA
  have key := hmp.setLIntegral_comp_preimage_emb hemb (fun y => ENNReal.ofReal (p' y)) (s := f' ⁻¹' A)
  have hee : ∀ x : EuclideanSpace ℝ (Fin d), e.symm (WithLp.ofLp x) = x := fun x => e.symm_apply_apply x
  have hpre : (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (f' ⁻¹' A) = f ⁻¹' A := by
    ext x
    show f (e.symm (WithLp.ofLp x)) ∈ A ↔ f x ∈ A
    rw [hee]
  rw [hpre] at key
  have hPeq : (volume.withDensity fun x => ENNReal.ofReal (p x)) (f ⁻¹' A) =
      (volume.withDensity fun y => ENNReal.ofReal (p' y)) (f' ⁻¹' A) := by
    rw [withDensity_apply _ hm1, withDensity_apply _ hm2, ← key]
    refine setLIntegral_congr_fun hm1 fun x _ => ?_
    show ENNReal.ofReal (p x) = ENNReal.ofReal (p (e.symm (WithLp.ofLp x)))
    rw [hee]
  rw [hPeq]
  exact hg A hA hAI

/-- `rem:qdens (v3, every d)`, "(Q) holds". -/
theorem qdens_gauss_Q : Claims.qdens_gauss_Q := by
  intro d H _ _ _ _ φ σ κ α P Q _ _ dstar p U tα hσ hgram _hmeas _hκ _hα0 _hα1 _hD _hmin _hquant hP ht hne
    hgrad hU hLU hcont hpos
  obtain ⟨hC1, hdecay⟩ := gaussian_regular d H φ σ hσ hgram dstar
  obtain ⟨r, c, C, hr, hc, hcC, hQ⟩ := qdens_euclid d (witFn dstar φ) p U tα hC1 hdecay ht hne hgrad hU hLU hcont hpos
  refine ⟨r, c, C, hr, hc, hcC, ?_⟩
  rw [hP]
  exact hQ

/-- `rem:qdens (v3, every d)`, "the same conditions at `u_α` under `Q` give (Q′)". -/
theorem qdens_gauss_Qprime : Claims.qdens_gauss_Qprime := by
  intro d H _ _ _ _ φ σ κ α P Q _ _ dstar q V uα hσ hgram _hmeas _hκ _hα0 _hα1 _hD _hmin _hquant hQ ht hne
    hgrad hV hLV hcont hpos
  obtain ⟨hC1, hdecay⟩ := gaussian_regular d H φ σ hσ hgram dstar
  obtain ⟨r, c, C, hr, hc, hcC, hQd⟩ := qdens_euclid d (witFn dstar φ) q V uα hC1 hdecay ht hne hgrad hV hLV hcont hpos
  refine ⟨r, c, hr, hc, ?_⟩
  rw [hQ]
  exact QDensityLower_of_QDensity hQd

/-- `rem:qdens (v3, every d)`, (Q) and (Q′) with one common half-width. -/
theorem qdens_gauss_Q_Qprime : Claims.qdens_gauss_Q_Qprime := by
  intro d H _ _ _ _ φ σ κ α P Q _ _ dstar p q U V tα uα hσ hgram _hmeas _hκ _hα0 _hα1 _hD _hmin _hqP _hqQ hP hQ
    ht hne hgrad hU hLU hcont hpos hu hune hugrad hV hLV hqcont hqpos
  obtain ⟨hC1, hdecay⟩ := gaussian_regular d H φ σ hσ hgram dstar
  obtain ⟨r1, c, C, hr1, hc, hcC, hQ1⟩ := qdens_euclid d (witFn dstar φ) p U tα hC1 hdecay ht hne hgrad hU hLU hcont hpos
  obtain ⟨r2, c', C', hr2, hc', hcC', hQ2⟩ :=
    qdens_euclid d (witFn dstar φ) q V uα hC1 hdecay hu hune hugrad hV hLV hqcont hqpos
  refine ⟨min r1 r2, c, C, c', lt_min hr1 hr2, hc, hcC, hc', ?_, ?_⟩
  · rw [hP]
    exact QDensity_mono' (min_le_left _ _) hQ1
  · rw [hQ]
    exact QDensityLower_mono' (min_le_right _ _) (QDensityLower_of_QDensity hQ2)

end StatFormal.Wave31th
