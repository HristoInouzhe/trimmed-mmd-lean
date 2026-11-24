import StatFormal.Wave31tr.Statements
import StatFormal.Lib.KernelRun.HorizonWealth
import StatFormal.Lib.KernelRun.DownClosed

/-!
# Wave 31tr, chunk A3, T50 (b)–(d): averaged e-values and the summaries of several bounds (untrusted route)

* `averaged_evalue_route` (T50 (b)): for admissible runs `R_s` on the same data, under `H_{0,α_j}` each wealth at the horizon is an
  e-value (`Lib/KernelRun/HorizonWealth.lean`: the wealth is a nonnegative supermartingale, `E K_N ≤ E K_0 = 1`; no optional
  stopping); Markov's inequality for their average; the grid read upward on the averaged tests is a `δ`-level lower bound by the
  first-true-null argument of `cor:lower` (certified `TrimmedMMD.Lower` route: `exists_first`, `badEvent_subset`, `badEvent_empty`).
* `bound_summaries_route` (T50 (c)–(d)): the larger of two `δ`-level bounds is `2δ`-level (union bound), and the bound read on an
  initial segment of the grid is at most the bound of the whole grid (`Lib/KernelRun/DownClosed.lean`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tr.RouteKernel

open StatFormal.KernelRun StatFormal.Wave30tz StatFormal.Wave30tp StatFormal.TrimmedMMD.Lower

/-- **T50 (c)–(d)**. -/
theorem bound_summaries_route : Claims.bound_summaries :=
  ⟨fun _ _ μ A B a δ hA hB => measure_lt_max_le μ A B a δ hA hB, fun _ _ α rej h hα => alphaLo_castLE_le h α rej hα⟩

/-- **T50 (b)**: averaged e-values of admissible runs on the same data. -/
theorem averaged_evalue_route : Claims.averaged_evalue := by
  intro 𝒳 _ P Q _ _ S J n m α δ lmax R hS hgrid hδ0 _ _ hl1 hadm
  have : IsProbabilityMeasure (sampleLaw P Q n m) := by unfold sampleLaw; infer_instance
  have hev : ∀ j s, StatFormal.Distances.tvDist P Q ≤ α j →
      Measurable (fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => hzWealth (R s) α j ω.1 ω.2) ∧
      (∀ ω : (Fin n → 𝒳) × (Fin m → 𝒳), 0 ≤ hzWealth (R s) α j ω.1 ω.2) ∧
      Integrable (fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => hzWealth (R s) α j ω.1 ω.2) (sampleLaw P Q n m) ∧
      ∫ ω, hzWealth (R s) α j ω.1 ω.2 ∂(sampleLaw P Q n m) ≤ 1 := fun j s hTV =>
    fitRule_horizon_evalue (A := (R s).A) (B := (R s).B) P Q (hadm s).1 (hgrid.2 j).1 hl1 ((hadm s).2.1 j)
      ((hadm s).2.2 j) hTV
  have hmark : ∀ j, StatFormal.Distances.tvDist P Q ≤ α j →
      sampleLaw P Q n m {ω | 1 / δ ≤ (∑ s, hzWealth (R s) α j ω.1 ω.2) / S} ≤ ENNReal.ofReal δ := fun j hTV =>
    measure_avg_ge_le (sampleLaw P Q n m) hS (fun s ω => hzWealth (R s) α j ω.1 ω.2) (fun s ω => (hev j s hTV).2.1 ω)
      (fun s => (hev j s hTV).2.2.1) (fun s => (hev j s hTV).2.2.2) hδ0
  refine ⟨fun j s hTV => ?_, hmark, ?_⟩
  · exact lintegral_horizon_wealth_le_one (A := (R s).A) (B := (R s).B) P Q (hadm s).1 (hgrid.2 j).1 hl1
      ((hadm s).2.1 j) ((hadm s).2.2 j) hTV
  · set t := StatFormal.Distances.tvDist P Q with ht
    have ht0 : 0 ≤ t := StatFormal.Distances.tvDist_nonneg P Q
    set Rj : Fin J → Set ((Fin n → 𝒳) × (Fin m → 𝒳)) := fun j =>
      {ω | 1 / δ ≤ (∑ s, hzWealth (R s) α j ω.1 ω.2) / S} with hRj
    change sampleLaw P Q n m {ω | t < alphaLo α (fun j => ω ∈ Rj j)} ≤ ENNReal.ofReal δ
    by_cases hex : ∃ j, t ≤ α j
    · obtain ⟨j₀, hj₀, hfirst⟩ := exists_first α hex
      exact (measure_mono (badEvent_subset α Rj ht0 j₀ hj₀ hfirst)).trans (hmark j₀ hj₀)
    · push Not at hex
      rw [badEvent_empty α Rj ht0 hex, measure_empty]
      exact zero_le

end StatFormal.Wave31tr.RouteKernel
