import StatFormal.Wave31tu.Statements
import StatFormal.Wave31tq.RouteM21
import StatFormal.Lib.CrossExamples.Mixture

/-!
# Wave 31tu route S: Y20 (e) `lower2pt_not_cross` (S4 :1383-1384; untrusted proof material)

"The pairs of Proposition 5.8 are separated and do not satisfy these hypotheses": for `R, P₀, Q₀` concentrated on pairwise disjoint
measurable sets and `b, c ∈ (0,1)`, the pair `((1−b)R + bP₀, (1−c)R + cQ₀)` has no Lebesgue densities `p, q` crossing as in
Proposition 5.5 (`IsCross`) with `p(x₀) > 0`.

Route: under `IsCross`, `p(x₀) = q(x₀)` (31tq `RouteM.cross_zero`), so `p, q` are continuous and positive on the open set
`W = (x₀ − r, x₀ + r) ∩ {p > 0} ∩ {q > 0}` about `x₀`; by `Lib/CrossExamples/Mixture` (`mixture_ratio_eqOn`), `(1−c)p = (1−b)q`
everywhere on `W`; at `x₀` this forces `b = c`, so `p = q` on `W`, `p − q` is `0` near `x₀` and its derivative at `x₀` is `0`,
not `ℓ₀ > 0`.

* `lower2pt_not_cross_route : Claims.lower2pt_not_cross`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave31tu.RouteS

open StatFormal.Wave31tq

/-- **Y20 (e)**: the two-point pairs `((1−b)R + bP₀, (1−c)R + cQ₀)` with disjoint component supports do not cross as in
Proposition 5.5. -/
theorem lower2pt_not_cross_route : Claims.lower2pt_not_cross := by
  intro R P₀ Q₀ _ _ _ SR SP SQ b c p q x₀ ℓ₀ hSR hSP hSQ hRP hRQ hPQ hR hP hQ _ hb1 _ hc1 ⟨hcross, hpx⟩
  have hpq0 : p x₀ = q x₀ := RouteM.cross_zero hcross
  obtain ⟨hpm, hqm, hp0, hq0, hPd, hQd, ⟨r₀, hr₀, hpc, hqc⟩, -, -, hd, hℓ⟩ := hcross
  have hW₁ : IsOpen (Ioo (x₀ - r₀) (x₀ + r₀) ∩ p ⁻¹' Ioi 0) := hpc.isOpen_inter_preimage isOpen_Ioo isOpen_Ioi
  set W := (Ioo (x₀ - r₀) (x₀ + r₀) ∩ p ⁻¹' Ioi 0) ∩ q ⁻¹' Ioi 0 with hWdef
  have hW : IsOpen W := (hqc.mono inter_subset_left).isOpen_inter_preimage hW₁ isOpen_Ioi
  have hWsub : W ⊆ Ioo (x₀ - r₀) (x₀ + r₀) := fun x hx => hx.1.1
  have hx₀W : x₀ ∈ W :=
    ⟨⟨⟨by linarith, by linarith⟩, show 0 < p x₀ from hpx⟩, show 0 < q x₀ from hpq0 ▸ hpx⟩
  have heq := CrossExamples.mixture_ratio_eqOn (μ := volume) hSR hSP hSQ hRP hRQ hPQ hR hP hQ hb1.le hc1.le hpm hqm hp0 hq0
    hPd hQd hW (hpc.mono hWsub) (hqc.mono hWsub) (fun x hx => hx.1.2) (fun x hx => hx.2)
  have hbc : 1 - c = 1 - b := by
    have h := heq hx₀W
    simp only at h
    rw [← hpq0] at h
    exact mul_right_cancel₀ hpx.ne' h
  have hc' : (1 - c) ≠ 0 := by linarith
  have hpqW : ∀ x ∈ W, p x = q x := fun x hx => by
    have h := heq hx
    simp only at h
    rw [← hbc] at h
    exact mul_left_cancel₀ hc' h
  have hev : (fun x => p x - q x) =ᶠ[𝓝 x₀] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hW.mem_nhds hx₀W) fun x hx => by simp [hpqW x hx]
  have h0 : HasDerivAt (fun x => p x - q x) 0 x₀ := (hasDerivAt_const x₀ (0 : ℝ)).congr_of_eventuallyEq hev
  exact hℓ.ne' (hd.unique h0)

end StatFormal.Wave31tu.RouteS
