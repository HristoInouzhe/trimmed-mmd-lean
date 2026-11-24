import StatFormal.Lib.FourierOps.Mollify
import StatFormal.Lib.MollifierNorm.Margin

/-!
# A smooth Urysohn function with compact support (library, untrusted)

On a finite-dimensional real inner-product space `V`, a compact set `K` and a closed set `F` that are disjoint are separated by a
`C^∞` function with compact support: there is `f : V → ℝ`, `C^∞`, compactly supported, square integrable, with `0 ≤ f ≤ 1`,
`f = 1` on `K` and `f = 0` on `F`.

Proof (the construction of Proposition S4.5 of trimmed-mmd): `Disjoint.exists_cthickenings` gives `δ > 0` with disjoint closed
`δ`-thickenings of `K` and `F`; `E = cthickening (δ/2) K` is closed and bounded, and the mollified indicator `f = 1_E ⋆ b_{δ/2}`
(`b` a smooth probability density supported in the closed unit ball, `MollifierNorm.exists_mollifier`) is smooth with compact
support and values in `[0,1]` (`FourierOps.mollify_smooth_facts`); for `x ∈ K` the ball `B̄(x, δ/2)` lies in `E`, so `f(x) = 1`;
for `y ∈ F` the ball `B̄(y, δ/2)` lies in `cthickening δ F`, which misses `E ⊆ cthickening δ K`, so `f(y) = 0`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff

namespace StatFormal.SupportSeparation

open StatFormal.Wave31tp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- **Smooth Urysohn lemma with compact support**: a compact `K` and a closed `F` disjoint from it are separated by a `C^∞`
function with compact support and values in `[0,1]`, equal to `1` on `K` and `0` on `F` (and square integrable). -/
theorem exists_smooth_one_zero {K F : Set V} (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F) :
    ∃ f : V → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ MemLp f 2 ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x ∈ K, f x = 1) ∧ ∀ x ∈ F, f x = 0 := by
  obtain ⟨δ, hδ, hdisj⟩ := hKF.exists_cthickenings hK hF
  obtain ⟨b, hb, hb0, hb1, hbs⟩ := StatFormal.MollifierNorm.exists_mollifier V
  have hw : 0 < δ / 2 := half_pos hδ
  have hEm : MeasurableSet (cthickening (δ / 2) K) := isClosed_cthickening.measurableSet
  have hEb : Bornology.IsBounded (cthickening (δ / 2) K) := hK.isBounded.cthickening
  obtain ⟨hcd, hcs, h01, h1, h0, -, hL2, -⟩ :=
    StatFormal.FourierOps.mollify_smooth_facts hEm hEb hb hb0 hb1 hbs hw
  refine ⟨mollify (cthickening (δ / 2) K) (dilateR (δ / 2) b), hcd, hcs, hL2, h01, fun x hx => h1 x ?_,
    fun y hy => h0 y ?_⟩
  · exact closedBall_subset_cthickening hx _
  · rw [eq_empty_iff_forall_notMem]
    rintro z ⟨hzy, hzK⟩
    have hzF : z ∈ cthickening δ F :=
      (closedBall_subset_cthickening hy (δ / 2)).trans (cthickening_mono (by linarith) F) hzy
    have hzK' : z ∈ cthickening δ K := cthickening_mono (by linarith) K hzK
    exact hdisj.notMem_of_mem_left hzK' hzF

end StatFormal.SupportSeparation
