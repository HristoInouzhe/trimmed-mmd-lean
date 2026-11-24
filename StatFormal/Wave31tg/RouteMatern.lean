import StatFormal.Wave31tg.Statements
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Route: wave 31tg, the printed smooth function and the Matérn-case interpolation (untrusted proof material)

* `matern_bump` (G1c, `B_analytic.tex:318-321`, no bridge). Metric estimate (`key`): if `A, B ⊆ ℝ^d` are `ε`-separated, the closed `ε/3`-neighbourhood
  of `A` misses the OPEN `2ε/3`-neighbourhood of `B` (a point `x` within `ε/3` of `A` and within `<2ε/3` of `q ∈ B` gives `p ∈ A` with
  `d(p,q) < ε`). For each bounded `A ∈ {S_P, S_Q}` the closed sets `(thickening (2ε/3) A)ᶜ` and `cthickening (ε/3) A` are disjoint, so the smooth
  Urysohn lemma of Mathlib (`exists_contDiff_zero_iff_one_iff_of_isClosed`) gives a `C^∞` `f_A` equal to `1` on `cthickening (ε/3) A` and to `0`
  outside `thickening (2ε/3) A`; its support lies in the closure of the bounded set `thickening (2ε/3) A`, a compact set. The function is
  `g = f_{S_P} − f_{S_Q}`: `f_{S_Q}` vanishes on the closed `ε/3`-neighbourhood of `S_P` (by `key`) and conversely, and `g = 0` outside both open
  `2ε/3`-neighbourhoods; compact support is that of the two summands.
* `matern_interpolation` (G1c, `03_analytic.tex:182-183`): the bridge gives `f` representing the `g` of `matern_bump`; `S_R` is outside both open
  `2ε/3`-neighbourhoods since its points are at distance `≥ ε ≥ 2ε/3` from `S_P` and `S_Q`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace ContDiff

namespace StatFormal.Wave31tg

theorem matern_bump : Claims.matern_bump := by
  intro d SP SQ ε hSP hSQ hε hsep
  -- the metric estimate: the closed ε/3-nbhd of A misses the OPEN 2ε/3-nbhd of B when A, B are ε-separated
  have key : ∀ (A B : Set (EuclideanSpace ℝ (Fin d))), (∀ x ∈ A, ∀ y ∈ B, ε ≤ dist x y) →
      ∀ x ∈ Metric.cthickening (ε / 3) A, x ∉ Metric.thickening (2 * ε / 3) B := by
    intro A B hAB x hx hxB
    obtain ⟨q, hqB, hxq⟩ := Metric.mem_thickening_iff.1 hxB
    have h1 : x ∈ Metric.thickening (ε - dist x q) A :=
      Metric.cthickening_subset_thickening' (by linarith) (by linarith) A hx
    obtain ⟨p, hpA, hxp⟩ := Metric.mem_thickening_iff.1 h1
    have h2 := hAB p hpA q hqB
    have h3 := dist_triangle p x q
    rw [dist_comm p x] at h3
    linarith
  -- one smooth bump (smooth Urysohn for the disjoint closed sets (2ε/3-nbhd)ᶜ and the closed ε/3-nbhd)
  have bump : ∀ A : Set (EuclideanSpace ℝ (Fin d)), Bornology.IsBounded A →
      ∃ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ f ∧ (∀ x ∈ Metric.cthickening (ε / 3) A, f x = 1) ∧
        (∀ x, x ∉ Metric.thickening (2 * ε / 3) A → f x = 0) ∧
        ∃ K, IsCompact K ∧ ∀ x, x ∉ K → f x = 0 := by
    intro A hA
    have hd : Disjoint (Metric.thickening (2 * ε / 3) A)ᶜ (Metric.cthickening (ε / 3) A) := by
      rw [Set.disjoint_compl_left_iff_subset]
      exact Metric.cthickening_subset_thickening' (by linarith) (by linarith) A
    obtain ⟨f, hf, -, h0, h1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
      (Metric.isOpen_thickening.isClosed_compl) Metric.isClosed_cthickening hd
    refine ⟨f, hf, fun x hx => (h1 x).1 hx, fun x hx => (h0 x).1 hx, ?_⟩
    refine ⟨closure (Metric.thickening (2 * ε / 3) A), ?_, fun x hx => (h0 x).1 ?_⟩
    · exact Metric.isCompact_of_isClosed_isBounded isClosed_closure (hA.thickening.closure)
    · exact fun h => hx (subset_closure h)
  obtain ⟨fP, hfP, hP1, hP0, KP, hKP, hKP0⟩ := bump SP hSP
  obtain ⟨fQ, hfQ, hQ1, hQ0, KQ, hKQ, hKQ0⟩ := bump SQ hSQ
  refine ⟨fun x => fP x - fQ x, hfP.sub hfQ, ?_, ?_, ?_, ?_⟩
  · refine HasCompactSupport.intro (hKP.union hKQ) fun x hx => ?_
    simp only [mem_union, not_or] at hx
    simp [hKP0 x hx.1, hKQ0 x hx.2]
  · intro x hx
    have : fQ x = 0 := hQ0 x (key SP SQ hsep x hx)
    simp [hP1 x hx, this]
  · intro x hx
    have : fP x = 0 :=
      hP0 x (key SQ SP (fun a ha b hb => by rw [dist_comm]; exact hsep b hb a ha) x hx)
    simp [hQ1 x hx, this]
  · intro x h1 h2
    simp [hP0 x h1, hQ0 x h2]

theorem matern_interpolation : Claims.matern_interpolation := by
  intro d H _ _ φ hb SR SP SQ ε hSP hSQ hε hRP hRQ hPQ
  obtain ⟨g, hg, hgc, h1, h2, h0⟩ := matern_bump d SP SQ ε hSP hSQ hε hPQ
  obtain ⟨f, hf⟩ := hb g hg hgc
  refine ⟨f, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hf x]
    apply h0
    · intro hmem
      obtain ⟨p, hp, hxp⟩ := Metric.mem_thickening_iff.1 hmem
      have := hRP x hx p hp
      linarith
    · intro hmem
      obtain ⟨q, hq, hxq⟩ := Metric.mem_thickening_iff.1 hmem
      have := hRQ x hx q hq
      linarith
  · rw [hf x]; exact h1 x (Metric.self_subset_cthickening _ hx)
  · rw [hf x]; exact h2 x (Metric.self_subset_cthickening _ hx)

end StatFormal.Wave31tg
