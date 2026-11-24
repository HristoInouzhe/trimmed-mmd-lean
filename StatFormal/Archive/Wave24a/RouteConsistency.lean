import StatFormal.Archive.Wave24a.Statements
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Route — A and B `thm:consistency` (untrusted)

Reverse triangle inequality for the gauge: `|g a − g b| ≤ g(a − b) ≤ c'‖a − b‖` (subadditivity and symmetry), and for
the `M_K`-norm `|‖La‖ − ‖Lb‖| ≤ ‖L‖‖a − b‖`; the calibrated depth uses uniform continuity of `c_K` on `[−1, 2]`
(Heine–Cantor), which contains the values `g(F z) ∈ [0,1]` and their `1`-neighbourhood.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave24a

theorem consistency_A : Claims.consistency_A := by
  intro Ω E H _ _ _ P PiK L F Fh 𝒦 h
  filter_upwards [h] with ω hω
  rw [Metric.tendstoUniformlyOn_iff] at hω ⊢
  intro ε hε
  have hL : 0 < ‖L‖ + 1 := by positivity
  filter_upwards [hω (ε / (‖L‖ + 1)) (by positivity)] with n hn x hx
  have h1 := hn (PiK x) hx
  rw [dist_eq_norm] at h1
  rw [Real.dist_eq]
  have h2 : |(1 - ‖L (F (PiK x))‖) - (1 - ‖L (Fh n ω (PiK x))‖)| ≤ ‖L‖ * ‖F (PiK x) - Fh n ω (PiK x)‖ := by
    rw [show (1 - ‖L (F (PiK x))‖) - (1 - ‖L (Fh n ω (PiK x))‖) = ‖L (Fh n ω (PiK x))‖ - ‖L (F (PiK x))‖ by ring]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← map_sub, norm_sub_rev]
    exact L.le_opNorm _
  calc _ ≤ ‖L‖ * ‖F (PiK x) - Fh n ω (PiK x)‖ := h2
    _ ≤ (‖L‖ + 1) * ‖F (PiK x) - Fh n ω (PiK x)‖ := by
        gcongr; linarith
    _ < (‖L‖ + 1) * (ε / (‖L‖ + 1)) := by gcongr
    _ = ε := by field_simp

lemma gauge_abs_sub_le {E : Type*} [NormedAddCommGroup E] {g : E → ℝ} {c' : ℝ}
    (hsub : ∀ a b, g (a + b) ≤ g a + g b) (hsym : ∀ a, g (-a) = g a) (hle : ∀ a, g a ≤ c' * ‖a‖) (a b : E) :
    |g a - g b| ≤ c' * ‖a - b‖ := by
  have h1 := hsub (a - b) b
  have h2 := hsub (b - a) a
  rw [sub_add_cancel] at h1 h2
  have h3 : g (b - a) = g (a - b) := by rw [← hsym, neg_sub]
  rw [abs_le]
  constructor <;> linarith [hle (a - b)]

lemma gauge_nonneg {E : Type*} [NormedAddCommGroup E] {g : E → ℝ}
    (hsub : ∀ a b, g (a + b) ≤ g a + g b) (hsym : ∀ a, g (-a) = g a) (a : E) : 0 ≤ g a := by
  have h0 := hsub 0 0
  rw [add_zero] at h0
  have h1 := hsub a (-a)
  rw [add_neg_cancel, hsym] at h1
  linarith

theorem consistency_B : Claims.consistency_B := by
  intro Ω E H _ _ _ P PiK g cK c' F Fh 𝒦 hsub hsym hle hc hF1
  have hgeo : ∀ a b, |(1 - g a) - (1 - g b)| ≤ c' * ‖a - b‖ := fun a b => by
    rw [show (1 - g a) - (1 - g b) = -(g a - g b) by ring, abs_neg]
    exact gauge_abs_sub_le hsub hsym hle a b
  refine ⟨fun n ω x => hgeo _ _, fun h => ?_⟩
  filter_upwards [h] with ω hω
  have hU := (isCompact_Icc (a := (-1 : ℝ)) (b := 2)).uniformContinuousOn_of_continuous hc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hU
  rw [Metric.tendstoUniformlyOn_iff] at hω
  -- geometric depth
  have hgeoU : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ {x | PiK x ∈ 𝒦},
      |g (Fh n ω (PiK x)) - g (F (PiK x))| < ε := by
    intro ε hε
    filter_upwards [hω (ε / (|c'| + 1)) (by positivity)] with n hn x hx
    have h1 := hn (PiK x) hx
    rw [dist_eq_norm, norm_sub_rev] at h1
    calc _ ≤ c' * ‖Fh n ω (PiK x) - F (PiK x)‖ := gauge_abs_sub_le hsub hsym hle _ _
      _ ≤ (|c'| + 1) * ‖Fh n ω (PiK x) - F (PiK x)‖ := by
          gcongr; linarith [le_abs_self c']
      _ < (|c'| + 1) * (ε / (|c'| + 1)) := by gcongr
      _ = ε := by field_simp
  refine ⟨?_, ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hgeoU ε hε] with n hn x hx
    rw [Real.dist_eq, show (1 - g (F (PiK x))) - (1 - g (Fh n ω (PiK x))) =
      g (Fh n ω (PiK x)) - g (F (PiK x)) by ring]
    exact hn x hx
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδU⟩ := hU ε hε
    filter_upwards [hgeoU (min δ 1) (lt_min hδ one_pos)] with n hn x hx
    have h1 := hn x hx
    have h0 := gauge_nonneg hsub hsym (F (PiK x))
    have hF := hF1 _ hx
    have hm : |g (Fh n ω (PiK x)) - g (F (PiK x))| < 1 := h1.trans_le (min_le_right _ _)
    have hmem1 : g (F (PiK x)) ∈ Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
    have hmem2 : g (Fh n ω (PiK x)) ∈ Icc (-1 : ℝ) 2 := by
      have := abs_lt.1 hm; exact ⟨by linarith, by linarith⟩
    have := hδU _ hmem1 _ hmem2 (by rw [Real.dist_eq, abs_sub_comm]; exact h1.trans_le (min_le_left _ _))
    rw [Real.dist_eq] at this ⊢
    rw [show (1 - cK (g (F (PiK x)))) - (1 - cK (g (Fh n ω (PiK x)))) =
      -(cK (g (F (PiK x))) - cK (g (Fh n ω (PiK x)))) by ring, abs_neg]
    exact this

example : Claims.consistency_A := consistency_A
example : Claims.consistency_B := consistency_B

end StatFormal.Wave24a
