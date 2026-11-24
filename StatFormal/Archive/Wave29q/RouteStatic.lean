import StatFormal.Archive.Wave29q.Statements
import StatFormal.Lib.SchrodingerPath.Static

/-!
# Route — `lem:equiv`, static half (untrusted)

`refPlan = refP` and `sqCost = halfSq` by definition; the library `klDiv_refP` (density `q(y)/p_ε(y−x)` of `μ ⊗ ν`
against `R₀₁`, `rnDeriv_mul_rnDeriv`) and `static_iff_entropic` (the affine order-preserving relation between the two
objectives on couplings) give the claims.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave29q

open StatFormal.SchrodingerPath

lemma refPlan_eq_refP (ε : ℝ) (μ : Measure ℝ) : refPlan ε μ = refP ε μ := rfl

lemma sqCost_eq_halfSq : StatFormal.WaveP3b.sqCost = halfSq := rfl

theorem mixture_static : Claims.mixture_static := by
  intro ε μ ν q hε hμ hν hq hq0 hνq hlog hμ2 hν2 π hπ
  rw [refPlan_eq_refP]
  exact klDiv_refP hε hνq hq hq0 hlog hμ2 hν2 hπ

theorem mixture_static_plan : Claims.mixture_static_plan := by
  intro ε μ ν q hε hμ hν hq hq0 hνq hlog hμ2 hν2
  obtain ⟨hne, hiff⟩ := static_iff_entropic hε hνq hq hq0 hlog hμ2 hν2
  rw [sqCost_eq_halfSq]
  refine ⟨hne, fun π => ?_⟩
  unfold IsStaticBridge StatFormal.WaveP3b.IsEntPlan
  rw [sqCost_eq_halfSq]
  exact hiff π

end StatFormal.Wave29q
