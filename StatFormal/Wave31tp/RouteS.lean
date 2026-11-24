import StatFormal.Wave31tp.Statements
import StatFormal.Lib.JBall.One
import StatFormal.Lib.GaussMix.Support
import StatFormal.Lib.GaussMix.Basic

/-!
# Wave 31tp, route S: ball-averaged cosine, supports, Gaussian mixtures (untrusted proofs)

L11 (`jball_facts`, `jball_one`) from `Lib/JBall/Basic.lean` and `Lib/JBall/One.lean`;
L27 (`support_density`, `gaussMix_facts`, `gaussMix_distinct`) from `Lib/GaussMix/Support.lean` and
`Lib/GaussMix/Basic.lean`.
-/

noncomputable section
open MeasureTheory

namespace StatFormal.Wave31tp.RouteS

theorem jball_facts_route : Claims.jball_facts := by
  intro d _
  refine ⟨JBall.continuous_jBall, JBall.jBall_neg, JBall.jBall_zero, JBall.abs_jBall_le_one,
    fun y hy => JBall.jBall_lt_one hy, JBall.tendsto_jBall_cocompact, JBall.bddAbove_jBall _,
    JBall.sSup_jBall_Ici_one_lt_one, ?_⟩
  intro V _ _ _ _ _ hd r ξ hr
  exact JBall.avg_cos_inner hd hr ξ

theorem jball_one_route : Claims.jball_one :=
  ⟨fun _ hy => JBall.jBall_one_eq hy, by rw [JBall.sSup_jBall_one_Ici_one]⟩

theorem support_density_route : Claims.support_density := by
  intro V _ _ _ _ _ U p hU hp _ x hx
  exact GaussMix.mem_support_withDensity_indicator_iff volume hU hp hx

theorem gaussMix_facts_route : Claims.gaussMix_facts := by
  intro d n w m B hw hsum hB
  exact ⟨GaussMix.gaussMix_eq_withDensity m (fun i => (hw i).le) hB,
    GaussMix.analyticOnNhd_gaussMixDens w m B, GaussMix.gaussMixDens_pos m hw hsum hB⟩

theorem gaussMix_distinct_route : Claims.gaussMix_distinct := by
  intro d n n' w m B w' m' B' hw _ hB hw' _ hB' hne U hU hUne
  exact GaussMix.exists_ne_of_gaussMix_ne m m' (fun i => (hw i).le) hB (fun i => (hw' i).le) hB' hne
    hU hUne

end StatFormal.Wave31tp.RouteS
