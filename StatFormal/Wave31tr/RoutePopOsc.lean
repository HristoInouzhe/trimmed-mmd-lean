import StatFormal.Wave31tr.Statements
import StatFormal.Wave30tj.RouteBlindLaw

/-!
# Wave 31tr, chunk E2: a fixed kernel is blind to fast oscillation (T45) (untrusted)

`oscLaw ς ν` (density `(1 + ς(ν·))·1_{[0,1]}` against Lebesgue measure on `ℝ`) is the certified `Wave30tj.blindLaw ς ν` (density
`1 + ς(ν·)` against `λ|_{[0,1]}`), by `withDensity_indicator` (`oscLaw_eq_blindLaw`). Then:
* (a) is the certified `Wave30tj.blind_construction` (probability law, `TV = ½`);
* (b)–(d) are the certified `Wave30tj.blind_mmd`, whose MMD limit rests on the certified Riemann–Lebesgue lemma for Bochner integrals
  `Wave30tj.riemann_lebesgue_periodic` (density of continuous compactly supported functions in `L¹`, `Wave30tj.rl_continuous`):
  `‖μ_{Q_ν} − μ_{P_u}‖ → 0`, `D_α ≤ MMD` (`μ_P` lies in every region), and the uniform smallness of the trimmed path.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave31tr.RoutePop

/-- The law `Q_ν` of T45 is the law `Q_N` of the certified kernel-blindness construction (wave 30tj). -/
theorem oscLaw_eq_blindLaw (ς : ℝ → ℝ) (ν : ℕ) : oscLaw ς ν = StatFormal.Wave30tj.blindLaw ς ν := by
  unfold oscLaw StatFormal.Wave30tj.blindLaw StatFormal.Wave30tj.unifLaw
  rw [← withDensity_indicator measurableSet_Icc]
  congr 1
  funext x
  by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [hx]

theorem oscillation_blind_route : Claims.oscillation_blind := by
  intro H _ _ _ _ φ κ ς hφ hκ hςm hςp hςint hςabs
  have hu : StatFormal.Wave30tj.unifLaw = volume.restrict (Icc (0 : ℝ) 1) := rfl
  have hc := StatFormal.Wave30tj.blind_construction ς hςm hςp hςabs hςint
  obtain ⟨-, htend, hle, hev⟩ := StatFormal.Wave30tj.blind_mmd H φ κ ς hφ hκ hςm hςp hςabs hςint
  simp only [oscLaw_eq_blindLaw]
  simp only [hu] at hc htend hle hev
  refine ⟨fun ν hν => ?_, ?_, fun ν hν α hα => hle ν hν α hα.1 hα.2, fun ε hε => ?_⟩
  · obtain ⟨-, -, hprob, -, htv⟩ := hc ν hν
    exact ⟨hprob, htv⟩
  · refine htend.congr fun N => ?_
    simp only [StatFormal.Wave30tj.mmd]
    rw [norm_sub_rev]
  · obtain ⟨N, hN⟩ := eventually_atTop.1 (hev ε hε)
    exact ⟨N, fun ν hν α hα => hN ν hν α hα.1 hα.2⟩

end StatFormal.Wave31tr.RoutePop
