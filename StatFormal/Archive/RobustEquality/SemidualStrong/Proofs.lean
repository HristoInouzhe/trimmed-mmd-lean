import StatFormal.Archive.RobustEquality.SemidualStrong.Statements
import StatFormal.Lib.SemiDiscrete.Convex

/-!
# Proofs: `lem:semidual` (i) strong duality, (iii) subgradient, (iv) convexity and TV-Lipschitz
(untrusted proof file)

Bridges the frozen definitions to the library `StatFormal.Foundations.SemiDiscrete`:
`OTdisc` is definitionally `SemiDiscrete.Theta`, `Jdual` is definitionally `SemiDiscrete.Jdual`, and
`Setting` gives `SemiDiscrete.SDHyp` for some cost bound `B`. Weak duality is the certified
`StatFormal.RobustEquality.Semidual.semidual_weak`.

Routes (the paper's): (i) existence of a maximiser of the concave, shift-invariant, coercive `J_Q`,
its first-order condition, and the Gibbs plan `γ* = e^{(f*_i + g_{f*} − c_i)/ε} μ⊗Q` attaining
`J_Q(f*)`; `F_W` by comparing the first-order equations for `i` and `j`; (iii) weak duality at `Q'`
applied to `f*`; (iv) `Θ` is a maximum of affine functions of `Q`, and the TV bound is (iii) in both
directions with `|∫ g̃ d(Q' − Q)| ≤ osc(g̃) ‖Q − Q'‖_TV` (layer cake).
-/

noncomputable section
open MeasureTheory

namespace StatFormal.RobustEquality.SemidualStrong

open StatFormal.RobustEquality.Semidual

lemma setting_hyp {K : Type*} [MeasurableSpace K] {k : ℕ} {ε : ℝ} {a : Fin k → ℝ}
    {c : Fin k → K → ℝ} (hs : Setting ε a c) :
    ∃ B, StatFormal.Foundations.SemiDiscrete.SDHyp ε a c B := by
  obtain ⟨hε, ha, hsum, hc, B, hB⟩ := hs
  exact ⟨B, ⟨hε, ha, hsum, hc, hB⟩⟩

theorem strong_duality : Claims.strong_duality := by
  intro K _ k ε a c Q _ hs
  obtain ⟨B, h⟩ := setting_hyp hs
  obtain ⟨fs, hmax, γ, hγ, hfst, hsnd, hval⟩ :=
    StatFormal.Foundations.SemiDiscrete.strong_duality h Q
  have hΘ := StatFormal.Foundations.SemiDiscrete.Theta_eq_Jdual' h Q hmax
  refine ⟨fs, hmax, hΘ, γ, hγ, hfst, hsnd, ?_⟩
  rw [hval]
  exact hΘ.symm

theorem maximiser_foc : Claims.maximiser_foc := by
  intro K _ k ε a c Q _ fs hs hmax
  obtain ⟨B, h⟩ := setting_hyp hs
  have hfoc := StatFormal.Foundations.SemiDiscrete.foc_Jdual' h hmax
  refine ⟨hfoc, fun i j B' hB' => ?_⟩
  set g := gsoft ε a fs c
  have hg : Measurable g := h.measurable_gsoft fs
  have hgb := h.abs_gsoft_le fs
  have hint : ∀ l, Integrable (fun y => Real.exp ((g y - c l y) / ε)) Q := fun l =>
    StatFormal.Foundations.SemiDiscrete.integrable_exp_of_le ((hg.sub (h.hc l)).div_const ε)
      ((‖fs‖ + B + B) / ε) fun y => by
        refine div_le_div_of_nonneg_right ?_ h.hε.le
        linarith [le_abs_self (g y), hgb y, neg_abs_le (c l y), h.hB l y]
  -- `e^{−f_i/ε} ≥ e^{−B'/ε} e^{−f_j/ε}`
  have hmono : Real.exp (-B' / ε) * ∫ y, Real.exp ((g y - c j y) / ε) ∂Q ≤
      ∫ y, Real.exp ((g y - c i y) / ε) ∂Q := by
    rw [← integral_const_mul]
    refine integral_mono ((hint j).const_mul _) (hint i) fun y => ?_
    simp only
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [← add_div, div_le_div_iff_of_pos_right h.hε]
    linarith [hB' y]
  rw [← hfoc i, ← hfoc j, ← Real.exp_add, Real.exp_le_exp, ← add_div,
    div_le_div_iff_of_pos_right h.hε] at hmono
  linarith

theorem subgradient : Claims.subgradient := by
  intro K _ k ε a c Q Q' _ _ fs hs hmax
  obtain ⟨B, h⟩ := setting_hyp hs
  obtain ⟨hΘ, hsg⟩ := StatFormal.Foundations.SemiDiscrete.Theta_subgradient' h Q Q' hmax
  change StatFormal.Foundations.SemiDiscrete.Theta ε a c Q + _ ≤
    StatFormal.Foundations.SemiDiscrete.Theta ε a c Q'
  rw [hΘ, ← EReal.coe_add]
  refine le_trans (le_of_eq ?_) hsg
  congr 1
  change StatFormal.Foundations.SemiDiscrete.Jdual ε a c Q fs + _ = _
  ring

theorem convex : Claims.convex := by
  intro K _ k ε a c Q Q' _ _ θ hs hθ0 hθ1
  obtain ⟨B, h⟩ := setting_hyp hs
  exact StatFormal.Foundations.SemiDiscrete.Theta_convex' h hθ0 hθ1 Q Q'

theorem tv_lipschitz : Claims.tv_lipschitz := by
  intro K _ k ε a c Q Q' _ _ b hs hb
  obtain ⟨B, h⟩ := setting_hyp hs
  exact StatFormal.Foundations.SemiDiscrete.Theta_tv_lipschitz' h Q Q' hb fun A hA => by
    rw [abs_sub_comm]; exact StatFormal.Distances.abs_measureReal_sub_le_tvDist hA

example : Claims.strong_duality := strong_duality
example : Claims.maximiser_foc := maximiser_foc
example : Claims.subgradient := subgradient
example : Claims.convex := convex
example : Claims.tv_lipschitz := tv_lipschitz

end StatFormal.RobustEquality.SemidualStrong
