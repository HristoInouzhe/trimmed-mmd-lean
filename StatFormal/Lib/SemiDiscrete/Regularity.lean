import StatFormal.Lib.SemiDiscrete.Primal
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Semi-discrete entropic OT: regularity in the second marginal (component F.C′, part 3)

Setting as in `StatFormal.Foundations.SemiDiscrete.Dual` / `.Primal`; `lem:semidual` (ii)–(iv) of
the robust-equality JASA supplement (`supp_proofs.tex:63-105`).

Main results:
* `Jdual_change_measure`: `J_{Q'}(f) = J_Q(f) + ∫ g_f dQ' − ∫ g_f dQ`;
* `subgradient_coupling` (paper (iii), coupling form): given weak duality at `Q'` as an explicit
  hypothesis, every coupling `γ'` of `(μ, Q')` has
  `∫ c dγ' + ε KL(γ'‖μ⊗Q') ≥ J_Q(f) + ∫ g_f d(Q'−Q)`;
* `Theta_subgradient` (paper (iii)): with `f*` a maximiser of `J_Q` and weak duality
  (`Claims.semidual_weak`) as hypothesis, `Θ(Q) = J_Q(f*)` and `Θ(Q') ≥ Θ(Q) + ∫ g_{f*} d(Q' − Q)`;
* `gsoft_osc_le`: `g_f(y) − g_f(y') ≤ b` whenever `c_i(y) − c_i(y') ≤ b` for all `i`;
* `integral_sub_le_osc_mul_tv`: `∫ g dQ' − ∫ g dQ ≤ osc(g) · sup_A |Q' A − Q A|` (layer cake);
* `maxJ_tv_lipschitz`, `Theta_tv_lipschitz` (paper (iv)): `|Θ(Q) − Θ(Q')| ≤ b · sup_A |Q A − Q' A|`;
* `maxJ_convex`, `Theta_convex` (paper (iv)): `Θ(θQ + (1−θ)Q') ≤ θ Θ(Q) + (1−θ) Θ(Q')`.
Statements about `Θ` take weak duality as the hypothesis `hweak : Claims.semidual_weak`; the
`maxJ_*` versions need no such hypothesis.
-/

noncomputable section
open Finset MeasureTheory
open scoped ENNReal
open StatFormal.RobustEquality.Semidual

namespace StatFormal.Foundations.SemiDiscrete

/-! ### Oscillation and total variation -/

/-- Increments / oscillation: `g_f(y) − g_f(y') ≤ b` if `c_i(y) − c_i(y') ≤ b` for all
`i, y, y'`. -/
theorem gsoft_osc_le {K : Type*} {k : ℕ} {ε b : ℝ} {a : Fin k → ℝ} (c : Fin k → K → ℝ)
    (f : Fin k → ℝ) (hk : 0 < k) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
    (hb : ∀ i y y', c i y - c i y' ≤ b) (y y' : K) :
    gsoft ε a f c y - gsoft ε a f c y' ≤ b :=
  gsoft_sub_le c f y y' hk hε ha fun i => hb i y y'

/-- `∫ g dQ' − ∫ g dQ ≤ b δ` when `osc g ≤ b` and `|Q' A − Q A| ≤ δ` for all measurable `A`. -/
theorem integral_sub_le_osc_mul_tv {X : Type*} [MeasurableSpace X] (Q Q' : Measure X)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] {g : X → ℝ} (hg : Measurable g) {b δ : ℝ}
    (hosc : ∀ y y', g y - g y' ≤ b)
    (htv : ∀ A, MeasurableSet A → |Q'.real A - Q.real A| ≤ δ) :
    ∫ y, g y ∂Q' - ∫ y, g y ∂Q ≤ b * δ := by
  have hne : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    have h1 : Q Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr hX, measure_empty] at h1
    exact zero_ne_one h1
  obtain ⟨y0⟩ := id hne
  have hb : 0 ≤ b := by simpa using hosc y0 y0
  have hbdd : BddBelow (Set.range g) :=
    ⟨g y0 - b, by rintro _ ⟨y, rfl⟩; linarith [hosc y0 y]⟩
  set m := ⨅ y, g y
  have hm : ∀ y, m ≤ g y := fun y => ciInf_le hbdd y
  have hmb : ∀ y, g y ≤ m + b := fun y => by
    have : g y - b ≤ m := le_ciInf fun y' => by linarith [hosc y y']
    linarith
  set h : X → ℝ := fun y => g y - m
  have hh : Measurable h := hg.sub measurable_const
  have hgint : ∀ (μ : Measure X) [IsFiniteMeasure μ], Integrable g μ := fun μ _ =>
    integrable_of_abs_le hg (|m| + |b|) fun y => by
      have h1 := hm y
      have h2 := hmb y
      have h3 := neg_abs_le m
      have h4 := le_abs_self m
      have h5 := le_abs_self b
      exact abs_le.mpr ⟨by linarith [abs_nonneg b], by linarith⟩
  have hhint : ∀ (μ : Measure X) [IsFiniteMeasure μ], Integrable h μ := fun μ _ =>
    (hgint μ).sub (integrable_const m)
  have hred : ∫ y, g y ∂Q' - ∫ y, g y ∂Q = ∫ y, h y ∂Q' - ∫ y, h y ∂Q := by
    simp only [h]
    rw [integral_sub (hgint Q') (integrable_const m), integral_sub (hgint Q) (integrable_const m)]
    simp
  have hlayer : ∀ (μ : Measure X) [IsProbabilityMeasure μ],
      ∫ y, h y ∂μ = ∫ t in Set.Ioc 0 b, μ.real {y | t ≤ h y} := fun μ _ =>
    (hhint μ).integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall fun y => sub_nonneg.mpr (hm y))
      (Filter.Eventually.of_forall fun y => show h y ≤ b by simp only [h]; linarith [hmb y])
  have hFint : ∀ (μ : Measure X) [IsProbabilityMeasure μ],
      Integrable (fun t => μ.real {y | t ≤ h y}) (volume.restrict (Set.Ioc (0 : ℝ) b)) := by
    intro μ _
    have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) b)) :=
      isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
    have hanti : Antitone fun t => μ.real {y | t ≤ h y} := fun t t' htt' =>
      measureReal_mono fun y (hy : t' ≤ h y) => (show t ≤ h y from htt'.trans hy)
    refine integrable_of_abs_le hanti.measurable 1 fun t => ?_
    rw [abs_of_nonneg measureReal_nonneg]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  rw [hred, hlayer Q', hlayer Q, ← integral_sub (hFint Q') (hFint Q)]
  calc ∫ t in Set.Ioc 0 b, (Q'.real {y | t ≤ h y} - Q.real {y | t ≤ h y})
      ≤ ∫ t in Set.Ioc 0 b, δ := by
        have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) b)) :=
          isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
        refine integral_mono ((hFint Q').sub (hFint Q)) (integrable_const δ) fun t => ?_
        exact (le_abs_self _).trans (htv _ (measurableSet_le measurable_const hh))
    _ = b * δ := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hb, smul_eq_mul, sub_zero]

/-! ### Subgradient inequality -/

section Subgradient

variable {K : Type*} [MeasurableSpace K] {k : ℕ} {ε : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ}

/-- `J_{Q'}(f) = J_Q(f) + ∫ g_f dQ' − ∫ g_f dQ` (pure algebra). -/
theorem Jdual_change_measure (Q Q' : Measure K) (f : Fin k → ℝ) :
    Jdual ε a c Q' f =
      Jdual ε a c Q f + ∫ y, gsoft ε a f c y ∂Q' - ∫ y, gsoft ε a f c y ∂Q := by
  unfold Jdual; ring

/-- **Subgradient inequality, coupling form** (paper (iii)): if weak duality holds at `Q'`
(hypothesis `hweak'`), then every coupling `γ'` of `(μ, Q')` satisfies
`∫ c dγ' + ε KL(γ'‖μ⊗Q') ≥ J_{Q'}(f) = J_Q(f) + ∫ g_f dQ' − ∫ g_f dQ`. -/
theorem subgradient_coupling (Q Q' : Measure K) (f : Fin k → ℝ)
    (hweak' : ∀ (f : Fin k → ℝ) (γ : Measure (Fin k × K)), IsProbabilityMeasure γ →
      γ.map Prod.fst = muDisc a → γ.map Prod.snd = Q' →
      (Jdual ε a c Q' f : EReal) ≤ ((∫ z, c z.1 z.2 ∂γ : ℝ) : EReal) +
        (ε : EReal) * StatFormal.RobustEquality.klRef γ ((muDisc a).prod Q'))
    (γ' : Measure (Fin k × K)) (hγ' : IsProbabilityMeasure γ') (hfst : γ'.map Prod.fst = muDisc a)
    (hsnd : γ'.map Prod.snd = Q') :
    ((Jdual ε a c Q f + ∫ y, gsoft ε a f c y ∂Q' - ∫ y, gsoft ε a f c y ∂Q : ℝ) : EReal) ≤
      ((∫ z, c z.1 z.2 ∂γ' : ℝ) : EReal) +
        (ε : EReal) * StatFormal.RobustEquality.klRef γ' ((muDisc a).prod Q') := by
  rw [← Jdual_change_measure]
  exact hweak' f γ' hγ' hfst hsnd

end Subgradient

section ThetaReg

variable {K : Type} [MeasurableSpace K] {k : ℕ} {ε B : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ}

/-- `Θ(Q') ≥ J_{Q'}(f)` for every `f`, given weak duality. -/
lemma Jdual_le_Theta (hweak : Claims.semidual_weak) (h : SDHyp ε a c B) (Q' : Measure K)
    [IsProbabilityMeasure Q'] (f : Fin k → ℝ) :
    (Jdual ε a c Q' f : EReal) ≤ Theta ε a c Q' := by
  refine le_sInf ?_
  rintro v ⟨γ, hγ, hfst, hsnd, rfl⟩
  exact hweak K k a f c Q' γ ε h.hε h.ha h.hsum h.hc ⟨B, h.hB⟩ hfst hsnd

/-- **Subgradient inequality** (paper (iii)): with `f*` a maximiser of `J_Q` (so `Θ(Q) = J_Q(f*)`),
`Θ(Q') ≥ Θ(Q) + ∫ g_{f*} dQ' − ∫ g_{f*} dQ`, given weak duality. -/
theorem Theta_subgradient (hweak : Claims.semidual_weak) (h : SDHyp ε a c B) (Q Q' : Measure K)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] {fs : Fin k → ℝ}
    (hmax : ∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs) :
    Theta ε a c Q = (Jdual ε a c Q fs : EReal) ∧
      ((Jdual ε a c Q fs + ∫ y, gsoft ε a fs c y ∂Q' - ∫ y, gsoft ε a fs c y ∂Q : ℝ) : EReal) ≤
        Theta ε a c Q' := by
  refine ⟨Theta_eq_Jdual hweak h Q hmax, ?_⟩
  rw [← Jdual_change_measure]
  exact Jdual_le_Theta hweak h Q' fs

/-! ### Lipschitz continuity in total variation -/

/-- `|max J_Q − max J_{Q'}| ≤ b · δ` where `b` bounds the cost increments and
`δ ≥ sup_A |Q' A − Q A|` (no duality needed). -/
theorem maxJ_tv_lipschitz (h : SDHyp ε a c B) (Q Q' : Measure K) [IsProbabilityMeasure Q]
    [IsProbabilityMeasure Q'] {fs fs' : Fin k → ℝ}
    (hmax : ∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs)
    (hmax' : ∀ f, Jdual ε a c Q' f ≤ Jdual ε a c Q' fs') {b δ : ℝ}
    (hb : ∀ i y y', c i y - c i y' ≤ b)
    (htv : ∀ A, MeasurableSet A → |Q'.real A - Q.real A| ≤ δ) :
    |Jdual ε a c Q fs - Jdual ε a c Q' fs'| ≤ b * δ := by
  have htv' : ∀ A, MeasurableSet A → |Q.real A - Q'.real A| ≤ δ := fun A hA => by
    rw [abs_sub_comm]; exact htv A hA
  have h1 := integral_sub_le_osc_mul_tv Q' Q (h.measurable_gsoft fs)
    (gsoft_osc_le c fs h.hk h.hε h.ha hb) htv'
  have h2 := integral_sub_le_osc_mul_tv Q Q' (h.measurable_gsoft fs')
    (gsoft_osc_le c fs' h.hk h.hε h.ha hb) htv
  have e1 := Jdual_change_measure (ε := ε) (a := a) (c := c) Q Q' fs
  have e2 := Jdual_change_measure (ε := ε) (a := a) (c := c) Q' Q fs'
  have m1 := hmax' fs
  have m2 := hmax fs'
  rw [abs_le]
  constructor <;> linarith

/-- **Lipschitz continuity of `Θ` in total variation** (paper (iv)), given weak duality:
`Θ(Q), Θ(Q')` are finite and `|Θ(Q) − Θ(Q')| ≤ b · δ`. -/
theorem Theta_tv_lipschitz (hweak : Claims.semidual_weak) (h : SDHyp ε a c B)
    (Q Q' : Measure K) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] {b δ : ℝ}
    (hb : ∀ i y y', c i y - c i y' ≤ b)
    (htv : ∀ A, MeasurableSet A → |Q'.real A - Q.real A| ≤ δ) :
    ∃ t t' : ℝ, Theta ε a c Q = t ∧ Theta ε a c Q' = t' ∧ |t - t'| ≤ b * δ := by
  obtain ⟨fs, hmax⟩ := exists_max_Jdual h Q
  obtain ⟨fs', hmax'⟩ := exists_max_Jdual h Q'
  exact ⟨_, _, Theta_eq_Jdual hweak h Q hmax, Theta_eq_Jdual hweak h Q' hmax',
    maxJ_tv_lipschitz h Q Q' hmax hmax' hb htv⟩

/-! ### Convexity -/

/-- The mixture `θ Q + (1 − θ) Q'`. -/
def mixMeasure (θ : ℝ) (Q Q' : Measure K) : Measure K :=
  ENNReal.ofReal θ • Q + ENNReal.ofReal (1 - θ) • Q'

lemma isProb_mixMeasure {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (Q Q' : Measure K)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] :
    IsProbabilityMeasure (mixMeasure θ Q Q') := by
  constructor
  simp only [mixMeasure, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hθ0 (sub_nonneg.mpr hθ1)]
  simp

lemma Jdual_mix (h : SDHyp ε a c B) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (Q Q' : Measure K)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] (f : Fin k → ℝ) :
    Jdual ε a c (mixMeasure θ Q Q') f = θ * Jdual ε a c Q f + (1 - θ) * Jdual ε a c Q' f := by
  unfold Jdual mixMeasure
  rw [integral_add_measure ((h.integrable_gsoft f).smul_measure ENNReal.ofReal_ne_top)
      ((h.integrable_gsoft f).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hθ0,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hθ1), smul_eq_mul, smul_eq_mul]
  ring

/-- Convexity of `Q ↦ max_f J_Q(f)` (no duality needed). -/
theorem maxJ_convex (h : SDHyp ε a c B) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (Q Q' : Measure K)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] {fθ fs fs' : Fin k → ℝ}
    (hmax : ∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs)
    (hmax' : ∀ f, Jdual ε a c Q' f ≤ Jdual ε a c Q' fs') :
    Jdual ε a c (mixMeasure θ Q Q') fθ ≤ θ * Jdual ε a c Q fs + (1 - θ) * Jdual ε a c Q' fs' := by
  rw [Jdual_mix h hθ0 hθ1]
  have := mul_le_mul_of_nonneg_left (hmax fθ) hθ0
  have := mul_le_mul_of_nonneg_left (hmax' fθ) (sub_nonneg.mpr hθ1)
  linarith

/-- **Convexity of `Θ`** (paper (iv)), given weak duality:
`Θ(θQ + (1−θ)Q') ≤ θ Θ(Q) + (1−θ) Θ(Q')`. -/
theorem Theta_convex (hweak : Claims.semidual_weak) (h : SDHyp ε a c B) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (Q Q' : Measure K) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] :
    Theta ε a c (mixMeasure θ Q Q') ≤
      (θ : EReal) * Theta ε a c Q + ((1 - θ : ℝ) : EReal) * Theta ε a c Q' := by
  have := isProb_mixMeasure hθ0 hθ1 Q Q'
  obtain ⟨fθ, hmaxθ⟩ := exists_max_Jdual h (mixMeasure θ Q Q')
  obtain ⟨fs, hmax⟩ := exists_max_Jdual h Q
  obtain ⟨fs', hmax'⟩ := exists_max_Jdual h Q'
  rw [Theta_eq_Jdual hweak h _ hmaxθ, Theta_eq_Jdual hweak h Q hmax,
    Theta_eq_Jdual hweak h Q' hmax', ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
    EReal.coe_le_coe_iff]
  exact maxJ_convex h hθ0 hθ1 Q Q' hmax hmax'

end ThetaReg

end StatFormal.Foundations.SemiDiscrete
