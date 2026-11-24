import StatFormal.Lib.SemiDiscrete.Regularity
import StatFormal.Archive.RobustEquality.Semidual.Proofs

/-!
# Semi-discrete entropic OT: unconditional `Θ` lemmas and convexity in the discrete marginal

Part 1: now that weak duality is certified (`StatFormal.RobustEquality.Semidual.semidual_weak`),
the `Θ`-level results of `Primal` / `Regularity` are restated without the `hweak` hypothesis
(`Theta_eq_Jdual'`, `Theta_eq_iSup'`, `Jdual_le_Theta'`, `Theta_subgradient'`,
`Theta_tv_lipschitz'`, `Theta_convex'`).

Part 2: `lem:convex` (i) of the robust-equality JASA supplement (`supp_proofs.tex:107`), in the
form used in the proof of `thm:coverage-general` (`supp_proofs.tex:530`):
`OT_ε(P̂, Q) ≤ Σ_v w_v OT_ε(P̂_v, Q)` for `P̂ = Σ_v w_v P̂_v` the mixture of the fold laws.

Fold encoding (labelled atoms): the labels are `Fin N` with weights `a_i > 0`, `Σ a = 1`; a fold
assignment `fold : Fin N → Fin V` (surjective: all blocks nonempty) and, for each fold `v`, an
enumeration `e v : Fin (n v) ≃ {i // fold i = v}` of its block. The fold law has labels
`Fin (n v)`, weights `a_{e v j} / w_v` (`foldA`), with `w_v = Σ_{fold i = v} a_i` (`foldWeight`),
and costs `c_{e v j}` (`foldC`). Every enumeration is allowed (the result holds for all of them),
so the frozen `Fin`-indexed `gsoft` / `muDisc` are reused unchanged.

Main result: `Theta_le_sum_fold` (and the finite-valued form `Theta_le_sum_fold_real`):
`Θ_μ(Q) ≤ Σ_v w_v Θ_{μ_v}(Q)`.
Route: strong duality at `μ`, weak duality at each `μ_v`, and the pointwise Jensen step
`g^μ_f(y) = −ε log Σ_v w_v S_v(y) ≤ Σ_v w_v (−ε log S_v(y))`.
-/

noncomputable section
open Finset MeasureTheory
open StatFormal.RobustEquality.Semidual

namespace StatFormal.Foundations.SemiDiscrete

/-! ### Unconditional versions (weak duality is certified) -/

section Unconditional

variable {K : Type} [MeasurableSpace K] {k : ℕ} {ε B : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ}

theorem Theta_eq_Jdual' (h : SDHyp ε a c B) (Q : Measure K) [IsProbabilityMeasure Q]
    {fs : Fin k → ℝ} (hmax : ∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs) :
    Theta ε a c Q = (Jdual ε a c Q fs : EReal) :=
  Theta_eq_Jdual semidual_weak h Q hmax

/-- `Θ(Q) = sup_f J_Q(f)` (attained). -/
theorem Theta_eq_iSup' (h : SDHyp ε a c B) (Q : Measure K) [IsProbabilityMeasure Q] :
    Theta ε a c Q = ⨆ f, (Jdual ε a c Q f : EReal) :=
  Theta_eq_iSup semidual_weak h Q

theorem Jdual_le_Theta' (h : SDHyp ε a c B) (Q : Measure K) [IsProbabilityMeasure Q]
    (f : Fin k → ℝ) : (Jdual ε a c Q f : EReal) ≤ Theta ε a c Q :=
  Jdual_le_Theta semidual_weak h Q f

/-- `Θ(Q)` is finite: `Θ(Q) = J_Q(f*)` for some `f*`. -/
theorem Theta_finite (h : SDHyp ε a c B) (Q : Measure K) [IsProbabilityMeasure Q] :
    ∃ t : ℝ, Theta ε a c Q = t := by
  obtain ⟨fs, hmax⟩ := exists_max_Jdual h Q
  exact ⟨_, Theta_eq_Jdual' h Q hmax⟩

theorem Theta_subgradient' (h : SDHyp ε a c B) (Q Q' : Measure K) [IsProbabilityMeasure Q]
    [IsProbabilityMeasure Q'] {fs : Fin k → ℝ} (hmax : ∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs) :
    Theta ε a c Q = (Jdual ε a c Q fs : EReal) ∧
      ((Jdual ε a c Q fs + ∫ y, gsoft ε a fs c y ∂Q' - ∫ y, gsoft ε a fs c y ∂Q : ℝ) : EReal) ≤
        Theta ε a c Q' :=
  Theta_subgradient semidual_weak h Q Q' hmax

theorem Theta_tv_lipschitz' (h : SDHyp ε a c B) (Q Q' : Measure K) [IsProbabilityMeasure Q]
    [IsProbabilityMeasure Q'] {b δ : ℝ} (hb : ∀ i y y', c i y - c i y' ≤ b)
    (htv : ∀ A, MeasurableSet A → |Q'.real A - Q.real A| ≤ δ) :
    ∃ t t' : ℝ, Theta ε a c Q = t ∧ Theta ε a c Q' = t' ∧ |t - t'| ≤ b * δ :=
  Theta_tv_lipschitz semidual_weak h Q Q' hb htv

theorem Theta_convex' (h : SDHyp ε a c B) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Q Q' : Measure K) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] :
    Theta ε a c (mixMeasure θ Q Q') ≤
      (θ : EReal) * Theta ε a c Q + ((1 - θ : ℝ) : EReal) * Theta ε a c Q' :=
  Theta_convex semidual_weak h hθ0 hθ1 Q Q'

end Unconditional

/-! ### Folds -/

section Fold

variable {N V : ℕ}

/-- Fold weight `w_v = Σ_{i : fold i = v} a_i`. -/
def foldWeight (a : Fin N → ℝ) (fold : Fin N → Fin V) (v : Fin V) : ℝ :=
  ∑ x : {i // fold i = v}, a x

/-- Weights of the fold law: `a_{e v j} / w_v`. -/
def foldA (a : Fin N → ℝ) (fold : Fin N → Fin V) {n : Fin V → ℕ}
    (e : ∀ v, Fin (n v) ≃ {i // fold i = v}) (v : Fin V) : Fin (n v) → ℝ :=
  fun j => a (e v j) / foldWeight a fold v

/-- Costs of the fold law: `c_{e v j}`. -/
def foldC {K : Type*} (c : Fin N → K → ℝ) (fold : Fin N → Fin V) {n : Fin V → ℕ}
    (e : ∀ v, Fin (n v) ≃ {i // fold i = v}) (v : Fin V) : Fin (n v) → K → ℝ :=
  fun j => c (e v j)

variable (fold : Fin N → Fin V) {n : Fin V → ℕ} (e : ∀ v, Fin (n v) ≃ {i // fold i = v})

/-- Regrouping a sum over labels by folds. -/
lemma sum_eq_sum_fold (F : Fin N → ℝ) : ∑ i, F i = ∑ v, ∑ j, F (e v j) := by
  rw [← Fintype.sum_fiberwise fold F]
  exact Finset.sum_congr rfl fun v _ => (Equiv.sum_comp (e v) (fun x => F x)).symm

lemma sum_fold_eq_weight (a : Fin N → ℝ) (v : Fin V) :
    ∑ j, a (e v j) = foldWeight a fold v :=
  Equiv.sum_comp (e v) (fun x => a x)

lemma foldWeight_pos {a : Fin N → ℝ} (ha : ∀ i, 0 < a i) (hsurj : Function.Surjective fold)
    (v : Fin V) : 0 < foldWeight a fold v := by
  obtain ⟨i, hi⟩ := hsurj v
  exact Finset.sum_pos (fun x _ => ha x) ⟨⟨i, hi⟩, mem_univ _⟩

lemma sum_foldWeight {a : Fin N → ℝ} (hsum : ∑ i, a i = 1) : ∑ v, foldWeight a fold v = 1 := by
  rw [← hsum]
  exact Fintype.sum_fiberwise fold a

variable {K : Type} [MeasurableSpace K] {ε B : ℝ} {a : Fin N → ℝ} {c : Fin N → K → ℝ}

/-- The fold problems satisfy the standing hypotheses. -/
lemma SDHyp.toFold (h : SDHyp ε a c B) (hsurj : Function.Surjective fold) (v : Fin V) :
    SDHyp ε (foldA a fold e v) (foldC c fold e v) B where
  hε := h.hε
  ha j := div_pos (h.ha _) (foldWeight_pos fold h.ha hsurj v)
  hsum := by
    simp only [foldA]
    rw [← Finset.sum_div, sum_fold_eq_weight fold e,
      div_self (foldWeight_pos fold h.ha hsurj v).ne']
  hc j := h.hc _
  hB j y := h.hB _ y

/-- Pointwise Jensen step: `g^μ_f(y) ≤ Σ_v w_v g^{μ_v}_{f∘e_v}(y)`. -/
lemma gsoft_le_sum_fold (h : SDHyp ε a c B) (hsurj : Function.Surjective fold) (f : Fin N → ℝ)
    (y : K) :
    gsoft ε a f c y ≤ ∑ v, foldWeight a fold v *
      gsoft ε (foldA a fold e v) (fun j => f (e v j)) (foldC c fold e v) y := by
  set w := foldWeight a fold
  have hw : ∀ v, 0 < w v := foldWeight_pos fold h.ha hsurj
  set S : Fin V → ℝ := fun v =>
    ∑ j, foldA a fold e v j * Real.exp ((f (e v j) - foldC c fold e v j y) / ε)
  have hS : ∀ v, 0 < S v := fun v => sum_exp_pos (h.toFold fold e hsurj v).hk
    (h.toFold fold e hsurj v).ha _
  have hsplit : ∑ i, a i * Real.exp ((f i - c i y) / ε) = ∑ v, w v * S v := by
    rw [sum_eq_sum_fold fold e]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [S, foldA, foldC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show w v = foldWeight a fold v from rfl]
    have hw0 := (foldWeight_pos fold h.ha hsurj v).ne'
    field_simp
  have hJ := exp_wavg_le w (fun v => Real.log (S v)) (fun v => (hw v).le)
    (sum_foldWeight fold h.hsum)
  simp_rw [Real.exp_log (hS _)] at hJ
  rw [← hsplit] at hJ
  have hlog := Real.log_le_log (Real.exp_pos _) hJ
  rw [Real.log_exp] at hlog
  have := mul_le_mul_of_nonneg_left hlog h.hε.le
  unfold gsoft
  rw [Finset.mul_sum] at this
  have e2 : ∑ v, w v * (-ε * Real.log (S v)) = -(∑ v, ε * (w v * Real.log (S v))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  simp only [S] at e2
  rw [e2]
  linarith

/-- Dual step: `J^μ_Q(f) ≤ Σ_v w_v J^{μ_v}_Q(f ∘ e_v)`. -/
lemma Jdual_le_sum_fold (h : SDHyp ε a c B) (hsurj : Function.Surjective fold) (Q : Measure K)
    [IsProbabilityMeasure Q] (f : Fin N → ℝ) :
    Jdual ε a c Q f ≤ ∑ v, foldWeight a fold v *
      Jdual ε (foldA a fold e v) (foldC c fold e v) Q (fun j => f (e v j)) := by
  have hw : ∀ v, 0 < foldWeight a fold v := foldWeight_pos fold h.ha hsurj
  have hlin : ∑ i, a i * f i = ∑ v, foldWeight a fold v *
      ∑ j, foldA a fold e v j * f (e v j) := by
    rw [sum_eq_sum_fold fold e]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [foldA]
    field_simp [(hw v).ne']
  have hint : ∫ y, gsoft ε a f c y ∂Q ≤ ∑ v, foldWeight a fold v *
      ∫ y, gsoft ε (foldA a fold e v) (fun j => f (e v j)) (foldC c fold e v) y ∂Q := by
    have hiv : ∀ v, Integrable (fun y => foldWeight a fold v *
        gsoft ε (foldA a fold e v) (fun j => f (e v j)) (foldC c fold e v) y) Q := fun v =>
      ((h.toFold fold e hsurj v).integrable_gsoft _).const_mul _
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun v _ => hiv v]
    exact integral_mono (h.integrable_gsoft f) (integrable_finsetSum _ fun v _ => hiv v)
      fun y => gsoft_le_sum_fold fold e h hsurj f y
  unfold Jdual
  rw [hlin]
  simp only [mul_add, Finset.sum_add_distrib]
  linarith

lemma EReal.coe_finsetSum {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ((∑ i ∈ s, x i : ℝ) : EReal) = ∑ i ∈ s, (x i : EReal) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, EReal.coe_add, ih]

/-- **Convexity in the discrete marginal over folds** (`lem:convex` (i), finite-valued form):
`Θ_μ(Q) = t`, `Θ_{μ_v}(Q) = t_v` and `t ≤ Σ_v w_v t_v`. -/
theorem Theta_le_sum_fold_real (h : SDHyp ε a c B) (hsurj : Function.Surjective fold)
    (Q : Measure K) [IsProbabilityMeasure Q] :
    ∃ (t : ℝ) (tv : Fin V → ℝ), Theta ε a c Q = t ∧
      (∀ v, Theta ε (foldA a fold e v) (foldC c fold e v) Q = tv v) ∧
      t ≤ ∑ v, foldWeight a fold v * tv v := by
  obtain ⟨fs, hmax⟩ := exists_max_Jdual h Q
  have hv := fun v => exists_max_Jdual (h.toFold fold e hsurj v) Q
  choose fv hfv using hv
  refine ⟨_, fun v => Jdual ε (foldA a fold e v) (foldC c fold e v) Q (fv v),
    Theta_eq_Jdual' h Q hmax, fun v => Theta_eq_Jdual' (h.toFold fold e hsurj v) Q (hfv v), ?_⟩
  refine (Jdual_le_sum_fold fold e h hsurj Q fs).trans ?_
  exact Finset.sum_le_sum fun v _ =>
    mul_le_mul_of_nonneg_left (hfv v _) (foldWeight_pos fold h.ha hsurj v).le

/-- **Convexity in the discrete marginal over folds** (`lem:convex` (i), as used in
`thm:coverage-general`): `OT_ε(Σ_v w_v P̂_v, Q) ≤ Σ_v w_v OT_ε(P̂_v, Q)`, in `EReal`
(both sides are finite, see `Theta_le_sum_fold_real`). -/
theorem Theta_le_sum_fold (h : SDHyp ε a c B) (hsurj : Function.Surjective fold)
    (Q : Measure K) [IsProbabilityMeasure Q] :
    Theta ε a c Q ≤
      ∑ v, (foldWeight a fold v : EReal) * Theta ε (foldA a fold e v) (foldC c fold e v) Q := by
  obtain ⟨t, tv, ht, htv, hle⟩ := Theta_le_sum_fold_real fold e h hsurj Q
  simp_rw [ht, htv, ← EReal.coe_mul]
  rw [← EReal.coe_finsetSum]
  exact EReal.coe_le_coe_iff.mpr hle

end Fold

end StatFormal.Foundations.SemiDiscrete
