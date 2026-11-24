import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrals over disjoint pairs of coordinates of a product measure

Library component F.B (part 3). Untrusted library code: no `Statements.lean` is involved.

Under `Measure.pi fun _ : Fin n => ν`, functions of the disjoint pairs of coordinates
`(ω (2i), ω (2i+1))`, `i < k`, `2k ≤ n`, are independent with law `ν ⊗ ν`. We only need the
multiplicativity of the integral of their product, proved by peeling two coordinates at a time with
`piFinSuccAbove`.

## Main results

* `integral_pi_succ_eq`: `∫ F d(ν^{m+1}) = ∫ F (Fin.cons a w) d(ν ⊗ ν^m)`;
* `integral_pair_mul`: `∫ A(ω 0, ω 1) · B(ω ∘ succ ∘ succ) dν^{m+2} = (∫ A d(ν⊗ν)) (∫ B dν^m)`;
* `pairProd`, `integral_pairProd`: `∫ ∏_{i<k} F(ω(2i), ω(2i+1)) dν^n = (∫ F d(ν⊗ν))^k`;
* `integral_comp_perm`: invariance of `ν^n` under permutations of the coordinates.
-/

noncomputable section
open MeasureTheory

namespace StatFormal.Bernstein

variable {β : Type*} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]

theorem measurable_finCons {m : ℕ} :
    Measurable fun p : β × (Fin m → β) => (Fin.cons p.1 p.2 : Fin (m + 1) → β) := by
  apply measurable_pi_iff.mpr
  intro j
  refine Fin.cases ?_ ?_ j
  · simp only [Fin.cons_zero]
    exact measurable_fst
  · intro i
    simp only [Fin.cons_succ]
    exact (measurable_pi_apply i).comp measurable_snd

/-- Peeling the first coordinate of `ν^{m+1}`. -/
theorem integral_pi_succ_eq {m : ℕ} (F : (Fin (m + 1) → β) → ℝ) :
    ∫ x, F x ∂(Measure.pi fun _ : Fin (m + 1) => ν) =
      ∫ p, F (Fin.cons p.1 p.2) ∂(ν.prod (Measure.pi fun _ : Fin m => ν)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => β) 0 with he
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ν) 0
  have hcons : ∀ (a : β) (w : Fin m → β), e.symm (a, w) = Fin.cons a w := by
    intro a w
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [he]
    · intro i
      simp [he]
  rw [← mp.symm.integral_comp' F]
  congr 1
  ext ⟨a, w⟩
  exact congrArg F (hcons a w)

private theorem integrable_of_abs_le_one {γ : Type*} [MeasurableSpace γ] {μ : Measure γ}
    [IsFiniteMeasure μ] {f : γ → ℝ} (hf : Measurable f) (h : ∀ x, |f x| ≤ 1) : Integrable f μ :=
  (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using h x)

/-- **Two-coordinate peeling**. -/
theorem integral_pair_mul {m : ℕ} (A : β → β → ℝ) (B : (Fin m → β) → ℝ)
    (hA : Measurable fun z : β × β => A z.1 z.2) (hB : Measurable B)
    (hA1 : ∀ x y, |A x y| ≤ 1) (hB1 : ∀ w, |B w| ≤ 1) :
    ∫ ω, A (ω 0) (ω 1) * B (fun j => ω j.succ.succ) ∂(Measure.pi fun _ : Fin (m + 2) => ν) =
      (∫ z, A z.1 z.2 ∂(ν.prod ν)) * ∫ w, B w ∂(Measure.pi fun _ : Fin m => ν) := by
  set Pm := Measure.pi fun _ : Fin m => ν with hPm
  set Pm1 := Measure.pi fun _ : Fin (m + 1) => ν with hPm1
  rw [integral_pi_succ_eq ν]
  have h1 : ∀ p : β × (Fin (m + 1) → β), (Fin.cons p.1 p.2 : Fin (m + 2) → β) 1 = p.2 0 :=
    fun p => rfl
  simp only [Fin.cons_zero, Fin.cons_succ, h1]
  have hmeas1 : Measurable fun p : β × (Fin (m + 1) → β) =>
      A p.1 (p.2 0) * B (fun j => p.2 j.succ) :=
    (hA.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).mul
      (hB.comp (measurable_pi_iff.mpr fun j => (measurable_pi_apply j.succ).comp measurable_snd))
  have hint1 : Integrable (fun p : β × (Fin (m + 1) → β) =>
      A p.1 (p.2 0) * B (fun j => p.2 j.succ)) (ν.prod Pm1) :=
    integrable_of_abs_le_one hmeas1 fun p => by
      rw [abs_mul]
      exact (mul_le_mul (hA1 _ _) (hB1 _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  rw [integral_prod _ hint1]
  have hinner : ∀ a : β, ∫ t, A a (t 0) * B (fun j => t j.succ) ∂Pm1 =
      (∫ b, A a b ∂ν) * ∫ w, B w ∂Pm := fun a => by
    rw [hPm1, integral_pi_succ_eq ν]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact integral_prod_mul (μ := ν) (ν := Pm) (fun b => A a b) B
  simp_rw [hinner]
  rw [integral_mul_const]
  congr 1
  have hAint : Integrable (fun z : β × β => A z.1 z.2) (ν.prod ν) :=
    integrable_of_abs_le_one hA fun z => hA1 _ _
  exact (integral_prod _ hAint).symm

/-- The product `∏_{i<k} F(ω(2i), ω(2i+1))` over `k` disjoint consecutive pairs. -/
def pairProd (F : β → β → ℝ) (k n : ℕ) (hk : 2 * k ≤ n) (ω : Fin n → β) : ℝ :=
  ∏ i : Fin k, F (ω ⟨2 * i, by have := i.2; omega⟩) (ω ⟨2 * i + 1, by have := i.2; omega⟩)

theorem measurable_pairProd {F : β → β → ℝ} (hF : Measurable fun z : β × β => F z.1 z.2)
    (k n : ℕ) (hk : 2 * k ≤ n) : Measurable (pairProd F k n hk) := by
  unfold pairProd
  refine Finset.measurable_prod _ fun i _ => ?_
  have h1 : Measurable fun ω : Fin n → β => (ω ⟨2 * i, by have := i.2; omega⟩,
      ω ⟨2 * i + 1, by have := i.2; omega⟩) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  exact hF.comp h1

omit [MeasurableSpace β] in
theorem abs_pairProd_le_one {F : β → β → ℝ} (hF1 : ∀ x y, |F x y| ≤ 1) (k n : ℕ)
    (hk : 2 * k ≤ n) (ω : Fin n → β) : |pairProd F k n hk ω| ≤ 1 := by
  unfold pairProd
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun _ _ => hF1 _ _

/-- **Independence of disjoint pairs**: `∫ ∏_{i<k} F(ω(2i), ω(2i+1)) dν^n = (∫ F d(ν⊗ν))^k`. -/
theorem integral_pairProd {F : β → β → ℝ} (hF : Measurable fun z : β × β => F z.1 z.2)
    (hF1 : ∀ x y, |F x y| ≤ 1) :
    ∀ (k n : ℕ) (hk : 2 * k ≤ n),
      ∫ ω, pairProd F k n hk ω ∂(Measure.pi fun _ : Fin n => ν) =
        (∫ z, F z.1 z.2 ∂(ν.prod ν)) ^ k := by
  intro k
  induction k with
  | zero =>
    intro n hk
    simp [pairProd]
  | succ k ih =>
    intro n hk
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hk' : 2 * k ≤ m := by omega
    have hsplit : ∀ ω : Fin (m + 2) → β, pairProd F (k + 1) (m + 2) hk ω =
        F (ω 0) (ω 1) * pairProd F k m hk' (fun j => ω j.succ.succ) := fun ω => by
      unfold pairProd
      rw [Fin.prod_univ_succ]
      congr 1
    simp_rw [hsplit]
    rw [integral_pair_mul ν F (pairProd F k m hk') hF (measurable_pairProd hF k m hk') hF1
      (abs_pairProd_le_one hF1 k m hk'), ih m hk', pow_succ']

/-- **Exchangeability**: `ν^n` is invariant under permutations of the coordinates. -/
theorem integral_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : (Fin n → β) → ℝ) :
    ∫ ω, G (fun i => ω (σ i)) ∂(Measure.pi fun _ : Fin n => ν) =
      ∫ ω, G ω ∂(Measure.pi fun _ : Fin n => ν) := by
  have mp := measurePreserving_arrowCongr' (fun _ : Fin n => ν) (fun _ : Fin n => ν) σ.symm
    (MeasurableEquiv.refl β) (fun _ => MeasurePreserving.id ν)
  have h : ∀ ω : Fin n → β,
      (MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl β)) ω = fun i => ω (σ i) :=
    fun ω => by
      ext i
      simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr]
  rw [← mp.integral_comp' G]
  simp_rw [h]

end StatFormal.Bernstein
