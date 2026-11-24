import StatFormal.Lib.Concentration.ContractionCoord
import StatFormal.Lib.Concentration.Symmetrization
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Symmetrisation for independent, non-identically distributed summands; two-sample symmetrisation

Library component (concentration). Untrusted library code. Generalises `Symmetrization.lean` (one i.i.d. sample) to
independent coordinates `W_i ∼ μ_i` with coordinate-specific classes (van der Vaart and Wellner 1996, Lemma 2.3.6, for
independent non-identically distributed processes), and specialises it to two independent samples
`X ∼ P^{⊗n}`, `Y ∼ Q^{⊗m}` with one joint supremum.

Setting: a finite index type `ι`, probability measures `μ i` on `X`, a countable nonempty index type `T`, measurable
`g t i : X → ℝ` with `|g t i x| ≤ B`; the sample is `w : ι → X` under `Measure.pi μ`. The signs are averaged exactly
(`signE`, uniform on `{±1}^ι`, independent of `w` by construction).

## Proof route
As in the i.i.d. case: ghost sample `w'` and Fubini (`integral_prod`); the pair sample is moved to
`Measure.pi (fun i => μ i ⊗ μ i)` (`measurePreserving_arrowProdEquivProdArrow`, which allows different `μ i`); swapping
`(w_i, w'_i)` on the coordinates with `σ_i = −1` preserves that law coordinatewise (`Measure.pi_map_pi`,
`Measure.prod_swap`) — this is where "swapping `W_k ↔ W'_k` coordinatewise preserves the joint law" is used for
non-identical coordinates; then `sup(a + b) ≤ sup a + sup b` and `σ ↦ −σ` invariance. The two-sample form uses
`ι = Fin n ⊕ Fin m`, `μ = (P, …, P, Q, …, Q)` and `measurePreserving_sumPiEquivProdPi`.

## Main results
* `integral_iSup_sumDev_le`: `E sup_t ∑_i (g_{t,i}(W_i) − E g_{t,i}(W_i)) ≤ 2 E_{W,σ} sup_t ∑_i σ_i g_{t,i}(W_i)`;
* `integral_iSup_empDev2_le` (**two-sample, one joint supremum**):
  `E sup_t [(P_n − P) g₁_t + (Q_m − Q) g₂_t] ≤ 2 E_{X,Y,σ} sup_t [n⁻¹∑ σ_i g₁_t(X_i) + m⁻¹∑ σ'_j g₂_t(Y_j)]`,
  with one sign vector `(σ, σ') ∈ {±1}^{Fin n ⊕ Fin m}`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

namespace StatFormal.Concentration

variable {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∑_i (g t i (w i) − ∫ g t i dμ_i)`. -/
def sumDev (μ : ι → Measure X) {T : Type*} (g : T → ι → X → ℝ) (w : ι → X) (t : T) : ℝ :=
  ∑ i, (g t i (w i) - ∫ y, g t i y ∂μ i)

/-- `E_σ sup_t ∑_i σ_i g t i (w i)`. -/
def radAvgι {T : Type*} (g : T → ι → X → ℝ) (w : ι → X) : ℝ :=
  signE (fun σ => ⨆ t, ∑ i, rsign (σ i) * g t i (w i))

omit [DecidableEq ι] in
theorem abs_sum_le_card_mul {c : ι → ℝ} {C : ℝ} (h : ∀ i, |c i| ≤ C) :
    |∑ i, c i| ≤ Fintype.card ι * C := by
  calc |∑ i, c i| ≤ ∑ i, |c i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, C := sum_le_sum fun i _ => h i
    _ = Fintype.card ι * C := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

variable (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)] {T : Type*} [Countable T] [Nonempty T]
  {g : T → ι → X → ℝ} {B : ℝ}

omit [Nonempty T] [∀ i, IsProbabilityMeasure (μ i)] in
theorem measurable_radAvgι (hg : ∀ t i, Measurable (g t i)) :
    Measurable fun w : ι → X => radAvgι g w := by
  unfold radAvgι signE
  refine Measurable.const_mul (Finset.measurable_fun_sum _ fun σ _ => ?_) _
  exact Measurable.iSup fun t => Finset.measurable_fun_sum _ fun i _ =>
    ((hg t i).comp (measurable_pi_apply i)).const_mul _

omit [MeasurableSpace X] [Countable T] [∀ i, IsProbabilityMeasure (μ i)] in
theorem abs_radAvgι_le (hB : ∀ t i y, |g t i y| ≤ B) (w : ι → X) :
    |radAvgι g w| ≤ Fintype.card ι * B :=
  abs_signE_le fun σ => abs_ciSup_le fun t => abs_sum_le_card_mul fun i => by
    rw [abs_mul, abs_rsign, one_mul]; exact hB _ _ _

omit [DecidableEq ι] [Countable T] [Nonempty T] in
theorem abs_sumDev_le (hB : ∀ t i y, |g t i y| ≤ B) (w : ι → X) (t : T) :
    |sumDev μ g w t| ≤ Fintype.card ι * (2 * B) := by
  refine abs_sum_le_card_mul fun i => (abs_sub _ _).trans ?_
  have h2 : |∫ y, g t i y ∂μ i| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := μ i) (f := g t i) (C := B)
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hB t i y)
    simpa [Real.norm_eq_abs] using this
  linarith [hB t i (w i)]

omit [DecidableEq ι] [Countable T] [Nonempty T] [∀ i, IsProbabilityMeasure (μ i)] in
theorem measurable_sumDev (hg : ∀ t i, Measurable (g t i)) (t : T) :
    Measurable fun w : ι → X => sumDev μ g w t :=
  Finset.measurable_fun_sum _ fun i _ => ((hg t i).comp (measurable_pi_apply i)).sub_const _

/-- **Symmetrisation for independent, non-identically distributed summands** (one-sided). -/
theorem integral_iSup_sumDev_le (hg : ∀ t i, Measurable (g t i)) (hB : ∀ t i y, |g t i y| ≤ B) :
    ∫ w, ⨆ t, sumDev μ g w t ∂(Measure.pi μ) ≤ 2 * ∫ w, radAvgι g w ∂(Measure.pi μ) := by
  set Pn := Measure.pi μ with hPn
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hgi : ∀ t i, Measurable fun w : ι → X => g t i (w i) := fun t i =>
    (hg t i).comp (measurable_pi_apply i)
  have hsub2 : ∀ t i a b, |g t i a - g t i b| ≤ 2 * B := fun t i a b =>
    (abs_sub _ _).trans (by linarith [hB t i a, hB t i b])
  -- the ghost-sample supremum on the product
  set W : (ι → X) × (ι → X) → ℝ :=
    fun z => ⨆ t, ∑ i, (g t i (z.1 i) - g t i (z.2 i)) with hW
  have hWb : ∀ z, |W z| ≤ N * (2 * B) := fun z => abs_ciSup_le fun t =>
    abs_sum_le_card_mul fun i => hsub2 t i _ _
  have hWm : Measurable W := Measurable.iSup fun t => Finset.measurable_fun_sum _ fun i _ =>
    ((hgi t i).comp measurable_fst).sub ((hgi t i).comp measurable_snd)
  have hWint : Integrable W (Pn.prod Pn) :=
    Integrable.of_bound hWm.aestronglyMeasurable (N * (2 * B)) (ae_of_all _ fun z => hWb z)
  -- Step A/B: Jensen for the supremum and Fubini
  have hA : ∀ w, ⨆ t, sumDev μ g w t ≤ ∫ w', W (w, w') ∂Pn := by
    intro w
    refine ciSup_le fun t => ?_
    have hIi : ∀ i, Integrable (fun w' : ι → X => g t i (w' i)) Pn := fun i =>
      Integrable.of_bound (hgi t i).aestronglyMeasurable B (ae_of_all _ fun w' => by
        rw [Real.norm_eq_abs]; exact hB t i _)
    have hrep : sumDev μ g w t = ∫ w', ∑ i, (g t i (w i) - g t i (w' i)) ∂Pn := by
      rw [integral_finsetSum]
      · unfold sumDev
        refine sum_congr rfl fun i _ => ?_
        rw [integral_sub (integrable_const _) (hIi i), integral_const, probReal_univ, one_smul,
          MeasureTheory.integral_comp_eval (μ := μ) (f := g t i) (hg t i).aestronglyMeasurable]
      · intro i _; exact (integrable_const _).sub (hIi i)
    rw [hrep]
    refine integral_mono ?_ ?_ fun w' => ?_
    · exact Integrable.of_bound (Finset.measurable_fun_sum _ fun i _ =>
        measurable_const.sub (hgi t i)).aestronglyMeasurable (N * (2 * B))
        (ae_of_all _ fun w' => by
          rw [Real.norm_eq_abs]; exact abs_sum_le_card_mul fun i => hsub2 t i _ _)
    · exact Integrable.of_bound (hWm.comp measurable_prodMk_left).aestronglyMeasurable
        (N * (2 * B)) (ae_of_all _ fun w' => hWb _)
    · exact le_ciSup (f := fun t => ∑ i, (g t i (w i) - g t i (w' i)))
        (bddAbove_of_abs_le (C := N * (2 * B)) fun t => abs_sum_le_card_mul fun i =>
          hsub2 t i _ _) t
  have hB1 : ∫ w, ⨆ t, sumDev μ g w t ∂Pn ≤ ∫ z, W z ∂(Pn.prod Pn) := by
    rw [integral_prod W hWint]
    refine integral_mono ?_ hWint.integral_prod_left hA
    exact Integrable.of_bound (Measurable.iSup fun t =>
      measurable_sumDev μ hg t).aestronglyMeasurable (N * (2 * B))
      (ae_of_all _ fun w => abs_ciSup_le fun t => abs_sumDev_le μ hB w t)
  -- Step C: move to the pair-sample measure
  set Q : Measure (ι → X × X) := Measure.pi fun i => (μ i).prod (μ i) with hQ
  have he := measurePreserving_arrowProdEquivProdArrow X X ι μ μ
  set V : (ι → X × X) → ℝ :=
    fun z => ⨆ t, ∑ i, (g t i (z i).1 - g t i (z i).2) with hV
  have hC : ∫ z, W z ∂(Pn.prod Pn) = ∫ z, V z ∂Q := (he.integral_comp' W).symm
  -- Step D: swap invariance inserts signs
  set Vσ : (ι → Bool) → (ι → X × X) → ℝ :=
    fun σ z => ⨆ t, ∑ i, rsign (σ i) * (g t i (z i).1 - g t i (z i).2) with hVσ
  have hgz1 : ∀ t i, Measurable fun z : ι → X × X => g t i (z i).1 := fun t i =>
    (hg t i).comp (measurable_fst.comp (measurable_pi_apply i))
  have hgz2 : ∀ t i, Measurable fun z : ι → X × X => g t i (z i).2 := fun t i =>
    (hg t i).comp (measurable_snd.comp (measurable_pi_apply i))
  have hVσm : ∀ σ, Measurable (Vσ σ) := fun σ => Measurable.iSup fun t =>
    Finset.measurable_fun_sum _ fun i _ => ((hgz1 t i).sub (hgz2 t i)).const_mul _
  have hVσb : ∀ σ z, |Vσ σ z| ≤ N * (2 * B) := fun σ z => abs_ciSup_le fun t =>
    abs_sum_le_card_mul fun i => by
      rw [abs_mul, abs_rsign, one_mul]
      exact hsub2 t i _ _
  have hVm : Measurable V := Measurable.iSup fun t =>
    Finset.measurable_fun_sum _ fun i _ => (hgz1 t i).sub (hgz2 t i)
  have hD : ∀ σ : ι → Bool, ∫ z, V z ∂Q = ∫ z, Vσ σ z ∂Q := by
    intro σ
    let f : ι → X × X → X × X := fun i => if σ i then id else Prod.swap
    have hfm : ∀ i, Measurable (f i) := fun i => by
      by_cases h : σ i
      · simp only [f, h, ite_true]; exact measurable_id
      · simp only [f, h]; exact measurable_swap
    have hmap : ∀ i, ((μ i).prod (μ i)).map (f i) = (μ i).prod (μ i) := fun i => by
      by_cases h : σ i
      · simp only [f, h, ite_true, Measure.map_id]
      · simp only [f, h]; exact Measure.prod_swap
    have : ∀ i, SigmaFinite (((μ i).prod (μ i)).map (f i)) := fun i => by
      rw [hmap i]; infer_instance
    have hpi : Q.map (fun z i => f i (z i)) = Q := by
      rw [hQ, Measure.pi_map_pi fun i => (hfm i).aemeasurable]
      simp_rw [hmap]
    have hswm : Measurable fun z : ι → X × X => fun i => f i (z i) :=
      measurable_pi_iff.2 fun i => (hfm i).comp (measurable_pi_apply i)
    have hint := integral_map (μ := Q) hswm.aemeasurable
      (f := V) (by rw [hpi]; exact hVm.aestronglyMeasurable)
    rw [hpi] at hint
    rw [hint]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hV, hVσ]
    congr 1
    funext t
    refine sum_congr rfl fun i _ => ?_
    by_cases h : σ i
    · simp [f, h]
    · simp [f, h]
  -- Step E: average over σ and split the supremum
  have hE : ∫ z, V z ∂Q = ∫ z, signE (fun σ => Vσ σ z) ∂Q := by
    have h1 : ∫ z, V z ∂Q = signE (fun σ => ∫ z, Vσ σ z ∂Q) := by
      rw [← signE_const (ι := ι) (∫ z, V z ∂Q)]
      congr 1; funext σ; exact hD σ
    rw [h1]
    unfold signE
    rw [integral_const_mul, integral_finsetSum _ fun σ _ => Integrable.of_bound
      (hVσm σ).aestronglyMeasurable (N * (2 * B)) (ae_of_all _ fun z => hVσb σ z)]
  set R : (ι → Bool) → (ι → X) → ℝ :=
    fun σ w => ⨆ t, ∑ i, rsign (σ i) * g t i (w i) with hR
  have hRb : ∀ (σ : ι → Bool) (w : ι → X) t, |∑ i, rsign (σ i) * g t i (w i)| ≤ N * B :=
    fun σ w t => abs_sum_le_card_mul fun i => by rw [abs_mul, abs_rsign, one_mul]; exact hB _ _ _
  have hsplit : ∀ z : ι → X × X, signE (fun σ => Vσ σ z) ≤
      radAvgι g (fun i => (z i).1) + radAvgι g (fun i => (z i).2) := by
    intro z
    have hpt : ∀ σ, Vσ σ z ≤ R σ (fun i => (z i).1) + R (negSignsι σ) (fun i => (z i).2) := by
      intro σ
      have heq : ∀ t, ∑ i, rsign (σ i) * (g t i (z i).1 - g t i (z i).2) =
          ∑ i, rsign (σ i) * g t i (z i).1 + ∑ i, rsign (negSignsι σ i) * g t i (z i).2 := by
        intro t
        simp only [negSignsι, rsign_not, ← sum_add_distrib]
        refine sum_congr rfl fun i _ => ?_; ring
      simp only [hVσ, hR]
      simp_rw [heq]
      exact ciSup_add_le (bddAbove_of_abs_le fun t => hRb σ _ t)
        (bddAbove_of_abs_le fun t => hRb (negSignsι σ) _ t)
    calc signE (fun σ => Vσ σ z)
        ≤ signE (fun σ => R σ (fun i => (z i).1) + R (negSignsι σ) (fun i => (z i).2)) :=
          signE_mono hpt
      _ = radAvgι g (fun i => (z i).1) + radAvgι g (fun i => (z i).2) := by
          rw [signE_add, signE_negSigns (fun σ => R σ fun i => (z i).2)]
          rfl
  -- Step F: marginals
  have hRm := measurable_radAvgι (g := g) hg
  have hF1 : ∫ z, radAvgι g (fun i => (z i).1) ∂Q = ∫ w, radAvgι g w ∂Pn := by
    have := he.integral_comp' (fun p => radAvgι g p.1)
    rw [integral_fun_fst, probReal_univ, one_smul] at this
    exact this
  have hF2 : ∫ z, radAvgι g (fun i => (z i).2) ∂Q = ∫ w, radAvgι g w ∂Pn := by
    have := he.integral_comp' (fun p => radAvgι g p.2)
    rw [integral_fun_snd, probReal_univ, one_smul] at this
    exact this
  have hint1 : Integrable (fun z : ι → X × X => radAvgι g (fun i => (z i).1)) Q :=
    Integrable.of_bound (hRm.comp (measurable_pi_iff.2 fun i =>
      measurable_fst.comp (measurable_pi_apply i))).aestronglyMeasurable (N * B)
      (ae_of_all _ fun z => abs_radAvgι_le hB _)
  have hint2 : Integrable (fun z : ι → X × X => radAvgι g (fun i => (z i).2)) Q :=
    Integrable.of_bound (hRm.comp (measurable_pi_iff.2 fun i =>
      measurable_snd.comp (measurable_pi_apply i))).aestronglyMeasurable (N * B)
      (ae_of_all _ fun z => abs_radAvgι_le hB _)
  have hradm : Measurable fun z => signE (fun σ => Vσ σ z) := by
    unfold signE
    exact Measurable.const_mul (Finset.measurable_fun_sum _ fun σ _ => hVσm σ) _
  have hfinal : ∫ z, signE (fun σ => Vσ σ z) ∂Q ≤
      ∫ w, radAvgι g w ∂Pn + ∫ w, radAvgι g w ∂Pn := by
    have h := integral_mono
      (g := fun z => radAvgι g (fun i => (z i).1) + radAvgι g (fun i => (z i).2))
      (Integrable.of_bound hradm.aestronglyMeasurable (N * (2 * B))
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact abs_signE_le fun σ => hVσb σ z))
      (hint1.add hint2) hsplit
    rw [integral_add hint1 hint2, hF1, hF2] at h
    exact h
  calc ∫ w, ⨆ t, sumDev μ g w t ∂Pn ≤ ∫ z, W z ∂(Pn.prod Pn) := hB1
    _ = ∫ z, signE (fun σ => Vσ σ z) ∂Q := by rw [hC, hE]
    _ ≤ ∫ w, radAvgι g w ∂Pn + ∫ w, radAvgι g w ∂Pn := hfinal
    _ = 2 * ∫ w, radAvgι g w ∂Pn := by ring

/-! ### Two independent samples, one joint supremum -/

/-- `E_{σ,σ'} sup_t [n⁻¹ ∑_i σ_i g₁_t(x_i) + m⁻¹ ∑_j σ'_j g₂_t(y_j)]`, with one sign vector on `Fin n ⊕ Fin m`. -/
def radAvg2 {T : Type*} (g₁ g₂ : T → X → ℝ) (n m : ℕ) (z : (Fin n → X) × (Fin m → X)) : ℝ :=
  signE (ι := Fin n ⊕ Fin m) (fun σ => ⨆ t, ((n : ℝ)⁻¹ * ∑ i, rsign (σ (Sum.inl i)) * g₁ t (z.1 i) +
    (m : ℝ)⁻¹ * ∑ j, rsign (σ (Sum.inr j)) * g₂ t (z.2 j)))

omit [Countable T] [Nonempty T] in
theorem measurable_radAvg2 [Countable T] {g₁ g₂ : T → X → ℝ} (hg₁ : ∀ t, Measurable (g₁ t))
    (hg₂ : ∀ t, Measurable (g₂ t)) (n m : ℕ) : Measurable (radAvg2 g₁ g₂ n m) := by
  unfold radAvg2 signE
  refine Measurable.const_mul (Finset.measurable_fun_sum _ fun σ _ => ?_) _
  refine Measurable.iSup fun t => ?_
  refine (Measurable.const_mul (Finset.measurable_fun_sum _ fun i _ => ?_) _).add
    (Measurable.const_mul (Finset.measurable_fun_sum _ fun j _ => ?_) _)
  · exact ((hg₁ t).comp ((measurable_pi_apply i).comp measurable_fst)).const_mul _
  · exact ((hg₂ t).comp ((measurable_pi_apply j).comp measurable_snd)).const_mul _

/-- **Two-sample symmetrisation for a joint (signed) supremum.** Under `P^{⊗n} ⊗ Q^{⊗m}`,
`E sup_t [(P_n − P) g₁_t + (Q_m − Q) g₂_t] ≤ 2 E_{X,Y,σ} sup_t [n⁻¹ ∑ σ_i g₁_t(X_i) + m⁻¹ ∑ σ'_j g₂_t(Y_j)]`. -/
theorem integral_iSup_empDev2_le (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {g₁ g₂ : T → X → ℝ} (hg₁ : ∀ t, Measurable (g₁ t)) (hg₂ : ∀ t, Measurable (g₂ t))
    (hB₁ : ∀ t y, |g₁ t y| ≤ B) (hB₂ : ∀ t y, |g₂ t y| ≤ B) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    ∫ z, ⨆ t, (empDev P g₁ n z.1 t + empDev Q g₂ m z.2 t)
        ∂((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) ≤
      2 * ∫ z, radAvg2 g₁ g₂ n m z
        ∂((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) := by
  obtain ⟨y₀⟩ := nonempty_of_isProbabilityMeasure P
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB₁ (Classical.arbitrary T) y₀)
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hninv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)
  have hminv : (m : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm)
  set μ : Fin n ⊕ Fin m → Measure X := Sum.elim (fun _ => P) (fun _ => Q) with hμ
  have : ∀ k, IsProbabilityMeasure (μ k) := fun k => by
    cases k <;> simp only [hμ, Sum.elim_inl, Sum.elim_inr] <;> infer_instance
  set G : T → Fin n ⊕ Fin m → X → ℝ := fun t k =>
    Sum.elim (fun _ y => (n : ℝ)⁻¹ * g₁ t y) (fun _ y => (m : ℝ)⁻¹ * g₂ t y) k with hG
  have hGm : ∀ t k, Measurable (G t k) := fun t k => by
    cases k
    · exact (hg₁ t).const_mul _
    · exact (hg₂ t).const_mul _
  have hGB : ∀ t k y, |G t k y| ≤ B := fun t k y => by
    cases k
    · simp only [hG, Sum.elim_inl]
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ)⁻¹)]
      calc (n : ℝ)⁻¹ * |g₁ t y| ≤ 1 * B := mul_le_mul hninv (hB₁ t y) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    · simp only [hG, Sum.elim_inr]
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ)⁻¹)]
      calc (m : ℝ)⁻¹ * |g₂ t y| ≤ 1 * B := mul_le_mul hminv (hB₂ t y) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
  have hsym := integral_iSup_sumDev_le μ hGm hGB
  have hmp := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin m => X) μ
  have hlaw : (Measure.pi fun i => μ (Sum.inl i)).prod (Measure.pi fun i => μ (Sum.inr i)) =
      (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) := rfl
  rw [hlaw] at hmp
  -- identify the two sides
  have hL : ∀ w : Fin n ⊕ Fin m → X,
      (⨆ t, (empDev P g₁ n (fun i => w (Sum.inl i)) t + empDev Q g₂ m (fun j => w (Sum.inr j)) t)) =
        ⨆ t, sumDev μ G w t := by
    intro w
    congr 1; funext t
    simp only [sumDev, Fintype.sum_sum_type, hG, hμ, Sum.elim_inl, Sum.elim_inr, empDev,
      integral_const_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    field_simp
    ring
  have hR : ∀ w : Fin n ⊕ Fin m → X,
      radAvg2 g₁ g₂ n m ((fun i => w (Sum.inl i)), (fun j => w (Sum.inr j))) = radAvgι G w := by
    intro w
    unfold radAvg2 radAvgι
    congr 1; funext σ; congr 1; funext t
    simp only [Fintype.sum_sum_type, hG, Sum.elim_inl, Sum.elim_inr, Finset.mul_sum]
    congr 1 <;> refine sum_congr rfl fun i _ => ?_ <;> ring
  have h1 := hmp.integral_comp' (fun z => ⨆ t, (empDev P g₁ n z.1 t + empDev Q g₂ m z.2 t))
  have h2 := hmp.integral_comp' (radAvg2 g₁ g₂ n m)
  rw [← h1, ← h2]
  calc _ = ∫ w, ⨆ t, sumDev μ G w t ∂(Measure.pi μ) :=
        integral_congr_ae (ae_of_all _ fun w => hL w)
    _ ≤ 2 * ∫ w, radAvgι G w ∂(Measure.pi μ) := hsym
    _ = _ := by
        congr 1
        exact integral_congr_ae (ae_of_all _ fun w => (hR w).symm)

end StatFormal.Concentration
