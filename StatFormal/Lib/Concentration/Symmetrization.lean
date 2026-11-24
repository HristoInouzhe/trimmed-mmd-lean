import StatFormal.Lib.Concentration.EmpiricalProcess
import StatFormal.Lib.Concentration.HilbertMean
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Symmetrisation of empirical processes

Library component (concentration, part 5). Untrusted library code.

Setting: device (a) of `EmpiricalProcess.lean` — a countable nonempty index type `T`, measurable
`g t : X → ℝ` with `|g t x| ≤ B`, sample `x ~ Pⁿ = Measure.pi (fun _ : Fin n => P)`, `n ≠ 0`.
The Rademacher signs are averaged exactly (`radE`, uniform on `{±1}ⁿ`, independent of `x` by
construction: `E_{X,σ} F = ∫ x, radE (fun σ => F x σ) dPⁿ`).

`radAvg P g n x = E_σ sup_t n⁻¹ ∑ σᵢ g t (xᵢ)` (signed Rademacher average at the sample `x`).

## Proof route

Ghost sample `x'`: `(Pₙ − P)g_t = E_{x'}[n⁻¹ ∑ (g_t(xᵢ) − g_t(x'ᵢ))]`, so
`sup_t (Pₙ − P) g_t ≤ E_{x'} sup_t (…)` (Fubini, `integral_prod`). The pair sample is moved to
`Measure.pi (fun _ => P.prod P)` by `measurePreserving_arrowProdEquivProdArrow`; there, swapping
`(xᵢ, x'ᵢ)` on the coordinates with `σᵢ = −1` preserves the law (`Measure.pi_map_pi`,
`Measure.prod_swap`), which inserts the signs; finally `sup(a + b) ≤ sup a + sup b` and
`σ ↦ −σ` invariance.

## Main results

* `integral_iSup_empDev_le` (one-sided): `E sup_t (Pₙ − P) g_t ≤ 2 E_{X,σ} sup_t n⁻¹ ∑ σᵢ g_t(Xᵢ)`;
* `integral_iSup_abs_empDev_le` (two-sided):
  `E sup_t |(Pₙ − P) g_t| ≤ 2 E_{X,σ} sup_t |n⁻¹ ∑ σᵢ g_t(Xᵢ)|`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

namespace StatFormal.Concentration

variable {X : Type*} [MeasurableSpace X]

/-- Signed Rademacher average of the class at the sample `x`. -/
def radAvg {T : Type*} (g : T → X → ℝ) (n : ℕ) (x : Fin n → X) : ℝ :=
  radE (fun σ => ⨆ t, (n : ℝ)⁻¹ * ∑ i, rsign (σ i) * g t (x i))

theorem abs_mean_le {n : ℕ} (hn : n ≠ 0) {c : Fin n → ℝ} {C : ℝ} (h : ∀ i, |c i| ≤ C) :
    |(n : ℝ)⁻¹ * ∑ i, c i| ≤ C := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  rw [abs_mul, abs_inv, Nat.abs_cast]
  calc (n : ℝ)⁻¹ * |∑ i, c i| ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, C := by
        gcongr; exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => h i)
    _ = C := by simp [Finset.sum_const]; field_simp

theorem abs_ciSup_le {T : Type*} [Nonempty T] {f : T → ℝ} {C : ℝ} (h : ∀ t, |f t| ≤ C) :
    |⨆ t, f t| ≤ C := by
  obtain ⟨t₀⟩ := ‹Nonempty T›
  rw [abs_le]
  constructor
  · have := le_ciSup (bddAbove_of_abs_le h) t₀
    have := (abs_le.1 (h t₀)).1
    linarith
  · exact ciSup_le fun t => (le_abs_self _).trans (h t)

theorem ciSup_add_le {T : Type*} [Nonempty T] {a b : T → ℝ} (ha : BddAbove (Set.range a))
    (hb : BddAbove (Set.range b)) : (⨆ t, (a t + b t)) ≤ (⨆ t, a t) + ⨆ t, b t :=
  ciSup_le fun t => add_le_add (le_ciSup ha t) (le_ciSup hb t)

theorem abs_radE_le {n : ℕ} {F : (Fin n → Bool) → ℝ} {C : ℝ} (h : ∀ σ, |F σ| ≤ C) :
    |radE F| ≤ C := by
  unfold radE
  rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]
  calc ((2 : ℝ) ^ n)⁻¹ * |∑ σ, F σ| ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ _σ : Fin n → Bool, C := by
        gcongr; exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun σ _ => h σ)
    _ = C := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_signs]; field_simp

variable (P : Measure X) [IsProbabilityMeasure P] {T : Type*} [Countable T] [Nonempty T]
  {g : T → X → ℝ} {B : ℝ}

omit [IsProbabilityMeasure P] in
theorem measurable_radAvg (hg : ∀ t, Measurable (g t)) (n : ℕ) :
    Measurable (radAvg g n) := by
  have h : ∀ σ : Fin n → Bool, Measurable fun x : Fin n → X =>
      ⨆ t, (n : ℝ)⁻¹ * ∑ i, rsign (σ i) * g t (x i) := fun σ =>
    Measurable.iSup fun t => Measurable.const_mul (Finset.measurable_fun_sum _ fun i _ =>
      ((hg t).comp (measurable_pi_apply i)).const_mul _) _
  have h2 : Measurable fun x : Fin n → X =>
      ∑ σ : Fin n → Bool, ⨆ t, (n : ℝ)⁻¹ * ∑ i, rsign (σ i) * g t (x i) :=
    Finset.measurable_fun_sum _ fun σ _ => h σ
  exact h2.const_mul ((2 : ℝ) ^ n)⁻¹

omit [Countable T] [Nonempty T] in
theorem abs_rsign_mul_le (hB : ∀ t y, |g t y| ≤ B) (b : Bool) (t : T) (y : X) :
    |rsign b * g t y| ≤ B := by
  rw [abs_mul, abs_rsign, one_mul]; exact hB t y

omit [Countable T] [Nonempty T] in
theorem abs_sub_le_two (hB : ∀ t y, |g t y| ≤ B) (t : T) (a b : X) :
    |g t a - g t b| ≤ 2 * B :=
  (abs_sub _ _).trans (by linarith [hB t a, hB t b])

theorem abs_radAvg_le (hB : ∀ t y, |g t y| ≤ B) {n : ℕ} (hn : n ≠ 0) (x : Fin n → X) :
    |radAvg g n x| ≤ B :=
  abs_radE_le fun σ => abs_ciSup_le fun t => abs_mean_le hn fun i => by
    rw [abs_mul, abs_rsign, one_mul]; exact hB _ _

theorem integral_mean_comp (hg : ∀ t, Measurable (g t)) (hB : ∀ t y, |g t y| ≤ B) {n : ℕ}
    (hn : n ≠ 0) (t : T) :
    ∫ x', (n : ℝ)⁻¹ * ∑ i, g t (x' i) ∂(Measure.pi fun _ : Fin n => P) = ∫ y, g t y ∂P := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [integral_const_mul, integral_finsetSum _ fun i _ =>
    Integrable.of_bound (f := fun x : Fin n → X => g t (x i))
      ((hg t).comp (measurable_pi_apply i)).aestronglyMeasurable B
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hB t _)]
  simp_rw [integral_comp_eval (P := P) _ (hg t).aestronglyMeasurable]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Symmetrisation (one-sided).** -/
theorem integral_iSup_empDev_le (hg : ∀ t, Measurable (g t)) (hB : ∀ t y, |g t y| ≤ B)
    {n : ℕ} (hn : n ≠ 0) :
    ∫ x, ⨆ t, empDev P g n x t ∂(Measure.pi fun _ : Fin n => P) ≤
      2 * ∫ x, radAvg g n x ∂(Measure.pi fun _ : Fin n => P) := by
  set Pn := Measure.pi fun _ : Fin n => P with hPn
  have hgi : ∀ t i, Measurable fun x : Fin n → X => g t (x i) := fun t i =>
    (hg t).comp (measurable_pi_apply i)
  -- the ghost-sample supremum on the product
  set W : (Fin n → X) × (Fin n → X) → ℝ :=
    fun z => ⨆ t, (n : ℝ)⁻¹ * ∑ i, (g t (z.1 i) - g t (z.2 i)) with hW
  have hWb : ∀ z, |W z| ≤ 2 * B := fun z => abs_ciSup_le fun t => abs_mean_le hn fun i =>
    abs_sub_le_two hB t _ _
  have hWm : Measurable W := Measurable.iSup fun t => Measurable.const_mul
    (Finset.measurable_fun_sum _ fun i _ =>
      ((hgi t i).comp measurable_fst).sub ((hgi t i).comp measurable_snd)) _
  have hWint : Integrable W (Pn.prod Pn) :=
    Integrable.of_bound hWm.aestronglyMeasurable (2 * B) (ae_of_all _ fun z => hWb z)
  -- Step A/B: Jensen for the supremum and Fubini
  have hA : ∀ x, ⨆ t, empDev P g n x t ≤ ∫ x', W (x, x') ∂Pn := by
    intro x
    refine ciSup_le fun t => ?_
    have hrep : empDev P g n x t =
        ∫ x', (n : ℝ)⁻¹ * ∑ i, (g t (x i) - g t (x' i)) ∂Pn := by
      simp_rw [Finset.sum_sub_distrib, mul_sub]
      rw [integral_sub (integrable_const _), integral_const, probReal_univ, one_smul,
        integral_mean_comp P hg hB hn t]
      · rfl
      · exact Integrable.of_bound ((Finset.measurable_fun_sum _ fun i _ =>
          hgi t i).const_mul _).aestronglyMeasurable B
          (ae_of_all _ fun x' => abs_mean_le hn fun i => hB t _)
    rw [hrep]
    refine integral_mono ?_ ?_ fun x' => ?_
    · exact Integrable.of_bound ((Finset.measurable_fun_sum _ fun i _ =>
        measurable_const.sub (hgi t i)).const_mul _).aestronglyMeasurable (2 * B)
        (ae_of_all _ fun x' => abs_mean_le hn fun i => abs_sub_le_two hB t _ _)
    · exact Integrable.of_bound (hWm.comp (measurable_prodMk_left)).aestronglyMeasurable
        (2 * B) (ae_of_all _ fun x' => hWb _)
    · exact le_ciSup (f := fun t => (n : ℝ)⁻¹ * ∑ i, (g t (x i) - g t (x' i)))
        (bddAbove_of_abs_le (C := 2 * B) fun t => abs_mean_le hn fun i =>
          abs_sub_le_two hB t _ _) t
  have hB1 : ∫ x, ⨆ t, empDev P g n x t ∂Pn ≤ ∫ z, W z ∂(Pn.prod Pn) := by
    rw [integral_prod W hWint]
    refine integral_mono ?_ hWint.integral_prod_left hA
    exact Integrable.of_bound (Measurable.iSup fun t =>
      measurable_empDev P hg n t).aestronglyMeasurable (2 * B)
      (ae_of_all _ fun x => abs_ciSup_le fun t => abs_empDev_le P hB x t)
  -- Step C: move to the pair-sample measure
  set Q : Measure (Fin n → X × X) := Measure.pi fun _ : Fin n => P.prod P with hQ
  have he := measurePreserving_arrowProdEquivProdArrow X X (Fin n) (fun _ => P) (fun _ => P)
  set V : (Fin n → X × X) → ℝ :=
    fun z => ⨆ t, (n : ℝ)⁻¹ * ∑ i, (g t (z i).1 - g t (z i).2) with hV
  have hC : ∫ z, W z ∂(Pn.prod Pn) = ∫ z, V z ∂Q := (he.integral_comp' W).symm
  -- Step D: swap invariance inserts signs
  set Vσ : (Fin n → Bool) → (Fin n → X × X) → ℝ :=
    fun σ z => ⨆ t, (n : ℝ)⁻¹ * ∑ i, rsign (σ i) * (g t (z i).1 - g t (z i).2) with hVσ
  have hgz1 : ∀ t i, Measurable fun z : Fin n → X × X => g t (z i).1 := fun t i =>
    (hg t).comp (measurable_fst.comp (measurable_pi_apply i))
  have hgz2 : ∀ t i, Measurable fun z : Fin n → X × X => g t (z i).2 := fun t i =>
    (hg t).comp (measurable_snd.comp (measurable_pi_apply i))
  have hVσm : ∀ σ, Measurable (Vσ σ) := fun σ => Measurable.iSup fun t =>
    Measurable.const_mul (Finset.measurable_fun_sum _ fun i _ =>
      ((hgz1 t i).sub (hgz2 t i)).const_mul _) _
  have hVσb : ∀ σ z, |Vσ σ z| ≤ 2 * B := fun σ z => abs_ciSup_le fun t =>
    abs_mean_le hn fun i => by
      rw [abs_mul, abs_rsign, one_mul]
      exact abs_sub_le_two hB t _ _
  have hVm : Measurable V := Measurable.iSup fun t => Measurable.const_mul
    (Finset.measurable_fun_sum _ fun i _ => (hgz1 t i).sub (hgz2 t i)) _
  have hD : ∀ σ : Fin n → Bool, ∫ z, V z ∂Q = ∫ z, Vσ σ z ∂Q := by
    intro σ
    let f : Fin n → X × X → X × X := fun i => if σ i then id else Prod.swap
    have hfm : ∀ i, Measurable (f i) := fun i => by
      by_cases h : σ i
      · simp only [f, h, if_true]; exact measurable_id
      · simp only [f, h]; exact measurable_swap
    have hmap : ∀ i, (P.prod P).map (f i) = P.prod P := fun i => by
      by_cases h : σ i
      · simp only [f, h, if_true, Measure.map_id]
      · simp only [f, h]; exact Measure.prod_swap
    haveI : ∀ i, SigmaFinite ((P.prod P).map (f i)) := fun i => by rw [hmap i]; infer_instance
    have hpi : Q.map (fun z i => f i (z i)) = Q := by
      rw [hQ, Measure.pi_map_pi fun i => (hfm i).aemeasurable]
      simp_rw [hmap]
    have hswm : Measurable fun z : Fin n → X × X => fun i => f i (z i) :=
      measurable_pi_iff.2 fun i => (hfm i).comp (measurable_pi_apply i)
    have hint := integral_map (μ := Q) hswm.aemeasurable
      (f := V) (by rw [hpi]; exact hVm.aestronglyMeasurable)
    rw [hpi] at hint
    rw [hint]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hV, hVσ]
    congr 1
    funext t
    congr 1
    refine sum_congr rfl fun i _ => ?_
    by_cases h : σ i
    · simp [f, h]
    · simp [f, h]
  -- Step E: average over σ and split the supremum
  have hE : ∫ z, V z ∂Q = ∫ z, radE (fun σ => Vσ σ z) ∂Q := by
    have h1 : ∫ z, V z ∂Q = radE (fun σ => ∫ z, Vσ σ z ∂Q) := by
      rw [← radE_const (n := n) (∫ z, V z ∂Q)]
      congr 1; funext σ; exact hD σ
    rw [h1]
    unfold radE
    rw [integral_const_mul, integral_finsetSum _ fun σ _ => Integrable.of_bound
      (hVσm σ).aestronglyMeasurable (2 * B) (ae_of_all _ fun z => hVσb σ z)]
  set R : (Fin n → Bool) → (Fin n → X) → ℝ :=
    fun σ x => ⨆ t, (n : ℝ)⁻¹ * ∑ i, rsign (σ i) * g t (x i) with hR
  have hRb : ∀ (σ : Fin n → Bool) (x : Fin n → X) t, |(n : ℝ)⁻¹ * ∑ i, rsign (σ i) * g t (x i)| ≤ B :=
    fun σ x t => abs_mean_le hn fun i => by rw [abs_mul, abs_rsign, one_mul]; exact hB _ _
  have hsplit : ∀ z : Fin n → X × X, radE (fun σ => Vσ σ z) ≤
      radAvg g n (fun i => (z i).1) + radAvg g n (fun i => (z i).2) := by
    intro z
    have hpt : ∀ σ, Vσ σ z ≤ R σ (fun i => (z i).1) + R (negSigns σ) (fun i => (z i).2) := by
      intro σ
      have heq : ∀ t, (n : ℝ)⁻¹ * ∑ i, rsign (σ i) * (g t (z i).1 - g t (z i).2) =
          (n : ℝ)⁻¹ * ∑ i, rsign (σ i) * g t (z i).1 +
            (n : ℝ)⁻¹ * ∑ i, rsign (negSigns σ i) * g t (z i).2 := by
        intro t
        simp only [negSigns, rsign_not, ← mul_add, ← sum_add_distrib]
        congr 1; refine sum_congr rfl fun i _ => ?_; ring
      simp only [hVσ, hR]
      simp_rw [heq]
      exact ciSup_add_le (bddAbove_of_abs_le fun t => hRb σ _ t)
        (bddAbove_of_abs_le fun t => hRb (negSigns σ) _ t)
    calc radE (fun σ => Vσ σ z)
        ≤ radE (fun σ => R σ (fun i => (z i).1) + R (negSigns σ) (fun i => (z i).2)) :=
          radE_mono hpt
      _ = radAvg g n (fun i => (z i).1) + radAvg g n (fun i => (z i).2) := by
          rw [radE_add, radE_negSigns (fun σ => R σ fun i => (z i).2)]
          rfl
  -- Step F: marginals
  have hRm := measurable_radAvg (g := g) hg n
  have hRint : Integrable (radAvg g n) Pn :=
    Integrable.of_bound hRm.aestronglyMeasurable B (ae_of_all _ fun x => abs_radAvg_le hB hn x)
  have hF1 : ∫ z, radAvg g n (fun i => (z i).1) ∂Q = ∫ x, radAvg g n x ∂Pn := by
    have := he.integral_comp' (fun p => radAvg g n p.1)
    rw [integral_fun_fst, probReal_univ, one_smul] at this
    exact this
  have hF2 : ∫ z, radAvg g n (fun i => (z i).2) ∂Q = ∫ x, radAvg g n x ∂Pn := by
    have := he.integral_comp' (fun p => radAvg g n p.2)
    rw [integral_fun_snd, probReal_univ, one_smul] at this
    exact this
  have hint1 : Integrable (fun z : Fin n → X × X => radAvg g n (fun i => (z i).1)) Q :=
    Integrable.of_bound (hRm.comp (measurable_pi_iff.2 fun i =>
      measurable_fst.comp (measurable_pi_apply i))).aestronglyMeasurable B
      (ae_of_all _ fun z => abs_radAvg_le hB hn _)
  have hint2 : Integrable (fun z : Fin n → X × X => radAvg g n (fun i => (z i).2)) Q :=
    Integrable.of_bound (hRm.comp (measurable_pi_iff.2 fun i =>
      measurable_snd.comp (measurable_pi_apply i))).aestronglyMeasurable B
      (ae_of_all _ fun z => abs_radAvg_le hB hn _)
  have hradm : Measurable fun z => radE (fun σ => Vσ σ z) := by
    unfold radE
    exact Measurable.const_mul (Finset.measurable_fun_sum _ fun σ _ => hVσm σ) _
  have hfinal : ∫ z, radE (fun σ => Vσ σ z) ∂Q ≤
      ∫ x, radAvg g n x ∂Pn + ∫ x, radAvg g n x ∂Pn := by
    have h := integral_mono
      (g := fun z => radAvg g n (fun i => (z i).1) + radAvg g n (fun i => (z i).2))
      (Integrable.of_bound hradm.aestronglyMeasurable (2 * B)
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact abs_radE_le fun σ => hVσb σ z))
      (hint1.add hint2) hsplit
    rw [integral_add hint1 hint2, hF1, hF2] at h
    exact h
  calc ∫ x, ⨆ t, empDev P g n x t ∂Pn ≤ ∫ z, W z ∂(Pn.prod Pn) := hB1
    _ = ∫ z, radE (fun σ => Vσ σ z) ∂Q := by rw [hC, hE]
    _ ≤ ∫ x, radAvg g n x ∂Pn + ∫ x, radAvg g n x ∂Pn := hfinal
    _ = 2 * ∫ x, radAvg g n x ∂Pn := by ring

/-- `sup` over `T × Bool` of `±a` is `sup |a|`. -/
theorem iSup_rsign_mul_eq {a : T → ℝ} {C : ℝ} (ha : ∀ t, |a t| ≤ C) :
    (⨆ p : T × Bool, rsign p.2 * a p.1) = ⨆ t, |a t| := by
  have hb1 : BddAbove (Set.range fun p : T × Bool => rsign p.2 * a p.1) :=
    bddAbove_of_abs_le fun p => by rw [abs_mul, abs_rsign, one_mul]; exact ha _
  have hb2 : BddAbove (Set.range fun t => |a t|) :=
    bddAbove_of_abs_le fun t => by rw [abs_abs]; exact ha t
  refine le_antisymm (ciSup_le fun p => ?_) (ciSup_le fun t => ?_)
  · refine le_trans ?_ (le_ciSup hb2 p.1)
    rcases p with ⟨t, b⟩
    cases b
    · simp [neg_le_abs]
    · simp [le_abs_self]
  · rcases le_total 0 (a t) with h | h
    · rw [abs_of_nonneg h]
      exact le_trans (by simp) (le_ciSup hb1 (t, true))
    · rw [abs_of_nonpos h]
      exact le_trans (by simp) (le_ciSup hb1 (t, false))

/-- **Symmetrisation (two-sided)**:
`E sup_t |(Pₙ − P) g_t| ≤ 2 E_{X,σ} sup_t |n⁻¹ ∑ σᵢ g_t(Xᵢ)|`. -/
theorem integral_iSup_abs_empDev_le (hg : ∀ t, Measurable (g t)) (hB : ∀ t y, |g t y| ≤ B)
    {n : ℕ} (hn : n ≠ 0) :
    ∫ x, ⨆ t, |empDev P g n x t| ∂(Measure.pi fun _ : Fin n => P) ≤
      2 * ∫ x, radE (fun σ => ⨆ t, |(n : ℝ)⁻¹ * ∑ i, rsign (σ i) * g t (x i)|)
        ∂(Measure.pi fun _ : Fin n => P) := by
  set g' : T × Bool → X → ℝ := fun p y => rsign p.2 * g p.1 y
  have hg' : ∀ p, Measurable (g' p) := fun p => (hg p.1).const_mul _
  have hB' : ∀ p y, |g' p y| ≤ B := fun p y => by
    simp only [g']; rw [abs_mul, abs_rsign, one_mul]; exact hB _ _
  have h := integral_iSup_empDev_le P hg' hB' hn
  have hl : ∀ x : Fin n → X, (⨆ p, empDev P g' n x p) = ⨆ t, |empDev P g n x t| := by
    intro x
    have : ∀ p : T × Bool, empDev P g' n x p = rsign p.2 * empDev P g n x p.1 := by
      intro p
      simp only [empDev, g', integral_const_mul, ← mul_sum]
      ring
    simp_rw [this]
    exact iSup_rsign_mul_eq fun t => abs_empDev_le P hB x t
  have hr : ∀ x : Fin n → X, radAvg g' n x =
      radE (fun σ => ⨆ t, |(n : ℝ)⁻¹ * ∑ i, rsign (σ i) * g t (x i)|) := by
    intro x
    unfold radAvg
    congr 1; funext σ
    have : ∀ p : T × Bool, (n : ℝ)⁻¹ * ∑ i, rsign (σ i) * g' p (x i) =
        rsign p.2 * ((n : ℝ)⁻¹ * ∑ i, rsign (σ i) * g p.1 (x i)) := by
      intro p
      simp only [g', Finset.mul_sum]
      exact sum_congr rfl fun i _ => by ring
    simp_rw [this]
    exact iSup_rsign_mul_eq (T := T) (C := B) fun t => abs_mean_le hn fun i =>
      abs_rsign_mul_le hB (σ i) t (x i)
  simp_rw [hl, hr] at h
  exact h

end StatFormal.Concentration
