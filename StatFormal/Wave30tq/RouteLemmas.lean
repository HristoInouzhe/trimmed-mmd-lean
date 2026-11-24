import StatFormal.Wave30tq.Statements
import StatFormal.Archive.Wave8a.RouteCvar
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Wave 30tq route: Lemma 1 (one cut point is enough) and Lemma 2 (clipping) — untrusted

* `psi_le_trim`, `trim_le_upper`: the two halves of the proof of Lemma 1 (`γ(f − s) ≥ −β(s − f)₊`, and
  symmetrically); `lem1_trim_route`, `lem1_route`;
* `lem1_null_route`: through the certified `TrimmedMMD.ZeroSet.tvintersect` (`eq:tvintersect`);
* `psi_le_psi_quantile`: every `(1−α)`-quantile maximises `s ↦ E ψ_s(f)` (first-order argument, by cases);
  with the certified `Wave8a.cvar_core` (`lem:cvar`: `inf_γ E[γ f]` attained, and equal to an attained
  `sup_s E ψ_s(f)`), this gives `E ψ_q(f) = inf_{R_α(P)} E_{P'} f` (`lower_attain`) and its mirror
  `upper_attain`; `exists_quantile` (sInf of `{t : p ≤ P(f ≤ t)}`, continuity of measure);
* `lem1_rkhs_route`: `⟨f, ∫ γ φ dP⟩ = ∫ γ ⟨f, φ⟩ dP` (certified `Concentration.inner_integral_smul`) and the
  `EReal` coercion of a bounded infimum;
* Lemma 2: pointwise identities by cases; the variance comparison from `Var h(W) ≤ E(h(W) − h(EW))² ≤ Var W`
  for a 1-Lipschitz `h`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave30tq

open StatFormal.TrimmedMMD.ZeroSet StatFormal.TrimmedMMD.Concentration

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-! ### Elementary facts -/

lemma beta_pos {α : ℝ} (hα1 : α < 1) : 0 < beta α := by
  unfold beta; exact one_div_pos.2 (by linarith)

lemma beta_mul_one_sub {α : ℝ} (hα1 : α < 1) : beta α * (1 - α) = 1 := by
  unfold beta; field_simp [show (1 - α) ≠ 0 by linarith]

lemma one_le_beta {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) : 1 ≤ beta α := by
  unfold beta; rw [le_div_iff₀ (by linarith)]; linarith

lemma integrable_of_abs_le {μ : Measure 𝒳} [IsFiniteMeasure μ] {h : 𝒳 → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) : Integrable h μ :=
  Integrable.of_mem_Icc (-C) C hh.aemeasurable (ae_of_all _ fun x => abs_le.1 (hC x))

lemma isTrim_one {P : Measure 𝒳} [IsProbabilityMeasure P] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    IsTrimDensity P α (fun _ => 1) := by
  refine ⟨measurable_const, fun _ => ⟨zero_le_one, ?_⟩, by simp⟩
  have := one_le_beta hα0 hα1; unfold beta at this; exact this

lemma integral_trimMeasure (P : Measure 𝒳) {α : ℝ} {γ : 𝒳 → ℝ} (hγ : IsTrimDensity P α γ)
    (f : 𝒳 → ℝ) : ∫ x, f x ∂(trimMeasure P γ) = ∫ x, γ x * f x ∂P := by
  unfold trimMeasure
  have hfun : (fun x => ENNReal.ofReal (γ x)) = fun x => ((γ x).toNNReal : ℝ≥0∞) := rfl
  rw [hfun, integral_withDensity_eq_integral_smul hγ.1.real_toNNReal f]
  congr 1; funext x
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hγ.2.1 x).1]

lemma isProb_trimMeasure (P : Measure 𝒳) [IsProbabilityMeasure P] {α : ℝ} {γ : 𝒳 → ℝ}
    (hγ : IsTrimDensity P α γ) : IsProbabilityMeasure (trimMeasure P γ) := by
  constructor
  unfold trimMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable γ P := integrable_of_abs_le hγ.1 (C := 1 / (1 - α)) fun x => by
    rw [abs_of_nonneg (hγ.2.1 x).1]; exact (hγ.2.1 x).2
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (hγ.2.1 x).1), hγ.2.2,
    ENNReal.ofReal_one]

lemma abs_integral_trim_le {P : Measure 𝒳} [IsProbabilityMeasure P] {α : ℝ} {γ : 𝒳 → ℝ}
    (hγ : IsTrimDensity P α γ) {f : 𝒳 → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    |∫ x, f x ∂(trimMeasure P γ)| ≤ C := by
  have := isProb_trimMeasure P hγ
  have hi : Integrable f (trimMeasure P γ) := integrable_of_abs_le hf hC
  rw [abs_le]
  constructor
  · have h := integral_mono (integrable_const (-C)) hi fun x => (abs_le.1 (hC x)).1
    simpa using h
  · have h := integral_mono hi (integrable_const C) fun x => (abs_le.1 (hC x)).2
    simpa using h

instance nonempty_trim {P : Measure 𝒳} [IsProbabilityMeasure P] {α : ℝ} [Fact (0 ≤ α)] [Fact (α < 1)] :
    Nonempty {γ : 𝒳 → ℝ // IsTrimDensity P α γ} :=
  ⟨⟨fun _ => 1, isTrim_one (Fact.out) (Fact.out)⟩⟩

lemma bddBelow_trim {P : Measure 𝒳} [IsProbabilityMeasure P] {α : ℝ} {f : 𝒳 → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    BddBelow (Set.range fun γ : {γ : 𝒳 → ℝ // IsTrimDensity P α γ} => ∫ x, f x ∂(trimMeasure P γ.1)) :=
  ⟨-C, by rintro _ ⟨γ, rfl⟩; exact (abs_le.1 (abs_integral_trim_le γ.2 hf hC)).1⟩

lemma bddAbove_trim {P : Measure 𝒳} [IsProbabilityMeasure P] {α : ℝ} {f : 𝒳 → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    BddAbove (Set.range fun γ : {γ : 𝒳 → ℝ // IsTrimDensity P α γ} => ∫ x, f x ∂(trimMeasure P γ.1)) :=
  ⟨C, by rintro _ ⟨γ, rfl⟩; exact (abs_le.1 (abs_integral_trim_le γ.2 hf hC)).2⟩

lemma integral_psiS (μ : Measure 𝒳) [IsProbabilityMeasure μ] {α s : ℝ} {f : 𝒳 → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    ∫ x, psiS α s (f x) ∂μ = s - beta α * ∫ x, max (s - f x) 0 ∂μ := by
  have hm : Integrable (fun x => max (s - f x) 0) μ :=
    integrable_of_abs_le ((measurable_const.sub hf).max measurable_const) (C := |s| + C) fun x => by
      have := abs_le.1 (hC x)
      rw [abs_le]; constructor
      · have := le_max_right (s - f x) 0; linarith [abs_nonneg s]
      · refine max_le ?_ (by linarith [abs_nonneg s])
        linarith [le_abs_self s]
  unfold psiS
  rw [integral_sub (integrable_const s) (hm.const_mul _), integral_const, probReal_univ, one_smul,
    integral_const_mul]

lemma integral_upper (μ : Measure 𝒳) [IsProbabilityMeasure μ] {α s' : ℝ} {f : 𝒳 → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    ∫ x, (s' + beta α * max (f x - s') 0) ∂μ = s' + beta α * ∫ x, max (f x - s') 0 ∂μ := by
  have hm : Integrable (fun x => max (f x - s') 0) μ :=
    integrable_of_abs_le ((hf.sub measurable_const).max measurable_const) (C := C + |s'|) fun x => by
      have := abs_le.1 (hC x)
      rw [abs_le]; constructor
      · have := le_max_right (f x - s') 0; linarith [abs_nonneg s']
      · refine max_le ?_ (by linarith [abs_nonneg s'])
        linarith [neg_abs_le s']
  rw [integral_add (integrable_const s') (hm.const_mul _), integral_const, probReal_univ, one_smul,
    integral_const_mul]

/-! ### Lemma 1 -/

/-- `E_P ψ_s(f) ≤ E_{P'} f` for every trimming `P'` of `P`. -/
lemma psi_le_trim (P : Measure 𝒳) [IsProbabilityMeasure P] {α : ℝ} (hα1 : α < 1) {f : 𝒳 → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) {γ : 𝒳 → ℝ} (hγ : IsTrimDensity P α γ) (s : ℝ) :
    ∫ x, psiS α s (f x) ∂P ≤ ∫ x, f x ∂(trimMeasure P γ) := by
  have hβ := beta_pos hα1
  have hγb : ∀ x, 0 ≤ γ x ∧ γ x ≤ beta α := fun x => hγ.2.1 x
  have hγi : Integrable γ P := integrable_of_abs_le hγ.1 (C := beta α) fun x => by
    rw [abs_of_nonneg (hγb x).1]; exact (hγb x).2
  have hmi : Integrable (fun x => max (s - f x) 0) P :=
    integrable_of_abs_le ((measurable_const.sub hf).max measurable_const) (C := |s| + C) fun x => by
      have := abs_le.1 (hC x)
      rw [abs_le]; constructor
      · have := le_max_right (s - f x) 0; linarith [abs_nonneg s]
      · refine max_le ?_ (by linarith [abs_nonneg s])
        linarith [le_abs_self s]
  have hγfi : Integrable (fun x => γ x * f x) P :=
    integrable_of_abs_le (hγ.1.mul hf) (C := beta α * C) fun x => by
      rw [abs_mul, abs_of_nonneg (hγb x).1]
      exact mul_le_mul (hγb x).2 (hC x) (abs_nonneg _) hβ.le
  rw [integral_trimMeasure P hγ, integral_psiS P hf hC]
  have hkey : s - beta α * ∫ x, max (s - f x) 0 ∂P =
      ∫ x, (s * γ x - beta α * max (s - f x) 0) ∂P := by
    rw [integral_sub (hγi.const_mul s) (hmi.const_mul _), integral_const_mul, integral_const_mul,
      hγ.2.2, mul_one]
  rw [hkey]
  refine integral_mono ((hγi.const_mul s).sub (hmi.const_mul _)) hγfi fun x => ?_
  have h1 : s - f x ≤ max (s - f x) 0 := le_max_left _ _
  have h2 : 0 ≤ max (s - f x) 0 := le_max_right _ _
  have h3 : γ x * (s - f x) ≤ γ x * max (s - f x) 0 := mul_le_mul_of_nonneg_left h1 (hγb x).1
  have h4 : γ x * max (s - f x) 0 ≤ beta α * max (s - f x) 0 := mul_le_mul_of_nonneg_right (hγb x).2 h2
  show s * γ x - beta α * max (s - f x) 0 ≤ γ x * f x
  nlinarith

/-- `E_{Q'} f ≤ E_Q[s' + β(f − s')₊]` for every trimming `Q'` of `Q`. -/
lemma trim_le_upper (Q : Measure 𝒳) [IsProbabilityMeasure Q] {α : ℝ} (hα1 : α < 1) {f : 𝒳 → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) {γ : 𝒳 → ℝ} (hγ : IsTrimDensity Q α γ) (s' : ℝ) :
    ∫ x, f x ∂(trimMeasure Q γ) ≤ ∫ x, (s' + beta α * max (f x - s') 0) ∂Q := by
  have hβ := beta_pos hα1
  have hγb : ∀ x, 0 ≤ γ x ∧ γ x ≤ beta α := fun x => hγ.2.1 x
  have hγi : Integrable γ Q := integrable_of_abs_le hγ.1 (C := beta α) fun x => by
    rw [abs_of_nonneg (hγb x).1]; exact (hγb x).2
  have hmi : Integrable (fun x => max (f x - s') 0) Q :=
    integrable_of_abs_le ((hf.sub measurable_const).max measurable_const) (C := C + |s'|) fun x => by
      have := abs_le.1 (hC x)
      rw [abs_le]; constructor
      · have := le_max_right (f x - s') 0; linarith [abs_nonneg s']
      · refine max_le ?_ (by linarith [abs_nonneg s'])
        linarith [neg_abs_le s']
  have hγfi : Integrable (fun x => γ x * f x) Q :=
    integrable_of_abs_le (hγ.1.mul hf) (C := beta α * C) fun x => by
      rw [abs_mul, abs_of_nonneg (hγb x).1]
      exact mul_le_mul (hγb x).2 (hC x) (abs_nonneg _) hβ.le
  rw [integral_trimMeasure Q hγ, integral_upper Q hf hC]
  have hkey : s' + beta α * ∫ x, max (f x - s') 0 ∂Q =
      ∫ x, (s' * γ x + beta α * max (f x - s') 0) ∂Q := by
    rw [integral_add (hγi.const_mul s') (hmi.const_mul _), integral_const_mul, integral_const_mul,
      hγ.2.2, mul_one]
  rw [hkey]
  refine integral_mono hγfi ((hγi.const_mul s').add (hmi.const_mul _)) fun x => ?_
  have h1 : f x - s' ≤ max (f x - s') 0 := le_max_left _ _
  have h2 : 0 ≤ max (f x - s') 0 := le_max_right _ _
  have h3 : γ x * (f x - s') ≤ γ x * max (f x - s') 0 := mul_le_mul_of_nonneg_left h1 (hγb x).1
  have h4 : γ x * max (f x - s') 0 ≤ beta α * max (f x - s') 0 := mul_le_mul_of_nonneg_right (hγb x).2 h2
  show γ x * f x ≤ s' * γ x + beta α * max (f x - s') 0
  nlinarith

theorem lem1_trim_route : Claims.lem1_trim := by
  intro 𝒳 _ P Q _ _ α f s s' γ γ' hf ⟨C, hC⟩ _ hα1 hγ hγ'
  unfold theta
  have h1 := psi_le_trim P hα1 hf hC hγ s
  have h2 := trim_le_upper Q hα1 hf hC hγ' s'
  linarith

lemma le_trimInf (P : Measure 𝒳) [IsProbabilityMeasure P] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {f : 𝒳 → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) (s : ℝ) :
    ∫ x, psiS α s (f x) ∂P ≤ trimInf P α f := by
  have : Fact (0 ≤ α) := ⟨hα0⟩
  have : Fact (α < 1) := ⟨hα1⟩
  exact le_ciInf fun γ => psi_le_trim P hα1 hf hC γ.2 s

lemma trimSup_le (Q : Measure 𝒳) [IsProbabilityMeasure Q] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {f : 𝒳 → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) (s' : ℝ) :
    trimSup Q α f ≤ ∫ x, (s' + beta α * max (f x - s') 0) ∂Q := by
  have : Fact (0 ≤ α) := ⟨hα0⟩
  have : Fact (α < 1) := ⟨hα1⟩
  exact ciSup_le fun γ => trim_le_upper Q hα1 hf hC γ.2 s'

theorem lem1_route : Claims.lem1 := by
  intro 𝒳 _ P Q _ _ α f s s' hf ⟨C, hC⟩ hα0 hα1
  unfold theta
  have h1 := le_trimInf P hα0 hα1 hf hC s
  have h2 := trimSup_le Q hα0 hα1 hf hC s'
  linarith

theorem lem1_null_route : Claims.lem1_null := by
  intro 𝒳 _ P Q _ _ α f hf ⟨C, hC⟩ hα0 hα1 hTV
  obtain ⟨gP, gQ, hP, hQ, heq⟩ :=
    (StatFormal.TrimmedMMD.ZeroSet.tvintersect 𝒳 P Q α hα0 hα1).1 hTV
  have : Fact (0 ≤ α) := ⟨hα0⟩
  have : Fact (α < 1) := ⟨hα1⟩
  have h1 : trimInf P α f ≤ ∫ x, f x ∂(trimMeasure P gP) :=
    ciInf_le (bddBelow_trim hf hC) ⟨gP, hP⟩
  have h2 : ∫ x, f x ∂(trimMeasure Q gQ) ≤ trimSup Q α f :=
    le_ciSup (bddAbove_trim hf hC) ⟨gQ, hQ⟩
  have h3 : trimMeasure P gP = trimMeasure Q gQ := heq
  rw [h3] at h1
  have hT : trimInf P α f - trimSup Q α f ≤ 0 := by linarith
  refine ⟨hT, fun s s' => ?_⟩
  exact (lem1_route 𝒳 P Q α f s s' hf ⟨C, hC⟩ hα0 hα1).trans hT

/-! ### Quantiles -/

/-- Pointwise, `s ≥ q`: `ψ_s(u) − ψ_q(u) ≤ (s − q) − β(s − q)·1{u ≤ q}`. -/
lemma psi_diff_le_ge {β s q u : ℝ} (hβ : 0 ≤ β) (hqs : q ≤ s) :
    (s - β * max (s - u) 0) - (q - β * max (q - u) 0) ≤
      (s - q) - β * ((s - q) * (if u ≤ q then 1 else 0)) := by
  split_ifs with hu
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
  · rw [max_eq_right (by linarith : q - u ≤ 0)]
    have := mul_nonneg hβ (le_max_right (s - u) 0)
    linarith

/-- Pointwise, `s < q`: `ψ_s(u) − ψ_q(u) ≤ (s − q) + β(q − s)·1{u < q}`. -/
lemma psi_diff_le_lt {β s q u : ℝ} (hβ : 0 ≤ β) (hsq : s < q) :
    (s - β * max (s - u) 0) - (q - β * max (q - u) 0) ≤
      (s - q) + β * ((q - s) * (if u < q then 1 else 0)) := by
  split_ifs with hu
  · rw [max_eq_left (by linarith : 0 ≤ q - u)]
    have h1 : s - u ≤ max (s - u) 0 := le_max_left _ _
    have := mul_le_mul_of_nonneg_left h1 hβ
    nlinarith
  · rw [max_eq_right (by linarith : q - u ≤ 0), max_eq_right (by linarith : s - u ≤ 0)]
    simp

/-- Every `(1−α)`-quantile maximises `s ↦ E ψ_s(f)`. -/
lemma psi_le_psi_quantile (μ : Measure 𝒳) [IsProbabilityMeasure μ] {α : ℝ} (hα1 : α < 1)
    {f : 𝒳 → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) {q : ℝ}
    (hq : IsQuantileAt μ f (1 - α) q) (s : ℝ) :
    ∫ x, psiS α s (f x) ∂μ ≤ ∫ x, psiS α q (f x) ∂μ := by
  have hβ := beta_pos hα1
  have hb1 := beta_mul_one_sub hα1
  have hpsi_int : ∀ t, Integrable (fun x => psiS α t (f x)) μ := fun t => by
    have h := integral_psiS μ (s := t) (α := α) hf hC
    refine integrable_of_abs_le ((measurable_const.sub (measurable_const.mul
      ((measurable_const.sub hf).max measurable_const)))) (C := |t| + beta α * (|t| + C)) fun x => ?_
    have hx := abs_le.1 (hC x)
    have hm0 : 0 ≤ max (t - f x) 0 := le_max_right _ _
    have hm1 : max (t - f x) 0 ≤ |t| + C := max_le (by linarith [le_abs_self t]) (by linarith [abs_nonneg t])
    unfold psiS
    rw [abs_le]; constructor
    · nlinarith [le_abs_self t, neg_abs_le t]
    · nlinarith [le_abs_self t, neg_abs_le t]
  have hset_le : MeasurableSet {x | f x ≤ q} := measurableSet_le hf measurable_const
  have hset_lt : MeasurableSet {x | f x < q} := measurableSet_lt hf measurable_const
  rw [← sub_nonpos, ← integral_sub (hpsi_int s) (hpsi_int q)]
  rcases le_or_gt q s with hqs | hsq
  · have hb : ∀ x, psiS α s (f x) - psiS α q (f x) ≤
        (s - q) - beta α * ((s - q) * ({x | f x ≤ q}.indicator (fun _ => (1 : ℝ)) x)) := fun x => by
      have := psi_diff_le_ge (u := f x) hβ.le hqs
      unfold psiS
      convert this using 3
      by_cases h : f x ≤ q <;> simp [h]
    have hind : Integrable ({x | f x ≤ q}.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hset_le
    have hint2 : Integrable (fun x => (s - q) - beta α * ((s - q) *
        ({x | f x ≤ q}.indicator (fun _ => (1 : ℝ)) x))) μ :=
      (integrable_const _).sub ((hind.const_mul _).const_mul _)
    have hcalc : ∫ x, ((s - q) - beta α * ((s - q) * ({x | f x ≤ q}.indicator (fun _ => (1 : ℝ)) x))) ∂μ =
        (s - q) - beta α * ((s - q) * μ.real {x | f x ≤ q}) := by
      rw [integral_sub (integrable_const _) ((hind.const_mul _).const_mul _), integral_const,
        probReal_univ, one_smul, integral_const_mul, integral_const_mul,
        integral_indicator_const _ hset_le, smul_eq_mul, mul_one]
    refine (integral_mono ((hpsi_int s).sub (hpsi_int q)) hint2 hb).trans ?_
    rw [hcalc]
    have := hq.2
    have h0 : 0 ≤ s - q := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hβ.le h0)]
  · have hb : ∀ x, psiS α s (f x) - psiS α q (f x) ≤
        (s - q) + beta α * ((q - s) * ({x | f x < q}.indicator (fun _ => (1 : ℝ)) x)) := fun x => by
      have := psi_diff_le_lt (u := f x) hβ.le hsq
      unfold psiS
      convert this using 3
      by_cases h : f x < q <;> simp [h]
    have hind : Integrable ({x | f x < q}.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hset_lt
    have hint2 : Integrable (fun x => (s - q) + beta α * ((q - s) *
        ({x | f x < q}.indicator (fun _ => (1 : ℝ)) x))) μ :=
      (integrable_const _).add ((hind.const_mul _).const_mul _)
    have hcalc : ∫ x, ((s - q) + beta α * ((q - s) * ({x | f x < q}.indicator (fun _ => (1 : ℝ)) x))) ∂μ =
        (s - q) + beta α * ((q - s) * μ.real {x | f x < q}) := by
      rw [integral_add (integrable_const _) ((hind.const_mul _).const_mul _), integral_const,
        probReal_univ, one_smul, integral_const_mul, integral_const_mul,
        integral_indicator_const _ hset_lt, smul_eq_mul, mul_one]
    refine (integral_mono ((hpsi_int s).sub (hpsi_int q)) hint2 hb).trans ?_
    rw [hcalc]
    have := hq.1
    have h0 : 0 ≤ q - s := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hβ.le h0)]

/-- At a `(1−α)`-quantile, `E_P ψ_q(f) = inf_{P' ∈ R_α(P)} E_{P'} f`. -/
lemma lower_attain (P : Measure 𝒳) [IsProbabilityMeasure P] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {f : 𝒳 → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) {q : ℝ}
    (hq : IsQuantileAt P f (1 - α) q) :
    ∫ x, psiS α q (f x) ∂P = trimInf P α f := by
  have : Fact (0 ≤ α) := ⟨hα0⟩
  have : Fact (α < 1) := ⟨hα1⟩
  refine le_antisymm (le_trimInf P hα0 hα1 hf hC q) ?_
  have hC' : ∀ x, |(-f) x| ≤ C := fun x => by simpa using hC x
  obtain ⟨v, ⟨⟨g₀, hg₀, hv⟩, -⟩, ⟨⟨t, ht⟩, -⟩⟩ :=
    StatFormal.Wave8a.cvar_core P (Y := -f) hf.neg hC' hα0 hα1
  -- `trimInf ≤ ∫ f dP_{g₀} = -v`
  have h1 : trimInf P α f ≤ ∫ x, f x ∂(trimMeasure P g₀) :=
    ciInf_le (bddBelow_trim hf hC) ⟨g₀, hg₀⟩
  have h2 : ∫ x, f x ∂(trimMeasure P g₀) = -v := by
    rw [integral_trimMeasure P hg₀, hv, ← integral_neg]
    congr 1; funext x; simp
  -- `E ψ_{-t}(f) = -v`
  have h3 : ∫ x, psiS α (-t) (f x) ∂P = -v := by
    rw [integral_psiS P hf hC, ← ht]
    simp only [Pi.neg_apply]
    have : (fun x => max (-t - f x) 0) = fun x => max (-f x - t) 0 := by
      funext x; ring_nf
    rw [this]; unfold beta; ring
  have h4 := psi_le_psi_quantile P hα1 hf hC hq (-t)
  linarith

lemma quantile_neg {μ : Measure 𝒳} [IsProbabilityMeasure μ] {f : 𝒳 → ℝ} (hf : Measurable f) {α q : ℝ}
    (hq : IsQuantileAt μ f α q) : IsQuantileAt μ (fun x => -f x) (1 - α) (-q) := by
  have h1 : {x | -f x < -q} = {x | f x ≤ q}ᶜ := by ext x; simp
  have h2 : {x | -f x ≤ -q} = {x | f x < q}ᶜ := by ext x; simp
  unfold IsQuantileAt
  rw [h1, h2, probReal_compl_eq_one_sub (measurableSet_le hf measurable_const),
    probReal_compl_eq_one_sub (measurableSet_lt hf measurable_const)]
  exact ⟨by linarith [hq.2], by linarith [hq.1]⟩

lemma quantile_of_neg {μ : Measure 𝒳} [IsProbabilityMeasure μ] {f : 𝒳 → ℝ} (hf : Measurable f) {α q : ℝ}
    (hq : IsQuantileAt μ (fun x => -f x) (1 - α) q) : IsQuantileAt μ f α (-q) := by
  have h1 : {x | f x < -q} = {x | -f x ≤ q}ᶜ := by ext x; simp; constructor <;> intro h <;> linarith
  have h2 : {x | f x ≤ -q} = {x | -f x < q}ᶜ := by ext x; simp; constructor <;> intro h <;> linarith
  have hm1 : MeasurableSet {x | -f x ≤ q} := measurableSet_le hf.neg measurable_const
  have hm2 : MeasurableSet {x | -f x < q} := measurableSet_lt hf.neg measurable_const
  unfold IsQuantileAt
  rw [h1, h2, probReal_compl_eq_one_sub hm1, probReal_compl_eq_one_sub hm2]
  exact ⟨by linarith [hq.2], by linarith [hq.1]⟩

/-- At an `α`-quantile, `E_Q[q' + β(f − q')₊] = sup_{Q' ∈ R_α(Q)} E_{Q'} f`. -/
lemma upper_attain (Q : Measure 𝒳) [IsProbabilityMeasure Q] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {f : 𝒳 → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) {q' : ℝ}
    (hq : IsQuantileAt Q f α q') :
    ∫ x, (q' + beta α * max (f x - q') 0) ∂Q = trimSup Q α f := by
  have : Fact (0 ≤ α) := ⟨hα0⟩
  have : Fact (α < 1) := ⟨hα1⟩
  refine le_antisymm ?_ (trimSup_le Q hα0 hα1 hf hC q')
  obtain ⟨v, ⟨⟨g₀, hg₀, hv⟩, -⟩, ⟨⟨t, ht⟩, -⟩⟩ := StatFormal.Wave8a.cvar_core Q hf hC hα0 hα1
  have h1 : ∫ x, f x ∂(trimMeasure Q g₀) ≤ trimSup Q α f :=
    le_ciSup (bddAbove_trim hf hC) ⟨g₀, hg₀⟩
  have h2 : ∫ x, f x ∂(trimMeasure Q g₀) = v := by rw [integral_trimMeasure Q hg₀, hv]
  -- minimisation at the quantile, through `-f`
  have hC' : ∀ x, |(fun x => -f x) x| ≤ C := fun x => by simpa using hC x
  have hfn : Measurable fun x => -f x := hf.neg
  have hmin := psi_le_psi_quantile Q hα1 hfn hC' (quantile_neg hf hq) (-t)
  rw [integral_psiS Q hfn hC', integral_psiS Q hfn hC'] at hmin
  have e1 : (fun x => max (-t - -f x) 0) = fun x => max (f x - t) 0 := by funext x; ring_nf
  have e2 : (fun x => max (-q' - -f x) 0) = fun x => max (f x - q') 0 := by funext x; ring_nf
  rw [e1, e2] at hmin
  rw [integral_upper Q hf hC]
  have h3 : t + beta α * ∫ x, max (f x - t) 0 ∂Q = v := by unfold beta; exact ht
  linarith

/-- Existence of a `p`-quantile, `0 < p ≤ 1`, for a bounded measurable `f`. -/
lemma exists_quantile (μ : Measure 𝒳) [IsProbabilityMeasure μ] {f : 𝒳 → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ q, IsQuantileAt μ f p q := by
  set S : Set ℝ := {t | p ≤ μ.real {x | f x ≤ t}} with hS
  have hCS : C ∈ S := by
    have : {x | f x ≤ C} = univ := by ext x; simp [(abs_le.1 (hC x)).2]
    simp only [hS, mem_ofPred_eq, this, probReal_univ]; exact hp1
  have hlow : ∀ t ∈ S, -C ≤ t := fun t ht => by
    by_contra h
    push Not at h
    have : {x | f x ≤ t} = ∅ := by
      ext x; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      linarith [(abs_le.1 (hC x)).1]
    simp only [hS, mem_ofPred_eq, this, measureReal_empty] at ht
    linarith
  have hbdd : BddBelow S := ⟨-C, hlow⟩
  have hne : S.Nonempty := ⟨C, hCS⟩
  set q := sInf S with hq
  refine ⟨q, ?_, ?_⟩
  · -- `μ{f < q} ≤ p`: `{f < q} = ⋃_n {f ≤ q - 1/(n+1)}`
    have hU : {x | f x < q} = ⋃ n : ℕ, {x | f x ≤ q - 1 / ((n : ℝ) + 1)} := by
      ext x; simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have hmono : Monotone fun n : ℕ => {x | f x ≤ q - 1 / ((n : ℝ) + 1)} := by
      intro a b hab x hx
      simp only [mem_ofPred_eq] at hx ⊢
      have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
      linarith
    have hlt : ∀ n : ℕ, μ {x | f x ≤ q - 1 / ((n : ℝ) + 1)} ≤ ENNReal.ofReal p := fun n => by
      have hnS : q - 1 / ((n : ℝ) + 1) ∉ S := fun h => by
        have := csInf_le hbdd h
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      simp only [hS, mem_ofPred_eq, not_le] at hnS
      rw [← ofReal_measureReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal hnS.le
    have hμ : μ {x | f x < q} ≤ ENNReal.ofReal p := by
      rw [hU, hmono.measure_iUnion]
      exact iSup_le hlt
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hp0.le hμ
  · -- `p ≤ μ{f ≤ q}`: `{f ≤ q} = ⋂_n {f ≤ q + 1/(n+1)}`
    have hI : {x | f x ≤ q} = ⋂ n : ℕ, {x | f x ≤ q + 1 / ((n : ℝ) + 1)} := by
      ext x; simp only [mem_ofPred_eq, mem_iInter]
      constructor
      · intro h n
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · intro h
        by_contra hx
        push Not at hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
        linarith [h n]
    have hanti : Antitone fun n : ℕ => {x | f x ≤ q + 1 / ((n : ℝ) + 1)} := by
      intro a b hab x hx
      simp only [mem_ofPred_eq] at hx ⊢
      have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
      linarith
    have hge : ∀ n : ℕ, ENNReal.ofReal p ≤ μ {x | f x ≤ q + 1 / ((n : ℝ) + 1)} := fun n => by
      have hlt : q < q + 1 / ((n : ℝ) + 1) := by
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      obtain ⟨s, hs, hsl⟩ := exists_lt_of_csInf_lt hne hlt
      have hsub : {x | f x ≤ s} ⊆ {x | f x ≤ q + 1 / ((n : ℝ) + 1)} := fun x hx => by
        simp only [mem_ofPred_eq] at hx ⊢; linarith
      have := (show p ≤ μ.real {x | f x ≤ s} from hs).trans (measureReal_mono hsub)
      rw [← ofReal_measureReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal this
    have hμ : ENNReal.ofReal p ≤ μ {x | f x ≤ q} := by
      rw [hI, hanti.measure_iInter (fun n => (measurableSet_le hf measurable_const).nullMeasurableSet)
        ⟨0, measure_ne_top _ _⟩]
      exact le_iInf hge
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hμ

theorem lem1_attain_route : Claims.lem1_attain := by
  intro 𝒳 _ P Q _ _ α f hf ⟨C, hC⟩ hα0 hα1
  have hval : ∀ q q', IsQuantileAt P f (1 - α) q → IsQuantileAt Q f α q' →
      theta P Q α f q q' = trimInf P α f - trimSup Q α f := fun q q' hq hq' => by
    unfold theta
    rw [lower_attain P hα0 hα1 hf hC hq, upper_attain Q hα0 hα1 hf hC hq']
  obtain ⟨q, hq⟩ := exists_quantile P hf hC (p := 1 - α) (by linarith) (by linarith)
  have hC' : ∀ x, |(fun x => -f x) x| ≤ C := fun x => by simpa using hC x
  obtain ⟨q'', hq''⟩ := exists_quantile Q hf.neg hC' (p := 1 - α) (by linarith) (by linarith)
  have hq' := quantile_of_neg hf hq''
  refine ⟨⟨⟨(q, -q''), hval q (-q'') hq hq'⟩, ?_⟩, ⟨q, -q'', hq, hq'⟩, hval⟩
  rintro _ ⟨⟨s, s'⟩, rfl⟩
  exact lem1_route 𝒳 P Q α f s s' hf ⟨C, hC⟩ hα0 hα1

/-! ### The RKHS sentence -/

lemma ereal_coe_ciInf {ι : Type*} [Nonempty ι] {x : ι → ℝ} (hb : BddBelow (Set.range x)) :
    ((⨅ i, x i : ℝ) : EReal) = ⨅ i, (x i : EReal) := by
  refine le_antisymm (le_iInf fun i => EReal.coe_le_coe_iff.2 (ciInf_le hb i)) ?_
  set e : EReal := ⨅ i, (x i : EReal) with he
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hle : ∀ i, e ≤ (x i : EReal) := fun i => iInf_le _ i
  have hge : ((⨅ i, x i : ℝ) : EReal) ≤ e := le_iInf fun i => EReal.coe_le_coe_iff.2 (ciInf_le hb i)
  have htop : e ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hle i₀)
  have hbot : e ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hge
  rw [← EReal.coe_toReal htop hbot] at hle ⊢
  exact EReal.coe_le_coe_iff.2 (le_ciInf fun i => EReal.coe_le_coe_iff.1 (hle i))

lemma ereal_coe_ciSup {ι : Type*} [Nonempty ι] {x : ι → ℝ} (hb : BddAbove (Set.range x)) :
    ((⨆ i, x i : ℝ) : EReal) = ⨆ i, (x i : EReal) := by
  refine le_antisymm ?_ (iSup_le fun i => EReal.coe_le_coe_iff.2 (le_ciSup hb i))
  set e : EReal := ⨆ i, (x i : EReal) with he
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hle : ∀ i, (x i : EReal) ≤ e := fun i => le_iSup (fun i => (x i : EReal)) i
  have hge : e ≤ ((⨆ i, x i : ℝ) : EReal) := iSup_le fun i => EReal.coe_le_coe_iff.2 (le_ciSup hb i)
  have htop : e ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hge
  have hbot : e ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hle i₀)
  rw [← EReal.coe_toReal htop hbot] at hle ⊢
  exact EReal.coe_le_coe_iff.2 (ciSup_le fun i => EReal.coe_le_coe_iff.1 (hle i))

theorem lem1_rkhs_route : Claims.lem1_rkhs := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ α f hφ hκ hα0 hα1
  have : Fact (0 ≤ α) := ⟨hα0⟩
  have : Fact (α < 1) := ⟨hα1⟩
  set h : 𝒳 → ℝ := fun x => ⟪f, φ x⟫_ℝ with hh
  have hhm : Measurable h := (stronglyMeasurable_const.inner hφ).measurable
  have hhC : ∀ x, |h x| ≤ ‖f‖ * κ := fun x =>
    (abs_real_inner_le_norm f (φ x)).trans (mul_le_mul_of_nonneg_left (hκ x) (norm_nonneg f))
  -- values of `⟪f, a⟫` on the region are the trimmed means of `h`
  have hval : ∀ (R : Measure 𝒳) [IsProbabilityMeasure R],
      (⨅ a ∈ region φ α R, ((⟪f, a⟫_ℝ : ℝ) : EReal)) = ((trimInf R α h : ℝ) : EReal) ∧
      (⨆ b ∈ region φ α R, ((⟪f, b⟫_ℝ : ℝ) : EReal)) = ((trimSup R α h : ℝ) : EReal) := by
    intro R _
    have hmem : ∀ γ : {γ : 𝒳 → ℝ // IsTrimDensity R α γ},
        ∫ x, γ.1 x • φ x ∂R ∈ region φ α R := fun γ => ⟨γ.1, γ.2.1, γ.2.2.1, γ.2.2.2, rfl⟩
    have hinner : ∀ γ : {γ : 𝒳 → ℝ // IsTrimDensity R α γ},
        ⟪f, ∫ x, γ.1 x • φ x ∂R⟫_ℝ = ∫ x, h x ∂(trimMeasure R γ.1) := fun γ => by
      rw [integral_trimMeasure R γ.2]
      exact inner_integral_smul R hφ hκ γ.2.1 γ.2.2.1 f
    have hback : ∀ a ∈ region φ α R, ∃ γ : {γ : 𝒳 → ℝ // IsTrimDensity R α γ},
        ⟪f, a⟫_ℝ = ∫ x, h x ∂(trimMeasure R γ.1) := by
      rintro a ⟨g, hg, hgb, hg1, rfl⟩
      exact ⟨⟨g, hg, hgb, hg1⟩, hinner ⟨g, hg, hgb, hg1⟩⟩
    constructor
    · unfold trimInf
      rw [ereal_coe_ciInf (bddBelow_trim hhm hhC)]
      refine le_antisymm (le_iInf fun γ => ?_) (le_iInf₂ fun a ha => ?_)
      · exact (iInf₂_le _ (hmem γ)).trans_eq (by rw [hinner γ])
      · obtain ⟨γ, hγ⟩ := hback a ha
        exact (iInf_le _ γ).trans_eq (by rw [hγ])
    · unfold trimSup
      rw [ereal_coe_ciSup (bddAbove_trim hhm hhC)]
      refine le_antisymm (iSup₂_le fun a ha => ?_) (iSup_le fun γ => ?_)
      · obtain ⟨γ, hγ⟩ := hback a ha
        exact (le_iSup _ γ).trans_eq' (by rw [hγ])
      · exact (le_iSup₂ (f := fun b (_ : b ∈ region φ α R) => ((⟪f, b⟫_ℝ : ℝ) : EReal)) _ (hmem γ)).trans_eq'
          (by rw [hinner γ])
  unfold StatFormal.Wave17a.sepVal
  rw [(hval P).1, (hval Q).2, ← EReal.coe_sub]

/-! ### Lemma 2 -/

omit [MeasurableSpace 𝒳] in
lemma clip_mem {f : 𝒳 → ℝ} {s s' : ℝ} (hs : s' < s) (x : 𝒳) : clip f s s' x ∈ Icc s' s := by
  unfold clip
  exact ⟨le_min (le_max_right _ _) hs.le, min_le_right _ _⟩

lemma measurable_clip {f : 𝒳 → ℝ} (hf : Measurable f) (s s' : ℝ) : Measurable (clip f s s') :=
  (hf.max measurable_const).min measurable_const

omit [MeasurableSpace 𝒳] in
lemma abs_clip_le {f : 𝒳 → ℝ} {s s' : ℝ} (hs : s' < s) (x : 𝒳) : |clip f s s' x| ≤ |s| + |s'| := by
  have h := clip_mem (f := f) hs x
  rw [abs_le]; constructor
  · linarith [h.1, neg_abs_le s', abs_nonneg s]
  · linarith [h.2, le_abs_self s, abs_nonneg s']

theorem lem2_1_route : Claims.lem2_1 := by
  intro 𝒳 _ P Q _ _ α f s s' hf _ hα1 hs
  have hss : 0 < s - s' := by linarith
  have hr : ∀ x, ramp f s s' x ∈ Icc (0 : ℝ) 1 := fun x => by
    have h := clip_mem (f := f) hs x
    unfold ramp
    exact ⟨div_nonneg (by linarith [h.1]) hss.le, (div_le_one hss).2 (by linarith [h.2])⟩
  refine ⟨hr, ?_⟩
  have hrm : Measurable (ramp f s s') := ((measurable_clip hf s s').sub_const s').div_const _
  have hri : ∀ μ : Measure 𝒳, IsFiniteMeasure μ → Integrable (ramp f s s') μ := fun μ _ =>
    Integrable.of_mem_Icc 0 1 hrm.aemeasurable (ae_of_all _ hr)
  have hc : ∀ x, clip f s s' x = s' + (s - s') * ramp f s s' x := fun x => by
    unfold ramp; field_simp; ring
  have e1 : ∀ x, psiS α s (clip f s s' x) = (s - beta α * (s - s')) + beta α * (s - s') * ramp f s s' x :=
    fun x => by
      have h := clip_mem (f := f) hs x
      unfold psiS
      rw [max_eq_left (by linarith [h.2]), hc x]; ring
  have e2 : ∀ x, s' + beta α * max (clip f s s' x - s') 0 = s' + beta α * (s - s') * ramp f s s' x :=
    fun x => by
      have h := clip_mem (f := f) hs x
      rw [max_eq_left (by linarith [h.1]), hc x]; ring
  unfold theta
  simp_rw [e1, e2]
  rw [integral_add (integrable_const _) ((hri P inferInstance).const_mul _),
    integral_add (integrable_const _) ((hri Q inferInstance).const_mul _),
    integral_const, integral_const, probReal_univ, probReal_univ, one_smul, one_smul,
    integral_const_mul, integral_const_mul]
  have hb := beta_mul_one_sub hα1
  linear_combination (-(s - s')) * hb

theorem lem2_2_route : Claims.lem2_2 := by
  intro 𝒳 _ P Q _ _ α f s s' hf ⟨C, hC⟩ _ hα1 hs
  have hβ := beta_pos hα1
  have hcm := measurable_clip hf s s'
  have hcC := abs_clip_le (f := f) hs
  -- pointwise identities
  have p1 : ∀ x, psiS α s (clip f s s' x) - psiS α s (f x) = beta α * max (s' - f x) 0 := fun x => by
    unfold psiS clip
    rcases le_total (f x) s' with h1 | h1
    · rw [max_eq_right h1, min_eq_left hs.le, max_eq_left (by linarith : 0 ≤ s - s'),
        max_eq_left (by linarith : 0 ≤ s - f x), max_eq_left (by linarith : 0 ≤ s' - f x)]; ring
    · rcases le_total (f x) s with h2 | h2
      · rw [max_eq_left h1, min_eq_left h2, max_eq_right (by linarith : s' - f x ≤ 0)]; ring
      · rw [max_eq_left h1, min_eq_right h2, max_eq_right (by linarith : s' - f x ≤ 0),
          max_eq_right (by linarith : s - f x ≤ 0)]; simp
  have p2 : ∀ x, (s' + beta α * max (clip f s s' x - s') 0) - (s' + beta α * max (f x - s') 0) =
      -(beta α * max (f x - s) 0) := fun x => by
    unfold clip
    rcases le_total (f x) s' with h1 | h1
    · rw [max_eq_right h1, min_eq_left hs.le, max_eq_right (by linarith : f x - s' ≤ 0),
        max_eq_right (by linarith : f x - s ≤ 0)]; simp
    · rcases le_total (f x) s with h2 | h2
      · rw [max_eq_left h1, min_eq_left h2, max_eq_right (by linarith : f x - s ≤ 0)]; simp
      · rw [max_eq_left h1, min_eq_right h2, max_eq_left (by linarith : 0 ≤ s - s'),
          max_eq_left (by linarith : 0 ≤ f x - s'), max_eq_left (by linarith : 0 ≤ f x - s)]; ring
  -- integrability
  have hpsi : ∀ (μ : Measure 𝒳) [IsFiniteMeasure μ] (u : 𝒳 → ℝ), Measurable u → ∀ D, (∀ x, |u x| ≤ D) →
      Integrable (fun x => psiS α s (u x)) μ := fun μ _ u hu D hD => by
    refine integrable_of_abs_le (measurable_const.sub (measurable_const.mul
      ((measurable_const.sub hu).max measurable_const))) (C := |s| + beta α * (|s| + D)) fun x => ?_
    have hx := abs_le.1 (hD x)
    have hm0 : 0 ≤ max (s - u x) 0 := le_max_right _ _
    have hm1 : max (s - u x) 0 ≤ |s| + D :=
      max_le (by linarith [le_abs_self s]) (by linarith [abs_nonneg s, abs_nonneg (u x), hD x])
    unfold psiS
    rw [abs_le]; constructor <;> nlinarith [le_abs_self s, neg_abs_le s]
  have hup : ∀ (μ : Measure 𝒳) [IsFiniteMeasure μ] (u : 𝒳 → ℝ), Measurable u → ∀ D, (∀ x, |u x| ≤ D) →
      Integrable (fun x => s' + beta α * max (u x - s') 0) μ := fun μ _ u hu D hD => by
    refine integrable_of_abs_le (measurable_const.add (measurable_const.mul
      ((hu.sub measurable_const).max measurable_const))) (C := |s'| + beta α * (D + |s'|)) fun x => ?_
    have hx := abs_le.1 (hD x)
    have hm0 : 0 ≤ max (u x - s') 0 := le_max_right _ _
    have hm1 : max (u x - s') 0 ≤ D + |s'| :=
      max_le (by linarith [neg_abs_le s']) (by linarith [abs_nonneg s', abs_nonneg (u x), hD x])
    rw [abs_le]; constructor <;> nlinarith [le_abs_self s', neg_abs_le s']
  have hmP : Integrable (fun x => max (s' - f x) 0) P :=
    integrable_of_abs_le ((measurable_const.sub hf).max measurable_const) (C := |s'| + C) fun x => by
      have := abs_le.1 (hC x)
      rw [abs_le]; constructor
      · have := le_max_right (s' - f x) 0; linarith [abs_nonneg s']
      · exact max_le (by linarith [le_abs_self s']) (by linarith [abs_nonneg s'])
  have hmQ : Integrable (fun x => max (f x - s) 0) Q :=
    integrable_of_abs_le ((hf.sub measurable_const).max measurable_const) (C := C + |s|) fun x => by
      have := abs_le.1 (hC x)
      rw [abs_le]; constructor
      · have := le_max_right (f x - s) 0; linarith [abs_nonneg s]
      · exact max_le (by linarith [neg_abs_le s]) (by linarith [abs_nonneg s])
  have hdiff : theta P Q α (clip f s s') s s' - theta P Q α f s s' =
      beta α * (∫ x, max (s' - f x) 0 ∂P) + beta α * (∫ y, max (f y - s) 0 ∂Q) := by
    unfold theta
    have hP1 := hpsi P (clip f s s') hcm _ hcC
    have hP2 := hpsi P f hf C hC
    have hQ1 := hup Q (clip f s s') hcm _ hcC
    have hQ2 := hup Q f hf C hC
    have eP : (∫ x, psiS α s (clip f s s' x) ∂P) - ∫ x, psiS α s (f x) ∂P =
        beta α * ∫ x, max (s' - f x) 0 ∂P := by
      rw [← integral_sub hP1 hP2, ← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ p1)
    have eQ : (∫ x, (s' + beta α * max (clip f s s' x - s') 0) ∂Q) -
        ∫ x, (s' + beta α * max (f x - s') 0) ∂Q = -(beta α * ∫ y, max (f y - s) 0 ∂Q) := by
      rw [← integral_sub hQ1 hQ2, ← integral_const_mul, ← integral_neg]
      exact integral_congr_ae (ae_of_all _ p2)
    linarith
  refine ⟨hdiff, ?_⟩
  have h1 : 0 ≤ ∫ x, max (s' - f x) 0 ∂P := integral_nonneg fun x => le_max_right _ _
  have h2 : 0 ≤ ∫ y, max (f y - s) 0 ∂Q := integral_nonneg fun x => le_max_right _ _
  positivity

/-- `Var h(W) ≤ Var W` for a 1-Lipschitz `h` and a bounded measurable `W`. -/
lemma variance_lipschitz_le (μ : Measure 𝒳) [IsProbabilityMeasure μ] {W : 𝒳 → ℝ} (hW : Measurable W)
    {D : ℝ} (hD : ∀ x, |W x| ≤ D) {h : ℝ → ℝ} (hhm : Measurable h)
    (hh : ∀ a b, |h a - h b| ≤ |a - b|) :
    variance (fun x => h (W x)) μ ≤ variance W μ := by
  have hhW : Measurable fun x => h (W x) := hhm.comp hW
  have hWi : Integrable W μ := integrable_of_abs_le hW hD
  set m := ∫ x, W x ∂μ with hm
  have hbd : ∀ x, |h (W x)| ≤ |h m| + |W x - m| := fun x => by
    have := hh (W x) m
    calc |h (W x)| = |h m + (h (W x) - h m)| := by ring_nf
      _ ≤ |h m| + |h (W x) - h m| := abs_add_le _ _
      _ ≤ |h m| + |W x - m| := by linarith
  have hhWi : Integrable (fun x => h (W x)) μ :=
    integrable_of_abs_le hhW (C := |h m| + (D + |m|)) fun x => by
      have := hbd x
      have : |W x - m| ≤ D + |m| := (abs_sub _ _).trans (by linarith [hD x])
      linarith
  set m' := ∫ x, h (W x) ∂μ with hm'
  rw [variance_eq_integral hhW.aemeasurable, variance_eq_integral hW.aemeasurable]
  -- `E(h(W) - m')² ≤ E(h(W) - h(m))²`
  have hsq : ∀ (c : ℝ), Integrable (fun x => (h (W x) - c) ^ 2) μ := fun c =>
    integrable_of_abs_le ((hhW.sub_const c).pow_const 2) (C := (|h m| + (D + |m|) + |c|) ^ 2) fun x => by
      have h1 := hbd x
      have h2 : |W x - m| ≤ D + |m| := (abs_sub _ _).trans (by linarith [hD x])
      rw [abs_pow, sq_abs]
      have h3 : |h (W x) - c| ≤ |h m| + (D + |m|) + |c| := (abs_sub _ _).trans (by linarith)
      exact pow_le_pow_left₀ (abs_nonneg _) h3 2 |>.trans_eq' (by rw [sq_abs])
  have hstep1 : ∫ x, (h (W x) - m') ^ 2 ∂μ ≤ ∫ x, (h (W x) - h m) ^ 2 ∂μ := by
    have hexp : ∀ x, (h (W x) - h m) ^ 2 = (h (W x) - m') ^ 2 +
        (2 * (m' - h m) * h (W x) + (h m ^ 2 - m' ^ 2)) := fun x => by ring
    simp_rw [hexp]
    have hB : Integrable (fun x => 2 * (m' - h m) * h (W x) + (h m ^ 2 - m' ^ 2)) μ :=
      (hhWi.const_mul _).add (integrable_const _)
    have hB1 : Integrable (fun x => 2 * (m' - h m) * h (W x)) μ := hhWi.const_mul _
    rw [integral_add (hsq m') hB, integral_add hB1 (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul]
    nlinarith [sq_nonneg (m' - h m)]
  have hWsq : Integrable (fun x => (W x - m) ^ 2) μ :=
    integrable_of_abs_le ((hW.sub_const m).pow_const 2) (C := (D + |m|) ^ 2) fun x => by
      have h2 : |W x - m| ≤ D + |m| := (abs_sub _ _).trans (by linarith [hD x])
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hstep2 : ∫ x, (h (W x) - h m) ^ 2 ∂μ ≤ ∫ x, (W x - m) ^ 2 ∂μ :=
    integral_mono (hsq (h m)) hWsq fun x => by
      have := hh (W x) m
      rw [← sq_abs (h (W x) - h m), ← sq_abs (W x - m)]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
  linarith

theorem lem2_3_route : Claims.lem2_3 := by
  intro 𝒳 _ P Q _ _ α f s s' hf ⟨C, hC⟩ _ hα1 hs
  have hβ := beta_pos hα1
  constructor
  · -- `ψ_s(f̃) = max{ψ_s(f), s − β(s − s')}`
    have hrep : ∀ x, psiS α s (clip f s s' x) = max (psiS α s (f x)) (s - beta α * (s - s')) := fun x => by
      unfold psiS clip
      rcases le_total (f x) s' with h1 | h1
      · rw [max_eq_right h1, min_eq_left hs.le, max_eq_left (by linarith : 0 ≤ s - s'),
          max_eq_left (by linarith : 0 ≤ s - f x)]
        rw [max_eq_right]
        nlinarith [mul_le_mul_of_nonneg_left (show s - s' ≤ s - f x by linarith) hβ.le]
      · rcases le_total (f x) s with h2 | h2
        · rw [max_eq_left h1, min_eq_left h2, max_eq_left (by linarith : 0 ≤ s - f x)]
          rw [max_eq_left]
          nlinarith [mul_le_mul_of_nonneg_left (show s - f x ≤ s - s' by linarith) hβ.le]
        · rw [max_eq_left h1, min_eq_right h2, max_eq_right (by linarith : s - f x ≤ 0)]
          simp only [sub_self, max_self, mul_zero, sub_zero]
          rw [max_eq_left]
          nlinarith [mul_nonneg hβ.le (show 0 ≤ s - s' by linarith)]
    simp_rw [hrep]
    have hW : Measurable fun x => psiS α s (f x) :=
      measurable_const.sub (measurable_const.mul ((measurable_const.sub hf).max measurable_const))
    have hWb : ∀ x, |psiS α s (f x)| ≤ |s| + beta α * (|s| + C) := fun x => by
      have hx := abs_le.1 (hC x)
      have hm0 : 0 ≤ max (s - f x) 0 := le_max_right _ _
      have hm1 : max (s - f x) 0 ≤ |s| + C :=
        max_le (by linarith [le_abs_self s]) (by linarith [abs_nonneg s])
      unfold psiS
      rw [abs_le]; constructor <;> nlinarith [le_abs_self s, neg_abs_le s]
    exact variance_lipschitz_le P hW hWb (h := fun w => max w (s - beta α * (s - s')))
      (measurable_id.max measurable_const) fun a b => abs_max_sub_max_le_abs a b _
  · -- `(f̃ − s')₊ = min{(f − s')₊, s − s'}`
    have hrep : ∀ x, max (clip f s s' x - s') 0 = min (max (f x - s') 0) (s - s') := fun x => by
      unfold clip
      rcases le_total (f x) s' with h1 | h1
      · rw [max_eq_right h1, min_eq_left hs.le, sub_self, max_self,
          max_eq_right (by linarith : f x - s' ≤ 0), min_eq_left (by linarith : (0 : ℝ) ≤ s - s')]
      · rcases le_total (f x) s with h2 | h2
        · rw [max_eq_left h1, min_eq_left h2, max_eq_left (by linarith : 0 ≤ f x - s'),
            min_eq_left (by linarith : f x - s' ≤ s - s')]
        · rw [max_eq_left h1, min_eq_right h2, max_eq_left (by linarith : 0 ≤ s - s'),
            max_eq_left (by linarith : 0 ≤ f x - s'), min_eq_right (by linarith : s - s' ≤ f x - s')]
    simp_rw [hrep]
    have hW : Measurable fun x => max (f x - s') 0 := (hf.sub measurable_const).max measurable_const
    have hWb : ∀ x, |max (f x - s') 0| ≤ C + |s'| := fun x => by
      have := abs_le.1 (hC x)
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [neg_abs_le s']) (by linarith [abs_nonneg s'])
    refine variance_lipschitz_le Q hW hWb (h := fun w => min w (s - s'))
      (measurable_id.min measurable_const) fun a b => ?_
    have := abs_min_sub_min_le_max a (s - s') b (s - s')
    simpa using this

theorem lem2_4_route : Claims.lem2_4 := by
  intro 𝒳 _ P Q _ _ α f s s' hf ⟨C, hC⟩ _ hα1 hss
  have hβ := beta_pos hα1
  unfold theta
  rw [integral_psiS P hf hC, integral_upper Q hf hC]
  have h1 : 0 ≤ ∫ x, max (s - f x) 0 ∂P := integral_nonneg fun x => le_max_right _ _
  have h2 : 0 ≤ ∫ y, max (f y - s') 0 ∂Q := integral_nonneg fun x => le_max_right _ _
  refine ⟨?_, by linarith⟩
  nlinarith [mul_nonneg hβ.le h1, mul_nonneg hβ.le h2]

end StatFormal.Wave30tq
