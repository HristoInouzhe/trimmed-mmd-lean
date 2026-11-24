import StatFormal.Wave30tv.Statements
import StatFormal.Wave30tq.RouteBetting
import StatFormal.Lib.Betting.Predictable

/-!
# Wave 30tv route: functions of a set of coordinates, and the freezing lemma (untrusted)

On `Ω = 𝒳^n × 𝒳^m` under `P^{⊗n} ⊗ Q^{⊗m}` (coordinates indexed by `Fin n ⊕ Fin m`, 30tq `coord`):

* `DepOn C F`: `F` depends only on the coordinates in `C`;
* `depOn_of_measurable`: a `σ(coordinates in C)`-measurable real function depends only on them (the sets that are
  saturated for "agree on `C`" form a σ-algebra containing the generators);
* `measurable_coordSigma_of_depOn`: conversely, a measurable function that depends only on `C` is
  `σ(coordinates in C)`-measurable (it factors through `resetOut C ω₀`, which resets the other coordinates);
* `integral_mul_coord` (**freezing**): if `V` and the random function `G` depend only on `C` and `j ∉ C`, then
  `E[V G(X_j)] = E[V ∫ G dLaw(X_j)]` (independence of `resetOut C ω₀` and `X_j`, and Fubini).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.Wave30tv

open StatFormal.Wave30tq

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {n m : ℕ}

/-- `F` depends only on the coordinates in `C`. -/
def DepOn {β : Type*} (C : Set (Fin n ⊕ Fin m)) (F : (Fin n → 𝒳) × (Fin m → 𝒳) → β) : Prop :=
  ∀ ω ω', (∀ j ∈ C, coord j ω = coord j ω') → F ω = F ω'

omit [MeasurableSpace 𝒳] in
lemma DepOn.mono {β : Type*} {C D : Set (Fin n ⊕ Fin m)} {F : (Fin n → 𝒳) × (Fin m → 𝒳) → β}
    (h : DepOn C F) (hCD : C ⊆ D) : DepOn D F :=
  fun ω ω' hω => h ω ω' fun j hj => hω j (hCD hj)

/-- The σ-algebra of sets saturated for "agree on the coordinates in `C`". -/
@[instance_reducible] def satSigma (C : Set (Fin n ⊕ Fin m)) : MeasurableSpace ((Fin n → 𝒳) × (Fin m → 𝒳)) where
  MeasurableSet' S := ∀ ω ω', (∀ j ∈ C, coord j ω = coord j ω') → (ω ∈ S ↔ ω' ∈ S)
  measurableSet_empty := fun _ _ _ => Iff.rfl
  measurableSet_compl S hS ω ω' h := not_congr (hS ω ω' h)
  measurableSet_iUnion f hf ω ω' h := by
    simp only [Set.mem_iUnion]
    exact exists_congr fun i => hf i ω ω' h

lemma coordSigma_le_satSigma (C : Set (Fin n ⊕ Fin m)) :
    coordSigma (𝒳 := 𝒳) C ≤ satSigma C := by
  refine iSup₂_le fun j hj => ?_
  rintro S ⟨T, -, rfl⟩ ω ω' h
  simp only [Set.mem_preimage, h j hj]

/-- A `σ(coordinates in C)`-measurable real function depends only on the coordinates in `C`. -/
lemma depOn_of_measurable {C : Set (Fin n ⊕ Fin m)} {V : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ}
    (hV : Measurable[coordSigma C] V) : DepOn C V := by
  intro ω ω' h
  have hS : MeasurableSet[coordSigma C] (V ⁻¹' {V ω}) := hV (measurableSet_singleton _)
  have := (coordSigma_le_satSigma C _ hS ω ω' h).1 rfl
  exact (Set.mem_singleton_iff.1 this).symm

open Classical in
/-- Keep the coordinates in `C`, reset the others to those of `ω₀`. -/
def resetOut (C : Set (Fin n ⊕ Fin m)) (ω₀ ω : (Fin n → 𝒳) × (Fin m → 𝒳)) : (Fin n → 𝒳) × (Fin m → 𝒳) :=
  (fun i => if Sum.inl i ∈ C then ω.1 i else ω₀.1 i, fun j => if Sum.inr j ∈ C then ω.2 j else ω₀.2 j)

omit [MeasurableSpace 𝒳] in
lemma coord_resetOut {C : Set (Fin n ⊕ Fin m)} {ω₀ ω : (Fin n → 𝒳) × (Fin m → 𝒳)} {j : Fin n ⊕ Fin m}
    (hj : j ∈ C) : coord j (resetOut C ω₀ ω) = coord j ω := by
  cases j with
  | inl i => simp [coord, resetOut, hj]
  | inr i => simp [coord, resetOut, hj]

lemma measurable_resetOut (C : Set (Fin n ⊕ Fin m)) (ω₀ : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    Measurable[coordSigma C] (resetOut C ω₀) := by
  refine Measurable.prodMk ?_ ?_
  · refine @Measurable.of_eval _ _ _ (coordSigma C) _ _ fun i => ?_
    by_cases h : Sum.inl i ∈ C
    · simp only [resetOut, h, ite_true]
      exact measurable_coord_sigma (𝒳 := 𝒳) h
    · simp only [resetOut, h, ite_false]
      exact measurable_const
  · refine @Measurable.of_eval _ _ _ (coordSigma C) _ _ fun i => ?_
    by_cases h : Sum.inr i ∈ C
    · simp only [resetOut, h, ite_true]
      exact measurable_coord_sigma (𝒳 := 𝒳) h
    · simp only [resetOut, h, ite_false]
      exact measurable_const

lemma resetOut_eq {β : Type*} {C : Set (Fin n ⊕ Fin m)} {F : (Fin n → 𝒳) × (Fin m → 𝒳) → β}
    (hF : DepOn C F) (ω₀ ω : (Fin n → 𝒳) × (Fin m → 𝒳)) : F (resetOut C ω₀ ω) = F ω :=
  hF _ _ fun _ hj => coord_resetOut hj

/-- A measurable function that depends only on the coordinates in `C` is `σ(coordinates in C)`-measurable. -/
lemma measurable_coordSigma_of_depOn {β : Type*} [MeasurableSpace β] {C : Set (Fin n ⊕ Fin m)}
    {F : (Fin n → 𝒳) × (Fin m → 𝒳) → β} (hFm : Measurable F) (hF : DepOn C F) :
    Measurable[coordSigma C] F := by
  rcases isEmpty_or_nonempty ((Fin n → 𝒳) × (Fin m → 𝒳)) with h | ⟨⟨ω₀⟩⟩
  · intro s _
    rw [Set.eq_empty_of_isEmpty (F ⁻¹' s)]
    exact (coordSigma C).measurableSet_empty
  · have : F = F ∘ resetOut C ω₀ := funext fun ω => (resetOut_eq hF ω₀ ω).symm
    rw [this]
    intro s hs
    exact measurable_resetOut C ω₀ (hFm hs)

/-- The law of coordinate `j`: `P` for an `X`, `Q` for a `Y`. -/
def coordLaw (P Q : Measure 𝒳) : Fin n ⊕ Fin m → Measure 𝒳 := Sum.elim (fun _ => P) (fun _ => Q)

instance coordLaw_isProb (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (j : Fin n ⊕ Fin m) : IsProbabilityMeasure (coordLaw (n := n) (m := m) P Q j) := by
  cases j with
  | inl i => simp only [coordLaw, Sum.elim_inl]; infer_instance
  | inr i => simp only [coordLaw, Sum.elim_inr]; infer_instance

lemma map_coord (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (j : Fin n ⊕ Fin m) :
    ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)).map (coord j) =
      coordLaw P Q j := by
  cases j with
  | inl i =>
    have h : coord (𝒳 := 𝒳) (n := n) (m := m) (Sum.inl i) = (fun x : Fin n → 𝒳 => x i) ∘ Prod.fst := rfl
    rw [h, ← Measure.map_map (measurable_pi_apply i) measurable_fst, Measure.map_fst_prod, measure_univ,
      one_smul, (measurePreserving_eval (fun _ : Fin n => P) i).map_eq]
    rfl
  | inr i =>
    have h : coord (𝒳 := 𝒳) (n := n) (m := m) (Sum.inr i) = (fun x : Fin m → 𝒳 => x i) ∘ Prod.snd := rfl
    rw [h, ← Measure.map_map (measurable_pi_apply i) measurable_snd, Measure.map_snd_prod, measure_univ,
      one_smul, (measurePreserving_eval (fun _ : Fin m => Q) i).map_eq]
    rfl

lemma indepFun_resetOut_coord (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {C : Set (Fin n ⊕ Fin m)} {j : Fin n ⊕ Fin m} (hj : j ∉ C) (ω₀ : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    IndepFun (resetOut C ω₀) (coord j) ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) := by
  have hI := (iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_coord (n := n) (m := m) P Q)
  have hdisj : Disjoint C {j} := Set.disjoint_singleton_right.2 hj
  have H := indep_iSup_of_disjoint (fun j => (measurable_coord (𝒳 := 𝒳) j).comap_le) hI hdisj
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left H (measurable_resetOut C ω₀).comap_le) ?_
  exact le_iSup₂ (f := fun i (_ : i ∈ ({j} : Set (Fin n ⊕ Fin m))) =>
    MeasurableSpace.comap (coord (𝒳 := 𝒳) i) inferInstance) j rfl

/-- **Freezing**: if `V` and the random function `G` depend only on the coordinates in `C` and `j ∉ C`, then
`E[V · G(X_j)] = E[V · ∫ G d(law of X_j)]`. -/
lemma integral_mul_coord (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {C : Set (Fin n ⊕ Fin m)} {j : Fin n ⊕ Fin m} (hj : j ∉ C)
    {V : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ} (hVm : Measurable V) (hVd : DepOn C V) {K : ℝ}
    (hVb : ∀ ω, |V ω| ≤ K)
    {G : (Fin n → 𝒳) × (Fin m → 𝒳) → 𝒳 → ℝ} (hGm : Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => G p.1 p.2)
    (hGd : DepOn C G) (hGb : ∀ ω t, |G ω t| ≤ 1) :
    ∫ ω, V ω * G ω (coord j ω) ∂((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) =
      ∫ ω, V ω * ∫ t, G ω t ∂(coordLaw P Q j)
        ∂((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) := by
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hF : Measurable (resetOut C ω₀) := (measurable_resetOut C ω₀).mono (coordSigma_le C) le_rfl
  have hind := indepFun_resetOut_coord P Q hj ω₀
  have hmap : μ.map (fun ω => (resetOut C ω₀ ω, coord j ω)) =
      (μ.map (resetOut C ω₀)).prod (coordLaw P Q j) := by
    rw [← map_coord P Q j]
    exact (indepFun_iff_map_prod_eq_prod_map_map hF.aemeasurable (measurable_coord j).aemeasurable).1 hind
  set Φ : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 → ℝ := fun p => V p.1 * G p.1 p.2 with hΦ
  have hΦm : Measurable Φ := (hVm.comp measurable_fst).mul hGm
  have h1 : ∫ ω, V ω * G ω (coord j ω) ∂μ = ∫ ω, Φ (resetOut C ω₀ ω, coord j ω) ∂μ := by
    congr 1; funext ω
    simp only [hΦ]
    rw [resetOut_eq hVd, resetOut_eq hGd]
  have hΦint : Integrable Φ ((μ.map (resetOut C ω₀)).prod (coordLaw P Q j)) := by
    refine Integrable.of_bound hΦm.aestronglyMeasurable (K * 1) (ae_of_all _ fun p => ?_)
    simp only [hΦ, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hVb p.1) (hGb p.1 p.2) (abs_nonneg _) ((abs_nonneg _).trans (hVb p.1))
  rw [h1, ← integral_map (hF.prodMk (measurable_coord j)).aemeasurable hΦm.aestronglyMeasurable, hmap,
    integral_prod Φ hΦint]
  simp only [hΦ, integral_const_mul]
  have hmeas2 : Measurable fun ω' => V ω' * ∫ t, G ω' t ∂(coordLaw P Q j) :=
    hVm.mul (hGm.stronglyMeasurable.integral_prod_right' (ν := coordLaw P Q j)).measurable
  rw [integral_map hF.aemeasurable hmeas2.aestronglyMeasurable]
  congr 1; funext ω
  rw [resetOut_eq hVd, resetOut_eq hGd]

end StatFormal.Wave30tv
