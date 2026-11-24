import StatFormal.Archive.OTFD.Wave22a.Statements

/-!
# Route — otfd A `thm:rt-fixedK`, `prop:rt-lift`(ii), `thm:rt-coherent` (`Λ ∈ 𝒫^ℓ`) (untrusted)

* rank laws: if `F` is injective on a measurable `S` carrying `P` and `Q`, then `P(A) = P(A ∩ S) = (F#P)(F(A ∩ S))`
  with `F(A ∩ S)` measurable by Lusin–Souslin, so `F#P = F#Q` forces `P = Q`;
* lifts: the lift is injective on `{x_K ∈ S_K} ∩ ⋂_j {x_j ∈ I_j}`, a `Λ`-conull set;
* `Λ ∈ 𝒫^ℓ`: masses, second moments and null sets are additive in the measure.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.OTFD.Wave22a

open StatFormal.OTFD.Wave1 (PellClass)

lemma mix_null {X : Type*} [MeasurableSpace X] {θ : ℝ} {P Q : Measure X} (hθ : 0 < θ) (hθ1 : θ < 1)
    {A : Set X} (h : mix θ P Q A = 0) : P A = 0 ∧ Q A = 0 := by
  simp only [mix, Measure.add_apply, Measure.smul_apply, smul_eq_mul, add_eq_zero, mul_eq_zero,
    ENNReal.ofReal_eq_zero, not_le.mpr hθ, false_or, not_le.mpr (sub_pos.mpr hθ1)] at h
  exact h

lemma map_eq_on_image {E Y : Type*} [MeasurableSpace E] [StandardBorelSpace E] [MeasurableSpace Y]
    [MeasurableSpace.CountablySeparated Y] {ν : Measure E} {F : E → Y} {S : Set E} (hF : Measurable F)
    (hS : MeasurableSet S) (hinj : InjOn F S) (hν : ν Sᶜ = 0) {A : Set E} (hA : MeasurableSet A) :
    ν A = ν.map F (F '' (A ∩ S)) := by
  have hM : MeasurableSet (F '' (A ∩ S)) :=
    (hA.inter hS).image_of_measurable_injOn hF (hinj.mono inter_subset_right)
  rw [Measure.map_apply hF hM, ← measure_inter_conull (s := F ⁻¹' (F '' (A ∩ S))) hν,
    ← measure_inter_conull (s := A) hν]
  congr 1
  ext x
  constructor
  · rintro ⟨hxA, hxS⟩
    exact ⟨⟨x, ⟨hxA, hxS⟩, rfl⟩, hxS⟩
  · rintro ⟨⟨y, ⟨hyA, hyS⟩, hxy⟩, hxS⟩
    exact ⟨hinj hyS hxS hxy ▸ hyA, hxS⟩

lemma laws_iff_of_injOn {E Y : Type*} [MeasurableSpace E] [StandardBorelSpace E] [MeasurableSpace Y]
    [MeasurableSpace.CountablySeparated Y] {P Q : Measure E} {θ : ℝ} {F : E → Y} {S : Set E}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hF : Measurable F) (hS : MeasurableSet S) (hnull : mix θ P Q Sᶜ = 0)
    (hinj : InjOn F S) : P.map F = Q.map F ↔ P = Q := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  obtain ⟨hP, hQ⟩ := mix_null hθ hθ1 hnull
  ext A hA
  rw [map_eq_on_image hF hS hinj hP hA, map_eq_on_image hF hS hinj hQ hA, h]

theorem rt_fixedK_laws : Claims.rt_fixedK_laws := by
  intro E Y _ _ _ _ P Q _ _ θ F S hθ hθ1 hF hS hnull hinj
  exact laws_iff_of_injOn hθ hθ1 hF hS hnull hinj

lemma continuous_headT {K m : ℕ} : Continuous (headT (K := K) (m := m)) := by
  unfold headT
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => (PiLp.continuous_apply 2 _ _))

lemma measurable_liftMap {K m : ℕ} {FK : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)}
    {t : Fin m → ℝ → ℝ} (hFK : Measurable FK) (ht : ∀ j, Measurable (t j)) :
    Measurable (liftMap FK t) := by
  unfold liftMap
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr fun i => ?_)
  rcases i with k | j
  · exact (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp
      (hFK.comp continuous_headT.measurable))
  · exact (ht j).comp ((measurable_pi_apply (Sum.inr j)).comp (WithLp.measurable_ofLp 2 _))

theorem rt_lift_laws : Claims.rt_lift_laws := by
  intro K m P Q _ _ θ FK SK t I hθ hθ1 hFK hSK hinjK hnullK ht hI hinjI hnullI
  set S : Set (EuclideanSpace ℝ (Fin K ⊕ Fin m)) :=
    {x | headT x ∈ SK} ∩ ⋂ j, {x | x (Sum.inr j) ∈ I j}
  have hmeasj : ∀ j, Measurable fun x : EuclideanSpace ℝ (Fin K ⊕ Fin m) => x (Sum.inr j) :=
    fun j => (measurable_pi_apply (Sum.inr j)).comp (WithLp.measurable_ofLp 2 _)
  have hS : MeasurableSet S :=
    (continuous_headT.measurable hSK).inter (MeasurableSet.iInter fun j => hmeasj j (hI j))
  have hnull : mix θ P Q Sᶜ = 0 := by
    simp only [S, compl_inter, compl_iInter]
    refine measure_union_null ?_ (measure_iUnion_null fun j => ?_)
    · exact hnullK
    · exact hnullI j
  have hinj : InjOn (liftMap FK t) S := by
    intro x hx x' hx' hxx
    have hc : ∀ i, liftMap FK t x i = liftMap FK t x' i := fun i => by rw [hxx]
    have hhead : FK (headT x) = FK (headT x') := by
      ext k; simpa [liftMap] using hc (Sum.inl k)
    have hh := hinjK hx.1 hx'.1 hhead
    ext i
    rcases i with k | j
    · have := congrArg (fun z => z k) hh
      simpa [headT] using this
    · have hj := hc (Sum.inr j)
      simp only [liftMap, PiLp.toLp_apply, Sum.elim_inr] at hj
      exact hinjI j (mem_iInter.mp hx.2 j) (mem_iInter.mp hx'.2 j) hj
  exact laws_iff_of_injOn hθ hθ1 (measurable_liftMap hFK ht) hS hnull hinj

theorem rt_coherent_pell : Claims.rt_coherent_pell := by
  intro H _ _ _ P Q θ hθ hθ1 hP hQ
  obtain ⟨hPp, hP2, hPl⟩ := hP
  obtain ⟨hQp, hQ2, hQl⟩ := hQ
  refine ⟨⟨?_⟩, ?_, fun S hS => ?_⟩
  · simp only [mix, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hθ.le (sub_pos.mpr hθ1).le]
    simp
  · simp only [mix]
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hP2,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQ2⟩
  · simp [mix, hPl S hS, hQl S hS]

end StatFormal.OTFD.Wave22a
