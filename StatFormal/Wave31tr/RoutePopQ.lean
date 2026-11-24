import StatFormal.Wave31tr.Statements
import StatFormal.Wave30tj.RouteLowerTrim
import StatFormal.Wave31tb.RouteSeparated
import StatFormal.Lib.ExcessRamp.Quantile
import StatFormal.Lib.TVFacts.FiniteSupport

/-!
# Wave 31tr, chunk E2: the bathtub cuts are exactly the quantiles (T37); finite support violates (Q) (T47(b)) (untrusted)

* `bathtub_quantiles_route` (T37): (a) push `R` forward by `f` (a law on `[−C, C]`); the certified `Wave30tj.lowertrim_shape` says
  the maximisers of `s ↦ ∫ψ_s d(f#R)` are exactly the `s` with `f#R(−∞,s) ≤ 1−α ≤ f#R(−∞,s]`; (b) from (a) applied to `−f`
  (`u` minimizes `u + βE(f−u)₊` iff `−u` maximizes `s − βE(s+f)₊`) and `ExcessRamp.quantile_iff_neg`;
* `finite_support_not_qdens_route` (T47(b)): `TVFacts.exists_null_preimage_pos_density` (the interval minus the finite image);
* `margin_without_qdens_route` (T47(b), existence): the certified `Wave31tb.separated` on `Fin 3` with the basis feature map and
  `f = e₁ − e₂` (`c₀ = 2/‖f‖`), and the first half.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr.RoutePop

open StatFormal.Wave30tq

/-! ### T37 -/

/-- Part (a) of T37 for one bounded measurable function. -/
theorem bathtub_max_iff {𝒳 : Type*} [MeasurableSpace 𝒳] (R : Measure 𝒳) [IsProbabilityMeasure R] {f : 𝒳 → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (t : ℝ) :
    IsMaxOn (fun s : ℝ => s - 1 / (1 - α) * ∫ x, max (s - f x) 0 ∂R) univ t ↔ IsQuantileAt R f (1 - α) t := by
  set F := R.map f with hF
  have hFC : F (Icc (-C) C) = 1 := by
    rw [hF, Measure.map_apply hf measurableSet_Icc]
    have : f ⁻¹' Icc (-C) C = univ := eq_univ_of_forall fun x => abs_le.1 (hC x)
    rw [this, measure_univ]
  have hshape := (StatFormal.Wave30tj.lowertrim_shape F C α hFC hα0 hα1).2.2.2 t
  have hfun : (fun s => ∫ u, StatFormal.Wave30tj.psi α s u ∂F) =
      (fun s : ℝ => s - 1 / (1 - α) * ∫ x, max (s - f x) 0 ∂R) := by
    funext s
    have hpm : Measurable fun u : ℝ => StatFormal.Wave30tj.psi α s u := by
      unfold StatFormal.Wave30tj.psi
      exact measurable_const.sub (measurable_const.mul ((measurable_const.sub measurable_id).max measurable_const))
    rw [hF, integral_map hf.aemeasurable hpm.aestronglyMeasurable]
    simp only [StatFormal.Wave30tj.psi]
    have hint : Integrable (fun x => max (s - f x) 0) R :=
      Integrable.of_mem_Icc 0 (|s| + |C|) ((measurable_const.sub hf).max measurable_const).aemeasurable
        (ae_of_all _ fun x => ⟨le_max_right _ _, max_le (by linarith [le_abs_self s, neg_abs_le (f x), hC x, le_abs_self C])
          (by positivity)⟩)
    rw [integral_sub (integrable_const s) (hint.const_mul _), integral_const, probReal_univ, one_smul,
      integral_const_mul, one_div]
  rw [← hfun, hshape, map_measureReal_apply hf measurableSet_Iio, map_measureReal_apply hf measurableSet_Iic]
  rfl

theorem bathtub_quantiles_route : Claims.bathtub_quantiles := by
  intro 𝒳 _ R _ f α hf ⟨C, hC⟩ hα0 hα1
  refine ⟨fun t => bathtub_max_iff R hf hC hα0 hα1 t, fun u => ?_⟩
  have hnf : Measurable fun x => -f x := hf.neg
  have hnC : ∀ x, |-f x| ≤ C := fun x => by rw [abs_neg]; exact hC x
  have ha := bathtub_max_iff R hnf hnC hα0 hα1 (-u)
  set U : ℝ → ℝ := fun s => s + 1 / (1 - α) * ∫ x, max (f x - s) 0 ∂R with hU
  set T : ℝ → ℝ := fun s => s - 1 / (1 - α) * ∫ x, max (s - -f x) 0 ∂R with hT
  have key : ∀ v, T (-v) = -U v := by
    intro v
    simp only [hT, hU]
    have : (fun x => max (-v - -f x) 0) = fun x => max (f x - v) 0 := by
      funext x; congr 1; ring
    rw [this]; ring
  have hmin : IsMinOn U univ u ↔ IsMaxOn T univ (-u) := by
    simp only [isMinOn_iff, isMaxOn_iff, mem_univ, true_imp_iff]
    constructor
    · intro h s
      have := h (-s)
      rw [show s = -(-s) by ring, key (-s), key u]
      linarith
    · intro h v
      have := h (-v)
      rw [key v, key u] at this
      linarith
  rw [hmin, ha]
  exact (StatFormal.ExcessRamp.quantile_iff_neg R hf α u).symm

/-! ### T47 (b) -/

theorem finite_support_not_qdens_route : Claims.finite_support_not_qdens := by
  intro 𝒳 _ _ P _ S f t r c C _ hS hr hc ⟨g, hg, hgb, hPA⟩
  obtain ⟨A, hA, hAI, hP0, hpos⟩ :=
    TVFacts.exists_null_preimage_pos_density P S hS f hr hc hg fun s hs => (hgb s hs).1
  have h := hPA A hA hAI
  rw [hP0] at h
  exact hpos.ne' h.symm

theorem margin_without_qdens_route : Claims.margin_without_qdens := by
  set e : Fin 3 → EuclideanSpace ℝ (Fin 3) := fun i => EuclideanSpace.single i (1 : ℝ) with he
  set P : Measure (Fin 3) := (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1 with hP
  set Q : Measure (Fin 3) := (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 2 with hQ
  have h12 : ENNReal.ofReal (1 / 2) = 1 / 2 := by
    rw [ENNReal.ofReal_div_of_pos two_pos]; simp
  have h12' : ENNReal.ofReal (1 - 1 / 2) = 1 / 2 := by norm_num [h12]
  have hφ : StronglyMeasurable e := StronglyMeasurable.of_discrete
  have hκ : ∀ i, ‖e i‖ ≤ 1 := fun i => by simp [he]
  have hd : ∀ i j : Fin 3, i ≠ j → Disjoint ({i} : Set (Fin 3)) {j} := fun i j hij => Set.disjoint_singleton.2 hij
  have hsep := StatFormal.Wave31tb.separated (Fin 3) (EuclideanSpace ℝ (Fin 3)) e 1 (Measure.dirac 0) (Measure.dirac 1)
    (Measure.dirac 2) P Q {0} {1} {2} (1 / 2) hφ hκ (measurableSet_singleton _) (measurableSet_singleton _)
    (measurableSet_singleton _) (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide)) (by simp) (by simp) (by simp)
    (by norm_num) (by norm_num) (by rw [h12', h12]) (by rw [h12', h12])
  set v : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 1 (1 : ℝ) - EuclideanSpace.single 2 (1 : ℝ) with hv
  have hinner : ∀ i : Fin 3, ⟪v, e i⟫_ℝ = v i := fun i => by
    simp [he, EuclideanSpace.inner_single_right]
  have hv0 : v 0 = 0 := by simp [hv, PiLp.single_apply]
  have hv1 : v 1 = 1 := by simp [hv, PiLp.single_apply]
  have hv2 : v 2 = -1 := by simp [hv, PiLp.single_apply]
  obtain ⟨-, hf⟩ := hsep
  obtain ⟨-, -, -, hpoly⟩ := hf v
    (fun x hx => by rw [mem_singleton_iff] at hx; subst hx; rw [hinner, hv0])
    (fun x hx => by rw [mem_singleton_iff] at hx; subst hx; rw [hinner, hv1])
    (fun x hx => by rw [mem_singleton_iff] at hx; subst hx; rw [hinner, hv2])
  have : IsProbabilityMeasure P := ⟨by simp [hP, ENNReal.inv_two_add_inv_two]⟩
  refine ⟨2 / ‖v‖, hpoly.1, ⟨hpoly.1, le_rfl, hpoly.2⟩, ?_⟩
  intro f t r c C hr hc
  exact finite_support_not_qdens_route (Fin 3) P Finset.univ f t r c C Measurable.of_discrete (by simp) hr hc

end StatFormal.Wave31tr.RoutePop
