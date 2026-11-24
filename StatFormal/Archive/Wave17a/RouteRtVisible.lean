import StatFormal.Archive.Wave17a.Statements

/-!
# Route: otfd A `lem:rt-visible` (untrusted)

`Π_{K'}` factors through `Π_K` for `K' ≤ K`. If every projection agrees, the partial sums
`S_K x = Σ_{k<K} ⟨e_k, x⟩ e_k = L_K(Π_K x)` converge to `x` (Hilbert basis), so dominated convergence gives
`∫ f dP = ∫ f dQ` for every bounded continuous `f`, hence `P = Q`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave17a

lemma continuous_projK {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (b : HilbertBasis ℕ ℝ H)
    (K : ℕ) : Continuous (projK b K) := by
  unfold projK
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => continuous_const.inner continuous_id)

theorem rt_visible_initial : Claims.rt_visible_initial := by
  intro H _ _ _ _ b P Q K K' hK h
  let r : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K') :=
    fun y => WithLp.toLp 2 fun k => (WithLp.ofLp y) (Fin.castLE hK k)
  have hr : Continuous r :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      (continuous_apply (Fin.castLE hK k)).comp (PiLp.continuous_ofLp 2 _))
  have hcomp : projK b K' = r ∘ projK b K := by
    funext x
    rfl
  have hp := (continuous_projK b K).measurable
  rw [hcomp, ← Measure.map_map hr.measurable hp, ← Measure.map_map hr.measurable hp, h]

theorem rt_visible : Claims.rt_visible := by
  intro H _ _ _ _ _ b P Q hP hQ hne
  by_contra hcon
  push Not at hcon
  have hall : ∀ K, P.map (projK b K) = Q.map (projK b K) := fun K => by
    obtain ⟨K', hK', h⟩ := hcon K
    exact rt_visible_initial H b P Q K' K hK' h
  apply hne
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let S : ℕ → H → H := fun K x => ∑ i ∈ Finset.range K, ⟪b i, x⟫ • b i
  have hS : ∀ x, Tendsto (fun K => S K x) atTop (𝓝 x) := fun x => by
    have := (b.hasSum_repr x).tendsto_sum_nat
    simpa [HilbertBasis.repr_apply_apply] using this
  have hScont : ∀ K, Continuous (S K) := fun K =>
    continuous_finsetSum _ fun i _ => (continuous_const.inner continuous_id).smul continuous_const
  have hint : ∀ μ : Measure H, IsProbabilityMeasure μ →
      Tendsto (fun K => ∫ x, f (S K x) ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    intro μ _
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖) ?_ (integrable_const _) ?_ ?_
    · intro K; exact (f.continuous.comp (hScont K)).aestronglyMeasurable
    · intro K; exact ae_of_all _ fun x => f.norm_coe_le_norm _
    · exact ae_of_all _ fun x => (f.continuous.tendsto x).comp (hS x)
  have heq : ∀ K, ∫ x, f (S K x) ∂P = ∫ x, f (S K x) ∂Q := by
    intro K
    let L : EuclideanSpace ℝ (Fin K) → H := fun y => ∑ i : Fin K, (WithLp.ofLp y i) • b i
    have hL : Continuous L :=
      continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).smul continuous_const
    have hSL : ∀ x, S K x = L (projK b K x) := by
      intro x
      simp only [S, L, projK]
      rw [Finset.sum_range (fun i => ⟪b i, x⟫ • b i)]
    simp_rw [hSL]
    have hp := (continuous_projK b K).measurable
    have h1 := integral_map (μ := P) hp.aemeasurable (f.continuous.comp hL).aestronglyMeasurable
    have h2 := integral_map (μ := Q) hp.aemeasurable (f.continuous.comp hL).aestronglyMeasurable
    simp only [Function.comp] at h1 h2
    rw [← h1, ← h2, hall K]
  have hP' := hint P hP
  simp_rw [heq] at hP'
  exact tendsto_nhds_unique hP' (hint Q hQ)

end StatFormal.Wave17a
