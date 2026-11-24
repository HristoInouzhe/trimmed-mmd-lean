import StatFormal.Archive.Wave29f.Statements
import StatFormal.Archive.Wave24c.RouteCoverage
import StatFormal.Archive.Wave23b.RouteTransfer
import StatFormal.Archive.Wave23b.RoutePop

/-!
# Route — T `thm:coverage-error` with the representation discharged (untrusted)

`U := F(L_m X)` is measurable with `𝓛(U) = F#ν = μ`; the certified Wave 23b `pop_manifold` gives
`E_m Q(F(L_m X)) = X` a.s. The `μ`-a.e. bound on `Q` is made pointwise by replacing `Q` by `Q̂` on a measurable
`μ`-null set (`Q'`); the frozen Wave 24c `coverage_error` for `(U, Q')` gives an event `Ev₀`; removing a measurable
`P`-null set on which `X ≠ E_m Q(U)` or `Q'(U) ≠ Q(U)` gives the event for `X` with the same probability. Under
`ass:model` the rank pair is supplied by the certified Wave 23b `pop_hilbert`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave29f

open StatFormal.OTFD.Wave8c (IsRankPair)

theorem coverr_rank : Claims.coverr_rank := by
  intro H _ _ _ _ _ Tm V W M C Ω _ _ _ _ _ _ _ P X curve μ Ex D ι Em Lm Dr F Q Qhat tube A b Λ pbar δ
    hP hμ hX hcurve hEm hLm hDr hLE hXr hrank hQhat hA hδ hΛ hLB hLb hι hQb hQhatb htube hpA
  have hpm := StatFormal.Wave23b.pop_manifold H C (P.map X) μ Em Lm Dr F Q hEm hLm hDr hLE hXr hrank
  obtain ⟨hF, hQ, -, -, -, -⟩ := hrank
  -- the reference variable
  set U : Ω → H := fun ω => F (Lm (X ω)) with hUdef
  have hU : Measurable U := hF.comp (hLm.comp hX)
  have hUlaw : P.map U = μ := by
    rw [show U = (F ∘ Lm) ∘ X from rfl, ← Measure.map_map (hF.comp hLm) hX]
    exact hpm.1
  -- a pointwise-bounded version of `Q`
  set N : Set H := toMeasurable μ {u | ¬ ∀ t, ‖ι (Q u) t‖ ≤ b} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : μ N = 0 := by rw [hNdef, measure_toMeasurable]; exact hQb
  classical
  set Q' : H → H := fun u => if u ∈ N then Qhat u else Q u with hQ'def
  have hQ' : Measurable Q' := Measurable.ite hNm hQhat hQ
  have hQ'b : ∀ u t, ‖ι (Q' u) t‖ ≤ b := by
    intro u t
    by_cases hu : u ∈ N
    · simp only [hQ'def, hu, ↓reduceIte]; exact hQhatb u t
    · simp only [hQ'def, hu, ↓reduceIte]
      by_contra hc
      exact hu (subset_toMeasurable μ _ (fun h => hc (h t)))
  have hQ'ae : ∀ᵐ u ∂μ, Q' u = Q u := by
    have : ∀ᵐ u ∂μ, u ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
    filter_upwards [this] with u hu
    simp only [hQ'def, hu, ↓reduceIte]
  obtain ⟨Ev₀, hEv₀m, hEv₀, hbound⟩ :=
    StatFormal.Wave24c.coverage_error H Tm V W M Ω P U μ Ex D ι Q' Qhat tube A b Λ pbar δ hP hU hUlaw hQ'
      hQhat hA hδ hΛ hLB hLb hι hQ'b hQhatb htube hpA
  -- the a.s. representation
  have hrep : ∀ᵐ ω ∂P, X ω = Em (Q (U ω)) ∧ Q' (U ω) = Q (U ω) := by
    have h1 : ∀ᵐ ω ∂P, Em (Q (F (Lm (X ω)))) = X ω := ae_of_ae_map hX.aemeasurable hpm.2.2.1
    have h2 : ∀ᵐ ω ∂P, Q' (U ω) = Q (U ω) := ae_of_ae_map hU.aemeasurable (hUlaw ▸ hQ'ae)
    filter_upwards [h1, h2] with ω h1 h2
    exact ⟨h1.symm, h2⟩
  set N' : Set Ω := toMeasurable P {ω | ¬ (X ω = Em (Q (U ω)) ∧ Q' (U ω) = Q (U ω))} with hN'def
  have hN'm : MeasurableSet N' := measurableSet_toMeasurable _ _
  have hN'0 : P N' = 0 := by rw [hN'def, measure_toMeasurable]; exact hrep
  refine ⟨Ev₀ \ N', hEv₀m.diff hN'm, ?_, ?_⟩
  · rintro ω ⟨hω, hωN⟩ t
    have hgood : X ω = Em (Q (U ω)) ∧ Q' (U ω) = Q (U ω) := by
      by_contra hc
      exact hωN (subset_toMeasurable P _ hc)
    obtain ⟨y, hy, hd⟩ := hEv₀ ω hω t
    refine ⟨y, hy, ?_⟩
    rw [hgood.1, hcurve, ← hgood.2]
    exact hd
  · rw [measure_sdiff_null hN'0]
    have hint : ∫⁻ u, ‖Qhat u - Q' u‖ₑ ^ 2 ∂μ = ∫⁻ u, ‖Qhat u - Q u‖ₑ ^ 2 ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hQ'ae] with u hu
      rw [hu]
    rw [← hint]
    exact hbound

theorem coverr_model : Claims.coverr_model := by
  intro H _ _ _ _ _ _ Tm V W M C Ω _ _ _ _ _ _ _ P X curve μ Ex D ι Em Lm Dr B Bμ Λ
    hP hμ hX hcurve hEm hLm hDr hLE hXr hνnull hμnull hB hBμ hΛ hι hLB
  obtain ⟨F, Q, hrank, hgF, hgQ, -, -⟩ :=
    StatFormal.Wave23b.pop_hilbert H ((P.map X).map Lm) μ B Bμ hνnull hμnull hB hBμ
  refine ⟨F, Q, hrank, hgF, hgQ, ?_⟩
  intro Qhat tube A b pbar δ hQhat hA hδ hLb hQb hQhatb htube hpA
  exact coverr_rank H Tm V W M C Ω P X curve μ Ex D ι Em Lm Dr F Q Qhat tube A b Λ pbar δ hP hμ hX hcurve
    hEm hLm hDr hLE hXr hrank hQhat hA hδ hΛ hLB hLb hι hQb hQhatb htube hpA

/-- Fidelity check (new ⇒ old, critic 2026-10-20): on the objects of the frozen Wave 24c `coverage_error` — `U ∼ μ`,
`Q` with the `μ`-a.e. tangent bound, the represented trajectory `X := E_m Q(U)` — the new `coverr_rank` returns the frozen
conclusion (an event on which the curve `t ↦ Ex t (ι (Q U) t)` is in the expanded tube, with the frozen bound) as soon as
`(F, Q)` is a rank pair between `μ` and `Q#μ`, `Q(U) ∈ 𝒟_r` a.s. and `E_m Q(U) ∈ E_m(𝒟_r)` with `L_m E_m = id`. -/
theorem coverr_rank_gives_frozen (hnew : Claims.coverr_rank) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (Tm V W M C Ω : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [PseudoEMetricSpace M] [MeasurableSpace C] [MeasurableSpace Ω] (P : Measure Ω) (U : Ω → H)
    (μ : Measure H) (Ex : Tm → V → M) (D : Tm → V → V →L[ℝ] W) (ι : H →ₗ[ℝ] (Tm → V)) (Q Qhat : H → H)
    (tube : Tm → Set M) (A : Set H) (b Λ pbar δ : ℝ) (curve : C → Tm → M) (Em : H → C) (Lm : C → H)
    (Dr : Set H) (F : H → H)
    (hP : IsProbabilityMeasure P) (hU : Measurable U) (hUlaw : P.map U = μ) (hcurve : ∀ v t, curve (Em v) t = Ex t (ι v t))
    (hEm : Measurable Em) (hLm : Measurable Lm) (hDr : MeasurableSet Dr) (hLE : ∀ v ∈ Dr, Lm (Em v) = v)
    (hQDr : ∀ᵐ u ∂μ, Q u ∈ Dr)
    (hXr : ∀ᵐ x ∂(P.map fun ω => Em (Q (U ω))), Lm x ∈ Dr ∧ Em (Lm x) = x)
    (hrank : IsRankPair μ (μ.map Q) F Q) (hQhat : Measurable Qhat) (hA : MeasurableSet A) (hδ : 0 < δ)
    (hΛ : 0 ≤ Λ) (hLB : StatFormal.OTFD.Wave22b.LengthBound Ex D) (hLb : StatFormal.OTFD.Wave22b.Lb D b ≠ ⊤)
    (hι : ∀ x t, ‖ι x t‖ ≤ Λ * ‖x‖) (hQb : ∀ᵐ u ∂μ, ∀ t, ‖ι (Q u) t‖ ≤ b) (hQhatb : ∀ u t, ‖ι (Qhat u) t‖ ≤ b)
    (htube : ∀ u ∈ A, ∀ t, Ex t (ι (Qhat u) t) ∈ tube t) (hpA : ENNReal.ofReal pbar ≤ μ A) :
    ∃ Ev : Set Ω, MeasurableSet Ev ∧
      (∀ ω ∈ Ev, ∀ t, ∃ y ∈ tube t, edist (Ex t (ι (Q (U ω)) t)) y ≤ ENNReal.ofReal δ) ∧
      ENNReal.ofReal pbar - ENNReal.ofReal (((StatFormal.OTFD.Wave22b.Lb D b).toReal * Λ) ^ 2 / δ ^ 2) *
          ∫⁻ u, ‖Qhat u - Q u‖ₑ ^ 2 ∂μ ≤ P Ev := by
  have hμ : IsProbabilityMeasure μ := by rw [← hUlaw]; infer_instance
  have hQ : Measurable Q := hrank.2.1
  have hX : Measurable fun ω => Em (Q (U ω)) := hEm.comp (hQ.comp hU)
  have hlaw : (P.map fun ω => Em (Q (U ω))).map Lm = μ.map Q := by
    rw [Measure.map_map hLm hX, ← hUlaw, Measure.map_map hQ hU]
    refine Measure.map_congr ?_
    have h : ∀ᵐ ω ∂P, Q (U ω) ∈ Dr := ae_of_ae_map hU.aemeasurable (hUlaw ▸ hQDr)
    filter_upwards [h] with ω hω
    exact hLE _ hω
  obtain ⟨Ev, hEvm, hEv, hbd⟩ := hnew H Tm V W M C Ω P (fun ω => Em (Q (U ω))) curve μ Ex D ι Em Lm Dr F Q Qhat
    tube A b Λ pbar δ hP hμ hX hcurve hEm hLm hDr hLE hXr (hlaw ▸ hrank) hQhat hA hδ hΛ hLB hLb hι hQb hQhatb
    htube hpA
  refine ⟨Ev, hEvm, fun ω hω t => ?_, hbd⟩
  obtain ⟨y, hy, hd⟩ := hEv ω hω t
  exact ⟨y, hy, by rwa [hcurve] at hd⟩

end StatFormal.Wave29f
