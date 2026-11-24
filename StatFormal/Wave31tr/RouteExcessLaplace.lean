import StatFormal.Wave31tr.RouteExcess
import StatFormal.Lib.ExcessRamp.LaplacePotential

/-!
# Wave 31tr route (E1): Proposition 5.10 (iii), the Laplace kernel (untrusted)

* `laplace_green_route` (T42(d)): the library `ExcessRamp.laplace_green_identity` (fundamental theorem of calculus on the two
  half-lines) and `ExcessRamp.laplace_second_diff_le/eq`;
* `excess_laplace_route` (T42(a)–(c)), with no distribution theory: the witness is a positive multiple of the difference of
  the Laplace potentials of the closest parts, `U_{P′} − U_{Q′} = (1−α)‖a−b‖ f⋆` (`pot_eq`). `P′` does not charge `{f⋆ > t}`
  and `Q′` does not charge `{f⋆ < u}` (Lemma S4.17 (b)), so the library maximum principle `ExcessRamp.lapPot_max_principle`
  (a maximum point inside `{f⋆ > t}` and the discrete second difference) gives `u ≤ f⋆ ≤ t`. Then (b) is Lemma S4.18 with both
  overshoots `0`, and (c) is Lemma S4.17 (b): `P{f⋆ < t} = P′{f⋆ < t} ≤ 1 − α`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31tr.RouteExcess

open StatFormal.Wave30tq StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.ZeroSet StatFormal.ExcessRamp

/-! ### T42 (d) -/

theorem laplace_green_route : Claims.laplace_green := fun σ hσ =>
  ⟨fun _ hψ hc => laplace_green_identity hσ hψ hc, fun x y h hh =>
    ⟨laplace_second_diff_le hσ x y hh.le, fun hxy => laplace_second_diff_eq hσ x y hh.le hxy⟩⟩

/-! ### T42 (a)–(c) -/

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A feature map with the Laplace Gram function has unit norms. -/
lemma norm_le_one_of_gram {σ : ℝ} {φ : ℝ → H} (hgram : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) (x : ℝ) :
    ‖φ x‖ ≤ 1 := by
  have h : ‖φ x‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hgram, sub_self, abs_zero, neg_zero, zero_div, Real.exp_zero]
  nlinarith [norm_nonneg (φ x)]

/-- The Laplace potential of a closest part is `(1−α)⟪φ x, a⟫`. -/
lemma pot_part [CompleteSpace H] {σ : ℝ} {φ : ℝ → H} (hφ : StronglyMeasurable φ)
    (hgram : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) {P : Measure ℝ} [IsProbabilityMeasure P] {α : ℝ}
    (hα1 : α < 1) {g : ℝ → ℝ} (hg : IsTrimDensity P α g) (x : ℝ) :
    lapPot σ (trimMeasure P fun x => (1 - α) * g x) x = (1 - α) * ⟪φ x, ∫ y, g y • φ y ∂P⟫_ℝ := by
  unfold lapPot
  rw [show (fun y => Real.exp (-|x - y| / σ)) = fun y => ⟪φ x, φ y⟫_ℝ from funext fun y => (hgram x y).symm]
  exact inner_part hφ (norm_le_one_of_gram hgram) hα1 hg (φ x)

/-- Proposition 5.10 (iii), general form. -/
theorem laplace_G [CompleteSpace H] {σ : ℝ} {φ : ℝ → H} {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {α : ℝ} {a b : H} {t u : ℝ} (hσ : 0 < σ) (hφ : StronglyMeasurable φ)
    (hgram : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) (hα0 : 0 ≤ α) (hα1 : α < 1) (hD : 0 < Dpop φ P Q α)
    (ha : a ∈ region φ α P) (hb : b ∈ region φ α Q) (hab : ‖a - b‖ = Dpop φ P Q α)
    (ht : IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) t)
    (hu : IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α u) (hut : u < t) :
    (∀ x : ℝ, u ≤ ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ ∧ ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ ≤ t) ∧
      (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
          (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - α =
        (1 - α) * Dpop φ P Q α / (t - u) ∧
      α ≤ P.real {x | ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ = t} ∧
      α ≤ Q.real {y | ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ = u} := by
  have hκ := norm_le_one_of_gram hgram
  have hiden := identity_G hφ hκ hα0 hα1 hD ha hb hab ht hu hut
  obtain ⟨g, hgm, hgb, hgi, ha'⟩ := ha
  obtain ⟨h, hhm, hhb, hhi, hb'⟩ := hb
  have hg : IsTrimDensity P α g := ⟨hgm, hgb, hgi⟩
  have hh : IsTrimDensity Q α h := ⟨hhm, hhb, hhi⟩
  have hc0 : 0 < ‖a - b‖ := hab ▸ hD
  have haR : a ∈ region φ α P := ⟨g, hg.1, hg.2.1, hg.2.2, ha'⟩
  have hbR : b ∈ region φ α Q := ⟨h, hh.1, hh.2.1, hh.2.2, hb'⟩
  obtain ⟨hP1, hP2⟩ := part_threshold_P hφ hκ hα0 hα1 hD hg ha' hbR hab ht
  obtain ⟨hQ1, hQ2⟩ := part_threshold_Q hφ hκ hα0 hα1 hD hh hb' haR hab hu
  have hdiff := parts_inner_diff hφ hκ hα1 hg ha' hh hb' hc0
  set P' := trimMeasure P fun x => (1 - α) * g x with hP'
  set Q' := trimMeasure Q fun y => (1 - α) * h y with hQ'
  have := part_finite hα1 hg
  have := part_finite hα1 hh
  set c := ‖a - b‖ with hc
  set F : ℝ → ℝ := fun x => ⟪c⁻¹ • (a - b), φ x⟫_ℝ with hF
  have hK : 0 < (1 - α) * c := mul_pos (by linarith) hc0
  -- the witness is a multiple of the difference of the potentials
  have hpot : ∀ x, lapPot σ P' x - lapPot σ Q' x = (1 - α) * c * F x := fun x => by
    rw [pot_part hφ hgram hα1 hg x, pot_part hφ hgram hα1 hh x, ← ha', ← hb', ← mul_sub, ← inner_sub_right,
      real_inner_comm, inner_eq_norm_mul_dir hc0 (φ x)]
    simp only [hF]
    ring
  have hmass : P' univ = Q' univ := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P' univ), ← ENNReal.ofReal_toReal (measure_ne_top Q' univ)]
    have e1 := part_real_univ hα1 hg
    have e2 := part_real_univ hα1 hh
    rw [measureReal_def] at e1 e2
    rw [e1, e2]
  have hne : ∃ x, lapPot σ P' x ≠ lapPot σ Q' x := by
    by_contra hcon
    push Not at hcon
    have hF0 : ∀ x, F x = 0 := fun x => by
      have := hpot x
      rw [hcon x, sub_self] at this
      rcases mul_eq_zero.1 this.symm with h0 | h0
      · exact absurd h0 hK.ne'
      · exact h0
    have : (∫ x, F x ∂P') - ∫ y, F y ∂Q' = 0 := by simp only [hF0, integral_zero, sub_zero]
    rw [this] at hdiff
    linarith
  -- (a): the maximum principle on both sides
  have hup : ∀ x, F x ≤ t := by
    have hnull : P' {x | (1 - α) * c * t < lapPot σ P' x - lapPot σ Q' x} = 0 := by
      have : {x | (1 - α) * c * t < lapPot σ P' x - lapPot σ Q' x} = {x | t < F x} := by
        ext x; simp only [mem_ofPred_eq, hpot, mul_lt_mul_iff_right₀ hK]
      rw [this]; exact hP2
    intro x
    have := lapPot_max_principle hσ P' Q' hmass hne hnull x
    rw [hpot] at this
    exact le_of_mul_le_mul_left this hK
  have hlo : ∀ x, u ≤ F x := by
    have hne' : ∃ x, lapPot σ Q' x ≠ lapPot σ P' x := by
      obtain ⟨x, hx⟩ := hne; exact ⟨x, fun h' => hx h'.symm⟩
    have hpot' : ∀ x, lapPot σ Q' x - lapPot σ P' x = -((1 - α) * c * F x) := fun x => by
      rw [← hpot]; ring
    have hnull : Q' {x | -((1 - α) * c * u) < lapPot σ Q' x - lapPot σ P' x} = 0 := by
      have : {x | -((1 - α) * c * u) < lapPot σ Q' x - lapPot σ P' x} = {x | F x < u} := by
        ext x; simp only [mem_ofPred_eq, hpot', neg_lt_neg_iff, mul_lt_mul_iff_right₀ hK]
      rw [this]; exact hQ2
    intro x
    have := lapPot_max_principle hσ Q' P' hmass.symm hne' hnull x
    rw [hpot', neg_le_neg_iff] at this
    exact le_of_mul_le_mul_left this hK
  have hFm : Measurable F := measurable_wit hφ _
  refine ⟨fun x => ⟨hlo x, hup x⟩, ?_, ?_, ?_⟩
  · -- (b): both overshoots vanish
    rw [hiden]
    have h1 : ∫ x, max (u - F x) 0 ∂P = 0 := by
      have : (fun x => max (u - F x) 0) = fun _ => (0 : ℝ) := funext fun x => max_eq_right (by linarith [hlo x])
      rw [this, integral_zero]
    have h2 : ∫ y, max (F y - t) 0 ∂Q = 0 := by
      have : (fun y => max (F y - t) 0) = fun _ => (0 : ℝ) := funext fun y => max_eq_right (by linarith [hup y])
      rw [this, integral_zero]
    rw [h1, h2, add_zero, add_zero, StatFormal.Wave31ti.uPath]
  · -- (c) for `P`
    have hS : MeasurableSet {x | F x < t} := measurableSet_lt hFm measurable_const
    have hcompl : {x | F x = t} = {x | F x < t}ᶜ := by
      ext x; simp only [mem_ofPred_eq, mem_compl_iff]
      exact ⟨fun h' => by rw [h']; exact lt_irrefl t, fun h' => le_antisymm (hup x) (not_lt.1 h')⟩
    have hPS : P.real {x | F x < t} = P'.real {x | F x < t} := by
      have := congrArg (fun μ : Measure ℝ => μ univ) hP1
      simp only [Measure.restrict_apply_univ] at this
      rw [measureReal_def, measureReal_def, this]
    have hle : P'.real {x | F x < t} ≤ P'.real univ := measureReal_mono (subset_univ _)
    rw [part_real_univ hα1 hg] at hle
    change α ≤ P.real {x | F x = t}
    rw [hcompl, probReal_compl_eq_one_sub hS]
    linarith
  · -- (c) for `Q`
    have hS : MeasurableSet {x | u < F x} := measurableSet_lt measurable_const hFm
    have hcompl : {x | F x = u} = {x | u < F x}ᶜ := by
      ext x; simp only [mem_ofPred_eq, mem_compl_iff]
      exact ⟨fun h' => by rw [h']; exact lt_irrefl u, fun h' => le_antisymm (not_lt.1 h') (hlo x)⟩
    have hQS : Q.real {x | u < F x} = Q'.real {x | u < F x} := by
      have := congrArg (fun μ : Measure ℝ => μ univ) hQ1
      simp only [Measure.restrict_apply_univ] at this
      rw [measureReal_def, measureReal_def, this]
    have hle : Q'.real {x | u < F x} ≤ Q'.real univ := measureReal_mono (subset_univ _)
    rw [part_real_univ hα1 hh] at hle
    change α ≤ Q.real {x | F x = u}
    rw [hcompl, probReal_compl_eq_one_sub hS]
    linarith

theorem excess_laplace_route : Claims.excess_laplace := by
  refine ⟨?_, ?_⟩
  · intro H _ _ _ _ σ φ P Q _ _ α a b t u hσ hφ hgram hα0 hα1 hD ha hb hab ht hu hut
    exact laplace_G hσ hφ hgram hα0 hα1 hD ha hb hab ht hu hut
  · intro H _ _ _ _ σ φ P Q _ _ α a b t u hσ hφ hgram hchar _ htv1 hα0 hαtv ha hb hab ht hu
    have hκ := norm_le_one_of_gram hgram
    have hα1 : α < 1 := hαtv.trans htv1
    have hD := dpop_pos_of_lt_tv hφ hκ hchar hα0 hα1 hαtv
    have hut : u < t := by linarith [pop_gap hφ hκ hα0 hα1 ha hb hab hD ht hu]
    exact laplace_G hσ hφ hgram hα0 hα1 hD ha hb hab ht.1 hu.1 hut

end StatFormal.Wave31tr.RouteExcess
