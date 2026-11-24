import StatFormal.Archive.Wave24a.Statements

/-!
# Route — TM `lem:tcompact` (untrusted)

`A(t) = t + (1−α)⁻¹ ∫ (f − t)_+ dR` is Lipschitz (each `t ↦ (f x − t)_+` is `1`-Lipschitz), equals `t` on
`[κ, ∞)` and `t + (1−α)⁻¹(∫ f − t)` on `(−∞, −κ]`, where `A(t) − A(−κ) = (t + κ)(1 − (1−α)⁻¹) ≥ 0`. A minimiser
of `A` on the compact `[−κ, κ]` is therefore global. No convexity or derivative is needed.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave24a

section
variable {X : Type*} [MeasurableSpace X] {R : Measure X} [IsProbabilityMeasure R] {f : X → ℝ} {κ : ℝ}

lemma integrable_pos_part (hf : Measurable f) (hκ : ∀ x, |f x| ≤ κ) (t : ℝ) :
    Integrable (fun x => max (f x - t) 0) R := by
  refine Integrable.of_bound (C := |κ| + |t|) ((hf.sub_const t).max measurable_const).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have h1 := hκ x
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  refine max_le ?_ (by positivity)
  have := abs_le.1 h1
  have := le_abs_self κ
  have := neg_abs_le t
  linarith [this]

lemma integral_pos_part_le (hf : Measurable f) (hκ : ∀ x, |f x| ≤ κ) (t s : ℝ) :
    ∫ x, max (f x - t) 0 ∂R ≤ (∫ x, max (f x - s) 0 ∂R) + |t - s| := by
  have hi := integrable_pos_part (R := R) hf hκ s
  calc ∫ x, max (f x - t) 0 ∂R ≤ ∫ x, (max (f x - s) 0 + |t - s|) ∂R := by
        refine integral_mono (integrable_pos_part hf hκ t) (hi.add (integrable_const _)) fun x => ?_
        have := le_abs_self (s - t)
        rw [abs_sub_comm] at this
        simp only
        refine max_le ?_ ?_
        · have := le_max_left (f x - s) 0
          linarith
        · have := le_max_right (f x - s) 0
          have := abs_nonneg (t - s)
          linarith
    _ = (∫ x, max (f x - s) 0 ∂R) + |t - s| := by
        rw [integral_add hi (integrable_const _), integral_const]
        simp

lemma continuous_cvarObj (hf : Measurable f) (hκ : ∀ x, |f x| ≤ κ) (α : ℝ) :
    Continuous (cvarObj R α f) := by
  have hI : Continuous fun t => ∫ x, max (f x - t) 0 ∂R := by
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun t s => ?_).continuous
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
    have h1 := integral_pos_part_le (R := R) hf hκ t s
    have h2 := integral_pos_part_le (R := R) hf hκ s t
    rw [abs_sub_comm] at h2
    constructor <;> linarith
  exact continuous_id.add (continuous_const.mul hI)

end

theorem tcompact : Claims.tcompact := by
  intro X _ R _ f κ α hf hκ hα0 hα1
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure R
  have hκ0 : 0 ≤ κ := (abs_nonneg _).trans (hκ x0)
  set A := cvarObj R α f with hA
  have hc : 1 ≤ (1 - α)⁻¹ := by
    rw [one_le_inv₀ (by linarith)]; linarith
  -- right of `κ`
  have hright : ∀ t, κ ≤ t → A t = t := by
    intro t ht
    have : (fun x => max (f x - t) 0) = fun _ => (0 : ℝ) := by
      funext x; exact max_eq_right (by linarith [(abs_le.1 (hκ x)).2])
    simp only [hA, cvarObj, this, integral_zero, mul_zero, add_zero]
  -- left of `−κ`
  have hleft : ∀ t, t ≤ -κ → A t = t + (1 - α)⁻¹ * ((∫ x, f x ∂R) - t) := by
    intro t ht
    have : (fun x => max (f x - t) 0) = fun x => f x - t := by
      funext x; exact max_eq_left (by linarith [(abs_le.1 (hκ x)).1])
    have hfi : Integrable f R := by
      refine Integrable.of_bound (C := κ) hf.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs]; exact hκ x
    simp only [hA, cvarObj, this]
    rw [integral_sub hfi (integrable_const _), integral_const]
    simp
  obtain ⟨t, ht, hmin⟩ := (isCompact_Icc (a := -κ) (b := κ)).exists_isMinOn
    (nonempty_Icc.2 (by linarith)) (continuous_cvarObj (R := R) hf hκ α).continuousOn
  refine ⟨t, ht, fun s => ?_⟩
  rcases le_or_gt s (-κ) with hs | hs
  · have h1 : A (-κ) ≤ A s := by
      rw [hleft s hs, hleft (-κ) le_rfl]
      have : (s + κ) * (1 - (1 - α)⁻¹) ≥ 0 := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      nlinarith
    exact (hmin (left_mem_Icc.2 (by linarith))).trans h1
  rcases le_or_gt κ s with hs' | hs'
  · have h1 : A κ ≤ A s := by rw [hright s hs', hright κ le_rfl]; exact hs'
    exact (hmin (right_mem_Icc.2 (by linarith))).trans h1
  · exact hmin ⟨hs.le, hs'.le⟩

example : Claims.tcompact := tcompact

end StatFormal.Wave24a
