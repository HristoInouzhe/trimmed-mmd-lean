import StatFormal.Archive.TrimmedMMD.Concentration.Region
import StatFormal.Lib.Concentration.TrimmedClass

/-!
# Proofs: trimmed-MMD `thm:concentration` and `cor:uniform`

Route (the supplement's):
* `eq:reduction` (`hausdorffDist_region_le`, via `eq:hormander` by projection onto the closed
  convex hull, `eq:cvar` and `lem:tcompact` with an explicit quantile witness), applied to
  `Q₁ = Pₙ`, `Q₂ = P`: `d_H ≤ (1−α)⁻¹ · sup_{g∈𝒢} |(Pₙ − P) g|` for every sample
  (`hausdorffDist_le_iSup`);
* the uniform-deviation event of `StatFormal.Concentration.tm_concentration_countable` (symmetrisation,
  contraction, McDiarmid), over a countable dense subclass, which is a measurable event and does
  not depend on `α` (`exists_good_event`).
-/

noncomputable section
open MeasureTheory Set StatFormal.Concentration

namespace StatFormal.TrimmedMMD.Concentration

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem isProbabilityMeasure_empirical {n : ℕ} (hn : n ≠ 0) (x : Fin n → 𝒳) :
    IsProbabilityMeasure (empirical x) := by
  constructor
  have h1 : ENNReal.ofReal (1 / n) = (n : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)), ENNReal.ofReal_one,
      ENNReal.ofReal_natCast, one_div]
  simp only [empirical, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, h1]
  exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hn) (ENNReal.natCast_ne_top n)

theorem integral_empirical {n : ℕ} (x : Fin n → 𝒳) {h : 𝒳 → ℝ} (hh : StronglyMeasurable h)
    {C : ℝ} (hC : ∀ y, |h y| ≤ C) :
    ∫ y, h y ∂(empirical x) = (n : ℝ)⁻¹ * ∑ i, h (x i) := by
  unfold empirical
  rw [integral_finsetSum_measure fun i _ =>
    (Integrable.of_bound hh.aestronglyMeasurable C (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]; exact hC y)).smul_measure ENNReal.ofReal_ne_top]
  simp_rw [integral_smul_measure, integral_dirac' _ _ hh]
  rw [ENNReal.toReal_ofReal (by positivity), Finset.mul_sum]
  simp [smul_eq_mul, one_div]

variable {φ : 𝒳 → H} {κ α : ℝ}

/-- Deterministic reduction at every sample. -/
theorem hausdorffDist_le_iSup [CompleteSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P]
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) {n : ℕ}
    (hn : n ≠ 0) (x : Fin n → 𝒳) :
    Metric.hausdorffDist (region φ α (empirical x)) (region φ α P) ≤
      1 / (1 - α) * ⨆ p : tmParams H κ, |empDev P (gTM φ) n x p.1| := by
  haveI := isProbabilityMeasure_empirical hn x
  have hκ0 : 0 ≤ κ := by
    obtain ⟨y⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ y)
  have h0 : ((0 : H), (0 : ℝ)) ∈ tmParams H κ := ⟨by simp, by simp [hκ0]⟩
  haveI : Nonempty (tmParams H κ) := ⟨⟨_, h0⟩⟩
  have hbdd : BddAbove (Set.range fun p : tmParams H κ => |empDev P (gTM φ) n x p.1|) :=
    bddAbove_of_abs_le (C := 2 * (2 * κ)) fun p => by
      rw [abs_abs]
      exact abs_empDev_le P (g := fun p : tmParams H κ => gTM φ p.1)
        (fun p y => abs_gTM_le hκ p.2 y) x p
  have hS0 : 0 ≤ ⨆ p : tmParams H κ, |empDev P (gTM φ) n x p.1| :=
    le_ciSup_of_le hbdd ⟨_, h0⟩ (abs_nonneg _)
  refine hausdorffDist_region_le (empirical x) P hφ hκ hα0 hα1 hS0 fun f q hf hq => ?_
  have hp : (f, q) ∈ tmParams H κ := ⟨hf, hq⟩
  have hemp := integral_empirical x (measurable_gTM hφ (f, q)).stronglyMeasurable
    (fun y => abs_gTM_le hκ hp y)
  have : |∫ y, max (inner ℝ f (φ y) - q) 0 ∂(empirical x) -
      ∫ y, max (inner ℝ f (φ y) - q) 0 ∂P| = |empDev P (gTM φ) n x (f, q)| := by
    change |∫ y, gTM φ (f, q) y ∂(empirical x) - ∫ y, gTM φ (f, q) y ∂P| = _
    rw [hemp]; rfl
  rw [this]
  exact le_ciSup hbdd ⟨(f, q), hp⟩

/-- The measurable, `α`-free event on which the uniform deviation is small. -/
theorem exists_good_event [TopologicalSpace.SeparableSpace H] (P : Measure 𝒳)
    [IsProbabilityMeasure P] (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {n : ℕ}
    (hn : 1 ≤ n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ E : Set (Fin n → 𝒳), MeasurableSet E ∧ 1 - δ ≤ (Measure.pi fun _ : Fin n => P).real E ∧
      ∀ x ∈ E, (⨆ p : tmParams H κ, |empDev P (gTM φ) n x p.1|) ≤
        4 * κ / √n + κ * √(2 * Real.log (2 / δ) / n) := by
  have hκ0 : 0 ≤ κ := by
    obtain ⟨y⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ y)
  have h0 : ((0 : H), (0 : ℝ)) ∈ tmParams H κ := ⟨by simp, by simp [hκ0]⟩
  haveI : Nonempty (tmParams H κ) := ⟨⟨_, h0⟩⟩
  rcases hκ0.eq_or_lt with hκe | hκpos
  · -- `κ = 0`: the class is `{0}`.
    subst hκe
    refine ⟨univ, MeasurableSet.univ, by rw [probReal_univ]; linarith, fun x _ => ?_⟩
    have hφ0 : ∀ y, φ y = 0 := fun y => norm_le_zero_iff.1 (hκ y)
    refine ciSup_le fun p => ?_
    have hp2 : p.1.2 = 0 := abs_nonpos_iff.1 p.2.2
    have hg : ∀ y, gTM φ p.1 y = 0 := fun y => by simp [gTM, hφ0, hp2]
    simp [empDev, hg]
  · obtain ⟨T₀, hT₀, hcount, hdense⟩ :=
      (TopologicalSpace.IsSeparable.of_separableSpace (tmParams H κ)).exists_countable_dense_subset
    have hne : T₀.Nonempty := closure_nonempty_iff.1 ⟨_, hdense h0⟩
    haveI : Nonempty T₀ := hne.to_subtype
    haveI : Countable T₀ := hcount.to_subtype
    refine ⟨{x | ⨆ q : T₀, |empDev P (fun q : T₀ => gTM φ q.1) n x q| ≤
        4 * κ / √n + κ * √(2 * Real.log (2 / δ) / n)}, ?_,
      tm_concentration_countable P T₀ hT₀ hφ hκ hκpos hn hδ0 hδ1, fun x hx => ?_⟩
    · exact measurableSet_le (Measurable.iSup fun q => continuous_abs.measurable.comp
        (measurable_empDev P (fun q : T₀ => measurable_gTM hφ q.1) n q)) measurable_const
    · rw [iSup_tmParams_eq P hφ hκ T₀ hT₀ hdense x]
      exact hx

theorem rn_eq (κ α δ : ℝ) (n : ℕ) :
    1 / (1 - α) * (4 * κ / √n + κ * √(2 * Real.log (2 / δ) / n)) =
      StatFormal.TrimmedMMD.rn κ α δ n := by
  unfold StatFormal.TrimmedMMD.rn; ring

theorem hausdorffDist_le_rn [CompleteSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P]
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) {n : ℕ}
    (hn : 1 ≤ n) {δ : ℝ} (x : Fin n → 𝒳)
    (hx : (⨆ p : tmParams H κ, |empDev P (gTM φ) n x p.1|) ≤
        4 * κ / √n + κ * √(2 * Real.log (2 / δ) / n)) :
    Metric.hausdorffDist (region φ α (empirical x)) (region φ α P) ≤
      StatFormal.TrimmedMMD.rn κ α δ n := by
  have hβ : 0 ≤ 1 / (1 - α) := by
    have : 0 < 1 - α := by linarith
    positivity
  rw [← rn_eq]
  exact (hausdorffDist_le_iSup P hφ hκ hα0 hα1 (Nat.one_le_iff_ne_zero.1 hn) x).trans
    (mul_le_mul_of_nonneg_left hx hβ)

theorem concentration : Claims.concentration := by
  intro 𝒳 H _ _ _ _ _ P _ φ κ α δ n hφ hκ hα0 hα1 hn hδ0 hδ1
  obtain ⟨E, hEm, hEp, hE⟩ := exists_good_event P hφ hκ hn hδ0 hδ1
  exact ⟨E, hEm, hEp, fun x hx => hausdorffDist_le_rn P hφ hκ hα0 hα1 hn x (hE x hx)⟩

theorem uniform_alpha : Claims.uniform_alpha := by
  intro 𝒳 H _ _ _ _ _ P _ φ κ δ n hφ hκ hn hδ0 hδ1
  obtain ⟨E, hEm, hEp, hE⟩ := exists_good_event P hφ hκ hn hδ0 hδ1
  exact ⟨E, hEm, hEp, fun x hx α hα0 hα1 =>
    hausdorffDist_le_rn P hφ hκ hα0 hα1 hn x (hE x hx)⟩

theorem rn_mono {κ α α' δ : ℝ} {n : ℕ} (hκ : 0 ≤ κ) (hαα' : α ≤ α') (hα' : α' < 1) :
    StatFormal.TrimmedMMD.rn κ α δ n ≤ StatFormal.TrimmedMMD.rn κ α' δ n := by
  unfold StatFormal.TrimmedMMD.rn
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact div_le_div_of_nonneg_left hκ (by linarith) (by linarith)

theorem uniform_sup : Claims.uniform_sup := by
  intro 𝒳 H _ _ _ _ _ P _ φ κ δ η n hφ hκ hn hδ0 hδ1 hη0 hη1
  obtain ⟨E, hEm, hEp, hE⟩ := exists_good_event P hφ hκ hn hδ0 hδ1
  have hκ0 : 0 ≤ κ := by
    obtain ⟨y⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ y)
  refine ⟨E, hEm, hEp, fun x hx α hα0 hα1 => ?_⟩
  exact (hausdorffDist_le_rn P hφ hκ hα0 (by linarith) hn x (hE x hx)).trans
    (rn_mono hκ0 hα1 (by linarith))

end StatFormal.TrimmedMMD.Concentration
