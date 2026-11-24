import StatFormal.Archive.Wave29d.Statements
import StatFormal.Lib.Bathtub.Basic

/-!
# `lem:lindsay`, the density-bounded class (`lindsay_bathtub`)

Untrusted proof file. With `κ = δ` the likelihoods are `ψ_i = e^{φ_i}`, so `D_{m̂}` is measurable and bounded; the
level-set intermediate value theorem gives `θ`, and the bathtub principle (`StatFormal.Foundations.Bathtub.Basic`)
gives the value, attained at `M · Leb|_{K ∩ {D > θ}}`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave29d

lemma psiK_id {L : Type*} [MeasurableSpace L] [MeasurableSingletonClass L] {n : ℕ} (φ : Fin n → L → ℝ)
    (i : Fin n) (y : L) : psiK Kernel.id φ i y = Real.exp (φ i y) := by
  simp only [psiK, Kernel.id_apply, integral_dirac]

lemma lindsayDK_id_measurable {L : Type*} [MeasurableSpace L] [MeasurableSingletonClass L] {n : ℕ}
    (φ : Fin n → L → ℝ) (hφ : ∀ i, Measurable (φ i)) (mh : Measure L) :
    Measurable (lindsayDK Kernel.id φ mh) := by
  have : lindsayDK Kernel.id φ mh =
      fun y => (1 / n : ℝ) * ∑ i, Real.exp (φ i y) / ∫ y', psiK Kernel.id φ i y' ∂mh := by
    funext y; simp only [lindsayDK, psiK_id]
  rw [this]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    ((hφ i).exp).div_const _)

lemma lindsayDK_id_bdd {L : Type*} [MeasurableSpace L] [MeasurableSingletonClass L] {n : ℕ}
    (φ : Fin n → L → ℝ) {B : ℝ} (hB : ∀ i x, |φ i x| ≤ B) (mh : Measure L) :
    ∀ y, |lindsayDK Kernel.id φ mh y| ≤
      |(1 / n : ℝ)| * ∑ i, Real.exp B * |(∫ y', psiK Kernel.id φ i y' ∂mh)|⁻¹ := by
  intro y
  simp only [lindsayDK]
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [psiK_id, abs_div, Real.abs_exp, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ((le_abs_self _).trans (hB i y)))
    (inv_nonneg.2 (abs_nonneg _))

theorem lindsay_bathtub : Claims.lindsay_bathtub := by
  intro d n K φ M mh hset hKc hM hmh hlev
  obtain ⟨_, _, hφm, B, hB⟩ := hset
  obtain ⟨hmhP, hmhle⟩ := hmh
  set D := lindsayDK Kernel.id φ mh with hDdef
  have hD : Measurable D := lindsayDK_id_measurable φ hφm mh
  have hC := lindsayDK_id_bdd φ hB mh
  have hKm : MeasurableSet K := hKc.measurableSet
  have hKfin : volume K ≠ ∞ := hKc.measure_lt_top.ne
  -- `1/M ≤ Leb K`, from `1 = mh univ ≤ M · Leb K`
  have haK : ENNReal.ofReal (1 / M) ≤ volume K := by
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal M * volume K := by
      have := hmhle univ
      rwa [measure_univ, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul] at this
    calc ENNReal.ofReal (1 / M) = ENNReal.ofReal (1 / M) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal (1 / M) * (ENNReal.ofReal M * volume K) := by gcongr
      _ = volume K := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hM.ne',
          ENNReal.ofReal_one, one_mul]
  obtain ⟨θ, hθ⟩ := StatFormal.Bathtub.exists_level_measure_eq volume hKm hKfin hD hC hlev
    (ENNReal.ofReal_pos.2 (by positivity)) haK
  obtain ⟨hstarP, hstarle⟩ := StatFormal.Bathtub.bathtub_mem volume (D := D) hM hθ
  have hgreat : IsGreatest {v | ∃ ν ∈ densClass K M, v = ∫ y, D y ∂ν}
      (M * ∫ x in K ∩ {x | θ < D x}, D x) := by
    refine ⟨⟨_, ⟨hstarP, hstarle⟩, (StatFormal.Bathtub.bathtub_integral_eq volume hM).symm⟩, ?_⟩
    rintro v ⟨ν, ⟨hνP, hνle⟩, rfl⟩
    exact StatFormal.Bathtub.bathtub_integral_le volume hKm hKfin hD hC hM hθ ν hνle
  refine ⟨θ, hθ, hgreat, ⟨hstarP, hstarle⟩, ?_⟩
  exact hgreat.csSup_eq

end StatFormal.Wave29d
