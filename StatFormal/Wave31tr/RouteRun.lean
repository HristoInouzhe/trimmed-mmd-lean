import StatFormal.Wave31tr.Statements
import StatFormal.Lib.PaperRun.OrdStat

/-!
# Wave 31tr, chunk A1, T1: quantile rules and the printed genuine rules (untrusted route)

Proves `Claims.genuine_rules`, `Claims.printed_cuts`, `Claims.npQuantile_rule`, `Claims.ordStat_facts`. The brackets are the
certified `Wave30tz` claims `exact_quantile_bracket`, `numpy_bracket` (route theorems of `Wave30tz.RouteOrder`); measurability,
Lipschitz continuity and the extreme quantiles are `StatFormal.Lib.PaperRun.OrdStat`.
-/

set_option linter.style.longLine false

noncomputable section

namespace StatFormal.Wave31tr.RouteRun

open StatFormal.Wave30tz StatFormal.PaperRun

/-- `h ↦ lowQ k h p` is measurable (an order statistic at a rank fixed by `k, p`). -/
theorem measurable_lowQ (k : ℕ) (p : ℝ) : Measurable fun h : Fin k → ℝ => lowQ k h p :=
  measurable_ordStat _

/-- `h ↦ highQ k h p` is measurable. -/
theorem measurable_highQ (k : ℕ) (p : ℝ) : Measurable fun h : Fin k → ℝ => highQ k h p :=
  measurable_ordStat _

/-- Every genuine-quantile rule is a quantile rule (`eq:cutrank`), by the certified `exact_quantile_bracket`. -/
theorem isQuantileRule_of_genuine {q : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ} (hq : IsGenuineQuantileRule q) :
    IsQuantileRule q := by
  refine ⟨hq.1, fun k h p hk hp0 hp1 => ?_⟩
  obtain ⟨hE, hlo, hhi⟩ := hq.2 k h p hk hp0 hp1
  exact exact_quantile_bracket_route k p (q k h p) h hk hp0 hp1 hE hlo hhi

/-- `lowQ` is a genuine-quantile rule. -/
theorem genuine_lowQ : IsGenuineQuantileRule lowQ := by
  refine ⟨measurable_lowQ, fun k h p hk hp0 hp1 => ?_⟩
  have hr1 : 1 ≤ max 1 ⌈(k : ℝ) * p⌉₊ := le_max_left _ _
  obtain ⟨i, hi⟩ := exists_eq_ordStat h hr1 (ceil_rank_le hk hp1)
  exact ⟨isEmpQuantile_ordStat_ceil h hk hp0 hp1, ⟨i, by unfold lowQ; rw [hi]⟩, ⟨i, by unfold lowQ; rw [hi]⟩⟩

/-- `highQ` is a genuine-quantile rule. -/
theorem genuine_highQ : IsGenuineQuantileRule highQ := by
  refine ⟨measurable_highQ, fun k h p hk hp0 hp1 => ?_⟩
  have hr1 : 1 ≤ min k (⌊(k : ℝ) * p⌋₊ + 1) := le_min hk (by omega)
  obtain ⟨i, hi⟩ := exists_eq_ordStat h hr1 (min_le_left _ _)
  exact ⟨isEmpQuantile_ordStat_floor h hk hp0 hp1, ⟨i, by unfold highQ; rw [hi]⟩, ⟨i, by unfold highQ; rw [hi]⟩⟩

theorem genuine_rules_route : Claims.genuine_rules :=
  ⟨genuine_lowQ, genuine_highQ, fun _ hq => isQuantileRule_of_genuine hq⟩

theorem printed_cuts_route : Claims.printed_cuts := by
  intro k h α hk hα0 hα1
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < (k : ℝ) * (1 - α) := mul_pos (by linarith) (by linarith)
  have hc1 : 1 ≤ ⌈(k : ℝ) * (1 - α)⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hpos).ne'
  have hck : ⌈(k : ℝ) * (1 - α)⌉₊ ≤ k := Nat.ceil_le.mpr (by nlinarith)
  have hfk : ⌊(k : ℝ) * α⌋₊ + 1 ≤ k := by
    have : ⌊(k : ℝ) * α⌋₊ < k := (Nat.floor_lt (by positivity)).mpr (by nlinarith)
    omega
  have hlow : lowQ k h (1 - α) = ordStat h ⌈(k : ℝ) * (1 - α)⌉₊ := by
    unfold lowQ; rw [max_eq_right hc1]
  have hhigh : highQ k h α = ordStat h (⌊(k : ℝ) * α⌋₊ + 1) := by
    unfold highQ; rw [min_eq_right hfk]
  refine ⟨hc1, hck, hfk, hlow, hhigh, ⟨?_, fun q hq => ?_⟩, ⟨?_, fun q hq => ?_⟩⟩
  · exact (genuine_lowQ.2 k h (1 - α) hk (by linarith) (by linarith)).1
  · rw [hlow]; exact ordStat_ceil_le_of_isEmpQuantile h (by linarith) (by linarith) hk hq
  · exact (genuine_highQ.2 k h α hk hα0 hα1.le).1
  · rw [hhigh]; exact le_ordStat_floor_of_isEmpQuantile h hα0 hfk hq

theorem npQuantile_rule_route : Claims.npQuantile_rule := by
  refine ⟨fun k p => ?_, fun k h p hk hp0 hp1 => (numpy_bracket_route k p h hk hp0 hp1).2.2⟩
  unfold npQuantile
  exact (measurable_ordStat _).add (measurable_const.mul ((measurable_ordStat _).sub (measurable_ordStat _)))

theorem ordStat_facts_route : Claims.ordStat_facts := fun _ r hr1 hrk =>
  ⟨measurable_ordStat r, ordStat_lipschitz hr1 hrk, fun h v => ordStat_le_iff h hr1 hrk v⟩

end StatFormal.Wave31tr.RouteRun
