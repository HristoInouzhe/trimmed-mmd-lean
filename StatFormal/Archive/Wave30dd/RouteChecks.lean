import StatFormal.Archive.Wave30dd.Statements
import StatFormal.Archive.Wave29l.RouteChecks
import Mathlib.Analysis.SpecificLimits.Basic

/-! Route checks (non-target): the size witnesses `n_k = k + 1`, `m_k = 2^k` (outside every ratio regime) meet the
size premises of all claims, and the frozen `ass:split` witness (uniform law on `[0,1]`, `α = 1/2`). -/

set_option linter.style.longLine false

open Filter

namespace StatFormal.Wave30dd

lemma wdd_sizes : (∀ k : ℕ, 1 ≤ k + 1) ∧ (∀ k : ℕ, 1 ≤ 2 ^ k) ∧ Tendsto (fun k : ℕ => k + 1) atTop atTop ∧
    Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
  ⟨fun k => Nat.le_add_left 1 k, fun k => Nat.one_le_two_pow, tendsto_add_atTop_nat 1,
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two⟩

example : StatFormal.Wave29i.splitAss (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) id (1/2) (1/2) :=
  StatFormal.Wave29i.splitAss_uniform

end StatFormal.Wave30dd
