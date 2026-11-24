import StatFormal.Lib.MollifierNorm.Dyadic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Dyadic shells: a weighted `L²` bound from a tail bound (library, untrusted)

Let `(α, μ)` be a measure space, `u : α → [0, ∞)` measurable (a "radius"), `F : α → [0, ∞]` with total mass `≤ M` and tail
bound `∫_{u ≥ t} F ≤ A/t` for all `t > 0`, and `B : α → [0, ∞]` with `B ≤ 1` and `B ≤ C_b² (w u)^{−4m}` where `u > 0`. For
`s > 1/2`, `4m > 2s − 1` and `0 < w ≤ 1`:
`∫ F · B · (1 + u²)^s dμ ≤ 2^s M + 2^{3s} A w^{1−2s} [1/(1 − 2^{1−2s}) + C_b²/(1 − 2^{−(4m+1−2s)})]`.

This is the frequency splitting in the proof of Lemma S4.9 of trimmed-mmd, written for an abstract radius: on `{u < 1}`
the weight is at most `2^s`; on the shell `S_j = {2^j ≤ u < 2^{j+1}}` it is at most `2^{3s} 4^{sj}`, `B ≤ min{1, C_b²(w2^j)^{−4m}}`
and `∫_{S_j} F ≤ A 2^{−j}`; the shells partition `{u ≥ 1}` (`lintegral_iUnion`) and the dyadic sum is `dyadic_tsum_le`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.MollifierNorm

/-- The weight on the dyadic shell `j`: `(2^{2j+3})^s = 2^{3s} · (2^{2s−1})^j · 2^j`. -/
theorem two_pow_shell_rpow (s : ℝ) (j : ℕ) :
    ((2 : ℝ) ^ (2 * j + 3)) ^ s = 2 ^ (3 * s) * (((2 : ℝ) ^ (2 * s - 1)) ^ j * 2 ^ j) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, ← Real.rpow_mul_natCast zero_le_two, ← Real.rpow_natCast 2 j,
    ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
  congr 1
  push_cast
  ring

/-- The dyadic shell `{2^j ≤ u < 2^{j+1}}` of a radius `u`. -/
def shell {α : Type*} (u : α → ℝ) (j : ℕ) : Set α := {x | (2 : ℝ) ^ j ≤ u x ∧ u x < 2 ^ (j + 1)}

/-- The dyadic shells `{2^j ≤ u < 2^{j+1}}` partition `{u ≥ 1}`. -/
theorem iUnion_shells {α : Type*} (u : α → ℝ) : (⋃ j : ℕ, shell u j) = {x | u x < 1}ᶜ := by
  ext x
  simp only [shell, mem_iUnion, mem_ofPred_eq, mem_compl_iff, not_lt]
  constructor
  · rintro ⟨j, hj, -⟩; exact (one_le_pow₀ one_le_two).trans hj
  · intro hx; exact exists_nat_pow_near hx one_lt_two

/-- The dyadic shells are pairwise disjoint. -/
theorem pairwise_disjoint_shells {α : Type*} (u : α → ℝ) : Pairwise (Function.onFun Disjoint (shell u)) := by
  intro i j hij
  refine Set.disjoint_left.2 fun x hi hj => ?_
  rcases lt_or_gt_of_ne hij with h | h
  · have : (2 : ℝ) ^ (i + 1) ≤ 2 ^ j := pow_le_pow_right₀ one_le_two h
    exact absurd (hi.2.trans_le (this.trans hj.1)) (lt_irrefl _)
  · have : (2 : ℝ) ^ (j + 1) ≤ 2 ^ i := pow_le_pow_right₀ one_le_two h
    exact absurd (hj.2.trans_le (this.trans hi.1)) (lt_irrefl _)

/-- **The dyadic-shell bound**: with `F` of total mass `≤ M` and tail `∫_{u ≥ t} F ≤ A/t`, and a multiplier `B ≤ 1`,
`B ≤ C_b² (w u)^{−4m}` where `u > 0`:
`∫ F B (1 + u²)^s ≤ 2^s M + 2^{3s} A w^{1−2s} [1/(1 − 2^{1−2s}) + C_b²/(1 − 2^{−(4m+1−2s)})]`. -/
theorem lintegral_shells_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {u : α → ℝ} (hu : Measurable u)
    (hu0 : ∀ x, 0 ≤ u x) {F B : α → ℝ≥0∞} {M A Cb s w : ℝ} {m : ℕ} (hs : 1 / 2 < s) (hm : 2 * s - 1 < 4 * m)
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hA : 0 ≤ A)
    (htot : ∫⁻ x, F x ∂μ ≤ ENNReal.ofReal M)
    (htail : ∀ t : ℝ, 0 < t → ∫⁻ x in {x | t ≤ u x}, F x ∂μ ≤ ENNReal.ofReal (A / t))
    (hB1 : ∀ x, B x ≤ 1) (hB2 : ∀ x, 0 < u x → B x ≤ ENNReal.ofReal (Cb ^ 2 * ((w * u x) ^ (4 * m))⁻¹)) :
    ∫⁻ x, F x * B x * ENNReal.ofReal ((1 + u x ^ 2) ^ s) ∂μ ≤
      ENNReal.ofReal (2 ^ s * M) + ENNReal.ofReal (2 ^ (3 * s) * A * (w ^ (1 - 2 * s) *
        (1 / (1 - (2 : ℝ) ^ (1 - 2 * s)) + Cb ^ 2 / (1 - (2 : ℝ) ^ (-(4 * m + 1 - 2 * s)))))) := by
  set Ψ : α → ℝ≥0∞ := fun x => F x * B x * ENNReal.ofReal ((1 + u x ^ 2) ^ s) with hΨ
  have hL : MeasurableSet {x | u x < 1} := measurableSet_lt hu measurable_const
  rw [← lintegral_add_compl Ψ hL]
  refine add_le_add ?_ ?_
  · -- low frequencies
    calc ∫⁻ x in {x | u x < 1}, Ψ x ∂μ ≤ ∫⁻ x in {x | u x < 1}, F x * ENNReal.ofReal (2 ^ s) ∂μ := by
          refine setLIntegral_mono' hL fun x hx => ?_
          have h2 : 1 + u x ^ 2 ≤ 2 := by
            have := hu0 x; have : u x < 1 := hx; nlinarith
          calc Ψ x ≤ F x * 1 * ENNReal.ofReal (2 ^ s) := by
                simp only [hΨ]
                gcongr
                exact hB1 x
            _ = F x * ENNReal.ofReal (2 ^ s) := by rw [mul_one]
      _ ≤ ∫⁻ x, F x * ENNReal.ofReal (2 ^ s) ∂μ := setLIntegral_le_lintegral _ _
      _ = (∫⁻ x, F x ∂μ) * ENNReal.ofReal (2 ^ s) := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (2 ^ s) := by gcongr
      _ = ENNReal.ofReal (2 ^ s * M) := by rw [mul_comm, ENNReal.ofReal_mul (by positivity)]
  · -- the dyadic shells
    set S : ℕ → Set α := shell u with hS
    have hSm : ∀ j, MeasurableSet (S j) := fun j =>
      (measurableSet_le measurable_const hu).inter (measurableSet_lt hu measurable_const)
    set a : ℕ → ℝ := fun j => ((2 : ℝ) ^ (2 * s - 1)) ^ j * min 1 (Cb ^ 2 * ((w * 2 ^ j) ^ (4 * m))⁻¹) with ha
    obtain ⟨hsumm, hsum⟩ := dyadic_tsum_le (Cb := Cb) hs hm hw0 hw1
    have ha0 : ∀ j, 0 ≤ a j := fun j => mul_nonneg (by positivity) (le_min zero_le_one (by positivity))
    have hshell : ∀ j, ∫⁻ x in S j, Ψ x ∂μ ≤ ENNReal.ofReal (2 ^ (3 * s) * A * a j) := by
      intro j
      have h2j : (0 : ℝ) < 2 ^ j := by positivity
      set c : ℝ := 2 ^ (3 * s) * (((2 : ℝ) ^ (2 * s - 1)) ^ j * 2 ^ j) * min 1 (Cb ^ 2 * ((w * 2 ^ j) ^ (4 * m))⁻¹)
        with hc
      have hc0 : 0 ≤ c := by positivity
      calc ∫⁻ x in S j, Ψ x ∂μ ≤ ∫⁻ x in S j, F x * ENNReal.ofReal c ∂μ := by
            refine setLIntegral_mono' (hSm j) fun x hx => ?_
            have hx : (2 : ℝ) ^ j ≤ u x ∧ u x < 2 ^ (j + 1) := hx
            have hux : 0 < u x := h2j.trans_le hx.1
            simp only [hΨ]
            rw [mul_assoc]
            gcongr
            have hW : (1 + u x ^ 2) ^ s ≤ 2 ^ (3 * s) * (((2 : ℝ) ^ (2 * s - 1)) ^ j * 2 ^ j) := by
              rw [← two_pow_shell_rpow]
              refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
              have h1 : (1 : ℝ) ≤ u x := (one_le_pow₀ one_le_two).trans hx.1
              have h3 : u x ^ 2 < (2 ^ (j + 1)) ^ 2 := pow_lt_pow_left₀ hx.2 (hu0 x) two_ne_zero
              calc 1 + u x ^ 2 ≤ 2 * u x ^ 2 := by nlinarith
                _ ≤ 2 * (2 ^ (j + 1)) ^ 2 := by linarith
                _ = 2 ^ (2 * j + 3) := by ring
            have hB : B x ≤ ENNReal.ofReal (min 1 (Cb ^ 2 * ((w * 2 ^ j) ^ (4 * m))⁻¹)) := by
              rw [ENNReal.ofReal_min, ENNReal.ofReal_one]
              refine le_min (hB1 x) ((hB2 x hux).trans (ENNReal.ofReal_le_ofReal ?_))
              gcongr
              exact hx.1
            calc B x * ENNReal.ofReal ((1 + u x ^ 2) ^ s)
                ≤ ENNReal.ofReal (min 1 (Cb ^ 2 * ((w * 2 ^ j) ^ (4 * m))⁻¹)) *
                    ENNReal.ofReal (2 ^ (3 * s) * (((2 : ℝ) ^ (2 * s - 1)) ^ j * 2 ^ j)) := by
                  gcongr
              _ = ENNReal.ofReal c := by
                  rw [← ENNReal.ofReal_mul (le_min zero_le_one (by positivity)), hc]; ring_nf
        _ = (∫⁻ x in S j, F x ∂μ) * ENNReal.ofReal c := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
        _ ≤ (∫⁻ x in {x | (2 : ℝ) ^ j ≤ u x}, F x ∂μ) * ENNReal.ofReal c := by
            gcongr
            exact fun x (hx : x ∈ S j) => hx.1
        _ ≤ ENNReal.ofReal (A / 2 ^ j) * ENNReal.ofReal c := by gcongr; exact htail _ h2j
        _ = ENNReal.ofReal (2 ^ (3 * s) * A * a j) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [hc, ha]
            field_simp
    rw [← iUnion_shells u, lintegral_iUnion hSm (pairwise_disjoint_shells u)]
    calc ∑' j, ∫⁻ x in S j, Ψ x ∂μ ≤ ∑' j, ENNReal.ofReal (2 ^ (3 * s) * A * a j) := ENNReal.tsum_le_tsum hshell
      _ = ENNReal.ofReal (∑' j, 2 ^ (3 * s) * A * a j) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun j => by have := ha0 j; positivity) (hsumm.mul_left _)).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [tsum_mul_left]
          exact mul_le_mul_of_nonneg_left hsum (by positivity)

end StatFormal.MollifierNorm
