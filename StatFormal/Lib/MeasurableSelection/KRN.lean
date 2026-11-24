import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Bases

/-!
# The Kuratowski–Ryll-Nardzewski measurable selection theorem

Library component (untrusted). `X` a measurable space, `Y` a nonempty complete separable metric space with its Borel
σ-algebra, `A : X → Set Y` with closed nonempty values which is *weakly measurable* in the ball form:
`{x | A x ∩ B(c, r) ≠ ∅}` is measurable for every centre `c` and radius `r`. Then `A` has a measurable selector.

* `measurable_dite_find`: `x ↦ (if ∃ n, p x n then Nat.find else 0)` is measurable when every `{x | p x n}` is.
* `exists_measurable_selector`: the theorem (Kuratowski–Ryll-Nardzewski 1965; Aliprantis–Border, Thm 18.13).
* `exists_measurable_selector_of_isOpen`: the same with the hypothesis for all open sets.

Proof: with a dense sequence `D`, choose indices `s_k(x)` (least index, so measurable) with
`A x ∩ B(D s_k(x), 2^{-k}) ≠ ∅` and `d(D s_{k+1}(x), D s_k(x)) < 2·2^{-k}`; the points `D s_k(x)` are Cauchy, their limit
is measurable (limit of countably-valued measurable maps) and lies in the closed set `A x`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open Filter Topology MeasureTheory Set Metric
open scoped Classical

namespace StatFormal.Foundations.MeasurableSelection

variable {X : Type*} [MeasurableSpace X]

/-- The least `n` with `p x n` (or `0` if there is none) is measurable in `x`. -/
theorem measurable_dite_find (p : X → ℕ → Prop) {dp : ∀ x, DecidablePred (p x)}
    {de : ∀ x, Decidable (∃ n, p x n)} (hp : ∀ n, MeasurableSet {x | p x n}) :
    Measurable fun x => if h : ∃ n, p x n then Nat.find h else 0 := by
  refine measurable_to_countable' fun n => ?_
  have hE : MeasurableSet {x | ∃ n, p x n} := by
    simp only [setOf_exists]; exact MeasurableSet.iUnion hp
  have : (fun x => if h : ∃ n, p x n then Nat.find h else 0) ⁻¹' {n} =
      ({x | p x n} ∩ ⋂ m ∈ Finset.range n, {x | ¬ p x m}) ∪ ({x | ¬ ∃ n, p x n} ∩ {_x | n = 0}) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_setOf_eq, mem_iInter,
      Finset.mem_range]
    by_cases h : ∃ n, p x n
    · rw [dif_pos h, Nat.find_eq_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact Or.inl ⟨h1, fun m hm => h2 m hm⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
        · exact ⟨h1, fun m hm => h2 m hm⟩
        · exact absurd h h1
    · rw [dif_neg h]
      constructor
      · rintro rfl; exact Or.inr ⟨h, rfl⟩
      · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
        · exact absurd ⟨n, h1⟩ h
        · exact h2.symm
  rw [this]
  refine MeasurableSet.union ((hp n).inter ?_) (hE.compl.inter ?_)
  · exact MeasurableSet.biInter (Set.to_countable _) fun m _ => (hp m).compl
  · by_cases hn : n = 0
    · simp [hn]
    · simp [hn]

section KRN

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The radii `2^{-k}`. -/
def krnRad (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

lemma krnRad_pos (k : ℕ) : 0 < krnRad k := pow_pos (by norm_num) k

lemma krnRad_succ (k : ℕ) : krnRad (k + 1) = krnRad k / 2 := by
  unfold krnRad; rw [pow_succ]; ring

/-- The index sequence of the Kuratowski–Ryll-Nardzewski construction. -/
def krnIdx (A : X → Set Y) (D : ℕ → Y) : ℕ → X → ℕ
  | 0 => fun x => if h : ∃ n, (A x ∩ ball (D n) (krnRad 0)).Nonempty then Nat.find h else 0
  | k + 1 => fun x =>
      if h : ∃ n, (A x ∩ ball (D n) (krnRad (k + 1))).Nonempty ∧
          dist (D n) (D (krnIdx A D k x)) < 2 * krnRad k then Nat.find h else 0

lemma krnIdx_spec (A : X → Set Y) (D : ℕ → Y) (hD : DenseRange D) (hne : ∀ x, (A x).Nonempty) :
    ∀ k x, (A x ∩ ball (D (krnIdx A D k x)) (krnRad k)).Nonempty ∧
      dist (D (krnIdx A D (k + 1) x)) (D (krnIdx A D k x)) < 2 * krnRad k := by
  have hgood : ∀ k x, (A x ∩ ball (D (krnIdx A D k x)) (krnRad k)).Nonempty := by
    intro k
    induction k with
    | zero =>
      intro x
      obtain ⟨a, ha⟩ := hne x
      obtain ⟨n, hn⟩ := hD.exists_dist_lt a (krnRad_pos 0)
      have h : ∃ n, (A x ∩ ball (D n) (krnRad 0)).Nonempty := ⟨n, a, ha, by rw [mem_ball]; exact hn⟩
      simp only [krnIdx, dif_pos h]
      exact Nat.find_spec h
    | succ k ih =>
      intro x
      obtain ⟨a, haA, hab⟩ := ih x
      obtain ⟨n, hn⟩ := hD.exists_dist_lt a (krnRad_pos (k + 1))
      have h : ∃ n, (A x ∩ ball (D n) (krnRad (k + 1))).Nonempty ∧
          dist (D n) (D (krnIdx A D k x)) < 2 * krnRad k := by
        refine ⟨n, ⟨a, haA, by rw [mem_ball]; exact hn⟩, ?_⟩
        rw [mem_ball] at hab
        have := dist_triangle (D n) a (D (krnIdx A D k x))
        rw [dist_comm] at hn
        rw [krnRad_succ] at hn
        linarith [krnRad_pos k]
      simp only [krnIdx, dif_pos h]
      exact (Nat.find_spec h).1
  intro k x
  refine ⟨hgood k x, ?_⟩
  obtain ⟨a, haA, hab⟩ := hgood k x
  obtain ⟨n, hn⟩ := hD.exists_dist_lt a (krnRad_pos (k + 1))
  have h : ∃ n, (A x ∩ ball (D n) (krnRad (k + 1))).Nonempty ∧
      dist (D n) (D (krnIdx A D k x)) < 2 * krnRad k := by
    refine ⟨n, ⟨a, haA, by rw [mem_ball]; exact hn⟩, ?_⟩
    rw [mem_ball] at hab
    have := dist_triangle (D n) a (D (krnIdx A D k x))
    rw [dist_comm] at hn
    rw [krnRad_succ] at hn
    linarith [krnRad_pos k]
  simp only [krnIdx, dif_pos h]
  exact (Nat.find_spec h).2

lemma measurable_krnIdx (A : X → Set Y) (D : ℕ → Y)
    (hA : ∀ (c : Y) (r : ℝ), MeasurableSet {x | (A x ∩ ball c r).Nonempty}) :
    ∀ k, Measurable (krnIdx A D k) := by
  intro k
  induction k with
  | zero => exact measurable_dite_find _ fun n => hA (D n) _
  | succ k ih =>
    rw [krnIdx.eq_2]
    refine measurable_dite_find (fun x n => (A x ∩ ball (D n) (krnRad (k + 1))).Nonempty ∧
      dist (D n) (D (krnIdx A D k x)) < 2 * krnRad k) fun n => ?_
    refine MeasurableSet.inter (hA (D n) _) ?_
    exact ih (MeasurableSet.of_discrete : MeasurableSet {j : ℕ | dist (D n) (D j) < 2 * krnRad k})

/-- **Kuratowski–Ryll-Nardzewski.** A closed-nonempty-valued correspondence into a complete separable metric space
which is weakly measurable (`{x | A x ∩ B(c, r) ≠ ∅}` measurable for all balls) has a measurable selector. -/
theorem exists_measurable_selector [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y] [Nonempty Y]
    (A : X → Set Y) (hcl : ∀ x, IsClosed (A x)) (hne : ∀ x, (A x).Nonempty)
    (hA : ∀ (c : Y) (r : ℝ), MeasurableSet {x | (A x ∩ ball c r).Nonempty}) :
    ∃ σ : X → Y, Measurable σ ∧ ∀ x, σ x ∈ A x := by
  set D := TopologicalSpace.denseSeq Y
  have hD : DenseRange D := TopologicalSpace.denseRange_denseSeq Y
  have hspec := krnIdx_spec A D hD hne
  set y : ℕ → X → Y := fun k x => D (krnIdx A D k x)
  have hcau : ∀ x, CauchySeq fun k => y k x := by
    intro x
    refine cauchySeq_of_le_geometric_two (C := 4) fun k => ?_
    have h := (hspec k x).2
    rw [dist_comm]
    have : (4 : ℝ) / 2 / 2 ^ k = 2 * krnRad k := by unfold krnRad; rw [div_pow, one_pow]; ring
    rw [this]; exact h.le
  have hlim : ∀ x, Tendsto (fun k => y k x) atTop (𝓝 (limUnder atTop fun k => y k x)) := fun x =>
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcau x))
  refine ⟨fun x => limUnder atTop fun k => y k x, ?_, fun x => ?_⟩
  · refine measurable_of_tendsto_metrizable (f := y) (fun k => ?_) (tendsto_pi_nhds.2 hlim)
    exact measurable_from_nat.comp (measurable_krnIdx A D hA k)
  · choose a haA had using fun k => (hspec k x).1
    refine (hcl x).mem_of_tendsto (b := atTop) (f := a) ?_ (Eventually.of_forall haA)
    have hr : Tendsto krnRad atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun k =>
      dist_triangle (a k) (y k x) _) ?_)
    have h1 : Tendsto (fun k => dist (a k) (y k x)) atTop (𝓝 0) := by
      refine squeeze_zero (fun _ => dist_nonneg) (fun k => (mem_ball.1 (had k)).le) hr
    have h2 : Tendsto (fun k => dist (y k x) (limUnder atTop fun k => y k x)) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.1 (hlim x)
    simpa using h1.add h2

/-- Kuratowski–Ryll-Nardzewski with the weak measurability hypothesis for every open set. -/
theorem exists_measurable_selector_of_isOpen [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y] [Nonempty Y]
    (A : X → Set Y) (hcl : ∀ x, IsClosed (A x)) (hne : ∀ x, (A x).Nonempty)
    (hA : ∀ U : Set Y, IsOpen U → MeasurableSet {x | (A x ∩ U).Nonempty}) :
    ∃ σ : X → Y, Measurable σ ∧ ∀ x, σ x ∈ A x :=
  exists_measurable_selector A hcl hne fun _ _ => hA _ isOpen_ball

end KRN

end StatFormal.Foundations.MeasurableSelection
