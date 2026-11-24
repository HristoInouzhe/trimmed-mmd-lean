import StatFormal.Archive.Wave30h.Statements
import StatFormal.Archive.Wave9b.RouteField

/-!
# Route — `O_P` algebra for the frozen Wave 9b `BigOP` (untrusted; route lemmas only)

`BigOP P r X` is stated with events of probability `≥ 1 − η`. Here:
* `bigOP_iff_compl`: equivalently events with `P(Aᶜ) ≤ η` and a nonnegative constant `M`;
* `bigOP_add`, `bigOP_const_mul`, `bigOP_mono`, `bigOP_zero`, `bigOP_rate_mono` (`r ≤ C r'` eventually);
* `bigOP_add_rate` (`O_P(r) + O_P(s) = O_P(r + s)`);
* `bigOP_lipBounded_mul` (`O_P(1) · O_P(r) = O_P(r)` for a quantity bounded by `K` on the events of a
  `LipBoundedP`-type bound), in the form needed by the field theorems.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave30h

open StatFormal.Wave9b (BigOP)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma compl_le_of_ofReal_le' [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A) {a : ℝ} (ha : 0 ≤ a)
    (h : ENNReal.ofReal (1 - a) ≤ P A) : P Aᶜ ≤ ENNReal.ofReal a :=
  StatFormal.Wave9b.compl_le_of_ofReal_le hA ha h

lemma ofReal_le_of_compl_le' [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A) {a : ℝ} (ha : 0 ≤ a)
    (h : P Aᶜ ≤ ENNReal.ofReal a) : ENNReal.ofReal (1 - a) ≤ P A :=
  StatFormal.Wave9b.ofReal_le_of_compl_le hA ha h

/-- Complement form of `BigOP`, with a nonnegative constant. -/
lemma bigOP_iff_compl [IsProbabilityMeasure P] {r : ℕ → ℝ} {X : ℕ → Ω → ℝ≥0∞} (hr : ∀ n, 0 ≤ r n) :
    BigOP P r X ↔ ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 ≤ M ∧ ∃ N : ℕ, ∀ n ≥ N, ∃ A : Set Ω, MeasurableSet A ∧
      P Aᶜ ≤ ENNReal.ofReal η ∧ ∀ ω ∈ A, X n ω ≤ ENNReal.ofReal (M * r n) := by
  constructor
  · intro h η hη
    obtain ⟨M, N, hN⟩ := h η hη
    refine ⟨max M 0, le_max_right _ _, N, fun n hn => ?_⟩
    obtain ⟨A, hA, hPA, hX⟩ := hN n hn
    refine ⟨A, hA, compl_le_of_ofReal_le' hA hη.le hPA, fun ω hω => (hX ω hω).trans ?_⟩
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (hr n))
  · intro h η hη
    obtain ⟨M, -, N, hN⟩ := h η hη
    refine ⟨M, N, fun n hn => ?_⟩
    obtain ⟨A, hA, hPA, hX⟩ := hN n hn
    exact ⟨A, hA, ofReal_le_of_compl_le' hA hη.le hPA, hX⟩

lemma measure_compl_inter_le {A B : Set Ω} : P (A ∩ B)ᶜ ≤ P Aᶜ + P Bᶜ := by
  rw [compl_inter]; exact measure_union_le _ _

lemma bigOP_mono [IsProbabilityMeasure P] {r : ℕ → ℝ} {X Y : ℕ → Ω → ℝ≥0∞} (hXY : ∀ n ω, X n ω ≤ Y n ω)
    (hY : BigOP P r Y) : BigOP P r X := by
  intro η hη
  obtain ⟨M, N, hN⟩ := hY η hη
  refine ⟨M, N, fun n hn => ?_⟩
  obtain ⟨A, hA, hPA, hb⟩ := hN n hn
  exact ⟨A, hA, hPA, fun ω hω => (hXY n ω).trans (hb ω hω)⟩

/-- Monotonicity on events: it suffices that `X ≤ Y` eventually on a family of events of probability tending to
one. -/
lemma bigOP_mono_ae [IsProbabilityMeasure P] {r : ℕ → ℝ} {X Y : ℕ → Ω → ℝ≥0∞} (hr : ∀ n, 0 ≤ r n)
    (hXY : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n ≥ N, ∃ A : Set Ω, MeasurableSet A ∧ P Aᶜ ≤ ENNReal.ofReal η ∧
      ∀ ω ∈ A, X n ω ≤ Y n ω)
    (hY : BigOP P r Y) : BigOP P r X := by
  rw [bigOP_iff_compl hr] at hY ⊢
  intro η hη
  obtain ⟨M, hM, N, hN⟩ := hY (η / 2) (by positivity)
  obtain ⟨N', hN'⟩ := hXY (η / 2) (by positivity)
  refine ⟨M, hM, max N N', fun n hn => ?_⟩
  obtain ⟨A, hA, hPA, hb⟩ := hN n (le_of_max_le_left hn)
  obtain ⟨B, hB, hPB, hb'⟩ := hN' n (le_of_max_le_right hn)
  refine ⟨A ∩ B, hA.inter hB, measure_compl_inter_le.trans ?_, fun ω hω => (hb' ω hω.2).trans (hb ω hω.1)⟩
  calc P Aᶜ + P Bᶜ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add hPA hPB
    _ = ENNReal.ofReal η := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

lemma bigOP_zero [IsProbabilityMeasure P] {r : ℕ → ℝ} : BigOP P r (fun _ _ => 0) := by
  intro η hη
  refine ⟨0, 0, fun n _ => ⟨univ, MeasurableSet.univ, ?_, fun _ _ => zero_le⟩⟩
  rw [measure_univ]
  exact ENNReal.ofReal_le_one.2 (by linarith)

lemma bigOP_add_rate [IsProbabilityMeasure P] {r s : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) (hs : ∀ n, 0 ≤ s n)
    {X Y : ℕ → Ω → ℝ≥0∞} (hX : BigOP P r X) (hY : BigOP P s Y) :
    BigOP P (fun n => r n + s n) (fun n ω => X n ω + Y n ω) := by
  rw [bigOP_iff_compl hr] at hX
  rw [bigOP_iff_compl hs] at hY
  rw [bigOP_iff_compl fun n => add_nonneg (hr n) (hs n)]
  intro η hη
  obtain ⟨M, hM, N, hN⟩ := hX (η / 2) (by positivity)
  obtain ⟨M', hM', N', hN'⟩ := hY (η / 2) (by positivity)
  refine ⟨max M M', le_max_of_le_left hM, max N N', fun n hn => ?_⟩
  obtain ⟨A, hA, hPA, hb⟩ := hN n (le_of_max_le_left hn)
  obtain ⟨B, hB, hPB, hb'⟩ := hN' n (le_of_max_le_right hn)
  refine ⟨A ∩ B, hA.inter hB, measure_compl_inter_le.trans ?_, fun ω hω => ?_⟩
  · calc P Aᶜ + P Bᶜ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add hPA hPB
      _ = ENNReal.ofReal η := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  · calc X n ω + Y n ω ≤ ENNReal.ofReal (M * r n) + ENNReal.ofReal (M' * s n) :=
          add_le_add (hb ω hω.1) (hb' ω hω.2)
      _ ≤ ENNReal.ofReal (max M M' * r n) + ENNReal.ofReal (max M M' * s n) := by
          gcongr
          · exact hr n
          · exact le_max_left _ _
          · exact hs n
          · exact le_max_right _ _
      _ = ENNReal.ofReal (max M M' * (r n + s n)) := by
          rw [← ENNReal.ofReal_add (mul_nonneg (le_max_of_le_left hM) (hr n))
            (mul_nonneg (le_max_of_le_left hM) (hs n))]
          ring_nf

lemma bigOP_add [IsProbabilityMeasure P] {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) {X Y : ℕ → Ω → ℝ≥0∞}
    (hX : BigOP P r X) (hY : BigOP P r Y) : BigOP P r (fun n ω => X n ω + Y n ω) := by
  have h := bigOP_add_rate hr hr hX hY
  intro η hη
  obtain ⟨M, N, hN⟩ := h η hη
  refine ⟨2 * M, N, fun n hn => ?_⟩
  obtain ⟨A, hA, hPA, hb⟩ := hN n hn
  exact ⟨A, hA, hPA, fun ω hω => (hb ω hω).trans_eq (by ring_nf)⟩

lemma bigOP_const_mul [IsProbabilityMeasure P] {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) {X : ℕ → Ω → ℝ≥0∞} (c : ℝ≥0)
    (hX : BigOP P r X) : BigOP P r (fun n ω => (c : ℝ≥0∞) * X n ω) := by
  rw [bigOP_iff_compl hr] at hX ⊢
  intro η hη
  obtain ⟨M, hM, N, hN⟩ := hX η hη
  refine ⟨c * M, mul_nonneg (NNReal.coe_nonneg c) hM, N, fun n hn => ?_⟩
  obtain ⟨A, hA, hPA, hb⟩ := hN n hn
  refine ⟨A, hA, hPA, fun ω hω => ?_⟩
  calc (c : ℝ≥0∞) * X n ω ≤ ENNReal.ofReal c * ENNReal.ofReal (M * r n) := by
        rw [ENNReal.ofReal_coe_nnreal]; gcongr; exact hb ω hω
    _ = ENNReal.ofReal (c * M * r n) := by rw [← ENNReal.ofReal_mul (NNReal.coe_nonneg c)]; ring_nf

/-- Change of rate: `r ≤ C r'` eventually. -/
lemma bigOP_rate_mono [IsProbabilityMeasure P] {r r' : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) {C : ℝ} (hC : 0 ≤ C)
    (hrr : ∀ᶠ n in atTop, r n ≤ C * r' n) {X : ℕ → Ω → ℝ≥0∞} (hX : BigOP P r X) : BigOP P r' X := by
  rw [bigOP_iff_compl hr] at hX
  intro η hη
  obtain ⟨M, hM, N, hN⟩ := hX η hη
  obtain ⟨N', hN'⟩ := eventually_atTop.1 hrr
  refine ⟨M * C, max N N', fun n hn => ?_⟩
  obtain ⟨A, hA, hPA, hb⟩ := hN n (le_of_max_le_left hn)
  refine ⟨A, hA, ofReal_le_of_compl_le' hA hη.le hPA, fun ω hω => (hb ω hω).trans ?_⟩
  refine ENNReal.ofReal_le_ofReal ?_
  calc M * r n ≤ M * (C * r' n) := mul_le_mul_of_nonneg_left (hN' n (le_of_max_le_right hn)) hM
    _ = M * C * r' n := by ring

/-- Bounded-in-probability family (e.g. Lipschitz constants): `Y = O_P(1)` in event form. -/
def BoundedP (P : Measure Ω) (Y : ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ K : ℝ≥0, ∃ N : ℕ, ∀ n ≥ N, ∃ A : Set Ω, MeasurableSet A ∧
    ENNReal.ofReal (1 - η) ≤ P A ∧ ∀ ω ∈ A, Y n ω ≤ K

/-- `O_P(1) · O_P(r) = O_P(r)`, with the `O_P(1)` factor given on events by a constant `K` and the product bound
`X ≤ Z + K·W` holding on those events. -/
lemma bigOP_of_lip [IsProbabilityMeasure P] {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) {X Z W : ℕ → Ω → ℝ≥0∞}
    {Q : ℕ → Ω → ℝ≥0 → Prop}
    (hQ : ∀ η : ℝ, 0 < η → ∃ K : ℝ≥0, ∃ N : ℕ, ∀ n ≥ N, ∃ A : Set Ω, MeasurableSet A ∧
      ENNReal.ofReal (1 - η) ≤ P A ∧ ∀ ω ∈ A, Q n ω K)
    (hXQ : ∀ n ω K, Q n ω K → X n ω ≤ Z n ω + K * W n ω)
    (hZ : BigOP P r Z) (hW : BigOP P r W) : BigOP P r X := by
  rw [bigOP_iff_compl hr] at hZ hW ⊢
  intro η hη
  obtain ⟨M, hM, N, hN⟩ := hZ (η / 3) (by positivity)
  obtain ⟨M', hM', N', hN'⟩ := hW (η / 3) (by positivity)
  obtain ⟨K, N'', hN''⟩ := hQ (η / 3) (by positivity)
  refine ⟨M + K * M', add_nonneg hM (mul_nonneg (NNReal.coe_nonneg K) hM'), max (max N N') N'', fun n hn => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hn
  obtain ⟨A, hA, hPA, hb⟩ := hN n hn.1.1
  obtain ⟨B, hB, hPB, hb'⟩ := hN' n hn.1.2
  obtain ⟨C, hC, hPC, hq⟩ := hN'' n hn.2
  have hPC' := compl_le_of_ofReal_le' hC (by positivity : (0 : ℝ) ≤ η / 3) hPC
  refine ⟨A ∩ B ∩ C, (hA.inter hB).inter hC, ?_, fun ω hω => ?_⟩
  · calc P (A ∩ B ∩ C)ᶜ ≤ P (A ∩ B)ᶜ + P Cᶜ := measure_compl_inter_le
      _ ≤ P Aᶜ + P Bᶜ + P Cᶜ := by gcongr; exact measure_compl_inter_le
      _ ≤ ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) := by gcongr
      _ = ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  · obtain ⟨⟨hωA, hωB⟩, hωC⟩ := hω
    calc X n ω ≤ Z n ω + K * W n ω := hXQ n ω K (hq ω hωC)
      _ ≤ ENNReal.ofReal (M * r n) + ENNReal.ofReal K * ENNReal.ofReal (M' * r n) := by
          rw [ENNReal.ofReal_coe_nnreal]; gcongr
          · exact hb ω hωA
          · exact hb' ω hωB
      _ = ENNReal.ofReal ((M + K * M') * r n) := by
          rw [← ENNReal.ofReal_mul (NNReal.coe_nonneg K), ← ENNReal.ofReal_add (mul_nonneg hM (hr n))
            (mul_nonneg (NNReal.coe_nonneg K) (mul_nonneg hM' (hr n)))]
          ring_nf

end StatFormal.Wave30h
