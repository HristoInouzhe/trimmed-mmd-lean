import StatFormal.Wave30tu.Crossing.Statements
import StatFormal.Wave30tu.Full.Route

/-!
# Wave 30tu — `lem:crossing` without continuity of the threshold (untrusted proof route)

Upward closure and `D̂_{α̂} ≤ τ(α̂+)` need only monotonicity of `τ` (`RouteBasic`). Measurability: `α̂ ≥ 0` always (`sInf ∅ = 0`), and for
`a ∈ (0,1]`-type levels `{α̂ < a} = ⋃_{q ∈ ℚ ∩ (0, min(a,1))} {D̂_q ≤ τ(q)} ∪ {S = ∅}`, where
`{S = ∅} = {D̂_0 > τ(0)} ∩ ⋂_{q ∈ ℚ ∩ (0,1)} {D̂_q > τ(q)}` (a nonempty `S` contains `(α̂,1)`, hence a rational).
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tu.Crossing

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tl StatFormal.Wave30tu StatFormal.Wave30tu.Full

theorem alphaHat_nonneg' (D τ : ℝ → ℝ) : 0 ≤ alphaHat D τ := Real.sInf_nonneg fun _ h => h.1.1

theorem alphaHat_lt_one' (D τ : ℝ → ℝ) : alphaHat D τ < 1 := by
  rcases (crossSet D τ).eq_empty_or_nonempty with h | h
  · unfold alphaHat; rw [h, Real.sInf_empty]; exact one_pos
  · exact alphaHat_lt_one h

theorem crossSet_empty_iff {D τ : ℝ → ℝ} (hDa : AntitoneOn D (Ico 0 1)) (hτm : MonotoneOn τ (Ico 0 1)) :
    crossSet D τ = ∅ ↔ ¬ D 0 ≤ τ 0 ∧ ∀ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < 1 → ¬ D q ≤ τ q := by
  constructor
  · intro h
    refine ⟨fun h0 => ?_, fun q hq hle => ?_⟩
    · have : (0 : ℝ) ∈ crossSet D τ := ⟨⟨le_rfl, one_pos⟩, h0⟩
      rw [h] at this; exact this
    · have : (q : ℝ) ∈ crossSet D τ := ⟨⟨hq.1.le, hq.2⟩, hle⟩
      rw [h] at this; exact this
  · rintro ⟨_, hq⟩
    by_contra hne
    have hne' := Set.nonempty_iff_ne_empty.2 hne
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (alphaHat_lt_one hne')
    have hq0 : 0 < (q : ℝ) := lt_of_le_of_lt (alphaHat_nonneg hne') hq1
    exact hq q ⟨hq0, hq2⟩ (Ioo_subset_crossSet hDa hτm hne' ⟨hq1, hq2⟩).2

section

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem measurable_alphaHat_nc {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {τ : ℝ → ℝ} {n m : ℕ} (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hτm : MonotoneOn τ (Ico 0 1)) :
    Measurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => alphaHat (Demp φ z.1 z.2) τ := by
  refine measurable_of_Iio fun a => ?_
  by_cases ha : 0 < a
  · set U : Set ((Fin n → 𝒳) × (Fin m → 𝒳)) :=
      ⋃ q : ℚ, ⋃ (_ : 0 < (q : ℝ) ∧ (q : ℝ) < min a 1), {z | Demp φ z.1 z.2 q ≤ τ q}
    set Em : Set ((Fin n → 𝒳) × (Fin m → 𝒳)) := {z | ¬ Demp φ z.1 z.2 0 ≤ τ 0} ∩
      ⋂ q : ℚ, ⋂ (_ : 0 < (q : ℝ) ∧ (q : ℝ) < 1), {z | ¬ Demp φ z.1 z.2 q ≤ τ q}
    have heq : (fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => alphaHat (Demp φ z.1 z.2) τ) ⁻¹' Iio a = U ∪ Em := by
      ext z
      have hDa := Demp_antitoneOn φ hn hm z.1 z.2
      have hiff := crossSet_empty_iff hDa hτm (τ := τ)
      simp only [mem_preimage, mem_Iio, mem_union, U, Em, mem_iUnion, mem_inter_iff, mem_iInter, mem_setOf_eq,
        exists_prop]
      constructor
      · intro h
        rcases (crossSet (Demp φ z.1 z.2) τ).eq_empty_or_nonempty with he | hne
        · exact Or.inr ⟨(hiff.1 he).1, fun q hq => (hiff.1 he).2 q hq⟩
        · left
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min h (alphaHat_lt_one hne))
          have hq0 : 0 < (q : ℝ) := lt_of_le_of_lt (alphaHat_nonneg hne) hq1
          exact ⟨q, ⟨hq0, hq2⟩, (Ioo_subset_crossSet hDa hτm hne ⟨hq1, hq2.trans_le (min_le_right _ _)⟩).2⟩
      · rintro (⟨q, ⟨hq0, hqa⟩, hq⟩ | ⟨h0, hq⟩)
        · have hq1 : (q : ℝ) < 1 := hqa.trans_le (min_le_right _ _)
          exact (alphaHat_le_of_mem ⟨⟨hq0.le, hq1⟩, hq⟩).trans_lt (hqa.trans_le (min_le_left _ _))
        · have he := hiff.2 ⟨h0, fun q hq' => hq q hq'⟩
          unfold alphaHat; rw [he, Real.sInf_empty]; exact ha
    rw [heq]
    refine MeasurableSet.union (MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_)
      ((measurableSet_le (measurable_Demp hφ hn hm le_rfl one_pos) measurable_const).compl.inter
        (MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq =>
          (measurableSet_le (measurable_Demp hφ hn hm hq.1.le hq.2) measurable_const).compl))
    exact measurableSet_le (measurable_Demp hφ hn hm hq.1.le (hq.2.trans_le (min_le_right _ _))) measurable_const
  · push_neg at ha
    convert MeasurableSet.empty
    ext z
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
    exact ha.trans (alphaHat_nonneg' _ _)

end

theorem crossing_nc : Claims.crossing_nc := by
  intro 𝒳 H _ _ _ _ _ φ κ τ n m hφ hκ hn hm _ hτm
  refine ⟨fun x y hne => ?_, fun hne a => ?_, measurable_alphaHat_nc hφ hn hm hτm⟩
  · have hD := Demp_continuousOn hφ hκ hn hm x y
    have hDa := Demp_antitoneOn φ hn hm x y
    exact ⟨⟨hD, hDa⟩, Ioo_subset_crossSet hDa hτm hne, le_tauRight hD hDa hτm hne⟩
  · ext z
    simp only [mem_setOf_eq, mem_iUnion, exists_prop]
    have hnz := hne z.1 z.2
    have hDa := Demp_antitoneOn φ hn hm z.1 z.2
    have hlt1 := alphaHat_lt_one hnz
    constructor
    · intro ha
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min ha hlt1)
      have hq0 : 0 < (q : ℝ) := lt_of_le_of_lt (alphaHat_nonneg hnz) hq1
      exact ⟨q, ⟨hq0, hq2.trans_le (min_le_left _ _)⟩,
        (Ioo_subset_crossSet hDa hτm hnz ⟨hq1, hq2.trans_le (min_le_right _ _)⟩).2⟩
    · rintro ⟨q, ⟨hq0, hqa⟩, hq⟩
      by_cases hq1 : (q : ℝ) < 1
      · exact (alphaHat_le_of_mem ⟨⟨hq0.le, hq1⟩, hq⟩).trans_lt hqa
      · exact hlt1.trans_le ((not_lt.1 hq1).trans hqa.le)

theorem crossing_full : Claims.crossing_full := by
  intro 𝒳 H _ _ _ _ _ φ κ D δ n m hφ hκ hD hδ0 hδ1 hn hm
  rcases isEmpty_or_nonempty 𝒳 with h𝒳 | h𝒳
  · refine ⟨fun x _ _ => isEmptyElim (x ⟨0, hn⟩), fun s _ => ?_⟩
    have : (fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m)) ⁻¹' s
        = ∅ := Set.eq_empty_of_forall_notMem fun z _ => isEmptyElim (z.1 ⟨0, hn⟩)
    rw [this]; exact MeasurableSet.empty
  · have hv := (tauFull_threshold 𝒳 H φ κ D δ n m h𝒳 hφ hκ hD hδ0 hδ1 hn hm).1
    obtain ⟨hpath, -, hmeas⟩ := crossing_nc 𝒳 H φ κ _ n m hφ hκ hn hm hv.1 hv.2.1
    exact ⟨fun x y hne => (hpath x y hne).2, hmeas⟩

end StatFormal.Wave30tu.Crossing
