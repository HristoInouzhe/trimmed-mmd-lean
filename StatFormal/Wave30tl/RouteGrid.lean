import StatFormal.Wave30tl.RouteConfset
import StatFormal.Wave30tl.Revision.Statements

/-!
# Wave 30tl — `rem:grid`, both conventions (untrusted proof route)

By `lem:crossing` a grid level `g ∈ [0,1)` is not rejected iff `α̂ ≤ g`. Mesh at `t = α̂` gives a non-rejected level in
`[α̂, α̂ + h]` (or `α̂ + h ≥ 1` for a grid of `[0,1)`); if every level is rejected, every level lies below `α̂`. On the event of
`thm:consistency` (i), `α̂ ≤ α*`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tl

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

section Grid

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem lastRejected_lt {φ : 𝒳 → H} {κ δ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳)
    {G : Finset ℝ} (hG : ∀ g ∈ G, 0 ≤ g ∧ g < 1) {b : ℝ}
    (hb : LastRejected G (Demp φ x y) (fun α => tau κ α δ n m) b) :
    b < alphaHat (Demp φ x y) (fun α => tau κ α δ n m) :=
  lt_alphaHat_of_reject hφ hκ hδ0 hδ1 hn hm x y (hG b hb.1.1).1 (hG b hb.1.1).2 hb.1.2

theorem gridReturn_le {φ : 𝒳 → H} {κ δ h : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳)
    {G : Finset ℝ} (hG : MeshGrid G h) {a : ℝ} (ha : GridReturn G (Demp φ x y) (fun α => tau κ α δ n m) a) :
    a ≤ alphaHat (Demp φ x y) (fun α => tau κ α δ n m) + h := by
  set ah := alphaHat (Demp φ x y) (fun α => tau κ α δ n m)
  have hah := alphaHat_mem_crossSet hφ hκ hδ0 hδ1 hn hm x y
  rcases ha with ⟨⟨haG, haD⟩, hmin⟩ | ⟨hall, ⟨haG, -⟩⟩
  · have hle : ah ≤ a :=
      (mem_crossSet_iff_le hφ hκ hδ0 hδ1 hn hm x y (hG.1 a haG).1 (hG.1 a haG).2).2 haD
    obtain ⟨g, hgG, hag, hgh⟩ := hG.2 ah hah.1.1 ⟨a, haG, hle⟩
    have hgD : Demp φ x y g ≤ tau κ g δ n m :=
      (mem_crossSet_iff_le hφ hκ hδ0 hδ1 hn hm x y (hG.1 g hgG).1 (hG.1 g hgG).2).1 hag
    exact (hmin ⟨hgG, hgD⟩).trans hgh
  · have hlt : a < ah := lt_alphaHat_of_reject hφ hκ hδ0 hδ1 hn hm x y (hG.1 a haG).1 (hG.1 a haG).2
      (hall a haG)
    obtain ⟨g, hgG, hg0, hgh⟩ := hG.2 0 le_rfl ⟨a, haG, (hG.1 a haG).1⟩
    linarith

theorem gridReturnOne_le {φ : 𝒳 → H} {κ δ h : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳)
    {G : Finset ℝ} (hG : Revision.MeshGridUnit G h) {a : ℝ}
    (ha : Revision.GridReturnOne G (Demp φ x y) (fun α => tau κ α δ n m) a) :
    a ≤ alphaHat (Demp φ x y) (fun α => tau κ α δ n m) + h := by
  set ah := alphaHat (Demp φ x y) (fun α => tau κ α δ n m)
  have hah := alphaHat_mem_crossSet hφ hκ hδ0 hδ1 hn hm x y
  rcases ha with ⟨⟨haG, -⟩, hmin⟩ | ⟨hall, rfl⟩
  · rcases hG.2 ah hah.1.1 hah.1.2 with h1 | ⟨g, hgG, hag, hgh⟩
    · linarith [(hG.1 a haG).2]
    · have hgD : Demp φ x y g ≤ tau κ g δ n m :=
        (mem_crossSet_iff_le hφ hκ hδ0 hδ1 hn hm x y (hG.1 g hgG).1 (hG.1 g hgG).2).1 hag
      exact (hmin ⟨hgG, hgD⟩).trans hgh
  · rcases hG.2 ah hah.1.1 hah.1.2 with h1 | ⟨g, hgG, hag, -⟩
    · exact h1
    · have := lt_alphaHat_of_reject hφ hκ hδ0 hδ1 hn hm x y (hG.1 g hgG).1 (hG.1 g hgG).2 (hall g hgG)
      linarith

end Grid

theorem grid_mesh : Claims.grid_mesh := by
  intro 𝒳 H _ _ _ _ _ φ κ δ h n m G hφ hκ hδ0 hδ1 hn hm hG x y
  exact ⟨fun a ha => gridReturn_le hφ hκ hδ0 hδ1 hn hm x y hG ha,
    fun b hb => lastRejected_lt hφ hκ hδ0 hδ1 hn hm x y hG.1 hb⟩

theorem grid_prob : Claims.grid_prob := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ n m hφ hκ htv hδ0 hδ1 hn hm
  obtain ⟨E, hEm, hEp, hE⟩ := exists_event P Q hφ hκ hδ0 hδ1 hn hm
  refine ⟨E, hEm, hEp, fun z hz G h hG => ?_⟩
  have hle := alphaHat_le_of_event ⟨StatFormal.Distances.tvDist_nonneg P Q, htv⟩
    (Dpop_tv_eq_zero P Q hφ hκ htv) (hE z hz)
  refine ⟨fun a ha => (gridReturn_le hφ hκ hδ0 hδ1 hn hm z.1 z.2 hG ha).trans (by linarith),
    fun b hb => (lastRejected_lt hφ hκ hδ0 hδ1 hn hm z.1 z.2 hG.1 hb).trans_le hle⟩

end StatFormal.Wave30tl

namespace StatFormal.Wave30tl.Revision

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tl

theorem grid_mesh_one : Claims.grid_mesh_one := by
  intro 𝒳 H _ _ _ _ _ φ κ δ h n m G hφ hκ hδ0 hδ1 hn hm hG x y
  exact ⟨fun a ha => gridReturnOne_le hφ hκ hδ0 hδ1 hn hm x y hG ha,
    fun b hb => lastRejected_lt hφ hκ hδ0 hδ1 hn hm x y hG.1 hb⟩

theorem grid_prob_one : Claims.grid_prob_one := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ n m hφ hκ htv hδ0 hδ1 hn hm
  obtain ⟨E, hEm, hEp, hE⟩ := exists_event P Q hφ hκ hδ0 hδ1 hn hm
  refine ⟨E, hEm, hEp, fun z hz G h hG => ?_⟩
  have hle := StatFormal.TrimmedMMD.alphaHat_le_of_event ⟨StatFormal.Distances.tvDist_nonneg P Q, htv⟩
    (Dpop_tv_eq_zero P Q hφ hκ htv) (hE z hz)
  refine ⟨fun a ha => (gridReturnOne_le hφ hκ hδ0 hδ1 hn hm z.1 z.2 hG ha).trans (by linarith),
    fun b hb => (lastRejected_lt hφ hκ hδ0 hδ1 hn hm z.1 z.2 hG.1 hb).trans_le hle⟩

end StatFormal.Wave30tl.Revision
