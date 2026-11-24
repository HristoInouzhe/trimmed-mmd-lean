import StatFormal.Wave30tq.RouteEB
import StatFormal.Archive.TrimmedMMD.Lower.RouteLower

/-!
# Wave 30tq route: Corollary 2 (the down-closed lower confidence bound) — untrusted

As `cor:lower`: by the certified `TrimmedMMD.Lower.downclosed_measurable_le`, `{α̂_lo > TV}` is contained in the
rejection of the first grid level `j₀` with `TV ≤ α_{j₀}` (a true null), and is empty if there is none. That one
level's test has probability `≤ δ` by Theorem 1 (`thm1_route`) or by Corollary 1 (`cor1_test_route`), whatever the
other levels do.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.Wave30tq

theorem cor2_route : Claims.cor2 := by
  intro 𝒳 Ω₁ _ _ P Q _ _ μ₁ _ n m N J A B α useBet δ c δ₁ δ₂ g lam hAB hδ0 hδ1 hc0 hc1 hα hg hg01
    hlam hEB
  set ν := μ₁.prod ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) with hν
  set R : Fin J → Set (Ω₁ × ((Fin n → 𝒳) × (Fin m → 𝒳))) := fun j =>
    {ω | levelReject A B (useBet j) (α j) δ δ₁ δ₂ (g j ω.1) (lam j ω.1) ω.2.1 ω.2.2} with hR
  have hRbet : ∀ j, useBet j = true → R j =
      {ω | betReject (lam j ω.1) (α j) δ (pairZ (g j ω.1) A B ω.2.1 ω.2.2)} := fun j hb => by
    ext ω; simp [hR, levelReject, hb]
  have hReb : ∀ j, useBet j = false → R j =
      {ω | α j < ebLB δ₁ δ₂ (fun i => g j ω.1 (ω.2.1 i)) (fun i => g j ω.1 (ω.2.2 i))} := fun j hb => by
    ext ω; simp [hR, levelReject, hb]
  have hRm : ∀ j, MeasurableSet (R j) := fun j => by
    cases hb : useBet j
    · rw [hReb j hb]
      exact measurableSet_lt measurable_const (measurable_ebLB (hg j) δ₁ δ₂)
    · rw [hRbet j hb]
      exact measurableSet_betReject (hg j) (fun k hk => (hlam j hb k hk).1) A B (α j) δ
  have hRle : ∀ j, StatFormal.Distances.tvDist P Q ≤ α j → ν (R j) ≤ ENNReal.ofReal δ := fun j hj => by
    cases hb : useBet j
    · obtain ⟨hn, hm, h1, h2, hδ⟩ := hEB j hb
      rw [hReb j hb, hδ]
      exact cor1_test_route 𝒳 Ω₁ P Q μ₁ n m (g j) (α j) δ₁ δ₂ hn hm h1 h2 (hg j) (hg01 j) hj
    · rw [hRbet j hb]
      exact thm1_route 𝒳 Ω₁ P Q μ₁ n m N A B (α j) δ c (g j) (lam j) hAB (hα j) hδ0 hδ1 hc0 hc1
        (hg j) (hg01 j) (hlam j hb) hj
  set t := StatFormal.Distances.tvDist P Q with ht
  have ht0 : 0 ≤ t := StatFormal.Distances.tvDist_nonneg P Q
  have hD := StatFormal.TrimmedMMD.Lower.downclosed_measurable_le _ ν J α R t hRm ht0
  show ν {ω | t < StatFormal.TrimmedMMD.Lower.alphaLo α (fun j => ω ∈ R j)} ≤ ENNReal.ofReal δ
  by_cases hex : ∃ j, t ≤ α j
  · classical
    set s := Finset.univ.filter (fun j : Fin J => t ≤ α j) with hs
    have hsne : s.Nonempty := by
      obtain ⟨j, hj⟩ := hex
      exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩
    set j₀ := s.min' hsne with hj₀
    have hj₀mem : t ≤ α j₀ := (Finset.mem_filter.1 (s.min'_mem hsne)).2
    have hmin : ∀ i < j₀, α i < t := fun i hi => by
      by_contra hcon
      push Not at hcon
      have : j₀ ≤ i := s.min'_le i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon⟩)
      exact absurd hi (not_lt.2 this)
    exact (hD.2.1 j₀ hj₀mem hmin).trans (hRle j₀ hj₀mem)
  · push Not at hex
    rw [hD.2.2 hex, measure_empty]
    exact zero_le

end StatFormal.Wave30tq
