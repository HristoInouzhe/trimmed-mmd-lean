import StatFormal.Wave31to.RouteA

/-!
# Route B (untrusted): `prop:newapproxgen` (iii) and `prop:newapprox` (a), (b)

`ξ_ℋ` is a supremum of a set bounded by `u(α⋆−ε)` (route A, (ii)); its monotonicity is elementwise; the `𝒩` bound goes through a
real lower bound `ε/(2ξ) ≤ ‖g‖` for every `g ∈ 𝓕` with `err(g) ≤ ε/2` (all such `g` are nonzero since `err(0) = α⋆`).
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31to.RouteB

open StatFormal.TrimmedMMD.Unconditional StatFormal.Distances StatFormal.Wave31to.RouteA

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem dpop_nonneg (φ : 𝒳 → H) (P Q : Measure 𝒳) (α : ℝ) : 0 ≤ Dpop φ P Q α := by
  unfold Dpop setDist
  exact Real.sInf_nonneg fun r ⟨a, _, b, _, hr⟩ => hr ▸ norm_nonneg _

theorem wit_zero (φ : 𝒳 → H) : wit φ (0 : H) = fun _ => (0 : ℝ) := by
  funext x; simp [wit]

theorem zero_mem_F (φ : 𝒳 → H) : (0 : H) ∈ Fset φ := fun x => by simp [wit]

/-- The set defining `ξ_ℋ(ε)`. -/
def xiSet (φ : 𝒳 → H) (P Q : Measure 𝒳) (ε : ℝ) : Set ℝ :=
  {r | ∃ g ∈ Fset φ, g ≠ 0 ∧ r = max (ε - errFn P Q (wit φ g)) 0 / ‖g‖}

theorem xiH_eq (φ : 𝒳 → H) (P Q : Measure 𝒳) (ε : ℝ) : xiH φ P Q ε = sSup (xiSet φ P Q ε) := rfl

theorem xiSet_nonneg {φ : 𝒳 → H} {P Q : Measure 𝒳} {ε r : ℝ} (hr : r ∈ xiSet φ P Q ε) : 0 ≤ r := by
  obtain ⟨g, -, -, rfl⟩ := hr
  exact div_nonneg (le_max_right _ _) (norm_nonneg _)

section Main

variable {X : Type} [MeasurableSpace X] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K] (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {φ : X → K} {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
  (hα0 : 0 < tvDist P Q) (hα1 : tvDist P Q < 1)

include hφ hκ hα0 hα1

theorem u_nonneg {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) (tvDist P Q)) :
    0 ≤ StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - ε) := by
  unfold StatFormal.Wave31ti.uPath
  exact mul_nonneg (by linarith [hε.1, hα1]) (dpop_nonneg φ P Q _)

theorem xiSet_le {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) (tvDist P Q)) :
    ∀ r ∈ xiSet φ P Q ε, r ≤ StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - ε) := by
  rintro r ⟨g, hgF, hg, rfl⟩
  have h2 := (approxgen_ii_route X K P Q φ κ g hφ hκ hα0 hα1 hgF).2 hg ε hε
  rcases le_total (ε - errFn P Q (wit φ g)) 0 with h | h
  · rw [max_eq_right h, zero_div]; exact u_nonneg P Q hφ hκ hα0 hα1 hε
  · rw [max_eq_left h]; exact h2

theorem xiSet_bdd {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) (tvDist P Q)) : BddAbove (xiSet φ P Q ε) :=
  ⟨_, xiSet_le P Q hφ hκ hα0 hα1 hε⟩

theorem xiH_le_u {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) (tvDist P Q)) :
    xiH φ P Q ε ≤ StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - ε) :=
  Real.sSup_le (xiSet_le P Q hφ hκ hα0 hα1 hε) (u_nonneg P Q hφ hκ hα0 hα1 hε)

theorem xiH_nonneg (ε : ℝ) : 0 ≤ xiH φ P Q ε := Real.sSup_nonneg fun _ hr => xiSet_nonneg hr

/-- Every `g ∈ 𝓕` with `err(g) ≤ ε/2`, `ε ∈ (0,α⋆]`, is nonzero and has `ε/(2‖g‖) ≤ ξ_ℋ(ε)`. -/
theorem half_bound {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) (tvDist P Q)) (hεpos : 0 < ε) {g : K} (hgF : g ∈ Fset φ)
    (herr : errFn P Q (wit φ g) ≤ ε / 2) : g ≠ 0 ∧ ε / (2 * ‖g‖) ≤ xiH φ P Q ε := by
  have hg : g ≠ 0 := by
    rintro rfl
    rw [wit_zero, err_zero] at herr
    linarith [hε.2]
  refine ⟨hg, ?_⟩
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  have hmem : max (ε - errFn P Q (wit φ g)) 0 / ‖g‖ ∈ xiSet φ P Q ε := ⟨g, hgF, hg, rfl⟩
  refine le_trans ?_ (le_csSup (xiSet_bdd P Q hφ hκ hα0 hα1 hε) hmem)
  rw [max_eq_left (by linarith), div_le_div_iff₀ (by positivity) hgpos]
  nlinarith

end Main

theorem iii_a : Claims.newapproxgen_iii_a := by
  intro X K _ _ _ _ _ P Q _ _ φ κ hφ hκ hα0 hα1
  refine ⟨?_, fun ε hε => ⟨xiSet_bdd P Q hφ hκ hα0 hα1 hε, ?_, xiH_le_u P Q hφ hκ hα0 hα1 hε, ?_⟩⟩
  · intro ε₁ h₁ ε₂ h₂ h12
    rcases (xiSet φ P Q ε₁).eq_empty_or_nonempty with he | hne
    · show sSup (xiSet φ P Q ε₁) ≤ sSup (xiSet φ P Q ε₂)
      rw [he, Real.sSup_empty]; exact xiH_nonneg P Q hφ hκ hα0 hα1 ε₂
    · refine csSup_le hne ?_
      rintro r ⟨g, hgF, hg, rfl⟩
      have hmem : max (ε₂ - errFn P Q (wit φ g)) 0 / ‖g‖ ∈ xiSet φ P Q ε₂ := ⟨g, hgF, hg, rfl⟩
      refine le_trans ?_ (le_csSup (xiSet_bdd P Q hφ hκ hα0 hα1 h₂) hmem)
      exact div_le_div_of_nonneg_right (max_le_max (by linarith) le_rfl) (norm_nonneg _)
  · unfold StatFormal.Wave31ti.uPath
    have hD := dpop_nonneg φ P Q (tvDist P Q - ε)
    nlinarith [mul_nonneg (sub_nonneg.2 hε.2) hD]
  · rcases eq_or_lt_of_le hε.1 with h0 | hεpos
    · rw [← h0, ENNReal.ofReal_zero, ENNReal.zero_div]; exact bot_le
    set N := Nfun φ P Q (ε / 2)
    by_cases hN : N = ⊤
    · rw [hN, ENNReal.mul_top two_ne_zero, ENNReal.div_top]; exact bot_le
    -- some `g ∈ 𝓕` has `err(g) ≤ ε/2`
    have hex : ∃ g ∈ Fset φ, errFn P Q (wit φ g) ≤ ε / 2 := by
      by_contra hno
      simp only [not_exists, not_and, not_le] at hno
      apply hN
      simp only [N, Nfun]
      refine iInf_eq_top.2 fun g => iInf_eq_top.2 fun hgF => iInf_eq_top.2 fun hle => ?_
      exact absurd hle (not_le.2 (hno g hgF))
    obtain ⟨g₀, hg₀F, hg₀e⟩ := hex
    obtain ⟨hg₀, hξ₀⟩ := half_bound P Q hφ hκ hα0 hα1 hε hεpos hg₀F hg₀e
    have hg₀pos : 0 < ‖g₀‖ := norm_pos_iff.2 hg₀
    set ξ := xiH φ P Q ε
    have hξpos : 0 < ξ := lt_of_lt_of_le (by positivity) hξ₀
    set c := ε / (2 * ξ)
    have hcpos : 0 < c := by positivity
    have hcN : ENNReal.ofReal c ≤ N := by
      refine le_iInf fun g => le_iInf fun hgF => le_iInf fun hle => ENNReal.ofReal_le_ofReal ?_
      obtain ⟨hg, hξg⟩ := half_bound P Q hφ hκ hα0 hα1 hε hεpos hgF hle
      have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
      rw [div_le_iff₀ (by positivity)] at hξg
      show ε / (2 * ξ) ≤ ‖g‖
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc ENNReal.ofReal ε / (2 * N) ≤ ENNReal.ofReal ε / (2 * ENNReal.ofReal c) := by
          gcongr
      _ = ENNReal.ofReal ξ := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_div_of_pos (by positivity)]
          congr 1
          simp only [c]; field_simp

theorem iii_b : Claims.newapproxgen_iii_b := by
  intro X K _ _ _ _ _ P Q _ _ φ κ hφ hκ hα0 hα1 lam ε hlam hε0 hεα
  have hε : ε ∈ Icc (0 : ℝ) (tvDist P Q) := ⟨hε0.le, hεα⟩
  set Kset := {r | ∃ g ∈ Fset φ, r = errFn P Q (wit φ g) + lam * ‖g‖}
  have hKbdd : BddBelow Kset := ⟨0, by
    rintro r ⟨g, -, rfl⟩
    exact add_nonneg (err_nonneg P Q _) (mul_nonneg hlam (norm_nonneg _))⟩
  have hKne : Kset.Nonempty := ⟨_, 0, zero_mem_F φ, rfl⟩
  constructor
  · intro hlt
    have hne : (xiSet φ P Q ε).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have : xiH φ P Q ε = 0 := by rw [xiH_eq, h, Real.sSup_empty]
      linarith
    obtain ⟨r, ⟨g, hgF, hg, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hne hlt
    have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
    have hrpos : 0 < max (ε - errFn P Q (wit φ g)) 0 / ‖g‖ := lt_of_le_of_lt hlam hr
    have hmpos : 0 < max (ε - errFn P Q (wit φ g)) 0 := by
      by_contra h
      have := div_nonpos_of_nonpos_of_nonneg (not_lt.1 h) (norm_nonneg g); linarith
    have hm : max (ε - errFn P Q (wit φ g)) 0 = ε - errFn P Q (wit φ g) := by
      rcases le_total (ε - errFn P Q (wit φ g)) 0 with h | h
      · rw [max_eq_right h] at hmpos; linarith
      · exact max_eq_left h
    rw [hm, lt_div_iff₀ hgpos] at hr
    calc Kfun φ P Q lam ≤ errFn P Q (wit φ g) + lam * ‖g‖ := csInf_le hKbdd ⟨g, hgF, rfl⟩
      _ < ε := by linarith
  · intro hlt
    obtain ⟨r, ⟨g, hgF, rfl⟩, hr⟩ := exists_lt_of_csInf_lt hKne hlt
    have hg : g ≠ 0 := by
      rintro rfl
      rw [wit_zero, err_zero, norm_zero, mul_zero, add_zero] at hr
      linarith
    have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
    have hm : max (ε - errFn P Q (wit φ g)) 0 = ε - errFn P Q (wit φ g) :=
      max_eq_left (by nlinarith [mul_nonneg hlam (norm_nonneg g)])
    have hmem : max (ε - errFn P Q (wit φ g)) 0 / ‖g‖ ∈ xiSet φ P Q ε := ⟨g, hgF, hg, rfl⟩
    refine lt_of_lt_of_le ?_ (le_csSup (xiSet_bdd P Q hφ hκ hα0 hα1 hε) hmem)
    rw [hm, lt_div_iff₀ hgpos]
    linarith

theorem approx_a : Claims.newapprox_a := by
  intro X K _ _ _ _ _ P Q _ _ φ κ hφ hκ hα0 hα1 g hgF hg ε hε
  have h2 := (approxgen_ii_route X K P Q φ κ g hφ hκ hα0 hα1 hgF).2 hg ε hε
  unfold StatFormal.Wave31ti.uPath at h2
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  have hb : 0 < 1 - tvDist P Q + ε := by linarith [hε.1]
  rw [div_le_iff₀ (mul_pos hb hgpos)]
  rw [div_le_iff₀ hgpos] at h2
  have : 1 - (tvDist P Q - ε) = 1 - tvDist P Q + ε := by ring
  rw [this] at h2
  nlinarith

theorem approx_b : Claims.newapprox_b := by
  intro X K _ _ _ _ _ P Q _ _ φ κ hφ hκ hα0 hα1 ε hε
  obtain ⟨-, h⟩ := iii_a X K P Q φ κ hφ hκ hα0 hα1
  obtain ⟨-, hu, hξ, hN⟩ := h ε hε
  exact hN.trans (ENNReal.ofReal_le_ofReal (hξ.trans hu))

end StatFormal.Wave31to.RouteB
