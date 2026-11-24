import StatFormal.Archive.Wave22c.Statements
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs

/-!
# Route — TM `thm:split`, certification direction and level (untrusted)

* `split_null_nonpos`: under `TV ≤ α` the certified common trimming (`exists_common_of_tvDist_le`) gives one point
  `z ∈ 𝒞_α(P) ∩ 𝒞_α(Q)`; then `inf_A ⟨f,·⟩ ≤ ⟨f,z⟩ ≤ sup_B ⟨f,·⟩`.
* `split_level`: on the coverage event `T̂ ≤ sep ≤ 0`, so `{T̂ > 0} ⊆ Eᶜ`; on `E`, `T̂ > 0` forces `sep > 0`, hence
  `TV > α` by the contrapositive.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter

namespace StatFormal.Wave22c

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.ZeroSet StatFormal.Wave17a

theorem split_null_nonpos : Claims.split_null_nonpos := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ α _ _ _ hα1 htv f
  obtain ⟨gP, gQ, hP, hQ, hR⟩ := exists_common_of_tvDist_le hα1 htv
  have ha : ∫ x, gP x • φ x ∂P ∈ region φ α P := ⟨gP, hP.1, hP.2.1, hP.2.2, rfl⟩
  have hb : ∫ x, gQ x • φ x ∂Q ∈ region φ α Q := ⟨gQ, hQ.1, hQ.2.1, hQ.2.2, rfl⟩
  have hab : ∫ x, gP x • φ x ∂P = ∫ x, gQ x • φ x ∂Q := by
    rw [integral_smul_eq_withDensity P hP.1 (fun x => (hP.2.1 x).1),
      integral_smul_eq_withDensity Q hQ.1 (fun x => (hQ.2.1 x).1), hR]
  set z := ∫ x, gP x • φ x ∂P
  have h1 : (⨅ a ∈ region φ α P, ((inner ℝ f a : ℝ) : EReal)) ≤ ((inner ℝ f z : ℝ) : EReal) :=
    biInf_le (fun a => ((inner ℝ f a : ℝ) : EReal)) ha
  have h2 : ((inner ℝ f z : ℝ) : EReal) ≤ ⨆ b ∈ region φ α Q, ((inner ℝ f b : ℝ) : EReal) := by
    rw [hab]; exact le_biSup (fun b => ((inner ℝ f b : ℝ) : EReal)) hb
  unfold sepVal
  calc (⨅ a ∈ region φ α P, ((inner ℝ f a : ℝ) : EReal)) - ⨆ b ∈ region φ α Q, ((inner ℝ f b : ℝ) : EReal)
      ≤ ((inner ℝ f z : ℝ) : EReal) - ((inner ℝ f z : ℝ) : EReal) := EReal.sub_le_sub h1 h2
    _ = 0 := by rw [← EReal.coe_sub, sub_self, EReal.coe_zero]

theorem split_level : Claims.split_level := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ α δ f Ω _ μ Tlo E hφ hκ hα0 hα1 hμ hE hcov hlim
  have hcert : ∀ n, ∀ ω ∈ E n, 0 < Tlo n ω → α < StatFormal.Distances.tvDist P Q := by
    intro n ω hω hpos
    by_contra hle
    rw [not_lt] at hle
    have h0 := split_null_nonpos 𝒳 H P Q φ κ α hφ hκ hα0 hα1 hle f
    have h1 := (hcov n ω hω).trans h0
    have : (Tlo n ω : ℝ) ≤ 0 := by exact_mod_cast h1
    linarith
  refine ⟨fun htv η hη => ?_, hcert⟩
  filter_upwards [hlim η hη] with n hn
  have hsub : {ω | 0 < Tlo n ω} ⊆ (E n)ᶜ := by
    intro ω hω hωE
    have h0 := split_null_nonpos 𝒳 H P Q φ κ α hφ hκ hα0 hα1 htv f
    have h1 := (hcov n ω hωE).trans h0
    have : (Tlo n ω : ℝ) ≤ 0 := by exact_mod_cast h1
    exact absurd hω (not_lt.mpr this)
  have := hμ n
  calc μ n {ω | 0 < Tlo n ω} ≤ μ n (E n)ᶜ := measure_mono hsub
    _ = 1 - μ n (E n) := prob_compl_eq_one_sub (hE n)
    _ ≤ ENNReal.ofReal (δ + η) := by
      have hle : (μ n).real (E n) ≤ 1 := measureReal_le_one
      rw [← ofReal_measureReal (measure_ne_top _ _), ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub _ measureReal_nonneg]
      exact ENNReal.ofReal_le_ofReal (by linarith)

end StatFormal.Wave22c
