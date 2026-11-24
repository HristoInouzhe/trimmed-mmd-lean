import StatFormal.Archive.Wave18b.Statements
import StatFormal.Lib.Tax.Tax
import StatFormal.Archive.Wave11a.Proofs
import StatFormal.Archive.Wave4b.Proofs

/-!
# Route: robust equality `lem:projection` (untrusted)

* A coupling `γ ∈ Π(P̂, Q)` on `Fin k × 𝒵` maps to `γ^X = (id × π)_#γ ∈ Π(P̂^X, Q^X)` with
  `E_{γ^X} c_X ≤ E_γ c_𝒵` (domination) and, by data processing (`klDiv_map_le`; `klRef` differs from `klDiv` by
  the mass `ν(𝒵) = (π_#ν)(X)`), `KL(γ^X ‖ P̂ ⊗ π_#ν) ≤ KL(γ ‖ P̂ ⊗ ν)` (`(id × π)_#(P̂ ⊗ ν) = P̂ ⊗ π_#ν`).
* Ball inclusion and worst cases follow; the disparity of a covariate rule is `(h∘π)_#Q = h_#(π_#Q)`.
* Certificate: the projected sets are `lem:kernel` sets (certified `Wave11a.kernel_iff`), so the worst case is
  `≤ F(h)` of `Wave4b.Findep`, and `F ≤ F̄` is the certified `Wave4b.certificate_independent`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set TauCeti InformationTheory Filter
open scoped ENNReal

namespace StatFormal.Wave18b

open StatFormal.RobustEquality StatFormal.RobustEquality.Tax StatFormal.RobustEquality.SemidualStrong
  StatFormal.RobustEquality.Semidual StatFormal.RobustEquality.Certificate StatFormal.Wave4b

variable {Z X : Type} [MeasurableSpace Z] [MeasurableSpace X]

/-- Data processing for the paper's `KL` (`klRef`). -/
lemma klRef_map_le {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (γ ρ : Measure α)
    [IsProbabilityMeasure γ] [IsFiniteMeasure ρ] {g : α → β} (hg : Measurable g) :
    klRef (γ.map g) (ρ.map g) ≤ klRef γ ρ := by
  have hmass : (ρ.map g).real univ = ρ.real univ := by
    rw [measureReal_def, measureReal_def, Measure.map_apply hg MeasurableSet.univ, preimage_univ]
  have hDP := klDiv_map_le (μ := γ) (ν := ρ) hg
  have : IsProbabilityMeasure (γ.map g) := inferInstance
  rw [StatFormal.Foundations.Tax.klRef_eq_klDiv (γ.map g) (ρ.map g),
    StatFormal.Foundations.Tax.klRef_eq_klDiv γ ρ, hmass]
  by_cases h : klDiv γ ρ = ⊤
  · simp only [h, ↓reduceIte, le_top]
  · have h' : klDiv (γ.map g) (ρ.map g) ≠ ⊤ := ne_top_of_le_ne_top h hDP
    simp only [h, h', ↓reduceIte]
    exact EReal.coe_le_coe_iff.2 (by linarith [ENNReal.toReal_mono h hDP])

lemma setting_bound {k : ℕ} {ε : ℝ} {a : Fin k → ℝ} {c : Fin k → Z → ℝ} (hs : Setting ε a c) :
    Measurable (fun z : Fin k × Z => c z.1 z.2) ∧ ∃ B, ∀ z : Fin k × Z, |c z.1 z.2| ≤ B := by
  obtain ⟨-, -, -, hm, B, hB⟩ := hs
  exact ⟨measurable_from_prod_countable_right hm, B, fun z => hB _ _⟩

lemma integrable_of_setting {k : ℕ} {ε : ℝ} {a : Fin k → ℝ} {c : Fin k → Z → ℝ} (hs : Setting ε a c)
    (γ : Measure (Fin k × Z)) [IsFiniteMeasure γ] : Integrable (fun z : Fin k × Z => c z.1 z.2) γ := by
  obtain ⟨hm, B, hB⟩ := setting_bound hs
  exact Integrable.of_bound hm.aestronglyMeasurable B (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hB z)

theorem projection_disc : Claims.projection_disc := by
  intro Z X _ _ k ε a cZ cX π ν Q _ _ hsZ hsX hπ hdom
  refine le_sInf ?_
  rintro v ⟨γ, hγp, hγ1, hγ2, rfl⟩
  have hg : Measurable (Prod.map (id : Fin k → Fin k) π) := measurable_id.prodMap hπ
  set γX := γ.map (Prod.map (id : Fin k → Fin k) π) with hγX
  have hγXp : IsProbabilityMeasure γX := inferInstance
  have hγX1 : γX.map Prod.fst = muDisc a := by
    rw [hγX, Measure.map_map measurable_fst hg]; exact hγ1
  have hγX2 : γX.map Prod.snd = Q.map π := by
    rw [hγX, Measure.map_map measurable_snd hg, ← hγ2, Measure.map_map hπ measurable_snd]; rfl
  refine sInf_le_of_le ⟨γX, hγXp, hγX1, hγX2, rfl⟩ ?_
  have hcost : ∫ z, cX z.1 z.2 ∂γX ≤ ∫ z, cZ z.1 z.2 ∂γ := by
    rw [hγX, integral_map hg.aemeasurable (setting_bound hsX).1.aestronglyMeasurable]
    refine integral_mono ?_ (integrable_of_setting hsZ γ) fun z => hdom z.1 z.2
    obtain ⟨hm, B, hB⟩ := setting_bound hsX
    exact Integrable.of_bound (hm.comp hg).aestronglyMeasurable B (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hB _)
  have : IsProbabilityMeasure (muDisc a) :=
    StatFormal.Foundations.SemiDiscrete.isProb_muDisc hsZ.2.1 hsZ.2.2.1
  have hprod : (muDisc a).prod (ν.map π) = ((muDisc a).prod ν).map (Prod.map id π) := by
    rw [← Measure.map_prod_map _ _ measurable_id hπ, Measure.map_id]
  have hkl : klRef γX ((muDisc a).prod (ν.map π)) ≤ klRef γ ((muDisc a).prod ν) := by
    rw [hprod, hγX]; exact klRef_map_le γ _ hg
  exact add_le_add (EReal.coe_le_coe_iff.2 hcost)
    (StatFormal.Foundations.Tax.coe_mul_le_coe_mul hsZ.1.le hkl)

theorem projection_ball : Claims.projection_ball := by
  intro Z X _ _ k ε a cZ cX π 𝒩 r Q hsZ hsX hπ hdom hN hQ
  obtain ⟨hQp, ν, hν, hW⟩ := hQ
  have := hN ν hν
  refine ⟨inferInstance, ν.map π, ⟨ν, hν, rfl⟩, ?_⟩
  exact (projection_disc Z X k ε a cZ cX π ν Q hsZ hsX hπ hdom).trans hW

theorem projection_worst : Claims.projection_worst := by
  intro Z X _ _ k₀ k₁ ε a₀ cZ₀ cX₀ a₁ cZ₁ cX₁ π 𝒩₀ 𝒩₁ r₀ r₁ h hsZ₀ hsX₀ hsZ₁ hsX₁ hπ hh hd₀ hd₁ hN₀ hN₁
  refine iSup₂_le fun Q₀ hQ₀ => iSup₂_le fun Q₁ hQ₁ => ?_
  rw [← Measure.map_map hh hπ, ← Measure.map_map hh hπ]
  exact le_iSup₂_of_le (Q₀.map π) (projection_ball Z X k₀ ε a₀ cZ₀ cX₀ π 𝒩₀ r₀ Q₀ hsZ₀ hsX₀ hπ hd₀ hN₀ hQ₀)
    (le_iSup₂_of_le (Q₁.map π) (projection_ball Z X k₁ ε a₁ cZ₁ cX₁ π 𝒩₁ r₁ Q₁ hsZ₁ hsX₁ hπ hd₁ hN₁ hQ₁) le_rfl)

lemma refClass_push {𝒩 : Set (Measure Z)} (h : RefClass 𝒩) {π : Z → X} (hπ : Measurable π) :
    RefClass (pushClass π 𝒩) := by
  rintro _ ⟨ν, hν, rfl⟩
  obtain ⟨hf, h0, h1⟩ := h ν hν
  refine ⟨Measure.isFiniteMeasure_map ν π, ?_, ?_⟩ <;> rw [Measure.map_apply hπ MeasurableSet.univ, preimage_univ]
  · exact h0
  · exact h1

theorem projection_certificate : Claims.projection_certificate := by
  intro Z X _ _ n₀ n₁ z₀ z₁ cZ c π ε r₀ r₁ lam₀ lam₁ h 𝒩₀ 𝒩₁ hn₀ hn₁ hε hl₀ hl₁ hc hc0 hcB hcZm hcZB hdom hπ hh hhB hR₀ hR₁
  obtain ⟨B, hB⟩ := hcB
  obtain ⟨BZ, hBZ⟩ := hcZB
  have hcrow : ∀ y, Measurable (c y) := fun y => hc.comp (measurable_const.prodMk measurable_id)
  have hcabs : ∃ B', ∀ a b, |c a b| ≤ B' := ⟨B, fun a b => by rw [abs_of_nonneg (hc0 a b)]; exact hB a b⟩
  have setZ : ∀ (n : ℕ) (z : Fin n → Z), 0 < n → Setting ε (fun _ => (1 : ℝ) / n) (fun i => cZ (z i)) :=
    fun n z hn => ⟨hε, fun _ => by positivity, by simp [Finset.card_univ]; field_simp, fun i => hcZm (z i),
      BZ, fun i y => hBZ _ _⟩
  have setX : ∀ (n : ℕ) (z : Fin n → Z), 0 < n →
      Setting ε (fun _ => (1 : ℝ) / n) (fun i => c ((π ∘ z) i)) :=
    fun n z hn => ⟨hε, fun _ => by positivity, by simp [Finset.card_univ]; field_simp, fun i => hcrow _,
      B, fun i y => by rw [abs_of_nonneg (hc0 _ _)]; exact hB _ _⟩
  have hN₀ : ∀ ν ∈ 𝒩₀, IsFiniteMeasure ν := fun ν hν => (hR₀ ν hν).1
  have hN₁ : ∀ ν ∈ 𝒩₁, IsFiniteMeasure ν := fun ν hν => (hR₁ ν hν).1
  have hP₀ := refClass_push hR₀ hπ
  have hP₁ := refClass_push hR₁ hπ
  have hF := certificate_independent X n₀ n₁ (π ∘ z₀) (π ∘ z₁) c ε r₀ r₁ lam₀ lam₁ h (pushClass π 𝒩₀)
    (pushClass π 𝒩₁) hn₀ hn₁ hε hl₀ hl₁ hc hc0 ⟨B, hB⟩ hh hhB hP₀ hP₁
  refine le_trans ?_ hF
  refine iSup₂_le fun Q₀ hQ₀ => iSup₂_le fun Q₁ hQ₁ => ?_
  have hb₀ := projection_ball Z X n₀ ε _ _ (fun i => c ((π ∘ z₀) i)) π 𝒩₀ _ Q₀ (setZ n₀ z₀ hn₀) (setX n₀ z₀ hn₀) hπ
    (fun i z => hdom _ _) hN₀ hQ₀
  have hb₁ := projection_ball Z X n₁ ε _ _ (fun i => c ((π ∘ z₁) i)) π 𝒩₁ _ Q₁ (setZ n₁ z₁ hn₁) (setX n₁ z₁ hn₁) hπ
    (fun i z => hdom _ _) hN₁ hQ₁
  have hpQ₀ : IsProbabilityMeasure (Q₀.map π) := hb₀.1
  have hpQ₁ : IsProbabilityMeasure (Q₁.map π) := hb₁.1
  have hk₀ := (StatFormal.Wave11a.kernel_iff X n₀ (π ∘ z₀) c ε r₀ (pushClass π 𝒩₀) (Q₀.map π) hn₀ hε hcrow hcabs
    (fun ν hν => (hP₀ ν hν).1)).1 hb₀
  have hk₁ := (StatFormal.Wave11a.kernel_iff X n₁ (π ∘ z₁) c ε r₁ (pushClass π 𝒩₁) (Q₁.map π) hn₁ hε hcrow hcabs
    (fun ν hν => (hP₁ ν hν).1)).1 hb₁
  rw [← Measure.map_map hh hπ, ← Measure.map_map hh hπ]
  unfold Findep
  exact le_iSup_of_le (Q₀.map π) (le_iSup_of_le (Q₁.map π)
    (le_iSup_of_le ⟨⟨hpQ₀, hk₀⟩, ⟨hpQ₁, hk₁⟩⟩ le_rfl))

end StatFormal.Wave18b
