import StatFormal.Archive.Wave4b.Statements
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs

/-!
# Route — trimmed MMD `prop:deletionfloor`

For a trimming density `g` of `P` and a measurable `A`, the residual mass
`a_A = P(A) − (1−α) P'(A)` lies in `[0, α]` (`P'(A) ≤ P(A)/(1−α)` on `A` and on `Aᶜ`). Hence
`P(A) − Q(A) = (1−α)(P'(A) − Q'(A)) + a_A − b_A` gives `TV(P,Q) ≤ (1−α) TV(P',Q') + α`.
-/

noncomputable section
open MeasureTheory Set StatFormal.Distances StatFormal.TrimmedMMD.ZeroSet

namespace StatFormal.Wave4b

variable {𝒳 : Type} [MeasurableSpace 𝒳]

lemma trim_finite {P : Measure 𝒳} [IsProbabilityMeasure P] {α : ℝ} {g : 𝒳 → ℝ}
    (hg : IsTrimDensity P α g) :
    IsFiniteMeasure (P.withDensity fun x => ENNReal.ofReal (g x)) :=
  isFiniteMeasure_withDensity_ofReal hg.integrable.2

lemma trim_real {P : Measure 𝒳} [IsProbabilityMeasure P] {α : ℝ} {g : 𝒳 → ℝ}
    (hg : IsTrimDensity P α g) {A : Set 𝒳} (hA : MeasurableSet A) :
    (P.withDensity fun x => ENNReal.ofReal (g x)).real A = ∫ x in A, g x ∂P := by
  rw [Measure.real, withDensity_ofReal_apply hg.integrable (fun x => (hg.2.1 x).1) hA,
    ENNReal.toReal_ofReal (setIntegral_nonneg hA fun x _ => (hg.2.1 x).1)]

/-- The residual mass `P(A) − (1−α) ∫_A g dP` lies in `[0, α]`. -/
lemma residual_mem {P : Measure 𝒳} [IsProbabilityMeasure P] {α : ℝ} (hα1 : α < 1)
    {g : 𝒳 → ℝ} (hg : IsTrimDensity P α g) {A : Set 𝒳} (hA : MeasurableSet A) :
    0 ≤ P.real A - (1 - α) * ∫ x in A, g x ∂P ∧
      P.real A - (1 - α) * ∫ x in A, g x ∂P ≤ α := by
  have hc : 0 < 1 - α := by linarith
  have bnd : ∀ B, MeasurableSet B → (1 - α) * ∫ x in B, g x ∂P ≤ P.real B := by
    intro B _
    have h1 : ∫ x in B, g x ∂P ≤ ∫ _ in B, 1 / (1 - α) ∂P :=
      setIntegral_mono hg.integrable.integrableOn (integrable_const _).integrableOn
        fun x => (hg.2.1 x).2
    rw [setIntegral_const, smul_eq_mul] at h1
    calc (1 - α) * ∫ x in B, g x ∂P ≤ (1 - α) * (P.real B * (1 / (1 - α))) :=
          mul_le_mul_of_nonneg_left h1 hc.le
      _ = P.real B := by field_simp
  have hA' := bnd A hA
  have hAc := bnd Aᶜ hA.compl
  have hsum : ∫ x in A, g x ∂P + ∫ x in Aᶜ, g x ∂P = 1 := by
    rw [integral_add_compl hA hg.integrable, hg.2.2]
  have hPc : P.real Aᶜ = 1 - P.real A := probReal_compl_eq_one_sub hA
  constructor
  · linarith
  · rw [hPc] at hAc
    nlinarith

theorem tv_le_trim {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {α : ℝ}
    (hα1 : α < 1) {gP gQ : 𝒳 → ℝ} (hP : IsTrimDensity P α gP) (hQ : IsTrimDensity Q α gQ) :
    tvDist P Q ≤ (1 - α) * tvDist (P.withDensity fun x => ENNReal.ofReal (gP x))
      (Q.withDensity fun x => ENNReal.ofReal (gQ x)) + α := by
  have hc : 0 < 1 - α := by linarith
  haveI := trim_finite hP
  haveI := trim_finite hQ
  refine tvDist_le_of_forall fun A hA => ?_
  have hT := abs_measureReal_sub_le_tvDist
    (μ := P.withDensity fun x => ENNReal.ofReal (gP x))
    (ν := Q.withDensity fun x => ENNReal.ofReal (gQ x)) hA
  rw [trim_real hP hA, trim_real hQ hA] at hT
  obtain ⟨a0, a1⟩ := residual_mem hα1 hP hA
  obtain ⟨b0, b1⟩ := residual_mem hα1 hQ hA
  have hT' := mul_le_mul_of_nonneg_left hT hc.le
  rw [← abs_of_pos hc, ← abs_mul, abs_of_pos hc] at hT'
  rw [abs_le] at hT' ⊢
  constructor <;> nlinarith [hT'.1, hT'.2]

theorem deletionfloor : Claims.deletionfloor := by
  intro 𝒳 _ P Q _ _ α gP gQ _ hα1 hP hQ
  have hc : 0 < 1 - α := by linarith
  rw [div_le_iff₀ hc]
  have := tv_le_trim hα1 hP hQ
  linarith

theorem deletionfloor_conf : Claims.deletionfloor_conf := by
  intro 𝒳 _ P Q _ _ α L gP gQ h0 hα1 hP hQ hL
  have hc : 0 < 1 - α := by linarith
  refine ⟨?_, fun hR => hL.trans (tvDist_le_of_common hα1 hP hQ hR)⟩
  have := deletionfloor 𝒳 P Q α gP gQ h0 hα1 hP hQ
  exact le_trans (div_le_div_of_nonneg_right (by linarith) hc.le) this

end StatFormal.Wave4b
