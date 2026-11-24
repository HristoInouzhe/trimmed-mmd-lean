import StatFormal.Archive.Wave18b.Statements
import StatFormal.Lib.Tax.Tax
import StatFormal.Archive.RobustEquality.Tax.Proofs
import StatFormal.Archive.Wave11a.Proofs
import StatFormal.Archive.Wave4b.Proofs

/-!
# Route: robust equality `thm:classcoverage` (untrusted)

* On `A_s ∩ T_s`: `OT_ε(P̂_s,P_s) + ε τ_𝒩(P_s) ≤ r̂^OT_s + ε τ̂_s`; with an attaining reference `ν*`,
  `W^{ν*}_ε = OT_ε + ε KL(P_s‖ν*)` (certified `tax_identity`), so `P_s ∈ 𝓑^𝒩_s(r̂_s)`, i.e. a `lem:kernel` witness
  (certified `Wave11a.kernel_iff`); then `W₂²(h#P₀,h#P₁) ≤ F(h) ≤ F̄` (certified `Wave4b.certificate_independent`).
* Union bound over the four events.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter TauCeti
open scoped ENNReal

namespace StatFormal.Wave18b

open StatFormal.RobustEquality StatFormal.RobustEquality.Tax StatFormal.RobustEquality.SemidualStrong
  StatFormal.RobustEquality.Certificate StatFormal.Wave4b

lemma prob_inter_ge' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {S T : Set Ω}
    {a b : ℝ} (hT : MeasurableSet T) (hS : ENNReal.ofReal (1 - a) ≤ μ S) (hTp : ENNReal.ofReal (1 - b) ≤ μ T) :
    ENNReal.ofReal (1 - (a + b)) ≤ μ (S ∩ T) := by
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)] at hS hTp ⊢
  have hU := measureReal_union_add_inter (μ := μ) (s := S) hT
  have h1 : μ.real (S ∪ T) ≤ 1 := measureReal_le_one
  change 1 - a ≤ μ.real S at hS
  change 1 - b ≤ μ.real T at hTp
  change 1 - (a + b) ≤ μ.real (S ∩ T)
  linarith

lemma mem_ball_of_bounds {K : Type} [MeasurableSpace K] {n : ℕ} (hn : 0 < n) {x : Fin n → K} {c : K → K → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hc : Measurable (Function.uncurry c)) {B : ℝ} (hB : ∀ a b, |c a b| ≤ B)
    {𝒩 : Set (Measure K)} (hR : RefClass 𝒩) {P : Measure K} [IsProbabilityMeasure P]
    (hatt : ∃ ν ∈ 𝒩, klRef P ν = tax 𝒩 P) {r τ : ℝ}
    (hOT : OTdisc ε (fun _ => (1 : ℝ) / n) (fun i => c (x i)) P ≤ (r : EReal)) (hτ : tax 𝒩 P ≤ (τ : EReal)) :
    InBall x c ε (r + ε * τ) 𝒩 P := by
  have hs : Setting ε (fun _ : Fin n => (1 : ℝ) / n) (fun i => c (x i)) := by
    refine ⟨hε, fun _ => by positivity, ?_, fun i => hc.comp (measurable_const.prodMk measurable_id),
      B, fun i y => hB _ _⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  obtain ⟨ν, hν, heq⟩ := hatt
  have : IsFiniteMeasure ν := (hR ν hν).1
  have hball : P ∈ ballN 𝒩 ε (fun _ : Fin n => (1 : ℝ) / n) (fun i => c (x i)) ((r + ε * τ : ℝ) : EReal) := by
    refine ⟨inferInstance, ν, hν, ?_⟩
    rw [tax_identity K n ε _ _ ν P hs, heq, EReal.coe_add, EReal.coe_mul]
    exact add_le_add hOT (StatFormal.Foundations.Tax.coe_mul_le_coe_mul hε.le hτ)
  have hcrow : ∀ y, Measurable (c y) := fun y => hc.comp (measurable_const.prodMk measurable_id)
  exact ⟨inferInstance, (StatFormal.Wave11a.kernel_iff K n x c ε _ 𝒩 P hn hε hcrow ⟨B, hB⟩
    (fun ν hν => (hR ν hν).1)).1 hball⟩

theorem classcoverage : Claims.classcoverage := by
  intro K Ω _ _ μ _ n₀ n₁ x₀ x₁ c ε 𝒩₀ 𝒩₁ P₀ P₁ _ _ rOT₀ rOT₁ τ₀ τ₁ a₀ a₁ a₀' a₁' A₀ A₁ T₀ T₁
    hn₀ hn₁ hε hc hc0 hcB hR₀ hR₁ hatt₀ hatt₁ hA₀ hA₁ hT₀ hT₁ hpA₀ hpA₁ hpT₀ hpT₁ hOT₀ hOT₁ hτ₀ hτ₁
  obtain ⟨B, hB⟩ := hcB
  have hBabs : ∀ a b, |c a b| ≤ B := fun a b => by rw [abs_of_nonneg (hc0 a b)]; exact hB a b
  refine ⟨(A₀ ∩ T₀) ∩ (A₁ ∩ T₁), (hA₀.inter hT₀).inter (hA₁.inter hT₁), ?_, ?_⟩
  · have h0 := prob_inter_ge' hT₀ hpA₀ hpT₀
    have h1 := prob_inter_ge' hT₁ hpA₁ hpT₁
    have h := prob_inter_ge' (hA₁.inter hT₁) h0 h1
    rw [show a₀ + a₀' + a₁ + a₁' = a₀ + a₀' + (a₁ + a₁') by ring]
    exact h
  · rintro ω ⟨⟨hω₀, hωT₀⟩, ⟨hω₁, hωT₁⟩⟩ h lam₀ lam₁ hh hhB hl₀ hl₁
    have hb₀ := mem_ball_of_bounds hn₀ hε hc hBabs hR₀ hatt₀ (hOT₀ ω hω₀) (hτ₀ ω hωT₀)
    have hb₁ := mem_ball_of_bounds hn₁ hε hc hBabs hR₁ hatt₁ (hOT₁ ω hω₁) (hτ₁ ω hωT₁)
    have hF := certificate_independent K n₀ n₁ (x₀ ω) (x₁ ω) c ε (rOT₀ ω + ε * τ₀ ω) (rOT₁ ω + ε * τ₁ ω)
      lam₀ lam₁ h 𝒩₀ 𝒩₁ hn₀ hn₁ hε hl₀ hl₁ hc hc0 ⟨B, hB⟩ hh hhB hR₀ hR₁
    refine le_trans ?_ hF
    unfold Findep
    exact le_iSup_of_le P₀ (le_iSup_of_le P₁ (le_iSup_of_le ⟨hb₀, hb₁⟩ le_rfl))

end StatFormal.Wave18b
