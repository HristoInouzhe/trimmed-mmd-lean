import StatFormal.Archive.RobustEquality.SemidualStrong.Statements
import StatFormal.Lib.SemiDiscrete.Convex
import TauCeti.InformationTheory.KullbackLeibler.ChangeOfReference
import TauCeti.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# The misspecification tax (`lem:tax`) for a discrete first marginal

Library component (robust equality, JASA). Untrusted library code; it imports the frozen
`SemidualStrong/Statements.lean` only for `OTdisc`, `muDisc`, `Setting` and the paper's KL
`klRef`, and does not modify them.

## Definitions

* `Wdisc ε a c ν Q`: the Sinkhorn discrepancy `W^ν_ε(μ, Q) = inf_{γ ∈ Π(μ,Q)} E_γ c + ε KL(γ‖μ⊗ν)`
  for `μ = Σ_i a_i δ_i` (labelled atoms), in the encoding of `OTdisc` (reference `ν` any finite
  measure; `KL` = `klRef`);
* `tax 𝒩 Q = inf_{ν ∈ 𝒩} KL(Q‖ν)` and `ballN 𝒩 ε a c r = ⋃_{ν ∈ 𝒩} {Q ∈ 𝒫(K) : W^ν_ε(μ,Q) ≤ r}`.

## Main results

* `klRef_eq_klDiv`: `klRef` in terms of Mathlib's `klDiv` (mass correction `1 − ν(K)`);
* `ac_prod_of_coupling`: a coupling of `μ = Σ a_i δ_i` (`a_i > 0`) and `Q` is `≪ μ ⊗ Q`;
* `klRef_chain`: **chain rule** `KL(γ‖μ⊗ν) = KL(γ‖μ⊗Q) + KL(Q‖ν)` for couplings `γ ∈ Π(μ, Q)`
  (both sides `⊤` when `Q` is not `≪ ν`);
* `Wdisc_eq` (**`lem:tax`**): `W^ν_ε(μ, Q) = OT_ε(μ, Q) + ε KL(Q‖ν)`, and
  `Wdisc_eq_top_of_not_ac`: both sides are `⊤` when `Q` is not `≪ ν`;
* `ballN_subset`, `mem_ballN_iff_of_attained`: the ball is
  `{Q : OT_ε(μ,Q) + ε τ_𝒩(Q) ≤ r}` when the infimum defining the tax is attained, and always
  contained in it.
-/

noncomputable section
open MeasureTheory InformationTheory Set
open scoped ENNReal

namespace StatFormal.Foundations.Tax

open StatFormal.RobustEquality StatFormal.RobustEquality.Semidual
  StatFormal.RobustEquality.SemidualStrong

variable {K : Type} [MeasurableSpace K] {k : ℕ}

/-- The Sinkhorn discrepancy `W^ν_ε(μ, Q)` with reference `ν`, for `μ = Σ_i a_i δ_i`. -/
def Wdisc (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (ν Q : Measure K) : EReal :=
  sInf {v | ∃ γ : Measure (Fin k × K), IsProbabilityMeasure γ ∧ γ.map Prod.fst = muDisc a ∧
    γ.map Prod.snd = Q ∧
    v = ((∫ z, c z.1 z.2 ∂γ : ℝ) : EReal) + (ε : EReal) * klRef γ ((muDisc a).prod ν)}

/-- The tax `τ_𝒩(Q) = inf_{ν ∈ 𝒩} KL(Q‖ν)`. -/
def tax (𝒩 : Set (Measure K)) (Q : Measure K) : EReal := ⨅ ν ∈ 𝒩, klRef Q ν

/-- The ball `𝓑^𝒩(r) = ⋃_{ν ∈ 𝒩} {Q ∈ 𝒫(K) : W^ν_ε(μ, Q) ≤ r}`. -/
def ballN (𝒩 : Set (Measure K)) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (r : EReal) :
    Set (Measure K) :=
  {Q | IsProbabilityMeasure Q ∧ ∃ ν ∈ 𝒩, Wdisc ε a c ν Q ≤ r}

theorem klRef_ne_bot (Γ ν : Measure K) : klRef Γ ν ≠ ⊥ := by
  unfold klRef
  split_ifs
  · exact EReal.coe_ne_bot _
  · exact top_ne_bot

/-- `klRef` through Mathlib's `klDiv`: `klRef Γ ν = klDiv Γ ν − ν(K) + 1` when finite. -/
theorem klRef_eq_klDiv (Γ ν : Measure K) [IsProbabilityMeasure Γ] [IsFiniteMeasure ν] :
    klRef Γ ν = if klDiv Γ ν = ⊤ then ⊤
      else (((klDiv Γ ν).toReal - ν.real univ + 1 : ℝ) : EReal) := by
  unfold klRef
  by_cases h : Γ ≪ ν ∧ Integrable (llr Γ ν) Γ
  · have hΓ : Γ.real univ = 1 := probReal_univ
    rw [ite_eq_left h, ite_eq_right (klDiv_ne_top_iff.2 h), klDiv_of_ac_of_integrable h.1 h.2,
      ENNReal.toReal_ofReal (integral_llr_add_sub_measure_univ_nonneg h.1 h.2), hΓ]
    congr 1
    ring
  · rw [ite_eq_right h, ite_eq_left]
    by_contra h'
    exact h (klDiv_ne_top_iff.1 h')

theorem klRef_eq_top_iff (Γ ν : Measure K) [IsProbabilityMeasure Γ] [IsFiniteMeasure ν] :
    klRef Γ ν = ⊤ ↔ klDiv Γ ν = ⊤ := by
  rw [klRef_eq_klDiv]
  by_cases h : klDiv Γ ν = ⊤
  · simp [h]
  · rw [ite_eq_right h]
    exact ⟨fun h' => absurd h' (EReal.coe_ne_top _), fun h' => absurd h' h⟩

theorem klRef_nonneg_of_prob (Γ ν : Measure K) [IsProbabilityMeasure Γ]
    [IsProbabilityMeasure ν] : 0 ≤ klRef Γ ν := by
  rw [klRef_eq_klDiv]
  split_ifs
  · exact le_top
  · have hν : ν.real univ = 1 := probReal_univ
    rw [hν, sub_add_cancel]
    exact EReal.coe_nonneg.2 ENNReal.toReal_nonneg

/-- A finitely supported law charging a point that `ν` does not has infinite `KL`. -/
theorem klRef_eq_top_of_atom {Q ν : Measure K} {x : K} (hQ : Q {x} ≠ 0) (hν : ν {x} = 0) :
    klRef Q ν = ⊤ := by
  unfold klRef
  rw [ite_eq_right]
  rintro ⟨hac, -⟩
  exact hQ (hac hν)

/-- A coupling of `Σ_i a_i δ_i` (`a_i > 0`) and `Q` is absolutely continuous w.r.t. the
product `μ ⊗ Q`. -/
theorem ac_prod_of_coupling {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) {Q : Measure K}
    [IsFiniteMeasure Q]
    {γ : Measure (Fin k × K)} (hsnd : γ.map Prod.snd = Q) : γ ≪ (muDisc a).prod Q := by
  intro s hs0
  have hs := measurableSet_toMeasurable ((muDisc a).prod Q) s
  have hs0' : (muDisc a).prod Q (toMeasurable ((muDisc a).prod Q) s) = 0 := by
    rw [measure_toMeasurable]; exact hs0
  set t := toMeasurable ((muDisc a).prod Q) s
  rw [Measure.prod_apply hs, StatFormal.Foundations.SemiDiscrete.lintegral_muDisc] at hs0'
  have hQi : ∀ i, Q (Prod.mk i ⁻¹' t) = 0 := fun i => by
    have := (Finset.sum_eq_zero_iff.1 hs0') i (Finset.mem_univ i)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by simpa using ha i)
    · exact h
  have hsub : s ⊆ ⋃ i, Prod.snd ⁻¹' (Prod.mk i ⁻¹' t) := by
    intro z hz
    refine mem_iUnion.2 ⟨z.1, ?_⟩
    simp only [mem_preimage]
    exact subset_toMeasurable _ _ hz
  refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
  rw [← Measure.map_apply measurable_snd (measurable_prodMk_left hs), hsnd]
  exact hQi i

/-- The log-likelihood ratio of `μ ⊗ Q` against `μ ⊗ ν` is `llr Q ν ∘ snd`. -/
theorem prod_ac_and_llr_eq {μ : Measure (Fin k)} [IsFiniteMeasure μ] {Q ν : Measure K}
    [IsFiniteMeasure Q] [IsFiniteMeasure ν] (hQν : Q ≪ ν) :
    μ.prod Q ≪ μ.prod ν ∧
      llr (μ.prod Q) (μ.prod ν) =ᵐ[μ.prod Q] fun z => llr Q ν z.2 := by
  have hQ : ν.withDensity (Q.rnDeriv ν) = Q := Measure.withDensity_rnDeriv_eq Q ν hQν
  have hP : μ.prod Q = (μ.prod ν).withDensity (fun z => Q.rnDeriv ν z.2) := by
    calc μ.prod Q = μ.prod (ν.withDensity (Q.rnDeriv ν)) := by rw [hQ]
      _ = _ := prod_withDensity_right (Measure.measurable_rnDeriv _ _)
  have hac : μ.prod Q ≪ μ.prod ν := by
    rw [hP]; exact withDensity_absolutelyContinuous _ _
  have hrn : (μ.prod Q).rnDeriv (μ.prod ν) =ᵐ[μ.prod ν] fun z => Q.rnDeriv ν z.2 := by
    rw [hP]
    exact Measure.rnDeriv_withDensity _ ((Measure.measurable_rnDeriv _ _).comp measurable_snd)
  refine ⟨hac, ?_⟩
  filter_upwards [hac.ae_le hrn] with z hz
  simp only [llr_def, hz]

/-- **Chain rule of relative entropy** for a coupling `γ` of `μ = Σ_i a_i δ_i` and `Q`:
`KL(γ‖μ⊗ν) = KL(γ‖μ⊗Q) + KL(Q‖ν)` (paper's `klRef`, reference `ν` any finite measure). -/
theorem klRef_chain {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1)
    (ν Q : Measure K) [IsFiniteMeasure ν] [IsProbabilityMeasure Q]
    (γ : Measure (Fin k × K)) [IsProbabilityMeasure γ] (hsnd : γ.map Prod.snd = Q) :
    klRef γ ((muDisc a).prod ν) = klRef γ ((muDisc a).prod Q) + klRef Q ν := by
  have hμ : IsProbabilityMeasure (muDisc a) :=
    StatFormal.Foundations.SemiDiscrete.isProb_muDisc ha hsum
  set μ := muDisc a with hμdef
  have hγπ : γ ≪ μ.prod Q := ac_prod_of_coupling ha hsnd
  -- data processing along `snd`
  have hDP : klDiv Q ν ≤ klDiv γ (μ.prod ν) := by
    have h := klDiv_map_le (μ := γ) (ν := μ.prod ν) measurable_snd
    rwa [hsnd, Measure.map_snd_prod, measure_univ, one_smul] at h
  have hπR : klDiv (μ.prod Q) (μ.prod ν) = klDiv Q ν := by
    rw [TauCeti.klDiv_prod_right, measure_univ, one_mul]
  have hRuniv : (μ.prod ν).real univ = ν.real univ := by
    rw [measureReal_def, ← univ_prod_univ, Measure.prod_prod, measure_univ, one_mul]
    rfl
  by_cases hQ : klDiv Q ν = ⊤
  · have hR : klDiv γ (μ.prod ν) = ⊤ := top_le_iff.1 (hQ ▸ hDP)
    rw [(klRef_eq_top_iff _ _).2 hR, (klRef_eq_top_iff _ _).2 hQ,
      EReal.add_top_of_ne_bot (klRef_ne_bot _ _)]
  obtain ⟨hQν, hint⟩ := klDiv_ne_top_iff.1 hQ
  obtain ⟨hπac, hllr⟩ := prod_ac_and_llr_eq (μ := μ) hQν
  have hllrγ : llr (μ.prod Q) (μ.prod ν) =ᵐ[γ] fun z => llr Q ν z.2 := hγπ.ae_le hllr
  have hm := measurable_llr Q ν
  have hπsnd : (μ.prod Q).map Prod.snd = Q := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hintγ' : Integrable (fun z : Fin k × K => llr Q ν z.2) γ :=
    (integrable_map_measure hm.aestronglyMeasurable measurable_snd.aemeasurable).1
      (by rw [hsnd]; exact hint)
  have hintπ' : Integrable (fun z : Fin k × K => llr Q ν z.2) (μ.prod Q) :=
    (integrable_map_measure hm.aestronglyMeasurable measurable_snd.aemeasurable).1
      (by rw [hπsnd]; exact hint)
  have hγ : Integrable (llr (μ.prod Q) (μ.prod ν)) γ := (integrable_congr hllrγ).2 hintγ'
  have hπ : Integrable (llr (μ.prod Q) (μ.prod ν)) (μ.prod Q) := (integrable_congr hllr).2 hintπ'
  have hI : ∫ z, llr (μ.prod Q) (μ.prod ν) z ∂γ =
      ∫ z, llr (μ.prod Q) (μ.prod ν) z ∂(μ.prod Q) := by
    rw [integral_congr_ae hllrγ, integral_congr_ae hllr]
    have e1 := integral_map (μ := γ) measurable_snd.aemeasurable hm.aestronglyMeasurable
    have e2 := integral_map (μ := μ.prod Q) measurable_snd.aemeasurable hm.aestronglyMeasurable
    rw [hsnd] at e1
    rw [hπsnd] at e2
    rw [← e1, ← e2]
  have hPy := TauCeti.klDiv_eq_klDiv_add_klDiv hγπ hπac hγ hπ hI
  rw [hπR] at hPy
  by_cases hγπ' : klDiv γ (μ.prod Q) = ⊤
  · have hR : klDiv γ (μ.prod ν) = ⊤ := by rw [hPy, hγπ', top_add]
    rw [(klRef_eq_top_iff _ _).2 hR, (klRef_eq_top_iff _ _).2 hγπ',
      EReal.top_add_of_ne_bot (klRef_ne_bot _ _)]
  have hR : klDiv γ (μ.prod ν) ≠ ⊤ := by rw [hPy]; exact ENNReal.add_ne_top.2 ⟨hγπ', hQ⟩
  rw [klRef_eq_klDiv γ (μ.prod ν), klRef_eq_klDiv γ (μ.prod Q), klRef_eq_klDiv Q ν, ite_eq_right hR,
    ite_eq_right hγπ', ite_eq_right hQ, hPy, ENNReal.toReal_add hγπ' hQ, hRuniv,
    probReal_univ (μ := μ.prod Q), ← EReal.coe_add]
  congr 1
  ring

/-- Adding a constant `C ≠ ⊥` commutes with `sInf` when the infimum is not `⊥`. -/
theorem sInf_add_const (S : Set EReal) {C : EReal} (hC : C ≠ ⊥) (hS : sInf S ≠ ⊥) :
    sInf {v | ∃ w ∈ S, v = w + C} = sInf S + C := by
  apply le_antisymm
  · rcases eq_or_ne C ⊤ with hCt | hCt
    · rw [hCt, EReal.add_top_of_ne_bot hS]; exact le_top
    · lift C to ℝ using ⟨hCt, hC⟩
      rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot C)) (Or.inl (EReal.coe_ne_top C))]
      refine le_sInf fun w hw => ?_
      rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot C)) (Or.inl (EReal.coe_ne_top C))]
      exact sInf_le ⟨w, hw, rfl⟩
  · refine le_sInf ?_
    rintro v ⟨w, hw, rfl⟩
    exact add_le_add (sInf_le hw) le_rfl

theorem OTdisc_ne_bot {ε : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ} (hs : Setting ε a c)
    (Q : Measure K) [IsProbabilityMeasure Q] : OTdisc ε a c Q ≠ ⊥ := by
  obtain ⟨hε, ha, hsum, hc, B, hB⟩ := hs
  have h : StatFormal.Foundations.SemiDiscrete.SDHyp ε a c B := ⟨hε, ha, hsum, hc, hB⟩
  have := StatFormal.Foundations.SemiDiscrete.Jdual_le_Theta' h Q 0
  intro hbot
  change StatFormal.Foundations.SemiDiscrete.Theta ε a c Q = ⊥ at hbot
  rw [hbot] at this
  exact EReal.coe_ne_bot _ (le_bot_iff.1 this)

theorem coe_mul_klRef_ne_bot {ε : ℝ} (hε : 0 < ε) (Γ ν : Measure K) :
    (ε : EReal) * klRef Γ ν ≠ ⊥ := by
  unfold klRef
  split_ifs
  · rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
  · rw [EReal.coe_mul_top_of_pos hε]; exact top_ne_bot

/-- **`lem:tax`** (discrete first marginal): `W^ν_ε(μ, Q) = OT_ε(μ, Q) + ε KL(Q‖ν)` for every
finite reference `ν` and probability `Q`; both sides are `⊤` when `Q` is not `≪ ν`. -/
theorem Wdisc_eq {ε : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ} (hs : Setting ε a c)
    (ν : Measure K) [IsFiniteMeasure ν] (Q : Measure K) [IsProbabilityMeasure Q] :
    Wdisc ε a c ν Q = OTdisc ε a c Q + (ε : EReal) * klRef Q ν := by
  have hε := hs.1
  have ha := hs.2.1
  have hsum := hs.2.2.1
  have hdist : ∀ x y : EReal, (ε : EReal) * (x + y) = ε * x + ε * y :=
    EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 hε.le) (EReal.coe_ne_top ε)
  have hset : {v | ∃ γ : Measure (Fin k × K), IsProbabilityMeasure γ ∧ γ.map Prod.fst = muDisc a ∧
      γ.map Prod.snd = Q ∧
      v = ((∫ z, c z.1 z.2 ∂γ : ℝ) : EReal) + (ε : EReal) * klRef γ ((muDisc a).prod ν)} =
      {v | ∃ w ∈ {v | ∃ γ : Measure (Fin k × K), IsProbabilityMeasure γ ∧
        γ.map Prod.fst = muDisc a ∧ γ.map Prod.snd = Q ∧
        v = ((∫ z, c z.1 z.2 ∂γ : ℝ) : EReal) + (ε : EReal) * klRef γ ((muDisc a).prod Q)},
        v = w + (ε : EReal) * klRef Q ν} := by
    ext v
    constructor
    · rintro ⟨γ, hγ, hfst, hsnd, rfl⟩
      refine ⟨_, ⟨γ, hγ, hfst, hsnd, rfl⟩, ?_⟩
      rw [klRef_chain ha hsum ν Q γ hsnd, hdist, add_assoc]
    · rintro ⟨w, ⟨γ, hγ, hfst, hsnd, rfl⟩, rfl⟩
      refine ⟨γ, hγ, hfst, hsnd, ?_⟩
      rw [klRef_chain ha hsum ν Q γ hsnd, hdist, add_assoc]
  unfold Wdisc
  rw [hset, sInf_add_const _ (coe_mul_klRef_ne_bot hε Q ν) (OTdisc_ne_bot hs Q)]
  rfl

/-- Both sides of `lem:tax` are `⊤` when `Q` is not absolutely continuous w.r.t. `ν`. -/
theorem Wdisc_eq_top_of_not_ac {ε : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ}
    (hs : Setting ε a c) (ν : Measure K) [IsFiniteMeasure ν] (Q : Measure K)
    [IsProbabilityMeasure Q] (h : ¬ Q ≪ ν) : Wdisc ε a c ν Q = ⊤ := by
  have hkl : klRef Q ν = ⊤ := by
    unfold klRef
    rw [ite_eq_right]
    exact fun h' => h h'.1
  rw [Wdisc_eq hs, hkl, EReal.coe_mul_top_of_pos hs.1,
    EReal.add_top_of_ne_bot (OTdisc_ne_bot hs Q)]

theorem coe_mul_le_coe_mul {ε : ℝ} (hε : 0 ≤ ε) {x y : EReal} (h : x ≤ y) :
    (ε : EReal) * x ≤ ε * y :=
  mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.2 hε)

/-- The ball is always contained in `{Q : OT_ε(μ, Q) + ε τ_𝒩(Q) ≤ r}`. -/
theorem ballN_subset {ε : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ} (hs : Setting ε a c)
    {𝒩 : Set (Measure K)} (hN : ∀ ν ∈ 𝒩, IsFiniteMeasure ν) {r : EReal} {Q : Measure K}
    (hQ : Q ∈ ballN 𝒩 ε a c r) : OTdisc ε a c Q + (ε : EReal) * tax 𝒩 Q ≤ r := by
  obtain ⟨hQp, ν, hν, hW⟩ := hQ
  have := hN ν hν
  rw [Wdisc_eq hs] at hW
  refine le_trans (add_le_add le_rfl (coe_mul_le_coe_mul hs.1.le ?_)) hW
  exact iInf₂_le ν hν

/-- When the infimum defining the tax is attained, the ball is exactly
`{Q ∈ 𝒫(K) : OT_ε(μ, Q) + ε τ_𝒩(Q) ≤ r}`. -/
theorem mem_ballN_iff_of_attained {ε : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ}
    (hs : Setting ε a c) {𝒩 : Set (Measure K)} (hN : ∀ ν ∈ 𝒩, IsFiniteMeasure ν) (r : EReal)
    (Q : Measure K) [IsProbabilityMeasure Q] (hatt : ∃ ν ∈ 𝒩, klRef Q ν = tax 𝒩 Q) :
    Q ∈ ballN 𝒩 ε a c r ↔ OTdisc ε a c Q + (ε : EReal) * tax 𝒩 Q ≤ r := by
  refine ⟨ballN_subset hs hN, fun h => ?_⟩
  obtain ⟨ν, hν, heq⟩ := hatt
  have := hN ν hν
  refine ⟨inferInstance, ν, hν, ?_⟩
  rw [Wdisc_eq hs, heq]
  exact h

/-- `KL(Q‖Q) = 0`: the free class `𝒩 = 𝒫(K)` has no tax (attained at `ν = Q`). -/
theorem klRef_self (Q : Measure K) [IsProbabilityMeasure Q] : klRef Q Q = 0 := by
  have hQ1 : Q.real univ = 1 := probReal_univ
  rw [klRef_eq_klDiv, klDiv_self, hQ1]
  simp

theorem tax_eq_zero_of_mem {𝒩 : Set (Measure K)} (h𝒩 : ∀ ν ∈ 𝒩, IsProbabilityMeasure ν)
    (Q : Measure K) [IsProbabilityMeasure Q] (hQ : Q ∈ 𝒩) : tax 𝒩 Q = 0 := by
  refine le_antisymm ((iInf₂_le Q hQ).trans_eq (klRef_self Q)) (le_iInf₂ fun ν hν => ?_)
  have := h𝒩 ν hν
  exact klRef_nonneg_of_prob Q ν

end StatFormal.Foundations.Tax
