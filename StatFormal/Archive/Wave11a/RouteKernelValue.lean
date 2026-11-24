import StatFormal.Archive.Wave11a.RouteKernel
import TauCeti.InformationTheory.KullbackLeibler.ChainRule

/-!
# Wave 11a route: robust equality JASA `lem:kernel`, the coupling ↔ kernel step

Untrusted proof file. For labels `μ = n⁻¹ Σ δ_i`, every coupling `γ` with first marginal `μ` is `μ ⊗ₘ Γ` for
the kernel `Γ_i = n · γ({i} × ·)`; for `γ = μ ⊗ₘ Γ` the cost is `n⁻¹ Σ_i E_{Γ_i} c_i` and, by the conditional
chain rule (Tau Ceti `klDiv_compProd_right`), `KL(γ‖μ ⊗ ν) = n⁻¹ Σ_i KL(Γ_i‖ν)`. The infimum is attained by
the frozen strong duality (an optimal coupling for `OT_ε`) and `lem:tax` (`klRef_chain`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Real ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatFormal.Wave11a

open StatFormal.RobustEquality StatFormal.RobustEquality.Tax StatFormal.RobustEquality.SemidualStrong
  StatFormal.RobustEquality.Semidual StatFormal.RobustEquality.Certificate StatFormal.RobustEquality.Strong

variable {K : Type} [MeasurableSpace K] {n : ℕ}

/-- The uniform label weights. -/
abbrev unifW (n : ℕ) : Fin n → ℝ := fun _ => (1 : ℝ) / n

lemma ofReal_unifW (hn : 0 < n) (i : Fin n) : ENNReal.ofReal (unifW n i) = (n : ℝ≥0∞)⁻¹ := by
  simp only [unifW, one_div]
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast]

lemma unifW_pos (hn : 0 < n) (i : Fin n) : 0 < unifW n i := by
  simp only [unifW]; have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

lemma unifW_sum (hn : 0 < n) : ∑ i, unifW n i = 1 := by
  simp only [unifW, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- The kernel of a family of laws on the labels. -/
def kerOf (Γ : Fin n → Measure K) : Kernel (Fin n) K := Kernel.ofFunOfCountable Γ

lemma kerOf_apply (Γ : Fin n → Measure K) (i : Fin n) : kerOf Γ i = Γ i := rfl

lemma kerOf_markov (Γ : Fin n → Measure K) (hΓ : ∀ i, IsProbabilityMeasure (Γ i)) :
    IsMarkovKernel (kerOf Γ) := ⟨fun i => hΓ i⟩

section Forward

variable (hn : 0 < n) (Γ : Fin n → Measure K) (hΓ : ∀ i, IsProbabilityMeasure (Γ i))
include hn hΓ

lemma fwd_prob : IsProbabilityMeasure (muDisc (unifW n) ⊗ₘ kerOf Γ) := by
  haveI := StatFormal.Foundations.SemiDiscrete.isProb_muDisc (unifW_pos hn) (unifW_sum hn)
  haveI := kerOf_markov Γ hΓ
  infer_instance

lemma fwd_fst : (muDisc (unifW n) ⊗ₘ kerOf Γ).map Prod.fst = muDisc (unifW n) := by
  haveI := kerOf_markov Γ hΓ
  exact Measure.fst_compProd _ _

lemma fwd_snd : (muDisc (unifW n) ⊗ₘ kerOf Γ).map Prod.snd = (n : ℝ≥0∞)⁻¹ • ∑ i, Γ i := by
  haveI := kerOf_markov Γ hΓ
  ext s hs
  rw [Measure.map_apply measurable_snd hs, Measure.compProd_apply (measurable_snd hs),
    StatFormal.Foundations.SemiDiscrete.lintegral_muDisc, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofReal_unifW hn, kerOf_apply]
  rfl

lemma fwd_cost (c : Fin n → K → ℝ) (hcm : ∀ i, Measurable (c i)) {B : ℝ} (hB : ∀ i y, |c i y| ≤ B) :
    ∫ z, c z.1 z.2 ∂(muDisc (unifW n) ⊗ₘ kerOf Γ) = (n : ℝ)⁻¹ * ∑ i, ∫ y, c i y ∂(Γ i) := by
  haveI := kerOf_markov Γ hΓ
  have := fwd_prob hn Γ hΓ
  have hm : Measurable fun z : Fin n × K => c z.1 z.2 := measurable_from_prod_countable_right hcm
  have hint : Integrable (fun z : Fin n × K => c z.1 z.2) (muDisc (unifW n) ⊗ₘ kerOf Γ) :=
    Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact hB _ _)
  rw [Measure.integral_compProd hint, StatFormal.Foundations.SemiDiscrete.integral_muDisc' (unifW_pos hn),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kerOf_apply]
  simp [unifW]

lemma fwd_klDiv (ν : Measure K) [IsFiniteMeasure ν] :
    klDiv (muDisc (unifW n) ⊗ₘ kerOf Γ) ((muDisc (unifW n)).prod ν) =
      ∑ i, (n : ℝ≥0∞)⁻¹ * klDiv (Γ i) ν := by
  haveI := kerOf_markov Γ hΓ
  haveI := StatFormal.Foundations.SemiDiscrete.isProb_muDisc (unifW_pos hn) (unifW_sum hn)
  rw [← Measure.compProd_const, TauCeti.klDiv_compProd_right,
    StatFormal.Foundations.SemiDiscrete.lintegral_muDisc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofReal_unifW hn, kerOf_apply, Kernel.const_apply]

/-- The coupling objective of `μ ⊗ₘ Γ` is the kernel budget. -/
lemma fwd_value (x : Fin n → K) (c : K → K → ℝ) {ε : ℝ} (hε : 0 < ε) (hcm : ∀ y, Measurable (c y))
    {B : ℝ} (hB : ∀ a b, |c a b| ≤ B) (ν : Measure K) [IsFiniteMeasure ν] :
    ((∫ z, (fun i => c (x i)) z.1 z.2 ∂(muDisc (unifW n) ⊗ₘ kerOf Γ) : ℝ) : EReal) +
        (ε : EReal) * klRef (muDisc (unifW n) ⊗ₘ kerOf Γ) ((muDisc (unifW n)).prod ν) =
      budget x c ε ν Γ := by
  have := fwd_prob hn Γ hΓ
  haveI := StatFormal.Foundations.SemiDiscrete.isProb_muDisc (unifW_pos hn) (unifW_sum hn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [fwd_cost hn Γ hΓ (fun i => c (x i)) (fun i => hcm _) (fun i y => hB _ _)]
  have hkl := fwd_klDiv hn Γ hΓ ν
  rw [StatFormal.Foundations.Tax.klRef_eq_klDiv, hkl]
  have hTbot : ∀ i, (((∫ z, c (x i) z ∂(Γ i) : ℝ) : EReal) + (ε : EReal) * klRef (Γ i) ν) ≠ ⊥ :=
    fun i => anchor_term_ne_bot hε _ _ _
  have hninv : (0 : EReal) < ((n : ℝ) : EReal)⁻¹ := by
    rw [← EReal.coe_inv]; exact EReal.coe_pos.2 (inv_pos.2 hnR)
  have hinvne : (n : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n)
  by_cases htop : ∃ j, klDiv (Γ j) ν = ⊤
  · obtain ⟨j, hj⟩ := htop
    have hsum : ∑ i, (n : ℝ≥0∞)⁻¹ * klDiv (Γ i) ν = ⊤ := by
      rw [ENNReal.sum_eq_top]
      exact ⟨j, Finset.mem_univ _, by rw [hj, ENNReal.mul_top hinvne]⟩
    have hTj : ((∫ z, c (x j) z ∂(Γ j) : ℝ) : EReal) + (ε : EReal) * klRef (Γ j) ν = ⊤ := by
      haveI := hΓ j
      rw [(StatFormal.Foundations.Tax.klRef_eq_top_iff (Γ j) ν).2 hj, EReal.coe_mul_top_of_pos hε,
        EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    rw [if_pos hsum, EReal.coe_mul_top_of_pos hε, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    change ⊤ = ((n : ℝ) : EReal)⁻¹ * ∑ i, _
    rw [ereal_sum_eq_top _ hTbot j hTj, EReal.mul_top_of_pos hninv]
  push Not at htop
  have hsum : ∑ i, (n : ℝ≥0∞)⁻¹ * klDiv (Γ i) ν ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun i _ => ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (by exact_mod_cast hn.ne')) (htop i)
  rw [if_neg hsum]
  have hki : ∀ i, klRef (Γ i) ν = (((klDiv (Γ i) ν).toReal - ν.real univ + 1 : ℝ) : EReal) := fun i => by
    haveI := hΓ i
    rw [StatFormal.Foundations.Tax.klRef_eq_klDiv, if_neg (htop i)]
  change _ = ((n : ℝ) : EReal)⁻¹ * ∑ i, _
  simp only [hki]
  have hprod : ((muDisc (unifW n)).prod ν).real univ = ν.real univ := by
    rw [measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod, measure_univ, one_mul, measureReal_def]
  rw [hprod, ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (by exact_mod_cast hn.ne')) (htop i))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← EReal.coe_inv]
  norm_cast
  rw [← StatFormal.Foundations.SemiDiscrete.EReal.coe_finsetSum, ← EReal.coe_mul, EReal.coe_eq_coe_iff,
    ← Finset.mul_sum]
  simp only [mul_add, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  field_simp

end Forward

section Converse

variable (γ : Measure (Fin n × K))

/-- The kernel of a coupling with first marginal `n⁻¹ Σ δ_i`: `Γ_i = n · γ({i} × ·)`. -/
def kerFromCoupling (i : Fin n) : Measure K := (n : ℝ≥0∞) • (γ.restrict ({i} ×ˢ univ)).map Prod.snd

lemma kerFromCoupling_apply (i : Fin n) {S : Set K} (hS : MeasurableSet S) :
    kerFromCoupling γ i S = (n : ℝ≥0∞) * γ ({i} ×ˢ S) := by
  rw [kerFromCoupling, Measure.smul_apply, Measure.map_apply measurable_snd hS,
    Measure.restrict_apply (measurable_snd hS), smul_eq_mul]
  congr 2
  ext ⟨j, y⟩
  simp [and_comm]

variable (hn : 0 < n) (hfst : γ.map Prod.fst = muDisc (unifW n))
include hn hfst

lemma coupling_singleton (i : Fin n) : γ ({i} ×ˢ univ) = (n : ℝ≥0∞)⁻¹ := by
  have h : (γ.map Prod.fst) {i} = (muDisc (unifW n)) {i} := by rw [hfst]
  rw [Measure.map_apply measurable_fst (measurableSet_singleton i),
    StatFormal.Foundations.SemiDiscrete.muDisc_singleton, ofReal_unifW hn] at h
  rw [← h]
  congr 1
  ext ⟨j, y⟩
  simp

lemma kerFromCoupling_prob (i : Fin n) : IsProbabilityMeasure (kerFromCoupling γ i) := by
  refine ⟨?_⟩
  rw [kerFromCoupling_apply γ i MeasurableSet.univ, coupling_singleton γ hn hfst i]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

lemma coupling_eq_compProd : γ = muDisc (unifW n) ⊗ₘ kerOf (kerFromCoupling γ) := by
  haveI := kerOf_markov _ (kerFromCoupling_prob γ hn hfst)
  ext T hT
  rw [Measure.compProd_apply hT, StatFormal.Foundations.SemiDiscrete.lintegral_muDisc]
  have hslice : ∀ i : Fin n, MeasurableSet (Prod.mk i ⁻¹' T) := fun i => measurable_prodMk_left hT
  have hT' : T = ⋃ i : Fin n, ({i} ×ˢ (Prod.mk i ⁻¹' T)) := by
    ext ⟨j, y⟩
    simp
  have hdisj : Pairwise (Function.onFun Disjoint fun i : Fin n => ({i} ×ˢ (Prod.mk i ⁻¹' T))) := by
    intro i j hij
    refine Set.disjoint_left.2 fun p hp hq => hij ?_
    simp only [Set.mem_prod, Set.mem_singleton_iff] at hp hq
    rw [← hp.1, hq.1]
  conv_lhs => rw [hT']
  rw [measure_iUnion hdisj (fun i => (measurableSet_singleton i).prod (hslice i)), tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kerOf_apply, kerFromCoupling_apply γ i (hslice i), ofReal_unifW hn, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n), one_mul]

end Converse

theorem kernel_value : Claims.kernel_value := by
  intro K _ n x c ε ν Q _ _ hn hε hcm ⟨B, hB⟩
  have hs : Setting ε (fun _ : Fin n => (1 : ℝ) / n) (fun i => c (x i)) :=
    StatFormal.Foundations.Tax.setting_centre (cost := c) hn hε hcm hB x
  refine ⟨?_, ?_⟩
  · -- attainment: an optimal coupling for `OT_ε`, disintegrated
    obtain ⟨-, -, -, γ, hγ, hfst, hsnd, hval⟩ :=
      StatFormal.RobustEquality.SemidualStrong.strong_duality K n ε _ _ Q hs
    have := hγ
    set Γ := kerFromCoupling γ
    have hΓ := kerFromCoupling_prob γ hn hfst
    have heq := coupling_eq_compProd γ hn hfst
    refine ⟨Γ, hΓ, ?_, ?_⟩
    · rw [← hsnd, heq]; exact fwd_snd hn Γ hΓ
    · rw [StatFormal.RobustEquality.Tax.tax_identity K n ε _ _ ν Q hs, ← hval,
        ← fwd_value hn Γ hΓ x c hε hcm hB ν, ← heq,
        StatFormal.Foundations.Tax.klRef_chain (unifW_pos hn) (unifW_sum hn) ν Q γ hsnd,
        EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 hε.le) (EReal.coe_ne_top ε), add_assoc]
  · rintro v ⟨Γ, hΓ, hQ, rfl⟩
    have := fwd_prob hn Γ hΓ
    refine csInf_le (OrderBot.bddBelow _) ⟨_, inferInstance, fwd_fst hn Γ hΓ, ?_, (fwd_value hn Γ hΓ x c hε hcm hB ν).symm⟩
    rw [fwd_snd hn Γ hΓ, hQ]

theorem kernel_iff : Claims.kernel_iff := by
  intro K _ n x c ε r 𝒩 Q _ hn hε hcm hB h𝒩
  constructor
  · rintro ⟨-, ν, hν, hW⟩
    have := h𝒩 ν hν
    obtain ⟨⟨Γ, hΓ, hQ, hv⟩, -⟩ := kernel_value K n x c ε ν Q hn hε hcm hB
    exact ⟨ν, hν, Γ, hΓ, hQ, hv.symm.trans_le hW⟩
  · rintro ⟨ν, hν, Γ, hΓ, hQ, hle⟩
    have := h𝒩 ν hν
    obtain ⟨-, hlow⟩ := kernel_value K n x c ε ν Q hn hε hcm hB
    exact ⟨inferInstance, ν, hν, (hlow ⟨Γ, hΓ, hQ, rfl⟩).trans hle⟩

example : Claims.kernel_value := kernel_value
example : Claims.kernel_iff := kernel_iff
example : Claims.kernel_floor_min := kernel_floor_min
example : Claims.kernel_floor_ref := kernel_floor_ref
example : Claims.kernel_floor := kernel_floor
example : Claims.kernel_floor_compact := kernel_floor_compact

end StatFormal.Wave11a
