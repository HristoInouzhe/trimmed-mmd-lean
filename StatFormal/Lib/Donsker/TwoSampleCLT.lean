import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Donsker library — the two-sample one-dimensional CLT (untrusted library code)

Route.
* One sample (`tendstoInDistribution_oneSample`): `X_i = F ∘ ξ_i` is i.i.d. (`iIndepFun.comp`, the laws
  are `P.map F`), bounded hence in `L²`, with `μ[X_0] = ∫ F dP` and `Var[X_0] = Var_P F`
  (`integral_map`, `variance_map`). Mathlib's CLT `tendstoInDistribution_inv_sqrt_mul_sum_sub`,
  composed along `n_k → ∞`, gives `S_k = (√n_k)⁻¹ (Σ_{i<n_k} X_i − n_k PF) ⇒ N(0, Var_P F)`.
  Slutsky with the deterministic factor `r_k/√n_k → c_P`
  (`TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`) gives
  `(r_k/√n_k) S_k ⇒ c_P · N(0, Var_P F) = N(0, c_P² Var_P F)` (`gaussianReal_map_const_mul`), and for
  `n_k ≥ 1` (eventually) `(r_k/√n_k) S_k = r_k (n_k⁻¹ Σ X_i − PF)`.
* Two samples: the two terms are functions of the independent sequences `ξ`, `η`
  (`IndepFun.comp`), so the characteristic function of the sum is the product
  (`IndepFun.charFun_map_fun_add_eq_mul`); it converges (`TendstoInDistribution.tendsto_charFun`) to
  `charFun N(0,a) · charFun N(0,b) = charFun (N(0,a) ∗ N(0,b)) = charFun N(0,a+b)`
  (`gaussianReal_conv_gaussianReal`), and Lévy (`TendstoInDistribution.of_tendsto_charFun`) concludes.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace StatFormal.Foundations.Donsker

section Aux

variable {ι E Ω' Ω'' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {m'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
  {mE : MeasurableSpace E} [TopologicalSpace E] [OpensMeasurableSpace E]

/-- Replace the limit variable by another one with the same law. -/
lemma tendstoInDistribution_congr_limit {X : (i : ι) → Ω i → E} {l : Filter ι} {Z : Ω' → E}
    {Z' : Ω'' → E} (h : TendstoInDistribution X l Z μ μ') (hZ' : AEMeasurable Z' μ'')
    (hlaw : μ'.map Z = μ''.map Z') : TendstoInDistribution X l Z' μ μ'' where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hZ'
  tendsto := by
    have : (⟨μ''.map Z', inferInstance⟩ : ProbabilityMeasure E) = ⟨μ'.map Z, inferInstance⟩ :=
      Subtype.ext hlaw.symm
    rw [this]
    exact h.tendsto

/-- Convergence in distribution only depends on the eventual values of the sequence. -/
lemma tendstoInDistribution_congr_eventually {X Y : (i : ι) → Ω i → E} {l : Filter ι} {Z : Ω' → E}
    (h : TendstoInDistribution X l Z μ μ') (hY : ∀ i, AEMeasurable (Y i) (μ i))
    (hXY : ∀ᶠ i in l, X i = Y i) : TendstoInDistribution Y l Z μ μ' where
  forall_aemeasurable := hY
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := by
    refine h.tendsto.congr' ?_
    filter_upwards [hXY] with i hi
    exact Subtype.ext (by simp only [hi])

end Aux

/-- Convergence in distribution along a sequence of indices tending to infinity. -/
lemma tendstoInDistribution_comp_atTop {E Ω Ω' : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {X : ℕ → Ω → E}
    {Z : Ω' → E} (h : TendstoInDistribution X atTop Z (fun _ => μ) μ') {n : ℕ → ℕ}
    (hn : Tendsto n atTop atTop) :
    TendstoInDistribution (fun k => X (n k)) atTop Z (fun _ => μ) μ' where
  forall_aemeasurable k := h.forall_aemeasurable (n k)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hn

/-- The one-sample CLT with a general rate: `r_k (P_{n_k} F − P F) ⇒ N(0, c² Var_P F)` when
`r_k / √n_k → c`. -/
theorem tendstoInDistribution_oneSample {𝒳 Ω : Type*} [MeasurableSpace 𝒳] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure 𝒳) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → 𝒳) (hξ : ∀ i, Measurable (ξ i)) (hiξ : iIndepFun ξ μ)
    (hlξ : ∀ i, μ.map (ξ i) = P) (F : 𝒳 → ℝ) (hF : Measurable F) (hFb : ∃ B, ∀ x, |F x| ≤ B)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (r : ℕ → ℝ) (c : ℝ)
    (hrn : Tendsto (fun k => r k / √(n k : ℝ)) atTop (𝓝 c)) :
    TendstoInDistribution
      (fun k ω => r k * ((∑ i ∈ Finset.range (n k), F (ξ i ω)) / n k - ∫ x, F x ∂P))
      atTop id (fun _ => μ) (gaussianReal 0 (c ^ 2 * Var[F; P]).toNNReal) := by
  set X : ℕ → Ω → ℝ := fun i ω => F (ξ i ω) with hXdef
  have hXm : ∀ i, Measurable (X i) := fun i => hF.comp (hξ i)
  have hlaw : ∀ i, μ.map (X i) = P.map F := fun i => by
    rw [← hlξ i, Measure.map_map hF (hξ i)]
    rfl
  have hident : ∀ i, IdentDistrib (X i) (X 0) μ μ := fun i =>
    ⟨(hXm i).aemeasurable, (hXm 0).aemeasurable, by rw [hlaw, hlaw]⟩
  have hindep : iIndepFun X μ := hiξ.comp (fun _ => F) (fun _ => hF)
  obtain ⟨B, hB⟩ := hFb
  have hmem : MemLp (X 0) 2 μ :=
    MemLp.of_bound (hXm 0).aestronglyMeasurable B
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB _)
  have hmean : μ[X 0] = ∫ x, F x ∂P := by
    rw [← hlξ 0, integral_map (hξ 0).aemeasurable hF.aestronglyMeasurable]
  have hvar : Var[X 0; μ] = Var[F; P] := by
    rw [← hlξ 0, variance_map hF.aemeasurable (hξ 0).aemeasurable]
    rfl
  -- the CLT along `n_k`
  have hclt := tendstoInDistribution_comp_atTop (tendstoInDistribution_inv_sqrt_mul_sum_sub (Y := id)
    (P' := gaussianReal 0 Var[X 0; μ].toNNReal) HasLaw.id hmem hindep hident) hn
  -- Slutsky with the deterministic factor `r_k / √n_k`
  have hconst : TendstoInMeasure μ (fun k (_ : Ω) => r k / √(n k : ℝ)) atTop (fun _ => c) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const) (ae_of_all _ fun _ => hrn)
  have hsl := hclt.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop) hconst (fun _ => aemeasurable_const)
  -- identify the limit law
  have hlim := tendstoInDistribution_congr_limit hsl (Z' := id) (μ'' := gaussianReal 0 (c ^ 2 * Var[F; P]).toNNReal)
    aemeasurable_id (by
      rw [Measure.map_id]
      have : (fun ω : ℝ => (id ω, c).2 * (id ω, c).1) = (c * ·) := rfl
      rw [this, gaussianReal_map_const_mul, mul_zero, hvar]
      congr 1
      ext
      simp [Real.toNNReal_mul (sq_nonneg c), Real.coe_toNNReal _ (sq_nonneg c)])
  -- the sequences agree once `n_k ≥ 1`
  refine tendstoInDistribution_congr_eventually hlim (fun k => ?_) ?_
  · exact (measurable_const.mul ((Finset.measurable_sum _ fun i _ => hXm i).div_const _
      |>.sub_const _)).aemeasurable
  · filter_upwards [hn.eventually_ge_atTop 1] with k hk
    funext ω
    rw [hmean]
    simp only [hXdef]
    have hpos : (0 : ℝ) < n k := by exact_mod_cast hk
    have hs : (0 : ℝ) < √(n k : ℝ) := Real.sqrt_pos.2 hpos
    have hn' : (n k : ℝ) = √(n k : ℝ) ^ 2 := (Real.sq_sqrt hpos.le).symm
    generalize √(n k : ℝ) = s at hs hn' ⊢
    rw [hn']
    field_simp

/-- The two-sample CLT with general rates. -/
theorem tendstoInDistribution_twoSample_clt {𝒳 Ω : Type*} [MeasurableSpace 𝒳] [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (ξ η : ℕ → Ω → 𝒳)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ j, Measurable (η j)) (hiξ : iIndepFun ξ μ) (hiη : iIndepFun η μ)
    (hlξ : ∀ i, μ.map (ξ i) = P) (hlη : ∀ j, μ.map (η j) = Q)
    (hind : IndepFun (fun ω i => ξ i ω) (fun ω j => η j ω) μ)
    (F G : 𝒳 → ℝ) (hF : Measurable F) (hG : Measurable G) (hFb : ∃ B, ∀ x, |F x| ≤ B) (hGb : ∃ B, ∀ x, |G x| ≤ B)
    (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop) (r : ℕ → ℝ) (cP cQ : ℝ)
    (hrn : Tendsto (fun k => r k / √(n k : ℝ)) atTop (𝓝 cP)) (hrm : Tendsto (fun k => r k / √(m k : ℝ)) atTop (𝓝 cQ)) :
    TendstoInDistribution
      (fun k ω => r k * ((∑ i ∈ Finset.range (n k), F (ξ i ω)) / n k - ∫ x, F x ∂P)
        + r k * ((∑ j ∈ Finset.range (m k), G (η j ω)) / m k - ∫ x, G x ∂Q))
      atTop id (fun _ => μ) (gaussianReal 0 (cP ^ 2 * Var[F; P] + cQ ^ 2 * Var[G; Q]).toNNReal) := by
  have hP := tendstoInDistribution_oneSample μ P ξ hξ hiξ hlξ F hF hFb n hn r cP hrn
  have hQ := tendstoInDistribution_oneSample μ Q η hη hiη hlη G hG hGb m hm r cQ hrm
  -- the two terms as functions of the two sequences
  set fP : ℕ → (ℕ → 𝒳) → ℝ :=
    fun k x => r k * ((∑ i ∈ Finset.range (n k), F (x i)) / n k - ∫ x, F x ∂P) with hfP
  set fQ : ℕ → (ℕ → 𝒳) → ℝ :=
    fun k x => r k * ((∑ j ∈ Finset.range (m k), G (x j)) / m k - ∫ x, G x ∂Q) with hfQ
  have hfPm : ∀ k, Measurable (fP k) := fun k =>
    measurable_const.mul (((Finset.measurable_sum _ fun i _ =>
      hF.comp (measurable_pi_apply i)).div_const _).sub_const _)
  have hfQm : ∀ k, Measurable (fQ k) := fun k =>
    measurable_const.mul (((Finset.measurable_sum _ fun i _ =>
      hG.comp (measurable_pi_apply i)).div_const _).sub_const _)
  have hξm : Measurable (fun ω i => ξ i ω) := measurable_pi_iff.2 hξ
  have hηm : Measurable (fun ω j => η j ω) := measurable_pi_iff.2 hη
  have hTP : ∀ k, Measurable (fun ω => fP k (fun i => ξ i ω)) := fun k => (hfPm k).comp hξm
  have hTQ : ∀ k, Measurable (fun ω => fQ k (fun j => η j ω)) := fun k => (hfQm k).comp hηm
  have hindk : ∀ k, IndepFun (fun ω => fP k (fun i => ξ i ω)) (fun ω => fQ k (fun j => η j ω)) μ :=
    fun k => hind.comp (hfPm k) (hfQm k)
  have hvP : 0 ≤ cP ^ 2 * Var[F; P] := mul_nonneg (sq_nonneg _) (variance_nonneg _ _)
  have hvQ : 0 ≤ cQ ^ 2 * Var[G; Q] := mul_nonneg (sq_nonneg _) (variance_nonneg _ _)
  refine TendstoInDistribution.of_tendsto_charFun (fun k => ((hTP k).add (hTQ k)).aemeasurable)
    aemeasurable_id fun t => ?_
  have hprod := (hP.tendsto_charFun t).mul (hQ.tendsto_charFun t)
  simp only [Measure.map_id] at hprod ⊢
  have hconv : gaussianReal 0 ((cP ^ 2 * Var[F; P]).toNNReal + (cQ ^ 2 * Var[G; Q]).toNNReal) =
      gaussianReal 0 (cP ^ 2 * Var[F; P]).toNNReal ∗ gaussianReal 0 (cQ ^ 2 * Var[G; Q]).toNNReal := by
    rw [gaussianReal_conv_gaussianReal, zero_add]
  rw [Real.toNNReal_add hvP hvQ, hconv, charFun_conv]
  refine hprod.congr fun k => ?_
  have := (hindk k).charFun_map_fun_add_eq_mul (hTP k).aemeasurable (hTQ k).aemeasurable
  exact (congrFun this t).symm

end StatFormal.Foundations.Donsker
