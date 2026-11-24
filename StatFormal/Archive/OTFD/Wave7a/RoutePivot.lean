import StatFormal.Archive.OTFD.Wave7a.Statements
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Route: C `prop:cond-sign-pivot`

* Disintegration: for Borel `A ⊆ ℝ^q × ℝ^K`, `(π ⊗ₘ κ)((id, F)⁻¹A) = ∫ κ_c{z : (c, F(c,z)) ∈ A} dπ(c)`, and on
  `𝒳_ac` the inner measure is `μ_K(A_c)` by the rank-map identity; so the joint law is `π ⊗ μ_K`.
* Groups: the sign law is `∫ k_g dπ` (`compProd_apply`); Dirac covariate laws give the "only if" halves.
* Reweighting: `lintegral_compProd` and `lintegral_rnDeriv_mul`.
* Example: `P_{1,c} = μ = Unif[−½,½]`, `F(c,z) = z`, a group with `Z = C` (Dirac kernel), covariate laws `δ_{1}` and
  `δ_{−1}`: the sign laws are `δ_{s(1)}` and `δ_{s(−1)}`, separated by the sign of the coordinate.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.OTFD.Wave7a

variable {q K : ℕ} {𝒮 : Type*} [MeasurableSpace 𝒮]

lemma meas_sec {F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ} (hF : Measurable F) (c : Fin q → ℝ) :
    Measurable fun z => F (c, z) := hF.comp measurable_prodMk_left

lemma meas_sec_s {F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ} {s : (Fin K → ℝ) → 𝒮} (hF : Measurable F)
    (hs : Measurable s) (c : Fin q → ℝ) : Measurable fun z => s (F (c, z)) := hs.comp (meas_sec hF c)

lemma joint_map_eq {μ : Measure (Fin K → ℝ)} [IsProbabilityMeasure μ] {κ : Kernel (Fin q → ℝ) (Fin K → ℝ)}
    [IsMarkovKernel κ] {X : Set (Fin q → ℝ)} {F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ}
    {π : Measure (Fin q → ℝ)} [IsProbabilityMeasure π] (hX : MeasurableSet X) (hF : IsRankMap μ κ X F)
    (hπ : π X = 1) : (π ⊗ₘ κ).map (fun p => (p.1, F p)) = π.prod μ := by
  have hΦ : Measurable fun p : (Fin q → ℝ) × (Fin K → ℝ) => (p.1, F p) := measurable_fst.prodMk hF.1
  have hae : ∀ᵐ c ∂π, c ∈ X := by
    rw [ae_iff]; exact (prob_compl_eq_zero_iff hX).2 hπ
  ext A hA
  rw [Measure.map_apply hΦ hA, Measure.compProd_apply (hΦ hA), Measure.prod_apply hA]
  refine lintegral_congr_ae (hae.mono fun c hc => ?_)
  dsimp only
  rw [← hF.2 c hc, Measure.map_apply (meas_sec hF.1 c) (measurable_prodMk_left hA)]
  rfl

theorem pivot_joint : Claims.pivot_joint := by
  intro q K Ω _ P _ μ _ κ _ X F π _ C Z hX hF hπ hC hZ hlaw
  have hΦ : Measurable fun p : (Fin q → ℝ) × (Fin K → ℝ) => (p.1, F p) := measurable_fst.prodMk hF.1
  have e : (fun ω => (C ω, F (C ω, Z ω))) = (fun p => (p.1, F p)) ∘ fun ω => (C ω, Z ω) := rfl
  rw [e, ← Measure.map_map hΦ (hC.prodMk hZ), hlaw, joint_map_eq hX hF hπ]

lemma indep_of_joint {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
    [IsProbabilityMeasure P] {π : Measure (Fin q → ℝ)} [IsProbabilityMeasure π] {ν : Measure β}
    [IsProbabilityMeasure ν] {C : Ω → Fin q → ℝ} {W : Ω → β} (hC : Measurable C) (hW : Measurable W)
    (h : P.map (fun ω => (C ω, W ω)) = π.prod ν) : IndepFun C W P ∧ P.map W = ν := by
  have hCl : P.map C = π := by
    have : P.map C = (P.map (fun ω => (C ω, W ω))).map Prod.fst := by
      rw [Measure.map_map measurable_fst (hC.prodMk hW)]; rfl
    rw [this, h]; exact Measure.fst_prod
  have hWl : P.map W = ν := by
    have : P.map W = (P.map (fun ω => (C ω, W ω))).map Prod.snd := by
      rw [Measure.map_map measurable_snd (hC.prodMk hW)]; rfl
    rw [this, h]; exact Measure.snd_prod
  refine ⟨(indepFun_iff_map_prod_eq_prod_map_map hC.aemeasurable hW.aemeasurable).2 ?_, hWl⟩
  rw [hCl, hWl, h]

theorem pivot_indep : Claims.pivot_indep := by
  intro q K Ω _ P _ μ _ κ _ X F π _ C Z hX hF hπ hC hZ hlaw
  exact indep_of_joint hC (hF.1.comp (hC.prodMk hZ))
    (pivot_joint q K Ω P μ κ X F π C Z hX hF hπ hC hZ hlaw)

theorem pivot_sign : Claims.pivot_sign := by
  intro q K 𝒮 _ Ω _ P _ μ _ κ _ X F s π _ C Z hX hF hs hπ hC hZ hlaw
  have hW : Measurable fun ω => F (C ω, Z ω) := hF.1.comp (hC.prodMk hZ)
  have hj := pivot_joint q K Ω P μ κ X F π C Z hX hF hπ hC hZ hlaw
  refine indep_of_joint (P := P) (π := π) (ν := μ.map s) hC (hs.comp hW) ?_
  have e : (fun ω => (C ω, s (F (C ω, Z ω)))) = Prod.map id s ∘ fun ω => (C ω, F (C ω, Z ω)) := rfl
  rw [e, ← Measure.map_map (measurable_id.prodMap hs) (hC.prodMk hW), hj,
    ← Measure.map_prod_map π μ measurable_id hs, Measure.map_id]

lemma signLaw_apply {κg : Kernel (Fin q → ℝ) (Fin K → ℝ)} [IsMarkovKernel κg]
    {F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ} {s : (Fin K → ℝ) → 𝒮} {π : Measure (Fin q → ℝ)}
    [IsProbabilityMeasure π] (hF : Measurable F) (hs : Measurable s) {E : Set 𝒮} (hE : MeasurableSet E) :
    signLaw s F π κg E = ∫⁻ c, kLaw s F κg c E ∂π := by
  have hm : Measurable fun p => s (F p) := hs.comp hF
  unfold signLaw kLaw
  rw [Measure.map_apply hm hE, Measure.compProd_apply (hm hE)]
  refine lintegral_congr fun c => ?_
  rw [Measure.map_apply (meas_sec_s hF hs c) hE]
  rfl

theorem groups_mix : Claims.groups_mix := by
  intro q K 𝒮 _ κg _ F s π _ hF hs E hE
  exact signLaw_apply hF hs hE

lemma signLaw_dirac {κg : Kernel (Fin q → ℝ) (Fin K → ℝ)} [IsMarkovKernel κg]
    {F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ} {s : (Fin K → ℝ) → 𝒮} (hF : Measurable F)
    (hs : Measurable s) (c : Fin q → ℝ) : signLaw s F (Measure.dirac c) κg = kLaw s F κg c := by
  ext E hE
  rw [signLaw_apply hF hs hE, lintegral_dirac]

lemma signLaw_of_ae {κg : Kernel (Fin q → ℝ) (Fin K → ℝ)} [IsMarkovKernel κg]
    {F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ} {s : (Fin K → ℝ) → 𝒮} {π : Measure (Fin q → ℝ)}
    [IsProbabilityMeasure π] (hF : Measurable F) (hs : Measurable s) {ν : Measure 𝒮}
    (h : ∀ᵐ c ∂π, kLaw s F κg c = ν) : signLaw s F π κg = ν := by
  ext E hE
  rw [signLaw_apply hF hs hE, lintegral_congr_ae (h.mono fun c hc => by rw [hc]), lintegral_const,
    measure_univ, mul_one]

lemma ae_mem_of {π : Measure (Fin q → ℝ)} [IsProbabilityMeasure π] {X : Set (Fin q → ℝ)}
    (hX : MeasurableSet X) (hπ : π X = 1) : ∀ᵐ c ∂π, c ∈ X := by
  rw [ae_iff]; exact (prob_compl_eq_zero_iff hX).2 hπ

theorem groups_const_iff : Claims.groups_const_iff := by
  intro q K 𝒮 _ κg _ X F s hX hF hs
  constructor
  · intro h c hc c' hc'
    have := h (Measure.dirac c) (Measure.dirac c') inferInstance inferInstance
      (Measure.dirac_apply_of_mem hc) (Measure.dirac_apply_of_mem hc')
    rwa [signLaw_dirac hF hs, signLaw_dirac hF hs] at this
  · intro h π π' hp hp' hπ hπ'
    obtain ⟨c0, hc0⟩ : X.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, measure_empty] at hπ
      exact zero_ne_one hπ
    rw [signLaw_of_ae hF hs ((ae_mem_of hX hπ).mono fun c hc => h c hc c0 hc0),
      signLaw_of_ae hF hs ((ae_mem_of hX hπ').mono fun c hc => h c hc c0 hc0)]

theorem groups_ref_iff : Claims.groups_ref_iff := by
  intro q K 𝒮 _ μ κg _ X F s hX hF hs
  constructor
  · intro h c hc
    have := h (Measure.dirac c) inferInstance (Measure.dirac_apply_of_mem hc)
    rwa [signLaw_dirac hF hs] at this
  · intro h π hp hπ
    exact signLaw_of_ae hF hs ((ae_mem_of hX hπ).mono fun c hc => h c hc)

theorem groups_fitted : Claims.groups_fitted := by
  intro q K 𝒮 _ μ κ κg X F s hF hs hk c hc
  unfold kLaw
  rw [hk c hc, ← hF.2 c hc, Measure.map_map hs (meas_sec hF.1 c)]
  rfl

theorem diff_shows : Claims.diff_shows := by
  intro q K 𝒮 _ μ _ κ κg _ _ X F s π _ hX hF hs hπ hne hae
  apply hne
  refine signLaw_of_ae hF.1 hs ?_
  filter_upwards [hae, ae_mem_of hX hπ] with c hc hcX
  unfold kLaw
  rw [hc, ← hF.2 c hcX, Measure.map_map hs (meas_sec hF.1 c)]
  rfl

theorem common_law : Claims.common_law := by
  intro q K 𝒮 _ κg κh _ _ F s πs _ hF hs hae
  ext E hE
  rw [signLaw_apply hF hs hE, signLaw_apply hF hs hE]
  exact lintegral_congr_ae (hae.mono fun c hc => by simp only [kLaw, hc])

lemma kLaw_meas {κg : Kernel (Fin q → ℝ) (Fin K → ℝ)} [IsMarkovKernel κg]
    {F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ} {s : (Fin K → ℝ) → 𝒮} (hF : Measurable F)
    (hs : Measurable s) {E : Set 𝒮} (hE : MeasurableSet E) : Measurable fun c => kLaw s F κg c E := by
  have hm : Measurable fun p => s (F p) := hs.comp hF
  have e : (fun c => kLaw s F κg c E) = fun c => κg c (Prod.mk c ⁻¹' ((fun p => s (F p)) ⁻¹' E)) := by
    funext c; unfold kLaw
    rw [Measure.map_apply (meas_sec_s hF hs c) hE]; rfl
  rw [e]
  exact Kernel.measurable_kernel_prodMk_left (hm hE)

theorem reweight : Claims.reweight := by
  intro q K 𝒮 _ Ω _ P _ κg _ F s πg πs _ _ C Z hF hs hC hZ hlaw hac E hE
  have hm : Measurable fun p => s (F p) := hs.comp hF
  set f : (Fin q → ℝ) × (Fin K → ℝ) → ℝ≥0∞ :=
    fun p => πs.rnDeriv πg p.1 * E.indicator 1 (s (F p)) with hf
  have hfm : Measurable f :=
    ((Measure.measurable_rnDeriv πs πg).comp measurable_fst).mul
      ((measurable_one.indicator hE).comp hm)
  have e1 : ∫⁻ ω, πs.rnDeriv πg (C ω) * E.indicator 1 (s (F (C ω, Z ω))) ∂P =
      ∫⁻ p, f p ∂(P.map fun ω => (C ω, Z ω)) := by
    rw [lintegral_map hfm (hC.prodMk hZ)]
  rw [e1, hlaw, Measure.lintegral_compProd hfm]
  have e2 : ∀ c, ∫⁻ z, f (c, z) ∂κg c = πs.rnDeriv πg c * kLaw s F κg c E := by
    intro c
    simp only [hf]
    rw [lintegral_const_mul (πs.rnDeriv πg c) (f := fun z => E.indicator 1 (s (F (c, z))))
      ((measurable_one.indicator hE).comp (meas_sec_s hF hs c))]
    congr 1
    unfold kLaw
    rw [Measure.map_apply (meas_sec_s hF hs c) hE, ← lintegral_indicator_one
      ((meas_sec_s hF hs c) hE)]
    exact lintegral_congr fun z => rfl
  simp_rw [e2]
  exact lintegral_rnDeriv_mul hac (kLaw_meas hF hs hE).aemeasurable

theorem imbalance_example : Claims.imbalance_example := by
  set a : Fin 1 → ℝ := fun _ => -(1 / 2)
  set b : Fin 1 → ℝ := fun _ => 1 / 2
  set μ : Measure (Fin 1 → ℝ) := volume.restrict (Icc a b)
  have hμ : IsProbabilityMeasure μ := ⟨by
    simp only [μ, Measure.restrict_apply_univ, Real.volume_Icc_pi, a, b]; norm_num⟩
  set κ : Kernel (Fin 1 → ℝ) (Fin 1 → ℝ) := Kernel.const _ μ
  set κg : Kernel (Fin 1 → ℝ) (Fin 1 → ℝ) := Kernel.deterministic id measurable_id
  set F : (Fin 1 → ℝ) × (Fin 1 → ℝ) → Fin 1 → ℝ := fun p => p.2
  have hF : Measurable F := measurable_snd
  set one : Fin 1 → ℝ := fun _ => 1
  set mone : Fin 1 → ℝ := fun _ => -1
  refine ⟨μ, κ, κg, univ, F, Measure.dirac one, Measure.dirac mone, hμ,
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self, ?_, inferInstance, inferInstance,
    MeasurableSet.univ, fun c _ => Measure.absolutelyContinuous_of_le Measure.restrict_le_self,
    ⟨hF, fun c _ => by simp [κ, F, Measure.map_id']⟩, fun c _ => monotone_id, inferInstance,
    inferInstance, Measure.dirac_apply_of_mem (mem_univ _), Measure.dirac_apply_of_mem (mem_univ _), ?_⟩
  · have h0 : ({0} : Set (Fin 1 → ℝ)) = Icc 0 0 := (Set.Icc_self 0).symm
    refine le_antisymm ?_ bot_le
    calc μ {0} ≤ volume ({0} : Set (Fin 1 → ℝ)) := Measure.restrict_le_self _
      _ = 0 := by rw [h0, Real.volume_Icc_pi]; simp
  · intro ρ hρ hpos
    set s : (Fin 1 → ℝ) → Fin 1 → ℝ := fun u => (ρ u)⁻¹ • u
    have hs : Measurable s := measurable_pi_iff.2 fun i =>
      (hρ.inv).mul (measurable_pi_apply i)
    have hsl : ∀ c, signLaw s F (Measure.dirac c) κg = Measure.dirac (s c) := by
      intro c
      rw [signLaw_dirac hF hs]
      unfold kLaw
      simp only [κg, Kernel.deterministic_apply, F]
      exact Measure.map_dirac' hs c
    rw [hsl, hsl]
    intro heq
    have hS : MeasurableSet {v : Fin 1 → ℝ | 0 < v 0} :=
      measurableSet_lt measurable_const (measurable_pi_apply 0)
    have h1 : 0 < s one 0 := by
      simp only [s, one, Pi.smul_apply, smul_eq_mul, mul_one]
      exact inv_pos.2 (hpos _ fun h => by simpa using congrFun h 0)
    have h2 : ¬ 0 < s mone 0 := by
      simp only [s, mone, Pi.smul_apply, smul_eq_mul, mul_neg, mul_one, not_lt, neg_nonpos]
      exact (inv_pos.2 (hpos _ fun h => by simpa using congrFun h 0)).le
    have := congrArg (fun m : Measure (Fin 1 → ℝ) => m {v | 0 < v 0}) heq
    simp only [Measure.dirac_apply' _ hS, Set.indicator_apply, mem_setOf_eq, h1, h2,
      if_true, if_false, Pi.one_apply] at this
    exact one_ne_zero this

end StatFormal.OTFD.Wave7a
