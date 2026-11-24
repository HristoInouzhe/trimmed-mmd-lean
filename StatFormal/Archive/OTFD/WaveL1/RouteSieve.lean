import StatFormal.Archive.OTFD.WaveL1.RoutePlanStab
import Mathlib.Analysis.InnerProductSpace.l2Space
import StatFormal.Archive.Wave21b.RouteSieveStrong

/-!
# Route (wave L1): sieve limits — A `prop:integrated-sieve-strong` (main limit),
# A `prop:integrated-quantile`, R `thm:moment-sieve`

Untrusted route file. The embedded sieve map `T_K = ι_K ∘ F_K ∘ Π_K` pushes the fixed source to the
coherent embedded reference `(ι_K Π_K)#μ`, is cyclically monotone a.e. (pull-back of the
finite-dimensional map, `⟨ι_K u, x⟩ = ⟨u, Π_K x⟩`), and `(ι_K Π_K)#μ → μ` weakly with converging
second moments (`ι_K Π_K y → y` for a Hilbert basis, Bessel domination). The mean-square plan
stability (`RouteL2`) then gives the limit.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL1

open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Wave8b (embed)

section Sieve

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem truncK_apply (e : ℕ → H) (K : ℕ) (x : H) (k : Fin K) : truncK e K x k = ⟪e k, x⟫ := rfl

theorem inner_embed (e : ℕ → H) (K : ℕ) (z : Euc K) (x : H) :
    ⟪embed e K z, x⟫ = ⟪z, truncK e K x⟫ := by
  simp only [embed, sum_inner, real_inner_smul_left, PiLp.inner_apply, truncK_apply,
    RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem truncK_sub (e : ℕ → H) (K : ℕ) (a b : H) :
    truncK e K (a - b) = truncK e K a - truncK e K b := by
  ext k
  simp [truncK_apply, inner_sub_right]

theorem continuous_truncK (e : ℕ → H) (K : ℕ) : Continuous (truncK e K) := by
  unfold truncK
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => continuous_const.inner continuous_id)

theorem continuous_embed (e : ℕ → H) (K : ℕ) : Continuous (embed e K) := by
  unfold embed
  exact continuous_finsetSum _ fun k _ => ((PiLp.continuous_apply 2 _ k)).smul continuous_const

theorem embed_truncK_eq (e : ℕ → H) (K : ℕ) (y : H) :
    embed e K (truncK e K y) = ∑ i ∈ Finset.range K, ⟪e i, y⟫ • e i := by
  rw [embed, ← Fin.sum_univ_eq_sum_range (fun i => ⟪e i, y⟫ • e i) K]
  rfl

/-- Bessel: `‖ι_K Π_K y‖ ≤ ‖y‖`. -/
theorem norm_embed_truncK_le {e : ℕ → H} (he : Orthonormal ℝ e) (K : ℕ) (y : H) :
    ‖embed e K (truncK e K y)‖ ≤ ‖y‖ := by
  rw [embed_truncK_eq]
  have h1 := he.inner_sum (fun i => ⟪e i, y⟫) (fun i => ⟪e i, y⟫) (Finset.range K)
  rw [real_inner_self_eq_norm_sq] at h1
  have h2 := he.sum_inner_products_le (x := y) (s := Finset.range K)
  simp only [conj_trivial, Real.norm_eq_abs, sq_abs] at h1 h2
  have h3 : ‖∑ i ∈ Finset.range K, ⟪e i, y⟫ • e i‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [h1]; simpa [sq] using h2
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

/-- `ι_K Π_K y → y` for a Hilbert basis. -/
theorem tendsto_embed_truncK [CompleteSpace H] {e : ℕ → H} (he : Orthonormal ℝ e)
    (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) (y : H) :
    Tendsto (fun K => embed e K (truncK e K y)) atTop (𝓝 y) := by
  set b := HilbertBasis.mk he hsp
  have h := (b.hasSum_repr y).tendsto_sum_nat
  simp only [b, HilbertBasis.repr_apply_apply, HilbertBasis.coe_mk] at h
  exact h.congr fun K => (embed_truncK_eq e K y).symm

/-- The embedded sieve map is cyclically monotone a.e. -/
theorem isCMMapAE_sieve [MeasurableSpace H] [OpensMeasurableSpace H] {e : ℕ → H} {K : ℕ}
    {P : Measure H} {FK : Euc K → Euc K}
    (hcm : IsCMMapAE (P.map (truncK e K)) FK) :
    IsCMMapAE P fun x => embed e K (FK (truncK e K x)) := by
  obtain ⟨S, hS, hS0, hcyc⟩ := hcm
  have hm : Measurable (truncK e K) := (continuous_truncK e K).measurable
  refine ⟨truncK e K ⁻¹' S, hm hS, ?_, ?_⟩
  · rw [Measure.map_apply hm hS.compl] at hS0
    exact hS0
  · intro m z hz
    have hw := hcyc m (fun i => (truncK e K (z i).1, FK (truncK e K (z i).1)))
      (fun i => ⟨(hz i).1, rfl⟩)
    refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_) hw
    rw [(hz i).2, inner_embed, truncK_sub]

end Sieve

section Coherent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem measurable_pk (e : ℕ → H) (K : ℕ) : Measurable fun y => embed e K (truncK e K y) :=
  ((continuous_embed e K).comp (continuous_truncK e K)).measurable

/-- Coherent truncations converge weakly: `(ι_K Π_K)#μ → μ`. -/
theorem tendsto_coherent {e : ℕ → H} (he : Orthonormal ℝ e)
    (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) (μ : ProbabilityMeasure H) :
    Tendsto (fun K => μ.map fun y => embed e K (truncK e K y)) atTop (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto]
  intro f
  simp only [ProbabilityMeasure.toMeasure_map]
  have hfm : Measurable fun y : H => (f y : ℝ≥0∞) := by fun_prop
  simp_rw [lintegral_map hfm (measurable_pk e _)]
  refine tendsto_lintegral_of_dominated_convergence (fun _ => (nndist f 0 : ℝ≥0∞))
    (fun K => hfm.comp (measurable_pk e K)) (fun K => Eventually.of_forall fun y => ?_)
    (by simp) (Eventually.of_forall fun y => ?_)
  · exact ENNReal.coe_le_coe.2 (BoundedContinuousFunction.NNReal.upper_bound f _)
  · exact (ENNReal.continuous_coe.comp f.continuous).continuousAt.tendsto.comp
      (tendsto_embed_truncK he hsp y)

/-- Coherent truncations have converging second moments. -/
theorem tendsto_mom2_coherent {e : ℕ → H} (he : Orthonormal ℝ e)
    (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) {μ : Measure H}
    (hμ2 : Mom2 μ ≠ ∞) :
    Tendsto (fun K => Mom2 (μ.map fun y => embed e K (truncK e K y))) atTop (𝓝 (Mom2 μ)) := by
  simp_rw [← lintegral_map_enorm_sq (measurable_pk e _)]
  refine tendsto_lintegral_of_dominated_convergence (fun y => ‖y‖ₑ ^ 2)
    (fun K => measurable_enorm_sq.comp (measurable_pk e K)) (fun K => Eventually.of_forall fun y => ?_)
    hμ2 (Eventually.of_forall fun y => ?_)
  · change ‖embed e K (truncK e K y)‖ₑ ^ 2 ≤ ‖y‖ₑ ^ 2
    gcongr
    rw [enorm_le_iff_norm_le]
    exact norm_embed_truncK_le he K y
  · exact (ENNReal.continuous_pow 2 |>.comp continuous_enorm).continuousAt.tendsto.comp
      (tendsto_embed_truncK he hsp y)

/-- **Sieve core**: with `T_K = ι_K ∘ F_K ∘ Π_K`, `E‖T_K(X) − F(X)‖² → 0`. -/
theorem sieve_core {e : ℕ → H} {P μ : ProbabilityMeasure H} {F : H → H}
    {FK : (K : ℕ) → Euc K → Euc K} (he : Orthonormal ℝ e)
    (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure)
    (hμ2 : Mom2 (μ : Measure H) ≠ ∞) (hF : Measurable F)
    (huniq : BrenierUniq (P : Measure H) μ F) (hFK : ∀ K, Measurable (FK K))
    (hpush : ∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K))
    (hcm : ∀ K, IsCMMapAE ((P : Measure H).map (truncK e K)) (FK K)) :
    Tendsto (fun K => ∫⁻ x, ‖embed e K (FK K (truncK e K x)) - F x‖ₑ ^ 2 ∂(P : Measure H))
      atTop (𝓝 0) := by
  set ν : ℕ → ProbabilityMeasure H := fun K => μ.map fun y => embed e K (truncK e K y)
    with hνdef
  have hmt : ∀ K, Measurable (truncK e K) := fun K => (continuous_truncK e K).measurable
  have hme : ∀ K, Measurable (embed e K) := fun K => (continuous_embed e K).measurable
  have hT : ∀ K, Measurable fun x => embed e K (FK K (truncK e K x)) := fun K =>
    (hme K).comp ((hFK K).comp (hmt K))
  have hTν : ∀ K, (P : Measure H).map (fun x => embed e K (FK K (truncK e K x))) = ν K := by
    intro K
    simp only [hνdef, ProbabilityMeasure.toMeasure_map]
    have h1 : (fun x => embed e K (FK K (truncK e K x))) = embed e K ∘ FK K ∘ truncK e K := rfl
    have h2 : (fun y => embed e K (truncK e K y)) = embed e K ∘ truncK e K := rfl
    rw [h1, h2, ← Measure.map_map (hme K) ((hFK K).comp (hmt K)),
      ← Measure.map_map (hFK K) (hmt K), hpush K, Measure.map_map (hme K) (hmt K)]
  have hν : Tendsto ν atTop (𝓝 μ) := tendsto_coherent he hsp μ
  have hmom : Tendsto (fun K => Mom2 (ν K : Measure H)) atTop (𝓝 (Mom2 (μ : Measure H))) :=
    tendsto_mom2_coherent he hsp hμ2
  exact tendsto_L2_map hF hT hTν (fun K => isCMMapAE_sieve (hcm K)) fun π hfst hsnd hcmπ =>
    tendsto_L2_of_cmConc hF huniq hν hmom hμ2 hfst hsnd hcmπ

/-- Under the sieve hypotheses the limit map pushes `P` to `μ` (it is the limit coupling). -/
theorem sieve_map_eq {e : ℕ → H} {P μ : ProbabilityMeasure H} {F : H → H}
    {FK : (K : ℕ) → Euc K → Euc K} (he : Orthonormal ℝ e)
    (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) (hF : Measurable F)
    (huniq : BrenierUniq (P : Measure H) μ F) (hFK : ∀ K, Measurable (FK K))
    (hpush : ∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K))
    (hcm : ∀ K, IsCMMapAE ((P : Measure H).map (truncK e K)) (FK K)) :
    (P : Measure H).map F = μ := by
  set ν : ℕ → ProbabilityMeasure H := fun K => μ.map fun y => embed e K (truncK e K y)
    with hνdef
  have hmt : ∀ K, Measurable (truncK e K) := fun K => (continuous_truncK e K).measurable
  have hme : ∀ K, Measurable (embed e K) := fun K => (continuous_embed e K).measurable
  set T : ℕ → H → H := fun K x => embed e K (FK K (truncK e K x)) with hTdef
  have hT : ∀ K, Measurable (T K) := fun K => (hme K).comp ((hFK K).comp (hmt K))
  have hTν : ∀ K, (P : Measure H).map (T K) = ν K := by
    intro K
    simp only [hνdef, hTdef, ProbabilityMeasure.toMeasure_map]
    have h1 : (fun x => embed e K (FK K (truncK e K x))) = embed e K ∘ FK K ∘ truncK e K := rfl
    have h2 : (fun y => embed e K (truncK e K y)) = embed e K ∘ truncK e K := rfl
    rw [h1, h2, ← Measure.map_map (hme K) ((hFK K).comp (hmt K)),
      ← Measure.map_map (hFK K) (hmt K), hpush K, Measure.map_map (hme K) (hmt K)]
  set π : ℕ → ProbabilityMeasure (H × H) := fun K => P.map fun x => (x, T K x) with hπdef
  have hfst : ∀ K, (π K : Measure (H × H)).fst = P := fun K => graph_fst (hT K)
  have hsnd : ∀ K, (π K : Measure (H × H)).snd = ν K := fun K => (graph_snd (hT K)).trans (hTν K)
  have hconv : Tendsto π atTop (𝓝 (P.map fun x => (x, F x))) :=
    tendsto_of_cmConc huniq tendsto_const_nhds (tendsto_coherent he hsp μ) hfst hsnd
      (fun K => cmConc_graph (hT K) (isCMMapAE_sieve (hcm K))) rfl
  have hcoupG : TauCeti.IsCoupling ((P.map fun x => (x, F x) : ProbabilityMeasure (H × H)) : Measure (H × H))
      P μ :=
    TauCeti.isCoupling_of_tendsto (Eventually.of_forall fun K => ⟨hfst K, hsnd K⟩) hconv
      tendsto_const_nhds (tendsto_coherent he hsp μ)
  rw [← graph_snd hF]; exact hcoupG.snd_eq

end Coherent

/-! ### The claims -/

theorem sieve_strong_limit : Claims.sieve_strong_limit := by
  intro H _ _ _ _ _ _ e P μ F M FK he hsp _ hμM hF huniq hFK hpush hcm
  exact sieve_core he hsp (mom2_ne_top_of_bounded hμM) hF huniq hFK hpush hcm

theorem sieve_strong_full : Claims.sieve_strong_full := by
  intro H _ _ _ _ _ _ e P μ F M FK c he hsp _ hμM hμ0 hF huniq hFK hpush hcm
  have hL2 := sieve_core he hsp (mom2_ne_top_of_bounded hμM) hF huniq hFK hpush hcm
  have hmap := sieve_map_eq he hsp hF huniq hFK hpush hcm
  have hT : ∀ K, Measurable fun x => embed e K (FK K (truncK e K x)) := fun K =>
    (continuous_embed e K).measurable.comp ((hFK K).comp (continuous_truncK e K).measurable)
  have h0 : (P : Measure H) {x | F x = 0} = 0 := by
    have : (P : Measure H) (F ⁻¹' {0}) = 0 := by
      rw [← Measure.map_apply hF (measurableSet_singleton 0), hmap]; exact hμ0
    exact this
  exact ⟨StatFormal.Wave21b.sieve_strong_radial H H _ _ _ hL2,
    StatFormal.Wave21b.sieve_strong_signs_prob H H _ _ _ c (fun K => (hT K).aestronglyMeasurable)
      hF.aestronglyMeasurable hL2 h0,
    StatFormal.Wave21b.sieve_strong_signs_L2 H H _ _ _ c (fun K => (hT K).aestronglyMeasurable)
      hF.aestronglyMeasurable hL2 h0⟩

theorem integrated_quantile : Claims.integrated_quantile := by
  intro H _ _ _ _ _ _ e P μ Q M QK he hsp hP _ hQ huniq hQK hpush hcm
  exact sieve_core he hsp hP.2.1.ne hQ huniq hQK hpush hcm

theorem moment_sieve_a : Claims.moment_sieve_a := by
  intro H _ _ _ _ _ _ e P μ F FK he hsp _ hμ2 hF huniq hFK hpush hcm
  exact sieve_core he hsp hμ2 hF huniq hFK hpush hcm

theorem moment_sieve_b : Claims.moment_sieve_b := by
  intro H _ _ _ _ _ _ e P μ Q QK he hsp hP _ hQ huniq hQK hpush hcm
  exact sieve_core he hsp hP.2.1.ne hQ huniq hQK hpush hcm

end StatFormal.OTFD.WaveL1
