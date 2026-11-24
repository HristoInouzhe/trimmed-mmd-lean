import StatFormal.Archive.Wave24f.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Barycenter
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Rearrangement

/-!
# Route — SB `thm:copbary` (untrusted)

No Agueh–Carlier and no Brenier theorem is needed. Write `R_s = copLaw C (F_{s,·}^{-1})`, `ν = copLaw C (G^{-1})`, and
`A_s = Σ_i W₂²(F_{s,i}, G_i)` (one-dimensional distances; `G_i` is Tau Ceti's `quantileBarycenter`).
* Marginals: the `i`-th marginal of `copLaw C Q` is `Q_i # Unif(0, 1)`, so `R_s` has marginals `F_{s,i}` and `ν` has
  marginals `G_i`.
* Product lower bound: `W₂²(μ, ω) ≥ Σ_i W₂²(μ_i, ω_i)` for laws on `ℝ^d` (project every coupling).
* `T_s(F_s^{-1}(u)) = G^{-1}(u)` for `C`-a.e. `u` (`F(F^{-1}(t)) = t` a.e. for continuous `F`), so
  `(T_s)#R_s = ν` and `∫ ‖x − T_s x‖² dR_s = Σ_i ∫_0^1 |F_{s,i}^{-1} − G_i^{-1}|² = A_s`.
* Hence `A_s ≤ W₂²(R_s, ν) ≤ A_s`, and for every probability `ω`,
  `F(ω) ≥ Σ_i Σ_s p_s W₂²(F_{s,i}, ω_i) ≥ Σ_i Σ_s p_s W₂²(F_{s,i}, G_i) = Σ_s p_s A_s = F(ν)` (the one-dimensional
  barycenter inequality of Tau Ceti).
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave24f

open TauCeti
open StatFormal.OTFD.WaveL1 (Euc)

section

variable {d : ℕ}

lemma measurable_vec {Q : Fin d → ℝ → ℝ} (hQ : ∀ i, Measurable (Q i)) :
    Measurable (fun u : Fin d → ℝ => (WithLp.toLp 2 (fun i => Q i (u i)) : Euc d)) :=
  (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => (hQ i).comp (measurable_pi_apply i))

lemma measurable_coord (i : Fin d) : Measurable (fun x : Euc d => x i) :=
  (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)

lemma isProb_U01 : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩

lemma copLaw_prob {C : Measure (Fin d → ℝ)} (hC : IsCopula C) {Q : Fin d → ℝ → ℝ} (hQ : ∀ i, Measurable (Q i)) :
    IsProbabilityMeasure (copLaw C Q) := by
  have := hC.1
  unfold copLaw
  infer_instance

lemma copLaw_marg {C : Measure (Fin d → ℝ)} (hC : IsCopula C) {Q : Fin d → ℝ → ℝ} (hQ : ∀ i, Measurable (Q i))
    (i : Fin d) : (copLaw C Q).map (fun x : Euc d => x i) = (volume.restrict (Ioo (0 : ℝ) 1)).map (Q i) := by
  unfold copLaw
  rw [Measure.map_map (measurable_coord i) (measurable_vec hQ), ← hC.2 i,
    Measure.map_map (hQ i) (measurable_pi_apply i)]
  rfl

lemma edist_sq_euc (x y : Euc d) : edist x y ^ 2 = ∑ i, edist (x i) (y i) ^ 2 := by
  rw [PiLp.edist_eq_sum (by simp : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma measurable_edist_euc : Measurable fun z : Euc d × Euc d => edist z.1 z.2 := continuous_edist.measurable

lemma W2_sq_eq_transport (μ ω : Measure (Euc d)) :
    wassersteinEDist 2 μ ω ^ 2 = transportCost (fun z : Euc d × Euc d => edist z.1 z.2 ^ 2) μ ω := by
  have h := wassersteinEDist_rpow_eq_transportCost ((measurable_edist_euc : Measurable fun z : Euc d × Euc d => edist z.1 z.2)) two_ne_zero
    ENNReal.ofNat_ne_top μ ω
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  exact h

lemma W2_sq_eq_transport_real (μ ω : Measure ℝ) :
    wassersteinEDist 2 μ ω ^ 2 = transportCost (fun z : ℝ × ℝ => edist z.1 z.2 ^ 2) μ ω := by
  have h := wassersteinEDist_rpow_eq_transportCost (continuous_edist.measurable : Measurable fun z : ℝ × ℝ =>
    edist z.1 z.2) two_ne_zero ENNReal.ofNat_ne_top μ ω
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  exact h

/-- The product lower bound `Σ_i W₂²(μ_i, ω_i) ≤ W₂²(μ, ω)`. -/
lemma sum_W2_marg_le (μ ω : Measure (Euc d)) :
    ∑ i, wassersteinEDist 2 (μ.map fun x : Euc d => x i) (ω.map fun x : Euc d => x i) ^ 2 ≤
      wassersteinEDist 2 μ ω ^ 2 := by
  rw [W2_sq_eq_transport, transportCost]
  refine le_iInf₂ fun π hπ => ?_
  have hi : ∀ i, wassersteinEDist 2 (μ.map fun x : Euc d => x i) (ω.map fun x : Euc d => x i) ^ 2 ≤
      ∫⁻ z, edist (z.1 i) (z.2 i) ^ 2 ∂π := by
    intro i
    have hc := hπ.map (measurable_coord i) (measurable_coord i)
    have h := wassersteinEDist_rpow_le_lintegral (continuous_edist.measurable : Measurable fun z : ℝ × ℝ =>
      edist z.1 z.2) two_ne_zero ENNReal.ofNat_ne_top hc
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
    refine h.trans_eq ?_
    rw [lintegral_map ((continuous_edist.measurable).pow_const 2)
      ((measurable_coord i).prodMap (measurable_coord i))]
    rfl
  calc _ ≤ ∑ i, ∫⁻ z, edist (z.1 i) (z.2 i) ^ 2 ∂π := Finset.sum_le_sum fun i _ => hi i
    _ = ∫⁻ z, ∑ i, edist (z.1 i) (z.2 i) ^ 2 ∂π := by
        exact (lintegral_finsetSum _ fun i _ => by
          exact (((measurable_coord i).comp measurable_fst).edist
            ((measurable_coord i).comp measurable_snd)).pow_const 2).symm
    _ = _ := lintegral_congr fun z => (edist_sq_euc z.1 z.2).symm

end

section Main

variable {S d : ℕ} {p : Fin S → ℝ≥0} {m : Fin S → Fin d → Measure ℝ} {C : Measure (Fin d → ℝ)}

lemma measurable_baryQ (p : Fin S → ℝ≥0) (m : Fin S → Fin d → Measure ℝ) (i : Fin d) :
    Measurable (baryQ p m i) := by
  unfold baryQ
  exact Finset.measurable_sum _ fun s _ => (Measure.measurable_quantile _).const_mul _

/-- The barycentric marginal `G_i` (Tau Ceti's quantile barycenter). -/
abbrev baryM (p : Fin S → ℝ≥0) (m : Fin S → Fin d → Measure ℝ) (i : Fin d) : Measure ℝ :=
  quantileBarycenter p fun s => m s i

lemma baryM_eq (p : Fin S → ℝ≥0) (m : Fin S → Fin d → Measure ℝ) (i : Fin d) :
    baryM p m i = (volume.restrict (Ioo (0 : ℝ) 1)).map (baryQ p m i) := by
  rw [baryM, quantileBarycenter_def]; rfl

/-- `T_s(F_s^{-1}(u)) = G^{-1}(u)` for `C`-a.e. `u`. -/
lemma copMap_comp_ae (hC : IsCopula C) (hm : ∀ s i, IsProbabilityMeasure (m s i))
    (hna : ∀ s i, NullSingletonClass (m s i)) (s : Fin S) :
    ∀ᵐ u ∂C, copMap p m s (WithLp.toLp 2 (fun i => (m s i).quantile (u i))) =
      WithLp.toLp 2 (fun i => baryQ p m i (u i)) := by
  have hcoord : ∀ i, ∀ᵐ u ∂C, cdf (m s i) ((m s i).quantile (u i)) = u i := by
    intro i
    have h1 : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), cdf (m s i) ((m s i).quantile t) = t := by
      have := Measure.cdf_quantile_ae (m s i)
      have hle : volume.restrict (Ioo (0 : ℝ) 1) ≤ volume.restrict (Icc (0 : ℝ) 1) :=
        Measure.restrict_mono Set.Ioo_subset_Icc_self le_rfl
      exact ae_mono hle this
    rw [← hC.2 i] at h1
    have hmeas : MeasurableSet {t : ℝ | cdf (m s i) ((m s i).quantile t) = t} :=
      measurableSet_eq_fun ((ProbabilityTheory.cdf _).mono.measurable.comp (Measure.measurable_quantile _)) measurable_id
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h1
  have hall := ae_all_iff.2 hcoord
  filter_upwards [hall] with u hu
  unfold copMap
  congr 1
  funext i
  simp only [hu i]

lemma copMap_measurable (s : Fin S) : Measurable (copMap p m s) := by
  unfold copMap
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => ?_)
  exact (measurable_baryQ p m i).comp ((ProbabilityTheory.cdf _).mono.measurable.comp (measurable_coord i))

lemma push_eq (hC : IsCopula C) (hm : ∀ s i, IsProbabilityMeasure (m s i))
    (hna : ∀ s i, NullSingletonClass (m s i)) (s : Fin S) :
    (copLaw C fun i => (m s i).quantile).map (copMap p m s) = copLaw C (baryQ p m) := by
  unfold copLaw
  rw [Measure.map_map (copMap_measurable s) (measurable_vec fun i => Measure.measurable_quantile _)]
  exact Measure.map_congr (copMap_comp_ae hC hm hna s)

/-- `A_s = Σ_i W₂²(F_{s,i}, G_i)`. -/
abbrev Acost (p : Fin S → ℝ≥0) (m : Fin S → Fin d → Measure ℝ) (s : Fin S) : ℝ≥0∞ :=
  ∑ i, wassersteinEDist 2 (m s i) (baryM p m i) ^ 2

lemma W2_one_dim (hm : ∀ s i, IsProbabilityMeasure (m s i)) (s : Fin S) (i : Fin d) :
    wassersteinEDist 2 (m s i) (baryM p m i) ^ 2 =
      ∫⁻ t in Ioo (0 : ℝ) 1, ‖(m s i).quantile t - baryQ p m i t‖ₑ ^ 2 := by
  have h := wassersteinEDist_rpow_eq_lintegral_rpow_enorm_quantile_sub one_le_two ENNReal.ofNat_ne_top
    (m s i) (baryM p m i)
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  rw [h]
  refine lintegral_congr_ae ((quantile_quantileBarycenter_ae p fun s => m s i).mono fun t ht => ?_)
  simp only [ht, baryQ]

lemma cost_eq (hC : IsCopula C) (hm : ∀ s i, IsProbabilityMeasure (m s i))
    (hna : ∀ s i, NullSingletonClass (m s i)) (s : Fin S) :
    ∫⁻ x, ‖x - copMap p m s x‖ₑ ^ 2 ∂(copLaw C fun i => (m s i).quantile) = Acost p m s := by
  have hφ := measurable_vec (d := d) fun i => Measure.measurable_quantile (m s i)
  unfold copLaw
  beta_reduce
  rw [lintegral_map (f := fun x => ‖x - copMap p m s x‖ₑ ^ 2)
    (((measurable_id.sub (copMap_measurable s)).enorm).pow_const 2) hφ]
  have h1 : ∀ᵐ u ∂C, ‖(WithLp.toLp 2 (fun i => (m s i).quantile (u i)) : Euc d) -
      copMap p m s (WithLp.toLp 2 (fun i => (m s i).quantile (u i)))‖ₑ ^ 2 =
      ∑ i, ‖(m s i).quantile (u i) - baryQ p m i (u i)‖ₑ ^ 2 := by
    filter_upwards [copMap_comp_ae hC hm hna s] with u hu
    rw [hu, ← edist_eq_enorm_sub, edist_sq_euc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [edist_eq_enorm_sub]
  rw [lintegral_congr_ae h1, lintegral_finsetSum _ fun i _ => by
    exact ((((Measure.measurable_quantile _).comp (measurable_pi_apply i)).sub
      ((measurable_baryQ p m i).comp (measurable_pi_apply i))).enorm).pow_const 2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [W2_one_dim hm s i]
  have hmeas : Measurable fun t : ℝ => ‖(m s i).quantile t - baryQ p m i t‖ₑ ^ 2 :=
    (((Measure.measurable_quantile _).sub (measurable_baryQ p m i)).enorm).pow_const 2
  rw [← hC.2 i, lintegral_map hmeas (measurable_pi_apply i)]

lemma W2_eq (hC : IsCopula C) (hm : ∀ s i, IsProbabilityMeasure (m s i))
    (hna : ∀ s i, NullSingletonClass (m s i)) (s : Fin S) :
    wassersteinEDist 2 (copLaw C fun i => (m s i).quantile) (copLaw C (baryQ p m)) ^ 2 = Acost p m s := by
  have hq : ∀ i, Measurable ((m s i).quantile) := fun i => Measure.measurable_quantile _
  refine le_antisymm ?_ ?_
  · -- the graph coupling of `T_s`
    rw [← push_eq hC hm hna s, ← cost_eq hC hm hna s]
    have h := wassersteinEDist_map_le ((measurable_edist_euc : Measurable fun z : Euc d × Euc d => edist z.1 z.2)) (copMap_measurable (p := p) (m := m) s).aemeasurable 2
      (μ := copLaw C fun i => (m s i).quantile)
    have : IsProbabilityMeasure (copLaw C fun i => (m s i).quantile) := copLaw_prob hC hq
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top] at h
    calc _ ≤ ((∫⁻ x, ‖edist x (copMap p m s x)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(copLaw C fun i => (m s i).quantile)) ^
          (1 / (2 : ℝ≥0∞).toReal)) ^ 2 := pow_le_pow_left₀ zero_le h 2
      _ = _ := by
        simp only [ENNReal.toReal_ofNat, enorm_eq_self, edist_eq_enorm_sub]
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    exact (measurable_id.edist (copMap_measurable (p := p) (m := m) s)).aestronglyMeasurable
  · calc Acost p m s = ∑ i, wassersteinEDist 2 ((copLaw C fun i => (m s i).quantile).map fun x : Euc d => x i)
          ((copLaw C (baryQ p m)).map fun x : Euc d => x i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [copLaw_marg hC hq i, copLaw_marg hC (measurable_baryQ p m) i, Measure.map_quantile_volume_Ioo,
            ← baryM_eq]
      _ ≤ _ := sum_W2_marg_le _ _

/-- `F(ν) ≤ F(ω)` for every probability law `ω`. -/
lemma barF_le (hp : ∑ s, p s = 1) (hC : IsCopula C) (hm : ∀ s i, IsProbabilityMeasure (m s i))
    (hna : ∀ s i, NullSingletonClass (m s i)) (ω : Measure (Euc d)) [IsProbabilityMeasure ω] :
    StatFormal.Wave23a.barF p (fun s => copLaw C fun i => (m s i).quantile) (copLaw C (baryQ p m)) ≤
      StatFormal.Wave23a.barF p (fun s => copLaw C fun i => (m s i).quantile) ω := by
  have hq : ∀ s i, Measurable ((m s i).quantile) := fun s i => Measure.measurable_quantile _
  have hdr : Measurable fun z : ℝ × ℝ => edist z.1 z.2 := continuous_edist.measurable
  unfold StatFormal.Wave23a.barF
  simp_rw [W2_eq hC hm hna]
  have hωi : ∀ i, IsProbabilityMeasure (ω.map fun x : Euc d => x i) := fun i => inferInstance
  calc ∑ s, (p s : ℝ≥0∞) * Acost p m s
      = ∑ i, ∑ s, (p s : ℝ≥0∞) * wassersteinEDist 2 (baryM p m i) (m s i) ^ 2 := by
        simp only [Acost, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
        rw [wassersteinEDist_comm hdr]
    _ ≤ ∑ i, ∑ s, (p s : ℝ≥0∞) * wassersteinEDist 2 (ω.map fun x : Euc d => x i) (m s i) ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          sum_mul_wassersteinEDist_sq_quantileBarycenter_le hp (fun s => m s i) (ω.map fun x : Euc d => x i)
    _ = ∑ s, (p s : ℝ≥0∞) * ∑ i, wassersteinEDist 2 ((copLaw C fun i => (m s i).quantile).map
          fun x : Euc d => x i) (ω.map fun x : Euc d => x i) ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
        rw [copLaw_marg hC (hq s) i, Measure.map_quantile_volume_Ioo, wassersteinEDist_comm hdr]
    _ ≤ _ := Finset.sum_le_sum fun s _ => by gcongr; exact sum_W2_marg_le _ _

end Main

theorem copbary_bary : Claims.copbary_bary := by
  intro S d p m C ⟨hp, hm, hna, hC, hmom⟩
  have hq : ∀ s i, Measurable ((m s i).quantile) := fun s i => Measure.measurable_quantile _
  have hνp : IsProbabilityMeasure (copLaw C (baryQ p m)) := copLaw_prob hC (measurable_baryQ p m)
  have hle := fun ω (h : IsProbabilityMeasure ω) => @barF_le S d p m C hp hC hm hna ω h
  refine ⟨⟨hνp, ?_, fun ω hω _ => hle ω hω⟩, fun ω hω => hle ω hω⟩
  -- finite second moment of `ν`
  obtain ⟨s0, hs0⟩ : ∃ s0, p s0 ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hp
  have hR : ∀ s, IsProbabilityMeasure (copLaw C fun i => (m s i).quantile) := fun s => copLaw_prob hC (hq s)
  have hdE : Measurable fun z : Euc d × Euc d => edist z.1 z.2 := measurable_edist_euc
  have hfin : StatFormal.Wave23a.barF p (fun s => copLaw C fun i => (m s i).quantile)
      (copLaw C fun i => (m s0 i).quantile) ≠ ∞ := by
    unfold StatFormal.Wave23a.barF
    refine (ENNReal.sum_lt_top.2 fun s _ => ENNReal.mul_lt_top ENNReal.coe_lt_top ?_).ne
    have h := (hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment hdE (hmom s)).1 (hmom s0)
    exact ENNReal.pow_lt_top (lt_top_iff_ne_top.2 h)
  have hfinν := ne_top_of_le_ne_top hfin (hle _ (hR s0))
  refine hasFiniteMoment_of_sum_mul_wassersteinEDist_pow_ne_top (w := fun s => (p s : ℝ≥0∞)) (μ := fun s => copLaw C fun i => (m s i).quantile) hdE
    (Finset.mem_univ s0) (by exact_mod_cast hs0) (hmom s0) two_ne_zero ?_
  · unfold StatFormal.Wave23a.barF at hfinν
    simpa only [wassersteinEDist_comm hdE 2 (copLaw C (baryQ p m))] using hfinν

theorem copbary_map : Claims.copbary_map := by
  intro S d p m C ⟨hp, hm, hna, hC, hmom⟩ s
  exact ⟨push_eq hC hm hna s, (cost_eq hC hm hna s).trans (W2_eq hC hm hna s).symm⟩

theorem copbary_cost : Claims.copbary_cost := by
  intro S d p m C ⟨hp, hm, hna, hC, hmom⟩
  refine ⟨fun s t => (push_eq hC hm hna s).trans (push_eq hC hm hna t).symm, le_antisymm ?_ ?_⟩
  · refine le_iInf₂ fun ω hω => ?_
    have := @barF_le S d p m C hp hC hm hna ω hω
    unfold StatFormal.Wave23a.barF at this
    simp_rw [cost_eq hC hm hna, ← W2_eq hC hm hna]
    exact this
  · refine (iInf₂_le (copLaw C (baryQ p m)) (copLaw_prob hC (measurable_baryQ p m))).trans_eq ?_
    unfold StatFormal.Wave23a.barF
    simp_rw [cost_eq hC hm hna, W2_eq hC hm hna]

end StatFormal.Wave24f
