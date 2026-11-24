import StatFormal.Archive.Wave30h.RouteQuantiles
import StatFormal.Archive.Wave30h.RouteDKW
import StatFormal.Archive.Wave30h.RouteFieldJ
import StatFormal.Archive.Wave24e.RouteCop

/-!
# Route — `cor:field-cop`, journal form (untrusted)

* (ii) `fieldcop_fwd`: on the DKW event of all coordinates, `|F̃_{n,i} − F_i| ≤ M/√n + 1/n` everywhere
  (`quantiles_cdf`), so `‖Ŝ_μ − S_μ‖_{L²(μ)} ≤ d(M + 1)/√n = √d(M + 1)√(d/n)`.
* (iii) `fieldcop_inv`: `S'(u) = (F_i^{-1}(clamp₀₁ u_i))_i` with `F_i^{-1}` extended `L`-Lipschitz from `(0,1)`
  (McShane), equal to `copInv ν` on `(0,1)^d`, which carries `γ = (S_ν)_#ν` (`ass:marg`: the cdfs map `(a_i, b_i)`
  into `(0,1)`). `Q̃_{n,i}(w) = Q̃_{n,i}(clamp₀₁ w)`, so `sup_w |Q̃_{n,i} − S'_i| = sup_{(0,1)}`, bounded by
  `quantiles_quant` on the DKW event intersected with the full-probability event that the sample lies in the
  supports; `h_n = Ŝ_ν⁻¹ − S'`, `k_n = 0`.
* `fieldcop_rate`: `fieldJ_rate` with (i) from the certified Wave 24e `field_cop_standardises`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave30h

open StatFormal.Wave9b (Standardises BigOP)
open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.Wave24f (marg)
open StatFormal.Wave24e (copStd copInv)

variable {d : ℕ}

lemma norm_le_sum_abs (v : Euc d) : ‖v‖ ≤ ∑ i, |v i| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
  simp only [Real.norm_eq_abs]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _

lemma norm_le_of_coord {v : Euc d} {c : ℝ} (h : ∀ i, |v i| ≤ c) : ‖v‖ ≤ d * c := by
  refine (norm_le_sum_abs v).trans ?_
  calc ∑ i, |v i| ≤ ∑ _i : Fin d, c := Finset.sum_le_sum fun i _ => h i
    _ = d * c := by simp

lemma eLpNorm_le_of_coord {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f : Euc d → Euc d}
    (hf : Measurable f) {c : ℝ} (h : ∀ x i, |f x i| ≤ c) : eLpNorm f 2 μ ≤ ENNReal.ofReal (d * c) := by
  refine (eLpNorm_le_of_ae_bound hf.aestronglyMeasurable (.of_forall fun x => norm_le_of_coord (h x))).trans ?_
  simp

/-! ### Measurability and continuity of the estimators -/

lemma ramp_mono (a b : ℝ) : Monotone (ramp a b) := by
  intro s t hst
  unfold ramp
  split_ifs with h1 h2 h3
  · exact clamp01_mono (div_le_div_of_nonneg_right (by linarith) (by linarith))
  · norm_num
  · exact absurd (h2.trans hst) h3
  · norm_num
  · exact le_rfl

lemma interpCdf_mono {n : ℕ} (x : Fin n → ℝ) : Monotone (interpCdf x) := by
  intro s t hst
  unfold interpCdf
  refine div_le_div_of_nonneg_right (add_le_add ?_ (Finset.sum_le_sum fun j _ => ramp_mono _ _ hst)) (by positivity)
  split_ifs with h1 h2 <;> first | exact absurd (h1.trans hst) h2 | norm_num

lemma measurable_copStdHat {n : ℕ} (X : Fin n → Euc d) : Measurable (copStdHat X) :=
  (WithLp.measurable_toLp (p := 2) (X := Fin d → ℝ)).comp
    (Measurable.of_eval fun i => (interpCdf_mono _).measurable.comp (StatFormal.Wave24e.measurable_coord i))

lemma continuous_clamp01 : Continuous clamp01 := by
  unfold clamp01; fun_prop

lemma continuous_interpQuant {n : ℕ} (x : Fin n → ℝ) : Continuous (interpQuant x) := by
  unfold interpQuant
  refine continuous_const.add (continuous_finset_sum _ fun j _ => continuous_const.mul ?_)
  exact continuous_clamp01.comp (by fun_prop)

lemma continuous_copInvHat {n : ℕ} (Z : Fin n → Euc d) : Continuous (copInvHat Z) := by
  unfold copInvHat
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => (continuous_interpQuant _).comp ?_)
  exact (EuclideanSpace.proj i).continuous

lemma clamp01_idem (w : ℝ) : clamp01 (clamp01 w) = clamp01 w := by
  unfold clamp01
  have h0 : 0 ≤ max 0 (min w 1) := le_max_left _ _
  have h1 : max 0 (min w 1) ≤ 1 := max_le zero_le_one (min_le_right _ _)
  rw [min_eq_left h1, max_eq_right h0]

lemma clamp01_of_mem {w : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) : clamp01 w = w := by
  unfold clamp01; rw [min_eq_left hw.2, max_eq_right hw.1]

lemma abs_clamp01_sub (u v : ℝ) : |clamp01 u - clamp01 v| ≤ |u - v| := by
  unfold clamp01
  calc |max 0 (min u 1) - max 0 (min v 1)| ≤ max |(0 : ℝ) - 0| |min u 1 - min v 1| := abs_max_sub_max_le_max _ _ _ _
    _ ≤ |u - v| := by
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
        exact (abs_min_sub_min_le_max _ _ _ _).trans (by simp)

lemma interpQuant_clamp {n : ℕ} (x : Fin n → ℝ) (w : ℝ) : interpQuant x w = interpQuant x (clamp01 w) := by
  unfold interpQuant
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  congr 1
  rcases lt_or_ge w 0 with hw | hw
  · have : clamp01 w = 0 := clamp01_of_nonpos hw.le
    rw [this, clamp01_of_nonpos, clamp01_of_nonpos] <;>
      nlinarith [show (0 : ℝ) ≤ n by positivity, show (0 : ℝ) ≤ j by positivity]
  rcases le_or_gt w 1 with hw1 | hw1
  · rw [clamp01_of_mem ⟨hw, hw1⟩]
  · have : clamp01 w = 1 := clamp01_of_one_le hw1.le
    have hjn : (j : ℝ) + 2 ≤ n := by exact_mod_cast (show j + 2 ≤ n by omega)
    rw [this, clamp01_of_one_le, clamp01_of_one_le] <;> nlinarith

/-! ### (ii) -/

theorem fieldcop_fwd : Claims.fieldcop_fwd := by
  intro d μ _ Ω _ P _ X _ hX hind hlaw
  rw [bigOP_iff_compl (fun n => Real.sqrt_nonneg _)]
  intro η hη
  obtain ⟨M, hM, hA⟩ := dkw_coords hX hind hlaw hη
  refine ⟨Real.sqrt d * (M + 1), by positivity, 1, fun n hn => ?_⟩
  obtain ⟨A, hAm, hPA, hb⟩ := hA n hn
  refine ⟨A, hAm, hPA, fun ω hω => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq : 1 / (n : ℝ) ≤ 1 / Real.sqrt n := by
    rw [div_le_div_iff₀ hnpos (Real.sqrt_pos.2 hnpos), one_mul, one_mul]
    calc Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := le_mul_of_one_le_left (Real.sqrt_nonneg _)
          (Real.one_le_sqrt.2 (by exact_mod_cast hn))
      _ = n := Real.mul_self_sqrt hnpos.le
  have hcoord : ∀ x i, |(copStdHat (fun j : Fin n => X j ω) x - copStd μ x) i| ≤ (M + 1) * (1 / Real.sqrt n) := by
    intro x i
    have : IsProbabilityMeasure (marg μ i) := by unfold marg; infer_instance
    have h := quantiles_cdf (marg μ i) n (fun j => X j ω i) (M * (1 / Real.sqrt n)) hn (hb ω hω i) (x i)
    simp only [PiLp.sub_apply, copStdHat, copStd]
    exact h.trans (by nlinarith)
  refine (eLpNorm_le_of_coord ((measurable_copStdHat _).sub (StatFormal.Wave24e.measurable_copStd μ)) hcoord).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [Real.sqrt_div' _ (Nat.cast_nonneg n), show Real.sqrt d * (M + 1) * (Real.sqrt d / Real.sqrt n) =
    (Real.sqrt d * Real.sqrt d) * ((M + 1) * (1 / Real.sqrt n)) by ring, Real.mul_self_sqrt (Nat.cast_nonneg _)]

/-! ### (iii) -/

section Inv
variable {F : Measure ℝ} [IsProbabilityMeasure F] {L : ℝ≥0} {a b : ℝ}

lemma AssMarg.null_compl_Ioo (h : AssMarg L a b F) : F (Ioo a b)ᶜ = 0 := by
  obtain ⟨-, -, -, hup⟩ := h
  refine le_antisymm ((hup _).trans ?_) zero_le
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (measurableSet_Ioo.compl)]
  have : (Ioo a b)ᶜ ∩ Icc a b ⊆ {a, b} := by
    intro z ⟨hz1, hz2⟩
    simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt] at hz1
    rcases hz1 with h | h
    · left; exact le_antisymm h hz2.1
    · right; exact le_antisymm hz2.2 h
  rw [measure_mono_null this (Set.Finite.measure_zero (by simp) _)]; simp

lemma AssMarg.null_compl_Icc (h : AssMarg L a b F) : F (Icc a b)ᶜ = 0 :=
  measure_mono_null (compl_subset_compl.2 Ioo_subset_Icc_self) h.null_compl_Ioo

lemma AssMarg.cdf_mem_Ioo (h : AssMarg L a b F) {t : ℝ} (ht : t ∈ Ioo a b) : cdf F t ∈ Ioo (0 : ℝ) 1 := by
  have hL : (0 : ℝ) < L := h.1
  constructor
  · have := h.le_cdf_sub le_rfl ht.1.le ht.2.le
    rw [h.cdf_left] at this
    have : 0 < (L : ℝ)⁻¹ * (t - a) := mul_pos (inv_pos.2 hL) (by linarith [ht.1])
    linarith
  · have := h.le_cdf_sub ht.1.le ht.2.le le_rfl
    rw [h.cdf_right] at this
    have : 0 < (L : ℝ)⁻¹ * (b - t) := mul_pos (inv_pos.2 hL) (by linarith [ht.2])
    linarith

/-- The extension `w ↦ F⁻¹(clamp₀₁ w)` (`F⁻¹` extended `L`-Lipschitz from `(0,1)`). -/
lemma AssMarg.exists_ext (h : AssMarg L a b F) :
    ∃ g : ℝ → ℝ, LipschitzWith L g ∧ (∀ w ∈ Ioo (0 : ℝ) 1, g w = F.quantile w) ∧ ∀ w, g w = g (clamp01 w) := by
  obtain ⟨g, hg, heq⟩ := h.quantile_lipschitzOn.extend_real
  refine ⟨g ∘ clamp01, ?_, fun w hw => ?_, fun w => by simp [clamp01_idem]⟩
  · refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [Real.dist_eq, Real.dist_eq]
    calc |g (clamp01 u) - g (clamp01 v)| ≤ L * |clamp01 u - clamp01 v| := by
          have := hg.dist_le_mul (clamp01 u) (clamp01 v); rwa [Real.dist_eq, Real.dist_eq] at this
      _ ≤ L * |u - v| := mul_le_mul_of_nonneg_left (abs_clamp01_sub u v) L.2
  · simp [clamp01_of_mem (Ioo_subset_Icc_self hw), heq hw]

/-- `sup_w |Q̃_n(w) − g(w)| ≤ L(ε + 2/n)`. -/
lemma sup_interpQuant_sub (h : AssMarg L a b F) {g : ℝ → ℝ} (hgL : LipschitzWith L g)
    (hgq : ∀ w ∈ Ioo (0 : ℝ) 1, g w = F.quantile w) (hgc : ∀ w, g w = g (clamp01 w)) {n : ℕ} (hn : 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Icc a b) {ε : ℝ} (hε : ∀ t, |empCdf x t - cdf F t| ≤ ε) (w : ℝ) :
    |interpQuant x w - g w| ≤ L * (ε + 2 / n) := by
  rw [interpQuant_clamp, hgc]
  have hS : IsClosed {w : ℝ | |interpQuant x w - g w| ≤ L * (ε + 2 / n)} :=
    isClosed_le (((continuous_interpQuant x).sub hgL.continuous).abs) continuous_const
  have hsub : Ioo (0 : ℝ) 1 ⊆ {w : ℝ | |interpQuant x w - g w| ≤ L * (ε + 2 / n)} := by
    intro w hw
    simp only [mem_setOf_eq]
    rw [hgq w hw]
    exact quantiles_quant F L a b n x ε h hn hx hε w hw
  have hcl := hS.closure_subset_iff.2 hsub
  rw [closure_Ioo zero_ne_one] at hcl
  exact hcl ⟨clamp01_nonneg w, clamp01_le_one w⟩

end Inv

lemma lipschitz_coordMap {g : Fin d → ℝ → ℝ} {L : ℝ≥0} (hg : ∀ i, LipschitzWith L (g i)) :
    LipschitzWith L (fun u : Euc d => (WithLp.toLp 2 fun i => g i (u i) : Euc d)) := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  have hb : ∀ i, dist (g i (u i)) (g i (v i)) ^ 2 ≤ (L : ℝ) ^ 2 * dist (u i) (v i) ^ 2 := fun i => by
    rw [← mul_pow]; exact pow_le_pow_left₀ dist_nonneg ((hg i).dist_le_mul _ _) 2
  calc √(∑ i, dist ((WithLp.toLp 2 fun i => g i (u i) : Euc d) i) ((WithLp.toLp 2 fun i => g i (v i) : Euc d) i) ^ 2)
      ≤ √(∑ i, (L : ℝ) ^ 2 * dist (u i) (v i) ^ 2) := Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => by simpa using hb i)
    _ = L * √(∑ i, dist (u i) (v i) ^ 2) := by
        rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (NNReal.coe_nonneg L)]

theorem fieldcop_inv : Claims.fieldcop_inv := by
  intro d ν _ L a b Ω _ P _ Z hM hZ hind hlaw
  have hprob : ∀ i, IsProbabilityMeasure (marg ν i) := fun i => by unfold marg; infer_instance
  choose g hgL hgq hgc using fun i => (hM i).exists_ext
  set S' : Euc d → Euc d := fun u => WithLp.toLp 2 fun i => g i (u i)
  have hS'L : LipschitzWith L S' := lipschitz_coordMap hgL
  -- `S' = copInv ν` on `(0,1)^d`, which carries `γ`
  have hae : S' =ᵐ[ν.map (copStd ν)] copInv ν := by
    have hset : MeasurableSet {u : Euc d | ∀ i, u i ∈ Ioo (0 : ℝ) 1} := by
      simp only [setOf_forall]
      exact MeasurableSet.iInter fun i =>
        (StatFormal.Wave24e.measurable_coord i) measurableSet_Ioo
    have h1 : ∀ᵐ u ∂(ν.map (copStd ν)), ∀ i, u i ∈ Ioo (0 : ℝ) 1 := by
      rw [ae_map_iff (StatFormal.Wave24e.measurable_copStd ν).aemeasurable hset]
      rw [ae_all_iff]
      intro i
      have h2 : ∀ᵐ t ∂(marg ν i), t ∈ Ioo (a i) (b i) := by
        rw [ae_iff]; simpa [compl_def] using (hM i).null_compl_Ioo
      have h3 := ae_of_ae_map (StatFormal.Wave24e.measurable_coord i).aemeasurable h2
      filter_upwards [h3] with x hx
      exact (hM i).cdf_mem_Ioo hx
    filter_upwards [h1] with u hu
    ext i
    simp only [S', copInv]
    exact hgq i (u i) (hu i)
  refine ⟨S', fun n ω u => copInvHat (fun j : Fin n => Z j ω) u - S' u, fun _ _ _ => 0, hS'L, hae,
    fun n ω z => by simp, ?_, ?_, ?_⟩
  · -- `‖h_n‖_∞ = O_P(√(d/n))`
    rw [bigOP_iff_compl (fun n => Real.sqrt_nonneg _)]
    intro η hη
    obtain ⟨M, hM0, hA⟩ := dkw_coords hZ hind hlaw hη
    refine ⟨Real.sqrt d * L * (M + 2), by positivity, 1, fun n hn => ?_⟩
    obtain ⟨A, hAm, hPA, hb⟩ := hA n hn
    -- the sample lies in the supports almost surely
    set E : Set Ω := ⋂ (j : Fin n), ⋂ (i : Fin d), (fun ω => Z j ω i) ⁻¹' Icc (a i) (b i)
    have hEm : MeasurableSet E :=
      MeasurableSet.iInter fun j => MeasurableSet.iInter fun i =>
        ((StatFormal.Wave24e.measurable_coord i).comp (hZ j)) measurableSet_Icc
    have hEc : P Eᶜ = 0 := by
      simp only [E, compl_iInter]
      refine measure_iUnion_null fun j => measure_iUnion_null fun i => ?_
      have hm : Measurable fun ω => Z j ω i := (StatFormal.Wave24e.measurable_coord i).comp (hZ (j : ℕ))
      rw [← preimage_compl, ← Measure.map_apply hm measurableSet_Icc.compl, (coord_iid hZ hind hlaw i).2.2 j]
      exact (hM i).null_compl_Icc
    refine ⟨A ∩ E, hAm.inter hEm, measure_compl_inter_le.trans (by rw [hEc, add_zero]; exact hPA),
      fun ω hω => ?_⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsq : 2 / (n : ℝ) ≤ 2 / Real.sqrt n := by
      rw [div_le_div_iff₀ hnpos (Real.sqrt_pos.2 hnpos)]
      have : Real.sqrt n ≤ n := by
        calc Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := le_mul_of_one_le_left (Real.sqrt_nonneg _)
              (Real.one_le_sqrt.2 (by exact_mod_cast hn))
          _ = n := Real.mul_self_sqrt hnpos.le
      linarith
    have hcoord : ∀ u i, |(copInvHat (fun j : Fin n => Z j ω) u - S' u) i| ≤ L * (M + 2) * (1 / Real.sqrt n) := by
      intro u i
      simp only [PiLp.sub_apply, copInvHat, S']
      refine (sup_interpQuant_sub (hM i) (hgL i) (hgq i) (hgc i) hn (fun j => Z j ω i) (fun j => by have := hω.2; simp only [E, mem_iInter, mem_preimage] at this; exact this j i)
        (hb ω hω.1 i) (u i)).trans ?_
      calc (L : ℝ) * (M * (1 / Real.sqrt n) + 2 / n) ≤ L * (M * (1 / Real.sqrt n) + 2 / Real.sqrt n) := by gcongr
        _ = L * (M + 2) * (1 / Real.sqrt n) := by ring
    refine iSup_le fun u => ?_
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((norm_le_of_coord (hcoord u)).trans (le_of_eq ?_))
    rw [Real.sqrt_div' _ (Nat.cast_nonneg n), show Real.sqrt d * L * (M + 2) * (Real.sqrt d / Real.sqrt n) =
      (Real.sqrt d * Real.sqrt d) * (L * (M + 2) * (1 / Real.sqrt n)) by ring, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  · intro η hη
    refine ⟨0, 0, fun n _ => ⟨univ, MeasurableSet.univ, ?_, fun ω _ => LipschitzWith.const 0⟩⟩
    rw [measure_univ]; exact ENNReal.ofReal_le_one.2 (by linarith)
  · refine bigOP_mono (fun n ω => ?_) bigOP_zero
    simp

/-! ### The rate -/

theorem fieldcop_rate : Claims.fieldcop_rate := by
  intro d R ν L a b Ω _ P _ X Z hR hν hRat hM hcop hX hindX hlawX hZ hindZ hlawZ
  have hνat : ∀ i, NullSingletonClass (marg ν i) := fun i => by
    have hp : IsProbabilityMeasure (marg ν i) := by unfold marg; infer_instance
    refine ⟨fun t => ?_⟩
    rw [← measure_cdf (marg ν i), StieltjesFunction.measure_singleton]
    have hc := (hM i).continuous_cdf.continuousAt (x := t)
    rw [leftLim_eq_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)]
    simp
  have hstd : ∀ μ : Measure (Euc d), IsProbabilityMeasure μ → (∀ i, NullSingletonClass (marg μ i)) →
      Standardises μ (μ.map (copStd μ)) (copStd μ) (copInv μ) := fun μ hμ hat =>
    (StatFormal.Wave24e.field_cop_standardises d μ fun k t => (hat k).measure_singleton t).2
  have hS : ∀ s, Standardises (R s) (ν.map (copStd ν)) (copStd (R s)) (copInv (R s)) := fun s => by
    rw [← hcop s]; exact hstd (R s) (hR s) (hRat s)
  have hSν := hstd ν hν hνat
  have hfwd : ∀ s, BigOP P (fun n => Real.sqrt (d / n)) fun n ω =>
      eLpNorm (fun x => copStdHat (fun j : Fin n => X s j ω) x - copStd (R s) x) 2 (R s) := fun s => by
    have := hR s
    exact fieldcop_fwd d (R s) Ω P (X s) (hRat s) (hX s) (hindX s) (hlawX s)
  have hinv := fieldcop_inv d ν L a b Ω P Z hM hZ hindZ hlawZ
  exact fieldJ_rate d R ν (ν.map (copStd ν)) (fun s => copStd (R s)) (fun s => copInv (R s)) (copStd ν) (copInv ν)
    Ω P (fun n ω s => copStdHat (fun j : Fin n => X s j ω)) (fun n ω => copInvHat (fun j : Fin n => Z j ω))
    (fun n => Real.sqrt (d / n)) L inferInstance (fun n => Real.sqrt_nonneg _) hR hν inferInstance hS hSν
    (fun n ω s => measurable_copStdHat _) (fun n ω => (continuous_copInvHat _).measurable) hfwd hinv

end StatFormal.Wave30h
