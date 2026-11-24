import StatFormal.Archive.Wave18b.Statements
import StatFormal.Archive.Wave9b.RoutePareto

/-!
# Route: SB `prop:randpenalty` (untrusted)

* Decomposition: `∫ f d(ρ ⊗ K) = ∫∫ f dK dρ` (`Measure.integral_compProd`); for `ρ`-a.e. `p`, `K p.1` has a
  finite second moment, so `∫(u − y)² dK = ∫(u − m)² dK + (m − y)²` (the cross term `∫(u − m) dK = 0`).
  Both summands are measurable (kernel integrals) and dominated by the integrable inner integral.
* Bridge variance: `(μ.map A) ∗ N(0,s) = (μ ⊗ N(0,s)).map (A x + z)`, `A x = (1−t)u + tx`; expand
  `(t(x − m) + z)²` with `∫ z dN = 0`, `∫ z² dN = s` and `∫∫ f(x)g(z) = ∫f ∫g`.
* Positivity: `varK (K w) = t² varK(π w) + εt(1−t) ≥ εt(1−t)`; at `t = 1`, `varK(π w) > 0` unless `π w` is a
  Dirac mass (`x = m` a.e. forces `π w = δ_m`, certified `Wave9b.eq_dirac_of_compl`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace StatFormal.Wave18b

lemma varK_nonneg (μ : Measure ℝ) : 0 ≤ varK μ := integral_nonneg fun _ => sq_nonneg _

/-- Finite second moment ⇒ `∫(u − y)² = varK + (meanK − y)²`. -/
lemma sq_dev_split (μ : Measure ℝ) [IsProbabilityMeasure μ] (h2 : Integrable (fun x => x ^ 2) μ) (y : ℝ) :
    ∫ u, (u - y) ^ 2 ∂μ = varK μ + (meanK μ - y) ^ 2 := by
  have hm2 : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq measurable_id'.aestronglyMeasurable).2 h2
  have h1 : Integrable (fun x : ℝ => x) μ := hm2.integrable one_le_two
  set m := meanK μ with hm
  have hA : Integrable (fun u : ℝ => (u - m) ^ 2) μ := (hm2.sub (memLp_const m)).integrable_sq
  have hB : Integrable (fun u : ℝ => 2 * (m - y) * (u - m)) μ := (h1.sub (integrable_const m)).const_mul _
  have hexp : ∀ u : ℝ, (u - y) ^ 2 = (u - m) ^ 2 + 2 * (m - y) * (u - m) + (m - y) ^ 2 := fun u => by ring
  rw [show (fun u : ℝ => (u - y) ^ 2) = fun u => (u - m) ^ 2 + 2 * (m - y) * (u - m) + (m - y) ^ 2 from
    funext hexp]
  have hAB : Integrable (fun u : ℝ => (u - m) ^ 2 + 2 * (m - y) * (u - m)) μ := hA.add hB
  have hC : Integrable (fun u : ℝ => u - m) μ := h1.sub (integrable_const m)
  rw [integral_add hAB (integrable_const _), integral_add hA hB, integral_const_mul,
    integral_sub h1 (integrable_const _), integral_const, integral_const, probReal_univ, one_smul, one_smul]
  have hmu : ∫ x, x ∂μ = m := rfl
  rw [hmu]
  change _ = ∫ u, (u - m) ^ 2 ∂μ + (m - y) ^ 2
  ring

lemma varK_le_moment (μ : Measure ℝ) [IsProbabilityMeasure μ] (h2 : Integrable (fun x => x ^ 2) μ) :
    varK μ ≤ ∫ u, u ^ 2 ∂μ := by
  have := sq_dev_split μ h2 0
  simp only [sub_zero] at this
  rw [this]; nlinarith [sq_nonneg (meanK μ)]

section Decomp

variable {α : Type*} [MeasurableSpace α] (ρ : Measure (α × ℝ)) [IsProbabilityMeasure ρ] (K : Kernel α ℝ)
  [IsMarkovKernel K]

lemma meas_meanK : StronglyMeasurable fun p : α × ℝ => meanK (K p.1) := by
  let K' : Kernel (α × ℝ) ℝ := K.comap Prod.fst measurable_fst
  have hf : StronglyMeasurable fun q : (α × ℝ) × ℝ => q.2 := measurable_snd.stronglyMeasurable
  have := StronglyMeasurable.integral_kernel_prod_right' (κ := K') hf
  simpa [meanK, K', Kernel.comap_apply] using this

lemma meas_varK : StronglyMeasurable fun p : α × ℝ => varK (K p.1) := by
  have hm := (meas_meanK K).measurable
  let K' : Kernel (α × ℝ) ℝ := K.comap Prod.fst measurable_fst
  have hf : StronglyMeasurable fun q : (α × ℝ) × ℝ => (q.2 - meanK (K q.1.1)) ^ 2 :=
    ((measurable_snd.sub (hm.comp measurable_fst)).pow_const 2).stronglyMeasurable
  have := StronglyMeasurable.integral_kernel_prod_right' (κ := K') hf
  simpa [varK, K', Kernel.comap_apply] using this

lemma ae_moment (h : Integrable (fun z : (α × ℝ) × ℝ => z.2 ^ 2) (ρ ⊗ₘ K.comap Prod.fst measurable_fst)) :
    ∀ᵐ p ∂ρ, Integrable (fun u => u ^ 2) (K p.1) := by
  have := ((Measure.integrable_compProd_iff h.1).1 h).1
  simpa [Kernel.comap_apply] using this

lemma integrable_moment (h : Integrable (fun z : (α × ℝ) × ℝ => z.2 ^ 2) (ρ ⊗ₘ K.comap Prod.fst measurable_fst)) :
    Integrable (fun p : α × ℝ => ∫ u, u ^ 2 ∂(K p.1)) ρ := by
  have := ((Measure.integrable_compProd_iff h.1).1 h).2
  simpa [Kernel.comap_apply, norm_pow, Real.norm_eq_abs, sq_abs] using this

lemma integrable_varK (h : Integrable (fun z : (α × ℝ) × ℝ => z.2 ^ 2) (ρ ⊗ₘ K.comap Prod.fst measurable_fst)) :
    Integrable (fun p : α × ℝ => varK (K p.1)) ρ := by
  refine (integrable_moment ρ K h).mono' (meas_varK K).aestronglyMeasurable ?_
  filter_upwards [ae_moment ρ K h] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (varK_nonneg _)]
  exact varK_le_moment _ hp

end Decomp

theorem randpenalty_decomp : Claims.randpenalty_decomp := by
  intro α _ ρ _ K _ hY hU
  set J := ρ ⊗ₘ K.comap Prod.fst measurable_fst
  have hfst : J.map Prod.fst = ρ := Measure.fst_compProd _ _
  have hY' : Integrable (fun z : (α × ℝ) × ℝ => z.1.2 ^ 2) J := by
    have : Integrable (fun p : α × ℝ => p.2 ^ 2) (J.map Prod.fst) := by rw [hfst]; exact hY
    exact (integrable_map_measure this.1 measurable_fst.aemeasurable).1 this
  have hf : Integrable (fun z : (α × ℝ) × ℝ => (z.2 - z.1.2) ^ 2) J := by
    refine ((hU.const_mul 2).add (hY'.const_mul 2)).mono' (by fun_prop) (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (z.2 - z.1.2))]
    nlinarith [sq_nonneg (z.2 + z.1.2)]
  have hinner : Integrable (fun p : α × ℝ => ∫ u, (u - p.2) ^ 2 ∂(K p.1)) ρ := by
    have := ((Measure.integrable_compProd_iff hf.1).1 hf).2
    simpa [Kernel.comap_apply, norm_pow, Real.norm_eq_abs, sq_abs] using this
  have hae : ∀ᵐ p ∂ρ, ∫ u, (u - p.2) ^ 2 ∂(K p.1) = (meanK (K p.1) - p.2) ^ 2 + varK (K p.1) := by
    filter_upwards [ae_moment ρ K hU] with p hp
    rw [sq_dev_split _ hp, add_comm]
  have hA : Integrable (fun p : α × ℝ => (meanK (K p.1) - p.2) ^ 2) ρ := by
    refine hinner.mono' (((meas_meanK K).measurable.sub measurable_snd).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hp]
    linarith [varK_nonneg (K p.1)]
  have hB := integrable_varK ρ K hU
  refine ⟨?_, integral_nonneg fun p => varK_nonneg _⟩
  rw [Measure.integral_compProd hf, ← integral_add hA hB]
  refine integral_congr_ae ?_
  filter_upwards [hae] with p hp
  simpa [Kernel.comap_apply] using hp

/-! ### The bridge kernel -/

lemma bridgeLaw_eq (ε t u : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    bridgeLaw ε t u μ = (μ.prod (gaussianReal 0 (ε * t * (1 - t)).toNNReal)).map
      (fun p => (1 - t) * u + t * p.1 + p.2) := by
  unfold bridgeLaw Measure.conv
  have hA : Measurable fun x : ℝ => (1 - t) * u + t * x := by fun_prop
  rw [← Measure.map_id (μ := gaussianReal 0 (ε * t * (1 - t)).toNNReal),
    Measure.map_prod_map _ _ hA measurable_id, Measure.map_map (by fun_prop) (hA.prodMap measurable_id),
    Measure.map_id]
  rfl

theorem randpenalty_bridge_var : Claims.randpenalty_bridge_var := by
  intro ε t u μ _ hε ht h2
  set s : ℝ≥0 := (ε * t * (1 - t)).toNNReal with hs
  have hsv : (s : ℝ) = ε * t * (1 - t) := Real.coe_toNNReal _ (mul_nonneg (mul_nonneg hε ht.1) (by linarith [ht.2]))
  set N := gaussianReal 0 s
  have hm2 : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq measurable_id'.aestronglyMeasurable).2 h2
  have h1 : Integrable (fun x : ℝ => x) μ := hm2.integrable one_le_two
  have hN1 : Integrable (fun z : ℝ => z) N := (memLp_id_gaussianReal 1).integrable le_rfl
  have hN2 : Integrable (fun z : ℝ => z ^ 2) N := (memLp_id_gaussianReal 2).integrable_sq
  have hNmean : ∫ z, z ∂N = 0 := integral_id_gaussianReal
  have hNvar : ∫ z, z ^ 2 ∂N = s := by
    have h := variance_fun_id_gaussianReal (μ := 0) (v := s)
    rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id'.aemeasurable, integral_id_gaussianReal] at h
    simpa using h
  have hmeas : Measurable fun p : ℝ × ℝ => (1 - t) * u + t * p.1 + p.2 := by fun_prop
  have hmean : meanK (bridgeLaw ε t u μ) = (1 - t) * u + t * meanK μ := by
    rw [meanK, bridgeLaw_eq, integral_map hmeas.aemeasurable (by fun_prop)]
    have i1 : Integrable (fun p : ℝ × ℝ => (1 - t) * u + t * p.1) (μ.prod N) :=
      (integrable_const _).add ((h1.const_mul t).comp_fst N)
    have i2 : Integrable (fun p : ℝ × ℝ => p.2) (μ.prod N) := hN1.comp_snd μ
    rw [integral_add i1 i2, integral_add (integrable_const _) ((h1.const_mul t).comp_fst N),
      integral_fun_snd (fun z => z), integral_fun_fst (fun x => t * x), integral_const_mul, hNmean,
      integral_const]
    simp only [meanK, smul_eq_mul, probReal_univ, one_mul, mul_one, add_zero]
    rw [integral_const_mul]
  refine ⟨hmean, ?_⟩
  rw [varK, hmean, bridgeLaw_eq, integral_map hmeas.aemeasurable (by fun_prop)]
  set m := meanK μ
  have hexp : ∀ p : ℝ × ℝ, ((1 - t) * u + t * p.1 + p.2 - ((1 - t) * u + t * m)) ^ 2 =
      t ^ 2 * (p.1 - m) ^ 2 + 2 * t * ((p.1 - m) * p.2) + p.2 ^ 2 := fun p => by ring
  simp_rw [hexp]
  have iA : Integrable (fun x : ℝ => (x - m) ^ 2) μ := (hm2.sub (memLp_const m)).integrable_sq
  have iB : Integrable (fun x : ℝ => x - m) μ := h1.sub (integrable_const m)
  have j1 : Integrable (fun p : ℝ × ℝ => t ^ 2 * (p.1 - m) ^ 2) (μ.prod N) := (iA.const_mul _).comp_fst N
  have j2 : Integrable (fun p : ℝ × ℝ => 2 * t * ((p.1 - m) * p.2)) (μ.prod N) :=
    (iB.mul_prod hN1).const_mul _
  have j3 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (μ.prod N) := hN2.comp_snd μ
  have j12 : Integrable (fun p : ℝ × ℝ => t ^ 2 * (p.1 - m) ^ 2 + 2 * t * ((p.1 - m) * p.2)) (μ.prod N) :=
    j1.add j2
  rw [integral_add j12 j3, integral_add j1 j2, integral_fun_fst (fun x => t ^ 2 * (x - m) ^ 2),
    integral_const_mul, integral_const_mul, integral_prod_mul (fun x => x - m) (fun z => z), hNmean,
    integral_fun_snd (fun z => z ^ 2), hNvar, hsv]
  simp [varK, m]

lemma varK_pos_of_ne_dirac (μ : Measure ℝ) [IsProbabilityMeasure μ] (h2 : Integrable (fun x => x ^ 2) μ)
    (hnd : ∀ y, μ ≠ Measure.dirac y) : 0 < varK μ := by
  rcases (varK_nonneg μ).lt_or_eq with h | h
  · exact h
  exfalso
  have hm2 : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq measurable_id'.aestronglyMeasurable).2 h2
  have iA : Integrable (fun x : ℝ => (x - meanK μ) ^ 2) μ := (hm2.sub (memLp_const _)).integrable_sq
  have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) iA).1 h.symm
  apply hnd (meanK μ)
  apply StatFormal.Wave9b.eq_dirac_of_compl
  have : ∀ᵐ x ∂μ, x = meanK μ := by
    filter_upwards [hz] with x hx
    have hx' : (x - meanK μ) ^ 2 = 0 := hx
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hx'
    linarith
  have h0 := ae_iff.1 this
  have hset : {a : ℝ | ¬a = meanK μ} = {meanK μ}ᶜ := by ext; simp
  rw [hset] at h0
  exact h0

theorem randpenalty_pos : Claims.randpenalty_pos := by
  intro G _ ρ _ K _ π ε t hε ht hπ h2 hK hU
  have hvar : ∀ w, varK (K w) = t ^ 2 * varK (π w) + ε * t * (1 - t) := fun w => by
    have := hπ w
    rw [hK w]
    exact (randpenalty_bridge_var ε t w.1 (π w) hε.le ⟨ht.1.le, ht.2.le⟩ (h2 w)).2
  have hpos : 0 < ε * t * (1 - t) := mul_pos (mul_pos hε ht.1) (by linarith [ht.2])
  have hint := integrable_varK ρ K hU
  have hle : ε * t * (1 - t) ≤ ∫ p, varK (K p.1) ∂ρ := by
    calc ε * t * (1 - t) = ∫ _p, ε * t * (1 - t) ∂ρ := by simp
      _ ≤ ∫ p, varK (K p.1) ∂ρ := integral_mono (integrable_const _) hint fun p => by
          rw [hvar]; nlinarith [varK_nonneg (π p.1), sq_nonneg t]
  exact ⟨hle, hpos.trans_le hle⟩

theorem randpenalty_pos_one : Claims.randpenalty_pos_one := by
  intro G _ ρ _ K _ π ε hε hπ h2 hnd hK hU
  have hvar : ∀ w, varK (K w) = varK (π w) := fun w => by
    have := hπ w
    rw [hK w, (randpenalty_bridge_var ε 1 w.1 (π w) hε ⟨zero_le_one, le_rfl⟩ (h2 w)).2]
    ring
  have hint := integrable_varK ρ K hU
  have hposw : ∀ w, 0 < varK (K w) := fun w => by
    have := hπ w; rw [hvar]; exact varK_pos_of_ne_dirac _ (h2 w) (hnd w)
  rw [integral_pos_iff_support_of_nonneg (f := fun p : (ℝ × G) × ℝ => varK (K p.1)) (fun p => (hposw p.1).le) hint]
  have : Function.support (fun p : (ℝ × G) × ℝ => varK (K p.1)) = univ := by
    ext p; simp [(hposw p.1).ne']
  rw [this, measure_univ]; exact zero_lt_one

theorem randpenalty_zero : Claims.randpenalty_zero := by
  intro ε u μ _
  have h : bridgeLaw ε 0 u μ = Measure.dirac u := by
    rw [bridgeLaw_eq, show (ε * 0 * (1 - 0)).toNNReal = 0 by simp, gaussianReal_zero_var, Measure.prod_dirac,
      Measure.map_map (by fun_prop) (by fun_prop)]
    have : ((fun p : ℝ × ℝ => (1 - 0) * u + 0 * p.1 + p.2) ∘ fun x => (x, (0 : ℝ))) = fun _ => u := by
      funext x; simp
    rw [this, Measure.map_const, measure_univ, one_smul]
  refine ⟨h, ?_⟩
  rw [h, varK, meanK]
  simp

end StatFormal.Wave18b
