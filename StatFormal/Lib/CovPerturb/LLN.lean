import Mathlib.Probability.StrongLaw
import StatFormal.Lib.CovPerturb.EmpCov

/-!
# Strong law for empirical covariance operators in operator norm (untrusted library)

For an i.i.d. sequence `Z_i ∼ P` in a separable Hilbert space with `E‖X‖² < ∞` and a complete orthonormal family
`(e_a)`, the empirical centred covariance of `Z_0, …, Z_{n−1}` converges to the population one in operator norm,
almost surely (`ae_tendsto_norm_cCov`). The proof avoids Hilbert–Schmidt-valued strong laws: the operator norm is
bounded by `bnd N` (finite block + tails + mean term, `EmpCov.norm_cCov_sub_le`), whose pieces obey the real strong law
and the Banach strong law in `H`; the tails vanish as `N → ∞`. The bound `betaB = inf_N bnd N` is a MEASURABLE function
of the sample dominating the operator-norm error (`norm_le_betaB`, `measurable_betaB`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped RealInnerProductSpace ENNReal

namespace StatFormal.CovPerturb

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The finite-block discrepancy. -/
def blockF (P : Measure H) (e : ℕ → H) (N : ℕ) {n : ℕ} (z : Fin n → H) : ℝ :=
  ∑ a ∈ range N, ∑ b ∈ range N, |(n : ℝ)⁻¹ * ∑ i, ⟪e a, z i⟫ * ⟪e b, z i⟫ - ∫ x, ⟪e a, x⟫ * ⟪e b, x⟫ ∂P|

/-- The operator-norm bound at truncation level `N`. -/
def bnd (P : Measure H) (e : ℕ → H) (N : ℕ) {n : ℕ} (z : Fin n → H) : ℝ :=
  blockF P e N z + 2 * ((n : ℝ)⁻¹ * ∑ i, tailF e N (z i)) + 2 * ∫ x, tailF e N x ∂P
    + ‖(n : ℝ)⁻¹ • ∑ i, z i - ∫ y, y ∂P‖ * (‖(n : ℝ)⁻¹ • ∑ i, z i‖ + ‖∫ y, y ∂P‖)

/-- The measurable dominant `inf_N bnd N`. -/
def betaB (P : Measure H) (e : ℕ → H) {n : ℕ} (z : Fin n → H) : ℝ := ⨅ N, bnd P e N z

variable {P : Measure H} {e : ℕ → H}

lemma bnd_nonneg (N : ℕ) {n : ℕ} (z : Fin n → H) : 0 ≤ bnd P e N z := by
  unfold bnd blockF
  have h1 : 0 ≤ (n : ℝ)⁻¹ * ∑ i, tailF e N (z i) :=
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun i _ => tailF_nonneg N _)
  have h2 : 0 ≤ ∫ x, tailF e N x ∂P := integral_nonneg (tailF_nonneg N)
  positivity

lemma betaB_nonneg {n : ℕ} (z : Fin n → H) : 0 ≤ betaB P e z := le_ciInf fun N => bnd_nonneg N z

lemma betaB_le (N : ℕ) {n : ℕ} (z : Fin n → H) : betaB P e z ≤ bnd P e N z :=
  ciInf_le ⟨0, by rintro _ ⟨M, rfl⟩; exact bnd_nonneg M z⟩ N

lemma continuous_bnd (N n : ℕ) : Continuous (fun z : Fin n → H => bnd P e N z) := by
  have hT := continuous_tailF (e := e) N
  unfold bnd blockF
  fun_prop

lemma measurable_betaB (n : ℕ) : Measurable (fun z : Fin n → H => betaB P e z) :=
  Measurable.iInf fun N => (continuous_bnd N n).measurable

/-- The operator-norm error is dominated by `bnd N` for every `N`. -/
lemma norm_cCov_emp_sub_le_bnd (he : Orthonormal ℝ e) [IsProbabilityMeasure P] (h2 : MemLp id 2 P) (N : ℕ)
    {n : ℕ} (hn : n ≠ 0) (z : Fin n → H) :
    ‖cCov (empMeasure z) - cCov P‖ ≤ bnd P e N z := by
  haveI := empMeasure_isProb z hn
  refine (norm_cCov_sub_le he h2 (memLp_empMeasure z) N).trans (le_of_eq ?_)
  unfold bnd blockF
  simp only [covOp_emp_inner, covOp_inner h2, mean_emp, integral_empMeasure, smul_eq_mul]

lemma norm_le_betaB (he : Orthonormal ℝ e) [IsProbabilityMeasure P] (h2 : MemLp id 2 P) {n : ℕ} (hn : n ≠ 0)
    (z : Fin n → H) : ‖cCov (empMeasure z) - cCov P‖ ≤ betaB P e z :=
  le_ciInf fun N => norm_cCov_emp_sub_le_bnd he h2 N hn z

/-- The population tails vanish. -/
lemma tendsto_tail (he : Orthonormal ℝ e) (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure)
    (h2 : MemLp id 2 P) : Tendsto (fun N => ∫ x, tailF e N x ∂P) atTop (𝓝 0) := by
  have hlim : ∀ x, Tendsto (fun N => tailF e N x) atTop (𝓝 0) := by
    intro x
    have hs := (hasSum_repr_of he hsp x).tendsto_sum_nat
    have h1 : Tendsto (fun N => x - projN e N x) atTop (𝓝 (x - x)) := tendsto_const_nhds.sub hs
    rw [sub_self] at h1
    have h3 := (h1.norm).mul_const ‖x‖
    simpa [tailF, norm_zero, zero_mul] using h3
  have := tendsto_integral_of_dominated_convergence (fun x => ‖x‖ ^ 2)
    (fun N => (continuous_tailF N).aestronglyMeasurable) (integrable_sq_norm h2)
    (fun N => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tailF_nonneg N x)]; exact tailF_le he N x)
    (Eventually.of_forall hlim)
  simpa using this

section Strong

variable {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr] {Z : ℕ → Ω → H}

/-- The real strong law, prefix form over `Fin n`. -/
lemma slln_real (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z Pr) (hlaw : ∀ i, Pr.map (Z i) = P)
    {f : H → ℝ} (hf : Measurable f) (hint : Integrable f P) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f (Z i ω)) atTop (𝓝 (∫ x, f x ∂P)) := by
  have hident : ∀ i, IdentDistrib (Z i) (Z 0) Pr Pr :=
    fun i => ⟨(hZ i).aemeasurable, (hZ 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩
  have hint0 : Integrable (f ∘ Z 0) Pr := by
    rw [← hlaw 0] at hint; exact hint.comp_measurable (hZ 0)
  have hs := strong_law_ae_real (fun i => f ∘ Z i) hint0
    (fun i j hij => (hind.indepFun hij).comp hf hf) (fun i => (hident i).comp hf)
  filter_upwards [hs] with ω hω
  have hmean : ∫ ω, (f ∘ Z 0) ω ∂Pr = ∫ x, f x ∂P := by
    rw [← hlaw 0, integral_map (hZ 0).aemeasurable hf.aestronglyMeasurable]; rfl
  rw [← hmean]
  refine hω.congr fun n => ?_
  rw [Fin.sum_univ_eq_sum_range (fun i => f (Z i ω)) n, div_eq_inv_mul]; rfl

/-- The strong law for the mean in `H`. -/
lemma slln_mean (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z Pr) (hlaw : ∀ i, Pr.map (Z i) = P)
    (hint : Integrable id P) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i : Fin n, Z i ω) atTop (𝓝 (∫ x, x ∂P)) := by
  have hident : ∀ i, IdentDistrib (Z i) (Z 0) Pr Pr :=
    fun i => ⟨(hZ i).aemeasurable, (hZ 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩
  have hint0 : Integrable (Z 0) Pr := by
    rw [← hlaw 0] at hint; exact hint.comp_measurable (hZ 0)
  have hs := strong_law_ae Z hint0 (fun i j hij => hind.indepFun hij) hident
  filter_upwards [hs] with ω hω
  have hmean : ∫ ω, Z 0 ω ∂Pr = ∫ x, x ∂P := by
    have := integral_map (f := id) (hZ 0).aemeasurable (aestronglyMeasurable_id (μ := Pr.map (Z 0)))
    rw [← hlaw 0]; exact this.symm
  rw [← hmean]
  refine hω.congr fun n => ?_
  rw [Fin.sum_univ_eq_sum_range (fun i => Z i ω) n]

/-- **Almost surely `inf_N bnd N → 0`.** -/
theorem ae_tendsto_betaB (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z Pr) (hlaw : ∀ i, Pr.map (Z i) = P)
    (he : Orthonormal ℝ e) (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure)
    (h2 : MemLp id 2 P) [IsProbabilityMeasure P] :
    ∀ᵐ ω ∂Pr, Tendsto (fun n : ℕ => betaB P e (fun i : Fin n => Z i ω)) atTop (𝓝 0) := by
  have hblock : ∀ᵐ ω ∂Pr, ∀ a b, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, ⟪e a, Z i ω⟫ * ⟪e b, Z i ω⟫)
      atTop (𝓝 (∫ x, ⟪e a, x⟫ * ⟪e b, x⟫ ∂P)) :=
    ae_all_iff.2 fun a => ae_all_iff.2 fun b =>
      slln_real hZ hind hlaw (f := fun x => ⟪e a, x⟫ * ⟪e b, x⟫) (by fun_prop) (integrable_inner_mul h2 _ _)
  have htail : ∀ᵐ ω ∂Pr, ∀ N, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, tailF e N (Z i ω))
      atTop (𝓝 (∫ x, tailF e N x ∂P)) :=
    ae_all_iff.2 fun N => slln_real hZ hind hlaw (continuous_tailF N).measurable (integrable_tailF he h2 N)
  have hmean := slln_mean hZ hind hlaw (integrable_id_of_memLp h2)
  filter_upwards [hblock, htail, hmean] with ω h1 h2' h3
  have hN : ∀ N, Tendsto (fun n : ℕ => bnd P e N (fun i : Fin n => Z i ω)) atTop
      (𝓝 (4 * ∫ x, tailF e N x ∂P)) := by
    intro N
    have hb : Tendsto (fun n : ℕ => blockF P e N (fun i : Fin n => Z i ω)) atTop (𝓝 0) := by
      have := tendsto_finset_sum (range N) fun a _ => tendsto_finset_sum (range N) fun b _ =>
        ((h1 a b).sub_const (∫ x, ⟪e a, x⟫ * ⟪e b, x⟫ ∂P)).abs
      simpa [blockF] using this
    have hm := ((h3.sub_const (∫ y, y ∂P)).norm).mul ((h3.norm).add_const ‖∫ y, y ∂P‖)
    have := ((hb.add ((h2' N).const_mul 2)).add_const (2 * ∫ x, tailF e N x ∂P)).add hm
    convert this using 2
    · rfl
    · rw [sub_self, norm_zero, zero_mul, add_zero, zero_add]
      ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN'⟩ := ((tendsto_tail he hsp h2).const_mul 4).eventually (gt_mem_nhds (by linarith : (4 : ℝ) * 0 < ε))
    |>.exists
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 ((hN N).eventually (gt_mem_nhds hN'))
  refine ⟨n₀, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (betaB_nonneg _)]
  exact (betaB_le N _).trans_lt (hn₀ n hn)

/-- **Strong law in operator norm.** -/
theorem ae_tendsto_norm_cCov (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z Pr) (hlaw : ∀ i, Pr.map (Z i) = P)
    (he : Orthonormal ℝ e) (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure)
    (h2 : MemLp id 2 P) [IsProbabilityMeasure P] :
    ∀ᵐ ω ∂Pr, Tendsto (fun n : ℕ => ‖cCov (empMeasure (fun i : Fin n => Z i ω)) - cCov P‖) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_betaB hZ hind hlaw he hsp h2] with ω hω
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hω
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact norm_le_betaB he h2 (by omega) _

end Strong

end StatFormal.CovPerturb
