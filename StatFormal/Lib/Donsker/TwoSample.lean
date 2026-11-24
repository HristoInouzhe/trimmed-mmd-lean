import StatFormal.Lib.Donsker.EmpProc
import StatFormal.Lib.Donsker.Fidi
import StatFormal.Lib.Donsker.TwoSampleCLT

/-!
# A two-sample Donsker theorem for Lipschitz-parametrised bounded classes on a compact index (untrusted library)

`X` a compact metric space with exponential nets, `F, G : X → 𝒳 → ℝ` measurable, bounded by `B` and `L`-Lipschitz
in the index; i.i.d. samples `ξ ∼ P`, `η ∼ Q`, independent; sizes `n_k, m_k → ∞`, rates `r_k > 0` with
`r_k/√n_k → c_P`, `r_k/√m_k → c_Q`. Then the continuous process
`V_k(z) = r_k (P_{n_k} − P) F_z + r_k (Q_{m_k} − Q) G_z` converges in distribution in `C(X, ℝ)` to a law `ν` whose
finite linear combinations of evaluations are `N(0, c_P² Var_P[Σ u_i F_{z_i}] + c_Q² Var_Q[Σ u_i G_{z_i}])`.

Route: tightness (`isTightMeasureSet_of_subgaussian`, with the Hoeffding tails `tsProc_tail_inc`, `tsProc_tail_pt`
and `r_k²/n_k, r_k²/m_k ≤ R²`), the finite-dimensional CLT (`tendstoInDistribution_twoSample_clt` applied to the
functions `Σ u_i F_{z_i}`, `Σ u_i G_{z_i}`), and Prokhorov plus identification (`tendstoInDistribution_of_tight`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set

namespace StatFormal.Foundations.Donsker

variable {X 𝒳 Ω : Type*} [MeasurableSpace 𝒳] [MeasurableSpace Ω]

lemma measurable_tsProc [PseudoMetricSpace X] {F G : X → 𝒳 → ℝ} (hFm : ∀ z, Measurable (F z))
    (hGm : ∀ z, Measurable (G z)) (P Q : Measure 𝒳) (n m : ℕ) (r : ℝ) (ξ η : ℕ → Ω → 𝒳)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ j, Measurable (η j)) (z : X) :
    Measurable fun ω => tsProc F G P Q n m r (fun i => ξ i ω) (fun j => η j ω) z := by
  unfold tsProc
  refine (measurable_const.mul (((Finset.measurable_sum _ fun i _ => (hFm z).comp (hξ i)).div_const _).sub_const _)).add
    (measurable_const.mul (((Finset.measurable_sum _ fun j _ => (hGm z).comp (hη j)).div_const _).sub_const _))

/-- A finite linear combination of the process is the process of the combined functions. -/
lemma linEval_tsProc [PseudoMetricSpace X] {F G : X → 𝒳 → ℝ} {P Q : Measure 𝒳} [IsFiniteMeasure P]
    [IsFiniteMeasure Q] {B : ℝ} (hFm : ∀ z, Measurable (F z)) (hGm : ∀ z, Measurable (G z))
    (hFb : ∀ z w, |F z w| ≤ B) (hGb : ∀ z w, |G z w| ≤ B) (n m : ℕ) (r : ℝ) (x y : ℕ → 𝒳)
    (v : C(X, ℝ)) (hv : ∀ z, v z = tsProc F G P Q n m r x y z) {p : ℕ} (z : Fin p → X) (u : Fin p → ℝ) :
    linEval z u v = r * ((∑ i ∈ Finset.range n, (fun w => ∑ l, u l * F (z l) w) (x i)) / n -
        ∫ w, (∑ l, u l * F (z l) w) ∂P) +
      r * ((∑ j ∈ Finset.range m, (fun w => ∑ l, u l * G (z l) w) (y j)) / m - ∫ w, (∑ l, u l * G (z l) w) ∂Q) := by
  have hiF : ∀ l, Integrable (fun w => u l * F (z l) w) P := fun l =>
    (integrable_of_abs_le (hFm (z l)) (hFb (z l))).const_mul _
  have hiG : ∀ l, Integrable (fun w => u l * G (z l) w) Q := fun l =>
    (integrable_of_abs_le (hGm (z l)) (hGb (z l))).const_mul _
  simp only [linEval, hv, tsProc]
  rw [integral_finset_sum _ fun l _ => hiF l, integral_finset_sum _ fun l _ => hiG l]
  simp only [integral_const_mul]
  rw [Finset.sum_comm (s := Finset.range n), Finset.sum_comm (s := Finset.range m)]
  simp only [← Finset.mul_sum, Finset.sum_div, Finset.mul_sum, mul_sub, mul_add, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  congr 1 <;> congr 1 <;> refine Finset.sum_congr rfl fun l _ => ?_ <;>
    first | (refine Finset.sum_congr rfl fun i _ => ?_; ring) | ring

/-- The two-sample Donsker theorem. -/
theorem donsker_twoSample [MetricSpace X] [CompactSpace X] (hX : HasExpNets X)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ξ η : ℕ → Ω → 𝒳) (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ j, Measurable (η j))
    (hiξ : iIndepFun ξ μ) (hiη : iIndepFun η μ) (hlξ : ∀ i, μ.map (ξ i) = P) (hlη : ∀ j, μ.map (η j) = Q)
    (hind : IndepFun (fun ω i => ξ i ω) (fun ω j => η j ω) μ)
    {F G : X → 𝒳 → ℝ} {B L : ℝ} (hF : IsLipClass F B L) (hG : IsLipClass G B L) (hB : 0 < B) (hL : 0 < L)
    (n m : ℕ → ℕ) (hn1 : ∀ k, 1 ≤ n k) (hm1 : ∀ k, 1 ≤ m k) (hn : Tendsto n atTop atTop)
    (hm : Tendsto m atTop atTop) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (cP cQ : ℝ)
    (hrn : Tendsto (fun k => r k / √(n k : ℝ)) atTop (𝓝 cP)) (hrm : Tendsto (fun k => r k / √(m k : ℝ)) atTop (𝓝 cQ))
    (V : ℕ → Ω → C(X, ℝ))
    (hV : ∀ k ω z, V k ω z = tsProc F G P Q (n k) (m k) (r k) (fun i => ξ i ω) (fun j => η j ω) z) :
    ∃ ν : ProbabilityMeasure C(X, ℝ), TendstoInDistribution V atTop id (fun _ => μ) (ν : Measure C(X, ℝ)) ∧
      ∀ (p : ℕ) (z : Fin p → X) (u : Fin p → ℝ), (ν : Measure C(X, ℝ)).map (linEval z u) =
        gaussianReal 0 (cP ^ 2 * Var[fun w => ∑ i, u i * F (z i) w; P] +
          cQ ^ 2 * Var[fun w => ∑ i, u i * G (z i) w; Q]).toNNReal := by
  -- measurability
  have hVm : ∀ k, AEMeasurable (V k) μ := by
    intro k
    refine (ContinuousMap.measurable_iff_eval.2 fun z => ?_).aemeasurable
    simp_rw [hV]
    exact measurable_tsProc hF.meas hG.meas P Q _ _ _ ξ η hξ hη z
  -- the rate bound
  obtain ⟨R, hR, hRb⟩ : ∃ R : ℝ, 0 < R ∧ ∀ k, r k ^ 2 / n k ≤ R ^ 2 ∧ r k ^ 2 / m k ≤ R ^ 2 := by
    obtain ⟨R1, hR1⟩ := hrn.bddAbove_range
    obtain ⟨R2, hR2⟩ := hrm.bddAbove_range
    refine ⟨max (max R1 R2) 1, by positivity, fun k => ?_⟩
    have h1 : r k / √(n k : ℝ) ≤ max (max R1 R2) 1 := (hR1 ⟨k, rfl⟩).trans (by simp)
    have h2 : r k / √(m k : ℝ) ≤ max (max R1 R2) 1 := (hR2 ⟨k, rfl⟩).trans (by simp)
    have hn0 : (0 : ℝ) ≤ n k := Nat.cast_nonneg _
    have hm0 : (0 : ℝ) ≤ m k := Nat.cast_nonneg _
    have e1 : r k ^ 2 / n k = (r k / √(n k : ℝ)) ^ 2 := by rw [div_pow, Real.sq_sqrt hn0]
    have e2 : r k ^ 2 / m k = (r k / √(m k : ℝ)) ^ 2 := by rw [div_pow, Real.sq_sqrt hm0]
    have p1 : 0 ≤ r k / √(n k : ℝ) := div_nonneg (hr k).le (Real.sqrt_nonneg _)
    have p2 : 0 ≤ r k / √(m k : ℝ) := div_nonneg (hr k).le (Real.sqrt_nonneg _)
    exact ⟨by rw [e1]; exact pow_le_pow_left₀ p1 h1 2, by rw [e2]; exact pow_le_pow_left₀ p2 h2 2⟩
  -- tightness
  have htight : IsTightMeasureSet (Set.range fun k => μ.map (V k)) := by
    refine isTightMeasureSet_of_subgaussian hX μ V hVm (c := 4) (L := 3 * R * L) (B := 3 * R * B)
      (by norm_num) (by positivity) (by positivity) ?_ ?_
    · intro k x y ρ hρ hd u hu
      simp_rw [hV]
      exact tsProc_tail_inc μ ξ η hξ hη hiξ hiη P Q hlξ hlη hF hG hL (hn1 k) (hm1 k) (hr k) hR (hRb k).1 (hRb k).2
        x y hρ hd hu
    · intro k x u hu
      simp_rw [hV]
      exact tsProc_tail_pt μ ξ η hξ hη hiξ hiη P Q hlξ hlη hF hG hB (hn1 k) (hm1 k) (hr k) hR (hRb k).1 (hRb k).2 x hu
  -- finite-dimensional CLT
  let γ : (p : ℕ) → (Fin p → X) → (Fin p → ℝ) → ProbabilityMeasure ℝ := fun p z u =>
    ⟨gaussianReal 0 (cP ^ 2 * Var[fun w => ∑ i, u i * F (z i) w; P] +
      cQ ^ 2 * Var[fun w => ∑ i, u i * G (z i) w; Q]).toNNReal, inferInstance⟩
  have hfidi : ∀ (p : ℕ) (z : Fin p → X) (u : Fin p → ℝ),
      TendstoInDistribution (fun k ω => linEval z u (V k ω)) atTop id (fun _ => μ) (γ p z u : Measure ℝ) := by
    intro p z u
    have hbF : ∃ C, ∀ w, |∑ i, u i * F (z i) w| ≤ C := ⟨∑ i, |u i| * B, fun w =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hF.bound _ _) (abs_nonneg _))⟩
    have hbG : ∃ C, ∀ w, |∑ i, u i * G (z i) w| ≤ C := ⟨∑ i, |u i| * B, fun w =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hG.bound _ _) (abs_nonneg _))⟩
    have hmF : Measurable fun w => ∑ i, u i * F (z i) w :=
      Finset.measurable_sum _ fun i _ => measurable_const.mul (hF.meas _)
    have hmG : Measurable fun w => ∑ i, u i * G (z i) w :=
      Finset.measurable_sum _ fun i _ => measurable_const.mul (hG.meas _)
    have h := tendstoInDistribution_twoSample_clt μ P Q ξ η hξ hη hiξ hiη hlξ hlη hind _ _ hmF hmG hbF hbG n m hn hm
      r cP cQ hrn hrm
    have heq : (fun k ω => linEval z u (V k ω)) = fun k ω =>
        r k * ((∑ i ∈ Finset.range (n k), (fun w => ∑ l, u l * F (z l) w) (ξ i ω)) / n k -
          ∫ w, (∑ l, u l * F (z l) w) ∂P) +
        r k * ((∑ j ∈ Finset.range (m k), (fun w => ∑ l, u l * G (z l) w) (η j ω)) / m k -
          ∫ w, (∑ l, u l * G (z l) w) ∂Q) := by
      funext k ω
      exact linEval_tsProc hF.meas hG.meas hF.bound hG.bound _ _ _ _ _ (V k ω) (hV k ω) z u
    rw [heq]
    exact h
  obtain ⟨ν, hν, hνf⟩ := tendstoInDistribution_of_tight μ V hVm htight γ hfidi
  exact ⟨ν, hν, fun p z u => hνf p z u⟩

end StatFormal.Foundations.Donsker
