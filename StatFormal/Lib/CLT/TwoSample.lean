import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Two-sample central limit theorem (library)

Mathlib provides the one-dimensional i.i.d. central limit theorem
(`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`), Lévy's continuity theorem
(`TendstoInDistribution.of_tendsto_charFun`) and Slutsky's lemma
(`TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`). From them:

* `TendstoInDistribution.comp_tendsto`: convergence in distribution along `m(n) → ∞`.
* `tendstoInDistribution_mul_of_tendsto`: `c_n A_n ⇝ c Z` when `A_n ⇝ Z` and `c_n → c` (deterministic).
* `tendstoInDistribution_add_gaussian`: independent `A_n ⇝ N(0,a)`, `C_n ⇝ N(0,c)` give `A_n + C_n ⇝ N(0,a+c)`.
* `clt_centered`: `n^{-1/2} Σ_{i<n} U_i ⇝ N(0, Var U_0)` for centred i.i.d. square-integrable `U`.
* `clt_two_sample`: for independent i.i.d. families `U`, `W` (centred, square integrable) and `m(n)/n → κ > 0`,
  `n^{-1/2} Σ_{i<n} U_i + √n m^{-1} Σ_{i<m} W_i ⇝ N(0, Var U_0 + Var W_0/κ)`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal Real

namespace StatFormal.Foundations.CLT

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} {P' : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- Convergence in distribution along a sequence of indices tending to infinity. -/
lemma TendstoInDistribution.comp_tendsto {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {X : ℕ → Ω → E} {Z : Ω' → E}
    (h : TendstoInDistribution X atTop Z (fun _ => P) P') {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    TendstoInDistribution (fun n => X (m n)) atTop Z (fun _ => P) P' where
  forall_aemeasurable n := h.forall_aemeasurable (m n)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hm

/-- Slutsky with a deterministic factor: `c_n A_n ⇝ c Z` if `A_n ⇝ Z` and `c_n → c`. -/
lemma tendstoInDistribution_mul_of_tendsto {A : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hA : TendstoInDistribution A atTop Z (fun _ => P) P') {c : ℕ → ℝ} {c0 : ℝ} (hc : Tendsto c atTop (𝓝 c0)) :
    TendstoInDistribution (fun n ω => c n * A n ω) atTop (fun ω => c0 * Z ω) (fun _ => P) P' := by
  have hY : TendstoInMeasure P (fun n (_ : Ω) => c n) atTop (fun _ => c0) :=
    tendstoInMeasure_of_tendsto_ae (fun n => aestronglyMeasurable_const) (ae_of_all _ fun _ => hc)
  have := hA.continuous_comp_prodMk_of_tendstoInMeasure_const (g := fun p : ℝ × ℝ => p.2 * p.1)
    (by fun_prop) hY (fun n => aemeasurable_const)
  exact this

/-- The characteristic function of `N(0, v)`. -/
lemma charFun_gaussianReal_zero (v : ℝ≥0) (t : ℝ) :
    charFun (gaussianReal 0 v) t = cexp (-((v : ℂ) * (t : ℂ) ^ 2 / 2)) := by
  rw [charFun_gaussianReal]
  congr 1
  push_cast
  ring

/-- Independent summands with Gaussian limits: `A_n + C_n ⇝ N(0, a + c)`. -/
lemma tendstoInDistribution_add_gaussian {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {A C : ℕ → Ω → ℝ} {ZA : Ω₁ → ℝ} {ZC : Ω₂ → ℝ} {G : Ω' → ℝ} {a c : ℝ≥0}
    (hA : TendstoInDistribution A atTop ZA (fun _ => P) P₁) (hC : TendstoInDistribution C atTop ZC (fun _ => P) P₂)
    (hZA : HasLaw ZA (gaussianReal 0 a) P₁) (hZC : HasLaw ZC (gaussianReal 0 c) P₂)
    (hG : HasLaw G (gaussianReal 0 (a + c)) P') (hind : ∀ n, IndepFun (A n) (C n) P) :
    TendstoInDistribution (fun n ω => A n ω + C n ω) atTop G (fun _ => P) P' := by
  refine TendstoInDistribution.of_tendsto_charFun
    (fun n => (hA.forall_aemeasurable n).add (hC.forall_aemeasurable n)) hG.aemeasurable fun t => ?_
  have e : ∀ n, charFun (P.map (fun ω => A n ω + C n ω)) t =
      charFun (P.map (A n)) t * charFun (P.map (C n)) t := fun n => by
    rw [(hind n).charFun_map_fun_add_eq_mul (hA.forall_aemeasurable n) (hC.forall_aemeasurable n)]
    rfl
  simp_rw [e]
  have h1 := hA.tendsto_charFun t
  have h2 := hC.tendsto_charFun t
  rw [hZA.map_eq] at h1
  rw [hZC.map_eq] at h2
  rw [hG.map_eq]
  convert h1.mul h2 using 2
  rw [charFun_gaussianReal_zero, charFun_gaussianReal_zero, charFun_gaussianReal_zero, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The centred i.i.d. central limit theorem: `n^{-1/2} Σ_{i<n} U_i ⇝ N(0, Var U_0)`. -/
lemma clt_centered {U : ℕ → Ω → ℝ} (hU2 : MemLp (U 0) 2 P) (hUi : iIndepFun U P)
    (hUid : ∀ i, IdentDistrib (U i) (U 0) P P) (hU0 : P[U 0] = 0) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 Var[U 0; P].toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, U i ω) atTop Z
      (fun _ => P) P' := by
  have := tendstoInDistribution_inv_sqrt_mul_sum_sub hZ hU2 hUi hUid
  simpa [hU0] using this

/-- `√n/√m(n) → κ^{-1/2}` when `m(n)/n → κ > 0`. -/
lemma tendsto_sqrt_ratio {m : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ) (hm : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ)) :
    Tendsto (fun n : ℕ => √(n : ℝ) / √(m n : ℝ)) atTop (𝓝 (√κ)⁻¹) := by
  have h1 : Tendsto (fun n : ℕ => (√((m n : ℝ) / n))⁻¹) atTop (𝓝 (√κ)⁻¹) :=
    ((Real.continuous_sqrt.tendsto κ).comp hm).inv₀ (Real.sqrt_pos.2 hκ).ne'
  refine h1.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_apply]
  rw [Real.sqrt_div' _ hn'.le, inv_div]

/-- `m(n) → ∞` when `m(n)/n → κ > 0`. -/
lemma tendsto_atTop_of_ratio {m : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ) (hm : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ)) :
    Tendsto m atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => (m n : ℝ) / n * n) atTop atTop :=
    Tendsto.pos_mul_atTop hκ hm tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => (m n : ℝ)) atTop atTop :=
    h1.congr' (eventually_atTop.2 ⟨1, fun n hn => by
      have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      field_simp⟩)
  exact tendsto_natCast_atTop_iff.1 h2

/-- The two-sample central limit theorem: for independent i.i.d. families `U` (pool) and `W` (validation),
centred and square integrable, and `m(n)/n → κ > 0`,
`n^{-1/2} Σ_{i<n} U_i + √n m(n)^{-1} Σ_{i<m(n)} W_i ⇝ N(0, Var U_0 + Var W_0/κ)`. -/
theorem clt_two_sample {U W : ℕ → Ω → ℝ} {m : ℕ → ℕ} {κ : ℝ} {G : Ω' → ℝ}
    (hUm : ∀ i, Measurable (U i)) (hWm : ∀ i, Measurable (W i)) (hUi : iIndepFun U P) (hWi : iIndepFun W P)
    (hUW : IndepFun (fun ω i => U i ω) (fun ω i => W i ω) P)
    (hUid : ∀ i, IdentDistrib (U i) (U 0) P P) (hWid : ∀ i, IdentDistrib (W i) (W 0) P P)
    (hU2 : MemLp (U 0) 2 P) (hW2 : MemLp (W 0) 2 P) (hU0 : P[U 0] = 0) (hW0 : P[W 0] = 0)
    (hκ : 0 < κ) (hm : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ))
    (hG : HasLaw G (gaussianReal 0 (Var[U 0; P] + Var[W 0; P] / κ).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, U i ω +
      √(n : ℝ) / m n * ∑ i ∈ Finset.range (m n), W i ω) atTop G (fun _ => P) P' := by
  set vU : ℝ≥0 := Var[U 0; P].toNNReal with hvU
  set vW : ℝ≥0 := Var[W 0; P].toNNReal with hvW
  have hvU0 : 0 ≤ Var[U 0; P] := variance_nonneg _ _
  have hvW0 : 0 ≤ Var[W 0; P] := variance_nonneg _ _
  have hmtop : Tendsto m atTop atTop := tendsto_atTop_of_ratio hκ hm
  -- the pool part
  have hA := clt_centered (P' := gaussianReal 0 vU) (Z := id) hU2 hUi hUid hU0
    ⟨aemeasurable_id, Measure.map_id⟩
  -- the validation part
  have hB := clt_centered (P' := gaussianReal 0 vW) (Z := id) hW2 hWi hWid hW0
    ⟨aemeasurable_id, Measure.map_id⟩
  have hB' := TendstoInDistribution.comp_tendsto hB hmtop
  have hC := tendstoInDistribution_mul_of_tendsto hB' (tendsto_sqrt_ratio hκ hm)
  have hCe : ∀ n : ℕ, (fun ω => √(n : ℝ) / √(m n : ℝ) * ((√(m n : ℝ))⁻¹ * ∑ i ∈ Finset.range (m n), W i ω)) =
      fun ω => √(n : ℝ) / m n * ∑ i ∈ Finset.range (m n), W i ω := by
    intro n
    funext ω
    rcases Nat.eq_zero_or_pos (m n) with h0 | hpos
    · simp [h0]
    · have hs : (0 : ℝ) < √(m n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hpos)
      have hsq : √(m n : ℝ) * √(m n : ℝ) = m n := Real.mul_self_sqrt (by positivity)
      calc √(n : ℝ) / √(m n : ℝ) * ((√(m n : ℝ))⁻¹ * ∑ i ∈ Finset.range (m n), W i ω)
          = √(n : ℝ) / (√(m n : ℝ) * √(m n : ℝ)) * ∑ i ∈ Finset.range (m n), W i ω := by
            field_simp
        _ = √(n : ℝ) / m n * ∑ i ∈ Finset.range (m n), W i ω := by rw [hsq]
  have hC' : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) / m n * ∑ i ∈ Finset.range (m n), W i ω) atTop
      (fun x => (√κ)⁻¹ * id x) (fun _ => P) (gaussianReal 0 vW) := by
    have e : (fun (n : ℕ) ω => √(n : ℝ) / m n * ∑ i ∈ Finset.range (m n), W i ω) =
        fun (n : ℕ) ω => √(n : ℝ) / √(m n : ℝ) * ((√(m n : ℝ))⁻¹ * ∑ i ∈ Finset.range (m n), W i ω) :=
      funext fun n => (hCe n).symm
    rw [e]
    exact hC
  let c2 : ℝ≥0 := ⟨((√κ)⁻¹) ^ 2, sq_nonneg _⟩
  have hZC : HasLaw (fun x => (√κ)⁻¹ * id x)
      (gaussianReal 0 (c2 * vW)) (gaussianReal 0 vW) := by
    have := gaussianReal_const_mul (P := gaussianReal 0 vW) (X := id) ⟨aemeasurable_id, Measure.map_id⟩ (√κ)⁻¹
    rw [mul_zero] at this
    exact this
  have hvar : vU + c2 * vW = (Var[U 0; P] + Var[W 0; P] / κ).toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by positivity)]
    rw [NNReal.coe_add, NNReal.coe_mul, show (c2 : ℝ) = ((√κ)⁻¹) ^ 2 from rfl, hvU, hvW, Real.coe_toNNReal _ hvU0,
      Real.coe_toNNReal _ hvW0, inv_pow, Real.sq_sqrt hκ.le]
    ring
  rw [← hvar] at hG
  refine tendstoInDistribution_add_gaussian hA hC' ⟨aemeasurable_id, Measure.map_id⟩ hZC hG fun n => ?_
  have hf : Measurable fun x : ℕ → ℝ => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, x i :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_mul _
  have hg : Measurable fun x : ℕ → ℝ => √(n : ℝ) / m n * ∑ i ∈ Finset.range (m n), x i :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_mul _
  exact hUW.comp hf hg

end StatFormal.Foundations.CLT
