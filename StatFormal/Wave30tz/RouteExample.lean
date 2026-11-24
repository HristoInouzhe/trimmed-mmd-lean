import StatFormal.Wave30tz.RouteKS
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Route: Proposition 3's example, the finite certificate (untrusted proof material)

Proves the frozen claim `Claims.alpha0_example` of `StatFormal.Wave30tz.Statements` (its last
conjunct through `ramp_ks_route` of `RouteKS`).

* the laws as Dirac sums: `exP_apply`, `exQ_apply` (`P(S)`, `Q(S)` for every set `S`), `integral_exP`,
  `integral_exQ` (`∫ g` for every function `g`); both are probability measures;
* `tv_ex : TV(P, Q) = 3/5`;
* the unnormalized witness `wit x = ∫ k(a,x) dP(a) − ∫ k(b,x) dQ(b)` at the atoms, with
  `η = e^{−50} ≤ 1/1301` (all far pairs) and `E = e^{−1/8} ∈ [7/8, 8/9]`;
* `mmd_sq_eq : MMD² = ∫ wit dP − ∫ wit dQ` (Fubini for one cross term), hence `MMD > 0`;
* `ks_ex : KS⁺(f₀) = 2/5`, attained at `x = f₀(1/2)`;
* `alpha0_example_route : Claims.alpha0_example`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter

namespace StatFormal.Wave30tz

open StatFormal.Wave30tq

/-! ### Dirac pieces -/

open Classical in
/-- `1{a ∈ S}`. -/
def ind (S : Set ℝ) (a : ℝ) : ℝ := if a ∈ S then 1 else 0

theorem ind_of_mem {S : Set ℝ} {a : ℝ} (h : a ∈ S) : ind S a = 1 := by simp [ind, h]

theorem ind_of_notMem {S : Set ℝ} {a : ℝ} (h : a ∉ S) : ind S a = 0 := by simp [ind, h]

theorem ind_nonneg (S : Set ℝ) (a : ℝ) : 0 ≤ ind S a := by
  unfold ind; split_ifs <;> norm_num

theorem ind_le_one (S : Set ℝ) (a : ℝ) : ind S a ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

theorem measure_smul_dirac (S : Set ℝ) {c : ℝ} (_hc : 0 ≤ c) (a : ℝ) :
    (ENNReal.ofReal c • Measure.dirac a) S = ENNReal.ofReal (c * ind S a) := by
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases h : a ∈ S
  · simp [ind, h]
  · simp [ind, h]

theorem integrable_smul_dirac (g : ℝ → ℝ) (c : ℝ) (a : ℝ) :
    Integrable g (ENNReal.ofReal c • Measure.dirac a) :=
  (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

theorem integral_smul_dirac (g : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) (a : ℝ) :
    ∫ x, g x ∂(ENNReal.ofReal c • Measure.dirac a) = c * g a := by
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hc, smul_eq_mul]

/-! ### The weights `i/1050` -/

theorem sum_w : ∑ i ∈ Finset.Icc (1 : ℕ) 20, (i : ℝ) / 1050 = 1 / 5 := by
  rw [← Finset.sum_div]
  have : (∑ i ∈ Finset.Icc (1 : ℕ) 20, (i : ℝ)) = ((∑ i ∈ Finset.Icc (1 : ℕ) 20, i : ℕ) : ℝ) := by
    push_cast; rfl
  rw [this]
  have h2 : (∑ i ∈ Finset.Icc (1 : ℕ) 20, i) = 210 := by decide
  rw [h2]
  norm_num

theorem sum_w_le {b : ℕ → ℝ} {B : ℝ} (h : ∀ i ∈ Finset.Icc (1 : ℕ) 20, b i ≤ B) :
    ∑ i ∈ Finset.Icc (1 : ℕ) 20, (i : ℝ) / 1050 * b i ≤ B / 5 := by
  calc ∑ i ∈ Finset.Icc (1 : ℕ) 20, (i : ℝ) / 1050 * b i
      ≤ ∑ i ∈ Finset.Icc (1 : ℕ) 20, (i : ℝ) / 1050 * B :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (h i hi) (by positivity)
    _ = B / 5 := by rw [← Finset.sum_mul, sum_w]; ring

theorem le_sum_w {b : ℕ → ℝ} {B : ℝ} (h : ∀ i ∈ Finset.Icc (1 : ℕ) 20, B ≤ b i) :
    B / 5 ≤ ∑ i ∈ Finset.Icc (1 : ℕ) 20, (i : ℝ) / 1050 * b i := by
  calc B / 5 = ∑ i ∈ Finset.Icc (1 : ℕ) 20, (i : ℝ) / 1050 * B := by rw [← Finset.sum_mul, sum_w]; ring
    _ ≤ ∑ i ∈ Finset.Icc (1 : ℕ) 20, (i : ℝ) / 1050 * b i :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (h i hi) (by positivity)

theorem mem_Icc_cast {i : ℕ} (hi : i ∈ Finset.Icc (1 : ℕ) 20) : (1 : ℝ) ≤ i ∧ (i : ℝ) ≤ 20 := by
  rw [Finset.mem_Icc] at hi
  exact ⟨by exact_mod_cast hi.1, by exact_mod_cast hi.2⟩

/-! ### The laws as finite sums -/

/-- `P(S)` as a finite sum. -/
def pm (S : Set ℝ) : ℝ :=
  2 / 5 * ind S 0 + ∑ i ∈ Finset.Icc (1 : ℕ) 20, (i : ℝ) / 1050 * ind S (20 + 10 * (i : ℝ)) +
    2 / 5 * ind S (-100)

/-- `Q(S)` as a finite sum. -/
def qm (S : Set ℝ) : ℝ := 3 / 10 * ind S (1 / 2) + 3 / 10 * ind S 300 + 2 / 5 * ind S (-100)

theorem pm_nonneg (S : Set ℝ) : 0 ≤ pm S := by
  have h1 := ind_nonneg S 0
  have h2 := ind_nonneg S (-100)
  have h3 : 0 ≤ ∑ i ∈ Finset.Icc (1 : ℕ) 20, (i : ℝ) / 1050 * ind S (20 + 10 * (i : ℝ)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (ind_nonneg _ _)
  unfold pm; linarith

theorem qm_nonneg (S : Set ℝ) : 0 ≤ qm S := by
  have := ind_nonneg S (1 / 2); have := ind_nonneg S 300; have := ind_nonneg S (-100)
  unfold qm; linarith

theorem exP_apply (S : Set ℝ) : exP S = ENNReal.ofReal (pm S) := by
  have h3 : 0 ≤ ∑ i ∈ Finset.Icc (1 : ℕ) 20, (i : ℝ) / 1050 * ind S (20 + 10 * (i : ℝ)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (ind_nonneg _ _)
  have hsum : ∑ i ∈ Finset.Icc (1 : ℕ) 20, (ENNReal.ofReal ((i : ℝ) / 1050) • Measure.dirac (20 + 10 * (i : ℝ))) S =
      ∑ i ∈ Finset.Icc (1 : ℕ) 20, ENNReal.ofReal ((i : ℝ) / 1050 * ind S (20 + 10 * (i : ℝ))) :=
    Finset.sum_congr rfl fun i _ => measure_smul_dirac S (by positivity) _
  unfold exP pm
  rw [Measure.add_apply, Measure.add_apply, Measure.finsetSum_apply,
    measure_smul_dirac S (by norm_num), measure_smul_dirac S (by norm_num), hsum,
    ← ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (by positivity) (ind_nonneg _ _),
    ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (ind_nonneg _ _)) h3,
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (by norm_num) (ind_nonneg _ _)) h3)
      (mul_nonneg (by norm_num) (ind_nonneg _ _))]

theorem exQ_apply (S : Set ℝ) : exQ S = ENNReal.ofReal (qm S) := by
  unfold exQ qm
  rw [Measure.add_apply, Measure.add_apply,
    measure_smul_dirac S (by norm_num), measure_smul_dirac S (by norm_num), measure_smul_dirac S (by norm_num),
    ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (ind_nonneg _ _)) (mul_nonneg (by norm_num) (ind_nonneg _ _)),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (by norm_num) (ind_nonneg _ _))
      (mul_nonneg (by norm_num) (ind_nonneg _ _))) (mul_nonneg (by norm_num) (ind_nonneg _ _))]

theorem exP_real (S : Set ℝ) : exP.real S = pm S := by
  rw [measureReal_def, exP_apply, ENNReal.toReal_ofReal (pm_nonneg S)]

theorem exQ_real (S : Set ℝ) : exQ.real S = qm S := by
  rw [measureReal_def, exQ_apply, ENNReal.toReal_ofReal (qm_nonneg S)]

theorem pm_univ : pm univ = 1 := by
  unfold pm
  simp only [ind_of_mem (mem_univ _), mul_one, sum_w]
  norm_num

theorem qm_univ : qm univ = 1 := by
  unfold qm
  simp only [ind_of_mem (mem_univ _), mul_one]
  norm_num

instance isProbabilityMeasure_exP : IsProbabilityMeasure exP :=
  ⟨by rw [exP_apply, pm_univ, ENNReal.ofReal_one]⟩

instance isProbabilityMeasure_exQ : IsProbabilityMeasure exQ :=
  ⟨by rw [exQ_apply, qm_univ, ENNReal.ofReal_one]⟩

theorem integrable_exP (g : ℝ → ℝ) : Integrable g exP := by
  unfold exP
  refine ((integrable_smul_dirac g _ _).add_measure ?_).add_measure (integrable_smul_dirac g _ _)
  exact integrable_finsetSum_measure.2 fun i _ => integrable_smul_dirac g _ _

theorem integrable_exQ (g : ℝ → ℝ) : Integrable g exQ := by
  unfold exQ
  exact ((integrable_smul_dirac g _ _).add_measure (integrable_smul_dirac g _ _)).add_measure
    (integrable_smul_dirac g _ _)

theorem integral_exP (g : ℝ → ℝ) :
    ∫ x, g x ∂exP = 2 / 5 * g 0 + ∑ i ∈ Finset.Icc (1 : ℕ) 20, (i : ℝ) / 1050 * g (20 + 10 * (i : ℝ)) +
      2 / 5 * g (-100) := by
  have hsum : ∑ i ∈ Finset.Icc (1 : ℕ) 20, ∫ x, g x ∂(ENNReal.ofReal ((i : ℝ) / 1050) • Measure.dirac (20 + 10 * (i : ℝ))) =
      ∑ i ∈ Finset.Icc (1 : ℕ) 20, (i : ℝ) / 1050 * g (20 + 10 * (i : ℝ)) :=
    Finset.sum_congr rfl fun i _ => integral_smul_dirac g (by positivity) _
  unfold exP
  rw [integral_add_measure ((integrable_smul_dirac g _ _).add_measure
      (integrable_finsetSum_measure.2 fun i _ => integrable_smul_dirac g _ _)) (integrable_smul_dirac g _ _),
    integral_add_measure (integrable_smul_dirac g _ _)
      (integrable_finsetSum_measure.2 fun i _ => integrable_smul_dirac g _ _),
    integral_finsetSum_measure fun i _ => integrable_smul_dirac g _ _,
    integral_smul_dirac g (by norm_num), integral_smul_dirac g (by norm_num), hsum]

theorem integral_exQ (g : ℝ → ℝ) :
    ∫ x, g x ∂exQ = 3 / 10 * g (1 / 2) + 3 / 10 * g 300 + 2 / 5 * g (-100) := by
  unfold exQ
  rw [integral_add_measure ((integrable_smul_dirac g _ _).add_measure (integrable_smul_dirac g _ _))
      (integrable_smul_dirac g _ _),
    integral_add_measure (integrable_smul_dirac g _ _) (integrable_smul_dirac g _ _),
    integral_smul_dirac g (by norm_num), integral_smul_dirac g (by norm_num), integral_smul_dirac g (by norm_num)]

/-! ### Total variation -/

theorem tv_ex : StatFormal.Distances.tvDist exP exQ = 3 / 5 := by
  apply le_antisymm
  · refine StatFormal.Distances.tvDist_le_of_forall fun A _ => ?_
    rw [exP_real, exQ_real]
    unfold pm qm
    have h0 := ind_le_one A 0
    have h0' := ind_nonneg A 0
    have hh := ind_le_one A (1 / 2)
    have hh' := ind_nonneg A (1 / 2)
    have h3 := ind_le_one A 300
    have h3' := ind_nonneg A 300
    have hs := sum_w_le (b := fun i : ℕ => ind A (20 + 10 * (i : ℝ))) fun i _ => ind_le_one _ _
    have hs' := le_sum_w (b := fun i : ℕ => ind A (20 + 10 * (i : ℝ))) (B := 0) fun i _ => ind_nonneg _ _
    rw [abs_le]
    constructor <;> linarith
  · set A : Set ℝ := Iio (1 / 4) ∪ Ioo 1 250 with hA
    have hAm : MeasurableSet A := measurableSet_Iio.union measurableSet_Ioo
    have h := StatFormal.Distances.abs_measureReal_sub_le_tvDist (μ := exP) (ν := exQ) hAm
    have hP : pm A = 1 := by
      unfold pm
      have hs : ∑ i ∈ Finset.Icc (1 : ℕ) 20, (i : ℝ) / 1050 * ind A (20 + 10 * (i : ℝ)) = 1 / 5 := by
        rw [← sum_w]
        refine Finset.sum_congr rfl fun i hi => ?_
        obtain ⟨h1, h2⟩ := mem_Icc_cast hi
        rw [ind_of_mem (Or.inr ⟨by linarith, by linarith⟩), mul_one]
      rw [hs, ind_of_mem (Or.inl (by norm_num)), ind_of_mem (Or.inl (by norm_num))]
      norm_num
    have hQ : qm A = 2 / 5 := by
      unfold qm
      have h1 : (1 / 2 : ℝ) ∉ A := by
        rintro (h | h)
        · simp only [mem_Iio] at h; norm_num at h
        · simp only [mem_Ioo] at h; norm_num at h
      have h2 : (300 : ℝ) ∉ A := by
        rintro (h | h)
        · simp only [mem_Iio] at h; norm_num at h
        · simp only [mem_Ioo] at h; norm_num at h
      rw [ind_of_notMem h1, ind_of_notMem h2, ind_of_mem (Or.inl (by norm_num))]
      norm_num
    rw [exP_real, exQ_real, hP, hQ] at h
    norm_num at h ⊢
    linarith [h]

/-! ### The kernel -/

theorem gaussK_pos (a x : ℝ) : 0 < gaussK a x := Real.exp_pos _

theorem gaussK_le_one (a x : ℝ) : gaussK a x ≤ 1 := by
  unfold gaussK
  rw [Real.exp_le_one_iff]
  nlinarith [sq_nonneg (a - x)]

theorem gaussK_self (a : ℝ) : gaussK a a = 1 := by simp [gaussK]

theorem gaussK_symm (a x : ℝ) : gaussK a x = gaussK x a := by
  unfold gaussK; ring_nf

theorem gaussK_far {a x : ℝ} (h : 100 ≤ (a - x) ^ 2) : gaussK a x ≤ Real.exp (-50) :=
  Real.exp_le_exp.2 (by linarith)

theorem eta_pos : 0 < Real.exp (-50) := Real.exp_pos _

theorem eta_le : Real.exp (-50) ≤ 1 / 1301 := by
  have h := Real.quadratic_le_exp_of_nonneg (x := 50) (by norm_num)
  rw [Real.exp_neg, inv_eq_one_div]
  rw [div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  linarith

theorem gaussK_zero_half : gaussK (1 / 2) 0 = Real.exp (-1 / 8) := by
  unfold gaussK; norm_num

theorem gaussK_half_zero : gaussK 0 (1 / 2) = Real.exp (-1 / 8) := by
  unfold gaussK; norm_num

theorem E_ge : 7 / 8 ≤ Real.exp (-1 / 8) := by
  have := Real.add_one_le_exp (-1 / 8)
  linarith

theorem E_le : Real.exp (-1 / 8) ≤ 8 / 9 := by
  have h := Real.add_one_le_exp (1 / 8)
  rw [show (-1 / 8 : ℝ) = -(1 / 8) by norm_num, Real.exp_neg, inv_eq_one_div,
    div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  linarith

/-! ### The unnormalized witness at the atoms -/

/-- The sum `Σ_j (j/1050) k(20 + 10 j, x)` (the middle atoms of `P`). -/
def midSum (x : ℝ) : ℝ := ∑ j ∈ Finset.Icc (1 : ℕ) 20, (j : ℝ) / 1050 * gaussK (20 + 10 * (j : ℝ)) x

/-- `wit x = ∫ k(a, x) dP(a) − ∫ k(b, x) dQ(b)`, as a finite sum. -/
def wit (x : ℝ) : ℝ :=
  (2 / 5 * gaussK 0 x + midSum x + 2 / 5 * gaussK (-100) x) -
    (3 / 10 * gaussK (1 / 2) x + 3 / 10 * gaussK 300 x + 2 / 5 * gaussK (-100) x)

theorem wit_eq (x : ℝ) : (∫ a, gaussK a x ∂exP) - ∫ b, gaussK b x ∂exQ = wit x := by
  rw [integral_exP (fun a => gaussK a x), integral_exQ (fun b => gaussK b x)]
  rfl

theorem midSum_nonneg (x : ℝ) : 0 ≤ midSum x :=
  Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (gaussK_pos _ _).le

theorem midSum_far {x : ℝ} (h : ∀ j ∈ Finset.Icc (1 : ℕ) 20, 100 ≤ (20 + 10 * (j : ℝ) - x) ^ 2) :
    midSum x ≤ Real.exp (-50) / 5 :=
  sum_w_le fun j hj => gaussK_far (h j hj)

theorem midSum_diag {i : ℕ} (hi : i ∈ Finset.Icc (1 : ℕ) 20) :
    midSum (20 + 10 * (i : ℝ)) ≤ (i : ℝ) / 1050 + Real.exp (-50) / 5 := by
  have hη := eta_pos
  have key : ∀ j ∈ Finset.Icc (1 : ℕ) 20, (j : ℝ) / 1050 * gaussK (20 + 10 * (j : ℝ)) (20 + 10 * (i : ℝ)) ≤
      (if j = i then (j : ℝ) / 1050 else 0) + (j : ℝ) / 1050 * Real.exp (-50) := by
    intro j _
    have hw : (0 : ℝ) ≤ (j : ℝ) / 1050 := by positivity
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl, gaussK_self, mul_one]
      nlinarith
    · rw [if_neg hji, zero_add]
      refine mul_le_mul_of_nonneg_left (gaussK_far ?_) hw
      have h1 : (1 : ℝ) ≤ ((j : ℝ) - i) ^ 2 := by
        rcases Nat.lt_or_gt_of_ne hji with h | h
        · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
          nlinarith
        · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
          nlinarith
      nlinarith
  calc midSum (20 + 10 * (i : ℝ))
      ≤ ∑ j ∈ Finset.Icc (1 : ℕ) 20, ((if j = i then (j : ℝ) / 1050 else 0) + (j : ℝ) / 1050 * Real.exp (-50)) :=
        Finset.sum_le_sum key
    _ = (i : ℝ) / 1050 + Real.exp (-50) / 5 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.Icc 1 20) i (fun j : ℕ => (j : ℝ) / 1050),
          if_pos hi, ← Finset.sum_mul, sum_w]
        ring

theorem wit_zero_ge : 2 / 5 - 3 / 10 * Real.exp (-1 / 8) - 3 / 10 * Real.exp (-50) ≤ wit 0 := by
  have h1 := gaussK_self 0
  have h2 := midSum_nonneg 0
  have h3 := gaussK_zero_half
  have h4 : gaussK 300 0 ≤ Real.exp (-50) := gaussK_far (by norm_num)
  unfold wit; linarith

theorem wit_half_le : wit (1 / 2) ≤ 2 / 5 * Real.exp (-1 / 8) + Real.exp (-50) / 5 - 3 / 10 := by
  have h1 := gaussK_half_zero
  have h2 : midSum (1 / 2) ≤ Real.exp (-50) / 5 := midSum_far fun j hj => by
    obtain ⟨h1, _⟩ := mem_Icc_cast hj
    nlinarith
  have h3 := gaussK_self (1 / 2)
  have h4 := (gaussK_pos 300 (1 / 2)).le
  unfold wit; linarith

theorem wit_half_ge : 2 / 5 * Real.exp (-1 / 8) - 3 / 10 - 3 / 10 * Real.exp (-50) ≤ wit (1 / 2) := by
  have h1 := gaussK_half_zero
  have h2 := midSum_nonneg (1 / 2)
  have h3 := gaussK_self (1 / 2)
  have h4 : gaussK 300 (1 / 2) ≤ Real.exp (-50) := gaussK_far (by norm_num)
  unfold wit; linarith

theorem wit_300_le : wit 300 ≤ 3 / 5 * Real.exp (-50) - 3 / 10 := by
  have h1 : gaussK 0 300 ≤ Real.exp (-50) := gaussK_far (by norm_num)
  have h2 : midSum 300 ≤ Real.exp (-50) / 5 := midSum_far fun j hj => by
    obtain ⟨_, h2⟩ := mem_Icc_cast hj
    nlinarith
  have h3 := gaussK_self 300
  have h4 := (gaussK_pos (1 / 2) 300).le
  unfold wit; linarith

theorem wit_mid_le {i : ℕ} (hi : i ∈ Finset.Icc (1 : ℕ) 20) :
    wit (20 + 10 * (i : ℝ)) ≤ 20 / 1050 + 3 / 5 * Real.exp (-50) := by
  obtain ⟨hi1, hi2⟩ := mem_Icc_cast hi
  have h1 : gaussK 0 (20 + 10 * (i : ℝ)) ≤ Real.exp (-50) := gaussK_far (by nlinarith)
  have h2 := midSum_diag hi
  have h3 := (gaussK_pos (1 / 2) (20 + 10 * (i : ℝ))).le
  have h4 := (gaussK_pos 300 (20 + 10 * (i : ℝ))).le
  have h5 : (i : ℝ) / 1050 ≤ 20 / 1050 := by linarith
  unfold wit; linarith

theorem wit_mid_ge {i : ℕ} (hi : i ∈ Finset.Icc (1 : ℕ) 20) :
    -(3 / 5 * Real.exp (-50)) ≤ wit (20 + 10 * (i : ℝ)) := by
  obtain ⟨hi1, hi2⟩ := mem_Icc_cast hi
  have h1 := (gaussK_pos 0 (20 + 10 * (i : ℝ))).le
  have h2 := midSum_nonneg (20 + 10 * (i : ℝ))
  have h3 : gaussK (1 / 2) (20 + 10 * (i : ℝ)) ≤ Real.exp (-50) := gaussK_far (by nlinarith)
  have h4 : gaussK 300 (20 + 10 * (i : ℝ)) ≤ Real.exp (-50) := gaussK_far (by nlinarith)
  unfold wit; linarith

/-! ### The order facts -/

theorem wit_mid_le_half {i : ℕ} (hi : i ∈ Finset.Icc (1 : ℕ) 20) : wit (20 + 10 * (i : ℝ)) ≤ wit (1 / 2) := by
  have := wit_mid_le hi; have := wit_half_ge; have := E_ge; have := eta_le
  linarith

theorem wit_300_le_half : wit 300 ≤ wit (1 / 2) := by
  have := wit_300_le; have := wit_half_ge; have := E_ge; have := eta_le
  linarith

theorem wit_half_lt_zero : wit (1 / 2) < wit 0 := by
  have := wit_half_le; have := wit_zero_ge; have := E_le; have := eta_le; have := eta_pos
  linarith

/-! ### `MMD² = ∫ wit dP − ∫ wit dQ`, hence `MMD > 0` -/

theorem continuous_gaussK : Continuous (Function.uncurry gaussK) := by
  change Continuous fun p : ℝ × ℝ => Real.exp (-(p.1 - p.2) ^ 2 / 2)
  fun_prop

theorem integrable_gaussK_prod : Integrable (Function.uncurry gaussK) (exP.prod exQ) := by
  refine Integrable.of_bound continuous_gaussK.aestronglyMeasurable 1 (ae_of_all _ fun p => ?_)
  change ‖gaussK p.1 p.2‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_pos (gaussK_pos _ _)]
  exact gaussK_le_one _ _

/-- The squared MMD as the `P − Q` mean of the unnormalized witness (symmetry of `k`, and Fubini for the
cross term). -/
theorem mmd_sq_eq :
    (∫ a, ∫ a', gaussK a a' ∂exP ∂exP) - 2 * (∫ a, ∫ b, gaussK a b ∂exQ ∂exP) + ∫ b, ∫ b', gaussK b b' ∂exQ ∂exQ =
      (∫ x, wit x ∂exP) - ∫ x, wit x ∂exQ := by
  have hA : (∫ a, ∫ a', gaussK a a' ∂exP ∂exP) = ∫ a, ∫ a', gaussK a' a ∂exP ∂exP :=
    integral_congr_ae (ae_of_all _ fun a => integral_congr_ae (ae_of_all _ fun a' => gaussK_symm a a'))
  have hB1 : (∫ a, ∫ b, gaussK a b ∂exQ ∂exP) = ∫ a, ∫ b, gaussK b a ∂exQ ∂exP :=
    integral_congr_ae (ae_of_all _ fun a => integral_congr_ae (ae_of_all _ fun b => gaussK_symm a b))
  have hB2 : (∫ a, ∫ b, gaussK a b ∂exQ ∂exP) = ∫ b, ∫ a, gaussK a b ∂exP ∂exQ :=
    integral_integral_swap integrable_gaussK_prod
  have hC : (∫ b, ∫ b', gaussK b b' ∂exQ ∂exQ) = ∫ b, ∫ b', gaussK b' b ∂exQ ∂exQ :=
    integral_congr_ae (ae_of_all _ fun b => integral_congr_ae (ae_of_all _ fun b' => gaussK_symm b b'))
  have hP : (∫ x, wit x ∂exP) = (∫ a, ∫ a', gaussK a' a ∂exP ∂exP) - ∫ a, ∫ b, gaussK b a ∂exQ ∂exP := by
    rw [← integral_sub (integrable_exP _) (integrable_exP _)]
    exact integral_congr_ae (ae_of_all _ fun x => (wit_eq x).symm)
  have hQ : (∫ x, wit x ∂exQ) = (∫ b, ∫ a, gaussK a b ∂exP ∂exQ) - ∫ b, ∫ b', gaussK b' b ∂exQ ∂exQ := by
    rw [← integral_sub (integrable_exQ _) (integrable_exQ _)]
    exact integral_congr_ae (ae_of_all _ fun x => (wit_eq x).symm)
  rw [hP, hQ]
  linarith

/-- `MMD² ≥ 0.34 − 0.24 e^{−1/8} − 0.48 e^{−50} > 0.12` (the `−100` terms cancel exactly). -/
theorem mmd_sq_pos : 0 < (∫ x, wit x ∂exP) - ∫ x, wit x ∂exQ := by
  rw [integral_exP wit, integral_exQ wit]
  have h0 := wit_zero_ge
  have hh := wit_half_le
  have h3 := wit_300_le
  have hs := le_sum_w (b := fun i : ℕ => wit (20 + 10 * (i : ℝ))) (B := -(3 / 5 * Real.exp (-50)))
    fun i hi => wit_mid_ge hi
  have := E_le; have := eta_le; have := eta_pos
  linarith

theorem mmd_pos : 0 < mmdGauss exP exQ := by
  unfold mmdGauss
  rw [mmd_sq_eq]
  exact Real.sqrt_pos.2 mmd_sq_pos

/-! ### `KS⁺(f₀) = 2/5` -/

theorem exWitness_eq (x : ℝ) : exWitness exP exQ x = wit x / mmdGauss exP exQ := by
  unfold exWitness
  rw [wit_eq]

theorem continuous_wit : Continuous wit := by
  unfold wit midSum gaussK
  fun_prop

theorem measurable_exWitness : Measurable (exWitness exP exQ) := by
  have : exWitness exP exQ = fun x => wit x / mmdGauss exP exQ := funext exWitness_eq
  rw [this]
  exact continuous_wit.measurable.div_const _

theorem f0_mid_le_half {i : ℕ} (hi : i ∈ Finset.Icc (1 : ℕ) 20) :
    exWitness exP exQ (20 + 10 * (i : ℝ)) ≤ exWitness exP exQ (1 / 2) := by
  rw [exWitness_eq, exWitness_eq]
  exact div_le_div_of_nonneg_right (wit_mid_le_half hi) mmd_pos.le

theorem f0_300_le_half : exWitness exP exQ 300 ≤ exWitness exP exQ (1 / 2) := by
  rw [exWitness_eq, exWitness_eq]
  exact div_le_div_of_nonneg_right wit_300_le_half mmd_pos.le

theorem f0_half_lt_zero : exWitness exP exQ (1 / 2) < exWitness exP exQ 0 := by
  rw [exWitness_eq, exWitness_eq]
  exact (div_lt_div_iff_of_pos_right mmd_pos).2 wit_half_lt_zero

/-- `KS⁺(f₀) = 2/5`: every up-set of `f₀` has `P − Q` mass `≤ 2/5` (it contains `1/2` and then at most
`0.4 + 0.2 − 0.3`, or it misses `1/2`, hence all of `20 + 10 i` and `300`, and then at most `0.4`; the
masses at `−100` cancel), and `{f₀ > f₀(1/2)}` meets the atoms in `0` and possibly `−100`. -/
theorem ks_ex : ksPlus exP exQ (exWitness exP exQ) = 2 / 5 := by
  apply le_antisymm
  · unfold ksPlus
    refine ciSup_le fun x => ?_
    rw [exP_real, exQ_real]
    set S := {z | x < exWitness exP exQ z} with hS_def
    unfold pm qm
    have i0 := ind_le_one S 0
    have ih := ind_nonneg S (1 / 2)
    have i3 := ind_nonneg S 300
    by_cases hS : (1 / 2 : ℝ) ∈ S
    · rw [ind_of_mem hS]
      have hs := sum_w_le (b := fun i : ℕ => ind S (20 + 10 * (i : ℝ))) fun i _ => ind_le_one _ _
      linarith
    · have hx : exWitness exP exQ (1 / 2) ≤ x := not_lt.1 hS
      have hs := sum_w_le (b := fun i : ℕ => ind S (20 + 10 * (i : ℝ))) (B := 0) fun i hi =>
        (ind_of_notMem fun h => (not_lt.2 ((f0_mid_le_half hi).trans hx)) h).le
      linarith
  · have h := le_ksPlus exP exQ (exWitness exP exQ) (exWitness exP exQ (1 / 2))
    rw [exP_real, exQ_real] at h
    set S := {z | exWitness exP exQ (1 / 2) < exWitness exP exQ z} with hS_def
    have hS0 : (0 : ℝ) ∈ S := f0_half_lt_zero
    have hSh : (1 / 2 : ℝ) ∉ S := fun h => lt_irrefl (exWitness exP exQ (1 / 2)) h
    have hS3 : (300 : ℝ) ∉ S := not_lt.2 f0_300_le_half
    have hs := le_sum_w (b := fun i : ℕ => ind S (20 + 10 * (i : ℝ))) (B := 0) fun i _ => ind_nonneg _ _
    unfold pm qm at h
    rw [ind_of_mem hS0, ind_of_notMem hSh, ind_of_notMem hS3] at h
    linarith

/-! ### Assembly -/

/-- **Proposition 3**, the example (finite certificate). -/
theorem alpha0_example_route : Claims.alpha0_example := by
  refine ⟨inferInstance, inferInstance, tv_ex, mmd_pos, ks_ex, fun t u htu => ?_⟩
  have h := ((ramp_ks_route ℝ exP exQ (exWitness exP exQ) measurable_exWitness).1 t u htu).2
  rwa [ks_ex] at h

end StatFormal.Wave30tz
