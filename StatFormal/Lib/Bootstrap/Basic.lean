import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite resampling: averages, variances, moments and Hoeffding's inequality (library)

The nonparametric bootstrap of a sample `v : Fin n → ℝ` draws `I : Fin n → Fin n` uniformly (i.i.d. uniform
indices) and evaluates statistics at `v ∘ I`. Everything is a finite average:

* `bAvg F = |ι|⁻¹ Σ_i F i`, `bVar F = bAvg (F − bAvg F)²` (mean and variance under the uniform law on `ι`);
  linearity, `bVar_eq`, Cauchy–Schwarz `bAvg_mul_sq_le`, Minkowski `sqrt_bVar_add_le`, and
  `bVar_prod_add` (variance of `F(i) + G(k)` under the product uniform law);
* `bAvg_resample_sq`: the bootstrap second moment `E*[((Σ_i a_{I_i})/n − ā)²] = (P_n a² − (P_n a)²)/n`;
* `hoeffding_resample`: `P*((Σ_i b_{I_i})/n − b̄ ≥ t) ≤ exp(−2nt²)` for `b ∈ [0,1]` (Mathlib's Hoeffding lemma on
  the uniform law of `Fin n`, factorised over the `n` independent draws by `Fintype.prod_sum`).
-/

set_option linter.style.longLine false

noncomputable section
open Finset Real

namespace StatFormal.Foundations.Bootstrap

/-! ### Finite averages and variances -/

section Avg
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The average `|ι|⁻¹ Σ_i F i` (expectation under the uniform law on `ι`). -/
def bAvg (F : ι → ℝ) : ℝ := (Fintype.card ι : ℝ)⁻¹ * ∑ i, F i

/-- The variance `bAvg (F − bAvg F)²` under the uniform law on `ι`. -/
def bVar (F : ι → ℝ) : ℝ := bAvg fun i => (F i - bAvg F) ^ 2

lemma bAvg_add (F G : ι → ℝ) : bAvg (fun i => F i + G i) = bAvg F + bAvg G := by
  unfold bAvg; rw [sum_add_distrib, mul_add]

lemma bAvg_sub (F G : ι → ℝ) : bAvg (fun i => F i - G i) = bAvg F - bAvg G := by
  unfold bAvg; rw [sum_sub_distrib, mul_sub]

lemma bAvg_const_mul (c : ℝ) (F : ι → ℝ) : bAvg (fun i => c * F i) = c * bAvg F := by
  unfold bAvg; rw [← mul_sum]; ring

lemma bAvg_mul_const (c : ℝ) (F : ι → ℝ) : bAvg (fun i => F i * c) = bAvg F * c := by
  unfold bAvg; rw [← sum_mul]; ring

lemma bAvg_neg (F : ι → ℝ) : bAvg (fun i => -F i) = -bAvg F := by
  unfold bAvg; rw [sum_neg_distrib]; ring

lemma bAvg_const [Nonempty ι] (c : ℝ) : bAvg (fun _ : ι => c) = c := by
  unfold bAvg
  rw [sum_const, card_univ, nsmul_eq_mul]
  have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma bAvg_mono {F G : ι → ℝ} (h : ∀ i, F i ≤ G i) : bAvg F ≤ bAvg G :=
  mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => h i) (by positivity)

lemma bAvg_nonneg {F : ι → ℝ} (h : ∀ i, 0 ≤ F i) : 0 ≤ bAvg F :=
  mul_nonneg (by positivity) (sum_nonneg fun i _ => h i)

lemma bAvg_le_const [Nonempty ι] {F : ι → ℝ} {c : ℝ} (h : ∀ i, F i ≤ c) : bAvg F ≤ c :=
  (bAvg_mono h).trans (bAvg_const c).le

lemma bVar_nonneg (F : ι → ℝ) : 0 ≤ bVar F := bAvg_nonneg fun _ => sq_nonneg _

lemma bVar_eq [Nonempty ι] (F : ι → ℝ) : bVar F = bAvg (fun i => F i ^ 2) - bAvg F ^ 2 := by
  unfold bVar
  have e : (fun i => (F i - bAvg F) ^ 2) = fun i => F i ^ 2 + (-(2 * bAvg F) * F i + bAvg F ^ 2) := by
    funext i; ring
  rw [e, bAvg_add, bAvg_add, bAvg_const_mul, bAvg_const]; ring

lemma bVar_le_bAvg_sq [Nonempty ι] (F : ι → ℝ) : bVar F ≤ bAvg fun i => F i ^ 2 := by
  rw [bVar_eq]; linarith [sq_nonneg (bAvg F)]

lemma bVar_add_const [Nonempty ι] (F : ι → ℝ) (c : ℝ) : bVar (fun i => F i + c) = bVar F := by
  unfold bVar
  rw [bAvg_add, bAvg_const]
  congr 1; funext i; ring

lemma bVar_const_mul (c : ℝ) (F : ι → ℝ) : bVar (fun i => c * F i) = c ^ 2 * bVar F := by
  have h1 : bAvg (fun i => c * F i) = c * bAvg F := bAvg_const_mul c F
  unfold bVar
  have e : (fun i => (c * F i - bAvg fun i => c * F i) ^ 2) = fun i => c ^ 2 * (F i - bAvg F) ^ 2 := by
    funext i; rw [h1]; ring
  rw [e, bAvg_const_mul]

lemma bVar_neg (F : ι → ℝ) : bVar (fun i => -F i) = bVar F := by
  have := bVar_const_mul (-1) F
  simp only [neg_one_mul, neg_one_sq, one_mul] at this
  exact this

/-- Cauchy–Schwarz for finite averages. -/
lemma bAvg_mul_sq_le (F G : ι → ℝ) :
    bAvg (fun i => F i * G i) ^ 2 ≤ bAvg (fun i => F i ^ 2) * bAvg (fun i => G i ^ 2) := by
  unfold bAvg
  have h := sum_mul_sq_le_sq_mul_sq univ F G
  have hc : (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ := by positivity
  calc ((Fintype.card ι : ℝ)⁻¹ * ∑ i, F i * G i) ^ 2 = (Fintype.card ι : ℝ)⁻¹ ^ 2 * (∑ i, F i * G i) ^ 2 := by ring
    _ ≤ (Fintype.card ι : ℝ)⁻¹ ^ 2 * ((∑ i, F i ^ 2) * ∑ i, G i ^ 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- Minkowski for standard deviations: `√Var(F + G) ≤ √Var F + √Var G`. -/
lemma sqrt_bVar_add_le [Nonempty ι] (F G : ι → ℝ) : √(bVar fun i => F i + G i) ≤ √(bVar F) + √(bVar G) := by
  set f : ι → ℝ := fun i => F i - bAvg F
  set g : ι → ℝ := fun i => G i - bAvg G
  have hv : bVar (fun i => F i + G i) = bAvg fun i => (f i + g i) ^ 2 := by
    unfold bVar; rw [bAvg_add]; congr 1; funext i; simp only [f, g]; ring
  have hF : bVar F = bAvg fun i => f i ^ 2 := rfl
  have hG : bVar G = bAvg fun i => g i ^ 2 := rfl
  have e : (bAvg fun i => (f i + g i) ^ 2) = bAvg (fun i => f i ^ 2) + 2 * bAvg (fun i => f i * g i) +
      bAvg fun i => g i ^ 2 := by
    rw [← bAvg_const_mul, ← bAvg_add, ← bAvg_add]; congr 1; funext i; ring
  have hcs := bAvg_mul_sq_le f g
  have ha := bAvg_nonneg fun i => sq_nonneg (f i)
  have hb := bAvg_nonneg fun i => sq_nonneg (g i)
  have hcs' : bAvg (fun i => f i * g i) ≤ √(bAvg fun i => f i ^ 2) * √(bAvg fun i => g i ^ 2) := by
    rw [← Real.sqrt_mul ha]
    exact Real.le_sqrt_of_sq_le hcs
  rw [hv, hF, hG]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [e, add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  linarith

/-- `|√Var(F + G) − √Var G| ≤ √Var F`. -/
lemma abs_sqrt_bVar_add_sub_le [Nonempty ι] (F G : ι → ℝ) :
    |√(bVar fun i => F i + G i) - √(bVar G)| ≤ √(bVar F) := by
  rw [abs_sub_le_iff]
  constructor
  · have := sqrt_bVar_add_le F G; linarith
  · have h := sqrt_bVar_add_le (fun i => F i + G i) (fun i => -F i)
    simp only [add_neg_cancel_comm, bVar_neg] at h
    show √(bVar fun i => G i) - _ ≤ _
    linarith

/-- The variance of `F(i) + G(k)` under the product of the uniform laws is `Var F + Var G`. -/
lemma bVar_prod_add [Nonempty ι] [Nonempty κ] (F : ι → ℝ) (G : κ → ℝ) :
    bVar (fun p : ι × κ => F p.1 + G p.2) = bVar F + bVar G := by
  have hcard : (Fintype.card (ι × κ) : ℝ) = Fintype.card ι * Fintype.card κ := by
    rw [Fintype.card_prod]; push_cast; ring
  have hι : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hκ : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have havg : ∀ H : ι × κ → ℝ, bAvg H = bAvg fun i => bAvg fun k => H (i, k) := fun H => by
    unfold bAvg
    rw [hcard, Fintype.sum_prod_type, mul_inv, mul_assoc]
    congr 1
    rw [mul_sum]
  have hm : bAvg (fun p : ι × κ => F p.1 + G p.2) = bAvg F + bAvg G := by
    rw [havg]
    simp only [bAvg_add, bAvg_const]
  unfold bVar
  rw [hm, havg]
  have hG0 : bAvg (fun k => G k - bAvg G) = 0 := by rw [bAvg_sub, bAvg_const, sub_self]
  have inner : ∀ i, (bAvg fun k => (F i + G k - (bAvg F + bAvg G)) ^ 2) =
      (F i - bAvg F) ^ 2 + bAvg fun k => (G k - bAvg G) ^ 2 := fun i => by
    have e : (fun k => (F i + G k - (bAvg F + bAvg G)) ^ 2) = fun k =>
        (F i - bAvg F) ^ 2 + ((2 * (F i - bAvg F)) * (G k - bAvg G) + (G k - bAvg G) ^ 2) := by
      funext k; ring
    rw [e, bAvg_add, bAvg_const, bAvg_add, bAvg_const_mul, hG0, mul_zero, zero_add]
  simp only [inner]
  rw [bAvg_add, bAvg_const]

end Avg

/-! ### Resampling moments -/

section Resample
variable {n : ℕ}

lemma card_resample : (Fintype.card (Fin n → Fin n) : ℝ) = (n : ℝ) ^ n := by
  simp [Fintype.card_fun]

/-- Sum over resamples of a product: the `n` draws are independent. -/
lemma sum_resample_prod (f : Fin n → Fin n → ℝ) :
    ∑ I : Fin n → Fin n, ∏ i, f i (I i) = ∏ i, ∑ j, f i j :=
  (Fintype.prod_sum f).symm

lemma sum_resample_apply_eq_zero {c : Fin n → ℝ} (hc : ∑ j, c j = 0) (i : Fin n) :
    ∑ I : Fin n → Fin n, c (I i) = 0 := by
  set f : Fin n → Fin n → ℝ := fun k j => if k = i then c j else 1
  have e : ∀ I : Fin n → Fin n, c (I i) = ∏ k, f k (I k) := fun I => by
    simp only [f]; rw [Finset.prod_ite_eq' univ i]; simp
  rw [Finset.sum_congr rfl fun I _ => e I, sum_resample_prod]
  exact Finset.prod_eq_zero (mem_univ i) (by simp [f, hc])

lemma sum_resample_mul_eq_zero {c : Fin n → ℝ} (hc : ∑ j, c j = 0) {i i' : Fin n} (h : i ≠ i') :
    ∑ I : Fin n → Fin n, c (I i) * c (I i') = 0 := by
  set f : Fin n → Fin n → ℝ := fun k j => if k = i then c j else if k = i' then c j else 1
  have e : ∀ I : Fin n → Fin n, c (I i) * c (I i') = ∏ k, f k (I k) := fun I => by
    rw [← Finset.prod_subset (subset_univ {i, i'}) (fun k _ hk => ?_), Finset.prod_pair h]
    · simp [f, h.symm]
    · simp only [mem_insert, mem_singleton, not_or] at hk
      simp [f, hk.1, hk.2]
  rw [Finset.sum_congr rfl fun I _ => e I, sum_resample_prod]
  exact Finset.prod_eq_zero (mem_univ i) (by simp [f, hc])

lemma sum_resample_sq (c : Fin n → ℝ) (i : Fin n) :
    ∑ I : Fin n → Fin n, c (I i) ^ 2 = (n : ℝ) ^ (n - 1) * ∑ j, c j ^ 2 := by
  set f : Fin n → Fin n → ℝ := fun k j => if k = i then c j ^ 2 else 1
  have e : ∀ I : Fin n → Fin n, c (I i) ^ 2 = ∏ k, f k (I k) := fun I => by
    simp only [f]; rw [Finset.prod_ite_eq' univ i]; simp
  rw [Finset.sum_congr rfl fun I _ => e I, sum_resample_prod,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ i)]
  have h2 : ∀ k ∈ univ \ {i}, ∑ j, f k j = n := fun k hk => by
    have : k ≠ i := by simpa using hk
    simp [f, this]
  rw [Finset.prod_congr rfl h2, prod_const]
  have hc : (univ \ {i} : Finset (Fin n)).card = n - 1 := by
    rw [card_sdiff_of_subset (subset_univ _)]; simp
  rw [hc]
  simp [f]
  ring

/-- **Bootstrap second moment**: `E*[((Σ_i a_{I_i})/n − ā)²] = (P_n a² − (P_n a)²)/n`. -/
lemma bAvg_resample_sq (hn : 0 < n) (a : Fin n → ℝ) :
    bAvg (fun I : Fin n → Fin n => ((∑ i, a (I i)) / n - (∑ j, a j) / n) ^ 2) =
      ((∑ j, a j ^ 2) / n - ((∑ j, a j) / n) ^ 2) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set abar := (∑ j, a j) / n with habar
  set c : Fin n → ℝ := fun j => a j - abar
  have hsa : ∑ j, a j = n * abar := by rw [habar]; field_simp
  have hc : ∑ j, c j = 0 := by
    simp only [c, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hsa, sub_self]
  have hc2 : ∑ j, c j ^ 2 = ∑ j, a j ^ 2 - n * abar ^ 2 := by
    have e : ∀ j, c j ^ 2 = a j ^ 2 + (-(2 * abar) * a j + abar ^ 2) := fun j => by simp only [c]; ring
    simp only [e, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hsa]
    ring
  have e1 : ∀ I : Fin n → Fin n, (∑ i, a (I i)) / n - abar = (∑ i, c (I i)) / n := fun I => by
    simp only [c, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hsum : ∑ I : Fin n → Fin n, (∑ i, c (I i)) ^ 2 = (n : ℝ) * ((n : ℝ) ^ (n - 1) * ∑ j, c j ^ 2) := by
    calc ∑ I : Fin n → Fin n, (∑ i, c (I i)) ^ 2 = ∑ I : Fin n → Fin n, ∑ i, ∑ i', c (I i) * c (I i') := by
          refine sum_congr rfl fun I _ => ?_
          rw [sq, sum_mul_sum]
      _ = ∑ i, ∑ i', ∑ I : Fin n → Fin n, c (I i) * c (I i') := by
          rw [Finset.sum_comm]; exact sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ _i : Fin n, (n : ℝ) ^ (n - 1) * ∑ j, c j ^ 2 := by
          refine sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single i (fun i' _ hne => sum_resample_mul_eq_zero hc (Ne.symm hne)) (by simp)]
          simp_rw [← sq]
          exact sum_resample_sq c i
      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpow : (n : ℝ) * (n : ℝ) ^ (n - 1) = (n : ℝ) ^ n := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  unfold bAvg
  rw [card_resample]
  simp_rw [e1, div_pow]
  rw [← sum_div, hsum, ← mul_assoc, hpow, hc2]
  have hpn : (0 : ℝ) < (n : ℝ) ^ n := pow_pos hn' n
  field_simp

/-- The bootstrap mean is centred: `E*[(Σ_i a_{I_i})/n − ā] = 0`. -/
lemma bAvg_resample_mean (hn : 0 < n) (a : Fin n → ℝ) :
    bAvg (fun I : Fin n → Fin n => (∑ i, a (I i)) / n - (∑ j, a j) / n) = 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set abar := (∑ j, a j) / n with habar
  set c : Fin n → ℝ := fun j => a j - abar
  have hsa : ∑ j, a j = n * abar := by rw [habar]; field_simp
  have hc : ∑ j, c j = 0 := by
    simp only [c, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hsa, sub_self]
  have e1 : ∀ I : Fin n → Fin n, (∑ i, a (I i)) / n - abar = (∑ i, c (I i)) / n := fun I => by
    simp only [c, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  unfold bAvg
  rw [Finset.sum_congr rfl fun I _ => e1 I, ← sum_div, Finset.sum_comm]
  simp [sum_resample_apply_eq_zero hc]

lemma bAvg_exp_sum (c : Fin n → ℝ) (s : ℝ) :
    bAvg (fun I : Fin n → Fin n => exp (s * ∑ i, c (I i))) = ((∑ j, exp (s * c j)) / n) ^ n := by
  unfold bAvg
  rw [card_resample]
  have e : ∀ I : Fin n → Fin n, exp (s * ∑ i, c (I i)) = ∏ i, (fun _ j => exp (s * c j)) i (I i) := fun I => by
    rw [mul_sum, Real.exp_sum]
  rw [Finset.sum_congr rfl fun I _ => e I, sum_resample_prod (fun _ j => exp (s * c j)), prod_const, card_univ,
    Fintype.card_fin, div_pow, div_eq_inv_mul]

/-- Hoeffding's lemma for the uniform law on `Fin n`. -/
lemma avg_exp_le (hn : 0 < n) {c : Fin n → ℝ} (hc : ∑ j, c j = 0) {a : ℝ} (hb : ∀ j, a ≤ c j ∧ c j ≤ a + 1)
    (s : ℝ) : (∑ j, exp (s * c j)) / n ≤ exp (s ^ 2 / 8) := by
  have : NeZero n := ⟨hn.ne'⟩
  set μ := (PMF.uniformOfFintype (Fin n)).toMeasure
  have hint : ∀ g : Fin n → ℝ, ∫ j, g j ∂μ = (∑ j, g j) / n := fun g => by
    rw [PMF.integral_eq_sum]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      smul_eq_mul, ← mul_sum]
    rw [div_eq_inv_mul]
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := μ) (X := c) (a := a)
    (b := a + 1) (Measurable.of_discrete.aemeasurable) (MeasureTheory.ae_of_all _ fun j => ⟨(hb j).1, (hb j).2⟩)
    (by rw [hint, hc, zero_div])
  have := hsub.mgf_le s
  rw [ProbabilityTheory.mgf, hint] at this
  refine this.trans (le_of_eq ?_)
  congr 1
  have : ‖a + 1 - a‖₊ = 1 := by simp
  rw [this]
  push_cast
  ring

/-- **Hoeffding's inequality for the bootstrap mean** of `b ∈ [0,1]`. -/
lemma hoeffding_resample (hn : 0 < n) (b : Fin n → ℝ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    bAvg (fun I : Fin n → Fin n => if t ≤ (∑ i, b (I i)) / n - (∑ j, b j) / n then (1 : ℝ) else 0) ≤
      exp (-2 * n * t ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set bbar := (∑ j, b j) / n with hbbar
  set c : Fin n → ℝ := fun j => b j - bbar
  have hsa : ∑ j, b j = n * bbar := by rw [hbbar]; field_simp
  have hc : ∑ j, c j = 0 := by
    simp only [c, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hsa, sub_self]
  have hcb : ∀ j, -bbar ≤ c j ∧ c j ≤ -bbar + 1 := fun j => by
    simp only [c]; constructor <;> linarith [(hb j).1, (hb j).2]
  set s := 4 * t with hs
  have hs0 : 0 ≤ s := by positivity
  have key : ∀ I : Fin n → Fin n, (if t ≤ (∑ i, b (I i)) / n - bbar then (1 : ℝ) else 0) ≤
      exp (-(s * n * t)) * exp (s * ∑ i, c (I i)) := fun I => by
    have e : (∑ i, b (I i)) / n - bbar = (∑ i, c (I i)) / n := by
      simp only [c, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [e, ← Real.exp_add]
    split_ifs with h
    · refine Real.one_le_exp ?_
      rw [le_div_iff₀ hn'] at h
      nlinarith
    · exact (exp_pos _).le
  calc bAvg (fun I : Fin n → Fin n => if t ≤ (∑ i, b (I i)) / n - bbar then (1 : ℝ) else 0)
      ≤ bAvg (fun I : Fin n → Fin n => exp (-(s * n * t)) * exp (s * ∑ i, c (I i))) := bAvg_mono key
    _ = exp (-(s * n * t)) * ((∑ j, exp (s * c j)) / n) ^ n := by rw [bAvg_const_mul, bAvg_exp_sum]
    _ ≤ exp (-(s * n * t)) * exp (s ^ 2 / 8) ^ n := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (div_nonneg (sum_nonneg fun j _ => (exp_pos _).le) (Nat.cast_nonneg n)) (avg_exp_le hn hc hcb s) n)
          (exp_pos _).le
    _ = exp (-2 * n * t ^ 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        simp only [hs]
        ring

end Resample

end StatFormal.Foundations.Bootstrap
