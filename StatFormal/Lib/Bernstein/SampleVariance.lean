import StatFormal.Lib.Bernstein.Bernstein
import StatFormal.Lib.Bernstein.Pairs
import StatFormal.Lib.Bernstein.Hoeffding
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Concentration of the sample standard deviation

Library component F.B (part 5). Untrusted library code: no `Statements.lean` is involved.

Setting of `Bernstein.lean`: `Z_i = g(ω i)` i.i.d. under `ν^n`, `g` measurable with values in
`[0, 1]`. The sample variance is `V_n = (1/(n(n−1))) Σ_{i<j} (Z_i − Z_j)²` (`sampleVar`).

## Main results

* `sqrt_popVar_le_of_pairs`: for `n ≥ 2`, `k = ⌊n/2⌋` and `0 < δ ≤ 1`,
  `P(√V_n + √(log(1/δ)/k) ≤ σ) ≤ δ`;
* `sqrt_popVar_le` (**Maurer–Pontil 2009, Thm 10**): `P(√V_n + √(2 log(1/δ)/(n−1)) ≤ σ) ≤ δ`.

## Proof

Not the entropy method of Maurer–Pontil, but Hoeffding's (1963) representation of the U-statistic
`V_n` as the average over permutations `σ` of `(1/k) Σ_{i<k} h(Z_{σ(2i)}, Z_{σ(2i+1)})`,
`h(x, y) = (x − y)²/2 ∈ [0, ½]` (`Hoeffding.lean`), Jensen for `exp`, independence of disjoint
pairs (`Pairs.lean`) and the lower-tail bound `E e^{−λh} ≤ exp((λ²/4 − λ) σ²)` (from
`e^{−y} ≤ 1 − y + y²/2` and `h² ≤ h/2`). Since `⌊n/2⌋ ≥ (n−1)/2`, the constant is the paper's
(and slightly better for even `n`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set

namespace StatFormal.Bernstein

variable {β : Type*} [MeasurableSpace β]

/-- Sample variance `V_n = (1/(n(n−1))) Σ_{i<j} (g(ω i) − g(ω j))²`. -/
def sampleVar {n : ℕ} (g : β → ℝ) (ω : Fin n → β) : ℝ :=
  (∑ i, ∑ j, if i < j then (g (ω i) - g (ω j)) ^ 2 else 0) / (n * (n - 1))

omit [MeasurableSpace β] in
theorem sampleVar_nonneg {n : ℕ} (hn : 1 ≤ n) (g : β → ℝ) (ω : Fin n → β) :
    0 ≤ sampleVar g ω := by
  unfold sampleVar
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
    (mul_nonneg (by linarith) (by linarith))
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

theorem measurable_sampleVar {n : ℕ} {g : β → ℝ} (hg : Measurable g) :
    Measurable (sampleVar (n := n) g) := by
  unfold sampleVar
  refine Measurable.div_const (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _
    fun j _ => ?_) _
  split_ifs
  · exact ((hg.comp (measurable_pi_apply i)).sub (hg.comp (measurable_pi_apply j))).pow_const 2
  · exact measurable_const

variable (ν : Measure β) [IsProbabilityMeasure ν]

/-- The pair kernel `h(x, y) = (g x − g y)²/2`. -/
def pairKernel (g : β → ℝ) (x y : β) : ℝ := (g x - g y) ^ 2 / 2

omit [MeasurableSpace β] in
theorem pairKernel_mem {g : β → ℝ} (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) (x y : β) :
    pairKernel g x y ∈ Icc (0 : ℝ) (1 / 2) := by
  unfold pairKernel
  have hx := hg01 x
  have hy := hg01 y
  constructor
  · positivity
  · nlinarith [hx.1, hx.2, hy.1, hy.2]

theorem measurable_pairKernel {g : β → ℝ} (hg : Measurable g) :
    Measurable fun z : β × β => pairKernel g z.1 z.2 :=
  (((hg.comp measurable_fst).sub (hg.comp measurable_snd)).pow_const 2).div_const 2

/-- `E_{ν⊗ν} h = σ²`. -/
theorem integral_pairKernel {g : β → ℝ} (hg : Measurable g) (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    ∫ z, pairKernel g z.1 z.2 ∂(ν.prod ν) = popVar ν g := by
  set μ := popMean ν g with hμ
  set u : β → ℝ := fun x => g x - μ with hu
  have hgi : Integrable g ν := Integrable.of_mem_Icc 0 1 hg.aemeasurable (ae_of_all _ hg01)
  have hui : Integrable u ν := hgi.sub (integrable_const μ)
  have hu0 : ∫ x, u x ∂ν = 0 := by
    simp only [hu]
    rw [integral_sub hgi (integrable_const _), integral_const]
    simp [hμ, popMean]
  have hu2i : Integrable (fun x => u x ^ 2 / 2) ν := by
    refine Integrable.of_mem_Icc 0 (1 / 2)
      (((hg.sub measurable_const).pow_const 2).div_const 2).aemeasurable (ae_of_all _ fun x => ?_)
    have hx := hg01 x
    have hm := popMean_mem_Icc ν hg hg01
    simp only [hu]
    constructor
    · positivity
    · rw [← hμ] at hm; nlinarith [hx.1, hx.2, hm.1, hm.2]
  have hpt : ∀ z : β × β, pairKernel g z.1 z.2 =
      (u z.1 ^ 2 / 2) * 1 + (-u z.1) * u z.2 + 1 * (u z.2 ^ 2 / 2) := fun z => by
    simp only [pairKernel, hu]; ring
  simp_rw [hpt]
  have i1 : Integrable (fun z : β × β => (u z.1 ^ 2 / 2) * 1) (ν.prod ν) :=
    hu2i.mul_prod (integrable_const 1)
  have i2 : Integrable (fun z : β × β => (-u z.1) * u z.2) (ν.prod ν) := hui.neg.mul_prod hui
  have i3 : Integrable (fun z : β × β => 1 * (u z.2 ^ 2 / 2)) (ν.prod ν) :=
    (integrable_const 1).mul_prod hu2i
  have i12 : Integrable (fun z : β × β => (u z.1 ^ 2 / 2) * 1 + (-u z.1) * u z.2) (ν.prod ν) :=
    i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2,
    integral_prod_mul (fun x => u x ^ 2 / 2) (fun _ => (1 : ℝ)),
    integral_prod_mul (fun x => -u x) u,
    integral_prod_mul (fun _ => (1 : ℝ)) (fun x => u x ^ 2 / 2),
    integral_neg, hu0, integral_div]
  simp only [integral_const, probReal_univ, one_smul, mul_one, one_mul, neg_zero, zero_mul,
    add_zero]
  rw [popVar, ← hμ]
  ring

/-- **Lower-tail MGF of the pair kernel**: `E_{ν⊗ν} e^{−λh} ≤ exp((λ²/4 − λ) σ²)` for `λ ≥ 0`. -/
theorem integral_exp_neg_pairKernel_le {g : β → ℝ} (hg : Measurable g)
    (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) {l : ℝ} (hl : 0 ≤ l) :
    ∫ z, exp (-l * pairKernel g z.1 z.2) ∂(ν.prod ν) ≤ exp ((l ^ 2 / 4 - l) * popVar ν g) := by
  have hm := measurable_pairKernel hg
  have hHi : Integrable (fun z : β × β => pairKernel g z.1 z.2) (ν.prod ν) :=
    Integrable.of_mem_Icc 0 (1 / 2) hm.aemeasurable
      (ae_of_all _ fun z => pairKernel_mem hg01 z.1 z.2)
  have hei : Integrable (fun z : β × β => exp (-l * pairKernel g z.1 z.2)) (ν.prod ν) :=
    Integrable.of_mem_Icc 0 1 (measurable_exp.comp (hm.const_mul _)).aemeasurable
      (ae_of_all _ fun z => ⟨(exp_pos _).le, by
        rw [exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hl) (pairKernel_mem hg01 _ _).1⟩)
  calc ∫ z, exp (-l * pairKernel g z.1 z.2) ∂(ν.prod ν)
      ≤ ∫ z, (1 + (l ^ 2 / 4 - l) * pairKernel g z.1 z.2) ∂(ν.prod ν) := by
        refine integral_mono hei ((integrable_const 1).add (hHi.const_mul _)) fun z => ?_
        have hz := pairKernel_mem hg01 z.1 z.2
        have h1 := exp_le_quad_of_nonpos
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hl) hz.1)
        have h2 : (pairKernel g z.1 z.2) ^ 2 ≤ pairKernel g z.1 z.2 / 2 := by
          nlinarith [hz.1, hz.2]
        have h3 : l ^ 2 * (pairKernel g z.1 z.2) ^ 2 ≤ l ^ 2 * (pairKernel g z.1 z.2 / 2) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg l)
        nlinarith [h1, h3]
    _ = 1 + (l ^ 2 / 4 - l) * popVar ν g := by
        have j : Integrable (fun z : β × β => (l ^ 2 / 4 - l) * pairKernel g z.1 z.2) (ν.prod ν) :=
          hHi.const_mul _
        rw [integral_add (integrable_const 1) j, integral_const_mul,
          integral_pairKernel ν hg hg01]
        simp
    _ ≤ exp ((l ^ 2 / 4 - l) * popVar ν g) := by
        linarith [add_one_le_exp ((l ^ 2 / 4 - l) * popVar ν g)]

/-- The pair sum `Σ_{i<k} h(ω(2i), ω(2i+1))`. -/
def pairSum (g : β → ℝ) (k n : ℕ) (hk : 2 * k ≤ n) (ω : Fin n → β) : ℝ :=
  ∑ i : Fin k,
    pairKernel g (ω ⟨2 * i, by have := i.2; omega⟩) (ω ⟨2 * i + 1, by have := i.2; omega⟩)

omit [MeasurableSpace β] in
theorem pairSum_nonneg {g : β → ℝ} (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) (k n : ℕ) (hk : 2 * k ≤ n)
    (ω : Fin n → β) : 0 ≤ pairSum g k n hk ω :=
  Finset.sum_nonneg fun _ _ => (pairKernel_mem hg01 _ _).1

theorem measurable_pairSum {g : β → ℝ} (hg : Measurable g) (k n : ℕ) (hk : 2 * k ≤ n) :
    Measurable (pairSum g k n hk) := by
  unfold pairSum
  refine Finset.measurable_sum _ fun i _ => ?_
  have h1 : Measurable fun ω : Fin n → β => (ω ⟨2 * i, by have := i.2; omega⟩,
      ω ⟨2 * i + 1, by have := i.2; omega⟩) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  exact (measurable_pairKernel hg).comp h1

/-- MGF of the pair sum: `E e^{−λ Σ h} ≤ exp(k (λ²/4 − λ) σ²)`. -/
theorem integral_exp_neg_pairSum_le {g : β → ℝ} (hg : Measurable g)
    (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) {l : ℝ} (hl : 0 ≤ l) (k n : ℕ) (hk : 2 * k ≤ n) :
    ∫ ω, exp (-l * pairSum g k n hk ω) ∂(Measure.pi fun _ : Fin n => ν) ≤
      exp (k * ((l ^ 2 / 4 - l) * popVar ν g)) := by
  have hF : Measurable fun z : β × β => exp (-l * pairKernel g z.1 z.2) :=
    measurable_exp.comp ((measurable_pairKernel hg).const_mul _)
  have hF1 : ∀ x y, |exp (-l * pairKernel g x y)| ≤ 1 := fun x y => by
    rw [abs_of_pos (exp_pos _), exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hl) (pairKernel_mem hg01 _ _).1
  have hpt : ∀ ω : Fin n → β, exp (-l * pairSum g k n hk ω) =
      pairProd (fun x y => exp (-l * pairKernel g x y)) k n hk ω := fun ω => by
    unfold pairSum pairProd
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [hpt]
  rw [integral_pairProd ν hF hF1 k n hk, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (integral_nonneg fun _ => (exp_pos _).le)
    (integral_exp_neg_pairKernel_le ν hg hg01 hl) k

omit [MeasurableSpace β] in
/-- **Hoeffding's representation**: `Σ_σ pairSum(ω ∘ σ) = |Perm| · k · V_n(ω)`. -/
theorem sum_perm_pairSum {n : ℕ} (hn : 2 ≤ n) (g : β → ℝ) (k : ℕ) (hk : 2 * k ≤ n)
    (ω : Fin n → β) :
    ∑ σ : Equiv.Perm (Fin n), pairSum g k n hk (fun i => ω (σ i)) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (k * sampleVar g ω) := by
  set F : Fin n → Fin n → ℝ := fun a b => pairKernel g (ω a) (ω b) with hF
  have hnn : (n : ℝ) * (n - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_ne_zero (by linarith) (by linarith)
  have hperm : ∀ i : Fin k, permSum F ⟨2 * i, by have := i.2; omega⟩
      ⟨2 * i + 1, by have := i.2; omega⟩ =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * offDiagSum F / (n * (n - 1)) := fun i => by
    rw [eq_div_iff hnn, mul_comm, natCast_mul_permSum F]
    intro h
    have := congrArg Fin.val h
    simp at this
  unfold pairSum
  rw [Finset.sum_comm]
  have hrw : ∀ i : Fin k, (∑ σ : Equiv.Perm (Fin n), pairKernel g (ω (σ ⟨2 * i, by
      have := i.2; omega⟩)) (ω (σ ⟨2 * i + 1, by have := i.2; omega⟩))) =
      permSum F ⟨2 * i, by have := i.2; omega⟩ ⟨2 * i + 1, by have := i.2; omega⟩ :=
    fun i => rfl
  simp_rw [hrw, hperm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hoff : offDiagSum F = ∑ a, ∑ b, if a < b then (g (ω a) - g (ω b)) ^ 2 else 0 :=
    offDiagSum_half_sq (fun a => g (ω a))
  rw [hoff, sampleVar]
  ring

/-- **Exponential moment of the sample variance** (lower tail): for `n ≥ 2`, `k = ⌊n/2⌋`,
`λ ≥ 0`: `E e^{−λ k V_n} ≤ exp(k (λ²/4 − λ) σ²)`. -/
theorem integral_exp_neg_sampleVar_le {g : β → ℝ} (hg : Measurable g)
    (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) {n : ℕ} (hn : 2 ≤ n) {l : ℝ} (hl : 0 ≤ l) :
    ∫ ω, exp (-(l * (n / 2 : ℕ)) * sampleVar g ω) ∂(Measure.pi fun _ : Fin n => ν) ≤
      exp ((n / 2 : ℕ) * ((l ^ 2 / 4 - l) * popVar ν g)) := by
  set k := n / 2 with hkdef
  have hk : 2 * k ≤ n := Nat.mul_div_le n 2
  set P := Measure.pi fun _ : Fin n => ν with hP
  set N : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hU0 : ∀ ω, 0 ≤ sampleVar g ω := sampleVar_nonneg (n := n) (by omega) g
  -- Jensen
  have hjensen : ∀ ω : Fin n → β, exp (-(l * k) * sampleVar g ω) ≤
      ∑ σ : Equiv.Perm (Fin n), (1 / N) * exp (-l * pairSum g k n hk (fun i => ω (σ i))) := by
    intro ω
    have hJ := (convexOn_exp).map_sum_le (t := Finset.univ)
      (w := fun _ : Equiv.Perm (Fin n) => 1 / N)
      (p := fun σ => -l * pairSum g k n hk (fun i => ω (σ i)))
      (fun _ _ => by positivity) (by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN]; field_simp)
      (fun _ _ => mem_univ _)
    simp only [smul_eq_mul] at hJ
    refine le_trans (le_of_eq ?_) hJ
    congr 1
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_perm_pairSum hn g k hk ω, ← hN]
    field_simp
  have hint : ∀ σ : Equiv.Perm (Fin n),
      Integrable (fun ω : Fin n → β => exp (-l * pairSum g k n hk (fun i => ω (σ i)))) P :=
    fun σ => by
      refine Integrable.of_mem_Icc 0 1 ?_ (ae_of_all _ fun ω => ⟨(exp_pos _).le, ?_⟩)
      · exact (measurable_exp.comp (((measurable_pairSum hg k n hk).comp
          (measurable_pi_iff.mpr fun i => measurable_pi_apply (σ i))).const_mul _)).aemeasurable
      · rw [exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hl) (pairSum_nonneg hg01 k n hk _)
  have hintU : Integrable (fun ω : Fin n → β => exp (-(l * k) * sampleVar g ω)) P := by
    refine Integrable.of_mem_Icc 0 1
      (measurable_exp.comp ((measurable_sampleVar hg).const_mul _)).aemeasurable
      (ae_of_all _ fun ω => ⟨(exp_pos _).le, ?_⟩)
    rw [exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (hU0 ω)
  calc ∫ ω, exp (-(l * k) * sampleVar g ω) ∂P
      ≤ ∫ ω, ∑ σ : Equiv.Perm (Fin n),
          (1 / N) * exp (-l * pairSum g k n hk (fun i => ω (σ i))) ∂P :=
        integral_mono hintU (integrable_finsetSum _ fun σ _ => (hint σ).const_mul _) hjensen
    _ = ∑ σ : Equiv.Perm (Fin n), (1 / N) * ∫ ω, exp (-l * pairSum g k n hk ω) ∂P := by
        rw [integral_finsetSum _ fun σ _ => (hint σ).const_mul _]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [integral_const_mul]
        congr 1
        exact integral_comp_perm ν σ (fun ω => exp (-l * pairSum g k n hk ω))
    _ = ∫ ω, exp (-l * pairSum g k n hk ω) ∂P := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN, ← mul_assoc]
        field_simp
    _ ≤ _ := integral_exp_neg_pairSum_le ν hg hg01 hl k n hk

/-- **Concentration of the sample standard deviation** with the block constant `k = ⌊n/2⌋`:
`P(√V_n + √(log(1/δ)/k) ≤ σ) ≤ δ` for `n ≥ 2`, `0 < δ ≤ 1`. -/
theorem sqrt_popVar_le_of_pairs {g : β → ℝ} (hg : Measurable g)
    (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ : Fin n => ν).real
      {ω | √(sampleVar g ω) + √(log (1 / δ) / (n / 2 : ℕ)) ≤ √(popVar ν g)} ≤ δ := by
  set P := Measure.pi fun _ : Fin n => ν with hP
  set k := n / 2 with hkdef
  have hk1 : 1 ≤ k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  set L := log (1 / δ) with hL
  set σ2 := popVar ν g with hσ2
  set σ := √σ2 with hσ
  set r := √(L / k) with hr
  have hσ0 : 0 ≤ σ2 := popVar_nonneg ν g
  rcases hδ1.eq_or_lt with h1 | h1
  · rw [h1]
    exact (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  have hLpos : 0 < L := by
    rw [hL]; exact log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hrpos : 0 < r := Real.sqrt_pos.2 (div_pos hLpos hkR)
  have hexpL : exp (-L) = δ := by
    rw [hL, log_div one_ne_zero hδ0.ne', log_one, zero_sub, neg_neg, exp_log hδ0]
  rcases hσ0.eq_or_lt with h0 | hpos
  · -- zero variance: the event is empty
    have hempty : {ω : Fin n → β | √(sampleVar g ω) + r ≤ σ} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      rw [hσ, ← h0, Real.sqrt_zero]
      exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hrpos
    rw [hempty]
    simp [hδ0.le]
  -- positive variance: Chernoff on `−V_n`
  have hσpos : 0 < σ := Real.sqrt_pos.2 hpos
  have hσsq : σ ^ 2 = σ2 := Real.sq_sqrt hσ0
  set l := 2 * r / σ with hl
  have hl0 : 0 ≤ l := by positivity
  have hsub : {ω : Fin n → β | √(sampleVar g ω) + r ≤ σ} ⊆
      {ω | r * σ - σ2 ≤ -sampleVar g ω} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have hU0 := sampleVar_nonneg (by omega) g ω
    have hs := Real.sq_sqrt hU0
    have h1 : √(sampleVar g ω) ≤ σ - r := by linarith
    have h2 : sampleVar g ω ≤ (σ - r) ^ 2 := by
      rw [← hs]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    nlinarith [h2, hσsq, Real.sqrt_nonneg (sampleVar g ω)]
  have hint : Integrable (fun ω : Fin n → β => exp ((l * k) * -sampleVar g ω)) P := by
    refine Integrable.of_mem_Icc 0 1
      (measurable_exp.comp ((measurable_sampleVar hg).neg.const_mul _)).aemeasurable
      (ae_of_all _ fun ω => ⟨(exp_pos _).le, ?_⟩)
    rw [exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (neg_nonpos.2 (sampleVar_nonneg (by omega) g ω))
  have hch := measure_ge_le_exp_mul_mgf (μ := P) (X := fun ω => -sampleVar g ω) (r * σ - σ2)
    (by positivity : 0 ≤ l * k) hint
  have hmgf : mgf (fun ω => -sampleVar g ω) P (l * k) ≤ exp (k * ((l ^ 2 / 4 - l) * σ2)) := by
    rw [mgf]
    have := integral_exp_neg_sampleVar_le ν hg hg01 hn hl0
    rw [← hkdef] at this
    refine le_trans (le_of_eq ?_) this
    congr 1; ext ω; ring_nf
  refine (measureReal_mono hsub).trans (hch.trans ?_)
  calc exp (-(l * k) * (r * σ - σ2)) * mgf (fun ω => -sampleVar g ω) P (l * k)
      ≤ exp (-(l * k) * (r * σ - σ2)) * exp (k * ((l ^ 2 / 4 - l) * σ2)) := by gcongr
    _ = exp (-(l * k) * (r * σ - σ2) + k * ((l ^ 2 / 4 - l) * σ2)) := by rw [Real.exp_add]
    _ = δ := by
        rw [← hexpL]
        congr 1
        have hr2 : r ^ 2 = L / k := Real.sq_sqrt (div_nonneg hLpos.le hkR.le)
        have e1 : l * σ = 2 * r := by rw [hl]; field_simp
        have e2 : -(l * k) * (r * σ - σ2) + k * ((l ^ 2 / 4 - l) * σ2) =
            -(k * ((l * σ) * r)) + k * (l * σ) ^ 2 / 4 := by rw [← hσsq]; ring
        rw [e2, e1]
        have e3 : -(k * (2 * r * r)) + k * (2 * r) ^ 2 / 4 = -(k * r ^ 2) := by ring
        rw [e3, hr2]
        field_simp

/-- **Maurer–Pontil 2009, Thm 10**: for `n ≥ 2` and `0 < δ ≤ 1`,
`P(√V_n + √(2 log(1/δ)/(n−1)) ≤ σ) ≤ δ`, i.e. with probability at least `1 − δ`,
`σ < √V_n + √(2 log(1/δ)/(n−1))`. -/
theorem sqrt_popVar_le {g : β → ℝ} (hg : Measurable g) (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ : Fin n => ν).real
      {ω | √(sampleVar g ω) + √(2 * log (1 / δ) / (n - 1)) ≤ √(popVar ν g)} ≤ δ := by
  refine (measureReal_mono fun ω hω => ?_).trans (sqrt_popVar_le_of_pairs ν hg hg01 hn hδ0 hδ1)
  simp only [mem_ofPred_eq] at hω ⊢
  refine le_trans (add_le_add le_rfl (Real.sqrt_le_sqrt ?_)) hω
  have hL : 0 ≤ log (1 / δ) := log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hk : ((n : ℝ) - 1) / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
    have h := Nat.lt_mul_div_succ n (by norm_num : 0 < 2)
    have : (n : ℝ) < 2 * ((n / 2 : ℕ) : ℝ) + 2 := by exact_mod_cast (by omega : n < 2 * (n / 2) + 2)
    have h2 : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (by omega : n ≤ 2 * (n / 2) + 1)
    linarith
  have hn1 : (0 : ℝ) < n - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hkpos : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n / 2)
  rw [div_le_div_iff₀ hkpos hn1]
  nlinarith [hk, hL]

end StatFormal.Bernstein
