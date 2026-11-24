import StatFormal.Archive.Wave11b.Statements
import StatFormal.Archive.Wave11b.RouteSwor
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Order.Compact

/-!
# Route: ICL `lem:cond-nonunique` (the faithful two-cell route)

Witness: `𝒳 = [0,1]`, `𝒴 = {0,1} ⊂ ℝ`, so `𝒵 = 𝒳 × 𝒴` is two disjoint intervals; `P₀ = Leb ⊗ Unif{0,1}` (atomless),
`P_{Y|x} = Unif{0,1}`; `ψ(z) = −1` on the cell `{y = 0}`, `+1` on `{y = 1}` (continuous: the cells are clopen);
`L(z; t) = b(C − e₂(ψ(t₁),…,ψ(t_M)))`, `C = binom(M,2)`, `b = B_L/(C + ⌊M/2⌋)`, independent of the query.
1. `μ ≪ P₀` ⇒ `μ` atomless ⇒ `μ^{⊗M}(D_M) = 1`, `Π_μ = μ^{⊗M}`, and `Ḡ_μ = bC(1 − m_μ²)`, `m_μ = ∫ψ dμ = 1 − 2q`,
   `q = μ(y = 0)` (Fubini over the product: `E[ψ(t_k)ψ(t_l)] = m²` for `k ≠ l`).
2. Data processing along `z ↦ y`: `KL(μ | P₀) ≥ KL(Bern(q) | Bern(½)) = h(q)`, with equality for the measure
   `μ_q` of constant density on each cell. So `φ_λ(x, μ) ≥ F(q_μ) = φ_λ(x, μ_q)`,
   `F(q) = bC(1 − (1−2q)²) + λ h(q)`, an exact symmetric double well on `[0,1]`.
3. `F` is continuous, `F(1−q) = F(q)`, and `F(½ + x/2) ≤ bC − x²(bC − λ/2 − 2λx) < F(½)` for small `x > 0`
   (`log(1±x) ≤ ±x − x²/2 + 2x³`, `Real.abs_log_sub_add_sum_range_le`), because `λ < κ'_M B_L = 2bC`.
   A minimiser `q*` exists and `q* ≠ ½`, so `μ_{q*} ≠ μ_{1−q*}` both minimise; constant policies.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave11b

namespace NU

/-! ### The real double well -/

/-- `h(q) = q log 2q + (1−q) log 2(1−q) = KL(Bern(q) | Bern(½))`. -/
def hq (q : ℝ) : ℝ := q * Real.log (2 * q) + (1 - q) * Real.log (2 * (1 - q))

lemma mul_log_two_mul (q : ℝ) : q * Real.log (2 * q) = q * Real.log 2 - Real.negMulLog q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · rw [Real.log_mul two_ne_zero hq, Real.negMulLog]; ring

lemma hq_eq (q : ℝ) : hq q = Real.log 2 - Real.negMulLog q - Real.negMulLog (1 - q) := by
  unfold hq; rw [mul_log_two_mul, mul_log_two_mul]; ring

lemma continuous_hq : Continuous hq := by
  have : hq = fun q => Real.log 2 - Real.negMulLog q - Real.negMulLog (1 - q) := funext hq_eq
  rw [this]
  exact (continuous_const.sub Real.continuous_negMulLog).sub
    (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id))

lemma hq_symm (q : ℝ) : hq (1 - q) = hq q := by unfold hq; rw [sub_sub_cancel]; ring

lemma hq_half : hq (1 / 2) = 0 := by unfold hq; norm_num

/-- `F(q) = bC(1 − (1−2q)²) + λ h(q)`. -/
def Fw (bC lam q : ℝ) : ℝ := bC * (1 - (1 - 2 * q) ^ 2) + lam * hq q

lemma Fw_symm (bC lam q : ℝ) : Fw bC lam (1 - q) = Fw bC lam q := by
  unfold Fw; rw [hq_symm]; ring

lemma log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.log (1 - x) ≤ -x - x ^ 2 / 2 + 2 * x ^ 3 := by
  have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_of_nonneg hx0] at h
  have h2 : x ^ (2 + 1) / (1 - x) ≤ 2 * x ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ x ^ 3 := by positivity
    have e : x ^ (2 + 1) = x ^ 3 := by norm_num
    rw [e]
    nlinarith [mul_nonneg this (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]
  have := (abs_le.1 h).2
  norm_num at this
  linarith

lemma log_one_add_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + 2 * x ^ 3 := by
  have habs : |-x| < 1 := by rw [abs_neg, abs_of_nonneg hx0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_neg, abs_of_nonneg hx0, sub_neg_eq_add] at h
  have h2 : x ^ (2 + 1) / (1 - x) ≤ 2 * x ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ x ^ 3 := by positivity
    have e : x ^ (2 + 1) = x ^ 3 := by norm_num
    rw [e]
    nlinarith [mul_nonneg this (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]
  have := (abs_le.1 h).2
  norm_num at this
  nlinarith

lemma hq_near_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    hq (1 / 2 + x / 2) ≤ (x ^ 2 + 4 * x ^ 3) / 2 := by
  unfold hq
  have e1 : 2 * (1 / 2 + x / 2) = 1 + x := by ring
  have e2 : 2 * (1 - (1 / 2 + x / 2)) = 1 - x := by ring
  rw [e1, e2]
  have h1 := log_one_add_le hx0 hx1
  have h2 := log_one_sub_le hx0 hx1
  have a1 : (1 / 2 + x / 2) * Real.log (1 + x) ≤ (1 / 2 + x / 2) * (x - x ^ 2 / 2 + 2 * x ^ 3) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have a2 : (1 - (1 / 2 + x / 2)) * Real.log (1 - x) ≤
      (1 - (1 / 2 + x / 2)) * (-x - x ^ 2 / 2 + 2 * x ^ 3) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  nlinarith

/-- The double well: if `λ < 2bC` there is a minimiser of `F` on `[0,1]` other than `½`. -/
lemma exists_min_ne_half {bC lam : ℝ} (hlam : 0 < lam) (hb : lam < 2 * bC) :
    ∃ q ∈ Icc (0 : ℝ) 1, q ≠ 1 / 2 ∧ ∀ q' ∈ Icc (0 : ℝ) 1, Fw bC lam q ≤ Fw bC lam q' := by
  have hcont : ContinuousOn (Fw bC lam) (Icc 0 1) := by
    unfold Fw
    exact (Continuous.continuousOn (by fun_prop : Continuous fun q : ℝ => bC * (1 - (1 - 2 * q) ^ 2)) ).add
      ((continuous_const.mul continuous_hq).continuousOn)
  obtain ⟨q, hqI, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hcont
  refine ⟨q, hqI, ?_, fun q' hq' => hmin hq'⟩
  rintro rfl
  set x : ℝ := min (1 / 2) ((bC - lam / 2) / (4 * lam)) with hxdef
  have hpos : 0 < bC - lam / 2 := by linarith
  have hx0 : 0 < x := lt_min (by norm_num) (div_pos hpos (by positivity))
  have hx1 : x ≤ 1 / 2 := min_le_left _ _
  have hx2 : x ≤ (bC - lam / 2) / (4 * lam) := min_le_right _ _
  have hlx : 2 * lam * x ≤ (bC - lam / 2) / 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * lam)] at hx2
    nlinarith
  have hmem : 1 / 2 + x / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hle : Fw bC lam (1 / 2) ≤ Fw bC lam (1 / 2 + x / 2) := hmin hmem
  have hF : Fw bC lam (1 / 2 + x / 2) < Fw bC lam (1 / 2) := by
    unfold Fw
    rw [hq_half]
    have hh := hq_near_half hx0.le hx1
    have e : (1 - 2 * (1 / 2 + x / 2)) ^ 2 = x ^ 2 := by ring
    rw [e]
    have hx3 : 0 < x ^ 2 := by positivity
    have : lam * hq (1 / 2 + x / 2) ≤ lam * ((x ^ 2 + 4 * x ^ 3) / 2) :=
      mul_le_mul_of_nonneg_left hh hlam.le
    nlinarith
  exact absurd hle (not_le.2 hF)

/-! ### The witness -/

/-- The two-point label space `{0, 1} ⊂ ℝ`. -/
abbrev T2 : Type := ↥({0, 1} : Set ℝ)

def t0 : T2 := ⟨0, by simp⟩
def t1 : T2 := ⟨1, by simp⟩

lemma t0_ne_t1 : t0 ≠ t1 := by
  intro h; have := congrArg Subtype.val h; simp [t0, t1] at this

lemma t1_ne_t0 : t1 ≠ t0 := t0_ne_t1.symm

lemma T2_cases (y : T2) : y = t0 ∨ y = t1 := by
  obtain ⟨v, hv⟩ := y
  simp only [mem_insert_iff, mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · left; rfl
  · right; rfl

abbrev ZW : Type := unitInterval × T2

/-- `Unif{0,1}`. -/
def nu2 : Measure T2 := (2⁻¹ : ℝ≥0∞) • (Measure.dirac t0 + Measure.dirac t1)

lemma nu2_t0 : nu2 {t0} = 2⁻¹ := by
  simp [nu2, Set.indicator, t1_ne_t0]

lemma nu2_t1 : nu2 {t1} = 2⁻¹ := by
  simp [nu2, Set.indicator, t0_ne_t1]

instance : IsProbabilityMeasure nu2 :=
  ⟨by simp [nu2]; exact ENNReal.inv_two_add_inv_two⟩

lemma integral_nu2 (f : T2 → ℝ) : ∫ y, f y ∂nu2 = (f t0 + f t1) / 2 := by
  rw [nu2, integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, integral_dirac]
  simp; ring

/-- `P₀ = Leb ⊗ Unif{0,1}` on `𝒵 = [0,1] × {0,1}`. -/
def P0w : Measure ZW := (volume : Measure unitInterval).prod nu2

instance : IsProbabilityMeasure P0w := by unfold P0w; infer_instance

lemma P0w_atomless (z : ZW) : P0w {z} = 0 := by
  rw [P0w, ← Set.singleton_prod_singleton, Measure.prod_prod]
  simp

lemma P0w_fst : P0w.fst = volume := by
  rw [P0w, Measure.fst, Measure.map_fst_prod]; simp

lemma P0w_snd : P0w.map Prod.snd = nu2 := by
  rw [P0w, Measure.map_snd_prod]; simp

/-- `P_{Y|x} = Unif{0,1}` for every `x`. -/
def kw : Kernel unitInterval T2 := Kernel.const _ nu2

instance : IsMarkovKernel kw := by unfold kw; infer_instance

lemma P0w_disint : P0w = P0w.fst ⊗ₘ kw := by
  rw [P0w_fst, kw, Measure.compProd_const]; rfl

/-- `ψ = −1` on the cell `{y = 0}`, `+1` on `{y = 1}`. -/
def psi (z : ZW) : ℝ := if z.2 = t0 then -1 else 1

lemma continuous_psi : Continuous psi :=
  (continuous_of_discreteTopology (f := fun y : T2 => if y = t0 then (-1 : ℝ) else 1)).comp
    continuous_snd

lemma measurable_psi : Measurable psi := continuous_psi.measurable

lemma psi_sq (z : ZW) : psi z ^ 2 = 1 := by unfold psi; split_ifs <;> norm_num

lemma abs_psi (z : ZW) : |psi z| = 1 := by unfold psi; split_ifs <;> norm_num

/-- `e₂(v) = Σ_{k<l} v_k v_l = ((Σ v)² − Σ v²)/2`. -/
def e2 {M : ℕ} (v : Fin M → ℝ) : ℝ := ((∑ k, v k) ^ 2 - ∑ k, v k ^ 2) / 2

/-- `b = B_L / (binom(M,2) + ⌊M/2⌋)`. -/
def bco (M : ℕ) (BL : ℝ) : ℝ := BL / ((M.choose 2 : ℝ) + ((M / 2 : ℕ) : ℝ))

/-- `L(z; t) = b(C − e₂(ψ(t₁), …, ψ(t_M)))`. -/
def Lw (M : ℕ) (BL : ℝ) (_z : ZW) (t : Fin M → ZW) : ℝ :=
  bco M BL * ((M.choose 2 : ℝ) - e2 (fun k => psi (t k)))

lemma continuous_Lw (M : ℕ) (BL : ℝ) :
    Continuous (fun p : ZW × (Fin M → ZW) => Lw M BL p.1 p.2) := by
  unfold Lw e2
  have h : ∀ k : Fin M, Continuous fun p : ZW × (Fin M → ZW) => psi (p.2 k) :=
    fun k => continuous_psi.comp ((continuous_apply k).comp continuous_snd)
  fun_prop

lemma Lw_symm (M : ℕ) (BL : ℝ) (z : ZW) (t : Fin M → ZW) (σ : Equiv.Perm (Fin M)) :
    Lw M BL z (t ∘ σ) = Lw M BL z t := by
  unfold Lw e2
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp σ (fun k => psi (t k)), Equiv.sum_comp σ (fun k => psi (t k) ^ 2)]

lemma two_choose (M : ℕ) : 2 * (M.choose 2 : ℝ) = M * ((M : ℝ) - 1) := by
  rw [Nat.cast_choose_two]; ring

lemma e2_bounds {M : ℕ} (t : Fin M → ZW) :
    -((M / 2 : ℕ) : ℝ) ≤ e2 (fun k => psi (t k)) ∧ e2 (fun k => psi (t k)) ≤ M.choose 2 := by
  classical
  have hsq : ∑ k, psi (t k) ^ 2 = M := by simp [psi_sq]
  -- `Σ ψ = 2a − M`, `a = #{ψ = 1}`
  set a := (Finset.univ.filter fun k => (t k).2 ≠ t0).card with ha
  have hsum : ∑ k, psi (t k) = 2 * (a : ℝ) - M := by
    have : ∀ k, psi (t k) = 2 * (if (t k).2 ≠ t0 then (1 : ℝ) else 0) - 1 := by
      intro k; unfold psi; by_cases h : (t k).2 = t0 <;> simp [h]; norm_num
    simp_rw [this]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp [ha]
  have haM : a ≤ M := by
    calc a ≤ (Finset.univ : Finset (Fin M)).card := Finset.card_filter_le _ _
      _ = M := by simp
  unfold e2
  rw [hsq, hsum]
  constructor
  · -- `(2a − M)² ≥ M mod 2`
    have hdm := Nat.div_add_mod M 2
    have hmod : ((M % 2 : ℕ) : ℤ) ≤ (2 * (a : ℤ) - (M : ℤ)) ^ 2 := by
      rcases Nat.mod_two_eq_zero_or_one M with h | h
      · rw [h]; push_cast; positivity
      · rw [h]
        have hne : (2 * (a : ℤ) - M) ≠ 0 := by omega
        have : 1 ≤ |2 * (a : ℤ) - M| := Int.one_le_abs hne
        push_cast
        nlinarith [sq_abs (2 * (a : ℤ) - M)]
    have hmodR : ((M % 2 : ℕ) : ℝ) ≤ (2 * (a : ℝ) - M) ^ 2 := by
      have h := (Int.cast_le (R := ℝ)).2 hmod
      push_cast at h
      exact h
    have hdmR : (2 : ℝ) * ((M / 2 : ℕ) : ℝ) + ((M % 2 : ℕ) : ℝ) = M := by exact_mod_cast hdm
    linarith
  · have h1 : (2 * (a : ℝ) - M) ^ 2 ≤ (M : ℝ) ^ 2 := by
      have : (a : ℝ) ≤ M := by exact_mod_cast haM
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg _
      nlinarith
    have := two_choose M
    linarith

lemma Lw_bounds {M : ℕ} {BL : ℝ} (hM : 2 ≤ M) (hBL : 0 ≤ BL) (z : ZW) (t : Fin M → ZW) :
    0 ≤ Lw M BL z t ∧ Lw M BL z t ≤ BL := by
  have hC : (1 : ℝ) ≤ M.choose 2 := by
    have : 1 ≤ M.choose 2 := Nat.choose_pos hM
    exact_mod_cast this
  have hden : 0 < (M.choose 2 : ℝ) + ((M / 2 : ℕ) : ℝ) := by positivity
  have hb : 0 ≤ bco M BL := div_nonneg hBL hden.le
  obtain ⟨h1, h2⟩ := e2_bounds t
  unfold Lw
  refine ⟨mul_nonneg hb (by linarith), ?_⟩
  calc bco M BL * ((M.choose 2 : ℝ) - e2 (fun k => psi (t k)))
      ≤ bco M BL * ((M.choose 2 : ℝ) + ((M / 2 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hb
    _ = BL := by unfold bco; field_simp

/-! ### Product of an atomless law: distinct coordinates, `Π_μ = μ^{⊗M}` -/

lemma pi_pair_map (μ : Measure ZW) [IsProbabilityMeasure μ] {M : ℕ} {k l : Fin M} (hkl : k ≠ l) :
    (Measure.pi fun _ : Fin M => μ).map (fun t => (t k, t l)) = μ.prod μ := by
  classical
  have hm : Measurable fun t : Fin M → ZW => (t k, t l) :=
    (measurable_pi_apply k).prodMk (measurable_pi_apply l)
  refine (Measure.prod_eq fun s u hs hu => ?_).symm
  rw [Measure.map_apply hm (hs.prod hu)]
  have hset : (fun t : Fin M → ZW => (t k, t l)) ⁻¹' (s ×ˢ u) =
      Set.pi univ (fun i => if i = k then s else if i = l then u else univ) := by
    ext t
    simp only [mem_preimage, mem_prod, Set.mem_pi, mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ i
      by_cases hik : i = k
      · subst hik; simpa using h1
      · by_cases hil : i = l
        · subst hil; simpa [hik] using h2
        · simp [hik, hil]
    · intro h
      exact ⟨by simpa using h k, by simpa [Ne.symm hkl] using h l⟩
  rw [hset, Measure.pi_pi, prod_two _ hkl]
  have hr : ∏ i ∈ (Finset.univ.erase k).erase l,
      μ (if i = k then s else if i = l then u else univ) = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    have hik : i ≠ k := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hil : i ≠ l := Finset.ne_of_mem_erase hi
    simp [hik, hil]
  rw [hr, mul_one]
  simp [Ne.symm hkl]

/-- The set `{t : t_k = t_l}` for `k ≠ l` (empty for `k = l`). -/
def collSet {M : ℕ} (k l : Fin M) : Set (Fin M → ZW) := {t | k ≠ l ∧ t k = t l}

lemma measurableSet_collSet {M : ℕ} (k l : Fin M) : MeasurableSet (collSet k l) := by
  by_cases hkl : k = l
  · have : collSet k l = ∅ := by ext t; simp [collSet, hkl]
    rw [this]; exact MeasurableSet.empty
  · have : collSet k l = (fun t : Fin M → ZW => (t k, t l)) ⁻¹' Set.diagonal ZW := by
      ext t; simp [collSet, hkl]
    rw [this]
    exact ((measurable_pi_apply k).prodMk (measurable_pi_apply l)) measurableSet_diagonal

lemma distinctSet_compl {M : ℕ} : (distinctSet M : Set (Fin M → ZW))ᶜ = ⋃ k, ⋃ l, collSet k l := by
  ext t
  simp only [distinctSet, mem_compl_iff, mem_setOf_eq, Function.Injective, not_forall, mem_iUnion,
    collSet]
  constructor
  · rintro ⟨k, l, h1, h2⟩; exact ⟨k, l, h2, h1⟩
  · rintro ⟨k, l, h1, h2⟩; exact ⟨k, l, h2, h1⟩

lemma measurableSet_distinctSet {M : ℕ} : MeasurableSet (distinctSet M : Set (Fin M → ZW)) := by
  rw [← compl_compl (distinctSet M), distinctSet_compl]
  exact (MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l => measurableSet_collSet k l).compl

lemma pi_distinct_compl (μ : Measure ZW) [IsProbabilityMeasure μ] (hμ : ∀ z, μ {z} = 0) {M : ℕ} :
    Measure.pi (fun _ : Fin M => μ) (distinctSet M)ᶜ = 0 := by
  rw [distinctSet_compl]
  refine measure_iUnion_null fun k => measure_iUnion_null fun l => ?_
  by_cases hkl : k = l
  · have : collSet k l = ∅ := by ext t; simp [collSet, hkl]
    rw [this, measure_empty]
  · have hm : Measurable fun t : Fin M → ZW => (t k, t l) :=
      (measurable_pi_apply k).prodMk (measurable_pi_apply l)
    have : collSet k l = (fun t : Fin M → ZW => (t k, t l)) ⁻¹' Set.diagonal ZW := by
      ext t; simp [collSet, hkl]
    rw [this, ← Measure.map_apply hm measurableSet_diagonal, pi_pair_map μ hkl,
      Measure.prod_apply measurableSet_diagonal]
    have : ∀ x : ZW, Prod.mk x ⁻¹' Set.diagonal ZW = {x} := by
      intro x; ext y; simp [eq_comm]
    simp_rw [this, hμ, lintegral_zero]

lemma pi_distinct (μ : Measure ZW) [IsProbabilityMeasure μ] (hμ : ∀ z, μ {z} = 0) {M : ℕ} :
    Measure.pi (fun _ : Fin M => μ) (distinctSet M) = 1 := by
  rw [← prob_compl_eq_zero_iff measurableSet_distinctSet]
  exact pi_distinct_compl μ hμ

lemma ctxLaw_eq (μ : Measure ZW) [IsProbabilityMeasure μ] (hμ : ∀ z, μ {z} = 0) {M : ℕ} :
    ctxLaw μ M = Measure.pi fun _ : Fin M => μ := by
  unfold ctxLaw
  rw [ProbabilityTheory.cond, pi_distinct μ hμ, inv_one, one_smul]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  exact (measure_eq_zero_iff_ae_notMem.mp (pi_distinct_compl μ hμ (M := M))).mono
    fun t ht => by simpa using ht

/-! ### The conditional risk of an atomless law -/

lemma integral_pair (μ : Measure ZW) [IsProbabilityMeasure μ] {M : ℕ} (k l : Fin M) :
    ∫ t, psi (t k) * psi (t l) ∂(Measure.pi fun _ : Fin M => μ) =
      if k = l then 1 else (∫ z, psi z ∂μ) ^ 2 := by
  classical
  by_cases hkl : k = l
  · subst hkl
    simp only [ite_true, ← sq, psi_sq, integral_const, probReal_univ, smul_eq_mul, one_pow]
  · rw [if_neg hkl]
    have h := integral_fintype_prod_eq_prod (𝕜 := ℝ) (E := fun _ : Fin M => ZW)
      (μ := fun _ => μ) (fun i z => if i = k ∨ i = l then psi z else 1)
    have hl : ∀ t : Fin M → ZW, ∏ i, (if i = k ∨ i = l then psi (t i) else 1) =
        psi (t k) * psi (t l) := by
      intro t
      rw [prod_two _ hkl]
      have : ∏ i ∈ (Finset.univ.erase k).erase l, (if i = k ∨ i = l then psi (t i) else 1) = 1 := by
        refine Finset.prod_eq_one fun i hi => ?_
        have hik : i ≠ k := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
        have hil : i ≠ l := Finset.ne_of_mem_erase hi
        simp [hik, hil]
      rw [this]; simp
    have hr : ∏ i : Fin M, ∫ z, (if i = k ∨ i = l then psi z else 1) ∂μ = (∫ z, psi z ∂μ) ^ 2 := by
      rw [prod_two _ hkl]
      have : ∏ i ∈ (Finset.univ.erase k).erase l, ∫ z, (if i = k ∨ i = l then psi z else 1) ∂μ = 1 := by
        refine Finset.prod_eq_one fun i hi => ?_
        have hik : i ≠ k := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
        have hil : i ≠ l := Finset.ne_of_mem_erase hi
        simp [hik, hil]
      rw [this]; simp; ring
    simp_rw [hl] at h
    rw [h, hr]

lemma integrable_psi_prod (μ : Measure ZW) [IsProbabilityMeasure μ] {M : ℕ} (k l : Fin M) :
    Integrable (fun t : Fin M → ZW => psi (t k) * psi (t l)) (Measure.pi fun _ : Fin M => μ) := by
  refine Integrable.of_mem_Icc (-1) 1
    ((measurable_psi.comp (measurable_pi_apply k)).mul
      (measurable_psi.comp (measurable_pi_apply l))).aemeasurable (ae_of_all _ fun t => ?_)
  have h := abs_mul (psi (t k)) (psi (t l))
  rw [abs_psi, abs_psi, one_mul] at h
  exact abs_le.1 h.le

lemma integral_e2 (μ : Measure ZW) [IsProbabilityMeasure μ] {M : ℕ} :
    ∫ t, e2 (fun k => psi (t k)) ∂(Measure.pi fun _ : Fin M => μ) =
      (M.choose 2 : ℝ) * (∫ z, psi z ∂μ) ^ 2 := by
  classical
  set m := ∫ z, psi z ∂μ
  have hpt : ∀ t : Fin M → ZW, e2 (fun k => psi (t k)) =
      (∑ k, ∑ l, psi (t k) * psi (t l) - M) / 2 := by
    intro t
    unfold e2
    rw [sq, Finset.sum_mul_sum]
    simp [psi_sq]
  simp_rw [hpt]
  rw [integral_div, integral_sub (integrable_finsetSum _ fun k _ => integrable_finsetSum _
      fun l _ => integrable_psi_prod μ k l) (integrable_const _),
    integral_finset_sum _ fun k _ => integrable_finsetSum _ fun l _ => integrable_psi_prod μ k l]
  simp_rw [integral_finset_sum _ fun l _ => integrable_psi_prod μ _ l, integral_pair]
  have hs : ∑ k : Fin M, ∑ l : Fin M, (if k = l then (1 : ℝ) else m ^ 2) = M + (M * M - M) * m ^ 2 := by
    have : ∀ k : Fin M, ∑ l : Fin M, (if k = l then (1 : ℝ) else m ^ 2) = 1 + (M - 1) * m ^ 2 := by
      intro k
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), if_pos rfl,
        Finset.sum_congr rfl (fun l hl => if_neg (Ne.symm (Finset.ne_of_mem_erase hl))),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos M with h0 | hpos
      · exact absurd k.2 (by omega)
      · rw [Nat.cast_sub hpos]; push_cast; ring
    rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [hs, integral_const, probReal_univ, one_smul, Nat.cast_choose_two]
  ring

lemma integral_psi (μ : Measure ZW) [IsProbabilityMeasure μ] :
    ∫ z, psi z ∂μ = 1 - 2 * μ.real (Prod.snd ⁻¹' {t0}) := by
  have hA : MeasurableSet (Prod.snd ⁻¹' {t0} : Set ZW) := measurable_snd (measurableSet_singleton _)
  have : psi = fun z => 1 - 2 * (Prod.snd ⁻¹' {t0} : Set ZW).indicator (fun _ => (1 : ℝ)) z := by
    funext z; unfold psi
    by_cases h : z.2 = t0 <;> simp [h, Set.indicator]; norm_num
  rw [this, integral_sub (integrable_const _) ((integrable_const _).indicator hA |>.const_mul 2),
    integral_const_mul, integral_indicator_const (1 : ℝ) hA]
  simp

lemma condRisk_eq {M : ℕ} {BL : ℝ} (hM : 2 ≤ M) (hBL : 0 ≤ BL) (μ : Measure ZW)
    [IsProbabilityMeasure μ] (hμ : ∀ z, μ {z} = 0) (x : unitInterval) :
    condRisk kw (Lw M BL) μ x =
      ENNReal.ofReal (bco M BL * (M.choose 2 : ℝ) * (1 - (∫ z, psi z ∂μ) ^ 2)) := by
  unfold condRisk
  rw [ctxLaw_eq μ hμ]
  have hin : ∀ t : Fin M → ZW, ∫⁻ y, ENNReal.ofReal (Lw M BL (x, y) t) ∂(kw x) =
      ENNReal.ofReal (Lw M BL (x, t0) t) := by
    intro t
    simp only [Lw, kw, Kernel.const_apply, lintegral_const, measure_univ, mul_one]
  simp_rw [hin]
  have hmeas : Measurable fun t : Fin M → ZW => Lw M BL (x, t0) t :=
    ((continuous_Lw M BL).comp (Continuous.prodMk
      (continuous_const : Continuous fun _ : Fin M → ZW => ((x, t0) : ZW)) continuous_id)).measurable
  have hint : Integrable (fun t : Fin M → ZW => Lw M BL (x, t0) t) (Measure.pi fun _ : Fin M => μ) :=
    Integrable.of_mem_Icc 0 BL hmeas.aemeasurable
      (ae_of_all _ fun t => ⟨(Lw_bounds hM hBL _ t).1, (Lw_bounds hM hBL _ t).2⟩)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => (Lw_bounds hM hBL _ t).1)]
  congr 1
  have hint2 : Integrable (fun t : Fin M → ZW => e2 (fun k => psi (t k)))
      (Measure.pi fun _ : Fin M => μ) := by
    have hc : Continuous fun t : Fin M → ZW => e2 (fun k => psi (t k)) := by
      unfold e2
      have h : ∀ k : Fin M, Continuous fun t : Fin M → ZW => psi (t k) :=
        fun k => continuous_psi.comp (continuous_apply k)
      fun_prop
    exact Integrable.of_mem_Icc (-((M / 2 : ℕ) : ℝ)) (M.choose 2 : ℝ) hc.measurable.aemeasurable
      (ae_of_all _ fun t => ⟨(e2_bounds t).1, (e2_bounds t).2⟩)
  simp only [Lw]
  rw [integral_const_mul, integral_sub (integrable_const _) hint2, integral_e2, integral_const,
    probReal_univ, one_smul]
  ring

/-! ### Relative entropy: the two-cell reduction -/

/-- The cell-constant density `d_q = 2q` on `{y = 0}` and `2(1−q)` on `{y = 1}`. -/
def dens (q : ℝ) (y : T2) : ℝ := 2 * (if y = t0 then q else 1 - q)

lemma dens_t0 (q : ℝ) : dens q t0 = 2 * q := by simp [dens]
lemma dens_t1 (q : ℝ) : dens q t1 = 2 * (1 - q) := by simp [dens, t1_ne_t0]

lemma dens_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (y : T2) : 0 ≤ dens q y := by
  unfold dens; split_ifs <;> linarith

lemma ofReal_two_mul_inv (x : ℝ) : ENNReal.ofReal (2 * x) * 2⁻¹ = ENNReal.ofReal x := by
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_comm, ← mul_assoc,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

lemma integral_comp_cell {W : Type*} [MeasurableSpace W] (ν : Measure W) (g : W → T2)
    (hg : Measurable g) (hν : ν.map g = nu2) (φ : T2 → ℝ) :
    ∫ w, φ (g w) ∂ν = (φ t0 + φ t1) / 2 := by
  rw [← integral_map hg.aemeasurable (measurable_of_countable φ).aestronglyMeasurable, hν,
    integral_nu2]

lemma kl_cell {W : Type*} [MeasurableSpace W] (ν : Measure W) [IsProbabilityMeasure ν] (g : W → T2)
    (hg : Measurable g) (hν : ν.map g = nu2) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsProbabilityMeasure (ν.withDensity fun w => ENNReal.ofReal (dens q (g w))) ∧
      klDiv (ν.withDensity fun w => ENNReal.ofReal (dens q (g w))) ν = ENNReal.ofReal (hq q) ∧
      0 ≤ hq q ∧
      (ν.withDensity fun w => ENNReal.ofReal (dens q (g w))) (g ⁻¹' {t0}) = ENNReal.ofReal q := by
  set ρ := ν.withDensity fun w => ENNReal.ofReal (dens q (g w)) with hρ
  have hdm : Measurable fun w => dens q (g w) := (measurable_of_countable (dens q)).comp hg
  have hdn : ∀ w, 0 ≤ dens q (g w) := fun w => dens_nonneg hq0 hq1 _
  have hdint : Integrable (fun w => dens q (g w)) ν :=
    Integrable.of_mem_Icc 0 2 hdm.aemeasurable (ae_of_all _ fun w => ⟨hdn w, by
      unfold dens; split_ifs <;> linarith⟩)
  have hprob : IsProbabilityMeasure ρ := by
    constructor
    rw [hρ, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hdint (ae_of_all _ hdn),
      integral_comp_cell ν g hg hν, dens_t0, dens_t1]
    have : (2 * q + 2 * (1 - q)) / 2 = (1 : ℝ) := by ring
    rw [this, ENNReal.ofReal_one]
  have hac : ρ ≪ ν := withDensity_absolutelyContinuous _ _
  have hllr : llr ρ ν =ᵐ[ν] fun w => Real.log (dens q (g w)) := by
    filter_upwards [Measure.rnDeriv_withDensity ν hdm.ennreal_ofReal] with w hw
    rw [llr_def]
    simp only
    rw [hw, ENNReal.toReal_ofReal (hdn w)]
  have hlogm : Measurable fun w => Real.log (dens q (g w)) := Real.measurable_log.comp hdm
  set Cb := |Real.log (2 * q)| + |Real.log (2 * (1 - q))|
  have hlogb : ∀ w, |Real.log (dens q (g w))| ≤ Cb := by
    intro w
    rcases T2_cases (g w) with h | h
    · rw [h, dens_t0]; exact le_add_of_nonneg_right (abs_nonneg _)
    · rw [h, dens_t1]; exact le_add_of_nonneg_left (abs_nonneg _)
  have hllrρ : llr ρ ν =ᵐ[ρ] fun w => Real.log (dens q (g w)) := hac.ae_le hllr
  have hint : Integrable (llr ρ ν) ρ :=
    (Integrable.of_mem_Icc (-Cb) Cb hlogm.aemeasurable (ae_of_all _ fun w =>
      abs_le.1 (hlogb w))).congr hllrρ.symm
  have hkl_ne : klDiv ρ ν ≠ ∞ := klDiv_ne_top hac hint
  have hreal : (klDiv ρ ν).toReal = hq q := by
    rw [toReal_klDiv_of_measure_eq hac (by simp [measure_univ]),
      integral_congr_ae hllrρ]
    have e := integral_withDensity_eq_integral_smul (μ := ν)
      (f := fun w => (dens q (g w)).toNNReal) (by fun_prop) (fun w => Real.log (dens q (g w)))
    have e' : (ν.withDensity fun w => ((dens q (g w)).toNNReal : ℝ≥0∞)) = ρ := rfl
    rw [e'] at e
    rw [e]
    have e2 : (fun w => (dens q (g w)).toNNReal • Real.log (dens q (g w))) =
        fun w => dens q (g w) * Real.log (dens q (g w)) := by
      funext w
      rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hdn w)]
    rw [e2, integral_comp_cell ν g hg hν (fun y => dens q y * Real.log (dens q y)), dens_t0,
      dens_t1]
    unfold hq
    ring
  refine ⟨hprob, ?_, ?_, ?_⟩
  · rw [← hreal, ENNReal.ofReal_toReal hkl_ne]
  · rw [← hreal]; exact ENNReal.toReal_nonneg
  · have hA : MeasurableSet (g ⁻¹' {t0}) := hg (measurableSet_singleton _)
    have hc : ∫⁻ w in g ⁻¹' {t0}, ENNReal.ofReal (dens q (g w)) ∂ν =
        ∫⁻ _w in g ⁻¹' {t0}, ENNReal.ofReal (dens q t0) ∂ν :=
      setLIntegral_congr_fun_ae hA (ae_of_all _ fun w hw => by
        rw [mem_preimage, mem_singleton_iff] at hw; rw [hw])
    rw [hρ, withDensity_apply _ hA, hc, setLIntegral_const,
      ← Measure.map_apply hg (measurableSet_singleton _), hν, nu2_t0, dens_t0, ofReal_two_mul_inv]

lemma rep_T2 (ρ : Measure T2) [IsProbabilityMeasure ρ] :
    ρ = nu2.withDensity fun y => ENNReal.ofReal (dens (ρ.real {t0}) y) := by
  rw [Measure.ext_iff_singleton]
  intro a
  rw [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton]
  have hsum : ρ {t0} + ρ {t1} = 1 := by
    rw [← measure_union (by simpa using t0_ne_t1) (measurableSet_singleton _)]
    have : ({t0} ∪ {t1} : Set T2) = univ := by
      ext y; rcases T2_cases y with rfl | rfl <;> simp
    rw [this, measure_univ]
  rcases T2_cases a with rfl | rfl
  · rw [nu2_t0, dens_t0, ofReal_two_mul_inv, ofReal_measureReal]
  · rw [nu2_t1, dens_t1, ofReal_two_mul_inv]
    have h0 : ρ {t0} = ENNReal.ofReal (ρ.real {t0}) := (ofReal_measureReal).symm
    have hle : ρ.real {t0} ≤ 1 := measureReal_le_one
    rw [ENNReal.ofReal_sub _ measureReal_nonneg, ENNReal.ofReal_one, ← h0]
    rw [← hsum, ENNReal.add_sub_cancel_left (measure_ne_top _ _)]

lemma kl_lower (μ : Measure ZW) [IsProbabilityMeasure μ] :
    ENNReal.ofReal (hq (μ.real (Prod.snd ⁻¹' {t0}))) ≤ klDiv μ P0w ∧
      0 ≤ hq (μ.real (Prod.snd ⁻¹' {t0})) := by
  have hdp := klDiv_map_le μ P0w (g := Prod.snd) measurable_snd
  rw [P0w_snd] at hdp
  have hq' : (μ.map Prod.snd).real {t0} = μ.real (Prod.snd ⁻¹' {t0}) :=
    map_measureReal_apply measurable_snd (measurableSet_singleton _)
  have hrep := rep_T2 (μ.map Prod.snd)
  rw [hq'] at hrep
  have h0 : 0 ≤ μ.real (Prod.snd ⁻¹' {t0}) := measureReal_nonneg
  have h1 : μ.real (Prod.snd ⁻¹' {t0}) ≤ 1 := measureReal_le_one
  have hk := kl_cell nu2 id measurable_id Measure.map_id h0 h1
  simp only [id] at hk
  rw [hrep, hk.2.1] at hdp
  exact ⟨hdp, hk.2.2.1⟩

/-- The candidate minimiser `μ_q = d_q · P₀`. -/
def muq (q : ℝ) : Measure ZW := P0w.withDensity fun z => ENNReal.ofReal (dens q z.2)

lemma muq_facts {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsProbabilityMeasure (muq q) ∧ klDiv (muq q) P0w = ENNReal.ofReal (hq q) ∧ 0 ≤ hq q ∧
      (muq q).real (Prod.snd ⁻¹' {t0}) = q ∧ muq q ≪ P0w := by
  have hk := kl_cell P0w Prod.snd measurable_snd P0w_snd hq0 hq1
  refine ⟨hk.1, hk.2.1, hk.2.2.1, ?_, withDensity_absolutelyContinuous _ _⟩
  rw [measureReal_def]
  show ((P0w.withDensity fun z => ENNReal.ofReal (dens q z.2)) (Prod.snd ⁻¹' {t0})).toReal = q
  rw [hk.2.2.2, ENNReal.toReal_ofReal hq0]

/-! ### Assembly -/

lemma atomless_of_ac {μ : Measure ZW} (hac : μ ≪ P0w) (z : ZW) : μ {z} = 0 := hac (P0w_atomless z)

lemma phi_eq_of_ac {M : ℕ} {BL lam : ℝ} (hM : 2 ≤ M) (hBL : 0 ≤ BL) (μ : Measure ZW)
    [IsProbabilityMeasure μ] (hac : μ ≪ P0w) (x : unitInterval) :
    phiObj kw (Lw M BL) P0w lam μ x =
      ENNReal.ofReal (bco M BL * (M.choose 2 : ℝ) *
        (1 - (1 - 2 * μ.real (Prod.snd ⁻¹' {t0})) ^ 2)) + ENNReal.ofReal lam * klDiv μ P0w := by
  unfold phiObj
  rw [condRisk_eq hM hBL μ (atomless_of_ac hac) x, integral_psi]

lemma admissible_of_ac {M : ℕ} (μ : Measure ZW) [IsProbabilityMeasure μ] (hac : μ ≪ P0w) :
    Admissible P0w M μ :=
  ⟨inferInstance, hac Measure.measure_compl_support, by
    rw [pi_distinct μ (atomless_of_ac hac)]; exact one_pos⟩

lemma ofReal_Fw {bC lam q : ℝ} (hbC : 0 ≤ bC) (hlam : 0 ≤ lam) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hh : 0 ≤ hq q) :
    ENNReal.ofReal (bC * (1 - (1 - 2 * q) ^ 2)) + ENNReal.ofReal lam * ENNReal.ofReal (hq q) =
      ENNReal.ofReal (Fw bC lam q) := by
  have h1 : 0 ≤ bC * (1 - (1 - 2 * q) ^ 2) := by
    refine mul_nonneg hbC ?_
    nlinarith
  rw [← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_add h1 (mul_nonneg hlam hh)]
  rfl

end NU

open NU in
theorem cond_nonunique : Claims.cond_nonunique := by
  intro M BL lam hM hBL hlam0 hlam
  set bC := bco M BL * (M.choose 2 : ℝ) with hbCdef
  have hC : (1 : ℝ) ≤ M.choose 2 := by
    have : 1 ≤ M.choose 2 := Nat.choose_pos hM
    exact_mod_cast this
  have hden : 0 < (M.choose 2 : ℝ) + ((M / 2 : ℕ) : ℝ) := by positivity
  have hbC0 : 0 ≤ bC := mul_nonneg (div_nonneg hBL.le hden.le) (by positivity)
  have h2bC : kappaPrime M * BL = 2 * bC := by
    rw [hbCdef, kappaPrime, bco, ← two_choose M]
    field_simp
  obtain ⟨q, hqI, hqne, hqmin⟩ := exists_min_ne_half hlam0 (by rw [← h2bC]; exact hlam)
  -- every `μ_{q'}` with `q'` a minimiser of `F` minimises `φ_λ(x, ·)`
  have hmin : ∀ q' ∈ Icc (0 : ℝ) 1, (∀ q'' ∈ Icc (0 : ℝ) 1, Fw bC lam q' ≤ Fw bC lam q'') →
      ∀ x, IsMinimizer kw (Lw M BL) P0w lam x (muq q') := by
    intro q' hq' hq'min x
    obtain ⟨hprob, hkl, hhq, hreal, hac⟩ := muq_facts hq'.1 hq'.2
    refine ⟨admissible_of_ac _ hac, fun ν hν => ?_⟩
    have := hν.1
    by_cases htop : klDiv ν P0w = ⊤
    · have htop' : phiObj kw (Lw M BL) P0w lam ν x = ⊤ := by
        unfold phiObj; rw [htop, ENNReal.mul_top (by simpa using hlam0), add_top]
      rw [htop']; exact le_top
    · have hacν : ν ≪ P0w := (klDiv_ne_top_iff.1 htop).1
      rw [phi_eq_of_ac hM hBL.le _ hac x, phi_eq_of_ac hM hBL.le _ hacν x, hkl, hreal, ← hbCdef]
      obtain ⟨hlow, hhν⟩ := kl_lower ν
      set qν := ν.real (Prod.snd ⁻¹' {t0})
      have hqν0 : 0 ≤ qν := measureReal_nonneg
      have hqν1 : qν ≤ 1 := measureReal_le_one
      calc ENNReal.ofReal (bC * (1 - (1 - 2 * q') ^ 2)) + ENNReal.ofReal lam * ENNReal.ofReal (hq q')
          = ENNReal.ofReal (Fw bC lam q') := ofReal_Fw hbC0 hlam0.le hq'.1 hq'.2 hhq
        _ ≤ ENNReal.ofReal (Fw bC lam qν) := ENNReal.ofReal_le_ofReal (hq'min qν ⟨hqν0, hqν1⟩)
        _ = ENNReal.ofReal (bC * (1 - (1 - 2 * qν) ^ 2)) + ENNReal.ofReal lam * ENNReal.ofReal (hq qν) :=
            (ofReal_Fw hbC0 hlam0.le hqν0 hqν1 hhν).symm
        _ ≤ ENNReal.ofReal (bC * (1 - (1 - 2 * qν) ^ 2)) + ENNReal.ofReal lam * klDiv ν P0w := by
            gcongr
  have hqI' : 1 - q ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hqI.2], by linarith [hqI.1]⟩
  have hmin1 := hmin q hqI hqmin
  have hmin2 := hmin (1 - q) hqI' (fun q'' hq'' => by rw [Fw_symm]; exact hqmin q'' hq'')
  have hne : muq q ≠ muq (1 - q) := by
    intro h
    have h1 := (muq_facts hqI.1 hqI.2).2.2.2.1
    have h2 := (muq_facts hqI'.1 hqI'.2).2.2.2.1
    rw [h] at h1
    rw [h1] at h2
    exact hqne (by linarith)
  refine ⟨unitInterval, T2, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, P0w, kw, Lw M BL, inferInstance,
    P0w_atomless, inferInstance, P0w_disint, continuous_Lw M BL, Lw_bounds hM hBL.le, Lw_symm M BL,
    fun x => ⟨muq q, muq (1 - q), hne, hmin1 x, hmin2 x⟩,
    Kernel.const _ (muq q), Kernel.const _ (muq (1 - q)), ?_, ?_, fun x => by
      simpa [Kernel.const_apply] using hne⟩
  · refine ⟨fun x => (hmin1 x).1, fun π' hπ' => ?_⟩
    unfold condObj
    exact lintegral_mono fun x => by
      simpa [Kernel.const_apply] using (hmin1 x).2 (π' x) (hπ' x)
  · refine ⟨fun x => (hmin2 x).1, fun π' hπ' => ?_⟩
    unfold condObj
    exact lintegral_mono fun x => by
      simpa [Kernel.const_apply] using (hmin2 x).2 (π' x) (hπ' x)

end StatFormal.Wave11b
