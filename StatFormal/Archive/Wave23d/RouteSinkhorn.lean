import StatFormal.Archive.Wave23d.Statements
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Route — B `prop:ext-sinkhorn-aposteriori` (untrusted)

* `osc` on a nonempty `Fin n` is characterised by pairwise differences (`osc_le_iff`).
* **Birkhoff's contraction** (elementary proof). For positive `x, y` with `m ≤ x_j/y_j ≤ M`, `M/m = e^{d_H(x,y)}`,
  put `x' = x − m y ≥ 0`, `y' = M y − x ≥ 0`, `p = 𝖬x'`, `q = 𝖬y'`. Then `(𝖬x)_i/(𝖬y)_i = (M p_i + m q_i)/(p_i + q_i)`,
  and `p_i q_k ≤ η p_k q_i` (cross ratios of `𝖬`). With `t = p_i/q_i ≤ η s`, `s = p_k/q_k`, the function
  `D ↦ log(e^D t + 1) − log(e^D s + 1) − tanh(¼ log η) D` is antitone on `[0, ∞)`, because
  `σ(z + c) − σ(z) ≤ tanh(c/4)` (`(1 − A√B)² ≥ 0`); evaluating at `D = log(M/m)` gives the bound.
* Sinkhorn (i), (ii): the supplement's triangle-inequality arguments, in the variables `u = e^{f/ε}`, `v = e^{g/ε}`.
-/

set_option linter.style.longLine false

noncomputable section
open Set Finset Real
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave23d

open StatFormal.OTFD.Bands2 (osc)

/-! ### `osc` -/

section Osc
variable {n : ℕ}

lemma le_ciSup_fin [NeZero n] (d : Fin n → ℝ) (i : Fin n) : d i ≤ ⨆ j, d j :=
  le_ciSup (Set.finite_range d).bddAbove i

lemma ciInf_le_fin [NeZero n] (d : Fin n → ℝ) (i : Fin n) : ⨅ j, d j ≤ d i :=
  ciInf_le (Set.finite_range d).bddBelow i

lemma osc_le_iff [NeZero n] (d : Fin n → ℝ) (c : ℝ) : osc d ≤ c ↔ ∀ i k, d i - d k ≤ c := by
  constructor
  · intro h i k
    have := le_ciSup_fin d i
    have := ciInf_le_fin d k
    unfold osc at h; linarith
  · intro h
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := d)
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := d)
    unfold osc; rw [← hi, ← hk]; exact h i k

lemma sub_le_osc [NeZero n] (d : Fin n → ℝ) (i k : Fin n) : d i - d k ≤ osc d :=
  (osc_le_iff d _).1 le_rfl i k

lemma osc_nonneg [NeZero n] (d : Fin n → ℝ) : 0 ≤ osc d := by
  have := sub_le_osc d 0 0; simpa using this

lemma osc_congr_add_const [NeZero n] (d e : Fin n → ℝ) (c : ℝ) (h : ∀ i, d i = e i + c) :
    osc d = osc e := by
  apply le_antisymm
  · rw [osc_le_iff]; intro i k; rw [h, h]; have := sub_le_osc e i k; linarith
  · rw [osc_le_iff]; intro i k; have := sub_le_osc d i k; rw [h, h] at this; linarith

lemma osc_neg [NeZero n] (d : Fin n → ℝ) : osc (fun i => -d i) = osc d := by
  apply le_antisymm
  · rw [osc_le_iff]; intro i k; have := sub_le_osc d k i; linarith
  · rw [osc_le_iff]; intro i k; have := sub_le_osc (fun i => -d i) k i; linarith

lemma osc_add_le [NeZero n] (d e : Fin n → ℝ) : osc (fun i => d i + e i) ≤ osc d + osc e := by
  rw [osc_le_iff]; intro i k
  have := sub_le_osc d i k; have := sub_le_osc e i k; linarith

lemma osc_smul [NeZero n] (d : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    osc (fun i => c * d i) = c * osc d := by
  apply le_antisymm
  · rw [osc_le_iff]; intro i k
    have := sub_le_osc d i k
    nlinarith
  · rcases hc.eq_or_lt with rfl | hc
    · simp only [zero_mul]; exact osc_nonneg _
    · rw [← le_div_iff₀' hc, osc_le_iff]; intro i k
      have := sub_le_osc (fun i => c * d i) i k
      rw [le_div_iff₀' hc]; nlinarith

end Osc

/-! ### Hilbert's projective metric -/

section Hilb
variable {n : ℕ}

lemma hilb_symm [NeZero n] (x y : Fin n → ℝ) : hilb x y = hilb y x := by
  unfold hilb; rw [← osc_neg]; congr 1; ext i; ring

lemma hilb_triangle [NeZero n] (x y z : Fin n → ℝ) : hilb x z ≤ hilb x y + hilb y z := by
  unfold hilb
  calc osc (fun i => Real.log (x i) - Real.log (z i))
      = osc (fun i => (Real.log (x i) - Real.log (y i)) + (Real.log (y i) - Real.log (z i))) := by
        congr 1; ext i; ring
    _ ≤ _ := osc_add_le _ _

lemma hilb_nonneg [NeZero n] (x y : Fin n → ℝ) : 0 ≤ hilb x y := osc_nonneg _

/-- `d_H(c ⊙ x, c ⊙ y) = d_H(x, y)`. -/
lemma hilb_mul_left [NeZero n] {c x y : Fin n → ℝ} (hc : ∀ i, 0 < c i) (hx : ∀ i, 0 < x i)
    (hy : ∀ i, 0 < y i) : hilb (fun i => c i * x i) (fun i => c i * y i) = hilb x y := by
  unfold hilb; congr 1; ext i
  rw [Real.log_mul (hc i).ne' (hx i).ne', Real.log_mul (hc i).ne' (hy i).ne']; ring

/-- `d_H(c / x, c / y) = d_H(x, y)`. -/
lemma hilb_div_left [NeZero n] {c x y : Fin n → ℝ} (hc : ∀ i, 0 < c i) (hx : ∀ i, 0 < x i)
    (hy : ∀ i, 0 < y i) : hilb (fun i => c i / x i) (fun i => c i / y i) = hilb x y := by
  unfold hilb
  rw [← osc_neg]; congr 1; ext i
  rw [Real.log_div (hc i).ne' (hx i).ne', Real.log_div (hc i).ne' (hy i).ne']; ring

end Hilb

/-! ### Finite suprema over four indices -/

section Sup4
variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]

lemma le_sup4 (F : α → α → β → β → ℝ) (i i' : α) (j j' : β) :
    F i i' j j' ≤ ⨆ (i : α) (i' : α) (j : β) (j' : β), F i i' j j' := by
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove i)
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove i')
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove j)
  exact le_ciSup (Set.finite_range _).bddAbove j'

lemma sup4_le {F : α → α → β → β → ℝ} {c : ℝ} (h : ∀ i i' j j', F i i' j j' ≤ c) :
    ⨆ (i : α) (i' : α) (j : β) (j' : β), F i i' j j' ≤ c :=
  ciSup_le fun i => ciSup_le fun i' => ciSup_le fun j => ciSup_le fun j' => h i i' j j'

lemma sup4_congr_le {F G : α → α → β → β → ℝ}
    (h : ∀ i i' j j', ∃ k k' l l', F i i' j j' ≤ G k k' l l') :
    ⨆ (i : α) (i' : α) (j : β) (j' : β), F i i' j j' ≤ ⨆ (i : α) (i' : α) (j : β) (j' : β), G i i' j j' :=
  sup4_le fun i i' j j' => by
    obtain ⟨k, k', l, l', hh⟩ := h i i' j j'
    exact hh.trans (le_sup4 G k k' l l')

lemma sup4_congr_le' {γ δ : Type*} [Fintype γ] [Fintype δ] [Nonempty γ] [Nonempty δ]
    (F : α → α → β → β → ℝ) (G : γ → γ → δ → δ → ℝ)
    (h : ∀ i i' j j', ∃ k k' l l', F i i' j j' ≤ G k k' l l') :
    ⨆ (i : α) (i' : α) (j : β) (j' : β), F i i' j j' ≤ ⨆ (i : γ) (i' : γ) (j : δ) (j' : δ), G i i' j j' :=
  sup4_le fun i i' j j' => by
    obtain ⟨k, k', l, l', hh⟩ := h i i' j j'
    exact hh.trans (le_sup4 G k k' l l')

lemma exists_sup4 (F : α → α → β → β → ℝ) :
    ∃ i i' j j', F i i' j j' = ⨆ (i : α) (i' : α) (j : β) (j' : β), F i i' j j' := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => ⨆ (i' : α) (j : β) (j' : β), F i i' j j')
  obtain ⟨i', hi'⟩ := exists_eq_ciSup_of_finite (f := fun i' => ⨆ (j : β) (j' : β), F i i' j j')
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun j => ⨆ (j' : β), F i i' j j')
  obtain ⟨j', hj'⟩ := exists_eq_ciSup_of_finite (f := fun j' => F i i' j j')
  exact ⟨i, i', j, j', by rw [← hi, ← hi', ← hj, ← hj']⟩

end Sup4

/-! ### The scalar inequality behind Birkhoff's theorem -/

lemma tanh_eq_exp (x : ℝ) : Real.tanh x = (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h1 : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  have hx := Real.exp_pos x
  rw [h1, h2]; field_simp

/-- `tanh(¼ log η) = (√η − 1)/(√η + 1)`. -/
lemma tanh_quarter_log {η : ℝ} (hη : 0 < η) :
    Real.tanh (Real.log η / 4) = (√η - 1) / (√η + 1) := by
  rw [tanh_eq_exp]
  have : Real.exp (2 * (Real.log η / 4)) = √η := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hη]; congr 1; ring
  rw [this]

/-- `σ(z + c) − σ(z) ≤ (√B − 1)/(√B + 1)` with `A = e^z`, `B = e^c ≥ 1`. -/
lemma logistic_diff_le {A B : ℝ} (hA : 0 < A) (hB : 1 ≤ B) :
    A * B / (A * B + 1) - A / (A + 1) ≤ (√B - 1) / (√B + 1) := by
  have hs : 0 ≤ √B := Real.sqrt_nonneg B
  have hs2 : √B ^ 2 = B := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ √B := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hB
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  set r := √B with hr
  have hB' : B = r ^ 2 := hs2.symm
  have key : A * (r + 1) ^ 2 ≤ (A * B + 1) * (A + 1) := by
    rw [hB']; nlinarith [sq_nonneg (1 - A * r)]
  have e : A * B * (A + 1) - (A * B + 1) * A = A * (r - 1) * (r + 1) := by
    rw [hB']; ring
  rw [e]
  have : 0 ≤ √B - 1 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left key this]

lemma sqrt_ratio_mono {B η : ℝ} (hB : 0 ≤ B) (hBη : B ≤ η) :
    (√B - 1) / (√B + 1) ≤ (√η - 1) / (√η + 1) := by
  have h1 := Real.sqrt_le_sqrt hBη
  have := Real.sqrt_nonneg B
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The scalar Birkhoff inequality: `t ≤ η s`, `ψ ≥ 1` ⇒
`log(ψt+1) − log(t+1) − log(ψs+1) + log(s+1) ≤ tanh(¼ log η) log ψ`. -/
lemma scalar_birkhoff {t s η ψ : ℝ} (ht : 0 < t) (hs : 0 < s) (hη : 1 ≤ η) (hts : t ≤ η * s)
    (hψ : 1 ≤ ψ) :
    Real.log (ψ * t + 1) - Real.log (t + 1) - (Real.log (ψ * s + 1) - Real.log (s + 1)) ≤
      Real.tanh (Real.log η / 4) * Real.log ψ := by
  set c := Real.tanh (Real.log η / 4) with hc
  have hc0 : 0 ≤ c := by
    rw [hc, tanh_quarter_log (by linarith)]
    have : 1 ≤ √η := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hη
    exact div_nonneg (by linarith) (by positivity)
  let φ : ℝ → ℝ := fun D => Real.log (Real.exp D * t + 1) - Real.log (Real.exp D * s + 1) - c * D
  have hderiv : ∀ D, HasDerivAt φ (Real.exp D * t / (Real.exp D * t + 1) -
      Real.exp D * s / (Real.exp D * s + 1) - c) D := by
    intro D
    have h1 : HasDerivAt (fun D => Real.exp D * t + 1) (Real.exp D * t) D :=
      ((Real.hasDerivAt_exp D).mul_const t).add_const 1
    have h2 : HasDerivAt (fun D => Real.exp D * s + 1) (Real.exp D * s) D :=
      ((Real.hasDerivAt_exp D).mul_const s).add_const 1
    have h1' := h1.log (by positivity)
    have h2' := h2.log (by positivity)
    have h3 : HasDerivAt (fun D => c * D) c D := by simpa using (hasDerivAt_id D).const_mul c
    exact (h1'.sub h2').sub h3
  have hanti : AntitoneOn φ (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
    · exact (fun D _ => (hderiv D).continuousAt.continuousWithinAt)
    · exact fun D _ => (hderiv D).differentiableAt.differentiableWithinAt
    · intro D _
      rw [(hderiv D).deriv]
      have hA : 0 < Real.exp D * s := by positivity
      rcases le_or_gt t s with hle | hlt
      · have : Real.exp D * t / (Real.exp D * t + 1) ≤ Real.exp D * s / (Real.exp D * s + 1) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have := Real.exp_pos D
          nlinarith [mul_le_mul_of_nonneg_left hle this.le]
        linarith
      · set B := t / s
        have hB1 : 1 ≤ B := by rw [le_div_iff₀ hs]; linarith
        have hBη : B ≤ η := by rw [div_le_iff₀ hs]; linarith
        have e : Real.exp D * t = Real.exp D * s * B := by
          simp only [B]; field_simp
        rw [e]
        have := logistic_diff_le hA hB1
        have := sqrt_ratio_mono (by linarith) hBη
        rw [hc, tanh_quarter_log (by linarith)]
        linarith
  have hD : 0 ≤ Real.log ψ := Real.log_nonneg hψ
  have := hanti (Set.mem_Ici.2 le_rfl) hD hD
  simp only [φ, Real.exp_zero, one_mul, mul_zero, sub_zero, Real.exp_log (by linarith : (0 : ℝ) < ψ)] at this
  linarith

/-! ### Birkhoff's contraction theorem -/

section Birkhoff
variable {p q : ℕ}

lemma matVec_pos {M : Fin p → Fin q → ℝ} [NeZero q] (hM : ∀ i j, 0 < M i j) {x : Fin q → ℝ}
    (hx : ∀ j, 0 < x j) (i : Fin p) : 0 < matVec M x i :=
  Finset.sum_pos (fun j _ => mul_pos (hM i j) (hx j)) Finset.univ_nonempty

lemma matVec_pos_of_nonneg {M : Fin p → Fin q → ℝ} (hM : ∀ i j, 0 < M i j) {x : Fin q → ℝ}
    (hx : ∀ j, 0 ≤ x j) {j₀ : Fin q} (hj₀ : 0 < x j₀) (i : Fin p) : 0 < matVec M x i :=
  lt_of_lt_of_le (mul_pos (hM i j₀) hj₀)
    (Finset.single_le_sum (fun j _ => mul_nonneg (hM i j).le (hx j)) (Finset.mem_univ j₀))

lemma one_le_etaM [NeZero p] [NeZero q] {M : Fin p → Fin q → ℝ} (hM : ∀ i j, 0 < M i j) : 1 ≤ etaM M := by
  have := le_sup4 (fun i i' j j' => M i j * M i' j' / (M i' j * M i j')) 0 0 0 0
  rw [div_self (by have := hM 0 0; positivity)] at this
  exact this

/-- Cross ratios: `p_i q_k ≤ η p_k q_i` for `p = 𝖬x'`, `q = 𝖬y'`, `x', y' ≥ 0`. -/
lemma cross_ratio [NeZero p] [NeZero q] {M : Fin p → Fin q → ℝ} (hM : ∀ i j, 0 < M i j)
    {x y : Fin q → ℝ} (hx : ∀ j, 0 ≤ x j) (hy : ∀ j, 0 ≤ y j) (i k : Fin p) :
    matVec M x i * matVec M y k ≤ etaM M * (matVec M x k * matVec M y i) := by
  simp only [matVec, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun j _ => ?_
  have h := le_sup4 (fun i i' j j' => M i j * M i' j' / (M i' j * M i j')) i k j l
  rw [div_le_iff₀ (by have := hM k j; have := hM i l; positivity)] at h
  have := mul_le_mul_of_nonneg_right h (mul_nonneg (hx j) (hy l))
  calc M i j * x j * (M k l * y l) = M i j * M k l * (x j * y l) := by ring
    _ ≤ etaM M * (M k j * M i l) * (x j * y l) := this
    _ = etaM M * (M k j * x j * (M i l * y l)) := by ring

theorem birkhoff_contraction_thm : Claims.birkhoff_contraction := by
  intro p q M hp hq hM x y hx hy
  have : NeZero p := ⟨hp.ne'⟩
  have : NeZero q := ⟨hq.ne'⟩
  set η := etaM M
  have hη := one_le_etaM hM
  set d : Fin q → ℝ := fun j => Real.log (x j) - Real.log (y j) with hd
  set lo := ⨅ j, d j
  set hi := ⨆ j, d j
  have hD : hilb x y = hi - lo := rfl
  set mm := Real.exp lo
  set MM := Real.exp hi
  have hmm : 0 < mm := Real.exp_pos _
  have hratio : ∀ j, mm * y j ≤ x j ∧ x j ≤ MM * y j := by
    intro j
    have hxj : x j = Real.exp (d j) * y j := by
      simp only [hd]; rw [Real.exp_sub, Real.exp_log (hx j), Real.exp_log (hy j)]
      rw [div_mul_cancel₀ _ (hy j).ne']
    have h1 := ciInf_le_fin d j
    have h2 := le_ciSup_fin d j
    rw [hxj]
    exact ⟨mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h1) (hy j).le,
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h2) (hy j).le⟩
  have hc0 : 0 ≤ Real.tanh (Real.log η / 4) := by
    rw [tanh_quarter_log (by linarith)]
    have : 1 ≤ √η := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hη
    exact div_nonneg (by linarith) (by positivity)
  rcases (show lo ≤ hi from (ciInf_le_fin d 0).trans (le_ciSup_fin d 0)).eq_or_lt with hlh | hlh
  · -- `x = mm y`: both sides vanish
    have hxy : ∀ j, x j = mm * y j := fun j => by
      have := hratio j; rw [show MM = mm by simp [MM, mm, hlh]] at this; linarith [this.1, this.2]
    have hMx : ∀ i, matVec M x i = mm * matVec M y i := fun i => by
      simp only [matVec, hxy, Finset.mul_sum]; congr 1; ext j; ring
    have : hilb (matVec M x) (matVec M y) = 0 := by
      unfold hilb
      have h0 : ∀ i, Real.log (matVec M x i) - Real.log (matVec M y i) = 0 + Real.log mm := fun i => by
        rw [hMx, Real.log_mul hmm.ne' (matVec_pos hM hy i).ne']; ring
      rw [osc_congr_add_const _ (fun _ => (0 : ℝ)) _ h0]; simp [osc]
    rw [this]; exact mul_nonneg hc0 (hilb_nonneg _ _)
  · obtain ⟨jh, hjh⟩ := exists_eq_ciSup_of_finite (f := d)
    obtain ⟨jl, hjl⟩ := exists_eq_ciInf_of_finite (f := d)
    have hMMmm : mm < MM := Real.exp_lt_exp.2 hlh
    set x' : Fin q → ℝ := fun j => x j - mm * y j
    set y' : Fin q → ℝ := fun j => MM * y j - x j
    have hx' : ∀ j, 0 ≤ x' j := fun j => by simp only [x']; linarith [(hratio j).1]
    have hy' : ∀ j, 0 ≤ y' j := fun j => by simp only [y']; linarith [(hratio j).2]
    have hxjh : x jh = MM * y jh := by
      have : Real.exp (d jh) = MM := by rw [hjh]
      simp only [hd] at this
      rw [Real.exp_sub, Real.exp_log (hx jh), Real.exp_log (hy jh), div_eq_iff (hy jh).ne'] at this
      linarith
    have hxjl : x jl = mm * y jl := by
      have : Real.exp (d jl) = mm := by rw [hjl]
      simp only [hd] at this
      rw [Real.exp_sub, Real.exp_log (hx jl), Real.exp_log (hy jl), div_eq_iff (hy jl).ne'] at this
      linarith
    have hx'p : 0 < x' jh := by
      simp only [x']; rw [hxjh]; nlinarith [hy jh]
    have hy'p : 0 < y' jl := by
      simp only [y']; rw [hxjl]; nlinarith [hy jl]
    set P := matVec M x'
    set Q := matVec M y'
    have hP : ∀ i, 0 < P i := matVec_pos_of_nonneg hM hx' hx'p
    have hQ : ∀ i, 0 < Q i := matVec_pos_of_nonneg hM hy' hy'p
    have hMx : ∀ i, matVec M x i = P i + mm * matVec M y i := fun i => by
      simp only [P, matVec, x', Finset.mul_sum, ← Finset.sum_add_distrib]; congr 1; ext j; ring
    have hMy : ∀ i, (MM - mm) * matVec M y i = P i + Q i := fun i => by
      simp only [P, Q, matVec, x', y', Finset.mul_sum, ← Finset.sum_add_distrib]; congr 1; ext j; ring
    -- the log-ratio in terms of `t_i = P_i/Q_i`
    set ψ := MM / mm
    have hψ : 1 ≤ ψ := by rw [le_div_iff₀ hmm]; linarith
    have hlogψ : Real.log ψ = hi - lo := by
      simp only [ψ, MM, mm]; rw [← Real.exp_sub, Real.log_exp]
    have hlr : ∀ i, Real.log (matVec M x i) - Real.log (matVec M y i) =
        Real.log mm + (Real.log (ψ * (P i / Q i) + 1) - Real.log (P i / Q i + 1)) := by
      intro i
      have hy0 := matVec_pos hM hy i
      have hQi := hQ i
      have hPi := hP i
      have hyi : matVec M y i = (P i + Q i) / (MM - mm) := by
        rw [eq_div_iff (by linarith)]; linarith [hMy i]
      have e1 : matVec M x i / matVec M y i = mm * ((ψ * (P i / Q i) + 1) / (P i / Q i + 1)) := by
        have hne : MM - mm ≠ 0 := sub_ne_zero.2 hMMmm.ne'
        rw [hMx, hyi]; simp only [ψ]; field_simp; ring
      rw [← Real.log_div (matVec_pos hM hx i).ne' hy0.ne', e1,
        Real.log_mul hmm.ne' (by positivity), Real.log_div (by positivity) (by positivity)]
    unfold hilb
    rw [osc_le_iff]
    intro i k
    rw [hlr i, hlr k, show (osc fun i => Real.log (x i) - Real.log (y i)) = hi - lo from rfl, ← hlogψ]
    have hcr := cross_ratio hM hx' hy' i k
    have hts : P i / Q i ≤ η * (P k / Q k) := by
      rw [div_le_iff₀ (hQ i), mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ (hQ k)]
      linarith [hcr]
    have := scalar_birkhoff (div_pos (hP i) (hQ i)) (div_pos (hP k) (hQ k)) hη hts hψ
    linarith

end Birkhoff

/-! ### The Sinkhorn constants -/

section Constants
variable {n m : ℕ}

lemma deltaC_transpose [NeZero n] [NeZero m] (C : Fin n → Fin m → ℝ) :
    deltaC (fun j i => C i j) = deltaC C := by
  unfold deltaC
  apply le_antisymm
  · refine sup4_congr_le' _ _ fun j j' i i' => ⟨i, i', j, j', le_of_eq ?_⟩
    ring
  · refine sup4_congr_le' _ _ fun i i' j j' => ⟨j, j', i, i', le_of_eq ?_⟩
    ring

lemma deltaC_nonneg [NeZero n] [NeZero m] (C : Fin n → Fin m → ℝ) : 0 ≤ deltaC C := by
  have := le_sup4 (fun i i' j j' => C i j + C i' j' - C i j' - C i' j) 0 0 0 0
  simp only [sub_self, add_sub_cancel_right] at this
  unfold deltaC; linarith

lemma etaM_gibbs [NeZero n] [NeZero m] {ε : ℝ} (hε : 0 < ε) (C : Fin n → Fin m → ℝ) :
    etaM (gibbs ε C) = Real.exp (deltaC C / ε) := by
  have key : ∀ i i' j j', gibbs ε C i j * gibbs ε C i' j' / (gibbs ε C i' j * gibbs ε C i j') =
      Real.exp ((C i' j + C i j' - C i' j' - C i j) / ε) := by
    intro i i' j j'
    simp only [gibbs]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]; congr 1; ring
  unfold etaM
  simp_rw [key]
  apply le_antisymm
  · refine sup4_le fun i i' j j' => Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hε.le)
    exact le_sup4 (fun i i' j j' => C i j + C i' j' - C i j' - C i' j) i' i j j'
  · obtain ⟨a, b, c, d, h⟩ := exists_sup4 (fun i i' j j' => C i j + C i' j' - C i j' - C i' j)
    unfold deltaC; rw [← h]
    refine le_trans (le_of_eq ?_) (le_sup4 (fun i i' j j' =>
      Real.exp ((C i' j + C i j' - C i' j' - C i j) / ε)) b a c d)
    congr 2

/-- `log η(𝖪)/4 = Δ_C/(4ε)`. -/
lemma log_etaM_gibbs [NeZero n] [NeZero m] {ε : ℝ} (hε : 0 < ε) (C : Fin n → Fin m → ℝ) :
    Real.log (etaM (gibbs ε C)) / 4 = deltaC C / (4 * ε) := by
  rw [etaM_gibbs hε, Real.log_exp]; field_simp

theorem sinkhorn_constants_thm : Claims.sinkhorn_constants := by
  intro n m ε C hn hm hε
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero m := ⟨hm.ne'⟩
  refine ⟨etaM_gibbs hε C, by rw [log_etaM_gibbs hε], ?_⟩
  rw [← log_etaM_gibbs hε, tanh_quarter_log (by rw [etaM_gibbs hε]; positivity)]

lemma tanh_sq_lt_one (x : ℝ) : Real.tanh x ^ 2 < 1 := by
  have h1 := Real.tanh_lt_one x
  have h2 := Real.neg_one_lt_tanh x
  nlinarith

lemma one_sub_tanh_sq (x : ℝ) : 1 - Real.tanh x ^ 2 = 1 / Real.cosh x ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc := Real.cosh_pos x
  have := Real.cosh_sq_sub_sinh_sq x
  field_simp; linarith

lemma div_one_sub_tanh_sq (ε x : ℝ) : ε / (1 - Real.tanh x ^ 2) = ε * Real.cosh x ^ 2 := by
  rw [one_sub_tanh_sq]; field_simp

lemma tanh_div_one_sub_tanh_sq (ε x : ℝ) :
    ε * Real.tanh x / (1 - Real.tanh x ^ 2) = ε / 2 * Real.sinh (2 * x) := by
  rw [one_sub_tanh_sq, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
  have hc := (Real.cosh_pos x).ne'
  field_simp

end Constants

/-! ### `Δ_C` for the squared-distance cost -/

theorem sinkhorn_deltaC_diam_thm : Claims.sinkhorn_deltaC_diam := by
  intro E _ _ n m Z u hn hm
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero m := ⟨hm.ne'⟩
  have key : ∀ i i' j j', ‖Z i - u j‖ ^ 2 + ‖Z i' - u j'‖ ^ 2 - ‖Z i - u j'‖ ^ 2 - ‖Z i' - u j‖ ^ 2 =
      2 * ⟪Z i - Z i', u j' - u j⟫ := by
    intro i i' j j'
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right]
    rw [real_inner_comm (u j) (Z i), real_inner_comm (u j') (Z i'), real_inner_comm (u j') (Z i),
      real_inner_comm (u j) (Z i')]
    ring
  have heq : deltaC (fun i j => ‖Z i - u j‖ ^ 2) =
      2 * ⨆ (i : Fin n) (i' : Fin n) (j : Fin m) (j' : Fin m), ⟪Z i - Z i', u j' - u j⟫ := by
    unfold deltaC
    simp_rw [key]
    apply le_antisymm
    · refine sup4_le fun i i' j j' => ?_
      have := le_sup4 (fun i i' j j' => ⟪Z i - Z i', u j' - u j⟫) i i' j j'
      linarith
    · obtain ⟨a, b, c, d, h⟩ := exists_sup4 (fun i i' j j' => ⟪Z i - Z i', u j' - u j⟫)
      rw [← h]; exact le_sup4 (fun i i' j j' => 2 * ⟪Z i - Z i', u j' - u j⟫) a b c d
  refine ⟨heq, ?_⟩
  rw [heq, mul_assoc]
  refine mul_le_mul_of_nonneg_left (sup4_le fun i i' j j' => ?_) (by norm_num)
  have hZ : Bornology.IsBounded (Set.range Z) := (Set.finite_range Z).isBounded
  have hu : Bornology.IsBounded (Set.range u) := (Set.finite_range u).isBounded
  calc ⟪Z i - Z i', u j' - u j⟫ ≤ ‖Z i - Z i'‖ * ‖u j' - u j‖ := real_inner_le_norm _ _
    _ ≤ Metric.diam (Set.range Z) * Metric.diam (Set.range u) := by
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact mul_le_mul (Metric.dist_le_diam_of_mem hZ (mem_range_self _) (mem_range_self _))
        (Metric.dist_le_diam_of_mem hu (mem_range_self _) (mem_range_self _)) dist_nonneg
        Metric.diam_nonneg


/-! ### Sinkhorn in the scaling variables -/

section Sinkhorn
variable {n m : ℕ} {ε : ℝ} {C : Fin n → Fin m → ℝ}

/-- The transposed Gibbs kernel. -/
abbrev gibbsT (ε : ℝ) (C : Fin n → Fin m → ℝ) : Fin m → Fin n → ℝ := fun j i => gibbs ε C i j

lemma gibbs_pos (i : Fin n) (j : Fin m) : 0 < gibbs ε C i j := Real.exp_pos _

lemma planFG_eq (hε : 0 < ε) (f : Fin n → ℝ) (g : Fin m → ℝ) (i : Fin n) (j : Fin m) :
    planFG ε C f g i j = Real.exp (f i / ε) * gibbs ε C i j * Real.exp (g j / ε) := by
  simp only [planFG, gibbs]; rw [← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring

lemma rowSum_planFG (hε : 0 < ε) (f : Fin n → ℝ) (g : Fin m → ℝ) (i : Fin n) :
    rowSum (planFG ε C f g) i = Real.exp (f i / ε) * matVec (gibbs ε C) (fun j => Real.exp (g j / ε)) i := by
  simp only [rowSum, matVec, Finset.mul_sum, planFG_eq hε]; congr 1; ext j; ring

lemma colSum_planFG (hε : 0 < ε) (f : Fin n → ℝ) (g : Fin m → ℝ) (j : Fin m) :
    colSum (planFG ε C f g) j = Real.exp (g j / ε) * matVec (gibbsT ε C) (fun i => Real.exp (f i / ε)) j := by
  simp only [colSum, matVec, Finset.mul_sum, planFG_eq hε]; congr 1; ext i; ring

lemma exp_colStep [NeZero n] (hε : 0 < ε) {b : Fin m → ℝ} (hb : ∀ j, 0 < b j) (f : Fin n → ℝ) (j : Fin m) :
    Real.exp (colStep ε b C f j / ε) = b j / matVec (gibbsT ε C) (fun i => Real.exp (f i / ε)) j := by
  have hS : ∑ i, Real.exp ((f i - C i j) / ε) = matVec (gibbsT ε C) (fun i => Real.exp (f i / ε)) j := by
    simp only [matVec, gibbs]; congr 1; ext i; rw [← Real.exp_add]; congr 1; ring
  have hpos : 0 < matVec (gibbsT ε C) (fun i => Real.exp (f i / ε)) j :=
    matVec_pos (fun _ _ => gibbs_pos _ _) (fun _ => Real.exp_pos _) j
  have e : colStep ε b C f j / ε = Real.log (b j) - Real.log (matVec (gibbsT ε C) (fun i => Real.exp (f i / ε)) j) := by
    simp only [colStep]; rw [hS]; field_simp
  rw [e, Real.exp_sub, Real.exp_log (hb j), Real.exp_log hpos]

lemma exp_rowStep [NeZero m] (hε : 0 < ε) {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) (g : Fin m → ℝ) (i : Fin n) :
    Real.exp (rowStep ε a C g i / ε) = a i / matVec (gibbs ε C) (fun j => Real.exp (g j / ε)) i := by
  have hS : ∑ j, Real.exp ((g j - C i j) / ε) = matVec (gibbs ε C) (fun j => Real.exp (g j / ε)) i := by
    simp only [matVec, gibbs]; congr 1; ext j; rw [← Real.exp_add]; congr 1; ring
  have hpos : 0 < matVec (gibbs ε C) (fun j => Real.exp (g j / ε)) i :=
    matVec_pos (fun _ _ => gibbs_pos _ _) (fun _ => Real.exp_pos _) i
  have e : rowStep ε a C g i / ε = Real.log (a i) - Real.log (matVec (gibbs ε C) (fun j => Real.exp (g j / ε)) i) := by
    simp only [rowStep]; rw [hS]; field_simp
  rw [e, Real.exp_sub, Real.exp_log (ha i), Real.exp_log hpos]

/-- `osc(f − f') = ε d_H(e^{f/ε}, e^{f'/ε})`. -/
lemma osc_eq_hilb [NeZero n] (hε : 0 < ε) (f f' : Fin n → ℝ) :
    osc (f - f') = ε * hilb (fun i => Real.exp (f i / ε)) (fun i => Real.exp (f' i / ε)) := by
  unfold hilb
  simp_rw [Real.log_exp]
  rw [← osc_smul _ hε.le]
  congr 1; ext i; simp only [Pi.sub_apply]; field_simp

/-- Hilbert-metric bookkeeping for `d_H(x, a/w) = d_H(x ⊙ w, a)`. -/
lemma hilb_div_eq {k : ℕ} [NeZero k] {x w a : Fin k → ℝ} (hx : ∀ i, 0 < x i) (hw : ∀ i, 0 < w i)
    (ha : ∀ i, 0 < a i) : hilb x (fun i => a i / w i) = hilb (fun i => x i * w i) a := by
  unfold hilb; congr 1; ext i
  rw [Real.log_div (ha i).ne' (hw i).ne', Real.log_mul (hx i).ne' (hw i).ne']; ring

variable [NeZero n] [NeZero m]

lemma birkhoff_gibbs (hε : 0 < ε) {x y : Fin m → ℝ} (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j) :
    hilb (matVec (gibbs ε C) x) (matVec (gibbs ε C) y) ≤ Real.tanh (deltaC C / (4 * ε)) * hilb x y := by
  have := birkhoff_contraction_thm n m (gibbs ε C) (Nat.pos_of_ne_zero (NeZero.ne n))
    (Nat.pos_of_ne_zero (NeZero.ne m)) (fun _ _ => gibbs_pos _ _) x y hx hy
  rwa [log_etaM_gibbs hε] at this

lemma birkhoff_gibbsT (hε : 0 < ε) {x y : Fin n → ℝ} (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j) :
    hilb (matVec (gibbsT ε C) x) (matVec (gibbsT ε C) y) ≤ Real.tanh (deltaC C / (4 * ε)) * hilb x y := by
  have := birkhoff_gibbs (C := fun j i => C i j) hε hx hy
  rwa [deltaC_transpose] at this

lemma lam_nonneg (hε : 0 < ε) : 0 ≤ Real.tanh (deltaC C / (4 * ε)) :=
  by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.2 (div_nonneg (deltaC_nonneg C) (by positivity)))
      (Real.cosh_pos _).le

/-- The dual optimality conditions in scaling form: `u* = a/(𝖪v*)`, `v* = b/(𝖪^⊤u*)`. -/
lemma dualSol_scaling (hε : 0 < ε) {a : Fin n → ℝ} {b : Fin m → ℝ} {fs : Fin n → ℝ} {gs : Fin m → ℝ}
    (h : IsDualSol ε a b C fs gs) :
    (fun i => Real.exp (fs i / ε)) = (fun i => a i / matVec (gibbs ε C) (fun j => Real.exp (gs j / ε)) i) ∧
    (fun j => Real.exp (gs j / ε)) = (fun j => b j / matVec (gibbsT ε C) (fun i => Real.exp (fs i / ε)) j) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · ext i
    have := congrFun h1 i
    rw [rowSum_planFG hε] at this
    rw [← this, mul_div_assoc, div_self (matVec_pos (fun _ _ => gibbs_pos _ _) (fun _ => Real.exp_pos _) i).ne',
      mul_one]
  · ext j
    have := congrFun h2 j
    rw [colSum_planFG hε] at this
    rw [← this, mul_div_assoc, div_self (matVec_pos (fun _ _ => gibbs_pos _ _) (fun _ => Real.exp_pos _) j).ne',
      mul_one]

theorem sinkhorn_aposteriori_i_thm : Claims.sinkhorn_aposteriori_i := by
  intro n m ε a b C fs gs f hn hm hε ha hb hsol
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero m := ⟨hm.ne'⟩
  set lam := Real.tanh (deltaC C / (4 * ε))
  refine ⟨?_, div_one_sub_tanh_sq _ _⟩
  set u : Fin n → ℝ := fun i => Real.exp (f i / ε)
  set us : Fin n → ℝ := fun i => Real.exp (fs i / ε)
  set vs : Fin m → ℝ := fun j => Real.exp (gs j / ε)
  set vf : Fin m → ℝ := fun j => Real.exp (colStep ε b C f j / ε)
  have hu : ∀ i, 0 < u i := fun _ => Real.exp_pos _
  have hus : ∀ i, 0 < us i := fun _ => Real.exp_pos _
  have hvs : ∀ j, 0 < vs j := fun _ => Real.exp_pos _
  have hvf : ∀ j, 0 < vf j := fun _ => Real.exp_pos _
  have hK : ∀ (w : Fin m → ℝ), (∀ j, 0 < w j) → ∀ i, 0 < matVec (gibbs ε C) w i :=
    fun w hw => matVec_pos (fun _ _ => gibbs_pos _ _) hw
  have hKT : ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → ∀ j, 0 < matVec (gibbsT ε C) w j :=
    fun w hw => matVec_pos (fun _ _ => gibbs_pos _ _) hw
  obtain ⟨hus_eq, hvs_eq⟩ := dualSol_scaling hε hsol
  have hvf_eq : vf = fun j => b j / matVec (gibbsT ε C) u j := funext (exp_colStep hε hb f)
  have hr : rowSum (planFG ε C f (colStep ε b C f)) = fun i => u i * matVec (gibbs ε C) vf i :=
    funext (rowSum_planFG hε f _)
  -- `d_H(u, a/(𝖪v^f)) = d_H(r(f), a)`
  have h1 : hilb u (fun i => a i / matVec (gibbs ε C) vf i) = hilb (rowSum (planFG ε C f (colStep ε b C f))) a := by
    rw [hr]; exact hilb_div_eq hu (hK vf hvf) ha
  -- `d_H(a/(𝖪v^f), u*) ≤ λ² d_H(u, u*)`
  have h2 : hilb (fun i => a i / matVec (gibbs ε C) vf i) us ≤ lam ^ 2 * hilb u us := by
    have e1 : hilb (fun i => a i / matVec (gibbs ε C) vf i) us = hilb (matVec (gibbs ε C) vf) (matVec (gibbs ε C) vs) := by
      rw [show us = fun i => a i / matVec (gibbs ε C) vs i from hus_eq]
      exact hilb_div_left ha (hK vf hvf) (hK vs hvs)
    have e2 : hilb vf vs = hilb (matVec (gibbsT ε C) u) (matVec (gibbsT ε C) us) := by
      rw [hvf_eq, show vs = fun j => b j / matVec (gibbsT ε C) us j from hvs_eq]
      exact hilb_div_left hb (hKT u hu) (hKT us hus)
    rw [e1]
    calc _ ≤ lam * hilb vf vs := birkhoff_gibbs hε hvf hvs
      _ = lam * hilb (matVec (gibbsT ε C) u) (matVec (gibbsT ε C) us) := by rw [e2]
      _ ≤ lam * (lam * hilb u us) := mul_le_mul_of_nonneg_left (birkhoff_gibbsT hε hu hus) (lam_nonneg hε)
      _ = lam ^ 2 * hilb u us := by ring
  have htri := hilb_triangle u (fun i => a i / matVec (gibbs ε C) vf i) us
  rw [h1] at htri
  have hl2 : lam ^ 2 < 1 := tanh_sq_lt_one _
  have hmain : hilb u us ≤ hilb (rowSum (planFG ε C f (colStep ε b C f))) a / (1 - lam ^ 2) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  rw [osc_eq_hilb hε]
  calc ε * hilb u us ≤ ε * (hilb (rowSum (planFG ε C f (colStep ε b C f))) a / (1 - lam ^ 2)) :=
        mul_le_mul_of_nonneg_left hmain hε.le
    _ = _ := by ring

theorem sinkhorn_aposteriori_ii_thm : Claims.sinkhorn_aposteriori_ii := by
  intro n m ε a b C fs gs g hn hm hε ha hb hsol
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero m := ⟨hm.ne'⟩
  intro f lam d
  have hd_def : d = hilb (colSum (planFG ε C f g)) b := rfl
  set u : Fin n → ℝ := fun i => Real.exp (f i / ε)
  set us : Fin n → ℝ := fun i => Real.exp (fs i / ε)
  set v : Fin m → ℝ := fun j => Real.exp (g j / ε)
  set vs : Fin m → ℝ := fun j => Real.exp (gs j / ε)
  have hu : ∀ i, 0 < u i := fun _ => Real.exp_pos _
  have hus : ∀ i, 0 < us i := fun _ => Real.exp_pos _
  have hv : ∀ j, 0 < v j := fun _ => Real.exp_pos _
  have hvs : ∀ j, 0 < vs j := fun _ => Real.exp_pos _
  have hK : ∀ (w : Fin m → ℝ), (∀ j, 0 < w j) → ∀ i, 0 < matVec (gibbs ε C) w i :=
    fun w hw => matVec_pos (fun _ _ => gibbs_pos _ _) hw
  have hKT : ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → ∀ j, 0 < matVec (gibbsT ε C) w j :=
    fun w hw => matVec_pos (fun _ _ => gibbs_pos _ _) hw
  obtain ⟨hus_eq, hvs_eq⟩ := dualSol_scaling hε hsol
  have hu_eq : u = fun i => a i / matVec (gibbs ε C) v i := funext (exp_rowStep hε ha g)
  set v' : Fin m → ℝ := fun j => b j / matVec (gibbsT ε C) u j
  have hv' : ∀ j, 0 < v' j := fun j => div_pos (hb j) (hKT u hu j)
  have hlam0 : 0 ≤ lam := lam_nonneg hε
  have hl2 : lam ^ 2 < 1 := tanh_sq_lt_one _
  -- `d = d_H(v, v')`
  have hd : d = hilb v v' := by
    rw [hd_def, show colSum (planFG ε C f g) = fun j => v j * matVec (gibbsT ε C) u j from
      funext (colSum_planFG hε f g)]
    exact (hilb_div_eq hv (hKT u hu) hb).symm
  -- `d_H(u, u*) = d_H(𝖪v, 𝖪v*)`
  have hUU : hilb u us = hilb (matVec (gibbs ε C) v) (matVec (gibbs ε C) vs) := by
    rw [hu_eq, show us = fun i => a i / matVec (gibbs ε C) vs i from hus_eq]
    exact hilb_div_left ha (hK v hv) (hK vs hvs)
  have hV'V : hilb v' vs ≤ lam * hilb u us := by
    have : hilb v' vs = hilb (matVec (gibbsT ε C) u) (matVec (gibbsT ε C) us) := by
      rw [show vs = fun j => b j / matVec (gibbsT ε C) us j from hvs_eq]
      exact hilb_div_left hb (hKT u hu) (hKT us hus)
    rw [this]; exact birkhoff_gibbsT hε hu hus
  have hUV : hilb u us ≤ lam * hilb v vs := by rw [hUU]; exact birkhoff_gibbs hε hv hvs
  have hVV : hilb v vs ≤ d / (1 - lam ^ 2) := by
    have htri := hilb_triangle v v' vs
    rw [← hd] at htri
    rw [le_div_iff₀ (by linarith)]
    have : hilb v' vs ≤ lam ^ 2 * hilb v vs := by
      calc hilb v' vs ≤ lam * hilb u us := hV'V
        _ ≤ lam * (lam * hilb v vs) := mul_le_mul_of_nonneg_left hUV hlam0
        _ = lam ^ 2 * hilb v vs := by ring
    nlinarith
  have hUmain : hilb u us ≤ lam * d / (1 - lam ^ 2) := by
    calc hilb u us ≤ lam * hilb v vs := hUV
      _ ≤ lam * (d / (1 - lam ^ 2)) := mul_le_mul_of_nonneg_left hVV hlam0
      _ = lam * d / (1 - lam ^ 2) := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [osc_eq_hilb hε]
    calc ε * hilb u us ≤ ε * (lam * d / (1 - lam ^ 2)) := mul_le_mul_of_nonneg_left hUmain hε.le
      _ = ε * lam / (1 - lam ^ 2) * d := by ring
  · rw [tanh_div_one_sub_tanh_sq]; congr 2; ring
  · -- `v^f = v'`, `a = u ⊙ 𝖪v`, so `d_H(r(f), a) = d_H(𝖪v', 𝖪v) ≤ λ d`
    have hvf : (fun j => Real.exp (colStep ε b C f j / ε)) = v' := funext (exp_colStep hε hb f)
    have hr : rowSum (planFG ε C f (colStep ε b C f)) = fun i => u i * matVec (gibbs ε C) v' i := by
      rw [← hvf]; exact funext (rowSum_planFG hε f _)
    have ha_eq : a = fun i => u i * matVec (gibbs ε C) v i := by
      ext i; rw [hu_eq]; simp only
      rw [div_mul_cancel₀ _ (hK v hv i).ne']
    have hra : hilb (rowSum (planFG ε C f (colStep ε b C f))) a ≤ lam * d := by
      rw [hr]; nth_rewrite 1 [ha_eq]
      rw [hilb_mul_left hu (hK v' hv') (hK v hv), hd, hilb_symm v v']
      exact birkhoff_gibbs hε hv' hv
    have hpos : 0 ≤ ε / (1 - lam ^ 2) := div_nonneg hε.le (by linarith)
    calc ε / (1 - lam ^ 2) * hilb (rowSum (planFG ε C f (colStep ε b C f))) a
        ≤ ε / (1 - lam ^ 2) * (lam * d) := mul_le_mul_of_nonneg_left hra hpos
      _ = ε * lam / (1 - lam ^ 2) * d := by ring

end Sinkhorn

end StatFormal.Wave23d
