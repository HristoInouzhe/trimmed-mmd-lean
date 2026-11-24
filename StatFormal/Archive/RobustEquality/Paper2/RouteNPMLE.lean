import StatFormal.Archive.RobustEquality.Paper2.RouteSeminorm
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Route for paper2 `thm:npmle`, finite mixture class

Triage: the mixing space `L` is finite (`Fin p`), so the class is
`𝒩 = {Σ_y m_y κ(y, ·) : m ∈ Δ_p}`; for the anchors `x_1..x_n` the functions
`ψ_i(y) = ∫ e^{(f_h(x_i,x) − λ c(x_i,x))/(λε)} κ(y,dx)` enter as any positive `ψ : Fin n → Fin p → ℝ`.
`Lval(m) = (1/n) Σ_i log Σ_y m_y ψ_i(y)`; dual objective `D(v) = −(1/n) Σ_i log v_i` over
`v > 0`, `(1/n) Σ_i v_i ψ_i(y) ≤ 1` for all `y` (`DualFeas`).

Main results:
* `weak_duality`: `Lval m ≤ D v` for every `m ∈ Δ_p` and feasible `v`;
* `exists_max_Lval`: a maximiser `m*` exists on the simplex;
* `foc_npmle`: at any maximiser, `v*_i = 1/Σ_y m*_y ψ_i(y)` is feasible (Lindsay's condition);
* `npmle_duality`: `sup_m Lval = min_v D`, both attained, at `v*`;
* `Phi_convex`: for a finite kernel `κ(y,·) = Σ_k κ_{yk} δ_{ξ_k}`, every
  `Φ_y(z,w,λ) = (λ/n) Σ_i Σ_k κ_{yk} e^{(z_i + ⟪w,ξ_k − x_i⟫² − λ‖ξ_k − x_i‖²)/(λε)} − λ` is jointly
  convex on `ℝⁿ × E × (0,∞)`;
* `correction`: if `V ≥ sup_y (Φ_y/λ + 1)` then `z' = z − λε log max(1,V)` gives a certified bound
  `λ r + λε Lval(m) ≤ λ r − (1/n) Σ z'_i` for every mixture `m`.
-/

noncomputable section
open Finset Real
open StatFormal.Foundations.SemiDiscrete

namespace StatFormal.RobustEquality.Paper2.Route

variable {n p : ℕ}

/-- The probability simplex on `Fin p`. -/
def simplex (p : ℕ) : Set (Fin p → ℝ) := {m | (∀ y, 0 ≤ m y) ∧ ∑ y, m y = 1}

lemma isCompact_simplex (p : ℕ) : IsCompact (simplex p) := by
  have hsub : simplex p ⊆ Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1 := by
    intro m hm y _
    refine ⟨hm.1 y, ?_⟩
    rw [← hm.2]
    exact Finset.single_le_sum (f := m) (fun y _ => hm.1 y) (mem_univ y)
  have hclosed : IsClosed (simplex p) := by
    have : simplex p = (⋂ y, {m : Fin p → ℝ | 0 ≤ m y}) ∩ {m | ∑ y, m y = 1} := by
      ext m; simp [simplex]
    rw [this]
    exact (isClosed_iInter fun y => isClosed_le continuous_const (continuous_apply y)).inter
      (isClosed_eq (continuous_finsetSum _ fun y _ => continuous_apply y) continuous_const)
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hclosed hsub

lemma vertex_mem_simplex (y0 : Fin p) : (fun y => if y = y0 then (1 : ℝ) else 0) ∈ simplex p := by
  refine ⟨fun y => ?_, ?_⟩
  · show (0 : ℝ) ≤ if y = y0 then 1 else 0
    split_ifs <;> norm_num
  · simp

/-- `Lval(m) = (1/n) Σ_i log Σ_y m_y ψ_i(y)`. -/
def Lval (ψ : Fin n → Fin p → ℝ) (m : Fin p → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, Real.log (∑ y, m y * ψ i y)

/-- Dual objective `D(v) = −(1/n) Σ log v_i`. -/
def Dval (v : Fin n → ℝ) : ℝ := -((1 / (n : ℝ)) * ∑ i, Real.log (v i))

/-- Dual feasibility. -/
def DualFeas (ψ : Fin n → Fin p → ℝ) (v : Fin n → ℝ) : Prop :=
  (∀ i, 0 < v i) ∧ ∀ y, (1 / (n : ℝ)) * ∑ i, v i * ψ i y ≤ 1

lemma A_pos {ψ : Fin n → Fin p → ℝ} (hψ : ∀ i y, 0 < ψ i y) {m : Fin p → ℝ}
    (hm : m ∈ simplex p) (i : Fin n) : 0 < ∑ y, m y * ψ i y := by
  obtain ⟨hm0, hm1⟩ := hm
  have hne : ∃ y, 0 < m y := by
    by_contra h
    push Not at h
    have : ∑ y, m y ≤ 0 := Finset.sum_nonpos fun y _ => h y
    linarith
  obtain ⟨y0, hy0⟩ := hne
  exact lt_of_lt_of_le (mul_pos hy0 (hψ i y0)) (Finset.single_le_sum
    (f := fun y => m y * ψ i y) (fun y _ => mul_nonneg (hm0 y) (hψ i y).le) (mem_univ y0))

/-- **Weak duality**. -/
theorem weak_duality (hn : 0 < n) {ψ : Fin n → Fin p → ℝ} (hψ : ∀ i y, 0 < ψ i y)
    {m : Fin p → ℝ} (hm : m ∈ simplex p) {v : Fin n → ℝ} (hv : DualFeas ψ v) :
    Lval ψ m ≤ Dval v := by
  obtain ⟨hv0, hv1⟩ := hv
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set A := fun i => ∑ y, m y * ψ i y
  have hA : ∀ i, 0 < A i := A_pos hψ hm
  have hp0 : ∀ _i : Fin n, (0 : ℝ) ≤ 1 / (n : ℝ) := fun _ => by positivity
  have hp1 : ∑ _i : Fin n, 1 / (n : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hn'.ne'
  have hJ := exp_wavg_le (fun _ : Fin n => 1 / (n : ℝ)) (fun i => Real.log (v i * A i)) hp0 hp1
  simp_rw [Real.exp_log (mul_pos (hv0 _) (hA _))] at hJ
  have hsum : ∑ i, 1 / (n : ℝ) * (v i * A i) ≤ 1 := by
    have : ∑ i, 1 / (n : ℝ) * (v i * A i) = ∑ y, m y * ((1 / (n : ℝ)) * ∑ i, v i * ψ i y) := by
      simp only [A, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    calc ∑ y, m y * ((1 / (n : ℝ)) * ∑ i, v i * ψ i y) ≤ ∑ y, m y * 1 :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hv1 y) (hm.1 y)
      _ = 1 := by rw [Finset.sum_congr rfl fun y _ => mul_one (m y)]; exact hm.2
  have hle := hJ.trans hsum
  have hlog : ∑ i, 1 / (n : ℝ) * Real.log (v i * A i) ≤ 0 := by
    have := Real.log_le_log (Real.exp_pos _) hle
    rwa [Real.log_exp, Real.log_one] at this
  have e : ∑ i, 1 / (n : ℝ) * Real.log (v i * A i) = Lval ψ m - Dval v := by
    simp only [Lval, Dval, A]
    rw [sub_neg_eq_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_mul (hv0 i).ne' (hA i).ne']
    ring
  linarith

lemma continuousOn_Lval {ψ : Fin n → Fin p → ℝ} (hψ : ∀ i y, 0 < ψ i y) :
    ContinuousOn (Lval ψ) (simplex p) := by
  unfold Lval
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => ?_)
  refine ContinuousOn.log ?_ fun m hm => (A_pos hψ hm i).ne'
  exact (continuous_finsetSum _ fun y _ =>
    (continuous_apply y).mul continuous_const).continuousOn

/-- A maximiser of `Lval` on the simplex exists. -/
theorem exists_max_Lval (hp : 0 < p) {ψ : Fin n → Fin p → ℝ} (hψ : ∀ i y, 0 < ψ i y) :
    ∃ ms ∈ simplex p, ∀ m ∈ simplex p, Lval ψ m ≤ Lval ψ ms := by
  obtain ⟨ms, hms, hmax⟩ := (isCompact_simplex p).exists_isMaxOn
    ⟨_, vertex_mem_simplex (⟨0, hp⟩ : Fin p)⟩ (continuousOn_Lval hψ)
  exact ⟨ms, hms, fun m hm => isMaxOn_iff.mp hmax m hm⟩

/-- **First-order (Lindsay) condition**: `(1/n) Σ_i ψ_i(y)/A_i(m*) ≤ 1` at a maximiser. -/
theorem foc_npmle (hn : 0 < n) {ψ : Fin n → Fin p → ℝ} (hψ : ∀ i y, 0 < ψ i y)
    {ms : Fin p → ℝ} (hms : ms ∈ simplex p)
    (hmax : ∀ m ∈ simplex p, Lval ψ m ≤ Lval ψ ms) (y : Fin p) :
    (1 / (n : ℝ)) * ∑ i, ψ i y / ∑ y', ms y' * ψ i y' ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set A := fun i => ∑ y', ms y' * ψ i y'
  have hA : ∀ i, 0 < A i := A_pos hψ hms
  set d := fun i => ψ i y - A i
  set F : ℝ → ℝ := fun t => (1 / (n : ℝ)) * ∑ i, d i / (A i + t * d i)
  have hF0 : F 0 = (1 / (n : ℝ)) * ∑ i, ψ i y / A i - 1 := by
    simp only [F, d, zero_mul, add_zero, sub_div]
    rw [Finset.sum_sub_distrib, mul_sub]
    congr 1
    rw [Finset.sum_congr rfl fun i _ => div_self (hA i).ne', Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
  by_contra hcon
  push Not at hcon
  have hpos : 0 < F 0 := by rw [hF0]; linarith
  have hcont : ContinuousAt F 0 := by
    refine continuousAt_const.mul (tendsto_finsetSum _ fun i _ => ?_)
    refine continuousAt_const.div (continuousAt_const.add (continuousAt_id.mul continuousAt_const))
      ?_
    simp only [zero_mul, add_zero]
    exact (hA i).ne'
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < F t ∧ t ∈ Set.Ioo 0 1 :=
    ((hcont.eventually (lt_mem_nhds hpos)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsGT one_pos)
  obtain ⟨t, hFt, ht0, ht1⟩ := hev.exists
  -- the mixture `m_t = (1 − t) m* + t δ_y`
  set mt : Fin p → ℝ := fun y' => (1 - t) * ms y' + t * (if y' = y then 1 else 0)
  have hmt : mt ∈ simplex p := by
    refine ⟨fun y' => ?_, ?_⟩
    · have := hms.1 y'
      simp only [mt]
      split_ifs <;> nlinarith
    · simp only [mt, Finset.sum_add_distrib, ← Finset.mul_sum, hms.2, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      ring
  have hAt : ∀ i, ∑ y', mt y' * ψ i y' = A i + t * d i := by
    intro i
    simp only [mt, d, A, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hAtpos : ∀ i, 0 < A i + t * d i := fun i => by rw [← hAt]; exact A_pos hψ hmt i
  -- `log(A + t d) − log A ≥ t d/(A + t d)`
  have hlog : ∀ i, t * (d i / (A i + t * d i)) ≤ Real.log (A i + t * d i) - Real.log (A i) := by
    intro i
    have h1 := Real.log_le_sub_one_of_pos (div_pos (hA i) (hAtpos i))
    rw [Real.log_div (hA i).ne' (hAtpos i).ne'] at h1
    have hne := (hAtpos i).ne'
    have : A i / (A i + t * d i) - 1 = -(t * (d i / (A i + t * d i))) := by
      field_simp; ring
    linarith
  have hgain : t * F t ≤ Lval ψ mt - Lval ψ ms := by
    simp only [Lval, hAt, F]
    rw [← mul_sub, ← Finset.sum_sub_distrib, mul_left_comm, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hlog i) (by positivity)
  have := hmax mt hmt
  nlinarith [mul_pos ht0 hFt]

/-- **Duality** `sup_m Lval = min_v D`, attained at `v*_i = 1/A_i(m*)` for any maximiser `m*`. -/
theorem npmle_duality (hn : 0 < n) (hp : 0 < p) {ψ : Fin n → Fin p → ℝ}
    (hψ : ∀ i y, 0 < ψ i y) :
    ∃ ms ∈ simplex p,
      IsGreatest (Lval ψ '' simplex p) (Lval ψ ms) ∧
      IsLeast (Dval '' {v | DualFeas ψ v}) (Lval ψ ms) ∧
      DualFeas ψ (fun i => 1 / ∑ y, ms y * ψ i y) ∧
      Dval (fun i => 1 / ∑ y, ms y * ψ i y) = Lval ψ ms := by
  obtain ⟨ms, hms, hmax⟩ := exists_max_Lval hp hψ
  have hA : ∀ i, 0 < ∑ y, ms y * ψ i y := A_pos hψ hms
  have hfeas : DualFeas ψ (fun i => 1 / ∑ y, ms y * ψ i y) := by
    refine ⟨fun i => by have := hA i; positivity, fun y => ?_⟩
    have := foc_npmle hn hψ hms hmax y
    refine le_trans (le_of_eq ?_) this
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hval : Dval (fun i => 1 / ∑ y, ms y * ψ i y) = Lval ψ ms := by
    simp only [Dval, Lval, one_div, Real.log_inv, Finset.sum_neg_distrib, mul_neg, neg_neg]
  refine ⟨ms, hms, ⟨⟨ms, hms, rfl⟩, ?_⟩, ⟨⟨_, hfeas, hval⟩, ?_⟩, hfeas, hval⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact hmax m hm
  · rintro _ ⟨v, hv, rfl⟩
    exact weak_duality hn hψ hms hv

/-! ### Convexity of the constraint functions -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s : ℕ}

/-- `Φ_y(z, w, λ)` for a finite kernel `κ(y, ·) = Σ_k κ_k δ_{ξ_k}`. -/
def Phi (ε : ℝ) (x : Fin n → E) (κ : Fin s → ℝ) (ξ : Fin s → E) (z : Fin n → ℝ) (w : E)
    (l : ℝ) : ℝ :=
  l / n * ∑ i, ∑ k, κ k * Real.exp ((z i + gexp w l (ξ k - x i)) / (l * ε)) - l

/-- **Joint convexity of `Φ_y`** on `ℝⁿ × E × (0,∞)`. -/
theorem Phi_convex {ε : ℝ} (hε : 0 < ε) (x : Fin n → E) {κ : Fin s → ℝ} (hκ : ∀ k, 0 ≤ κ k)
    (ξ : Fin s → E) :
    ConvexOn ℝ (Set.univ ×ˢ (Set.univ ×ˢ Set.Ioi 0))
      (fun q : (Fin n → ℝ) × E × ℝ => Phi ε x κ ξ q.1 q.2.1 q.2.2) := by
  refine ⟨convex_univ.prod (convex_univ.prod (convex_Ioi 0)), ?_⟩
  rintro ⟨z₁, w₁, l₁⟩ ⟨-, -, hl₁⟩ ⟨z₂, w₂, l₂⟩ ⟨-, -, hl₂⟩ θ η hθ hη hθη
  obtain rfl : η = 1 - θ := by linarith
  simp only [Set.mem_Ioi] at hl₁ hl₂
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  have hθ1 : θ ≤ 1 := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- each term `λ e^{g/(λε)}` is a perspective of `exp`
  have hterm : ∀ i k, (θ * l₁ + (1 - θ) * l₂) *
      Real.exp (((θ • z₁ + (1 - θ) • z₂) i + gexp (θ • w₁ + (1 - θ) • w₂)
        (θ * l₁ + (1 - θ) * l₂) (ξ k - x i)) / ((θ * l₁ + (1 - θ) * l₂) * ε)) ≤
      θ * (l₁ * Real.exp ((z₁ i + gexp w₁ l₁ (ξ k - x i)) / (l₁ * ε))) +
        (1 - θ) * (l₂ * Real.exp ((z₂ i + gexp w₂ l₂ (ξ k - x i)) / (l₂ * ε))) := by
    intro i k
    set g₁ := z₁ i + gexp w₁ l₁ (ξ k - x i)
    set g₂ := z₂ i + gexp w₂ l₂ (ξ k - x i)
    have ht₁ : 0 < l₁ * ε := mul_pos hl₁ hε
    have ht₂ : 0 < l₂ * ε := mul_pos hl₂ hε
    have hP := perspective_le convexOn_exp (x₁ := g₁) (x₂ := g₂) ht₁ ht₂ hθ hθ1
    have hte : θ * (l₁ * ε) + (1 - θ) * (l₂ * ε) = (θ * l₁ + (1 - θ) * l₂) * ε := by ring
    rw [hte] at hP
    have hlpos : 0 < θ * l₁ + (1 - θ) * l₂ := by
      rcases eq_or_lt_of_le hθ with h | h
      · rw [← h]; linarith
      · nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) hl₂.le]
    have htpos : 0 < (θ * l₁ + (1 - θ) * l₂) * ε := mul_pos hlpos hε
    have hmono : ((θ • z₁ + (1 - θ) • z₂) i + gexp (θ • w₁ + (1 - θ) • w₂)
        (θ * l₁ + (1 - θ) * l₂) (ξ k - x i)) ≤ θ * g₁ + (1 - θ) * g₂ := by
      have := gexp_convex (ξ k - x i) (w₁ := w₁) (w₂ := w₂) (l₁ := l₁) (l₂ := l₂) hθ hθ1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, g₁, g₂]
      linarith
    have hexp : Real.exp (((θ • z₁ + (1 - θ) • z₂) i + gexp (θ • w₁ + (1 - θ) • w₂)
        (θ * l₁ + (1 - θ) * l₂) (ξ k - x i)) / ((θ * l₁ + (1 - θ) * l₂) * ε)) ≤
        Real.exp (((θ * l₁ + (1 - θ) * l₂) * ε)⁻¹ • (θ • g₁ + (1 - θ) • g₂)) := by
      refine Real.exp_le_exp.mpr ?_
      simp only [smul_eq_mul]
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr htpos.le)
    have hscale : ∀ (t g : ℝ), 0 < t → t * Real.exp (t⁻¹ • g) / ε =
        t / ε * Real.exp (g / t) := fun t g ht => by
      rw [smul_eq_mul, div_eq_inv_mul g t]; ring
    have key := mul_le_mul_of_nonneg_left hexp htpos.le
    have e0 : (θ * l₁ + (1 - θ) * l₂) * Real.exp (((θ * l₁ + (1 - θ) * l₂) * ε)⁻¹ •
        (θ • g₁ + (1 - θ) • g₂)) = ((θ * l₁ + (1 - θ) * l₂) * ε) *
        Real.exp (((θ * l₁ + (1 - θ) * l₂) * ε)⁻¹ • (θ • g₁ + (1 - θ) • g₂)) / ε := by
      field_simp
    have e1 : l₁ * Real.exp (g₁ / (l₁ * ε)) = (l₁ * ε) * Real.exp ((l₁ * ε)⁻¹ • g₁) / ε := by
      rw [smul_eq_mul, ← div_eq_inv_mul]; field_simp
    have e2 : l₂ * Real.exp (g₂ / (l₂ * ε)) = (l₂ * ε) * Real.exp ((l₂ * ε)⁻¹ • g₂) / ε := by
      rw [smul_eq_mul, ← div_eq_inv_mul]; field_simp
    have hP' := div_le_div_of_nonneg_right hP hε.le
    calc (θ * l₁ + (1 - θ) * l₂) * Real.exp (((θ • z₁ + (1 - θ) • z₂) i +
          gexp (θ • w₁ + (1 - θ) • w₂) (θ * l₁ + (1 - θ) * l₂) (ξ k - x i)) /
            ((θ * l₁ + (1 - θ) * l₂) * ε))
        ≤ (θ * l₁ + (1 - θ) * l₂) * Real.exp (((θ * l₁ + (1 - θ) * l₂) * ε)⁻¹ •
            (θ • g₁ + (1 - θ) • g₂)) := mul_le_mul_of_nonneg_left hexp hlpos.le
      _ = _ := e0
      _ ≤ (θ * ((l₁ * ε) * Real.exp ((l₁ * ε)⁻¹ • g₁)) +
            (1 - θ) * ((l₂ * ε) * Real.exp ((l₂ * ε)⁻¹ • g₂))) / ε := hP'
      _ = θ * (l₁ * Real.exp (g₁ / (l₁ * ε))) + (1 - θ) * (l₂ * Real.exp (g₂ / (l₂ * ε))) := by
          rw [e1, e2]; ring
  unfold Phi
  have hsum : (θ * l₁ + (1 - θ) * l₂) / n * ∑ i, ∑ k, κ k *
      Real.exp (((θ • z₁ + (1 - θ) • z₂) i + gexp (θ • w₁ + (1 - θ) • w₂)
        (θ * l₁ + (1 - θ) * l₂) (ξ k - x i)) / ((θ * l₁ + (1 - θ) * l₂) * ε)) ≤
      θ * (l₁ / n * ∑ i, ∑ k, κ k * Real.exp ((z₁ i + gexp w₁ l₁ (ξ k - x i)) / (l₁ * ε))) +
        (1 - θ) * (l₂ / n * ∑ i, ∑ k, κ k *
          Real.exp ((z₂ i + gexp w₂ l₂ (ξ k - x i)) / (l₂ * ε))) := by
    simp only [div_eq_mul_inv, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have h := mul_le_mul_of_nonneg_left (hterm i k) (mul_nonneg (inv_nonneg.mpr hn0) (hκ k))
    ring_nf at h ⊢
    linarith
  nlinarith [hsum]

/-- **Correction** (certified feasible point): with `v_i = e^{z_i/(λε)}` and `V ≥ (1/n) Σ_i v_i ψ_i(y)`
for all `y`, the point `z' = z − λε log max(1, V)` satisfies, for every mixture `m`,
`λ r + λε Lval(m) ≤ λ r − (1/n) Σ_i z'_i`. -/
theorem correction (hn : 0 < n) {ψ : Fin n → Fin p → ℝ} (hψ : ∀ i y, 0 < ψ i y) {ε l r : ℝ}
    (hε : 0 < ε) (hl : 0 < l) (z : Fin n → ℝ) {V : ℝ}
    (hV : ∀ y, (1 / (n : ℝ)) * ∑ i, Real.exp (z i / (l * ε)) * ψ i y ≤ V)
    {m : Fin p → ℝ} (hm : m ∈ simplex p) :
    l * r + l * ε * Lval ψ m ≤
      l * r - (1 / (n : ℝ)) * ∑ i, (z i - l * ε * Real.log (max 1 V)) := by
  have hτ : 0 < l * ε := mul_pos hl hε
  set M := max 1 V
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  set v : Fin n → ℝ := fun i => Real.exp (z i / (l * ε)) / M
  have hfeas : DualFeas ψ v := by
    refine ⟨fun i => div_pos (Real.exp_pos _) hM, fun y => ?_⟩
    have h := hV y
    have : (1 / (n : ℝ)) * ∑ i, v i * ψ i y =
        ((1 / (n : ℝ)) * ∑ i, Real.exp (z i / (l * ε)) * ψ i y) / M := by
      simp only [v, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, div_le_one hM]
    exact h.trans (le_max_right _ _)
  have hw := weak_duality hn hψ hm hfeas
  have hD : Dval v = (1 / (l * ε)) * ((-(1 / (n : ℝ))) * ∑ i, (z i - l * ε * Real.log M)) := by
    simp only [Dval, v]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_div (Real.exp_pos _).ne' hM.ne', Real.log_exp]
    field_simp
  rw [hD] at hw
  have := mul_le_mul_of_nonneg_left hw hτ.le
  rw [← mul_assoc, mul_one_div_cancel hτ.ne', one_mul] at this
  linarith

end StatFormal.RobustEquality.Paper2.Route
