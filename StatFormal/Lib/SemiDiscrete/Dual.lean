import StatFormal.Archive.RobustEquality.Semidual.Statements
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Compact

/-!
# Semi-discrete entropic OT: the semi-dual objective (component F.C′, part 1)

Setting (`lem:semidual`, robust-equality JASA `supp_proofs.tex:35-105`): a discrete first marginal
`μ = Σ_{i<k} a_i δ_i` on `Fin k` (`a_i > 0`, `Σ a_i = 1`), a probability measure `Q` on a measurable
space `K`, bounded measurable costs `c_i : K → ℝ`, `ε > 0`, the soft-min potential
`g_f = gsoft ε a f c` and the semi-dual objective `J_Q(f) = Σ a_i f_i + ∫ g_f dQ` (`Jdual`).

Main results:
* `gsoft_add_const`, `Jdual_add_const`: `g_{f+t1} = g_f − t`, `J_Q(f + t1) = J_Q(f)`;
* `abs_gsoft_sub_le`: `g_f` is 1-Lipschitz in `f` for the sup norm, uniformly in `y`;
* `Jdual_lipschitz`, `continuous_Jdual`: `|J_Q f − J_Q f'| ≤ 2 ‖f − f'‖`, so `J_Q` is continuous;
* `concaveOn_Jdual`: `J_Q` is concave on `ℝ^k`;
* `exists_max_Jdual`: `J_Q` attains its supremum on `ℝ^k`;
* `foc_Jdual`, `foc_Jdual'`: first-order condition at any maximiser,
  `∫ e^{(f*_i + g_{f*} − c_i)/ε} dQ = 1`, i.e. `e^{−f*_i/ε} = ∫ e^{(g_{f*} − c_i)/ε} dQ`.

Self-contained: the elementary log-sum-exp facts are reproved here (they also appear in the
weak-duality proof file, on which this file deliberately does not depend).
-/

noncomputable section
open Finset MeasureTheory
open StatFormal.RobustEquality.Semidual

namespace StatFormal.Foundations.SemiDiscrete

/-- The semi-dual objective `J_Q(f) = Σ_i a_i f_i + ∫ g_f dQ`. -/
def Jdual {K : Type*} [MeasurableSpace K] {k : ℕ} (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (Q : Measure K) (f : Fin k → ℝ) : ℝ :=
  ∑ i, a i * f i + ∫ y, gsoft ε a f c y ∂Q

section Pointwise

variable {K : Type*} {k : ℕ}

lemma pos_of_sum_eq_one {a : Fin k → ℝ} (hsum : ∑ i, a i = 1) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp at hsum
  · exact h

/-- Log-sum-exp is monotone under a uniform shift. -/
lemma lse_le {a : Fin k → ℝ} (hk : 0 < k) (ha : ∀ i, 0 < a i) (u u' : Fin k → ℝ)
    (D : ℝ) (h : ∀ i, u i ≤ u' i + D) :
    Real.log (∑ i, a i * Real.exp (u i)) ≤ Real.log (∑ i, a i * Real.exp (u' i)) + D := by
  have hne : (univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, mem_univ _⟩
  have hpos : 0 < ∑ i, a i * Real.exp (u i) :=
    Finset.sum_pos (fun i _ => mul_pos (ha i) (Real.exp_pos _)) hne
  have hpos' : 0 < ∑ i, a i * Real.exp (u' i) :=
    Finset.sum_pos (fun i _ => mul_pos (ha i) (Real.exp_pos _)) hne
  have hle : ∑ i, a i * Real.exp (u i) ≤ Real.exp D * ∑ i, a i * Real.exp (u' i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have : Real.exp (u i) ≤ Real.exp D * Real.exp (u' i) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [h i])
    nlinarith [ha i]
  calc Real.log (∑ i, a i * Real.exp (u i))
      ≤ Real.log (Real.exp D * ∑ i, a i * Real.exp (u' i)) := Real.log_le_log hpos hle
    _ = _ := by rw [Real.log_mul (Real.exp_pos _).ne' hpos'.ne', Real.log_exp]; ring

lemma sum_exp_pos {a : Fin k → ℝ} (hk : 0 < k) (ha : ∀ i, 0 < a i) (u : Fin k → ℝ) :
    0 < ∑ i, a i * Real.exp (u i) :=
  Finset.sum_pos (fun i _ => mul_pos (ha i) (Real.exp_pos _)) ⟨⟨0, hk⟩, mem_univ _⟩

/-- `g_f` is 1-Lipschitz in `f` for the sup norm, uniformly in `y`. -/
lemma abs_gsoft_sub_le {ε D : ℝ} {a : Fin k → ℝ} (c : Fin k → K → ℝ) (f f' : Fin k → ℝ) (y : K)
    (hk : 0 < k) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hD : ∀ i, |f i - f' i| ≤ D) :
    |gsoft ε a f c y - gsoft ε a f' c y| ≤ D := by
  unfold gsoft
  have h1 := lse_le hk ha (fun i => (f i - c i y) / ε) (fun i => (f' i - c i y) / ε)
    (D / ε) (fun i => by
      rw [← add_div, div_le_div_iff_of_pos_right hε]; linarith [(abs_le.mp (hD i)).2])
  have h2 := lse_le hk ha (fun i => (f' i - c i y) / ε) (fun i => (f i - c i y) / ε)
    (D / ε) (fun i => by
      rw [← add_div, div_le_div_iff_of_pos_right hε]; linarith [(abs_le.mp (hD i)).1])
  have e1 := mul_le_mul_of_nonneg_right h1 hε.le
  have e2 := mul_le_mul_of_nonneg_right h2 hε.le
  rw [add_mul, div_mul_cancel₀ _ hε.ne'] at e1 e2
  rw [abs_le]
  constructor <;> linarith

/-- Increments: `g_f(y) − g_f(y') ≤ B` whenever `c_i(y) − c_i(y') ≤ B` for all `i`. -/
lemma gsoft_sub_le {ε B : ℝ} {a : Fin k → ℝ} (c : Fin k → K → ℝ) (f : Fin k → ℝ) (y y' : K)
    (hk : 0 < k) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hB : ∀ i, c i y - c i y' ≤ B) :
    gsoft ε a f c y - gsoft ε a f c y' ≤ B := by
  unfold gsoft
  have h := lse_le hk ha (fun i => (f i - c i y') / ε) (fun i => (f i - c i y) / ε)
    (B / ε) (fun i => by
      rw [← add_div, div_le_div_iff_of_pos_right hε]; linarith [hB i])
  have : Real.log (∑ i, a i * Real.exp ((f i - c i y') / ε)) * ε ≤
      (Real.log (∑ i, a i * Real.exp ((f i - c i y) / ε)) + B / ε) * ε :=
    mul_le_mul_of_nonneg_right h hε.le
  rw [add_mul, div_mul_cancel₀ _ hε.ne'] at this
  linarith

/-- `|g_f(y)| ≤ F + B` when `|f_i| ≤ F` and `|c_i(y)| ≤ B`. -/
lemma abs_gsoft_le {ε F B : ℝ} {a : Fin k → ℝ} (c : Fin k → K → ℝ) (f : Fin k → ℝ) (y : K)
    (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1)
    (hF : ∀ i, |f i| ≤ F) (hB : ∀ i, |c i y| ≤ B) :
    |gsoft ε a f c y| ≤ F + B := by
  have hk := pos_of_sum_eq_one hsum
  set C := (F + B) / ε
  have hu : ∀ i, |(f i - c i y) / ε| ≤ C := by
    intro i
    rw [abs_div, abs_of_pos hε]
    refine div_le_div_of_nonneg_right ?_ hε.le
    calc |f i - c i y| ≤ |f i| + |c i y| := abs_sub _ _
      _ ≤ F + B := add_le_add (hF i) (hB i)
  have h0 : Real.log (∑ i, a i * Real.exp ((fun _ => (0 : ℝ)) i)) = 0 := by simp [hsum]
  have h1 := lse_le hk ha (fun i => (f i - c i y) / ε) (fun _ => 0) C
    (fun i => by linarith [(abs_le.mp (hu i)).2])
  have h2 := lse_le hk ha (fun _ => 0) (fun i => (f i - c i y) / ε) C
    (fun i => by linarith [(abs_le.mp (hu i)).1])
  rw [h0] at h1 h2
  have hl : |Real.log (∑ i, a i * Real.exp ((f i - c i y) / ε))| ≤ C := by
    rw [abs_le]; constructor <;> linarith
  unfold gsoft
  rw [abs_mul, abs_neg, abs_of_pos hε]
  calc ε * |Real.log (∑ i, a i * Real.exp ((f i - c i y) / ε))| ≤ ε * C :=
        mul_le_mul_of_nonneg_left hl hε.le
    _ = F + B := by simp only [C]; field_simp

/-- Upper bound `g_f(y) ≤ c_i(y) − f_i − ε log a_i`. -/
lemma gsoft_le_single {ε : ℝ} {a : Fin k → ℝ} (c : Fin k → K → ℝ) (f : Fin k → ℝ) (y : K)
    (hε : 0 < ε) (ha : ∀ i, 0 < a i) (i : Fin k) :
    gsoft ε a f c y ≤ c i y - f i - ε * Real.log (a i) := by
  have hk : 0 < k := Fin.pos i
  have hle : a i * Real.exp ((f i - c i y) / ε) ≤ ∑ j, a j * Real.exp ((f j - c j y) / ε) :=
    Finset.single_le_sum (f := fun j => a j * Real.exp ((f j - c j y) / ε))
      (fun j _ => (mul_pos (ha j) (Real.exp_pos _)).le) (mem_univ i)
  have hlog := Real.log_le_log (mul_pos (ha i) (Real.exp_pos _)) hle
  rw [Real.log_mul (ha i).ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  unfold gsoft
  have := mul_le_mul_of_nonneg_left hlog hε.le
  rw [mul_add, mul_div_cancel₀ _ hε.ne'] at this
  linarith

/-- Shift invariance: `g_{f + t1} = g_f − t`. -/
lemma gsoft_add_const {ε : ℝ} {a : Fin k → ℝ} (c : Fin k → K → ℝ) (f : Fin k → ℝ) (t : ℝ) (y : K)
    (hk : 0 < k) (hε : 0 < ε) (ha : ∀ i, 0 < a i) :
    gsoft ε a (fun i => f i + t) c y = gsoft ε a f c y - t := by
  unfold gsoft
  have hsplit : ∑ i, a i * Real.exp ((f i + t - c i y) / ε) =
      Real.exp (t / ε) * ∑ i, a i * Real.exp ((f i - c i y) / ε) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (f i + t - c i y) / ε = t / ε + (f i - c i y) / ε by ring, Real.exp_add]
    ring
  rw [hsplit, Real.log_mul (Real.exp_pos _).ne' (sum_exp_pos hk ha _).ne', Real.log_exp]
  field_simp
  ring

lemma measurable_gsoft' [MeasurableSpace K] (ε : ℝ) (a f : Fin k → ℝ) (c : Fin k → K → ℝ)
    (hc : ∀ i, Measurable (c i)) : Measurable (gsoft ε a f c) := by
  unfold gsoft
  refine Measurable.const_mul (Measurable.log ?_) _
  exact Finset.measurable_sum _ fun i _ =>
    ((((hc i).const_sub (f i)).div_const ε).exp).const_mul (a i)

/-- Jensen for `exp` with weights summing to one (via `e^x ≥ 1 + x`). -/
lemma exp_wavg_le (p d : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    Real.exp (∑ i, p i * d i) ≤ ∑ i, p i * Real.exp (d i) := by
  set D := ∑ i, p i * d i
  have h1 : ∑ i, p i * (d i - D + 1) = 1 := by
    have : ∑ i, p i * (d i - D + 1) = ∑ i, p i * d i - (∑ i, p i) * D + ∑ i, p i := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hp1]; ring
  calc Real.exp D = Real.exp D * ∑ i, p i * (d i - D + 1) := by rw [h1, mul_one]
    _ = ∑ i, p i * (Real.exp D * (d i - D + 1)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i, p i * (Real.exp D * Real.exp (d i - D)) := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hp i)
        exact mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
    _ = ∑ i, p i * Real.exp (d i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Real.exp_add]; ring_nf

/-- Supporting-hyperplane inequality for log-sum-exp (convexity). -/
lemma lse_ge {a : Fin k → ℝ} (hk : 0 < k) (ha : ∀ i, 0 < a i) (u u' : Fin k → ℝ) :
    Real.log (∑ i, a i * Real.exp (u i)) +
        ∑ i, (a i * Real.exp (u i) / ∑ j, a j * Real.exp (u j)) * (u' i - u i) ≤
      Real.log (∑ i, a i * Real.exp (u' i)) := by
  set S := ∑ j, a j * Real.exp (u j)
  have hS : 0 < S := sum_exp_pos hk ha u
  have hS' : 0 < ∑ j, a j * Real.exp (u' j) := sum_exp_pos hk ha u'
  set p := fun i => a i * Real.exp (u i) / S
  have hp : ∀ i, 0 ≤ p i := fun i => (div_pos (mul_pos (ha i) (Real.exp_pos _)) hS).le
  have hp1 : ∑ i, p i = 1 := by simp only [p]; rw [← Finset.sum_div, div_self hS.ne']
  have hJ := exp_wavg_le p (fun i => u' i - u i) hp hp1
  have hr : ∑ i, p i * Real.exp (u' i - u i) = (∑ j, a j * Real.exp (u' j)) / S := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [p, Real.exp_sub]
    field_simp
  rw [hr] at hJ
  have := Real.log_le_log (Real.exp_pos _) hJ
  rw [Real.log_exp, Real.log_div hS'.ne' hS.ne'] at this
  linarith

/-- Concavity of `f ↦ g_f(y)`. -/
lemma gsoft_concave {ε θ : ℝ} {a : Fin k → ℝ} (c : Fin k → K → ℝ) (f f' : Fin k → ℝ) (y : K)
    (hk : 0 < k) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ * gsoft ε a f c y + (1 - θ) * gsoft ε a f' c y ≤
      gsoft ε a (fun i => θ * f i + (1 - θ) * f' i) c y := by
  set w := fun i => θ * f i + (1 - θ) * f' i
  set u := fun i => (w i - c i y) / ε
  have h1 := lse_ge hk ha u (fun i => (f i - c i y) / ε)
  have h2 := lse_ge hk ha u (fun i => (f' i - c i y) / ε)
  set S := ∑ j, a j * Real.exp (u j)
  have hzero : θ * ∑ i, (a i * Real.exp (u i) / S) * ((f i - c i y) / ε - u i) +
      (1 - θ) * ∑ i, (a i * Real.exp (u i) / S) * ((f' i - c i y) / ε - u i) = 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [u, w]
    field_simp
    ring
  have e1 := mul_le_mul_of_nonneg_left h1 hθ0
  have e2 := mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hθ1)
  have e3 := add_le_add e1 e2
  rw [mul_add, mul_add] at e3
  have hL : Real.log S ≤ θ * Real.log (∑ i, a i * Real.exp ((f i - c i y) / ε)) +
      (1 - θ) * Real.log (∑ i, a i * Real.exp ((f' i - c i y) / ε)) := by linarith
  have hL' := mul_le_mul_of_nonneg_left hL hε.le
  unfold gsoft
  linarith

end Pointwise

section Integral

variable {X : Type*} [MeasurableSpace X]

lemma integrable_of_abs_le {μ : Measure X} [IsFiniteMeasure μ] {h : X → ℝ} (hm : Measurable h)
    (M : ℝ) (hb : ∀ x, |h x| ≤ M) : Integrable h μ :=
  Integrable.of_bound hm.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

lemma integrable_exp_of_le {μ : Measure X} [IsFiniteMeasure μ] {h : X → ℝ} (hm : Measurable h)
    (M : ℝ) (hb : ∀ x, h x ≤ M) : Integrable (fun x => Real.exp (h x)) μ :=
  integrable_of_abs_le hm.exp (Real.exp M) fun x => by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (hb x)

end Integral

/-- Standing hypotheses of the semi-discrete problem: `ε > 0`, positive weights summing to one,
measurable costs bounded by `B`. -/
structure SDHyp {K : Type*} [MeasurableSpace K] {k : ℕ} (ε : ℝ) (a : Fin k → ℝ)
    (c : Fin k → K → ℝ) (B : ℝ) : Prop where
  hε : 0 < ε
  ha : ∀ i, 0 < a i
  hsum : ∑ i, a i = 1
  hc : ∀ i, Measurable (c i)
  hB : ∀ i y, |c i y| ≤ B

section Objective

variable {K : Type*} [MeasurableSpace K] {k : ℕ} {ε B : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ}
  {Q : Measure K}

lemma SDHyp.hk (h : SDHyp ε a c B) : 0 < k := pos_of_sum_eq_one h.hsum

lemma abs_apply_le_norm (f : Fin k → ℝ) (i : Fin k) : |f i| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm f i

lemma SDHyp.abs_gsoft_le (h : SDHyp ε a c B) (f : Fin k → ℝ) (y : K) :
    |gsoft ε a f c y| ≤ ‖f‖ + B :=
  StatFormal.Foundations.SemiDiscrete.abs_gsoft_le c f y h.hε h.ha h.hsum (abs_apply_le_norm f)
    (fun i => h.hB i y)

lemma SDHyp.measurable_gsoft (h : SDHyp ε a c B) (f : Fin k → ℝ) : Measurable (gsoft ε a f c) :=
  measurable_gsoft' ε a f c h.hc

lemma SDHyp.integrable_gsoft (h : SDHyp ε a c B) (f : Fin k → ℝ) [IsFiniteMeasure Q] :
    Integrable (gsoft ε a f c) Q :=
  integrable_of_abs_le (h.measurable_gsoft f) _ (h.abs_gsoft_le f)

/-- `J_Q` is invariant under `f ↦ f + t·1`. -/
theorem Jdual_add_const (h : SDHyp ε a c B) [IsProbabilityMeasure Q] (f : Fin k → ℝ) (t : ℝ) :
    Jdual ε a c Q (fun i => f i + t) = Jdual ε a c Q f := by
  unfold Jdual
  simp_rw [gsoft_add_const c f t _ h.hk h.hε h.ha]
  rw [integral_sub (h.integrable_gsoft f) (integrable_const t), integral_const]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, h.hsum, one_mul, probReal_univ,
    smul_eq_mul]
  ring

/-- `J_Q` is 2-Lipschitz for the sup norm. -/
theorem Jdual_lipschitz (h : SDHyp ε a c B) [IsProbabilityMeasure Q] (f f' : Fin k → ℝ) :
    |Jdual ε a c Q f - Jdual ε a c Q f'| ≤ 2 * dist f f' := by
  have hd : ∀ i, |f i - f' i| ≤ dist f f' := fun i => by
    rw [← Real.dist_eq]; exact dist_le_pi_dist f f' i
  have hlin : |∑ i, a i * f i - ∑ i, a i * f' i| ≤ dist f f' := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ i, (a i * f i - a i * f' i)| ≤ ∑ i, |a i * f i - a i * f' i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, a i * dist f f' := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← mul_sub, abs_mul, abs_of_pos (h.ha i)]
          exact mul_le_mul_of_nonneg_left (hd i) (h.ha i).le
      _ = dist f f' := by rw [← Finset.sum_mul, h.hsum, one_mul]
  have hint : |∫ y, gsoft ε a f c y ∂Q - ∫ y, gsoft ε a f' c y ∂Q| ≤ dist f f' := by
    rw [← integral_sub (h.integrable_gsoft f) (h.integrable_gsoft f'), ← Real.norm_eq_abs]
    have := norm_integral_le_of_norm_le_const (μ := Q)
      (f := fun y => gsoft ε a f c y - gsoft ε a f' c y) (C := dist f f')
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact abs_gsoft_sub_le c f f' y h.hk h.hε h.ha hd)
    simpa using this
  unfold Jdual
  calc |∑ i, a i * f i + ∫ y, gsoft ε a f c y ∂Q - (∑ i, a i * f' i + ∫ y, gsoft ε a f' c y ∂Q)|
      = |(∑ i, a i * f i - ∑ i, a i * f' i) +
          (∫ y, gsoft ε a f c y ∂Q - ∫ y, gsoft ε a f' c y ∂Q)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

theorem continuous_Jdual (h : SDHyp ε a c B) [IsProbabilityMeasure Q] :
    Continuous (Jdual ε a c Q) := by
  refine (LipschitzWith.of_dist_le_mul (K := 2) fun f f' => ?_).continuous
  rw [Real.dist_eq]
  exact_mod_cast Jdual_lipschitz h f f'

/-- `J_Q` is concave on `ℝ^k`. -/
theorem concaveOn_Jdual (h : SDHyp ε a c B) [IsProbabilityMeasure Q] :
    ConcaveOn ℝ Set.univ (Jdual ε a c Q) := by
  refine ⟨convex_univ, fun f _ f' _ θ η hθ hη hθη => ?_⟩
  obtain rfl : η = 1 - θ := by linarith
  have hw : θ • f + (1 - θ) • f' = fun i => θ * f i + (1 - θ) * f' i := by
    ext i; simp
  rw [hw]
  unfold Jdual
  simp only [smul_eq_mul]
  have hlin : ∑ i, a i * (θ * f i + (1 - θ) * f' i) =
      θ * ∑ i, a i * f i + (1 - θ) * ∑ i, a i * f' i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hint : θ * ∫ y, gsoft ε a f c y ∂Q + (1 - θ) * ∫ y, gsoft ε a f' c y ∂Q ≤
      ∫ y, gsoft ε a (fun i => θ * f i + (1 - θ) * f' i) c y ∂Q := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((h.integrable_gsoft f).const_mul _) ((h.integrable_gsoft f').const_mul _)]
    exact integral_mono (((h.integrable_gsoft f).const_mul _).add
      ((h.integrable_gsoft f').const_mul _)) (h.integrable_gsoft _)
      fun y => gsoft_concave c f f' y h.hk h.hε h.ha hθ (by linarith)
  rw [hlin]
  linarith

/-- Coercivity bound: with `m` an index of a maximal coordinate of `f`,
`J_Q(f) ≤ B + C₀ − a_j (f_m − f_j)` for every `j`, where `C₀ = Σ_i |ε log a_i|`. -/
lemma Jdual_le_osc (h : SDHyp ε a c B) [IsProbabilityMeasure Q] (f : Fin k → ℝ) :
    ∃ m, (∀ j, f j ≤ f m) ∧ ∀ j, Jdual ε a c Q f ≤
      B + (∑ i, |ε * Real.log (a i)|) - a j * (f m - f j) := by
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image univ f ⟨⟨0, h.hk⟩, mem_univ _⟩
  have hm' : ∀ j, f j ≤ f m := fun j => hm j (mem_univ j)
  refine ⟨m, hm', fun j => ?_⟩
  set C0 := ∑ i, |ε * Real.log (a i)|
  have hlogm : -(ε * Real.log (a m)) ≤ C0 :=
    (neg_le_abs _).trans (Finset.single_le_sum (f := fun i => |ε * Real.log (a i)|)
      (fun i _ => abs_nonneg _) (mem_univ m))
  have hint : ∫ y, gsoft ε a f c y ∂Q ≤ B - f m + C0 := by
    have := integral_mono (h.integrable_gsoft (Q := Q) f) (integrable_const (B - f m + C0))
      fun y => by
      have h1 := gsoft_le_single c f y h.hε h.ha m
      have h2 := (abs_le.mp (h.hB m y)).2
      show gsoft ε a f c y ≤ B - f m + C0
      linarith
    simpa using this
  have hsum : ∑ l, a l * (f l - f m) ≤ a j * (f j - f m) := by
    rw [← Finset.add_sum_erase _ _ (mem_univ j)]
    have := Finset.sum_nonpos (s := univ.erase j) (f := fun l => a l * (f l - f m))
      (fun l _ => mul_nonpos_of_nonneg_of_nonpos (h.ha l).le (sub_nonpos.mpr (hm' l)))
    linarith
  have hsum' : ∑ l, a l * (f l - f m) = ∑ l, a l * f l - f m := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h.hsum, one_mul]
  unfold Jdual
  linarith

lemma Jdual_zero_ge (h : SDHyp ε a c B) [IsProbabilityMeasure Q] :
    -B ≤ Jdual ε a c Q (fun _ => 0) := by
  unfold Jdual
  have := integral_mono (integrable_const (-B)) (h.integrable_gsoft (Q := Q) (fun _ => 0))
    fun y => by
    have h1 := h.abs_gsoft_le (fun _ => 0) y
    have h0 : ‖(fun _ => (0 : ℝ) : Fin k → ℝ)‖ = 0 := norm_zero (E := Fin k → ℝ)
    rw [h0, zero_add] at h1
    show -B ≤ gsoft ε a (fun _ => 0) c y
    linarith [(abs_le.mp h1).1]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
  simp only [mul_zero, Finset.sum_const_zero, zero_add]
  exact this

/-- **Existence of a maximiser**: `J_Q` attains its supremum on `ℝ^k`. -/
theorem exists_max_Jdual (h : SDHyp ε a c B) (Q : Measure K) [IsProbabilityMeasure Q] :
    ∃ fs : Fin k → ℝ, ∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs := by
  set i0 : Fin k := ⟨0, h.hk⟩
  set C0 := ∑ i, |ε * Real.log (a i)|
  have hC0 : 0 ≤ C0 := Finset.sum_nonneg fun i _ => abs_nonneg _
  set Rj : Fin k → ℝ := fun j => (2 * |B| + C0) / a j
  have hRj : ∀ j, 0 ≤ Rj j := fun j => div_nonneg (by positivity) (h.ha j).le
  set R := ∑ j, Rj j
  have hRR : ∀ j, Rj j ≤ R := fun j =>
    Finset.single_le_sum (f := Rj) (fun j _ => hRj j) (mem_univ j)
  have haR : ∀ j, a j * Rj j = 2 * |B| + C0 := fun j => by
    simp only [Rj]; field_simp [(h.ha j).ne']
  set S : Set (Fin k → ℝ) := Set.univ.pi (fun _ => Set.Icc (-R) R) ∩ {f | f i0 = 0}
  have hS : IsCompact S := (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
    (isClosed_eq (continuous_apply i0) continuous_const)
  have h0S : (fun _ => (0 : ℝ)) ∈ S := by
    refine ⟨fun j _ => ?_, rfl⟩
    have : 0 ≤ R := (hRj j).trans (hRR j)
    exact ⟨by linarith, this⟩
  obtain ⟨fs, -, hmax⟩ := hS.exists_isMaxOn ⟨_, h0S⟩ (continuous_Jdual h (Q := Q)).continuousOn
  have hmax' := isMaxOn_iff.mp hmax
  refine ⟨fs, fun f => ?_⟩
  set f' : Fin k → ℝ := fun i => f i + -f i0
  have hJ : Jdual ε a c Q f = Jdual ε a c Q f' := (Jdual_add_const h f _).symm
  have hf'0 : f' i0 = 0 := by simp [f']
  rw [hJ]
  by_cases hin : ∀ j, |f' j| ≤ R
  · exact hmax' f' ⟨fun j _ => abs_le.mp (hin j), hf'0⟩
  · push Not at hin
    obtain ⟨j, hj⟩ := hin
    obtain ⟨m, hm, hbd⟩ := Jdual_le_osc h (Q := Q) f'
    have hlt : Jdual ε a c Q f' < -B := by
      rcases lt_or_ge (f' j) 0 with hneg | hpos
      · rw [abs_of_neg hneg] at hj
        have h1 := hbd j
        have h2 : a j * Rj j < a j * (f' m - f' j) := by
          refine mul_lt_mul_of_pos_left ?_ (h.ha j)
          have := hm i0; rw [hf'0] at this; linarith [hRR j]
        rw [haR] at h2
        linarith [le_abs_self B]
      · rw [abs_of_nonneg hpos] at hj
        have h1 := hbd i0
        rw [hf'0, sub_zero] at h1
        have h2 : a i0 * Rj i0 < a i0 * f' m := by
          refine mul_lt_mul_of_pos_left ?_ (h.ha i0)
          linarith [hRR i0, hm j]
        rw [haR] at h2
        linarith [le_abs_self B]
    exact hlt.le.trans ((Jdual_zero_ge h (Q := Q)).trans (hmax' _ h0S))

/-- Pointwise lower bound for a perturbation of one coordinate:
`g_{f + t e_i}(y) ≥ g_f(y) − ε a_i (e^{t/ε} − 1) e^{(f_i + g_f(y) − c_i(y))/ε}`. -/
lemma gsoft_single_ge {K : Type*} (hε : 0 < ε) (ha : ∀ i, 0 < a i) (c : Fin k → K → ℝ)
    (f : Fin k → ℝ) (i : Fin k) (t : ℝ) (y : K) :
    gsoft ε a f c y - ε * a i * (Real.exp (t / ε) - 1) *
        Real.exp ((f i + gsoft ε a f c y - c i y) / ε) ≤
      gsoft ε a (fun j => f j + if j = i then t else 0) c y := by
  have hk : 0 < k := Fin.pos i
  set S0 := ∑ j, a j * Real.exp ((f j - c j y) / ε)
  have hS0 : 0 < S0 := sum_exp_pos hk ha _
  set X := a i * Real.exp ((f i - c i y) / ε) * (Real.exp (t / ε) - 1)
  have hSt : ∑ j, a j * Real.exp ((f j + (if j = i then t else 0) - c j y) / ε) = S0 + X := by
    have : S0 + X = ∑ j, (a j * Real.exp ((f j - c j y) / ε) + if j = i then X else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp [S0]
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      simp only [ite_true, X]
      rw [show (f j + t - c j y) / ε = (f j - c j y) / ε + t / ε by ring, Real.exp_add]
      ring
    · simp [hj]
  have hSt_pos : 0 < S0 + X := hSt ▸ sum_exp_pos hk ha _
  have hq : Real.exp ((f i + gsoft ε a f c y - c i y) / ε) = Real.exp ((f i - c i y) / ε) / S0 := by
    have : (f i + gsoft ε a f c y - c i y) / ε = (f i - c i y) / ε - Real.log S0 := by
      simp only [gsoft, S0]; field_simp; ring
    rw [this, Real.exp_sub, Real.exp_log hS0]
  have hlog : Real.log (S0 + X) ≤ Real.log S0 + X / S0 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hSt_pos hS0)
    rw [Real.log_div hSt_pos.ne' hS0.ne'] at h1
    have : (S0 + X) / S0 - 1 = X / S0 := by field_simp; ring
    linarith
  have hlog' := mul_le_mul_of_nonneg_left hlog hε.le
  have hX : ε * a i * (Real.exp (t / ε) - 1) * (Real.exp ((f i - c i y) / ε) / S0) =
      ε * (X / S0) := by simp only [X]; ring
  rw [hq, hX]
  unfold gsoft
  rw [hSt]
  change -ε * Real.log S0 - ε * (X / S0) ≤ -ε * Real.log (S0 + X)
  nlinarith

/-- **First-order condition** at a maximiser `f*` of `J_Q`:
`∫ e^{(f*_i + g_{f*}(y) − c_i(y))/ε} dQ(y) = 1` for every `i`. -/
theorem foc_Jdual (h : SDHyp ε a c B) [IsProbabilityMeasure Q] {fs : Fin k → ℝ}
    (hmax : ∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs) (i : Fin k) :
    ∫ y, Real.exp ((fs i + gsoft ε a fs c y - c i y) / ε) ∂Q = 1 := by
  set E : K → ℝ := fun y => Real.exp ((fs i + gsoft ε a fs c y - c i y) / ε)
  set P := ∫ y, E y ∂Q
  have hEint : Integrable E Q := by
    refine integrable_exp_of_le (((measurable_const.add (h.measurable_gsoft fs)).sub
      (h.hc i)).div_const ε) ((‖fs‖ + (‖fs‖ + B) + B) / ε) fun y => ?_
    refine div_le_div_of_nonneg_right ?_ h.hε.le
    have h1 := abs_apply_le_norm fs i
    have h2 := h.abs_gsoft_le fs y
    have h3 := h.hB i y
    linarith [le_abs_self (fs i), le_abs_self (gsoft ε a fs c y), neg_abs_le (c i y)]
  have key : ∀ t : ℝ, Jdual ε a c Q fs + a i * t - ε * a i * (Real.exp (t / ε) - 1) * P ≤
      Jdual ε a c Q fs := by
    intro t
    refine le_trans ?_ (hmax (fun j => fs j + if j = i then t else 0))
    unfold Jdual
    have hlin : ∑ j, a j * (fs j + if j = i then t else 0) = ∑ j, a j * fs j + a i * t := by
      simp [mul_add, Finset.sum_add_distrib]
    have hint : ∫ y, (gsoft ε a fs c y - ε * a i * (Real.exp (t / ε) - 1) * E y) ∂Q ≤
        ∫ y, gsoft ε a (fun j => fs j + if j = i then t else 0) c y ∂Q :=
      integral_mono ((h.integrable_gsoft (Q := Q) fs).sub (hEint.const_mul
        (ε * a i * (Real.exp (t / ε) - 1)))) (h.integrable_gsoft _)
        (fun y => gsoft_single_ge h.hε h.ha c fs i t y)
    rw [integral_sub (h.integrable_gsoft fs) (hEint.const_mul _), integral_const_mul] at hint
    rw [hlin]
    linarith
  set ψ : ℝ → ℝ := fun t =>
    Jdual ε a c Q fs + a i * t - ε * a i * P * (Real.exp (t / ε) - 1)
  have hψ0 : ψ 0 = Jdual ε a c Q fs := by simp [ψ]
  have hloc : IsLocalMax ψ 0 := Filter.Eventually.of_forall fun t => by
    rw [hψ0]
    have := key t
    simp only [ψ]
    linarith
  have hd1 : HasDerivAt (fun t : ℝ => Real.exp (t / ε)) (Real.exp (0 / ε) * (1 / ε)) 0 :=
    ((hasDerivAt_id' 0).div_const ε).exp
  have hψd : HasDerivAt ψ (a i * 1 - ε * a i * P * (Real.exp (0 / ε) * (1 / ε))) 0 :=
    (((hasDerivAt_id' 0).const_mul (a i)).const_add _).sub ((hd1.sub_const 1).const_mul _)
  have h0 := hloc.hasDerivAt_eq_zero hψd
  rw [zero_div, Real.exp_zero, one_mul] at h0
  have e : ε * a i * P * (1 / ε) = a i * P := by field_simp [h.hε.ne']
  have : a i * (1 - P) = 0 := by
    rw [mul_one, e] at h0; linear_combination h0
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 (h.ha i).ne'
  · linarith

/-- First-order condition, paper form: `e^{−f*_i/ε} = ∫ e^{(g_{f*} − c_i)/ε} dQ`. -/
theorem foc_Jdual' (h : SDHyp ε a c B) [IsProbabilityMeasure Q] {fs : Fin k → ℝ}
    (hmax : ∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs) (i : Fin k) :
    Real.exp (-fs i / ε) = ∫ y, Real.exp ((gsoft ε a fs c y - c i y) / ε) ∂Q := by
  have h1 := foc_Jdual h hmax i
  have hsplit : ∀ y, Real.exp ((fs i + gsoft ε a fs c y - c i y) / ε) =
      Real.exp (fs i / ε) * Real.exp ((gsoft ε a fs c y - c i y) / ε) := fun y => by
    rw [← Real.exp_add]; ring_nf
  simp_rw [hsplit] at h1
  rw [integral_const_mul] at h1
  rw [show -fs i / ε = -(fs i / ε) by ring, Real.exp_neg]
  exact (eq_inv_of_mul_eq_one_right h1).symm

end Objective

end StatFormal.Foundations.SemiDiscrete
