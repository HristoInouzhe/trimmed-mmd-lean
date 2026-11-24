import StatFormal.Archive.WaveP1d.Statements
import StatFormal.Archive.Wave11b.RouteSwor
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Route: ICL `prop:swor-score`, the derivative bounds `C₁/n`, `C₂/n` (untrusted)

The paper's proof ("Derivatives", "Application"), along a real parameter `t`:
* `C2B U g g₁ g₂ b₀ b₁ b₂`: `g` twice differentiable on `U` with `|g| ≤ b₀`, `|g'| ≤ b₁`, `|g''| ≤ b₂`; closed under
  sums, products (Leibniz), constant multiples and `1/g` for `g ≥ lo > 0`.
* The i.i.d. tuple law is `exp G_j(t)`, `G_j = Σ_k log s_t(z_{j_k}) − M log Σ_l s_t(z_l)`, with `|G_j'| ≤ 2Mb₁/s₋ =: A₁`
  and `|G_j''| ≤ 2M(b₂/s₋ + (b₁/s₋)²) =: A₂`; so every `Σ_{j∈T} q_j f_j` is `C2B` with bounds `(F, A₁F, (A₁²+A₂)F)·P`,
  `P ≥ Σ_T q_j` — for `T = D^c` the collision mass `p ≤ P := M(M−1)s₊/(2s₋n) ≤ ½` (certified `collision_score`).
* `E°f − Ef = (pEf − N_f)/(1 − p)` (certified `perturb`) is `C2B` with bounds `(4, 10A₁, 42A₁² + 18A₂)·F·P`.
* Coverage: `log(u + R) − log u` with `u = Eφ`, `u + R = E°φ ∈ [K_min, K_max]` is `C2B` with bounds `O(P)` (`logdiff`).
* `J_{n,m} − J^iid_{n,m}` is the average of these (certified decomposition of the Wave 11b `swor_value` route; the
  `KL` terms cancel), so its derivatives are bounded by `C₁P·n/n` and `C₂P·n/n`.
-/

set_option linter.style.longLine false

noncomputable section
open Finset

namespace StatFormal.WaveP1d

namespace RouteSwor

/-- `g` is twice differentiable on `U` with derivatives `g1`, `g2`, and `|g| ≤ b0`, `|g1| ≤ b1`, `|g2| ≤ b2` there. -/
structure C2B (U : Set ℝ) (g g1 g2 : ℝ → ℝ) (b0 b1 b2 : ℝ) : Prop where
  d1 : ∀ t ∈ U, HasDerivAt g (g1 t) t
  d2 : ∀ t ∈ U, HasDerivAt g1 (g2 t) t
  h0 : ∀ t ∈ U, |g t| ≤ b0
  h1 : ∀ t ∈ U, |g1 t| ≤ b1
  h2 : ∀ t ∈ U, |g2 t| ≤ b2

namespace C2B

variable {U : Set ℝ} {f f1 f2 g g1 g2 : ℝ → ℝ} {a0 a1 a2 b0 b1 b2 : ℝ}

lemma mono (h : C2B U f f1 f2 a0 a1 a2) (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) :
    C2B U f f1 f2 b0 b1 b2 :=
  ⟨h.d1, h.d2, fun t ht => (h.h0 t ht).trans h0, fun t ht => (h.h1 t ht).trans h1,
    fun t ht => (h.h2 t ht).trans h2⟩

lemma const (c : ℝ) : C2B U (fun _ => c) (fun _ => 0) (fun _ => 0) |c| 0 0 :=
  ⟨fun t _ => hasDerivAt_const t c, fun t _ => hasDerivAt_const t 0, fun _ _ => le_rfl,
    fun _ _ => by simp, fun _ _ => by simp⟩

lemma add (hf : C2B U f f1 f2 a0 a1 a2) (hg : C2B U g g1 g2 b0 b1 b2) :
    C2B U (fun t => f t + g t) (fun t => f1 t + g1 t) (fun t => f2 t + g2 t) (a0 + b0) (a1 + b1) (a2 + b2) :=
  ⟨fun t ht => (hf.d1 t ht).add (hg.d1 t ht), fun t ht => (hf.d2 t ht).add (hg.d2 t ht),
    fun t ht => (abs_add_le _ _).trans (add_le_add (hf.h0 t ht) (hg.h0 t ht)),
    fun t ht => (abs_add_le _ _).trans (add_le_add (hf.h1 t ht) (hg.h1 t ht)),
    fun t ht => (abs_add_le _ _).trans (add_le_add (hf.h2 t ht) (hg.h2 t ht))⟩

lemma sub (hf : C2B U f f1 f2 a0 a1 a2) (hg : C2B U g g1 g2 b0 b1 b2) :
    C2B U (fun t => f t - g t) (fun t => f1 t - g1 t) (fun t => f2 t - g2 t) (a0 + b0) (a1 + b1) (a2 + b2) :=
  ⟨fun t ht => (hf.d1 t ht).sub (hg.d1 t ht), fun t ht => (hf.d2 t ht).sub (hg.d2 t ht),
    fun t ht => (abs_sub _ _).trans (add_le_add (hf.h0 t ht) (hg.h0 t ht)),
    fun t ht => (abs_sub _ _).trans (add_le_add (hf.h1 t ht) (hg.h1 t ht)),
    fun t ht => (abs_sub _ _).trans (add_le_add (hf.h2 t ht) (hg.h2 t ht))⟩

lemma const_mul (c : ℝ) (hf : C2B U f f1 f2 a0 a1 a2) :
    C2B U (fun t => c * f t) (fun t => c * f1 t) (fun t => c * f2 t) (|c| * a0) (|c| * a1) (|c| * a2) :=
  ⟨fun t ht => (hf.d1 t ht).const_mul c, fun t ht => (hf.d2 t ht).const_mul c,
    fun t ht => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hf.h0 t ht) (abs_nonneg c),
    fun t ht => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hf.h1 t ht) (abs_nonneg c),
    fun t ht => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hf.h2 t ht) (abs_nonneg c)⟩

lemma mul (hf : C2B U f f1 f2 a0 a1 a2) (hg : C2B U g g1 g2 b0 b1 b2) :
    C2B U (fun t => f t * g t) (fun t => f1 t * g t + f t * g1 t)
      (fun t => f2 t * g t + 2 * (f1 t * g1 t) + f t * g2 t)
      (a0 * b0) (a1 * b0 + a0 * b1) (a2 * b0 + 2 * (a1 * b1) + a0 * b2) := by
  refine ⟨fun t ht => (hf.d1 t ht).mul (hg.d1 t ht), fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
    fun t ht => ?_⟩
  · have := ((hf.d2 t ht).mul (hg.d1 t ht)).add ((hf.d1 t ht).mul (hg.d2 t ht))
    convert this using 1; ring
  · rw [abs_mul]
    exact mul_le_mul (hf.h0 t ht) (hg.h0 t ht) (abs_nonneg _) ((abs_nonneg _).trans (hf.h0 t ht))
  · have ha0 := (abs_nonneg _).trans (hf.h0 t ht)
    calc |f1 t * g t + f t * g1 t| ≤ |f1 t| * |g t| + |f t| * |g1 t| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ a1 * b0 + a0 * b1 := add_le_add
          (mul_le_mul (hf.h1 t ht) (hg.h0 t ht) (abs_nonneg _) ((abs_nonneg _).trans (hf.h1 t ht)))
          (mul_le_mul (hf.h0 t ht) (hg.h1 t ht) (abs_nonneg _) ha0)
  · have ha0 := (abs_nonneg _).trans (hf.h0 t ht)
    have ha1 := (abs_nonneg _).trans (hf.h1 t ht)
    have ha2 := (abs_nonneg _).trans (hf.h2 t ht)
    calc |f2 t * g t + 2 * (f1 t * g1 t) + f t * g2 t|
        ≤ |f2 t| * |g t| + 2 * (|f1 t| * |g1 t|) + |f t| * |g2 t| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
          · rw [abs_mul]
          · rw [abs_mul, abs_mul, abs_two]
          · rw [abs_mul]
      _ ≤ a2 * b0 + 2 * (a1 * b1) + a0 * b2 := by
          gcongr
          · exact hf.h2 t ht
          · exact hg.h0 t ht
          · exact hf.h1 t ht
          · exact hg.h1 t ht
          · exact hf.h0 t ht
          · exact hg.h2 t ht

lemma inv {lo : ℝ} (hlo : 0 < lo) (hg : C2B U g g1 g2 b0 b1 b2) (hpos : ∀ t ∈ U, lo ≤ g t) :
    C2B U (fun t => 1 / g t) (fun t => -g1 t / g t ^ 2) (fun t => (2 * g1 t ^ 2 - g t * g2 t) / g t ^ 3)
      (1 / lo) (b1 / lo ^ 2) ((2 * b1 ^ 2 + b0 * b2) / lo ^ 3) := by
  have hg0 : ∀ t ∈ U, g t ≠ 0 := fun t ht => (hlo.trans_le (hpos t ht)).ne'
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · have := (hasDerivAt_const t (1 : ℝ)).div (hg.d1 t ht) (hg0 t ht)
    convert this using 1; ring
  · have hd := ((hg.d2 t ht).neg).div ((hg.d1 t ht).pow 2) (pow_ne_zero 2 (hg0 t ht))
    convert hd using 1
    have := hg0 t ht
    simp only [Pi.pow_apply, Pi.neg_apply]
    field_simp
    push_cast
    ring
  · have := hpos t ht
    rw [abs_div, abs_one, abs_of_pos (hlo.trans_le this)]
    exact one_div_le_one_div_of_le hlo this
  · have hgt := hpos t ht
    have hgp : 0 < g t := hlo.trans_le hgt
    rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < g t ^ 2)]
    have : lo ^ 2 ≤ g t ^ 2 := pow_le_pow_left₀ hlo.le hgt 2
    calc |g1 t| / g t ^ 2 ≤ b1 / g t ^ 2 := div_le_div_of_nonneg_right (hg.h1 t ht) (by positivity)
      _ ≤ b1 / lo ^ 2 := div_le_div_of_nonneg_left ((abs_nonneg _).trans (hg.h1 t ht)) (by positivity) this
  · have hgt := hpos t ht
    have hgp : 0 < g t := hlo.trans_le hgt
    rw [abs_div, abs_of_pos (by positivity : 0 < g t ^ 3)]
    have h3 : lo ^ 3 ≤ g t ^ 3 := pow_le_pow_left₀ hlo.le hgt 3
    have hnum : |2 * g1 t ^ 2 - g t * g2 t| ≤ 2 * b1 ^ 2 + b0 * b2 := by
      have e1 : |g1 t| ^ 2 ≤ b1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hg.h1 t ht) 2
      have e2 : |g t| * |g2 t| ≤ b0 * b2 :=
        mul_le_mul (hg.h0 t ht) (hg.h2 t ht) (abs_nonneg _) ((abs_nonneg _).trans (hg.h0 t ht))
      calc |2 * g1 t ^ 2 - g t * g2 t| ≤ |2 * g1 t ^ 2| + |g t * g2 t| := abs_sub _ _
        _ = 2 * |g1 t| ^ 2 + |g t| * |g2 t| := by rw [abs_mul, abs_mul, abs_two, abs_pow]
        _ ≤ _ := by linarith
    calc |2 * g1 t ^ 2 - g t * g2 t| / g t ^ 3 ≤ (2 * b1 ^ 2 + b0 * b2) / g t ^ 3 :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (2 * b1 ^ 2 + b0 * b2) / lo ^ 3 :=
          div_le_div_of_nonneg_left ((abs_nonneg _).trans hnum) (by positivity) h3


lemma sum {ι : Type*} (s : Finset ι) {F F1 F2 : ι → ℝ → ℝ} {B0 B1 B2 : ι → ℝ}
    (h : ∀ i ∈ s, C2B U (F i) (F1 i) (F2 i) (B0 i) (B1 i) (B2 i)) :
    C2B U (fun t => ∑ i ∈ s, F i t) (fun t => ∑ i ∈ s, F1 i t) (fun t => ∑ i ∈ s, F2 i t)
      (∑ i ∈ s, B0 i) (∑ i ∈ s, B1 i) (∑ i ∈ s, B2 i) :=
  ⟨fun t ht => HasDerivAt.fun_sum fun i hi => (h i hi).d1 t ht,
    fun t ht => HasDerivAt.fun_sum fun i hi => (h i hi).d2 t ht,
    fun t ht => (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => (h i hi).h0 t ht),
    fun t ht => (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => (h i hi).h1 t ht),
    fun t ht => (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => (h i hi).h2 t ht)⟩

end C2B

/-- `|Σ_{j∈T} e_j x_j| ≤ X Σ_{j∈T} e_j` for `e ≥ 0`, `|x_j| ≤ X`. -/
lemma abs_wsum_le {ι : Type*} (T : Finset ι) (e x : ι → ℝ) (X : ℝ) (he : ∀ j, 0 ≤ e j)
    (hx : ∀ j ∈ T, |x j| ≤ X) : |∑ j ∈ T, e j * x j| ≤ X * ∑ j ∈ T, e j := by
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
  rw [abs_mul, abs_of_nonneg (he j), mul_comm]
  exact mul_le_mul_of_nonneg_right (hx j hj) (he j)

/-- Weights `q_j = exp G_j` with `G_j' = a_j`, `a_j' = a2_j`: sums `Σ_{j∈T} q_j f_j` are `C²`, with
bounds proportional to the mass `P ≥ Σ_{j∈T} q_j`. -/
lemma weights {U : Set ℝ} {ι : Type*} (T : Finset ι) (G a a2 : ι → ℝ → ℝ) (A1 A2 F P : ℝ)
    (hG : ∀ j, ∀ t ∈ U, HasDerivAt (G j) (a j t) t ∧ HasDerivAt (a j) (a2 j t) t)
    (ha : ∀ j, ∀ t ∈ U, |a j t| ≤ A1 ∧ |a2 j t| ≤ A2) (f : ι → ℝ) (hf : ∀ j, |f j| ≤ F)
    (hF : 0 ≤ F) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hP : ∀ t ∈ U, ∑ j ∈ T, Real.exp (G j t) ≤ P) :
    C2B U (fun t => ∑ j ∈ T, Real.exp (G j t) * f j) (fun t => ∑ j ∈ T, Real.exp (G j t) * (a j t * f j))
      (fun t => ∑ j ∈ T, Real.exp (G j t) * ((a j t ^ 2 + a2 j t) * f j))
      (F * P) (A1 * F * P) ((A1 ^ 2 + A2) * F * P) := by
  have he : ∀ t j, 0 ≤ Real.exp (G j t) := fun t j => (Real.exp_pos _).le
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · refine HasDerivAt.fun_sum fun j _ => ?_
    have := ((hG j t ht).1.exp).mul_const (f j)
    convert this using 1; ring
  · refine HasDerivAt.fun_sum fun j _ => ?_
    have := ((hG j t ht).1.exp).mul (((hG j t ht).2).mul_const (f j))
    convert this using 1; ring
  · refine (abs_wsum_le T _ _ F (he t) fun j _ => hf j).trans ?_
    exact mul_le_mul_of_nonneg_left (hP t ht) hF
  · refine (abs_wsum_le T _ _ (A1 * F) (he t) fun j _ => ?_).trans ?_
    · rw [abs_mul]; exact mul_le_mul (ha j t ht).1 (hf j) (abs_nonneg _) hA1
    · exact mul_le_mul_of_nonneg_left (hP t ht) (by positivity)
  · refine (abs_wsum_le T _ _ ((A1 ^ 2 + A2) * F) (he t) fun j _ => ?_).trans ?_
    · rw [abs_mul]
      refine mul_le_mul ?_ (hf j) (abs_nonneg _) (by positivity)
      refine (abs_add_le _ _).trans (add_le_add ?_ (ha j t ht).2)
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (ha j t ht).1 2
    · exact mul_le_mul_of_nonneg_left (hP t ht) (by positivity)


lemma abs_frac_le {x y X Y : ℝ} (hY : 0 < Y) (hx : |x| ≤ X) (hy : Y ≤ y) : |x / y| ≤ X / Y := by
  have hy0 : 0 < y := hY.trans_le hy
  rw [abs_div, abs_of_pos hy0]
  calc |x| / y ≤ X / y := div_le_div_of_nonneg_right hx hy0.le
    _ ≤ X / Y := div_le_div_of_nonneg_left ((abs_nonneg _).trans hx) hY hy

lemma log_sub_le' {a b K : ℝ} (hK : 0 < K) (ha : K ≤ a) (hb : K ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / K := by
  have ha0 : 0 < a := hK.trans_le ha
  have hb0 : 0 < b := hK.trans_le hb
  have h1 : Real.log a - Real.log b ≤ (a - b) / b := by
    rw [← Real.log_div ha0.ne' hb0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    rw [sub_div, div_self hb0.ne']; exact this
  have h2 : Real.log b - Real.log a ≤ (b - a) / a := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    rw [sub_div, div_self ha0.ne']; exact this
  rw [abs_le]
  constructor
  · have : (b - a) / a ≤ |a - b| / K := by
      rw [div_le_div_iff₀ ha0 hK]
      have := le_abs_self (b - a); rw [abs_sub_comm] at this
      nlinarith [abs_nonneg (a - b)]
    linarith
  · have : (a - b) / b ≤ |a - b| / K := by
      rw [div_le_div_iff₀ hb0 hK]
      have := le_abs_self (a - b)
      nlinarith [abs_nonneg (a - b)]
    linarith

/-- `log(u + R) − log u` is `C²` with bounds linear in those of the perturbation `R`. -/
lemma logdiff {U : Set ℝ} {u u1 u2 R R1 R2 : ℝ → ℝ} {U0 U1 U2 r0 r1 r2 Km : ℝ} (hKm : 0 < Km)
    (hu : C2B U u u1 u2 U0 U1 U2) (hR : C2B U R R1 R2 r0 r1 r2) (hulo : ∀ t ∈ U, Km ≤ u t)
    (hvlo : ∀ t ∈ U, Km ≤ u t + R t) :
    C2B U (fun t => Real.log (u t + R t) - Real.log (u t))
      (fun t => (u1 t + R1 t) / (u t + R t) - u1 t / u t)
      (fun t => ((u2 t + R2 t) * (u t + R t) - (u1 t + R1 t) * (u1 t + R1 t)) / (u t + R t) ^ 2 -
        (u2 t * u t - u1 t * u1 t) / u t ^ 2)
      (r0 / Km) ((r1 * U0 + U1 * r0) / Km ^ 2)
      ((r2 * U0 + U2 * r0) / Km ^ 2 + (r1 * U0 + U1 * r0) / Km ^ 2 * ((2 * U1 + r1) / Km)) := by
  have hv := hu.add hR
  have hu0 : ∀ t ∈ U, u t ≠ 0 := fun t ht => (hKm.trans_le (hulo t ht)).ne'
  have hv0 : ∀ t ∈ U, u t + R t ≠ 0 := fun t ht => (hKm.trans_le (hvlo t ht)).ne'
  -- the key bound on the first derivative
  have hD1 : ∀ t ∈ U, |(u1 t + R1 t) / (u t + R t) - u1 t / u t| ≤ (r1 * U0 + U1 * r0) / Km ^ 2 := by
    intro t ht
    have hup := hKm.trans_le (hulo t ht)
    have hvp := hKm.trans_le (hvlo t ht)
    have e : (u1 t + R1 t) / (u t + R t) - u1 t / u t = (R1 t * u t - u1 t * R t) / (u t * (u t + R t)) := by
      field_simp; ring
    rw [e]
    refine abs_frac_le (by positivity) ?_ ?_
    · refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul (hR.h1 t ht) (hu.h0 t ht) (abs_nonneg _) ((abs_nonneg _).trans (hR.h1 t ht)))
        (mul_le_mul (hu.h1 t ht) (hR.h0 t ht) (abs_nonneg _) ((abs_nonneg _).trans (hu.h1 t ht)))
    · rw [sq]; exact mul_le_mul (hulo t ht) (hvlo t ht) hKm.le hup.le
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, hD1, fun t ht => ?_⟩
  · exact ((hv.d1 t ht).log (hv0 t ht)).sub ((hu.d1 t ht).log (hu0 t ht))
  · exact ((hv.d2 t ht).div (hv.d1 t ht) (hv0 t ht)).sub ((hu.d2 t ht).div (hu.d1 t ht) (hu0 t ht))
  · refine (log_sub_le' hKm (hvlo t ht) (hulo t ht)).trans ?_
    rw [add_sub_cancel_left]
    exact div_le_div_of_nonneg_right (hR.h0 t ht) hKm.le
  · have hup := hKm.trans_le (hulo t ht)
    have hvp := hKm.trans_le (hvlo t ht)
    set v := u t + R t
    set v1 := u1 t + R1 t
    set v2 := u2 t + R2 t
    have e : (v2 * v - v1 * v1) / v ^ 2 - (u2 t * u t - u1 t * u1 t) / u t ^ 2 =
        (R2 t * u t - u2 t * R t) / (u t * v) - (v1 / v - u1 t / u t) * (v1 / v + u1 t / u t) := by
      have hvne : u t + R t ≠ 0 := hv0 t ht
      have hune : u t ≠ 0 := hu0 t ht
      simp only [v, v1, v2]
      field_simp; ring
    rw [e]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · refine abs_frac_le (by positivity) ?_ ?_
      · refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul (hR.h2 t ht) (hu.h0 t ht) (abs_nonneg _) ((abs_nonneg _).trans (hR.h2 t ht)))
          (mul_le_mul (hu.h2 t ht) (hR.h0 t ht) (abs_nonneg _) ((abs_nonneg _).trans (hu.h2 t ht)))
      · rw [sq]; exact mul_le_mul (hulo t ht) (hvlo t ht) hKm.le hup.le
    · rw [abs_mul]
      refine mul_le_mul (hD1 t ht) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hD1 t ht))
      have h1 : |v1 / v| ≤ (U1 + r1) / Km :=
        abs_frac_le hKm ((abs_add_le _ _).trans (add_le_add (hu.h1 t ht) (hR.h1 t ht))) (hvlo t ht)
      have h2 : |u1 t / u t| ≤ U1 / Km := abs_frac_le hKm (hu.h1 t ht) (hulo t ht)
      calc |v1 / v + u1 t / u t| ≤ (U1 + r1) / Km + U1 / Km := (abs_add_le _ _).trans (add_le_add h1 h2)
        _ = (2 * U1 + r1) / Km := by ring


/-! ### Score-induced weights -/

section Score

variable {Z : Type*} {n M : ℕ}

/-- `log Π_k w_{j_k}(t) = Σ_k log s_t(z_{j_k}) − M log Σ_l s_t(z_l)`. -/
def Gs (s : ℝ → Z → ℝ) (z : Fin n → Z) (j : Fin M → Fin n) (t : ℝ) : ℝ :=
  ∑ k, Real.log (s t (z (j k))) - M * Real.log (∑ l, s t (z l))

/-- Its derivative. -/
def as1 (s s1 : ℝ → Z → ℝ) (z : Fin n → Z) (j : Fin M → Fin n) (t : ℝ) : ℝ :=
  ∑ k, s1 t (z (j k)) / s t (z (j k)) - M * ((∑ l, s1 t (z l)) / ∑ l, s t (z l))

/-- Its second derivative. -/
def as2 (s s1 s2 : ℝ → Z → ℝ) (z : Fin n → Z) (j : Fin M → Fin n) (t : ℝ) : ℝ :=
  ∑ k, (s2 t (z (j k)) * s t (z (j k)) - s1 t (z (j k)) * s1 t (z (j k))) / s t (z (j k)) ^ 2 -
    M * (((∑ l, s2 t (z l)) * (∑ l, s t (z l)) - (∑ l, s1 t (z l)) * (∑ l, s1 t (z l))) /
      (∑ l, s t (z l)) ^ 2)

lemma iidLaw_wScore {s : ℝ → Z → ℝ} {sm sp : ℝ} (hsm : 0 < sm) (hs : ∀ t x, sm ≤ s t x ∧ s t x ≤ sp)
    (hn : 0 < n) (z : Fin n → Z) (j : Fin M → Fin n) (t : ℝ) :
    StatFormal.ICL.Cond.iidLaw (StatFormal.Wave11b.wScore s z t) M j = Real.exp (Gs s z j t) := by
  have hpos : ∀ x, 0 < s t x := fun x => hsm.trans_le (hs t x).1
  have hS : 0 < ∑ l, s t (z l) := sum_pos (fun l _ => hpos _) ⟨⟨0, hn⟩, mem_univ _⟩
  unfold StatFormal.ICL.Cond.iidLaw StatFormal.Wave11b.wScore Gs
  rw [Real.exp_sub, Real.exp_sum, ← Real.log_pow, Real.exp_log (pow_pos hS M), prod_div_distrib,
    prod_const, card_univ, Fintype.card_fin]
  congr 1
  exact prod_congr rfl fun k _ => (Real.exp_log (hpos _)).symm

lemma Gs_deriv {s s1 s2 : ℝ → Z → ℝ} {sm sp : ℝ} {U : Set ℝ} (hsm : 0 < sm)
    (hs : ∀ t x, sm ≤ s t x ∧ s t x ≤ sp)
    (hd : ∀ x, ∀ t ∈ U, HasDerivAt (fun t => s t x) (s1 t x) t ∧ HasDerivAt (fun t => s1 t x) (s2 t x) t)
    (hn : 0 < n) (z : Fin n → Z) (j : Fin M → Fin n) :
    ∀ t ∈ U, HasDerivAt (Gs s z j) (as1 s s1 z j t) t ∧ HasDerivAt (as1 s s1 z j) (as2 s s1 s2 z j t) t := by
  intro t ht
  have hpos : ∀ t x, 0 < s t x := fun t x => hsm.trans_le (hs t x).1
  have hS : ∀ t, 0 < ∑ l, s t (z l) := fun t => sum_pos (fun l _ => hpos _ _) ⟨⟨0, hn⟩, mem_univ _⟩
  have hSd : HasDerivAt (fun t => ∑ l, s t (z l)) (∑ l, s1 t (z l)) t :=
    HasDerivAt.fun_sum fun l _ => (hd (z l) t ht).1
  have hS1d : HasDerivAt (fun t => ∑ l, s1 t (z l)) (∑ l, s2 t (z l)) t :=
    HasDerivAt.fun_sum fun l _ => (hd (z l) t ht).2
  constructor
  · unfold Gs as1
    refine (HasDerivAt.fun_sum fun k _ => ((hd _ t ht).1.log (hpos t _).ne')).sub
      ((hSd.log (hS t).ne').const_mul (M : ℝ))
  · unfold as1 as2
    refine (HasDerivAt.fun_sum fun k _ => ((hd _ t ht).2.div (hd _ t ht).1 (hpos t _).ne')).sub
      ((hS1d.div hSd (hS t).ne').const_mul (M : ℝ))

lemma abs_sum_card_le {ι : Type*} [Fintype ι] (x : ι → ℝ) (X : ℝ) (hx : ∀ i, |x i| ≤ X) :
    |∑ i, x i| ≤ Fintype.card ι * X := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |x i| ≤ ∑ _i : ι, X := sum_le_sum fun i _ => hx i
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

lemma as_bounds {s s1 s2 : ℝ → Z → ℝ} {sm sp b1 b2 : ℝ} {U : Set ℝ} (hsm : 0 < sm)
    (hs : ∀ t x, sm ≤ s t x ∧ s t x ≤ sp) (hb : ∀ x, ∀ t ∈ U, |s1 t x| ≤ b1 ∧ |s2 t x| ≤ b2)
    (hn : 0 < n) (z : Fin n → Z) (j : Fin M → Fin n) :
    ∀ t ∈ U, |as1 s s1 z j t| ≤ 2 * M * (b1 / sm) ∧
      |as2 s s1 s2 z j t| ≤ 2 * M * (b2 / sm + (b1 / sm) ^ 2) := by
  intro t ht
  have hpos : ∀ x, 0 < s t x := fun x => hsm.trans_le (hs t x).1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set S := ∑ l, s t (z l) with hSdef
  have hSlo : n * sm ≤ S := by
    calc (n : ℝ) * sm = ∑ _l : Fin n, sm := by simp
      _ ≤ S := sum_le_sum fun l _ => (hs t (z l)).1
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity) hSlo
  have hS1 : |∑ l, s1 t (z l)| ≤ n * b1 := by
    have := abs_sum_card_le (fun l => s1 t (z l)) b1 fun l => (hb _ t ht).1
    simpa using this
  have hS2 : |∑ l, s2 t (z l)| ≤ n * b2 := by
    have := abs_sum_card_le (fun l => s2 t (z l)) b2 fun l => (hb _ t ht).2
    simpa using this
  have hb1 : 0 ≤ b1 := (abs_nonneg _).trans (hb (z ⟨0, hn⟩) t ht).1
  have hb2 : 0 ≤ b2 := (abs_nonneg _).trans (hb (z ⟨0, hn⟩) t ht).2
  -- one-point ratios
  have r1 : ∀ x, |s1 t x / s t x| ≤ b1 / sm := fun x => abs_frac_le hsm (hb x t ht).1 (hs t x).1
  have r2 : ∀ x, |(s2 t x * s t x - s1 t x * s1 t x) / s t x ^ 2| ≤ b2 / sm + (b1 / sm) ^ 2 := by
    intro x
    have hx := hpos x
    have e : (s2 t x * s t x - s1 t x * s1 t x) / s t x ^ 2 = s2 t x / s t x - (s1 t x / s t x) ^ 2 := by
      field_simp
    rw [e]
    refine (abs_sub _ _).trans (add_le_add (abs_frac_le hsm (hb x t ht).2 (hs t x).1) ?_)
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (r1 x) 2
  -- the normaliser
  have R1 : |(∑ l, s1 t (z l)) / S| ≤ b1 / sm := by
    have := abs_frac_le (by positivity) hS1 hSlo
    rwa [mul_div_mul_left _ _ hnR.ne'] at this
  have R2 : |((∑ l, s2 t (z l)) * S - (∑ l, s1 t (z l)) * (∑ l, s1 t (z l))) / S ^ 2| ≤
      b2 / sm + (b1 / sm) ^ 2 := by
    have e : ((∑ l, s2 t (z l)) * S - (∑ l, s1 t (z l)) * (∑ l, s1 t (z l))) / S ^ 2 =
        (∑ l, s2 t (z l)) / S - ((∑ l, s1 t (z l)) / S) ^ 2 := by field_simp
    rw [e]
    have h2 := abs_frac_le (by positivity) hS2 hSlo
    rw [mul_div_mul_left _ _ hnR.ne'] at h2
    refine (abs_sub _ _).trans (add_le_add h2 ?_)
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) R1 2
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  constructor
  · unfold as1
    refine (abs_sub _ _).trans ?_
    have h1 := abs_sum_card_le (fun k => s1 t (z (j k)) / s t (z (j k))) (b1 / sm) fun k => r1 _
    rw [Fintype.card_fin] at h1
    rw [abs_mul, abs_of_nonneg hM0]
    have := mul_le_mul_of_nonneg_left R1 hM0
    linarith
  · unfold as2
    refine (abs_sub _ _).trans ?_
    have h1 := abs_sum_card_le (fun k => (s2 t (z (j k)) * s t (z (j k)) - s1 t (z (j k)) * s1 t (z (j k))) /
      s t (z (j k)) ^ 2) _ fun k => r2 _
    rw [Fintype.card_fin] at h1
    rw [abs_mul, abs_of_nonneg hM0]
    have := mul_le_mul_of_nonneg_left R2 hM0
    linarith


/-- Weighted sums along the score family. -/
lemma wsum_C2B {s s1 s2 : ℝ → Z → ℝ} {sm sp b1 b2 : ℝ} {U : Set ℝ} (hsm : 0 < sm)
    (hs : ∀ t x, sm ≤ s t x ∧ s t x ≤ sp)
    (hd : ∀ x, ∀ t ∈ U, HasDerivAt (fun t => s t x) (s1 t x) t ∧ HasDerivAt (fun t => s1 t x) (s2 t x) t)
    (hb : ∀ x, ∀ t ∈ U, |s1 t x| ≤ b1 ∧ |s2 t x| ≤ b2) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (hn : 0 < n) (z : Fin n → Z) (T : Finset (Fin M → Fin n)) (f : (Fin M → Fin n) → ℝ) (F P : ℝ)
    (hf : ∀ j, |f j| ≤ F) (hF : 0 ≤ F)
    (hP : ∀ t ∈ U, ∑ j ∈ T, StatFormal.ICL.Cond.iidLaw (StatFormal.Wave11b.wScore s z t) M j ≤ P) :
    ∃ g1 g2, C2B U (fun t => ∑ j ∈ T, StatFormal.ICL.Cond.iidLaw (StatFormal.Wave11b.wScore s z t) M j * f j)
      g1 g2 (F * P) (2 * M * (b1 / sm) * F * P)
      ((((2 * M * (b1 / sm)) ^ 2 + 2 * M * (b2 / sm + (b1 / sm) ^ 2))) * F * P) := by
  have hsm' := hsm
  have key := weights (U := U) T (fun j => Gs s z j) (fun j => as1 s s1 z j) (fun j => as2 s s1 s2 z j)
    (2 * M * (b1 / sm)) (2 * M * (b2 / sm + (b1 / sm) ^ 2)) F P
    (fun j => Gs_deriv hsm hs hd hn z j) (fun j => as_bounds hsm hs hb hn z j) f hf hF (by positivity)
    (by positivity) (fun t ht => by
      have := hP t ht
      simp only [iidLaw_wScore hsm hs hn z] at this
      exact this)
  have heq : (fun t => ∑ j ∈ T, StatFormal.ICL.Cond.iidLaw (StatFormal.Wave11b.wScore s z t) M j * f j) =
      fun t => ∑ j ∈ T, Real.exp (Gs s z j t) * f j := by
    funext t; simp only [iidLaw_wScore hsm hs hn z]
  rw [heq]
  exact ⟨_, _, key⟩


lemma pert_C2B {s s1 s2 : ℝ → Z → ℝ} {sm sp b1 b2 : ℝ} {U : Set ℝ} (hsm : 0 < sm)
    (hs : ∀ t x, sm ≤ s t x ∧ s t x ≤ sp)
    (hd : ∀ x, ∀ t ∈ U, HasDerivAt (fun t => s t x) (s1 t x) t ∧ HasDerivAt (fun t => s1 t x) (s2 t x) t)
    (hb : ∀ x, ∀ t ∈ U, |s1 t x| ≤ b1 ∧ |s2 t x| ≤ b2) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (hn : 0 < n) (z : Fin n → Z) (f : (Fin M → Fin n) → ℝ) (F P : ℝ)
    (hf : ∀ j, |f j| ≤ F) (hF : 0 ≤ F) (hP0 : 0 ≤ P) (hP1 : P ≤ 1 / 2)
    (hP : ∀ t, StatFormal.Wave11b.collision (StatFormal.Wave11b.wScore s z t) M ≤ P) :
    ∃ g1 g2, C2B U (fun t => StatFormal.Wave11b.swoExp (StatFormal.Wave11b.wScore s z t) M f -
        StatFormal.Wave11b.iidExp (StatFormal.Wave11b.wScore s z t) M f) g1 g2
      (4 * F * P) (10 * (2 * M * (b1 / sm)) * F * P)
      ((42 * (2 * M * (b1 / sm)) ^ 2 + 18 * (2 * M * (b2 / sm + (b1 / sm) ^ 2))) * F * P) := by
  set A1 := 2 * (M : ℝ) * (b1 / sm) with hA1
  set A2 := 2 * (M : ℝ) * (b2 / sm + (b1 / sm) ^ 2) with hA2
  have hA1p : 0 ≤ A1 := by positivity
  have hA2p : 0 ≤ A2 := by positivity
  set Dc := univ.filter (fun j : Fin M → Fin n => ¬ Function.Injective j)
  have hwf := fun t => StatFormal.Wave11b.wScore_facts (z := z) (θ := t) (s := s) hn hsm hs
  have hcol : ∀ t, StatFormal.Wave11b.collision (StatFormal.Wave11b.wScore s z t) M =
      ∑ j ∈ Dc, StatFormal.ICL.Cond.iidLaw (StatFormal.Wave11b.wScore s z t) M j * (fun _ => (1 : ℝ)) j := by
    intro t; simp [StatFormal.Wave11b.collision, Dc]
  obtain ⟨p1, p2, hp⟩ := wsum_C2B hsm hs hd hb hb1 hb2 hn z Dc (fun _ => 1) 1 P (fun _ => by simp) zero_le_one
    (fun t _ => by have := hP t; rw [hcol t] at this; simpa using this)
  obtain ⟨e1, e2, hE⟩ := wsum_C2B hsm hs hd hb hb1 hb2 hn z univ f F 1 hf hF
    (fun t _ => by rw [StatFormal.ICL.Cond.iidLaw_sum _ M (hwf t).2.1])
  obtain ⟨n1, n2, hN⟩ := wsum_C2B hsm hs hd hb hb1 hb2 hn z Dc f F P hf hF (fun t _ => by
    have := hP t; rw [hcol t] at this; simpa using this)
  have hX := (hp.mul hE).sub hN
  have hOM := (C2B.const (U := U) (1 : ℝ)).sub hp
  have hlo : ∀ t ∈ U, (1 / 2 : ℝ) ≤ 1 - ∑ j ∈ Dc, StatFormal.ICL.Cond.iidLaw (StatFormal.Wave11b.wScore s z t) M j *
      (fun _ => (1 : ℝ)) j := by
    intro t _; rw [← hcol t]; linarith [hP t]
  have hI := C2B.inv (by norm_num) hOM hlo
  have hR := hX.mul hI
  have heq : (fun t => StatFormal.Wave11b.swoExp (StatFormal.Wave11b.wScore s z t) M f -
        StatFormal.Wave11b.iidExp (StatFormal.Wave11b.wScore s z t) M f) = fun t =>
      ((∑ j ∈ Dc, StatFormal.ICL.Cond.iidLaw (StatFormal.Wave11b.wScore s z t) M j * (fun _ => (1 : ℝ)) j) *
        (∑ j ∈ univ, StatFormal.ICL.Cond.iidLaw (StatFormal.Wave11b.wScore s z t) M j * f j) -
        ∑ j ∈ Dc, StatFormal.ICL.Cond.iidLaw (StatFormal.Wave11b.wScore s z t) M j * f j) *
      (1 / (1 - ∑ j ∈ Dc, StatFormal.ICL.Cond.iidLaw (StatFormal.Wave11b.wScore s z t) M j * (fun _ => (1 : ℝ)) j)) := by
    funext t
    have hp1 : StatFormal.Wave11b.collision (StatFormal.Wave11b.wScore s z t) M < 1 := by linarith [hP t]
    rw [(StatFormal.Wave11b.perturb _ f F (fun j => ((hwf t).1 j).le) (hwf t).2.1 hp1 hf).1, ← hcol t]
    simp only [StatFormal.Wave11b.iidExp, StatFormal.Wave11b.collisionPart, Dc]
    rw [div_eq_mul_one_div]
  rw [heq]
  have hFP : 0 ≤ F * P := mul_nonneg hF hP0
  have hAFP : 0 ≤ A1 * F * P := by positivity
  have hA2FP : 0 ≤ A2 * F * P := by positivity
  have hAAFP : 0 ≤ A1 ^ 2 * F * P := by positivity
  refine ⟨_, _, hR.mono ?_ ?_ ?_⟩
  · norm_num; nlinarith
  · try simp only [← hA1]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_left hP1 hAFP]
  · try simp only [← hA1]
    norm_num
    have h1 := mul_le_mul_of_nonneg_left hP1 hAAFP
    have h2 := mul_le_mul_of_nonneg_left hP1 hA2FP
    have h3 := mul_le_mul_of_nonneg_left hP1 (mul_nonneg hAAFP hP0)
    nlinarith

end Score


section Assembly

lemma arith_log1 (a K k P κ : ℝ) (ha : 0 ≤ a) (hk : 0 < k) (hK : 0 ≤ K) (hρκ : K / k ≤ κ) (hP : 0 ≤ P) :
    (10 * a * K * P * (K * 1) + a * K * 1 * (4 * K * P)) / k ^ 2 ≤ 14 * a * κ ^ 2 * P := by
  have hρ : 0 ≤ K / k := div_nonneg hK hk.le
  calc (10 * a * K * P * (K * 1) + a * K * 1 * (4 * K * P)) / k ^ 2 = 14 * a * (K / k) ^ 2 * P := by
        field_simp; ring
    _ ≤ 14 * a * κ ^ 2 * P := by gcongr

lemma arith_log2 (a b K k P κ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : 0 < k) (hK : 0 ≤ K) (hρκ : K / k ≤ κ)
    (hP : 0 ≤ P) (hP1 : P ≤ 1 / 2) :
    ((42 * a ^ 2 + 18 * b) * K * P * (K * 1) + (a ^ 2 + b) * K * 1 * (4 * K * P)) / k ^ 2 +
      (10 * a * K * P * (K * 1) + a * K * 1 * (4 * K * P)) / k ^ 2 * ((2 * (a * K * 1) + 10 * a * K * P) / k) ≤
    ((46 * a ^ 2 + 22 * b) * κ ^ 2 + 98 * a ^ 2 * κ ^ 3) * P := by
  set ρ := K / k with hρdef
  have hρ : 0 ≤ ρ := div_nonneg hK hk.le
  have hKρ : K = ρ * k := by rw [hρdef]; field_simp
  have e : ((42 * a ^ 2 + 18 * b) * K * P * (K * 1) + (a ^ 2 + b) * K * 1 * (4 * K * P)) / k ^ 2 +
      (10 * a * K * P * (K * 1) + a * K * 1 * (4 * K * P)) / k ^ 2 * ((2 * (a * K * 1) + 10 * a * K * P) / k) =
      (46 * a ^ 2 + 22 * b) * ρ ^ 2 * P + 14 * a * ρ ^ 2 * P * (2 * a * ρ + 10 * a * ρ * P) := by
    rw [hKρ]; field_simp; ring
  rw [e]
  have h1 : 2 * a * ρ + 10 * a * ρ * P ≤ 7 * a * ρ := by nlinarith [mul_nonneg ha hρ]
  have h2 : 14 * a * ρ ^ 2 * P * (2 * a * ρ + 10 * a * ρ * P) ≤ 14 * a * ρ ^ 2 * P * (7 * a * ρ) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : ρ ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ hρ hρκ 2
  have h4 : ρ ^ 3 ≤ κ ^ 3 := pow_le_pow_left₀ hρ hρκ 3
  have h5 : (46 * a ^ 2 + 22 * b) * ρ ^ 2 * P ≤ (46 * a ^ 2 + 22 * b) * κ ^ 2 * P := by gcongr
  have h6 : 98 * a ^ 2 * ρ ^ 3 * P ≤ 98 * a ^ 2 * κ ^ 3 * P := by gcongr
  nlinarith

open StatFormal.Wave11b StatFormal.ICL StatFormal.ICL.Cond

end Assembly

end RouteSwor

open RouteSwor StatFormal.Wave11b StatFormal.ICL StatFormal.ICL.Cond

theorem swor_derivs : Claims.swor_derivs := by
  intro M sm sp b1 b2 BL κ Λ
  set b1' := max b1 0
  set b2' := max b2 0
  set BL' := max BL 0
  set κ' := max κ 0
  set Λ' := max Λ 0
  set A1 := 2 * (M : ℝ) * (b1' / sm) with hA1
  set A2 := 2 * (M : ℝ) * (b2' / sm + (b1' / sm) ^ 2) with hA2
  set Q := (M : ℝ) * ((M : ℝ) - 1) * sp / (2 * sm) with hQ
  refine ⟨(10 * A1 * BL' + Λ' * (14 * A1 * κ' ^ 2)) * Q,
    ((42 * A1 ^ 2 + 18 * A2) * BL' + Λ' * ((46 * A1 ^ 2 + 22 * A2) * κ' ^ 2 + 98 * A1 ^ 2 * κ' ^ 3)) * Q, ?_⟩
  intro Z n m z zt s s1 s2 L K Kmin Kmax lcov lKL U hM hMn hm hsm hs hd hb hL hsym hKmin hK hκ hlcov hΛle hN
  classical
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hb1' : 0 ≤ b1' := le_max_right _ _
  have hb2' : 0 ≤ b2' := le_max_right _ _
  have hBL' : 0 ≤ BL' := le_max_right _ _
  have hκ' : 0 ≤ κ' := le_max_right _ _
  have hΛ' : 0 ≤ Λ' := le_max_right _ _
  have hA1p : 0 ≤ A1 := by positivity
  have hA2p : 0 ≤ A2 := by positivity
  have hb' : ∀ x, ∀ t ∈ U, |s1 t x| ≤ b1' ∧ |s2 t x| ≤ b2' := fun x t ht =>
    ⟨(hb x t ht).1.trans (le_max_left _ _), (hb x t ht).2.trans (le_max_left _ _)⟩
  -- the collision level `P = M(M−1)s₊/(2s₋n) ≤ 1/2`
  set P := Q / n with hPdef
  have hPeq : P = M * ((M : ℝ) - 1) * sp / (2 * sm * n) := by
    rw [hPdef, hQ]; field_simp
  have hPcol : ∀ t, collision (wScore s z t) M ≤ P := fun t => by
    rw [hPeq]; exact collision_score (θ := t) hn hsm hs
  have hwf := fun t => wScore_facts (z := z) (θ := t) (s := s) hn hsm hs
  have hP0 : 0 ≤ P := (sum_nonneg fun j _ => iidLaw_nonneg (fun l => ((hwf 0).1 l).le) j).trans (hPcol 0)
  have hP1 : P ≤ 1 / 2 := by
    rw [hPeq, div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ hsm).1 hN
    nlinarith
  -- risk terms
  set f : Fin m → (Fin M → Fin n) → ℝ := fun i j => L (zt i) (z ∘ j) with hfdef
  have hf : ∀ i j, |f i j| ≤ BL' := fun i j => by
    rw [abs_of_nonneg (hL _ _).1]; exact (hL _ _).2.trans (le_max_left _ _)
  have hRi := fun i => pert_C2B hsm hs hd hb' hb1' hb2' hn z (f i) BL' P (hf i) hBL' hP0 hP1 hPcol
  choose R1 R2 hR using hRi
  -- coverage terms
  set c : Fin n → (Fin M → Fin n) → ℝ := fun l j =>
    ((univ.filter fun k => j k = l).card : ℝ) / M with hc
  set φ : Fin m → (Fin M → Fin n) → ℝ := fun i j => ∑ l, c l j * K (zt i) (z l) with hφ
  have hc0 : ∀ l j, 0 ≤ c l j := fun l j => by simp only [hc]; positivity
  have hc1 : ∀ j, ∑ l, c l j = 1 := fun j => by
    simp only [hc]; rw [← sum_div, cnt_sum j, div_self hMR.ne']
  have hφb : ∀ i j, Kmin ≤ φ i j ∧ φ i j ≤ Kmax := by
    intro i j
    constructor
    · calc Kmin = ∑ l, c l j * Kmin := by rw [← sum_mul, hc1, one_mul]
        _ ≤ φ i j := sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hK _ _).1 (hc0 l j)
    · calc φ i j ≤ ∑ l, c l j * Kmax := sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hK _ _).2 (hc0 l j)
        _ = Kmax := by rw [← sum_mul, hc1, one_mul]
  have hKmax : 0 ≤ Kmax := hKmin.le.trans ((hφb ⟨0, hm⟩ (fun _ => ⟨0, hn⟩)).1.trans (hφb ⟨0, hm⟩ (fun _ => ⟨0, hn⟩)).2)
  have hφa : ∀ i j, |φ i j| ≤ Kmax := fun i j => by
    rw [abs_of_nonneg (hKmin.le.trans (hφb i j).1)]; exact (hφb i j).2
  have hui := fun i => wsum_C2B hsm hs hd hb' hb1' hb2' hn z univ (φ i) Kmax 1 (hφa i) hKmax
    (fun t _ => by rw [iidLaw_sum _ M (hwf t).2.1])
  choose u1 u2 hu using hui
  have hRφi := fun i => pert_C2B hsm hs hd hb' hb1' hb2' hn z (φ i) Kmax P (hφa i) hKmax hP0 hP1 hPcol
  choose Rφ1 Rφ2 hRφ using hRφi
  have hulo : ∀ i, ∀ t ∈ U, Kmin ≤ ∑ j ∈ univ, iidLaw (wScore s z t) M j * φ i j := fun i t _ =>
    iidExp_ge _ (fun l => ((hwf t).1 l).le) (hwf t).2.1 (φ i) Kmin fun j => (hφb i j).1
  have hvlo : ∀ i, ∀ t ∈ U, Kmin ≤ (∑ j ∈ univ, iidLaw (wScore s z t) M j * φ i j) +
      (swoExp (wScore s z t) M (φ i) - iidExp (wScore s z t) M (φ i)) := fun i t _ => by
    have hp1 : collision (wScore s z t) M < 1 := by linarith [hPcol t]
    have := swoExp_ge _ (fun l => ((hwf t).1 l).le) (hwf t).2.1 hp1 (φ i) Kmin fun j => (hφb i j).1
    have e : (∑ j ∈ univ, iidLaw (wScore s z t) M j * φ i j) = iidExp (wScore s z t) M (φ i) := rfl
    rw [e]; linarith
  have hΛi := fun i => logdiff hKmin (hu i) (hRφ i) (hulo i) (hvlo i)
  have hρ0 : 0 ≤ Kmax / Kmin := div_nonneg hKmax hKmin.le
  have hρκ : Kmax / Kmin ≤ κ' := hκ.trans (le_max_left _ _)
  have hΛ := fun i => (hΛi i).mono (b0 := 4 * Kmax * P / Kmin) (b1 := 14 * A1 * κ' ^ 2 * P)
    (b2 := ((46 * A1 ^ 2 + 22 * A2) * κ' ^ 2 + 98 * A1 ^ 2 * κ' ^ 3) * P) le_rfl ?_ ?_
  rotate_left
  · exact arith_log1 A1 Kmax Kmin P κ' hA1p hKmin hKmax hρκ hP0
  · exact arith_log2 A1 A2 Kmax Kmin P κ' hA1p hA2p hKmin hKmax hρκ hP0 hP1
  have hA := (C2B.sum univ (fun i _ => hR i)).const_mul (1 / (m : ℝ))
  have hB := ((C2B.sum univ (fun i _ => hΛ i)).const_mul (-(1 / (m : ℝ)))).const_mul lcov
  have hT := hA.add hB
  -- the objective difference is the assembled function
  have heq : (fun t => jSwor L K z zt lcov lKL (wScore s z t) - jIid L K z zt lcov lKL (wScore s z t)) =
      fun t => (1 / (m : ℝ)) * (∑ i, (swoExp (wScore s z t) M (f i) - iidExp (wScore s z t) M (f i))) +
        lcov * (-(1 / (m : ℝ)) * ∑ i, (Real.log ((∑ j ∈ univ, iidLaw (wScore s z t) M j * φ i j) +
          (swoExp (wScore s z t) M (φ i) - iidExp (wScore s z t) M (φ i))) -
          Real.log (∑ j ∈ univ, iidLaw (wScore s z t) M j * φ i j))) := by
    funext t
    set w := wScore s z t with hwdef
    obtain ⟨hwpos, hw1, -⟩ := hwf t
    have hΔ : InDeltaM w M := ⟨fun j => (hwpos j).le, hw1, by
      rw [filter_true_of_mem (fun j _ => (hwpos j).ne'), card_univ, Fintype.card_fin]; exact hMn⟩
    have hswo : ∀ i, ∑ l, incl w M l / M * K (zt i) (z l) = swoExp w M (φ i) := by
      intro i
      rw [hφ, swoExp_lin]
      refine sum_congr rfl fun l _ => ?_
      rw [(swor_cps Z n M w L (zt i) z l hΔ hsym).2.2 hM]
    have hiid : ∀ i, ∑ l, w l * K (zt i) (z l) = iidExp w M (φ i) := by
      intro i
      rw [hφ, iidExp_lin]
      refine sum_congr rfl fun l _ => ?_
      rw [iidExp_cnt w hw1 hM l]
    have hdecomp : jSwor L K z zt lcov lKL w - jIid L K z zt lcov lKL w =
        (1 / (m : ℝ)) * ∑ i, (Grisk w M (lossSub L (zt i) z) - ∑ j, iidLaw w M j * L (zt i) (z ∘ j)) +
          lcov * (-(1 / (m : ℝ)) * ∑ i, (Real.log (∑ l, incl w M l / M * K (zt i) (z l)) -
            Real.log (∑ l, w l * K (zt i) (z l)))) := by
      unfold jSwor jIid
      rw [sum_sub_distrib, sum_sub_distrib]
      ring
    rw [hdecomp]
    congr 1
    · congr 1
      refine sum_congr rfl fun i _ => ?_
      rw [(swor_cps Z n M w L (zt i) z ⟨0, hn⟩ hΔ hsym).2.1]
      rfl
    · congr 2
      refine sum_congr rfl fun i _ => ?_
      rw [hswo, hiid]
      have e : (∑ j ∈ univ, iidLaw w M j * φ i j) = iidExp w M (φ i) := rfl
      rw [e, add_sub_cancel]
  rw [heq]
  have hc : ∀ X : ℝ, 1 / (m : ℝ) * (m * X) = X := fun X => by field_simp
  refine ⟨_, _, fun t ht => ⟨hT.d1 t ht, hT.d2 t ht, ?_, ?_⟩⟩
  · refine (hT.h1 t ht).trans ?_
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / m), abs_of_nonneg hlcov]
    rw [hc, hc]
    try simp only [← hA1]
    have hY : 0 ≤ 14 * A1 * κ' ^ 2 * P := by positivity
    have := mul_le_mul_of_nonneg_right (hΛle.trans (le_max_left Λ 0)) hY
    rw [show (10 * A1 * BL' + Λ' * (14 * A1 * κ' ^ 2)) * Q / n =
      10 * A1 * BL' * P + Λ' * (14 * A1 * κ' ^ 2 * P) by rw [hPdef]; ring]
    linarith
  · refine (hT.h2 t ht).trans ?_
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / m), abs_of_nonneg hlcov]
    rw [hc, hc]
    try simp only [← hA1]
    have hY : 0 ≤ ((46 * A1 ^ 2 + 22 * A2) * κ' ^ 2 + 98 * A1 ^ 2 * κ' ^ 3) * P := by positivity
    have := mul_le_mul_of_nonneg_right (hΛle.trans (le_max_left Λ 0)) hY
    rw [show ((42 * A1 ^ 2 + 18 * A2) * BL' + Λ' * ((46 * A1 ^ 2 + 22 * A2) * κ' ^ 2 + 98 * A1 ^ 2 * κ' ^ 3)) * Q / n =
      (42 * A1 ^ 2 + 18 * A2) * BL' * P + Λ' * (((46 * A1 ^ 2 + 22 * A2) * κ' ^ 2 + 98 * A1 ^ 2 * κ' ^ 3) * P) by
      rw [hPdef]; ring]
    linarith

end StatFormal.WaveP1d
