import StatFormal.Lib.SemiDiscrete.Dual
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Function

/-!
# Route for paper2 `thm:seminorm` (finite reference): convexity, homogeneity, seminorm

Setting (paper2 `main.tex:240-340`, triage: a single *finitely supported* sub-probability reference):
real inner-product space `E` (covariates), centre `P̂_s = Σ_i a_i δ_{x_i}` (`a_i ≥ 0`, `Σ a_i = 1`),
reference `ν = Σ_j m_j δ_{y_j}` (`m_j > 0`, `Σ m_j ≤ 1`, at least one atom), linear rule
`h_w = ⟪w, ·⟫`, cost `c(x₀, x) = ‖x − x₀‖²`, `ε > 0`, budget `r`, multiplier `λ > 0`:
`T(w, λ) = λ r + Σ_i a_i · λε · log Σ_j m_j exp{(⟪w, y_j − x_i⟫² − λ‖y_j − x_i‖²)/(λε)}` (`Tfin`).

Main results:
* (i) `Tfin_convex` (joint convexity on `E × (0,∞)`), `Tfin_neg` (even), `Tfin_homog`
  (`T(t w, t² λ) = t² T(w, λ)`);
* `gibbs_fin`: finite Gibbs inequality, whence `Tfin_nonneg` under feasibility of the budget
  (`Feasible`: some kernel `p_i` with `Σ_i a_i (E_{p_i} c + ε KL(p_i‖ν)) ≤ r`, i.e. the set is non-empty);
* (ii) `Nsq = inf_{λ>0} T` (`⨅` over `Ioi 0`, bounded below under feasibility): `Nsq_convex`,
  `Nsq_neg`, `Nsq_homog`, `Nsq_zero`, `Nsq_le` (`≤ r ‖w‖²`), and `seminormN`: `√Nsq` is a
  `Seminorm ℝ E` with `N(w) ≤ √r ‖w‖`;
* (iii) `inf_Fbar`: `inf_{λ₀,λ₁} (Δ + √T₀ + √T₁)² = (Δ + N₀ + N₁)²` for any `Δ ≥ 0`.
Generic tools: `lse` (log-sum-exp) is convex and monotone; `perspective_le` (perspective of a convex
function is jointly convex).
-/

noncomputable section
open Finset Real
open StatFormal.Foundations.SemiDiscrete

namespace StatFormal.RobustEquality.Paper2.Route

/-! ### Log-sum-exp and perspectives -/

section LSE

variable {q : ℕ}

/-- `lse_m(u) = log Σ_j m_j e^{u_j}`. -/
def lse (m u : Fin q → ℝ) : ℝ := Real.log (∑ j, m j * Real.exp (u j))

lemma lse_mono {m : Fin q → ℝ} (hq : 0 < q) (hm : ∀ j, 0 < m j) {u u' : Fin q → ℝ}
    (h : ∀ j, u j ≤ u' j) : lse m u ≤ lse m u' := by
  have := lse_le hq hm u u' 0 (fun j => by simpa using h j)
  simpa [lse] using this

lemma lse_convex {m : Fin q → ℝ} (hq : 0 < q) (hm : ∀ j, 0 < m j) :
    ConvexOn ℝ Set.univ (lse m) := by
  refine ⟨convex_univ, fun u _ u' _ θ η hθ hη hθη => ?_⟩
  set w := θ • u + η • u'
  have h1 := lse_ge hq hm w u
  have h2 := lse_ge hq hm w u'
  set S := ∑ j, m j * Real.exp (w j)
  have hzero : θ * ∑ j, (m j * Real.exp (w j) / S) * (u j - w j) +
      η * ∑ j, (m j * Real.exp (w j) / S) * (u' j - w j) = 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : w j = θ * u j + η * u' j := by simp [w]
    rw [this]
    have hη' : η = 1 - θ := by linarith
    rw [hη']
    ring
  have e1 := mul_le_mul_of_nonneg_left h1 hθ
  have e2 := mul_le_mul_of_nonneg_left h2 hη
  have e3 := add_le_add e1 e2
  rw [mul_add, mul_add] at e3
  simp only [lse, smul_eq_mul]
  have : θ * Real.log S + η * Real.log S = Real.log S := by rw [← add_mul, hθη, one_mul]
  linarith

/-- Perspective of a convex function: `t f(x/t)` is jointly convex on `V × (0,∞)`. -/
theorem perspective_le {V : Type*} [AddCommGroup V] [Module ℝ V] {f : V → ℝ}
    (hf : ConvexOn ℝ Set.univ f) {x₁ x₂ : V} {t₁ t₂ θ : ℝ} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (θ * t₁ + (1 - θ) * t₂) * f ((θ * t₁ + (1 - θ) * t₂)⁻¹ • (θ • x₁ + (1 - θ) • x₂)) ≤
      θ * (t₁ * f (t₁⁻¹ • x₁)) + (1 - θ) * (t₂ * f (t₂⁻¹ • x₂)) := by
  set t := θ * t₁ + (1 - θ) * t₂
  have ht : 0 < t := by
    rcases eq_or_lt_of_le hθ0 with h | h
    · simp only [t, ← h]; linarith
    · have : 0 ≤ (1 - θ) * t₂ := mul_nonneg (by linarith) ht₂.le
      have : 0 < θ * t₁ := mul_pos h ht₁
      linarith
  set α := θ * t₁ / t
  set β := (1 - θ) * t₂ / t
  have hα : 0 ≤ α := div_nonneg (mul_nonneg hθ0 ht₁.le) ht.le
  have hβ : 0 ≤ β := div_nonneg (mul_nonneg (by linarith) ht₂.le) ht.le
  have hαβ : α + β = 1 := by
    simp only [α, β]
    rw [← add_div]
    exact div_self ht.ne'
  have hpt : t⁻¹ • (θ • x₁ + (1 - θ) • x₂) = α • (t₁⁻¹ • x₁) + β • (t₂⁻¹ • x₂) := by
    simp only [α, β, smul_add, smul_smul]
    congr 1
    · congr 1; field_simp
    · congr 1; field_simp
  have hc := hf.2 (Set.mem_univ (t₁⁻¹ • x₁)) (Set.mem_univ (t₂⁻¹ • x₂)) hα hβ hαβ
  rw [← hpt, smul_eq_mul, smul_eq_mul] at hc
  have := mul_le_mul_of_nonneg_left hc ht.le
  calc t * f (t⁻¹ • (θ • x₁ + (1 - θ) • x₂)) ≤ t * (α * f (t₁⁻¹ • x₁) + β * f (t₂⁻¹ • x₂)) := this
    _ = _ := by simp only [α, β]; field_simp

end LSE

/-! ### The groupwise term for a finite reference -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n q : ℕ}

/-- `f_{h_w}(x₀, x) − λ c(x₀, x)` at displacement `u = x − x₀`. -/
def gexp (w : E) (l : ℝ) (u : E) : ℝ := (inner ℝ w u) ^ 2 - l * ‖u‖ ^ 2

/-- `T(w, λ) = λ r + Σ_i a_i λε log Σ_j m_j exp{gexp(w, λ, y_j − x_i)/(λε)}`. -/
def Tfin (ε r : ℝ) (a : Fin n → ℝ) (x : Fin n → E) (m : Fin q → ℝ) (y : Fin q → E) (w : E)
    (l : ℝ) : ℝ :=
  l * r + ∑ i, a i * (l * ε * lse m (fun j => gexp w l (y j - x i) / (l * ε)))

lemma gexp_convex (u : E) {w₁ w₂ : E} {l₁ l₂ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    gexp (θ • w₁ + (1 - θ) • w₂) (θ * l₁ + (1 - θ) * l₂) u ≤
      θ * gexp w₁ l₁ u + (1 - θ) * gexp w₂ l₂ u := by
  unfold gexp
  rw [inner_add_left, inner_smul_left, inner_smul_left]
  simp only [conj_trivial]
  have : (θ * inner ℝ w₁ u + (1 - θ) * inner ℝ w₂ u) ^ 2 ≤
      θ * (inner ℝ w₁ u) ^ 2 + (1 - θ) * (inner ℝ w₂ u) ^ 2 := by
    nlinarith [sq_nonneg (inner ℝ w₁ u - inner ℝ w₂ u), mul_nonneg hθ0 (sub_nonneg.mpr hθ1)]
  nlinarith

lemma gexp_neg (w : E) (l : ℝ) (u : E) : gexp (-w) l u = gexp w l u := by
  simp [gexp, inner_neg_left]

lemma gexp_homog (w : E) (l t : ℝ) (u : E) : gexp (t • w) (t ^ 2 * l) u = t ^ 2 * gexp w l u := by
  simp only [gexp, inner_smul_left, conj_trivial]
  ring

/-- Per-anchor term `λε · lse(g/(λε))` as a perspective. -/
lemma anchor_eq (ε : ℝ) (m : Fin q → ℝ) (g : Fin q → ℝ) (l : ℝ) :
    l * ε * lse m (fun j => g j / (l * ε)) = (l * ε) * lse m ((l * ε)⁻¹ • g) := by
  congr 2
  funext j
  simp [div_eq_inv_mul]

/-- **(i) joint convexity** of `T` on `E × (0,∞)`. -/
theorem Tfin_convex {ε r : ℝ} (hε : 0 < ε) {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) (x : Fin n → E)
    {m : Fin q → ℝ} (hq : 0 < q) (hm : ∀ j, 0 < m j) (y : Fin q → E) :
    ConvexOn ℝ (Set.univ ×ˢ Set.Ioi 0) (fun p : E × ℝ => Tfin ε r a x m y p.1 p.2) := by
  refine ⟨convex_univ.prod (convex_Ioi 0), ?_⟩
  rintro ⟨w₁, l₁⟩ ⟨-, hl₁⟩ ⟨w₂, l₂⟩ ⟨-, hl₂⟩ θ η hθ hη hθη
  obtain rfl : η = 1 - θ := by linarith
  simp only [Set.mem_Ioi] at hl₁ hl₂
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  unfold Tfin
  have hθ1 : θ ≤ 1 := by linarith
  -- per anchor
  have hanchor : ∀ i, (θ * l₁ + (1 - θ) * l₂) * ε *
      lse m (fun j => gexp (θ • w₁ + (1 - θ) • w₂) (θ * l₁ + (1 - θ) * l₂) (y j - x i) /
        ((θ * l₁ + (1 - θ) * l₂) * ε)) ≤
      θ * (l₁ * ε * lse m (fun j => gexp w₁ l₁ (y j - x i) / (l₁ * ε))) +
        (1 - θ) * (l₂ * ε * lse m (fun j => gexp w₂ l₂ (y j - x i) / (l₂ * ε))) := by
    intro i
    set g₁ : Fin q → ℝ := fun j => gexp w₁ l₁ (y j - x i)
    set g₂ : Fin q → ℝ := fun j => gexp w₂ l₂ (y j - x i)
    have ht₁ : 0 < l₁ * ε := mul_pos hl₁ hε
    have ht₂ : 0 < l₂ * ε := mul_pos hl₂ hε
    have hP := perspective_le (lse_convex hq hm) (x₁ := g₁) (x₂ := g₂) ht₁ ht₂ hθ hθ1
    have hte : θ * (l₁ * ε) + (1 - θ) * (l₂ * ε) = (θ * l₁ + (1 - θ) * l₂) * ε := by ring
    rw [hte] at hP
    have hlpos : 0 < θ * l₁ + (1 - θ) * l₂ := by
      rcases eq_or_lt_of_le hθ with h | h
      · rw [← h]; linarith
      · nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) hl₂.le]
    have htpos : 0 < (θ * l₁ + (1 - θ) * l₂) * ε := mul_pos hlpos hε
    rw [anchor_eq, anchor_eq, anchor_eq]
    refine le_trans ?_ hP
    refine mul_le_mul_of_nonneg_left (lse_mono hq hm fun j => ?_) htpos.le
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr htpos.le)
    exact gexp_convex _ hθ hθ1
  have hsum : ∑ i, a i * ((θ * l₁ + (1 - θ) * l₂) * ε *
      lse m (fun j => gexp (θ • w₁ + (1 - θ) • w₂) (θ * l₁ + (1 - θ) * l₂) (y j - x i) /
        ((θ * l₁ + (1 - θ) * l₂) * ε))) ≤
      θ * ∑ i, a i * (l₁ * ε * lse m (fun j => gexp w₁ l₁ (y j - x i) / (l₁ * ε))) +
        (1 - θ) * ∑ i, a i * (l₂ * ε * lse m (fun j => gexp w₂ l₂ (y j - x i) / (l₂ * ε))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_left (hanchor i) (ha i)
    linarith
  nlinarith [hsum]

/-- **(i) evenness**. -/
theorem Tfin_neg (ε r : ℝ) (a : Fin n → ℝ) (x : Fin n → E) (m : Fin q → ℝ) (y : Fin q → E)
    (w : E) (l : ℝ) : Tfin ε r a x m y (-w) l = Tfin ε r a x m y w l := by
  simp only [Tfin, gexp_neg]

/-- **(i) homogeneity** `T(t w, t² λ) = t² T(w, λ)`. -/
theorem Tfin_homog (ε r : ℝ) (a : Fin n → ℝ) (x : Fin n → E) (m : Fin q → ℝ) (y : Fin q → E)
    (w : E) (l : ℝ) {t : ℝ} (ht : 0 < t) :
    Tfin ε r a x m y (t • w) (t ^ 2 * l) = t ^ 2 * Tfin ε r a x m y w l := by
  unfold Tfin
  simp_rw [gexp_homog]
  have ht2 : t ^ 2 ≠ 0 := by positivity
  have hfun : ∀ i, (fun j => t ^ 2 * gexp w l (y j - x i) / (t ^ 2 * l * ε)) =
      fun j => gexp w l (y j - x i) / (l * ε) := fun i => by
    funext j
    rw [mul_assoc (t ^ 2) l ε, mul_div_mul_left _ _ ht2]
  simp_rw [hfun, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

end StatFormal.RobustEquality.Paper2.Route
