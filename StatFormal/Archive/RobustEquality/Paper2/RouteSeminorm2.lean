import StatFormal.Archive.RobustEquality.Paper2.RouteSeminorm
import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Route for paper2 `thm:seminorm` (finite reference), parts (ii)–(iii)

Continues `RouteSeminorm.lean`.
* `gibbs_fin`: `Σ_j p_j g_j − τ Σ_j p_j log(p_j/m_j) ≤ τ lse_m(g/τ)` (finite Gibbs inequality);
* `Feasible`: the budget has a feasible kernel (the set `𝓑` is non-empty, `r ≥` floor), and
  `Tfin_nonneg`: then `T ≥ 0` on `λ > 0`;
* `Nsq = ⨅_{λ>0} T`: `Nsq_nonneg`, `Nsq_le_T`, `Nsq_homog`, `Nsq_neg`, `Nsq_zero`, `Nsq_convex`,
  `Nsq_le` (`≤ r‖w‖²`);
* `sqrt_subadd`: `√g` is subadditive for convex, nonnegative, 2-homogeneous `g`;
  `seminormN`: **(ii)** `√Nsq` is a `Seminorm ℝ E`, with `seminormN_le`: `N(w) ≤ √r ‖w‖`;
* **(iii)** `inf_Fbar`: `IsGLB {(Δ + √T₀(λ₀) + √T₁(λ₁))² | λ₀, λ₁ > 0} ((Δ + N₀ + N₁)²)` for `Δ ≥ 0`;
  `Deltafin` (nominal disparity of two finite centres, as an infimum over couplings) and
  `G_homog`: `G = Δ + N₀ + N₁` is positively homogeneous.
-/

noncomputable section
open Finset Real
open StatFormal.Foundations.SemiDiscrete

namespace StatFormal.RobustEquality.Paper2.Route

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n q : ℕ}

/-- Finite Gibbs inequality. -/
theorem gibbs_fin {m : Fin q → ℝ} (hq : 0 < q) (hm : ∀ j, 0 < m j) (p : Fin q → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (g : Fin q → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∑ j, p j * g j - τ * ∑ j, p j * Real.log (p j / m j) ≤ τ * lse m (fun j => g j / τ) := by
  set Z := ∑ j, m j * Real.exp (g j / τ)
  have hZ : 0 < Z := sum_exp_pos hq hm _
  have hterm : ∀ j, p j * (g j / τ - Real.log (p j / m j)) ≤
      p j * Real.log Z + m j * Real.exp (g j / τ) / Z - p j := by
    intro j
    rcases eq_or_lt_of_le (hp j) with h0 | hpos
    · rw [← h0]; simp only [zero_mul, sub_zero, zero_add]
      exact div_nonneg (mul_nonneg (hm j).le (Real.exp_pos _).le) hZ.le
    · have hx : 0 < m j * Real.exp (g j / τ) / (p j * Z) :=
        div_pos (mul_pos (hm j) (Real.exp_pos _)) (mul_pos hpos hZ)
      have hlog := Real.log_le_sub_one_of_pos hx
      rw [Real.log_div (mul_pos (hm j) (Real.exp_pos _)).ne' (mul_pos hpos hZ).ne',
        Real.log_mul (hm j).ne' (Real.exp_pos _).ne', Real.log_exp,
        Real.log_mul hpos.ne' hZ.ne'] at hlog
      rw [Real.log_div hpos.ne' (hm j).ne']
      have := mul_le_mul_of_nonneg_left hlog hpos.le
      have e : p j * (m j * Real.exp (g j / τ) / (p j * Z) - 1) =
          m j * Real.exp (g j / τ) / Z - p j := by field_simp
      rw [e] at this
      nlinarith
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ univ) => hterm j
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul,
    ← Finset.sum_div, div_self hZ.ne'] at hsum
  have hL : ∑ j, p j * g j - τ * ∑ j, p j * Real.log (p j / m j) =
      τ * ∑ j, p j * (g j / τ - Real.log (p j / m j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [hL]
  refine mul_le_mul_of_nonneg_left ?_ hτ.le
  simp only [lse]
  linarith

/-- The budget has a feasible kernel: `Σ_i a_i (E_{p_i} c + ε KL(p_i ‖ ν)) ≤ r` (the set is non-empty). -/
def Feasible (ε r : ℝ) (a : Fin n → ℝ) (x : Fin n → E) (m : Fin q → ℝ) (y : Fin q → E) : Prop :=
  ∃ p : Fin n → Fin q → ℝ, (∀ i j, 0 ≤ p i j) ∧ (∀ i, ∑ j, p i j = 1) ∧
    ∑ i, a i * (∑ j, p i j * ‖y j - x i‖ ^ 2 + ε * ∑ j, p i j * Real.log (p i j / m j)) ≤ r

/-- Standing hypotheses on the centre and the finite reference. -/
structure Hyp (ε : ℝ) (a : Fin n → ℝ) (m : Fin q → ℝ) : Prop where
  hε : 0 < ε
  ha : ∀ i, 0 ≤ a i
  hsum : ∑ i, a i = 1
  hq : 0 < q
  hm : ∀ j, 0 < m j
  hmass : ∑ j, m j ≤ 1

variable {ε r : ℝ} {a : Fin n → ℝ} {x : Fin n → E} {m : Fin q → ℝ} {y : Fin q → E}

theorem Tfin_nonneg (h : Hyp ε a m) (hF : Feasible ε r a x m y) (w : E) {l : ℝ} (hl : 0 < l) :
    0 ≤ Tfin ε r a x m y w l := by
  obtain ⟨p, hp0, hp1, hpr⟩ := hF
  have hτ : 0 < l * ε := mul_pos hl h.hε
  have hi : ∀ i, a i * (∑ j, p i j * (inner ℝ w (y j - x i)) ^ 2 -
      l * (∑ j, p i j * ‖y j - x i‖ ^ 2 + ε * ∑ j, p i j * Real.log (p i j / m j))) ≤
      a i * (l * ε * lse m (fun j => gexp w l (y j - x i) / (l * ε))) := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (h.ha i)
    have hg := gibbs_fin h.hq h.hm (p i) (hp0 i) (hp1 i) (fun j => gexp w l (y j - x i)) hτ
    have e : ∑ j, p i j * gexp w l (y j - x i) =
        ∑ j, p i j * (inner ℝ w (y j - x i)) ^ 2 - l * ∑ j, p i j * ‖y j - x i‖ ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [gexp]; ring
    rw [e] at hg
    linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ univ) => hi i
  have hpos : 0 ≤ ∑ i, a i * ∑ j, p i j * (inner ℝ w (y j - x i)) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (h.ha i)
      (Finset.sum_nonneg fun j _ => mul_nonneg (hp0 i j) (sq_nonneg _))
  have hsplit : ∑ i, a i * (∑ j, p i j * (inner ℝ w (y j - x i)) ^ 2 -
      l * (∑ j, p i j * ‖y j - x i‖ ^ 2 + ε * ∑ j, p i j * Real.log (p i j / m j))) =
      ∑ i, a i * ∑ j, p i j * (inner ℝ w (y j - x i)) ^ 2 -
        l * ∑ i, a i * (∑ j, p i j * ‖y j - x i‖ ^ 2 +
          ε * ∑ j, p i j * Real.log (p i j / m j)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit] at hsum
  unfold Tfin
  have := mul_le_mul_of_nonneg_left hpr hl.le
  linarith

/-- `N_s(w)² = inf_{λ > 0} T(w, λ)`. -/
def Nsq (ε r : ℝ) (a : Fin n → ℝ) (x : Fin n → E) (m : Fin q → ℝ) (y : Fin q → E) (w : E) : ℝ :=
  ⨅ l : Set.Ioi (0 : ℝ), Tfin ε r a x m y w l

instance : Nonempty (Set.Ioi (0 : ℝ)) := ⟨⟨1, Set.mem_Ioi.mpr one_pos⟩⟩

lemma bdd_T (h : Hyp ε a m) (hF : Feasible ε r a x m y) (w : E) :
    BddBelow (Set.range fun l : Set.Ioi (0 : ℝ) => Tfin ε r a x m y w l) :=
  ⟨0, by rintro _ ⟨l, rfl⟩; exact Tfin_nonneg h hF w l.2⟩

lemma Nsq_nonneg (h : Hyp ε a m) (hF : Feasible ε r a x m y) (w : E) :
    0 ≤ Nsq ε r a x m y w :=
  le_ciInf fun l => Tfin_nonneg h hF w l.2

lemma Nsq_le_T (h : Hyp ε a m) (hF : Feasible ε r a x m y) (w : E) {l : ℝ} (hl : 0 < l) :
    Nsq ε r a x m y w ≤ Tfin ε r a x m y w l :=
  ciInf_le (bdd_T h hF w) ⟨l, hl⟩

lemma Nsq_homog (h : Hyp ε a m) (hF : Feasible ε r a x m y) (w : E) {t : ℝ} (ht : 0 < t) :
    Nsq ε r a x m y (t • w) = t ^ 2 * Nsq ε r a x m y w := by
  have ht2 : 0 < t ^ 2 := by positivity
  apply le_antisymm
  · have : Nsq ε r a x m y (t • w) / t ^ 2 ≤ Nsq ε r a x m y w := by
      refine le_ciInf fun l => ?_
      rw [div_le_iff₀ ht2]
      have := Nsq_le_T h hF (t • w) (mul_pos ht2 l.2)
      rw [Tfin_homog _ _ _ _ _ _ _ _ ht] at this
      linarith
    rwa [div_le_iff₀ ht2, mul_comm] at this
  · refine le_ciInf fun l => ?_
    have hl : 0 < (l : ℝ) / t ^ 2 := div_pos l.2 ht2
    have e := Tfin_homog ε r a x m y w ((l : ℝ) / t ^ 2) ht
    rw [mul_div_cancel₀ _ ht2.ne'] at e
    rw [e]
    exact mul_le_mul_of_nonneg_left (Nsq_le_T h hF w hl) ht2.le

lemma Nsq_neg (w : E) : Nsq ε r a x m y (-w) = Nsq ε r a x m y w := by
  simp only [Nsq, Tfin_neg]

lemma Nsq_zero (h : Hyp ε a m) (hF : Feasible ε r a x m y) : Nsq ε r a x m y (0 : E) = 0 := by
  have := Nsq_homog h hF (0 : E) (two_pos)
  rw [smul_zero] at this
  linarith

lemma Nsq_convex (h : Hyp ε a m) (hF : Feasible ε r a x m y) :
    ConvexOn ℝ Set.univ (Nsq ε r a x m y) := by
  refine ⟨convex_univ, fun w₁ _ w₂ _ θ η hθ hη hθη => ?_⟩
  obtain rfl : η = 1 - θ := by linarith
  simp only [smul_eq_mul]
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  obtain ⟨l₁, hl₁⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right (Nsq ε r a x m y w₁) hδ)
  obtain ⟨l₂, hl₂⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right (Nsq ε r a x m y w₂) hδ)
  have hc := (Tfin_convex h.hε h.ha x h.hq h.hm y (r := r)).2
    (show ((w₁, (l₁ : ℝ)) : E × ℝ) ∈ Set.univ ×ˢ Set.Ioi 0 from ⟨trivial, l₁.2⟩)
    (show ((w₂, (l₂ : ℝ)) : E × ℝ) ∈ Set.univ ×ˢ Set.Ioi 0 from ⟨trivial, l₂.2⟩) hθ hη hθη
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hc
  have p1 : 0 < (l₁ : ℝ) := l₁.2
  have p2 : 0 < (l₂ : ℝ) := l₂.2
  have hlpos : 0 < θ * (l₁ : ℝ) + (1 - θ) * l₂ := by
    rcases eq_or_lt_of_le hθ with h0 | h0
    · rw [← h0]; simpa using p2
    · nlinarith [mul_pos h0 p1, mul_nonneg hη p2.le]
  have h1 := Nsq_le_T h hF (θ • w₁ + (1 - θ) • w₂) hlpos
  nlinarith [mul_le_mul_of_nonneg_left hl₁.le hθ, mul_le_mul_of_nonneg_left hl₂.le hη]

lemma Nsq_le (h : Hyp ε a m) (hF : Feasible ε r a x m y) (w : E) :
    Nsq ε r a x m y w ≤ r * ‖w‖ ^ 2 := by
  rcases eq_or_ne w 0 with hw | hw
  · rw [hw, Nsq_zero h hF, norm_zero]; simp
  have hl : 0 < ‖w‖ ^ 2 := by positivity
  refine (Nsq_le_T h hF w hl).trans ?_
  unfold Tfin
  have hτ : 0 < ‖w‖ ^ 2 * ε := mul_pos hl h.hε
  have hterm : ∀ i, a i * (‖w‖ ^ 2 * ε *
      lse m (fun j => gexp w (‖w‖ ^ 2) (y j - x i) / (‖w‖ ^ 2 * ε))) ≤ 0 := by
    intro i
    refine mul_nonpos_of_nonneg_of_nonpos (h.ha i) (mul_nonpos_of_nonneg_of_nonpos hτ.le ?_)
    have hle : lse m (fun j => gexp w (‖w‖ ^ 2) (y j - x i) / (‖w‖ ^ 2 * ε)) ≤
        lse m (fun _ => 0) := lse_mono h.hq h.hm fun j => by
      refine div_nonpos_of_nonpos_of_nonneg ?_ hτ.le
      simp only [gexp]
      have := abs_real_inner_le_norm w (y j - x i)
      have h2 : (inner ℝ w (y j - x i)) ^ 2 ≤ (‖w‖ * ‖y j - x i‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      nlinarith
    refine hle.trans ?_
    simp only [lse, Real.exp_zero, mul_one]
    exact Real.log_nonpos (Finset.sum_nonneg fun j _ => (h.hm j).le) h.hmass
  have := Finset.sum_nonpos fun i (_ : i ∈ univ) => hterm i
  linarith

/-! ### Seminorm -/

/-- `√g` is subadditive for a convex, nonnegative, 2-homogeneous `g`. -/
theorem sqrt_subadd {g : E → ℝ} (hconv : ConvexOn ℝ Set.univ g) (hnn : ∀ w, 0 ≤ g w)
    (hhom : ∀ (t : ℝ) w, 0 < t → g (t • w) = t ^ 2 * g w) (u v : E) :
    √(g (u + v)) ≤ √(g u) + √(g v) := by
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  set A := √(g u) + δ / 3
  set B := √(g v) + δ / 3
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  set θ := A / (A + B)
  have hθ0 : 0 < θ := div_pos hA (by positivity)
  have hθ1 : 1 - θ = B / (A + B) := by simp only [θ]; field_simp; ring
  have h1θ : 0 < 1 - θ := by rw [hθ1]; positivity
  have hsplit : u + v = θ • (θ⁻¹ • u) + (1 - θ) • ((1 - θ)⁻¹ • v) := by
    rw [smul_smul, smul_smul, mul_inv_cancel₀ hθ0.ne', mul_inv_cancel₀ h1θ.ne', one_smul, one_smul]
  have hc := hconv.2 (Set.mem_univ (θ⁻¹ • u)) (Set.mem_univ ((1 - θ)⁻¹ • v)) hθ0.le h1θ.le
    (by ring)
  rw [← hsplit, smul_eq_mul, smul_eq_mul, hhom _ _ (inv_pos.mpr hθ0),
    hhom _ _ (inv_pos.mpr h1θ)] at hc
  have hu : g u ≤ A ^ 2 := by
    rw [← Real.sq_sqrt (hnn u)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (by simp only [A]; linarith) 2
  have hv : g v ≤ B ^ 2 := by
    rw [← Real.sq_sqrt (hnn v)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (by simp only [B]; linarith) 2
  have hbound : g (u + v) ≤ (A + B) ^ 2 := by
    have e1 : θ * (θ⁻¹ ^ 2 * g u) = g u / θ := by field_simp
    have e2 : (1 - θ) * ((1 - θ)⁻¹ ^ 2 * g v) = g v / (1 - θ) := by field_simp
    rw [e1, e2] at hc
    have f1 : g u / θ ≤ A ^ 2 / θ := div_le_div_of_nonneg_right hu hθ0.le
    have f2 : g v / (1 - θ) ≤ B ^ 2 / (1 - θ) := div_le_div_of_nonneg_right hv h1θ.le
    have f3 : A ^ 2 / θ + B ^ 2 / (1 - θ) = (A + B) ^ 2 := by
      rw [hθ1]; simp only [θ]; field_simp
    linarith
  have := Real.sqrt_le_sqrt hbound
  rw [Real.sqrt_sq (by positivity)] at this
  simp only [A, B] at this
  linarith

/-- **(ii)** `N_s = √(inf_λ T)` is a seminorm. -/
def seminormN (h : Hyp ε a m) (hF : Feasible ε r a x m y) : Seminorm ℝ E :=
  Seminorm.of (fun w => √(Nsq ε r a x m y w))
    (sqrt_subadd (Nsq_convex h hF) (Nsq_nonneg h hF) fun t w ht => Nsq_homog h hF w ht)
    (fun t w => by
      rcases lt_trichotomy t 0 with ht | ht | ht
      · have e : t • w = (-t) • (-w) := by rw [neg_smul_neg]
        rw [e, Nsq_homog h hF (-w) (neg_pos.mpr ht), Nsq_neg, Real.sqrt_mul (sq_nonneg _),
          Real.sqrt_sq (neg_pos.mpr ht).le, Real.norm_eq_abs, abs_of_neg ht]
      · rw [ht, zero_smul, Nsq_zero h hF, norm_zero, zero_mul, Real.sqrt_zero]
      · rw [Nsq_homog h hF w ht, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht.le,
          Real.norm_eq_abs, abs_of_pos ht])

lemma seminormN_apply (h : Hyp ε a m) (hF : Feasible ε r a x m y) (w : E) :
    seminormN h hF w = √(Nsq ε r a x m y w) := rfl

/-- **(ii)** `N_s(w) ≤ √r ‖w‖`. -/
theorem seminormN_le (h : Hyp ε a m) (hF : Feasible ε r a x m y) (w : E) :
    seminormN h hF w ≤ √r * ‖w‖ := by
  rw [seminormN_apply]
  have := Real.sqrt_le_sqrt (Nsq_le h hF w)
  rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
  exact this

/-! ### (iii) the infimum of the certificate -/

/-- Abstract (iii): for `D ≥ 0` and `f₀, f₁ ≥ 0` on `λ > 0`,
`inf_{λ₀,λ₁} (D + √f₀ + √f₁)² = (D + √(inf f₀) + √(inf f₁))²`. -/
theorem isGLB_sq_sum {D : ℝ} (hD : 0 ≤ D) (f₀ f₁ : ℝ → ℝ) (h₀ : ∀ l, 0 < l → 0 ≤ f₀ l)
    (h₁ : ∀ l, 0 < l → 0 ≤ f₁ l) :
    IsGLB {v | ∃ l₀ l₁ : ℝ, 0 < l₀ ∧ 0 < l₁ ∧ v = (D + √(f₀ l₀) + √(f₁ l₁)) ^ 2}
      ((D + √(⨅ l : Set.Ioi (0 : ℝ), f₀ l) + √(⨅ l : Set.Ioi (0 : ℝ), f₁ l)) ^ 2) := by
  have hb₀ : BddBelow (Set.range fun l : Set.Ioi (0 : ℝ) => f₀ l) :=
    ⟨0, by rintro _ ⟨l, rfl⟩; exact h₀ l l.2⟩
  have hb₁ : BddBelow (Set.range fun l : Set.Ioi (0 : ℝ) => f₁ l) :=
    ⟨0, by rintro _ ⟨l, rfl⟩; exact h₁ l l.2⟩
  set I₀ := ⨅ l : Set.Ioi (0 : ℝ), f₀ l
  set I₁ := ⨅ l : Set.Ioi (0 : ℝ), f₁ l
  have hI₀ : 0 ≤ I₀ := le_ciInf fun l => h₀ l l.2
  have hI₁ : 0 ≤ I₁ := le_ciInf fun l => h₁ l l.2
  refine ⟨?_, ?_⟩
  · rintro v ⟨l₀, l₁, hl₀, hl₁, rfl⟩
    have a₀ : √I₀ ≤ √(f₀ l₀) := Real.sqrt_le_sqrt (ciInf_le hb₀ ⟨l₀, hl₀⟩)
    have a₁ : √I₁ ≤ √(f₁ l₁) := Real.sqrt_le_sqrt (ciInf_le hb₁ ⟨l₁, hl₁⟩)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  · intro b hb
    by_contra hlt
    push Not at hlt
    -- choose η with (G + 2η)² < b
    set G := D + √I₀ + √I₁
    have hG : 0 ≤ G := by positivity
    have hsb : G < √b := by
      rw [show G = √(G ^ 2) from (Real.sqrt_sq hG).symm]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt
    set η := (√b - G) / 3
    have hη : 0 < η := by simp only [η]; linarith
    obtain ⟨l₀, hl₀⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right I₀ (pow_pos hη 2))
    obtain ⟨l₁, hl₁⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right I₁ (pow_pos hη 2))
    have c₀ : √(f₀ l₀) ≤ √I₀ + η := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      nlinarith [Real.sq_sqrt hI₀, Real.sqrt_nonneg I₀]
    have c₁ : √(f₁ l₁) ≤ √I₁ + η := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      nlinarith [Real.sq_sqrt hI₁, Real.sqrt_nonneg I₁]
    have hmem := hb ⟨l₀, l₁, l₀.2, l₁.2, rfl⟩
    have hle : D + √(f₀ l₀) + √(f₁ l₁) ≤ G + 2 * η := by simp only [G]; linarith
    have hsq : (D + √(f₀ l₀) + √(f₁ l₁)) ^ 2 ≤ (G + 2 * η) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hle 2
    have hlt2 : (G + 2 * η) ^ 2 < b := by
      have : G + 2 * η < √b := by simp only [η]; linarith
      have h2 := pow_lt_pow_left₀ this (by positivity) (two_ne_zero)
      rwa [Real.sq_sqrt (le_trans (sq_nonneg _) hlt.le)] at h2
    linarith

/-- The nominal disparity of two finite centres, `Δ(w) = (min_γ Σ γ_ij ⟪w, x⁰_i − x¹_j⟫²)^{1/2}`. -/
def Deltafin {n₀ n₁ : ℕ} (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E)
    (w : E) : ℝ :=
  √(⨅ γ : {γ : Fin n₀ → Fin n₁ → ℝ | (∀ i j, 0 ≤ γ i j) ∧ (∀ i, ∑ j, γ i j = a₀ i) ∧
      ∀ j, ∑ i, γ i j = a₁ j},
    ∑ i, ∑ j, (γ : Fin n₀ → Fin n₁ → ℝ) i j * (inner ℝ w (x₀ i - x₁ j)) ^ 2)

lemma Deltafin_homog {n₀ n₁ : ℕ} (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ)
    (x₁ : Fin n₁ → E) (w : E) {t : ℝ} (ht : 0 < t) :
    Deltafin a₀ x₀ a₁ x₁ (t • w) = t * Deltafin a₀ x₀ a₁ x₁ w := by
  unfold Deltafin
  have e : ∀ γ : Fin n₀ → Fin n₁ → ℝ, ∑ i, ∑ j, γ i j * (inner ℝ (t • w) (x₀ i - x₁ j)) ^ 2 =
      t ^ 2 * ∑ i, ∑ j, γ i j * (inner ℝ w (x₀ i - x₁ j)) ^ 2 := fun γ => by
    simp only [inner_smul_left, conj_trivial, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [← Real.mul_iInf_of_nonneg (sq_nonneg t), Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]

lemma Deltafin_nonneg {n₀ n₁ : ℕ} (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ)
    (x₁ : Fin n₁ → E) (w : E) : 0 ≤ Deltafin a₀ x₀ a₁ x₁ w := Real.sqrt_nonneg _

/-- **(iii)** `inf_{λ₀,λ₁} F̄ = G²` with `G = Δ + N₀ + N₁`. -/
theorem inf_Fbar {r₀ r₁ : ℝ} {a₀ : Fin n → ℝ} {x₀ : Fin n → E} {a₁ : Fin n → ℝ}
    {x₁ : Fin n → E} (h₀ : Hyp ε a₀ m) (h₁ : Hyp ε a₁ m) (hF₀ : Feasible ε r₀ a₀ x₀ m y)
    (hF₁ : Feasible ε r₁ a₁ x₁ m y) (w : E) :
    IsGLB {v | ∃ l₀ l₁ : ℝ, 0 < l₀ ∧ 0 < l₁ ∧ v = (Deltafin a₀ x₀ a₁ x₁ w +
        √(Tfin ε r₀ a₀ x₀ m y w l₀) + √(Tfin ε r₁ a₁ x₁ m y w l₁)) ^ 2}
      ((Deltafin a₀ x₀ a₁ x₁ w + seminormN h₀ hF₀ w + seminormN h₁ hF₁ w) ^ 2) :=
  isGLB_sq_sum (Deltafin_nonneg _ _ _ _ w) _ _ (fun _ hl => Tfin_nonneg h₀ hF₀ w hl)
    (fun _ hl => Tfin_nonneg h₁ hF₁ w hl)

/-- **(iii)** `G` is positively homogeneous of degree one. -/
theorem G_homog {r₀ r₁ : ℝ} {a₀ : Fin n → ℝ} {x₀ : Fin n → E} {a₁ : Fin n → ℝ}
    {x₁ : Fin n → E} (h₀ : Hyp ε a₀ m) (h₁ : Hyp ε a₁ m) (hF₀ : Feasible ε r₀ a₀ x₀ m y)
    (hF₁ : Feasible ε r₁ a₁ x₁ m y) (w : E) {t : ℝ} (ht : 0 < t) :
    Deltafin a₀ x₀ a₁ x₁ (t • w) + seminormN h₀ hF₀ (t • w) + seminormN h₁ hF₁ (t • w) =
      t * (Deltafin a₀ x₀ a₁ x₁ w + seminormN h₀ hF₀ w + seminormN h₁ hF₁ w) := by
  rw [Deltafin_homog _ _ _ _ _ ht, map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs,
    abs_of_pos ht]
  ring

end StatFormal.RobustEquality.Paper2.Route
