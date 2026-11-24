import StatFormal.Archive.Wave24e.Statements
import StatFormal.Lib.Convex.GradientAE
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Route — otfd C `lem:cond-rank-consistency` (untrusted)

* Steps 1–2: the column equation gives `exp((g_j − ‖u_j‖²)/ε) = m⁻¹/S_j`, `S_j = Σ_i e^{2ℓ_i(u_j)/ε} ∈
  [e^{2χ(u_j)/ε}, N e^{2χ(u_j)/ε}]`, so `Φ(y) = (ε/2) log Σ_j m⁻¹ S_j⁻¹ e^{2⟨u_j,y⟩/ε}` is squeezed between
  `φ − ½ε log(mN)` and `φ`.
* Step 3: `χ` is `R`-Lipschitz (slopes `Z_i ∈ B̄(0,R)`), so `X − φ ≤ (‖y‖ + R)δ` on a `δ`-dense grid.
* `F̂(y)` is a subgradient of `Φ` (finite Jensen `exp(Σ p x) ≤ Σ p e^x`); hence `Φ` is convex.
* Step 5: `Φ_n − c_n → X` pointwise; Rockafellar 24.5 (`Foundations/Convex/GradientAE`, `tendsto_subgradient_inner`)
  at differentiability points; Rademacher for the convex limit (Tau Ceti) and `P ≪ Leb` for the a.e. form.
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave24e

open StatFormal.Wave23c (lagPot lagPiece)

section Lemmas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma le_lagPot {n : ℕ} (z : Fin (n + 1) → E) (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (w : E) :
    lagPiece z f i w ≤ lagPot z f w :=
  Finset.le_sup' (fun i => lagPiece z f i w) (Finset.mem_univ i)

lemma lagPot_le_add {n : ℕ} {z : Fin (n + 1) → E} (f : Fin (n + 1) → ℝ) {R : ℝ} (hz : ∀ i, ‖z i‖ ≤ R)
    (w w' : E) : lagPot z f w ≤ lagPot z f w' + R * ‖w - w'‖ := by
  refine Finset.sup'_le _ _ fun i _ => ?_
  have h1 := le_lagPot z f i w'
  have h2 : lagPiece z f i w = lagPiece z f i w' + ⟪w - w', z i⟫ := by
    simp only [lagPiece, inner_sub_left]; ring
  have h3 : ⟪w - w', z i⟫ ≤ R * ‖w - w'‖ := by
    refine (real_inner_le_norm _ _).trans ?_
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hz i) (norm_nonneg _)
  linarith

lemma convexOn_of_subgrad {F : E → ℝ} {G : E → E} (h : ∀ y y', F y + ⟪G y, y' - y⟫ ≤ F y') :
    ConvexOn ℝ univ F := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  set z := a • x + (1 - a) • y
  have h1 := h z x
  have h2 := h z y
  have hz : a • (x - z) + (1 - a) • (y - z) = 0 := by simp only [z]; module
  have h3 : a * ⟪G z, x - z⟫ + (1 - a) * ⟪G z, y - z⟫ = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right, hz, inner_zero_right]
  show F z ≤ a • F x + (1 - a) • F y
  simp only [smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- Finite Jensen for `log ∘ Σ p exp`. -/
lemma sum_le_log_sum_exp {M : ℕ} (p x : Fin M → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1) :
    ∑ j, p j * x j ≤ Real.log (∑ j, p j * Real.exp (x j)) := by
  have := convexOn_exp.map_sum_le (t := Finset.univ) (w := p) (p := x) (fun j _ => hp j) hsum
    (fun j _ => mem_univ _)
  simp only [smul_eq_mul] at this
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) this)]
  exact this

lemma rankMap_subgrad {M : ℕ} {ε : ℝ} (hε : 0 < ε) (u : Fin (M + 1) → E) (g : Fin (M + 1) → ℝ) (y y' : E) :
    rankPot ε u g y + ⟪rankMap ε u g y, y' - y⟫ ≤ rankPot ε u g y' := by
  set A : E → Fin (M + 1) → ℝ := fun y j => (g j - ‖u j‖ ^ 2 + 2 * ⟪u j, y⟫) / ε
  set W : E → ℝ := fun y => ∑ j, Real.exp (A y j)
  have hWpos : ∀ y, 0 < W y := fun y => Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨0, mem_univ _⟩
  set p : Fin (M + 1) → ℝ := fun j => Real.exp (A y j) / W y
  have hp0 : ∀ j, 0 ≤ p j := fun j => div_nonneg (Real.exp_pos _).le (hWpos y).le
  have hpsum : ∑ j, p j = 1 := by simp only [p]; rw [← Finset.sum_div, div_self (hWpos y).ne']
  -- the rank map is the `p`-mean of the grid
  have hmap : rankMap ε u g y = ∑ j, p j • u j := by
    have hexp : ∀ j, Real.exp ((g j - ‖y - u j‖ ^ 2) / ε) = Real.exp (A y j) * Real.exp (-(‖y‖ ^ 2) / ε) := by
      intro j; rw [← Real.exp_add]; congr 1
      simp only [A]; rw [norm_sub_sq_real, real_inner_comm]; field_simp; ring
    simp only [rankMap, hexp, ← Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_div_mul_right _ _ (Real.exp_pos _).ne']
  set x : Fin (M + 1) → ℝ := fun j => 2 * ⟪u j, y' - y⟫ / ε
  have hW' : W y' = W y * ∑ j, p j * Real.exp (x j) := by
    simp only [W, p, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ (hWpos y).ne', ← Real.exp_add]
    congr 1; simp only [A, x, inner_sub_right]; ring
  have hJ := sum_le_log_sum_exp p x hp0 hpsum
  have hPhi : ∀ y, rankPot ε u g y = ε / 2 * Real.log (W y) := fun y => rfl
  rw [hPhi, hPhi, hW', Real.log_mul (hWpos y).ne' (by
      exact (Finset.sum_pos (fun j _ => mul_pos (div_pos (Real.exp_pos _) (hWpos y)) (Real.exp_pos _))
        ⟨0, mem_univ _⟩).ne'), hmap, sum_inner]
  have hlin : ∑ j, ⟪p j • u j, y' - y⟫ = ε / 2 * ∑ j, p j * x j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [x, inner_smul_left, RCLike.conj_to_real]; field_simp
  rw [hlin]
  nlinarith [mul_le_mul_of_nonneg_left hJ (by positivity : (0 : ℝ) ≤ ε / 2)]

end Lemmas

theorem cond_rank_sandwich : Claims.cond_rank_sandwich := by
  intro K n M ε R δ z f u g U hε hcol hz hgrid hdense y
  -- Steps 1–2
  set S : Fin (M + 1) → ℝ := fun j => ∑ i, Real.exp (2 * lagPiece z f i (u j) / ε)
  have hSpos : ∀ j, 0 < S j := fun j => Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨0, mem_univ _⟩
  have hkey : ∀ j, Real.exp ((g j - ‖u j‖ ^ 2) / ε) = 1 / ((M : ℝ) + 1) / S j := by
    intro j
    have hsum : ∑ i, Real.exp ((f i - ‖u j - z i‖ ^ 2) / ε) = Real.exp (-(‖u j‖ ^ 2) / ε) * S j := by
      simp only [S, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Real.exp_add]; congr 1
      simp only [lagPiece]; rw [norm_sub_sq_real]; field_simp; ring
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    rw [hcol j, hsum, Real.log_mul (Real.exp_pos _).ne' (hSpos j).ne', Real.log_exp]
    rw [show (ε * Real.log (1 / ((M : ℝ) + 1)) - ε * (-(‖u j‖ ^ 2) / ε + Real.log (S j)) - ‖u j‖ ^ 2) / ε =
        Real.log (1 / ((M : ℝ) + 1)) - Real.log (S j) by field_simp; ring]
    rw [Real.exp_sub, Real.exp_log (by positivity), Real.exp_log (hSpos j)]
  have hSup : ∀ j, S j ≤ ((n : ℝ) + 1) * Real.exp (2 * lagPot z f (u j) / ε) := by
    intro j
    calc S j ≤ ∑ _i : Fin (n + 1), Real.exp (2 * lagPot z f (u j) / ε) :=
          Finset.sum_le_sum fun i _ => Real.exp_le_exp.2 (by
            rw [div_le_div_iff_of_pos_right hε]; linarith [le_lagPot z f i (u j)])
      _ = _ := by simp
  have hSlow : ∀ j, Real.exp (2 * lagPot z f (u j) / ε) ≤ S j := by
    intro j
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i => lagPiece z f i (u j)
    have : lagPot z f (u j) = lagPiece z f i (u j) := hi
    rw [this]
    exact Finset.single_le_sum (f := fun i => Real.exp (2 * lagPiece z f i (u j) / ε))
      (fun i _ => (Real.exp_pos _).le) (mem_univ i)
  set a : Fin (M + 1) → ℝ := fun j => ⟪u j, y⟫ - lagPot z f (u j)
  set φ := gridConj z f u y
  have hφ : ∀ j, a j ≤ φ := fun j => Finset.le_sup' (fun j => ⟪u j, y⟫ - lagPot z f (u j)) (mem_univ j)
  obtain ⟨jstar, -, hjstar⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun j => ⟪u j, y⟫ - lagPot z f (u j)
  have hφj : φ = a jstar := hjstar
  have hterm : ∀ j, Real.exp ((g j - ‖u j‖ ^ 2 + 2 * ⟪u j, y⟫) / ε) =
      1 / ((M : ℝ) + 1) / S j * Real.exp (2 * ⟪u j, y⟫ / ε) := by
    intro j; rw [← hkey, ← Real.exp_add]; congr 1; ring
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set T := ∑ j, Real.exp ((g j - ‖u j‖ ^ 2 + 2 * ⟪u j, y⟫) / ε)
  have hTup : T ≤ Real.exp (2 * φ / ε) := by
    calc T ≤ ∑ _j : Fin (M + 1), 1 / ((M : ℝ) + 1) * Real.exp (2 * φ / ε) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [hterm]
          have h1 : 1 / ((M : ℝ) + 1) / S j * Real.exp (2 * ⟪u j, y⟫ / ε) =
              1 / ((M : ℝ) + 1) * (Real.exp (2 * ⟪u j, y⟫ / ε) / S j) := by ring
          rw [h1]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_iff₀ (hSpos j)]
          calc Real.exp (2 * ⟪u j, y⟫ / ε) = Real.exp (2 * a j / ε) * Real.exp (2 * lagPot z f (u j) / ε) := by
                rw [← Real.exp_add]; congr 1; simp only [a]; ring
            _ ≤ Real.exp (2 * φ / ε) * S j := mul_le_mul (Real.exp_le_exp.2 (by
                rw [div_le_div_iff_of_pos_right hε]; linarith [hφ j])) (hSlow j) (Real.exp_pos _).le
                (Real.exp_pos _).le
      _ = Real.exp (2 * φ / ε) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; field_simp
  have hTlow : Real.exp (2 * φ / ε) / (((M : ℝ) + 1) * ((n : ℝ) + 1)) ≤ T := by
    have hj := Finset.single_le_sum (f := fun j => Real.exp ((g j - ‖u j‖ ^ 2 + 2 * ⟪u j, y⟫) / ε))
      (fun j _ => (Real.exp_pos _).le) (mem_univ jstar)
    refine le_trans ?_ hj
    show _ ≤ Real.exp ((g jstar - ‖u jstar‖ ^ 2 + 2 * ⟪u jstar, y⟫) / ε)
    rw [hterm, hφj]
    have h2 : Real.exp (2 * ⟪u jstar, y⟫ / ε) = Real.exp (2 * a jstar / ε) * Real.exp (2 * lagPot z f (u jstar) / ε) := by
      rw [← Real.exp_add]; congr 1; simp only [a]; ring
    rw [h2, div_le_iff₀ (by positivity)]
    have h3 := hSup jstar
    have hS := hSpos jstar
    have hE1 := Real.exp_pos (2 * a jstar / ε)
    have hE2 := Real.exp_pos (2 * lagPot z f (u jstar) / ε)
    rw [show 1 / ((M : ℝ) + 1) / S jstar * (Real.exp (2 * a jstar / ε) * Real.exp (2 * lagPot z f (u jstar) / ε)) *
        (((M : ℝ) + 1) * ((n : ℝ) + 1)) = Real.exp (2 * a jstar / ε) *
          (((n : ℝ) + 1) * Real.exp (2 * lagPot z f (u jstar) / ε) / S jstar) by field_simp]
    have : 1 ≤ ((n : ℝ) + 1) * Real.exp (2 * lagPot z f (u jstar) / ε) / S jstar := by
      rw [le_div_iff₀ hS]; linarith
    nlinarith
  have hTpos : 0 < T := Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨0, mem_univ _⟩
  have hPhi : rankPot ε u g y = ε / 2 * Real.log T := rfl
  refine ⟨?_, ?_, ?_, fun y' => rankMap_subgrad hε u g y y'⟩
  · have hl1 : Real.log T ≤ 2 * φ / ε := by
      have := Real.log_le_log hTpos hTup; rwa [Real.log_exp] at this
    have hl2 : 2 * φ / ε - Real.log (((M : ℝ) + 1) * ((n : ℝ) + 1)) ≤ Real.log T := by
      have := Real.log_le_log (by positivity) hTlow
      rwa [Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp] at this
    rw [hPhi, abs_le]
    have e1 : ε / 2 * (2 * φ / ε) = φ := by field_simp
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ ε / 2)]
    · nlinarith [mul_le_mul_of_nonneg_left hl1 (by positivity : (0 : ℝ) ≤ ε / 2),
        Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ ((M : ℝ) + 1) * ((n : ℝ) + 1))]
  all_goals
    have hbound : ∀ w ∈ U, ⟪w, y⟫ - lagPot z f w ≤ φ + (‖y‖ + R) * δ := by
      intro w hw
      obtain ⟨j, hj⟩ := hdense w hw
      have h1 := lagPot_le_add f hz (u j) w
      have h2 : ⟪w - u j, y⟫ ≤ ‖y‖ * δ := by
        refine (real_inner_le_norm _ _).trans ?_
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hj (norm_nonneg _)
      rw [norm_sub_rev] at h1
      have h3 := hφ j
      simp only [a] at h3
      rw [inner_sub_left] at h2
      nlinarith [mul_le_mul_of_nonneg_left hj (show (0 : ℝ) ≤ R by
        exact le_trans (norm_nonneg _) (hz 0))]
    have hbdd : BddAbove ((fun w => ⟪w, y⟫ - lagPot z f w) '' U) := by
      refine ⟨φ + (‖y‖ + R) * δ, ?_⟩
      rintro _ ⟨w, hw, rfl⟩; exact hbound w hw
  · rw [hφj]
    exact le_csSup hbdd ⟨u jstar, hgrid jstar, rfl⟩
  · have : contConj z f U y ≤ φ + (‖y‖ + R) * δ :=
      csSup_le ⟨_, ⟨u 0, hgrid 0, rfl⟩⟩ (by rintro _ ⟨w, hw, rfl⟩; exact hbound w hw)
    linarith

theorem cond_rank_consistency : Claims.cond_rank_consistency := by
  intro K n M ε δ R z f u g U X c P hε hεlog hδ hcol hz hgrid hdense hX hP
  set Φ : ℕ → EuclideanSpace ℝ (Fin K) → ℝ := fun k y => rankPot (ε k) (u k) (g k) y - c k
  have hsand := fun k y => cond_rank_sandwich K (n k) (M k) (ε k) R (δ k) (z k) (f k) (u k) (g k) U (hε k)
    (hcol k) (hz k) (hgrid k) (hdense k) y
  have hlim : ∀ y ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin K))), Tendsto (fun k => Φ k y) atTop (𝓝 (X y)) := by
    intro y _
    have hdiff : Tendsto (fun k => Φ k y - (contConj (z k) (f k) U y - c k)) atTop (𝓝 0) := by
      have hb : Tendsto (fun k => ε k / 2 * Real.log (((M k : ℝ) + 1) * ((n k : ℝ) + 1)) + (‖y‖ + R) * δ k)
          atTop (𝓝 0) := by
        have h1 : Tendsto (fun k => ε k / 2 * Real.log (((M k : ℝ) + 1) * ((n k : ℝ) + 1))) atTop (𝓝 0) := by
          have := hεlog.div_const 2
          rw [zero_div] at this
          exact this.congr fun k => by ring
        have h2 := hδ.const_mul (‖y‖ + R)
        rw [mul_zero] at h2
        simpa using h1.add h2
      refine squeeze_zero_norm (fun k => ?_) hb
      obtain ⟨s1, s2, s3, -⟩ := hsand k y
      rw [Real.norm_eq_abs]
      have e : Φ k y - (contConj (z k) (f k) U y - c k) =
          (rankPot (ε k) (u k) (g k) y - gridConj (z k) (f k) (u k) y) -
            (contConj (z k) (f k) U y - gridConj (z k) (f k) (u k) y) := by simp only [Φ]; ring
      rw [e]
      have := abs_sub (rankPot (ε k) (u k) (g k) y - gridConj (z k) (f k) (u k) y)
        (contConj (z k) (f k) U y - gridConj (z k) (f k) (u k) y)
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ contConj (z k) (f k) U y - gridConj (z k) (f k) (u k) y)] at this
      linarith
    simpa using hdiff.add (hX y)
  have hconv : ∀ k, ConvexOn ℝ Set.univ (Φ k) := fun k =>
    convexOn_of_subgrad (G := rankMap (ε k) (u k) (g k)) fun y y' => by
      have := rankMap_subgrad (hε k) (u k) (g k) y y'
      simp only [Φ]; linarith
  have hpt : ∀ y, DifferentiableAt ℝ X y →
      Tendsto (fun k => rankMap (ε k) (u k) (g k) y) atTop (𝓝 (gradient X y)) := by
    intro y hy
    refine StatFormal.Convex.tendsto_subgradient_inner isOpen_univ (Eventually.of_forall hconv) hlim
      (Set.mem_univ y) hy.hasGradientAt tendsto_const_nhds (Eventually.of_forall fun k y' _ => ?_)
    have := rankMap_subgrad (hε k) (u k) (g k) y y'
    simp only [Φ]; linarith
  refine ⟨hpt, ?_⟩
  have hXconv : ConvexOn ℝ Set.univ X :=
    StatFormal.Convex.convexOn_of_tendsto (Eventually.of_forall hconv) hlim
  have hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin K))), y ∈ Set.univ → DifferentiableAt ℝ X y :=
    hXconv.ae_differentiableAt_of_mem
  filter_upwards [hP.ae_le hae] with y hy
  exact hpt y (hy (Set.mem_univ y))

end StatFormal.Wave24e
