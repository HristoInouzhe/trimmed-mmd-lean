import StatFormal.Archive.OTFD.Wave2.RouteTangent
import StatFormal.Archive.OTFD.Bands.Proofs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Real.Pointwise

/-!
# Route: C `prop:conditional-perturbation`
-/

noncomputable section
open Finset Matrix

namespace StatFormal.OTFD.Wave2

open StatFormal.OTFD.Bands StatFormal.OTFD.Bands2

variable {n K : ℕ}

/-! ### Real-analysis helpers -/

lemma tanh_le_self {y : ℝ} (hy : 0 ≤ y) : Real.tanh y ≤ y := by
  set h : ℝ → ℝ := fun w => (2 + w) - (2 - w) * Real.exp w with hh
  have hd : ∀ w, HasDerivAt h (1 - ((-1) * Real.exp w + (2 - w) * Real.exp w)) w := by
    intro w
    have h1 : HasDerivAt (fun w : ℝ => 2 + w) 1 w := (hasDerivAt_id w).const_add 2
    have h2 : HasDerivAt (fun w : ℝ => 2 - w) (-1) w := by
      simpa using (hasDerivAt_id w).const_sub 2
    exact h1.sub (h2.mul (Real.hasDerivAt_exp w))
  have hmono : Monotone h := by
    apply monotone_of_deriv_nonneg (fun w => (hd w).differentiableAt)
    intro w
    rw [(hd w).deriv]
    have hexp := Real.add_one_le_exp (-w)
    have hpos := Real.exp_pos w
    have : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have h0 : h 0 = 0 := by simp [hh]
  have hw := hmono (by linarith : (0 : ℝ) ≤ 2 * y)
  rw [h0] at hw
  simp only [hh] at hw
  rw [tanh_formula, div_le_iff₀ (by positivity)]
  nlinarith

lemma iSup_fin_le {f : Fin n → ℝ} {c : ℝ} [Nonempty (Fin n)] (h : ∀ i, f i ≤ c) : ⨆ i, f i ≤ c :=
  ciSup_le h

lemma le_iSup_fin' (f : Fin n → ℝ) (k : Fin n) : f k ≤ ⨆ i, f i :=
  le_ciSup (Finite.bddAbove_range f) k

lemma iInf_le_fin' (f : Fin n → ℝ) (k : Fin n) : ⨅ i, f i ≤ f k :=
  ciInf_le (Finite.bddBelow_range f) k

/-- Each `|Δf_k − c|` is bounded by `D_c = sup_i |Δf_i − c|`. -/
lemma abs_le_Dc (f f' : Fin n → ℝ) (c : ℝ) (k : Fin n) :
    |f k - f' k - c| ≤ ⨆ i, |f i - f' i - c| :=
  le_iSup_fin' (fun i => |f i - f' i - c|) k

lemma Dc_nonneg (f f' : Fin n → ℝ) (c : ℝ) : 0 ≤ ⨆ i, |f i - f' i - c| := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · simp [Real.iSup_of_isEmpty]
  · obtain ⟨k⟩ := h
    exact (abs_nonneg _).trans (abs_le_Dc f f' c k)

lemma potOsc_nonneg (f f' : Fin n → ℝ) : 0 ≤ potOsc f f' :=
  le_ciInf fun c => Dc_nonneg f f' c

/-- Pass a bound `X ≤ r D_c` (all `c`) to `X ≤ r D_f`. -/
lemma le_mul_potOsc {X r : ℝ} (hr : 0 ≤ r) (f f' : Fin n → ℝ)
    (h : ∀ c, X ≤ r * ⨆ i, |f i - f' i - c|) : X ≤ r * potOsc f f' := by
  unfold potOsc
  rw [Real.mul_iInf_of_nonneg hr]
  exact le_ciInf h

/-! ### Gap and witness shifts -/

lemma condScore_diff (f f' : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (k : Fin n) (u : Fin K → ℝ) :
    score (condA f Z) (condB Z) k u = score (condA f' Z) (condB Z) k u + (f k - f' k) := by
  simp only [score, condA]; ring

/-- `|F(u) − F'(u)| ≤ 2 D_c` for the gap integrands. -/
lemma gap_integrand_shift (f f' : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (i : Fin n) (c : ℝ)
    (u : Fin K → ℝ) :
    |((⨆ k, score (condA f Z) (condB Z) k u) - score (condA f Z) (condB Z) i u) -
      ((⨆ k, score (condA f' Z) (condB Z) k u) - score (condA f' Z) (condB Z) i u)| ≤
      2 * ⨆ j, |f j - f' j - c| := by
  have : Nonempty (Fin n) := ⟨i⟩
  set D := ⨆ j, |f j - f' j - c|
  have hk : ∀ k, |f k - f' k - c| ≤ D := abs_le_Dc f f' c
  set s := fun k => score (condA f Z) (condB Z) k u
  set s' := fun k => score (condA f' Z) (condB Z) k u
  have hss : ∀ k, s k = s' k + (f k - f' k) := fun k => condScore_diff f f' Z k u
  have hup : (⨆ k, s k) ≤ (⨆ k, s' k) + c + D := by
    apply ciSup_le; intro k
    rw [hss k]
    have := le_iSup_fin' s' k
    have := (abs_le.mp (hk k)).2
    linarith
  have hlo : (⨆ k, s' k) + c - D ≤ (⨆ k, s k) := by
    have : (⨆ k, s' k) ≤ (⨆ k, s k) - c + D := by
      apply ciSup_le; intro k
      have h1 := le_iSup_fin' s k
      have h2 := (abs_le.mp (hk k)).1
      rw [hss k] at h1
      linarith
    linarith
  have hi := abs_le.mp (hk i)
  show |(⨆ k, s k) - s i - ((⨆ k, s' k) - s' i)| ≤ 2 * D
  rw [hss i, abs_le]
  constructor <;> linarith [hi.1, hi.2]

lemma sInf_shift {X : Type*} {A : Set X} (hA : A.Nonempty) (g g' : X → ℝ) (r : ℝ)
    (hg : ∀ u, 0 ≤ g u) (hg' : ∀ u, 0 ≤ g' u) (h : ∀ u, g u ≤ g' u + r) :
    sInf (g '' A) ≤ sInf (g' '' A) + r := by
  have : sInf (g '' A) - r ≤ sInf (g' '' A) := by
    apply le_csInf (hA.image g')
    rintro _ ⟨u, hu, rfl⟩
    have hbdd : BddBelow (g '' A) := ⟨0, by rintro _ ⟨v, _, rfl⟩; exact hg v⟩
    have := csInf_le hbdd (Set.mem_image_of_mem g hu)
    linarith [h u]
  linarith

theorem cond_gap_shift : Claims.cond_gap_shift := by
  intro n K f f' Z A i hA
  have : Nonempty (Fin n) := ⟨i⟩
  apply le_mul_potOsc (by norm_num) f f'
  intro c
  have hF := gap_integrand_shift f f' Z i c
  set F := fun u => (⨆ k, score (condA f Z) (condB Z) k u) - score (condA f Z) (condB Z) i u
  set F' := fun u => (⨆ k, score (condA f' Z) (condB Z) k u) - score (condA f' Z) (condB Z) i u
  have hF0 : ∀ u, 0 ≤ F u := fun u =>
    sub_nonneg.mpr (le_iSup_fin' (fun k => score (condA f Z) (condB Z) k u) i)
  have hF0' : ∀ u, 0 ≤ F' u := fun u =>
    sub_nonneg.mpr (le_iSup_fin' (fun k => score (condA f' Z) (condB Z) k u) i)
  have h1 := sInf_shift hA F F' (2 * ⨆ j, |f j - f' j - c|) hF0 hF0' fun u => by
    show F u ≤ F' u + _
    simp only [F, F']; linarith [(abs_le.mp (hF u)).2]
  have h2 := sInf_shift hA F' F (2 * ⨆ j, |f j - f' j - c|) hF0' hF0 fun u => by
    show F' u ≤ F u + _
    simp only [F, F']; linarith [(abs_le.mp (hF u)).1]
  show |sInf (F '' A) - sInf (F' '' A)| ≤ _
  rw [abs_le]; constructor <;> linarith

theorem cond_witness_shift : Claims.cond_witness_shift := by
  intro n K f f' Z A ω i hω
  apply le_mul_potOsc (by norm_num) f f'
  intro c
  set D := ⨆ j, |f j - f' j - c|
  have hk : ∀ k, |f k - f' k - c| ≤ D := abs_le_Dc f f' c
  have hdiff : condWitness f Z A ω i - condWitness f' Z A ω i =
      ∑ k, ω k * (f k - f' k - c) - (f i - f' i - c) := by
    simp only [condWitness, condA]
    have : ∑ k, ω k * (f k - f' k - c) = ∑ k, ω k * (f k - Z k ⬝ᵥ Z k) -
        ∑ k, ω k * (f' k - Z k ⬝ᵥ Z k) - c * ∑ k, ω k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, hω.2]; ring
  rw [hdiff]
  have hsum : |∑ k, ω k * (f k - f' k - c)| ≤ D := by
    calc |∑ k, ω k * (f k - f' k - c)| ≤ ∑ k, |ω k * (f k - f' k - c)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, ω k * D := by
          apply Finset.sum_le_sum; intro k _
          rw [abs_mul, abs_of_nonneg (hω.1 k)]
          exact mul_le_mul_of_nonneg_left (hk k) (hω.1 k)
      _ = D := by rw [← Finset.sum_mul, hω.2, one_mul]
  calc |∑ k, ω k * (f k - f' k - c) - (f i - f' i - c)|
      ≤ |∑ k, ω k * (f k - f' k - c)| + |f i - f' i - c| := abs_sub _ _
    _ ≤ D + D := add_le_add hsum (hk i)
    _ = 2 * D := by ring

/-! ### Euclidean helpers -/

lemma dot_self_nonneg (x : Fin K → ℝ) : 0 ≤ x ⬝ᵥ x := by
  simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

lemma eucl_sq (x : Fin K → ℝ) : eucl x ^ 2 = x ⬝ᵥ x := Real.sq_sqrt (dot_self_nonneg x)

lemma eucl_add_le (x y : Fin K → ℝ) : eucl (x + y) ≤ eucl x + eucl y := by
  have h1 := dot_le_eucl x y
  have h2 : eucl (x + y) ^ 2 ≤ (eucl x + eucl y) ^ 2 := by
    rw [eucl_sq, add_sq, eucl_sq, eucl_sq]
    simp only [add_dotProduct, dotProduct_add, dotProduct_comm y x]
    linarith
  exact (pow_le_pow_iff_left₀ (eucl_nonneg _) (add_nonneg (eucl_nonneg _) (eucl_nonneg _))
    two_ne_zero).mp h2

lemma eucl_smul (a : ℝ) (x : Fin K → ℝ) : eucl (a • x) = |a| * eucl x := by
  unfold eucl
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Real.sqrt_mul (mul_self_nonneg a), Real.sqrt_mul_self_eq_abs]

lemma eucl_zero : eucl (0 : Fin K → ℝ) = 0 := by simp [eucl]

lemma eucl_sum_le {ι : Type*} (s : Finset ι) (g : ι → Fin K → ℝ) :
    eucl (∑ i ∈ s, g i) ≤ ∑ i ∈ s, eucl (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eucl_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (eucl_add_le _ _).trans (add_le_add le_rfl ih)

lemma eucl_neg (x : Fin K → ℝ) : eucl (-x) = eucl x := by
  unfold eucl; rw [neg_dotProduct, dotProduct_neg, neg_neg]

/-! ### Entropic map -/

lemma softmax_sub_const (x : Fin n → ℝ) (c : ℝ) (j : Fin n) :
    softmax (fun k => x k - c) j = softmax x j := by
  unfold softmax
  simp only [Real.exp_sub]
  rw [← Finset.sum_div, div_div_div_cancel_right₀ (Real.exp_pos c).ne']

lemma condMapEnt_eq (ε : ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (u : Fin K → ℝ) :
    condMapEnt ε f Z u = Qent ε 1 Z f u := by
  unfold condMapEnt Qent entWeights
  congr 1; ext1 i; congr 1
  rw [← softmax_sub_const (fun k => score (condA f Z) (condB Z) k u / ε) (u ⬝ᵥ u / ε) i]
  congr 1; ext1 k
  simp only [score, condA, condB, mnormSq, one_mulVec, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, smul_eq_mul, dotProduct_comm u (Z k)]
  ring

theorem cond_map_ent : Claims.cond_map_ent := by
  intro n K ε R f f' Z hε hR u
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [condMapEnt, eucl_zero]
    have := potOsc_nonneg f f'
    simp [potOsc, Real.iSup_of_isEmpty]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hR0 : 0 ≤ R := (eucl_nonneg _).trans (hR ⟨0, hn⟩)
  set w := condMapEnt ε f Z u - condMapEnt ε f' Z u with hw
  have hdot : w ⬝ᵥ w ≤ Real.tanh (((⨆ j, (f j - f' j)) - ⨅ j, (f j - f' j)) / (4 * ε)) *
      ((⨆ j, w ⬝ᵥ Z j) - ⨅ j, w ⬝ᵥ Z j) := by
    have := ext_solver_error n K ε 1 Z f f' u w hn hε Matrix.PosDef.one
    rw [← condMapEnt_eq, ← condMapEnt_eq, ← hw] at this
    exact (le_abs_self _).trans this
  have hrange : (⨆ j, w ⬝ᵥ Z j) - ⨅ j, w ⬝ᵥ Z j ≤ 2 * R * eucl w := by
    have hup : (⨆ j, w ⬝ᵥ Z j) ≤ eucl w * R := ciSup_le fun j =>
      (dot_le_eucl w (Z j)).trans (mul_le_mul_of_nonneg_left (hR j) (eucl_nonneg _))
    have hlo : -(eucl w * R) ≤ ⨅ j, w ⬝ᵥ Z j := le_ciInf fun j => by
      have := dot_le_eucl (-w) (Z j)
      rw [eucl_neg, neg_dotProduct] at this
      nlinarith [mul_le_mul_of_nonneg_left (hR j) (eucl_nonneg w)]
    linarith
  have hrange0 : 0 ≤ (⨆ j, w ⬝ᵥ Z j) - ⨅ j, w ⬝ᵥ Z j :=
    sub_nonneg.mpr ((iInf_le_fin' (fun j => w ⬝ᵥ Z j) ⟨0, hn⟩).trans
      (le_iSup_fin' (fun j => w ⬝ᵥ Z j) ⟨0, hn⟩))
  have key : ∀ c, eucl w ≤ (R / ε) * ⨆ i, |f i - f' i - c| := by
    intro c
    set D := ⨆ i, |f i - f' i - c| with hD
    have hD0 : 0 ≤ D := Dc_nonneg f f' c
    have hosc : (⨆ j, (f j - f' j)) - (⨅ j, (f j - f' j)) ≤ 2 * D := by
      have h1 : (⨆ j, (f j - f' j)) ≤ c + D := ciSup_le fun j => by
        linarith [(abs_le.mp (abs_le_Dc f f' c j)).2]
      have h2 : c - D ≤ ⨅ j, (f j - f' j) := le_ciInf fun j => by
        linarith [(abs_le.mp (abs_le_Dc f f' c j)).1]
      linarith
    have hosc0 : 0 ≤ (⨆ j, (f j - f' j)) - (⨅ j, (f j - f' j)) :=
      sub_nonneg.mpr ((iInf_le_fin' (fun j => f j - f' j) ⟨0, hn⟩).trans
        (le_iSup_fin' (fun j => f j - f' j) ⟨0, hn⟩))
    have hy0 : 0 ≤ ((⨆ j, (f j - f' j)) - (⨅ j, (f j - f' j))) / (4 * ε) :=
      div_nonneg hosc0 (by positivity)
    have ht : Real.tanh (((⨆ j, (f j - f' j)) - (⨅ j, (f j - f' j))) / (4 * ε)) ≤ D / (2 * ε) := by
      refine (tanh_le_self hy0).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hsq : eucl w ^ 2 ≤ D / (2 * ε) * (2 * R * eucl w) := by
      rw [eucl_sq]
      exact hdot.trans (mul_le_mul ht hrange hrange0 (by positivity))
    have e : D / (2 * ε) * (2 * R * eucl w) = (R / ε * D) * eucl w := by
      field_simp
    rw [e] at hsq
    by_cases h0 : eucl w = 0
    · rw [h0]; positivity
    · have hpos : 0 < eucl w := lt_of_le_of_ne (eucl_nonneg _) (Ne.symm h0)
      have : eucl w * eucl w ≤ (R / ε * D) * eucl w := by nlinarith
      exact le_of_mul_le_mul_right this hpos
  calc eucl w ≤ R / ε * potOsc f f' := le_mul_potOsc (div_nonneg hR0 hε.le) f f' key
    _ = R * potOsc f f' / ε := div_mul_eq_mul_div _ _ _

/-! ### Quadratic map -/

lemma proj_VI {x q : Fin n → ℝ} (hq : IsSimplexProj x q) {p : Fin n → ℝ} (hp : p ∈ simplex n) :
    0 ≤ ∑ i, (q i - x i) * (p i - q i) := by
  set A := ∑ i, (q i - x i) * (p i - q i) with hAdef
  set B := ∑ i, (p i - q i) ^ 2 with hBdef
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => sq_nonneg _
  have key : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ 2 * t * A + t ^ 2 * B := by
    intro t ht0 ht1
    have hmem : (fun i => q i + t * (p i - q i)) ∈ simplex n := by
      refine ⟨fun i => ?_, ?_⟩
      · show 0 ≤ q i + t * (p i - q i)
        have h1 := hq.1.1 i; have h2 := hp.1 i
        have : q i + t * (p i - q i) = (1 - t) * q i + t * p i := by ring
        rw [this]
        exact add_nonneg (mul_nonneg (by linarith) h1) (mul_nonneg ht0 h2)
      · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hq.1.2,
          hp.2]
        ring
    have h := hq.2 _ hmem
    have e : ∑ i, (q i + t * (p i - q i) - x i) ^ 2 =
        ∑ i, (q i - x i) ^ 2 + (2 * t * A + t ^ 2 * B) := by
      simp only [hAdef, hBdef, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  by_contra hA
  push_neg at hA
  set t := min 1 (-A / (B + 1)) with htdef
  have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ -A / (B + 1) := min_le_right _ _
  have h := key t ht0.le ht1
  have h' : 0 ≤ 2 * A + t * B := by
    have : 0 ≤ t * (2 * A + t * B) := by nlinarith
    exact (mul_nonneg_iff_of_pos_left ht0).mp this
  have h3 : t * (B + 1) ≤ -A := by rwa [le_div_iff₀ (by linarith)] at ht2
  nlinarith

theorem cond_map_quad : Claims.cond_map_quad := by
  intro n K m γ R f f' Z u q q' hγ hm hR hq hq'
  have hlam : 0 < γ / (m : ℝ) := div_pos hγ (by exact_mod_cast hm)
  set lam := γ / (m : ℝ) with hlamdef
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [eucl_zero]
  have hR0 : 0 ≤ R := (eucl_nonneg _).trans (hR ⟨0, hn⟩)
  set x := fun k => score (condA f Z) (condB Z) k u / lam with hx
  set x' := fun k => score (condA f' Z) (condB Z) k u / lam with hx'
  set S := ∑ i, |q i - q' i| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hl1 : ∀ c, S ≤ n * ((⨆ i, |f i - f' i - c|) / lam) := by
    intro c
    set D := ⨆ i, |f i - f' i - c| with hD
    have hD0 : 0 ≤ D := Dc_nonneg f f' c
    have hxy : ∀ i, |x i - (x' i + c / lam)| ≤ D / lam := by
      intro i
      have : x i - (x' i + c / lam) = (f i - f' i - c) / lam := by
        simp only [hx, hx', condScore_diff f f' Z i u]
        field_simp
        ring
      rw [this, abs_div, abs_of_pos hlam]
      exact div_le_div_of_nonneg_right (abs_le_Dc f f' c i) hlam.le
    have v1 := proj_VI hq hq'.1
    have v2 := proj_VI hq' hq.1
    have hsh : ∑ i, (c / lam) * (q i - q' i) = 0 := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hq.1.2, hq'.1.2]; ring
    have hsq : ∑ i, (q i - q' i) ^ 2 ≤ ∑ i, (x i - (x' i + c / lam)) * (q i - q' i) := by
      have e : ∑ i, (x i - (x' i + c / lam)) * (q i - q' i) - ∑ i, (q i - q' i) ^ 2 =
          ∑ i, (q i - x i) * (q' i - q i) + ∑ i, (q' i - x' i) * (q i - q' i) -
            ∑ i, (c / lam) * (q i - q' i) := by
        simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      linarith
    have hsq2 : ∑ i, (q i - q' i) ^ 2 ≤ D / lam * S := by
      calc ∑ i, (q i - q' i) ^ 2 ≤ ∑ i, (x i - (x' i + c / lam)) * (q i - q' i) := hsq
        _ ≤ ∑ i, |x i - (x' i + c / lam)| * |q i - q' i| :=
            Finset.sum_le_sum fun i _ => by rw [← abs_mul]; exact le_abs_self _
        _ ≤ ∑ i, D / lam * |q i - q' i| :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hxy i) (abs_nonneg _)
        _ = D / lam * S := by rw [Finset.mul_sum]
    have hcs : S ^ 2 ≤ n * ∑ i, (q i - q' i) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => |q i - q' i|)
      simpa [sq_abs] using this
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hS2 : S * S ≤ (n * (D / lam)) * S := by
      have := mul_le_mul_of_nonneg_left hsq2 hnn
      nlinarith
    by_cases hS : S = 0
    · rw [hS]; positivity
    · exact le_of_mul_le_mul_right hS2 (lt_of_le_of_ne hS0 (Ne.symm hS))
  have hmap : eucl (∑ i, q i • Z i - ∑ i, q' i • Z i) ≤ R * S := by
    rw [← Finset.sum_sub_distrib]
    calc eucl (∑ i, (q i • Z i - q' i • Z i)) = eucl (∑ i, (q i - q' i) • Z i) := by
          simp_rw [sub_smul]
      _ ≤ ∑ i, eucl ((q i - q' i) • Z i) := eucl_sum_le _ _
      _ = ∑ i, |q i - q' i| * eucl (Z i) := by simp_rw [eucl_smul]
      _ ≤ ∑ i, |q i - q' i| * R :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hR i) (abs_nonneg _)
      _ = R * S := by rw [← Finset.sum_mul, mul_comm]
  have key : ∀ c, eucl (∑ i, q i • Z i - ∑ i, q' i • Z i) ≤
      (n * R / lam) * ⨆ i, |f i - f' i - c| := fun c => by
    calc eucl (∑ i, q i • Z i - ∑ i, q' i • Z i) ≤ R * S := hmap
      _ ≤ R * (n * ((⨆ i, |f i - f' i - c|) / lam)) := mul_le_mul_of_nonneg_left (hl1 c) hR0
      _ = (n * R / lam) * ⨆ i, |f i - f' i - c| := by ring
  calc eucl (∑ i, q i • Z i - ∑ i, q' i • Z i) ≤ n * R / lam * potOsc f f' :=
        le_mul_potOsc (by positivity) f f' key
    _ = n * R * potOsc f f' / lam := by ring

/-! ### Edges -/

lemma hsup_shift (T T' : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ)) (v : Fin K → ℝ) (r : ℝ)
    (h : ∀ u, v ⬝ᵥ T u ≤ v ⬝ᵥ T' u + r) : hsup T A v ≤ hsup T' A v + (r : EReal) := by
  unfold hsup
  apply iSup₂_le
  intro u hu
  calc ((v ⬝ᵥ T u : ℝ) : EReal) ≤ ((v ⬝ᵥ T' u + r : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (h u)
    _ = ((v ⬝ᵥ T' u : ℝ) : EReal) + (r : EReal) := EReal.coe_add _ _
    _ ≤ (⨆ u ∈ A, ((v ⬝ᵥ T' u : ℝ) : EReal)) + r :=
        add_le_add (le_iSup₂_of_le (f := fun u _ => ((v ⬝ᵥ T' u : ℝ) : EReal)) u hu le_rfl) le_rfl

lemma ereal_sub_aux (m r : ℝ) (X Y : EReal) (h : Y ≤ X + r) :
    (m : EReal) - X ≤ (m : EReal) - Y + r := by
  induction X using EReal.rec with
  | bot =>
    have : Y = ⊥ := by simpa using h
    subst this; simp
  | top => simp
  | coe x =>
    induction Y using EReal.rec with
    | bot => simp
    | top => simp at h
    | coe y =>
      have h' : y ≤ x + r := by exact_mod_cast h
      exact_mod_cast (by linarith : m - x ≤ m - y + r)

theorem cond_edge_shift : Claims.cond_edge_shift := by
  intro K T T' A mo B E v hB hE
  have hE0 : 0 ≤ E := (eucl_nonneg v).trans hE
  have hbound : ∀ (S S' : (Fin K → ℝ) → Fin K → ℝ) (w : Fin K → ℝ), eucl w ≤ E →
      (∀ u, eucl (S u - S' u) ≤ B) → ∀ u, w ⬝ᵥ S u ≤ w ⬝ᵥ S' u + E * B := by
    intro S S' w hw hSS u
    have h1 := dot_le_eucl w (S u - S' u)
    rw [dotProduct_sub] at h1
    have h2 : eucl w * eucl (S u - S' u) ≤ E * B :=
      mul_le_mul hw (hSS u) (eucl_nonneg _) hE0
    linarith
  have hB' : ∀ u, eucl (T' u - T u) ≤ B := fun u => by
    rw [← neg_sub, eucl_neg]; exact hB u
  have hEn : eucl (-v) ≤ E := by rw [eucl_neg]; exact hE
  have u1 := hsup_shift T T' A v _ (hbound T T' v hE hB)
  have u2 := hsup_shift T' T A v _ (hbound T' T v hE hB')
  have l1 := hsup_shift T T' A (-v) _ (hbound T T' (-v) hEn hB)
  have l2 := hsup_shift T' T A (-v) _ (hbound T' T (-v) hEn hB')
  unfold edgeUp edgeLo
  refine ⟨?_, ?_, ereal_sub_aux _ _ _ _ l2, ereal_sub_aux _ _ _ _ l1⟩
  · rw [add_assoc]; exact add_le_add le_rfl u1
  · rw [add_assoc]; exact add_le_add le_rfl u2

end StatFormal.OTFD.Wave2
