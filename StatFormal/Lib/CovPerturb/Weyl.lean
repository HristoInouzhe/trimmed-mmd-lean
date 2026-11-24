import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Eigenvalue and eigenvector perturbation for operators with ordered eigenbases (untrusted library)

For bounded operators `A, B` on a real Hilbert space, each with a complete orthonormal eigenbasis whose eigenvalues are
listed in nonincreasing order:
* `weyl_half`, `abs_sub_le_weyl`: Weyl's inequality `|μ_k − λ_k| ≤ ‖B − A‖` (Courant–Fischer through a kernel vector);
* `one_sub_sq_le_bosq`: Bosq's eigenvector bound `1 − ⟨ê_k, e_k⟩² ≤ 4‖B − A‖²/s²` when `|λ_j − λ_k| ≥ s > 0` for
  every `j ≠ k`;
* `norm_sign_sub_sq_le`: `‖η ê − e‖² = 2 − 2|⟨ê, e⟩| ≤ 2(1 − ⟨ê, e⟩²)` for unit vectors, `η ⟨ê, e⟩ = |⟨ê, e⟩|`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open Filter Topology
open scoped RealInnerProductSpace

namespace StatFormal.CovPerturb

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Expansion in a complete orthonormal family. -/
lemma hasSum_repr_of {b : ℕ → H} (hon : Orthonormal ℝ b)
    (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range b)).topologicalClosure) (v : H) :
    HasSum (fun j => ⟪b j, v⟫ • b j) v := by
  have := (HilbertBasis.mk hon hsp).hasSum_repr v
  simpa only [HilbertBasis.repr_apply_apply, HilbertBasis.coe_mk] using this

/-- Parseval in a complete orthonormal family. -/
lemma hasSum_sq_inner {b : ℕ → H} (hon : Orthonormal ℝ b)
    (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range b)).topologicalClosure) (v : H) :
    HasSum (fun j => ⟪b j, v⟫ ^ 2) (‖v‖ ^ 2) := by
  have := (HilbertBasis.mk hon hsp).hasSum_inner_mul_inner v v
  simp only [HilbertBasis.coe_mk] at this
  rw [← real_inner_self_eq_norm_sq]
  refine this.congr_fun fun j => ?_
  rw [real_inner_comm v (b j), sq]

/-- `⟨B v, v⟩ = Σ_j μ_j ⟨b_j, v⟩²` for an eigenbasis `b` of `B`. -/
lemma hasSum_inner_apply {b : ℕ → H} (hon : Orthonormal ℝ b)
    (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range b)).topologicalClosure) (B : H →L[ℝ] H) {μ : ℕ → ℝ}
    (hB : ∀ j, B (b j) = μ j • b j) (v : H) :
    HasSum (fun j => μ j * ⟪b j, v⟫ ^ 2) ⟪B v, v⟫ := by
  have h2 := ((hasSum_repr_of hon hsp v).mapL B).mapL (innerSL ℝ v)
  rw [real_inner_comm]
  refine h2.congr_fun fun j => ?_
  simp only [Function.comp_apply, map_smul, hB, innerSL_apply_apply, inner_smul_right]
  rw [real_inner_comm v (b j)]; ring

/-- `⟨b_j, B v⟩ = μ_j ⟨b_j, v⟩` for an eigenbasis `b` of `B` (no symmetry of `B` needed). -/
lemma inner_apply_eigen {b : ℕ → H} (hon : Orthonormal ℝ b)
    (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range b)).topologicalClosure) (B : H →L[ℝ] H) {μ : ℕ → ℝ}
    (hB : ∀ j, B (b j) = μ j • b j) (v : H) (j : ℕ) :
    ⟪b j, B v⟫ = μ j * ⟪b j, v⟫ := by
  have h2 := ((hasSum_repr_of hon hsp v).mapL B).mapL (innerSL ℝ (b j))
  have h3 : HasSum (fun i => if i = j then μ j * ⟪b j, v⟫ else 0) (μ j * ⟪b j, v⟫) := hasSum_ite_eq j _
  refine h2.unique (h3.congr_fun fun i => ?_)
  simp only [Function.comp_apply, map_smul, hB, innerSL_apply_apply, inner_smul_right]
  by_cases hij : i = j
  · subst hij; simp [real_inner_self_eq_norm_sq, hon.1 i, mul_comm]
  · simp [hij, hon.2 (Ne.symm hij)]

/-- **Weyl, one half.** `A` has eigenvectors `a_0, …, a_k` (orthonormal) with `λ_i ≥ λ_k`; `B` has a complete
orthonormal eigenbasis with nonincreasing eigenvalues `μ`. Then `λ_k ≤ μ_k + ‖A − B‖`. -/
theorem weyl_half {A B : H →L[ℝ] H} {a b : ℕ → H} {lam mu : ℕ → ℝ} (k : ℕ)
    (ha : Orthonormal ℝ a) (hA : ∀ i ≤ k, A (a i) = lam i • a i) (hlam : ∀ i ≤ k, lam k ≤ lam i)
    (hb : Orthonormal ℝ b) (hbsp : ⊤ ≤ (Submodule.span ℝ (Set.range b)).topologicalClosure)
    (hB : ∀ j, B (b j) = mu j • b j) (hmu : Antitone mu) :
    lam k ≤ mu k + ‖A - B‖ := by
  classical
  set a' : Fin (k + 1) → H := fun i => a i with ha'_def
  have ha' : Orthonormal ℝ a' := ha.comp (fun i : Fin (k + 1) => (i : ℕ)) Fin.val_injective
  let L : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
    { toFun := fun c j => ⟪b j, ∑ i, c i • a' i⟫
      map_add' := fun c d => by
        funext j; simp [add_smul, Finset.sum_add_distrib, inner_add_right]
      map_smul' := fun r c => by
        funext j; simp [inner_smul_right, inner_sum, Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨c, hcL, hc0⟩ := (Submodule.ne_bot_iff _).1 hker
  set v := ∑ i, c i • a' i with hv
  have hLc : ∀ j : Fin k, ⟪b j, v⟫ = 0 := fun j => congrFun (LinearMap.mem_ker.1 hcL) j
  have hnorm : ‖v‖ ^ 2 = ∑ i, c i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hv, ha'.inner_sum c c Finset.univ]
    simp [sq]
  have hpos : 0 < ‖v‖ ^ 2 := by
    rw [hnorm]
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h; push_neg at h; exact hc0 (funext h)
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩
  -- `⟨A v, v⟩ ≥ λ_k ‖v‖²`
  have hAv : A v = ∑ i, (c i * lam i) • a' i := by
    rw [hv, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ha'_def]; simp only
    rw [hA i (Nat.lt_succ_iff.1 i.2), smul_smul]
  have hA1 : lam k * ‖v‖ ^ 2 ≤ ⟪A v, v⟫ := by
    rw [hAv, hv, ha'.inner_sum, hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [starRingEnd_apply, star_trivial]
    have := hlam i (Nat.lt_succ_iff.1 i.2)
    nlinarith [sq_nonneg (c i)]
  -- `⟨B v, v⟩ ≤ μ_k ‖v‖²`
  have hB1 : ⟪B v, v⟫ ≤ mu k * ‖v‖ ^ 2 := by
    refine hasSum_le (fun j => ?_) (hasSum_inner_apply hb hbsp B hB v)
      ((hasSum_sq_inner hb hbsp v).mul_left (mu k))
    by_cases hj : j < k
    · have := hLc ⟨j, hj⟩; simp only at this; simp [this]
    · exact mul_le_mul_of_nonneg_right (hmu (not_lt.1 hj)) (sq_nonneg _)
  have hAB : ⟪(A - B) v, v⟫ ≤ ‖A - B‖ * ‖v‖ ^ 2 := by
    calc ⟪(A - B) v, v⟫ ≤ ‖(A - B) v‖ * ‖v‖ := real_inner_le_norm _ _
      _ ≤ ‖A - B‖ * ‖v‖ * ‖v‖ := mul_le_mul_of_nonneg_right ((A - B).le_opNorm v) (norm_nonneg _)
      _ = ‖A - B‖ * ‖v‖ ^ 2 := by ring
  have hsplit : ⟪A v, v⟫ = ⟪B v, v⟫ + ⟪(A - B) v, v⟫ := by
    rw [sub_apply, inner_sub_left]; ring
  have : lam k * ‖v‖ ^ 2 ≤ (mu k + ‖A - B‖) * ‖v‖ ^ 2 := by nlinarith
  exact le_of_mul_le_mul_right this hpos

/-- **Weyl's inequality** for two operators with ordered complete orthonormal eigenbases. -/
theorem abs_sub_le_weyl {A B : H →L[ℝ] H} {a b : ℕ → H} {lam mu : ℕ → ℝ}
    (ha : Orthonormal ℝ a) (hasp : ⊤ ≤ (Submodule.span ℝ (Set.range a)).topologicalClosure)
    (hA : ∀ i, A (a i) = lam i • a i) (hlam : Antitone lam)
    (hb : Orthonormal ℝ b) (hbsp : ⊤ ≤ (Submodule.span ℝ (Set.range b)).topologicalClosure)
    (hB : ∀ j, B (b j) = mu j • b j) (hmu : Antitone mu) (k : ℕ) :
    |mu k - lam k| ≤ ‖B - A‖ := by
  have h1 := weyl_half k ha (fun i _ => hA i) (fun i hi => hlam hi) hb hbsp hB hmu
  have h2 := weyl_half k hb (fun i _ => hB i) (fun i hi => hmu hi) ha hasp hA hlam
  rw [norm_sub_rev] at h1
  rw [abs_le]; constructor <;> linarith

/-- **Bosq's eigenvector bound.** With `A`, `B` as in `abs_sub_le_weyl` and `|λ_j − λ_k| ≥ s > 0` for all `j ≠ k`,
`1 − ⟨b_k, a_k⟩² ≤ 4‖B − A‖²/s²`. -/
theorem one_sub_sq_le_bosq {A B : H →L[ℝ] H} {a b : ℕ → H} {lam mu : ℕ → ℝ}
    (ha : Orthonormal ℝ a) (hasp : ⊤ ≤ (Submodule.span ℝ (Set.range a)).topologicalClosure)
    (hA : ∀ i, A (a i) = lam i • a i) (hlam : Antitone lam)
    (hb : Orthonormal ℝ b) (hbsp : ⊤ ≤ (Submodule.span ℝ (Set.range b)).topologicalClosure)
    (hB : ∀ j, B (b j) = mu j • b j) (hmu : Antitone mu) {k : ℕ} {s : ℝ} (hs : 0 < s)
    (hsep : ∀ j, j ≠ k → s ≤ |lam j - lam k|) :
    1 - ⟪b k, a k⟫ ^ 2 ≤ 4 * ‖B - A‖ ^ 2 / s ^ 2 := by
  set δ := ‖B - A‖
  set w : H := A (b k) - lam k • b k with hw
  -- `‖w‖ ≤ 2δ`
  have hw' : w = (A - B) (b k) + (mu k - lam k) • b k := by
    rw [hw, sub_apply, hB k, sub_smul]; abel
  have hwn : ‖w‖ ≤ 2 * δ := by
    rw [hw']
    calc ‖(A - B) (b k) + (mu k - lam k) • b k‖ ≤ ‖(A - B) (b k)‖ + ‖(mu k - lam k) • b k‖ := norm_add_le _ _
      _ ≤ ‖A - B‖ * ‖b k‖ + |mu k - lam k| * ‖b k‖ := by
          gcongr
          · exact (A - B).le_opNorm _
          · rw [norm_smul, Real.norm_eq_abs]
      _ ≤ δ + δ := by
          rw [hb.1 k, mul_one, mul_one, norm_sub_rev]
          gcongr
          exact abs_sub_le_weyl ha hasp hA hlam hb hbsp hB hmu k
      _ = 2 * δ := by ring
  -- coefficients of `w` in the basis `a`
  have hcoef : ∀ j, ⟪a j, w⟫ = (lam j - lam k) * ⟪a j, b k⟫ := by
    intro j
    rw [hw, inner_sub_right, inner_apply_eigen ha hasp A hA, inner_smul_right]; ring
  have hpars := hasSum_sq_inner ha hasp w
  have hpars1 := hasSum_sq_inner ha hasp (b k)
  rw [hb.1 k, one_pow] at hpars1
  -- `s² (1 − c_k²) ≤ ‖w‖²`
  have hmain : s ^ 2 * (1 - ⟪a k, b k⟫ ^ 2) ≤ ‖w‖ ^ 2 := by
    have hs1 : HasSum (fun j => if j = k then 0 else s ^ 2 * ⟪a j, b k⟫ ^ 2)
        (s ^ 2 * (1 - ⟪a k, b k⟫ ^ 2)) := by
      have := (hpars1.mul_left (s ^ 2)).update k 0
      convert this using 1
      · funext j; by_cases hj : j = k <;> simp [Function.update, hj]
      · ring
    refine hasSum_le (fun j => ?_) hs1 hpars
    by_cases hj : j = k
    · simp only [hj, if_true]; positivity
    · simp only [hj, ite_false, hcoef]
      have := hsep j hj
      have h1 : s ^ 2 ≤ (lam j - lam k) ^ 2 := by
        rw [← sq_abs (lam j - lam k)]; exact pow_le_pow_left₀ hs.le this 2
      calc s ^ 2 * ⟪a j, b k⟫ ^ 2 ≤ (lam j - lam k) ^ 2 * ⟪a j, b k⟫ ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = ((lam j - lam k) * ⟪a j, b k⟫) ^ 2 := by ring
  have h4 : ‖w‖ ^ 2 ≤ 4 * δ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hwn 2; nlinarith
  rw [real_inner_comm, le_div_iff₀ (by positivity)]
  nlinarith

/-- `‖η ê − e‖² = 2 − 2|⟨ê, e⟩| ≤ 2(1 − ⟨ê, e⟩²)` for unit vectors and `η ⟨ê, e⟩ = |⟨ê, e⟩|`, `η = ±1`. -/
theorem norm_sign_sub_sq_le {e f : H} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) {η : ℝ} (hη : η = 1 ∨ η = -1)
    (hηc : η * ⟪f, e⟫ = |⟪f, e⟫|) :
    ‖η • f - e‖ ^ 2 ≤ 2 * (1 - ⟪f, e⟫ ^ 2) := by
  have hη2 : η ^ 2 = 1 := by rcases hη with rfl | rfl <;> norm_num
  have hexp : ‖η • f - e‖ ^ 2 = 2 - 2 * |⟪f, e⟫| := by
    rw [@norm_sub_sq_real, norm_smul, inner_smul_left, Real.norm_eq_abs, he, hf]
    simp only [conj_trivial, mul_one, one_pow]
    rw [hηc, sq_abs, hη2]; ring
  have hc : |⟪f, e⟫| ≤ 1 := by
    have := abs_real_inner_le_norm f e; rw [he, hf, mul_one] at this; exact this
  rw [hexp, ← sq_abs ⟪f, e⟫]
  nlinarith [abs_nonneg ⟪f, e⟫]

end StatFormal.CovPerturb
