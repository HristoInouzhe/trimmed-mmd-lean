import StatFormal.Archive.WaveP1d.Statements
import StatFormal.Archive.Wave24c.RoutePaths

/-!
# Route: otfd B `prop:rk-paths` (i), strictness (untrusted)

With `M` symmetric, `‖tv − Z_j‖²_M = t²‖v‖²_M − 2t⟨Z_j, Mv⟩ + ‖Z_j‖²_M`, and the softmax ignores the common term, so
`⟨Mv, Q̂(tv)⟩ = Σ_j softmax_j((a_j + 2t c_j)/ε) c_j` with `c_j = ⟨Z_j, Mv⟩`: the one-dimensional entropic map
`lseMap` of the certified Wave 24c route at the point `t·1 ∈ ℝ`. Its ray is strictly increasing when the `c_j` are not
all equal (the certified `lseMap_path_strictMonoOn` with `z = c` affinely spanning `ℝ`), which holds because the `Z_j`
affinely span `ℝ^K` and `Mv ≠ 0`; and `p ↦ τ_{K,p}` is strictly increasing (certified `cdfKInv_strictMonoOn`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Finset Matrix
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.WaveP1d

namespace RouteRkPaths

open StatFormal.OTFD.Bands (softmax Qent mnormSq)

lemma softmax_add_const {n : ℕ} (x : Fin n → ℝ) (c : ℝ) :
    softmax (fun j => x j + c) = softmax x := by
  funext j
  unfold softmax
  simp only [Real.exp_add, ← Finset.sum_mul]
  by_cases h : (∑ k, Real.exp (x k)) = 0
  · simp [h]
  · have : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
    field_simp

/-- The path value as a one-dimensional entropic map. -/
lemma path_eq {K n : ℕ} (ε : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (hM : M.IsHermitian) (Z : Fin n → Fin K → ℝ)
    (f : Fin n → ℝ) (v : Fin K → ℝ) (t : ℝ) :
    (M *ᵥ v) ⬝ᵥ Qent ε M Z f (t • v) =
      StatFormal.Wave24c.lseMap ε 2 (fun j => f j - mnormSq M (Z j)) (fun j => Z j ⬝ᵥ (M *ᵥ v))
        (t • (1 : ℝ)) := by
  have hsym : Mᵀ = M := by simpa using hM.eq
  have hscore : (fun j => (f j - mnormSq M (t • v - Z j)) / ε) =
      fun j => ((f j - mnormSq M (Z j)) + 2 * ⟪Z j ⬝ᵥ (M *ᵥ v), t • (1 : ℝ)⟫) / ε +
        (-(t ^ 2 * (v ⬝ᵥ (M *ᵥ v))) / ε) := by
    funext j
    have hvZ : v ⬝ᵥ (M *ᵥ Z j) = Z j ⬝ᵥ (M *ᵥ v) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
    simp only [mnormSq, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hvZ]
    simp only [real_inner_eq_re_inner, RCLike.re_to_real]
    simp
    ring
  unfold Qent StatFormal.Wave24c.lseMap
  rw [hscore, softmax_add_const]
  simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, real_inner_eq_re_inner]
  simp [mul_comm, dotProduct_comm]


/-- A real family with two distinct values affinely spans `ℝ`. -/
lemma affineSpan_real_eq_top {n : ℕ} (c : Fin n → ℝ) {i j : Fin n} (hij : c i ≠ c j) :
    affineSpan ℝ (Set.range c) = ⊤ := by
  have hne : (affineSpan ℝ (Set.range c) : Set ℝ).Nonempty :=
    ⟨c i, subset_affineSpan ℝ _ ⟨i, rfl⟩⟩
  refine (AffineSubspace.direction_eq_top_iff_of_nonempty hne).1 ?_
  rw [direction_affineSpan]
  have hmem : c i - c j ∈ vectorSpan ℝ (Set.range c) :=
    vsub_mem_vectorSpan ℝ ⟨i, rfl⟩ ⟨j, rfl⟩
  rw [eq_top_iff]
  intro x _
  have hx : x = (x / (c i - c j)) • (c i - c j) := by
    rw [smul_eq_mul, div_mul_cancel₀ _ (sub_ne_zero.2 hij)]
  rw [hx]
  exact Submodule.smul_mem _ _ hmem

/-- If the `Z_j` affinely span `ℝ^K` and `w ≠ 0`, the values `⟨Z_j, w⟩` are not all equal. -/
lemma exists_ne_dot {K n : ℕ} (Z : Fin n → Fin K → ℝ) (hspan : affineSpan ℝ (Set.range Z) = ⊤)
    {w : Fin K → ℝ} (hw : w ≠ 0) : ∃ i j, Z i ⬝ᵥ w ≠ Z j ⬝ᵥ w := by
  by_contra hcon
  push Not at hcon
  let ℓ : (Fin K → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => x ⬝ᵥ w
      map_add' := fun x y => add_dotProduct x y w
      map_smul' := fun r x => by simp [smul_dotProduct] }
  have hvs : vectorSpan ℝ (Set.range Z) = ⊤ := by
    rw [← direction_affineSpan, hspan, AffineSubspace.direction_top]
  have hle : vectorSpan ℝ (Set.range Z) ≤ LinearMap.ker ℓ := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro x ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub]
    show (Z i - Z j) ⬝ᵥ w = 0
    rw [sub_dotProduct, hcon i j, sub_self]
  have hw0 : w ∈ LinearMap.ker ℓ := hle (by rw [hvs]; exact Submodule.mem_top)
  have : w ⬝ᵥ w = 0 := hw0
  exact hw (dotProduct_self_eq_zero.1 this)


lemma mulVec_ne_zero_of_posDef {K : ℕ} {M : Matrix (Fin K) (Fin K) ℝ} (hM : M.PosDef) {v : Fin K → ℝ}
    (hv : v ≠ 0) : M *ᵥ v ≠ 0 := by
  intro h
  have := hM.dotProduct_mulVec_pos hv
  simp [h] at this

end RouteRkPaths

open RouteRkPaths StatFormal.OTFD.Bands

theorem rk_paths_strict : Claims.rk_paths_strict := by
  intro K n ε M Z f μ ρ v hε hM hspan hv hc h0 h1
  obtain ⟨i, j, hij⟩ := exists_ne_dot Z hspan (mulVec_ne_zero_of_posDef hM hv)
  have hspan1 := affineSpan_real_eq_top (fun j => Z j ⬝ᵥ (M *ᵥ v)) hij
  have hstrict := StatFormal.Wave24c.lseMap_path_strictMonoOn hε two_pos (fun j => f j - mnormSq M (Z j))
    _ hspan1 one_ne_zero (StatFormal.Wave24c.cdfKInv_strictMonoOn μ ρ hc h0 h1)
  intro p hp q hq hpq
  have := hstrict hp hq hpq
  simp only [RCLike.inner_apply, conj_trivial] at this
  simp only [path_eq ε M hM.1 Z f v]
  simpa using this

end StatFormal.WaveP1d
