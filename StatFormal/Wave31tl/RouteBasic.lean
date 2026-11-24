import StatFormal.Wave31tl.Statements
import StatFormal.Wave30tz.Proofs
import StatFormal.Wave30tl.RouteCrossing

/-!
# Wave 31tl route: elementary facts (untrusted proof material)

* `gridFloor`: nonnegative, at most its argument (for a grid), attained at a level when positive; the mesh bound at `α⋆ − e`.
* `gap_add`: consecutive gaps `≥ h₀` give `α_j − α_i ≥ (j − i)h₀`.
* `sum_exp_le_Jeps`: the last step of the proof of Theorem 33 (i): with `x_j = (α⋆ − α_j)/ε`, the levels `≤ α⋆ − ε` have
  `Σ_j e^{−A x_j²} ≤ J_ε e^{−A}` for `A ≥ log 2` (at most `1 + ε/h₀` of the `x_j` in each `[1+k, 2+k)`, `(1+k)² ≥ 1 + 3k`, a geometric sum).
* `dpop_le_dphi`: `D_α(P,Q) ≤ ‖μ_P − μ_Q‖ ≤ Δ_φ`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tl

open StatFormal.Wave30tq StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.TrimmedMMD.Unconditional

namespace Basic

/-! ### The grid floor -/

section Floor

variable {J : ℕ} (α : Fin J → ℝ)

lemma gridFloor_nonneg (x : ℝ) : 0 ≤ gridFloor α x := by
  unfold gridFloor
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

lemma gridFloor_le {x : ℝ} (hx : 0 ≤ x) : gridFloor α x ≤ x := by
  classical
  unfold gridFloor
  split_ifs with h
  · exact max_le hx (Finset.sup'_le _ _ fun j hj => (Finset.mem_filter.1 hj).2)
  · exact hx

lemma exists_of_lt_gridFloor {x y : ℝ} (hy : 0 ≤ y) (h : y < gridFloor α x) : ∃ i, α i ≤ x ∧ y < α i := by
  classical
  unfold gridFloor at h
  split_ifs at h with hne
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' hne α
    refine ⟨i, (Finset.mem_filter.1 hi).2, ?_⟩
    rw [heq] at h
    exact (lt_max_iff.1 h).resolve_left (not_lt.2 hy)
  · exact absurd h (not_lt.2 hy)

lemma gridFloor_zero : gridFloor α 0 = 0 :=
  le_antisymm (gridFloor_le α le_rfl) (gridFloor_nonneg α 0)

/-- The mesh bound gives `gridFloor α (α⋆ − e) ≥ α⋆ − e − h` for `e ∈ [0, α⋆]`. -/
lemma floor_ge_of_mesh {αs h e : ℝ} (hmesh : MeshBelowLe α αs h) (he0 : 0 ≤ e) (heα : e ≤ αs) :
    αs - e - h ≤ gridFloor α (αs - e) := by
  have := hmesh (αs - e) ⟨by linarith, by linarith⟩
  linarith

lemma mesh_nonneg {αs h : ℝ} (hmesh : MeshBelowLe α αs h) (hαs : 0 ≤ αs) : 0 ≤ h := by
  have := hmesh 0 ⟨le_rfl, hαs⟩
  rw [gridFloor_zero] at this
  linarith

end Floor

/-! ### Gaps -/

section Gaps

variable {J : ℕ} {α : Fin J → ℝ} {h0 : ℝ}

lemma gap_add (hgap : GapsGe α h0) : ∀ (d : ℕ) (i : Fin J) (hd : i.1 + d < J), α i + d * h0 ≤ α ⟨i.1 + d, hd⟩
  | 0, i, _ => by simp
  | d + 1, i, hd => by
    have h1 := gap_add hgap d i (by omega)
    have h2 := hgap ⟨i.1 + d, by omega⟩ (by simp only; omega)
    have e : (⟨(⟨i.1 + d, by omega⟩ : Fin J).1 + 1, by simp only; omega⟩ : Fin J) = ⟨i.1 + (d + 1), hd⟩ := by
      ext; simp only; omega
    rw [e] at h2
    push_cast
    linarith

lemma gap_le (hgap : GapsGe α h0) {i j : Fin J} (hij : i ≤ j) : α i + ((j : ℕ) - (i : ℕ) : ℕ) * h0 ≤ α j := by
  have hd : i.1 + ((j : ℕ) - (i : ℕ)) < J := by have := j.isLt; have : i.1 ≤ j.1 := hij; omega
  have := gap_add hgap ((j : ℕ) - (i : ℕ)) i hd
  have e : (⟨i.1 + ((j : ℕ) - (i : ℕ)), hd⟩ : Fin J) = j := by ext; simp only; have : i.1 ≤ j.1 := hij; omega
  rwa [e] at this

end Gaps

/-! ### The sum over the levels -/

section Sum

open Finset

variable {J : ℕ} {α : Fin J → ℝ} {h0 ε αs : ℝ}

/-- The geometric sum: `Σ_{k ∈ s} q^k ≤ 1/(1 − q)` for `0 ≤ q < 1`. -/
lemma sum_pow_le (s : Finset ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : ∑ k ∈ s, q ^ k ≤ 1 / (1 - q) := by
  obtain ⟨M, hM⟩ : ∃ M, s ⊆ range M := ⟨s.sup id + 1, fun k hk => mem_range.2 (Nat.lt_succ_of_le (le_sup (f := id) hk))⟩
  calc ∑ k ∈ s, q ^ k ≤ ∑ k ∈ range M, q ^ k :=
        sum_le_sum_of_subset_of_nonneg hM fun k _ _ => pow_nonneg hq0 k
    _ ≤ 1 / (1 - q) := by
        rw [geom_sum_eq hq1.ne, le_div_iff₀ (by linarith)]
        have : 0 ≤ q ^ M := pow_nonneg hq0 M
        rw [div_mul_eq_mul_div, div_le_iff_of_neg (by linarith)]
        nlinarith

/-- At most `1 + ε/h₀` levels of a grid with gaps `≥ h₀` lie in an interval of length `< ε`. -/
lemma card_le_of_spread (hgap : GapsGe α h0) (hh0 : 0 < h0) (hε : 0 ≤ ε) (S : Finset (Fin J))
    (hS : ∀ i ∈ S, ∀ j ∈ S, α j - α i < ε) : (S.card : ℝ) ≤ 1 + ε / h0 := by
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hSe, Finset.card_empty, Nat.cast_zero]
    positivity
  · set lo := S.min' hSne
    set hi := S.max' hSne
    have hlo : lo ∈ S := min'_mem S hSne
    have hhi : hi ∈ S := max'_mem S hSne
    have hle : lo ≤ hi := min'_le S hi hhi
    have hspread := hS lo hlo hi hhi
    have hgapl := gap_le hgap hle
    have hdiff : (((hi : ℕ) - (lo : ℕ) : ℕ) : ℝ) * h0 < ε := by linarith
    have hcard : S.card ≤ ((hi : ℕ) - (lo : ℕ)) + 1 := by
      have hsub : S.image (fun j : Fin J => (j : ℕ)) ⊆ Icc (lo : ℕ) (hi : ℕ) := by
        intro k hk
        obtain ⟨j, hj, rfl⟩ := mem_image.1 hk
        exact mem_Icc.2 ⟨Fin.le_def.1 (min'_le S j hj), Fin.le_def.1 (le_max' S j hj)⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Icc] at h1
      omega
    have hq : (((hi : ℕ) - (lo : ℕ) : ℕ) : ℝ) < ε / h0 := by rwa [lt_div_iff₀ hh0]
    have : (S.card : ℝ) ≤ (((hi : ℕ) - (lo : ℕ) : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
    linarith

/-- The grouped sum of the proof of Theorem 33 (i): `Σ_{α_j ≤ α⋆−ε} e^{−A x_j²} ≤ 2(1 + ε/h₀)e^{−A}` for `A ≥ log 2`,
`x_j = (α⋆ − α_j)/ε`. -/
lemma sum_exp_le_two (hgap : GapsGe α h0) (hh0 : 0 < h0) (hε : 0 < ε) {A : ℝ} (hA : Real.log 2 ≤ A) :
    ∑ j ∈ univ.filter (fun j => α j ≤ αs - ε), Real.exp (-(A * ((αs - α j) / ε) ^ 2)) ≤
      2 * (1 + ε / h0) * Real.exp (-A) := by
  classical
  set T := univ.filter (fun j : Fin J => α j ≤ αs - ε) with hT
  set x : Fin J → ℝ := fun j => (αs - α j) / ε with hx
  have hx1 : ∀ j ∈ T, 1 ≤ x j := by
    intro j hj
    have := (mem_filter.1 hj).2
    rw [hx]; simp only
    rw [le_div_iff₀ hε]; linarith
  set kf : Fin J → ℕ := fun j => ⌊x j⌋₊ - 1 with hkf
  set q := Real.exp (-(3 * A)) with hq
  have hA0 : 0 < A := lt_of_lt_of_le (Real.log_pos (by norm_num)) hA
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq12 : q ≤ 1 / 2 := by
    rw [hq]
    have h3 : Real.log 2 ≤ 3 * A := by linarith
    calc Real.exp (-(3 * A)) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
  -- each term
  have hterm : ∀ j ∈ T, Real.exp (-(A * x j ^ 2)) ≤ Real.exp (-A) * q ^ kf j := by
    intro j hj
    have h1 := hx1 j hj
    have hfl : 1 ≤ ⌊x j⌋₊ := Nat.one_le_iff_ne_zero.2 (by
      intro h0'; rw [Nat.floor_eq_zero] at h0'; linarith)
    have hk : (kf j : ℝ) + 1 ≤ x j := by
      have : (kf j : ℝ) + 1 = (⌊x j⌋₊ : ℝ) := by rw [hkf]; simp only; push_cast [Nat.cast_sub hfl]; ring
      rw [this]; exact Nat.floor_le (by linarith)
    have hk0 : (0 : ℝ) ≤ kf j := Nat.cast_nonneg _
    have hsq : 1 + 3 * (kf j : ℝ) ≤ x j ^ 2 := by
      have : ((kf j : ℝ) + 1) ^ 2 ≤ x j ^ 2 := pow_le_pow_left₀ (by positivity) hk 2
      -- (k+1)^2 ≥ 1 + 3k for natural k
      have hnat : (1 : ℝ) + 3 * (kf j : ℝ) ≤ ((kf j : ℝ) + 1) ^ 2 := by
        rcases Nat.eq_zero_or_pos (kf j) with h0' | hpos
        · rw [h0']; norm_num
        · have : (1 : ℝ) ≤ kf j := by exact_mod_cast hpos
          nlinarith
      linarith
    rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  -- the fibers
  have hfib : ∀ k : ℕ, ((T.filter fun j => kf j = k).card : ℝ) ≤ 1 + ε / h0 := by
    intro k
    refine card_le_of_spread hgap hh0 hε.le _ ?_
    intro i hi j hj
    obtain ⟨hiT, hik⟩ := mem_filter.1 hi
    obtain ⟨hjT, hjk⟩ := mem_filter.1 hj
    have hfi : 1 ≤ ⌊x i⌋₊ := Nat.one_le_iff_ne_zero.2 (by
      intro h0'; rw [Nat.floor_eq_zero] at h0'; linarith [hx1 i hiT])
    have hfj : 1 ≤ ⌊x j⌋₊ := Nat.one_le_iff_ne_zero.2 (by
      intro h0'; rw [Nat.floor_eq_zero] at h0'; linarith [hx1 j hjT])
    have hfeq : ⌊x i⌋₊ = ⌊x j⌋₊ := by
      have := hik.trans hjk.symm; rw [hkf] at this; simp only at this; omega
    have hxi : x i < ⌊x i⌋₊ + 1 := Nat.lt_floor_add_one _
    have hxj : (⌊x j⌋₊ : ℝ) ≤ x j := Nat.floor_le (by linarith [hx1 j hjT])
    rw [hfeq] at hxi
    -- x_i − x_j = (α_j − α_i)/ε < 1
    have : (α j - α i) / ε < 1 := by
      have e : (α j - α i) / ε = x i - x j := by rw [hx]; simp only; field_simp; ring
      rw [e]; linarith
    rwa [div_lt_one hε] at this
  -- group by `k`
  calc ∑ j ∈ T, Real.exp (-(A * x j ^ 2)) ≤ ∑ j ∈ T, Real.exp (-A) * q ^ kf j := sum_le_sum hterm
    _ = Real.exp (-A) * ∑ j ∈ T, q ^ kf j := by rw [mul_sum]
    _ = Real.exp (-A) * ∑ k ∈ T.image kf, ((T.filter fun j => kf j = k).card : ℝ) * q ^ k := by
        rw [sum_comp (fun k => q ^ k) kf]; simp only [nsmul_eq_mul]
    _ ≤ Real.exp (-A) * ∑ k ∈ T.image kf, (1 + ε / h0) * q ^ k := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hfib k)
          (pow_nonneg hq0 k)) (Real.exp_pos _).le
    _ = Real.exp (-A) * ((1 + ε / h0) * ∑ k ∈ T.image kf, q ^ k) := by rw [← mul_sum]
    _ ≤ Real.exp (-A) * ((1 + ε / h0) * 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (Real.exp_pos _).le
        calc ∑ k ∈ T.image kf, q ^ k ≤ 1 / (1 - q) := sum_pow_le _ hq0 (by linarith)
          _ ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    _ = 2 * (1 + ε / h0) * Real.exp (-A) := by ring

/-- `Σ_{α_j ≤ α⋆−ε} e^{−A x_j²} ≤ J_ε e^{−A}` for `A ≥ log 2` (the end of the proof of Theorem 33 (i)). -/
lemma sum_exp_le_Jeps (hgap : GapsGe α h0) (hh0 : 0 < h0) (hε : 0 < ε) {A : ℝ} (hA : Real.log 2 ≤ A) :
    ∑ j ∈ univ.filter (fun j => α j ≤ αs - ε), Real.exp (-(A * ((αs - α j) / ε) ^ 2)) ≤
      Jeps J ε h0 * Real.exp (-A) := by
  classical
  have hA0 : 0 ≤ A := le_trans (Real.log_nonneg (by norm_num)) hA
  have hJ : ∑ j ∈ univ.filter (fun j => α j ≤ αs - ε), Real.exp (-(A * ((αs - α j) / ε) ^ 2)) ≤
      (J : ℝ) * Real.exp (-A) := by
    calc ∑ j ∈ univ.filter (fun j => α j ≤ αs - ε), Real.exp (-(A * ((αs - α j) / ε) ^ 2)) ≤
          ∑ _j ∈ univ.filter (fun j => α j ≤ αs - ε), Real.exp (-A) := by
          refine sum_le_sum fun j hj => Real.exp_le_exp.2 ?_
          have h1 : 1 ≤ (αs - α j) / ε := by
            rw [le_div_iff₀ hε]; linarith [(mem_filter.1 hj).2]
          have h2 : 1 ≤ ((αs - α j) / ε) ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left h2 hA0]
      _ = ((univ.filter (fun j => α j ≤ αs - ε)).card : ℝ) * Real.exp (-A) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (J : ℝ) * Real.exp (-A) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact_mod_cast (card_filter_le _ _).trans (by simp)
  have h2 := sum_exp_le_two (αs := αs) hgap hh0 hε hA
  unfold Jeps
  rw [min_mul_of_nonneg _ _ (Real.exp_pos _).le]
  exact le_min hJ h2

end Sum

/-! ### `D_α ≤ Δ_φ` -/

section Dphi

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma norm_mean_sub_le (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ Dφ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) :
    ‖(∫ x, φ x ∂P) - ∫ y, φ y ∂Q‖ ≤ Dφ := by
  have hiP : Integrable φ P := Integrable.of_bound hφ.aestronglyMeasurable κ (ae_of_all _ hκ)
  have hiQ : Integrable φ Q := Integrable.of_bound hφ.aestronglyMeasurable κ (ae_of_all _ hκ)
  have h1 : (∫ x, φ x ∂P) - ∫ y, φ y ∂Q = ∫ x, (φ x - ∫ y, φ y ∂Q) ∂P := by
    rw [integral_sub hiP (integrable_const _), integral_const, probReal_univ, one_smul]
  have h2 : ∀ x, ‖φ x - ∫ y, φ y ∂Q‖ ≤ Dφ := by
    intro x
    have e : φ x - ∫ y, φ y ∂Q = ∫ y, (φ x - φ y) ∂Q := by
      rw [integral_sub (integrable_const _) hiQ, integral_const, probReal_univ, one_smul]
    rw [e]
    have := norm_integral_le_of_norm_le_const (μ := Q) (f := fun y => φ x - φ y) (C := Dφ)
      (ae_of_all _ fun y => hDφ x y)
    simpa [probReal_univ] using this
  rw [h1]
  have := norm_integral_le_of_norm_le_const (μ := P) (f := fun x => φ x - ∫ y, φ y ∂Q) (C := Dφ) (ae_of_all _ h2)
  simpa [probReal_univ] using this

lemma dpop_le_dphi (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ Dφ α : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Dpop φ P Q α ≤ Dφ := by
  refine (StatFormal.Wave30tz.Lower.setDist_le_norm' (StatFormal.Wave30tl.one_mem_region P φ hα0 hα1)
    (StatFormal.Wave30tl.one_mem_region Q φ hα0 hα1)).trans ?_
  simp only [one_smul]
  exact norm_mean_sub_le P Q hφ hκ hDφ

end Dphi

end Basic

end StatFormal.Wave31tl
