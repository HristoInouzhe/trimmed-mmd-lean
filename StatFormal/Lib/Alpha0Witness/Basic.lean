import StatFormal.Lib.PaperRun.QPMeas

/-!
# The witness fitted at `α = 0`: the capped simplex, uniform weights, normalization (library)

Library component (untrusted).

* `eq_unif_of_le_of_sum`, `isCapped_zero_iff`, `isQPMin_zero_iff`: at `α = 0` the capped simplex of `eq:qp` is the single point
  `(1/n, …, 1/n)` (`n ≥ 1`), so the exact minimizers of `eq:qp` are exactly the uniform pair;
* `wsum_unif`, `qpVal_unif`, `witness_unif`: at the uniform pair `D̂ = ‖n⁻¹Σφ(x_i) − m⁻¹Σφ(y_j)‖` and the witness is the normalized
  difference of the empirical mean embeddings;
* `integral_empirical`: the Bochner integral of a strongly measurable `φ` against the empirical measure is the sample mean;
* `norm_normalize_sub_le`: `‖‖d‖⁻¹d − ‖c‖⁻¹c‖ ≤ 2‖d − c‖/‖c‖` for `c ≠ 0` (also when `d = 0`);
* `abs_inner_sub_le`: `|⟪u, h⟫ − ⟪u₀, h⟫| ≤ ‖u − u₀‖ ‖h‖`;
* `exists_pos_le_gaps`: a finite set on which `f` is injective has a positive lower bound `g₀` on its gaps.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Alpha0Witness

open StatFormal.Wave30tz

/-! ### The capped simplex at `α = 0` -/

/-- Reals `w_i ≤ 1/n` (`n ≥ 1`) summing to `1` are all equal to `1/n`: the slacks `1/n − w_i` are nonnegative and sum to `0`. -/
theorem eq_unif_of_le_of_sum {n : ℕ} (hn : 1 ≤ n) {w : Fin n → ℝ} (hle : ∀ i, w i ≤ 1 / n) (hs : ∑ i, w i = 1) :
    w = fun _ => 1 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hsum : ∑ i, (1 / (n : ℝ) - w i) = 0 := by
    rw [Finset.sum_sub_distrib, hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div_cancel hn', sub_self]
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.2 (hle j))).1 hsum i (Finset.mem_univ _)
  linarith

/-- At `α = 0` the capped simplex `Δ_0(n)` (`n ≥ 1`) is the single point `(1/n, …, 1/n)`. -/
theorem isCapped_zero_iff {n : ℕ} (hn : 1 ≤ n) (w : Fin n → ℝ) : IsCapped 0 w ↔ w = fun _ => 1 / (n : ℝ) := by
  constructor
  · rintro ⟨hb, hs⟩
    refine eq_unif_of_le_of_sum hn (fun i => ?_) hs
    have h := (hb i).2
    simpa using h
  · rintro rfl
    exact StatFormal.PaperRun.capped_unif le_rfl one_pos hn

/-- The capped simplex at `α = 0` as a set. -/
theorem setOf_isCapped_zero {n : ℕ} (hn : 1 ≤ n) : {w : Fin n → ℝ | IsCapped 0 w} = {fun _ => 1 / (n : ℝ)} :=
  Set.ext fun w => isCapped_zero_iff hn w

/-- At `α = 0` the exact minimizers of `eq:qp` (`n, m ≥ 1`) are exactly the uniform pair. -/
theorem isQPMin_zero_iff {𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) :
    IsQPMin φ 0 x y w v ↔ w = (fun _ => 1 / (n : ℝ)) ∧ v = fun _ => 1 / (m : ℝ) := by
  constructor
  · rintro ⟨hw, hv, -⟩
    exact ⟨(isCapped_zero_iff hn w).1 hw, (isCapped_zero_iff hm v).1 hv⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨(isCapped_zero_iff hn _).2 rfl, (isCapped_zero_iff hm _).2 rfl, fun w' v' hw' hv' => ?_⟩
    rw [(isCapped_zero_iff hn w').1 hw', (isCapped_zero_iff hm v').1 hv']

/-! ### The uniform pair -/

section Unif

variable {𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `Σ_i n⁻¹ φ(x_i) = n⁻¹ Σ_i φ(x_i)`. -/
theorem wsum_unif (φ : 𝒳 → H) {n : ℕ} (x : Fin n → 𝒳) :
    wsum φ x (fun _ => 1 / (n : ℝ)) = (n : ℝ)⁻¹ • ∑ i, φ (x i) := by
  unfold wsum
  rw [Finset.smul_sum]
  simp only [one_div]

/-- `D̂` at the uniform pair. -/
theorem qpVal_unif (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    qpVal φ x y (fun _ => 1 / (n : ℝ)) (fun _ => 1 / (m : ℝ)) =
      ‖(n : ℝ)⁻¹ • ∑ i, φ (x i) - (m : ℝ)⁻¹ • ∑ j, φ (y j)‖ := by
  unfold qpVal
  rw [wsum_unif, wsum_unif]

/-- The witness at the uniform pair: the normalized difference of the empirical mean embeddings (`0` when it vanishes). -/
theorem witness_unif (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    witness φ x y (fun _ => 1 / (n : ℝ)) (fun _ => 1 / (m : ℝ)) =
      ‖(n : ℝ)⁻¹ • ∑ i, φ (x i) - (m : ℝ)⁻¹ • ∑ j, φ (y j)‖⁻¹ • ((n : ℝ)⁻¹ • ∑ i, φ (x i) - (m : ℝ)⁻¹ • ∑ j, φ (y j)) := by
  unfold witness
  rw [qpVal_unif, wsum_unif, wsum_unif]

/-- The Bochner integral of a strongly measurable map against the empirical measure `n⁻¹ Σ δ_{x_i}` is the sample mean. -/
theorem integral_empirical [MeasurableSpace 𝒳] [CompleteSpace H] {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {n : ℕ}
    (x : Fin n → 𝒳) :
    ∫ z, φ z ∂(StatFormal.TrimmedMMD.Concentration.empirical x) = (n : ℝ)⁻¹ • ∑ i, φ (x i) := by
  unfold StatFormal.TrimmedMMD.Concentration.empirical
  rw [integral_finsetSum_measure fun i _ =>
    (integrable_dirac' hφ enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac' _ _ hφ, ENNReal.toReal_ofReal (by positivity), one_div]

end Unif

/-! ### Normalization and evaluation -/

section Norm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Normalization is Lipschitz away from `0`**: for `c ≠ 0` and any `d`, `‖‖d‖⁻¹d − ‖c‖⁻¹c‖ ≤ 2‖d − c‖/‖c‖` (with `‖0‖⁻¹ 0 = 0`). -/
theorem norm_normalize_sub_le {c : H} (hc : c ≠ 0) (d : H) :
    ‖‖d‖⁻¹ • d - ‖c‖⁻¹ • c‖ ≤ 2 * ‖d - c‖ / ‖c‖ := by
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  have h1 : ‖‖d‖⁻¹ • d - ‖c‖⁻¹ • d‖ ≤ ‖d - c‖ / ‖c‖ := by
    by_cases hd : d = 0
    · subst hd
      simp only [smul_zero, sub_zero, norm_zero, zero_sub, norm_neg]
      positivity
    · have hd0 : 0 < ‖d‖ := norm_pos_iff.2 hd
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      have e : (‖d‖⁻¹ - ‖c‖⁻¹) * ‖d‖ = (‖c‖ - ‖d‖) / ‖c‖ := by
        field_simp
      calc |‖d‖⁻¹ - ‖c‖⁻¹| * ‖d‖ = |(‖d‖⁻¹ - ‖c‖⁻¹) * ‖d‖| := by rw [abs_mul, abs_of_pos hd0]
        _ = |‖c‖ - ‖d‖| / ‖c‖ := by rw [e, abs_div, abs_of_pos hc0]
        _ ≤ ‖d - c‖ / ‖c‖ := by
          gcongr
          rw [abs_sub_comm]
          exact abs_norm_sub_norm_le d c
  have h2 : ‖‖c‖⁻¹ • d - ‖c‖⁻¹ • c‖ = ‖d - c‖ / ‖c‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc0, inv_mul_eq_div]
  calc ‖‖d‖⁻¹ • d - ‖c‖⁻¹ • c‖ = ‖(‖d‖⁻¹ • d - ‖c‖⁻¹ • d) + (‖c‖⁻¹ • d - ‖c‖⁻¹ • c)‖ := by
        congr 1; abel
    _ ≤ ‖‖d‖⁻¹ • d - ‖c‖⁻¹ • d‖ + ‖‖c‖⁻¹ • d - ‖c‖⁻¹ • c‖ := norm_add_le _ _
    _ ≤ ‖d - c‖ / ‖c‖ + ‖d - c‖ / ‖c‖ := by rw [h2]; exact add_le_add h1 le_rfl
    _ = 2 * ‖d - c‖ / ‖c‖ := by ring

/-- `|⟪u, h⟫ − ⟪u₀, h⟫| ≤ ‖u − u₀‖ ‖h‖` (Cauchy–Schwarz). -/
theorem abs_inner_sub_le (u u₀ h : H) : |⟪u, h⟫_ℝ - ⟪u₀, h⟫_ℝ| ≤ ‖u - u₀‖ * ‖h‖ := by
  rw [← inner_sub_left]
  exact abs_real_inner_le_norm _ _

end Norm

/-! ### Gaps of a function on a finite set -/

/-- A finite set on which `f` is injective has a positive lower bound on the gaps `|f a − f b|`, `a ≠ b`. -/
theorem exists_pos_le_gaps {α : Type*} (S : Finset α) (f : α → ℝ) (hinj : Set.InjOn f ↑S) :
    ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → g₀ ≤ |f a - f b| := by
  classical
  set D : Finset ℝ := ((S ×ˢ S).filter fun p => p.1 ≠ p.2).image fun p => |f p.1 - f p.2| with hD
  by_cases hne : D.Nonempty
  · refine ⟨D.min' hne, ?_, fun a ha b hb hab => D.min'_le _ ?_⟩
    · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 (D.min'_mem hne)
      rw [← hpe]
      obtain ⟨hpS, hp12⟩ := Finset.mem_filter.1 hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hpS
      refine abs_pos.2 (sub_ne_zero.2 fun h => hp12 (hinj h1 h2 h))
    · exact Finset.mem_image.2 ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, hab⟩, rfl⟩
  · refine ⟨1, one_pos, fun a ha b hb hab => absurd ?_ hne⟩
    exact ⟨_, Finset.mem_image.2 ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, hab⟩, rfl⟩⟩

end StatFormal.Alpha0Witness
