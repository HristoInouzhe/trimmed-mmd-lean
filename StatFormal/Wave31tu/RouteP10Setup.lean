import StatFormal.Wave31tu.Statements
import StatFormal.Wave31tq.Proofs
import StatFormal.Wave31tq.RouteM26
import StatFormal.Wave31tp.Proofs
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs
import StatFormal.Lib.EmpiricalQuantile.Basic
import StatFormal.Lib.FrankWolfe.Capped

set_option linter.style.longLine false

/-!
# Wave31tu, chunk P: the setting of Lemma S4.21 (`lem:lapclip`, S4 :1088-1119)

Facts about the Laplace feature map and the empirical laws of the fitting batches used by Y10 `lap_clip`:

* `laplace_feature_facts`: a feature map with the Gram function `e^{−|x−y|/σ}` is strongly measurable, has unit norms and is
  characteristic (31tp L16 `mmd_fourier`, 31tq Q7 `kernel_instances` (the spectrum `2σ/(1+σ²ξ²)`), Q5 `sobolev_angular`);
* `tvDist_empirical_eq_one`: if no `x_i` equals a `y_j`, `TV(P̃, Q̃) = 1`;
* `dpop_empirical_pos`: then `D_α(P̃, Q̃) > 0` for every `α ∈ [0,1)` (`eq:zeroeq`, "Since `TV(P̃,Q̃) = 1 > α`, `D̄̂ > 0`");
* `wsum_mem_region`: capped combinations lie in the empirical regions (`FrankWolfe.region_empirical_eq_image`);
* `iSup_iInf_of_attained`: a function between `u` and `t` attaining both has `sup = t`, `inf = u`;
* `norm_le_of_rep`, `inner_wsum_eq_zero`: an element of the span of the features has the least norm among the
  representers of its function.
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteP

open StatFormal.Distances StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.Concentration
  StatFormal.Wave30tz

/-- The Laplace feature map is strongly measurable, has unit norms and is characteristic. -/
theorem laplace_feature_facts {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {σ : ℝ}
    {φ : ℝ → H} (hσ : 0 < σ) (hφ : IsLaplaceFeature σ φ) :
    StronglyMeasurable φ ∧ (∀ x, ‖φ x‖ = 1) ∧ StatFormal.TrimmedMMD.ZeroSet.Characteristic φ := by
  obtain ⟨hk, hki, -, -, hlow, -⟩ := StatFormal.Wave31tq.kernel_instances.1 σ hσ
  have hg : ∀ x y, ⟪φ x, φ y⟫_ℝ = (fun z : ℝ => Real.exp (-|z| / σ)) (x - y) := fun x y => hφ x y
  obtain ⟨-, hsm, hnorm, -⟩ := StatFormal.Wave31tp.mmd_fourier ℝ H φ _ hk hki hg
  have hc : 0 < 2 * σ * min 1 (σ ^ 2)⁻¹ := mul_pos (by linarith) (lt_min one_pos (inv_pos.mpr (by positivity)))
  have hchar := (StatFormal.Wave31tq.RouteM.sobolev_char StatFormal.Wave31tq.sobolev_angular hk hki hg hc
    (s := 1) (fun ξ => (hlow ξ).1)).1
  refine ⟨hsm, fun x => ?_, hchar⟩
  rw [hnorm x]; simp

/-- If no `x_i` equals a `y_j`, the empirical laws are at total variation `1`. -/
theorem tvDist_empirical_eq_one {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hxy : ∀ i j, x i ≠ y j) : tvDist (empirical x) (empirical y) = 1 := by
  classical
  have := isProbabilityMeasure_empirical (by omega : n ≠ 0) x
  have := isProbabilityMeasure_empirical (by omega : m ≠ 0) y
  have hA : MeasurableSet (range x) := (finite_range x).measurableSet
  have hP : (empirical x).real (range x) = 1 := by
    rw [StatFormal.EmpiricalQuantile.empirical_real_eq (by omega) x hA]
    have : (Finset.univ.filter fun i => x i ∈ range x) = Finset.univ := by
      ext i; simp
    rw [this, Finset.card_univ, Fintype.card_fin, div_self (by exact_mod_cast (show n ≠ 0 by omega))]
  have hQ : (empirical y).real (range x) = 0 := by
    rw [StatFormal.EmpiricalQuantile.empirical_real_eq (by omega) y hA]
    have : (Finset.univ.filter fun j => y j ∈ range x) = ∅ := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_range, Finset.notMem_empty, iff_false]
      rintro ⟨i, hi⟩; exact hxy i j hi
    rw [this]; simp
  apply le_antisymm tvDist_le_one
  have := abs_measureReal_sub_le_tvDist (μ := empirical x) (ν := empirical y) hA
  rw [hP, hQ] at this; simpa using this

/-- `D_α(P̃, Q̃) > 0` for `α ∈ [0,1)` when no `x_i` equals a `y_j` (Laplace kernel). -/
theorem dpop_empirical_pos {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] {σ : ℝ} {φ : ℝ → H} (hσ : 0 < σ) (hφ : IsLaplaceFeature σ φ) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → ℝ) (y : Fin m → ℝ) (hxy : ∀ i j, x i ≠ y j) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) : 0 < Dpop φ (empirical x) (empirical y) α := by
  have := isProbabilityMeasure_empirical (by omega : n ≠ 0) x
  have := isProbabilityMeasure_empirical (by omega : m ≠ 0) y
  obtain ⟨hsm, hnorm, hchar⟩ := laplace_feature_facts hσ hφ
  have hz := StatFormal.TrimmedMMD.ZeroSet.zeroeq ℝ H (empirical x) (empirical y) φ 1 α hsm (fun z => (hnorm z).le)
    hchar hα0 hα1
  have h0 : 0 ≤ Dpop φ (empirical x) (empirical y) α :=
    Real.sInf_nonneg fun _ ⟨_, _, _, _, hr⟩ => hr ▸ norm_nonneg _
  rcases h0.lt_or_eq with h | h
  · exact h
  · have := hz.1 h.symm
    rw [tvDist_empirical_eq_one hn hm x y hxy] at this
    linarith

/-- Capped combinations of the features lie in the empirical region. -/
theorem wsum_mem_region {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {α : ℝ} {n : ℕ} (x : Fin n → 𝒳) {w : Fin n → ℝ} (hw : IsCapped α w) :
    wsum φ x w ∈ region φ α (empirical x) := by
  rw [StatFormal.FrankWolfe.region_empirical_eq_image hφ x hw]
  exact ⟨w, hw, rfl⟩

/-- A function between `u` and `t` attaining both has `sup = t` and `inf = u`. -/
theorem iSup_iInf_of_attained {𝒳 : Type*} {G : 𝒳 → ℝ} {t u : ℝ} (hb : ∀ z, u ≤ G z ∧ G z ≤ t) {z₁ z₂ : 𝒳}
    (h1 : G z₁ = t) (h2 : G z₂ = u) : (⨆ z, G z) = t ∧ (⨅ z, G z) = u := by
  have : Nonempty 𝒳 := ⟨z₁⟩
  refine ⟨le_antisymm (ciSup_le fun z => (hb z).2) ?_, le_antisymm ?_ (le_ciInf fun z => (hb z).1)⟩
  · rw [← h1]; exact le_ciSup ⟨t, by rintro _ ⟨z, rfl⟩; exact (hb z).2⟩ z₁
  · rw [← h2]; exact ciInf_le ⟨u, by rintro _ ⟨z, rfl⟩; exact (hb z).1⟩ z₂

/-- `⟪d, Σ w_i φ(x_i)⟫ = 0` when `d` is orthogonal to every feature. -/
theorem inner_wsum_eq_zero {𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {φ : 𝒳 → H} {d : H}
    (hd : ∀ z, ⟪d, φ z⟫_ℝ = 0) {n : ℕ} (x : Fin n → 𝒳) (w : Fin n → ℝ) : ⟪d, wsum φ x w⟫_ℝ = 0 := by
  unfold wsum
  rw [inner_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [inner_smul_right, hd, mul_zero]

/-- **Least representer norm.** If `e` is orthogonal to every `d` orthogonal to all features, every `g′` representing the
same function as `e` has `‖e‖ ≤ ‖g′‖`. -/
theorem norm_le_of_rep {𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {φ : 𝒳 → H} {e g' : H}
    (he : ∀ d : H, (∀ z, ⟪d, φ z⟫_ℝ = 0) → ⟪e, d⟫_ℝ = 0) (hrep : ∀ z, ⟪g', φ z⟫_ℝ = ⟪e, φ z⟫_ℝ) : ‖e‖ ≤ ‖g'‖ := by
  have hd : ∀ z, ⟪g' - e, φ z⟫_ℝ = 0 := fun z => by rw [inner_sub_left, hrep, sub_self]
  have h0 := he (g' - e) hd
  have hsq : ‖g'‖ ^ 2 = ‖e‖ ^ 2 + 2 * ⟪e, g' - e⟫_ℝ + ‖g' - e‖ ^ 2 := by
    rw [← norm_add_sq_real, add_sub_cancel]
  rw [h0] at hsq
  nlinarith [norm_nonneg e, norm_nonneg g', sq_nonneg ‖g' - e‖]

/-- The scaled witness `c • f̂` is orthogonal to everything orthogonal to the features. -/
theorem witness_orth {𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) {n m : ℕ}
    (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) (c : ℝ) :
    ∀ d : H, (∀ z, ⟪d, φ z⟫_ℝ = 0) → ⟪c • witness φ x y w v, d⟫_ℝ = 0 := by
  intro d hd
  unfold witness
  rw [real_inner_comm, inner_smul_right, inner_smul_right, inner_sub_right, inner_wsum_eq_zero hd,
    inner_wsum_eq_zero hd]
  ring

end StatFormal.Wave31tu.RouteP
