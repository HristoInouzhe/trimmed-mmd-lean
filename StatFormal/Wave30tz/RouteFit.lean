import StatFormal.Wave30tz.RouteOrder
import StatFormal.Wave30tz.RouteElem
import StatFormal.Wave30tr.RouteDet

/-!
# Wave 30tz route: Lemma 4 (`eq:fittedramp`, the fitted ramp) — untrusted

Proves `Claims.fitted_ramp` (`fitted_ramp_route`), following NOTE §4, Lemma 4:
1. `Fit.dpop_sub_le_qpVal`: `D_α − βZ⁻ ≤ D̂` for every capped pair, by the projection argument
   of `Wave30tr.setDist_region_le` with the QP point `(Σ w_i φ(x_i), Σ v_j φ(y_j))` as target:
   for capped `w`, `⟨−f, Σ w_i φ(x_i)⟩ ≤ q + (β/n) Σ_i (⟨−f, φ(x_i)⟩ − q)₊`, and the bracket
   is a term of the supremum `Z⁻`;
2. `Fit.qp_foc_x`, `Fit.qp_foc_y`: the first-order conditions of `eq:qp` along segments of
   capped weights;
3. `Fit.exists_critT_eq`, `Fit.exists_critU_eq`: finite CVaR strong duality, from
   `exists_cvar_witness` for the empirical measure (capped weights `g(x_i)/n` attaining `T(t)`,
   resp. `U(u)`), so `max T ≥ A`, `min U ≤ B` with `A − B = D̂`;
4. own terms: `h_i − βκ²/(nD̂) ≤ h̃_i ≤ h_i`, `h'_j ≤ h̃'_j ≤ h'_j + βκ²/(mD̂)`, then
   order-statistic monotonicity and shift (`RouteOrder`), Lemma 3 (`critT_bracket`,
   `critU_bracket`) at the nearest bracket point and the Lipschitz bounds (`critT_lipschitz`,
   `critU_lipschitz`, constant `≤ β`);
5. Lemma 2 (`crit_uniform_route`) and `x ↦ x − c/x` increasing: `θ ≥ Θ`;
6. width `t − u ≤ D_φ` from the order statistics of the in-sample values; `θ ≤ t − u` (hinges
   `≥ 0`); the excess through the certified `Wave30tq.lem2_1`, `Wave30tq.lem2_2`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30tz

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30ty StatFormal.Wave30tp
open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.ZeroSet

namespace Fit

section QPAlg

variable {𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma wsum_mix (φ : 𝒳 → H) {n : ℕ} (x : Fin n → 𝒳) (w w' : Fin n → ℝ) (s : ℝ) :
    wsum φ x (fun i => (1 - s) * w i + s * w' i) = (1 - s) • wsum φ x w + s • wsum φ x w' := by
  unfold wsum
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_smul, mul_smul, mul_smul]

lemma inner_wsum (φ : 𝒳 → H) {n : ℕ} (x : Fin n → 𝒳) (w : Fin n → ℝ) (f : H) :
    ⟪f, wsum φ x w⟫_ℝ = ∑ i, w i * ⟪f, φ (x i)⟫_ℝ := by
  unfold wsum
  rw [inner_sum]
  simp_rw [real_inner_smul_right]

lemma capped_mix {α : ℝ} {n : ℕ} {w w' : Fin n → ℝ} (hw : IsCapped α w) (hw' : IsCapped α w') {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : IsCapped α (fun i => (1 - s) * w i + s * w' i) := by
  obtain ⟨hb, hsum⟩ := hw
  obtain ⟨hb', hsum'⟩ := hw'
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · have := (hb i).1; have := (hb' i).1
    have : 0 ≤ 1 - s := by linarith
    positivity
  · have h1 := (hb i).2; have h2 := (hb' i).2
    have : 0 ≤ 1 - s := by linarith
    have e1 := mul_le_mul_of_nonneg_left h1 this
    have e2 := mul_le_mul_of_nonneg_left h2 hs0
    linarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum, hsum']; ring

/-- First-order condition at a minimum of `s ↦ ‖e + s • d‖` on `[0,1]` attained at `s = 0`. -/
lemma inner_nonneg_of_min {e d : H} (h : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ‖e‖ ≤ ‖e + s • d‖) :
    0 ≤ ⟪e, d⟫_ℝ := by
  by_contra hneg
  rw [not_le] at hneg
  set c := ⟪e, d⟫_ℝ with hc
  have hd0 : d ≠ 0 := by rintro rfl; simp [c] at hneg
  have hd : 0 < ‖d‖ ^ 2 := by have := norm_pos_iff.2 hd0; positivity
  set s := min 1 (-c / ‖d‖ ^ 2) with hs
  have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) hd)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsN : s * ‖d‖ ^ 2 ≤ -c := by
    have : s ≤ -c / ‖d‖ ^ 2 := min_le_right _ _
    rwa [le_div_iff₀ hd] at this
  have h1 := h s hs0.le hs1
  have h2 : ‖e‖ ^ 2 ≤ ‖e + s • d‖ ^ 2 := by gcongr
  rw [norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs] at h2
  have h3 : 0 ≤ s * (2 * c + s * ‖d‖ ^ 2) := by nlinarith
  have h4 : 2 * c + s * ‖d‖ ^ 2 < 0 := by linarith
  nlinarith

lemma qp_foc_x {φ : 𝒳 → H} {α : ℝ} {n m : ℕ} {x : Fin n → 𝒳} {y : Fin m → 𝒳} {w : Fin n → ℝ}
    {v : Fin m → ℝ} (hqp : IsQPMin φ α x y w v) {w' : Fin n → ℝ} (hw' : IsCapped α w') :
    0 ≤ ⟪wsum φ x w - wsum φ y v, wsum φ x w' - wsum φ x w⟫_ℝ := by
  refine inner_nonneg_of_min fun s hs0 hs1 => ?_
  have := hqp.2.2 _ v (capped_mix hqp.1 hw' hs0 hs1) hqp.2.1
  unfold qpVal at this
  rw [wsum_mix] at this
  convert this using 2
  module

lemma qp_foc_y {φ : 𝒳 → H} {α : ℝ} {n m : ℕ} {x : Fin n → 𝒳} {y : Fin m → 𝒳} {w : Fin n → ℝ}
    {v : Fin m → ℝ} (hqp : IsQPMin φ α x y w v) {v' : Fin m → ℝ} (hv' : IsCapped α v') :
    0 ≤ ⟪wsum φ x w - wsum φ y v, wsum φ y v - wsum φ y v'⟫_ℝ := by
  refine inner_nonneg_of_min fun s hs0 hs1 => ?_
  have := hqp.2.2 w _ hqp.1 (capped_mix hqp.2.1 hv' hs0 hs1)
  unfold qpVal at this
  rw [wsum_mix] at this
  convert this using 2
  module

/-- The cap `1/(n(1−α))` is `β/n`. -/
lemma cap_eq (n : ℕ) (α : ℝ) : 1 / (n * (1 - α)) = beta α / n := by
  rw [beta_eq, div_div, mul_comm]

/-- For capped weights, `Σ w_i Y_i ≤ q + β · n⁻¹ Σ (Y_i − q)₊`. -/
lemma capped_sum_le {α : ℝ} {n : ℕ} {w : Fin n → ℝ} (hw : IsCapped α w) (Y : Fin n → ℝ) (q : ℝ) :
    ∑ i, w i * Y i ≤ q + beta α * ((n : ℝ)⁻¹ * ∑ i, max (Y i - q) 0) := by
  obtain ⟨hb, hsum⟩ := hw
  have e1 : ∑ i, w i * Y i = q + ∑ i, w i * (Y i - q) := by
    have : ∑ i, w i * (Y i - q) = ∑ i, w i * Y i - q * ∑ i, w i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; congr 1; funext i; ring
    rw [this, hsum]; ring
  have e2 : ∑ i, w i * (Y i - q) ≤ ∑ i, beta α / n * max (Y i - q) 0 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hc := (hb i).2
    rw [cap_eq] at hc
    calc w i * (Y i - q) ≤ w i * max (Y i - q) 0 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (hb i).1
      _ ≤ beta α / n * max (Y i - q) 0 := mul_le_mul_of_nonneg_right hc (le_max_right _ _)
  have e3 : ∑ i, beta α / n * max (Y i - q) 0 = beta α * ((n : ℝ)⁻¹ * ∑ i, max (Y i - q) 0) := by
    rw [← Finset.mul_sum]; ring
  linarith

end QPAlg


section Dual

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- Finite CVaR strong duality for `T`: some capped weights attain `T(t)` at some `t`. -/
lemma exists_critT_eq {n : ℕ} (hn : 1 ≤ n) (x : Fin n → 𝒳) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {F : 𝒳 → ℝ} (hF : Measurable F) {κ : ℝ} (hFb : ∀ z, |F z| ≤ κ) :
    ∃ t : ℝ, ∃ w' : Fin n → ℝ, IsCapped α w' ∧ ∑ i, w' i * F (x i) = critT α (fun i => F (x i)) t := by
  have := isProbabilityMeasure_empirical (by omega : n ≠ 0) x
  have hY : Measurable fun z => -F z := hF.neg
  have hYb : ∀ z, |-F z| ≤ κ := fun z => by rw [abs_neg]; exact hFb z
  obtain ⟨q, -, g, hg, hgb, hg1, hval⟩ := exists_cvar_witness (empirical x) hY hYb (one_le_beta hα0 hα1)
  rw [Elem.integral_empirical_of_measurable x hg] at hg1
  rw [Elem.integral_empirical_of_measurable x (g := fun z => g z * -F z) (hg.mul hY),
    Elem.integral_empirical_of_measurable x (g := fun z => max (-F z - q) 0) (by fun_prop)] at hval
  refine ⟨-q, fun i => (n : ℝ)⁻¹ * g (x i), ⟨fun i => ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact mul_nonneg (by positivity) (hgb _).1
  · rw [cap_eq, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hgb _).2 (by positivity)
  · rw [← Finset.mul_sum, hg1]
  · have e1 : ∑ i, (n : ℝ)⁻¹ * g (x i) * F (x i) = -((n : ℝ)⁻¹ * ∑ i, g (x i) * -F (x i)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [e1, hval]
    unfold critT
    have e2 : ∀ i, max (-F (x i) - q) 0 = max (-q - F (x i)) 0 := fun i => by ring_nf
    simp_rw [e2]
    ring

/-- Finite CVaR strong duality for `U`. -/
lemma exists_critU_eq {m : ℕ} (hm : 1 ≤ m) (y : Fin m → 𝒳) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {F : 𝒳 → ℝ} (hF : Measurable F) {κ : ℝ} (hFb : ∀ z, |F z| ≤ κ) :
    ∃ u : ℝ, ∃ v' : Fin m → ℝ, IsCapped α v' ∧ ∑ j, v' j * F (y j) = critU α (fun j => F (y j)) u := by
  have := isProbabilityMeasure_empirical (by omega : m ≠ 0) y
  obtain ⟨q, -, g, hg, hgb, hg1, hval⟩ := exists_cvar_witness (empirical y) hF hFb (one_le_beta hα0 hα1)
  rw [Elem.integral_empirical_of_measurable y hg] at hg1
  rw [Elem.integral_empirical_of_measurable y (g := fun z => g z * F z) (hg.mul hF),
    Elem.integral_empirical_of_measurable y (g := fun z => max (F z - q) 0) (by fun_prop)] at hval
  refine ⟨q, fun j => (m : ℝ)⁻¹ * g (y j), ⟨fun j => ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact mul_nonneg (by positivity) (hgb _).1
  · rw [cap_eq, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hgb _).2 (by positivity)
  · rw [← Finset.mul_sum, hg1]
  · have e1 : ∑ j, (m : ℝ)⁻¹ * g (y j) * F (y j) = (m : ℝ)⁻¹ * ∑ j, g (y j) * F (y j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [e1, hval]
    unfold critU
    ring

end Dual

section Hinge

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `(P_n − P) g ≤ B` for `0 ≤ g ≤ B`. -/
lemma devEmp_le (P : Measure 𝒳) [IsProbabilityMeasure P] {n : ℕ} (x : Fin n → 𝒳) {g : 𝒳 → ℝ} {B : ℝ}
    (hg0 : ∀ z, 0 ≤ g z) (hgB : ∀ z, g z ≤ B) : devEmp P x g ≤ B := by
  unfold devEmp
  have hB : 0 ≤ B := by
    obtain ⟨z⟩ := nonempty_of_isProbabilityMeasure P
    exact (hg0 z).trans (hgB z)
  have h1 : 0 ≤ ∫ z, g z ∂P := integral_nonneg hg0
  have h2 : (n : ℝ)⁻¹ * ∑ i, g (x i) ≤ B := by
    have : ∑ i, g (x i) ≤ n * B := by
      calc ∑ i, g (x i) ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ => hgB _
        _ = n * B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [hB]
    · have hn : (0 : ℝ) < n := by exact_mod_cast hpos
      rw [inv_mul_le_iff₀ hn]; exact this
  linarith

omit [MeasurableSpace 𝒳] in
lemma abs_inner_le_of_norm {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {f : H} (hf : ‖f‖ ≤ 1) (z : 𝒳) :
    |⟪f, φ z⟫_ℝ| ≤ κ :=
  (abs_real_inner_le_norm f (φ z)).trans
    ((mul_le_mul hf (hκ z) (norm_nonneg _) zero_le_one).trans_eq (one_mul κ))

lemma bddAbove_hingeZm (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    BddAbove (range fun p : hingePar (H := H) 1 κ κ =>
      devEmp P x (hOne hingePos φ p.1.1 p.1.2.1) + devEmp Q y (hTwo hingePos φ p.1.1 p.1.2.2)) := by
  refine ⟨2 * κ + 2 * κ, ?_⟩
  rintro _ ⟨⟨⟨f, a, b⟩, hp⟩, rfl⟩
  obtain ⟨hf, ha, hb⟩ := hp
  have hvb := abs_inner_le_of_norm hκ hf
  have h1 : devEmp P x (hOne hingePos φ f a) ≤ 2 * κ := by
    refine devEmp_le P x (fun z => le_max_right _ _) fun z => ?_
    have := abs_le.1 (hvb z)
    have := abs_le.1 ha
    have hκ0 : 0 ≤ κ := (abs_nonneg _).trans ha
    exact max_le (by linarith) (by linarith)
  have h2 : devEmp Q y (hTwo hingePos φ f b) ≤ 2 * κ := by
    refine devEmp_le Q y (fun z => le_max_right _ _) fun z => ?_
    have := abs_le.1 (hvb z)
    have := abs_le.1 hb
    have hκ0 : 0 ≤ κ := (abs_nonneg _).trans hb
    exact max_le (by linarith) (by linarith)
  exact add_le_add h1 h2

lemma le_hingeZm (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) {f : H} (hf : ‖f‖ ≤ 1)
    {a b : ℝ} (ha : |a| ≤ κ) (hb : |b| ≤ κ) :
    devEmp P x (hOne hingePos φ f a) + devEmp Q y (hTwo hingePos φ f b) ≤
      hingeZm P Q φ hingePos hingePos 1 κ κ (x, y) :=
  le_ciSup (bddAbove_hingeZm P Q hκ x y) ⟨(f, a, b), hf, ha, hb⟩

lemma hingeZm_nonneg (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    0 ≤ hingeZm P Q φ hingePos hingePos 1 κ κ (x, y) := by
  obtain ⟨z⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ z)
  have := le_hingeZm P Q hκ x y (f := 0) (by simp) (a := 0) (b := 0) (by simpa using hκ0) (by simpa using hκ0)
  simpa [devEmp, hOne, hTwo, hingePos] using this

end Hinge


section Step1

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Step 1** (the reverse inequality of `thm:twosided`, Step 1, with a QP point as target):
`D_α − βZ⁻ ≤ D̂` for every capped pair `(w, v)`. -/
theorem dpop_sub_le_qpVal [CompleteSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {φ : 𝒳 → H} {κ α : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) {w : Fin n → ℝ} {v : Fin m → ℝ}
    (hw : IsCapped α w) (hv : IsCapped α v) :
    Dpop φ P Q α - beta α * hingeZm P Q φ hingePos hingePos 1 κ κ (x, y) ≤ qpVal φ x y w v := by
  set β := beta α with hβdef
  have hβ1 : 1 ≤ β := one_le_beta hα0 hα1
  have hβ0 : 0 ≤ β := by linarith
  set Zm := hingeZm P Q φ hingePos hingePos 1 κ κ (x, y) with hZm
  have hZm0 : 0 ≤ Zm := hingeZm_nonneg P Q hκ x y
  have hDh0 : 0 ≤ qpVal φ x y w v := norm_nonneg _
  set A₁ := region φ α P
  set B₁ := region φ α Q
  have hA₁ : A₁.Nonempty := region_nonempty P hα0 hα1
  have hB₁ : B₁.Nonempty := region_nonempty Q hα0 hα1
  -- projection of `0` onto the closure of `A₁ − B₁`
  set K := closure (A₁ - B₁) with hK
  have hKne : K.Nonempty := (hA₁.sub hB₁).closure
  have hKconv : Convex ℝ K := ((region_convex P hφ hκ).sub (region_convex Q hφ hκ)).closure
  have hKcomp : IsComplete K := isClosed_closure.isComplete
  obtain ⟨v₀, hvK, hvproj⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKcomp hKconv 0
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hKconv hvK).1 hvproj
  have hd1 : setDist A₁ B₁ ≤ ‖v₀‖ := by
    have hcl : K ⊆ {c | setDist A₁ B₁ ≤ ‖c‖} := by
      refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact setDist_le_norm ha hb
    exact hcl hvK
  have hDdef : Dpop φ P Q α = setDist A₁ B₁ := rfl
  rw [hDdef]
  by_cases hv0 : v₀ = 0
  · rw [hv0, norm_zero] at hd1
    nlinarith
  have hnpos : 0 < ‖v₀‖ := norm_pos_iff.2 hv0
  set f : H := ‖v₀‖⁻¹ • v₀ with hfdef
  have hf1 : ‖f‖ ≤ 1 := by
    rw [hfdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnpos.ne']
  -- separation: `⟨f, a − b⟩ ≥ ‖v₀‖` on `A₁ × B₁`
  have hsep : ∀ a ∈ A₁, ∀ b ∈ B₁, ‖v₀‖ ≤ ⟪f, a - b⟫_ℝ := by
    intro a ha b hb
    have h := hvi (a - b) (subset_closure ⟨a, ha, b, hb, rfl⟩)
    have h' : ‖v₀‖ ^ 2 ≤ ⟪v₀, a - b⟫_ℝ := by
      have e : ⟪0 - v₀, a - b - v₀⟫_ℝ = ‖v₀‖ ^ 2 - ⟪v₀, a - b⟫_ℝ := by
        rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq]; ring
      linarith
    have e2 : ⟪f, a - b⟫_ℝ = ‖v₀‖⁻¹ * ⟪v₀, a - b⟫_ℝ := by
      rw [hfdef, real_inner_smul_left]
    rw [e2, le_inv_mul_iff₀ hnpos]
    nlinarith
  -- the CVaR witnesses at `−f` for `P` and at `f` for `Q`
  set Y₁ : 𝒳 → ℝ := fun z => ⟪-f, φ z⟫_ℝ with hY₁
  set Y₂ : 𝒳 → ℝ := fun z => ⟪f, φ z⟫_ℝ with hY₂
  have hY₁m : Measurable Y₁ := (stronglyMeasurable_const.inner hφ).measurable
  have hY₂m : Measurable Y₂ := (stronglyMeasurable_const.inner hφ).measurable
  have hf1' : ‖-f‖ ≤ 1 := by rw [norm_neg]; exact hf1
  obtain ⟨q₁, hq₁, g₁, hg₁, hb₁, hi₁, hval₁⟩ :=
    exists_cvar_witness P hY₁m (abs_inner_le_of_norm hκ hf1') hβ1
  obtain ⟨q₂, hq₂, g₂, hg₂, hb₂, hi₂, hval₂⟩ :=
    exists_cvar_witness Q hY₂m (abs_inner_le_of_norm hκ hf1) hβ1
  set a₁ := ∫ z, g₁ z • φ z ∂P
  set b₁ := ∫ z, g₂ z • φ z ∂Q
  have ha₁ : a₁ ∈ A₁ := ⟨g₁, hg₁, hb₁, hi₁, rfl⟩
  have hb₁' : b₁ ∈ B₁ := ⟨g₂, hg₂, hb₂, hi₂, rfl⟩
  have hia₁ : ⟪-f, a₁⟫_ℝ = q₁ + β * ∫ z, max (Y₁ z - q₁) 0 ∂P := by
    rw [inner_integral_smul P hφ hκ hg₁ hb₁ (-f)]; exact hval₁
  have hib₁ : ⟪f, b₁⟫_ℝ = q₂ + β * ∫ z, max (Y₂ z - q₂) 0 ∂Q := by
    rw [inner_integral_smul Q hφ hκ hg₂ hb₂ f]; exact hval₂
  have hlow : setDist A₁ B₁ ≤
      -q₁ - β * ∫ z, max (Y₁ z - q₁) 0 ∂P - (q₂ + β * ∫ z, max (Y₂ z - q₂) 0 ∂Q) := by
    have h := hsep a₁ ha₁ b₁ hb₁'
    rw [inner_sub_right, hib₁] at h
    have : ⟪f, a₁⟫_ℝ = -⟪-f, a₁⟫_ℝ := by rw [inner_neg_left, neg_neg]
    rw [this, hia₁] at h
    linarith
  -- upper bounds at the QP point
  have hu1 : ⟪-f, wsum φ x w⟫_ℝ ≤ q₁ + β * ((n : ℝ)⁻¹ * ∑ i, max (Y₁ (x i) - q₁) 0) := by
    rw [inner_wsum]; exact capped_sum_le hw (fun i => Y₁ (x i)) q₁
  have hu2 : ⟪f, wsum φ y v⟫_ℝ ≤ q₂ + β * ((m : ℝ)⁻¹ * ∑ j, max (Y₂ (y j) - q₂) 0) := by
    rw [inner_wsum]; exact capped_sum_le hv (fun j => Y₂ (y j)) q₂
  have hnorm : ⟪f, wsum φ x w - wsum φ y v⟫_ℝ ≤ qpVal φ x y w v := by
    refine (real_inner_le_norm _ _).trans ?_
    calc ‖f‖ * ‖wsum φ x w - wsum φ y v‖ ≤ 1 * ‖wsum φ x w - wsum φ y v‖ := by gcongr
      _ = qpVal φ x y w v := one_mul _
  rw [inner_sub_right] at hnorm
  have hneg : ⟪f, wsum φ x w⟫_ℝ = -⟪-f, wsum φ x w⟫_ℝ := by rw [inner_neg_left, neg_neg]
  rw [hneg] at hnorm
  -- the bracket is at most `Z⁻`
  have hZ := le_hingeZm P Q hκ x y hf1 (a := -q₁) (b := q₂) (by rwa [abs_neg]) hq₂
  have e1 : hOne hingePos φ f (-q₁) = fun z => max (Y₁ z - q₁) 0 := by
    funext z; simp only [hOne, hingePos, hY₁, inner_neg_left]; ring_nf
  have e2 : hTwo hingePos φ f q₂ = fun z => max (Y₂ z - q₂) 0 := by
    funext z; simp only [hTwo, hingePos, hY₂]
  rw [e1, e2] at hZ
  unfold devEmp at hZ
  have hZ' := mul_le_mul_of_nonneg_left hZ hβ0
  nlinarith

end Step1

end Fit

open Fit

/-- **Lemma 4** (`eq:fittedramp`, the fitted ramp). -/
theorem fitted_ramp_route : Claims.fitted_ramp := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ Dφ α n m x y w v hφ hκ hDφ hα0 hα1 hn hm hqp hZm
  set D := Dpop φ P Q α with hDdef
  set Zp := hingeZ P Q φ hingePos hingePos 1 κ κ (x, y) with hZpdef
  set Zm := hingeZm P Q φ hingePos hingePos 1 κ κ (x, y) with hZmdef
  have hβ1 : 1 ≤ beta α := one_le_beta hα0 hα1
  have hβ0 : 0 ≤ beta α := by linarith
  have h1 : D - beta α * Zm ≤ qpVal φ x y w v := dpop_sub_le_qpVal P Q hφ hκ hα0 hα1 x y hqp.1 hqp.2.1
  set Dh := qpVal φ x y w v with hDhdef
  have hDh : 0 < Dh := by linarith
  refine ⟨h1, hDh, fun t u hC => ?_⟩
  set e := wsum φ x w - wsum φ y v with hedef
  have hne : ‖e‖ = Dh := rfl
  set fh := witness φ x y w v with hfhdef
  have hfh : fh = Dh⁻¹ • e := rfl
  have hfh1 : ‖fh‖ = 1 := by
    rw [hfh, norm_smul, norm_inv, Real.norm_of_nonneg hDh.le, hne, inv_mul_cancel₀ hDh.ne']
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨z0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ z0)
  set F : 𝒳 → ℝ := fun z => ⟪fh, φ z⟫_ℝ with hFdef
  have hFm : Measurable F := (stronglyMeasurable_const.inner hφ).measurable
  have hFb : ∀ z, |F z| ≤ κ := abs_inner_le_of_norm hκ hfh1.le
  set h : Fin n → ℝ := fun i => F (x i) with hhdef
  set h' : Fin m → ℝ := fun j => F (y j) with hh'def
  -- the QP first-order conditions
  have hinner : ∀ c : H, ⟪fh, c⟫_ℝ = Dh⁻¹ * ⟪e, c⟫_ℝ := fun c => by rw [hfh, real_inner_smul_left]
  have hAB : ∑ i, w i * h i - ∑ j, v j * h' j = Dh := by
    have e1 : ∑ i, w i * h i = ⟪fh, wsum φ x w⟫_ℝ := (inner_wsum φ x w fh).symm
    have e2 : ∑ j, v j * h' j = ⟪fh, wsum φ y v⟫_ℝ := (inner_wsum φ y v fh).symm
    rw [e1, e2, ← inner_sub_right, hinner, real_inner_self_eq_norm_sq, hne]
    field_simp
  have hAmin : ∀ w', IsCapped α w' → ∑ i, w i * h i ≤ ∑ i, w' i * h i := by
    intro w' hw'
    have h0 := qp_foc_x hqp hw'
    have h2 : 0 ≤ ⟪fh, wsum φ x w' - wsum φ x w⟫_ℝ := by
      rw [hinner]; exact mul_nonneg (inv_nonneg.2 hDh.le) h0
    rw [inner_sub_right, inner_wsum, inner_wsum] at h2
    linarith
  have hBmax : ∀ v', IsCapped α v' → ∑ j, v' j * h' j ≤ ∑ j, v j * h' j := by
    intro v' hv'
    have h0 := qp_foc_y hqp hv'
    have h2 : 0 ≤ ⟪fh, wsum φ y v - wsum φ y v'⟫_ℝ := by
      rw [hinner]; exact mul_nonneg (inv_nonneg.2 hDh.le) h0
    rw [inner_sub_right, inner_wsum, inner_wsum] at h2
    linarith
  -- finite CVaR duality: `max T ≥ A`, `min U ≤ B`
  obtain ⟨tstar, w', hw', hw'eq⟩ := exists_critT_eq hn x hα0 hα1 hFm hFb
  obtain ⟨ustar, v', hv', hv'eq⟩ := exists_critU_eq hm y hα0 hα1 hFm hFb
  have hTstar : ∑ i, w i * h i ≤ critT α h tstar := (hAmin w' hw').trans_eq hw'eq
  have hUstar : critU α h' ustar ≤ ∑ j, v j * h' j := hv'eq.symm.le.trans (hBmax v' hv')
  -- own terms
  set εX := beta α / n * κ ^ 2 / Dh with hεX
  set εY := beta α / m * κ ^ 2 / Dh with hεY
  have hεX0 : 0 ≤ εX := by positivity
  have hεY0 : 0 ≤ εY := by positivity
  have hown : ∀ (k : ℕ) (c : ℝ), 0 ≤ c → c ≤ 1 / (k * (1 - α)) → ∀ z,
      0 ≤ c * ‖φ z‖ ^ 2 / Dh ∧ c * ‖φ z‖ ^ 2 / Dh ≤ beta α / k * κ ^ 2 / Dh := by
    intro k c hc0 hc1 z
    rw [cap_eq] at hc1
    refine ⟨by positivity, ?_⟩
    gcongr
    exact hκ z
  have hownX : ∀ i, h i - εX ≤ ownX φ x y w v i ∧ ownX φ x y w v i ≤ h i := by
    intro i
    obtain ⟨a, b⟩ := hown n (w i) (hqp.1.1 i).1 (hqp.1.1 i).2 (x i)
    have : ownX φ x y w v i = h i - w i * ‖φ (x i)‖ ^ 2 / Dh := rfl
    rw [this]; constructor <;> linarith
  have hownY : ∀ j, h' j ≤ ownY φ x y w v j ∧ ownY φ x y w v j ≤ h' j + εY := by
    intro j
    obtain ⟨a, b⟩ := hown m (v j) (hqp.2.1.1 j).1 (hqp.2.1.1 j).2 (y j)
    have : ownY φ x y w v j = h' j + v j * ‖φ (y j)‖ ^ 2 / Dh := rfl
    rw [this]; constructor <;> linarith
  -- ranks
  have hp1 : 1 - α ≤ 1 := by linarith
  have hα1' : α ≤ 1 := hα1.le
  have hkL1 : 1 ≤ rkLo n (1 - α) := one_le_rkLo _ _
  have hkLn : rkLo n (1 - α) ≤ n := rkLo_le hn hp1
  have hkH1 : 1 ≤ rkHi n (1 - α) := one_le_rkHi hn _
  have hkHn : rkHi n (1 - α) ≤ n := rkHi_le _ _
  have hkLH : rkLo n (1 - α) ≤ rkHi n (1 - α) := rkLo_le_rkHi hn hp1
  have hjL1 : 1 ≤ rkLo m α := one_le_rkLo _ _
  have hjLm : rkLo m α ≤ m := rkLo_le hm hα1'
  have hjH1 : 1 ≤ rkHi m α := one_le_rkHi hm _
  have hjHm : rkHi m α ≤ m := rkHi_le _ _
  have hjLH : rkLo m α ≤ rkHi m α := rkLo_le_rkHi hm hα1'
  -- the cuts against the order statistics of the in-sample values
  obtain ⟨⟨ht1, ht2⟩, ⟨hu1, hu2⟩⟩ := hC
  have ht_lo : ordStat h (rkLo n (1 - α)) - εX ≤ t :=
    (ordStat_sub_le (fun i => (hownX i).1) hkL1 hkLn).trans ht1
  have ht_hi : t ≤ ordStat h (rkHi n (1 - α)) :=
    ht2.trans (ordStat_mono (fun i => (hownX i).2) hkH1 hkHn)
  have hu_lo : ordStat h' (rkLo m α) ≤ u :=
    (ordStat_mono (fun j => (hownY j).1) hjL1 hjLm).trans hu1
  have hu_hi : u ≤ ordStat h' (rkHi m α) + εY := by
    have := ordStat_sub_le (h := ownY φ x y w v) (h' := h') (ε := εY)
      (fun j => by linarith [(hownY j).2]) hjH1 hjHm
    linarith
  -- the range of the witness values
  have hrange : ∀ a b : 𝒳, F a - F b ≤ Dφ := by
    intro a b
    have : F a - F b = ⟪fh, φ a - φ b⟫_ℝ := by simp only [hFdef, inner_sub_right]
    rw [this]
    refine (real_inner_le_norm _ _).trans ?_
    rw [hfh1, one_mul]; exact hDφ a b
  have hR : ∀ i j, h i - h j ≤ Dφ := fun i j => hrange _ _
  have hR' : ∀ i j, h' i - h' j ≤ Dφ := fun i j => hrange _ _
  have hLip : max 1 (beta α - 1) ≤ beta α := max_le hβ1 (by linarith)
  -- the cuts are nearly optimal (Lemma 3)
  have hT : critT α h tstar - beta α / n * Dφ - beta α * εX ≤ critT α h t := by
    set t₀ := max t (ordStat h (rkLo n (1 - α))) with ht₀def
    have ht₀ : t₀ ∈ Icc (ordStat h (rkLo n (1 - α))) (ordStat h (rkHi n (1 - α))) :=
      ⟨le_max_right _ _, max_le ht_hi (ordStat_mono_rank h hkL1 hkLH hkHn)⟩
    have hb := critT_bracket hn hα0 hα1 h hR ht₀ tstar
    have hl := critT_lipschitz hα0 hα1 h t₀ t
    have hd : |t₀ - t| ≤ εX := by
      have h0 : t ≤ t₀ := le_max_left _ _
      have h2 : t₀ - t ≤ εX := by
        rcases le_total t (ordStat h (rkLo n (1 - α))) with hle | hle
        · rw [ht₀def, max_eq_right hle]; linarith
        · rw [ht₀def, max_eq_left hle]; linarith
      rw [abs_of_nonneg (by linarith)]; exact h2
    have h3 : |critT α h t₀ - critT α h t| ≤ beta α * εX :=
      hl.trans (mul_le_mul hLip hd (abs_nonneg _) hβ0)
    have := (abs_le.1 h3).2
    linarith
  have hU : critU α h' u ≤ critU α h' ustar + beta α / m * Dφ + beta α * εY := by
    set u₀ := min u (ordStat h' (rkHi m α)) with hu₀def
    have hu₀ : u₀ ∈ Icc (ordStat h' (rkLo m α)) (ordStat h' (rkHi m α)) :=
      ⟨le_min hu_lo (ordStat_mono_rank h' hjL1 hjLH hjHm), min_le_right _ _⟩
    have hb := critU_bracket hm hα0 hα1 h' hR' hu₀ ustar
    have hl := critU_lipschitz hα0 hα1 h' u u₀
    have hd : |u - u₀| ≤ εY := by
      have h0 : u₀ ≤ u := min_le_left _ _
      have h2 : u - u₀ ≤ εY := by
        rcases le_total u (ordStat h' (rkHi m α)) with hle | hle
        · rw [hu₀def, min_eq_left hle]; linarith
        · rw [hu₀def, min_eq_right hle]; linarith
      rw [abs_of_nonneg (by linarith)]; exact h2
    have h3 : |critU α h' u - critU α h' u₀| ≤ beta α * εY :=
      hl.trans (mul_le_mul hLip hd (abs_nonneg _) hβ0)
    have := (abs_le.1 h3).2
    linarith
  -- the empirical criterion at the fitted cuts
  have hθn : Dh - beta α * Dφ * (1 / n + 1 / m) - beta α ^ 2 * κ ^ 2 * (1 / n + 1 / m) / Dh ≤
      critT α h t - critU α h' u := by
    have e1 : beta α * εX + beta α * εY = beta α ^ 2 * κ ^ 2 * (1 / n + 1 / m) / Dh := by
      simp only [hεX, hεY]; ring
    have e2 : beta α / n * Dφ + beta α / m * Dφ = beta α * Dφ * (1 / n + 1 / m) := by ring
    linarith
  -- Lemma 2: the population criterion
  have hcu : -(beta α) * Zp ≤ theta P Q α F t u - (critT α h t - critU α h' u) :=
    (crit_uniform_route 𝒳 H P Q φ κ α n m x y fh t u hφ hκ hα0 hα1 hn hm hfh1.le).1
  have hDm : 0 < D - beta α * Zm := by linarith
  have hc0 : 0 ≤ beta α ^ 2 * κ ^ 2 * (1 / n + 1 / m) := by positivity
  have hdiv : beta α ^ 2 * κ ^ 2 * (1 / n + 1 / m) / Dh ≤
      beta α ^ 2 * κ ^ 2 * (1 / n + 1 / m) / (D - beta α * Zm) :=
    div_le_div_of_nonneg_left hc0 hDm h1
  have hθ : fitTheta α D Zp Zm κ Dφ (1 / n + 1 / m) ≤ theta P Q α F t u := by
    unfold fitTheta
    linarith
  -- the width
  have hwidth : t - u ≤ Dφ := by
    obtain ⟨i, hi⟩ := exists_eq_ordStat h hkH1 hkHn
    obtain ⟨j, hj⟩ := exists_eq_ordStat h' hjL1 hjLm
    have := hrange (x i) (y j)
    have hi' : F (x i) = ordStat h (rkHi n (1 - α)) := hi
    have hj' : F (y j) = ordStat h' (rkLo m α) := hj
    linarith
  have hθle : theta P Q α F t u ≤ t - u := by
    rw [Elem.theta_eq P Q α (Elem.integrable_hinge hFm hFb t).1 (Elem.integrable_hinge hFm hFb u).2]
    have h1 : 0 ≤ ∫ z, max (t - F z) 0 ∂P := integral_nonneg fun _ => le_max_right _ _
    have h2 : 0 ≤ ∫ z, max (F z - u) 0 ∂Q := integral_nonneg fun _ => le_max_right _ _
    have h3 := mul_nonneg hβ0 h1
    have h4 := mul_nonneg hβ0 h2
    linarith only [h3, h4]
  refine ⟨hwidth, hθle, hθ, fun hΘpos => ?_⟩
  -- the excess of the ramp
  have hut : u < t := by linarith
  obtain ⟨-, h21⟩ := StatFormal.Wave30tq.lem2_1 𝒳 P Q α F t u hFm hα0 hα1 hut
  obtain ⟨-, h22⟩ := StatFormal.Wave30tq.lem2_2 𝒳 P Q α F t u hFm ⟨κ, hFb⟩ hα0 hα1 hut
  obtain ⟨h22e, -⟩ := StatFormal.Wave30tq.lem2_2 𝒳 P Q α F t u hFm ⟨κ, hFb⟩ hα0 hα1 hut
  have hβpos : 0 < beta α := by linarith
  have hclip : fitTheta α D Zp Zm κ Dφ (1 / n + 1 / m) ≤
      beta α * (t - u) * ((∫ z, ramp F t u z ∂P) - (∫ z, ramp F t u z ∂Q) - α) := by
    rw [← h21]; linarith
  have hpos : 0 < beta α * (t - u) := mul_pos hβpos (by linarith)
  refine ⟨hut, ?_⟩
  calc fitTheta α D Zp Zm κ Dφ (1 / n + 1 / m) / (beta α * Dφ)
      ≤ fitTheta α D Zp Zm κ Dφ (1 / n + 1 / m) / (beta α * (t - u)) :=
        div_le_div_of_nonneg_left hΘpos.le hpos (mul_le_mul_of_nonneg_left hwidth hβpos.le)
    _ ≤ _ := by rw [div_le_iff₀ hpos]; linarith

end StatFormal.Wave30tz
