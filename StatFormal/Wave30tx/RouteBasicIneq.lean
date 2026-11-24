import StatFormal.Wave30tx.RouteBasic
import StatFormal.Archive.Wave12c.RouteTrimConsist
import StatFormal.Archive.TrimmedMMD.Concentration.Proofs
import StatFormal.Archive.TrimmedMMD.Concentration.Region

/-!
# Route: `lem:basicineq (v2)` (untrusted proof material)

* Hilbert-space part (as in `RouteSep`): the first-order condition of the projection of the origin onto a convex set,
  `sepAB_le_inner` (`sep(f; A, B) ≤ ⟨f, d⟩` for `d ∈ A − B`), `le_sepAB_dir` (`sep(d/‖d‖; A, B) ≥ ‖d‖` for the minimum-norm
  element `d` of a convex `A − B`).
* CVaR part, for any probability measure `R` and bounded measurable `Y`, `β̄ = (1−α)⁻¹`:
  `integral_ge_cvar` (weak duality, lower tail: `∫gY ≥ t − β̄∫(t − Y)₊`), `exists_attain_lower` (attainment at a
  `(1−α)`-quantile), `exists_attain_upper` (attainment at an `α`-quantile, via `−Y`); and for the regions:
  `lower_le_sInf`, `sInf_le_attain`, `sSup_le_upper`, `attain_le_sSup`.
* Empirical quantiles: `isQuantile_ord` (`t̂`, the `(n_α+1)`-th smallest, is a `(1−α)`-quantile under `P_n`) and
  `isQuantile_ordTop` (`û`, the `(m_α+1)`-th largest, is an `α`-quantile under `Q_m`).
* `basicineq`: the claim.
-/

noncomputable section
open MeasureTheory Set Finset
open scoped InnerProductSpace Pointwise

namespace StatFormal.Wave30tx.RBasicIneq

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.Projection StatFormal.Wave30tx
  StatFormal.Wave12c

/-! ### Hilbert-space facts -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem inner_nonneg_of_min' {d v : H}
    (h : ∀ s : ℝ, 0 < s → s ≤ 1 → ‖d‖ ^ 2 ≤ ‖d + s • v‖ ^ 2) : 0 ≤ ⟪d, v⟫_ℝ := by
  by_contra hc
  push Not at hc
  set c := ⟪d, v⟫_ℝ
  set N := ‖v‖ ^ 2
  have hN : 0 ≤ N := sq_nonneg _
  set s := min 1 (-c / (N + 1))
  have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) (by linarith))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsN : s * N ≤ -c := by
    have h1 : s ≤ -c / (N + 1) := min_le_right _ _
    have h2 : s * N ≤ -c / (N + 1) * N := mul_le_mul_of_nonneg_right h1 hN
    have h3 : -c / (N + 1) * N ≤ -c := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have key := h s hs0 hs1
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at key
  have : 0 ≤ s * (2 * c + s * N) := by nlinarith
  have := (mul_nonneg_iff_of_pos_left hs0).1 this
  linarith

theorem inner_ge_of_isMinNorm {K : Set H} {d : H} (hK : Convex ℝ K) (hd : IsMinNorm K d) {z : H}
    (hz : z ∈ K) : ‖d‖ ^ 2 ≤ ⟪d, z⟫_ℝ := by
  have key : 0 ≤ ⟪d, z - d⟫_ℝ := by
    refine inner_nonneg_of_min' fun s hs0 hs1 => ?_
    have hmem : d + s • (z - d) ∈ K := by
      have := hK hd.1 hz (by linarith : (0 : ℝ) ≤ 1 - s) hs0.le (by ring)
      convert this using 1
      rw [smul_sub, sub_smul, one_smul]; abel
    exact pow_le_pow_left₀ (norm_nonneg _) (hd.2 _ hmem) 2
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at key
  linarith

theorem norm_le_inner_dir {K : Set H} {d : H} (hK : Convex ℝ K) (hd : IsMinNorm K d)
    (hD : 0 < ‖d‖) {z : H} (hz : z ∈ K) : ‖d‖ ≤ ⟪‖d‖⁻¹ • d, z⟫_ℝ := by
  have h := inner_ge_of_isMinNorm hK hd hz
  rw [real_inner_smul_left, le_inv_mul_iff₀ hD]
  nlinarith

theorem inner_unit {u f : H} (hu : ‖u‖ = 1) (hf : ‖f‖ = 1) : ⟪u, f⟫_ℝ = 1 - ‖u - f‖ ^ 2 / 2 := by
  rw [norm_sub_sq_real, hu, hf]; ring

theorem norm_dir {d : H} (hD : 0 < ‖d‖) : ‖‖d‖⁻¹ • d‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hD.ne']

/-- `sep(f; A, B) ≤ ⟨f, d⟩` for every `d ∈ A − B`. -/
theorem sepAB_le_inner {A B : Set H} {f d : H}
    (hA : BddBelow ((fun a => ⟪f, a⟫_ℝ) '' A)) (hB : BddAbove ((fun b => ⟪f, b⟫_ℝ) '' B))
    (hd : d ∈ A - B) : sepAB A B f ≤ ⟪f, d⟫_ℝ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hd
  have h1 : sInf ((fun a => ⟪f, a⟫_ℝ) '' A) ≤ ⟪f, a⟫_ℝ := csInf_le hA (mem_image_of_mem _ ha)
  have h2 : ⟪f, b⟫_ℝ ≤ sSup ((fun b => ⟪f, b⟫_ℝ) '' B) := le_csSup hB (mem_image_of_mem _ hb)
  unfold sepAB
  rw [inner_sub_right]
  linarith

/-- If `c ≤ ⟨f, a − b⟩` for all `a ∈ A`, `b ∈ B` (both nonempty), then `c ≤ sep(f; A, B)`. -/
theorem le_sepAB {A B : Set H} {f : H} (hA : A.Nonempty) (hB : B.Nonempty) {c : ℝ}
    (h : ∀ a ∈ A, ∀ b ∈ B, c ≤ ⟪f, a - b⟫_ℝ) : c ≤ sepAB A B f := by
  have hs : ∀ a ∈ A, c + sSup ((fun b => ⟪f, b⟫_ℝ) '' B) ≤ ⟪f, a⟫_ℝ := by
    intro a ha
    have : sSup ((fun b => ⟪f, b⟫_ℝ) '' B) ≤ ⟪f, a⟫_ℝ - c := by
      refine csSup_le (hB.image _) ?_
      rintro _ ⟨b, hb, rfl⟩
      have := h a ha b hb
      rw [inner_sub_right] at this
      linarith
    linarith
  have : c + sSup ((fun b => ⟪f, b⟫_ℝ) '' B) ≤ sInf ((fun a => ⟪f, a⟫_ℝ) '' A) := by
    refine le_csInf (hA.image _) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact hs a ha
  unfold sepAB
  linarith

/-- For the minimum-norm element `d` of a convex `A − B`, `sep(d/‖d‖; A, B) ≥ ‖d‖`. -/
theorem le_sepAB_dir {A B : Set H} {d : H} (hA : A.Nonempty) (hB : B.Nonempty)
    (hC : Convex ℝ (A - B)) (hd : IsMinNorm (A - B) d) (hD : 0 < ‖d‖) :
    ‖d‖ ≤ sepAB A B (‖d‖⁻¹ • d) :=
  le_sepAB hA hB fun _ ha _ hb => norm_le_inner_dir hC hd hD (Set.sub_mem_sub ha hb)

end Hilbert

/-! ### CVaR facts for a bounded measurable variable -/

section CVaR

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

theorem integrable_ramp (R : Measure 𝒳) [IsFiniteMeasure R] {Y : 𝒳 → ℝ} (hY : Measurable Y) {K : ℝ}
    (hYb : ∀ x, |Y x| ≤ K) (t : ℝ) :
    Integrable (fun x => max (t - Y x) 0) R ∧ Integrable (fun x => max (Y x - t) 0) R := by
  have hb : ∀ x, |max (t - Y x) 0| ≤ |t| + K ∧ |max (Y x - t) 0| ≤ |t| + K := fun x => by
    have h1 := hYb x
    have h2 := abs_nonneg t
    have h3 := le_abs_self (Y x)
    have h4 := neg_abs_le (Y x)
    have h5 := le_abs_self t
    have h6 := neg_abs_le t
    constructor
    · rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (by linarith) (by linarith)
    · rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (by linarith) (by linarith)
  exact ⟨Integrable.of_bound ((measurable_const.sub hY).max measurable_const).aestronglyMeasurable
      (|t| + K) (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact (hb x).1),
    Integrable.of_bound ((hY.sub measurable_const).max measurable_const).aestronglyMeasurable
      (|t| + K) (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact (hb x).2)⟩

/-- Weak duality, lower tail: `∫ g Y ≥ t − β ∫ (t − Y)₊` for an admissible weight `g`. -/
theorem integral_ge_cvar (R : Measure 𝒳) [IsProbabilityMeasure R] {Y : 𝒳 → ℝ} (hY : Measurable Y)
    {K : ℝ} (hYb : ∀ x, |Y x| ≤ K) {β : ℝ} {g : 𝒳 → ℝ} (hg : Measurable g)
    (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ β) (hg1 : ∫ x, g x ∂R = 1) (t : ℝ) :
    t - β * ∫ x, max (t - Y x) 0 ∂R ≤ ∫ x, g x * Y x ∂R := by
  have h := integral_mul_le_cvar R (Y := fun x => -Y x) hY.neg (κ := K)
    (fun x => by rw [abs_neg]; exact hYb x) hg hgb hg1 (-t)
  have e1 : ∫ x, g x * -Y x ∂R = -∫ x, g x * Y x ∂R := by
    rw [← integral_neg]; congr 1; funext x; ring
  have e2 : (fun x => max (-Y x - -t) 0) = fun x => max (t - Y x) 0 := by
    funext x; congr 1; ring
  rw [e1, e2] at h
  linarith

/-- Attainment at a `(1−α)`-quantile `t`: the bathtub weight `β̄ 1{Y < t} + θ 1{Y = t}`. -/
theorem exists_attain_lower (R : Measure 𝒳) [IsProbabilityMeasure R] {Y : 𝒳 → ℝ}
    (hY : Measurable Y) {K : ℝ} (hYb : ∀ x, |Y x| ≤ K) {α t : ℝ} (hα1 : α < 1)
    (ht1 : R.real {x | Y x < t} ≤ 1 - α) (ht2 : 1 - α ≤ R.real {x | Y x ≤ t}) :
    ∃ g : 𝒳 → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ 1 / (1 - α)) ∧ ∫ x, g x ∂R = 1 ∧
      ∫ x, g x * Y x ∂R = t - 1 / (1 - α) * ∫ x, max (t - Y x) 0 ∂R := by
  have hβ' : 0 < 1 - α := by linarith
  set B := 1 / (1 - α) with hBdef
  have hB0 : 0 < B := by positivity
  set p1 := R.real {x | Y x < t}
  set p2 := R.real {x | Y x = t}
  have hle : R.real {x | Y x ≤ t} = p1 + p2 := by
    have hu : {x | Y x ≤ t} = {x | Y x < t} ∪ {x | Y x = t} := by
      ext x; simp only [mem_ofPred_eq, mem_union, le_iff_lt_or_eq]
    have hdisj : Disjoint {x | Y x < t} {x | Y x = t} := Set.disjoint_left.2 fun x hx hx' => by
      have h1 : Y x < t := hx
      have h2 : Y x = t := hx'
      linarith
    rw [hu, measureReal_union hdisj (measurableSet_eq_fun hY measurable_const)]
  have hp2 : 0 ≤ p2 := measureReal_nonneg
  have hBp1 : B * p1 ≤ 1 := by
    rw [hBdef, div_mul_eq_mul_div, one_mul, div_le_one hβ']; exact ht1
  have hBp12 : 1 ≤ B * (p1 + p2) := by
    rw [hBdef, div_mul_eq_mul_div, one_mul, le_div_iff₀ hβ', one_mul, ← hle]; exact ht2
  set θ : ℝ := if p2 = 0 then 0 else (1 - B * p1) / p2 with hθdef
  have hθ : 0 ≤ θ ∧ θ ≤ B ∧ B * p1 + θ * p2 = 1 := by
    by_cases h0 : p2 = 0
    · simp only [hθdef, h0, ite_true, mul_zero, add_zero, le_refl, true_and]
      refine ⟨hB0.le, ?_⟩
      rw [h0, add_zero] at hBp12; linarith
    · have hp2' : 0 < p2 := lt_of_le_of_ne hp2 (Ne.symm h0)
      simp only [hθdef, h0, ite_false]
      refine ⟨div_nonneg (by linarith) hp2, ?_, ?_⟩
      · rw [div_le_iff₀ hp2']; nlinarith
      · field_simp; ring
  set gb : 𝒳 → ℝ := fun x => if Y x < t then B else if Y x = t then θ else 0 with hgbdef
  have hgbm : Measurable gb :=
    Measurable.ite (measurableSet_lt hY measurable_const) measurable_const
      (Measurable.ite (measurableSet_eq_fun hY measurable_const) measurable_const measurable_const)
  have hgbb : ∀ x, 0 ≤ gb x ∧ gb x ≤ B := fun x => by
    simp only [gb]; split_ifs <;> constructor <;> linarith [hθ.1, hθ.2.1]
  have hgb1 : ∫ x, gb x ∂R = 1 := by
    have e : gb = fun x => B * ({x | Y x < t}.indicator 1 x) + θ * ({x | Y x = t}.indicator 1 x) := by
      funext x; simp only [gb, Set.indicator, mem_ofPred_eq, Pi.one_apply]
      split_ifs <;> first | (exfalso; linarith) | simp
    rw [e, integral_add (f := fun x => B * {x | Y x < t}.indicator 1 x)
        (g := fun x => θ * {x | Y x = t}.indicator 1 x)
        ((integrable_const (1 : ℝ)).indicator (measurableSet_lt hY measurable_const) |>.const_mul _)
        ((integrable_const (1 : ℝ)).indicator (measurableSet_eq_fun hY measurable_const) |>.const_mul _),
      integral_const_mul, integral_const_mul,
      integral_indicator_one (measurableSet_lt hY measurable_const),
      integral_indicator_one (measurableSet_eq_fun hY measurable_const)]
    exact hθ.2.2
  refine ⟨gb, hgbm, hgbb, hgb1, ?_⟩
  have hpt : ∀ x, gb x * Y x = t * gb x + -B * max (t - Y x) 0 := by
    intro x
    simp only [gb]
    split_ifs with h1 h2
    · rw [max_eq_left (by linarith)]; ring
    · rw [h2, sub_self, max_self]; ring
    · push Not at h1
      have : t < Y x := lt_of_le_of_ne h1 (Ne.symm h2)
      rw [max_eq_right (by linarith)]; ring
  have hgI : Integrable gb R := Integrable.of_bound hgbm.aestronglyMeasurable B
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hgbb x).1]; exact (hgbb x).2)
  have hmI := (integrable_ramp R hY hYb t).1
  calc ∫ x, gb x * Y x ∂R = ∫ x, (t * gb x + -B * max (t - Y x) 0) ∂R :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = t - B * ∫ x, max (t - Y x) 0 ∂R := by
        rw [integral_add (hgI.const_mul t) (hmI.const_mul (-B)), integral_const_mul,
          integral_const_mul, hgb1]
        ring

/-- Attainment at an `α`-quantile `u` (upper tail), via `−Y`. -/
theorem exists_attain_upper (R : Measure 𝒳) [IsProbabilityMeasure R] {Y : 𝒳 → ℝ}
    (hY : Measurable Y) {K : ℝ} (hYb : ∀ x, |Y x| ≤ K) {α u : ℝ} (hα1 : α < 1)
    (hu1 : R.real {x | Y x < u} ≤ α) (hu2 : α ≤ R.real {x | Y x ≤ u}) :
    ∃ g : 𝒳 → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ 1 / (1 - α)) ∧ ∫ x, g x ∂R = 1 ∧
      ∫ x, g x * Y x ∂R = u + 1 / (1 - α) * ∫ x, max (Y x - u) 0 ∂R := by
  have hc1 : R.real {x | -Y x < -u} ≤ 1 - α := by
    have : {x | -Y x < -u} = {x | Y x ≤ u}ᶜ := by ext x; simp [not_le]
    rw [this, probReal_compl_eq_one_sub (measurableSet_le hY measurable_const)]; linarith
  have hc2 : 1 - α ≤ R.real {x | -Y x ≤ -u} := by
    have : {x | -Y x ≤ -u} = {x | Y x < u}ᶜ := by ext x; simp [not_lt]
    rw [this, probReal_compl_eq_one_sub (measurableSet_lt hY measurable_const)]; linarith
  obtain ⟨g, hg, hgb, hg1, hgY⟩ := exists_attain_lower R (Y := fun x => -Y x) hY.neg (K := K)
    (fun x => by rw [abs_neg]; exact hYb x) hα1 hc1 hc2
  refine ⟨g, hg, hgb, hg1, ?_⟩
  have e1 : ∫ x, g x * -Y x ∂R = -∫ x, g x * Y x ∂R := by
    rw [← integral_neg]; congr 1; funext x; ring
  have e2 : ∫ x, max (-u - -Y x) 0 ∂R = ∫ x, max (Y x - u) 0 ∂R := by
    congr 1; funext x; congr 1; ring
  rw [e1, e2] at hgY
  linarith

end CVaR

/-! ### The regions -/

section Region

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] {φ : 𝒳 → H} {κ α : ℝ}

theorem inner_mem_region (R : Measure 𝒳) [IsProbabilityMeasure R] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) {a : H} (ha : a ∈ region φ α R) (f : H) :
    ∃ g : 𝒳 → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ 1 / (1 - α)) ∧ ∫ x, g x ∂R = 1 ∧
      ⟪f, a⟫_ℝ = ∫ x, g x * witFn f φ x ∂R := by
  obtain ⟨g, hg, hgb, hg1, rfl⟩ := ha
  exact ⟨g, hg, hgb, hg1, inner_integral_smul R hφ hκ hg hgb f⟩

theorem lower_le_sInf (R : Measure 𝒳) [IsProbabilityMeasure R] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (f : H) (t : ℝ) :
    t - 1 / (1 - α) * ∫ x, max (t - witFn f φ x) 0 ∂R ≤
      sInf ((fun a => ⟪f, a⟫_ℝ) '' region φ α R) := by
  refine le_csInf ((region_nonempty R hα0 hα1).image _) ?_
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨g, hg, hgb, hg1, he⟩ := inner_mem_region R hφ hκ ha f
  dsimp only
  rw [he]
  exact integral_ge_cvar R (measurable_witFn hφ f) (abs_witFn_le hκ f) hg hgb hg1 t

theorem bddBelow_region (R : Measure 𝒳) [IsProbabilityMeasure R] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (f : H) : BddBelow ((fun a => ⟪f, a⟫_ℝ) '' region φ α R) := by
  refine ⟨0 - 1 / (1 - α) * ∫ x, max (0 - witFn f φ x) 0 ∂R, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨g, hg, hgb, hg1, he⟩ := inner_mem_region R hφ hκ ha f
  dsimp only
  rw [he]
  exact integral_ge_cvar R (measurable_witFn hφ f) (abs_witFn_le hκ f) hg hgb hg1 0

theorem bddAbove_region (R : Measure 𝒳) [IsProbabilityMeasure R] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (f : H) : BddAbove ((fun a => ⟪f, a⟫_ℝ) '' region φ α R) := by
  refine ⟨0 + 1 / (1 - α) * ∫ x, max (witFn f φ x - 0) 0 ∂R, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨g, hg, hgb, hg1, he⟩ := inner_mem_region R hφ hκ ha f
  dsimp only
  rw [he]
  exact integral_mul_le_cvar R (measurable_witFn hφ f) (abs_witFn_le hκ f) hg hgb hg1 0

theorem sInf_le_attain (R : Measure 𝒳) [IsProbabilityMeasure R] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα1 : α < 1) (f : H) {t : ℝ}
    (ht : IsQuantile R (witFn f φ) (1 - α) t) :
    sInf ((fun a => ⟪f, a⟫_ℝ) '' region φ α R) ≤
      t - 1 / (1 - α) * ∫ x, max (t - witFn f φ x) 0 ∂R := by
  obtain ⟨g, hg, hgb, hg1, hgY⟩ :=
    exists_attain_lower R (measurable_witFn hφ f) (abs_witFn_le hκ f) hα1 ht.1 ht.2
  have hmem : ∫ x, g x • φ x ∂R ∈ region φ α R := ⟨g, hg, hgb, hg1, rfl⟩
  calc sInf ((fun a => ⟪f, a⟫_ℝ) '' region φ α R) ≤ ⟪f, ∫ x, g x • φ x ∂R⟫_ℝ :=
        csInf_le (bddBelow_region R hφ hκ f) (mem_image_of_mem _ hmem)
    _ = ∫ x, g x * witFn f φ x ∂R := inner_integral_smul R hφ hκ hg hgb f
    _ = _ := hgY

theorem sSup_le_upper (R : Measure 𝒳) [IsProbabilityMeasure R] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (f : H) (u : ℝ) :
    sSup ((fun a => ⟪f, a⟫_ℝ) '' region φ α R) ≤
      u + 1 / (1 - α) * ∫ x, max (witFn f φ x - u) 0 ∂R := by
  refine csSup_le ((region_nonempty R hα0 hα1).image _) ?_
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨g, hg, hgb, hg1, he⟩ := inner_mem_region R hφ hκ ha f
  dsimp only
  rw [he]
  exact integral_mul_le_cvar R (measurable_witFn hφ f) (abs_witFn_le hκ f) hg hgb hg1 u

theorem attain_le_sSup (R : Measure 𝒳) [IsProbabilityMeasure R] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα1 : α < 1) (f : H) {u : ℝ}
    (hu : IsQuantile R (witFn f φ) α u) :
    u + 1 / (1 - α) * ∫ x, max (witFn f φ x - u) 0 ∂R ≤
      sSup ((fun a => ⟪f, a⟫_ℝ) '' region φ α R) := by
  obtain ⟨g, hg, hgb, hg1, hgY⟩ :=
    exists_attain_upper R (measurable_witFn hφ f) (abs_witFn_le hκ f) hα1 hu.1 hu.2
  have hmem : ∫ x, g x • φ x ∂R ∈ region φ α R := ⟨g, hg, hgb, hg1, rfl⟩
  calc u + 1 / (1 - α) * ∫ x, max (witFn f φ x - u) 0 ∂R = ∫ x, g x * witFn f φ x ∂R := hgY.symm
    _ = ⟪f, ∫ x, g x • φ x ∂R⟫_ℝ := (inner_integral_smul R hφ hκ hg hgb f).symm
    _ ≤ sSup ((fun a => ⟪f, a⟫_ℝ) '' region φ α R) :=
        le_csSup (bddAbove_region R hφ hκ f) (mem_image_of_mem _ hmem)

end Region

/-! ### Empirical quantiles -/

section Empirical

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

theorem empirical_real {n : ℕ} (hn : n ≠ 0) (x : Fin n → 𝒳) {p : 𝒳 → Prop} [DecidablePred p]
    (hS : MeasurableSet {y | p y}) :
    (empirical x).real {y | p y} = (n : ℝ)⁻¹ * ((Finset.univ.filter fun i => p (x i)).card : ℝ) := by
  have := isProbabilityMeasure_empirical hn x
  rw [← integral_indicator_one hS,
    integral_empirical x (stronglyMeasurable_one.indicator hS) (C := 1) (fun y => by
      by_cases h : p y <;> simp [h])]
  congr 1
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : p (x i) <;> simp [h]

theorem card_lt_ord_le {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k < n) :
    (Finset.univ.filter fun i => v i < ord v k).card ≤ k := by
  by_contra hc
  push Not at hc
  set S := Finset.univ.filter fun i => v i < ord v k with hSdef
  have hS : S.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image S v hS
  have hsub : S ⊆ Finset.univ.filter fun i => v i ≤ v i0 := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmax i hi
  have h1 := (ord_le_iff v k hk (v i0)).2 (by have := Finset.card_le_card hsub; omega)
  have h2 : v i0 < ord v k := (Finset.mem_filter.1 hi0).2
  linarith

theorem card_le_ord {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k < n) :
    k + 1 ≤ (Finset.univ.filter fun i => v i ≤ ord v k).card :=
  (ord_le_iff v k hk (ord v k)).1 le_rfl

theorem kfloor_bounds {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ((kfloor n α : ℕ) : ℝ) ≤ n * (1 - α) ∧ (n : ℝ) * (1 - α) < kfloor n α + 1 ∧ kfloor n α < n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hk1 : ((kfloor n α : ℕ) : ℝ) ≤ n * (1 - α) := Nat.floor_le (by nlinarith)
  have hk2 : (n : ℝ) * (1 - α) < kfloor n α + 1 := Nat.lt_floor_add_one _
  refine ⟨hk1, hk2, ?_⟩
  have : ((kfloor n α : ℕ) : ℝ) < n := by nlinarith
  exact_mod_cast this

/-- `t̂ = (n_α+1)`-th smallest of the `Y(x_i)` is a `(1−α)`-quantile of `Y` under `P_n`. -/
theorem isQuantile_ord {n : ℕ} (hn : 1 ≤ n) (x : Fin n → 𝒳) {Y : 𝒳 → ℝ} (hY : Measurable Y) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    IsQuantile (empirical x) Y (1 - α) (ord (fun i => Y (x i)) (kfloor n α)) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hk1, hk2, hkn⟩ := kfloor_bounds hn hα0 hα1
  constructor
  · rw [empirical_real hn0 x (measurableSet_lt hY measurable_const)]
    have hc := card_lt_ord_le (fun i => Y (x i)) (kfloor n α) hkn
    have : ((Finset.univ.filter fun i => Y (x i) < ord (fun i => Y (x i)) (kfloor n α)).card : ℝ) ≤
        (kfloor n α : ℕ) := by exact_mod_cast hc
    rw [inv_mul_le_iff₀ hnpos]
    linarith
  · rw [empirical_real hn0 x (measurableSet_le hY measurable_const)]
    have hc := card_le_ord (fun i => Y (x i)) (kfloor n α) hkn
    have : ((kfloor n α : ℕ) : ℝ) + 1 ≤
        ((Finset.univ.filter fun i => Y (x i) ≤ ord (fun i => Y (x i)) (kfloor n α)).card : ℝ) := by
      exact_mod_cast hc
    rw [le_inv_mul_iff₀ hnpos]
    linarith

/-- `û = (m_α+1)`-th largest of the `Y(y_j)` is an `α`-quantile of `Y` under `Q_m`. -/
theorem isQuantile_ordTop {m : ℕ} (hm : 1 ≤ m) (y : Fin m → 𝒳) {Y : 𝒳 → ℝ} (hY : Measurable Y)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IsQuantile (empirical y) Y α (ordTop (fun j => Y (y j)) α) := by
  have hm0 : m ≠ 0 := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hk1, hk2, hkm⟩ := kfloor_bounds hm hα0 hα1
  set k := kfloor m α with hkdef
  have hj0 : m - k - 1 < m := by omega
  have hsum : (((m - k - 1 : ℕ) : ℝ)) + k + 1 = m := by
    have : m - k - 1 + k + 1 = m := by omega
    exact_mod_cast this
  unfold ordTop
  rw [← hkdef]
  constructor
  · rw [empirical_real hm0 y (measurableSet_lt hY measurable_const)]
    have hc := card_lt_ord_le (fun j => Y (y j)) (m - k - 1) hj0
    have : ((Finset.univ.filter fun j => Y (y j) < ord (fun j => Y (y j)) (m - k - 1)).card : ℝ) ≤
        ((m - k - 1 : ℕ) : ℝ) := by exact_mod_cast hc
    rw [inv_mul_le_iff₀ hmpos]
    nlinarith
  · rw [empirical_real hm0 y (measurableSet_le hY measurable_const)]
    have hc := card_le_ord (fun j => Y (y j)) (m - k - 1) hj0
    have : ((m - k - 1 : ℕ) : ℝ) + 1 ≤
        ((Finset.univ.filter fun j => Y (y j) ≤ ord (fun j => Y (y j)) (m - k - 1)).card : ℝ) := by
      exact_mod_cast hc
    rw [le_inv_mul_iff₀ hmpos]
    nlinarith

end Empirical

/-! ### The claim -/

theorem basicineq : Claims.basicineq := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α tstar ustar n m dstar hφ hκ hα0 hα1 hn hm hmin hD htq huq
    x y pr hpr hprmin hDh D fstar fh th uh ξ
  have hn0 : n ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  have := isProbabilityMeasure_empirical hn0 x
  have := isProbabilityMeasure_empirical hm0 y
  set dh := StatFormal.Wave4b.witness φ x y pr with hdhdef
  have hDeq : D = ‖dstar‖ := RBasic.Dpop_eq_norm hmin
  have hdh : IsMinNorm (region φ α (empirical x) - region φ α (empirical y)) dh :=
    RBasic.witness_isMinNorm hφ hα0.le hα1 hn hm x y hpr hprmin
  have hDheq : Demp φ x y α = ‖dh‖ := RBasic.Demp_eq_norm hφ hα0.le hα1 hn hm x y hpr hprmin
  have hDpos : 0 < ‖dstar‖ := by rw [← hDeq]; exact hD
  have hDhpos : 0 < ‖dh‖ := by rw [← hDheq]; exact hDh
  have hfs : fstar = ‖dstar‖⁻¹ • dstar := by simp only [fstar, hDeq]
  have hfh : fh = ‖dh‖⁻¹ • dh := by simp only [fh, hDheq, dh]
  have hfsn : ‖fstar‖ = 1 := by rw [hfs]; exact norm_dir hDpos
  have hfhn : ‖fh‖ = 1 := by rw [hfh]; exact norm_dir hDhpos
  -- convexity and nonemptiness of the regions
  have hα0' : (0 : ℝ) ≤ α := hα0.le
  have hCP : Convex ℝ (region φ α P - region φ α Q) :=
    (region_convex P hφ hκ).sub (region_convex Q hφ hκ)
  have hCE : Convex ℝ (region φ α (empirical x) - region φ α (empirical y)) :=
    (region_convex (empirical x) hφ hκ).sub (region_convex (empirical y) hφ hκ)
  have hneP := region_nonempty (φ := φ) P hα0' hα1
  have hneQ := region_nonempty (φ := φ) Q hα0' hα1
  have hneX := region_nonempty (φ := φ) (empirical x) hα0' hα1
  have hneY := region_nonempty (φ := φ) (empirical y) hα0' hα1
  -- the margin part
  have hpop1 : ‖dstar‖ ≤ sepAB (region φ α P) (region φ α Q) fstar := by
    rw [hfs]; exact le_sepAB_dir hneP hneQ hCP hmin hDpos
  have hpop2 : sepAB (region φ α P) (region φ α Q) fh ≤ ⟪fh, dstar⟫_ℝ :=
    sepAB_le_inner (bddBelow_region P hφ hκ fh) (bddAbove_region Q hφ hκ fh) hmin.1
  have hemp1 : ‖dh‖ ≤ sepAB (region φ α (empirical x)) (region φ α (empirical y)) fh := by
    rw [hfh]; exact le_sepAB_dir hneX hneY hCE hdh hDhpos
  have hemp2 : sepAB (region φ α (empirical x)) (region φ α (empirical y)) fstar ≤ ‖dh‖ := by
    refine (sepAB_le_inner (bddBelow_region (empirical x) hφ hκ fstar)
      (bddAbove_region (empirical y) hφ hκ fstar) hdh.1).trans ?_
    calc ⟪fstar, dh⟫_ℝ ≤ ‖fstar‖ * ‖dh‖ := real_inner_le_norm _ _
      _ = ‖dh‖ := by rw [hfsn, one_mul]
  have hinner : ⟪fh, dstar⟫_ℝ = ‖dstar‖ * (1 - ‖fh - fstar‖ ^ 2 / 2) := by
    have hds : dstar = ‖dstar‖ • fstar := by
      rw [hfs, smul_smul, mul_inv_cancel₀ hDpos.ne', one_smul]
    conv_lhs => rw [hds]
    rw [real_inner_smul_right, inner_unit hfhn hfsn]
  refine ⟨?_, ?_⟩
  · simp only [ξ]
    rw [hDeq]
    nlinarith [hpop1, hpop2, hemp1, hemp2, hinner]
  · -- the upper bound
    set Zh := witFn fh φ with hZh
    set Zs := witFn fstar φ with hZs
    have hZhm : Measurable Zh := measurable_witFn hφ fh
    have hZsm : Measurable Zs := measurable_witFn hφ fstar
    have hZhb : ∀ x, |Zh x| ≤ ‖fh‖ * κ := abs_witFn_le hκ fh
    have hZsb : ∀ x, |Zs x| ≤ ‖fstar‖ * κ := abs_witFn_le hκ fstar
    have hthq : IsQuantile (empirical x) Zh (1 - α) th := isQuantile_ord hn x hZhm hα0 hα1
    have huhq : IsQuantile (empirical y) Zh α uh := isQuantile_ordTop hm y hZhm hα0 hα1
    -- the eight one-sided bounds
    have b1 := sInf_le_attain (empirical x) hφ hκ hα1 fh hthq
    have b2 := lower_le_sInf P hφ hκ hα0' hα1 fh th
    have b3 := attain_le_sSup (empirical y) hφ hκ hα1 fh huhq
    have b4 := sSup_le_upper Q hφ hκ hα0' hα1 fh uh
    have b5 := sInf_le_attain P hφ hκ hα1 fstar htq
    have b6 := lower_le_sInf (empirical x) hφ hκ hα0' hα1 fstar tstar
    have b7 := attain_le_sSup Q hφ hκ hα1 fstar huq
    have b8 := sSup_le_upper (empirical y) hφ hκ hα0' hα1 fstar ustar
    -- empirical integrals as averages
    have hsmX : ∀ (Z : 𝒳 → ℝ), Measurable Z → ∀ t : ℝ,
        StronglyMeasurable (fun x' => max (t - Z x') 0) ∧ StronglyMeasurable (fun x' => max (Z x' - t) 0) :=
      fun Z hZ t => ⟨((measurable_const.sub hZ).max measurable_const).stronglyMeasurable,
        ((hZ.sub measurable_const).max measurable_const).stronglyMeasurable⟩
    have hbd : ∀ (Z : 𝒳 → ℝ) (K : ℝ), (∀ x, |Z x| ≤ K) → ∀ t : ℝ,
        (∀ x', |max (t - Z x') 0| ≤ |t| + K) ∧ (∀ x', |max (Z x' - t) 0| ≤ |t| + K) := by
      intro Z K hZb t
      refine ⟨fun x' => ?_, fun x' => ?_⟩ <;>
      · have h1 := hZb x'
        have h3 := le_abs_self (Z x')
        have h4 := neg_abs_le (Z x')
        have h5 := le_abs_self t
        have h6 := neg_abs_le t
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) (by linarith)
    have e1 := integral_empirical x (hsmX Zh hZhm th).1 ((hbd Zh _ hZhb th).1)
    have e6 := integral_empirical x (hsmX Zs hZsm tstar).1 ((hbd Zs _ hZsb tstar).1)
    have e3 := integral_empirical y (hsmX Zh hZhm uh).2 ((hbd Zh _ hZhb uh).2)
    have e8 := integral_empirical y (hsmX Zs hZsm ustar).2 ((hbd Zs _ hZsb ustar).2)
    rw [e1] at b1
    rw [e6] at b6
    rw [e3] at b3
    rw [e8] at b8
    -- the two empirical-process terms
    have iP1 := (integrable_ramp P hZhm hZhb th).1
    have iP2 := (integrable_ramp P hZsm hZsb tstar).1
    have iQ1 := (integrable_ramp Q hZhm hZhb uh).2
    have iQ2 := (integrable_ramp Q hZsm hZsb ustar).2
    have hpd1 : popDev P x (fun x' => max (th - witFn fh φ x') 0 - max (tstar - witFn fstar φ x') 0) =
        (∫ x', max (th - Zh x') 0 ∂P - ∫ x', max (tstar - Zs x') 0 ∂P) -
          ((n : ℝ)⁻¹ * ∑ i, max (th - Zh (x i)) 0 - (n : ℝ)⁻¹ * ∑ i, max (tstar - Zs (x i)) 0) := by
      unfold popDev
      rw [integral_sub iP1 iP2, Finset.sum_sub_distrib, mul_sub]
    have hpd2 : popDev Q y (fun y' => max (witFn fh φ y' - uh) 0 - max (witFn fstar φ y' - ustar) 0) =
        (∫ y', max (Zh y' - uh) 0 ∂Q - ∫ y', max (Zs y' - ustar) 0 ∂Q) -
          ((m : ℝ)⁻¹ * ∑ j, max (Zh (y j) - uh) 0 - (m : ℝ)⁻¹ * ∑ j, max (Zs (y j) - ustar) 0) := by
      unfold popDev
      rw [integral_sub iQ1 iQ2, Finset.sum_sub_distrib, mul_sub]
    rw [hpd1, hpd2]
    simp only [ξ, sepAB]
    linarith

end StatFormal.Wave30tx.RBasicIneq
