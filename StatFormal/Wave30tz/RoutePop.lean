import StatFormal.Wave30tz.Statements
import StatFormal.Wave30tq.Proofs
import StatFormal.Wave30tr.RouteDet
import StatFormal.Wave30tv.Proofs
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs

/-!
# Wave 30tz route: Lemma 1 (`lem:popramp`, the population ramp) and "TV = sup over ramps" (untrusted)

* `inner_nonneg_of_norm_le`: first-order optimality of a norm minimum along a segment
  (`‖e‖ ≤ ‖e + s d‖` for `s ∈ (0,1]` gives `⟨e, d⟩ ≥ 0`);
* `exists_sep_dir`: the projection argument of `Wave30tr.setDist_region_le` (projection of `0` onto
  `closure(𝒞_α(P) − 𝒞_α(Q))`): a direction `‖f‖ ≤ 1` with `⟨f, a − b⟩ ≥ D_α` on the two regions;
* `le_trimInf_of`, `trimSup_le_of`, `trim_gap`: every trimming gives a point `∫ γ φ` of the region with
  `∫ F d(γP) = ⟨f, ∫ γ φ dP⟩` (certified `inner_integral_smul`);
* `theta_le_sub` (the hinge terms are `≥ 0`), `excess_of_theta` (the certified 30tq `lem2_1`, `lem2_2`);
* `pop_ramp_rkhs_route`: nearest points, first-order optimality on the convex regions, the certified
  `lem1_attain` at the quantile pair, and `t* ≤ sup F`, `u* ≥ inf F` for the extreme quantiles;
* `ramp_tv_route`: the certified `lem_ramp_iii` (upper bound) and `zeroeq` (`D_α > 0` for `α < TV`), the
  separating direction, `lem1_attain` (quantiles with `θ = trimInf − trimSup ≥ D_α > 0`) and `excess_of_theta`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace Pointwise

set_option linter.style.longLine false

namespace StatFormal.Wave30tz

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30ty StatFormal.Wave30tp
open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.ZeroSet

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- First-order optimality of a norm minimum along a segment. -/
theorem inner_nonneg_of_norm_le {e d : H} (h : ∀ s : ℝ, 0 < s → s ≤ 1 → ‖e‖ ≤ ‖e + s • d‖) :
    0 ≤ ⟪e, d⟫_ℝ := by
  by_contra hneg
  push Not at hneg
  have hd : d ≠ 0 := by rintro rfl; simp at hneg
  have hc : 0 < ‖d‖ ^ 2 := by positivity
  set s := min 1 (-⟪e, d⟫_ℝ / ‖d‖ ^ 2) with hs
  have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) hc)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsc : s * ‖d‖ ^ 2 ≤ -⟪e, d⟫_ℝ := by
    have : s ≤ -⟪e, d⟫_ℝ / ‖d‖ ^ 2 := min_le_right _ _
    rwa [le_div_iff₀ hc] at this
  have h1 := h s hs0 hs1
  have h2 : ‖e‖ ^ 2 ≤ ‖e + s • d‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, abs_of_pos hs0,
    mul_pow] at h2
  have h3 : 0 ≤ s * (-⟪e, d⟫_ℝ - s * ‖d‖ ^ 2) := mul_nonneg hs0.le (by linarith)
  have h4 : s * ⟪e, d⟫_ℝ < 0 := mul_neg_of_pos_of_neg hs0 hneg
  nlinarith

end Hilbert

section Trim

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {φ : 𝒳 → H} {κ α : ℝ}

/-- The separating direction of the projection argument (`Wave30tr.setDist_region_le`, Step 1). -/
theorem exists_sep_dir [CompleteSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ f : H, ‖f‖ ≤ 1 ∧ ∀ a ∈ region φ α P, ∀ b ∈ region φ α Q, Dpop φ P Q α ≤ ⟪f, a - b⟫_ℝ := by
  set A := region φ α P
  set B := region φ α Q
  have hA : A.Nonempty := region_nonempty P hα0 hα1
  have hB : B.Nonempty := region_nonempty Q hα0 hα1
  set K := closure (A - B) with hK
  have hKne : K.Nonempty := (hA.sub hB).closure
  have hKconv : Convex ℝ K := ((region_convex P hφ hκ).sub (region_convex Q hφ hκ)).closure
  have hKcomp : IsComplete K := isClosed_closure.isComplete
  obtain ⟨v, hvK, hv⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKcomp hKconv 0
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hKconv hvK).1 hv
  have hd1 : Dpop φ P Q α ≤ ‖v‖ := by
    have hcl : K ⊆ {c | setDist A B ≤ ‖c‖} := by
      refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact setDist_le_norm ha hb
    exact hcl hvK
  by_cases hv0 : v = 0
  · refine ⟨0, by simp, fun a _ b _ => ?_⟩
    rw [inner_zero_left]
    rw [hv0, norm_zero] at hd1
    exact hd1
  have hnpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  refine ⟨‖v‖⁻¹ • v, ?_, fun a ha b hb => ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnpos.ne']
  have h := hvi (a - b) (subset_closure ⟨a, ha, b, hb, rfl⟩)
  have h' : ‖v‖ ^ 2 ≤ ⟪v, a - b⟫_ℝ := by
    have e : ⟪0 - v, a - b - v⟫_ℝ = ‖v‖ ^ 2 - ⟪v, a - b⟫_ℝ := by
      rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq]; ring
    linarith
  have e2 : ⟪‖v‖⁻¹ • v, a - b⟫_ℝ = ‖v‖⁻¹ * ⟪v, a - b⟫_ℝ := by rw [real_inner_smul_left]
  rw [e2]
  refine hd1.trans ?_
  rw [le_inv_mul_iff₀ hnpos]
  nlinarith

/-- A trimming of `P` gives a point of the region, and the value of `⟨f, ·⟩` there is the trimmed mean. -/
theorem inner_trim [CompleteSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (f : H) {γ : 𝒳 → ℝ} (hγ : IsTrimDensity P α γ) :
    ∫ x, γ x • φ x ∂P ∈ region φ α P ∧
      ⟪f, ∫ x, γ x • φ x ∂P⟫_ℝ = ∫ x, ⟪f, φ x⟫_ℝ ∂(trimMeasure P γ) := by
  refine ⟨⟨γ, hγ.1, hγ.2.1, hγ.2.2, rfl⟩, ?_⟩
  rw [integral_trimMeasure P hγ]
  exact inner_integral_smul P hφ hκ hγ.1 hγ.2.1 f

theorem le_trimInf_of [CompleteSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (f : H) {c : ℝ}
    (hc : ∀ a ∈ region φ α P, c ≤ ⟪f, a⟫_ℝ) : c ≤ trimInf P α (fun x => ⟪f, φ x⟫_ℝ) := by
  have : Fact (0 ≤ α) := ⟨hα0⟩
  have : Fact (α < 1) := ⟨hα1⟩
  refine le_ciInf fun γ => ?_
  obtain ⟨hmem, heq⟩ := inner_trim P hφ hκ f γ.2
  exact (hc _ hmem).trans heq.le

theorem trimSup_le_of [CompleteSpace H] (Q : Measure 𝒳) [IsProbabilityMeasure Q] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (f : H) {c : ℝ}
    (hc : ∀ b ∈ region φ α Q, ⟪f, b⟫_ℝ ≤ c) : trimSup Q α (fun x => ⟪f, φ x⟫_ℝ) ≤ c := by
  have : Fact (0 ≤ α) := ⟨hα0⟩
  have : Fact (α < 1) := ⟨hα1⟩
  refine ciSup_le fun γ => ?_
  obtain ⟨hmem, heq⟩ := inner_trim Q hφ hκ f γ.2
  exact heq.symm.le.trans (hc _ hmem)

/-- A uniform separation of the regions bounds `trimInf − trimSup` from below. -/
theorem trim_gap [CompleteSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (f : H) {c : ℝ}
    (h : ∀ a ∈ region φ α P, ∀ b ∈ region φ α Q, c ≤ ⟪f, a - b⟫_ℝ) :
    c ≤ trimInf P α (fun x => ⟪f, φ x⟫_ℝ) - trimSup Q α (fun x => ⟪f, φ x⟫_ℝ) := by
  have hs : trimSup Q α (fun x => ⟪f, φ x⟫_ℝ) ≤ trimInf P α (fun x => ⟪f, φ x⟫_ℝ) - c := by
    refine trimSup_le_of Q hφ hκ hα0 hα1 f fun b hb => ?_
    have : c + ⟪f, b⟫_ℝ ≤ trimInf P α (fun x => ⟪f, φ x⟫_ℝ) :=
      le_trimInf_of P hφ hκ hα0 hα1 f fun a ha => by
        have := h a ha b hb
        rw [inner_sub_right] at this
        linarith
    linarith
  linarith

end Trim

section Theta

/-- The hinge terms are nonnegative: `θ(F; t, u) ≤ t − u`. -/
theorem theta_le_sub {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {α : ℝ} (hα1 : α < 1) {F : 𝒳 → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ x, |F x| ≤ C) (t u : ℝ) : theta P Q α F t u ≤ t - u := by
  have hβ := beta_pos hα1
  unfold theta
  rw [integral_psiS P hF hC, integral_upper Q hF hC]
  have h1 : 0 ≤ ∫ x, max (t - F x) 0 ∂P := integral_nonneg fun x => le_max_right _ _
  have h2 : 0 ≤ ∫ y, max (F y - u) 0 ∂Q := integral_nonneg fun x => le_max_right _ _
  nlinarith [mul_nonneg hβ.le h1, mul_nonneg hβ.le h2]

/-- Clipping (30tq Lemma 2): a lower bound `d ≤ θ(F; t, u)` with `u < t` gives the ramp excess
`E_P g − E_Q g − α ≥ d / (β (t − u))`. -/
theorem excess_of_theta {𝒳 : Type} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {F : 𝒳 → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ x, |F x| ≤ C) {t u d : ℝ} (hut : u < t) (hd : d ≤ theta P Q α F t u) :
    d / (beta α * (t - u)) ≤ (∫ x, ramp F t u x ∂P) - (∫ y, ramp F t u y ∂Q) - α := by
  have h1 := (StatFormal.Wave30tq.lem2_1 𝒳 P Q α F t u hF hα0 hα1 hut).2
  have h2 := StatFormal.Wave30tq.lem2_2 𝒳 P Q α F t u hF ⟨C, hC⟩ hα0 hα1 hut
  have hpos : 0 < beta α * (t - u) := mul_pos (beta_pos hα1) (sub_pos.2 hut)
  rw [div_le_iff₀ hpos]
  set E := (∫ x, ramp F t u x ∂P) - (∫ y, ramp F t u y ∂Q) - α
  have : theta P Q α F t u ≤ beta α * (t - u) * E := by linarith [h2.1, h2.2]
  linarith

end Theta

/-! ### Lemma 1 (`lem:popramp`) -/

theorem pop_ramp_rkhs_route : StatFormal.Wave30tz.Claims.pop_ramp_rkhs := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ Dφ α a b t u hφ hκ hDφ hα0 hα1 ha hb hab hD ht hu
  set D := Dpop φ P Q α with hDdef
  set e := a - b with he
  set f : H := ‖e‖⁻¹ • e with hf
  set F : 𝒳 → ℝ := fun z => ⟪f, φ z⟫_ℝ with hFdef
  have hβ := beta_pos hα1
  have he0 : 0 < ‖e‖ := hab ▸ hD
  have hf1 : ‖f‖ = 1 := by rw [hf, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ he0.ne']
  have hFm : Measurable F := (stronglyMeasurable_const.inner hφ).measurable
  have hFb : ∀ x, |F x| ≤ κ := fun x =>
    (abs_real_inner_le_norm _ _).trans (by rw [hf1, one_mul]; exact hκ x)
  have hinv : 0 < ‖e‖⁻¹ := inv_pos.2 he0
  -- first-order optimality on the two convex regions
  have hA : ∀ a' ∈ region φ α P, ⟪f, a⟫_ℝ ≤ ⟪f, a'⟫_ℝ := by
    intro a' ha'
    have h0 : 0 ≤ ⟪e, a' - a⟫_ℝ := inner_nonneg_of_norm_le fun s hs0 hs1 => by
      have hmem : (1 - s) • a + s • a' ∈ region φ α P :=
        region_convex P hφ hκ ha ha' (by linarith) hs0.le (by ring)
      have h1 : D ≤ ‖(1 - s) • a + s • a' - b‖ := setDist_le_norm hmem hb
      have h2 : (1 - s) • a + s • a' - b = e + s • (a' - a) := by
        rw [he, smul_sub, sub_smul, one_smul]; abel
      rw [h2] at h1
      rw [hab]; exact h1
    have h3 : ⟪f, a' - a⟫_ℝ = ‖e‖⁻¹ * ⟪e, a' - a⟫_ℝ := by rw [hf, real_inner_smul_left]
    rw [inner_sub_right] at h3
    nlinarith [mul_nonneg hinv.le h0]
  have hB : ∀ b' ∈ region φ α Q, ⟪f, b'⟫_ℝ ≤ ⟪f, b⟫_ℝ := by
    intro b' hb'
    have h0 : 0 ≤ ⟪e, b - b'⟫_ℝ := inner_nonneg_of_norm_le fun s hs0 hs1 => by
      have hmem : (1 - s) • b + s • b' ∈ region φ α Q :=
        region_convex Q hφ hκ hb hb' (by linarith) hs0.le (by ring)
      have h1 : D ≤ ‖a - ((1 - s) • b + s • b')‖ := setDist_le_norm ha hmem
      have h2 : a - ((1 - s) • b + s • b') = e + s • (b - b') := by
        rw [he, smul_sub, sub_smul, one_smul]; abel
      rw [h2] at h1
      rw [hab]; exact h1
    have h3 : ⟪f, b - b'⟫_ℝ = ‖e‖⁻¹ * ⟪e, b - b'⟫_ℝ := by rw [hf, real_inner_smul_left]
    rw [inner_sub_right] at h3
    nlinarith [mul_nonneg hinv.le h0]
  have hInf : ⟪f, a⟫_ℝ ≤ trimInf P α F := le_trimInf_of P hφ hκ hα0 hα1 f hA
  have hSup : trimSup Q α F ≤ ⟪f, b⟫_ℝ := trimSup_le_of Q hφ hκ hα0 hα1 f hB
  have hfe : ⟪f, a⟫_ℝ - ⟪f, b⟫_ℝ = ‖e‖ := by
    rw [← inner_sub_right, ← he, hf, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hatt := (StatFormal.Wave30tq.lem1_attain 𝒳 P Q α F hFm ⟨κ, hFb⟩ hα0 hα1).2.2 t u ht.1 hu.1
  have hθ : D ≤ theta P Q α F t u := by rw [hatt]; linarith
  have hθle := theta_le_sub P Q hα1 hFm hFb t u
  have hDtu : D ≤ t - u := hθ.trans hθle
  have hut : u < t := by linarith
  -- the extreme quantiles lie in the range of `F`
  have : Nonempty 𝒳 := nonempty_of_isProbabilityMeasure P
  have hbddA : BddAbove (range F) := ⟨κ, by rintro _ ⟨x, rfl⟩; exact (abs_le.1 (hFb x)).2⟩
  have hbddB : BddBelow (range F) := ⟨-κ, by rintro _ ⟨x, rfl⟩; exact (abs_le.1 (hFb x)).1⟩
  have ht_le : t ≤ ⨆ x, F x := by
    by_contra hlt
    push Not at hlt
    have hall : {x | F x < t} = univ := eq_univ_of_forall fun x => (le_ciSup hbddA x).trans_lt hlt
    have h1 := ht.1.1
    rw [hall, probReal_univ] at h1
    have hSq : IsQuantileAt P F (1 - α) (⨆ x, F x) := by
      refine ⟨measureReal_le_one.trans h1, ?_⟩
      have : {x | F x ≤ ⨆ x, F x} = univ := eq_univ_of_forall fun x => le_ciSup hbddA x
      rw [this, probReal_univ]; linarith
    exact absurd (ht.2 hSq) (not_le.2 hlt)
  have hu_ge : ⨅ x, F x ≤ u := by
    by_contra hlt
    push Not at hlt
    have hempty : {x | F x ≤ u} = ∅ :=
      eq_empty_of_forall_notMem fun x hx => absurd (hlt.trans_le (ciInf_le hbddB x)) (not_lt.2 hx)
    have h2 := hu.1.2
    rw [hempty, measureReal_empty] at h2
    have hIq : IsQuantileAt Q F α (⨅ x, F x) := by
      refine ⟨?_, ?_⟩
      · have : {x | F x < ⨅ x, F x} = ∅ :=
          eq_empty_of_forall_notMem fun x hx => absurd (ciInf_le hbddB x) (not_le.2 hx)
        rw [this, measureReal_empty]; exact hα0
      · exact h2.trans measureReal_nonneg
    exact absurd (hu.2 hIq) (not_le.2 hlt)
  have hosc : ∀ x x', F x - F x' ≤ Dφ := fun x x' => by
    have h1 : F x - F x' = ⟪f, φ x - φ x'⟫_ℝ := by simp only [hFdef, inner_sub_right]
    rw [h1]
    exact (real_inner_le_norm _ _).trans (by rw [hf1, one_mul]; exact hDφ x x')
  have hSI : (⨆ x, F x) ≤ (⨅ x, F x) + Dφ := ciSup_le fun x => by
    have : F x - Dφ ≤ ⨅ x, F x := le_ciInf fun x' => by linarith [hosc x x']
    linarith
  have htuD : t - u ≤ Dφ := by linarith
  have hex := excess_of_theta P Q hα0 hα1 hFm hFb hut hθ
  refine ⟨hDtu, htuD, hex, ?_⟩
  exact div_le_div_of_nonneg_left hD.le (mul_pos hβ (sub_pos.2 hut))
    (mul_le_mul_of_nonneg_left htuD hβ.le)

/-! ### Under (A3), TV = sup over ramps -/

theorem ramp_tv_route : StatFormal.Wave30tz.Claims.ramp_tv := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ hφ hκ hchar
  constructor
  · rintro r ⟨f, t, u, -, hut, rfl⟩
    exact (StatFormal.Wave30tv.lem_ramp_iii 𝒳 P Q _ t u
      (stronglyMeasurable_const.inner hφ).measurable hut).2.2
  · intro M hM
    by_contra hlt
    push Not at hlt
    have h0 : (0 : ℝ) ∈ {r : ℝ | ∃ (f : H) (t u : ℝ), ‖f‖ ≤ 1 ∧ u < t ∧
        r = (∫ x, ramp (fun z => ⟪f, φ z⟫_ℝ) t u x ∂P) - ∫ y, ramp (fun z => ⟪f, φ z⟫_ℝ) t u y ∂Q} :=
      ⟨0, 1, 0, by simp, one_pos, by simp [ramp, clip]⟩
    have hM0 : 0 ≤ M := hM h0
    have hM1 : M < 1 := hlt.trans_le StatFormal.Distances.tvDist_le_one
    have hDne : Dpop φ P Q M ≠ 0 := fun h =>
      absurd ((StatFormal.TrimmedMMD.ZeroSet.zeroeq 𝒳 H P Q φ κ M hφ hκ hchar hM0 hM1).1 h) (not_le.2 hlt)
    have hDpos : 0 < Dpop φ P Q M :=
      lt_of_le_of_ne (StatFormal.Wave30tr.setDist_nonneg _ _) (Ne.symm hDne)
    obtain ⟨f, hf1, hsep⟩ := exists_sep_dir P Q hφ hκ hM0 hM1
    set F : 𝒳 → ℝ := fun z => ⟪f, φ z⟫_ℝ with hFdef
    have hFm : Measurable F := (stronglyMeasurable_const.inner hφ).measurable
    have hFb : ∀ x, |F x| ≤ κ := fun x => (abs_real_inner_le_norm _ _).trans (by
      calc ‖f‖ * ‖φ x‖ ≤ 1 * κ := mul_le_mul hf1 (hκ x) (norm_nonneg _) zero_le_one
        _ = κ := one_mul κ)
    have hgap : Dpop φ P Q M ≤ trimInf P M F - trimSup Q M F := trim_gap P Q hφ hκ hM0 hM1 f hsep
    have hatt := StatFormal.Wave30tq.lem1_attain 𝒳 P Q M F hFm ⟨κ, hFb⟩ hM0 hM1
    obtain ⟨q, q', hq, hq'⟩ := hatt.2.1
    have hθ := hatt.2.2 q q' hq hq'
    have hθle := theta_le_sub P Q hM1 hFm hFb q q'
    have hqq : q' < q := by linarith
    have hex := excess_of_theta P Q hM0 hM1 hFm hFb hqq (d := Dpop φ P Q M) (by rw [hθ]; exact hgap)
    have hpos : 0 < Dpop φ P Q M / (beta M * (q - q')) :=
      div_pos hDpos (mul_pos (beta_pos hM1) (sub_pos.2 hqq))
    have hmem := hM ⟨f, q, q', hf1, hqq, rfl⟩
    linarith

end StatFormal.Wave30tz
