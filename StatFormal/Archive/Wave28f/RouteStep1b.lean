import StatFormal.Archive.Wave28f.RouteStep1

/-!
# Route — Step 1 of ICL `thm:score`: the uniform law for the first two derivatives (untrusted)

Almost surely, on every closed ball `B̄(θ⋆, r) ⊆ U`, the explicit first and second derivatives `gE`, `hE` of
`J^iid_{n,m}` converge uniformly to their population counterparts `D1`, `D2` (`tu_gE_hE`): the derivative pieces
converge uniformly (route `RouteStep1`) and the outer formulas `jF1`, `jF2` are continuous on the region
`{c ≥ s₋}` (`tuOn_map`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal Real

namespace StatFormal.Wave28f

open StatFormal.Foundations.CLT

/-! ### Continuity of the outer formulas -/

lemma continuousOn_jF1 (M : ℕ) {sm : ℝ} (hsm : 0 < sm) :
    ContinuousOn (fun v : Fin 9 → ℝ => jF1 M (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6 - lD1 (v 4) (v 5)) (v 7) (v 8))
      {v | sm ≤ v 4} := by
  have h : ContinuousOn (fun v : Fin 9 → ℝ => jF1 M (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6 - lD1 (v 4) (v 5))
      (v 7) (v 8)) {v | v 4 ≠ 0} := by
    unfold jF1 zD1 qD1 lD1 zI
    fun_prop (disch := (intro x hx; simp_all))
  exact h.mono fun v hv => (hsm.trans_le hv).ne'

lemma continuousOn_jF2 (M : ℕ) {sm : ℝ} (hsm : 0 < sm) :
    ContinuousOn (fun v : Fin 12 → ℝ => jF2 M (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
      (v 8 - lD2 (v 5) (v 6) (v 7)) (v 9) (v 10) (v 11)) {v | sm ≤ v 5} := by
  have h : ContinuousOn (fun v : Fin 12 → ℝ => jF2 M (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
      (v 8 - lD2 (v 5) (v 6) (v 7)) (v 9) (v 10) (v 11)) {v | v 5 ≠ 0} := by
    unfold jF2 zD2 qD2 lD2 zI
    fun_prop (disch := (intro x hx; simp_all))
  exact h.mono fun v hv => (hsm.trans_le hv).ne'

lemma continuousOn_lD1v {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun v : Fin 2 → ℝ => lD1 (v 0) (v 1)) {v | a ≤ v 0} := by
  have h : ContinuousOn (fun v : Fin 2 → ℝ => lD1 (v 0) (v 1)) {v | v 0 ≠ 0} := by
    unfold lD1
    fun_prop (disch := (intro x hx; simp_all))
  exact h.mono fun v hv => (ha.trans_le hv).ne'

lemma continuousOn_lD2v {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun v : Fin 3 → ℝ => lD2 (v 0) (v 1) (v 2)) {v | a ≤ v 0} := by
  have h : ContinuousOn (fun v : Fin 3 → ℝ => lD2 (v 0) (v 1) (v 2)) {v | v 0 ≠ 0} := by
    unfold lD2
    fun_prop (disch := (intro x hx; simp_all))
  exact h.mono fun v hv => (ha.trans_le hv).ne'

lemma cv1_eq {Z : Type*} (s s1 : ℝ → Z → ℝ) (K : Z → Z → ℝ) (x y : ℕ → Z) (n : ℕ) {m : ℕ} (hm : 1 ≤ m) (θ : ℝ) :
    cv1 s s1 K x y n m θ = (m : ℝ)⁻¹ * ∑ i : Fin m, lD1 (eE s K x n θ (y i)) (eE s1 K x n θ (y i)) -
      lD1 (cE s x n θ) (cE s1 x n θ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold cv1
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sub]
  field_simp

lemma cv2_eq {Z : Type*} (s s1 s2 : ℝ → Z → ℝ) (K : Z → Z → ℝ) (x y : ℕ → Z) (n : ℕ) {m : ℕ} (hm : 1 ≤ m)
    (θ : ℝ) :
    cv2 s s1 s2 K x y n m θ = (m : ℝ)⁻¹ * ∑ i : Fin m, lD2 (eE s K x n θ (y i)) (eE s1 K x n θ (y i))
      (eE s2 K x n θ (y i)) - lD2 (cE s x n θ) (cE s1 x n θ) (cE s2 x n θ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold cv2
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sub]
  field_simp

section Main
variable {Z Ω : Type} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {P0 : Measure Z} [IsProbabilityMeasure P0] {X Y : ℕ → Ω → Z}

/-- Step 1: almost surely, the first two derivatives of `J^iid_{n,m}` converge uniformly on every closed ball
inside `U` to the population formulas `D1`, `D2`. -/
theorem tu_gE_hE (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P) (hXl : ∀ i, P.map (X i) = P0)
    (hYm : ∀ i, Measurable (Y i)) (hYi : iIndepFun Y P) (hYl : ∀ i, P.map (Y i) = P0) {M : ℕ} (hM : 1 ≤ M)
    {s s1 s2 : ℝ → Z → ℝ} {L : Z → (Fin M → Z) → ℝ} {K : Z → Z → ℝ} {θs δ r sm Kmin lc lK : ℝ}
    {lcn lKn : ℕ → ℝ} {m : ℕ → ℕ} (hsm : 0 < sm) (hsb : ∀ t w, sm ≤ s t w) (hKm : 0 < Kmin)
    (hKb : ∀ z w, Kmin ≤ K z w) (hK : Continuous (Function.uncurry K)) (hL : Continuous (Function.uncurry L))
    (hs : ContinuousOn (Function.uncurry s) (Metric.ball θs δ ×ˢ univ))
    (hs1 : ContinuousOn (Function.uncurry s1) (Metric.ball θs δ ×ˢ univ))
    (hs2 : ContinuousOn (Function.uncurry s2) (Metric.ball θs δ ×ˢ univ)) (hr : r < δ)
    (hm : Tendsto m atTop atTop) (hlc : Tendsto lcn atTop (𝓝 lc)) (hlK : Tendsto lKn atTop (𝓝 lK)) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n θ => gE M s s1 L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n)
        (lKn n) θ) (D1 M P0 s s1 L K lc lK) atTop (Metric.closedBall θs r) ∧
      TendstoUniformlyOn (fun n θ => hE M s s1 s2 L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n)
        (lKn n) θ) (D2 M P0 s s1 s2 L K lc lK) atTop (Metric.closedBall θs r) := by
  set Sb := Metric.closedBall θs r with hSbdef
  have hSb : IsCompact Sb := isCompact_closedBall θs r
  have hsub : Sb ×ˢ (univ : Set Z) ⊆ Metric.ball θs δ ×ˢ univ :=
    prod_mono (Metric.closedBall_subset_ball hr) subset_rfl
  have hs' := hs.mono hsub
  have hs1' := hs1.mono hsub
  have hs2' := hs2.mono hsub
  have hpos : ∀ t w, 0 < s t w := fun t w => hsm.trans_le (hsb t w)
  have hsK : 0 < sm * Kmin := mul_pos hsm hKm
  -- population lower bounds
  have hcont_w : ∀ θ ∈ Sb, Continuous (fun w => s θ w) := fun θ hθ =>
    (continuous_on_sub hs').comp ((continuous_const (y := (⟨θ, hθ⟩ : Sb))).prodMk continuous_id)
  have hcP : ∀ θ ∈ Sb, sm ≤ cP P0 s θ := by
    intro θ hθ
    have h := integral_mono (μ := P0) (integrable_const sm)
      (StatFormal.Wave24c.integrable_of_continuous' (hcont_w θ hθ)) (fun w => hsb θ w)
    simpa [cP] using h
  have hePl : ∀ θ ∈ Sb, ∀ z, sm * Kmin ≤ eP P0 s K θ z := by
    intro θ hθ z
    have hc : Continuous (fun w => s θ w * K z w) :=
      (hcont_w θ hθ).mul (hK.comp ((continuous_const (y := z)).prodMk continuous_id))
    have h := integral_mono (μ := P0) (integrable_const (sm * Kmin))
      (StatFormal.Wave24c.integrable_of_continuous' hc)
      (fun w => mul_le_mul (hsb θ w) (hKb z w) hKm.le (hpos θ w).le)
    simpa [eP] using h
  have hφ2 : ∀ j, ContinuousOn (Function.uncurry ((![s, s1] : Fin 2 → ℝ → Z → ℝ) j)) (Sb ×ˢ univ) := by
    intro j; fin_cases j
    exacts [hs', hs1']
  have hφ3 : ∀ j, ContinuousOn (Function.uncurry ((![s, s1, s2] : Fin 3 → ℝ → Z → ℝ) j)) (Sb ×ˢ univ) := by
    intro j; fin_cases j
    exacts [hs', hs1', hs2']
  have hD2c : IsClosed {v : Fin 2 → ℝ | sm * Kmin ≤ v 0} := isClosed_le continuous_const (continuous_apply 0)
  have hD3c : IsClosed {v : Fin 3 → ℝ | sm * Kmin ≤ v 0} := isClosed_le continuous_const (continuous_apply 0)
  have hDE2 : ∀ᶠ n in atTop, ∀ x : ℕ → Z, ∀ θ ∈ Sb, ∀ z,
      (fun j => eE ((![s, s1] : Fin 2 → ℝ → Z → ℝ) j) K x n θ z) ∈ {v : Fin 2 → ℝ | sm * Kmin ≤ v 0} := by
    filter_upwards [eventually_ge_atTop 1] with n hn x θ _ z
    exact eE_ge hn hsm (hsb θ) hKb hKm z
  have hDE3 : ∀ᶠ n in atTop, ∀ x : ℕ → Z, ∀ θ ∈ Sb, ∀ z,
      (fun j => eE ((![s, s1, s2] : Fin 3 → ℝ → Z → ℝ) j) K x n θ z) ∈ {v : Fin 3 → ℝ | sm * Kmin ≤ v 0} := by
    filter_upwards [eventually_ge_atTop 1] with n hn x θ _ z
    exact eE_ge hn hsm (hsb θ) hKb hKm z
  have hDP2 : ∀ θ ∈ Sb, ∀ z, (fun j => eP P0 ((![s, s1] : Fin 2 → ℝ → Z → ℝ) j) K θ z) ∈
      {v : Fin 2 → ℝ | sm * Kmin ≤ v 0} := fun θ hθ z => hePl θ hθ z
  have hDP3 : ∀ θ ∈ Sb, ∀ z, (fun j => eP P0 ((![s, s1, s2] : Fin 3 → ℝ → Z → ℝ) j) K θ z) ∈
      {v : Fin 3 → ℝ | sm * Kmin ≤ v 0} := fun θ hθ z => hePl θ hθ z
  have hsl0 := continuousOn_sl0 hs' hpos
  have hsl1 := continuousOn_sl1 hs' hs1' hpos
  have hsl2 := continuousOn_sl2 hs' hs1' hs2' hpos
  have hpr0 := continuousOn_pr0 (M := M) hs'
  have hpr1 := continuousOn_pr1 (M := M) hs' hs1'
  have hpr2 := continuousOn_pr2 (M := M) hs' hs1' hs2'
  filter_upwards [tu_cE hXm hXi hXl hSb hs', tu_cE hXm hXi hXl hSb hs1', tu_cE hXm hXi hXl hSb hs2',
    tu_cE hXm hXi hXl hSb hsl0, tu_cE hXm hXi hXl hSb hsl1, tu_cE hXm hXi hXl hSb hsl2,
    tu_VE hXm hXi hXl hYm hYi hYl hM hSb hpr0 hL hm, tu_VE hXm hXi hXl hYm hYi hYl hM hSb hpr1 hL hm,
    tu_VE hXm hXi hXl hYm hYi hYl hM hSb hpr2 hL hm,
    tu_cov hXm hXi hXl hYm hYi hYl hSb hφ2 hK hD2c (continuousOn_lD1v hsK) hDE2 hDP2 hm,
    tu_cov hXm hXi hXl hYm hYi hYl hSb hφ3 hK hD3c (continuousOn_lD2v hsK) hDE3 hDP3 hm]
    with ω hc0 hc1 hc2 hf0 hf1 hf2 hV0 hV1 hV2 hA1 hA2
  constructor
  · set F : ℕ → ℝ → Fin 9 → ℝ := fun n θ => ![lcn n, lKn n, VE (pr0 s) L (fun i => X i ω) (fun i => Y i ω) n (m n) θ,
      VE (pr1 s s1) L (fun i => X i ω) (fun i => Y i ω) n (m n) θ, cE s (fun i => X i ω) n θ,
      cE s1 (fun i => X i ω) n θ, (m n : ℝ)⁻¹ * ∑ i : Fin (m n),
        lD1 (eE s K (fun l => X l ω) n θ (Y i ω)) (eE s1 K (fun l => X l ω) n θ (Y i ω)),
      cE (sl0 s) (fun i => X i ω) n θ, cE (sl1 s s1) (fun i => X i ω) n θ] with hF
    set f : ℝ → Fin 9 → ℝ := fun θ => ![lc, lK, VP P0 (pr0 s) L θ, VP P0 (pr1 s s1) L θ, cP P0 s θ, cP P0 s1 θ,
      ∫ y, lD1 (eP P0 s K θ y) (eP P0 s1 K θ y) ∂P0, cP P0 (sl0 s) θ, cP P0 (sl1 s s1) θ] with hf
    have hFf : TendstoUniformlyOn F f atTop Sb := by
      refine tuOn_pi fun i => ?_
      fin_cases i
      exacts [tuOn_const_seq hlc _, tuOn_const_seq hlK _, hV0, hV1, hc0, hc1, hA1, hf0, hf1]
    have hfc : Continuous (fun a : Sb => f a) := by
      refine continuous_pi fun i => ?_
      fin_cases i
      exacts [continuous_const, continuous_const, continuous_VP hSb hpr0 hL, continuous_VP hSb hpr1 hL,
        continuous_cP hSb hs', continuous_cP hSb hs1',
        continuous_covLim hSb hφ2 hK (continuousOn_lD1v hsK) hDP2, continuous_cP hSb hsl0, continuous_cP hSb hsl1]
    obtain ⟨R, hR⟩ := bound_on_of_continuous hSb hfc
    have hmap := tuOn_map hFf (isClosed_le continuous_const (continuous_apply 4)) (continuousOn_jF1 M hsm)
      (fun θ hθ => hcP θ hθ) ((eventually_ge_atTop 1).mono fun n hn θ _ => show sm ≤ cE s (fun i => X i ω) n θ from cE_ge hn (hsb θ)) hR
    refine hmap.congr_eventually ?_ fun θ _ => rfl
    filter_upwards [hm.eventually_ge_atTop 1] with n hmn θ _
    show jF1 M (lcn n) (lKn n) _ _ _ _ _ _ _ = gE M s s1 L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) θ
    unfold gE
    rw [cv1_eq s s1 K _ _ n hmn θ]
    rfl
  · set F : ℕ → ℝ → Fin 12 → ℝ := fun n θ => ![lcn n, lKn n,
      VE (pr0 s) L (fun i => X i ω) (fun i => Y i ω) n (m n) θ,
      VE (pr1 s s1) L (fun i => X i ω) (fun i => Y i ω) n (m n) θ,
      VE (pr2 s s1 s2) L (fun i => X i ω) (fun i => Y i ω) n (m n) θ, cE s (fun i => X i ω) n θ,
      cE s1 (fun i => X i ω) n θ, cE s2 (fun i => X i ω) n θ, (m n : ℝ)⁻¹ * ∑ i : Fin (m n),
        lD2 (eE s K (fun l => X l ω) n θ (Y i ω)) (eE s1 K (fun l => X l ω) n θ (Y i ω))
          (eE s2 K (fun l => X l ω) n θ (Y i ω)),
      cE (sl0 s) (fun i => X i ω) n θ, cE (sl1 s s1) (fun i => X i ω) n θ,
      cE (sl2 s s1 s2) (fun i => X i ω) n θ] with hF
    set f : ℝ → Fin 12 → ℝ := fun θ => ![lc, lK, VP P0 (pr0 s) L θ, VP P0 (pr1 s s1) L θ,
      VP P0 (pr2 s s1 s2) L θ, cP P0 s θ, cP P0 s1 θ, cP P0 s2 θ,
      ∫ y, lD2 (eP P0 s K θ y) (eP P0 s1 K θ y) (eP P0 s2 K θ y) ∂P0, cP P0 (sl0 s) θ, cP P0 (sl1 s s1) θ,
      cP P0 (sl2 s s1 s2) θ] with hf
    have hFf : TendstoUniformlyOn F f atTop Sb := by
      refine tuOn_pi fun i => ?_
      fin_cases i
      exacts [tuOn_const_seq hlc _, tuOn_const_seq hlK _, hV0, hV1, hV2, hc0, hc1, hc2, hA2, hf0, hf1, hf2]
    have hfc : Continuous (fun a : Sb => f a) := by
      refine continuous_pi fun i => ?_
      fin_cases i
      exacts [continuous_const, continuous_const, continuous_VP hSb hpr0 hL, continuous_VP hSb hpr1 hL,
        continuous_VP hSb hpr2 hL, continuous_cP hSb hs', continuous_cP hSb hs1', continuous_cP hSb hs2',
        continuous_covLim hSb hφ3 hK (continuousOn_lD2v hsK) hDP3, continuous_cP hSb hsl0, continuous_cP hSb hsl1,
        continuous_cP hSb hsl2]
    obtain ⟨R, hR⟩ := bound_on_of_continuous hSb hfc
    have hmap := tuOn_map hFf (isClosed_le continuous_const (continuous_apply 5)) (continuousOn_jF2 M hsm)
      (fun θ hθ => hcP θ hθ) ((eventually_ge_atTop 1).mono fun n hn θ _ => show sm ≤ cE s (fun i => X i ω) n θ from cE_ge hn (hsb θ)) hR
    refine hmap.congr_eventually ?_ fun θ _ => rfl
    filter_upwards [hm.eventually_ge_atTop 1] with n hmn θ _
    show jF2 M (lcn n) (lKn n) _ _ _ _ _ _ _ _ _ _ =
      hE M s s1 s2 L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) θ
    unfold hE
    rw [cv2_eq s s1 s2 K _ _ n hmn θ]
    rfl

/-- The population second derivative is continuous on compact sub-balls. -/
theorem continuousOn_D2 {M : ℕ} {s s1 s2 : ℝ → Z → ℝ} {L : Z → (Fin M → Z) → ℝ} {K : Z → Z → ℝ}
    {θs δ r sm Kmin lc lK : ℝ} (hsm : 0 < sm) (hsb : ∀ t w, sm ≤ s t w) (hKm : 0 < Kmin)
    (hKb : ∀ z w, Kmin ≤ K z w) (hK : Continuous (Function.uncurry K)) (hL : Continuous (Function.uncurry L))
    (hs : ContinuousOn (Function.uncurry s) (Metric.ball θs δ ×ˢ univ))
    (hs1 : ContinuousOn (Function.uncurry s1) (Metric.ball θs δ ×ˢ univ))
    (hs2 : ContinuousOn (Function.uncurry s2) (Metric.ball θs δ ×ˢ univ)) (hr : r < δ) :
    ContinuousOn (D2 M P0 s s1 s2 L K lc lK) (Metric.closedBall θs r) := by
  set Sb := Metric.closedBall θs r with hSbdef
  have hSb : IsCompact Sb := isCompact_closedBall θs r
  have hsub : Sb ×ˢ (univ : Set Z) ⊆ Metric.ball θs δ ×ˢ univ :=
    prod_mono (Metric.closedBall_subset_ball hr) subset_rfl
  have hs' := hs.mono hsub
  have hs1' := hs1.mono hsub
  have hs2' := hs2.mono hsub
  have hpos : ∀ t w, 0 < s t w := fun t w => hsm.trans_le (hsb t w)
  have hsK : 0 < sm * Kmin := mul_pos hsm hKm
  have hcont_w : ∀ θ ∈ Sb, Continuous (fun w => s θ w) := fun θ hθ =>
    (continuous_on_sub hs').comp ((continuous_const (y := (⟨θ, hθ⟩ : Sb))).prodMk continuous_id)
  have hcP : ∀ θ ∈ Sb, sm ≤ cP P0 s θ := by
    intro θ hθ
    have h := integral_mono (μ := P0) (integrable_const sm)
      (StatFormal.Wave24c.integrable_of_continuous' (hcont_w θ hθ)) (fun w => hsb θ w)
    simpa [cP] using h
  have hePl : ∀ θ ∈ Sb, ∀ z, sm * Kmin ≤ eP P0 s K θ z := by
    intro θ hθ z
    have hc : Continuous (fun w => s θ w * K z w) :=
      (hcont_w θ hθ).mul (hK.comp ((continuous_const (y := z)).prodMk continuous_id))
    have h := integral_mono (μ := P0) (integrable_const (sm * Kmin))
      (StatFormal.Wave24c.integrable_of_continuous' hc)
      (fun w => mul_le_mul (hsb θ w) (hKb z w) hKm.le (hpos θ w).le)
    simpa [eP] using h
  have hφ3 : ∀ j, ContinuousOn (Function.uncurry ((![s, s1, s2] : Fin 3 → ℝ → Z → ℝ) j)) (Sb ×ˢ univ) := by
    intro j; fin_cases j
    exacts [hs', hs1', hs2']
  have hDP3 : ∀ θ ∈ Sb, ∀ z, (fun j => eP P0 ((![s, s1, s2] : Fin 3 → ℝ → Z → ℝ) j) K θ z) ∈
      {v : Fin 3 → ℝ | sm * Kmin ≤ v 0} := fun θ hθ z => hePl θ hθ z
  set f : ℝ → Fin 12 → ℝ := fun θ => ![lc, lK, VP P0 (pr0 s) L θ, VP P0 (pr1 s s1) L θ,
    VP P0 (pr2 s s1 s2) L θ, cP P0 s θ, cP P0 s1 θ, cP P0 s2 θ,
    ∫ y, lD2 (eP P0 s K θ y) (eP P0 s1 K θ y) (eP P0 s2 K θ y) ∂P0, cP P0 (sl0 s) θ, cP P0 (sl1 s s1) θ,
    cP P0 (sl2 s s1 s2) θ] with hf
  have hfc : Continuous (fun a : Sb => f a) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    exacts [continuous_const, continuous_const, continuous_VP hSb (continuousOn_pr0 hs') hL,
      continuous_VP hSb (continuousOn_pr1 hs' hs1') hL, continuous_VP hSb (continuousOn_pr2 hs' hs1' hs2') hL,
      continuous_cP hSb hs', continuous_cP hSb hs1', continuous_cP hSb hs2',
      continuous_covLim hSb hφ3 hK (continuousOn_lD2v hsK) hDP3, continuous_cP hSb (continuousOn_sl0 hs' hpos),
      continuous_cP hSb (continuousOn_sl1 hs' hs1' hpos), continuous_cP hSb (continuousOn_sl2 hs' hs1' hs2' hpos)]
  have hfon : ContinuousOn f Sb := continuousOn_iff_continuous_restrict.2 hfc
  exact (continuousOn_jF2 M hsm).comp hfon fun θ hθ => show sm ≤ cP P0 s θ from hcP θ hθ

end Main

end StatFormal.Wave28f
