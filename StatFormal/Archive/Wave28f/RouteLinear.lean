import StatFormal.Archive.Wave28f.RouteHessian

/-!
# Route — ICL `thm:score`, Step 2: the linearisation `eq:e-linear` (untrusted)

At `θ⋆`, the explicit gradient `gE = jF1(V, V', c, c', cv', f, f')` of `J^iid_{n,m}` is a smooth function of
* the two-sample V-statistics `V`, `V'` of degree `(1, M)` with bounded kernels (`isAL_vstat2`: Hoeffding);
* the pool averages `c = P_n s`, `c' = P_n s'`, `f = P_n(s log s)`, `f' = P_n (s log s)'` (`isAL_poolAvg`);
* the coverage term `m^{−1} Σ_i P_n(s' K(z̃_i, ·))/P_n(s K(z̃_i, ·))` (`isAL_ratio2`);
and of the deterministic penalties `λ_{·,n}` with `√n(λ_{·,n} − λ_·) → 0` (`IsAL.seq_mul`). The delta method
(`IsAL.mul`, `IsAL.inv`, `IsAL.div`) gives `IsAL` with centre `D1(θ⋆) = J'(θ⋆) = 0` (local minimum).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal Real

namespace StatFormal.Wave28f

open StatFormal.Foundations.CLT StatFormal.Wave28b

section Linear
variable {Z Ω : Type} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {P0 : Measure Z} [IsProbabilityMeasure P0] {M : ℕ}
  {X Y : ℕ → Ω → Z} {m : ℕ → ℕ} {κ : ℝ}

lemma bound_of_continuous_compact {W : Type*} [TopologicalSpace W] [CompactSpace W] {f : W → ℝ} (hf : Continuous f) :
    ∃ C, 0 ≤ C ∧ ∀ w, |f w| ≤ C := bound_of_compact hf

/-- The gradient at `θ⋆` is asymptotically linear with centre `D1(θ⋆)`. -/
theorem isAL_gE (hS : TwoSampleIID P P0 X Y m κ) (hM : 1 ≤ M) {s s1 : ℝ → Z → ℝ} {L : Z → (Fin M → Z) → ℝ}
    {K : Z → Z → ℝ} {θs δ sm Kmin lc lK : ℝ} {lcn lKn : ℕ → ℝ} (hδ : 0 < δ) (hsm : 0 < sm)
    (hsb : ∀ t w, sm ≤ s t w) (hKm : 0 < Kmin) (hKb : ∀ z w, Kmin ≤ K z w) (hK : Continuous (Function.uncurry K))
    (hL : Continuous (Function.uncurry L))
    (hs : ContinuousOn (Function.uncurry s) (Metric.ball θs δ ×ˢ univ))
    (hs1 : ContinuousOn (Function.uncurry s1) (Metric.ball θs δ ×ˢ univ))
    (hlc : Tendsto lcn atTop (𝓝 lc)) (hlK : Tendsto lKn atTop (𝓝 lK))
    (hslc : Tendsto (fun n : ℕ => √(n : ℝ) * (lcn n - lc)) atTop (𝓝 0))
    (hslK : Tendsto (fun n : ℕ => √(n : ℝ) * (lKn n - lK)) atTop (𝓝 0)) :
    IsAL P P0 X Y m (fun n ω => gE M s s1 L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) θs)
      (D1 M P0 s s1 L K lc lK θs) := by
  have hθ : θs ∈ Metric.ball θs δ := Metric.mem_ball_self hδ
  have hpos : ∀ t w, 0 < s t w := fun t w => hsm.trans_le (hsb t w)
  have hsl0 := continuousOn_sl0 hs hpos
  have hsl1 := continuousOn_sl1 hs hs1 hpos
  have hpr0 := continuousOn_pr0 (M := M) hs
  have hpr1 := continuousOn_pr1 (M := M) hs hs1
  -- continuity at `θ⋆`
  have cw : ∀ {W : Type} [TopologicalSpace W] {φ : ℝ → W → ℝ},
      ContinuousOn (Function.uncurry φ) (Metric.ball θs δ ×ˢ univ) → Continuous (φ θs) := by
    intro W _ φ hφ
    exact hφ.comp_continuous ((continuous_const (y := θs)).prodMk continuous_id) fun w => ⟨hθ, mem_univ _⟩
  have hsc := cw hs
  have hs1c := cw hs1
  have hsl0c := cw hsl0
  have hsl1c := cw hsl1
  have hpr0c := cw hpr0
  have hpr1c := cw hpr1
  obtain ⟨Cs, hCs0, hCs⟩ := bound_of_compact hsc
  obtain ⟨Cs1, hCs10, hCs1⟩ := bound_of_compact hs1c
  obtain ⟨Cf0, -, hCf0⟩ := bound_of_compact hsl0c
  obtain ⟨Cf1, -, hCf1⟩ := bound_of_compact hsl1c
  obtain ⟨Cp0, hCp00, hCp0⟩ := bound_of_compact hpr0c
  obtain ⟨Cp1, hCp10, hCp1⟩ := bound_of_compact hpr1c
  obtain ⟨CL, hCL0, hCL⟩ := bound_of_compact hL
  obtain ⟨CK, hCK0, hCK⟩ := bound_of_compact hK
  -- the pieces
  have hc0 : IsAL P P0 X Y m (fun n ω => cE s (fun i => X i ω) n θs) (cP P0 s θs) :=
    (isAL_poolAvg hsc.measurable hCs).congr (Eventually.of_forall fun n ω => (cE_eq_empAvg _ _ _ _).symm)
  have hc1 : IsAL P P0 X Y m (fun n ω => cE s1 (fun i => X i ω) n θs) (cP P0 s1 θs) :=
    (isAL_poolAvg hs1c.measurable hCs1).congr (Eventually.of_forall fun n ω => (cE_eq_empAvg _ _ _ _).symm)
  have hf0 : IsAL P P0 X Y m (fun n ω => cE (sl0 s) (fun i => X i ω) n θs) (cP P0 (sl0 s) θs) :=
    (isAL_poolAvg hsl0c.measurable hCf0).congr (Eventually.of_forall fun n ω => (cE_eq_empAvg _ _ _ _).symm)
  have hf1 : IsAL P P0 X Y m (fun n ω => cE (sl1 s s1) (fun i => X i ω) n θs) (cP P0 (sl1 s s1) θs) :=
    (isAL_poolAvg hsl1c.measurable hCf1).congr (Eventually.of_forall fun n ω => (cE_eq_empAvg _ _ _ _).symm)
  have hVgen : ∀ (pr : ℝ → (Fin M → Z) → ℝ) (Cp : ℝ), 0 ≤ Cp → Continuous (pr θs) → (∀ t, |pr θs t| ≤ Cp) →
      IsAL P P0 X Y m (fun n ω => VE pr L (fun i => X i ω) (fun i => Y i ω) n (m n) θs) (VP P0 pr L θs) := by
    intro pr Cp hCp0 hprc hCp
    have hk : Measurable (Function.uncurry fun (y : Z) (t : Fin M → Z) => pr θs t * L y t) :=
      ((hprc.comp continuous_snd).mul hL).measurable
    refine (isAL_vstat2 hS hM hk (mul_nonneg hCp0 hCL0) fun y t => ?_).congr (Eventually.of_forall fun n ω => ?_)
    · rw [abs_mul]; exact mul_le_mul (hCp t) (hCL (y, t)) (abs_nonneg _) hCp0
    · unfold VE
      rw [Fin.sum_univ_eq_sum_range (fun i => vstat (fun t => pr θs t * L (Y i ω) t) (fun j : Fin n => X j ω))]
  have hV0 := hVgen (pr0 s) Cp0 hCp00 hpr0c hCp0
  have hV1 := hVgen (pr1 s s1) Cp1 hCp10 hpr1c hCp1
  -- the coverage term
  have hA : IsAL P P0 X Y m (fun n ω => (m n : ℝ)⁻¹ * ∑ i : Fin (m n),
      lD1 (eE s K (fun l => X l ω) n θs (Y i ω)) (eE s1 K (fun l => X l ω) n θs (Y i ω)))
      (∫ y, lD1 (eP P0 s K θs y) (eP P0 s1 K θs y) ∂P0) := by
    have ha : Measurable (Function.uncurry fun (y x : Z) => s θs x * K y x) :=
      ((hsc.comp continuous_snd).mul (hK)).measurable
    have hb : Measurable (Function.uncurry fun (y x : Z) => s1 θs x * K y x) :=
      ((hs1c.comp continuous_snd).mul (hK)).measurable
    have hab' : ∀ y x, sm * Kmin ≤ s θs x * K y x ∧ s θs x * K y x ≤ Cs * CK + Cs1 * CK := fun y x =>
      ⟨mul_le_mul (hsb θs x) (hKb y x) hKm.le (hpos θs x).le,
        (le_abs_self _).trans (by
          rw [abs_mul]
          have h1 : |s θs x| * |K y x| ≤ Cs * CK := mul_le_mul (hCs x) (hCK (y, x)) (abs_nonneg _) hCs0
          nlinarith [mul_nonneg hCs10 hCK0])⟩
    have hbb : ∀ y x, |s1 θs x * K y x| ≤ Cs * CK + Cs1 * CK := fun y x => by
      rw [abs_mul]
      have h1 : |s1 θs x| * |K y x| ≤ Cs1 * CK := mul_le_mul (hCs1 x) (hCK (y, x)) (abs_nonneg _) hCs10
      nlinarith [mul_nonneg hCs0 hCK0]
    refine (isAL_ratio2 hS ha hb (mul_pos hsm hKm) hab' hbb).congr (Eventually.of_forall fun n ω => ?_)
    rw [← Fin.sum_univ_eq_sum_range]
    rfl
  have hc0pos : 0 < cP P0 s θs := by
    have h := integral_mono (μ := P0) (integrable_const sm)
      (StatFormal.Wave24c.integrable_of_continuous' hsc) (fun w => hsb θs w)
    have : sm ≤ cP P0 s θs := by simpa [cP] using h
    linarith
  have hc0ne := hc0pos.ne'
  -- the formula
  have hcv : IsAL P P0 X Y m (fun n ω => cv1 s s1 K (fun i => X i ω) (fun i => Y i ω) n (m n) θs)
      (cvP1 P0 s s1 K θs) := by
    refine (hA.sub (hc1.div hS hc0ne hc0)).congr ?_
    filter_upwards [(tendsto_atTop_of_ratio hS.hκ hS.hm).eventually_ge_atTop 1] with n hn ω
    rw [cv1_eq s s1 K _ _ n hn θs]
    rfl
  have hz0 : IsAL P P0 X Y m (fun n ω => zI M 0 (cE s (fun i => X i ω) n θs)) (zI M 0 (cP P0 s θs)) :=
    (hc0.pow hS (M + 0)).inv hS (pow_ne_zero _ hc0ne)
  have hz1 : IsAL P P0 X Y m (fun n ω => zI M 1 (cE s (fun i => X i ω) n θs)) (zI M 1 (cP P0 s θs)) :=
    (hc0.pow hS (M + 1)).inv hS (pow_ne_zero _ hc0ne)
  have hzD : IsAL P P0 X Y m (fun n ω => zD1 M (VE (pr0 s) L (fun i => X i ω) (fun i => Y i ω) n (m n) θs)
      (VE (pr1 s s1) L (fun i => X i ω) (fun i => Y i ω) n (m n) θs) (cE s (fun i => X i ω) n θs)
      (cE s1 (fun i => X i ω) n θs))
      (zD1 M (VP P0 (pr0 s) L θs) (VP P0 (pr1 s s1) L θs) (cP P0 s θs) (cP P0 s1 θs)) :=
    (hV1.mul hS hz0).add (hV0.mul hS (((hz1.const_mul (-(M : ℝ))).mul hS hc1)))
  have hl : IsAL P P0 X Y m (fun n ω => lD1 (cE s (fun i => X i ω) n θs) (cE s1 (fun i => X i ω) n θs))
      (lD1 (cP P0 s θs) (cP P0 s1 θs)) := hc1.div hS hc0ne hc0
  have hq : IsAL P P0 X Y m (fun n ω => qD1 (cE (sl0 s) (fun i => X i ω) n θs) (cE (sl1 s s1) (fun i => X i ω) n θs)
      (cE s (fun i => X i ω) n θs) (cE s1 (fun i => X i ω) n θs))
      (qD1 (cP P0 (sl0 s) θs) (cP P0 (sl1 s s1) θs) (cP P0 s θs) (cP P0 s1 θs)) :=
    ((hf1.mul hS hc0).sub (hf0.mul hS hc1)).div hS (pow_ne_zero 2 hc0ne) (hc0.pow hS 2)
  exact (hzD.add (hcv.neg.seq_mul hS hlc hslc)).add ((hq.sub hl).seq_mul hS hlK hslK)

end Linear

theorem score_linearization : Claims.score_linearization := by
  intro M sm sp Kmin Kmax κ lc lK θs δ Z Ω _ _ _ _ _ P _ P0 X Y m s s1 s2 L K lcn lKn hM hsm hsb hδ hs hs1 hs2 hsd
    hL hK hKmin hKb hXm hYm hXi hYi hXY hXl hYl hκ hmκ hlc hlK hslc hslK hmin
  have hP0 : IsProbabilityMeasure P0 := by
    rw [← hXl 0]; exact (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).2 inferInstance
  have hS : TwoSampleIID P P0 X Y m κ := ⟨hXm, hYm, hXi, hYi, hXY, hXl, hYl, hκ, hmκ⟩
  have hm := tendsto_atTop_of_ratio hκ hmκ
  have hθ : θs ∈ Metric.ball θs δ := Metric.mem_ball_self hδ
  have hsm' : ∀ θ w, sm ≤ s θ w := fun θ w => (hsb θ w).1
  have hAL := isAL_gE hS hM hδ hsm hsm' hKmin (fun z w => (hKb z w).1) hK hL hs hs1 hlc hlK hslc hslK
  have hpop := pop_derivs (P := P) (P0 := P0) (X := X) (Y := Y) (lcn := lcn) (lKn := lKn) hM hsm hsb hs hs1 hs2
    hsd hL hK hKmin hKb hXm hXi hXl hYm hYi hYl hm hlc hlK θs hθ
  have hloc : IsLocalMin (jPop P0 s L K lc lK) θs := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hθ] with t ht
    exact hmin t ht
  have hD0 : D1 M P0 s s1 L K lc lK θs = 0 := hloc.hasDerivAt_eq_zero hpop.1
  obtain ⟨α, β, ⟨hαm, ⟨Cα, hCα⟩, hα0⟩, ⟨hβm, ⟨Cβ, hCβ⟩, hβ0⟩, hres⟩ := hAL
  refine ⟨fun n ω => (Jiid_derivs hM hsm hsm' hsd hKmin (fun z w => (hKb z w).1) (L := L) _ _ n (m n) (lcn n)
    (lKn n) θs hθ).2.1, α, β, hαm, hβm, ⟨max Cα Cβ, fun z => ⟨(hCα z).trans (le_max_left _ _),
    (hCβ z).trans (le_max_right _ _)⟩⟩, hα0, hβ0, ?_⟩
  rw [tip0_iff]
  refine hres.congr ?_
  filter_upwards [eventually_ge_atTop 1] with n hn ω
  rw [hD0, sub_zero, ((Jiid_derivs hM hsm hsm' hsd hKmin (fun z w => (hKb z w).1) (L := L) _ _ n (m n) (lcn n)
    (lKn n) θs hθ).1 hn).1]
  rfl

end StatFormal.Wave28f
