import StatFormal.Archive.Wave28f.Statements
import StatFormal.Archive.Wave28f.RouteStep1b
import StatFormal.Archive.Wave28b.RouteConsistency

/-!
# Route — ICL `thm:score`, Step 1: `J ∈ C²(U)` and the Hessian uniform law (untrusted)

* `J^iid_{n,m}` equals the representation `jRep` (`n ≥ 1`) and is the constant `0` at `n = 0`; its derivatives are
  the explicit `gE`, `hE` on `U`.
* Almost surely `J^iid_{n,m} → J` pointwise on compact sub-balls (`jIid_tendsto`: the Wave 28b route of
  `score_argmin_discharged` — certified Wave 24e `e_vstat`, Wave 24c `compactGC_of_iid`, `e_ulln` — on the
  compact parameter set `B̄(θ⋆, r)`).
* With the uniform convergence of `gE`, `hE` (route `RouteStep1b`), `hasDerivAt_of_tendstoUniformlyOn` gives
  `J' = D1`, `J'' = D2` on `U`; `D2` is continuous; the Hessian uniform law follows.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal Real

namespace StatFormal.Wave28f

open StatFormal.Foundations.CLT StatFormal.Wave28b StatFormal.ICL StatFormal.ICL.Cond StatFormal.ICL.Diag
  StatFormal.Wave11b

section Basic
variable {Z : Type*} {M : ℕ}

lemma jScoreIid_zero (hM : 1 ≤ M) (s : ℝ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (x y : ℕ → Z)
    (m : ℕ) (lc lK θ : ℝ) : jScoreIid s L K x y 0 m lc lK θ = 0 := by
  haveI : IsEmpty (Fin M → Fin 0) := ⟨fun f => (f ⟨0, hM⟩).elim0⟩
  unfold jScoreIid jIid klUnif
  simp

variable [MeasurableSpace Z] {s s1 s2 : ℝ → Z → ℝ} {L : Z → (Fin M → Z) → ℝ} {K : Z → Z → ℝ}

lemma hasDerivAt_Jiid {sm Kmin : ℝ} (hsm : 0 < sm) (hsb : ∀ t w, sm ≤ s t w) (hKm : 0 < Kmin)
    (hKb : ∀ z w, Kmin ≤ K z w) {t : ℝ} (hs : ∀ w, HasDerivAt (fun θ => s θ w) (s1 t w) t) (x y : ℕ → Z)
    {n : ℕ} (hn : 1 ≤ n) (m : ℕ) (lc lK : ℝ) :
    HasDerivAt (jScoreIid s L K x y n m lc lK) (gE M s s1 L K x y n m lc lK t) t := by
  have hpos : ∀ θ w, 0 < s θ w := fun θ w => hsm.trans_le (hsb θ w)
  have e : jScoreIid s L K x y n m lc lK = fun θ => jRep M s L K x y n m lc lK θ :=
    funext fun θ => jScoreIid_rep L hpos (fun z w => hKm.trans_le (hKb z w)) x y hn m lc lK θ
  rw [e]
  exact hasDerivAt_jRep hn hsm hs (hsb t) hKb hKm lc lK

end Basic

/-! ### Pointwise convergence of the i.i.d. objective -/

section Conv
variable {Z Ω : Type} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω]

lemma jIid_tendsto {P : Measure Ω} [IsProbabilityMeasure P] {P0 : Measure Z} {M : ℕ} {X Y : ℕ → Ω → Z}
    {m : ℕ → ℕ} {s : ℝ → Z → ℝ} {L : Z → (Fin M → Z) → ℝ} {K : Z → Z → ℝ} {sm sp Kmin Kmax lc lK : ℝ}
    {lcn lKn : ℕ → ℝ} {Sb : Set ℝ} (hSb : IsCompact Sb) (hsc : ContinuousOn (Function.uncurry s) (Sb ×ˢ univ))
    (hsm : 0 < sm) (hsb : ∀ θ z, sm ≤ s θ z ∧ s θ z ≤ sp) (hK : Continuous (Function.uncurry K))
    (hKmin : 0 < Kmin) (hKb : ∀ z z', Kmin ≤ K z z' ∧ K z z' ≤ Kmax) (hL : Continuous (Function.uncurry L))
    (hXm : ∀ j, Measurable (X j)) (hXi : iIndepFun X P) (hXl : ∀ j, P.map (X j) = P0)
    (hYm : ∀ j, Measurable (Y j)) (hYi : iIndepFun Y P) (hYl : ∀ j, P.map (Y j) = P0)
    (hm : Tendsto m atTop atTop) (hlc : Tendsto lcn atTop (𝓝 lc)) (hlK : Tendsto lKn atTop (𝓝 lK)) :
    ∀ᵐ ω ∂P, ∀ t ∈ Sb, Tendsto (fun n => jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n)
      (lKn n) t) atTop (𝓝 (jPop P0 s L K lc lK t)) := by
  have hP0 : IsProbabilityMeasure P0 := by
    rw [← hXl 0]; exact (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).2 inferInstance
  haveI : CompactSpace Sb := isCompact_iff_compactSpace.1 hSb
  set Θ := Sb
  set sT : Θ → Z → ℝ := fun θ z => s θ z with hsTdef
  have hs : Continuous (Function.uncurry sT) := continuous_on_sub hsc
  have hsbT : ∀ θ z, sm ≤ sT θ z ∧ sT θ z ≤ sp := fun θ z => hsb θ z
  have hpos : ∀ θ z, 0 < sT θ z := fun θ z => lt_of_lt_of_le hsm (hsbT θ z).1
  have hLsw : Continuous (Function.uncurry fun (t : Fin M → Z) (z : Z) => L z t) := hL.comp continuous_swap
  have hLbar : Continuous (lossBar P0 L) :=
    StatFormal.Wave24c.continuous_param_integral (P0 := P0) (f := fun t z => L z t) hLsw
  set sQ : Θ × Z → ℝ := fun q => sT q.1 q.2 with hsQ
  set Lb : Θ × (Fin M → Z) → ℝ := fun q => lossBar P0 L q.2 with hLbdef
  have hsQc : Continuous sQ := hs
  have hLbc : Continuous Lb := hLbar.comp continuous_snd
  have hvs := StatFormal.Wave24e.e_vstat Θ Z Ω P P0 M sQ Lb sm sp X hsQc hLbc hsm (fun q => hsbT q.1 q.2)
    hXm hXi hXl
  have hGL := StatFormal.Wave24c.compactGC_of_iid hP0 inferInstance hYm hYi hYl (Fin M → Z) (fun t y => L y t) hLsw
  set Rn : ℕ → Ω → Θ → ℝ := fun n ω θ => (1 / (m n : ℝ)) * ∑ i : Fin (m n), ∑ j : Fin M → Fin n,
      iidLaw (wScore sT (fun i : Fin n => X i ω) θ) M j * L (Y i ω) ((fun i : Fin n => X i ω) ∘ j) with hRn
  have hR : ∀ᵐ ω ∂P, TendstoUniformly (fun n => Rn n ω) (StatFormal.Wave24e.wPop P0 sQ Lb) atTop := by
    filter_upwards [hvs, hGL] with ω h1 h2
    have h2' := StatFormal.Wave24c.tu_comp_tendsto h2 hm
    rw [Metric.tendstoUniformly_iff] at h1 h2' ⊢
    intro ε hε
    filter_upwards [h1 (ε / 2) (by linarith), h2' (ε / 2) (by linarith), eventually_ge_atTop 1]
      with n hn1 hn2 hn θ
    set z : Fin n → Z := fun i => X i ω with hz
    set w := wScore sT z θ with hwdef
    obtain ⟨hwpos, hw1, -⟩ := wScore_facts (z := z) (θ := θ) hn hsm hsbT
    have hsum := iidLaw_sum w M hw1
    have hRe : Rn n ω θ = ∑ j : Fin M → Fin n, iidLaw w M j *
        StatFormal.Wave24c.empAvg (fun i => Y i ω) (m n) (fun t => L t (z ∘ j)) :=
      risk_eq w z L (fun i => Y i ω) (m n)
    have hVe : StatFormal.Wave24e.wVStat sQ Lb z θ = ∑ j : Fin M → Fin n, iidLaw w M j * lossBar P0 L (z ∘ j) :=
      rfl
    have hb : |Rn n ω θ - StatFormal.Wave24e.wVStat sQ Lb z θ| ≤ ε / 2 := by
      rw [hRe, hVe, ← Finset.sum_sub_distrib]
      calc |∑ j : Fin M → Fin n, (iidLaw w M j * StatFormal.Wave24c.empAvg (fun i => Y i ω) (m n)
              (fun t => L t (z ∘ j)) - iidLaw w M j * lossBar P0 L (z ∘ j))|
          ≤ ∑ j : Fin M → Fin n, |iidLaw w M j * StatFormal.Wave24c.empAvg (fun i => Y i ω) (m n)
              (fun t => L t (z ∘ j)) - iidLaw w M j * lossBar P0 L (z ∘ j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin M → Fin n, iidLaw w M j * (ε / 2) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hj := hn2 (z ∘ j)
          rw [Real.dist_eq] at hj
          rw [← mul_sub, abs_mul, abs_of_nonneg (iidLaw_nonneg (fun k => (hwpos k).le) j), abs_sub_comm]
          exact mul_le_mul_of_nonneg_left hj.le (iidLaw_nonneg (fun k => (hwpos k).le) j)
        _ = ε / 2 := by rw [← Finset.sum_mul, hsum, one_mul]
    have hv := hn1 θ
    rw [Real.dist_eq] at hv ⊢
    calc |StatFormal.Wave24e.wPop P0 sQ Lb θ - Rn n ω θ|
        ≤ |StatFormal.Wave24e.wPop P0 sQ Lb θ - StatFormal.Wave24e.wVStat sQ Lb z θ| +
          |Rn n ω θ - StatFormal.Wave24e.wVStat sQ Lb z θ| := by
          rw [abs_sub_comm (Rn n ω θ)]; exact abs_sub_le _ _ _
      _ < ε := by linarith
  have hU := StatFormal.Wave24c.e_ulln Θ Z Ω P P0 X Y m sT K sm sp Kmin Kmax (StatFormal.Wave24e.wPop P0 sQ Lb) Rn
    lc lK lcn lKn hP0 hs hsm hsbT hK hKmin hKb hm inferInstance hXm hXi hXl hYm hYi hYl hlc hlK hR
  filter_upwards [hU] with ω hUω t ht
  have hIid : TendstoUniformly (fun n => jScoreIid sT L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))
      (jPop P0 sT L K lc lK) atTop := by
    refine StatFormal.Wave24c.tu_congr hUω (eventually_atTop.2 ⟨1, fun n hn θ => ?_⟩)
    rw [jScoreIid_eq hpos hK (fun i => X i ω) (fun i => Y i ω) hn (m n) (lcn n) (lKn n) θ]
  exact hIid.tendsto_at ⟨t, ht⟩

/-! ### Identification of the population derivatives -/

variable {P : Measure Ω} [IsProbabilityMeasure P] {P0 : Measure Z} [IsProbabilityMeasure P0] {M : ℕ}
  {X Y : ℕ → Ω → Z} {m : ℕ → ℕ} {s s1 s2 : ℝ → Z → ℝ} {L : Z → (Fin M → Z) → ℝ} {K : Z → Z → ℝ}
  {sm sp Kmin Kmax lc lK θs δ : ℝ} {lcn lKn : ℕ → ℝ}

lemma radius_of_mem {t θs δ : ℝ} (ht : t ∈ Metric.ball θs δ) :
    ∃ r, 0 < r ∧ r < δ ∧ t ∈ Metric.ball θs r := by
  have h := Metric.mem_ball.1 ht
  refine ⟨(dist t θs + δ) / 2, by linarith [dist_nonneg (x := t) (y := θs)], by linarith, ?_⟩
  rw [Metric.mem_ball]; linarith

/-- `J' = D1` and `D1' = D2` on `U`. -/
theorem pop_derivs (hM : 1 ≤ M) (hsm : 0 < sm) (hsb : ∀ t x, sm ≤ s t x ∧ s t x ≤ sp)
    (hs : ContinuousOn (Function.uncurry s) (Metric.ball θs δ ×ˢ univ))
    (hs1 : ContinuousOn (Function.uncurry s1) (Metric.ball θs δ ×ˢ univ))
    (hs2 : ContinuousOn (Function.uncurry s2) (Metric.ball θs δ ×ˢ univ))
    (hsd : ∀ x, ∀ t ∈ Metric.ball θs δ, HasDerivAt (fun t => s t x) (s1 t x) t ∧
      HasDerivAt (fun t => s1 t x) (s2 t x) t)
    (hL : Continuous (Function.uncurry L)) (hK : Continuous (Function.uncurry K)) (hKmin : 0 < Kmin)
    (hKb : ∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax)
    (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P) (hXl : ∀ i, P.map (X i) = P0)
    (hYm : ∀ i, Measurable (Y i)) (hYi : iIndepFun Y P) (hYl : ∀ i, P.map (Y i) = P0)
    (hm : Tendsto m atTop atTop) (hlc : Tendsto lcn atTop (𝓝 lc)) (hlK : Tendsto lKn atTop (𝓝 lK)) :
    ∀ t ∈ Metric.ball θs δ, HasDerivAt (jPop P0 s L K lc lK) (D1 M P0 s s1 L K lc lK t) t ∧
      HasDerivAt (D1 M P0 s s1 L K lc lK) (D2 M P0 s s1 s2 L K lc lK t) t := by
  intro t ht
  obtain ⟨r, hr0, hrδ, htr⟩ := radius_of_mem ht
  have hsub : Metric.closedBall θs r ×ˢ (univ : Set Z) ⊆ Metric.ball θs δ ×ˢ univ :=
    prod_mono (Metric.closedBall_subset_ball hrδ) subset_rfl
  have hae := (tu_gE_hE (P0 := P0) (lcn := lcn) (lKn := lKn) (m := m) hXm hXi hXl hYm hYi hYl hM (L := L)
    hsm (fun t x => (hsb t x).1) hKmin (fun z w => (hKb z w).1) hK hL hs hs1 hs2 hrδ hm hlc hlK).and
    (jIid_tendsto (isCompact_closedBall θs r) (hs.mono hsub) hsm hsb hK hKmin hKb hL hXm hXi hXl hYm hYi hYl hm
      hlc hlK)
  haveI : (ae P).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero P)
  obtain ⟨ω, ⟨hg, hh⟩, hJ⟩ := hae.exists
  have hball : Metric.ball θs r ⊆ Metric.closedBall θs r := Metric.ball_subset_closedBall
  have hbδ : Metric.ball θs r ⊆ Metric.ball θs δ := Metric.ball_subset_ball hrδ.le
  have hsm' : ∀ θ w, sm ≤ s θ w := fun θ w => (hsb θ w).1
  constructor
  · refine hasDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball (hg.mono hball) ?_ (fun x hx => hJ x (hball hx)) htr
    filter_upwards [eventually_ge_atTop 1] with n hn x hx
    exact hasDerivAt_Jiid hsm hsm' hKmin (fun z w => (hKb z w).1) (fun w => (hsd w x (hbδ hx)).1) _ _ hn _ _ _
  · refine hasDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball (hh.mono hball) ?_
      (fun x hx => hg.tendsto_at (hball hx)) htr
    filter_upwards [eventually_ge_atTop 1] with n hn x hx
    exact hasDerivAt_gE hn hsm (fun w => (hsd w x (hbδ hx)).1) (fun w => (hsd w x (hbδ hx)).2) (hsm' x)
      (fun z w => (hKb z w).1) hKmin _ _

/-- The derivative facts for `J^iid_{n,m}` (any `n`) on `U`. -/
lemma Jiid_derivs (hM : 1 ≤ M) (hsm : 0 < sm) (hsm' : ∀ θ w, sm ≤ s θ w)
    (hsd : ∀ x, ∀ t ∈ Metric.ball θs δ, HasDerivAt (fun t => s t x) (s1 t x) t ∧
      HasDerivAt (fun t => s1 t x) (s2 t x) t) (hKmin : 0 < Kmin) (hKb : ∀ x y, Kmin ≤ K x y)
    (x y : ℕ → Z) (n m' : ℕ) (lc' lK' : ℝ) :
    ∀ t ∈ Metric.ball θs δ, (1 ≤ n → deriv (jScoreIid s L K x y n m' lc' lK') t = gE M s s1 L K x y n m' lc' lK' t ∧
        deriv (deriv (jScoreIid s L K x y n m' lc' lK')) t = hE M s s1 s2 L K x y n m' lc' lK' t) ∧
      HasDerivAt (jScoreIid s L K x y n m' lc' lK') (deriv (jScoreIid s L K x y n m' lc' lK') t) t ∧
      HasDerivAt (deriv (jScoreIid s L K x y n m' lc' lK'))
        (deriv (deriv (jScoreIid s L K x y n m' lc' lK')) t) t := by
  intro t ht
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have e : jScoreIid s L K x y 0 m' lc' lK' = fun _ => 0 := funext fun θ => jScoreIid_zero hM s L K x y m' lc' lK' θ
    rw [e]
    refine ⟨fun h => absurd h (by norm_num), ?_, ?_⟩
    · rw [deriv_const']; exact hasDerivAt_const _ _
    · simp only [deriv_const']; exact hasDerivAt_const _ _
  · have hn : 1 ≤ n := hpos
    have hd : ∀ u ∈ Metric.ball θs δ, HasDerivAt (jScoreIid s L K x y n m' lc' lK') (gE M s s1 L K x y n m' lc' lK' u) u :=
      fun u hu => hasDerivAt_Jiid hsm hsm' hKmin hKb (fun w => (hsd w u hu).1) x y hn m' lc' lK'
    have heq : deriv (jScoreIid s L K x y n m' lc' lK') =ᶠ[𝓝 t] fun u => gE M s s1 L K x y n m' lc' lK' u := by
      filter_upwards [Metric.isOpen_ball.mem_nhds ht] with u hu
      exact (hd u hu).deriv
    have h2 : HasDerivAt (deriv (jScoreIid s L K x y n m' lc' lK')) (hE M s s1 s2 L K x y n m' lc' lK' t) t :=
      (hasDerivAt_gE hn hsm (fun w => (hsd w t ht).1) (fun w => (hsd w t ht).2) (hsm' t) hKb hKmin lc' lK').congr_of_eventuallyEq
        heq
    refine ⟨fun _ => ⟨(hd t ht).deriv, h2.deriv⟩, ?_, ?_⟩
    · rw [(hd t ht).deriv]; exact hd t ht
    · rw [h2.deriv]; exact h2

end Conv

open Claims in
theorem score_hessian_ulln : Claims.score_hessian_ulln := by
  intro M sm sp Kmin Kmax lc lK θs δ Z Ω _ _ _ _ _ P _ P0 X Y m s s1 s2 L K lcn lKn hM hsm hsb hδ hs hs1 hs2 hsd hL hK
    hKmin hKb hXm hXi hXl hYm hYi hYl hm hlc hlK
  have hP0 : IsProbabilityMeasure P0 := by
    rw [← hXl 0]; exact (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).2 inferInstance
  have hsm' : ∀ θ w, sm ≤ s θ w := fun θ w => (hsb θ w).1
  have hpop := pop_derivs (P := P) (P0 := P0) (X := X) (Y := Y) (lcn := lcn) (lKn := lKn) hM hsm hsb hs hs1 hs2 hsd
    hL hK hKmin hKb hXm hXi hXl hYm hYi hYl hm hlc hlK
  set J := jPop P0 s L K lc lK with hJdef
  have hJ1 : ∀ t ∈ Metric.ball θs δ, deriv J t = D1 M P0 s s1 L K lc lK t := fun t ht => (hpop t ht).1.deriv
  have hJeq : ∀ t ∈ Metric.ball θs δ, deriv J =ᶠ[𝓝 t] D1 M P0 s s1 L K lc lK := fun t ht => by
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with u hu
    exact hJ1 u hu
  have hJ2 : ∀ t ∈ Metric.ball θs δ, HasDerivAt (deriv J) (D2 M P0 s s1 s2 L K lc lK t) t := fun t ht =>
    (hpop t ht).2.congr_of_eventuallyEq (hJeq t ht)
  have hJ2' : ∀ t ∈ Metric.ball θs δ, deriv (deriv J) t = D2 M P0 s s1 s2 L K lc lK t := fun t ht =>
    (hJ2 t ht).deriv
  have hper : ∀ r, r < δ → ∀ᵐ ω ∂P, TendstoUniformlyOn
      (fun n => deriv (deriv (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))))
      (deriv (deriv J)) atTop (Metric.closedBall θs r) := by
    intro r hr
    have hae := tu_gE_hE (P0 := P0) (lcn := lcn) (lKn := lKn) (m := m) hXm hXi hXl hYm hYi hYl hM (L := L)
      hsm hsm' hKmin (fun z w => (hKb z w).1) hK hL hs hs1 hs2 hr hm hlc hlK
    filter_upwards [hae] with ω hω
    obtain ⟨-, hh⟩ := hω
    refine hh.congr_eventually ?_ fun t ht => (hJ2' t (Metric.closedBall_subset_ball hr ht)).symm
    filter_upwards [eventually_ge_atTop 1] with n hn t ht
    exact ((Jiid_derivs hM hsm hsm' hsd hKmin (fun z w => (hKb z w).1) _ _ n (m n) (lcn n) (lKn n) t
      (Metric.closedBall_subset_ball hr ht)).1 hn).2.symm
  refine ⟨fun t ht => ⟨?_, ?_⟩, ?_, fun n ω t ht => ?_, ?_⟩
  · rw [hJ1 t ht]; exact (hpop t ht).1
  · rw [hJ2' t ht]; exact hJ2 t ht
  · -- continuity of `J''` on `U`
    intro t ht
    obtain ⟨r, hr0, hrδ, htr⟩ := radius_of_mem ht
    have hc := continuousOn_D2 (P0 := P0) (M := M) (L := L) (lc := lc) (lK := lK) hsm hsm' hKmin
      (fun z w => (hKb z w).1) hK hL hs hs1 hs2 hrδ
    have hca : ContinuousAt (D2 M P0 s s1 s2 L K lc lK) t :=
      hc.continuousAt (mem_of_superset (Metric.isOpen_ball.mem_nhds htr) Metric.ball_subset_closedBall)
    have hev : deriv (deriv J) =ᶠ[𝓝 t] D2 M P0 s s1 s2 L K lc lK := by
      filter_upwards [Metric.isOpen_ball.mem_nhds ht] with u hu
      exact hJ2' u hu
    exact (hca.congr hev.symm).continuousWithinAt
  · exact (Jiid_derivs hM hsm hsm' hsd hKmin (fun z w => (hKb z w).1) _ _ n (m n) (lcn n) (lKn n) t ht).2
  · -- one null set for all radii: the radii `δ − 1/(k+1)`, `k ∈ ℕ`
    have hall := ae_all_iff.2 fun k : ℕ => hper (δ - 1 / ((k : ℝ) + 1)) (by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith)
    filter_upwards [hall] with ω hω r hr
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hr)
    exact (hω k).mono (Metric.closedBall_subset_closedBall (by linarith))

end StatFormal.Wave28f
