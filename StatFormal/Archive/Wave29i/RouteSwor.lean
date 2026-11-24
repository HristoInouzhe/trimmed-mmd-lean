import StatFormal.Archive.Wave29i.Statements
import StatFormal.Lib.CLT.AsympLinear
import StatFormal.Archive.Wave28f.RouteHessian
import StatFormal.Archive.Wave28f.RouteLinear
import StatFormal.Archive.WaveP1d.RouteSwor

/-!
# Route — ICL `prop:swor-score`, the transfer of Steps 1 and 2 of `thm:score` to `J_{n,m}` (untrusted)

`J_{n,m} = J^iid_{n,m} + (J_{n,m} − J^iid_{n,m})` and the frozen WaveP1d `swor_derivs` bounds the first two
derivatives of the difference by `C₁/n`, `C₂/n` on every ball where `s'`, `s''` are bounded (every closed sub-ball of
`U`, by continuity on the compact `B̄ × 𝒵`). Hence:
* (b) `swor_hessian_of`: frozen Wave 28f `score_hessian_ulln` + `swor_derivs` ⇒ `J_{n,m}` is twice differentiable on
  `U` and `sup_{B̄(θ⋆,r)} |J''_{n,m} − J''| ≤ sup_{B̄(θ⋆,r)} |(J^iid_{n,m})'' − J''| + C₂/n → 0`;
* (c) `swor_linear_of`: frozen Wave 28f `score_linearization` + `swor_derivs` ⇒ `√n|J'_{n,m}(θ⋆) − (J^iid)'(θ⋆)| ≤
  C₁/√n`, so the same influence functions linearise both gradients.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal Real

namespace StatFormal.Wave29i

open StatFormal.Wave28b StatFormal.Foundations.CLT

/-- Second-order transfer: if `F − G` has derivatives `D1`, `D2` on an open `U` and `G` is twice differentiable on
`U`, then so is `F`, with `F' = G' + D1`, `F'' = G'' + D2` on `U`. -/
lemma deriv2_transfer {F G D1 D2 : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hF : ∀ t ∈ U, HasDerivAt (fun t => F t - G t) (D1 t) t ∧ HasDerivAt D1 (D2 t) t)
    (hG : ∀ t ∈ U, HasDerivAt G (deriv G t) t ∧ HasDerivAt (deriv G) (deriv (deriv G) t) t) :
    ∀ t ∈ U, HasDerivAt F (deriv F t) t ∧ HasDerivAt (deriv F) (deriv (deriv F) t) t ∧
      deriv F t = deriv G t + D1 t ∧ deriv (deriv F) t = deriv (deriv G) t + D2 t := by
  have h1 : ∀ u ∈ U, HasDerivAt F (deriv G u + D1 u) u := by
    intro u hu
    have := (hG u hu).1.add (hF u hu).1
    convert this using 1
    funext t
    simp only [Pi.add_apply]
    ring
  have hd : ∀ u ∈ U, deriv F u = deriv G u + D1 u := fun u hu => (h1 u hu).deriv
  intro t ht
  have hev : deriv F =ᶠ[𝓝 t] fun u => deriv G u + D1 u :=
    Filter.eventually_of_mem (hU.mem_nhds ht) fun u hu => hd u hu
  have h2 : HasDerivAt (deriv F) (deriv (deriv G) t + D2 t) t :=
    ((hG t ht).2.add (hF t ht).2).congr_of_eventuallyEq hev
  refine ⟨?_, ?_, hd t ht, h2.deriv⟩
  · rw [hd t ht]; exact h1 t ht
  · rw [h2.deriv]; exact h2

/-- `prop:swor-score`, transfer (b): frozen Wave 28f `score_hessian_ulln` + frozen WaveP1d `swor_derivs`. -/
theorem swor_hessian_of (h1 : StatFormal.Wave28f.Claims.score_hessian_ulln)
    (h2 : StatFormal.WaveP1d.Claims.swor_derivs) : Claims.swor_hessian := by
  intro M sm sp BL Kmin Kmax lc lK θs δ Z Ω _ _ _ _ _ P _ P0 X Y m s s1 s2 L K lcn lKn hM hsm hsb hδ hs hs1 hs2
    hsd hL hLb hLsym hK hKmin hKb hXm hXi hXl hYm hYi hYl hm hlc0 hlc hlK
  obtain ⟨-, -, hJiid, hunif⟩ := h1 M sm sp Kmin Kmax lc lK θs δ Z Ω P P0 X Y m s s1 s2 L K lcn lKn hM hsm hsb hδ
    hs hs1 hs2 hsd hL hK hKmin hKb hXm hXi hXl hYm hYi hYl hm hlc hlK
  obtain ⟨Λ, hΛ⟩ := hlc.bddAbove_range
  have hlcΛ : ∀ n, 0 ≤ lcn n ∧ lcn n ≤ Λ := fun n => ⟨hlc0 n, hΛ ⟨n, rfl⟩⟩
  set good : ℕ → Prop := fun n => M ≤ n ∧ 0 < m n ∧ M * ((M : ℝ) - 1) * sp / sm ≤ n with hgooddef
  have hgood : ∀ᶠ n in atTop, good n := by
    filter_upwards [eventually_ge_atTop M, hm.eventually_gt_atTop 0,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (M * ((M : ℝ) - 1) * sp / sm)] with n h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- the local transfer on a ball `B(θ⋆, r')`, `r' < δ`
  have hloc : ∀ r', 0 < r' → r' < δ → ∃ C2 : ℝ, ∀ n, good n → ∀ ω, ∀ t ∈ Metric.ball θs r',
      (HasDerivAt (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))
          (deriv (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) t) t ∧
        HasDerivAt (deriv (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)))
          (deriv (deriv (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))) t) t) ∧
      |deriv (deriv (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))) t -
        deriv (deriv (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))) t| ≤ C2 / n := by
    intro r' hr'0 hr'δ
    have hbb : Metric.ball θs r' ⊆ Metric.ball θs δ := Metric.ball_subset_ball hr'δ.le
    have hcb : Metric.closedBall θs r' ×ˢ (univ : Set Z) ⊆ Metric.ball θs δ ×ˢ univ :=
      prod_mono (Metric.closedBall_subset_ball hr'δ) subset_rfl
    obtain ⟨b1, hb1⟩ := ((isCompact_closedBall θs r').prod isCompact_univ).exists_bound_of_continuousOn
      (hs1.mono hcb)
    obtain ⟨b2, hb2⟩ := ((isCompact_closedBall θs r').prod isCompact_univ).exists_bound_of_continuousOn
      (hs2.mono hcb)
    have hsdb : ∀ x, ∀ t ∈ Metric.ball θs r', |s1 t x| ≤ b1 ∧ |s2 t x| ≤ b2 := fun x t ht =>
      ⟨by simpa using hb1 (t, x) ⟨Metric.ball_subset_closedBall ht, mem_univ _⟩,
        by simpa using hb2 (t, x) ⟨Metric.ball_subset_closedBall ht, mem_univ _⟩⟩
    have hsd' : ∀ x, ∀ t ∈ Metric.ball θs r', HasDerivAt (fun t => s t x) (s1 t x) t ∧
        HasDerivAt (fun t => s1 t x) (s2 t x) t := fun x t ht => hsd x t (hbb ht)
    obtain ⟨C1, C2, hCs⟩ := h2 M sm sp b1 b2 BL (Kmax / Kmin) Λ
    refine ⟨C2, fun n hg ω => ?_⟩
    obtain ⟨D1, D2, hD⟩ := hCs Z n (m n) (fun i : Fin n => X i ω) (fun i : Fin (m n) => Y i ω) s s1 s2 L K Kmin
      Kmax (lcn n) (lKn n) (Metric.ball θs r') hM hg.1 hg.2.1 hsm hsb hsd' hsdb hLb hLsym hKmin hKb le_rfl
      (hlcΛ n).1 (hlcΛ n).2 hg.2.2
    have htr := deriv2_transfer (F := jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))
      (G := jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) (D1 := D1) (D2 := D2)
      Metric.isOpen_ball (fun t ht => ⟨(hD t ht).1, (hD t ht).2.1⟩) (fun t ht => hJiid n ω t (hbb ht))
    intro t ht
    obtain ⟨ha, hb, -, hc⟩ := htr t ht
    refine ⟨⟨ha, hb⟩, ?_⟩
    rw [hc, add_sub_cancel_left]
    exact (hD t ht).2.2.2
  refine ⟨?_, ?_⟩
  · filter_upwards [hgood] with n hn ω t ht
    have hd : dist t θs < δ := ht
    obtain ⟨C2, hC2⟩ := hloc ((dist t θs + δ) / 2) (by positivity) (by linarith)
    exact (hC2 n hn ω t (show dist t θs < (dist t θs + δ) / 2 by linarith)).1
  · filter_upwards [hunif] with ω hω r hr
    set r' := (max r 0 + δ) / 2 with hr'
    have hr0 : 0 < r' := by rw [hr']; have := le_max_right r 0; linarith
    have hrr : max r 0 < r' := by rw [hr']; have := max_lt hr hδ; linarith
    have hr'δ : r' < δ := by rw [hr']; have := max_lt hr hδ; linarith
    obtain ⟨C2, hC2⟩ := hloc r' hr0 hr'δ
    have hsub : Metric.closedBall θs r ⊆ Metric.ball θs r' := Metric.closedBall_subset_ball
      (lt_of_le_of_lt (le_max_left r 0) hrr)
    have hiid := hω r hr
    have hc : Tendsto (fun n : ℕ => C2 / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat C2
    rw [Metric.tendstoUniformlyOn_iff] at hiid ⊢
    intro ε hε
    filter_upwards [hiid (ε / 2) (by positivity), hc.eventually (gt_mem_nhds (by positivity : 0 < ε / 2)),
      hgood] with n hn1 hn2 hn3 t ht
    have hb := (hC2 n hn3 ω t (hsub ht)).2
    have h1 := hn1 t ht
    rw [Real.dist_eq] at h1 ⊢
    calc |deriv (deriv (jPop P0 s L K lc lK)) t -
          deriv (deriv (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))) t|
        ≤ |deriv (deriv (jPop P0 s L K lc lK)) t -
            deriv (deriv (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))) t| +
          |deriv (deriv (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))) t -
            deriv (deriv (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))) t| := by
          rw [abs_sub_comm (deriv (deriv (jScore _ _ _ _ _ _ _ _ _)) t)]
          exact abs_sub_le _ _ _
      _ < ε := by linarith

theorem swor_hessian : Claims.swor_hessian :=
  swor_hessian_of StatFormal.Wave28f.score_hessian_ulln StatFormal.WaveP1d.swor_derivs

/-- `prop:swor-score`, transfer (c): frozen Wave 28f `score_linearization` + frozen WaveP1d `swor_derivs`. -/
theorem swor_linear_of (h1 : StatFormal.Wave28f.Claims.score_linearization)
    (h2 : StatFormal.WaveP1d.Claims.swor_derivs) : Claims.swor_linear := by
  intro M sm sp BL Kmin Kmax κ lc lK θs δ Z Ω _ _ _ _ _ P _ P0 X Y m s s1 s2 L K lcn lKn hM hsm hsb hδ hs hs1 hs2
    hsd hL hLb hLsym hK hKmin hKb hXm hYm hXi hYi hXY hXl hYl hκ hmκ hlc0 hlc hlK hslc hslK hmin
  have hm := tendsto_atTop_of_ratio hκ hmκ
  obtain ⟨hdiff, ψp, ψv, hψpm, hψvm, ⟨C, hC⟩, hψp0, hψv0, hlin⟩ := h1 M sm sp Kmin Kmax κ lc lK θs δ Z Ω P P0 X Y
    m s s1 s2 L K lcn lKn hM hsm hsb hδ hs hs1 hs2 hsd hL hK hKmin hKb hXm hYm hXi hYi hXY hXl hYl hκ hmκ hlc hlK
    hslc hslK hmin
  set δ' := δ / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hδ'δ : δ' < δ := by linarith
  have hbb : Metric.ball θs δ' ⊆ Metric.ball θs δ := Metric.ball_subset_ball hδ'δ.le
  have hcb : Metric.closedBall θs δ' ×ˢ (univ : Set Z) ⊆ Metric.ball θs δ ×ˢ univ :=
    prod_mono (Metric.closedBall_subset_ball hδ'δ) subset_rfl
  obtain ⟨b1, hb1⟩ := ((isCompact_closedBall θs δ').prod isCompact_univ).exists_bound_of_continuousOn (hs1.mono hcb)
  obtain ⟨b2, hb2⟩ := ((isCompact_closedBall θs δ').prod isCompact_univ).exists_bound_of_continuousOn (hs2.mono hcb)
  have hsdb : ∀ x, ∀ t ∈ Metric.ball θs δ', |s1 t x| ≤ b1 ∧ |s2 t x| ≤ b2 := fun x t ht =>
    ⟨by simpa using hb1 (t, x) ⟨Metric.ball_subset_closedBall ht, mem_univ _⟩,
      by simpa using hb2 (t, x) ⟨Metric.ball_subset_closedBall ht, mem_univ _⟩⟩
  have hsd' : ∀ x, ∀ t ∈ Metric.ball θs δ', HasDerivAt (fun t => s t x) (s1 t x) t ∧
      HasDerivAt (fun t => s1 t x) (s2 t x) t := fun x t ht => hsd x t (hbb ht)
  obtain ⟨Λ, hΛ⟩ := hlc.bddAbove_range
  have hlcΛ : ∀ n, 0 ≤ lcn n ∧ lcn n ≤ Λ := fun n => ⟨hlc0 n, hΛ ⟨n, rfl⟩⟩
  obtain ⟨C1, C2, hCs⟩ := h2 M sm sp b1 b2 BL (Kmax / Kmin) Λ
  set good : ℕ → Prop := fun n => M ≤ n ∧ 0 < m n ∧ M * ((M : ℝ) - 1) * sp / sm ≤ n with hgooddef
  have hgood : ∀ᶠ n in atTop, good n := by
    filter_upwards [eventually_ge_atTop M, hm.eventually_gt_atTop 0,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (M * ((M : ℝ) - 1) * sp / sm)] with n h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hex : ∀ (n : ℕ) (ω : Ω), ∃ D1 D2 : ℝ → ℝ, good n → ∀ t ∈ Metric.ball θs δ',
      HasDerivAt (fun t => jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) t -
        jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) t) (D1 t) t ∧
      HasDerivAt D1 (D2 t) t ∧ |D1 t| ≤ C1 / n ∧ |D2 t| ≤ C2 / n := by
    intro n ω
    by_cases hg : good n
    · obtain ⟨D1, D2, hD⟩ := hCs Z n (m n) (fun i : Fin n => X i ω) (fun i : Fin (m n) => Y i ω) s s1 s2 L K Kmin
        Kmax (lcn n) (lKn n) (Metric.ball θs δ') hM hg.1 hg.2.1 hsm hsb hsd' hsdb hLb hLsym hKmin hKb le_rfl
        (hlcΛ n).1 (hlcΛ n).2 hg.2.2
      exact ⟨D1, D2, fun _ => hD⟩
    · exact ⟨0, 0, fun h' => absurd h' hg⟩
  choose D1 D2 hD using hex
  have hθ' : θs ∈ Metric.ball θs δ' := Metric.mem_ball_self hδ'0
  have hderivH : ∀ᶠ n in atTop, ∀ ω, HasDerivAt (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n)
      (lKn n)) (deriv (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs + D1 n ω θs)
      θs := by
    filter_upwards [hgood] with n hn ω
    have h1 := hdiff n ω
    have h2 := (hD n ω hn θs hθ').1
    convert h1.add h2 using 1
    funext t; simp only [Pi.add_apply]; ring
  have hsmall : TIP0 P (fun (n : ℕ) ω => √(n : ℝ) * D1 n ω θs) := by
    have hc : Tendsto (fun n : ℕ => C1 / √(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    refine TIP0.of_dominated (W := fun n _ => C1 / √(n : ℝ)) (Bad := fun _ => ∅) (tip0_det hc) (by simp) ?_
    filter_upwards [hgood, eventually_ge_atTop 1] with n hn hn1 ω _
    have hb := (hD n ω hn θs hθ').2.2.1
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsq : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 hn'
    have hC1 : 0 ≤ C1 / n := (abs_nonneg _).trans hb
    have hC10 : 0 ≤ C1 := by
      rcases div_nonneg_iff.1 hC1 with h | h
      · exact h.1
      · linarith [h.2, hn']
    calc |√(n : ℝ) * D1 n ω θs| = √(n : ℝ) * |D1 n ω θs| := by rw [abs_mul, abs_of_pos hsq]
      _ ≤ √(n : ℝ) * (C1 / n) := mul_le_mul_of_nonneg_left hb hsq.le
      _ = C1 / √(n : ℝ) := by
        rw [show √(n : ℝ) * (C1 / n) = C1 * (√(n : ℝ) / n) by ring, Real.sqrt_div_self']
        ring
      _ ≤ |C1 / √(n : ℝ)| := le_abs_self _
  refine ⟨?_, ψp, ψv, hψpm, hψvm, ⟨C, hC⟩, hψp0, hψv0, hlin, ?_⟩
  · filter_upwards [hderivH] with n hn ω
    rw [(hn ω).deriv]; exact hn ω
  · rw [tip0_iff] at hlin ⊢
    refine (hlin.add hsmall).congr ?_
    filter_upwards [hderivH] with n hn ω
    rw [(hn ω).deriv]
    ring

theorem swor_linear : Claims.swor_linear :=
  swor_linear_of StatFormal.Wave28f.score_linearization StatFormal.WaveP1d.swor_derivs

end StatFormal.Wave29i
