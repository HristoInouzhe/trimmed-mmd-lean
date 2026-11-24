import StatFormal.Archive.Wave29i.Statements
import StatFormal.Archive.Wave28b.RouteConsistency

/-!
# Route — ICL `lem:e-ulln`, the risk-term premise discharged (untrusted)

* `eulln_risk_of`: the frozen Wave 28b `score_argmin_discharged` at `λ_cov = λ_KL = 0` (with the constant kernel
  `K ≡ 1`, which the risk term does not see, and `1/(n+1)`-minimisers, which exist because the risk term is `≥ 0`)
  gives `sup_Θ |J_{n,m} − J| → 0` almost surely for the without-replacement risk term; the frozen Wave 11b
  `swor_value` (`sup_Θ |J_{n,m} − J^iid_{n,m}| ≤ C₀/n`, here with `λ_cov = 0`) transfers it to the i.i.d. risk term.
  So the two frozen claims alone discharge the premise.
* `eulln_discharged_of`: the frozen Wave 24c `e_ulln` with that premise; the display of `lem:e-ulln` follows from
  the identification of `J^iid_{n,m}` with the Wave 24c empirical objects (Wave 28b route lemma `jScoreIid_eq`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal

namespace StatFormal.Wave29i

open StatFormal.Wave28b StatFormal.Wave11b

/-- The risk term of `lem:e-ulln`, i.e. the premise of the frozen Wave 24c `e_ulln` for the concrete i.i.d.-context
risk: under `as:compact`–`as:loss`, almost surely `sup_Θ |P_m[∫ L dμ_{θ,n}^{⊗M}] − ∫ L̄ dμ_θ^{⊗M}| → 0`. The risk term
is `J^iid_{n,m}` at `λ_cov = λ_KL = 0` (frozen Wave 28b `jScoreIid`), its limit `J` at `λ_cov = λ_KL = 0` (frozen
Wave 28b `jPop`, i.e. the frozen Wave 24e `wPop` with `H_θ = L̄`). Route statement (not a target: it is the
`λ ≡ 0`, `K ≡ 1` instance of the second conjunct of `Claims.eulln_discharged`). -/
def eullnRisk : Prop :=
  ∀ (Θ Z Ω : Type) [MetricSpace Θ] [CompactSpace Θ] [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) (P0 : Measure Z) (M : ℕ) (X Y : ℕ → Ω → Z) (m : ℕ → ℕ)
    (s : Θ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (sm sp BL : ℝ),
    IsProbabilityMeasure P0 → Continuous (Function.uncurry s) → 0 < sm → (∀ θ z, sm ≤ s θ z ∧ s θ z ≤ sp) →
    1 ≤ M → Continuous (Function.uncurry L) → (∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) →
    (∀ z t (σ : Equiv.Perm (Fin M)), L z (t ∘ σ) = L z t) →
    Tendsto m atTop atTop → IsProbabilityMeasure P →
    (∀ j, Measurable (X j)) → iIndepFun X P → (∀ j, P.map (X j) = P0) →
    (∀ j, Measurable (Y j)) → iIndepFun Y P → (∀ j, P.map (Y j) = P0) →
      ∀ᵐ ω ∂P, TendstoUniformly (fun n => jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) 0 0)
        (jPop P0 s L K 0 0) atTop


section Aux
variable {Θ Z : Type*} {M : ℕ}

/-- The without-replacement risk term (`λ = 0`) is nonnegative. -/
lemma jScore_zero_nonneg {s : Θ → Z → ℝ} {L : Z → (Fin M → Z) → ℝ} {K : Z → Z → ℝ}
    (hs : ∀ θ z, 0 < s θ z) (hL : ∀ z t, 0 ≤ L z t) (x y : ℕ → Z) (n m : ℕ) (θ : Θ) :
    0 ≤ jScore s L K x y n m 0 0 θ := by
  unfold jScore jSwor
  have hw : ∀ j, 0 ≤ wScore s (fun i : Fin n => x i) θ j := fun j =>
    div_nonneg (hs θ _).le (Finset.sum_nonneg fun l _ => (hs θ _).le)
  have hcps : ∀ S, 0 ≤ StatFormal.ICL.cps (wScore s (fun i : Fin n => x i) θ) univ M S := fun S =>
    div_nonneg (Finset.prod_nonneg fun j _ => hw j)
      (Finset.sum_nonneg fun T _ => Finset.prod_nonneg fun j _ => hw j)
  have hloss : ∀ (z : Z) (S : Finset (Fin n)), 0 ≤ lossSub L z (fun i : Fin n => x i) S := by
    intro z S
    unfold lossSub
    split_ifs
    · exact hL _ _
    · exact le_rfl
  simp only [zero_mul, add_zero]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
  exact Finset.sum_nonneg fun S _ => mul_nonneg (hcps S) (hloss _ S)

/-- At `λ = 0` the i.i.d. objective does not depend on the kernel. -/
lemma jScoreIid_zero_kernel (s : Θ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K K' : Z → Z → ℝ) (x y : ℕ → Z)
    (n m : ℕ) : jScoreIid s L K x y n m 0 0 = jScoreIid s L K' x y n m 0 0 := by
  funext θ
  unfold jScoreIid jIid
  simp

/-- At `λ = 0` the population objective does not depend on the kernel. -/
lemma jPop_zero_kernel [MeasurableSpace Z] (P0 : Measure Z) (s : Θ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ)
    (K K' : Z → Z → ℝ) : jPop P0 s L K 0 0 = jPop P0 s L K' 0 0 := by
  funext θ
  unfold jPop
  simp

end Aux

/-- Frozen Wave 28b `score_argmin_discharged` + frozen Wave 11b `swor_value` ⇒ the risk-term premise of the frozen
Wave 24c `e_ulln`. -/
theorem eulln_risk_of (h1 : StatFormal.Wave28b.Claims.score_argmin_discharged)
    (h2 : StatFormal.Wave11b.Claims.swor_value) : eullnRisk := by
  intro Θ Z Ω _ _ _ _ _ _ _ P P0 M X Y m s L K sm sp BL hP0 hs hsm hsb hM hL hLb hLsym hm hP hXm hXi hXl hYm hYi
    hYl
  rcases isEmpty_or_nonempty Θ with hΘ | hΘ
  · refine ae_of_all _ fun ω => ?_
    rw [Metric.tendstoUniformly_iff]
    intro ε _
    exact Eventually.of_forall fun n θ => isEmptyElim θ
  have hpos : ∀ θ z, 0 < s θ z := fun θ z => lt_of_lt_of_le hsm (hsb θ z).1
  set K1 : Z → Z → ℝ := fun _ _ => 1 with hK1
  set J : ℕ → Ω → Θ → ℝ := fun n ω => jScore s L K1 (fun i => X i ω) (fun i => Y i ω) n (m n) 0 0 with hJ
  have hJ0 : ∀ n ω θ, 0 ≤ J n ω θ := fun n ω θ =>
    jScore_zero_nonneg hpos (fun z t => (hLb z t).1) _ _ n (m n) θ
  have hex : ∀ n ω, ∃ θ, ∀ θ', J n ω θ ≤ J n ω θ' + 1 / ((n : ℝ) + 1) := by
    intro n ω
    have hbdd : BddBelow (range (J n ω)) := ⟨0, by rintro _ ⟨θ, rfl⟩; exact hJ0 n ω θ⟩
    have hlt : ⨅ θ, J n ω θ < (⨅ θ, J n ω θ) + 1 / ((n : ℝ) + 1) := lt_add_of_pos_right _ (by positivity)
    obtain ⟨θ, hθ⟩ := exists_lt_of_ciInf_lt hlt
    exact ⟨θ, fun θ' => hθ.le.trans (by linarith [ciInf_le hbdd θ'])⟩
  choose θn hθn using hex
  have hd := h1 Θ Z Ω P P0 M X Y m s L K1 sm sp BL 1 1 0 0 (fun _ => 0) (fun _ => 0) θn
    (fun n _ => 1 / ((n : ℝ) + 1)) hP hP0 hM hs hsm hsb continuous_const one_pos (fun _ _ => ⟨le_rfl, le_rfl⟩)
    hL hLb hLsym hXm hXi hXl hYm hYi hYl hm (fun _ => le_rfl) tendsto_const_nhds tendsto_const_nhds
    (ae_of_all _ fun _ => tendsto_one_div_add_atTop_nhds_zero_nat) (ae_of_all _ fun ω n θ => hθn n ω θ)
  filter_upwards [hd] with ω hω
  have hu : TendstoUniformly (fun n => J n ω) (jPop P0 s L K1 0 0) atTop := hω.2.2.1
  -- the without-replacement / i.i.d. difference
  have hD : TendstoUniformly (fun n θ => jScoreIid s L K1 (fun i => X i ω) (fun i => Y i ω) n (m n) 0 0 θ -
      J n ω θ) (fun _ => 0) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hC := (tendsto_const_div_atTop_nhds_zero_nat (swC0 M sm sp BL 1 1 0)).eventually (gt_mem_nhds hε)
    have hN : ∀ᶠ n : ℕ in atTop, M * ((M : ℝ) - 1) * sp / sm ≤ n :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop _
    have hm1 : ∀ᶠ n in atTop, 1 ≤ m n := hm.eventually_ge_atTop 1
    filter_upwards [hC, hN, hm1, eventually_ge_atTop M] with n hCn hNn hmn hMn θ
    have hsw := h2 Z Θ n M (m n) (fun i : Fin n => X i ω) (fun i : Fin (m n) => Y i ω) s L K1 sm sp BL 1 1 0 0 0
      hM hMn hmn hsm hsb hLb hLsym one_pos (fun _ _ => ⟨le_rfl, le_rfl⟩) le_rfl le_rfl hNn θ
    rw [Real.dist_eq, zero_sub, abs_neg, abs_sub_comm]
    exact lt_of_le_of_lt hsw hCn
  have hI : TendstoUniformly (fun n => jScoreIid s L K1 (fun i => X i ω) (fun i => Y i ω) n (m n) 0 0)
      (jPop P0 s L K1 0 0) atTop := by
    have h := hu.add hD
    refine StatFormal.Wave24c.tu_congr_lim (StatFormal.Wave24c.tu_congr h (Eventually.of_forall fun n θ => ?_))
      fun θ => add_zero _
    simp only [Pi.add_apply]
    ring
  have hfun : (fun n => jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) 0 0) =
      fun n => jScoreIid s L K1 (fun i => X i ω) (fun i => Y i ω) n (m n) 0 0 :=
    funext fun n => jScoreIid_zero_kernel s L K K1 _ _ n (m n)
  rw [hfun, jPop_zero_kernel P0 s L K K1]
  exact hI

/-- `eulln_risk` (proved from the frozen Wave 28b and Wave 11b claims). -/
theorem eulln_risk : eullnRisk :=
  eulln_risk_of StatFormal.Wave28b.score_argmin_discharged StatFormal.Wave11b.swor_value

/-- Lean check of the discharge: frozen Wave 24c `e_ulln` + the discharged premise `eulln_risk` ⇒
`eulln_discharged` (whose first conjunct is the frozen `e_ulln` conclusion at the concrete risk term). -/
theorem eulln_discharged_of (h : StatFormal.Wave24c.Claims.e_ulln) (hr : eullnRisk) :
    Claims.eulln_discharged := by
  intro Θ Z Ω _ _ _ _ _ _ _ P P0 M X Y m s L K sm sp BL Kmin Kmax lc lK lcn lKn hP0 hs hsm hsb hK hKmin hKb hM hL
    hLb hLsym hm hP hXm hXi hXl hYm hYi hYl hlc hlK
  have hpos : ∀ θ z, 0 < s θ z := fun θ z => lt_of_lt_of_le hsm (hsb θ z).1
  have hR := hr Θ Z Ω P P0 M X Y m s L K sm sp BL hP0 hs hsm hsb hM hL hLb hLsym hm hP hXm hXi hXl hYm hYi hYl
  have hU := h Θ Z Ω P P0 X Y m s K sm sp Kmin Kmax (jPop P0 s L K 0 0)
    (fun n ω => jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) 0 0) lc lK lcn lKn hP0 hs hsm hsb hK
    hKmin hKb hm hP hXm hXi hXl hYm hYi hYl hlc hlK hR
  filter_upwards [hU] with ω hω
  refine ⟨hω, ?_⟩
  refine StatFormal.Wave24c.tu_congr_lim (StatFormal.Wave24c.tu_congr hω (eventually_atTop.2 ⟨1, fun n hn θ => ?_⟩))
    fun θ => ?_
  · rw [jScoreIid_eq hpos hK (fun i => X i ω) (fun i => Y i ω) hn (m n) (lcn n) (lKn n) θ,
      jScoreIid_eq hpos hK (fun i => X i ω) (fun i => Y i ω) hn (m n) 0 0 θ]
    ring
  · unfold jPop
    ring

theorem eulln_discharged : Claims.eulln_discharged :=
  eulln_discharged_of StatFormal.Wave24c.e_ulln eulln_risk

end StatFormal.Wave29i
