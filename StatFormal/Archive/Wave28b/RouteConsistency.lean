import StatFormal.Archive.Wave28b.Statements
import StatFormal.Archive.Wave23a.RouteScore
import StatFormal.Archive.Wave24c.RouteICL
import StatFormal.Archive.Wave24e.RouteVStat
import StatFormal.Archive.Wave11b.RouteSwor

/-!
# Route — ICL `thm:score`, the almost-sure uniform law and consistency on the concrete objective (untrusted)

* Risk term (`lem:e-ulln`, first display): `P_m[∫ L dμ_{θ,n}^{⊗M}] − ∫ L̄ dμ_{θ,n}^{⊗M}` is a `w(θ)^{⊗M}`-average of
  `(P_m − P₀) L(·; z_{1:M})`, so it is bounded by `sup_t |(P_m − P₀)L(·; t)|` (Glivenko–Cantelli with index
  `t ∈ 𝒵^M`, certified Wave 24c `compactGC_of_iid`), and `∫ L̄ dμ_{θ,n}^{⊗M} → ∫ L̄ dμ_θ^{⊗M}` uniformly (certified
  Wave 24e `e_vstat` with `H_θ = L̄`).
* Coverage and relative entropy: certified Wave 24c `e_ulln`, after identifying the frozen Wave 11b `jIid` at the
  score weights with the Wave 24c empirical objects (`coverRho` of `empCtxLaw`, `klEmp = klUnif`).
* Without replacement: certified Wave 11b `swor_value`, `sup_Θ |J_{n,m} − J^iid_{n,m}| ≤ C₀/n`.
* `J_{n,m}` is continuous for `n ≥ M` (finite sums, products and quotients by `e_M(w(θ)) > 0`, logarithms of
  coverages `≥ K_min`), so `J` is continuous as a uniform limit; the frozen Wave 23a `score_argmin` concludes.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal

namespace StatFormal.Wave28b

open StatFormal.ICL StatFormal.ICL.Cond StatFormal.ICL.Diag StatFormal.Wave11b

/-! ### Continuity of the objective in `θ` -/

section Cont
variable {Θ Z : Type*} [TopologicalSpace Θ] {M n m : ℕ}

lemma continuous_wScore {s : Θ → Z → ℝ} (hs : ∀ z, Continuous fun θ => s θ z) {z : Fin n → Z}
    (hpos : ∀ θ, 0 < ∑ l, s θ (z l)) : Continuous fun θ => wScore s z θ :=
  continuous_pi fun j => (hs (z j)).div (continuous_finsetSum _ fun l _ => hs (z l)) fun θ => (hpos θ).ne'

lemma continuous_esym {w : Θ → Fin n → ℝ} (hw : Continuous w) (t : Finset (Fin n)) (k : ℕ) :
    Continuous fun θ => esym (w θ) t k :=
  continuous_finsetSum _ fun _ _ => continuous_finsetProd _ fun j _ => (continuous_apply j).comp hw

lemma continuous_cps {w : Θ → Fin n → ℝ} (hw : Continuous w) (hE : ∀ θ, esym (w θ) univ M ≠ 0)
    (S : Finset (Fin n)) : Continuous fun θ => cps (w θ) univ M S :=
  (continuous_finsetProd _ fun j _ => (continuous_apply j).comp hw).div (continuous_esym hw univ M) hE

lemma continuous_Grisk {w : Θ → Fin n → ℝ} (hw : Continuous w) (hE : ∀ θ, esym (w θ) univ M ≠ 0)
    (f : Finset (Fin n) → ℝ) : Continuous fun θ => Grisk (w θ) M f :=
  continuous_finsetSum _ fun S _ => (continuous_cps hw hE S).mul continuous_const

lemma continuous_incl {w : Θ → Fin n → ℝ} (hw : Continuous w) (hE : ∀ θ, esym (w θ) univ M ≠ 0)
    (l : Fin n) : Continuous fun θ => incl (w θ) M l :=
  continuous_finsetSum _ fun S _ => continuous_cps hw hE S

/-- The score weights lie in `Δ^{(M)}` when `M ≤ n` (all coordinates are positive). -/
lemma inDeltaM_wScore {s : Θ → Z → ℝ} {sm sp : ℝ} (hsm : 0 < sm) (hsb : ∀ θ x, sm ≤ s θ x ∧ s θ x ≤ sp)
    {z : Fin n → Z} (hM : 1 ≤ M) (hMn : M ≤ n) (θ : Θ) : InDeltaM (wScore s z θ) M := by
  have hn : 0 < n := by omega
  obtain ⟨hwpos, hw1, -⟩ := wScore_facts (z := z) (θ := θ) hn hsm hsb
  refine ⟨fun j => (hwpos j).le, hw1, ?_⟩
  rw [filter_true_of_mem (fun j _ => (hwpos j).ne'), card_univ, Fintype.card_fin]
  exact hMn

/-- The without-replacement coverage `Σ_l (π_l/M) K(x, z_l)` is at least `K_min`. -/
lemma coverage_ge {w : Fin n → ℝ} (hM : 1 ≤ M) (hΔ : InDeltaM w M) {K : Z → Z → ℝ} {Kmin Kmax : ℝ}
    (hKb : ∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) (x : Z) (z : Fin n → Z) :
    Kmin ≤ ∑ l, incl w M l / M * K x (z l) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum := (StatFormal.ICL.cps_incl n M w hM hΔ).2
  have hnn : ∀ l, 0 ≤ incl w M l := fun l => by
    unfold incl
    refine sum_nonneg fun S hS => ?_
    exact (StatFormal.ICL.cps_wellPosed n M w hΔ).2.1 S (mem_filter.1 hS).1
  calc Kmin = ∑ l, incl w M l / M * Kmin := by
        rw [← sum_mul, ← sum_div, hsum, div_self hM'.ne', one_mul]
    _ ≤ _ := sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hKb _ _).1 (div_nonneg (hnn l) hM'.le)

/-- `θ ↦ J_{n,m}(θ)` is continuous for `n ≥ M`. -/
lemma continuous_jScore {s : Θ → Z → ℝ} {L : Z → (Fin M → Z) → ℝ} {K : Z → Z → ℝ} {sm sp Kmin Kmax : ℝ}
    (hs : ∀ z, Continuous fun θ => s θ z) (hsm : 0 < sm) (hsb : ∀ θ x, sm ≤ s θ x ∧ s θ x ≤ sp)
    (hKmin : 0 < Kmin) (hKb : ∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) (hM : 1 ≤ M) (hMn : M ≤ n)
    (x y : ℕ → Z) (lcov lKL : ℝ) : Continuous (jScore s L K x y n m lcov lKL) := by
  have hn : 0 < n := by omega
  set z : Fin n → Z := fun i => x i with hz
  have hpos : ∀ θ, 0 < ∑ l, s θ (z l) := fun θ =>
    sum_pos (fun l _ => lt_of_lt_of_le hsm (hsb θ (z l)).1) ⟨⟨0, hn⟩, mem_univ _⟩
  have hw : Continuous fun θ => wScore s z θ := continuous_wScore hs hpos
  have hΔ : ∀ θ, InDeltaM (wScore s z θ) M := inDeltaM_wScore hsm hsb hM hMn
  have hE : ∀ θ, esym (wScore s z θ) univ M ≠ 0 := fun θ => (esym_univ_pos (hΔ θ)).ne'
  have hwpos : ∀ θ j, 0 < wScore s z θ j := fun θ j => ((wScore_facts (z := z) (θ := θ) hn hsm hsb).1 j)
  unfold jScore jSwor klUnif
  refine ((continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_Grisk hw hE _)).add
    (continuous_const.mul (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)))).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_))
  · refine Continuous.log (continuous_finsetSum _ fun l _ =>
      ((continuous_incl hw hE l).div_const _).mul continuous_const) fun θ => ?_
    exact (lt_of_lt_of_le hKmin (coverage_ge hM (hΔ θ) hKb _ z)).ne'
  · refine ((continuous_apply i).comp hw).mul (Continuous.log (continuous_const.mul
      ((continuous_apply i).comp hw)) fun θ => ?_)
    exact (mul_pos (by exact_mod_cast hn) (hwpos θ i)).ne'

end Cont

/-! ### The i.i.d.-context objective in the Wave 24c empirical form -/

section Ident
variable {Θ Z : Type} {M : ℕ}

open StatFormal.Wave24c in
/-- `J^iid_{n,m} = R_{n,m} − λ_cov P_m log ρ_{μ_{θ,n}} + λ_KL KL(μ_{θ,n} ‖ P_n)` in the Wave 24c notation. -/
lemma jScoreIid_eq [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z] {s : Θ → Z → ℝ}
    {L : Z → (Fin M → Z) → ℝ} {K : Z → Z → ℝ} (hpos : ∀ θ z, 0 < s θ z) (hK : Continuous (Function.uncurry K))
    (x y : ℕ → Z) {n : ℕ} (hn : 0 < n) (m : ℕ) (lcov lKL : ℝ) (θ : Θ) :
    jScoreIid s L K x y n m lcov lKL θ =
      (1 / (m : ℝ)) * ∑ i : Fin m, ∑ j : Fin M → Fin n,
          iidLaw (wScore s (fun i : Fin n => x i) θ) M j * L (y i) ((fun i : Fin n => x i) ∘ j) -
        lcov * empAvg y m (fun z => Real.log (coverRho K (empCtxLaw s x n θ) z)) +
      lKL * klEmp s x n θ := by
  have hS : 0 < ∑ k ∈ Finset.range n, s θ (x k) :=
    Finset.sum_pos (fun k _ => hpos θ (x k)) ⟨0, Finset.mem_range.2 hn⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hSf : ∑ l : Fin n, s θ (x l) = ∑ k ∈ Finset.range n, s θ (x k) :=
    Fin.sum_univ_eq_sum_range (fun k => s θ (x k)) n
  -- coverage
  have hcov : ∀ z, ∑ l : Fin n, wScore s (fun i : Fin n => x i) θ l * K z (x l) =
      coverRho K (empCtxLaw s x n θ) z := by
    intro z
    rw [coverRho_emp x hn hpos hK θ z]
    unfold empAvg wScore
    rw [hSf, mul_div_mul_left _ _ (inv_ne_zero hn'.ne')]
    rw [← Fin.sum_univ_eq_sum_range (fun k => s θ (x k) * K z (x k)) n, Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  -- relative entropy
  have hkl : klUnif n (wScore s (fun i : Fin n => x i) θ) = klEmp s x n θ := by
    unfold klUnif klEmp empAvg wScore
    rw [hSf]
    set S := ∑ k ∈ Finset.range n, s θ (x k)
    have hlog : ∀ l : Fin n, Real.log (n * (s θ (x l) / S)) = Real.log (s θ (x l)) - Real.log ((n : ℝ)⁻¹ * S) := by
      intro l
      rw [show (n : ℝ) * (s θ (x l) / S) = s θ (x l) / ((n : ℝ)⁻¹ * S) by field_simp,
        Real.log_div (hpos θ (x l)).ne' (by positivity)]
    simp_rw [hlog, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, ← hSf, div_self (by rw [hSf]; exact hS.ne'),
      one_mul, mul_div_mul_left _ _ (inv_ne_zero hn'.ne'),
      ← Fin.sum_univ_eq_sum_range (fun k => s θ (x k) * Real.log (s θ (x k))) n, Finset.sum_div, hSf]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  unfold jScoreIid jIid
  rw [hkl]
  simp_rw [hcov]
  unfold empAvg
  rw [← Fin.sum_univ_eq_sum_range (fun i => Real.log (coverRho K (empCtxLaw s x n θ) (y i))) m]
  ring

/-- The risk term of `J^iid_{n,m}` is a `w(θ)^{⊗M}`-average of the validation averages `P_m L(·; z_j)`. -/
lemma risk_eq (w : Fin n → ℝ) (z : Fin n → Z) (L : Z → (Fin M → Z) → ℝ) (y : ℕ → Z) (m : ℕ) :
    (1 / (m : ℝ)) * ∑ i : Fin m, ∑ j : Fin M → Fin n, iidLaw w M j * L (y i) (z ∘ j) =
      ∑ j : Fin M → Fin n, iidLaw w M j * StatFormal.Wave24c.empAvg y m (fun t => L t (z ∘ j)) := by
  unfold StatFormal.Wave24c.empAvg
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun i => L (y i) (z ∘ j)) m, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Ident

/-! ### The almost-sure uniform law and consistency -/

theorem score_argmin_discharged : Claims.score_argmin_discharged := by
  intro Θ Z Ω _ _ _ _ _ _ _ _ P P0 M X Y m s L K sm sp BL Kmin Kmax lc lK lcn lKn θn εn hP hP0 hM hs hsm hsb
    hK hKmin hKb hL hLb hLsym hXm hXi hXl hYm hYi hYl hm hlc0 hlc hlK hε hmin
  have hpos : ∀ θ z, 0 < s θ z := fun θ z => lt_of_lt_of_le hsm (hsb θ z).1
  -- `L̄` is continuous
  have hLsw : Continuous (Function.uncurry fun (t : Fin M → Z) (z : Z) => L z t) :=
    hL.comp continuous_swap
  have hLbar : Continuous (lossBar P0 L) :=
    StatFormal.Wave24c.continuous_param_integral (P0 := P0) (f := fun t z => L z t) hLsw
  set sT : Θ × Z → ℝ := fun q => s q.1 q.2 with hsT
  set Lb : Θ × (Fin M → Z) → ℝ := fun q => lossBar P0 L q.2 with hLbdef
  have hsTc : Continuous sT := hs
  have hLbc : Continuous Lb := hLbar.comp continuous_snd
  have hvs := StatFormal.Wave24e.e_vstat Θ Z Ω P P0 M sT Lb sm sp X hsTc hLbc hsm (fun q => hsb q.1 q.2)
    hXm hXi hXl
  have hGL := StatFormal.Wave24c.compactGC_of_iid hP0 hP hYm hYi hYl (Fin M → Z) (fun t y => L y t) hLsw
  -- the risk term
  set Rn : ℕ → Ω → Θ → ℝ := fun n ω θ => (1 / (m n : ℝ)) * ∑ i : Fin (m n), ∑ j : Fin M → Fin n,
      iidLaw (wScore s (fun i : Fin n => X i ω) θ) M j * L (Y i ω) ((fun i : Fin n => X i ω) ∘ j) with hRn
  have hR : ∀ᵐ ω ∂P, TendstoUniformly (fun n => Rn n ω) (StatFormal.Wave24e.wPop P0 sT Lb) atTop := by
    filter_upwards [hvs, hGL] with ω h1 h2
    have h2' := StatFormal.Wave24c.tu_comp_tendsto h2 hm
    rw [Metric.tendstoUniformly_iff] at h1 h2' ⊢
    intro ε hε
    filter_upwards [h1 (ε / 2) (by linarith), h2' (ε / 2) (by linarith), eventually_ge_atTop 1]
      with n hn1 hn2 hn θ
    set z : Fin n → Z := fun i => X i ω with hz
    set w := wScore s z θ with hwdef
    obtain ⟨hwpos, hw1, -⟩ := wScore_facts (z := z) (θ := θ) hn hsm hsb
    have hsum := iidLaw_sum w M hw1
    have hRe : Rn n ω θ = ∑ j : Fin M → Fin n, iidLaw w M j *
        StatFormal.Wave24c.empAvg (fun i => Y i ω) (m n) (fun t => L t (z ∘ j)) :=
      risk_eq w z L (fun i => Y i ω) (m n)
    have hVe : StatFormal.Wave24e.wVStat sT Lb z θ = ∑ j : Fin M → Fin n, iidLaw w M j * lossBar P0 L (z ∘ j) :=
      rfl
    have hb : |Rn n ω θ - StatFormal.Wave24e.wVStat sT Lb z θ| ≤ ε / 2 := by
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
    calc |StatFormal.Wave24e.wPop P0 sT Lb θ - Rn n ω θ|
        ≤ |StatFormal.Wave24e.wPop P0 sT Lb θ - StatFormal.Wave24e.wVStat sT Lb z θ| +
          |Rn n ω θ - StatFormal.Wave24e.wVStat sT Lb z θ| := by
          rw [abs_sub_comm (Rn n ω θ)]; exact abs_sub_le _ _ _
      _ < ε := by linarith
  have hU := StatFormal.Wave24c.e_ulln Θ Z Ω P P0 X Y m s K sm sp Kmin Kmax (StatFormal.Wave24e.wPop P0 sT Lb) Rn
    lc lK lcn lKn hP0 hs hsm hsb hK hKmin hKb hm hP hXm hXi hXl hYm hYi hYl hlc hlK hR
  filter_upwards [hU, hε, hmin] with ω hUω hεω hminω
  set J : Θ → ℝ := jPop P0 s L K lc lK with hJdef
  set Jn : ℕ → Θ → ℝ := fun n => jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) with hJn
  set Ji : ℕ → Θ → ℝ := fun n => jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)
    with hJi
  -- i.i.d. contexts
  have hIid : TendstoUniformly Ji J atTop := by
    refine StatFormal.Wave24c.tu_congr hUω (eventually_atTop.2 ⟨1, fun n hn θ => ?_⟩)
    rw [hJi]
    dsimp only
    rw [jScoreIid_eq hpos hK (fun i => X i ω) (fun i => Y i ω) hn (m n) (lcn n) (lKn n) θ]
  -- without replacement
  have hD : TendstoUniformly (fun n θ => Jn n θ - Ji n θ) (fun _ => 0) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hC := (tendsto_const_div_atTop_nhds_zero_nat (swC0 M sm sp BL Kmin Kmax (lc + 1))).eventually
      (gt_mem_nhds hε)
    have hlc1 : ∀ᶠ n in atTop, lcn n ≤ lc + 1 := hlc.eventually (ge_mem_nhds (by linarith))
    have hN : ∀ᶠ n : ℕ in atTop, M * ((M : ℝ) - 1) * sp / sm ≤ n := tendsto_natCast_atTop_atTop.eventually_ge_atTop _
    have hm1 : ∀ᶠ n in atTop, 1 ≤ m n := hm.eventually_ge_atTop 1
    filter_upwards [hC, hlc1, hN, hm1, eventually_ge_atTop M] with n hCn hlcn hNn hmn hMn θ
    have hsw := StatFormal.Wave11b.swor_value Z Θ n M (m n) (fun i : Fin n => X i ω) (fun i : Fin (m n) => Y i ω)
      s L K sm sp BL Kmin Kmax (lcn n) (lc + 1) (lKn n) hM hMn hmn hsm hsb hLb hLsym hKmin hKb (hlc0 n) hlcn hNn θ
    rw [Real.dist_eq, zero_sub, abs_neg]
    exact lt_of_le_of_lt hsw hCn
  have hJnu : TendstoUniformly Jn J atTop := by
    have h := hIid.add hD
    refine StatFormal.Wave24c.tu_congr_lim (StatFormal.Wave24c.tu_congr h (Eventually.of_forall fun n θ => ?_))
      fun θ => add_zero (J θ)
    simp only [Pi.add_apply]
    ring
  -- continuity
  have hcont : ∀ n, M ≤ n → Continuous (Jn n) := fun n hn =>
    continuous_jScore (fun z => hs.uncurry_right z) hsm hsb hKmin hKb hM hn _ _ _ _
  have hJc : Continuous J := hJnu.continuous (eventually_atTop.2 ⟨M, hcont⟩).frequently
  obtain ⟨h1, h2, h3, h4⟩ := StatFormal.Wave23a.score_argmin Θ J Jn (fun n => θn n ω) (fun n => εn n ω) hJc hJnu
    hεω hminω
  exact ⟨h1, fun n hn => h2 n (hcont n hn), hJnu, h3, h4⟩

theorem score_argmin_unique : Claims.score_argmin_unique := by
  intro Θ Z Ω _ _ _ _ _ _ _ _ P P0 M X Y m s L K sm sp BL Kmin Kmax lc lK lcn lKn θn εn θs hP hP0 hM hs hsm hsb
    hK hKmin hKb hL hLb hLsym hXm hXi hXl hYm hYi hYl hm hlc0 hlc hlK hε hmin huniq
  filter_upwards [score_argmin_discharged Θ Z Ω P P0 M X Y m s L K sm sp BL Kmin Kmax lc lK lcn lKn θn εn hP hP0 hM
    hs hsm hsb hK hKmin hKb hL hLb hLsym hXm hXi hXl hYm hYi hYl hm hlc0 hlc hlK hε hmin] with ω hω
  exact tendsto_nhds_of_unique_mapClusterPt fun θ hθ => huniq θ (hω.2.2.2.2 θ hθ)

end StatFormal.Wave28b
