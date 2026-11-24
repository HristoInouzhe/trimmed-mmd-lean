import StatFormal.Archive.Wave28f.RouteDerivs
import StatFormal.Lib.CLT.HessianULLN
import StatFormal.Archive.Wave24c.RouteICL
import StatFormal.Archive.Wave24e.RouteVStat

/-!
# Route — Step 1 of ICL `thm:score`: uniform laws for the derivative pieces (untrusted)

On a closed ball `Sb ⊆ U` around `θ⋆` (compact):
* pool averages `P_n φ_θ` (`tu_cE`, compact-parametric Glivenko–Cantelli, certified Wave 24c `compactGC_of_iid`);
* coverage averages `P_n(φ_θ K(z, ·))` uniformly in `(θ, z)` (`tu_eE`);
* the two-sample V-statistics `m^{−1} Σ_i n^{−M} Σ_j pr_θ(x_j) L(y_i; x_j)` (`tu_VE`, certified Wave 24e `vstat_ae`
  with the Glivenko–Cantelli step for `P_m L(·; t)` uniformly in `t ∈ 𝒵^M`);
* validation averages of smooth functions of the coverage averages (`tu_cov`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal Real

namespace StatFormal.Wave28f

open StatFormal.Foundations.CLT

section GC
variable {Z Ω : Type} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {P0 : Measure Z} [IsProbabilityMeasure P0] {X Y : ℕ → Ω → Z}

lemma cE_eq_empAvg (φ : ℝ → Z → ℝ) (x : ℕ → Z) (n : ℕ) (θ : ℝ) :
    cE φ x n θ = StatFormal.Wave24c.empAvg x n (φ θ) := by
  unfold cE pAvg StatFormal.Wave24c.empAvg
  rw [Fin.sum_univ_eq_sum_range (fun i => φ θ (x i)) n]

omit [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z] in
lemma continuous_on_sub {W : Type*} [TopologicalSpace W] {φ : ℝ → W → ℝ} {Sb : Set ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Sb ×ˢ univ)) :
    Continuous (Function.uncurry fun (a : Sb) (z : W) => φ a z) :=
  hφ.comp_continuous (continuous_subtype_val.prodMap continuous_id) fun p => ⟨p.1.2, mem_univ _⟩

lemma tu_cE (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P) (hXl : ∀ i, P.map (X i) = P0)
    {φ : ℝ → Z → ℝ} {Sb : Set ℝ} (hSb : IsCompact Sb) (hφ : ContinuousOn (Function.uncurry φ) (Sb ×ˢ univ)) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n θ => cE φ (fun i => X i ω) n θ) (cP P0 φ) atTop Sb := by
  haveI : CompactSpace Sb := isCompact_iff_compactSpace.1 hSb
  filter_upwards [StatFormal.Wave24c.compactGC_of_iid inferInstance inferInstance hXm hXi hXl Sb _
    (continuous_on_sub hφ)] with ω hω
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  simp_rw [cE_eq_empAvg]
  exact hω

lemma tu_eE (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P) (hXl : ∀ i, P.map (X i) = P0)
    {φ : ℝ → Z → ℝ} {Sb : Set ℝ} (hSb : IsCompact Sb) (hφ : ContinuousOn (Function.uncurry φ) (Sb ×ˢ univ))
    {K : Z → Z → ℝ} (hK : Continuous (Function.uncurry K)) :
    ∀ᵐ ω ∂P, TendstoUniformly (fun n (p : Sb × Z) => eE φ K (fun i => X i ω) n p.1 p.2)
      (fun p => eP P0 φ K p.1 p.2) atTop := by
  haveI : CompactSpace Sb := isCompact_iff_compactSpace.1 hSb
  have hc : Continuous (Function.uncurry fun (p : Sb × Z) (w : Z) => φ p.1 w * K p.2 w) := by
    have h1 := continuous_on_sub hφ
    refine (h1.comp (continuous_fst.fst.prodMk continuous_snd)).mul
      (hK.comp (continuous_fst.snd.prodMk continuous_snd))
  filter_upwards [StatFormal.Wave24c.compactGC_of_iid inferInstance inferInstance hXm hXi hXl (Sb × Z) _ hc]
    with ω hω
  have e : ∀ n (p : Sb × Z), eE φ K (fun i => X i ω) n p.1 p.2 =
      StatFormal.Wave24c.empAvg (fun i => X i ω) n (fun w => φ p.1 w * K p.2 w) := by
    intro n p
    unfold eE pAvg StatFormal.Wave24c.empAvg
    rw [Fin.sum_univ_eq_sum_range (fun i => φ p.1 (X i ω) * K p.2 (X i ω)) n]
  simp_rw [e]
  exact hω

lemma VE_eq {M : ℕ} (pr : ℝ → (Fin M → Z) → ℝ) (L : Z → (Fin M → Z) → ℝ) (x y : ℕ → Z) (n m : ℕ) (θ : ℝ) :
    VE pr L x y n m θ = vstat (fun t => pr θ t * StatFormal.Wave24c.empAvg y m (fun z => L z t))
      (fun j : Fin n => x j) := by
  unfold VE vstat StatFormal.Wave24c.empAvg
  dsimp only
  simp only [Finset.sum_range, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

lemma bound_of_compact {W : Type*} [TopologicalSpace W] [CompactSpace W] {f : W → ℝ} (hf : Continuous f) :
    ∃ C, 0 ≤ C ∧ ∀ w, |f w| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun w => (hC w (mem_univ _)).trans (le_max_left _ _)⟩

lemma vstat_sub {M n : ℕ} (f g : (Fin M → Z) → ℝ) (z : Fin n → Z) :
    vstat f z - vstat g z = vstat (fun t => f t - g t) z := by
  unfold vstat; rw [← mul_sub, ← Finset.sum_sub_distrib]

lemma tu_VE (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P) (hXl : ∀ i, P.map (X i) = P0)
    (hYm : ∀ i, Measurable (Y i)) (hYi : iIndepFun Y P) (hYl : ∀ i, P.map (Y i) = P0) {M : ℕ} (hM : 1 ≤ M)
    {pr : ℝ → (Fin M → Z) → ℝ} {Sb : Set ℝ} (hSb : IsCompact Sb)
    (hpr : ContinuousOn (Function.uncurry pr) (Sb ×ˢ univ)) {L : Z → (Fin M → Z) → ℝ}
    (hL : Continuous (Function.uncurry L)) {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n θ => VE pr L (fun i => X i ω) (fun i => Y i ω) n (m n) θ) (VP P0 pr L)
      atTop Sb := by
  haveI : CompactSpace Sb := isCompact_iff_compactSpace.1 hSb
  set Lb : (Fin M → Z) → ℝ := fun t => ∫ z, L z t ∂P0 with hLbdef
  have hLsw : Continuous (Function.uncurry fun (t : Fin M → Z) (z : Z) => L z t) := hL.comp continuous_swap
  have hLb : Continuous Lb := StatFormal.Wave24c.continuous_param_integral (P0 := P0) (f := fun t z => L z t) hLsw
  have hprc : Continuous (Function.uncurry fun (a : Sb) (t : Fin M → Z) => pr a t) := continuous_on_sub hpr
  set ψ : Sb × (Fin M → Z) → ℝ := fun q => pr q.1 q.2 * Lb q.2 with hψdef
  have hψ : Continuous ψ := hprc.mul (hLb.comp continuous_snd)
  obtain ⟨Cp, hCp0, hCp⟩ := bound_of_compact hprc
  obtain ⟨CL, hCL0, hCL⟩ := bound_of_compact hL
  -- Fubini for the population limit
  have hfub : ∀ θ (hθ : θ ∈ Sb), VP P0 pr L θ = ∫ t, ψ (⟨θ, hθ⟩, t) ∂(Measure.pi fun _ : Fin M => P0) := by
    intro θ hθ
    have hc : Continuous (Function.uncurry fun (y : Z) (t : Fin M → Z) => pr θ t * L y t) :=
      (hprc.comp ((continuous_const (y := (⟨θ, hθ⟩ : Sb))).prodMk continuous_snd)).mul hL
    unfold VP hMean
    rw [integral_integral_swap (integrable_of_abs_le hc.measurable (C := Cp * CL) fun p => by
      show |pr θ p.2 * L p.1 p.2| ≤ _
      rw [abs_mul]
      exact mul_le_mul (hCp (⟨θ, hθ⟩, p.2)) (hCL (p.1, p.2)) (abs_nonneg _) hCp0)]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [hψdef, hLbdef]
    rw [← integral_const_mul]
  filter_upwards [StatFormal.Wave24e.vstat_ae hψ hXm hXi hXl,
    StatFormal.Wave24c.compactGC_of_iid inferInstance inferInstance hYm hYi hYl (Fin M → Z) _ hLsw] with ω h1 h2
  have h2' := StatFormal.Wave24c.tu_comp_tendsto h2 hm
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set η : ℝ := ε / (2 * (Cp + 1)) with hη
  have hη0 : 0 < η := by positivity
  filter_upwards [Metric.tendstoUniformly_iff.1 h1 (ε / 2) (by positivity),
    Metric.tendstoUniformly_iff.1 h2' η hη0] with n hn1 hn2 θ hθ
  have e1 : StatFormal.Wave24e.vStat ψ (fun i : Fin n => X i ω) ⟨θ, hθ⟩ =
      vstat (fun t => pr θ t * Lb t) (fun i : Fin n => X i ω) := by
    unfold StatFormal.Wave24e.vStat vstat; rw [one_div]
  have hb : |vstat (fun t => pr θ t * Lb t) (fun i : Fin n => X i ω) -
      VE pr L (fun i => X i ω) (fun i => Y i ω) n (m n) θ| ≤ Cp * η := by
    rw [VE_eq, vstat_sub]
    refine abs_vstat_le hM (by positivity) (fun t => ?_) _
    rw [← mul_sub, abs_mul]
    refine mul_le_mul (hCp (⟨θ, hθ⟩, t)) ?_ (abs_nonneg _) hCp0
    have := hn2 t
    rw [Real.dist_eq] at this
    exact this.le
  have hlt : Cp * η < ε / 2 := by
    rw [hη]
    have : Cp * (ε / (2 * (Cp + 1))) = ε / 2 * (Cp / (Cp + 1)) := by field_simp
    rw [this]
    have : Cp / (Cp + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  have hv := hn1 ⟨θ, hθ⟩
  rw [Real.dist_eq, e1, ← hfub θ hθ] at hv
  rw [Real.dist_eq]
  calc |VP P0 pr L θ - VE pr L (fun i => X i ω) (fun i => Y i ω) n (m n) θ|
      ≤ |VP P0 pr L θ - vstat (fun t => pr θ t * Lb t) (fun i : Fin n => X i ω)| +
        |vstat (fun t => pr θ t * Lb t) (fun i : Fin n => X i ω) - VE pr L (fun i => X i ω) (fun i => Y i ω) n (m n) θ| :=
        abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hv (hb.trans hlt.le)
    _ = ε := by ring

lemma continuous_eP {φ : ℝ → Z → ℝ} {Sb : Set ℝ} (hSb : IsCompact Sb)
    (hφ : ContinuousOn (Function.uncurry φ) (Sb ×ˢ univ)) {K : Z → Z → ℝ} (hK : Continuous (Function.uncurry K)) :
    Continuous (fun p : Sb × Z => eP P0 φ K p.1 p.2) := by
  haveI : CompactSpace Sb := isCompact_iff_compactSpace.1 hSb
  have hc : Continuous (Function.uncurry fun (p : Sb × Z) (w : Z) => φ p.1 w * K p.2 w) :=
    ((continuous_on_sub hφ).comp (continuous_fst.fst.prodMk continuous_snd)).mul
      (hK.comp (continuous_fst.snd.prodMk continuous_snd))
  exact StatFormal.Wave24c.continuous_param_integral (P0 := P0) hc

lemma tu_cov (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P) (hXl : ∀ i, P.map (X i) = P0)
    (hYm : ∀ i, Measurable (Y i)) (hYi : iIndepFun Y P) (hYl : ∀ i, P.map (Y i) = P0) {k : ℕ}
    {φs : Fin k → ℝ → Z → ℝ} {Sb : Set ℝ} (hSb : IsCompact Sb)
    (hφ : ∀ j, ContinuousOn (Function.uncurry (φs j)) (Sb ×ˢ univ)) {K : Z → Z → ℝ}
    (hK : Continuous (Function.uncurry K)) {Λ : (Fin k → ℝ) → ℝ} {D : Set (Fin k → ℝ)} (hD : IsClosed D)
    (hΛ : ContinuousOn Λ D) (hDE : ∀ᶠ n in atTop, ∀ x : ℕ → Z, ∀ θ ∈ Sb, ∀ z, (fun j => eE (φs j) K x n θ z) ∈ D)
    (hDP : ∀ θ ∈ Sb, ∀ z, (fun j => eP P0 (φs j) K θ z) ∈ D) {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n θ => (m n : ℝ)⁻¹ * ∑ i : Fin (m n),
        Λ (fun j => eE (φs j) K (fun l => X l ω) n θ (Y i ω)))
      (fun θ => ∫ y, Λ (fun j => eP P0 (φs j) K θ y) ∂P0) atTop Sb := by
  haveI : CompactSpace Sb := isCompact_iff_compactSpace.1 hSb
  have hePc : Continuous (fun p : Sb × Z => fun j => eP P0 (φs j) K p.1 p.2) :=
    continuous_pi fun j => continuous_eP hSb (hφ j) hK
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hePc.continuousOn
  set Γ : Sb → Z → ℝ := fun a y => Λ (fun j => eP P0 (φs j) K a y) with hΓdef
  have hΓ : Continuous (Function.uncurry Γ) :=
    hΛ.comp_continuous hePc fun p => hDP p.1 p.1.2 p.2
  have hE : ∀ᵐ ω ∂P, ∀ j, TendstoUniformly (fun n (p : Sb × Z) => eE (φs j) K (fun i => X i ω) n p.1 p.2)
      (fun p => eP P0 (φs j) K p.1 p.2) atTop :=
    ae_all_iff.2 fun j => tu_eE hXm hXi hXl hSb (hφ j) hK
  filter_upwards [hE, StatFormal.Wave24c.compactGC_of_iid inferInstance inferInstance hYm hYi hYl Sb Γ hΓ]
    with ω hEω hG
  have hG' := StatFormal.Wave24c.tu_comp_tendsto hG hm
  have hvec : TendstoUniformlyOn (fun n (p : Sb × Z) => fun j => eE (φs j) K (fun i => X i ω) n p.1 p.2)
      (fun p => fun j => eP P0 (φs j) K p.1 p.2) atTop univ :=
    tuOn_pi fun j => (hEω j).tendstoUniformlyOn
  have hΛu := tuOn_map hvec hD hΛ (fun p _ => hDP p.1 p.1.2 p.2)
    (hDE.mono fun n hn p _ => hn _ p.1 p.1.2 p.2) (fun p _ => hR p (mem_univ _))
  rw [Metric.tendstoUniformlyOn_iff] at hΛu ⊢
  intro ε hε
  filter_upwards [hΛu (ε / 2) (by positivity), Metric.tendstoUniformly_iff.1 hG' (ε / 2) (by positivity),
    hm.eventually_ge_atTop 1] with n hn1 hn2 hn3 θ hθ
  have hm0 : (0 : ℝ) < m n := by exact_mod_cast hn3
  set a : Sb := ⟨θ, hθ⟩
  have e2 : StatFormal.Wave24c.empAvg (fun i => Y i ω) (m n) (Γ a) = (m n : ℝ)⁻¹ * ∑ i : Fin (m n), Γ a (Y i ω) := by
    unfold StatFormal.Wave24c.empAvg; rw [Fin.sum_univ_eq_sum_range (fun i => Γ a (Y i ω)) (m n)]
  have h2 := hn2 a
  rw [e2, Real.dist_eq] at h2
  have h3 : |(m n : ℝ)⁻¹ * ∑ i : Fin (m n), Γ a (Y i ω) - (m n : ℝ)⁻¹ * ∑ i : Fin (m n),
      Λ (fun j => eE (φs j) K (fun l => X l ω) n θ (Y i ω))| ≤ ε / 2 := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.2 hm0)]
    calc (m n : ℝ)⁻¹ * |∑ i : Fin (m n), (Γ a (Y i ω) - Λ (fun j => eE (φs j) K (fun l => X l ω) n θ (Y i ω)))|
        ≤ (m n : ℝ)⁻¹ * ∑ _i : Fin (m n), ε / 2 := by
          refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_))
            (by positivity)
          have := hn1 (a, Y i ω) (mem_univ _)
          rw [Real.dist_eq] at this
          exact this.le
      _ = ε / 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  rw [Real.dist_eq]
  calc |∫ y, Λ (fun j => eP P0 (φs j) K θ y) ∂P0 - (m n : ℝ)⁻¹ * ∑ i : Fin (m n),
        Λ (fun j => eE (φs j) K (fun l => X l ω) n θ (Y i ω))|
      ≤ |∫ y, Γ a y ∂P0 - (m n : ℝ)⁻¹ * ∑ i : Fin (m n), Γ a (Y i ω)| +
        |(m n : ℝ)⁻¹ * ∑ i : Fin (m n), Γ a (Y i ω) - (m n : ℝ)⁻¹ * ∑ i : Fin (m n),
          Λ (fun j => eE (φs j) K (fun l => X l ω) n θ (Y i ω))| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h2 h3
    _ = ε := by ring

/-! ### Continuity of the pieces -/

lemma continuousOn_comp_slot {M : ℕ} {φ : ℝ → Z → ℝ} {Sb : Set ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Sb ×ˢ univ)) (k : Fin M) :
    ContinuousOn (fun p : ℝ × (Fin M → Z) => φ p.1 (p.2 k)) (Sb ×ˢ univ) :=
  hφ.comp (f := fun p : ℝ × (Fin M → Z) => (p.1, p.2 k))
    (continuous_fst.prodMk ((continuous_apply k).comp continuous_snd)).continuousOn
    fun p (hp : p ∈ Sb ×ˢ univ) => ⟨hp.1, mem_univ _⟩

lemma continuousOn_prod_slots {M : ℕ} {φ : ℝ → Z → ℝ} {Sb : Set ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Sb ×ˢ univ)) (u : Finset (Fin M)) :
    ContinuousOn (fun p : ℝ × (Fin M → Z) => ∏ l ∈ u, φ p.1 (p.2 l)) (Sb ×ˢ univ) :=
  continuousOn_finset_prod _ fun l _ => continuousOn_comp_slot hφ l

lemma continuousOn_pr0 {M : ℕ} {s : ℝ → Z → ℝ} {Sb : Set ℝ} (hs : ContinuousOn (Function.uncurry s) (Sb ×ˢ univ)) :
    ContinuousOn (Function.uncurry (pr0 (M := M) s)) (Sb ×ˢ univ) := by
  unfold pr0
  exact continuousOn_prod_slots hs univ

lemma continuousOn_pr1 {M : ℕ} {s s1 : ℝ → Z → ℝ} {Sb : Set ℝ}
    (hs : ContinuousOn (Function.uncurry s) (Sb ×ˢ univ)) (hs1 : ContinuousOn (Function.uncurry s1) (Sb ×ˢ univ)) :
    ContinuousOn (Function.uncurry (pr1 (M := M) s s1)) (Sb ×ˢ univ) := by
  unfold pr1
  exact continuousOn_finset_sum _ fun k _ => (continuousOn_prod_slots hs _).mul (continuousOn_comp_slot hs1 k)

lemma continuousOn_pr2 {M : ℕ} {s s1 s2 : ℝ → Z → ℝ} {Sb : Set ℝ}
    (hs : ContinuousOn (Function.uncurry s) (Sb ×ˢ univ)) (hs1 : ContinuousOn (Function.uncurry s1) (Sb ×ˢ univ))
    (hs2 : ContinuousOn (Function.uncurry s2) (Sb ×ˢ univ)) :
    ContinuousOn (Function.uncurry (pr2 (M := M) s s1 s2)) (Sb ×ˢ univ) := by
  unfold pr2
  refine continuousOn_finset_sum _ fun k _ => ?_
  exact ((continuousOn_finset_sum _ fun l _ => (continuousOn_prod_slots hs _).mul (continuousOn_comp_slot hs1 l)).mul
    (continuousOn_comp_slot hs1 k)).add ((continuousOn_prod_slots hs _).mul (continuousOn_comp_slot hs2 k))

lemma continuousOn_sl0 {s : ℝ → Z → ℝ} {Sb : Set ℝ} (hs : ContinuousOn (Function.uncurry s) (Sb ×ˢ univ))
    (hpos : ∀ t w, 0 < s t w) : ContinuousOn (Function.uncurry (sl0 s)) (Sb ×ˢ univ) := by
  unfold sl0
  exact hs.mul (hs.log fun p _ => (hpos p.1 p.2).ne')

lemma continuousOn_sl1 {s s1 : ℝ → Z → ℝ} {Sb : Set ℝ} (hs : ContinuousOn (Function.uncurry s) (Sb ×ˢ univ))
    (hs1 : ContinuousOn (Function.uncurry s1) (Sb ×ˢ univ)) (hpos : ∀ t w, 0 < s t w) :
    ContinuousOn (Function.uncurry (sl1 s s1)) (Sb ×ˢ univ) := by
  unfold sl1
  exact (hs1.mul (hs.log fun p _ => (hpos p.1 p.2).ne')).add (hs.mul (hs1.div hs fun p _ => (hpos p.1 p.2).ne'))

lemma continuousOn_sl2 {s s1 s2 : ℝ → Z → ℝ} {Sb : Set ℝ} (hs : ContinuousOn (Function.uncurry s) (Sb ×ˢ univ))
    (hs1 : ContinuousOn (Function.uncurry s1) (Sb ×ˢ univ)) (hs2 : ContinuousOn (Function.uncurry s2) (Sb ×ˢ univ))
    (hpos : ∀ t w, 0 < s t w) : ContinuousOn (Function.uncurry (sl2 s s1 s2)) (Sb ×ˢ univ) := by
  unfold sl2
  have hne : ∀ p ∈ Sb ×ˢ (univ : Set Z), s p.1 p.2 ≠ 0 := fun p _ => (hpos p.1 p.2).ne'
  exact ((hs2.mul (hs.log hne)).add (hs1.mul (hs1.div hs hne))).add ((hs1.mul (hs1.div hs hne)).add
    (hs.mul (((hs2.mul hs).sub (hs1.mul hs1)).div (hs.pow 2) fun p hp => pow_ne_zero 2 (hne p hp))))

lemma continuous_cP {φ : ℝ → Z → ℝ} {Sb : Set ℝ} (hSb : IsCompact Sb)
    (hφ : ContinuousOn (Function.uncurry φ) (Sb ×ˢ univ)) : Continuous (fun a : Sb => cP P0 φ a) := by
  haveI : CompactSpace Sb := isCompact_iff_compactSpace.1 hSb
  exact StatFormal.Wave24c.continuous_param_integral (P0 := P0) (continuous_on_sub hφ)

lemma VP_eq {M : ℕ} {pr : ℝ → (Fin M → Z) → ℝ} {Sb : Set ℝ} (hSb : IsCompact Sb)
    (hpr : ContinuousOn (Function.uncurry pr) (Sb ×ˢ univ)) {L : Z → (Fin M → Z) → ℝ}
    (hL : Continuous (Function.uncurry L)) (θ : ℝ) (hθ : θ ∈ Sb) :
    VP P0 pr L θ = ∫ t, pr θ t * (∫ z, L z t ∂P0) ∂(Measure.pi fun _ : Fin M => P0) := by
  haveI : CompactSpace Sb := isCompact_iff_compactSpace.1 hSb
  have hprc : Continuous (Function.uncurry fun (a : Sb) (t : Fin M → Z) => pr a t) := continuous_on_sub hpr
  obtain ⟨Cp, hCp0, hCp⟩ := bound_of_compact hprc
  obtain ⟨CL, hCL0, hCL⟩ := bound_of_compact hL
  have hc : Continuous (Function.uncurry fun (y : Z) (t : Fin M → Z) => pr θ t * L y t) :=
    (hprc.comp ((continuous_const (y := (⟨θ, hθ⟩ : Sb))).prodMk continuous_snd)).mul hL
  unfold VP hMean
  rw [integral_integral_swap (integrable_of_abs_le hc.measurable (C := Cp * CL) fun p => by
    show |pr θ p.2 * L p.1 p.2| ≤ _
    rw [abs_mul]
    exact mul_le_mul (hCp (⟨θ, hθ⟩, p.2)) (hCL (p.1, p.2)) (abs_nonneg _) hCp0)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  show ∫ x, pr θ t * L x t ∂P0 = pr θ t * ∫ z, L z t ∂P0
  rw [integral_const_mul]

lemma continuous_VP {M : ℕ} {pr : ℝ → (Fin M → Z) → ℝ} {Sb : Set ℝ} (hSb : IsCompact Sb)
    (hpr : ContinuousOn (Function.uncurry pr) (Sb ×ˢ univ)) {L : Z → (Fin M → Z) → ℝ}
    (hL : Continuous (Function.uncurry L)) : Continuous (fun a : Sb => VP P0 pr L a) := by
  haveI : CompactSpace Sb := isCompact_iff_compactSpace.1 hSb
  have hLsw : Continuous (Function.uncurry fun (t : Fin M → Z) (z : Z) => L z t) := hL.comp continuous_swap
  have hLb : Continuous fun t : Fin M → Z => ∫ z, L z t ∂P0 :=
    StatFormal.Wave24c.continuous_param_integral (P0 := P0) (f := fun t z => L z t) hLsw
  have hψ : Continuous (Function.uncurry fun (a : Sb) (t : Fin M → Z) => pr a t * ∫ z, L z t ∂P0) :=
    (continuous_on_sub hpr).mul (hLb.comp continuous_snd)
  have := StatFormal.Wave24c.continuous_param_integral (Z := Fin M → Z) (P0 := Measure.pi fun _ : Fin M => P0) hψ
  refine this.congr fun a => ?_
  exact (VP_eq hSb hpr hL a a.2).symm

lemma continuous_covLim {k : ℕ} {φs : Fin k → ℝ → Z → ℝ} {Sb : Set ℝ} (hSb : IsCompact Sb)
    (hφ : ∀ j, ContinuousOn (Function.uncurry (φs j)) (Sb ×ˢ univ)) {K : Z → Z → ℝ}
    (hK : Continuous (Function.uncurry K)) {Λ : (Fin k → ℝ) → ℝ} {D : Set (Fin k → ℝ)} (hΛ : ContinuousOn Λ D)
    (hDP : ∀ θ ∈ Sb, ∀ z, (fun j => eP P0 (φs j) K θ z) ∈ D) :
    Continuous (fun a : Sb => ∫ y, Λ (fun j => eP P0 (φs j) K a y) ∂P0) := by
  haveI : CompactSpace Sb := isCompact_iff_compactSpace.1 hSb
  have hePc : Continuous (fun p : Sb × Z => fun j => eP P0 (φs j) K p.1 p.2) :=
    continuous_pi fun j => continuous_eP hSb (hφ j) hK
  have hΓ : Continuous (Function.uncurry fun (a : Sb) (y : Z) => Λ (fun j => eP P0 (φs j) K a y)) :=
    hΛ.comp_continuous hePc fun p => hDP p.1 p.1.2 p.2
  exact StatFormal.Wave24c.continuous_param_integral (P0 := P0) hΓ

lemma bound_on_of_continuous {k : ℕ} {Sb : Set ℝ} (hSb : IsCompact Sb) {f : ℝ → Fin k → ℝ}
    (hf : Continuous (fun a : Sb => f a)) : ∃ R, ∀ θ ∈ Sb, ‖f θ‖ ≤ R := by
  haveI : CompactSpace Sb := isCompact_iff_compactSpace.1 hSb
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨R, fun θ hθ => hR ⟨θ, hθ⟩ (mem_univ _)⟩

end GC

end StatFormal.Wave28f
