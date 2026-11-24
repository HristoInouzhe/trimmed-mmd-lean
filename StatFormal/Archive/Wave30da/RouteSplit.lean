import StatFormal.Archive.Wave30da.Statements
import StatFormal.Archive.Wave29i.RouteSplit
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Route — wave 30da: trimmed-mmd `thm:split` in the general regime `n₂, m₂ → ∞` (untrusted)

* `wda_norm_core`: if `Ã_n ⇒ N(0,1)`, `B̃_m ⇒ N(0,1)` (independent), `R_n, R'_m → 0` in probability, and the
  weights `w_k, w'_k ∈ [0,1]` satisfy `w_k² + w'_k² = 1`, then `w_k(Ã_{n_k} + R_{n_k}) + w'_k(B̃_{m_k} + R'_{m_k}) ⇒ N(0,1)`
  for any `n_k, m_k → ∞`: along every subsequence pick a further one with `w → w₀`, `w' → w₀'` (Bolzano–Weierstrass),
  then Slutsky + independent Gaussian sums (`Foundations/CLT/TwoSample`), and conclude by the subsequence principle.
* `split_normal_any`: the one-sample asymptotic linearity of the two trimmed means (`tip0_trimLo`, applied to `h` and to
  `−h`) and the centred CLT (`clt_centered`), with `w = √(a/n)/√S`, `w' = √(b/m)/√S`, `S = a/n + b/m`.
* `split_level_any`: `ŝe/se → 1` in probability (`tip0_varLo` on each side; the ratio is a convex combination of
  `V̂_X/a` and `V̂_Y/b`), Slutsky + portmanteau (`coverage_lim`), and the frozen `Wave22c.split_level` (through the
  wave-29i `level_of_cov`); the `Q`-side variance is positive under `ass:split` by the mirror of `AssDens.var_pos`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatFormal.Wave30da

open StatFormal.Foundations.TrimmedMean StatFormal.Foundations.CLT
open StatFormal.Wave17a (sepVal)
open StatFormal.TrimmedMMD.Concentration (region)
open StatFormal.Wave29i (splitTrimLo splitTrimUp splitSE splitUQ splitAss)

section Core
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma wda_subseq {Y : ℕ → Ω → ℝ} (hY : ∀ k, AEMeasurable (Y k) μ)
    (h : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ψ : ℕ → ℕ,
      TendstoInDistribution (fun k => Y (ns (ψ k))) atTop id (fun _ => μ) (gaussianReal 0 1)) :
    TendstoInDistribution Y atTop id (fun _ => μ) (gaussianReal 0 1) where
  forall_aemeasurable := hY
  aemeasurable_limit := aemeasurable_id
  tendsto := tendsto_of_subseq_tendsto fun ns hns => by
    obtain ⟨ψ, hψ⟩ := h ns hns
    exact ⟨ψ, hψ.tendsto⟩

lemma wda_hasLaw_mul (c : ℝ) :
    HasLaw (fun x : ℝ => c * id x) (gaussianReal 0 ⟨c ^ 2, sq_nonneg _⟩) (gaussianReal 0 1) := by
  have := gaussianReal_const_mul (P := gaussianReal 0 1) (X := id) ⟨aemeasurable_id, Measure.map_id⟩ c
  rw [mul_zero, mul_one] at this
  exact this

lemma wda_norm_core {A B R R' : ℕ → Ω → ℝ} {Y : ℕ → Ω → ℝ} {n m : ℕ → ℕ} {w w' : ℕ → ℝ}
    (hA : TendstoInDistribution A atTop id (fun _ => μ) (gaussianReal 0 1))
    (hB : TendstoInDistribution B atTop id (fun _ => μ) (gaussianReal 0 1))
    (hind : ∀ a b, IndepFun (A a) (B b) μ) (hR : TIP0 μ R) (hR' : TIP0 μ R')
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hw : ∀ k, w k ∈ Icc (0 : ℝ) 1) (hw' : ∀ k, w' k ∈ Icc (0 : ℝ) 1) (hsum : ∀ k, w k ^ 2 + w' k ^ 2 = 1)
    (hYm : ∀ k, AEMeasurable (Y k) μ)
    (hY : ∀ k ω, Y k ω = w k * (A (n k) ω + R (n k) ω) + w' k * (B (m k) ω + R' (m k) ω)) :
    TendstoInDistribution Y atTop id (fun _ => μ) (gaussianReal 0 1) := by
  refine wda_subseq hYm fun ns hns => ?_
  obtain ⟨a, -, φ1, hφ1, h1⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (0 : ℝ) 1) (fun k => hw (ns k))
  obtain ⟨b, -, φ2, hφ2, h2⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (0 : ℝ) 1) (fun k => hw' (ns (φ1 k)))
  refine ⟨fun k => φ1 (φ2 k), ?_⟩
  set idx : ℕ → ℕ := fun k => ns (φ1 (φ2 k)) with hidx
  have hidxt : Tendsto idx atTop atTop := hns.comp (hφ1.tendsto_atTop.comp hφ2.tendsto_atTop)
  have hwa : Tendsto (fun k => w (idx k)) atTop (𝓝 a) := h1.comp hφ2.tendsto_atTop
  have hwb : Tendsto (fun k => w' (idx k)) atTop (𝓝 b) := h2
  have hab : a ^ 2 + b ^ 2 = 1 := by
    have hl := (hwa.pow 2).add (hwb.pow 2)
    have hc : Tendsto (fun k => w (idx k) ^ 2 + w' (idx k) ^ 2) atTop (𝓝 1) := by
      simp only [hsum]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hl hc
  have hA1 := tendstoInDistribution_mul_of_tendsto (TendstoInDistribution.comp_tendsto hA (hn.comp hidxt)) hwa
  have hB1 := tendstoInDistribution_mul_of_tendsto (TendstoInDistribution.comp_tendsto hB (hm.comp hidxt)) hwb
  have hG : HasLaw (id : ℝ → ℝ) (gaussianReal 0 (⟨a ^ 2, sq_nonneg _⟩ + ⟨b ^ 2, sq_nonneg _⟩)) (gaussianReal 0 1) := by
    have e : (⟨a ^ 2, sq_nonneg _⟩ + ⟨b ^ 2, sq_nonneg _⟩ : ℝ≥0) = 1 := NNReal.eq (by simp only [NNReal.coe_add, NNReal.coe_mk, NNReal.coe_one]; exact hab)
    rw [e]; exact ⟨aemeasurable_id, Measure.map_id⟩
  have hmain := tendstoInDistribution_add_gaussian hA1 hB1 (wda_hasLaw_mul a) (wda_hasLaw_mul b) hG
    (fun k => (hind _ _).comp (measurable_const_mul _) (measurable_const_mul _))
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hmain ?_ (fun k => hYm _)
  rw [tip0_iff]
  have hRc : TIP0 μ (fun k ω => R (n (idx k)) ω) := fun ε hε => (hR ε hε).comp (hn.comp hidxt)
  have hRc' : TIP0 μ (fun k ω => R' (m (idx k)) ω) := fun ε hε => (hR' ε hε).comp (hm.comp hidxt)
  refine ((hRc.bip_mul (bip_det hwa)).add (hRc'.bip_mul (bip_det hwb))).congr (Eventually.of_forall fun k ω => ?_)
  simp only [Function.comp_apply, Pi.sub_apply, hY, hidx]
  ring

end Core

section Split
variable {𝒳 : Type} [MeasurableSpace 𝒳] {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : ℕ → Ω → 𝒳}

lemma wda_sqrt_div_mul {a n : ℝ} (ha : 0 ≤ a) (hn : 0 < n) : √(a / n) * √n = √a := by
  rw [← Real.sqrt_mul (div_nonneg ha hn.le), div_mul_cancel₀ _ hn.ne']

/-- The per-sample algebra: `w · (Ã + (β/√a) R) = β (L − L₀)/√S`. -/
lemma wda_alg {β a n S x sx : ℝ} (hβ : 0 < β) (ha : 0 < a) (hn : 0 < n) (hS : 0 < S) :
    √(a / n) / √S * ((√n)⁻¹ * (-(√a)⁻¹ * sx) + β / √a * (√n * x + β⁻¹ * ((√n)⁻¹ * sx))) = β * x / √S := by
  have hsa : 0 < √a := Real.sqrt_pos.2 ha
  have hsn : 0 < √n := Real.sqrt_pos.2 hn
  have hsS : 0 < √S := Real.sqrt_pos.2 hS
  rw [Real.sqrt_div' _ hn.le]
  field_simp
  ring

/-- The standardised split statistic is `w(Ã + R̃) + w'(B̃ + R̃')`, and its normal limit. -/
lemma wda_normal (hX : IIDSample μ P X) (hY : IIDSample μ Q Y)
    (hXY : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {α q q' : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hP : UQ P h (1 - α) q) (hQ : UQ Q h α q')
    (ha : 0 < Var[fun x => max (q - h x) 0; P]) (hb : 0 < Var[fun x => max (h x - q') 0; Q])
    {n m : ℕ → ℕ} (hn1 : ∀ k, 1 ≤ n k) (hm1 : ∀ k, 1 ≤ m k) (hn : Tendsto n atTop atTop) (hm' : Tendsto m atTop atTop) :
    TendstoInDistribution (fun k ω => (statT X Y h (fun _ => m k) α (n k) ω - (popLo P h α q - popUp Q h α q')) /
        StatFormal.Wave30da.splitSdAny P Q h α q q' (n k) (m k)) atTop id (fun _ => μ) (gaussianReal 0 1) := by
  have hβ : 0 < 1 - α := by linarith
  set β := 1 - α with hβdef
  have hQ' : UQ Q (fun x => -h x) (1 - α) (-q') := by
    have := hQ.neg hm; simpa only [sub_sub_cancel] using this
  set g : 𝒳 → ℝ := fun x => max (q - h x) 0 with hgdef
  set g' : 𝒳 → ℝ := fun x => max (-q' - -h x) 0 with hg'def
  have hg' : g' = fun x => max (h x - q') 0 := funext fun x => by simp only [g']; ring_nf
  set a := Var[g; P] with hadef
  set b := Var[g'; Q] with hbdef
  have hb' : 0 < b := by rw [hbdef, hg']; exact hb
  have hgm : Measurable g := (hm.const_sub q).max measurable_const
  have hgm' : Measurable g' := (hm.neg.const_sub (-q')).max measurable_const
  have hB0 : ∀ x, |h x| ≤ |B| := fun x => (hB x).trans (le_abs_self B)
  have hgb : ∀ x, |g x| ≤ |q| + |B| := fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by positivity)
    have := le_abs_self q; have := neg_abs_le (h x); have := hB0 x; linarith
  have hgb' : ∀ x, |g' x| ≤ |q'| + |B| := fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by positivity)
    have := neg_abs_le q'; have := le_abs_self (h x); have := hB0 x; linarith
  have hsa : 0 < √a := Real.sqrt_pos.2 ha
  have hsb : 0 < √b := Real.sqrt_pos.2 hb'
  obtain ⟨hUm, hUi, hUid, hU2, hU0, hUv⟩ := clt_terms hX hgm hgb (-(√a)⁻¹)
  obtain ⟨hWm, hWi, hWid, hW2, hW0, hWv⟩ := clt_terms hY hgm' hgb' (-(√b)⁻¹)
  set U : ℕ → Ω → ℝ := fun i ω => -(√a)⁻¹ * (g (X i ω) - ∫ x, g x ∂P)
  set W : ℕ → Ω → ℝ := fun i ω => -(√b)⁻¹ * (g' (Y i ω) - ∫ x, g' x ∂Q)
  have hUv1 : Var[U 0; μ] = 1 := by
    rw [hUv, neg_sq, inv_pow, Real.sq_sqrt ha.le, inv_mul_cancel₀ ha.ne']
  have hWv1 : Var[W 0; μ] = 1 := by
    rw [hWv, neg_sq, inv_pow, Real.sq_sqrt hb'.le, inv_mul_cancel₀ hb'.ne']
  have hZ1 : ∀ v : ℝ, v = 1 → HasLaw (id : ℝ → ℝ) (gaussianReal 0 v.toNNReal) (gaussianReal 0 1) := by
    intro v hv; rw [hv, Real.toNNReal_one]; exact ⟨aemeasurable_id, Measure.map_id⟩
  have hA := clt_centered hU2 hUi hUid hU0 (hZ1 _ hUv1)
  have hBt := clt_centered hW2 hWi hWid hW0 (hZ1 _ hWv1)
  have hind : ∀ a' b' : ℕ, IndepFun (fun ω => (√(a' : ℝ))⁻¹ * ∑ i ∈ Finset.range a', U i ω)
      (fun ω => (√(b' : ℝ))⁻¹ * ∑ i ∈ Finset.range b', W i ω) μ := by
    intro a' b'
    have hf : Measurable fun x : ℕ → 𝒳 => (√(a' : ℝ))⁻¹ * ∑ i ∈ Finset.range a', -(√a)⁻¹ * (g (x i) - ∫ x, g x ∂P) :=
      (Finset.measurable_sum _ fun i _ => ((hgm.comp (measurable_pi_apply i)).sub_const _).const_mul _).const_mul _
    have hf' : Measurable fun x : ℕ → 𝒳 => (√(b' : ℝ))⁻¹ * ∑ i ∈ Finset.range b', -(√b)⁻¹ * (g' (x i) - ∫ x, g' x ∂Q) :=
      (Finset.measurable_sum _ fun i _ => ((hgm'.comp (measurable_pi_apply i)).sub_const _).const_mul _).const_mul _
    exact hXY.comp hf hf'
  have hR := (tip0_trimLo hX hm hα0 hα1 hP).const_mul (β / √a)
  have hR' := (tip0_trimLo hY hm.neg hα0 hα1 hQ').const_mul (β / √b)
  set S : ℕ → ℝ := fun k => a / n k + b / m k with hSdef
  have hn0 : ∀ k, (0 : ℝ) < n k := fun k => by exact_mod_cast hn1 k
  have hm0 : ∀ k, (0 : ℝ) < m k := fun k => by exact_mod_cast hm1 k
  have hS0 : ∀ k, 0 < S k := fun k => by have := hn0 k; have := hm0 k; positivity
  refine wda_norm_core (w := fun k => √(a / n k) / √(S k)) (w' := fun k => √(b / m k) / √(S k))
    hA hBt hind hR hR' hn hm' (fun k => ⟨by positivity, ?_⟩) (fun k => ⟨by positivity, ?_⟩) (fun k => ?_)
    (fun k => ?_) (fun k ω => ?_)
  · rw [div_le_one (Real.sqrt_pos.2 (hS0 k))]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (by have := hm0 k; positivity))
  · rw [div_le_one (Real.sqrt_pos.2 (hS0 k))]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (by have := hn0 k; positivity))
  · have e1 : 0 ≤ a / n k := by have := hn0 k; positivity
    have e2 : 0 ≤ b / m k := by have := hm0 k; positivity
    rw [div_pow, div_pow, Real.sq_sqrt e1, Real.sq_sqrt e2, Real.sq_sqrt (hS0 k).le, ← add_div, div_self (hS0 k).ne']
  · exact (((measurable_statT hX hY hm hα0 hα1 (fun _ => m k) (n k)).sub_const _).div_const _).aemeasurable
  · -- the algebraic identity
    have hmk : 0 < m k := hm1 k
    have hup := trimUp_eq hmk hα0 hα1 (smp Y h (m k) ω)
    have hsd : StatFormal.Wave30da.splitSdAny P Q h α q q' (n k) (m k) = √(S k) / β := by
      simp only [StatFormal.Wave30da.splitSdAny, S, hadef, hbdef, hg', hgdef]
      rfl
    have hPU : popUp Q h α q' = -(-q' - (1 - α)⁻¹ * ∫ x, max (-q' - -h x) 0 ∂Q) := by
      rw [popUp, ← hg'def, hg']; ring
    have hsX : ∑ i ∈ range (n k), U i ω = -(√a)⁻¹ * ∑ i ∈ range (n k), (g (X i ω) - ∫ x, g x ∂P) := by
      rw [mul_sum]
    have hsY : ∑ i ∈ range (m k), W i ω = -(√b)⁻¹ * ∑ i ∈ range (m k), (g' (Y i ω) - ∫ x, g' x ∂Q) := by
      rw [mul_sum]
    simp only [hsX, hsY, alRem]
    rw [hsd]
    simp only [statT, hup]
    simp only [popLo, hPU, hg'def, hgdef, smp, Pi.neg_apply]
    rw [Real.sqrt_div' a (hn0 k).le, Real.sqrt_div' b (hm0 k).le]
    have hsS : 0 < √(S k) := Real.sqrt_pos.2 (hS0 k)
    have hsn : 0 < √(n k : ℝ) := Real.sqrt_pos.2 (hn0 k)
    have hsm : 0 < √(m k : ℝ) := Real.sqrt_pos.2 (hm0 k)
    have hβne : (1 - α) ≠ 0 := by linarith
    rw [hβdef]
    field_simp
    ring

/-- The mirror of `AssDens.var_pos` on the upper side. -/
lemma wda_var_pos_up {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) {p q : ℝ}
    (hA : AssDens Q h p q) (hp : 0 < p) : 0 < Var[fun x => max (h x - q) 0; Q] := by
  obtain ⟨ε, hε, hpos⟩ := hA.mass_pos
  obtain ⟨-, h2, -⟩ := hA
  set g : 𝒳 → ℝ := fun x => max (h x - q) 0
  have hgm : Measurable g := (hm.sub_const q).max measurable_const
  have hgb : ∀ x, ‖g x‖ ≤ |q| + |B| := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by positivity)
    have := neg_abs_le q; have := le_abs_self (h x); have := (hB x).trans (le_abs_self B); linarith
  have hmem : MemLp g 2 Q := MemLp.of_bound hgm.aestronglyMeasurable _ (ae_of_all _ hgb)
  rcases (variance_nonneg g Q).eq_or_lt with h0 | h0
  · exfalso
    have hev : evariance g Q = 0 := by rw [← ofReal_variance hmem, ← h0, ENNReal.ofReal_zero]
    have hae := (evariance_eq_zero_iff hgm.aemeasurable).1 hev
    have hS1 : 0 < Q.real {x | h x ≤ q} := by linarith
    obtain ⟨x1, hx1, hgx1⟩ := exists_mem_of_ae_eq hS1 hae
    have hc0 : Q[g] = 0 := by
      rw [← hgx1]; simp only [g]; rw [max_eq_right]; simp only [mem_setOf_eq] at hx1; linarith
    have hS2 := hpos (q + ε / 4) (q + ε / 2) (by linarith) (by linarith) (by linarith)
    obtain ⟨x2, hx2, hgx2⟩ := exists_mem_of_ae_eq hS2 hae
    simp only [Set.mem_ofPred_eq, Set.mem_Ioc] at hx2
    have : 0 < g x2 := lt_of_lt_of_le (by linarith [hx2.1]) (le_max_left _ _)
    rw [hgx2, hc0] at this
    exact lt_irrefl _ this
  · exact h0

end Split

open StatFormal.TrimmedMMD.Concentration (region) in
theorem split_normal_any : Claims.split_normal_any := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' α q q' f Ω _ μ _ X Y n m hφ hκ hα0 hα1 hP hQ ha hb hXm hYm hXi hYi hXY hXl hYl
    hn1 hm1 hn hm
  refine ⟨_, StatFormal.Wave29i.sep_eq_of_uq hφ hκ hα0 hα1 hP hQ, ?_⟩
  exact wda_normal ⟨hXm, hXi, hXl⟩ ⟨hYm, hYi, hYl⟩ hXY (measurable_inner_comp hφ f) (abs_inner_le hκ f) hα0 hα1
    hP hQ ha hb hn1 hm1 hn hm

theorem split_level_any : Claims.split_level_any := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' α q q' δ z f Ω _ μ _ X Y n m hφ hκ hα0 hα1 hP hQ hXm hYm hXi hYi hXY hXl hYl
    hn1 hm1 hn hm hz
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  set h : 𝒳 → ℝ := fun x => ⟪f, φ x⟫ with hhdef
  have hhm : Measurable h := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  have hβ : 0 < 1 - α := by linarith
  have hPu : UQ P h (1 - α) q := AssDens.uq hhm hP
  have hQu : UQ Q h α q' := AssDens.uq hhm hQ
  have ha : 0 < Var[fun x => max (q - h x) 0; P] := AssDens.var_pos hhm hB hP (by linarith)
  have hb : 0 < Var[fun x => max (h x - q') 0; Q] := wda_var_pos_up hhm hB hQ hα0
  have hQ' : UQ Q (fun x => -h x) (1 - α) (-q') := by
    have := hQu.neg hhm; simpa only [sub_sub_cancel] using this
  have hnorm := wda_normal hX hY hXY hhm hB hα0.le hα1 hPu hQu ha hb hn1 hm1 hn hm
  set a := Var[fun x => max (q - h x) 0; P]
  set b := Var[fun x => max (h x - q') 0; Q]
  have hg' : (fun x => max (-q' - -h x) 0) = fun x => max (h x - q') 0 := funext fun x => by ring_nf
  set sd : ℕ → ℝ := fun k => StatFormal.Wave30da.splitSdAny P Q h α q q' (n k) (m k) with hsddef
  set se : ℕ → Ω → ℝ := fun k ω => splitSE (n k) (m k) α (fun i => h (X i ω)) (fun j => h (Y j ω)) with hsedef
  have hn0 : ∀ k, (0 : ℝ) < n k := fun k => by exact_mod_cast hn1 k
  have hm0 : ∀ k, (0 : ℝ) < m k := fun k => by exact_mod_cast hm1 k
  have hsd0 : ∀ k, 0 < sd k := fun k => by
    have := hn0 k; have := hm0 k
    exact div_pos (Real.sqrt_pos.2 (by positivity)) hβ
  -- consistency of the standard error ratio
  have h1 := tip0_varLo hX hhm hB hα0.le hα1 hPu
  have h2 := tip0_varLo (h := fun x => -h x) hY hhm.neg (B := ‖f‖ * κ') (fun x => by rw [abs_neg]; exact hB x)
    hα0.le hα1 hQ'
  rw [hg'] at h2
  have h1n : TIP0 μ (fun k ω => varLo (n k) α (smp X h (n k) ω) - a) := fun ε hε => (h1 ε hε).comp hn
  have h2m : TIP0 μ (fun k ω => varLo (m k) α (smp Y (fun x => -h x) (m k) ω) - b) := fun ε hε => (h2 ε hε).comp hm
  have hD : TIP0 μ (fun k ω => (varLo (n k) α (smp X h (n k) ω) / n k + varLo (m k) α (smp Y (fun x => -h x) (m k) ω) / m k) /
      (a / n k + b / m k) - 1) := by
    refine TIP0.of_dominated ((h1n.const_mul a⁻¹).abs'.add (h2m.const_mul b⁻¹).abs') (Bad := fun _ => ∅) (by simp)
      (Eventually.of_forall fun k ω _ => ?_)
    set u := varLo (n k) α (smp X h (n k) ω)
    set v := varLo (m k) α (smp Y (fun x => -h x) (m k) ω)
    have hnk := hn0 k; have hmk := hm0 k
    have hS : 0 < a / n k + b / m k := by positivity
    have e : (u / n k + v / m k) / (a / n k + b / m k) - 1 =
        (a / n k) / (a / n k + b / m k) * (a⁻¹ * (u - a)) + (b / m k) / (a / n k + b / m k) * (b⁻¹ * (v - b)) := by
      field_simp; ring
    have hθ1 : (a / n k) / (a / n k + b / m k) ≤ 1 := (div_le_one hS).2 (le_add_of_nonneg_right (by positivity))
    have hθ2 : (b / m k) / (a / n k + b / m k) ≤ 1 := (div_le_one hS).2 (le_add_of_nonneg_left (by positivity))
    rw [e, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |a⁻¹ * (u - a)| + |b⁻¹ * (v - b)|)]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a / n k) / (a / n k + b / m k))]
      exact mul_le_of_le_one_left (abs_nonneg _) hθ1
    · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b / m k) / (a / n k + b / m k))]
      exact mul_le_of_le_one_left (abs_nonneg _) hθ2
  have hratio : TIP0 μ (fun k ω => se k ω / sd k - 1) := by
    refine TIP0.of_dominated hD (Bad := fun _ => ∅) (by simp) (Eventually.of_forall fun k ω _ => ?_)
    have hnk := hn0 k; have hmk := hm0 k
    have hS : 0 < a / n k + b / m k := by positivity
    have e : se k ω / sd k = √((varLo (n k) α (smp X h (n k) ω) / n k +
        varLo (m k) α (smp Y (fun x => -h x) (m k) ω) / m k) / (a / n k + b / m k)) := by
      have e0 : se k ω / sd k = √(varLo (n k) α (smp X h (n k) ω) / n k +
          varLo (m k) α (smp Y (fun x => -h x) (m k) ω) / m k) / (1 - α) / (√(a / n k + b / m k) / (1 - α)) := rfl
      rw [e0, Real.sqrt_div' _ hS.le, div_div_div_cancel_right₀ hβ.ne']
    rw [e]
    have := abs_sqrt_sub_sqrt_le (a := (varLo (n k) α (smp X h (n k) ω) / n k +
        varLo (m k) α (smp Y (fun x => -h x) (m k) ω) / m k) / (a / n k + b / m k)) one_pos
    rw [Real.sqrt_one, div_one] at this
    exact this
  -- coverage
  set Tst : ℕ → Ω → ℝ := fun k ω => statT X Y h (fun _ => m k) α (n k) ω with hTst
  set T₀ := popLo P h α q - popUp Q h α q'
  have hsep := StatFormal.Wave29i.sep_eq_of_uq hφ hκ hα0.le hα1 hPu hQu
  have hsem : ∀ k, Measurable (fun ω => se k ω / sd k) := fun k =>
    (measurable_seHat hX hY hhm α (fun _ => m k) (n k)).div_const _
  have hnorm' : TendstoInDistribution (fun k ω => (Tst k ω - T₀) / sd k) atTop id (fun _ => μ)
      (gaussianReal 0 ((1 : ℝ) ^ 2).toNNReal) := by
    rw [one_pow, Real.toNNReal_one]; exact hnorm
  have hcov0 := coverage_lim one_pos hnorm' hratio hsem z
  have hcov : Tendsto (fun k => μ.real {ω | ((Tst k ω - z * se k ω : ℝ) : EReal) ≤
      sepVal f (region φ α P) (region φ α Q)}) atTop (𝓝 ((gaussianReal 0 1).real (Iic z))) := by
    refine hcov0.congr fun k => ?_
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, hsep, EReal.coe_le_coe_iff]
    have hs := hsd0 k
    rw [show (Tst k ω - T₀) / sd k - z * (se k ω / sd k) = (Tst k ω - z * se k ω - T₀) / sd k by field_simp; ring,
      div_le_iff₀ hs, zero_mul, sub_nonpos]
  have hTm : ∀ k, Measurable (fun ω => Tst k ω - z * se k ω) := fun k =>
    (measurable_statT hX hY hhm hα0.le hα1 (fun _ => m k) (n k)).sub
      ((measurable_seHat hX hY hhm α (fun _ => m k) (n k)).const_mul z)
  exact StatFormal.Wave29i.level_of_cov StatFormal.Wave22c.split_level hφ hκ hα0.le hα1 hPu hQu hTm hz hcov

end StatFormal.Wave30da
