import StatFormal.Wave30tz.Statements
import StatFormal.Wave30tq.Proofs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

set_option linter.style.longLine false

/-!
# Wave 30tz route: the elementary claims — untrusted

* `log_lower_route` (Lemma 5, the Taylor step): `g(x) = log(1+x) − x + x²/(2(1−a)²)` has `g(0) = 0` and
  `g'(x) = x[1/(1−a)² − 1/(1+x)]`, `≥ 0` on `[0,∞)` and `≤ 0` on `[−a,0]` (`1 + x ≥ 1 − a ≥ (1−a)²`);
* `fractions_bounds_route` (§1 "Fractions"): the running mean is a convex combination of earlier `Z_l − α` and `0`;
* `theta_mono_route` (Lemma 4, freeze item 5): termwise monotonicity, `β` increasing on `[0,1)`;
* `grid_events_route`, `mesh_point_route` (freeze item 9): finite combinatorics of `alphaLo`, `gridBelow`, `gridMesh`;
* `crit_identity_route`, `crit_emp_route`, `crit_uniform_route` (Lemma 2): constants cancel for probability measures;
  integrals against `empirical` are averages; the hinge maps are constant outside `[−κ, κ]`;
* `pop_ramp_route` (Lemma 1, abstract form): through the certified `Wave30tq.lem2_1`, `Wave30tq.lem2_2`;
  `pop_ramp_freeze_false_route`: the Dirac counterexample;
* `epsN_le_exp`, `epsN_rate` (quantitative): for `0 < L ≤ η N` with `η = ϱ²/(8C²)`, `C = 1 + 4(1+α)²/σ²_min`, and every
  `ϱ' ≥ ϱ`: `ε_N(ϱ') ≤ exp(−σ²_min ϱ² N/32)`; `epsN_small_route`: the second conjunct of `Claims.bet_power_frac`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave30tz

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30ty StatFormal.Wave30tp
open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.ZeroSet

/-! ### Lemma 5, the Taylor step -/

theorem log_lower_route : Claims.log_lower := by
  intro a x ha0 ha1 hx
  set c : ℝ := (1 - a) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 - a := by nlinarith
  set g : ℝ → ℝ := fun y => Real.log (1 + y) - y + y ^ 2 / (2 * c) with hg
  have hderiv : ∀ y, 0 < 1 + y → HasDerivAt g (y * (1 / c - 1 / (1 + y))) y := by
    intro y hy
    have h2 : HasDerivAt (fun y : ℝ => 1 + y) 1 y := by simpa using (hasDerivAt_id y).const_add 1
    have h3 := ((h2.log hy.ne').sub (hasDerivAt_id' y)).add ((hasDerivAt_pow 2 y).div_const (2 * c))
    convert h3 using 1
    field_simp
    ring
  have hcont : ∀ y, 0 < 1 + y → ContinuousAt g y := fun y hy => (hderiv y hy).continuousAt
  have hg0 : g 0 = 0 := by simp [hg]
  have hgx : 0 ≤ g x := by
    rcases le_total 0 x with hx0 | hx0
    · have hmono : MonotoneOn g (Ici 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
        · exact fun y hy => (hcont y (by linarith [mem_Ici.1 hy])).continuousWithinAt
        · rw [interior_Ici]
          exact fun y hy => (hderiv y (by linarith [mem_Ioi.1 hy])).differentiableAt.differentiableWithinAt
        · rw [interior_Ici]
          intro y hy
          have hy0 : 0 < y := hy
          rw [(hderiv y (by linarith)).deriv]
          have h1 : 1 / (1 + y) ≤ 1 / c := one_div_le_one_div_of_le hc0 (by linarith)
          exact mul_nonneg hy0.le (by linarith)
      have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hx0) hx0
      linarith
    · have hanti : AntitoneOn g (Icc (-a) 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc (-a) 0) ?_ ?_ ?_
        · exact fun y hy => (hcont y (by linarith [hy.1])).continuousWithinAt
        · rw [interior_Icc]
          exact fun y hy => (hderiv y (by linarith [hy.1])).differentiableAt.differentiableWithinAt
        · rw [interior_Icc]
          intro y hy
          rw [(hderiv y (by linarith [hy.1])).deriv]
          have h1 : 1 / (1 + y) ≤ 1 / c := one_div_le_one_div_of_le hc0 (by linarith [hy.1])
          exact mul_nonpos_of_nonpos_of_nonneg hy.2.le (by linarith)
      have := hanti ⟨hx, hx0⟩ ⟨by linarith, le_rfl⟩ hx0
      linarith
  simp only [hg] at hgx
  linarith

/-! ### §1, "Fractions" -/

theorem fractions_bounds_route : Claims.fractions_bounds := by
  intro K Z S w0 s0 α s2 lmax L N hw0 hs0 hs04 hα0 hα1 hZ hs2 hL
  have hsq : ∀ i ∈ S, (Z i - α - (∑ l ∈ S.filter (· < i), (Z l - α)) /
      (w0 + (S.filter (· < i)).card)) ^ 2 ≤ 4 := by
    intro i _
    set T := S.filter (· < i)
    have hk : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    have hden : 0 < w0 + T.card := by linarith
    have hsum_le : ∑ l ∈ T, (Z l - α) ≤ T.card * (1 - α) := by
      have := Finset.sum_le_sum (s := T) (fun l _ => (show Z l - α ≤ 1 - α by linarith [(hZ l).2]))
      rwa [Finset.sum_const, nsmul_eq_mul] at this
    have hsum_ge : (T.card : ℝ) * (-1 - α) ≤ ∑ l ∈ T, (Z l - α) := by
      have := Finset.sum_le_sum (s := T) (fun l _ => (show -1 - α ≤ Z l - α by linarith [(hZ l).1]))
      rwa [Finset.sum_const, nsmul_eq_mul] at this
    have hw1 : 0 ≤ w0 * (1 - α) := mul_nonneg hw0.le (by linarith)
    have hw2 : 0 ≤ w0 * (1 + α) := mul_nonneg hw0.le (by linarith)
    have hμ1 : (∑ l ∈ T, (Z l - α)) / (w0 + T.card) ≤ 1 - α := by
      rw [div_le_iff₀ hden]; nlinarith
    have hμ2 : -1 - α ≤ (∑ l ∈ T, (Z l - α)) / (w0 + T.card) := by
      rw [le_div_iff₀ hden]; nlinarith
    have hZi := hZ i
    have e1 : Z i - α - (∑ l ∈ T, (Z l - α)) / (w0 + T.card) ≤ 2 := by linarith [hZi.2]
    have e2 : -2 ≤ Z i - α - (∑ l ∈ T, (Z l - α)) / (w0 + T.card) := by linarith [hZi.1]
    nlinarith [mul_nonneg (sub_nonneg.2 e1) (sub_nonneg.2 e2)]
  have hden : 0 < w0 + S.card := by have : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _; linarith
  have hR0 : 0 ≤ (w0 * s0 + ∑ i ∈ S, (Z i - α - (∑ l ∈ S.filter (· < i), (Z l - α)) /
      (w0 + (S.filter (· < i)).card)) ^ 2) / (w0 + S.card) :=
    div_nonneg (add_nonneg (mul_nonneg hw0.le hs0) (Finset.sum_nonneg fun i _ => sq_nonneg _)) hden.le
  have hR4 : (w0 * s0 + ∑ i ∈ S, (Z i - α - (∑ l ∈ S.filter (· < i), (Z l - α)) /
      (w0 + (S.filter (· < i)).card)) ^ 2) / (w0 + S.card) ≤ 4 := by
    rw [div_le_iff₀ hden]
    have h1 := Finset.sum_le_sum hsq
    simp only [Finset.sum_const, nsmul_eq_mul] at h1
    nlinarith
  refine ⟨hR0, hR4, ?_⟩
  intro σ2 hσ2
  have hσs : s2 ≤ σ2 := hσ2 ▸ le_max_left _ _
  have hσ4 : σ2 ≤ max s2 4 := hσ2 ▸ max_le_max le_rfl hR4
  have hσ0 : 0 < σ2 := lt_of_lt_of_le hs2 hσs
  have hL2 : 0 ≤ 2 * L := by linarith
  refine ⟨hσs, hσ4, ?_, ?_⟩
  · unfold lamLo
    refine min_le_min_left _ (Real.sqrt_le_sqrt ?_)
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
      exact div_le_div_of_nonneg_left hL2 (mul_pos hN' hσ0) (mul_le_mul_of_nonneg_left hσ4 hN'.le)
  · unfold lamHi
    refine min_le_min_left _ (Real.sqrt_le_sqrt ?_)
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
      exact div_le_div_of_nonneg_left hL2 (mul_pos hN' hs2) (mul_le_mul_of_nonneg_left hσs hN'.le)

/-! ### Lemma 4, freeze item 5 -/

theorem theta_mono_route : Claims.theta_mono := by
  intro α α' D D' Zp Zm κ Dφ r hα0 hαα hα1 hZp hZm hDφ hr hD hDD
  have hα1' : α < 1 := lt_of_le_of_lt hαα hα1
  have hb : beta α ≤ beta α' := by
    unfold beta; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hb0 : 0 < beta α := Wave30tq.beta_pos hα1'
  have hden : 0 < D - beta α' * Zm := by linarith
  have hden' : D - beta α' * Zm ≤ D' - beta α * Zm := by nlinarith
  have hnum : beta α ^ 2 * κ ^ 2 * r ≤ beta α' ^ 2 * κ ^ 2 * r := by
    have h1 : beta α ^ 2 ≤ beta α' ^ 2 := pow_le_pow_left₀ hb0.le hb 2
    have h2 : 0 ≤ κ ^ 2 * r := mul_nonneg (sq_nonneg _) hr
    nlinarith
  have hfrac : beta α ^ 2 * κ ^ 2 * r / (D' - beta α * Zm) ≤
      beta α' ^ 2 * κ ^ 2 * r / (D - beta α' * Zm) :=
    div_le_div₀ (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hr) hnum hden hden'
  unfold fitTheta
  have h1 : beta α * (Zp + Zm) ≤ beta α' * (Zp + Zm) := mul_le_mul_of_nonneg_right hb (by linarith)
  have h2 : beta α * Dφ * r ≤ beta α' * Dφ * r :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hDφ) hr
  linarith

/-! ### The assembly, freeze item 9 -/

theorem grid_events_route : Claims.grid_events := by
  classical
  intro J α rej a hgrid
  have hgb0 : 0 ≤ gridBelow α a := by
    unfold gridBelow
    split_ifs with h
    · obtain ⟨j, hj⟩ := h
      exact (hgrid.2 j).1.trans (Finset.le_sup' α hj)
    · exact le_rfl
  constructor
  · intro hlt
    unfold StatFormal.TrimmedMMD.Lower.alphaLo at hlt
    split_ifs at hlt with hF
    · rw [Finset.lt_sup'_iff] at hlt
      obtain ⟨j₁, hj₁F, hj₁⟩ := hlt
      have hj₁mem : ∀ i ≤ j₁, rej i := (Finset.mem_filter.1 hj₁F).2
      have ha : a ≤ α j₁ := by
        by_contra hcon
        rw [not_le] at hcon
        have : α j₁ ≤ gridBelow α a := by
          unfold gridBelow
          split_ifs with hG
          · exact (Finset.le_sup'_iff hG).2 ⟨j₁, by simpa using hcon, le_rfl⟩
          · exact absurd ⟨j₁, by simpa using hcon⟩ hG
        linarith
      let T := Finset.univ.filter (fun i => a ≤ α i)
      have hT : T.Nonempty := ⟨j₁, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩⟩
      refine ⟨T.min' hT, (Finset.mem_filter.1 (T.min'_mem hT)).2, ?_, ?_⟩
      · intro i hi
        by_contra hcon
        rw [not_lt] at hcon
        have := T.min'_le i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon⟩)
        exact absurd hi (not_lt.2 this)
      · exact hj₁mem _ (T.min'_le j₁ (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩))
    · linarith
  · intro i hi
    by_contra hcon'
    have hcon : ∀ j ≤ i, rej j := fun j hj => by_contra fun hr => hcon' ⟨j, hj, hr⟩
    unfold StatFormal.TrimmedMMD.Lower.alphaLo at hi
    split_ifs at hi with hF
    · rw [Finset.sup'_lt_iff] at hi
      exact lt_irrefl _ (hi i (by simpa using hcon))
    · exact hF ⟨i, by simpa using hcon⟩

theorem mesh_point_route : Claims.mesh_point := by
  intro J α a _ ha0 ha1
  have hSfin : (insert (0 : ℝ) (range α)).Finite := (Set.finite_range α).insert 0
  have hSne : (insert (0 : ℝ) (range α)).Nonempty := ⟨0, Set.mem_insert _ _⟩
  have hbdd : BddAbove (range fun b : Ico (0 : ℝ) 1 => Metric.infDist (b : ℝ) (insert 0 (range α))) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨b, rfl⟩
    have := Metric.infDist_le_dist_of_mem (x := (b : ℝ)) (Set.mem_insert (0 : ℝ) (range α))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg b.2.1] at this
    exact this.trans b.2.2.le
  have hh0 : 0 ≤ gridMesh α := Real.iSup_nonneg fun _ => Metric.infDist_nonneg
  by_cases hcase : a ≤ 2 * gridMesh α
  · exact ⟨0, Set.mem_insert _ _, ha0, by linarith⟩
  · rw [not_le] at hcase
    have hmem : a - gridMesh α ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hle : Metric.infDist (a - gridMesh α) (insert 0 (range α)) ≤ gridMesh α :=
      le_ciSup hbdd (⟨a - gridMesh α, hmem⟩ : Ico (0 : ℝ) 1)
    obtain ⟨s, hs, hsd⟩ := hSfin.isCompact.exists_infDist_eq_dist hSne (a - gridMesh α)
    rw [hsd, Real.dist_eq] at hle
    have hle' := abs_le.1 hle
    exact ⟨s, hs, by linarith [hle'.1], by linarith [hle'.2]⟩

/-! ### Lemma 2 -/

namespace Elem

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- Hinges of a bounded measurable function are integrable against finite measures. -/
lemma integrable_hinge {μ : Measure 𝒳} [IsFiniteMeasure μ] {f : 𝒳 → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (t : ℝ) :
    Integrable (fun x => max (t - f x) 0) μ ∧ Integrable (fun x => max (f x - t) 0) μ := by
  constructor
  · refine Wave30tq.integrable_of_abs_le ((measurable_const.sub hf).max measurable_const) (C := |t| + C) fun x => ?_
    have := abs_le.1 (hC x)
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [le_abs_self t]) (by linarith [abs_nonneg t, abs_nonneg (f x), hC x])
  · refine Wave30tq.integrable_of_abs_le ((hf.sub measurable_const).max measurable_const) (C := C + |t|) fun x => ?_
    have := abs_le.1 (hC x)
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [neg_abs_le t]) (by linarith [abs_nonneg t, abs_nonneg (f x), hC x])

/-- `θ(f; t, u) = t − β E_P(t − f)₊ − (u + β E_Q(f − u)₊)` for probability measures. -/
lemma theta_eq (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (α : ℝ) {f : 𝒳 → ℝ}
    {t u : ℝ} (hP : Integrable (fun x => max (t - f x) 0) P) (hQ : Integrable (fun x => max (f x - u) 0) Q) :
    theta P Q α f t u =
      t - beta α * (∫ x, max (t - f x) 0 ∂P) - (u + beta α * ∫ y, max (f y - u) 0 ∂Q) := by
  unfold theta psiS
  rw [integral_sub (integrable_const _) (hP.const_mul _), integral_add (integrable_const _) (hQ.const_mul _),
    integral_const, integral_const, probReal_univ, probReal_univ, one_smul, one_smul,
    integral_const_mul, integral_const_mul]

/-- Every measurable real function is integrable against a Dirac mass. -/
lemma integrable_dirac_of_measurable {g : 𝒳 → ℝ} (hg : Measurable g) (a : 𝒳) :
    Integrable g (Measure.dirac a) := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_dirac' a hg.enorm]
  exact enorm_lt_top

/-- Integrals against `empirical x` are averages (measurable integrands, no boundedness needed). -/
lemma integral_empirical_of_measurable {n : ℕ} (x : Fin n → 𝒳) {g : 𝒳 → ℝ} (hg : Measurable g) :
    ∫ z, g z ∂(empirical x) = (n : ℝ)⁻¹ * ∑ i, g (x i) := by
  unfold empirical
  rw [integral_finsetSum_measure fun i _ =>
    (integrable_dirac_of_measurable hg (x i)).smul_measure ENNReal.ofReal_ne_top]
  simp_rw [integral_smul_measure, integral_dirac' _ _ hg.stronglyMeasurable]
  rw [ENNReal.toReal_ofReal (by positivity), Finset.mul_sum]
  simp [smul_eq_mul, one_div]

/-- `(P − P_n)(s − h) = P_n h − P h`: the hinge map is affine (hence constant) past the range. -/
lemma devPop_const_sub (P : Measure 𝒳) [IsProbabilityMeasure P] {n : ℕ} (hn : 1 ≤ n) (x : Fin n → 𝒳)
    {h : 𝒳 → ℝ} (hh : Integrable h P) (s : ℝ) :
    devPop P x (fun z => s - h z) = (n : ℝ)⁻¹ * ∑ i, h (x i) - ∫ z, h z ∂P := by
  have hn' : (n : ℝ) ≠ 0 := by have : (0 : ℝ) < n := Nat.cast_pos.2 hn; exact this.ne'
  unfold devPop
  rw [integral_sub (integrable_const _) hh, integral_const, probReal_univ, one_smul,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- `(P − P_n)(h − s) = P h − P_n h`. -/
lemma devPop_sub_const (P : Measure 𝒳) [IsProbabilityMeasure P] {n : ℕ} (hn : 1 ≤ n) (x : Fin n → 𝒳)
    {h : 𝒳 → ℝ} (hh : Integrable h P) (s : ℝ) :
    devPop P x (fun z => h z - s) = ∫ z, h z ∂P - (n : ℝ)⁻¹ * ∑ i, h (x i) := by
  have hn' : (n : ℝ) ≠ 0 := by have : (0 : ℝ) < n := Nat.cast_pos.2 hn; exact this.ne'
  unfold devPop
  rw [integral_sub hh (integrable_const _), integral_const, probReal_univ, one_smul,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- `(P − P_n) g ≤ B` for `0 ≤ g ≤ B`. -/
lemma devPop_le (P : Measure 𝒳) [IsProbabilityMeasure P] {n : ℕ} (x : Fin n → 𝒳) {g : 𝒳 → ℝ} {B : ℝ}
    (hg0 : ∀ z, 0 ≤ g z) (hgB : ∀ z, g z ≤ B) : devPop P x g ≤ B := by
  unfold devPop
  have h1 : ∫ z, g z ∂P ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := g) (C := B)
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 z)]; exact hgB z)
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have h2 : 0 ≤ (n : ℝ)⁻¹ * ∑ i, g (x i) := mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hg0 _)
  linarith

end Elem

open Elem

theorem crit_identity_route : Claims.crit_identity := by
  intro 𝒳 _ P Q P' Q' _ _ _ _ α f t u hf ⟨C, hC⟩
  rw [theta_eq P Q α (integrable_hinge hf hC t).1 (integrable_hinge hf hC u).2,
    theta_eq P' Q' α (integrable_hinge hf hC t).1 (integrable_hinge hf hC u).2]
  ring

theorem crit_emp_route : Claims.crit_emp := by
  intro 𝒳 _ n m x y α f t u hn hm hf
  have hn' : (n : ℝ) ≠ 0 := by have : (0 : ℝ) < n := Nat.cast_pos.2 hn; exact this.ne'
  have hm' : (m : ℝ) ≠ 0 := by have : (0 : ℝ) < m := Nat.cast_pos.2 hm; exact this.ne'
  unfold theta critT critU psiS
  rw [integral_empirical_of_measurable x (g := fun z => t - beta α * max (t - f z) 0) (by fun_prop),
    integral_empirical_of_measurable y (g := fun z => u + beta α * max (f z - u) 0) (by fun_prop)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, Finset.card_univ,
    Finset.card_univ, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, ← Finset.mul_sum,
    ← Finset.mul_sum]
  field_simp

theorem crit_uniform_route : Claims.crit_uniform := by
  intro 𝒳 H _ _ _ P Q _ _ φ κ α n m x y f t u hφ hκ hα0 hα1 hn hm hf
  obtain ⟨z0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ z0)
  have hβ := Wave30tq.beta_pos hα1
  -- values of a unit-ball function are in `[−κ, κ]`
  have hval : ∀ v : H, ‖v‖ ≤ 1 → ∀ z, |⟪v, φ z⟫_ℝ| ≤ κ := fun v hv z =>
    (abs_real_inner_le_norm v (φ z)).trans
      ((mul_le_mul hv (hκ z) (norm_nonneg _) zero_le_one).trans_eq (one_mul κ))
  set h : 𝒳 → ℝ := fun z => ⟪f, φ z⟫_ℝ with hhdef
  have hhm : Measurable h := (stronglyMeasurable_const.inner hφ).measurable
  have hhb : ∀ z, |h z| ≤ κ := hval f hf
  have hhP : Integrable h P := Wave30tq.integrable_of_abs_le hhm hhb
  have hhQ : Integrable h Q := Wave30tq.integrable_of_abs_le hhm hhb
  -- the identity `θ − θ_n = −β[(P − P_n)(t − h)₊ + (Q − Q_m)(h − u)₊]`
  have hident : theta P Q α h t u - (critT α (fun i => h (x i)) t - critU α (fun j => h (y j)) u) =
      -(beta α) * (devPop P x (fun z => max (t - h z) 0) + devPop Q y (fun z => max (h z - u) 0)) := by
    rw [theta_eq P Q α (integrable_hinge hhm hhb t).1 (integrable_hinge hhm hhb u).2]
    unfold critT critU devPop
    ring
  -- the hinge maps are constant outside `[−κ, κ]`
  have hTconst : ∀ s : ℝ, ∃ s₀ ∈ Icc (-κ) κ,
      devPop P x (fun z => max (s - h z) 0) = devPop P x (fun z => max (s₀ - h z) 0) := by
    intro s
    by_cases h1 : s < -κ
    · refine ⟨-κ, ⟨le_rfl, by linarith⟩, ?_⟩
      have e1 : (fun z => max (s - h z) 0) = fun _ => (0 : ℝ) :=
        funext fun z => max_eq_right (by linarith [(abs_le.1 (hhb z)).1])
      have e2 : (fun z => max (-κ - h z) 0) = fun _ => (0 : ℝ) :=
        funext fun z => max_eq_right (by linarith [(abs_le.1 (hhb z)).1])
      rw [e1, e2]
    · by_cases h2 : κ < s
      · refine ⟨κ, ⟨by linarith, le_rfl⟩, ?_⟩
        have e1 : (fun z => max (s - h z) 0) = fun z => s - h z :=
          funext fun z => max_eq_left (by linarith [(abs_le.1 (hhb z)).2])
        have e2 : (fun z => max (κ - h z) 0) = fun z => κ - h z :=
          funext fun z => max_eq_left (by linarith [(abs_le.1 (hhb z)).2])
        rw [e1, e2, devPop_const_sub P hn x hhP, devPop_const_sub P hn x hhP]
      · exact ⟨s, ⟨by linarith, by linarith⟩, rfl⟩
  have hUconst : ∀ s : ℝ, ∃ s₀ ∈ Icc (-κ) κ,
      devPop Q y (fun z => max (h z - s) 0) = devPop Q y (fun z => max (h z - s₀) 0) := by
    intro s
    by_cases h1 : s < -κ
    · refine ⟨-κ, ⟨le_rfl, by linarith⟩, ?_⟩
      have e1 : (fun z => max (h z - s) 0) = fun z => h z - s :=
        funext fun z => max_eq_left (by linarith [(abs_le.1 (hhb z)).1])
      have e2 : (fun z => max (h z - -κ) 0) = fun z => h z - -κ :=
        funext fun z => max_eq_left (by linarith [(abs_le.1 (hhb z)).1])
      rw [e1, e2, devPop_sub_const Q hm y hhQ, devPop_sub_const Q hm y hhQ]
    · by_cases h2 : κ < s
      · refine ⟨κ, ⟨by linarith, le_rfl⟩, ?_⟩
        have e1 : (fun z => max (h z - s) 0) = fun _ => (0 : ℝ) :=
          funext fun z => max_eq_right (by linarith [(abs_le.1 (hhb z)).2])
        have e2 : (fun z => max (h z - κ) 0) = fun _ => (0 : ℝ) :=
          funext fun z => max_eq_right (by linarith [(abs_le.1 (hhb z)).2])
        rw [e1, e2]
      · exact ⟨s, ⟨by linarith, by linarith⟩, rfl⟩
  -- the supremum `Z` is a genuine supremum
  have hbdd : BddAbove (range fun p : hingePar (H := H) 1 κ κ =>
      devPop P x (hOne hingePos φ p.1.1 p.1.2.1) + devPop Q y (hTwo hingePos φ p.1.1 p.1.2.2)) := by
    refine ⟨2 * κ + 2 * κ, ?_⟩
    rintro _ ⟨⟨⟨v, a, b⟩, hp⟩, rfl⟩
    obtain ⟨hv, ha, hb⟩ := hp
    have hvb := hval v hv
    have h1 : devPop P x (hOne hingePos φ v a) ≤ 2 * κ := by
      refine devPop_le P x (fun z => le_max_right _ _) fun z => ?_
      have := abs_le.1 (hvb z)
      have := abs_le.1 ha
      exact max_le (by linarith) (by linarith)
    have h2 : devPop Q y (hTwo hingePos φ v b) ≤ 2 * κ := by
      refine devPop_le Q y (fun z => le_max_right _ _) fun z => ?_
      have := abs_le.1 (hvb z)
      have := abs_le.1 hb
      exact max_le (by linarith) (by linarith)
    exact add_le_add h1 h2
  obtain ⟨t₀, ht₀, hT⟩ := hTconst t
  obtain ⟨u₀, hu₀, hU⟩ := hUconst u
  refine ⟨?_, ⟨t₀, ht₀, hT⟩⟩
  have hZ : devPop P x (fun z => max (t₀ - h z) 0) + devPop Q y (fun z => max (h z - u₀) 0) ≤
      hingeZ P Q φ hingePos hingePos 1 κ κ (x, y) :=
    le_ciSup hbdd ⟨(f, t₀, u₀), hf, abs_le.2 ⟨ht₀.1, ht₀.2⟩, abs_le.2 ⟨hu₀.1, hu₀.2⟩⟩
  rw [hident, hT, hU]
  exact mul_le_mul_of_nonpos_left hZ (neg_nonpos.2 hβ.le)

/-! ### Lemma 1, abstract form -/

theorem pop_ramp_route : Claims.pop_ramp := by
  intro 𝒳 _ P Q _ _ α f t u Dφ d hf hfb hα0 hα1 hD ht hu hd hθ
  obtain ⟨C, hC⟩ := hfb
  have := nonempty_of_isProbabilityMeasure P
  have hβ := Wave30tq.beta_pos hα1
  have hθle : theta P Q α f t u ≤ t - u := by
    rw [theta_eq P Q α (integrable_hinge hf hC t).1 (integrable_hinge hf hC u).2]
    have h1 : 0 ≤ ∫ x, max (t - f x) 0 ∂P := integral_nonneg fun _ => le_max_right _ _
    have h2 : 0 ≤ ∫ y, max (f y - u) 0 ∂Q := integral_nonneg fun _ => le_max_right _ _
    nlinarith
  have hut : u < t := by linarith
  have hsup : (⨆ x, f x) - (⨅ x, f x) ≤ Dφ := by
    have : (⨆ x, f x) - Dφ ≤ ⨅ x, f x := le_ciInf fun x' => by
      have : (⨆ x, f x) ≤ Dφ + f x' := ciSup_le fun x => by linarith [hD x x']
      linarith
    linarith
  have htu : t - u ≤ Dφ := by linarith
  refine ⟨hut, htu, ?_⟩
  obtain ⟨-, h21⟩ := StatFormal.Wave30tq.lem2_1 𝒳 P Q α f t u hf hα0 hα1 hut
  obtain ⟨h22, h22'⟩ := StatFormal.Wave30tq.lem2_2 𝒳 P Q α f t u hf ⟨C, hC⟩ hα0 hα1 hut
  have hclip : d ≤ beta α * (t - u) * ((∫ x, ramp f t u x ∂P) - (∫ y, ramp f t u y ∂Q) - α) := by
    rw [← h21]; linarith
  have hpos : 0 < beta α * (t - u) := mul_pos hβ (by linarith)
  calc d / (beta α * Dφ) ≤ d / (beta α * (t - u)) :=
        div_le_div_of_nonneg_left hd.le hpos (mul_le_mul_of_nonneg_left htu hβ.le)
    _ ≤ _ := by rw [div_le_iff₀ hpos]; linarith

theorem pop_ramp_freeze_false_route : Claims.pop_ramp_freeze_false := by
  intro hall
  have hf : Measurable (fun x : ℝ => min (max x 0) 1) := (measurable_id.max measurable_const).min measurable_const
  have hb : ∃ C, ∀ x : ℝ, |min (max x 0) 1| ≤ C := ⟨1, fun x => by
    rw [abs_le]
    exact ⟨by linarith [le_min (le_max_right x 0) (zero_le_one' ℝ)], min_le_right _ _⟩⟩
  have hD : ∀ x x' : ℝ, min (max x 0) 1 - min (max x' 0) 1 ≤ 1 := fun x x' => by
    have := min_le_right (max x 0) 1
    have := le_min (le_max_right x' 0) (zero_le_one' ℝ)
    linarith
  have hβ : beta 0 = 1 := by simp [beta]
  have hθ : theta (Measure.dirac (1 : ℝ)) (Measure.dirac (0 : ℝ)) 0 (fun x : ℝ => min (max x 0) 1) 2 0 = 1 := by
    unfold theta psiS
    rw [integral_dirac, integral_dirac, hβ]
    norm_num
  have key := hall ℝ (Measure.dirac 1) (Measure.dirac 0) 0 (fun x => min (max x 0) 1) 2 0 1 hf hb le_rfl
    one_pos hD (by rw [hθ]; norm_num)
  rw [hθ, hβ, integral_dirac, integral_dirac] at key
  unfold ramp clip at key
  norm_num at key

/-! ### Lemma 5 for `eq:fractions`: `ε_N → 0` (quantitative) -/

/-- **Quantitative form.** With `C = 1 + 4(1+α)²/σ²_min` and `η = ϱ²/(8C²)`: for every `N`, every `0 < L ≤ ηN` and every
`ϱ' ≥ ϱ`, `ε_N(ϱ') ≤ exp(−σ²_min ϱ² N/32)`. (Indeed `LC ≤ ϱ√(NL/2)/2`, so the positive part is `≥ ϱ√(NL/2)/2`.) -/
theorem epsN_le_exp (s2 α ρ : ℝ) (hs2 : 0 < s2) (hα : 0 ≤ α) (hρ : 0 < ρ) (N : ℕ) (L ρ' : ℝ) (hL : 0 < L)
    (hLN : L ≤ ρ ^ 2 / (8 * (1 + 4 * (1 + α) ^ 2 / s2) ^ 2) * N) (hρρ' : ρ ≤ ρ') :
    epsN s2 α L N ρ' ≤ Real.exp (-(s2 * ρ ^ 2 * N / 32)) := by
  set C := 1 + 4 * (1 + α) ^ 2 / s2 with hC
  have hC1 : 1 ≤ C := by have : 0 ≤ 4 * (1 + α) ^ 2 / s2 := by positivity
                         linarith
  have hC0 : 0 < C := by linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold epsN
  set s := √(N * L / 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2' : s ^ 2 = N * L / 2 := Real.sq_sqrt (by positivity)
  have hLC2 : L * C ^ 2 ≤ ρ ^ 2 * N / 8 := by
    have h1 := mul_le_mul_of_nonneg_right hLN (sq_nonneg C)
    calc L * C ^ 2 ≤ ρ ^ 2 / (8 * C ^ 2) * N * C ^ 2 := h1
      _ = ρ ^ 2 * N / 8 := by field_simp
  have hρs : 0 ≤ ρ * s / 2 := div_nonneg (mul_nonneg hρ.le hs0) zero_le_two
  have hkey : L * C ≤ ρ * s / 2 := by
    have h1 : (L * C) ^ 2 ≤ (ρ * s / 2) ^ 2 := by
      have e : (ρ * s / 2) ^ 2 = ρ ^ 2 * (N * L / 2) / 4 := by rw [← hs2']; ring
      rw [e]
      have : L * (L * C ^ 2) ≤ L * (ρ ^ 2 * N / 8) := mul_le_mul_of_nonneg_left hLC2 hL.le
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hρs two_ne_zero).1 h1
  have hX : ρ * s / 2 ≤ ρ' * s - L - 4 * L * (1 + α) ^ 2 / s2 := by
    have h1 : ρ * s ≤ ρ' * s := mul_le_mul_of_nonneg_right hρρ' hs0
    have h2 : L + 4 * L * (1 + α) ^ 2 / s2 = L * C := by rw [hC]; ring
    linarith
  have hmax : ρ * s / 2 ≤ max (ρ' * s - L - 4 * L * (1 + α) ^ 2 / s2) 0 := hX.trans (le_max_left _ _)
  have hsq : (ρ * s / 2) ^ 2 ≤ (max (ρ' * s - L - 4 * L * (1 + α) ^ 2 / s2) 0) ^ 2 :=
    pow_le_pow_left₀ hρs hmax 2
  rw [Real.exp_le_exp]
  have e : s2 * ρ ^ 2 * N / 32 = s2 / (4 * L) * (ρ * s / 2) ^ 2 := by
    rw [div_pow, mul_pow, hs2']; field_simp; ring
  rw [e]
  have hsL : 0 ≤ s2 / (4 * L) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsq hsL]

/-- **Quantitative form, existential.** For `σ²_min > 0`, `α ≥ 0`, `ϱ > 0` there is `η > 0` (namely
`η = ϱ²/(8(1 + 4(1+α)²/σ²_min)²)`) with `ε_N(ϱ') ≤ exp(−σ²_min ϱ² N/32)` whenever `0 < L ≤ ηN` and `ϱ' ≥ ϱ`. -/
theorem epsN_rate (s2 α ρ : ℝ) (hs2 : 0 < s2) (hα : 0 ≤ α) (hρ : 0 < ρ) :
    ∃ η > 0, ∀ (N : ℕ) (L ρ' : ℝ), 0 < L → L ≤ η * N → ρ ≤ ρ' →
      epsN s2 α L N ρ' ≤ Real.exp (-(s2 * ρ ^ 2 * N / 32)) := by
  have hC0 : 0 < 1 + 4 * (1 + α) ^ 2 / s2 := by positivity
  exact ⟨ρ ^ 2 / (8 * (1 + 4 * (1 + α) ^ 2 / s2) ^ 2), by positivity,
    fun N L ρ' hL hLN hρρ' => epsN_le_exp s2 α ρ hs2 hα hρ N L ρ' hL hLN hρρ'⟩

/-- The second conjunct of `Claims.bet_power_frac` (verbatim): `ε_N(ϱ') → 0` uniformly over `ϱ' ≥ ϱ` and `0 < L ≤ ηN`. -/
theorem epsN_small_route : ∀ (s2 α ρ ε : ℝ), 0 < s2 → 0 ≤ α → 0 < ρ → 0 < ε → ∃ η > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ L ρ' : ℝ, 0 < L → L ≤ η * N → ρ ≤ ρ' → epsN s2 α L N ρ' ≤ ε := by
  intro s2 α ρ ε hs2 hα hρ hε
  obtain ⟨η, hη, hrate⟩ := epsN_rate s2 α ρ hs2 hα hρ
  refine ⟨η, hη, ⌈Real.log (1 / ε) * 32 / (s2 * ρ ^ 2)⌉₊, ?_⟩
  intro N hN L ρ' hL hLN hρρ'
  refine (hrate N L ρ' hL hLN hρρ').trans ?_
  have hN' : Real.log (1 / ε) * 32 / (s2 * ρ ^ 2) ≤ N := (Nat.le_ceil _).trans (Nat.cast_le.2 hN)
  rw [div_le_iff₀ (by positivity), one_div, Real.log_inv] at hN'
  have : -(s2 * ρ ^ 2 * N / 32) ≤ Real.log ε := by nlinarith
  calc Real.exp (-(s2 * ρ ^ 2 * N / 32)) ≤ Real.exp (Real.log ε) := Real.exp_le_exp.2 this
    _ = ε := Real.exp_log hε

/-- Compile-time check that `epsN_small_route` states exactly the second conjunct of `Claims.bet_power_frac`. -/
example (h : Claims.bet_power_frac) : ∀ (s2 α ρ ε : ℝ), 0 < s2 → 0 ≤ α → 0 < ρ → 0 < ε → ∃ η > 0, ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → ∀ L ρ' : ℝ, 0 < L → L ≤ η * N → ρ ≤ ρ' → epsN s2 α L N ρ' ≤ ε := h.2

end StatFormal.Wave30tz
