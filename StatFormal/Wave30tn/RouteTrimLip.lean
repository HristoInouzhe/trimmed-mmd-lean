import StatFormal.Wave30tn.Statements
import StatFormal.Lib.TrimmedMean.Empirical
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Route — wave 30tn: `eq:trimlip` (untrusted)

For a law `F` on `[−κ,κ]` and `Φ_F(s) = ∫ ψ_s dF`:
* `integral_posPart_eq`: `∫(s−u)_+ dF(u) = ∫_{−κ}^s F(u) du` for `s ∈ [−κ,κ]` (Tonelli on the indicator of `{u ≤ t}`
  over `F ⊗ λ|_{[−κ,s]}`);
* `exists_Icc_ge`: every `s` is dominated pointwise (`F`-a.e.) by some `s' ∈ [−κ,κ]` (`s' = −κ` below, `s' = κ` above,
  because `β ≥ 1`), so `L(F) = sup_{[−κ,κ]} Φ_F`; `Φ_F ≤ κ`;
* `lowerTrim_le_add`: `L(F) ≤ L(F') + sup_{[−κ,κ]} β|∫_{−κ}^s (F − F')|`, and the symmetric bound;
* `lowerTrim_empirical`: `L(F_n) = min_{Δ_α(n)} Σ w_i v_i` (`splitTrimLo`), through the library duality
  `trimDual_le_trimLo` / `trimLo_eq` (used by `prop:splitfs`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave30tn

open StatFormal.Wave29i (splitTrimLo splitTrimUp)

section Lip

variable {F : Measure ℝ} [IsProbabilityMeasure F] {κ α : ℝ}

lemma kappa_nonneg_of (hF : F (Icc (-κ) κ) = 1) : 0 ≤ κ := by
  by_contra h
  push Not at h
  have : Icc (-κ) κ = ∅ := Icc_eq_empty (by linarith)
  rw [this, measure_empty] at hF
  exact zero_ne_one hF

lemma ae_mem_Icc (hF : F (Icc (-κ) κ) = 1) : ∀ᵐ u ∂F, u ∈ Icc (-κ) κ := by
  rw [ae_iff]
  have : {u | ¬ u ∈ Icc (-κ) κ} = (Icc (-κ) κ)ᶜ := rfl
  rw [this, prob_compl_eq_zero_iff measurableSet_Icc]
  exact hF

lemma one_le_beta (hα0 : 0 ≤ α) (hα1 : α < 1) : 1 ≤ (1 - α)⁻¹ := by
  rw [one_le_inv₀ (by linarith)]; linarith

lemma psi_le_self (hα0 : 0 ≤ α) (hα1 : α < 1) (s u : ℝ) : psi α s u ≤ u := by
  have hb := one_le_beta hα0 hα1
  unfold psi
  rcases le_total s u with h | h
  · rw [max_eq_right (by linarith)]; linarith
  · rw [max_eq_left (by linarith)]; nlinarith

lemma continuous_psi (α s : ℝ) : Continuous (psi α s) := by
  unfold psi; fun_prop

lemma abs_psi_le (α s u : ℝ) (hu : |u| ≤ κ) : |psi α s u| ≤ |s| + |(1 - α)⁻¹| * (|s| + κ) := by
  unfold psi
  have h1 : |max (s - u) 0| ≤ |s| + κ := by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by have := (abs_nonneg u).trans hu; have := abs_nonneg s; linarith)
    have := le_abs_self s; have := neg_abs_le u; linarith
  calc |s - (1 - α)⁻¹ * max (s - u) 0| ≤ |s| + |(1 - α)⁻¹ * max (s - u) 0| := abs_sub _ _
    _ = |s| + |(1 - α)⁻¹| * |max (s - u) 0| := by rw [abs_mul]
    _ ≤ _ := by gcongr

lemma integrable_psi (hF : F (Icc (-κ) κ) = 1) (α s : ℝ) : Integrable (psi α s) F := by
  refine (integrable_const (|s| + |(1 - α)⁻¹| * (|s| + κ))).mono' (continuous_psi α s).aestronglyMeasurable ?_
  filter_upwards [ae_mem_Icc hF] with u hu
  rw [Real.norm_eq_abs]
  exact abs_psi_le α s u (abs_le.2 ⟨hu.1, hu.2⟩)

lemma integrable_posPart (hF : F (Icc (-κ) κ) = 1) (s : ℝ) : Integrable (fun u => max (s - u) 0) F := by
  refine (integrable_const (|s| + κ)).mono' (by fun_prop : Continuous fun u : ℝ => max (s - u) 0).aestronglyMeasurable ?_
  filter_upwards [ae_mem_Icc hF] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  refine max_le ?_ (by have := kappa_nonneg_of hF; positivity)
  have := le_abs_self s; have := hu.1; linarith

lemma integral_psi_eq (hF : F (Icc (-κ) κ) = 1) (α s : ℝ) :
    ∫ u, psi α s u ∂F = s - (1 - α)⁻¹ * ∫ u, max (s - u) 0 ∂F := by
  unfold psi
  rw [integral_sub (integrable_const _) ((integrable_posPart hF s).const_mul _), integral_const,
    integral_const_mul]
  simp

lemma cdf_mono (F : Measure ℝ) [IsProbabilityMeasure F] : Monotone fun u : ℝ => F.real (Iic u) :=
  fun _ _ h => measureReal_mono (Iic_subset_Iic.2 h)

lemma cdf_intervalIntegrable (F : Measure ℝ) [IsProbabilityMeasure F] (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => F.real (Iic u)) volume a b :=
  (cdf_mono F).intervalIntegrable

/-- `∫(s−u)_+ dF(u) = ∫_{−κ}^s F(u) du` for `s ∈ [−κ,κ]`. -/
lemma integral_posPart_eq (hF : F (Icc (-κ) κ) = 1) {s : ℝ} (hs : s ∈ Icc (-κ) κ) :
    ∫ u, max (s - u) 0 ∂F = ∫ u in (-κ)..s, F.real (Iic u) := by
  rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
  set ν : Measure ℝ := volume.restrict (Icc (-κ) s) with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  set f : ℝ → ℝ → ℝ := fun t u => (Iic t).indicator (1 : ℝ → ℝ) u with hf
  have hfm : Measurable (Function.uncurry f) := by
    have e : Function.uncurry f = {p : ℝ × ℝ | p.2 ≤ p.1}.indicator (fun _ => (1 : ℝ)) := by
      funext p; simp [f, Function.uncurry, Set.indicator, Set.mem_Iic]
    rw [e]
    exact measurable_const.indicator (measurableSet_le measurable_snd measurable_fst)
  have hint : Integrable (Function.uncurry f) (ν.prod F) := by
    refine (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [f, Function.uncurry]
    by_cases h : p.2 ∈ Iic p.1 <;> simp [Set.indicator, h]
  have hswap := integral_integral_swap hint
  -- the inner integrals
  have hin1 : ∀ t, ∫ u, f t u ∂F = F.real (Iic t) := fun t => by
    simp only [f]; rw [integral_indicator_one measurableSet_Iic]
  have hin2 : ∀ u ∈ Icc (-κ) κ, ∫ t, f t u ∂ν = max (s - u) 0 := fun u hu => by
    have e : (fun t => f t u) = (Ici u).indicator (1 : ℝ → ℝ) := by
      funext t; simp [f, Set.indicator, Set.mem_Iic, Set.mem_Ici]
    rw [e, integral_indicator_one measurableSet_Ici, hν, measureReal_restrict_apply measurableSet_Ici]
    rcases le_total u s with hus | hus
    · have : Ici u ∩ Icc (-κ) s = Icc u s := by
        ext t; simp only [mem_inter_iff, mem_Ici, mem_Icc]
        constructor
        · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith [hu.1], h3⟩
      rw [this, Real.volume_real_Icc_of_le hus, max_eq_left (by linarith)]
    · have : Ici u ∩ Icc (-κ) s ⊆ {s} := by
        intro t ht; simp only [mem_inter_iff, mem_Ici, mem_Icc] at ht
        exact le_antisymm ht.2.2 (hus.trans ht.1)
      rw [max_eq_right (by linarith)]
      have h0 : volume (Ici u ∩ Icc (-κ) s) = 0 :=
        measure_mono_null this (Real.volume_singleton)
      simp [measureReal_def, h0]
  calc ∫ u, max (s - u) 0 ∂F = ∫ u, ∫ t, f t u ∂ν ∂F := by
        refine integral_congr_ae ?_
        filter_upwards [ae_mem_Icc hF] with u hu
        exact (hin2 u hu).symm
    _ = ∫ t, ∫ u, f t u ∂F ∂ν := hswap.symm
    _ = ∫ t in Icc (-κ) s, F.real (Iic t) := by
        simp only [hin1, hν]

/-- Every `s` is dominated, `F`-a.e. pointwise, by a point of `[−κ,κ]`. -/
lemma exists_Icc_ge (hF : F (Icc (-κ) κ) = 1) (hα0 : 0 ≤ α) (hα1 : α < 1) (s : ℝ) :
    ∃ s' ∈ Icc (-κ) κ, ∫ u, psi α s u ∂F ≤ ∫ u, psi α s' u ∂F := by
  have hκ := kappa_nonneg_of hF
  have hb := one_le_beta hα0 hα1
  rcases lt_or_ge s (-κ) with h1 | h1
  · refine ⟨-κ, ⟨le_rfl, by linarith⟩, integral_mono_ae (integrable_psi hF α s) (integrable_psi hF α _) ?_⟩
    filter_upwards [ae_mem_Icc hF] with u hu
    unfold psi
    rw [max_eq_right (by linarith [hu.1]), max_eq_right (by linarith [hu.1])]
    linarith
  rcases le_or_gt s κ with h2 | h2
  · exact ⟨s, ⟨h1, h2⟩, le_rfl⟩
  · refine ⟨κ, ⟨by linarith, le_rfl⟩, integral_mono_ae (integrable_psi hF α s) (integrable_psi hF α _) ?_⟩
    filter_upwards [ae_mem_Icc hF] with u hu
    unfold psi
    rw [max_eq_left (by linarith [hu.2]), max_eq_left (by linarith [hu.2])]
    nlinarith

lemma integral_psi_le (hF : F (Icc (-κ) κ) = 1) (hα0 : 0 ≤ α) (hα1 : α < 1) (s : ℝ) :
    ∫ u, psi α s u ∂F ≤ κ := by
  have : ∫ u, psi α s u ∂F ≤ ∫ _u, κ ∂F := by
    refine integral_mono_ae (integrable_psi hF α s) (integrable_const _) ?_
    filter_upwards [ae_mem_Icc hF] with u hu
    exact (psi_le_self hα0 hα1 s u).trans hu.2
  simpa using this

lemma bdd_psi (hF : F (Icc (-κ) κ) = 1) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    BddAbove (range fun s => ∫ u, psi α s u ∂F) :=
  ⟨κ, by rintro _ ⟨s, rfl⟩; exact integral_psi_le hF hα0 hα1 s⟩

lemma le_lowerTrim (hF : F (Icc (-κ) κ) = 1) (hα0 : 0 ≤ α) (hα1 : α < 1) (s : ℝ) :
    ∫ u, psi α s u ∂F ≤ lowerTrim F α :=
  le_ciSup (bdd_psi hF hα0 hα1) s

/-- `g(s) = β |∫_{−κ}^s (F − F')|`. -/
def gap (F F' : Measure ℝ) (κ α s : ℝ) : ℝ := (1 - α)⁻¹ * |∫ u in (-κ)..s, (F.real (Iic u) - F'.real (Iic u))|

lemma abs_cdf_sub_le_one (F F' : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure F'] (u : ℝ) :
    |F.real (Iic u) - F'.real (Iic u)| ≤ 1 := by
  rw [abs_le]
  have := measureReal_le_one (μ := F) (s := Iic u); have := measureReal_le_one (μ := F') (s := Iic u)
  have := measureReal_nonneg (μ := F) (s := Iic u); have := measureReal_nonneg (μ := F') (s := Iic u)
  constructor <;> linarith

lemma gap_le (F F' : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure F'] (hα1 : α < 1) {C : ℝ}
    (hC : ∀ u, |F.real (Iic u) - F'.real (Iic u)| ≤ C) {s : ℝ} (hs : s ∈ Icc (-κ) κ) :
    gap F F' κ α s ≤ (1 - α)⁻¹ * (C * (2 * κ)) := by
  have hβ : 0 ≤ (1 - α)⁻¹ := inv_nonneg.2 (by linarith)
  unfold gap
  refine mul_le_mul_of_nonneg_left ?_ hβ
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -κ) (b := s) (C := C)
    (f := fun u => F.real (Iic u) - F'.real (Iic u)) (fun u _ => by rw [Real.norm_eq_abs]; exact hC u)
  rw [Real.norm_eq_abs] at h
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hC0)
  rw [abs_of_nonneg (by linarith [hs.1])]
  linarith [hs.2]

lemma bdd_gap (F F' : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure F'] (hα1 : α < 1) :
    BddAbove ((fun s => gap F F' κ α s) '' Icc (-κ) κ) :=
  ⟨(1 - α)⁻¹ * (1 * (2 * κ)), by
    rintro _ ⟨s, hs, rfl⟩; exact gap_le F F' hα1 (abs_cdf_sub_le_one F F') hs⟩

/-- `|Φ_F(s) − Φ_{F'}(s)| = g(s)` on `[−κ,κ]`. -/
lemma abs_Phi_sub (F F' : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure F'] (hF : F (Icc (-κ) κ) = 1)
    (hF' : F' (Icc (-κ) κ) = 1) (hα1 : α < 1) {s : ℝ} (hs : s ∈ Icc (-κ) κ) :
    |∫ u, psi α s u ∂F - ∫ u, psi α s u ∂F'| = gap F F' κ α s := by
  rw [integral_psi_eq hF, integral_psi_eq hF', integral_posPart_eq hF hs, integral_posPart_eq hF' hs]
  rw [show ∀ A B : ℝ, s - (1 - α)⁻¹ * A - (s - (1 - α)⁻¹ * B) = -((1 - α)⁻¹ * (A - B)) from
    fun A B => by ring]
  rw [← intervalIntegral.integral_sub (cdf_intervalIntegrable F _ _) (cdf_intervalIntegrable F' _ _),
    abs_neg, abs_mul, abs_of_nonneg (inv_nonneg.2 (by linarith : (0 : ℝ) ≤ 1 - α))]
  rfl

lemma lowerTrim_le_add (F F' : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure F']
    (hF : F (Icc (-κ) κ) = 1) (hF' : F' (Icc (-κ) κ) = 1) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    lowerTrim F α ≤ lowerTrim F' α + sSup ((fun s => gap F F' κ α s) '' Icc (-κ) κ) := by
  refine ciSup_le fun s => ?_
  obtain ⟨s', hs', hle⟩ := exists_Icc_ge hF hα0 hα1 s
  have h1 := le_lowerTrim hF' hα0 hα1 s'
  have h2 := abs_Phi_sub F F' hF hF' hα1 hs'
  have h3 : gap F F' κ α s' ≤ sSup ((fun s => gap F F' κ α s) '' Icc (-κ) κ) :=
    le_csSup (bdd_gap F F' hα1) (mem_image_of_mem _ hs')
  have h4 := le_abs_self (∫ u, psi α s' u ∂F - ∫ u, psi α s' u ∂F')
  linarith

lemma gap_comm (F F' : Measure ℝ) (κ α s : ℝ) : gap F' F κ α s = gap F F' κ α s := by
  unfold gap
  congr 1
  rw [← abs_neg, ← intervalIntegral.integral_neg]
  congr 1
  exact intervalIntegral.integral_congr fun u _ => by ring

theorem trimlip_route : Claims.trimlip := by
  intro F F' _ _ κ α hF hF' hα0 hα1
  have hκ := kappa_nonneg_of hF
  refine ⟨fun s hs => integral_posPart_eq hF hs, ?_, ?_⟩
  · have hA := lowerTrim_le_add F F' hF hF' hα0 hα1
    have hB : lowerTrim F' α ≤ lowerTrim F α + sSup ((fun s => gap F F' κ α s) '' Icc (-κ) κ) := by
      have := lowerTrim_le_add F' F hF' hF hα0 hα1
      rwa [show (fun s => gap F' F κ α s) = (fun s => gap F F' κ α s) from
        funext fun s => gap_comm F F' κ α s] at this
    change |lowerTrim F α - lowerTrim F' α| ≤ sSup ((fun s => gap F F' κ α s) '' Icc (-κ) κ)
    rw [abs_le]
    constructor <;> linarith
  · have hD : ∀ u, |F.real (Iic u) - F'.real (Iic u)| ≤ ⨆ v : ℝ, |F.real (Iic v) - F'.real (Iic v)| :=
      fun u => le_ciSup (f := fun v : ℝ => |F.real (Iic v) - F'.real (Iic v)|)
        ⟨1, by rintro _ ⟨v, rfl⟩; exact abs_cdf_sub_le_one F F' v⟩ u
    refine csSup_le ((nonempty_Icc.2 (by linarith)).image _) ?_
    rintro _ ⟨s, hs, rfl⟩
    have := gap_le (κ := κ) F F' hα1 hD hs
    simp only [gap] at this
    calc _ ≤ _ := this
      _ = _ := by ring

end Lip

section Emp

/-- `∫ g d(empirical v) = n⁻¹ Σ g(v_i)` for continuous `g`. -/
lemma integral_empirical_real {n : ℕ} (v : Fin n → ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ u, g u ∂(StatFormal.TrimmedMMD.Concentration.empirical v) = (∑ i, g (v i)) / n := by
  unfold StatFormal.TrimmedMMD.Concentration.empirical
  rw [integral_finsetSum_measure fun i _ =>
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)]
  simp_rw [integral_smul_measure, integral_dirac' _ _ hg.stronglyMeasurable]
  rw [ENNReal.toReal_ofReal (by positivity), Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]; ring

lemma isProbabilityMeasure_empirical' {𝒳 : Type*} [MeasurableSpace 𝒳] {n : ℕ} (x : Fin n → 𝒳) (hn : 1 ≤ n) :
    IsProbabilityMeasure (StatFormal.TrimmedMMD.Concentration.empirical x) := by
  have hn' : n ≠ 0 := by omega
  constructor
  have h1 : ENNReal.ofReal (1 / n) = (n : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn')), ENNReal.ofReal_one,
      ENNReal.ofReal_natCast, one_div]
  simp only [StatFormal.TrimmedMMD.Concentration.empirical, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, h1]
  exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hn') (ENNReal.natCast_ne_top n)

open StatFormal.Foundations.TrimmedMean in
/-- `L(F_n) = min_{w ∈ Δ_α(n)} Σ w_i v_i`. -/
lemma lowerTrim_empirical {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (v : Fin n → ℝ) :
    lowerTrim (StatFormal.TrimmedMMD.Concentration.empirical v) α = splitTrimLo n α v := by
  have e : ∀ s, ∫ u, psi α s u ∂(StatFormal.TrimmedMMD.Concentration.empirical v) = trimDual n α v s := by
    intro s
    rw [integral_empirical_real v (continuous_psi α s)]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hβ : (1 - α) ≠ 0 := by linarith
    simp only [psi, trimDual, StatFormal.TrimmedMMD.BangBang.cap]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
    field_simp
  unfold lowerTrim splitTrimLo
  simp only [e]
  refine le_antisymm (ciSup_le fun s => trimDual_le_trimLo hn hα0 hα1 v s) ?_
  rw [trimLo_eq hn hα0 hα1]
  exact le_ciSup (f := fun s => trimDual n α v s)
    ⟨_, by rintro _ ⟨s, rfl⟩; exact trimDual_le_trimLo hn hα0 hα1 v s⟩ _

end Emp

end StatFormal.Wave30tn
