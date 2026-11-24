import StatFormal.Archive.RobustEquality.Lower.Statements
import StatFormal.Lib.Distances.LeCam

/-!
# Proofs — robust equality (JASA): what validity forces (lower bounds)

Proofs of the frozen claims in `StatFormal.RobustEquality.Lower.Statements`.

* `twopoint`: Le Cam's event bound (`lecam_of_highProb`) on `A = {Θ P₁ ≤ ρ̂}`.
* `ad_lower`: `P₁ ≥ (1−η) P̃` gives `P₁^m ≥ (1−η)^m P̃^m`, hence `P̃^m(A) ≥ 1 − α'`; then the
  Donsker–Varadhan bound with the test function `log(α'/(1−α')) · 1_A`, KL tensorisation and an
  elementary inequality give `P^m(A) ≥ ½`.
* `ad_lower_mean`: Markov's inequality on top of `ad_lower`.
* `kappa_formula`, `admissible_checks`: real arithmetic.
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace StatFormal.RobustEquality.Lower

/-! ### Real-analysis helpers -/

theorem klBern_half_one_sub {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    klBern (1 / 2) (1 - a) =
      -Real.log 2 - (1 / 2) * Real.log (1 - a) - (1 / 2) * Real.log a := by
  unfold klBern
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, show (1 : ℝ) - (1 - a) = a by ring,
    Real.log_div (by norm_num) (sub_pos.mpr ha1).ne', Real.log_div (by norm_num) ha0.ne',
    show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv]
  ring

theorem klBern_half_one_sub_eq (a : ℝ) (h0 : 0 < a) (h1 : a < 1) :
    klBern (1 / 2) (1 - a) = (1 / 2) * Real.log (1 / (4 * a * (1 - a))) := by
  rw [klBern_half_one_sub h0 h1, one_div (4 * a * (1 - a)), Real.log_inv,
    Real.log_mul (by positivity) (sub_pos.mpr h1).ne', Real.log_mul (by norm_num) h0.ne',
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

theorem klBern_half_nonneg {a : ℝ} (h0 : 0 < a) (h1 : a < 1) :
    0 ≤ klBern (1 / 2) (1 - a) := by
  rw [klBern_half_one_sub_eq a h0 h1]
  have h1' := sub_pos.mpr h1
  have hpos : 0 < 4 * a * (1 - a) := by positivity
  have hle : 4 * a * (1 - a) ≤ 1 := by nlinarith [sq_nonneg (2 * a - 1)]
  have h : 1 ≤ 1 / (4 * a * (1 - a)) := by rw [le_div_iff₀ hpos]; linarith
  have := Real.log_nonneg h
  linarith

/-! ### Measure helper: `c • ν ≤ μ ⇒ c^m • ν^m ≤ μ^m` -/

theorem pi_smul_le {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {c : ℝ≥0∞} (h : c • ν ≤ μ) (m : ℕ) :
    c ^ m • Measure.pi (fun _ : Fin m => ν) ≤ Measure.pi (fun _ : Fin m => μ) := by
  induction m with
  | zero =>
    simp only [pow_zero, one_smul]
    exact le_of_eq (by
      rw [Measure.pi_of_empty (fun _ : Fin 0 => ν), Measure.pi_of_empty (fun _ : Fin 0 => μ)])
  | succ m ih =>
    rw [StatFormal.Distances.pi_succ_eq_map μ m, StatFormal.Distances.pi_succ_eq_map ν m,
      ← Measure.map_smul]
    · refine Measure.map_mono ?_ (MeasurableEquiv.measurable _)
      calc c ^ (m + 1) • ν.prod (Measure.pi fun _ : Fin m => ν)
          = (c • ν).prod (c ^ m • Measure.pi fun _ : Fin m => ν) := by
            rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, pow_succ']
        _ ≤ μ.prod (Measure.pi fun _ : Fin m => μ) := Measure.prod_mono h ih
    · exact (MeasurableEquiv.measurable _).aemeasurable

/-! ### The claims -/

theorem twopoint : Claims.twopoint := by
  intro K _ Θ 𝔓 m ρ δ P₀ P₁ hρ hprob hcov h₀ h₁
  have := hprob P₀ h₀
  have := hprob P₁ h₁
  have hset : {y : Fin m → K | Θ P₁ - Θ P₀ ≤ ρ y - Θ P₀} = {y | Θ P₁ ≤ ρ y} := by
    ext y; simp
  rw [hset]
  exact StatFormal.Distances.lecam_of_highProb (measurableSet_le measurable_const hρ)
    (hcov P₁ h₁)

theorem ad_lower : Claims.ad_lower := by
  intro K _ Θ m ρ α η P Pt Q _ _ _ hα0 hα1 hvalid hη0 hη1 hmass hkl
  have hP1prob : IsProbabilityMeasure (ENNReal.ofReal (1 - η) • Pt + ENNReal.ofReal η • Q) := by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by linarith) hη0]
    simp
  have hAm : MeasurableSet {y : Fin m → K |
      Θ (ENNReal.ofReal (1 - η) • Pt + ENNReal.ofReal η • Q) ≤ ρ y} :=
    measurableSet_le measurable_const hvalid.1
  have hset : {y : Fin m → K | Θ (ENNReal.ofReal (1 - η) • Pt + ENNReal.ofReal η • Q) - Θ P ≤
      ρ y - Θ P} = {y | Θ (ENNReal.ofReal (1 - η) • Pt + ENNReal.ofReal η • Q) ≤ ρ y} := by
    ext y; simp
  rw [hset]
  generalize hP1 : ENNReal.ofReal (1 - η) • Pt + ENNReal.ofReal η • Q = P1 at hP1prob hAm
  generalize hA : {y : Fin m → K | Θ P1 ≤ ρ y} = A at hAm
  have hcov : 1 - α ≤ (Measure.pi fun _ : Fin m => P1).real A := by
    rw [← hA]; exact hvalid.2 P1 hP1prob
  have hcompl1 : (Measure.pi fun _ : Fin m => P1).real Aᶜ ≤ α := by
    rw [measureReal_compl hAm, probReal_univ]; linarith
  have hle : ENNReal.ofReal (1 - η) ^ m • (Measure.pi fun _ : Fin m => Pt) ≤
      Measure.pi fun _ : Fin m => P1 :=
    pi_smul_le (by rw [← hP1]; exact Measure.le_add_right le_rfl) m
  have hpow_pos : 0 < (1 - η) ^ m := pow_pos (by linarith) m
  have hνc : (1 - η) ^ m * (Measure.pi fun _ : Fin m => Pt).real Aᶜ ≤ α := by
    have h1 := Measure.le_iff'.1 hle Aᶜ
    rw [Measure.smul_apply, smul_eq_mul] at h1
    have h2 := ENNReal.toReal_mono (measure_ne_top _ _) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)] at h2
    exact h2.trans hcompl1
  -- the effective level `a = α (1−η)^{−m}`
  generalize ha : α * ((1 - η) ^ m)⁻¹ = a at hkl
  have ha0 : 0 < a := by rw [← ha]; exact mul_pos hα0 (inv_pos.mpr hpow_pos)
  have ha1 : a < 1 / 2 := by
    rw [← ha, ← div_eq_mul_inv, div_lt_iff₀ hpow_pos]; linarith
  have hνc' : (Measure.pi fun _ : Fin m => Pt).real Aᶜ ≤ a := by
    rw [← ha, ← div_eq_mul_inv, le_div_iff₀ hpow_pos]; linarith
  have hy : 1 - a ≤ (Measure.pi fun _ : Fin m => Pt).real A := by
    rw [measureReal_compl hAm, probReal_univ] at hνc'; linarith
  have hy1 : (Measure.pi fun _ : Fin m => Pt).real A ≤ 1 :=
    (measureReal_mono (Set.subset_univ A)).trans_eq probReal_univ
  by_contra hx
  push Not at hx
  -- Donsker–Varadhan with `f = c' · 1_A`
  set c' : ℝ := Real.log (a / (1 - a)) with hc'
  have h1a : 0 < 1 - a := by linarith
  have hexpc : Real.exp c' = a / (1 - a) := Real.exp_log (div_pos ha0 h1a)
  have hexp : (fun x => Real.exp (A.indicator (fun _ => c') x)) =
      fun x => A.indicator (fun _ => Real.exp c' - 1) x + 1 := by
    funext x; by_cases hx : x ∈ A <;> simp [hx]
  have hfint : Integrable (A.indicator (fun _ => c')) (Measure.pi fun _ : Fin m => P) :=
    (integrable_const c').indicator hAm
  have hefint : Integrable (fun x => Real.exp (A.indicator (fun _ => c') x))
      (Measure.pi fun _ : Fin m => Pt) := by
    rw [hexp]; exact ((integrable_const _).indicator hAm).add (integrable_const _)
  have hDV := TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv hfint hefint
  rw [StatFormal.Distances.klDiv_pi_eq P Pt m] at hDV
  have hDV' := hDV.trans hkl
  rw [ENNReal.ofReal_le_ofReal_iff (klBern_half_nonneg ha0 (by linarith))] at hDV'
  rw [integral_indicator_const _ hAm, hexp,
    integral_add ((integrable_const _).indicator hAm) (integrable_const _),
    integral_indicator_const _ hAm] at hDV'
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, hexpc] at hDV'
  rw [klBern_half_one_sub ha0 (by linarith)] at hDV'
  -- elementary inequality
  set x := (Measure.pi fun _ : Fin m => P).real A
  set y := (Measure.pi fun _ : Fin m => Pt).real A
  set e := a / (1 - a) with he
  have hea : e * (1 - a) = a := by rw [he]; field_simp
  have he0 : 0 < e := div_pos ha0 h1a
  have he1 : e < 1 := by rw [he, div_lt_one h1a]; linarith
  have hy0 : 0 ≤ 1 - y := by linarith
  have hZpos : 0 < y * (e - 1) + 1 := by
    nlinarith [mul_le_mul_of_nonneg_left he1.le hy0]
  have hZle : y * (e - 1) + 1 ≤ 2 * a := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy) (sub_nonpos.mpr he1.le)]
  have hlogZ := Real.log_le_log hZpos hZle
  rw [Real.log_mul (by norm_num) ha0.ne'] at hlogZ
  have hc'eq : c' = Real.log a - Real.log (1 - a) := by
    rw [hc', Real.log_div ha0.ne' h1a.ne']
  have hc'neg : c' < 0 := by rw [hc']; exact Real.log_neg he0 he1
  have hxc : c' / 2 < x * c' := by nlinarith
  linarith [hxc, hc'eq, hDV', hlogZ]

theorem ad_lower_mean : Claims.ad_lower_mean := by
  intro K _ Θ m ρ α η P Pt Q _ _ _ hα0 hα1 hvalid hη0 hη1 hmass hkl
  have hhalf := ad_lower K Θ m ρ α η P Pt Q hα0 hα1 hvalid hη0 hη1 hmass hkl
  generalize ht : Θ (ENNReal.ofReal (1 - η) • Pt + ENNReal.ofReal η • Q) - Θ P = t at hhalf ⊢
  rcases le_or_gt t 0 with ht0 | ht0
  · rw [ENNReal.ofReal_of_nonpos (by linarith)]; exact bot_le
  · have hmeas : AEMeasurable (fun y => ENNReal.ofReal (ρ y - Θ P))
        (Measure.pi fun _ : Fin m => P) :=
      (hvalid.1.sub_const _).ennreal_ofReal.aemeasurable
    refine le_trans ?_ (mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal t))
    rw [ENNReal.ofReal_mul (by norm_num), mul_comm]
    gcongr
    calc ENNReal.ofReal (1 / 2) ≤ (Measure.pi fun _ : Fin m => P) {y | t ≤ ρ y - Θ P} :=
          ENNReal.ofReal_le_of_le_toReal hhalf
      _ ≤ _ := measure_mono fun y hy => ENNReal.ofReal_le_ofReal hy

theorem kappa_formula : Claims.kappa_formula := by
  intro α h0 h1
  exact klBern_half_one_sub_eq α h0 (by linarith)

theorem admissible_checks : Claims.admissible_checks := by
  intro m α η hm hα0 hα1
  refine ⟨⟨by rw [sub_zero, one_pow]; linarith, by rw [sub_zero, one_pow, inv_one, mul_one]⟩,
    fun hη0 hη => ?_⟩
  have hr0 : 0 ≤ (2 * α) ^ ((1 : ℝ) / m) := Real.rpow_nonneg (by linarith) _
  have hm0 : m ≠ 0 := by omega
  have hlt : 2 * α < (1 - η) ^ m := by
    have := pow_lt_pow_left₀ (show (2 * α) ^ ((1 : ℝ) / m) < 1 - η by linarith) hr0 hm0
    rwa [one_div, Real.rpow_inv_natCast_pow (by linarith) hm0] at this
  refine ⟨hlt, ?_⟩
  have hp : 0 < (1 - η) ^ m := by linarith
  apply klBern_half_nonneg
  · exact mul_pos hα0 (inv_pos.mpr hp)
  · rw [← div_eq_mul_inv, div_lt_one hp]; linarith

end StatFormal.RobustEquality.Lower
