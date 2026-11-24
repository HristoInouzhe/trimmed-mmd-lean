import StatFormal.Wave31tu.Statements
import StatFormal.Wave31tq.Proofs
import StatFormal.Wave31tq.RouteM21
import StatFormal.Archive.TrimmedMMD.Concentration.Proofs
import StatFormal.Lib.TIKernel.Profile
import StatFormal.Lib.BandLimited.Density
import StatFormal.Lib.TVMeasure.Basic
import StatFormal.Lib.MomentTrim.Crossing
import StatFormal.Lib.LaplaceDev.OneSample
import StatFormal.Lib.LaplaceDev.Collect

set_option linter.style.longLine false

/-!
# Wave31tu, chunk D: auxiliary facts for Y13 `lap_dev` (Lemma S4.25, S4 :1227-1275)

* `phi_continuous`: a Laplace feature map (`⟪φ x, φ y⟫ = e^{−|x−y|}`) is continuous;
* `intervalDev_of`, `localDev_of`: the frozen event `IntervalEvent P x c` and the frozen claim `Claims.lap_bv` (Y5) in the general
  form `LaplaceDev.IntervalDev`, `LaplaceDev.LocalDev` with `ε = c/n`, `ζ = c_x/n`;
* `wit_facts`: from `Claims.laplace_h1` (Y3) at `σ = 1`, `f = wit φ g` is continuous, `|f| ≤ 1` when `osc f ≤ 1`, and its variation
  on `[a, b]` is at most `(2(b − a))^{1/2}N` for every `N ≥ ‖g‖`;
* `dens_bounds`: under (5.1) (`CondR`), the signs of `IsCross` and `p + q ≤ p̄` on `[x₀−r⋆, x₀+r⋆]`, for a law `ν = ρ·Leb` with
  `0 ≤ ρ ≤ p + q` and `w ∈ (0, r⋆]`: `ν((x₀, x₀+w]), ν((x₀−w, x₀]) ≤ p̄w`, and, when `∫(M − f)(p − q)₊ ≤ T` and
  `∫(f − m)(q − p)₊ ≤ T`, `∫_{(x₀+w, x₀+K]}(M − f) dν ≤ T/(c⋆w)` and `∫_{[x₀−K, x₀−w]}(f − m) dν ≤ T/(c⋆w)` (S4 :1262-1265);
* `errL_pos`: under `IsCross`, `p(x₀) > 0` and `Claims.lap_err` (Y6), every continuous `f` with `|f| ≤ 1`, `osc f ≤ 1` has
  `err(f) > 0` (S4 :1252-1255).
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteD

open StatFormal StatFormal.TrimmedMMD.Concentration StatFormal.LaplaceDev StatFormal.Wave31tq

/-- A Laplace feature map at bandwidth `1` is continuous. -/
theorem phi_continuous {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {φ : ℝ → H}
    (hφ : IsLaplaceFeature 1 φ) : Continuous φ := by
  have hg : ∀ x y, ⟪φ x, φ y⟫_ℝ = (fun z : ℝ => Real.exp (-|z| / 1)) (x - y) := fun x y => hφ x y
  have hc : Continuous fun z : ℝ => Real.exp (-|z| / 1) := by fun_prop
  exact ((StatFormal.TIKernel.gram_cont_iff hg).1).2 hc.continuousAt

/-- The event of Lemma S4.23 in the general form, `ε = c/n`, `ζ = c_x/n`. -/
theorem intervalDev_of {P : Measure ℝ} {n : ℕ} {x : Fin n → ℝ} {c : ℝ} (h : IntervalEvent P x c) :
    IntervalDev (empirical x) P (c / n) (cx c / n) := by
  intro I hI
  rw [← mul_div_assoc]
  exact h I hI

/-- `Claims.lap_bv` (Y5) in the general form, `ε = c/n`, `ζ = c_x/n`. -/
theorem localDev_of (h5 : Claims.lap_bv) {P : Measure ℝ} [IsProbabilityMeasure P] {n : ℕ} {x : Fin n → ℝ} {c : ℝ}
    (hn : 1 ≤ n) (hc : 0 ≤ c) (h : IntervalEvent P x c) : LocalDev (empirical x) P (c / n) (cx c / n) := by
  intro I hh V hIo hIb hh01 hhc hV hvar
  have := h5 P n x c hn hc h I hh V hIo hIb hh01 hhc hV hvar
  rw [← mul_div_assoc, ← mul_div_assoc]
  exact this

/-- From Y3 at `σ = 1`: continuity, `|f| ≤ 1`, and the variation bound `(2(b − a))^{1/2}N` for `N ≥ ‖g‖`. -/
theorem wit_facts (h3 : Claims.laplace_h1) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {φ : ℝ → H} (hφ : IsLaplaceFeature 1 φ) (g : H) (hosc : Wave31to.oscFn (Wave31to.wit φ g) ≤ 1) {N : ℝ}
    (hN : ‖g‖ ≤ N) :
    Continuous (Wave31to.wit φ g) ∧ (∀ z, |Wave31to.wit φ g z| ≤ 1) ∧
      ∀ a b, a ≤ b → eVariationOn (Wave31to.wit φ g) (Icc a b) ≤ ENNReal.ofReal (√(2 * (b - a)) * N) := by
  obtain ⟨-, hc⟩ := h3 H 1 φ one_pos hφ
  obtain ⟨-, -, hv, -, h1⟩ := hc g
  refine ⟨continuous_const.inner (phi_continuous hφ), h1 hosc, fun a b hab => (hv a b hab).trans ?_⟩
  rw [div_one]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hN (Real.sqrt_nonneg _))

/-- The mass and integral bounds of the proof of Lemma S4.25 (b) for a law `ν = ρ·Leb` with `0 ≤ ρ ≤ p + q` (S4 :1262-1265). -/
theorem dens_bounds {p q ρ : ℝ → ℝ} (hpi : Integrable p) (hqi : Integrable q) (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (hρle : ∀ x, ρ x ≤ p x + q x)
    {x₀ rs cs pbar w K : ℝ} (hcond : CondR p q x₀ rs cs) (hpbar : ∀ z ∈ Icc (x₀ - rs) (x₀ + rs), p z + q z ≤ pbar)
    (hw : 0 < w) (hwr : w ≤ rs)
    (hR : ∀ᵐ x ∂volume, x₀ < x → q x ≤ p x) (hL : ∀ᵐ x ∂volume, x < x₀ → p x ≤ q x)
    {f : ℝ → ℝ} (hfc : Continuous f) {M m : ℝ} (hfM : ∀ z, 0 ≤ M - f z ∧ M - f z ≤ 1) (hfm : ∀ z, 0 ≤ f z - m ∧ f z - m ≤ 1)
    {T : ℝ} (hA : ∫ x, (M - f x) * max (p x - q x) 0 ≤ T) (hB : ∫ x, (f x - m) * max (q x - p x) 0 ≤ T) :
    (volume.withDensity fun x => ENNReal.ofReal (ρ x)).real (Ioc x₀ (x₀ + w)) ≤ pbar * w ∧
    (volume.withDensity fun x => ENNReal.ofReal (ρ x)).real (Ioc (x₀ - w) x₀) ≤ pbar * w ∧
    ∫ z in Ioc (x₀ + w) (x₀ + K), (M - f z) ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x)) ≤ T / (cs * w) ∧
    ∫ z in Icc (x₀ - K) (x₀ - w), (f z - m) ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x)) ≤ T / (cs * w) := by
  obtain ⟨hrs, -, hcs, hae⟩ := hcond
  have hρi : Integrable ρ := (hpi.add hqi).mono' hρm.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 x)]; exact hρle x)
  have hcw : 0 < cs * w := mul_pos hcs hw
  -- the short intervals
  have hshort : ∀ {a b : ℝ}, a ≤ b → b - a = w → Ioc a b ⊆ Icc (x₀ - rs) (x₀ + rs) →
      (volume.withDensity fun x => ENNReal.ofReal (ρ x)).real (Ioc a b) ≤ pbar * w := by
    intro a b hab hba hsub
    rw [measureReal_def, StatFormal.BandLimited.withDensity_real_eq_setIntegral hρi hρ0 measurableSet_Ioc]
    calc ∫ x in Ioc a b, ρ x ≤ ∫ _ in Ioc a b, pbar :=
          setIntegral_mono_on hρi.integrableOn (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc
            fun z hz => (hρle z).trans (hpbar z (hsub hz))
      _ = pbar * w := by rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, hba, smul_eq_mul, mul_comm]
  refine ⟨hshort (by linarith) (by ring) (fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩),
    hshort (by linarith) (by ring) (fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩), ?_, ?_⟩
  · -- `(x₀ + w, x₀ + K]`: `p + q ≤ (p − q)₊/(c⋆w)` a.e.
    have hgi : Integrable fun x => (M - f x) * max (p x - q x) 0 :=
      (hpi.sub hqi).pos_part.bdd_mul (continuous_const.sub hfc).aestronglyMeasurable
        (ae_of_all _ fun z => by show ‖M - f z‖ ≤ 1; rw [Real.norm_eq_abs, abs_of_nonneg (hfM z).1]; exact (hfM z).2)
    rw [restrict_withDensity measurableSet_Ioc, StatFormal.TVMeasure.integral_withDensity_ofReal hρm hρ0]
    calc ∫ z in Ioc (x₀ + w) (x₀ + K), (M - f z) * ρ z ≤
          ∫ z in Ioc (x₀ + w) (x₀ + K), (cs * w)⁻¹ * ((M - f z) * max (p z - q z) 0) := by
          refine setIntegral_mono_on_ae ?_ ?_ measurableSet_Ioc ?_
          · exact (hρi.bdd_mul (continuous_const.sub hfc).aestronglyMeasurable (ae_of_all _ fun z => by
              show ‖M - f z‖ ≤ 1; rw [Real.norm_eq_abs, abs_of_nonneg (hfM z).1]; exact (hfM z).2)).integrableOn
          · exact (hgi.const_mul _).integrableOn
          · filter_upwards [hae, hR] with z hz hzR hzI
            have hz0 : x₀ < z := by linarith [hzI.1]
            have hmin : w ≤ min rs |z - x₀| := le_min hwr (by rw [abs_of_pos (by linarith)]; linarith [hzI.1])
            have hpq : q z ≤ p z := hzR hz0
            have h1 : cs * w * (p z + q z) ≤ max (p z - q z) 0 := by
              rw [max_eq_left (by linarith)]
              calc cs * w * (p z + q z) ≤ cs * min rs |z - x₀| * (p z + q z) :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin hcs.le) (by linarith [hp0 z, hq0 z])
                _ ≤ |p z - q z| := hz
                _ = p z - q z := abs_of_nonneg (by linarith)
            have h2 : ρ z ≤ (cs * w)⁻¹ * max (p z - q z) 0 := by
              rw [inv_mul_eq_div, le_div_iff₀ hcw]; nlinarith [hρle z]
            calc (M - f z) * ρ z ≤ (M - f z) * ((cs * w)⁻¹ * max (p z - q z) 0) :=
                  mul_le_mul_of_nonneg_left h2 (hfM z).1
              _ = _ := by ring
      _ = (cs * w)⁻¹ * ∫ z in Ioc (x₀ + w) (x₀ + K), (M - f z) * max (p z - q z) 0 := integral_const_mul _ _
      _ ≤ (cs * w)⁻¹ * ∫ z, (M - f z) * max (p z - q z) 0 :=
          mul_le_mul_of_nonneg_left (setIntegral_le_integral hgi (ae_of_all _ fun z =>
            mul_nonneg (hfM z).1 (le_max_right _ _))) (inv_nonneg.2 hcw.le)
      _ ≤ (cs * w)⁻¹ * T := mul_le_mul_of_nonneg_left hA (inv_nonneg.2 hcw.le)
      _ = T / (cs * w) := by rw [inv_mul_eq_div]
  · -- `[x₀ − K, x₀ − w]`: `p + q ≤ (q − p)₊/(c⋆w)` a.e.
    have hgi : Integrable fun x => (f x - m) * max (q x - p x) 0 :=
      (hqi.sub hpi).pos_part.bdd_mul (hfc.sub continuous_const).aestronglyMeasurable
        (ae_of_all _ fun z => by show ‖f z - m‖ ≤ 1; rw [Real.norm_eq_abs, abs_of_nonneg (hfm z).1]; exact (hfm z).2)
    rw [restrict_withDensity measurableSet_Icc, StatFormal.TVMeasure.integral_withDensity_ofReal hρm hρ0]
    calc ∫ z in Icc (x₀ - K) (x₀ - w), (f z - m) * ρ z ≤
          ∫ z in Icc (x₀ - K) (x₀ - w), (cs * w)⁻¹ * ((f z - m) * max (q z - p z) 0) := by
          refine setIntegral_mono_on_ae ?_ ?_ measurableSet_Icc ?_
          · exact (hρi.bdd_mul (hfc.sub continuous_const).aestronglyMeasurable (ae_of_all _ fun z => by
              show ‖f z - m‖ ≤ 1; rw [Real.norm_eq_abs, abs_of_nonneg (hfm z).1]; exact (hfm z).2)).integrableOn
          · exact (hgi.const_mul _).integrableOn
          · filter_upwards [hae, hL] with z hz hzL hzI
            have hz0 : z < x₀ := by linarith [hzI.2]
            have hmin : w ≤ min rs |z - x₀| :=
              le_min hwr (by rw [abs_of_neg (by linarith)]; linarith [hzI.2])
            have hpq : p z ≤ q z := hzL hz0
            have h1 : cs * w * (p z + q z) ≤ max (q z - p z) 0 := by
              rw [max_eq_left (by linarith)]
              calc cs * w * (p z + q z) ≤ cs * min rs |z - x₀| * (p z + q z) :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin hcs.le) (by linarith [hp0 z, hq0 z])
                _ ≤ |p z - q z| := hz
                _ = q z - p z := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
            have h2 : ρ z ≤ (cs * w)⁻¹ * max (q z - p z) 0 := by
              rw [inv_mul_eq_div, le_div_iff₀ hcw]; nlinarith [hρle z]
            calc (f z - m) * ρ z ≤ (f z - m) * ((cs * w)⁻¹ * max (q z - p z) 0) :=
                  mul_le_mul_of_nonneg_left h2 (hfm z).1
              _ = _ := by ring
      _ = (cs * w)⁻¹ * ∫ z in Icc (x₀ - K) (x₀ - w), (f z - m) * max (q z - p z) 0 := integral_const_mul _ _
      _ ≤ (cs * w)⁻¹ * ∫ z, (f z - m) * max (q z - p z) 0 :=
          mul_le_mul_of_nonneg_left (setIntegral_le_integral hgi (ae_of_all _ fun z =>
            mul_nonneg (hfm z).1 (le_max_right _ _))) (inv_nonneg.2 hcw.le)
      _ ≤ (cs * w)⁻¹ * T := mul_le_mul_of_nonneg_left hB (inv_nonneg.2 hcw.le)
      _ = T / (cs * w) := by rw [inv_mul_eq_div]

end StatFormal.Wave31tu.RouteD
