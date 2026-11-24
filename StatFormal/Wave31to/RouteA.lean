import StatFormal.Wave31to.Statements
import StatFormal.Lib.Distances.Hellinger
import StatFormal.Archive.Wave8a.RouteGeorep

/-!
# Route A (untrusted): `lem:newtrimmean`, the err identities, `prop:newapproxgen` (i), (ii)

* `trim_bounds`: for `P′ ∈ trimSet P α` with density `g ≤ β`, `∫ f dP′ = ∫ g f dP`, `(β − g) f` between `(β − g) inf f` and
  `(β − g) sup f`, `∫(β − g) = β − 1 = αβ`.
* `err_eq`: `err(f) = TV − (E_P f − E_Q f)` for measurable `[0,1]`-valued `f` (`Distances.tvDist_eq_integral_max_sub`, pointwise
  `|1_A − f||p − q| = (p − q)₊ − f(p − q)`).
* `approxgen_i_route`: Cauchy–Schwarz on `⟪g, μ_{P′} − μ_{Q′}⟫` and `le_csInf` over the trimming pairs, `dTrim = Dpop`
  (certified `Wave8a.georep_dist`).
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31to.RouteA

open StatFormal.TrimmedMMD.Unconditional StatFormal.Distances

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-! ### Trimmed means (S8) -/

theorem integrable_of_bdd (μ : Measure 𝒳) [IsFiniteMeasure μ] {f : 𝒳 → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)

theorem bound_of_bdd {f : 𝒳 → ℝ} (h1 : BddAbove (range f)) (h2 : BddBelow (range f)) :
    ∃ C, ∀ x, |f x| ≤ C := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨max a (-b), fun x => ?_⟩
  have hx1 : f x ≤ a := ha ⟨x, rfl⟩
  have hx2 : b ≤ f x := hb ⟨x, rfl⟩
  rw [abs_le]; constructor <;> [linarith [le_max_right a (-b)]; linarith [le_max_left a (-b)]]

theorem newtrimmean_route : Claims.newtrimmean := by
  intro 𝒳 _ P _ α f hα0 hα1 hf hbA hbB P' hP'
  obtain ⟨hP'p, hac, hle⟩ := hP'
  obtain ⟨C, hC⟩ := bound_of_bdd hbA hbB
  have hne : Nonempty 𝒳 := nonempty_of_isProbabilityMeasure P
  set β : ℝ := 1 / (1 - α) with hβ
  have h1α : 0 < 1 - α := by linarith
  have hβ0 : 0 < β := by rw [hβ]; positivity
  set g : 𝒳 → ℝ := fun x => (P'.rnDeriv P x).toReal with hg
  have hgm : Measurable g := (Measure.measurable_rnDeriv P' P).ennreal_toReal
  have hg0 : ∀ x, 0 ≤ g x := fun x => ENNReal.toReal_nonneg
  have hgβ : ∀ᵐ x ∂P, g x ≤ β := by
    filter_upwards [hle] with x hx
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hx
    rwa [ENNReal.toReal_ofReal hβ0.le] at this
  have hgi : Integrable g P := Measure.integrable_toReal_rnDeriv
  have hint1 : ∫ x, g x ∂P = 1 := by
    rw [hg, Measure.integral_toReal_rnDeriv hac]; simp
  have hfP : Integrable f P := integrable_of_bdd P hf hC
  have hgf : ∫ x, f x ∂P' = ∫ x, g x * f x ∂P := (integral_toReal_rnDeriv_mul hac).symm
  have hgfi : Integrable (fun x => g x * f x) P := (integrable_toReal_rnDeriv_mul_iff hac).2
    (integrable_of_bdd P' hf hC)
  set S := ⨆ x, f x
  set I := ⨅ x, f x
  have hfS : ∀ x, f x ≤ S := fun x => le_ciSup hbA x
  have hfI : ∀ x, I ≤ f x := fun x => ciInf_le hbB x
  have hβg : Integrable (fun x => β - g x) P := (integrable_const β).sub hgi
  have hint2 : ∫ x, (β - g x) ∂P = β - 1 := by
    rw [integral_sub (integrable_const β) hgi, hint1, integral_const]; simp
  have hβ1 : β - 1 = α * β := by rw [hβ]; field_simp; ring
  constructor
  · -- lower bound
    have hpt : ∀ᵐ x ∂P, β * f x - (β - g x) * S ≤ g x * f x := by
      filter_upwards [hgβ] with x hx
      have : (β - g x) * f x ≤ (β - g x) * S := mul_le_mul_of_nonneg_left (hfS x) (by linarith)
      nlinarith
    have hmono : ∫ x, (β * f x - (β - g x) * S) ∂P ≤ ∫ x, g x * f x ∂P :=
      integral_mono_ae ((hfP.const_mul β).sub (hβg.mul_const S)) hgfi hpt
    rw [integral_sub (hfP.const_mul β) (hβg.mul_const S), integral_const_mul, integral_mul_const, hint2] at hmono
    rw [hgf]
    calc ((∫ x, f x ∂P) - α * S) / (1 - α) = β * (∫ x, f x ∂P) - (β - 1) * S := by
          rw [hβ1, hβ]; field_simp
      _ ≤ _ := hmono
  · have hpt : ∀ᵐ x ∂P, g x * f x ≤ β * f x - (β - g x) * I := by
      filter_upwards [hgβ] with x hx
      have : (β - g x) * I ≤ (β - g x) * f x := mul_le_mul_of_nonneg_left (hfI x) (by linarith)
      nlinarith
    have hmono : ∫ x, g x * f x ∂P ≤ ∫ x, (β * f x - (β - g x) * I) ∂P :=
      integral_mono_ae hgfi ((hfP.const_mul β).sub (hβg.mul_const I)) hpt
    rw [integral_sub (hfP.const_mul β) (hβg.mul_const I), integral_const_mul, integral_mul_const, hint2] at hmono
    rw [hgf]
    calc _ ≤ β * (∫ x, f x ∂P) - (β - 1) * I := hmono
      _ = ((∫ x, f x ∂P) - α * I) / (1 - α) := by rw [hβ1, hβ]; field_simp

/-! ### The err identities -/

section Err

variable (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

theorem absP : P ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right Q
theorem absQ : Q ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right' P

theorem densP_meas : Measurable (densP P Q) := (Measure.measurable_rnDeriv P (P + Q)).ennreal_toReal
theorem densQ_meas : Measurable (densQ P Q) := (Measure.measurable_rnDeriv Q (P + Q)).ennreal_toReal
theorem densP_int : Integrable (densP P Q) (P + Q) := Measure.integrable_toReal_rnDeriv
theorem densQ_int : Integrable (densQ P Q) (P + Q) := Measure.integrable_toReal_rnDeriv

theorem setA_meas : MeasurableSet (setA P Q) := measurableSet_lt (densQ_meas P Q) (densP_meas P Q)

theorem integral_eq_dens {f : 𝒳 → ℝ} : ∫ x, f x ∂P = ∫ x, densP P Q x * f x ∂(P + Q) :=
  (integral_toReal_rnDeriv_mul (absP P Q)).symm

theorem integral_eq_densQ {f : 𝒳 → ℝ} : ∫ x, f x ∂Q = ∫ x, densQ P Q x * f x ∂(P + Q) :=
  (integral_toReal_rnDeriv_mul (absQ P Q)).symm

theorem tv_eq : tvDist P Q = ∫ x, max (densP P Q x - densQ P Q x) 0 ∂(P + Q) :=
  tvDist_eq_integral_max_sub (P + Q) (absP P Q) (absQ P Q)

/-- Pointwise: for `0 ≤ f ≤ 1`, `|1_A − f||p − q| = (p − q)₊ − f(p − q)`. -/
theorem pt_err (f : 𝒳 → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : 𝒳) :
    |(setA P Q).indicator (fun _ => (1 : ℝ)) x - f x| * |densP P Q x - densQ P Q x| =
      max (densP P Q x - densQ P Q x) 0 - f x * (densP P Q x - densQ P Q x) := by
  obtain ⟨h0, h1⟩ := hf x
  by_cases hA : x ∈ setA P Q
  · have hlt : densQ P Q x < densP P Q x := hA
    rw [indicator_of_mem hA, abs_of_nonneg (by linarith), abs_of_pos (by linarith), max_eq_left (by linarith)]
    ring
  · have hle : densP P Q x ≤ densQ P Q x := not_lt.1 hA
    rw [indicator_of_notMem hA, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
      max_eq_right (by linarith)]
    ring

theorem err_eq {f : 𝒳 → ℝ} (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    errFn P Q f = tvDist P Q - ((∫ x, f x ∂P) - ∫ x, f x ∂Q) := by
  have hb : ∀ x, |f x| ≤ 1 := fun x => by rw [abs_le]; constructor <;> linarith [hf x]
  have hpi := densP_int P Q
  have hqi := densQ_int P Q
  have hpq : Integrable (fun x => densP P Q x - densQ P Q x) (P + Q) := hpi.sub hqi
  have hmax : Integrable (fun x => max (densP P Q x - densQ P Q x) 0) (P + Q) := hpq.pos_part
  have hfpq : Integrable (fun x => f x * (densP P Q x - densQ P Q x)) (P + Q) :=
    hpq.bdd_mul hfm.aestronglyMeasurable (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb x)
  rw [errFn, integral_congr_ae (ae_of_all _ (pt_err P Q f hf)), integral_sub hmax hfpq, ← tv_eq,
    integral_eq_dens P Q, integral_eq_densQ P Q]
  have hfp : Integrable (fun x => densP P Q x * f x) (P + Q) :=
    hpi.mul_bdd hfm.aestronglyMeasurable (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have hfq : Integrable (fun x => densQ P Q x * f x) (P + Q) :=
    hqi.mul_bdd hfm.aestronglyMeasurable (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb x)
  rw [← integral_sub hfp hfq]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only; ring

theorem err_nonneg (f : 𝒳 → ℝ) : 0 ≤ errFn P Q f :=
  integral_nonneg fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _)

theorem err_zero : errFn P Q (fun _ => 0) = tvDist P Q := by
  rw [err_eq P Q measurable_const (fun _ => ⟨le_rfl, zero_le_one⟩)]; simp

theorem integrable_unit {f : 𝒳 → ℝ} (μ : Measure 𝒳) [IsFiniteMeasure μ] (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : Integrable f μ :=
  integrable_of_bdd μ hfm (C := 1) fun x => by rw [abs_le]; constructor <;> linarith [hf x]

theorem newapprox_err_route : Claims.newapprox_err := by
  intro 𝒳 _ P Q _ _ f hfm hf
  have hE := err_eq P Q hfm hf
  have hfi := integrable_unit P hfm hf
  have hfQ := integrable_unit Q hfm hf
  have h1f : ∫ x, (1 - f x) ∂P = 1 - ∫ x, f x ∂P := by
    rw [integral_sub (integrable_const 1) hfi, integral_const]; simp
  have hA := setA_meas P Q
  set iA : 𝒳 → ℝ := (setA P Q).indicator (fun _ => (1 : ℝ))
  have hiAm : Measurable iA := measurable_const.indicator hA
  have hiA : ∀ x, 0 ≤ iA x ∧ iA x ≤ 1 := fun x => by
    by_cases h : x ∈ setA P Q
    · simp [iA, indicator_of_mem h]
    · simp [iA, indicator_of_notMem h]
  have hEA : errFn P Q iA = 0 := by
    rw [errFn]
    refine integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)
    simp only [iA, sub_self, abs_zero, zero_mul, Pi.zero_apply]
  have hE0 := err_nonneg P Q f
  have hEA' := err_eq P Q hiAm hiA
  have hiAi := integrable_unit P hiAm hiA
  have h1A : ∫ x, (1 - iA x) ∂P = 1 - ∫ x, iA x ∂P := by
    rw [integral_sub (integrable_const 1) hiAi, integral_const]; simp
  refine ⟨hE, hE0, ?_, ?_, ?_, hA, hEA, ?_⟩
  · rw [h1f, hE]; ring
  · rw [h1f]; linarith
  · rw [h1f, hE]; ring
  · rw [h1A]; linarith

end Err

/-! ### `prop:newapproxgen` (i), (ii) -/

section Kernel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem wit_meas {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) (g : H) : Measurable (wit φ g) :=
  ((stronglyMeasurable_const (b := g)).inner (𝕜 := ℝ) hφ).measurable

theorem wit_bound {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (g : H) (x : 𝒳) : |wit φ g x| ≤ ‖g‖ * κ := by
  unfold wit
  exact (abs_real_inner_le_norm g (φ x)).trans (mul_le_mul_of_nonneg_left (hκ x) (norm_nonneg g))

theorem integrable_phi {φ : 𝒳 → H} (μ : Measure 𝒳) [IsFiniteMeasure μ] (hφ : StronglyMeasurable φ) {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) : Integrable φ μ :=
  Integrable.of_bound hφ.aestronglyMeasurable κ (ae_of_all _ hκ)

theorem inner_integral {φ : 𝒳 → H} (μ : Measure 𝒳) [IsFiniteMeasure μ] (hφ : StronglyMeasurable φ) {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (g : H) : ⟪g, ∫ x, φ x ∂μ⟫_ℝ = ∫ x, wit φ g x ∂μ :=
  (integral_inner (integrable_phi μ hφ hκ) g).symm

theorem self_mem_trimSet (P : Measure 𝒳) [IsProbabilityMeasure P] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    P ∈ StatFormal.Wave8a.trimSet P α := by
  refine ⟨inferInstance, Measure.AbsolutelyContinuous.rfl, ?_⟩
  filter_upwards [Measure.rnDeriv_self P] with x hx
  rw [hx, ENNReal.one_le_ofReal]
  rw [le_div_iff₀ (by linarith)]; linarith

theorem wit_bdd {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (g : H) :
    BddAbove (range (wit φ g)) ∧ BddBelow (range (wit φ g)) := by
  refine ⟨⟨‖g‖ * κ, ?_⟩, ⟨-(‖g‖ * κ), ?_⟩⟩
  · rintro _ ⟨x, rfl⟩; exact (abs_le.1 (wit_bound hκ g x)).2
  · rintro _ ⟨x, rfl⟩; exact (abs_le.1 (wit_bound hκ g x)).1

theorem approxgen_i_route : Claims.newapproxgen_i := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ g α hφ hκ hg hα0 hα1
  have hdist := StatFormal.Wave8a.georep_dist 𝒳 H P Q φ κ α hφ hκ hα0 hα1
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  have h1α : 0 < 1 - α := by linarith
  obtain ⟨hbA, hbB⟩ := wit_bdd hκ g
  set f := wit φ g
  have hfm : Measurable f := wit_meas hφ g
  set L := (∫ x, f x ∂P) - (∫ x, f x ∂Q) - α * oscFn f
  -- every trimming pair: `L/(1−α) ≤ ‖g‖‖μ_{P′} − μ_{Q′}‖`
  have hpair : ∀ P' ∈ StatFormal.Wave8a.trimSet P α, ∀ Q' ∈ StatFormal.Wave8a.trimSet Q α,
      L / (1 - α) / ‖g‖ ≤ ‖∫ x, φ x ∂P' - ∫ x, φ x ∂Q'‖ := by
    intro P' hP' Q' hQ'
    have := hP'.1
    have := hQ'.1
    obtain ⟨hP1, -⟩ := newtrimmean_route 𝒳 P α f hα0 hα1 hfm hbA hbB P' hP'
    obtain ⟨-, hQ2⟩ := newtrimmean_route 𝒳 Q α f hα0 hα1 hfm hbA hbB Q' hQ'
    have hinner : ⟪g, ∫ x, φ x ∂P' - ∫ x, φ x ∂Q'⟫_ℝ = (∫ x, f x ∂P') - ∫ x, f x ∂Q' := by
      rw [inner_sub_right, inner_integral P' hφ hκ, inner_integral Q' hφ hκ]
    have hcs : ⟪g, ∫ x, φ x ∂P' - ∫ x, φ x ∂Q'⟫_ℝ ≤ ‖g‖ * ‖∫ x, φ x ∂P' - ∫ x, φ x ∂Q'‖ :=
      real_inner_le_norm _ _
    rw [div_le_iff₀ hgpos, mul_comm]
    refine le_trans ?_ (hinner ▸ hcs)
    have : L / (1 - α) = ((∫ x, f x ∂P) - α * ⨆ x, f x) / (1 - α) - ((∫ x, f x ∂Q) - α * ⨅ x, f x) / (1 - α) := by
      simp only [L, oscFn]; field_simp; ring
    rw [this]; linarith
  have hne : {r | ∃ P' ∈ StatFormal.Wave8a.trimSet P α, ∃ Q' ∈ StatFormal.Wave8a.trimSet Q α,
      r = ‖∫ x, φ x ∂P' - ∫ x, φ x ∂Q'‖}.Nonempty :=
    ⟨_, P, self_mem_trimSet P hα0 hα1, Q, self_mem_trimSet Q hα0 hα1, rfl⟩
  have hle : L / (1 - α) / ‖g‖ ≤ StatFormal.Wave8a.dTrim φ P Q α := by
    refine le_csInf hne ?_
    rintro r ⟨P', hP', Q', hQ', rfl⟩
    exact hpair P' hP' Q' hQ'
  rw [hdist] at hle
  rw [div_div, div_le_iff₀ (by positivity)] at hle
  linarith [hle]

/-- `osc f ≤ 1` for `[0,1]`-valued `f` on a nonempty space. -/
theorem osc_le_one [Nonempty 𝒳] {f : 𝒳 → ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : oscFn f ≤ 1 := by
  unfold oscFn
  have h1 : (⨆ x, f x) ≤ 1 := ciSup_le fun x => (hf x).2
  have h2 : 0 ≤ ⨅ x, f x := le_ciInf fun x => (hf x).1
  linarith

theorem approxgen_ii_route : Claims.newapproxgen_ii := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ g hφ hκ hα0 hα1 hgF
  have hne : Nonempty 𝒳 := nonempty_of_isProbabilityMeasure P
  have hfm := wit_meas hφ g
  have hE := err_eq P Q hfm hgF
  refine ⟨by rw [hE]; ring, fun hg ε hε => ?_⟩
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  set αs := tvDist P Q
  have ha0 : 0 ≤ αs - ε := by linarith [hε.2]
  have ha1 : αs - ε < 1 := by linarith [hε.1]
  have hi := approxgen_i_route 𝒳 H P Q φ κ g (αs - ε) hφ hκ hg ha0 ha1
  have hosc := osc_le_one hgF
  have hosc0 : 0 ≤ oscFn (wit φ g) := by
    unfold oscFn
    obtain ⟨hbA, hbB⟩ := wit_bdd hκ g
    obtain ⟨x0⟩ := hne
    linarith [le_ciSup hbA x0, ciInf_le hbB x0]
  rw [div_le_iff₀ hgpos]
  unfold StatFormal.Wave31ti.uPath
  have hdiff : (∫ x, wit φ g x ∂P) - (∫ x, wit φ g x ∂Q) = αs - errFn P Q (wit φ g) := by rw [hE]; ring
  have : (αs - ε) * oscFn (wit φ g) ≤ αs - ε := by
    calc (αs - ε) * oscFn (wit φ g) ≤ (αs - ε) * 1 := mul_le_mul_of_nonneg_left hosc ha0
      _ = αs - ε := mul_one _
  nlinarith [hi, hdiff]

end Kernel

end StatFormal.Wave31to.RouteA
