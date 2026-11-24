import StatFormal.Archive.Wave29d.RouteLocLower

/-!
# Route — robust equality JASA `thm:loc-lower` (ii) (untrusted)

`K = [−R, R]`, `μ = P₀ = ½δ_{−R} + ½δ_R`, `P_t = (½ − t)δ_{−R} + (½ + t)δ_R`.
* `OT_ε(μ, P_t) ≥ J_{P_t}(4R², 0) ≥ 4R² t` (weak duality; `log(½e^a + ½e^{−a}) ≤ a`);
* `OT_ε(μ, P₀) = max_f J_{P₀}(f) ≤ ε log 2` (drop one exponential in each soft-min);
* `TV(P₀^m, P_t^m) ≤ √(m KL(P₀‖P_t)/2)` (Pinsker, tensorisation), `KL(P₀‖P_t) ≤ KL(B₀‖B_t) = −½ log(1 − 4t²) ≤ 4t²` for the
  laws `B` on `Fin 2` mapped to `{−R, R}`;
* the variance: the first-order condition at label `0` forces `e^{f*_0/ε} = e^{f*_1/ε}`;
* the envelope by evaluation on the four pairs.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology InformationTheory
open scoped ENNReal

namespace StatFormal.Wave29d

open StatFormal.RobustEquality.Semidual (gsoft muDisc)
open StatFormal.RobustEquality.SemidualStrong (OTdisc Jdual Setting)
open StatFormal.RobustEquality.AllPairs (Dbar)

namespace TwoPt

/-- Integral against a two-atom measure. -/
lemma integral_two {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (p q : ℝ≥0∞) (hp : p ≠ ⊤)
    (hq : q ≠ ⊤) (u v : X) (f : X → ℝ) :
    ∫ y, f y ∂(p • Measure.dirac u + q • Measure.dirac v) = p.toReal * f u + q.toReal * f v := by
  have hu : Integrable f (Measure.dirac u) := (integrable_const (f u)).congr (ae_eq_dirac f).symm
  have hv : Integrable f (Measure.dirac v) := (integrable_const (f v)).congr (ae_eq_dirac f).symm
  rw [integral_add_measure (hu.smul_measure hp) (hv.smul_measure hq), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac, smul_eq_mul, smul_eq_mul]

variable {R : ℝ}

lemma cTwo_low0 (hR : 0 ≤ R) : cTwo R 0 (lowPt R hR) = 0 := by simp [cTwo, lowPt]
lemma cTwo_low1 (hR : 0 ≤ R) : cTwo R 1 (lowPt R hR) = 4 * R ^ 2 := by simp [cTwo, lowPt]; ring
lemma cTwo_high0 (hR : 0 ≤ R) : cTwo R 0 (highPt R hR) = 4 * R ^ 2 := by simp [cTwo, highPt]; ring
lemma cTwo_high1 (hR : 0 ≤ R) : cTwo R 1 (highPt R hR) = 0 := by simp [cTwo, highPt]

lemma setting_two {ε : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) : Setting ε (fun _ : Fin 2 => (1 : ℝ) / 2) (cTwo R) := by
  refine ⟨hε, fun _ => by norm_num, by norm_num [Fin.sum_univ_two], fun i => ?_, ⟨4 * R ^ 2, fun i y => ?_⟩⟩
  · exact ((continuous_const.sub continuous_subtype_val).pow 2).measurable
  · have hy := y.2
    rw [abs_of_nonneg (by unfold cTwo; positivity)]
    unfold cTwo
    fin_cases i <;> simp <;> nlinarith [hy.1, hy.2]

/-- `g_f(−R)` and `g_f(R)` in closed form. -/
lemma gsoft_low (ε : ℝ) (hR : 0 ≤ R) (f : Fin 2 → ℝ) :
    gsoft ε (fun _ => (1 : ℝ) / 2) f (cTwo R) (lowPt R hR) =
      -ε * Real.log (1 / 2 * Real.exp (f 0 / ε) + 1 / 2 * Real.exp ((f 1 - 4 * R ^ 2) / ε)) := by
  simp only [gsoft, Fin.sum_univ_two, cTwo_low0, cTwo_low1, sub_zero]

lemma gsoft_high (ε : ℝ) (hR : 0 ≤ R) (f : Fin 2 → ℝ) :
    gsoft ε (fun _ => (1 : ℝ) / 2) f (cTwo R) (highPt R hR) =
      -ε * Real.log (1 / 2 * Real.exp ((f 0 - 4 * R ^ 2) / ε) + 1 / 2 * Real.exp (f 1 / ε)) := by
  simp only [gsoft, Fin.sum_univ_two, cTwo_high0, cTwo_high1, sub_zero]

/-- `P_t = (½ − t)δ_{−R} + (½ + t)δ_R`. -/
def Pt (R : ℝ) (hR : 0 ≤ R) (t : ℝ) : Measure (Icc (-R) R) :=
  ENNReal.ofReal (1 / 2 - t) • Measure.dirac (lowPt R hR) + ENNReal.ofReal (1 / 2 + t) • Measure.dirac (highPt R hR)

lemma Pt_prob (hR : 0 ≤ R) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) : IsProbabilityMeasure (Pt R hR t) := by
  constructor
  simp only [Pt, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
  norm_num

lemma ofReal_half : ENNReal.ofReal (1 / 2) = (1 / 2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos two_pos]; simp

lemma twoPt_eq (hR : 0 ≤ R) : twoPt R hR = Pt R hR 0 := by
  simp only [twoPt, Pt, sub_zero, add_zero, ofReal_half]

instance twoPt_prob (hR : 0 ≤ R) : IsProbabilityMeasure (twoPt R hR) := by
  rw [twoPt_eq]; exact Pt_prob hR le_rfl (by norm_num)

lemma integral_Pt (hR : 0 ≤ R) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (f : Icc (-R) R → ℝ) :
    ∫ y, f y ∂(Pt R hR t) = (1 / 2 - t) * f (lowPt R hR) + (1 / 2 + t) * f (highPt R hR) := by
  rw [Pt, integral_two _ _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (by linarith)]

lemma integral_twoPt (hR : 0 ≤ R) (f : Icc (-R) R → ℝ) :
    ∫ y, f y ∂(twoPt R hR) = 1 / 2 * f (lowPt R hR) + 1 / 2 * f (highPt R hR) := by
  rw [twoPt_eq, integral_Pt hR le_rfl (by norm_num)]; ring

/-- `OT_ε(μ, P_t) ≥ 4R² t`. -/
lemma OT_Pt_ge {ε : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    ((4 * R ^ 2 * t : ℝ) : EReal) ≤ OTdisc ε (fun _ => 1 / 2) (cTwo R) (Pt R hR t) := by
  haveI := Pt_prob hR ht0 ht
  refine le_trans ?_ (LocLower.J_le_OT (setting_two hε hR) (Pt R hR t) ![4 * R ^ 2, 0])
  rw [EReal.coe_le_coe_iff]
  unfold Jdual
  rw [integral_Pt hR ht0 ht, gsoft_low, gsoft_high]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, sub_self,
    zero_div, Real.exp_zero, zero_sub]
  set A := 4 * R ^ 2 / ε
  have hA : 0 ≤ A := by positivity
  have hlog : Real.log (1 / 2 * Real.exp A + 1 / 2 * Real.exp (-(4 * R ^ 2) / ε)) ≤ A := by
    have h1 : Real.exp (-(4 * R ^ 2) / ε) ≤ Real.exp A := Real.exp_le_exp.2 (by
      rw [neg_div]; linarith)
    have hpos : 0 < 1 / 2 * Real.exp A + 1 / 2 * Real.exp (-(4 * R ^ 2) / ε) := by positivity
    rw [Real.log_le_iff_le_exp hpos]; linarith
  have h1 : Real.log (1 / 2 * 1 + 1 / 2 * 1) = 0 := by norm_num
  rw [h1]
  have hεA : ε * A = 4 * R ^ 2 := by simp only [A]; field_simp
  have : -ε * Real.log (1 / 2 * Real.exp A + 1 / 2 * Real.exp (-(4 * R ^ 2) / ε)) ≥ -(4 * R ^ 2) := by
    nlinarith
  nlinarith

/-- `J_{P₀}(f) ≤ ε log 2` for every `f`, hence `OT_ε(μ, P₀) ≤ ε log 2`. -/
lemma J_twoPt_le {ε : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) (f : Fin 2 → ℝ) :
    Jdual ε (fun _ => 1 / 2) (cTwo R) (twoPt R hR) f ≤ ε * Real.log 2 := by
  unfold Jdual
  rw [integral_twoPt, gsoft_low, gsoft_high]
  simp only [Fin.sum_univ_two]
  have key : ∀ x y : ℝ, -ε * Real.log (1 / 2 * Real.exp (x / ε) + 1 / 2 * Real.exp y) ≤ ε * Real.log 2 - x := by
    intro x y
    have hA : 0 < 1 / 2 * Real.exp (x / ε) := by positivity
    have hmono : Real.log (1 / 2 * Real.exp (x / ε)) ≤ Real.log (1 / 2 * Real.exp (x / ε) + 1 / 2 * Real.exp y) :=
      Real.log_le_log hA (by have := Real.exp_pos y; linarith)
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, one_div, Real.log_inv] at hmono
    have : ε * (x / ε) = x := by field_simp
    nlinarith
  have k1 := key (f 0) ((f 1 - 4 * R ^ 2) / ε)
  have k2 : -ε * Real.log (1 / 2 * Real.exp ((f 0 - 4 * R ^ 2) / ε) + 1 / 2 * Real.exp (f 1 / ε)) ≤
      ε * Real.log 2 - f 1 := by
    rw [add_comm]; exact key (f 1) ((f 0 - 4 * R ^ 2) / ε)
  nlinarith

lemma OT_twoPt_le {ε : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    ∃ J₀ : ℝ, OTdisc ε (fun _ => 1 / 2) (cTwo R) (twoPt R hR) = J₀ ∧ J₀ ≤ ε * Real.log 2 := by
  obtain ⟨fs, -, hval, -⟩ := StatFormal.RobustEquality.SemidualStrong.strong_duality _ 2 ε _ _ (twoPt R hR)
    (setting_two hε hR)
  exact ⟨_, hval, J_twoPt_le hε hR fs⟩

/-! ### The Bernoulli laws on `Fin 2` -/

/-- `B_t = (½ − t)δ_0 + (½ + t)δ_1` on `Fin 2`. -/
def Bt (t : ℝ) : Measure (Fin 2) :=
  ENNReal.ofReal (1 / 2 - t) • Measure.dirac 0 + ENNReal.ofReal (1 / 2 + t) • Measure.dirac 1

lemma Bt_prob {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) : IsProbabilityMeasure (Bt t) := by
  constructor
  simp only [Bt, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
  norm_num

lemma Bt_zero_single (t : ℝ) : Bt t {0} = ENNReal.ofReal (1 / 2 - t) := by
  simp [Bt, Measure.add_apply, Measure.smul_apply]

lemma Bt_one_single (t : ℝ) : Bt t {1} = ENNReal.ofReal (1 / 2 + t) := by
  simp [Bt, Measure.add_apply, Measure.smul_apply]

/-- The two-point map `0 ↦ −R`, `1 ↦ R`. -/
def emb (R : ℝ) (hR : 0 ≤ R) : Fin 2 → Icc (-R) R := ![lowPt R hR, highPt R hR]

lemma map_Bt (hR : 0 ≤ R) (t : ℝ) : (Bt t).map (emb R hR) = Pt R hR t := by
  have hm : Measurable (emb R hR) := measurable_of_finite _
  rw [Bt, Measure.map_add _ _ hm, Measure.map_smul, Measure.map_smul, Measure.map_dirac' hm, Measure.map_dirac' hm]
  all_goals first | rfl | exact hm.aemeasurable

lemma klDiv_Bt {t : ℝ} (ht0 : 0 ≤ t) (ht : 4 * t ^ 2 ≤ 1 / 2) :
    klDiv (Bt 0) (Bt t) ≤ ENNReal.ofReal (4 * t ^ 2) := by
  have ht1 : t < 1 / 2 := by nlinarith
  haveI := Bt_prob (le_refl (0 : ℝ)) (by norm_num)
  haveI := Bt_prob ht0 ht1.le
  have hne : ∀ x : Fin 2, Bt t {x} ≠ 0 := by
    intro x; fin_cases x
    · simp only [Fin.zero_eta]; rw [Bt_zero_single]; exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
    · simp only [Fin.mk_one]; rw [Bt_one_single]; exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
  rw [TauCeti.klDiv_eq_ofReal_sum_log_singleton hne]
  apply ENNReal.ofReal_le_ofReal
  simp only [Fin.sum_univ_two, measureReal_def, Bt_zero_single, Bt_one_single, probReal_univ,
    measure_univ, ENNReal.toReal_one]
  simp only [sub_zero, add_zero, add_sub_cancel_right]
  rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1 / 2), ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 / 2 - t),
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 / 2 + t)]
  -- `½ log(½/(½−t)) + ½ log(½/(½+t)) = −½ log(1 − 4t²) ≤ 4t²`
  have h1 : (1 : ℝ) / 2 / (1 / 2 - t) = (1 - 2 * t)⁻¹ := by field_simp
  have h2 : (1 : ℝ) / 2 / (1 / 2 + t) = (1 + 2 * t)⁻¹ := by field_simp
  rw [h1, h2, Real.log_inv, Real.log_inv]
  have hpos : 0 < 1 - 4 * t ^ 2 := by linarith
  have hprod : Real.log (1 - 2 * t) + Real.log (1 + 2 * t) = Real.log (1 - 4 * t ^ 2) := by
    rw [← Real.log_mul (by linarith) (by linarith)]; ring_nf
  have hlb := Real.one_sub_inv_le_log_of_pos hpos
  have : 1 - (1 - 4 * t ^ 2)⁻¹ ≥ -(2 * (4 * t ^ 2)) := by
    rw [ge_iff_le, ← sub_nonneg]
    have : 1 - (1 - 4 * t ^ 2)⁻¹ - -(2 * (4 * t ^ 2)) = (4 * t ^ 2) * (1 - 2 * (4 * t ^ 2)) / (1 - 4 * t ^ 2) := by
      field_simp; ring
    rw [this]; apply div_nonneg _ hpos.le
    nlinarith
  nlinarith

end TwoPt

open TwoPt in
theorem loclower_instab : Claims.loclower_instab := by
  intro R ε δ κ hR m ρ hε hρ hvalid hκ hκm
  have hR' := hR.le
  have hmR : (0 : ℝ) < m := by
    have : (0 : ℝ) < m / 2 := lt_of_lt_of_le hκ hκm
    linarith
  set t := 1 / 2 * √(κ / m) with ht
  have hκm' : κ / m ≤ 1 / 2 := by rw [div_le_iff₀ hmR]; linarith
  have hsq : √(κ / m) ^ 2 = κ / m := Real.sq_sqrt (div_pos hκ hmR).le
  have ht0 : 0 ≤ t := by positivity
  have h4t : 4 * t ^ 2 = κ / m := by rw [ht]; nlinarith
  have h4t' : 4 * t ^ 2 ≤ 1 / 2 := by rw [h4t]; exact hκm'
  have ht1 : t ≤ 1 / 2 := by nlinarith
  haveI hPt := Pt_prob hR' ht0 ht1
  -- the event `A = {OT(P_t) ≤ ρ̂}`
  set A : Set (Fin m → Icc (-R) R) := {y | OTdisc ε (fun _ => 1 / 2) (cTwo R) (Pt R hR' t) ≤ (ρ y : EReal)}
  have hAm : MeasurableSet A := by
    have : A = (fun y => (ρ y : EReal)) ⁻¹' Ici (OTdisc ε (fun _ => 1 / 2) (cTwo R) (Pt R hR' t)) := rfl
    rw [this]; exact (measurable_coe_real_ereal.comp hρ) measurableSet_Ici
  have hA1 : 1 - δ ≤ (Measure.pi fun _ : Fin m => Pt R hR' t).real A := hvalid _ hPt
  -- inclusion of events
  obtain ⟨J₀, hJ₀, hJ₀le⟩ := OT_twoPt_le hε hR'
  have hsub : A ⊆ {y | OTdisc ε (fun _ => 1 / 2) (cTwo R) (twoPt R hR') +
      ((2 * R ^ 2 * √(κ / m) - ε * Real.log 2 : ℝ) : EReal) ≤ (ρ y : EReal)} := by
    intro y hy
    simp only [mem_setOf_eq] at hy ⊢
    refine le_trans ?_ ((OT_Pt_ge hε hR' ht0 ht1).trans hy)
    rw [hJ₀, ← EReal.coe_add, EReal.coe_le_coe_iff, ht]
    linarith
  -- TV between the product laws
  have hkl : klDiv (twoPt R hR') (Pt R hR' t) ≤ ENNReal.ofReal (4 * t ^ 2) := by
    haveI := Bt_prob (le_refl (0 : ℝ)) (by norm_num)
    haveI := Bt_prob ht0 ht1
    rw [twoPt_eq, ← map_Bt hR' 0, ← map_Bt hR' t]
    exact (klDiv_map_le _ _ (measurable_of_finite _)).trans (klDiv_Bt ht0 h4t')
  have hkl_ne : klDiv (twoPt R hR') (Pt R hR' t) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  have htv := StatFormal.Distances.tvDist_pi_le_sqrt_klDiv (twoPt R hR') (Pt R hR' t) m hkl_ne
  have hklr : (klDiv (twoPt R hR') (Pt R hR' t)).toReal ≤ 4 * t ^ 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hkl
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have htv' : StatFormal.Distances.tvDist (Measure.pi fun _ : Fin m => twoPt R hR')
      (Measure.pi fun _ : Fin m => Pt R hR' t) ≤ √(κ / 2) := by
    refine htv.trans (Real.sqrt_le_sqrt ?_)
    have : (m : ℝ) * (klDiv (twoPt R hR') (Pt R hR' t)).toReal ≤ m * (4 * t ^ 2) :=
      mul_le_mul_of_nonneg_left hklr hmR.le
    rw [h4t, mul_div_cancel₀ _ hmR.ne'] at this
    linarith
  have hlecam := StatFormal.Distances.measureReal_ge_sub_tvDist
    (μ := Measure.pi fun _ : Fin m => twoPt R hR') (ν := Measure.pi fun _ : Fin m => Pt R hR' t) hAm
  have hmono := measureReal_mono (μ := Measure.pi fun _ : Fin m => twoPt R hR') hsub
  linarith

open TwoPt in
theorem loclower_instab_var : Claims.loclower_instab_var := by
  intro R ε hR fs hε hmax
  have hR' := hR.le
  have hfoc := (StatFormal.RobustEquality.SemidualStrong.maximiser_foc _ 2 ε _ _ (twoPt R hR') fs
    (setting_two hε hR') hmax).1 0
  rw [integral_twoPt, cTwo_low0, cTwo_high0, gsoft_low, gsoft_high] at hfoc
  set u0 := Real.exp (fs 0 / ε)
  set u1 := Real.exp (fs 1 / ε)
  set k := Real.exp (-(4 * R ^ 2) / ε)
  have hu0 : 0 < u0 := Real.exp_pos _
  have hu1 : 0 < u1 := Real.exp_pos _
  have hk : 0 < k := Real.exp_pos _
  have e1 : Real.exp ((fs 1 - 4 * R ^ 2) / ε) = u1 * k := by
    rw [← Real.exp_add]; congr 1; ring
  have e0 : Real.exp ((fs 0 - 4 * R ^ 2) / ε) = u0 * k := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, e0] at hfoc
  set X := 1 / 2 * u0 + 1 / 2 * (u1 * k)
  set Y := 1 / 2 * (u0 * k) + 1 / 2 * u1
  have hX : 0 < X := by positivity
  have hY : 0 < Y := by positivity
  have eX : Real.exp ((-ε * Real.log X - 0) / ε) = X⁻¹ := by
    rw [show (-ε * Real.log X - 0) / ε = -Real.log X by field_simp; ring, Real.exp_neg, Real.exp_log hX]
  have eY : Real.exp ((-ε * Real.log Y - 4 * R ^ 2) / ε) = Y⁻¹ * k := by
    rw [show (-ε * Real.log Y - 4 * R ^ 2) / ε = -Real.log Y + (-(4 * R ^ 2) / ε) by field_simp; ring,
      Real.exp_add, Real.exp_neg, Real.exp_log hY]
  have eL : Real.exp (-fs 0 / ε) = u0⁻¹ := by rw [neg_div, Real.exp_neg]
  rw [eX, eY, eL] at hfoc
  -- `k (u₁² − u₀²) = 0`
  have hkey : u0 = u1 := by
    have h := hfoc
    field_simp at h
    have : k * (u1 - u0) * (u1 + u0) = 0 := by simp only [X, Y] at h; nlinarith
    rcases mul_eq_zero.1 this with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hk.ne'
      · linarith
    · linarith
  have hXY : X = Y := by simp only [X, Y]; rw [hkey]; ring
  have hlh : gsoft ε (fun _ => 1 / 2) fs (cTwo R) (lowPt R hR') = gsoft ε (fun _ => 1 / 2) fs (cTwo R) (highPt R hR') := by
    rw [gsoft_low, gsoft_high, e1, e0]
    change -ε * Real.log X = -ε * Real.log Y
    rw [hXY]
  refine ⟨hlh, ?_⟩
  -- the potential is `P₀`-a.e. constant
  set g := fun y => gsoft ε (fun _ => (1 : ℝ) / 2) fs (cTwo R) y
  have hae : g =ᵐ[twoPt R hR'] fun _ => g (lowPt R hR') := by
    rw [twoPt, Filter.EventuallyEq, MeasureTheory.ae_add_measure_iff]
    refine ⟨Measure.ae_smul_measure ((ae_eq_dirac g).mono fun y hy => hy) _,
      Measure.ae_smul_measure ((ae_eq_dirac g).mono fun y hy => ?_) _⟩
    rw [hy]; exact hlh.symm
  rw [variance_congr hae]
  simp [variance, evariance]

open TwoPt in
theorem loclower_envelope : Claims.loclower_envelope := by
  intro R hR
  have hR' := hR.le
  have hD : ∀ y y' : Icc (-R) R, Dbar (cTwo R) y y' = max |cTwo R 0 y - cTwo R 0 y'| |cTwo R 1 y - cTwo R 1 y'| := by
    intro y y'
    unfold Dbar
    refine le_antisymm (ciSup_le fun i => ?_) (max_le (le_ciSup (f := fun i : Fin 2 => |cTwo R i y - cTwo R i y'|) (Finite.bddAbove_range _) 0)
      (le_ciSup (f := fun i : Fin 2 => |cTwo R i y - cTwo R i y'|) (Finite.bddAbove_range _) 1))
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  simp only [integral_twoPt, hD, cTwo_low0, cTwo_low1, cTwo_high0, cTwo_high1]
  have h4 : (0 : ℝ) ≤ 4 * R ^ 2 := by positivity
  simp only [sub_self, abs_zero, zero_sub, sub_zero, abs_neg, abs_of_nonneg h4, max_self, max_eq_left h4]
  rw [show (1 : ℝ) / 2 * (1 / 2 * (1 / 2 * 0 ^ 2 + 1 / 2 * (4 * R ^ 2) ^ 2) +
      1 / 2 * (1 / 2 * (4 * R ^ 2) ^ 2 + 1 / 2 * 0 ^ 2)) = (2 * R ^ 2) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

end StatFormal.Wave29d
