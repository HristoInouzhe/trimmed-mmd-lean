import StatFormal.Wave31tq.RouteSNorm
import StatFormal.Lib.MollifierNorm.Boundary
import StatFormal.Lib.TIKernel.MMD
import StatFormal.Wave31to.Proofs

/-!
# Wave 31tq, route S: Theorem S4.10, the margin for Sobolev kernels (untrusted proof file)

Q11 `newsobolev_thm`, with the cross-chunk hypotheses Q1 `tv_density` (part (b): `|P − Q|` has density `|p − q|` and
`err(f) = ∫ |1_G − f| |p − q|`) and Q5 `sobolev_angular` (part (a): `‖f‖²_ℋ ≤ ‖f‖²_{H^s}/c`). Route (printed, S4 :605-618):
Lemma S4.9 (`newsobnorm_route`) bounds `‖f_w‖_{H^s}`, and Q5(a) gives the representer with `‖g‖² ≤ B/c`; for the error, off
`B_{ρ−1}` `|1_G − f_w| ≤ 1` contributes `T(ρ)`, and on `B_{ρ−1}` the mollified indicator equals `1_G` at distance `> w` from `∂G`
(`MollifierNorm.mollify_eq_indicator_of_lt_infDist`), while near `∂G` (G2), (G3) give `ℓ w^r V_ρ w`; the certified
`Wave31to.newapproxgen_ii` and `newapproxgen_iii_a` give the bound on `D̄ = uPath` and `D̄ ≤ D`.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal ContDiff symmDiff InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tq.RouteS

open StatFormal.Wave31tp StatFormal.TrimmedMMD.Unconditional

/-- The constant `C_{d,s,b}` is positive. -/
theorem sobConst_pos {cd s Cb : ℝ} {m : ℕ} (hcd : 0 < cd) (hs : 1 / 2 < s) (hm : 2 * s - 1 < 4 * m) :
    0 < sobConst cd s Cb m := by
  unfold sobConst
  have hr : 0 < 1 - (2 : ℝ) ^ (1 - 2 * s) := sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))
  have hy : 0 < 1 - (2 : ℝ) ^ (-(4 * (m : ℝ) + 1 - 2 * s)) :=
    sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))
  positivity

/-- A density of a probability measure is integrable. -/
theorem integrable_of_density {V : Type*} [MeasurableSpace V] {μ P : Measure V} [IsProbabilityMeasure P] {p : V → ℝ}
    (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hP : P = μ.withDensity (fun x => ENNReal.ofReal (p x))) :
    Integrable p μ := by
  refine ⟨hp.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hp0)]
  have : ∫⁻ x, ENNReal.ofReal (p x) ∂μ = 1 := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hP, measure_univ]
  rw [this]; exact ENNReal.one_lt_top

theorem newsobolev_thm_of (h1 : Claims.tv_density) (h5 : Claims.sobolev_angular) : Claims.newsobolev_thm := by
  intro d _ V _ _ _ _ _ hd H _ _ _ _ φ k₀ c s P Q _ _ p q G c₀ ρ r ℓ w₀ Piρ Vρ b m hk₀c hk₀i hφ hc hs hspec hp hq hp0
    hq0 hP hQ htv0 htv1 hG hGp hGq hρ hr hℓ hw₀ hw₀1 hPi hV hG1 hG2 hG3 hb hb0 hb1 hbs hm w hw
  dsimp only
  set f : V → ℝ := mollify (G ∩ ball c₀ ρ) (dilateR w b) with hfdef
  set C : ℝ := sobConst (cJ d) s (lapC m b) m with hCdef
  set B : ℝ := 2 ^ s * (volume (ball c₀ ρ)).toReal + C * Piρ * w ^ (1 - 2 * s) with hBdef
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hs' : 1 / 2 < s := by linarith
  have hE : MeasurableSet (G ∩ ball c₀ ρ) := hG.measurableSet.inter measurableSet_ball
  have hEb : Bornology.IsBounded (G ∩ ball c₀ ρ) := isBounded_ball.subset inter_subset_right
  have hw0 : 0 < w := hw.1
  have hw1 : w ≤ 1 := hw.2.trans hw₀1
  obtain ⟨hcd, hQ10⟩ := newsobnorm_route d V hd s Piρ (G ∩ ball c₀ ρ) b m hs' hE hEb hG1 hb hb0 hb1 hbs hm
  obtain ⟨h01, hsm, -, hsob⟩ := hQ10 w hw0
  obtain ⟨-, -, -, -, -, -, hfL2, -⟩ := FourierOps.mollify_smooth_facts hE hEb hb hb0 hb1 hbs hw0
  -- the denominator `B`
  have hC : 0 < C := sobConst_pos hcd hs' hm
  have hball_pos : 0 < (volume (ball c₀ ρ)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos _ _ (by linarith)).ne' measure_ball_lt_top.ne
  have hvolE : (volume (G ∩ ball c₀ ρ)).toReal ≤ (volume (ball c₀ ρ)).toReal :=
    ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono inter_subset_right)
  have hwpow : 0 < w ^ (1 - 2 * s) := Real.rpow_pos_of_pos hw0 _
  have hCPw : 0 ≤ C * Piρ * w ^ (1 - 2 * s) := mul_nonneg (mul_nonneg hC.le hPi) hwpow.le
  have h2s : 0 < (2 : ℝ) ^ s := by positivity
  have hB : 0 < B := by have := mul_pos h2s hball_pos; linarith
  have hsobB : sobolevA s (fun x => (f x : ℂ)) ≤ ENNReal.ofReal B := (hsob hw1).trans
    (ENNReal.ofReal_le_ofReal (by have := mul_le_mul_of_nonneg_left hvolE h2s.le; linarith))
  -- the representer
  obtain ⟨g, hgrep, hgnorm⟩ := (h5.1 V H φ k₀ c s hk₀c hk₀i hφ hc hspec).1 f hsm.continuous hfL2
    (hsobB.trans_lt ENNReal.ofReal_lt_top)
  have hgB : ‖g‖ ^ 2 ≤ B / c := by
    have : ENNReal.ofReal (‖g‖ ^ 2) ≤ ENNReal.ofReal (B / c) := by
      rw [ENNReal.ofReal_div_of_pos hc]; exact hgnorm.trans (ENNReal.div_le_div_right hsobB _)
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
  -- the error
  obtain ⟨habs, -, -, -, herr⟩ := h1.2 V P Q p q hp hq hp0 hq0 hP hQ
  have hfmeas : Measurable f := hsm.continuous.measurable
  have herrf : StatFormal.Wave31to.errFn P Q f = ∫ x, |G.indicator (fun _ => (1 : ℝ)) x - f x| * |p x - q x| :=
    herr G f hG.measurableSet hfmeas h01 hGp hGq
  have hpq : Integrable (fun x => |p x - q x|) :=
    ((integrable_of_density hp hp0 hP).sub (integrable_of_density hq hq0 hQ)).abs
  set S : Set V := {x | x ∈ ball c₀ ρ ∧ infDist x (frontier G) ≤ w} with hSdef
  have hSm : MeasurableSet S :=
    measurableSet_ball.inter (measurableSet_le (continuous_infDist_pt _).measurable measurable_const)
  have hSfin : volume S ≠ ⊤ := ((measure_mono fun x (hx : x ∈ S) => hx.1).trans_lt measure_ball_lt_top).ne
  set Bc : Set V := (ball c₀ (ρ - 1))ᶜ with hBcdef
  have hBcm : MeasurableSet Bc := measurableSet_ball.compl
  have hpt : ∀ᵐ x ∂volume, |G.indicator (fun _ => (1 : ℝ)) x - f x| * |p x - q x| ≤
      Bc.indicator (fun x => |p x - q x|) x + S.indicator (fun _ => ℓ * w ^ r) x := by
    filter_upwards [hG3] with x hx
    have hfx := h01 x
    have hind : |G.indicator (fun _ => (1 : ℝ)) x - f x| ≤ 1 := by
      rw [abs_le]
      by_cases hxG : x ∈ G
      · rw [indicator_of_mem hxG]; constructor <;> linarith [hfx.1, hfx.2]
      · rw [indicator_of_notMem hxG]; constructor <;> linarith [hfx.1, hfx.2]
    have hS0 : 0 ≤ S.indicator (fun _ => ℓ * w ^ r) x :=
      indicator_nonneg (fun _ _ => mul_nonneg hℓ.le (Real.rpow_nonneg hw0.le _)) x
    by_cases hxB : x ∈ ball c₀ (ρ - 1)
    · rw [indicator_of_notMem (show x ∉ Bc from fun h => h hxB), zero_add]
      by_cases hdx : infDist x (frontier G) ≤ w
      · have hxρ : x ∈ ball c₀ ρ := ball_subset_ball (by linarith) hxB
        rw [indicator_of_mem (show x ∈ S from ⟨hxρ, hdx⟩)]
        have hpqx : |p x - q x| ≤ ℓ * w ^ r := (hx hxρ (hdx.trans hw.2)).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow infDist_nonneg hdx hr.le) hℓ.le)
        calc |G.indicator (fun _ => (1 : ℝ)) x - f x| * |p x - q x| ≤ 1 * (ℓ * w ^ r) :=
              mul_le_mul hind hpqx (abs_nonneg _) zero_le_one
          _ = ℓ * w ^ r := one_mul _
      · have hfx' : f x = G.indicator (fun _ => (1 : ℝ)) x :=
          MollifierNorm.mollify_eq_indicator_of_lt_infDist hG hb hb0 hb1 hbs hw0 hw1 hxB (not_le.1 hdx)
        rw [hfx', sub_self, abs_zero, zero_mul]; exact hS0
    · rw [indicator_of_mem (show x ∈ Bc from hxB)]
      calc |G.indicator (fun _ => (1 : ℝ)) x - f x| * |p x - q x| ≤ 1 * |p x - q x| :=
            mul_le_mul_of_nonneg_right hind (abs_nonneg _)
        _ = |p x - q x| := one_mul _
        _ ≤ |p x - q x| + S.indicator (fun _ => ℓ * w ^ r) x := le_add_of_nonneg_right hS0
  have hSi : Integrable (S.indicator (fun _ => ℓ * w ^ r)) := (integrable_indicator_iff hSm).2 (integrableOn_const hSfin)
  have hrhs : Integrable (fun x => Bc.indicator (fun x => |p x - q x|) x + S.indicator (fun _ => ℓ * w ^ r) x) :=
    (hpq.indicator hBcm).add hSi
  have htail : ∫ x in Bc, |p x - q x| = tailOut P Q c₀ ρ := by
    unfold tailOut
    rw [habs, withDensity_apply _ hBcm, ← ofReal_integral_eq_lintegral_ofReal hpq.integrableOn
      (Filter.Eventually.of_forall fun x => abs_nonneg _),
      ENNReal.toReal_ofReal (setIntegral_nonneg hBcm fun x _ => abs_nonneg _)]
  have hSvol : (volume S).toReal ≤ Vρ * w := ENNReal.toReal_le_of_le_ofReal (by positivity) (hG2 w hw)
  have herrbound : StatFormal.Wave31to.errFn P Q f ≤ ℓ * Vρ * w ^ (r + 1) + tailOut P Q c₀ ρ := by
    rw [herrf]
    calc ∫ x, |G.indicator (fun _ => (1 : ℝ)) x - f x| * |p x - q x|
        ≤ ∫ x, (Bc.indicator (fun x => |p x - q x|) x + S.indicator (fun _ => ℓ * w ^ r) x) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hrhs hpt
      _ = (∫ x in Bc, |p x - q x|) + ℓ * w ^ r * (volume S).toReal := by
          rw [integral_add (hpq.indicator hBcm) hSi, integral_indicator hBcm, integral_indicator hSm,
            setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
      _ ≤ ℓ * Vρ * w ^ (r + 1) + tailOut P Q c₀ ρ := by
          rw [htail, Real.rpow_add_one hw0.ne']
          have := mul_le_mul_of_nonneg_left hSvol (mul_nonneg hℓ.le (Real.rpow_nonneg hw0.le r))
          linarith
  refine ⟨⟨g, hgrep, hgB⟩, h01, herrbound, fun ε hε => ?_⟩
  -- the path
  have hφc : Continuous φ := TIKernel.phi_continuous hφ hk₀c
  have hφm : StronglyMeasurable φ := hφc.stronglyMeasurable
  have hφb : ∀ x, ‖φ x‖ ≤ √(k₀ 0) := fun x => by
    rw [← TIKernel.gram_norm_sq hφ x, Real.sqrt_sq (norm_nonneg _)]
  obtain ⟨-, hiii⟩ := StatFormal.Wave31to.newapproxgen_iii_a V H P Q φ (√(k₀ 0)) hφm hφb htv0 htv1
  obtain ⟨-, hUD, hxi, -⟩ := hiii ε hε
  refine ⟨hUD, ?_⟩
  have hxi0 : 0 ≤ StatFormal.Wave31to.xiH φ P Q ε :=
    Real.sSup_nonneg fun t ⟨g', _, _, ht⟩ => ht ▸ div_nonneg (le_max_right _ _) (norm_nonneg _)
  rcases le_or_gt (ε - ℓ * Vρ * w ^ (r + 1) - tailOut P Q c₀ ρ) 0 with hneg | hpos
  · rw [max_eq_right hneg, mul_zero, zero_div]; exact hxi0.trans hxi
  rw [max_eq_left hpos.le]
  have hwit : StatFormal.Wave31to.wit φ g = f := funext hgrep
  have hgF : g ∈ StatFormal.Wave31to.Fset φ := fun x => by
    rw [show StatFormal.Wave31to.wit φ g x = f x from hgrep x]; exact h01 x
  have hg0 : g ≠ 0 := by
    rintro rfl
    have hf0 : ∀ x, f x = 0 := fun x => by rw [← hgrep x, inner_zero_left]
    have h0 := (StatFormal.Wave31to.newapprox_err V P Q f hfmeas h01).1
    simp only [hf0, integral_zero, sub_zero] at h0
    linarith [hε.2]
  obtain ⟨-, hii⟩ := StatFormal.Wave31to.newapproxgen_ii V H P Q φ (√(k₀ 0)) g hφm hφb htv0 htv1 hgF
  have hii' := hii hg0 ε hε
  rw [hwit] at hii'
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg0
  have hgle : ‖g‖ ≤ √B / √c := by
    rw [← Real.sqrt_div hB.le, ← Real.sqrt_sq (norm_nonneg g)]
    exact Real.sqrt_le_sqrt hgB
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  have hsB : 0 < √B := Real.sqrt_pos.2 hB
  calc √c * (ε - ℓ * Vρ * w ^ (r + 1) - tailOut P Q c₀ ρ) / √B
      = (ε - ℓ * Vρ * w ^ (r + 1) - tailOut P Q c₀ ρ) / (√B / √c) := by field_simp
    _ ≤ (ε - ℓ * Vρ * w ^ (r + 1) - tailOut P Q c₀ ρ) / ‖g‖ := div_le_div_of_nonneg_left hpos.le hgpos hgle
    _ ≤ (ε - StatFormal.Wave31to.errFn P Q f) / ‖g‖ := by
        refine div_le_div_of_nonneg_right ?_ hgpos.le
        linarith
    _ ≤ _ := hii'

end StatFormal.Wave31tq.RouteS
