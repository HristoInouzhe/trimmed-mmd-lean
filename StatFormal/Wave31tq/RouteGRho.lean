import StatFormal.Wave31tq.RouteGThm
import StatFormal.Lib.BandLimited.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Wave 31tq, chunk G: the choice `ρ_ε` and the logarithmic bound of Theorem S4.13 (Q17 `newgauss_thm_rho`)

Route (S4 :711-715, :717-726). With `b` the band-limited density of Q15 (`m₂ = π²`, `b̄(t) ≤ 16π/(3t³)` for `t ≥ 2^{1/2}π`)
and `T₊(t) ≤ C_T e^{−t/a}`:
(a) `ρ_ε = max{2, 2a log(8C_T/((1−θ)ε))}` gives `2T₊(ρ_ε/2) ≤ (1−θ)ε/4`, and `b̄(Ω_ε t) ≤ (1−θ)ε/16` for `t = r₀ ∧ 1` and
`t = ρ_ε/2 ≥ 1` once `ε` is small (`Lib/BandLimited/Asymptotics.cubic_tail_small`, `Ω_ε = √(ℓπ²/(2θε))`), so the condition of
Theorem S4.13 holds;
(b) Theorem S4.13 (`newgauss_thm_of`) then gives `D̄_{α⋆−ε} ≥ ((1−θ)ε/2)(√(2π)σ/ρ_ε)^{1/2} e^{−σ²ℓπ²/(8θε)} > 0`, and
`ρ_ε ≤ (2 + 4a) log(1/ε)` once `ε ≤ (1−θ)/(8C_T)`; for `ε ≤ e^{−3}` (so `log log(1/ε) ≥ 1`) the additive constants are absorbed
into `C log log(1/ε)`.
The facts of the density are taken from `Claims.bandB_facts` (proved in this chunk, `bandB_facts_route`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal NNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteG

open StatFormal StatFormal.Wave31tp StatFormal.TrimmedMMD.Unconditional

/-- The exponential tail at `ρ_ε/2` is at most `(1−θ)ε/8`. -/
theorem tail_rho_le (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {x₀ CT a θ ε : ℝ} (hCT : 0 < CT)
    (ha : 0 < a) (hθ1 : θ < 1) (hε : 0 < ε) (htail : ∀ t : ℝ, 0 < t → tailPlus P Q x₀ t ≤ CT * Real.exp (-t / a)) :
    tailPlus P Q x₀ (max 2 (2 * a * Real.log (8 * CT / ((1 - θ) * ε))) / 2) ≤ (1 - θ) * ε / 8 := by
  set ρ := max 2 (2 * a * Real.log (8 * CT / ((1 - θ) * ε))) with hρ
  have h1θ : 0 < 1 - θ := by linarith
  have hY : 0 < 8 * CT / ((1 - θ) * ε) := by positivity
  have hρ2' : (2 : ℝ) ≤ ρ := le_max_left _ _
  have hρ2 : 0 < ρ / 2 := by linarith
  refine (htail _ hρ2).trans ?_
  have hlog : Real.log (8 * CT / ((1 - θ) * ε)) ≤ ρ / 2 / a := by
    rw [le_div_iff₀ ha]
    have : 2 * a * Real.log (8 * CT / ((1 - θ) * ε)) ≤ ρ := le_max_right _ _
    linarith
  calc CT * Real.exp (-(ρ / 2) / a) ≤ CT * Real.exp (-Real.log (8 * CT / ((1 - θ) * ε))) := by
        gcongr
        rw [neg_div]; linarith
    _ = (1 - θ) * ε / 8 := by
        rw [Real.exp_neg, Real.exp_log hY]
        field_simp

/-- Part (a) of Q17 `newgauss_thm_rho`: for all small `ε`, `ρ_ε` satisfies the condition of Theorem S4.13 (with `b` = `bandB`,
whose tail is `≤ 16π/(3t³)` for `t ≥ 2^{1/2}π`). -/
theorem rho_condition (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {x₀ ℓ CT a θ : ℝ} {r₀ : ℝ≥0∞}
    (hℓ : 0 < ℓ) (hr₀ : 0 < r₀) (hCT : 0 < CT) (ha : 0 < a) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (htail : ∀ t : ℝ, 0 < t → tailPlus P Q x₀ t ≤ CT * Real.exp (-t / a))
    (hb0 : ∀ t, 0 ≤ bandB t) (hb1 : ∫ t, bandB t = 1)
    (hcub : ∀ t, √2 * Real.pi ≤ t → bbar bandB t ≤ 16 * Real.pi / (3 * t ^ 3)) :
    ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ ε, 0 < ε → ε ≤ min ε₂ (StatFormal.Distances.tvDist P Q) →
      2 * tailPlus P Q x₀ (max 2 (2 * a * Real.log (8 * CT / ((1 - θ) * ε))) / 2) +
        2 * StatFormal.Distances.tvDist P Q * (bbarE bandB (√(ℓ * Real.pi ^ 2 / (2 * θ * ε))) r₀ +
          bbar bandB (√(ℓ * Real.pi ^ 2 / (2 * θ * ε)) * max 2 (2 * a * Real.log (8 * CT / ((1 - θ) * ε))) / 2)) ≤
        (1 - θ) * ε / 2 := by
  set αs := StatFormal.Distances.tvDist P Q with hαs
  have hα1 : αs ≤ 1 := StatFormal.Distances.tvDist_le_one
  have hα0 : 0 ≤ αs := StatFormal.Distances.tvDist_nonneg P Q
  have h1θ : 0 < 1 - θ := by linarith
  have hanti : Antitone (bbar bandB) := BandLimited.tail_antitone hb0 hb1
  have hbb0 : ∀ t, 0 ≤ bbar bandB t := BandLimited.tail_nonneg hb0
  -- the scale `s₀ = min 1 r₀`
  set s₀ : ℝ := if r₀ = ⊤ then 1 else min 1 r₀.toReal with hs₀
  have hs₀pos : 0 < s₀ := by
    rw [hs₀]; split_ifs with h
    · exact one_pos
    · exact lt_min one_pos (ENNReal.toReal_pos hr₀.ne' h)
  have hs₀1 : s₀ ≤ 1 := by rw [hs₀]; split_ifs <;> simp
  set A : ℝ := ℓ * Real.pi ^ 2 / (2 * θ) with hA
  have hA0 : 0 < A := by positivity
  have hcub' : ∀ t, √2 * Real.pi ≤ t → bbar bandB t ≤ (16 * Real.pi / 3) / t ^ 3 := fun t ht => by
    rw [div_div]; exact hcub t ht
  obtain ⟨ε₂, hε₂, hsmall⟩ := BandLimited.cubic_tail_small (T := bbar bandB) (by positivity) hcub' hA0 hs₀pos
    (show (0 : ℝ) < (1 - θ) / 16 by positivity)
  refine ⟨ε₂, hε₂, fun ε hε hεle => ?_⟩
  have hΩeq : √(ℓ * Real.pi ^ 2 / (2 * θ * ε)) = √(A / ε) := by
    rw [hA]; congr 1; field_simp
  set ρ := max 2 (2 * a * Real.log (8 * CT / ((1 - θ) * ε))) with hρ
  have hρ2 : (2 : ℝ) ≤ ρ := le_max_left _ _
  rw [hΩeq]
  set Ω := √(A / ε) with hΩ
  have hΩ0 : 0 < Ω := Real.sqrt_pos.2 (div_pos hA0 hε)
  have hsm := hsmall ε hε (hεle.trans (min_le_left _ _))
  have hT := tail_rho_le P Q hCT ha hθ1 hε htail
  have hB' : bbar bandB (Ω * ρ / 2) ≤ (1 - θ) / 16 * ε := by
    refine (hanti ?_).trans hsm
    have : Ω * s₀ ≤ Ω := by nlinarith
    nlinarith
  have hE' : bbarE bandB Ω r₀ ≤ (1 - θ) / 16 * ε := by
    rw [bbarE]; split_ifs with h
    · positivity
    · refine (hanti ?_).trans hsm
      have : s₀ ≤ r₀.toReal := by rw [hs₀, ite_eq_right_iff.mpr (fun h' => absurd h' h)]; exact min_le_right _ _
      exact mul_le_mul_of_nonneg_left this hΩ0.le
  have hE0 : 0 ≤ bbarE bandB Ω r₀ := by rw [bbarE]; split_ifs; exacts [le_rfl, hbb0 _]
  have hsum0 : 0 ≤ bbarE bandB Ω r₀ + bbar bandB (Ω * ρ / 2) := add_nonneg hE0 (hbb0 _)
  nlinarith [mul_le_mul_of_nonneg_right hα1 hsum0]

/-- The arithmetic of part (b) of Q17 `newgauss_thm_rho`: a lower bound `U ≥ ((1−θ)ε/2)(√(2π)σ/ρ_ε)^{1/2}e^{−X}` gives
`log(1/U) ≤ X + log(1/ε) + C log log(1/ε)` for `ε ≤ (1−θ)/(8C_T)` and `ε ≤ e^{−3}`, with an explicit `C`. -/
theorem log_bound {σ θ CT a ε U : ℝ} (hσ : 0 < σ) (hθ1 : θ < 1) (hCT : 0 < CT) (ha : 0 < a) (hε0 : 0 < ε)
    (hεC : ε ≤ (1 - θ) / (8 * CT)) (hεe : ε ≤ Real.exp (-3)) (X : ℝ)
    (hlow : (1 - θ) * ε / 2 * √(√(2 * Real.pi) * σ / max 2 (2 * a * Real.log (8 * CT / ((1 - θ) * ε)))) *
      Real.exp (-X) ≤ U) :
    0 < U ∧ Real.log (1 / U) ≤ X + Real.log (1 / ε) +
      (1 / 2 + |Real.log (2 / (1 - θ)) + Real.log (2 + 4 * a) / 2 - Real.log (√(2 * Real.pi) * σ) / 2|) *
        Real.log (Real.log (1 / ε)) := by
  have h1θ : 0 < 1 - θ := by linarith
  set ρ := max 2 (2 * a * Real.log (8 * CT / ((1 - θ) * ε))) with hρ
  have hρ2 : (2 : ℝ) ≤ ρ := le_max_left _ _
  have hρ0 : 0 < ρ := by linarith
  set K₀ : ℝ := Real.log (2 / (1 - θ)) + Real.log (2 + 4 * a) / 2 - Real.log (√(2 * Real.pi) * σ) / 2 with hK₀
  set B₀ := (1 - θ) * ε / 2 * √(√(2 * Real.pi) * σ / ρ) * Real.exp (-X) with hB₀
  have hB₀pos : 0 < B₀ := by positivity
  have hU : 0 < U := lt_of_lt_of_le hB₀pos hlow
  refine ⟨hU, ?_⟩
  set L := Real.log (1 / ε) with hL
  have hL3 : 3 ≤ L := by
    rw [hL, one_div, Real.log_inv, le_neg]
    calc Real.log ε ≤ Real.log (Real.exp (-3)) := Real.log_le_log hε0 hεe
      _ = -3 := Real.log_exp _
  have hlogL : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_d9
    linarith
  have hlog1 : Real.log (1 / U) ≤ Real.log (1 / B₀) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hB₀pos hlow)
  have hσ2 : 0 < √(2 * Real.pi) * σ := by positivity
  have hlogB : Real.log (1 / B₀) =
      X + Real.log (2 / (1 - θ)) + L + (Real.log ρ - Real.log (√(2 * Real.pi) * σ)) / 2 := by
    have hc : (1 - θ) * ε / 2 ≠ 0 := by positivity
    have hs : √(√(2 * Real.pi) * σ / ρ) ≠ 0 := by positivity
    have he : Real.exp (-X) ≠ 0 := by positivity
    have hcs : (1 - θ) * ε / 2 * √(√(2 * Real.pi) * σ / ρ) ≠ 0 := mul_ne_zero hc hs
    have hnn : 0 ≤ √(2 * Real.pi) * σ / ρ := by positivity
    have e1 : Real.log B₀ = Real.log ((1 - θ) * ε / 2) + Real.log (√(2 * Real.pi) * σ / ρ) / 2 - X := by
      rw [hB₀, Real.log_mul hcs he, Real.log_mul hc hs, Real.log_exp, Real.log_sqrt hnn]; ring
    have h2θ : (2 / (1 - θ)) ≠ 0 := by positivity
    have e2 : Real.log ((1 - θ) * ε / 2) = Real.log ε - Real.log (2 / (1 - θ)) := by
      rw [show (1 - θ) * ε / 2 = ε / (2 / (1 - θ)) by field_simp, Real.log_div hε0.ne' h2θ]
    have e3 : L = -Real.log ε := by rw [hL, one_div, Real.log_inv]
    have e4 : Real.log (√(2 * Real.pi) * σ / ρ) = Real.log (√(2 * Real.pi) * σ) - Real.log ρ :=
      Real.log_div hσ2.ne' hρ0.ne'
    rw [one_div, Real.log_inv, e1, e2, e3, e4]
    ring
  -- `ρ_ε ≤ (2 + 4a) L`
  have hρL : ρ ≤ (2 + 4 * a) * L := by
    have hlogY : Real.log (8 * CT / ((1 - θ) * ε)) ≤ 2 * L := by
      have hY : 8 * CT / ((1 - θ) * ε) ≤ (1 / ε) * (1 / ε) := by
        rw [div_le_iff₀ (by positivity)]
        have h8 : 8 * CT ≤ (1 - θ) / ε := by
          rw [le_div_iff₀ hε0]; rw [le_div_iff₀ (by positivity)] at hεC; linarith
        calc 8 * CT ≤ (1 - θ) / ε := h8
          _ = 1 / ε * (1 / ε) * ((1 - θ) * ε) := by field_simp
      have hie : (1 / ε) ≠ 0 := by positivity
      calc Real.log (8 * CT / ((1 - θ) * ε)) ≤ Real.log ((1 / ε) * (1 / ε)) := Real.log_le_log (by positivity) hY
        _ = 2 * L := by rw [Real.log_mul hie hie, hL]; ring
    rw [hρ]
    refine max_le (by nlinarith) ?_
    nlinarith
  have hlogρ : Real.log ρ ≤ Real.log (2 + 4 * a) + Real.log L := by
    have h2a : (2 + 4 * a) ≠ 0 := by positivity
    have hL0 : L ≠ 0 := by linarith
    rw [← Real.log_mul h2a hL0]
    exact Real.log_le_log hρ0 hρL
  have hK₀le : K₀ ≤ |K₀| * Real.log L := by
    calc K₀ ≤ |K₀| := le_abs_self K₀
      _ = |K₀| * 1 := (mul_one _).symm
      _ ≤ |K₀| * Real.log L := mul_le_mul_of_nonneg_left hlogL (abs_nonneg _)
  calc Real.log (1 / U) ≤ Real.log (1 / B₀) := hlog1
    _ = X + Real.log (2 / (1 - θ)) + L + (Real.log ρ - Real.log (√(2 * Real.pi) * σ)) / 2 := hlogB
    _ ≤ X + L + (Real.log L / 2 + K₀) := by linarith [hlogρ, hK₀]
    _ ≤ X + L + (1 / 2 + |K₀|) * Real.log L := by linarith [hK₀le]

/-- Q17 `newgauss_thm_rho`, from Q1(b) (`Claims.tv_density`) and the facts of the density `bandB` (`Claims.bandB_facts`). -/
theorem newgauss_thm_rho_of_facts (htv : Claims.tv_density) (hB : Claims.bandB_facts) : Claims.newgauss_thm_rho := by
  intro H _ _ _ _ φ σ P Q _ _ p q x₀ ℓ r₀ CT a θ hσ hφ hp hq hp0 hq0 hP hQ hsgn1 hsgn2 hℓ hr₀ hlip hCT ha htail hθ0 hθ1 hα0
  obtain ⟨-, ⟨hbc, -, hbev, hb0, -, hb1, -, hbft, -⟩, ⟨hm, hm2, -, -⟩, hd⟩ := hB
  obtain ⟨ε₂, hε₂, hcond⟩ := rho_condition P Q hℓ hr₀ hCT ha hθ0 hθ1 htail hb0 hb1 (fun t ht => (hd t ht).2.2)
  have h1θ : 0 < 1 - θ := by linarith
  set αs := StatFormal.Distances.tvDist P Q with hαs
  set ε₃ : ℝ := min (min ε₂ αs) (min ((1 - θ) / (8 * CT)) (Real.exp (-3))) with hε₃
  have hε₃0 : 0 < ε₃ := by positivity
  have he3 : Real.exp (-3) < Real.exp (-1) := Real.exp_lt_exp.2 (by norm_num)
  refine ⟨⟨ε₂, hε₂, fun ε hε => hcond ε hε.1 hε.2⟩,
    1 / 2 + |Real.log (2 / (1 - θ)) + Real.log (2 + 4 * a) / 2 - Real.log (√(2 * Real.pi) * σ) / 2|, ε₃, hε₃0,
    lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) he3, (min_le_left _ _).trans (min_le_right _ _),
    fun ε hε => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hε2a : ε ≤ min ε₂ αs := hε.2.trans (min_le_left _ _)
  have hεα : ε ≤ αs := hε2a.trans (min_le_right _ _)
  have hεC : ε ≤ (1 - θ) / (8 * CT) := hε.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεe : ε ≤ Real.exp (-3) := hε.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρ0 : 0 < max 2 (2 * a * Real.log (8 * CT / ((1 - θ) * ε))) :=
    lt_of_lt_of_le two_pos (le_max_left _ _)
  have hthm := newgauss_thm_of htv H φ σ P Q p q bandB x₀ ℓ r₀ hσ hφ hp hq hp0 hq0 hP hQ hsgn1 hsgn2 hℓ hr₀ hlip
    hbc.measurable hb0 hb1 hbev hbft hm θ ε (max 2 (2 * a * Real.log (8 * CT / ((1 - θ) * ε)))) hθ0 hθ1 hε0 hεα hρ0
  simp only [hm2] at hthm
  obtain ⟨-, hlow, -⟩ := hthm (hcond ε hε0 hε2a)
  exact log_bound hσ hθ1 hCT ha hε0 hεC hεe _ hlow

end StatFormal.Wave31tq.RouteG
