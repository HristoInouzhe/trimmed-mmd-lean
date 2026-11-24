import StatFormal.Archive.Wave11a.Statements
import StatFormal.Lib.Tax.Tax
import StatFormal.Archive.RobustEquality.Tax.Proofs
import StatFormal.Archive.RobustEquality.SemidualStrong.Proofs
import StatFormal.Archive.RobustEquality.Semidual.Proofs
import TauCeti.MeasureTheory.OptimalTransport.Existence.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Wave 11a route: robust equality JASA `prop:cs-compose` (composition at the free end)

Untrusted proof file. A **dual** route (no gluing, no data processing): with `s = 1 + t`, the inequality
`|x_i − z|² ≤ (1+t)|x_i − y|² + (1 + 1/t)|y − z|²` gives, for every potential `f`,
`g^c_f(z) ≤ g^{s c}_f(y) + (1 + 1/t)|y − z|²`; integrating along an optimal `W₂` coupling `pl ∈ Π(P,Q)`,
`J^c_Q(f) ≤ J^{sc}_P(f) + (1 + 1/t) W₂²(P,Q)`. Weak duality for the cost `s c` at the coupling `γ_P` optimal for
`OT_ε(μ,P)` gives `J^{sc}_P(f) ≤ s E_{γ_P} c + ε KL(γ_P) ≤ s OT_ε(μ,P)`. At the dual optimiser for `Q`,
`OT_ε(μ,Q) ≤ (1+t) OT_ε(μ,P) + (1 + 1/t) W₂²` for every `t > 0`, and `inf_t = (√OT_ε(μ,P) + W₂)²`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Real TauCeti Filter Topology
open scoped ENNReal

namespace StatFormal.Wave11a

open StatFormal.RobustEquality StatFormal.RobustEquality.Tax StatFormal.RobustEquality.SemidualStrong
  StatFormal.RobustEquality.Semidual

/-- `inf_{t>0} (1+t)A + (1 + 1/t)V = (√A + √V)²`. -/
lemma opt_bound {X A V : ℝ} (hA : 0 ≤ A) (hV : 0 ≤ V) (h : ∀ t > 0, X ≤ (1 + t) * A + (1 + 1 / t) * V) :
    X ≤ (√A + √V) ^ 2 := by
  have hδ : ∀ δ > 0, X ≤ (√(A + δ) + √(V + δ)) ^ 2 := by
    intro δ hδ
    set p := √(A + δ) with hp
    set q := √(V + δ) with hq
    have hp0 : 0 < p := Real.sqrt_pos.2 (by linarith)
    have hq0 : 0 < q := Real.sqrt_pos.2 (by linarith)
    have hp2 : p ^ 2 = A + δ := Real.sq_sqrt (by linarith)
    have hq2 : q ^ 2 = V + δ := Real.sq_sqrt (by linarith)
    have ht : 0 < q / p := div_pos hq0 hp0
    have h1 := h (q / p) ht
    have h2 : (1 + q / p) * A + (1 + 1 / (q / p)) * V ≤ (1 + q / p) * (A + δ) + (1 + 1 / (q / p)) * (V + δ) := by
      have : 0 < 1 + 1 / (q / p) := by positivity
      nlinarith
    have h3 : (1 + q / p) * (A + δ) + (1 + 1 / (q / p)) * (V + δ) = (p + q) ^ 2 := by
      rw [← hp2, ← hq2]
      field_simp
      ring
    linarith
  have hcont : Continuous fun δ : ℝ => (√(A + δ) + √(V + δ)) ^ 2 :=
    (((continuous_const.add continuous_id).sqrt).add ((continuous_const.add continuous_id).sqrt)).pow 2
  have hlim : Tendsto (fun δ : ℝ => (√(A + δ) + √(V + δ)) ^ 2) (𝓝[>] 0) (𝓝 ((√A + √V) ^ 2)) := by
    have := hcont.tendsto 0
    simp only [add_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ' => hδ δ hδ')

section Metric

variable {K : Type} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

lemma integrable_of_continuous' {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {g : X → ℝ} (hg : Continuous g) :
    Integrable g μ :=
  (BoundedContinuousFunction.mkOfCompact ⟨g, hg⟩).integrable μ

lemma continuous_gsoft {k : ℕ} {ε : ℝ} {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) (hk : 0 < k) (f : Fin k → ℝ)
    {c : Fin k → K → ℝ} (hc : ∀ i, Continuous (c i)) : Continuous (gsoft ε a f c) := by
  unfold gsoft
  refine continuous_const.mul (Continuous.log ?_ fun y => ?_)
  · exact continuous_finset_sum _ fun i _ => continuous_const.mul
      (((continuous_const.sub (hc i)).div_const ε).rexp)
  · refine (Finset.sum_pos (fun i _ => mul_pos (ha i) (Real.exp_pos _)) ⟨⟨0, hk⟩, Finset.mem_univ _⟩).ne'

/-- The shifted soft-min bound `g^c_f(z) ≤ g^{(1+t)c}_f(y) + (1 + 1/t)|y − z|²`. -/
lemma gsoft_shift {k : ℕ} {ε : ℝ} (hε : 0 < ε) {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) (hk : 0 < k)
    (f : Fin k → ℝ) (x : Fin k → K) {t : ℝ} (ht : 0 < t) (y z : K) :
    gsoft ε a f (fun i w => dist (x i) w ^ 2) z ≤
      gsoft ε a f (fun i w => (1 + t) * dist (x i) w ^ 2) y + (1 + 1 / t) * dist y z ^ 2 := by
  unfold gsoft
  set R := (1 + 1 / t) * dist y z ^ 2 with hR
  have hterm : ∀ i, a i * Real.exp ((f i - (1 + t) * dist (x i) y ^ 2) / ε) * Real.exp (-R / ε) ≤
      a i * Real.exp ((f i - dist (x i) z ^ 2) / ε) := by
    intro i
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (ha i).le
    rw [← add_div, div_le_div_iff_of_pos_right hε]
    have htri := dist_triangle (x i) y z
    set d := dist (x i) y
    set e := dist y z
    have hd : 0 ≤ d := dist_nonneg
    have he : 0 ≤ e := dist_nonneg
    have hz : dist (x i) z ^ 2 ≤ (d + e) ^ 2 := pow_le_pow_left₀ dist_nonneg htri 2
    have hy : 0 ≤ (t * d - e) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
    have hy' : (t * d - e) ^ 2 / t = t * d ^ 2 - 2 * d * e + e ^ 2 / t := by field_simp; ring
    have hR' : R = e ^ 2 + e ^ 2 / t := by rw [hR]; field_simp
    nlinarith
  have hS' : 0 < ∑ i, a i * Real.exp ((f i - (1 + t) * dist (x i) y ^ 2) / ε) :=
    Finset.sum_pos (fun i _ => mul_pos (ha i) (Real.exp_pos _)) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hsum : (∑ i, a i * Real.exp ((f i - (1 + t) * dist (x i) y ^ 2) / ε)) * Real.exp (-R / ε) ≤
      ∑ i, a i * Real.exp ((f i - dist (x i) z ^ 2) / ε) := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum fun i _ => hterm i
  have hlog := Real.log_le_log (mul_pos hS' (Real.exp_pos _)) hsum
  rw [Real.log_mul hS'.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have := mul_le_mul_of_nonneg_left hlog hε.le
  rw [mul_add, mul_div_cancel₀ _ hε.ne'] at this
  linarith

lemma W2_ne_top (P Q : Measure K) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    wassersteinEDist 2 P Q ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := Metric.diam (univ : Set K)))
    ((wassersteinEDist_le (isCoupling_prod P Q) 2).trans ?_)
  refine (eLpNorm_le_of_ae_enorm_bound (C := ENNReal.ofReal (Metric.diam (univ : Set K)))
    (continuous_edist.measurable.aestronglyMeasurable) (Eventually.of_forall fun z => ?_)).trans ?_
  · rw [enorm_eq_self, edist_dist]
    exact ENNReal.ofReal_le_ofReal
      (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _))
  · simp

/-- An optimal `W₂` coupling and its real transport integral. -/
lemma exists_W2_coupling (P Q : Measure K) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ∃ pl : Measure (K × K), IsCoupling pl P Q ∧ IsProbabilityMeasure pl ∧
      ∫ z, dist z.1 z.2 ^ 2 ∂pl = (wassersteinEDist 2 P Q).toReal ^ 2 := by
  obtain ⟨pl, hplopt⟩ := exists_isOptimalCoupling_edist_rpow P Q 2
  have hpl : IsCoupling pl P Q := hplopt.toIsCoupling
  have hprob : IsProbabilityMeasure pl := ⟨by rw [← Measure.fst_univ, hpl.fst_eq, measure_univ]⟩
  refine ⟨pl, hpl, hprob, ?_⟩
  have hlin : ∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂pl = wassersteinEDist 2 P Q ^ (2 : ℝ) := by
    rw [hplopt.lintegral_eq]
    have := wassersteinEDist_rpow_eq_transportCost (p := 2) (X := K) measurable_edist two_ne_zero
      ENNReal.ofNat_ne_top P Q
    simp only [ENNReal.toReal_ofNat] at this
    rw [this]
  have hcont : Continuous fun z : K × K => dist z.1 z.2 ^ 2 := (continuous_fst.dist continuous_snd).pow 2
  have hint := integrable_of_continuous' pl hcont
  have hof : ENNReal.ofReal (∫ z, dist z.1 z.2 ^ 2 ∂pl) = wassersteinEDist 2 P Q ^ (2 : ℝ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z => sq_nonneg _), ← hlin]
    refine lintegral_congr fun z => ?_
    rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num), Real.rpow_two]
  have h2 := congrArg ENNReal.toReal hof
  rw [ENNReal.toReal_ofReal (integral_nonneg fun z => sq_nonneg _), ← ENNReal.toReal_rpow,
    Real.rpow_two] at h2
  exact h2

end Metric

theorem cs_compose : Claims.cs_compose := by
  intro K _ _ _ _ k ε a x P Q _ _ hε ha hsum
  have hk : 0 < k := StatFormal.Foundations.SemiDiscrete.pos_of_sum_eq_one hsum
  haveI hμ := StatFormal.Foundations.SemiDiscrete.isProb_muDisc ha hsum
  set c : Fin k → K → ℝ := fun i y => dist (x i) y ^ 2 with hcdef
  have hccont : ∀ i, Continuous (c i) := fun i => (continuous_const.dist continuous_id).pow 2
  obtain ⟨D, hD⟩ : ∃ D, ∀ i y, |c i y| ≤ D := by
    refine ⟨Metric.diam (univ : Set K) ^ 2, fun i y => ?_⟩
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ dist_nonneg
      (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)) 2
  have hs : Setting ε a c := ⟨hε, ha, hsum, fun i => (hccont i).measurable, D, hD⟩
  -- the optimal coupling at `P` and the value `A`
  obtain ⟨fP, -, hOTP, γP, hγP, hfstP, hsndP, hvalP⟩ := strong_duality K k ε a c P hs
  haveI := hγP
  set A := Jdual ε a c P fP with hAdef
  set I := ∫ z, c z.1 z.2 ∂γP with hIdef
  have hkl_ne_top : klRef γP ((muDisc a).prod P) ≠ ⊤ := by
    intro h
    rw [hOTP, h, EReal.coe_mul_top_of_pos hε, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at hvalP
    exact EReal.coe_ne_top _ hvalP.symm
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, klRef γP ((muDisc a).prod P) = κ :=
    ⟨_, (EReal.coe_toReal hkl_ne_top (StatFormal.Foundations.Tax.klRef_ne_bot _ _)).symm⟩
  have hκ0 : 0 ≤ κ := by
    have := StatFormal.Foundations.Tax.klRef_nonneg_of_prob γP ((muDisc a).prod P)
    rw [hκ] at this; exact_mod_cast this
  have hAeq : A = I + ε * κ := by
    rw [hOTP, hκ] at hvalP
    norm_cast at hvalP
    linarith
  have hI0 : 0 ≤ I := integral_nonneg fun z => sq_nonneg _
  have hA0 : 0 ≤ A := by rw [hAeq]; positivity
  -- the dual optimiser at `Q`
  obtain ⟨fQ, -, hOTQ, -⟩ := strong_duality K k ε a c Q hs
  -- the `W₂` coupling
  obtain ⟨pl, hpl, hplprob, hplval⟩ := exists_W2_coupling P Q
  set W := (wassersteinEDist 2 P Q).toReal with hWdef
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  -- the key bound for every `t > 0`
  have hkey : ∀ t > 0, Jdual ε a c Q fQ ≤ (1 + t) * A + (1 + 1 / t) * W ^ 2 := by
    intro t ht
    set c' : Fin k → K → ℝ := fun i y => (1 + t) * dist (x i) y ^ 2 with hc'def
    have hc'cont : ∀ i, Continuous (c' i) := fun i => continuous_const.mul (hccont i)
    have hgc := continuous_gsoft (ε := ε) ha hk fQ hccont
    have hgc' := continuous_gsoft (ε := ε) ha hk fQ hc'cont
    have hQint : ∫ y, gsoft ε a fQ c y ∂Q = ∫ z, gsoft ε a fQ c z.2 ∂pl := by
      rw [← hpl.snd_eq, Measure.snd, integral_map measurable_snd.aemeasurable hgc.aestronglyMeasurable]
    have hPint : ∫ y, gsoft ε a fQ c' y ∂P = ∫ z, gsoft ε a fQ c' z.1 ∂pl := by
      rw [← hpl.fst_eq, Measure.fst, integral_map measurable_fst.aemeasurable hgc'.aestronglyMeasurable]
    have hshift : ∫ z, gsoft ε a fQ c z.2 ∂pl ≤
        ∫ z, (gsoft ε a fQ c' z.1 + (1 + 1 / t) * dist z.1 z.2 ^ 2) ∂pl :=
      integral_mono (integrable_of_continuous' pl (hgc.comp continuous_snd))
        (integrable_of_continuous' pl ((hgc'.comp continuous_fst).add
          (continuous_const.mul ((continuous_fst.dist continuous_snd).pow 2))))
        fun z => gsoft_shift hε ha hk fQ x ht z.1 z.2
    have hi1 : Integrable (fun z : K × K => gsoft ε a fQ c' z.1) pl :=
      integrable_of_continuous' pl (hgc'.comp continuous_fst)
    have hi2 : Integrable (fun z : K × K => (1 + 1 / t) * dist z.1 z.2 ^ 2) pl :=
      integrable_of_continuous' pl (continuous_const.mul ((continuous_fst.dist continuous_snd).pow 2))
    rw [integral_add hi1 hi2,
      integral_const_mul, hplval] at hshift
    -- weak duality for the cost `(1+t) c` at `γ_P`
    have hweak := StatFormal.RobustEquality.Semidual.semidual_weak K k a fQ c' P γP ε hε ha hsum
      (fun i => (hc'cont i).measurable) ⟨(1 + t) * D, fun i y => by
        rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + t)]
        exact mul_le_mul_of_nonneg_left (hD i y) (by linarith)⟩ hfstP hsndP
    have hI' : ∫ z, c' z.1 z.2 ∂γP = (1 + t) * I := by
      rw [hIdef, ← integral_const_mul]
    rw [hI', hκ] at hweak
    norm_cast at hweak
    have hJ'le : Jdual ε a c' P fQ ≤ (1 + t) * A := by
      unfold Jdual
      rw [hAeq]
      nlinarith [mul_nonneg ht.le (mul_nonneg hε.le hκ0)]
    unfold Jdual at hJ'le ⊢
    rw [hQint]
    rw [← hPint] at hshift
    linarith
  have hbound := opt_bound hA0 (sq_nonneg W) hkey
  rw [Real.sqrt_sq hW0] at hbound
  have hOTPr : (OTdisc ε a c P).toReal = A := by rw [hOTP, EReal.toReal_coe]
  refine ⟨?_, ?_, W2_ne_top P Q, ?_⟩
  · rw [hOTP]; exact_mod_cast hA0
  · rw [hOTP]; exact EReal.coe_ne_top _
  · rw [hOTQ, hOTPr]
    exact EReal.coe_le_coe_iff.2 hbound

theorem cs_compose_ball : Claims.cs_compose_ball := by
  intro K _ _ _ _ k ε a x P Q _ _ ρ β hε ha hsum hρ hβ hOT hW
  obtain ⟨h0, htop, hWtop, hmain⟩ := cs_compose K k ε a x P Q hε ha hsum
  set c : Fin k → K → ℝ := fun i y => dist (x i) y ^ 2
  obtain ⟨D, hD⟩ : ∃ D, ∀ i y, |c i y| ≤ D := by
    refine ⟨Metric.diam (univ : Set K) ^ 2, fun i y => ?_⟩
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ dist_nonneg
      (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)) 2
  have hs : Setting ε a c := ⟨hε, ha, hsum, fun i => ((continuous_const.dist continuous_id).pow 2).measurable, D, hD⟩
  -- real bounds on the two pieces
  have hA : (OTdisc ε a c P).toReal ≤ ρ := by
    have hbot : OTdisc ε a c P ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) h0
    rw [← EReal.coe_toReal htop hbot] at hOT
    exact EReal.coe_le_coe_iff.1 hOT
  have hWr : (wassersteinEDist 2 P Q).toReal ≤ √β := by
    refine Real.le_sqrt_of_sq_le ?_
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hW
    rwa [ENNReal.toReal_pow, ENNReal.toReal_ofReal hβ] at this
  have hA0 : 0 ≤ (OTdisc ε a c P).toReal := EReal.toReal_nonneg h0
  have hle : (√((OTdisc ε a c P).toReal) + (wassersteinEDist 2 P Q).toReal) ^ 2 ≤ (√ρ + √β) ^ 2 := by
    have : √((OTdisc ε a c P).toReal) ≤ √ρ := Real.sqrt_le_sqrt hA
    have h1 : 0 ≤ √((OTdisc ε a c P).toReal) + (wassersteinEDist 2 P Q).toReal := by positivity
    exact pow_le_pow_left₀ h1 (by linarith) 2
  refine ⟨inferInstance, Q, (show Q ∈ freeClass from (inferInstance : IsProbabilityMeasure Q)), ?_⟩
  rw [StatFormal.RobustEquality.Tax.tax_identity K k ε a c Q Q hs, StatFormal.Foundations.Tax.klRef_self Q,
    mul_zero, add_zero]
  exact hmain.trans (EReal.coe_le_coe_iff.2 hle)

example : Claims.cs_compose := cs_compose
example : Claims.cs_compose_ball := cs_compose_ball

end StatFormal.Wave11a
