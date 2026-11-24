import StatFormal.Archive.Wave25a.RouteChain
import StatFormal.Archive.Wave20a.RouteCoarse
import StatFormal.Archive.Wave20b.RouteCertBetting

/-!
# Route — robust equality JASA `thm:cert-chain`, probability and the `OT_ε` bound (untrusted)

Union bound over the `(2^r − 2)(S + 1)` lower confidence bounds, then `chain_gap` on the complement. The `OT_ε` bound:
`lem:cert-coarse` (frozen), `OT_ε(μ̄_r, P) ≤ J_P(f̂) + Γ` from `chain_gap`, `J_P(f̂) = ⟨w, f̂⟩ + E_P g_{f̂}` and the
betting bound `E_P g_{f̂} ≤ UCB_B` (frozen `lem:cert-betting`), on the intersection of the two events.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

namespace StatFormal.Wave25a

open StatFormal.RobustEquality.Semidual (gsoft)
open StatFormal.RobustEquality.SemidualStrong (OTdisc Jdual Setting)
open StatFormal.Wave15b (mOdds)
open StatFormal.Wave20a (clW clBar clD)
open StatFormal.Wave20b (confSet Predictable)

/-- The nonempty proper subsets of `Fin r`. -/
def properSets (r : ℕ) : Finset (Finset (Fin r)) := ((univ : Finset (Fin r)).powerset.erase ∅).erase univ

lemma mem_properSets {r : ℕ} (U : Finset (Fin r)) : U ∈ properSets r ↔ U.Nonempty ∧ U ≠ univ := by
  simp [properSets, Finset.nonempty_iff_ne_empty, and_comm]

lemma card_properSets {r : ℕ} (hr : 0 < r) : ((properSets r).card : ℝ) = 2 ^ r - 2 := by
  have hne : (univ : Finset (Fin r)) ≠ ∅ := by
    rw [← Finset.nonempty_iff_ne_empty]; exact ⟨⟨0, hr⟩, mem_univ _⟩
  have h1 : univ ∈ (univ : Finset (Fin r)).powerset.erase ∅ := by simp [hne]
  have h2 : (∅ : Finset (Fin r)) ∈ (univ : Finset (Fin r)).powerset := by simp
  have hc : (properSets r).card = 2 ^ r - 1 - 1 := by
    rw [properSets, card_erase_of_mem h1, card_erase_of_mem h2, card_powerset, card_univ, Fintype.card_fin]
  have h2r : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  rw [hc]
  have : 2 ^ r - 1 - 1 = 2 ^ r - 2 := by omega
  rw [this, Nat.cast_sub h2r]
  push_cast; ring

theorem chain_prob : Claims.chain_prob := by
  intro K Ω _ _ Pr _ r S ε w c P _ fs fh s mlow bX δ hset hmax hs0 hbX hδ hfail
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; obtain ⟨-, -, h1, -⟩ := hset; simp at h1
    · exact h
  set q := δ / ((2 ^ r - 2) * (S + 1))
  set Fail : Set Ω := ⋃ g ∈ (univ : Finset (Fin (S + 1))), ⋃ U ∈ properSets r,
    {ω | mOdds ε (s g) w fh c P U < mlow ω g U}
  have hFm : MeasurableSet Fail := by
    refine Finset.measurableSet_biUnion _ fun g _ => Finset.measurableSet_biUnion _ fun U hU => ?_
    rw [mem_properSets] at hU
    exact (hfail g U hU.1 hU.2).1
  have hFle : Pr Fail ≤ ENNReal.ofReal δ := by
    calc Pr Fail ≤ ∑ g ∈ (univ : Finset (Fin (S + 1))), Pr (⋃ U ∈ properSets r,
          {ω | mOdds ε (s g) w fh c P U < mlow ω g U}) := measure_biUnion_finset_le _ _
      _ ≤ ∑ g ∈ (univ : Finset (Fin (S + 1))), ∑ U ∈ properSets r,
          Pr {ω | mOdds ε (s g) w fh c P U < mlow ω g U} :=
          sum_le_sum fun g _ => measure_biUnion_finset_le _ _
      _ ≤ ∑ g ∈ (univ : Finset (Fin (S + 1))), ∑ U ∈ properSets r, ENNReal.ofReal q :=
          sum_le_sum fun g _ => sum_le_sum fun U hU => by
            rw [mem_properSets] at hU; exact (hfail g U hU.1 hU.2).2
      _ = ENNReal.ofReal (((S + 1 : ℕ) : ℝ) * ((properSets r).card * q)) := by
          rw [sum_const, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal δ := by
          apply ENNReal.ofReal_le_ofReal
          rw [card_properSets hr]
          rcases eq_or_lt_of_le (show (2 : ℝ) ≤ 2 ^ r from by
              calc (2 : ℝ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr) with h | h
          · rw [← h]; simp; exact hδ.le
          · have hpos : 0 < ((2 : ℝ) ^ r - 2) * (S + 1) := by
              have : (0 : ℝ) < S + 1 := by positivity
              nlinarith
            have : ((S + 1 : ℕ) : ℝ) * ((2 ^ r - 2) * q) = δ := by
              simp only [q]; push_cast; field_simp
            rw [this]
  refine ⟨Failᶜ, hFm.compl, ?_, fun ω hω => ?_⟩
  · rw [prob_compl_eq_one_sub hFm]
    calc ENNReal.ofReal (1 - δ) = 1 - ENNReal.ofReal δ := by
          rw [ENNReal.ofReal_sub _ hδ.le, ENNReal.ofReal_one]
      _ ≤ 1 - Pr Fail := tsub_le_tsub_left hFle _
  · refine chain_gap K r S ε w c P fs fh s (mlow ω) bX hset hmax hs0 hbX fun g U hU hU' => ?_
    by_contra hlt'
    have hlt := not_le.1 hlt'
    apply hω
    simp only [Fail, Set.mem_iUnion]
    exact ⟨g, mem_univ _, U, (mem_properSets U).2 ⟨hU, hU'⟩, hlt⟩

namespace ChainOT

lemma gsoft_meas {K : Type*} [MeasurableSpace K] {r : ℕ} (ε : ℝ) (w f : Fin r → ℝ) {c : Fin r → K → ℝ}
    (hc : ∀ i, Measurable (c i)) : Measurable (gsoft ε w f c) := by
  unfold gsoft
  exact (Real.measurable_log.comp (Finset.measurable_sum _ fun l _ =>
    ((((measurable_const.sub (hc l)).div_const ε)).exp).const_mul (w l))).const_mul (-ε)

end ChainOT

theorem chain_ot : Claims.chain_ot := by
  intro K Ω _ _ Pr _ d k r S m φ x a σ ε P _ fs fh s mlow bX δ δ' ub lb Yb bet hε ha ha1 hσ hφ hφb hmax hs0
    hbX hδ hfail hYm hYi hYl hgb hlu hδ' hbm hpred hb09
  obtain ⟨R, hR⟩ := hφb
  set cc : Fin r → K → ℝ := fun z y => ‖clBar σ a x z - φ y‖ ^ 2 with hcc
  have hset : Setting ε (clW σ a) cc := by
    refine ⟨hε, fun z => StatFormal.Wave20a.clW_pos ha hσ z, by rw [StatFormal.Wave20a.clW_sum, ha1],
      fun z => ((measurable_const.sub hφ).norm.pow_const 2), ⟨(∑ z, ‖clBar σ a x z‖ + R) ^ 2, fun z y => ?_⟩⟩
    have h1 : ‖clBar σ a x z - φ y‖ ≤ ∑ z, ‖clBar σ a x z‖ + R :=
      (norm_sub_le _ _).trans (add_le_add (Finset.single_le_sum (f := fun z => ‖clBar σ a x z‖)
        (fun z _ => norm_nonneg _) (mem_univ z)) (hR y))
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  obtain ⟨E1, hE1m, hE1, hE1g⟩ := chain_prob K Ω Pr r S ε (clW σ a) cc P fs fh s mlow bX δ hset hmax hs0 hbX hδ hfail
  have hgm : Measurable (gsoft ε (clW σ a) fh cc) := ChainOT.gsoft_meas ε _ fh hset.2.2.2.1
  obtain ⟨E2, hE2m, hE2, hE2g⟩ := StatFormal.Wave20b.cert_betting Ω K Pr P m Yb (gsoft ε (clW σ a) fh cc) ub lb δ'
    bet hYm hYi hYl hgm hgb hlu hδ' hbm hpred hb09
  refine ⟨E1 ∩ E2, hE1m.inter hE2m, ?_, fun ω hω b hb => ?_⟩
  · -- `P(E1 ∩ E2) ≥ 1 − δ − δ'`
    have h1 : 1 - δ ≤ Pr.real E1 := by
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hE1
    have h2 : 1 - δ' ≤ Pr.real E2 := by
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hE2
    have h3 : Pr.real (E1 ∩ E2) + Pr.real (E1 ∪ E2) = Pr.real E1 + Pr.real E2 := by
      rw [add_comm]; exact measureReal_union_add_inter hE2m
    have h4 : Pr.real (E1 ∪ E2) ≤ 1 := measureReal_le_one
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    change 1 - δ - δ' ≤ Pr.real (E1 ∩ E2)
    linarith
  · obtain ⟨hω1, hω2⟩ := hω
    have hgap := (hE1g ω hω1).1
    have hbet := (hE2g ω hω2).2 b hb
    have hcoarse := StatFormal.Wave20a.cert_coarse K d k r φ x a σ ε P hε ha ha1 hσ hφ ⟨R, hR⟩
    -- `OT_ε(μ̄_r, P) ≤ J_P(f̂) + Γ`
    have hJ : OTdisc ε (clW σ a) cc P ≤ ((Jdual ε (clW σ a) cc P fh + chainGamma s (mlow ω) (clW σ a) (bX + osc fh) : ℝ) : EReal) := by
      rw [EReal.coe_add, add_comm]
      exact (EReal.sub_le_iff_le_add (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _))).1 hgap
    have hJ' : Jdual ε (clW σ a) cc P fh ≤ ∑ z, clW σ a z * fh z + (ub - (ub - lb) * b) := by
      unfold Jdual; linarith
    calc OTdisc ε a (fun i y => ‖x i - φ y‖ ^ 2) P
        ≤ OTdisc ε (clW σ a) cc P + ((clD σ a x : ℝ) : EReal) := hcoarse
      _ ≤ ((Jdual ε (clW σ a) cc P fh + chainGamma s (mlow ω) (clW σ a) (bX + osc fh) : ℝ) : EReal) +
            ((clD σ a x : ℝ) : EReal) := by gcongr
      _ ≤ _ := by
          rw [← EReal.coe_add, EReal.coe_le_coe_iff]
          linarith

end StatFormal.Wave25a
