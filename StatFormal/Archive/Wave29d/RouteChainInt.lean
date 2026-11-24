import StatFormal.Archive.Wave29d.Statements
import StatFormal.Archive.Wave25a.RouteChainProb
import StatFormal.Lib.ChainInt.Basic
import StatFormal.Archive.RobustEquality.SemidualStrong.Proofs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Route — robust equality JASA `thm:cert-chain`, integral form `Γ_int` (untrusted)

`u = f* − f̂` sorted decreasingly by `σ`, chain sets `U_l`, gaps `s_l = u_(l) − u_(l+1) ≥ 0`, `f_t = f̂ + t u`.
`Gap = J(f*) − J(f̂) = g(1) − g(0)`, `g(t) = J(f_t)`, `g'(t) = ⟨∇J(f_t), u⟩ = Σ_l s_l G_t(U_l)` (Abel summation,
`Σ ∇J = 0`), `G_t(U) = w(U) − m^{f_t}_0(U) ≤ w(U) − m^{f̂}_{t s_l}(U)` (`lem:cert-odds`, pointwise and in mean), and for
`v = t s_l` in the cell `[s_g, s_{g+1})`: `m^{f̂}_v ≥ m^{f̂}_{s_g} ≥ m̲_g`, so `G_t(U_l) ≤ h_l(t s_l)` with the step
function `h_l = Σ_g (w(U_l) − m̲_g(U_l))_+ 𝟏_{cell g}`. Then `g(1) − g(0) ≤ ∫_0^1 Σ_l s_l h_l(t s_l) dt
= Σ_l ∫_0^{s_l} h_l ≤ Σ_l Ā(U_l) ≤ Γ_int` (`s_l ≤ s̄(U_l)`). Probability and `OT_ε` bounds as in the frozen
`chain_prob`, `chain_ot`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

namespace StatFormal.Wave29d

open StatFormal.RobustEquality.Semidual (gsoft)
open StatFormal.RobustEquality.SemidualStrong (OTdisc Jdual Setting)
open StatFormal.Wave15b (mOdds phiOdds piCond)
open StatFormal.Wave20a (clW clBar clD)
open StatFormal.Wave20b (confSet Predictable)
open StatFormal.Wave25a (chainSet osc sBar pext pext_lt sum_eq_range sum_chainSet mem_chainSet abel_zero
  Ioo_eq_Ico le_iSup_fin iInf_le_fin mOdds_mono properSets mem_properSets card_properSets)
open StatFormal.Foundations.ChainInt (stepH segL)

lemma int_phi {K : Type} [MeasurableSpace K] {r : ℕ} {ε : ℝ} (hε : 0 < ε) {w : Fin r → ℝ} (hw : ∀ i, 0 < w i)
    (hr : 0 < r) (f : Fin r → ℝ) {c : Fin r → K → ℝ} (hc : ∀ i, Measurable (c i)) (P : Measure K)
    [IsFiniteMeasure P] {U : Finset (Fin r)} (hU : U.Nonempty) (t : ℝ) :
    Integrable (fun y => phiOdds ε t (∑ i ∈ U, piCond ε w f c y i)) P :=
  StatFormal.Wave15b.integrable_of_unit (StatFormal.Wave15b.phi_meas (StatFormal.Wave15b.sumU_meas f hc U))
    (fun y => (StatFormal.Wave15b.phiOdds_mem (StatFormal.Wave15b.piCond_sumU_pos hw f c y hU)
      (StatFormal.Wave15b.piCond_sumU_le hε hw hr f c y U)).1)
    (fun y => (StatFormal.Wave15b.phiOdds_mem (StatFormal.Wave15b.piCond_sumU_pos hw f c y hU)
      (StatFormal.Wave15b.piCond_sumU_le hε hw hr f c y U)).2)

theorem certchain_int_gap : Claims.certchain_int_gap := by
  intro K _ r S ε w c P _ fs fh s mlow bX hset hmax hs0 _hsm hbX hlow
  obtain ⟨hε, hw, hw1, hcm, hcB⟩ := hset
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp at hw1
    · exact h
  set u : Fin r → ℝ := fun i => fs i - fh i with hu
  set σ : Equiv.Perm (Fin r) := Tuple.sort (fun i => -u i) with hσ
  have hmono : Monotone ((fun i => -u i) ∘ σ) := Tuple.monotone_sort _
  have hanti : ∀ j j' : Fin r, j ≤ j' → u (σ j') ≤ u (σ j) := fun j j' h => by
    have := hmono h; simp only [Function.comp] at this; linarith
  set B : ℕ → ℝ := pext σ u with hB
  set smax := bX + osc fh
  have hfoc := (StatFormal.RobustEquality.SemidualStrong.maximiser_foc K r ε w c P fs
    ⟨hε, hw, hw1, hcm, hcB⟩ hmax).2
  set sl : ℕ → ℝ := fun l => B (l - 1) - B l with hsl
  set cc : ℕ → Fin (S + 1) → ℝ := fun l g => max 0 (∑ i ∈ chainSet σ l, w i - mlow g (chainSet σ l)) with hcc
  have hcc0 : ∀ l g, 0 ≤ cc l g := fun l g => le_max_left _ _
  -- per-level facts
  have hlevel : ∀ l ∈ Ico 1 r, 0 ≤ sl l ∧ sl l ≤ sBar s mlow w smax (chainSet σ l) ∧
      (chainSet σ l).Nonempty ∧ chainSet σ l ≠ univ ∧
      ∀ i ∈ chainSet σ l, ∀ j ∉ chainSet σ l, sl l ≤ u i - u j := by
    intro l hl
    rw [mem_Ico] at hl
    have hl1 : l - 1 < r := by omega
    have hl2 : l < r := hl.2
    have hBl1 : B (l - 1) = u (σ ⟨l - 1, hl1⟩) := pext_lt σ u hl1
    have hBl : B l = u (σ ⟨l, hl2⟩) := pext_lt σ u hl2
    set U := chainSet σ l with hUdef
    have hUne : U.Nonempty := ⟨σ ⟨0, hr⟩, by rw [mem_chainSet]; simp; omega⟩
    have hUnu : U ≠ univ := fun h => by
      have : σ ⟨l, hl2⟩ ∈ U := h ▸ mem_univ _
      rw [mem_chainSet] at this; simp at this
    have hgap0 : 0 ≤ sl l := by
      simp only [hsl]
      rw [hBl1, hBl]; linarith [hanti ⟨l - 1, hl1⟩ ⟨l, hl2⟩ (by simp [Fin.le_def])]
    have hgap : ∀ i ∈ U, ∀ j ∉ U, sl l ≤ u i - u j := by
      intro i hi j hj
      rw [mem_chainSet] at hi hj
      have h1 : u (σ ⟨l - 1, hl1⟩) ≤ u i := by
        have := hanti (σ.symm i) ⟨l - 1, hl1⟩ (by simp [Fin.le_def]; omega)
        simpa using this
      have h2 : u j ≤ u (σ ⟨l, hl2⟩) := by
        have := hanti ⟨l, hl2⟩ (σ.symm j) (by simp [Fin.le_def]; omega)
        simpa using this
      simp only [hsl]
      rw [hBl1, hBl]; linarith
    refine ⟨hgap0, ?_, hUne, hUnu, hgap⟩
    -- `s_l ≤ s̄(U)`
    unfold sBar
    rw [Finset.le_fold_min]
    refine ⟨?_, fun g hg => ?_⟩
    · simp only [hsl]
      rw [hBl1, hBl]
      simp only [hu]
      have h1 := hfoc (σ ⟨l - 1, hl1⟩) (σ ⟨l, hl2⟩) bX (fun y => hbX _ _ y)
      have h2 := le_iSup_fin fh (σ ⟨l, hl2⟩)
      have h3 := iInf_le_fin fh (σ ⟨l - 1, hl1⟩)
      change _ ≤ bX + osc fh
      unfold osc; linarith
    · rw [mem_filter] at hg
      obtain ⟨-, hg1, hg2⟩ := hg
      by_contra hlt'
      have hlt := not_le.1 hlt'
      have hmo := mOdds_mono hε hw hr fh hcm P hUne hlt.le
      have hsU : sl l ≤ u (σ ⟨l - 1, hl1⟩) - u (σ ⟨l, hl2⟩) := by simp only [hsl]; rw [hBl1, hBl]
      have := hlow g U hUne hUnu
      -- `m_{s_l}(U) ≤ w(U)` from `cert_odds_mean` with gap `s_l`
      have hm1 := (StatFormal.Wave15b.cert_odds_mean K r ε w fs fh c P U (sl l)
        ⟨hε, hw, hw1, hcm, hcB⟩ hmax hUne hgap0 (fun i hi j hj => by
          have := hgap i hi j hj; simp only [hu] at this; linarith)).1
      linarith
  -- the line `f_t = f̂ + t u`
  set ft : ℝ → Fin r → ℝ := fun t => fh + t • u with hftdef
  have hft : ∀ t i, ft t i = fh i + t * u i := fun t i => rfl
  set gf : ℝ → ℝ := fun t => Jdual ε w c P (ft t) with hgf
  set D : ℝ → ℝ := fun t => ∑ i, StatFormal.Wave19b.gradJ ε w c P (ft t) i * u i with hD
  have hderiv : ∀ t, HasDerivAt gf (D t) t := by
    intro t
    have h1 := (StatFormal.Wave19b.cert_structure_ii_grad K r ε w c P (ft t) ⟨hε, hw, hw1, hcm, hcB⟩).1
    have h2 : HasDerivAt ft u t := by
      have := ((hasDerivAt_id t).smul_const u).const_add fh
      rw [one_smul] at this
      exact this
    have := h1.comp_hasDerivAt t h2
    have hDt : D t = (∑ i, StatFormal.Wave19b.gradJ ε w c P (ft t) i •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℝ) i) u := by
      simp only [hD, _root_.sum_apply, smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [hDt]
    exact this
  -- the derivative bound
  have hDle : ∀ t ∈ Set.Icc (0 : ℝ) 1, D t ≤ ∑ l ∈ Ico 1 r, sl l * stepH s (cc l) (sl l * t) := by
    intro t ⟨ht0, ht1⟩
    set G : Fin r → ℝ := fun i => StatFormal.Wave19b.gradJ ε w c P (ft t) i with hG
    have hsumG : ∑ j ∈ range r, pext σ G j = 0 := by
      rw [← sum_eq_range σ G]
      exact (StatFormal.Wave19b.cert_structure_ii_grad K r ε w c P (ft t) ⟨hε, hw, hw1, hcm, hcB⟩).2
    have habel : D t = ∑ l ∈ Ico 1 r, sl l * ∑ i ∈ chainSet σ l, G i := by
      change ∑ i, G i * u i = _
      rw [sum_eq_range σ (fun i => G i * u i)]
      have : ∀ j, pext σ (fun i => G i * u i) j = pext σ G j * B j := fun j => by
        simp only [pext, hB]; split_ifs <;> simp
      simp_rw [this]
      rw [abel_zero (pext σ G) B r hr hsumG]
      refine sum_congr rfl fun l hl => ?_
      rw [sum_chainSet σ G (by rw [mem_Ico] at hl; omega)]
    rw [habel]
    refine sum_le_sum fun l hl => mul_le_mul_of_nonneg_left ?_ (hlevel l hl).1
    obtain ⟨h0, -, hUne, hUnu, hgap⟩ := hlevel l hl
    set U := chainSet σ l with hU
    have hGU : ∑ i ∈ U, G i = ∑ i ∈ U, w i - mOdds ε 0 w (ft t) c P U :=
      (StatFormal.Wave15b.cert_odds_mean K r ε w fs (ft t) c P U 0 ⟨hε, hw, hw1, hcm, hcB⟩ hmax hUne le_rfl
        (fun i hi j hj => by
          rw [hft, hft]
          have h1 := hgap i hi j hj
          have h2 : 0 ≤ (1 - t) * (u i - u j) := mul_nonneg (by linarith) (by linarith)
          simp only [hu] at h1 h2 ⊢
          nlinarith)).2.1
    have hpt : mOdds ε (sl l * t) w fh c P U ≤ mOdds ε 0 w (ft t) c P U := by
      unfold mOdds
      refine integral_mono (int_phi hε hw hr fh hcm P hUne _) (int_phi hε hw hr (ft t) hcm P hUne _) fun y => ?_
      have := StatFormal.Wave15b.cert_odds_pointwise K r ε w (ft t) fh c U (sl l * t) y hε hw hUne
        (mul_nonneg h0 ht0) (fun i hi j hj => by
          rw [hft, hft]
          have h1 := hgap i hi j hj
          have h2 : sl l * t ≤ (u i - u j) * t := mul_le_mul_of_nonneg_right h1 ht0
          linarith)
      rw [StatFormal.Wave15b.phiOdds_zero (StatFormal.Wave15b.piCond_sumU_pos hw (ft t) c y hUne)]
      exact this
    obtain ⟨g0, hg0, hv⟩ := StatFormal.Foundations.ChainInt.exists_cell hs0 (mul_nonneg h0 ht0)
    have hmo := mOdds_mono hε hw hr fh hcm P hUne hg0
    have hl' := hlow g0 U hUne hUnu
    calc ∑ i ∈ U, G i ≤ cc l g0 := by
          rw [hGU]
          exact le_trans (by linarith) (le_max_right _ _)
      _ ≤ stepH s (cc l) (sl l * t) := StatFormal.Foundations.ChainInt.le_stepH (hcc0 l) hv
  -- the integral bound
  have hint : MeasureTheory.IntegrableOn (fun t => ∑ l ∈ Ico 1 r, sl l * stepH s (cc l) (sl l * t))
      (Set.Icc 0 1) :=
    integrable_finsetSum _ fun l _ =>
      (StatFormal.Foundations.ChainInt.integrableOn_stepH_comp (sl l) (by simp)).const_mul (sl l)
  have hFTC := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le zero_le_one
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt) (fun t _ => (hderiv t).hasDerivWithinAt) hint
    (fun t ht => hDle t (Set.Ioo_subset_Icc_self ht))
  have hI : ∫ t in (0 : ℝ)..1, ∑ l ∈ Ico 1 r, sl l * stepH s (cc l) (sl l * t) =
      ∑ l ∈ Ico 1 r, sl l * ∫ t in (0 : ℝ)..1, stepH s (cc l) (sl l * t) := by
    rw [intervalIntegral.integral_finsetSum (fun l _ =>
      (StatFormal.Foundations.ChainInt.intervalIntegrable_stepH_comp _ _ _).const_mul _)]
    simp_rw [intervalIntegral.integral_const_mul]
  have hsum : ∑ l ∈ Ico 1 r, sl l * ∫ t in (0 : ℝ)..1, stepH s (cc l) (sl l * t) ≤
      ∑ l ∈ Ico 1 r, aBar s mlow w smax (chainSet σ l) := by
    refine sum_le_sum fun l hl => ?_
    obtain ⟨h0, h1, -⟩ := hlevel l hl
    exact StatFormal.Foundations.ChainInt.mul_integral_stepH_comp_le (hcc0 l) h0 h1
  have hG : ∑ l ∈ Ico 1 r, aBar s mlow w smax (chainSet σ l) ≤ chainGammaInt s mlow w smax := by
    refine le_trans ?_ (le_sup' (fun σ' : Equiv.Perm (Fin r) => ∑ l ∈ Ioo 0 r,
      aBar s mlow w smax (chainSet σ' l)) (mem_univ σ))
    rw [Ioo_eq_Ico]
  have h1 : ft 1 = fs := by funext i; rw [hft]; simp [hu]
  have h0 : ft 0 = fh := by funext i; rw [hft]; simp
  have hJ : Jdual ε w c P fs - Jdual ε w c P fh ≤ chainGammaInt s mlow w smax := by
    have : gf 1 - gf 0 = Jdual ε w c P fs - Jdual ε w c P fh := by simp only [hgf, h1, h0]
    rw [← this]
    linarith
  obtain ⟨fs', hmax', hOT, -⟩ := StatFormal.RobustEquality.SemidualStrong.strong_duality K r ε w c P
    ⟨hε, hw, hw1, hcm, hcB⟩
  have hfs : Jdual ε w c P fs' = Jdual ε w c P fs := le_antisymm (hmax fs') (hmax' fs)
  rw [hOT, hfs, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  exact hJ

theorem certchain_int_prob : Claims.certchain_int_prob := by
  intro K Ω _ _ Pr _ r S ε w c P _ fs fh s mlow bX δ hset hmax hs0 hsm hbX hδ hfail
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
          · rw [← h]; simp only [Nat.cast_add, Nat.cast_one, sub_self, zero_mul, mul_zero]; exact hδ.le
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
  · refine certchain_int_gap K r S ε w c P fs fh s (mlow ω) bX hset hmax hs0 hsm hbX fun g U hU hU' => ?_
    by_contra hlt'
    have hlt := not_le.1 hlt'
    apply hω
    simp only [Fail, Set.mem_iUnion]
    exact ⟨g, mem_univ _, U, (mem_properSets U).2 ⟨hU, hU'⟩, hlt⟩

theorem certchain_int_ot : Claims.certchain_int_ot := by
  intro K Ω _ _ Pr _ d k r S m φ x a σ ε P _ fs fh s mlow bX δ δ' ub lb Yb bet hε ha ha1 hσ hφ hφb hmax hs0
    hsm hbX hδ hfail hYm hYi hYl hgb hlu hδ' hbm hpred hb09
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
  obtain ⟨E1, hE1m, hE1, hE1g⟩ :=
    certchain_int_prob K Ω Pr r S ε (clW σ a) cc P fs fh s mlow bX δ hset hmax hs0 hsm hbX hδ hfail
  have hgm : Measurable (gsoft ε (clW σ a) fh cc) := StatFormal.Wave25a.ChainOT.gsoft_meas ε _ fh hset.2.2.2.1
  obtain ⟨E2, hE2m, hE2, hE2g⟩ := StatFormal.Wave20b.cert_betting Ω K Pr P m Yb (gsoft ε (clW σ a) fh cc) ub lb δ'
    bet hYm hYi hYl hgm hgb hlu hδ' hbm hpred hb09
  refine ⟨E1 ∩ E2, hE1m.inter hE2m, ?_, fun ω hω b hb => ?_⟩
  · have h1 : 1 - δ ≤ Pr.real E1 := by
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
    have hgap := hE1g ω hω1
    have hbet := (hE2g ω hω2).2 b hb
    have hcoarse := StatFormal.Wave20a.cert_coarse K d k r φ x a σ ε P hε ha ha1 hσ hφ ⟨R, hR⟩
    have hJ : OTdisc ε (clW σ a) cc P ≤
        ((Jdual ε (clW σ a) cc P fh + chainGammaInt s (mlow ω) (clW σ a) (bX + osc fh) : ℝ) : EReal) := by
      rw [EReal.coe_add, add_comm]
      exact (EReal.sub_le_iff_le_add (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _))).1 hgap
    have hJ' : Jdual ε (clW σ a) cc P fh ≤ ∑ z, clW σ a z * fh z + (ub - (ub - lb) * b) := by
      unfold Jdual; linarith
    calc OTdisc ε a (fun i y => ‖x i - φ y‖ ^ 2) P
        ≤ OTdisc ε (clW σ a) cc P + ((clD σ a x : ℝ) : EReal) := hcoarse
      _ ≤ ((Jdual ε (clW σ a) cc P fh + chainGammaInt s (mlow ω) (clW σ a) (bX + osc fh) : ℝ) : EReal) +
            ((clD σ a x : ℝ) : EReal) := by gcongr
      _ ≤ _ := by
          rw [← EReal.coe_add, EReal.coe_le_coe_iff]
          linarith

end StatFormal.Wave29d
