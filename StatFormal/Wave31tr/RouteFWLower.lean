import StatFormal.Wave30tz.RouteLower
import StatFormal.Wave31tr.RouteFWFit

/-!
# Wave 31tr, chunk M3: T20 (a) `lo_lower_bound_fw` — Proposition 4.4's explicit lower bound for Frank–Wolfe runs (untrusted)

Copy-adapted from the certified `Wave30tz` route `RouteLower.lean` (`witness_step`, `bet_step`, `core_lower_bound`,
`lo_lower_bound_route`). The exact minimizer enters there only through Lemma 4 (`fitted_ramp_route`) in `witness_step`; here
T19 (`fitted_ramp_fw_route`) takes its place, with `D′ = (1 − ρ/2)D_{α_j} ≥ d` (`d ≤ (1 − ρ/2)D_{α_i}` and
`α ↦ D_α` nonincreasing, the certified `Wave30tz.Lower.dpop_antitone`), so `Θ((1 − ρ/2)D_{α_j}) ≥ Θ(α_i, d) ≥ d/2`
(`theta_mono_route`) and the excess is `≥ ϱ_* = d/(2β_*D_φ)`. The fitting event, its probability (`fitEvent_compl_le`),
Lemma 5 (`bet_power_route`, `bet_arith`) and the union over the levels `j ≤ i` are reused unchanged; `D_φ > 0` follows from
`D_{α_i} > 0`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr.RouteFW

open StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30ty StatFormal.Wave30tp
open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
open StatFormal.Wave30tz.Lower StatFormal.Wave30tz.Bet
open scoped StatFormal.Wave30tz.Bet

section Step

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable [CompleteSpace H]

/-- (copy-adapted from the certified `Wave30tz.Lower.witness_step`) On `{Z ≤ τ_*, Z⁻ ≤ τ_*}`, at a level `α_j ≤ α_i` with
`(1 − ρ/2)D_{α_j} ≥ d` and (S): a Frank–Wolfe witness rule of gap `ρ` bets and the ramp has excess
`E_P g − E_Q g − α_j ≥ ϱ_* = d/(2β_* D_φ)` (T19 in place of Lemma 4). -/
theorem witness_step_fw (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ Dφ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) (hDφ0 : 0 < Dφ)
    {n' m' : ℕ} (hn : 1 ≤ n') (hm : 1 ≤ m') (xs : Fin n' → 𝒳) (ys : Fin m' → 𝒳)
    {αj αi d r ρ : ℝ} (hαj0 : 0 ≤ αj) (hji : αj ≤ αi) (hαi1 : αi < 1) (hd : 0 < d) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdD : d ≤ (1 - ρ / 2) * Dpop φ P Q αj)
    (hr : 1 / (n' : ℝ) + 1 / (m' : ℝ) ≤ r) (hS1 : beta αi * Dφ * r ≤ d / 8)
    (hS2 : beta αi ^ 2 * κ ^ 2 * r ≤ 7 * d ^ 2 / 64)
    (hZ : hingeZ P Q φ hingePos hingePos 1 κ κ (xs, ys) ≤ d / (8 * beta αi))
    (hZm : hingeZm P Q φ hingePos hingePos 1 κ κ (xs, ys) ≤ d / (8 * beta αi))
    {has : Prop} {g : 𝒳 → ℝ} (hW : IsWitnessRampFW φ αj ρ xs ys has g) :
    has ∧ αj + d / (2 * beta αi * Dφ) ≤ (∫ z, g z ∂P) - ∫ z, g z ∂Q := by
  obtain ⟨-, hW2⟩ := hW
  obtain ⟨w, v, hfw, -, hpos⟩ := hW2 hn hm
  set β := beta αi with hβdef
  set Z := hingeZ P Q φ hingePos hingePos 1 κ κ (xs, ys) with hZdef
  set Zm := hingeZm P Q φ hingePos hingePos 1 κ κ (xs, ys) with hZmdef
  have hαj1 : αj < 1 := hji.trans_lt hαi1
  have hβ1 : 1 ≤ β := Wave30tz.one_le_beta (hαj0.trans hji) hαi1
  have hβj1 : 1 ≤ beta αj := Wave30tz.one_le_beta hαj0 hαj1
  have hβj : beta αj ≤ β := by
    rw [hβdef]; unfold beta; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hZ0 : 0 ≤ Z := hingeZ_nonneg P Q hκ _
  have hZm0 : 0 ≤ Zm := hingeZm_nonneg' P Q hκ _
  have hβτ : β * (d / (8 * β)) = d / 8 := by field_simp
  have hβZm : β * Zm ≤ d / 8 := by
    calc β * Zm ≤ β * (d / (8 * β)) := mul_le_mul_of_nonneg_left hZm (by linarith)
      _ = d / 8 := hβτ
  have hβZ : β * Z ≤ d / 8 := by
    calc β * Z ≤ β * (d / (8 * β)) := mul_le_mul_of_nonneg_left hZ (by linarith)
      _ = d / 8 := hβτ
  have hβjZm : beta αj * Zm < (1 - ρ / 2) * Dpop φ P Q αj := by
    have : beta αj * Zm ≤ β * Zm := mul_le_mul_of_nonneg_right hβj hZm0
    linarith
  obtain ⟨-, hqpos, hcuts⟩ :=
    fitted_ramp_fw_route 𝒳 H P Q φ κ Dφ αj ρ n' m' xs ys w v hφ hκ hDφ hαj0 hαj1 hn hm hρ0 hρ1 hfw hβjZm
  obtain ⟨t, u, hC, hiff, hg⟩ := hpos hqpos
  obtain ⟨-, -, -, hΘpos⟩ := hcuts t u hC
  set s : ℝ := 1 / (n' : ℝ) + 1 / (m' : ℝ) with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hmono := theta_mono_route αj αi d ((1 - ρ / 2) * Dpop φ P Q αj) Z Zm κ Dφ s hαj0 hji hαi1 hZ0 hZm0 hDφ0.le hs0
    (by linarith) hdD
  -- `Θ(α_i, d) ≥ d/2`
  have hΘi : d / 2 ≤ fitTheta αi d Z Zm κ Dφ s := by
    unfold fitTheta
    have h1 : β * Dφ * s ≤ d / 8 := by
      have : β * Dφ * s ≤ β * Dφ * r := mul_le_mul_of_nonneg_left hr (by positivity)
      linarith
    have hden : 7 * d / 8 ≤ d - β * Zm := by linarith
    have hden0 : 0 < d - β * Zm := by linarith
    have h2 : β ^ 2 * κ ^ 2 * s / (d - β * Zm) ≤ d / 8 := by
      rw [div_le_iff₀ hden0]
      have : β ^ 2 * κ ^ 2 * s ≤ β ^ 2 * κ ^ 2 * r := mul_le_mul_of_nonneg_left hr (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hden (by linarith : (0 : ℝ) ≤ d / 8)]
    have h3 : β * (Z + Zm) ≤ d / 4 := by rw [mul_add]; linarith
    linarith
  set Θ := fitTheta αj ((1 - ρ / 2) * Dpop φ P Q αj) Z Zm κ Dφ s with hΘdef
  have hΘ : d / 2 ≤ Θ := hΘi.trans hmono
  obtain ⟨hut, hexc⟩ := hΘpos (by linarith)
  have hhas : has := hiff.2 hut
  refine ⟨hhas, ?_⟩
  rw [hg hhas]
  have hpos1 : 0 < beta αj * Dφ := by positivity
  have hle : d / (2 * β * Dφ) ≤ Θ / (beta αj * Dφ) := by
    rw [show d / (2 * β * Dφ) = (d / 2) / (β * Dφ) by ring]
    exact div_le_div₀ (by linarith) hΘ hpos1 (mul_le_mul_of_nonneg_right hβj hDφ0.le)
  linarith

end Step

section BetStep

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- (copy-adapted from the certified `Wave30tz.Lower.bet_step`) Lemma 5 on the fitting event at a level `α_j ≤ α_i`, for a
Frank–Wolfe run: every pair is bet on with `λ_k ≥ λ_N(α_i)` and excess `≥ ϱ_*`. -/
theorem bet_step_fw (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ Dφ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) (hDφ0 : 0 < Dφ)
    {J n m : ℕ} {α : Fin J → ℝ} {δ lmax s2 ρ : ℝ} {R : LoRun 𝒳 J n m} {i j : Fin J} {d r : ℝ}
    (hgrid : IsGrid α) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hl0 : 0 < lmax) (hl12 : lmax ≤ 1 / 2) (hs2 : 0 < s2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hRun : IsWitnessRunFW R φ α δ lmax s2 ρ)
    (hfit1 : ∀ k, 1 ≤ fitCard R.lx (R.bat k) ∧ 1 ≤ fitCard R.ly (R.bat k))
    (hfitr : ∀ k, 1 / (fitCard R.lx (R.bat k) : ℝ) + 1 / (fitCard R.ly (R.bat k) : ℝ) ≤ r)
    (hd : 0 < d) (hdD : d ≤ (1 - ρ / 2) * Dpop φ P Q (α i))
    (hS1 : beta (α i) * Dφ * r ≤ d / 8) (hS2 : beta (α i) ^ 2 * κ ^ 2 * r ≤ 7 * d ^ 2 / 64)
    (hji : j ≤ i) (hN : 1 ≤ R.N)
    (hEm : MeasurableSet (fitEvent P Q φ κ (d / (8 * beta (α i))) R.lx R.ly R.bat)) :
    sampleLaw P Q n m (fitEvent P Q φ κ (d / (8 * beta (α i))) R.lx R.ly R.bat ∩
        {ω | ¬ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2}) ≤
      ENNReal.ofReal (genEps s2 (α i) (Real.log (1 / δ)) R.N (d / (2 * beta (α i) * Dφ))
        (lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N)) := by
  obtain ⟨⟨hpair, hfit, hfrac⟩, hwit, hlam⟩ := hRun
  have hL : 0 < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  have hαi0 : 0 ≤ α i := (hgrid.2 i).1
  have hαi1 : α i < 1 := (hgrid.2 i).2
  have hβ1 : 1 ≤ beta (α i) := Wave30tz.one_le_beta hαi0 hαi1
  have hϱ : 0 < d / (2 * beta (α i) * Dφ) := by positivity
  have hαji : α j ≤ α i := hgrid.1.monotone hji
  have hαj0 : 0 ≤ α j := (hgrid.2 j).1
  have h1αj : 0 < 1 + α j := by linarith
  have hhicap : lamHi lmax (α j) (Real.log (1 / δ)) s2 R.N ≤ lmax / (1 + α j) := min_le_left _ _
  have hha : lamHi lmax (α j) (Real.log (1 / δ)) s2 R.N * (1 + α j) ≤ lmax := by
    rwa [le_div_iff₀ h1αj] at hhicap
  have hlo0 : 0 ≤ lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N :=
    le_min (div_pos hl0 (by linarith)).le (Real.sqrt_nonneg _)
  have hlolo : lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N ≤ lamLo lmax (α j) (Real.log (1 / δ)) s2 R.N :=
    min_le_min (div_le_div_of_nonneg_left hl0.le h1αj (by linarith)) le_rfl
  have hE : ∀ ω ∈ fitEvent P Q φ κ (d / (8 * beta (α i))) R.lx R.ly R.bat, ∀ k : Fin R.N,
      lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N ≤ fracAt (R.lam j) (R.g j) R.bat R.A R.B ω.1 ω.2 k ∧
      α j + d / (2 * beta (α i) * Dφ) ≤ condMean P Q (R.g j) R.bat ω.1 ω.2 k := by
    intro ω hω k
    obtain ⟨hZk, hZmk⟩ := hω k
    obtain ⟨hhas, hexc⟩ := witness_step_fw P Q hφ hκ hDφ hDφ0 (hfit1 k).1 (hfit1 k).2
      (fitSample R.lx (R.bat k) ω.1) (fitSample R.ly (R.bat k) ω.2) hαj0 hαji hαi1 hd hρ0 hρ1
      (hdD.trans (mul_le_mul_of_nonneg_left (dpop_antitone 𝒳 H φ κ P Q (α j) (α i) hφ hκ hαj0 hαji hαi1)
        (by linarith))) (hfitr k) hS1 hS2 hZk hZmk (hwit j k ω.1 ω.2)
    exact ⟨hlolo.trans ((hlam j k ω.1 ω.2 (past (pairStat (R.g j) R.bat R.A R.B ω.1 ω.2) k)).2.1 hhas
      fun l => Bet.pairStat_mem hpair (hfit j) (Fin.castLE k.isLt.le l) ω.1 ω.2), hexc⟩
  refine (bet_power_route 𝒳 P Q n m R.N R.lx R.ly R.bat R.A R.B (α j) δ lmax
    (lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N) (lamHi lmax (α j) (Real.log (1 / δ)) s2 R.N) lmax
    (d / (2 * beta (α i) * Dφ)) (R.g j) (R.lam j) _ hpair hαj0 hδ0 hδ1 hl0 (by linarith) (hfit j) (hfrac j)
    (fun k x y z => (hlam j k x y z).1) hha (by linarith) hlo0 hϱ hEm hE).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact bet_arith hN hl0 hl12 hs2 hL hαj0 hαji

end BetStep

/-- (copy-adapted from the certified `Wave30tz.core_lower_bound`) **Proposition 1 (1), lower side** (§5) for Frank–Wolfe runs
of gap `ρ ∈ [0,1)`, with `d ≤ (1 − ρ/2)D_{α_i}`, for every floor `σ²_min > 0` and with the general lower fraction `λ_N`. -/
theorem core_lower_bound_fw {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (J n m : ℕ) (α : Fin J → ℝ) (δ lmax s2 ρ : ℝ) (R : LoRun 𝒳 J n m) (Bmax : ℕ) (i : Fin J)
    (d r : ℝ)
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ)
    (hgrid : IsGrid α) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hl0 : 0 < lmax) (hl12 : lmax ≤ 1 / 2) (hs2 : 0 < s2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hRun : IsWitnessRunFW R φ α δ lmax s2 ρ)
    (hBmax : ∀ k, R.bat k ≤ Bmax) (hfit1 : ∀ k, 1 ≤ fitCard R.lx (R.bat k) ∧ 1 ≤ fitCard R.ly (R.bat k))
    (hfitr : ∀ k, 1 / (fitCard R.lx (R.bat k) : ℝ) + 1 / (fitCard R.ly (R.bat k) : ℝ) ≤ r)
    (hd : 0 < d) (hdD : d ≤ (1 - ρ / 2) * Dpop φ P Q (α i))
    (hS1 : beta (α i) * Dφ * r ≤ d / 8) (hS2 : beta (α i) ^ 2 * κ ^ 2 * r ≤ 7 * d ^ 2 / 64) :
      sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < α i} ≤
        ENNReal.ofReal (2 * Bmax * Real.exp (-(2 * (max (d / (8 * beta (α i)) - 2 * (1 + √2) * κ * √r) 0) ^ 2 /
            (Dφ ^ 2 * r))) +
          J * genEps s2 (α i) (Real.log (1 / δ)) R.N (d / (2 * beta (α i) * Dφ))
            (lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N)) := by
  have hαi0 : 0 ≤ α i := (hgrid.2 i).1
  have hαi1 : α i < 1 := (hgrid.2 i).2
  have hDpos : 0 < Dpop φ P Q (α i) := by
    by_contra hcon
    have : (1 - ρ / 2) * Dpop φ P Q (α i) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.1 hcon)
    linarith
  have hDφ0 : 0 < Dφ := dphi_pos P Q hDφ hαi0 hαi1 hDpos
  have hL : 0 < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  set e := Real.exp (-(2 * (max (d / (8 * beta (α i)) - 2 * (1 + √2) * κ * √r) 0) ^ 2 / (Dφ ^ 2 * r))) with hedef
  set G := genEps s2 (α i) (Real.log (1 / δ)) R.N (d / (2 * beta (α i) * Dφ))
    (lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N) with hGdef
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hG0 : 0 ≤ G := (Real.exp_pos _).le
  have hJ : (1 : ℝ) ≤ J := Nat.one_le_cast.2 (Fin.pos i)
  -- the trivial case: `genEps = 1`
  by_cases hy : (R.N : ℝ) * lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N * (d / (2 * beta (α i) * Dφ)) -
      Real.log (1 / δ) - 4 * Real.log (1 / δ) * (1 + α i) ^ 2 / s2 ≤ 0
  · have hG1 : G = 1 := by
      rw [hGdef]; unfold genEps; rw [max_eq_right hy]; simp
    calc sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < α i} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hG1]
        have : 0 ≤ 2 * (Bmax : ℝ) * e := by positivity
        linarith
  replace hy := not_le.1 hy
  have hN : 1 ≤ R.N := by
    rcases Nat.eq_zero_or_pos R.N with h0 | h0
    · exfalso
      have h0' : (R.N : ℝ) = 0 := by exact_mod_cast h0
      rw [h0'] at hy
      have : 0 ≤ 4 * Real.log (1 / δ) * (1 + α i) ^ 2 / s2 := by positivity
      linarith
    · exact h0
  set Efit := fitEvent P Q φ κ (d / (8 * beta (α i))) R.lx R.ly R.bat with hEdef
  have hEm : MeasurableSet Efit := measurableSet_fitEvent P Q hφ hκ _ hfit1
  have hfitP : sampleLaw P Q n m Efitᶜ ≤ ENNReal.ofReal (2 * Bmax * e) :=
    fitEvent_compl_le P Q hφ hκ hDφ hDφ0 _ r hRun.1.1.2.2.1 hBmax hfit1 hfitr
  have hbet : ∀ j : Fin J, j ≤ i → sampleLaw P Q n m
      (Efit ∩ {ω | ¬ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2}) ≤ ENNReal.ofReal G :=
    fun j hji => bet_step_fw P Q hφ hκ hDφ hDφ0 hgrid hδ0 hδ1 hl0 hl12 hs2 hρ0 hρ1 hRun hfit1 hfitr hd hdD hS1 hS2 hji hN hEm
  -- the down-closed rule and the union bound
  set T := Finset.univ.filter fun j : Fin J => j ≤ i with hT
  have hsub : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | R.alphaLo α δ ω.1 ω.2 < α i} ⊆
      Efitᶜ ∪ ⋃ j ∈ T, (Efit ∩ {ω | ¬ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2}) := by
    intro ω hω
    obtain ⟨j, hj, hnr⟩ := (grid_events_route J α
      (fun j => rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2) 0 hgrid).2 i hω
    by_cases hωE : ω ∈ Efit
    · exact Or.inr (mem_iUnion₂.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, hωE, hnr⟩)
    · exact Or.inl hωE
  have hTcard : T.card ≤ J := (Finset.card_filter_le _ _).trans (by simp)
  calc sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < α i} ≤ sampleLaw P Q n m Efitᶜ + sampleLaw P Q n m
        (⋃ j ∈ T, (Efit ∩ {ω | ¬ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2})) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (2 * Bmax * e) + ∑ j ∈ T, ENNReal.ofReal G :=
        add_le_add hfitP ((measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun j hj => hbet j (Finset.mem_filter.1 hj).2))
    _ = ENNReal.ofReal (2 * Bmax * e) + T.card * ENNReal.ofReal G := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (2 * Bmax * e) + J * ENNReal.ofReal G :=
        by gcongr
    _ = ENNReal.ofReal (2 * Bmax * e + J * G) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- **T20 (a)** (copy-adapted from the certified `Wave30tz.lo_lower_bound_route`): the explicit bound of §5 for Frank–Wolfe
runs (`σ²_min ≤ 4`, `N ≥ L(1+α_i)²/(2λ_max²)`, `d ≤ (1 − ρ/2)D_{α_i}`). -/
theorem lo_lower_bound_fw_route : Claims.lo_lower_bound_fw := by
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ J n m α δ lmax s2 ρ R Bmax i d r hφ hκ hDφ hgrid hδ0 hδ1 hl0 hl12 hs20 hs24
    hρ0 hρ1 hRun hBmax hfit1 hfitr hd hdD hS1 hS2 hNL
  have h := core_lower_bound_fw φ κ Dφ P Q J n m α δ lmax s2 ρ R Bmax i d r hφ hκ hDφ hgrid hδ0 hδ1 hl0 hl12 hs20
    hρ0 hρ1 hRun hBmax hfit1 hfitr hd hdD hS1 hS2
  have hL : 0 < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  set L := Real.log (1 / δ) with hLdef
  have h1α : 0 < 1 + α i := by linarith [(hgrid.2 i).1]
  have hN : (0 : ℝ) < R.N := lt_of_lt_of_le (by positivity) hNL
  set lo := lamLo lmax (α i) L s2 R.N with hlodef
  have hcap : 0 < lmax / (1 + α i) := div_pos hl0 h1α
  have hlo_eq : lo = √(2 * L / (R.N * 4)) := by
    have hmax : max s2 4 = 4 := max_eq_right hs24
    have hsq : 2 * L / (R.N * 4) ≤ (lmax / (1 + α i)) ^ 2 := by
      have hNL' := hNL
      rw [div_le_iff₀ (by positivity)] at hNL'
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [hlodef]
    change min (lmax / (1 + α i)) (√(2 * L / (R.N * max s2 4))) = √(2 * L / (R.N * 4))
    rw [hmax]
    apply min_eq_right
    calc √(2 * L / (R.N * 4)) ≤ √((lmax / (1 + α i)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = lmax / (1 + α i) := Real.sqrt_sq hcap.le
  have hNlo : (R.N : ℝ) * lo = √(R.N * L / 2) := by
    rw [hlo_eq, show (R.N : ℝ) * L / 2 = R.N ^ 2 * (2 * L / (R.N * 4)) by field_simp; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hN.le]
  have hG : genEps s2 (α i) L R.N (d / (2 * beta (α i) * Dφ)) lo =
      epsN s2 (α i) L R.N (d / (2 * beta (α i) * Dφ)) := by
    unfold genEps epsN
    rw [show (R.N : ℝ) * lo * (d / (2 * beta (α i) * Dφ)) = d / (2 * beta (α i) * Dφ) * √(R.N * L / 2) by
      rw [← hNlo]; ring]
  rw [hG] at h
  exact h

end StatFormal.Wave31tr.RouteFW
