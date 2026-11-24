import StatFormal.Wave31tu.Statements
import StatFormal.Wave31tl.RouteCore

/-!
# Wave 31tu route B: Claim Y16 `lap_bets`, the bets are those of Theorem S4.3 (S4 :1037-1038, :1354-1366; untrusted proof material)

The betting half of the proof of Theorem S4.3 with an arbitrary measurable event `E` of probability `≥ 1 − η/2` in place of the
fitting event: on `E`, at every level `α_j ≤ α⋆ − ε`, every pair bets and has excess `Δ_k − α_j ≥ ϱx_j`, `x_j = (α⋆ − α_j)/ε ≥ 1`,
and `ϱ ≥ T_bet(J_ε)` (the frozen `Tbet` at `Δ_φ = ½`). The route replays `Wave31tl.Core.core_lower`:

* `ϱ ≤ 1` (some level `≤ α⋆ − ε` exists, else the event is empty; `E ≠ ∅` as `η/2 < 1`; `Δ_k ≤ 1` for a ramp in `[0,1]`), so
  `T_bet ≤ 1` gives `N ≥ 50L_δ ≥ 8L_δ` (`N_ge_of_Tbet`) and `λ_N = √(L_δ/(2N))`;
* Lemma 5 (`Wave30tz.bet_power_route`, `Lower.bet_arith`) and `Core.genEps_le`, `Core.arith_a0` at `β = 1`, `Δ_φ = ½`, `D⋆ = ϱ`:
  `P(E ∩ {H_{0,α_j} not rejected}) ≤ e^{−A x_j²}`, `A ≥ log(2J_ε/η)`;
* the union bound over `Eᶜ` and the levels `α_j ≤ α⋆ − ε` (`grid_events_route`, `eq:downclosed`) and the level sum
  `Σ_j e^{−A x_j²} ≤ J_ε e^{−A} ≤ η/2` (`Basic.sum_exp_le_Jeps`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tu.RouteB

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.Wave31tl

/-- `T_bet(½, σ²_min, L, η, J′, N) = √(2/N)((1 + 16/σ²_min)√L + (2/σ_min)√(log(2J′/η))) ≥ 5√(2L/N) > 0`. -/
lemma Tbet_half_ge {s2 L η J' : ℝ} {N : ℕ} (hs20 : 0 < s2) (hs24 : s2 ≤ 4) :
    5 * (√(2 / N) * √L) ≤ Tbet (1 / 2) s2 L η J' N := by
  unfold Tbet
  have h5 : 5 ≤ 1 + 16 / s2 := by
    have : 4 ≤ 16 / s2 := by rw [le_div_iff₀ hs20]; linarith
    linarith
  have hW : 5 * √L ≤ (1 + 16 / s2) * √L + 2 / √s2 * √(Real.log (2 * J' / η)) := by
    have : 0 ≤ 2 / √s2 * √(Real.log (2 * J' / η)) := by positivity
    nlinarith [Real.sqrt_nonneg L]
  have := mul_le_mul_of_nonneg_left hW (Real.sqrt_nonneg (2 / (N : ℝ)))
  linarith

/-- `T_bet(½, …) ≤ ϱ ≤ 1` forces `N ≥ 50L ≥ 8L`. -/
lemma N_ge_of_Tbet {s2 L η J' ϱ : ℝ} {N : ℕ} (hs20 : 0 < s2) (hs24 : s2 ≤ 4) (hL : 0 < L) (hN : (0 : ℝ) < N)
    (h : Tbet (1 / 2) s2 L η J' N ≤ ϱ) (hϱ : ϱ ≤ 1) : 8 * L ≤ N := by
  have h5 := Tbet_half_ge (L := L) (η := η) (J' := J') (N := N) hs20 hs24
  set u := √(2 / (N : ℝ)) * √L with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 / 5 := by linarith
  have hsq : u ^ 2 = 2 * L / N := by
    rw [hu, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hL.le]; ring
  have : u ^ 2 ≤ (1 / 5) ^ 2 := pow_le_pow_left₀ hu0 hu1 2
  rw [hsq, div_le_iff₀ hN] at this
  linarith

/-- A pair's conditional mean of a `[0,1]`-valued ramp is at most `1`. -/
lemma condMean_le_one {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {n m N : ℕ} {g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ} {bat : Fin N → ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (k : Fin N)
    (hg : ∀ z, g (bat k) x y z ∈ Icc (0 : ℝ) 1) : condMean P Q g bat x y k ≤ 1 := by
  unfold condMean
  have h1 : ∫ z, g (bat k) x y z ∂P ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := P) (C := 1) (f := fun z => g (bat k) x y z)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hg z).1], (hg z).2⟩)
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have h2 : 0 ≤ ∫ z, g (bat k) x y z ∂Q := integral_nonneg fun z => (hg z).1
  linarith

/-- **Claim Y16** (`lap_bets`): the bets of the proof of Theorem S4.19 are those of Theorem S4.3. -/
theorem lap_bets_route : Claims.lap_bets := by
  intro 𝒳 _ P Q _ _ J n m α δ s2 η h0 ε ϱ R E hgrid hJ hδ0 hδ1 hs20 hs24 hη0 hη1 hh0 hgap hε hN hadm hlam hEm hEc hTbet hE
  classical
  obtain ⟨hpair, hfitR, hfrac⟩ := hadm
  set αs := StatFormal.Distances.tvDist P Q with hαsdef
  set T := Finset.univ.filter (fun j : Fin J => α j ≤ αs - ε) with hTdef
  -- no level `≤ α⋆ − ε`: the event is empty
  by_cases hTne : T.Nonempty
  swap
  · have : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | R.alphaLo α δ ω.1 ω.2 < gridFloor α (αs - ε)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      by_contra hlt
      obtain ⟨i, hi, -⟩ := Basic.exists_of_lt_gridFloor α (Limits.run_alphaLo_nonneg R hgrid δ ω.1 ω.2)
        (not_le.1 hlt)
      exact hTne ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
    rw [this, measure_empty]; exact bot_le
  obtain ⟨j0, hj0⟩ := hTne
  have hj0a : α j0 ≤ αs - ε := (Finset.mem_filter.1 hj0).2
  -- `E` is nonempty
  have hEne : E.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hprob : sampleLaw P Q n m univ = 1 := by
      unfold sampleLaw; exact measure_univ
    rw [hne, Set.compl_empty, hprob] at hEc
    have : (1 : ℝ≥0∞) < 1 := hEc.trans_lt (by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith))
    exact lt_irrefl _ this
  obtain ⟨z0, hz0⟩ := hEne
  -- the constants
  set L := Real.log (1 / δ) with hLdef
  have hL : 0 < L := by rw [hLdef, one_div, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  have hNr : (1 : ℝ) ≤ R.N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < R.N := by linarith
  set J' := Jeps J ε h0 with hJ'def
  have hJ'1 : 1 ≤ J' := by
    rw [hJ'def]; unfold Jeps
    refine le_min (by exact_mod_cast hJ) ?_
    have : 0 ≤ ε / h0 := (div_pos hε hh0).le
    linarith
  set ℓ := Real.log (2 * J' / η) with hℓdef
  have hℓ : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hη0]; nlinarith)
  have hℓ0 : 0 ≤ ℓ := le_trans (Real.log_nonneg (by norm_num)) hℓ
  have hT5 := Tbet_half_ge (L := L) (η := η) (J' := J') (N := R.N) hs20 hs24
  have hϱ : 0 < ϱ := lt_of_lt_of_le (by positivity) (hT5.trans hTbet)
  -- `ϱ ≤ 1`
  have hϱ1 : ϱ ≤ 1 := by
    obtain ⟨-, hΔ0⟩ := hE z0 hz0 j0 hj0a ⟨0, hN⟩
    have hΔle := condMean_le_one P Q (g := R.g j0) (bat := R.bat) z0.1 z0.2 ⟨0, hN⟩
      (fun z => Bet.fit_mem (hfitR j0) ⟨0, hN⟩ z0.1 z0.2 z)
    have hx0 : 1 ≤ (αs - α j0) / ε := by rw [le_div_iff₀ hε]; linarith
    have : ϱ ≤ ϱ * ((αs - α j0) / ε) := le_mul_of_one_le_right hϱ.le hx0
    linarith [(hgrid.2 j0).1]
  have hN8 : 8 * L ≤ R.N := N_ge_of_Tbet hs20 hs24 hL hNpos hTbet hϱ1
  -- the excess margin (`Core.arith_a0` at `β = 1`, `Δ_φ = ½`, `D⋆ = ϱ`)
  have hbet' : (1 : ℝ) * (2 * (1 / 2) * √(2 / R.N) * ((1 + 16 / s2) * √L + 2 / √s2 * √ℓ)) ≤ ϱ := by
    rw [one_mul]; exact hTbet
  obtain ⟨ha0, hA⟩ := Core.arith_a0 one_pos (by norm_num) hs20 hL hNpos hℓ0 hbet'
  have e1 : ϱ / (2 * 1 * (1 / 2)) = ϱ := by norm_num
  rw [e1] at ha0 hA
  set a0 := ϱ * √(R.N * L / 2) - L * (1 + 16 / s2) with ha0def
  have ha00 : 0 ≤ a0 := le_trans (by positivity) ha0
  set A := s2 * a0 ^ 2 / (4 * L) with hAdef
  -- one level
  have hlevel : ∀ j ∈ T, sampleLaw P Q n m (E ∩ {ω | ¬ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2}) ≤
      ENNReal.ofReal (Real.exp (-(A * ((αs - α j) / ε) ^ 2))) := by
    intro j hj
    have hja : α j ≤ αs - ε := (Finset.mem_filter.1 hj).2
    have hαj0 : 0 ≤ α j := (hgrid.2 j).1
    have hαj1 : α j < 1 := (hgrid.2 j).2
    set xj := (αs - α j) / ε with hxjdef
    have hxj1 : 1 ≤ xj := by rw [hxjdef, le_div_iff₀ hε]; linarith
    have hlo0 : 0 ≤ lamLo (1 / 2) (α j) L s2 R.N :=
      le_min (div_pos (by norm_num) (by linarith)).le (Real.sqrt_nonneg _)
    have hE' : ∀ ω ∈ E, ∀ k : Fin R.N,
        lamLo (1 / 2) (α j) L s2 R.N ≤ fracAt (R.lam j) (R.g j) R.bat R.A R.B ω.1 ω.2 k ∧
        α j + ϱ * xj ≤ condMean P Q (R.g j) R.bat ω.1 ω.2 k := by
      intro ω hω k
      obtain ⟨hhas, hexc⟩ := hE ω hω j hja k
      exact ⟨(hlam j k ω.1 ω.2 (past (pairStat (R.g j) R.bat R.A R.B ω.1 ω.2) k)).2 hhas
        fun l => Bet.pairStat_mem hpair (hfitR j) (Fin.castLE k.isLt.le l) ω.1 ω.2, hexc⟩
    have h1αj : 0 < 1 + α j := by linarith
    have hhicap : lamHi (1 / 2) (α j) L s2 R.N ≤ 1 / 2 / (1 + α j) := min_le_left _ _
    have hha : lamHi (1 / 2) (α j) L s2 R.N * (1 + α j) ≤ 1 / 2 := by rwa [le_div_iff₀ h1αj] at hhicap
    have hρj : 0 < ϱ * xj := mul_pos hϱ (by linarith)
    refine (bet_power_route 𝒳 P Q n m R.N R.lx R.ly R.bat R.A R.B (α j) δ (1 / 2)
      (lamLo (1 / 2) (α j) L s2 R.N) (lamHi (1 / 2) (α j) L s2 R.N) (1 / 2)
      (ϱ * xj) (R.g j) (R.lam j) _ hpair hαj0 hδ0 hδ1 (by norm_num) (by norm_num) (hfitR j)
      (hfrac j) (fun k x y z => (hlam j k x y z).1) hha (by norm_num) hlo0 hρj hEm hE').trans
      (ENNReal.ofReal_le_ofReal ?_)
    refine (Lower.bet_arith hN (by norm_num) le_rfl hs20 hL hαj0 le_rfl).trans ?_
    exact Core.genEps_le s2 L (α j) _ ϱ xj R.N hs20 hs24 hL hαj0 hαj1 hN8 hxj1 le_rfl ha00
  -- the union bound
  have hsub : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | R.alphaLo α δ ω.1 ω.2 < gridFloor α (αs - ε)} ⊆
      Eᶜ ∪ ⋃ j ∈ T, (E ∩ {ω | ¬ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2}) := by
    intro ω hω
    obtain ⟨i0, hi0a, hi0lt⟩ := Basic.exists_of_lt_gridFloor α (Limits.run_alphaLo_nonneg R hgrid δ ω.1 ω.2) hω
    obtain ⟨j, hj, hnr⟩ := (grid_events_route J α
      (fun j => rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2) 0 hgrid).2 i0 hi0lt
    have hjT : j ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ _, (hgrid.1.monotone hj).trans hi0a⟩
    by_cases hωE : ω ∈ E
    · exact Or.inr (mem_iUnion₂.2 ⟨j, hjT, hωE, hnr⟩)
    · exact Or.inl hωE
  have hsumA := Basic.sum_exp_le_Jeps (αs := αs) hgap hh0 hε (hℓ.trans hA)
  have hexpA : J' * Real.exp (-A) ≤ η / 2 := by
    calc J' * Real.exp (-A) ≤ J' * Real.exp (-ℓ) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith))
          (by linarith)
      _ = η / 2 := by
          rw [hℓdef, Real.exp_neg, Real.exp_log (by positivity), inv_div]; field_simp
  calc sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < gridFloor α (αs - ε)}
      ≤ sampleLaw P Q n m Eᶜ + sampleLaw P Q n m
          (⋃ j ∈ T, (E ∩ {ω | ¬ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2})) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (η / 2) + ∑ j ∈ T, ENNReal.ofReal (Real.exp (-(A * ((αs - α j) / ε) ^ 2))) :=
        add_le_add hEc ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hlevel))
    _ = ENNReal.ofReal (η / 2) + ENNReal.ofReal (∑ j ∈ T, Real.exp (-(A * ((αs - α j) / ε) ^ 2))) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal (hsumA.trans hexpA))
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end StatFormal.Wave31tu.RouteB
