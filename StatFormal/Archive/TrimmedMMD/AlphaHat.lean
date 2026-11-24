import StatFormal.Archive.TrimmedMMD.Statements
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic

/-!
# Proofs: the threshold-crossing estimator of the trimmed-MMD paper

Certifies `Claims.alphaest_wellDefined`, `Claims.consistency_i`, `Claims.consistency_i_zero`,
`Claims.consistency_ii`, `Claims.rate` (see `Statements.lean` for scope).
-/

noncomputable section
open Real Set MeasureTheory Filter Topology

namespace StatFormal.TrimmedMMD

/-! ## The radius and threshold -/

/-- The sample-size factor `4/√n + √(2 log(2/δ)/n)` is nonnegative. -/
theorem fac_nonneg (δ : ℝ) (n : ℕ) : 0 ≤ 4 / √(n : ℝ) + √(2 * Real.log (2 / δ) / n) := by
  positivity

theorem rn_eq (κ α δ : ℝ) (n : ℕ) :
    rn κ α δ n = κ / (1 - α) * (4 / √(n : ℝ) + √(2 * Real.log (2 / δ) / n)) := rfl

theorem rn_nonneg {κ α : ℝ} (hκ : 0 ≤ κ) (hα : α < 1) (δ : ℝ) (n : ℕ) : 0 ≤ rn κ α δ n := by
  rw [rn_eq]
  exact mul_nonneg (div_nonneg hκ (by linarith)) (fac_nonneg δ n)

theorem tau_nonneg {κ α : ℝ} (hκ : 0 ≤ κ) (hα : α < 1) (δ : ℝ) (n m : ℕ) :
    0 ≤ tau κ α δ n m :=
  add_nonneg (rn_nonneg hκ hα _ n) (rn_nonneg hκ hα _ m)

/-- `κ/(1-α)` is monotone on `α < 1`. -/
theorem coef_mono {κ α β : ℝ} (hκ : 0 ≤ κ) (hab : α ≤ β) (hb : β < 1) :
    κ / (1 - α) ≤ κ / (1 - β) :=
  div_le_div_of_nonneg_left hκ (by linarith) (by linarith)

/-- `τ_{n,m}(·,δ)` is monotone on `[0,1)` ("`r_n(·,δ)` increases in `α`"). -/
theorem tau_mono {κ α β : ℝ} (hκ : 0 ≤ κ) (hab : α ≤ β) (hb : β < 1) (δ : ℝ) (n m : ℕ) :
    tau κ α δ n m ≤ tau κ β δ n m := by
  unfold tau
  rw [rn_eq, rn_eq, rn_eq κ β, rn_eq κ β]
  have h := coef_mono hκ hab hb
  have h1 := fac_nonneg (δ / 2) n
  have h2 := fac_nonneg (δ / 2) m
  nlinarith [mul_le_mul_of_nonneg_right h h1, mul_le_mul_of_nonneg_right h h2]

/-- For fixed `α < 1`, `r_n(α,δ) → 0` as `n → ∞`. -/
theorem tendsto_rn {κ α : ℝ} (δ : ℝ) :
    Tendsto (fun n : ℕ => rn κ α δ n) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => 4 / √(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  have h2 : Tendsto (fun n : ℕ => √(2 * Real.log (2 / δ) / n)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.log (2 / δ)))
    rw [Real.sqrt_zero] at this
    exact this
  have := (h1.add h2).const_mul (κ / (1 - α))
  simpa [rn_eq] using this

/-! ## The crossing set and `α̂` -/

theorem crossSet_bddBelow (Dh τ : ℝ → ℝ) : BddBelow (crossSet Dh τ) :=
  ⟨0, fun _ h => h.1.1⟩

theorem alphaHat_nonneg {Dh τ : ℝ → ℝ} (h : (crossSet Dh τ).Nonempty) : 0 ≤ alphaHat Dh τ :=
  le_csInf h (fun _ hx => hx.1.1)

/-- Deterministic core of (i): on the event, `α*` is in the crossing set, so `α̂ ≤ α*`. -/
theorem mem_crossSet_of_event {D Dh τ : ℝ → ℝ} {αs : ℝ} (hαs : αs ∈ Ico (0 : ℝ) 1)
    (hD : D αs = 0) (hE : ∀ α ∈ Ico (0 : ℝ) 1, |Dh α - D α| ≤ τ α) : αs ∈ crossSet Dh τ := by
  refine ⟨hαs, ?_⟩
  have := (abs_le.1 (hE αs hαs)).2
  linarith

theorem alphaHat_le_of_event {D Dh τ : ℝ → ℝ} {αs : ℝ} (hαs : αs ∈ Ico (0 : ℝ) 1)
    (hD : D αs = 0) (hE : ∀ α ∈ Ico (0 : ℝ) 1, |Dh α - D α| ≤ τ α) : alphaHat Dh τ ≤ αs :=
  csInf_le (crossSet_bddBelow Dh τ) (mem_crossSet_of_event hαs hD hE)

/-- Lower bound: if every point of the (nonempty) crossing set is `≥ a`, then `α̂ ≥ a`. -/
theorem le_alphaHat {Dh τ : ℝ → ℝ} {a : ℝ} (hne : (crossSet Dh τ).Nonempty)
    (h : ∀ α ∈ crossSet Dh τ, a ≤ α) : a ≤ alphaHat Dh τ :=
  le_csInf hne h

/-! ## The probability layer -/

/-- Union bound: `P(EP ∩ EQ) ≥ 1 - δ` when each event has probability `≥ 1 - δ/2`. -/
theorem prob_inter_ge {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {EP EQ : Set Ω} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hQm : MeasurableSet EQ)
    (hP : ENNReal.ofReal (1 - δ / 2) ≤ P EP) (hQ : ENNReal.ofReal (1 - δ / 2) ≤ P EQ) :
    ENNReal.ofReal (1 - δ) ≤ P (EP ∩ EQ) := by
  have hU := measure_union_add_inter EP hQm (μ := P)
  have hle : P (EP ∪ EQ) ≤ 1 := prob_le_one
  have hsum : ENNReal.ofReal (1 - δ / 2) + ENNReal.ofReal (1 - δ / 2) =
      1 + ENNReal.ofReal (1 - δ) := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by norm_num) (by linarith)]
    congr 1; ring
  have : 1 + ENNReal.ofReal (1 - δ) ≤ 1 + P (EP ∩ EQ) := by
    calc 1 + ENNReal.ofReal (1 - δ) = ENNReal.ofReal (1 - δ / 2) + ENNReal.ofReal (1 - δ / 2) :=
          hsum.symm
      _ ≤ P EP + P EQ := add_le_add hP hQ
      _ = P (EP ∪ EQ) + P (EP ∩ EQ) := hU.symm
      _ ≤ 1 + P (EP ∩ EQ) := add_le_add hle le_rfl
  exact (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 this

/-! ## Certified claims -/

theorem alphaest_wellDefined : Claims.alphaest_wellDefined := by
  intro κ δ n m Dh hκ hδ0 hδ1 hn hm hDh
  -- choose α close to 1 so that r_n(α, δ/2) ≥ 2κ
  set c := 4 / √(n : ℝ) + √(2 * Real.log (2 / (δ / 2)) / n) with hc
  have hsqrt : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hcpos : 0 < c := by
    have : 0 < 4 / √(n : ℝ) := div_pos (by norm_num) hsqrt
    have := Real.sqrt_nonneg (2 * Real.log (2 / (δ / 2)) / n)
    linarith
  set α := max 0 (1 - c / 2) with hαdef
  have hα1 : α < 1 := max_lt (by norm_num) (by linarith)
  have hα0 : 0 ≤ α := le_max_left _ _
  have h1α : 1 - α ≤ c / 2 := by have := le_max_right 0 (1 - c / 2); linarith
  have h1αpos : 0 < 1 - α := by linarith
  refine ⟨α, ⟨hα0, hα1⟩, ?_⟩
  have hrn : 2 * κ ≤ rn κ α (δ / 2) n := by
    rw [rn_eq, ← hc, div_mul_eq_mul_div, le_div_iff₀ h1αpos]
    nlinarith
  have hrm := rn_nonneg hκ.le hα1 (δ / 2) m
  calc Dh α ≤ 2 * κ := hDh α ⟨hα0, hα1⟩
    _ ≤ tau κ α δ n m := by unfold tau; linarith

theorem consistency_i : Claims.consistency_i := by
  intro Ω _ P _ D Dh κ δ αs n m EP EQ hκ hδ0 hδ1 hn hm hαs hD hEPm hEQm hP hQ hE
  refine le_trans (prob_inter_ge hδ0 hδ1 hEQm hP hQ) (measure_mono ?_)
  intro ω hω
  exact alphaHat_le_of_event hαs hD (hE ω hω)

theorem consistency_i_zero : Claims.consistency_i_zero := by
  intro Ω _ P _ D Dh κ δ n m EP EQ hκ hδ0 hδ1 hn hm hD hEPm hEQm hP hQ hE
  refine le_trans (prob_inter_ge hδ0 hδ1 hEQm hP hQ) (measure_mono ?_)
  intro ω hω
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, one_pos⟩
  have hle := alphaHat_le_of_event h0 hD (hE ω hω)
  have hge := alphaHat_nonneg ⟨0, mem_crossSet_of_event h0 hD (hE ω hω)⟩
  exact le_antisymm hle hge

/-- Deterministic core of `thm:rate`. -/
theorem rate_det {D Dh : ℝ → ℝ} {κ δ αs : ℝ} {n m : ℕ} {om : ℝ → ℝ} {ε : ℝ} (hκ : 0 < κ)
    (hαs : αs ∈ Ico (0 : ℝ) 1) (hD : D αs = 0) (hom : StrictMonoOn om (Icc 0 αs))
    (hmar : ∀ e ∈ Icc (0 : ℝ) αs, om e ≤ D (αs - e)) (hε : ε ∈ Icc (0 : ℝ) αs)
    (hωε : om ε = 2 * tau κ αs δ n m)
    (hE : ∀ α ∈ Ico (0 : ℝ) 1, |Dh α - D α| ≤ tau κ α δ n m) :
    alphaHat Dh (fun α => tau κ α δ n m) ∈ Icc (αs - ε) αs := by
  have hmem := mem_crossSet_of_event (τ := fun α => tau κ α δ n m) hαs hD hE
  refine ⟨le_alphaHat ⟨αs, hmem⟩ ?_, alphaHat_le_of_event hαs hD hE⟩
  intro α ⟨hαI, hαle⟩
  by_contra hlt
  push Not at hlt
  set e := αs - α with he
  have he_mem : e ∈ Icc (0 : ℝ) αs := ⟨by linarith [hε.1], by linarith [hαI.1]⟩
  have hεe : ε < e := by linarith
  have h1 : om ε < om e := hom hε he_mem hεe
  have h2 : om e ≤ D α := by have := hmar e he_mem; rwa [he, sub_sub_cancel] at this
  have h3 : D α ≤ 2 * tau κ α δ n m := by
    have := (abs_le.1 (hE α hαI)).1
    simp only at hαle
    linarith
  have h4 : tau κ α δ n m ≤ tau κ αs δ n m :=
    tau_mono hκ.le (by linarith [hε.1]) hαs.2 δ n m
  linarith

theorem rate : Claims.rate := by
  intro Ω _ P _ D Dh κ δ αs n m EP EQ om ε hκ hδ0 hδ1 hn hm hαs hD hom hmar hε hωε
    hEPm hEQm hP hQ hE
  refine le_trans (prob_inter_ge hδ0 hδ1 hEQm hP hQ) (measure_mono ?_)
  intro ω hω
  exact rate_det hκ hαs hD hom hmar hε hωε (hE ω hω)

theorem consistency_ii : Claims.consistency_ii := by
  intro D κ δ αs hκ hδ0 hδ1 hαs hD hanti hpos ε hε
  have hαs' : αs ∈ Ico (0 : ℝ) 1 := ⟨hαs.1.le, hαs.2⟩
  have hb_mem : αs - ε ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hε.2], by linarith [hε.1, hαs.2]⟩
  -- the gap to beat
  have hc : 0 < D (αs - ε) := hpos _ ⟨hb_mem.1, by linarith [hε.1]⟩
  -- eventually r_n(αs, δ/2) < D(αs - ε)/4
  have hev : ∀ᶠ n : ℕ in atTop, rn κ αs (δ / 2) n < D (αs - ε) / 4 :=
    (tendsto_rn (κ := κ) (α := αs) (δ / 2)).eventually (gt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n m hNn hNm hn hm Ω _ P _ Dh EP EQ hEPm hEQm hP hQ hE => ?_⟩
  refine le_trans (prob_inter_ge hδ0 hδ1 hEQm hP hQ) (measure_mono ?_)
  intro ω hω
  have hEω := hE ω hω
  have hmem := mem_crossSet_of_event (τ := fun α => tau κ α δ n m) hαs' hD hEω
  refine ⟨le_alphaHat ⟨αs, hmem⟩ ?_, alphaHat_le_of_event hαs' hD hEω⟩
  intro α ⟨hαI, hαle⟩
  by_contra hlt
  push Not at hlt
  have h1 : D (αs - ε) ≤ D α := hanti hαI hb_mem hlt.le
  have h2 : D α ≤ 2 * tau κ α δ n m := by
    have := (abs_le.1 (hEω α hαI)).1
    simp only at hαle
    linarith
  have h3 : tau κ α δ n m ≤ tau κ αs δ n m :=
    tau_mono hκ.le (by linarith [hε.1]) hαs.2 δ n m
  have h4 : tau κ αs δ n m < D (αs - ε) / 2 := by
    unfold tau; have := hN n hNn; have := hN m hNm; linarith
  linarith

end StatFormal.TrimmedMMD

namespace StatFormal.TrimmedMMD

theorem consistency_i_onEvent : Claims.consistency_i_onEvent :=
  fun _ _ _ _ _ _ _ hαs hD hE => alphaHat_le_of_event hαs hD hE

theorem rate_onEvent : Claims.rate_onEvent :=
  fun _ _ _ _ _ _ _ _ _ hκ hαs hD hom hmar hε hωε hE => rate_det hκ hαs hD hom hmar hε hωε hE

theorem event_prob : Claims.event_prob := by
  intro Ω _ P _ δ EP EQ hδ0 hδ1 _ hQm hP hQ
  exact prob_inter_ge hδ0 hδ1 hQm hP hQ

end StatFormal.TrimmedMMD
