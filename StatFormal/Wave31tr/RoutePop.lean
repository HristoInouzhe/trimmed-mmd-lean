import StatFormal.Wave31tr.Statements
import StatFormal.Wave30tz.RouteLower
import StatFormal.Lib.TVFacts.Basic
import StatFormal.Lib.TVFacts.Rpow

/-!
# Wave 31tr, chunk E2: margins, total variation under maps, the Bayes risk, the propensity score (untrusted)

* `upper_end_route` (T54): the margin at `ε = α⋆ − α` and `ε^γ ≤ Ď/c₀ ⇔ ε ≤ (Ď/c₀)^{1/γ}` (`TVFacts.rpow_le_iff_le_rpow_one_div`);
  trivial for `α ≥ α⋆`;
* `margin_eps0_route` (T55): for `ε ≤ ε₀` the factor `(ε₀/α⋆)^γ ≤ 1`; for `ε > ε₀` the path is nonincreasing
  (`Wave30tz.dpop_antitone`) and `(ε₀/α⋆)^γ ε^γ = (ε₀ε/α⋆)^γ ≤ ε₀^γ`;
* `margin_dbar_factor_route` (T25): the generalized inverse of `ε ↦ (1−α⋆)c₀ε^γ` (`TVFacts.sSup_rpow_sublevel`,
  `TVFacts.rpow_one_div_div_mul`);
* `tv_pushforward_route` (T53): data processing (`Distances.tvDist_map_le`), the Scheffé set (`TVFacts.tvDist_eq_sub_of_withDensity`),
  `[0,1]`-valued functions (`TVFacts.integral_sub_le_tvDist_of_mem_Icc`);
* `bayes_risk_route` (T57): `TVFacts.iInf_bayes_eq`;
* `propensity_core_route` (T52): arithmetic, and `{p > q} = {e > π}`, so `TV` is attained at a preimage under `e`
  (`TVFacts.tvDist_map_eq_of_preimage`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tr.RoutePop

open StatFormal.TrimmedMMD.Unconditional StatFormal.Distances

theorem dpop_nonneg {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H)
    (P Q : Measure 𝒳) (α : ℝ) : 0 ≤ Dpop φ P Q α :=
  Real.sInf_nonneg fun _ ⟨_, _, _, _, hr⟩ => hr ▸ norm_nonneg _

/-! ### T54 -/

theorem upper_end_route : Claims.upper_end := by
  intro 𝒳 H _ _ _ φ P Q _ _ c₀ γ α Dc hM hα0 hα1 hD
  obtain ⟨hc₀, hγ, hm⟩ := hM
  set T := tvDist P Q with hT
  have hDc0 : 0 ≤ Dc / c₀ := div_nonneg ((dpop_nonneg φ P Q α).trans hD) hc₀.le
  by_cases hαT : T ≤ α
  · linarith [Real.rpow_nonneg hDc0 (1 / γ)]
  · push_neg at hαT
    have h1 := hm (T - α) ⟨by linarith, by linarith⟩
    rw [sub_sub_cancel] at h1
    have h2 : (T - α) ^ γ ≤ Dc / c₀ := by
      rw [le_div_iff₀ hc₀]
      linarith [mul_comm c₀ ((T - α) ^ γ)]
    have h3 := (TVFacts.rpow_le_iff_le_rpow_one_div (by linarith) hDc0 (by linarith)).1 h2
    linarith

/-! ### T55 -/

theorem margin_eps0_route : Claims.margin_eps0 := by
  intro 𝒳 H _ _ _ _ φ κ P Q _ _ c₀ γ ε₀ hφ hκ hc₀ hγ hε₀ hε₀T hm
  set T := tvDist P Q with hT
  have hT0 : 0 < T := lt_of_lt_of_le hε₀ hε₀T
  have hT1 : T ≤ 1 := tvDist_le_one
  have hr0 : 0 ≤ ε₀ / T := div_nonneg hε₀.le hT0.le
  have hr1 : ε₀ / T ≤ 1 := (div_le_one hT0).2 hε₀T
  refine ⟨mul_pos hc₀ (Real.rpow_pos_of_pos (div_pos hε₀ hT0) _), hγ, ?_⟩
  intro e he
  have he0 : 0 ≤ e ^ γ := Real.rpow_nonneg he.1 γ
  by_cases hee : e ≤ ε₀
  · have h1 := hm e ⟨he.1, hee⟩
    have h2 : (ε₀ / T) ^ γ ≤ 1 := Real.rpow_le_one hr0 hr1 (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hc₀.le he0)
    nlinarith
  · push_neg at hee
    have h1 := hm ε₀ ⟨hε₀.le, le_rfl⟩
    have hanti : Dpop φ P Q (T - ε₀) ≤ Dpop φ P Q (T - e) :=
      StatFormal.Wave30tz.dpop_antitone 𝒳 H φ κ P Q (T - e) (T - ε₀) hφ hκ (by linarith [he.2]) (by linarith)
        (by linarith)
    have h2 : (ε₀ / T) ^ γ * e ^ γ ≤ ε₀ ^ γ := by
      rw [← Real.mul_rpow hr0 he.1]
      refine Real.rpow_le_rpow (mul_nonneg hr0 he.1) ?_ (by linarith)
      calc ε₀ / T * e ≤ ε₀ / T * T := mul_le_mul_of_nonneg_left he.2 hr0
        _ = ε₀ := div_mul_cancel₀ ε₀ hT0.ne'
    calc c₀ * (ε₀ / T) ^ γ * e ^ γ = c₀ * ((ε₀ / T) ^ γ * e ^ γ) := by ring
      _ ≤ c₀ * ε₀ ^ γ := mul_le_mul_of_nonneg_left h2 hc₀.le
      _ ≤ Dpop φ P Q (T - ε₀) := h1
      _ ≤ Dpop φ P Q (T - e) := hanti

/-! ### T25 -/

theorem margin_dbar_factor_route : Claims.margin_dbar_factor := by
  intro 𝒳 H _ _ _ φ P Q _ _ c₀ γ hM hT1
  obtain ⟨hc₀, hγ, hm⟩ := hM
  set T := tvDist P Q with hT
  have hT0 : 0 ≤ T := tvDist_nonneg P Q
  have hs : 0 < 1 - T := by linarith
  have hγ0 : 0 < γ := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.1 hab hγ0.le) (mul_nonneg hs.le hc₀.le)
  · intro e he
    have h1 := hm e he
    have hD := dpop_nonneg φ P Q (T - e)
    have he0 : 0 ≤ e ^ γ := Real.rpow_nonneg he.1 γ
    have huP : StatFormal.Wave31ti.uPath φ P Q (T - e) = (1 - T + e) * Dpop φ P Q (T - e) := by
      simp only [StatFormal.Wave31ti.uPath]; ring
    refine ⟨mul_nonneg (mul_nonneg hs.le hc₀.le) he0, ?_, huP⟩
    rw [huP]
    have h2 := mul_le_mul_of_nonneg_left h1 hs.le
    have h3 : (1 - T) * Dpop φ P Q (T - e) ≤ (1 - T + e) * Dpop φ P Q (T - e) :=
      mul_le_mul_of_nonneg_right (by linarith [he.1]) hD
    nlinarith
  · intro t ht
    simp only [StatFormal.Wave31to.genInv]
    rw [TVFacts.sSup_rpow_sublevel (mul_pos hs hc₀) hγ0 hT0 ht, TVFacts.rpow_one_div_div_mul hs hc₀ ht]
  · exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs (by linarith) (div_nonpos_of_nonpos_of_nonneg (by norm_num) hγ0.le)

/-! ### T53 -/

theorem tv_pushforward_route : Claims.tv_pushforward := by
  refine ⟨fun 𝒳 𝒴 _ _ P Q _ _ f hf => tvDist_map_le hf, ?_⟩
  intro 𝒳 _ P Q _ _ p q hp hq hP hQ
  exact ⟨(TVFacts.tvDist_eq_sub_of_withDensity (P + Q) P Q hp hq hP hQ).symm,
    fun ψ hψ h01 => TVFacts.integral_sub_le_tvDist_of_mem_Icc P Q hψ h01⟩

/-! ### T57 -/

theorem bayes_risk_route : Claims.bayes_risk := by
  intro 𝒳 _ P Q _ _
  have h := TVFacts.iInf_bayes_eq P Q
  refine ⟨h, fun Ω _ μ αt δ hμ => ?_⟩
  rw [h]
  have hset : {ω | (1 - αt ω) / 2 < (1 - tvDist P Q) / 2} = {ω | tvDist P Q < αt ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact hμ

/-! ### T52 -/

theorem propensity_core_route : Claims.propensity_core := by
  intro 𝒳 _ P Q _ _ p q π hp hq hp0 hq0 hπ0 hπ1 hP hQ
  have hπ1' : 0 < 1 - π := by linarith
  refine ⟨?_, ?_⟩
  · intro x hρ
    have e1 : π * p x / (π * p x + (1 - π) * q x) / π = p x / (π * p x + (1 - π) * q x) := by
      field_simp
    have e2 : (1 - π * p x / (π * p x + (1 - π) * q x)) / (1 - π) = q x / (π * p x + (1 - π) * q x) := by
      field_simp
      ring
    rw [e1, e2, min_div_div_right hρ.le]
    field_simp
  · set e : 𝒳 → ℝ := fun x => if π * p x + (1 - π) * q x = 0 then 0 else π * p x / (π * p x + (1 - π) * q x)
      with he
    have hρm : Measurable fun x => π * p x + (1 - π) * q x :=
      (measurable_const.mul hp).add (measurable_const.mul hq)
    have hem : Measurable e :=
      Measurable.ite (measurableSet_eq_fun hρm measurable_const) measurable_const
        ((measurable_const.mul hp).div hρm)
    have hpre : {x | q x < p x} = e ⁻¹' Ioi π := by
      ext x
      simp only [Set.mem_ofPred_eq, mem_preimage, mem_Ioi, he]
      by_cases h0 : π * p x + (1 - π) * q x = 0
      · rw [if_pos h0]
        have hpx : p x = 0 := by nlinarith [hp0 x, hq0 x, mul_nonneg hπ0.le (hp0 x), mul_nonneg hπ1'.le (hq0 x)]
        have hqx : q x = 0 := by nlinarith [hp0 x, hq0 x, mul_nonneg hπ0.le (hp0 x), mul_nonneg hπ1'.le (hq0 x)]
        rw [hpx, hqx]
        constructor <;> intro h <;> linarith
      · rw [if_neg h0]
        have hρ : 0 < π * p x + (1 - π) * q x :=
          lt_of_le_of_ne (add_nonneg (mul_nonneg hπ0.le (hp0 x)) (mul_nonneg hπ1'.le (hq0 x))) (Ne.symm h0)
        rw [lt_div_iff₀ hρ]
        constructor
        · intro h
          nlinarith [mul_pos hπ0 (mul_pos hπ1' (sub_pos.2 h))]
        · intro h
          by_contra hc
          push_neg at hc
          nlinarith [mul_nonneg hπ0.le (mul_nonneg hπ1'.le (sub_nonneg.2 hc))]
    have hscheffe := TVFacts.tvDist_eq_sub_of_withDensity (P + Q) P Q hp hq hP hQ
    rw [hpre] at hscheffe
    exact TVFacts.tvDist_map_eq_of_preimage P Q hem measurableSet_Ioi hscheffe.symm

end StatFormal.Wave31tr.RoutePop
