import StatFormal.Archive.Wave15a.Statements
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs
import StatFormal.Archive.TrimmedMMD.Unconditional.Proofs
import StatFormal.Archive.Wave4b.Proofs

/-!
# Route: TM `prop:upper`, `cor:marginderived`, `lem:nullbound` (untrusted)

* `prop:upper`: the paper's proof; with the `sup`-form of `ω⁻¹` neither monotonicity nor continuity is
  needed for the inequality (they are needed only for `omegaInv_spec`, which uses the IVT).
* `cor:marginderived`: the deletion floor `TV(P*,Q*) ≥ (TV(P,Q) − α)/(1 − α)` (the frozen, certified
  `Wave4b.Claims.deletionfloor`, `prop:deletionfloor`), then `rpow` algebra.
* `lem:nullbound`: a common trimming (the frozen `tvintersect`, (⇒)) gives a common point of
  `𝒞_α(P) ∩ 𝒞_α(Q)`; approximate it in both empirical regions within the Hausdorff distances.
-/

noncomputable section
open MeasureTheory Set Metric

namespace StatFormal.Wave15a

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.ZeroSet StatFormal.Distances

/-! ### `prop:upper` -/

theorem omegaInv_nonneg_mem {ω : ℝ → ℝ} {αs u : ℝ} (hαs : 0 ≤ αs) (h0 : ω 0 = 0) (hu : 0 ≤ u) :
    BddAbove {e | e ∈ Icc 0 αs ∧ ω e ≤ u} ∧ (0 : ℝ) ∈ {e | e ∈ Icc 0 αs ∧ ω e ≤ u} :=
  ⟨⟨αs, fun _ he => he.1.2⟩, ⟨⟨le_rfl, hαs⟩, by rw [h0]; exact hu⟩⟩

theorem Dpop_nonneg {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : 𝒳 → H) (P Q : Measure 𝒳) (α : ℝ) : 0 ≤ Dpop φ P Q α :=
  Real.sInf_nonneg (by rintro _ ⟨a, -, b, -, rfl⟩; exact norm_nonneg _)

theorem prop_upper : Claims.prop_upper := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ ω α Dc _ _ hM hα0 _ hD
  obtain ⟨-, -, h0, -, hmar⟩ := hM
  set T := tvDist P Q
  have hT : 0 ≤ T := tvDist_nonneg P Q
  have hDc : 0 ≤ Dc := (Dpop_nonneg φ P Q α).trans hD
  obtain ⟨hbdd, hmem0⟩ := omegaInv_nonneg_mem (ω := ω) hT h0 hDc
  by_cases hαT : T ≤ α
  · have := le_csSup hbdd hmem0
    unfold omegaInv; linarith
  · push Not at hαT
    have he : T - α ∈ Ioc 0 T := ⟨by linarith, by linarith⟩
    have h1 := hmar (T - α) he
    rw [show T - (T - α) = α by ring] at h1
    have hmem : T - α ∈ {e | e ∈ Icc 0 T ∧ ω e ≤ Dc} := ⟨Ioc_subset_Icc_self he, h1.trans hD⟩
    have := le_csSup hbdd hmem
    unfold omegaInv; linarith

theorem omegaInv_spec : Claims.omegaInv_spec := by
  intro ω a ha hmono hcont h0
  constructor
  · intro u hu
    have hsub := intermediate_value_Icc ha hcont
    rw [h0] at hsub
    obtain ⟨e₀, he₀, hωe⟩ := hsub hu
    have hset : {e | e ∈ Icc 0 a ∧ ω e ≤ u} = Icc 0 e₀ := by
      ext e
      simp only [mem_ofPred_eq, mem_Icc]
      constructor
      · rintro ⟨⟨he0, hea⟩, heu⟩
        refine ⟨he0, ?_⟩
        rw [← hωe] at heu
        exact (hmono.le_iff_le ⟨he0, hea⟩ he₀).1 heu
      · rintro ⟨he0, hee⟩
        refine ⟨⟨he0, hee.trans he₀.2⟩, ?_⟩
        rw [← hωe]
        exact (hmono.le_iff_le ⟨he0, hee.trans he₀.2⟩ he₀).2 hee
    have hs : omegaInv ω a u = e₀ := by
      unfold omegaInv; rw [hset]; exact csSup_Icc he₀.1
    rw [hs]; exact ⟨he₀, hωe⟩
  · intro u hu
    have hset : {e | e ∈ Icc 0 a ∧ ω e ≤ u} = Icc 0 a := by
      ext e
      simp only [mem_ofPred_eq]
      refine ⟨fun h => h.1, fun he => ⟨he, ?_⟩⟩
      exact ((hmono.monotoneOn he ⟨ha, le_rfl⟩ he.2)).trans hu
    unfold omegaInv; rw [hset]; exact csSup_Icc ha

/-! ### `cor:marginderived` -/


theorem marginderived : Claims.marginderived := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ α V A L θ gP gQ _ _ hV hA hL hθ hα0 hαT hα1 hgP hgQ hopt hint
  set T := tvDist P Q
  set D := Dpop φ P Q α
  set Ts := tvDist (P.withDensity fun x => ENNReal.ofReal (gP x))
    (Q.withDensity fun x => ENNReal.ofReal (gQ x))
  have hpos : 0 < 1 - α := by linarith
  have hfloor : T ≤ (1 - α) * Ts + α := by
    have h := StatFormal.Wave4b.deletionfloor 𝒳 P Q α gP gQ hα0 hα1 hgP hgQ
    rw [div_le_iff₀ hpos] at h
    linarith
  have hD0 : 0 ≤ D := Dpop_nonneg φ P Q α
  unfold InterpBound at hint
  rw [hopt] at hint
  have hsV : 0 < √V := Real.sqrt_pos.2 hV
  have hLθ : 0 < L ^ (1 - θ) := Real.rpow_pos_of_pos hL _
  have hden : 0 < √V * (1 - α) * L ^ (1 - θ) := by positivity
  set X := 2 * (T - α) / (√V * (1 - α) * L ^ (1 - θ)) with hX
  have hX0 : 0 ≤ X := div_nonneg (by linarith) hden.le
  have hXle : X ≤ (A * D) ^ θ := by
    rw [Real.mul_rpow hA.le hD0, hX, div_le_iff₀ hden]
    have : T - α ≤ (1 - α) * Ts := by linarith
    have h2 : (1 - α) * Ts ≤ (1 - α) * (1 / 2 * √V * A ^ θ * L ^ (1 - θ) * D ^ θ) :=
      mul_le_mul_of_nonneg_left hint hpos.le
    nlinarith
  have hroot : X ^ (1 / θ) ≤ A * D := by
    have h1 := Real.rpow_le_rpow hX0 hXle (by positivity : (0 : ℝ) ≤ 1 / θ)
    rw [one_div] at h1 ⊢
    rw [Real.rpow_rpow_inv (by positivity) hθ.ne'] at h1
    exact h1
  unfold marginLB
  rw [← hX]
  calc 1 / A * X ^ (1 / θ) ≤ 1 / A * (A * D) := mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = D := by field_simp

theorem marginderived_power : Claims.marginderived_power := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ V A L θ hφ hκ hV hA hL hθ hpair
  set T := tvDist P Q
  have hT1 : T ≤ 1 := tvDist_le_one
  have hγ : 0 < 1 / θ := by positivity
  have hsV : 0 < √V := Real.sqrt_pos.2 hV
  have hLθ : 0 < L ^ (1 - θ) := Real.rpow_pos_of_pos hL _
  have hc0 : 0 < marginC0 V A L θ := by unfold marginC0; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hx.1 hxy hγ) hc0
  · exact ((Real.continuous_rpow_const hγ.le).const_smul (marginC0 V A L θ)).continuousOn
  · change marginC0 V A L θ * (0 : ℝ) ^ (1 / θ) = 0
    rw [Real.zero_rpow hγ.ne', mul_zero]
  · intro e he; exact mul_nonneg hc0.le (Real.rpow_nonneg he.1 _)
  · intro e he
    have hα0 : 0 ≤ T - e := by linarith [he.2]
    have hα1 : T - e < 1 := by linarith [he.1]
    obtain ⟨gP, gQ, hgP, hgQ, hopt, hint⟩ := hpair (T - e) hα0 (by linarith [he.1]) hα1
    have key := marginderived 𝒳 H P Q φ κ (T - e) V A L θ gP gQ hφ hκ hV hA hL hθ hα0
      (by linarith [he.1]) hα1 hgP hgQ hopt hint
    refine le_trans ?_ key
    change 1 / A * (2 / (√V * L ^ (1 - θ))) ^ (1 / θ) * e ^ (1 / θ) ≤
      1 / A * (2 * (T - (T - e)) / (√V * (1 - (T - e)) * L ^ (1 - θ))) ^ (1 / θ)
    rw [show T - (T - e) = e by ring, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Real.mul_rpow (by positivity) he.1.le]
    have he0 : 0 < e := he.1
    refine Real.rpow_le_rpow (by positivity) ?_ hγ.le
    have h1e : 0 < 1 - (T - e) := by linarith
    have h1e' : 1 - (T - e) ≤ 1 := by linarith
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 2 * e * (√V * (1 - (T - e)) * L ^ (1 - θ)) ≤ 2 * e * (√V * L ^ (1 - θ)) := by
      have hh : √V * (1 - (T - e)) * L ^ (1 - θ) ≤ √V * L ^ (1 - θ) := by
        have := mul_le_mul_of_nonneg_left h1e' (mul_pos hsV hLθ).le
        nlinarith
      exact mul_le_mul_of_nonneg_left hh (by linarith [he.1])
    linarith

/-! ### `lem:nullbound` -/

theorem nullbound : Claims.nullbound := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ α n m hφ hκ hα0 hα1 hn hm htv x y
  have := isProbabilityMeasure_empirical (by omega : n ≠ 0) x
  have := isProbabilityMeasure_empirical (by omega : m ≠ 0) y
  obtain ⟨gP, gQ, hP, hQ, hR⟩ := exists_common_of_tvDist_le hα1 htv
  have hzP : ∫ x, gP x • φ x ∂P ∈ region φ α P := ⟨gP, hP.1, hP.2.1, hP.2.2, rfl⟩
  have hzQ : ∫ x, gP x • φ x ∂P ∈ region φ α Q := by
    refine ⟨gQ, hQ.1, hQ.2.1, hQ.2.2, ?_⟩
    rw [integral_smul_eq_withDensity P hP.1 (fun x => (hP.2.1 x).1),
      integral_smul_eq_withDensity Q hQ.1 (fun x => (hQ.2.1 x).1), hR]
  set z := ∫ x, gP x • φ x ∂P
  set An := region φ α (empirical x)
  set Bm := region φ α (empirical y)
  have hfA : hausdorffEDist (region φ α P) An ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (region_nonempty P hα0 hα1)
      (region_nonempty _ hα0 hα1) (region_isBounded P hκ) (region_isBounded _ hκ)
  have hfB : hausdorffEDist (region φ α Q) Bm ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (region_nonempty Q hα0 hα1)
      (region_nonempty _ hα0 hα1) (region_isBounded Q hκ) (region_isBounded _ hκ)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have h1 : infDist z An < hausdorffDist (region φ α P) An + ε / 2 :=
    lt_of_le_of_lt (infDist_le_hausdorffDist_of_mem hzP hfA) (by linarith)
  have h2 : infDist z Bm < hausdorffDist (region φ α Q) Bm + ε / 2 :=
    lt_of_le_of_lt (infDist_le_hausdorffDist_of_mem hzQ hfB) (by linarith)
  obtain ⟨a, ha, hda⟩ := (infDist_lt_iff (region_nonempty _ hα0 hα1)).1 h1
  obtain ⟨b, hb, hdb⟩ := (infDist_lt_iff (region_nonempty _ hα0 hα1)).1 h2
  rw [dist_eq_norm] at hda hdb
  have htri : ‖a - b‖ ≤ ‖z - a‖ + ‖z - b‖ := by
    have : a - b = (z - b) - (z - a) := by abel
    rw [this]; exact (norm_sub_le _ _).trans (by linarith)
  have hsd := setDist_le_norm ha hb
  rw [hausdorffDist_comm (s := region φ α P), hausdorffDist_comm (s := region φ α Q)] at *
  unfold Demp
  linarith

end StatFormal.Wave15a
