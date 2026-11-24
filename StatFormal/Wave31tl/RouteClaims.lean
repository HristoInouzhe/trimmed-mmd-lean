import StatFormal.Wave31tl.RouteCore

/-!
# Wave 31tl route: Theorem 33 (i), (ii), the paragraph after it and the general margin (untrusted proof material)

* `upper_le`: `P(α̂_lo > α⋆) ≤ δ` and the measurability of `α̂_lo` (the certified `Wave30tz.lo_upper`, `gridBelow α α⋆ ≤ α⋆`).
* `two_sided`: from `P(α̂_lo < ℓ) ≤ η` and the upper side, one measurable event of probability `≥ 1 − δ − η` with
  `ℓ ≤ α̂_lo ≤ α⋆`.
* `lorate_i_route`: `Core.core_lower` with `D⋆ = c₀ε^γ`, `x_j = (α⋆ − α_j)/ε` (`x_j ≤ x_j^γ`, the margin at `εx_j`) and
  `Basic.sum_exp_le_Jeps`.
* `lorate_ii_route`, `lorate_general_route`: `Core.core_lower` with `x_j = 1`, `J′ = J`, `D⋆ = t_{n,m}`, and the mesh bound
  `gridFloor α (α⋆ − e) ≥ α⋆ − e − h`; the case `α⋆ − h − e ≤ 0` is trivial (`α̂_lo ≥ 0`); otherwise `α⋆ > 0`, the margin gives `κ > 0`
  (`D₀ ≤ 2κ`), so `t_{n,m} > 0`.
* `lorate_nologJ_route`: `ε′ ≤ h₀` gives `J_{ε′} ≤ 2(1+1) = 4`, `T_bet` increases in `J′`, and (i) at `ε = ε′`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tl

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.TrimmedMMD.Unconditional

namespace Route

/-! ### Elementary facts -/

lemma ofReal_one_sub_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {S : Set Ω}
    (hS : MeasurableSet S) {a : ℝ} (ha : 0 ≤ a) (h : μ Sᶜ ≤ ENNReal.ofReal a) : ENNReal.ofReal (1 - a) ≤ μ S := by
  rw [← compl_compl S, prob_compl_eq_one_sub hS.compl, ENNReal.ofReal_sub _ ha, ENNReal.ofReal_one]
  exact tsub_le_tsub_left h 1

lemma ofReal_le_inter {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S T : Set Ω} (hT : MeasurableSet T) {a b : ℝ}
    (ha : ENNReal.ofReal a ≤ μ S) (hb : ENNReal.ofReal b ≤ μ T) : ENNReal.ofReal (a + b - 1) ≤ μ (S ∩ T) := by
  have ha' : a ≤ μ.real S := by
    by_cases h : a ≤ 0
    · exact h.trans measureReal_nonneg
    · exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 ha
  have hb' : b ≤ μ.real T := by
    by_cases h : b ≤ 0
    · exact h.trans measureReal_nonneg
    · exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hb
  have hu := measureReal_union_add_inter (μ := μ) (s := S) hT
  have h1 : μ.real (S ∪ T) ≤ 1 := measureReal_le_one
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  change a + b - 1 ≤ μ.real (S ∩ T)
  linarith

lemma Tbet_mono {Dφ s2 L η J1 J2 : ℝ} {N : ℕ} (hDφ : 0 ≤ Dφ) (hs2 : 0 < s2) (hη : 0 < η) (hJ1 : 0 < J1)
    (hJ : J1 ≤ J2) : Tbet Dφ s2 L η J1 N ≤ Tbet Dφ s2 L η J2 N := by
  unfold Tbet
  refine mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (Real.log_le_log (by positivity) (by gcongr))) (by positivity))) (by positivity)

lemma Tfit_pos {κ Dφ η r1 : ℝ} {B : ℕ} (hκ : 0 < κ) (hDφ : 0 ≤ Dφ) (hr1 : 0 < r1) : 0 < Tfit κ Dφ η r1 B := by
  unfold Tfit
  have : 0 < √r1 := Real.sqrt_pos.2 hr1
  positivity

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- `κ > 0` when `α⋆ > 0` under a margin `c₀(α⋆)^γ ≤ D₀` (`D₀ ≤ 2κ`). -/
lemma kappa_pos_of_poly (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ c₀ γ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hm : StatFormal.Wave31ti.PolyMargin φ P Q c₀ γ) (hpos : 0 < StatFormal.Distances.tvDist P Q)
    (h1 : StatFormal.Distances.tvDist P Q < 1) : 0 < κ := by
  obtain ⟨hc0, -, hD⟩ := hm
  have h := hD _ ⟨hpos.le, le_rfl⟩
  rw [sub_self] at h
  have h2 := StatFormal.Wave30tl.Dpop_le_two_kappa P Q (φ := φ) hκ le_rfl (by norm_num : (0 : ℝ) < 1)
  have h3 : 0 < c₀ * StatFormal.Distances.tvDist P Q ^ γ := mul_pos hc0 (Real.rpow_pos_of_pos hpos _)
  linarith

/-- The upper side: `α̂_lo` is measurable and `P(α̂_lo > α⋆) ≤ δ` (`cor:lower`, certified `Wave30tz.lo_upper`). -/
lemma upper_le (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {J n m : ℕ} {α : Fin J → ℝ}
    {δ lmax : ℝ} {R : LoRun 𝒳 J n m} (hgrid : IsGrid α) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hl0 : 0 < lmax) (hl1 : lmax ≤ 1)
    (hadm : R.IsAdmissible α lmax) :
    Measurable (fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => R.alphaLo α δ ω.1 ω.2) ∧
      sampleLaw P Q n m {ω | StatFormal.Distances.tvDist P Q < R.alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal δ := by
  obtain ⟨hmeas, hle, -⟩ := lo_upper_route 𝒳 P Q J n m α δ lmax R hgrid hδ0 hδ1 hl0 hl1 hadm
  refine ⟨hmeas, le_trans (measure_mono fun ω hω => ?_) hle⟩
  simp only [mem_setOf_eq] at hω ⊢
  refine lt_of_le_of_lt ?_ hω
  rcases Limits.gridBelow_spec α (StatFormal.Distances.tvDist P Q) with ⟨j, hj, he⟩ | ⟨-, he⟩
  · rw [he]; exact hj.le
  · rw [he]; exact StatFormal.Distances.tvDist_nonneg P Q

/-- One measurable event of probability `≥ 1 − δ − η` with `ℓ ≤ α̂_lo ≤ α⋆`. -/
lemma two_sided (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {J n m : ℕ} {α : Fin J → ℝ}
    {δ η lmax ℓ : ℝ} {R : LoRun 𝒳 J n m} (hgrid : IsGrid α) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hη0 : 0 ≤ η)
    (hl0 : 0 < lmax) (hl1 : lmax ≤ 1) (hadm : R.IsAdmissible α lmax)
    (hlow : sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < ℓ} ≤ ENNReal.ofReal η) :
    ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
      ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
      E ⊆ {ω | ℓ ≤ R.alphaLo α δ ω.1 ω.2 ∧ R.alphaLo α δ ω.1 ω.2 ≤ StatFormal.Distances.tvDist P Q} := by
  have := Limits.sampleLaw_isProb P Q n m
  obtain ⟨hmeas, hup⟩ := upper_le P Q hgrid hδ0 hδ1 hl0 hl1 hadm
  set S := {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | ℓ ≤ R.alphaLo α δ ω.1 ω.2}
  set T := {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | R.alphaLo α δ ω.1 ω.2 ≤ StatFormal.Distances.tvDist P Q}
  have hSm : MeasurableSet S := measurableSet_le measurable_const hmeas
  have hTm : MeasurableSet T := measurableSet_le hmeas measurable_const
  have hS : ENNReal.ofReal (1 - η) ≤ sampleLaw P Q n m S := by
    refine ofReal_one_sub_le _ hSm hη0 (le_trans (measure_mono fun ω hω => ?_) hlow)
    simp only [S, mem_compl_iff, mem_setOf_eq, not_le] at hω ⊢; exact hω
  have hT : ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m T := by
    refine ofReal_one_sub_le _ hTm hδ0.le (le_trans (measure_mono fun ω hω => ?_) hup)
    simp only [T, mem_compl_iff, mem_setOf_eq, not_le] at hω ⊢; exact hω
  refine ⟨S ∩ T, hSm.inter hTm, ?_, fun ω hω => ⟨hω.1, hω.2⟩⟩
  have h := ofReal_le_inter _ hTm hS hT
  rwa [show 1 - η + (1 - δ) - 1 = 1 - δ - η by ring] at h

/-- The event `{α̂_lo < ℓ}` is empty when `ℓ ≤ 0`. -/
lemma lower_trivial (P Q : Measure 𝒳) {J n m : ℕ} {α : Fin J → ℝ} {δ ℓ η : ℝ} (R : LoRun 𝒳 J n m)
    (hgrid : IsGrid α) (hℓ : ℓ ≤ 0) : sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < ℓ} ≤ ENNReal.ofReal η := by
  have : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | R.alphaLo α δ ω.1 ω.2 < ℓ} = ∅ := by
    ext ω
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
    exact hℓ.trans (Limits.run_alphaLo_nonneg R hgrid δ ω.1 ω.2)
  rw [this, measure_empty]; exact bot_le

/-- The lower side with `x_j = 1`, `J′ = J`: for `e ∈ [0, α⋆]` and `D⋆ = t > 0` below `D_{α_j}` at every level `α_j ≤ α⋆ − e`,
`P(α̂_lo < α⋆ − h − e) ≤ η`. -/
lemma lower_flat (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ Dφ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) (hD2 : Dφ ≤ 2 * κ)
    {J n m : ℕ} {α : Fin J → ℝ} {δ s2 η h e t : ℝ} {R : LoRun 𝒳 J n m} {B : ℕ}
    (hgrid : IsGrid α) (hJ : 1 ≤ J) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hs20 : 0 < s2) (hs24 : s2 ≤ 4)
    (hRun : R.IsWitnessRun φ α δ (1 / 2) s2) (hB : ∀ k, R.bat k ≤ B)
    (hn1 : 1 ≤ fitCard R.lx 1) (hm1 : 1 ≤ fitCard R.ly 1) (hr1 : rOne R.lx R.ly ≤ 1) (hN : 1 ≤ R.N)
    (hη0 : 0 < η) (hη1 : η < 1) (hαs1 : StatFormal.Distances.tvDist P Q < 1)
    (hmesh : MeshBelowLe α (StatFormal.Distances.tvDist P Q) h)
    (he0 : 0 ≤ e) (heα : e ≤ StatFormal.Distances.tvDist P Q) (ht : 0 < t)
    (htdef : t = tNM κ Dφ (StatFormal.Distances.tvDist P Q) s2 δ η (rOne R.lx R.ly) B J R.N)
    (hD : ∀ j, α j ≤ StatFormal.Distances.tvDist P Q - e → t ≤ Dpop φ P Q (α j)) :
    sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < StatFormal.Distances.tvDist P Q - h - e} ≤ ENNReal.ofReal η := by
  classical
  set αs := StatFormal.Distances.tvDist P Q
  have hβ0 : 0 ≤ beta αs := by
    unfold beta
    have : 0 < 1 - αs := by linarith
    positivity
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hfitc : beta αs * Tfit κ Dφ η (rOne R.lx R.ly) B ≤ t := by
    rw [htdef]; unfold tNM; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hβ0
  have hbetc : beta αs * Tbet Dφ s2 (Real.log (1 / δ)) η (J : ℝ) R.N ≤ t := by
    rw [htdef]; unfold tNM; exact mul_le_mul_of_nonneg_left (le_max_right _ _) hβ0
  have hsum : ∀ A : ℝ, Real.log (2 * (J : ℝ) / η) ≤ A →
      ∑ j ∈ Finset.univ.filter (fun j => α j ≤ αs - e), Real.exp (-(A * (fun _ : Fin J => (1 : ℝ)) j ^ 2)) ≤
        (J : ℝ) * Real.exp (-A) := by
    intro A _
    simp only [one_pow, mul_one]
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have hcore := Core.core_lower P Q hφ hκ hDφ hD2 hgrid hδ0 hδ1 hs20 hs24 hRun hB hn1 hm1 hr1 hN hη0 hη1
    (αs := αs) (a := αs - e) (Ds := t) (J' := (J : ℝ)) (fun _ => 1) hαs1 (by linarith) ht
    (fun j hj => ⟨le_rfl, by rw [mul_one]; exact hD j hj⟩) hJr hfitc hbetc hsum
  refine le_trans (measure_mono fun ω hω => ?_) hcore
  simp only [mem_setOf_eq] at hω ⊢
  have := Basic.floor_ge_of_mesh α hmesh he0 heα
  linarith

end Route

open Route

/-- **Theorem 33 (i)**. -/
theorem lorate_i_route : Claims.lorate_i := by
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ c₀ γ J n m α δ s2 η h0 ε R B hφ hκ hDφ hD2 hm hαs1 hgrid hJ hδ0 hδ1 hs20 hs24
    hRun hB hn1 hm1 hr1 hN hη0 hη1 hh0 hgap hε hεα hcond
  classical
  set αs := StatFormal.Distances.tvDist P Q
  obtain ⟨hc0, hγ, hmarg⟩ := hm
  have hβ0 : 0 ≤ beta αs := by
    unfold beta
    have : 0 < 1 - αs := by linarith
    positivity
  have hJeps : 1 ≤ Jeps J ε h0 := by
    unfold Jeps
    refine le_min (by exact_mod_cast hJ) ?_
    have : 0 ≤ ε / h0 := by positivity
    linarith
  refine Core.core_lower P Q hφ hκ hDφ hD2 hgrid hδ0 hδ1 hs20 hs24 hRun hB hn1 hm1 hr1 hN hη0 hη1
    (αs := αs) (a := αs - ε) (Ds := c₀ * ε ^ γ) (J' := Jeps J ε h0) (fun j => (αs - α j) / ε) hαs1 (by linarith)
    (mul_pos hc0 (Real.rpow_pos_of_pos hε _)) ?_ hJeps
    ((mul_le_mul_of_nonneg_left (le_max_left _ _) hβ0).trans hcond)
    ((mul_le_mul_of_nonneg_left (le_max_right _ _) hβ0).trans hcond) ?_
  · intro j hj
    have hαj0 : 0 ≤ α j := (hgrid.2 j).1
    have hx1 : 1 ≤ (αs - α j) / ε := by rw [le_div_iff₀ hε]; linarith
    refine ⟨hx1, ?_⟩
    have hmj := hmarg (αs - α j) ⟨by linarith, by linarith⟩
    rw [sub_sub_cancel] at hmj
    refine le_trans ?_ hmj
    have hxx : (αs - α j) / ε ≤ ((αs - α j) / ε) ^ γ := by
      calc (αs - α j) / ε = ((αs - α j) / ε) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ((αs - α j) / ε) ^ γ := Real.rpow_le_rpow_of_exponent_le hx1 hγ
    have he : ε ^ γ * ((αs - α j) / ε) ^ γ = (αs - α j) ^ γ := by
      rw [← Real.mul_rpow hε.le (by positivity)]; congr 1; field_simp
    calc c₀ * ε ^ γ * ((αs - α j) / ε) ≤ c₀ * ε ^ γ * ((αs - α j) / ε) ^ γ :=
          mul_le_mul_of_nonneg_left hxx (mul_pos hc0 (Real.rpow_pos_of_pos hε _)).le
      _ = c₀ * (αs - α j) ^ γ := by rw [mul_assoc, he]
  · intro A hA
    have hA2 : Real.log 2 ≤ A := le_trans (Real.log_le_log (by norm_num) (by
      rw [le_div_iff₀ hη0]; nlinarith)) hA
    exact Basic.sum_exp_le_Jeps hgap hh0 hε hA2

/-- **Theorem 33 (ii)**. -/
theorem lorate_ii_route : Claims.lorate_ii := by
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ c₀ γ J n m α δ s2 η h R B hφ hκ hDφ hD2 hm hαs1 hgrid hJ hδ0 hδ1 hs20 hs24
    hRun hB hn1 hm1 hr1 hN hη0 hη1 hmesh
  set αs := StatFormal.Distances.tvDist P Q with hαsdef
  set t := tNM κ Dφ αs s2 δ η (rOne R.lx R.ly) B J R.N with htdef
  set e := (t / c₀) ^ (1 / γ) with hedef
  refine two_sided P Q hgrid hδ0 hδ1 hη0.le (by norm_num) (by norm_num) hRun.1 ?_
  by_cases hlow : αs - h - e ≤ 0
  · exact lower_trivial P Q R hgrid hlow
  push_neg at hlow
  have hm' := hm
  obtain ⟨hc0, hγ, hmarg⟩ := hm
  have hαs0 : 0 ≤ αs := StatFormal.Distances.tvDist_nonneg P Q
  have hh0 : 0 ≤ h := Basic.mesh_nonneg α hmesh hαs0
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hDφ0 : 0 ≤ Dφ := by simpa using hDφ x0 x0
  have hn1r : (0 : ℝ) < fitCard R.lx 1 := by exact_mod_cast hn1
  have hm1r : (0 : ℝ) < fitCard R.ly 1 := by exact_mod_cast hm1
  have hr10 : 0 < rOne R.lx R.ly := by unfold rOne; positivity
  have hβ1 : 1 ≤ beta αs := Core.one_le_beta' hαs0 hαs1
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
  have hTfit0 : 0 ≤ Tfit κ Dφ η (rOne R.lx R.ly) B := by unfold Tfit; positivity
  have ht0 : 0 ≤ t := by rw [htdef]; unfold tNM; exact mul_nonneg (by linarith) (hTfit0.trans (le_max_left _ _))
  have he0 : 0 ≤ e := Real.rpow_nonneg (div_nonneg ht0 hc0.le) _
  have hαs : 0 < αs := by linarith
  have hκpos := kappa_pos_of_poly P Q hκ hm' hαs hαs1
  have htpos : 0 < t := by
    rw [htdef]; unfold tNM
    exact mul_pos (by linarith) (lt_of_lt_of_le (Tfit_pos hκpos hDφ0 hr10) (le_max_left _ _))
  have hte : c₀ * e ^ γ = t := by
    rw [hedef, one_div, Real.rpow_inv_rpow (div_nonneg htpos.le hc0.le) (by linarith)]; field_simp
  refine lower_flat P Q hφ hκ hDφ hD2 hgrid hJ hδ0 hδ1 hs20 hs24 hRun hB hn1 hm1 hr1 hN hη0 hη1 hαs1 hmesh he0
    (by linarith) htpos htdef ?_
  intro j hj
  have hαj0 : 0 ≤ α j := (hgrid.2 j).1
  have hmj := hmarg (αs - α j) ⟨by linarith, by linarith⟩
  rw [sub_sub_cancel] at hmj
  refine le_trans ?_ hmj
  rw [← hte]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow he0 (by linarith) (by linarith)) hc0.le

/-- **The paragraph after the proof of Theorem 33**: a general margin. -/
theorem lorate_general_route : Claims.lorate_general := by
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ ω J n m α δ s2 η h e R B hφ hκ hDφ hD2 hm hαs1 hgrid hJ hδ0 hδ1 hs20 hs24
    hRun hB hn1 hm1 hr1 hN hη0 hη1 hmesh he hωe
  set αs := StatFormal.Distances.tvDist P Q with hαsdef
  refine two_sided P Q hgrid hδ0 hδ1 hη0.le (by norm_num) (by norm_num) hRun.1 ?_
  by_cases hlow : αs - h - e ≤ 0
  · exact lower_trivial P Q R hgrid hlow
  push_neg at hlow
  obtain ⟨hmono, -, hω0, -, hωD⟩ := hm
  have hαs0 : 0 ≤ αs := StatFormal.Distances.tvDist_nonneg P Q
  have hh0 : 0 ≤ h := Basic.mesh_nonneg α hmesh hαs0
  have hαs : 0 < αs := by linarith [he.1]
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hDφ0 : 0 ≤ Dφ := by simpa using hDφ x0 x0
  have hn1r : (0 : ℝ) < fitCard R.lx 1 := by exact_mod_cast hn1
  have hm1r : (0 : ℝ) < fitCard R.ly 1 := by exact_mod_cast hm1
  have hr10 : 0 < rOne R.lx R.ly := by unfold rOne; positivity
  have hβ1 : 1 ≤ beta αs := Core.one_le_beta' hαs0 hαs1
  -- `κ > 0`: `ω(α⋆) > ω(0) = 0` and `ω(α⋆) ≤ D₀ ≤ 2κ`
  have hκpos : 0 < κ := by
    have h1 : ω 0 < ω αs := hmono ⟨le_rfl, hαs0⟩ ⟨hαs0, le_rfl⟩ hαs
    have h2 := hωD αs ⟨hαs0, le_rfl⟩
    rw [sub_self] at h2
    have h3 := StatFormal.Wave30tl.Dpop_le_two_kappa P Q (φ := φ) hκ le_rfl (by norm_num : (0 : ℝ) < 1)
    linarith
  set t := tNM κ Dφ αs s2 δ η (rOne R.lx R.ly) B J R.N with htdef
  have htpos : 0 < t := by
    rw [htdef]; unfold tNM
    exact mul_pos (by linarith) (lt_of_lt_of_le (Tfit_pos hκpos hDφ0 hr10) (le_max_left _ _))
  refine lower_flat P Q hφ hκ hDφ hD2 hgrid hJ hδ0 hδ1 hs20 hs24 hRun hB hn1 hm1 hr1 hN hη0 hη1 hαs1 hmesh he.1
    he.2 htpos htdef ?_
  intro j hj
  have hαj0 : 0 ≤ α j := (hgrid.2 j).1
  rw [← hωe]
  refine (hωD e he).trans ?_
  exact dpop_antitone 𝒳 H φ κ P Q (α j) (αs - e) hφ hκ hαj0 hj (by linarith [he.1])

/-- **The paragraph after Theorem 33**: no `log J` when the grid is not finer than the rate. -/
theorem lorate_nologJ_route : Claims.lorate_nologJ := by
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ c₀ γ J n m α δ s2 η h0 h R B hφ hκ hDφ hD2 hm hαs1 hgrid hJ hδ0 hδ1 hs20 hs24
    hRun hB hn1 hm1 hr1 hN hη0 hη1 hh0 hgap hmesh he'
  set αs := StatFormal.Distances.tvDist P Q with hαsdef
  set t' := beta αs * max (Tfit κ Dφ η (rOne R.lx R.ly) B) (Tbet Dφ s2 (Real.log (1 / δ)) η 4 R.N) with ht'def
  set e := (t' / c₀) ^ (1 / γ) with hedef
  have hJe : Jeps J e h0 ≤ 4 := by
    unfold Jeps
    refine (min_le_right _ _).trans ?_
    have : e / h0 ≤ 1 := div_le_one_of_le₀ he' hh0.le
    linarith
  refine ⟨hJe, two_sided P Q hgrid hδ0 hδ1 hη0.le (by norm_num) (by norm_num) hRun.1 ?_⟩
  by_cases hlow : αs - h - e ≤ 0
  · exact lower_trivial P Q R hgrid hlow
  push_neg at hlow
  have hm' := hm
  obtain ⟨hc0, hγ, hmarg⟩ := hm
  have hαs0 : 0 ≤ αs := StatFormal.Distances.tvDist_nonneg P Q
  have hmh : 0 ≤ h := Basic.mesh_nonneg α hmesh hαs0
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hDφ0 : 0 ≤ Dφ := by simpa using hDφ x0 x0
  have hn1r : (0 : ℝ) < fitCard R.lx 1 := by exact_mod_cast hn1
  have hm1r : (0 : ℝ) < fitCard R.ly 1 := by exact_mod_cast hm1
  have hr10 : 0 < rOne R.lx R.ly := by unfold rOne; positivity
  have hβ1 : 1 ≤ beta αs := Core.one_le_beta' hαs0 hαs1
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
  have hTfit0 : 0 ≤ Tfit κ Dφ η (rOne R.lx R.ly) B := by unfold Tfit; positivity
  have ht'0 : 0 ≤ t' := by rw [ht'def]; exact mul_nonneg (by linarith) (hTfit0.trans (le_max_left _ _))
  have he0 : 0 ≤ e := Real.rpow_nonneg (div_nonneg ht'0 hc0.le) _
  have hαs : 0 < αs := by linarith
  have hκpos := kappa_pos_of_poly P Q hκ hm' hαs hαs1
  have ht'pos : 0 < t' := mul_pos (by linarith) (lt_of_lt_of_le (Tfit_pos hκpos hDφ0 hr10) (le_max_left _ _))
  have hepos : 0 < e := Real.rpow_pos_of_pos (div_pos ht'pos hc0) _
  have hte : c₀ * e ^ γ = t' := by
    rw [hedef, one_div, Real.rpow_inv_rpow (div_nonneg ht'pos.le hc0.le) (by linarith)]; field_simp
  have hJe1 : 1 ≤ Jeps J e h0 := by
    unfold Jeps
    refine le_min (by exact_mod_cast hJ) ?_
    have : 0 ≤ e / h0 := by positivity
    linarith
  have hi := lorate_i_route 𝒳 H φ κ Dφ P Q c₀ γ J n m α δ s2 η h0 e R B hφ hκ hDφ hD2 hm' hαs1 hgrid hJ hδ0 hδ1
    hs20 hs24 hRun hB hn1 hm1 hr1 hN hη0 hη1 hh0 hgap hepos (by linarith) (by
      rw [hte, ht'def]
      refine mul_le_mul_of_nonneg_left (max_le_max le_rfl (Tbet_mono hDφ0 hs20 hη0 (by linarith) hJe))
        (by linarith))
  refine le_trans (measure_mono fun ω hω => ?_) hi
  simp only [mem_setOf_eq] at hω ⊢
  have := Basic.floor_ge_of_mesh α hmesh hepos.le (by linarith)
  linarith

end StatFormal.Wave31tl
