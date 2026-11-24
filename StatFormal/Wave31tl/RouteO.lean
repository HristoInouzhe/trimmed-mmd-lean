import StatFormal.Wave31tl.RouteArith

/-!
# Wave 31tl route: the display after Proposition 12 and "the same rate" (untrusted proof material)

* `lorate_O_route`: for `n∧m ≥ 10`, Theorem 33 (ii) (`lorate_ii_route`, with `Δ_φ = 2κ` and `B = 2`, every pair lying in batch 1 or
  2 of the default labels) and (iii) (`lorate_iii_route`, `lorate_batches_route`); for `n∧m ≤ 9`, the bound term is `≥ α⋆`
  (`c₀(α⋆)^γ ≤ D₀ ≤ 2κ`, the base `≥ 1000κ/(12c₀) ≥ (α⋆)^γ`), so the lower inequality is trivial, and the upper side is `cor:lower`.
* `same_rate_route`: `(K√(S/M))^{1/γ} = (K√S)^{1/γ} M^{-1/(2γ)}`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tl

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.TrimmedMMD.Unconditional
open Route

/-- **The display after Proposition 12** (Theorem 33 (ii) + (iii)). -/
theorem lorate_O_route : Claims.lorate_O := by
  intro 𝒳 H _ _ _ _ _ φ κ P Q _ _ c₀ γ J n m α δ s2 η h R hφ hκ hm hαs1 hgrid hJ hδ0 hδ1 hs20 hs24 hRun hdef hn
    hm1 hη0 hη1 hmesh
  set αs := StatFormal.Distances.tvDist P Q with hαsdef
  set S := 1 + Real.log (1 / δ) + Real.log (J / η) with hSdef
  set M : ℝ := ((min n m : ℕ) : ℝ) with hMdef
  set K := 1000 * κ / (c₀ * (1 - αs) * s2) with hKdef
  set e := (K * √(S / M)) ^ (1 / γ) with hedef
  have hm' := hm
  obtain ⟨hc0, hγ, hmarg⟩ := hm
  have hαs0 : 0 ≤ αs := StatFormal.Distances.tvDist_nonneg P Q
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
  have hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ 2 * κ := fun x x' => (norm_sub_le _ _).trans (by linarith [hκ x, hκ x'])
  by_cases hM : 10 ≤ min n m
  · obtain ⟨bn1, bn2, bm1, bm2, hcn, hcm, hlx, hly, hN⟩ := hdef
    have hlxe : R.lx = fun i : Fin n => defaultLabel bn1 bn2 i := funext hlx
    have hlye : R.ly = fun j : Fin m => defaultLabel bm1 bm2 j := funext hly
    obtain ⟨hn1', hm1', hr1', hN'⟩ := lorate_batches_route n m bn1 bn2 bm1 bm2 hM hcn hcm
    have hB : ∀ k, R.bat k ≤ 2 := by
      intro k
      obtain ⟨i, hi⟩ := hRun.1.1.1.1 k
      rw [← hRun.1.1.2.2.2.1 k i hi, hlx]
      exact Arith.label_le_two _ _ _
    have hn1 : 1 ≤ fitCard R.lx 1 := by rw [hlxe]; exact hn1'
    have hm1'' : 1 ≤ fitCard R.ly 1 := by rw [hlye]; exact hm1'
    have hr1 : rOne R.lx R.ly ≤ 1 := by rw [hlxe, hlye]; exact hr1'.trans (min_le_left _ _)
    have hNr : (1 : ℝ) ≤ R.N := by
      rw [hN, hlxe, hlye]
      have : (10 : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast hM
      linarith
    have hN1 : 1 ≤ R.N := by exact_mod_cast hNr
    obtain ⟨E, hEm, hEp, hE⟩ := lorate_ii_route 𝒳 H φ κ (2 * κ) P Q c₀ γ J n m α δ s2 η h R 2 hφ hκ hDφ le_rfl hm'
      hαs1 hgrid hJ hδ0 hδ1 hs20 hs24 hRun hB hn1 hm1'' hr1 hN1 hη0 hη1 hmesh
    have hiii := (lorate_iii_route κ (2 * κ) c₀ γ αs s2 δ η J n m bn1 bn2 bm1 bm2 (by linarith) le_rfl hc0 hγ hαs0
      hαs1 hs20 hs24 hδ0 hδ1 hη0 hη1 hJ hM hcn hcm).2
    have ht : tNM κ (2 * κ) αs s2 δ η (rOne R.lx R.ly) 2 J R.N =
        tNM κ (2 * κ) αs s2 δ η (rOne (fun i : Fin n => defaultLabel bn1 bn2 i) (fun j : Fin m => defaultLabel bm1 bm2 j)) 2 J
          (defaultPairs (fun i : Fin n => defaultLabel bn1 bn2 i) (fun j : Fin m => defaultLabel bm1 bm2 j)) := by
      rw [hN, hlxe, hlye]
    refine ⟨E, hEm, hEp, fun ω hω => ⟨?_, (hE hω).2⟩⟩
    have h1 := (hE hω).1
    rw [ht] at h1
    show _ ≤ _
    linarith
  · -- `n∧m ≤ 9`: the lower inequality is trivial
    push_neg at hM
    refine two_sided P Q hgrid hδ0 hδ1 hη0.le (by norm_num) (by norm_num) hRun.1 (lower_trivial P Q R hgrid ?_)
    have hh0 : 0 ≤ h := Basic.mesh_nonneg α hmesh hαs0
    suffices hea : αs ≤ e by linarith
    have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast le_min hn hm1
    have hM9 : M ≤ 9 := by rw [hMdef]; exact_mod_cast Nat.lt_succ_iff.1 hM
    have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have hL : 0 < Real.log (1 / δ) := by rw [one_div, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
    have hℓ0 : 0 ≤ Real.log (J / η) := Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
    have hS1 : 1 ≤ S := by linarith
    have h1α : 0 < 1 - αs := by linarith
    have hK0 : 0 ≤ K := by rw [hKdef]; positivity
    have hX0 : 0 ≤ K * √(S / M) := mul_nonneg hK0 (Real.sqrt_nonneg _)
    rcases hαs0.lt_or_eq with hαs | hαs
    · have hκpos := kappa_pos_of_poly P Q hκ hm' hαs hαs1
      have hmα := hmarg αs ⟨hαs0, le_rfl⟩
      rw [sub_self] at hmα
      have hD0 := StatFormal.Wave30tl.Dpop_le_two_kappa P Q (φ := φ) hκ le_rfl (by norm_num : (0 : ℝ) < 1)
      have hpow : c₀ * αs ^ γ ≤ 2 * κ := hmα.trans hD0
      have hsq : 1 / 3 ≤ √(S / M) := by
        rw [show (1 / 3 : ℝ) = √(1 / 9) by rw [show (1 / 9 : ℝ) = (1 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith)
      have hK : 1000 * κ / (4 * c₀) ≤ K := by
        rw [hKdef]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have : (1 - αs) * s2 ≤ 4 := by nlinarith
        nlinarith
      have hX : αs ^ γ ≤ K * √(S / M) := by
        have h1 : 1000 * κ / (4 * c₀) * (1 / 3) ≤ K * √(S / M) :=
          mul_le_mul hK hsq (by norm_num) hK0
        have h2 : αs ^ γ ≤ 1000 * κ / (4 * c₀) * (1 / 3) := by
          rw [show 1000 * κ / (4 * c₀) * (1 / 3) = 250 * κ / (3 * c₀) by ring, le_div_iff₀ (by positivity)]
          have : 0 ≤ αs ^ γ := Real.rpow_nonneg hαs0 _
          nlinarith
        linarith
      calc αs = (αs ^ γ) ^ (1 / γ) := by
            rw [one_div, Real.rpow_rpow_inv hαs0 (by linarith)]
        _ ≤ e := Real.rpow_le_rpow (Real.rpow_nonneg hαs0 _) hX (by positivity)
    · rw [← hαs]; exact Real.rpow_nonneg hX0 _

/-- **The sentence after Theorem 8**: the same rate `(n∧m)^{-1/(2γ)}`. -/
theorem same_rate_route : Claims.same_rate := by
  intro 𝒳 H _ _ _ _ _ φ κ P Q _ _ c₀ γ J δ s2 η hφ hκ hm hαs1 hJ hδ0 hδ1 hs20 hs24 hη0 hη1
  set αs := StatFormal.Distances.tvDist P Q with hαsdef
  set S := 1 + Real.log (1 / δ) + Real.log (J / η) with hSdef
  set K := 1000 * κ / (c₀ * (1 - αs) * s2) with hKdef
  have hm' := hm
  obtain ⟨hc0, hγ, -⟩ := hm
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
  have h1α : 0 < 1 - αs := by linarith
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hKS : 0 ≤ K * √S := mul_nonneg hK0 (Real.sqrt_nonneg _)
  refine ⟨(K * √S) ^ (1 / γ), Real.rpow_nonneg hKS _, ?_⟩
  intro n m α R h hgrid hRun hdef hn hm1 hmesh
  obtain ⟨E, hEm, hEp, hE⟩ := lorate_O_route 𝒳 H φ κ P Q c₀ γ J n m α δ s2 η h R hφ hκ hm' hαs1 hgrid hJ hδ0 hδ1
    hs20 hs24 hRun hdef hn hm1 hη0 hη1 hmesh
  refine ⟨E, hEm, hEp, fun ω hω => ⟨?_, (hE hω).2⟩⟩
  have h1 := (hE hω).1
  set M : ℝ := ((min n m : ℕ) : ℝ) with hMdef
  have hM : 0 < M := by rw [hMdef]; exact_mod_cast lt_of_lt_of_le zero_lt_one (le_min hn hm1)
  have hrw : (K * √(S / M)) ^ (1 / γ) = (K * √S) ^ (1 / γ) * M ^ (-(1 / (2 * γ))) := by
    have e1 : K * √(S / M) = K * √S * (M ^ (1 / 2 : ℝ))⁻¹ := by
      rw [Real.sqrt_div' S hM.le, Real.sqrt_eq_rpow M, div_eq_mul_inv, mul_assoc]
    have hM12 : 0 ≤ (M ^ (1 / 2 : ℝ))⁻¹ := inv_nonneg.2 (Real.rpow_nonneg hM.le _)
    rw [e1, Real.mul_rpow hKS hM12, ← Real.rpow_neg hM.le, ← Real.rpow_mul hM.le]
    congr 2
    field_simp
  rw [hrw] at h1
  show _ ≤ _
  linarith

end StatFormal.Wave31tl
