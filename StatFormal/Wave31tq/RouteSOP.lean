import StatFormal.Wave31tq.Statements
import StatFormal.Wave31tl.Proofs
import StatFormal.Wave30tz.RouteBet

/-!
# Wave 31tq, route S: the "Hence" of Corollary S4.11, the split-sample rate (untrusted proof file)

Q12 `newsobolev_cor_OP` (S4 :628-630, :646-647): under a polynomial margin, for the runs of `same_rate` on a grid of `J` fixed
levels, `α̂ ≥ α⋆ − h − C (n∧m)^{−1/(2γ)}` with probability `≥ 1 − η`. Route (printed): `ε_n = (t_{n,m}(η)/c₀)^{1/γ}` with the
size `t_{n,m} ≤ K_t (n∧m)^{−1/2}` of the certified `Wave31tl.lorate_iii` (batches of `Wave31tl.lorate_batches`, `n∧m ≥ 10`);
then the certified `Wave31tl.lorate_i` at `ε_n` (its hypothesis holds since `J_ε ≤ J`, `Route.Tbet_mono`) bounds
`P(α̂ < a_{ε_n})` by `η`, and the mesh gives `a_{ε_n} ≥ α⋆ − ε_n − h`. When `α⋆ = 0` the bound is trivial (`α̂ ≥ 0`).
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tq.RouteS

open StatFormal.Wave30tq StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.Wave31tl
open scoped StatFormal.Wave30tz.Bet

/-- A strictly increasing grid has a positive lower bound on its consecutive gaps. -/
theorem exists_gapsGe {J : ℕ} {α : Fin J → ℝ} (hα : StrictMono α) : ∃ h0 : ℝ, 0 < h0 ∧ GapsGe α h0 := by
  classical
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ
    exact ⟨1, one_pos, fun j => j.elim0⟩
  set g : Fin J → ℝ := fun j => if hj : j.1 + 1 < J then α ⟨j.1 + 1, hj⟩ - α j else 1 with hg
  have huniv : (Finset.univ : Finset (Fin J)).Nonempty := ⟨⟨0, hJ⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' huniv g, (Finset.lt_inf'_iff huniv).2 fun j _ => ?_, fun j hj => ?_⟩
  · simp only [hg]
    split_ifs with hj
    · exact sub_pos.2 (hα (Fin.mk_lt_mk.2 (Nat.lt_succ_self j.1)))
    · exact one_pos
  · have := Finset.inf'_le g (Finset.mem_univ j)
    have hgj : g j = α ⟨j.1 + 1, hj⟩ - α j := by rw [hg]; simp [hj]
    rw [hgj] at this
    linarith

/-- The rate exponent: `(K/(c₀√M))^{1/γ} = (K/c₀)^{1/γ} M^{−1/(2γ)}`. -/
theorem rate_rpow_eq {K c₀ M γ : ℝ} (hK : 0 ≤ K) (hc₀ : 0 < c₀) (hM : 0 < M) :
    (K / (c₀ * √M)) ^ (1 / γ) = (K / c₀) ^ (1 / γ) * M ^ (-(1 / (2 * γ))) := by
  have e1 : K / (c₀ * √M) = K / c₀ * (M ^ (1 / 2 : ℝ))⁻¹ := by
    rw [Real.sqrt_eq_rpow, div_mul_eq_div_div, div_eq_mul_inv]
  rw [e1, Real.mul_rpow (div_nonneg hK hc₀.le) (inv_nonneg.2 (Real.rpow_nonneg hM.le _)), ← Real.rpow_neg hM.le,
    ← Real.rpow_mul hM.le]
  congr 2
  ring

theorem newsobolev_cor_OP_route : Claims.newsobolev_cor_OP := by
  intro 𝒳 H _ _ _ _ _ φ κ P Q _ _ c₀ γ J δ s2 hφm hφb hPM htv1 hJ hδ0 hδ1 hs20 hs24 η hη0 hη1
  set αs := StatFormal.Distances.tvDist P Q with hαsdef
  have hPM' := hPM
  obtain ⟨hc0, hγ, -⟩ := hPM
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hφb x0)
  have hαs0 : 0 ≤ αs := StatFormal.Distances.tvDist_nonneg P Q
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  set S : ℝ := 1 + Real.log (1 / δ) + Real.log (J / η) with hSdef
  have hL : 0 < Real.log (1 / δ) := by rw [one_div, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  have hlJ : 0 ≤ Real.log (J / η) := Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
  have hS : 0 ≤ S := by linarith
  have hβ : 0 ≤ beta αs := by unfold beta; exact div_nonneg zero_le_one (by linarith)
  set K₀ : ℝ := 1000 * beta αs * κ / s2 * √S with hK₀def
  have hK₀ : 0 ≤ K₀ := by positivity
  set Kt : ℝ := K₀ + 1 with hKtdef
  have hKt : 0 < Kt := by linarith
  set C : ℝ := (Kt / c₀) ^ (1 / γ) with hCdef
  have hC : 0 ≤ C := Real.rpow_nonneg (div_nonneg hKt.le hc0.le) _
  rcases hαs0.eq_or_lt with hα0 | hαpos
  · -- `α⋆ = 0`: the bound is at most `0 ≤ α̂`
    refine ⟨C, 0, fun n m α R h _ hgrid _ _ hmesh => ⟨univ, MeasurableSet.univ, ?_, fun ω _ => ?_⟩⟩
    · rw [measure_univ]; exact ENNReal.ofReal_le_one.2 (by linarith)
    · have hh : 0 ≤ h := Basic.mesh_nonneg α hmesh hαs0
      have hM : 0 ≤ C * ((min n m : ℕ) : ℝ) ^ (-(1 / (2 * γ))) := mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have := Limits.run_alphaLo_nonneg R hgrid δ ω.1 ω.2
      show αs - h - _ ≤ _
      rw [← hα0]; linarith
  -- `α⋆ > 0`
  set n₀ : ℕ := max 10 ⌈(Kt / (c₀ * αs ^ γ)) ^ 2⌉₊ with hn₀
  refine ⟨C, n₀, fun n m α R h hn hgrid hRun hdef hmesh => ?_⟩
  set M : ℝ := ((min n m : ℕ) : ℝ) with hMdef
  have hM10 : 10 ≤ min n m := (le_max_left _ _).trans hn
  have hMpos : 0 < M := by rw [hMdef]; exact_mod_cast lt_of_lt_of_le (by norm_num) hM10
  have hsM : 0 < √M := Real.sqrt_pos.2 hMpos
  set ε : ℝ := (Kt / (c₀ * √M)) ^ (1 / γ) with hεdef
  have hεC : ε = C * M ^ (-(1 / (2 * γ))) := rate_rpow_eq hKt.le hc0 hMpos
  have hbase : 0 < Kt / (c₀ * √M) := by positivity
  have hεpos : 0 < ε := Real.rpow_pos_of_pos hbase _
  have hcε : c₀ * ε ^ γ = Kt / √M := by
    rw [hεdef, one_div, Real.rpow_inv_rpow hbase.le (by linarith)]; field_simp
  have hαγ : 0 < αs ^ γ := Real.rpow_pos_of_pos hαpos γ
  have hεα : ε ≤ αs := by
    have hx : Kt / (c₀ * αs ^ γ) ≤ √M := by
      rw [Real.le_sqrt (by positivity) hMpos.le]
      calc (Kt / (c₀ * αs ^ γ)) ^ 2 ≤ (⌈(Kt / (c₀ * αs ^ γ)) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (n₀ : ℝ) := by exact_mod_cast le_max_right _ _
        _ ≤ M := by rw [hMdef]; exact_mod_cast hn
    have hb : Kt / (c₀ * √M) ≤ αs ^ γ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hx
      nlinarith
    calc ε ≤ (αs ^ γ) ^ (1 / γ) := Real.rpow_le_rpow hbase.le hb (by positivity)
      _ = αs := by rw [one_div, Real.rpow_rpow_inv hαs0 (by linarith)]
  -- the run facts
  obtain ⟨bn1, bn2, bm1, bm2, hcn, hcm, hlx, hly, hN⟩ := hdef
  have hlxe : R.lx = fun i : Fin n => defaultLabel bn1 bn2 i := funext hlx
  have hlye : R.ly = fun j : Fin m => defaultLabel bm1 bm2 j := funext hly
  obtain ⟨hn1', hm1', hr1', hN'⟩ := lorate_batches n m bn1 bn2 bm1 bm2 hM10 hcn hcm
  have hB : ∀ k, R.bat k ≤ 2 := by
    intro k
    obtain ⟨i, hi⟩ := hRun.1.1.1.1 k
    rw [← hRun.1.1.2.2.2.1 k i hi, hlx]
    exact Arith.label_le_two _ _ _
  have hn1 : 1 ≤ fitCard R.lx 1 := by rw [hlxe]; exact hn1'
  have hm1 : 1 ≤ fitCard R.ly 1 := by rw [hlye]; exact hm1'
  have hr1 : rOne R.lx R.ly ≤ 1 := by rw [hlxe, hlye]; exact hr1'.trans (min_le_left _ _)
  have hN1 : 1 ≤ R.N := by
    have hNr : (1 : ℝ) ≤ R.N := by
      rw [hN, hlxe, hlye]
      have : (10 : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast hM10
      linarith
    exact_mod_cast hNr
  obtain ⟨h0, hh0, hgap⟩ := exists_gapsGe hgrid.1
  have hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ 2 * κ := fun x x' =>
    (norm_sub_le _ _).trans (by linarith [hφb x, hφb x'])
  -- the size condition of `lorate_i` at `ε`
  have hiii := (lorate_iii κ (2 * κ) c₀ γ αs s2 δ η J n m bn1 bn2 bm1 bm2 (by linarith) le_rfl hc0 hγ hαs0 htv1
    hs20 hs24 hδ0 hδ1 hη0 hη1 hJ hM10 hcn hcm).1
  have ht : tNM κ (2 * κ) αs s2 δ η (rOne R.lx R.ly) 2 J R.N =
      tNM κ (2 * κ) αs s2 δ η (rOne (fun i : Fin n => defaultLabel bn1 bn2 i) (fun j : Fin m => defaultLabel bm1 bm2 j))
        2 J (defaultPairs (fun i : Fin n => defaultLabel bn1 bn2 i) (fun j : Fin m => defaultLabel bm1 bm2 j)) := by
    rw [hN, hlxe, hlye]
  have hJeps : 0 < Jeps J ε h0 := lt_min (by linarith) (by positivity)
  have hsize : beta αs * max (Tfit κ (2 * κ) η (rOne R.lx R.ly) 2)
      (Tbet (2 * κ) s2 (Real.log (1 / δ)) η (Jeps J ε h0) R.N) ≤ c₀ * ε ^ γ := by
    calc beta αs * max (Tfit κ (2 * κ) η (rOne R.lx R.ly) 2) (Tbet (2 * κ) s2 (Real.log (1 / δ)) η (Jeps J ε h0) R.N)
        ≤ beta αs * max (Tfit κ (2 * κ) η (rOne R.lx R.ly) 2) (Tbet (2 * κ) s2 (Real.log (1 / δ)) η J R.N) :=
          mul_le_mul_of_nonneg_left (max_le_max le_rfl (Route.Tbet_mono (by linarith) hs20 hη0 hJeps
            (min_le_left _ _))) hβ
      _ = tNM κ (2 * κ) αs s2 δ η (rOne R.lx R.ly) 2 J R.N := rfl
      _ ≤ 1000 * beta αs * κ / s2 * √(S / M) := ht ▸ hiii
      _ ≤ Kt / √M := by
          rw [Real.sqrt_div' S hMpos.le, hKtdef, hK₀def, ← mul_div_assoc]
          exact div_le_div_of_nonneg_right (by linarith) hsM.le
      _ = c₀ * ε ^ γ := hcε.symm
  have hbad := lorate_i 𝒳 H φ κ (2 * κ) P Q c₀ γ J n m α δ s2 η h0 ε R 2 hφm hφb hDφ le_rfl hPM' htv1 hgrid hJ
    hδ0 hδ1 hs20 hs24 hRun hB hn1 hm1 hr1 hN1 hη0 hη1 hh0 hgap hεpos hεα hsize
  set Bad : Set ((Fin n → 𝒳) × (Fin m → 𝒳)) := {ω | R.alphaLo α δ ω.1 ω.2 < gridFloor α (αs - ε)} with hBad
  refine ⟨(toMeasurable (sampleLaw P Q n m) Bad)ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
  · refine Route.ofReal_one_sub_le _ (measurableSet_toMeasurable _ _).compl hη0.le ?_
    rw [compl_compl, measure_toMeasurable]; exact hbad
  · have hω' : ω ∉ Bad := fun h => hω (subset_toMeasurable _ _ h)
    simp only [hBad, mem_ofPred_eq, not_lt] at hω'
    have hfl := Basic.floor_ge_of_mesh α hmesh hεpos.le hεα
    show αs - h - C * M ^ (-(1 / (2 * γ))) ≤ _
    rw [← hεC]
    linarith

end StatFormal.Wave31tq.RouteS
