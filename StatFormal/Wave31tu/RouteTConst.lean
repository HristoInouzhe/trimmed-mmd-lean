import StatFormal.Wave31tu.RouteTFit

/-!
# Wave 31tu route T: Theorem S4.19 in the uniform form (G) (S4 :989-1018, proof :1346-1381; untrusted proof material)

* `kappa0_pos`, `cV_pos`: `κ₀, c_V > 0`.
* `piK_scale`: the tail mass `π_K` of the data rescaled by `1/σ` is `(P+Q)({|z − x₀| > σK})`.
* `const_core`: the structure of the proof — given the conclusion of Proposition S4.27 for the rescaled data at every level
  `α⋆ − e`, `e ≥ ε`, on the events of Lemma S4.23 with the common `x`, and `κ₀ε/2 ≥ T_bet(J)`, `P(α̂ < α⋆ − Δ − ε) ≤ η`
  (`lower_of_fits` with `fit_transfer`, and the mesh: `a_ε ≥ α⋆ − ε − Δ`).
* `laplace_const_i_of`: case (i) with `x = log(16(n∨m+1)²/η)`, `K = max{1, 1/σ, C′log(n∨m)/σ}` (so `σK ≥ max{1, C′log(n∨m)}`),
  `π_K ≤ C′/((c⋆r⋆)(n∨m))` (Claim Y8), `ε = C·Z`, `Z = {(log(n∨m))^{1/4}L^{1/2} + v_min^{−2}(…)}/√(n∧m)`,
  `C = √5K₀^{1/4}(1 + coefI) + 80/κ₀`; if `C·Z ≥ α⋆` the bound is trivial, else `u ≤ √5K₀^{1/4}·Z < 1`, `ε_fit ≤ coefI·u ≤ ε` and
  `T_bet ≤ 40Z ≤ κ₀ε/2`.
* `laplace_const_ii_of`: case (ii), the same with `π_K ≤ C′/(n∨m)` from the `(P+Q)` tail, `ε_fit ≤ coefII·u^{8/9}` and
  `u^{8/9} ≤ (5K₀^{1/2})^{4/9}{(log(n∨m))^{1/2}L/(n∧m)}^{4/9}`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tu.RouteT

open StatFormal.Wave30tq StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.Wave31tl StatFormal.LaplaceRate

lemma kappa0_pos {αs c₁ c₂ ε₀ : ℝ} (hαs0 : 0 < αs) (hαs1 : αs < 1) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hε₀ : 0 < ε₀) :
    0 < kappa0 αs c₁ c₂ ε₀ := by
  have h1 : 0 < 1 - αs := by linarith
  unfold kappa0 rho0
  refine lt_min ?_ ?_
  · exact div_pos (mul_pos h1 hc₁) (mul_pos (Real.rpow_pos_of_pos two_pos _) hc₂)
  · exact div_pos (mul_pos (mul_pos h1 hc₁) (Real.rpow_pos_of_pos (by positivity) _)) (by positivity)

lemma cV_pos {αs c₁ ε₀ : ℝ} (hαs0 : 0 < αs) (hαs1 : αs < 1) (hc₁ : 0 < c₁) (hε₀ : 0 < ε₀) : 0 < cV αs c₁ ε₀ := by
  have h1 : 0 < 1 - αs := by linarith
  unfold cV
  exact mul_pos (mul_pos h1 hc₁) (Real.rpow_pos_of_pos (div_pos hε₀ hαs0) _)

/-- The tail mass of the rescaled data: `π_K(P∘(·/σ)⁻¹, Q∘(·/σ)⁻¹, x₀/σ) = (P+Q)({|z − x₀| > σK})`. -/
lemma piK_scale {σ : ℝ} (hσ : 0 < σ) (P Q : Measure ℝ) (x₀ K : ℝ) :
    piK (P.map fun z => z / σ) (Q.map fun z => z / σ) (x₀ / σ) K = (P + Q).real {z | σ * K < |z - x₀|} := by
  have hmeas : Measurable fun z : ℝ => z / σ := measurable_id.div_const σ
  have hS : MeasurableSet {z : ℝ | K < |z - x₀ / σ|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hpre : (fun z : ℝ => z / σ) ⁻¹' {z | K < |z - x₀ / σ|} = {z | σ * K < |z - x₀|} := by
    ext z
    simp only [mem_preimage, mem_setOf_eq]
    rw [show z / σ - x₀ / σ = (z - x₀) / σ by ring, abs_div, abs_of_pos hσ, lt_div_iff₀ hσ, mul_comm]
  unfold piK
  simp only [Measure.real, Measure.add_apply, Measure.map_apply hmeas hS, hpre]

/-- `e^{−σK/C′} ≤ 1/M` when `σK ≥ C′ log M`, `M > 0`. -/
lemma exp_tail_le {σK C' M : ℝ} (hC' : 0 < C') (hM : 0 < M) (h : C' * Real.log M ≤ σK) :
    Real.exp (-σK / C') ≤ 1 / M := by
  have h1 : Real.log M ≤ σK / C' := by rw [le_div_iff₀ hC']; linarith
  calc Real.exp (-σK / C') ≤ Real.exp (-Real.log M) := Real.exp_le_exp.2 (by rw [neg_div]; linarith)
    _ = 1 / M := by rw [Real.exp_neg, Real.exp_log hM, one_div]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- **The structure of the proof of Theorem S4.19**: good rescaled fits at every level `α⋆ − e`, `e ≥ ε`, and `κε/2 ≥ T_bet(J)`
give `P(α̂ < α⋆ − Δ − ε) ≤ η`. -/
lemma const_core (h4 : Claims.lap_intervals) (h10 : Claims.lap_clip) (h16 : Claims.lap_bets) (h17 : Claims.lap_rescale)
    {σ : ℝ} (hσ : 0 < σ) (φ : ℝ → H) (hφ : IsLaplaceFeature σ φ)
    (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [NullSingletonClass P] [NullSingletonClass Q]
    {J n m : ℕ} {α : Fin J → ℝ} {δ s2 η h ε κ c : ℝ} {R : LoRun ℝ J n m}
    (hgrid : IsGrid α) (hα0 : ∀ j, 0 < α j) (hJ : 1 ≤ J) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hs20 : 0 < s2) (hs24 : s2 ≤ 4)
    (hη0 : 0 < η) (hη1 : η < 1) (hrun : IsGenuineRun R φ α δ (1 / 2) s2) (hdef : IsDefaultRun R)
    (hN10 : 10 ≤ min n m) (hc : Real.log (16 * (((max n m : ℕ) : ℝ) + 1) ^ 2 / η) ≤ c) (hε : 0 < ε)
    (hεα : ε ≤ Distances.tvDist P Q) (hmesh : MeshBelowLe α (Distances.tvDist P Q) h)
    (hTbet : Tbet (1 / 2) s2 (Real.log (1 / δ)) η J R.N ≤ κ * ε / 2)
    (hfit : ∀ (n' m' : ℕ) (xs : Fin n' → ℝ) (ys : Fin m' → ℝ), ((min n m : ℕ) : ℝ) / 5 ≤ n' →
      ((min n m : ℕ) : ℝ) / 5 ≤ m' → IntervalEvent (P.map fun z => z / σ) xs c →
      IntervalEvent (Q.map fun z => z / σ) ys c → (∀ i j, xs i ≠ ys j) →
      ∀ e, ε ≤ e → e < Distances.tvDist P Q →
      ∀ w v, IsQPMin (fun u => φ (σ * u)) (Distances.tvDist P Q - e) xs ys w v →
        ∀ t u, GenuineCuts (fun u => φ (σ * u)) xs ys w v (Distances.tvDist P Q - e) t u →
          u < t ∧ κ * e / 2 ≤ (∫ z, ramp (fitF (fun u => φ (σ * u)) xs ys w v) t u z ∂(P.map fun z => z / σ)) -
            (∫ z, ramp (fitF (fun u => φ (σ * u)) xs ys w v) t u z ∂(Q.map fun z => z / σ)) -
              (Distances.tvDist P Q - e)) :
    sampleLaw P Q n m {z | R.alphaLo α δ z.1 z.2 < Distances.tvDist P Q - h - ε} ≤ ENNReal.ofReal η := by
  have hlow := lower_of_fits h4 h10 h16 hσ φ hφ P Q hgrid hα0 hJ hδ0 hδ1 hs20 hs24 hη0 hη1 hrun hdef hN10 hc hε hTbet
    (fun n' m' xs ys hn hm hevX hevY hxy e he1 he2 w v hqp t u hcuts =>
      fit_transfer h17 hσ φ hφ P Q xs ys _ _
        (fun w' v' hqp' t' u' hcuts' => hfit n' m' _ _ hn hm (intervalEvent_scale hσ P xs hevX)
          (intervalEvent_scale hσ Q ys hevY) (fun i j hij => hxy i j ((div_left_inj' hσ.ne').1 hij)) e he1 he2
          w' v' hqp' t' u' hcuts') w v hqp t u hcuts)
  refine le_trans (measure_mono fun z hz => ?_) hlow
  simp only [mem_setOf_eq] at hz ⊢
  have := Basic.floor_ge_of_mesh α hmesh hε.le hεα
  linarith

/-- The common numerical setting of both cases. -/
lemma setting_facts {n m : ℕ} {η : ℝ} (hN10 : 10 ≤ min n m) (hη0 : 0 < η) (hη1 : η < 1) :
    (10 : ℝ) ≤ ((min n m : ℕ) : ℝ) ∧ ((min n m : ℕ) : ℝ) ≤ ((max n m : ℕ) : ℝ) ∧ 10 ≤ ((max n m : ℕ) : ℝ) ∧
      1 ≤ Real.log ((max n m : ℕ) : ℝ) ∧ Real.log ((max n m : ℕ) : ℝ) ≤ Real.log (((max n m : ℕ) : ℝ) / η) ∧
      Real.log 8 ≤ Real.log (16 * (((max n m : ℕ) : ℝ) + 1) ^ 2 / η) := by
  have hN : (10 : ℝ) ≤ ((min n m : ℕ) : ℝ) := by exact_mod_cast hN10
  have hMN : ((min n m : ℕ) : ℝ) ≤ ((max n m : ℕ) : ℝ) := by exact_mod_cast min_le_max
  have hM : (10 : ℝ) ≤ ((max n m : ℕ) : ℝ) := hN.trans hMN
  refine ⟨hN, hMN, hM, one_le_log_of_ten_le hM, Real.log_le_log (by linarith) ?_, Real.log_le_log (by norm_num) ?_⟩
  · rw [le_div_iff₀ hη0]; nlinarith
  · rw [le_div_iff₀ hη0]; nlinarith

/-- **Theorem S4.19 (i)**, uniform form (G). -/
theorem laplace_const_i_of (h4 : Claims.lap_intervals) (h8 : Claims.condR_facts) (h10 : Claims.lap_clip)
    (h15 : Claims.lap_fitted) (h16 : Claims.lap_bets) (h17 : Claims.lap_rescale) : Claims.laplace_const_i := by
  intro σ αs c₁ c₂ ε₀ C' cs rs pbar hσ hαs0 hαs1 hc₁ hc₁₂ hε₀ hε₀α hC' hcs hrs0 hrs1 hpbar
  have hκ : 0 < kappa0 αs c₁ c₂ ε₀ := kappa0_pos hαs0 hαs1 hc₁ (hc₁.trans_le hc₁₂) hε₀
  have hcv : 0 < cV αs c₁ ε₀ := cV_pos hαs0 hαs1 hc₁ hε₀
  have hrs' : 0 < min 1 (rs / σ) := lt_min one_pos (div_pos hrs0 hσ)
  have hcr' : 0 < cs * σ * min 1 (rs / σ) := by positivity
  set K₀ := max 1 (max (1 / σ) (C' / σ)) with hK₀def
  have hK₀ : 1 ≤ K₀ := le_max_left _ _
  set C₃ := √5 * K₀ ^ (1 / 4 : ℝ) with hC₃def
  have hC₃ : 0 < C₃ := by positivity
  set Ci := coefI (kappa0 αs c₁ c₂ ε₀) (cV αs c₁ ε₀) (lapA0 (σ * pbar) (cs * σ) (min 1 (rs / σ)))
    (lapA1 (σ * pbar) (cs * σ) (min 1 (rs / σ))) (C' / (cs * rs)) with hCidef
  have hCi : 0 ≤ Ci := coefI_nonneg hκ hcv (lapA0_nonneg hcr') (lapA1_nonneg (by positivity) hcr') (by positivity)
  set A := C₃ + Ci * C₃ + 80 / kappa0 αs c₁ c₂ ε₀ with hAdef
  have hA : 0 < A := by positivity
  refine ⟨A, hA, ?_⟩
  intro H _ _ _ _ φ P Q _ _ p q x₀ ℓ₀ J n m α δ s2 η h R hφ hcross hpx hexp htv htwo hcond hpb hgrid hα0 hJ hδ0 hδ1
    hs20 hs24 hη0 hη1 hrun hdef hN10 hmesh
  subst htv
  haveI := nullSingleton_of_density hcross.2.2.2.2.1
  haveI := nullSingleton_of_density hcross.2.2.2.2.2.1
  obtain ⟨hN, hMN, hM, hlM, hLlM, hlog8⟩ := setting_facts hN10 hη0 hη1
  obtain ⟨hc5, hc2⟩ := x_facts hM hη0 hη1.le
  set N := ((min n m : ℕ) : ℝ) with hNdef
  set M := ((max n m : ℕ) : ℝ) with hMdef
  set lM := Real.log M with hlMdef
  set L := Real.log (M / η) with hLdef
  set c := Real.log (16 * (M + 1) ^ 2 / η) with hcdef
  set K := max 1 (max (1 / σ) (C' * lM / σ)) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKK : K ≤ K₀ * lM := K_le hσ hlM
  have hN0 : 0 < N := by linarith
  have hsN : 0 < √N := Real.sqrt_pos.2 hN0
  set X := lM ^ (1 / 4 : ℝ) * L ^ (1 / 2 : ℝ) with hXdef
  set Y := s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) with hYdef
  have hX0 : 0 < X := mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos (by linarith) _)
  have hY0 : 0 ≤ Y := by positivity
  have hu : K ^ (1 / 4 : ℝ) * √(c / N) ≤ C₃ * (X / √N) :=
    u_le (by linarith) hKK (by linarith) (by linarith) (by linarith) hc5 hN0
  refine Route.two_sided P Q hgrid hδ0 hδ1 hη0.le (by norm_num) (by norm_num) hrun.1 ?_
  by_cases htriv : Distances.tvDist P Q ≤ A * (X + Y) / √N
  · apply Route.lower_trivial P Q R hgrid
    have hh := Basic.mesh_nonneg α hmesh (Distances.tvDist_nonneg P Q)
    linarith
  push_neg at htriv
  have hε0 : 0 < A * (X + Y) / √N := by positivity
  have hC₃A : C₃ ≤ A := by
    have := div_pos (by norm_num : (0 : ℝ) < 80) hκ
    have := mul_nonneg hCi hC₃.le
    rw [hAdef]; linarith
  have hXA : A * (X / √N) ≤ A * (X + Y) / √N := by
    calc A * (X / √N) ≤ A * ((X + Y) / √N) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hsN.le) hA.le
      _ = A * (X + Y) / √N := by ring
  have hCX : C₃ * (X / √N) ≤ A * (X + Y) / √N :=
    (mul_le_mul_of_nonneg_right hC₃A (by positivity)).trans hXA
  have hu1 : K ^ (1 / 4 : ℝ) * √(c / N) ≤ 1 := by linarith
  obtain ⟨-, -, hNp⟩ := default_batches R hdef hrun.1.1 hN10
  refine const_core h4 h10 h16 h17 hσ φ hφ P Q hgrid hα0 hJ hδ0 hδ1 hs20 hs24 hη0 hη1 hrun hdef hN10 le_rfl hε0
    htriv.le hmesh (κ := kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀) ?_ ?_
  · -- the bets: `T_bet(J) ≤ 40Y/√N ≤ κ₀ε/2`
    have hT := Tbet_le (L := Real.log (1 / δ)) hs20 hs24 hη0 (J' := J) (J := J) (by exact_mod_cast hJ) le_rfl hN0 hNp
    refine hT.trans ?_
    have h80 : 80 / kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ ≤ A := by
      have := mul_nonneg hCi hC₃.le
      rw [hAdef]; linarith
    have e : kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ * (A * (X + Y) / √N) / 2 =
        (kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ * A) * (X + Y) / (2 * √N) := by ring
    rw [e, div_le_div_iff₀ hsN (by positivity)]
    have hκA : 80 ≤ kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ * A := by
      rw [div_le_iff₀ hκ] at h80; linarith
    have h1 : 80 * (Y * √N) ≤ (kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ * A) * (Y * √N) :=
      mul_le_mul_of_nonneg_right hκA (by positivity)
    have h2 : 0 ≤ (kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ * A) * (X * √N) := by positivity
    linarith
  · -- the fits: Proposition S4.27 (a) for the rescaled data (Claim Y15), Claim Y17 for the rescaled hypotheses
    intro n' m' xs ys hn hm hevX hevY hxy e he1 he2 w v hqp t u hcuts
    obtain ⟨hφ₁, -, hb⟩ := h17 H σ φ hσ hφ
    obtain ⟨hcross₁, htv₁, hD₁, -, -, hcond₁, hpb₁, -⟩ := hb P Q p q x₀ ℓ₀ C' rs cs pbar hcross
    have hpx₁ : 0 < σ * p (σ * (x₀ / σ)) := by rw [mul_div_cancel₀ _ hσ.ne']; exact mul_pos hσ hpx
    have htwo₁ : TwoSided54 (fun u => φ (σ * u)) (P.map fun x => x / σ) (Q.map fun x => x / σ) c₁ c₂ ε₀ := by
      unfold TwoSided54 at htwo ⊢
      rw [htv₁]; simp only [hD₁]; exact htwo
    have hn1 : 1 ≤ n' := by
      have : (1 : ℝ) ≤ n' := by linarith
      exact_mod_cast this
    have hm1 : 1 ≤ m' := by
      have : (1 : ℝ) ≤ m' := by linarith
      exact_mod_cast this
    have hσK : σ * K ≥ max 1 (C' * lM) := by
      have h1 : 1 / σ ≤ K := (le_max_left _ _).trans (le_max_right _ _)
      have h2 : C' * lM / σ ≤ K := (le_max_right _ _).trans (le_max_right _ _)
      refine max_le ?_ ?_
      · rw [div_le_iff₀ hσ] at h1; linarith
      · rw [div_le_iff₀ hσ] at h2; linarith
    have hpi : piK (P.map fun z => z / σ) (Q.map fun z => z / σ) (x₀ / σ) K ≤ C' / (cs * rs) / N := by
      rw [piK_scale hσ]
      have htail := (((h8 P Q p q x₀ ℓ₀ hcross hpx).2 rs cs hcond).2.2.2.2 C' hexp).1 (σ * K)
        (by linarith [le_max_left 1 (C' * lM)])
      have h1 : (P + Q).real {z | σ * K < |z - x₀|} ≤ C' * Real.exp (-(σ * K) / C') / (cs * rs) :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) htail
      have h2 : Real.exp (-(σ * K) / C') ≤ 1 / M :=
        exp_tail_le hC' (by linarith) (by linarith [le_max_right 1 (C' * lM)])
      have h3 : 1 / M ≤ 1 / N := one_div_le_one_div_of_le hN0 hMN
      calc (P + Q).real {z | σ * K < |z - x₀|} ≤ C' * Real.exp (-(σ * K) / C') / (cs * rs) := h1
        _ ≤ C' * (1 / N) / (cs * rs) := by gcongr; exact h2.trans h3
        _ = C' / (cs * rs) / N := by ring
    have heps := epsFitI_le (P.map fun z => z / σ) (Q.map fun z => z / σ) (x₀ := x₀ / σ) (pbar := σ * pbar)
      (cs := cs * σ) (rs := min 1 (rs / σ)) (n' := n') (m' := m') hκ hcv (by positivity) hcr' (by positivity)
      (by linarith) hn hm hc2 hK1 hu1 hpi
    have heps' : epsFitI (kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀) (cV (Distances.tvDist P Q) c₁ ε₀)
        (devA (P.map fun z => z / σ) (Q.map fun z => z / σ) (x₀ / σ) K (σ * pbar) (cs * σ) (min 1 (rs / σ)) c n' m')
        (devG (σ * pbar) (cs * σ) (min 1 (rs / σ)) K c n' m') (devB K c n' m') (min n' m') ≤ e := by
      refine heps.trans (le_trans ?_ he1)
      refine (mul_le_mul_of_nonneg_left hu (by positivity)).trans ?_
      rw [← mul_assoc]
      have hCiA : Ci * C₃ ≤ A := by
        have := div_pos (by norm_num : (0 : ℝ) < 80) hκ
        rw [hAdef]; linarith
      exact (mul_le_mul_of_nonneg_right hCiA (by positivity)).trans hXA
    have hY15 := h15 H (fun u => φ (σ * u)) (P.map fun x => x / σ) (Q.map fun x => x / σ) (fun u => σ * p (σ * u))
      (fun u => σ * q (σ * u)) (x₀ / σ) (σ ^ 2 * ℓ₀) c₁ c₂ ε₀ c K n' m' xs ys hφ₁ hcross₁ hpx₁ htwo₁
      (by rw [htv₁]; exact hαs1) hn1 hm1 hxy (by linarith) hK1 hevX hevY
    have hY := (hY15.1 (min 1 (rs / σ)) (cs * σ) (σ * pbar) (hcond₁ hcond) (hpb₁ hpb) e (by rw [htv₁]; exact heps')
      (by rw [htv₁]; exact he2) w v (by rw [htv₁]; exact hqp)).1 t u (by rw [htv₁]; exact hcuts)
    rw [htv₁] at hY
    exact hY

/-- **Theorem S4.19 (ii)**, uniform form (G). -/
theorem laplace_const_ii_of (h4 : Claims.lap_intervals) (h10 : Claims.lap_clip) (h15 : Claims.lap_fitted)
    (h16 : Claims.lap_bets) (h17 : Claims.lap_rescale) : Claims.laplace_const_ii := by
  intro σ αs c₁ c₂ ε₀ C' hσ hαs0 hαs1 hc₁ hc₁₂ hε₀ hε₀α hC'
  have hκ : 0 < kappa0 αs c₁ c₂ ε₀ := kappa0_pos hαs0 hαs1 hc₁ (hc₁.trans_le hc₁₂) hε₀
  have hcv : 0 < cV αs c₁ ε₀ := cV_pos hαs0 hαs1 hc₁ hε₀
  set K₀ := max 1 (max (1 / σ) (C' / σ)) with hK₀def
  have hK₀ : 1 ≤ K₀ := le_max_left _ _
  set D₃ := (5 * K₀ ^ (1 / 2 : ℝ)) ^ (4 / 9 : ℝ) with hD₃def
  have hD₃ : 0 < D₃ := by positivity
  set Ci := coefII (kappa0 αs c₁ c₂ ε₀) (cV αs c₁ ε₀) C' with hCidef
  have hCi : 0 ≤ Ci := coefII_nonneg hκ hcv hC'.le
  set A := D₃ + Ci * D₃ + 80 / kappa0 αs c₁ c₂ ε₀ with hAdef
  have hA : 0 < A := by positivity
  refine ⟨A, hA, ?_⟩
  intro H _ _ _ _ φ P Q _ _ p q x₀ ℓ₀ J n m α δ s2 η h R hφ hcross hpx hsum htv htwo hgrid hα0 hJ hδ0 hδ1
    hs20 hs24 hη0 hη1 hrun hdef hN10 hmesh
  subst htv
  haveI := nullSingleton_of_density hcross.2.2.2.2.1
  haveI := nullSingleton_of_density hcross.2.2.2.2.2.1
  obtain ⟨hN, hMN, hM, hlM, hLlM, hlog8⟩ := setting_facts hN10 hη0 hη1
  obtain ⟨hc5, hc2⟩ := x_facts hM hη0 hη1.le
  set N := ((min n m : ℕ) : ℝ) with hNdef
  set M := ((max n m : ℕ) : ℝ) with hMdef
  set lM := Real.log M with hlMdef
  set L := Real.log (M / η) with hLdef
  set c := Real.log (16 * (M + 1) ^ 2 / η) with hcdef
  set K := max 1 (max (1 / σ) (C' * lM / σ)) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKK : K ≤ K₀ * lM := K_le hσ hlM
  have hN0 : 0 < N := by linarith
  have hsN : 0 < √N := Real.sqrt_pos.2 hN0
  set X := (lM ^ (1 / 2 : ℝ) * L / N) ^ (4 / 9 : ℝ) with hXdef
  set Y := s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) with hYdef
  have hX0 : 0 < X := Real.rpow_pos_of_pos (div_pos (mul_pos (Real.rpow_pos_of_pos (by linarith) _) (by linarith)) hN0) _
  have hY0 : 0 ≤ Y := by positivity
  have hu : (K ^ (1 / 4 : ℝ) * √(c / N)) ^ (8 / 9 : ℝ) ≤ D₃ * X :=
    u_pow_le (by linarith) hKK (by linarith) (by linarith) (by linarith) hc5 hN0
  refine Route.two_sided P Q hgrid hδ0 hδ1 hη0.le (by norm_num) (by norm_num) hrun.1 ?_
  by_cases htriv : Distances.tvDist P Q ≤ A * (X + Y / √N)
  · apply Route.lower_trivial P Q R hgrid
    have hh := Basic.mesh_nonneg α hmesh (Distances.tvDist_nonneg P Q)
    linarith
  push_neg at htriv
  have hε0 : 0 < A * (X + Y / √N) := by positivity
  have hYN0 : 0 ≤ Y / √N := by positivity
  have hXA : A * X ≤ A * (X + Y / √N) := mul_le_mul_of_nonneg_left (by linarith) hA.le
  have hD₃A : D₃ ≤ A := by
    have := div_pos (by norm_num : (0 : ℝ) < 80) hκ
    have := mul_nonneg hCi hD₃.le
    rw [hAdef]; linarith
  have hDX : D₃ * X ≤ A * (X + Y / √N) := (mul_le_mul_of_nonneg_right hD₃A hX0.le).trans hXA
  have hu0 : 0 ≤ K ^ (1 / 4 : ℝ) * √(c / N) := by positivity
  have hu1 : K ^ (1 / 4 : ℝ) * √(c / N) ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have := Real.one_lt_rpow hcon (by norm_num : (0 : ℝ) < 8 / 9)
    linarith
  obtain ⟨-, -, hNp⟩ := default_batches R hdef hrun.1.1 hN10
  refine const_core h4 h10 h16 h17 hσ φ hφ P Q hgrid hα0 hJ hδ0 hδ1 hs20 hs24 hη0 hη1 hrun hdef hN10 le_rfl hε0
    htriv.le hmesh (κ := kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀) ?_ ?_
  · -- the bets: `T_bet(J) ≤ 40Y/√N ≤ κ₀ε/2`
    have hT := Tbet_le (L := Real.log (1 / δ)) hs20 hs24 hη0 (J' := J) (J := J) (by exact_mod_cast hJ) le_rfl hN0 hNp
    refine hT.trans ?_
    have h80 : 80 / kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ ≤ A := by
      have := mul_nonneg hCi hD₃.le
      rw [hAdef]; linarith
    have hκA : 80 ≤ kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ * A := by
      rw [div_le_iff₀ hκ] at h80; linarith
    have hYN : 0 ≤ Y / √N := by positivity
    have e1 : 40 * Y / √N = 40 * (Y / √N) := by ring
    have e2 : kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ * (A * (X + Y / √N)) / 2 =
        (kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ * A) * (X + Y / √N) / 2 := by ring
    rw [e1, e2]
    have h1 : 80 * (Y / √N) ≤ (kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ * A) * (Y / √N) :=
      mul_le_mul_of_nonneg_right hκA hYN
    have h2 : 0 ≤ (kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀ * A) * X := by positivity
    linarith
  · -- the fits: Proposition S4.27 (b) for the rescaled data (Claim Y15), Claim Y17 for the rescaled hypotheses
    intro n' m' xs ys hn hm hevX hevY hxy e he1 he2 w v hqp t u hcuts
    obtain ⟨hφ₁, -, hb⟩ := h17 H σ φ hσ hφ
    obtain ⟨hcross₁, htv₁, hD₁, -, -, -, -, -⟩ := hb P Q p q x₀ ℓ₀ C' 1 1 0 hcross
    have hpx₁ : 0 < σ * p (σ * (x₀ / σ)) := by rw [mul_div_cancel₀ _ hσ.ne']; exact mul_pos hσ hpx
    have htwo₁ : TwoSided54 (fun u => φ (σ * u)) (P.map fun x => x / σ) (Q.map fun x => x / σ) c₁ c₂ ε₀ := by
      unfold TwoSided54 at htwo ⊢
      rw [htv₁]; simp only [hD₁]; exact htwo
    have hn1 : 1 ≤ n' := by
      have : (1 : ℝ) ≤ n' := by linarith
      exact_mod_cast this
    have hm1 : 1 ≤ m' := by
      have : (1 : ℝ) ≤ m' := by linarith
      exact_mod_cast this
    have hσK : C' * lM ≤ σ * K := by
      have h2 : C' * lM / σ ≤ K := (le_max_right _ _).trans (le_max_right _ _)
      rw [div_le_iff₀ hσ] at h2; linarith
    have hpi : piK (P.map fun z => z / σ) (Q.map fun z => z / σ) (x₀ / σ) K ≤ C' / N := by
      rw [piK_scale hσ]
      have htail := hsum.2 (σ * K) (by positivity)
      have h1 : (P + Q).real {z | σ * K < |z - x₀|} ≤ C' * Real.exp (-(σ * K) / C') :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) htail
      have h2 : Real.exp (-(σ * K) / C') ≤ 1 / M := exp_tail_le hC' (by linarith) hσK
      have h3 : 1 / M ≤ 1 / N := one_div_le_one_div_of_le hN0 hMN
      calc (P + Q).real {z | σ * K < |z - x₀|} ≤ C' * Real.exp (-(σ * K) / C') := h1
        _ ≤ C' * (1 / N) := by gcongr; exact h2.trans h3
        _ = C' / N := by ring
    have heps := epsFitII_le (P.map fun z => z / σ) (Q.map fun z => z / σ) (x₀ := x₀ / σ) (n' := n') (m' := m')
      hκ hcv hC'.le (by linarith) hn hm hc2 hK1 hu1 hpi
    have heps' : epsFitII (kappa0 (Distances.tvDist P Q) c₁ c₂ ε₀) (cV (Distances.tvDist P Q) c₁ ε₀)
        (devA' (P.map fun z => z / σ) (Q.map fun z => z / σ) (x₀ / σ) K c n' m') (devG' K c n' m') (devB K c n' m')
        (min n' m') ≤ e := by
      refine heps.trans (le_trans ?_ he1)
      refine (mul_le_mul_of_nonneg_left hu hCi).trans ?_
      rw [← mul_assoc]
      have hCiA : Ci * D₃ ≤ A := by
        have := div_pos (by norm_num : (0 : ℝ) < 80) hκ
        rw [hAdef]; linarith
      exact (mul_le_mul_of_nonneg_right hCiA hX0.le).trans hXA
    have hY15 := h15 H (fun u => φ (σ * u)) (P.map fun x => x / σ) (Q.map fun x => x / σ) (fun u => σ * p (σ * u))
      (fun u => σ * q (σ * u)) (x₀ / σ) (σ ^ 2 * ℓ₀) c₁ c₂ ε₀ c K n' m' xs ys hφ₁ hcross₁ hpx₁ htwo₁
      (by rw [htv₁]; exact hαs1) hn1 hm1 hxy (by linarith) hK1 hevX hevY
    have hY := hY15.2 e (by rw [htv₁]; exact heps') (by rw [htv₁]; exact he2) w v (by rw [htv₁]; exact hqp) t u
      (by rw [htv₁]; exact hcuts)
    rw [htv₁] at hY
    exact hY

end StatFormal.Wave31tu.RouteT
