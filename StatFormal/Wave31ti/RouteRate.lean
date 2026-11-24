import StatFormal.Wave31ti.Statements
import StatFormal.Wave30tu.Proofs
import StatFormal.Wave30tu.Full.Route
import StatFormal.Wave30tr.RouteConst
import StatFormal.Wave30tr.RouteEvents
import StatFormal.Wave31tf.Proofs

set_option linter.style.longLine false

/-!
# Route: wave 31ti, the polynomial margin, `thm:rate` (v3) and the linear pair (untrusted)

* `poly_is_general`: `ω(ε) = c₀ε^γ` is strictly increasing (`rpow`, `γ > 0`) and continuous with `ω(0) = 0`, and for
  `0 ≤ t ≤ c₀(α⋆)^γ`, `ε = (t/c₀)^{1/γ} ∈ [0,α⋆]` with `c₀ε^γ = t` (`rpow_inv_rpow`, `rpow_rpow_inv`).
* `rate_v3`: the certified `Wave30tu.rate` at that `ω` and `ε` (`t ≥ 0` since `τ, τ^A ≥ 0` on `[0,1)`), which gives
  `α⋆ − ε ≤ α̂ ≤ α⋆`, hence `|α̂ − α⋆| ≤ ε`; the constant 24 is the second half of the certified `Wave30tu.rate_poly` (`γ > 0`).
* `rate_v3_full`: the certified `Wave30tu.Full.rate_full` likewise; `τ_{n,m} ≤ τ^A_{n,m}` (certified `tauFull_threshold`),
  `s ≤ 2/(n∧m)`, `e_k ≤ k^{-1/2}` (certified `Wave30tr.ek_le`) and `D ≤ 2κ` give the printed bound; Cauchy–Schwarz,
  `(A + x + y)² ≤ (A² + 2)(1 + x² + y²)` with `A = 2√2 + 4`, `A² + 2 ≤ 49`, gives the constant `2 · 7 = 14`.
* `linear_poly`: the certified `Wave31tf.linear_margin` (`ω(ε) = 3ε/2`).
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave31ti

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tu

theorem poly_is_general : Claims.poly_is_general := by
  intro 𝒳 H _ _ _ P Q _ _ φ c₀ γ ⟨hc, hγ, hb⟩
  set a := StatFormal.Distances.tvDist P Q with ha
  have ha0 : 0 ≤ a := StatFormal.Distances.tvDist_nonneg P Q
  have hγ0 : 0 < γ := by linarith
  refine ⟨⟨fun x hx y hy hxy => mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hx.1 hxy hγ0) hc,
    continuousOn_const.mul (continuousOn_id.rpow_const fun _ _ => Or.inr hγ0.le),
    by simp [Real.zero_rpow hγ0.ne'], fun e he => mul_nonneg hc.le (Real.rpow_nonneg he.1 _), hb⟩, ?_⟩
  intro t ht0 ht
  have htc : 0 ≤ t / c₀ := div_nonneg ht0 hc.le
  have hle : t / c₀ ≤ a ^ γ := by rw [div_le_iff₀ hc]; linarith
  refine ⟨⟨Real.rpow_nonneg htc _, ?_⟩, ?_⟩
  · calc (t / c₀) ^ (1 / γ) ≤ (a ^ γ) ^ (1 / γ) :=
          Real.rpow_le_rpow htc hle (by positivity)
      _ = a := by rw [one_div, Real.rpow_rpow_inv ha0 hγ0.ne']
  · rw [one_div, Real.rpow_inv_rpow htc hγ0.ne']; field_simp

theorem rate_v3 : Claims.rate_v3 := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ δ' c₀ γ τ τA n m hφ hκ h1 hpm hδ hδ1 hδ' hδ'1 hn hm hτ hτA ht
  set a := StatFormal.Distances.tvDist P Q with ha
  have ha0 : 0 ≤ a := StatFormal.Distances.tvDist_nonneg P Q
  have ht0 : 0 ≤ τ a + τA a := add_nonneg (hτ.1 a ⟨ha0, h1⟩) (hτA.1 a ⟨ha0, h1⟩)
  obtain ⟨hmar, hsol⟩ := poly_is_general 𝒳 H P Q φ c₀ γ hpm
  obtain ⟨hε, hωε⟩ := hsol _ ht0 ht
  obtain ⟨E, hE, hPE, hsub⟩ := StatFormal.Wave30tu.rate 𝒳 H P Q φ κ δ δ' τ τA (fun e => c₀ * e ^ γ) n m _ hφ hκ h1
    hmar hδ hδ1 hδ' hδ'1 hn hm hτ hτA hε hωε
  refine ⟨⟨E, hE, hPE, fun z hz => ?_⟩, ?_⟩
  · obtain ⟨hlo, hhi⟩ := hsub hz
    exact ⟨hhi, abs_sub_le_iff.2 ⟨by linarith, by linarith⟩⟩
  · exact (StatFormal.Wave30tu.rate_poly 𝒳 H P Q φ κ δ δ' c₀ γ τ τA n m hφ hκ h1 hpm.1 (by linarith [hpm.2.1])
      hpm.2.2 hδ hδ1 hδ' hδ'1 hn hm hτ hτA ht).2

/-- The printed bound on `τ^A_{n,m}(α,δ)` for `Δ_φ ≤ 2κ`. -/
lemma tauA_le_printed {κ D α δ : ℝ} {n m : ℕ} (hκ0 : 0 ≤ κ) (hD0 : 0 ≤ D) (hD : D ≤ 2 * κ) (hα : α < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    StatFormal.Wave30tr.tauA κ D α δ n m ≤
      2 * κ / (1 - α) * (√2 + 2 + √(Real.log (1 / δ))) / √((min n m : ℕ) : ℝ) := by
  set k : ℕ := min n m with hkdef
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast le_min hn hm
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast min_le_left n m
  have hkm : (k : ℝ) ≤ m := by exact_mod_cast min_le_right n m
  have hk0 : (0 : ℝ) < k := by linarith
  have hsk : 0 < √(k : ℝ) := Real.sqrt_pos.2 hk0
  have hL : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  set L := Real.log (1 / δ)
  have hs : StatFormal.Wave30tp.sNM n m ≤ 2 / k := by
    simp only [StatFormal.Wave30tp.sNM]
    have h1 : 1 / (n : ℝ) ≤ 1 / k := one_div_le_one_div_of_le hk0 hkn
    have h2 : 1 / (m : ℝ) ≤ 1 / k := one_div_le_one_div_of_le hk0 hkm
    have h3 : (2 : ℝ) / k = 1 / k + 1 / k := by ring
    rw [h3]; exact add_le_add h1 h2
  have hs0 : 0 ≤ StatFormal.Wave30tp.sNM n m := by simp only [StatFormal.Wave30tp.sNM]; positivity
  have hsq : √(StatFormal.Wave30tp.sNM n m) ≤ √2 / √(k : ℝ) := by
    rw [← Real.sqrt_div (by norm_num)]; exact Real.sqrt_le_sqrt hs
  have hen : StatFormal.Wave30tr.ek n ≤ 1 / √(k : ℝ) :=
    (StatFormal.Wave30tr.ek_le n hn).trans (one_div_le_one_div_of_le hsk (Real.sqrt_le_sqrt hkn))
  have hem : StatFormal.Wave30tr.ek m ≤ 1 / √(k : ℝ) :=
    (StatFormal.Wave30tr.ek_le m hm).trans (one_div_le_one_div_of_le hsk (Real.sqrt_le_sqrt hkm))
  have hlog : √(StatFormal.Wave30tp.sNM n m * L / 2) ≤ √L / √(k : ℝ) := by
    rw [← Real.sqrt_div hL]
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ (by norm_num) hk0]
    have hsk2 : StatFormal.Wave30tp.sNM n m * k ≤ 2 := by
      have := mul_le_mul_of_nonneg_right hs hk0.le
      rwa [div_mul_cancel₀ _ hk0.ne'] at this
    nlinarith [mul_le_mul_of_nonneg_left hsk2 hL]
  have hinner : 2 * κ * √(StatFormal.Wave30tp.sNM n m) + 2 * κ * (StatFormal.Wave30tr.ek n + StatFormal.Wave30tr.ek m) +
      D * √(StatFormal.Wave30tp.sNM n m * L / 2) ≤
      2 * κ * (√2 / √(k : ℝ)) + 2 * κ * (1 / √(k : ℝ) + 1 / √(k : ℝ)) + 2 * κ * (√L / √(k : ℝ)) := by
    have h3 : D * √(StatFormal.Wave30tp.sNM n m * L / 2) ≤ 2 * κ * (√L / √(k : ℝ)) :=
      mul_le_mul hD hlog (Real.sqrt_nonneg _) (by linarith)
    have h1 := mul_le_mul_of_nonneg_left hsq (by linarith : 0 ≤ 2 * κ)
    have h2 := mul_le_mul_of_nonneg_left (add_le_add hen hem) (by linarith : 0 ≤ 2 * κ)
    linarith
  have hβ : 0 < 1 - α := by linarith
  simp only [StatFormal.Wave30tr.tauA]
  calc 1 / (1 - α) * (2 * κ * √(StatFormal.Wave30tp.sNM n m) + 2 * κ * (StatFormal.Wave30tr.ek n + StatFormal.Wave30tr.ek m) +
        D * √(StatFormal.Wave30tp.sNM n m * L / 2))
      ≤ 1 / (1 - α) * (2 * κ * (√2 / √(k : ℝ)) + 2 * κ * (1 / √(k : ℝ) + 1 / √(k : ℝ)) + 2 * κ * (√L / √(k : ℝ))) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 2 * κ / (1 - α) * (√2 + 2 + √L) / √(k : ℝ) := by field_simp; ring

/-- `A + x + y ≤ 7√(1 + x² + y²)` for `A = 2√2 + 4` and `x, y ≥ 0`. -/
lemma cs_seven {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * √2 + 4 + x + y ≤ 7 * √(1 + x ^ 2 + y ^ 2) := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h20 : 0 ≤ √2 := Real.sqrt_nonneg _
  have hA : (2 * √2 + 4) ^ 2 + 2 ≤ 49 := by nlinarith
  have hS : 0 ≤ 1 + x ^ 2 + y ^ 2 := by positivity
  rw [show (7 : ℝ) * √(1 + x ^ 2 + y ^ 2) = √(49 * (1 + x ^ 2 + y ^ 2)) by
    rw [Real.sqrt_mul (by norm_num), show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  apply Real.le_sqrt_of_sq_le
  set A := 2 * √2 + 4
  have hcs : (A + x + y) ^ 2 ≤ (A ^ 2 + 2) * (1 + x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (A * x - 1), sq_nonneg (A * y - 1), sq_nonneg (x - y)]
  nlinarith

theorem rate_v3_full : Claims.rate_v3_full := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ δ' c₀ γ n m hφ hκ hD h1 hpm hδ hδ1 hδ' hδ'1 hn hm ht
  set a := StatFormal.Distances.tvDist P Q with ha
  have ha0 : 0 ≤ a := StatFormal.Distances.tvDist_nonneg P Q
  haveI : Nonempty 𝒳 := MeasureTheory.Measure.nonempty_of_neZero P
  obtain ⟨x0⟩ := (inferInstance : Nonempty 𝒳)
  have hthr := StatFormal.Wave30tu.Full.tauFull_threshold 𝒳 H φ κ D δ n m ⟨x0⟩ hφ hκ hD hδ hδ1 hn hm
  have hthr' := StatFormal.Wave30tu.Full.tauFull_threshold 𝒳 H φ κ D δ' n m ⟨x0⟩ hφ hκ hD hδ' hδ'1 hn hm
  have hF0 : 0 ≤ StatFormal.Wave30tu.Full.tauFull κ D a δ n m := hthr.1.1 a ⟨ha0, h1⟩
  have hA0 : 0 ≤ StatFormal.Wave30tr.tauA κ D a δ' n m :=
    (hthr'.1.1 a ⟨ha0, h1⟩).trans (hthr'.2.1 a ⟨ha0, h1⟩)
  have ht0 := add_nonneg hF0 hA0
  obtain ⟨hmar, hsol⟩ := poly_is_general 𝒳 H P Q φ c₀ γ hpm
  obtain ⟨hε, hωε⟩ := hsol _ ht0 ht
  obtain ⟨E, hE, hPE, hsub⟩ := StatFormal.Wave30tu.Full.rate_full 𝒳 H P Q φ κ D δ δ' (fun e => c₀ * e ^ γ) n m _ hφ hκ hD h1
    hmar hδ hδ1 hδ' hδ'1 hn hm hε hωε
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
  have hD0 : 0 ≤ D := by simpa using hD x0 x0
  have hbound : D ≤ 2 * κ →
      StatFormal.Wave30tu.Full.tauFull κ D a δ n m + StatFormal.Wave30tr.tauA κ D a δ' n m ≤
        2 * κ / (1 - a) * (2 * √2 + 4 + √(Real.log (1 / δ)) + √(Real.log (1 / δ'))) / √((min n m : ℕ) : ℝ) := by
    intro hD2
    have e1 := (hthr.2.1 a ⟨ha0, h1⟩).trans (tauA_le_printed hκ0 hD0 hD2 h1 hδ hδ1 hn hm)
    have e2 := tauA_le_printed (α := a) hκ0 hD0 hD2 h1 hδ' hδ'1 hn hm
    calc _ ≤ 2 * κ / (1 - a) * (√2 + 2 + √(Real.log (1 / δ))) / √((min n m : ℕ) : ℝ) +
          2 * κ / (1 - a) * (√2 + 2 + √(Real.log (1 / δ'))) / √((min n m : ℕ) : ℝ) := add_le_add e1 e2
      _ = _ := by ring
  refine ⟨⟨E, hE, hPE, fun z hz => ?_⟩, hbound, fun hD2 => ?_⟩
  · obtain ⟨hlo, hhi⟩ := hsub hz
    exact ⟨hhi, abs_sub_le_iff.2 ⟨by linarith, by linarith⟩⟩
  · have hc := hpm.1
    have hγ0 : 0 < γ := by linarith [hpm.2.1]
    have hb := hbound hD2
    set L1 := Real.log (1 / δ)
    set L2 := Real.log (1 / δ')
    have hL1 : 0 ≤ L1 := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    have hL2 : 0 ≤ L2 := Real.log_nonneg (by rw [le_div_iff₀ hδ']; linarith)
    have hk0 : (0 : ℝ) < ((min n m : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one (le_min hn hm)
    have hsk : 0 < √((min n m : ℕ) : ℝ) := Real.sqrt_pos.2 hk0
    have hβ : 0 < 1 - a := by linarith
    have hcs := cs_seven (Real.sqrt_nonneg L1) (Real.sqrt_nonneg L2)
    rw [Real.sq_sqrt hL1, Real.sq_sqrt hL2] at hcs
    apply Real.rpow_le_rpow (div_nonneg ht0 hc.le) _ (by positivity)
    rw [div_le_iff₀ hc]
    have hfac : 0 ≤ 2 * κ / (1 - a) / √((min n m : ℕ) : ℝ) := by positivity
    calc _ ≤ 2 * κ / (1 - a) * (2 * √2 + 4 + √L1 + √L2) / √((min n m : ℕ) : ℝ) := hb
      _ = 2 * κ / (1 - a) / √((min n m : ℕ) : ℝ) * (2 * √2 + 4 + √L1 + √L2) := by ring
      _ ≤ 2 * κ / (1 - a) / √((min n m : ℕ) : ℝ) * (7 * √(1 + L1 + L2)) := mul_le_mul_of_nonneg_left hcs hfac
      _ = 14 * κ / (c₀ * (1 - a)) * √((1 + L1 + L2) / ((min n m : ℕ) : ℝ)) * c₀ := by
          rw [Real.sqrt_div (by positivity)]; field_simp; ring

theorem linear_poly : Claims.linear_poly := by
  obtain ⟨htv, hM⟩ := StatFormal.Wave31tf.linear_margin
  refine ⟨by norm_num, le_rfl, fun e he => ?_⟩
  have h := hM.2.2.2.2 e he
  simp only at h
  rw [Real.rpow_one]; linarith

end StatFormal.Wave31ti
