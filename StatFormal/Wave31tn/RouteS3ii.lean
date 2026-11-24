import StatFormal.Wave31tn.Statements
import StatFormal.Wave31ti.RouteRate

/-!
# Wave 31tn route: S3 (ii) `cor:minimax`, the analytic estimator (untrusted proof material)

`C′ = 2κK/(1−a₁)`, `K = 2√2 + 4 + √log(1/δ) + √log(1/δ′)`, `C = C′/c₀`, `N₁ = max(1, (C′/(c₀a₀))²)`. For `(P,Q) ∈ 𝓜` and `N = n∧m ≥ N₁`:
`t = τ_{n,m}(α⋆,δ) + τ^A_{n,m}(α⋆,δ′) ≤ 2κK/((1−α⋆)√N) ≤ C′/√N ≤ c₀a₀ ≤ c₀α⋆` (the certified `tauFull ≤ τ^A` of `tauFull_threshold` and
the printed bound `Wave31ti.tauA_le_printed`, both free of the rate hypothesis), so the certified `Wave31ti.rate_v3_full` (`γ = 1`) gives
an event of probability `≥ 1 − δ − δ′` on which `α⋆ − α̂ ≤ t/c₀ ≤ C/√N`; validity is the certified `Wave30tu.Full.consistency_i_full`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tn

namespace RouteS3ii

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional

/-- An event of probability `≥ 1 − x` has a complement of probability `≤ x`. -/
lemma compl_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {E : Set α} (hE : MeasurableSet E)
    {x : ℝ} (hx : 0 ≤ x) (h : ENNReal.ofReal (1 - x) ≤ μ E) : μ Eᶜ ≤ ENNReal.ofReal x := by
  rw [prob_compl_eq_one_sub hE]
  by_cases hx1 : x ≤ 1
  · calc 1 - μ E ≤ 1 - ENNReal.ofReal (1 - x) := tsub_le_tsub_left h 1
      _ = ENNReal.ofReal x := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ 1 - x)]
          congr 1; ring
  · exact tsub_le_self.trans (ENNReal.one_le_ofReal.2 (by linarith))

theorem minimax_ii_route : Claims.minimax_ii := by
  intro κ Dφ a₀ a₁ c₀ δ δ' ha0 ha01 ha1 hc0 hδ0 hδ1 hδ'0 hδ'1
  set K := 2 * √2 + 4 + √(Real.log (1 / δ)) + √(Real.log (1 / δ')) with hK
  set C' := 2 * κ * K / (1 - a₁) with hC'
  refine ⟨C' / c₀, max 1 ((C' / (c₀ * a₀)) ^ 2), ?_⟩
  intro 𝒳 H _ _ _ _ _ φ n m P Q hφ hκ hD hD2 hN hM
  obtain ⟨hP, hQ, hlo, hhi, hpm⟩ := hM
  haveI := hP
  haveI := hQ
  set a := StatFormal.Distances.tvDist P Q with hadef
  have h1 : a < 1 := by linarith
  have hN1 : (1 : ℝ) ≤ ((min n m : ℕ) : ℝ) := (le_max_left _ _).trans hN
  have hn : 1 ≤ n := by have : 1 ≤ min n m := by exact_mod_cast hN1
                        omega
  have hm : 1 ≤ m := by have : 1 ≤ min n m := by exact_mod_cast hN1
                        omega
  haveI : Nonempty 𝒳 := MeasureTheory.Measure.nonempty_of_neZero P
  obtain ⟨x0⟩ := (inferInstance : Nonempty 𝒳)
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
  have hD0 : 0 ≤ Dφ := by simpa using hD x0 x0
  have ha0' : 0 ≤ a := StatFormal.Distances.tvDist_nonneg P Q
  have hthr := StatFormal.Wave30tu.Full.tauFull_threshold 𝒳 H φ κ Dφ δ n m ⟨x0⟩ hφ hκ hD hδ0 hδ1 hn hm
  have hL1 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hL2 : 0 ≤ Real.log (1 / δ') := Real.log_nonneg (by rw [le_div_iff₀ hδ'0]; linarith)
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hC'0 : 0 ≤ C' := by rw [hC']; exact div_nonneg (by positivity) (by linarith)
  have hk0 : (0 : ℝ) < ((min n m : ℕ) : ℝ) := by linarith
  have hsk : 0 < √((min n m : ℕ) : ℝ) := Real.sqrt_pos.2 hk0
  -- the bound on `t`, free of the rate hypothesis
  have ht : StatFormal.Wave30tu.Full.tauFull κ Dφ a δ n m + StatFormal.Wave30tr.tauA κ Dφ a δ' n m ≤
      C' / √((min n m : ℕ) : ℝ) := by
    have e1 := (hthr.2.1 a ⟨ha0', h1⟩).trans (StatFormal.Wave31ti.tauA_le_printed hκ0 hD0 hD2 h1 hδ0 hδ1 hn hm)
    have e2 := StatFormal.Wave31ti.tauA_le_printed (α := a) hκ0 hD0 hD2 h1 hδ'0 hδ'1 hn hm
    have hβ : 2 * κ / (1 - a) ≤ 2 * κ / (1 - a₁) :=
      div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
    calc _ ≤ 2 * κ / (1 - a) * (√2 + 2 + √(Real.log (1 / δ))) / √((min n m : ℕ) : ℝ) +
          2 * κ / (1 - a) * (√2 + 2 + √(Real.log (1 / δ'))) / √((min n m : ℕ) : ℝ) := add_le_add e1 e2
      _ = 2 * κ / (1 - a) * K / √((min n m : ℕ) : ℝ) := by rw [hK]; ring
      _ ≤ 2 * κ / (1 - a₁) * K / √((min n m : ℕ) : ℝ) := by gcongr
      _ = C' / √((min n m : ℕ) : ℝ) := by rw [hC']; ring
  have hsmall : C' / √((min n m : ℕ) : ℝ) ≤ c₀ * a₀ := by
    rw [div_le_iff₀ hsk]
    have hq : C' / (c₀ * a₀) ≤ √((min n m : ℕ) : ℝ) := by
      rw [← Real.sqrt_sq (div_nonneg hC'0 (by positivity))]
      exact Real.sqrt_le_sqrt ((le_max_right _ _).trans hN)
    rw [div_le_iff₀ (by positivity)] at hq
    linarith
  have htc : StatFormal.Wave30tu.Full.tauFull κ Dφ a δ n m + StatFormal.Wave30tr.tauA κ Dφ a δ' n m ≤ c₀ * a ^ (1 : ℝ) := by
    rw [Real.rpow_one]; nlinarith
  obtain ⟨⟨E, hE, hPE, hEsub⟩, -, -⟩ := StatFormal.Wave31ti.rate_v3_full 𝒳 H P Q φ κ Dφ δ δ' c₀ 1 n m hφ hκ hD h1 hpm
    hδ0 hδ1 hδ'0 hδ'1 hn hm htc
  obtain ⟨E', hE', hPE', hE'sub⟩ := StatFormal.Wave30tu.Full.consistency_i_full 𝒳 H P Q φ κ Dφ δ n m hφ hκ hD h1 hδ0 hδ1 hn hm
  have hsl : IsProbabilityMeasure (StatFormal.Wave30tp.sampleLaw P Q n m) := by
    unfold StatFormal.Wave30tp.sampleLaw; infer_instance
  constructor
  · refine (measure_mono fun z hz => ?_).trans (compl_le (μ := StatFormal.Wave30tp.sampleLaw P Q n m) hE' hδ0.le hPE')
    intro hzE
    exact absurd (hE'sub hzE).1 (not_le.2 hz)
  · refine (measure_mono fun z hz => ?_).trans
      (compl_le (μ := StatFormal.Wave30tp.sampleLaw P Q n m) hE (by linarith) (by rw [show 1 - (δ + δ') = 1 - δ - δ' by ring]; exact hPE))
    intro hzE
    obtain ⟨-, habs⟩ := hEsub hzE
    rw [div_one, Real.rpow_one] at habs
    have h2 : a - alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tu.Full.tauFull κ Dφ α δ n m) ≤
        (StatFormal.Wave30tu.Full.tauFull κ Dφ a δ n m + StatFormal.Wave30tr.tauA κ Dφ a δ' n m) / c₀ :=
      (le_abs_self _).trans (by rw [abs_sub_comm]; exact habs)
    have h3 : (StatFormal.Wave30tu.Full.tauFull κ Dφ a δ n m + StatFormal.Wave30tr.tauA κ Dφ a δ' n m) / c₀ ≤
        C' / c₀ / √((min n m : ℕ) : ℝ) := by
      rw [div_right_comm]
      exact div_le_div_of_nonneg_right ht hc0.le
    have hz' : C' / c₀ / √((min n m : ℕ) : ℝ) < a - alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tu.Full.tauFull κ Dφ α δ n m) := hz
    linarith

end RouteS3ii

end StatFormal.Wave31tn
