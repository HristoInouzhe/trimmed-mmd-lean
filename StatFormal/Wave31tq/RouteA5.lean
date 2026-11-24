import StatFormal.Wave31tq.RouteA2

/-!
# Wave 31tq, route A: Q5 `sobolev_angular` (untrusted proof file)

The angular spectral bounds `c(1 + |ξ|²)^{−s} ≤ k̂₀(ξ) ≤ C(1 + |ξ|²)^{−s}` are, at `ξ = 2πη`, the bounds
`c(1 + 4π²|η|²)^{−s} ≤ specDens k₀ η ≤ C(…)^{−s}` of the certified library (`specDens_lower`, `specDens_upper`). Then (a) is L19
`sobolev_incl` with `sobolevA = sobolevS`; (b) is L25 `characteristic_spec` (`specDens > 0` everywhere); (c) compares the native and
Sobolev functionals pointwise in `[0, ∞]` (`AngularFourier.lintegral_div_le_of_lower`, `div_le_lintegral_of_upper`) and uses L18
`native_char` for the iff and the least representer (`C ≥ c > 0` from the bounds at `ξ = 0`); (d) is L22 `matern_facts` at `η = ξ/2π`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter FourierTransform
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteA

open StatFormal.Wave31tp StatFormal.AngularFourier

section Bounds

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- An angular lower bound is a lower bound of `specDens` with the weight `(1 + 4π²|η|²)^{−s}`. -/
theorem specDens_lower {k₀ : V → ℝ} {c s : ℝ} (h : ∀ ξ, c * (1 + ‖ξ‖ ^ 2) ^ (-s) ≤ kHat k₀ ξ) (η : V) :
    c * (1 + 4 * Real.pi ^ 2 * ‖η‖ ^ 2) ^ (-s) ≤ specDens k₀ η := by
  have := h ((2 * Real.pi) • η)
  rwa [kHat_two_pi_smul, norm_two_pi_smul_sq] at this

/-- An angular upper bound is an upper bound of `specDens` with the weight `(1 + 4π²|η|²)^{−s}`. -/
theorem specDens_upper {k₀ : V → ℝ} {C s : ℝ} (h : ∀ ξ, kHat k₀ ξ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-s)) (η : V) :
    specDens k₀ η ≤ C * (1 + 4 * Real.pi ^ 2 * ‖η‖ ^ 2) ^ (-s) := by
  have := h ((2 * Real.pi) • η)
  rwa [kHat_two_pi_smul, norm_two_pi_smul_sq] at this

end Bounds

theorem sobolev_angular_route : Claims.sobolev_angular := by
  refine ⟨fun V _ _ _ _ _ H _ _ _ φ k₀ c s hc hi hgram hc0 hlow => ?_, fun V _ _ _ _ _ s a ℓ hs ha hℓ => ?_⟩
  · have hlow' := specDens_lower hlow
    have hw : ∀ η : V, 0 < (1 + 4 * Real.pi ^ 2 * ‖η‖ ^ 2) ^ s := fun η => Real.rpow_pos_of_pos (by positivity) _
    have hneg : ∀ η : V, (1 + 4 * Real.pi ^ 2 * ‖η‖ ^ 2) ^ (-s) = ((1 + 4 * Real.pi ^ 2 * ‖η‖ ^ 2) ^ s)⁻¹ :=
      fun η => Real.rpow_neg (by positivity) s
    have hpos : ∀ η, 0 < specDens k₀ η := fun η =>
      (mul_pos hc0 (Real.rpow_pos_of_pos (by positivity) _)).trans_le (hlow' η)
    have h19 := sobolev_incl V H φ k₀ c s hc hi hgram hc0 hlow'
    have h18 := native_char V H φ k₀ hc hi hgram
    have h25 := characteristic_spec V H φ k₀ hc hi hgram (Eventually.of_forall hpos)
    have hNle : ∀ f : V → ℂ, nativeN k₀ f ≤ sobolevS s f / ENNReal.ofReal c := fun f =>
      lintegral_div_le_of_lower hc0 hw (fun η => by rw [← hneg]; exact hlow' η)
    refine ⟨fun f hf hf2 hfs => ?_, h25, fun C hup f hf => ?_⟩
    · rw [RouteS.sobolevA_eq_sobolevS] at hfs ⊢
      exact h19 f hf hf2 hfs
    · have hup' := specDens_upper hup
      have hcC : c ≤ C := by
        have h0 := (hlow 0).trans (hup 0)
        simpa using h0
      have hC : 0 < C := hc0.trans_le hcC
      have hSle : ∀ f : V → ℂ, sobolevS s f / ENNReal.ofReal C ≤ nativeN k₀ f := fun f =>
        div_le_lintegral_of_upper hC hw hpos (fun η => by rw [← hneg]; exact hup' η)
      simp only [RouteS.sobolevA_eq_sobolevS]
      obtain ⟨hiff, hmin⟩ := h18.2 f hf
      refine ⟨⟨fun hrep => ?_, fun hfs => ?_⟩, fun hrep => ?_⟩
      · obtain ⟨hf2, hN⟩ := hiff.1 hrep
        refine ⟨hf2, ?_⟩
        have hlt := (hSle (fun x => (f x : ℂ))).trans_lt hN
        have heq : sobolevS s (fun x => (f x : ℂ)) / ENNReal.ofReal C * ENNReal.ofReal C = sobolevS s (fun x => (f x : ℂ)) :=
          ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 hC).ne' ENNReal.ofReal_ne_top
        rw [← heq]
        exact ENNReal.mul_lt_top hlt ENNReal.ofReal_lt_top
      · obtain ⟨g, hg, -⟩ := h19 f hf hfs.1 hfs.2
        exact ⟨g, hg⟩
      · obtain ⟨g₀, hg₀, hnorm, hle⟩ := hmin hrep
        exact ⟨g₀, hg₀, hle, hnorm ▸ hSle _, hnorm ▸ hNle _⟩
  · obtain ⟨-, -, -, -, -, -, -, hm⟩ := matern_facts V s hs
    obtain ⟨hcont, -, hint, -, hb⟩ := hm a ℓ ha hℓ
    refine ⟨hcont, hint, fun ξ => ?_⟩
    have := hb ((2 * Real.pi)⁻¹ • ξ)
    rw [four_pi_sq_mul_norm_inv_two_pi_smul_sq] at this
    exact this

end StatFormal.Wave31tq.RouteA
