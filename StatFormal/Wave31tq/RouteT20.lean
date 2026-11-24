import StatFormal.Wave31tq.RouteT20b

/-!
# Wave 31tq, route T (Q20): `Claims.newmoments` (untrusted)

`newmoments_of (h1 : Claims.tv_density) (h4 : Claims.bochner_angular) : Claims.newmoments`. The main part is
`MomentTrim.exists_moment_trimming` turned into measures (`trimming_measures`, RouteT20a); (a) and (b) are
`trim_bound_at` (the level `w = (8ε/ℓ₀)^{1/2}`, monotonicity of `D̄` from the certified `Wave31ti.pathconvex`, the explicit
trimming bound `MomentTrim.uPath_le_of_le`, eq:newmomentdecay `momentdecay_signed`) followed by `norm_le_case_a`,
`norm_le_case_b` (RouteT20b) and the algebra `w² = 8ε/ℓ₀`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteT

open StatFormal.MomentTrim

/-- **The trimming at level `ε`.** With `w = (8ε/ℓ₀)^{1/2} ≤ w_N`, there are `P′ ≤ P`, `Q′ ≤ Q` with
`D̄_{α⋆−ε} ≤ ‖∫ φ dP′ − ∫ φ dQ′‖` and `|P̂′ − Q̂′| ≤ 2ℓ₀w² min{1, (|ξ|Tw)^N/N!}`. -/
theorem trim_bound_at (h1 : Claims.tv_density) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : ℝ → H) {κ : ℝ} (hsm : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {p q : ℝ → ℝ} {x₀ ℓ₀ T wN : ℝ} {N : ℕ}
    (hpm : Measurable p) (hqm : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hP : P = volume.withDensity (fun x => ENNReal.ofReal (p x))) (hQ : Q = volume.withDensity (fun x => ENNReal.ofReal (q x)))
    (hℓ : 0 < ℓ₀) (hN : 1 ≤ N) (hT : 1 ≤ T) (hwN : 0 < wN)
    (htrim : ∀ w ∈ Ioc (0 : ℝ) wN, ∃ fP fQ hp hm : ℝ → ℝ, ∃ e : ℝ, IsMomentTrimming p q x₀ ℓ₀ N T w fP fQ hp hm e)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (ℓ₀ * wN ^ 2 / 8)) :
    ∃ P' Q' : FiniteMeasure ℝ,
      StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤
        ‖∫ x, φ x ∂(P' : Measure ℝ) - ∫ x, φ x ∂(Q' : Measure ℝ)‖ ∧
      ∀ ξ, ‖ftMeasA (P' : Measure ℝ) ξ - ftMeasA (Q' : Measure ℝ) ξ‖ ≤
        2 * ℓ₀ * √(8 * ε / ℓ₀) ^ 2 * min 1 ((|ξ| * (T * √(8 * ε / ℓ₀))) ^ N / (N.factorial : ℝ)) := by
  set w := √(8 * ε / ℓ₀) with hwdef
  have hε0 := hε.1
  have h8 : 0 < 8 * ε / ℓ₀ := by positivity
  have hw0 : 0 < w := Real.sqrt_pos.mpr h8
  have hw2 : w ^ 2 = 8 * ε / ℓ₀ := Real.sq_sqrt h8.le
  have hwN' : w ≤ wN := by
    have h : 8 * ε / ℓ₀ ≤ wN ^ 2 := by
      rw [div_le_iff₀ hℓ]; have := hε.2; rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)] at this; linarith
    exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq hwN.le)
  obtain ⟨fP, fQ, hp, hm, e, ht⟩ := htrim w ⟨hw0, hwN'⟩
  obtain ⟨P', Q', hP'le, hQ'le, he, hmP, hmQ, htv, hsupp, hmom⟩ := trimming_measures h1 hpm hqm hp0 hq0 hP hQ ht
  refine ⟨P', Q', ?_, ?_⟩
  · have hεe : ε ≤ e := by
      have : ℓ₀ * w ^ 2 / 8 = ε := by rw [hw2]; field_simp
      linarith
    have hmin := integral_min_eq h1 hpm hqm hp0 hq0 hP hQ
    have htv1 : StatFormal.Distances.tvDist P Q ≤ 1 := by
      have := integral_nonneg (f := fun x => min (p x) (q x)) (μ := volume) (fun x => le_min (hp0 x) (hq0 x))
      linarith
    have heα : e ≤ StatFormal.Distances.tvDist P Q := by
      have h := Measure.le_iff'.mp hP'le univ
      rw [hmP, measure_univ] at h
      have := ENNReal.ofReal_le_one.mp h
      linarith
    have hanti := (StatFormal.Wave31ti.pathconvex ℝ H P Q φ κ hsm hκ).2
    have hstep : StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤
        StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - e) :=
      hanti ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    refine hstep.trans (uPath_le_of_le φ P Q (P' : Measure ℝ) (Q' : Measure ℝ) hP'le hQ'le (by linarith) ?_ ?_)
    · rw [hmP]; congr 1; ring
    · rw [hmQ]; congr 1; ring
  · intro ξ
    rw [← ftSigned_sub]
    refine (momentdecay_signed _ x₀ (T * w) N (by positivity) hN hsupp hmom ξ).trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.toReal_le_of_le_ofReal (by positivity) htv)
      (le_min zero_le_one (by positivity))

/-- The algebra of case (a): with `w = (8ε/ℓ₀)^{1/2}`, `2ℓ₀w²(Tw)^{s−1/2}R = Kε^{(2s+3)/4}`. -/
lemma alg_a {ε ℓ₀ T s R : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ₀) (hT : 0 < T) :
    2 * ℓ₀ * √(8 * ε / ℓ₀) ^ 2 * (T * √(8 * ε / ℓ₀)) ^ (s - 1 / 2) * R =
      16 * T ^ (s - 1 / 2) * (8 / ℓ₀) ^ ((2 * s - 1) / 4) * R * ε ^ ((2 * s + 3) / 4) := by
  have h8 : 0 ≤ 8 * ε / ℓ₀ := by positivity
  rw [Real.sq_sqrt h8, Real.mul_rpow hT.le (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul h8,
    show 8 * ε / ℓ₀ = 8 / ℓ₀ * ε by ring, Real.mul_rpow (by positivity) hε.le,
    show 1 / (2 : ℝ) * (s - 1 / 2) = (2 * s - 1) / 4 by ring,
    show (2 * s + 3) / 4 = 1 + (2 * s - 1) / 4 by ring, Real.rpow_add hε, Real.rpow_one]
  field_simp
  ring

/-- The algebra of case (b): with `w = (8ε/ℓ₀)^{1/2}`, `2ℓ₀w²(Tw)^N R/N! = Kε^{1+N/2}`. -/
lemma alg_b {ε ℓ₀ T R : ℝ} {N : ℕ} (hε : 0 < ε) (hℓ : 0 < ℓ₀) :
    2 * ℓ₀ * √(8 * ε / ℓ₀) ^ 2 * (T * √(8 * ε / ℓ₀)) ^ N * R / (N.factorial : ℝ) =
      16 * T ^ N * (8 / ℓ₀) ^ ((N : ℝ) / 2) * R / (N.factorial : ℝ) * ε ^ (1 + (N : ℝ) / 2) := by
  have h8 : 0 ≤ 8 * ε / ℓ₀ := by positivity
  rw [Real.sq_sqrt h8, mul_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast ((8 * ε / ℓ₀) ^ (1 / (2 : ℝ))) N,
    ← Real.rpow_mul h8, show 8 * ε / ℓ₀ = 8 / ℓ₀ * ε by ring, Real.mul_rpow (by positivity) hε.le,
    show 1 / (2 : ℝ) * (N : ℝ) = (N : ℝ) / 2 by ring, Real.rpow_add hε, Real.rpow_one]
  field_simp
  ring

/-- Q20 `newmoments` (Proposition S4.15), from Q1(b) and Q4. -/
theorem newmoments_of (h1 : Claims.tv_density) (h4 : Claims.bochner_angular) : Claims.newmoments := by
  intro P Q _ _ p q x₀ r₀ ℓ₀ hpm hqm hp0 hq0 hP hQ hr₀ hpc hqc hd hℓ hpq hpos N hN
  obtain ⟨hpi, -⟩ := density_integrable hpm hp0 hP
  obtain ⟨T, wN, hT, hwN, htrim⟩ := exists_moment_trimming hpm hqm hp0 hq0 hpi hr₀ hpc hqc hd hℓ hpq hpos N hN
  have hT0 : 0 < T := by linarith
  have hfac2 : (0 : ℝ) < (N.factorial : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr (Nat.factorial_pos N)) 2
  refine ⟨T, wN, hT, hwN, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨fP, fQ, hp, hm, e, ht⟩ := htrim w hw
    obtain ⟨P', Q', h⟩ := trimming_measures h1 hpm hqm hp0 hq0 hP hQ ht
    exact ⟨P', Q', e, h⟩
  · intro H _ _ _ _ φ k₀ C s hk hki hg hC hs hsN hkb
    refine ⟨integrable_minPow N hfac2 hs hsN, ?_⟩
    obtain ⟨-, hsm, hnorm, -⟩ := Wave31tp.mmd_fourier ℝ H φ k₀ hk hki hg
    set I := ∫ v : ℝ, min 1 (v ^ (2 * N) / (N.factorial : ℝ) ^ 2) * |v| ^ (-2 * s) with hI
    refine ⟨16 * T ^ (s - 1 / 2) * (8 / ℓ₀) ^ ((2 * s - 1) / 4) * √(C * I / (2 * Real.pi)), fun ε hε => ?_⟩
    intro w I'
    obtain ⟨P', Q', hu, hft⟩ :=
      trim_bound_at h1 φ hsm (fun x => (hnorm x).le) hpm hqm hp0 hq0 hP hQ hℓ hN hT hwN htrim hε
    have hw0 : 0 < w := Real.sqrt_pos.mpr (by have := hε.1; positivity)
    refine ⟨hu.trans (norm_le_case_a h4 φ k₀ hk hki hg hC hs hsN hkb (P' : Measure ℝ) (Q' : Measure ℝ)
      (by positivity) (by positivity) hft), le_of_eq (alg_a hε.1 hℓ hT0)⟩
  · intro H _ _ _ _ φ k₀ hk hki hg hmi
    obtain ⟨-, hsm, hnorm, -⟩ := Wave31tp.mmd_fourier ℝ H φ k₀ hk hki hg
    set M := (2 * Real.pi)⁻¹ * ∫ ξ : ℝ, ξ ^ (2 * N) * kHat k₀ ξ with hM
    refine ⟨16 * T ^ N * (8 / ℓ₀) ^ ((N : ℝ) / 2) * √M / (N.factorial : ℝ), fun ε hε => ?_⟩
    intro w M'
    obtain ⟨P', Q', hu, hft⟩ :=
      trim_bound_at h1 φ hsm (fun x => (hnorm x).le) hpm hqm hp0 hq0 hP hQ hℓ hN hT hwN htrim hε
    refine ⟨hu.trans (norm_le_case_b h4 φ k₀ hk hki hg hmi (P' : Measure ℝ) (Q' : Measure ℝ)
      (by positivity) (by positivity) hft), le_of_eq (alg_b hε.1 hℓ)⟩

end StatFormal.Wave31tq.RouteT
