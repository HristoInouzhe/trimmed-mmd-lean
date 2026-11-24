import StatFormal.Wave31tl.RouteBasic

/-!
# Wave 31tl route: the lower side of Theorem 33 (untrusted proof material)

`core_lower`: the proof of Theorem 33 (i) for a general excess profile. With `β⋆ = β(α⋆)`, `D⋆ > 0` and weights `x_j ≥ 1` with
`D⋆x_j ≤ D_{α_j}` at every level `α_j ≤ a ≤ α⋆`, if `β⋆T_fit(η) ≤ D⋆`, `β⋆T_bet(η,J′) ≤ D⋆` and
`Σ_{α_j ≤ a} e^{−A x_j²} ≤ J′e^{−A}` for `A ≥ log(2J′/η)`, then `P(α̂_lo < gridFloor α a) ≤ η`.
* the fitting event `E_fit = {Z_b, Z⁻_b ≤ τ⋆ = D⋆/(8β⋆)}` (Wave 30tz `fitEvent`) has `P(E_fitᶜ) ≤ 2B·η/(4B) = η/2`
  (`fitEvent_compl_le`; `τ⋆ − μ₁ ≥ Δ_φ√(r₁ log(4B/η)/2)` from `β⋆T_fit ≤ D⋆`);
* on `E_fit`, at every level `α_j ≤ a`, `witness_step` (Wave 30tz, with `d = D_{α_j}`, `β = β⋆`) gives a ramp with excess
  `ϱ_j = D_{α_j}/(2β⋆Δ_φ) ≥ ϱ⋆x_j`; Lemma 5 (`bet_power_route`, `bet_arith`) gives `ε_N(ϱ_j)`, and `N ≥ 200L ≥ 8L` makes
  `λ_N = √(L/(2N))`; `(ϱ_jS − C)₊ ≥ a x_j` with `a = ϱ⋆S − C ≥ (2/σ_min)√(L log(2J′/η))`, so `ε_N(ϱ_j) ≤ e^{−A x_j²}`, `A ≥ log(2J′/η)`;
* the union bound over `E_fitᶜ` and the levels `α_j ≤ a` (`grid_events_route`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tl

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.TrimmedMMD.Unconditional

namespace Core

lemma fitCard_mono {p : ℕ} (l : Fin p → ℕ) {b b' : ℕ} (h : b ≤ b') : fitCard l b ≤ fitCard l b' := by
  unfold fitCard
  refine Finset.card_le_card fun i hi => ?_
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, lt_of_lt_of_le hi.2 h⟩

lemma one_le_beta' {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) : 1 ≤ beta α := by
  unfold beta; rw [le_div_iff₀ (by linarith)]; linarith

/-- The arithmetic of the betting step: for `σ²_min ∈ (0,4]`, `N ≥ 8L`, `α ∈ [0,1)`, the Lemma-5 term `genEps` at `λ_N` and excess
`ρ ≥ ϱ⋆x`, `x ≥ 1`, with `a₀ = ϱ⋆√(NL/2) − L(1+16/σ²_min) ≥ 0`, is at most `exp(−(σ²_min a₀²/(4L)) x²)`. -/
lemma genEps_le (s2 L α ρ ρs x : ℝ) (N : ℕ) (hs20 : 0 < s2) (hs24 : s2 ≤ 4) (hL : 0 < L) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hN8 : 8 * L ≤ N) (hx1 : 1 ≤ x) (hρ : ρs * x ≤ ρ)
    (ha0 : 0 ≤ ρs * √(N * L / 2) - L * (1 + 16 / s2)) :
    genEps s2 α L N ρ (lamLo (1 / 2) α L s2 N) ≤
      Real.exp (-(s2 * (ρs * √(N * L / 2) - L * (1 + 16 / s2)) ^ 2 / (4 * L) * x ^ 2)) := by
  have hNpos : (0 : ℝ) < N := by linarith
  set a0 := ρs * √(N * L / 2) - L * (1 + 16 / s2) with ha0def
  have h1α : 0 < 1 + α := by linarith
  -- `λ_N = √(2L/(4N))`
  have hlo_eq : lamLo (1 / 2) α L s2 N = √(2 * L / (N * 4)) := by
    unfold lamLo
    rw [max_eq_right hs24]
    apply min_eq_right
    have hsq : 2 * L / (N * 4) ≤ (1 / 2 / (1 + α)) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : (1 + α) ^ 2 ≤ 4 := by nlinarith
      have := mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ 2 * L)
      nlinarith
    calc √(2 * L / (N * 4)) ≤ √((1 / 2 / (1 + α)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 1 / 2 / (1 + α) := Real.sqrt_sq (by positivity)
  have hNlo : (N : ℝ) * √(2 * L / (N * 4)) = √(N * L / 2) := by
    rw [show (N : ℝ) * L / 2 = N ^ 2 * (2 * L / (N * 4)) by field_simp; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hNpos.le]
  have hS0 : 0 ≤ √(N * L / 2) := Real.sqrt_nonneg _
  have hρs0 : 0 ≤ ρs := by
    by_contra h
    have : ρs * √(N * L / 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.1 h)) hS0
    have : 0 < L * (1 + 16 / s2) := by positivity
    linarith
  unfold genEps
  rw [hlo_eq, show (N : ℝ) * √(2 * L / (N * 4)) * ρ = ρ * √(N * L / 2) by rw [← hNlo]; ring]
  apply Real.exp_le_exp.2
  -- `(ρS − L − 4L(1+α)²/s2)₊ ≥ a₀ x ≥ 0`
  have hC : 4 * L * (1 + α) ^ 2 / s2 ≤ 16 * L / s2 := by
    apply div_le_div_of_nonneg_right _ hs20.le
    have : (1 + α) ^ 2 ≤ 4 := by nlinarith
    nlinarith
  have hlin : a0 * x ≤ ρ * √(N * L / 2) - L - 4 * L * (1 + α) ^ 2 / s2 := by
    have h2 : ρs * x * √(N * L / 2) ≤ ρ * √(N * L / 2) := mul_le_mul_of_nonneg_right hρ hS0
    have h3 : a0 * x ≤ ρs * x * √(N * L / 2) - L * (1 + 16 / s2) := by
      -- a₀x = ϱ⋆Sx − Cx ≤ ϱ⋆Sx − C  since C ≥ 0, x ≥ 1
      have hC0 : 0 ≤ L * (1 + 16 / s2) := by positivity
      rw [ha0def]; nlinarith
    have : L * (1 + 16 / s2) = L + 16 * L / s2 := by field_simp
    linarith
  have hax : 0 ≤ a0 * x := mul_nonneg ha0 (by linarith)
  have hmax : a0 * x ≤ max (ρ * √(N * L / 2) - L - 4 * L * (1 + α) ^ 2 / s2) 0 := hlin.trans (le_max_left _ _)
  have hsq : (a0 * x) ^ 2 ≤ (max (ρ * √(N * L / 2) - L - 4 * L * (1 + α) ^ 2 / s2) 0) ^ 2 :=
    pow_le_pow_left₀ hax hmax 2
  have hk : 0 ≤ s2 / (4 * L) := by positivity
  have := mul_le_mul_of_nonneg_left hsq hk
  have e : s2 * a0 ^ 2 / (4 * L) * x ^ 2 = s2 / (4 * L) * (a0 * x) ^ 2 := by ring
  rw [e]
  linarith

/-- The fitting constants: from `β⋆T_fit(η) ≤ D⋆`, with `Δ_φ ≤ 2κ`, `r₁ ≤ 1`: the size conditions (S) of Wave 30tz and
`τ⋆ − μ₁ ≥ Δ_φ s √r₁`. -/
lemma arith_fit {β κ Dφ r1 sfit Ds : ℝ} (hβ1 : 1 ≤ β) (hκ0 : 0 ≤ κ) (hD2 : Dφ ≤ 2 * κ) (hDφ0 : 0 ≤ Dφ) (hr10 : 0 < r1)
    (hr1 : r1 ≤ 1) (hsfit0 : 0 ≤ sfit) (h : β * (8 * (2 * (1 + √2) * κ + Dφ * sfit) * √r1) ≤ Ds) :
    β * Dφ * r1 ≤ Ds / 8 ∧ β ^ 2 * κ ^ 2 * r1 ≤ 7 * Ds ^ 2 / 64 ∧
      2 * (1 + √2) * κ * √r1 + Dφ * sfit * √r1 ≤ Ds / (8 * β) := by
  have hβ0 : 0 < β := by linarith
  have hsqr1 : 0 < √r1 := Real.sqrt_pos.2 hr10
  have hs2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hr1sq : r1 ≤ √r1 := by
    have := Real.sqrt_le_sqrt hr1
    rw [Real.sqrt_one] at this
    calc r1 = √r1 * √r1 := (Real.mul_self_sqrt hr10.le).symm
      _ ≤ √r1 * 1 := mul_le_mul_of_nonneg_left this hsqr1.le
      _ = √r1 := mul_one _
  have e : β * (8 * (2 * (1 + √2) * κ + Dφ * sfit) * √r1) =
      16 * (β * κ * √r1) + 16 * (√2 * (β * κ * √r1)) + 8 * (β * (Dφ * sfit * √r1)) := by ring
  have h1 : 0 ≤ √2 * (β * κ * √r1) := by positivity
  have h2 : 0 ≤ β * (Dφ * sfit * √r1) := by positivity
  have hF0 : 16 * (β * κ * √r1) ≤ Ds := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have hDr : Dφ * r1 ≤ 2 * κ * √r1 := mul_le_mul hD2 hr1sq hr10.le (by linarith)
    have : β * (Dφ * r1) ≤ β * (2 * κ * √r1) := mul_le_mul_of_nonneg_left hDr hβ0.le
    have e1 : β * Dφ * r1 = β * (Dφ * r1) := by ring
    have e2 : β * (2 * κ * √r1) = 2 * (β * κ * √r1) := by ring
    linarith
  · have h0 : 0 ≤ β * κ * √r1 := by positivity
    have h3 : (β * κ * √r1) ^ 2 ≤ (Ds / 16) ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
    have e3 : (β * κ * √r1) ^ 2 = β ^ 2 * κ ^ 2 * r1 := by rw [mul_pow, mul_pow, Real.sq_sqrt hr10.le]
    have e4 : (Ds / 16) ^ 2 = Ds ^ 2 / 256 := by ring
    have h5 : 0 ≤ Ds ^ 2 := sq_nonneg Ds
    linarith
  · rw [le_div_iff₀ (by positivity)]
    have e5 : (2 * (1 + √2) * κ * √r1 + Dφ * sfit * √r1) * (8 * β) =
        β * (8 * (2 * (1 + √2) * κ + Dφ * sfit) * √r1) := by ring
    linarith

/-- The betting constants: `β⋆T_bet(η,J′) ≤ D⋆ ≤ Δ_φ` gives `N ≥ 200L ≥ 8L`. -/
lemma arith_N {β Dφ Ds N L s2 ℓ : ℝ} (hβ1 : 1 ≤ β) (hDφ0 : 0 < Dφ) (hDsle : Ds ≤ Dφ) (hs20 : 0 < s2) (hs24 : s2 ≤ 4)
    (hL : 0 < L) (hN : 0 < N) (hℓ0 : 0 ≤ ℓ)
    (h : β * (2 * Dφ * √(2 / N) * ((1 + 16 / s2) * √L + 2 / √s2 * √ℓ)) ≤ Ds) : 8 * L ≤ N := by
  have h5 : 5 ≤ 1 + 16 / s2 := by
    have : 4 ≤ 16 / s2 := by rw [le_div_iff₀ hs20]; linarith
    linarith
  set u := √(2 / N) * √L with hu
  have hu0 : 0 ≤ u := by positivity
  have hW : 5 * √L ≤ (1 + 16 / s2) * √L + 2 / √s2 * √ℓ := by
    have : 0 ≤ 2 / √s2 * √ℓ := by positivity
    nlinarith [Real.sqrt_nonneg L]
  have hX0 : 0 ≤ 2 * Dφ * √(2 / N) * ((1 + 16 / s2) * √L + 2 / √s2 * √ℓ) := by
    have : 0 ≤ (1 + 16 / s2) * √L + 2 / √s2 * √ℓ := by positivity
    positivity
  have hX : 2 * Dφ * √(2 / N) * (5 * √L) ≤ 2 * Dφ * √(2 / N) * ((1 + 16 / s2) * √L + 2 / √s2 * √ℓ) :=
    mul_le_mul_of_nonneg_left hW (by positivity)
  have hβX := le_mul_of_one_le_left hX0 hβ1
  have h10 : 10 * Dφ * u ≤ Dφ := by
    have e : 2 * Dφ * √(2 / N) * (5 * √L) = 10 * Dφ * u := by rw [hu]; ring
    linarith
  have hu1 : u ≤ 1 / 10 := by
    have : Dφ * (10 * u) ≤ Dφ * 1 := by linarith
    have := le_of_mul_le_mul_left this hDφ0
    linarith
  have hsq : u ^ 2 = 2 * L / N := by
    rw [hu, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hL.le]; ring
  have : u ^ 2 ≤ (1 / 10) ^ 2 := pow_le_pow_left₀ hu0 hu1 2
  rw [hsq, div_le_iff₀ hN] at this
  linarith

/-- The excess margin: `a₀ = ϱ⋆√(NL/2) − L(1 + 16/σ²_min) ≥ (2/σ_min)√(L log(2J′/η))`, and then
`A = σ²_min a₀²/(4L) ≥ log(2J′/η)`. -/
lemma arith_a0 {β Dφ Ds N L s2 ℓ : ℝ} (hβ0 : 0 < β) (hDφ0 : 0 < Dφ) (hs20 : 0 < s2) (hL : 0 < L) (hN : 0 < N)
    (hℓ0 : 0 ≤ ℓ) (h : β * (2 * Dφ * √(2 / N) * ((1 + 16 / s2) * √L + 2 / √s2 * √ℓ)) ≤ Ds) :
    2 / √s2 * √(L * ℓ) ≤ Ds / (2 * β * Dφ) * √(N * L / 2) - L * (1 + 16 / s2) ∧
    ℓ ≤ s2 * (Ds / (2 * β * Dφ) * √(N * L / 2) - L * (1 + 16 / s2)) ^ 2 / (4 * L) := by
  set W := (1 + 16 / s2) * √L + 2 / √s2 * √ℓ with hWdef
  set S := √(N * L / 2) with hSdef
  have hsqN : √(2 / N) * S = √L := by
    rw [hSdef, ← Real.sqrt_mul (by positivity)]; congr 1; field_simp
  have h1 : √(2 / N) * W ≤ Ds / (2 * β * Dφ) := by
    rw [le_div_iff₀ (by positivity)]
    have e : √(2 / N) * W * (2 * β * Dφ) = β * (2 * Dφ * √(2 / N) * W) := by ring
    linarith
  have h2 : √(2 / N) * W * S ≤ Ds / (2 * β * Dφ) * S := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
  have h3 : √(2 / N) * W * S = √L * W := by
    calc √(2 / N) * W * S = W * (√(2 / N) * S) := by ring
      _ = √L * W := by rw [hsqN, mul_comm]
  have h4 : √L * W = L * (1 + 16 / s2) + 2 / √s2 * √(L * ℓ) := by
    rw [hWdef, Real.sqrt_mul hL.le]
    have : √L * √L = L := Real.mul_self_sqrt hL.le
    linear_combination (1 + 16 / s2) * this
  have ha0 : 2 / √s2 * √(L * ℓ) ≤ Ds / (2 * β * Dφ) * S - L * (1 + 16 / s2) := by linarith
  refine ⟨ha0, ?_⟩
  set a0 := Ds / (2 * β * Dφ) * S - L * (1 + 16 / s2)
  have hb0 : 0 ≤ 2 / √s2 * √(L * ℓ) := by positivity
  have h5 : (2 / √s2 * √(L * ℓ)) ^ 2 ≤ a0 ^ 2 := pow_le_pow_left₀ hb0 ha0 2
  have h6 : (2 / √s2 * √(L * ℓ)) ^ 2 = 4 * L * ℓ / s2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt hs20.le, Real.sq_sqrt (by positivity)]; ring
  rw [h6] at h5
  rw [le_div_iff₀ (by positivity)]
  have h7 := mul_le_mul_of_nonneg_left h5 hs20.le
  have e : s2 * (4 * L * ℓ / s2) = ℓ * (4 * L) := by field_simp
  linarith

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- **The lower side of Theorem 33** for a general excess profile (see the module docstring). -/
theorem core_lower (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ Dφ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) (hD2 : Dφ ≤ 2 * κ)
    {J n m : ℕ} {α : Fin J → ℝ} {δ s2 η : ℝ} {R : LoRun 𝒳 J n m} {B : ℕ}
    (hgrid : IsGrid α) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hs20 : 0 < s2) (hs24 : s2 ≤ 4)
    (hRun : R.IsWitnessRun φ α δ (1 / 2) s2) (hB : ∀ k, R.bat k ≤ B)
    (hn1 : 1 ≤ fitCard R.lx 1) (hm1 : 1 ≤ fitCard R.ly 1) (hr1 : rOne R.lx R.ly ≤ 1) (hN : 1 ≤ R.N)
    (hη0 : 0 < η) (hη1 : η < 1)
    {αs a Ds J' : ℝ} (x : Fin J → ℝ) (hαs1 : αs < 1) (haαs : a ≤ αs) (hDs : 0 < Ds)
    (hx : ∀ j, α j ≤ a → 1 ≤ x j ∧ Ds * x j ≤ Dpop φ P Q (α j))
    (hJ' : 1 ≤ J')
    (hfitc : beta αs * Tfit κ Dφ η (rOne R.lx R.ly) B ≤ Ds)
    (hbetc : beta αs * Tbet Dφ s2 (Real.log (1 / δ)) η J' R.N ≤ Ds)
    (hsum : ∀ A : ℝ, Real.log (2 * J' / η) ≤ A →
      ∑ j ∈ Finset.univ.filter (fun j => α j ≤ a), Real.exp (-(A * x j ^ 2)) ≤ J' * Real.exp (-A)) :
    sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < gridFloor α a} ≤ ENNReal.ofReal η := by
  classical
  obtain ⟨⟨hpair, hfitR, hfrac⟩, hwit, hlam⟩ := hRun
  set T := Finset.univ.filter (fun j : Fin J => α j ≤ a) with hTdef
  -- no level `≤ a`: the event is empty
  by_cases hTne : T.Nonempty
  swap
  · have : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | R.alphaLo α δ ω.1 ω.2 < gridFloor α a} = ∅ := by
      ext ω
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
      by_contra hlt
      obtain ⟨i, hi, -⟩ := Basic.exists_of_lt_gridFloor α (Limits.run_alphaLo_nonneg R hgrid δ ω.1 ω.2)
        (not_le.1 hlt)
      exact hTne ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
    rw [this, measure_empty]; exact bot_le
  obtain ⟨j0, hj0⟩ := hTne
  have hj0a : α j0 ≤ a := (Finset.mem_filter.1 hj0).2
  have hαj00 : 0 ≤ α j0 := (hgrid.2 j0).1
  have hαs0 : 0 ≤ αs := hαj00.trans (hj0a.trans haαs)
  obtain ⟨hx01, hx0D⟩ := hx j0 hj0a
  have hDsle : Ds ≤ Dφ := by
    have h1 : Ds ≤ Ds * x j0 := le_mul_of_one_le_right hDs.le hx01
    exact h1.trans (hx0D.trans (Basic.dpop_le_dphi P Q hφ hκ hDφ hαj00 (hgrid.2 j0).2))
  have hDφ0 : 0 < Dφ := hDs.trans_le hDsle
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
  set β := beta αs with hβdef
  have hβ1 : 1 ≤ β := one_le_beta' hαs0 hαs1
  have hβ0 : 0 < β := by linarith
  set L := Real.log (1 / δ) with hLdef
  have hL : 0 < L := by rw [hLdef, one_div, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  set r1 := rOne R.lx R.ly with hr1def
  have hn1r : (0 : ℝ) < fitCard R.lx 1 := by exact_mod_cast hn1
  have hm1r : (0 : ℝ) < fitCard R.ly 1 := by exact_mod_cast hm1
  have hr10 : 0 < r1 := by rw [hr1def]; unfold rOne; positivity
  -- batches: `1 ≤ bat k ≤ B`, fitting sizes `≥` those of batch 0
  have hbat1 : ∀ k, 1 ≤ R.bat k := hpair.2.2.1
  have hfit1 : ∀ k, 1 ≤ fitCard R.lx (R.bat k) ∧ 1 ≤ fitCard R.ly (R.bat k) := fun k =>
    ⟨hn1.trans (fitCard_mono _ (hbat1 k)), hm1.trans (fitCard_mono _ (hbat1 k))⟩
  have hfitr : ∀ k, 1 / (fitCard R.lx (R.bat k) : ℝ) + 1 / (fitCard R.ly (R.bat k) : ℝ) ≤ r1 := by
    intro k
    rw [hr1def]; unfold rOne
    have h1 : (fitCard R.lx 1 : ℝ) ≤ fitCard R.lx (R.bat k) := by exact_mod_cast fitCard_mono _ (hbat1 k)
    have h2 : (fitCard R.ly 1 : ℝ) ≤ fitCard R.ly (R.bat k) := by exact_mod_cast fitCard_mono _ (hbat1 k)
    exact add_le_add (one_div_le_one_div_of_le hn1r h1) (one_div_le_one_div_of_le hm1r h2)
  have hB1 : 1 ≤ B := (hbat1 ⟨0, hN⟩).trans (hB ⟨0, hN⟩)
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  -- the fitting constants
  set sfit := √(1 / 2 * Real.log (4 * B / η)) with hsfit
  have hlog4 : 0 ≤ Real.log (4 * B / η) := Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
  have hsfit0 : 0 ≤ sfit := Real.sqrt_nonneg _
  have hfit' : β * (8 * (2 * (1 + √2) * κ + Dφ * sfit) * √r1) ≤ Ds := hfitc
  obtain ⟨hS1, hS2, hτ'⟩ := arith_fit hβ1 hκ0 hD2 hDφ0.le hr10 hr1 hsfit0 hfit'
  set τ := Ds / (8 * β) with hτdef
  -- the fitting event
  set Efit := Lower.fitEvent P Q φ κ τ R.lx R.ly R.bat with hEdef
  have hEm : MeasurableSet Efit := Lower.measurableSet_fitEvent P Q hφ hκ τ hfit1
  have hfitP : sampleLaw P Q n m Efitᶜ ≤ ENNReal.ofReal (η / 2) := by
    refine (Lower.fitEvent_compl_le P Q hφ hκ hDφ hDφ0 τ r1 hbat1 hB hfit1 hfitr).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hy : Dφ * sfit * √r1 ≤ τ - 2 * (1 + √2) * κ * √r1 := by linarith
    have hy0 : 0 ≤ Dφ * sfit * √r1 := by have := Real.sqrt_nonneg r1; positivity
    have hmax : Dφ * sfit * √r1 ≤ max (τ - 2 * (1 + √2) * κ * √r1) 0 := hy.trans (le_max_left _ _)
    have hsq := pow_le_pow_left₀ hy0 hmax 2
    have hss : sfit ^ 2 = 1 / 2 * Real.log (4 * B / η) := Real.sq_sqrt (by positivity)
    have hval : 2 * (Dφ * sfit * √r1) ^ 2 / (Dφ ^ 2 * r1) = Real.log (4 * B / η) := by
      rw [mul_pow, mul_pow, hss, Real.sq_sqrt hr10.le]; field_simp
    have hexp : Real.exp (-(2 * (max (τ - 2 * (1 + √2) * κ * √r1) 0) ^ 2 / (Dφ ^ 2 * r1))) ≤ η / (4 * B) := by
      calc Real.exp (-(2 * (max (τ - 2 * (1 + √2) * κ * √r1) 0) ^ 2 / (Dφ ^ 2 * r1)))
          ≤ Real.exp (-(2 * (Dφ * sfit * √r1) ^ 2 / (Dφ ^ 2 * r1))) := by
            refine Real.exp_le_exp.2 (neg_le_neg ?_)
            exact div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ = η / (4 * B) := by
            rw [hval, Real.exp_neg, Real.exp_log (by positivity), inv_div]
    calc 2 * (B : ℝ) * Real.exp (-(2 * (max (τ - 2 * (1 + √2) * κ * √r1) 0) ^ 2 / (Dφ ^ 2 * r1)))
        ≤ 2 * B * (η / (4 * B)) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = η / 2 := by field_simp; ring
  -- the betting constants
  set ℓ := Real.log (2 * J' / η) with hℓdef
  have hℓ : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hη0]; nlinarith)
  have hℓ0 : 0 ≤ ℓ := le_trans (Real.log_nonneg (by norm_num)) hℓ
  have hNr : (1 : ℝ) ≤ R.N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < R.N := by linarith
  have hbet' : β * (2 * Dφ * √(2 / R.N) * ((1 + 16 / s2) * √L + 2 / √s2 * √ℓ)) ≤ Ds := hbetc
  have hN8 : 8 * L ≤ R.N := arith_N hβ1 hDφ0 hDsle hs20 hs24 hL hNpos hℓ0 hbet'
  obtain ⟨ha0, hA⟩ := arith_a0 hβ0 hDφ0 hs20 hL hNpos hℓ0 hbet'
  set ρs := Ds / (2 * β * Dφ) with hρsdef
  set a0 := ρs * √(R.N * L / 2) - L * (1 + 16 / s2) with ha0def
  have ha00 : 0 ≤ a0 := le_trans (by positivity) ha0
  set A := s2 * a0 ^ 2 / (4 * L) with hAdef
  -- one level
  have hlevel : ∀ j ∈ T, sampleLaw P Q n m (Efit ∩ {ω | ¬ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2}) ≤
      ENNReal.ofReal (Real.exp (-(A * x j ^ 2))) := by
    intro j hj
    have hja : α j ≤ a := (Finset.mem_filter.1 hj).2
    obtain ⟨hxj1, hxjD⟩ := hx j hja
    have hαj0 : 0 ≤ α j := (hgrid.2 j).1
    have hαj1 : α j < 1 := (hgrid.2 j).2
    have hjs : α j ≤ αs := hja.trans haαs
    set Dj := Dpop φ P Q (α j) with hDjdef
    have hDsDj : Ds ≤ Dj := (le_mul_of_one_le_right hDs.le hxj1).trans hxjD
    have hDj : 0 < Dj := hDs.trans_le hDsDj
    have hS1j : beta αs * Dφ * r1 ≤ Dj / 8 := hS1.trans (by linarith)
    have hS2j : beta αs ^ 2 * κ ^ 2 * r1 ≤ 7 * Dj ^ 2 / 64 := by
      have := pow_le_pow_left₀ hDs.le hDsDj 2
      linarith
    have hτj : τ ≤ Dj / (8 * beta αs) := div_le_div_of_nonneg_right hDsDj (by positivity)
    have hlo0 : 0 ≤ lamLo (1 / 2) (α j) L s2 R.N :=
      le_min (div_pos (by norm_num) (by linarith)).le (Real.sqrt_nonneg _)
    have hE : ∀ ω ∈ Efit, ∀ k : Fin R.N,
        lamLo (1 / 2) (α j) L s2 R.N ≤ fracAt (R.lam j) (R.g j) R.bat R.A R.B ω.1 ω.2 k ∧
        α j + Dj / (2 * beta αs * Dφ) ≤ condMean P Q (R.g j) R.bat ω.1 ω.2 k := by
      intro ω hω k
      obtain ⟨hZk, hZmk⟩ := hω k
      obtain ⟨hhas, hexc⟩ := Lower.witness_step P Q hφ hκ hDφ hDφ0 (hfit1 k).1 (hfit1 k).2
        (fitSample R.lx (R.bat k) ω.1) (fitSample R.ly (R.bat k) ω.2) hαj0 hjs hαs1 hDj le_rfl (hfitr k)
        hS1j hS2j (hZk.trans hτj) (hZmk.trans hτj) (hwit j k ω.1 ω.2)
      exact ⟨(hlam j k ω.1 ω.2 (past (pairStat (R.g j) R.bat R.A R.B ω.1 ω.2) k)).2.1 hhas
        fun l => Bet.pairStat_mem hpair (hfitR j) (Fin.castLE k.isLt.le l) ω.1 ω.2, hexc⟩
    have h1αj : 0 < 1 + α j := by linarith
    have hhicap : lamHi (1 / 2) (α j) L s2 R.N ≤ 1 / 2 / (1 + α j) := min_le_left _ _
    have hha : lamHi (1 / 2) (α j) L s2 R.N * (1 + α j) ≤ 1 / 2 := by rwa [le_div_iff₀ h1αj] at hhicap
    have hρj : 0 < Dj / (2 * beta αs * Dφ) := by positivity
    refine (bet_power_route 𝒳 P Q n m R.N R.lx R.ly R.bat R.A R.B (α j) δ (1 / 2)
      (lamLo (1 / 2) (α j) L s2 R.N) (lamHi (1 / 2) (α j) L s2 R.N) (1 / 2)
      (Dj / (2 * beta αs * Dφ)) (R.g j) (R.lam j) _ hpair hαj0 hδ0 hδ1 (by norm_num) (by norm_num) (hfitR j)
      (hfrac j) (fun k x y z => (hlam j k x y z).1) hha (by norm_num) hlo0 hρj hEm hE).trans
      (ENNReal.ofReal_le_ofReal ?_)
    refine (Lower.bet_arith hN (by norm_num) le_rfl hs20 hL hαj0 le_rfl).trans ?_
    refine genEps_le s2 L (α j) _ ρs (x j) R.N hs20 hs24 hL hαj0 hαj1 hN8 hxj1 ?_ ha00
    -- `ϱ⋆ x_j ≤ ϱ_j`
    rw [hρsdef, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hxjD (by positivity)
  -- the union bound
  have hsub : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | R.alphaLo α δ ω.1 ω.2 < gridFloor α a} ⊆
      Efitᶜ ∪ ⋃ j ∈ T, (Efit ∩ {ω | ¬ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2}) := by
    intro ω hω
    obtain ⟨i0, hi0a, hi0lt⟩ := Basic.exists_of_lt_gridFloor α (Limits.run_alphaLo_nonneg R hgrid δ ω.1 ω.2) hω
    obtain ⟨j, hj, hnr⟩ := (grid_events_route J α
      (fun j => rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2) 0 hgrid).2 i0 hi0lt
    have hjT : j ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ _, (hgrid.1.monotone hj).trans hi0a⟩
    by_cases hωE : ω ∈ Efit
    · exact Or.inr (mem_iUnion₂.2 ⟨j, hjT, hωE, hnr⟩)
    · exact Or.inl hωE
  have hsumA := hsum A hA
  have hexpA : J' * Real.exp (-A) ≤ η / 2 := by
    calc J' * Real.exp (-A) ≤ J' * Real.exp (-ℓ) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith))
          (by linarith)
      _ = η / 2 := by
          rw [hℓdef, Real.exp_neg, Real.exp_log (by positivity), inv_div]; field_simp
  calc sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < gridFloor α a}
      ≤ sampleLaw P Q n m Efitᶜ + sampleLaw P Q n m
          (⋃ j ∈ T, (Efit ∩ {ω | ¬ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2})) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (η / 2) + ∑ j ∈ T, ENNReal.ofReal (Real.exp (-(A * x j ^ 2))) :=
        add_le_add hfitP ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hlevel))
    _ = ENNReal.ofReal (η / 2) + ENNReal.ofReal (∑ j ∈ T, Real.exp (-(A * x j ^ 2))) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal (hsumA.trans hexpA))
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end Core

end StatFormal.Wave31tl
