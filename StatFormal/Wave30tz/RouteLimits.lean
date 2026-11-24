import StatFormal.Wave30tz.RouteIface
import StatFormal.Wave30tz.RouteElem
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs

/-!
# Wave 30tz route: the limits of Proposition 1 from four black-box inputs (untrusted)

Every limit claim of Proposition 1 is derived here as an implication from (a subset of)
`Iface.CoreLowerBound` (the lower-side bound of §5 at every floor), `Iface.DpopAntitone`
(`α ↦ D_α` is nonincreasing), `Claims.lo_upper` (the upper side at every `n, m`) and
`Claims.lo_strict_bound` (the strict-null bound).

* `Limits.fit_term_small`, `Limits.genEps_small`, `Limits.strict_term_small`: the three terms
  of §5 are eventually small (the fitting term as `r → 0`; the betting term `genEps(λ_N)`
  as `N → ∞` with `0 < L ≤ ηN`, where `λ_N = √(2L/(N max(σ²_min,4)))`; the strict-null term
  as `N → ∞` with `L ≥ L₀ > 0`);
* `Limits.core_eventually`: `P(α̂_lo < α_i) → 0` uniformly over the pairs with `D_{α_i} ≥ d`
  and the levels `α_i ≤ a₀ < 1` of grids with `log|𝒢_{n,m}| = o(min(n,m))`, for levels with
  `log(1/δ_{n,m}) = o(min(n,m))` and runs in the asymptotic regime (`D_φ > 0` is forced by
  `D_{α_i} ≥ d > 0`: a constant feature map has `D_α = 0`);
* `Limits.upper_eventually`: `P(α̂_lo > TV + ε) → 0` (the strict-null bound at the one-level
  sub-run of the first level `≥ TV + ε/2`, which `α̂_lo > TV + ε` requires to be rejected);
* the targets `lo_lower_of`, `lo_consistency_of`, `lo_exact_of`, `lo_vanishing_of`,
  `lo_refining_kernel_of`, `lo_refining_of`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.Wave30tz

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tp StatFormal.TrimmedMMD.Unconditional
open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.ZeroSet

namespace Limits

/-! ### Elementary analysis -/

/-- `exp(−x) ≤ 1/x` for `x > 0`. -/
lemma exp_neg_le_one_div {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le hx (by linarith [Real.add_one_le_exp x])

lemma ceil_le_cast {x : ℝ} {n : ℕ} (h : ⌈x⌉₊ ≤ n) : x ≤ n := (Nat.le_ceil x).trans (Nat.cast_le.2 h)

/-- The fitting term of §5 is small for small `r`, uniformly over `τ ≥ τ₀`. -/
lemma fit_term_small (B κ Dφ τ₀ ε : ℝ) (hB : 0 ≤ B) (hτ₀ : 0 < τ₀) (hDφ : 0 < Dφ) (hε : 0 < ε) :
    ∃ r₀ > 0, ∀ r τ : ℝ, 0 < r → r ≤ r₀ → τ₀ ≤ τ →
      2 * B * Real.exp (-(2 * (max (τ - 2 * (1 + √2) * κ * √r) 0) ^ 2 / (Dφ ^ 2 * r))) ≤ ε := by
  refine ⟨min (ε * τ₀ ^ 2 / (4 * (B + 1) * Dφ ^ 2)) ((τ₀ / (12 * (|κ| + 1))) ^ 2), by positivity, ?_⟩
  intro r τ hr hrr₀ hτ
  have hr1 : r ≤ ε * τ₀ ^ 2 / (4 * (B + 1) * Dφ ^ 2) := hrr₀.trans (min_le_left _ _)
  have hr2 : r ≤ (τ₀ / (12 * (|κ| + 1))) ^ 2 := hrr₀.trans (min_le_right _ _)
  have hk1 : 0 < |κ| + 1 := by positivity
  have hsq : √r ≤ τ₀ / (12 * (|κ| + 1)) := by
    calc √r ≤ √((τ₀ / (12 * (|κ| + 1))) ^ 2) := Real.sqrt_le_sqrt hr2
      _ = τ₀ / (12 * (|κ| + 1)) := Real.sqrt_sq (by positivity)
  have hs2 : √2 ≤ 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hsr : 0 ≤ √r := Real.sqrt_nonneg r
  have hμ : 2 * (1 + √2) * κ * √r ≤ τ₀ / 2 := by
    have e1 : κ * √r ≤ |κ| * √r := mul_le_mul_of_nonneg_right (le_abs_self κ) hsr
    have e2 : 0 ≤ |κ| * √r := mul_nonneg (abs_nonneg κ) hsr
    have e3 : (|κ| + 1) * √r ≤ (|κ| + 1) * (τ₀ / (12 * (|κ| + 1))) := mul_le_mul_of_nonneg_left hsq hk1.le
    have e4 : (|κ| + 1) * (τ₀ / (12 * (|κ| + 1))) = τ₀ / 12 := by field_simp
    have e5 : 2 * (1 + √2) * κ * √r = 2 * (1 + √2) * (κ * √r) := by ring
    rw [e5]
    nlinarith [Real.sqrt_nonneg 2]
  have hX : τ₀ / 2 ≤ max (τ - 2 * (1 + √2) * κ * √r) 0 := (by linarith : τ₀ / 2 ≤ _).trans (le_max_left _ _)
  have hX2 : (τ₀ / 2) ^ 2 ≤ (max (τ - 2 * (1 + √2) * κ * √r) 0) ^ 2 := pow_le_pow_left₀ (by positivity) hX 2
  have hy : 0 < τ₀ ^ 2 / (2 * Dφ ^ 2 * r) := by positivity
  have hexp : Real.exp (-(2 * (max (τ - 2 * (1 + √2) * κ * √r) 0) ^ 2 / (Dφ ^ 2 * r))) ≤
      2 * Dφ ^ 2 * r / τ₀ ^ 2 := by
    calc Real.exp (-(2 * (max (τ - 2 * (1 + √2) * κ * √r) 0) ^ 2 / (Dφ ^ 2 * r)))
        ≤ Real.exp (-(τ₀ ^ 2 / (2 * Dφ ^ 2 * r))) := by
          rw [Real.exp_le_exp, neg_le_neg_iff]
          have e : τ₀ ^ 2 / (2 * Dφ ^ 2 * r) = 2 * (τ₀ / 2) ^ 2 / (Dφ ^ 2 * r) := by
            field_simp
            try ring
          rw [e]
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ 1 / (τ₀ ^ 2 / (2 * Dφ ^ 2 * r)) := exp_neg_le_one_div hy
      _ = 2 * Dφ ^ 2 * r / τ₀ ^ 2 := by rw [one_div_div]
  have hBexp : 2 * B * Real.exp (-(2 * (max (τ - 2 * (1 + √2) * κ * √r) 0) ^ 2 / (Dφ ^ 2 * r))) ≤
      2 * (B + 1) * (2 * Dφ ^ 2 * r / τ₀ ^ 2) := by
    have h0 : 0 ≤ Real.exp (-(2 * (max (τ - 2 * (1 + √2) * κ * √r) 0) ^ 2 / (Dφ ^ 2 * r))) := (Real.exp_pos _).le
    calc 2 * B * Real.exp (-(2 * (max (τ - 2 * (1 + √2) * κ * √r) 0) ^ 2 / (Dφ ^ 2 * r)))
        ≤ 2 * (B + 1) * Real.exp (-(2 * (max (τ - 2 * (1 + √2) * κ * √r) 0) ^ 2 / (Dφ ^ 2 * r))) := by
          nlinarith
      _ ≤ 2 * (B + 1) * (2 * Dφ ^ 2 * r / τ₀ ^ 2) := mul_le_mul_of_nonneg_left hexp (by positivity)
  refine hBexp.trans ?_
  have e : 2 * (B + 1) * (2 * Dφ ^ 2 * r / τ₀ ^ 2) = r * (4 * (B + 1) * Dφ ^ 2) / τ₀ ^ 2 := by ring
  rw [e, div_le_iff₀ (by positivity)]
  rw [le_div_iff₀ (by positivity)] at hr1
  linarith

/-- The betting term with the lower fraction `λ_N` is exponentially small once `0 < L ≤ ηN`, uniformly over
`ϱ ≥ ϱ₀` and `α ∈ [0,1)`: `genEps(σ²_min, α, L, N, ϱ, λ_N) ≤ exp(−K N)`. -/
lemma genEps_small (s2 lmax ρ₀ : ℝ) (hs2 : 0 < s2) (hl : 0 < lmax) (hρ₀ : 0 < ρ₀) :
    ∃ η > 0, ∃ K > 0, ∀ (α : ℝ) (N : ℕ) (L ρ : ℝ), 0 ≤ α → α < 1 → 0 < L → L ≤ η * N → ρ₀ ≤ ρ →
      genEps s2 α L N ρ (lamLo lmax α L s2 N) ≤ Real.exp (-(K * N)) := by
  set M : ℝ := max s2 4 with hM
  have hM4 : 4 ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  set C₁ : ℝ := 1 + 16 / s2 with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  refine ⟨min (ρ₀ ^ 2 / (2 * M * C₁ ^ 2)) (lmax ^ 2 * M / 16), by positivity, s2 * ρ₀ ^ 2 / (8 * M), by positivity, ?_⟩
  intro α N L ρ hα0 hα1 hL hLN hρ
  have hLN1 : L ≤ ρ₀ ^ 2 / (2 * M * C₁ ^ 2) * N := hLN.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have hLN2 : L ≤ lmax ^ 2 * M / 16 * N := hLN.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  have hN : (0 : ℝ) < N := by
    rcases (Nat.cast_nonneg N : (0 : ℝ) ≤ N).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hLN; linarith
  set b : ℝ := √(2 * L / (N * M)) with hb
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = 2 * L / (N * M) := Real.sq_sqrt (by positivity)
  have ha0 : 0 < lmax / (1 + α) := by positivity
  have hba : b ≤ lmax / (1 + α) := by
    have h1 : b ^ 2 ≤ (lmax / (1 + α)) ^ 2 := by
      rw [hb2, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : (1 + α) ^ 2 ≤ 4 := by nlinarith
      have h5 : L * 16 ≤ lmax ^ 2 * M * N := by
        have := hLN2; rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)] at this; linarith
      have h7 : 2 * L * (1 + α) ^ 2 ≤ 2 * L * 4 := mul_le_mul_of_nonneg_left h4 (by positivity)
      have e : lmax ^ 2 * (N * M) = lmax ^ 2 * M * N := by ring
      rw [e]
      linarith
    exact (pow_le_pow_iff_left₀ hb0 ha0.le two_ne_zero).1 h1
  have hlo : lamLo lmax α L s2 N = b := by
    unfold lamLo; rw [← hb]; exact min_eq_right hba
  rw [hlo]
  unfold genEps
  set s : ℝ := N * b with hs
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hs2' : s ^ 2 = 2 * L * N / M := by
    rw [hs, mul_pow, hb2]; field_simp
  set C : ℝ := 1 + 4 * (1 + α) ^ 2 / s2 with hC
  have hCC : C ≤ C₁ := by
    rw [hC, hC₁]
    have h4 : (1 + α) ^ 2 ≤ 4 := by nlinarith
    have : 4 * (1 + α) ^ 2 / s2 ≤ 16 / s2 := div_le_div_of_nonneg_right (by linarith) hs2.le
    linarith
  have hC0 : 0 < C := by rw [hC]; positivity
  have h3 : L * C₁ ^ 2 ≤ ρ₀ ^ 2 * N / (2 * M) := by
    have := mul_le_mul_of_nonneg_right hLN1 (sq_nonneg C₁)
    calc L * C₁ ^ 2 ≤ ρ₀ ^ 2 / (2 * M * C₁ ^ 2) * N * C₁ ^ 2 := this
      _ = ρ₀ ^ 2 * N / (2 * M) := by field_simp
  have hρs : 0 ≤ ρ₀ * s / 2 := by positivity
  have hLC : L * C ≤ ρ₀ * s / 2 := by
    have hCsq : C ^ 2 ≤ C₁ ^ 2 := pow_le_pow_left₀ hC0.le hCC 2
    have h1 : (L * C) ^ 2 ≤ (ρ₀ * s / 2) ^ 2 := by
      calc (L * C) ^ 2 = L ^ 2 * C ^ 2 := mul_pow L C 2
        _ ≤ L ^ 2 * C₁ ^ 2 := mul_le_mul_of_nonneg_left hCsq (sq_nonneg L)
        _ = L * (L * C₁ ^ 2) := by ring
        _ ≤ L * (ρ₀ ^ 2 * N / (2 * M)) := mul_le_mul_of_nonneg_left h3 hL.le
        _ = ρ₀ ^ 2 * (2 * L * N / M) / 4 := by field_simp; ring
        _ = (ρ₀ * s / 2) ^ 2 := by rw [← hs2']; ring
    exact (pow_le_pow_iff_left₀ (by positivity) hρs two_ne_zero).1 h1
  have hX : ρ₀ * s / 2 ≤ s * ρ - L - 4 * L * (1 + α) ^ 2 / s2 := by
    have h1 : s * ρ₀ ≤ s * ρ := mul_le_mul_of_nonneg_left hρ hs0
    have h2 : L + 4 * L * (1 + α) ^ 2 / s2 = L * C := by rw [hC]; ring
    linarith
  have hmax : ρ₀ * s / 2 ≤ max (s * ρ - L - 4 * L * (1 + α) ^ 2 / s2) 0 := hX.trans (le_max_left _ _)
  have hsq : (ρ₀ * s / 2) ^ 2 ≤ (max (s * ρ - L - 4 * L * (1 + α) ^ 2 / s2) 0) ^ 2 :=
    pow_le_pow_left₀ hρs hmax 2
  rw [Real.exp_le_exp]
  have e : s2 * ρ₀ ^ 2 / (8 * M) * N = s2 / (4 * L) * (ρ₀ * s / 2) ^ 2 := by
    rw [div_pow, mul_pow, hs2']; field_simp; ring
  rw [e, neg_mul, neg_le_neg_iff]
  have hsL : 0 ≤ s2 / (4 * L) := by positivity
  exact mul_le_mul_of_nonneg_left hsq hsL

/-- The strict-null term `exp(−ζ σ_min √(2NL))` is small for large `N`, uniformly over `L ≥ L₀ > 0`. -/
lemma strict_term_small (ζ s2 L₀ ε : ℝ) (hζ : 0 < ζ) (hs2 : 0 < s2) (hL₀ : 0 < L₀) (hε : 0 < ε) :
    ∃ T : ℝ, ∀ (N : ℕ) (L : ℝ), T ≤ N → L₀ ≤ L → Real.exp (-(ζ * √s2 * √(2 * N * L))) ≤ ε := by
  refine ⟨1 / (ε ^ 2 * ζ ^ 2 * s2 * 2 * L₀), ?_⟩
  intro N L hN hL
  have hT : 0 < 1 / (ε ^ 2 * ζ ^ 2 * s2 * 2 * L₀) := by positivity
  have hN0 : (0 : ℝ) < N := hT.trans_le hN
  have hL0 : 0 < L := hL₀.trans_le hL
  set x : ℝ := ζ * √s2 * √(2 * N * L) with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx2 : x ^ 2 = ζ ^ 2 * s2 * (2 * N * L) := by
    rw [hx, mul_pow, mul_pow, Real.sq_sqrt hs2.le, Real.sq_sqrt (by positivity)]
  have hx1 : 1 / ε ≤ x := by
    have h1 : (1 / ε) ^ 2 ≤ x ^ 2 := by
      rw [hx2]
      have h2 : 1 / (ε ^ 2 * ζ ^ 2 * s2 * 2 * L₀) * L₀ ≤ N * L :=
        mul_le_mul hN hL hL₀.le (Nat.cast_nonneg _)
      have e : 1 / (ε ^ 2 * ζ ^ 2 * s2 * 2 * L₀) * L₀ = (1 / ε) ^ 2 / (ζ ^ 2 * s2 * 2) := by
        field_simp
      rw [e, div_le_iff₀ (by positivity)] at h2
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) hx0 two_ne_zero).1 h1
  have hxpos : 0 < x := (by positivity : (0 : ℝ) < 1 / ε).trans_le hx1
  calc Real.exp (-x) ≤ 1 / x := exp_neg_le_one_div hxpos
    _ ≤ 1 / (1 / ε) := one_div_le_one_div_of_le (by positivity) hx1
    _ = ε := one_div_one_div ε

/-- A constant is `o(min(n,m))`. -/
lemma const_small (x : ℝ) : ∀ η > 0, ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m → x ≤ η * ((min n m : ℕ) : ℝ) := by
  intro η hη
  refine ⟨⌈x / η⌉₊, fun n m hn hm => ?_⟩
  have h := ceil_le_cast (le_min hn hm)
  rw [div_le_iff₀ hη] at h
  linarith

/-! ### The grid, `α̂_lo`, `D_α` -/

lemma sampleLaw_isProb {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (n m : ℕ) : IsProbabilityMeasure (sampleLaw P Q n m) := by
  unfold sampleLaw; infer_instance

lemma alphaLo_nonneg {J : ℕ} {α : Fin J → ℝ} (hg : IsGrid α) (rej : Fin J → Prop) :
    0 ≤ StatFormal.TrimmedMMD.Lower.alphaLo α rej := by
  classical
  unfold StatFormal.TrimmedMMD.Lower.alphaLo
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    exact (hg.2 j).1.trans (Finset.le_sup' α hj)
  · exact le_rfl

lemma run_alphaLo_nonneg {𝒳 : Type*} [MeasurableSpace 𝒳] {J n m : ℕ} (R : LoRun 𝒳 J n m) {α : Fin J → ℝ}
    (hg : IsGrid α) (δ : ℝ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) : 0 ≤ R.alphaLo α δ x y :=
  alphaLo_nonneg hg _

lemma le_alphaLo {J : ℕ} (α : Fin J → ℝ) (rej : Fin J → Prop) (j : Fin J) (h : ∀ i ≤ j, rej i) :
    α j ≤ StatFormal.TrimmedMMD.Lower.alphaLo α rej := by
  classical
  unfold StatFormal.TrimmedMMD.Lower.alphaLo
  split_ifs with hF
  · exact Finset.le_sup' α (by simpa using h)
  · exact absurd ⟨j, by simpa using h⟩ hF

lemma gridBelow_lt {J : ℕ} (α : Fin J → ℝ) {a : ℝ} (ha : 0 < a) : gridBelow α a < a := by
  classical
  unfold gridBelow
  split_ifs with h
  · rw [Finset.sup'_lt_iff]
    intro j hj
    exact (Finset.mem_filter.1 hj).2
  · exact ha

lemma gridBelow_spec {J : ℕ} (α : Fin J → ℝ) (a : ℝ) :
    (∃ j, α j < a ∧ gridBelow α a = α j) ∨ ((∀ j, a ≤ α j) ∧ gridBelow α a = 0) := by
  classical
  unfold gridBelow
  split_ifs with h
  · left
    obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup' h α
    exact ⟨j, (Finset.mem_filter.1 hj).2, he⟩
  · right
    refine ⟨fun j => ?_, rfl⟩
    by_contra hc
    exact h ⟨j, by simpa using not_le.1 hc⟩

lemma Dpop_nonneg {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H)
    (P Q : Measure 𝒳) (α : ℝ) : 0 ≤ Dpop φ P Q α := by
  unfold Dpop setDist
  exact Real.sInf_nonneg (by rintro _ ⟨a, -, b, -, rfl⟩; exact norm_nonneg _)

/-- A constant feature map has `D_α = 0` (so `D_α > 0` forces `D_φ > 0`). -/
lemma Dpop_nonpos_of_const {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (φ : 𝒳 → H) (P Q : Measure 𝒳) [IsProbabilityMeasure P] (α : ℝ) (h : ∀ x x', φ x = φ x') :
    Dpop φ P Q α ≤ 0 := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have hreg : ∀ (μ : Measure 𝒳), ∀ z ∈ region φ α μ, z = φ x₀ := by
    rintro μ z ⟨g, -, -, hg1, rfl⟩
    have : (fun x => g x • φ x) = fun x => g x • φ x₀ := funext fun x => by rw [h x x₀]
    rw [this, integral_smul_const, hg1, one_smul]
  unfold Dpop setDist
  refine Real.sInf_nonpos ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  rw [hreg P a ha, hreg Q b hb, sub_self, norm_zero]

/-- The one-level sub-run of level `i`. -/
def subRun {𝒳 : Type*} {J n m : ℕ} (R : LoRun 𝒳 J n m) (i : Fin J) : LoRun 𝒳 1 n m :=
  ⟨R.lx, R.ly, R.N, R.bat, R.A, R.B, fun _ => R.has i, fun _ => R.g i, fun _ => R.lam i⟩

lemma isGrid_one {a : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) : IsGrid (fun _ : Fin 1 => a) :=
  ⟨fun x y hxy => absurd hxy (by rw [Subsingleton.elim x y]; exact lt_irrefl _), fun _ => ⟨h0, h1⟩⟩

/-- `P(E₁ ∪ E₂)ᶜ`-bound: if `P(f < c) ≤ a` and `P(f > c) ≤ b`, then `P(f = c) ≥ 1 − (a + b)`. -/
lemma prob_eq_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (c a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : μ {ω | f ω < c} ≤ ENNReal.ofReal a)
    (h2 : μ {ω | c < f ω} ≤ ENNReal.ofReal b) : ENNReal.ofReal (1 - (a + b)) ≤ μ {ω | f ω = c} := by
  have hS : MeasurableSet {ω | f ω = c} := hf (measurableSet_singleton c)
  have hc : μ {ω | f ω = c}ᶜ ≤ ENNReal.ofReal (a + b) := by
    have hsub : {ω | f ω = c}ᶜ ⊆ {ω | f ω < c} ∪ {ω | c < f ω} := by
      intro ω hω
      simp only [mem_compl_iff, mem_ofPred_eq] at hω
      rcases lt_or_gt_of_ne hω with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc μ {ω | f ω = c}ᶜ ≤ μ ({ω | f ω < c} ∪ {ω | c < f ω}) := measure_mono hsub
      _ ≤ μ {ω | f ω < c} + μ {ω | c < f ω} := measure_union_le _ _
      _ ≤ ENNReal.ofReal a + ENNReal.ofReal b := add_le_add h1 h2
      _ = ENNReal.ofReal (a + b) := (ENNReal.ofReal_add ha hb).symm
  have he := prob_compl_eq_one_sub (μ := μ) hS.compl
  rw [compl_compl] at he
  rw [he, ENNReal.ofReal_sub _ (add_nonneg ha hb), ENNReal.ofReal_one]
  exact tsub_le_tsub_left hc 1

/-! ### The lower side: `P(α̂_lo < α_i) → 0` uniformly -/

/-- **The lower side, eventually.** For grids `𝒢_{n,m}` with `log|𝒢_{n,m}| = o(min(n,m))`, levels with
`log(1/δ_{n,m}) = o(min(n,m))` and runs of Proposition 1 in the asymptotic regime: for every `d > 0`, `a₀ < 1`, `ε > 0`,
eventually `P(α̂_lo < α_i) ≤ ε` for all pairs `(P,Q)` and all levels `α_i ≤ a₀` with `D_{α_i}(P,Q) ≥ d`. -/
theorem core_eventually (hcore : Iface.CoreLowerBound) {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ)
    (J : ℕ → ℕ → ℕ) (α : ∀ n m, Fin (J n m) → ℝ) (δ : ℕ → ℕ → ℝ) (lmax s2 c C0 : ℝ) (Bmax : ℕ)
    (R : ∀ n m : ℕ, LoRun 𝒳 (J n m) n m)
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ)
    (hgrid : ∀ n m, IsGrid (α n m)) (hδ : ∀ n m, 0 < δ n m ∧ δ n m < 1)
    (hL : ∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → Real.log (1 / δ n m) ≤ η * (min n m : ℕ))
    (hJ : ∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → Real.log (J n m) ≤ η * (min n m : ℕ))
    (hl0 : 0 < lmax) (hl1 : lmax ≤ 1 / 2) (hs2 : 0 < s2) (hc : 0 < c)
    (hR : ∀ n m, (R n m).IsWitnessRun φ (α n m) (δ n m) lmax s2 ∧ (R n m).IsSizedRun c C0 Bmax)
    (d a₀ : ℝ) (hd : 0 < d) (ha₀ : a₀ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → ∀ (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (i : Fin (J n m)), α n m i ≤ a₀ → d ≤ Dpop φ P Q (α n m i) →
        sampleLaw P Q n m {ω | (R n m).alphaLo (α n m) (δ n m) ω.1 ω.2 < α n m i} ≤ ENNReal.ofReal ε := by
  rcases le_or_gt Dφ 0 with hD0 | hDpos
  · refine ⟨0, fun n m _ _ P Q _ _ i _ hdi => absurd hdi (not_le.2 (lt_of_le_of_lt ?_ hd))⟩
    refine Dpop_nonpos_of_const φ P Q _ fun x x' => ?_
    exact sub_eq_zero.1 (norm_le_zero_iff.1 ((hDφ x x').trans hD0))
  set β₀ : ℝ := 1 / (1 - a₀) with hβ₀
  have hβ₀pos : 0 < β₀ := one_div_pos.2 (by linarith)
  obtain ⟨r₁, hr₁, hfit⟩ := fit_term_small (Bmax : ℝ) κ Dφ (d / (8 * β₀)) (ε / 2) (Nat.cast_nonneg _)
    (by positivity) hDpos (by positivity)
  set r₀ : ℝ := min r₁ (min (d / (8 * β₀ * Dφ)) (7 * d ^ 2 / (64 * β₀ ^ 2 * (κ ^ 2 + 1)))) with hr₀
  have hr₀pos : 0 < r₀ := lt_min hr₁ (lt_min (by positivity) (by positivity))
  obtain ⟨η₀, hη₀, K, hK, hgen⟩ := genEps_small s2 lmax (d / (2 * β₀ * Dφ)) hs2 hl0 (by positivity)
  obtain ⟨NL, hNL⟩ := hL (η₀ * c / 2) (by positivity)
  obtain ⟨NJ, hNJ⟩ := hJ (K * c / 4) (by positivity)
  set A1 : ℕ := ⌈(C0 + max 1 (2 / r₀)) / c⌉₊ with hA1
  set A2 : ℕ := ⌈2 * C0 / c⌉₊ with hA2
  set A3 : ℕ := ⌈4 * Real.log (2 / ε) / (K * c)⌉₊ with hA3
  refine ⟨max (max A1 A2) (max A3 (max NL NJ)), ?_⟩
  intro n m hn hm P Q _ _ i hia hdi
  have hn' : max (max A1 A2) (max A3 (max NL NJ)) ≤ n := hn
  have hm' : max (max A1 A2) (max A3 (max NL NJ)) ≤ m := hm
  set Nmin : ℝ := ((min n m : ℕ) : ℝ) with hNmin
  have hmin2 : 2 * C0 / c ≤ Nmin := ceil_le_cast (le_min (by omega) (by omega))
  have hmin4 : 4 * Real.log (2 / ε) / (K * c) ≤ Nmin := ceil_le_cast (le_min (by omega) (by omega))
  have hn1 : (C0 + max 1 (2 / r₀)) / c ≤ n := ceil_le_cast (by omega)
  have hm1 : (C0 + max 1 (2 / r₀)) / c ≤ m := ceil_le_cast (by omega)
  have hLnm := hNL n m (by omega) (by omega)
  have hJnm := hNJ n m (by omega) (by omega)
  obtain ⟨hW, hS⟩ := hR n m
  obtain ⟨hbat, hfx, hfy, hNN⟩ := hS
  -- the sizes
  have hcn : max 1 (2 / r₀) ≤ c * n - C0 := by rw [div_le_iff₀ hc] at hn1; linarith
  have hcm : max 1 (2 / r₀) ≤ c * m - C0 := by rw [div_le_iff₀ hc] at hm1; linarith
  have hcn1 : 1 ≤ c * n - C0 := (le_max_left _ _).trans hcn
  have hcm1 : 1 ≤ c * m - C0 := (le_max_left _ _).trans hcm
  set r : ℝ := 1 / (c * n - C0) + 1 / (c * m - C0) with hr
  have hrpos : 0 < r := add_pos (one_div_pos.2 (by linarith)) (one_div_pos.2 (by linarith))
  have hinv : ∀ x : ℝ, 2 / r₀ ≤ x → 1 / x ≤ r₀ / 2 := fun x hx => by
    calc 1 / x ≤ 1 / (2 / r₀) := one_div_le_one_div_of_le (by positivity) hx
      _ = r₀ / 2 := by rw [one_div_div]
  have hrr₀ : r ≤ r₀ := by
    have h1 := hinv _ ((le_max_right _ _).trans hcn)
    have h2 := hinv _ ((le_max_right _ _).trans hcm)
    linarith
  have hfit1 : ∀ k, 1 ≤ fitCard (R n m).lx ((R n m).bat k) ∧ 1 ≤ fitCard (R n m).ly ((R n m).bat k) := fun k =>
    ⟨Nat.one_le_cast.1 (hcn1.trans (hfx k)), Nat.one_le_cast.1 (hcm1.trans (hfy k))⟩
  have hfitr : ∀ k, 1 / (fitCard (R n m).lx ((R n m).bat k) : ℝ) + 1 / (fitCard (R n m).ly ((R n m).bat k) : ℝ) ≤ r :=
    fun k => add_le_add (one_div_le_one_div_of_le (by linarith) (hfx k)) (one_div_le_one_div_of_le (by linarith) (hfy k))
  -- the level
  have hα0 : 0 ≤ α n m i := ((hgrid n m).2 i).1
  have hα1 : α n m i < 1 := ((hgrid n m).2 i).2
  have hβi : beta (α n m i) = 1 / (1 - α n m i) := rfl
  have hβipos : 0 < beta (α n m i) := by rw [hβi]; exact one_div_pos.2 (by linarith)
  have hβle : beta (α n m i) ≤ β₀ := by
    rw [hβi, hβ₀]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  -- the size condition (S)
  have hS1 : beta (α n m i) * Dφ * r ≤ d / 8 := by
    have h1 : r ≤ d / (8 * β₀ * Dφ) := hrr₀.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h2 : β₀ * Dφ * r ≤ d / 8 := by
      rw [le_div_iff₀ (by positivity)] at h1
      have e : β₀ * Dφ * r = r * (8 * β₀ * Dφ) / 8 := by ring
      rw [e]; linarith
    have h3 : beta (α n m i) * Dφ * r ≤ β₀ * Dφ * r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβle hDpos.le) hrpos.le
    linarith
  have hS2 : beta (α n m i) ^ 2 * κ ^ 2 * r ≤ 7 * d ^ 2 / 64 := by
    have h1 : r ≤ 7 * d ^ 2 / (64 * β₀ ^ 2 * (κ ^ 2 + 1)) := hrr₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : β₀ ^ 2 * (κ ^ 2 + 1) * r ≤ 7 * d ^ 2 / 64 := by
      rw [le_div_iff₀ (by positivity)] at h1
      have e : β₀ ^ 2 * (κ ^ 2 + 1) * r = r * (64 * β₀ ^ 2 * (κ ^ 2 + 1)) / 64 := by ring
      rw [e]; linarith
    have h3 : beta (α n m i) ^ 2 ≤ β₀ ^ 2 := pow_le_pow_left₀ hβipos.le hβle 2
    have h4 : beta (α n m i) ^ 2 * κ ^ 2 * r ≤ β₀ ^ 2 * (κ ^ 2 + 1) * r := by
      apply mul_le_mul_of_nonneg_right _ hrpos.le
      exact mul_le_mul h3 (by linarith) (sq_nonneg κ) (sq_nonneg β₀)
    linarith
  have hb := hcore 𝒳 H φ κ Dφ P Q (J n m) n m (α n m) (δ n m) lmax s2 (R n m) Bmax i d r hφ hκ hDφ (hgrid n m)
    (hδ n m).1 (hδ n m).2 hl0 hl1 hs2 hW hbat hfit1 hfitr hd hdi hS1 hS2
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the fitting term
  have hT1 := hfit r (d / (8 * beta (α n m i))) hrpos (hrr₀.trans (min_le_left _ _))
    (div_le_div_of_nonneg_left hd.le (by positivity) (by linarith))
  -- the betting term
  set L : ℝ := Real.log (1 / δ n m) with hLdef
  have hLpos : 0 < L := Real.log_pos (one_lt_one_div (hδ n m).1 (hδ n m).2)
  have hNhalf : c * Nmin / 2 ≤ (R n m).N := by
    have : C0 ≤ c * Nmin / 2 := by
      rw [div_le_iff₀ hc] at hmin2
      linarith
    linarith [hNN]
  have hLN : L ≤ η₀ * (R n m).N := by
    have h2 : η₀ * (c * Nmin / 2) ≤ η₀ * (R n m).N := mul_le_mul_of_nonneg_left hNhalf hη₀.le
    have e : η₀ * c / 2 * Nmin = η₀ * (c * Nmin / 2) := by ring
    linarith
  have hρ : d / (2 * β₀ * Dφ) ≤ d / (2 * beta (α n m i) * Dφ) :=
    div_le_div_of_nonneg_left hd.le (by positivity)
      (mul_le_mul_of_nonneg_right (by linarith) hDpos.le)
  have hT2 := hgen (α n m i) (R n m).N L _ hα0 hα1 hLpos hLN hρ
  have hKN : K * (c * Nmin / 2) ≤ K * (R n m).N := mul_le_mul_of_nonneg_left hNhalf hK.le
  have hJexp : ((J n m : ℕ) : ℝ) * Real.exp (-(K * (R n m).N)) ≤ ε / 2 := by
    rcases Nat.eq_zero_or_pos (J n m) with hJ0 | hJ0
    · have h0 : ((J n m : ℕ) : ℝ) = 0 := by exact_mod_cast hJ0
      rw [h0, zero_mul]; positivity
    · have hJpos : (0 : ℝ) < J n m := Nat.cast_pos.2 hJ0
      have h1 : Real.log (J n m) ≤ K * (R n m).N / 2 := by
        have e : K * c / 4 * Nmin = K * (c * Nmin / 2) / 2 := by ring
        linarith
      have h2 : Real.log (2 / ε) ≤ K * (R n m).N / 2 := by
        rw [div_le_iff₀ (by positivity)] at hmin4
        have e : Nmin * (K * c) = 2 * (K * (c * Nmin / 2)) := by ring
        linarith
      calc ((J n m : ℕ) : ℝ) * Real.exp (-(K * (R n m).N))
          = Real.exp (Real.log (J n m) - K * (R n m).N) := by
            rw [Real.exp_sub, Real.exp_log hJpos, Real.exp_neg, div_eq_mul_inv]
        _ ≤ Real.exp (-Real.log (2 / ε)) := Real.exp_le_exp.2 (by linarith)
        _ = ε / 2 := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hJg := mul_le_mul_of_nonneg_left hT2 (Nat.cast_nonneg (J n m) : (0 : ℝ) ≤ J n m)
  linarith

/-! ### The upper side: `P(α̂_lo > TV + ε) → 0` -/

/-- **The upper side, eventually**, for any grids: `α̂_lo > TV + ε` needs the rejection of the first level
`α_{i₀} ≥ TV + ε/2` (`grid_events`), a strict null with `ζ = ε/2`; the strict-null bound at the one-level sub-run of that
level gives `≤ exp(−(ε/2) σ_min √(2NL))`, small once `N` is large and `L ≥ log(1/δ̄) > 0`. -/
theorem upper_eventually (hstrict : Claims.lo_strict_bound) {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (φ : 𝒳 → H) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (J : ℕ → ℕ → ℕ) (α : ∀ n m, Fin (J n m) → ℝ) (δ : ℕ → ℕ → ℝ) (δbar lmax s2 c C0 : ℝ) (Bmax : ℕ)
    (R : ∀ n m : ℕ, LoRun 𝒳 (J n m) n m)
    (hgrid : ∀ n m, IsGrid (α n m)) (hδ : ∀ n m, 0 < δ n m ∧ δ n m < 1) (hδbar : δbar < 1)
    (hδb : ∃ N₁ : ℕ, ∀ n m, N₁ ≤ n → N₁ ≤ m → δ n m ≤ δbar)
    (hl0 : 0 < lmax) (hl1 : lmax ≤ 1 / 2) (hs2 : 0 < s2) (hc : 0 < c)
    (hR : ∀ n m, (R n m).IsWitnessRun φ (α n m) (δ n m) lmax s2 ∧ (R n m).IsSizedRun c C0 Bmax)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m →
      sampleLaw P Q n m {ω | StatFormal.Distances.tvDist P Q + ε < (R n m).alphaLo (α n m) (δ n m) ω.1 ω.2} ≤
        ENNReal.ofReal η := by
  obtain ⟨N₁, hN₁⟩ := hδb
  have hδbar0 : 0 < δbar := (hδ N₁ N₁).1.trans_le (hN₁ N₁ N₁ le_rfl le_rfl)
  have hL₀ : 0 < Real.log (1 / δbar) := Real.log_pos (one_lt_one_div hδbar0 hδbar)
  obtain ⟨T, hT⟩ := strict_term_small (ε / 2) s2 (Real.log (1 / δbar)) η (by positivity) hs2 hL₀ hη
  refine ⟨max N₁ ⌈(T + C0) / c⌉₊, ?_⟩
  intro n m hn hm
  obtain ⟨hW, hS⟩ := hR n m
  have hNT : T ≤ (R n m).N := by
    have h1 : (T + C0) / c ≤ ((min n m : ℕ) : ℝ) := ceil_le_cast (le_min (by omega) (by omega))
    rw [div_le_iff₀ hc] at h1
    linarith [hS.2.2.2]
  have hLL : Real.log (1 / δbar) ≤ Real.log (1 / δ n m) := by
    apply Real.log_le_log (by positivity)
    exact one_div_le_one_div_of_le (hδ n m).1 (hN₁ n m (by omega) (by omega))
  have hTV0 : 0 ≤ StatFormal.Distances.tvDist P Q := StatFormal.Distances.tvDist_nonneg P Q
  have ha0 : 0 < StatFormal.Distances.tvDist P Q + ε / 2 := by linarith
  have hlt : ∀ ω : (Fin n → 𝒳) × (Fin m → 𝒳),
      StatFormal.Distances.tvDist P Q + ε < (R n m).alphaLo (α n m) (δ n m) ω.1 ω.2 →
      gridBelow (α n m) (StatFormal.Distances.tvDist P Q + ε / 2) < (R n m).alphaLo (α n m) (δ n m) ω.1 ω.2 := by
    intro ω hω
    have := gridBelow_lt (α n m) ha0
    linarith
  by_cases hex : ∃ i₀, StatFormal.Distances.tvDist P Q + ε / 2 ≤ α n m i₀ ∧
      ∀ i < i₀, α n m i < StatFormal.Distances.tvDist P Q + ε / 2
  · obtain ⟨i₀, hi₀a, hi₀⟩ := hex
    have hsub := hstrict 𝒳 P Q 1 n m (fun _ => α n m i₀) (δ n m) lmax s2 (ε / 2) (subRun (R n m) i₀)
      (isGrid_one ((hgrid n m).2 i₀).1 ((hgrid n m).2 i₀).2) (hδ n m).1 (hδ n m).2 hl0 (by linarith) hs2
      ⟨hW.1.1, fun _ => hW.1.2.1 i₀, fun _ => hW.1.2.2 i₀⟩ (fun _ k x y z => (hW.2.2 i₀ k x y z).1)
      (by positivity) (fun _ _ => hi₀a)
    refine (measure_mono ?_).trans (hsub.2.trans (ENNReal.ofReal_le_ofReal (hT _ _ hNT hLL)))
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have hgb : gridBelow (fun _ : Fin 1 => α n m i₀) (StatFormal.Distances.tvDist P Q) = 0 := by
      rcases gridBelow_spec (fun _ : Fin 1 => α n m i₀) (StatFormal.Distances.tvDist P Q) with ⟨j, hj, -⟩ | ⟨-, h0⟩
      · exact absurd hj (not_lt.2 (by linarith))
      · exact h0
    rw [hgb]
    obtain ⟨i₁, hi₁a, hi₁, hrej⟩ := (grid_events_route _ (α n m)
      (fun j => rejects ((R n m).lam j) ((R n m).g j) (R n m).bat (R n m).A (R n m).B (α n m j) (δ n m) ω.1 ω.2)
      _ (hgrid n m)).1 (hlt ω hω)
    have hii : i₁ = i₀ := by
      rcases lt_trichotomy i₁ i₀ with h | h | h
      · exact absurd (hi₀ i₁ h) (not_lt.2 hi₁a)
      · exact h
      · exact absurd (hi₁ i₀ h) (not_lt.2 hi₀a)
    subst hii
    have hle : α n m i₁ ≤ (subRun (R n m) i₁).alphaLo (fun _ => α n m i₁) (δ n m) ω.1 ω.2 :=
      le_alphaLo (fun _ : Fin 1 => α n m i₁) _ 0 (fun _ _ => hrej)
    linarith
  · refine (measure_mono (t := ∅) ?_).trans (by simp)
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    obtain ⟨i₁, hi₁a, hi₁, -⟩ := (grid_events_route _ (α n m)
      (fun j => rejects ((R n m).lam j) ((R n m).g j) (R n m).bat (R n m).A (R n m).B (α n m j) (δ n m) ω.1 ω.2)
      _ (hgrid n m)).1 (hlt ω hω)
    exact hex ⟨i₁, hi₁a, hi₁⟩

/-! ### Fixed grids: the lower side below `TV`, the upper side off the grid -/

/-- (A3), fixed grid: `P(α̂_lo < α_{j*}) → 0` (`D_{α_{j*}} > 0` by `eq:zeroeq` when `α_{j*}` is a grid level below `TV`;
otherwise `α_{j*} = 0 ≤ α̂_lo`). -/
theorem lower_gridBelow (hcore : Iface.CoreLowerBound) {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (J : ℕ) (α : Fin J → ℝ) (δ : ℕ → ℕ → ℝ)
    (lmax s2 c C0 : ℝ) (Bmax : ℕ) (R : ∀ n m : ℕ, LoRun 𝒳 J n m)
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) (hchar : Characteristic φ)
    (hgrid : IsGrid α) (hδ : ∀ n m, 0 < δ n m ∧ δ n m < 1)
    (hL : ∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → Real.log (1 / δ n m) ≤ η * (min n m : ℕ))
    (hl0 : 0 < lmax) (hl1 : lmax ≤ 1 / 2) (hs2 : 0 < s2) (hc : 0 < c)
    (hR : ∀ n m, (R n m).IsWitnessRun φ α (δ n m) lmax s2 ∧ (R n m).IsSizedRun c C0 Bmax) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → sampleLaw P Q n m
      {ω | (R n m).alphaLo α (δ n m) ω.1 ω.2 < gridBelow α (StatFormal.Distances.tvDist P Q)} ≤ ENNReal.ofReal ε := by
  rcases gridBelow_spec α (StatFormal.Distances.tvDist P Q) with ⟨j, hj, hgb⟩ | ⟨-, hgb⟩
  · have hD : 0 < Dpop φ P Q (α j) := by
      refine lt_of_le_of_ne (Dpop_nonneg _ _ _ _) fun h => ?_
      have := (StatFormal.TrimmedMMD.ZeroSet.zeroeq 𝒳 H P Q φ κ (α j) hφ hκ hchar (hgrid.2 j).1 (hgrid.2 j).2).1 h.symm
      linarith
    obtain ⟨N₀, hN₀⟩ := core_eventually hcore φ κ Dφ (fun _ _ => J) (fun _ _ => α) δ lmax s2 c C0 Bmax R hφ hκ hDφ
      (fun _ _ => hgrid) hδ hL (const_small _) hl0 hl1 hs2 hc hR (Dpop φ P Q (α j)) (α j) hD (hgrid.2 j).2 ε hε
    refine ⟨N₀, fun n m hn hm => ?_⟩
    rw [hgb]
    exact hN₀ n m hn hm P Q j le_rfl le_rfl
  · refine ⟨0, fun n m _ _ => (measure_mono (t := ∅) fun ω hω => ?_).trans (by simp)⟩
    simp only [mem_ofPred_eq, hgb] at hω
    exact absurd hω (not_lt.2 (run_alphaLo_nonneg _ hgrid _ _ _))

/-- Fixed grid, fixed `δ`, `TV` off the grid: `P(α̂_lo > α_{j*}) → 0` (`lo_strict_bound` with `ζ` the gap from `TV` to the
first level above it). -/
theorem upper_offgrid (hstrict : Claims.lo_strict_bound) {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (φ : 𝒳 → H) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (J : ℕ) (α : Fin J → ℝ) (δ lmax s2 c C0 : ℝ) (Bmax : ℕ) (R : ∀ n m : ℕ, LoRun 𝒳 J n m)
    (hgrid : IsGrid α) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hl0 : 0 < lmax) (hl1 : lmax ≤ 1 / 2) (hs2 : 0 < s2) (hc : 0 < c)
    (hR : ∀ n m, (R n m).IsWitnessRun φ α δ lmax s2 ∧ (R n m).IsSizedRun c C0 Bmax)
    (hoff : ∀ j, α j ≠ StatFormal.Distances.tvDist P Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → sampleLaw P Q n m
      {ω | gridBelow α (StatFormal.Distances.tvDist P Q) < (R n m).alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal ε := by
  classical
  obtain ⟨ζ, hζ, hζTV⟩ : ∃ ζ > 0, ∀ j, StatFormal.Distances.tvDist P Q ≤ α j →
      StatFormal.Distances.tvDist P Q + ζ ≤ α j := by
    by_cases hne : (Finset.univ.filter fun j => StatFormal.Distances.tvDist P Q ≤ α j).Nonempty
    · obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_min_image _ α hne
      have h0 : StatFormal.Distances.tvDist P Q < α j₀ :=
        lt_of_le_of_ne (Finset.mem_filter.1 hj₀).2 (hoff j₀).symm
      refine ⟨α j₀ - StatFormal.Distances.tvDist P Q, by linarith, fun j hj => ?_⟩
      have := hmin j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
      linarith
    · exact ⟨1, one_pos, fun j hj => absurd ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩ hne⟩
  have hL0 : 0 < Real.log (1 / δ) := Real.log_pos (one_lt_one_div hδ0 hδ1)
  obtain ⟨T, hT⟩ := strict_term_small ζ s2 (Real.log (1 / δ)) ε hζ hs2 hL0 hε
  refine ⟨⌈(T + C0) / c⌉₊, fun n m hn hm => ?_⟩
  obtain ⟨hW, hS⟩ := hR n m
  have hNT : T ≤ (R n m).N := by
    have h1 : (T + C0) / c ≤ ((min n m : ℕ) : ℝ) := ceil_le_cast (le_min hn hm)
    rw [div_le_iff₀ hc] at h1
    linarith [hS.2.2.2]
  exact (hstrict 𝒳 P Q J n m α δ lmax s2 ζ (R n m) hgrid hδ0 hδ1 hl0 (by linarith) hs2 hW.1
    (fun j k x y z => (hW.2.2 j k x y z).1) hζ hζTV).2.trans (ENNReal.ofReal_le_ofReal (hT _ _ hNT le_rfl))

end Limits

open Limits

/-! ### The targets -/

/-- `Claims.lo_lower` from the core lower bound. -/
theorem lo_lower_of (hcore : Iface.CoreLowerBound) : Claims.lo_lower := by
  intro 𝒳 H _ _ _ _ _ φ κ Dφ J α δ lmax s2 c C0 Bmax R hφ hκ hDφ hgrid hδ hL hl0 hl1 hs2 hc hR i d hd ε hε
  obtain ⟨N₀, hN₀⟩ := core_eventually hcore φ κ Dφ (fun _ _ => J) (fun _ _ => α) δ lmax s2 c C0 Bmax R
    hφ hκ hDφ (fun _ _ => hgrid) hδ hL (const_small _) hl0 hl1 hs2 hc hR d (α i) hd (hgrid.2 i).2 ε hε
  exact ⟨N₀, fun n m hn hm P Q hP hQ hdi => @hN₀ n m hn hm P Q hP hQ i le_rfl hdi⟩

/-- `Claims.lo_consistency` (the printed proposition) from the core lower bound, `lo_upper` and `lo_strict_bound`. -/
theorem lo_consistency_of (hcore : Iface.CoreLowerBound) (hup : Claims.lo_upper) (hstrict : Claims.lo_strict_bound) :
    Claims.lo_consistency := by
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ J α δ lmax s2 c C0 Bmax R hφ hκ hDφ hchar hgrid hδ0 hδ1 hl0 hl1 hs2 hc hR
  refine ⟨fun n m => (hup 𝒳 P Q J n m α δ lmax (R n m) hgrid hδ0 hδ1 hl0 (by linarith) (hR n m).1.1).2.1,
    fun ε hε => ?_, fun hoff ε hε => ?_⟩
  · exact lower_gridBelow hcore φ κ Dφ P Q J α (fun _ _ => δ) lmax s2 c C0 Bmax R hφ hκ hDφ hchar hgrid
      (fun _ _ => ⟨hδ0, hδ1⟩) (const_small _) hl0 hl1 hs2 hc hR ε hε
  · exact upper_offgrid hstrict φ P Q J α δ lmax s2 c C0 Bmax R hgrid hδ0 hδ1 hl0 hl1 hs2 hc hR hoff ε hε

/-- `Claims.lo_exact` from the core lower bound, `lo_upper` (also for the measurability of `{α̂_lo = α_{j*}}`) and
`lo_strict_bound`. -/
theorem lo_exact_of (hcore : Iface.CoreLowerBound) (hup : Claims.lo_upper) (hstrict : Claims.lo_strict_bound) :
    Claims.lo_exact := by
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ J α δ lmax s2 c C0 Bmax R hφ hκ hDφ hchar hgrid hδ0 hδ1 hl0 hl1 hs2 hc hR
  have hupn := fun n m => hup 𝒳 P Q J n m α δ lmax (R n m) hgrid hδ0 hδ1 hl0 (by linarith) (hR n m).1.1
  have hlow := lower_gridBelow hcore φ κ Dφ P Q J α (fun _ _ => δ) lmax s2 c C0 Bmax R hφ hκ hDφ hchar hgrid
    (fun _ _ => ⟨hδ0, hδ1⟩) (const_small _) hl0 hl1 hs2 hc hR
  refine ⟨fun hoff ε hε => ?_, fun _ ε hε => ?_⟩
  · obtain ⟨N₁, hN₁⟩ := hlow (ε / 2) (by positivity)
    obtain ⟨N₂, hN₂⟩ := upper_offgrid hstrict φ P Q J α δ lmax s2 c C0 Bmax R hgrid hδ0 hδ1 hl0 hl1 hs2 hc hR hoff
      (ε / 2) (by positivity)
    refine ⟨max N₁ N₂, fun n m hn hm => ?_⟩
    have := sampleLaw_isProb P Q n m
    have h := prob_eq_ge (sampleLaw P Q n m) _ (hupn n m).1 (gridBelow α (StatFormal.Distances.tvDist P Q)) (ε / 2)
      (ε / 2) (by positivity) (by positivity) (hN₁ n m (le_of_max_le_left hn) (le_of_max_le_left hm))
      (hN₂ n m (le_of_max_le_right hn) (le_of_max_le_right hm))
    rwa [add_halves] at h
  · obtain ⟨N₁, hN₁⟩ := hlow ε hε
    refine ⟨N₁, fun n m hn hm => ?_⟩
    have := sampleLaw_isProb P Q n m
    have h := prob_eq_ge (sampleLaw P Q n m) _ (hupn n m).1 (gridBelow α (StatFormal.Distances.tvDist P Q)) ε δ
      hε.le hδ0.le (hN₁ n m hn hm) (hupn n m).2.1
    have e : 1 - δ - ε = 1 - (ε + δ) := by ring
    rwa [e]

/-- `Claims.lo_vanishing` from the core lower bound and `lo_upper`. -/
theorem lo_vanishing_of (hcore : Iface.CoreLowerBound) (hup : Claims.lo_upper) : Claims.lo_vanishing := by
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ J α δ lmax s2 c C0 Bmax R hφ hκ hDφ hchar hgrid hδ hδL hl0 hl1 hs2 hc hR ε hε
  obtain ⟨N₁, hN₁⟩ := lower_gridBelow hcore φ κ Dφ P Q J α δ lmax s2 c C0 Bmax R hφ hκ hDφ hchar hgrid hδ
    (fun η hη => let ⟨N, hN⟩ := hδL η hη; ⟨N, fun n m hn hm => (hN n m hn hm).2⟩) hl0 hl1 hs2 hc hR (ε / 2)
    (by positivity)
  obtain ⟨N₂, hN₂⟩ := hδL (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, fun n m hn hm => ?_⟩
  have hu := hup 𝒳 P Q J n m α (δ n m) lmax (R n m) hgrid (hδ n m).1 (hδ n m).2 hl0 (by linarith) (hR n m).1.1
  have h2 := hu.2.1.trans (ENNReal.ofReal_le_ofReal (hN₂ n m (le_of_max_le_right hn) (le_of_max_le_right hm)).1)
  have := sampleLaw_isProb P Q n m
  have h := prob_eq_ge (sampleLaw P Q n m) _ hu.1 (gridBelow α (StatFormal.Distances.tvDist P Q)) (ε / 2) (ε / 2)
    (by positivity) (by positivity) (hN₁ n m (le_of_max_le_left hn) (le_of_max_le_left hm)) h2
  rwa [add_halves] at h

/-- `Claims.lo_refining_kernel` (refining grids, no (A3)) from the core lower bound, the monotonicity of `D_α` and
`lo_strict_bound`. -/
theorem lo_refining_kernel_of (hcore : Iface.CoreLowerBound) (hanti : Iface.DpopAntitone)
    (hstrict : Claims.lo_strict_bound) : Claims.lo_refining_kernel := by
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ J α δ δbar lmax s2 c C0 Bmax R hφ hκ hDφ hgrid hmesh hδ hδbar hδL hl0 hl1 hs2
    hc hR
  refine ⟨fun a ha0 ha1 hDa ε hε η hη => ?_, fun ε hε η hη => ?_⟩
  · obtain ⟨N₁, hN₁⟩ := core_eventually hcore φ κ Dφ J α δ lmax s2 c C0 Bmax R hφ hκ hDφ hgrid hδ
      (fun η hη => let ⟨N, hN⟩ := hδL η hη; ⟨N, fun n m hn hm => (hN n m hn hm).2⟩)
      (fun η hη => let ⟨N, hN⟩ := hmesh η hη; ⟨N, fun n m hn hm => (hN n m hn hm).2⟩)
      hl0 hl1 hs2 hc hR (Dpop φ P Q a) a hDa ha1 η hη
    obtain ⟨N₂, hN₂⟩ := hmesh (ε / 2) (by positivity)
    refine ⟨max N₁ N₂, fun n m hn hm => ?_⟩
    obtain ⟨b, hb, hba, hab⟩ := mesh_point_route _ (α n m) a (hgrid n m) ha0 ha1
    have hh := (hN₂ n m (le_of_max_le_right hn) (le_of_max_le_right hm)).1
    have hb' : a - ε ≤ b := by linarith
    rcases hb with rfl | ⟨i, rfl⟩
    · refine (measure_mono (t := ∅) fun ω hω => ?_).trans (by simp)
      simp only [mem_ofPred_eq] at hω
      have := run_alphaLo_nonneg (R n m) (hgrid n m) (δ n m) ω.1 ω.2
      linarith
    · refine (measure_mono fun ω hω => ?_).trans (hN₁ n m (le_of_max_le_left hn) (le_of_max_le_left hm) P Q i hba
        (hanti 𝒳 H φ κ P Q (α n m i) a hφ hκ ((hgrid n m).2 i).1 hba ha1))
      simp only [mem_ofPred_eq] at hω ⊢
      linarith
  · exact upper_eventually hstrict φ P Q J α δ δbar lmax s2 c C0 Bmax R hgrid hδ hδbar
      (let ⟨N, hN⟩ := hδL 1 one_pos; ⟨N, fun n m hn hm => (hN n m hn hm).1⟩) hl0 hl1 hs2 hc hR ε hε η hη

/-- `Claims.lo_refining` (refining grids, (A3)) from the core lower bound, the monotonicity of `D_α` and
`lo_strict_bound`: the kernel version at `a = TV − ε/2`, where `D_a > 0` by `eq:zeroeq`. -/
theorem lo_refining_of (hcore : Iface.CoreLowerBound) (hanti : Iface.DpopAntitone)
    (hstrict : Claims.lo_strict_bound) : Claims.lo_refining := by
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ J α δ δbar lmax s2 c C0 Bmax R hφ hκ hDφ hchar hgrid hmesh hδ hδbar hδL hl0 hl1
    hs2 hc hR ε hε η hη
  have hK := lo_refining_kernel_of hcore hanti hstrict 𝒳 H φ κ Dφ P Q J α δ δbar lmax s2 c C0 Bmax R hφ hκ hDφ hgrid
    hmesh hδ hδbar hδL hl0 hl1 hs2 hc hR
  have hTV0 : 0 ≤ StatFormal.Distances.tvDist P Q := StatFormal.Distances.tvDist_nonneg P Q
  have hTV1 : StatFormal.Distances.tvDist P Q ≤ 1 := StatFormal.Distances.tvDist_le_one
  obtain ⟨N₁, hN₁⟩ := hK.2 ε hε (η / 2) (by positivity)
  -- the lower side
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n m, N₂ ≤ n → N₂ ≤ m → sampleLaw P Q n m
      {ω | (R n m).alphaLo (α n m) (δ n m) ω.1 ω.2 < StatFormal.Distances.tvDist P Q - ε} ≤ ENNReal.ofReal (η / 2) := by
    by_cases hTVε : ε ≤ StatFormal.Distances.tvDist P Q
    · set a := StatFormal.Distances.tvDist P Q - ε / 2 with ha
      have ha0 : 0 ≤ a := by linarith
      have ha1 : a < 1 := by linarith
      have hDa : 0 < Dpop φ P Q a := by
        refine lt_of_le_of_ne (Dpop_nonneg _ _ _ _) fun h => ?_
        have := (StatFormal.TrimmedMMD.ZeroSet.zeroeq 𝒳 H P Q φ κ a hφ hκ hchar ha0 ha1).1 h.symm
        linarith
      obtain ⟨N₂, hN₂⟩ := hK.1 a ha0 ha1 hDa (ε / 2) (by positivity) (η / 2) (by positivity)
      refine ⟨N₂, fun n m hn hm => (measure_mono fun ω hω => ?_).trans (hN₂ n m hn hm)⟩
      simp only [mem_ofPred_eq] at hω ⊢
      linarith
    · refine ⟨0, fun n m _ _ => (measure_mono (t := ∅) fun ω hω => ?_).trans (by simp)⟩
      simp only [mem_ofPred_eq] at hω
      have := run_alphaLo_nonneg (R n m) (hgrid n m) (δ n m) ω.1 ω.2
      linarith
  refine ⟨max N₁ N₂, fun n m hn hm => ?_⟩
  have hsub : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | ε < |(R n m).alphaLo (α n m) (δ n m) ω.1 ω.2 -
      StatFormal.Distances.tvDist P Q|} ⊆
      {ω | (R n m).alphaLo (α n m) (δ n m) ω.1 ω.2 < StatFormal.Distances.tvDist P Q - ε} ∪
      {ω | StatFormal.Distances.tvDist P Q + ε < (R n m).alphaLo (α n m) (δ n m) ω.1 ω.2} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union] at hω ⊢
    rcases lt_abs.1 hω with h | h
    · right; linarith
    · left; linarith
  calc sampleLaw P Q n m {ω | ε < |(R n m).alphaLo (α n m) (δ n m) ω.1 ω.2 - StatFormal.Distances.tvDist P Q|}
      ≤ sampleLaw P Q n m ({ω | (R n m).alphaLo (α n m) (δ n m) ω.1 ω.2 < StatFormal.Distances.tvDist P Q - ε} ∪
          {ω | StatFormal.Distances.tvDist P Q + ε < (R n m).alphaLo (α n m) (δ n m) ω.1 ω.2}) := measure_mono hsub
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
        (measure_union_le _ _).trans (add_le_add (hN₂ n m (le_of_max_le_right hn) (le_of_max_le_right hm))
          (hN₁ n m (le_of_max_le_left hn) (le_of_max_le_left hm)))
    _ = ENNReal.ofReal η := by rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-! ### Compile-time checks: each target is literally the frozen claim -/

example (hcore : Iface.CoreLowerBound) : Claims.lo_lower := lo_lower_of hcore
example (hcore : Iface.CoreLowerBound) (hup : Claims.lo_upper) (hstrict : Claims.lo_strict_bound) :
    Claims.lo_consistency := lo_consistency_of hcore hup hstrict
example (hcore : Iface.CoreLowerBound) (hup : Claims.lo_upper) (hstrict : Claims.lo_strict_bound) :
    Claims.lo_exact := lo_exact_of hcore hup hstrict
example (hcore : Iface.CoreLowerBound) (hup : Claims.lo_upper) : Claims.lo_vanishing := lo_vanishing_of hcore hup
example (hcore : Iface.CoreLowerBound) (hanti : Iface.DpopAntitone) (hstrict : Claims.lo_strict_bound) :
    Claims.lo_refining_kernel := lo_refining_kernel_of hcore hanti hstrict
example (hcore : Iface.CoreLowerBound) (hanti : Iface.DpopAntitone) (hstrict : Claims.lo_strict_bound) :
    Claims.lo_refining := lo_refining_of hcore hanti hstrict

end StatFormal.Wave30tz
