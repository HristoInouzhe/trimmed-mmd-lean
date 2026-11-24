import StatFormal.Wave30tz.Proofs
import StatFormal.Wave31tr.RouteFWLower

/-!
# Wave 31tr, chunk M3: T20 (b) `lo_consistency_fw` — Proposition 4.4 for Frank–Wolfe runs (untrusted route)

The three printed sentences of `prop:loconsistency` for families of `IsWitnessRunFW ρ ∧ IsSizedRun` runs (`0 ≤ ρ < 1`):
* validity at every `n, m`: the certified `Wave30tz.lo_upper` (it needs admissibility only);
* `P(α̂_lo < α_{j*}) → 0`: copy-adapted from the certified `Wave30tz.Limits.core_eventually` and `lower_gridBelow`, with
  `core_lower_bound_fw` (T20 (a) at every floor) at `d = (1 − ρ/2)D_{α_{j*}} > 0` (`D_{α_{j*}} > 0` by the certified
  `TrimmedMMD.ZeroSet.zeroeq` under (A3));
* `P(α̂_lo > α_{j*}) → 0` off the grid: copy-adapted from `Wave30tz.Limits.upper_offgrid` (admissibility and the upper fraction
  bound, the certified `Wave30tz.lo_strict_bound`).
The elementary limits (`fit_term_small`, `genEps_small`, `strict_term_small`, `const_small`, …) are the certified route's.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tr.RouteFW

open StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tp StatFormal.TrimmedMMD.Unconditional
open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.ZeroSet
open StatFormal.Wave30tz.Limits

/-- (copy-adapted from the certified `Wave30tz.Limits.core_eventually`, for Frank–Wolfe runs of gap `ρ ∈ [0,1)`, with
`d ≤ (1 − ρ/2)D_{α_i}` and `core_lower_bound_fw` in place of `Iface.CoreLowerBound`) **The lower side, eventually.** For grids `𝒢_{n,m}` with `log|𝒢_{n,m}| = o(min(n,m))`, levels with
`log(1/δ_{n,m}) = o(min(n,m))` and runs of Proposition 1 in the asymptotic regime: for every `d > 0`, `a₀ < 1`, `ε > 0`,
eventually `P(α̂_lo < α_i) ≤ ε` for all pairs `(P,Q)` and all levels `α_i ≤ a₀` with `D_{α_i}(P,Q) ≥ d`. -/
theorem core_eventually_fw {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ)
    (J : ℕ → ℕ → ℕ) (α : ∀ n m, Fin (J n m) → ℝ) (δ : ℕ → ℕ → ℝ) (lmax s2 c C0 : ℝ) (Bmax : ℕ)
    (R : ∀ n m : ℕ, LoRun 𝒳 (J n m) n m)
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ)
    (hgrid : ∀ n m, IsGrid (α n m)) (hδ : ∀ n m, 0 < δ n m ∧ δ n m < 1)
    (hL : ∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → Real.log (1 / δ n m) ≤ η * (min n m : ℕ))
    (hJ : ∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → Real.log (J n m) ≤ η * (min n m : ℕ))
    (hl0 : 0 < lmax) (hl1 : lmax ≤ 1 / 2) (hs2 : 0 < s2) (hc : 0 < c) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hR : ∀ n m, IsWitnessRunFW (R n m) φ (α n m) (δ n m) lmax s2 ρ ∧ (R n m).IsSizedRun c C0 Bmax)
    (d a₀ : ℝ) (hd : 0 < d) (ha₀ : a₀ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → ∀ (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (i : Fin (J n m)), α n m i ≤ a₀ → d ≤ (1 - ρ / 2) * Dpop φ P Q (α n m i) →
        sampleLaw P Q n m {ω | (R n m).alphaLo (α n m) (δ n m) ω.1 ω.2 < α n m i} ≤ ENNReal.ofReal ε := by
  rcases le_or_gt Dφ 0 with hD0 | hDpos
  · refine ⟨0, fun n m _ _ P Q _ _ i _ hdi => absurd hdi (not_le.2 (lt_of_le_of_lt ?_ hd))⟩
    refine mul_nonpos_of_nonneg_of_nonpos (by linarith) (Dpop_nonpos_of_const φ P Q _ fun x x' => ?_)
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
  have hb := core_lower_bound_fw φ κ Dφ P Q (J n m) n m (α n m) (δ n m) lmax s2 ρ (R n m) Bmax i d r hφ hκ hDφ (hgrid n m)
    (hδ n m).1 (hδ n m).2 hl0 hl1 hs2 hρ0 hρ1 hW hbat hfit1 hfitr hd hdi hS1 hS2
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

/-- (copy-adapted from the certified `Wave30tz.Limits.lower_gridBelow`, for Frank–Wolfe runs: `d = (1 − ρ/2)D_{α_{j*}} > 0`)
(A3), fixed grid: `P(α̂_lo < α_{j*}) → 0` (`D_{α_{j*}} > 0` by `eq:zeroeq` when `α_{j*}` is a grid level below `TV`;
otherwise `α_{j*} = 0 ≤ α̂_lo`). -/
theorem lower_gridBelow_fw {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (J : ℕ) (α : Fin J → ℝ) (δ : ℕ → ℕ → ℝ)
    (lmax s2 c C0 : ℝ) (Bmax : ℕ) (R : ∀ n m : ℕ, LoRun 𝒳 J n m)
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) (hchar : Characteristic φ)
    (hgrid : IsGrid α) (hδ : ∀ n m, 0 < δ n m ∧ δ n m < 1)
    (hL : ∀ η > 0, ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → Real.log (1 / δ n m) ≤ η * (min n m : ℕ))
    (hl0 : 0 < lmax) (hl1 : lmax ≤ 1 / 2) (hs2 : 0 < s2) (hc : 0 < c) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hR : ∀ n m, IsWitnessRunFW (R n m) φ α (δ n m) lmax s2 ρ ∧ (R n m).IsSizedRun c C0 Bmax) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m → sampleLaw P Q n m
      {ω | (R n m).alphaLo α (δ n m) ω.1 ω.2 < gridBelow α (StatFormal.Distances.tvDist P Q)} ≤ ENNReal.ofReal ε := by
  rcases gridBelow_spec α (StatFormal.Distances.tvDist P Q) with ⟨j, hj, hgb⟩ | ⟨-, hgb⟩
  · have hD : 0 < Dpop φ P Q (α j) := by
      refine lt_of_le_of_ne (Dpop_nonneg _ _ _ _) fun h => ?_
      have := (StatFormal.TrimmedMMD.ZeroSet.zeroeq 𝒳 H P Q φ κ (α j) hφ hκ hchar (hgrid.2 j).1 (hgrid.2 j).2).1 h.symm
      linarith
    obtain ⟨N₀, hN₀⟩ := core_eventually_fw φ κ Dφ (fun _ _ => J) (fun _ _ => α) δ lmax s2 c C0 Bmax R hφ hκ hDφ
      (fun _ _ => hgrid) hδ hL (const_small _) hl0 hl1 hs2 hc hρ0 hρ1 hR ((1 - ρ / 2) * Dpop φ P Q (α j)) (α j)
      (mul_pos (by linarith) hD) (hgrid.2 j).2 ε hε
    refine ⟨N₀, fun n m hn hm => ?_⟩
    rw [hgb]
    exact hN₀ n m hn hm P Q j le_rfl le_rfl
  · refine ⟨0, fun n m _ _ => (measure_mono (t := ∅) fun ω hω => ?_).trans (by simp)⟩
    simp only [mem_ofPred_eq, hgb] at hω
    exact absurd hω (not_lt.2 (run_alphaLo_nonneg _ hgrid _ _ _))

/-- (copy-adapted from the certified `Wave30tz.Limits.upper_offgrid`, for Frank–Wolfe runs: only admissibility and the
upper fraction bound are used, the certified `Wave30tz.lo_strict_bound` as is) Fixed grid, fixed `δ`, `TV` off the grid: `P(α̂_lo > α_{j*}) → 0` (`lo_strict_bound` with `ζ` the gap from `TV` to the
first level above it). -/
theorem upper_offgrid_fw {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (φ : 𝒳 → H) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (J : ℕ) (α : Fin J → ℝ) (δ lmax s2 c C0 : ℝ) (Bmax : ℕ) (R : ∀ n m : ℕ, LoRun 𝒳 J n m)
    (hgrid : IsGrid α) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hl0 : 0 < lmax) (hl1 : lmax ≤ 1 / 2) (hs2 : 0 < s2) (hc : 0 < c)
    {ρ : ℝ} (hR : ∀ n m, IsWitnessRunFW (R n m) φ α δ lmax s2 ρ ∧ (R n m).IsSizedRun c C0 Bmax)
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
  exact (StatFormal.Wave30tz.lo_strict_bound 𝒳 P Q J n m α δ lmax s2 ζ (R n m) hgrid hδ0 hδ1 hl0 (by linarith) hs2 hW.1
    (fun j k x y z => (hW.2.2 j k x y z).1) hζ hζTV).2.trans (ENNReal.ofReal_le_ofReal (hT _ _ hNT le_rfl))

/-- **T20 (b)**: the certified `Wave30tz.lo_consistency` (the printed three sentences) for families of
`IsWitnessRunFW ρ ∧ IsSizedRun` runs, `0 ≤ ρ < 1`. -/
theorem lo_consistency_fw_route : Claims.lo_consistency_fw := by
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ J α δ lmax s2 c C0 ρ Bmax R hφ hκ hDφ hchar hgrid hδ0 hδ1 hl0 hl1 hs2 hc hρ0 hρ1 hR
  refine ⟨fun n m => (StatFormal.Wave30tz.lo_upper 𝒳 P Q J n m α δ lmax (R n m) hgrid hδ0 hδ1 hl0 (by linarith)
    (hR n m).1.1).2.1, fun ε hε => ?_, fun hoff ε hε => ?_⟩
  · exact lower_gridBelow_fw φ κ Dφ P Q J α (fun _ _ => δ) lmax s2 c C0 Bmax R hφ hκ hDφ hchar hgrid
      (fun _ _ => ⟨hδ0, hδ1⟩) (const_small _) hl0 hl1 hs2 hc hρ0 hρ1 hR ε hε
  · exact upper_offgrid_fw φ P Q J α δ lmax s2 c C0 Bmax R hgrid hδ0 hδ1 hl0 hl1 hs2 hc hR hoff ε hε

end StatFormal.Wave31tr.RouteFW
