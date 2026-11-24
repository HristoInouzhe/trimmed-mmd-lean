import StatFormal.Wave31tl.RouteClaims

/-!
# Wave 31tl route: Theorem 33 (iii) (untrusted proof material)

* `lorate_batches_route`: the default labels give `n_{<1} = b₁`, `n_[1] = b₂ − b₁`, `n_[2] = n − b₂`; with `|b₁ − n/4| ≤ ½`,
  `|b₂ − n/2| ≤ ½`: `b₁ ≥ (n−2)/4`, `b₂ − b₁ ≥ n/4 − 1`, `n − b₂ ≥ n/2 − ½`, so `r₁ ≤ 8/(n∧m − 2) ≤ min{1, 12/(n∧m)}` and
  `N ≥ ¾(n∧m) − 3/2 ≥ (n∧m)/2` for `n∧m ≥ 10`.
* `lorate_iii_route`: with `S = 1 + L_δ + log(J/η)`, `q = √(S/(n∧m))`: `T_fit ≤ 224κq` (`2(1+√2) ≤ 5`, `½log(8/η) ≤ 2S`, `√12 ≤ 3.5`) and
  `T_bet ≤ 192κq/σ²_min` (`1 + 16/σ² ≤ 20/σ²`, `2/σ ≤ 4/σ²`, `√(2/N) ≤ 2/√(n∧m)`), so `t ≤ β⋆·896κq/σ²_min ≤ 1000β⋆κq/σ²_min`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tl

open StatFormal.Wave30tq StatFormal.Wave30tz

namespace Arith

open Finset

/-- `#{i < n : a ≤ i < b} = min b n − a` for `a ≤ min b n`. -/
lemma card_fin_Ico (n a b : ℕ) (ha : a ≤ min b n) :
    (univ.filter fun i : Fin n => a ≤ (i : ℕ) ∧ (i : ℕ) < b).card = min b n - a := by
  have e : (univ.filter fun i : Fin n => a ≤ (i : ℕ) ∧ (i : ℕ) < b).map Fin.valEmbedding = Finset.Ico a (min b n) := by
    ext k
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_Ico, lt_min_iff]
    constructor
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2, i.isLt⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨k, h3⟩, ⟨h1, h2⟩, rfl⟩
  rw [← card_map, e, Nat.card_Ico]

lemma label_lt_one {b1 b2 i : ℕ} : defaultLabel b1 b2 i < 1 ↔ i < b1 := by
  unfold defaultLabel; split_ifs <;> constructor <;> intro h <;> omega

lemma label_eq_one {b1 b2 i : ℕ} (h : b1 ≤ b2) : defaultLabel b1 b2 i = 1 ↔ b1 ≤ i ∧ i < b2 := by
  unfold defaultLabel
  rcases Nat.lt_or_ge i b1 with h1 | h1
  · rw [if_pos h1]
    constructor
    · intro h'; exact absurd h' (by norm_num)
    · rintro ⟨h2, -⟩; omega
  · rw [if_neg (by omega)]
    rcases Nat.lt_or_ge i b2 with h2 | h2
    · rw [if_pos h2]; exact ⟨fun _ => ⟨h1, h2⟩, fun _ => rfl⟩
    · rw [if_neg (by omega)]
      constructor
      · intro h'; exact absurd h' (by norm_num)
      · rintro ⟨-, h3⟩; omega

lemma label_le_two (b1 b2 i : ℕ) : defaultLabel b1 b2 i ≤ 2 := by
  unfold defaultLabel; split_ifs <;> omega

/-- The sizes of the default batches. -/
lemma counts {n b1 b2 : ℕ} (h12 : b1 ≤ b2) (h2n : b2 ≤ n) :
    fitCard (fun i : Fin n => defaultLabel b1 b2 i) 1 = b1 ∧
    batchCount (fun i : Fin n => defaultLabel b1 b2 i) 1 = b2 - b1 ∧
    batchCount (fun i : Fin n => defaultLabel b1 b2 i) 2 = n - b2 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold fitCard
    have e : (univ.filter fun i : Fin n => defaultLabel b1 b2 i < 1) =
        univ.filter fun i : Fin n => 0 ≤ (i : ℕ) ∧ (i : ℕ) < b1 := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, label_lt_one, zero_le]
    rw [e, card_fin_Ico n 0 b1 (by omega)]; omega
  · unfold batchCount
    have e : (univ.filter fun i : Fin n => defaultLabel b1 b2 i = 1) =
        univ.filter fun i : Fin n => b1 ≤ (i : ℕ) ∧ (i : ℕ) < b2 := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, label_eq_one h12]
    rw [e, card_fin_Ico n b1 b2 (by omega)]; omega
  · unfold batchCount
    have e : (univ.filter fun i : Fin n => defaultLabel b1 b2 i = 2) =
        univ.filter fun i : Fin n => b2 ≤ (i : ℕ) ∧ (i : ℕ) < n := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold defaultLabel
      have hi := i.isLt
      rcases Nat.lt_or_ge (i : ℕ) b1 with h1 | h1
      · rw [if_pos h1]
        constructor
        · intro h'; exact absurd h' (by norm_num)
        · rintro ⟨h2, -⟩; omega
      · rw [if_neg (by omega)]
        rcases Nat.lt_or_ge (i : ℕ) b2 with h2 | h2
        · rw [if_pos h2]
          constructor
          · intro h'; exact absurd h' (by norm_num)
          · rintro ⟨h3, -⟩; omega
        · rw [if_neg (by omega)]; exact ⟨fun _ => ⟨h2, hi⟩, fun _ => rfl⟩
    rw [e, card_fin_Ico n b2 n (by omega)]; omega

/-- The nearest-integer boundaries: `b₁ ≤ b₂ ≤ n` and the three size bounds. -/
lemma cuts_bounds {n b1 b2 : ℕ} (hn : 4 ≤ n) (hc : NearestCuts n b1 b2) :
    b1 ≤ b2 ∧ b2 ≤ n ∧ ((n : ℝ) - 2) / 4 ≤ b1 ∧ (n : ℝ) / 4 - 1 ≤ (b2 : ℝ) - b1 ∧ (n : ℝ) / 2 - 1 / 2 ≤ (n : ℝ) - b2 := by
  obtain ⟨h1, h2⟩ := hc
  rw [abs_le] at h1 h2
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have h12 : b1 ≤ b2 := by
    have : (b1 : ℝ) < b2 + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have h2n : b2 ≤ n := by
    have : (b2 : ℝ) < n + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  exact ⟨h12, h2n, by linarith, by linarith, by linarith⟩

end Arith

open Arith

/-- **Theorem 33 (iii)**, the default batches. -/
theorem lorate_batches_route : Claims.lorate_batches := by
  intro n m bn1 bn2 bm1 bm2 hM hcn hcm
  have hn : 10 ≤ n := le_trans hM (min_le_left _ _)
  have hm : 10 ≤ m := le_trans hM (min_le_right _ _)
  obtain ⟨hn12, hn2, hn0, hn1, hn2'⟩ := cuts_bounds (by omega) hcn
  obtain ⟨hm12, hm2, hm0, hm1, hm2'⟩ := cuts_bounds (by omega) hcm
  obtain ⟨cn0, cn1, cn2⟩ := counts hn12 hn2
  obtain ⟨cm0, cm1, cm2⟩ := counts hm12 hm2
  set M : ℝ := ((min n m : ℕ) : ℝ) with hMdef
  have hM10 : (10 : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast hM
  have hMn : M ≤ n := by rw [hMdef]; exact_mod_cast min_le_left n m
  have hMm : M ≤ m := by rw [hMdef]; exact_mod_cast min_le_right n m
  have hb1 : (M - 2) / 4 ≤ bn1 := le_trans (by linarith) hn0
  have hb1' : (M - 2) / 4 ≤ bm1 := le_trans (by linarith) hm0
  have hpos : 0 < (M - 2) / 4 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cn0]; exact_mod_cast (show (1 : ℝ) ≤ bn1 by linarith)
  · rw [cm0]; exact_mod_cast (show (1 : ℝ) ≤ bm1 by linarith)
  · unfold rOne
    rw [cn0, cm0]
    have h1 : 1 / (bn1 : ℝ) ≤ 1 / ((M - 2) / 4) := one_div_le_one_div_of_le hpos hb1
    have h2 : 1 / (bm1 : ℝ) ≤ 1 / ((M - 2) / 4) := one_div_le_one_div_of_le hpos hb1'
    have h3 : 1 / ((M - 2) / 4) + 1 / ((M - 2) / 4) = 8 / (M - 2) := by field_simp; ring
    have h4 : 8 / (M - 2) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h5 : 8 / (M - 2) ≤ 12 / M := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
    exact le_min (by linarith) (by linarith)
  · unfold defaultPairs
    rw [cn1, cn2, cm1, cm2]
    push_cast [hn12, hm12, hn2, hm2]
    have e1 : M / 4 - 1 ≤ min ((bn2 : ℝ) - bn1) ((bm2 : ℝ) - bm1) := le_min (by linarith) (by linarith)
    have e2 : M / 2 - 1 / 2 ≤ min ((n : ℝ) - bn2) ((m : ℝ) - bm2) := le_min (by linarith) (by linarith)
    have : ((min (bn2 - bn1) (bm2 - bm1) + min (n - bn2) (m - bm2) : ℕ) : ℝ) =
        min ((bn2 : ℝ) - bn1) ((bm2 : ℝ) - bm1) + min ((n : ℝ) - bn2) ((m : ℝ) - bm2) := by
      push_cast [Nat.cast_min, Nat.cast_sub hn12, Nat.cast_sub hm12, Nat.cast_sub hn2, Nat.cast_sub hm2]; ring
    linarith

/-- **Theorem 33 (iii)**, the `O(·)` with the constant 1000. -/
theorem lorate_iii_route : Claims.lorate_iii := by
  intro κ Dφ c₀ γ αs s2 δ η J n m bn1 bn2 bm1 bm2 hDφ0 hD2 hc0 hγ hαs0 hαs1 hs20 hs24 hδ0 hδ1 hη0 hη1 hJ hM hcn hcm
  obtain ⟨hn1, hm1, hr1, hN⟩ := lorate_batches_route n m bn1 bn2 bm1 bm2 hM hcn hcm
  set lx : Fin n → ℕ := fun i => defaultLabel bn1 bn2 i
  set ly : Fin m → ℕ := fun j => defaultLabel bm1 bm2 j
  set r1 := rOne lx ly with hr1def
  set N := defaultPairs lx ly with hNdef
  set M : ℝ := ((min n m : ℕ) : ℝ) with hMdef
  have hM10 : (10 : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast hM
  have hMpos : 0 < M := by linarith
  set L := Real.log (1 / δ) with hLdef
  have hL : 0 < L := by rw [hLdef, one_div, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  set ℓ := Real.log (J / η) with hℓdef
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
  set S := 1 + L + ℓ with hSdef
  have hS1 : 1 ≤ S := by linarith
  set q := √(S / M) with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hκ0 : 0 ≤ κ := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsS : 1 ≤ √S := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hS1
  have hsqrt2 : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  -- `T_fit ≤ 224 κ q`
  have hTfit : Tfit κ Dφ η r1 2 ≤ 224 * κ * q := by
    unfold Tfit
    have hlog8 : Real.log (4 * ((2 : ℕ) : ℝ) / η) ≤ 4 * S := by
      have e : Real.log (4 * ((2 : ℕ) : ℝ) / η) = 3 * Real.log 2 + Real.log (1 / η) := by
        rw [show 4 * ((2 : ℕ) : ℝ) / η = 2 ^ 3 * (1 / η) by push_cast; ring, Real.log_mul (by norm_num) (by positivity),
          Real.log_pow]; push_cast; ring
      have h1 : Real.log (1 / η) ≤ ℓ := Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hJr hη0.le)
      rw [e]; linarith
    have hsq : √(1 / 2 * Real.log (4 * ((2 : ℕ) : ℝ) / η)) ≤ 3 / 2 * √S := by
      calc √(1 / 2 * Real.log (4 * ((2 : ℕ) : ℝ) / η)) ≤ √(2 * S) := Real.sqrt_le_sqrt (by linarith)
        _ = √2 * √S := Real.sqrt_mul (by norm_num) S
        _ ≤ 3 / 2 * √S := mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg _)
    have hX : 2 * (1 + √2) * κ + Dφ * √(1 / 2 * Real.log (4 * ((2 : ℕ) : ℝ) / η)) ≤ 8 * κ * √S := by
      have h1 : 2 * (1 + √2) * κ ≤ 5 * κ * √S := by
        have : 2 * (1 + √2) ≤ 5 := by linarith
        nlinarith
      have h2 : Dφ * √(1 / 2 * Real.log (4 * ((2 : ℕ) : ℝ) / η)) ≤ 2 * κ * (3 / 2 * √S) :=
        mul_le_mul hD2 hsq (Real.sqrt_nonneg _) (by linarith)
      nlinarith
    have hr : √r1 ≤ √12 * √(1 / M) := by
      rw [← Real.sqrt_mul (by norm_num), show (12 : ℝ) * (1 / M) = 12 / M by ring]
      exact Real.sqrt_le_sqrt (hr1.trans (min_le_right _ _))
    have h12 : √12 ≤ 7 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hSq : √S * √(1 / M) = q := by rw [← Real.sqrt_mul (by linarith), hqdef]; congr 1; ring
    have hr0 : 0 ≤ √r1 := Real.sqrt_nonneg _
    calc 8 * (2 * (1 + √2) * κ + Dφ * √(1 / 2 * Real.log (4 * ((2 : ℕ) : ℝ) / η))) * √r1
        ≤ 8 * (8 * κ * √S) * (√12 * √(1 / M)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hX (by norm_num)) hr hr0 (by positivity)
      _ = 64 * κ * √12 * (√S * √(1 / M)) := by ring
      _ = 64 * κ * √12 * q := by rw [hSq]
      _ ≤ 64 * κ * (7 / 2) * q := by gcongr
      _ = 224 * κ * q := by ring
  -- `T_bet ≤ 192 κ q / s2`
  have hTbet : Tbet Dφ s2 L η J N ≤ 192 * κ / s2 * q := by
    unfold Tbet
    have hNr : M / 2 ≤ (N : ℝ) := hN
    have hNpos : (0 : ℝ) < N := by linarith
    have hs2s : √s2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; linarith
    have hs2p : 0 < √s2 := Real.sqrt_pos.2 hs20
    have h1 : 1 + 16 / s2 ≤ 20 / s2 := by
      have h4 : 1 ≤ 4 / s2 := by rw [le_div_iff₀ hs20]; linarith
      have e : 20 / s2 = 4 / s2 + 16 / s2 := by ring
      linarith
    have h2 : 2 / √s2 ≤ 4 / s2 := by
      rw [div_le_div_iff₀ hs2p hs20]
      have : s2 = √s2 * √s2 := (Real.mul_self_sqrt hs20.le).symm
      nlinarith
    have hlogJ : Real.log (2 * (J : ℝ) / η) ≤ S := by
      rw [show 2 * (J : ℝ) / η = 2 * (J / η) by ring, Real.log_mul (by norm_num) (by positivity)]; linarith
    have hY : (1 + 16 / s2) * √L + 2 / √s2 * √(Real.log (2 * (J : ℝ) / η)) ≤ 24 / s2 * √S := by
      have hL' : √L ≤ √S := Real.sqrt_le_sqrt (by linarith)
      have hJ' : √(Real.log (2 * (J : ℝ) / η)) ≤ √S := Real.sqrt_le_sqrt hlogJ
      have a1 : (1 + 16 / s2) * √L ≤ 20 / s2 * √S := mul_le_mul h1 hL' (Real.sqrt_nonneg _) (by positivity)
      have a2 : 2 / √s2 * √(Real.log (2 * (J : ℝ) / η)) ≤ 4 / s2 * √S :=
        mul_le_mul h2 hJ' (Real.sqrt_nonneg _) (by positivity)
      have : 20 / s2 * √S + 4 / s2 * √S = 24 / s2 * √S := by ring
      linarith
    have hN2 : √(2 / (N : ℝ)) ≤ √(4 / M) := Real.sqrt_le_sqrt (by
      rw [div_le_div_iff₀ hNpos hMpos]; linarith)
    have hSq : √(4 / M) * √S = 2 * q := by
      rw [← Real.sqrt_mul (by positivity), hqdef, show 4 / M * S = 2 ^ 2 * (S / M) by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    calc 2 * Dφ * √(2 / (N : ℝ)) * ((1 + 16 / s2) * √L + 2 / √s2 * √(Real.log (2 * (J : ℝ) / η)))
        ≤ 2 * (2 * κ) * √(4 / M) * (24 / s2 * √S) := by
          refine mul_le_mul (mul_le_mul (by linarith) hN2 (Real.sqrt_nonneg _) (by positivity)) hY
            (by positivity) (by positivity)
      _ = 96 * κ / s2 * (√(4 / M) * √S) := by ring
      _ = 192 * κ / s2 * q := by rw [hSq]; ring
  have hβ0 : 0 < beta αs := by
    unfold beta
    have : 0 < 1 - αs := by linarith
    positivity
  have hmax : max (Tfit κ Dφ η r1 2) (Tbet Dφ s2 L η J N) ≤ 1000 * κ / s2 * q := by
    have h1 : 224 * κ * q ≤ 1000 * κ / s2 * q := by
      have : 224 ≤ 1000 / s2 := by rw [le_div_iff₀ hs20]; linarith
      have hκq : 0 ≤ κ * q := mul_nonneg hκ0 hq0
      calc 224 * κ * q = 224 * (κ * q) := by ring
        _ ≤ 1000 / s2 * (κ * q) := mul_le_mul_of_nonneg_right this hκq
        _ = 1000 * κ / s2 * q := by ring
    have h2 : 192 * κ / s2 * q ≤ 1000 * κ / s2 * q := by
      have : 0 ≤ κ / s2 * q := by positivity
      have e1 : 192 * κ / s2 * q = 192 * (κ / s2 * q) := by ring
      have e2 : 1000 * κ / s2 * q = 1000 * (κ / s2 * q) := by ring
      linarith
    exact max_le (hTfit.trans h1) (hTbet.trans h2)
  have ht : tNM κ Dφ αs s2 δ η r1 2 J N ≤ 1000 * beta αs * κ / s2 * q := by
    unfold tNM
    calc beta αs * max (Tfit κ Dφ η r1 2) (Tbet Dφ s2 L η J N) ≤ beta αs * (1000 * κ / s2 * q) :=
          mul_le_mul_of_nonneg_left hmax hβ0.le
      _ = 1000 * beta αs * κ / s2 * q := by ring
  refine ⟨ht, ?_⟩
  have ht0 : 0 ≤ tNM κ Dφ αs s2 δ η r1 2 J N := by
    unfold tNM
    refine mul_nonneg hβ0.le (le_trans ?_ (le_max_left _ _))
    unfold Tfit; positivity
  refine Real.rpow_le_rpow (div_nonneg ht0 hc0.le) ?_ (by positivity)
  rw [div_le_iff₀ hc0]
  calc tNM κ Dφ αs s2 δ η r1 2 J N ≤ 1000 * beta αs * κ / s2 * q := ht
    _ = 1000 * κ / (c₀ * (1 - αs) * s2) * q * c₀ := by
        unfold beta; field_simp

end StatFormal.Wave31tl
