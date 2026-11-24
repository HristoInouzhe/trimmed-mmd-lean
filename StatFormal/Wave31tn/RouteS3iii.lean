import StatFormal.Wave31tn.Statements
import StatFormal.Wave31tl.Proofs

/-!
# Wave 31tn route: S3 (iii) `cor:minimax`, the split-sample estimator (untrusted proof material)

The certified `Wave31tl.lorate_i` (Theorem 33 (i)) at `ε = C_ε/√N`, `h₀ = 1/√N` (the exact gap of `rootGrid`), `γ = 1`, `B = 2`:
`J_ε ≤ 2(1 + C_ε)` does not grow with `N`; with `r₁ ≤ 12/N`, `R.N ≥ N/2` (certified `Wave31tl.lorate_batches`), `T_fit ≤ A/√N` and
`T_bet ≤ (b₀ + b₁√log(4(1+C_ε)/η))/√N`, and `C_ε = max(1, A/c′, 2b₀/c′, 32b₁²/(ηc′²))`, `c′ = c₀(1−a₁)`, makes
`β⋆ max{T_fit, T_bet} ≤ c₀ε` (`log y ≤ y`, so `b₁√log(4(1+C_ε)/η) ≤ b₁√(8C_ε/η) ≤ c′C_ε/2`). Then `P(α̂_lo < a_ε) ≤ η` and
`a_ε ≥ α⋆ − ε − 1/√N` on `rootGrid`, so `C = C_ε + 1`; when `ε > α⋆` the event is empty (`α̂_lo ≥ 0`). Validity: the certified
`Wave30tz.lo_upper` (`gridBelow α⋆ ≤ α⋆`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tn

namespace RouteS3iii

open StatFormal.Wave30tz StatFormal.Wave31tl

lemma rootLevels_pos {N : ℕ} (hN : (10 : ℝ) ≤ N) : 1 ≤ rootLevels N := by
  unfold rootLevels
  have h1 : (1 : ℝ) < √(N : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have : 1 < ⌈√(N : ℝ)⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast h1)
  omega

lemma succ_lt_sqrt {N : ℕ} (j : Fin (rootLevels N)) : ((j : ℕ) + 1 : ℝ) < √(N : ℝ) := by
  have hj := j.2
  unfold rootLevels at hj
  have h1 : (j : ℕ) + 1 ≤ ⌈√(N : ℝ)⌉₊ - 1 := hj
  have h2 : (((⌈√(N : ℝ)⌉₊ - 1 : ℕ)) : ℝ) < √(N : ℝ) := by
    have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (N : ℝ))
    have hpos : 1 ≤ ⌈√(N : ℝ)⌉₊ := by omega
    rw [Nat.cast_sub hpos, Nat.cast_one]; linarith
  calc ((j : ℕ) + 1 : ℝ) = (((j : ℕ) + 1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (((⌈√(N : ℝ)⌉₊ - 1 : ℕ)) : ℝ) := by exact_mod_cast h1
    _ < √(N : ℝ) := h2

lemma rootGrid_isGrid {N : ℕ} (hN : 1 ≤ N) : IsGrid (rootGrid N) := by
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  refine ⟨fun i j hij => ?_, fun j => ⟨by unfold rootGrid; positivity, ?_⟩⟩
  · unfold rootGrid
    have : ((i : ℕ) : ℝ) < (j : ℕ) := by exact_mod_cast hij
    exact div_lt_div_of_pos_right (by linarith) hs
  · unfold rootGrid
    rw [div_lt_one hs]; exact succ_lt_sqrt j

lemma rootGrid_gaps {N : ℕ} : GapsGe (rootGrid N) (1 / √(N : ℝ)) := by
  intro j hj
  unfold rootGrid
  apply le_of_eq
  push_cast
  ring

/-- `x − 1/√N ≤ a(x)` on `rootGrid N` for `x ∈ [0,1)`. -/
lemma gridFloor_root {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x - 1 / √(N : ℝ) ≤ gridFloor (rootGrid N) x := by
  classical
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hfl0 : 0 ≤ gridFloor (rootGrid N) x := by
    unfold gridFloor; split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  set k := ⌊x * √(N : ℝ)⌋₊ with hk
  have hkle : (k : ℝ) ≤ x * √(N : ℝ) := Nat.floor_le (by positivity)
  have hklt : x * √(N : ℝ) < k + 1 := Nat.lt_floor_add_one _
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · have : x < 1 / √(N : ℝ) := by
      rw [lt_div_iff₀ hs]; rw [hk0] at hklt; simpa using hklt
    linarith
  · have hkJ : k - 1 < rootLevels N := by
      unfold rootLevels
      have h1 : (k : ℝ) < ⌈√(N : ℝ)⌉₊ :=
        lt_of_le_of_lt hkle (lt_of_lt_of_le (by nlinarith) (Nat.le_ceil _))
      have : k < ⌈√(N : ℝ)⌉₊ := by exact_mod_cast h1
      omega
    set j : Fin (rootLevels N) := ⟨k - 1, hkJ⟩
    have hj : rootGrid N j = k / √(N : ℝ) := by
      unfold rootGrid
      simp only [j]
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one, sub_add_cancel]
    have hjx : rootGrid N j ≤ x := by rw [hj, div_le_iff₀ hs]; linarith
    have hmem : j ∈ Finset.univ.filter fun i => rootGrid N i ≤ x := by simp [hjx]
    have hne : (Finset.univ.filter fun i => rootGrid N i ≤ x).Nonempty := ⟨j, hmem⟩
    have hle : rootGrid N j ≤ gridFloor (rootGrid N) x := by
      unfold gridFloor
      rw [dif_pos hne]
      exact (Finset.le_sup' _ hmem).trans (le_max_right _ _)
    have : x - 1 / √(N : ℝ) < rootGrid N j := by
      rw [hj, lt_div_iff₀ hs, sub_mul, one_div, inv_mul_cancel₀ hs.ne']; linarith
    linarith

/-! ### The constants -/

/-- `A = 8[2(1+√2)κ + Δ_φ√(½ log(8/η))]√12`, so that `T_fit(η) ≤ A/√N` when `r₁ ≤ 12/N`, `B = 2`. -/
def Afit (κ Dφ η : ℝ) : ℝ := 8 * (2 * (1 + √2) * κ + Dφ * √(1 / 2 * Real.log (4 * ((2 : ℕ) : ℝ) / η))) * √12

/-- `b₀ = 4Δ_φ(1 + 16/σ²_min)√L_δ`. -/
def b0 (Dφ s2 δ : ℝ) : ℝ := 4 * Dφ * ((1 + 16 / s2) * √(Real.log (1 / δ)))

/-- `b₁ = 4Δ_φ · 2/σ_min`. -/
def b1 (Dφ s2 : ℝ) : ℝ := 4 * Dφ * (2 / √s2)

/-- `C_ε = max(1, A/c′, 2b₀/c′, 32b₁²/(ηc′²))`, `c′ = c₀(1−a₁)`. -/
def cE (κ Dφ a₁ c₀ s2 δ η : ℝ) : ℝ :=
  max (max 1 (Afit κ Dφ η / (c₀ * (1 - a₁))))
    (max (2 * b0 Dφ s2 δ / (c₀ * (1 - a₁))) (32 * b1 Dφ s2 ^ 2 / (η * (c₀ * (1 - a₁)) ^ 2)))

lemma tfit_le {κ Dφ η r1 N : ℝ} (hκ : 0 ≤ κ) (hD : 0 ≤ Dφ) (hη0 : 0 < η) (hη1 : η < 1) (hN : 0 < N)
    (hr : r1 ≤ 12 / N) : Tfit κ Dφ η r1 2 ≤ Afit κ Dφ η / √N := by
  unfold Tfit Afit
  have hl : 0 ≤ Real.log (4 * ((2 : ℕ) : ℝ) / η) :=
    Real.log_nonneg (by rw [le_div_iff₀ hη0]; push_cast; linarith)
  have hbr : 0 ≤ 8 * (2 * (1 + √2) * κ + Dφ * √(1 / 2 * Real.log (4 * ((2 : ℕ) : ℝ) / η))) := by positivity
  have hsq : √r1 ≤ √12 / √N := by
    rw [← Real.sqrt_div (by norm_num)]; exact Real.sqrt_le_sqrt hr
  calc _ ≤ 8 * (2 * (1 + √2) * κ + Dφ * √(1 / 2 * Real.log (4 * ((2 : ℕ) : ℝ) / η))) * (√12 / √N) :=
        mul_le_mul_of_nonneg_left hsq hbr
    _ = _ := by ring

lemma tbet_le {Dφ s2 L η J' X N : ℝ} {Np : ℕ} (hD : 0 ≤ Dφ) (hs2 : 0 < s2) (hL : 0 ≤ L) (hη0 : 0 < η)
    (hJ1 : 1 ≤ J') (hJX : J' ≤ X) (hN : 0 < N) (hp : N / 2 ≤ Np) :
    Tbet Dφ s2 L η J' Np ≤ 4 * Dφ * ((1 + 16 / s2) * √L + 2 / √s2 * √(Real.log (2 * X / η))) / √N := by
  unfold Tbet
  have hNp : (0 : ℝ) < Np := by linarith
  have h2 : √(2 / (Np : ℝ)) ≤ 2 / √N := by
    have : 2 / (Np : ℝ) ≤ 4 / N := by
      rw [div_le_div_iff₀ hNp hN]; linarith
    calc √(2 / (Np : ℝ)) ≤ √(4 / N) := Real.sqrt_le_sqrt this
      _ = 2 / √N := by rw [Real.sqrt_div (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hlog : Real.log (2 * J' / η) ≤ Real.log (2 * X / η) :=
    Real.log_le_log (by positivity) (by gcongr)
  have hbr : (1 + 16 / s2) * √L + 2 / √s2 * √(Real.log (2 * J' / η)) ≤
      (1 + 16 / s2) * √L + 2 / √s2 * √(Real.log (2 * X / η)) := by
    gcongr
  have hbr0 : 0 ≤ (1 + 16 / s2) * √L + 2 / √s2 * √(Real.log (2 * J' / η)) := by positivity
  calc 2 * Dφ * √(2 / (Np : ℝ)) * ((1 + 16 / s2) * √L + 2 / √s2 * √(Real.log (2 * J' / η)))
      ≤ 2 * Dφ * (2 / √N) * ((1 + 16 / s2) * √L + 2 / √s2 * √(Real.log (2 * X / η))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h2 (by linarith)) hbr hbr0 (by positivity)
    _ = _ := by ring

lemma sq_le_imp {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u ^ 2 ≤ v ^ 2) : u ≤ v := by
  calc u = √(u ^ 2) := (Real.sqrt_sq hu).symm
    _ ≤ √(v ^ 2) := Real.sqrt_le_sqrt h
    _ = v := Real.sqrt_sq hv

/-- `max{A, b₀ + b₁√log(4(1+C_ε)/η)} ≤ c′C_ε`. -/
lemma key_const {κ Dφ a₁ c₀ s2 δ η : ℝ} (hc : 0 < c₀ * (1 - a₁)) (hη0 : 0 < η) (hη1 : η < 1)
    (hb0 : 0 ≤ b0 Dφ s2 δ) (hb1 : 0 ≤ b1 Dφ s2) :
    max (Afit κ Dφ η) (b0 Dφ s2 δ + b1 Dφ s2 * √(Real.log (2 * (2 * (1 + cE κ Dφ a₁ c₀ s2 δ η)) / η))) ≤
      c₀ * (1 - a₁) * cE κ Dφ a₁ c₀ s2 δ η := by
  set c' := c₀ * (1 - a₁) with hc'
  set C := cE κ Dφ a₁ c₀ s2 δ η with hC
  have hC1 : 1 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCA : Afit κ Dφ η / c' ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCb0 : 2 * b0 Dφ s2 δ / c' ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCb1 : 32 * b1 Dφ s2 ^ 2 / (η * c' ^ 2) ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  rw [div_le_iff₀ hc] at hCA hCb0
  rw [div_le_iff₀ (by positivity)] at hCb1
  have hy : 0 < 2 * (2 * (1 + C)) / η := by positivity
  have hl : Real.log (2 * (2 * (1 + C)) / η) ≤ 8 * C / η := by
    have := Real.log_le_sub_one_of_pos hy
    have h2 : 2 * (2 * (1 + C)) / η ≤ 8 * C / η := div_le_div_of_nonneg_right (by linarith) hη0.le
    linarith
  have hsq : √(Real.log (2 * (2 * (1 + C)) / η)) ≤ √(8 * C / η) := Real.sqrt_le_sqrt hl
  have hb1' : b1 Dφ s2 * √(8 * C / η) ≤ c' * C / 2 := by
    apply sq_le_imp (by positivity) (by positivity)
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hCη : 0 < C / (4 * η) := by positivity
    have := mul_le_mul_of_nonneg_left hCb1 hCη.le
    field_simp at this ⊢
    nlinarith
  apply max_le
  · linarith
  · have := mul_le_mul_of_nonneg_left hsq hb1
    linarith

/-! ### The claim -/

lemma label_le_two' (b1 b2 i : ℕ) : defaultLabel b1 b2 i ≤ 2 := by
  unfold defaultLabel; split_ifs <;> omega

lemma gridBelow_le' {J : ℕ} (α : Fin J → ℝ) {a : ℝ} (ha : 0 ≤ a) : gridBelow α a ≤ a := by
  classical
  unfold gridBelow
  split_ifs with h
  · exact Finset.sup'_le _ _ fun j hj => (Finset.mem_filter.1 hj).2.le
  · exact ha

theorem minimax_iii_route : Claims.minimax_iii := by
  intro κ Dφ a₁ c₀ s2 δ η ha10 ha11 hc0 hs20 hs24 hδ0 hδ1 hη0 hη1
  set C := cE κ Dφ a₁ c₀ s2 δ η with hCdef
  refine ⟨C + 1, 10, ?_⟩
  intro a₀ 𝒳 H _ _ _ _ _ φ n m P Q R hφ hκ hD hD2 ha00 ha0a1 hN hM hRun hdef
  obtain ⟨hP, hQ, hlo, hhi, hpm⟩ := hM
  haveI := hP
  haveI := hQ
  set αs := StatFormal.Distances.tvDist P Q with hαs
  have hαs0 : 0 ≤ αs := StatFormal.Distances.tvDist_nonneg P Q
  have hαs1 : αs < 1 := by linarith
  have hN10 : (10 : ℝ) ≤ ((min n m : ℕ) : ℝ) := (le_max_right _ _).trans hN
  have hN10' : 10 ≤ min n m := by exact_mod_cast hN10
  have hN1 : 1 ≤ min n m := by omega
  have hgrid := rootGrid_isGrid hN1
  have hJ := rootLevels_pos hN10
  have hNpos : (0 : ℝ) < ((min n m : ℕ) : ℝ) := by linarith
  have hsN : 0 < √((min n m : ℕ) : ℝ) := Real.sqrt_pos.2 hNpos
  have hpos := fun (ω : (Fin n → 𝒳) × (Fin m → 𝒳)) =>
    StatFormal.Wave30tz.Limits.run_alphaLo_nonneg R hgrid δ ω.1 ω.2
  constructor
  · -- validity: `cor:lower`
    have hup := (StatFormal.Wave30tz.lo_upper 𝒳 P Q _ n m (rootGrid (min n m)) δ (1 / 2) R hgrid hδ0 hδ1
      (by norm_num) (by norm_num) hRun.1).2.1
    refine le_trans (measure_mono fun ω hω => ?_) hup
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact lt_of_le_of_lt (gridBelow_le' _ hαs0) hω
  · haveI : Nonempty 𝒳 := MeasureTheory.Measure.nonempty_of_neZero P
    obtain ⟨x0⟩ := (inferInstance : Nonempty 𝒳)
    have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
    have hD0 : 0 ≤ Dφ := by simpa using hD x0 x0
    have hC1 : 1 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
    set ε := C / √((min n m : ℕ) : ℝ) with hεdef
    by_cases hεα : ε ≤ αs
    · -- Theorem 33 (i)
      obtain ⟨bn1, bn2, bm1, bm2, hcn, hcm, hlx, hly, hNp⟩ := hdef
      have hlxe : R.lx = fun i : Fin n => defaultLabel bn1 bn2 i := funext hlx
      have hlye : R.ly = fun j : Fin m => defaultLabel bm1 bm2 j := funext hly
      obtain ⟨hn1', hm1', hr1', hN'⟩ := StatFormal.Wave31tl.lorate_batches n m bn1 bn2 bm1 bm2 hN10' hcn hcm
      have hB : ∀ k, R.bat k ≤ 2 := by
        intro k
        obtain ⟨i, hi⟩ := hRun.1.1.1.1 k
        rw [← hRun.1.1.2.2.2.1 k i hi, hlx]
        exact label_le_two' _ _ _
      have hn1 : 1 ≤ fitCard R.lx 1 := by rw [hlxe]; exact hn1'
      have hm1 : 1 ≤ fitCard R.ly 1 := by rw [hlye]; exact hm1'
      have hr1 : rOne R.lx R.ly ≤ min 1 (12 / ((min n m : ℕ) : ℝ)) := by rw [hlxe, hlye]; exact hr1'
      have hpairs : ((min n m : ℕ) : ℝ) / 2 ≤ (R.N : ℝ) := by rw [hNp, hlxe, hlye]; exact hN'
      have hRN : 1 ≤ R.N := by
        have : (1 : ℝ) ≤ R.N := by linarith
        exact_mod_cast this
      have hε0 : 0 < ε := by rw [hεdef]; positivity
      have hratio : ε / (1 / √((min n m : ℕ) : ℝ)) = C := by rw [hεdef]; field_simp
      have hJ1 : (1 : ℝ) ≤ Jeps (rootLevels (min n m)) ε (1 / √((min n m : ℕ) : ℝ)) := by
        unfold Jeps; rw [hratio]
        exact le_min (by exact_mod_cast hJ) (by linarith)
      have hJX : Jeps (rootLevels (min n m)) ε (1 / √((min n m : ℕ) : ℝ)) ≤ 2 * (1 + C) := by
        unfold Jeps; rw [hratio]; exact min_le_right _ _
      have hb0 : 0 ≤ b0 Dφ s2 δ := by unfold b0; positivity
      have hb1 : 0 ≤ b1 Dφ s2 := by unfold b1; positivity
      have hL : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
      have hTf := tfit_le (r1 := rOne R.lx R.ly) hκ0 hD0 hη0 hη1 hNpos (hr1.trans (min_le_right _ _))
      have hTb := tbet_le (Np := R.N) hD0 hs20 hL hη0 hJ1 hJX hNpos hpairs
      have hkey := key_const (κ := κ) (Dφ := Dφ) (a₁ := a₁) (c₀ := c₀) (s2 := s2) (δ := δ) (by nlinarith) hη0 hη1 hb0 hb1
      have hBv : 4 * Dφ * ((1 + 16 / s2) * √(Real.log (1 / δ)) + 2 / √s2 * √(Real.log (2 * (2 * (1 + C)) / η))) =
          b0 Dφ s2 δ + b1 Dφ s2 * √(Real.log (2 * (2 * (1 + C)) / η)) := by unfold b0 b1; ring
      rw [hBv] at hTb
      have hmax : max (Tfit κ Dφ η (rOne R.lx R.ly) 2)
            (Tbet Dφ s2 (Real.log (1 / δ)) η (Jeps (rootLevels (min n m)) ε (1 / √((min n m : ℕ) : ℝ))) R.N) ≤
          c₀ * (1 - a₁) * C / √((min n m : ℕ) : ℝ) := by
        refine max_le (hTf.trans ?_) (hTb.trans ?_)
        · exact div_le_div_of_nonneg_right ((le_max_left _ _).trans hkey) hsN.le
        · exact div_le_div_of_nonneg_right ((le_max_right _ _).trans hkey) hsN.le
      have hbeta : StatFormal.Wave30tq.beta αs ≤ 1 / (1 - a₁) := by
        unfold StatFormal.Wave30tq.beta
        exact one_div_le_one_div_of_le (by linarith) (by linarith)
      have hTf0 : 0 ≤ Tfit κ Dφ η (rOne R.lx R.ly) 2 := by
        unfold Tfit
        have : 0 ≤ Real.log (4 * ((2 : ℕ) : ℝ) / η) :=
          Real.log_nonneg (by rw [le_div_iff₀ hη0]; push_cast; linarith)
        positivity
      have hcond : StatFormal.Wave30tq.beta αs * max (Tfit κ Dφ η (rOne R.lx R.ly) 2)
            (Tbet Dφ s2 (Real.log (1 / δ)) η (Jeps (rootLevels (min n m)) ε (1 / √((min n m : ℕ) : ℝ))) R.N) ≤
          c₀ * ε ^ (1 : ℝ) := by
        rw [Real.rpow_one]
        have h1a₁ : 0 < 1 - a₁ := by linarith
        calc _ ≤ 1 / (1 - a₁) * (c₀ * (1 - a₁) * C / √((min n m : ℕ) : ℝ)) :=
              mul_le_mul hbeta hmax ((le_max_left _ _).trans' hTf0) (one_div_pos.2 h1a₁).le
          _ = c₀ * ε := by rw [hεdef]; field_simp [show (1 - a₁) ≠ 0 by linarith]
      have hlor := StatFormal.Wave31tl.lorate_i 𝒳 H φ κ Dφ P Q c₀ 1 (rootLevels (min n m)) n m (rootGrid (min n m)) δ s2 η
        (1 / √((min n m : ℕ) : ℝ)) ε R 2 hφ hκ hD hD2 hpm hαs1 hgrid hJ hδ0 hδ1 hs20 hs24 hRun hB hn1 hm1
        (hr1.trans (min_le_left _ _)) hRN hη0 hη1 (by positivity) rootGrid_gaps hε0 hεα hcond
      refine le_trans (measure_mono fun ω hω => ?_) hlor
      simp only [mem_setOf_eq] at hω ⊢
      have hfl := gridFloor_root hN1 (x := αs - ε) (by linarith) (by linarith)
      have : (C + 1) / √((min n m : ℕ) : ℝ) = ε + 1 / √((min n m : ℕ) : ℝ) := by rw [hεdef]; ring
      rw [this] at hω
      linarith
    · -- `ε > α⋆`: the event is empty since `α̂_lo ≥ 0`
      push_neg at hεα
      have hempty : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | (C + 1) / √((min n m : ℕ) : ℝ) <
          αs - R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2} = ∅ := by
        ext ω
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
        have h1 := hpos ω
        have h2 : ε ≤ (C + 1) / √((min n m : ℕ) : ℝ) := by
          rw [hεdef]; exact div_le_div_of_nonneg_right (by linarith) hsN.le
        linarith
      rw [hempty, measure_empty]
      exact zero_le

end RouteS3iii

end StatFormal.Wave31tn
