import StatFormal.Wave31tu.RouteP11
import StatFormal.Wave31tu.RouteP10

set_option linter.style.longLine false

/-!
# Wave31tu, chunk P: Y12 `lap_compare` (Lemma S4.22 `lem:lapcompare`, S4 :1145-1182)

With `Δ(φ) = ∫φ d{(P̃−P) − (Q̃−Q)}`, `Δ̂ = Δ(φ̂)`, `Δ⋆ = Δ(φ⋆)`, `T̂ = err(φ̂)`, `y = V(ε) + g⋆Δ⋆` and `e = E_Pψ̂ − E_Qψ̂ − α`:
(i) `e = ε − T̂`, `e + Δ̂ = D̄̂N̂`, `D̄̂ ≥ y`, `N̂y + T̂ ≤ ε + Δ̂`; (ii) if `κ₀ε − |Δ⋆| − Δ̂ > 0` then `e ≥ κ₀ε − |Δ⋆| − Δ̂`;
(iii) if `|Δ⋆| ≤ κ₀ε/4` then `y ≥ V(ε)/2 ≥ c_Vε^{5/4}/2`.

Route (printed, with the subcases F2 and F8 of CHECK.md: `e + Δ̂ = D̄̂N̂ > 0` closes the cases where the hypothesis of (ii) is not
used): Y10 (`lap_clip_route`), Y11 (`lap_pop_route`), Y9 (`ratio_le_uPath`, for `P̃, Q̃` with `φ⋆` and for `P, Q` at the level
`α⋆ − 2ε` with `φ̂`), Y7 (`lap_const_route`: `ρ₀V(2ε) ≤ V(ε)`, `κ₀ ≤ ρ₀`, `V(ε₀/2) ≥ 2κ₀α⋆`), 31tr T40 (i-2) `excess_i` (G) (the
supporting slope `g⋆ε ≤ V(2ε) − V(ε)`). The real-number case analysis is isolated in `compare_ii_near`, `compare_ii_far`,
`compare_iii_near`, `compare_iii_far`.
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteP

open StatFormal.Distances StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.Concentration
  StatFormal.Wave30tz StatFormal.Wave30tq

/-! ### The real-number core of the case analysis -/

/-- Lemma S4.22 (ii) for `ε < ε₀/2` (`V = V(ε)`, `W = V(2ε)`, `g = g⋆`, `N = N̂`, `D = D̄̂`). -/
theorem compare_ii_near {V W g Δs Δh D N e ε κ : ℝ} (hε : 0 < ε) (hκ1 : κ < 1) (hV : 0 < V) (hW : 0 < W)
    (hκW : κ * W ≤ V) (hsupp : g * ε ≤ W - V) (hg : 0 < g) (hiden : e + Δh = D * N) (hpos : 0 < D * N)
    (hy : V + g * Δs ≤ D) (hN : 0 ≤ N) (hrat : 0 < e + ε → e + ε ≤ W * N) (hyp : 0 < κ * ε - |Δs| - Δh) :
    κ * ε - |Δs| - Δh ≤ e := by
  have habs := abs_nonneg Δs
  have hg' := hg.le
  have hgΔ : -(g * |Δs|) ≤ g * Δs := by
    have := neg_abs_le Δs; nlinarith
  rcases le_or_gt (ε * V) (|Δs| * W) with hbig | hsmall
  · -- `|Δ⋆| ≥ εV(ε)/V(2ε)`: then `κ₀ε ≤ |Δ⋆|`, and `e > −Δ̂` (F8)
    have : κ * ε ≤ |Δs| := by
      by_contra hlt; push Not at hlt
      have h1 : |Δs| * W < κ * ε * W := mul_lt_mul_of_pos_right hlt hW
      have h2 : ε * (κ * W) ≤ ε * V := mul_le_mul_of_nonneg_left hκW hε.le
      nlinarith
    linarith
  · rcases le_or_gt (e + ε) 0 with hneg | hposε
    · -- `e + ε ≤ 0` contradicts the hypothesis of (ii)
      have : ε < Δh := by linarith
      nlinarith
    · have hWN := hrat hposε
      set y := V + g * Δs with hydef
      -- `y > 0`
      have hgs : g * |Δs| * W < (W - V) * V := by
        have h2 : g * ε * V ≤ (W - V) * V := mul_le_mul_of_nonneg_right hsupp hV.le
        have h3 : g * (|Δs| * W) < g * (ε * V) := mul_lt_mul_of_pos_left hsmall hg
        nlinarith
      have hy0 : 0 < y := by
        have : (V - g * |Δs|) * W > V * V := by nlinarith
        nlinarith
      have hyW : y < W := by
        have h0 : g * Δs ≤ g * |Δs| := mul_le_mul_of_nonneg_left (le_abs_self Δs) hg'
        have h1 : y * W ≤ (V + g * |Δs|) * W := mul_le_mul_of_nonneg_right (by rw [hydef]; linarith) hW.le
        nlinarith [sq_nonneg (W - V)]
      -- `e + Δ̂ ≥ N̂y ≥ y(e + ε)/V(2ε)`
      have h1 : (e + Δh) * W ≥ y * (e + ε) := by
        have : y * N ≤ D * N := mul_le_mul_of_nonneg_right hy hN
        have h2 : y * (e + ε) ≤ y * (W * N) := mul_le_mul_of_nonneg_left hWN hy0.le
        nlinarith
      have h2 : y * ε ≥ ε * V - |Δs| * W := by
        have : g * |Δs| * ε ≤ |Δs| * W := by
          have := mul_le_mul_of_nonneg_left (show g * ε ≤ W by linarith) habs
          nlinarith
        nlinarith
      have h3 : e * (W - y) ≥ W * (κ * ε - |Δs| - Δh) := by nlinarith
      have hK : 0 < W * (κ * ε - |Δs| - Δh) := mul_pos hW hyp
      have he : 0 < e := by
        by_contra hle; push Not at hle
        have : e * (W - y) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle (by linarith)
        linarith
      have h4 : e * (W - y) ≤ e * W := by nlinarith
      by_contra hlt; push Not at hlt
      have : e * W < (κ * ε - |Δs| - Δh) * W := mul_lt_mul_of_pos_right hlt hW
      nlinarith

/-- Lemma S4.22 (ii) for `ε ≥ ε₀/2` (`V(ε) ≥ 2κ₀ε`, `g⋆ ≤ 2`, `N̂ ≥ ½`; the case `y < 0` is F2). -/
theorem compare_ii_far {V g Δs Δh D N e ε κ : ℝ} (hV : 2 * κ * ε ≤ V) (hg0 : 0 ≤ g) (hg2 : g ≤ 2)
    (hiden : e + Δh = D * N) (hpos : 0 < D * N) (hy : V + g * Δs ≤ D) (hN : 1 / 2 ≤ N) :
    κ * ε - |Δs| - Δh ≤ e := by
  have habs := abs_nonneg Δs
  have hgΔ : -(g * |Δs|) ≤ g * Δs := by
    have := neg_abs_le Δs; nlinarith
  have hgΔ2 : g * |Δs| ≤ 2 * |Δs| := mul_le_mul_of_nonneg_right hg2 habs
  rcases le_or_gt 0 (V + g * Δs) with hy0 | hy0
  · have h1 : (V + g * Δs) * N ≤ D * N := mul_le_mul_of_nonneg_right hy (by linarith)
    have h2 : (V + g * Δs) * (1 / 2) ≤ (V + g * Δs) * N := mul_le_mul_of_nonneg_left hN hy0
    nlinarith
  · linarith

/-- Lemma S4.22 (iii) for `ε < ε₀/2`. -/
theorem compare_iii_near {V W g Δs ε κ : ℝ} (_hε : 0 < ε) (hκ0 : 0 ≤ κ) (hV : 0 ≤ V) (hκW : κ * W ≤ V)
    (hsupp : g * ε ≤ W - V) (hg : 0 ≤ g) (hΔ : |Δs| ≤ κ * ε / 4) : V / 2 ≤ V + g * Δs := by
  have habs := abs_nonneg Δs
  have hgΔ : -(g * |Δs|) ≤ g * Δs := by
    have := neg_abs_le Δs; nlinarith
  have h1 : g * |Δs| ≤ g * (κ * ε / 4) := mul_le_mul_of_nonneg_left hΔ hg
  have h2 : g * ε * κ ≤ W * κ := mul_le_mul_of_nonneg_right (by linarith) hκ0
  nlinarith

/-- Lemma S4.22 (iii) for `ε ≥ ε₀/2`. -/
theorem compare_iii_far {V g Δs ε κ : ℝ} (hV : 2 * κ * ε ≤ V) (hg0 : 0 ≤ g) (hg2 : g ≤ 2) (hΔ : |Δs| ≤ κ * ε / 4) :
    V / 2 ≤ V + g * Δs := by
  have habs := abs_nonneg Δs
  have hgΔ : -(g * |Δs|) ≤ g * Δs := by
    have := neg_abs_le Δs; nlinarith
  have h1 : g * |Δs| ≤ 2 * (κ * ε / 4) := mul_le_mul hg2 hΔ habs (by norm_num)
  nlinarith

/-- `L(h − c) = L(h)` for probability measures and an integrable `h`. -/
theorem linL_sub_const {𝒳 : Type*} [MeasurableSpace 𝒳] {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {h : 𝒳 → ℝ} (hP : Integrable h P) (hQ : Integrable h Q) (c : ℝ) :
    (∫ z, (h z - c) ∂P) - (∫ z, (h z - c) ∂Q) = linL P Q h := by
  unfold linL
  rw [integral_sub hP (integrable_const c), integral_sub hQ (integrable_const c)]
  simp

/-- `2κ₀ε ≤ V(ε)` once `V(ε) ≥ A ≥ 2κ₀α⋆` and `ε < α⋆`. -/
theorem two_kappa_le {κ ε tv A V : ℝ} (hk : κ * (2 * tv) ≤ A) (hk0 : 0 < κ) (hεtv : ε < tv) (hAV : A ≤ V) :
    2 * κ * ε ≤ V := by
  have : κ * (2 * ε) ≤ κ * (2 * tv) := mul_le_mul_of_nonneg_left (by linarith) hk0.le
  linarith

/-- The path facts of Lemma S4.22: for `ε < ε₀/2`, `V(2ε) > 0`, `κ₀V(2ε) ≤ V(ε)` and the supporting slope
`g⋆ε ≤ V(2ε) − V(ε)`; for `ε ≥ ε₀/2`, `2κ₀ε ≤ V(ε)`. -/
theorem compare_path {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] {φ : ℝ → H} {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {c₁ c₂ ε₀ ε : ℝ} {a b : H} {t u : ℝ} (hsm : StronglyMeasurable φ) (hκφ : ∀ z, ‖φ z‖ ≤ 1)
    (htv1 : tvDist P Q < 1) (hTS : TwoSided54 φ P Q c₁ c₂ ε₀) (hε : 0 < ε) (hεtv : ε < tvDist P Q)
    (ha : a ∈ region φ (tvDist P Q - ε) P) (hb : b ∈ region φ (tvDist P Q - ε) Q)
    (hab : ‖a - b‖ = Dpop φ P Q (tvDist P Q - ε)) (hDpop : 0 < Dpop φ P Q (tvDist P Q - ε))
    (ht : IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - (tvDist P Q - ε)) t)
    (hu : IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (tvDist P Q - ε) u) :
    (ε < ε₀ / 2 → 0 < Wave31ti.uPath φ P Q (tvDist P Q - 2 * ε) ∧
      kappa0 (tvDist P Q) c₁ c₂ ε₀ * Wave31ti.uPath φ P Q (tvDist P Q - 2 * ε) ≤ Wave31ti.uPath φ P Q (tvDist P Q - ε) ∧
      (t - u) * ε ≤ Wave31ti.uPath φ P Q (tvDist P Q - 2 * ε) - Wave31ti.uPath φ P Q (tvDist P Q - ε)) ∧
    (ε₀ / 2 ≤ ε → 2 * kappa0 (tvDist P Q) c₁ c₂ ε₀ * ε ≤ Wave31ti.uPath φ P Q (tvDist P Q - ε)) := by
  obtain ⟨-, -, hk0, -, hcV, hmono, hsand, hcVe, hrho⟩ := lap_const_route H φ 1 P Q c₁ c₂ ε₀ hsm hκφ htv1 hTS
  obtain ⟨hc₁, hc₁₂, hε₀, hε₀α, hTwo⟩ := hTS
  have hα0 : 0 ≤ tvDist P Q - ε := by linarith
  have hα1 : tvDist P Q - ε < 1 := by linarith
  constructor
  · intro hnear
    have hW : 0 < Wave31ti.uPath φ P Q (tvDist P Q - 2 * ε) :=
      lt_of_lt_of_le (mul_pos hcV (Real.rpow_pos_of_pos (by linarith) _)) (hcVe (2 * ε) ⟨by linarith, by linarith⟩)
    have hκW : kappa0 (tvDist P Q) c₁ c₂ ε₀ * Wave31ti.uPath φ P Q (tvDist P Q - 2 * ε) ≤
        Wave31ti.uPath φ P Q (tvDist P Q - ε) :=
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hW.le).trans (hrho ε ⟨hε, hnear⟩)
    have hline := (StatFormal.Wave31tr.excess_i.1 ℝ H P Q φ 1 (tvDist P Q - ε) a b t u hsm hκφ hα0 hα1 hDpop ha hb hab
      ht hu).2 (tvDist P Q - 2 * ε) ⟨by linarith, by linarith⟩
    have hαe : tvDist P Q - 2 * ε - (tvDist P Q - ε) = -ε := by ring
    rw [hαe] at hline
    have h1 : (1 - (tvDist P Q - ε)) * Dpop φ P Q (tvDist P Q - ε) = Wave31ti.uPath φ P Q (tvDist P Q - ε) := rfl
    have h2 : (1 - (tvDist P Q - 2 * ε)) * Dpop φ P Q (tvDist P Q - 2 * ε) =
      Wave31ti.uPath φ P Q (tvDist P Q - 2 * ε) := rfl
    rw [h1, h2] at hline
    exact ⟨hW, hκW, by linarith⟩
  · intro hfar
    have hm := hmono ⟨by linarith, by linarith⟩ ⟨hε.le, hεtv.le⟩ hfar
    have hl := (hsand (ε₀ / 2) ⟨by linarith, by linarith⟩).1
    have hT := (hTwo (ε₀ / 2) ⟨by linarith, by linarith⟩).1
    have hk : kappa0 (tvDist P Q) c₁ c₂ ε₀ ≤ (1 - tvDist P Q) * c₁ * (ε₀ / 2) ^ (5 / 4 : ℝ) / (2 * tvDist P Q) :=
      min_le_right _ _
    rw [le_div_iff₀ (by linarith)] at hk
    have h1 : (1 - tvDist P Q) * c₁ * (ε₀ / 2) ^ (5 / 4 : ℝ) ≤ Wave31ti.uPath φ P Q (tvDist P Q - ε) := by
      calc (1 - tvDist P Q) * c₁ * (ε₀ / 2) ^ (5 / 4 : ℝ) = (1 - tvDist P Q) * (c₁ * (ε₀ / 2) ^ (5 / 4 : ℝ)) := by ring
        _ ≤ (1 - tvDist P Q) * Dpop φ P Q (tvDist P Q - ε₀ / 2) := mul_le_mul_of_nonneg_left hT (by linarith)
        _ ≤ _ := hl.trans hm
    exact two_kappa_le hk hk0 hεtv h1

/-- Y12 `lap_compare`. -/
theorem lap_compare_route : Claims.lap_compare := by
  intro H _ _ _ _ σ φ P Q _ _ c₁ c₂ ε₀ ε a b t u n m x y w v hσ hφ htv1 hTS hε hεtv ha hb hab ht hu hn hm hxy hQP
  intro α φs gh φh Δ V Dh Th yy e κ
  obtain ⟨hsm, hnorm, -⟩ := laplace_feature_facts hσ hφ
  have hκφ : ∀ z, ‖φ z‖ ≤ 1 := fun z => (hnorm z).le
  have hα0 : 0 < α := by show 0 < tvDist P Q - ε; linarith
  have hα1 : α < 1 := by show tvDist P Q - ε < 1; linarith
  have hαdef : α = tvDist P Q - ε := rfl
  have hPe := isProbabilityMeasure_empirical (by omega : n ≠ 0) x
  have hQe := isProbabilityMeasure_empirical (by omega : m ≠ 0) y
  -- the empirical side (Y10)
  obtain ⟨hDpos, hDeq, -, -, hgh, -, -, -, -, hramp, hoscw, -, hhalf, -, hlinh, -, -, -, -, -⟩ :=
    lap_clip_route H σ φ n m x y α w v hσ hφ hn hm hxy hα0 hα1 hQP
  have hgh' : 0 < gh := hgh
  have hhalf' : 1 / 2 ≤ ‖φh‖ := hhalf
  have hoscw' : Wave31to.oscFn (Wave31to.wit φ φh) = 1 := hoscw
  have hlinh' : linL (empirical x) (empirical y) (Wave31to.wit φ φh) - α = Dh * ‖φh‖ := hlinh
  have hramp' : ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α) =
      fun z => (fitF φ x y w v z - uHat φ x y w v α) / gh := hramp
  -- the population side (Y11)
  obtain ⟨hDpop, hgs, hoscs, hns, -, hlins, hids, -, -, -, hosc1, hosc2, -⟩ :=
    lap_pop_route H σ φ P Q ε a b t u hσ hφ hε hεtv htv1 ha hb hab ht hu
  have hoscs' : Wave31to.oscFn (Wave31to.wit φ φs) ≤ 1 := hoscs
  have hns' : ‖φs‖ = 1 / (t - u) := hns
  have hlins' : linL P Q (Wave31to.wit φ φs) - α = V / (t - u) := hlins.trans hids
  have hgs2 : t - u ≤ 2 := hosc1.trans hosc2
  -- the path (Y7, T40)
  obtain ⟨hnearF, hfarF⟩ := compare_path hsm hκφ htv1 hTS hε hεtv ha hb hab hDpop ht.1 hu.1
  obtain ⟨-, -, hk0, hk1, hcV, -, -, hcVe, -⟩ := lap_const_route H φ 1 P Q c₁ c₂ ε₀ hsm hκφ htv1 hTS
  have hk0' : 0 < κ := hk0
  have hk1' : κ < 1 := hk1
  have hV0 : 0 < V := lt_of_lt_of_le (mul_pos hcV (Real.rpow_pos_of_pos hε _)) (hcVe ε ⟨hε, hεtv.le⟩)
  -- notation
  have hDh : Dh = (1 - α) * qpVal φ x y w v := rfl
  have hDhpos : 0 < Dh := mul_pos (by linarith) hDpos
  have hNpos : 0 < ‖φh‖ := by linarith
  have hDN : 0 < Dh * ‖φh‖ := mul_pos hDhpos hNpos
  -- integrability of the functions of `ℋ`
  have hwi : ∀ (g : H) (μ : Measure ℝ), IsFiniteMeasure μ → Integrable (Wave31to.wit φ g) μ := fun g μ _ =>
    Integrable.of_bound ((continuous_const.inner continuous_id).comp_stronglyMeasurable hsm).measurable.aestronglyMeasurable
      ‖g‖ (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]; exact (abs_real_inner_le_norm g (φ z)).trans (by rw [hnorm, mul_one]))
  -- (i): `e = ε − T̂`
  have hwh : ∀ z, Wave31to.wit φ φh z = gh⁻¹ * fitF φ x y w v z := fun z => by
    show ⟪gh⁻¹ • witness φ x y w v, φ z⟫_ℝ = _
    rw [real_inner_smul_left]; rfl
  have hrampw : ∀ z, ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α) z =
      Wave31to.wit φ φh z - uHat φ x y w v α / gh := fun z => by
    rw [hramp', hwh]
    field_simp
  have he : e = linL P Q (Wave31to.wit φ φh) - α := by
    show (∫ z, ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α) z ∂P) -
      (∫ z, ramp (fitF φ x y w v) (tHat φ x y w v α) (uHat φ x y w v α) z ∂Q) - α = _
    simp_rw [hrampw]
    rw [linL_sub_const (hwi φh P inferInstance) (hwi φh Q inferInstance)]
  have heT : e = ε - Th := by
    rw [he]; show _ = ε - errL P Q (Wave31to.wit φ φh); unfold errL; rw [hαdef]; ring
  -- (i): `e + Δ̂ = D̄̂N̂`
  have hΔh : Δ φh = linL (empirical x) (empirical y) (Wave31to.wit φ φh) - linL P Q (Wave31to.wit φ φh) := rfl
  have hiden : e + Δ φh = Dh * ‖φh‖ := by
    rw [hΔh, he]; linarith [hlinh']
  -- (i): `D̄̂ ≥ y` (Lemma S4.20 for `P̃, Q̃` and `φ⋆`)
  have hφs0 : φs ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hns'; have : 0 < 1 / (t - u) := one_div_pos.mpr hgs; linarith
  have hrat := ratio_le_uPath (P := empirical x) (Q := empirical y) hsm (κ := 1) hκφ hα0.le hα1 hφs0 hoscs'
  have hUemp : Wave31ti.uPath φ (empirical x) (empirical y) α = Dh := by
    show (1 - α) * Dpop φ (empirical x) (empirical y) α = (1 - α) * qpVal φ x y w v
    rw [hDeq]; rfl
  rw [hUemp, hns', div_div_eq_mul_div, div_one] at hrat
  have hVid : V = (t - u) * (linL P Q (Wave31to.wit φ φs) - α) := by
    rw [hlins']; field_simp
  have hyy : yy = (t - u) * (linL (empirical x) (empirical y) (Wave31to.wit φ φs) - α) := by
    show V + (t - u) * Δ φs = _
    rw [hVid]; show (t - u) * (linL P Q (Wave31to.wit φ φs) - α) +
      (t - u) * (linL (empirical x) (empirical y) (Wave31to.wit φ φs) - linL P Q (Wave31to.wit φ φs)) = _
    ring
  have hyD : yy ≤ Dh := by rw [hyy, mul_comm]; exact hrat
  have hNy : ‖φh‖ * yy + Th ≤ ε + Δ φh := by
    have : ‖φh‖ * yy ≤ ‖φh‖ * Dh := mul_le_mul_of_nonneg_left hyD hNpos.le
    have h2 : ‖φh‖ * Dh = Dh * ‖φh‖ := mul_comm _ _
    linarith [heT, hiden]
  have hyy' : yy = V + (t - u) * Δ φs := rfl
  rw [hyy'] at hyD
  refine ⟨⟨heT, hiden, hyy' ▸ hyD, hNy⟩, ?_, ?_⟩
  · rcases lt_or_ge ε (ε₀ / 2) with hnear | hfar
    · obtain ⟨hW, hκW, hsupp⟩ := hnearF hnear
      have hε₀α : ε₀ ≤ tvDist P Q := hTS.2.2.2.1
      -- Lemma S4.20 at `α⋆ − 2ε` for `φ̂`
      have hrat2 : 0 < e + ε → e + ε ≤ Wave31ti.uPath φ P Q (tvDist P Q - 2 * ε) * ‖φh‖ := by
        intro _
        have hφh0 : φh ≠ 0 := by intro h0; rw [h0, norm_zero] at hNpos; exact lt_irrefl _ hNpos
        have h := ratio_le_uPath (P := P) (Q := Q) (α := tvDist P Q - 2 * ε) hsm hκφ (by linarith) (by linarith)
          hφh0 hoscw'.le
        rw [div_le_iff₀ hNpos] at h
        have : linL P Q (Wave31to.wit φ φh) - (tvDist P Q - 2 * ε) = e + ε := by rw [he, hαdef]; ring
        linarith
      exact compare_ii_near hε hk1' hV0 hW hκW hsupp hgs hiden hDN hyD hNpos.le hrat2
    · exact fun _ => compare_ii_far (hfarF hfar) hgs.le hgs2 hiden hDN hyD hhalf'
  · intro hΔ
    have hcVε : cV (tvDist P Q) c₁ ε₀ * ε ^ (5 / 4 : ℝ) ≤ V := hcVe ε ⟨hε, hεtv.le⟩
    refine ⟨?_, by linarith⟩
    rcases lt_or_ge ε (ε₀ / 2) with hnear | hfar
    · obtain ⟨-, hκW, hsupp⟩ := hnearF hnear
      exact compare_iii_near hε hk0'.le hV0.le hκW hsupp hgs.le hΔ
    · exact compare_iii_far (hfarF hfar) hgs.le hgs2 hΔ

end StatFormal.Wave31tu.RouteP
