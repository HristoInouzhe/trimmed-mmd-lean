import StatFormal.Wave30tp.RouteMoments
import StatFormal.Archive.Wave8a.RouteGeorep
import StatFormal.Archive.WaveP1a.RouteConsistency

/-!
# Route: NOTE Lemma P0 (one good empirical pair), the remark at `α = 0`, and Lemma 1

Untrusted proof material.

* `exists_weights`: explicit capped-simplex weights — `w = w⁰/S` when `S ≥ 1`; `w = w⁰ + θ(β/n − w⁰)`,
  `θ = (1 − S)/(β − S)`, when `S < 1` — with `Σ wᵢ pᵢ − μ = λ A + r`, `λ ∈ [0,1]`, `‖r‖ ≤ ρ (1 − S)₊`.
* `norm_smul_sub_smul_le_max`: `‖λA − λ'B‖ ≤ max{‖A − B‖, ‖A‖, ‖B‖}` on `[0,1]²`.
* Feasibility of the weights in the empirical region is the certified `prop:georep` (`Wave8a.georep_empirical`, ties
  allowed); the bound on `D̂` is `setDist ≤ ‖a − b‖`.
* Lemma 1: nested regions (`WaveP1a.region_mono`, `setDist_anti`), `toMeasurable` of the rejection set.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped InnerProductSpace

namespace StatFormal.Wave30tp

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.BangBang

section Weights

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_smul_sub_smul_le_max (A B : H) {l l' : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hl'0 : 0 ≤ l')
    (hl'1 : l' ≤ 1) : ‖l • A - l' • B‖ ≤ max (max ‖A - B‖ ‖A‖) ‖B‖ := by
  set M := max (max ‖A - B‖ ‖A‖) ‖B‖
  have h1 : ‖A - B‖ ≤ M := le_max_of_le_left (le_max_left _ _)
  have h2 : ‖A‖ ≤ M := le_max_of_le_left (le_max_right _ _)
  have h3 : ‖B‖ ≤ M := le_max_right _ _
  have h0 : 0 ≤ M := (norm_nonneg _).trans h3
  rcases le_total l' l with h | h
  · have e : l • A - l' • B = l' • (A - B) + (l - l') • A := by rw [smul_sub, sub_smul]; abel
    rw [e]
    calc ‖l' • (A - B) + (l - l') • A‖ ≤ ‖l' • (A - B)‖ + ‖(l - l') • A‖ := norm_add_le _ _
      _ = l' * ‖A - B‖ + (l - l') * ‖A‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl'0,
            abs_of_nonneg (by linarith)]
      _ ≤ l' * M + (l - l') * M :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hl'0) (mul_le_mul_of_nonneg_left h2 (by linarith))
      _ = l * M := by ring
      _ ≤ M := by nlinarith
  · have e : l • A - l' • B = l • (A - B) - (l' - l) • B := by rw [smul_sub, sub_smul]; abel
    rw [e]
    calc ‖l • (A - B) - (l' - l) • B‖ ≤ ‖l • (A - B)‖ + ‖(l' - l) • B‖ := norm_sub_le _ _
      _ = l * ‖A - B‖ + (l' - l) * ‖B‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl0,
            abs_of_nonneg (by linarith)]
      _ ≤ l * M + (l' - l) * M :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hl0) (mul_le_mul_of_nonneg_left h3 (by linarith))
      _ = l' * M := by ring
      _ ≤ M := by nlinarith

theorem sum_smul_sub_eq {n : ℕ} (w : Fin n → ℝ) (hw : ∑ i, w i = 1) (p : Fin n → H) (μ : H) :
    ∑ i, w i • p i - μ = ∑ i, w i • (p i - μ) := by
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hw, one_smul]

/-- One side of Lemma P0: explicit capped-simplex weights. -/
theorem exists_weights {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (p : Fin n → H) (μ : H)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1 / (1 - α)) {ρ : ℝ} (hρ : ∀ i, ‖p i - μ‖ ≤ ρ) :
    ∃ w ∈ capped n α, ∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ ∃ r : H,
      ∑ i, w i • p i - μ = l • ((n : ℝ)⁻¹ • ∑ i, a i • (p i - μ)) + r ∧
      ‖r‖ ≤ ρ * max (1 - (n : ℝ)⁻¹ * ∑ i, a i) 0 := by
  set β := 1 / (1 - α) with hβ
  have hβ1 : 1 ≤ β := one_le_beta hα0 hα1
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hcap : cap n α = β / n := by
    rw [cap, hβ]; field_simp
  set S := (n : ℝ)⁻¹ * ∑ i, a i with hS
  have hsumS : ∑ i, a i = n * S := by rw [hS]; field_simp
  set A := (n : ℝ)⁻¹ • ∑ i, a i • (p i - μ) with hA
  rcases le_or_gt 1 S with hS1 | hS1
  · -- scale down
    have hS0 : 0 < S := by linarith
    refine ⟨fun i => a i / (n * S), ⟨fun i => ⟨div_nonneg (ha i).1 (by positivity), ?_⟩, ?_⟩,
      S⁻¹, by positivity, inv_le_one_of_one_le₀ hS1, 0, ?_, ?_⟩
    · rw [hcap, div_le_div_iff₀ (by positivity) hnpos]
      nlinarith [mul_le_mul_of_nonneg_left hS1 (show (0 : ℝ) ≤ β * n by positivity),
        mul_le_mul_of_nonneg_right (ha i).2 hnpos.le]
    · rw [← Finset.sum_div, hsumS]; field_simp
    · rw [add_zero, sum_smul_sub_eq _ (by rw [← Finset.sum_div, hsumS]; field_simp), hA, smul_smul,
        Finset.smul_sum]
      congr 1; ext i
      rw [smul_smul]; congr 1; field_simp
    · rw [norm_zero, max_eq_right (by linarith), mul_zero]
  · -- top up under the caps
    have hgap : 0 < β - S := by linarith
    set θ := (1 - S) / (β - S) with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hgap.le
    have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hgap]; linarith
    set u : Fin n → ℝ := fun i => θ * (β / n - a i / n) with hu
    have hu0 : ∀ i, 0 ≤ u i := fun i => mul_nonneg hθ0 (by
      rw [sub_nonneg]; exact div_le_div_of_nonneg_right (ha i).2 hnpos.le)
    have hsub : ∑ i, (β / n - a i / n) = β - S := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.sum_div, hsumS]
      field_simp
    have hsumu : ∑ i, u i = 1 - S := by
      simp only [hu]
      rw [← Finset.mul_sum, hsub, hθ]
      field_simp
    have hsumw : ∑ i, (a i / n + u i) = 1 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, hsumS, hsumu]; field_simp; ring
    refine ⟨fun i => a i / n + u i, ⟨fun i => ⟨?_, ?_⟩, hsumw⟩, 1, zero_le_one, le_rfl,
      ∑ i, u i • (p i - μ), ?_, ?_⟩
    · exact add_nonneg (div_nonneg (ha i).1 hnpos.le) (hu0 i)
    · rw [hcap]
      simp only [hu]
      have h2 := (ha i).2
      have h0 := (ha i).1
      have : a i / n + θ * (β / n - a i / n) = ((1 - θ) * a i + θ * β) / n := by field_simp; ring
      rw [this, div_le_div_iff_of_pos_right hnpos]
      nlinarith
    · rw [sum_smul_sub_eq _ hsumw, one_smul, hA]
      simp_rw [add_smul]
      rw [Finset.sum_add_distrib, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, div_eq_inv_mul]
    · rw [max_eq_left (by linarith)]
      calc ‖∑ i, u i • (p i - μ)‖ ≤ ∑ i, ‖u i • (p i - μ)‖ := norm_sum_le _ _
        _ = ∑ i, u i * ‖p i - μ‖ := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hu0 i)]
        _ ≤ ∑ i, u i * ρ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hρ i) (hu0 i)
        _ = ρ * (1 - S) := by rw [← Finset.sum_mul, hsumu, mul_comm]

end Weights

/-! ### Lemma P0 -/

theorem polytope_mem_region {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {n : ℕ}
    (hn : 1 ≤ n) (x : Fin n → 𝒳) {w : Fin n → ℝ} (hw : w ∈ capped n α) :
    ∑ i, w i • φ (x i) ∈ region φ α (empirical x) := by
  rw [StatFormal.Wave8a.georep_empirical 𝒳 H φ α n x hφ hα0 hα1 (by omega)]
  exact ⟨w, hw, rfl⟩

theorem plugin_det : Claims.plugin_det := by
  intro 𝒳 H _ _ _ _ φ κ α P Q R _ _ _ a b n m hφ hκ hα0 hα1 hn hm ha hb x y
  set μR := ∫ z, φ z ∂R
  set ρ := rhoR φ R
  have hρ : ∀ z, ‖φ z - μR‖ ≤ ρ := fun z => le_rhoR (R := R) hκ z
  obtain ⟨w, hw, l, hl0, hl1, r, hwr, hr⟩ := exists_weights hn hα0 hα1 (fun i => φ (x i)) μR
    (fun i => a (x i)) (fun i => ha.2.1 (x i)) (fun i => hρ (x i))
  obtain ⟨v, hv, l', hl'0, hl'1, r', hvr, hr'⟩ := exists_weights hm hα0 hα1 (fun j => φ (y j)) μR
    (fun j => b (y j)) (fun j => hb.2.1 (y j)) (fun j => hρ (y j))
  have hX := polytope_mem_region hφ hα0 hα1 hn x hw
  have hY := polytope_mem_region hφ hα0 hα1 hm y hv
  refine (setDist_le_norm hX hY).trans ?_
  set A := wMeanDev a φ μR x
  set B := wMeanDev b φ μR y
  have hwr' : ∑ i, w i • φ (x i) - μR = l • A + r := hwr
  have hvr' : ∑ j, v j • φ (y j) - μR = l' • B + r' := hvr
  have e : ∑ i, w i • φ (x i) - ∑ j, v j • φ (y j) = (l • A - l' • B) + (r - r') := by
    have h1 : ∑ i, w i • φ (x i) = μR + (l • A + r) := by rw [← hwr']; abel
    have h2 : ∑ j, v j • φ (y j) = μR + (l' • B + r') := by rw [← hvr']; abel
    rw [h1, h2]; abel
  rw [e]
  have hvert := norm_smul_sub_smul_le_max A B hl0 hl1 hl'0 hl'1
  calc ‖(l • A - l' • B) + (r - r')‖ ≤ ‖l • A - l' • B‖ + (‖r‖ + ‖r'‖) := by
        have := norm_add_le (l • A - l' • B) (r - r'); have := norm_sub_le r r'; linarith
    _ ≤ max (max ‖A - B‖ ‖A‖) ‖B‖ + (ρ * max (1 - wMass a x) 0 + ρ * max (1 - wMass b y) 0) :=
        add_le_add hvert (add_le_add hr hr')
    _ = _ := by ring

/-! ### The remark after Lemma P0 (`α = 0`) -/

theorem ae_density_eq_one {𝒳 : Type*} [MeasurableSpace 𝒳] {R P : Measure 𝒳} [IsProbabilityMeasure P]
    [IsProbabilityMeasure R] {a : 𝒳 → ℝ} (ha : IsDensityLe R P 0 a) : (∀ᵐ x ∂P, a x = 1) ∧ P = R := by
  have h1 := integral_density_eq_one ha
  obtain ⟨ham, hab, hR⟩ := ha
  have hb1 : ∀ x, a x ≤ 1 := fun x => by simpa using (hab x).2
  have hai : Integrable a P := Integrable.of_bound ham.aestronglyMeasurable 1
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hab x).1]; exact hb1 x)
  have h0 : ∫ x, (1 - a x) ∂P = 0 := by
    rw [integral_sub (integrable_const _) hai, h1]; simp
  have hae : ∀ᵐ x ∂P, a x = 1 := by
    have := (integral_eq_zero_iff_of_nonneg (f := fun x => 1 - a x)
      (fun x => by show (0 : ℝ) ≤ 1 - a x; linarith [hb1 x]) ((integrable_const 1).sub hai)).1 h0
    filter_upwards [this] with x hx
    simp only [Pi.zero_apply] at hx
    linarith
  refine ⟨hae, ?_⟩
  rw [hR]
  have : (fun x => ENNReal.ofReal (a x)) =ᵐ[P] fun _ => 1 := by
    filter_upwards [hae] with x hx; simp [hx]
  rw [withDensity_congr_ae this]
  exact (withDensity_one).symm

theorem ae_sample_eq_one {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (n m : ℕ) {a : 𝒳 → ℝ} (hae : ∀ᵐ x ∂P, a x = 1) :
    ∀ᵐ z ∂(sampleLaw P Q n m), ∀ i, a (z.1 i) = 1 := by
  rw [ae_all_iff]
  intro i
  have hmp : MeasurePreserving (fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => z.1 i) (sampleLaw P Q n m) P :=
    (measurePreserving_eval (fun _ : Fin n => P) i).comp (measurePreserving_fst)
  exact hmp.quasiMeasurePreserving.ae hae

theorem ae_sample_eq_one_snd {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (n m : ℕ) {b : 𝒳 → ℝ} (hae : ∀ᵐ y ∂Q, b y = 1) :
    ∀ᵐ z ∂(sampleLaw P Q n m), ∀ j, b (z.2 j) = 1 := by
  rw [ae_all_iff]
  intro j
  have hmp : MeasurePreserving (fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => z.2 j) (sampleLaw P Q n m) Q :=
    (measurePreserving_eval (fun _ : Fin m => Q) j).comp (measurePreserving_snd)
  exact hmp.quasiMeasurePreserving.ae hae

theorem plugin_det_zero : Claims.plugin_det_zero := by
  intro 𝒳 H _ _ _ _ φ κ P Q R _ _ _ a b n m hφ hκ hn hm ha hb
  obtain ⟨haP, hPR⟩ := ae_density_eq_one ha
  obtain ⟨hbQ, hQR⟩ := ae_density_eq_one hb
  refine ⟨haP, hbQ, hPR, hQR, ?_⟩
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  filter_upwards [ae_sample_eq_one P Q n m haP, ae_sample_eq_one_snd P Q n m hbQ] with z hz1 hz2
  · have hS1 : wMass a z.1 = 1 := by
      simp only [wMass, hz1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      field_simp
    have hS2 : wMass b z.2 = 1 := by
      simp only [wMass]
      rw [Finset.sum_congr rfl fun j _ => hz2 j]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      field_simp
    refine ⟨hS1, hS2, ?_⟩
    set μR := ∫ w, φ w ∂R
    -- uniform weights are feasible at `α = 0`
    have hwx : (fun _ : Fin n => (n : ℝ)⁻¹) ∈ capped n 0 := by
      refine ⟨fun i => ⟨by positivity, by simp [cap]⟩, ?_⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hwy : (fun _ : Fin m => (m : ℝ)⁻¹) ∈ capped m 0 := by
      refine ⟨fun i => ⟨by positivity, by simp [cap]⟩, ?_⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hX := polytope_mem_region hφ le_rfl zero_lt_one hn z.1 hwx
    have hY := polytope_mem_region hφ le_rfl zero_lt_one hm z.2 hwy
    refine (setDist_le_norm hX hY).trans (le_of_eq ?_)
    congr 1
    have hsn : ∑ _i : Fin n, (n : ℝ)⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
    have hsm : ∑ _j : Fin m, (m : ℝ)⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
    have hA : wMeanDev a φ μR z.1 = ∑ i, (n : ℝ)⁻¹ • φ (z.1 i) - μR := by
      rw [sum_smul_sub_eq _ hsn, wMeanDev, Finset.smul_sum]
      simp only [hz1, one_smul]
    have hB : wMeanDev b φ μR z.2 = ∑ j, (m : ℝ)⁻¹ • φ (z.2 j) - μR := by
      rw [sum_smul_sub_eq _ hsm, wMeanDev, Finset.smul_sum]
      simp only [hz2, one_smul]
    rw [hA, hB]; abel

end StatFormal.Wave30tp
