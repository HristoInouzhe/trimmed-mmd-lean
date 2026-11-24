import StatFormal.Archive.OTFD.Wave16b.Statements
import StatFormal.Archive.OTFD.Wave8b.RouteBregman
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Route: A `prop:rate-decomp`, `prop:emp-bijective`, `prop:app-entropic` (untrusted)

* Minkowski for `rmsE` (`rmsE_le_add`): `n⁻¹Σ_i` is the integral against `ν = Σ_i P.map (ω ↦ (ω, i))` on `Ω × Fin n`,
  where `ENNReal.lintegral_Lp_add_le` applies.
* `rate_decomp`: `ι` is an isometry, so `‖ιF̂ − 𝔽‖ ≤ ‖F̂ − F_m‖ + ‖F_m − F_K‖ + ‖ιF_K − 𝔽‖`. Local form: the sieve error
  is `≤ D` on `𝒦₀` and `≤ 2M` off it, so its mean square is `≤ D² + 4M²P(H∖𝒦₀)`.
* Two-sided cores: `σ̂` (resp. the entropic plan) minimises the Bregman cost up to `0` (resp. `ε log min(n,m)/2`) among
  plans (certified `bregman_assign`, `bregman_plan`, Birkhoff `perm_le_plan`, `entropic_gap`); the upper Bregman bound
  gives `κ Σ P_ij ‖u_j − r_i‖²` for every plan `P`, hence `κW₂²(ν̂_n, μ_{K,m})`; then the `W₂` triangle inequality and
  `(a + b)² ≤ 2a² + 2b²`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave16b

open StatFormal.OTFD.Wave8b (bregD IsOptAssign IsEntPlan entBary unifW polytope_nonneg perm_le_plan
  ofReal_le_of_forall_plan bary_jensen entropic_gap measurable_edist_E)
open StatFormal.OTFD.Wave6b (empMeasure)
open TauCeti (wassersteinEDist)

/-! ### Minkowski for `rmsE` -/

section Minkowski
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}

/-- `ν = Σ_i P.map (ω ↦ (ω, i))`. -/
def nuP : Measure (Ω × Fin n) := Measure.sum fun i : Fin n => P.map fun ω => (ω, i)

lemma lintegral_nuP {F : Ω × Fin n → ℝ≥0∞} (hF : ∀ i, Measurable fun ω => F (ω, i)) :
    ∫⁻ z, F z ∂(nuP P) = ∑ i, ∫⁻ ω, F (ω, i) ∂P := by
  have hFm : Measurable F := measurable_from_prod_countable_left hF
  rw [nuP, lintegral_sum_measure, tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_map (g := fun ω : Ω => (ω, i)) hFm (by fun_prop)]

lemma ofReal_mean_sq {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) :
    ENNReal.ofReal ((1 / n : ℝ) * ∑ i, a i ^ 2) =
      ENNReal.ofReal (1 / n) * ∑ i, ENNReal.ofReal (a i) ^ (2 : ℝ) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.rpow_two, ENNReal.ofReal_pow (ha i)]

lemma rmsE_eq {g : Ω → Fin n → ℝ} (h0 : ∀ ω i, 0 ≤ g ω i) (hm : ∀ i, Measurable fun ω => g ω i) :
    rmsE P g = (ENNReal.ofReal (1 / n) *
      ∫⁻ z, ENNReal.ofReal (g z.1 z.2) ^ (2 : ℝ) ∂(nuP P)) ^ (1 / 2 : ℝ) := by
  have hmi : ∀ i, Measurable fun ω => ENNReal.ofReal (g ω i) ^ (2 : ℝ) :=
    fun i => ((hm i).ennreal_ofReal).pow_const _
  unfold rmsE
  congr 1
  rw [lintegral_nuP P (F := fun z => ENNReal.ofReal (g z.1 z.2) ^ (2 : ℝ)) hmi]
  simp_rw [ofReal_mean_sq (h0 _)]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hmi i),
    lintegral_finsetSum _ fun i _ => hmi i]

lemma rmsE_mono {g g' : Ω → Fin n → ℝ} (h0 : ∀ ω i, 0 ≤ g ω i) (hle : ∀ ω i, g ω i ≤ g' ω i) :
    rmsE P g ≤ rmsE P g' := by
  unfold rmsE
  refine ENNReal.rpow_le_rpow (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_) (by norm_num)
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => ?_) (by positivity)
  exact pow_le_pow_left₀ (h0 ω i) (hle ω i) 2

/-- Minkowski for `rmsE`. -/
lemma rmsE_le_add {g g₁ g₂ : Ω → Fin n → ℝ} (h0 : ∀ ω i, 0 ≤ g ω i) (h1 : ∀ ω i, 0 ≤ g₁ ω i)
    (h2 : ∀ ω i, 0 ≤ g₂ ω i) (hle : ∀ ω i, g ω i ≤ g₁ ω i + g₂ ω i)
    (hm1 : ∀ i, Measurable fun ω => g₁ ω i) (hm2 : ∀ i, Measurable fun ω => g₂ ω i) :
    rmsE P g ≤ rmsE P g₁ + rmsE P g₂ := by
  have hs0 : ∀ ω i, 0 ≤ g₁ ω i + g₂ ω i := fun ω i => add_nonneg (h1 ω i) (h2 ω i)
  refine (rmsE_mono P h0 hle).trans ?_
  rw [rmsE_eq P hs0 (fun i => (hm1 i).add (hm2 i)), rmsE_eq P h1 hm1, rmsE_eq P h2 hm2]
  have hF1 : Measurable fun z : Ω × Fin n => ENNReal.ofReal (g₁ z.1 z.2) :=
    measurable_from_prod_countable_left fun i => (hm1 i).ennreal_ofReal
  have hF2 : Measurable fun z : Ω × Fin n => ENNReal.ofReal (g₂ z.1 z.2) :=
    measurable_from_prod_countable_left fun i => (hm2 i).ennreal_ofReal
  have e : (fun z : Ω × Fin n => ENNReal.ofReal (g₁ z.1 z.2 + g₂ z.1 z.2) ^ (2 : ℝ)) =
      fun z : Ω × Fin n => ((fun z : Ω × Fin n => ENNReal.ofReal (g₁ z.1 z.2)) +
        fun z : Ω × Fin n => ENNReal.ofReal (g₂ z.1 z.2)) z ^ (2 : ℝ) := by
    funext z
    simp only [Pi.add_apply]
    rw [ENNReal.ofReal_add (h1 _ _) (h2 _ _)]
  rw [e]
  have hM := ENNReal.lintegral_Lp_add_le (μ := nuP P) (p := 2) hF1.aemeasurable hF2.aemeasurable one_le_two
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← mul_add]
  gcongr

end Minkowski

/-! ### `prop:rate-decomp` -/

theorem rate_decomp : Claims.rate_decomp := by
  intro H _ _ K n Ω _ P ι Fhat Fm FK FP h1 h2 h3
  have hle : ∀ ω i, ‖ι (Fhat ω i) - FP ω i‖ ≤
      ‖Fhat ω i - Fm ω i‖ + (‖Fm ω i - FK ω i‖ + ‖ι (FK ω i) - FP ω i‖) := by
    intro ω i
    have e : ι (Fhat ω i) - FP ω i = ι (Fhat ω i - Fm ω i) + (ι (Fm ω i - FK ω i) + (ι (FK ω i) - FP ω i)) := by
      simp only [map_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (le_of_eq (LinearIsometry.norm_map _ _))
      ((norm_add_le _ _).trans (add_le_add (le_of_eq (LinearIsometry.norm_map _ _)) le_rfl)))
  have a := rmsE_le_add P (fun ω i => norm_nonneg _) (fun ω i => norm_nonneg _)
    (fun ω i => add_nonneg (norm_nonneg _) (norm_nonneg _)) hle h1 (fun i => (h2 i).add (h3 i))
  have b := rmsE_le_add P (g := fun ω i => ‖Fm ω i - FK ω i‖ + ‖ι (FK ω i) - FP ω i‖)
    (fun ω i => add_nonneg (norm_nonneg _) (norm_nonneg _)) (fun ω i => norm_nonneg _)
    (fun ω i => norm_nonneg _) (fun ω i => le_rfl) h2 h3
  calc _ ≤ _ := a
    _ ≤ _ := by gcongr
    _ = _ := (add_assoc _ _ _).symm

/-- The local sieve term: `rms ≤ D + 2M√P(H∖𝒦₀)`. -/
lemma rms_local {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Ω → Fin n → H) (PX : Measure H) (s : H → ℝ) (K₀ : Set H) {D M : ℝ}
    (hX : ∀ i, Measurable fun ω => X ω i) (hlaw : ∀ i, P.map (fun ω => X ω i) = PX) (hK : MeasurableSet K₀)
    (hs0 : ∀ x, 0 ≤ s x) (hD : 0 ≤ D) (hM0 : 0 ≤ 2 * M) (hsD : ∀ᵐ x ∂PX, x ∈ K₀ → s x ≤ D) (hM : ∀ x, s x ≤ 2 * M) :
    rmsE P (fun ω i => s (X ω i)) ≤ ENNReal.ofReal D + ENNReal.ofReal (2 * M) * PX K₀ᶜ ^ (1 / 2 : ℝ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    unfold rmsE
    simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- pointwise
  set I : Ω → Fin n → ℝ := fun ω i => (K₀ᶜ).indicator (fun _ => (1 : ℝ)) (X ω i) with hI
  have hae : ∀ᵐ ω ∂P, ∀ i, X ω i ∈ K₀ → s (X ω i) ≤ D := by
    rw [ae_all_iff]
    intro i
    rw [← hlaw i] at hsD
    exact ae_of_ae_map (hX i).aemeasurable hsD
  have hpt : ∀ ω, (∀ i, X ω i ∈ K₀ → s (X ω i) ≤ D) → ∀ i, s (X ω i) ^ 2 ≤ D ^ 2 + (2 * M) ^ 2 * I ω i := by
    intro ω hω i
    by_cases hx : X ω i ∈ K₀
    · have : I ω i = 0 := by simp [hI, hx]
      rw [this, mul_zero, add_zero]
      exact pow_le_pow_left₀ (hs0 _) (hω i hx) 2
    · have : I ω i = 1 := by simp [hI, hx]
      rw [this, mul_one]
      have := pow_le_pow_left₀ (hs0 _) (hM (X ω i)) 2
      nlinarith [sq_nonneg D]
  have hmean : ∀ ω, (∀ i, X ω i ∈ K₀ → s (X ω i) ≤ D) → (1 / n : ℝ) * ∑ i, s (X ω i) ^ 2 ≤
      D ^ 2 + (2 * M) ^ 2 * ((1 / n : ℝ) * ∑ i, I ω i) := by
    intro ω hω
    have h1 := sum_le_sum fun i (_ : i ∈ univ) => hpt ω hω i
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum] at h1
    have : (1 / n : ℝ) * (n * D ^ 2 + (2 * M) ^ 2 * ∑ i, I ω i) =
        D ^ 2 + (2 * M) ^ 2 * ((1 / n : ℝ) * ∑ i, I ω i) := by field_simp
    rw [← this]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hI0 : ∀ ω i, 0 ≤ I ω i := fun ω i => by
    simp only [hI]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hIm : ∀ i, Measurable fun ω => ENNReal.ofReal (I ω i) := fun i =>
    ((measurable_const.indicator hK.compl).comp (hX i)).ennreal_ofReal
  have hlint : ∫⁻ ω, ENNReal.ofReal ((1 / n : ℝ) * ∑ i, I ω i) ∂P = PX K₀ᶜ := by
    have e : ∀ ω, ENNReal.ofReal ((1 / n : ℝ) * ∑ i, I ω i) =
        ENNReal.ofReal (1 / n) * ∑ i, ENNReal.ofReal (I ω i) := fun ω => by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg fun i _ => hI0 ω i]
    simp_rw [e]
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hIm i),
      lintegral_finsetSum _ fun i _ => hIm i]
    have hi : ∀ i, ∫⁻ ω, ENNReal.ofReal (I ω i) ∂P = PX K₀ᶜ := by
      intro i
      have e2 : (fun ω => ENNReal.ofReal (I ω i)) = fun ω => (K₀ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) (X ω i) := by
        funext ω
        simp only [hI]
        by_cases hx : X ω i ∈ K₀ᶜ <;> simp [Set.indicator, hx]
      rw [e2, ← lintegral_map (measurable_const.indicator hK.compl) (hX i), hlaw i,
        lintegral_indicator_const hK.compl, one_mul]
    simp_rw [hi]
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    rw [show (1 / n : ℝ) * n = 1 by field_simp, ENNReal.ofReal_one, one_mul]
  unfold rmsE
  calc (∫⁻ ω, ENNReal.ofReal ((1 / n : ℝ) * ∑ i, s (X ω i) ^ 2) ∂P) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ ω, (ENNReal.ofReal (D ^ 2) + ENNReal.ofReal ((2 * M) ^ 2) *
          ENNReal.ofReal ((1 / n : ℝ) * ∑ i, I ω i)) ∂P) ^ (1 / 2 : ℝ) := by
        refine ENNReal.rpow_le_rpow (lintegral_mono_ae (hae.mono fun ω hω => ?_)) (by norm_num)
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (mul_nonneg (by positivity) (mul_nonneg (by positivity) (sum_nonneg fun i _ => hI0 ω i)))]
        exact ENNReal.ofReal_le_ofReal (hmean ω hω)
    _ = (ENNReal.ofReal (D ^ 2) + ENNReal.ofReal ((2 * M) ^ 2) * PX K₀ᶜ) ^ (1 / 2 : ℝ) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hlint]
    _ ≤ ENNReal.ofReal (D ^ 2) ^ (1 / 2 : ℝ) + (ENNReal.ofReal ((2 * M) ^ 2) * PX K₀ᶜ) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)
    _ = ENNReal.ofReal D + ENNReal.ofReal (2 * M) * PX K₀ᶜ ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
          ← Real.sqrt_eq_rpow, Real.sqrt_sq hD, Real.sqrt_sq hM0]

theorem rate_decomp_local : Claims.rate_decomp_local := by
  intro H _ _ _ K n Ω _ P _ ι X PX Pi FK FP Fhat Fm K₀ D M hX hlaw hK h1 h2 h3 hD hsD hM1 hM2
  have hle : ∀ ω i, ‖ι (Fhat ω i) - FP (X ω i)‖ ≤
      ‖Fhat ω i - Fm ω i‖ + (‖Fm ω i - FK (Pi (X ω i))‖ + ‖ι (FK (Pi (X ω i))) - FP (X ω i)‖) := by
    intro ω i
    have e : ι (Fhat ω i) - FP (X ω i) = ι (Fhat ω i - Fm ω i) +
        (ι (Fm ω i - FK (Pi (X ω i))) + (ι (FK (Pi (X ω i))) - FP (X ω i))) := by
      simp only [map_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (le_of_eq (LinearIsometry.norm_map _ _))
      ((norm_add_le _ _).trans (add_le_add (le_of_eq (LinearIsometry.norm_map _ _)) le_rfl)))
  have h3' : ∀ i, Measurable fun ω => ‖ι (FK (Pi (X ω i))) - FP (X ω i)‖ := fun i => h3.comp (hX i)
  have a := rmsE_le_add P (fun ω i => norm_nonneg _) (fun ω i => norm_nonneg _)
    (fun ω i => add_nonneg (norm_nonneg _) (norm_nonneg _)) hle h1 (fun i => (h2 i).add (h3' i))
  have b := rmsE_le_add P (g := fun ω i => ‖Fm ω i - FK (Pi (X ω i))‖ + ‖ι (FK (Pi (X ω i))) - FP (X ω i)‖)
    (fun ω i => add_nonneg (norm_nonneg _) (norm_nonneg _)) (fun ω i => norm_nonneg _)
    (fun ω i => norm_nonneg _) (fun ω i => le_rfl) h2 h3'
  have hM0 : 0 ≤ 2 * M := by have := (norm_nonneg _).trans (hM2 0); linarith
  have c := rms_local P X PX (fun x => ‖ι (FK (Pi x)) - FP x‖) K₀ hX hlaw hK (fun x => norm_nonneg _) hD hM0 hsD
    (fun x => show ‖ι (FK (Pi x)) - FP x‖ ≤ 2 * M from
      (norm_sub_le _ _).trans (by have := hM1 x; have := hM2 x; linarith))
  exact a.trans ((add_le_add le_rfl (b.trans (add_le_add le_rfl c))).trans_eq (by ring))

/-! ### two-sided cores -/

section Cores
variable {K n m : ℕ}

/-- `Y ≤ κ Σ P_ij‖r_i − u_j‖² + c` for every plan gives `ofReal Y ≤ κ W₂²(ν̂, μ_{K,m}) + c`. -/
lemma ofReal_le_sq_of_forall_plan (hn : 1 ≤ n) (hm : 1 ≤ m) (r : Fin n → EuclideanSpace ℝ (Fin K))
    (u : Fin m → EuclideanSpace ℝ (Fin K)) {Y κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c)
    (h : ∀ P ∈ Matrix.transportPolytope (unifW n) (unifW m),
      Y ≤ κ * ∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2 + c) :
    ENNReal.ofReal Y ≤
      ENNReal.ofReal κ * wassersteinEDist 2 (empMeasure r) (empMeasure u) ^ 2 + ENNReal.ofReal c := by
  set Z := max (Y - c) 0 with hZ
  have hZ0 : 0 ≤ Z := le_max_right _ _
  have key := ofReal_le_of_forall_plan (Y := √Z) hn hm r u (Real.sqrt_nonneg κ) le_rfl (fun P hP => by
    have hX : 0 ≤ ∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2 :=
      sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (polytope_nonneg hP i j) (by positivity)
    have h1 : Z ≤ κ * ∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2 :=
      max_le (by linarith [h P hP]) (mul_nonneg hκ hX)
    rw [add_zero, ← Real.sqrt_mul hκ]
    exact Real.sqrt_le_sqrt h1)
  rw [ENNReal.ofReal_zero, add_zero] at key
  have hsq : ENNReal.ofReal Z ≤ ENNReal.ofReal κ * wassersteinEDist 2 (empMeasure r) (empMeasure u) ^ 2 := by
    have := pow_le_pow_left₀ bot_le key 2
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hZ0, mul_pow,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hκ] at this
    exact this
  calc ENNReal.ofReal Y ≤ ENNReal.ofReal (Z + c) := ENNReal.ofReal_le_ofReal (by
        have := le_max_left (Y - c) 0; linarith)
    _ = ENNReal.ofReal Z + ENNReal.ofReal c := ENNReal.ofReal_add hZ0 hc
    _ ≤ _ := by gcongr

/-- The upper Bregman bound against any plan. -/
lemma upper_plan {α L : ℝ} {f : EuclideanSpace ℝ (Fin K) → ℝ} {x r : Fin n → EuclideanSpace ℝ (Fin K)}
    {u : Fin m → EuclideanSpace ℝ (Fin K)} (h2 : TwoSidedAt α L f u x r) {P : Matrix (Fin n) (Fin m) ℝ}
    (hP : P ∈ Matrix.transportPolytope (unifW n) (unifW m)) :
    ∑ i, ∑ j, P i j * bregD f (x i) (r i) (u j) ≤ L / 2 * ∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2 := by
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  have := mul_le_mul_of_nonneg_left (h2 i j).2 (polytope_nonneg hP i j)
  rw [norm_sub_rev (u j) (r i)] at this
  linarith

/-- The lower Bregman bound under a plan. -/
lemma lower_plan {α L : ℝ} {f : EuclideanSpace ℝ (Fin K) → ℝ} {x r : Fin n → EuclideanSpace ℝ (Fin K)}
    {u : Fin m → EuclideanSpace ℝ (Fin K)} (h2 : TwoSidedAt α L f u x r) {P : Matrix (Fin n) (Fin m) ℝ}
    (hP : P ∈ Matrix.transportPolytope (unifW n) (unifW m)) :
    α / 2 * ∑ i, ∑ j, P i j * ‖u j - r i‖ ^ 2 ≤ ∑ i, ∑ j, P i j * bregD f (x i) (r i) (u j) := by
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  have := mul_le_mul_of_nonneg_left (h2 i j).1 (polytope_nonneg hP i j)
  linarith

end Cores

theorem bijective_two_sided_core : Claims.bijective_two_sided_core := by
  intro K n α L f x r u σ hn hα hαL h2 hopt
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hκ : 0 ≤ L / α := div_nonneg (hα.le.trans hαL) hα.le
  have := ofReal_le_sq_of_forall_plan (Y := (1 / n : ℝ) * ∑ i, ‖u (σ i) - r i‖ ^ 2) hn hn r u hκ le_rfl ?_
  · simpa using this
  intro P hP
  -- σ minimises the Bregman total cost over permutations, hence over plans
  have hbreg := (StatFormal.OTFD.Wave8b.bregman_assign K n f x r u σ).1 hopt
  have hpl := perm_le_plan hn (fun i j => bregD f (x i) (r i) (u j)) σ hbreg hP
  have hup := upper_plan h2 hP
  have hlow : α / 2 * ((1 / n : ℝ) * ∑ i, ‖u (σ i) - r i‖ ^ 2) ≤
      (1 / n : ℝ) * ∑ i, bregD f (x i) (r i) (u (σ i)) := by
    have e : α / 2 * ((1 / n : ℝ) * ∑ i, ‖u (σ i) - r i‖ ^ 2) =
        (1 / n : ℝ) * ∑ i, α / 2 * ‖u (σ i) - r i‖ ^ 2 := by rw [← mul_sum]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => (h2 i (σ i)).1) (by positivity)
  have hfin : α / 2 * ((1 / n : ℝ) * ∑ i, ‖u (σ i) - r i‖ ^ 2) ≤
      L / 2 * ∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2 := hlow.trans (hpl.trans hup)
  rw [add_zero]
  have hα2 : 0 < α / 2 := by linarith
  calc (1 / n : ℝ) * ∑ i, ‖u (σ i) - r i‖ ^ 2 ≤ (L / 2 * ∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2) / (α / 2) :=
        (le_div_iff₀' hα2).2 hfin
    _ = L / α * ∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2 := by field_simp

theorem entropic_two_sided_core : Claims.entropic_two_sided_core := by
  intro K n m α L ε f x r u π hn hm hα hαL hε h2 hπ
  have hκ : 0 ≤ L / α := div_nonneg (hα.le.trans hαL) hα.le
  have hlog : 0 ≤ Real.log (min n m) := by
    apply Real.log_nonneg
    rcases le_total n m with h | h
    · rw [min_eq_left (by exact_mod_cast h)]; exact_mod_cast hn
    · rw [min_eq_right (by exact_mod_cast h)]; exact_mod_cast hm
  refine ofReal_le_sq_of_forall_plan hn hm r u hκ (by positivity) fun P hP => ?_
  have hgap := entropic_gap hn hm hε hπ hP
  have hbp := StatFormal.OTFD.Wave8b.bregman_plan K n m f x r u (unifW n) (unifW m) π P hπ.1.2 hP.2
  have hlow := lower_plan h2 hπ.1
  have hup := upper_plan h2 hP
  have hjen := bary_jensen hn hπ.1 u r
  have hα2 : 0 < α / 2 := by linarith
  have hmain : α / 2 * ∑ i, ∑ j, π i j * ‖u j - r i‖ ^ 2 ≤
      L / 2 * ∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2 + ε * Real.log (min n m) / 2 := by linarith
  have h3 : ∑ i, ∑ j, π i j * ‖u j - r i‖ ^ 2 ≤
      L / α * ∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2 + ε / α * Real.log (min n m) := by
    have := (le_div_iff₀' hα2).2 hmain
    calc _ ≤ _ := this
      _ = _ := by field_simp
  exact hjen.trans h3

/-! ### expectations -/

lemma w2_sq_le {K n m : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (r : Fin n → EuclideanSpace ℝ (Fin K)) (u : Fin m → EuclideanSpace ℝ (Fin K)) :
    wassersteinEDist 2 (empMeasure r) (empMeasure u) ^ 2 ≤
      2 * (wassersteinEDist 2 (empMeasure r) μ ^ 2 + wassersteinEDist 2 (empMeasure u) μ ^ 2) := by
  have htri : wassersteinEDist 2 (empMeasure r) (empMeasure u) ≤
      wassersteinEDist 2 (empMeasure r) μ + wassersteinEDist 2 (empMeasure u) μ := by
    rw [TauCeti.wassersteinEDist_comm measurable_edist_E 2 (empMeasure u) μ]
    exact TauCeti.wassersteinEDist_triangle measurable_edist_E (by norm_num) _ μ _
  have hp := ENNReal.rpow_add_le_mul_rpow_add_rpow (wassersteinEDist 2 (empMeasure r) μ)
    (wassersteinEDist 2 (empMeasure u) μ) (p := 2) one_le_two
  norm_num at hp
  try simp only [ENNReal.rpow_two, ENNReal.rpow_one] at hp
  calc _ ≤ (wassersteinEDist 2 (empMeasure r) μ + wassersteinEDist 2 (empMeasure u) μ) ^ 2 := by gcongr
    _ ≤ _ := hp

lemma expect_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {K n m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (r : Ω → Fin n → EuclideanSpace ℝ (Fin K)) (u : Fin m → EuclideanSpace ℝ (Fin K)) (Y : Ω → ℝ) {κ c : ℝ}
    (hκ : 0 ≤ κ)
    (hcore : ∀ᵐ ω ∂P, ENNReal.ofReal (Y ω) ≤
      ENNReal.ofReal κ * wassersteinEDist 2 (empMeasure (r ω)) (empMeasure u) ^ 2 + ENNReal.ofReal c) :
    ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P ≤
      ENNReal.ofReal (2 * κ) * (∫⁻ ω, wassersteinEDist 2 (empMeasure (r ω)) μ ^ 2 ∂P +
        wassersteinEDist 2 (empMeasure u) μ ^ 2) + ENNReal.ofReal c := by
  set Wg := wassersteinEDist 2 (empMeasure u) μ
  calc ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * κ) * (wassersteinEDist 2 (empMeasure (r ω)) μ ^ 2 + Wg ^ 2) +
          ENNReal.ofReal c) ∂P := by
        refine lintegral_mono_ae (hcore.mono fun ω h => h.trans ?_)
        have hw := w2_sq_le μ (r ω) u
        calc ENNReal.ofReal κ * wassersteinEDist 2 (empMeasure (r ω)) (empMeasure u) ^ 2 + ENNReal.ofReal c
            ≤ ENNReal.ofReal κ * (2 * (wassersteinEDist 2 (empMeasure (r ω)) μ ^ 2 + Wg ^ 2)) +
                ENNReal.ofReal c := by gcongr
          _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]; ring
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ measurable_const,
          lintegral_const, measure_univ, mul_one]

theorem emp_bijective_sq : Claims.emp_bijective_sq := by
  intro K n Ω _ P _ μ _ x F u f α L σ hn hα hαL hae hopt
  have hκ : 0 ≤ L / α := div_nonneg (hα.le.trans hαL) hα.le
  have := expect_sq (c := 0) P μ (fun ω i => F (x i ω)) u
    (fun ω => (1 / n : ℝ) * ∑ i, ‖u (σ ω i) - F (x i ω)‖ ^ 2) hκ ?_
  · simpa using this
  filter_upwards [hae] with ω hω
  rw [ENNReal.ofReal_zero, add_zero]
  exact bijective_two_sided_core K n α L f (fun i => x i ω) (fun i => F (x i ω)) u (σ ω) hn hα hαL hω (hopt ω)

theorem app_entropic : Claims.app_entropic := by
  intro K n m Ω _ P _ μ _ x F u f α L ε π hn hm hα hαL hε hae hπ
  have hκ : 0 ≤ L / α := div_nonneg (hα.le.trans hαL) hα.le
  refine expect_sq P μ (fun ω i => F (x i ω)) u
    (fun ω => (1 / n : ℝ) * ∑ i, ‖entBary (π ω) u i - F (x i ω)‖ ^ 2) hκ ?_
  filter_upwards [hae] with ω hω
  exact entropic_two_sided_core K n m α L ε f (fun i => x i ω) (fun i => F (x i ω)) u (π ω) hn hm hα hαL hε
    hω (hπ ω)

theorem emp_bijective : Claims.emp_bijective := by
  intro K n Ω _ P _ μ _ x F Fg u f α L σ hn hα hαL hx hF hFg hu hae hopt
  have hm1 : ∀ i, Measurable fun ω => ‖u (σ ω i) - F (x i ω)‖ := fun i =>
    ((hu i).sub (hF.comp (hx i))).norm
  have hm2 : ∀ i, Measurable fun ω => ‖Fg (x i ω) - F (x i ω)‖ := fun i =>
    ((hFg.comp (hx i)).sub (hF.comp (hx i))).norm
  have hM := rmsE_le_add P (g := fun ω i => ‖u (σ ω i) - Fg (x i ω)‖) (fun ω i => norm_nonneg _)
    (fun ω i => norm_nonneg _) (fun ω i => norm_nonneg _)
    (fun ω i => by
      calc ‖u (σ ω i) - Fg (x i ω)‖ = ‖(u (σ ω i) - F (x i ω)) - (Fg (x i ω) - F (x i ω))‖ := by
            congr 1; abel
        _ ≤ _ := norm_sub_le _ _) hm1 hm2
  refine hM.trans (add_le_add ?_ le_rfl)
  unfold rmsE
  exact ENNReal.rpow_le_rpow (emp_bijective_sq K n Ω P μ x F u f α L σ hn hα hαL hae hopt) (by norm_num)

theorem app_entropic_hilbert : Claims.app_entropic_hilbert := by
  intro H _ _ K n m Ω _ P _ ι μ _ x F u f α L ε π FPX hn hm hα hαL hε hm1 hm2 hae hπ
  have hM := rmsE_le_add P (g := fun ω i => ‖ι (entBary (π ω) u i) - FPX ω i‖) (fun ω i => norm_nonneg _)
    (fun ω i => norm_nonneg _) (fun ω i => norm_nonneg _)
    (fun ω i => by
      have e : ι (entBary (π ω) u i) - FPX ω i = ι (entBary (π ω) u i - F (x i ω)) + (ι (F (x i ω)) - FPX ω i) := by
        simp only [map_sub]; abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [LinearIsometry.norm_map]) hm1 hm2
  refine hM.trans (add_le_add ?_ le_rfl)
  unfold rmsE
  exact ENNReal.rpow_le_rpow (app_entropic K n m Ω P μ x F u f α L ε π hn hm hα hαL hε hae hπ) (by norm_num)

end StatFormal.OTFD.Wave16b
