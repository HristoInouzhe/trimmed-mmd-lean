import StatFormal.Lib.Concentration.Symmetrization
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Basic

/-!
# Uniform concentration for the trimmed-MMD class `𝒢`

Library component (concentration, part 6). Untrusted library code.

Source: `trimmed-mmd/paper.tex` `thm:concentration` and the supplement's proof (Steps 2–3).
The class is `𝒢 = {x ↦ (⟨f, φ(x)⟩ − t)₊ : ‖f‖ ≤ 1, |t| ≤ κ}`, here
`gTM φ (f, t) x = max (⟪f, φ x⟫ − t) 0` with parameters in `tmParams H κ`.
`H` is a real inner-product space (`φ` strongly measurable, `‖φ x‖ ≤ κ`, `κ > 0`).

## Measurability device

Device (b): the class is uncountable, but for every sample `x` the map
`p ↦ (Pₙ − P) g_p` is continuous (indeed `2(κ+1)`-Lipschitz) on `H × ℝ`, so the supremum over
`tmParams H κ` equals the supremum over any countable `T₀ ⊆ tmParams H κ` dense in it
(`iSup_tmParams_eq`). Such a `T₀` exists when `H` is separable. All probabilistic statements
are first proved for an arbitrary countable `T₀` (device (a)) and then transferred.

## Main results

* `radAvg_tm_le`: at every sample, `E_σ sup_{𝒢} n⁻¹ ∑ σᵢ g(xᵢ) ≤ 2κ/√n`
  (contraction for `(·)₊`, Cauchy–Schwarz, `E_σ‖∑σᵢφ(xᵢ)‖ ≤ κ√n`, `E_σ|∑σᵢ| ≤ √n`);
* `integral_iSup_empDev_tm_le`, `integral_iSup_neg_empDev_tm_le`: `E sup_𝒢 ±(Pₙ − P)g ≤ 4κ/√n`;
* `tm_concentration_countable` and **`tm_concentration`** (separable `H`): for `n ≥ 1`,
  `0 < δ < 1`, with probability `≥ 1 − δ`,
  `sup_{g ∈ 𝒢} |(Pₙ − P) g| ≤ 4κ/√n + κ √(2 log(2/δ)/n)`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

namespace StatFormal.Concentration

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Parameter set `{(f, t) : ‖f‖ ≤ 1, |t| ≤ κ}`. -/
def tmParams (H : Type*) [NormedAddCommGroup H] (κ : ℝ) : Set (H × ℝ) :=
  {p | ‖p.1‖ ≤ 1 ∧ |p.2| ≤ κ}

/-- The trimmed-MMD class member `x ↦ (⟪f, φ x⟫ − t)₊`. -/
def gTM (φ : X → H) (p : H × ℝ) (x : X) : ℝ := max (inner ℝ p.1 (φ x) - p.2) 0

variable {φ : X → H} {κ : ℝ}

theorem abs_inner_sub_le (hκ : ∀ x, ‖φ x‖ ≤ κ) {p : H × ℝ} (hp : p ∈ tmParams H κ) (x : X) :
    |inner ℝ p.1 (φ x) - p.2| ≤ 2 * κ := by
  refine (abs_sub _ _).trans ?_
  have h1 : |inner ℝ p.1 (φ x)| ≤ κ :=
    (abs_real_inner_le_norm _ _).trans (by
      calc ‖p.1‖ * ‖φ x‖ ≤ 1 * κ := mul_le_mul hp.1 (hκ x) (norm_nonneg _) zero_le_one
        _ = κ := one_mul κ)
  linarith [hp.2]

theorem gTM_mem_Icc (hκ : ∀ x, ‖φ x‖ ≤ κ) {p : H × ℝ} (hp : p ∈ tmParams H κ) (x : X) :
    gTM φ p x ∈ Set.Icc 0 (2 * κ) := by
  have hκ0 : 0 ≤ κ := (abs_nonneg _).trans hp.2
  exact ⟨le_max_right _ _, max_le ((le_abs_self _).trans (abs_inner_sub_le hκ hp x))
    (by linarith)⟩

theorem abs_gTM_le (hκ : ∀ x, ‖φ x‖ ≤ κ) {p : H × ℝ} (hp : p ∈ tmParams H κ) (x : X) :
    |gTM φ p x| ≤ 2 * κ := by
  have h := gTM_mem_Icc hκ hp x
  rw [abs_of_nonneg h.1]; exact h.2

theorem measurable_gTM (hφ : StronglyMeasurable φ) (p : H × ℝ) : Measurable (gTM φ p) :=
  (((stronglyMeasurable_const (b := p.1)).inner hφ).measurable.sub_const _).max measurable_const

/-! ### Rademacher average of `𝒢` -/

theorem radAvg_tm_le (T₀ : Set (H × ℝ)) [Nonempty T₀] (hT₀ : T₀ ⊆ tmParams H κ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) {n : ℕ} (hn : n ≠ 0) (x : Fin n → X) :
    radAvg (fun q : T₀ => gTM φ q.1) n x ≤ 2 * κ / √n := by
  obtain ⟨q₀⟩ := ‹Nonempty T₀›
  have hκ0 : 0 ≤ κ := (abs_nonneg _).trans (hT₀ q₀.2).2
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  set a : T₀ → Fin n → ℝ := fun q i => inner ℝ q.1.1 (φ (x i)) - q.1.2 with ha_def
  have ha : ∀ q i, |a q i| ≤ 2 * κ := fun q i => abs_inner_sub_le hκ (hT₀ q.2) _
  have h1 : (fun σ : Fin n → Bool => ⨆ q : T₀, (n : ℝ)⁻¹ * ∑ i, rsign (σ i) * gTM φ q.1 (x i)) =
      fun σ => (n : ℝ)⁻¹ * ⨆ q : T₀, ∑ i, rsign (σ i) * max (a q i) 0 := by
    funext σ
    rw [Real.mul_iSup_of_nonneg (by positivity)]
    rfl
  unfold radAvg
  rw [h1, radE_const_mul]
  have hpt : ∀ σ : Fin n → Bool, (⨆ q : T₀, ∑ i, rsign (σ i) * a q i) ≤
      ‖∑ i, rsign (σ i) • φ (x i)‖ + κ * |∑ i, rsign (σ i)| := by
    intro σ
    refine ciSup_le fun q => ?_
    have heq : ∑ i, rsign (σ i) * a q i =
        inner ℝ q.1.1 (∑ i, rsign (σ i) • φ (x i)) - q.1.2 * ∑ i, rsign (σ i) := by
      rw [inner_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_right]; simp only [ha_def]; ring
    rw [heq]
    have hq := hT₀ q.2
    have h2 : inner ℝ q.1.1 (∑ i, rsign (σ i) • φ (x i)) ≤ ‖∑ i, rsign (σ i) • φ (x i)‖ := by
      refine (real_inner_le_norm _ _).trans ?_
      calc ‖q.1.1‖ * ‖∑ i, rsign (σ i) • φ (x i)‖ ≤ 1 * ‖∑ i, rsign (σ i) • φ (x i)‖ := by
            gcongr; exact hq.1
        _ = _ := one_mul _
    have h3 : -(q.1.2 * ∑ i, rsign (σ i)) ≤ κ * |∑ i, rsign (σ i)| := by
      refine (neg_le_abs _).trans ?_
      rw [abs_mul]; gcongr; exact hq.2
    linarith
  have hball : radE (fun σ : Fin n → Bool => ‖∑ i, rsign (σ i) • φ (x i)‖) ≤ κ * √n := by
    refine (radE_norm_sum_le _).trans ?_
    have : ∑ i, ‖φ (x i)‖ ^ 2 ≤ κ ^ 2 * n := by
      calc ∑ i, ‖φ (x i)‖ ^ 2 ≤ ∑ _i : Fin n, κ ^ 2 :=
            sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hκ _) 2
        _ = κ ^ 2 * n := by simp [Finset.sum_const]; ring
    calc √(∑ i, ‖φ (x i)‖ ^ 2) ≤ √(κ ^ 2 * n) := Real.sqrt_le_sqrt this
      _ = κ * √n := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ0]
  have hshift := radE_abs_sum_rsign_le (n := n)
  calc (n : ℝ)⁻¹ * radE (fun σ => ⨆ q : T₀, ∑ i, rsign (σ i) * max (a q i) 0)
      ≤ (n : ℝ)⁻¹ * radE (fun σ => ⨆ q : T₀, ∑ i, rsign (σ i) * a q i) :=
        mul_le_mul_of_nonneg_left (radE_iSup_posPart_le a ha) (by positivity)
    _ ≤ (n : ℝ)⁻¹ * radE (fun σ : Fin n → Bool =>
          ‖∑ i, rsign (σ i) • φ (x i)‖ + κ * |∑ i, rsign (σ i)|) :=
        mul_le_mul_of_nonneg_left (radE_mono hpt) (by positivity)
    _ = (n : ℝ)⁻¹ * (radE (fun σ : Fin n → Bool => ‖∑ i, rsign (σ i) • φ (x i)‖) +
          κ * radE (fun σ : Fin n → Bool => |∑ i, rsign (σ i)|)) := by
        rw [radE_add, radE_const_mul]
    _ ≤ (n : ℝ)⁻¹ * (κ * √n + κ * √n) := by
        gcongr
    _ = 2 * κ * (√n / n) := by ring
    _ = 2 * κ / √n := by rw [Real.sqrt_div_self']; ring

/-! ### Expected suprema -/

variable (P : Measure X) [IsProbabilityMeasure P]

theorem integral_iSup_empDev_tm_le (T₀ : Set (H × ℝ)) [Countable T₀] [Nonempty T₀]
    (hT₀ : T₀ ⊆ tmParams H κ) (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {n : ℕ}
    (hn : n ≠ 0) :
    ∫ x, ⨆ q : T₀, empDev P (fun q : T₀ => gTM φ q.1) n x q
      ∂(Measure.pi fun _ : Fin n => P) ≤ 4 * κ / √n := by
  have hg : ∀ q : T₀, Measurable (gTM φ q.1) := fun q => measurable_gTM hφ q.1
  have hB : ∀ (q : T₀) y, |gTM φ q.1 y| ≤ 2 * κ := fun q y => abs_gTM_le hκ (hT₀ q.2) y
  have hsym := integral_iSup_empDev_le P hg hB hn
  have hint : Integrable (radAvg (fun q : T₀ => gTM φ q.1) n) (Measure.pi fun _ : Fin n => P) :=
    Integrable.of_bound (measurable_radAvg (T := T₀) hg n).aestronglyMeasurable (2 * κ)
      (ae_of_all _ fun x => abs_radAvg_le hB hn x)
  have := integral_mono hint (integrable_const (2 * κ / √n)) fun x =>
    radAvg_tm_le T₀ hT₀ hκ hn x
  rw [integral_const, probReal_univ, one_smul] at this
  exact hsym.trans ((mul_le_mul_of_nonneg_left this (by norm_num)).trans_eq (by ring))

theorem empDev_neg {T : Type*} (g : T → X → ℝ) (n : ℕ) (x : Fin n → X) (t : T) :
    empDev P (fun t y => -g t y) n x t = -empDev P g n x t := by
  simp only [empDev, integral_neg, sum_neg_distrib]; ring

theorem radAvg_neg {T : Type*} (g : T → X → ℝ) (n : ℕ) (x : Fin n → X) :
    radAvg (fun t y => -g t y) n x = radAvg g n x := by
  unfold radAvg
  rw [← radE_negSigns]
  congr 1
  funext σ
  simp only [negSigns, rsign_not, neg_mul, mul_neg, neg_neg]

theorem integral_iSup_neg_empDev_tm_le (T₀ : Set (H × ℝ)) [Countable T₀] [Nonempty T₀]
    (hT₀ : T₀ ⊆ tmParams H κ) (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {n : ℕ}
    (hn : n ≠ 0) :
    ∫ x, ⨆ q : T₀, empDev P (fun (q : T₀) y => -gTM φ q.1 y) n x q
      ∂(Measure.pi fun _ : Fin n => P) ≤ 4 * κ / √n := by
  have hg : ∀ q : T₀, Measurable fun y => -gTM φ q.1 y := fun q => (measurable_gTM hφ q.1).neg
  have hB : ∀ (q : T₀) y, |-gTM φ q.1 y| ≤ 2 * κ := fun q y => by
    rw [abs_neg]; exact abs_gTM_le hκ (hT₀ q.2) y
  have hsym := integral_iSup_empDev_le P hg hB hn
  have hint : Integrable (radAvg (fun (q : T₀) y => -gTM φ q.1 y) n)
      (Measure.pi fun _ : Fin n => P) :=
    Integrable.of_bound (measurable_radAvg (T := T₀) hg n).aestronglyMeasurable (2 * κ)
      (ae_of_all _ fun x => abs_radAvg_le hB hn x)
  have := integral_mono hint (integrable_const (2 * κ / √n)) fun x => by
    rw [radAvg_neg]; exact radAvg_tm_le T₀ hT₀ hκ hn x
  rw [integral_const, probReal_univ, one_smul] at this
  exact hsym.trans ((mul_le_mul_of_nonneg_left this (by norm_num)).trans_eq (by ring))

/-! ### High-probability bound for a countable subclass -/

theorem abs_empDev_tm_update_le (hκ : ∀ x, ‖φ x‖ ≤ κ) {T₀ : Set (H × ℝ)}
    (hT₀ : T₀ ⊆ tmParams H κ) {n : ℕ} (s : ℝ) (hs : |s| = 1) (q : T₀) (x : Fin n → X)
    (i : Fin n) (b : X) :
    |empDev P (fun (q : T₀) y => s * gTM φ q.1 y) n (Function.update x i b) q -
      empDev P (fun (q : T₀) y => s * gTM φ q.1 y) n x q| ≤ 2 * κ / n := by
  rw [empDev_update_sub, abs_mul, abs_inv, Nat.abs_cast, div_eq_inv_mul, ← mul_sub, abs_mul, hs,
    one_mul]
  gcongr
  have h1 := gTM_mem_Icc hκ (hT₀ q.2) b
  have h2 := gTM_mem_Icc hκ (hT₀ q.2) (x i)
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Uniform concentration over a countable subclass of `𝒢`.** -/
theorem tm_concentration_countable (T₀ : Set (H × ℝ)) [Countable T₀] [Nonempty T₀]
    (hT₀ : T₀ ⊆ tmParams H κ) (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hκpos : 0 < κ) {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin n => P).real
      {x | ⨆ q : T₀, |empDev P (fun q : T₀ => gTM φ q.1) n x q| ≤
        4 * κ / √n + κ * √(2 * log (2 / δ) / n)} := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
  set Pn := Measure.pi fun _ : Fin n => P
  set g : T₀ → X → ℝ := fun q => gTM φ q.1 with hg_def
  set gn : T₀ → X → ℝ := fun q y => -gTM φ q.1 y with hgn_def
  have hδ2 : 0 < δ / 2 := by positivity
  have hδ21 : δ / 2 ≤ 1 := by linarith
  have hL : 0 ≤ log (1 / (δ / 2)) := Real.log_nonneg (by rw [le_div_iff₀ hδ2]; linarith)
  have hlog : log (1 / (δ / 2)) = log (2 / δ) := by rw [one_div_div]
  set ε := κ * √(2 * log (2 / δ) / n) with hε
  have hgm : ∀ q : T₀, Measurable (g q) := fun q => measurable_gTM hφ q.1
  have hgnm : ∀ q : T₀, Measurable (gn q) := fun q => (measurable_gTM hφ q.1).neg
  have hgB : ∀ (q : T₀) y, |g q y| ≤ 2 * κ := fun q y => abs_gTM_le hκ (hT₀ q.2) y
  have hgnB : ∀ (q : T₀) y, |gn q y| ≤ 2 * κ := fun q y => by
    simp only [hgn_def, abs_neg]; exact abs_gTM_le hκ (hT₀ q.2) y
  have hc : (0 : ℝ) < 2 * κ / n := by positivity
  -- the two McDiarmid events
  have hplus := iSup_tail P hn0 (fun q x => empDev P g n x q) (fun q => measurable_empDev P hgm n q)
    (C := 2 * (2 * κ)) (fun q x => abs_empDev_le P hgB x q) hc
    (fun q x i b => by
      have := abs_empDev_tm_update_le P hκ hT₀ 1 (by simp) q x i b
      simpa [hg_def] using this) hδ2 hδ21
  have hminus := iSup_tail P hn0 (fun q x => empDev P gn n x q)
    (fun q => measurable_empDev P hgnm n q)
    (C := 2 * (2 * κ)) (fun q x => abs_empDev_le P hgnB x q) hc
    (fun q x i b => by
      have := abs_empDev_tm_update_le P hκ hT₀ (-1) (by simp) q x i b
      simpa [hgn_def] using this) hδ2 hδ21
  rw [two_mul_div_mul_sqrt hn0 hL, hlog] at hplus hminus
  set Ep := {x | ⨆ q, empDev P g n x q ≤ (∫ y, ⨆ q, empDev P g n y q ∂Pn) + ε} with hEp
  set Em := {x | ⨆ q, empDev P gn n x q ≤ (∫ y, ⨆ q, empDev P gn n y q ∂Pn) + ε} with hEm
  have hEpm : MeasurableSet Ep :=
    measurableSet_le (Measurable.iSup fun q => measurable_empDev P hgm n q) measurable_const
  have hEmm : MeasurableSet Em :=
    measurableSet_le (Measurable.iSup fun q => measurable_empDev P hgnm n q) measurable_const
  have hIp := integral_iSup_empDev_tm_le P T₀ hT₀ hφ hκ hn0
  have hIm := integral_iSup_neg_empDev_tm_le P T₀ hT₀ hφ hκ hn0
  -- on `Ep ∩ Em` the two-sided bound holds
  have hsub : Ep ∩ Em ⊆ {x | ⨆ q : T₀, |empDev P (fun q : T₀ => gTM φ q.1) n x q| ≤
      4 * κ / √n + ε} := by
    rintro x ⟨hxp, hxm⟩
    simp only [hEp, hEm, Set.mem_ofPred_eq] at hxp hxm ⊢
    refine ciSup_le fun q => abs_le.2 ⟨?_, ?_⟩
    · have h1 : empDev P gn n x q ≤ ⨆ q, empDev P gn n x q :=
        le_ciSup (bddAbove_of_abs_le fun q => abs_empDev_le P hgnB x q) q
      have h2 : empDev P gn n x q = -empDev P g n x q := empDev_neg P g n x q
      change -(4 * κ / √n + ε) ≤ empDev P g n x q
      linarith
    · have h1 : empDev P g n x q ≤ ⨆ q, empDev P g n x q :=
        le_ciSup (bddAbove_of_abs_le fun q => abs_empDev_le P hgB x q) q
      change empDev P g n x q ≤ 4 * κ / √n + ε
      linarith
  refine le_trans ?_ (measureReal_mono hsub)
  have hcompl : Pn.real (Ep ∩ Em)ᶜ ≤ Pn.real Epᶜ + Pn.real Emᶜ := by
    rw [Set.compl_inter]; exact measureReal_union_le _ _
  rw [probReal_compl_eq_one_sub (hEpm.inter hEmm), probReal_compl_eq_one_sub hEpm,
    probReal_compl_eq_one_sub hEmm] at hcompl
  linarith

/-! ### Device (b): from a countable dense subclass to all of `𝒢` -/

theorem abs_gTM_sub_le (hκ : ∀ x, ‖φ x‖ ≤ κ) (p q : H × ℝ) (y : X) :
    |gTM φ p y - gTM φ q y| ≤ (κ + 1) * dist p q := by
  refine (abs_max_sub_max_le_abs _ _ 0).trans ?_
  have hd1 : ‖p.1 - q.1‖ ≤ dist p q := by
    rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ dist p q := by
    rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_right _ _
  have h1 : |inner ℝ (p.1 - q.1) (φ y)| ≤ κ * dist p q :=
    (abs_real_inner_le_norm _ _).trans (by
      rw [mul_comm]; exact mul_le_mul (hκ y) hd1 (norm_nonneg _) ((norm_nonneg _).trans (hκ y)))
  have : inner ℝ p.1 (φ y) - p.2 - (inner ℝ q.1 (φ y) - q.2) =
      inner ℝ (p.1 - q.1) (φ y) - (p.2 - q.2) := by rw [inner_sub_left]; ring
  rw [this]
  refine (abs_sub _ _).trans ?_
  linarith

theorem continuous_empDev_tm (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {n : ℕ}
    (x : Fin n → X) : Continuous fun p : H × ℝ => empDev P (gTM φ) n x p := by
  have hκ0 : 0 ≤ κ := by
    obtain ⟨y⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ y)
  have h0 : ∀ y, gTM φ (0 : H × ℝ) y = 0 := fun y => by simp [gTM]
  have hint : ∀ p : H × ℝ, Integrable (gTM φ p) P := fun p =>
    Integrable.of_bound (measurable_gTM hφ p).aestronglyMeasurable ((κ + 1) * dist p 0)
      (ae_of_all _ fun y => by
        have := abs_gTM_sub_le hκ p 0 y
        rw [h0, sub_zero] at this
        rwa [Real.norm_eq_abs])
  have hlip : LipschitzWith (κ + 1).toNNReal fun p : H × ℝ => ∫ y, gTM φ p y ∂P := by
    refine LipschitzWith.of_dist_le' fun p q => ?_
    rw [Real.dist_eq, ← integral_sub (hint p) (hint q)]
    have := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun y => gTM φ p y - gTM φ q y) (C := (κ + 1) * dist p q)
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact abs_gTM_sub_le hκ p q y)
    simpa [Real.norm_eq_abs] using this
  have hsum : Continuous fun p : H × ℝ => ∑ i, gTM φ p (x i) :=
    continuous_finset_sum _ fun i _ =>
      ((continuous_fst.inner continuous_const).sub continuous_snd).max continuous_const
  exact (continuous_const.mul hsum).sub hlip.continuous

theorem iSup_tmParams_eq (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (T₀ : Set (H × ℝ)) [Nonempty T₀] (hT₀ : T₀ ⊆ tmParams H κ)
    (hdense : tmParams H κ ⊆ closure T₀) {n : ℕ} (x : Fin n → X) :
    (⨆ p : tmParams H κ, |empDev P (gTM φ) n x p.1|) =
      ⨆ q : T₀, |empDev P (gTM φ) n x q.1| := by
  obtain ⟨q₀⟩ := ‹Nonempty T₀›
  haveI : Nonempty (tmParams H κ) := ⟨⟨q₀.1, hT₀ q₀.2⟩⟩
  have hbΘ : BddAbove (Set.range fun p : tmParams H κ => |empDev P (gTM φ) n x p.1|) :=
    bddAbove_of_abs_le (C := 2 * (2 * κ)) fun p => by
      rw [abs_abs]
      exact abs_empDev_le P (g := fun p : tmParams H κ => gTM φ p.1)
        (fun p y => abs_gTM_le hκ p.2 y) x p
  have hb0 : BddAbove (Set.range fun q : T₀ => |empDev P (gTM φ) n x q.1|) :=
    bddAbove_of_abs_le (C := 2 * (2 * κ)) fun q => by
      rw [abs_abs]
      exact abs_empDev_le P (g := fun q : T₀ => gTM φ q.1)
        (fun q y => abs_gTM_le hκ (hT₀ q.2) y) x q
  refine le_antisymm (ciSup_le fun p => ?_) (ciSup_le fun q => ?_)
  · have hcl : closure T₀ ⊆
        {r | |empDev P (gTM φ) n x r| ≤ ⨆ q : T₀, |empDev P (gTM φ) n x q.1|} :=
      closure_minimal (fun r hr => le_ciSup hb0 ⟨r, hr⟩)
        (isClosed_le (continuous_abs.comp (continuous_empDev_tm P hφ hκ x)) continuous_const)
    exact hcl (hdense p.2)
  · exact le_ciSup hbΘ ⟨q.1, hT₀ q.2⟩

/-- **`trimmed-mmd` `thm:concentration`, uniform-deviation event** (supplement Steps 2–3): for
separable `H`, `n ≥ 1` and `0 < δ < 1`, with probability at least `1 − δ`,
`sup_{g ∈ 𝒢} |(Pₙ − P) g| ≤ 4κ/√n + κ √(2 log(2/δ)/n)`, where
`𝒢 = {(⟪f, φ ·⟫ − t)₊ : ‖f‖ ≤ 1, |t| ≤ κ}`. -/
theorem tm_concentration [TopologicalSpace.SeparableSpace H] (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκpos : 0 < κ) {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin n => P).real
      {x | ⨆ p : tmParams H κ, |empDev P (gTM φ) n x p.1| ≤
        4 * κ / √n + κ * √(2 * log (2 / δ) / n)} := by
  obtain ⟨T₀, hT₀, hcount, hdense⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (tmParams H κ)).exists_countable_dense_subset
  have h0 : ((0 : H), (0 : ℝ)) ∈ tmParams H κ := ⟨by simp, by simp [hκpos.le]⟩
  have hne : T₀.Nonempty := closure_nonempty_iff.1 ⟨_, hdense h0⟩
  haveI : Nonempty T₀ := hne.to_subtype
  haveI : Countable T₀ := hcount.to_subtype
  have hset : {x : Fin n → X | ⨆ p : tmParams H κ, |empDev P (gTM φ) n x p.1| ≤
      4 * κ / √n + κ * √(2 * log (2 / δ) / n)} =
      {x | ⨆ q : T₀, |empDev P (fun q : T₀ => gTM φ q.1) n x q| ≤
        4 * κ / √n + κ * √(2 * log (2 / δ) / n)} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [iSup_tmParams_eq P hφ hκ T₀ hT₀ hdense x]
    rfl
  rw [hset]
  exact tm_concentration_countable P T₀ hT₀ hφ hκ hκpos hn hδ0 hδ1

end StatFormal.Concentration
