import StatFormal.Wave30tn.RouteTrimLip
import StatFormal.Lib.DKW.Massart
import StatFormal.Lib.TrimmedMean.Population
import StatFormal.Archive.Wave12c.RouteTrimConsist
import StatFormal.Archive.Wave22c.RouteSplit
import StatFormal.Archive.TrimmedMMD.Lower.Proofs

/-!
# Route — wave 30tn: `prop:splitfs` and the finite-sample clause of `cor:lower` (untrusted)

* `isLeast_lowerTrim`: `min_{a ∈ 𝒞_α(R)} ⟨f, a⟩ = L(law of ⟨f, φ⟩ under R)` — weak duality `∫ ψ_s(h) dR ≤ ∫ g h dR` for
  every trimming density `g` and every `s`, and the library minimiser (`isLeast_region`) at the quantile of the frozen
  wave-12c `quantileAt`; so `T = L(F) + L(G)`, `F`, `G` the laws of `f̂(X)` and `−f̂(Y)`.
* `side_bound`: `|L_n − L(F)| ≤ 2κβ ‖F_n − F‖_∞` (eq:trimlip with the empirical law, `lowerTrim_empirical`).
* `dkw_event`: `P(‖F_n − F‖_∞ > e) ≤ 2e^{−2ne²}` (library DKW–Massart with the score `e^{h}`, transported from
  `Measure.pi` to the sample space by `iIndepFun_iff_map_fun_eq_pi_map` and `Measure.le_map_apply`).
* `two_exp_dkwRad`: `2 exp(−2n e_n(δ)²) = δ/2`; union bound.
* Level: under `TV ≤ α`, `T ≤ 0` (frozen wave-22c `split_null_nonpos`).
* `cor_lower_fs`: the frozen `downclosed_pathwise` puts `{α̂_lo > TV}` inside the rejection at the first grid level
  `≥ TV`, a true null; or the event is empty.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatFormal.Wave30tn

open StatFormal.Wave29i (splitTrimLo splitTrimUp)
open StatFormal.TrimmedMMD.Concentration (region empirical)
open StatFormal.Foundations.TrimmedMean (isLeast_region inner_integral_smul measurable_inner_comp abs_inner_le
  iInf_coe_of_isLeast iSup_coe_of_isGreatest trimUp_eq)

section Pop
variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma integral_psi_map (R : Measure 𝒳) {h : 𝒳 → ℝ} (hh : Measurable h) (α s : ℝ) :
    ∫ u, psi α s u ∂(R.map h) = ∫ x, psi α s (h x) ∂R :=
  integral_map hh.aemeasurable (continuous_psi α s).aestronglyMeasurable

/-- Weak duality: `∫ ψ_s(h) dR ≤ ⟨f, a⟩` for every `a ∈ 𝒞_α(R)` and every `s`. -/
lemma weak_dual (R : Measure 𝒳) [IsProbabilityMeasure R] {φ : 𝒳 → H} {κ α : ℝ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα1 : α < 1) (f : H) (s : ℝ) {a : H} (ha : a ∈ region φ α R) :
    ∫ x, psi α s ⟪f, φ x⟫ ∂R ≤ ⟪f, a⟫ := by
  obtain ⟨g, hg, hgb, hg1, rfl⟩ := ha
  set h : 𝒳 → ℝ := fun x => ⟪f, φ x⟫ with hhdef
  have hhm : Measurable h := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  have hβ : 0 < 1 - α := by linarith
  have hgC : ∀ x, |g x| ≤ 1 / (1 - α) := fun x => by rw [abs_of_nonneg (hgb x).1]; exact (hgb x).2
  rw [inner_integral_smul R hφ hκ hg hgC f]
  have hgi : Integrable g R := Integrable.of_bound hg.aestronglyMeasurable (1 / (1 - α))
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hgC x)
  have hpos : Integrable (fun x => max (s - h x) 0) R := Integrable.of_bound
    ((hhm.const_sub s).max measurable_const).aestronglyMeasurable (|s| + ‖f‖ * κ)
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (by have := (abs_nonneg _).trans (hB x); positivity)
      have := le_abs_self s; have := neg_abs_le (h x); have := hB x; linarith)
  have hgh : Integrable (fun x => g x * h x) R := Integrable.of_bound
    (hg.mul hhm).aestronglyMeasurable (1 / (1 - α) * (‖f‖ * κ)) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgC x) (hB x) (abs_nonneg _) (by positivity))
  have e1 : ∫ x, psi α s (h x) ∂R = ∫ x, (s * g x - (1 - α)⁻¹ * max (s - h x) 0) ∂R := by
    unfold psi
    rw [integral_sub (integrable_const s) (hpos.const_mul _), integral_sub (hgi.const_mul s) (hpos.const_mul _),
      integral_const, integral_const_mul s, hg1]
    simp
  rw [e1]
  refine integral_mono ((hgi.const_mul s).sub (hpos.const_mul _)) hgh fun x => ?_
  have h1 := (hgb x).1
  have h2 : g x ≤ (1 - α)⁻¹ := by rw [← one_div]; exact (hgb x).2
  have h3 : s - h x ≤ max (s - h x) 0 := le_max_left _ _
  have h4 : 0 ≤ max (s - h x) 0 := le_max_right _ _
  simp only
  nlinarith [mul_le_mul_of_nonneg_left h3 h1, mul_le_mul_of_nonneg_right h2 h4]

/-- `min_{a ∈ 𝒞_α(R)} ⟨f, a⟩ = L(R ∘ ⟨f, φ⟩⁻¹)`. -/
lemma isLeast_lowerTrim (R : Measure 𝒳) [IsProbabilityMeasure R] {φ : 𝒳 → H} {κ α : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (f : H) :
    IsLeast ((fun a => ⟪f, a⟫) '' region φ α R) (lowerTrim (R.map fun x => ⟪f, φ x⟫) α) := by
  set h : 𝒳 → ℝ := fun x => ⟪f, φ x⟫ with hhdef
  have hhm : Measurable h := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  have hp0 : 0 < 1 - α := by linarith
  have hp1 : 1 - α ≤ 1 := by linarith
  set q := StatFormal.Wave12c.quantileAt R h (1 - α)
  have hq1 := StatFormal.Wave12c.quantile_lt_le R hhm hB hp0 hp1
  have hq2 := StatFormal.Wave12c.quantile_ge R hhm hB hp0 hp1
  have hL := isLeast_region R hφ hκ hα0 hα1 f hq1 hq2
  suffices hV : lowerTrim (R.map h) α = q - (1 - α)⁻¹ * ∫ x, max (q - ⟪f, φ x⟫) 0 ∂R by rw [hV]; exact hL
  obtain ⟨⟨a, ha, hav⟩, -⟩ := hL
  have hw : ∀ s, ∫ u, psi α s u ∂(R.map h) ≤ ⟪f, a⟫ := fun s => by
    rw [integral_psi_map R hhm]; exact weak_dual R hφ hκ hα1 f s ha
  simp only at hav
  refine le_antisymm ?_ ?_
  · rw [← hav]; exact ciSup_le hw
  · refine le_ciSup_of_le ⟨⟪f, a⟫, by rintro _ ⟨s, rfl⟩; exact hw s⟩ q (le_of_eq ?_)
    rw [integral_psi_map R hhm]
    unfold psi
    have hpos : Integrable (fun x => max (q - h x) 0) R := Integrable.of_bound
      ((hhm.const_sub q).max measurable_const).aestronglyMeasurable (|q| + ‖f‖ * κ)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        refine max_le ?_ (by have := (abs_nonneg _).trans (hB x); positivity)
        have := le_abs_self q; have := neg_abs_le (h x); have := hB x; linarith)
    rw [integral_sub (integrable_const q) (hpos.const_mul _), integral_const, integral_const_mul]
    simp [h]

lemma kappa_nonneg_of_prob (R : Measure 𝒳) [IsProbabilityMeasure R] {φ : 𝒳 → H} {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) : 0 ≤ κ := by
  obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure R
  exact (norm_nonneg _).trans (hκ x)

/-- `sep(f; 𝒞_α(P), 𝒞_α(Q)) = L(F) + L(G)`, `F` the law of `⟨f, φ⟩` under `P`, `G` that of `⟨−f, φ⟩` under `Q`. -/
lemma sepVal_eq_lowerTrim (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {κ α : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (f : H) :
    StatFormal.Wave17a.sepVal f (region φ α P) (region φ α Q) =
      ((lowerTrim (P.map fun x => ⟪f, φ x⟫) α + lowerTrim (Q.map fun x => ⟪-f, φ x⟫) α : ℝ) : EReal) := by
  have hP := isLeast_lowerTrim P hφ hκ hα0 hα1 f
  obtain ⟨⟨b, hb, hbv⟩, hlb⟩ := isLeast_lowerTrim Q hφ hκ hα0 hα1 (-f)
  have hQ : IsGreatest ((fun b => ⟪f, b⟫) '' region φ α Q) (-lowerTrim (Q.map fun x => ⟪-f, φ x⟫) α) := by
    refine ⟨⟨b, hb, ?_⟩, ?_⟩
    · simp only [inner_neg_left] at hbv ⊢; linarith
    · rintro _ ⟨c, hc, rfl⟩
      have := hlb ⟨c, hc, rfl⟩
      simp only [inner_neg_left] at this ⊢; linarith
  unfold StatFormal.Wave17a.sepVal
  rw [iInf_coe_of_isLeast hP, iSup_coe_of_isGreatest hQ, ← EReal.coe_sub]
  congr 1; ring

end Pop

section Emp

lemma integral_empirical_sm {n : ℕ} (v : Fin n → ℝ) {g : ℝ → ℝ} (hg : StronglyMeasurable g) :
    ∫ u, g u ∂(empirical v) = (∑ i, g (v i)) / n := by
  unfold empirical
  rw [integral_finsetSum_measure fun i _ =>
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)]
  simp_rw [integral_smul_measure, integral_dirac' _ _ hg]
  rw [ENNReal.toReal_ofReal (by positivity), Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]; ring

lemma empirical_real_Iic {n : ℕ} (hn : 1 ≤ n) (v : Fin n → ℝ) (u : ℝ) :
    (empirical v).real (Iic u) = ((Finset.univ.filter fun i => v i ≤ u).card : ℝ) / n := by
  haveI := isProbabilityMeasure_empirical' v hn
  rw [← integral_indicator_one measurableSet_Iic,
    integral_empirical_sm v (g := (Iic u).indicator 1) (stronglyMeasurable_one.indicator measurableSet_Iic),
    Finset.natCast_card_filter]
  rfl

lemma empirical_Icc {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (v : Fin n → ℝ) (hv : ∀ i, v i ∈ Icc (-κ) κ) :
    empirical v (Icc (-κ) κ) = 1 := by
  haveI := isProbabilityMeasure_empirical' v hn
  rw [← prob_compl_eq_zero_iff measurableSet_Icc]
  simp only [empirical, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Measure.dirac_apply' _ measurableSet_Icc.compl]
  simp [Set.indicator, hv i]

end Emp

section DKW
variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]

lemma map_sample_pi (μ : Measure Ω) [IsProbabilityMeasure μ] {X : ℕ → Ω → 𝒳} {P : Measure 𝒳}
    (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X μ) (hlaw : ∀ j, μ.map (X j) = P) (n : ℕ) :
    μ.map (fun ω (j : Fin n) => X j ω) = Measure.pi fun _ : Fin n => P := by
  have hind' : iIndepFun (fun j : Fin n => X j) μ := hind.precomp Fin.val_injective
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun j : Fin n => (hX j).aemeasurable)).1 hind']
  simp only [hlaw]

/-- DKW–Massart on the sample space for a real score `h`. -/
lemma dkw_event (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure 𝒳) [IsProbabilityMeasure P]
    {X : ℕ → Ω → 𝒳} (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i) = P)
    {h : 𝒳 → ℝ} (hh : Measurable h) {n : ℕ} (hn : 1 ≤ n) {e : ℝ} (he : 0 ≤ e) :
    μ {ω | ∃ u : ℝ, e < |((Finset.univ.filter fun i : Fin n => h (X i ω) ≤ u).card : ℝ) / n -
        P.real {x | h x ≤ u}|} ≤ ENNReal.ofReal (2 * Real.exp (-2 * n * e ^ 2)) := by
  set S : Ω → (Fin n → 𝒳) := fun ω j => X j ω with hSdef
  have hS : Measurable S := measurable_pi_iff.2 fun j => hXm j
  set V : 𝒳 → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (h x)) with hVdef
  have hV : Measurable V := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hh)
  have hVle : ∀ x u, V x ≤ ENNReal.ofReal (Real.exp u) ↔ h x ≤ u := fun x u => by
    simp only [V]; rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos u).le, Real.exp_le_exp]
  set B : Set (Fin n → 𝒳) := {y | ∃ s, e < |((Finset.univ.filter fun i => V (y i) ≤ s).card : ℝ) / n -
    (P {x | V x ≤ s}).toReal|}
  have hsub : {ω | ∃ u : ℝ, e < |((Finset.univ.filter fun i : Fin n => h (X i ω) ≤ u).card : ℝ) / n -
      P.real {x | h x ≤ u}|} ⊆ S ⁻¹' B := by
    rintro ω ⟨u, hu⟩
    refine ⟨ENNReal.ofReal (Real.exp u), ?_⟩
    have h1 : (Finset.univ.filter fun i => V (S ω i) ≤ ENNReal.ofReal (Real.exp u)) =
        Finset.univ.filter fun i : Fin n => h (X i ω) ≤ u := by
      ext i; simp [hVle, S]
    have h2 : {x | V x ≤ ENNReal.ofReal (Real.exp u)} = {x | h x ≤ u} := by ext x; simp [hVle]
    rw [h1, h2, ← measureReal_def]
    exact hu
  calc _ ≤ μ (S ⁻¹' B) := measure_mono hsub
    _ ≤ μ.map S B := Measure.le_map_apply hS.aemeasurable B
    _ = (Measure.pi fun _ : Fin n => P) B := by rw [map_sample_pi μ hXm hind hlaw n]
    _ ≤ _ := StatFormal.DKW.Massart.massart P V hV hn he

lemma two_exp_dkwRad {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    2 * Real.exp (-2 * n * dkwRad n δ ^ 2) = δ / 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (4 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  unfold dkwRad
  rw [Real.sq_sqrt (by positivity)]
  have : -2 * (n : ℝ) * (Real.log (4 / δ) / (2 * n)) = Real.log (δ / 4) := by
    rw [show δ / 4 = (4 / δ)⁻¹ by field_simp, Real.log_inv]; field_simp
  rw [this, Real.exp_log (by positivity)]; ring

lemma dkwRad_nonneg (n : ℕ) (δ : ℝ) : 0 ≤ dkwRad n δ := Real.sqrt_nonneg _

end DKW

section Main
variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `D_n = ‖F_n − F‖_∞` for the sample `g(v_1), …, g(v_k)` and the law of `g` under `R`. -/
def supDev (R : Measure 𝒳) (g : 𝒳 → ℝ) {k : ℕ} (v : Fin k → 𝒳) : ℝ :=
  ⨆ u : ℝ, |((Finset.univ.filter fun i => g (v i) ≤ u).card : ℝ) / k - R.real {x | g x ≤ u}|

lemma bdd_supDev (R : Measure 𝒳) [IsProbabilityMeasure R] (g : 𝒳 → ℝ) {k : ℕ} (hk : 1 ≤ k) (v : Fin k → 𝒳) :
    BddAbove (range fun u : ℝ => |((Finset.univ.filter fun i => g (v i) ≤ u).card : ℝ) / k -
      R.real {x | g x ≤ u}|) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨u, rfl⟩
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : ((Finset.univ.filter fun i => g (v i) ≤ u).card : ℝ) / k ≤ 1 := by
    rw [div_le_one hk']; exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have h2 : 0 ≤ ((Finset.univ.filter fun i => g (v i) ≤ u).card : ℝ) / k := by positivity
  have h3 := measureReal_le_one (μ := R) (s := {x | g x ≤ u})
  have h4 := measureReal_nonneg (μ := R) (s := {x | g x ≤ u})
  rw [abs_le]; constructor <;> linarith

/-- One side: `|L_k − L(R ∘ g⁻¹)| ≤ 2κβ ‖F_k − F‖_∞`. -/
lemma side_bound (R : Measure 𝒳) [IsProbabilityMeasure R] {g : 𝒳 → ℝ} (hg : Measurable g) {κ α : ℝ}
    (hgb : ∀ x, |g x| ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) {k : ℕ} (hk : 1 ≤ k) (v : Fin k → 𝒳) :
    |splitTrimLo k α (fun i => g (v i)) - lowerTrim (R.map g) α| ≤ 2 * κ * (1 - α)⁻¹ * supDev R g v := by
  haveI := isProbabilityMeasure_empirical' (fun i => g (v i)) hk
  have hmem : ∀ x, g x ∈ Icc (-κ) κ := fun x => abs_le.1 (hgb x)
  have hE := empirical_Icc hk (fun i => g (v i)) fun i => hmem (v i)
  have hM : R.map g (Icc (-κ) κ) = 1 := by
    rw [Measure.map_apply hg measurableSet_Icc]
    have : g ⁻¹' Icc (-κ) κ = univ := eq_univ_of_forall hmem
    rw [this, measure_univ]
  obtain ⟨-, h1, h2⟩ := trimlip_route _ _ κ α hE hM hα0 hα1
  rw [← lowerTrim_empirical (by omega) hα0 hα1]
  refine (h1.trans h2).trans (le_of_eq ?_)
  unfold supDev
  congr 1
  refine iSup_congr fun u => ?_
  rw [empirical_real_Iic hk, map_measureReal_apply hg measurableSet_Iic]
  rfl

lemma side_prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Measure 𝒳)
    [IsProbabilityMeasure R] {X : ℕ → Ω → 𝒳} (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = R) {g : 𝒳 → ℝ} (hg : Measurable g) {k : ℕ} (hk : 1 ≤ k) {e : ℝ} (he : 0 ≤ e) :
    μ {ω | e < supDev R g (fun i : Fin k => X i ω)} ≤ ENNReal.ofReal (2 * Real.exp (-2 * k * e ^ 2)) := by
  refine (measure_mono fun ω (hω : e < supDev R g (fun i : Fin k => X i ω)) => ?_).trans
    (dkw_event μ R hXm hind hlaw hg hk he)
  obtain ⟨u, hu⟩ := exists_lt_of_lt_ciSup hω
  exact ⟨u, hu⟩

theorem splitfs_route : Claims.splitfs := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ α δ f Ω _ μ _ X Y n m hφ hκ hf hα0 hα1 hδ0 hδ1 hXm hYm hXi hYi hXl hYl hn hm
  have hκ0 := kappa_nonneg_of_prob P hκ
  set h : 𝒳 → ℝ := fun x => ⟪f, φ x⟫ with hhdef
  set h' : 𝒳 → ℝ := fun x => ⟪-f, φ x⟫ with hh'def
  have hhm : Measurable h := measurable_inner_comp hφ f
  have hh'm : Measurable h' := measurable_inner_comp hφ (-f)
  have hbd : ∀ (f' : H), ‖f'‖ ≤ 1 → ∀ x, |⟪f', φ x⟫| ≤ κ := fun f' hf' x =>
    (abs_inner_le hκ f' x).trans (by nlinarith [norm_nonneg f'])
  have hhb : ∀ x, |h x| ≤ κ := hbd f hf
  have hh'b : ∀ x, |h' x| ≤ κ := hbd (-f) (by rwa [norm_neg])
  set LP := lowerTrim (P.map h) α
  set LQ := lowerTrim (Q.map h') α
  set β := (1 - α)⁻¹
  have hβ : 0 ≤ β := inv_nonneg.2 (by linarith)
  set c := 2 * κ * β * (dkwRad n δ + dkwRad m δ) with hc
  -- the statistic
  have hT : ∀ ω, splitTrimLo n α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp m α (fun j => ⟪f, φ (Y j ω)⟫) =
      splitTrimLo n α (fun i => h (X i ω)) + splitTrimLo m α (fun j => h' (Y j ω)) := fun ω => by
    have := trimUp_eq (by omega : 0 < m) hα0 hα1 (fun j => ⟪f, φ (Y j ω)⟫)
    unfold splitTrimUp
    rw [this]
    simp only [h, h', inner_neg_left]
    unfold splitTrimLo
    ring
  -- pathwise bound
  have hpath : ∀ ω, |splitTrimLo n α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp m α (fun j => ⟪f, φ (Y j ω)⟫) -
      (LP + LQ)| ≤ 2 * κ * β * supDev P h (fun i : Fin n => X i ω) +
        2 * κ * β * supDev Q h' (fun j : Fin m => Y j ω) := fun ω => by
    rw [hT ω]
    have h1 := side_bound P hhm hhb hα0 hα1 hn (fun i : Fin n => X i ω)
    have h2 := side_bound Q hh'm hh'b hα0 hα1 hm (fun j : Fin m => Y j ω)
    calc _ = |(splitTrimLo n α (fun i => h (X i ω)) - LP) + (splitTrimLo m α (fun j => h' (Y j ω)) - LQ)| := by
          ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)
  have hsub : {ω | c < |splitTrimLo n α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp m α (fun j => ⟪f, φ (Y j ω)⟫) -
      (LP + LQ)|} ⊆ {ω | dkwRad n δ < supDev P h (fun i : Fin n => X i ω)} ∪
        {ω | dkwRad m δ < supDev Q h' (fun j : Fin m => Y j ω)} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union] at hω ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hκβ : 0 ≤ 2 * κ * β := by positivity
    have := hpath ω
    have : 2 * κ * β * supDev P h (fun i : Fin n => X i ω) + 2 * κ * β * supDev Q h' (fun j : Fin m => Y j ω) ≤ c := by
      rw [hc, mul_add]; exact add_le_add (mul_le_mul_of_nonneg_left h1 hκβ) (mul_le_mul_of_nonneg_left h2 hκβ)
    linarith
  have hprob : μ {ω | c < |splitTrimLo n α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp m α (fun j => ⟪f, φ (Y j ω)⟫) -
      (LP + LQ)|} ≤ ENNReal.ofReal δ := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have e1 := side_prob μ P hXm hXi hXl hhm hn (dkwRad_nonneg n δ)
    have e2 := side_prob μ Q hYm hYi hYl hh'm hm (dkwRad_nonneg m δ)
    rw [two_exp_dkwRad hn hδ0 hδ1] at e1
    rw [two_exp_dkwRad hm hδ0 hδ1] at e2
    calc _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add e1 e2
      _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  refine ⟨LP + LQ, sepVal_eq_lowerTrim P Q hφ hκ hα0 hα1 f, hprob, fun hnull => ?_⟩
  have hT0 : LP + LQ ≤ 0 := by
    have := StatFormal.Wave22c.split_null_nonpos 𝒳 H P Q φ κ α hφ hκ hα0 hα1 hnull f
    rw [sepVal_eq_lowerTrim P Q hφ hκ hα0 hα1 f] at this
    exact_mod_cast this
  refine (measure_mono fun ω (hω : c < _) => ?_).trans hprob
  simp only [mem_ofPred_eq]
  refine lt_of_lt_of_le hω ?_
  refine le_trans ?_ (le_abs_self _)
  linarith

end Main

end StatFormal.Wave30tn
