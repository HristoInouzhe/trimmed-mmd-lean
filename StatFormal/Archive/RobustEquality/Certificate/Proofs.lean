import StatFormal.Archive.RobustEquality.Certificate.Statements
import StatFormal.Archive.RobustEquality.Gibbs
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Proofs: `thm:certificate` and `prop:uniform`

Route (the paper's): triangle inequality for `W₂`; the groupwise coupling
`π = n⁻¹ Σ_i (Γ_i).map (z ↦ (h(x_i), h z))` of `h#P̂` and `h#Q`; Lagrangian + Gibbs per anchor
(`gibbs_finite_case`); union bound for the uniform statement.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti
open scoped ENNReal

namespace StatFormal.RobustEquality.Certificate

variable {K : Type} [MeasurableSpace K]

lemma centre_isProb {n : ℕ} (hn : 0 < n) (x : Fin n → K) : IsProbabilityMeasure (centre x) := by
  constructor
  simp only [centre, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

lemma map_centre {n : ℕ} (x : Fin n → K) {h : K → ℝ} (hh : Measurable h) :
    (centre x).map h = (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (h (x i)) := by
  rw [centre, Measure.map_smul _ hh.aemeasurable, Measure.map_finset_sum' hh.aemeasurable]
  simp [Measure.map_dirac' hh]

lemma map_mix {n : ℕ} (Γ : Fin n → Measure K) {h : K → ℝ} (hh : Measurable h) :
    ((n : ℝ≥0∞)⁻¹ • ∑ i, Γ i).map h = (n : ℝ≥0∞)⁻¹ • ∑ i, (Γ i).map h := by
  rw [Measure.map_smul _ hh.aemeasurable, Measure.map_finset_sum' hh.aemeasurable]

/-- The groupwise plan. -/
def plan {n : ℕ} (x : Fin n → K) (Γ : Fin n → Measure K) (h : K → ℝ) : Measure (ℝ × ℝ) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, (Γ i).map (fun z => (h (x i), h z))

lemma plan_coupling {n : ℕ} (x : Fin n → K) (Γ : Fin n → Measure K)
    (hΓ : ∀ i, IsProbabilityMeasure (Γ i)) {h : K → ℝ} (hh : Measurable h) :
    IsCoupling (plan x Γ h) ((centre x).map h) (((n : ℝ≥0∞)⁻¹ • ∑ i, Γ i).map h) := by
  rw [map_centre x hh, map_mix Γ hh, plan]
  refine IsCoupling.smul ?_ _
  simp only [← Measure.sum_fintype]
  refine IsCoupling.sum fun i => ?_
  have := isCoupling_map_prodMk (h (x i)) ((Γ i).map h)
  rwa [Measure.map_map measurable_prodMk_left hh] at this

omit [MeasurableSpace K] in
lemma sq_bound {n : ℕ} (x : Fin n → K) {h : K → ℝ} {H : ℝ} (hH : ∀ z, |h z| ≤ H) (i : Fin n)
    (z : K) : 0 ≤ (h z - h (x i)) ^ 2 ∧ (h z - h (x i)) ^ 2 ≤ (2 * H) ^ 2 := by
  refine ⟨sq_nonneg _, ?_⟩
  have h1 : |h z - h (x i)| ≤ 2 * H := by
    have := abs_sub (h z) (h (x i))
    linarith [hH z, hH (x i)]
  have h2 : (h z - h (x i)) ^ 2 = |h z - h (x i)| ^ 2 := (sq_abs _).symm
  rw [h2]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

lemma integrable_sq {n : ℕ} (x : Fin n → K) {h : K → ℝ} (hh : Measurable h) {H : ℝ}
    (hH : ∀ z, |h z| ≤ H) (i : Fin n) (μ : Measure K) [IsFiniteMeasure μ] :
    Integrable (fun z => (h z - h (x i)) ^ 2) μ := by
  refine Integrable.of_bound ((hh.sub measurable_const).pow_const 2).aestronglyMeasurable
    ((2 * H) ^ 2) (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_bound x hH i z).1]
  exact (sq_bound x hH i z).2

lemma plan_lintegral {n : ℕ} (x : Fin n → K) (Γ : Fin n → Measure K)
    {h : K → ℝ} (hh : Measurable h) :
    ∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂(plan x Γ h) =
      (n : ℝ≥0∞)⁻¹ * ∑ i, ∫⁻ z, ENNReal.ofReal ((h z - h (x i)) ^ 2) ∂(Γ i) := by
  rw [plan, lintegral_smul_measure, lintegral_finsetSum_measure]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_map (by fun_prop) (measurable_const.prodMk hh)]
  congr 1
  funext z
  rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  congr 1
  rw [Real.rpow_two, sq_abs]
  ring

/-- Step 2: the groupwise coupling bound. -/
lemma group_bound {n : ℕ} (hn : 0 < n) (x : Fin n → K) (Γ : Fin n → Measure K)
    (hΓ : ∀ i, IsProbabilityMeasure (Γ i)) {h : K → ℝ} (hh : Measurable h) {H : ℝ}
    (hH : ∀ z, |h z| ≤ H) (T : ℝ)
    (hT : (n : ℝ)⁻¹ * ∑ i, ∫ z, (h z - h (x i)) ^ 2 ∂(Γ i) ≤ T) :
    wassersteinEDist 2 ((centre x).map h) (((n : ℝ≥0∞)⁻¹ • ∑ i, Γ i).map h) ≤
      ENNReal.ofReal (√T) := by
  have hd : Measurable fun z : ℝ × ℝ => edist z.1 z.2 := measurable_edist
  have h1 := wassersteinEDist_rpow_le_lintegral hd (p := 2) (by norm_num) (by norm_num)
    (plan_coupling x Γ hΓ hh)
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2, plan_lintegral x Γ hh] at h1
  have h3 : (n : ℝ≥0∞)⁻¹ * ∑ i, ∫⁻ z, ENNReal.ofReal ((h z - h (x i)) ^ 2) ∂(Γ i) =
      ENNReal.ofReal ((n : ℝ)⁻¹ * ∑ i, ∫ z, (h z - h (x i)) ^ 2 ∂(Γ i)) := by
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le), ENNReal.ofReal_inv_of_pos hpos,
      ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ofReal_integral_eq_lintegral_ofReal (integrable_sq x hh hH i (Γ i))
        (Filter.Eventually.of_forall fun z => (sq_bound x hH i z).1)]
    · intro i _
      exact integral_nonneg fun z => (sq_bound x hH i z).1
  rw [h3] at h1
  have h4 : ENNReal.ofReal T ≤ ENNReal.ofReal (√T) ^ (2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_or_gt 0 T with hT0 | hT0
    · rw [Real.sq_sqrt hT0]
    · exact hT0.le.trans (sq_nonneg _)
  have h5 := h1.trans ((ENNReal.ofReal_le_ofReal hT).trans h4)
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp h5

lemma klRef_ne_bot (Γ ν : Measure K) : StatFormal.RobustEquality.klRef Γ ν ≠ ⊥ := by
  unfold StatFormal.RobustEquality.klRef
  split_ifs
  · exact EReal.coe_ne_bot _
  · exact top_ne_bot

/-- The budget forces every KL term to be finite. -/
lemma kl_finite {n : ℕ} (hn : 0 < n) (x : Fin n → K) (c : K → K → ℝ) {ε r : ℝ} (hε : 0 < ε)
    (ν : Measure K) (Γ : Fin n → Measure K)
    (hbud : ((n : ℝ)⁻¹ : EReal) * ∑ i, (((∫ z, c (x i) z ∂(Γ i) : ℝ) : EReal) +
      (ε : EReal) * StatFormal.RobustEquality.klRef (Γ i) ν) ≤ (r : EReal)) (j : Fin n) :
    Γ j ≪ ν ∧ Integrable (llr (Γ j) ν) (Γ j) := by
  by_contra hj
  have hkj : StatFormal.RobustEquality.klRef (Γ j) ν = ⊤ := by
    unfold StatFormal.RobustEquality.klRef
    split_ifs
    rfl
  have hεE : (0 : EReal) < (ε : EReal) := by exact_mod_cast hε
  have hne : ∀ i, (((∫ z, c (x i) z ∂(Γ i) : ℝ) : EReal) +
      (ε : EReal) * StatFormal.RobustEquality.klRef (Γ i) ν) ≠ ⊥ := by
    intro i
    refine EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, ?_⟩
    unfold StatFormal.RobustEquality.klRef
    split_ifs
    · exact (EReal.coe_mul _ _ ▸ EReal.coe_ne_bot _)
    · rw [EReal.mul_top_of_pos hεE]; exact top_ne_bot
  have htop : (((∫ z, c (x j) z ∂(Γ j) : ℝ) : EReal) +
      (ε : EReal) * StatFormal.RobustEquality.klRef (Γ j) ν) = ⊤ := by
    rw [hkj, EReal.mul_top_of_pos hεE, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
  have hrest : ∑ i ∈ Finset.univ.erase j, (((∫ z, c (x i) z ∂(Γ i) : ℝ) : EReal) +
      (ε : EReal) * StatFormal.RobustEquality.klRef (Γ i) ν) ≠ ⊥ := by
    refine Finset.sum_induction _ (fun a : EReal => a ≠ ⊥) (fun a b ha hb => ?_)
      (EReal.coe_ne_bot 0) (fun i _ => hne i)
    exact EReal.add_ne_bot_iff.mpr ⟨ha, hb⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), htop, EReal.top_add_of_ne_bot hrest] at hbud
  have hnpos : (0 : EReal) < ((n : ℝ) : EReal)⁻¹ := by
    rw [← EReal.coe_inv]
    exact_mod_cast inv_pos.mpr (by exact_mod_cast hn : (0 : ℝ) < n)
  rw [EReal.mul_top_of_pos hnpos] at hbud
  exact EReal.coe_ne_top r (top_le_iff.mp hbud)

/-- Step 3: Lagrangian relaxation and Gibbs per anchor. -/
lemma lagrangian_bound {n : ℕ} (hn : 0 < n) (x : Fin n → K) (c : K → K → ℝ)
    (hc : Measurable (Function.uncurry c)) (hc0 : ∀ a b, 0 ≤ c a b) {B : ℝ} (hB : ∀ a b, c a b ≤ B)
    {h : K → ℝ} (hh : Measurable h) {H : ℝ} (hH : ∀ z, |h z| ≤ H) {ε r lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (ν : Measure K) [IsFiniteMeasure ν] (hν0 : ν Set.univ ≠ 0)
    (Γ : Fin n → Measure K) (hΓ : ∀ i, IsProbabilityMeasure (Γ i))
    (hbud : ((n : ℝ)⁻¹ : EReal) * ∑ i, (((∫ z, c (x i) z ∂(Γ i) : ℝ) : EReal) +
      (ε : EReal) * StatFormal.RobustEquality.klRef (Γ i) ν) ≤ (r : EReal)) :
    (n : ℝ)⁻¹ * ∑ i, ∫ z, (h z - h (x i)) ^ 2 ∂(Γ i) ≤ Tref1 x c h ε r lam ν := by
  have : NeZero ν := ⟨fun h0 => hν0 (by simp [h0])⟩
  have hfin := kl_finite hn x c hε ν Γ hbud
  have hcm : ∀ i, Measurable (c (x i)) := fun i =>
    hc.comp (measurable_const.prodMk measurable_id)
  have hcint : ∀ i, Integrable (c (x i)) (Γ i) := fun i =>
    Integrable.of_bound (hcm i).aestronglyMeasurable B (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hc0 _ _)]; exact hB _ _)
  set k : Fin n → ℝ := fun i => ∫ z, llr (Γ i) ν z ∂(Γ i) with hk
  set Z : Fin n → ℝ := fun i => Real.log (∫ z, Real.exp
    (((h z - h (x i)) ^ 2 - lam * c (x i) z) / (lam * ε)) ∂ν) with hZ
  set C : Fin n → ℝ := fun i => ∫ z, c (x i) z ∂(Γ i) with hC
  set F : Fin n → ℝ := fun i => ∫ z, (h z - h (x i)) ^ 2 ∂(Γ i) with hF
  have hlε : 0 < lam * ε := mul_pos hlam hε
  -- per-anchor bound
  have hper : ∀ i, F i ≤ lam * (C i + ε * k i) + lam * ε * Z i := by
    intro i
    have hgm : Measurable fun z => ((h z - h (x i)) ^ 2 - lam * c (x i) z) / (lam * ε) :=
      (((hh.sub measurable_const).pow_const 2).sub ((hcm i).const_mul lam)).div_const _
    have hgB : ∀ z, |((h z - h (x i)) ^ 2 - lam * c (x i) z) / (lam * ε)| ≤
        ((2 * H) ^ 2 + lam * B) / (lam * ε) := by
      intro z
      rw [abs_div, abs_of_pos hlε]
      refine div_le_div_of_nonneg_right ?_ hlε.le
      obtain ⟨s0, s1⟩ := sq_bound x hH i z
      have c0 := hc0 (x i) z
      have c1 := hB (x i) z
      rw [abs_le]
      constructor <;> nlinarith
    obtain ⟨hg1, -⟩ := StatFormal.RobustEquality.gibbs_finite_case ν _ hgm _ hgB (Γ i)
      (hfin i).1 (hfin i).2
    have hint : ∫ z, ((h z - h (x i)) ^ 2 - lam * c (x i) z) / (lam * ε) ∂(Γ i) =
        (F i - lam * C i) / (lam * ε) := by
      rw [integral_div, integral_sub (integrable_sq x hh hH i (Γ i)) ((hcint i).const_mul lam),
        integral_const_mul]
    rw [hint] at hg1
    have := (div_le_iff₀ hlε).mp (by linarith : (F i - lam * C i) / (lam * ε) ≤ k i + Z i)
    simp only [hk, hZ, hC, hF] at this ⊢
    nlinarith
  -- budget in reals
  have hbudR : (n : ℝ)⁻¹ * ∑ i, (C i + ε * k i) ≤ r := by
    have hkl : ∀ i, StatFormal.RobustEquality.klRef (Γ i) ν = ((k i : ℝ) : EReal) := by
      intro i
      unfold StatFormal.RobustEquality.klRef
      rw [ite_eq_left (hfin i)]
    simp only [hkl] at hbud
    have hsum : ∑ i, (((C i : ℝ) : EReal) + (ε : EReal) * ((k i : ℝ) : EReal)) =
        ((∑ i, (C i + ε * k i) : ℝ) : EReal) := by
      have := map_sum Real.toERealAddHom (fun i => C i + ε * k i) Finset.univ
      simp only [Real.coe_toERealAddHom] at this
      rw [this]
      simp only [EReal.coe_add, EReal.coe_mul]
    have hbud' : ((n : ℝ) : EReal)⁻¹ * ((∑ i, (C i + ε * k i) : ℝ) : EReal) ≤ (r : EReal) := by
      rw [← hsum]; exact hbud
    rw [← EReal.coe_inv, ← EReal.coe_mul] at hbud'
    exact_mod_cast hbud'
  have hnpos : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hn)
  calc (n : ℝ)⁻¹ * ∑ i, F i
      ≤ (n : ℝ)⁻¹ * ∑ i, (lam * (C i + ε * k i) + lam * ε * Z i) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hper i) hnpos.le
    _ = lam * ((n : ℝ)⁻¹ * ∑ i, (C i + ε * k i)) + lam * ε * ((n : ℝ)⁻¹ * ∑ i, Z i) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
    _ ≤ lam * r + lam * ε * ((n : ℝ)⁻¹ * ∑ i, Z i) := by
        gcongr
    _ = Tref1 x c h ε r lam ν := rfl

/-- Steps 2–4 for one group: `W₂(h#P̂, h#Q) ≤ √T`. -/
lemma group_W_le {n : ℕ} (hn : 0 < n) (x : Fin n → K) (c : K → K → ℝ)
    (hc : Measurable (Function.uncurry c)) (hc0 : ∀ a b, 0 ≤ c a b) {B : ℝ} (hB : ∀ a b, c a b ≤ B)
    {h : K → ℝ} (hh : Measurable h) {H : ℝ} (hH : ∀ z, |h z| ≤ H) {ε r lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (ν Q : Measure K) [IsFiniteMeasure ν] (hν0 : ν Set.univ ≠ 0)
    (hW : KernelWitness x c ε r ν Q) :
    wassersteinEDist 2 ((centre x).map h) (Q.map h) ≤
      ENNReal.ofReal (√(Tref1 x c h ε r lam ν)) := by
  obtain ⟨Γ, hΓ, hQ, hbud⟩ := hW
  rw [hQ]
  exact group_bound hn x Γ hΓ hh hH _
    (lagrangian_bound hn x c hc hc0 hB hh hH hε hlam ν hν0 Γ hΓ hbud)

theorem certificate : Claims.certificate := by
  intro K _ n₀ n₁ x₀ x₁ c ε r₀ r₁ lam₀ lam₁ h ν₀ ν₁ Q₀ Q₁ _ _ _ _ hn₀ hn₁ hε hl₀ hl₁ hc hc0
    ⟨B, hB⟩ hh ⟨H, hH⟩ hν₀0 _ hν₁0 _ hW₀ hW₁
  have hd : Measurable fun z : ℝ × ℝ => edist z.1 z.2 := measurable_edist
  have g₀ := group_W_le hn₀ x₀ c hc hc0 hB hh hH hε hl₀ ν₀ Q₀ hν₀0 hW₀
  have g₁ := group_W_le hn₁ x₁ c hc hc0 hB hh hH hε hl₁ ν₁ Q₁ hν₁0 hW₁
  have := centre_isProb hn₀ x₀
  have := centre_isProb hn₁ x₁
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  calc wassersteinEDist 2 (Q₀.map h) (Q₁.map h)
      ≤ wassersteinEDist 2 (Q₀.map h) ((centre x₀).map h) +
          wassersteinEDist 2 ((centre x₀).map h) (Q₁.map h) :=
        wassersteinEDist_triangle hd hp _ _ _
    _ ≤ wassersteinEDist 2 (Q₀.map h) ((centre x₀).map h) +
          (wassersteinEDist 2 ((centre x₀).map h) ((centre x₁).map h) +
            wassersteinEDist 2 ((centre x₁).map h) (Q₁.map h)) := by
        gcongr
        exact wassersteinEDist_triangle hd hp _ _ _
    _ ≤ ENNReal.ofReal (√(Tref1 x₀ c h ε r₀ lam₀ ν₀)) +
          (wassersteinEDist 2 ((centre x₀).map h) ((centre x₁).map h) +
            ENNReal.ofReal (√(Tref1 x₁ c h ε r₁ lam₁ ν₁))) := by
        gcongr
        rw [wassersteinEDist_comm hd]
        exact g₀
    _ = _ := by ring

theorem uniform : Claims.uniform := by
  intro K Ω _ _ P _ n₀ n₁ x₀ x₁ c ε α r₀ r₁ ν₀ ν₁ P₀ P₁ _ _ E₀ E₁ hn₀ hn₁ hε hα0 hα1 hc hc0 hcB
    hν₀ hν₁ hE₀ hE₁ hP₀ hP₁ hw₀ hw₁
  have hsub : E₀ ∩ E₁ ⊆ {ω | ∀ (h : K → ℝ) (lam₀ lam₁ : ℝ), Measurable h →
      (∃ H, ∀ z, |h z| ≤ H) → 0 < lam₀ → 0 < lam₁ →
        wassersteinEDist 2 (P₀.map h) (P₁.map h) ≤
          wassersteinEDist 2 ((centre (x₀ ω)).map h) ((centre (x₁ ω)).map h) +
            ENNReal.ofReal (√(Tref1 (x₀ ω) c h ε (r₀ ω) lam₀ (ν₀ ω))) +
            ENNReal.ofReal (√(Tref1 (x₁ ω) c h ε (r₁ ω) lam₁ (ν₁ ω)))} := by
    rintro ω ⟨h0, h1⟩ hf lam₀ lam₁ hh hH hl₀ hl₁
    obtain ⟨i0, a0, b0⟩ := hν₀ ω
    obtain ⟨i1, a1, b1⟩ := hν₁ ω
    have := i0
    have := i1
    exact certificate K n₀ n₁ (x₀ ω) (x₁ ω) c ε (r₀ ω) (r₁ ω) lam₀ lam₁ hf (ν₀ ω) (ν₁ ω) P₀ P₁
      hn₀ hn₁ hε hl₀ hl₁ hc hc0 hcB hh hH a0 b0 a1 b1 (hw₀ ω h0) (hw₁ ω h1)
  refine le_trans ?_ (measure_mono hsub)
  have hu := measure_union_add_inter (μ := P) E₀ hE₁
  have hle : P (E₀ ∪ E₁) ≤ 1 := prob_le_one
  have key : ENNReal.ofReal (1 - α / 2) + ENNReal.ofReal (1 - α / 2) =
      1 + ENNReal.ofReal (1 - α) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by norm_num) (by linarith)]
    congr 1
    ring
  have h2 : 1 + ENNReal.ofReal (1 - α) ≤ 1 + P (E₀ ∩ E₁) := by
    rw [← key]
    calc ENNReal.ofReal (1 - α / 2) + ENNReal.ofReal (1 - α / 2) ≤ P E₀ + P E₁ :=
          add_le_add hP₀ hP₁
      _ = P (E₀ ∪ E₁) + P (E₀ ∩ E₁) := hu.symm
      _ ≤ 1 + P (E₀ ∩ E₁) := by gcongr
  exact (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp h2

example : Claims.certificate := certificate
example : Claims.uniform := uniform

end StatFormal.RobustEquality.Certificate
