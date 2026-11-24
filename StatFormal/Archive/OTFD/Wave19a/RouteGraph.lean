import StatFormal.Archive.OTFD.Wave19a.Statements
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Route: A `lem:app-graph-barycenter`, `lem:app-graph-empirical`; T `lem:graph` (untrusted)

* Approximation (replaces Lusin + Tietze): for Borel `Q` and finite `μ`, bounded continuous `g` make
  `∫ min(1, ‖Q − g‖) dμ` small (truncate `Q`, then density of `C_b` in `L¹`, Mathlib).
* In probability: `1{‖y − Q(u)‖ > γ} ≤ min(1, (2/γ)‖y − g(u)‖) + min(1,‖g(u) − Q(u)‖)/min(1,γ/2)`; the first
  term is a bounded continuous test function, the second depends on `u` only (fixed first marginal, or the strong
  law for countably many `g_k`).
* Integrals: `‖y − Q(u)‖² ≤ γ² + M·1{‖y−Q(u)‖>γ} + ‖y−Q(u)‖²1{‖y−Q(u)‖² > M}`.
* Barycentres: pointwise `‖∫ y dκ_x − Q(x)‖² ≤ ∫⁻ ‖y − Q(x)‖² dκ_x` in `ℝ≥0∞` (also when `y` is not integrable),
  integrated against the disintegration.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace StatFormal.OTFD.Wave19a

section Core
variable {X E : Type*} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- `ψ_g(x) = min(1, ‖Q(x) − g(x)‖)`. -/
def psiG (Q : X → E) (g : X →ᵇ E) (x : X) : ℝ≥0∞ := min 1 ‖Q x - g x‖ₑ

lemma measurable_psiG {Q : X → E} (hQ : Measurable Q) (g : X →ᵇ E) : Measurable (psiG Q g) := by
  unfold psiG
  exact measurable_const.min ((hQ.sub g.continuous.measurable).enorm)

lemma psiG_le_one (Q : X → E) (g : X →ᵇ E) (x : X) : psiG Q g x ≤ 1 := min_le_left _ _

/-- Approximation in measure by bounded continuous maps. -/
lemma exists_bcf_psiG (μ : Measure X) [IsFiniteMeasure μ] {Q : X → E} (hQ : Measurable Q) {δ : ℝ≥0∞}
    (hδ : δ ≠ 0) : ∃ g : X →ᵇ E, ∫⁻ x, psiG Q g x ∂μ ≤ δ := by
  have hδ2 : δ / 2 ≠ 0 := by simpa using hδ
  -- tails of `‖Q‖`
  have htail : Tendsto (fun n : ℕ => μ {x | (n : ℝ) < ‖Q x‖}) atTop (𝓝 0) := by
    have hanti : Antitone fun n : ℕ => {x | (n : ℝ) < ‖Q x‖} := by
      intro m n hmn x hx
      simp only [mem_setOf_eq] at hx ⊢
      exact lt_of_le_of_lt (by exact_mod_cast hmn) hx
    have h0 : ⋂ n : ℕ, {x | (n : ℝ) < ‖Q x‖} = ∅ := by
      ext x
      simp only [mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨n, hn⟩ := exists_nat_ge ‖Q x‖
      exact ⟨n, hn⟩
    have := tendsto_measure_iInter_atTop (μ := μ)
      (fun n => (measurableSet_lt measurable_const hQ.norm).nullMeasurableSet) hanti
      ⟨0, measure_ne_top μ _⟩
    rwa [h0, measure_empty] at this
  obtain ⟨N, hN⟩ := (((tendsto_order.1 htail).2 (δ / 2) (pos_iff_ne_zero.2 hδ2)).exists)
  set A := {x | (N : ℝ) < ‖Q x‖} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hQ.norm
  set QN : X → E := Aᶜ.indicator Q
  have hQN : Integrable QN μ := by
    refine Integrable.of_bound ((hQ.indicator hAm.compl).aestronglyMeasurable) N
      (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ A
    · simp [QN, hx]
    · simp only [QN, indicator_of_mem (show x ∈ Aᶜ from hx)]
      simpa [hA] using hx
  obtain ⟨g, hg, -⟩ := hQN.exists_boundedContinuous_lintegral_sub_le hδ2
  refine ⟨g, ?_⟩
  have hpt : ∀ x, psiG Q g x ≤ ‖QN x - g x‖ₑ + A.indicator 1 x := by
    intro x
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      exact (psiG_le_one Q g x).trans (le_add_left le_rfl)
    · have : QN x = Q x := by simp [QN, indicator_of_mem (show x ∈ Aᶜ from hx)]
      rw [this]
      exact (min_le_right _ _).trans le_self_add
  calc ∫⁻ x, psiG Q g x ∂μ ≤ ∫⁻ x, (‖QN x - g x‖ₑ + A.indicator 1 x) ∂μ := lintegral_mono hpt
    _ = ∫⁻ x, ‖QN x - g x‖ₑ ∂μ + ∫⁻ x, A.indicator 1 x ∂μ := by
        rw [lintegral_add_right _ (measurable_one.indicator hAm)]
    _ ≤ δ / 2 + δ / 2 := by
        gcongr
        rw [lintegral_indicator_one hAm]; exact hN.le
    _ = δ := ENNReal.add_halves δ

/-- A sequence of approximations with `∫ ψ_{g_k} dμ ≤ 1/(k+1)`. -/
lemma exists_bcf_seq (μ : Measure X) [IsFiniteMeasure μ] {Q : X → E} (hQ : Measurable Q) :
    ∃ g : ℕ → X →ᵇ E, Tendsto (fun k => ∫⁻ x, psiG Q (g k) x ∂μ) atTop (𝓝 0) := by
  choose g hg using fun k : ℕ => exists_bcf_psiG μ hQ (δ := ((k : ℝ≥0∞) + 1)⁻¹) (by simp)
  have ht : Tendsto (fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.cast_add] using this
  exact ⟨g, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le) hg⟩

/-- The test function `min(1, a‖y − g(x)‖)`, `a ≥ 0`. -/
def testH (g : X →ᵇ E) {a : ℝ} (ha : 0 ≤ a) : X × E →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => min 1 (a * ‖z.2 - g z.1‖), by
      exact continuous_const.min (continuous_const.mul
        ((continuous_snd.sub (g.continuous.comp continuous_fst)).norm))⟩ 1
    (by
      intro z w
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 : 0 ≤ min 1 (a * ‖z.2 - g z.1‖) := le_min zero_le_one (by positivity)
      have h2 : 0 ≤ min 1 (a * ‖w.2 - g w.1‖) := le_min zero_le_one (by positivity)
      have h3 := min_le_left 1 (a * ‖z.2 - g z.1‖)
      have h4 := min_le_left 1 (a * ‖w.2 - g w.1‖)
      rw [abs_le]; constructor <;> linarith)

lemma testH_apply (g : X →ᵇ E) {a : ℝ} (ha : 0 ≤ a) (z : X × E) :
    testH g ha z = min 1 (a * ‖z.2 - g z.1‖) := rfl

lemma testH_nonneg (g : X →ᵇ E) {a : ℝ} (ha : 0 ≤ a) (z : X × E) : 0 ≤ testH g ha z := by
  rw [testH_apply]; exact le_min zero_le_one (by positivity)

/-- `min(1, a t) ≤ max(1, a) min(1, t)`. -/
lemma min_mul_le (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) : min 1 (a * t) ≤ max 1 a * min 1 t := by
  rcases le_total t 1 with h | h
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ht)
  · rw [min_eq_left h, mul_one]; exact (min_le_left _ _).trans (le_max_left _ _)

/-- Pointwise bound of the bad-event indicator. -/
lemma indicator_bad_le (Q : X → E) (g : X →ᵇ E) {γ : ℝ} (hγ : 0 < γ) (z : X × E) :
    {z : X × E | γ < ‖z.2 - Q z.1‖}.indicator 1 z ≤
      ENNReal.ofReal (testH g (a := 2 / γ) (by positivity) z) +
        (ENNReal.ofReal (min 1 (γ / 2)))⁻¹ * psiG Q g z.1 := by
  by_cases hz : γ < ‖z.2 - Q z.1‖
  · rw [indicator_of_mem (show z ∈ {z : X × E | γ < ‖z.2 - Q z.1‖} from hz), Pi.one_apply]
    have htri : ‖z.2 - Q z.1‖ ≤ ‖z.2 - g z.1‖ + ‖g z.1 - Q z.1‖ := by
      calc ‖z.2 - Q z.1‖ = ‖(z.2 - g z.1) + (g z.1 - Q z.1)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    rcases le_or_gt (γ / 2) ‖z.2 - g z.1‖ with h | h
    · refine le_add_right ?_
      rw [testH_apply, min_eq_left, ENNReal.ofReal_one]
      calc (1 : ℝ) = 2 / γ * (γ / 2) := by field_simp
        _ ≤ 2 / γ * ‖z.2 - g z.1‖ := by gcongr
    · refine le_add_left ?_
      have hc : 0 < min 1 (γ / 2) := lt_min one_pos (by positivity)
      have hpsi : ENNReal.ofReal (min 1 (γ / 2)) ≤ psiG Q g z.1 := by
        unfold psiG
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_one, ← ENNReal.ofReal_min]
        refine ENNReal.ofReal_le_ofReal (min_le_min le_rfl ?_)
        rw [norm_sub_rev]; linarith
      calc (1 : ℝ≥0∞) = (ENNReal.ofReal (min 1 (γ / 2)))⁻¹ * ENNReal.ofReal (min 1 (γ / 2)) :=
            (ENNReal.inv_mul_cancel (by simpa using hc) ENNReal.ofReal_ne_top).symm
        _ ≤ _ := by gcongr
  · rw [indicator_of_notMem (show z ∉ {z : X × E | γ < ‖z.2 - Q z.1‖} from hz)]; exact zero_le'

lemma measurableSet_bad {Q : X → E} (hQ : Measurable Q) (γ : ℝ) :
    MeasurableSet {z : X × E | γ < ‖z.2 - Q z.1‖} :=
  measurableSet_lt measurable_const ((measurable_snd.sub (hQ.comp measurable_fst)).norm)

lemma measurable_sqDisc {Q : X → E} (hQ : Measurable Q) : Measurable (sqDisc Q) := by
  unfold sqDisc; exact ((measurable_snd.sub (hQ.comp measurable_fst)).enorm).pow_const 2

/-- **In probability**, for a general filter and varying first marginals controlled on the `ψ_{g_k}`. -/
theorem tendsto_bad {ι : Type*} {l : Filter ι} (μ : Measure X) [IsProbabilityMeasure μ] {Q : X → E}
    (hQ : Measurable Q) (Γ : ι → Measure (X × E)) (hΓ : ∀ i, IsFiniteMeasure (Γ i))
    (hw : WeakTo l Γ (graphLaw μ Q)) (g : ℕ → X →ᵇ E)
    (hg : Tendsto (fun k => ∫⁻ x, psiG Q (g k) x ∂μ) atTop (𝓝 0))
    (hmarg : ∀ k, Tendsto (fun i => ∫⁻ x, psiG Q (g k) x ∂((Γ i).map Prod.fst)) l
      (𝓝 (∫⁻ x, psiG Q (g k) x ∂μ)))
    {γ : ℝ} (hγ : 0 < γ) : Tendsto (fun i => Γ i {z | γ < ‖z.2 - Q z.1‖}) l (𝓝 0) := by
  have ha : (0 : ℝ) ≤ 2 / γ := by positivity
  set c := ENNReal.ofReal (min 1 (γ / 2)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; simpa using lt_min one_pos (by positivity : (0 : ℝ) < γ / 2)
  set C := ENNReal.ofReal (max 1 (2 / γ)) + c⁻¹ with hC
  have hCt : C ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.2 hc0⟩
  have hgraph : Measurable fun x : X => (x, Q x) := measurable_id.prodMk hQ
  haveI : IsProbabilityMeasure (graphLaw μ Q) := by unfold graphLaw; infer_instance
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨k, hk⟩ := ((tendsto_order.1 (ENNReal.Tendsto.const_mul hg (Or.inr hCt))).2 ε
    (by simpa using hε)).exists
  set h := testH (g k) ha
  have hlim : Tendsto (fun i => ENNReal.ofReal (∫ z, h z ∂(Γ i)) +
      c⁻¹ * ∫⁻ x, psiG Q (g k) x ∂((Γ i).map Prod.fst)) l
      (𝓝 (ENNReal.ofReal (∫ z, h z ∂(graphLaw μ Q)) + c⁻¹ * ∫⁻ x, psiG Q (g k) x ∂μ)) :=
    ((ENNReal.continuous_ofReal.tendsto _).comp (hw h)).add
      (ENNReal.Tendsto.const_mul (hmarg k) (Or.inr (ENNReal.inv_ne_top.2 hc0)))
  have hU : ENNReal.ofReal (∫ z, h z ∂(graphLaw μ Q)) + c⁻¹ * ∫⁻ x, psiG Q (g k) x ∂μ ≤
      C * ∫⁻ x, psiG Q (g k) x ∂μ := by
    rw [hC, add_mul]
    gcongr
    rw [ofReal_integral_eq_lintegral_ofReal (h.integrable _)
      (Eventually.of_forall fun z => testH_nonneg (g k) ha z), graphLaw,
      lintegral_map (f := fun z => ENNReal.ofReal (h z)) (ENNReal.measurable_ofReal.comp h.continuous.measurable) hgraph,
      ← lintegral_const_mul _ (measurable_psiG hQ (g k))]
    refine lintegral_mono fun x => ?_
    simp only [Function.comp, h, testH_apply]
    unfold psiG
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_one, ← ENNReal.ofReal_min, ← ENNReal.ofReal_mul
      (le_trans zero_le_one (le_max_left _ _)), norm_sub_rev]
    exact ENNReal.ofReal_le_ofReal (min_mul_le _ _ ha (norm_nonneg _))
  have hev := (tendsto_order.1 hlim).2 ε (lt_of_le_of_lt hU hk)
  filter_upwards [hev] with i hi
  refine le_of_lt (lt_of_le_of_lt ?_ hi)
  haveI := hΓ i
  rw [← lintegral_indicator_one (measurableSet_bad hQ γ)]
  calc ∫⁻ z, {z : X × E | γ < ‖z.2 - Q z.1‖}.indicator 1 z ∂(Γ i)
      ≤ ∫⁻ z, (ENNReal.ofReal (h z) + c⁻¹ * psiG Q (g k) z.1) ∂(Γ i) :=
        lintegral_mono fun z => indicator_bad_le Q (g k) hγ z
    _ = ∫⁻ z, ENNReal.ofReal (h z) ∂(Γ i) + c⁻¹ * ∫⁻ z, psiG Q (g k) z.1 ∂(Γ i) := by
        rw [lintegral_add_right _ (show Measurable fun z : X × E => c⁻¹ * psiG Q (g k) z.1 from
            ((measurable_psiG hQ (g k)).comp measurable_fst).const_mul _),
          lintegral_const_mul _ (show Measurable fun z : X × E => psiG Q (g k) z.1 from
            (measurable_psiG hQ (g k)).comp measurable_fst)]
    _ = _ := by
        rw [ofReal_integral_eq_lintegral_ofReal (h.integrable _)
          (Eventually.of_forall fun z => testH_nonneg (g k) ha z),
          lintegral_map (measurable_psiG hQ (g k)) measurable_fst]

/-- Integrals from in-probability convergence and uniform integrability. -/
theorem tendsto_lintegral_sqDisc {ι : Type*} {l : Filter ι} {Q : X → E} (hQ : Measurable Q)
    (Γ : ι → Measure (X × E)) (hΓ : ∀ i, Γ i univ ≤ 1)
    (hbad : ∀ γ : ℝ, 0 < γ → Tendsto (fun i => Γ i {z | γ < ‖z.2 - Q z.1‖}) l (𝓝 0))
    (hUI : ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
      ∀ i, ∫⁻ z in {z | M < sqDisc Q z}, sqDisc Q z ∂(Γ i) ≤ ε) :
    Tendsto (fun i => ∫⁻ z, sqDisc Q z ∂(Γ i)) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  set η := ε' / 2 with hη
  have hη0 : 0 < η := by simp [hη, hε'0.ne']
  have hηt : η ≠ ⊤ := ENNReal.div_ne_top hε'1 two_ne_zero
  obtain ⟨M, hMt, hM⟩ := hUI (ε' / 2) (by simp [hε'0.ne'])
  set γ := Real.sqrt (η.toReal / 2) with hγ
  have hηr : 0 < η.toReal := ENNReal.toReal_pos hη0.ne' hηt
  have hγ0 : 0 < γ := Real.sqrt_pos.2 (by linarith)
  have hγsq : ENNReal.ofReal (γ ^ 2) ≤ η / 2 := by
    rw [hγ, Real.sq_sqrt (by linarith), ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_toReal hηt]
    simp
  have hlimM : Tendsto (fun i => M * Γ i {z | γ < ‖z.2 - Q z.1‖}) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (hbad γ hγ0) (Or.inr hMt)
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hlimM) (η / 2) (by simp [hη0.ne', hηt])] with i hi
  have hpt : ∀ z, sqDisc Q z ≤ {z | M < sqDisc Q z}.indicator (sqDisc Q) z +
      (ENNReal.ofReal (γ ^ 2) + M * {z : X × E | γ < ‖z.2 - Q z.1‖}.indicator 1 z) := by
    intro z
    by_cases h1 : M < sqDisc Q z
    · rw [indicator_of_mem (show z ∈ {z | M < sqDisc Q z} from h1)]; exact le_self_add
    · rw [indicator_of_notMem (show z ∉ {z | M < sqDisc Q z} from h1), zero_add]
      push_neg at h1
      by_cases h2 : γ < ‖z.2 - Q z.1‖
      · rw [indicator_of_mem (show z ∈ {z : X × E | γ < ‖z.2 - Q z.1‖} from h2), Pi.one_apply, mul_one]
        exact h1.trans le_add_self
      · push_neg at h2
        refine le_add_right ?_
        unfold sqDisc
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h2 2)
  have hmS : MeasurableSet {z | M < sqDisc Q z} := measurableSet_lt measurable_const (measurable_sqDisc hQ)
  calc ∫⁻ z, sqDisc Q z ∂(Γ i)
      ≤ ∫⁻ z, ({z | M < sqDisc Q z}.indicator (sqDisc Q) z +
          (ENNReal.ofReal (γ ^ 2) + M * {z : X × E | γ < ‖z.2 - Q z.1‖}.indicator 1 z)) ∂(Γ i) :=
        lintegral_mono hpt
    _ = ∫⁻ z in {z | M < sqDisc Q z}, sqDisc Q z ∂(Γ i) +
          (ENNReal.ofReal (γ ^ 2) * Γ i univ + M * Γ i {z | γ < ‖z.2 - Q z.1‖}) := by
        rw [lintegral_add_left ((measurable_sqDisc hQ).indicator hmS), lintegral_indicator hmS,
          lintegral_add_left measurable_const, lintegral_const,
          lintegral_const_mul _ (measurable_one.indicator (measurableSet_bad hQ γ)),
          lintegral_indicator_one (measurableSet_bad hQ γ)]
    _ ≤ ε' / 2 + (η / 2 * 1 + η / 2) := by
        gcongr
        · exact hM i
        · exact hΓ i
    _ = ε' := by rw [mul_one, ENNReal.add_halves, hη, ENNReal.add_halves]
    _ ≤ ε := min_le_left _ _

/-- A uniform a.e. bound gives uniform integrability. -/
lemma ui_of_ae_le {ι : Type*} {Q : X → E} (hQ : Measurable Q) (Γ : ι → Measure (X × E)) {M : ℝ≥0∞}
    (hMt : M ≠ ⊤) (hM : ∀ i, ∀ᵐ z ∂(Γ i), sqDisc Q z ≤ M) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
      ∀ i, ∫⁻ z in {z | M < sqDisc Q z}, sqDisc Q z ∂(Γ i) ≤ ε := by
  intro ε _
  refine ⟨M, hMt, fun i => ?_⟩
  have h0 : Γ i {z | M < sqDisc Q z} = 0 := by
    have := ae_iff.1 (hM i); simpa [not_le] using this
  rw [setLIntegral_measure_zero _ _ h0]; exact zero_le'

end Core

section Jensen

lemma sq_lintegral_le {Ω : Type*} [MeasurableSpace Ω] (m : Measure Ω) [IsProbabilityMeasure m]
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f m) : (∫⁻ x, f x ∂m) ^ 2 ≤ ∫⁻ x, f x ^ 2 ∂m := by
  have h := eLpNorm_le_eLpNorm_of_exponent_le (f := f) (μ := m) (p := 1) (q := ((2 : NNReal) : ℝ≥0∞))
    (by norm_num)
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    eLpNorm_nnreal_eq_lintegral (by norm_num) hf.aestronglyMeasurable] at h
  simp only [enorm_eq_self, NNReal.coe_ofNat] at h
  calc (∫⁻ x, f x ∂m) ^ 2 ≤ ((∫⁻ x, f x ^ (2 : ℝ) ∂m) ^ (1 / (2 : ℝ))) ^ 2 := pow_le_pow_left₀ zero_le' h 2
    _ = ∫⁻ x, f x ^ (2 : ℝ) ∂m := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    _ = ∫⁻ x, f x ^ 2 ∂m := by simp_rw [ENNReal.rpow_two]

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- Pointwise conditional Jensen in `ℝ≥0∞` (valid also when `y` is not `m`-integrable). -/
lemma enorm_integral_sub_sq_le (m : Measure E) [IsProbabilityMeasure m] (c : E) :
    ‖(∫ y, y ∂m) - c‖ₑ ^ 2 ≤ ∫⁻ y, ‖y - c‖ₑ ^ 2 ∂m := by
  have hm : AEMeasurable (fun y : E => ‖y - c‖ₑ) m := (measurable_id.sub_const c).enorm.aemeasurable
  refine le_trans ?_ (sq_lintegral_le m hm)
  gcongr
  by_cases hint : Integrable (fun y : E => y) m
  · have : (∫ y, y ∂m) - c = ∫ y, (y - c) ∂m := by
      rw [integral_sub hint (integrable_const c)]; simp
    rw [this]; exact enorm_integral_le_lintegral_enorm _
  · have htop : ∫⁻ y, ‖y - c‖ₑ ∂m = ⊤ := by
      by_contra hne
      apply hint
      refine ⟨aestronglyMeasurable_id, ?_⟩
      have : ∫⁻ y, ‖y‖ₑ ∂m ≤ ∫⁻ y, (‖y - c‖ₑ + ‖c‖ₑ) ∂m := lintegral_mono fun y => by
        calc ‖y‖ₑ = ‖(y - c) + c‖ₑ := by rw [sub_add_cancel]
          _ ≤ _ := enorm_add_le _ _
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one] at this
      exact lt_of_le_of_lt this (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hne, enorm_lt_top⟩)
    rw [htop]; exact le_top

/-- Integrated conditional Jensen against a disintegration `ν ⊗ κ`. -/
lemma lintegral_bary_le (ν : Measure X) [SFinite ν] (κ : Kernel X E) [IsMarkovKernel κ] {F : X → E}
    (hF : Measurable F) :
    ∫⁻ x, ‖bary κ x - F x‖ₑ ^ 2 ∂ν ≤ ∫⁻ z, sqDisc F z ∂(ν ⊗ₘ κ) := by
  rw [Measure.lintegral_compProd (by
    unfold sqDisc; exact ((measurable_snd.sub (hF.comp measurable_fst)).enorm).pow_const 2)]
  exact lintegral_mono fun x => enorm_integral_sub_sq_le (κ x) (F x)

end Jensen


section Claims
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

lemma ae_snd_mem (π : Measure (X × E)) [IsProbabilityMeasure π] {C : Set E} (hC : MeasurableSet C)
    (h : (π.map Prod.snd) C = 1) : ∀ᵐ z ∂π, z.2 ∈ C :=
  ae_of_ae_map measurable_snd.aemeasurable ((mem_ae_iff_prob_eq_one hC).2 h)

lemma sqDisc_le_of_mem {F : X → E} {R : ℝ} {z : X × E} (h2 : ‖z.2‖ ≤ R) (h1 : ‖F z.1‖ ≤ R) :
    sqDisc F z ≤ ENNReal.ofReal ((2 * R) ^ 2) := by
  unfold sqDisc
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
  calc ‖z.2 - F z.1‖ ≤ ‖z.2‖ + ‖F z.1‖ := norm_sub_le _ _
    _ ≤ 2 * R := by linarith

end Claims

/-! ### A `lem:app-graph-barycenter` -/

theorem app_graph_barycenter : Claims.app_graph_barycenter := by
  intro K P0 _ C γ Qq κ _ F hC hF hFC hγ hsnd hQC hw
  have hprob : ∀ q, IsProbabilityMeasure (γ q) := fun q => by rw [hγ q]; infer_instance
  have hfst : ∀ q, (γ q).map Prod.fst = P0 := fun q => by
    rw [hγ q]; exact Measure.fst_compProd P0 (κ q)
  obtain ⟨g, hg⟩ := exists_bcf_seq P0 hF
  have hbad : ∀ r : ℝ, 0 < r → Tendsto (fun q => γ q {z | r < ‖z.2 - F z.1‖}) atTop (𝓝 0) :=
    fun r hr => tendsto_bad P0 hF γ (fun q => inferInstance) hw g hg
      (fun k => by simp only [hfst]; exact tendsto_const_nhds) hr
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hC.isBounded
  have hae : ∀ q, ∀ᵐ z ∂(γ q), sqDisc F z ≤ ENNReal.ofReal ((2 * R) ^ 2) := fun q => by
    filter_upwards [ae_snd_mem (γ q) hC.measurableSet (by rw [hsnd q]; exact hQC q)] with z hz
    exact sqDisc_le_of_mem (hR _ hz) (hR _ (hFC _))
  have hint := tendsto_lintegral_sqDisc hF γ (fun q => prob_le_one) hbad
    (ui_of_ae_le hF γ ENNReal.ofReal_ne_top hae)
  refine ⟨hint, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hint (fun _ => zero_le')
    fun q => ?_⟩
  rw [hγ q]; exact lintegral_bary_le P0 (κ q) hF

theorem app_graph_barycenter_family : Claims.app_graph_barycenter_family := by
  intro K ι l _ P0 _ C γ Qt κ _ F hC hF hFC hγ hsnd hQC hw
  have key : ∀ s : ℕ → ι, Tendsto s atTop l →
      Tendsto (fun q => ∫⁻ z, sqDisc F z ∂(γ (s q))) atTop (𝓝 0) ∧
        Tendsto (fun q => ∫⁻ x, ‖bary (κ (s q)) x - F x‖ₑ ^ 2 ∂P0) atTop (𝓝 0) := fun s hs =>
    @app_graph_barycenter K P0 _ C (γ ∘ s) (Qt ∘ s) (κ ∘ s) (fun q => inferInstanceAs (IsMarkovKernel (κ (s q))))
      F hC hF hFC (fun q => hγ (s q)) (fun q => hsnd (s q)) (fun q => hQC (s q)) (hw s hs)
  exact ⟨tendsto_of_seq_tendsto fun s hs => (key s hs).1, tendsto_of_seq_tendsto fun s hs => (key s hs).2⟩

/-! ### T `lem:graph` -/

section T
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

lemma coupling_fst {μ ν : Measure H} {Γ : Measure (H × H)} (h : TauCeti.IsCoupling Γ μ ν) :
    Γ.map Prod.fst = μ := h.fst_eq

lemma coupling_prob {μ ν : Measure H} [IsProbabilityMeasure μ] {Γ : Measure (H × H)}
    (h : TauCeti.IsCoupling Γ μ ν) : IsProbabilityMeasure Γ :=
  ⟨by rw [← Measure.fst_univ, h.fst_eq, measure_univ]⟩

lemma graph_bad (μ : Measure H) [IsProbabilityMeasure μ] (ν : ℕ → Measure H) (Γ : ℕ → Measure (H × H))
    {Q : H → H} (hQ : Measurable Q) (hc : ∀ n, TauCeti.IsCoupling (Γ n) μ (ν n))
    (hw : WeakTo atTop Γ (graphLaw μ Q)) :
    ∀ r : ℝ, 0 < r → Tendsto (fun n => Γ n {z | r < ‖z.2 - Q z.1‖}) atTop (𝓝 0) := by
  obtain ⟨g, hg⟩ := exists_bcf_seq μ hQ
  intro r hr
  have := fun n => coupling_prob (hc n)
  exact tendsto_bad μ hQ Γ (fun n => inferInstance) hw g hg
    (fun k => by simp only [fun n => coupling_fst (hc n)]; exact tendsto_const_nhds) hr

end T

theorem graphprob : Claims.graphprob := by
  intro H _ _ _ _ _ _ μ _ ν Γ Q hQ hc hw r hr
  exact ⟨measurableSet_bad hQ r, graph_bad μ ν Γ hQ hc hw r hr⟩

theorem graph_ui : Claims.graph_ui := by
  intro H _ _ _ _ _ _ μ _ ν Γ Q hQ hc hw hUI
  have := fun n => coupling_prob (hc n)
  exact tendsto_lintegral_sqDisc hQ Γ (fun n => prob_le_one) (graph_bad μ ν Γ hQ hc hw) hUI

theorem graph_bounded : Claims.graph_bounded := by
  intro H _ _ _ _ _ _ μ _ ν Γ Q B hQ hc hw hy hQB
  have hae : ∀ n, ∀ᵐ z ∂(Γ n), sqDisc Q z ≤ ENNReal.ofReal ((2 * B) ^ 2) := fun n => by
    have h1 : ∀ᵐ z ∂(Γ n), ‖Q z.1‖ ≤ B :=
      ae_of_ae_map measurable_fst.aemeasurable (by rw [coupling_fst (hc n)]; exact hQB)
    filter_upwards [hy n, h1] with z hz1 hz2
    exact sqDisc_le_of_mem hz1 hz2
  have hUI : SqUI Γ Q := ui_of_ae_le hQ Γ ENNReal.ofReal_ne_top hae
  exact ⟨hUI, graph_ui H μ ν Γ Q hQ hc hw hUI⟩

theorem graph_barycenter : Claims.graph_barycenter := by
  intro H _ _ _ _ _ _ μ _ ν Γ Q κ _ hQ hc hΓ hw hUI
  have hint := graph_ui H μ ν Γ Q hQ hc hw hUI
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hint (fun _ => zero_le') fun n => ?_
  rw [hΓ n]; exact lintegral_bary_le μ (κ n) hQ

/-! ### A `lem:app-graph-empirical` -/

section Emp
variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E]

lemma lintegral_empHat (Xs : ℕ → Ω → E) (n : ℕ) (ω : Ω) (f : E → ℝ≥0∞) :
    ∫⁻ x, f x ∂(empHat Xs n ω) = (n : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range n, f (Xs i ω) := by
  unfold empHat
  rw [lintegral_smul_measure, lintegral_finsetSum_measure]
  simp [lintegral_dirac]

lemma empHat_univ (Xs : ℕ → Ω → E) {n : ℕ} (hn : 1 ≤ n) (ω : Ω) : empHat Xs n ω univ = 1 := by
  have := lintegral_empHat Xs n ω 1
  simp only [Pi.one_apply, lintegral_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
  rw [this]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (by omega : n ≠ 0)) (ENNReal.natCast_ne_top n)

end Emp

theorem app_graph_empirical : Claims.app_graph_empirical := by
  intro K Ω _ P _ P0 C F Xs γ hC hF hFC hXm hind hlaw hmarg hw
  haveI : IsProbabilityMeasure P0 := by rw [← hlaw 0]; infer_instance
  obtain ⟨g, hg⟩ := exists_bcf_seq P0 hF
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hC.isBounded
  -- the strong law for each `ψ_{g_k}`
  have hslln : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n => ∫⁻ x, psiG F (g k) x ∂(empHat Xs n ω)) atTop
      (𝓝 (∫⁻ x, psiG F (g k) x ∂P0)) := by
    intro k
    have hψ := measurable_psiG hF (g k)
    set Y : ℕ → Ω → ℝ := fun i ω => (psiG F (g k) (Xs i ω)).toReal with hY
    have hYm : ∀ i, Measurable (Y i) := fun i => (hψ.comp (hXm i)).ennreal_toReal
    have hint : Integrable (Y 0) P := by
      refine Integrable.of_bound (hYm 0).aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using psiG_le_one F (g k) _)
    have hindY : Pairwise fun i j => IndepFun (Y i) (Y j) P := fun i j hij =>
      (hind hij).comp (hψ.ennreal_toReal) (hψ.ennreal_toReal)
    have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
      (show IdentDistrib (Xs i) (Xs 0) P P from
        ⟨(hXm i).aemeasurable, (hXm 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩).comp hψ.ennreal_toReal
    have hs := strong_law_ae_real Y hint hindY hident
    filter_upwards [hs] with ω hω
    have hmean : ENNReal.ofReal (∫ ω, Y 0 ω ∂P) = ∫⁻ x, psiG F (g k) x ∂P0 := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
      rw [← hlaw 0, lintegral_map hψ (hXm 0)]
      refine lintegral_congr fun ω => ?_
      exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (psiG_le_one F (g k) _))
    rw [← hmean]
    refine ((ENNReal.continuous_ofReal.tendsto _).comp hω).congr fun n => ?_
    simp only [Function.comp, lintegral_empHat]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_sum_of_nonneg
      (fun _ _ => ENNReal.toReal_nonneg), ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (psiG_le_one F (g k) _))
  have hall := ae_all_iff.2 hslln
  have hbound : ∀ n ω, ∫⁻ z, sqDisc F z ∂(γ (n + 1) ω) ≤ ENNReal.ofReal ((2 * R) ^ 2) := by
    intro n ω
    obtain ⟨h1, h2⟩ := hmarg (n + 1) (by omega) ω
    have huniv : γ (n + 1) ω univ = 1 := by
      rw [← Measure.fst_univ]; exact (congrArg (· univ) h1).trans (empHat_univ Xs (by omega) ω)
    haveI : IsProbabilityMeasure (γ (n + 1) ω) := ⟨huniv⟩
    calc ∫⁻ z, sqDisc F z ∂(γ (n + 1) ω) ≤ ∫⁻ _, ENNReal.ofReal ((2 * R) ^ 2) ∂(γ (n + 1) ω) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_snd_mem (γ (n + 1) ω) hC.measurableSet h2] with z hz
          exact sqDisc_le_of_mem (hR _ hz) (hR _ (hFC _))
      _ = _ := by rw [lintegral_const, huniv, mul_one]
  have hdet : ∀ᵐ ω ∂P, Tendsto (fun n => ∫⁻ z, sqDisc F z ∂(γ (n + 1) ω)) atTop (𝓝 0) := by
    filter_upwards [hall, hw] with ω h1 h2
    set Γ : ℕ → Measure _ := fun n => γ (n + 1) ω
    have hfst : ∀ n, (Γ n).map Prod.fst = empHat Xs (n + 1) ω := fun n => (hmarg (n + 1) (by omega) ω).1
    have huniv : ∀ n, Γ n univ = 1 := fun n => by
      rw [← Measure.fst_univ]; exact (congrArg (· univ) (hfst n)).trans (empHat_univ Xs (by omega) ω)
    have hw' : WeakTo atTop Γ (graphLaw P0 F) := fun f => (tendsto_add_atTop_iff_nat 1).2 (h2 f)
    have hbad : ∀ r : ℝ, 0 < r → Tendsto (fun n => Γ n {z | r < ‖z.2 - F z.1‖}) atTop (𝓝 0) :=
      fun r hr => tendsto_bad P0 hF Γ (fun n => ⟨by rw [huniv]; exact ENNReal.one_lt_top⟩) hw' g hg
        (fun k => by simp only [hfst]; exact (tendsto_add_atTop_iff_nat 1).2 (h1 k)) hr
    refine tendsto_lintegral_sqDisc hF Γ (fun n => (huniv n).le) hbad
      (ui_of_ae_le hF Γ (M := ENNReal.ofReal ((2 * R) ^ 2)) ENNReal.ofReal_ne_top fun n => ?_)
    obtain ⟨-, h2⟩ := hmarg (n + 1) (by omega) ω
    haveI : IsProbabilityMeasure (Γ n) := ⟨huniv n⟩
    filter_upwards [ae_snd_mem (Γ n) hC.measurableSet h2] with z hz
    exact sqDisc_le_of_mem (hR _ hz) (hR _ (hFC _))
  refine ⟨?_, ?_⟩
  · filter_upwards [hdet] with ω h
    exact (tendsto_add_atTop_iff_nat 1).1 h
  · rw [← tendsto_add_atTop_iff_nat 1]
    have := tendsto_lintegral_of_dominated_convergence (μ := P)
      (F := fun n ω => ∫⁻ z, sqDisc F z ∂(γ (n + 1) ω)) (f := fun _ => 0)
      (fun _ => ENNReal.ofReal ((2 * R) ^ 2))
      (fun n => (measurable_sqDisc hF).lintegral_kernel)
      (fun n => Eventually.of_forall fun ω => hbound n ω)
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hdet
    simpa using this

theorem app_graph_empirical_barycenter : Claims.app_graph_empirical_barycenter := by
  intro K Ω _ P _ P0 C F Xs γ κ _ hC hF hFC hXm hind hlaw hmarg hdis hw
  obtain ⟨has, hexp⟩ := app_graph_empirical K P P0 C F Xs γ hC hF hFC hXm hind hlaw hmarg hw
  have hle : ∀ n, 1 ≤ n → ∀ ω, ∫⁻ x, ‖bary (κ n ω) x - F x‖ₑ ^ 2 ∂(empHat Xs n ω) ≤
      ∫⁻ z, sqDisc F z ∂(γ n ω) := by
    intro n hn ω
    haveI : IsProbabilityMeasure (empHat Xs n ω) := ⟨empHat_univ Xs hn ω⟩
    rw [hdis n hn ω]; exact lintegral_bary_le _ (κ n ω) hF
  refine ⟨?_, ?_⟩
  · filter_upwards [has] with ω h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun _ => zero_le') (eventually_atTop.2 ⟨1, fun n hn => hle n hn ω⟩)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
      (Eventually.of_forall fun _ => zero_le')
      (eventually_atTop.2 ⟨1, fun n hn => lintegral_mono fun ω => hle n hn ω⟩)

end StatFormal.OTFD.Wave19a
