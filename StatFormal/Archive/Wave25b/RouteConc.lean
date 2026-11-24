import StatFormal.Archive.OTFD.Wave19a.RouteGraph
import StatFormal.Lib.Empirical.Varadarajan

/-!
# Route (wave 25b): graph concentration for plans with empirical first marginals (untrusted)

* `slln_fin`: the strong law for a fixed Borel `[0,1]`-valued function, prefix averages over `Fin n`.
* `conc_det`: deterministic glue of the wave-19a tools (`tendsto_bad`, `tendsto_lintegral_sqDisc`): plans converging
  weakly to a graph plan `(Id, Q)#μ`, whose first marginals integrate the countably many test functions `ψ_{g_k}`
  correctly in the limit, and carried by a bounded set in `y` (with `Q` bounded), have `∫ ‖y − Q x‖² → 0`.
* `measurable_of_fibres`: `ω ↦ φ(s ω) ω` is measurable for a finite-valued `s` with measurable fibres.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace StatFormal.Wave25b

open StatFormal.OTFD.Wave19a (WeakTo graphLaw sqDisc psiG measurable_psiG psiG_le_one tendsto_bad
  tendsto_lintegral_sqDisc ui_of_ae_le sqDisc_le_of_mem)

/-- **Strong law, prefix form.** -/
theorem slln_fin {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {Pr : Measure Ω}
    [IsProbabilityMeasure Pr] {X : ℕ → Ω → α} {μ : Measure α} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X Pr) (hlaw : ∀ i, Pr.map (X i) = μ) {f : α → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, f x ≤ 1) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n : ℕ => (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, f (X i ω)) atTop (𝓝 (∫⁻ x, f x ∂μ)) := by
  set Y : ℕ → Ω → ℝ := fun i ω => (f (X i ω)).toReal with hY
  have hYm : ∀ i, Measurable (Y i) := fun i => (hf.comp (hX i)).ennreal_toReal
  have hint : Integrable (Y 0) Pr := by
    refine Integrable.of_bound (hYm 0).aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hf1 _)
  have hindY : Pairwise fun i j => IndepFun (Y i) (Y j) Pr := fun i j hij =>
    (hind.indepFun hij).comp hf.ennreal_toReal hf.ennreal_toReal
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) Pr Pr := fun i =>
    (show IdentDistrib (X i) (X 0) Pr Pr from
      ⟨(hX i).aemeasurable, (hX 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩).comp hf.ennreal_toReal
  have hs := strong_law_ae_real Y hint hindY hident
  filter_upwards [hs] with ω hω
  have hmean : ENNReal.ofReal (∫ ω, Y 0 ω ∂Pr) = ∫⁻ x, f x ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
    rw [← hlaw 0, lintegral_map hf (hX 0)]
    refine lintegral_congr fun ω => ?_
    exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 _))
  rw [← hmean]
  refine ((ENNReal.continuous_ofReal.tendsto _).comp hω).congr fun n => ?_
  simp only [Function.comp]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_sum_of_nonneg
    (fun _ _ => ENNReal.toReal_nonneg), ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun i => ENNReal.ofReal (Y i ω)) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 _))

section Det
variable {X E : Type*} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- **Deterministic concentration.** -/
theorem conc_det (μ : Measure X) [IsProbabilityMeasure μ] {Q : X → E} (hQ : Measurable Q) {B : ℝ}
    (hQB : ∀ x, ‖Q x‖ ≤ B) (Γ : ℕ → Measure (X × E)) (hΓ : ∀ n, IsProbabilityMeasure (Γ n))
    (hw : WeakTo atTop Γ (graphLaw μ Q)) (g : ℕ → X →ᵇ E)
    (hg : Tendsto (fun k => ∫⁻ x, psiG Q (g k) x ∂μ) atTop (𝓝 0))
    (hmarg : ∀ k, Tendsto (fun n => ∫⁻ x, psiG Q (g k) x ∂((Γ n).map Prod.fst)) atTop
      (𝓝 (∫⁻ x, psiG Q (g k) x ∂μ)))
    (hy : ∀ n, ∀ᵐ z ∂(Γ n), ‖z.2‖ ≤ B) :
    Tendsto (fun n => ∫⁻ z, sqDisc Q z ∂(Γ n)) atTop (𝓝 0) := by
  have hbad : ∀ r : ℝ, 0 < r → Tendsto (fun n => Γ n {z | r < ‖z.2 - Q z.1‖}) atTop (𝓝 0) :=
    fun r hr => tendsto_bad μ hQ Γ (fun n => by haveI := hΓ n; exact inferInstance) hw g hg hmarg hr
  refine tendsto_lintegral_sqDisc hQ Γ (fun n => by haveI := hΓ n; exact prob_le_one) hbad
    (ui_of_ae_le hQ Γ (M := ENNReal.ofReal ((2 * B) ^ 2)) ENNReal.ofReal_ne_top fun n => ?_)
  filter_upwards [hy n] with z hz
  exact sqDisc_le_of_mem hz (hQB _)

end Det

/-- `ω ↦ φ (s ω) ω` is measurable when `s` takes values in a finite type with measurable fibres. -/
theorem measurable_of_fibres {Ω A : Type*} [MeasurableSpace Ω] [Fintype A] [DecidableEq A] {s : Ω → A}
    (hs : ∀ a, MeasurableSet {ω | s ω = a}) {φ : A → Ω → ℝ≥0∞} (hφ : ∀ a, Measurable (φ a)) :
    Measurable fun ω => φ (s ω) ω := by
  have heq : (fun ω => φ (s ω) ω) = fun ω => ∑ a, {ω | s ω = a}.indicator (φ a) ω := by
    funext ω
    rw [Finset.sum_eq_single (s ω)]
    · exact (indicator_of_mem (show ω ∈ {ω' | s ω' = s ω} from rfl) _).symm
    · intro b _ hb
      rw [indicator_of_notMem (show ω ∉ {ω | s ω = b} from fun h => hb h.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [heq]
  exact Finset.measurable_sum _ fun a _ => (hφ a).indicator (hs a)

end StatFormal.Wave25b
