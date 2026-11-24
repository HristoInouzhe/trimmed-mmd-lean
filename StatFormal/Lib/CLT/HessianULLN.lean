import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Instances.Rat
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Uniform laws for smooth functionals (library)

Tools for uniform laws of large numbers of derivatives of a plug-in objective (the Hessian uniform law, Step 1 of
ICL `thm:score`):

* `tuOn_pi`: componentwise uniform convergence of `ℝ^k`-valued functions is uniform convergence;
* `tuOn_map`: if `F_n → f` uniformly on `S` with values in a closed set `D` on which `Φ` is continuous and `f` is
  bounded, then `Φ ∘ F_n → Φ ∘ f` uniformly on `S` (uniform continuity on a compact piece of `D`);
* `tuOn_const_seq`, `TendstoUniformlyOn.congr_eventually`;
* `tendsto_outer_of_ae_tendstoUniformlyOn`: almost-sure uniform convergence on an open set of functions continuous
  in the parameter and measurable in `ω` gives `P*(∃ t ∈ U, |h_n(t) − H(t)| ≥ η) → 0` (the event is covered by a
  countable union over rational `t`).
-/

noncomputable section
open Filter Topology Set Metric

namespace StatFormal.Foundations.CLT

variable {A : Type*}

lemma tuOn_pi {k : ℕ} {F : ℕ → A → Fin k → ℝ} {f : A → Fin k → ℝ} {S : Set A}
    (h : ∀ i, TendstoUniformlyOn (fun n a => F n a i) (fun a => f a i) atTop S) :
    TendstoUniformlyOn F f atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h2 : ∀ i, ∀ᶠ n in atTop, ∀ a ∈ S, dist (f a i) (F n a i) < ε / 2 := fun i =>
    (Metric.tendstoUniformlyOn_iff.1 (h i)) (ε / 2) (half_pos hε)
  filter_upwards [Filter.eventually_all.2 h2] with n hn a ha
  exact ((dist_pi_le_iff (half_pos hε).le).2 fun i => (hn i a ha).le).trans_lt (half_lt_self hε)

lemma tuOn_map {k : ℕ} {F : ℕ → A → Fin k → ℝ} {f : A → Fin k → ℝ} {S : Set A}
    (hF : TendstoUniformlyOn F f atTop S) {D : Set (Fin k → ℝ)} (hD : IsClosed D) {Φ : (Fin k → ℝ) → ℝ}
    (hΦ : ContinuousOn Φ D) (hfD : ∀ a ∈ S, f a ∈ D) (hFD : ∀ᶠ n in atTop, ∀ a ∈ S, F n a ∈ D) {R : ℝ}
    (hR : ∀ a ∈ S, ‖f a‖ ≤ R) :
    TendstoUniformlyOn (fun n a => Φ (F n a)) (fun a => Φ (f a)) atTop S := by
  set C := D ∩ closedBall (0 : Fin k → ℝ) (R + 1) with hC
  have hCc : IsCompact C := (isCompact_closedBall 0 (R + 1)).inter_left hD
  have hu : UniformContinuousOn Φ C := hCc.uniformContinuousOn_of_continuous (hΦ.mono inter_subset_left)
  have hfC : ∀ a ∈ S, f a ∈ C := fun a ha => ⟨hfD a ha, by
    rw [mem_closedBall, dist_zero_right]; linarith [hR a ha]⟩
  have hFC : ∀ᶠ n in atTop, ∀ a ∈ S, F n a ∈ C := by
    filter_upwards [hFD, (Metric.tendstoUniformlyOn_iff.1 hF) 1 one_pos] with n hn h1 a ha
    refine ⟨hn a ha, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    have := h1 a ha
    rw [dist_comm, dist_eq_norm] at this
    have h3 := norm_le_insert' (F n a) (f a)
    linarith [hR a ha]
  exact hu.comp_tendstoUniformlyOn_eventually hFC hfC hF

lemma tuOn_const_seq {c : ℕ → ℝ} {c0 : ℝ} (hc : Tendsto c atTop (𝓝 c0)) (S : Set A) :
    TendstoUniformlyOn (fun n (_ : A) => c n) (fun _ => c0) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.1 hc ε hε] with n hn a _
  rw [dist_comm]; exact hn

lemma TendstoUniformlyOn.congr_eventually {F G : ℕ → A → ℝ} {f g : A → ℝ} {S : Set A}
    (h : TendstoUniformlyOn F f atTop S) (hFG : ∀ᶠ n in atTop, ∀ a ∈ S, F n a = G n a)
    (hfg : ∀ a ∈ S, f a = g a) : TendstoUniformlyOn G g atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε, hFG] with n hn hn' a ha
  rw [← hn' a ha, ← hfg a ha]; exact hn a ha

open MeasureTheory in
/-- Almost-sure uniform convergence on an open set gives convergence in outer probability of the supremum event,
for functions continuous in the parameter and measurable in `ω`. -/
theorem tendsto_outer_of_ae_tendstoUniformlyOn {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {h : ℕ → Ω → ℝ → ℝ} {H : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hcont : ∀ᶠ n in atTop, ∀ ω, ContinuousOn (h n ω) U) (hHc : ContinuousOn H U)
    (hmeas : ∀ᶠ n in atTop, ∀ q ∈ U, Measurable (fun ω => h n ω q))
    (hunif : ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n => h n ω) H atTop U) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => P {ω | ∃ t ∈ U, η ≤ |h n ω t - H t|}) atTop (𝓝 0) := by
  set S : ℕ → Set Ω := fun n => ⋃ (q : ℚ) (_ : (q : ℝ) ∈ U), {ω | η / 2 < |h n ω q - H q|} with hSdef
  -- the event is covered by `S n`
  have hcover : ∀ᶠ n in atTop, {ω | ∃ t ∈ U, η ≤ |h n ω t - H t|} ⊆ S n := by
    filter_upwards [hcont] with n hn ω ⟨t, htU, ht⟩
    have hfc : ContinuousOn (fun u => |h n ω u - H u|) U := ((hn ω).sub hHc).abs
    have hO : IsOpen (U ∩ (fun u => |h n ω u - H u|) ⁻¹' Ioi (η / 2)) := hfc.isOpen_inter_preimage hU isOpen_Ioi
    have htmem : t ∈ U ∩ (fun u => |h n ω u - H u|) ⁻¹' Ioi (η / 2) :=
      ⟨htU, show η / 2 < |h n ω t - H t| by linarith⟩
    obtain ⟨q, hqO⟩ : ∃ q : ℚ, (q : ℝ) ∈ U ∩ (fun u => |h n ω u - H u|) ⁻¹' Ioi (η / 2) := by
      obtain ⟨y, hy, ⟨q, rfl⟩⟩ := Rat.denseRange_cast.inter_open_nonempty _ hO ⟨t, htmem⟩
      exact ⟨q, hy⟩
    simp only [hSdef, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨q, hqO.1, hqO.2⟩
  -- measurability and the vanishing of `P (S n)`
  obtain ⟨N, hN⟩ := eventually_atTop.1 hmeas
  have hSm : ∀ n, N ≤ n → MeasurableSet (S n) := fun n hn =>
    MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq =>
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (((hN n hn) q hq).sub_const _))
  set T : ℕ → Set Ω := fun n => ⋃ k, S (N + n + k) with hTdef
  have hTm : ∀ n, MeasurableSet (T n) := fun n => MeasurableSet.iUnion fun k => hSm _ (by omega)
  have hTanti : Antitone T := by
    intro a b hab ω hω
    simp only [hTdef, Set.mem_iUnion] at hω ⊢
    obtain ⟨k, hk⟩ := hω
    exact ⟨b - a + k, by rwa [show N + a + (b - a + k) = N + b + k by omega]⟩
  have hnull : P (⋂ n, T n) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hunif)
    simp only [Set.mem_setOf_eq]
    intro hu
    rw [Metric.tendstoUniformlyOn_iff] at hu
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hu (η / 2) (half_pos hη))
    simp only [hTdef, Set.mem_iInter, Set.mem_iUnion] at hω
    obtain ⟨k, hk⟩ := hω K
    simp only [hSdef, Set.mem_iUnion, Set.mem_setOf_eq] at hk
    obtain ⟨q, hqU, hq⟩ := hk
    have := hK (N + K + k) (by omega) q hqU
    rw [dist_comm, Real.dist_eq] at this
    linarith
  have hT : Tendsto (fun n => P (T n)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := P) (fun n => (hTm n).nullMeasurableSet) hTanti
      ⟨0, measure_ne_top _ _⟩
    rwa [hnull] at this
  have hST : ∀ n, P (S (N + n)) ≤ P (T n) := fun n =>
    measure_mono (Set.subset_iUnion_of_subset 0 (by simp [add_zero]))
  have hS : Tendsto (fun n => P (S n)) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat N]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => zero_le) fun n => ?_
    simpa [add_comm] using hST n
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hS (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hcover] with n hn
  exact measure_mono hn

end StatFormal.Foundations.CLT
