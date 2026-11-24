import StatFormal.Archive.Wave24c.Statements
import StatFormal.Archive.Wave20b.RouteENormalizers
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Route — ICL `lem:e-measures`, `lem:e-ulln` (untrusted)

* Population: `∫ φ dμ_θ = P₀(φ s_θ)/c_θ`, a ratio of parametric integrals of jointly continuous integrands on compact
  spaces with `c_θ ≥ s_− > 0`; `ρ_{μ_θ}(z) = P₀(s_θ K(z,·))/c_θ ∈ [K_min, K_max]`.
* Empirical: `ρ_{μ_{θ,n}}(z) = P_n(s_θ K(z,·))/P_n s_θ` with `P_n s_θ ≥ s_−` and values in `[K_min, K_max]`; uniform
  convergence of ratios with denominators bounded below, `|log a − log b| ≤ |a − b|/K_min`, and the Glivenko–Cantelli
  principle for the three continuous classes `s_θ`, `s_θ K(z,·)` (index `(θ,z)`) and `log ρ_{μ_θ}`.
* Glivenko–Cantelli (`compactGC_of_iid`): the compact-parametric principle for i.i.d. nested samples is the Wave 20b
  route's `uniform_slln` (strong law on a countable dense set, Heine–Cantor), re-indexed from `n + 1` to `n` points.
* `lem:e-ulln`: the same for `KL = P(s log s)/P s − log P s`, and `λ_n F_n → λ F` uniformly for bounded `F`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset
open scoped ENNReal NNReal

namespace StatFormal.Wave24c

/-! ### The compact-parametric Glivenko–Cantelli principle -/

section GC
variable {Z : Type*} [MeasurableSpace Z]

/-- For every compact metric `A` and continuous `f : A × 𝒵 → ℝ`, almost surely `sup_a |P_n f_a − P₀ f_a| → 0`. -/
def CompactGC [TopologicalSpace Z] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P0 : Measure Z)
    (X : ℕ → Ω → Z) : Prop :=
  ∀ (A : Type) [MetricSpace A] [CompactSpace A] (f : A → Z → ℝ), Continuous (Function.uncurry f) →
    ∀ᵐ ω ∂P, TendstoUniformly (fun n a => empAvg (fun i => X i ω) n (f a)) (fun a => ∫ z, f a z ∂P0) atTop

end GC

lemma compactGC_of_iid {Z Ω : Type} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [MeasurableSpace Ω] {P : Measure Ω} {P0 : Measure Z} {X : ℕ → Ω → Z} (hP0 : IsProbabilityMeasure P0)
    (hP : IsProbabilityMeasure P) (hXm : ∀ j, Measurable (X j)) (hXi : ProbabilityTheory.iIndepFun X P)
    (hXl : ∀ j, P.map (X j) = P0) : CompactGC P P0 X := by
  intro A _ _ f hf
  have h := StatFormal.Wave20b.uniform_slln (Θ := A) (Pr := P) (P0 := P0) hXm hXi hXl hf
  filter_upwards [h] with ω hω
  rw [Metric.tendstoUniformly_iff] at hω ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hω ε hε)
  refine Filter.eventually_atTop.2 ⟨N + 1, fun n hn a => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk := hN k (by omega) a
  have heq : StatFormal.Wave20b.empAvg X k (f a) ω = empAvg (fun i => X i ω) (k + 1) (f a) := by
    simp only [StatFormal.Wave20b.empAvg, empAvg, Nat.cast_add, Nat.cast_one]
  rwa [heq] at hk

/-! ### Uniform convergence algebra -/

section UnifAlg
variable {ι A : Type*} {l : Filter ι}

lemma abs_div_sub_div_le {a b c d k C : ℝ} (hk : 0 < k) (hb : k ≤ b) (hd : k ≤ d) (hc : |c| ≤ C) :
    |a / b - c / d| ≤ |a - c| / k + C * |d - b| / k ^ 2 := by
  have hb0 : 0 < b := lt_of_lt_of_le hk hb
  have hd0 : 0 < d := lt_of_lt_of_le hk hd
  have heq : a / b - c / d = (a - c) / b + c * (d - b) / (b * d) := by field_simp; ring
  rw [heq]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hb0]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hk hb
  · rw [abs_div, abs_mul, abs_of_pos (mul_pos hb0 hd0)]
    have h1 : |c| * |d - b| ≤ C * |d - b| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    have h2 : k ^ 2 ≤ b * d := by nlinarith
    calc |c| * |d - b| / (b * d) ≤ C * |d - b| / (b * d) := div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ C * |d - b| / k ^ 2 := by
          apply div_le_div_of_nonneg_left _ (by positivity) h2
          exact le_trans (mul_nonneg (abs_nonneg _) (abs_nonneg _)) h1

lemma tendstoUniformly_div_of_ge {Nn Dn : ι → A → ℝ} {N D : A → ℝ} {k C : ℝ} (hk : 0 < k) (hC : 0 ≤ C)
    (hN : TendstoUniformly Nn N l) (hD : TendstoUniformly Dn D l) (hDn : ∀ᶠ i in l, ∀ a, k ≤ Dn i a)
    (hDk : ∀ a, k ≤ D a) (hNC : ∀ a, |N a| ≤ C) :
    TendstoUniformly (fun i a => Nn i a / Dn i a) (fun a => N a / D a) l := by
  rw [Metric.tendstoUniformly_iff] at hN hD ⊢
  intro ε hε
  set η := ε * k ^ 2 / (2 * (k + C + 1)) with hη
  have hk1 : 0 < k + C + 1 := by linarith
  have hη0 : 0 < η := by positivity
  filter_upwards [hN η hη0, hD η hη0, hDn] with i hi1 hi2 hi3 a
  simp only [Real.dist_eq] at hi1 hi2 ⊢
  have h := abs_div_sub_div_le (a := Nn i a) (b := Dn i a) (c := N a) (d := D a) hk (hi3 a) (hDk a) (hNC a)
  have e1 : |Nn i a - N a| < η := by rw [abs_sub_comm]; exact hi1 a
  have e2 : |D a - Dn i a| < η := hi2 a
  have hk2 : 0 < k ^ 2 := by positivity
  rw [abs_sub_comm]
  refine lt_of_le_of_lt h ?_
  have hb : |Nn i a - N a| / k + C * |D a - Dn i a| / k ^ 2 ≤ η / k + C * η / k ^ 2 := by
    gcongr
  have hval : η / k + C * η / k ^ 2 = ε * (k + C) / (2 * (k + C + 1)) := by
    rw [hη]; field_simp
  have hlt : ε * (k + C) / (2 * (k + C + 1)) < ε := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  linarith

lemma abs_log_sub_log_le {a b k : ℝ} (hk : 0 < k) (ha : k ≤ a) (hb : k ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / k := by
  have ha0 : 0 < a := lt_of_lt_of_le hk ha
  have hb0 : 0 < b := lt_of_lt_of_le hk hb
  have h1 : Real.log a - Real.log b ≤ (a - b) / b := by
    rw [← Real.log_div ha0.ne' hb0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    have e : a / b - 1 = (a - b) / b := by field_simp
    linarith
  have h2 : Real.log b - Real.log a ≤ (b - a) / a := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    have e : b / a - 1 = (b - a) / a := by field_simp
    linarith
  rw [abs_le]
  constructor
  · have : (b - a) / a ≤ |a - b| / k := by
      rw [abs_sub_comm]
      calc (b - a) / a ≤ |b - a| / a := div_le_div_of_nonneg_right (le_abs_self _) ha0.le
        _ ≤ |b - a| / k := div_le_div_of_nonneg_left (abs_nonneg _) hk ha
    linarith
  · calc Real.log a - Real.log b ≤ (a - b) / b := h1
      _ ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb0.le
      _ ≤ |a - b| / k := div_le_div_of_nonneg_left (abs_nonneg _) hk hb

lemma tendstoUniformly_log_of_ge {Fn : ι → A → ℝ} {F : A → ℝ} {k : ℝ} (hk : 0 < k)
    (hF : TendstoUniformly Fn F l) (hFn : ∀ᶠ i in l, ∀ a, k ≤ Fn i a) (hFk : ∀ a, k ≤ F a) :
    TendstoUniformly (fun i a => Real.log (Fn i a)) (fun a => Real.log (F a)) l := by
  rw [Metric.tendstoUniformly_iff] at hF ⊢
  intro ε hε
  filter_upwards [hF (ε * k) (by positivity), hFn] with i hi1 hi2 a
  simp only [Real.dist_eq] at hi1 ⊢
  refine lt_of_le_of_lt (abs_log_sub_log_le hk (hFk a) (hi2 a)) ?_
  rw [div_lt_iff₀ hk]
  exact hi1 a

lemma tendstoUniformly_seq_mul {Fn : ι → A → ℝ} {F : A → ℝ} {lamn : ι → ℝ} {lam0 C : ℝ}
    (hlam : Tendsto lamn l (𝓝 lam0)) (hF : TendstoUniformly Fn F l) (hFC : ∀ a, |F a| ≤ C) :
    TendstoUniformly (fun i a => lamn i * Fn i a) (fun a => lam0 * F a) l := by
  rw [Metric.tendstoUniformly_iff] at hF ⊢
  intro ε hε
  have hC1 : 0 < |C| + 1 := by positivity
  set η := ε / (2 * (|C| + 1 + |lam0| + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ ε := by
    rw [hη, div_le_iff₀ (by positivity)]; nlinarith [abs_nonneg C, abs_nonneg lam0]
  have hlam' : ∀ᶠ i in l, |lamn i - lam0| < min η 1 := by
    have := (Metric.tendsto_nhds.1 hlam) (min η 1) (lt_min hη0 one_pos)
    filter_upwards [this] with i hi
    rwa [Real.dist_eq] at hi
  filter_upwards [hF (min η 1) (lt_min hη0 one_pos), hlam'] with i hi1 hi2 a
  simp only [Real.dist_eq] at hi1 ⊢
  have e1 : |F a - Fn i a| < min η 1 := hi1 a
  have hFn : |Fn i a| ≤ |C| + 1 := by
    have := abs_sub_abs_le_abs_sub (Fn i a) (F a)
    rw [abs_sub_comm (Fn i a)] at this
    have := hFC a
    have := le_abs_self C
    linarith [min_le_right η 1]
  have heq : lam0 * F a - lamn i * Fn i a = (lam0 - lamn i) * Fn i a + lam0 * (F a - Fn i a) := by ring
  rw [heq]
  calc |(lam0 - lamn i) * Fn i a + lam0 * (F a - Fn i a)| ≤ |lam0 - lamn i| * |Fn i a| + |lam0| * |F a - Fn i a| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ η * (|C| + 1) + |lam0| * η := by
        rw [abs_sub_comm]
        gcongr
        · exact le_trans hi2.le (min_le_left _ _)
        · exact le_trans e1.le (min_le_left _ _)
    _ < ε := by
        rw [hη]
        rw [div_mul_eq_mul_div, mul_div_assoc', ← add_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg C, abs_nonneg lam0]

lemma tu_congr {F G : ι → A → ℝ} {f : A → ℝ} (h : TendstoUniformly F f l) (hFG : ∀ᶠ i in l, ∀ a, F i a = G i a) :
    TendstoUniformly G f l := by
  intro u hu
  filter_upwards [h u hu, hFG] with i h1 h2 a
  rw [← h2 a]; exact h1 a

lemma tu_congr_lim {F : ι → A → ℝ} {f g : A → ℝ} (h : TendstoUniformly F f l) (hfg : ∀ a, f a = g a) :
    TendstoUniformly F g l := by
  have : f = g := funext hfg
  rwa [← this]

lemma tu_sub {F G : ι → A → ℝ} {f g : A → ℝ} (hF : TendstoUniformly F f l) (hG : TendstoUniformly G g l) :
    TendstoUniformly (fun i a => F i a - G i a) (fun a => f a - g a) l := hF.sub hG

lemma tu_add {F G : ι → A → ℝ} {f g : A → ℝ} (hF : TendstoUniformly F f l) (hG : TendstoUniformly G g l) :
    TendstoUniformly (fun i a => F i a + G i a) (fun a => f a + g a) l := hF.add hG

lemma abs_log_le_of_mem {a b x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    |Real.log x| ≤ |Real.log a| + |Real.log b| := by
  have h1 : Real.log a ≤ Real.log x := Real.log_le_log ha hax
  have h2 : Real.log x ≤ Real.log b := Real.log_le_log (lt_of_lt_of_le ha hax) hxb
  rw [abs_le]; constructor <;> cases abs_cases (Real.log a) <;> cases abs_cases (Real.log b) <;> linarith

lemma tu_comp_tendsto {F : ℕ → A → ℝ} {f : A → ℝ} (h : TendstoUniformly F f atTop) {m : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) : TendstoUniformly (fun n a => F (m n) a) f atTop := by
  intro u hu
  exact hm.eventually (h u hu)

end UnifAlg

/-! ### Population and empirical context laws -/

section ICLMeasure
variable {Θ Z : Type} [MetricSpace Θ] [CompactSpace Θ] [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
  [BorelSpace Z]

lemma integrable_of_continuous' {μ : Measure Z} [IsFiniteMeasure μ] {f : Z → ℝ} (hf : Continuous f) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ fun z => hC z (mem_univ z))

variable {P0 : Measure Z} [IsProbabilityMeasure P0] {s : Θ → Z → ℝ} {K : Z → Z → ℝ}

lemma normC_bounds (hs : Continuous (Function.uncurry s)) {sm sp : ℝ} (hb : ∀ θ z, sm ≤ s θ z ∧ s θ z ≤ sp)
    (θ : Θ) : sm ≤ normC P0 s θ ∧ normC P0 s θ ≤ sp := by
  have hi := integrable_of_continuous' (μ := P0) (hs.uncurry_left θ)
  constructor
  · have := integral_mono (integrable_const sm) hi (fun z => (hb θ z).1)
    simpa [normC] using this
  · have := integral_mono hi (integrable_const sp) (fun z => (hb θ z).2)
    simpa [normC] using this

lemma continuous_param_integral {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [LocallyCompactSpace X] {f : X → Z → ℝ} (hf : Continuous (Function.uncurry f)) :
    Continuous fun x => ∫ z, f x z ∂P0 := by
  have := continuous_parametric_integral_of_continuous (μ := P0) hf (isCompact_univ (X := Z))
  simpa [Measure.restrict_univ] using this

lemma integral_ctxLawT (hs : Continuous (Function.uncurry s)) {sm : ℝ} (hsm : 0 < sm)
    (hb : ∀ θ z, sm ≤ s θ z) (θ : Θ) (φ : Z → ℝ) :
    ∫ z, φ z ∂ctxLawT P0 s θ = (∫ z, φ z * s θ z ∂P0) / normC P0 s θ := by
  have hc : 0 < normC P0 s θ := by
    have := integral_mono (integrable_const sm) (integrable_of_continuous' (μ := P0) (hs.uncurry_left θ))
      (fun z => hb θ z)
    have h' : sm ≤ normC P0 s θ := by simpa [normC] using this
    exact lt_of_lt_of_le hsm h'
  have hmeas : Measurable fun z => Real.toNNReal (s θ z / normC P0 s θ) :=
    (((hs.uncurry_left θ).measurable).div_const _).real_toNNReal
  unfold ctxLawT
  change ∫ z, φ z ∂P0.withDensity (fun z => ((Real.toNNReal (s θ z / normC P0 s θ) : ℝ≥0) : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hmeas, ← integral_div]
  congr 1
  funext z
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (div_nonneg (le_trans hsm.le (hb θ z)) hc.le)]
  ring

lemma isProb_ctxLawT (hs : Continuous (Function.uncurry s)) {sm : ℝ} (hsm : 0 < sm)
    (hb : ∀ θ z, sm ≤ s θ z) (θ : Θ) : IsProbabilityMeasure (ctxLawT P0 s θ) := by
  have hi := integrable_of_continuous' (μ := P0) (hs.uncurry_left θ)
  have hc : 0 < normC P0 s θ := by
    have := integral_mono (integrable_const sm) hi (fun z => hb θ z)
    have h' : sm ≤ normC P0 s θ := by simpa [normC] using this
    exact lt_of_lt_of_le hsm h'
  constructor
  unfold ctxLawT
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (ae_of_all _ fun z => div_nonneg (le_trans hsm.le (hb θ z)) hc.le), integral_div]
  rw [show ∫ z, s θ z ∂P0 = normC P0 s θ from rfl, div_self hc.ne', ENNReal.ofReal_one]

lemma coverRho_pop (hs : Continuous (Function.uncurry s)) {sm : ℝ} (hsm : 0 < sm) (hb : ∀ θ z, sm ≤ s θ z)
    (θ : Θ) (z : Z) : coverRho K (ctxLawT P0 s θ) z = (∫ z', s θ z' * K z z' ∂P0) / normC P0 s θ := by
  unfold coverRho
  rw [integral_ctxLawT hs hsm hb θ]
  congr 1; congr 1; funext z'; ring

lemma normC_pos (hs : Continuous (Function.uncurry s)) {sm : ℝ} (hsm : 0 < sm) (hb : ∀ θ z, sm ≤ s θ z)
    (θ : Θ) : 0 < normC P0 s θ := by
  have := integral_mono (integrable_const sm) (integrable_of_continuous' (μ := P0) (hs.uncurry_left θ))
    (fun z => hb θ z)
  have h' : sm ≤ normC P0 s θ := by simpa [normC] using this
  exact lt_of_lt_of_le hsm h'

lemma coverRho_bounds (hs : Continuous (Function.uncurry s)) {sm : ℝ} (hsm : 0 < sm) (hb : ∀ θ z, sm ≤ s θ z)
    (hK : Continuous (Function.uncurry K)) {Kmin Kmax : ℝ} (hKb : ∀ z z', Kmin ≤ K z z' ∧ K z z' ≤ Kmax)
    (θ : Θ) (z : Z) : Kmin ≤ coverRho K (ctxLawT P0 s θ) z ∧ coverRho K (ctxLawT P0 s θ) z ≤ Kmax := by
  haveI := isProb_ctxLawT (P0 := P0) hs hsm hb θ
  have hi := integrable_of_continuous' (μ := ctxLawT P0 s θ) (hK.uncurry_left z)
  unfold coverRho
  constructor
  · have := integral_mono (integrable_const Kmin) hi (fun z' => (hKb z z').1)
    simpa using this
  · have := integral_mono hi (integrable_const Kmax) (fun z' => (hKb z z').2)
    simpa using this

end ICLMeasure

theorem e_measures_pop : Claims.e_measures_pop := by
  intro Θ Z _ _ _ _ _ _ P0 s K sm sp Kmin Kmax hP0 hs hsm hsb hK hKmin hKb
  have hb : ∀ θ z, sm ≤ s θ z := fun θ z => (hsb θ z).1
  have hcC : Continuous (normC P0 s) := continuous_param_integral (P0 := P0) hs
  refine ⟨isProb_ctxLawT hs hsm hb, fun φ hφ => ?_, ?_, coverRho_bounds hs hsm hb hK hKb⟩
  · have : (fun θ => ∫ z, φ z ∂ctxLawT P0 s θ) = fun θ => (∫ z, φ z * s θ z ∂P0) / normC P0 s θ :=
      funext fun θ => integral_ctxLawT hs hsm hb θ φ
    rw [this]
    refine Continuous.div ?_ hcC fun θ => (normC_pos hs hsm hb θ).ne'
    exact continuous_param_integral (P0 := P0) (f := fun θ z => φ z * s θ z)
      ((hφ.comp continuous_snd).mul hs)
  · have : (fun p : Θ × Z => coverRho K (ctxLawT P0 s p.1) p.2) =
        fun p => (∫ z', s p.1 z' * K p.2 z' ∂P0) / normC P0 s p.1 :=
      funext fun p => coverRho_pop hs hsm hb p.1 p.2
    rw [this]
    refine Continuous.div ?_ (hcC.comp continuous_fst) fun p => (normC_pos hs hsm hb p.1).ne'
    refine continuous_param_integral (P0 := P0) (f := fun (p : Θ × Z) z' => s p.1 z' * K p.2 z') ?_
    exact (hs.comp (continuous_fst.fst.prodMk continuous_snd)).mul
      (hK.comp (continuous_fst.snd.prodMk continuous_snd))

section ICLEmp
variable {Θ Z : Type} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

lemma empAvg_ge (X : ℕ → Z) {n : ℕ} (hn : 0 < n) {f : Z → ℝ} {c : ℝ} (h : ∀ z, c ≤ f z) : c ≤ empAvg X n f := by
  unfold empAvg
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : (n : ℝ) * c ≤ ∑ i ∈ Finset.range n, f (X i) := by
    have := Finset.sum_le_sum (s := Finset.range n) (fun i _ => h (X i))
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  rw [inv_mul_eq_div, le_div_iff₀ hn']; linarith

lemma empAvg_le (X : ℕ → Z) {n : ℕ} (hn : 0 < n) {f : Z → ℝ} {c : ℝ} (h : ∀ z, f z ≤ c) : empAvg X n f ≤ c := by
  have := empAvg_ge X hn (f := fun z => -f z) (c := -c) (fun z => by linarith [h z])
  unfold empAvg at this ⊢
  rw [Finset.sum_neg_distrib, mul_neg] at this
  linarith

lemma empAvg_sub (X : ℕ → Z) (n : ℕ) (f g : Z → ℝ) :
    empAvg X n (fun z => f z - g z) = empAvg X n f - empAvg X n g := by
  unfold empAvg; rw [Finset.sum_sub_distrib, mul_sub]

lemma empAvg_mul_const (X : ℕ → Z) (n : ℕ) (f : Z → ℝ) (c : ℝ) :
    empAvg X n (fun z => c * f z) = c * empAvg X n f := by
  unfold empAvg; rw [← Finset.mul_sum]; ring

lemma abs_empAvg_le (X : ℕ → Z) (n : ℕ) {g : Z → ℝ} {η : ℝ} (hη : 0 ≤ η) (h : ∀ z, |g z| ≤ η) :
    |empAvg X n g| ≤ η := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [empAvg, hη]
  rw [abs_le]
  constructor
  · have := empAvg_ge X hn (f := g) (c := -η) (fun z => by linarith [(abs_le.1 (h z)).1])
    linarith
  · exact empAvg_le X hn (fun z => (abs_le.1 (h z)).2)

variable {s : Θ → Z → ℝ} {K : Z → Z → ℝ}

lemma coverRho_emp (X : ℕ → Z) {n : ℕ} (hn : 0 < n) (hpos : ∀ θ z, 0 < s θ z) (hK : Continuous (Function.uncurry K))
    (θ : Θ) (z : Z) :
    coverRho K (empCtxLaw s X n θ) z = empAvg X n (fun z' => s θ z' * K z z') / empAvg X n (s θ) := by
  have hS : 0 < ∑ k ∈ Finset.range n, s θ (X k) :=
    Finset.sum_pos (fun k _ => hpos θ (X k)) ⟨0, Finset.mem_range.2 hn⟩
  unfold coverRho empCtxLaw
  rw [integral_finsetSum_measure (fun j _ =>
    (integrable_of_continuous' (μ := Measure.dirac (X j)) (hK.uncurry_left z)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  have hw : ∀ j, (ENNReal.ofReal (s θ (X j) / ∑ k ∈ Finset.range n, s θ (X k))).toReal =
      s θ (X j) / ∑ k ∈ Finset.range n, s θ (X k) := fun j =>
    ENNReal.toReal_ofReal (div_nonneg (hpos θ (X j)).le hS.le)
  simp only [hw]
  unfold empAvg
  have hn' : ((n : ℝ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn.ne')
  rw [mul_div_mul_left _ _ hn', Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma integral_empCtxLaw (X : ℕ → Z) {n : ℕ} (hn : 0 < n) (hpos : ∀ θ z, 0 < s θ z) {φ : Z → ℝ}
    (hφ : Continuous φ) (θ : Θ) :
    ∫ z, φ z ∂empCtxLaw s X n θ = empAvg X n (fun z' => s θ z' * φ z') / empAvg X n (s θ) := by
  have hS : 0 < ∑ k ∈ Finset.range n, s θ (X k) :=
    Finset.sum_pos (fun k _ => hpos θ (X k)) ⟨0, Finset.mem_range.2 hn⟩
  unfold empCtxLaw
  rw [integral_finsetSum_measure (fun j _ =>
    (integrable_of_continuous' (μ := Measure.dirac (X j)) hφ).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  have hw : ∀ j, (ENNReal.ofReal (s θ (X j) / ∑ k ∈ Finset.range n, s θ (X k))).toReal =
      s θ (X j) / ∑ k ∈ Finset.range n, s θ (X k) := fun j =>
    ENNReal.toReal_ofReal (div_nonneg (hpos θ (X j)).le hS.le)
  simp only [hw]
  unfold empAvg
  have hn' : ((n : ℝ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn.ne')
  rw [mul_div_mul_left _ _ hn', Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end ICLEmp

theorem e_measures_emp_weak : Claims.e_measures_emp_weak := by
  intro Θ Z Ω _ _ _ _ _ _ _ P P0 X s sm sp φ hP0 hs hsm hsb hφ hP hXm hXi hXl
  have hGX := compactGC_of_iid hP0 hP hXm hXi hXl
  have hb : ∀ θ z, sm ≤ s θ z := fun θ z => (hsb θ z).1
  have hpos : ∀ θ z, 0 < s θ z := fun θ z => lt_of_lt_of_le hsm (hb θ z)
  have hsφ : Continuous (Function.uncurry fun θ z => s θ z * φ z) := hs.mul (hφ.comp continuous_snd)
  filter_upwards [hGX Θ s hs, hGX Θ _ hsφ] with ω h1 h2 θn θ hθ
  have hN : Continuous fun θ => ∫ z, s θ z * φ z ∂P0 := continuous_param_integral (P0 := P0) hsφ
  have hD : Continuous fun θ => ∫ z, s θ z ∂P0 := continuous_param_integral (P0 := P0) hs
  have t1 := h2.tendsto_comp hN.continuousAt hθ
  have t2 := h1.tendsto_comp hD.continuousAt hθ
  have hD0 : (∫ z, s θ z ∂P0) ≠ 0 := (normC_pos (P0 := P0) hs hsm hb θ).ne'
  have hlim := t1.div t2 hD0
  rw [integral_ctxLawT hs hsm hb θ φ]
  have heq : (∫ z, s θ z * φ z ∂P0) / (∫ z, s θ z ∂P0) = (∫ z, φ z * s θ z ∂P0) / normC P0 s θ := by
    unfold normC; congr 1; congr 1; funext z; ring
  rw [← heq]
  refine hlim.congr' (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  exact (integral_empCtxLaw (fun i => X i ω) hn hpos hφ (θn n)).symm

theorem e_measures_emp : Claims.e_measures_emp := by
  intro Θ Z Ω _ _ _ _ _ _ _ P P0 X Y m s K sm sp Kmin Kmax hP0 hs hsm hsb hK hKmin hKb hm hP hXm hXi hXl hYm hYi
    hYl
  have hGX := compactGC_of_iid hP0 hP hXm hXi hXl
  have hGY := compactGC_of_iid hP0 hP hYm hYi hYl
  have hb : ∀ θ z, sm ≤ s θ z := fun θ z => (hsb θ z).1
  have hpos : ∀ θ z, 0 < s θ z := fun θ z => lt_of_lt_of_le hsm (hb θ z)
  have hsK : Continuous (Function.uncurry fun (p : Θ × Z) z' => s p.1 z' * K p.2 z') :=
    (hs.comp (continuous_fst.fst.prodMk continuous_snd)).mul (hK.comp (continuous_fst.snd.prodMk continuous_snd))
  have hρc : Continuous (fun p : Θ × Z => coverRho K (ctxLawT P0 s p.1) p.2) :=
    ((e_measures_pop Θ Z P0 s K sm sp Kmin Kmax hP0 hs hsm hsb hK hKmin hKb).2.2.1)
  have hρb := coverRho_bounds (P0 := P0) hs hsm hb hK hKb
  have hlogc : Continuous (Function.uncurry fun θ z => Real.log (coverRho K (ctxLawT P0 s θ) z)) :=
    hρc.log fun p => (lt_of_lt_of_le hKmin (hρb p.1 p.2).1).ne'
  have GC1 := hGX Θ s hs
  have GC2 := hGX (Θ × Z) _ hsK
  have GC3 := hGY Θ _ hlogc
  filter_upwards [GC1, GC2, GC3] with ω h1 h2 h3
  -- part 1
  set CN : ℝ := |sp| * (|Kmin| + |Kmax|)
  have hCN : 0 ≤ CN := by positivity
  have hNb : ∀ p : Θ × Z, |∫ z', s p.1 z' * K p.2 z' ∂P0| ≤ CN := by
    intro p
    have := norm_integral_le_of_norm_le_const (μ := P0) (f := fun z' => s p.1 z' * K p.2 z') (C := CN)
      (ae_of_all _ fun z' => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hpos _ _)]
        have hK1 : |K p.2 z'| ≤ |Kmin| + |Kmax| := by
          rw [abs_le]; constructor <;> cases abs_cases Kmin <;> cases abs_cases Kmax <;>
            linarith [(hKb p.2 z').1, (hKb p.2 z').2]
        exact mul_le_mul ((hsb _ _).2.trans (le_abs_self sp)) hK1 (abs_nonneg _) (abs_nonneg sp))
    simpa [Real.norm_eq_abs] using this
  have hpart1 : TendstoUniformly (fun n (p : Θ × Z) => coverRho K (empCtxLaw s (fun i => X i ω) n p.1) p.2)
      (fun p => coverRho K (ctxLawT P0 s p.1) p.2) atTop := by
    have hdiv := tendstoUniformly_div_of_ge (k := sm) (C := CN)
      (Dn := fun n (p : Θ × Z) => empAvg (fun i => X i ω) n (s p.1)) (D := fun p => ∫ z, s p.1 z ∂P0)
      hsm hCN h2 (h1.comp Prod.fst)
      (Filter.eventually_atTop.2 ⟨1, fun n hn p => empAvg_ge _ hn (hb p.1)⟩)
      (fun p => (normC_bounds (P0 := P0) hs hsb p.1).1) hNb
    refine tu_congr_lim (tu_congr hdiv (Filter.eventually_atTop.2 ⟨1, fun n hn p => ?_⟩)) fun p => ?_
    · exact (coverRho_emp (fun i => X i ω) hn hpos hK p.1 p.2).symm
    · exact (coverRho_pop hs hsm hb p.1 p.2).symm
  refine ⟨hpart1, ?_⟩
  -- part 2
  have hlog := tendstoUniformly_log_of_ge hKmin hpart1
    (Filter.eventually_atTop.2 ⟨1, fun n hn p => by
      rw [coverRho_emp (fun i => X i ω) hn hpos hK p.1 p.2, le_div_iff₀ (lt_of_lt_of_le hsm (empAvg_ge _ hn (hb p.1)))]
      have := empAvg_ge (fun i => X i ω) hn (f := fun z' => s p.1 z' * K p.2 z' - Kmin * s p.1 z') (c := 0)
        (fun z' => by nlinarith [(hKb p.2 z').1, hpos p.1 z'])
      rw [empAvg_sub, empAvg_mul_const] at this
      linarith⟩)
    (fun p => (hρb p.1 p.2).1)
  have h3m := tu_comp_tendsto h3 hm
  rw [Metric.tendstoUniformly_iff] at hlog h3m ⊢
  intro ε hε
  filter_upwards [hlog (ε / 2) (by positivity), h3m (ε / 2) (by positivity)] with n hn1 hn2 θ
  simp only [Real.dist_eq] at hn1 hn2 ⊢
  have e1 := hn2 θ
  have e2 : |empAvg (fun i => Y i ω) (m n) (fun z => Real.log (coverRho K (ctxLawT P0 s θ) z) -
      Real.log (coverRho K (empCtxLaw s (fun i => X i ω) n θ) z))| ≤ ε / 2 :=
    abs_empAvg_le _ _ (by positivity) fun z => (hn1 (θ, z)).le
  rw [empAvg_sub] at e2
  calc |∫ z, Real.log (coverRho K (ctxLawT P0 s θ) z) ∂P0 -
        empAvg (fun i => Y i ω) (m n) (fun z => Real.log (coverRho K (empCtxLaw s (fun i => X i ω) n θ) z))|
      ≤ |∫ z, Real.log (coverRho K (ctxLawT P0 s θ) z) ∂P0 -
          empAvg (fun i => Y i ω) (m n) (fun z => Real.log (coverRho K (ctxLawT P0 s θ) z))| +
        |empAvg (fun i => Y i ω) (m n) (fun z => Real.log (coverRho K (ctxLawT P0 s θ) z)) -
          empAvg (fun i => Y i ω) (m n)
            (fun z => Real.log (coverRho K (empCtxLaw s (fun i => X i ω) n θ) z))| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

theorem e_ulln : Claims.e_ulln := by
  intro Θ Z Ω _ _ _ _ _ _ _ P P0 X Y m s K sm sp Kmin Kmax R Rn lc lK lcn lKn hP0 hs hsm hsb hK hKmin hKb hm hP hXm
    hXi hXl hYm hYi hYl hlc hlK hR
  have hGX := compactGC_of_iid hP0 hP hXm hXi hXl
  have hb : ∀ θ z, sm ≤ s θ z := fun θ z => (hsb θ z).1
  have hpos : ∀ θ z, 0 < s θ z := fun θ z => lt_of_lt_of_le hsm (hb θ z)
  have hslog : Continuous (Function.uncurry fun θ z => s θ z * Real.log (s θ z)) :=
    hs.mul (hs.log fun p => (hpos p.1 p.2).ne')
  have hcovae := e_measures_emp Θ Z Ω P P0 X Y m s K sm sp Kmin Kmax hP0 hs hsm hsb hK hKmin hKb hm hP hXm hXi hXl
    hYm hYi hYl
  have hρb := coverRho_bounds (P0 := P0) hs hsm hb hK hKb
  filter_upwards [hcovae, hGX Θ s hs, hGX Θ _ hslog, hR] with ω hcov hS hA hRω
  -- coverage term
  set BL : ℝ := |Real.log Kmin| + |Real.log Kmax|
  have hCb : ∀ θ, |∫ z, Real.log (coverRho K (ctxLawT P0 s θ) z) ∂P0| ≤ BL := by
    intro θ
    have := norm_integral_le_of_norm_le_const (μ := P0) (C := BL)
      (f := fun z => Real.log (coverRho K (ctxLawT P0 s θ) z))
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]; exact abs_log_le_of_mem hKmin (hρb θ z).1 (hρb θ z).2)
    simpa [Real.norm_eq_abs] using this
  have hT2 := tendstoUniformly_seq_mul hlc hcov.2 hCb
  -- relative entropy term
  set CA : ℝ := |sp| * (|Real.log sm| + |Real.log sp|)
  have hCA : 0 ≤ CA := by positivity
  have hAb : ∀ θ, |∫ z, s θ z * Real.log (s θ z) ∂P0| ≤ CA := by
    intro θ
    have := norm_integral_le_of_norm_le_const (μ := P0) (C := CA) (f := fun z => s θ z * Real.log (s θ z))
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hpos θ z)]
        exact mul_le_mul ((hsb θ z).2.trans (le_abs_self sp)) (abs_log_le_of_mem hsm (hsb θ z).1 (hsb θ z).2)
          (abs_nonneg _) (abs_nonneg sp))
    simpa [Real.norm_eq_abs] using this
  have hDn : ∀ᶠ n in atTop, ∀ θ, sm ≤ empAvg (fun i => X i ω) n (s θ) :=
    Filter.eventually_atTop.2 ⟨1, fun n hn θ => empAvg_ge _ hn (hb θ)⟩
  have hDk : ∀ θ, sm ≤ ∫ z, s θ z ∂P0 := fun θ => (normC_bounds (P0 := P0) hs hsb θ).1
  have hratio := tendstoUniformly_div_of_ge (k := sm) (C := CA) hsm hCA hA hS hDn hDk hAb
  have hlogD := tendstoUniformly_log_of_ge hsm hS hDn hDk
  have hKL : TendstoUniformly (fun n θ => klEmp s (fun i => X i ω) n θ) (fun θ => klPop P0 s θ) atTop :=
    tu_sub hratio hlogD
  have hKLb : ∀ θ, |klPop P0 s θ| ≤ CA / sm + (|Real.log sm| + |Real.log sp|) := by
    intro θ
    unfold klPop normC
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos (lt_of_lt_of_le hsm (hDk θ))]
      exact div_le_div₀ hCA (hAb θ) hsm (hDk θ)
    · exact abs_log_le_of_mem hsm (hDk θ) (normC_bounds (P0 := P0) hs hsb θ).2
  have hT3 := tendstoUniformly_seq_mul hlK hKL hKLb
  exact tu_add (tu_sub hRω hT2) hT3

end StatFormal.Wave24c
