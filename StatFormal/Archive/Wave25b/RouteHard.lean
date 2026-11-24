import StatFormal.Archive.Wave25b.Statements
import StatFormal.Archive.Wave25b.RouteConc
import StatFormal.Archive.OTFD.WaveL3.Proofs
import StatFormal.Archive.OTFD.WaveL2.RouteLimit

/-!
# Route (wave 25b): A `thm:app-hard-diagonal`, fixed-`K` step (untrusted)

At a fixed level `K` everything is lifted to `H`: the assignment plan
`Γ_n = n⁻¹ Σ_i δ_{(X_i, ι_K u_{σ(i)})}` is cyclically monotone in `H` (`⟨ι_K v, x⟩ = ⟨v, Π_K x⟩`), its first marginal
is the empirical law of `X_1, …, X_n` (Varadarajan in `H`) and its second the embedded grid law, so the frozen
`plan_stab_a_uncond` gives `Γ_n ⇀ (Id × G_K)#P`, `G_K` the Hilbert Brenier map of `P` onto `(ι_K Π_K)#μ`. The
strong law for countably many test functions (wave-19a approximation) turns this into
`n⁻¹ Σ_i ‖ι_K u_{σ(i)} − G_K(X_i)‖² → 0` almost surely, for every sequence of optimal assignments, and in expectation
for a measurable selection (bounded convergence).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction

namespace StatFormal.Wave25b

open StatFormal.OTFD.WaveL1 (CycMon CMConc IsCMMapAE Graph LipNull Mom2 Euc inner_embed truncK_sub
  continuous_truncK continuous_embed)
open StatFormal.OTFD.WaveL3 (Mom1)
open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.OTFD.Ranks (IsMin cost)
open StatFormal.OTFD.Wave19a (WeakTo graphLaw sqDisc psiG measurable_psiG psiG_le_one exists_bcf_seq
  measurable_sqDisc)
open TauCeti.Probability (empiricalMeasureOfFintype empiricalMeasure lintegral_empiricalMeasureOfFintype
  lintegral_empiricalMeasure)

/-! ### Cyclical monotonicity of assignment plans -/

section CM
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem isCM_real_of_isMin {n : ℕ} (u z : Fin n → E) (σ : Equiv.Perm (Fin n)) (hσ : IsMin u z σ) :
    TauCeti.IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) (range fun a => (z a, u (σ a))) := by
  intro m xs ys hmem ρ
  choose i hi using hmem
  have hx : ∀ k, xs k = z (i k) := fun k => (congrArg Prod.fst (hi k)).symm
  have hy : ∀ k, ys k = u (σ (i k)) := fun k => (congrArg Prod.snd (hi k)).symm
  have hopt : ∀ π : Equiv.Perm (Fin n), ∑ a, ‖z a - u (σ a)‖ ^ 2 / 2 ≤ ∑ a, ‖z a - u (σ (π a))‖ ^ 2 / 2 := by
    intro π
    rw [← Finset.sum_div, ← Finset.sum_div]
    have := hσ (σ * π)
    unfold cost at this
    exact div_le_div_of_nonneg_right this (by norm_num)
  have key := StatFormal.OTFD.WaveL2.sum_le_sum_perm_of_opt (fun a b => ‖z a - u (σ b)‖ ^ 2 / 2) hopt i ρ
  simpa only [hx, hy] using key

end CM

section Lift
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem cycMon_assign_H (e : ℕ → H) {K n : ℕ} (x : Fin n → H) (u : Fin n → Euc K) (σ : Equiv.Perm (Fin n))
    (hσ : IsMin u (fun a => truncK e K (x a)) σ) :
    CycMon (range fun a => (x a, embed e K (u (σ a)))) := by
  have hK : CycMon (range fun a => (truncK e K (x a), u (σ a))) :=
    (StatFormal.OTFD.WaveL3.cycmon_iff (Euc K) _).2 (isCM_real_of_isMin _ _ σ hσ)
  intro m w hw
  choose i hi using hw
  have := hK m (fun j => (truncK e K (x (i j)), u (σ (i j)))) (fun j => ⟨i j, rfl⟩)
  refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) this
  rw [← hi j, ← hi (finRotate m j)]
  simp only
  rw [inner_embed, truncK_sub]

theorem norm_embed_le {e : ℕ → H} (he : Orthonormal ℝ e) (K : ℕ) (z : Euc K) :
    ‖embed e K z‖ ≤ K * ‖z‖ := by
  unfold embed
  calc ‖∑ k : Fin K, z k • e k‖ ≤ ∑ k : Fin K, ‖z k • e k‖ := norm_sum_le _ _
    _ = ∑ k : Fin K, ‖z k‖ := by simp [norm_smul, he.1]
    _ ≤ ∑ _k : Fin K, ‖z‖ := Finset.sum_le_sum fun k _ => PiLp.norm_apply_le z k
    _ = K * ‖z‖ := by simp

end Lift

/-! ### The fixed-`K` limit -/

section FixedK
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- **Fixed-`K` step, almost surely, for every sequence of optimal assignments.** -/
theorem fixedK_hard {e : ℕ → H} (he : Orthonormal ℝ e) {P : ProbabilityMeasure H}
    (hP : LipNull (P : Measure H)) (hP1 : Mom1 (P : Measure H) ≠ ∞) {K : ℕ} {ν : Measure (Euc K)}
    [IsProbabilityMeasure ν] {G : H → H} (hG : Measurable G)
    (hGpush : (P : Measure H).map G = ν.map (embed e K)) (hGcm : IsCMMapAE (P : Measure H) G) {M : ℝ}
    (hGb : ∀ x, ‖G x‖ ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr] {X : ℕ → Ω → H}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X Pr) (hlaw : ∀ i, Pr.map (X i) = P)
    {u : (n : ℕ) → Fin n → Euc K} {R : ℝ} (hR : ∀ n i, ‖u n i‖ ≤ R)
    (hgrid : ∀ f : Euc K →ᵇ ℝ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i, f (u n i)) atTop (𝓝 (∫ z, f z ∂ν))) :
    ∀ᵐ ω ∂Pr, ∀ σ : (n : ℕ) → Equiv.Perm (Fin n),
      (∀ n, IsMin (u n) (fun j => truncK e K (X j ω)) (σ n)) →
      Tendsto (fun n : ℕ => (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, ‖embed e K (u n (σ n i)) - G (X i ω)‖ₑ ^ 2)
        atTop (𝓝 0) := by
  have hemb : Measurable (embed e K) := (continuous_embed e K).measurable
  set νH : ProbabilityMeasure H := (StatFormal.OTFD.WaveL2.toPM ν).map (embed e K) with hνH
  have hνHm : (νH : Measure H) = ν.map (embed e K) := rfl
  -- the reference is carried by the ball of radius `M`
  have hball : (νH : Measure H) (Metric.closedBall 0 M)ᶜ = 0 := by
    rw [hνHm, ← hGpush, Measure.map_apply hG Metric.isClosed_closedBall.measurableSet.compl]
    have : G ⁻¹' (Metric.closedBall (0 : H) M)ᶜ = ∅ := by
      ext x; simp [hGb x]
    rw [this, measure_empty]
  have hgraph : Measurable fun x => (x, G x) := measurable_id.prodMk hG
  set GP : ProbabilityMeasure (H × H) := P.map (fun x => (x, G x)) with hGP
  -- Varadarajan and the strong law for the test functions
  have hV := StatFormal.Empirical.tendsto_empiricalMeasure_ae_of_iIndepFun (μ := P) hind
    (fun i => ⟨(hX i).aemeasurable, hlaw i⟩)
  obtain ⟨g, hg⟩ := exists_bcf_seq (P : Measure H) hG
  have hS : ∀ᵐ ω ∂Pr, ∀ k, Tendsto (fun n : ℕ => (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, psiG G (g k) (X i ω)) atTop
      (𝓝 (∫⁻ x, psiG G (g k) x ∂(P : Measure H))) :=
    ae_all_iff.2 fun k => slln_fin hX hind hlaw (measurable_psiG hG (g k)) (psiG_le_one G (g k))
  filter_upwards [hV, hS] with ω hVω hSω
  intro σ hσ
  -- the shifted plans
  set pts : (n : ℕ) → Fin (n + 1) → H × H := fun n i => (X i ω, embed e K (u (n + 1) (σ (n + 1) i)))
    with hpts
  set Γ : ℕ → ProbabilityMeasure (H × H) := fun n => empiricalMeasureOfFintype (pts n) with hΓ
  have hfst : ∀ n, (Γ n : Measure (H × H)).fst = empiricalMeasure (fun i => X i ω) n := by
    intro n
    rw [Measure.fst, StatFormal.OTFD.WaveL2.map_emp _ measurable_fst]
    rfl
  have hsnd : ∀ n, (Γ n : Measure (H × H)).snd =
      ((empiricalMeasureOfFintype (u (n + 1))).map (embed e K) : ProbabilityMeasure H) := by
    intro n
    rw [Measure.snd, StatFormal.OTFD.WaveL2.map_emp _ measurable_snd, ProbabilityMeasure.toMeasure_map,
      StatFormal.OTFD.WaveL2.map_emp _ hemb]
    exact StatFormal.OTFD.WaveL2.emp_comp_perm (embed e K ∘ u (n + 1)) (σ (n + 1))
  have hgrid' : Tendsto (fun n => empiricalMeasureOfFintype (u (n + 1))) atTop
      (𝓝 (StatFormal.OTFD.WaveL2.toPM ν)) :=
    StatFormal.OTFD.WaveL2.tendsto_emp_grid (N := fun n => n + 1) (fun n => u (n + 1))
      (fun f => (tendsto_add_atTop_iff_nat 1).2 (hgrid f))
  have hνlim : Tendsto (fun n => (empiricalMeasureOfFintype (u (n + 1))).map (embed e K)) atTop
      (𝓝 νH) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hgrid' (continuous_embed e K)
  have hcm : ∀ n, CMConc (Γ n : Measure (H × H)) := by
    intro n
    refine ⟨range (pts n), (Set.finite_range _).measurableSet, ?_, StatFormal.OTFD.WaveL2.emp_compl_range _⟩
    exact cycMon_assign_H e (fun i : Fin (n + 1) => X i ω) (u (n + 1)) (σ (n + 1)) (hσ (n + 1))
  have hplan : Tendsto Γ atTop (𝓝 GP) :=
    StatFormal.OTFD.WaveL3.plan_stab_a_uncond H P νH G M (fun n => empiricalMeasure (fun i => X i ω) n)
      (fun n => (empiricalMeasureOfFintype (u (n + 1))).map (embed e K)) Γ GP hP hP1 hball hG
      hGpush hGcm hVω hνlim hfst hsnd hcm rfl
  have hw : WeakTo atTop (fun n => (Γ n : Measure (H × H))) (graphLaw (P : Measure H) G) := by
    intro f
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hplan f
  set B := max M (K * R) with hB
  have hQB : ∀ x, ‖G x‖ ≤ B := fun x => (hGb x).trans (le_max_left _ _)
  have hy : ∀ n, ∀ᵐ z ∂(Γ n : Measure (H × H)), ‖z.2‖ ≤ B := by
    intro n
    have h0 := StatFormal.OTFD.WaveL2.emp_compl_range (pts n)
    filter_upwards [ae_iff.2 h0] with z hz
    obtain ⟨i, rfl⟩ := hz
    exact ((norm_embed_le he K _).trans (mul_le_mul_of_nonneg_left (hR _ _) (Nat.cast_nonneg _))).trans
      (le_max_right _ _)
  have hmarg : ∀ k, Tendsto (fun n => ∫⁻ x, psiG G (g k) x ∂((Γ n : Measure (H × H)).map Prod.fst)) atTop
      (𝓝 (∫⁻ x, psiG G (g k) x ∂(P : Measure H))) := by
    intro k
    refine ((tendsto_add_atTop_iff_nat 1).2 (hSω k)).congr fun n => ?_
    change _ = ∫⁻ x, psiG G (g k) x ∂((Γ n : Measure (H × H)).fst)
    rw [hfst, lintegral_empiricalMeasure (measurable_psiG hG (g k)),
      ← Fin.sum_univ_eq_sum_range (fun i => psiG G (g k) (X i ω)) (n + 1)]
  have hconc := conc_det (P : Measure H) hG hQB (fun n => (Γ n : Measure (H × H))) (fun n => inferInstance)
    hw g hg hmarg hy
  refine (tendsto_add_atTop_iff_nat 1).1 (hconc.congr fun n => ?_)
  simp only [hΓ]
  rw [lintegral_empiricalMeasureOfFintype (measurable_sqDisc hG), Fintype.card_fin]
  rfl

theorem enorm_sub_sq_le_of {E : Type*} [NormedAddCommGroup E] {a b : E} {B : ℝ} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) :
    ‖a - b‖ₑ ^ 2 ≤ ENNReal.ofReal ((2 * B) ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
  calc ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le _ _
    _ ≤ 2 * B := by linarith

theorem avg_le (n : ℕ) (t : Fin n → ℝ≥0∞) {c : ℝ≥0∞} (ht : ∀ i, t i ≤ c) :
    (n : ℝ≥0∞)⁻¹ * ∑ i, t i ≤ c := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  calc (n : ℝ≥0∞)⁻¹ * ∑ i, t i ≤ (n : ℝ≥0∞)⁻¹ * ∑ _i : Fin n, c := by gcongr with i; exact ht i
    _ = c := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n), one_mul]

/-- **Fixed-`K` step in expectation** (measurable selection, bounded convergence). -/
theorem fixedK_hard_exp {e : ℕ → H} (he : Orthonormal ℝ e) {P : ProbabilityMeasure H}
    (hP : LipNull (P : Measure H)) (hP1 : Mom1 (P : Measure H) ≠ ∞) {K : ℕ} {ν : Measure (Euc K)}
    [IsProbabilityMeasure ν] {G : H → H} (hG : Measurable G)
    (hGpush : (P : Measure H).map G = ν.map (embed e K)) (hGcm : IsCMMapAE (P : Measure H) G) {M : ℝ}
    (hGb : ∀ x, ‖G x‖ ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr] {X : ℕ → Ω → H}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X Pr) (hlaw : ∀ i, Pr.map (X i) = P)
    {u : (n : ℕ) → Fin n → Euc K} {R : ℝ} (hR : ∀ n i, ‖u n i‖ ≤ R)
    (hgrid : ∀ f : Euc K →ᵇ ℝ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i, f (u n i)) atTop (𝓝 (∫ z, f z ∂ν)))
    {sel : (n : ℕ) → (Fin n → Euc K) → Equiv.Perm (Fin n)} (hsel : ∀ n z, IsMin (u n) z (sel n z))
    (hselm : ∀ n h, MeasurableSet {z | sel n z = h}) :
    (∀ n : ℕ, Measurable fun ω => (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n,
      ‖embed e K (u n (sel n (fun j => truncK e K (X j ω)) i)) - G (X i ω)‖ₑ ^ 2) ∧
    Tendsto (fun n : ℕ => ∫⁻ ω, (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n,
      ‖embed e K (u n (sel n (fun j => truncK e K (X j ω)) i)) - G (X i ω)‖ₑ ^ 2 ∂Pr) atTop (𝓝 0) := by
  have has := fixedK_hard he hP hP1 hG hGpush hGcm hGb hX hind hlaw hR hgrid
  set B := max M (K * R) with hB
  have hz : ∀ n : ℕ, Measurable fun ω => (fun j : Fin n => truncK e K (X j ω)) := fun n =>
    measurable_pi_iff.2 fun j => (continuous_truncK e K).measurable.comp (hX j)
  have hmeas : ∀ n : ℕ, Measurable fun ω => (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n,
      ‖embed e K (u n (sel n (fun j => truncK e K (X j ω)) i)) - G (X i ω)‖ₑ ^ 2 := by
    intro n
    exact measurable_of_fibres (s := fun ω => sel n (fun j => truncK e K (X j ω)))
      (fun h => hz n (hselm n h))
      (φ := fun h ω => (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, ‖embed e K (u n (h i)) - G (X i ω)‖ₑ ^ 2)
      (fun h => by fun_prop)
  have hbd : ∀ (n : ℕ) ω, (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n,
      ‖embed e K (u n (sel n (fun j => truncK e K (X j ω)) i)) - G (X i ω)‖ₑ ^ 2 ≤
        ENNReal.ofReal ((2 * B) ^ 2) := by
    intro n ω
    refine avg_le n _ fun i => enorm_sub_sq_le_of ?_ ((hGb _).trans (le_max_left _ _))
    exact ((norm_embed_le he K _).trans (mul_le_mul_of_nonneg_left (hR _ _) (Nat.cast_nonneg _))).trans
      (le_max_right _ _)
  refine ⟨hmeas, ?_⟩
  have := tendsto_lintegral_of_dominated_convergence (μ := Pr) (fun _ => ENNReal.ofReal ((2 * B) ^ 2)) hmeas
    (fun n => Eventually.of_forall (hbd n)) (by simp [lintegral_const])
    (by filter_upwards [has] with ω hω; exact hω _ fun n => hsel n _)
  simpa using this

end FixedK

/-! ### The diagonal -/

/-- **Diagonal extraction**: `a K n → 0` for each `K` gives a nondecreasing `K_n → ∞` with `a K_n n → 0`. -/
theorem exists_diag (a : ℕ → ℕ → ℝ≥0∞) (ha : ∀ K, Tendsto (a K) atTop (𝓝 0)) :
    ∃ Kn : ℕ → ℕ, Monotone Kn ∧ Tendsto Kn atTop atTop ∧ Tendsto (fun n => a (Kn n) n) atTop (𝓝 0) := by
  have hpos : ∀ K : ℕ, (0 : ℝ≥0∞) < ((K : ℝ≥0∞) + 1)⁻¹ := fun K => by simp
  choose N hN using fun K => eventually_atTop.1 ((tendsto_order.1 (ha K)).2 _ (hpos K))
  set N' : ℕ → ℕ := fun K => (Finset.range (K + 1)).sup N + K with hN'
  have hNN' : ∀ K, N K ≤ N' K := fun K =>
    (Finset.le_sup (f := N) (Finset.mem_range.2 (Nat.lt_succ_self K))).trans (Nat.le_add_right _ _)
  have hKN' : ∀ K, K ≤ N' K := fun K => Nat.le_add_left _ _
  set Kn : ℕ → ℕ := fun n => Nat.findGreatest (fun K => N' K ≤ n) n with hKn
  have hmono : Monotone Kn := fun m n hmn =>
    Nat.findGreatest_mono (fun K hK => le_trans hK hmn) hmn
  have htend : Tendsto Kn atTop atTop := by
    refine tendsto_atTop.2 fun K₀ => eventually_atTop.2 ⟨N' K₀, fun n hn => ?_⟩
    exact Nat.le_findGreatest ((hKN' K₀).trans hn) hn
  refine ⟨Kn, hmono, htend, ?_⟩
  have hinv : Tendsto (fun n => ((Kn n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, Nat.cast_add] using this
    exact h1.comp htend
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop (N' 0)] with n hn
  have hspec : N' (Kn n) ≤ n := Nat.findGreatest_spec (P := fun K => N' K ≤ n) (Nat.zero_le n) hn
  exact (hN (Kn n) n ((hNN' _).trans hspec)).le

end StatFormal.Wave25b
