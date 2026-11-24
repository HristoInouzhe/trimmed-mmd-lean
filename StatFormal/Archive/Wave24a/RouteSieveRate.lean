import StatFormal.Archive.Wave24a.Statements
import StatFormal.Archive.OTFD.WaveL3.RouteHilbert
import StatFormal.Archive.OTFD.Wave8b.RouteBregman
import StatFormal.Archive.OTFD.Wave8b.RouteNaive
import StatFormal.Archive.OTFD.Wave6b.RouteEmpirical
import StatFormal.Archive.OTFD.Wave1.RoutePullback

/-!
# Route — A `cor:app-bijective-rate` (a) and `cor:app-entropic-rate` (untrusted)

Chain of certified results at `K = K_n`: the frozen `emp_bijective_weak` / `app_entropic_weak` bound the empirical
term `A_n = E[n⁻¹Σ‖F̂(x_i) − F_{+,K}(x_i)‖²]` in terms of `E W₂²(ν̂_n, μ_K)`, which the frozen `empirical_wass_rate20`
bounds by `20M²(K+1)n^{−2/(K+4)}` (the ranks `r_i = F_{+,K}(x_i)` are i.i.d. `μ_K`, supported in `B̄(0, M)` by
Bessel); the sieve term `S(K)² = ∫ ‖ι_K F_{+,K}Π_K x − 𝔽_P x‖² dP → 0` is the frozen `sieve_strong_limit_uncond`
(`m₁(P) < ∞` from the second moment). The split `‖ι_K(F̂ − F_{+,K}x) + (ι_K F_{+,K}x − 𝔽_P X)‖² ≤ 2‖·‖² + 2‖·‖²`
(`ι_K` an isometry) gives `E_n ≤ 2A_n + 2S(K_n)²` (consistency only; the paper's Minkowski form is sharper).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave24a

open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.Wave8b (embed)

local notation "𝔼" K => EuclideanSpace ℝ (Fin K)

lemma memLp_two_of_lintegral_aux {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {ρ : Measure E}
    (h : ∫⁻ x, ‖x‖ₑ ^ 2 ∂ρ ≠ ∞) : MemLp id 2 ρ := by
  have hlt : eLpNorm id 2 ρ < ∞ := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      aestronglyMeasurable_id]
    simpa [ENNReal.rpow_two] using h.lt_top
  exact hlt

section Sieve
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma embed_sub' (e : ℕ → H) (K : ℕ) (a b : 𝔼 K) : embed e K (a - b) = embed e K a - embed e K b := by
  simp [embed, sub_smul, Finset.sum_sub_distrib]

lemma norm_sq_add_le (a b : H) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := norm_add_le a b
  have h0 := norm_nonneg (a + b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The pointwise split of the error. -/
lemma split_le {e : ℕ → H} (he : Orthonormal ℝ e) {K n : ℕ} (FK : (𝔼 K) → 𝔼 K) (F : H → H) (Fh : Fin n → 𝔼 K)
    (x : Fin n → H) :
    ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, ‖embed e K (Fh i) - F (x i)‖ ^ 2) ≤
      2 * ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, ‖Fh i - FK (truncK e K (x i))‖ ^ 2) +
        2 * ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, ‖embed e K (FK (truncK e K (x i))) - F (x i)‖ ^ 2) := by
  have hn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  suffices key : (1 / (n : ℝ)) * ∑ i, ‖embed e K (Fh i) - F (x i)‖ ^ 2 ≤
      2 * ((1 / (n : ℝ)) * ∑ i, ‖Fh i - FK (truncK e K (x i))‖ ^ 2) +
        2 * ((1 / (n : ℝ)) * ∑ i, ‖embed e K (FK (truncK e K (x i))) - F (x i)‖ ^ 2) by
    refine (ENNReal.ofReal_le_ofReal key).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (p := 2) (by norm_num),
      ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_ofNat]
  have hpt : ∀ i, ‖embed e K (Fh i) - F (x i)‖ ^ 2 ≤ 2 * ‖Fh i - FK (truncK e K (x i))‖ ^ 2 +
      2 * ‖embed e K (FK (truncK e K (x i))) - F (x i)‖ ^ 2 := by
    intro i
    have hsplit : embed e K (Fh i) - F (x i) = embed e K (Fh i - FK (truncK e K (x i))) +
        (embed e K (FK (truncK e K (x i))) - F (x i)) := by
      rw [embed_sub']; abel
    rw [hsplit]
    refine (norm_sq_add_le _ _).trans ?_
    rw [StatFormal.OTFD.Wave8b.norm_embed e he]
  calc (1 / (n : ℝ)) * ∑ i, ‖embed e K (Fh i) - F (x i)‖ ^ 2
      ≤ (1 / (n : ℝ)) * ∑ i, (2 * ‖Fh i - FK (truncK e K (x i))‖ ^ 2 +
          2 * ‖embed e K (FK (truncK e K (x i))) - F (x i)‖ ^ 2) := by
        gcongr with i; exact hpt i
    _ = 2 * ((1 / (n : ℝ)) * ∑ i, ‖Fh i - FK (truncK e K (x i))‖ ^ 2) +
          2 * ((1 / (n : ℝ)) * ∑ i, ‖embed e K (FK (truncK e K (x i))) - F (x i)‖ ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

/-- The sieve term of identically distributed data is `S(K)²`. -/
lemma sieve_term_eq {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω} {e : ℕ → H} {K n : ℕ} (hn : 1 ≤ n)
    {FK : (𝔼 K) → 𝔼 K} {F : H → H} (hFK : Measurable FK) (hF : Measurable F) {P : Measure H}
    {X : Fin n → Ω → H} (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, Pr.map (X i) = P) :
    ∫⁻ ω, ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, ‖embed e K (FK (truncK e K (X i ω))) - F (X i ω)‖ ^ 2) ∂Pr =
      ∫⁻ x, ‖embed e K (FK (truncK e K x)) - F x‖ₑ ^ 2 ∂P := by
  set g : H → ℝ≥0∞ := fun x => ‖embed e K (FK (truncK e K x)) - F x‖ₑ ^ 2 with hg
  have hgm : Measurable g := by
    have h1 : Measurable fun x => embed e K (FK (truncK e K x)) :=
      (StatFormal.OTFD.WaveL1.continuous_embed e K).measurable.comp
        (hFK.comp (StatFormal.OTFD.WaveL1.continuous_truncK e K).measurable)
    exact ((h1.sub hF).enorm).pow_const 2
  have hpt : ∀ ω, ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, ‖embed e K (FK (truncK e K (X i ω))) - F (X i ω)‖ ^ 2) =
      ∑ i, ENNReal.ofReal (1 / (n : ℝ)) * g (X i ω) := by
    intro ω
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_mul (by positivity), hg]
    simp only
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  simp_rw [hpt]
  rw [lintegral_finset_sum (f := fun i ω => ENNReal.ofReal (1 / (n : ℝ)) * g (X i ω)) _
    (fun i _ => (hgm.comp (hX i)).const_mul _)]
  have hi : ∀ i, ∫⁻ ω, ENNReal.ofReal (1 / (n : ℝ)) * g (X i ω) ∂Pr = ENNReal.ofReal (1 / (n : ℝ)) * ∫⁻ x, g x ∂P :=
    fun i => by
      rw [lintegral_const_mul (f := fun ω => g (X i ω)) _ (hgm.comp (hX i)), ← hlaw i, lintegral_map hgm (hX i)]
  simp_rw [hi]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show (n : ℝ≥0∞) * ENNReal.ofReal (1 / (n : ℝ)) = 1 by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), mul_one_div_cancel hn0.ne',
      ENNReal.ofReal_one], one_mul]

end Sieve

section Aux
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H]

lemma mom1_ne_top' {P : Measure H} [IsProbabilityMeasure P] (h : ∫⁻ x, ‖x‖ₑ ^ 2 ∂P < ⊤) :
    StatFormal.OTFD.WaveL3.Mom1 P ≠ ⊤ := by
  unfold StatFormal.OTFD.WaveL3.Mom1
  refine ne_top_of_le_ne_top (b := ∫⁻ x, (1 + ‖x‖ₑ ^ 2) ∂P) ?_ (lintegral_mono fun x => ?_)
  · rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, h.ne⟩
  · rcases le_total ‖x‖ₑ 1 with hx | hx
    · exact hx.trans le_self_add
    · calc ‖x‖ₑ = ‖x‖ₑ * 1 := (mul_one _).symm
        _ ≤ ‖x‖ₑ * ‖x‖ₑ := by gcongr
        _ = ‖x‖ₑ ^ 2 := (sq _).symm
        _ ≤ 1 + ‖x‖ₑ ^ 2 := le_add_self

lemma integrable_sq_truncK {e : ℕ → H} (he : Orthonormal ℝ e) (K : ℕ) {P : Measure H} [IsProbabilityMeasure P]
    (h : ∫⁻ x, ‖x‖ₑ ^ 2 ∂P < ⊤) : Integrable (fun z : 𝔼 K => ‖z‖ ^ 2) (P.map (truncK e K)) := by
  have hc := StatFormal.OTFD.WaveL1.continuous_truncK e K
  have hL : MemLp id 2 P := memLp_two_of_lintegral_aux h.ne
  have hI : Integrable (fun x : H => ‖x‖ ^ 2) P := by
    simpa using hL.integrable_norm_pow (p := 2) two_ne_zero
  refine (integrable_map_measure (by fun_prop) hc.aemeasurable).2 ?_
  refine hI.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  have := StatFormal.OTFD.Wave1.norm_truncK_le he K x
  gcongr

lemma rankLaw_ball {e : ℕ → H} (he : Orthonormal ℝ e) (K : ℕ) {μ : Measure H} [IsProbabilityMeasure μ] {M : ℝ}
    (hM : μ (Metric.closedBall 0 M)ᶜ = 0) :
    (μ.map (truncK e K)) (Metric.closedBall (0 : 𝔼 K) M) = 1 := by
  have hc := StatFormal.OTFD.WaveL1.continuous_truncK e K
  haveI : IsProbabilityMeasure (μ.map (truncK e K)) :=
    (Measure.isProbabilityMeasure_map_iff hc.aemeasurable).2 inferInstance
  rw [Measure.map_apply hc.measurable Metric.isClosed_closedBall.measurableSet]
  have h1 : μ (Metric.closedBall 0 M) = 1 := by
    rw [← prob_compl_eq_zero_iff Metric.isClosed_closedBall.measurableSet]; exact hM
  refine le_antisymm prob_le_one (h1 ▸ measure_mono fun x hx => ?_)
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hx ⊢
  exact (StatFormal.OTFD.Wave1.norm_truncK_le he K x).trans hx

end Aux

section Steps
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

/-- The ranks `r_i = F_{+,K}(Π_K X_i)` are measurable, independent, with law `μ_K = Π_K#μ`. -/
lemma ranks_facts {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω} {e : ℕ → H} {K n : ℕ}
    {P μ : Measure H} {FK : (𝔼 K) → 𝔼 K} (hFK : Measurable FK)
    (hFKmap : (P.map (truncK e K)).map FK = μ.map (truncK e K)) {X : Fin n → Ω → H}
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X Pr) (hlaw : ∀ i, Pr.map (X i) = P) :
    (∀ i, Measurable fun ω => FK (truncK e K (X i ω))) ∧
      iIndepFun (fun i ω => FK (truncK e K (X i ω))) Pr ∧
      (∀ i, Pr.map (fun ω => FK (truncK e K (X i ω))) = μ.map (truncK e K)) ∧
      (∀ i, Measurable fun ω => truncK e K (X i ω)) ∧ (∀ i, Pr.map (fun ω => truncK e K (X i ω)) = P.map (truncK e K)) := by
  have hc := (StatFormal.OTFD.WaveL1.continuous_truncK e K).measurable
  refine ⟨fun i => (hFK.comp hc).comp (hXm i), hind.comp (fun _ => FK ∘ truncK e K) (fun _ => hFK.comp hc),
    fun i => ?_, fun i => hc.comp (hXm i), fun i => ?_⟩
  · rw [← hFKmap, Measure.map_map hFK hc, ← hlaw i, Measure.map_map (hFK.comp hc) (hXm i)]; rfl
  · rw [← hlaw i, Measure.map_map hc (hXm i)]; rfl

/-- The two-term bound `E_n ≤ 2A_n + 2S(K)²`. -/
lemma two_term {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω} {e : ℕ → H} (he : Orthonormal ℝ e) {K n : ℕ}
    (hn : 1 ≤ n) {P : Measure H} {F : H → H} (hF : Measurable F) {FK : (𝔼 K) → 𝔼 K} (hFK : Measurable FK)
    {X : Fin n → Ω → H} (hXm : ∀ i, Measurable (X i)) (hlaw : ∀ i, Pr.map (X i) = P) (Fh : Ω → Fin n → 𝔼 K) :
    ∫⁻ ω, ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, ‖embed e K (Fh ω i) - F (X i ω)‖ ^ 2) ∂Pr ≤
      2 * ∫⁻ ω, ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, ‖Fh ω i - FK (truncK e K (X i ω))‖ ^ 2) ∂Pr +
        2 * ∫⁻ x, ‖embed e K (FK (truncK e K x)) - F x‖ₑ ^ 2 ∂P := by
  rw [← sieve_term_eq hn hFK hF hXm hlaw]
  have hbm : Measurable fun ω => 2 * ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i,
      ‖embed e K (FK (truncK e K (X i ω))) - F (X i ω)‖ ^ 2) := by
    have hc := (StatFormal.OTFD.WaveL1.continuous_truncK e K).measurable
    have hem := (StatFormal.OTFD.WaveL1.continuous_embed e K).measurable
    refine Measurable.const_mul (ENNReal.measurable_ofReal.comp (Measurable.const_mul ?_ _)) _
    exact Finset.measurable_sum _ fun i _ =>
      (((hem.comp ((hFK.comp hc).comp (hXm i))).sub (hF.comp (hXm i))).norm).pow_const 2
  calc _ ≤ ∫⁻ ω, (2 * ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, ‖Fh ω i - FK (truncK e K (X i ω))‖ ^ 2) +
        2 * ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, ‖embed e K (FK (truncK e K (X i ω))) - F (X i ω)‖ ^ 2)) ∂Pr :=
        lintegral_mono fun ω => split_le he FK F (Fh ω) (fun i => X i ω)
    _ = _ := by
        rw [lintegral_add_right' _ hbm.aemeasurable, lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]

end Steps

theorem app_bijective_rate : Claims.app_bijective_rate := by
  intro H _ _ _ _ _ _ e P μ F M FK Ω _ Pr _ Kn X α β u s f σ hON hspan hLip hmom2 hμM hF hmap hcm hFK hFKmap
    hFKcm hXm hind hlaw hKn hα hβ hcond hassign hB
  haveI : ∀ K, IsProbabilityMeasure ((μ : Measure H).map (truncK e K)) := fun K =>
    (Measure.isProbabilityMeasure_map_iff (StatFormal.OTFD.WaveL1.continuous_truncK e K).aemeasurable).2
      inferInstance
  have hS := (StatFormal.OTFD.WaveL3.sieve_strong_limit_uncond H e P μ F M FK hON hspan hLip (mom1_ne_top' hmom2)
    hμM hF hmap hcm hFK hFKmap hFKcm).comp hKn
  have hup := (ENNReal.Tendsto.const_mul (a := 2) hB (Or.inr ENNReal.ofNat_ne_top)).add
    (ENNReal.Tendsto.const_mul (a := 2) hS (Or.inr ENNReal.ofNat_ne_top))
  simp only [mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => by simp) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨hrm, hrind, hrlaw, hxm, hxlaw⟩ := ranks_facts (Pr := Pr) (e := e) (K := Kn n) (P := (P : Measure H))
    (μ := (μ : Measure H)) (hFK (Kn n)) (hFKmap (Kn n)) (hXm n) (hind n) (hlaw n)
  have hT := two_term hON hn hF (hFK (Kn n)) (hXm n) (hlaw n) (fun ω i => u n (σ n ω i))
  have hA := StatFormal.OTFD.Wave8b.emp_bijective_weak (Kn n) n Ω Pr ((P : Measure H).map (truncK e (Kn n)))
    ((μ : Measure H).map (truncK e (Kn n))) (fun i ω => truncK e (Kn n) (X n i ω)) (FK (Kn n)) (u n) (s n) (f n)
    (α n) (β n) (σ n) hn (hα n) hxm hxlaw (integrable_sq_truncK hON (Kn n) hmom2) (hβ n) (hcond n) (hassign n)
  have hW := StatFormal.OTFD.Wave6b.empirical_wass_rate20 (Kn n) n M 0 ((μ : Measure H).map (truncK e (Kn n))) Ω Pr
    (fun i ω => FK (Kn n) (truncK e (Kn n) (X n i ω))) hn (rankLaw_ball hON (Kn n) hμM) hrm hrind hrlaw
  refine hT.trans (add_le_add ?_ le_rfl)
  gcongr
  refine hA.trans ?_
  gcongr

theorem app_entropic_rate : Claims.app_entropic_rate := by
  intro H _ _ _ _ _ _ e P μ F M FK Ω _ Pr _ Kn X mn α β ε u s f π hON hspan hLip hmom2 hμM hF hmap hcm hFK hFKmap
    hFKcm hXm hind hlaw hKn hm hα hε hβ hcond hplan hJ hE
  haveI : ∀ K, IsProbabilityMeasure ((μ : Measure H).map (truncK e K)) := fun K =>
    (Measure.isProbabilityMeasure_map_iff (StatFormal.OTFD.WaveL1.continuous_truncK e K).aemeasurable).2
      inferInstance
  have hS := (StatFormal.OTFD.WaveL3.sieve_strong_limit_uncond H e P μ F M FK hON hspan hLip (mom1_ne_top' hmom2)
    hμM hF hmap hcm hFK hFKmap hFKcm).comp hKn
  set c0 : ℝ := max (20 * M ^ 2) 1 with hc0
  have hc01 : 1 ≤ c0 := le_max_right _ _
  set C : ℝ≥0∞ := ENNReal.ofReal 4 * ENNReal.ofReal c0 ^ (1 / 2 : ℝ) with hC
  have hCtop : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have hEe := ENNReal.tendsto_ofReal hE
  rw [ENNReal.ofReal_zero] at hEe
  have hup := (ENNReal.Tendsto.const_mul (a := 2) ((ENNReal.Tendsto.const_mul hJ (Or.inr hCtop)).add hEe)
    (Or.inr ENNReal.ofNat_ne_top)).add (ENNReal.Tendsto.const_mul (a := 2) hS (Or.inr ENNReal.ofNat_ne_top))
  simp only [mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => by simp) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨hrm, hrind, hrlaw, hxm, hxlaw⟩ := ranks_facts (Pr := Pr) (e := e) (K := Kn n) (P := (P : Measure H))
    (μ := (μ : Measure H)) (hFK (Kn n)) (hFKmap (Kn n)) (hXm n) (hind n) (hlaw n)
  have hT := two_term hON hn hF (hFK (Kn n)) (hXm n) (hlaw n)
    (fun ω i => StatFormal.OTFD.Wave8b.entBary (π n ω) (u n) i)
  have hA := StatFormal.OTFD.Wave8b.app_entropic_weak (Kn n) n (mn n) Ω Pr
    ((P : Measure H).map (truncK e (Kn n))) ((μ : Measure H).map (truncK e (Kn n)))
    (fun i ω => truncK e (Kn n) (X n i ω)) (FK (Kn n)) (u n) (s n) (f n) (α n) (β n) (ε n) (π n) hn (hm n) (hα n)
    (hε n) hxm hxlaw (integrable_sq_truncK hON (Kn n) hmom2) (hβ n) (hcond n) (hplan n)
  have hW := StatFormal.OTFD.Wave6b.empirical_wass_rate20 (Kn n) n M 0 ((μ : Measure H).map (truncK e (Kn n))) Ω Pr
    (fun i ω => FK (Kn n) (truncK e (Kn n) (X n i ω))) hn (rankLaw_ball hON (Kn n) hμM) hrm hrind hrlaw
  refine hT.trans (add_le_add ?_ le_rfl)
  gcongr
  refine hA.trans (add_le_add ?_ le_rfl)
  -- the Wasserstein part
  set σ2 := ∫ z, ‖z‖ ^ 2 ∂((P : Measure H).map (truncK e (Kn n))) with hσ2
  set a : ℝ := ((Kn n : ℝ) + 1) * (n : ℝ) ^ (-(2 : ℝ) / ((Kn n : ℝ) + 4)) with ha
  have ha0 : 0 ≤ a := by positivity
  set W2 := TauCeti.wassersteinEDist 2 (StatFormal.OTFD.Wave6b.empMeasure (u n))
    ((μ : Measure H).map (truncK e (Kn n))) ^ 2 with hW2
  have h20 : ENNReal.ofReal (20 * M ^ 2 * ((Kn n : ℝ) + 1) * (n : ℝ) ^ (-(2 : ℝ) / ((Kn n : ℝ) + 4))) + W2 ≤
      ENNReal.ofReal c0 * (ENNReal.ofReal a + W2) := by
    have h1 : ENNReal.ofReal (20 * M ^ 2 * ((Kn n : ℝ) + 1) * (n : ℝ) ^ (-(2 : ℝ) / ((Kn n : ℝ) + 4))) ≤
        ENNReal.ofReal c0 * ENNReal.ofReal a := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [show 20 * M ^ 2 * ((Kn n : ℝ) + 1) * (n : ℝ) ^ (-(2 : ℝ) / ((Kn n : ℝ) + 4)) = 20 * M ^ 2 * a by
        rw [ha]; ring]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) ha0
    have h2 : W2 ≤ ENNReal.ofReal c0 * W2 := by
      calc W2 = 1 * W2 := (one_mul _).symm
        _ ≤ ENNReal.ofReal c0 * W2 := by
          gcongr; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hc01
    calc _ ≤ ENNReal.ofReal c0 * ENNReal.ofReal a + ENNReal.ofReal c0 * W2 := _root_.add_le_add h1 h2
      _ = _ := (mul_add _ _ _).symm
  calc ENNReal.ofReal (4 / α n * √(β n ^ 2 + σ2)) *
        (∫⁻ ω, TauCeti.wassersteinEDist 2 (StatFormal.OTFD.Wave6b.empMeasure fun i =>
          FK (Kn n) (truncK e (Kn n) (X n i ω))) ((μ : Measure H).map (truncK e (Kn n))) ^ 2 ∂Pr + W2) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (4 / α n * √(β n ^ 2 + σ2)) * (ENNReal.ofReal c0 * (ENNReal.ofReal a + W2)) ^ (1 / 2 : ℝ) := by
        gcongr
        exact (add_le_add hW le_rfl).trans h20
    _ = C * (ENNReal.ofReal (√(β n ^ 2 + σ2) / α n) * (ENNReal.ofReal a + W2) ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          show 4 / α n * √(β n ^ 2 + σ2) = 4 * (√(β n ^ 2 + σ2) / α n) by ring,
          ENNReal.ofReal_mul (by norm_num), hC]
        ring

example : Claims.app_bijective_rate := app_bijective_rate
example : Claims.app_entropic_rate := app_entropic_rate

end StatFormal.Wave24a
