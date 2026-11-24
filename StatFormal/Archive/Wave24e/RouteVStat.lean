import StatFormal.Archive.Wave24e.Statements
import StatFormal.Lib.Empirical.Varadarajan
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Route — ICL `lem:cond-vstat`, `lem:e-vstat` (untrusted)

Instead of the printed Stone–Weierstrass argument:
* `tendstoUniformly_integral_pi`: if `ν_n → ν` weakly on a compact metric `𝒵`, then `ν_n^{⊗M} → ν^{⊗M}` weakly
  (Mathlib `ProbabilityMeasure.continuous_pi`), and for a continuous `ψ` on the compact `A × 𝒵^M` the convergence
  `∫ ψ_a dν_n^{⊗M} → ∫ ψ_a dν^{⊗M}` is uniform in `a` (uniform continuity and a finite net of `A`).
* `integral_pi_empirical`: the V-statistic is the integral against the `M`-fold product of the empirical measure.
* Varadarajan's theorem (`Foundations/Empirical`) gives the weak convergence almost surely.
* `lem:e-vstat`: the weighted V-statistic is `V_n(θ)/c_{θ,n}^M` with `V_n` the V-statistic of `∏_k s_θ(t_k) H_θ(t)`
  and `c_{θ,n} = P_n s_θ ∈ [s₋, s₊]`; both converge uniformly, and the quotient is controlled explicitly.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StatFormal.Wave24e

section Core

variable {A Z : Type*} [MetricSpace A] [CompactSpace A] [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
  [BorelSpace Z] {M : ℕ}

/-- The section `t ↦ ψ(a, t)` as a bounded continuous function. -/
def secBCF (ψ : A × (Fin M → Z) → ℝ) (hψ : Continuous ψ) (a : A) : (Fin M → Z) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun t => ψ (a, t), hψ.comp (Continuous.prodMk_right a)⟩

lemma secBCF_apply (ψ : A × (Fin M → Z) → ℝ) (hψ : Continuous ψ) (a : A) (t : Fin M → Z) :
    secBCF ψ hψ a t = ψ (a, t) := rfl

lemma abs_integral_sub_le_dist (ρ : ProbabilityMeasure (Fin M → Z)) (f g : (Fin M → Z) →ᵇ ℝ) :
    |∫ t, f t ∂(ρ : Measure (Fin M → Z)) - ∫ t, g t ∂(ρ : Measure (Fin M → Z))| ≤ dist f g := by
  rw [← integral_sub (f.integrable _) (g.integrable _)]
  have h := BoundedContinuousFunction.norm_integral_le_norm (μ := (ρ : Measure (Fin M → Z))) (f - g)
  rw [dist_eq_norm]
  simpa [Real.norm_eq_abs] using h

theorem tendstoUniformly_integral_pi (ψ : A × (Fin M → Z) → ℝ) (hψ : Continuous ψ)
    {ν : ℕ → ProbabilityMeasure Z} {ν₀ : ProbabilityMeasure Z} (hν : Tendsto ν atTop (𝓝 ν₀)) :
    TendstoUniformly (fun n a => ∫ t, ψ (a, t) ∂(Measure.pi fun _ : Fin M => (ν n : Measure Z)))
      (fun a => ∫ t, ψ (a, t) ∂(Measure.pi fun _ : Fin M => (ν₀ : Measure Z))) atTop := by
  set ρ : ℕ → ProbabilityMeasure (Fin M → Z) := fun n => ProbabilityMeasure.pi fun _ => ν n
  set ρ₀ : ProbabilityMeasure (Fin M → Z) := ProbabilityMeasure.pi fun _ => ν₀
  have hρ : Tendsto ρ atTop (𝓝 ρ₀) :=
    ((ProbabilityMeasure.continuous_pi (α := fun _ : Fin M => Z)).tendsto _).comp
      (tendsto_pi_nhds.2 fun _ => hν)
  have hint : ∀ a, Tendsto (fun n => ∫ t, secBCF ψ hψ a t ∂(ρ n : Measure (Fin M → Z))) atTop
      (𝓝 (∫ t, secBCF ψ hψ a t ∂(ρ₀ : Measure (Fin M → Z)))) := fun a =>
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hρ) (secBCF ψ hψ a)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have huc : UniformContinuous ψ := CompactSpace.uniformContinuous_of_continuous hψ
  obtain ⟨δ, hδ, hδψ⟩ := Metric.uniformContinuous_iff.1 huc (ε / 4) (by positivity)
  have hsec : ∀ a b : A, dist a b < δ → dist (secBCF ψ hψ a) (secBCF ψ hψ b) ≤ ε / 4 := by
    intro a b hab
    refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun t => ?_
    rw [secBCF_apply, secBCF_apply]
    refine (hδψ ?_).le
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact hab
  obtain ⟨T, -, hTfin, hcover⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_univ (X := A)).totallyBounded δ hδ
  have hev : ∀ᶠ n in atTop, ∀ b ∈ T, dist (∫ t, secBCF ψ hψ b t ∂(ρ₀ : Measure (Fin M → Z)))
      (∫ t, secBCF ψ hψ b t ∂(ρ n : Measure (Fin M → Z))) < ε / 4 :=
    (hTfin.eventually_all).2 fun b _ => by
      have := (hint b).eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 4))
      filter_upwards [this] with n hn
      rw [dist_comm]; exact hn
  filter_upwards [hev] with n hn a
  have hcov := hcover (mem_univ a)
  rw [mem_iUnion₂] at hcov
  obtain ⟨b, hbT, hab⟩ := hcov
  rw [Metric.mem_ball] at hab
  have h1 := abs_integral_sub_le_dist ρ₀ (secBCF ψ hψ a) (secBCF ψ hψ b)
  have h2 := abs_integral_sub_le_dist (ρ n) (secBCF ψ hψ a) (secBCF ψ hψ b)
  have h3 := hn b hbT
  have hd := hsec a b hab
  simp only [secBCF_apply] at h1 h2 h3
  rw [Real.dist_eq] at h3 ⊢
  change |(∫ t, ψ (a, t) ∂(ρ₀ : Measure (Fin M → Z))) - ∫ t, ψ (a, t) ∂(ρ n : Measure (Fin M → Z))| < ε
  set Ia0 := ∫ t, ψ (a, t) ∂(ρ₀ : Measure (Fin M → Z))
  set Ib0 := ∫ t, ψ (b, t) ∂(ρ₀ : Measure (Fin M → Z))
  set Ian := ∫ t, ψ (a, t) ∂(ρ n : Measure (Fin M → Z))
  set Ibn := ∫ t, ψ (b, t) ∂(ρ n : Measure (Fin M → Z))
  have t1 := abs_sub_le Ia0 Ib0 Ian
  have t2 := abs_sub_le Ib0 Ibn Ian
  rw [abs_sub_comm Ibn Ian] at t2
  linarith

end Core

section Empirical

open TauCeti.Probability

variable {Z : Type*} [MeasurableSpace Z] {M : ℕ}

lemma pi_indicator_one (s : Fin M → Set Z) (x : Fin M → Z) :
    (univ.pi s).indicator (1 : (Fin M → Z) → ℝ≥0∞) x = ∏ k, (s k).indicator 1 (x k) := by
  by_cases h : x ∈ univ.pi s
  · rw [indicator_of_mem h]
    symm
    exact Finset.prod_eq_one fun k _ => by rw [indicator_of_mem ((mem_univ_pi.1 h) k)]; rfl
  · obtain ⟨k, hk⟩ : ∃ k, x k ∉ s k := by simpa [mem_univ_pi] using h
    rw [indicator_of_notMem h]
    exact (Finset.prod_eq_zero (Finset.mem_univ k) (by rw [indicator_of_notMem hk])).symm

lemma pi_empirical {n : ℕ} (z : Fin (n + 1) → Z) :
    Measure.pi (fun _ : Fin M => (empiricalMeasureOfFintype z : Measure Z)) =
      ∑ j : Fin M → Fin (n + 1), (((n + 1 : ℕ) : ℝ≥0∞)⁻¹) ^ M • Measure.dirac (z ∘ j) := by
  refine Measure.pi_eq fun s hs => ?_
  simp only [empiricalMeasureOfFintype_toMeasure, Measure.coe_finset_sum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (MeasurableSet.univ_pi hs),
    Measure.dirac_apply' _ (hs _), Fintype.card_fin]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pi_indicator_one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

lemma integral_pi_empirical [MeasurableSingletonClass Z] {n : ℕ} (z : Fin (n + 1) → Z)
    (f : (Fin M → Z) → ℝ) :
    ∫ t, f t ∂(Measure.pi fun _ : Fin M => (empiricalMeasureOfFintype z : Measure Z)) =
      (1 / ((n + 1 : ℕ) : ℝ) ^ M) * ∑ j : Fin M → Fin (n + 1), f (z ∘ j) := by
  rw [pi_empirical, integral_finset_sum_measure fun j _ =>
    (integrable_dirac (by simp)).smul_measure (by simp)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, Nat.cast_add, Nat.cast_one]
  rw [ENNReal.toReal_add (by simp) (by simp)]
  simp

end Empirical

lemma tendstoUniformly_of_succ {X : Type*} {G : ℕ → X → ℝ} {f : X → ℝ}
    (h : TendstoUniformly (fun n => G (n + 1)) f atTop) : TendstoUniformly G f atTop := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h ε hε)
  refine eventually_atTop.2 ⟨N + 1, fun n hn x => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact hN m (by omega) x

/-- The almost-sure uniform law for V-statistics along the pool, in the shifted (`n + 1` points) form. -/
lemma vstat_ae {A Z Ω : Type*} [MetricSpace A] [CompactSpace A] [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω] {P : Measure Ω} {P₀ : Measure Z}
    [IsProbabilityMeasure P₀] {M : ℕ} {ψ : A × (Fin M → Z) → ℝ} {Zs : ℕ → Ω → Z}
    (hψ : Continuous ψ) (hm : ∀ i, Measurable (Zs i)) (hind : iIndepFun Zs P) (hlaw : ∀ i, P.map (Zs i) = P₀) :
    ∀ᵐ ω ∂P, TendstoUniformly (fun n a => vStat ψ (fun i : Fin n => Zs i ω) a)
        (fun a => ∫ t, ψ (a, t) ∂(Measure.pi fun _ : Fin M => P₀)) atTop := by
  set μ0 : ProbabilityMeasure Z := ⟨P₀, inferInstance⟩
  have hlaw' : ∀ i, HasLaw (Zs i) (μ0 : Measure Z) P := fun i => ⟨(hm i).aemeasurable, hlaw i⟩
  filter_upwards [StatFormal.Empirical.tendsto_empiricalMeasure_ae_of_iIndepFun hind hlaw'] with ω hω
  have hcore := tendstoUniformly_integral_pi ψ hψ hω
  refine tendstoUniformly_of_succ ((tendstoUniformly_congr (Eventually.of_forall fun n => funext fun a => ?_)).1 hcore)
  show ∫ t, ψ (a, t) ∂(Measure.pi fun _ : Fin M =>
      (TauCeti.Probability.empiricalMeasureOfFintype (fun i : Fin (n + 1) => Zs i ω) : Measure Z)) = _
  rw [integral_pi_empirical]
  simp only [vStat]

theorem cond_vstat : Claims.cond_vstat := by
  intro A Z Ω _ _ _ _ _ _ _ P _ P₀ _ M ψ Zs hψ hm hind hlaw
  exact vstat_ae hψ hm hind hlaw

lemma tu_quot {X : Type*} {M : ℕ} {F G : ℕ → X → ℝ} {f g : X → ℝ} (hF : TendstoUniformly F f atTop)
    (hG : TendstoUniformly G g atTop) {B lo hi : ℝ} (hlo : 0 < lo) (hf : ∀ x, |f x| ≤ B)
    (hg : ∀ x, lo ≤ g x ∧ g x ≤ hi) (hGb : ∀ᶠ n in atTop, ∀ x, lo ≤ G n x ∧ G n x ≤ hi) :
    TendstoUniformly (fun n x => F n x / G n x ^ M) (fun x => f x / g x ^ M) atTop := by
  set K : Set (ℝ × ℝ) := Icc (-(B + 1)) (B + 1) ×ˢ Icc lo hi
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hΦ : ContinuousOn (fun p : ℝ × ℝ => p.1 / p.2 ^ M) K :=
    continuousOn_fst.div (continuousOn_snd.pow M) fun p hp => pow_ne_zero _ (by linarith [hp.2.1])
  have huc := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hΦ)
  rw [Metric.tendstoUniformly_iff] at hF hG ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδK⟩ := huc ε hε
  filter_upwards [hF (min δ 1) (by positivity), hG δ hδ, hGb] with n hFn hGn hGbn x
  have h1 := hFn x
  have h2 := hGn x
  rw [Real.dist_eq] at h1 h2
  have hfx := hf x
  have hmin1 : min δ 1 ≤ 1 := min_le_right _ _
  have hminδ : min δ 1 ≤ δ := min_le_left _ _
  refine hδK (f x, g x) ⟨⟨?_, ?_⟩, hg x⟩ (F n x, G n x) ⟨⟨?_, ?_⟩, hGbn x⟩ ?_
  · linarith [neg_abs_le (f x)]
  · linarith [le_abs_self (f x)]
  · linarith [neg_abs_le (f x), (abs_lt.1 h1).2]
  · linarith [le_abs_self (f x), (abs_lt.1 h1).1]
  · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt (by linarith) h2

lemma cont_integrable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Continuous f) :
    Integrable f μ :=
  (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩).integrable μ

theorem e_vstat : Claims.e_vstat := by
  intro Θ Z Ω _ _ _ _ _ _ _ P _ P₀ _ M s H sLo sHi Zs hs hH hlo hb hm hind hlaw
  set ψ1 : Θ × (Fin M → Z) → ℝ := fun x => (∏ k, s (x.1, x.2 k)) * H x with hψ1def
  have hψ1 : Continuous ψ1 :=
    (continuous_finset_prod _ fun k _ =>
      hs.comp (continuous_fst.prodMk ((continuous_apply k).comp continuous_snd))).mul hH
  set ψ2 : Θ × (Fin 1 → Z) → ℝ := fun x => s (x.1, x.2 0) with hψ2def
  have hψ2 : Continuous ψ2 := hs.comp (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
  obtain ⟨BH, hBH⟩ : ∃ C, ∀ x, ‖H x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hH).isBounded.exists_norm_le
    exact ⟨C, fun x => hC _ ⟨x, mem_univ _, rfl⟩⟩
  filter_upwards [vstat_ae hψ1 hm hind hlaw, vstat_ae hψ2 hm hind hlaw] with ω h1 h2
  set C0 : Θ → ℝ := fun θ => ∫ z, s (θ, z) ∂P₀ with hC0
  have hc0 : ∀ θ, ∫ t, ψ2 (θ, t) ∂(Measure.pi fun _ : Fin 1 => P₀) = C0 θ := fun θ =>
    (measurePreserving_funUnique P₀ (Fin 1)).integral_comp' (fun z => s (θ, z))
  have hsint : ∀ θ, Integrable (fun z => s (θ, z)) P₀ := fun θ =>
    cont_integrable P₀ (hs.comp (Continuous.prodMk_right θ))
  have hC0b : ∀ θ, sLo ≤ C0 θ ∧ C0 θ ≤ sHi := fun θ => by
    constructor
    · have := integral_mono (integrable_const sLo) (hsint θ) fun z => (hb (θ, z)).1
      simpa using this
    · have := integral_mono (hsint θ) (integrable_const sHi) fun z => (hb (θ, z)).2
      simpa using this
  have hV0b : ∀ θ, |∫ t, ψ1 (θ, t) ∂(Measure.pi fun _ : Fin M => P₀)| ≤ sHi ^ M * BH := fun θ => by
    have := norm_integral_le_of_norm_le_const (μ := Measure.pi fun _ : Fin M => P₀)
      (f := fun t => ψ1 (θ, t)) (C := sHi ^ M * BH) (Eventually.of_forall fun t => by
        simp only [ψ1, norm_mul, norm_prod]
        have hprod : ∏ k, ‖s (θ, t k)‖ ≤ sHi ^ M := by
          calc ∏ k, ‖s (θ, t k)‖ ≤ ∏ _k : Fin M, sHi :=
                Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => by
                  rw [Real.norm_of_nonneg (le_trans hlo.le (hb _).1)]; exact (hb _).2
            _ = sHi ^ M := by simp
        calc (∏ k, ‖s (θ, t k)‖) * ‖H (θ, t)‖ ≤ (∏ k, ‖s (θ, t k)‖) * BH :=
              mul_le_mul_of_nonneg_left (hBH _) (Finset.prod_nonneg fun k _ => norm_nonneg _)
          _ ≤ sHi ^ M * BH := mul_le_mul_of_nonneg_right hprod (le_trans (norm_nonneg _) (hBH (θ, t))))
    simpa using this
  have hcn : ∀ n : ℕ, 1 ≤ n → ∀ θ, vStat ψ2 (fun i : Fin n => Zs i ω) θ =
      (1 / (n : ℝ)) * ∑ l : Fin n, s (θ, Zs l ω) := fun n hn θ => by
    simp only [vStat, ψ2, pow_one]
    congr 1
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) _ _ fun j => rfl
  have hcnb : ∀ n : ℕ, 1 ≤ n → ∀ θ, sLo ≤ vStat ψ2 (fun i : Fin n => Zs i ω) θ ∧
      vStat ψ2 (fun i : Fin n => Zs i ω) θ ≤ sHi := fun n hn θ => by
    rw [hcn n hn θ]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hlow : (n : ℝ) * sLo ≤ ∑ l : Fin n, s (θ, Zs l ω) := by
      have := Finset.sum_le_sum (s := Finset.univ) fun (l : Fin n) (_ : l ∈ Finset.univ) => (hb (θ, Zs l ω)).1
      simpa using this
    have hup : ∑ l : Fin n, s (θ, Zs l ω) ≤ n * sHi := by
      have := Finset.sum_le_sum (s := Finset.univ) fun (l : Fin n) (_ : l ∈ Finset.univ) => (hb (θ, Zs l ω)).2
      simpa using this
    constructor
    · rw [one_div, le_inv_mul_iff₀ hn']; linarith
    · rw [one_div, inv_mul_le_iff₀ hn']; linarith
  have hq := tu_quot (M := M) h1 h2 hlo (B := sHi ^ M * BH) hV0b
    (fun θ => by rw [hc0]; exact hC0b θ)
    (eventually_atTop.2 ⟨1, fun n hn θ => hcnb n hn θ⟩)
  have hlim : (fun θ => (∫ t, ψ1 (θ, t) ∂(Measure.pi fun _ : Fin M => P₀)) /
      (∫ t, ψ2 (θ, t) ∂(Measure.pi fun _ : Fin 1 => P₀)) ^ M) = wPop P₀ s H := by
    funext θ
    rw [hc0, wPop]
    rw [← integral_div]
    congr 1
    funext t
    simp only [ψ1, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [hlim] at hq
  refine (tendstoUniformly_congr (eventually_atTop.2 ⟨1, fun n hn => funext fun θ => ?_⟩)).1 hq
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hS : 0 < ∑ l : Fin n, s (θ, Zs l ω) :=
    Finset.sum_pos (fun l _ => lt_of_lt_of_le hlo (hb _).1) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  show vStat ψ1 (fun i : Fin n => Zs i ω) θ / vStat ψ2 (fun i : Fin n => Zs i ω) θ ^ M =
    wVStat s H (fun i : Fin n => Zs i ω) θ
  rw [hcn n hn θ]
  simp only [vStat, wVStat, ψ1, Function.comp_apply, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp
  rw [div_pow]
  field_simp

end StatFormal.Wave24e
