import StatFormal.Archive.WaveP1d.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Rearrangement
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.ParallelComp

/-!
# Route: robust equality paper 2 `lem:delta-inf` for general laws (untrusted)

The paper's proof (`app_proofs.tex:34-39`):
* `≥`: a coupling `γ` of `μ₀, μ₁` pushed forward by `(h, h)` couples `h#μ₀` and `h#μ₁` with the same cost;
* `≤`: take the monotone (quantile) coupling `π` of `h#μ₀, h#μ₁`, optimal by Tau Ceti's quantile formula for `W₂`; let
  `k_s(u, ·)` be the conditional law of `X` given `h(X) = u` under `μ_s` (Mathlib's `condKernel` of the law of
  `(h(X), X)`, standard Borel); draw `(U, V) ∼ π`, then `X ∼ k₀(U, ·)`, `Y ∼ k₁(V, ·)` independently
  (`π ⊗ₘ (k₀ ∥ₖ k₁)`). Its `(X, Y)`-marginal couples `μ₀, μ₁`, and `(h(X), h(Y)) = (U, V)` almost surely, so its cost
  is `W₂²`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set
open scoped ENNReal

namespace StatFormal.WaveP1d

namespace RouteDeltaInf

variable {K : Type*} [MeasurableSpace K]

lemma edist_sq_eq (a b : ℝ) : edist a b ^ 2 = ENNReal.ofReal ((a - b) ^ 2) := by
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- `W₂^2` as the second moment of the distance along a plan. -/
lemma eLpNorm_two_sq {X : Type*} [MeasurableSpace X] (π : Measure X) {f : X → ℝ≥0∞}
    (hf : AEStronglyMeasurable f π) :
    eLpNorm f 2 π ^ 2 = ∫⁻ x, f x ^ 2 ∂π := by
  have := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := π) (p := 2) two_ne_zero
  simp only [NNReal.coe_ofNat, enorm_eq_self] at this
  rw [show (2 : ℝ≥0∞) = ((2 : NNReal) : ℝ≥0∞) by rfl]
  have h2 : ∀ y : ℝ≥0∞, y ^ (2 : ℝ) = y ^ 2 := fun y => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  simp only [h2] at this
  exact this hf


/-- The transport cost of the monotone coupling is `W₂²`. -/
lemma W2_sq_quantileCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinEDist 2 μ ν ^ 2 =
      ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2) ∂(μ.quantileCoupling ν) := by
  rw [wassersteinEDist_eq_eLpNorm_quantile_sub one_le_two, ← eLpNorm_edist_quantileCoupling,
    eLpNorm_two_sq _ measurable_edist.aestronglyMeasurable]
  simp only [edist_sq_eq]

/-- Every coupling of the projected laws costs at least `W₂²`. -/
lemma W2_sq_le_of_coupling (μ ν : Measure ℝ) {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν) :
    wassersteinEDist 2 μ ν ^ 2 ≤ ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2) ∂π := by
  have h : wassersteinEDist 2 μ ν ≤ eLpNorm (fun z : ℝ × ℝ => edist z.1 z.2) 2 π :=
    iInf₂_le π hπ
  calc wassersteinEDist 2 μ ν ^ 2 ≤ eLpNorm (fun z : ℝ × ℝ => edist z.1 z.2) 2 π ^ 2 := by gcongr
    _ = _ := by
      rw [eLpNorm_two_sq _ measurable_edist.aestronglyMeasurable]
      simp only [edist_sq_eq]


lemma W2_sq_le_lift {μ₀ μ₁ : Measure K} {h : K → ℝ} (hh : Measurable h) {γ : Measure (K × K)}
    (hγ : IsCoupling γ μ₀ μ₁) :
    wassersteinEDist 2 (μ₀.map h) (μ₁.map h) ^ 2 ≤ ∫⁻ z, ENNReal.ofReal ((h z.1 - h z.2) ^ 2) ∂γ := by
  have hm : Measurable fun z : K × K => (h z.1, h z.2) := by fun_prop
  have hπ : IsCoupling (γ.map fun z : K × K => (h z.1, h z.2)) (μ₀.map h) (μ₁.map h) := by
    constructor
    · rw [Measure.fst, Measure.map_map measurable_fst hm, ← hγ.fst_eq, Measure.fst,
        Measure.map_map hh measurable_fst]; rfl
    · rw [Measure.snd, Measure.map_map measurable_snd hm, ← hγ.snd_eq, Measure.snd,
        Measure.map_map hh measurable_snd]; rfl
  have := W2_sq_le_of_coupling _ _ hπ
  rwa [lintegral_map (by fun_prop) hm] at this


section Fibre
variable [StandardBorelSpace K] [Nonempty K]

/-- The fibre kernel of `μ` along `h`: the conditional law of `X` given `h(X) = s`. -/
abbrev fib (μ : Measure K) [IsProbabilityMeasure μ] (h : K → ℝ) : Kernel ℝ K :=
  (μ.map fun x => (h x, x)).condKernel

omit [StandardBorelSpace K] [Nonempty K] in
lemma fst_graph (μ : Measure K) {h : K → ℝ} (hh : Measurable h) :
    (μ.map fun x => (h x, x)).fst = μ.map h := by
  have hm : Measurable fun x => (h x, x) := hh.prodMk measurable_id
  rw [Measure.fst, Measure.map_map measurable_fst hm]; rfl

lemma fib_ae (μ : Measure K) [IsProbabilityMeasure μ] {h : K → ℝ} (hh : Measurable h) :
    ∀ᵐ s ∂(μ.map h), ∀ᵐ x ∂(fib μ h s), h x = s := by
  set ν := μ.map fun x => (h x, x)
  have hm : Measurable fun x => (h x, x) := hh.prodMk measurable_id
  have h1 : ∀ᵐ q ∂ν, h q.2 = q.1 := by
    have hS : MeasurableSet {q : ℝ × K | h q.2 = q.1} :=
      measurableSet_eq_fun (hh.comp measurable_snd) measurable_fst
    exact (ae_map_iff hm.aemeasurable hS).2 (ae_of_all _ fun x => rfl)
  rw [← ν.disintegrate ν.condKernel] at h1
  have h2 := Measure.ae_ae_of_ae_compProd h1
  rw [fst_graph μ hh] at h2
  exact h2

lemma lintegral_fib (μ : Measure K) [IsProbabilityMeasure μ] {h : K → ℝ} (hh : Measurable h)
    {A : Set K} (hA : MeasurableSet A) : ∫⁻ s, fib μ h s A ∂(μ.map h) = μ A := by
  set ν := μ.map fun x => (h x, x)
  have hm : Measurable fun x => (h x, x) := hh.prodMk measurable_id
  have h1 : ν (univ ×ˢ A) = μ A := by
    rw [Measure.map_apply hm (MeasurableSet.univ.prod hA)]
    congr 1; ext x; simp
  rw [← ν.disintegrate ν.condKernel, Measure.compProd_apply_prod MeasurableSet.univ hA,
    Measure.restrict_univ, fst_graph μ hh] at h1
  exact h1


/-- The glued plan: draw `(s, t)` from the monotone coupling of the projections, then `X` and `Y`
independently from the fibres over `s` and `t`. -/
abbrev glue (μ₀ μ₁ : Measure K) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] (h : K → ℝ) :
    Measure ((ℝ × ℝ) × (K × K)) :=
  ((μ₀.map h).quantileCoupling (μ₁.map h)) ⊗ₘ (fib μ₀ h ∥ₖ fib μ₁ h)

lemma glue_fst_marg (μ₀ μ₁ : Measure K) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    {h : K → ℝ} (hh : Measurable h) : (glue μ₀ μ₁ h).snd.fst = μ₀ := by
  have hc := Measure.isCoupling_quantileCoupling (μ₀.map h) (μ₁.map h)
  ext A hA
  rw [Measure.fst_apply hA, Measure.snd_apply (measurable_fst hA), Measure.compProd_apply
    (measurable_snd (measurable_fst hA))]
  have hpre : ∀ p : ℝ × ℝ, Prod.mk p ⁻¹' (Prod.snd ⁻¹' (Prod.fst ⁻¹' A)) = A ×ˢ (univ : Set K) := by
    intro p; ext z; simp
  simp_rw [hpre, Kernel.parallelComp_apply_prod, measure_univ, mul_one]
  set π := (μ₀.map h).quantileCoupling (μ₁.map h)
  have e : ∫⁻ p, fib μ₀ h p.1 A ∂π = ∫⁻ s, fib μ₀ h s A ∂(π.map Prod.fst) :=
    (lintegral_map (Kernel.measurable_coe _ hA) measurable_fst).symm
  rw [e, show π.map Prod.fst = μ₀.map h from hc.fst_eq, lintegral_fib μ₀ hh hA]

lemma glue_snd_marg (μ₀ μ₁ : Measure K) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    {h : K → ℝ} (hh : Measurable h) : (glue μ₀ μ₁ h).snd.snd = μ₁ := by
  have hc := Measure.isCoupling_quantileCoupling (μ₀.map h) (μ₁.map h)
  ext A hA
  rw [Measure.snd_apply hA, Measure.snd_apply (measurable_snd hA), Measure.compProd_apply
    (measurable_snd (measurable_snd hA))]
  have hpre : ∀ p : ℝ × ℝ, Prod.mk p ⁻¹' (Prod.snd ⁻¹' (Prod.snd ⁻¹' A)) = (univ : Set K) ×ˢ A := by
    intro p; ext z; simp
  simp_rw [hpre, Kernel.parallelComp_apply_prod, measure_univ, one_mul]
  set π := (μ₀.map h).quantileCoupling (μ₁.map h)
  have e : ∫⁻ p, fib μ₁ h p.2 A ∂π = ∫⁻ s, fib μ₁ h s A ∂(π.map Prod.snd) :=
    (lintegral_map (Kernel.measurable_coe _ hA) measurable_snd).symm
  rw [e, show π.map Prod.snd = μ₁.map h from hc.snd_eq, lintegral_fib μ₁ hh hA]


lemma glue_cost (μ₀ μ₁ : Measure K) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    {h : K → ℝ} (hh : Measurable h) :
    ∫⁻ z, ENNReal.ofReal ((h z.1 - h z.2) ^ 2) ∂(glue μ₀ μ₁ h).snd =
      ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2) ∂((μ₀.map h).quantileCoupling (μ₁.map h)) := by
  have hc := Measure.isCoupling_quantileCoupling (μ₀.map h) (μ₁.map h)
  set π := (μ₀.map h).quantileCoupling (μ₁.map h)
  have hf : Measurable fun z : K × K => ENNReal.ofReal ((h z.1 - h z.2) ^ 2) := by fun_prop
  have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((p.1 - p.2) ^ 2) := by fun_prop
  rw [Measure.snd, lintegral_map hf measurable_snd]
  -- the glued plan lives on the fibres
  have h0 : ∀ᵐ p ∂π, ∀ᵐ x ∂(fib μ₀ h p.1), h x = p.1 := by
    have := fib_ae μ₀ hh
    rw [← hc.fst_eq] at this
    exact ae_of_ae_map measurable_fst.aemeasurable this
  have h1 : ∀ᵐ p ∂π, ∀ᵐ y ∂(fib μ₁ h p.2), h y = p.2 := by
    have := fib_ae μ₁ hh
    rw [← hc.snd_eq] at this
    exact ae_of_ae_map measurable_snd.aemeasurable this
  have hS : MeasurableSet {q : (ℝ × ℝ) × (K × K) | h q.2.1 = q.1.1 ∧ h q.2.2 = q.1.2} :=
    (measurableSet_eq_fun (by fun_prop) (by fun_prop)).inter
      (measurableSet_eq_fun (by fun_prop) (by fun_prop))
  have hae : ∀ᵐ q ∂(glue μ₀ μ₁ h), h q.2.1 = q.1.1 ∧ h q.2.2 = q.1.2 := by
    refine (Measure.ae_compProd_iff hS).2 ?_
    filter_upwards [h0, h1] with p hp0 hp1
    rw [Kernel.parallelComp_apply]
    exact (Measure.quasiMeasurePreserving_fst.ae hp0).and (Measure.quasiMeasurePreserving_snd.ae hp1)
  rw [lintegral_congr_ae (g := fun q : (ℝ × ℝ) × (K × K) => ENNReal.ofReal ((q.1.1 - q.1.2) ^ 2))
    (hae.mono fun q hq => by simp only [hq.1, hq.2])]
  rw [← lintegral_map hg measurable_fst, ← Measure.fst, Measure.fst_compProd]

end Fibre

end RouteDeltaInf

open RouteDeltaInf

theorem delta_inf_general : Claims.delta_inf_general := by
  intro K _ _ μ₀ μ₁ _ _ h hh
  have : Nonempty K := nonempty_of_isProbabilityMeasure μ₀
  refine ⟨fun γ hγ => W2_sq_le_lift hh hγ, (glue μ₀ μ₁ h).snd,
    ⟨glue_fst_marg μ₀ μ₁ hh, glue_snd_marg μ₀ μ₁ hh⟩, ?_⟩
  rw [glue_cost μ₀ μ₁ hh, W2_sq_quantileCoupling]

end StatFormal.WaveP1d
