import StatFormal.Archive.Wave8a.Statements
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import TauCeti.MeasureTheory.OptimalTransport.Entropic.SchroedingerSystem

/-!
# Route: SB `lem:sharp` (no barycentric projection is parity-exact)

1. Real Pythagoras (law of total variance, Mathlib `integral_condVar_add_variance_condExp`):
   `E(X − E[X|m])² = E X² − E(E[X|m])²` for `X ∈ L²`.
2. Coordinatewise (`PiLp.proj` commutes with `condExp`) and summed:
   `E‖X₁ − T(X₀)‖² = ∫‖y‖² dν − ∫‖T‖² dR`. So `T_#R = ν` forces `E‖X₁ − T(X₀)‖² = 0`, i.e. `X₁ = T(X₀)` a.s., i.e.
   `π = (id,T)_#R`; conversely a graph plan makes `X₁` `σ(X₀)`-measurable.
3. Positive density: a graph plan is carried by the graph `G`; `π ~ R ⊗ ν` forces `(R ⊗ ν)(G) = 1`, i.e.
   `∫ ν{T x} dR = 1`, so `ν{T x} = 1` for some `x`: `ν` is a Dirac.
4. Entropic plan, compact supports: on `supp R × supp ν` the quadratic cost equals the bounded cost
   `min(c, (2M)²)`; Tau Ceti's Schrödinger system for bounded costs gives existence and the product form
   `e^{φ ⊕ ψ}` of the density against the Gibbs measure, hence a positive density against `R ⊗ ν`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave8a

/-- `σ(X₀)` on `ℝ^d × ℝ^d` (a plain definition, not a local instance). -/
abbrev fstSigma (d : ℕ) : MeasurableSpace (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  MeasurableSpace.comap Prod.fst inferInstance

theorem fstSigma_le (d : ℕ) :
    fstSigma d ≤ (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) :=
  measurable_fst.comap_le

/-! ### Real Pythagoras -/

theorem integral_sq_sub_condExp {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    (hm : m ≤ m₀) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    ∫ ω, (X ω - μ[X | m] ω) ^ 2 ∂μ = ∫ ω, X ω ^ 2 ∂μ - ∫ ω, (μ[X | m] ω) ^ 2 ∂μ := by
  have h := integral_condVar_add_variance_condExp hm hX
  rw [variance_eq_sub (hX.condExp one_le_two), variance_eq_sub hX] at h
  have e1 : ∫ ω, (μ[X | m]) ω ∂μ = ∫ ω, X ω ∂μ := integral_condExp hm
  have e2 : ∫ ω, condVar m X μ ω ∂μ = ∫ ω, ((X - μ[X | m]) ^ 2) ω ∂μ := integral_condExp hm
  simp only [Pi.pow_apply, Pi.sub_apply] at h e2
  rw [e1, e2] at h
  linarith

/-- `∫ condVar = E(X − E[X|m])²`. -/
theorem integral_condVar_eq {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    (hm : m ≤ m₀) [IsProbabilityMeasure μ] (X : Ω → ℝ) :
    ∫ ω, condVar m X μ ω ∂μ = ∫ ω, (X ω - μ[X | m] ω) ^ 2 ∂μ := by
  have e2 : ∫ ω, condVar m X μ ω ∂μ = ∫ ω, ((X - μ[X | m]) ^ 2) ω ∂μ := integral_condExp hm
  simpa only [Pi.pow_apply, Pi.sub_apply] using e2

/-! ### The core identity -/

section Core

variable {d : ℕ}

/-- The core facts for a coupling `π` of `R` and `ν ∈ 𝒫₂` and a version `T` of its barycentric projection. -/
theorem sharp_core {R ν : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure R]
    [IsProbabilityMeasure ν] {π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))}
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hπ : IsCoupling π R ν) (hν : HasFiniteMoment 2 ν) (hT : IsBaryProj π T) :
    Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => ‖p.2 - T p.1‖ ^ 2) π ∧
      ∫ p, ‖p.2 - T p.1‖ ^ 2 ∂π = ∫ y, ‖y‖ ^ 2 ∂ν - ∫ x, ‖T x‖ ^ 2 ∂R ∧
      ∫ p, ‖p.2 - T p.1‖ ^ 2 ∂π = ∑ i, ∫ p, (p.2 i - T p.1 i) ^ 2 ∂π ∧
      ∀ i : Fin d, ∫ p, condVar (MeasurableSpace.comap Prod.fst inferInstance)
          (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.2 i) π p ∂π =
        ∫ p, (p.2 i - T p.1 i) ^ 2 ∂π := by
  have hm := fstSigma_le d
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hsnd : π.map Prod.snd = ν := by
    have h := hπ.snd_eq
    rwa [Measure.snd] at h
  have hfst : π.map Prod.fst = R := by
    have h := hπ.fst_eq
    rwa [Measure.fst] at h
  have hY : MemLp (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.2) 2 π :=
    memLp_of_hasFiniteMoment_map measurable_snd (hsnd ▸ hν)
  have hZ : MemLp (π[fun p => p.2 | fstSigma d]) 2 π := hY.condExp one_le_two
  have hTm : MemLp (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => T p.1) 2 π :=
    hZ.ae_eq hT.2.symm
  -- coordinates
  let pr : Fin d → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun i =>
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i
  have hpr : ∀ i (v : EuclideanSpace ℝ (Fin d)), pr i v = v i := fun i v => rfl
  have hYi : ∀ i, MemLp (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.2 i) 2 π :=
    fun i => (pr i).comp_memLp' hY
  have hTi : ∀ i, MemLp (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => T p.1 i) 2 π :=
    fun i => (pr i).comp_memLp' hTm
  have hcoord : ∀ i, (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => T p.1 i) =ᵐ[π]
      π[fun p => p.2 i | fstSigma d] := by
    intro i
    have h := (pr i).comp_condExp_comm (μ := π) (m := fstSigma d) (hY.integrable one_le_two)
    filter_upwards [hT.2, h] with p h1 h2
    simp only [Function.comp_apply, hpr] at h2
    rw [h1]
    exact h2
  have hkey : ∀ i, ∫ p, (p.2 i - T p.1 i) ^ 2 ∂π = ∫ p, (p.2 i) ^ 2 ∂π - ∫ p, (T p.1 i) ^ 2 ∂π := by
    intro i
    have h := integral_sq_sub_condExp hm (hYi i)
    have e1 : ∫ p, (p.2 i - T p.1 i) ^ 2 ∂π = ∫ p, (p.2 i - π[fun p => p.2 i | fstSigma d] p) ^ 2 ∂π :=
      integral_congr_ae (by filter_upwards [hcoord i] with p hp; rw [hp])
    have e2 : ∫ p, (T p.1 i) ^ 2 ∂π = ∫ p, (π[fun p => p.2 i | fstSigma d] p) ^ 2 ∂π :=
      integral_congr_ae (by filter_upwards [hcoord i] with p hp; rw [hp])
    rw [e1, e2]
    exact h
  have hnorm : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ^ 2 = ∑ i, (v i) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq
  have hsum : ∫ p, ‖p.2 - T p.1‖ ^ 2 ∂π = ∑ i, ∫ p, (p.2 i - T p.1 i) ^ 2 ∂π := by
    simp_rw [hnorm]
    rw [integral_finsetSum _ fun i _ => by simpa using ((hYi i).sub (hTi i)).integrable_sq]
    rfl
  have hsumY : ∫ p, ‖p.2‖ ^ 2 ∂π = ∑ i, ∫ p, (p.2 i) ^ 2 ∂π := by
    simp_rw [hnorm]
    rw [integral_finsetSum _ fun i _ => (hYi i).integrable_sq]
  have hsumT : ∫ p, ‖T p.1‖ ^ 2 ∂π = ∑ i, ∫ p, (T p.1 i) ^ 2 ∂π := by
    simp_rw [hnorm]
    rw [integral_finsetSum _ fun i _ => (hTi i).integrable_sq]
  have hν2 : ∫ p, ‖p.2‖ ^ 2 ∂π = ∫ y, ‖y‖ ^ 2 ∂ν := by
    rw [← hsnd, integral_map measurable_snd.aemeasurable (by fun_prop)]
  have hR2 : ∫ p, ‖T p.1‖ ^ 2 ∂π = ∫ x, ‖T x‖ ^ 2 ∂R := by
    rw [← hfst, integral_map measurable_fst.aemeasurable
      ((hT.1.norm.pow_const 2).aestronglyMeasurable)]
  refine ⟨(memLp_two_iff_integrable_sq_norm (hY.sub hTm).aestronglyMeasurable).1 (hY.sub hTm), ?_, hsum, ?_⟩
  · rw [hsum, ← hν2, ← hR2, hsumY, hsumT, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => hkey i
  · intro i
    rw [integral_condVar_eq hm]
    exact integral_congr_ae (by filter_upwards [hcoord i] with p hp; rw [hp])

/-- `condVarTrace` is the real integral, when integrable. -/
theorem condVarTrace_eq_ofReal {π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))}
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hi : Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => ‖p.2 - T p.1‖ ^ 2) π) :
    condVarTrace π T = ENNReal.ofReal (∫ p, ‖p.2 - T p.1‖ ^ 2 ∂π) := by
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => by positivity), condVarTrace]
  refine lintegral_congr fun p => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- A graph plan from `condVarTrace = 0`. -/
theorem graph_of_condVarTrace {R ν : Measure (EuclideanSpace ℝ (Fin d))}
    {π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))}
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hπ : IsCoupling π R ν) (hTm : Measurable T) (h0 : condVarTrace π T = 0) :
    π = R.map (fun x => (x, T x)) ∧ R.map T = ν := by
  have hfst : π.map Prod.fst = R := by
    have h := hπ.fst_eq
    rwa [Measure.fst] at h
  have hsnd : π.map Prod.snd = ν := by
    have h := hπ.snd_eq
    rwa [Measure.snd] at h
  have hmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ‖p.2 - T p.1‖ₑ ^ 2 := by fun_prop
  have hae : ∀ᵐ p ∂π, p.2 = T p.1 := by
    have := (lintegral_eq_zero_iff hmeas).1 h0
    filter_upwards [this] with p hp
    simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero, enorm_eq_zero, sub_eq_zero] at hp
    exact hp
  have hgraph : Measurable fun x : EuclideanSpace ℝ (Fin d) => (x, T x) :=
    measurable_id.prodMk hTm
  have hπg : π = R.map (fun x => (x, T x)) := by
    calc π = π.map id := Measure.map_id.symm
      _ = π.map (fun p => (p.1, T p.1)) := by
          refine Measure.map_congr ?_
          filter_upwards [hae] with p hp
          simp only [id]
          rw [← hp]
      _ = (π.map Prod.fst).map (fun x => (x, T x)) := by
          rw [Measure.map_map hgraph measurable_fst]
          rfl
      _ = R.map (fun x => (x, T x)) := by rw [hfst]
  refine ⟨hπg, ?_⟩
  rw [← hsnd, hπg, Measure.map_map measurable_snd hgraph]
  rfl

end Core

/-! ### The claims -/

theorem sharp_bary_exists : Claims.sharp_bary_exists := by
  intro d R ν _ _ π hπ hν
  have hsm : StronglyMeasurable[fstSigma d] (π[fun p => p.2 | fstSigma d]) :=
    stronglyMeasurable_condExp
  obtain ⟨h, hh, heq⟩ := hsm.exists_eq_measurable_comp
  exact ⟨h, hh.measurable, by rw [heq]; rfl⟩

theorem sharp_iff : Claims.sharp_iff := by
  intro d R ν _ _ π T hπ hν hT
  obtain ⟨hi, hpyth, -, -⟩ := sharp_core hπ hν hT
  have hfst : π.map Prod.fst = R := by
    have h := hπ.fst_eq
    rwa [Measure.fst] at h
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have h1 : R.map T = ν ↔ condVarTrace π T = 0 := by
    constructor
    · intro hmap
      rw [condVarTrace_eq_ofReal hi, hpyth, ← hmap,
        integral_map hT.1.aemeasurable (by fun_prop), sub_self, ENNReal.ofReal_zero]
    · intro h0
      exact (graph_of_condVarTrace hπ hT.1 h0).2
  refine ⟨h1, ?_, ?_⟩
  · intro h0
    exact ⟨T, hT.1, (graph_of_condVarTrace hπ hT.1 h0).1⟩
  · rintro ⟨S, hS, hπS⟩
    -- under a graph plan, `X₁ = S(X₀)` a.s., which is `σ(X₀)`-measurable
    have hm := fstSigma_le d
    have hgraph : Measurable fun x : EuclideanSpace ℝ (Fin d) => (x, S x) := measurable_id.prodMk hS
    have hae : ∀ᵐ p ∂π, p.2 = S p.1 := by
      rw [hπS]
      exact (ae_map_iff hgraph.aemeasurable
        (measurableSet_eq_fun measurable_snd (hS.comp measurable_fst))).2 (ae_of_all _ fun x => rfl)
    have hsnd : π.map Prod.snd = ν := by
      have h := hπ.snd_eq
      rwa [Measure.snd] at h
    have hYi : Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.2) π :=
      (memLp_of_hasFiniteMoment_map measurable_snd (hsnd ▸ hν)).integrable one_le_two
    have hSm : StronglyMeasurable[fstSigma d] (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        S p.1) :=
      (hS.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
    have hSi : Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => S p.1) π :=
      hYi.congr (by filter_upwards [hae] with p hp; exact hp)
    have hce : π[fun p => p.2 | fstSigma d] =ᵐ[π] fun p => S p.1 := by
      have h1 : π[fun p => p.2 | fstSigma d] =ᵐ[π] π[fun p => S p.1 | fstSigma d] :=
        condExp_congr_ae (by filter_upwards [hae] with p hp; exact hp)
      rwa [condExp_of_stronglyMeasurable hm hSm hSi] at h1
    rw [condVarTrace]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hT.2, hce, hae] with p h1 h2 h3
    rw [h1, h2, h3, sub_self, enorm_zero]
    simp

theorem sharp_condVar : Claims.sharp_condVar := by
  intro d R ν _ _ π T hπ hν hT
  obtain ⟨hi, -, hsum, hcv⟩ := sharp_core hπ hν hT
  have hiff := (sharp_iff d R ν π T hπ hν hT).1
  rw [hiff, condVarTrace_eq_ofReal hi, ENNReal.ofReal_eq_zero]
  have hnn : ∀ i, 0 ≤ ∫ p, (p.2 i - T p.1 i) ^ 2 ∂π := fun i =>
    integral_nonneg fun p => sq_nonneg _
  have hge : 0 ≤ ∫ p, ‖p.2 - T p.1‖ ^ 2 ∂π := integral_nonneg fun p => sq_nonneg _
  simp_rw [hcv]
  rw [hsum]
  constructor
  · intro h i
    have h0 : ∑ i, ∫ p, (p.2 i - T p.1 i) ^ 2 ∂π = 0 := le_antisymm h (Finset.sum_nonneg fun i _ => hnn i)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h0 i (Finset.mem_univ _)
  · intro h
    rw [Finset.sum_eq_zero fun i _ => h i]

/-! ### Positive density -/

/-- A probability measure with an atom of mass one is a Dirac measure. -/
theorem eq_dirac_of_singleton {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {ν : Measure X} [IsProbabilityMeasure ν] {y : X} (hy : ν {y} = 1) : ν = Measure.dirac y := by
  ext s hs
  rw [Measure.dirac_apply' _ hs]
  by_cases h : y ∈ s
  · rw [indicator_of_mem h, Pi.one_apply]
    refine le_antisymm prob_le_one ?_
    rw [← hy]
    exact measure_mono (singleton_subset_iff.2 h)
  · rw [indicator_of_notMem h]
    have hc : ν {y}ᶜ = 0 := (prob_compl_eq_zero_iff (measurableSet_singleton y)).2 hy
    refine measure_mono_null (fun z hz => ?_) hc
    rintro rfl
    exact h hz

/-- A graph plan with a positive density against `R ⊗ ν` forces `ν` to be a Dirac measure. -/
theorem dirac_of_graph_density {d : ℕ} {R ν : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure R] [IsProbabilityMeasure ν]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hTm : Measurable T)
    {f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hf : Measurable f)
    (hpos : ∀ᵐ z ∂(R.prod ν), 0 < f z)
    (hπ : R.map (fun x => (x, T x)) = (R.prod ν).withDensity f) :
    ∃ y, ν = Measure.dirac y := by
  set G : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) := {p | p.2 = T p.1} with hGdef
  have hG : MeasurableSet G := measurableSet_eq_fun measurable_snd (hTm.comp measurable_fst)
  have hgraph : Measurable fun x : EuclideanSpace ℝ (Fin d) => (x, T x) := measurable_id.prodMk hTm
  have h1 : (R.map (fun x => (x, T x))) Gᶜ = 0 := by
    rw [Measure.map_apply hgraph hG.compl]
    have : (fun x => (x, T x)) ⁻¹' Gᶜ = ∅ := by
      ext x; simp [hGdef]
    rw [this, measure_empty]
  rw [hπ, withDensity_apply _ hG.compl] at h1
  have h2 := (lintegral_eq_zero_iff hf).1 h1
  rw [Filter.EventuallyEq, ae_restrict_iff' hG.compl] at h2
  have hGc : (R.prod ν) Gᶜ = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h2, hpos] with z hz hp hmem
    have := hz hmem
    simp only [Pi.zero_apply] at this
    exact (ne_of_gt hp) this
  have hG1 : (R.prod ν) G = 1 := (prob_compl_eq_zero_iff hG).1 hGc
  rw [Measure.prod_apply hG] at hG1
  have hslice : ∀ x, Prod.mk x ⁻¹' G = {T x} := fun x => by
    ext y; simp [hGdef]
  simp_rw [hslice] at hG1
  have hae : (fun x => ν {T x}) =ᵐ[R] fun _ => 1 := by
    refine ae_eq_of_ae_le_of_lintegral_le (ae_of_all _ fun x => prob_le_one) (by rw [hG1]; simp)
      aemeasurable_const ?_
    rw [hG1, lintegral_const, measure_univ, one_mul]
  obtain ⟨x, hx⟩ := hae.exists
  exact ⟨T x, eq_dirac_of_singleton hx⟩

theorem sharp_density : Claims.sharp_density := by
  intro d R ν _ _ π T f hπ hν hT hf hpos hdens
  have hiff := (sharp_iff d R ν π T hπ hν hT).1
  constructor
  · intro hmap
    have hg := (graph_of_condVarTrace hπ hT.1 (hiff.1 hmap)).1
    exact dirac_of_graph_density hT.1 hf hpos (hg.symm.trans hdens)
  · rintro ⟨y, rfl⟩
    refine hiff.2 ?_
    have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
    have hm := fstSigma_le d
    have hsnd : π.map Prod.snd = Measure.dirac y := by
      have h := hπ.snd_eq
      rwa [Measure.snd] at h
    have hae : ∀ᵐ p ∂π, p.2 = y := by
      refine ae_of_ae_map (p := fun z => z = y) measurable_snd.aemeasurable ?_
      rw [hsnd]
      exact (ae_dirac_iff (measurableSet_eq_fun measurable_id measurable_const)).2 rfl
    have hce : π[fun p => p.2 | fstSigma d] =ᵐ[π] fun _ => y := by
      have h1 : π[fun p => p.2 | fstSigma d] =ᵐ[π] π[fun _ => y | fstSigma d] :=
        condExp_congr_ae (by filter_upwards [hae] with p hp; exact hp)
      rwa [condExp_const hm] at h1
    rw [condVarTrace]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hT.2, hce, hae] with p h1 h2 h3
    rw [h1, h2, h3, sub_self, enorm_zero]
    simp

/-! ### The entropic plan, compactly supported marginals -/

section Entropic

variable {d : ℕ}

theorem hasFiniteMoment_of_ball {ν : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure ν]
    {M : ℝ} (hν : ν (Metric.closedBall 0 M)ᶜ = 0) : HasFiniteMoment 2 ν := by
  refine hasFiniteMoment_def.2 ⟨0, MemLp.of_enorm_bound (C := ENNReal.ofReal M)
    measurable_edist_right.aestronglyMeasurable ENNReal.ofReal_ne_top ?_⟩
  have h := measure_eq_zero_iff_ae_notMem.1 hν
  filter_upwards [h] with y hy
  simp only [mem_compl_iff, not_not, Metric.mem_closedBall] at hy
  rw [enorm_eq_self, edist_dist, dist_comm]
  exact ENNReal.ofReal_le_ofReal hy

/-- Couplings of laws carried by `closedBall 0 M` are carried by its square. -/
theorem ae_mem_ball_prod {R ν : Measure (EuclideanSpace ℝ (Fin d))} {M : ℝ}
    {π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))} (hπ : IsCoupling π R ν)
    (hR : R (Metric.closedBall 0 M)ᶜ = 0) (hν : ν (Metric.closedBall 0 M)ᶜ = 0) :
    ∀ᵐ z ∂π, z.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) M ∧
      z.2 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) M := by
  have hK : MeasurableSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) M) :=
    Metric.isClosed_closedBall.measurableSet
  have h1 : π (Prod.fst ⁻¹' (Metric.closedBall 0 M)ᶜ) = 0 := by
    rw [← Measure.fst_apply hK.compl, hπ.fst_eq, hR]
  have h2 : π (Prod.snd ⁻¹' (Metric.closedBall 0 M)ᶜ) = 0 := by
    rw [← Measure.snd_apply hK.compl, hπ.snd_eq, hν]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1, measure_eq_zero_iff_ae_notMem.1 h2]
    with z hz1 hz2
  simp only [mem_preimage, mem_compl_iff, not_not] at hz1 hz2
  exact ⟨hz1, hz2⟩

/-- The truncated (bounded) quadratic cost. -/
def truncCost (M : ℝ) (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  min (quadCost z) (ENNReal.ofReal ((2 * M) ^ 2))

theorem measurable_quadCost : Measurable (quadCost (d := d)) := by
  unfold quadCost; fun_prop

theorem measurable_truncCost (M : ℝ) : Measurable (truncCost (d := d) M) :=
  measurable_quadCost.min measurable_const

theorem quadCost_ae_eq_truncCost {R ν : Measure (EuclideanSpace ℝ (Fin d))} {M : ℝ}
    {π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))} (hπ : IsCoupling π R ν)
    (hR : R (Metric.closedBall 0 M)ᶜ = 0) (hν : ν (Metric.closedBall 0 M)ᶜ = 0) :
    quadCost =ᵐ[π] truncCost M := by
  filter_upwards [ae_mem_ball_prod hπ hR hν] with z hz
  simp only [Metric.mem_closedBall, dist_zero_right] at hz
  unfold truncCost
  rw [min_eq_left]
  have hn : ‖z.1 - z.2‖ ≤ 2 * M := by
    calc ‖z.1 - z.2‖ ≤ ‖z.1‖ + ‖z.2‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add hz.1 hz.2
      _ = 2 * M := by ring
  unfold quadCost
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hn 2)

theorem truncCost_le (M : ℝ) (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    truncCost M z ≤ ((Real.toNNReal ((2 * M) ^ 2) : ℝ≥0) : ℝ≥0∞) :=
  min_le_right _ _

/-- On couplings of laws carried by the ball, the two entropic objectives coincide. -/
theorem objective_eq {R ν : Measure (EuclideanSpace ℝ (Fin d))} {M : ℝ} (ε : ℝ≥0)
    {π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))} (hπ : IsCoupling π R ν)
    (hR : R (Metric.closedBall 0 M)ᶜ = 0) (hν : ν (Metric.closedBall 0 M)ᶜ = 0) :
    ∫⁻ z, quadCost z ∂π + ε * klDiv π (R.prod ν) =
      ∫⁻ z, truncCost M z ∂π + ε * klDiv π (R.prod ν) := by
  rw [lintegral_congr_ae (quadCost_ae_eq_truncCost hπ hR hν)]

theorem entropicCost_eq {R ν : Measure (EuclideanSpace ℝ (Fin d))} {M : ℝ} (ε : ℝ≥0)
    (hR : R (Metric.closedBall 0 M)ᶜ = 0) (hν : ν (Metric.closedBall 0 M)ᶜ = 0) :
    entropicTransportCost quadCost ε R ν = entropicTransportCost (truncCost M) ε R ν := by
  rw [entropicTransportCost_def, entropicTransportCost_def]
  exact iInf_congr fun π => iInf_congr fun hπ => objective_eq ε hπ hR hν

/-- Every entropic optimal plan has a positive density against `R ⊗ ν`. -/
theorem entropicPlan_density {R ν : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure R]
    [IsProbabilityMeasure ν] {M : ℝ} {ε : ℝ≥0} (hε : ε ≠ 0)
    (hR : R (Metric.closedBall 0 M)ᶜ = 0) (hν : ν (Metric.closedBall 0 M)ᶜ = 0)
    {π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))} (hπ : IsEntropicPlan ε R ν π) :
    ∃ f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable f ∧
      (∀ z, 0 < f z) ∧ π = (R.prod ν).withDensity f := by
  obtain ⟨hc, hopt⟩ := hπ
  have hopt' : ∫⁻ z, truncCost M z ∂π + ε * klDiv π (R.prod ν) =
      entropicTransportCost (truncCost M) ε R ν := by
    rw [← objective_eq ε hc hR hν, hopt, entropicCost_eq ε hR hν]
  have hcm := measurable_truncCost (d := d) M
  have hctop : ∀ᵐ z ∂(R.prod ν), truncCost M z ≠ ∞ :=
    ae_of_all _ fun z => ((truncCost_le M z).trans_lt ENNReal.coe_lt_top).ne
  have hS := (lintegral_add_mul_klDiv_eq_entropicTransportCost_iff hc hcm.aemeasurable hctop hε).1
    hopt'
  set u : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ :=
    fun z => -((truncCost M z).toReal / ε) with hudef
  have hum : Measurable u := (hcm.ennreal_toReal.div_const _).neg
  have hB : ∀ z, |u z| ≤ (2 * M) ^ 2 / ε := by
    intro z
    have hε' : (0 : ℝ) < ε := by positivity
    rw [hudef, abs_neg, abs_div, abs_of_nonneg ENNReal.toReal_nonneg, NNReal.abs_eq]
    refine div_le_div_of_nonneg_right ?_ hε'.le
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_right (quadCost z)
      (ENNReal.ofReal ((2 * M) ^ 2)))
    rwa [ENNReal.toReal_ofReal (sq_nonneg _)] at this
  have hint : Integrable (fun z => Real.exp (u z)) (R.prod ν) := by
    refine Integrable.of_bound (hum.exp).aestronglyMeasurable 1 (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, hudef, neg_nonpos]
    exact div_nonneg ENNReal.toReal_nonneg (by positivity)
  set Z := ∫ z, Real.exp (u z) ∂(R.prod ν) with hZdef
  have hZ : 0 < Z := integral_exp_pos hint
  set g : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ := fun z => u z - Real.log Z
    with hgdef
  have hgm : Measurable g := hum.sub measurable_const
  have hgB : ∀ z, |g z| ≤ (2 * M) ^ 2 / ε + |Real.log Z| := fun z =>
    (abs_sub _ _).trans (add_le_add (hB z) le_rfl)
  have hR' : (R.prod ν).tilted u = (R.prod ν).withDensity fun z => ENNReal.ofReal (Real.exp (g z)) := by
    rw [Measure.tilted]
    congr 1
    funext z
    rw [hgdef, Real.exp_sub, Real.exp_log hZ]
  rw [hR'] at hS
  obtain ⟨φ, ψ, C, hφ, hψ, -, -, hπeq⟩ :=
    hc.exists_eq_withDensity_exp_add_of_klDiv_eq_schroedingerValue hgm hgB rfl hS
  refine ⟨fun z => ENNReal.ofReal (Real.exp (g z)) * ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2)),
    by fun_prop, fun z => ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne', ?_⟩
  rw [hπeq, ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  rfl

theorem sharp_entropic : Claims.sharp_entropic := by
  intro d R ν _ _ M ε hR hν hε
  have hν2 := hasFiniteMoment_of_ball hν
  refine ⟨?_, fun π T hπ hT => ?_⟩
  · obtain ⟨π, hc, hopt, -⟩ := exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost
      (μ := R) (ν := ν) (measurable_truncCost (d := d) M) (truncCost_le M) hε
    refine ⟨π, hc, ?_⟩
    rw [objective_eq ε hc hR hν, hopt, entropicCost_eq ε hR hν]
  · obtain ⟨f, hf, hpos, hπf⟩ := entropicPlan_density hε hR hν hπ
    exact sharp_density d R ν π T f hπ.1 hν2 hT hf (ae_of_all _ hpos) hπf

end Entropic

end StatFormal.Wave8a
