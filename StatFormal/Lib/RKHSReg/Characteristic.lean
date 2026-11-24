import StatFormal.Lib.TIKernel.MMD

/-!
# A positive spectral density makes a kernel characteristic and strictly positive definite (library, untrusted)

Let `k₀ : V → ℝ` be continuous and integrable with `specDens k₀ > 0` almost everywhere, and `φ : V → H` any feature map with
`⟪φ x, φ y⟫ = k₀ (x − y)`. Then:

* **the mean embedding is injective on finite measures** (`mean_embedding_injective`; Sriperumbudur, Gretton, Fukumizu,
  Schölkopf, Lanckriet 2010, Thm 9): by `TIKernel.mmd_fourier_facts`,
  `‖∫ φ dμ − ∫ φ dν‖² = ∫ specDens k₀ · |ftMeas μ − ftMeas ν|²`; if this vanishes, the continuous difference of the transforms
  vanishes a.e. (the density is positive a.e.), hence everywhere (Lebesgue measure charges open sets), and `ftMeas_inj` gives
  `μ = ν`. In particular `φ` is characteristic on probability measures (`characteristic_of_spec`);
* **`φ` is strictly positive definite on `V`** (`strictlyPD_of_spec`; Wendland Thm 6.11):
  `Σ c_z c_w ⟪φ z, φ w⟫ = ‖Σ c_z φ z‖²`, and if `Σ c_z φ z = 0` the finite atomic measures `Σ c_z⁺ δ_z` and `Σ c_z⁻ δ_z`
  (`atomMeas`) have equal mean embeddings, hence are equal; their masses `c_z⁺ = c_z⁻` at each point of the finite set
  agree, so `c = 0` there.
-/

noncomputable section
open MeasureTheory Filter Topology Set Complex
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace StatFormal.RKHSReg

open StatFormal.Wave31tp StatFormal.TIKernel

section Atom

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The finite atomic measure `Σ_{z ∈ Z} a(z)⁺ δ_z`. -/
def atomMeas (Z : Finset X) (a : X → ℝ) : Measure X := ∑ z ∈ Z, (a z).toNNReal • Measure.dirac z

instance (Z : Finset X) (a : X → ℝ) : IsFiniteMeasure (atomMeas Z a) := by
  unfold atomMeas; infer_instance

/-- Integrals against an atomic measure are finite sums: `∫ f d(Σ a(z)⁺ δ_z) = Σ a(z)⁺ f(z)`. -/
lemma integral_atomMeas {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (Z : Finset X)
    (a : X → ℝ) (f : X → E) : ∫ x, f x ∂(atomMeas Z a) = ∑ z ∈ Z, max (a z) 0 • f z := by
  rw [atomMeas, integral_finsetSum_measure fun z _ => (integrable_dirac enorm_lt_top).smul_measure_nnreal]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, Real.coe_toNNReal']

/-- The mass of `Σ_{z ∈ Z} a(z)⁺ δ_z` at a point `z₀ ∈ Z` is `a(z₀)⁺`. -/
lemma atomMeas_singleton (Z : Finset X) (a : X → ℝ) {z₀ : X} (hz₀ : z₀ ∈ Z) :
    atomMeas Z a {z₀} = ((a z₀).toNNReal : ℝ≥0∞) := by
  rw [atomMeas, Measure.finsetSum_apply, Finset.sum_eq_single z₀]
  · simp
  · intro z _ hz
    simp [hz]
  · intro h
    exact absurd hz₀ h

end Atom

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

section Char

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {φ : V → H} {k₀ : V → ℝ} (hφ : ∀ x y, ⟪φ x, φ y⟫ = k₀ (x - y)) (hc : Continuous k₀) (hi : Integrable k₀)
  (hpos : ∀ᵐ ξ ∂volume, 0 < specDens k₀ ξ)
include hφ hc hi hpos

/-- Equal mean embeddings give equal Fourier transforms when the spectral density is positive a.e. -/
theorem ftMeas_eq_of_integral_eq {μ ν : Measure V} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∫ x, φ x ∂μ = ∫ x, φ x ∂ν) : ftMeas μ = ftMeas ν := by
  obtain ⟨-, -, hs0, -, -, -⟩ := feature_exists_facts hc hi (gram_posdef hφ)
  obtain ⟨hint, heq, -⟩ := (mmd_fourier_facts hφ hc hi).2.2.2 μ ν
  rw [h, sub_self, norm_zero, zero_pow two_ne_zero] at heq
  have hae := (integral_eq_zero_iff_of_nonneg (fun ξ => mul_nonneg (hs0 ξ) (sq_nonneg _)) hint).1 heq.symm
  have hae' : ftMeas μ =ᵐ[volume] ftMeas ν := by
    filter_upwards [hae, hpos] with ξ h1 h2
    simp only [Pi.zero_apply] at h1
    rcases mul_eq_zero.1 h1 with h3 | h3
    · exact absurd h3 h2.ne'
    · exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h3))
  exact (Continuous.ae_eq_iff_eq volume (ftMeas_continuous μ) (ftMeas_continuous ν)).1 hae'

/-- **A spectral density positive a.e. makes the mean embedding injective on finite measures.** -/
theorem mean_embedding_injective {μ ν : Measure V} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∫ x, φ x ∂μ = ∫ x, φ x ∂ν) : μ = ν :=
  ftMeas_inj (ftMeas_eq_of_integral_eq hφ hc hi hpos h)

/-- **A spectral density positive a.e. makes the feature map characteristic** ((A3) of trimmed-mmd). -/
theorem characteristic_of_spec : TrimmedMMD.ZeroSet.Characteristic φ :=
  fun _ _ _ _ h => mean_embedding_injective hφ hc hi hpos h

/-- **A spectral density positive a.e. makes the kernel strictly positive definite on `V`**: the Gram matrix of every finite
set of distinct points is positive definite. -/
theorem strictlyPD_of_spec : Wave31tg.StrictlyPDOn φ univ := by
  rintro Z - c ⟨z₀, hz₀, hc₀⟩
  have hq : ∑ z ∈ Z, ∑ w ∈ Z, c z * c w * ⟪φ z, φ w⟫ = ‖∑ z ∈ Z, c z • φ z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hq]
  refine lt_of_le_of_ne (sq_nonneg _) fun hv => hc₀ ?_
  have hv0 : ∑ z ∈ Z, c z • φ z = 0 := by
    have := hv.symm
    rwa [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at this
  have hint : ∫ x, φ x ∂(atomMeas Z c) = ∫ x, φ x ∂(atomMeas Z (-c)) := by
    rw [integral_atomMeas, integral_atomMeas, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← hv0]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← sub_smul, Pi.neg_apply, max_zero_sub_eq_self]
  have hμν := mean_embedding_injective hφ hc hi hpos hint
  have h1 := congrArg (fun μ : Measure V => μ {z₀}) hμν
  simp only [atomMeas_singleton _ _ hz₀, ENNReal.coe_inj, Pi.neg_apply] at h1
  have h2 := max_zero_sub_eq_self (c z₀)
  rw [← Real.coe_toNNReal', ← Real.coe_toNNReal', h1, sub_self] at h2
  exact h2.symm

end Char

end StatFormal.RKHSReg
