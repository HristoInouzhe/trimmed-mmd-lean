import StatFormal.Archive.Wave4b.Statements
import StatFormal.Archive.RobustEquality.Certificate.Proofs

/-!
# Route — robust equality paper 2 `thm:certificate` (independent and structured) and JASA
`thm:cs-certificate`

Every admissible pair has witnesses `ν_s ∈ 𝒩_s`; the certified groupwise certificate
(`RobustEquality.Certificate.certificate`) bounds its disparity by the slice certificate at those
references, which is below the class supremum. Squaring is monotone in `ℝ≥0∞`. The structured
clause is the same bound on the slice `θ` that contains the pair, then `le_iSup`. For transported
classes, `∫ f d(𝔗#ν) = ∫ f ∘ 𝔗 dν` (`integral_map`) gives the pulled-back formula.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set
open scoped ENNReal

namespace StatFormal.Wave4b

open StatFormal.RobustEquality.Certificate

variable {K : Type} [MeasurableSpace K]

/-- The groupwise bound for one admissible pair, against the class supremum. -/
lemma pair_bound {n₀ n₁ : ℕ} (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (c : K → K → ℝ)
    {ε r₀ r₁ lam₀ lam₁ : ℝ} {h : K → ℝ} {N₀ N₁ : Set (Measure K)} {Q₀ Q₁ : Measure K}
    (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hε : 0 < ε) (hl₀ : 0 < lam₀) (hl₁ : 0 < lam₁)
    (hc : Measurable (Function.uncurry c)) (hc0 : ∀ a b, 0 ≤ c a b) (hcB : ∃ B, ∀ a b, c a b ≤ B)
    (hh : Measurable h) (hH : ∃ H, ∀ z, |h z| ≤ H) (hN₀ : RefClass N₀) (hN₁ : RefClass N₁)
    (hQ₀ : InBall x₀ c ε r₀ N₀ Q₀) (hQ₁ : InBall x₁ c ε r₁ N₁ Q₁) :
    wassersteinEDist 2 (Q₀.map h) (Q₁.map h) ^ 2 ≤ Fbar x₀ x₁ c ε r₀ r₁ N₀ N₁ h lam₀ lam₁ := by
  obtain ⟨hP₀, ν₀, hν₀, hW₀⟩ := hQ₀
  obtain ⟨hP₁, ν₁, hν₁, hW₁⟩ := hQ₁
  obtain ⟨hf₀, hz₀, ho₀⟩ := hN₀ ν₀ hν₀
  obtain ⟨hf₁, hz₁, ho₁⟩ := hN₁ ν₁ hν₁
  have key := StatFormal.RobustEquality.Certificate.certificate K n₀ n₁ x₀ x₁ c ε r₀ r₁ lam₀ lam₁
    h ν₀ ν₁ Q₀ Q₁ hn₀ hn₁ hε hl₀ hl₁ hc hc0 hcB hh hH hz₀ ho₀ hz₁ ho₁ hW₀ hW₁
  have h₀ : ENNReal.ofReal (√(Tref1 x₀ c h ε r₀ lam₀ ν₀)) ≤ sqrtT x₀ c h ε r₀ lam₀ N₀ :=
    le_iSup₂ (f := fun ν (_ : ν ∈ N₀) => ENNReal.ofReal (√(Tref1 x₀ c h ε r₀ lam₀ ν))) ν₀ hν₀
  have h₁ : ENNReal.ofReal (√(Tref1 x₁ c h ε r₁ lam₁ ν₁)) ≤ sqrtT x₁ c h ε r₁ lam₁ N₁ :=
    le_iSup₂ (f := fun ν (_ : ν ∈ N₁) => ENNReal.ofReal (√(Tref1 x₁ c h ε r₁ lam₁ ν))) ν₁ hν₁
  unfold Fbar nominal
  exact pow_le_pow_left₀ bot_le (key.trans (add_le_add (add_le_add le_rfl h₀) h₁)) 2

theorem certificate_independent : Claims.certificate_independent := by
  intro K _ n₀ n₁ x₀ x₁ c ε r₀ r₁ lam₀ lam₁ h N₀ N₁ hn₀ hn₁ hε hl₀ hl₁ hc hc0 hcB hh hH hN₀ hN₁
  unfold Findep
  refine iSup_le fun Q₀ => iSup_le fun Q₁ => iSup_le fun hQ => ?_
  exact pair_bound x₀ x₁ c hn₀ hn₁ hε hl₀ hl₁ hc hc0 hcB hh hH hN₀ hN₁ hQ.1 hQ.2

theorem certificate_structured : Claims.certificate_structured := by
  intro K Θ _ n₀ n₁ x₀ x₁ c ε lam₀ lam₁ r₀ r₁ 𝔗 h N₀ N₁ hn₀ hn₁ hε hl₀ hl₁ hc hc0 hcB hh hH
    hN₀ hN₁
  unfold Fstruct
  refine iSup_le fun Q₀ => iSup_le fun Q₁ => iSup_le fun ⟨θ, hQ₀, hQ₁⟩ => ?_
  refine le_trans ?_ (le_iSup _ θ)
  exact pair_bound _ _ c hn₀ hn₁ hε hl₀ hl₁ hc hc0 hcB hh hH (hN₀ θ) (hN₁ θ) hQ₀ hQ₁

theorem cs_slice_T : Claims.cs_slice_T := by
  intro K _ n x c h 𝔗 ε r lam ν hc hh h𝔗
  unfold Tref1 TrefPull
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [integral_map h𝔗.aemeasurable]
  refine Measurable.aestronglyMeasurable ?_
  refine Real.measurable_exp.comp (Measurable.div_const ?_ _)
  refine Measurable.sub ((hh.sub measurable_const).pow_const 2) (measurable_const.mul ?_)
  exact hc.comp (measurable_const.prodMk measurable_id)

lemma refClass_map {N : Set (Measure K)} (hN : RefClass N) {𝔗 : K → K} (h𝔗 : Measurable 𝔗) :
    RefClass ((fun ν => ν.map 𝔗) '' N) := by
  rintro _ ⟨ν, hν, rfl⟩
  obtain ⟨hf, hz, ho⟩ := hN ν hν
  refine ⟨inferInstance, ?_, ?_⟩ <;> rw [Measure.map_apply h𝔗 MeasurableSet.univ, preimage_univ]
  · exact hz
  · exact ho

lemma sqrtT_map {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) {𝔗 : K → K}
    (ε r lam : ℝ) (N : Set (Measure K)) (hc : Measurable (Function.uncurry c))
    (hh : Measurable h) (h𝔗 : Measurable 𝔗) :
    sqrtT (fun i => 𝔗 (x i)) c h ε r lam ((fun ν => ν.map 𝔗) '' N) =
      sqrtTPull x c h 𝔗 ε r lam N := by
  unfold sqrtT sqrtTPull
  rw [iSup_image]
  refine iSup_congr fun ν => iSup_congr fun _ => ?_
  rw [cs_slice_T K n x c h 𝔗 ε r lam ν hc hh h𝔗]

theorem cs_certificate : Claims.cs_certificate := by
  intro K Θ _ n₀ n₁ x₀ x₁ c ε r₀ r₁ 𝔗 h N₀ N₁ hn₀ hn₁ hε hc hc0 hcB hh hH h𝔗 hN₀ hN₁
  unfold Fstruct
  refine iSup_le fun Q₀ => iSup_le fun Q₁ => iSup_le fun ⟨θ, hQ₀, hQ₁⟩ => ?_
  refine le_trans ?_ (le_iSup _ θ)
  refine le_iInf₂ fun lam₀ hl₀ => le_iInf₂ fun lam₁ hl₁ => ?_
  have := pair_bound _ _ c hn₀ hn₁ hε hl₀ hl₁ hc hc0 hcB hh hH (refClass_map hN₀ (h𝔗 θ))
    (refClass_map hN₁ (h𝔗 θ)) hQ₀ hQ₁
  unfold Fbar at this
  rwa [sqrtT_map x₀ c h ε _ _ N₀ hc hh (h𝔗 θ), sqrtT_map x₁ c h ε _ _ N₁ hc hh (h𝔗 θ)] at this

end StatFormal.Wave4b
