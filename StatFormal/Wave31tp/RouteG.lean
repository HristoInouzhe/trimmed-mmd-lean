import StatFormal.Wave31tp.Statements
import StatFormal.Lib.TIKernel.Gram
import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
# Wave 31tp, route G: Gram-only dependence (untrusted proof file)

L12 (a)–(c) from `Lib/TIKernel/Gram.lean` (the Gram isometry of the closed span, projections, Bochner integrals).
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tp.RouteG

open StatFormal.TIKernel

theorem gram_iso_route : Claims.gram_iso := by
  intro 𝒳 H H' _ _ _ _ _ _ φ φ' hG
  exact ⟨gramIso hG, gramIso_apply hG⟩

theorem gram_rep_route : Claims.gram_rep := by
  intro 𝒳 H H' _ _ _ _ _ _ φ φ' hG g
  exact gram_rep_le hG g

section MMD

variable {𝒳 H H' : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H'] {φ : 𝒳 → H} {φ' : 𝒳 → H'} {κ : ℝ}

lemma integrable_smul_phi (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (μ : Measure 𝒳) [IsFiniteMeasure μ]
    {u : 𝒳 → ℝ} (hu : Measurable u) {C : ℝ} (hC : ∀ x, |u x| ≤ C) :
    Integrable (fun x => u x • φ x) μ := by
  refine Integrable.mono' (integrable_const (C * κ)) (hu.stronglyMeasurable.smul hφ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hC x) (hκ x) (norm_nonneg _) ((abs_nonneg _).trans (hC x))

lemma norm_eq_gram (hG : ∀ x y, ⟪φ x, φ y⟫ = ⟪φ' x, φ' y⟫) (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (u v : 𝒳 → ℝ) (hu : Measurable u)
    (hv : Measurable v) (hub : ∃ C, ∀ x, |u x| ≤ C) (hvb : ∃ C, ∀ x, |v x| ≤ C) :
    ‖∫ x, u x • φ x ∂μ - ∫ x, v x • φ x ∂ν‖ = ‖∫ x, u x • φ' x ∂μ - ∫ x, v x • φ' x ∂ν‖ := by
  obtain ⟨C, hC⟩ := hub
  obtain ⟨D, hD⟩ := hvb
  exact norm_integral_gram hG (integrable_smul_phi hφ hκ μ hu hC) (integrable_smul_phi hφ hκ ν hv hD)

lemma norm_eq_gram_one (hG : ∀ x y, ⟪φ x, φ y⟫ = ⟪φ' x, φ' y⟫) (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ‖∫ x, φ x ∂μ - ∫ x, φ x ∂ν‖ = ‖∫ x, φ' x ∂μ - ∫ x, φ' x ∂ν‖ := by
  have := norm_eq_gram hG hφ hκ μ ν (fun _ => 1) (fun _ => 1) measurable_const measurable_const
    ⟨1, fun _ => by simp⟩ ⟨1, fun _ => by simp⟩
  simpa using this

lemma region_dist_eq (hG : ∀ x y, ⟪φ x, φ y⟫ = ⟪φ' x, φ' y⟫) (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (P Q : Measure 𝒳) [IsFiniteMeasure P] [IsFiniteMeasure Q] (α : ℝ) :
    StatFormal.TrimmedMMD.Unconditional.setDist (StatFormal.TrimmedMMD.Concentration.region φ α P)
        (StatFormal.TrimmedMMD.Concentration.region φ α Q) =
      StatFormal.TrimmedMMD.Unconditional.setDist (StatFormal.TrimmedMMD.Concentration.region φ' α P)
        (StatFormal.TrimmedMMD.Concentration.region φ' α Q) := by
  unfold StatFormal.TrimmedMMD.Unconditional.setDist StatFormal.TrimmedMMD.Concentration.region
  congr 1
  ext r
  have key : ∀ g h : 𝒳 → ℝ, Measurable g → Measurable h → (∀ x, 0 ≤ g x ∧ g x ≤ 1 / (1 - α)) →
      (∀ x, 0 ≤ h x ∧ h x ≤ 1 / (1 - α)) →
      ‖∫ x, g x • φ x ∂P - ∫ x, h x • φ x ∂Q‖ = ‖∫ x, g x • φ' x ∂P - ∫ x, h x • φ' x ∂Q‖ := by
    intro g h hg hh hgb hhb
    refine norm_eq_gram hG hφ hκ P Q g h hg hh ⟨|1 / (1 - α)|, fun x => ?_⟩ ⟨|1 / (1 - α)|, fun x => ?_⟩
    · rw [abs_of_nonneg (hgb x).1]; exact (hgb x).2.trans (le_abs_self _)
    · rw [abs_of_nonneg (hhb x).1]; exact (hhb x).2.trans (le_abs_self _)
  constructor
  · rintro ⟨a, ⟨g, hg, hgb, hgi, rfl⟩, b, ⟨h, hh, hhb, hhi, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, hgb, hgi, rfl⟩, _, ⟨h, hh, hhb, hhi, rfl⟩, key g h hg hh hgb hhb⟩
  · rintro ⟨a, ⟨g, hg, hgb, hgi, rfl⟩, b, ⟨h, hh, hhb, hhi, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, hgb, hgi, rfl⟩, _, ⟨h, hh, hhb, hhi, rfl⟩, (key g h hg hh hgb hhb).symm⟩

end MMD

theorem gram_mmd_route : Claims.gram_mmd := by
  intro 𝒳 H H' _ _ _ _ _ _ _ φ φ' κ hG hφ hκ
  have hφ' : StronglyMeasurable φ' := by
    have : φ' = fun x => gramCLM hG (φ x) := funext (phi'_eq_clm hG)
    rw [this]
    exact (gramCLM hG).continuous.comp_stronglyMeasurable hφ
  have hκ' : ∀ x, ‖φ' x‖ ≤ κ := fun x => by rw [norm_phi'_eq hG]; exact hκ x
  refine ⟨fun μ ν _ _ u v hu hv hub hvb => norm_eq_gram hG hφ hκ μ ν u v hu hv hub hvb, hφ', hκ', ?_, ?_⟩
  · intro P Q _ _ α
    refine ⟨norm_eq_gram_one hG hφ hκ P Q, ?_, region_dist_eq hG hφ hκ P Q α⟩
    unfold StatFormal.Wave8a.dTrim
    congr 1
    ext r
    constructor
    · rintro ⟨P', hP', Q', hQ', rfl⟩
      have := hP'.1; have := hQ'.1
      exact ⟨P', hP', Q', hQ', norm_eq_gram_one hG hφ hκ P' Q'⟩
    · rintro ⟨P', hP', Q', hQ', rfl⟩
      have := hP'.1; have := hQ'.1
      exact ⟨P', hP', Q', hQ', (norm_eq_gram_one hG hφ hκ P' Q').symm⟩
  · intro n m x y α
    have : IsFiniteMeasure (StatFormal.TrimmedMMD.Concentration.empirical x) := by
      unfold StatFormal.TrimmedMMD.Concentration.empirical
      constructor
      simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      exact ENNReal.sum_lt_top.2 fun _ _ => ENNReal.ofReal_lt_top
    have : IsFiniteMeasure (StatFormal.TrimmedMMD.Concentration.empirical y) := by
      unfold StatFormal.TrimmedMMD.Concentration.empirical
      constructor
      simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      exact ENNReal.sum_lt_top.2 fun _ _ => ENNReal.ofReal_lt_top
    exact region_dist_eq hG hφ hκ _ _ α

theorem rkhs_canonical_route : Claims.rkhs_canonical := by
  intro 𝒳 H _ _ _ _
  have h1 : ∀ (f : H) (x : 𝒳), ⟪f, RKHS.kerFun H x (1 : ℝ)⟫ = f x := fun f x => by
    rw [RKHS.inner_kerFun]; simp
  have h2 : ∀ x y : 𝒳, ⟪RKHS.kerFun H x (1 : ℝ), RKHS.kerFun H y (1 : ℝ)⟫ = RKHS.kernel H y x (1 : ℝ) :=
    fun x y => by rw [h1, RKHS.kerFun_apply]
  have hspan : Submodule.span ℝ {f : H | ∃ (x : 𝒳) (v : ℝ), RKHS.kerFun H x v = f} =
      Submodule.span ℝ (Set.range fun x : 𝒳 => RKHS.kerFun H x (1 : ℝ)) := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, v, rfl⟩
      have : RKHS.kerFun H x v = v • RKHS.kerFun H x (1 : ℝ) := by
        rw [← map_smul, smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, rfl⟩
      exact Submodule.subset_span ⟨x, 1, rfl⟩
  have htop : (Submodule.span ℝ (Set.range fun x : 𝒳 => RKHS.kerFun H x (1 : ℝ))).topologicalClosure = ⊤ := by
    rw [← hspan]
    have := RKHS.kerFun_dense (𝕜 := ℝ) (H := H) (X := 𝒳) (V := ℝ)
    convert this using 3
  have h3 : Dense (Submodule.span ℝ (Set.range fun x : 𝒳 => RKHS.kerFun H x (1 : ℝ)) : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr htop
  refine ⟨h1, h2, h3, ?_⟩
  intro H' _ _ _ φ' hφ' u
  set φH : 𝒳 → H := fun x => RKHS.kerFun H x (1 : ℝ)
  have hG : ∀ x y, ⟪φH x, φH y⟫ = ⟪φ' x, φ' y⟫ := fun x y => by rw [hφ', h2]
  have hG' : ∀ x y, ⟪φ' x, φ' y⟫ = ⟪φH x, φH y⟫ := fun x y => (hG x y).symm
  have hrepH : ∀ g : H, (∀ x, ⟪g, φH x⟫ = u x) ↔ ⇑g = u := fun g =>
    ⟨fun h => funext fun x => by rw [← h x, h1], fun h x => by rw [h1, h]⟩
  refine ⟨⟨fun ⟨g', hg'⟩ => ?_, fun ⟨f, hf⟩ => ?_⟩, fun f hf => ?_⟩
  · obtain ⟨g, -, hg⟩ := gram_rep_le hG' g'
    exact ⟨g, (hrepH g).mp fun x => by rw [hg, hg']⟩
  · obtain ⟨g', -, hg'⟩ := gram_rep_le hG f
    exact ⟨g', fun x => by rw [hg', (hrepH f).mpr hf x]⟩
  · have hf' : f ∈ spanCl φH := by
      show f ∈ (Submodule.span ℝ (Set.range φH)).topologicalClosure
      rw [htop]; trivial
    obtain ⟨hn, hi⟩ := gram_rep_eq hG ⟨f, hf'⟩
    refine ⟨gramIso hG ⟨f, hf'⟩, fun x => by rw [hi]; exact (hrepH f).mpr hf x, hn.trans rfl, ?_⟩
    intro g' hg'
    obtain ⟨g, hgn, hg⟩ := gram_rep_le hG' g'
    have : g = f := RKHS.ext fun x => by
      have := (hrepH g).mp (fun x => by rw [hg, hg'])
      rw [this, hf]
    rw [hn]
    calc ‖(⟨f, hf'⟩ : spanCl φH)‖ = ‖f‖ := rfl
      _ = ‖g‖ := by rw [this]
      _ ≤ ‖g'‖ := hgn

end StatFormal.Wave31tp.RouteG
