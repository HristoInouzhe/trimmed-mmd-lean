import StatFormal.Archive.Wave9b.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward
import TauCeti.MeasureTheory.OptimalTransport.GraphPlan.Basic

/-!
# Route: SB `thm:field` (exactness, the deterministic triangle bound, the `O_P(r_n)` rate)

1. Exactness: `(S_ν⁻¹ ∘ S_{R_s})_#R_s = (S_ν⁻¹)_#γ = (S_ν⁻¹ ∘ S_ν)_#ν = ν`.
2. Two maps of one law: `W₂(f_#μ, g_#μ) ≤ ‖f − g‖_{L²(μ)}` (diagonal coupling, Tau Ceti
   `wassersteinEDist_map_le_eLpNorm`).
3. Triangle inequality through `(Ŝ_ν⁻¹)_#γ` (Tau Ceti `wassersteinEDist_triangle`), Lipschitz
   `Ŝ_ν⁻¹` for the first leg.
4. `O_P`: intersect the four measurable events (union bound) and add the bounds.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set Filter
open scoped ENNReal NNReal Topology

namespace StatFormal.Wave9b

local notation "𝔼" d => EuclideanSpace ℝ (Fin d)

lemma field_exact_one {d : ℕ} {μ ν γ : Measure (𝔼 d)} {S Sinv Sν Sνinv : (𝔼 d) → (𝔼 d)}
    (hS : Standardises μ γ S Sinv) (hν : Standardises ν γ Sν Sνinv) :
    μ.map (Sνinv ∘ S) = ν := by
  obtain ⟨hSm, -, hSmap, -, -⟩ := hS
  obtain ⟨hνm, hνim, hνmap, hνinv, -⟩ := hν
  rw [← Measure.map_map hνim hSm, hSmap, ← hνmap, Measure.map_map hνim hνm]
  rw [Measure.map_congr (show (Sνinv ∘ Sν) =ᵐ[ν] id from hνinv), Measure.map_id]

theorem field_exact : Claims.field_exact := by
  intro d R ν γ S Sinv Sν Sνinv hS hν s
  exact field_exact_one (hS s) hν

/-- Two measurable maps of one law. -/
lemma w2_map_map_le {d : ℕ} (μ : Measure (𝔼 d)) {f g : (𝔼 d) → (𝔼 d)} (hf : Measurable f)
    (hg : Measurable g) :
    wassersteinEDist 2 (μ.map f) (μ.map g) ≤ eLpNorm (fun x => f x - g x) 2 μ := by
  have hπ : IsCoupling (graphPlan id μ) μ μ := by
    simpa [Measure.map_id] using isCoupling_graphPlan_map (μ := μ) (T := id) aemeasurable_id
  refine (wassersteinEDist_map_le_eLpNorm hπ hf.aestronglyMeasurable
    hg.aestronglyMeasurable).trans_eq ?_
  rw [graphPlan_def, eLpNorm_map_measure]
  · refine eLpNorm_congr_enorm_ae ?_ ((hf.sub hg).aestronglyMeasurable) (.of_forall fun x => ?_)
    · exact (continuous_edist.measurable.comp (hf.prodMk hg)).aestronglyMeasurable
    · simp [edist_eq_enorm_sub]
  · exact (continuous_edist.measurable.comp (hf.prodMap hg)).aestronglyMeasurable
  · exact (measurable_id.prodMk measurable_id).aemeasurable

lemma field_bound_one {d : ℕ} {μ ν γ : Measure (𝔼 d)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure γ] {S Sinv Shat Sν Sνinv Sνinvhat : (𝔼 d) → (𝔼 d)} {L : ℝ≥0}
    (hS : Standardises μ γ S Sinv) (hν : Standardises ν γ Sν Sνinv) (hShat : Measurable Shat)
    (hinv : Measurable Sνinvhat) (hL : LipschitzWith L Sνinvhat) :
    wassersteinEDist 2 (μ.map (Sνinvhat ∘ Shat)) ν ≤
      L * eLpNorm (fun x => Shat x - S x) 2 μ + eLpNorm (fun z => Sνinvhat z - Sνinv z) 2 γ := by
  have hSm := hS.1
  have hνim := hν.2.1
  have hγν : γ.map Sνinv = ν := by
    have := field_exact_one hν hν
    obtain ⟨hνm, -, hνmap, -, -⟩ := hν
    rw [← hνmap, Measure.map_map hνim hνm]; exact this
  have hmid : γ.map Sνinvhat = μ.map (Sνinvhat ∘ S) := by
    rw [← hS.2.2.1, Measure.map_map hinv hSm]
  calc wassersteinEDist 2 (μ.map (Sνinvhat ∘ Shat)) ν
      ≤ wassersteinEDist 2 (μ.map (Sνinvhat ∘ Shat)) (γ.map Sνinvhat) +
          wassersteinEDist 2 (γ.map Sνinvhat) ν :=
        wassersteinEDist_triangle measurable_edist (by norm_num) _ _ _
    _ ≤ L * eLpNorm (fun x => Shat x - S x) 2 μ +
          eLpNorm (fun z => Sνinvhat z - Sνinv z) 2 γ := by
        gcongr
        · rw [hmid]
          refine (w2_map_map_le μ (hinv.comp hShat) (hinv.comp hSm)).trans ?_
          refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (g := fun x => Shat x - S x)
            (c := L) ?_ (.of_forall fun x => ?_) 2).trans_eq ?_
          · exact ((hinv.comp hShat).sub (hinv.comp hSm)).aestronglyMeasurable
          · simpa [edist_eq_enorm_sub] using hL.edist_le_mul (Shat x) (S x)
          · simp [ENNReal.smul_def]
        · rw [← hγν]
          exact w2_map_map_le γ hinv hν.2.1

theorem field_bound : Claims.field_bound := by
  intro d R ν γ S Sinv Shat Sν Sνinv Sνinvhat L hR hν hγ hS hSν hShat hinv hL
  have one : ∀ s, wassersteinEDist 2 ((R s).map (Sνinvhat ∘ Shat s)) ν ≤
      L * eLpNorm (fun x => Shat s x - S s x) 2 (R s) +
        eLpNorm (fun z => Sνinvhat z - Sνinv z) 2 γ := fun s => by
    have := hR s
    exact field_bound_one (hS s) hSν (hShat s) hinv hL
  refine ⟨one, ?_⟩
  rw [Fin.sum_univ_two]
  calc _ ≤ wassersteinEDist 2 ((R 0).map (Sνinvhat ∘ Shat 0)) ν +
        wassersteinEDist 2 ν ((R 1).map (Sνinvhat ∘ Shat 1)) :=
        wassersteinEDist_triangle measurable_edist (by norm_num) _ _ _
    _ ≤ _ := by
        rw [wassersteinEDist_comm measurable_edist 2 ν]
        exact add_le_add (one 0) (one 1)

/-! ### The rate -/

lemma compl_le_of_ofReal_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A) {a : ℝ} (ha : 0 ≤ a)
    (h : ENNReal.ofReal (1 - a) ≤ P A) : P Aᶜ ≤ ENNReal.ofReal a := by
  rw [prob_compl_eq_one_sub hA]
  rcases le_total a 1 with h1 | h1
  · rw [ENNReal.ofReal_sub _ ha, ENNReal.ofReal_one] at h
    calc 1 - P A ≤ 1 - (1 - ENNReal.ofReal a) := tsub_le_tsub_left h _
      _ = ENNReal.ofReal a := ENNReal.sub_sub_cancel ENNReal.one_ne_top
          (by simpa using ENNReal.ofReal_le_ofReal h1)
  · calc 1 - P A ≤ 1 := tsub_le_self
      _ ≤ ENNReal.ofReal a := by simpa using ENNReal.ofReal_le_ofReal h1

lemma ofReal_le_of_compl_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A) {a : ℝ} (ha : 0 ≤ a)
    (h : P Aᶜ ≤ ENNReal.ofReal a) : ENNReal.ofReal (1 - a) ≤ P A := by
  rw [prob_compl_eq_one_sub hA] at h
  rcases le_total a 1 with h1 | h1
  · rw [ENNReal.ofReal_sub _ ha, ENNReal.ofReal_one]
    have hPA : P A ≤ 1 := prob_le_one
    calc 1 - ENNReal.ofReal a ≤ 1 - (1 - P A) := tsub_le_tsub_left h _
      _ = P A := ENNReal.sub_sub_cancel ENNReal.one_ne_top hPA
  · rw [ENNReal.ofReal_of_nonpos (by linarith)]; exact bot_le

theorem field_rate : Claims.field_rate := by
  intro d R ν γ S Sinv Sν Sνinv Ω _ P Shat Sνinvhat r L hP hr hR hν hγ hS hSν hShat hinv
    hO hOi hLip η hη
  have hη4 : 0 < η / 4 := by positivity
  obtain ⟨M₀, N₀, h₀⟩ := hO 0 (η / 4) hη4
  obtain ⟨M₁, N₁, h₁⟩ := hO 1 (η / 4) hη4
  obtain ⟨Mi, Ni, hi⟩ := hOi (η / 4) hη4
  obtain ⟨A, hAm, hAt, hAL⟩ := hLip
  have hev : ∀ᶠ n in atTop, ENNReal.ofReal (1 - η / 4) < P (A n) := by
    refine hAt.eventually (lt_mem_nhds ?_)
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)
  obtain ⟨NL, hNL⟩ := eventually_atTop.1 hev
  refine ⟨L * max M₀ 0 + L * max M₁ 0 + 2 * max Mi 0, max (max N₀ N₁) (max Ni NL), fun n hn => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hn
  obtain ⟨B₀, hB₀m, hB₀P, hB₀⟩ := h₀ n hn.1.1
  obtain ⟨B₁, hB₁m, hB₁P, hB₁⟩ := h₁ n hn.1.2
  obtain ⟨Bi, hBim, hBiP, hBi⟩ := hi n hn.2.1
  refine ⟨B₀ ∩ B₁ ∩ Bi ∩ A n, ((hB₀m.inter hB₁m).inter hBim).inter (hAm n), ?_, ?_⟩
  · refine ofReal_le_of_compl_le (((hB₀m.inter hB₁m).inter hBim).inter (hAm n)) hη.le ?_
    have c₀ := compl_le_of_ofReal_le hB₀m hη4.le hB₀P
    have c₁ := compl_le_of_ofReal_le hB₁m hη4.le hB₁P
    have ci := compl_le_of_ofReal_le hBim hη4.le hBiP
    have cL := compl_le_of_ofReal_le (hAm n) hη4.le (hNL n hn.2.2).le
    calc P (B₀ ∩ B₁ ∩ Bi ∩ A n)ᶜ ≤ P B₀ᶜ + P B₁ᶜ + P Biᶜ + P (A n)ᶜ := by
          simp only [compl_inter]
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) +
            ENNReal.ofReal (η / 4) := by gcongr
      _ = ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_add hη4.le hη4.le, ← ENNReal.ofReal_add (by positivity) hη4.le,
            ← ENNReal.ofReal_add (by positivity) hη4.le]
          congr 1; ring
  · rintro ω ⟨⟨⟨hω₀, hω₁⟩, hωi⟩, hωA⟩
    have hb := (field_bound d R ν γ S Sinv (Shat n ω) Sν Sνinv (Sνinvhat n ω) L hR hν hγ hS hSν
      (hShat n ω) (hinv n ω) (hAL n ω hωA)).2
    refine hb.trans ?_
    rw [Fin.sum_univ_two]
    have hrn := hr n
    have e₀ : eLpNorm (fun x => Shat n ω 0 x - S 0 x) 2 (R 0) ≤
        ENNReal.ofReal (max M₀ 0 * r n) :=
      (hB₀ ω hω₀).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
    have e₁ : eLpNorm (fun x => Shat n ω 1 x - S 1 x) 2 (R 1) ≤
        ENNReal.ofReal (max M₁ 0 * r n) :=
      (hB₁ ω hω₁).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
    have ei : eLpNorm (fun z => Sνinvhat n ω z - Sνinv z) 2 γ ≤
        ENNReal.ofReal (max Mi 0 * r n) :=
      (hBi ω hωi).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
    have hL0 : (L : ℝ≥0∞) = ENNReal.ofReal (L : ℝ) := by simp
    calc _ ≤ (L : ℝ≥0∞) * ENNReal.ofReal (max M₀ 0 * r n) + ENNReal.ofReal (max Mi 0 * r n) +
          ((L : ℝ≥0∞) * ENNReal.ofReal (max M₁ 0 * r n) + ENNReal.ofReal (max Mi 0 * r n)) := by
          gcongr
      _ = ENNReal.ofReal ((L * max M₀ 0 + L * max M₁ 0 + 2 * max Mi 0) * r n) := by
          have h0 : 0 ≤ max M₀ 0 * r n := mul_nonneg (le_max_right _ _) hrn
          have h1 : 0 ≤ max M₁ 0 * r n := mul_nonneg (le_max_right _ _) hrn
          have h2 : 0 ≤ max Mi 0 * r n := mul_nonneg (le_max_right _ _) hrn
          have hL' := NNReal.coe_nonneg L
          rw [hL0, ← ENNReal.ofReal_mul hL', ← ENNReal.ofReal_mul hL',
            ← ENNReal.ofReal_add (mul_nonneg hL' h0) h2,
            ← ENNReal.ofReal_add (mul_nonneg hL' h1) h2,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring

end StatFormal.Wave9b
