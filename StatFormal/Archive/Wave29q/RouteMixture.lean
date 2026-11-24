import StatFormal.Archive.Wave29q.Statements
import StatFormal.Lib.SchrodingerPath.Gauss
import StatFormal.Lib.SchrodingerPath.Chain

/-!
# Route — `prop:mixture` and the path-space half of `lem:equiv` (untrusted)

* The reference: `IsBrownianRef` makes `R` a probability measure with `R ∘ (X₀,X₁)⁻¹ = R₀₁` and three-time law
  `bridgeLaw ε t R₀₁` (library `brownian_three`, the Brownian-bridge decomposition `gaussPair_bridge`).
* A Schrödinger bridge `P`: data processing (Mathlib `klDiv_map_le`) and the `h`-transform `htrans R Y π`
  (library `klDiv_htrans`) show that `π = P ∘ Y⁻¹` is a static minimiser with `KL(P ‖ R) = KL(π ‖ R₀₁)`; equality in
  data processing forces `P = htrans R Y π` (library `eq_htrans_of_klDiv_le`); the three-time law of the `h`-transform
  is `bridgeLaw ε t π` (`htrans_map_pair`, `bridgeLaw_withDensity`), whose projections are `endpointMixture1` and
  `stoPlan`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave29q

open StatFormal.SchrodingerPath

section Lemmas

variable {Ω : Type*} [MeasurableSpace Ω]

instance isProbabilityMeasure_refPlan (ε : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (refPlan ε μ) := by
  unfold refPlan; infer_instance

lemma bridgeLaw_withDensity (ε t : ℝ) (ρ : Measure (ℝ × ℝ)) [SFinite ρ] {g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    (bridgeLaw ε t ρ).withDensity (fun p => g p.1) = bridgeLaw ε t (ρ.withDensity g) := by
  unfold bridgeLaw
  rw [prod_withDensity_left hg]
  have hψ : Measurable (fun q : (ℝ × ℝ) × ℝ => (q.1, (1 - t) * q.1.1 + t * q.1.2 + q.2)) := by fun_prop
  exact (map_withDensity_comp hψ (hg.comp measurable_fst)).symm

lemma bridgeLaw_map_snd (ε t : ℝ) (π : Measure (ℝ × ℝ)) [SFinite π] :
    (bridgeLaw ε t π).map Prod.snd = StatFormal.Wave4b.endpointMixture1 ε t π := by
  unfold bridgeLaw StatFormal.Wave4b.endpointMixture1
  rw [Measure.map_map measurable_snd (by fun_prop)]
  change _ = ((π.map (fun p : ℝ × ℝ => (1 - t) * p.1 + t * p.2)).prod
    (gaussianReal 0 (ε * t * (1 - t)).toNNReal)).map (fun x => x.1 + x.2)
  have h := Measure.map_prod_map π (gaussianReal 0 (ε * t * (1 - t)).toNNReal)
    (f := fun p : ℝ × ℝ => (1 - t) * p.1 + t * p.2) (g := id) (by fun_prop) measurable_id
  rw [Measure.map_id] at h
  rw [h, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma bridgeLaw_map_sto (ε t : ℝ) (π : Measure (ℝ × ℝ)) :
    (bridgeLaw ε t π).map (fun p => (p.1.1, p.2)) = StatFormal.Wave9b.stoPlan ε t π := by
  unfold bridgeLaw StatFormal.Wave9b.stoPlan
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Consequences of `IsBrownianRef`. -/
lemma ref_facts {ε : ℝ} (hε : 0 ≤ ε) {μ : Measure ℝ} [IsProbabilityMeasure μ] {X : ℝ → Ω → ℝ} {R : Measure Ω}
    (hR : IsBrownianRef ε μ X R) :
    IsProbabilityMeasure R ∧ (∀ t ∈ Icc (0 : ℝ) 1,
      R.map (fun ω => ((X 0 ω, X 1 ω), X t ω)) = bridgeLaw ε t (refPlan ε μ)) ∧
      R.map (fun ω => (X 0 ω, X 1 ω)) = refPlan ε μ := by
  obtain ⟨hmeas, hlaw⟩ := hR
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hF : ∀ t ∈ Icc (0 : ℝ) 1, Measurable (fun ω => (X 0 ω, X t ω - X 0 ω, X 1 ω - X t ω)) := fun t ht =>
    (hmeas 0 h0).prodMk (((hmeas t ht).sub (hmeas 0 h0)).prodMk ((hmeas 1 h1).sub (hmeas t ht)))
  have hRp : IsProbabilityMeasure R := by
    have : IsProbabilityMeasure (R.map (fun ω => (X 0 ω, X 0 ω - X 0 ω, X 1 ω - X 0 ω))) := by
      rw [hlaw 0 h0]; infer_instance
    exact Measure.isProbabilityMeasure_of_map (hF 0 h0).aemeasurable
  have h3 : ∀ t ∈ Icc (0 : ℝ) 1,
      R.map (fun ω => ((X 0 ω, X 1 ω), X t ω)) = bridgeLaw ε t (refPlan ε μ) := by
    intro t ht
    have e : (fun ω => ((X 0 ω, X 1 ω), X t ω)) =
        (fun p : ℝ × ℝ × ℝ => ((p.1, p.1 + p.2.1 + p.2.2), p.1 + p.2.1)) ∘
          (fun ω => (X 0 ω, X t ω - X 0 ω, X 1 ω - X t ω)) := by
      funext ω; simp only [Function.comp]; ext <;> simp
    rw [e, ← Measure.map_map (by fun_prop) (hF t ht), hlaw t ht, brownian_three μ hε ht]
    rfl
  refine ⟨hRp, h3, ?_⟩
  have hY : (fun ω => (X 0 ω, X 1 ω)) = Prod.fst ∘ (fun ω => ((X 0 ω, X 1 ω), X 0 ω)) := rfl
  rw [hY, ← Measure.map_map measurable_fst ((hmeas 0 h0).prodMk (hmeas 1 h1) |>.prodMk (hmeas 0 h0)), h3 0 h0]
  unfold bridgeLaw
  rw [Measure.map_map measurable_fst (by fun_prop)]
  change (Measure.map Prod.fst ((refPlan ε μ).prod _)) = _
  simp

variable {X : ℝ → Ω → ℝ} {μ ν : Measure ℝ}

lemma isCoupling_map {Q : Measure Ω} (h0 : Measurable (X 0)) (h1 : Measurable (X 1))
    (hQ0 : Q.map (X 0) = μ) (hQ1 : Q.map (X 1) = ν) : IsCoupling (Q.map (fun ω => (X 0 ω, X 1 ω))) μ ν := by
  constructor
  · change (Q.map _).map Prod.fst = μ
    rw [Measure.map_map measurable_fst (h0.prodMk h1)]; exact hQ0
  · change (Q.map _).map Prod.snd = ν
    rw [Measure.map_map measurable_snd (h0.prodMk h1)]; exact hQ1

lemma isProbabilityMeasure_of_coupling {π : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ] (hπ : IsCoupling π μ ν) :
    IsProbabilityMeasure π := by
  have h : π.map Prod.fst = μ := hπ.fst_eq
  have : IsProbabilityMeasure (π.map Prod.fst) := by rw [h]; infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

/-- The `h`-transform of the reference by a coupling is in the constraint set. -/
lemma isPathCoupling_htrans {R : Measure Ω} [IsProbabilityMeasure R] [IsProbabilityMeasure μ]
    (h0 : Measurable (X 0)) (h1 : Measurable (X 1)) {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν)
    (hac : π ≪ R.map (fun ω => (X 0 ω, X 1 ω))) :
    IsPathCoupling X μ ν (htrans R (fun ω => (X 0 ω, X 1 ω)) π) := by
  have hπp := isProbabilityMeasure_of_coupling hπ
  have hY : Measurable (fun ω => (X 0 ω, X 1 ω)) := h0.prodMk h1
  have hm := htrans_map hY hac
  refine ⟨isProbabilityMeasure_htrans hY hac, ?_, ?_⟩
  · have e : (htrans R (fun ω => (X 0 ω, X 1 ω)) π).map (X 0) =
        ((htrans R (fun ω => (X 0 ω, X 1 ω)) π).map (fun ω => (X 0 ω, X 1 ω))).map Prod.fst := by
      rw [Measure.map_map measurable_fst hY]; rfl
    rw [e, hm]; exact hπ.fst_eq
  · have e : (htrans R (fun ω => (X 0 ω, X 1 ω)) π).map (X 1) =
        ((htrans R (fun ω => (X 0 ω, X 1 ω)) π).map (fun ω => (X 0 ω, X 1 ω))).map Prod.snd := by
      rw [Measure.map_map measurable_snd hY]; rfl
    rw [e, hm]; exact hπ.snd_eq

/-- The structure of a Schrödinger bridge. -/
lemma sb_structure {ε : ℝ} (hε : 0 ≤ ε) [IsProbabilityMeasure μ] {R P : Measure Ω}
    (hR : IsBrownianRef ε μ X R) (hP : IsSchrodingerBridge X R μ ν P) :
    IsStaticBridge ε μ ν (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
      klDiv P R = klDiv (P.map (fun ω => (X 0 ω, X 1 ω))) (refPlan ε μ) ∧
      P = htrans R (fun ω => (X 0 ω, X 1 ω)) (P.map (fun ω => (X 0 ω, X 1 ω))) := by
  obtain ⟨hRp, -, hRY⟩ := ref_facts hε hR
  have h0 : Measurable (X 0) := hR.1 0 ⟨le_rfl, zero_le_one⟩
  have h1 : Measurable (X 1) := hR.1 1 ⟨zero_le_one, le_rfl⟩
  have hY : Measurable (fun ω => (X 0 ω, X 1 ω)) := h0.prodMk h1
  obtain ⟨⟨hPp, hP0, hP1⟩, hPfin, hPmin⟩ := hP
  set Y := fun ω => (X 0 ω, X 1 ω)
  have hπc : IsCoupling (P.map Y) μ ν := isCoupling_map h0 h1 hP0 hP1
  have hdp : ∀ Q : Measure Ω, IsFiniteMeasure Q → klDiv (Q.map Y) (refPlan ε μ) ≤ klDiv Q R := fun Q _ => by
    rw [← hRY]; exact klDiv_map_le Q R hY
  have hPR : P ≪ R := (klDiv_ne_top_iff.1 hPfin).1
  have hπac : P.map Y ≪ R.map Y := hPR.map hY
  -- `KL(P ‖ R) ≤ KL(π' ‖ R₀₁)` for every coupling `π'`
  have hup : ∀ π' : Measure (ℝ × ℝ), IsCoupling π' μ ν → klDiv P R ≤ klDiv π' (refPlan ε μ) := by
    intro π' hπ'
    by_cases hk : klDiv π' (refPlan ε μ) = ∞
    · rw [hk]; exact le_top
    have hac' : π' ≪ R.map Y := by rw [hRY]; exact (klDiv_ne_top_iff.1 hk).1
    have := isProbabilityMeasure_of_coupling hπ'
    calc klDiv P R ≤ klDiv (htrans R Y π') R := hPmin _ (isPathCoupling_htrans h0 h1 hπ' hac')
      _ = klDiv π' (R.map Y) := klDiv_htrans hY hac'
      _ = klDiv π' (refPlan ε μ) := by rw [hRY]
  have heq : klDiv P R = klDiv (P.map Y) (refPlan ε μ) := le_antisymm (hup _ hπc) (hdp P inferInstance)
  refine ⟨⟨hπc, ?_, fun π' hπ' => (hdp P inferInstance).trans (hup π' hπ')⟩, heq, ?_⟩
  · rw [← heq]; exact hPfin
  · exact eq_htrans_of_klDiv_le hY hPfin (by rw [hRY]; exact heq.le)

end Lemmas

theorem mixture_bridge : Claims.mixture_bridge := by
  intro Ω _ ε μ ν X R P hε hμ hR hP
  obtain ⟨hRp, h3, hRY⟩ := ref_facts hε.le hR
  obtain ⟨hstat, hkl, hP_eq⟩ := sb_structure hε.le hR hP
  have h0 : Measurable (X 0) := hR.1 0 ⟨le_rfl, zero_le_one⟩
  have h1 : Measurable (X 1) := hR.1 1 ⟨zero_le_one, le_rfl⟩
  have hY : Measurable (fun ω => (X 0 ω, X 1 ω)) := h0.prodMk h1
  set Y := fun ω => (X 0 ω, X 1 ω)
  set π := P.map Y
  have hPp : IsProbabilityMeasure P := hP.1.1
  have hPR : P ≪ R := (klDiv_ne_top_iff.1 hP.2.1).1
  have hπac : π ≪ R.map Y := hPR.map hY
  set g := π.rnDeriv (R.map Y)
  have hg : Measurable g := Measure.measurable_rnDeriv _ _
  have hπg : π = (refPlan ε μ).withDensity g := by
    rw [← hRY]; exact (Measure.withDensity_rnDeriv_eq _ _ hπac).symm
  have h3P : ∀ t ∈ Icc (0 : ℝ) 1, P.map (fun ω => (Y ω, X t ω)) = bridgeLaw ε t π := by
    intro t ht
    have hXt : Measurable (X t) := hR.1 t ht
    rw [hP_eq, htrans_map_pair hY hXt π]
    have e := h3 t ht
    change R.map (fun ω => (Y ω, X t ω)) = _ at e
    rw [e, bridgeLaw_withDensity ε t _ hg, ← hRY, Measure.withDensity_rnDeriv_eq _ _ hπac]
  refine ⟨hRY, hstat, hkl, ⟨g, hg, hπg, hP_eq⟩, fun t ht => ⟨h3P t ht, ?_, ?_⟩⟩
  · have hXt : Measurable (X t) := hR.1 t ht
    have e : X t = Prod.snd ∘ (fun ω => (Y ω, X t ω)) := rfl
    rw [e, ← Measure.map_map measurable_snd (hY.prodMk hXt), h3P t ht, bridgeLaw_map_snd]
  · have hXt : Measurable (X t) := hR.1 t ht
    have e : (fun ω => (X 0 ω, X t ω)) = (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.2)) ∘ (fun ω => (Y ω, X t ω)) := rfl
    rw [e, ← Measure.map_map (by fun_prop) (hY.prodMk hXt), h3P t ht, bridgeLaw_map_sto]

theorem mixture_exists : Claims.mixture_exists := by
  intro Ω _ ε μ ν X R hε hμ hR
  obtain ⟨hRp, -, hRY⟩ := ref_facts hε.le hR
  have h0 : Measurable (X 0) := hR.1 0 ⟨le_rfl, zero_le_one⟩
  have h1 : Measurable (X 1) := hR.1 1 ⟨zero_le_one, le_rfl⟩
  have hY : Measurable (fun ω => (X 0 ω, X 1 ω)) := h0.prodMk h1
  refine ⟨fun π hπ => ?_, fun P P' hP hP' he => ?_⟩
  · obtain ⟨hπc, hπfin, hπmin⟩ := hπ
    have hac : π ≪ R.map (fun ω => (X 0 ω, X 1 ω)) := by rw [hRY]; exact (klDiv_ne_top_iff.1 hπfin).1
    have := isProbabilityMeasure_of_coupling hπc
    have hkl := klDiv_htrans hY hac
    rw [hRY] at hkl
    refine ⟨htrans R (fun ω => (X 0 ω, X 1 ω)) π, ⟨isPathCoupling_htrans h0 h1 hπc hac, ?_, fun Q hQ => ?_⟩,
      htrans_map hY hac⟩
    · rw [hkl]; exact hπfin
    · obtain ⟨hQp, hQ0, hQ1⟩ := hQ
      rw [hkl]
      refine (hπmin _ (isCoupling_map h0 h1 hQ0 hQ1)).trans ?_
      rw [← hRY]; exact klDiv_map_le Q R hY
  · rw [(sb_structure hε.le hR hP).2.2, (sb_structure hε.le hR hP').2.2, he]

/-! ### Non-vacuity of the reference hypothesis (route lemmas, not targets) -/

/-- The witness reference: `(x, z₁, z₂) ↦ (x, √ε z₁, √ε z₂)` pushes `μ ⊗ N(0,1) ⊗ N(0,1)` to `μ ⊗ N(0,ε) ⊗ N(0,ε)`. -/
def refMeasure (ε : ℝ) (μ : Measure ℝ) : Measure (ℝ × ℝ × ℝ) :=
  (μ.prod std2).map (fun ω => (ω.1, √ε * ω.2.1, √ε * ω.2.2))

instance isProbabilityMeasure_refMeasure (ε : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (refMeasure ε μ) :=
  by unfold refMeasure; infer_instance

/-- ONE process `X_t(x, z₁, z₂) = x + t z₁ + √(t(1−t)) z₂` on `ℝ³` (independent of `ε` and `μ`) carries an `ε`-Brownian
reference started from `μ` for every `ε ≥ 0` and every probability `μ` (it is not a Brownian motion: only the
three-time laws match). This witnesses the satisfiability of every `IsBrownianRef` premise, including the families
`R ε` on one `(Ω, X)` of the `θ`/limit claims and the two references `R₀`, `R₁` on one `(Ω, X)` of `gaussianthm_*`. -/
theorem isBrownianRef_refMeasure {ε : ℝ} (hε : 0 ≤ ε) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsBrownianRef ε μ (refWitness 1) (refMeasure ε μ) := by
  refine ⟨fun t _ => measurable_refWitness 1 t, fun t ht => ?_⟩
  unfold refMeasure
  rw [Measure.map_map (by
    exact (measurable_refWitness 1 0).prodMk (((measurable_refWitness 1 t).sub (measurable_refWitness 1 0)).prodMk
      ((measurable_refWitness 1 1).sub (measurable_refWitness 1 t)))) (by fun_prop)]
  rw [← refWitness_law μ hε ht]
  congr 1
  funext ω
  simp only [refWitness, Function.comp, Real.sqrt_one, one_mul]
  ext <;> simp <;> ring

theorem brownianRef_exists : ∃ X : ℝ → ℝ × ℝ × ℝ → ℝ, ∀ (ε : ℝ) (μ : Measure ℝ), 0 ≤ ε → IsProbabilityMeasure μ →
    ∃ R : Measure (ℝ × ℝ × ℝ), IsProbabilityMeasure R ∧ IsBrownianRef ε μ X R :=
  ⟨refWitness 1, fun ε μ hε _ => ⟨refMeasure ε μ, inferInstance, isBrownianRef_refMeasure hε μ⟩⟩

end StatFormal.Wave29q
