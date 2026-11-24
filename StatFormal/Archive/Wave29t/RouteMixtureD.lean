import StatFormal.Archive.Wave29t.Statements
import StatFormal.Lib.SchrodingerPathD.Gauss
import StatFormal.Lib.SchrodingerPath.Chain
import StatFormal.Lib.SchrodingerPath.Exists

/-!
# Route — `prop:mixture` and `lem:equiv` on path space in `ℝᵈ` (untrusted)

The `d = 1` argument of the frozen wave 29q (`RouteMixture`) with `ℝ` replaced by `ℝᵈ = EuclideanSpace ℝ (Fin d)`:
* the reference: library `brownian_threeD` (Brownian-bridge decomposition `gaussPairD_bridge`, proved with
  characteristic functionals on `ℝᵈ × ℝᵈ`) gives `R ∘ (X₀,X₁)⁻¹ = R₀₁` and the three-time law `bridgeLawD ε t R₀₁`;
* a Schrödinger bridge: data processing and the (dimension-free) `h`-transform library `Chain`;
* the time-`t` law: `N(0, cI) = Law(√c Z)` (library `isoG_eq_map`) and `Measure.conv`;
* existence/uniqueness: the generic static library `Exists` (Tau Ceti).
Non-vacuity (route lemma): `isBrownianRefD_witness` (one process on `(ℝᵈ)³` carrying an `ε`-Brownian reference for
every `ε ≥ 0` and every probability `μ`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave29t

open StatFormal.SchrodingerPath StatFormal.SchrodingerPathD

local notation "E" d => EuclideanSpace ℝ (Fin d)

lemma isoGauss_eq (d : ℕ) (s : ℝ) : isoGauss d s = isoG d s := rfl

instance isProbabilityMeasure_isoGauss (d : ℕ) (s : ℝ) : IsProbabilityMeasure (isoGauss d s) := by
  unfold isoGauss; infer_instance

instance isProbabilityMeasure_refPlanD {d : ℕ} (ε : ℝ) (μ : Measure (E d)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (refPlanD ε μ) := by
  unfold refPlanD isoGauss; infer_instance

section Lemmas

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma bridgeLawD_withDensity (ε t : ℝ) (ρ : Measure ((E d) × (E d))) [SFinite ρ] {g : (E d) × (E d) → ℝ≥0∞}
    (hg : Measurable g) :
    (bridgeLawD ε t ρ).withDensity (fun p => g p.1) = bridgeLawD ε t (ρ.withDensity g) := by
  unfold bridgeLawD
  rw [prod_withDensity_left hg]
  have hψ : Measurable (fun q : ((E d) × (E d)) × (E d) => (q.1, (1 - t) • q.1.1 + t • q.1.2 + q.2)) := by fun_prop
  exact (map_withDensity_comp hψ (hg.comp measurable_fst)).symm

/-- `eq:convolution`. -/
lemma bridgeLawD_map_snd_conv (ε t : ℝ) (π : Measure ((E d) × (E d))) [SFinite π] :
    (bridgeLawD ε t π).map Prod.snd =
      (π.map (fun z => (1 - t) • z.1 + t • z.2)) ∗ isoGauss d (ε * t * (1 - t)) := by
  unfold bridgeLawD
  rw [Measure.map_map measurable_snd (by fun_prop)]
  have h := Measure.map_prod_map π (isoGauss d (ε * t * (1 - t)))
    (f := fun z : (E d) × (E d) => (1 - t) • z.1 + t • z.2) (g := id) (by fun_prop) measurable_id
  rw [Measure.map_id] at h
  change _ = ((π.map (fun z : (E d) × (E d) => (1 - t) • z.1 + t • z.2)).prod
    (isoGauss d (ε * t * (1 - t)))).map (fun x => x.1 + x.2)
  rw [h, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- `eq:mixture`. -/
lemma bridgeLawD_map_snd_mix {ε t : ℝ} (hc : 0 ≤ ε * t * (1 - t)) (π : Measure ((E d) × (E d))) [SFinite π] :
    (bridgeLawD ε t π).map Prod.snd =
      (π.prod (stdGaussian (E d))).map (fun q => (1 - t) • q.1.1 + t • q.1.2 + √(ε * t * (1 - t)) • q.2) := by
  unfold bridgeLawD
  rw [isoGauss_eq, isoG_eq_map hc, Measure.map_map measurable_snd (by fun_prop)]
  have h := Measure.map_prod_map π (stdGaussian (E d)) (f := id)
    (g := fun z : E d => √(ε * t * (1 - t)) • z) measurable_id (by fun_prop)
  rw [Measure.map_id] at h
  rw [h, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Consequences of `IsBrownianRefD`. -/
lemma ref_factsD {ε : ℝ} (hε : 0 ≤ ε) {μ : Measure (E d)} [IsProbabilityMeasure μ] {X : ℝ → Ω → E d}
    {R : Measure Ω} (hR : IsBrownianRefD ε μ X R) :
    IsProbabilityMeasure R ∧ (∀ t ∈ Icc (0 : ℝ) 1,
      R.map (fun ω => ((X 0 ω, X 1 ω), X t ω)) = bridgeLawD ε t (refPlanD ε μ)) ∧
      R.map (fun ω => (X 0 ω, X 1 ω)) = refPlanD ε μ := by
  obtain ⟨hmeas, hlaw⟩ := hR
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hF : ∀ t ∈ Icc (0 : ℝ) 1, Measurable (fun ω => (X 0 ω, X t ω - X 0 ω, X 1 ω - X t ω)) := fun t ht =>
    (hmeas 0 h0).prodMk (((hmeas t ht).sub (hmeas 0 h0)).prodMk ((hmeas 1 h1).sub (hmeas t ht)))
  have hRp : IsProbabilityMeasure R := by
    have : IsProbabilityMeasure (R.map (fun ω => (X 0 ω, X 0 ω - X 0 ω, X 1 ω - X 0 ω))) := by
      rw [hlaw 0 h0]; unfold isoGauss; infer_instance
    exact Measure.isProbabilityMeasure_of_map (hF 0 h0).aemeasurable
  have h3 : ∀ t ∈ Icc (0 : ℝ) 1,
      R.map (fun ω => ((X 0 ω, X 1 ω), X t ω)) = bridgeLawD ε t (refPlanD ε μ) := by
    intro t ht
    have e : (fun ω => ((X 0 ω, X 1 ω), X t ω)) =
        (fun p : (E d) × (E d) × (E d) => ((p.1, p.1 + p.2.1 + p.2.2), p.1 + p.2.1)) ∘
          (fun ω => (X 0 ω, X t ω - X 0 ω, X 1 ω - X t ω)) := by
      funext ω
      simp only [Function.comp]
      refine Prod.ext (Prod.ext rfl ?_) ?_ <;> simp
    rw [e, ← Measure.map_map (by fun_prop) (hF t ht), hlaw t ht, isoGauss_eq, isoGauss_eq,
      brownian_threeD μ hε ht]
    rfl
  refine ⟨hRp, h3, ?_⟩
  have hY : (fun ω => (X 0 ω, X 1 ω)) = Prod.fst ∘ (fun ω => ((X 0 ω, X 1 ω), X 0 ω)) := rfl
  rw [hY, ← Measure.map_map measurable_fst ((hmeas 0 h0).prodMk (hmeas 1 h1) |>.prodMk (hmeas 0 h0)), h3 0 h0]
  unfold bridgeLawD
  rw [Measure.map_map measurable_fst (by fun_prop)]
  change (Measure.map Prod.fst ((refPlanD ε μ).prod _)) = _
  simp

variable {X : ℝ → Ω → E d} {μ ν : Measure (E d)}

lemma isCoupling_mapD {Q : Measure Ω} (h0 : Measurable (X 0)) (h1 : Measurable (X 1))
    (hQ0 : Q.map (X 0) = μ) (hQ1 : Q.map (X 1) = ν) : IsCoupling (Q.map (fun ω => (X 0 ω, X 1 ω))) μ ν := by
  constructor
  · change (Q.map _).map Prod.fst = μ
    rw [Measure.map_map measurable_fst (h0.prodMk h1)]; exact hQ0
  · change (Q.map _).map Prod.snd = ν
    rw [Measure.map_map measurable_snd (h0.prodMk h1)]; exact hQ1

lemma isProbabilityMeasure_of_couplingD {π : Measure ((E d) × (E d))} [IsProbabilityMeasure μ]
    (hπ : IsCoupling π μ ν) : IsProbabilityMeasure π := by
  have h : π.map Prod.fst = μ := hπ.fst_eq
  have : IsProbabilityMeasure (π.map Prod.fst) := by rw [h]; infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

lemma isPathCoupling_htransD {R : Measure Ω} [IsProbabilityMeasure R] [IsProbabilityMeasure μ]
    (h0 : Measurable (X 0)) (h1 : Measurable (X 1)) {π : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν)
    (hac : π ≪ R.map (fun ω => (X 0 ω, X 1 ω))) :
    IsPathCouplingD X μ ν (htrans R (fun ω => (X 0 ω, X 1 ω)) π) := by
  have hπp := isProbabilityMeasure_of_couplingD hπ
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

/-- The structure of a Schrödinger bridge in `ℝᵈ`. -/
lemma sb_structureD {ε : ℝ} (hε : 0 ≤ ε) [IsProbabilityMeasure μ] {R P : Measure Ω}
    (hR : IsBrownianRefD ε μ X R) (hP : IsSchrodingerBridgeD X R μ ν P) :
    IsStaticBridgeD ε μ ν (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
      klDiv P R = klDiv (P.map (fun ω => (X 0 ω, X 1 ω))) (refPlanD ε μ) ∧
      P = htrans R (fun ω => (X 0 ω, X 1 ω)) (P.map (fun ω => (X 0 ω, X 1 ω))) := by
  obtain ⟨hRp, -, hRY⟩ := ref_factsD hε hR
  have h0 : Measurable (X 0) := hR.1 0 ⟨le_rfl, zero_le_one⟩
  have h1 : Measurable (X 1) := hR.1 1 ⟨zero_le_one, le_rfl⟩
  have hY : Measurable (fun ω => (X 0 ω, X 1 ω)) := h0.prodMk h1
  obtain ⟨⟨hPp, hP0, hP1⟩, hPfin, hPmin⟩ := hP
  set Y := fun ω => (X 0 ω, X 1 ω)
  have hπc : IsCoupling (P.map Y) μ ν := isCoupling_mapD h0 h1 hP0 hP1
  have hdp : ∀ Q : Measure Ω, IsFiniteMeasure Q → klDiv (Q.map Y) (refPlanD ε μ) ≤ klDiv Q R := fun Q _ => by
    rw [← hRY]; exact klDiv_map_le Q R hY
  have hPR : P ≪ R := (klDiv_ne_top_iff.1 hPfin).1
  have hup : ∀ π' : Measure ((E d) × (E d)), IsCoupling π' μ ν → klDiv P R ≤ klDiv π' (refPlanD ε μ) := by
    intro π' hπ'
    by_cases hk : klDiv π' (refPlanD ε μ) = ∞
    · rw [hk]; exact le_top
    have hac' : π' ≪ R.map Y := by rw [hRY]; exact (klDiv_ne_top_iff.1 hk).1
    have := isProbabilityMeasure_of_couplingD hπ'
    calc klDiv P R ≤ klDiv (htrans R Y π') R := hPmin _ (isPathCoupling_htransD h0 h1 hπ' hac')
      _ = klDiv π' (R.map Y) := klDiv_htrans hY hac'
      _ = klDiv π' (refPlanD ε μ) := by rw [hRY]
  have heq : klDiv P R = klDiv (P.map Y) (refPlanD ε μ) := le_antisymm (hup _ hπc) (hdp P inferInstance)
  refine ⟨⟨hπc, ?_, fun π' hπ' => (hdp P inferInstance).trans (hup π' hπ')⟩, heq, ?_⟩
  · rw [← heq]; exact hPfin
  · exact eq_htrans_of_klDiv_le hY hPfin (by rw [hRY]; exact heq.le)

/-- The dynamic value is the static value (`ℝᵈ`). -/
lemma dyn_valueD {ε : ℝ} (hε : 0 ≤ ε) [IsProbabilityMeasure μ] {R : Measure Ω} (hR : IsBrownianRefD ε μ X R) :
    (⨅ (Q : Measure Ω) (_ : IsPathCouplingD X μ ν Q), klDiv Q R) = schroedingerValue (refPlanD ε μ) μ ν := by
  obtain ⟨hRp, -, hRY⟩ := ref_factsD hε hR
  have h0 : Measurable (X 0) := hR.1 0 ⟨le_rfl, zero_le_one⟩
  have h1 : Measurable (X 1) := hR.1 1 ⟨zero_le_one, le_rfl⟩
  have hY : Measurable (fun ω => (X 0 ω, X 1 ω)) := h0.prodMk h1
  apply le_antisymm
  · apply le_schroedingerValue
    intro π hπ
    by_cases hk : klDiv π (refPlanD ε μ) = ∞
    · rw [hk]; exact le_top
    have hac : π ≪ R.map (fun ω => (X 0 ω, X 1 ω)) := by rw [hRY]; exact (klDiv_ne_top_iff.1 hk).1
    have := isProbabilityMeasure_of_couplingD hπ
    calc (⨅ (Q : Measure Ω) (_ : IsPathCouplingD X μ ν Q), klDiv Q R)
        ≤ klDiv (htrans R (fun ω => (X 0 ω, X 1 ω)) π) R := iInf₂_le _ (isPathCoupling_htransD h0 h1 hπ hac)
      _ = klDiv π (refPlanD ε μ) := by rw [klDiv_htrans hY hac, hRY]
  · refine le_iInf₂ fun Q hQ => ?_
    obtain ⟨hQp, hQ0, hQ1⟩ := hQ
    refine (schroedingerValue_le_klDiv (isCoupling_mapD h0 h1 hQ0 hQ1) _).trans ?_
    rw [← hRY]; exact klDiv_map_le Q R hY

end Lemmas

theorem mixtureD_bridge : Claims.mixtureD_bridge := by
  intro Ω _ d ε μ ν X R P hε hμ hR hP
  obtain ⟨hRp, h3, hRY⟩ := ref_factsD hε.le hR
  obtain ⟨hstat, hkl, hP_eq⟩ := sb_structureD hε.le hR hP
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
  have hπg : π = (refPlanD ε μ).withDensity g := by
    rw [← hRY]; exact (Measure.withDensity_rnDeriv_eq _ _ hπac).symm
  have h3P : ∀ t ∈ Icc (0 : ℝ) 1, P.map (fun ω => (Y ω, X t ω)) = bridgeLawD ε t π := by
    intro t ht
    have hXt : Measurable (X t) := hR.1 t ht
    rw [hP_eq, htrans_map_pair hY hXt π]
    have e := h3 t ht
    change R.map (fun ω => (Y ω, X t ω)) = _ at e
    rw [e, bridgeLawD_withDensity ε t _ hg, ← hRY, Measure.withDensity_rnDeriv_eq _ _ hπac]
  refine ⟨hRY, hstat, hkl, ⟨g, hg, hπg, hP_eq⟩, fun t ht => ⟨h3P t ht, ?_, ?_⟩⟩
  · have hXt : Measurable (X t) := hR.1 t ht
    have hc : 0 ≤ ε * t * (1 - t) := mul_nonneg (mul_nonneg hε.le ht.1) (by linarith [ht.2])
    have e : X t = Prod.snd ∘ (fun ω => (Y ω, X t ω)) := rfl
    rw [e, ← Measure.map_map measurable_snd (hY.prodMk hXt), h3P t ht, bridgeLawD_map_snd_mix hc]
  · have hXt : Measurable (X t) := hR.1 t ht
    have e : X t = Prod.snd ∘ (fun ω => (Y ω, X t ω)) := rfl
    rw [e, ← Measure.map_map measurable_snd (hY.prodMk hXt), h3P t ht, bridgeLawD_map_snd_conv]

theorem mixtureD_exists : Claims.mixtureD_exists := by
  intro Ω _ d ε μ ν X R hε hμ hR
  obtain ⟨hRp, -, hRY⟩ := ref_factsD hε.le hR
  have h0 : Measurable (X 0) := hR.1 0 ⟨le_rfl, zero_le_one⟩
  have h1 : Measurable (X 1) := hR.1 1 ⟨zero_le_one, le_rfl⟩
  have hY : Measurable (fun ω => (X 0 ω, X 1 ω)) := h0.prodMk h1
  refine ⟨fun π hπ => ?_, fun P P' hP hP' he => ?_⟩
  · obtain ⟨hπc, hπfin, hπmin⟩ := hπ
    have hac : π ≪ R.map (fun ω => (X 0 ω, X 1 ω)) := by rw [hRY]; exact (klDiv_ne_top_iff.1 hπfin).1
    have := isProbabilityMeasure_of_couplingD hπc
    have hkl := klDiv_htrans hY hac
    rw [hRY] at hkl
    refine ⟨htrans R (fun ω => (X 0 ω, X 1 ω)) π, ⟨isPathCoupling_htransD h0 h1 hπc hac, ?_, fun Q hQ => ?_⟩,
      htrans_map hY hac⟩
    · rw [hkl]; exact hπfin
    · obtain ⟨hQp, hQ0, hQ1⟩ := hQ
      rw [hkl]
      refine (hπmin _ (isCoupling_mapD h0 h1 hQ0 hQ1)).trans ?_
      rw [← hRY]; exact klDiv_map_le Q R hY
  · rw [(sb_structureD hε.le hR hP).2.2, (sb_structureD hε.le hR hP').2.2, he]

lemma isStaticBridgeD_iff {d : ℕ} (ε : ℝ) (μ ν : Measure (E d)) (π : Measure ((E d) × (E d))) :
    IsStaticBridgeD ε μ ν π ↔ IsStaticMin (refPlanD ε μ) μ ν π := Iff.rfl

theorem equiv_static_d : Claims.equiv_static_d := by
  intro d ε μ ν _ hμ
  exact ⟨static_exists_iff, fun π π' h h' => static_unique h h'⟩

theorem equiv_bridge_d : Claims.equiv_bridge_d := by
  intro Ω _ d ε μ ν X R hε hμ hR
  have hval := dyn_valueD (ν := ν) hε.le hR
  have hPval : ∀ P : Measure Ω, IsSchrodingerBridgeD X R μ ν P →
      klDiv P R = schroedingerValue (refPlanD ε μ) μ ν :=
    fun P hP => hval ▸ le_antisymm (le_iInf₂ hP.2.2) (iInf₂_le P hP.1)
  refine ⟨hval, ⟨fun ⟨P, hP⟩ => hPval P hP ▸ hP.2.1, fun h => ?_⟩, fun P P' hP hP' => ?_, hPval⟩
  · obtain ⟨π, hπ⟩ := static_exists_iff.2 h
    obtain ⟨P, hP, -⟩ := (mixtureD_exists Ω d ε μ ν X R hε hμ hR).1 π hπ
    exact ⟨P, hP⟩
  · have s := (sb_structureD hε.le hR hP).1
    have s' := (sb_structureD hε.le hR hP').1
    exact (mixtureD_exists Ω d ε μ ν X R hε hμ hR).2 P P' hP hP' (static_unique s s')

/-! ### Non-vacuity of the reference hypothesis (route lemmas, not targets) -/

/-- The witness reference `μ ⊗ N(0, εI) ⊗ N(0, εI)` on `(ℝᵈ)³`. -/
def refMeasureD {d : ℕ} (ε : ℝ) (μ : Measure (E d)) : Measure ((E d) × (E d) × (E d)) :=
  μ.prod ((isoG d ε).prod (isoG d ε))

/-- ONE process `X_t(x, z₁, z₂) = x + t z₁ + √(t(1−t)) z₂` on `(ℝᵈ)³` carries an `ε`-Brownian reference started from
`μ` for every `ε ≥ 0` and every probability `μ` (only the three-time laws match). -/
theorem isBrownianRefD_witness {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (μ : Measure (E d)) [IsProbabilityMeasure μ] :
    IsBrownianRefD ε μ witnessD (refMeasureD ε μ) :=
  ⟨fun t _ => measurable_witnessD t, fun t ht => witnessD_law μ hε ht⟩

end StatFormal.Wave29t
