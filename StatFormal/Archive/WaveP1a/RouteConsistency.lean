import StatFormal.Archive.WaveP1a.Statements
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs

/-!
# Wave P1a — TM `thm:consistency` (ii) at `α* = TV(P,Q)`, unconditionally

Untrusted proof route. The abstract `D` of the certified `TrimmedMMD.consistency_ii` is instantiated at
`Dpop φ P Q`: `D(TV) = 0` (`zero_of_tv_le`), `D > 0` below `TV` (`zeroeq`), `D` nonincreasing (the trimming
regions increase with `α`, proved here); the concentration events are the certified `Unconditional.events`. The
probabilistic conclusion of `consistency_ii` is applied on a one-point space to extract the pathwise inclusion.
-/

open MeasureTheory Set

namespace StatFormal.WaveP1a

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

section
variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem region_mono {φ : 𝒳 → H} {P : Measure 𝒳} {α β : ℝ} (hβ1 : β < 1) (hαβ : α ≤ β) :
    region φ α P ⊆ region φ β P := by
  rintro z ⟨g, hg, hb, hi, rfl⟩
  refine ⟨g, hg, fun x => ⟨(hb x).1, (hb x).2.trans ?_⟩, hi, rfl⟩
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem setDist_nonneg' (A B : Set H) : 0 ≤ setDist A B :=
  Real.sInf_nonneg (by rintro _ ⟨a, -, b, -, rfl⟩; exact norm_nonneg _)

theorem setDist_anti {A B A' B' : Set H} (hA : A.Nonempty) (hB : B.Nonempty) (hAA : A ⊆ A')
    (hBB : B ⊆ B') : setDist A' B' ≤ setDist A B := by
  obtain ⟨a, ha⟩ := hA; obtain ⟨b, hb⟩ := hB
  refine csInf_le_csInf ⟨0, ?_⟩ ⟨_, a, ha, b, hb, rfl⟩ ?_
  · rintro _ ⟨a, -, b, -, rfl⟩; exact norm_nonneg _
  · rintro _ ⟨a, ha, b, hb, rfl⟩; exact ⟨a, hAA ha, b, hBB hb, rfl⟩

theorem Dpop_antitoneOn (φ : 𝒳 → H) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    AntitoneOn (Dpop φ P Q) (Ico 0 1) := by
  intro α hα β hβ hαβ
  exact setDist_anti (region_nonempty P hα.1 hα.2) (region_nonempty Q hα.1 hα.2)
    (region_mono hβ.2 hαβ) (region_mono hβ.2 hαβ)

end

theorem consistency_ii_tv : Claims.consistency_ii_tv := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ hφ hκ hchar hκ0 hδ0 hδ1 htv0 htv1 ε hε
  have h0 := StatFormal.Distances.tvDist_nonneg P Q
  have hD0 : Dpop φ P Q (StatFormal.Distances.tvDist P Q) = 0 :=
    StatFormal.TrimmedMMD.ZeroSet.zero_of_tv_le 𝒳 H P Q φ κ _ hφ hκ h0 htv1 le_rfl
  have hpos : ∀ α ∈ Ico (0 : ℝ) (StatFormal.Distances.tvDist P Q), 0 < Dpop φ P Q α := by
    intro α hα
    refine lt_of_le_of_ne (setDist_nonneg' _ _) (fun h => ?_)
    have := (StatFormal.TrimmedMMD.ZeroSet.zeroeq 𝒳 H P Q φ κ α hφ hκ hchar hα.1
      (by linarith [hα.2])).1 h.symm
    linarith [hα.2]
  obtain ⟨N, hN⟩ := StatFormal.TrimmedMMD.consistency_ii (Dpop φ P Q) κ δ _ hκ0 hδ0 hδ1
    ⟨htv0, htv1⟩ hD0 (Dpop_antitoneOn φ P Q) hpos ε hε
  refine ⟨N, fun n m hn hm hn1 hm1 => ?_⟩
  obtain ⟨AP, AQ, hAP, hAQ, hPEP, hPEQ, hev⟩ :=
    StatFormal.TrimmedMMD.Unconditional.events 𝒳 H P Q φ κ δ n m hφ hκ hκ0 hδ0 hδ1 hn1 hm1
  refine ⟨Prod.fst ⁻¹' AP ∩ Prod.snd ⁻¹' AQ, (measurable_fst hAP).inter (measurable_snd hAQ),
    StatFormal.TrimmedMMD.event_prob _ _ δ _ _ hδ0 hδ1 (measurable_fst hAP) (measurable_snd hAQ)
      hPEP hPEQ, ?_⟩
  intro z hz
  have hone : ENNReal.ofReal (1 - δ / 2) ≤ (Measure.dirac () : Measure Unit) univ := by
    rw [measure_univ]; exact ENNReal.ofReal_le_one.2 (by linarith)
  have key := hN n m hn hm hn1 hm1 Unit (Measure.dirac ()) (fun _ => Demp φ z.1 z.2) univ univ
    MeasurableSet.univ MeasurableSet.univ hone hone (fun _ _ α hα => hev z hz α hα)
  by_contra hnot
  have hempty : {ω : Unit | StatFormal.TrimmedMMD.alphaHat ((fun _ => Demp φ z.1 z.2) ω)
      (fun α => StatFormal.TrimmedMMD.tau κ α δ n m) ∈
        Icc (StatFormal.Distances.tvDist P Q - ε) (StatFormal.Distances.tvDist P Q)} = ∅ := by
    ext ω; simpa using hnot
  rw [hempty, measure_empty] at key
  have : (0 : ENNReal) < ENNReal.ofReal (1 - δ) := ENNReal.ofReal_pos.2 (by linarith)
  exact absurd key (not_le.2 this)

end StatFormal.WaveP1a
