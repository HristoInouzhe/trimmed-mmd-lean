import StatFormal.Archive.Wave25b.RouteGHS
import StatFormal.Archive.OTFD.WaveL8.Proofs

/-!
# Route (wave 25b): A `thm:app-ghs-stability` — the claims (untrusted)

The hypotheses of the theorem give `GHSCore`: `γ_n ⇀ (Id × 𝔽)#P` by the frozen `plan_stab_a_uncond` (`P ∈ 𝒫^ℓ`, so
`m₁(P) < ∞`; `Q` bounded; `𝔽` a `P`-a.e. subgradient selection of `ψ`, hence cyclically monotone; `γ_n` carried by its
support, a closed subset of the cyclically monotone graph of `∂ψ_n`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave25b

open StatFormal.OTFD.WaveL1 (CycMon CMConc IsCMMapAE Graph LipNull Mom2 Euc)
open StatFormal.OTFD.WaveL3 (Mom1)
open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Wave22a (IsSubgrad)

section Glue
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem ghsCore_of {Pn Qn : ℕ → ProbabilityMeasure H} {P Q : ProbabilityMeasure H}
    {γ : ℕ → ProbabilityMeasure (H × H)} {D : ℕ → Set H} {ψn : ℕ → H → ℝ} {ψ : H → ℝ} {F : H → H}
    {M L : ℝ} {N₀ : ℕ} {K₀ : Set H}
    (hPn : Tendsto Pn atTop (𝓝 P)) (hLip : LipNull (P : Measure H)) (hQn : Tendsto Qn atTop (𝓝 Q))
    (hQnM : ∀ n, (Qn n : Measure H) (Metric.closedBall 0 M)ᶜ = 0) (hQM : (Q : Measure H) (Metric.closedBall 0 M)ᶜ = 0)
    (hfst : ∀ n, (γ n : Measure (H × H)).fst = Pn n) (hsnd : ∀ n, (γ n : Measure (H × H)).snd = Qn n)
    (hsupp : ∀ n, (γ n : Measure (H × H)).support ⊆ {p | IsSubgradOn (D n) (ψn n) p.1 p.2})
    (hψ : ConvexOn ℝ univ ψ) (hL : ∀ x x', |ψ x - ψ x'| ≤ L * ‖x - x'‖)
    (hF : Measurable F) (hmap : (P : Measure H).map F = Q) (hFs : ∀ᵐ x ∂(P : Measure H), IsSubgrad ψ x (F x))
    (hK : IsCompact K₀) (hKs : K₀ ⊆ interior (P : Measure H).support)
    (hd : ∀ x ∈ K₀, ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v)
    (hbd : ∀ n, N₀ ≤ n → ∀ x ∈ K₀, ∀ y, IsSubgradOn (D n) (ψn n) x y → ‖y‖ ≤ M) :
    GHSCore P F γ D ψn ψ M L N₀ K₀ := by
  have hcm : IsCMMapAE (P : Measure H) F := StatFormal.OTFD.WaveL6.isCMMapAE_of_ae_subgrad hFs
  have hγΓ : ∀ n, ∀ᵐ p ∂(γ n : Measure (H × H)), IsSubgradOn (D n) (ψn n) p.1 p.2 := fun n =>
    Filter.mem_of_superset Measure.support_mem_ae (hsupp n)
  have hcmγ : ∀ n, CMConc (γ n : Measure (H × H)) := by
    intro n
    refine ⟨(γ n : Measure (H × H)).support, Measure.isClosed_support.measurableSet, ?_,
      Measure.measure_compl_support⟩
    intro m z hz
    exact cycMon_subgradOn (D n) (ψn n) m z fun i => hsupp n (hz i)
  have hgm : Measurable fun x => (x, F x) := measurable_id.prodMk hF
  have hlim : Tendsto γ atTop (𝓝 (P.map fun x => (x, F x))) :=
    StatFormal.OTFD.WaveL1.plan_stab_a H P Q F M Pn Qn γ (P.map fun x => (x, F x)) hLip hQM hF
      (StatFormal.OTFD.WaveL8.brenier_uniq_H H P Q F hLip hF hmap hcm) hPn hQn hfst hsnd hcmγ rfl
  have hγM : ∀ n, ∀ᵐ p ∂(γ n : Measure (H × H)), ‖p.2‖ ≤ M := by
    intro n
    have h0 : ∀ᵐ y ∂(Qn n : Measure H), ‖y‖ ≤ M := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hQnM n)] with y hy
      simpa using hy
    rw [← hsnd n] at h0
    exact ae_of_ae_map measurable_snd.aemeasurable h0
  exact ⟨hF, hγΓ, hγM, hlim, hFs, hL, hψ, hK, hKs, hd, hbd⟩

end Glue

theorem app_ghs_stability_weak : Claims.app_ghs_stability_weak := by
  intro H _ _ _ _ _ _ Pn Qn P Q γ D ψn ψ F M L N₀ K₀ h hPn hLip hQn hQnM hQM hfst hsnd hsupp hψ hL hF hmap
    hFs hK hKs hd hbd ε hε
  exact (ghsCore_of hPn hLip hQn hQnM hQM hfst hsnd hsupp hψ hL hF hmap hFs hK hKs hd hbd).eventually_abs_inner_le
    h hε

theorem app_ghs_stability_norm : Claims.app_ghs_stability_norm := by
  intro H _ _ _ _ _ _ Pn Qn P Q γ D ψn ψ F M L N₀ K₀ C hPn hLip hQn hQnM hQM hfst hsnd hsupp hψ hL hF hmap
    hFs hK hKs hd hbd hC hrange hFC ε hε
  exact (ghsCore_of hPn hLip hQn hQnM hQM hfst hsnd hsupp hψ hL hF hmap hFs hK hKs hd hbd).eventually_norm_le
    hC (fun n _ => hrange n) hFC hε

theorem app_ghs_stability_fd : Claims.app_ghs_stability_fd := by
  intro H _ _ _ _ _ Pn Qn P Q γ D ψn ψ F M L N₀ K₀ hPn hLip hQn hQnM hQM hfst hsnd hsupp hψ hL hF hmap
    hFs hK hKs hd hbd ε hε
  have hc := ghsCore_of hPn hLip hQn hQnM hQM hfst hsnd hsupp hψ hL hF hmap hFs hK hKs hd hbd
  refine hc.eventually_norm_le (C := Metric.closedBall 0 (max M (max L 0))) (isCompact_closedBall _ _)
    (fun n hn x hx y hy => ?_) (fun x hx => ?_) hε
  · exact mem_closedBall_zero_iff.2 ((hbd n hn x hx y hy).trans (le_max_left _ _))
  · exact mem_closedBall_zero_iff.2 ((StatFormal.ConvexH.norm_le_of_subgrad hL
      (StatFormal.ConvexH.subgrad_of_hasLineDerivAt hψ (hd x hx))).trans (le_max_right _ _))

end StatFormal.Wave25b
