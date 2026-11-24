import StatFormal.Archive.Wave30h.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward

/-!
# Route — `lem:transfer` and `lem:compose` (untrusted)

* `transfer_coupling`: for every coupling `π` of `(η, γ)` and `K`-Lipschitz `k`,
  `‖k‖_{L²(η)} ≤ ‖k‖_{L²(γ)} + K ‖edist‖_{L²(π)}` (Minkowski on `π`); `transfer_lip` takes the infimum over couplings
  (no optimal coupling needed; `K = 0` through the product coupling).
* `compose_perturbed`: induction on the chain length, `e_{k+1} ≤ ε + K e_k`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal

namespace StatFormal.Wave30h

open StatFormal.OTFD.WaveL1 (Euc)

section Transfer
variable {X Y : Type*} [MeasurableSpace X] [PseudoEMetricSpace X] [NormedAddCommGroup Y] [MeasurableSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y]

lemma transfer_coupling {η γ : Measure X} {π : Measure (X × X)} (hπ : IsCoupling π η γ) {K : ℝ≥0} {k : X → Y}
    (hk : LipschitzWith K k) (hd : Measurable fun z : X × X => edist z.1 z.2) [OpensMeasurableSpace X] :
    eLpNorm k 2 η ≤ eLpNorm k 2 γ + K * eLpNorm (fun z : X × X => edist z.1 z.2) 2 π := by
  have hkm : Measurable k := hk.continuous.measurable
  have h1 : eLpNorm k 2 η = eLpNorm (fun z : X × X => k z.1) 2 π := by
    rw [← hπ.fst_eq, Measure.fst, eLpNorm_map_measure hkm.aestronglyMeasurable measurable_fst.aemeasurable]
    rfl
  have h2 : eLpNorm k 2 γ = eLpNorm (fun z : X × X => k z.2) 2 π := by
    rw [← hπ.snd_eq, Measure.snd, eLpNorm_map_measure hkm.aestronglyMeasurable measurable_snd.aemeasurable]
    rfl
  rw [h1, h2]
  have hsplit : (fun z : X × X => k z.1) = (fun z => k z.2) + fun z => k z.1 - k z.2 := by
    funext z; simp
  rw [hsplit]
  refine (eLpNorm_add_le (μ := π) (p := 2) (f := fun z : X × X => k z.2) (g := fun z => k z.1 - k z.2)
    (by norm_num)).trans ?_
  gcongr
  refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (f := fun z : X × X => k z.1 - k z.2)
    (g := fun z : X × X => edist z.1 z.2) (c := K) ?_ (.of_forall fun z => ?_) 2).trans_eq ?_
  · exact ((hkm.comp measurable_fst).sub (hkm.comp measurable_snd)).aestronglyMeasurable
  · simp only [enorm_eq_self]
    rw [← edist_eq_enorm_sub]
    exact hk.edist_le_mul _ _
  · simp [ENNReal.smul_def]

lemma transfer_general [OpensMeasurableSpace X] (hd : Measurable fun z : X × X => edist z.1 z.2)
    (η γ : Measure X) [IsProbabilityMeasure η] [IsProbabilityMeasure γ] {K : ℝ≥0} {k : X → Y}
    (hk : LipschitzWith K k) :
    eLpNorm k 2 η ≤ eLpNorm k 2 γ + K * wassersteinEDist 2 η γ := by
  by_cases hK : K = 0
  · have := transfer_coupling (isCoupling_prod η γ) hk hd
    simpa [hK] using this
  · rw [wassersteinEDist, ENNReal.mul_iInf_of_ne (by simpa using hK) ENNReal.coe_ne_top, ENNReal.add_iInf]
    refine le_iInf fun π => ?_
    rw [ENNReal.mul_iInf_of_ne (by simpa using hK) ENNReal.coe_ne_top, ENNReal.add_iInf]
    exact le_iInf fun hπ => transfer_coupling hπ hk hd

end Transfer

theorem transfer_lip : Claims.transfer_lip := by
  intro d m η γ _ _ K k hk
  exact transfer_general measurable_edist η γ hk

/-! ### `lem:compose` -/

lemma chain_succ {X : Type*} (f : ℕ → X → X) (k : ℕ) (x : X) : chain f (k + 1) x = f k (chain f k x) := rfl

theorem compose_perturbed : Claims.compose_perturbed := by
  intro X _ m f fh A K ε x x' hL hε hx hx'
  have key : ∀ k ≤ m, dist (chain fh k x') (chain f k x) ≤
      (K : ℝ) ^ k * dist x' x + ε * ∑ j ∈ Finset.range k, (K : ℝ) ^ j := by
    intro k
    induction k with
    | zero => intro _; simp [chain]
    | succ k ih =>
      intro hk
      have hkm : k < m := hk
      have ih' := ih hkm.le
      rw [chain_succ, chain_succ]
      have h1 : dist (fh k (chain fh k x')) (f k (chain fh k x')) ≤ ε := hε k hkm _ (hx' k hkm)
      have h2 : dist (f k (chain fh k x')) (f k (chain f k x)) ≤ K * dist (chain fh k x') (chain f k x) :=
        (hL k hkm).dist_le_mul _ (hx' k hkm) _ (hx k hkm)
      calc dist (fh k (chain fh k x')) (f k (chain f k x))
          ≤ dist (fh k (chain fh k x')) (f k (chain fh k x')) +
              dist (f k (chain fh k x')) (f k (chain f k x)) := dist_triangle _ _ _
        _ ≤ ε + K * ((K : ℝ) ^ k * dist x' x + ε * ∑ j ∈ Finset.range k, (K : ℝ) ^ j) := by
            gcongr
            exact h2.trans (mul_le_mul_of_nonneg_left ih' K.2)
        _ = (K : ℝ) ^ (k + 1) * dist x' x + ε * ∑ j ∈ Finset.range (k + 1), (K : ℝ) ^ j := by
            have hs : ∑ j ∈ Finset.range (k + 1), (K : ℝ) ^ j = 1 + K * ∑ j ∈ Finset.range k, (K : ℝ) ^ j := by
              rw [Finset.sum_range_succ', Finset.mul_sum]
              simp only [pow_succ, pow_zero]
              rw [add_comm]
              congr 1
              exact Finset.sum_congr rfl fun j _ => by ring
            rw [hs]
            ring
  exact key m le_rfl

end StatFormal.Wave30h
