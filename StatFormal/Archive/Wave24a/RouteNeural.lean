import StatFormal.Archive.Wave24a.Statements
import StatFormal.Lib.OTLimits.Quadratic
import StatFormal.Archive.OTFD.Wave4.RouteWitness
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.WeakConvergence
import TauCeti.MeasureTheory.OptimalTransport.Brenier
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Route — C `lem:neural-law-to-map` (untrusted)

(a) Subgradient selections are optimal maps (Tau Ceti, Knott–Smith direction); `W₁ → 0` gives weak convergence
(continuity of `WassersteinSpace 1 → ProbabilityMeasure`), and on the common ball the second moments converge
(test function `min(‖y‖², R²)`); the library `OTLimits.tendsto_lintegral_brenierMap_sub_sq` (Villani Thm 5.20 +
Brenier uniqueness) concludes `∫ ‖T_n − Q‖² dμ → 0`.
(b) The certified `lem:neural-witness-ball` (Wave 4) with: a step modulus `ω` of `Q` on a compact thickening of `S`
(Heine–Cantor; `‖Q‖ ≤ R` bounds the large gaps), a positive mass bound for the witness balls (a finite cover of
`cthickening r S ⊆ O ⊆ supp μ` by balls of radius `r/8`), and monotonicity of subgradient selections.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction

namespace StatFormal.Wave24a

local notation "𝔼" K => EuclideanSpace ℝ (Fin K)

lemma memLp_two_of_lintegral' {K : ℕ} {ρ : Measure (𝔼 K)} (h : ∫⁻ x, ‖x‖ₑ ^ 2 ∂ρ ≠ ∞) : MemLp id 2 ρ := by
  have hlt : eLpNorm id 2 ρ < ∞ := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      aestronglyMeasurable_id]
    simpa [ENNReal.rpow_two] using h.lt_top
  exact hlt

lemma lintegral_map_bdd {K : ℕ} {μ : Measure (𝔼 K)} [IsProbabilityMeasure μ] {F : (𝔼 K) → 𝔼 K}
    (hF : Measurable F) {R : ℝ} (hR : ∀ u, ‖F u‖ ≤ R) (p : ℝ) (hp : 0 ≤ p) :
    ∫⁻ y, ‖y‖ₑ ^ p ∂(μ.map F) ≤ ENNReal.ofReal R ^ p := by
  rw [lintegral_map (by fun_prop) hF]
  calc ∫⁻ u, ‖F u‖ₑ ^ p ∂μ ≤ ∫⁻ _u, ENNReal.ofReal R ^ p ∂μ := by
        refine lintegral_mono fun u => ENNReal.rpow_le_rpow ?_ hp
        rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hR u)
    _ = ENNReal.ofReal R ^ p := by simp

lemma subdiff_monotone {K : ℕ} {φ : (𝔼 K) → EReal} {v w a b : 𝔼 K}
    (ha : a ∈ TauCeti.subdifferential (innerₗ (𝔼 K)) φ v) (hb : b ∈ TauCeti.subdifferential (innerₗ (𝔼 K)) φ w) :
    0 ≤ ⟪a - b, v - w⟫ := by
  obtain ⟨hv0, hv1, hva⟩ := ha
  obtain ⟨hw0, hw1, hwb⟩ := hb
  have h1 := hva w
  have h2 := hwb v
  lift φ v to ℝ using ⟨hv1, hv0⟩ with fv
  lift φ w to ℝ using ⟨hw1, hw0⟩ with fw
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h1 h2
  simp only [innerₗ_apply_apply] at h1 h2
  have e1 : ⟪w - v, a⟫ = -⟪a, v - w⟫ := by rw [← inner_neg_right, neg_sub, real_inner_comm]
  have e2 : ⟪v - w, b⟫ = ⟪b, v - w⟫ := real_inner_comm _ _
  rw [inner_sub_left]; linarith

theorem neural_law_to_map : Claims.neural_law_to_map := by
  intro K μ _ T Q φ ψ R hac hμ2 hTm hQm hTs hQs hTR hQR hW
  haveI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  let μP : ProbabilityMeasure (𝔼 K) := ⟨μ, inferInstance⟩
  let νs : ℕ → ProbabilityMeasure (𝔼 K) := fun n =>
    ⟨μ.map (T n), (Measure.isProbabilityMeasure_map_iff (hTm n).aemeasurable).2 inferInstance⟩
  let ν : ProbabilityMeasure (𝔼 K) := ⟨μ.map Q, (Measure.isProbabilityMeasure_map_iff hQm.aemeasurable).2 inferInstance⟩
  have hmom : ∀ {F : (𝔼 K) → 𝔼 K}, Measurable F → (∀ u, ‖F u‖ ≤ R) → (p : ℝ) → 0 ≤ p →
      ∫⁻ y, ‖y‖ₑ ^ p ∂(μ.map F) ≠ ∞ := fun hF hR p hp =>
    ((lintegral_map_bdd hF hR p hp).trans_lt (ENNReal.rpow_lt_top_of_nonneg hp ENNReal.ofReal_ne_top)).ne
  have hfin1 : ∀ {F : (𝔼 K) → 𝔼 K}, Measurable F → (∀ u, ‖F u‖ ≤ R) → HasFiniteMoment 1 (μ.map F) := by
    intro F hF hR
    haveI : IsProbabilityMeasure (μ.map F) := (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).2 inferInstance
    rw [hasFiniteMoment_iff_lintegral_edist_rpow_ne_top one_ne_zero ENNReal.one_ne_top 0]
    simpa [edist_zero_left, enorm_eq_nnnorm] using hmom hF hR 1 zero_le_one
  -- weak convergence
  have hw : Tendsto νs atTop (𝓝 ν) := by
    let ws : ℕ → WassersteinSpace 1 (𝔼 K) := fun n => WassersteinSpace.mk (νs n) (hfin1 (hTm n) (hTR n))
    let w : WassersteinSpace 1 (𝔼 K) := WassersteinSpace.mk ν (hfin1 hQm hQR)
    have hws : Tendsto ws atTop (𝓝 w) := by
      rw [tendsto_iff_edist_tendsto_0]
      convert hW using 1
      funext n
      exact WassersteinSpace.edist_def _ _
    exact (WassersteinSpace.continuous_toProbabilityMeasure.tendsto w).comp hws
  -- second moments converge
  set R' : ℝ≥0 := R.toNNReal with hR'
  let f : (𝔼 K) →ᵇ ℝ≥0 := BoundedContinuousFunction.mkOfBound
    ⟨fun y => min (‖y‖₊ ^ 2) (R' ^ 2), by fun_prop⟩ (R' ^ 2 : ℝ≥0) (fun x y => by
      simp only [ContinuousMap.coe_mk]
      rw [NNReal.dist_eq]
      have h3 : ((min (‖x‖₊ ^ 2) (R' ^ 2) : ℝ≥0) : ℝ) ≤ ((R' ^ 2 : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 (min_le_right _ _)
      have h4 : ((min (‖y‖₊ ^ 2) (R' ^ 2) : ℝ≥0) : ℝ) ≤ ((R' ^ 2 : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 (min_le_right _ _)
      have h5 := NNReal.coe_nonneg (min (‖x‖₊ ^ 2) (R' ^ 2))
      have h6 := NNReal.coe_nonneg (min (‖y‖₊ ^ 2) (R' ^ 2))
      rw [abs_le]; constructor <;> linarith)
  have hfeq : ∀ {F : (𝔼 K) → 𝔼 K}, Measurable F → (∀ u, ‖F u‖ ≤ R) →
      ∫⁻ y, (f y : ℝ≥0∞) ∂(μ.map F) = ∫⁻ y, ‖y‖ₑ ^ 2 ∂(μ.map F) := by
    intro F hF hR
    rw [lintegral_map (by fun_prop) hF, lintegral_map (by fun_prop) hF]
    refine lintegral_congr fun u => ?_
    have hle : ‖F u‖₊ ≤ R' := by
      rw [hR', ← NNReal.coe_le_coe, Real.coe_toNNReal _ ((norm_nonneg _).trans (hR u))]
      exact hR u
    have : min (‖F u‖₊ ^ 2) (R' ^ 2) = ‖F u‖₊ ^ 2 := min_eq_left (pow_le_pow_left₀ (by positivity) hle 2)
    simp only [f, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk, this]
    simp [enorm_eq_nnnorm]
  have hm : Tendsto (fun n => ∫⁻ y, ‖y‖ₑ ^ 2 ∂(νs n).toMeasure) atTop (𝓝 (∫⁻ y, ‖y‖ₑ ^ 2 ∂ν.toMeasure)) := by
    have h := (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.1 hw) f
    have e1 : ∀ n, ∫⁻ y, (f y : ℝ≥0∞) ∂(νs n : Measure (𝔼 K)) = ∫⁻ y, ‖y‖ₑ ^ 2 ∂(νs n).toMeasure :=
      fun n => hfeq (hTm n) (hTR n)
    have e2 : ∫⁻ y, (f y : ℝ≥0∞) ∂(ν : Measure (𝔼 K)) = ∫⁻ y, ‖y‖ₑ ^ 2 ∂ν.toMeasure := hfeq hQm hQR
    simp only [e1, e2] at h
    exact h
  have hsq : ∀ {F : (𝔼 K) → 𝔼 K}, Measurable F → (∀ u, ‖F u‖ ≤ R) → ∫⁻ y, ‖y‖ₑ ^ 2 ∂(μ.map F) ≠ ∞ := by
    intro F hF hR
    have := hmom hF hR 2 zero_le_two
    simpa [ENNReal.rpow_two] using this
  have hμL : MemLp id 2 μ := memLp_two_of_lintegral' hμ2.ne
  have hopt : ∀ {F : (𝔼 K) → 𝔼 K} {u : (𝔼 K) → EReal}, Measurable F → (∀ v, ‖F v‖ ≤ R) →
      (∀ᵐ v ∂μ, F v ∈ TauCeti.subdifferential (innerₗ (𝔼 K)) u v) →
      IsKantorovichOptimalTransportMap (StatFormal.OTLimits.quadCost (𝔼 K)) μ (μ.map F) F := by
    intro F u hF hR hsub
    haveI : IsProbabilityMeasure (μ.map F) := (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).2 inferInstance
    exact isKantorovichOptimalTransportMap_of_ae_mem_subdifferential hμL (memLp_two_of_lintegral' (hsq hF hR))
      (hasLaw_map hF.aemeasurable) hsub
  exact StatFormal.OTLimits.tendsto_lintegral_brenierMap_sub_sq (ρ := (volume : Measure (𝔼 K))) (μ := μP)
    (νs := νs) (ν := ν) hw hμ2.ne (fun n => hsq (hTm n) (hTR n)) (hsq hQm hQR) hm hac
    (fun n => hopt (hTm n) (hTR n) (hTs n)) (hopt hQm hQR hQs)

example : Claims.neural_law_to_map := neural_law_to_map

/-- A uniform positive mass bound for balls of radius `ρ/4` centred in a compact set inside the support. -/
lemma exists_mass_lb {K : ℕ} (μ : Measure (𝔼 K)) [IsFiniteMeasure μ] {C : Set (𝔼 K)} (hC : IsCompact C)
    (hCs : C ⊆ μ.support) (hne : C.Nonempty) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ m : ℝ, 0 < m ∧ ∀ c ∈ C, ENNReal.ofReal m ≤ μ (ball c (ρ / 4)) := by
  obtain ⟨t, htC, hcov⟩ := hC.elim_nhds_subcover (fun x => ball x (ρ / 8)) (fun x _ => ball_mem_nhds x (by positivity))
  have hpos : ∀ x ∈ t, 0 < μ (ball x (ρ / 8)) := fun x hx =>
    (Measure.mem_support_iff_forall x).1 (hCs (htC x hx)) _ (ball_mem_nhds x (by positivity))
  have htne : t.Nonempty := by
    obtain ⟨c, hc⟩ := hne
    obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.1 (hcov hc)
    exact ⟨x, hx⟩
  set m := t.inf' htne (fun x => (μ (ball x (ρ / 8))).toReal) with hm
  have hm0 : 0 < m := by
    rw [hm, Finset.lt_inf'_iff]
    intro x hx
    exact ENNReal.toReal_pos (hpos x hx).ne' (measure_ne_top _ _)
  refine ⟨m, hm0, fun c hc => ?_⟩
  obtain ⟨x, hx, hcx⟩ := Set.mem_iUnion₂.1 (hcov hc)
  have hsub : ball x (ρ / 8) ⊆ ball c (ρ / 4) := by
    intro y hy
    rw [mem_ball] at hy hcx ⊢
    have := dist_triangle y x c
    rw [dist_comm x c] at this
    linarith
  calc ENNReal.ofReal m ≤ ENNReal.ofReal (μ (ball x (ρ / 8))).toReal :=
        ENNReal.ofReal_le_ofReal (Finset.inf'_le _ hx)
    _ = μ (ball x (ρ / 8)) := ENNReal.ofReal_toReal (measure_ne_top _ _)
    _ ≤ μ (ball c (ρ / 4)) := measure_mono hsub

theorem neural_law_to_map_uniform : Claims.neural_law_to_map_uniform := by
  intro K μ _ T Q φ ψ R S O hac hμ2 hTm hQm hTs hQs hTR hQR hW hS hO hSO hOs hQc hTO
  have hL2 := neural_law_to_map K μ T Q φ ψ R hac hμ2 hTm hQm hTs hQs hTR hQR hW
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set ε0 := ε / 4 with hε0
  have hε0p : 0 < ε0 := by positivity
  obtain ⟨r0, hr0, hr0O⟩ := hS.exists_cthickening_subset_open hO hSO
  have hC0 : IsCompact (cthickening r0 S) := hS.cthickening
  have hU := hC0.uniformContinuousOn_of_continuous (hQc.mono hr0O)
  rw [Metric.uniformContinuousOn_iff] at hU
  obtain ⟨δ1, hδ1, hδU⟩ := hU ε0 hε0p
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hQR 0)
  set M := max (2 * R) ε0 with hM
  set r := min r0 δ1 / 2 with hr
  have hrpos : 0 < r := by positivity
  have h54 : 5 * r / 4 < min r0 δ1 := by rw [hr]; have := lt_min hr0 hδ1; linarith
  have hthick0 : cthickening (5 * r / 4) S ⊆ cthickening r0 S :=
    cthickening_mono (h54.le.trans (min_le_left _ _)) S
  set ω : ℝ → ℝ := fun t => if t < δ1 then ε0 else M with hω
  have hωmono : MonotoneOn ω (Ici 0) := by
    intro a _ b _ hab
    simp only [hω]
    split_ifs with h1 h2 <;> first | exact le_rfl | exact le_max_right _ _ | (exfalso; linarith)
  have hmod : ∀ x ∈ cthickening (5 * r / 4) S, ∀ y ∈ cthickening (5 * r / 4) S, ‖Q x - Q y‖ ≤ ω ‖x - y‖ := by
    intro x hx y hy
    simp only [hω]
    split_ifs with h
    · have := hδU x (hthick0 hx) y (hthick0 hy) (by rwa [dist_eq_norm])
      rw [dist_eq_norm] at this; exact this.le
    · calc ‖Q x - Q y‖ ≤ ‖Q x‖ + ‖Q y‖ := norm_sub_le _ _
        _ ≤ 2 * R := by linarith [hQR x, hQR y]
        _ ≤ M := le_max_left _ _
  have hω54 : ω (5 * r / 4) = ε0 := by
    simp only [hω]; rw [if_pos (h54.trans_le (min_le_right _ _))]
  -- witness-ball mass bound
  have hC1 : cthickening r S ⊆ μ.support :=
    (cthickening_mono (by linarith [h54, min_le_left r0 δ1]) S |>.trans hr0O).trans hOs
  obtain ⟨m, hm0, hmass⟩ := exists_mass_lb μ hS.cthickening hC1 (hne.mono (self_subset_cthickening S)) hrpos
  have hball : ∀ u ∈ S, ∀ e : EuclideanSpace ℝ (Fin K), ‖e‖ = 1 →
      ENNReal.ofReal m ≤ μ (ball (u + r • e) (r / 4)) := by
    intro u hu e he
    refine hmass _ ?_
    refine closedBall_subset_cthickening hu r ?_
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_pos hrpos]
  have hev := (ENNReal.tendsto_nhds_zero.1 hL2) (ENNReal.ofReal (m * ε0 ^ 2)) (by
    simp only [gt_iff_lt, ENNReal.ofReal_pos]; positivity)
  filter_upwards [hev] with n hn u hu
  set Rn := (∫⁻ v in O, ENNReal.ofReal (‖T n v - Q v‖ ^ 2) ∂μ).toReal with hRn
  have hint_le : (∫⁻ v in O, ENNReal.ofReal (‖T n v - Q v‖ ^ 2) ∂μ) ≤ ∫⁻ v, ‖T n v - Q v‖ₑ ^ 2 ∂μ := by
    refine (setLIntegral_le_lintegral _ _).trans (le_of_eq ?_)
    refine lintegral_congr fun v => ?_
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hfin : (∫⁻ v in O, ENNReal.ofReal (‖T n v - Q v‖ ^ 2) ∂μ) ≠ ⊤ :=
    (hint_le.trans hn).trans_lt ENNReal.ofReal_lt_top |>.ne
  have hRbound : (∫⁻ v in O, ENNReal.ofReal (‖T n v - Q v‖ ^ 2) ∂μ) ≤ ENNReal.ofReal Rn := by
    rw [hRn, ENNReal.ofReal_toReal hfin]
  have hRn_le : Rn ≤ m * ε0 ^ 2 := by
    rw [hRn]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hint_le.trans hn)
  have hmono : ∀ v ∈ O, ∀ w ∈ O, 0 ≤ ⟪T n v - T n w, v - w⟫ := fun v hv w hw =>
    subdiff_monotone (hTO n v hv) (hTO n w hw)
  have hwit := StatFormal.OTFD.Wave4.neural_witness_ball K μ S O (T n) Q ω r m Rn hS hO hSO hQc hmono hrpos
    (hthick0.trans hr0O) hωmono hmod hm0 hball hRbound u hu
  rw [hω54] at hwit
  have hsq : Real.sqrt (Rn / m) ≤ ε0 := by
    rw [Real.sqrt_le_left (by positivity)]
    rw [div_le_iff₀ hm0]; nlinarith
  rw [dist_eq_norm, norm_sub_rev]
  calc ‖T n u - Q u‖ ≤ 5 / 3 * (ε0 + Real.sqrt (Rn / m)) := hwit
    _ ≤ 5 / 3 * (ε0 + ε0) := by gcongr
    _ < ε := by rw [hε0]; linarith

example : Claims.neural_law_to_map_uniform := neural_law_to_map_uniform

end StatFormal.Wave24a
