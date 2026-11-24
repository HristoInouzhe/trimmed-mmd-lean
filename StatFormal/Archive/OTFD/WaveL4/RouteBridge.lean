import StatFormal.Archive.OTFD.WaveL4.Statements
import StatFormal.Archive.Wave15b.RouteDuality

/-!
# Route (wave L4): C `eq:weighted-hard-gap` gives the plan form of the inexact fit

Untrusted route file. For atomic laws `μ_{K,m} = Σ_j β_j δ_{u_j}` (grid in the compact `U`) and
`P̂ = Σ_i w_i δ_{Z_i}`, with the Laguerre potential `χ = max_{i∈I} ℓ_i` (`I = {w_i > 0}`) and
`X = (χ + ι_U)^*`:
* `χ` is convex (a finite maximum of affine functions) and Lipschitz, `X` is Lipschitz;
* the Fenchel–Young defect `d(u, z) = χ(u) − ⟨u, z⟩ + X(z)` is continuous, and
  `χ(u) + ⟨z, v − u⟩ ≤ χ(v) + d(u, z)` for all `v ∈ U` (definition of `X`);
* for an optimal (cost-minimising) plan `p` of the atomic problem, `d(u_j, Z_i) ≤ χ(u_j) − ℓ_i(u_j)`
  on the atoms charged by `p` (`X(Z_i) ≤ (‖Z_i‖² − f_i)/2`), and
  `Σ p_{ji} (χ(u_j) − ℓ_i(u_j)) = ½ (W₂² − ∫φ⁰ dμ_{K,m} − Σ w_i f_i) ≤ ζ/2`
  (the sandwich of `lem:weighted-duality`, here against the optimal plan).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL4

open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.Wave15b
open StatFormal.RobustEquality.Paper2.Alternating (Plans)

variable {K m n : ℕ}

/-- Laguerre potentials are convex. -/
theorem convexOn_chiI {I : Finset (Fin n)} (hI : I.Nonempty) (Z : Fin n → Euc K) (f : Fin n → ℝ) :
    ConvexOn ℝ univ (chiI I Z f) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨k, hk, hkeq⟩ := du_chi_attained hI Z f (a • x + b • y)
  rw [hkeq]
  have e : ellAff Z f k (a • x + b • y) = a * ellAff Z f k x + b * ellAff Z f k y := by
    unfold ellAff
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    linear_combination ((‖Z k‖ ^ 2 - f k) / 2) * hab
  rw [e, smul_eq_mul, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (du_ell_le Z f hk x) ha)
    (mul_le_mul_of_nonneg_left (du_ell_le Z f hk y) hb)

theorem continuous_of_le_add_mul {E : Type*} [NormedAddCommGroup E] {S : E → ℝ} {L : ℝ}
    (h : ∀ x y, S x ≤ S y + L * ‖x - y‖) : Continuous S :=
  (LipschitzWith.of_le_add_mul' L fun x y => by simpa [dist_eq_norm] using h x y).continuous

theorem continuous_chiI {I : Finset (Fin n)} (hI : I.Nonempty) (Z : Fin n → Euc K) (f : Fin n → ℝ) :
    Continuous (chiI I Z f) := by
  refine continuous_of_le_add_mul (L := ∑ i, ‖Z i‖) fun x y => ?_
  have : Nonempty I := ⟨⟨hI.choose, hI.choose_spec⟩⟩
  refine ciSup_le fun i => ?_
  have h1 := du_ell_le Z f i.2 y
  have h2 : ellAff Z f i x = ellAff Z f i y + ⟪x - y, Z i⟫ := by
    unfold ellAff; rw [inner_sub_left]; ring
  have h3 : ⟪x - y, Z i⟫ ≤ ‖Z i‖ * ‖x - y‖ := by
    rw [mul_comm]; exact real_inner_le_norm _ _
  have h4 : ‖Z i‖ ≤ ∑ i, ‖Z i‖ :=
    Finset.single_le_sum (f := fun i => ‖Z i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
  have h5 : ‖Z i‖ * ‖x - y‖ ≤ (∑ i, ‖Z i‖) * ‖x - y‖ := mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
  linarith

theorem continuous_conjU {U : Set (Euc K)} (hU : Bornology.IsBounded U) (hne : U.Nonempty)
    {I : Finset (Fin n)} (hI : I.Nonempty) (Z : Fin n → Euc K) (f : Fin n → ℝ) :
    Continuous (conjU U (chiI I Z f)) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hU
  refine continuous_of_le_add_mul (L := R) fun z z' => ?_
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨v, hv, rfl⟩
  have h1 := du_le_conjU hU hI Z f hv z'
  have h2 : ⟪v, z⟫ = ⟪v, z'⟫ + ⟪v, z - z'⟫ := by rw [inner_sub_right]; ring
  have h3 : ⟪v, z - z'⟫ ≤ R * ‖z - z'‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hR v hv) (norm_nonneg _))
  simp only
  linarith

/-- Existence of an optimal plan of the atomic problem. -/
theorem exists_optimal_plan {β : Fin m → ℝ} {w : Fin n → ℝ} (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (ug : Fin m → Euc K)
    (Z : Fin n → Euc K) : ∃ p ∈ Plans β w, costSum ug Z p = w2sq β ug w Z := by
  have hne : (Plans β w).Nonempty := ⟨_, du_prod_plan hβ0 hβ1 hw0 hw1⟩
  have hclosed : IsClosed (Plans β w) := by
    have e : Plans β w = (⋂ j, ⋂ i, {p : Fin m → Fin n → ℝ | 0 ≤ p j i}) ∩
        ((⋂ j, {p : Fin m → Fin n → ℝ | ∑ i, p j i = β j}) ∩
          ⋂ i, {p : Fin m → Fin n → ℝ | ∑ j, p j i = w i}) := by
      ext p; simp [Plans]
    rw [e]
    refine (isClosed_iInter fun j => isClosed_iInter fun i => ?_).inter
      ((isClosed_iInter fun j => ?_).inter (isClosed_iInter fun i => ?_))
    · exact isClosed_le continuous_const ((continuous_apply i).comp (continuous_apply j))
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => (continuous_apply i).comp (continuous_apply j))
        continuous_const
    · exact isClosed_eq (continuous_finsetSum _ fun j _ => (continuous_apply i).comp (continuous_apply j))
        continuous_const
  have hbdd : Bornology.IsBounded (Plans β w) := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun p hp => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hp.1 j i)]
    have h1 : p j i ≤ ∑ i, p j i :=
      Finset.single_le_sum (f := fun i => p j i) (fun i _ => hp.1 j i) (Finset.mem_univ _)
    have h2 : β j ≤ ∑ j, β j :=
      Finset.single_le_sum (f := β) (fun j _ => hβ0 j) (Finset.mem_univ _)
    rw [hp.2.1 j] at h1
    linarith
  have hcont : Continuous (costSum ug Z) := by
    unfold costSum; fun_prop
  obtain ⟨p, hp, hmin⟩ := (Metric.isCompact_of_isClosed_isBounded hclosed hbdd).exists_isMinOn hne
    hcont.continuousOn
  refine ⟨p, hp, ?_⟩
  unfold w2sq
  have hl : IsLeast (costSum ug Z '' Plans β w) (costSum ug Z p) :=
    ⟨⟨p, hp, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; exact hmin hq⟩
  exact hl.csInf_eq.symm

/-- The atomic plan measure `Σ_{j,i} p_{ji} δ_{(u_j, Z_i)}`. -/
def planMeas (p : Fin m → Fin n → ℝ) (ug : Fin m → Euc K) (Z : Fin n → Euc K) :
    Measure (Euc K × Euc K) :=
  ∑ j, ∑ i, ENNReal.ofReal (p j i) • Measure.dirac (ug j, Z i)

theorem planMeas_apply (p : Fin m → Fin n → ℝ) (ug : Fin m → Euc K) (Z : Fin n → Euc K)
    {s : Set (Euc K × Euc K)} (hs : MeasurableSet s) :
    planMeas p ug Z s = ∑ j, ∑ i, ENNReal.ofReal (p j i) * s.indicator 1 (ug j, Z i) := by
  simp only [planMeas, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs]

theorem planMeas_fst {β : Fin m → ℝ} {w : Fin n → ℝ} {p : Fin m → Fin n → ℝ} (hp : p ∈ Plans β w)
    (ug : Fin m → Euc K) (Z : Fin n → Euc K) :
    (planMeas p ug Z).fst = ∑ j, ENNReal.ofReal (β j) • Measure.dirac (ug j) := by
  ext s hs
  rw [Measure.fst_apply hs, planMeas_apply p ug Z (measurable_fst hs)]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hind : ∀ i, (Prod.fst ⁻¹' s).indicator (1 : Euc K × Euc K → ℝ≥0∞) (ug j, Z i) =
      s.indicator 1 (ug j) := fun i => by
    by_cases h : ug j ∈ s <;> simp [h]
  simp only [hind, ← Finset.sum_mul]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hp.1 j i, hp.2.1 j]

theorem planMeas_snd {β : Fin m → ℝ} {w : Fin n → ℝ} {p : Fin m → Fin n → ℝ} (hp : p ∈ Plans β w)
    (ug : Fin m → Euc K) (Z : Fin n → Euc K) :
    (planMeas p ug Z).snd = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (Z i) := by
  ext s hs
  rw [Measure.snd_apply hs, planMeas_apply p ug Z (measurable_snd hs)]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hind : ∀ j, (Prod.snd ⁻¹' s).indicator (1 : Euc K × Euc K → ℝ≥0∞) (ug j, Z i) =
      s.indicator 1 (Z i) := fun j => by
    by_cases h : Z i ∈ s <;> simp [h]
  simp only [hind, ← Finset.sum_mul]
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => hp.1 j i, hp.2.2 i]

theorem planMeas_prob {β : Fin m → ℝ} {w : Fin n → ℝ} {p : Fin m → Fin n → ℝ} (hp : p ∈ Plans β w)
    (hβ1 : ∑ j, β j = 1) (ug : Fin m → Euc K) (Z : Fin n → Euc K) :
    IsProbabilityMeasure (planMeas p ug Z) := by
  constructor
  rw [planMeas_apply p ug Z MeasurableSet.univ]
  simp only [indicator_univ, Pi.one_apply, mul_one]
  rw [Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_sum_of_nonneg fun i _ => hp.1 j i).symm]
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => Finset.sum_nonneg fun i _ => hp.1 j i]
  simp only [hp.2.1, hβ1, ENNReal.ofReal_one]

theorem lintegral_planMeas (p : Fin m → Fin n → ℝ) (ug : Fin m → Euc K) (Z : Fin n → Euc K)
    (g : Euc K × Euc K → ℝ≥0∞) :
    ∫⁻ z, g z ∂planMeas p ug Z = ∑ j, ∑ i, ENNReal.ofReal (p j i) * g (ug j, Z i) := by
  simp only [planMeas, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul]

theorem weighted_gap_plan_form : Claims.weighted_gap_plan_form := by
  intro K m n β ug w Z f U ζ hβ0 hβ1 hw0 hw1 hUc hug hgap
  have hI := du_posRows_nonempty hw0 hw1
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hβ1
    · exact h
  have hUne : U.Nonempty := ⟨ug ⟨0, hm⟩, hug _⟩
  have hU := hUc.isBounded
  set I := posRows w
  set χ := chiI I Z f with hχ
  set X := conjU U χ with hX
  refine ⟨convexOn_chiI hI Z f, ?_⟩
  obtain ⟨p, hp, hpcost⟩ := exists_optimal_plan hβ0 hβ1 hw0 hw1 ug Z
  have := planMeas_prob hp hβ1 ug Z
  set d : Euc K × Euc K → ℝ := fun z => χ z.1 - ⟪z.1, z.2⟫ + X z.2 with hd
  have hdc : Continuous d :=
    (((continuous_chiI hI Z f).comp continuous_fst).sub (continuous_fst.inner continuous_snd)).add
      ((continuous_conjU hU hUne hI Z f).comp continuous_snd)
  refine ⟨⟨planMeas p ug Z, this⟩, d, planMeas_fst hp ug Z, planMeas_snd hp ug Z, hdc.measurable,
    ?_, ?_⟩
  · change ∫⁻ z, ENNReal.ofReal (d z) ∂planMeas p ug Z ≤ _
    rw [lintegral_planMeas]
    set t : Fin m → Fin n → ℝ := fun j i => χ (ug j) - ⟪ug j, Z i⟫ + (‖Z i‖ ^ 2 - f i) / 2 with ht
    -- the columns outside `I` carry no mass
    have hpI : ∀ j i, 0 < p j i → i ∈ I := fun j i hpos => by
      refine du_mem_posRows.2 ?_
      have : p j i ≤ ∑ j, p j i :=
        Finset.single_le_sum (f := fun j => p j i) (fun j _ => hp.1 j i) (Finset.mem_univ _)
      rw [hp.2.2 i] at this
      linarith
    have hterm : ∀ j i, ENNReal.ofReal (p j i) * ENNReal.ofReal (d (ug j, Z i)) ≤
        ENNReal.ofReal (p j i * t j i) := fun j i => by
      rcases (hp.1 j i).lt_or_eq with hpos | hzero
      · rw [← ENNReal.ofReal_mul (hp.1 j i)]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (hp.1 j i))
        have := du_conjU_data hUne Z f (hpI j i hpos)
        simp only [hd, ht]
        linarith
      · rw [← hzero]; simp
    have htnn : ∀ j i, 0 ≤ p j i * t j i := fun j i => by
      rcases (hp.1 j i).lt_or_eq with hpos | hzero
      · refine mul_nonneg (hp.1 j i) ?_
        have := du_ell_le Z f (hpI j i hpos) (ug j)
        unfold ellAff at this
        simp only [ht]
        linarith
      · rw [← hzero]; simp
    have hsum : ∑ j, ∑ i, p j i * t j i ≤ ζ / 2 := by
      have e1 : ∀ j i, p j i * t j i =
          (p j i * ‖ug j - Z i‖ ^ 2 - p j i * phiHard I Z f (ug j) - p j i * f i) / 2 := fun j i => by
        simp only [ht, phiHard, ← hχ]
        rw [norm_sub_sq_real]
        ring
      simp only [e1, ← Finset.sum_div, Finset.sum_sub_distrib]
      have h1 : ∑ j, ∑ i, p j i * ‖ug j - Z i‖ ^ 2 = w2sq β ug w Z := hpcost
      have h2 : ∑ j, ∑ i, p j i * phiHard I Z f (ug j) = ∑ j, β j * phiHard I Z f (ug j) :=
        Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul, hp.2.1 j]
      have h3 : ∑ j, ∑ i, p j i * f i = ∑ i, w i * f i := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul, hp.2.2 i]
      rw [h1, h2, h3]
      linarith
    calc ∑ j, ∑ i, ENNReal.ofReal (p j i) * ENNReal.ofReal (d (ug j, Z i))
        ≤ ∑ j, ∑ i, ENNReal.ofReal (p j i * t j i) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hterm j i
      _ = ENNReal.ofReal (∑ j, ∑ i, p j i * t j i) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun j _ => Finset.sum_nonneg fun i _ => htnn j i]
          exact Finset.sum_congr rfl fun j _ =>
            (ENNReal.ofReal_sum_of_nonneg fun i _ => htnn j i).symm
      _ ≤ ENNReal.ofReal (ζ / 2) := ENNReal.ofReal_le_ofReal hsum
  · intro z x hx
    have := du_le_conjU hU hI Z f hx z.2
    have e1 : ⟪z.2, x⟫ = ⟪x, z.2⟫ := real_inner_comm _ _
    have e2 : ⟪z.2, z.1⟫ = ⟪z.1, z.2⟫ := real_inner_comm _ _
    simp only [hd]
    rw [inner_sub_right]
    linarith

end StatFormal.OTFD.WaveL4
