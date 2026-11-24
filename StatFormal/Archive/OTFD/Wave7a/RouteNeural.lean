import StatFormal.Archive.OTFD.Wave7a.Statements
import StatFormal.Archive.OTFD.Wave4.RouteWitness
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Route: C `thm:neural-band-consistency`

* Ess sup = sup: under `supp(μ|_A) = A` (hypothesis, `lem:full-support-region`(i)) a continuous function has
  `μ|_A-ess sup = sup_A` (a point beating the ess sup gives an open set of positive mass above it).
* Transfer: `|sup_A⟨v,T⟩ − sup_A⟨v,Q⟩| ≤ ‖v‖ sup_S‖T − Q‖` for `A ⊆ S` (Cauchy–Schwarz, termwise).
* Uniform core: the certified `lem:neural-witness-ball` with a step modulus (uniform continuity of `Q` on a
  compact thickening of `S`) and the ball-mass floor `m` from a finite cover by balls of radius `r/8` centred in
  `O` (positive mass by full support), so `sup_S‖T − Q‖ ≤ ε` once `𝓡 ≤ m(3ε/10)²`.
* Rate: the witness ball with `ω(h) = Lh`, `m = ρ|B₁|(r/4)^K`, `r = (𝓡/L²)^{1/(K+2)}`.
-/

noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave7a

variable {K : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin K)

/-! ### EReal bookkeeping -/

lemma eclose_up (mo c : ℝ) {x y : EReal} (h1 : x ≤ y + c) (h2 : y ≤ x + c) :
    EClose ((mo : EReal) + x) ((mo : EReal) + y) c := by
  constructor
  · rw [add_assoc]; exact add_le_add_right h1 _
  · rw [add_assoc]; exact add_le_add_right h2 _

lemma eclose_lo (mo c : ℝ) {x y : EReal} (h1 : x ≤ y + c) (h2 : y ≤ x + c) :
    EClose ((mo : EReal) - x) ((mo : EReal) - y) c := by
  unfold EClose
  induction x using EReal.rec <;> induction y using EReal.rec
  · simp
  · simp at h2
  · simp at h2
  · simp at h1
  · rename_i a b
    norm_cast at h1 h2 ⊢
    constructor <;> linarith
  · simp at h2
  · simp at h1
  · rename_i a
    exfalso
    have : (⊤ : EReal) ≤ ((a + c : ℝ) : EReal) := by exact_mod_cast h1
    exact absurd this (not_le.2 (EReal.coe_lt_top _))
  · simp

lemma eclose_mono {x y : EReal} {c d : ℝ} (h : EClose x y c) (hcd : c ≤ d) : EClose x y d := by
  have : (c : EReal) ≤ d := by exact_mod_cast hcd
  exact ⟨h.1.trans (add_le_add_right this _), h.2.trans (add_le_add_right this _)⟩

/-! ### ess sup = sup -/

lemma popSup_eq_nnSup {μ : Measure 𝔼} {Q : 𝔼 → 𝔼} {A : Set 𝔼} (hA : MeasurableSet A)
    (hQ : ContinuousOn Q A) (hsupp : ∀ N, IsOpen N → (N ∩ A).Nonempty → 0 < μ (A ∩ N)) (v : 𝔼) :
    popSup μ Q A v = nnSup Q A v := by
  set g : 𝔼 → ℝ := fun u => ⟪v, Q u⟫_ℝ
  have hg : ContinuousOn g A := continuousOn_const.inner hQ
  unfold popSup nnSup
  apply le_antisymm
  · refine essSup_le_of_ae_le _ ((ae_restrict_mem hA).mono fun u hu => ?_)
    exact le_iSup₂ (f := fun u (_ : u ∈ A) => ((⟪v, Q u⟫_ℝ : ℝ) : EReal)) u hu
  · refine iSup₂_le fun u hu => ?_
    by_contra hlt
    push_neg at hlt
    obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have hc2' : c < g u := by exact_mod_cast hc2
    obtain ⟨N, hNo, huN, hN⟩ : ∃ N, IsOpen N ∧ u ∈ N ∧ ∀ w ∈ N ∩ A, c < g w := by
      have h := (hg u hu).eventually (lt_mem_nhds hc2')
      rw [eventually_nhdsWithin_iff, _root_.eventually_nhds_iff] at h
      obtain ⟨N, hN, hNo, huN⟩ := h
      exact ⟨N, hNo, huN, fun w hw => hN w hw.1 hw.2⟩
    have hpos := hsupp N hNo ⟨u, huN, hu⟩
    have hae := ae_le_essSup (μ := μ.restrict A) (f := fun w => ((g w : ℝ) : EReal))
    rw [ae_iff] at hae
    have hsub : N ∩ A ⊆ {w | ¬ ((g w : ℝ) : EReal) ≤ essSup (fun w => ((g w : ℝ) : EReal)) (μ.restrict A)} := by
      intro w hw
      simp only [mem_setOf_eq, not_le]
      exact hc1.trans (by exact_mod_cast hN w hw)
    have h0 := measure_mono_null hsub hae
    rw [Measure.restrict_apply (hNo.measurableSet.inter hA), inter_assoc, inter_self, inter_comm] at h0
    exact (ne_of_gt hpos) h0

/-! ### transfer -/

lemma nnSup_transfer {T Q : 𝔼 → 𝔼} {A : Set 𝔼} {η E : ℝ} (hη : 0 ≤ η)
    (hS : ∀ u ∈ A, ‖T u - Q u‖ ≤ η) {v : 𝔼} (hv : ‖v‖ ≤ E) :
    nnSup T A v ≤ nnSup Q A v + ((E * η : ℝ) : EReal) ∧
      nnSup Q A v ≤ nnSup T A v + ((E * η : ℝ) : EReal) := by
  have hE : 0 ≤ E := (norm_nonneg v).trans hv
  have key : ∀ u ∈ A, |⟪v, T u⟫_ℝ - ⟪v, Q u⟫_ℝ| ≤ E * η := by
    intro u hu
    rw [← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hv (hS u hu) (norm_nonneg _) hE)
  constructor
  · refine iSup₂_le fun u hu => ?_
    have h := (abs_le.1 (key u hu)).2
    calc ((⟪v, T u⟫_ℝ : ℝ) : EReal) ≤ ((⟪v, Q u⟫_ℝ + E * η : ℝ) : EReal) := by
          exact_mod_cast (by linarith)
      _ = ((⟪v, Q u⟫_ℝ : ℝ) : EReal) + ((E * η : ℝ) : EReal) := EReal.coe_add _ _
      _ ≤ _ := add_le_add_left
          (le_iSup₂ (f := fun u (_ : u ∈ A) => ((⟪v, Q u⟫_ℝ : ℝ) : EReal)) u hu) _
  · refine iSup₂_le fun u hu => ?_
    have h := (abs_le.1 (key u hu)).1
    calc ((⟪v, Q u⟫_ℝ : ℝ) : EReal) ≤ ((⟪v, T u⟫_ℝ + E * η : ℝ) : EReal) := by
          exact_mod_cast (by linarith)
      _ = ((⟪v, T u⟫_ℝ : ℝ) : EReal) + ((E * η : ℝ) : EReal) := EReal.coe_add _ _
      _ ≤ _ := add_le_add_left
          (le_iSup₂ (f := fun u (_ : u ∈ A) => ((⟪v, T u⟫_ℝ : ℝ) : EReal)) u hu) _

/-- From a sup-error bound on `S` to `BandsClose`. -/
lemma bands_of_sup {𝒯 : Type} {μ : Measure 𝔼} {O : Set 𝔼} {Q T : 𝔼 → 𝔼} {A : ℝ → Set 𝔼} {δ : ℝ}
    {mo : 𝒯 → ℝ} {e : 𝒯 → 𝔼} {E η : ℝ} (hset : NeuralSetting μ O Q A δ e E)
    (hsupp : ∀ p, 0 < p → p ≤ 1 - δ → ∀ N, IsOpen N → (N ∩ A p).Nonempty → 0 < μ (A p ∩ N))
    (hη : 0 ≤ η) (hS : ∀ u ∈ A (1 - δ), ‖T u - Q u‖ ≤ η) : BandsClose μ T Q A δ mo e (E * η) := by
  obtain ⟨_, _, _, hSO, hQc, _, hreg, he⟩ := hset
  intro p hp0 hp1 t
  obtain ⟨hAS, hAm⟩ := hreg p hp0 hp1
  have hQA : ContinuousOn Q (A p) := hQc.mono (hAS.trans hSO)
  have hSA : ∀ u ∈ A p, ‖T u - Q u‖ ≤ η := fun u hu => hS u (hAS hu)
  have h1 := nnSup_transfer hη hSA (he t)
  have h2 := nnSup_transfer hη hSA (v := -e t) (E := E) (by rw [norm_neg]; exact he t)
  unfold edgeUpE edgeLoE
  rw [popSup_eq_nnSup hAm hQA (hsupp p hp0 hp1), popSup_eq_nnSup hAm hQA (hsupp p hp0 hp1)]
  exact ⟨eclose_up _ _ h1.1 h1.2, eclose_lo _ _ h2.1 h2.2⟩

/-! ### the uniform core -/

lemma unif_core {μ : Measure 𝔼} [IsFiniteMeasure μ] {S O : Set 𝔼} {Q : 𝔼 → 𝔼} (hS : IsCompact S)
    (hO : IsOpen O) (hSO : S ⊆ O) (hQc : ContinuousOn Q O) (hpos : ∀ x ∈ O, ∀ r, 0 < r → 0 < μ (ball x r))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η, 0 < η ∧ ∀ T : 𝔼 → 𝔼, MonoOn T O → risk μ O T Q ≤ ENNReal.ofReal η →
      ∀ u ∈ S, ‖T u - Q u‖ ≤ ε := by
  obtain ⟨r0, hr0, hr0O⟩ := hS.exists_cthickening_subset_open hO hSO
  set C0 := cthickening r0 S
  have hC0 : IsCompact C0 := hS.cthickening
  have hQC0 : ContinuousOn Q C0 := hQc.mono hr0O
  set ε'' := 3 * ε / 10
  have hε'' : 0 < ε'' := by positivity
  obtain ⟨h0, hh0, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (hC0.uniformContinuousOn_of_continuous hQC0) ε'' hε''
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 (hC0.image_of_continuousOn hQC0).isBounded
  set ω : ℝ → ℝ := fun h => if h < h0 then ε'' else max D ε''
  have hωmono : MonotoneOn ω (Ici 0) := by
    intro a _ b _ hab
    simp only [ω]
    split_ifs with ha hb hb
    · exact le_rfl
    · exact le_max_right _ _
    · exact absurd (lt_of_le_of_lt hab hb) ha
    · exact le_rfl
  set r := 4 / 5 * min r0 (h0 / 2)
  have hr : 0 < r := by positivity
  have h5r : 5 * r / 4 = min r0 (h0 / 2) := by simp only [r]; ring
  have hthick : cthickening (5 * r / 4) S ⊆ C0 := cthickening_mono (by rw [h5r]; exact min_le_left _ _) S
  have hmod : ∀ x ∈ cthickening (5 * r / 4) S, ∀ y ∈ cthickening (5 * r / 4) S,
      ‖Q x - Q y‖ ≤ ω ‖x - y‖ := by
    intro x hx y hy
    simp only [ω]
    split_ifs with hxy
    · rw [← dist_eq_norm] at hxy ⊢; exact (hunif x (hthick hx) y (hthick hy) hxy).le
    · rw [← dist_eq_norm]
      exact (hD ⟨x, hthick hx, rfl⟩ ⟨y, hthick hy, rfl⟩).trans (le_max_left _ _)
  have hω5 : ω (5 * r / 4) = ε'' := by
    simp only [ω]; rw [if_pos (by rw [h5r]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith))]
  -- ball-mass floor
  set C1 := cthickening r S
  have hC1 : IsCompact C1 := hS.cthickening
  have hC1O : C1 ⊆ O := (cthickening_mono (by
    calc r = 4 / 5 * min r0 (h0 / 2) := rfl
      _ ≤ min r0 (h0 / 2) := by have := le_min hr0.le (by linarith : 0 ≤ h0 / 2); nlinarith
      _ ≤ r0 := min_le_left _ _) S).trans hr0O
  obtain ⟨t, htC1, htfin, hcover⟩ := finite_cover_balls_of_compact hC1 (by positivity : 0 < r / 8)
  obtain ⟨m, hm, hmball⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ t, ENNReal.ofReal m ≤ μ (ball x (r / 8)) := by
    by_cases hne : t.Nonempty
    · obtain ⟨x0, hx0, hmin⟩ := Set.exists_min_image t (fun x => (μ (ball x (r / 8))).toReal) htfin hne
      refine ⟨(μ (ball x0 (r / 8))).toReal, ENNReal.toReal_pos (hpos x0 (hC1O (htC1 hx0)) _
        (by positivity)).ne' (measure_ne_top _ _), fun x hx => ?_⟩
      calc ENNReal.ofReal (μ (ball x0 (r / 8))).toReal ≤ ENNReal.ofReal (μ (ball x (r / 8))).toReal :=
            ENNReal.ofReal_le_ofReal (hmin x hx)
        _ = μ (ball x (r / 8)) := ENNReal.ofReal_toReal (measure_ne_top _ _)
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  have hballm : ∀ u ∈ S, ∀ e : 𝔼, ‖e‖ = 1 → ENNReal.ofReal m ≤ μ (ball (u + r • e) (r / 4)) := by
    intro u hu e he
    have hw : u + r • e ∈ C1 := mem_cthickening_of_dist_le _ u r S hu (by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_of_nonneg hr.le])
    obtain ⟨x, hxt, hwx⟩ := mem_iUnion₂.1 (hcover hw)
    refine (hmball x hxt).trans (measure_mono fun z hz => ?_)
    rw [mem_ball] at hz hwx ⊢
    calc dist z (u + r • e) ≤ dist z x + dist x (u + r • e) := dist_triangle _ _ _
      _ < r / 8 + r / 8 := by rw [dist_comm x]; exact add_lt_add hz hwx
      _ = r / 4 := by ring
  refine ⟨m * ε'' ^ 2, by positivity, fun T hT hR u hu => ?_⟩
  have hw := Wave4.neural_witness_ball K μ S O T Q ω r m (m * ε'' ^ 2) hS hO hSO hQc hT hr
    (hthick.trans hr0O) hωmono hmod hm hballm hR u hu
  rw [hω5, mul_div_cancel_left₀ _ hm.ne', Real.sqrt_sq hε''.le] at hw
  calc ‖T u - Q u‖ ≤ 5 / 3 * (ε'' + ε'') := hw
    _ = ε := by simp only [ε'']; ring

theorem neural_band_uniform : Claims.neural_band_uniform := by
  intro K 𝒯 μ O Q A δ mo e E hset hsupp ε hε
  have hset' := hset
  obtain ⟨hprob, hS, hO, hSO, hQc, hpos, _, _⟩ := hset
  haveI := hprob
  set E' := max E 0
  have hE' : 0 < E' + 1 := by positivity
  obtain ⟨η, hη, hcore⟩ := unif_core hS hO hSO hQc hpos (div_pos hε hE')
  refine ⟨η, hη, fun T hT hR => ?_⟩
  have hb := bands_of_sup (mo := mo) hset' hsupp (div_pos hε hE').le (hcore T hT hR)
  refine fun p hp0 hp1 t => ?_
  obtain ⟨h1, h2⟩ := hb p hp0 hp1 t
  have hle : E * (ε / (E' + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hE']
    nlinarith [le_max_left E 0, le_max_right E 0]
  exact ⟨eclose_mono h1 hle, eclose_mono h2 hle⟩

theorem neural_band_ae : Claims.neural_band_ae := by
  intro K 𝒯 μ O Q A δ mo e E Ω _ P T hset hsupp hmono hlim
  filter_upwards [hlim] with ω hω
  intro ε hε
  obtain ⟨η, hη, hgood⟩ := neural_band_uniform K 𝒯 μ O Q A δ mo e E hset hsupp ε hε
  have hev := (tendsto_order.1 hω).2 _ (ENNReal.ofReal_pos.2 hη)
  filter_upwards [hev] with n hn
  exact hgood _ (hmono n ω) hn.le

theorem neural_band_prob : Claims.neural_band_prob := by
  intro K 𝒯 μ O Q A δ mo e E Ω _ P T hset hsupp hmono hlim ε hε δ' hδ'
  obtain ⟨η, hη, hgood⟩ := neural_band_uniform K 𝒯 μ O Q A δ mo e E hset hsupp ε hε
  filter_upwards [hlim η hη δ' hδ'] with n ⟨G, hG, hGsub, hPG⟩
  exact ⟨G, hG, fun ω hω => hgood _ (hmono n ω) (hGsub hω), hPG⟩

/-! ### the rate -/

lemma Lr_eq {L R : ℝ} (hL : 0 < L) (hR : 0 < R) (K : ℕ) :
    L * (R / L ^ 2) ^ ((1 : ℝ) / (K + 2)) = L ^ ((K : ℝ) / (K + 2)) * R ^ ((1 : ℝ) / (K + 2)) := by
  have hK : (0 : ℝ) < K + 2 := by positivity
  rw [Real.div_rpow hR.le (by positivity), ← Real.rpow_natCast L 2, ← Real.rpow_mul hL.le]
  have e : (K : ℝ) / (K + 2) = 1 - (2 : ℕ) * (1 / (K + 2)) := by field_simp; ring
  rw [e, Real.rpow_sub hL, Real.rpow_one]
  field_simp

theorem neural_band_rate : Claims.neural_band_rate := by
  intro K ρ hK hρ
  have : Nontrivial (EuclideanSpace ℝ (Fin K)) := by
    have : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin K)) := by rw [finrank_euclideanSpace_fin]; exact hK
    exact Module.nontrivial_of_finrank_pos this
  set V := (volume (ball (0 : (EuclideanSpace ℝ (Fin K))) 1)).toReal
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume (0 : (EuclideanSpace ℝ (Fin K))) one_pos).ne'
    measure_ball_lt_top.ne
  set c0 := (4 : ℝ) ^ K / (ρ * V)
  have hc0 : 0 < c0 := by positivity
  refine ⟨5 / 3 * (5 / 4 + Real.sqrt c0), by positivity, ?_⟩
  intro 𝒯 μ O O' Q A δ mo e E L hset hsupp hO' hSO' hO'O hdens hL hLip
  have hset' := hset
  obtain ⟨hprob, hS, hO, hSO, hQc, hpos, hreg, he⟩ := hset
  set S := A (1 - δ)
  obtain ⟨r1', hr1', hthick1⟩ := hS.exists_cthickening_subset_open hO' hSO'
  set r1 := 4 / 5 * r1'
  have hr1 : 0 < r1 := by positivity
  refine ⟨L ^ 2 * r1 ^ (K + 2), by positivity, fun R hR0 hRle T hT hrisk => ?_⟩
  set r := (R / L ^ 2) ^ ((1 : ℝ) / (K + 2))
  have hr : 0 < r := Real.rpow_pos_of_pos (div_pos hR0 (by positivity)) _
  have hrpow : r ^ (K + 2) = R / L ^ 2 := by
    have h := Real.rpow_inv_natCast_pow (x := R / L ^ 2) (n := K + 2) (by positivity) (by omega)
    have e : ((K + 2 : ℕ) : ℝ)⁻¹ = (1 : ℝ) / (K + 2) := by push_cast; ring
    rw [e] at h
    exact h
  have hrle : r ≤ r1 := by
    have h1 : r ^ (K + 2) ≤ r1 ^ (K + 2) := by
      rw [hrpow, div_le_iff₀ (by positivity)]; linarith
    exact (pow_le_pow_iff_left₀ hr.le hr1.le (by omega)).1 h1
  have h5 : 5 * r / 4 ≤ r1' := by simp only [r1] at hrle; linarith
  have hthick : cthickening (5 * r / 4) S ⊆ O' := (cthickening_mono h5 S).trans hthick1
  set ω : ℝ → ℝ := fun h => L * h
  have hωmono : MonotoneOn ω (Ici 0) := fun a _ b _ hab => mul_le_mul_of_nonneg_left hab hL.le
  have hmod : ∀ x ∈ cthickening (5 * r / 4) S, ∀ y ∈ cthickening (5 * r / 4) S,
      ‖Q x - Q y‖ ≤ ω ‖x - y‖ := fun x hx y hy => hLip x (hthick hx) y (hthick hy)
  set m := ρ * V * (r / 4) ^ K
  have hm : 0 < m := by positivity
  have hballm : ∀ u ∈ S, ∀ e : (EuclideanSpace ℝ (Fin K)), ‖e‖ = 1 → ENNReal.ofReal m ≤ μ (ball (u + r • e) (r / 4)) := by
    intro u hu e he1
    have hsub : ball (u + r • e) (r / 4) ⊆ O' := by
      intro z hz
      refine hthick (mem_cthickening_of_dist_le z u _ S hu ?_)
      have h1 : dist (u + r • e) u = r := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he1, mul_one, Real.norm_of_nonneg hr.le]
      have h2 := dist_triangle z (u + r • e) u
      rw [mem_ball] at hz
      linarith
    refine le_trans (le_of_eq ?_) (hdens _ measurableSet_ball hsub)
    rw [Measure.addHaar_ball _ _ (by positivity : (0 : ℝ) ≤ r / 4), finrank_euclideanSpace_fin,
      ← ENNReal.ofReal_toReal (measure_ball_lt_top (μ := volume) (x := (0 : (EuclideanSpace ℝ (Fin K)))) (r := 1)).ne]
    simp only [m]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    ring
  have hw := Wave4.neural_witness_ball K μ S O T Q ω r m R hS hO hSO hQc hT hr
    (hthick.trans hO'O) hωmono hmod hm hballm hrisk
  have hRm : R / m = c0 * (L * r) ^ 2 := by
    have hR : R = L ^ 2 * r ^ (K + 2) := by rw [hrpow]; field_simp
    simp only [m, c0]
    rw [hR, div_pow, pow_add]
    field_simp
  have hsq : Real.sqrt (R / m) = Real.sqrt c0 * (L * r) := by
    rw [hRm, Real.sqrt_mul hc0.le, Real.sqrt_sq (by positivity)]
  have hsup : ∀ u ∈ S, ‖T u - Q u‖ ≤
      5 / 3 * (5 / 4 + Real.sqrt c0) * L ^ ((K : ℝ) / (K + 2)) * R ^ ((1 : ℝ) / (K + 2)) := by
    intro u hu
    have h := hw u hu
    simp only [ω] at h
    rw [hsq] at h
    calc ‖T u - Q u‖ ≤ 5 / 3 * (L * (5 * r / 4) + Real.sqrt c0 * (L * r)) := h
      _ = 5 / 3 * (5 / 4 + Real.sqrt c0) * (L * r) := by ring
      _ = _ := by rw [Lr_eq hL hR0 K]; ring
  have hb := bands_of_sup (mo := mo) hset' hsupp (by positivity) hsup
  convert hb using 1
  ring

end StatFormal.OTFD.Wave7a
