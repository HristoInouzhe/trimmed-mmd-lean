import StatFormal.Archive.OTFD.Wave16b.Statements
import StatFormal.Archive.OTFD.Wave7a.RouteNeural

/-!
# Route: C `cor:net-inner-band-neural` and the deterministic part of `prop:net-inner-band` (untrusted)

* Step 1 of `prop:net-inner-band`: on the compact `Ā = closure A_{K,p} ⊆ S`, a maximiser `u₀` of `⟨v, Q⟩` is pushed
  along the ray `u₀ + t w` (`w = v`, or any unit vector if `v = 0`) to the last point `u₁` of `Ā`, which lies on
  `∂Ā ⊆ ∂A_{K,p}`; monotonicity of `Q` on `O` gives `⟨v, Q(u₁)⟩ ≥ ⟨v, Q(u₀)⟩`.
* Step 3 (ii): a net point `u_h` within `h` of `u₁` gives `⟨v, T(u_h)⟩ ≥ ⟨v, Q(u₁)⟩ − ‖v‖(w + η)`; the essential sup is
  below the sup over `Ā`.
* (iv): under the support condition the essential sup is the sup (Wave 7a `popSup_eq_nnSup`), and the net sup is below
  the sup of `T` over `A`, within `‖v‖η` of that of `Q` (`nnSup_transfer`).
* Asymptotics: uniform continuity of `Q` on `S` and the uniform witness-ball core (Wave 7a `unif_core`). Rate: the
  witness-ball rate of the proof of `neural_band_rate`, restated as `rate_sup`, and `ω_S(h) ≤ Lh`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave16b

open StatFormal.OTFD.Wave7a (NeuralSetting nnSup popSup edgeUpE edgeLoE EClose risk MonoOn eclose_up eclose_lo
  eclose_mono popSup_eq_nnSup nnSup_transfer unif_core Lr_eq)

variable {K : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin K)

/-! ### Step 1: a maximiser on the frontier -/

lemma exists_frontier_max (hK : 0 < K) {O B : Set 𝔼} {Q : 𝔼 → 𝔼} (hB : IsCompact B) (hBne : B.Nonempty)
    (hBO : B ⊆ O) (hQc : ContinuousOn Q B) (hmono : MonoOn Q O) (v : 𝔼) :
    ∃ u ∈ B, u ∈ frontier B ∧ ∀ y ∈ B, ⟪v, Q y⟫_ℝ ≤ ⟪v, Q u⟫_ℝ := by
  have hcont : ContinuousOn (fun y => ⟪v, Q y⟫_ℝ) B := continuousOn_const.inner hQc
  obtain ⟨u₀, hu₀B, hu₀max⟩ := hB.exists_isMaxOn hBne hcont
  -- a nonzero direction
  set e : 𝔼 := EuclideanSpace.single (⟨0, hK⟩ : Fin K) 1 with he
  have hene : e ≠ 0 := by
    intro h0
    have := congrArg (fun z : 𝔼 => z ⟨0, hK⟩) h0
    simp [he] at this
  set w : 𝔼 := if v = 0 then e else v with hw
  have hw0 : w ≠ 0 := by simp only [hw]; split_ifs with h; exacts [hene, h]
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  set Tset : Set ℝ := {t | 0 ≤ t ∧ u₀ + t • w ∈ B} with hT
  have hTcl : IsClosed Tset := isClosed_Ici.inter (hB.isClosed.preimage (continuous_const.add (continuous_id.smul continuous_const)))
  obtain ⟨R, hR⟩ := hB.isBounded.subset_closedBall 0
  have hTsub : Tset ⊆ Icc 0 ((R + ‖u₀‖) / ‖w‖) := by
    rintro t ⟨ht0, htB⟩
    refine ⟨ht0, ?_⟩
    rw [le_div_iff₀ hwn]
    have h1 : ‖u₀ + t • w‖ ≤ R := by simpa using hR htB
    have h2 : ‖t • w‖ ≤ ‖u₀ + t • w‖ + ‖u₀‖ := by
      calc ‖t • w‖ = ‖(u₀ + t • w) - u₀‖ := by rw [add_sub_cancel_left]
        _ ≤ _ := norm_sub_le _ _
    rw [norm_smul, Real.norm_of_nonneg ht0] at h2
    linarith
  have hTc : IsCompact Tset := (isCompact_Icc).of_isClosed_subset hTcl hTsub
  have hT0 : (0 : ℝ) ∈ Tset := ⟨le_rfl, by simpa using hu₀B⟩
  obtain ⟨ts, ⟨hts0, htsB⟩, htsmax⟩ := hTc.exists_isMaxOn ⟨0, hT0⟩ continuousOn_id
  set u₁ := u₀ + ts • w
  refine ⟨u₁, htsB, ?_, ?_⟩
  · -- the last point of the ray is on the frontier
    refine ⟨subset_closure htsB, fun hint => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior u₁ hint
    set s := ε / (2 * ‖w‖)
    have hs : 0 < s := by positivity
    have hmem : u₀ + (ts + s) • w ∈ B := by
      refine interior_subset (hball ?_)
      have hn : ‖s • w‖ = ε / 2 := by
        rw [norm_smul, Real.norm_of_nonneg hs.le]; simp only [s]; field_simp
      rw [mem_ball, dist_eq_norm, add_smul, ← add_assoc, add_sub_cancel_left, hn]
      linarith
    have := isMaxOn_iff.1 htsmax (ts + s) ⟨by linarith, hmem⟩
    dsimp only [id] at this
    linarith
  · -- monotonicity along the ray
    intro y hy
    refine (hu₀max hy).trans ?_
    have hm := hmono u₁ (hBO htsB) u₀ (hBO hu₀B)
    rw [show u₁ - u₀ = ts • w from add_sub_cancel_left _ _, inner_smul_right] at hm
    by_cases hv : v = 0
    · simp [hv]
    · have hwv : w = v := by simp [hw, hv]
      rw [hwv] at hm
      rcases hts0.eq_or_lt with h0 | hpos
      · have : u₁ = u₀ := by simp [u₁, ← h0]
        rw [this]
      · have h3 : 0 ≤ ⟪Q u₁ - Q u₀, v⟫_ℝ := (mul_nonneg_iff_of_pos_left hpos).1 hm
        rw [inner_sub_left, real_inner_comm v (Q u₁), real_inner_comm v (Q u₀)] at h3
        linarith

/-! ### EReal bookkeeping -/

lemma up_le (mo c : ℝ) {x y : EReal} (h : x ≤ y + c) : (mo : EReal) + x ≤ ((mo : EReal) + y) + c := by
  rw [add_assoc]; exact add_le_add_right h _

lemma lo_le (mo c : ℝ) {x y : EReal} (h : y ≤ x + c) : (mo : EReal) - x ≤ ((mo : EReal) - y) + c := by
  induction x using EReal.rec <;> induction y using EReal.rec
  · simp
  · simp at h
  · simp at h
  · simp
  · rename_i a b
    norm_cast at h ⊢
    linarith
  · simp at h
  · simp
  · simp
  · simp

/-! ### the deterministic bounds -/

lemma nnSup_mono {T : 𝔼 → 𝔼} {A A' : Set 𝔼} (h : A ⊆ A') (v : 𝔼) : nnSup T A v ≤ nnSup T A' v :=
  iSup₂_le fun u hu => le_iSup₂ (f := fun u (_ : u ∈ A') => ((⟪v, T u⟫_ℝ : ℝ) : EReal)) u (h hu)

/-- `h^pop(v) ≤ max_{𝒩}⟨v, T⟩ + E(w + η)`. -/
lemma pop_le_net (hK : 0 < K) {μ : Measure 𝔼} {O S A : Set 𝔼} {Q T : 𝔼 → 𝔼} {N : Finset 𝔼} {h η w E : ℝ}
    (hS : IsCompact S) (hSO : S ⊆ O) (hQc : ContinuousOn Q O) (hmono : MonoOn Q O) (hAS : A ⊆ S)
    (hAm : MeasurableSet A) (hη : ∀ u ∈ S, ‖T u - Q u‖ ≤ η)
    (hw : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ h → ‖Q x - Q y‖ ≤ w) (hcov : NetCovers A N h) {v : 𝔼} (hv : ‖v‖ ≤ E) :
    popSup μ Q A v ≤ nnSup T ↑N v + ((E * (w + η) : ℝ) : EReal) := by
  rcases A.eq_empty_or_nonempty with hA | hA
  · simp [popSup, hA, essSup_measure_zero]
  set Ab := closure A
  have hAbS : Ab ⊆ S := hS.isClosed.closure_subset_iff.2 hAS
  have hAb : IsCompact Ab := hS.of_isClosed_subset isClosed_closure hAbS
  obtain ⟨u, huAb, hufr, humax⟩ := exists_frontier_max hK hAb hA.closure (hAbS.trans hSO)
    (hQc.mono (hAbS.trans hSO)) hmono v
  obtain ⟨uh, huhN, hdist⟩ := hcov.2 u (frontier_closure_subset hufr)
  have huhA : uh ∈ A := hcov.1 huhN
  have hQ := hw u (hAbS huAb) uh (hAS huhA) hdist
  have hT := hη uh (hAS huhA)
  have hE : 0 ≤ E := (norm_nonneg v).trans hv
  have hreal : ⟪v, Q u⟫_ℝ ≤ ⟪v, T uh⟫_ℝ + E * (w + η) := by
    have e : ⟪v, Q u⟫_ℝ - ⟪v, T uh⟫_ℝ = ⟪v, (Q u - Q uh) + (Q uh - T uh)⟫_ℝ := by
      rw [← inner_sub_right]; congr 1; abel
    have h1 : ⟪v, (Q u - Q uh) + (Q uh - T uh)⟫_ℝ ≤ ‖v‖ * (‖Q u - Q uh‖ + ‖Q uh - T uh‖) :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _))
    rw [norm_sub_rev (Q uh)] at h1
    have h2 : ‖v‖ * (‖Q u - Q uh‖ + ‖T uh - Q uh‖) ≤ E * (w + η) :=
      mul_le_mul hv (add_le_add hQ hT) (by positivity) hE
    linarith
  have hpop : popSup μ Q A v ≤ ((⟪v, Q u⟫_ℝ : ℝ) : EReal) := by
    refine essSup_le_of_ae_le _ ((ae_restrict_mem hAm).mono fun y hy => ?_)
    exact EReal.coe_le_coe_iff.2 (humax y (subset_closure hy))
  have hnet : ((⟪v, T uh⟫_ℝ : ℝ) : EReal) ≤ nnSup T ↑N v :=
    le_iSup₂ (f := fun u (_ : u ∈ (↑N : Set 𝔼)) => ((⟪v, T u⟫_ℝ : ℝ) : EReal)) uh huhN
  calc popSup μ Q A v ≤ ((⟪v, Q u⟫_ℝ : ℝ) : EReal) := hpop
    _ ≤ ((⟪v, T uh⟫_ℝ + E * (w + η) : ℝ) : EReal) := by exact_mod_cast hreal
    _ = ((⟪v, T uh⟫_ℝ : ℝ) : EReal) + ((E * (w + η) : ℝ) : EReal) := EReal.coe_add _ _
    _ ≤ _ := add_le_add_left hnet _

/-- On a nonempty region the covering radius and the modulus bound are nonnegative. -/
lemma w_nonneg (hK : 0 < K) {O S A : Set 𝔼} {Q : 𝔼 → 𝔼} {N : Finset 𝔼} {h w : ℝ}
    (hS : IsCompact S) (hSO : S ⊆ O) (hQc : ContinuousOn Q O) (hmono : MonoOn Q O) (hAS : A ⊆ S)
    (hA : A.Nonempty) (hw : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ h → ‖Q x - Q y‖ ≤ w) (hcov : NetCovers A N h) :
    0 ≤ w := by
  have hAbS : closure A ⊆ S := hS.isClosed.closure_subset_iff.2 hAS
  obtain ⟨u, -, hufr, -⟩ := exists_frontier_max hK (hS.of_isClosed_subset isClosed_closure hAbS) hA.closure
    (hAbS.trans hSO) (hQc.mono (hAbS.trans hSO)) hmono 0
  obtain ⟨uh, huhN, hdist⟩ := hcov.2 u (frontier_closure_subset hufr)
  have hh : 0 ≤ h := (norm_nonneg _).trans hdist
  have := hw uh (hAS (hcov.1 huhN)) uh (hAS (hcov.1 huhN)) (by simpa using hh)
  simpa using (norm_nonneg _).trans this

/-- `max_{𝒩}⟨v, T⟩ ≤ h^pop(v) + E(w + η)` under the support condition. -/
lemma net_le_pop (hK : 0 < K) {μ : Measure 𝔼} {O S A : Set 𝔼} {Q T : 𝔼 → 𝔼} {N : Finset 𝔼} {h η w E : ℝ}
    (hS : IsCompact S) (hSO : S ⊆ O) (hQc : ContinuousOn Q O) (hmono : MonoOn Q O) (hAS : A ⊆ S)
    (hAm : MeasurableSet A) (hsupp : ∀ N', IsOpen N' → (N' ∩ A).Nonempty → 0 < μ (A ∩ N')) (hη0 : 0 ≤ η)
    (hη : ∀ u ∈ S, ‖T u - Q u‖ ≤ η)
    (hw : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ h → ‖Q x - Q y‖ ≤ w) (hcov : NetCovers A N h) {v : 𝔼} (hv : ‖v‖ ≤ E) :
    nnSup T ↑N v ≤ popSup μ Q A v + ((E * (w + η) : ℝ) : EReal) := by
  rcases A.eq_empty_or_nonempty with hA | hA
  · have hN : (↑N : Set 𝔼) = ∅ := Set.subset_eq_empty hcov.1 hA
    simp [nnSup, hN]
  have hw0 := w_nonneg hK hS hSO hQc hmono hAS hA hw hcov
  have hE : 0 ≤ E := (norm_nonneg v).trans hv
  have h1 : nnSup T ↑N v ≤ nnSup T A v := nnSup_mono hcov.1 v
  have h2 := (nnSup_transfer hη0 (fun u hu => hη u (hAS hu)) hv).1
  rw [← popSup_eq_nnSup hAm (hQc.mono (hAS.trans hSO)) hsupp v] at h2
  refine h1.trans (h2.trans (add_le_add_right ?_ _))
  exact_mod_cast mul_le_mul_of_nonneg_left (by linarith) hE

theorem net_inner_deficit : Claims.net_inner_deficit := by
  intro K 𝒯 μ O Q A δ mo e E T N h η w hK hset hmono hη0 hη hw hcov
  obtain ⟨_, hS, _, hSO, hQc, _, hreg, he⟩ := hset
  refine ⟨fun p hp0 hp1 t => ⟨?_, ?_⟩, fun p hp0 hp1 t => ⟨?_, ?_⟩⟩
  · exact add_le_add_right (nnSup_mono (hcov p hp0 hp1).1 _) _
  · exact EReal.sub_le_sub le_rfl (nnSup_mono (hcov p hp0 hp1).1 _)
  · exact up_le _ _ (pop_le_net hK hS hSO hQc hmono (hreg p hp0 hp1).1 (hreg p hp0 hp1).2 hη hw (hcov p hp0 hp1)
      (he t))
  · exact lo_le _ _ (pop_le_net hK hS hSO hQc hmono (hreg p hp0 hp1).1 (hreg p hp0 hp1).2 hη hw (hcov p hp0 hp1)
      (by rw [norm_neg]; exact he t))

theorem net_inner_two_sided : Claims.net_inner_two_sided := by
  intro K 𝒯 μ O Q A δ mo e E T N h η w hK hset hmono hsupp hη0 hη hw hcov p hp0 hp1 t
  obtain ⟨_, hS, _, hSO, hQc, _, hreg, he⟩ := hset
  have hA := hreg p hp0 hp1
  have hv : ‖-e t‖ ≤ E := by rw [norm_neg]; exact he t
  refine ⟨eclose_up _ _ ?_ ?_, eclose_lo _ _ ?_ ?_⟩
  · exact net_le_pop hK hS hSO hQc hmono hA.1 hA.2 (hsupp p hp0 hp1) hη0 hη hw (hcov p hp0 hp1) (he t)
  · exact pop_le_net hK hS hSO hQc hmono hA.1 hA.2 hη hw (hcov p hp0 hp1) (he t)
  · exact net_le_pop hK hS hSO hQc hmono hA.1 hA.2 (hsupp p hp0 hp1) hη0 hη hw (hcov p hp0 hp1) hv
  · exact pop_le_net hK hS hSO hQc hmono hA.1 hA.2 hη hw (hcov p hp0 hp1) hv

/-! ### monotonicity in the tolerance -/

lemma netDeficit_mono {𝒯 : Type} {μ : Measure 𝔼} {T Q : 𝔼 → 𝔼} {A : ℝ → Set 𝔼} {δ : ℝ} {mo : 𝒯 → ℝ}
    {e : 𝒯 → 𝔼} {N : ℝ → Finset 𝔼} {c d : ℝ} (h : NetDeficit μ T Q A δ mo e N c) (hcd : c ≤ d) :
    NetDeficit μ T Q A δ mo e N d := by
  have : (c : EReal) ≤ d := by exact_mod_cast hcd
  intro p hp0 hp1 t
  exact ⟨(h p hp0 hp1 t).1.trans (add_le_add_right this _), (h p hp0 hp1 t).2.trans (add_le_add_right this _)⟩

lemma netClose_mono {𝒯 : Type} {μ : Measure 𝔼} {T Q : 𝔼 → 𝔼} {A : ℝ → Set 𝔼} {δ : ℝ} {mo : 𝒯 → ℝ}
    {e : 𝒯 → 𝔼} {N : ℝ → Finset 𝔼} {c d : ℝ} (h : NetClose μ T Q A δ mo e N c) (hcd : c ≤ d) :
    NetClose μ T Q A δ mo e N d := fun p hp0 hp1 t =>
  ⟨eclose_mono (h p hp0 hp1 t).1 hcd, eclose_mono (h p hp0 hp1 t).2 hcd⟩

/-! ### the uniform core for nets -/

/-- For every `ε > 0` there are `h₀, η₀ > 0` such that a monotone `T` with risk `≤ η₀` and nets of radius `< h₀`
have net deficit `≤ ε` (and, under the support condition, two-sided error `≤ ε`). -/
lemma net_uniform {𝒯 : Type} (hK : 0 < K) {μ : Measure 𝔼} {O : Set 𝔼} {Q : 𝔼 → 𝔼} {A : ℝ → Set 𝔼} {δ : ℝ}
    {mo : 𝒯 → ℝ} {e : 𝒯 → 𝔼} {E : ℝ} (hset : NeuralSetting μ O Q A δ e E) (hmono : MonoOn Q O) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ h₀ > 0, ∃ η₀ > 0, ∀ (T : 𝔼 → 𝔼) (N : ℝ → Finset 𝔼) (h : ℝ), MonoOn T O →
      risk μ O T Q ≤ ENNReal.ofReal η₀ → h < h₀ → (∀ p, 0 < p → p ≤ 1 - δ → NetCovers (A p) (N p) h) →
        NetDeficit μ T Q A δ mo e N ε ∧
          ((∀ p, 0 < p → p ≤ 1 - δ → ∀ N', IsOpen N' → (N' ∩ A p).Nonempty → 0 < μ (A p ∩ N')) →
            NetClose μ T Q A δ mo e N ε) := by
  have hset' := hset
  obtain ⟨hprob, hS, hO, hSO, hQc, hpos, _, _⟩ := hset
  have := hprob
  set E' := max E 0
  have hE' : 0 < E' + 1 := by positivity
  set ε' := ε / (2 * (E' + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨h₀, hh₀, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous (hQc.mono hSO)) ε' hε'0
  obtain ⟨η₀, hη₀, hcore⟩ := unif_core hS hO hSO hQc hpos hε'0
  refine ⟨h₀, hh₀, η₀, hη₀, fun T N h hT hR hh hcov => ?_⟩
  have hη := hcore T hT hR
  have hw : ∀ x ∈ A (1 - δ), ∀ y ∈ A (1 - δ), ‖x - y‖ ≤ h → ‖Q x - Q y‖ ≤ ε' := by
    intro x hx y hy hxy
    rw [← dist_eq_norm]
    exact (hunif x hx y hy (by rw [dist_eq_norm]; linarith)).le
  have hle : E * (ε' + ε') ≤ ε := by
    have : E * (ε' + ε') ≤ (E' + 1) * (ε' + ε') :=
      mul_le_mul_of_nonneg_right (by linarith [le_max_left E 0]) (by positivity)
    refine this.trans (le_of_eq ?_)
    simp only [hε']
    field_simp
    ring
  refine ⟨netDeficit_mono ((net_inner_deficit K 𝒯 μ O Q A δ mo e E T N h ε' ε' hK hset' hmono hε'0.le hη hw
    hcov).2) hle, fun hsupp => netClose_mono (net_inner_two_sided K 𝒯 μ O Q A δ mo e E T N h ε' ε' hK hset'
    hmono hsupp hε'0.le hη hw hcov) hle⟩

theorem net_band_neural_ae : Claims.net_band_neural_ae := by
  intro K 𝒯 μ O Q A δ mo e E Ω _ P T N h hK hset hmono hTm hh hcov hlim
  filter_upwards [hlim] with ω hω
  intro ε hε
  obtain ⟨h₀, hh₀, η₀, hη₀, hgood⟩ := net_uniform (mo := mo) hK hset hmono hε
  filter_upwards [(tendsto_order.1 hω).2 _ (ENNReal.ofReal_pos.2 hη₀), (tendsto_order.1 hh).2 _ hh₀] with n hn hhn
  exact (hgood _ _ _ (hTm n ω) hn.le hhn (hcov n)).1

theorem net_band_neural_prob : Claims.net_band_neural_prob := by
  intro K 𝒯 μ O Q A δ mo e E Ω _ P T N h hK hset hmono hTm hh hcov hlim ε hε δ' hδ'
  obtain ⟨h₀, hh₀, η₀, hη₀, hgood⟩ := net_uniform (mo := mo) hK hset hmono hε
  filter_upwards [hlim η₀ hη₀ δ' hδ', (tendsto_order.1 hh).2 _ hh₀] with n ⟨G, hG, hGsub, hPG⟩ hhn
  exact ⟨G, hG, fun ω hω => (hgood _ _ _ (hTm n ω) (hGsub hω) hhn (hcov n)).1, hPG⟩

theorem net_band_neural_two_sided_ae : Claims.net_band_neural_two_sided_ae := by
  intro K 𝒯 μ O Q A δ mo e E Ω _ P T N h hK hset hmono hTm hsupp hh hcov hlim
  filter_upwards [hlim] with ω hω
  intro ε hε
  obtain ⟨h₀, hh₀, η₀, hη₀, hgood⟩ := net_uniform (mo := mo) hK hset hmono hε
  filter_upwards [(tendsto_order.1 hω).2 _ (ENNReal.ofReal_pos.2 hη₀), (tendsto_order.1 hh).2 _ hh₀] with n hn hhn
  exact (hgood _ _ _ (hTm n ω) hn.le hhn (hcov n)).2 hsupp

theorem net_band_neural_two_sided_prob : Claims.net_band_neural_two_sided_prob := by
  intro K 𝒯 μ O Q A δ mo e E Ω _ P T N h hK hset hmono hTm hsupp hh hcov hlim ε hε δ' hδ'
  obtain ⟨h₀, hh₀, η₀, hη₀, hgood⟩ := net_uniform (mo := mo) hK hset hmono hε
  filter_upwards [hlim η₀ hη₀ δ' hδ', (tendsto_order.1 hh).2 _ hh₀] with n ⟨G, hG, hGsub, hPG⟩ hhn
  exact ⟨G, hG, fun ω hω => (hgood _ _ _ (hTm n ω) (hGsub hω) hhn (hcov n)).2 hsupp, hPG⟩

/-! ### the rate -/

/-- The map bound in the proof of `thm:neural-band-consistency` (restated from the Wave 7a route): for small risk,
`sup_S ‖T − Q‖ ≤ C_{K,ρ} L^{K/(K+2)} 𝓡^{1/(K+2)}`. -/
lemma rate_sup (K : ℕ) (ρ : ℝ) (hK : 0 < K) (hρ : 0 < ρ) : ∃ Cst : ℝ, 0 < Cst ∧
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin K))) (O O' S : Set (EuclideanSpace ℝ (Fin K)))
      (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (L : ℝ),
      IsCompact S → IsOpen O → S ⊆ O → ContinuousOn Q O →
      IsOpen O' → S ⊆ O' → O' ⊆ O →
      (∀ B, MeasurableSet B → B ⊆ O' → ENNReal.ofReal ρ * volume B ≤ μ B) →
      0 < L → (∀ x ∈ O', ∀ y ∈ O', ‖Q x - Q y‖ ≤ L * ‖x - y‖) →
        ∃ R₀, 0 < R₀ ∧ ∀ R, 0 < R → R ≤ R₀ →
          ∀ T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
            MonoOn T O → risk μ O T Q ≤ ENNReal.ofReal R →
              ∀ u ∈ S, ‖T u - Q u‖ ≤ Cst * L ^ ((K : ℝ) / (K + 2)) * R ^ ((1 : ℝ) / (K + 2)) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin K)) := by
    have : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin K)) := by rw [finrank_euclideanSpace_fin]; exact hK
    exact Module.nontrivial_of_finrank_pos this
  set V := (volume (ball (0 : (EuclideanSpace ℝ (Fin K))) 1)).toReal
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume (0 : (EuclideanSpace ℝ (Fin K))) one_pos).ne'
    measure_ball_lt_top.ne
  set c0 := (4 : ℝ) ^ K / (ρ * V)
  have hc0 : 0 < c0 := by positivity
  refine ⟨5 / 3 * (5 / 4 + Real.sqrt c0), by positivity, ?_⟩
  intro μ O O' S Q L hS hO hSO hQc hO' hSO' hO'O hdens hL hLip
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
  have hballm : ∀ u ∈ S, ∀ e : (EuclideanSpace ℝ (Fin K)), ‖e‖ = 1 →
      ENNReal.ofReal m ≤ μ (ball (u + r • e) (r / 4)) := by
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
  have hw := StatFormal.OTFD.Wave4.neural_witness_ball K μ S O T Q ω r m R hS hO hSO hQc hT hr
    (hthick.trans hO'O) hωmono hmod hm hballm hrisk
  have hRm : R / m = c0 * (L * r) ^ 2 := by
    have hR : R = L ^ 2 * r ^ (K + 2) := by rw [hrpow]; field_simp
    simp only [m, c0]
    rw [hR, div_pow, pow_add]
    field_simp
  have hsq : Real.sqrt (R / m) = Real.sqrt c0 * (L * r) := by
    rw [hRm, Real.sqrt_mul hc0.le, Real.sqrt_sq (by positivity)]
  intro u hu
  have h := hw u hu
  simp only [ω] at h
  rw [hsq] at h
  calc ‖T u - Q u‖ ≤ 5 / 3 * (L * (5 * r / 4) + Real.sqrt c0 * (L * r)) := h
    _ = 5 / 3 * (5 / 4 + Real.sqrt c0) * (L * r) := by ring
    _ = _ := by rw [Lr_eq hL hR0 K]; ring

theorem net_band_neural_rate : Claims.net_band_neural_rate := by
  intro K ρ hK hρ
  obtain ⟨Cst, hCst, hrate⟩ := rate_sup K ρ hK hρ
  refine ⟨Cst, hCst, ?_⟩
  intro 𝒯 μ O O' Q A δ mo e E L hset hmono hsupp hO' hSO' hO'O hdens hL hLip
  have hset' := hset
  obtain ⟨_, hS, hO, hSO, hQc, _, _, _⟩ := hset
  obtain ⟨R₀, hR₀, hgood⟩ := hrate μ O O' (A (1 - δ)) Q L hS hO hSO hQc hO' hSO' hO'O hdens hL hLip
  refine ⟨R₀, hR₀, fun R hR hRle T hT hrisk N h hh hcov => ?_⟩
  have hη := hgood R hR hRle T hT hrisk
  have hη0 : 0 ≤ Cst * L ^ ((K : ℝ) / (K + 2)) * R ^ ((1 : ℝ) / (K + 2)) := by positivity
  have hw : ∀ x ∈ A (1 - δ), ∀ y ∈ A (1 - δ), ‖x - y‖ ≤ h → ‖Q x - Q y‖ ≤ L * h := fun x hx y hy hxy =>
    (hLip x (hSO' hx) y (hSO' hy)).trans (mul_le_mul_of_nonneg_left hxy hL.le)
  exact net_inner_two_sided K 𝒯 μ O Q A δ mo e E T N h _ (L * h) hK hset' hmono hsupp hη0 hη hw hcov

end StatFormal.OTFD.Wave16b
