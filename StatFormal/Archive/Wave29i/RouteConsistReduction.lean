import StatFormal.Archive.Wave29i.RouteConsistPool

/-!
# Route — ICL `cor:consistency`, the reduction (untrusted)

`J_m(w) − devFull(Π°_w) = R(μ_w) + λ_KL KL(w|u_n)` on a distinct pool (with the frozen `swor_cps`); the frozen
`thm:joint` (`joint_full`, `δ = 1/m`, applied to the law `Π°_w` on `[n]^M` with the loss `L(·; z∘t)` on injective
`t` and `0` elsewhere, which `Π°_w` does not charge) and `cor:oracle` (`ICL/Diag` `oracle`) give the oracle event.
Proves `consist_reduction`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

namespace StatFormal.Wave29i

open StatFormal.Wave11b (distinctSet ctxLaw Admissible jSwor collision lossSub swoExp)
open StatFormal.Wave26b (poolLaw riskIid)
open StatFormal.Wave20a (rhoC PhiC)
open StatFormal.ICL (InDeltaM)
open StatFormal.ICL.Diag (klUnif)
open StatFormal.ICL.Cond (iidLaw)
open StatFormal.ICL.Joint (ProbVec)
open StatFormal.ICL.JointFull (devFull cover oneSlot)
open StatFormal.Foundations.SworLaw

variable {Z : Type} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

namespace ConsistR

section Red
variable {n M : ℕ}

lemma grisk_eq {L : Z → (Fin M → Z) → ℝ} (hsym : ∀ z t (σ : Equiv.Perm (Fin M)), L z (t ∘ σ) = L z t)
    (z : Fin n → Z) {w : Fin n → ℝ} (hΔ : InDeltaM w M) (hM : 1 ≤ M) (x : Z) :
    StatFormal.ICL.Grisk w M (lossSub L x z) = ∑ t, consistOrdLaw M w t * L x (z ∘ t) := by
  obtain ⟨t0, -, -⟩ := exists_inj_pos hΔ
  rw [(StatFormal.Wave11b.swor_cps Z n M w L x z (t0 ⟨0, hM⟩) hΔ hsym).2.1, swoExp_eq_ordLaw]

lemma incl_eq (z : Fin n → Z) {w : Fin n → ℝ} (hΔ : InDeltaM w M) (hM : 1 ≤ M) (l : Fin n) :
    StatFormal.ICL.incl w M l / M = oneSlot (consistOrdLaw M w) l := by
  rw [(StatFormal.Wave11b.swor_cps Z n M w (fun _ _ => (0 : ℝ)) (z l) z l hΔ (fun _ _ _ => rfl)).2.2 hM,
    swoExp_eq_ordLaw]
  unfold oneSlot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

lemma integrable_ordLaw_term {L : Z → (Fin M → Z) → ℝ}
    (hL : ContinuousOn (fun p : Z × (Fin M → Z) => L p.1 p.2) (univ ×ˢ distinctSet M))
    (P₀ : Measure Z) [IsProbabilityMeasure P₀] {z : Fin n → Z} (hz : Function.Injective z) (w : Fin n → ℝ)
    (t : Fin M → Fin n) : Integrable (fun x => consistOrdLaw M w t * L x (z ∘ t)) P₀ := by
  by_cases ht : Function.Injective t
  · exact (StatFormal.Wave26b.integrable_of_continuous_bdd P₀ (continuousOn_query hL (hz.comp ht))).const_mul _
  · simp only [ordLaw_of_not_inj ht, zero_mul]
    exact integrable_zero _ _ _

/-- The reduction identity: the deployed objective of `Π°_w` is `R(μ_w) + λ_KL KL(w|u_n)`. -/
lemma jSwor_sub_devFull (hM : 1 ≤ M) {L : Z → (Fin M → Z) → ℝ} {Kk : Z → Z → ℝ}
    (hL : ContinuousOn (fun p : Z × (Fin M → Z) => L p.1 p.2) (univ ×ˢ distinctSet M))
    (hsym : ∀ z t (σ : Equiv.Perm (Fin M)), L z (t ∘ σ) = L z t) (hK : Continuous (Function.uncurry Kk))
    (P₀ : Measure Z) [IsProbabilityMeasure P₀] {z : Fin n → Z} (hz : Function.Injective z) {w : Fin n → ℝ}
    (hΔ : InDeltaM w M) {m : ℕ} (xs : Fin m → Z) (lcov lKL : ℝ) :
    jSwor L Kk z xs lcov lKL w -
        devFull P₀ (fun t x => L x (z ∘ t)) (fun j x => Kk x (z j)) lcov (consistOrdLaw M w) xs =
      consistRisk L Kk lcov P₀ (poolLaw z w) + lKL * klUnif n w := by
  have hcov : ∀ x, (∑ l, StatFormal.ICL.incl w M l / M * Kk x (z l)) =
      cover (fun j x => Kk x (z j)) (consistOrdLaw M w) x := by
    intro x; unfold cover; simp_rw [incl_eq z hΔ hM]
  have hrisk : ∫ x, consistG L (poolLaw z w) x ∂P₀ = ∑ t, consistOrdLaw M w t * ∫ x, L x (z ∘ t) ∂P₀ := by
    simp_rw [consistG_poolLaw hz hΔ]
    rw [integral_finsetSum _ fun t _ => integrable_ordLaw_term hL P₀ hz w t]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [integral_const_mul]
  have hphi : PhiC Kk P₀ (consistMarg (poolLaw z w) M) =
      -∫ x, Real.log (cover (fun j x => Kk x (z j)) (consistOrdLaw M w) x) ∂P₀ := by
    unfold PhiC; simp_rw [rhoC_poolLaw hK hz hΔ]
  unfold jSwor consistRisk devFull StatFormal.ICL.Joint.devJ
  rw [hrisk, hphi]
  simp_rw [grisk_eq hsym z hΔ hM, hcov]
  have hswap : (1 / (m : ℝ)) * ∑ i, ∑ t, consistOrdLaw M w t * L (xs i) (z ∘ t) =
      ∑ t, consistOrdLaw M w t * ((1 / (m : ℝ)) * ∑ i, L (xs i) (z ∘ t)) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hswap]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

lemma devFull_congr_inj {L : Z → (Fin M → Z) → ℝ} {Kk : Z → Z → ℝ} (P₀ : Measure Z) (z : Fin n → Z)
    (w : Fin n → ℝ) (lcov : ℝ) {m : ℕ} (xs : Fin m → Z) :
    devFull P₀ (fun t x => if Function.Injective t then L x (z ∘ t) else 0) (fun j x => Kk x (z j)) lcov
        (consistOrdLaw M w) xs =
      devFull P₀ (fun t x => L x (z ∘ t)) (fun j x => Kk x (z j)) lcov (consistOrdLaw M w) xs := by
  unfold devFull StatFormal.ICL.Joint.devJ
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases ht : Function.Injective t
  · simp only [ht, ite_true]
  · simp only [ordLaw_of_not_inj ht, zero_mul]

/-- The oracle event (`thm:joint` at `δ = 1/m` + `cor:oracle` + the reduction). -/
lemma oracle_event_swor {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (hM : 1 ≤ M) {L : Z → (Fin M → Z) → ℝ} {Kk : Z → Z → ℝ}
    {BL Kmin Kmax lcov lKL eps : ℝ}
    (hL : ContinuousOn (fun p : Z × (Fin M → Z) => L p.1 p.2) (univ ×ˢ distinctSet M))
    (hLb : ∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) (hsym : ∀ z t (σ : Equiv.Perm (Fin M)), L z (t ∘ σ) = L z t)
    (hK : Continuous (Function.uncurry Kk)) (hKmin : 0 < Kmin) (hKb : ∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax)
    (hlcov : 0 ≤ lcov) (hlKL : 0 ≤ lKL) (P₀ : Measure Z) [IsProbabilityMeasure P₀] {z : Fin n → Z}
    (hz : Function.Injective z) (hzS : ∀ i, z i ∈ P₀.support)
    (X : Fin m → Ω → Z) (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P) (hXl : ∀ i, P.map (X i) = P₀)
    (wh : Ω → Fin n → ℝ) (hwh : ∀ ω, InDeltaM (wh ω) M)
    (hopt : ∀ ω (w : Fin n → ℝ), InDeltaM w M →
      jSwor L Kk z (fun i => X i ω) lcov lKL (wh ω) ≤ jSwor L Kk z (fun i => X i ω) lcov lKL w + eps) :
    ∃ S : Set Ω, MeasurableSet S ∧ ENNReal.ofReal (1 - 1 / m) ≤ P S ∧ ∀ ω ∈ S, ∀ w : Fin n → ℝ,
      InDeltaM w M →
        consistRisk L Kk lcov P₀ (poolLaw z (wh ω)) ≤
          consistRisk L Kk lcov P₀ (poolLaw z w) + lKL * Real.log n + eps +
            2 * StatFormal.Wave24d.devBound BL lcov Kmin Kmax M n m (1 / m) := by
  have hm0 : 0 < m := by omega
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hδ0 : (0 : ℝ) < 1 / m := by positivity
  have hδ1 : (1 : ℝ) / m < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hBL : 0 ≤ BL := le_trans (hLb (z ⟨0, by omega⟩) (fun _ => z ⟨0, by omega⟩)).1
    (hLb (z ⟨0, by omega⟩) (fun _ => z ⟨0, by omega⟩)).2
  set L' : (Fin M → Fin n) → Z → ℝ := fun t x => if Function.Injective t then L x (z ∘ t) else 0 with hL'
  have hL'm : ∀ t, Measurable (L' t) := by
    intro t
    by_cases ht : Function.Injective t
    · simp only [hL', ht, ite_true]; exact (continuousOn_query hL (hz.comp ht)).measurable
    · simp only [hL', ht, ite_false]; exact measurable_const
  have hL'b : ∀ t x, 0 ≤ L' t x ∧ L' t x ≤ BL := by
    intro t x
    by_cases ht : Function.Injective t
    · simp only [hL', ht, ite_true]; exact hLb _ _
    · simp only [hL', ht, ite_false]; exact ⟨le_rfl, hBL⟩
  obtain ⟨S, hSm, hSP, hSsub⟩ := StatFormal.ICL.JointFull.joint_full Z Ω P P₀ n M m L'
    (fun j x => Kk x (z j)) BL Kmin Kmax lcov (1 / m) X hn hM hm0 hδ0 hδ1 hlcov hKmin hL'm hL'b
    (fun j => (hK.comp (Continuous.prodMk continuous_id continuous_const)).measurable) (fun j x => hKb x _)
    hXm hXi hXl
  refine ⟨S, hSm, hSP, fun ω hω w hw => ?_⟩
  set dev := StatFormal.Wave24d.devBound BL lcov Kmin Kmax M n m (1 / m) with hdev
  set SV : Set (Fin n → ℝ) := {w | InDeltaM w M} with hSV
  set Jp : (Fin n → ℝ) → ℝ := fun w => consistRisk L Kk lcov P₀ (poolLaw z w) + lKL * klUnif n w with hJp
  have hne : SV.Nonempty := ⟨wh ω, hwh ω⟩
  have hdevw : ∀ w ∈ SV, |jSwor L Kk z (fun i => X i ω) lcov lKL w - Jp w| ≤ dev := by
    intro w hw
    have hid := jSwor_sub_devFull hM hL hsym hK P₀ hz hw (fun i => X i ω) lcov lKL
    have h1 : jSwor L Kk z (fun i => X i ω) lcov lKL w - Jp w =
        devFull P₀ L' (fun j x => Kk x (z j)) lcov (consistOrdLaw M w) (fun i => X i ω) := by
      rw [hL', devFull_congr_inj]; simp only [hJp]; linarith
    rw [h1]
    have := hSsub hω (consistOrdLaw M w) (ordLaw_probVec hw)
    simpa [hdev, StatFormal.Wave24d.devBound] using this
  have hJpLow : ∀ w ∈ SV, -(lcov * Real.log Kmax) ≤ Jp w := by
    intro w hw
    haveI := StatFormal.Wave26b.poolLaw_isProb z (w := w) ⟨hw.1, hw.2.1⟩
    have h1 := consistRisk_ge (L := L) hM hLb hK hKmin hKb hlcov P₀ (poolLaw z w)
      (admissible_poolLaw P₀ hz hzS hw).2.2
    have h2 := mul_nonneg hlKL (StatFormal.Wave26b.klUnif_nonneg ⟨hw.1, hw.2.1⟩)
    simp only [hJp]; linarith
  have hBdd : BddBelow (Jp '' SV) := ⟨_, by rintro _ ⟨w, hw, rfl⟩; exact hJpLow w hw⟩
  have hmin : jSwor L Kk z (fun i => X i ω) lcov lKL (wh ω) ≤
      sInf ((fun w => jSwor L Kk z (fun i => X i ω) lcov lKL w) '' SV) + eps := by
    have : jSwor L Kk z (fun i => X i ω) lcov lKL (wh ω) - eps ≤
        sInf ((fun w => jSwor L Kk z (fun i => X i ω) lcov lKL w) '' SV) := by
      refine le_csInf (hne.image _) ?_
      rintro _ ⟨w, hw, rfl⟩
      linarith [hopt ω w hw]
    linarith
  have horacle := StatFormal.ICL.Diag.oracle (Fin n → ℝ) SV
    (fun w => jSwor L Kk z (fun i => X i ω) lcov lKL w) Jp dev eps (wh ω) (hwh ω) hdevw hBdd hmin
  have hR : consistRisk L Kk lcov P₀ (poolLaw z (wh ω)) ≤ Jp (wh ω) := by
    have := mul_nonneg hlKL (StatFormal.Wave26b.klUnif_nonneg ⟨(hwh ω).1, (hwh ω).2.1⟩)
    simp only [hJp]; linarith
  have hinf : sInf (Jp '' SV) ≤ consistRisk L Kk lcov P₀ (poolLaw z w) + lKL * Real.log n := by
    have h1 : sInf (Jp '' SV) ≤ Jp w := csInf_le hBdd ⟨w, hw, rfl⟩
    have h2 : lKL * klUnif n w ≤ lKL * Real.log n :=
      mul_le_mul_of_nonneg_left (StatFormal.Wave26b.klUnif_le_log ⟨hw.1, hw.2.1⟩) hlKL
    simp only [hJp] at h1; linarith
  linarith

end Red

end ConsistR

open ConsistR

theorem consist_reduction : Claims.consist_reduction := by
  intro Z Ω₀ _ _ _ _ _ P₀ _ Q _ Zs M L Kk BL Kmin Kmax lcov hM hat hL hLb hsym hK hKmin hKb hlcov hZm hZi hZl
  have hatQ : ∀ i x, Q.map (Zs i) {x} = 0 := fun i x => by rw [hZl i]; exact hat x
  filter_upwards [StatFormal.Wave26b.ae_pool_dense hZm hZi hZl, ae_injective_of_iIndep hZm hZi hatQ]
    with ω₀ hω₀ hinj
  intro n
  have hzinj : Function.Injective fun i : Fin n => Zs i ω₀ := fun a b h => Fin.ext (hinj h)
  refine ⟨fun w hΔ => ⟨admissible_poolLaw P₀ hzinj (fun i => hω₀.1 i) hΔ,
    fun m xs lKL => jSwor_sub_devFull hM hL hsym hK P₀ hzinj hΔ xs lcov lKL,
    StatFormal.Wave26b.klUnif_nonneg ⟨hΔ.1, hΔ.2.1⟩, StatFormal.Wave26b.klUnif_le_log ⟨hΔ.1, hΔ.2.1⟩⟩, ?_⟩
  intro Ω _ P _ m X wh lKL eps hn hm hlKL hXm hXi hXl hwh hopt
  exact oracle_event_swor P hn hm hM hL hLb hsym hK hKmin hKb hlcov hlKL P₀ hzinj (fun i => hω₀.1 i) X hXm hXi
    hXl wh hwh hopt

end StatFormal.Wave29i
