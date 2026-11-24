import StatFormal.Archive.Wave26b.RouteICLAlg
import StatFormal.Archive.ICL.JointFull.Proofs
import StatFormal.Archive.ICL.Diag.Proofs
import StatFormal.Archive.Wave24d.RouteICL

/-!
# Route — ICL `cor:iid-consistency`, objectives and the oracle event (untrusted)

* `ρ_μ(z) ∈ [K_min, K_max]` and `G^iid_μ(z) ∈ [0, B_L]` are continuous in `z`; `R^iid ≥ −λ_cov log K_max`.
* Reduction: `J^iid_m(w) − J_pool(w) = devFull(w^{⊗M})` with `J_pool(w) = R^iid(μ_w) + λ_KL KL(w|u_n)`.
* The oracle event: the frozen `thm:joint` (`joint_full`, `δ = 1/m`) and `cor:oracle` give, with probability
  `≥ 1 − 1/m`, `R^iid(μ_ŵ) ≤ inf_w R^iid(μ_w) + λ_KL log n + ε_opt + 2 dev`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

namespace StatFormal.Wave26b

open StatFormal.Wave20a (rhoC PhiC)
open StatFormal.ICL.Joint (ProbVec)
open StatFormal.ICL.Diag (klUnif)

variable {Z : Type} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-! ### Continuity and bounds in the query -/

lemma continuous_rhoC {Kk : Z → Z → ℝ} {Kmin Kmax : ℝ} (hK : Continuous (Function.uncurry Kk))
    (hKb : ∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax) (hKmin : 0 < Kmin) (μ : Measure Z) [IsFiniteMeasure μ] :
    Continuous (rhoC Kk μ) := by
  unfold rhoC
  refine continuous_of_dominated (bound := fun _ => Kmax) (fun z => ?_) (fun z => ?_) (integrable_const _) ?_
  · exact (hK.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun z' => ?_
    rw [Real.norm_eq_abs, abs_of_pos (hKmin.trans_le (hKb z z').1)]
    exact (hKb z z').2
  · exact Eventually.of_forall fun z' => hK.comp (Continuous.prodMk continuous_id continuous_const)

lemma rhoC_mem {Kk : Z → Z → ℝ} {Kmin Kmax : ℝ} (hK : Continuous (Function.uncurry Kk))
    (hKb : ∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax) (μ : Measure Z) [IsProbabilityMeasure μ] (z : Z) :
    Kmin ≤ rhoC Kk μ z ∧ rhoC Kk μ z ≤ Kmax := by
  unfold rhoC
  have hint : Integrable (fun z' => Kk z z') μ := by
    refine Integrable.of_bound (C := max |Kmin| |Kmax|)
      (hK.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z' => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := (hKb z z').1
      have := neg_abs_le Kmin
      have := le_max_left |Kmin| |Kmax|
      linarith
    · have := (hKb z z').2
      have := le_abs_self Kmax
      have := le_max_right |Kmin| |Kmax|
      linarith
  constructor
  · calc Kmin = ∫ _, Kmin ∂μ := by simp
      _ ≤ _ := integral_mono (integrable_const _) hint fun z' => (hKb z z').1
  · calc ∫ z', Kk z z' ∂μ ≤ ∫ _, Kmax ∂μ := integral_mono hint (integrable_const _) fun z' => (hKb z z').2
      _ = Kmax := by simp

lemma continuous_gIid {M : ℕ} {L : Z → (Fin M → Z) → ℝ} {BL : ℝ}
    (hL : Continuous (fun p : Z × (Fin M → Z) => L p.1 p.2)) (hLb : ∀ z t, 0 ≤ L z t ∧ L z t ≤ BL)
    (μ : Measure Z) [IsFiniteMeasure μ] : Continuous (gIid L μ) := by
  unfold gIid
  refine continuous_of_dominated (bound := fun _ => BL) (fun z => ?_) (fun z => ?_) (integrable_const _) ?_
  · exact (hL.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hLb z t).1]
    exact (hLb z t).2
  · exact Eventually.of_forall fun t => hL.comp (Continuous.prodMk continuous_id continuous_const)

lemma gIid_mem {M : ℕ} {L : Z → (Fin M → Z) → ℝ} {BL : ℝ}
    (hL : Continuous (fun p : Z × (Fin M → Z) => L p.1 p.2)) (hLb : ∀ z t, 0 ≤ L z t ∧ L z t ≤ BL)
    (μ : Measure Z) [IsProbabilityMeasure μ] (z : Z) : 0 ≤ gIid L μ z ∧ gIid L μ z ≤ BL := by
  unfold gIid
  have hint : Integrable (fun t => L z t) (Measure.pi fun _ : Fin M => μ) := by
    refine Integrable.of_bound (C := BL)
      (hL.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hLb z t).1]
    exact (hLb z t).2
  constructor
  · exact integral_nonneg fun t => (hLb z t).1
  · calc ∫ t, L z t ∂(Measure.pi fun _ : Fin M => μ) ≤ ∫ _, BL ∂(Measure.pi fun _ : Fin M => μ) :=
        integral_mono hint (integrable_const _) fun t => (hLb z t).2
      _ = BL := by simp

lemma integrable_of_continuous_bdd (P : Measure Z) [IsFiniteMeasure P] {f : Z → ℝ} (hf : Continuous f) :
    Integrable f P := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hf).isBounded.exists_norm_le
  exact Integrable.of_bound (C := C) hf.aestronglyMeasurable
    (Eventually.of_forall fun z => hC _ ⟨z, mem_univ _, rfl⟩)

lemma riskIid_ge {M : ℕ} {L : Z → (Fin M → Z) → ℝ} {Kk : Z → Z → ℝ} {BL Kmin Kmax lcov : ℝ}
    (hL : Continuous (fun p : Z × (Fin M → Z) => L p.1 p.2)) (hLb : ∀ z t, 0 ≤ L z t ∧ L z t ≤ BL)
    (hK : Continuous (Function.uncurry Kk)) (hKmin : 0 < Kmin) (hKb : ∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax)
    (hlcov : 0 ≤ lcov) (P₀ : Measure Z) [IsProbabilityMeasure P₀] (μ : Measure Z) [IsProbabilityMeasure μ] :
    -(lcov * Real.log Kmax) ≤ riskIid L Kk lcov P₀ μ := by
  unfold riskIid PhiC
  have h1 : 0 ≤ ∫ z, gIid L μ z ∂P₀ := integral_nonneg fun z => (gIid_mem hL hLb μ z).1
  have hρc := continuous_rhoC hK hKb hKmin μ
  have h2 : ∫ z, Real.log (rhoC Kk μ z) ∂P₀ ≤ Real.log Kmax := by
    have hcont : Continuous fun z => Real.log (rhoC Kk μ z) :=
      hρc.log fun z => (hKmin.trans_le (rhoC_mem hK hKb μ z).1).ne'
    calc ∫ z, Real.log (rhoC Kk μ z) ∂P₀ ≤ ∫ _, Real.log Kmax ∂P₀ :=
          integral_mono (integrable_of_continuous_bdd P₀ hcont) (integrable_const _) fun z =>
            Real.log_le_log (hKmin.trans_le (rhoC_mem hK hKb μ z).1) (rhoC_mem hK hKb μ z).2
      _ = Real.log Kmax := by simp
  nlinarith

/-! ### The reduction `J_m − J_pool = devFull(w^{⊗M})` -/

/-- The deployed objective `J_pool(w) = R^iid(μ_w) + λ_KL KL(w|u_n)`. -/
def jPool {n M : ℕ} (L : Z → (Fin M → Z) → ℝ) (Kk : Z → Z → ℝ) (lcov lKL : ℝ) (P₀ : Measure Z)
    (z : Fin n → Z) (w : Fin n → ℝ) : ℝ :=
  riskIid L Kk lcov P₀ (poolLaw z w) + lKL * klUnif n w

lemma jIid_sub_jPool {n m M : ℕ} (hM : 1 ≤ M) {L : Z → (Fin M → Z) → ℝ} {Kk : Z → Z → ℝ} {BL Kmin Kmax : ℝ}
    (hL : Continuous (fun p : Z × (Fin M → Z) => L p.1 p.2)) (hLb : ∀ z t, 0 ≤ L z t ∧ L z t ≤ BL)
    (hK : Continuous (Function.uncurry Kk)) (hKmin : 0 < Kmin) (hKb : ∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax)
    (lcov lKL : ℝ) (P₀ : Measure Z) [IsProbabilityMeasure P₀] (z : Fin n → Z) (xs : Fin m → Z)
    {w : Fin n → ℝ} (hw : ProbVec w) :
    jIidEmp L Kk lcov lKL z xs w - jPool L Kk lcov lKL P₀ z w =
      StatFormal.ICL.JointFull.devFull P₀ (fun t x => L x (z ∘ t)) (fun j x => Kk x (z j)) lcov
        (prodLaw (M := M) w) xs := by
  have hLx : ∀ x, Measurable (L x) := fun x =>
    (hL.comp (Continuous.prodMk continuous_const continuous_id)).measurable
  have hLt : ∀ t : Fin M → Fin n, Continuous fun x => L x (z ∘ t) := fun t =>
    hL.comp (Continuous.prodMk continuous_id continuous_const)
  have hKx : ∀ x, Measurable (Kk x) := fun x =>
    (hK.comp (Continuous.prodMk continuous_const continuous_id)).measurable
  haveI := poolLaw_isProb z hw
  -- the risk part of `J_pool`
  have hrisk : ∫ x, gIid L (poolLaw z w) x ∂P₀ = ∑ t : Fin M → Fin n, prodLaw w t * ∫ x, L x (z ∘ t) ∂P₀ := by
    rw [integral_congr_ae (Eventually.of_forall fun x => gIid_poolLaw L z hw.1 x (hLx x))]
    unfold gIidPool
    rw [integral_finsetSum _ fun t _ => (integrable_of_continuous_bdd P₀ (hLt t)).const_mul _]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [integral_const_mul]
    rfl
  -- the coverage part
  have hcov : PhiC Kk P₀ (poolLaw z w) = -∫ x, Real.log (rhoPool Kk z w x) ∂P₀ := by
    unfold PhiC
    rw [integral_congr_ae (Eventually.of_forall fun x => by rw [rhoC_poolLaw Kk z hw.1 x (hKx x)])]
  unfold jIidEmp jPool riskIid StatFormal.ICL.JointFull.devFull StatFormal.ICL.Joint.devJ
  rw [hrisk, hcov]
  simp_rw [cover_prodLaw hM Kk z hw]
  unfold gIidPool
  have hswap : (1 / (m : ℝ)) * ∑ i, ∑ t : Fin M → Fin n, (∏ s, w (t s)) * L (xs i) (z ∘ t) =
      ∑ t : Fin M → Fin n, prodLaw w t * ((1 / (m : ℝ)) * ∑ i, L (xs i) (z ∘ t)) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold prodLaw; ring
  rw [hswap]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-! ### The oracle event -/

lemma probVec_nonempty {n : ℕ} (hn : 1 ≤ n) : ∃ w : Fin n → ℝ, ProbVec w := by
  refine ⟨fun _ => 1 / n, fun _ => by positivity, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

lemma oracle_event {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m M : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (hM : 1 ≤ M) {L : Z → (Fin M → Z) → ℝ} {Kk : Z → Z → ℝ}
    {BL Kmin Kmax lcov lKL eps : ℝ}
    (hL : Continuous (fun p : Z × (Fin M → Z) => L p.1 p.2)) (hLb : ∀ z t, 0 ≤ L z t ∧ L z t ≤ BL)
    (hK : Continuous (Function.uncurry Kk)) (hKmin : 0 < Kmin) (hKb : ∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax)
    (hlcov : 0 ≤ lcov) (hlKL : 0 ≤ lKL) (P₀ : Measure Z) [IsProbabilityMeasure P₀] (z : Fin n → Z)
    (X : Fin m → Ω → Z) (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P) (hXl : ∀ i, P.map (X i) = P₀)
    (wh : Ω → Fin n → ℝ) (hwh : ∀ ω, ProbVec (wh ω))
    (hopt : ∀ ω (w : Fin n → ℝ), ProbVec w →
      jIidEmp L Kk lcov lKL z (fun i => X i ω) (wh ω) ≤ jIidEmp L Kk lcov lKL z (fun i => X i ω) w + eps) :
    ∃ S : Set Ω, MeasurableSet S ∧ ENNReal.ofReal (1 - 1 / m) ≤ P S ∧ ∀ ω ∈ S,
      riskIid L Kk lcov P₀ (poolLaw z (wh ω)) ≤
        sInf ((fun w => riskIid L Kk lcov P₀ (poolLaw z w)) '' {w | ProbVec w}) + lKL * Real.log n + eps +
          2 * StatFormal.Wave24d.devBound BL lcov Kmin Kmax M n m (1 / m) := by
  have hm0 : 0 < m := by omega
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hδ0 : (0 : ℝ) < 1 / m := by positivity
  have hδ1 : (1 : ℝ) / m < 1 := by rw [div_lt_one (by linarith)]; linarith
  obtain ⟨S, hSm, hSP, hSsub⟩ := StatFormal.ICL.JointFull.joint_full Z Ω P P₀ n M m
    (fun t x => L x (z ∘ t)) (fun j x => Kk x (z j)) BL Kmin Kmax lcov (1 / m) X hn hM hm0 hδ0 hδ1 hlcov hKmin
    (fun t => (hL.comp (Continuous.prodMk continuous_id continuous_const)).measurable) (fun t x => hLb x _)
    (fun j => (hK.comp (Continuous.prodMk continuous_id continuous_const)).measurable) (fun j x => hKb x _)
    hXm hXi hXl
  refine ⟨S, hSm, hSP, fun ω hω => ?_⟩
  set dev := StatFormal.Wave24d.devBound BL lcov Kmin Kmax M n m (1 / m) with hdev
  set SV : Set (Fin n → ℝ) := {w | ProbVec w} with hSV
  have hne : SV.Nonempty := probVec_nonempty (by omega)
  -- `|J_m − J_pool| ≤ dev` on the simplex
  have hdevw : ∀ w ∈ SV, |jIidEmp L Kk lcov lKL z (fun i => X i ω) w - jPool L Kk lcov lKL P₀ z w| ≤ dev := by
    intro w hw
    rw [jIid_sub_jPool hM hL hLb hK hKmin hKb lcov lKL P₀ z _ hw]
    have := hSsub hω (prodLaw w) (prodLaw_probVec hw)
    simpa [hdev, StatFormal.Wave24d.devBound] using this
  -- lower bound of `J_pool`
  have hJpLow : ∀ w ∈ SV, -(lcov * Real.log Kmax) ≤ jPool L Kk lcov lKL P₀ z w := by
    intro w hw
    haveI := poolLaw_isProb z hw
    have := riskIid_ge hL hLb hK hKmin hKb hlcov P₀ (poolLaw z w)
    have := mul_nonneg hlKL (klUnif_nonneg hw)
    unfold jPool; linarith
  have hBdd : BddBelow ((jPool L Kk lcov lKL P₀ z) '' SV) := ⟨_, by rintro _ ⟨w, hw, rfl⟩; exact hJpLow w hw⟩
  have hJmLow : BddBelow ((fun w => jIidEmp L Kk lcov lKL z (fun i => X i ω) w) '' SV) := by
    refine ⟨-(lcov * Real.log Kmax) - dev, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hJpLow w hw
    have h2 := (abs_le.1 (hdevw w hw)).1
    linarith
  have hmin : jIidEmp L Kk lcov lKL z (fun i => X i ω) (wh ω) ≤
      sInf ((fun w => jIidEmp L Kk lcov lKL z (fun i => X i ω) w) '' SV) + eps := by
    have : jIidEmp L Kk lcov lKL z (fun i => X i ω) (wh ω) - eps ≤
        sInf ((fun w => jIidEmp L Kk lcov lKL z (fun i => X i ω) w) '' SV) := by
      refine le_csInf (hne.image _) ?_
      rintro _ ⟨w, hw, rfl⟩
      linarith [hopt ω w hw]
    linarith
  have horacle := StatFormal.ICL.Diag.oracle (Fin n → ℝ) SV (fun w => jIidEmp L Kk lcov lKL z (fun i => X i ω) w)
    (jPool L Kk lcov lKL P₀ z) dev eps (wh ω) (hwh ω) hdevw hBdd hmin
  -- from `J_pool` back to `R^iid`
  have hR : riskIid L Kk lcov P₀ (poolLaw z (wh ω)) ≤ jPool L Kk lcov lKL P₀ z (wh ω) := by
    have := mul_nonneg hlKL (klUnif_nonneg (hwh ω))
    unfold jPool; linarith
  have hinf : sInf ((jPool L Kk lcov lKL P₀ z) '' SV) ≤
      sInf ((fun w => riskIid L Kk lcov P₀ (poolLaw z w)) '' SV) + lKL * Real.log n := by
    have : sInf ((jPool L Kk lcov lKL P₀ z) '' SV) - lKL * Real.log n ≤
        sInf ((fun w => riskIid L Kk lcov P₀ (poolLaw z w)) '' SV) := by
      refine le_csInf (hne.image _) ?_
      rintro _ ⟨w, hw, rfl⟩
      have h1 : sInf ((jPool L Kk lcov lKL P₀ z) '' SV) ≤
          riskIid L Kk lcov P₀ (poolLaw z w) + lKL * klUnif n w :=
        csInf_le hBdd ⟨w, hw, rfl⟩
      have h2 : lKL * klUnif n w ≤ lKL * Real.log n := mul_le_mul_of_nonneg_left (klUnif_le_log hw) hlKL
      linarith
    linarith
  linarith

end StatFormal.Wave26b
