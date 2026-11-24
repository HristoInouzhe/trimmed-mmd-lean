import StatFormal.Archive.Wave29i.RouteConsistBasic
import StatFormal.Archive.Wave11b.RouteSwor

/-!
# Route — ICL `cor:consistency`, the pool objects (untrusted)

For a pool `z` of distinct points and `w ∈ Δ^(M)`:
* `μ_w^{⊗M} = Σ_t Π_s w_{t_s} δ_{z∘t}`, `μ_w^{⊗M}(D_M) = 1 − p(w) > 0`, and
  `Π_{μ_w} = Σ_t Π°_w(t) δ_{z∘t}` with the ordered conditional Poisson law `Π°_w` (a probability vector);
* `G_{μ_w}(x) = Σ_t Π°_w(t) L(x; z∘t)`, `ρ_{μ_w} = Σ_j Π̄°_j K(·, z_j)` (the frozen `JointFull.cover`);
* with the frozen `swor_cps` (`Π_w` is `Π°_w` up to order, symmetric `L`): `G_i(w) = Σ_t Π°_w(t) L(z̃_i; z∘t)` and
  `π_l/M = Π̄°_l`, hence `J_m(w) − devFull(Π°_w) = R(μ_w) + λ_KL KL(w|u_n)`.
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
open StatFormal.Foundations.SworLaw

variable {Z : Type} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

namespace ConsistR

/-! ### The index laws -/

section Index
variable {n M : ℕ}

/-- The mass `Σ_t Π_s w_{t_s} 1{t injective}` of the injective index tuples. -/
def swoMass (w : Fin n → ℝ) (M : ℕ) : ℝ := ∑ t : Fin M → Fin n, iidLaw w M t * (if Function.Injective t then 1 else 0)

lemma sum_iidLaw {w : Fin n → ℝ} (hw : ∑ j, w j = 1) : ∑ t : Fin M → Fin n, iidLaw w M t = 1 := by
  unfold iidLaw
  rw [← Fintype.prod_sum (fun _ : Fin M => fun j => w j)]
  simp [hw]

lemma swoMass_eq {w : Fin n → ℝ} (hw : ∑ j, w j = 1) : swoMass w M = 1 - collision w M := by
  unfold swoMass collision
  have h := Finset.sum_filter_add_sum_filter_not univ (fun t : Fin M → Fin n => Function.Injective t) (iidLaw w M)
  rw [sum_iidLaw hw] at h
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  linarith

lemma iidLaw_nonneg {w : Fin n → ℝ} (hw : ∀ j, 0 ≤ w j) (t : Fin M → Fin n) : 0 ≤ iidLaw w M t :=
  Finset.prod_nonneg fun s _ => hw _

lemma exists_inj_pos {w : Fin n → ℝ} (hΔ : InDeltaM w M) :
    ∃ t : Fin M → Fin n, Function.Injective t ∧ ∀ s, 0 < w (t s) := by
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hΔ.2.2
  refine ⟨fun s => T.orderEmbOfFin hTc s, (T.orderEmbOfFin hTc).injective, fun s => ?_⟩
  have hmem := hT (T.orderEmbOfFin_mem hTc s)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact lt_of_le_of_ne (hΔ.1 _) (Ne.symm hmem)

lemma swoMass_pos {w : Fin n → ℝ} (hΔ : InDeltaM w M) : 0 < swoMass w M := by
  obtain ⟨t, ht, hpos⟩ := exists_inj_pos hΔ
  unfold swoMass
  have hterm : 0 < iidLaw w M t * (if Function.Injective t then 1 else 0) := by
    rw [if_pos ht, mul_one]; exact Finset.prod_pos fun s _ => hpos s
  refine lt_of_lt_of_le hterm (Finset.single_le_sum (f := fun t => iidLaw w M t * (if Function.Injective t then 1 else 0))
    (fun t' _ => mul_nonneg (iidLaw_nonneg hΔ.1 t') (by split_ifs <;> norm_num)) (Finset.mem_univ t))

lemma collision_lt_one {w : Fin n → ℝ} (hΔ : InDeltaM w M) : collision w M < 1 := by
  have := swoMass_pos hΔ; rw [swoMass_eq hΔ.2.1] at this; linarith

lemma ordLaw_nonneg {w : Fin n → ℝ} (hΔ : InDeltaM w M) (t : Fin M → Fin n) : 0 ≤ consistOrdLaw M w t := by
  unfold consistOrdLaw
  refine div_nonneg (mul_nonneg (iidLaw_nonneg hΔ.1 t) (by split_ifs <;> norm_num)) ?_
  have := collision_lt_one hΔ; linarith

lemma ordLaw_eq {w : Fin n → ℝ} (hΔ : InDeltaM w M) (t : Fin M → Fin n) :
    consistOrdLaw M w t = iidLaw w M t * (if Function.Injective t then 1 else 0) / swoMass w M := by
  rw [swoMass_eq hΔ.2.1]; rfl

lemma ordLaw_probVec {w : Fin n → ℝ} (hΔ : InDeltaM w M) : ProbVec (consistOrdLaw M w) := by
  refine ⟨ordLaw_nonneg hΔ, ?_⟩
  simp_rw [ordLaw_eq hΔ]
  rw [← Finset.sum_div]
  exact div_self (swoMass_pos hΔ).ne'

lemma ordLaw_of_not_inj {w : Fin n → ℝ} {t : Fin M → Fin n} (ht : ¬ Function.Injective t) : consistOrdLaw M w t = 0 := by
  unfold consistOrdLaw; rw [if_neg ht]; simp

lemma swoExp_eq_ordLaw (w : Fin n → ℝ) (f : (Fin M → Fin n) → ℝ) :
    swoExp w M f = ∑ t, consistOrdLaw M w t * f t := by
  unfold swoExp consistOrdLaw
  rw [Finset.sum_filter, Finset.sum_div]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> ring

end Index

/-! ### The pool context law -/

section Pool
variable {n M : ℕ}

lemma poolLaw_eq_sum (z : Fin n → Z) (w : Fin n → ℝ) :
    poolLaw z w = ∑ j, ENNReal.ofReal (w j) • Measure.dirac (z j) := rfl

lemma pi_poolLaw_eq (z : Fin n → Z) (w : Fin n → ℝ) :
    Measure.pi (fun _ : Fin M => poolLaw z w) =
      ∑ t : Fin M → Fin n, (∏ s, ENNReal.ofReal (w (t s))) • Measure.dirac (z ∘ t) :=
  pi_sum_dirac _ (fun _ => ENNReal.ofReal_ne_top) z

lemma indicator_inj_comp {z : Fin n → Z} (hz : Function.Injective z) (t : Fin M → Fin n) :
    {t' : Fin M → Z | Function.Injective t'}.indicator (1 : (Fin M → Z) → ℝ≥0∞) (z ∘ t) =
      ENNReal.ofReal (if Function.Injective t then 1 else 0) := by
  by_cases ht : Function.Injective t
  · rw [indicator_of_mem (show z ∘ t ∈ {t' : Fin M → Z | Function.Injective t'} from hz.comp ht), if_pos ht]; simp
  · rw [indicator_of_notMem (show z ∘ t ∉ {t' : Fin M → Z | Function.Injective t'} from
      fun h => ht (Function.Injective.of_comp h)), if_neg ht]; simp

lemma pi_term_eq {z : Fin n → Z} (hz : Function.Injective z) {w : Fin n → ℝ} (hw : ∀ j, 0 ≤ w j)
    (t : Fin M → Fin n) :
    (∏ s, ENNReal.ofReal (w (t s))) * {t' : Fin M → Z | Function.Injective t'}.indicator 1 (z ∘ t) =
      ENNReal.ofReal (iidLaw w M t * (if Function.Injective t then 1 else 0)) := by
  rw [indicator_inj_comp hz, ENNReal.ofReal_mul (iidLaw_nonneg hw t), iidLaw,
    ENNReal.ofReal_prod_of_nonneg fun s _ => hw _]

lemma pi_poolLaw_distinct {z : Fin n → Z} (hz : Function.Injective z) {w : Fin n → ℝ} (hw : ∀ j, 0 ≤ w j) :
    Measure.pi (fun _ : Fin M => poolLaw z w) (distinctSet M) = ENNReal.ofReal (swoMass w M) := by
  rw [pi_poolLaw_eq, distinctSet_eq, sum_dirac_apply _ _ (measurableSet_injective M)]
  simp_rw [pi_term_eq hz hw]
  unfold swoMass
  rw [ENNReal.ofReal_sum_of_nonneg fun t _ => mul_nonneg (iidLaw_nonneg hw t) (by split_ifs <;> norm_num)]

/-- `Π_{μ_w} = Σ_t Π°_w(t) δ_{z∘t}` for a distinct pool and `w ∈ Δ^(M)`. -/
lemma ctxLaw_poolLaw {z : Fin n → Z} (hz : Function.Injective z) {w : Fin n → ℝ} (hΔ : InDeltaM w M) :
    ctxLaw (poolLaw z w) M = ∑ t : Fin M → Fin n, ENNReal.ofReal (consistOrdLaw M w t) • Measure.dirac (z ∘ t) := by
  rw [ctxLaw_eq, pi_poolLaw_eq, cond_sum_dirac _ _ (measurableSet_injective M)]
  simp_rw [pi_term_eq hz hΔ.1]
  rw [← ENNReal.ofReal_sum_of_nonneg fun t _ => mul_nonneg (iidLaw_nonneg hΔ.1 t) (by split_ifs <;> norm_num)]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  rw [ordLaw_eq hΔ, ENNReal.ofReal_div_of_pos (swoMass_pos hΔ), div_eq_mul_inv, mul_comm]
  rfl

lemma integral_ctxLaw_pool {z : Fin n → Z} (hz : Function.Injective z) {w : Fin n → ℝ} (hΔ : InDeltaM w M)
    (f : (Fin M → Z) → ℝ) : ∫ t, f t ∂(ctxLaw (poolLaw z w) M) = ∑ t, consistOrdLaw M w t * f (z ∘ t) := by
  rw [ctxLaw_poolLaw hz hΔ, integral_sum_dirac _ (fun _ => ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ENNReal.toReal_ofReal (ordLaw_nonneg hΔ t)]

lemma consistG_poolLaw {L : Z → (Fin M → Z) → ℝ} {z : Fin n → Z} (hz : Function.Injective z) {w : Fin n → ℝ}
    (hΔ : InDeltaM w M) (x : Z) : consistG L (poolLaw z w) x = ∑ t, consistOrdLaw M w t * L x (z ∘ t) :=
  integral_ctxLaw_pool hz hΔ _

lemma sum_slot_eq {Kx : Fin n → ℝ} (t : Fin M → Fin n) :
    ∑ s, Kx (t s) = ∑ j, ((univ.filter fun s => t s = j).card : ℝ) * Kx j := by
  rw [← Finset.sum_fiberwise univ t (fun s => Kx (t s))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => Kx j) fun s hs => by rw [(Finset.mem_filter.1 hs).2]]
  rw [Finset.sum_const, nsmul_eq_mul]

lemma rhoC_poolLaw {Kk : Z → Z → ℝ} (hK : Continuous (Function.uncurry Kk)) {z : Fin n → Z}
    (hz : Function.Injective z) {w : Fin n → ℝ} (hΔ : InDeltaM w M) (x : Z) :
    rhoC Kk (consistMarg (poolLaw z w) M) x =
      StatFormal.ICL.JointFull.cover (fun j x => Kk x (z j)) (consistOrdLaw M w) x := by
  haveI : IsFiniteMeasure (poolLaw z w) := StatFormal.Wave26b.poolLaw_isFinite z w
  unfold rhoC
  rw [integral_consistMarg _ M (g := fun z' => Kk x z') (hK.comp (Continuous.prodMk continuous_const continuous_id))]
  simp_rw [integral_ctxLaw_pool hz hΔ]
  unfold StatFormal.ICL.JointFull.cover StatFormal.ICL.JointFull.oneSlot
  rw [Finset.sum_comm]
  simp_rw [Function.comp_apply, ← Finset.mul_sum, sum_slot_eq (Kx := fun j => Kk x (z j))]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
  ring

/-- Every `μ_w`, `w ∈ Δ^(M)`, on a distinct pool in `supp P₀` is admissible. -/
lemma admissible_poolLaw (P₀ : Measure Z) {z : Fin n → Z} (hz : Function.Injective z) (hzS : ∀ i, z i ∈ P₀.support)
    {w : Fin n → ℝ} (hΔ : InDeltaM w M) : Admissible P₀ M (poolLaw z w) := by
  refine ⟨StatFormal.Wave26b.poolLaw_isProb z ⟨hΔ.1, hΔ.2.1⟩, StatFormal.Wave26b.poolLaw_carried z hzS w, ?_⟩
  rw [pi_poolLaw_distinct hz hΔ.1]
  exact ENNReal.ofReal_pos.2 (swoMass_pos hΔ)

end Pool

end ConsistR

end StatFormal.Wave29i
