import StatFormal.Wave30tz.RouteValid
import StatFormal.Wave30tz.RouteUpper
import StatFormal.Wave31tj.RouteGrid

set_option linter.style.longLine false

/-!
# Betting on one fixed function, given batch 0 (library)

Library component (untrusted). The ramp of every pair is one fixed measurable function `f : 𝒳 → [0,1]` (for the certificate of §8,
`f = F(batch 0)` once batch 0 is fixed); the fractions are any admissible rule evaluated at the sample with batch 0 frozen at
`(x₀, y₀)` (`Wave30tv.withBatchZero`).

* `rejects_congr_ramp`: the certificate depends on the ramps only through their values at the pairs' batches;
* `pairZ_withBatchZero`: the pair statistics do not see batch 0 (every block lies in a batch `≥ 1`);
* `level_fixed_cond`: **the level bound for a fixed function**: if `Δ = E_P f − E_Q f ≤ α`, `α ≥ 0`, the cap is `c ≤ 1`, then for
  every value `(x₀, y₀)` of batch 0, `P(reject H_{0,α}) ≤ δ` — with no assumption on `TV(P,Q)`. This is the positive-fraction
  supermartingale of the certified `Wave30tz.core_ind` (the predictable indicator `1{Δ_k ≤ α}` is identically `1`, `Δ_k = Δ`), with
  the fractions frozen at batch 0 as in the certified `Wave30tv.thm_betting_cond` route.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.FnCert

open StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Betting StatFormal.Wave30tp

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {n m N : ℕ}
  {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)} {B : Fin N → Finset (Fin m)}

omit [MeasurableSpace 𝒳] in
/-- The certificate depends on the ramps only through their values at the batches of the pairs. -/
theorem rejects_congr_ramp {lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}
    {g g' : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ} {α δ : ℝ} {x : Fin n → 𝒳} {y : Fin m → 𝒳}
    (h : ∀ k : Fin N, g (bat k) x y = g' (bat k) x y) :
    rejects lam g bat A B α δ x y ↔ rejects lam g' bat A B α δ x y := by
  have e : seqZ (U := Unit) (fun b _ => g b) bat A B () x y = seqZ (U := Unit) (fun b _ => g' b) bat A B () x y := by
    funext k
    show pairZ (g (bat k) x y) A B x y k = pairZ (g' (bat k) x y) A B x y k
    rw [h k]
  change betReject (fun k => lam k x y) α δ (seqZ (U := Unit) (fun b _ => g b) bat A B () x y) ↔
    betReject (fun k => lam k x y) α δ (seqZ (U := Unit) (fun b _ => g' b) bat A B () x y)
  rw [e]

omit [MeasurableSpace 𝒳] in
/-- The pair statistics do not see batch 0: every block lies in the batch `bat k ≥ 1` of its pair. -/
theorem pairZ_withBatchZero (hpair : IsBatchPairing lx ly bat A B) (f : 𝒳 → ℝ) (k : Fin N) (x₀ x : Fin n → 𝒳)
    (y₀ y : Fin m → 𝒳) : pairZ f A B (withBatchZero lx x₀ x) (withBatchZero ly y₀ y) k = pairZ f A B x y k := by
  refine pairZ_congr k (fun i hi => withBatchZero_of_ne ?_) (fun j hj => withBatchZero_of_ne ?_)
  · rw [hpair.2.2.2.1 k i hi]; have := hpair.2.2.1 k; omega
  · rw [hpair.2.2.2.2 k j hj]; have := hpair.2.2.1 k; omega

/-- **Level of the certificate for one fixed function, given batch 0**: `E_P f − E_Q f ≤ α` (any pair `(P,Q)`) bounds the rejection
probability by `δ` at every value `(x₀, y₀)` of batch 0. -/
theorem level_fixed_cond (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hpair : IsBatchPairing lx ly bat A B) {α δ c : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) (hc1 : c ≤ 1)
    {f : 𝒳 → ℝ} (hf : Measurable f) (hf01 : ∀ z, f z ∈ Icc (0 : ℝ) 1) (hΔ : (∫ z, f z ∂P) - (∫ z, f z ∂Q) ≤ α)
    {lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ} (hlam : IsFracRule lx ly bat α c lam)
    (x₀ : Fin n → 𝒳) (y₀ : Fin m → 𝒳) :
    sampleLaw P Q n m {ω | rejects lam (fun _ _ _ => f) bat A B α δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)} ≤
      ENNReal.ofReal δ := by
  have hlamB : IsBatchBetRule (U := Unit) lx ly bat α c (fun k _ => lam k) := hlam
  have hφ : Measurable fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => (withBatchZero lx x₀ ω.1, withBatchZero ly y₀ ω.2) :=
    ((measurable_withBatchZero lx x₀).comp measurable_fst).prodMk ((measurable_withBatchZero ly y₀).comp measurable_snd)
  have hψ : ∀ k : ℕ, Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × (Fin k → ℝ) =>
      ((((), (withBatchZero lx x₀ p.1.1, withBatchZero ly y₀ p.1.2)) : Unit × ((Fin n → 𝒳) × (Fin m → 𝒳))), p.2) :=
    fun k => (measurable_const.prodMk (hφ.comp measurable_fst)).prodMk measurable_snd
  set G : ℕ → (Fin n → 𝒳) × (Fin m → 𝒳) → 𝒳 → ℝ := fun _ _ => f with hG
  set Lam : (k : ℕ) → (Fin n → 𝒳) × (Fin m → 𝒳) → (Fin k → ℝ) → ℝ :=
    fun k ω => lam k (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2) with hLam
  have hcore := core_ind (A := A) (B := B) P Q hpair hα hδ hc1 G (fun _ => hf.comp measurable_snd)
    (fun _ _ z => hf01 z) (fun _ _ _ _ => rfl) Lam
    (fun k => (hlamB k).1.comp (hψ k))
    (fun k ω z => (hlamB k).2.1 () _ _ z)
    (fun k ω ω' hω => (hlamB k).2.2 () _ _ _ _ (withBatchZero_agree fun i hi => hω (Sum.inl i) hi)
      (withBatchZero_agree fun j hj => hω (Sum.inr j) hj))
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  unfold sampleLaw
  rw [← hμ]
  refine (measure_mono fun ω hω => ?_).trans ((ofReal_measureReal (measure_ne_top _ _)).symm.le.trans
    (ENNReal.ofReal_le_ofReal hcore))
  have hω' : ∃ t, t ≤ N ∧ 1 / δ ≤ wealth (fun k => lam k (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)) α
      (fun k => pairZ f A B (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2) k) t := hω
  obtain ⟨t, ht, hw⟩ := hω'
  rw [Set.mem_ofPred_eq]
  refine ⟨t, ht, le_of_le_of_eq hw ?_⟩
  unfold wealth wealthP
  refine Finset.prod_congr rfl fun k _ => ?_
  have hz : (fun i => pairZ f A B (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2) i) =
      fun i => pairZ (G (bat i) ω) A B ω.1 ω.2 i := funext fun i => pairZ_withBatchZero hpair f i x₀ ω.1 y₀ ω.2
  simp only [hz, hLam, hG, Set.indicator_apply, Set.mem_ofPred_eq, hΔ, ite_true, one_mul]

end StatFormal.FnCert
