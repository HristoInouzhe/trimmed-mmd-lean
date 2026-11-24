import StatFormal.Wave30tz.RouteValid
import StatFormal.Lib.Alpha0Witness.KSMeas
import StatFormal.Lib.PaperRun.Fitting
import StatFormal.Wave31tr.Statements

/-!
# Wave 31tr, chunk M2: T17(c) `alpha0_gate`, the printed predictability step (untrusted route)

* `f̂_{0,b}` is jointly measurable in the sample and the point (`PaperRun.measurable_witness_apply` on the fitting sample) and a
  function of the batches before `b` (`PaperRun.fitSample_congr`); hence `(x, y) ↦ KS⁺(f̂_{0,b}(x, y))` is measurable
  (`Alpha0Witness.measurable_ksPlus`: a supremum over the rationals of `x ↦ P{f̂_{0,b}(x) > q}`, Fubini) and predictable.
* The gated fractions `λ′ = λ·1{KS⁺ ≤ α}` are therefore admissible, and coincide with `λ` where every gate is open.
* With `λ′`, wherever `λ′_k > 0` the gate is open, so `Δ_k ≤ KS⁺(f̂_{0,bat k}) ≤ α` (Lemma 7, `Wave30tz.monotone_sub_le_ksPlus`)
  and the predictable indicator `1{Δ_k ≤ α}` of the certified core `Wave30tz.core_ind` equals `1`: the wealth with `λ′` is the
  supermartingale wealth of `core_ind`, which reaches `1/δ` with probability at most `δ` (Ville).
* The certificate with `λ` agrees with the one with `λ′` on `{max_b KS⁺ ≤ α}`; subadditivity gives `δ + P(max_b KS⁺ > α)`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr.RouteAlpha0

open StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Betting StatFormal.Wave30tp
  StatFormal.Alpha0Witness

section Gate

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] {n m N : ℕ}

/-- `f̂_{0,b}` is jointly measurable in the sample and the point. -/
theorem measurable_alphaZeroFn {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (b : ℕ) :
    Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => alphaZeroFn φ lx ly b p.1.1 p.1.2 p.2 :=
  PaperRun.measurable_witness_apply hφ ((PaperRun.measurable_fitSample lx b).comp (measurable_fst.comp measurable_fst))
    ((PaperRun.measurable_fitSample ly b).comp (measurable_snd.comp measurable_fst)) measurable_const measurable_const
    measurable_snd

/-- `f̂_{0,b}` depends only on the batches before `b`. -/
theorem alphaZeroFn_congr (φ : 𝒳 → H) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (b : ℕ) {x x' : Fin n → 𝒳} {y y' : Fin m → 𝒳}
    (hx : ∀ i, lx i < b → x i = x' i) (hy : ∀ j, ly j < b → y j = y' j) :
    alphaZeroFn φ lx ly b x y = alphaZeroFn φ lx ly b x' y' := by
  unfold alphaZeroFn
  rw [PaperRun.fitSample_congr lx b hx, PaperRun.fitSample_congr ly b hy]

/-- `(x, y) ↦ KS⁺(f̂_{0,b}(x, y))` is measurable. -/
theorem measurable_ksPlus_alphaZeroFn (P Q : Measure 𝒳) [IsFiniteMeasure P] [IsFiniteMeasure Q] {φ : 𝒳 → H}
    (hφ : StronglyMeasurable φ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (b : ℕ) :
    Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => ksPlus P Q (alphaZeroFn φ lx ly b p.1 p.2) :=
  measurable_ksPlus P Q (F := fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => alphaZeroFn φ lx ly b p.1 p.2)
    (measurable_alphaZeroFn hφ lx ly b)

/-- The gated fraction of a pair `k < N`. -/
theorem ksGate_apply (P Q : Measure 𝒳) (φ : 𝒳 → H) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (α : ℝ)
    (lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ) (k : Fin N) (x : Fin n → 𝒳) (y : Fin m → 𝒳)
    (z : Fin k → ℝ) :
    ksGate P Q φ lx ly bat α lam k x y z =
      if ksPlus P Q (alphaZeroFn φ lx ly (bat k) x y) ≤ α then lam k x y z else 0 := by
  unfold ksGate
  rw [dif_pos k.isLt]

/-- Where every gate is open, the gated fractions are the original ones. -/
theorem ksGate_eq_of_forall (P Q : Measure 𝒳) (φ : 𝒳 → H) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (α : ℝ)
    (lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ) (x : Fin n → 𝒳) (y : Fin m → 𝒳)
    (hall : ∀ k : Fin N, ksPlus P Q (alphaZeroFn φ lx ly (bat k) x y) ≤ α) :
    (fun k => ksGate P Q φ lx ly bat α lam k x y) = fun k => lam k x y := by
  funext k z
  unfold ksGate
  by_cases hk : k < N
  · rw [dif_pos hk]
    have h := hall ⟨k, hk⟩
    simp [h]
  · rw [dif_neg hk]

end Gate

theorem alpha0_gate_route : Claims.alpha0_gate := by
  intro 𝒳 H _ _ _ _ _ φ κ P Q _ _ n m N lx ly bat A B α δ c g lam hφ _ hpair hα hδ0 hδ1 hc0 hc1 hg hlam hh
  obtain ⟨lam', hlam'def⟩ : ∃ l, l = ksGate P Q φ lx ly bat α lam := ⟨_, rfl⟩
  rw [← hlam'def]
  have hg' : IsBatchRule (U := Unit) lx ly bat (fun b _ => g b) := hg
  have hlamB : IsBatchBetRule (U := Unit) lx ly bat α c (fun k _ => lam k) := hlam
  have hKSm := fun b => measurable_ksPlus_alphaZeroFn P Q hφ lx ly b
  have hKSd : ∀ (b : ℕ) (x x' : Fin n → 𝒳) (y y' : Fin m → 𝒳), (∀ i, lx i < b → x i = x' i) →
      (∀ j, ly j < b → y j = y' j) → ksPlus P Q (alphaZeroFn φ lx ly b x y) = ksPlus P Q (alphaZeroFn φ lx ly b x' y') :=
    fun b x x' y y' hx hy => by rw [alphaZeroFn_congr φ lx ly b hx hy]
  -- the gated fractions are admissible
  have h1α : 0 < 1 + α := by linarith
  have hlam'B : IsBatchBetRule (U := Unit) lx ly bat α c (fun k _ => lam' k) := by
    intro k
    refine ⟨?_, fun u x y z => ?_, fun u x x' y y' hx hy => ?_⟩
    · have e : (fun p : (Unit × ((Fin n → 𝒳) × (Fin m → 𝒳))) × (Fin k → ℝ) => lam' k p.1.2.1 p.1.2.2 p.2) =
          fun p => if ksPlus P Q (alphaZeroFn φ lx ly (bat k) p.1.2.1 p.1.2.2) ≤ α then lam k p.1.2.1 p.1.2.2 p.2 else 0 :=
        funext fun p => by rw [hlam'def]; exact ksGate_apply P Q φ lx ly bat α lam k _ _ _
      change Measurable (fun p : (Unit × ((Fin n → 𝒳) × (Fin m → 𝒳))) × (Fin k → ℝ) => lam' k p.1.2.1 p.1.2.2 p.2)
      rw [e]
      exact Measurable.ite (measurableSet_le ((hKSm (bat k)).comp (measurable_snd.comp measurable_fst)) measurable_const)
        (hlamB k).1 measurable_const
    · change 0 ≤ lam' k x y z ∧ lam' k x y z ≤ c / (1 + α)
      rw [hlam'def, ksGate_apply]
      split_ifs
      · exact (hlamB k).2.1 () x y z
      · exact ⟨le_rfl, div_nonneg hc0.le h1α.le⟩
    · change lam' k x y = lam' k x' y'
      funext z
      have hl : lam k x y = lam k x' y' := (hlamB k).2.2 () x x' y y' hx hy
      rw [hlam'def, ksGate_apply, ksGate_apply, hKSd (bat k) x x' y y' hx hy, hl]
  -- agreement on `{max_b KS⁺ ≤ α}`
  have hagree : ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), (∀ k : Fin N, ksPlus P Q (alphaZeroFn φ lx ly (bat k) x y) ≤ α) →
      (∀ k : Fin N, fracAt lam' g bat A B x y k = fracAt lam g bat A B x y k) ∧
        (rejects lam' g bat A B α δ x y ↔ rejects lam g bat A B α δ x y) := by
    intro x y hall
    have he := ksGate_eq_of_forall P Q φ lx ly bat α lam x y hall
    rw [← hlam'def] at he
    refine ⟨fun k => ?_, ?_⟩
    · unfold fracAt
      exact congrFun (congrFun he k) _
    · have e1 : rejects lam' g bat A B α δ x y =
          betReject (fun k => lam' k x y) α δ (seqZ (U := Unit) (fun b _ => g b) bat A B () x y) := rfl
      have e2 : rejects lam g bat A B α δ x y =
          betReject (fun k => lam k x y) α δ (seqZ (U := Unit) (fun b _ => g b) bat A B () x y) := rfl
      rw [e1, e2, he]
  -- the gated certificate is valid: the core with the predictable indicator
  have hGm : ∀ k : Fin N, Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => g (bat k) p.1.1 p.1.2 p.2 := by
    intro k
    have hφ' : Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => (((), p.1), p.2) :=
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    exact (hg' k).1.comp hφ'
  have hLm : ∀ k : Fin N, Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × (Fin k → ℝ) => lam' k p.1.1 p.1.2 p.2 := by
    intro k
    have hφ' : Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × (Fin k → ℝ) => (((), p.1), p.2) :=
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    exact (hlam'B k).1.comp hφ'
  have hcore := core_ind (A := A) (B := B) P Q hpair hα hδ0 hc1 (fun b ω => g b ω.1 ω.2) hGm
    (fun k ω z => (hg' k).2.1 () ω.1 ω.2 z)
    (fun k => depOn_before (F := fun x y => g (bat k) x y) fun x x' y y' hx hy => (hg' k).2.2 () x x' y y' hx hy)
    (fun k ω => lam' k ω.1 ω.2) hLm (fun k ω z => (hlam'B k).2.1 () ω.1 ω.2 z)
    (fun k => depOn_before (F := fun x y => lam' k x y) fun x x' y y' hx hy => (hlam'B k).2.2 () x x' y y' hx hy)
  -- `Δ_k ≤ KS⁺(f̂_{0,bat k})` (Lemma 7)
  have hΔks : ∀ (k : Fin N) (ω : (Fin n → 𝒳) × (Fin m → 𝒳)),
      (∫ z, g (bat k) ω.1 ω.2 z ∂P) - (∫ z, g (bat k) ω.1 ω.2 z ∂Q) ≤ ksPlus P Q (alphaZeroFn φ lx ly (bat k) ω.1 ω.2) := by
    intro k ω
    obtain ⟨h, hmon, hI, hgeq⟩ := hh k ω.1 ω.2
    have hFk : Measurable fun z => alphaZeroFn φ lx ly (bat k) ω.1 ω.2 z := by
      have := (measurable_alphaZeroFn hφ lx ly (bat k)).comp (measurable_prodMk_left (x := ω))
      exact this
    rw [hgeq]
    exact monotone_sub_le_ksPlus P Q hFk hmon hI
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  have hgated : sampleLaw P Q n m {ω | rejects lam' g bat A B α δ ω.1 ω.2} ≤ ENNReal.ofReal δ := by
    unfold sampleLaw
    rw [← hμ]
    refine (measure_mono fun ω hω => ?_).trans ((ofReal_measureReal (measure_ne_top _ _)).symm.le.trans
      (ENNReal.ofReal_le_ofReal hcore))
    have hω' : ∃ t, t ≤ N ∧ 1 / δ ≤ wealth (fun k => lam' k ω.1 ω.2) α
        (fun k => pairZ (g (bat k) ω.1 ω.2) A B ω.1 ω.2 k) t := hω
    obtain ⟨t, ht, hw⟩ := hω'
    rw [Set.mem_ofPred_eq]
    refine ⟨t, ht, le_of_le_of_eq hw ?_⟩
    unfold wealth wealthP
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hks : ksPlus P Q (alphaZeroFn φ lx ly (bat k) ω.1 ω.2) ≤ α
    · have hk : (∫ z, g (bat k) ω.1 ω.2 z ∂P) - (∫ z, g (bat k) ω.1 ω.2 z ∂Q) ≤ α := (hΔks k ω).trans hks
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, hk, ite_true, one_mul]
    · have h0 : ∀ z, lam' k ω.1 ω.2 z = 0 := fun z => by
        rw [hlam'def, ksGate_apply, if_neg hks]
      simp only [h0, zero_mul]
  refine ⟨fun b => ⟨hKSm b, fun x x' y y' hx hy => hKSd b x x' y y' hx hy⟩, hlam'B, hagree, hgated, ?_⟩
  calc sampleLaw P Q n m {ω | rejects lam g bat A B α δ ω.1 ω.2}
      ≤ sampleLaw P Q n m ({ω | rejects lam' g bat A B α δ ω.1 ω.2} ∪
          {ω | ∃ k : Fin N, α < ksPlus P Q (alphaZeroFn φ lx ly (bat k) ω.1 ω.2)}) := by
        refine measure_mono fun ω hω => ?_
        by_cases hks : ∃ k : Fin N, α < ksPlus P Q (alphaZeroFn φ lx ly (bat k) ω.1 ω.2)
        · exact Or.inr hks
        · left
          push Not at hks
          exact (hagree ω.1 ω.2 hks).2.2 hω
    _ ≤ sampleLaw P Q n m {ω | rejects lam' g bat A B α δ ω.1 ω.2} +
          sampleLaw P Q n m {ω | ∃ k : Fin N, α < ksPlus P Q (alphaZeroFn φ lx ly (bat k) ω.1 ω.2)} :=
        measure_union_le _ _
    _ ≤ _ := by gcongr

end StatFormal.Wave31tr.RouteAlpha0
