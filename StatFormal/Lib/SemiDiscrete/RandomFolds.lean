import StatFormal.Lib.SemiDiscrete.HeldOut
import StatFormal.Archive.RobustEquality.Coverage.Proofs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Bases

/-!
# Semi-discrete entropic OT: `thm:coverage` with random folds (unconditional form)

Data `X_1, …, X_N` i.i.d. `P` (`Measure.pi`), a fixed fold partition (`fold`, enumerations `e v`),
fold `v` = the coordinates in block `v` (weights `1/n_v`, costs `c(X_{e v j}, ·)`), held-out sample
= the remaining coordinates `{i // ¬ fold i = v}` (empirical measure `P̂_{−v}`, `empOn`), and
`ρ̂_v = OT_ε(P̂_v, P̂_{−v}) + B_c √(log(V/a)/(2 m_v))` (`rhoHat`).

**No measurable selection is needed.** Instead of a measurable choice of the canonical potential, we
use `Θ(Q) = sup_n J_Q(d_n)` over a fixed countable dense sequence `d_n` of `ℝ^k`
(`Theta_eq_iSup_dseq`, from strong duality and continuity of `J_Q`). For a jointly measurable
cost, each `J_Q(d_n)` is measurable in the atoms (and in the held-out sample when `Q = P̂_{−v}`), so
`OT_ε(P̂_v, P)` and `OT_ε(P̂_v, P̂_{−v})` are measurable functions of the data, and so is the
per-fold event (`measurableSet_cov`). The conditional bound (`coverage_fold_fintype`) then
integrates over the fold coordinates by Fubini (`prod_coverage`, `fold_coverage_random`).

Hypotheses beyond the per-fold setting: `c : K → K → ℝ` jointly measurable
(`Measurable (uncurry c)`)
and bounded, oscillation `c x y − c x y' ≤ B_c`, every fold has a nonempty complement. No topology
on `K`, no continuity of `c`, no compactness.

Main results:
* `fold_coverage_random`: the per-fold event is measurable and has `P^N`-probability `≥ 1 − α`;
* `coverage_random_folds` (`thm:coverage`): `P^N[OT_ε(P̂, P) ≤ Σ_v w_v ρ̂_v] ≥ 1 − a`.
-/

noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal
open StatFormal.RobustEquality.Semidual

namespace StatFormal.Foundations.SemiDiscrete

/-! ### `Θ` as a countable supremum -/

/-- A fixed countable dense sequence in `ℝ^k`. -/
abbrev dseq (k : ℕ) : ℕ → (Fin k → ℝ) := TopologicalSpace.denseSeq (Fin k → ℝ)

section DenseSup

variable {K : Type} [MeasurableSpace K] {k : ℕ} {ε B : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ}

theorem Theta_eq_iSup_dseq (h : SDHyp ε a c B) (Q : Measure K) [IsProbabilityMeasure Q] :
    Theta ε a c Q = ⨆ n, (Jdual ε a c Q (dseq k n) : EReal) := by
  refine le_antisymm ?_ (iSup_le fun n => Jdual_le_Theta' h Q _)
  obtain ⟨fs, hmax⟩ := exists_max_Jdual h Q
  rw [Theta_eq_Jdual' h Q hmax]
  set M := ⨆ n, (Jdual ε a c Q (dseq k n) : EReal)
  have hC : IsClosed {f : Fin k → ℝ | (Jdual ε a c Q f : EReal) ≤ M} :=
    isClosed_le (continuous_coe_real_ereal.comp (continuous_Jdual h)) continuous_const
  have hsub : Set.range (dseq k) ⊆ {f | (Jdual ε a c Q f : EReal) ≤ M} := by
    rintro _ ⟨n, rfl⟩
    exact le_iSup (fun n => (Jdual ε a c Q (dseq k n) : EReal)) n
  have := hC.closure_subset_iff.mpr hsub
  rw [(TopologicalSpace.denseRange_denseSeq _).closure_range] at this
  exact this (Set.mem_univ fs)

end DenseSup

/-! ### Measurability in the atoms and in the held-out sample -/

section Param

variable {K Z : Type} [MeasurableSpace K] [MeasurableSpace Z] {k : ℕ} {ε B : ℝ} {a : Fin k → ℝ}
  {C : Z → Fin k → K → ℝ}

lemma measurable_gsoft_param (hC : ∀ i, Measurable fun p : Z × K => C p.1 i p.2)
    (f : Fin k → ℝ) : Measurable fun p : Z × K => gsoft ε a f (C p.1) p.2 := by
  unfold gsoft
  refine Measurable.const_mul (Measurable.log ?_) _
  exact Finset.measurable_sum _ fun i _ =>
    ((((hC i).const_sub (f i)).div_const ε).exp).const_mul (a i)

lemma measurable_Jdual_param (hC : ∀ i, Measurable fun p : Z × K => C p.1 i p.2)
    (Q : Measure K) [IsFiniteMeasure Q] (f : Fin k → ℝ) :
    Measurable fun z => Jdual ε a (C z) Q f := by
  unfold Jdual
  exact measurable_const.add
    ((measurable_gsoft_param (ε := ε) (a := a) hC f).stronglyMeasurable.integral_prod_right'
      (ν := Q)).measurable

lemma measurable_Jdual_empOn {ι : Type} [Fintype ι] [Nonempty ι]
    (hC : ∀ i, Measurable fun p : Z × K => C p.1 i p.2) (hz : ∀ z, SDHyp ε a (C z) B)
    (f : Fin k → ℝ) : Measurable fun p : Z × (ι → K) => Jdual ε a (C p.1) (empOn p.2) f := by
  have hfun : (fun p : Z × (ι → K) => Jdual ε a (C p.1) (empOn p.2) f) = fun p =>
      ∑ i, a i * f i + (1 / (Fintype.card ι : ℝ)) * ∑ j, gsoft ε a f (C p.1) (p.2 j) := by
    funext p
    unfold Jdual
    rw [integral_empOn p.2 ((hz p.1).measurable_gsoft f) ((hz p.1).abs_gsoft_le f)]
  have hm : Measurable fun p : Z × (ι → K) =>
      ∑ i, a i * f i + (1 / (Fintype.card ι : ℝ)) * ∑ j, gsoft ε a f (C p.1) (p.2 j) := by
    refine Measurable.const_add (Measurable.const_mul ?_ _) _
    refine Finset.measurable_sum _ fun j _ => ?_
    have h1 := measurable_gsoft_param (ε := ε) (a := a) hC f
    have h2 : Measurable fun p : Z × (ι → K) => (p.1, p.2 j) :=
      measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)
    exact h1.comp (f := fun p : Z × (ι → K) => (p.1, p.2 j)) h2
  rw [hfun]
  exact hm

lemma measurable_Theta_param (hC : ∀ i, Measurable fun p : Z × K => C p.1 i p.2)
    (hz : ∀ z, SDHyp ε a (C z) B) (Q : Measure K) [IsProbabilityMeasure Q] :
    Measurable fun z => Theta ε a (C z) Q := by
  have hfun : (fun z => Theta ε a (C z) Q) =
      fun z => ⨆ n, (Jdual ε a (C z) Q (dseq k n) : EReal) :=
    funext fun z => Theta_eq_iSup_dseq (hz z) Q
  rw [hfun]
  exact Measurable.iSup fun n =>
    measurable_coe_real_ereal.comp (measurable_Jdual_param (ε := ε) (a := a) hC Q _)

lemma measurable_Theta_empOn {ι : Type} [Fintype ι] [Nonempty ι]
    (hC : ∀ i, Measurable fun p : Z × K => C p.1 i p.2) (hz : ∀ z, SDHyp ε a (C z) B) :
    Measurable fun p : Z × (ι → K) => Theta ε a (C p.1) (empOn p.2) := by
  have hfun : (fun p : Z × (ι → K) => Theta ε a (C p.1) (empOn p.2)) =
      fun p => ⨆ n, (Jdual ε a (C p.1) (empOn p.2) (dseq k n) : EReal) := by
    funext p
    have := isProb_empOn p.2
    exact Theta_eq_iSup_dseq (hz p.1) _
  rw [hfun]
  exact Measurable.iSup fun n =>
    measurable_coe_real_ereal.comp (measurable_Jdual_empOn (ι := ι) hC hz _)

/-- The per-fold coverage event is measurable jointly in the atoms and the held-out sample. -/
theorem measurableSet_cov {ι : Type} [Fintype ι] [Nonempty ι]
    (hC : ∀ i, Measurable fun p : Z × K => C p.1 i p.2) (hz : ∀ z, SDHyp ε a (C z) B)
    (P : Measure K) [IsProbabilityMeasure P] (t : ℝ) :
    MeasurableSet {p : Z × (ι → K) |
      Theta ε a (C p.1) P ≤ Theta ε a (C p.1) (empOn p.2) + (t : EReal)} :=
  measurableSet_le ((measurable_Theta_param hC hz P).comp measurable_fst)
    ((measurable_Theta_empOn hC hz).add_const _)

/-- **Fubini step**: if the atoms are drawn from any law `μ_Z` independently of the i.i.d. held-out
sample, the coverage event has probability at least `1 − α`. -/
theorem prod_coverage {ι : Type} [Fintype ι] [Nonempty ι] (μZ : Measure Z)
    [IsProbabilityMeasure μZ] (P : Measure K) [IsProbabilityMeasure P]
    (hC : ∀ i, Measurable fun p : Z × K => C p.1 i p.2) (hz : ∀ z, SDHyp ε a (C z) B)
    {Bc α : ℝ} (hBc : 0 < Bc) (hosc : ∀ z i y y', C z i y - C z i y' ≤ Bc) (hα0 : 0 < α)
    (hα1 : α ≤ 1) :
    ENNReal.ofReal (1 - α) ≤ (μZ.prod (Measure.pi fun _ : ι => P))
      {p : Z × (ι → K) | Theta ε a (C p.1) P ≤ Theta ε a (C p.1) (empOn p.2) +
        ((Bc * √(Real.log (1 / α) / (2 * Fintype.card ι)) : ℝ) : EReal)} := by
  rw [Measure.prod_apply (measurableSet_cov hC hz P _)]
  have hne : Nonempty K := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    have h1 : P Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr hK, measure_empty] at h1
    exact zero_ne_one h1
  calc ENNReal.ofReal (1 - α) = ∫⁻ _z, ENNReal.ofReal (1 - α) ∂μZ := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := lintegral_mono fun z => by
        have hlo : ∀ i, ∃ lo, ∀ y, C z i y ∈ Set.Icc lo (lo + Bc) := fun i =>
          exists_Icc_of_osc (hosc z i)
        choose lo hlo using hlo
        have hind : iIndepFun (fun (j : ι) (w : ι → K) => w j) (Measure.pi fun _ : ι => P) :=
          iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
        exact coverage_fold_fintype (hz z).hε (hz z).ha (hz z).hsum (hz z).hc hBc hlo P
          (Measure.pi fun _ : ι => P) (fun j w => w j) (fun j => measurable_pi_apply j) hind
          (fun j => (measurePreserving_eval (fun _ : ι => P) j).map_eq) hα0 hα1

end Param

/-! ### Random folds -/

section Folds

variable {K : Type} [MeasurableSpace K] {N V : ℕ} {fold : Fin N → Fin V} {n : Fin V → ℕ}

/-- `ρ̂_v(X) = OT_ε(P̂_v, P̂_{−v}) + B_c √(log(V/a)/(2 m_v))` (the `OT_ε` value is finite). -/
def rhoHat (ε : ℝ) (c : K → K → ℝ) (e : ∀ v, Fin (n v) ≃ {i // fold i = v}) (Bc a : ℝ)
    (v : Fin V) (X : Fin N → K) : ℝ :=
  (Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j => c (X (e v j)))
      (empOn fun i : {i // ¬ fold i = v} => X i)).toReal +
    Bc * √(Real.log (V / a) / (2 * Fintype.card {i // ¬ fold i = v}))

lemma sdhyp_fold_uniform {ε B : ℝ} (hε : 0 < ε) {c : K → K → ℝ}
    (hcm : Measurable (Function.uncurry c)) (hB : ∀ x y, |c x y| ≤ B)
    (e : ∀ v, Fin (n v) ≃ {i // fold i = v})
    (hsurj : Function.Surjective fold) (v : Fin V) (u : {i // fold i = v} → K) :
    SDHyp ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j y => c (u (e v j)) y) B := by
  have hn : (0 : ℝ) < n v := by
    exact_mod_cast StatFormal.RobustEquality.Coverage.n_pos e hsurj v
  refine ⟨hε, fun _ => by positivity, ?_, fun j => ?_, fun j y => hB _ _⟩
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  · exact hcm.comp (measurable_const.prodMk measurable_id)

/-- **Per-fold coverage with random folds** (unconditional): the event
`OT_ε(P̂_v, P) ≤ OT_ε(P̂_v, P̂_{−v}) + B_c √(log(1/α)/(2 m_v))` is measurable in the data and has
`P^N`-probability at least `1 − α`. -/
theorem fold_coverage_random (P : Measure K) [IsProbabilityMeasure P]
    (e : ∀ v, Fin (n v) ≃ {i // fold i = v}) (hsurj : Function.Surjective fold) (v : Fin V)
    [Nonempty {i // ¬ fold i = v}] {c : K → K → ℝ} (hcm : Measurable (Function.uncurry c))
    {B : ℝ} (hB : ∀ x y, |c x y| ≤ B) {Bc ε α : ℝ} (hε : 0 < ε) (hBc : 0 < Bc)
    (hosc : ∀ x y y', c x y - c x y' ≤ Bc) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    MeasurableSet {X : Fin N → K |
        Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j => c (X (e v j))) P ≤
          Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j => c (X (e v j)))
            (empOn fun i : {i // ¬ fold i = v} => X i) +
          ((Bc * √(Real.log (1 / α) / (2 * Fintype.card {i // ¬ fold i = v})) : ℝ) : EReal)} ∧
      ENNReal.ofReal (1 - α) ≤ Measure.pi (fun _ : Fin N => P) {X : Fin N → K |
        Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j => c (X (e v j))) P ≤
          Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j => c (X (e v j)))
            (empOn fun i : {i // ¬ fold i = v} => X i) +
          ((Bc * √(Real.log (1 / α) / (2 * Fintype.card {i // ¬ fold i = v})) : ℝ) : EReal)} := by
  set φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => K) (fun i => fold i = v)
  set C : ({i // fold i = v} → K) → Fin (n v) → K → ℝ := fun u j y => c (u (e v j)) y
  have hC : ∀ j, Measurable fun p : ({i // fold i = v} → K) × K => C p.1 j p.2 := fun j =>
    hcm.comp (f := fun p : ({i // fold i = v} → K) × K => (p.1 (e v j), p.2))
      (((measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd)
  have hz : ∀ u, SDHyp ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (C u) B :=
    sdhyp_fold_uniform hε hcm hB e hsurj v
  have hS := measurableSet_cov (ι := {i // ¬ fold i = v}) hC hz P
    (Bc * √(Real.log (1 / α) / (2 * Fintype.card {i // ¬ fold i = v})))
  set S := {p : ({i // fold i = v} → K) × ({i // ¬ fold i = v} → K) |
      Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (C p.1) P ≤
        Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (C p.1) (empOn p.2) +
        ((Bc * √(Real.log (1 / α) / (2 * Fintype.card {i // ¬ fold i = v})) : ℝ) : EReal)}
  have hpre : {X : Fin N → K |
        Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j => c (X (e v j))) P ≤
          Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j => c (X (e v j)))
            (empOn fun i : {i // ¬ fold i = v} => X i) +
          ((Bc * √(Real.log (1 / α) / (2 * Fintype.card {i // ¬ fold i = v})) : ℝ) : EReal)} =
      φ ⁻¹' S := rfl
  rw [hpre]
  refine ⟨φ.measurable hS, ?_⟩
  rw [(measurePreserving_piEquivPiSubtypeProd (fun _ : Fin N => P)
    (fun i => fold i = v)).measure_preimage hS.nullMeasurableSet]
  exact prod_coverage (Measure.pi fun _ : {i // fold i = v} => P) P hC hz hBc
    (fun u j y y' => hosc _ y y') hα0 hα1

/-- **`thm:coverage` with random folds**: for `X_1, …, X_N` i.i.d. `P`,
`P^N[OT_ε(P̂, P) ≤ Σ_v (n_v/N) ρ̂_v] ≥ 1 − a`, with
`ρ̂_v = OT_ε(P̂_v, P̂_{−v}) + B_c √(log(V/a)/(2 m_v))` (`rhoHat`). -/
theorem coverage_random_folds (P : Measure K) [IsProbabilityMeasure P]
    (e : ∀ v, Fin (n v) ≃ {i // fold i = v}) (hsurj : Function.Surjective fold)
    (hheld : ∀ v, ∃ i, ¬ fold i = v) {c : K → K → ℝ} (hcm : Measurable (Function.uncurry c))
    {B : ℝ} (hB : ∀ x y, |c x y| ≤ B) {Bc ε a : ℝ} (hε : 0 < ε) (hBc : 0 < Bc)
    (hosc : ∀ x y y', c x y - c x y' ≤ Bc) (ha0 : 0 < a) (ha1 : a < 1) (hN : 0 < N) :
    ENNReal.ofReal (1 - a) ≤ Measure.pi (fun _ : Fin N => P) {X : Fin N → K |
      Theta ε (fun _ : Fin N => (1 : ℝ) / N) (fun i => c (X i)) P ≤
        ((∑ v, ((n v : ℝ) / N) * rhoHat ε c e Bc a v X : ℝ) : EReal)} := by
  have hV : 0 < V := by
    rcases Nat.eq_zero_or_pos V with h0 | h0
    · subst h0; exact (fold ⟨0, hN⟩).elim0
    · exact h0
  have hV' : (0 : ℝ) < V := by exact_mod_cast hV
  have hαV0 : 0 < a / V := div_pos ha0 hV'
  have hαV1 : a / V ≤ 1 := by
    rw [div_le_one hV']
    have : (1 : ℝ) ≤ V := by exact_mod_cast hV
    linarith
  -- the per-fold events, rewritten in terms of `ρ̂_v`
  have hset : ∀ v, {X : Fin N → K | StatFormal.RobustEquality.SemidualStrong.OTdisc ε
        (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j => c (X (e v j))) P ≤
          (rhoHat ε c e Bc a v X : EReal)} =
      {X : Fin N → K |
        Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j => c (X (e v j))) P ≤
          Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j => c (X (e v j)))
            (empOn fun i : {i // ¬ fold i = v} => X i) +
          ((Bc * √(Real.log (1 / (a / V)) / (2 * Fintype.card {i // ¬ fold i = v})) : ℝ) :
            EReal)} := by
    intro v
    obtain ⟨i0, hi0⟩ := hheld v
    have : Nonempty {i // ¬ fold i = v} := ⟨⟨i0, hi0⟩⟩
    ext X
    have hP := isProb_empOn (K := K) fun i : {i // ¬ fold i = v} => X i
    obtain ⟨r, hr⟩ := Theta_finite (sdhyp_fold_uniform hε hcm hB e hsurj v
      (fun i => X i)) (empOn fun i : {i // ¬ fold i = v} => X i)
    simp only [Set.mem_ofPred_eq, rhoHat]
    show Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j => c (X (e v j))) P ≤ _ ↔ _
    rw [hr, EReal.toReal_coe, EReal.coe_add, one_div_div]
  refine StatFormal.RobustEquality.Coverage.coverage_general K (Fin N → K)
    (Measure.pi fun _ : Fin N => P) P N V fold n e c (fun X => X) (rhoHat ε c e Bc a) ε a hε ha0
    ha1 hN hsurj (fun x0 => hcm.comp (measurable_const.prodMk measurable_id)) ⟨B, hB⟩
    (fun v => ?_) (fun v => ?_)
  · obtain ⟨i0, hi0⟩ := hheld v
    have : Nonempty {i // ¬ fold i = v} := ⟨⟨i0, hi0⟩⟩
    rw [hset v]
    exact (fold_coverage_random P e hsurj v hcm hB hε hBc hosc hαV0 hαV1).1
  · obtain ⟨i0, hi0⟩ := hheld v
    have : Nonempty {i // ¬ fold i = v} := ⟨⟨i0, hi0⟩⟩
    rw [hset v]
    exact (fold_coverage_random P e hsurj v hcm hB hε hBc hosc hαV0 hαV1).2

end Folds

end StatFormal.Foundations.SemiDiscrete
