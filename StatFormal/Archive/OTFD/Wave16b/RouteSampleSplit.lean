import StatFormal.Archive.OTFD.Wave16b.Statements
import StatFormal.Archive.OTFD.Ranks.Proofs
import Mathlib.Probability.ConditionalProbability

/-!
# Route: A `thm:sample-split` (untrusted)

Independence and exchangeability give `(W, X∘τ) =ᵈ (W, X)` for every permutation `τ`. Under uniqueness,
`σ̂_W(Z∘τ) = σ̂_W(Z)·τ` (`Ranks.sel_comp`), so under `P[·|W ∈ B]` the law of `σ̂` is invariant under right
multiplication, and the certified `Ranks.invariant_perm_uniform` makes it uniform. The rank form sums over `π` the
events `{W ∈ B, u_W∘π ∈ S, σ̂ = π}`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.OTFD.Wave16b

open StatFormal.OTFD.Ranks (IsMin UniqueMin sel_comp)

section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H 𝒲 Ω : Type} [MeasurableSpace H] [MeasurableSpace 𝒲] [MeasurableSpace Ω] {n : ℕ}

lemma meas_scores {proj : 𝒲 → H → E} (hproj : Measurable (Function.uncurry proj)) :
    Measurable fun p : 𝒲 × (Fin n → H) => (p.1, fun i => proj p.1 (p.2 i)) := by
  exact measurable_fst.prodMk (Measurable.of_eval fun i =>
    hproj.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))

lemma meas_perm (τ : Equiv.Perm (Fin n)) : Measurable fun x : Fin n → H => x ∘ τ :=
  Measurable.of_eval fun i => measurable_pi_apply (τ i)

/-- The key invariance. -/
lemma split_invariance (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → 𝒲) (X : Ω → Fin n → H)
    (proj : 𝒲 → H → E) (u : 𝒲 → Fin n → E) (sel : 𝒲 → (Fin n → E) → Equiv.Perm (Fin n))
    (hW : Measurable W) (hX : Measurable X) (hproj : Measurable (Function.uncurry proj))
    (hsel : ∀ w z, IsMin (u w) z (sel w z))
    (hfib : ∀ π, MeasurableSet {p : 𝒲 × (Fin n → E) | sel p.1 p.2 = π})
    (hind : IndepFun W X P) (hexch : ∀ τ : Equiv.Perm (Fin n), P.map (fun ω => X ω ∘ τ) = P.map X)
    (huniq : ∀ᵐ ω ∂P, UniqueMin (u (W ω)) (fun i => proj (W ω) (X ω i)))
    {B : Set 𝒲} (hB : MeasurableSet B) (τ h : Equiv.Perm (Fin n)) :
    P ({ω | W ω ∈ B} ∩ {ω | sel (W ω) (fun i => proj (W ω) (X ω i)) * τ = h}) =
      P ({ω | W ω ∈ B} ∩ {ω | sel (W ω) (fun i => proj (W ω) (X ω i)) = h}) := by
  set G : Set (𝒲 × (Fin n → H)) := (B ×ˢ univ) ∩
    (fun p : 𝒲 × (Fin n → H) => (p.1, fun i => proj p.1 (p.2 i))) ⁻¹' {p | sel p.1 p.2 = h} with hG
  have hGm : MeasurableSet G := (hB.prod MeasurableSet.univ).inter (meas_scores hproj (hfib h))
  have hXτ : Measurable fun ω => X ω ∘ τ := (meas_perm τ).comp hX
  have hjoint : P.map (fun ω => (W ω, X ω ∘ τ)) = P.map (fun ω => (W ω, X ω)) := by
    have h1 := (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hX.aemeasurable).1 hind
    have hind' : IndepFun W (fun ω => X ω ∘ τ) P := hind.comp measurable_id (meas_perm τ)
    have h2 := (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hXτ.aemeasurable).1 hind'
    rw [h1, h2, hexch τ]
  have hae : ({ω | W ω ∈ B} ∩ {ω | sel (W ω) (fun i => proj (W ω) (X ω i)) * τ = h} : Set Ω) =ᵐ[P]
      (fun ω => (W ω, X ω ∘ τ)) ⁻¹' G := by
    filter_upwards [huniq] with ω hω
    have hc := sel_comp (u (W ω)) (sel (W ω)) (hsel (W ω)) _ hω τ
    simp only [hG, mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true, mem_setOf_eq, eq_iff_iff]
    have e : (fun i => proj (W ω) ((X ω ∘ τ) i)) = (fun i => proj (W ω) (X ω i)) ∘ τ := rfl
    rw [e, hc]
  rw [measure_congr hae, ← Measure.map_apply (hW.prodMk hXτ) hGm, hjoint, Measure.map_apply (hW.prodMk hX) hGm]
  congr 1
  ext ω
  simp [hG]

end

theorem sample_split : Claims.sample_split := by
  intro E _ _ _ _ H 𝒲 Ω _ _ _ P _ n W X proj u sel hW hX hproj hsel hfib hind hexch huniq B hB π
  set s : Set Ω := {ω | W ω ∈ B} with hs
  have hsm : MeasurableSet s := hW hB
  set σ : Ω → Equiv.Perm (Fin n) := fun ω => sel (W ω) (fun i => proj (W ω) (X ω i)) with hσ
  have hσm : ∀ h, MeasurableSet {ω | σ ω = h} := fun h =>
    ((meas_scores hproj).comp (hW.prodMk hX)) (hfib h)
  by_cases h0 : P s = 0
  · rw [h0, zero_mul]
    exact measure_mono_null inter_subset_left h0
  haveI := cond_isProbabilityMeasure (μ := P) h0
  have hinv : ∀ τ h, P[{ω | σ ω * τ = h} | s] = P[{ω | σ ω = h} | s] := by
    intro τ h
    rw [cond_apply hsm, cond_apply hsm]
    congr 1
    exact split_invariance P W X proj u sel hW hX hproj hsel hfib hind hexch huniq hB τ h
  have hu := StatFormal.OTFD.Ranks.invariant_perm_uniform Ω (P[|s]) n σ hσm hinv π
  rw [cond_apply hsm] at hu
  have htop : P s ≠ ⊤ := measure_ne_top _ _
  calc P (s ∩ {ω | σ ω = π}) = P s * ((P s)⁻¹ * P (s ∩ {ω | σ ω = π})) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel h0 htop, one_mul]
    _ = P s * (Nat.factorial n : ℝ≥0∞)⁻¹ := by rw [hu]

open scoped Classical in
theorem sample_split_ranks : Claims.sample_split_ranks := by
  intro E _ _ _ _ H 𝒲 Ω _ _ _ P _ n W X proj u sel hW hX hproj hu hsel hfib hind hexch huniq B hB S hS
  set s : Set Ω := {ω | W ω ∈ B} with hs
  set σ : Ω → Equiv.Perm (Fin n) := fun ω => sel (W ω) (fun i => proj (W ω) (X ω i)) with hσ
  have hσm : ∀ h, MeasurableSet {ω | σ ω = h} := fun h =>
    ((meas_scores hproj).comp (hW.prodMk hX)) (hfib h)
  set C : Equiv.Perm (Fin n) → Set 𝒲 := fun π => {w | u w ∘ π ∈ S} with hC
  have hCm : ∀ π, MeasurableSet (C π) := fun π =>
    (Measurable.of_eval fun i => (measurable_pi_apply (π i)).comp hu) hS
  -- decomposition of the event
  have hdec : s ∩ {ω | (fun i => u (W ω) (σ ω i)) ∈ S} =
      ⋃ π, ({ω | W ω ∈ B ∩ C π} ∩ {ω | σ ω = π}) := by
    ext ω
    simp only [hs, hC, mem_inter_iff, mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨σ ω, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨π, ⟨h1, h2⟩, h3⟩
      subst h3
      exact ⟨h1, h2⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun π => ({ω | W ω ∈ B ∩ C π} ∩ {ω | σ ω = π} : Set Ω)) := by
    intro π π' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨_, h1⟩ ⟨_, h2⟩
    exact hne (h1.symm.trans h2)
  have hmeas : ∀ π, MeasurableSet ({ω | W ω ∈ B ∩ C π} ∩ {ω | σ ω = π} : Set Ω) := fun π =>
    (hW (hB.inter (hCm π))).inter (hσm π)
  have hσ' : σ = fun ω => sel (W ω) (fun i => proj (W ω) (X ω i)) := rfl
  rw [show {ω | (fun i => u (W ω) (sel (W ω) (fun i => proj (W ω) (X ω i)) i)) ∈ S} =
      {ω | (fun i => u (W ω) (σ ω i)) ∈ S} from rfl, hdec, measure_iUnion hdisj hmeas, tsum_fintype]
  have hterm : ∀ π, P ({ω | W ω ∈ B ∩ C π} ∩ {ω | σ ω = π}) = P {ω | W ω ∈ B ∩ C π} * (Nat.factorial n : ℝ≥0∞)⁻¹ :=
    fun π => sample_split E H 𝒲 Ω P n W X proj u sel hW hX hproj hsel hfib hind hexch huniq _ (hB.inter (hCm π)) π
  simp_rw [hterm]
  -- the right-hand side
  have hcard : ∀ ω, ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => u (W ω) ∘ π ∈ S)).card : ℝ≥0∞) =
      ∑ π, (C π).indicator (fun _ => (1 : ℝ≥0∞)) (W ω) := by
    intro ω
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    by_cases h : u (W ω) ∘ π ∈ S <;> simp [hC, h, Set.indicator]
  simp_rw [hcard, Finset.sum_mul]
  have hind_m : ∀ π, Measurable fun ω => (C π).indicator (fun _ => (1 : ℝ≥0∞)) (W ω) * (Nat.factorial n : ℝ≥0∞)⁻¹ :=
    fun π => ((measurable_const.indicator (hCm π)).comp hW).mul_const _
  rw [lintegral_finsetSum _ fun π _ => hind_m π]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [lintegral_mul_const (f := fun ω => (C π).indicator (fun _ => (1 : ℝ≥0∞)) (W ω)) _
    ((measurable_const.indicator (hCm π)).comp hW)]
  congr 1
  have e : (fun ω => (C π).indicator (fun _ => (1 : ℝ≥0∞)) (W ω)) = (W ⁻¹' C π).indicator (fun _ => 1) := by
    funext ω; by_cases h : W ω ∈ C π <;> simp [Set.indicator, h]
  rw [e, lintegral_indicator_const ((hCm π).preimage hW), one_mul, Measure.restrict_apply ((hCm π).preimage hW)]
  congr 1
  ext ω; simp [hs, and_comm]

end StatFormal.OTFD.Wave16b
