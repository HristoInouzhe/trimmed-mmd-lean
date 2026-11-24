import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic

/-!
# Exchangeable vectors: ranks (component F.E, part 1)

Conventions (as in `StatFormal/OTFD/Ranks`): a law `μ` on `Fin m → ℝ` is *exchangeable* if
`μ.map (· ∘ τ) = μ` for every permutation `τ` (`IsExch`); for a random vector `S : Ω → Fin m → ℝ`
this is `P.map (fun ω => S ω ∘ τ) = P.map S` (`isExch_map`).

Two rank conventions for coordinate `i0` of `z`:
* `cntLt z i0 = #{j | z j < z i0}` (number strictly smaller; the *minimal* rank is `cntLt + 1`);
* `cntLe z i0 = #{j | z j ≤ z i0}` (number `≤`, itself included; the *maximal* rank).

Main results (`m` coordinates, `k : ℕ`):
* `measure_cntLe_le`: `P(cntLe ≤ k) ≤ k/m` — valid **without** any tie assumption
  (ties only make the maximal rank larger);
* `measure_cntLt_ge`: `P(cntLt < k) ≥ min(k, m)/m`, i.e. `P(minimal rank ≤ k) ≥ k/m` —
  valid without tie assumption (ties only make the minimal rank smaller);
  `P(cntLt < k) ≤ k/m` is false with ties (all coordinates equal: probability one);
* `measure_cntLt_le_of_inj`: with a.s. distinct coordinates, `P(cntLt < k) ≤ k/m`;
* `measure_cntLt_eq` (uniform rank): if the coordinates are a.s. distinct,
  `P(cntLt = r) = 1/m` for every `r < m`.
* `isExch_pi`, `isExch_of_iid`: i.i.d. coordinates (`Measure.pi`, or `iIndepFun` with a common
  law) are exchangeable.
Combinatorial cores: `card_cntLe_le`, `le_card_cntLt`; averaging: `card_mul_measure_eq`.
-/

noncomputable section
open MeasureTheory Finset
open scoped ENNReal

namespace StatFormal.Foundations.Exchangeable

/-! ### Combinatorics -/

section Comb

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder α]

omit [DecidableEq ι] in
/-- `#{i | #{j | v j ≤ v i} ≤ K} ≤ K`. -/
theorem card_cntLe_le (v : ι → α) (K : ℕ) :
    #(univ.filter fun i => #(univ.filter fun j => v j ≤ v i) ≤ K) ≤ K := by
  set A := univ.filter fun i => #(univ.filter fun j => v j ≤ v i) ≤ K
  rcases A.eq_empty_or_nonempty with h | h
  · rw [h, card_empty]; exact Nat.zero_le _
  obtain ⟨i0, hi0, hmax⟩ := A.exists_max_image v h
  have hsub : A ⊆ univ.filter fun j => v j ≤ v i0 := fun i hi =>
    mem_filter.mpr ⟨mem_univ _, hmax i hi⟩
  exact (card_le_card hsub).trans (mem_filter.mp hi0).2

/-- `min(k, |ι|) ≤ #{i | #{j | v j < v i} < k}`. -/
theorem le_card_cntLt (v : ι → α) (k : ℕ) :
    min k (Fintype.card ι) ≤ #(univ.filter fun i => #(univ.filter fun j => v j < v i) < k) := by
  set Bs := univ.filter fun i => ¬ (#(univ.filter fun j => v j < v i) < k)
  have hcompl := card_filter_add_card_filter_not (s := (univ : Finset ι))
    (fun i => #(univ.filter fun j => v j < v i) < k)
  rw [card_univ] at hcompl
  rcases Bs.eq_empty_or_nonempty with h | h
  · rw [show (univ.filter fun i => ¬ (#(univ.filter fun j => v j < v i) < k)) = ∅ from h,
      card_empty, add_zero] at hcompl
    omega
  obtain ⟨i0, hi0, hmin⟩ := Bs.exists_min_image v h
  have hk : k ≤ #(univ.filter fun j => v j < v i0) := not_lt.mp (mem_filter.mp hi0).2
  have hdisj : Disjoint (univ.filter fun j => v j < v i0) Bs := by
    rw [disjoint_left]
    intro j hj hjB
    exact absurd (hmin j hjB) (not_le.mpr (mem_filter.mp hj).2)
  have hU := card_le_univ ((univ.filter fun j => v j < v i0) ∪ Bs)
  rw [card_union_of_disjoint hdisj] at hU
  have : #Bs = #(univ.filter fun i => ¬ (#(univ.filter fun j => v j < v i) < k)) := rfl
  omega

/-- For injective `v`, `#{j | v j ≤ v i} = #{j | v j < v i} + 1`. -/
lemma cntLe_eq_cntLt_add_one {v : ι → α} (hv : Function.Injective v) (i : ι) :
    #(univ.filter fun j => v j ≤ v i) = #(univ.filter fun j => v j < v i) + 1 := by
  have : (univ.filter fun j => v j ≤ v i) = insert i (univ.filter fun j => v j < v i) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro h
      rcases h.lt_or_eq with h | h
      · exact Or.inr h
      · exact Or.inl (hv h)
    · rintro (rfl | h)
      · exact le_rfl
      · exact h.le
  rw [this, card_insert_of_notMem (by simp)]

/-- For injective `v`, exactly one coordinate has `r` strictly smaller ones (`r < |ι|`). -/
theorem card_cntLt_eq_one {v : ι → α} (hv : Function.Injective v) {r : ℕ}
    (hr : r < Fintype.card ι) :
    #(univ.filter fun i => #(univ.filter fun j => v j < v i) = r) = 1 := by
  have h1 := le_card_cntLt v (r + 1)
  have h2 := card_cntLe_le v r
  have h3 := le_card_cntLt v r
  have h4 := card_cntLe_le v (r + 1)
  simp_rw [cntLe_eq_cntLt_add_one hv] at h2 h4
  rw [min_eq_left (by omega)] at h1
  rw [min_eq_left (by omega)] at h3
  have e1 : (univ.filter fun i => #(univ.filter fun j => v j < v i) < r + 1) =
      (univ.filter fun i => #(univ.filter fun j => v j < v i) < r) ∪
        (univ.filter fun i => #(univ.filter fun j => v j < v i) = r) := by
    ext i; simp only [mem_filter, mem_univ, true_and, mem_union]; omega
  have hd : Disjoint (univ.filter fun i => #(univ.filter fun j => v j < v i) < r)
      (univ.filter fun i => #(univ.filter fun j => v j < v i) = r) := by
    rw [disjoint_filter]; intro i _ h; omega
  rw [e1, card_union_of_disjoint hd] at h1
  have e2 : (univ.filter fun i => #(univ.filter fun j => v j < v i) + 1 ≤ r) =
      univ.filter fun i => #(univ.filter fun j => v j < v i) < r := by
    ext i; simp only [mem_filter, mem_univ, true_and]; omega
  have e3 : (univ.filter fun i => #(univ.filter fun j => v j < v i) + 1 ≤ r + 1) =
      (univ.filter fun i => #(univ.filter fun j => v j < v i) < r) ∪
        (univ.filter fun i => #(univ.filter fun j => v j < v i) = r) := by
    ext i; simp only [mem_filter, mem_univ, true_and, mem_union]; omega
  rw [e2] at h2
  rw [e3, card_union_of_disjoint hd] at h4
  omega

end Comb

/-! ### Averaging over invariant transformations -/

section Avg

variable {X : Type*} [MeasurableSpace X]

/-- `|ι| · μ(E) = ∫ #{i | φ_i x ∈ E} dμ` for transformations `φ_i` preserving `μ`. -/
theorem card_mul_measure_eq (μ : Measure X) {ι : Type*} [Fintype ι] (φ : ι → X → X)
    (hφ : ∀ i, Measurable (φ i)) (hinv : ∀ i, μ.map (φ i) = μ) {E : Set X}
    [∀ x, DecidablePred fun i => φ i x ∈ E] (hE : MeasurableSet E) :
    (Fintype.card ι : ℝ≥0∞) * μ E = ∫⁻ x, (#(univ.filter fun i => φ i x ∈ E) : ℝ≥0∞) ∂μ := by
  have h1 : ∀ i, μ (φ i ⁻¹' E) = μ E := fun i => by
    rw [← Measure.map_apply (hφ i) hE, hinv i]
  have h2 : ∀ x, (#(univ.filter fun i => φ i x ∈ E) : ℝ≥0∞) =
      ∑ i, (φ i ⁻¹' E).indicator 1 x := fun x => by
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : φ i x ∈ E
    · rw [ite_eq_left h, Set.indicator_of_mem (show x ∈ φ i ⁻¹' E from h), Pi.one_apply]
    · rw [ite_eq_right h, Set.indicator_of_notMem (show x ∉ φ i ⁻¹' E from h)]
  simp_rw [h2]
  rw [lintegral_finsetSum _ fun i _ => (measurable_one.indicator ((hφ i) hE))]
  rw [Finset.sum_congr rfl fun i _ => by rw [lintegral_indicator_one ((hφ i) hE), h1 i],
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem card_mul_measure_le (μ : Measure X) [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (φ : ι → X → X) (hφ : ∀ i, Measurable (φ i)) (hinv : ∀ i, μ.map (φ i) = μ) {E : Set X}
    [∀ x, DecidablePred fun i => φ i x ∈ E] (hE : MeasurableSet E) {K : ℕ}
    (hK : ∀ᵐ x ∂μ, #(univ.filter fun i => φ i x ∈ E) ≤ K) :
    (Fintype.card ι : ℝ≥0∞) * μ E ≤ K := by
  rw [card_mul_measure_eq μ φ hφ hinv hE]
  calc ∫⁻ x, (#(univ.filter fun i => φ i x ∈ E) : ℝ≥0∞) ∂μ ≤ ∫⁻ _x, (K : ℝ≥0∞) ∂μ :=
        lintegral_mono_ae (hK.mono fun x hx => by exact_mod_cast hx)
    _ = K := by rw [lintegral_const, measure_univ, mul_one]

theorem le_card_mul_measure (μ : Measure X) [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (φ : ι → X → X) (hφ : ∀ i, Measurable (φ i)) (hinv : ∀ i, μ.map (φ i) = μ) {E : Set X}
    [∀ x, DecidablePred fun i => φ i x ∈ E] (hE : MeasurableSet E) {K : ℕ}
    (hK : ∀ᵐ x ∂μ, K ≤ #(univ.filter fun i => φ i x ∈ E)) :
    (K : ℝ≥0∞) ≤ (Fintype.card ι : ℝ≥0∞) * μ E := by
  rw [card_mul_measure_eq μ φ hφ hinv hE]
  calc (K : ℝ≥0∞) = ∫⁻ _x, (K : ℝ≥0∞) ∂μ := by rw [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := lintegral_mono_ae (hK.mono fun x hx => by exact_mod_cast hx)

end Avg

/-! ### Exchangeable laws on `Fin m → ℝ` -/

/-- Exchangeability of a law on `Fin m → ℝ`. -/
def IsExch {m : ℕ} (μ : Measure (Fin m → ℝ)) : Prop :=
  ∀ τ : Equiv.Perm (Fin m), μ.map (fun z => z ∘ τ) = μ

/-- Number of coordinates strictly smaller than coordinate `i`. -/
def cntLt {m : ℕ} (z : Fin m → ℝ) (i : Fin m) : ℕ := #(univ.filter fun j => z j < z i)

/-- Number of coordinates `≤` coordinate `i` (itself included). -/
def cntLe {m : ℕ} (z : Fin m → ℝ) (i : Fin m) : ℕ := #(univ.filter fun j => z j ≤ z i)

section Exch

variable {m : ℕ}

lemma measurable_comp_perm (τ : Equiv.Perm (Fin m)) :
    Measurable fun z : Fin m → ℝ => z ∘ τ :=
  Measurable.of_eval fun i => measurable_pi_apply (τ i)

/-- A random vector with permutation-invariant law has an exchangeable law. -/
theorem isExch_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {S : Ω → Fin m → ℝ}
    (hS : Measurable S) (h : ∀ τ : Equiv.Perm (Fin m), P.map (fun ω => S ω ∘ τ) = P.map S) :
    IsExch (P.map S) := fun τ => by
  rw [Measure.map_map (measurable_comp_perm τ) hS]
  exact h τ

lemma card_filter_comp_perm {p : Fin m → Prop} [DecidablePred p] (σ : Equiv.Perm (Fin m)) :
    #(univ.filter fun j => p (σ j)) = #(univ.filter p) := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp σ (fun j => if p j then 1 else 0)

lemma cntLt_comp (z : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    cntLt (z ∘ σ) i = cntLt z (σ i) :=
  card_filter_comp_perm (p := fun j => z j < z (σ i)) σ

lemma cntLe_comp (z : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    cntLe (z ∘ σ) i = cntLe z (σ i) :=
  card_filter_comp_perm (p := fun j => z j ≤ z (σ i)) σ

lemma measurable_cntLt (i : Fin m) : Measurable fun z : Fin m → ℝ => cntLt z i := by
  unfold cntLt
  simp_rw [Finset.card_filter]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact Measurable.ite (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i))
    measurable_const measurable_const

lemma measurable_cntLe (i : Fin m) : Measurable fun z : Fin m → ℝ => cntLe z i := by
  unfold cntLe
  simp_rw [Finset.card_filter]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact Measurable.ite (measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i))
    measurable_const measurable_const

/-- The transformations `z ↦ z ∘ swap i0 i` bring coordinate `i` to position `i0`. -/
lemma swap_avg (i0 : Fin m) {p : (Fin m → ℝ) → Fin m → Prop} [∀ z i, Decidable (p z i)]
    (hp : ∀ z (σ : Equiv.Perm (Fin m)) i, p (z ∘ σ) i ↔ p z (σ i)) (z : Fin m → ℝ) :
    #(univ.filter fun i => (z ∘ Equiv.swap i0 i) ∈ {w | p w i0}) =
      #(univ.filter fun i => p z i) := by
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, Set.mem_ofPred_eq, hp, Equiv.swap_apply_left]

/-- **`P(cntLe ≤ k) ≤ k/m`** (maximal rank; no tie assumption). -/
theorem measure_cntLe_le (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ] (hμ : IsExch μ)
    (i0 : Fin m) (k : ℕ) :
    (m : ℝ≥0∞) * μ {z | cntLe z i0 ≤ k} ≤ k := by
  have hE : MeasurableSet {z : Fin m → ℝ | cntLe z i0 ≤ k} :=
    measurable_cntLe i0 (MeasurableSet.of_discrete (s := {x : ℕ | x ≤ k}))
  have := card_mul_measure_le μ (fun i z => z ∘ Equiv.swap i0 i)
    (fun i => measurable_comp_perm _) (fun i => hμ _) hE (K := k)
    (Filter.Eventually.of_forall fun z => by
      rw [swap_avg i0 (p := fun w i => cntLe w i ≤ k) (fun w σ i => by rw [cntLe_comp]) z]
      exact card_cntLe_le z k)
  rwa [Fintype.card_fin] at this

/-- **`P(cntLt < k) ≥ min(k,m)/m`** (minimal rank; no tie assumption). -/
theorem measure_cntLt_ge (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ] (hμ : IsExch μ)
    (i0 : Fin m) (k : ℕ) :
    (min k m : ℝ≥0∞) ≤ (m : ℝ≥0∞) * μ {z | cntLt z i0 < k} := by
  have hE : MeasurableSet {z : Fin m → ℝ | cntLt z i0 < k} :=
    measurable_cntLt i0 (MeasurableSet.of_discrete (s := {x : ℕ | x < k}))
  have := le_card_mul_measure μ (fun i z => z ∘ Equiv.swap i0 i)
    (fun i => measurable_comp_perm _) (fun i => hμ _) hE (K := min k m)
    (Filter.Eventually.of_forall fun z => by
      rw [swap_avg i0 (p := fun w i => cntLt w i < k) (fun w σ i => by rw [cntLt_comp]) z]
      have := le_card_cntLt z k
      rwa [Fintype.card_fin] at this)
  rw [Fintype.card_fin] at this
  have e : ((min k m : ℕ) : ℝ≥0∞) = min (k : ℝ≥0∞) m := by
    rcases le_total k m with h | h
    · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
    · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]
  rw [e] at this
  exact this

/-- **Uniform rank**: with a.s. distinct coordinates, `P(cntLt = r) = 1/m` for `r < m`. -/
theorem measure_cntLt_eq (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ] (hμ : IsExch μ)
    (hdist : ∀ᵐ z ∂μ, Function.Injective z) (i0 : Fin m) {r : ℕ} (hr : r < m) :
    (m : ℝ≥0∞) * μ {z | cntLt z i0 = r} = 1 := by
  have hE : MeasurableSet {z : Fin m → ℝ | cntLt z i0 = r} :=
    measurable_cntLt i0 (MeasurableSet.of_discrete (s := {x : ℕ | x = r}))
  have hcount : ∀ᵐ z ∂μ,
      #(univ.filter fun i => z ∘ Equiv.swap i0 i ∈ {z : Fin m → ℝ | cntLt z i0 = r}) = 1 :=
    hdist.mono fun z hz => by
      rw [swap_avg i0 (p := fun w i => cntLt w i = r) (fun w σ i => by rw [cntLt_comp]) z]
      have := card_cntLt_eq_one hz (r := r) (by rwa [Fintype.card_fin])
      exact this
  have h1 := card_mul_measure_le μ (fun i z => z ∘ Equiv.swap i0 i)
    (fun i => measurable_comp_perm _) (fun i => hμ _) hE (K := 1) (hcount.mono fun z hz => hz.le)
  have h2 := le_card_mul_measure μ (fun i z => z ∘ Equiv.swap i0 i)
    (fun i => measurable_comp_perm _) (fun i => hμ _) hE (K := 1) (hcount.mono fun z hz => hz.ge)
  rw [Fintype.card_fin] at h1 h2
  exact le_antisymm (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- With a.s. distinct coordinates, `P(cntLt < k) ≤ k/m`. -/
theorem measure_cntLt_le_of_inj (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsExch μ) (hdist : ∀ᵐ z ∂μ, Function.Injective z) (i0 : Fin m) (k : ℕ) :
    (m : ℝ≥0∞) * μ {z | cntLt z i0 < k} ≤ k := by
  have hE : MeasurableSet {z : Fin m → ℝ | cntLt z i0 < k} :=
    measurable_cntLt i0 (MeasurableSet.of_discrete (s := {x : ℕ | x < k}))
  have := card_mul_measure_le μ (fun i z => z ∘ Equiv.swap i0 i)
    (fun i => measurable_comp_perm _) (fun i => hμ _) hE (K := k)
    (hdist.mono fun z hz => by
      rw [swap_avg i0 (p := fun w i => cntLt w i < k) (fun w σ i => by rw [cntLt_comp]) z]
      refine le_trans (card_le_card fun i hi => ?_) (card_cntLe_le z k)
      have hi' := (mem_filter.mp hi).2
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      have := cntLe_eq_cntLt_add_one hz i
      unfold cntLt at hi'
      omega)
  rwa [Fintype.card_fin] at this

end Exch

/-! ### I.i.d. ⇒ exchangeable -/

section IID

variable {X : Type*} [MeasurableSpace X] {m : ℕ}

/-- A product law is invariant under permutations of the coordinates. -/
theorem pi_map_comp_perm (ν : Measure X) [SigmaFinite ν] (τ : Equiv.Perm (Fin m)) :
    (Measure.pi fun _ : Fin m => ν).map (fun z => z ∘ τ) = Measure.pi fun _ : Fin m => ν := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hmeas : Measurable fun z : Fin m → X => z ∘ τ :=
    Measurable.of_eval fun i => measurable_pi_apply (τ i)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun z : Fin m → X => z ∘ τ) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun j => s (τ.symm j) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
    constructor
    · intro h j
      have := h (τ.symm j)
      rwa [Equiv.apply_symm_apply] at this
    · intro h i
      have := h (τ i)
      rwa [Equiv.symm_apply_apply] at this
  rw [hpre, Measure.pi_pi]
  exact Equiv.prod_comp τ.symm (fun j => ν (s j))

theorem isExch_pi (ν : Measure ℝ) [SigmaFinite ν] : IsExch (Measure.pi fun _ : Fin m => ν) :=
  pi_map_comp_perm ν

/-- **I.i.d. ⇒ exchangeable**: independent identically distributed scores have an exchangeable
joint law. -/
theorem isExch_of_iid {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {S : Fin m → Ω → ℝ} (hS : ∀ i, Measurable (S i)) (hind : ProbabilityTheory.iIndepFun S P)
    (ν : Measure ℝ) (hlaw : ∀ i, P.map (S i) = ν) :
    IsExch (P.map fun ω i => S i ω) := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    intro τ
    have : (fun z : Fin 0 → ℝ => z ∘ τ) = id := funext fun z => funext fun i => i.elim0
    rw [this, Measure.map_id]
  have hpi := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (hS i).aemeasurable)).mp hind
  rw [hpi]
  simp_rw [hlaw]
  have : IsProbabilityMeasure ν := by
    rw [← hlaw ⟨0, h0⟩]
    infer_instance
  exact isExch_pi ν

end IID

end StatFormal.Foundations.Exchangeable
