import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic

/-!
# Hoeffding decomposition of one-sample V-statistics (library)

For a bounded measurable kernel `f : 𝒵^M → ℝ` and i.i.d. `P₀` points `Z_0, …, Z_{n−1}`, the V-statistic
`V_n f = n^{−M} Σ_{j ∈ [n]^M} f(Z_{j_1}, …, Z_{j_M})` satisfies
`E[(V_n f − θ − Σ_r P_n f_r)²] ≤ 4 M⁴ ((2M+2) B)² / n²`, where `θ = P₀^{⊗M} f` and
`f_r(c) = ∫ f(u with u_r = c) dP₀^{⊗M}(u) − θ` are the first-order projections
(`vstat_hoeffding_sq_le`). Proof:
* the Hoeffding remainder `hRem f = f − θ − Σ_r f_r(u_r)` is first-order degenerate: integrating out all
  coordinates but one gives `0` (`hRem_deg`);
* resampling (`measurePreserving_mixPi`) and injective reindexing (`measurePreserving_comp_inj`) of product
  measures give `E[g(Z∘j) g(Z∘j')] = 0` for injective index tuples sharing at most one value
  (`integral_pair_eq_zero`);
* the remaining pairs number at most `M⁴ n^{2M−2}`, the non-injective tuples at most `M² n^{M−1}`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Finset Function

namespace StatFormal.Foundations.CLT

section PiTools
variable {Z : Type*} [MeasurableSpace Z] (P0 : Measure Z) [IsProbabilityMeasure P0]

/-- `mixPi S z w` takes the coordinates in `S` from `w`, the others from `z`. -/
def mixPi {ι : Type*} [DecidableEq ι] (S : Finset ι) (z w : ι → Z) : ι → Z :=
  fun i => if i ∈ S then w i else z i

lemma measurable_mixPi {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    Measurable (fun p : (ι → Z) × (ι → Z) => mixPi S p.1 p.2) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i ∈ S
  · simp only [mixPi, h, if_true]; exact (measurable_pi_apply i).comp measurable_snd
  · simp only [mixPi, h, if_false]; exact (measurable_pi_apply i).comp measurable_fst

/-- Resampling the coordinates in `S` by an independent copy preserves the product law. -/
lemma measurePreserving_mixPi {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) :
    MeasurePreserving (fun p : (ι → Z) × (ι → Z) => mixPi S p.1 p.2)
      ((Measure.pi fun _ : ι => P0).prod (Measure.pi fun _ : ι => P0)) (Measure.pi fun _ : ι => P0) := by
  refine ⟨measurable_mixPi S, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply (measurable_mixPi S) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → Z) × (ι → Z) => mixPi S p.1 p.2) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi fun i => if i ∈ S then Set.univ else s i) ×ˢ
        (Set.univ.pi fun i => if i ∈ S then s i else Set.univ) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, mixPi]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i ∈ S
        · simp only [hi, if_true, Set.mem_univ]
        · have := h i; simp only [hi, if_false] at this ⊢; exact this
      · by_cases hi : i ∈ S
        · have := h i; simp only [hi, if_true] at this ⊢; exact this
        · simp only [hi, if_false, Set.mem_univ]
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ S
      · have := h2 i; simp only [hi, if_true] at this ⊢; exact this
      · have := h1 i; simp only [hi, if_false] at this ⊢; exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S <;> simp [hi]

/-- Injective reindexing `z ↦ z ∘ j` preserves the product law. -/
lemma measurePreserving_comp_inj {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (j : κ → ι)
    (hj : Injective j) :
    MeasurePreserving (fun z : ι → Z => z ∘ j) (Measure.pi fun _ : ι => P0) (Measure.pi fun _ : κ => P0) := by
  have hm : Measurable (fun z : ι → Z => z ∘ j) := measurable_pi_iff.2 fun k => measurable_pi_apply (j k)
  refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  set t : ι → Set Z := fun i => ⋂ k ∈ (univ.filter fun k => j k = i), s k with htdef
  have hpre : (fun z : ι → Z => z ∘ j) ⁻¹' Set.univ.pi s = Set.univ.pi t := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, comp_apply, htdef, Set.mem_iInter, mem_filter, mem_univ,
      true_and]
    constructor
    · intro h i k hk; rw [← hk]; exact h k
    · intro h k; exact h (j k) k rfl
  rw [hpre, Measure.pi_pi]
  have h1 : ∀ i ∈ (univ : Finset ι), i ∉ univ.image j → P0 (t i) = 1 := by
    intro i _ hi
    have : t i = Set.univ := by
      ext z
      simp only [htdef, Set.mem_iInter, mem_filter, mem_univ, true_and, Set.mem_univ, iff_true]
      intro k hk; exact absurd (mem_image.2 ⟨k, mem_univ _, hk⟩) hi
    rw [this, measure_univ]
  have h2 : ∀ k, t (j k) = s k := by
    intro k; ext z
    simp only [htdef, Set.mem_iInter, mem_filter, mem_univ, true_and]
    constructor
    · intro h; exact h k rfl
    · intro h k' hk'; rw [hj hk']; exact h
  rw [← Finset.prod_subset (subset_univ (univ.image j)) h1, prod_image (fun a _ b _ h => hj h)]
  simp_rw [h2]

end PiTools

/-! ### Bounded measurable functions -/

lemma integral_eq_of_measurePreserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} {φ : α → β} (hφ : MeasurePreserving φ μ ν) {g : β → ℝ} (hg : Measurable g) :
    ∫ y, g y ∂ν = ∫ x, g (φ x) ∂μ := by
  rw [← hφ.map_eq, integral_map hφ.measurable.aemeasurable hg.aestronglyMeasurable]

lemma integrable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) {C : ℝ} (h : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact h x)

lemma abs_integral_le_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} {C : ℝ} (h : ∀ x, |f x| ≤ C) : |∫ x, f x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := C)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact h x)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
  exact this

/-! ### The Hoeffding projections -/

section Hoeffding
variable {Z : Type*} [MeasurableSpace Z] (P0 : Measure Z) [IsProbabilityMeasure P0] {M : ℕ}

/-- `θ = P₀^{⊗M} f`. -/
def hMean (f : (Fin M → Z) → ℝ) : ℝ := ∫ u, f u ∂(Measure.pi fun _ : Fin M => P0)

/-- `c ↦ ∫ f(u with u_r = c) dP₀^{⊗M}(u)` (the projection on the `r`-th coordinate, uncentred). -/
def hProj (f : (Fin M → Z) → ℝ) (r : Fin M) (c : Z) : ℝ :=
  ∫ u, f (update u r c) ∂(Measure.pi fun _ : Fin M => P0)

/-- The Hoeffding remainder `f − θ − Σ_r (f_r(u_r) − θ)`. -/
def hRem (f : (Fin M → Z) → ℝ) (u : Fin M → Z) : ℝ :=
  f u - hMean P0 f - ∑ r, (hProj P0 f r (u r) - hMean P0 f)

/-- The V-statistic `n^{−M} Σ_{j ∈ [n]^M} f(z ∘ j)`. -/
def vstat {n : ℕ} (f : (Fin M → Z) → ℝ) (z : Fin n → Z) : ℝ :=
  ((n : ℝ) ^ M)⁻¹ * ∑ j : Fin M → Fin n, f (z ∘ j)

variable {P0}

lemma measurable_update_fst (r : Fin M) :
    Measurable (fun p : Z × (Fin M → Z) => update p.2 r p.1) :=
  measurable_update'.comp (measurable_snd.prodMk measurable_fst)

lemma measurable_hProj {f : (Fin M → Z) → ℝ} (hf : Measurable f) (r : Fin M) : Measurable (hProj P0 f r) :=
  ((hf.comp (measurable_update_fst r)).stronglyMeasurable.integral_prod_right'
    (ν := Measure.pi fun _ : Fin M => P0)).measurable

lemma abs_hMean_le {f : (Fin M → Z) → ℝ} {B : ℝ} (hB : ∀ u, |f u| ≤ B) : |hMean P0 f| ≤ B :=
  abs_integral_le_of_abs_le hB

lemma abs_hProj_le {f : (Fin M → Z) → ℝ} {B : ℝ} (hB : ∀ u, |f u| ≤ B) (r : Fin M) (c : Z) :
    |hProj P0 f r c| ≤ B :=
  abs_integral_le_of_abs_le fun u => hB _

lemma measurable_hRem {f : (Fin M → Z) → ℝ} (hf : Measurable f) : Measurable (hRem P0 f) := by
  unfold hRem
  refine (hf.sub_const _).sub (Finset.measurable_sum _ fun r _ => ?_)
  exact ((measurable_hProj hf r).comp (measurable_pi_apply r)).sub_const _

lemma abs_hRem_le {f : (Fin M → Z) → ℝ} {B : ℝ} (hB : ∀ u, |f u| ≤ B) (u : Fin M → Z) :
    |hRem P0 f u| ≤ (2 * M + 2) * B := by
  unfold hRem
  have h1 := hB u
  have h2 := abs_hMean_le (P0 := P0) hB
  have h3 : |∑ r, (hProj P0 f r (u r) - hMean P0 f)| ≤ ∑ _r : Fin M, 2 * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    have := abs_hProj_le (P0 := P0) hB r (u r)
    calc |hProj P0 f r (u r) - hMean P0 f| ≤ |hProj P0 f r (u r)| + |hMean P0 f| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  calc |f u - hMean P0 f - ∑ r, (hProj P0 f r (u r) - hMean P0 f)|
      ≤ |f u| + |hMean P0 f| + |∑ r, (hProj P0 f r (u r) - hMean P0 f)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ B + B + M * (2 * B) := by linarith
    _ = (2 * M + 2) * B := by ring

/-- `∫ f_r(u_r) dP₀^{⊗M}(u) = θ`. -/
lemma integral_hProj {f : (Fin M → Z) → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ u, |f u| ≤ B) (r : Fin M) :
    ∫ u, hProj P0 f r (u r) ∂(Measure.pi fun _ : Fin M => P0) = hMean P0 f := by
  classical
  have hmp := measurePreserving_mixPi P0 ({r} : Finset (Fin M))
  have hmix : ∀ u w : Fin M → Z, mixPi {r} u w = update u r (w r) := by
    intro u w; funext k
    by_cases hk : k = r
    · subst hk; simp [mixPi]
    · simp [mixPi, hk, update_of_ne hk]
  unfold hMean
  rw [integral_eq_of_measurePreserving hmp hf]
  simp_rw [hmix]
  rw [integral_prod_symm]
  · rfl
  · refine integrable_of_abs_le ?_ fun p => hB _
    exact hf.comp (measurable_update'.comp (measurable_fst.prodMk ((measurable_pi_apply r).comp measurable_snd)))

/-- The Hoeffding remainder is first-order degenerate. -/
lemma hRem_deg {f : (Fin M → Z) → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ u, |f u| ≤ B) (r : Fin M) (c : Z) :
    ∫ u, hRem P0 f (update u r c) ∂(Measure.pi fun _ : Fin M => P0) = 0 := by
  classical
  set μ := Measure.pi fun _ : Fin M => P0
  have hmu : Measurable (fun u : Fin M → Z => update u r c) := measurable_update' (a := r) |>.comp
    (measurable_id.prodMk measurable_const)
  have hterm : ∀ r', Integrable (fun u : Fin M → Z => hProj P0 f r' (update u r c r') - hMean P0 f) μ := by
    intro r'
    refine integrable_of_abs_le (((measurable_hProj hf r').comp ((measurable_pi_apply r').comp hmu)).sub_const _)
      (C := 2 * B) fun u => ?_
    have := abs_hProj_le (P0 := P0) hB r' (update u r c r')
    have := abs_hMean_le (P0 := P0) hB
    calc _ ≤ |hProj P0 f r' (update u r c r')| + |hMean P0 f| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hval : ∀ r', ∫ u, (hProj P0 f r' (update u r c r') - hMean P0 f) ∂μ =
      if r' = r then hProj P0 f r c - hMean P0 f else 0 := by
    intro r'
    by_cases h : r' = r
    · subst h
      simp only [update_self, if_true]
      rw [integral_const, probReal_univ, one_smul]
    · simp only [h, if_false]
      simp_rw [update_of_ne h]
      rw [integral_sub ((integrable_of_abs_le (f := fun u : Fin M → Z => hProj P0 f r' (u r'))
        (Measurable.comp (g := hProj P0 f r') (f := fun u : Fin M → Z => u r') (measurable_hProj hf r')
          (measurable_pi_apply r'))
        (C := B) fun u => abs_hProj_le hB r' (u r'))) (integrable_const _), integral_hProj hf hB r',
        integral_const, probReal_univ, one_smul, sub_self]
  unfold hRem
  rw [integral_sub, integral_sub, integral_finset_sum _ fun r' _ => hterm r']
  · simp_rw [hval]
    rw [Finset.sum_ite_eq' univ r, if_pos (mem_univ _), integral_const, probReal_univ, one_smul]
    show hProj P0 f r c - hMean P0 f - (hProj P0 f r c - hMean P0 f) = 0
    ring
  · exact integrable_of_abs_le (hf.comp hmu) fun u => hB _
  · exact integrable_const _
  · exact (integrable_of_abs_le (hf.comp hmu) fun u => hB _).sub (integrable_const _)
  · exact integrable_finset_sum _ fun r' _ => hterm r'

end Hoeffding

/-! ### Counting index tuples -/

section Count
variable {M n : ℕ}

lemma sum_fun_prod (φ : Fin M → Fin n → ℝ) :
    ∑ j : Fin M → Fin n, ∏ k, φ k (j k) = ∏ k, ∑ c, φ k c := (Fintype.prod_sum φ).symm

lemma sum_comp_eval (φ : Fin n → ℝ) (r : Fin M) :
    ∑ j : Fin M → Fin n, φ (j r) = (n : ℝ) ^ (M - 1) * ∑ a, φ a := by
  classical
  have h1 : ∀ j : Fin M → Fin n, φ (j r) = ∏ k, (if k = r then φ (j k) else 1) := by
    intro j; rw [Finset.prod_ite_eq' univ r, if_pos (mem_univ _)]
  simp_rw [h1]
  rw [sum_fun_prod (fun k c => if k = r then φ c else 1), ← Finset.mul_prod_erase univ _ (mem_univ r)]
  simp only [if_true]
  rw [Finset.prod_congr rfl (g := fun _ => (n : ℝ)) (fun k hk => by simp [Finset.ne_of_mem_erase hk]),
    Finset.prod_const, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin, mul_comm]

lemma sum_indicator_two (p q : Fin M) (hpq : p ≠ q) (a b : Fin n) :
    ∑ j : Fin M → Fin n, ((if j p = a then (1 : ℝ) else 0) * (if j q = b then (1 : ℝ) else 0)) =
      (n : ℝ) ^ (M - 2) := by
  classical
  set φ : Fin M → Fin n → ℝ := fun k c =>
    if k = p then (if c = a then 1 else 0) else if k = q then (if c = b then 1 else 0) else 1 with hφ
  have hq : q ∈ univ.erase p := mem_erase.2 ⟨hpq.symm, mem_univ _⟩
  have h1 : ∀ j : Fin M → Fin n, ((if j p = a then (1 : ℝ) else 0) * (if j q = b then (1 : ℝ) else 0)) =
      ∏ k, φ k (j k) := by
    intro j
    rw [← Finset.mul_prod_erase univ _ (mem_univ p), ← Finset.mul_prod_erase _ _ hq]
    have hrest : ∏ k ∈ (univ.erase p).erase q, φ k (j k) = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      have hkq := Finset.ne_of_mem_erase hk
      have hkp := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
      simp [hφ, hkq, hkp]
    rw [hrest, mul_one]
    simp [hφ, hpq.symm]
  simp_rw [h1]
  rw [sum_fun_prod, ← Finset.mul_prod_erase univ _ (mem_univ p), ← Finset.mul_prod_erase _ _ hq]
  have hp1 : ∑ c, φ p c = 1 := by simp [hφ]
  have hq1 : ∑ c, φ q c = 1 := by simp [hφ, hpq.symm]
  have hrest : ∏ k ∈ (univ.erase p).erase q, ∑ c, φ k c = (n : ℝ) ^ (M - 2) := by
    rw [Finset.prod_congr rfl (g := fun _ => (n : ℝ)) (fun k hk => by
        have hkq := Finset.ne_of_mem_erase hk
        have hkp := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
        simp [hφ, hkq, hkp]),
      Finset.prod_const, Finset.card_erase_of_mem hq, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    congr 1
  rw [hp1, hq1, hrest, one_mul, one_mul]

lemma two_le_of_ne {p q : Fin M} (h : p ≠ q) : 2 ≤ M := by
  by_contra hc
  push_neg at hc
  interval_cases M
  · exact p.elim0
  · exact h (Subsingleton.elim p q)

/-- `#{j ∈ [n]^M non-injective} ≤ M² n^{M−1}`. -/
lemma card_nonInj_le :
    ∑ j : Fin M → Fin n, (if Injective j then (0 : ℝ) else 1) ≤ (M : ℝ) ^ 2 * (n : ℝ) ^ (M - 1) := by
  classical
  have hle : ∀ j : Fin M → Fin n, (if Injective j then (0 : ℝ) else 1) ≤
      ∑ p : Fin M, ∑ q : Fin M, if p ≠ q then ∑ a : Fin n,
        ((if j p = a then (1 : ℝ) else 0) * (if j q = a then (1 : ℝ) else 0)) else 0 := by
    intro j
    by_cases hj : Injective j
    · rw [if_pos hj]
      refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => ?_
      split_ifs
      · exact Finset.sum_nonneg fun a _ => by positivity
      · exact le_rfl
    · rw [if_neg hj]
      obtain ⟨p, q, hpq, hne⟩ : ∃ p q, j p = j q ∧ p ≠ q := by
        unfold Injective at hj; push_neg at hj; exact hj
      have hnn : ∀ p q : Fin M, 0 ≤ (if p ≠ q then ∑ a : Fin n,
          ((if j p = a then (1 : ℝ) else 0) * (if j q = a then (1 : ℝ) else 0)) else 0) := by
        intro p q; split_ifs
        · exact Finset.sum_nonneg fun a _ => by positivity
        · exact le_rfl
      calc (1 : ℝ) = if p ≠ q then ∑ a : Fin n,
            ((if j p = a then (1 : ℝ) else 0) * (if j q = a then (1 : ℝ) else 0)) else 0 := by
            rw [if_pos hne, Finset.sum_eq_single (j p)]
            · simp [hpq]
            · intro a _ ha; simp [Ne.symm ha]
            · intro h; exact absurd (mem_univ _) h
        _ ≤ ∑ q' : Fin M, if p ≠ q' then ∑ a : Fin n,
            ((if j p = a then (1 : ℝ) else 0) * (if j q' = a then (1 : ℝ) else 0)) else 0 :=
            Finset.single_le_sum (fun q' _ => hnn p q') (mem_univ q)
        _ ≤ _ := Finset.single_le_sum (f := fun p' => ∑ q' : Fin M, if p' ≠ q' then ∑ a : Fin n,
            ((if j p' = a then (1 : ℝ) else 0) * (if j q' = a then (1 : ℝ) else 0)) else 0)
            (fun p' _ => Finset.sum_nonneg fun q' _ => hnn p' q') (mem_univ p)
  refine (Finset.sum_le_sum fun j _ => hle j).trans ?_
  rw [Finset.sum_comm]
  have hpq : ∀ p q : Fin M, ∑ j : Fin M → Fin n, (if p ≠ q then ∑ a : Fin n,
      ((if j p = a then (1 : ℝ) else 0) * (if j q = a then (1 : ℝ) else 0)) else 0) ≤ (n : ℝ) ^ (M - 1) := by
    intro p q
    by_cases h : p ≠ q
    · simp_rw [if_pos h]
      rw [Finset.sum_comm]
      simp_rw [sum_indicator_two p q h]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h2 := two_le_of_ne h
      rw [show M - 1 = (M - 2) + 1 by omega, pow_succ, mul_comm]
    · simp_rw [if_neg h]; simp only [Finset.sum_const_zero]; positivity
  calc ∑ p : Fin M, ∑ j : Fin M → Fin n, ∑ q : Fin M, _ = ∑ p : Fin M, ∑ q : Fin M, ∑ j : Fin M → Fin n, _ := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ ≤ ∑ _p : Fin M, ∑ _q : Fin M, (n : ℝ) ^ (M - 1) :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hpq p q
    _ = (M : ℝ) ^ 2 * (n : ℝ) ^ (M - 1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma sum4_comm {α β γ δ : Type*} (s : Finset α) (t : Finset β) (u : Finset γ) (v : Finset δ)
    (F : α → β → γ → δ → ℝ) :
    ∑ x ∈ s, ∑ y ∈ t, ∑ a ∈ u, ∑ b ∈ v, F x y a b = ∑ a ∈ u, ∑ b ∈ v, ∑ x ∈ s, ∑ y ∈ t, F x y a b := by
  calc _ = ∑ x ∈ s, ∑ a ∈ u, ∑ y ∈ t, ∑ b ∈ v, F x y a b := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ a ∈ u, ∑ x ∈ s, ∑ y ∈ t, ∑ b ∈ v, F x y a b := Finset.sum_comm
    _ = ∑ a ∈ u, ∑ x ∈ s, ∑ b ∈ v, ∑ y ∈ t, F x y a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_comm

lemma sum2_comm_inner {α β γ : Type*} (s : Finset α) (t : Finset β) (u : Finset γ) (F : α → β → γ → ℝ) :
    ∑ x ∈ s, ∑ y ∈ t, ∑ q ∈ u, F x y q = ∑ q ∈ u, ∑ x ∈ s, ∑ y ∈ t, F x y q := by
  calc _ = ∑ x ∈ s, ∑ q ∈ u, ∑ y ∈ t, F x y q := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Two index tuples share at least two values (at distinct positions in each). -/
def Share2 (j j' : Fin M → Fin n) : Prop :=
  ∃ r1 r2 r1' r2' : Fin M, r1 ≠ r2 ∧ r1' ≠ r2' ∧ j r1 = j' r1' ∧ j r2 = j' r2'

open Classical in
/-- `#{(j, j') : Share2 j j'} ≤ M⁴ n^{2M−2}`. -/
lemma card_share2_le :
    ∑ j : Fin M → Fin n, ∑ j' : Fin M → Fin n, (if Share2 j j' then (1 : ℝ) else 0) ≤
      (M : ℝ) ^ 4 * (n : ℝ) ^ (2 * M - 2) := by
  classical
  set T : Fin M → Fin M → Fin M → Fin M → (Fin M → Fin n) → (Fin M → Fin n) → ℝ :=
    fun r1 r2 r1' r2' j j' => if r1 ≠ r2 ∧ r1' ≠ r2' then
      (∑ a : Fin n, (if j r1 = a then (1 : ℝ) else 0) * (if j' r1' = a then (1 : ℝ) else 0)) *
      (∑ b : Fin n, (if j r2 = b then (1 : ℝ) else 0) * (if j' r2' = b then (1 : ℝ) else 0)) else 0 with hT
  have hTnn : ∀ r1 r2 r1' r2' j j', 0 ≤ T r1 r2 r1' r2' j j' := by
    intro r1 r2 r1' r2' j j'
    simp only [hT]; split_ifs
    · exact mul_nonneg (Finset.sum_nonneg fun a _ => by positivity) (Finset.sum_nonneg fun a _ => by positivity)
    · exact le_rfl
  have hind : ∀ (j j' : Fin M → Fin n) (r1 r2 r1' r2' : Fin M), r1 ≠ r2 → r1' ≠ r2' →
      j r1 = j' r1' → j r2 = j' r2' → T r1 r2 r1' r2' j j' = 1 := by
    intro j j' r1 r2 r1' r2' h1 h2 h3 h4
    simp only [hT, if_pos (And.intro h1 h2)]
    rw [Finset.sum_eq_single (j r1), Finset.sum_eq_single (j r2)]
    · simp [h3, h4]
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (mem_univ _) h
    · intro a _ ha; simp [Ne.symm ha]
    · intro h; exact absurd (mem_univ _) h
  have hle : ∀ j j' : Fin M → Fin n, (if Share2 j j' then (1 : ℝ) else 0) ≤
      ∑ r1, ∑ r2, ∑ r1', ∑ r2', T r1 r2 r1' r2' j j' := by
    intro j j'
    by_cases hs : Share2 j j'
    · rw [if_pos hs]
      obtain ⟨r1, r2, r1', r2', h1, h2, h3, h4⟩ := hs
      rw [← hind j j' r1 r2 r1' r2' h1 h2 h3 h4]
      refine (Finset.single_le_sum (fun r2' _ => hTnn r1 r2 r1' r2' j j') (mem_univ r2')).trans ?_
      refine (Finset.single_le_sum (f := fun x => ∑ r2', T r1 r2 x r2' j j')
        (fun x _ => Finset.sum_nonneg fun _ _ => hTnn _ _ _ _ _ _) (mem_univ r1')).trans ?_
      refine (Finset.single_le_sum (f := fun x => ∑ r1', ∑ r2', T r1 x r1' r2' j j')
        (fun x _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hTnn _ _ _ _ _ _)
        (mem_univ r2)).trans ?_
      exact Finset.single_le_sum (f := fun x => ∑ r2, ∑ r1', ∑ r2', T x r2 r1' r2' j j')
        (fun x _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          hTnn _ _ _ _ _ _) (mem_univ r1)
    · rw [if_neg hs]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => hTnn _ _ _ _ _ _
  have hsumT : ∀ r1 r2 r1' r2' : Fin M,
      ∑ j : Fin M → Fin n, ∑ j' : Fin M → Fin n, T r1 r2 r1' r2' j j' ≤ (n : ℝ) ^ (2 * M - 2) := by
    intro r1 r2 r1' r2'
    by_cases hc : r1 ≠ r2 ∧ r1' ≠ r2'
    · have hM := two_le_of_ne hc.1
      have hexp : ∀ j j' : Fin M → Fin n, T r1 r2 r1' r2' j j' = ∑ a : Fin n, ∑ b : Fin n,
          ((if j r1 = a then (1 : ℝ) else 0) * (if j r2 = b then (1 : ℝ) else 0)) *
          ((if j' r1' = a then (1 : ℝ) else 0) * (if j' r2' = b then (1 : ℝ) else 0)) := by
        intro j j'
        simp only [hT, if_pos hc]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring
      simp_rw [hexp]
      calc ∑ j : Fin M → Fin n, ∑ j' : Fin M → Fin n, ∑ a : Fin n, ∑ b : Fin n,
            ((if j r1 = a then (1 : ℝ) else 0) * (if j r2 = b then (1 : ℝ) else 0)) *
            ((if j' r1' = a then (1 : ℝ) else 0) * (if j' r2' = b then (1 : ℝ) else 0))
          = ∑ a : Fin n, ∑ b : Fin n,
            (∑ j : Fin M → Fin n, (if j r1 = a then (1 : ℝ) else 0) * (if j r2 = b then (1 : ℝ) else 0)) *
            (∑ j' : Fin M → Fin n, (if j' r1' = a then (1 : ℝ) else 0) * (if j' r2' = b then (1 : ℝ) else 0)) := by
            simp_rw [Finset.sum_mul_sum]
            exact sum4_comm _ _ _ _ _
        _ = ∑ _a : Fin n, ∑ _b : Fin n, (n : ℝ) ^ (M - 2) * (n : ℝ) ^ (M - 2) := by
            simp_rw [sum_indicator_two r1 r2 hc.1, sum_indicator_two r1' r2' hc.2]
        _ = (n : ℝ) ^ (2 * M - 2) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [← pow_add, show 2 * M - 2 = (M - 2 + (M - 2)) + 2 by omega, pow_add]
            ring
        _ ≤ (n : ℝ) ^ (2 * M - 2) := le_rfl
    · simp only [hT, if_neg hc, Finset.sum_const_zero]; positivity
  calc ∑ j : Fin M → Fin n, ∑ j' : Fin M → Fin n, (if Share2 j j' then (1 : ℝ) else 0)
      ≤ ∑ j : Fin M → Fin n, ∑ j' : Fin M → Fin n, ∑ r1, ∑ r2, ∑ r1', ∑ r2', T r1 r2 r1' r2' j j' :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ => hle j j'
    _ = ∑ r1, ∑ r2, ∑ r1', ∑ r2', ∑ j : Fin M → Fin n, ∑ j' : Fin M → Fin n, T r1 r2 r1' r2' j j' := by
        rw [sum2_comm_inner]
        refine Finset.sum_congr rfl fun r1 _ => ?_
        rw [sum2_comm_inner]
        refine Finset.sum_congr rfl fun r2 _ => ?_
        rw [sum2_comm_inner]
        refine Finset.sum_congr rfl fun r1' _ => ?_
        rw [sum2_comm_inner]
    _ ≤ ∑ _r1 : Fin M, ∑ _r2 : Fin M, ∑ _r1' : Fin M, ∑ _r2' : Fin M, (n : ℝ) ^ (2 * M - 2) :=
        Finset.sum_le_sum fun r1 _ => Finset.sum_le_sum fun r2 _ => Finset.sum_le_sum fun r1' _ =>
          Finset.sum_le_sum fun r2' _ => hsumT r1 r2 r1' r2'
    _ = (M : ℝ) ^ 4 * (n : ℝ) ^ (2 * M - 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Count

/-! ### Orthogonality and the second-moment bound -/

section Moment
variable {Z : Type*} [MeasurableSpace Z] {P0 : Measure Z} [IsProbabilityMeasure P0] {M : ℕ}

/-- If `F` does not depend on the coordinates `j'(k)`, `k ≠ r'`, and `g` is first-order degenerate, then
`∫ F(z) g(z ∘ j') = 0`. -/
lemma integral_mul_deg_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {g : (Fin M → Z) → ℝ}
    (hg : Measurable g) {Bg : ℝ} (hgB : ∀ u, |g u| ≤ Bg)
    (hdeg : ∀ r c, ∫ u, g (update u r c) ∂(Measure.pi fun _ : Fin M => P0) = 0)
    {F : (ι → Z) → ℝ} (hF : Measurable F) {BF : ℝ} (hFB : ∀ z, |F z| ≤ BF)
    {j' : Fin M → ι} (hj' : Injective j') (r' : Fin M)
    (hinv : ∀ z w, F (mixPi ((univ.erase r').image j') z w) = F z) :
    ∫ z, F z * g (z ∘ j') ∂(Measure.pi fun _ : ι => P0) = 0 := by
  set B := (univ.erase r').image j' with hBdef
  set ν := Measure.pi fun _ : ι => P0 with hν
  have hmp := measurePreserving_mixPi P0 B
  have hcj : Measurable (fun z : ι → Z => z ∘ j') := measurable_pi_iff.2 fun k => measurable_pi_apply _
  have hG : Measurable (fun z => F z * g (z ∘ j')) := hF.mul (hg.comp hcj)
  rw [integral_eq_of_measurePreserving hmp hG]
  have hcomp : ∀ z w : ι → Z, (mixPi B z w) ∘ j' = update (w ∘ j') r' (z (j' r')) := by
    intro z w; funext k
    by_cases hk : k = r'
    · subst hk
      have : j' k ∉ B := by
        rw [hBdef, mem_image]; rintro ⟨k', hk', h⟩
        exact (Finset.ne_of_mem_erase hk') (hj' h)
      simp [mixPi, this]
    · have : j' k ∈ B := mem_image.2 ⟨k, mem_erase.2 ⟨hk, mem_univ _⟩, rfl⟩
      simp [mixPi, this, update_of_ne hk]
  simp_rw [hinv, hcomp]
  have hu : Measurable (fun p : (ι → Z) × (ι → Z) => update (p.2 ∘ j') r' (p.1 (j' r'))) :=
    measurable_update'.comp ((hcj.comp measurable_snd).prodMk ((measurable_pi_apply _).comp measurable_fst))
  rw [integral_prod (fun x : (ι → Z) × (ι → Z) => F x.1 * g (update (x.2 ∘ j') r' (x.1 (j' r'))))
    (integrable_of_abs_le (f := fun x : (ι → Z) × (ι → Z) => F x.1 * g (update (x.2 ∘ j') r' (x.1 (j' r'))))
    ((hF.comp measurable_fst).mul (hg.comp hu)) (C := BF * Bg)
    fun p => by
      rw [abs_mul]
      exact mul_le_mul (hFB _) (hgB _) (abs_nonneg _) ((abs_nonneg _).trans (hFB p.1)))]
  refine integral_eq_zero_of_ae (ae_of_all _ fun z => ?_)
  simp only [Pi.zero_apply]
  rw [integral_const_mul]
  have hmc := measurePreserving_comp_inj P0 j' hj'
  have hgu : Measurable (fun u : Fin M → Z => g (update u r' (z (j' r')))) :=
    hg.comp (measurable_update' (a := r') |>.comp (measurable_id.prodMk measurable_const))
  have : ∫ w, g (update (w ∘ j') r' (z (j' r'))) ∂ν = ∫ u, g (update u r' (z (j' r')))
      ∂(Measure.pi fun _ : Fin M => P0) := by
    exact (integral_eq_of_measurePreserving hmc hgu).symm
  rw [this, hdeg, mul_zero]

/-- Orthogonality: injective tuples sharing at most one value contribute nothing. -/
lemma integral_pair_eq_zero {n : ℕ} (hM : 1 ≤ M) {g : (Fin M → Z) → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ u, |g u| ≤ B) (hdeg : ∀ r c, ∫ u, g (update u r c) ∂(Measure.pi fun _ : Fin M => P0) = 0)
    {j j' : Fin M → Fin n} (hj' : Injective j') (hns : ¬ Share2 j j') :
    ∫ z, g (z ∘ j) * g (z ∘ j') ∂(Measure.pi fun _ : Fin n => P0) = 0 := by
  obtain ⟨r', hr'⟩ : ∃ r' : Fin M, ∀ k, k ≠ r' → ∀ l, j l ≠ j' k := by
    by_cases h : ∃ k0 l0, j l0 = j' k0
    · obtain ⟨k0, l0, h0⟩ := h
      refine ⟨k0, fun k hk l hl => hns ⟨l0, l, k0, k, ?_, Ne.symm hk, h0, hl⟩⟩
      intro hll
      subst hll
      exact hk (hj' (h0.symm.trans hl)).symm
    · push_neg at h
      exact ⟨⟨0, hM⟩, fun k _ l => h k l⟩
  have hcj : Measurable (fun z : Fin n → Z => z ∘ j) := measurable_pi_iff.2 fun k => measurable_pi_apply _
  refine integral_mul_deg_eq_zero (F := fun z : Fin n → Z => g (z ∘ j)) hg hB hdeg (hg.comp hcj)
    (fun z => hB _) hj' r' fun z w => ?_
  show g ((mixPi _ z w) ∘ j) = g (z ∘ j)
  congr 1
  funext l
  have : j l ∉ (univ.erase r').image j' := by
    rw [mem_image]; rintro ⟨k, hk, h⟩
    exact hr' k (Finset.ne_of_mem_erase hk) l h.symm
  simp [mixPi, this]

/-- The second moment of a degenerate V-statistic: `∫ (V_n g)² ≤ 4 M⁴ B² / n²`. -/
theorem integral_vstat_deg_sq_le (hM : 1 ≤ M) {n : ℕ} (hn : 1 ≤ n) {g : (Fin M → Z) → ℝ} (hg : Measurable g)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ u, |g u| ≤ B)
    (hdeg : ∀ r c, ∫ u, g (update u r c) ∂(Measure.pi fun _ : Fin M => P0) = 0) :
    ∫ z, (vstat g z) ^ 2 ∂(Measure.pi fun _ : Fin n => P0) ≤ 4 * (M : ℝ) ^ 4 * B ^ 2 / (n : ℝ) ^ 2 := by
  classical
  set ν := Measure.pi fun _ : Fin n => P0 with hν
  set I := univ.filter (fun j : Fin M → Fin n => Injective j) with hI
  set N := univ.filter (fun j : Fin M → Fin n => ¬ Injective j) with hN
  set A : (Fin n → Z) → ℝ := fun z => ∑ j ∈ I, g (z ∘ j) with hA
  set C : (Fin n → Z) → ℝ := fun z => ∑ j ∈ N, g (z ∘ j) with hC
  have hcj : ∀ j : Fin M → Fin n, Measurable (fun z : Fin n → Z => g (z ∘ j)) := fun j =>
    hg.comp (measurable_pi_iff.2 fun k => measurable_pi_apply _)
  have hAm : Measurable A := Finset.measurable_sum _ fun j _ => hcj j
  have hCm : Measurable C := Finset.measurable_sum _ fun j _ => hcj j
  set c : ℝ := ((n : ℝ) ^ M)⁻¹ with hc
  have hsplit : ∀ z, vstat g z = c * (A z + C z) := by
    intro z; unfold vstat; rw [hA, hC, hI, hN, Finset.sum_filter_add_sum_filter_not]
  set K : ℝ := B * ((M : ℝ) ^ 2 * (n : ℝ) ^ (M - 1)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hCb : ∀ z, |C z| ≤ K := by
    intro z
    calc |C z| ≤ ∑ j ∈ N, |g (z ∘ j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ N, B := Finset.sum_le_sum fun j _ => hB _
      _ = B * ∑ j : Fin M → Fin n, (if Injective j then (0 : ℝ) else 1) := by
          rw [hN, Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> simp
      _ ≤ K := mul_le_mul_of_nonneg_left card_nonInj_le hB0
  have hAb : ∀ z, |A z| ≤ I.card * B := by
    intro z
    calc |A z| ≤ ∑ j ∈ I, |g (z ∘ j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ I, B := Finset.sum_le_sum fun j _ => hB _
      _ = I.card * B := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the injective part
  have hpair : ∀ j ∈ I, ∀ j' ∈ I, ∫ z, g (z ∘ j) * g (z ∘ j') ∂ν ≤ B ^ 2 * (if Share2 j j' then 1 else 0) := by
    intro j _ j' hj'
    by_cases hs : Share2 j j'
    · rw [if_pos hs, mul_one]
      refine le_trans (le_abs_self _) (abs_integral_le_of_abs_le fun z => ?_)
      rw [abs_mul, sq]
      exact mul_le_mul (hB _) (hB _) (abs_nonneg _) hB0
    · rw [if_neg hs, mul_zero, integral_pair_eq_zero hM hg hB hdeg (mem_filter.1 hj').2 hs]
  have hA2 : ∫ z, (A z) ^ 2 ∂ν ≤ B ^ 2 * ((M : ℝ) ^ 4 * (n : ℝ) ^ (2 * M - 2)) := by
    have hsq : ∀ z, (A z) ^ 2 = ∑ j ∈ I, ∑ j' ∈ I, g (z ∘ j) * g (z ∘ j') := by
      intro z; rw [hA, sq, Finset.sum_mul_sum]
    have hint : ∀ j j' : Fin M → Fin n, Integrable (fun z => g (z ∘ j) * g (z ∘ j')) ν := fun j j' =>
      integrable_of_abs_le ((hcj j).mul (hcj j')) (C := B * B) fun z => by
        rw [abs_mul]; exact mul_le_mul (hB _) (hB _) (abs_nonneg _) hB0
    simp_rw [hsq]
    rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun j' _ => hint j j']
    calc ∑ j ∈ I, ∫ z, ∑ j' ∈ I, g (z ∘ j) * g (z ∘ j') ∂ν
        = ∑ j ∈ I, ∑ j' ∈ I, ∫ z, g (z ∘ j) * g (z ∘ j') ∂ν := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_finset_sum _ fun j' _ => hint j j']
      _ ≤ ∑ j ∈ I, ∑ j' ∈ I, B ^ 2 * (if Share2 j j' then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun j' hj' => hpair j hj j' hj'
      _ ≤ ∑ j : Fin M → Fin n, ∑ j' : Fin M → Fin n, B ^ 2 * (if Share2 j j' then (1 : ℝ) else 0) := by
          refine (Finset.sum_le_sum fun j _ => Finset.sum_le_sum_of_subset_of_nonneg (subset_univ I)
            fun j' _ _ => by positivity).trans ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ I) fun j _ _ =>
            Finset.sum_nonneg fun j' _ => by positivity
      _ = B ^ 2 * ∑ j : Fin M → Fin n, ∑ j' : Fin M → Fin n, (if Share2 j j' then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
      _ ≤ B ^ 2 * ((M : ℝ) ^ 4 * (n : ℝ) ^ (2 * M - 2)) := mul_le_mul_of_nonneg_left card_share2_le (by positivity)
  -- assemble
  have hpt : ∀ z, (vstat g z) ^ 2 ≤ c ^ 2 * (2 * (A z) ^ 2 + 2 * K ^ 2) := by
    intro z
    rw [hsplit, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hC2 : (C z) ^ 2 ≤ K ^ 2 := sq_le_sq' (abs_le.1 (hCb z)).1 (abs_le.1 (hCb z)).2
    nlinarith [sq_nonneg (A z - C z)]
  have hint2 : Integrable (fun z => c ^ 2 * (2 * (A z) ^ 2 + 2 * K ^ 2)) ν :=
    integrable_of_abs_le ((((hAm.pow_const 2).const_mul 2).add_const _).const_mul _)
      (C := c ^ 2 * (2 * (I.card * B) ^ 2 + 2 * K ^ 2)) fun z => by
        rw [abs_of_nonneg (by positivity)]
        have : (A z) ^ 2 ≤ (I.card * B) ^ 2 := sq_le_sq' (abs_le.1 (hAb z)).1 (abs_le.1 (hAb z)).2
        gcongr
  have hvm : Measurable (fun z : Fin n → Z => (vstat g z) ^ 2) := by
    simp_rw [hsplit]; exact ((hAm.add hCm).const_mul _).pow_const 2
  calc ∫ z, (vstat g z) ^ 2 ∂ν ≤ ∫ z, c ^ 2 * (2 * (A z) ^ 2 + 2 * K ^ 2) ∂ν :=
        integral_mono (integrable_of_abs_le hvm (C := c ^ 2 * (2 * (I.card * B) ^ 2 + 2 * K ^ 2)) fun z => by
          rw [abs_of_nonneg (sq_nonneg _)]
          refine (hpt z).trans ?_
          have : (A z) ^ 2 ≤ (I.card * B) ^ 2 := sq_le_sq' (abs_le.1 (hAb z)).1 (abs_le.1 (hAb z)).2
          gcongr) hint2 hpt
    _ = c ^ 2 * (2 * ∫ z, (A z) ^ 2 ∂ν + 2 * K ^ 2) := by
        rw [integral_const_mul, integral_add, integral_const_mul, integral_const, probReal_univ, one_smul]
        · exact ((integrable_of_abs_le (hAm.pow_const 2) (C := (I.card * B) ^ 2) fun z => by
            rw [abs_of_nonneg (sq_nonneg _)]
            exact sq_le_sq' (abs_le.1 (hAb z)).1 (abs_le.1 (hAb z)).2).const_mul 2)
        · exact integrable_const _
    _ ≤ c ^ 2 * (2 * (B ^ 2 * ((M : ℝ) ^ 4 * (n : ℝ) ^ (2 * M - 2))) + 2 * K ^ 2) := by gcongr
    _ = 4 * (M : ℝ) ^ 4 * B ^ 2 / (n : ℝ) ^ 2 := by
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
        have hpow : (n : ℝ) ^ (2 * M - 2) * (n : ℝ) ^ 2 = ((n : ℝ) ^ M) ^ 2 := by
          rw [← pow_add, ← pow_mul, show 2 * M - 2 + 2 = M * 2 by omega]
        have hpow2 : ((n : ℝ) ^ (M - 1)) ^ 2 = (n : ℝ) ^ (2 * M - 2) := by
          rw [← pow_mul, show (M - 1) * 2 = 2 * M - 2 by omega]
        rw [hK, hc, mul_pow, mul_pow, hpow2]
        field_simp
        rw [← hpow]
        ring

end Moment

/-! ### Transfer to i.i.d. sequences -/

section Transfer
variable {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {P0 : Measure Z} {X : ℕ → Ω → Z}

/-- The law of the first `n` points of an i.i.d. `P₀` sequence is `P₀^{⊗n}`. -/
lemma map_restrict_eq_pi (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P) (hXl : ∀ i, P.map (X i) = P0)
    (n : ℕ) : P.map (fun ω (i : Fin n) => X i ω) = Measure.pi fun _ : Fin n => P0 := by
  have h := (iIndepFun_iff_map_fun_eq_pi_map (f := fun i : Fin n => X i) (fun i => (hXm i).aemeasurable)).1
    (hXi.precomp Fin.val_injective)
  rw [h]
  congr
  funext i
  exact hXl i

lemma measurable_restrict (hXm : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (fun ω (i : Fin n) => X i ω) := measurable_pi_iff.2 fun i => hXm i

/-- `E_P[Φ(Z_0, …, Z_{n−1})] = ∫ Φ dP₀^{⊗n}`. -/
lemma integral_restrict_eq (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P) (hXl : ∀ i, P.map (X i) = P0)
    {n : ℕ} {Φ : (Fin n → Z) → ℝ} (hΦ : Measurable Φ) :
    ∫ ω, Φ (fun i => X i ω) ∂P = ∫ z, Φ z ∂(Measure.pi fun _ : Fin n => P0) := by
  rw [← map_restrict_eq_pi hXm hXi hXl n,
    integral_map (measurable_restrict hXm n).aemeasurable hΦ.aestronglyMeasurable]

variable [IsProbabilityMeasure P0] {M : ℕ}

lemma vstat_sub_eq {n : ℕ} (hn : 1 ≤ n) (hM : 1 ≤ M) (f : (Fin M → Z) → ℝ) (z : Fin n → Z) :
    vstat f z - hMean P0 f - (n : ℝ)⁻¹ * ∑ a : Fin n, ∑ r, (hProj P0 f r (z a) - hMean P0 f) =
      vstat (hRem P0 f) z := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold vstat hRem
  have hc : ∀ j : Fin M → Fin n, (z ∘ j) = fun k => z (j k) := fun j => rfl
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, Finset.sum_comm (s := (univ : Finset (Fin M → Fin n)))]
  have hce : ∀ r : Fin M, ∑ j : Fin M → Fin n, (hProj P0 f r ((z ∘ j) r) - hMean P0 f) =
      (n : ℝ) ^ (M - 1) * ∑ a : Fin n, (hProj P0 f r (z a) - hMean P0 f) :=
    fun r => sum_comp_eval (fun a => hProj P0 f r (z a) - hMean P0 f) r
  simp_rw [hce]
  rw [Finset.sum_comm (s := (univ : Finset (Fin n))), ← Finset.mul_sum]
  obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
  simp only [Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_pow]
  field_simp
  ring

/-- Hoeffding's decomposition for one-sample V-statistics:
`E[(V_n f − θ − n^{−1} Σ_a Σ_r (f_r(Z_a) − θ))²] ≤ 4 M⁴ ((2M+2)B)² / n²`. -/
theorem vstat_hoeffding_sq_le (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P)
    (hXl : ∀ i, P.map (X i) = P0) (hM : 1 ≤ M) {n : ℕ} (hn : 1 ≤ n) {f : (Fin M → Z) → ℝ} (hf : Measurable f)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ u, |f u| ≤ B) :
    ∫ ω, (vstat f (fun i : Fin n => X i ω) - hMean P0 f -
        (n : ℝ)⁻¹ * ∑ a : Fin n, ∑ r, (hProj P0 f r (X a ω) - hMean P0 f)) ^ 2 ∂P ≤
      4 * (M : ℝ) ^ 4 * ((2 * M + 2) * B) ^ 2 / (n : ℝ) ^ 2 := by
  simp_rw [fun ω => vstat_sub_eq (P0 := P0) hn hM f (fun i : Fin n => X i ω)]
  have hvm : Measurable (fun z : Fin n → Z => (vstat (hRem P0 f) z) ^ 2) := by
    unfold vstat
    exact ((Finset.measurable_sum _ fun j _ =>
      (measurable_hRem hf).comp (measurable_pi_iff.2 fun k => measurable_pi_apply _)).const_mul _).pow_const 2
  rw [integral_restrict_eq hXm hXi hXl hvm]
  exact integral_vstat_deg_sq_le hM hn (measurable_hRem hf) (by positivity) (abs_hRem_le hB)
    (hRem_deg hf hB)

end Transfer

end StatFormal.Foundations.CLT
