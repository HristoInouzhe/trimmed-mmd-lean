import StatFormal.Lib.DKW.MassartCalc
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Order.IsLUB
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The Dvoretzky–Kiefer–Wolfowitz–Massart inequality with Massart's sharp constant

For a measurable score `V : X → [0, ∞]`, an i.i.d. sample `y ∼ μ^{⊗n}` (`Measure.pi`), `Ĝ(s) = #{i : V(y_i) ≤ s}/n`
and `G(s) = μ(V ≤ s)`, for every `t ≥ 0`:
* `massart_upper`: `P(∃ s, t < Ĝ(s) − G(s)) ≤ e^{−2nt²}`;
* `massart_lower`: `P(∃ s, t < G(s) − Ĝ(s)) ≤ e^{−2nt²}`;
* `massart`: `P(∃ s, t < |Ĝ(s) − G(s)|) ≤ 2e^{−2nt²}` (Massart 1990).
No continuity of `G` is assumed, and the one-sided bounds hold without Massart's restriction on `t` (as in Reeve,
arXiv:2403.16651).

Route (the discrete-time exponential-tilt argument of J.-Y. Le Boudec, arXiv:2607.04387, with the reverse martingale
replaced by an explicit change of measure on the product space, and Sion's theorem by `MassartCalc.exists_lambda`):
* Levels `i ∈ [⌊nt⌋ + 1, n]`, `u_i = i/n − t`; nested sets `A_i = {x : G(V x) < u_i}` with `μ(A_i) ≤ u_i`
  (probability integral transform `pit_upper`, no continuity needed); the event is contained in
  `⋃_i {#{k : y_k ∈ A_i} ≥ i}`.
* `tilt_core`: with `ν_i = μ + (λ/μ(A_i)) μ|_{A_i}` (total mass `1 + λ`), the image of `ν_i` under the map
  collapsing `A_j` to a point is the same for every `i ≤ j` (`map_tilt`); so the product laws `ν_i^{⊗n}` agree on
  events determined by the sample outside `A_j` and the number of points inside, in particular on
  `E_j = {j = the largest level reached}`. On `E_j` the density `∏_k dν_j/dμ(y_k) ≥ (1 + λ/u_j)^j`
  (`pi_withDensity`). Summing over the disjoint `E_j`: `P(event) ≤ (1 + λ)^n / min_j (1 + λ/u_j)^j`.
* `MassartCalc.exists_lambda`: one `λ` makes this `≤ e^{−2nt²}`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Classical

namespace StatFormal.DKW.Massart

variable {X : Type*} [MeasurableSpace X]

/-! ### Products of densities -/

/-- `(μ.withDensity f)^{⊗n} = μ^{⊗n}.withDensity (∏_k f(y_k))`. -/
lemma pi_withDensity {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    [IsFiniteMeasure (μ.withDensity f)] :
    Measure.pi (fun _ : Fin n => μ.withDensity f) =
      (Measure.pi fun _ : Fin n => μ).withDensity (fun y => ∏ k, f (y k)) := by
  refine Measure.pi_eq fun s hs => ?_
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hbox, ← lintegral_indicator hbox]
  have hfun : (Set.univ.pi s).indicator (fun y : Fin n → X => ∏ k, f (y k)) =
      fun y => ∏ k, (s k).indicator f (y k) := by
    funext y
    by_cases hy : y ∈ Set.univ.pi s
    · rw [indicator_of_mem hy]
      exact Finset.prod_congr rfl fun k _ => (indicator_of_mem (hy k (Set.mem_univ k)) f).symm
    · rw [indicator_of_notMem hy]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hy
      obtain ⟨k, hk⟩ := hy
      exact (Finset.prod_eq_zero (Finset.mem_univ k) (indicator_of_notMem hk f)).symm
  rw [hfun]
  refine (lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun (k : Fin n) (y : Fin n → X) => (s k).indicator f (y k))
    (iIndepFun_pi (X := fun k => (s k).indicator f) fun k => (hf.indicator (hs k)).aemeasurable)
    (fun k => (hf.indicator (hs k)).comp (measurable_pi_apply (X := fun _ : Fin n => X) k))).trans ?_
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [withDensity_apply _ (hs k), ← lintegral_indicator (hs k)]
  exact (measurePreserving_eval (fun _ : Fin n => μ) k).lintegral_comp (hf.indicator (hs k))

/-! ### Collapsing a set to a point -/

/-- Collapse `A` to the extra point `inr ()`. -/
def collapse (A : Set X) (x : X) : X ⊕ Unit := if x ∈ A then Sum.inr () else Sum.inl x

lemma measurable_collapse {A : Set X} (hA : MeasurableSet A) : Measurable (collapse A) := by
  unfold collapse
  exact Measurable.ite hA measurable_const measurable_inl

/-- The image of `B ⊇ A` after collapsing `A`. -/
def tag (B : Set X) : Set (X ⊕ Unit) := Sum.inl '' B ∪ Set.range Sum.inr

lemma collapse_mem_tag {A B : Set X} (hAB : A ⊆ B) (x : X) : collapse A x ∈ tag B ↔ x ∈ B := by
  unfold collapse tag
  by_cases h : x ∈ A
  · simp [h, hAB h]
  · simp [h]

lemma measurableSet_tag {B : Set X} (hB : MeasurableSet B) : MeasurableSet (tag B) :=
  (measurableSet_inl_image.2 hB).union measurableSet_range_inr

/-! ### Counting -/

/-- `#{k : y_k ∈ A}`. -/
def cnt {β : Type*} {n : ℕ} (A : Set β) (y : Fin n → β) : ℕ := (Finset.univ.filter fun k => y k ∈ A).card

lemma measurable_cnt {β : Type*} [MeasurableSpace β] {n : ℕ} {A : Set β} (hA : MeasurableSet A) :
    Measurable (cnt (n := n) A) := by
  unfold cnt
  simp_rw [Finset.card_filter]
  exact Finset.measurable_sum _ fun k _ =>
    Measurable.ite (measurable_pi_apply k hA) measurable_const measurable_const

lemma cnt_collapse {n : ℕ} {A B : Set X} (hAB : A ⊆ B) (y : Fin n → X) :
    cnt (tag B) (fun k => collapse A (y k)) = cnt B y := by
  unfold cnt
  congr 1
  exact Finset.filter_congr fun k _ => collapse_mem_tag hAB (y k)

lemma cnt_le {β : Type*} {n : ℕ} (A : Set β) (y : Fin n → β) : cnt A y ≤ n := by
  unfold cnt
  exact (Finset.card_filter_le _ _).trans (by simp)

/-! ### Tilted measures -/

variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- `μ + κ μ|_A`. -/
def tilt (κ : ℝ≥0∞) (A : Set X) : Measure X := μ + κ • μ.restrict A

lemma tilt_eq_withDensity {κ : ℝ≥0∞} {A : Set X} (hA : MeasurableSet A) :
    tilt μ κ A = μ.withDensity (fun x => if x ∈ A then 1 + κ else 1) := by
  have : (fun x => if x ∈ A then 1 + κ else 1) = (1 : X → ℝ≥0∞) + A.indicator (fun _ => κ) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx, add_comm]
  rw [this, withDensity_add_left measurable_one, withDensity_one, withDensity_indicator hA, withDensity_const]
  rfl

lemma tilt_univ (κ : ℝ≥0∞) (A : Set X) : tilt μ κ A Set.univ = 1 + κ * μ A := by
  simp [tilt]

lemma isFiniteMeasure_tilt {κ : ℝ≥0∞} (hκ : κ ≠ ∞) (A : Set X) : IsFiniteMeasure (tilt μ κ A) :=
  ⟨by rw [tilt_univ]; exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top,
    ENNReal.mul_lt_top hκ.lt_top (measure_lt_top μ A)⟩⟩

/-- After collapsing `B ⊇ A`, the tilt only remembers its total extra mass `κ μ(A)`. -/
lemma map_tilt {κ : ℝ≥0∞} {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    (tilt μ κ A).map (collapse B) = μ.map (collapse B) + (κ * μ A) • Measure.dirac (Sum.inr ()) := by
  unfold tilt
  rw [Measure.map_add _ _ (measurable_collapse hB), Measure.map_smul _ (measurable_collapse hB).aemeasurable]
  have hc : collapse B =ᵐ[μ.restrict A] fun _ => Sum.inr () := by
    refine (ae_restrict_iff' hA).2 (Eventually.of_forall fun x hx => ?_)
    simp [collapse, hAB hx]
  rw [Measure.map_congr hc, Measure.map_const, Measure.restrict_apply_univ, smul_smul]

/-! ### The change-of-measure core -/

lemma null_level {n i : ℕ} (hi : 1 ≤ i) {A : Set X} (hA0 : μ A = 0) :
    (Measure.pi fun _ : Fin n => μ) {y | i ≤ cnt A y} = 0 := by
  refine measure_mono_null (t := ⋃ k, Function.eval k ⁻¹' A) ?_
    (measure_iUnion_null fun k => Measure.pi_eval_preimage_null _ hA0)
  intro y hy
  have hpos : 0 < cnt A y := lt_of_lt_of_le hi hy
  unfold cnt at hpos
  obtain ⟨k, hk⟩ := Finset.card_pos.1 hpos
  exact Set.mem_iUnion.2 ⟨k, (Finset.mem_filter.1 hk).2⟩

/-- **Core inequality, all masses positive.** -/
theorem tilt_core_pos {n : ℕ} (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) (hmono : Monotone A)
    (a b : ℕ) (u : ℕ → ℝ) (hpos : ∀ i ∈ Finset.Icc a b, 0 < μ.real (A i))
    (hμA : ∀ i ∈ Finset.Icc a b, μ.real (A i) ≤ u i)
    (l C : ℝ) (hl : 0 < l) (hC : ∀ i ∈ Finset.Icc a b, (1 + l) ^ n ≤ C * (1 + l / u i) ^ i) :
    (Measure.pi fun _ : Fin n => μ) {y | ∃ i ∈ Finset.Icc a b, i ≤ cnt (A i) y} ≤ ENNReal.ofReal C := by
  set P := Measure.pi fun _ : Fin n => μ with hPdef
  rcases Nat.lt_or_ge b a with hba | hab
  · have : {y : Fin n → X | ∃ i ∈ Finset.Icc a b, i ≤ cnt (A i) y} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro i hi
      exact absurd ((Finset.mem_Icc.1 hi).1.trans (Finset.mem_Icc.1 hi).2) (not_le.2 hba)
    rw [this, measure_empty]
    exact bot_le
  have haI : a ∈ Finset.Icc a b := Finset.mem_Icc.2 ⟨le_rfl, hab⟩
  have hu : ∀ i ∈ Finset.Icc a b, 0 < u i := fun i hi => (hpos i hi).trans_le (hμA i hi)
  have hC0 : 0 ≤ C := by
    have h1 := hC a haI
    have h2 : 0 < (1 + l) ^ n := by positivity
    have h3 : 0 < (1 + l / u a) ^ a := by have := hu a haI; positivity
    by_contra hc
    push_neg at hc
    nlinarith [mul_neg_of_neg_of_pos hc h3]
  set κ : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (l / μ.real (A i)) with hκ
  set ν : ℕ → Measure X := fun i => tilt μ (κ i) (A i) with hν
  have hfin : ∀ i, IsFiniteMeasure (ν i) := fun i => isFiniteMeasure_tilt μ ENNReal.ofReal_ne_top _
  have hμAi : ∀ i, μ (A i) = ENNReal.ofReal (μ.real (A i)) := fun i => (ofReal_measureReal).symm
  have hκA : ∀ i ∈ Finset.Icc a b, κ i * μ (A i) = ENNReal.ofReal l := by
    intro i hi
    rw [hμAi, hκ, ← ENNReal.ofReal_mul (by have := hpos i hi; positivity)]
    congr 1
    field_simp [(hpos i hi).ne']
  have hmapν : ∀ c ∈ Finset.Icc a b, ∀ j, c ≤ j → (ν c).map (collapse (A j)) =
      μ.map (collapse (A j)) + ENNReal.ofReal l • Measure.dirac (Sum.inr ()) := by
    intro c hc j hcj
    rw [hν, map_tilt μ (hA c) (hA j) (hmono hcj), hκA c hc]
  -- the events `E_j = {j is the largest level reached}`
  set E : ℕ → Set (Fin n → X) := fun j =>
    {y | j ≤ cnt (A j) y} ∩ ⋂ i ∈ Finset.Ioc j b, {y | cnt (A i) y < i} with hE
  have hEm : ∀ j, MeasurableSet (E j) := fun j =>
    (measurableSet_le measurable_const (measurable_cnt (hA j))).inter
      (MeasurableSet.biInter (Finset.countable_toSet _) fun i _ =>
        measurableSet_lt (measurable_cnt (hA i)) measurable_const)
  have hsub : {y | ∃ i ∈ Finset.Icc a b, i ≤ cnt (A i) y} ⊆ ⋃ j ∈ Finset.Icc a b, E j := by
    rintro y ⟨i, hi, hiy⟩
    set S := (Finset.Icc a b).filter fun i => i ≤ cnt (A i) y
    have hS : S.Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, hiy⟩⟩
    have hj := Finset.max'_mem S hS
    rw [Finset.mem_filter] at hj
    refine Set.mem_iUnion₂.2 ⟨S.max' hS, hj.1, hj.2, Set.mem_iInter₂.2 fun i' hi' => ?_⟩
    by_contra hc
    simp only [Set.mem_setOf_eq, not_lt] at hc
    have hi'S : i' ∈ S := Finset.mem_filter.2 ⟨Finset.mem_Icc.2
      ⟨(Finset.mem_Icc.1 hj.1).1.trans (Finset.mem_Ioc.1 hi').1.le, (Finset.mem_Ioc.1 hi').2⟩, hc⟩
    exact absurd (Finset.le_max' S i' hi'S) (not_le.2 (Finset.mem_Ioc.1 hi').1)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc a b)) E := by
    intro j hj j' hj' hne
    have key : ∀ j j', j' ∈ Finset.Icc a b → j < j' → Disjoint (E j) (E j') := by
      intro j j' hj' h
      refine Set.disjoint_left.2 fun y hy hy' => ?_
      have h1 := Set.mem_iInter₂.1 hy.2 j' (Finset.mem_Ioc.2 ⟨h, (Finset.mem_Icc.1 hj').2⟩)
      exact absurd (show j' ≤ cnt (A j') y from hy'.1) (not_le.2 (show cnt (A j') y < j' from h1))
    rcases lt_or_gt_of_ne hne with h | h
    · exact key j j' hj' h
    · exact (key j' j hj h).symm
  -- `ν_j^{⊗n}(E_j) = ν_a^{⊗n}(E_j)`
  have hQ : ∀ j ∈ Finset.Icc a b, (Measure.pi fun _ : Fin n => ν j) (E j) =
      (Measure.pi fun _ : Fin n => ν a) (E j) := by
    intro j hj
    have haj : a ≤ j := (Finset.mem_Icc.1 hj).1
    set T : (Fin n → X) → (Fin n → X ⊕ Unit) := fun y k => collapse (A j) (y k) with hT
    have hTm : Measurable T :=
      measurable_pi_iff.mpr fun k => (measurable_collapse (hA j)).comp (measurable_pi_apply k)
    set E' : Set (Fin n → X ⊕ Unit) := {z | j ≤ cnt (tag (A j)) z} ∩
      ⋂ i ∈ Finset.Ioc j b, {z | cnt (tag (A i)) z < i} with hE'
    have hE'm : MeasurableSet E' :=
      (measurableSet_le measurable_const (measurable_cnt (measurableSet_tag (hA j)))).inter
        (MeasurableSet.biInter (Finset.countable_toSet _) fun i _ =>
          measurableSet_lt (measurable_cnt (measurableSet_tag (hA i))) measurable_const)
    have hpre : E j = T ⁻¹' E' := by
      ext y
      simp only [hE, hE', hT, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
      rw [cnt_collapse (le_refl (A j)) y]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun i hi => ?_⟩
        rw [cnt_collapse (hmono (Finset.mem_Ioc.1 hi).1.le) y]
        exact h2 i hi
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun i hi => ?_⟩
        have := h2 i hi
        rwa [cnt_collapse (hmono (Finset.mem_Ioc.1 hi).1.le) y] at this
    have hlaw : ∀ c ∈ Finset.Icc a b, c ≤ j → (Measure.pi fun _ : Fin n => ν c) (E j) =
        (Measure.pi fun _ : Fin n => μ.map (collapse (A j)) + ENNReal.ofReal l • Measure.dirac (Sum.inr ())) E' := by
      intro c hc hcj
      haveI := hfin c
      rw [hpre, ← Measure.map_apply hTm hE'm, hT,
        Measure.pi_map_pi (fun _ => (measurable_collapse (hA j)).aemeasurable), hmapν c hc j hcj]
    rw [hlaw j hj le_rfl, hlaw a haI haj]
  -- `P(E_j) (1 + λ/u_j)^j ≤ ν_j^{⊗n}(E_j)`
  have hP : ∀ j ∈ Finset.Icc a b, P (E j) * ENNReal.ofReal ((1 + l / u j) ^ j) ≤
      (Measure.pi fun _ : Fin n => ν j) (E j) := by
    intro j hj
    haveI : IsFiniteMeasure (μ.withDensity (fun x => if x ∈ A j then 1 + κ j else 1)) := by
      rw [← tilt_eq_withDensity μ (hA j)]; exact hfin j
    have hdens : Measurable fun x => if x ∈ A j then 1 + κ j else (1 : ℝ≥0∞) :=
      Measurable.ite (hA j) measurable_const measurable_const
    have hνj : ν j = μ.withDensity (fun x => if x ∈ A j then 1 + κ j else 1) := tilt_eq_withDensity μ (hA j)
    rw [hνj, pi_withDensity μ hdens, withDensity_apply _ (hEm j), mul_comm, ← setLIntegral_const]
    refine setLIntegral_mono' (hEm j) fun y hy => ?_
    have hprod : (∏ k, if y k ∈ A j then 1 + κ j else (1 : ℝ≥0∞)) = (1 + κ j) ^ cnt (A j) y := by
      rw [Finset.prod_ite]
      simp [cnt]
    rw [hprod]
    have hpj := hpos j hj
    have h1 : ENNReal.ofReal ((1 + l / u j) ^ j) ≤ (1 + κ j) ^ j := by
      rw [ENNReal.ofReal_pow (by have := hu j hj; positivity)]
      gcongr
      rw [hκ, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have : l / u j ≤ l / μ.real (A j) := div_le_div_of_nonneg_left hl.le hpj (hμA j hj)
      linarith
    exact h1.trans (pow_le_pow_right₀ le_self_add hy.1)
  -- `Σ_j ν_a^{⊗n}(E_j) ≤ (1 + λ)^n`
  have hsum : ∑ j ∈ Finset.Icc a b, (Measure.pi fun _ : Fin n => ν a) (E j) ≤ ENNReal.ofReal ((1 + l) ^ n) := by
    haveI := hfin a
    rw [← measure_biUnion_finset hdisj (fun j _ => hEm j)]
    calc _ ≤ (Measure.pi fun _ : Fin n => ν a) Set.univ := measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal ((1 + l) ^ n) := by
        rw [← Set.pi_univ, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hν,
          tilt_univ, hκA a haI, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add zero_le_one hl.le,
          ENNReal.ofReal_one]
  have hkey : ∀ j ∈ Finset.Icc a b, P (E j) * ENNReal.ofReal ((1 + l) ^ n) ≤
      ENNReal.ofReal C * (Measure.pi fun _ : Fin n => ν a) (E j) := by
    intro j hj
    have hCj : ENNReal.ofReal ((1 + l) ^ n) ≤ ENNReal.ofReal C * ENNReal.ofReal ((1 + l / u j) ^ j) := by
      rw [← ENNReal.ofReal_mul hC0]
      exact ENNReal.ofReal_le_ofReal (hC j hj)
    calc P (E j) * ENNReal.ofReal ((1 + l) ^ n)
        ≤ P (E j) * (ENNReal.ofReal C * ENNReal.ofReal ((1 + l / u j) ^ j)) := by gcongr
      _ = ENNReal.ofReal C * (P (E j) * ENNReal.ofReal ((1 + l / u j) ^ j)) := by ring
      _ ≤ ENNReal.ofReal C * (Measure.pi fun _ : Fin n => ν j) (E j) := by gcongr; exact hP j hj
      _ = ENNReal.ofReal C * (Measure.pi fun _ : Fin n => ν a) (E j) := by rw [hQ j hj]
  have hfin' : (∑ j ∈ Finset.Icc a b, P (E j)) * ENNReal.ofReal ((1 + l) ^ n) ≤
      ENNReal.ofReal C * ENNReal.ofReal ((1 + l) ^ n) := by
    rw [Finset.sum_mul]
    calc _ ≤ ∑ j ∈ Finset.Icc a b, ENNReal.ofReal C * (Measure.pi fun _ : Fin n => ν a) (E j) :=
          Finset.sum_le_sum hkey
      _ = ENNReal.ofReal C * ∑ j ∈ Finset.Icc a b, (Measure.pi fun _ : Fin n => ν a) (E j) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by gcongr
  have hne0 : ENNReal.ofReal ((1 + l) ^ n) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hsumP := (ENNReal.mul_le_mul_iff_left hne0 ENNReal.ofReal_ne_top).mp hfin'
  calc P {y | ∃ i ∈ Finset.Icc a b, i ≤ cnt (A i) y} ≤ P (⋃ j ∈ Finset.Icc a b, E j) := measure_mono hsub
    _ ≤ ∑ j ∈ Finset.Icc a b, P (E j) := measure_biUnion_finset_le _ _
    _ ≤ ENNReal.ofReal C := hsumP

/-- **Core inequality.** For nested measurable sets `A_i` with `μ(A_i) ≤ u_i` on levels `i ∈ [a, b]`, `a ≥ 1`, and
`λ > 0`: `P(∃ i ∈ [a, b], #{k : y_k ∈ A_i} ≥ i) ≤ C` whenever `(1 + λ)^n ≤ C (1 + λ/u_i)^i` for all levels. -/
theorem tilt_core {n : ℕ} (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) (hmono : Monotone A)
    (a b : ℕ) (ha : 1 ≤ a) (u : ℕ → ℝ) (hμA : ∀ i ∈ Finset.Icc a b, μ.real (A i) ≤ u i)
    (l C : ℝ) (hl : 0 < l) (hC : ∀ i ∈ Finset.Icc a b, (1 + l) ^ n ≤ C * (1 + l / u i) ^ i) :
    (Measure.pi fun _ : Fin n => μ) {y | ∃ i ∈ Finset.Icc a b, i ≤ cnt (A i) y} ≤ ENNReal.ofReal C := by
  set P := Measure.pi fun _ : Fin n => μ
  set I := (Finset.Icc a b).filter fun i => 0 < μ.real (A i) with hI
  have hnull : ∀ i ∈ Finset.Icc a b, i ∉ I → P {y | i ≤ cnt (A i) y} = 0 := by
    intro i hi hiI
    have h0 : μ.real (A i) = 0 := by
      simp only [hI, Finset.mem_filter, not_and, not_lt] at hiI
      exact le_antisymm (hiI hi) measureReal_nonneg
    have hμ0 : μ (A i) = 0 := by
      rwa [measureReal_eq_zero_iff] at h0
    exact null_level μ (ha.trans (Finset.mem_Icc.1 hi).1) hμ0
  rcases I.eq_empty_or_nonempty with hIe | hIne
  · refine le_of_eq_of_le (measure_mono_null (t := ⋃ i ∈ Finset.Icc a b, {y | i ≤ cnt (A i) y}) ?_ ?_)
      bot_le
    · rintro y ⟨i, hi, hiy⟩
      exact Set.mem_iUnion₂.2 ⟨i, hi, hiy⟩
    · exact (measure_biUnion_null_iff (Finset.countable_toSet _)).2 fun i hi =>
        hnull i hi (by rw [hIe]; exact Finset.notMem_empty i)
  · set a' := I.min' hIne
    have ha'I : a' ∈ Finset.Icc a b ∧ 0 < μ.real (A a') := Finset.mem_filter.1 (Finset.min'_mem I hIne)
    have ha'a : a ≤ a' := (Finset.mem_Icc.1 ha'I.1).1
    have hsubI : ∀ i ∈ Finset.Icc a' b, i ∈ Finset.Icc a b := fun i hi =>
      Finset.mem_Icc.2 ⟨ha'a.trans (Finset.mem_Icc.1 hi).1, (Finset.mem_Icc.1 hi).2⟩
    have hpos : ∀ i ∈ Finset.Icc a' b, 0 < μ.real (A i) := fun i hi =>
      ha'I.2.trans_le (measureReal_mono (hmono (Finset.mem_Icc.1 hi).1))
    have hmain := tilt_core_pos μ A hA hmono a' b u hpos (fun i hi => hμA i (hsubI i hi)) l C hl
      (fun i hi => hC i (hsubI i hi))
    have hsub : {y : Fin n → X | ∃ i ∈ Finset.Icc a b, i ≤ cnt (A i) y} ⊆
        {y : Fin n → X | ∃ i ∈ Finset.Icc a' b, i ≤ cnt (A i) y} ∪
          ⋃ i ∈ (Finset.Icc a b).filter (fun i => i < a'), {y : Fin n → X | i ≤ cnt (A i) y} := by
      rintro y ⟨i, hi, hiy⟩
      by_cases hia : a' ≤ i
      · exact Or.inl ⟨i, Finset.mem_Icc.2 ⟨hia, (Finset.mem_Icc.1 hi).2⟩, hiy⟩
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨i, Finset.mem_filter.2 ⟨hi, not_le.1 hia⟩, hiy⟩)
    have hN : P (⋃ i ∈ (Finset.Icc a b).filter (fun i => i < a'), {y : Fin n → X | i ≤ cnt (A i) y}) = 0 := by
      refine (measure_biUnion_null_iff (Finset.countable_toSet _)).2 fun i hi => ?_
      have hi' := Finset.mem_filter.1 hi
      refine hnull i hi'.1 fun hiI => ?_
      exact absurd (Finset.min'_le I i hiI) (not_le.2 hi'.2)
    calc P {y | ∃ i ∈ Finset.Icc a b, i ≤ cnt (A i) y} ≤ _ := measure_mono hsub
      _ ≤ P {y | ∃ i ∈ Finset.Icc a' b, i ≤ cnt (A i) y} + _ := measure_union_le _ _
      _ = P {y | ∃ i ∈ Finset.Icc a' b, i ≤ cnt (A i) y} := by rw [hN, add_zero]
      _ ≤ ENNReal.ofReal C := hmain

/-! ### Probability integral transforms (no continuity) -/

lemma meas_le_ofReal_of_iUnion {S : ℕ → Set X} (hS : Monotone S) {u : ℝ} (hu : ∀ k, μ.real (S k) < u) :
    μ (⋃ k, S k) ≤ ENNReal.ofReal u := by
  rw [hS.measure_iUnion]
  refine iSup_le fun k => ?_
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (hu k).le

/-- `μ(G(V) < u) ≤ u` for `G(v) = μ(V ≤ v)`. -/
lemma pit_upper (V : X → ℝ≥0∞) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {x | μ.real {z | V z ≤ V x} < u} ≤ u := by
  set D := {v : ℝ≥0∞ | μ.real {z | V z ≤ v} < u} with hD
  have hpre : {x | μ.real {z | V z ≤ V x} < u} = V ⁻¹' D := rfl
  rw [hpre]
  rcases D.eq_empty_or_nonempty with hDe | hDne
  · rw [hDe, Set.preimage_empty, measureReal_empty]; exact hu
  apply ENNReal.toReal_le_of_le_ofReal hu
  by_cases hm : sSup D ∈ D
  · have hsub : V ⁻¹' D ⊆ {z | V z ≤ sSup D} := fun x hx => le_sSup (show V x ∈ D from hx)
    calc μ (V ⁻¹' D) ≤ μ {z | V z ≤ sSup D} := measure_mono hsub
      _ = ENNReal.ofReal (μ.real {z | V z ≤ sSup D}) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal u := ENNReal.ofReal_le_ofReal hm.le
  · obtain ⟨w, hwm, hwt, hwD⟩ := exists_seq_tendsto_sSup hDne (OrderTop.bddAbove D)
    have hsub : V ⁻¹' D ⊆ ⋃ k, {z | V z ≤ w k} := by
      intro x hx
      have hxD : V x ∈ D := hx
      have hlt : V x < sSup D := lt_of_le_of_ne (le_sSup hxD) fun h => hm (h ▸ hxD)
      obtain ⟨k, hk⟩ := (hwt.eventually (lt_mem_nhds hlt)).exists
      exact Set.mem_iUnion.2 ⟨k, hk.le⟩
    refine (measure_mono hsub).trans (meas_le_ofReal_of_iUnion μ ?_ fun k => hwD k)
    intro k k' hkk' z hz
    exact (show V z ≤ w k from hz).trans (hwm hkk')

/-- `μ(H(V) < u) ≤ u` for `H(v) = μ(V ≥ v)`. -/
lemma pit_lower (V : X → ℝ≥0∞) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {x | μ.real {z | V x ≤ V z} < u} ≤ u := by
  set D := {v : ℝ≥0∞ | μ.real {z | v ≤ V z} < u} with hD
  have hpre : {x | μ.real {z | V x ≤ V z} < u} = V ⁻¹' D := rfl
  rw [hpre]
  rcases D.eq_empty_or_nonempty with hDe | hDne
  · rw [hDe, Set.preimage_empty, measureReal_empty]; exact hu
  apply ENNReal.toReal_le_of_le_ofReal hu
  by_cases hm : sInf D ∈ D
  · have hsub : V ⁻¹' D ⊆ {z | sInf D ≤ V z} := fun x hx => sInf_le (show V x ∈ D from hx)
    calc μ (V ⁻¹' D) ≤ μ {z | sInf D ≤ V z} := measure_mono hsub
      _ = ENNReal.ofReal (μ.real {z | sInf D ≤ V z}) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal u := ENNReal.ofReal_le_ofReal hm.le
  · obtain ⟨w, hwm, hwt, hwD⟩ := exists_seq_tendsto_sInf hDne (OrderBot.bddBelow D)
    have hsub : V ⁻¹' D ⊆ ⋃ k, {z | w k ≤ V z} := by
      intro x hx
      have hxD : V x ∈ D := hx
      have hlt : sInf D < V x := lt_of_le_of_ne (sInf_le hxD) fun h => hm (h.symm ▸ hxD)
      obtain ⟨k, hk⟩ := (hwt.eventually (gt_mem_nhds hlt)).exists
      exact Set.mem_iUnion.2 ⟨k, hk.le⟩
    refine (measure_mono hsub).trans (meas_le_ofReal_of_iUnion μ ?_ fun k => hwD k)
    intro k k' hkk' z hz
    exact (hwm hkk').trans (show w k ≤ V z from hz)

/-! ### From the single tilt to `e^{−2nt²}` -/

lemma level_bound {n : ℕ} (hn : 1 ≤ n) {t l : ℝ}
    (hlam : ∀ p : ℝ, t < p → p ≤ 1 → Real.log (1 + l) + 2 * t ^ 2 ≤ p * Real.log (1 + l / (p - t)))
    (hl : 0 < l) {i : ℕ} (hti : t < (i : ℝ) / n) (hin : i ≤ n) :
    (1 + l) ^ n ≤ Real.exp (-2 * n * t ^ 2) * (1 + l / ((i : ℝ) / n - t)) ^ i := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp1 : (i : ℝ) / n ≤ 1 := by rw [div_le_one hn']; exact_mod_cast hin
  have h := hlam _ hti hp1
  have hupos : 0 < (i : ℝ) / n - t := by linarith
  have hpos2 : 0 < 1 + l / ((i : ℝ) / n - t) := by positivity
  have hmul : n * Real.log (1 + l) + 2 * n * t ^ 2 ≤ i * Real.log (1 + l / ((i : ℝ) / n - t)) := by
    have := mul_le_mul_of_nonneg_left h hn'.le
    have he : (n : ℝ) * ((i : ℝ) / n) = i := by field_simp
    have h2 : (n : ℝ) * ((i : ℝ) / n * Real.log (1 + l / ((i : ℝ) / n - t))) =
        i * Real.log (1 + l / ((i : ℝ) / n - t)) := by rw [← mul_assoc, he]
    have h3 : (n : ℝ) * Real.log (1 + l) + 2 * n * t ^ 2 = n * (Real.log (1 + l) + 2 * t ^ 2) := by ring
    linarith
  have hexp := Real.exp_le_exp.2 hmul
  rw [Real.exp_add, ← Real.log_pow, ← Real.log_pow, Real.exp_log (by positivity), Real.exp_log (by positivity)]
    at hexp
  have he2 : Real.exp (2 * n * t ^ 2) * Real.exp (-2 * n * t ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  calc (1 + l) ^ n = (1 + l) ^ n * Real.exp (2 * n * t ^ 2) * Real.exp (-2 * n * t ^ 2) := by
        rw [mul_assoc, he2, mul_one]
    _ ≤ (1 + l / ((i : ℝ) / n - t)) ^ i * Real.exp (-2 * n * t ^ 2) := by gcongr
    _ = _ := mul_comm _ _

/-- The generic level argument: if for every `s` with `t < Ĝ(s) − G(s)`-type deviation the `c` points counted have
`F < c/n − t` on them, then the event has probability `≤ e^{−2nt²}`. -/
lemma level_event {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (g : X → ℝ) (hg : Measurable g)
    (hpit : ∀ u : ℝ, 0 ≤ u → μ.real {x | g x < u} ≤ u) (Ev : Set (Fin n → X))
    (hEv : ∀ y ∈ Ev, ∃ c : ℕ, t < (c : ℝ) / n ∧ c ≤ n ∧ c ≤ cnt {x | g x < (c : ℝ) / n - t} y) :
    (Measure.pi fun _ : Fin n => μ) Ev ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨l, hl, hlam⟩ := exists_lambda ht0 ht1
  set u : ℕ → ℝ := fun i => (i : ℝ) / n - t with hu
  set A : ℕ → Set X := fun i => {x | g x < u i} with hA
  have hAm : ∀ i, MeasurableSet (A i) := fun i => measurableSet_lt hg measurable_const
  have hmono : Monotone A := by
    intro i j hij x hx
    simp only [hA, hu, Set.mem_setOf_eq] at hx ⊢
    have : (i : ℝ) / n ≤ (j : ℝ) / n := div_le_div_of_nonneg_right (by exact_mod_cast hij) hn'.le
    linarith
  set a := ⌊(n : ℝ) * t⌋₊ + 1 with ha
  have hlev : ∀ i ∈ Finset.Icc a n, t < (i : ℝ) / n := by
    intro i hi
    have h1 : (n : ℝ) * t < (a : ℝ) := by rw [ha]; push_cast; exact Nat.lt_floor_add_one _
    have h2 : (a : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Icc.1 hi).1
    rw [lt_div_iff₀ hn']; linarith
  have hcore := tilt_core μ A hAm hmono a n (by rw [ha]; omega) u
    (fun i hi => hpit _ (by have := hlev i hi; simp only [hu]; linarith)) l _ hl
    (fun i hi => level_bound hn hlam hl (hlev i hi) (Finset.mem_Icc.1 hi).2)
  refine le_trans (measure_mono fun y hy => ?_) hcore
  obtain ⟨c, hc1, hc2, hc3⟩ := hEv y hy
  refine ⟨c, Finset.mem_Icc.2 ⟨?_, hc2⟩, hc3⟩
  rw [ha, Nat.add_one_le_iff, Nat.floor_lt (by positivity)]
  rw [lt_div_iff₀ hn'] at hc1
  linarith

/-- **One-sided DKW–Massart, upper deviations**: `P(∃ s, t < Ĝ(s) − G(s)) ≤ e^{−2nt²}` for every `t ≥ 0`. -/
theorem massart_upper (V : X → ℝ≥0∞) (hV : Measurable V) {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => μ)
      {y | ∃ s, t < ((Finset.univ.filter fun i => V (y i) ≤ s).card : ℝ) / n - (μ {x | V x ≤ s}).toReal} ≤
      ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases ht.eq_or_lt with rfl | ht0
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Real.exp_zero,
      ENNReal.ofReal_one]
    exact prob_le_one
  by_cases ht1 : 1 ≤ t
  · have : {y : Fin n → X | ∃ s, t < ((Finset.univ.filter fun i => V (y i) ≤ s).card : ℝ) / n -
        (μ {x | V x ≤ s}).toReal} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
      intro s
      have h1 : ((Finset.univ.filter fun i => V (y i) ≤ s).card : ℝ) / n ≤ 1 := by
        rw [div_le_one hn']
        exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
      have h2 : 0 ≤ (μ {x | V x ≤ s}).toReal := ENNReal.toReal_nonneg
      linarith
    rw [this, measure_empty]; exact bot_le
  push_neg at ht1
  set g : X → ℝ := fun x => μ.real {z | V z ≤ V x} with hg
  have hGm : Monotone fun v : ℝ≥0∞ => μ.real {z | V z ≤ v} := fun v w hvw =>
    measureReal_mono fun z hz => (show V z ≤ v from hz).trans hvw
  have hgm : Measurable g := hGm.measurable.comp hV
  refine level_event μ hn ht0 ht1 g hgm (fun u hu => pit_upper μ V hu) _ ?_
  rintro y ⟨s, hs⟩
  set c := (Finset.univ.filter fun i => V (y i) ≤ s).card with hc
  have hG0 : 0 ≤ (μ {x | V x ≤ s}).toReal := ENNReal.toReal_nonneg
  refine ⟨c, by linarith, (Finset.card_filter_le _ _).trans (by simp), ?_⟩
  unfold cnt
  refine hc.le.trans (Finset.card_le_card ?_)
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hk ⊢
  have : g (y k) ≤ (μ {x | V x ≤ s}).toReal := hGm hk
  linarith

/-- **One-sided DKW–Massart, lower deviations**: `P(∃ s, t < G(s) − Ĝ(s)) ≤ e^{−2nt²}` for every `t ≥ 0`. -/
theorem massart_lower (V : X → ℝ≥0∞) (hV : Measurable V) {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => μ)
      {y | ∃ s, t < (μ {x | V x ≤ s}).toReal - ((Finset.univ.filter fun i => V (y i) ≤ s).card : ℝ) / n} ≤
      ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases ht.eq_or_lt with rfl | ht0
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Real.exp_zero,
      ENNReal.ofReal_one]
    exact prob_le_one
  by_cases ht1 : 1 ≤ t
  · have : {y : Fin n → X | ∃ s, t < (μ {x | V x ≤ s}).toReal -
        ((Finset.univ.filter fun i => V (y i) ≤ s).card : ℝ) / n} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
      intro s
      have h1 : 0 ≤ ((Finset.univ.filter fun i => V (y i) ≤ s).card : ℝ) / n := by positivity
      have h2 : (μ {x | V x ≤ s}).toReal ≤ 1 := by
        rw [← measureReal_def]; exact measureReal_le_one
      linarith
    rw [this, measure_empty]; exact bot_le
  push_neg at ht1
  set g : X → ℝ := fun x => μ.real {z | V x ≤ V z} with hg
  have hHm : Antitone fun v : ℝ≥0∞ => μ.real {z | v ≤ V z} := fun v w hvw =>
    measureReal_mono fun z hz => hvw.trans (show w ≤ V z from hz)
  have hgm : Measurable g := hHm.measurable.comp hV
  refine level_event μ hn ht0 ht1 g hgm (fun u hu => pit_lower μ V hu) _ ?_
  rintro y ⟨s, hs⟩
  set c := (Finset.univ.filter fun i => V (y i) ≤ s).card with hc
  set c' := (Finset.univ.filter fun i => ¬ V (y i) ≤ s).card with hc'
  have hcc : c + c' = n := by
    rw [hc, hc', Finset.card_filter_add_card_filter_not]; simp
  have hmeas : MeasurableSet {x | V x ≤ s} := measurableSet_le hV measurable_const
  have hcompl : μ.real {z | s < V z} = 1 - (μ {x | V x ≤ s}).toReal := by
    have : {z | s < V z} = {x | V x ≤ s}ᶜ := by ext z; simp
    rw [this, probReal_compl_eq_one_sub hmeas, measureReal_def]
  have hcast : (c' : ℝ) = n - c := by
    have : ((c + c' : ℕ) : ℝ) = n := by exact_mod_cast hcc
    push_cast at this; linarith
  have hdev : μ.real {z | s < V z} < (c' : ℝ) / n - t := by
    rw [hcompl, hcast, sub_div, div_self hn'.ne']
    linarith
  have hH0 : 0 ≤ μ.real {z | s < V z} := measureReal_nonneg
  refine ⟨c', by linarith, by omega, ?_⟩
  unfold cnt
  refine hc'.le.trans (Finset.card_le_card ?_)
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, not_le] at hk ⊢
  have : g (y k) ≤ μ.real {z | s < V z} :=
    measureReal_mono fun z hz => hk.trans_le (show V (y k) ≤ V z from hz)
  linarith

/-- **The Dvoretzky–Kiefer–Wolfowitz–Massart inequality**: `P(∃ s, t < |Ĝ(s) − G(s)|) ≤ 2e^{−2nt²}` for every
`t ≥ 0`, every probability `μ` and every measurable score `V` (no continuity of `G`). -/
theorem massart (V : X → ℝ≥0∞) (hV : Measurable V) {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => μ)
      {y | ∃ s, t < |((Finset.univ.filter fun i => V (y i) ≤ s).card : ℝ) / n - (μ {x | V x ≤ s}).toReal|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * n * t ^ 2)) := by
  have hsub : {y : Fin n → X | ∃ s, t < |((Finset.univ.filter fun i => V (y i) ≤ s).card : ℝ) / n -
      (μ {x | V x ≤ s}).toReal|} ⊆
      {y | ∃ s, t < ((Finset.univ.filter fun i => V (y i) ≤ s).card : ℝ) / n - (μ {x | V x ≤ s}).toReal} ∪
      {y | ∃ s, t < (μ {x | V x ≤ s}).toReal - ((Finset.univ.filter fun i => V (y i) ≤ s).card : ℝ) / n} := by
    rintro y ⟨s, hs⟩
    rcases lt_abs.1 hs with h | h
    · exact Or.inl ⟨s, h⟩
    · exact Or.inr ⟨s, by linarith⟩
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) + ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) :=
        add_le_add (massart_upper μ V hV hn ht) (massart_lower μ V hV hn ht)
    _ = ENNReal.ofReal (2 * Real.exp (-2 * n * t ^ 2)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]

end StatFormal.DKW.Massart
