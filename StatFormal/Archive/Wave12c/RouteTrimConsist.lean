import StatFormal.Archive.Wave12c.Statements
import StatFormal.Archive.Wave4b.RouteWitness
import StatFormal.Lib.Concentration.Symmetrization
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Finset.Fin

/-!
# Route: TM `thm:trimconsist` (untrusted)

1. **Order statistics.** `d̂_{(k+1)} ≤ t ⟺ #{i : d̂(X_i) ≤ t} ≥ k + 1` (`ord_le_iff`, via `Tuple.sort`).
2. **Quantile and margins.** With `F(t) = P(d* ≤ t)`: `F(t_α) ≥ 1−α` (continuity from above) and
   `P(d* < t_α) ≤ 1−α` (continuity from below); integrating the density over `(t_α, t_α+ε]` and
   `(t_α−ε, t_α)` gives `eq:marginlb` from the lower bound `c_f` alone; `(Q)` then forces `α ≥ c_fρ > 0`.
3. **Two Hoeffding bounds** (McDiarmid for the empirical CDF, bounded differences `1/n`) at the
   deterministic points `t_α ± u`, `u = (s_n + 1/n)/c_f`, each at level `δ/6` (no DKW needed).
4. **Assembly.** Intersect with the certified `prop:witnessstab` event at level `2δ/3` (its `η` is the
   theorem's `η`); then Steps 2–5 of the paper's proof are deterministic.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal InnerProductSpace Topology Pointwise

namespace StatFormal.Wave12c

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.Projection

/-! ### Order statistics -/

theorem ord_le_iff {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k < n) (t : ℝ) :
    ord v k ≤ t ↔ k + 1 ≤ (univ.filter fun i => v i ≤ t).card := by
  set σ := Tuple.sort v
  have hm : Monotone (v ∘ σ) := Tuple.monotone_sort v
  have hcard : (univ.filter fun i => v i ≤ t).card = (univ.filter fun j => v (σ j) ≤ t).card := by
    refine Finset.card_nbij' (fun i => σ.symm i) (fun j => σ j) ?_ ?_ ?_ ?_
    · intro i hi; simpa using hi
    · intro j hj; simpa using hj
    · intro i _; simp
    · intro j _; simp
  rw [hcard]
  set k0 : Fin n := ⟨k, hk⟩
  have hord : ord v k = v (σ k0) := by simp [ord, hk, k0, σ]
  rw [hord]
  constructor
  · intro h
    have hsub : Finset.Iic k0 ⊆ univ.filter fun j => v (σ j) ≤ t := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hm hj).trans h
    have := Finset.card_le_card hsub
    rwa [Fin.card_Iic] at this
  · intro h
    by_contra hlt
    push_neg at hlt
    have hsub : (univ.filter fun j => v (σ j) ≤ t) ⊆ Finset.Iio k0 := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Iio]
      by_contra hle
      push_neg at hle
      exact absurd ((hm hle).trans hj) (not_le.2 hlt)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    simp [k0] at this
    omega

/-! ### Witness functions -/

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem measurable_witFn {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) (d : H) :
    Measurable (witFn d φ) :=
  (stronglyMeasurable_const.inner hφ).measurable

theorem abs_witFn_le {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (d : H) (x : 𝒳) :
    |witFn d φ x| ≤ ‖d‖ * κ :=
  (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hκ x) (norm_nonneg _))

/-! ### The quantile -/

section Quantile

variable (P : Measure 𝒳) [IsProbabilityMeasure P] {f : 𝒳 → ℝ}

theorem quantile_bdd (hf : Measurable f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) :
    ({t : ℝ | p ≤ P.real {x | f x ≤ t}}).Nonempty ∧ BddBelow {t : ℝ | p ≤ P.real {x | f x ≤ t}} := by
  refine ⟨⟨K, ?_⟩, ⟨-K, fun t ht => ?_⟩⟩
  · have : {x | f x ≤ K} = univ := eq_univ_of_forall fun x => (le_abs_self _).trans (hK x)
    simp [this, hp1]
  · by_contra hlt
    push_neg at hlt
    have : {x | f x ≤ t} = ∅ := eq_empty_of_forall_notMem fun x hx => by
      have := neg_abs_le (f x); have := hK x; simp only [mem_setOf_eq] at hx; linarith
    simp only [mem_setOf_eq, this, measureReal_empty] at ht
    linarith

theorem quantile_ge (hf : Measurable f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) : p ≤ P.real {x | f x ≤ quantileAt P f p} := by
  obtain ⟨hne, hbdd⟩ := quantile_bdd P hf hK hp0 hp1
  set q := quantileAt P f p
  set s : ℕ → Set 𝒳 := fun k => {x | f x ≤ q + 1 / ((k : ℝ) + 1)}
  have hanti : Antitone s := by
    intro a b hab x hx
    simp only [s, mem_setOf_eq] at hx ⊢
    have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
    linarith
  have hinter : (⋂ k, s k) = {x | f x ≤ q} := by
    ext x
    simp only [mem_iInter, mem_setOf_eq, s]
    constructor
    · intro h
      by_contra hlt
      push_neg at hlt
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
      have := h k
      linarith
    · intro h k
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  have hk : ∀ k, ENNReal.ofReal p ≤ P (s k) := by
    intro k
    obtain ⟨t, ht, htq⟩ := exists_lt_of_csInf_lt hne
      (show sInf {t : ℝ | p ≤ P.real {x | f x ≤ t}} < q + 1 / ((k : ℝ) + 1) by
        have : 0 < 1 / ((k : ℝ) + 1) := by positivity
        change q < _; linarith)
    have hmono : P.real {x | f x ≤ t} ≤ P.real (s k) :=
      measureReal_mono fun x (hx : f x ≤ t) => (show f x ≤ _ from hx.trans htq.le)
    rw [← ofReal_measureReal (by finiteness)]
    exact ENNReal.ofReal_le_ofReal (ht.trans hmono)
  have hmeas : ∀ k, NullMeasurableSet (s k) P := fun k =>
    (measurableSet_le hf measurable_const).nullMeasurableSet
  have := hanti.measure_iInter hmeas ⟨0, measure_ne_top _ _⟩
  rw [hinter] at this
  have hle : ENNReal.ofReal p ≤ P {x | f x ≤ q} := by rw [this]; exact le_iInf hk
  rw [← ofReal_measureReal (by finiteness)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff measureReal_nonneg).1 hle

theorem quantile_lt_le (hf : Measurable f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) : P.real {x | f x < quantileAt P f p} ≤ p := by
  obtain ⟨hne, hbdd⟩ := quantile_bdd P hf hK hp0 hp1
  set q := quantileAt P f p
  set s : ℕ → Set 𝒳 := fun k => {x | f x ≤ q - 1 / ((k : ℝ) + 1)}
  have hmono : Monotone s := by
    intro a b hab x hx
    simp only [s, mem_setOf_eq] at hx ⊢
    have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
    linarith
  have hunion : (⋃ k, s k) = {x | f x < q} := by
    ext x
    simp only [mem_iUnion, mem_setOf_eq, s]
    constructor
    · rintro ⟨k, hk⟩
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    · intro h
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 h)
      exact ⟨k, by linarith⟩
  have hk : ∀ k, P (s k) ≤ ENNReal.ofReal p := by
    intro k
    have hlt : q - 1 / ((k : ℝ) + 1) < sInf {t : ℝ | p ≤ P.real {x | f x ≤ t}} := by
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      change _ < q; linarith
    have hnot := notMem_of_lt_csInf hlt hbdd
    simp only [mem_setOf_eq, not_le] at hnot
    rw [← ofReal_measureReal (by finiteness)]
    exact ENNReal.ofReal_le_ofReal hnot.le
  have := hmono.measure_iUnion (μ := P)
  rw [hunion] at this
  have hle : P {x | f x < q} ≤ ENNReal.ofReal p := by rw [this]; exact iSup_le hk
  rw [← ofReal_measureReal (by finiteness)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 hle

end Quantile

/-! ### Density integrals -/

section Density

variable {P : Measure 𝒳} [IsProbabilityMeasure P] {f : 𝒳 → ℝ}

theorem density_lower {g : ℝ → ℝ} {I : Set ℝ} {cf : ℝ}
    (hg : ∀ s ∈ I, cf ≤ g s) (hd : ∀ A : Set ℝ, MeasurableSet A → A ⊆ I →
      P (f ⁻¹' A) = ∫⁻ s in A, ENNReal.ofReal (g s)) {a b : ℝ} (hab : a ≤ b)
    {A : Set ℝ} (hA : MeasurableSet A) (hAI : A ⊆ I) (hvol : volume A = ENNReal.ofReal (b - a)) :
    cf * (b - a) ≤ P.real (f ⁻¹' A) := by
  have h1 : ENNReal.ofReal cf * ENNReal.ofReal (b - a) ≤ P (f ⁻¹' A) := by
    rw [hd A hA hAI, ← hvol, ← setLIntegral_const]
    refine setLIntegral_mono' hA fun s hs => ENNReal.ofReal_le_ofReal (hg s (hAI hs))
  rcases le_or_gt cf 0 with hc | hc
  · exact (mul_nonpos_of_nonpos_of_nonneg hc (by linarith)).trans measureReal_nonneg
  rw [← ENNReal.ofReal_mul hc.le, ← ofReal_measureReal (by finiteness)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff measureReal_nonneg).1 h1

theorem density_upper {g : ℝ → ℝ} {I : Set ℝ} {Cf : ℝ}
    (hg : ∀ s ∈ I, g s ≤ Cf) (hd : ∀ A : Set ℝ, MeasurableSet A → A ⊆ I →
      P (f ⁻¹' A) = ∫⁻ s in A, ENNReal.ofReal (g s)) {a b : ℝ}
    {A : Set ℝ} (hA : MeasurableSet A) (hAI : A ⊆ I) (hvol : volume A = ENNReal.ofReal (b - a)) :
    P (f ⁻¹' A) ≤ ENNReal.ofReal (Cf * (b - a)) := by
  rw [hd A hA hAI]
  calc ∫⁻ s in A, ENNReal.ofReal (g s) ≤ ∫⁻ _ in A, ENNReal.ofReal Cf :=
        setLIntegral_mono' hA fun s hs => ENNReal.ofReal_le_ofReal (hg s (hAI hs))
    _ = ENNReal.ofReal Cf * ENNReal.ofReal (b - a) := by rw [setLIntegral_const, hvol]
    _ ≤ ENNReal.ofReal (Cf * (b - a)) := by
        rcases le_or_gt Cf 0 with hc | hc
        · simp [ENNReal.ofReal_of_nonpos hc]
        · rw [ENNReal.ofReal_mul hc.le]

/-- `eq:marginlb`, lower bound only. -/
theorem margins (hf : Measurable f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) {α ρ cf : ℝ} (hα1 : α < 1)
    (hα0 : 0 ≤ α) (g : ℝ → ℝ)
    (hg : ∀ s ∈ Icc (quantileAt P f (1 - α) - ρ) (quantileAt P f (1 - α) + ρ), cf ≤ g s)
    (hd : ∀ A : Set ℝ, MeasurableSet A →
      A ⊆ Icc (quantileAt P f (1 - α) - ρ) (quantileAt P f (1 - α) + ρ) →
      P (f ⁻¹' A) = ∫⁻ s in A, ENNReal.ofReal (g s)) {ε : ℝ} (hε0 : 0 < ε) (hερ : ε ≤ ρ) :
    (1 - α) + cf * ε ≤ P.real {x | f x ≤ quantileAt P f (1 - α) + ε} ∧
      P.real {x | f x ≤ quantileAt P f (1 - α) - ε} ≤ (1 - α) - cf * ε := by
  set q := quantileAt P f (1 - α)
  have hp0 : 0 < 1 - α := by linarith
  have hp1 : 1 - α ≤ 1 := by linarith
  constructor
  · have h1 := quantile_ge P hf hK hp0 hp1
    have h2 := density_lower (P := P) (f := f) hg hd (a := q) (b := q + ε) (by linarith)
      (A := Ioc q (q + ε)) measurableSet_Ioc
      (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩) Real.volume_Ioc
    have hunion : {x | f x ≤ q + ε} = {x | f x ≤ q} ∪ f ⁻¹' Ioc q (q + ε) := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_preimage, Set.mem_Ioc]
      constructor
      · intro h; by_cases h' : f x ≤ q
        · exact Or.inl h'
        · exact Or.inr ⟨not_le.1 h', h⟩
      · rintro (h | h)
        · linarith
        · exact h.2
    have hdisj : Disjoint {x | f x ≤ q} (f ⁻¹' Ioc q (q + ε)) :=
      Set.disjoint_left.2 fun x hx hx' => by
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioc] at hx hx'; linarith [hx'.1]
    rw [hunion, measureReal_union hdisj (hf measurableSet_Ioc)]
    have : q + ε - q = ε := by ring
    rw [this] at h2
    linarith
  · have h1 := quantile_lt_le P hf hK hp0 hp1
    have h2 := density_lower (P := P) (f := f) hg hd (a := q - ε) (b := q) (by linarith)
      (A := Ioo (q - ε) q) measurableSet_Ioo
      (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩) Real.volume_Ioo
    have hsub : {x | f x ≤ q - ε} ∪ f ⁻¹' Ioo (q - ε) q ⊆ {x | f x < q} := by
      rintro x (hx | hx)
      · simp only [mem_setOf_eq] at hx ⊢; linarith
      · simp only [Set.mem_preimage, Set.mem_Ioo] at hx; exact hx.2
    have hdisj : Disjoint {x | f x ≤ q - ε} (f ⁻¹' Ioo (q - ε) q) :=
      Set.disjoint_left.2 fun x hx hx' => by
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioo] at hx hx'; linarith [hx'.1]
    have h3 := measureReal_mono (μ := P) hsub
    rw [measureReal_union hdisj (hf measurableSet_Ioo)] at h3
    have : q - (q - ε) = ε := by ring
    rw [this] at h2
    linarith

end Density

/-! ### Hoeffding for the empirical CDF at a point -/

section Hoeffding

variable (P : Measure 𝒳) [IsProbabilityMeasure P] {f : 𝒳 → ℝ}

/-- The empirical CDF `F_n(t) = n⁻¹ #{i : f(x_i) ≤ t}`. -/
def empCdf {n : ℕ} (f : 𝒳 → ℝ) (x : Fin n → 𝒳) (t : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, ({y | f y ≤ t}.indicator (fun _ => (1 : ℝ)) (x i))

theorem measurable_empCdf (hf : Measurable f) (n : ℕ) (t : ℝ) :
    Measurable fun x : Fin n → 𝒳 => empCdf f x t :=
  (Finset.measurable_fun_sum _ fun i _ =>
    ((measurable_const.indicator (measurableSet_le hf measurable_const)).comp
      (measurable_pi_apply i))).const_mul _

theorem empCdf_eq_card {n : ℕ} (f : 𝒳 → ℝ) (x : Fin n → 𝒳) (t : ℝ) :
    empCdf f x t = (n : ℝ)⁻¹ * ((univ.filter fun i => f (x i) ≤ t).card : ℝ) := by
  unfold empCdf
  congr 1
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [Finset.sum_boole]

theorem empCdf_update (f : 𝒳 → ℝ) {n : ℕ} (x : Fin n → 𝒳) (i : Fin n) (b : 𝒳) (t : ℝ) :
    |empCdf f (Function.update x i b) t - empCdf f x t| ≤ 1 / n := by
  unfold empCdf
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp only [Function.update_self]
    rw [abs_mul, abs_inv, Nat.abs_cast, one_div]
    refine mul_le_of_le_one_right (by positivity) ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs <;> norm_num
  · intro j _ hj; simp [Function.update_of_ne hj]
  · simp

theorem integral_empCdf (hf : Measurable f) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    ∫ x, empCdf f x t ∂(Measure.pi fun _ : Fin n => P) = P.real {y | f y ≤ t} := by
  have h := StatFormal.Concentration.integral_mean_comp P (T := Unit)
    (g := fun _ => {y | f y ≤ t}.indicator (fun _ => (1 : ℝ)))
    (fun _ => measurable_const.indicator (measurableSet_le hf measurable_const)) (B := 1)
    (fun _ y => by
      simp only [Set.indicator_apply]; split_ifs <;> norm_num) hn ()
  rw [show (fun x : Fin n → 𝒳 => empCdf f x t) = fun x' => (n : ℝ)⁻¹ *
    ∑ i, {y | f y ≤ t}.indicator (fun _ => (1 : ℝ)) (x' i) from rfl, h,
    integral_indicator_const _ (measurableSet_le hf measurable_const), smul_eq_mul, mul_one]

theorem sqrt_hoeffding {n : ℕ} (hn : n ≠ 0) {L : ℝ} :
    1 / (n : ℝ) * √(n * L / 2) = √(L / (2 * n)) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have : L / (2 * n) = (1 / n) ^ 2 * (n * L / 2) := by field_simp
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- One-sided Hoeffding bounds for `F_n(t)` at a fixed point. -/
theorem hoeffding_cdf (hf : Measurable f) (t : ℝ) {n : ℕ} (hn : n ≠ 0) {δ' : ℝ} (h0 : 0 < δ')
    (h1 : δ' ≤ 1) :
    1 - δ' ≤ (Measure.pi fun _ : Fin n => P).real
        {x | P.real {y | f y ≤ t} - √(Real.log (1 / δ') / (2 * n)) ≤ empCdf f x t} ∧
      1 - δ' ≤ (Measure.pi fun _ : Fin n => P).real
        {x | empCdf f x t ≤ P.real {y | f y ≤ t} + √(Real.log (1 / δ') / (2 * n))} := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hL : 0 ≤ Real.log (1 / δ') := Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)
  have hmeas := measurable_empCdf hf n t
  have hc : (0 : ℝ) < 1 / n := by positivity
  constructor
  · have hosc : ∀ (x : Fin n → 𝒳) (i : Fin n) (b : 𝒳),
        |(fun x => -empCdf f x t) (Function.update x i b) - (fun x => -empCdf f x t) x| ≤ 1 / n := by
      intro x i b
      have := empCdf_update f x i b t
      simp only
      rw [show -empCdf f (Function.update x i b) t - -empCdf f x t =
        -(empCdf f (Function.update x i b) t - empCdf f x t) by ring, abs_neg]
      exact this
    have := StatFormal.Concentration.mcdiarmid_tail P hn (fun x => -empCdf f x t) hmeas.neg hc
      hosc h0 h1
    rw [integral_neg, integral_empCdf P hf hn, sqrt_hoeffding hn] at this
    refine this.trans_eq (congrArg _ (Set.ext fun x => ?_))
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  · have := StatFormal.Concentration.mcdiarmid_tail P hn (fun x => empCdf f x t) hmeas hc
      (fun x i b => empCdf_update f x i b t) h0 h1
    rwa [integral_empCdf P hf hn, sqrt_hoeffding hn] at this

end Hoeffding

/-! ### Deterministic steps -/

theorem tHat_bounds {n k : ℕ} (v w : Fin n → ℝ) {Δ q u : ℝ} (hk : k < n)
    (hvw : ∀ i, |v i - w i| ≤ Δ) (hA : k + 1 ≤ (univ.filter fun i => w i ≤ q + u).card)
    (hB : (univ.filter fun i => w i ≤ q - u).card < k + 1) :
    |ord v k - q| ≤ Δ + u := by
  rw [abs_le]
  constructor
  · by_contra hlt
    push_neg at hlt
    have h1 := (ord_le_iff v k hk (q - (Δ + u))).1 (by linarith)
    have h2 : (univ.filter fun i => v i ≤ q - (Δ + u)) ⊆ univ.filter fun i => w i ≤ q - u := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have := (abs_le.1 (hvw i)).1
      linarith
    have := Finset.card_le_card h2
    omega
  · have h2 : (univ.filter fun i => w i ≤ q + u) ⊆ univ.filter fun i => v i ≤ q + (Δ + u) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have := (abs_le.1 (hvw i)).2
      linarith
    have h3 := (ord_le_iff v k hk (q + (Δ + u))).2 (hA.trans (Finset.card_le_card h2))
    linarith

theorem band_incl (dh ds : 𝒳 → ℝ) {Δ th q ε Λ : ℝ} (hΔ : ∀ x, |dh x - ds x| ≤ Δ)
    (hth : |th - q| ≤ ε) (hΛ : Δ + ε ≤ Λ) :
    symmDiff {x | dh x < th} {x | ds x < q} ⊆ {x | |ds x - q| ≤ Λ} ∧
      ∀ x, dh x = th → |ds x - q| ≤ Λ := by
  have hth' := abs_le.1 hth
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have hd := abs_le.1 (hΔ x)
    simp only [Set.mem_symmDiff, Set.mem_setOf_eq, not_lt] at hx
    simp only [Set.mem_setOf_eq, abs_le]
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor <;> linarith
    · constructor <;> linarith
  · have hd := abs_le.1 (hΔ x)
    rw [abs_le]
    constructor <;> linarith

theorem plugDensity_mem {α γ : ℝ} (hα1 : α < 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1 / (1 - α))
    (f : 𝒳 → ℝ) (t : ℝ) (x : 𝒳) : 0 ≤ plugDensity α γ f t x ∧ plugDensity α γ f t x ≤ 1 / (1 - α) := by
  have h : 0 < 1 / (1 - α) := by have : 0 < 1 - α := by linarith
                                 positivity
  unfold plugDensity
  split_ifs <;> constructor <;> linarith

theorem measurable_plugDensity {f : 𝒳 → ℝ} (hf : Measurable f) (α γ t : ℝ) :
    Measurable (plugDensity α γ f t) :=
  Measurable.ite (measurableSet_lt hf measurable_const) measurable_const
    (Measurable.ite (measurableSet_eq_fun hf measurable_const) measurable_const measurable_const)

/-! ### The event -/

theorem prob_inter_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S T : Set Ω} (hT : MeasurableSet T) : μ.real S + μ.real T - 1 ≤ μ.real (S ∩ T) := by
  have h := measureReal_union_add_inter (μ := μ) (s := S) hT
  have : μ.real (S ∪ T) ≤ 1 := measureReal_le_one
  linarith

theorem etaNM_eq (κ α δ : ℝ) (n m : ℕ) :
    StatFormal.Wave4b.etaNM κ α α (2 * δ / 3) n m = etaTC κ α δ n m := by
  unfold StatFormal.Wave4b.etaNM etaTC
  rw [show 2 * δ / 3 / 2 = δ / 3 by ring]

theorem rn_nonneg {κ α δ : ℝ} (hκ : 0 ≤ κ) (hα : α < 1) (n : ℕ) :
    0 ≤ StatFormal.TrimmedMMD.rn κ α δ n := by
  unfold StatFormal.TrimmedMMD.rn
  have : 0 < 1 - α := by linarith
  positivity

/-- The common core of `trimconsist` and `trimconsist_lower`. -/
theorem trim_event (𝒳 H : Type) [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α δ ρ cf : ℝ) (n m : ℕ) (dstar : H)
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hmin : IsMinNorm (region φ α P - region φ α Q) dstar) (hρ : 0 < ρ) (hcf : 0 < cf)
    (g : ℝ → ℝ)
    (hgl : ∀ s ∈ Icc (quantileAt P (witFn dstar φ) (1 - α) - ρ)
      (quantileAt P (witFn dstar φ) (1 - α) + ρ), cf ≤ g s)
    (hd : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (quantileAt P (witFn dstar φ) (1 - α) - ρ)
      (quantileAt P (witFn dstar φ) (1 - α) + ρ) →
      P (witFn dstar φ ⁻¹' A) = ∫⁻ s in A, ENNReal.ofReal (g s))
    (hΛ : lamTC κ (zetaTC (etaTC κ α δ n m) ‖dstar‖) cf δ n ≤ ρ) :
    ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
      ENNReal.ofReal (1 - δ) ≤
        ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
      E ⊆ {z | ∀ pr : (Fin n → ℝ) × (Fin m → ℝ),
        pr ∈ capped n α ×ˢ capped m α →
        IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m α) pr →
        |tHat φ (StatFormal.Wave4b.witness φ z.1 z.2 pr) α z.1 -
            quantileAt P (witFn dstar φ) (1 - α)| ≤
          lamTC κ (zetaTC (etaTC κ α δ n m) ‖dstar‖) cf δ n ∧
        symmDiff {x | witFn (StatFormal.Wave4b.witness φ z.1 z.2 pr) φ x <
            tHat φ (StatFormal.Wave4b.witness φ z.1 z.2 pr) α z.1}
          {x | witFn dstar φ x < quantileAt P (witFn dstar φ) (1 - α)} ⊆
          {x | |witFn dstar φ x - quantileAt P (witFn dstar φ) (1 - α)| ≤
            lamTC κ (zetaTC (etaTC κ α δ n m) ‖dstar‖) cf δ n} ∧
        ∀ x, witFn (StatFormal.Wave4b.witness φ z.1 z.2 pr) φ x =
            tHat φ (StatFormal.Wave4b.witness φ z.1 z.2 pr) α z.1 →
          |witFn dstar φ x - quantileAt P (witFn dstar φ) (1 - α)| ≤
            lamTC κ (zetaTC (etaTC κ α δ n m) ‖dstar‖) cf δ n} := by
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ x₀)
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set f := witFn dstar φ with hfdef
  have hf : Measurable f := measurable_witFn hφ dstar
  have hK : ∀ x, |f x| ≤ ‖dstar‖ * κ := abs_witFn_le hκ dstar
  set q := quantileAt P f (1 - α) with hq
  set η := etaTC κ α δ n m with hηdef
  set ζ := zetaTC η ‖dstar‖ with hζdef
  set Λ := lamTC κ ζ cf δ n with hΛdef
  set sn := √(Real.log (6 / δ) / (2 * n)) with hsn
  set u := (sn + 1 / n) / cf with hu
  have hη0 : 0 ≤ η := add_nonneg (rn_nonneg hκ0 hα1 n) (rn_nonneg hκ0 hα1 m)
  have hζ0 : 0 ≤ ζ := add_nonneg hη0 (Real.sqrt_nonneg _)
  have hsn0 : 0 ≤ sn := Real.sqrt_nonneg _
  have hu0 : 0 < u := by positivity
  have hΛu : Λ = 2 * κ * ζ + u := by rw [hΛdef, lamTC, hu]; ring
  have hκζ : 0 ≤ κ * ζ := mul_nonneg hκ0 hζ0
  have huρ : u ≤ ρ := by linarith
  have hcfu : cf * u = sn + 1 / n := by rw [hu]; field_simp
  -- margins
  have hmar := margins (P := P) hf hK hα1 hα0 g hgl hd hu0 huρ
  have hmarρ := margins (P := P) hf hK hα1 hα0 g hgl hd hρ le_rfl
  have hαpos : 0 < α := by
    have h1 := hmarρ.1
    have h2 : P.real {x | f x ≤ q + ρ} ≤ 1 := measureReal_le_one
    nlinarith
  set k := kfloor n α with hk
  have hknp : (k : ℝ) ≤ n * (1 - α) := Nat.floor_le (by nlinarith)
  have hknp1 : (n : ℝ) * (1 - α) < k + 1 := Nat.lt_floor_add_one _
  have hkn : k < n := by
    have : (k : ℝ) < n := by nlinarith
    exact_mod_cast this
  -- the witness event at level `2δ/3`
  obtain ⟨E12, hm12, hp12, hsub12⟩ := StatFormal.Wave4b.witnessstab 𝒳 H P Q φ κ α α (2 * δ / 3) n m
    hφ hκ hα0 hα1 hα0 hα1 hn hm (by positivity) (by linarith)
  rw [etaNM_eq] at hsub12
  -- the two Hoeffding events at level `δ/6`
  have hδ6 : 0 < δ / 6 := by positivity
  have hδ61 : δ / 6 ≤ 1 := by linarith
  have hlog : Real.log (1 / (δ / 6)) = Real.log (6 / δ) := by congr 1; field_simp
  obtain ⟨hEa, -⟩ := hoeffding_cdf P hf (q + u) hn0 hδ6 hδ61
  obtain ⟨-, hEb⟩ := hoeffding_cdf P hf (q - u) hn0 hδ6 hδ61
  rw [hlog] at hEa hEb
  set Ea := {x : Fin n → 𝒳 | P.real {y | f y ≤ q + u} - sn ≤ empCdf f x (q + u)} with hEadef
  set Eb := {x : Fin n → 𝒳 | empCdf f x (q - u) ≤ P.real {y | f y ≤ q - u} + sn} with hEbdef
  have hmEa : MeasurableSet Ea := measurableSet_le measurable_const (measurable_empCdf hf n _)
  have hmEb : MeasurableSet Eb := measurableSet_le (measurable_empCdf hf n _) measurable_const
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  refine ⟨E12 ∩ ((Ea ∩ Eb) ×ˢ Set.univ), hm12.inter ((hmEa.inter hmEb).prod MeasurableSet.univ), ?_, ?_⟩
  · -- probability
    have hAB : 1 - δ / 3 ≤ (Measure.pi fun _ : Fin n => P).real (Ea ∩ Eb) := by
      have := prob_inter_ge (Measure.pi fun _ : Fin n => P) (S := Ea) hmEb
      linarith
    have hprod : μ.real ((Ea ∩ Eb) ×ˢ (Set.univ : Set (Fin m → 𝒳))) =
        (Measure.pi fun _ : Fin n => P).real (Ea ∩ Eb) := by
      simp [hμ, measureReal_def, Measure.prod_prod]
    have h12 : 1 - 2 * δ / 3 ≤ μ.real E12 := by
      rw [measureReal_def]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hp12
    have := prob_inter_ge μ (S := E12) ((hmEa.inter hmEb).prod MeasurableSet.univ)
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _), ← measureReal_def]
    linarith
  · -- deterministic consequences
    rintro z ⟨hz12, ⟨hza, hzb⟩, -⟩ pr hpr hprmin
    set dh := StatFormal.Wave4b.witness φ z.1 z.2 pr with hdh
    obtain ⟨-, hnorm, -, hsup⟩ := hsub12 hz12 pr dstar hpr hprmin hmin
    set Δ := κ * ‖dh - dstar‖ with hΔdef
    have hΔ : ∀ x, |witFn dh φ x - f x| ≤ Δ := fun x => hsup x
    have hΔζ : Δ ≤ κ * ζ := by
      refine mul_le_mul_of_nonneg_left (hnorm.trans ?_) hκ0
      rw [hζdef, zetaTC]
      gcongr
      exact min_le_left _ _
    -- counts
    have hA : k + 1 ≤ (univ.filter fun i => f (z.1 i) ≤ q + u).card := by
      have h1 : P.real {y | f y ≤ q + u} - sn ≤ empCdf f z.1 (q + u) := hza
      rw [empCdf_eq_card] at h1
      have h2 : ((k : ℝ) + 1) ≤ ((univ.filter fun i => f (z.1 i) ≤ q + u).card : ℝ) := by
        have h3 : (1 - α) + cf * u ≤ P.real {y | f y ≤ q + u} := hmar.1
        rw [hcfu] at h3
        have h4 : (n : ℝ)⁻¹ * ((1 - α) * n + 1) ≤
            (n : ℝ)⁻¹ * ((univ.filter fun i => f (z.1 i) ≤ q + u).card : ℝ) := by
          have : (n : ℝ)⁻¹ * ((1 - α) * n + 1) = (1 - α) + 1 / n := by field_simp
          linarith
        have h5 := le_of_mul_le_mul_left h4 (by positivity)
        linarith
      exact_mod_cast h2
    have hB : (univ.filter fun i => f (z.1 i) ≤ q - u).card < k + 1 := by
      have h1 : empCdf f z.1 (q - u) ≤ P.real {y | f y ≤ q - u} + sn := hzb
      rw [empCdf_eq_card] at h1
      have h3 : P.real {y | f y ≤ q - u} ≤ (1 - α) - cf * u := hmar.2
      rw [hcfu] at h3
      have h4 : (n : ℝ)⁻¹ * ((univ.filter fun i => f (z.1 i) ≤ q - u).card : ℝ) ≤
          (n : ℝ)⁻¹ * ((1 - α) * n - 1) := by
        have : (n : ℝ)⁻¹ * ((1 - α) * n - 1) = (1 - α) - 1 / n := by field_simp
        linarith
      have h5 := le_of_mul_le_mul_left h4 (by positivity)
      have h6 : ((univ.filter fun i => f (z.1 i) ≤ q - u).card : ℝ) < k + 1 := by linarith
      exact_mod_cast h6
    have hth := tHat_bounds (fun i => witFn dh φ (z.1 i)) (fun i => f (z.1 i)) hkn
      (fun i => hΔ (z.1 i)) hA hB
    have hth' : |tHat φ dh α z.1 - q| ≤ Δ + u := hth
    have hbd := band_incl (witFn dh φ) f hΔ hth' (Λ := Λ) (by rw [hΛu]; linarith)
    exact ⟨hth'.trans (by rw [hΛu]; linarith), hbd.1, hbd.2⟩

/-! ### The claims -/

theorem trimconsist_lower : Claims.trimconsist_lower := by
  intro 𝒳 H _ _ _ _ _ _ P Q _ _ φ κ α δ ρ cf n m dstar hφ hκ hα0 hα1 hn hm hδ0 hδ1 hmin hρ hcf
    hQ _ hΛ
  obtain ⟨g, -, hgl, hd⟩ := hQ
  obtain ⟨E, hE, hpE, hsub⟩ := trim_event 𝒳 H P Q φ κ α δ ρ cf n m dstar hφ hκ hα0 hα1 hn hm hδ0
    hδ1 hmin hρ hcf g hgl hd hΛ
  refine ⟨E, hE, hpE, fun z hz pr hpr hprmin => ?_⟩
  obtain ⟨h1, h2, -⟩ := hsub hz pr hpr hprmin
  intro dh tα th Λ
  exact ⟨h1, h2⟩

theorem trimconsist : Claims.trimconsist := by
  intro 𝒳 H _ _ _ _ _ _ P Q _ _ φ κ α δ ρ cf Cf n m dstar hφ hκ hα0 hα1 hn hm hδ0 hδ1 hmin hρ hcf
    hQ _ hΛ
  obtain ⟨g, -, hgb, hd⟩ := hQ
  obtain ⟨E, hE, hpE, hsub⟩ := trim_event 𝒳 H P Q φ κ α δ ρ cf n m dstar hφ hκ hα0 hα1 hn hm hδ0
    hδ1 hmin hρ hcf g (fun s hs => (hgb s hs).1) hd hΛ
  refine ⟨E, hE, hpE, fun z hz pr γ γh hpr hprmin hγ0 hγ1 hγh0 hγh1 => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hsub hz pr hpr hprmin
  intro dh tα th Λ
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ x₀)
  have hf : Measurable (witFn dstar φ) := measurable_witFn hφ dstar
  have hfh : Measurable (witFn dh φ) := measurable_witFn hφ dh
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans h1
  have hCf : 0 ≤ Cf := by
    have := hgb tα ⟨by linarith, by linarith⟩
    linarith
  set B := {x | |witFn dstar φ x - tα| ≤ Λ} with hBdef
  have hBeq : B = witFn dstar φ ⁻¹' Icc (tα - Λ) (tα + Λ) := by
    ext x; simp [hBdef, abs_le, le_sub_iff_add_le]; constructor <;>
      rintro ⟨a, b⟩ <;> constructor <;> linarith
  have hBm : MeasurableSet B := by rw [hBeq]; exact hf measurableSet_Icc
  have hPB : P B ≤ ENNReal.ofReal (2 * Cf * Λ) := by
    rw [hBeq]
    have := density_upper (P := P) (f := witFn dstar φ) (fun s hs => (hgb s hs).2) hd
      (a := tα - Λ) (b := tα + Λ) (A := Icc (tα - Λ) (tα + Λ)) measurableSet_Icc
      (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩) Real.volume_Icc
    rwa [show Cf * (tα + Λ - (tα - Λ)) = 2 * Cf * Λ by ring] at this
  refine ⟨h1, h2, (measure_mono h2).trans hPB, ?_⟩
  -- the densities
  have hα' : 0 < 1 - α := by linarith
  have hpt : ∀ x, |plugDensity α γh (witFn dh φ) th x - plugDensity α γ (witFn dstar φ) tα x| ≤
      B.indicator (fun _ => 1 / (1 - α)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      have ha := plugDensity_mem hα1 hγh0 hγh1 (witFn dh φ) th x
      have hb := plugDensity_mem hα1 hγ0 hγ1 (witFn dstar φ) tα x
      rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    · rw [Set.indicator_of_notMem hx]
      have hnot : x ∉ symmDiff {x | witFn dh φ x < th} {x | witFn dstar φ x < tα} :=
        fun h => hx (h2 h)
      have hne1 : witFn dh φ x ≠ th := fun h => hx (h3 x h)
      have hne2 : witFn dstar φ x ≠ tα := fun h => hx (by simp [hBdef, h, hΛ0])
      simp only [Set.mem_symmDiff, Set.mem_setOf_eq, not_or, not_and, not_not] at hnot
      unfold plugDensity
      by_cases hlt : witFn dh φ x < th
      · have := hnot.1 hlt
        simp [hlt, this]
      · have hlt2 : ¬ witFn dstar φ x < tα := fun h => hlt (hnot.2 h)
        simp [hlt, hlt2, hne1, hne2]
  have hint : Integrable (fun x => |plugDensity α γh (witFn dh φ) th x -
      plugDensity α γ (witFn dstar φ) tα x|) P := by
    refine Integrable.of_bound (C := 1 / (1 - α))
      ((continuous_abs.measurable.comp ((measurable_plugDensity hfh α γh th).sub
        (measurable_plugDensity hf α γ tα))).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    refine (hpt x).trans ?_
    simp only [Set.indicator_apply]
    split_ifs
    · rfl
    · positivity
  calc ∫ x, |plugDensity α γh (witFn dh φ) th x - plugDensity α γ (witFn dstar φ) tα x| ∂P
      ≤ ∫ x, B.indicator (fun _ => 1 / (1 - α)) x ∂P :=
        integral_mono hint ((integrable_const _).indicator hBm) hpt
    _ = P.real B * (1 / (1 - α)) := by rw [integral_indicator_const _ hBm, smul_eq_mul]
    _ ≤ (2 * Cf * Λ) * (1 / (1 - α)) := by
        gcongr
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hPB
    _ = 2 * Cf * Λ / (1 - α) := by ring

end StatFormal.Wave12c
