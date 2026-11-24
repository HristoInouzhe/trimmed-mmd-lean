import StatFormal.Wave30tx.RouteBasic
import StatFormal.Wave30tr.Proofs
import StatFormal.Archive.Wave12c.RouteTrimConsist
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs

/-!
# Route: `thm:trimrate (v2)` (i)–(iii), its last sentence and the (A3) parenthetical (untrusted)

Deterministic core (public):
* `ord_mul_pos` (order statistics commute with positive scaling), `real_inter_ge`, `real_biInter_ge` (union bounds);
* `quad_solve` (Step 3), `norm_sub_identity` and `witness_bound` (Step 4), `kept_of_band` (Step 5: mass and density bounds with
  tie functions from the band inclusions), `peel` (Step 2), `y_margins` and `counts_of_cdf` (Step 1).
Events: `Wave30tr.thmA` at `δ/5` (`E⁺`, `E⁻`), two one-sided Hoeffding bounds for the empirical cdf of `d*(X)` at `t_α ± λ_X` and
of `d*(Y)` at `u_α ± λ_Y` (each at `δ/10`, Wave12c `hoeffding_cdf`), and `lem:localmod` at the `J + 1` radii `2θ^{−j}`.
For the last sentence, the event of `thm:trimconsist` is rebuilt (Wave12c `trim_event` with `Wave30az.witnessstab_gen`, no
measurable singletons), keeping the tie set in the band.
-/

noncomputable section
open MeasureTheory Set Finset Filter
open scoped ENNReal InnerProductSpace Pointwise

namespace StatFormal.Wave30tx.RRate

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.Projection StatFormal.TrimmedMMD.ZeroSet
  StatFormal.Wave12c StatFormal.Wave4b StatFormal.Wave30tp StatFormal.Wave30tr StatFormal.Wave30tx

/-! ### Order statistics and union bounds -/

theorem ord_mul_pos {n : ℕ} (v : Fin n → ℝ) (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ord (fun i => c * v i) k = c * ord v k := by
  by_cases hk : k < n
  · refine le_antisymm ?_ ?_
    · rw [ord_le_iff _ k hk]
      have := (ord_le_iff v k hk (ord v k)).1 le_rfl
      refine this.trans (Finset.card_le_card fun i hi => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact mul_le_mul_of_nonneg_left hi hc.le
    · have h := (ord_le_iff (fun i => c * v i) k hk (ord (fun i => c * v i) k)).1 le_rfl
      have : ord v k ≤ c⁻¹ * ord (fun i => c * v i) k := by
        rw [ord_le_iff v k hk]
        refine h.trans (Finset.card_le_card fun i hi => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        rw [le_inv_mul_iff₀ hc]; exact hi
      rwa [le_inv_mul_iff₀ hc] at this
  · simp [ord, hk]

theorem real_inter_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S T : Set Ω} (hT : MeasurableSet T) {a b : ℝ} (hS : 1 - a ≤ μ.real S) (hT' : 1 - b ≤ μ.real T) :
    1 - (a + b) ≤ μ.real (S ∩ T) := by
  have := prob_inter_ge μ (S := S) hT; linarith

theorem real_biInter_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : ℕ → Set Ω) (hE : ∀ j, MeasurableSet (E j)) {a : ℝ} (s : Finset ℕ)
    (h : ∀ j ∈ s, 1 - a ≤ μ.real (E j)) : 1 - s.card * a ≤ μ.real (⋂ j ∈ s, E j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.set_biInter_insert, Finset.card_insert_of_notMem hi]
    have h1 := h i (Finset.mem_insert_self i s)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hm : MeasurableSet (⋂ j ∈ s, E j) := Finset.measurableSet_biInter s fun j _ => hE j
    have := prob_inter_ge μ (S := E i) hm
    push_cast; linarith

theorem ofReal_le_of_real {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {S : Set Ω} {a : ℝ} (h : a ≤ μ.real S) : ENNReal.ofReal a ≤ μ S :=
  ENNReal.ofReal_le_of_le_toReal h

theorem real_of_ofReal_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {S : Set Ω} {a : ℝ} (h : ENNReal.ofReal a ≤ μ S) : a ≤ μ.real S := by
  rcases le_or_gt a 0 with ha | ha
  · exact ha.trans measureReal_nonneg
  · exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h

/-! ### Step 3: the quadratic inequality -/

theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

theorem quad_solve {D r A B : ℝ} (hD : 0 < D) (_hr : 0 ≤ r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : D / 2 * r ^ 2 ≤ A * r + B) : r ≤ (2 * A + √(2 * D * B)) / D := by
  set s := √(2 * D * B) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * D * B := Real.sq_sqrt (by positivity)
  rw [le_div_iff₀ hD]
  by_contra hlt
  push Not at hlt
  have h2 : (r * D) ^ 2 ≤ 2 * A * (r * D) + s ^ 2 := by rw [hs2]; nlinarith
  have hp1 : 0 < r * D - 2 * A - s := by linarith
  have hp2 : 0 < r * D - 2 * A := by linarith
  nlinarith [mul_pos hp1 hp2, mul_nonneg hs0 hp1.le]

/-! ### Step 4: the witness -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_sub_identity (d' d : H) (h' : 0 < ‖d'‖) (h : 0 < ‖d‖) :
    ‖d' - d‖ ^ 2 = (‖d'‖ - ‖d‖) ^ 2 + ‖d'‖ * ‖d‖ * ‖‖d'‖⁻¹ • d' - ‖d‖⁻¹ • d‖ ^ 2 := by
  rw [@norm_sub_sq_real, @norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_inv, abs_norm, abs_norm,
    inv_mul_cancel₀ h'.ne', inv_mul_cancel₀ h.ne']
  field_simp
  ring

theorem witness_bound {d' d : H} {τ ζ : ℝ} (h' : 0 < ‖d'‖) (h : 0 < ‖d‖) (hτ : |‖d'‖ - ‖d‖| ≤ τ)
    (hr : ‖‖d'‖⁻¹ • d' - ‖d‖⁻¹ • d‖ ≤ ζ / ‖d‖) :
    ‖d' - d‖ ≤ τ + √(1 + τ / ‖d‖) * ζ := by
  set D := ‖d‖
  set r := ‖‖d'‖⁻¹ • d' - D⁻¹ • d‖
  have hτ0 : 0 ≤ τ := (abs_nonneg _).trans hτ
  have hr0 : 0 ≤ r := norm_nonneg _
  have hζ : 0 ≤ ζ := by
    have := mul_nonneg (hr0.trans hr) h.le
    rwa [div_mul_cancel₀ _ h.ne'] at this
  have hD'le : ‖d'‖ ≤ D + τ := by linarith [(abs_le.1 hτ).2]
  have hid := norm_sub_identity d' d h' h
  have hsq : ‖d' - d‖ ^ 2 ≤ τ ^ 2 + (D + τ) * D * r ^ 2 := by
    rw [hid]
    have h1 : (‖d'‖ - D) ^ 2 ≤ τ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hτ 2
    have h2 : ‖d'‖ * D * r ^ 2 ≤ (D + τ) * D * r ^ 2 := by gcongr
    linarith
  have hX : √((D + τ) * D * r ^ 2) ≤ √(1 + τ / D) * ζ := by
    have e : (D + τ) * D * r ^ 2 = (1 + τ / D) * (D * r) ^ 2 := by field_simp
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    gcongr
    rwa [le_div_iff₀ h, mul_comm] at hr
  calc ‖d' - d‖ = √(‖d' - d‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(τ ^ 2 + (D + τ) * D * r ^ 2) := Real.sqrt_le_sqrt hsq
    _ ≤ √(τ ^ 2) + √((D + τ) * D * r ^ 2) := sqrt_add_le' (sq_nonneg _) (by positivity)
    _ ≤ τ + √(1 + τ / D) * ζ := by rw [Real.sqrt_sq hτ0]; linarith

end Hilbert

/-! ### Step 2: peeling -/

theorem peel (Z : ℝ → ℝ) (hZ : MonotoneOn Z (Ici 0)) {κL M θ : ℝ} (hκL : 0 ≤ κL) (hθ : 1 < θ) (J : ℕ)
    (hj : ∀ j ≤ J, Z (2 * (θ ^ j)⁻¹) ≤ κL * (2 * (θ ^ j)⁻¹) + M) {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    Z r ≤ κL * (θ * r + 2 * (θ ^ J)⁻¹) + M := by
  have hθ0 : 0 < θ := by linarith
  have hrj0 : ∀ j : ℕ, 0 ≤ 2 * (θ ^ j)⁻¹ := fun j => by positivity
  by_cases hrJ : r ≤ 2 * (θ ^ J)⁻¹
  · have h1 := hZ hr0 (hrj0 J) hrJ
    have h2 := hj J le_rfl
    have : 0 ≤ κL * (θ * r) := mul_nonneg hκL (mul_nonneg hθ0.le hr0)
    nlinarith
  · push Not at hrJ
    set j0 := Nat.findGreatest (fun j => r ≤ 2 * (θ ^ j)⁻¹) J with hj0
    have hP0 : r ≤ 2 * (θ ^ 0)⁻¹ := by simpa using hr2
    have hspec : r ≤ 2 * (θ ^ j0)⁻¹ := Nat.findGreatest_spec (P := fun j => r ≤ 2 * (θ ^ j)⁻¹)
      (Nat.zero_le J) hP0
    have hle : j0 ≤ J := Nat.findGreatest_le J
    have hne : j0 ≠ J := by
      intro h; rw [h] at hspec; linarith
    have hnot : ¬ r ≤ 2 * (θ ^ (j0 + 1))⁻¹ :=
      Nat.findGreatest_is_greatest (P := fun j => r ≤ 2 * (θ ^ j)⁻¹) (Nat.lt_succ_self j0)
        (by omega)
    push Not at hnot
    have hstep : 2 * (θ ^ j0)⁻¹ = θ * (2 * (θ ^ (j0 + 1))⁻¹) := by
      rw [pow_succ]; field_simp
    have hlt : 2 * (θ ^ j0)⁻¹ ≤ θ * r := by
      rw [hstep]; exact mul_le_mul_of_nonneg_left hnot.le hθ0.le
    have h1 := hZ hr0 (hrj0 j0) hspec
    have h2 := hj j0 hle
    have h3 : κL * (2 * (θ ^ j0)⁻¹) ≤ κL * (θ * r) := mul_le_mul_of_nonneg_left hlt hκL
    have h4 : 0 ≤ κL * (2 * (θ ^ J)⁻¹) := mul_nonneg hκL (hrj0 J)
    nlinarith

/-! ### Step 1: the cuts -/

section Cuts

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

theorem atom_zero {Q : Measure 𝒳} {f : 𝒳 → ℝ} {u ρ c : ℝ} (hQ : QDensityLower Q f u ρ c) (hρ : 0 < ρ) :
    Q (f ⁻¹' {u}) = 0 := by
  obtain ⟨g, -, -, hd⟩ := hQ
  rw [hd {u} (measurableSet_singleton u) (fun s hs => by
    rw [Set.mem_singleton_iff] at hs; subst hs; exact ⟨by linarith, by linarith⟩)]
  exact setLIntegral_measure_zero _ _ Real.volume_singleton

theorem y_margins {Q : Measure 𝒳} [IsProbabilityMeasure Q] {f : 𝒳 → ℝ} (hf : Measurable f) {α u ρ c : ℝ}
    (hq : IsQuantile Q f α u) (hQ : QDensityLower Q f u ρ c) (hρ : 0 < ρ) {l : ℝ} (hl0 : 0 < l)
    (hlρ : l ≤ ρ) :
    α + c * l ≤ Q.real {x | f x ≤ u + l} ∧ Q.real {x | f x ≤ u - l} ≤ α - c * l := by
  have hatom := atom_zero hQ hρ
  obtain ⟨g, -, hgl, hd⟩ := hQ
  have hle_eq : Q.real {x | f x ≤ u} = Q.real {x | f x < u} := by
    have hu : {x | f x ≤ u} = {x | f x < u} ∪ f ⁻¹' {u} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_preimage, Set.mem_singleton_iff, le_iff_lt_or_eq]
    have hdisj : Disjoint {x | f x < u} (f ⁻¹' {u}) := Set.disjoint_left.2 fun x hx hx' => by
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff] at hx hx'; linarith
    have h0 : Q.real (f ⁻¹' {u}) = 0 := by simp [measureReal_def, hatom]
    rw [hu, measureReal_union hdisj (hf (measurableSet_singleton u)), h0, add_zero]
  have hGu : Q.real {x | f x ≤ u} = α := by
    have := hq.1; have := hq.2; linarith
  constructor
  · have h2 := density_lower (P := Q) (f := f) hgl hd (a := u) (b := u + l) (by linarith)
      (A := Ioc u (u + l)) measurableSet_Ioc
      (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩) Real.volume_Ioc
    have hunion : {x | f x ≤ u + l} = {x | f x ≤ u} ∪ f ⁻¹' Ioc u (u + l) := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_preimage, Set.mem_Ioc]
      constructor
      · intro h; by_cases h' : f x ≤ u
        · exact Or.inl h'
        · exact Or.inr ⟨not_le.1 h', h⟩
      · rintro (h | h)
        · linarith
        · exact h.2
    have hdisj : Disjoint {x | f x ≤ u} (f ⁻¹' Ioc u (u + l)) :=
      Set.disjoint_left.2 fun x hx hx' => by
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioc] at hx hx'; linarith [hx'.1]
    rw [hunion, measureReal_union hdisj (hf measurableSet_Ioc)]
    rw [show u + l - u = l by ring] at h2
    linarith
  · have h2 := density_lower (P := Q) (f := f) hgl hd (a := u - l) (b := u) (by linarith)
      (A := Ioc (u - l) u) measurableSet_Ioc
      (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩) Real.volume_Ioc
    have hunion : {x | f x ≤ u} = {x | f x ≤ u - l} ∪ f ⁻¹' Ioc (u - l) u := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_preimage, Set.mem_Ioc]
      constructor
      · intro h; by_cases h' : f x ≤ u - l
        · exact Or.inl h'
        · exact Or.inr ⟨not_le.1 h', h⟩
      · rintro (h | h)
        · linarith
        · exact h.2
    have hdisj : Disjoint {x | f x ≤ u - l} (f ⁻¹' Ioc (u - l) u) :=
      Set.disjoint_left.2 fun x hx hx' => by
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioc] at hx hx'; linarith [hx'.1]
    have h3 : Q.real {x | f x ≤ u} = Q.real {x | f x ≤ u - l} + Q.real (f ⁻¹' Ioc (u - l) u) := by
      rw [hunion, measureReal_union hdisj (hf measurableSet_Ioc)]
    rw [show u - (u - l) = l by ring] at h2
    linarith

end Cuts

/-- Counting for the `(k+1)`-th smallest, `k = n_α`, from empirical-cdf bounds at `q ± l` (`c·l = ε + 1/n`). -/
theorem counts_X {n : ℕ} (hn : 1 ≤ n) (w : Fin n → ℝ) {α q l c ε F1 F2 : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hcl : c * l = ε + 1 / n)
    (hA : F1 - ε ≤ (n : ℝ)⁻¹ * ((univ.filter fun i => w i ≤ q + l).card : ℝ))
    (hB : (n : ℝ)⁻¹ * ((univ.filter fun i => w i ≤ q - l).card : ℝ) ≤ F2 + ε)
    (hm1 : (1 - α) + c * l ≤ F1) (hm2 : F2 ≤ (1 - α) - c * l) :
    kfloor n α + 1 ≤ (univ.filter fun i => w i ≤ q + l).card ∧
      (univ.filter fun i => w i ≤ q - l).card < kfloor n α + 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set k := kfloor n α
  have hknp : (k : ℝ) ≤ n * (1 - α) := Nat.floor_le (by nlinarith)
  have hknp1 : (n : ℝ) * (1 - α) < k + 1 := Nat.lt_floor_add_one _
  set a := ((univ.filter fun i => w i ≤ q + l).card : ℝ) with hadef
  set b := ((univ.filter fun i => w i ≤ q - l).card : ℝ) with hbdef
  have ha : (n : ℝ) * (1 - α) + 1 ≤ a := by
    have h1 : (1 - α) + 1 / n ≤ (n : ℝ)⁻¹ * a := by linarith
    have h2 : (n : ℝ) * ((1 - α) + 1 / n) ≤ n * ((n : ℝ)⁻¹ * a) := mul_le_mul_of_nonneg_left h1 hnpos.le
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul, mul_one_div_cancel hnpos.ne'] at h2
    exact h2
  have hb : b ≤ (n : ℝ) * (1 - α) - 1 := by
    have h1 : (n : ℝ)⁻¹ * b ≤ (1 - α) - 1 / n := by linarith
    have h2 : (n : ℝ) * ((n : ℝ)⁻¹ * b) ≤ n * ((1 - α) - 1 / n) := mul_le_mul_of_nonneg_left h1 hnpos.le
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul, mul_one_div_cancel hnpos.ne'] at h2
    exact h2
  constructor
  · have : (k : ℝ) + 1 ≤ a := by linarith
    rw [hadef] at this; exact_mod_cast this
  · have : b < (k : ℝ) + 1 := by linarith
    rw [hbdef] at this; exact_mod_cast this

/-- Counting for the `(m_α+1)`-th largest, i.e. the `(k'+1)`-th smallest with `k' = m − m_α − 1`, from empirical-cdf bounds
at `u ± l` around an `α`-quantile (`c·l = ε + 1/m`). -/
theorem counts_Y {m : ℕ} (hm : 1 ≤ m) (w : Fin m → ℝ) {α q l c ε G1 G2 : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hcl : c * l = ε + 1 / m)
    (hA : G1 - ε ≤ (m : ℝ)⁻¹ * ((univ.filter fun i => w i ≤ q + l).card : ℝ))
    (hB : (m : ℝ)⁻¹ * ((univ.filter fun i => w i ≤ q - l).card : ℝ) ≤ G2 + ε)
    (hm1 : α + c * l ≤ G1) (hm2 : G2 ≤ α - c * l) :
    kfloor m α < m ∧ (m - kfloor m α - 1) + 1 ≤ (univ.filter fun i => w i ≤ q + l).card ∧
      (univ.filter fun i => w i ≤ q - l).card < (m - kfloor m α - 1) + 1 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set k := kfloor m α
  have hknp : (k : ℝ) ≤ m * (1 - α) := Nat.floor_le (by nlinarith)
  have hknp1 : (m : ℝ) * (1 - α) < k + 1 := Nat.lt_floor_add_one _
  have hkm : k < m := by
    have : (k : ℝ) < m := by nlinarith
    exact_mod_cast this
  have hidx : m - k - 1 + 1 = m - k := by omega
  have hcast : ((m - k : ℕ) : ℝ) = m - k := by rw [Nat.cast_sub hkm.le]
  set a := ((univ.filter fun i => w i ≤ q + l).card : ℝ) with hadef
  set b := ((univ.filter fun i => w i ≤ q - l).card : ℝ) with hbdef
  have ha : (m : ℝ) * α + 1 ≤ a := by
    have h1 : α + 1 / m ≤ (m : ℝ)⁻¹ * a := by linarith
    have h2 : (m : ℝ) * (α + 1 / m) ≤ m * ((m : ℝ)⁻¹ * a) := mul_le_mul_of_nonneg_left h1 hmpos.le
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hmpos.ne', one_mul, mul_one_div_cancel hmpos.ne'] at h2
    exact h2
  have hb : b ≤ (m : ℝ) * α - 1 := by
    have h1 : (m : ℝ)⁻¹ * b ≤ α - 1 / m := by linarith
    have h2 : (m : ℝ) * ((m : ℝ)⁻¹ * b) ≤ m * (α - 1 / m) := mul_le_mul_of_nonneg_left h1 hmpos.le
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hmpos.ne', one_mul, mul_one_div_cancel hmpos.ne'] at h2
    exact h2
  refine ⟨hkm, ?_, ?_⟩
  · rw [hidx]
    have : ((m - k : ℕ) : ℝ) ≤ a := by rw [hcast]; nlinarith
    rw [hadef] at this; exact_mod_cast this
  · rw [hidx]
    have : b < ((m - k : ℕ) : ℝ) := by rw [hcast]; nlinarith
    rw [hbdef] at this; exact_mod_cast this

/-! ### Step 5: the kept set -/

section Kept

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem plugDensityFn_mem {α : ℝ} (hα1 : α < 1) {ϑ : 𝒳 → ℝ} (hϑ : ∀ x, 0 ≤ ϑ x ∧ ϑ x ≤ 1 / (1 - α))
    (f : 𝒳 → ℝ) (t : ℝ) (x : 𝒳) :
    0 ≤ plugDensityFn α ϑ f t x ∧ plugDensityFn α ϑ f t x ≤ 1 / (1 - α) := by
  have h : 0 < 1 / (1 - α) := by
    have : 0 < 1 - α := by linarith
    positivity
  unfold plugDensityFn
  split_ifs
  · exact ⟨h.le, le_rfl⟩
  · exact hϑ x
  · exact ⟨le_rfl, h.le⟩

/-- Step 5: the mass and density bounds of the kept set from the two band inclusions (any tie functions). -/
theorem kept_of_band (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H} (hφ : StronglyMeasurable φ)
    {α ρ Cf : ℝ} (hα1 : α < 1) {dstar dh : H} {tα th ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hCf : 0 ≤ Cf)
    (g : ℝ → ℝ) (hg : ∀ s ∈ Icc (tα - ρ) (tα + ρ), g s ≤ Cf)
    (hd : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (tα - ρ) (tα + ρ) →
      P (witFn dstar φ ⁻¹' A) = ∫⁻ s in A, ENNReal.ofReal (g s))
    (hsd : symmDiff {x | witFn dh φ x < th} {x | witFn dstar φ x < tα} ⊆
      {x | |witFn dstar φ x - tα| ≤ ℓ})
    (htie : ∀ x, witFn dh φ x = th → |witFn dstar φ x - tα| ≤ ℓ) :
    KeptConcl P φ α ρ Cf dstar dh tα th ℓ := by
  refine ⟨hsd, fun hℓρ => ?_⟩
  have hf : Measurable (witFn dstar φ) := measurable_witFn hφ dstar
  set B := {x | |witFn dstar φ x - tα| ≤ ℓ} with hBdef
  have hBeq : B = witFn dstar φ ⁻¹' Icc (tα - ℓ) (tα + ℓ) := by
    ext x; simp only [hBdef, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc, abs_le]; constructor <;>
      rintro ⟨a, b⟩ <;> constructor <;> linarith
  have hBm : MeasurableSet B := by rw [hBeq]; exact hf measurableSet_Icc
  have hPB : P B ≤ ENNReal.ofReal (2 * Cf * ℓ) := by
    rw [hBeq]
    have := density_upper (P := P) (f := witFn dstar φ) hg hd
      (a := tα - ℓ) (b := tα + ℓ) (A := Icc (tα - ℓ) (tα + ℓ)) measurableSet_Icc
      (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩) Real.volume_Icc
    rwa [show Cf * (tα + ℓ - (tα - ℓ)) = 2 * Cf * ℓ by ring] at this
  refine ⟨(measure_mono hsd).trans hPB, fun ϑ ϑh hϑ hϑh => ?_⟩
  have hα' : 0 < 1 - α := by linarith
  have hpt : ∀ x, |plugDensityFn α ϑh (witFn dh φ) th x - plugDensityFn α ϑ (witFn dstar φ) tα x| ≤
      B.indicator (fun _ => 1 / (1 - α)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      have ha := plugDensityFn_mem hα1 hϑh (witFn dh φ) th x
      have hb := plugDensityFn_mem hα1 hϑ (witFn dstar φ) tα x
      rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    · rw [Set.indicator_of_notMem hx]
      have hnot : x ∉ symmDiff {x | witFn dh φ x < th} {x | witFn dstar φ x < tα} :=
        fun h => hx (hsd h)
      have hne1 : witFn dh φ x ≠ th := fun h => hx (htie x h)
      have hne2 : witFn dstar φ x ≠ tα := fun h => hx (by simp [hBdef, h, hℓ])
      simp only [Set.mem_symmDiff, Set.mem_setOf_eq, not_or, not_and, not_not] at hnot
      unfold plugDensityFn
      by_cases hlt : witFn dh φ x < th
      · have := hnot.1 hlt
        simp [hlt, this]
      · have hlt2 : ¬ witFn dstar φ x < tα := fun h => hlt (hnot.2 h)
        simp [hlt, hlt2, hne1, hne2]
  have hRHS : 0 ≤ 2 * Cf * ℓ / (1 - α) := by positivity
  by_cases hint : Integrable (fun x => |plugDensityFn α ϑh (witFn dh φ) th x -
      plugDensityFn α ϑ (witFn dstar φ) tα x|) P
  · calc ∫ x, |plugDensityFn α ϑh (witFn dh φ) th x - plugDensityFn α ϑ (witFn dstar φ) tα x| ∂P
        ≤ ∫ x, B.indicator (fun _ => 1 / (1 - α)) x ∂P :=
          integral_mono hint ((integrable_const _).indicator hBm) hpt
      _ = P.real B * (1 / (1 - α)) := by rw [integral_indicator_const _ hBm, smul_eq_mul]
      _ ≤ (2 * Cf * ℓ) * (1 / (1 - α)) := by
          gcongr
          exact ENNReal.toReal_le_of_le_ofReal (by positivity) hPB
      _ = 2 * Cf * ℓ / (1 - α) := by ring
  · rw [integral_undef hint]; exact hRHS

end Kept

/-! ### Scaling and constants -/

section Scal

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem witFn_smul (c : ℝ) (d : H) (φ : 𝒳 → H) (x : 𝒳) : witFn (c • d) φ x = c * witFn d φ x := by
  simp only [witFn, real_inner_smul_left]

theorem abs_witFn_sub_le {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (a b : H) (x : 𝒳) :
    |witFn a φ x - witFn b φ x| ≤ κ * ‖a - b‖ := by
  have : witFn a φ x - witFn b φ x = witFn (a - b) φ x := by simp only [witFn, inner_sub_left]
  rw [this, mul_comm]; exact abs_witFn_le hκ (a - b) x

end Scal

theorem Mloc_div {D : ℝ} (hD : 0 < D) (l1 l2 χ : ℝ) (n m : ℕ) :
    Mloc (l1 / D) (l2 / D) χ n m = Mloc l1 l2 χ n m / D := by
  unfold Mloc
  have e : 2 * χ * ((l1 / D) ^ 2 / n + (l2 / D) ^ 2 / m) = 2 * χ * (l1 ^ 2 / n + l2 ^ 2 / m) / D ^ 2 := by
    field_simp
  rw [e, Real.sqrt_div' _ (sq_nonneg D), Real.sqrt_sq hD.le]
  field_simp

theorem Lloc_nonneg (χ : ℝ) (n m : ℕ) : 0 ≤ Lloc χ n m := by
  unfold Lloc
  have := ek_nonneg n; have := ek_nonneg m
  positivity

theorem Mloc_nonneg {l1 l2 : ℝ} (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) (χ : ℝ) (n m : ℕ) : 0 ≤ Mloc l1 l2 χ n m := by
  unfold Mloc
  have := ek_nonneg n; have := ek_nonneg m
  positivity

theorem lamQ_pos {c : ℝ} (hc : 0 < c) (δ : ℝ) {n : ℕ} (hn : 1 ≤ n) : 0 < lamQ c δ n := by
  unfold lamQ
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem scale_le {D a b : ℝ} (hD : 0 < D) : D⁻¹ * a ≤ b / D ↔ a ≤ b := by
  rw [inv_mul_eq_div, div_le_div_iff_of_pos_right hD]

theorem scale_lt {D a b : ℝ} (hD : 0 < D) : D⁻¹ * a < b / D ↔ a < b := by
  rw [inv_mul_eq_div, div_lt_div_iff_of_pos_right hD]

/-! ### The event of `thm:trimrate` -/

section Main

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

set_option maxHeartbeats 1600000 in
/-- The event of `thm:trimrate` (i)–(iii), together with the tie set `{d̂ = t̂_n}` inside the band of half-width `ℓ^loc`. -/
theorem rate_event (hb : Claims.basicineq) (hl : Claims.localmod)
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ Dφ α δ θ ρ cf Cf cf' uα : ℝ} {n m : ℕ} {dstar : H}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ)
    (hα0 : 0 < α) (hα1 : α < 1) (hD : 0 < Dpop φ P Q α)
    (hmin : IsMinNorm (region φ α P - region φ α Q) dstar)
    (hρ : 0 < ρ) (hcf : 0 < cf) (hcf' : 0 < cf')
    (hQd : QDensity P (witFn dstar φ) (quantileAt P (witFn dstar φ) (1 - α)) ρ cf Cf)
    (hqu : IsQuantile Q (witFn dstar φ) α uα) (hQd' : QDensityLower Q (witFn dstar φ) uα ρ cf')
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hθ : 1 < θ)
    (hτ : tauA κ Dφ α (δ / 5) n m < Dpop φ P Q α) (hlam : max (lamQ cf δ n) (lamQ cf' δ m) ≤ ρ) :
    ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
      ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m E ∧
      ∀ z ∈ E, ∀ pr ∈ capped n α ×ˢ capped m α,
        IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m α) pr →
          RateConcl P Q φ κ Dφ α δ θ ρ cf Cf cf' n m dstar z pr ∧
          ∀ x, witFn (witness φ z.1 z.2 pr) φ x = tHat φ (witness φ z.1 z.2 pr) α z.1 →
            |witFn dstar φ x - quantileAt P (witFn dstar φ) (1 - α)| ≤
              ellLoc κ (zetaLoc κ α (Dpop φ P Q α) θ (Jpeel θ n m) (Lloc (chiPeel θ δ n m) n m)
                (Mloc (lamQ cf δ n) (lamQ cf' δ m) (chiPeel θ δ n m) n m)) (lamQ cf δ n) := by
  classical
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x₀)
  have hn0 : n ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have h1α : 0 < 1 - α := by linarith
  have hθ0 : 0 < θ := by linarith
  set D := Dpop φ P Q α with hDdef
  have hDn : D = ‖dstar‖ := RBasic.Dpop_eq_norm hmin
  set fstar : H := D⁻¹ • dstar with hfstar
  set f := witFn dstar φ with hfdef
  set tα := quantileAt P f (1 - α) with htα
  set lX := lamQ cf δ n with hlX
  set lY := lamQ cf' δ m with hlY
  set J := Jpeel θ n m with hJ
  set χ := chiPeel θ δ n m with hχ
  set L := Lloc χ n m with hL
  set M := Mloc lX lY χ n m with hM
  set ζ := zetaLoc κ α D θ J L M with hζ
  set τA := tauA κ Dφ α (δ / 5) n m with hτA
  set tstar := tα / D with htstar
  set ustar := uα / D with hustar
  set rr : ℕ → ℝ := fun j => 2 * (θ ^ j)⁻¹ with hrr
  have hfm : Measurable f := measurable_witFn hφ dstar
  have hK : ∀ x, |f x| ≤ ‖dstar‖ * κ := abs_witFn_le hκ dstar
  obtain ⟨g, -, hgb, hgd⟩ := hQd
  have hCf : 0 ≤ Cf := by
    have := hgb tα ⟨by linarith, by linarith⟩
    linarith [this.1, this.2]
  have hlX0 : 0 < lX := lamQ_pos hcf δ hn
  have hlY0 : 0 < lY := lamQ_pos hcf' δ hm
  have hlXρ : lX ≤ ρ := (le_max_left _ _).trans hlam
  have hlYρ : lY ≤ ρ := (le_max_right _ _).trans hlam
  have hL0 : 0 ≤ L := Lloc_nonneg χ n m
  have hM0 : 0 ≤ M := Mloc_nonneg hlX0.le hlY0.le χ n m
  have hMD : Mloc (lX / D) (lY / D) χ n m = M / D := Mloc_div hD lX lY χ n m
  have hζ0 : 0 ≤ ζ := by
    simp only [hζ, zetaLoc]
    have : 0 ≤ 2 * θ * κ * L / (1 - α) := by positivity
    linarith [Real.sqrt_nonneg (2 * (2 * (θ ^ J)⁻¹ * κ * D * L + M) / (1 - α))]
  -- events 1: Theorem A at δ/5
  obtain ⟨Ep, Em, hEpm, hEpp, hEmm, hEmp, hEp, hEm⟩ :=
    StatFormal.Wave30tr.thmA 𝒳 H φ κ Dφ P Q (δ / 5) n m hφ hκ hDφ (by positivity) (by linarith) hn hm
  -- events 2: X side
  have hlog : Real.log (1 / (δ / 10)) = Real.log (10 / δ) := by congr 1; field_simp
  have hδ10 : 0 < δ / 10 := by positivity
  have hδ101 : δ / 10 ≤ 1 := by linarith
  set εn := √(Real.log (10 / δ) / (2 * n)) with hεn
  set εm := √(Real.log (10 / δ) / (2 * m)) with hεm
  obtain ⟨hEa, -⟩ := hoeffding_cdf P hfm (tα + lX) hn0 hδ10 hδ101
  obtain ⟨-, hEb⟩ := hoeffding_cdf P hfm (tα - lX) hn0 hδ10 hδ101
  obtain ⟨hEc, -⟩ := hoeffding_cdf Q hfm (uα + lY) hm0 hδ10 hδ101
  obtain ⟨-, hEd⟩ := hoeffding_cdf Q hfm (uα - lY) hm0 hδ10 hδ101
  rw [hlog] at hEa hEb hEc hEd
  set Ea := {x : Fin n → 𝒳 | P.real {y | f y ≤ tα + lX} - εn ≤ empCdf f x (tα + lX)} with hEadef
  set Eb := {x : Fin n → 𝒳 | empCdf f x (tα - lX) ≤ P.real {y | f y ≤ tα - lX} + εn} with hEbdef
  set Ec := {y : Fin m → 𝒳 | Q.real {w | f w ≤ uα + lY} - εm ≤ empCdf f y (uα + lY)} with hEcdef
  set Ed := {y : Fin m → 𝒳 | empCdf f y (uα - lY) ≤ Q.real {w | f w ≤ uα - lY} + εm} with hEddef
  have hmEa : MeasurableSet Ea := measurableSet_le measurable_const (measurable_empCdf hfm n _)
  have hmEb : MeasurableSet Eb := measurableSet_le (measurable_empCdf hfm n _) measurable_const
  have hmEc : MeasurableSet Ec := measurableSet_le measurable_const (measurable_empCdf hfm m _)
  have hmEd : MeasurableSet Ed := measurableSet_le (measurable_empCdf hfm m _) measurable_const
  -- events 3: the local process at the radii
  have hl1 : 0 ≤ lX / D := by positivity
  have hl2 : 0 ≤ lY / D := by positivity
  set Zf : ℝ → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ :=
    fun r z => Zloc P Q φ fstar tstar ustar κ r (lX / D) (lY / D) z with hZf
  set EZj : ℕ → Set ((Fin n → 𝒳) × (Fin m → 𝒳)) :=
    fun j => {z | Zf (rr j) z ≤ κ * rr j * L + M / D} with hEZj
  have hrr0 : ∀ j, 0 ≤ rr j := fun j => by simp only [hrr]; positivity
  have hEZm : ∀ j, MeasurableSet (EZj j) := fun j =>
    measurableSet_le (hl 𝒳 H P Q φ κ fstar tstar ustar (rr j) (lX / D) (lY / D) n m hφ hκ (hrr0 j) hl1 hl2
      hn hm).1 measurable_const
  have hχexp : Real.exp (-χ) = δ / (5 * ((J : ℝ) + 1)) := by
    simp only [hχ, chiPeel, ← hJ]
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hχ0 : 0 < χ := by
    simp only [hχ, chiPeel, ← hJ]
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hδ0]
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith
  have hEZp : ∀ j, 1 - δ / (5 * ((J : ℝ) + 1)) ≤ (sampleLaw P Q n m).real (EZj j) := by
    intro j
    have h := (hl 𝒳 H P Q φ κ fstar tstar ustar (rr j) (lX / D) (lY / D) n m hφ hκ (hrr0 j) hl1 hl2
      hn hm).2.2.2.2.2.2 χ hχ0
    rw [hχexp, hMD] at h
    exact real_of_ofReal_le h
  set EZ := ⋂ j ∈ Finset.range (J + 1), EZj j with hEZdef
  have hmEZ : MeasurableSet EZ := Finset.measurableSet_biInter _ fun j _ => hEZm j
  have hEZpr : 1 - δ / 5 ≤ (sampleLaw P Q n m).real EZ := by
    have := real_biInter_ge (sampleLaw P Q n m) EZj hEZm (Finset.range (J + 1))
      (fun j _ => hEZp j)
    rw [Finset.card_range] at this
    have e : ((J + 1 : ℕ) : ℝ) * (δ / (5 * ((J : ℝ) + 1))) = δ / 5 := by
      push_cast; field_simp
    linarith
  -- the event
  set E := Ep ∩ Em ∩ ((Ea ∩ Eb) ×ˢ (univ : Set (Fin m → 𝒳))) ∩
    ((univ : Set (Fin n → 𝒳)) ×ˢ (Ec ∩ Ed)) ∩ EZ with hEdef
  have hmX : MeasurableSet ((Ea ∩ Eb) ×ˢ (univ : Set (Fin m → 𝒳))) :=
    (hmEa.inter hmEb).prod MeasurableSet.univ
  have hmY : MeasurableSet ((univ : Set (Fin n → 𝒳)) ×ˢ (Ec ∩ Ed)) :=
    MeasurableSet.univ.prod (hmEc.inter hmEd)
  refine ⟨E, (((hEpm.inter hEmm).inter hmX).inter hmY).inter hmEZ, ?_, ?_⟩
  · -- probability
    have hpX : 1 - δ / 5 ≤ (sampleLaw P Q n m).real ((Ea ∩ Eb) ×ˢ (univ : Set (Fin m → 𝒳))) := by
      have h := real_inter_ge (Measure.pi fun _ : Fin n => P) (S := Ea) hmEb hEa hEb
      have e : (sampleLaw P Q n m).real ((Ea ∩ Eb) ×ˢ (univ : Set (Fin m → 𝒳))) =
          (Measure.pi fun _ : Fin n => P).real (Ea ∩ Eb) := by
        simp [sampleLaw, measureReal_def, Measure.prod_prod]
      rw [e]; linarith
    have hpY : 1 - δ / 5 ≤ (sampleLaw P Q n m).real ((univ : Set (Fin n → 𝒳)) ×ˢ (Ec ∩ Ed)) := by
      have h := real_inter_ge (Measure.pi fun _ : Fin m => Q) (S := Ec) hmEd hEc hEd
      have e : (sampleLaw P Q n m).real ((univ : Set (Fin n → 𝒳)) ×ˢ (Ec ∩ Ed)) =
          (Measure.pi fun _ : Fin m => Q).real (Ec ∩ Ed) := by
        simp [sampleLaw, measureReal_def, Measure.prod_prod]
      rw [e]; linarith
    have h1 := real_inter_ge (sampleLaw P Q n m) (S := Ep) hEmm (real_of_ofReal_le hEpp)
      (real_of_ofReal_le hEmp)
    have h2 := real_inter_ge (sampleLaw P Q n m) (S := Ep ∩ Em) hmX h1 hpX
    have h3 := real_inter_ge (sampleLaw P Q n m) (S := Ep ∩ Em ∩ _) hmY h2 hpY
    have h4 := real_inter_ge (sampleLaw P Q n m) (S := Ep ∩ Em ∩ _ ∩ _) hmEZ h3 hEZpr
    exact ofReal_le_of_real (by linarith)
  · -- the deterministic steps
    rintro z ⟨⟨⟨⟨hzp, hzm⟩, ⟨hza, hzb⟩, -⟩, -, ⟨hzc, hzd⟩⟩, hzZ⟩ pr hpr hprmin
    have hzZ' : ∀ j ≤ J, Zf (rr j) z ≤ κ * rr j * L + M / D := by
      intro j hj
      have := Set.mem_iInter₂.1 hzZ j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
      exact this
    set dh := witness φ z.1 z.2 pr with hdhdef
    have hDh : Demp φ z.1 z.2 α = ‖dh‖ := RBasic.Demp_eq_norm hφ hα0.le hα1 hn hm z.1 z.2 hpr hprmin
    have hαI : α ∈ Ico (0 : ℝ) 1 := ⟨hα0.le, hα1⟩
    have hup := (hEp z hzp α hαI).1
    have hlow := hEm z hzm α hαI
    set Dh := Demp φ z.1 z.2 α with hDhdef
    have hDhpos : 0 < Dh := by linarith
    have hdhpos : 0 < ‖dh‖ := hDh ▸ hDhpos
    have hdspos : 0 < ‖dstar‖ := hDn ▸ hD
    set fh : H := Dh⁻¹ • dh with hfhdef
    have hfh1 : ‖fh‖ = 1 := by
      rw [hfhdef, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hDhpos, hDh, inv_mul_cancel₀ hdhpos.ne']
    have hfs1 : ‖fstar‖ = 1 := by
      rw [hfstar, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hD, hDn, inv_mul_cancel₀ hdspos.ne']
    set r := ‖fh - fstar‖ with hrdef
    have hr0 : 0 ≤ r := norm_nonneg _
    have hr2 : r ≤ 2 := (norm_sub_le _ _).trans (by rw [hfh1, hfs1]; norm_num)
    have hsup : ∀ x, |witFn fh φ x - witFn fstar φ x| ≤ κ * r := fun x => abs_witFn_sub_le hκ fh fstar x
    have hwfh : ∀ x, witFn fh φ x = Dh⁻¹ * witFn dh φ x := fun x => witFn_smul _ _ _ _
    have hwfs : ∀ x, witFn fstar φ x = D⁻¹ * f x := fun x => witFn_smul _ _ _ _
    have hwfs' : ∀ x, f x = D * witFn fstar φ x := fun x => by
      rw [hwfs, ← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul]
    set th := tHat φ dh α z.1 with hthdef
    set th' := ord (fun i => witFn fh φ (z.1 i)) (kfloor n α) with hth'def
    have hth' : th' = Dh⁻¹ * th := by
      rw [hth'def, hthdef, tHat, ← ord_mul_pos _ _ (inv_pos.2 hDhpos)]
      simp only [hwfh]
    set uh' := ordTop (fun j => witFn fh φ (z.2 j)) α with huh'def
    -- Step 1: the cuts
    have hcX : cf * lX = εn + 1 / n := by
      simp only [hlX, lamQ, hεn]; field_simp
    have hcY : cf' * lY = εm + 1 / m := by
      simp only [hlY, lamQ, hεm]; field_simp
    have hmarX := margins (P := P) hfm hK hα1 hα0.le g (fun s hs => (hgb s hs).1) hgd hlX0 hlXρ
    have hmarY := y_margins (Q := Q) hfm hqu hQd' hρ hlY0 hlYρ
    have hza' := hza; have hzb' := hzb; have hzc' := hzc; have hzd' := hzd
    simp only [hEadef, hEbdef, hEcdef, hEddef, Set.mem_setOf_eq, empCdf_eq_card] at hza' hzb' hzc' hzd'
    obtain ⟨hAX, hBX⟩ := counts_X hn (fun i => f (z.1 i)) hα0.le hα1 hcX hza' hzb' hmarX.1 hmarX.2
    obtain ⟨hkm, hAY, hBY⟩ := counts_Y hm (fun j => f (z.2 j)) hα0 hα1 hcY hzc' hzd' hmarY.1 hmarY.2
    have hkn : kfloor n α < n := by
      rw [kfloor, Nat.floor_lt (by nlinarith)]; nlinarith
    have hfilX : ∀ s : ℝ, (univ.filter fun i => witFn fstar φ (z.1 i) ≤ s / D) =
        univ.filter fun i => f (z.1 i) ≤ s := fun s => by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hwfs, scale_le hD]
    have hfilY : ∀ s : ℝ, (univ.filter fun j => witFn fstar φ (z.2 j) ≤ s / D) =
        univ.filter fun j => f (z.2 j) ≤ s := fun s => by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hwfs, scale_le hD]
    have htX : |th' - tstar| ≤ κ * r + lX / D := by
      refine tHat_bounds (fun i => witFn fh φ (z.1 i)) (fun i => witFn fstar φ (z.1 i)) hkn
        (fun i => hsup (z.1 i)) ?_ ?_
      · rw [htstar, ← add_div, hfilX]; exact hAX
      · rw [htstar, ← sub_div, hfilX]; exact hBX
    have htY : |uh' - ustar| ≤ κ * r + lY / D := by
      refine tHat_bounds (fun j => witFn fh φ (z.2 j)) (fun j => witFn fstar φ (z.2 j)) (by omega)
        (fun j => hsup (z.2 j)) ?_ ?_
      · rw [hustar, ← add_div, hfilY]; exact hAY
      · rw [hustar, ← sub_div, hfilY]; exact hBY
    -- the quantiles of `f*`
    have hp0 : 0 < 1 - α := h1α
    have hqP : IsQuantile P (witFn ((Dpop φ P Q α)⁻¹ • dstar) φ) (1 - α) tstar := by
      have e1 : {x | witFn fstar φ x < tstar} = {x | f x < tα} := by
        ext x; simp only [Set.mem_setOf_eq, hwfs, htstar, scale_lt hD]
      have e2 : {x | witFn fstar φ x ≤ tstar} = {x | f x ≤ tα} := by
        ext x; simp only [Set.mem_setOf_eq, hwfs, htstar, scale_le hD]
      refine ⟨?_, ?_⟩
      · change P.real {x | witFn fstar φ x < tstar} ≤ 1 - α
        rw [e1]; exact quantile_lt_le P hfm hK hp0 (by linarith)
      · change 1 - α ≤ P.real {x | witFn fstar φ x ≤ tstar}
        rw [e2]; exact quantile_ge P hfm hK hp0 (by linarith)
    have hqQ : IsQuantile Q (witFn ((Dpop φ P Q α)⁻¹ • dstar) φ) α ustar := by
      have e1 : {x | witFn fstar φ x < ustar} = {x | f x < uα} := by
        ext x; simp only [Set.mem_setOf_eq, hwfs, hustar, scale_lt hD]
      have e2 : {x | witFn fstar φ x ≤ ustar} = {x | f x ≤ uα} := by
        ext x; simp only [Set.mem_setOf_eq, hwfs, hustar, scale_le hD]
      refine ⟨?_, ?_⟩
      · change Q.real {x | witFn fstar φ x < ustar} ≤ α
        rw [e1]; exact hqu.1
      · change α ≤ Q.real {x | witFn fstar φ x ≤ ustar}
        rw [e2]; exact hqu.2
    -- the basic inequality and the local process
    obtain ⟨hb1, hb2⟩ := hb 𝒳 H P Q φ κ α tstar ustar n m dstar hφ hκ hα0 hα1 hn hm hmin hD hqP hqQ
      z.1 z.2 pr hpr hprmin hDhpos
    have hbasic : D / 2 * r ^ 2 ≤ 1 / (1 - α) * rampDev P Q φ fstar tstar ustar z (fh, th', uh') :=
      le_trans hb1 hb2
    obtain ⟨-, -, hub, -, -, -, -⟩ :=
      hl 𝒳 H P Q φ κ fstar tstar ustar r (lX / D) (lY / D) n m hφ hκ hr0 hl1 hl2 hn hm
    have hmono := (hl 𝒳 H P Q φ κ fstar tstar ustar 0 (lX / D) (lY / D) n m hφ hκ le_rfl hl1 hl2
      hn hm).2.2.2.1 z
    have hmem : (fh, th', uh') ∈ rampPar fstar tstar ustar κ r (lX / D) (lY / D) := ⟨le_rfl, htX, htY⟩
    have hZr : rampDev P Q φ fstar tstar ustar z (fh, th', uh') ≤ Zf r z := hub z _ hmem
    -- Step 2: peeling
    have hpeel := peel (fun r' => Zf r' z) hmono (mul_nonneg hκ0 hL0) (M := M / D) hθ J
      (fun j hj => by
        have h := hzZ' j hj
        have e : κ * rr j * L = κ * L * rr j := by ring
        simp only [hrr] at h e ⊢
        linarith) hr0 hr2
    -- Step 3: the direction
    set A := 1 / (1 - α) * (κ * L) * θ with hA
    set B := 1 / (1 - α) * (κ * L * rr J + M / D) with hB
    have hA0 : 0 ≤ A := by positivity
    have hB0 : 0 ≤ B := by
      have : 0 ≤ M / D := div_nonneg hM0 hD.le
      have : 0 ≤ rr J := hrr0 J
      positivity
    have hquad : D / 2 * r ^ 2 ≤ A * r + B := by
      have h1 : D / 2 * r ^ 2 ≤ 1 / (1 - α) * Zf r z :=
        hbasic.trans (mul_le_mul_of_nonneg_left hZr (by positivity))
      have h2 : 1 / (1 - α) * Zf r z ≤ 1 / (1 - α) * (κ * L * (θ * r + 2 * (θ ^ J)⁻¹) + M / D) :=
        mul_le_mul_of_nonneg_left hpeel (by positivity)
      have h3 : 1 / (1 - α) * (κ * L * (θ * r + 2 * (θ ^ J)⁻¹) + M / D) = A * r + B := by
        simp only [hA, hB, hrr]; ring
      linarith
    have hrζ : r ≤ ζ / D := by
      have := quad_solve hD hr0 hA0 hB0 hquad
      have e : 2 * A + √(2 * D * B) = ζ := by
        have e1 : 2 * D * B = 2 * (2 * (θ ^ J)⁻¹ * κ * D * L + M) / (1 - α) := by
          simp only [hB, hrr]; field_simp
        rw [e1, hζ, zetaLoc, hA]; ring
      rwa [e] at this
    have hDr : D * r ≤ ζ := by rwa [le_div_iff₀ hD, mul_comm] at hrζ
    -- Step 4: the witness
    have hτabs : |‖dh‖ - ‖dstar‖| ≤ τA := by
      rw [← hDh, ← hDn, abs_le]; constructor <;> linarith
    have hwit : ‖dh - dstar‖ ≤ τA + √(1 + τA / D) * ζ := by
      have hr' : ‖‖dh‖⁻¹ • dh - ‖dstar‖⁻¹ • dstar‖ ≤ ζ / ‖dstar‖ := by
        rw [← hDh, ← hDn]; exact hrζ
      have := witness_bound hdhpos hdspos hτabs hr'
      rwa [← hDn] at this
    -- Step 5: the kept set
    have hcut : |th / Dh - tα / D| ≤ (κ * ζ + lX) / D := by
      have e : th / Dh = th' := by rw [hth', div_eq_inv_mul]
      rw [e]
      calc |th' - tα / D| ≤ κ * r + lX / D := htX
        _ ≤ κ * (ζ / D) + lX / D := by gcongr
        _ = (κ * ζ + lX) / D := by ring
    set ℓ := ellLoc κ ζ lX with hℓdef
    have hℓ0 : 0 ≤ ℓ := by simp only [hℓdef, ellLoc]; positivity
    have hband := band_incl (fun x => D * witFn fh φ x) f (Δ := D * (κ * r)) (th := D * th') (q := tα)
      (ε := D * (κ * r) + lX) (Λ := ℓ)
      (fun x => by
        rw [hwfs' x, ← mul_sub, abs_mul, abs_of_pos hD]
        exact mul_le_mul_of_nonneg_left (hsup x) hD.le)
      (by
        have e : D * th' - tα = D * (th' - tstar) := by
          rw [htstar, mul_sub, mul_div_cancel₀ _ hD.ne']
        rw [e, abs_mul, abs_of_pos hD]
        calc D * |th' - tstar| ≤ D * (κ * r + lX / D) := mul_le_mul_of_nonneg_left htX hD.le
          _ = D * (κ * r) + lX := by field_simp)
      (by
        have e : ℓ = 2 * κ * ζ + lX := rfl
        have h1 := mul_le_mul_of_nonneg_left hDr hκ0
        have e2 : D * (κ * r) = κ * (D * r) := by ring
        rw [e]; linarith)
    have hsetA : {x | D * witFn fh φ x < D * th'} = {x | witFn dh φ x < th} := by
      ext x
      simp only [Set.mem_setOf_eq, hwfh, hth', mul_lt_mul_iff_right₀ hD,
        mul_lt_mul_iff_right₀ (inv_pos.2 hDhpos)]
    have hsd : symmDiff {x | witFn dh φ x < th} {x | witFn dstar φ x < tα} ⊆
        {x | |witFn dstar φ x - tα| ≤ ℓ} := by
      rw [← hsetA]; exact hband.1
    have htie : ∀ x, witFn dh φ x = th → |witFn dstar φ x - tα| ≤ ℓ := by
      intro x hx
      refine hband.2 x ?_
      simp only [hwfh, hth', hx]
    refine ⟨?_, htie⟩
    unfold RateConcl
    intro D' τA' lX' lY' χ' ζ' tα' dh' Dh' th''
    exact ⟨⟨hDhpos, hrζ⟩, hwit, hcut,
      kept_of_band P hφ hα1 hℓ0 hCf g (fun s hs => (hgb s hs).2) hgd hsd htie⟩

/-! ### The event of `thm:trimconsist`, without measurable singletons -/

set_option maxHeartbeats 1600000 in
/-- Wave12c `trim_event` rebuilt on `Wave30az.witnessstab_gen` (no `MeasurableSingletonClass`), with the event constructed
unconditionally and the deterministic consequences (cut, band, tie set) under `ℓ_{n,m} ≤ ρ`. -/
theorem consist_event [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ α δ ρ cf : ℝ} {n m : ℕ} {dstar : H}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hmin : IsMinNorm (region φ α P - region φ α Q) dstar) (hρ : 0 < ρ) (hcf : 0 < cf)
    (g : ℝ → ℝ)
    (hgl : ∀ s ∈ Icc (quantileAt P (witFn dstar φ) (1 - α) - ρ)
      (quantileAt P (witFn dstar φ) (1 - α) + ρ), cf ≤ g s)
    (hd : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (quantileAt P (witFn dstar φ) (1 - α) - ρ)
      (quantileAt P (witFn dstar φ) (1 - α) + ρ) →
      P (witFn dstar φ ⁻¹' A) = ∫⁻ s in A, ENNReal.ofReal (g s)) :
    ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
      ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m E ∧
      (lamTC κ (zetaTC (etaTC κ α δ n m) ‖dstar‖) cf δ n ≤ ρ →
        ∀ z ∈ E, ∀ pr ∈ capped n α ×ˢ capped m α,
          IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m α) pr →
          |tHat φ (witness φ z.1 z.2 pr) α z.1 - quantileAt P (witFn dstar φ) (1 - α)| ≤
              lamTC κ (zetaTC (etaTC κ α δ n m) ‖dstar‖) cf δ n ∧
            symmDiff {x | witFn (witness φ z.1 z.2 pr) φ x < tHat φ (witness φ z.1 z.2 pr) α z.1}
                {x | witFn dstar φ x < quantileAt P (witFn dstar φ) (1 - α)} ⊆
              {x | |witFn dstar φ x - quantileAt P (witFn dstar φ) (1 - α)| ≤
                lamTC κ (zetaTC (etaTC κ α δ n m) ‖dstar‖) cf δ n} ∧
            ∀ x, witFn (witness φ z.1 z.2 pr) φ x = tHat φ (witness φ z.1 z.2 pr) α z.1 →
              |witFn dstar φ x - quantileAt P (witFn dstar φ) (1 - α)| ≤
                lamTC κ (zetaTC (etaTC κ α δ n m) ‖dstar‖) cf δ n) := by
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
  have hcfu : cf * u = sn + 1 / n := by rw [hu]; field_simp
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
  obtain ⟨E12, hm12, hp12, hsub12⟩ := StatFormal.Wave30az.witnessstab_gen 𝒳 H P Q φ κ α α (2 * δ / 3) n m
    hφ hκ hα0 hα1 hα0 hα1 hn hm (by positivity) (by linarith)
  rw [etaNM_eq] at hsub12
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
  · have hAB : 1 - δ / 3 ≤ (Measure.pi fun _ : Fin n => P).real (Ea ∩ Eb) := by
      have := prob_inter_ge (Measure.pi fun _ : Fin n => P) (S := Ea) hmEb
      linarith
    have hprod : μ.real ((Ea ∩ Eb) ×ˢ (Set.univ : Set (Fin m → 𝒳))) =
        (Measure.pi fun _ : Fin n => P).real (Ea ∩ Eb) := by
      simp [hμ, measureReal_def, Measure.prod_prod]
    have h12 : 1 - 2 * δ / 3 ≤ μ.real E12 := by
      rw [measureReal_def]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hp12
    have := prob_inter_ge μ (S := E12) ((hmEa.inter hmEb).prod MeasurableSet.univ)
    change ENNReal.ofReal (1 - δ) ≤ μ _
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _), ← measureReal_def]
    linarith
  · intro hΛρ
    have huρ : u ≤ ρ := by linarith
    have hmar := margins (P := P) hf hK hα1 hα0 g hgl hd hu0 huρ
    rintro z ⟨hz12, ⟨hza, hzb⟩, -⟩ pr hpr hprmin
    set dh := witness φ z.1 z.2 pr with hdh
    obtain ⟨-, hnorm, -, hsup⟩ := hsub12 hz12 pr dstar hpr hprmin hmin
    set Δ := κ * ‖dh - dstar‖ with hΔdef
    have hΔ : ∀ x, |witFn dh φ x - f x| ≤ Δ := fun x => hsup x
    have hΔζ : Δ ≤ κ * ζ := by
      refine mul_le_mul_of_nonneg_left (hnorm.trans ?_) hκ0
      rw [hζdef, zetaTC]
      gcongr
      exact min_le_left _ _
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

theorem trimrate_of (hb : Claims.basicineq) (hl : Claims.localmod) : Claims.trimrate := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ Dφ α δ θ ρ cf Cf cf' uα n m dstar hφ hκ hDφ hα0 hα1 hD hmin hρ hcf hcf'
    hQd hqu hQd' hn hm hδ0 hδ1 hθ hτ hlam
  obtain ⟨E, hEm, hEp, hE⟩ := rate_event hb hl P Q hφ hκ hDφ hα0 hα1 hD hmin hρ hcf hcf' hQd hqu hQd'
    hn hm hδ0 hδ1 hθ hτ hlam
  exact ⟨E, hEm, hEp, fun z hz pr hpr hprmin => (hE z hz pr hpr hprmin).1⟩

theorem trimrate_inter_of (hb : Claims.basicineq) (hl : Claims.localmod) : Claims.trimrate_inter := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ Dφ α δ θ ρ cf Cf cf' uα n m dstar hφ hκ hDφ hα0 hα1 hD hmin hρ hcf hcf'
    hQd hqu hQd' hn hm hδ0 hδ1 hθ hτ hlam
  have hDn : Dpop φ P Q α = ‖dstar‖ := RBasic.Dpop_eq_norm hmin
  obtain ⟨E₁, hE₁m, hE₁p, hE₁⟩ := rate_event hb hl P Q hφ hκ hDφ hα0 hα1 hD hmin hρ hcf hcf' hQd hqu hQd'
    hn hm hδ0 hδ1 hθ hτ hlam
  have hQd2 := hQd
  obtain ⟨g, -, hgb, hgd⟩ := hQd2
  have hCf : 0 ≤ Cf := by
    have := hgb (quantileAt P (witFn dstar φ) (1 - α)) ⟨by linarith, by linarith⟩
    linarith [this.1, this.2]
  obtain ⟨E₂, hE₂m, hE₂p, hE₂⟩ := consist_event P Q hφ hκ hα0.le hα1 hn hm hδ0 hδ1 hmin hρ hcf g
    (fun s hs => (hgb s hs).1) hgd
  refine ⟨E₁, E₂, hE₁m, hE₂m, hE₁p, hE₂p, ?_, fun z hz pr hpr hprmin => (hE₁ z hz pr hpr hprmin).1,
    ?_, ?_⟩
  · have := real_inter_ge (sampleLaw P Q n m) (S := E₁) hE₂m (real_of_ofReal_le hE₁p)
      (real_of_ofReal_le hE₂p)
    exact ofReal_le_of_real (by linarith)
  · intro _ hℓρ z hz pr hpr hprmin
    rw [hDn] at hℓρ
    obtain ⟨h1, h2, h3⟩ := hE₂ hℓρ z hz pr hpr hprmin
    unfold ConsistConcl
    intro tα dh th ℓ
    have hℓ : ℓ = lamTC κ (zetaTC (etaTC κ α δ n m) ‖dstar‖) cf δ n := by rw [← hDn]
    rw [hℓ]
    exact ⟨h1, kept_of_band P hφ hα1 ((abs_nonneg _).trans h1) hCf g (fun s hs => (hgb s hs).2) hgd h2 h3⟩
  · intro _ hℓρ z hz pr hpr hprmin
    rw [hDn] at hℓρ ⊢
    obtain ⟨-, h2, h3⟩ := hE₂ hℓρ z hz.2 pr hpr hprmin
    obtain ⟨hR, h3'⟩ := hE₁ z hz.1 pr hpr hprmin
    have h2' := hR.2.2.2.1
    rw [hDn] at h3' h2'
    have hℓ0 : 0 ≤ lamTC κ (zetaTC (etaTC κ α δ n m) ‖dstar‖) cf δ n :=
      (abs_nonneg _).trans (hE₂ hℓρ z hz.2 pr hpr hprmin).1
    have hℓ0' : 0 ≤ ellLoc κ (zetaLoc κ α ‖dstar‖ θ (Jpeel θ n m) (Lloc (chiPeel θ δ n m) n m)
        (Mloc (lamQ cf δ n) (lamQ cf' δ m) (chiPeel θ δ n m) n m)) (lamQ cf δ n) := by
      obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
      have hθ0 : 0 < θ := by linarith
      have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
      have := Lloc_nonneg (chiPeel θ δ n m) n m
      have := Mloc_nonneg (lamQ_pos hcf δ hn).le (lamQ_pos hcf' δ hm).le (chiPeel θ δ n m) n m
      have := lamQ_pos hcf δ hn
      have h1α : 0 < 1 - α := by linarith
      unfold ellLoc zetaLoc
      positivity
    refine kept_of_band P hφ hα1 (le_min hℓ0 hℓ0') hCf g (fun s hs => (hgb s hs).2) hgd ?_ ?_
    · intro x hx
      have a := h2 hx
      have b := h2' hx
      simp only [Set.mem_setOf_eq] at a b ⊢
      exact le_min a b
    · intro x hx
      exact le_min (h3 x hx) (h3' x hx)

theorem trimrate_A3 : Claims.trimrate_A3 := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α hφ hκ hchar hα0 hα
  have hα1 : α < 1 := hα.trans_le StatFormal.Distances.tvDist_le_one
  have hne : Dpop φ P Q α ≠ 0 := fun h0 =>
    (not_le.2 hα) ((StatFormal.TrimmedMMD.ZeroSet.zeroeq 𝒳 H P Q φ κ α hφ hκ hchar hα0 hα1).1 h0)
  exact lt_of_le_of_ne (StatFormal.Wave30tr.setDist_nonneg _ _) (Ne.symm hne)

end Main

end StatFormal.Wave30tx.RRate
