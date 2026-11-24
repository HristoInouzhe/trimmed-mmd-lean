import StatFormal.Lib.Exchangeable.Group
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Monte-Carlo randomisation tests (component F.E, part 5)

Setting of `Group.lean` (finite group `G`, measurable action `act`, `G`-invariant law `μ`,
measurable statistic `T`), plus `B` group elements `g_1, …, g_B` drawn i.i.d. uniformly from `G`
(`unifG`), independently of the data: the joint law is `μ ⊗ unif(G)^B`. The Monte-Carlo p-value is
`p(x, g) = (1 + #{b | T(g_b·x) ≥ T(x)}) / (B + 1)`.

Main results:
* `mc_test_valid`: `P(p ≤ α) ≤ α` for every real `α` (the paper's `α ∈ [0,1]` included);
* `mc_sum_le`: the averaged form `(B+1) Σ_g μ(1 + #{b | T(g_b·x) ≥ T(x)} ≤ K) ≤ |G|^B K`;
* `mc_comb`: the finite symmetry count `m · #{k ∈ Y^m | #{j | w(k_{i0}) ≤ w(k_j)} ≤ K} ≤ |Y|^m K`.
Route: invariance of `μ` under `h` and of `unif(G)^B` under right multiplication by `h` turn
`(x, g_1, …, g_B)` into `(h x, g_1 h⁻¹ …)`, so `(h, g_1, …, g_B)` plays the role of `B+1`
i.i.d. uniform elements whose values `T(k_j x)` are exchangeable; then `card_cntLe_le`.
-/

noncomputable section
open MeasureTheory Finset
open scoped ENNReal

namespace StatFormal.Foundations.Exchangeable

/-- The finite symmetry count. -/
theorem mc_comb {Y : Type*} [Fintype Y] {m : ℕ} (w : Y → ℝ) (i0 : Fin m) (K : ℕ) :
    m * #(univ.filter fun k : Fin m → Y => #(univ.filter fun j => w (k i0) ≤ w (k j)) ≤ K) ≤
      Fintype.card Y ^ m * K := by
  classical
  set P : Fin m → (Fin m → Y) → Prop := fun i k => #(univ.filter fun j => w (k i) ≤ w (k j)) ≤ K
  have hterm : ∀ i, #(univ.filter (P i)) = #(univ.filter (P i0)) := by
    intro i
    let e : (Fin m → Y) ≃ (Fin m → Y) :=
      { toFun := fun k => k ∘ Equiv.swap i0 i
        invFun := fun k => k ∘ Equiv.swap i0 i
        left_inv := fun k => by ext j; simp
        right_inv := fun k => by ext j; simp }
    have hP : ∀ k, P i0 (e k) ↔ P i k := fun k => by
      simp only [P, e, Equiv.coe_fn_mk, Function.comp_apply, Equiv.swap_apply_left]
      rw [card_filter_comp_perm (p := fun j => w (k i) ≤ w (k j)) (Equiv.swap i0 i)]
    rw [Finset.card_filter, Finset.card_filter,
      ← Equiv.sum_comp e (fun k => if P i0 k then 1 else 0)]
    exact Finset.sum_congr rfl fun k _ => if_congr (hP k).symm rfl rfl
  have hsum : ∑ i : Fin m, #(univ.filter (P i)) =
      ∑ k : Fin m → Y, #(univ.filter fun i => P i k) := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hk : ∀ k : Fin m → Y, #(univ.filter fun i => P i k) ≤ K := by
    intro k
    have hc := card_cntLe_le (fun j => -w (k j)) K
    simp only [neg_le_neg_iff] at hc
    exact hc
  calc m * #(univ.filter (P i0)) = ∑ i : Fin m, #(univ.filter (P i)) := by
        rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
    _ = ∑ k : Fin m → Y, #(univ.filter fun i => P i k) := hsum
    _ ≤ ∑ _k : Fin m → Y, K := Finset.sum_le_sum fun k _ => hk k
    _ = Fintype.card Y ^ m * K := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]

section MC

variable {G Ω : Type*} [Group G] [Fintype G] [MeasurableSpace Ω]
  {act : G → Ω → Ω} {T : Ω → ℝ}

/-- `1 + #{b | T(g_b·x) ≥ T(x)}`. -/
def mcCount {B : ℕ} (act : G → Ω → Ω) (T : Ω → ℝ) (x : Ω) (g : Fin B → G) : ℕ :=
  1 + #(univ.filter fun b => T x ≤ T (act (g b) x))

omit [Fintype G] in
lemma measurable_mcCount (hact : IsAct act) (hT : Measurable T) {B : ℕ} (g : Fin B → G) :
    Measurable fun x => mcCount act T x g := by
  unfold mcCount
  simp_rw [Finset.card_filter]
  refine measurable_const.add (Finset.measurable_sum _ fun b _ => ?_)
  exact Measurable.ite (measurableSet_le hT (hT.comp (hact.meas _)))
    measurable_const measurable_const

omit [Group G] [Fintype G] in
lemma count_cons {B : ℕ} (w : G → ℝ) (h : G) (g : Fin B → G) :
    #(univ.filter fun j : Fin (B + 1) => w ((Fin.cons h g : Fin (B + 1) → G) 0) ≤
        w ((Fin.cons h g : Fin (B + 1) → G) j)) =
      1 + #(univ.filter fun b => w h ≤ w (g b)) := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp

/-- **Monte-Carlo test, averaged form**. -/
theorem mc_sum_le (μ : Measure Ω) [IsProbabilityMeasure μ] (hact : IsAct act)
    (hinv : ∀ g, μ.map (act g) = μ) (hT : Measurable T) (B K : ℕ) :
    ((B + 1 : ℕ) : ℝ≥0∞) * ∑ g : Fin B → G, μ {x | mcCount act T x g ≤ K} ≤
      Fintype.card G ^ B * K := by
  set E : (Fin B → G) → Set Ω := fun g => {x | mcCount act T x g ≤ K}
  set F : G → (Fin B → G) → Set Ω := fun h g =>
    {x | 1 + #(univ.filter fun b => T (act h x) ≤ T (act (g b) x)) ≤ K}
  have hFm : ∀ h g, MeasurableSet (F h g) := by
    intro h g
    have : Measurable fun x => 1 + #(univ.filter fun b => T (act h x) ≤ T (act (g b) x)) := by
      simp_rw [Finset.card_filter]
      refine measurable_const.add (Finset.measurable_sum _ fun b _ => ?_)
      exact Measurable.ite (measurableSet_le (hT.comp (hact.meas h)) (hT.comp (hact.meas _)))
        measurable_const measurable_const
    exact this (MeasurableSet.of_discrete (s := {c : ℕ | c ≤ K}))
  -- step 1: translate by `h`
  have step1 : ∀ h, ∑ g, μ (E g) = ∑ g, μ (F h g) := by
    intro h
    have e1 : ∀ g, μ (E g) = μ (F h (fun b => g b * h)) := by
      intro g
      have hEm : MeasurableSet (E g) :=
        measurable_mcCount hact hT g (MeasurableSet.of_discrete (s := {c : ℕ | c ≤ K}))
      have hset : act h ⁻¹' E g = F h (fun b => g b * h) := by
        ext x
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, E, F, mcCount, hact.mul]
      have hm := Measure.map_apply (μ := μ) (hact.meas h) hEm
      rw [hinv h] at hm
      rw [hm, hset]
    rw [Finset.sum_congr rfl fun g _ => e1 g]
    exact Equiv.sum_comp (Equiv.piCongrRight fun _ => Equiv.mulRight h)
      (fun g => μ (F h g))
  -- step 2: sum over `h` and `g` as an integral of a count
  have step2 : (Fintype.card G : ℝ≥0∞) * ∑ g, μ (E g) =
      ∫⁻ x, (#(univ.filter fun p : G × (Fin B → G) => x ∈ F p.1 p.2) : ℝ≥0∞) ∂μ := by
    rw [← sum_measure_eq_lintegral_card μ (fun p : G × (Fin B → G) => F p.1 p.2)
      fun p => hFm p.1 p.2, Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl fun h _ => (step1 h).symm, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  -- step 3: the pointwise count is the symmetric count over `Fin (B+1) → G`
  have step3 : ∀ x, (B + 1) * #(univ.filter fun p : G × (Fin B → G) => x ∈ F p.1 p.2) ≤
      Fintype.card G ^ (B + 1) * K := by
    intro x
    have hc := mc_comb (fun g : G => T (act g x)) (0 : Fin (B + 1)) K
    refine le_trans (le_of_eq ?_) hc
    congr 1
    rw [Finset.card_filter, Finset.card_filter, ← Equiv.sum_comp (Fin.consEquiv fun _ => G),
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun g _ => ?_
    simp only [F, Set.mem_ofPred_eq, Fin.consEquiv_apply]
    rw [count_cons (fun g : G => T (act g x)) h g]
  have hcard0 : (Fintype.card G : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have hcardt : (Fintype.card G : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmain : (Fintype.card G : ℝ≥0∞) * (((B + 1 : ℕ) : ℝ≥0∞) * ∑ g, μ (E g)) ≤
      (Fintype.card G : ℝ≥0∞) * (Fintype.card G ^ B * K) := by
    rw [mul_left_comm, step2, ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
    calc ∫⁻ x, ((B + 1 : ℕ) : ℝ≥0∞) *
          (#(univ.filter fun p : G × (Fin B → G) => x ∈ F p.1 p.2) : ℝ≥0∞) ∂μ
        ≤ ∫⁻ _x, ((Fintype.card G ^ (B + 1) * K : ℕ) : ℝ≥0∞) ∂μ :=
          lintegral_mono fun x => by
            rw [← Nat.cast_mul]
            exact Nat.cast_le.mpr (step3 x)
      _ = _ := by
          rw [lintegral_const, measure_univ, mul_one]
          push_cast
          ring
  exact (ENNReal.mul_le_mul_iff_right hcard0 hcardt).mp hmain

/-- The uniform law on a finite group. -/
def unifG (G : Type*) [Fintype G] [MeasurableSpace G] : Measure G :=
  (Fintype.card G : ℝ≥0∞)⁻¹ • Measure.count

variable [MeasurableSpace G] [MeasurableSingletonClass G]

omit [Group G] in
lemma unifG_singleton (g : G) : unifG G {g} = (Fintype.card G : ℝ≥0∞)⁻¹ := by
  simp [unifG]

omit [Group G] in
instance isProb_unifG : IsProbabilityMeasure (unifG G) := by
  constructor
  rw [← lintegral_one, lintegral_fintype]
  simp_rw [unifG_singleton, one_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_pos.ne')
    (ENNReal.natCast_ne_top _)

/-- **Validity of the Monte-Carlo randomisation test**: for data `X ~ μ` (`G`-invariant) and
`g_1, …, g_B` i.i.d. uniform on `G` independent of `X`,
`P((1 + #{b | T(g_b·X) ≥ T(X)})/(B+1) ≤ α) ≤ α`. -/
theorem mc_test_valid (μ : Measure Ω) [IsProbabilityMeasure μ] (hact : IsAct act)
    (hinv : ∀ g, μ.map (act g) = μ) (hT : Measurable T) (B : ℕ) (α : ℝ) :
    (μ.prod (Measure.pi fun _ : Fin B => unifG G))
        {p | (mcCount act T p.1 p.2 : ℝ) / (B + 1) ≤ α} ≤ ENNReal.ofReal α := by
  set ν := Measure.pi fun _ : Fin B => unifG G
  have hB : (0 : ℝ) < B + 1 := by positivity
  rcases lt_or_ge α 0 with hα | hα
  · have : {p : Ω × (Fin B → G) | (mcCount act T p.1 p.2 : ℝ) / (B + 1) ≤ α} = ∅ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hα (div_nonneg (Nat.cast_nonneg _) hB.le)
    rw [this, measure_empty]
    exact bot_le
  set K := ⌊α * (B + 1)⌋₊
  set S : Set (Ω × (Fin B → G)) := {p | mcCount act T p.1 p.2 ≤ K}
  have hsub : {p : Ω × (Fin B → G) | (mcCount act T p.1 p.2 : ℝ) / (B + 1) ≤ α} ⊆ S := by
    intro p hp
    simp only [S, Set.mem_ofPred_eq, div_le_iff₀ hB] at hp ⊢
    exact Nat.le_floor hp
  have hSm : MeasurableSet S := by
    have : S = ⋃ g : Fin B → G, {x | mcCount act T x g ≤ K} ×ˢ {g} := by
      ext p
      simp only [S, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨p.2, h, rfl⟩, fun ⟨g, h1, h2⟩ => h2 ▸ h1⟩
    rw [this]
    exact MeasurableSet.iUnion fun g =>
      (measurable_mcCount hact hT g (MeasurableSet.of_discrete (s := {c : ℕ | c ≤ K}))).prod
        (measurableSet_singleton g)
  have hsing : ∀ g : Fin B → G, ν {g} = ((Fintype.card G : ℝ≥0∞)⁻¹) ^ B := by
    intro g
    rw [← Set.univ_pi_singleton, Measure.pi_pi]
    simp_rw [unifG_singleton]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hS : (μ.prod ν) S = ∑ g : Fin B → G, μ {x | mcCount act T x g ≤ K} *
      ((Fintype.card G : ℝ≥0∞)⁻¹) ^ B := by
    rw [Measure.prod_apply_symm hSm, lintegral_fintype]
    exact Finset.sum_congr rfl fun g _ => by rw [hsing g]; rfl
  have hsum := mc_sum_le μ hact hinv hT B K
  have hc0 : (Fintype.card G : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have hct : (Fintype.card G : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hB0 : ((B + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero B
  have hBt : ((B + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hKb : (K : ℝ≥0∞) ≤ ((B + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    rw [mul_comm]
    exact Nat.floor_le (mul_nonneg hα hB.le)
  refine (measure_mono hsub).trans ?_
  rw [hS, ← Finset.sum_mul]
  have hpow0 : ((Fintype.card G : ℝ≥0∞)⁻¹) ^ B ≠ 0 :=
    pow_ne_zero _ (ENNReal.inv_ne_zero.mpr hct)
  have hpowt : ((Fintype.card G : ℝ≥0∞)⁻¹) ^ B ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hc0)
  have hinvpow : (Fintype.card G : ℝ≥0∞) ^ B * ((Fintype.card G : ℝ≥0∞)⁻¹) ^ B = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel hc0 hct, one_pow]
  refine (ENNReal.mul_le_mul_iff_right hB0 hBt).mp ?_
  calc ((B + 1 : ℕ) : ℝ≥0∞) * ((∑ g : Fin B → G, μ {x | mcCount act T x g ≤ K}) *
        ((Fintype.card G : ℝ≥0∞)⁻¹) ^ B)
      = (((B + 1 : ℕ) : ℝ≥0∞) * ∑ g : Fin B → G, μ {x | mcCount act T x g ≤ K}) *
        ((Fintype.card G : ℝ≥0∞)⁻¹) ^ B := by ring
    _ ≤ ((Fintype.card G : ℝ≥0∞) ^ B * K) * ((Fintype.card G : ℝ≥0∞)⁻¹) ^ B :=
        mul_le_mul_left hsum _
    _ = K := by rw [mul_comm ((Fintype.card G : ℝ≥0∞) ^ B), mul_assoc, hinvpow, mul_one]
    _ ≤ _ := hKb

end MC

end StatFormal.Foundations.Exchangeable
