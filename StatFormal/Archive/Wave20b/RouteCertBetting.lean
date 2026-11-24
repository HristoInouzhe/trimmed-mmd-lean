import StatFormal.Archive.Wave20b.Statements
import Mathlib.Probability.Independence.Integration

/-!
# Route — JASA `lem:cert-betting` (untrusted)

Finite-horizon Ville inequality by a stopped product, without martingale machinery.
* At `t₀ = E Z` the factors `1 + β_j W_j`, `W_j = Z_j − E Z`, have predictable `β_j ∈ [0, 0.9]` and centred `W_j`
  independent of the past (`iIndepFun.indepFun_finset`), so every product `Π_{j<t}(1 + b_j W_j)` with predictable
  bounded `b_j` has expectation `1` (induction on `t`).
* Freezing the bets after the first time `M_t ≥ 1/δ'` (`b_j = 1{max_{i<j} M_i < 1/δ'} β_j`, still predictable) gives a
  nonnegative product `S` with `S = M_τ ≥ 1/δ'` on the bad event; Markov gives `P(bad) ≤ δ' E S = δ'`.
* On the good event `E Z` is in the confidence set, so every lower bound `b` of it is `≤ E Z`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave20b

section Betting
variable {Y : Type} [MeasurableSpace Y] {m : ℕ}

/-- Extension of a partial vector by a default point. -/
def extendVec (S : Finset (Fin m)) (y0 : Y) (u : S → Y) : Fin m → Y :=
  fun i => if h : i ∈ S then u ⟨i, h⟩ else y0

lemma measurable_extendVec (S : Finset (Fin m)) (y0 : Y) : Measurable (extendVec S y0) := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : i ∈ S
  · simp only [extendVec, h, dif_pos]; exact measurable_pi_apply _
  · simp only [extendVec, h, dif_neg, not_false_eq_true]; exact measurable_const

/-- A function of the coordinates `< t` is independent of the coordinate `t`. -/
lemma indep_past {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω} {Yb : Fin m → Ω → Y}
    (hY : ∀ j, Measurable (Yb j)) (hind : iIndepFun Yb Pr) (y0 : Y) (t : Fin m)
    {Φ : (Fin m → Y) → ℝ} (hΦ : Measurable Φ) (hdep : ∀ y y', (∀ i, i < t → y i = y' i) → Φ y = Φ y')
    {Ψ : Y → ℝ} (hΨ : Measurable Ψ) :
    IndepFun (fun ω => Φ (fun i => Yb i ω)) (fun ω => Ψ (Yb t ω)) Pr := by
  set S := Finset.univ.filter (fun i : Fin m => i < t) with hS
  have hST : Disjoint S {t} := by
    rw [Finset.disjoint_singleton_right]; simp [hS]
  have h := hind.indepFun_finset S {t} hST hY
  have hφ : Measurable (fun u : S → Y => Φ (extendVec S y0 u)) := hΦ.comp (measurable_extendVec S y0)
  have hψ : Measurable (fun u : ({t} : Finset (Fin m)) → Y => Ψ (u ⟨t, Finset.mem_singleton_self t⟩)) :=
    hΨ.comp (measurable_pi_apply _)
  have h2 := h.comp hφ hψ
  have hfun : (fun ω => Φ (fun i => Yb i ω)) =
      (fun u : S → Y => Φ (extendVec S y0 u)) ∘ (fun a (i : S) => Yb i a) := by
    funext ω
    simp only [Function.comp]
    apply hdep
    intro i hi
    have hiS : i ∈ S := by simp [hS, hi]
    simp [extendVec, hiS]
  rw [hfun]
  exact h2

variable (g : Y → ℝ) (ub lb μ c : ℝ) (bet : Fin m → (Fin m → Y) → ℝ)

/-- `Z(y) = (ū − g(y))/(ū − ℓ)`. -/
def zf (y : Y) : ℝ := (ub - g y) / (ub - lb)

/-- `W_j = Z(y_j) − μ`. -/
def wf (j : Fin m) (y : Fin m → Y) : ℝ := zf g ub lb (y j) - μ

/-- `M_i = Π_{l ≤ i} (1 + β_l W_l)`. -/
def mf (i : Fin m) (y : Fin m → Y) : ℝ := ∏ l ∈ Finset.Iic i, (1 + bet l y * wf g ub lb μ l y)

/-- `I_j = 1{max_{i<j} M_i < c}`. -/
def indf (j : Fin m) (y : Fin m → Y) : ℝ := if ∀ i, i < j → mf g ub lb μ bet i y < c then 1 else 0

/-- `P_t = Π_{j<t} (1 + I_j β_j W_j)`. -/
def pf (t : ℕ) (y : Fin m → Y) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin m => j.val < t),
    (1 + indf g ub lb μ c bet j y * bet j y * wf g ub lb μ j y)

variable {g ub lb μ c bet}

lemma dep_mf (hpred : StatFormal.Wave20b.Predictable bet) (i : Fin m) (y y' : Fin m → Y)
    (h : ∀ l, l ≤ i → y l = y' l) : mf g ub lb μ bet i y = mf g ub lb μ bet i y' := by
  unfold mf wf
  refine Finset.prod_congr rfl fun l hl => ?_
  have hli : l ≤ i := Finset.mem_Iic.mp hl
  rw [hpred l y y' (fun i' hi' => h i' (le_trans hi'.le hli)), h l hli]

lemma dep_indf (hpred : StatFormal.Wave20b.Predictable bet) (j : Fin m) (y y' : Fin m → Y)
    (h : ∀ l, l < j → y l = y' l) : indf g ub lb μ c bet j y = indf g ub lb μ c bet j y' := by
  have hiff : (∀ i, i < j → mf g ub lb μ bet i y < c) ↔ (∀ i, i < j → mf g ub lb μ bet i y' < c) := by
    have hm : ∀ i, i < j → mf g ub lb μ bet i y = mf g ub lb μ bet i y' := fun i hi =>
      dep_mf hpred i y y' (fun l hl => h l (lt_of_le_of_lt hl hi))
    exact ⟨fun H i hi => hm i hi ▸ H i hi, fun H i hi => (hm i hi).symm ▸ H i hi⟩
  unfold indf
  by_cases hp : ∀ i, i < j → mf g ub lb μ bet i y < c
  · rw [if_pos hp, if_pos (hiff.mp hp)]
  · rw [if_neg hp, if_neg (fun h' => hp (hiff.mpr h'))]

lemma dep_pf (hpred : StatFormal.Wave20b.Predictable bet) (t : ℕ) (y y' : Fin m → Y)
    (h : ∀ l : Fin m, l.val < t → y l = y' l) : pf g ub lb μ c bet t y = pf g ub lb μ c bet t y' := by
  unfold pf
  refine Finset.prod_congr rfl fun j hj => ?_
  have hjt : j.val < t := (Finset.mem_filter.mp hj).2
  have hpast : ∀ l, l < j → y l = y' l := fun l hl => h l (lt_trans (Fin.lt_def.mp hl) hjt)
  rw [dep_indf hpred j y y' hpast, hpred j y y' hpast]
  unfold wf
  rw [h j hjt]

lemma measurable_mf (hg : Measurable g) (hbet : ∀ j, Measurable (bet j)) (i : Fin m) :
    Measurable (mf g ub lb μ bet i) := by
  unfold mf wf zf
  refine Finset.measurable_prod _ fun l _ => ?_
  have := hbet l
  have : Measurable fun y : Fin m → Y => g (y l) := hg.comp (measurable_pi_apply l)
  fun_prop

lemma measurable_indf (hg : Measurable g) (hbet : ∀ j, Measurable (bet j)) (j : Fin m) :
    Measurable (indf g ub lb μ c bet j) := by
  unfold indf
  refine Measurable.ite ?_ measurable_const measurable_const
  have : {a : Fin m → Y | ∀ i, i < j → mf g ub lb μ bet i a < c} =
      ⋂ i : Fin m, {a | i < j → mf g ub lb μ bet i a < c} := by ext a; simp
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  by_cases hij : i < j
  · simp only [hij, true_implies]
    exact measurableSet_lt (measurable_mf hg hbet i) measurable_const
  · simp only [hij, false_implies, setOf_true, MeasurableSet.univ]

lemma measurable_pf (hg : Measurable g) (hbet : ∀ j, Measurable (bet j)) (t : ℕ) :
    Measurable (pf g ub lb μ c bet t) := by
  unfold pf wf zf
  refine Finset.measurable_prod _ fun j _ => ?_
  have := hbet j
  have := measurable_indf (ub := ub) (lb := lb) (μ := μ) (c := c) hg hbet j
  have : Measurable fun y : Fin m → Y => g (y j) := hg.comp (measurable_pi_apply j)
  fun_prop

lemma zf_mem (hgb : ∀ y, lb ≤ g y ∧ g y ≤ ub) (hlu : lb < ub) (y : Y) :
    0 ≤ zf g ub lb y ∧ zf g ub lb y ≤ 1 := by
  unfold zf
  have hd : 0 < ub - lb := by linarith
  exact ⟨div_nonneg (by linarith [(hgb y).2]) hd.le, by rw [div_le_one hd]; linarith [(hgb y).1]⟩

/-- Bounds: `Z ∈ [0,1]` and `μ ∈ [0,1]` give `|W| ≤ 1`, hence every factor is in `[0.1, 1.9]`. -/
lemma abs_wf_le (hgb : ∀ y, lb ≤ g y ∧ g y ≤ ub) (hlu : lb < ub) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (j : Fin m) (y : Fin m → Y) : |wf g ub lb μ j y| ≤ 1 := by
  unfold wf zf
  have hd : 0 < ub - lb := by linarith
  have h0 : 0 ≤ (ub - g (y j)) / (ub - lb) := div_nonneg (by linarith [(hgb (y j)).2]) hd.le
  have h1 : (ub - g (y j)) / (ub - lb) ≤ 1 := by rw [div_le_one hd]; linarith [(hgb (y j)).1]
  rw [abs_le]; constructor <;> linarith

lemma indf_mem (j : Fin m) (y : Fin m → Y) : indf g ub lb μ c bet j y = 0 ∨ indf g ub lb μ c bet j y = 1 := by
  unfold indf; split_ifs <;> simp

lemma factor_bounds (hgb : ∀ y, lb ≤ g y ∧ g y ≤ ub) (hlu : lb < ub) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hb : ∀ j y, 0 ≤ bet j y ∧ bet j y ≤ 0.9) (j : Fin m) (y : Fin m → Y) :
    0 ≤ 1 + indf g ub lb μ c bet j y * bet j y * wf g ub lb μ j y ∧
      |1 + indf g ub lb μ c bet j y * bet j y * wf g ub lb μ j y| ≤ 2 := by
  have hw := abs_le.mp (abs_wf_le hgb hlu hμ0 hμ1 j y)
  have hb' := hb j y
  rcases indf_mem (c := c) (bet := bet) (g := g) (ub := ub) (lb := lb) (μ := μ) j y with h0 | h1
  · rw [h0]; simp
  · rw [h1, one_mul]
    have hlo : -0.9 ≤ bet j y * wf g ub lb μ j y := by nlinarith
    have hhi : bet j y * wf g ub lb μ j y ≤ 0.9 := by nlinarith
    refine ⟨by linarith, ?_⟩
    rw [abs_le]; constructor <;> linarith

lemma abs_pf_le (hgb : ∀ y, lb ≤ g y ∧ g y ≤ ub) (hlu : lb < ub) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hb : ∀ j y, 0 ≤ bet j y ∧ bet j y ≤ 0.9) (t : ℕ) (y : Fin m → Y) :
    |pf g ub lb μ c bet t y| ≤ 2 ^ m := by
  unfold pf
  rw [Finset.abs_prod]
  calc ∏ j ∈ Finset.univ.filter (fun j : Fin m => j.val < t),
        |1 + indf g ub lb μ c bet j y * bet j y * wf g ub lb μ j y|
      ≤ ∏ _j ∈ Finset.univ.filter (fun j : Fin m => j.val < t), (2 : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => (factor_bounds hgb hlu hμ0 hμ1 hb j y).2
    _ = 2 ^ (Finset.univ.filter (fun j : Fin m => j.val < t)).card := Finset.prod_const _
    _ ≤ 2 ^ m := by
        refine pow_le_pow_right₀ (by norm_num) ?_
        exact (Finset.card_filter_le _ _).trans (by simp)

end Betting

theorem cert_betting : Claims.cert_betting := by
  intro Ω Y _ _ Pr _ P _ m Yb g ub lb δ bet hY hind hlaw hg hgb hlu hδ hbet hpred hb
  have hd : 0 < ub - lb := by linarith
  have hYne : Nonempty Y := nonempty_of_isProbabilityMeasure P
  obtain ⟨y0⟩ := id hYne
  have hgi : Integrable g P := Integrable.of_bound hg.aestronglyMeasurable (|lb| + |ub|)
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [(hgb y).1, (hgb y).2, abs_nonneg lb, abs_nonneg ub, neg_abs_le lb, le_abs_self ub])
  set μ := (ub - ∫ y, g y ∂P) / (ub - lb) with hμdef
  have hEg0 : lb ≤ ∫ y, g y ∂P := by
    have := integral_mono (integrable_const lb) hgi fun y => (hgb y).1
    simpa using this
  have hEg1 : ∫ y, g y ∂P ≤ ub := by
    have := integral_mono hgi (integrable_const ub) fun y => (hgb y).2
    simpa using this
  have hμ0 : 0 ≤ μ := div_nonneg (by linarith) hd.le
  have hμ1 : μ ≤ 1 := by rw [hμdef, div_le_one hd]; linarith
  set c := 1 / δ with hc
  have hcpos : 0 < c := by positivity
  -- the vector of observations
  set V : Ω → Fin m → Y := fun ω i => Yb i ω with hV
  have hVm : Measurable V := Measurable.of_eval hY
  -- mean of `W_t` is zero
  have hzm : Measurable (zf g ub lb) := by unfold zf; fun_prop
  have hW0 : ∀ t : Fin m, ∫ ω, (zf g ub lb (Yb t ω) - μ) ∂Pr = 0 := by
    intro t
    have hzi : Integrable (zf g ub lb) P := Integrable.of_bound hzm.aestronglyMeasurable 1
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_le]
        have := zf_mem hgb hlu y
        constructor <;> linarith [this.1, this.2])
    have h1 : ∫ ω, zf g ub lb (Yb t ω) ∂Pr = ∫ y, zf g ub lb y ∂P := by
      rw [← hlaw t, integral_map (hY t).aemeasurable hzm.aestronglyMeasurable]
    have h2 : ∫ y, zf g ub lb y ∂P = μ := by
      unfold zf
      rw [integral_div, integral_sub (integrable_const _) hgi, integral_const, probReal_univ, one_smul]
    have hzi' : Integrable (fun ω => zf g ub lb (Yb t ω)) Pr := by
      have h' : Integrable (zf g ub lb) (Pr.map (Yb t)) := by rw [hlaw t]; exact hzi
      exact h'.comp_measurable (hY t)
    rw [integral_sub hzi' (integrable_const _), h1, h2, integral_const, probReal_univ, one_smul, sub_self]
  -- expectation of every prefix product is one
  have hPint : ∀ t, Integrable (fun ω => pf g ub lb μ c bet t (V ω)) Pr := fun t =>
    Integrable.of_bound ((measurable_pf hg hbet t).comp hVm).aestronglyMeasurable (2 ^ m)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact abs_pf_le hgb hlu hμ0 hμ1 hb t (V ω))
  have hP1 : ∀ t, t ≤ m → ∫ ω, pf g ub lb μ c bet t (V ω) ∂Pr = 1 := by
    intro t
    induction t with
    | zero =>
      intro _
      simp [pf]
    | succ t ih =>
      intro ht
      have htm : t < m := ht
      set T : Fin m := ⟨t, htm⟩
      have hfilt : Finset.univ.filter (fun j : Fin m => j.val < t + 1) =
          insert T (Finset.univ.filter (fun j : Fin m => j.val < t)) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, T, Fin.ext_iff]; omega
      have hnot : T ∉ Finset.univ.filter (fun j : Fin m => j.val < t) := by simp [T]
      have hsplit : ∀ y, pf g ub lb μ c bet (t + 1) y = pf g ub lb μ c bet t y +
          (pf g ub lb μ c bet t y * (indf g ub lb μ c bet T y * bet T y)) * (zf g ub lb (y T) - μ) := by
        intro y
        unfold pf
        rw [hfilt, Finset.prod_insert hnot]
        unfold wf
        ring
      -- independence of the past part and the new increment
      set Φ : (Fin m → Y) → ℝ := fun y => pf g ub lb μ c bet t y * (indf g ub lb μ c bet T y * bet T y)
      have hΦm : Measurable Φ := by
        have := measurable_pf (ub := ub) (lb := lb) (μ := μ) (c := c) hg hbet t
        have := measurable_indf (ub := ub) (lb := lb) (μ := μ) (c := c) hg hbet T
        have := hbet T
        fun_prop
      have hdep : ∀ y y', (∀ i, i < T → y i = y' i) → Φ y = Φ y' := by
        intro y y' h
        simp only [Φ]
        rw [dep_pf hpred t y y' (fun l hl => h l (Fin.lt_def.mpr hl)), dep_indf hpred T y y' h,
          hpred T y y' h]
      have hind' := indep_past hY hind y0 T hΦm hdep (Ψ := fun y => zf g ub lb y - μ) (by fun_prop)
      have hΦb : ∀ y, |Φ y| ≤ 2 ^ m := by
        intro y
        simp only [Φ]
        rw [abs_mul]
        have h1 := abs_pf_le (c := c) hgb hlu hμ0 hμ1 hb t y
        have h2 : |indf g ub lb μ c bet T y * bet T y| ≤ 1 := by
          rw [abs_mul]
          rcases indf_mem (c := c) (bet := bet) (g := g) (ub := ub) (lb := lb) (μ := μ) T y with h0 | h1'
          · rw [h0]; simp
          · rw [h1', abs_one, one_mul, abs_of_nonneg (hb T y).1]; linarith [(hb T y).2]
        calc |pf g ub lb μ c bet t y| * |indf g ub lb μ c bet T y * bet T y| ≤ 2 ^ m * 1 :=
              mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
          _ = 2 ^ m := mul_one _
      have hΦi : Integrable (fun ω => Φ (V ω)) Pr :=
        Integrable.of_bound (hΦm.comp hVm).aestronglyMeasurable (2 ^ m)
          (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hΦb _)
      have hWi : Integrable (fun ω => zf g ub lb (Yb T ω) - μ) Pr :=
        Integrable.of_bound ((hzm.comp (hY T)).sub_const μ).aestronglyMeasurable 1
          (Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs]
            exact abs_wf_le (m := m) hgb hlu hμ0 hμ1 T (V ω))
      have hprod : ∫ ω, Φ (V ω) * (zf g ub lb (Yb T ω) - μ) ∂Pr = 0 := by
        rw [hind'.integral_fun_mul_eq_mul_integral (hΦm.comp hVm).aestronglyMeasurable
          ((hzm.comp (hY T)).sub_const μ).aestronglyMeasurable]
        have := hW0 T
        change (∫ ω, Φ (V ω) ∂Pr) * (∫ ω, (zf g ub lb (Yb T ω) - μ) ∂Pr) = 0
        rw [this, mul_zero]
      have hmulint : Integrable (fun ω => Φ (V ω) * (zf g ub lb (Yb T ω) - μ)) Pr := by
        refine Integrable.of_bound ((hΦm.comp hVm).mul ((hzm.comp (hY T)).sub_const μ)).aestronglyMeasurable
          (2 ^ m * 1) (Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hΦb _) (abs_wf_le (m := m) hgb hlu hμ0 hμ1 T (V ω)) (abs_nonneg _) (by positivity)
      calc ∫ ω, pf g ub lb μ c bet (t + 1) (V ω) ∂Pr
          = ∫ ω, (pf g ub lb μ c bet t (V ω) + Φ (V ω) * (zf g ub lb (Yb T ω) - μ)) ∂Pr := by
            refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
            simp only [hsplit, Φ, V]
        _ = 1 := by
            rw [integral_add (hPint t) hmulint, ih (by omega), hprod, add_zero]
  -- the frozen product
  set Sf : (Fin m → Y) → ℝ := pf g ub lb μ c bet m with hSf
  have hS1 : ∫ ω, Sf (V ω) ∂Pr = 1 := hP1 m le_rfl
  have hS0 : ∀ y, 0 ≤ Sf y := fun y =>
    Finset.prod_nonneg fun j _ => (factor_bounds (c := c) hgb hlu hμ0 hμ1 hb j y).1
  -- on the bad event the frozen product is at least `c`
  have hbad : ∀ y, (∃ t, c ≤ mf g ub lb μ bet t y) → c ≤ Sf y := by
    rintro y ⟨t0, ht0⟩
    set F := Finset.univ.filter (fun t : Fin m => c ≤ mf g ub lb μ bet t y)
    have hFne : F.Nonempty := ⟨t0, by simp [F, ht0]⟩
    set τ := F.min' hFne
    have hτ : c ≤ mf g ub lb μ bet τ y := (Finset.mem_filter.mp (F.min'_mem hFne)).2
    have hmin : ∀ i, i < τ → mf g ub lb μ bet i y < c := by
      intro i hi
      by_contra hcon
      push Not at hcon
      have : τ ≤ i := F.min'_le i (by simp [F, hcon])
      exact absurd hi (not_lt.mpr this)
    have hI : ∀ j, indf g ub lb μ c bet j y = if j ∈ Finset.Iic τ then 1 else 0 := by
      intro j
      unfold indf
      by_cases hj : j ≤ τ
      · rw [if_pos (Finset.mem_Iic.mpr hj), if_pos fun i hi => hmin i (lt_of_lt_of_le hi hj)]
      · rw [if_neg (fun h => hj (Finset.mem_Iic.mp h))]
        push Not at hj
        rw [if_neg]; push Not; exact ⟨τ, hj, hτ⟩
    have hfilt : Finset.univ.filter (fun j : Fin m => j.val < m) = Finset.univ := by
      ext j; simp [j.isLt]
    have : Sf y = mf g ub lb μ bet τ y := by
      simp only [hSf, pf, hfilt]
      rw [Finset.prod_congr rfl fun j _ => by rw [hI j]]
      have : ∀ j : Fin m, (1 + (if j ∈ Finset.Iic τ then (1 : ℝ) else 0) * bet j y * wf g ub lb μ j y) =
          if j ∈ Finset.Iic τ then 1 + bet j y * wf g ub lb μ j y else 1 := by
        intro j; split_ifs <;> ring
      rw [Finset.prod_congr rfl fun j _ => this j, Finset.prod_ite_mem, Finset.univ_inter]
      rfl
    rw [this]; exact hτ
  -- the good event
  set E := {ω | ∀ t, mf g ub lb μ bet t (V ω) < c} with hE
  have hEm : MeasurableSet E := by
    have : E = ⋂ t, {ω | mf g ub lb μ bet t (V ω) < c} := by ext ω; simp [hE]
    rw [this]
    exact MeasurableSet.iInter fun t => measurableSet_lt ((measurable_mf hg hbet t).comp hVm) measurable_const
  have hEc : Eᶜ ⊆ {ω | c ≤ Sf (V ω)} := by
    intro ω hω
    simp only [hE, mem_compl_iff, mem_setOf_eq, not_forall, not_lt] at hω
    exact hbad (V ω) hω
  have hmarkov : c * Pr.real {ω | c ≤ Sf (V ω)} ≤ 1 := by
    rw [← hS1]
    exact mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => hS0 _)
      (by simpa [hSf] using hPint m) c
  have hbadP : Pr Eᶜ ≤ ENNReal.ofReal δ := by
    refine (measure_mono hEc).trans ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hc] at hmarkov
    have := (le_div_iff₀' (by positivity : 0 < 1 / δ)).mpr hmarkov
    rwa [one_div_one_div] at this
  refine ⟨E, hEm, ?_, fun ω hω => ⟨?_, ?_⟩⟩
  · have h1 : Pr E = 1 - Pr Eᶜ := by simpa using prob_compl_eq_one_sub (μ := Pr) hEm.compl
    rw [h1]
    calc ENNReal.ofReal (1 - δ) = 1 - ENNReal.ofReal δ := by
          rw [ENNReal.ofReal_sub _ hδ.le, ENNReal.ofReal_one]
      _ ≤ 1 - Pr Eᶜ := tsub_le_tsub_left hbadP _
  · intro t
    exact hω t
  · intro b hbnd
    have hmem : μ ∈ confSet (fun j => bet j fun i => Yb i ω) (fun j => (ub - g (Yb j ω)) / (ub - lb)) δ :=
      fun t => hω t
    have hbμ := hbnd hmem
    have : (ub - lb) * μ = ub - ∫ y, g y ∂P := by rw [hμdef]; field_simp
    nlinarith

end StatFormal.Wave20b
