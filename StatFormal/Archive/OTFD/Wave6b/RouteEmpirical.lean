import StatFormal.Archive.OTFD.Wave6b.Statements
import TauCeti.MeasureTheory.OptimalTransport.Cost.Partition
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Moments.Variance

/-!
# Route: A `lem:app-empirical-wass`

* Cells: the cube `c + [−M, M]^K` is cut into `ℓ^K` cells by the coordinate index
  `min(ℓ−1, ⌊(x_k − c_k + M)ℓ/(2M)⌋)` (a partition of all of `ℝ^K`); two ball points in the same cell differ by
  `≤ 2M/ℓ` in each coordinate, so `dist² ≤ 4M²K/ℓ²`.
* Deterministic step: on couplings of two laws carried by the ball, the cost `‖x−y‖²` equals the cost truncated
  to `ball × ball`, which is `≤ 4M²` everywhere; Tau Ceti's `transportCost_le_sum_of_partition` gives
  `W₂² ≤ 4M²K/ℓ² + 4M² Σ_c (ν̂(c) − ν(c))₊`.
* Probabilistic step: `ν̂(c) = n⁻¹ Σ_j 1_c(X_j)`, `Var ≤ ν(c)/n` (pairwise independence), so
  `E|ν̂(c) − ν(c)| ≤ √(ν(c)/n)`, and Cauchy–Schwarz over the cells gives `√(ℓ^K/n)`.
* Rates: `ℓ = ⌊n^{1/(K+4)}⌋` satisfies `2ℓ ≥ n^{1/(K+4)}`, `ℓ ≤ n^{1/(K+4)}`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace

namespace StatFormal.OTFD.Wave6b

open TauCeti

variable {K : ℕ}

/-! ### Cells -/

/-- Coordinate cell index `min(ℓ−1, ⌊(x_k − c_k + M)ℓ/(2M)⌋)`. -/
def cellCoord (c : EuclideanSpace ℝ (Fin K)) (M : ℝ) (ℓ : ℕ) (x : EuclideanSpace ℝ (Fin K)) (k : Fin K) :
    ℕ :=
  min (ℓ - 1) ⌊(x k - c k + M) * ℓ / (2 * M)⌋₊

/-- The cell with multi-index `i`. -/
def cellSet (c : EuclideanSpace ℝ (Fin K)) (M : ℝ) (ℓ : ℕ) (i : Fin K → Fin ℓ) :
    Set (EuclideanSpace ℝ (Fin K)) :=
  {x | ∀ k, cellCoord c M ℓ x k = i k}

lemma measurable_cellCoord (c : EuclideanSpace ℝ (Fin K)) (M : ℝ) (ℓ : ℕ) (k : Fin K) :
    Measurable fun x => cellCoord c M ℓ x k := by
  have h1 : Measurable fun x : EuclideanSpace ℝ (Fin K) => (x k - c k + M) * ℓ / (2 * M) := by
    fun_prop
  exact (measurable_from_nat (f := fun m : ℕ => min (ℓ - 1) m)).comp h1.nat_floor

lemma measurableSet_cellSet (c : EuclideanSpace ℝ (Fin K)) (M : ℝ) (ℓ : ℕ) (i : Fin K → Fin ℓ) :
    MeasurableSet (cellSet c M ℓ i) := by
  have : cellSet c M ℓ i = ⋂ k, (fun x => cellCoord c M ℓ x k) ⁻¹' {((i k : Fin ℓ) : ℕ)} := by
    ext x; simp [cellSet]
  rw [this]
  exact MeasurableSet.iInter fun k => measurable_cellCoord c M ℓ k (measurableSet_singleton _)

lemma cellSet_disjoint (c : EuclideanSpace ℝ (Fin K)) (M : ℝ) (ℓ : ℕ) :
    Pairwise (Function.onFun Disjoint (cellSet c M ℓ)) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro x hi hj
  apply hij
  funext k
  exact Fin.ext ((hi k).symm.trans (hj k))

lemma cellSet_cover (c : EuclideanSpace ℝ (Fin K)) (M : ℝ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (⋃ i, cellSet c M ℓ i) = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.mpr ⟨fun k => ⟨cellCoord c M ℓ x k, ?_⟩, fun k => rfl⟩
  unfold cellCoord; omega

lemma floor_close {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {s t : ℝ} (hs0 : 0 ≤ s) (hsℓ : s ≤ ℓ) (ht0 : 0 ≤ t)
    (htℓ : t ≤ ℓ) (h : min (ℓ - 1) ⌊s⌋₊ = min (ℓ - 1) ⌊t⌋₊) : |s - t| ≤ 1 := by
  have hs1 := Nat.floor_le hs0
  have hs2 := Nat.lt_floor_add_one s
  have ht1 := Nat.floor_le ht0
  have ht2 := Nat.lt_floor_add_one t
  rcases lt_or_ge ⌊s⌋₊ (ℓ - 1) with ha | ha
  · have hb : ⌊t⌋₊ = ⌊s⌋₊ := by omega
    rw [hb] at ht1 ht2
    rw [abs_le]; constructor <;> linarith
  · have hb : ℓ - 1 ≤ ⌊t⌋₊ := by omega
    have hcast : ((ℓ - 1 : ℕ) : ℝ) = ℓ - 1 := by rw [Nat.cast_sub hℓ, Nat.cast_one]
    have ha' : (ℓ : ℝ) - 1 ≤ ⌊s⌋₊ := by rw [← hcast]; exact_mod_cast ha
    have hb' : (ℓ : ℝ) - 1 ≤ ⌊t⌋₊ := by rw [← hcast]; exact_mod_cast hb
    rw [abs_le]; constructor <;> linarith

lemma coord_sub_le {c x : EuclideanSpace ℝ (Fin K)} {M : ℝ} (hx : x ∈ Metric.closedBall c M)
    (k : Fin K) : |x k - c k| ≤ M := by
  have h := PiLp.norm_apply_le (x - c) k
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  have h' : (x - c) k = x k - c k := rfl
  rw [h', Real.norm_eq_abs] at h
  linarith

lemma cell_diam {c : EuclideanSpace ℝ (Fin K)} {M : ℝ} (hM : 0 ≤ M) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {i : Fin K → Fin ℓ} {x y : EuclideanSpace ℝ (Fin K)} (hx : x ∈ Metric.closedBall c M)
    (hy : y ∈ Metric.closedBall c M) (hxi : x ∈ cellSet c M ℓ i) (hyi : y ∈ cellSet c M ℓ i) :
    dist x y ^ 2 ≤ 4 * M ^ 2 * K / ℓ ^ 2 := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hcoord : ∀ k, |x k - y k| ≤ 2 * M / ℓ := by
    intro k
    have h1 := abs_le.mp (coord_sub_le hx k)
    have h2 := abs_le.mp (coord_sub_le hy k)
    rcases hM.eq_or_lt with hM0 | hMpos
    · have : x k - y k = 0 := by rw [← hM0] at h1 h2; linarith [h1.1, h1.2, h2.1, h2.2]
      rw [this, abs_zero, ← hM0]; simp
    · set s := (x k - c k + M) * ℓ / (2 * M) with hs
      set t := (y k - c k + M) * ℓ / (2 * M) with ht
      have hs0 : 0 ≤ s := div_nonneg (mul_nonneg (by linarith) hℓpos.le) (by linarith)
      have ht0 : 0 ≤ t := div_nonneg (mul_nonneg (by linarith) hℓpos.le) (by linarith)
      have hsℓ : s ≤ ℓ := by rw [hs, div_le_iff₀ (by linarith)]; nlinarith
      have htℓ : t ≤ ℓ := by rw [ht, div_le_iff₀ (by linarith)]; nlinarith
      have hst := floor_close hℓ hs0 hsℓ ht0 htℓ ((hxi k).trans (hyi k).symm)
      have heq : x k - y k = (s - t) * (2 * M / ℓ) := by
        rw [hs, ht]; field_simp; ring
      rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * M / ℓ)]
      calc |s - t| * (2 * M / ℓ) ≤ 1 * (2 * M / ℓ) :=
            mul_le_mul_of_nonneg_right hst (by positivity)
        _ = 2 * M / ℓ := one_mul _
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  calc ∑ k, dist (x k) (y k) ^ 2 ≤ ∑ _k : Fin K, (2 * M / ℓ) ^ 2 :=
        Finset.sum_le_sum fun k _ => by
          rw [Real.dist_eq]; exact pow_le_pow_left₀ (abs_nonneg _) (hcoord k) 2
    _ = 4 * M ^ 2 * K / ℓ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp; ring

/-! ### The deterministic bound -/

theorem w2sq_le_cells (c : EuclideanSpace ℝ (Fin K)) {M : ℝ} (hM : 0 ≤ M) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (μ ν : Measure (EuclideanSpace ℝ (Fin K))) [IsFiniteMeasure μ] (hmass : μ univ = ν univ)
    (hμ : μ (Metric.closedBall c M)ᶜ = 0) (hν : ν (Metric.closedBall c M)ᶜ = 0) :
    wassersteinEDist 2 μ ν ^ 2 ≤ ENNReal.ofReal (4 * M ^ 2 * K / ℓ ^ 2) * ν univ +
      ENNReal.ofReal (4 * M ^ 2) * ∑ i, (μ (cellSet c M ℓ i) - ν (cellSet c M ℓ i)) := by
  set Bc := Metric.closedBall c M with hBcdef
  have hBc : MeasurableSet Bc := measurableSet_closedBall
  have hrw : wassersteinEDist 2 μ ν ^ 2 =
      transportCost (fun z : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) =>
        edist z.1 z.2 ^ (2 : ℝ)) μ ν := by
    have := wassersteinEDist_rpow_eq_transportCost measurable_edist (p := 2) (by norm_num)
      (by norm_num) μ ν
    have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
    rw [h2] at this
    rw [← this, ENNReal.rpow_two]
  set c' : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ≥0∞ :=
    (Bc ×ˢ Bc).indicator fun z => edist z.1 z.2 ^ (2 : ℝ) with hc'
  have hcongr : transportCost (fun z : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) =>
      edist z.1 z.2 ^ (2 : ℝ)) μ ν = transportCost c' μ ν := by
    apply transportCost_congr
    intro π hπ
    have hae : ∀ᵐ z ∂π, z ∈ Bc ×ˢ Bc := by
      rw [ae_iff]
      apply measure_mono_null (t := Prod.fst ⁻¹' Bcᶜ ∪ Prod.snd ⁻¹' Bcᶜ)
      · intro z hz
        simp only [mem_prod, not_and_or] at hz
        rcases hz with h | h
        · exact Or.inl h
        · exact Or.inr h
      · apply measure_union_null
        · rw [← Measure.fst_apply hBc.compl, hπ.fst_eq]; exact hμ
        · rw [← Measure.snd_apply hBc.compl, hπ.snd_eq]; exact hν
    filter_upwards [hae] with z hz
    simp [hc', indicator_of_mem hz]
  have hcell : ∀ i, ∀ x ∈ cellSet c M ℓ i, ∀ y ∈ cellSet c M ℓ i,
      c' (x, y) ≤ ENNReal.ofReal (4 * M ^ 2 * K / ℓ ^ 2) := by
    intro i x hx y hy
    by_cases hz : (x, y) ∈ Bc ×ˢ Bc
    · rw [hc', indicator_of_mem hz]
      obtain ⟨hx', hy'⟩ := hz
      simp only
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.rpow_two]
      exact cell_diam hM hℓ hx' hy' hx hy
    · rw [hc', indicator_of_notMem hz]; exact bot_le
  have hbound : ∀ z, c' z ≤ ENNReal.ofReal (4 * M ^ 2) := by
    intro z
    by_cases hz : z ∈ Bc ×ˢ Bc
    · rw [hc', indicator_of_mem hz]
      obtain ⟨hx', hy'⟩ := hz
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.rpow_two]
      have h1 : dist z.1 z.2 ≤ 2 * M := by
        have := dist_triangle z.1 c z.2
        rw [Metric.mem_closedBall] at hx' hy'
        rw [dist_comm c] at this
        linarith
      nlinarith [dist_nonneg (x := z.1) (y := z.2)]
    · rw [hc', indicator_of_notMem hz]; exact bot_le
  have hsum : ∑ i, ν (cellSet c M ℓ i) = ν univ := by
    conv_rhs => rw [← cellSet_cover c M hℓ]
    rw [measure_iUnion (cellSet_disjoint c M ℓ) (measurableSet_cellSet c M ℓ), tsum_fintype]
  rw [hrw, hcongr]
  refine (transportCost_le_sum_of_partition (measurableSet_cellSet c M ℓ) (measurableSet_cellSet c M ℓ)
    (cellSet_disjoint c M ℓ) (cellSet_disjoint c M ℓ) (cellSet_cover c M hℓ) (cellSet_cover c M hℓ)
    hcell hbound μ ν hmass).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, hsum]

/-! ### Empirical measures -/

section Emp
variable {n : ℕ}

lemma empMeasure_apply (x : Fin n → EuclideanSpace ℝ (Fin K)) {A : Set (EuclideanSpace ℝ (Fin K))}
    (hA : MeasurableSet A) : empMeasure x A = (n : ℝ≥0∞)⁻¹ * ∑ j, A.indicator 1 (x j) := by
  simp [empMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply' _ hA]

lemma empMeasure_univ (hn : 1 ≤ n) (x : Fin n → EuclideanSpace ℝ (Fin K)) : empMeasure x univ = 1 := by
  rw [empMeasure_apply x MeasurableSet.univ]
  simp only [indicator_univ, Pi.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (by omega : n ≠ 0)) (ENNReal.natCast_ne_top n)

/-- The empirical frequency `n⁻¹ Σ_j 1_A(X_j)` as a real. -/
def empFreq {Ω : Type*} (X : Fin n → Ω → EuclideanSpace ℝ (Fin K)) (A : Set (EuclideanSpace ℝ (Fin K)))
    (ω : Ω) : ℝ :=
  (1 / n : ℝ) * ∑ j, A.indicator (fun _ => (1 : ℝ)) (X j ω)

lemma empMeasure_eq_ofReal {Ω : Type*} (hn : 1 ≤ n) (X : Fin n → Ω → EuclideanSpace ℝ (Fin K)) (ω : Ω)
    {A : Set (EuclideanSpace ℝ (Fin K))} (hA : MeasurableSet A) :
    empMeasure (fun j => X j ω) A = ENNReal.ofReal (empFreq X A ω) := by
  rw [empMeasure_apply _ hA, empFreq, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun j _ => indicator_nonneg (fun _ _ => zero_le_one) _)]
  congr 1
  · rw [one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast (by omega : 0 < n)), ENNReal.ofReal_natCast]
  · refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : X j ω ∈ A <;> simp [h]

lemma empFreq_mem {Ω : Type*} (hn : 1 ≤ n) (X : Fin n → Ω → EuclideanSpace ℝ (Fin K))
    (A : Set (EuclideanSpace ℝ (Fin K))) (ω : Ω) : empFreq X A ω ∈ Icc (0 : ℝ) 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ∀ j, A.indicator (fun _ => (1 : ℝ)) (X j ω) ≤ 1 := fun j => by
    by_cases h : X j ω ∈ A <;> simp [h]
  have h0 : ∀ j, 0 ≤ A.indicator (fun _ => (1 : ℝ)) (X j ω) := fun j =>
    indicator_nonneg (fun _ _ => zero_le_one) _
  refine ⟨mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => h0 j), ?_⟩
  have : ∑ j, A.indicator (fun _ => (1 : ℝ)) (X j ω) ≤ n := by
    calc ∑ j, A.indicator (fun _ => (1 : ℝ)) (X j ω) ≤ ∑ _j : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => h1 j
      _ = n := by simp
  unfold empFreq
  rw [one_div, inv_mul_le_iff₀ hnpos, mul_one]
  exact this

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Fin n → Ω → EuclideanSpace ℝ (Fin K)}

lemma measurable_empFreq (hXm : ∀ i, Measurable (X i)) {A : Set (EuclideanSpace ℝ (Fin K))}
    (hA : MeasurableSet A) : Measurable (empFreq X A) :=
  (Finset.measurable_sum _ fun j _ => (measurable_const.indicator hA).comp (hXm j)).const_mul _

/-- `E|ν̂(A) − ν(A)| ≤ √(ν(A)/n)`. -/
theorem integral_abs_empFreq_le (hn : 1 ≤ n) (ν : Measure (EuclideanSpace ℝ (Fin K)))
    [IsProbabilityMeasure ν] (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = ν) {A : Set (EuclideanSpace ℝ (Fin K))} (hA : MeasurableSet A) :
    ∫ ω, |empFreq X A ω - (ν A).toReal| ∂P ≤ Real.sqrt ((ν A).toReal / n) := by
  set p := (ν A).toReal with hp
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := by
    rw [hp]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set Y : Fin n → Ω → ℝ := fun j ω => A.indicator (fun _ => (1 : ℝ)) (X j ω) with hY
  have hYm : ∀ j, Measurable (Y j) := fun j => (measurable_const.indicator hA).comp (hXm j)
  have hY01 : ∀ j ω, Y j ω ∈ Icc (0 : ℝ) 1 := fun j ω => by
    by_cases h : X j ω ∈ A <;> simp [hY, h]
  have hYmem : ∀ j, MemLp (Y j) 2 P := fun j =>
    MemLp.of_bound (hYm j).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hY01 j ω).1, (hY01 j ω).2])
  have hEY : ∀ j, ∫ ω, Y j ω ∂P = p := by
    intro j
    have : ∫ ω, Y j ω ∂P = ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂(P.map (X j)) := by
      rw [integral_map (hXm j).aemeasurable
        (measurable_const.indicator hA).aestronglyMeasurable]
    rw [this, hlaw j, integral_indicator_const _ hA, smul_eq_mul, mul_one, measureReal_def]
  have hVarY : ∀ j, variance (Y j) P ≤ p := by
    intro j
    have := variance_le_sub_mul_sub (a := 0) (b := 1) (μ := P) (X := Y j)
      (ae_of_all _ fun ω => hY01 j ω) (hYm j).aemeasurable
    rw [hEY j] at this
    nlinarith
  have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin n))) fun i j => IndepFun (Y i) (Y j) P :=
    fun i _ j _ hij => (hind.indepFun hij).comp (measurable_const.indicator hA)
      (measurable_const.indicator hA)
  have hVarSum : variance (∑ j, Y j) P = ∑ j, variance (Y j) P :=
    IndepFun.variance_sum (fun j _ => hYmem j) hpair
  set S := empFreq X A with hS
  have hSeq : S = fun ω => (1 / n : ℝ) * (∑ j, Y j) ω := by
    funext ω; simp [hS, empFreq, hY, Finset.sum_apply]
  have hSm : Measurable S := measurable_empFreq hXm hA
  have hVarS : variance S P ≤ p / n := by
    rw [hSeq, variance_const_mul, hVarSum]
    calc (1 / (n : ℝ)) ^ 2 * ∑ j, variance (Y j) P ≤ (1 / (n : ℝ)) ^ 2 * ∑ _j : Fin n, p :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hVarY j) (by positivity)
      _ = p / n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have hYint : ∀ j, Integrable (Y j) P := fun j => (hYmem j).integrable one_le_two
  have hES : ∫ ω, S ω ∂P = p := by
    rw [hSeq]
    simp only [Finset.sum_apply]
    rw [integral_const_mul, integral_finsetSum _ fun j _ => hYint j]
    simp only [hEY, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- `W = |S − p|`
  set W : Ω → ℝ := fun ω => |S ω - p| with hW
  have hWm : Measurable W := continuous_abs.measurable.comp (hSm.sub_const p)
  have hWmem : MemLp W 2 P :=
    MemLp.of_bound hWm.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [hW, Real.norm_eq_abs, abs_abs, abs_le]
      have := empFreq_mem hn X A ω
      constructor <;> linarith [this.1, this.2])
  have hVarW := variance_nonneg W P
  rw [variance_eq_sub hWmem] at hVarW
  have hW2 : ∫ ω, (W ^ 2) ω ∂P = variance S P := by
    rw [variance_eq_integral hSm.aemeasurable, hES]
    congr 1; funext ω; simp [hW, sq_abs]
  rw [hW2] at hVarW
  have hsq : (∫ ω, W ω ∂P) ^ 2 ≤ p / n := by linarith
  exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)

end Emp

/-! ### The lemma -/

lemma sum_sqrt_cells_le {ℓ n : ℕ} (p : (Fin K → Fin ℓ) → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    ∑ i, Real.sqrt (p i / n) ≤ Real.sqrt ((ℓ : ℝ) ^ K / n) := by
  have h := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin K → Fin ℓ)) hp0
    (g := fun _ => (1 / n : ℝ)) (fun _ => by positivity)
  rw [hp1, Real.sqrt_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul] at h
  calc ∑ i, Real.sqrt (p i / n) = ∑ i, Real.sqrt (p i) * Real.sqrt (1 / n) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Real.sqrt_mul (hp0 i), mul_one_div]
    _ ≤ Real.sqrt (((ℓ ^ K : ℕ) : ℝ) * (1 / n)) := h
    _ = Real.sqrt ((ℓ : ℝ) ^ K / n) := by push_cast; rw [mul_one_div]

theorem empirical_wass : Claims.empirical_wass := by
  intro K n ℓ M c ν _ Ω _ P _ X hn hℓ hball hXm hind hlaw
  set Bc := Metric.closedBall c M with hBcdef
  have hBc : MeasurableSet Bc := measurableSet_closedBall
  have hM : 0 ≤ M := by
    by_contra h
    push Not at h
    have : Bc = ∅ := Metric.closedBall_eq_empty.mpr h
    rw [this, measure_empty] at hball
    exact zero_ne_one hball
  have hνc : ν Bcᶜ = 0 := by
    rw [measure_compl hBc (measure_ne_top _ _), hball, measure_univ, tsub_self]
  have hXin : ∀ᵐ ω ∂P, ∀ j, X j ω ∈ Bc := by
    rw [ae_all_iff]
    intro j
    have : P (X j ⁻¹' Bcᶜ) = 0 := by
      rw [← Measure.map_apply (hXm j) hBc.compl, hlaw j, hνc]
    exact measure_mono_null (fun ω hω => hω) this
  set η := ENNReal.ofReal (4 * M ^ 2 * K / ℓ ^ 2) with hη
  set C := ENNReal.ofReal (4 * M ^ 2) with hC
  set p : (Fin K → Fin ℓ) → ℝ := fun i => (ν (cellSet c M ℓ i)).toReal with hp
  have hpoint : ∀ᵐ ω ∂P, wassersteinEDist 2 (empMeasure fun i => X i ω) ν ^ 2 ≤
      η + C * ∑ i, ENNReal.ofReal |empFreq X (cellSet c M ℓ i) ω - p i| := by
    filter_upwards [hXin] with ω hω
    have hmass1 := empMeasure_univ hn (fun i => X i ω)
    have : IsFiniteMeasure (empMeasure fun i => X i ω) :=
      ⟨by rw [hmass1]; exact ENNReal.one_lt_top⟩
    have hmass : empMeasure (fun i => X i ω) univ = ν univ := by rw [hmass1, measure_univ]
    have hμc : empMeasure (fun i => X i ω) Bcᶜ = 0 := by
      rw [empMeasure_apply _ hBc.compl]
      simp [hω]
    refine (w2sq_le_cells c hM hℓ _ ν hmass hμc hνc).trans ?_
    rw [measure_univ, mul_one]
    gcongr with i
    rw [empMeasure_eq_ofReal hn X ω (measurableSet_cellSet c M ℓ i),
      ← ENNReal.ofReal_toReal (measure_ne_top ν (cellSet c M ℓ i)),
      ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hmeas : ∀ i, Measurable fun ω => ENNReal.ofReal |empFreq X (cellSet c M ℓ i) ω - p i| :=
    fun i => (continuous_abs.measurable.comp ((measurable_empFreq hXm (measurableSet_cellSet c M ℓ i)).sub_const _)).ennreal_ofReal
  have hint : ∀ i, ∫⁻ ω, ENNReal.ofReal |empFreq X (cellSet c M ℓ i) ω - p i| ∂P ≤
      ENNReal.ofReal (Real.sqrt (p i / n)) := by
    intro i
    have hInt : Integrable (fun ω => |empFreq X (cellSet c M ℓ i) ω - p i|) P := by
      refine Integrable.of_bound (C := 1) ?_ (ae_of_all _ fun ω => ?_)
      · exact (continuous_abs.measurable.comp ((measurable_empFreq hXm (measurableSet_cellSet c M ℓ i)).sub_const _)).aestronglyMeasurable
      · have h1 := empFreq_mem hn X (cellSet c M ℓ i) ω
        have hp0 : 0 ≤ p i := ENNReal.toReal_nonneg
        have hp1 : p i ≤ 1 :=
          ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
        rw [Real.norm_eq_abs, abs_abs, abs_le]
        constructor <;> linarith [h1.1, h1.2]
    rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun _ => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (integral_abs_empFreq_le hn ν hXm hind hlaw (measurableSet_cellSet c M ℓ i))
  refine (lintegral_mono_ae hpoint).trans ?_
  rw [lintegral_add_left (measurable_const (a := η)), lintegral_const,
    lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hmeas i),
    lintegral_finsetSum _ fun i _ => hmeas i]
  have hp0 : ∀ i, 0 ≤ p i := fun i => ENNReal.toReal_nonneg
  have hp1 : ∑ i, p i = 1 := by
    have hsum : ∑ i, ν (cellSet c M ℓ i) = 1 := by
      rw [← measure_univ (μ := ν), ← cellSet_cover c M hℓ,
        measure_iUnion (cellSet_disjoint c M ℓ) (measurableSet_cellSet c M ℓ), tsum_fintype]
    simp only [hp]
    rw [← ENNReal.toReal_sum fun i _ => measure_ne_top ν _, hsum, ENNReal.toReal_one]
  have hsq := sum_sqrt_cells_le (n := n) p hp0 hp1
  have hsqrt0 : ∀ i, 0 ≤ Real.sqrt (p i / n) := fun i => Real.sqrt_nonneg _
  calc η * P univ + C * ∑ i, ∫⁻ ω, ENNReal.ofReal |empFreq X (cellSet c M ℓ i) ω - p i| ∂P
      ≤ η + C * ∑ i, ENNReal.ofReal (Real.sqrt (p i / n)) := by
        rw [measure_univ, mul_one]
        gcongr with i
        exact hint i
    _ = ENNReal.ofReal (4 * M ^ 2 * K / ℓ ^ 2 + 4 * M ^ 2 * ∑ i, Real.sqrt (p i / n)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hsqrt0 i, hC, ← ENNReal.ofReal_mul (by positivity),
          hη, ← ENNReal.ofReal_add (by positivity)
            (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hsqrt0 i))]
    _ ≤ ENNReal.ofReal (4 * M ^ 2 * (K / (ℓ : ℝ) ^ 2 + Real.sqrt ((ℓ : ℝ) ^ K / n))) := by
        apply ENNReal.ofReal_le_ofReal
        have h4 : 0 ≤ 4 * M ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left hsq h4
        have : 4 * M ^ 2 * K / ℓ ^ 2 = 4 * M ^ 2 * (K / (ℓ : ℝ) ^ 2) := by ring
        nlinarith


/-! ### The rate -/

lemma rate_arith {K n : ℕ} (hn : 1 ≤ n) (M : ℝ) :
    1 ≤ ⌊(n : ℝ) ^ (1 / ((K : ℝ) + 4))⌋₊ ∧
    4 * M ^ 2 * (K / ((⌊(n : ℝ) ^ (1 / ((K : ℝ) + 4))⌋₊ : ℕ) : ℝ) ^ 2 +
        Real.sqrt (((⌊(n : ℝ) ^ (1 / ((K : ℝ) + 4))⌋₊ : ℕ) : ℝ) ^ K / n)) ≤
      4 * (4 * K + 1) * M ^ 2 * (n : ℝ) ^ (-(2 : ℝ) / (K + 4)) := by
  set a : ℝ := 1 / ((K : ℝ) + 4) with ha
  set x : ℝ := (n : ℝ) ^ a with hx
  set y : ℝ := (n : ℝ) ^ (-(2 : ℝ) / (K + 4)) with hy
  set ℓ : ℕ := ⌊x⌋₊ with hℓ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hK4 : (0 : ℝ) < (K : ℝ) + 4 := by positivity
  have hx1 : 1 ≤ x := Real.one_le_rpow hn' (by positivity)
  have hℓ1 : 1 ≤ ℓ := Nat.le_floor (by simpa using hx1)
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
  have hℓx : (ℓ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxℓ : x < ℓ + 1 := Nat.lt_floor_add_one x
  have h2ℓ : x ≤ 2 * ℓ := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
    linarith
  have hy0 : 0 ≤ y := Real.rpow_nonneg hn0 _
  have hpow : ∀ m : ℕ, x ^ m = (n : ℝ) ^ (a * m) := fun m => by
    rw [Real.rpow_mul hn0, Real.rpow_natCast]
  have hxy : x ^ 2 * y = 1 := by
    rw [hpow 2, hy, ← Real.rpow_add hnpos]
    have : a * ((2 : ℕ) : ℝ) + -(2 : ℝ) / (K + 4) = 0 := by rw [ha]; field_simp; ring
    rw [this, Real.rpow_zero]
  have hxK : x ^ K / n = y ^ 2 := by
    calc x ^ K / n = (n : ℝ) ^ (a * K) / n := by rw [hpow K]
      _ = (n : ℝ) ^ (a * K - 1) := by rw [Real.rpow_sub hnpos, Real.rpow_one]
      _ = y ^ 2 := by
        rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hn0]
        congr 1
        rw [ha]; field_simp; push_cast; ring
  refine ⟨hℓ1, ?_⟩
  have hb1 : (K : ℝ) / (ℓ : ℝ) ^ 2 ≤ 4 * K * y := by
    rw [div_le_iff₀ (by positivity)]
    have hx0 : 0 ≤ x := by linarith
    have hsq : x ^ 2 ≤ 4 * (ℓ : ℝ) ^ 2 := by nlinarith
    have h1 : 1 ≤ 4 * y * (ℓ : ℝ) ^ 2 := by nlinarith
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  have hb2 : Real.sqrt ((ℓ : ℝ) ^ K / n) ≤ y := by
    have h1 : (ℓ : ℝ) ^ K / n ≤ x ^ K / n :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hℓpos.le hℓx K) hn0
    rw [hxK] at h1
    calc Real.sqrt ((ℓ : ℝ) ^ K / n) ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h1
      _ = y := Real.sqrt_sq hy0
  have hM2 : 0 ≤ 4 * M ^ 2 := by positivity
  calc 4 * M ^ 2 * (K / (ℓ : ℝ) ^ 2 + Real.sqrt ((ℓ : ℝ) ^ K / n))
      ≤ 4 * M ^ 2 * (4 * K * y + y) := mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) hM2
    _ = 4 * (4 * K + 1) * M ^ 2 * y := by ring

theorem empirical_wass_rate : Claims.empirical_wass_rate := by
  intro K n M c ν _ Ω _ P _ X hn hball hXm hind hlaw
  obtain ⟨hℓ1, harith⟩ := rate_arith (K := K) hn M
  exact (empirical_wass K n _ M c ν Ω P X hn hℓ1 hball hXm hind hlaw).trans
    (ENNReal.ofReal_le_ofReal harith)

theorem empirical_wass_rate20 : Claims.empirical_wass_rate20 := by
  intro K n M c ν _ Ω _ P _ X hn hball hXm hind hlaw
  refine (empirical_wass_rate K n M c ν Ω P X hn hball hXm hind hlaw).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hy0 : 0 ≤ (n : ℝ) ^ (-(2 : ℝ) / (K + 4)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hMy : 0 ≤ M ^ 2 * (n : ℝ) ^ (-(2 : ℝ) / (K + 4)) := mul_nonneg (sq_nonneg M) hy0
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith

end StatFormal.OTFD.Wave6b
