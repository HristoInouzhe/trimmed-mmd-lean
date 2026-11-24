import StatFormal.Lib.Donsker.Defs
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Chaining: tightness in `C(X, ℝ)` of processes with sub-Gaussian increments (untrusted library code)

`X` a compact metric space with exponential nets (`HasExpNets`: `2^{-j}`-nets `T_j`, `|T_j| ≤ C A^j`), and a family
of random continuous functions `Z_i` with uniform sub-Gaussian tails
`P(u ≤ |Z_i(x) − Z_i(y)|) ≤ c exp(−u²/(Lρ)²)` for `d(x, y) ≤ ρ`, and `P(u ≤ |Z_i(x)|) ≤ c exp(−u²/B²)`.

Route (classical chaining with union bounds, no expectations of suprema and no measurability of suprema):
* deterministic chain (`chain_bound`): with projections `π_j : X → T_j`, `d(x, π_j x) ≤ 2^{-j}`, if every link
  `|f(π_{j+1}x) − f(π_j x)| ≤ u_j` then `|f x − f(π_J x)| ≤ Σ_{j ≥ J} u_j` (continuity of `f`);
* thresholds `u_j = 2L 2^{-j}(j+1)K₀`, `w_j = 4L 2^{-j}(j+1)K₀` with `e^{−K₀²} = r₀` small: the union bound over the
  `≤ C²A^{2j+1}` links at level `j` costs `≤ η 2^{-(j+1)}`;
* on the good event, `|f| ≤ M` and `|f x − f y| ≤ γ_J := 2Σ_{j≥J}u_j + w_J` whenever `d(x,y) ≤ 2^{-J}`; this set of
  `f` is compact by Arzelà–Ascoli (`isCompact_modulusSet`), uniformly in `i`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Filter Topology Set

namespace StatFormal.Foundations.Donsker

section Chain
variable {X : Type*} [MetricSpace X]

/-- Deterministic chaining. -/
lemma chain_bound (f : X → ℝ) (hf : Continuous f) (π : ℕ → X → X)
    (hπ : ∀ j x, dist x (π j x) ≤ (1 / 2 : ℝ) ^ j) (u : ℕ → ℝ) (hu0 : ∀ j, 0 ≤ u j) (hus : Summable u)
    (hlink : ∀ j x, |f (π (j + 1) x) - f (π j x)| ≤ u j) (x : X) (J : ℕ) :
    |f x - f (π J x)| ≤ ∑' j, u (j + J) := by
  have hsJ : Summable fun j => u (j + J) := (summable_nat_add_iff J).2 hus
  have hstep : ∀ K, |f (π (J + K) x) - f (π J x)| ≤ ∑ j ∈ Finset.range K, u (j + J) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have h1 := hlink (J + K) x
      have h2 : J + (K + 1) = J + K + 1 := by ring
      rw [h2]
      calc |f (π (J + K + 1) x) - f (π J x)|
          ≤ |f (π (J + K + 1) x) - f (π (J + K) x)| + |f (π (J + K) x) - f (π J x)| := abs_sub_le _ _ _
        _ ≤ u (J + K) + ∑ j ∈ Finset.range K, u (j + J) := add_le_add h1 ih
        _ = ∑ j ∈ Finset.range K, u (j + J) + u (K + J) := by rw [add_comm, Nat.add_comm J K]
  have hlim : Tendsto (fun K => f (π (J + K) x)) atTop (𝓝 (f x)) := by
    have hd : Tendsto (fun K => π (J + K) x) atTop (𝓝 x) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have h0 : Tendsto (fun K : ℕ => (1 / 2 : ℝ) ^ (J + K)) atTop (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
          (tendsto_atTop_atTop_of_monotone (fun a b h => by omega) (fun b => ⟨b, by omega⟩))
      refine squeeze_zero (fun _ => dist_nonneg) (fun K => ?_) h0
      rw [dist_comm]; exact hπ _ _
    exact (hf.tendsto x).comp hd
  have hlim2 : Tendsto (fun K => |f (π (J + K) x) - f (π J x)|) atTop (𝓝 (|f x - f (π J x)|)) :=
    ((hlim.sub_const _).abs)
  refine le_of_tendsto' hlim2 (fun K => (hstep K).trans ?_)
  exact hsJ.sum_le_tsum _ (fun j _ => hu0 _)

end Chain

/-- Normalised exponential nets (`1 ≤ C`, `1 ≤ A`). -/
lemma HasExpNets.normalize {X : Type*} [PseudoMetricSpace X] (h : HasExpNets X) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧ ∀ j : ℕ, ∃ T : Finset X, (T.card : ℝ) ≤ C * A ^ j ∧
      ∀ x, ∃ t ∈ T, dist x t ≤ (1 / 2 : ℝ) ^ j := by
  obtain ⟨C, A, h⟩ := h
  refine ⟨|C| + 1, |A| + 1, by linarith [abs_nonneg C], by linarith [abs_nonneg A], fun j => ?_⟩
  obtain ⟨T, hT, hc⟩ := h j
  refine ⟨T, hT.trans ?_, hc⟩
  calc C * A ^ j ≤ |C * A ^ j| := le_abs_self _
    _ = |C| * |A| ^ j := by rw [abs_mul, abs_pow]
    _ ≤ (|C| + 1) * (|A| + 1) ^ j := by
        gcongr
        · linarith
        · linarith

section Compact
variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- The Arzelà–Ascoli set: uniformly bounded by `M`, with modulus `γ_J` at scale `2^{-J}`, `γ_J → 0`. -/
def modulusSet (X : Type*) [MetricSpace X] (M : ℝ) (γ : ℕ → ℝ) : Set C(X, ℝ) :=
  {f | (∀ x, |f x| ≤ M) ∧ ∀ (J : ℕ) (x y : X), dist x y ≤ (1 / 2 : ℝ) ^ J → |f x - f y| ≤ γ J}

lemma isCompact_modulusSet (M : ℝ) (γ : ℕ → ℝ) (hγ : Tendsto γ atTop (𝓝 0)) :
    IsCompact (modulusSet X M γ) := by
  -- the pointwise description
  set S : Set (X → ℝ) := {f | (∀ x, |f x| ≤ M) ∧ ∀ (J : ℕ) (x y : X), dist x y ≤ (1 / 2 : ℝ) ^ J →
    |f x - f y| ≤ γ J} with hS
  have hmod : ∀ f ∈ S, ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → |f x - f y| < ε := by
    intro f hf ε hε
    obtain ⟨J, hJ⟩ := (hγ.eventually (gt_mem_nhds hε)).exists
    exact ⟨(1 / 2 : ℝ) ^ J, by positivity, fun x y hxy => (hf.2 J x y hxy.le).trans_lt hJ⟩
  have himage : ContinuousMap.toFun '' modulusSet X M γ = S := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩; exact hg
    · intro hf
      have hc : Continuous f := by
        rw [Metric.continuous_iff]
        intro x ε hε
        obtain ⟨δ, hδ, h⟩ := hmod f hf ε hε
        refine ⟨δ, hδ, fun y hy => ?_⟩
        rw [Real.dist_eq]
        exact h y x hy
      exact ⟨⟨f, hc⟩, hf, rfl⟩
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · rw [himage]
    have hsub : S ⊆ Set.pi univ (fun _ => Icc (-M) M) := by
      intro f hf x _
      exact abs_le.1 (hf.1 x)
    refine (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset ?_ hsub
    have h1 : IsClosed {f : X → ℝ | ∀ x, |f x| ≤ M} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun x => isClosed_le ((continuous_apply x).abs) continuous_const
    have h2 : IsClosed {f : X → ℝ | ∀ (J : ℕ) (x y : X), dist x y ≤ (1 / 2 : ℝ) ^ J → |f x - f y| ≤ γ J} := by
      simp only [ofPred_forall]
      refine isClosed_iInter fun J => isClosed_iInter fun x => isClosed_iInter fun y => ?_
      exact isClosed_iInter fun _ => isClosed_le (((continuous_apply x).sub (continuous_apply y)).abs) continuous_const
    exact h1.inter h2
  · intro x₀
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨J, hJ⟩ := (hγ.eventually (gt_mem_nhds hε)).exists
    refine ⟨(1 / 2 : ℝ) ^ J, by positivity, fun x hx f => ?_⟩
    rw [Real.dist_eq]
    exact (f.2.2 J x₀ x (by rw [dist_comm]; exact hx.le)).trans_lt hJ

end Compact

/-! ### The threshold arithmetic -/

lemma exp_neg_le_pow {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (j : ℕ) :
    Real.exp (-((((j : ℝ) + 1) * Real.sqrt (Real.log (1 / r))) ^ 2)) ≤ r ^ (j + 1) := by
  have hlog : 0 ≤ Real.log (1 / r) := Real.log_nonneg (by rw [le_div_iff₀ hr0]; linarith)
  have hK2 : Real.sqrt (Real.log (1 / r)) ^ 2 = Real.log (1 / r) := Real.sq_sqrt hlog
  have hr : r ^ (j + 1) = Real.exp (((j + 1 : ℕ) : ℝ) * (-Real.log (1 / r))) := by
    rw [Real.exp_nat_mul, one_div, Real.log_inv, neg_neg, Real.exp_log hr0]
  rw [hr, mul_pow, hK2]
  apply Real.exp_le_exp.2
  push_cast
  have h1 : ((j : ℝ) + 1) ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
  nlinarith [mul_le_mul_of_nonneg_right h1 hlog]

lemma exists_K0 {C A c η : ℝ} (hC : 1 ≤ C) (hA : 1 ≤ A) (hc : 0 ≤ c) (hη : 0 < η) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ j : ℕ,
      C ^ 2 * A * (A ^ 2) ^ j * (c * Real.exp (-((((j : ℝ) + 1) * K₀) ^ 2))) ≤ η * (1 / 2) ^ (j + 1) := by
  set D := C ^ 2 * A * c with hD
  have hD0 : 0 ≤ D := by positivity
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  set r₀ := min (1 / (2 * A ^ 2)) (η / (2 * D + 1)) with hr₀
  have hr0 : 0 < r₀ := lt_min (by positivity) (by positivity)
  have hr1 : r₀ ≤ 1 / (2 * A ^ 2) := min_le_left _ _
  have hr2 : r₀ ≤ η / (2 * D + 1) := min_le_right _ _
  have hr1' : r₀ ≤ 1 := hr1.trans (by rw [div_le_one (by positivity)]; linarith)
  refine ⟨Real.sqrt (Real.log (1 / r₀)), Real.sqrt_nonneg _, fun j => ?_⟩
  have hexp := exp_neg_le_pow hr0 hr1' j
  have hAr : A ^ 2 * r₀ ≤ 1 / 2 := by
    calc A ^ 2 * r₀ ≤ A ^ 2 * (1 / (2 * A ^ 2)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hDr : D * r₀ ≤ η / 2 := by
    calc D * r₀ ≤ D * (η / (2 * D + 1)) := by gcongr
      _ ≤ η / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hpow : (A ^ 2 * r₀) ^ j ≤ (1 / 2) ^ j := pow_le_pow_left₀ (by positivity) hAr j
  calc C ^ 2 * A * (A ^ 2) ^ j * (c * Real.exp (-((((j : ℝ) + 1) * Real.sqrt (Real.log (1 / r₀))) ^ 2)))
      ≤ C ^ 2 * A * (A ^ 2) ^ j * (c * r₀ ^ (j + 1)) := by gcongr
    _ = (D * r₀) * (A ^ 2 * r₀) ^ j := by rw [hD]; ring
    _ ≤ (η / 2) * (1 / 2) ^ j := by
        apply mul_le_mul hDr hpow (by positivity) (by positivity)
    _ = η * (1 / 2) ^ (j + 1) := by ring

lemma exists_K1 {C c η : ℝ} (hC : 1 ≤ C) (hc : 0 ≤ c) (hη : 0 < η) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ C * (c * Real.exp (-(K₁ ^ 2))) ≤ η := by
  set r₁ := min 1 (η / (C * c + 1)) with hr₁
  have hr0 : 0 < r₁ := lt_min one_pos (by positivity)
  have hr1 : r₁ ≤ 1 := min_le_left _ _
  have hr2 : r₁ ≤ η / (C * c + 1) := min_le_right _ _
  refine ⟨Real.sqrt (Real.log (1 / r₁)), Real.sqrt_nonneg _, ?_⟩
  have h := exp_neg_le_pow hr0 hr1 0
  simp only [Nat.cast_zero, zero_add, one_mul, pow_one] at h
  calc C * (c * Real.exp (-(Real.sqrt (Real.log (1 / r₁)) ^ 2))) ≤ C * (c * r₁) := by gcongr
    _ = (C * c) * r₁ := by ring
    _ ≤ (C * c) * (η / (C * c + 1)) := by gcongr
    _ ≤ η := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ C) hc]

lemma summable_succ_mul_half : Summable fun j : ℕ => ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j := by
  have h1 : Summable fun j : ℕ => (j : ℝ) ^ 1 * (1 / 2 : ℝ) ^ j :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  have h2 : Summable fun j : ℕ => (1 / 2 : ℝ) ^ j := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine (h1.add h2).congr fun j => ?_
  simp only [pow_one]; ring

/-! ### The tightness theorem -/

lemma ofReal_card_mul_le {ι : Type*} (F : Finset ι) {a b : ℝ} (ha : 0 ≤ a) (h : (F.card : ℝ) * a ≤ b) :
    ∑ _p ∈ F, ENNReal.ofReal a ≤ ENNReal.ofReal b := by
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

lemma tsum_ofReal_half (η : ℝ) (hη : 0 ≤ η) :
    ∑' j : ℕ, ENNReal.ofReal (η * (1 / 2) ^ (j + 1)) = ENNReal.ofReal η := by
  have hf : (fun j : ℕ => η * (1 / 2 : ℝ) ^ (j + 1)) = fun n => η / 2 / 2 ^ n := by
    funext j; rw [pow_succ, one_div, inv_pow]; field_simp
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)]
  · rw [hf, tsum_geometric_two' η]
  · rw [hf]
    exact (summable_geometric_two.mul_left (η / 2)).congr fun j => by rw [one_div, inv_pow]; field_simp

theorem isTightMeasureSet_of_subgaussian {X : Type*} [MetricSpace X] [CompactSpace X] (hX : HasExpNets X)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {ι : Type*}
    (Z : ι → Ω → C(X, ℝ)) (hZ : ∀ i, AEMeasurable (Z i) μ) {c L B : ℝ} (hc : 0 ≤ c) (hL : 0 < L) (hB : 0 < B)
    (hinc : ∀ i x y (ρ : ℝ), 0 < ρ → dist x y ≤ ρ → ∀ u : ℝ, 0 ≤ u →
      μ {ω | u ≤ |Z i ω x - Z i ω y|} ≤ ENNReal.ofReal (c * Real.exp (-(u ^ 2 / (L * ρ) ^ 2))))
    (hpt : ∀ i x (u : ℝ), 0 ≤ u → μ {ω | u ≤ |Z i ω x|} ≤ ENNReal.ofReal (c * Real.exp (-(u ^ 2 / B ^ 2)))) :
    IsTightMeasureSet (Set.range fun i => μ.map (Z i)) := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨η, hη0, hηε⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal (3 * η) ≤ ε := by
    by_cases htop : ε = ⊤
    · exact ⟨1, one_pos, by rw [htop]; exact le_top⟩
    · refine ⟨ε.toReal / 3, by have := ENNReal.toReal_pos hε.ne' htop; positivity, ?_⟩
      rw [mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0), ENNReal.ofReal_toReal htop]
  obtain ⟨C, A, hC, hA, hnet⟩ := hX.normalize
  choose T hTc hTd using hnet
  choose π hπT hπd using hTd
  obtain ⟨K₀, hK₀, hK₀b⟩ := exists_K0 hC hA hc hη0
  obtain ⟨K₁, hK₁, hK₁b⟩ := exists_K1 hC hc hη0
  -- thresholds
  set u : ℕ → ℝ := fun j => 2 * L * K₀ * (((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j) with hu
  set w : ℕ → ℝ := fun j => 4 * L * K₀ * (((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j) with hw
  have hu0 : ∀ j, 0 ≤ u j := fun j => by positivity
  have hus : Summable u := summable_succ_mul_half.mul_left _
  set S : ℕ → ℝ := fun J => ∑' j, u (j + J) with hS
  set M₀ : ℝ := B * K₁ with hM₀
  set M : ℝ := M₀ + S 0 with hM
  set γ : ℕ → ℝ := fun J => 2 * S J + w J with hγ
  have hγt : Tendsto γ atTop (𝓝 0) := by
    have h1 : Tendsto S atTop (𝓝 0) := tendsto_sum_nat_add u
    have h2 : Tendsto w atTop (𝓝 0) := by
      have := (summable_succ_mul_half.tendsto_atTop_zero).const_mul (4 * L * K₀)
      rw [mul_zero] at this
      exact this
    have := (h1.const_mul 2).add h2
    simpa using this
  refine ⟨modulusSet X M γ, isCompact_modulusSet M γ hγt, ?_⟩
  rintro _ ⟨i, rfl⟩
  -- the bad events
  let Lk : ℕ → Finset (X × X) := fun j =>
    ((T (j + 1)) ×ˢ (T j)).filter (fun p => dist p.1 p.2 ≤ 2 * (1 / 2 : ℝ) ^ j)
  let Md : ℕ → Finset (X × X) := fun j =>
    ((T j) ×ˢ (T j)).filter (fun p => dist p.1 p.2 ≤ 4 * (1 / 2 : ℝ) ^ j)
  let B1 : Set Ω := ⋃ j, ⋃ p ∈ Lk j, {ω | u j ≤ |Z i ω p.1 - Z i ω p.2|}
  let B2 : Set Ω := ⋃ j, ⋃ p ∈ Md j, {ω | w j ≤ |Z i ω p.1 - Z i ω p.2|}
  let B3 : Set Ω := ⋃ a ∈ T 0, {ω | M₀ ≤ |Z i ω a|}
  -- good event ⇒ in the compact set
  have hgood : Z i ⁻¹' (modulusSet X M γ)ᶜ ⊆ B1 ∪ B2 ∪ B3 := by
    intro ω hω
    by_contra hbad
    simp only [mem_union, not_or] at hbad
    obtain ⟨⟨hb1, hb2⟩, hb3⟩ := hbad
    apply hω
    set f := Z i ω with hf
    have hlink : ∀ j x, |f (π (j + 1) x) - f (π j x)| ≤ u j := by
      intro j x
      have hmem : (π (j + 1) x, π j x) ∈ Lk j := by
        simp only [Lk, Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨hπT _ _, hπT _ _⟩, ?_⟩
        calc dist (π (j + 1) x) (π j x) ≤ dist (π (j + 1) x) x + dist x (π j x) := dist_triangle _ _ _
          _ ≤ (1 / 2 : ℝ) ^ (j + 1) + (1 / 2 : ℝ) ^ j := by
              rw [dist_comm]; exact add_le_add (hπd _ _) (hπd _ _)
          _ ≤ 2 * (1 / 2 : ℝ) ^ j := by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) j]
      have : ω ∉ {ω | u j ≤ |Z i ω (π (j + 1) x) - Z i ω (π j x)|} := by
        intro h; apply hb1; exact mem_iUnion.2 ⟨j, mem_iUnion₂.2 ⟨_, hmem, h⟩⟩
      simp only [mem_ofPred_eq, not_le] at this
      exact this.le
    have hchain := chain_bound f f.continuous π hπd u hu0 hus hlink
    refine ⟨fun x => ?_, fun J x y hxy => ?_⟩
    · have h0 := hchain x 0
      have hpt0 : |f (π 0 x)| < M₀ := by
        have : ω ∉ {ω | M₀ ≤ |Z i ω (π 0 x)|} := by
          intro h; apply hb3; exact mem_iUnion₂.2 ⟨_, hπT 0 x, h⟩
        simpa using this
      have : S 0 = ∑' j, u (j + 0) := rfl
      calc |f x| ≤ |f x - f (π 0 x)| + |f (π 0 x)| := by
            have := abs_sub_abs_le_abs_sub (f x) (f (π 0 x)); linarith
        _ ≤ S 0 + M₀ := add_le_add h0 hpt0.le
        _ = M := by rw [hM]; ring
    · have hmem : (π J x, π J y) ∈ Md J := by
        simp only [Md, Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨hπT _ _, hπT _ _⟩, ?_⟩
        calc dist (π J x) (π J y) ≤ dist (π J x) x + dist x y + dist y (π J y) := dist_triangle4 _ _ _ _
          _ ≤ (1 / 2 : ℝ) ^ J + (1 / 2 : ℝ) ^ J + (1 / 2 : ℝ) ^ J := by
              rw [dist_comm (π J x)]; exact add_le_add (add_le_add (hπd _ _) hxy) (hπd _ _)
          _ ≤ 4 * (1 / 2 : ℝ) ^ J := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) J]
      have hmid : |f (π J x) - f (π J y)| < w J := by
        have : ω ∉ {ω | w J ≤ |Z i ω (π J x) - Z i ω (π J y)|} := by
          intro h; apply hb2; exact mem_iUnion.2 ⟨J, mem_iUnion₂.2 ⟨_, hmem, h⟩⟩
        simpa using this
      have hx := hchain x J
      have hy := hchain y J
      calc |f x - f y| ≤ |f x - f (π J x)| + |f (π J x) - f (π J y)| + |f (π J y) - f y| := by
            have h1 := abs_sub_le (f x) (f (π J x)) (f y)
            have h2 := abs_sub_le (f (π J x)) (f (π J y)) (f y)
            linarith
        _ ≤ S J + w J + S J := by
            rw [abs_sub_comm (f (π J y))]; exact add_le_add (add_le_add hx hmid.le) hy
        _ = γ J := by rw [hγ]; ring
  -- measure bounds
  have hlev : ∀ j, ∑ p ∈ Lk j, μ {ω | u j ≤ |Z i ω p.1 - Z i ω p.2|} ≤ ENNReal.ofReal (η * (1 / 2) ^ (j + 1)) := by
    intro j
    have hρ : (0 : ℝ) < 2 * (1 / 2) ^ j := by positivity
    have hexp : u j ^ 2 / (L * (2 * (1 / 2) ^ j)) ^ 2 = (((j : ℝ) + 1) * K₀) ^ 2 := by
      simp only [hu]; field_simp
    calc ∑ p ∈ Lk j, μ {ω | u j ≤ |Z i ω p.1 - Z i ω p.2|}
        ≤ ∑ p ∈ Lk j, ENNReal.ofReal (c * Real.exp (-((((j : ℝ) + 1) * K₀) ^ 2))) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hd : dist p.1 p.2 ≤ 2 * (1 / 2) ^ j := (Finset.mem_filter.1 hp).2
          have := hinc i p.1 p.2 _ hρ hd (u j) (hu0 j)
          rwa [hexp] at this
      _ ≤ ENNReal.ofReal (η * (1 / 2) ^ (j + 1)) := by
          refine ofReal_card_mul_le _ (by positivity) ?_
          have hcard : ((Lk j).card : ℝ) ≤ C ^ 2 * A * (A ^ 2) ^ j := by
            calc ((Lk j).card : ℝ) ≤ ((T (j + 1)) ×ˢ (T j)).card := by exact_mod_cast Finset.card_filter_le _ _
              _ = (T (j + 1)).card * (T j).card := by rw [Finset.card_product]; push_cast; ring
              _ ≤ (C * A ^ (j + 1)) * (C * A ^ j) :=
                  mul_le_mul (hTc _) (hTc _) (by positivity) (by positivity)
              _ = C ^ 2 * A * (A ^ 2) ^ j := by ring
          calc ((Lk j).card : ℝ) * (c * Real.exp (-((((j : ℝ) + 1) * K₀) ^ 2)))
              ≤ C ^ 2 * A * (A ^ 2) ^ j * (c * Real.exp (-((((j : ℝ) + 1) * K₀) ^ 2))) :=
                mul_le_mul_of_nonneg_right hcard (by positivity)
            _ ≤ _ := hK₀b j
  have hlev2 : ∀ j, ∑ p ∈ Md j, μ {ω | w j ≤ |Z i ω p.1 - Z i ω p.2|} ≤ ENNReal.ofReal (η * (1 / 2) ^ (j + 1)) := by
    intro j
    have hρ : (0 : ℝ) < 4 * (1 / 2) ^ j := by positivity
    have hexp : w j ^ 2 / (L * (4 * (1 / 2) ^ j)) ^ 2 = (((j : ℝ) + 1) * K₀) ^ 2 := by
      simp only [hw]; field_simp
    calc ∑ p ∈ Md j, μ {ω | w j ≤ |Z i ω p.1 - Z i ω p.2|}
        ≤ ∑ p ∈ Md j, ENNReal.ofReal (c * Real.exp (-((((j : ℝ) + 1) * K₀) ^ 2))) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hd : dist p.1 p.2 ≤ 4 * (1 / 2) ^ j := (Finset.mem_filter.1 hp).2
          have := hinc i p.1 p.2 _ hρ hd (w j) (by positivity)
          rwa [hexp] at this
      _ ≤ ENNReal.ofReal (η * (1 / 2) ^ (j + 1)) := by
          refine ofReal_card_mul_le _ (by positivity) ?_
          have hcard : ((Md j).card : ℝ) ≤ C ^ 2 * A * (A ^ 2) ^ j := by
            calc ((Md j).card : ℝ) ≤ ((T j) ×ˢ (T j)).card := by exact_mod_cast Finset.card_filter_le _ _
              _ = (T j).card * (T j).card := by rw [Finset.card_product]; push_cast; ring
              _ ≤ (C * A ^ j) * (C * A ^ j) :=
                  mul_le_mul (hTc _) (hTc _) (by positivity) (by positivity)
              _ = C ^ 2 * 1 * (A ^ 2) ^ j := by ring
              _ ≤ C ^ 2 * A * (A ^ 2) ^ j := by gcongr
          calc ((Md j).card : ℝ) * (c * Real.exp (-((((j : ℝ) + 1) * K₀) ^ 2)))
              ≤ C ^ 2 * A * (A ^ 2) ^ j * (c * Real.exp (-((((j : ℝ) + 1) * K₀) ^ 2))) :=
                mul_le_mul_of_nonneg_right hcard (by positivity)
            _ ≤ _ := hK₀b j
  have hB1 : μ B1 ≤ ENNReal.ofReal η := by
    calc μ B1 ≤ ∑' j, μ (⋃ p ∈ Lk j, {ω | u j ≤ |Z i ω p.1 - Z i ω p.2|}) := measure_iUnion_le _
      _ ≤ ∑' j, ENNReal.ofReal (η * (1 / 2) ^ (j + 1)) :=
          ENNReal.tsum_le_tsum fun j => (measure_biUnion_finset_le _ _).trans (hlev j)
      _ = ENNReal.ofReal η := tsum_ofReal_half η hη0.le
  have hB2 : μ B2 ≤ ENNReal.ofReal η := by
    calc μ B2 ≤ ∑' j, μ (⋃ p ∈ Md j, {ω | w j ≤ |Z i ω p.1 - Z i ω p.2|}) := measure_iUnion_le _
      _ ≤ ∑' j, ENNReal.ofReal (η * (1 / 2) ^ (j + 1)) :=
          ENNReal.tsum_le_tsum fun j => (measure_biUnion_finset_le _ _).trans (hlev2 j)
      _ = ENNReal.ofReal η := tsum_ofReal_half η hη0.le
  have hB3 : μ B3 ≤ ENNReal.ofReal η := by
    have hexp : M₀ ^ 2 / B ^ 2 = K₁ ^ 2 := by rw [hM₀]; field_simp
    calc μ B3 ≤ ∑ a ∈ T 0, μ {ω | M₀ ≤ |Z i ω a|} := measure_biUnion_finset_le _ _
      _ ≤ ∑ a ∈ T 0, ENNReal.ofReal (c * Real.exp (-(K₁ ^ 2))) :=
          Finset.sum_le_sum fun a _ => by have := hpt i a M₀ (by positivity); rwa [hexp] at this
      _ ≤ ENNReal.ofReal η := by
          refine ofReal_card_mul_le _ (by positivity) ?_
          have : ((T 0).card : ℝ) ≤ C := by simpa using hTc 0
          exact (mul_le_mul_of_nonneg_right this (by positivity)).trans hK₁b
  have hmeas : MeasurableSet (modulusSet X M γ)ᶜ := (isCompact_modulusSet M γ hγt).isClosed.measurableSet.compl
  rw [Measure.map_apply_of_aemeasurable (hZ i) hmeas]
  calc μ (Z i ⁻¹' (modulusSet X M γ)ᶜ) ≤ μ (B1 ∪ B2 ∪ B3) := measure_mono hgood
    _ ≤ μ B1 + μ B2 + μ B3 := (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _) |>.trans (by rw [add_assoc])
    _ ≤ ENNReal.ofReal η + ENNReal.ofReal η + ENNReal.ofReal η := add_le_add (add_le_add hB1 hB2) hB3
    _ = ENNReal.ofReal (3 * η) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ ≤ ε := hηε

end StatFormal.Foundations.Donsker
