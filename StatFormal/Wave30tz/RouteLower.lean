import StatFormal.Wave30tz.RouteIface
import StatFormal.Wave30tz.RouteBet
import StatFormal.Wave30tz.RouteFit
import StatFormal.Wave30ty.Proofs
import StatFormal.Wave30tr.RouteConst

/-!
# Wave 30tz route: the lower side of Proposition 1 (`prop:loconsistency`, §5) — untrusted

* `dpop_antitone : Iface.DpopAntitone`: the admissible weights at `α` are admissible at
  `α' ≥ α` (`1/(1−α) ≤ 1/(1−α')`), so the regions grow and their distance shrinks.
* `map_fitPair`: the law of the fitting sample `(fitSample lx b x, fitSample ly b y)` of a
  batch under `sampleLaw P Q n m` is `sampleLaw P Q n_b m_b` (a marginal of an i.i.d.
  product under an injective reindexing).
* `fit_tail`: `P(Z_b > τ), P(Z⁻_b > τ) ≤ exp(−2(τ − μ₁)₊²/(D_φ² r))` from the certified
  `Wave30ty.hinge` (`E Z ≤ 2[κ√s + κ(e_n + e_m)] ≤ μ₁ = 2(1+√2)κ√r`, `Wave30tr.ek_le`) and
  `Wave30ty.hinge_tail_strict` (oscillations `≤ D_φ`).
* `witness_step`: on `{Z_b ≤ τ_*, Z⁻_b ≤ τ_*}`, at a level `α_j ≤ α_i`, Lemma 4
  (`fitted_ramp_route`) and `theta_mono_route` with (S) give `Θ ≥ d/2`, so the rule bets
  and the ramp has excess `≥ ϱ_*`.
* `core_lower_bound : Iface.CoreLowerBound`: the union bound over the fitting event
  (`fitEvent_compl_le`) and the levels `j ≤ i` (`grid_events_route`), with Lemma 5
  (`bet_power_route`, via `bet_step`, `bet_arith`) on the fitting event at every level.
* `lo_lower_bound_route : Claims.lo_lower_bound`: `σ²_min ≤ 4` and
  `N ≥ L(1+α_i)²/(2λ_max²)` make `λ_N = √(L/(2N))`, so `genEps = ε_N`.
-/

set_option linter.style.longLine false


noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave30tz

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30ty StatFormal.Wave30tp
open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

namespace Lower

open scoped StatFormal.Wave30tz.Bet

/-! ### `α ↦ D_α` is nonincreasing -/

section Antitone

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma region_mono_alpha (φ : 𝒳 → H) (P : Measure 𝒳) {α α' : ℝ} (hle : α ≤ α') (h1 : α' < 1) :
    region φ α P ⊆ region φ α' P := by
  rintro z ⟨g, hg, hb, hi, rfl⟩
  have hβ : 1 / (1 - α) ≤ 1 / (1 - α') := one_div_le_one_div_of_le (by linarith) (by linarith)
  exact ⟨g, hg, fun x => ⟨(hb x).1, (hb x).2.trans hβ⟩, hi, rfl⟩

omit [InnerProductSpace ℝ H] in
lemma setDist_le_norm' {A B : Set H} {a b : H} (ha : a ∈ A) (hb : b ∈ B) : setDist A B ≤ ‖a - b‖ :=
  csInf_le ⟨0, by rintro _ ⟨a', _, b', _, rfl⟩; exact norm_nonneg _⟩ ⟨a, ha, b, hb, rfl⟩

omit [InnerProductSpace ℝ H] in
lemma setDist_anti' {A B A' B' : Set H} (hA : A.Nonempty) (hB : B.Nonempty) (hAA : A ⊆ A')
    (hBB : B ⊆ B') : setDist A' B' ≤ setDist A B := by
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  refine le_csInf ⟨_, a₀, ha₀, b₀, hb₀, rfl⟩ ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact setDist_le_norm' (hAA ha) (hBB hb)

end Antitone

end Lower

open Lower in
/-- `α ↦ D_α(P,Q)` is nonincreasing on `[0,1)`. -/
theorem dpop_antitone : Iface.DpopAntitone := by
  intro 𝒳 H _ _ _ φ κ P Q _ _ α α' _ _ h0 hle h1
  exact setDist_anti' (region_nonempty P h0 (hle.trans_lt h1)) (region_nonempty Q h0 (hle.trans_lt h1))
    (region_mono_alpha φ P hle h1) (region_mono_alpha φ Q hle h1)

namespace Lower

/-! ### The law of a fitting sample -/

section Marginal

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

lemma measurable_reindex {k p : ℕ} (e : Fin k → Fin p) :
    Measurable fun (x : Fin p → 𝒳) (j : Fin k) => x (e j) :=
  Measurable.of_eval fun j => measurable_pi_apply (e j)

/-- The marginal of an i.i.d. product under an injective reindexing. -/
lemma map_reindex (P : Measure 𝒳) [IsProbabilityMeasure P] {k p : ℕ} (e : Fin k → Fin p)
    (he : Function.Injective e) :
    (Measure.pi fun _ : Fin p => P).map (fun (x : Fin p → 𝒳) (j : Fin k) => x (e j)) =
      Measure.pi fun _ : Fin k => P := by
  classical
  have hm := measurable_reindex (𝒳 := 𝒳) e
  have : IsProbabilityMeasure ((Measure.pi fun _ : Fin p => P).map
      (fun (x : Fin p → 𝒳) (j : Fin k) => x (e j))) := inferInstance
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  set s' : Fin p → Set 𝒳 := Function.extend e s (fun _ => univ) with hs'
  have hpre : (fun (x : Fin p → 𝒳) (j : Fin k) => x (e j)) ⁻¹' univ.pi s = univ.pi s' := by
    ext x
    simp only [mem_preimage, mem_univ_pi]
    constructor
    · intro hx i
      by_cases h : ∃ j, e j = i
      · obtain ⟨j, rfl⟩ := h
        rw [hs', he.extend_apply]
        exact hx j
      · rw [hs', Function.extend_apply' _ _ _ h]
        exact mem_univ _
    · intro hx j
      have := hx (e j)
      rwa [hs', he.extend_apply] at this
  rw [hpre, Measure.pi_pi]
  have h1 : ∏ i ∈ Finset.univ.image e, P (s' i) = ∏ i, P (s' i) := by
    refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
    have h : ¬∃ j, e j = i := by
      rintro ⟨j, rfl⟩
      exact hi (Finset.mem_image_of_mem e (Finset.mem_univ j))
    rw [hs', Function.extend_apply' _ _ _ h, measure_univ]
  rw [← h1, Finset.prod_image fun a _ b _ hab => he hab]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hs', he.extend_apply]

lemma measurable_fitSample {p : ℕ} (l : Fin p → ℕ) (b : ℕ) :
    Measurable (fitSample (𝒳 := 𝒳) l b) :=
  measurable_reindex _

lemma map_fitSample (P : Measure 𝒳) [IsProbabilityMeasure P] {p : ℕ} (l : Fin p → ℕ) (b : ℕ) :
    (Measure.pi fun _ : Fin p => P).map (fitSample l b) = Measure.pi fun _ : Fin (fitCard l b) => P :=
  map_reindex P _ (Finset.orderEmbOfFin _ _).injective

/-- The fitting sample of a batch, as a map of the data. -/
def fitPair {n m : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ) (b : ℕ) (ω : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    (Fin (fitCard lx b) → 𝒳) × (Fin (fitCard ly b) → 𝒳) :=
  (fitSample lx b ω.1, fitSample ly b ω.2)

lemma measurable_fitPair {n m : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ) (b : ℕ) :
    Measurable (fitPair (𝒳 := 𝒳) lx ly b) :=
  ((measurable_fitSample lx b).comp measurable_fst).prodMk ((measurable_fitSample ly b).comp measurable_snd)

lemma map_fitPair (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {n m : ℕ}
    (lx : Fin n → ℕ) (ly : Fin m → ℕ) (b : ℕ) :
    (sampleLaw P Q n m).map (fitPair lx ly b) = sampleLaw P Q (fitCard lx b) (fitCard ly b) := by
  unfold sampleLaw
  have e : fitPair (𝒳 := 𝒳) lx ly b = Prod.map (fitSample lx b) (fitSample ly b) := rfl
  rw [e, ← Measure.map_prod_map _ _ (measurable_fitSample lx b) (measurable_fitSample ly b),
    map_fitSample, map_fitSample]

lemma fitPair_apply (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {n m : ℕ}
    (lx : Fin n → ℕ) (ly : Fin m → ℕ) (b : ℕ) {S : Set ((Fin (fitCard lx b) → 𝒳) × (Fin (fitCard ly b) → 𝒳))}
    (hS : MeasurableSet S) :
    sampleLaw P Q n m (fitPair lx ly b ⁻¹' S) = sampleLaw P Q (fitCard lx b) (fitCard ly b) S := by
  rw [← map_fitPair P Q lx ly b, Measure.map_apply (measurable_fitPair lx ly b) hS]

end Marginal

/-! ### The hinge suprema `Z`, `Z⁻` with `ψ = (·)₊`, `r = 1`, `ρ₁ = ρ₂ = κ` -/

section Hinge

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma isHingeMap_hingePos : IsHingeMap (hingePos (𝒳 := 𝒳)) := by
  refine ⟨fun _ => LipschitzWith.id.max_const 0, ?_, ⟨0, fun _ => by simp [hingePos]⟩⟩
  exact measurable_snd.max measurable_const

lemma bddAbove_hingeZ (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    BddAbove (range fun p : hingePar (H := H) 1 κ κ =>
      devPop P x (hOne hingePos φ p.1.1 p.1.2.1) + devPop Q y (hTwo hingePos φ p.1.1 p.1.2.2)) := by
  refine ⟨2 * κ + 2 * κ, ?_⟩
  rintro _ ⟨⟨⟨f, a, b⟩, hp⟩, rfl⟩
  obtain ⟨hf, ha, hb⟩ := hp
  have hvb := Fit.abs_inner_le_of_norm hκ hf
  have h1 : devPop P x (hOne hingePos φ f a) ≤ 2 * κ := by
    refine Elem.devPop_le P x (fun z => le_max_right _ _) fun z => ?_
    have := abs_le.1 (hvb z)
    have := abs_le.1 ha
    have hκ0 : 0 ≤ κ := (abs_nonneg _).trans ha
    exact max_le (by linarith) (by linarith)
  have h2 : devPop Q y (hTwo hingePos φ f b) ≤ 2 * κ := by
    refine Elem.devPop_le Q y (fun z => le_max_right _ _) fun z => ?_
    have := abs_le.1 (hvb z)
    have := abs_le.1 hb
    have hκ0 : 0 ≤ κ := (abs_nonneg _).trans hb
    exact max_le (by linarith) (by linarith)
  exact add_le_add h1 h2

lemma hingeZ_nonneg (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {n m : ℕ} (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    0 ≤ hingeZ P Q φ hingePos hingePos 1 κ κ z := by
  obtain ⟨z0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ z0)
  have h : devPop P z.1 (hOne hingePos φ (0 : H) 0) + devPop Q z.2 (hTwo hingePos φ (0 : H) 0) ≤
      hingeZ P Q φ hingePos hingePos 1 κ κ z :=
    le_ciSup (bddAbove_hingeZ P Q hκ z.1 z.2)
      (⟨((0 : H), (0 : ℝ), (0 : ℝ)), by simp, by simpa using hκ0, by simpa using hκ0⟩ : hingePar (H := H) 1 κ κ)
  have h0 : devPop P z.1 (hOne hingePos φ (0 : H) 0) + devPop Q z.2 (hTwo hingePos φ (0 : H) 0) = 0 := by
    simp [devPop, hOne, hTwo, hingePos]
  linarith

lemma hingeZm_nonneg' (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {n m : ℕ} (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    0 ≤ hingeZm P Q φ hingePos hingePos 1 κ κ z :=
  Fit.hingeZm_nonneg P Q hκ z.1 z.2

omit [MeasurableSpace 𝒳] in
lemma osc_hOne {φ : 𝒳 → H} {κ Dφ : ℝ} (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) :
    ∀ p ∈ hingePar (H := H) 1 κ κ, ∀ x x' : 𝒳, |hOne hingePos φ p.1 p.2.1 x - hOne hingePos φ p.1 p.2.1 x'| ≤ Dφ := by
  intro p hp x x'
  unfold hOne hingePos
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have e : p.2.1 - ⟪p.1, φ x⟫_ℝ - (p.2.1 - ⟪p.1, φ x'⟫_ℝ) = ⟪p.1, φ x' - φ x⟫_ℝ := by
    rw [inner_sub_right]; ring
  rw [e]
  refine (abs_real_inner_le_norm _ _).trans ?_
  calc ‖p.1‖ * ‖φ x' - φ x‖ ≤ 1 * Dφ := mul_le_mul hp.1 (hDφ x' x) (norm_nonneg _) zero_le_one
    _ = Dφ := one_mul _

omit [MeasurableSpace 𝒳] in
lemma osc_hTwo {φ : 𝒳 → H} {κ Dφ : ℝ} (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) :
    ∀ p ∈ hingePar (H := H) 1 κ κ, ∀ y y' : 𝒳, |hTwo hingePos φ p.1 p.2.2 y - hTwo hingePos φ p.1 p.2.2 y'| ≤ Dφ := by
  intro p hp y y'
  unfold hTwo hingePos
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have e : ⟪p.1, φ y⟫_ℝ - p.2.2 - (⟪p.1, φ y'⟫_ℝ - p.2.2) = ⟪p.1, φ y - φ y'⟫_ℝ := by
    rw [inner_sub_right]; ring
  rw [e]
  refine (abs_real_inner_le_norm _ _).trans ?_
  calc ‖p.1‖ * ‖φ y - φ y'‖ ≤ 1 * Dφ := mul_le_mul hp.1 (hDφ y y') (norm_nonneg _) zero_le_one
    _ = Dφ := one_mul _

/-- `1/√a + 1/√b ≤ √2 √(1/a + 1/b)`. -/
lemma inv_sqrt_add_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / √a + 1 / √b ≤ √2 * √(1 / a + 1 / b) := by
  have hu : 0 ≤ 1 / √a := by positivity
  have hv : 0 ≤ 1 / √b := by positivity
  have e1 : (1 / √a) ^ 2 = 1 / a := by rw [div_pow, Real.sq_sqrt ha.le, one_pow]
  have e2 : (1 / √b) ^ 2 = 1 / b := by rw [div_pow, Real.sq_sqrt hb.le, one_pow]
  rw [← Real.sqrt_mul (by norm_num)]
  refine Real.le_sqrt_of_sq_le ?_
  rw [← e1, ← e2]
  nlinarith [sq_nonneg (1 / √a - 1 / √b)]

end Hinge

/-! ### The fitting probability -/

section Tail

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [TopologicalSpace.SeparableSpace H]

/-- `E Z, E Z⁻ ≤ μ₁` and `P(Z > τ), P(Z⁻ > τ) ≤ exp(−2(τ − μ₁)₊²/(D_φ² r))` on samples of sizes `n', m' ≥ 1` with
`1/n' + 1/m' ≤ r`. -/
theorem fit_tail (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ Dφ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) (hDφ0 : 0 < Dφ)
    {n' m' : ℕ} (hn : 1 ≤ n') (hm : 1 ≤ m') {r : ℝ} (hr : 1 / (n' : ℝ) + 1 / (m' : ℝ) ≤ r) (τ : ℝ) :
    MeasurableSet {z : (Fin n' → 𝒳) × (Fin m' → 𝒳) | τ < hingeZ P Q φ hingePos hingePos 1 κ κ z} ∧
    MeasurableSet {z : (Fin n' → 𝒳) × (Fin m' → 𝒳) | τ < hingeZm P Q φ hingePos hingePos 1 κ κ z} ∧
    sampleLaw P Q n' m' {z | τ < hingeZ P Q φ hingePos hingePos 1 κ κ z} ≤
      ENNReal.ofReal (Real.exp (-(2 * (max (τ - 2 * (1 + √2) * κ * √r) 0) ^ 2 / (Dφ ^ 2 * r)))) ∧
    sampleLaw P Q n' m' {z | τ < hingeZm P Q φ hingePos hingePos 1 κ κ z} ≤
      ENNReal.ofReal (Real.exp (-(2 * (max (τ - 2 * (1 + √2) * κ * √r) 0) ^ 2 / (Dφ ^ 2 * r)))) := by
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
  obtain ⟨hZm, hZmm, -, -, hEZ, hEZm⟩ := StatFormal.Wave30ty.hinge 𝒳 H P Q φ κ hingePos hingePos 1 κ κ n' m' hφ hκ
    isHingeMap_hingePos isHingeMap_hingePos zero_le_one hκ0 hκ0 hn hm
  have hS1 : MeasurableSet {z : (Fin n' → 𝒳) × (Fin m' → 𝒳) | τ < hingeZ P Q φ hingePos hingePos 1 κ κ z} :=
    measurableSet_lt measurable_const hZm
  have hS2 : MeasurableSet {z : (Fin n' → 𝒳) × (Fin m' → 𝒳) | τ < hingeZm P Q φ hingePos hingePos 1 κ κ z} :=
    measurableSet_lt measurable_const hZmm
  refine ⟨hS1, hS2, ?_⟩
  have hnpos : (0 : ℝ) < n' := by exact_mod_cast hn
  have hmpos : (0 : ℝ) < m' := by exact_mod_cast hm
  set s : ℝ := 1 / (n' : ℝ) + 1 / (m' : ℝ) with hsdef
  have hs0 : 0 < s := by positivity
  have hr0 : 0 < r := hs0.trans_le hr
  set μ₁ : ℝ := 2 * (1 + √2) * κ * √r with hμ₁
  -- the means
  have hmean : 2 * (1 * κ * √(sNM n' m') + κ * Wave30tr.ek n' + κ * Wave30tr.ek m') ≤ μ₁ := by
    have h1 : √(sNM n' m') ≤ √r := Real.sqrt_le_sqrt hr
    have h2 : Wave30tr.ek n' + Wave30tr.ek m' ≤ √2 * √r := by
      calc Wave30tr.ek n' + Wave30tr.ek m' ≤ 1 / √(n' : ℝ) + 1 / √(m' : ℝ) :=
            add_le_add (StatFormal.Wave30tr.ek_le_inv_sqrt hn) (StatFormal.Wave30tr.ek_le_inv_sqrt hm)
        _ ≤ √2 * √s := inv_sqrt_add_le hnpos hmpos
        _ ≤ √2 * √r := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _)
    have : 2 * (1 * κ * √(sNM n' m') + κ * Wave30tr.ek n' + κ * Wave30tr.ek m') = 2 * κ * (√(sNM n' m') + (Wave30tr.ek n' + Wave30tr.ek m')) := by ring
    rw [this, hμ₁]
    have h3 : √(sNM n' m') + (Wave30tr.ek n' + Wave30tr.ek m') ≤ (1 + √2) * √r := by nlinarith
    nlinarith
  have hosc1 := osc_hOne (κ := κ) hDφ
  have hosc2 := osc_hTwo (κ := κ) hDφ
  rcases le_or_gt (τ - μ₁) 0 with hy | hy
  · rw [max_eq_right hy]
    have : Real.exp (-(2 * (0 : ℝ) ^ 2 / (Dφ ^ 2 * r))) = 1 := by simp
    rw [this, ENNReal.ofReal_one]
    exact ⟨prob_le_one, prob_le_one⟩
  · rw [max_eq_left hy.le]
    set y := τ - μ₁ with hydef
    set χ : ℝ := 2 * y ^ 2 / (Dφ ^ 2 * s) with hχdef
    have hχ : 0 < χ := by positivity
    obtain ⟨hT1, hT2⟩ := hinge_tail_strict 𝒳 H P Q φ κ hingePos hingePos 1 κ κ Dφ Dφ n' m' hφ hκ
      isHingeMap_hingePos isHingeMap_hingePos zero_le_one hκ0 hκ0 hn hm hosc1 hosc2 χ hχ
    have heps : √(χ * (Dφ ^ 2 / n' + Dφ ^ 2 / m') / 2) = y := by
      have : χ * (Dφ ^ 2 / n' + Dφ ^ 2 / m') / 2 = y ^ 2 := by
        rw [hχdef, hsdef]
        field_simp
      rw [this, Real.sqrt_sq hy.le]
    rw [heps] at hT1 hT2
    have hexp : Real.exp (-χ) ≤ Real.exp (-(2 * y ^ 2 / (Dφ ^ 2 * r))) := by
      refine Real.exp_le_exp.2 (neg_le_neg ?_)
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hr (by positivity))
    constructor
    · refine le_trans (measure_mono ?_) (hT1.trans (ENNReal.ofReal_le_ofReal hexp))
      intro z hz
      simp only [mem_ofPred_eq] at hz ⊢
      have : ∫ w, hingeZ P Q φ hingePos hingePos 1 κ κ w ∂(sampleLaw P Q n' m') + y ≤ τ := by
        rw [hydef]; linarith
      linarith
    · refine le_trans (measure_mono ?_) (hT2.trans (ENNReal.ofReal_le_ofReal hexp))
      intro z hz
      simp only [mem_ofPred_eq] at hz ⊢
      have : ∫ w, hingeZm P Q φ hingePos hingePos 1 κ κ w ∂(sampleLaw P Q n' m') + y ≤ τ := by
        rw [hydef]; linarith
      linarith

end Tail

/-! ### The fitting event: every batch gets a ramp with excess `≥ ϱ_*` -/

section Step

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable [CompleteSpace H]

/-- `D_φ > 0` when some `D_α > 0` (otherwise `φ` is constant and every region is `{φ x₀}`). -/
lemma dphi_pos (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {Dφ α : ℝ}
    (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hpos : 0 < Dpop φ P Q α) : 0 < Dφ := by
  by_contra hcon
  replace hcon := not_lt.1 hcon
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hc : ∀ x, φ x = φ x0 := fun x => sub_eq_zero.1 (norm_le_zero_iff.1 ((hDφ x x0).trans hcon))
  have h1 : (1 : ℝ) ≤ 1 / (1 - α) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hmem : ∀ μ : Measure 𝒳, IsProbabilityMeasure μ → φ x0 ∈ region φ α μ := by
    intro μ _
    refine ⟨fun _ => 1, measurable_const, fun _ => ⟨zero_le_one, h1⟩, by simp, ?_⟩
    have : ∫ x, (fun _ : 𝒳 => (1 : ℝ)) x • φ x ∂μ = ∫ _x, φ x0 ∂μ :=
      integral_congr_ae (ae_of_all _ fun x => by simp only [one_smul]; exact hc x)
    rw [this, integral_const, probReal_univ, one_smul]
  have := setDist_le_norm' (hmem P inferInstance) (hmem Q inferInstance)
  rw [sub_self, norm_zero] at this
  exact absurd hpos (not_lt.2 this)


/-- On `{Z ≤ τ_*, Z⁻ ≤ τ_*}`, at a level `α_j ≤ α_i` with `D_{α_j} ≥ d` and (S): the rule bets and the ramp has excess
`E_P g − E_Q g − α_j ≥ ϱ_* = d/(2β_* D_φ)`. -/
theorem witness_step (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ Dφ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) (hDφ0 : 0 < Dφ)
    {n' m' : ℕ} (hn : 1 ≤ n') (hm : 1 ≤ m') (xs : Fin n' → 𝒳) (ys : Fin m' → 𝒳)
    {αj αi d r : ℝ} (hαj0 : 0 ≤ αj) (hji : αj ≤ αi) (hαi1 : αi < 1) (hd : 0 < d)
    (hdD : d ≤ Dpop φ P Q αj)
    (hr : 1 / (n' : ℝ) + 1 / (m' : ℝ) ≤ r) (hS1 : beta αi * Dφ * r ≤ d / 8)
    (hS2 : beta αi ^ 2 * κ ^ 2 * r ≤ 7 * d ^ 2 / 64)
    (hZ : hingeZ P Q φ hingePos hingePos 1 κ κ (xs, ys) ≤ d / (8 * beta αi))
    (hZm : hingeZm P Q φ hingePos hingePos 1 κ κ (xs, ys) ≤ d / (8 * beta αi))
    {has : Prop} {g : 𝒳 → ℝ} (hW : IsWitnessRamp φ αj xs ys has g) :
    has ∧ αj + d / (2 * beta αi * Dφ) ≤ (∫ z, g z ∂P) - ∫ z, g z ∂Q := by
  obtain ⟨-, hW2⟩ := hW
  obtain ⟨w, v, hqp, -, hpos⟩ := hW2 hn hm
  set β := beta αi with hβdef
  set Z := hingeZ P Q φ hingePos hingePos 1 κ κ (xs, ys) with hZdef
  set Zm := hingeZm P Q φ hingePos hingePos 1 κ κ (xs, ys) with hZmdef
  have hαj1 : αj < 1 := hji.trans_lt hαi1
  have hβ1 : 1 ≤ β := one_le_beta (hαj0.trans hji) hαi1
  have hβj1 : 1 ≤ beta αj := one_le_beta hαj0 hαj1
  have hβj : beta αj ≤ β := by
    rw [hβdef]; unfold beta; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hZ0 : 0 ≤ Z := hingeZ_nonneg P Q hκ _
  have hZm0 : 0 ≤ Zm := hingeZm_nonneg' P Q hκ _
  have hβτ : β * (d / (8 * β)) = d / 8 := by field_simp
  have hβZm : β * Zm ≤ d / 8 := by
    calc β * Zm ≤ β * (d / (8 * β)) := mul_le_mul_of_nonneg_left hZm (by linarith)
      _ = d / 8 := hβτ
  have hβZ : β * Z ≤ d / 8 := by
    calc β * Z ≤ β * (d / (8 * β)) := mul_le_mul_of_nonneg_left hZ (by linarith)
      _ = d / 8 := hβτ
  have hβjZm : beta αj * Zm < Dpop φ P Q αj := by
    have : beta αj * Zm ≤ β * Zm := mul_le_mul_of_nonneg_right hβj hZm0
    linarith
  obtain ⟨-, hqpos, hcuts⟩ :=
    fitted_ramp_route 𝒳 H P Q φ κ Dφ αj n' m' xs ys w v hφ hκ hDφ hαj0 hαj1 hn hm hqp hβjZm
  obtain ⟨t, u, hC, hiff, hg⟩ := hpos hqpos
  obtain ⟨-, -, -, hΘpos⟩ := hcuts t u hC
  set s : ℝ := 1 / (n' : ℝ) + 1 / (m' : ℝ) with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hmono := theta_mono_route αj αi d (Dpop φ P Q αj) Z Zm κ Dφ s hαj0 hji hαi1 hZ0 hZm0 hDφ0.le hs0
    (by linarith) hdD
  -- `Θ(α_i, d) ≥ d/2`
  have hΘi : d / 2 ≤ fitTheta αi d Z Zm κ Dφ s := by
    unfold fitTheta
    have h1 : β * Dφ * s ≤ d / 8 := by
      have : β * Dφ * s ≤ β * Dφ * r := mul_le_mul_of_nonneg_left hr (by positivity)
      linarith
    have hden : 7 * d / 8 ≤ d - β * Zm := by linarith
    have hden0 : 0 < d - β * Zm := by linarith
    have h2 : β ^ 2 * κ ^ 2 * s / (d - β * Zm) ≤ d / 8 := by
      rw [div_le_iff₀ hden0]
      have : β ^ 2 * κ ^ 2 * s ≤ β ^ 2 * κ ^ 2 * r := mul_le_mul_of_nonneg_left hr (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hden (by linarith : (0 : ℝ) ≤ d / 8)]
    have h3 : β * (Z + Zm) ≤ d / 4 := by rw [mul_add]; linarith
    linarith
  set Θ := fitTheta αj (Dpop φ P Q αj) Z Zm κ Dφ s with hΘdef
  have hΘ : d / 2 ≤ Θ := hΘi.trans hmono
  obtain ⟨hut, hexc⟩ := hΘpos (by linarith)
  have hhas : has := hiff.2 hut
  refine ⟨hhas, ?_⟩
  rw [hg hhas]
  have hpos1 : 0 < beta αj * Dφ := by positivity
  have hle : d / (2 * β * Dφ) ≤ Θ / (beta αj * Dφ) := by
    rw [show d / (2 * β * Dφ) = (d / 2) / (β * Dφ) by ring]
    exact div_le_div₀ (by linarith) hΘ hpos1 (mul_le_mul_of_nonneg_right hβj hDφ0.le)
  linarith

end Step

/-! ### The fitting event and its probability -/

section Event

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `E_fit = {Z_b ≤ τ, Z⁻_b ≤ τ for the batch `b = bat k` of every pair `k`}`. -/
def fitEvent (P Q : Measure 𝒳) (φ : 𝒳 → H) (κ τ : ℝ) {n m N : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ)
    (bat : Fin N → ℕ) : Set ((Fin n → 𝒳) × (Fin m → 𝒳)) :=
  {ω | ∀ k : Fin N, hingeZ P Q φ hingePos hingePos 1 κ κ (fitPair lx ly (bat k) ω) ≤ τ ∧
    hingeZm P Q φ hingePos hingePos 1 κ κ (fitPair lx ly (bat k) ω) ≤ τ}

variable [TopologicalSpace.SeparableSpace H]

lemma measurableSet_fitEvent (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (τ : ℝ) {n m N : ℕ} {lx : Fin n → ℕ}
    {ly : Fin m → ℕ} {bat : Fin N → ℕ} (hfit1 : ∀ k, 1 ≤ fitCard lx (bat k) ∧ 1 ≤ fitCard ly (bat k)) :
    MeasurableSet (fitEvent P Q φ κ τ lx ly bat) := by
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
  have : fitEvent P Q φ κ τ lx ly bat = ⋂ k : Fin N,
      ({ω | hingeZ P Q φ hingePos hingePos 1 κ κ (fitPair lx ly (bat k) ω) ≤ τ} ∩
        {ω | hingeZm P Q φ hingePos hingePos 1 κ κ (fitPair lx ly (bat k) ω) ≤ τ}) := by
    ext ω; simp [fitEvent]
  rw [this]
  refine MeasurableSet.iInter fun k => ?_
  obtain ⟨hZm, hZmm, -⟩ := StatFormal.Wave30ty.hinge 𝒳 H P Q φ κ hingePos hingePos 1 κ κ _ _ hφ hκ
    isHingeMap_hingePos isHingeMap_hingePos zero_le_one hκ0 hκ0 (hfit1 k).1 (hfit1 k).2
  exact (measurableSet_le (hZm.comp (measurable_fitPair _ _ _)) measurable_const).inter
    (measurableSet_le (hZmm.comp (measurable_fitPair _ _ _)) measurable_const)

/-- `P(E_fitᶜ) ≤ 2B exp(−2(τ − μ₁)₊²/(D_φ² r))`: a union over the batches `b ∈ bat(Fin N) ⊆ [1, B]`. -/
theorem fitEvent_compl_le (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {κ Dφ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) (hDφ0 : 0 < Dφ)
    (τ r : ℝ) {n m N Bmax : ℕ} {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ}
    (hbat1 : ∀ k, 1 ≤ bat k) (hBmax : ∀ k, bat k ≤ Bmax)
    (hfit1 : ∀ k, 1 ≤ fitCard lx (bat k) ∧ 1 ≤ fitCard ly (bat k))
    (hfitr : ∀ k, 1 / (fitCard lx (bat k) : ℝ) + 1 / (fitCard ly (bat k) : ℝ) ≤ r) :
    sampleLaw P Q n m (fitEvent P Q φ κ τ lx ly bat)ᶜ ≤
      ENNReal.ofReal (2 * Bmax * Real.exp (-(2 * (max (τ - 2 * (1 + √2) * κ * √r) 0) ^ 2 / (Dφ ^ 2 * r)))) := by
  set e := Real.exp (-(2 * (max (τ - 2 * (1 + √2) * κ * √r) 0) ^ 2 / (Dφ ^ 2 * r))) with hedef
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  set S := Finset.univ.image bat with hS
  have hsub : (fitEvent P Q φ κ τ lx ly bat)ᶜ ⊆ ⋃ b ∈ S,
      (fitPair lx ly b ⁻¹' {z | τ < hingeZ P Q φ hingePos hingePos 1 κ κ z} ∪
        fitPair lx ly b ⁻¹' {z | τ < hingeZm P Q φ hingePos hingePos 1 κ κ z}) := by
    intro ω hω
    simp only [fitEvent, mem_compl_iff, mem_ofPred_eq, not_forall, not_and_or, not_le] at hω
    obtain ⟨k, hk⟩ := hω
    refine mem_iUnion₂.2 ⟨bat k, Finset.mem_image_of_mem _ (Finset.mem_univ k), ?_⟩
    rcases hk with hk | hk
    · exact Or.inl hk
    · exact Or.inr hk
  have hcard : S.card ≤ Bmax := by
    have : S ⊆ Finset.Icc 1 Bmax := by
      intro b hb
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hb
      exact Finset.mem_Icc.2 ⟨hbat1 k, hBmax k⟩
    simpa using Finset.card_le_card this
  calc sampleLaw P Q n m (fitEvent P Q φ κ τ lx ly bat)ᶜ ≤ ∑ b ∈ S, sampleLaw P Q n m
        (fitPair lx ly b ⁻¹' {z | τ < hingeZ P Q φ hingePos hingePos 1 κ κ z} ∪
          fitPair lx ly b ⁻¹' {z | τ < hingeZm P Q φ hingePos hingePos 1 κ κ z}) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ b ∈ S, (ENNReal.ofReal e + ENNReal.ofReal e) := by
        refine Finset.sum_le_sum fun b hb => ?_
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hb
        obtain ⟨hm1, hm2, hb1, hb2⟩ := fit_tail P Q hφ hκ hDφ hDφ0 (hfit1 k).1 (hfit1 k).2 (hfitr k) τ
        refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
        · rw [fitPair_apply P Q _ _ _ hm1]; exact hb1
        · rw [fitPair_apply P Q _ _ _ hm2]; exact hb2
    _ = S.card * (ENNReal.ofReal e + ENNReal.ofReal e) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Bmax * (ENNReal.ofReal e + ENNReal.ofReal e) := by gcongr
    _ = ENNReal.ofReal (2 * Bmax * e) := by
        rw [← ENNReal.ofReal_add he0 he0, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

end Event

/-! ### Betting on the fitting event -/

/-- The arithmetic of §5: Lemma 5's bound at level `α_j ≤ α_i` (with `λ̄ = λ̄_N(α_j)`, `a = λ_max ≤ 1/2`) is at most
`genEps` at `α_i`. -/
lemma bet_arith {N : ℕ} (hN : 1 ≤ N) {lmax s2 L αi αj lo ρ : ℝ} (hl0 : 0 < lmax) (hl12 : lmax ≤ 1 / 2)
    (hs2 : 0 < s2) (hL : 0 < L) (hαj0 : 0 ≤ αj) (hji : αj ≤ αi) :
    Real.exp (-(max (N * lo * ρ - 1 / (2 * (1 - lmax) ^ 2) * N * (lamHi lmax αj L s2 N) ^ 2 * (1 + αj) ^ 2 - L) 0) ^ 2 /
      (2 * N * (lamHi lmax αj L s2 N) ^ 2)) ≤ genEps s2 αi L N ρ lo := by
  set hi := lamHi lmax αj L s2 N with hhidef
  have h1αj : 0 < 1 + αj := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcap : 0 < lmax / (1 + αj) := div_pos hl0 h1αj
  have hq : 0 < √(2 * L / (N * s2)) := Real.sqrt_pos.2 (by positivity)
  have hhi0 : 0 < hi := lt_min hcap hq
  have hhiq : hi ≤ √(2 * L / (N * s2)) := min_le_right _ _
  have hNhi : (N : ℝ) * hi ^ 2 ≤ 2 * L / s2 := by
    have h1 : hi ^ 2 ≤ 2 * L / (N * s2) := by
      calc hi ^ 2 ≤ (√(2 * L / (N * s2))) ^ 2 := pow_le_pow_left₀ hhi0.le hhiq 2
        _ = 2 * L / (N * s2) := Real.sq_sqrt (by positivity)
    calc (N : ℝ) * hi ^ 2 ≤ N * (2 * L / (N * s2)) := mul_le_mul_of_nonneg_left h1 hNr.le
      _ = 2 * L / s2 := by field_simp
  have hC : 1 / (2 * (1 - lmax) ^ 2) ≤ 2 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have hαsq : (1 + αj) ^ 2 ≤ (1 + αi) ^ 2 := pow_le_pow_left₀ h1αj.le (by linarith) 2
  have hxy : (N : ℝ) * lo * ρ - L - 4 * L * (1 + αi) ^ 2 / s2 ≤
      N * lo * ρ - 1 / (2 * (1 - lmax) ^ 2) * N * hi ^ 2 * (1 + αj) ^ 2 - L := by
    have h2 : 1 / (2 * (1 - lmax) ^ 2) * N * hi ^ 2 * (1 + αj) ^ 2 ≤ 4 * L * (1 + αi) ^ 2 / s2 := by
      calc 1 / (2 * (1 - lmax) ^ 2) * N * hi ^ 2 * (1 + αj) ^ 2 =
            1 / (2 * (1 - lmax) ^ 2) * (N * hi ^ 2) * (1 + αj) ^ 2 := by ring
        _ ≤ 2 * (2 * L / s2) * (1 + αi) ^ 2 := by
            have h0 : (0 : ℝ) ≤ 1 / (2 * (1 - lmax) ^ 2) := by positivity
            have h00 : (0 : ℝ) ≤ N * hi ^ 2 := by positivity
            exact mul_le_mul (mul_le_mul hC hNhi h00 (by norm_num)) hαsq (by positivity) (by positivity)
        _ = 4 * L * (1 + αi) ^ 2 / s2 := by ring
    linarith
  have hden0 : (0 : ℝ) < 2 * N * hi ^ 2 := by positivity
  have hfrac' : s2 / (4 * L) ≤ 1 / (2 * N * hi ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) hden0, one_mul]
    have h1 := mul_le_mul_of_nonneg_left hNhi hs2.le
    rw [mul_div_cancel₀ _ hs2.ne'] at h1
    have e : s2 * (2 * N * hi ^ 2) = 2 * (s2 * (N * hi ^ 2)) := by ring
    rw [e]
    linarith
  unfold genEps
  exact Real.exp_le_exp.2 (Bet.exp_arg_le hxy (by positivity) hfrac')

section BetStep

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Lemma 5 on the fitting event at a level `α_j ≤ α_i`: every pair is bet on with `λ_k ≥ λ_N(α_i)` and excess `≥ ϱ_*`. -/
theorem bet_step (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ Dφ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ Dφ) (hDφ0 : 0 < Dφ)
    {J n m : ℕ} {α : Fin J → ℝ} {δ lmax s2 : ℝ} {R : LoRun 𝒳 J n m} {i j : Fin J} {d r : ℝ}
    (hgrid : IsGrid α) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hl0 : 0 < lmax) (hl12 : lmax ≤ 1 / 2) (hs2 : 0 < s2)
    (hRun : R.IsWitnessRun φ α δ lmax s2)
    (hfit1 : ∀ k, 1 ≤ fitCard R.lx (R.bat k) ∧ 1 ≤ fitCard R.ly (R.bat k))
    (hfitr : ∀ k, 1 / (fitCard R.lx (R.bat k) : ℝ) + 1 / (fitCard R.ly (R.bat k) : ℝ) ≤ r)
    (hd : 0 < d) (hdD : d ≤ Dpop φ P Q (α i))
    (hS1 : beta (α i) * Dφ * r ≤ d / 8) (hS2 : beta (α i) ^ 2 * κ ^ 2 * r ≤ 7 * d ^ 2 / 64)
    (hji : j ≤ i) (hN : 1 ≤ R.N)
    (hEm : MeasurableSet (fitEvent P Q φ κ (d / (8 * beta (α i))) R.lx R.ly R.bat)) :
    sampleLaw P Q n m (fitEvent P Q φ κ (d / (8 * beta (α i))) R.lx R.ly R.bat ∩
        {ω | ¬ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2}) ≤
      ENNReal.ofReal (genEps s2 (α i) (Real.log (1 / δ)) R.N (d / (2 * beta (α i) * Dφ))
        (lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N)) := by
  obtain ⟨⟨hpair, hfit, hfrac⟩, hwit, hlam⟩ := hRun
  have hL : 0 < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  have hαi0 : 0 ≤ α i := (hgrid.2 i).1
  have hαi1 : α i < 1 := (hgrid.2 i).2
  have hβ1 : 1 ≤ beta (α i) := one_le_beta hαi0 hαi1
  have hϱ : 0 < d / (2 * beta (α i) * Dφ) := by positivity
  have hαji : α j ≤ α i := hgrid.1.monotone hji
  have hαj0 : 0 ≤ α j := (hgrid.2 j).1
  have h1αj : 0 < 1 + α j := by linarith
  have hhicap : lamHi lmax (α j) (Real.log (1 / δ)) s2 R.N ≤ lmax / (1 + α j) := min_le_left _ _
  have hha : lamHi lmax (α j) (Real.log (1 / δ)) s2 R.N * (1 + α j) ≤ lmax := by
    rwa [le_div_iff₀ h1αj] at hhicap
  have hlo0 : 0 ≤ lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N :=
    le_min (div_pos hl0 (by linarith)).le (Real.sqrt_nonneg _)
  have hlolo : lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N ≤ lamLo lmax (α j) (Real.log (1 / δ)) s2 R.N :=
    min_le_min (div_le_div_of_nonneg_left hl0.le h1αj (by linarith)) le_rfl
  have hE : ∀ ω ∈ fitEvent P Q φ κ (d / (8 * beta (α i))) R.lx R.ly R.bat, ∀ k : Fin R.N,
      lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N ≤ fracAt (R.lam j) (R.g j) R.bat R.A R.B ω.1 ω.2 k ∧
      α j + d / (2 * beta (α i) * Dφ) ≤ condMean P Q (R.g j) R.bat ω.1 ω.2 k := by
    intro ω hω k
    obtain ⟨hZk, hZmk⟩ := hω k
    obtain ⟨hhas, hexc⟩ := witness_step P Q hφ hκ hDφ hDφ0 (hfit1 k).1 (hfit1 k).2
      (fitSample R.lx (R.bat k) ω.1) (fitSample R.ly (R.bat k) ω.2) hαj0 hαji hαi1 hd
      (hdD.trans (dpop_antitone 𝒳 H φ κ P Q (α j) (α i) hφ hκ hαj0 hαji hαi1)) (hfitr k) hS1 hS2 hZk hZmk
      (hwit j k ω.1 ω.2)
    exact ⟨hlolo.trans ((hlam j k ω.1 ω.2 (past (pairStat (R.g j) R.bat R.A R.B ω.1 ω.2) k)).2.1 hhas
      fun l => Bet.pairStat_mem hpair (hfit j) (Fin.castLE k.isLt.le l) ω.1 ω.2), hexc⟩
  refine (bet_power_route 𝒳 P Q n m R.N R.lx R.ly R.bat R.A R.B (α j) δ lmax
    (lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N) (lamHi lmax (α j) (Real.log (1 / δ)) s2 R.N) lmax
    (d / (2 * beta (α i) * Dφ)) (R.g j) (R.lam j) _ hpair hαj0 hδ0 hδ1 hl0 (by linarith) (hfit j) (hfrac j)
    (fun k x y z => (hlam j k x y z).1) hha (by linarith) hlo0 hϱ hEm hE).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact bet_arith hN hl0 hl12 hs2 hL hαj0 hαji

end BetStep

end Lower

open Lower Bet in
/-- **Proposition 1 (1), lower side** (§5), for every floor `σ²_min > 0` and with the general lower fraction `λ_N`. -/
theorem core_lower_bound : Iface.CoreLowerBound := by
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ J n m α δ lmax s2 R Bmax i d r hφ hκ hDφ hgrid hδ0 hδ1 hl0 hl12 hs2
    hRun hBmax hfit1 hfitr hd hdD hS1 hS2
  have hαi0 : 0 ≤ α i := (hgrid.2 i).1
  have hαi1 : α i < 1 := (hgrid.2 i).2
  have hDφ0 : 0 < Dφ := dphi_pos P Q hDφ hαi0 hαi1 (hd.trans_le hdD)
  have hL : 0 < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  set e := Real.exp (-(2 * (max (d / (8 * beta (α i)) - 2 * (1 + √2) * κ * √r) 0) ^ 2 / (Dφ ^ 2 * r))) with hedef
  set G := genEps s2 (α i) (Real.log (1 / δ)) R.N (d / (2 * beta (α i) * Dφ))
    (lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N) with hGdef
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hG0 : 0 ≤ G := (Real.exp_pos _).le
  have hJ : (1 : ℝ) ≤ J := Nat.one_le_cast.2 (Fin.pos i)
  -- the trivial case: `genEps = 1`
  by_cases hy : (R.N : ℝ) * lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N * (d / (2 * beta (α i) * Dφ)) -
      Real.log (1 / δ) - 4 * Real.log (1 / δ) * (1 + α i) ^ 2 / s2 ≤ 0
  · have hG1 : G = 1 := by
      rw [hGdef]; unfold genEps; rw [max_eq_right hy]; simp
    calc sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < α i} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hG1]
        have : 0 ≤ 2 * (Bmax : ℝ) * e := by positivity
        linarith
  replace hy := not_le.1 hy
  have hN : 1 ≤ R.N := by
    rcases Nat.eq_zero_or_pos R.N with h0 | h0
    · exfalso
      have h0' : (R.N : ℝ) = 0 := by exact_mod_cast h0
      rw [h0'] at hy
      have : 0 ≤ 4 * Real.log (1 / δ) * (1 + α i) ^ 2 / s2 := by positivity
      linarith
    · exact h0
  set Efit := fitEvent P Q φ κ (d / (8 * beta (α i))) R.lx R.ly R.bat with hEdef
  have hEm : MeasurableSet Efit := measurableSet_fitEvent P Q hφ hκ _ hfit1
  have hfitP : sampleLaw P Q n m Efitᶜ ≤ ENNReal.ofReal (2 * Bmax * e) :=
    fitEvent_compl_le P Q hφ hκ hDφ hDφ0 _ r hRun.1.1.2.2.1 hBmax hfit1 hfitr
  have hbet : ∀ j : Fin J, j ≤ i → sampleLaw P Q n m
      (Efit ∩ {ω | ¬ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2}) ≤ ENNReal.ofReal G :=
    fun j hji => bet_step P Q hφ hκ hDφ hDφ0 hgrid hδ0 hδ1 hl0 hl12 hs2 hRun hfit1 hfitr hd hdD hS1 hS2 hji hN hEm
  -- the down-closed rule and the union bound
  set T := Finset.univ.filter fun j : Fin J => j ≤ i with hT
  have hsub : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | R.alphaLo α δ ω.1 ω.2 < α i} ⊆
      Efitᶜ ∪ ⋃ j ∈ T, (Efit ∩ {ω | ¬ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2}) := by
    intro ω hω
    obtain ⟨j, hj, hnr⟩ := (grid_events_route J α
      (fun j => rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2) 0 hgrid).2 i hω
    by_cases hωE : ω ∈ Efit
    · exact Or.inr (mem_iUnion₂.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, hωE, hnr⟩)
    · exact Or.inl hωE
  have hTcard : T.card ≤ J := (Finset.card_filter_le _ _).trans (by simp)
  calc sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < α i} ≤ sampleLaw P Q n m Efitᶜ + sampleLaw P Q n m
        (⋃ j ∈ T, (Efit ∩ {ω | ¬ rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2})) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (2 * Bmax * e) + ∑ j ∈ T, ENNReal.ofReal G :=
        add_le_add hfitP ((measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun j hj => hbet j (Finset.mem_filter.1 hj).2))
    _ = ENNReal.ofReal (2 * Bmax * e) + T.card * ENNReal.ofReal G := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (2 * Bmax * e) + J * ENNReal.ofReal G :=
        by gcongr
    _ = ENNReal.ofReal (2 * Bmax * e + J * G) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- **Proposition 1 (1), lower side**, the explicit bound of §5 (`σ²_min ≤ 4`, `N ≥ L(1+α_i)²/(2λ_max²)`). -/
theorem lo_lower_bound_route : Claims.lo_lower_bound := by
  intro 𝒳 H _ _ _ _ _ φ κ Dφ P Q _ _ J n m α δ lmax s2 R Bmax i d r hφ hκ hDφ hgrid hδ0 hδ1 hl0 hl12 hs20 hs24
    hRun hBmax hfit1 hfitr hd hdD hS1 hS2 hNL
  have h := core_lower_bound 𝒳 H φ κ Dφ P Q J n m α δ lmax s2 R Bmax i d r hφ hκ hDφ hgrid hδ0 hδ1 hl0 hl12 hs20
    hRun hBmax hfit1 hfitr hd hdD hS1 hS2
  have hL : 0 < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  set L := Real.log (1 / δ) with hLdef
  have h1α : 0 < 1 + α i := by linarith [(hgrid.2 i).1]
  have hN : (0 : ℝ) < R.N := lt_of_lt_of_le (by positivity) hNL
  set lo := lamLo lmax (α i) L s2 R.N with hlodef
  have hcap : 0 < lmax / (1 + α i) := div_pos hl0 h1α
  have hlo_eq : lo = √(2 * L / (R.N * 4)) := by
    have hmax : max s2 4 = 4 := max_eq_right hs24
    have hsq : 2 * L / (R.N * 4) ≤ (lmax / (1 + α i)) ^ 2 := by
      have hNL' := hNL
      rw [div_le_iff₀ (by positivity)] at hNL'
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [hlodef]
    change min (lmax / (1 + α i)) (√(2 * L / (R.N * max s2 4))) = √(2 * L / (R.N * 4))
    rw [hmax]
    apply min_eq_right
    calc √(2 * L / (R.N * 4)) ≤ √((lmax / (1 + α i)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = lmax / (1 + α i) := Real.sqrt_sq hcap.le
  have hNlo : (R.N : ℝ) * lo = √(R.N * L / 2) := by
    rw [hlo_eq, show (R.N : ℝ) * L / 2 = R.N ^ 2 * (2 * L / (R.N * 4)) by field_simp; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hN.le]
  have hG : genEps s2 (α i) L R.N (d / (2 * beta (α i) * Dφ)) lo =
      epsN s2 (α i) L R.N (d / (2 * beta (α i) * Dφ)) := by
    unfold genEps epsN
    rw [show (R.N : ℝ) * lo * (d / (2 * beta (α i) * Dφ)) = d / (2 * beta (α i) * Dφ) * √(R.N * L / 2) by
      rw [← hNlo]; ring]
  rw [hG] at h
  exact h

end StatFormal.Wave30tz
