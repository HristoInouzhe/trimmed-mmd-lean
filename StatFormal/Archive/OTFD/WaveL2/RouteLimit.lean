import StatFormal.Archive.OTFD.WaveL2.RouteCM
import StatFormal.Archive.OTFD.WaveL2.RouteED
import StatFormal.Lib.OTLimits.Quadratic
import TauCeti.Probability.Process.EmpiricalMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Route (wave L2): `𝖤_N → 𝓔_K` (otfd A `thm:rt-fixedK`), deterministic core (untrusted)

Labelled pooled points `(z_a, β_a) ∈ ℝ^K × Bool` (`β_a = true` for group `P`). The plan of an optimal assignment,
`π_N = N⁻¹ Σ_a δ_{((z_a, β_a), u_{σ a})}`, couples the labelled empirical law `Λ̃_N` with the grid law `μ_N`; its
support is cyclically monotone for `c((x, β), y) = ‖x − y‖²/2` (`RouteCM`), so it is optimal (Schachermayer–Teichmann,
Tau Ceti). The limit problem `(Λ̃, μ)`, `Λ̃ = θ P⊗δ_true + (1−θ) Q⊗δ_false`, has the unique optimal plan
`(id, F ∘ fst)#Λ̃`: an optimal plan projects to a plan of `(Λ, μ)` on a cyclically monotone closed set, which is the
Brenier plan (Tau Ceti uniqueness). Villani 5.20 (library `tendsto_of_forall_isOptimalCoupling_eq`) gives
`π_N → (id, F ∘ fst)#Λ̃`, hence `π_N ⊗ π_N` converges (Mathlib `continuous_prod`), and `𝖤_N` is a combination of
integrals of bounded continuous functions of `π_N ⊗ π_N` (the label indicators are continuous on `Bool`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction

namespace StatFormal.OTFD.WaveL2

open StatFormal.OTFD.Ranks (IsMin cost)
open StatFormal.OTFD.Wave22a (mix energyD IsConvGradAE)
open TauCeti.Probability (empiricalMeasureOfFintype empiricalMeasureOfFintype_toMeasure
  empiricalMeasureOfFintype_apply integral_empiricalMeasureOfFintype lintegral_empiricalMeasureOfFintype)

/-! ### Empirical measures -/

section Emp

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {κ : Type*} [Fintype κ] [Nonempty κ]

theorem map_emp (x : κ → α) {g : α → β} (hg : Measurable g) :
    (empiricalMeasureOfFintype x : Measure α).map g = (empiricalMeasureOfFintype (g ∘ x) : Measure β) := by
  ext s hs
  rw [Measure.map_apply hg hs, empiricalMeasureOfFintype_apply (hg hs), empiricalMeasureOfFintype_apply hs]
  congr 1

theorem emp_comp_perm (x : κ → α) (σ : Equiv.Perm κ) :
    (empiricalMeasureOfFintype (x ∘ σ) : Measure α) = (empiricalMeasureOfFintype x : Measure α) := by
  ext s hs
  rw [empiricalMeasureOfFintype_apply hs, empiricalMeasureOfFintype_apply hs]
  congr 1
  exact Equiv.sum_comp σ (fun i => s.indicator (1 : α → ℝ≥0∞) (x i))

theorem emp_compl_range [MeasurableSingletonClass α] (x : κ → α) :
    (empiricalMeasureOfFintype x : Measure α) (range x)ᶜ = 0 := by
  have hm : MeasurableSet (range x)ᶜ := (Set.finite_range x).measurableSet.compl
  rw [empiricalMeasureOfFintype_apply hm]
  simp

end Emp

/-! ### Cyclical monotonicity of the assignment plan -/

section CMPoint

variable {X Y : Type*} [NormedAddCommGroup Y]

theorem isCM_assign {N : ℕ} (κ : X → Y → ℝ) (hκ : ∀ x y, 0 ≤ κ x y) (z : Fin N → X) (y : Fin N → Y)
    (hopt : ∀ π : Equiv.Perm (Fin N), ∑ a, κ (z a) (y a) ≤ ∑ a, κ (z a) (y (π a))) :
    IsCyclicallyMonotone (fun w : X × Y => ENNReal.ofReal (κ w.1 w.2)) (range fun a => (z a, y a)) := by
  intro n xs ys hmem ρ
  choose i hi using hmem
  have hx : ∀ k, xs k = z (i k) := fun k => (congrArg Prod.fst (hi k)).symm
  have hy : ∀ k, ys k = y (i k) := fun k => (congrArg Prod.snd (hi k)).symm
  have key := sum_le_sum_perm_of_opt (fun a b => κ (z a) (y b)) hopt i ρ
  simp only [hx, hy]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hκ _ _), ← ENNReal.ofReal_sum_of_nonneg (fun k _ => hκ _ _)]
  exact ENNReal.ofReal_le_ofReal key

end CMPoint

/-! ### Labelled empirical measures and their limits -/

section Core

variable {K : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin K)

/-- Group labels: `true` on the first `n₁` indices. -/
def lab (n₁ n₂ : ℕ) : Fin (n₁ + n₂) → Bool := Fin.append (fun _ => true) (fun _ => false)

@[simp] theorem lab_castAdd (n₁ n₂ : ℕ) (i : Fin n₁) : lab n₁ n₂ (Fin.castAdd n₂ i) = true := by
  simp [lab]

@[simp] theorem lab_natAdd (n₁ n₂ : ℕ) (j : Fin n₂) : lab n₁ n₂ (Fin.natAdd n₁ j) = false := by
  simp [lab]

/-- The labelled pooled law `Λ̃ = θ P⊗δ_true + (1−θ) Q⊗δ_false`. -/
def mixB (θ : ℝ) (P Q : Measure 𝔼) : Measure (𝔼 × Bool) :=
  mix θ (P.map fun x => (x, true)) (Q.map fun x => (x, false))

theorem integral_emp_lab {n₁ n₂ : ℕ} [Nonempty (Fin (n₁ + n₂))] (z : Fin (n₁ + n₂) → 𝔼) (f : (𝔼 × Bool) →ᵇ ℝ) :
    ∫ w, f w ∂(empiricalMeasureOfFintype (fun a => (z a, lab n₁ n₂ a)) : Measure (𝔼 × Bool)) =
      ((n₁ + n₂ : ℕ) : ℝ)⁻¹ * (∑ i : Fin n₁, f (z (Fin.castAdd n₂ i), true) +
        ∑ j : Fin n₂, f (z (Fin.natAdd n₁ j), false)) := by
  rw [integral_empiricalMeasureOfFintype f.continuous.stronglyMeasurable, Fintype.card_fin, smul_eq_mul,
    Fin.sum_univ_add]
  simp

theorem integral_mixB {θ : ℝ} {P Q : Measure 𝔼} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) {f : 𝔼 × Bool → ℝ} (hf : Continuous f) (hb : ∃ C, ∀ w, |f w| ≤ C) :
    ∫ w, f w ∂(mixB θ P Q) = θ * ∫ x, f (x, true) ∂P + (1 - θ) * ∫ x, f (x, false) ∂Q := by
  obtain ⟨C, hC⟩ := hb
  have hm1 : Measurable fun x : 𝔼 => (x, true) := measurable_id.prodMk measurable_const
  have hm2 : Measurable fun x : 𝔼 => (x, false) := measurable_id.prodMk measurable_const
  have hint : ∀ (m : Measure (𝔼 × Bool)) [IsFiniteMeasure m], Integrable f m := fun m _ =>
    Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun w => by
      simpa [Real.norm_eq_abs] using hC w)
  unfold mixB mix
  rw [integral_add_measure ((hint _).smul_measure ENNReal.ofReal_ne_top)
      ((hint _).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    integral_map hm1.aemeasurable hf.aestronglyMeasurable, integral_map hm2.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hθ, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

theorem isProb_mixB {θ : ℝ} {P Q : Measure 𝔼} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) : IsProbabilityMeasure (mixB θ P Q) :=
  isProbabilityMeasure_mix _ _ hθ hθ1

/-- `Λ̃` as a probability measure. -/
def mixBP {θ : ℝ} (P Q : Measure 𝔼) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hθ : 0 ≤ θ)
    (hθ1 : θ ≤ 1) : ProbabilityMeasure (𝔼 × Bool) :=
  ⟨mixB θ P Q, isProb_mixB hθ hθ1⟩

@[simp] theorem mixBP_toMeasure {θ : ℝ} (P Q : Measure 𝔼) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) : (mixBP P Q hθ hθ1 : Measure (𝔼 × Bool)) = mixB θ P Q := rfl

/-- Weak convergence of the labelled pooled empirical measures. -/
theorem tendsto_emp_lab {θ : ℝ} {P Q : Measure 𝔼} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) {n₁ n₂ : ℕ → ℕ} (h1 : ∀ ν, 0 < n₁ ν) (h2 : ∀ ν, 0 < n₂ ν)
    [∀ ν, Nonempty (Fin (n₁ ν + n₂ ν))]
    (hratio : Tendsto (fun ν => (n₁ ν : ℝ) / (n₁ ν + n₂ ν)) atTop (𝓝 θ))
    (z : ∀ ν, Fin (n₁ ν + n₂ ν) → 𝔼)
    (hzP : ∀ f : 𝔼 →ᵇ ℝ, Tendsto (fun ν => (n₁ ν : ℝ)⁻¹ * ∑ i : Fin (n₁ ν), f (z ν (Fin.castAdd (n₂ ν) i)))
      atTop (𝓝 (∫ x, f x ∂P)))
    (hzQ : ∀ f : 𝔼 →ᵇ ℝ, Tendsto (fun ν => (n₂ ν : ℝ)⁻¹ * ∑ j : Fin (n₂ ν), f (z ν (Fin.natAdd (n₁ ν) j)))
      atTop (𝓝 (∫ x, f x ∂Q))) :
    Tendsto (fun ν => empiricalMeasureOfFintype (fun a => (z ν a, lab (n₁ ν) (n₂ ν) a))) atTop
      (𝓝 (mixBP P Q hθ hθ1)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  set ft : 𝔼 →ᵇ ℝ := f.compContinuous ⟨fun x => (x, true), by fun_prop⟩
  set ff : 𝔼 →ᵇ ℝ := f.compContinuous ⟨fun x => (x, false), by fun_prop⟩
  have hratio' : Tendsto (fun ν => (n₂ ν : ℝ) / (n₁ ν + n₂ ν)) atTop (𝓝 (1 - θ)) := by
    refine (tendsto_const_nhds.sub hratio).congr' (Eventually.of_forall fun ν => ?_)
    have : (0 : ℝ) < n₁ ν + n₂ ν := by have := h1 ν; positivity
    field_simp; ring
  have hlim := (hratio.mul (hzP ft)).add (hratio'.mul (hzQ ff))
  have hval : ∫ w, f w ∂(mixB θ P Q) = θ * ∫ x, ft x ∂P + (1 - θ) * ∫ x, ff x ∂Q :=
    integral_mixB hθ hθ1 f.continuous ⟨‖f‖, fun w => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm w⟩
  rw [mixBP_toMeasure, hval]
  refine hlim.congr' (Eventually.of_forall fun ν => ?_)
  simp only
  rw [integral_emp_lab]
  have hn1 : (n₁ ν : ℝ) ≠ 0 := by have := h1 ν; positivity
  have hn2 : (n₂ ν : ℝ) ≠ 0 := by have := h2 ν; positivity
  have : (0 : ℝ) < n₁ ν + n₂ ν := by have := h1 ν; positivity
  simp only [ft, ff, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, Nat.cast_add]
  field_simp

/-- A probability measure packaged. -/
def toPM {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] : ProbabilityMeasure α :=
  ⟨μ, inferInstance⟩

@[simp] theorem toPM_toMeasure {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    (toPM μ : Measure α) = μ := rfl

theorem tendsto_emp_grid {N : ℕ → ℕ} [∀ ν, Nonempty (Fin (N ν))] {μ : Measure 𝔼} [IsProbabilityMeasure μ]
    (u : ∀ ν, Fin (N ν) → 𝔼)
    (hgrid : ∀ f : 𝔼 →ᵇ ℝ, Tendsto (fun ν => ((N ν : ℕ) : ℝ)⁻¹ * ∑ i, f (u ν i)) atTop (𝓝 (∫ x, f x ∂μ))) :
    Tendsto (fun ν => empiricalMeasureOfFintype (u ν)) atTop (𝓝 (toPM μ)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  refine (hgrid f).congr' (Eventually.of_forall fun ν => ?_)
  dsimp only
  rw [integral_empiricalMeasureOfFintype f.continuous.stronglyMeasurable, Fintype.card_fin, smul_eq_mul]

/-- The quadratic cost on labelled points, `c((x, β), y) = ‖x − y‖²/2`. -/
def costB (w : (𝔼 × Bool) × 𝔼) : ℝ≥0∞ := ENNReal.ofReal (‖w.1.1 - w.2‖ ^ 2 / 2)

theorem continuous_costB : Continuous (costB (K := K)) :=
  ENNReal.continuous_ofReal.comp ((((continuous_fst.comp continuous_fst).sub continuous_snd).norm.pow 2).div_const 2)

/-- The plan of an optimal assignment is an optimal coupling, of finite cost. -/
theorem plan_isOptimal {n : ℕ} [Nonempty (Fin n)] (x : Fin n → 𝔼 × Bool) (u : Fin n → 𝔼)
    (σ : Equiv.Perm (Fin n)) (hσ : IsMin u (fun a => (x a).1) σ) :
    IsOptimalCoupling costB (empiricalMeasureOfFintype (fun a => (x a, u (σ a))) : Measure ((𝔼 × Bool) × 𝔼))
      (empiricalMeasureOfFintype x : Measure (𝔼 × Bool)) (empiricalMeasureOfFintype u : Measure 𝔼) ∧
    transportCost costB (empiricalMeasureOfFintype x : Measure (𝔼 × Bool))
      (empiricalMeasureOfFintype u : Measure 𝔼) ≠ ⊤ := by
  set pts : Fin n → (𝔼 × Bool) × 𝔼 := fun a => (x a, u (σ a))
  have hcoup : IsCoupling (empiricalMeasureOfFintype pts : Measure ((𝔼 × Bool) × 𝔼))
      (empiricalMeasureOfFintype x) (empiricalMeasureOfFintype u) := by
    constructor
    · rw [Measure.fst, map_emp _ measurable_fst]; rfl
    · rw [Measure.snd, map_emp _ measurable_snd]
      exact emp_comp_perm u σ
  have hopt : ∀ π : Equiv.Perm (Fin n), ∑ a, ‖(x a).1 - u (σ a)‖ ^ 2 / 2 ≤
      ∑ a, ‖(x a).1 - u (σ (π a))‖ ^ 2 / 2 := by
    intro π
    rw [← Finset.sum_div, ← Finset.sum_div]
    have := hσ (σ * π)
    unfold cost at this
    exact div_le_div_of_nonneg_right this (by norm_num)
  have hS := isCM_assign (X := 𝔼 × Bool) (Y := 𝔼) (fun xb y => ‖xb.1 - y‖ ^ 2 / 2) (fun _ _ => by positivity)
    x (u ∘ σ) hopt
  have hπS : ∀ᵐ w ∂(empiricalMeasureOfFintype pts : Measure ((𝔼 × Bool) × 𝔼)), w ∈ range pts :=
    ae_iff.2 (emp_compl_range pts)
  refine ⟨hcoup.isOptimalCoupling_of_isCyclicallyMonotone continuous_costB.measurable
    (fun _ => ENNReal.ofReal_ne_top) hS hπS, ?_⟩
  refine ne_top_of_le_ne_top ?_ (transportCost_le_lintegral hcoup costB)
  rw [lintegral_empiricalMeasureOfFintype continuous_costB.measurable]
  exact ENNReal.mul_ne_top (by simp [Nat.pos_iff_ne_zero.1 (Fin.pos_iff_nonempty.2 ‹_›)])
    (ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top)

/-- Finite second moment as a lower integral. -/
theorem lintegral_sq_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → 𝔼} (h : MemLp f 2 μ) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ∞ := by
  have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) (by norm_num) (by norm_num) h.eLpNorm_lt_top
  simpa using this.ne

theorem map_fst_mixB {θ : ℝ} (P Q : Measure 𝔼) : (mixB θ P Q).map Prod.fst = mix θ P Q := by
  have h1 : Measurable fun x : 𝔼 => (x, true) := by fun_prop
  have h2 : Measurable fun x : 𝔼 => (x, false) := by fun_prop
  unfold mixB mix
  rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
    Measure.map_map measurable_fst h1, Measure.map_map measurable_fst h2]
  · simp [Function.comp_def]
  · exact measurable_fst.aemeasurable
  · exact measurable_fst.aemeasurable

theorem lintegral_mixB_fst {θ : ℝ} (P Q : Measure 𝔼) {g : 𝔼 → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ w, g w.1 ∂(mixB θ P Q) = ∫⁻ x, g x ∂(mix θ P Q) := by
  rw [← map_fst_mixB, lintegral_map hg measurable_fst]

/-- **Uniqueness of the labelled limit plan.** -/
theorem unique_opt_mixB {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (P Q μ : Measure 𝔼) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure μ] (hP2 : MemLp id 2 P) (hQ2 : MemLp id 2 Q)
    (hμ2 : MemLp id 2 μ) (hac : mix θ P Q ≪ volume) {F : 𝔼 → 𝔼} (hF : Measurable F)
    (hpush : (mix θ P Q).map F = μ) (hgrad : IsConvGradAE (mix θ P Q) F) :
    transportCost costB (mixB θ P Q) μ ≠ ⊤ ∧
      ∀ γ : Measure ((𝔼 × Bool) × 𝔼), IsOptimalCoupling costB γ (mixB θ P Q) μ →
        γ = (mixB θ P Q).map fun w => (w, F w.1) := by
  have := isProb_mixB (P := P) (Q := Q) hθ.le hθ1.le
  have := isProbabilityMeasure_mix P Q hθ.le hθ1.le
  set Λ := mix θ P Q
  set Λt := mixB θ P Q
  have hΛ2 : MemLp id 2 Λ := memLp_mix hP2 hQ2
  have hc : Continuous fun z : 𝔼 × 𝔼 => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) :=
    ENNReal.continuous_ofReal.comp (((continuous_fst.sub continuous_snd).norm.pow 2).div_const 2)
  -- finiteness of the labelled cost
  have hfin : transportCost costB Λt μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (StatFormal.OTLimits.transportCost_le_add
      (a := fun w : 𝔼 × Bool => ‖w.1‖ₑ ^ 2) (b := fun y : 𝔼 => ‖y‖ₑ ^ 2)
      (fun w => StatFormal.OTLimits.quadCost_le (w.1.1, w.2))
      (StatFormal.OTLimits.continuous_enorm_sq.measurable.comp measurable_fst)
      StatFormal.OTLimits.continuous_enorm_sq.measurable Λt μ)
    rw [lintegral_mixB_fst P Q StatFormal.OTLimits.continuous_enorm_sq.measurable]
    exact ENNReal.add_ne_top.2 ⟨lintegral_sq_ne_top hΛ2, lintegral_sq_ne_top hμ2⟩
  refine ⟨hfin, fun γ hγ => ?_⟩
  have hcmγ : IsCyclicallyMonotone costB γ.support := hγ.isCyclicallyMonotone_support continuous_costB hfin
  set S' : Set (𝔼 × 𝔼) :=
    {p | ((p.1, true), p.2) ∈ γ.support} ∪ {p | ((p.1, false), p.2) ∈ γ.support}
  have hS'c : IsClosed S' :=
    ((Measure.isClosed_support (μ := γ)).preimage (by fun_prop)).union
      ((Measure.isClosed_support (μ := γ)).preimage (by fun_prop))
  have hS'cm : IsCyclicallyMonotone (fun z : 𝔼 × 𝔼 => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) S' := by
    intro n xs ys hmem ρ
    have hb : ∀ k, ∃ b : Bool, ((xs k, b), ys k) ∈ γ.support := fun k => by
      rcases hmem k with h | h
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
    choose b hb using hb
    exact hcmγ n (fun k => (xs k, b k)) ys hb ρ
  set proj : (𝔼 × Bool) × 𝔼 → 𝔼 × 𝔼 := fun w => (w.1.1, w.2)
  have hproj : Measurable proj := by fun_prop
  set γ' := γ.map proj
  have hγfst : γ.map Prod.fst = Λt := hγ.toIsCoupling.fst_eq
  have hγsnd : γ.map Prod.snd = μ := hγ.toIsCoupling.snd_eq
  have hcoup' : IsCoupling γ' Λ μ := by
    constructor
    · change (γ.map proj).map Prod.fst = Λ
      rw [Measure.map_map measurable_fst hproj]
      have : (Prod.fst ∘ proj) = Prod.fst ∘ Prod.fst := rfl
      rw [this, ← Measure.map_map measurable_fst measurable_fst, hγfst, map_fst_mixB]
    · change (γ.map proj).map Prod.snd = μ
      rw [Measure.map_map measurable_snd hproj]
      exact hγsnd
  have hγ'S : ∀ᵐ p ∂γ', p ∈ S' := by
    refine (ae_map_iff hproj.aemeasurable hS'c.measurableSet).2 ?_
    filter_upwards [γ.support_mem_ae] with w hw
    rcases w with ⟨⟨x, b⟩, y⟩
    cases b
    · exact Or.inr hw
    · exact Or.inl hw
  have hopt' := hcoup'.isOptimalCoupling_of_isCyclicallyMonotone hc.measurable
    (fun _ => ENNReal.ofReal_ne_top) hS'cm hγ'S
  obtain ⟨φ, hφ, hgF⟩ := hgrad
  have hlawF : HasLaw F μ Λ := ⟨hF.aemeasurable, hpush⟩
  have hoptF := TauCeti.isKantorovichOptimalTransportMap_of_ae_mem_subdifferential hΛ2 hμ2 hlawF
    (hgF.mono fun x hx => StatFormal.OTFD.Wave22a.grad_mem_subdiff hφ hx)
  have hcoupF := (TauCeti.isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hlawF
    hc.measurable.aemeasurable).1 hoptF
  have hfinΛ : TauCeti.transportCost (fun z : 𝔼 × 𝔼 => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) Λ μ ≠ ⊤ := by
    rw [← hcoupF.lintegral_eq,
      (TauCeti.isCoupling_graphPlan hlawF).lintegral_norm_sub_sq_div_two hΛ2 hμ2]
    exact ENNReal.ofReal_ne_top
  have heq : γ' = graphPlan F Λ := hopt'.unique hac hcoupF hfinΛ
  have hmeasNe : MeasurableSet {p : 𝔼 × 𝔼 | p.2 ≠ F p.1} :=
    (measurableSet_eq_fun measurable_snd (hF.comp measurable_fst)).compl
  have hnull' : γ' {p | p.2 ≠ F p.1} = 0 := by
    rw [heq, graphPlan_apply hF.aemeasurable hmeasNe]; simp
  have hae : ∀ᵐ w ∂γ, w.2 = (F ∘ Prod.fst) w.1 := by
    have : γ (proj ⁻¹' {p | p.2 ≠ F p.1}) = 0 := by
      rw [← Measure.map_apply hproj hmeasNe]; exact hnull'
    exact ae_iff.2 this
  calc γ = graphPlan (F ∘ Prod.fst) (γ.map Prod.fst) :=
        eq_graphPlan_of_ae_snd_eq (hF.comp measurable_fst).aemeasurable hae
    _ = Λt.map fun w => (w, F w.1) := by rw [hγfst, graphPlan_def]; rfl

theorem integral_mixB' {θ : ℝ} {P Q : Measure 𝔼} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) {f : 𝔼 × Bool → ℝ} (hf : Measurable f) (hb : ∃ C, ∀ w, |f w| ≤ C) :
    ∫ w, f w ∂(mixB θ P Q) = θ * ∫ x, f (x, true) ∂P + (1 - θ) * ∫ x, f (x, false) ∂Q := by
  obtain ⟨C, hC⟩ := hb
  have hm1 : Measurable fun x : 𝔼 => (x, true) := measurable_id.prodMk measurable_const
  have hm2 : Measurable fun x : 𝔼 => (x, false) := measurable_id.prodMk measurable_const
  have hint : ∀ (m : Measure (𝔼 × Bool)) [IsFiniteMeasure m], Integrable f m := fun m _ =>
    Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun w => by
      simpa [Real.norm_eq_abs] using hC w)
  unfold mixB mix
  rw [integral_add_measure ((hint _).smul_measure ENNReal.ofReal_ne_top)
      ((hint _).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    integral_map hm1.aemeasurable hf.aestronglyMeasurable, integral_map hm2.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hθ, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

/-- Integrating a label-restricted function against `Λ̃`. -/
theorem integral_mixB_true {θ : ℝ} {P Q : Measure 𝔼} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) {ψ : 𝔼 → ℝ} (hψ : Measurable ψ) (hb : ∃ C, ∀ x, |ψ x| ≤ C) :
    ∫ w, (if w.2 = true then ψ w.1 else 0) ∂(mixB θ P Q) = θ * ∫ x, ψ x ∂P := by
  obtain ⟨C, hC⟩ := hb
  rw [integral_mixB' hθ hθ1]
  · simp
  · exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) (hψ.comp measurable_fst)
      measurable_const
  · refine ⟨max C 0, fun w => ?_⟩
    split_ifs
    · exact (hC _).trans (le_max_left _ _)
    · simp

theorem integral_mixB_false {θ : ℝ} {P Q : Measure 𝔼} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) {ψ : 𝔼 → ℝ} (hψ : Measurable ψ) (hb : ∃ C, ∀ x, |ψ x| ≤ C) :
    ∫ w, (if w.2 = false then ψ w.1 else 0) ∂(mixB θ P Q) = (1 - θ) * ∫ x, ψ x ∂Q := by
  obtain ⟨C, hC⟩ := hb
  rw [integral_mixB' hθ hθ1]
  · simp
  · exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) (hψ.comp measurable_fst)
      measurable_const
  · refine ⟨max C 0, fun w => ?_⟩
    split_ifs
    · exact (hC _).trans (le_max_left _ _)
    · simp

/-- The label indicator, a continuous function on `Bool`. -/
def ind (b : Bool) (w : (𝔼 × Bool) × 𝔼) : ℝ := if w.1.2 = b then 1 else 0

theorem continuous_ind (b : Bool) : Continuous (ind (K := K) b) := by
  have : ind (K := K) b = (fun β : Bool => if β = b then (1 : ℝ) else 0) ∘ (fun w => w.1.2) := rfl
  rw [this]
  exact (continuous_of_discreteTopology (f := fun β : Bool => if β = b then (1 : ℝ) else 0)).comp
    (continuous_snd.comp continuous_fst)

/-- The bounded continuous kernel `h_{bb'}(w, w') = 1{β = b} 1{β' = b'} min(‖y − y'‖, 2R)`. -/
def kern (R : ℝ) (hR : 0 ≤ R) (b b' : Bool) : ((𝔼 × Bool) × 𝔼) × ((𝔼 × Bool) × 𝔼) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun p => ind b p.1 * ind b' p.2 * min ‖p.1.2 - p.2.2‖ (2 * R), by
      have h1 := (continuous_ind (K := K) b).comp
        (continuous_fst (X := (𝔼 × Bool) × 𝔼) (Y := (𝔼 × Bool) × 𝔼))
      have h2 := (continuous_ind (K := K) b').comp
        (continuous_snd (X := (𝔼 × Bool) × 𝔼) (Y := (𝔼 × Bool) × 𝔼))
      have h3 : Continuous fun p : ((𝔼 × Bool) × 𝔼) × ((𝔼 × Bool) × 𝔼) => min ‖p.1.2 - p.2.2‖ (2 * R) :=
        ((continuous_snd.comp continuous_fst).sub (continuous_snd.comp continuous_snd)).norm.min continuous_const
      exact (h1.mul h2).mul h3⟩ (2 * R) (by
      intro p q
      have hb : ∀ p : ((𝔼 × Bool) × 𝔼) × ((𝔼 × Bool) × 𝔼),
          0 ≤ ind b p.1 * ind b' p.2 * min ‖p.1.2 - p.2.2‖ (2 * R) ∧
          ind b p.1 * ind b' p.2 * min ‖p.1.2 - p.2.2‖ (2 * R) ≤ 2 * R := by
        intro p
        have hm0 : 0 ≤ min ‖p.1.2 - p.2.2‖ (2 * R) := le_min (norm_nonneg _) (by linarith)
        have hm1 : min ‖p.1.2 - p.2.2‖ (2 * R) ≤ 2 * R := min_le_right _ _
        unfold ind
        split_ifs <;> simp [hm0, hm1, hR]
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      obtain ⟨a1, a2⟩ := hb p
      obtain ⟨b1, b2⟩ := hb q
      rw [abs_le]; constructor <;> linarith)

theorem kern_apply (R : ℝ) (hR : 0 ≤ R) (b b' : Bool) (p : ((𝔼 × Bool) × 𝔼) × ((𝔼 × Bool) × 𝔼)) :
    kern R hR b b' p = ind b p.1 * ind b' p.2 * min ‖p.1.2 - p.2.2‖ (2 * R) := rfl

theorem integral_prod_emp {n : ℕ} [Nonempty (Fin n)] (x : Fin n → (𝔼 × Bool) × 𝔼)
    (h : ((𝔼 × Bool) × 𝔼) × ((𝔼 × Bool) × 𝔼) →ᵇ ℝ) :
    ∫ p, h p ∂((empiricalMeasureOfFintype x).prod (empiricalMeasureOfFintype x) :
        ProbabilityMeasure (((𝔼 × Bool) × 𝔼) × ((𝔼 × Bool) × 𝔼))) =
      (n : ℝ)⁻¹ * ∑ a, ((n : ℝ)⁻¹ * ∑ a', h (x a, x a')) := by
  rw [ProbabilityMeasure.toMeasure_prod, integral_prod _ (h.integrable _)]
  have hin : ∀ w, ∫ w', h (w, w') ∂(empiricalMeasureOfFintype x : Measure ((𝔼 × Bool) × 𝔼)) =
      (n : ℝ)⁻¹ * ∑ a', h (w, x a') := fun w => by
    rw [integral_empiricalMeasureOfFintype (f := fun w' => h (w, w'))
      (h.continuous.comp (Continuous.prodMk_right w)).stronglyMeasurable, Fintype.card_fin, smul_eq_mul]
  simp_rw [hin]
  have hc : Continuous fun w => (n : ℝ)⁻¹ * ∑ a', h (w, x a') :=
    continuous_const.mul (continuous_finsetSum _ fun a' _ => h.continuous.comp (Continuous.prodMk_left _))
  rw [integral_empiricalMeasureOfFintype hc.stronglyMeasurable, Fintype.card_fin, smul_eq_mul]

/-- The kernel integral `I_{bb'}(π) = ∫ h_{bb'} d(π ⊗ π)`. -/
def kI (R : ℝ) (hR : 0 ≤ R) (b b' : Bool) (π : ProbabilityMeasure ((𝔼 × Bool) × 𝔼)) : ℝ :=
  ∫ p, kern R hR b b' p ∂((π.prod π : ProbabilityMeasure _) : Measure (((𝔼 × Bool) × 𝔼) × ((𝔼 × Bool) × 𝔼)))

/-- The rank-energy statistic through the kernels. -/
theorem rankEnergy_eq_kern {n₁ n₂ : ℕ} (h1 : 0 < n₁) (h2 : 0 < n₂) [Nonempty (Fin (n₁ + n₂))]
    (z y : Fin (n₁ + n₂) → 𝔼) {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ a, ‖y a‖ ≤ R) :
    rankEnergy n₁ n₂ y =
      2 * ((n₁ + n₂ : ℕ) : ℝ) ^ 2 / ((n₁ : ℝ) * n₂) *
          kI R hR0 true false (empiricalMeasureOfFintype (fun a => ((z a, lab n₁ n₂ a), y a))) -
        ((n₁ + n₂ : ℕ) : ℝ) ^ 2 / (n₁ : ℝ) ^ 2 *
          kI R hR0 true true (empiricalMeasureOfFintype (fun a => ((z a, lab n₁ n₂ a), y a))) -
        ((n₁ + n₂ : ℕ) : ℝ) ^ 2 / (n₂ : ℝ) ^ 2 *
          kI R hR0 false false (empiricalMeasureOfFintype (fun a => ((z a, lab n₁ n₂ a), y a))) := by
  have hmin : ∀ a a', min ‖y a - y a'‖ (2 * R) = ‖y a - y a'‖ := fun a a' =>
    min_eq_left ((norm_sub_le _ _).trans (by linarith [hR a, hR a']))
  simp only [kI]
  rw [integral_prod_emp, integral_prod_emp, integral_prod_emp]
  simp only [kern_apply, ind, hmin]
  simp only [Fin.sum_univ_add, lab_castAdd, lab_natAdd]
  simp only [if_true, if_false, Bool.true_eq_false, Bool.false_eq_true, one_mul, mul_one, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add, ite_true, ite_false]
  unfold rankEnergy
  have hn1 : (n₁ : ℝ) ≠ 0 := by exact_mod_cast h1.ne'
  have hn2 : (n₂ : ℝ) ≠ 0 := by exact_mod_cast h2.ne'
  have hN : ((n₁ + n₂ : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [← Finset.mul_sum]
  field_simp

end Core

end StatFormal.OTFD.WaveL2
