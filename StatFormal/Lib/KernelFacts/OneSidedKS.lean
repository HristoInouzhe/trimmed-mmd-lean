import StatFormal.Lib.Distances.TV
import StatFormal.Lib.DKW.Massart
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Total variation as a one-sided Kolmogorov distance; one-sided DKW on the line (library, untrusted)

* `tvDist_eq_of_hahn_set`: if `Q ≤ P` on the subsets of a measurable `R` and `P ≤ Q` on the subsets of `Rᶜ` (`R` a Hahn set of
  `P − Q`), then `TV(P,Q) = P(R) − Q(R)`, for probability measures.
* `withDensity_le_withDensity_on`: `b ≤ a` a.e. on `R` gives `μ.withDensity b ≤ μ.withDensity a` on the subsets of `R`.
* `ciSup_eq_of_le_of_eq`: a function bounded by `T` and equal to `T` somewhere has supremum `T`.
* `dkw_upper_real`, `dkw_lower_real`: the one-sided DKW–Massart bounds `P(∃u, t < F̂_n(u) − F(u)) ≤ e^{−2nt²}` and
  `P(∃u, t < F(u) − F̂_n(u)) ≤ e^{−2nt²}` for a law on `ℝ` (the library `DKW.Massart` with the score `x ↦ e^x`).
* `exists_measurable_compl_of_le`: a set of outer measure at most `c` misses a measurable set of measure at least `1 − c`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.KernelFacts

section Hahn

variable {α : Type*} [MeasurableSpace α]

/-- **TV at a Hahn set.** For probability measures `P, Q` and a measurable `R` with `Q(A) ≤ P(A)` for measurable `A ⊆ R` and
`P(A) ≤ Q(A)` for measurable `A ⊆ Rᶜ`: `TV(P,Q) = P(R) − Q(R)`. -/
theorem tvDist_eq_of_hahn_set (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {R : Set α}
    (hR : MeasurableSet R) (h1 : ∀ A, MeasurableSet A → A ⊆ R → Q A ≤ P A)
    (h2 : ∀ A, MeasurableSet A → A ⊆ Rᶜ → P A ≤ Q A) :
    StatFormal.Distances.tvDist P Q = P.real R - Q.real R := by
  have r1 : ∀ A, MeasurableSet A → A ⊆ R → Q.real A ≤ P.real A := fun A hA hAR =>
    ENNReal.toReal_mono (measure_ne_top P A) (h1 A hA hAR)
  have r2 : ∀ A, MeasurableSet A → A ⊆ Rᶜ → P.real A ≤ Q.real A := fun A hA hAR =>
    ENNReal.toReal_mono (measure_ne_top Q A) (h2 A hA hAR)
  have hRc : P.real Rᶜ = 1 - P.real R ∧ Q.real Rᶜ = 1 - Q.real R :=
    ⟨probReal_compl_eq_one_sub hR, probReal_compl_eq_one_sub hR⟩
  have key : ∀ A, MeasurableSet A → |P.real A - Q.real A| ≤ P.real R - Q.real R := by
    intro A hA
    have eA := measureReal_inter_add_sdiff (μ := P) (s := A) hR
    have eA' := measureReal_inter_add_sdiff (μ := Q) (s := A) hR
    have eR := measureReal_inter_add_sdiff (μ := P) (s := R) hA
    have eR' := measureReal_inter_add_sdiff (μ := Q) (s := R) hA
    have eC := measureReal_inter_add_sdiff (μ := P) (s := Rᶜ) hA
    have eC' := measureReal_inter_add_sdiff (μ := Q) (s := Rᶜ) hA
    have a1 := r1 (A ∩ R) (hA.inter hR) inter_subset_right
    have a2 := r1 (R \ A) (hR.diff hA) diff_subset
    have a3 := r2 (A \ R) (hA.diff hR) (fun x hx => hx.2)
    have a4 := r2 (Rᶜ \ A) (hR.compl.diff hA) diff_subset
    have i1 : R ∩ A = A ∩ R := inter_comm _ _
    have i2 : Rᶜ ∩ A = A \ R := by ext x; simp [and_comm]
    rw [i1] at eR eR'
    rw [i2] at eC eC'
    rw [abs_le]; constructor <;> linarith [hRc.1, hRc.2]
  refine le_antisymm (StatFormal.Distances.tvDist_le_of_forall key) ?_
  refine le_trans (le_abs_self _) (StatFormal.Distances.abs_measureReal_sub_le_tvDist hR)

/-- Densities ordered a.e. on `R` give measures ordered on the measurable subsets of `R`. -/
theorem withDensity_le_withDensity_on (μ : Measure α) {a b : α → ℝ≥0∞} {R : Set α}
    (hab : ∀ᵐ x ∂μ, x ∈ R → b x ≤ a x) {A : Set α} (hA : MeasurableSet A) (hAR : A ⊆ R) :
    μ.withDensity b A ≤ μ.withDensity a A := by
  rw [withDensity_apply _ hA, withDensity_apply _ hA]
  refine lintegral_mono_ae ?_
  rw [ae_restrict_iff' hA]
  filter_upwards [hab] with x hx hxA using hx (hAR hxA)

end Hahn

/-- A real function bounded by `T` everywhere and equal to `T` at one point has supremum `T`. -/
theorem ciSup_eq_of_le_of_eq {ι : Type*} [Nonempty ι] {F : ι → ℝ} {T : ℝ} (hle : ∀ i, F i ≤ T) (i₀ : ι)
    (heq : F i₀ = T) : ⨆ i, F i = T :=
  le_antisymm (ciSup_le hle) (heq ▸ le_ciSup ⟨T, by rintro _ ⟨i, rfl⟩; exact hle i⟩ i₀)

section DKW

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma score_le_iff (x u : ℝ) : ENNReal.ofReal (Real.exp x) ≤ ENNReal.ofReal (Real.exp u) ↔ x ≤ u := by
  rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos u).le, Real.exp_le_exp]

/-- **One-sided DKW–Massart on `ℝ`, upper deviations**: `P(∃u, t < F̂_n(u) − F(u)) ≤ e^{−2nt²}`, `F(u) = μ((−∞,u])`. -/
theorem dkw_upper_real {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => μ)
      {y | ∃ u : ℝ, t < ((Finset.univ.filter fun i => y i ≤ u).card : ℝ) / n - μ.real (Iic u)} ≤
      ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  set V : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp x) with hV
  have hVm : Measurable V := ENNReal.measurable_ofReal.comp Real.measurable_exp
  refine le_trans (measure_mono ?_) (StatFormal.DKW.Massart.massart_upper μ V hVm hn ht)
  rintro y ⟨u, hu⟩
  refine ⟨V u, ?_⟩
  have h1 : (Finset.univ.filter fun i => V (y i) ≤ V u) = Finset.univ.filter fun i => y i ≤ u := by
    ext i; simp [V, score_le_iff]
  have h2 : {x | V x ≤ V u} = Iic u := by ext x; simp [V, score_le_iff]
  rw [h1, h2, ← measureReal_def]
  exact hu

/-- **One-sided DKW–Massart on `ℝ`, lower deviations**: `P(∃u, t < F(u) − F̂_n(u)) ≤ e^{−2nt²}`, `F(u) = μ((−∞,u])`. -/
theorem dkw_lower_real {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => μ)
      {y | ∃ u : ℝ, t < μ.real (Iic u) - ((Finset.univ.filter fun i => y i ≤ u).card : ℝ) / n} ≤
      ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  set V : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp x) with hV
  have hVm : Measurable V := ENNReal.measurable_ofReal.comp Real.measurable_exp
  refine le_trans (measure_mono ?_) (StatFormal.DKW.Massart.massart_lower μ V hVm hn ht)
  rintro y ⟨u, hu⟩
  refine ⟨V u, ?_⟩
  have h1 : (Finset.univ.filter fun i => V (y i) ≤ V u) = Finset.univ.filter fun i => y i ≤ u := by
    ext i; simp [V, score_le_iff]
  have h2 : {x | V x ≤ V u} = Iic u := by ext x; simp [V, score_le_iff]
  rw [h1, h2, ← measureReal_def]
  exact hu

end DKW

/-- A set `N` of (outer) measure at most `ofReal c` under a probability measure misses a measurable set `E` with
`ofReal (1 − c) ≤ μ E` (the complement of a measurable hull of `N`). -/
theorem exists_measurable_compl_of_le {β : Type*} [MeasurableSpace β] (μ : Measure β) [IsProbabilityMeasure μ] {N : Set β}
    {c : ℝ} (hc : 0 ≤ c) (hN : μ N ≤ ENNReal.ofReal c) :
    ∃ E : Set β, MeasurableSet E ∧ ENNReal.ofReal (1 - c) ≤ μ E ∧ E ⊆ Nᶜ := by
  refine ⟨(toMeasurable μ N)ᶜ, (measurableSet_toMeasurable μ N).compl, ?_,
    compl_subset_compl.2 (subset_toMeasurable μ N)⟩
  rw [prob_compl_eq_one_sub (measurableSet_toMeasurable μ N), measure_toMeasurable]
  rw [ENNReal.ofReal_sub _ hc, ENNReal.ofReal_one]
  exact tsub_le_tsub_left hN _

section KS

variable (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- The one-sided upper-tail differences `P((x,∞)) − Q((x,∞))` are bounded above (by `1`). -/
theorem bddAbove_tail_sub : BddAbove (Set.range fun x : ℝ => P.real (Ioi x) - Q.real (Ioi x)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, rfl⟩
  have h1 : P.real (Ioi x) ≤ 1 := measureReal_le_one
  have h2 : 0 ≤ Q.real (Ioi x) := measureReal_nonneg
  linarith

/-- `P((x,∞)) − Q((x,∞)) = Q((−∞,x]) − P((−∞,x])` for probability measures. -/
theorem tail_sub_eq_cdf_sub (x : ℝ) : P.real (Ioi x) - Q.real (Ioi x) = Q.real (Iic x) - P.real (Iic x) := by
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  ring

/-- `KS⁺ ≤ TV`: `sup_x {P((x,∞)) − Q((x,∞))} ≤ TV(P,Q)`. -/
theorem iSup_tail_sub_le_tvDist : (⨆ x : ℝ, (P.real (Ioi x) - Q.real (Ioi x))) ≤ StatFormal.Distances.tvDist P Q :=
  ciSup_le fun x => (le_abs_self _).trans (StatFormal.Distances.abs_measureReal_sub_le_tvDist measurableSet_Ioi)

/-- **Stability of the one-sided KS distance.** If `F_P − F_{P'} ≤ a` and `F_{Q'} − F_Q ≤ b` pointwise (CDFs), then
`KS⁺(P',Q') ≤ KS⁺(P,Q) + a + b`, with `KS⁺(μ,ν) = sup_x {μ((x,∞)) − ν((x,∞))}`. -/
theorem iSup_tail_sub_le_add (P' Q' : Measure ℝ) [IsProbabilityMeasure P'] [IsProbabilityMeasure Q'] {a b : ℝ}
    (hP : ∀ u, P.real (Iic u) - P'.real (Iic u) ≤ a) (hQ : ∀ u, Q'.real (Iic u) - Q.real (Iic u) ≤ b) :
    (⨆ x : ℝ, (P'.real (Ioi x) - Q'.real (Ioi x))) ≤ (⨆ x : ℝ, (P.real (Ioi x) - Q.real (Ioi x))) + a + b := by
  refine ciSup_le fun x => ?_
  have h := le_ciSup (bddAbove_tail_sub P Q) x
  rw [tail_sub_eq_cdf_sub P' Q' x]
  rw [tail_sub_eq_cdf_sub P Q x] at h
  linarith [hP x, hQ x]

end KS

end StatFormal.KernelFacts
