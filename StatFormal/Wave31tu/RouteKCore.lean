import StatFormal.Wave31tu.Statements
import StatFormal.Lib.LocalLower.TwoPoint
import StatFormal.Lib.LocalLower.Tail
import StatFormal.Wave31tq.RouteA1
import StatFormal.Wave31tq.RouteM21

/-!
# Wave 31tu, route K: one density of a pair moved by a bump (untrusted proof material)

The common core of `lap_local` (Y20(a), the first density moved from `B₁` to `A₁`) and `lap_local_Q` (Y20(b), the second density
moved from `A₁` to `B₁`). For probability measures `P = f·Leb`, `G = g·Leb`, disjoint measurable `A, B` with `P(A), P(B) > 0`,
`π = min{P(A), P(B)}`, `h ∈ [0,1]` and the frozen `bumpDens f A B P(A) P(B) π h` (= the library `LocalLower.bump` with
`a = hπ/P(A)`, `b = hπ/P(B)`, `bumpDens_eq`), with `P_h` its law:

* `core_nonneg`, `core_set` (`P_h(S) = P(S) + hπ{P(S∩A)/P(A) − P(S∩B)/P(B)}`), `core_prob` (`P_h` is a probability measure);
* `core_tv`: if `g ≤ f` a.e. on `A` and `f ≤ g` a.e. on `B`, `TV(P_h, G) = TV(P, G) + hπ` (31tq Q1: `TV = ∫(p − q)₊`);
* `core_tv_self`: `TV(P_h, P) = hπ`;
* `core_condR`: `c·w·(f+g) ≤ |f−g|` a.e. gives `(c/2)·w·(f_h+g) ≤ |f_h−g|` a.e. (same signs);
* `core_tail`: `ExpTailWith P G x₀ C′` and `A ∪ B ⊆ {|x − x₀| < 2r}` give `ExpTailWith P_h G x₀ (C′ + 2r + 2e)` (31tq Q1:
  `|P−Q| = |p−q|·Leb`; the extra mass is at most `2` and lives in `{|x−x₀| < 2r}`);
* `core_pi`: `TV(P_h^n, P^n) ≤ h√(nπ)` (`χ² ≤ 2h²π`, Pinsker);
* `core_lecam`: the Le Cam step for the data law with the perturbed sample first or second and an independent randomization.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave31tu.RouteK

open StatFormal StatFormal.LocalLower StatFormal.Wave31tq StatFormal.Wave30tp

/-- `bumpDens` is the library bump with `a = hπ/P(A)`, `b = hπ/P(B)`. -/
theorem bumpDens_eq (p : ℝ → ℝ) (A B : Set ℝ) (PA PB π hh : ℝ) :
    bumpDens p A B PA PB π hh = LocalLower.bump p A B (hh * π / PA) (hh * π / PB) := rfl

/-- `|P − Q|` is symmetric. -/
theorem absPQ_comm {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    absPQ P Q = absPQ Q P := by
  unfold absPQ
  rw [← neg_sub, SignedMeasure.totalVariation_neg]

/-- The data law is a probability measure. -/
theorem sampleLaw_isProb (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n m : ℕ) :
    IsProbabilityMeasure (sampleLaw P Q n m) := by
  unfold sampleLaw; infer_instance

section Core

variable {P G : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure G] {f g : ℝ → ℝ} {A B : Set ℝ} {hh π : ℝ}

omit [IsProbabilityMeasure P] [IsProbabilityMeasure G] in
/-- The weights `a = hπ/P(A)`, `b = hπ/P(B)` lie in `[0,1]` and `a·P(A) = b·P(B) = hπ`. -/
theorem core_weights (hπ : 0 < π) (hπA : π ≤ P.real A) (hπB : π ≤ P.real B) (hh0 : 0 ≤ hh) (hh1 : hh ≤ 1) :
    0 ≤ hh * π / P.real A ∧ hh * π / P.real A ≤ 1 ∧
      0 ≤ hh * π / P.real B ∧ hh * π / P.real B ≤ 1 ∧
      hh * π / P.real A * P.real A = hh * π ∧
      hh * π / P.real B * P.real B = hh * π := by
  have hPA : 0 < P.real A := hπ.trans_le hπA
  have hPB : 0 < P.real B := hπ.trans_le hπB
  refine ⟨by positivity, ?_, by positivity, ?_, by field_simp, by field_simp⟩
  · rw [div_le_one hPA]; nlinarith
  · rw [div_le_one hPB]; nlinarith

theorem core_nonneg (hAB : Disjoint A B) (hf0 : ∀ z, 0 ≤ f z) (hπ : 0 < π) (hπA : π ≤ P.real A) (hπB : π ≤ P.real B) (hh0 : 0 ≤ hh)
    (hh1 : hh ≤ 1) : ∀ z, 0 ≤ bumpDens f A B (P.real A) (P.real B) π hh z := by
  obtain ⟨ha0, -, -, hb1, -, -⟩ := core_weights hπ hπA hπB hh0 hh1
  exact bump_nonneg hAB hf0 ha0 hb1

theorem core_set (hfm : Measurable f) (hf0 : ∀ z, 0 ≤ f z) (hP : P = volume.withDensity fun x => ENNReal.ofReal (f x))
    (hAB : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) (hπ : 0 < π) (hπA : π ≤ P.real A) (hπB : π ≤ P.real B)
    (hh0 : 0 ≤ hh) (hh1 : hh ≤ 1) (S : Set ℝ) (hS : MeasurableSet S) :
    (volume.withDensity fun z => ENNReal.ofReal (bumpDens f A B (P.real A) (P.real B) π hh z)).real S =
      P.real S + hh * π * (P.real (S ∩ A) / P.real A - P.real (S ∩ B) / P.real B) := by
  obtain ⟨ha0, -, -, hb1, -, -⟩ := core_weights hπ hπA hπB hh0 hh1
  have hint := StatFormal.CrossLaws.integrable_of_density hfm hf0 hP
  simp only [bumpDens_eq]
  rw [measureReal_bump hint hf0 hAB hA hB ha0 hb1 hS, ← hP]
  ring

theorem core_prob (hfm : Measurable f) (hf0 : ∀ z, 0 ≤ f z) (hP : P = volume.withDensity fun x => ENNReal.ofReal (f x))
    (hAB : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) (hπ : 0 < π) (hπA : π ≤ P.real A) (hπB : π ≤ P.real B)
    (hh0 : 0 ≤ hh) (hh1 : hh ≤ 1) :
    IsProbabilityMeasure
      (volume.withDensity fun z => ENNReal.ofReal (bumpDens f A B (P.real A) (P.real B) π hh z)) := by
  obtain ⟨ha0, -, -, hb1, hA1, hB1⟩ := core_weights hπ hπA hπB hh0 hh1
  have hint := StatFormal.CrossLaws.integrable_of_density hfm hf0 hP
  have : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (f x)) := by rw [← hP]; infer_instance
  simp only [bumpDens_eq]
  refine isProbabilityMeasure_bump hint hf0 hAB hA hB ha0 hb1 ?_
  rw [← hP, hA1, hB1]

/-- `TV(P_h, G) = TV(P, G) + hπ` when `g ≤ f` a.e. on `A` and `f ≤ g` a.e. on `B`. -/
theorem core_tv (hfm : Measurable f) (hgm : Measurable g) (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z)
    (hP : P = volume.withDensity fun x => ENNReal.ofReal (f x)) (hG : G = volume.withDensity fun x => ENNReal.ofReal (g x))
    (hAB : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) (hπ : 0 < π) (hπA : π ≤ P.real A) (hπB : π ≤ P.real B)
    (hh0 : 0 ≤ hh) (hh1 : hh ≤ 1) (hsA : ∀ᵐ x ∂volume, x ∈ A → g x ≤ f x) (hsB : ∀ᵐ x ∂volume, x ∈ B → f x ≤ g x) :
    Distances.tvDist
        (volume.withDensity fun z => ENNReal.ofReal (bumpDens f A B (P.real A) (P.real B) π hh z)) G =
      Distances.tvDist P G + hh * π := by
  obtain ⟨ha0, -, hb0, -, hA1, -⟩ := core_weights hπ hπA hπB hh0 hh1
  have := core_prob hfm hf0 hP hAB hA hB hπ hπA hπB hh0 hh1
  have hint := StatFormal.CrossLaws.integrable_of_density hfm hf0 hP
  have hgint := StatFormal.CrossLaws.integrable_of_density hgm hg0 hG
  have hfbm : Measurable (bumpDens f A B (P.real A) (P.real B) π hh) :=
    measurable_bump hfm hA hB
  have hT := (RouteA.tv_density_route.2 ℝ _ G _ g hfbm hgm (core_nonneg hAB hf0 hπ hπA hπB hh0 hh1) hg0 rfl hG).2.2.2.1
  have hT0 := (RouteA.tv_density_route.2 ℝ P G f g hfm hgm hf0 hg0 hP hG).2.2.2.1
  rw [hT, hT0]
  simp only [bumpDens_eq]
  rw [integral_posPart_bump hint hgint hf0 hAB hA ha0 hb0 hsA hsB, ← measureReal_withDensity_ofReal hint hf0 hA, ← hP,
    hA1]

/-- `TV(P_h, P) = hπ`. -/
theorem core_tv_self (hfm : Measurable f) (hf0 : ∀ z, 0 ≤ f z) (hP : P = volume.withDensity fun x => ENNReal.ofReal (f x))
    (hAB : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) (hπ : 0 < π) (hπA : π ≤ P.real A) (hπB : π ≤ P.real B)
    (hh0 : 0 ≤ hh) (hh1 : hh ≤ 1) :
    Distances.tvDist
        (volume.withDensity fun z => ENNReal.ofReal (bumpDens f A B (P.real A) (P.real B) π hh z)) P =
      hh * π := by
  have h := core_tv (G := P) hfm hfm hf0 hf0 hP hP hAB hA hB hπ hπA hπB hh0 hh1 (ae_of_all _ fun _ _ => le_rfl)
    (ae_of_all _ fun _ _ => le_rfl)
  rwa [Distances.tvDist_self, zero_add] at h

omit [IsProbabilityMeasure P] [IsProbabilityMeasure G] in
/-- Off `A ∪ B` the perturbed density is `f`. -/
theorem core_eq_off {z : ℝ} (hzA : z ∉ A) (hzB : z ∉ B) : bumpDens f A B (P.real A) (P.real B) π hh z = f z :=
  bump_of_not_mem hzA hzB

omit [IsProbabilityMeasure P] [IsProbabilityMeasure G] in
/-- Off `B` the perturbed density is at least `f`. -/
theorem core_ge_off (hAB : Disjoint A B) (hf0 : ∀ z, 0 ≤ f z) (hπ : 0 < π) (hπA : π ≤ P.real A) (hπB : π ≤ P.real B)
    (hh0 : 0 ≤ hh) (hh1 : hh ≤ 1) {z : ℝ} (hzB : z ∉ B) : f z ≤ bumpDens f A B (P.real A) (P.real B) π hh z := by
  obtain ⟨ha0, -, -, -, -, -⟩ := core_weights hπ hπA hπB hh0 hh1
  exact le_bump hAB hf0 ha0 hzB

omit [IsProbabilityMeasure P] [IsProbabilityMeasure G] in
/-- Off `A` the perturbed density is at most `f`. -/
theorem core_le_off (hAB : Disjoint A B) (hf0 : ∀ z, 0 ≤ f z) (hπ : 0 < π) (hπA : π ≤ P.real A) (hπB : π ≤ P.real B)
    (hh0 : 0 ≤ hh) (hh1 : hh ≤ 1) {z : ℝ} (hzA : z ∉ A) : bumpDens f A B (P.real A) (P.real B) π hh z ≤ f z := by
  obtain ⟨-, -, hb0, -, -, -⟩ := core_weights hπ hπA hπB hh0 hh1
  exact bump_le hAB hf0 hb0 hzA

omit [IsProbabilityMeasure P] [IsProbabilityMeasure G] in
/-- The perturbed density is at most `2f`. -/
theorem core_le_two (hAB : Disjoint A B) (hf0 : ∀ z, 0 ≤ f z) (hπ : 0 < π) (hπA : π ≤ P.real A) (hπB : π ≤ P.real B)
    (hh0 : 0 ≤ hh) (hh1 : hh ≤ 1) (z : ℝ) : bumpDens f A B (P.real A) (P.real B) π hh z ≤ 2 * f z := by
  obtain ⟨-, ha1, hb0, -, -, -⟩ := core_weights hπ hπA hπB hh0 hh1
  exact bump_le_two_mul hAB hf0 ha1 hb0 z

/-- The local condition with half the constant. -/
theorem core_condR (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z) (hAB : Disjoint A B) (hπ : 0 < π)
    (hπA : π ≤ P.real A) (hπB : π ≤ P.real B) (hh0 : 0 ≤ hh) (hh1 : hh ≤ 1) (hsA : ∀ᵐ x ∂volume, x ∈ A → g x ≤ f x)
    (hsB : ∀ᵐ x ∂volume, x ∈ B → f x ≤ g x) {c : ℝ} {w : ℝ → ℝ} (hc : 0 ≤ c) (hw : ∀ x, 0 ≤ w x)
    (h : ∀ᵐ x ∂volume, c * w x * (f x + g x) ≤ |f x - g x|) :
    ∀ᵐ x ∂volume, c / 2 * w x * (bumpDens f A B (P.real A) (P.real B) π hh x + g x) ≤
      |bumpDens f A B (P.real A) (P.real B) π hh x - g x| := by
  obtain ⟨ha0, ha1, hb0, -, -, -⟩ := core_weights hπ hπA hπB hh0 hh1
  simp only [bumpDens_eq]
  exact ae_condR_bump hf0 hg0 hAB ha0 ha1 hb0 hc hw hsA hsB h

/-- `|P_h − G|(S) ≤ |P − G|(S) + a·P(S ∩ A) + b·P(S ∩ B)`. -/
theorem core_abs (hfm : Measurable f) (hgm : Measurable g) (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z)
    (hP : P = volume.withDensity fun x => ENNReal.ofReal (f x)) (hG : G = volume.withDensity fun x => ENNReal.ofReal (g x))
    (hAB : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) (hπ : 0 < π) (hπA : π ≤ P.real A) (hπB : π ≤ P.real B)
    (hh0 : 0 ≤ hh) (hh1 : hh ≤ 1)
    [IsProbabilityMeasure
      (volume.withDensity fun z => ENNReal.ofReal (bumpDens f A B (P.real A) (P.real B) π hh z))]
    {S : Set ℝ} (hS : MeasurableSet S) :
    absPQ (volume.withDensity fun z => ENNReal.ofReal (bumpDens f A B (P.real A) (P.real B) π hh z))
        G S ≤
      absPQ P G S + ENNReal.ofReal (hh * π / P.real A) * P (S ∩ A) +
        ENNReal.ofReal (hh * π / P.real B) * P (S ∩ B) := by
  obtain ⟨ha0, -, hb0, -, -, -⟩ := core_weights hπ hπA hπB hh0 hh1
  have hfbm : Measurable (bumpDens f A B (P.real A) (P.real B) π hh) :=
    measurable_bump hfm hA hB
  have hT := (RouteA.tv_density_route.2 ℝ _ G _ g hfbm hgm (core_nonneg hAB hf0 hπ hπA hπB hh0 hh1) hg0 rfl hG).1
  have hT0 := (RouteA.tv_density_route.2 ℝ P G f g hfm hgm hf0 hg0 hP hG).1
  rw [hT, hT0, withDensity_apply _ hS, withDensity_apply _ hS]
  simp only [bumpDens_eq]
  have h := setLIntegral_abs_bump_sub_le (ν := volume) (g := g) hfm hgm hf0 hAB hA hB ha0 hb0 hS
  rw [← hP] at h
  exact h

/-- **The tail constant of the perturbed pair**: `ExpTailWith P G x₀ C′` and `A ∪ B ⊆ {|x − x₀| < 2r}` give
`ExpTailWith P_h G x₀ (C′ + 2r + 2e)`. -/
theorem core_tail (hfm : Measurable f) (hgm : Measurable g) (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z)
    (hP : P = volume.withDensity fun x => ENNReal.ofReal (f x)) (hG : G = volume.withDensity fun x => ENNReal.ofReal (g x))
    (hAB : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) (hπ : 0 < π) (hπA : π ≤ P.real A) (hπB : π ≤ P.real B)
    (hh0 : 0 ≤ hh) (hh1 : hh ≤ 1)
    [IsProbabilityMeasure
      (volume.withDensity fun z => ENNReal.ofReal (bumpDens f A B (P.real A) (P.real B) π hh z))]
    {x₀ r C' : ℝ} (hr : 0 < r) (hAx : ∀ x ∈ A, |x - x₀| < 2 * r) (hBx : ∀ x ∈ B, |x - x₀| < 2 * r)
    (hexp : ExpTailWith P G x₀ C') :
    ExpTailWith
      (volume.withDensity fun z => ENNReal.ofReal (bumpDens f A B (P.real A) (P.real B) π hh z))
      G x₀ (C' + 2 * r + 2 * Real.exp 1) := by
  obtain ⟨hC', ht⟩ := hexp
  obtain ⟨ha0, -, hb0, -, hA1, hB1⟩ := core_weights hπ hπA hπB hh0 hh1
  have hπ1 : hh * π ≤ 1 := by
    have h1 : π ≤ 1 := hπA.trans ((measureReal_mono (subset_univ A)).trans_eq probReal_univ)
    nlinarith
  refine ⟨by have := Real.exp_pos 1; linarith, fun t htpos => ?_⟩
  have hS : MeasurableSet {x : ℝ | t < |x - x₀|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_id.sub_const x₀))
  have habs := core_abs hfm hgm hf0 hg0 hP hG hAB hA hB hπ hπA hπB hh0 hh1 hS
  have hbase := ht t htpos
  rcases le_or_gt (2 * r) t with htr | htr
  · -- far out: the bump does not meet `{|x − x₀| > t}`
    have hSA : {x : ℝ | t < |x - x₀|} ∩ A = ∅ := by
      ext x; simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hx hxA; have := hAx x hxA; linarith
    have hSB : {x : ℝ | t < |x - x₀|} ∩ B = ∅ := by
      ext x; simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hx hxB; have := hBx x hxB; linarith
    simp only [hSA, hSB, measure_empty, mul_zero, add_zero] at habs
    refine habs.trans (hbase.trans (ENNReal.ofReal_le_ofReal ?_))
    exact exp_tail_mono hC' (by have := Real.exp_pos 1; linarith) htpos.le
  · -- near: the extra mass is at most `2`
    have hX : ∀ (C : Set ℝ) (c : ℝ), c * P.real C ≤ 1 → 0 ≤ c → ENNReal.ofReal c * P ({x : ℝ | t < |x - x₀|} ∩ C) ≤ 1 := by
      intro C c hc hc0
      calc ENNReal.ofReal c * P ({x : ℝ | t < |x - x₀|} ∩ C) ≤ ENNReal.ofReal c * P C :=
            mul_le_mul_right (measure_mono inter_subset_right) _
        _ = ENNReal.ofReal (c * P.real C) := by
            rw [ENNReal.ofReal_mul hc0, ofReal_measureReal]
        _ ≤ 1 := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hc
    have h1 := hX A _ (by rw [hA1]; exact hπ1) ha0
    have h2 := hX B _ (by rw [hB1]; exact hπ1) hb0
    calc absPQ _ G {x : ℝ | t < |x - x₀|}
        ≤ ENNReal.ofReal (C' * Real.exp (-t / C')) + 1 + 1 := habs.trans (add_le_add (add_le_add hbase h1) h2)
      _ = ENNReal.ofReal (C' * Real.exp (-t / C') + 2) := by
          rw [add_assoc, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one zero_le_one,
            ← ENNReal.ofReal_add (by positivity) (by norm_num)]
          norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal (exp_tail_add_two_le hC' htpos htr.le)

/-- **The `n`-sample total variation of the bump law**: `TV(P_h^n, P^n) ≤ h√(nπ)`. -/
theorem core_pi (hfm : Measurable f) (hf0 : ∀ z, 0 ≤ f z) (hP : P = volume.withDensity fun x => ENNReal.ofReal (f x))
    (hAB : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) (hπ : 0 < π) (hπA : π ≤ P.real A) (hπB : π ≤ P.real B)
    (hh0 : 0 ≤ hh) (hh1 : hh ≤ 1)
    [IsProbabilityMeasure
      (volume.withDensity fun z => ENNReal.ofReal (bumpDens f A B (P.real A) (P.real B) π hh z))]
    (n : ℕ) :
    Distances.tvDist
        (Measure.pi fun _ : Fin n =>
          volume.withDensity fun z => ENNReal.ofReal (bumpDens f A B (P.real A) (P.real B) π hh z))
        (Measure.pi fun _ : Fin n => P) ≤ hh * √(n * π) := by
  have heq : (volume.withDensity fun z =>
        ENNReal.ofReal (bumpDens f A B (P.real A) (P.real B) π hh z)) =
      P.withDensity fun x => ENNReal.ofReal (bumpFac A B (hh * π / P.real A)
        (hh * π / P.real B) x) := by
    simp only [bumpDens_eq]
    rw [withDensity_bump hfm hf0 hA hB, ← hP]
  have : IsProbabilityMeasure (P.withDensity fun x => ENNReal.ofReal (bumpFac A B
      (hh * π / P.real A) (hh * π / P.real B) x)) := by
    rw [← heq]; infer_instance
  rw [heq]
  exact tvDist_pi_bumpFac_le hAB hA hB hπ hπA hπB hh0 hh1 n

end Core

/-- **Le Cam's step, the first sample perturbed**: a valid `T` (`P_{P,Q}(T > α⋆) ≤ δ`) satisfies `T ≤ α⋆` with probability at least
`1 − δ − c` under `(P′, Q)` whenever `TV(P′^n, P^n) ≤ c`. -/
theorem lecam_first {P Q P' : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure P']
    {n m : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
    {T : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ} (hT : Measurable T) {t₀ δ c : ℝ}
    (hval : ((sampleLaw P Q n m).prod ρ).real {z | t₀ < T z} ≤ δ)
    (hc : Distances.tvDist (Measure.pi fun _ : Fin n => P') (Measure.pi fun _ : Fin n => P) ≤ c) :
    1 - δ - c ≤ ((sampleLaw P' Q n m).prod ρ).real {z | T z ≤ t₀} := by
  have := sampleLaw_isProb P Q n m
  have := sampleLaw_isProb P' Q n m
  refine lecam_randomized ρ hT hval ?_
  exact (Distances.tvDist_prod_left_le (Measure.pi fun _ : Fin m => Q)).trans hc

/-- **Le Cam's step, the second sample perturbed**. -/
theorem lecam_second {P Q Q' : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    {n m : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
    {T : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ} (hT : Measurable T) {t₀ δ c : ℝ}
    (hval : ((sampleLaw P Q n m).prod ρ).real {z | t₀ < T z} ≤ δ)
    (hc : Distances.tvDist (Measure.pi fun _ : Fin m => Q') (Measure.pi fun _ : Fin m => Q) ≤ c) :
    1 - δ - c ≤ ((sampleLaw P Q' n m).prod ρ).real {z | T z ≤ t₀} := by
  have := sampleLaw_isProb P Q n m
  have := sampleLaw_isProb P Q' n m
  refine lecam_randomized ρ hT hval ?_
  exact (Distances.tvDist_prod_right_le (Measure.pi fun _ : Fin n => P)).trans hc

/-! ### The two intervals `A₁ = (x₀ + r, x₀ + 2r)`, `B₁ = (x₀ − 2r, x₀ − r)` -/

theorem disjoint_A₁_B₁ {x₀ r : ℝ} (hr : 0 < r) : Disjoint (Ioo (x₀ + r) (x₀ + 2 * r)) (Ioo (x₀ - 2 * r) (x₀ - r)) :=
  Set.disjoint_left.2 fun x hA hB => by linarith [hA.1, hB.2]

theorem abs_lt_of_mem_A₁ {x₀ r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo (x₀ + r) (x₀ + 2 * r)) : |x - x₀| < 2 * r := by
  rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]

theorem abs_lt_of_mem_B₁ {x₀ r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo (x₀ - 2 * r) (x₀ - r)) : |x - x₀| < 2 * r := by
  rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]

/-- `P(A₁), P(B₁) > 0` and `Q(A₁), Q(B₁) > 0` from a density positive on `[x₀ − 2r, x₀ + 2r]`. -/
theorem real_pos_of_density {P : Measure ℝ} [IsProbabilityMeasure P] {p : ℝ → ℝ} (hpm : Measurable p)
    (hP : P = volume.withDensity fun x => ENNReal.ofReal (p x)) {S : Set ℝ} (hS : MeasurableSet S) (hpos : ∀ x ∈ S, 0 < p x)
    (hvol : 0 < volume S) : 0 < P.real S := by
  have h := withDensity_pos_of_pos_on hpm hS hpos hvol
  rw [← hP] at h
  exact ENNReal.toReal_pos h.ne' (measure_ne_top P S)

end StatFormal.Wave31tu.RouteK
