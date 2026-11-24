import StatFormal.Lib.MeasurableSelection.KRN
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measurable minimum and measurable argmin (Aliprantis–Border, Theorem 18.19)

Library component (untrusted). `X` a measurable space, `Y` a nonempty compact metric space (Borel).

* `UnifApprox f D`: every `y` is the limit of a sequence in `D` along which `f x · → f x y` for EVERY `x` (the same
  sequence for all `x`). For Carathéodory `f` (continuous in `y`) any dense `D` works; for `f = g + h` with `g`
  Carathéodory and `h` lower semicontinuous and independent of `x`, a countable `D` dense in the graph of `h` works
  (`exists_countable_approx_graph`).
* `exists_measurable_argmin_of_approx`: values in a complete linear order `β` with second-countable order topology
  (`ℝ≥0∞`, `EReal`); `f x ·` lower semicontinuous, `f · y` measurable for `y ∈ D` (countable), `UnifApprox f D`.
  Then `x ↦ min_y f x y` is measurable and there is a measurable `σ` with `f x (σ x) = min_y f x y`.
* `exists_measurable_argmin`: the Carathéodory case (`β`-valued); `exists_measurable_argmin_real` (real-valued);
  `exists_measurable_argmin_add` (`ℝ≥0∞`, `g + h`, `h` lower semicontinuous).
* `exists_measurable_argmin_on`: a fixed compact constraint set `K` of an arbitrary metric space (unit spheres, the
  simplex, `SO(3)` inside a finite-dimensional space): measurable `σ` with values in `K` minimising over `K`.

Proof of the main theorem: `m_U(x) = inf_{y ∈ U} f x y = inf_{d ∈ D ∩ U} f x d` for open `U` (measurable); the argmin
correspondence `A x = {y | f x y ≤ v x}` has closed nonempty values and
`{x | A x ∩ F ≠ ∅} = ⋂_j {m_{F_j}(x) ≤ v(x)}` for closed `F` (`F_j` the open `1/(j+1)`-thickenings; `⊇` by the
finite-intersection property of the compact sets `A x ∩ cthickening(1/(j+1)) F`); then Kuratowski–Ryll-Nardzewski.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open Filter Topology MeasureTheory Set Metric
open scoped ENNReal

namespace StatFormal.Foundations.MeasurableSelection

/-- `D` approximates every point of `Y` along sequences on which `f x ·` converges for every `x` simultaneously. -/
def UnifApprox {X Y β : Type*} [TopologicalSpace Y] [TopologicalSpace β] (f : X → Y → β) (D : Set Y) : Prop :=
  ∀ y, ∃ u : ℕ → Y, (∀ n, u n ∈ D) ∧ Tendsto u atTop (𝓝 y) ∧ ∀ x, Tendsto (fun n => f x (u n)) atTop (𝓝 (f x y))

/-- A countable set of points approximating every point together with the value of `h` (dense in the graph). -/
lemma exists_countable_approx_graph {Y β : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
    [TopologicalSpace β] [SecondCountableTopology β] (h : Y → β) :
    ∃ D : Set Y, D.Countable ∧ ∀ y, ∃ u : ℕ → Y, (∀ n, u n ∈ D) ∧ Tendsto u atTop (𝓝 y) ∧
      Tendsto (fun n => h (u n)) atTop (𝓝 (h y)) := by
  let G : Set (Y × β) := range fun y => (y, h y)
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense G
  refine ⟨(fun p : G => (p : Y × β).1) '' S, hSc.image _, fun y => ?_⟩
  have hy : (⟨(y, h y), y, rfl⟩ : G) ∈ closure S := hSd.closure_eq ▸ mem_univ _
  obtain ⟨s, hsS, hs⟩ := mem_closure_iff_seq_limit.1 hy
  have hval : ∀ n, h ((s n : Y × β).1) = (s n : Y × β).2 := by
    intro n
    obtain ⟨z, hz⟩ := (s n).2
    rw [← hz]
  refine ⟨fun n => (s n : Y × β).1, fun n => ⟨s n, hsS n, rfl⟩, ?_, ?_⟩
  · exact ((continuous_fst.comp continuous_subtype_val).tendsto _).comp hs
  · simp_rw [hval]
    exact ((continuous_snd.comp continuous_subtype_val).tendsto _).comp hs

section Main

variable {X Y β : Type*} [MeasurableSpace X] [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [BorelSpace Y] [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] [SecondCountableTopology β]
  [MeasurableSpace β] [BorelSpace β]

lemma biInf_open_eq (f : X → Y → β) (D : Set Y) (happ : UnifApprox f D) {U : Set Y} (hU : IsOpen U) (x : X) :
    ⨅ y ∈ U, f x y = ⨅ d ∈ D ∩ U, f x d := by
  refine le_antisymm (biInf_mono fun d hd => hd.2) ?_
  refine le_iInf₂ fun y hy => ?_
  obtain ⟨u, huD, hu, hfu⟩ := happ y
  have hev : ∀ᶠ n in atTop, u n ∈ U := hu (hU.mem_nhds hy)
  refine ge_of_tendsto (hfu x) ?_
  filter_upwards [hev] with n hn
  exact biInf_le (fun d => f x d) ⟨huD n, hn⟩

lemma measurable_biInf_open (f : X → Y → β) (D : Set Y) (hD : D.Countable)
    (hmeas : ∀ y ∈ D, Measurable fun x => f x y) (happ : UnifApprox f D) {U : Set Y} (hU : IsOpen U) :
    Measurable fun x => ⨅ y ∈ U, f x y := by
  have : (fun x => ⨅ y ∈ U, f x y) = fun x => ⨅ d ∈ D ∩ U, f x d := funext (biInf_open_eq f D happ hU)
  rw [this]
  exact Measurable.biInf _ (hD.mono inter_subset_left) fun d hd => hmeas d hd.1

/-- **Measurable maximum theorem** (minimum form; Aliprantis–Border 18.19 for `f` lower semicontinuous in `y` and
uniformly approximable from a countable set): `x ↦ min_y f x y` is measurable and has a measurable minimiser. -/
theorem exists_measurable_argmin_of_approx [Nonempty Y] (f : X → Y → β) (D : Set Y) (hD : D.Countable)
    (hmeas : ∀ y ∈ D, Measurable fun x => f x y) (hlsc : ∀ x, LowerSemicontinuous (f x))
    (happ : UnifApprox f D) :
    Measurable (fun x => ⨅ y, f x y) ∧ ∃ σ : X → Y, Measurable σ ∧ ∀ x, f x (σ x) = ⨅ y, f x y := by
  have hv : Measurable (fun x => ⨅ y, f x y) := by
    have h := measurable_biInf_open f D hD hmeas happ isOpen_univ
    have e : (fun x => ⨅ y ∈ (univ : Set Y), f x y) = fun x => ⨅ y, f x y := funext fun x => iInf_univ
    rwa [e] at h
  refine ⟨hv, ?_⟩
  set A : X → Set Y := fun x => {y | f x y ≤ ⨅ y, f x y} with hAdef
  have hcl : ∀ x, IsClosed (A x) := fun x => (hlsc x).isClosed_preimage _
  have hmin : ∀ x (K : Set Y), IsClosed K → K.Nonempty → ∃ y ∈ K, ∀ z ∈ K, f x y ≤ f x z := by
    intro x K hK hne
    obtain ⟨y, hy, hm⟩ := ((hlsc x).lowerSemicontinuousOn K).exists_isMinOn hne hK.isCompact
    exact ⟨y, hy, fun z hz => hm hz⟩
  have hne : ∀ x, (A x).Nonempty := by
    intro x
    obtain ⟨y, -, hy⟩ := hmin x univ isClosed_univ univ_nonempty
    exact ⟨y, le_iInf fun z => hy z trivial⟩
  have hF : ∀ F : Set Y, IsClosed F → MeasurableSet {x | (A x ∩ F).Nonempty} := by
    intro F hF
    rcases F.eq_empty_or_nonempty with rfl | hFne
    · simp
    have e : {x | (A x ∩ F).Nonempty} =
        ⋂ j : ℕ, {x | ⨅ y ∈ thickening (1 / ((j : ℝ) + 1)) F, f x y ≤ ⨅ y, f x y} := by
      ext x
      simp only [mem_setOf_eq, mem_iInter]
      constructor
      · rintro ⟨y, hyA, hyF⟩ j
        exact (biInf_le (fun y => f x y) (self_subset_thickening (by positivity) F hyF)).trans hyA
      · intro h
        set S : ℕ → Set Y := fun j => A x ∩ cthickening (1 / ((j : ℝ) + 1)) F with hS
        have hSn : ∀ j, (S j).Nonempty := by
          intro j
          obtain ⟨y, hy, hymin⟩ := hmin x (cthickening (1 / ((j : ℝ) + 1)) F) isClosed_cthickening
            (hFne.mono (self_subset_cthickening F))
          refine ⟨y, ?_, hy⟩
          refine le_trans ?_ (h j)
          exact le_iInf₂ fun z hz => hymin z (thickening_subset_cthickening _ _ hz)
        have hSd : ∀ j, S (j + 1) ⊆ S j := by
          intro j
          refine inter_subset_inter_right _ (cthickening_mono ?_ F)
          gcongr
          push_cast
          linarith
        obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hSd hSn
          ((hcl x).inter isClosed_cthickening).isCompact fun j => (hcl x).inter isClosed_cthickening
        simp only [mem_iInter] at hz
        refine ⟨z, (hz 0).1, ?_⟩
        rw [← hF.closure_eq, closure_eq_iInter_cthickening]
        simp only [mem_iInter]
        intro δ hδ
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
        exact cthickening_mono hj.le F (hz j).2
    rw [e]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le (measurable_biInf_open f D hD hmeas happ isOpen_thickening) hv
  have hball : ∀ (c : Y) (r : ℝ), MeasurableSet {x | (A x ∩ ball c r).Nonempty} := by
    intro c r
    have e : {x | (A x ∩ ball c r).Nonempty} =
        ⋃ k : ℕ, {x | (A x ∩ closedBall c (r - 1 / ((k : ℝ) + 1))).Nonempty} := by
      ext x
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨y, hyA, hy⟩
        rw [mem_ball] at hy
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
        exact ⟨k, y, hyA, by rw [mem_closedBall]; linarith⟩
      · rintro ⟨k, y, hyA, hy⟩
        rw [mem_closedBall] at hy
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        exact ⟨y, hyA, by rw [mem_ball]; linarith⟩
    rw [e]
    exact MeasurableSet.iUnion fun k => hF _ isClosed_closedBall
  obtain ⟨σ, hσm, hσ⟩ := exists_measurable_selector A hcl hne hball
  exact ⟨σ, hσm, fun x => le_antisymm (hσ x) (iInf_le _ _)⟩

/-- **Measurable maximum theorem, Carathéodory case** (Aliprantis–Border 18.19): `f · y` measurable for every `y`,
`f x ·` continuous; then `x ↦ min_y f x y` is measurable and has a measurable minimiser. -/
theorem exists_measurable_argmin [Nonempty Y] (f : X → Y → β) (hmeas : ∀ y, Measurable fun x => f x y)
    (hcont : ∀ x, Continuous (f x)) :
    Measurable (fun x => ⨅ y, f x y) ∧ ∃ σ : X → Y, Measurable σ ∧ ∀ x, f x (σ x) = ⨅ y, f x y := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense Y
  refine exists_measurable_argmin_of_approx f D hDc (fun y _ => hmeas y)
    (fun x => (hcont x).lowerSemicontinuous) fun y => ?_
  have hy : y ∈ closure D := hDd.closure_eq ▸ mem_univ y
  obtain ⟨u, huD, hu⟩ := mem_closure_iff_seq_limit.1 hy
  exact ⟨u, huD, hu, fun x => ((hcont x).tendsto y).comp hu⟩

end Main

section Corollaries

variable {X Y : Type*} [MeasurableSpace X] [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **Real-valued Carathéodory argmin.** `f · y` measurable, `f x ·` continuous on the compact metric `Y`: a measurable
minimiser `σ`, and the minimum value `x ↦ ⨅ y, f x y` is measurable and attained at `σ x`. -/
theorem exists_measurable_argmin_real [Nonempty Y] (f : X → Y → ℝ) (hmeas : ∀ y, Measurable fun x => f x y)
    (hcont : ∀ x, Continuous (f x)) :
    ∃ σ : X → Y, Measurable σ ∧ (∀ x y, f x (σ x) ≤ f x y) ∧ (∀ x, f x (σ x) = ⨅ y, f x y) ∧
      Measurable (fun x => ⨅ y, f x y) := by
  obtain ⟨-, σ, hσm, hσ⟩ := exists_measurable_argmin (β := EReal) (fun x y => (f x y : EReal))
    (fun y => measurable_coe_real_ereal.comp (hmeas y)) fun x => continuous_coe_real_ereal.comp (hcont x)
  have hle : ∀ x y, f x (σ x) ≤ f x y := fun x y => by
    have := (hσ x).trans_le (iInf_le _ y)
    exact EReal.coe_le_coe_iff.1 this
  have heq : ∀ x, f x (σ x) = ⨅ y, f x y := fun x =>
    le_antisymm (le_ciInf fun y => hle x y) (ciInf_le ⟨f x (σ x), forall_mem_range.2 (hle x)⟩ _)
  have hjoint : Measurable (Function.uncurry fun (y : Y) (x : X) => f x y) :=
    measurable_uncurry_of_continuous_of_measurable (fun x => hcont x) hmeas
  have hval : Measurable fun x => f x (σ x) :=
    hjoint.comp (hσm.prodMk measurable_id)
  refine ⟨σ, hσm, hle, heq, ?_⟩
  have e : (fun x => ⨅ y, f x y) = fun x => f x (σ x) := funext fun x => (heq x).symm
  rw [e]; exact hval

/-- **Argmin with an `x`-independent lower semicontinuous penalty** (`ℝ≥0∞`-valued): `g` Carathéodory, `h` lower
semicontinuous. Then `x ↦ min_y (g x y + h y)` is measurable and has a measurable minimiser. -/
theorem exists_measurable_argmin_add [Nonempty Y] (g : X → Y → ℝ≥0∞) (h : Y → ℝ≥0∞)
    (hmeas : ∀ y, Measurable fun x => g x y) (hcont : ∀ x, Continuous (g x)) (hlsc : LowerSemicontinuous h) :
    Measurable (fun x => ⨅ y, (g x y + h y)) ∧
      ∃ σ : X → Y, Measurable σ ∧ ∀ x y, g x (σ x) + h (σ x) ≤ g x y + h y := by
  obtain ⟨D, hDc, hD⟩ := exists_countable_approx_graph h
  obtain ⟨hv, σ, hσm, hσ⟩ := exists_measurable_argmin_of_approx (fun x y => g x y + h y) D hDc
    (fun y _ => (hmeas y).add_const _) (fun x => (hcont x).lowerSemicontinuous.add hlsc) fun y => by
      obtain ⟨u, huD, hu, hhu⟩ := hD y
      exact ⟨u, huD, hu, fun x => (((hcont x).tendsto y).comp hu).add hhu⟩
  exact ⟨hv, σ, hσm, fun x y => (hσ x).trans_le (iInf_le (fun y => g x y + h y) y)⟩

end Corollaries

section Constraint

variable {X E : Type*} [MeasurableSpace X] [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- **Argmin over a fixed compact constraint set** `K` of a metric space (Carathéodory on `K`): a measurable
`σ : X → E` with values in `K` minimising `f x` over `K`; the minimum `x ↦ ⨅ y : K, f x y` is measurable. -/
theorem exists_measurable_argmin_on (K : Set E) (hK : IsCompact K) (hKne : K.Nonempty) (f : X → E → ℝ)
    (hmeas : ∀ y ∈ K, Measurable fun x => f x y) (hcont : ∀ x, ContinuousOn (f x) K) :
    ∃ σ : X → E, Measurable σ ∧ (∀ x, σ x ∈ K) ∧ (∀ x, ∀ y ∈ K, f x (σ x) ≤ f x y) ∧
      Measurable (fun x => ⨅ y : K, f x y) ∧ ∀ x, f x (σ x) = ⨅ y : K, f x y := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Nonempty K := hKne.to_subtype
  obtain ⟨σ, hσm, hle, heq, hv⟩ := exists_measurable_argmin_real (X := X) (Y := K) (fun x y => f x y)
    (fun y => hmeas y y.2) fun x => (hcont x).domRestrict
  exact ⟨fun x => σ x, measurable_subtype_coe.comp hσm, fun x => (σ x).2, fun x y hy => hle x ⟨y, hy⟩, hv,
    heq⟩

/-- **Argmin over a fixed compact constraint set**, values in a complete linear order `β` (`ℝ≥0∞`, `EReal`). -/
theorem exists_measurable_argmin_on' {β : Type*} [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [SecondCountableTopology β] [MeasurableSpace β] [BorelSpace β] (K : Set E) (hK : IsCompact K)
    (hKne : K.Nonempty) (f : X → E → β) (hmeas : ∀ y ∈ K, Measurable fun x => f x y)
    (hcont : ∀ x, ContinuousOn (f x) K) :
    ∃ σ : X → E, Measurable σ ∧ (∀ x, σ x ∈ K) ∧ ∀ x, ∀ y ∈ K, f x (σ x) ≤ f x y := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Nonempty K := hKne.to_subtype
  obtain ⟨-, σ, hσm, hσ⟩ := exists_measurable_argmin (X := X) (Y := K) (β := β) (fun x y => f x y)
    (fun y => hmeas y y.2) fun x => (hcont x).domRestrict
  exact ⟨fun x => σ x, measurable_subtype_coe.comp hσm, fun x => (σ x).2, fun x y hy =>
    (hσ x).trans_le (iInf_le (fun y : K => f x y) ⟨y, hy⟩)⟩

end Constraint

end StatFormal.Foundations.MeasurableSelection
