import StatFormal.Lib.Potentials.HilbertUniqueness
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Moment-free uniqueness of couplings carried by subdifferential graphs (McCann's argument in `H`)

Library component (McCann–GHS uniqueness without moments). Untrusted library code; no frozen
statement is touched.

Let `H` be a separable real Hilbert space, `μ` a Borel probability on `H` null on every Lipschitz
hypersurface and `ν` any Borel probability. If two couplings `π₁, π₂ ∈ Π(μ, ν)` are carried by the
subdifferential graphs `∂φ₁`, `∂φ₂` of two **finite continuous** functions `φ₁, φ₂ : H → ℝ`, then
`π₁ = π₂` (and it is a graph plan). No moment of `μ` or `ν` is assumed.

## Proof (McCann 1995, adapted; no integration of the cost)

With the conjugates `φᵢ*(y) = sup_x ⟪x, y⟫ − φᵢ(x)` (in `EReal`, lower semicontinuous, hence Borel),
`φᵢ(x) + φᵢ*(y) = ⟪x, y⟫` on `∂φᵢ` and `≥` everywhere (Fenchel–Young). Put `u = φ₁ − φ₂` and
`v = φ₂* − φ₁*` (finite `ν`-a.e.). Then `u(x) ≤ v(y)` `π₁`-a.e. and `v(y) ≤ u(x)` `π₂`-a.e. Since
`u(x)` has law `u#μ` and `v(y)` has law `v#ν` under both couplings, the two inequalities force the
tails `μ{u > t} = ν{v > t}` for all `t`, and then `u(x) = v(y)` a.e. under both
(`ae_le_of_coupling`: a pointwise inequality between two random variables of equal tails is an a.e.
equality). Under `π₂` this says `φ₁(x) + φ₁*(y) = ⟪x, y⟫`, i.e. `π₂` is carried by `∂φ₁` too.
`∂φ₁` is a closed monotone set, single-valued off a `μ`-null union of Lipschitz hypersurfaces
(`Potentials.measure_multivaluedSet_eq_zero`), so `π₁ = π₂` is the graph plan of a Borel map
(`Potentials.exists_eq_graphPlan_of_ae_mem`).

Only the *laws* of the scalar random variables `u(x)` and `v(y)` are compared, so no integrability
is needed: this replaces the integrated cost `(M‖x‖ − ⟪x, y⟫)₊` (which needs `m₁(μ) < ∞`) of
the first-moment proof.

## Main results

* `ae_le_of_coupling` (the tail lemma), `measurable_conj`, `conj_eq_of_mem_subgradGraph`;
* `eq_of_ae_mem_subgradGraph`: two couplings of `(μ, ν)` carried by subdifferential graphs of
  finite continuous functions coincide (`μ` null on Lipschitz hypersurfaces).

## References

* R. J. McCann, *Existence and uniqueness of monotone measure-preserving maps*, Duke Math. J. 80
  (1995), the comparison of `φ*` along two maps with the same image law;
* González-Sanz, Hallin, Sen (GHS), Cor. 2.7.
-/

open Filter MeasureTheory Metric Set TauCeti
open scoped ENNReal NNReal Topology InnerProductSpace RealInnerProductSpace

namespace StatFormal.McCannH

/-! ### The tail lemma -/

section Tail

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- **Equal tails force equality.** If `π₁, π₂ ∈ Π(μ, ν)`, `u(x) ≤ v(y)` `π₁`-a.e. and
`v(y) ≤ u(x)` `π₂`-a.e., then `v(y) ≤ u(x)` also `π₁`-a.e. (so `u(x) = v(y)` `π₁`-a.e.). -/
theorem ae_le_of_coupling {μ : Measure X} {ν : Measure Y} {π₁ π₂ : Measure (X × Y)}
    [IsFiniteMeasure π₁] (h₁ : IsCoupling π₁ μ ν) (h₂ : IsCoupling π₂ μ ν) {u : X → ℝ}
    {v : Y → ℝ} (hu : Measurable u) (hv : Measurable v) (hle₁ : ∀ᵐ z ∂π₁, u z.1 ≤ v z.2)
    (hle₂ : ∀ᵐ z ∂π₂, v z.2 ≤ u z.1) : ∀ᵐ z ∂π₁, v z.2 ≤ u z.1 := by
  have key : ∀ t : ℝ, π₁ ({z : X × Y | t < v z.2} \ {z | t < u z.1}) = 0 := by
    intro t
    have hu' : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu
    have hv' : MeasurableSet {y | t < v y} := measurableSet_lt measurable_const hv
    have hA : MeasurableSet {z : X × Y | t < u z.1} := measurable_fst hu'
    have eA₁ : π₁ {z : X × Y | t < u z.1} = μ {x | t < u x} := by
      rw [← h₁.fst_eq, Measure.fst_apply hu']; rfl
    have eA₂ : π₂ {z : X × Y | t < u z.1} = μ {x | t < u x} := by
      rw [← h₂.fst_eq, Measure.fst_apply hu']; rfl
    have eB₁ : π₁ {z : X × Y | t < v z.2} = ν {y | t < v y} := by
      rw [← h₁.snd_eq, Measure.snd_apply hv']; rfl
    have eB₂ : π₂ {z : X × Y | t < v z.2} = ν {y | t < v y} := by
      rw [← h₂.snd_eq, Measure.snd_apply hv']; rfl
    have hBA₂ : π₂ {z : X × Y | t < v z.2} ≤ π₂ {z | t < u z.1} :=
      measure_mono_ae (hle₂.mono fun z hz hzB => lt_of_lt_of_le hzB hz)
    have hAB₁ : {z : X × Y | t < u z.1} ≤ᵐ[π₁] {z | t < v z.2} :=
      hle₁.mono fun z hz hzA => lt_of_lt_of_le hzA hz
    have hinter : π₁ ({z : X × Y | t < v z.2} ∩ {z | t < u z.1}) = π₁ {z | t < u z.1} := by
      refine measure_congr ?_
      filter_upwards [hAB₁] with z hz
      apply propext
      exact ⟨fun h => h.2, fun h => ⟨hz h, h⟩⟩
    have hsplit := measure_inter_add_sdiff {z : X × Y | t < v z.2} hA (μ := π₁)
    rw [hinter] at hsplit
    have hle : π₁ {z : X × Y | t < u z.1} + π₁ ({z : X × Y | t < v z.2} \ {z | t < u z.1}) ≤
        π₁ {z : X × Y | t < u z.1} + 0 := by
      rw [hsplit, add_zero, eB₁, ← eB₂, eA₁, ← eA₂]; exact hBA₂
    exact le_antisymm ((ENNReal.add_le_add_iff_left (measure_ne_top _ _)).1 hle) zero_le
  have hnull : π₁ (⋃ q : ℚ, {z : X × Y | (q : ℝ) < v z.2} \ {z | (q : ℝ) < u z.1}) = 0 :=
    measure_iUnion_null fun q => key q
  refine (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun z hz => ?_
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  exact hz (mem_iUnion.2 ⟨q, hq2, fun h => lt_irrefl _ (h.trans hq1)⟩)

end Tail

/-! ### Conjugates and subdifferential graphs -/

section Conj

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Legendre–Fenchel conjugate `φ*(y) = sup_x ⟪x, y⟫ − φ(x)`, in `EReal`. -/
noncomputable def conj (φ : H → ℝ) (y : H) : EReal := ⨆ x, ((⟪x, y⟫ - φ x : ℝ) : EReal)

/-- The (global) subdifferential graph `{(x, y) : φ(x) + ⟪y, x' − x⟫ ≤ φ(x') ∀ x'}`. -/
def subgradGraph (φ : H → ℝ) : Set (H × H) := {z | ∀ x, φ z.1 + ⟪z.2, x - z.1⟫ ≤ φ x}

theorem le_conj (φ : H → ℝ) (x y : H) : ((⟪x, y⟫ - φ x : ℝ) : EReal) ≤ conj φ y :=
  le_iSup (fun x => ((⟪x, y⟫ - φ x : ℝ) : EReal)) x

theorem conj_ne_bot (φ : H → ℝ) (y : H) : conj φ y ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_conj φ 0 y)

/-- On the subdifferential graph the Fenchel–Young inequality is an equality. -/
theorem conj_eq_of_mem_subgradGraph {φ : H → ℝ} {z : H × H} (hz : z ∈ subgradGraph φ) :
    conj φ z.2 = ((⟪z.1, z.2⟫ - φ z.1 : ℝ) : EReal) := by
  refine le_antisymm (iSup_le fun x => ?_) (le_conj φ z.1 z.2)
  rw [EReal.coe_le_coe_iff]
  have h := hz x
  rw [inner_sub_right] at h
  have e1 := real_inner_comm x z.2
  have e2 := real_inner_comm z.1 z.2
  linarith

/-- Equality in Fenchel–Young puts the pair on the subdifferential graph. -/
theorem mem_subgradGraph_of_conj_le {φ : H → ℝ} {z : H × H}
    (hz : conj φ z.2 ≤ ((⟪z.1, z.2⟫ - φ z.1 : ℝ) : EReal)) : z ∈ subgradGraph φ := by
  intro x
  have h := (le_conj φ x z.2).trans hz
  rw [EReal.coe_le_coe_iff] at h
  rw [inner_sub_right]
  have e1 := real_inner_comm x z.2
  have e2 := real_inner_comm z.1 z.2
  linarith

/-- Subdifferential graphs are monotone. -/
theorem isMonotoneSet_subgradGraph (φ : H → ℝ) :
    StatFormal.Potentials.IsMonotoneSet (subgradGraph φ) := by
  intro p hp q hq
  have h1 := hp q.1
  have h2 := hq p.1
  have e : ⟪p.2 - q.2, p.1 - q.1⟫ = -(⟪p.2, q.1 - p.1⟫ + ⟪q.2, p.1 - q.1⟫) := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [e]
  linarith

theorem isClosed_subgradGraph {φ : H → ℝ} (hφ : Continuous φ) : IsClosed (subgradGraph φ) := by
  simp only [subgradGraph, Set.ofPred_forall]
  refine isClosed_iInter fun x => isClosed_le ?_ continuous_const
  exact (hφ.comp continuous_fst).add (continuous_snd.inner (continuous_const.sub continuous_fst))

theorem lowerSemicontinuous_conj (φ : H → ℝ) : LowerSemicontinuous (conj φ) := by
  refine lowerSemicontinuous_iSup fun x => ?_
  exact (continuous_coe_real_ereal.comp
    ((continuous_const.inner continuous_id).sub continuous_const)).lowerSemicontinuous

theorem measurable_conj [MeasurableSpace H] [OpensMeasurableSpace H] (φ : H → ℝ) :
    Measurable (conj φ) :=
  (lowerSemicontinuous_conj φ).measurable

theorem le_toReal_conj {φ : H → ℝ} {y : H} (hy : conj φ y ≠ ⊤) (x : H) :
    ⟪x, y⟫ - φ x ≤ (conj φ y).toReal := by
  have h := le_conj φ x y
  rw [← EReal.coe_toReal hy (conj_ne_bot φ y), EReal.coe_le_coe_iff] at h
  exact h

theorem toReal_conj_of_mem {φ : H → ℝ} {z : H × H} (hz : z ∈ subgradGraph φ) :
    (conj φ z.2).toReal = ⟪z.1, z.2⟫ - φ z.1 := by
  rw [conj_eq_of_mem_subgradGraph hz, EReal.toReal_coe]

end Conj

/-! ### Uniqueness -/

section Uniq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- If `π` is carried by `∂φ`, then `φ*` is finite `ν`-a.e., hence along any coupling `π'` of
`(μ, ν)`. -/
theorem ae_conj_ne_top {μ ν : Measure H} {π π' : Measure (H × H)} (hπ : IsCoupling π μ ν)
    (hπ' : IsCoupling π' μ ν) {φ : H → ℝ} (hφ : ∀ᵐ z ∂π, z ∈ subgradGraph φ) :
    ∀ᵐ z ∂π', conj φ z.2 ≠ ⊤ := by
  have hN : MeasurableSet {y : H | conj φ y = ⊤} :=
    measurable_conj φ (measurableSet_singleton ⊤)
  have h0 : ν {y : H | conj φ y = ⊤} = 0 := by
    rw [← hπ.snd_eq, Measure.snd_apply hN]
    refine measure_eq_zero_iff_ae_notMem.2 (hφ.mono fun z hz hzN => ?_)
    have hzN' : conj φ z.2 = ⊤ := hzN
    rw [conj_eq_of_mem_subgradGraph hz] at hzN'
    exact EReal.coe_ne_top _ hzN'
  rw [← hπ'.snd_eq, Measure.snd_apply hN] at h0
  exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun z hz => hz

/-- **Moment-free McCann–GHS uniqueness in a separable Hilbert space.** Let `μ` be a finite Borel
measure null on every Lipschitz hypersurface, `ν` a Borel measure, and `π₁, π₂ ∈ Π(μ, ν)` carried by
the subdifferential graphs of finite continuous `φ₁, φ₂ : H → ℝ`. Then `π₁ = π₂`. No moment of
`μ` or `ν` is used. -/
theorem eq_of_ae_mem_subgradGraph {μ ν : Measure H} [IsFiniteMeasure μ]
    (hμ : ∀ S : Set H, StatFormal.Potentials.IsLipGraph S → μ S = 0) {π₁ π₂ : Measure (H × H)}
    (h₁ : IsCoupling π₁ μ ν) (h₂ : IsCoupling π₂ μ ν) {φ₁ φ₂ : H → ℝ} (hφ₁ : Continuous φ₁)
    (hφ₂ : Continuous φ₂) (hπ₁ : ∀ᵐ z ∂π₁, z ∈ subgradGraph φ₁)
    (hπ₂ : ∀ᵐ z ∂π₂, z ∈ subgradGraph φ₂) : π₁ = π₂ := by
  have : IsFiniteMeasure π₁ := h₁.isFiniteMeasure
  have : IsFiniteMeasure π₂ := h₂.isFiniteMeasure
  set u : H → ℝ := fun x => φ₁ x - φ₂ x with hudef
  set v : H → ℝ := fun y => (conj φ₂ y).toReal - (conj φ₁ y).toReal with hvdef
  have hu : Measurable u := (hφ₁.sub hφ₂).measurable
  have hv : Measurable v :=
    (measurable_conj φ₂).ereal_toReal.sub (measurable_conj φ₁).ereal_toReal
  have hle₁ : ∀ᵐ z ∂π₁, u z.1 ≤ v z.2 := by
    filter_upwards [hπ₁, ae_conj_ne_top h₂ h₁ hπ₂] with z hz hfin
    have e := toReal_conj_of_mem hz
    have h := le_toReal_conj hfin z.1
    simp only [hudef, hvdef]
    linarith
  have hle₂ : ∀ᵐ z ∂π₂, v z.2 ≤ u z.1 := by
    filter_upwards [hπ₂, ae_conj_ne_top h₁ h₂ hπ₁] with z hz hfin
    have e := toReal_conj_of_mem hz
    have h := le_toReal_conj hfin z.1
    simp only [hudef, hvdef]
    linarith
  have hge₂ : ∀ᵐ z ∂π₂, u z.1 ≤ v z.2 := by
    have := ae_le_of_coupling h₂ h₁ (u := fun x => -u x) (v := fun y => -v y) hu.neg hv.neg
      (hle₂.mono fun z hz => neg_le_neg hz) (hle₁.mono fun z hz => neg_le_neg hz)
    exact this.mono fun z hz => neg_le_neg_iff.1 hz
  have hπ₂' : ∀ᵐ z ∂π₂, z ∈ subgradGraph φ₁ := by
    filter_upwards [hπ₂, ae_conj_ne_top h₁ h₂ hπ₁, hge₂] with z hz hfin hge
    refine mem_subgradGraph_of_conj_le ?_
    rw [← EReal.coe_toReal hfin (conj_ne_bot φ₁ z.2), EReal.coe_le_coe_iff]
    have e := toReal_conj_of_mem hz
    simp only [hudef, hvdef] at hge
    linarith
  set Γ := subgradGraph φ₁
  have hΓm : MeasurableSet Γ := (isClosed_subgradGraph hφ₁).measurableSet
  have hM : μ (StatFormal.Potentials.multivaluedSet Γ) = 0 :=
    StatFormal.Potentials.measure_multivaluedSet_eq_zero hμ (isMonotoneSet_subgradGraph φ₁)
  obtain ⟨T, -, hπT, hTΓ⟩ := StatFormal.Potentials.exists_eq_graphPlan_of_ae_mem h₁ hΓm hπ₁ hM
  obtain ⟨T', -, hπT', hTΓ'⟩ := StatFormal.Potentials.exists_eq_graphPlan_of_ae_mem h₂ hΓm hπ₂' hM
  have hTT' : T =ᵐ[μ] T' := by
    filter_upwards [hTΓ, hTΓ', measure_eq_zero_iff_ae_notMem.1 hM] with x h1 h2 hx
    by_contra hne
    exact hx ⟨_, _, h1, h2, hne⟩
  rw [hπT, hπT', graphPlan_congr hTT']

end Uniq

end StatFormal.McCannH
