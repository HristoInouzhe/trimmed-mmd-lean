import StatFormal.Lib.McCannH.Uniqueness
import StatFormal.Archive.Wave23d.RouteCM

/-!
# Moment-free uniqueness with extended-valued potentials (McCann's argument in `H`, general targets)

Library component (McCann–GHS uniqueness without moments and without bounded targets). Untrusted library code;
no frozen statement is touched.

`Uniqueness.lean` runs McCann's comparison for **finite** continuous potentials, which Rockafellar's construction
gives only for bounded slopes (bounded targets). Here the potentials may take the value `+∞`: a potential is a pair
`(D, φ)` of a Borel "domain" `D ⊆ H` and a Borel `φ : H → ℝ` (its values off `D` are irrelevant), and the
subdifferential graph *relative to* `D` is

  `∂_D φ = {(x, y) : x ∈ D, φ(x) + ⟪y, x' − x⟫ ≤ φ(x') for all x' ∈ D}`.

With the relative conjugate `φ*_D(y) = sup_{x ∈ D} ⟪x, y⟫ − φ(x)` (in `EReal`, lower semicontinuous), Fenchel–Young
holds on `D × H` and is an equality on `∂_D φ`. McCann's argument goes through verbatim: if `π₁, π₂ ∈ Π(μ, ν)` are
carried by `∂_{D₁} φ₁`, `∂_{D₂} φ₂`, then `D₁, D₂` are `μ`-conull (marginals), `φᵢ*` are finite `ν`-a.e., and
`u = φ₁ − φ₂` (on `D₁ ∩ D₂`), `v = φ₂* − φ₁*` satisfy `u(x) ≤ v(y)` `π₁`-a.e. and `v(y) ≤ u(x)` `π₂`-a.e.; the tail
lemma (`ae_le_of_coupling`) gives equality, so `π₂` is carried by `∂_{D₁} φ₁`, a Borel monotone set; single-valued
off a `μ`-null set for `μ` null on Lipschitz hypersurfaces (`Potentials.measure_multivaluedSet_eq_zero` needs only
monotonicity, no interior of the domain), so `π₁ = π₂` is a graph plan.

Rockafellar's chain functional `f = sup_chains chainVal` (the certified wave-23d `chainVal`), taken in `EReal`, is
lower semicontinuous, `> −∞`, and `< +∞` on the first projection of the cyclically monotone set `Γ`; with
`D = {f < ∞}`, `φ = f.toReal`, every `(x, y) ∈ Γ` lies in `∂_D φ`. No moment and no bound on the target is used.

## Main results

* `eq_of_ae_mem_subgradGraphOn`: two couplings carried by relative subdifferential graphs of Borel potentials
  coincide (`μ` null on Lipschitz hypersurfaces);
* `exists_subgradGraphOn_of_cycMon`: every nonempty cyclically monotone `Γ` lies in some `∂_D φ` (Rockafellar,
  extended-valued).

## References

* R. J. McCann, *Existence and uniqueness of monotone measure-preserving maps*, Duke Math. J. 80 (1995);
* R. T. Rockafellar, *Convex Analysis* (1970), Thm 24.8; González-Sanz, Hallin, Sen, Cor. 2.7.
-/

set_option linter.style.longLine false

open Filter MeasureTheory Metric Set TauCeti
open scoped ENNReal NNReal Topology InnerProductSpace RealInnerProductSpace

namespace StatFormal.McCannH

/-! ### Relative conjugates and subdifferential graphs -/

section RelConj

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The conjugate relative to `D`: `φ*_D(y) = sup_{x ∈ D} ⟪x, y⟫ − φ(x)`, in `EReal`. -/
noncomputable def conjOn (D : Set H) (φ : H → ℝ) (y : H) : EReal :=
  ⨆ x : D, ((⟪(x : H), y⟫ - φ x : ℝ) : EReal)

/-- The subdifferential graph relative to `D`. -/
def subgradGraphOn (D : Set H) (φ : H → ℝ) : Set (H × H) :=
  {z | z.1 ∈ D ∧ ∀ x ∈ D, φ z.1 + ⟪z.2, x - z.1⟫ ≤ φ x}

theorem le_conjOn {D : Set H} (φ : H → ℝ) {x : H} (hx : x ∈ D) (y : H) :
    ((⟪x, y⟫ - φ x : ℝ) : EReal) ≤ conjOn D φ y :=
  le_iSup (fun x : D => ((⟪(x : H), y⟫ - φ x : ℝ) : EReal)) ⟨x, hx⟩

theorem conjOn_ne_bot {D : Set H} (φ : H → ℝ) {x : H} (hx : x ∈ D) (y : H) : conjOn D φ y ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_conjOn φ hx y)

theorem conjOn_eq_of_mem {D : Set H} {φ : H → ℝ} {z : H × H} (hz : z ∈ subgradGraphOn D φ) :
    conjOn D φ z.2 = ((⟪z.1, z.2⟫ - φ z.1 : ℝ) : EReal) := by
  refine le_antisymm (iSup_le fun x => ?_) (le_conjOn φ hz.1 z.2)
  rw [EReal.coe_le_coe_iff]
  have h := hz.2 x x.2
  rw [inner_sub_right] at h
  have e1 := real_inner_comm (x : H) z.2
  have e2 := real_inner_comm z.1 z.2
  linarith

theorem mem_subgradGraphOn_of_conjOn_le {D : Set H} {φ : H → ℝ} {z : H × H} (h1 : z.1 ∈ D)
    (hz : conjOn D φ z.2 ≤ ((⟪z.1, z.2⟫ - φ z.1 : ℝ) : EReal)) : z ∈ subgradGraphOn D φ := by
  refine ⟨h1, fun x hx => ?_⟩
  have h := (le_conjOn φ hx z.2).trans hz
  rw [EReal.coe_le_coe_iff] at h
  rw [inner_sub_right]
  have e1 := real_inner_comm x z.2
  have e2 := real_inner_comm z.1 z.2
  linarith

theorem subgradGraphOn_eq (D : Set H) (φ : H → ℝ) :
    subgradGraphOn D φ = {z | z.1 ∈ D ∧ conjOn D φ z.2 ≤ ((⟪z.1, z.2⟫ - φ z.1 : ℝ) : EReal)} := by
  ext z
  exact ⟨fun hz => ⟨hz.1, (conjOn_eq_of_mem hz).le⟩,
    fun hz => mem_subgradGraphOn_of_conjOn_le hz.1 hz.2⟩

/-- Relative subdifferential graphs are monotone. -/
theorem isMonotoneSet_subgradGraphOn (D : Set H) (φ : H → ℝ) :
    StatFormal.Potentials.IsMonotoneSet (subgradGraphOn D φ) := by
  intro p hp q hq
  have h1 := hp.2 q.1 hq.1
  have h2 := hq.2 p.1 hp.1
  have e : ⟪p.2 - q.2, p.1 - q.1⟫ = -(⟪p.2, q.1 - p.1⟫ + ⟪q.2, p.1 - q.1⟫) := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [e]
  linarith

theorem lowerSemicontinuous_conjOn (D : Set H) (φ : H → ℝ) : LowerSemicontinuous (conjOn D φ) := by
  refine lowerSemicontinuous_iSup fun x => ?_
  exact (continuous_coe_real_ereal.comp
    ((continuous_const.inner continuous_id).sub continuous_const)).lowerSemicontinuous

theorem measurable_conjOn [MeasurableSpace H] [OpensMeasurableSpace H] (D : Set H) (φ : H → ℝ) :
    Measurable (conjOn D φ) :=
  (lowerSemicontinuous_conjOn D φ).measurable

theorem le_toReal_conjOn {D : Set H} {φ : H → ℝ} {x y : H} (hy : conjOn D φ y ≠ ⊤) (hx : x ∈ D) :
    ⟪x, y⟫ - φ x ≤ (conjOn D φ y).toReal := by
  have h := le_conjOn φ hx y
  rw [← EReal.coe_toReal hy (conjOn_ne_bot φ hx y), EReal.coe_le_coe_iff] at h
  exact h

theorem toReal_conjOn_of_mem {D : Set H} {φ : H → ℝ} {z : H × H} (hz : z ∈ subgradGraphOn D φ) :
    (conjOn D φ z.2).toReal = ⟪z.1, z.2⟫ - φ z.1 := by
  rw [conjOn_eq_of_mem hz, EReal.toReal_coe]

end RelConj

/-! ### Uniqueness with relative potentials -/

section Uniq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

omit [CompleteSpace H] in
theorem measurableSet_subgradGraphOn {D : Set H} (hD : MeasurableSet D) {φ : H → ℝ} (hφ : Measurable φ) :
    MeasurableSet (subgradGraphOn D φ) := by
  rw [subgradGraphOn_eq]
  refine (measurable_fst hD).inter (measurableSet_le ((measurable_conjOn D φ).comp measurable_snd) ?_)
  exact measurable_coe_real_ereal.comp
    ((continuous_fst.inner continuous_snd).measurable.sub (hφ.comp measurable_fst))

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
  [BorelSpace H] in
/-- A first-coordinate property holding along one coupling of `(μ, ν)` holds along every coupling. -/
theorem ae_fst_mem_of_coupling {μ ν : Measure H} {π π' : Measure (H × H)} (hπ : IsCoupling π μ ν)
    (hπ' : IsCoupling π' μ ν) {D : Set H} (hD : MeasurableSet D) (h : ∀ᵐ z ∂π, z.1 ∈ D) :
    ∀ᵐ z ∂π', z.1 ∈ D := by
  have h0 : μ Dᶜ = 0 := by
    rw [← hπ.fst_eq, Measure.fst_apply hD.compl]
    exact measure_eq_zero_iff_ae_notMem.2 (h.mono fun z hz hzN => hzN hz)
  rw [← hπ'.fst_eq, Measure.fst_apply hD.compl] at h0
  exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun z hz => by simpa using hz

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- If `π` is carried by `∂_D φ`, then `φ*_D` is finite `ν`-a.e., hence along any coupling of `(μ, ν)`. -/
theorem ae_conjOn_ne_top {μ ν : Measure H} {π π' : Measure (H × H)} (hπ : IsCoupling π μ ν)
    (hπ' : IsCoupling π' μ ν) {D : Set H} {φ : H → ℝ} (hφ : ∀ᵐ z ∂π, z ∈ subgradGraphOn D φ) :
    ∀ᵐ z ∂π', conjOn D φ z.2 ≠ ⊤ := by
  have hN : MeasurableSet {y : H | conjOn D φ y = ⊤} :=
    measurable_conjOn D φ (measurableSet_singleton ⊤)
  have h0 : ν {y : H | conjOn D φ y = ⊤} = 0 := by
    rw [← hπ.snd_eq, Measure.snd_apply hN]
    refine measure_eq_zero_iff_ae_notMem.2 (hφ.mono fun z hz hzN => ?_)
    have hzN' : conjOn D φ z.2 = ⊤ := hzN
    rw [conjOn_eq_of_mem hz] at hzN'
    exact EReal.coe_ne_top _ hzN'
  rw [← hπ'.snd_eq, Measure.snd_apply hN] at h0
  exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun z hz => hz

/-- **Moment-free McCann–GHS uniqueness, extended-valued potentials.** Let `μ` be a finite Borel measure null on
every Lipschitz hypersurface, `ν` a Borel measure, and `π₁, π₂ ∈ Π(μ, ν)` carried by relative subdifferential
graphs `∂_{D₁} φ₁`, `∂_{D₂} φ₂` of Borel potentials on Borel domains. Then `π₁ = π₂`. No moment and no bound on `ν`
is used. -/
theorem eq_of_ae_mem_subgradGraphOn {μ ν : Measure H} [IsFiniteMeasure μ]
    (hμ : ∀ S : Set H, StatFormal.Potentials.IsLipGraph S → μ S = 0) {π₁ π₂ : Measure (H × H)}
    (h₁ : IsCoupling π₁ μ ν) (h₂ : IsCoupling π₂ μ ν) {D₁ D₂ : Set H} (hD₁ : MeasurableSet D₁)
    (hD₂ : MeasurableSet D₂) {φ₁ φ₂ : H → ℝ} (hφ₁ : Measurable φ₁) (hφ₂ : Measurable φ₂)
    (hπ₁ : ∀ᵐ z ∂π₁, z ∈ subgradGraphOn D₁ φ₁) (hπ₂ : ∀ᵐ z ∂π₂, z ∈ subgradGraphOn D₂ φ₂) :
    π₁ = π₂ := by
  have : IsFiniteMeasure π₁ := h₁.isFiniteMeasure
  have : IsFiniteMeasure π₂ := h₂.isFiniteMeasure
  have hD₂π₁ : ∀ᵐ z ∂π₁, z.1 ∈ D₂ := ae_fst_mem_of_coupling h₂ h₁ hD₂ (hπ₂.mono fun z hz => hz.1)
  have hD₁π₂ : ∀ᵐ z ∂π₂, z.1 ∈ D₁ := ae_fst_mem_of_coupling h₁ h₂ hD₁ (hπ₁.mono fun z hz => hz.1)
  set u : H → ℝ := fun x => φ₁ x - φ₂ x with hudef
  set v : H → ℝ := fun y => (conjOn D₂ φ₂ y).toReal - (conjOn D₁ φ₁ y).toReal with hvdef
  have hu : Measurable u := hφ₁.sub hφ₂
  have hv : Measurable v :=
    (measurable_conjOn D₂ φ₂).ereal_toReal.sub (measurable_conjOn D₁ φ₁).ereal_toReal
  have hle₁ : ∀ᵐ z ∂π₁, u z.1 ≤ v z.2 := by
    filter_upwards [hπ₁, ae_conjOn_ne_top h₂ h₁ hπ₂, hD₂π₁] with z hz hfin hD
    have e := toReal_conjOn_of_mem hz
    have h := le_toReal_conjOn hfin hD
    simp only [hudef, hvdef]
    linarith
  have hle₂ : ∀ᵐ z ∂π₂, v z.2 ≤ u z.1 := by
    filter_upwards [hπ₂, ae_conjOn_ne_top h₁ h₂ hπ₁, hD₁π₂] with z hz hfin hD
    have e := toReal_conjOn_of_mem hz
    have h := le_toReal_conjOn hfin hD
    simp only [hudef, hvdef]
    linarith
  have hge₂ : ∀ᵐ z ∂π₂, u z.1 ≤ v z.2 := by
    have := ae_le_of_coupling h₂ h₁ (u := fun x => -u x) (v := fun y => -v y) hu.neg hv.neg
      (hle₂.mono fun z hz => neg_le_neg hz) (hle₁.mono fun z hz => neg_le_neg hz)
    exact this.mono fun z hz => neg_le_neg_iff.1 hz
  have hπ₂' : ∀ᵐ z ∂π₂, z ∈ subgradGraphOn D₁ φ₁ := by
    filter_upwards [hπ₂, ae_conjOn_ne_top h₁ h₂ hπ₁, hge₂, hD₁π₂] with z hz hfin hge hD
    refine mem_subgradGraphOn_of_conjOn_le hD ?_
    rw [← EReal.coe_toReal hfin (conjOn_ne_bot φ₁ hD z.2), EReal.coe_le_coe_iff]
    have e := toReal_conjOn_of_mem hz
    simp only [hudef, hvdef] at hge
    linarith
  set Γ := subgradGraphOn D₁ φ₁
  have hΓm : MeasurableSet Γ := measurableSet_subgradGraphOn hD₁ hφ₁
  have hM : μ (StatFormal.Potentials.multivaluedSet Γ) = 0 :=
    StatFormal.Potentials.measure_multivaluedSet_eq_zero hμ (isMonotoneSet_subgradGraphOn D₁ φ₁)
  obtain ⟨T, -, hπT, hTΓ⟩ := StatFormal.Potentials.exists_eq_graphPlan_of_ae_mem h₁ hΓm hπ₁ hM
  obtain ⟨T', -, hπT', hTΓ'⟩ := StatFormal.Potentials.exists_eq_graphPlan_of_ae_mem h₂ hΓm hπ₂' hM
  have hTT' : T =ᵐ[μ] T' := by
    filter_upwards [hTΓ, hTΓ', measure_eq_zero_iff_ae_notMem.1 hM] with x h1 h2 hx
    by_contra hne
    exact hx ⟨_, _, h1, h2, hne⟩
  rw [hπT, hπT', graphPlan_congr hTT']

end Uniq

/-! ### Rockafellar's potential with values in `(−∞, +∞]` -/

section Rock

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

open StatFormal.Wave23d (chainVal chainVal_snoc chainVal_le)
open StatFormal.OTFD.WaveL1 (CycMon)

/-- Chains in `Γ` starting at `p₀`. -/
def RChain (Γ : Set (H × H)) (p₀ : H × H) : Type _ :=
  Σ n : ℕ, {w : Fin (n + 1) → H × H // w 0 = p₀ ∧ ∀ i, w i ∈ Γ}

/-- Rockafellar's chain functional in `EReal` (no bound on the slopes, so it may be `+∞`). -/
noncomputable def rockE (Γ : Set (H × H)) (p₀ : H × H) (x : H) : EReal :=
  ⨆ c : RChain Γ p₀, ((chainVal c.2.1 x : ℝ) : EReal)

theorem continuous_chainVal {n : ℕ} (w : Fin (n + 1) → H × H) : Continuous (chainVal w) := by
  have e : chainVal w = fun x => ⟪(w (Fin.last n)).2, x - (w (Fin.last n)).1⟫ +
      ∑ i : Fin n, ⟪(w i.castSucc).2, (w i.succ).1 - (w i.castSucc).1⟫ := rfl
  rw [e]
  exact (continuous_const.inner (continuous_id.sub continuous_const)).add continuous_const

variable {Γ : Set (H × H)} {p₀ : H × H}

theorem chainVal_le_rockE (c : RChain Γ p₀) (x : H) : ((chainVal c.2.1 x : ℝ) : EReal) ≤ rockE Γ p₀ x :=
  le_iSup (fun c : RChain Γ p₀ => ((chainVal c.2.1 x : ℝ) : EReal)) c

/-- Appending a point of `Γ` to a chain. -/
def RChain.snoc (c : RChain Γ p₀) (q : H × H) (hq : q ∈ Γ) : RChain Γ p₀ :=
  ⟨c.1 + 1, Fin.snoc c.2.1 q, by
      rw [show (0 : Fin (c.1 + 1 + 1)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc, c.2.2.1],
    fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact hq
      · rw [Fin.snoc_castSucc]; exact c.2.2.2 j⟩

theorem rockE_snoc (c : RChain Γ p₀) {q : H × H} (hq : q ∈ Γ) (z : H) :
    chainVal (c.snoc q hq).2.1 z = chainVal c.2.1 q.1 + ⟪q.2, z - q.1⟫ :=
  chainVal_snoc c.2.1 q z

theorem rockE_le_of_mem (hΓ : CycMon Γ) {q : H × H} (hq : q ∈ Γ) :
    rockE Γ p₀ q.1 ≤ ((-⟪q.2, p₀.1 - q.1⟫ : ℝ) : EReal) := by
  refine iSup_le fun c => ?_
  rw [EReal.coe_le_coe_iff]
  have h1 := rockE_snoc c hq p₀.1
  have h2 := chainVal_le hΓ (c.snoc q hq).2.2.2
  rw [(c.snoc q hq).2.2.1] at h2
  linarith

theorem rockE_ne_top_of_mem (hΓ : CycMon Γ) {q : H × H} (hq : q ∈ Γ) : rockE Γ p₀ q.1 ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (rockE_le_of_mem hΓ hq)

theorem rockE_ne_bot (hp : p₀ ∈ Γ) (x : H) : rockE Γ p₀ x ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
    (chainVal_le_rockE (⟨0, fun _ => p₀, rfl, fun _ => hp⟩ : RChain Γ p₀) x)

theorem lowerSemicontinuous_rockE (Γ : Set (H × H)) (p₀ : H × H) : LowerSemicontinuous (rockE Γ p₀) :=
  lowerSemicontinuous_iSup fun c =>
    (continuous_coe_real_ereal.comp (continuous_chainVal c.2.1)).lowerSemicontinuous

/-- The subgradient inequality of the extended-valued potential, on its domain. -/
theorem rockE_subgrad (hp : p₀ ∈ Γ) (hΓ : CycMon Γ) {q : H × H} (hq : q ∈ Γ) {x : H}
    (hx : rockE Γ p₀ x ≠ ⊤) :
    (rockE Γ p₀ q.1).toReal + ⟪q.2, x - q.1⟫ ≤ (rockE Γ p₀ x).toReal := by
  have hle : rockE Γ p₀ q.1 ≤ (((rockE Γ p₀ x).toReal - ⟪q.2, x - q.1⟫ : ℝ) : EReal) := by
    refine iSup_le fun c => ?_
    rw [EReal.coe_le_coe_iff]
    have h1 := rockE_snoc c hq x
    have h2 := chainVal_le_rockE (c.snoc q hq) x
    rw [← EReal.coe_toReal hx (rockE_ne_bot hp x), EReal.coe_le_coe_iff] at h2
    linarith
  rw [← EReal.coe_toReal (rockE_ne_top_of_mem hΓ hq) (rockE_ne_bot hp q.1), EReal.coe_le_coe_iff] at hle
  linarith

/-- **Rockafellar, extended-valued.** Every nonempty cyclically monotone `Γ ⊆ H × H` lies in the relative
subdifferential graph `∂_D φ` of a Borel potential on a Borel domain (`D = {f < ∞}`, `φ = f.toReal`, `f` the
lower semicontinuous chain functional). No bound on the slopes. -/
theorem exists_subgradGraphOn_of_cycMon [MeasurableSpace H] [OpensMeasurableSpace H]
    (hΓ : CycMon Γ) (hne : Γ.Nonempty) :
    ∃ (D : Set H) (φ : H → ℝ), MeasurableSet D ∧ Measurable φ ∧ Γ ⊆ subgradGraphOn D φ := by
  obtain ⟨p₀, hp⟩ := hne
  have hm : Measurable (rockE Γ p₀) := (lowerSemicontinuous_rockE Γ p₀).measurable
  refine ⟨{x | rockE Γ p₀ x ≠ ⊤}, fun x => (rockE Γ p₀ x).toReal,
    (measurableSet_singleton (⊤ : EReal)).compl.preimage hm, hm.ereal_toReal, fun q hq => ?_⟩
  exact ⟨rockE_ne_top_of_mem hΓ hq, fun x hx => rockE_subgrad hp hΓ hq hx⟩

end Rock

end StatFormal.McCannH
