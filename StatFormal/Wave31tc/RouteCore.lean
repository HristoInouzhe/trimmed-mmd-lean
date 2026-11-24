import StatFormal.Wave31tc.Statements
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Separation.Hausdorff

set_option linter.style.longLine false

/-!
# Wave 31tc, route: the univariate core of `rem:qdens` (untrusted proof file)

Route (the printed proof, `jmlr/v3/appendix/D_trimming.tex:312-333`, specialised to `d = 1`):
1. `band_compact`: the band `{|h − t| ≤ |t|/2}` is compact (`h → 0` at `±∞`, `t ≠ 0`); so is `L = {h = t}`.
2. `level_finite`: the points of `L` are isolated (`h′ ≠ 0`, `HasDerivAt.eventually_ne`), so the compact `L` is finite.
3. `local_data`: near each `x ∈ L` the inverse function theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`) gives an open `V ∋ x`
   inside `U` and a given open `W`, on which `p > 0`, `h′ ≠ 0`, `h` is injective with open image, and a continuous local inverse `g`.
4. `formula_core`: the `V`'s are pairwise disjoint (T2 separation of the finite `L`); for small `r` every level `s ∈ [t−r,t+r]` lies in
   every `h(V_x)` (finite intersection of open sets around `t`) and `h⁻¹[t−r,t+r] ⊆ ⋃ V_x` (minimum of `|h − t|` on the compact band
   minus `⋃ V_x`); then `{h = s} = {g_x(s) : x ∈ L}`, `levelDens h p s = Σ_x p(g_x s)/|h′(g_x s)|`, continuous and positive, and the
   1-D change of variables (`lintegral_image_eq_lintegral_abs_deriv_mul`) on each `h⁻¹A ∩ V_x` gives the density; `c, C` are the
   minimum and the maximum of `levelDens` on `[t−r,t+r]`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave31tc.Core

variable {h p : ℝ → ℝ} {U : Set ℝ} {t : ℝ}

/-- The band `{|h − t| ≤ |t|/2}` is compact. -/
lemma band_compact (hc : Continuous h) (hT : Tendsto h atTop (𝓝 0)) (hB : Tendsto h atBot (𝓝 0)) (ht : t ≠ 0) :
    IsCompact {x | |h x - t| ≤ |t| / 2} := by
  have hpos : 0 < |t| / 2 := by positivity
  obtain ⟨a, ha⟩ := eventually_atTop.1 (hT.eventually (Metric.ball_mem_nhds 0 hpos))
  obtain ⟨b, hb⟩ := eventually_atBot.1 (hB.eventually (Metric.ball_mem_nhds 0 hpos))
  refine (isCompact_Icc (a := b) (b := a)).of_isClosed_subset
    (isClosed_le (by fun_prop) continuous_const) ?_
  intro x hx
  simp only [mem_ofPred_eq] at hx
  have key : |t| / 2 ≤ |h x| := by
    have h1 := abs_sub_abs_le_abs_sub t (h x)
    rw [abs_sub_comm] at h1
    linarith
  constructor
  · by_contra hlt
    push Not at hlt
    have h2 := hb x hlt.le
    rw [Real.dist_eq, sub_zero] at h2
    linarith
  · by_contra hlt
    push Not at hlt
    have h2 := ha x hlt.le
    rw [Real.dist_eq, sub_zero] at h2
    linarith

/-- The level set `L = {h = t}` is finite. -/
lemma level_finite (hh : ContDiff ℝ 1 h) (hT : Tendsto h atTop (𝓝 0)) (hB : Tendsto h atBot (𝓝 0)) (ht : t ≠ 0)
    (hd : ∀ x, h x = t → deriv h x ≠ 0) : {x | h x = t}.Finite := by
  have hc : Continuous h := hh.continuous
  have hK : IsCompact {x | h x = t} :=
    (band_compact hc hT hB ht).of_isClosed_subset (isClosed_eq hc continuous_const) (fun x hx => by
      simp only [mem_ofPred_eq] at hx ⊢
      rw [hx, sub_self, abs_zero]
      positivity)
  have hU : ∀ x ∈ {x | h x = t}, {z | z ≠ x → h z ≠ t} ∈ 𝓝 x := by
    intro x hx
    have hder : HasDerivAt h (deriv h x) x := ((hh.differentiable one_ne_zero) x).hasDerivAt
    have hev := hder.eventually_ne (c := t) (hd x hx)
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with z hz hzx
    exact hz hzx
  obtain ⟨F, -, hcov⟩ := hK.elim_nhds_subcover _ hU
  refine F.finite_toSet.subset ?_
  intro z hz
  obtain ⟨x, hxF, hzx⟩ := mem_iUnion₂.1 (hcov hz)
  by_contra hne
  have hzx' : z ≠ x := fun e => hne (e ▸ hxF)
  exact hzx hzx' hz

/-- Local data near a point `x` with `h′(x) ≠ 0`, `p` continuous on an open `U ∋ x` and `p(x) > 0`. -/
lemma local_data (hh : ContDiff ℝ 1 h) (hUo : IsOpen U) (hp : ContinuousOn p U) {x : ℝ} (hxU : x ∈ U)
    (hpx : 0 < p x) (hdx : deriv h x ≠ 0) {W : Set ℝ} (hWo : IsOpen W) (hxW : x ∈ W) :
    ∃ (V : Set ℝ) (g : ℝ → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ V ⊆ W ∧ (∀ z ∈ V, 0 < p z) ∧
      (∀ z ∈ V, deriv h z ≠ 0) ∧ InjOn h V ∧ IsOpen (h '' V) ∧ (∀ z ∈ V, g (h z) = z) ∧
      ContinuousOn g (h '' V) ∧ MapsTo g (h '' V) V := by
  have hs : HasStrictDerivAt h (deriv h x) x := hh.hasStrictDerivAt one_ne_zero
  have hsF := hs.hasStrictFDerivAt_equiv hdx
  set e := hsF.toOpenPartialHomeomorph h with he
  have hcoe : (e : ℝ → ℝ) = h := rfl
  have hcd : Continuous (deriv h) := hh.continuous_deriv le_rfl
  set V := e.source ∩ W ∩ (U ∩ p ⁻¹' Ioi 0) ∩ (deriv h) ⁻¹' {0}ᶜ with hVdef
  have hVo : IsOpen V :=
    ((e.open_source.inter hWo).inter (hp.isOpen_inter_preimage hUo isOpen_Ioi)).inter
      (isOpen_compl_singleton.preimage hcd)
  have hxV : x ∈ V := ⟨⟨⟨hsF.mem_toOpenPartialHomeomorph_source, hxW⟩, hxU, hpx⟩, hdx⟩
  have hVs : V ⊆ e.source := fun z hz => hz.1.1.1
  have hleft : ∀ z ∈ V, e.symm (h z) = z := fun z hz => e.left_inv (hVs hz)
  refine ⟨V, e.symm, hVo, hxV, fun z hz => hz.1.2.1, fun z hz => hz.1.1.2, fun z hz => hz.1.2.2,
    fun z hz => hz.2, ?_, ?_, hleft, ?_, ?_⟩
  · rw [← hcoe]; exact e.injOn.mono hVs
  · rw [← hcoe]; exact e.isOpen_image_of_subset_source hVo hVs
  · refine e.continuousOn_symm.mono ?_
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_source (hVs hz)
  · rintro _ ⟨z, hz, rfl⟩
    rw [hleft z hz]
    exact hz

/-- The explicit form: `L` finite, and on a window `[t−r,t+r]` the law of `h(X)` has the continuous density `levelDens h p`
with values in `[c, C]`, `c > 0`. -/
theorem formula_core (hh : ContDiff ℝ 1 h) (hT : Tendsto h atTop (𝓝 0)) (hB : Tendsto h atBot (𝓝 0))
    (ht : t ≠ 0) (hne : ∃ x, h x = t) (hd : ∀ x, h x = t → deriv h x ≠ 0)
    (hUo : IsOpen U) (hLU : {x | h x = t} ⊆ U) (hp : ContinuousOn p U) (hpos : ∀ x, h x = t → 0 < p x) :
    {x | h x = t}.Finite ∧
      ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ c ≤ C ∧
        (∀ x, h x ∈ Icc (t - r) (t + r) → deriv h x ≠ 0) ∧
        (∀ s ∈ Icc (t - r) (t + r), {x | h x = s}.Finite ∧ c ≤ levelDens h p s ∧ levelDens h p s ≤ C) ∧
        ContinuousOn (levelDens h p) (Icc (t - r) (t + r)) ∧
        ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (t - r) (t + r) →
          (volume.withDensity fun x => ENNReal.ofReal (p x)) (h ⁻¹' A) =
            ∫⁻ s in A, ENNReal.ofReal (levelDens h p s) := by
  set L := {x | h x = t} with hLdef
  have hc : Continuous h := hh.continuous
  have hcd : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hLfin : L.Finite := level_finite hh hT hB ht hd
  obtain ⟨W, hW, hWdisj⟩ := hLfin.t2_separation
  have hloc : ∀ x, ∃ (V : Set ℝ) (g : ℝ → ℝ), x ∈ L → (IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ V ⊆ W x ∧
      (∀ z ∈ V, 0 < p z) ∧ (∀ z ∈ V, deriv h z ≠ 0) ∧ InjOn h V ∧ IsOpen (h '' V) ∧
      (∀ z ∈ V, g (h z) = z) ∧ ContinuousOn g (h '' V) ∧ MapsTo g (h '' V) V) := by
    intro x
    by_cases hx : x ∈ L
    · obtain ⟨V, g, hV⟩ := local_data hh hUo hp (hLU hx) (hpos x hx) (hd x hx) (hW x).2 (hW x).1
      exact ⟨V, g, fun _ => hV⟩
    · exact ⟨∅, id, fun h' => absurd h' hx⟩
  choose V g hVg using hloc
  have hVopen : ∀ x ∈ L, IsOpen (V x) := fun x hx => (hVg x hx).1
  have hVmem : ∀ x ∈ L, x ∈ V x := fun x hx => (hVg x hx).2.1
  have hVU : ∀ x ∈ L, V x ⊆ U := fun x hx => (hVg x hx).2.2.1
  have hVW : ∀ x ∈ L, V x ⊆ W x := fun x hx => (hVg x hx).2.2.2.1
  have hVpos : ∀ x ∈ L, ∀ z ∈ V x, 0 < p z := fun x hx => (hVg x hx).2.2.2.2.1
  have hVder : ∀ x ∈ L, ∀ z ∈ V x, deriv h z ≠ 0 := fun x hx => (hVg x hx).2.2.2.2.2.1
  have hVinj : ∀ x ∈ L, InjOn h (V x) := fun x hx => (hVg x hx).2.2.2.2.2.2.1
  have hVimg : ∀ x ∈ L, IsOpen (h '' V x) := fun x hx => (hVg x hx).2.2.2.2.2.2.2.1
  have hVleft : ∀ x ∈ L, ∀ z ∈ V x, g x (h z) = z := fun x hx => (hVg x hx).2.2.2.2.2.2.2.2.1
  have hVgc : ∀ x ∈ L, ContinuousOn (g x) (h '' V x) := fun x hx => (hVg x hx).2.2.2.2.2.2.2.2.2.1
  have hVmaps : ∀ x ∈ L, MapsTo (g x) (h '' V x) (V x) := fun x hx => (hVg x hx).2.2.2.2.2.2.2.2.2.2
  have hVdisj : L.PairwiseDisjoint V := fun x hx y hy hxy =>
    (hWdisj hx hy hxy).mono (hVW x hx) (hVW y hy)
  -- every level near `t` lies in every `h(V_x)`
  have hO : IsOpen (⋂ x ∈ L, h '' V x) := hLfin.isOpen_biInter hVimg
  have htO : t ∈ ⋂ x ∈ L, h '' V x := mem_iInter₂.2 fun x hx => ⟨x, hVmem x hx, hx⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO t htO
  -- the band near `t` lies in `⋃ V_x`
  have hband : ∃ r2 > 0, ∀ z, |h z - t| ≤ r2 → ∃ x ∈ L, z ∈ V x := by
    set O := ⋃ x ∈ L, V x with hOdef
    have hOo : IsOpen O := isOpen_biUnion fun x hx => hVopen x hx
    set K := {z | |h z - t| ≤ |t| / 2} ∩ Oᶜ with hKdef
    have hK : IsCompact K := (band_compact hc hT hB ht).inter_right hOo.isClosed_compl
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · refine ⟨|t| / 2, by positivity, fun z hz => ?_⟩
      by_contra hno
      have hzK : z ∈ K := ⟨hz, fun hzO => hno (by
        obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 hzO
        exact ⟨x, hx, hzx⟩)⟩
      rw [hKe] at hzK
      exact hzK
    · obtain ⟨z0, hz0K, hmin⟩ := hK.exists_isMinOn hKne
        (show Continuous fun z => |h z - t| by fun_prop).continuousOn
      have hm : 0 < |h z0 - t| := by
        rw [abs_pos, sub_ne_zero]
        intro hz0
        exact hz0K.2 (mem_iUnion₂.2 ⟨z0, hz0, hVmem z0 hz0⟩)
      refine ⟨min (|t| / 2) (|h z0 - t| / 2), by positivity, fun z hz => ?_⟩
      by_contra hno
      have hzK : z ∈ K := ⟨le_trans hz (min_le_left _ _), fun hzO => hno (by
        obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 hzO
        exact ⟨x, hx, hzx⟩)⟩
      have h1 : |h z0 - t| ≤ |h z - t| := isMinOn_iff.1 hmin z hzK
      have h2 := min_le_right (|t| / 2) (|h z0 - t| / 2)
      linarith
  obtain ⟨r2, hr2, hr2b⟩ := hband
  set r := min (ε / 2) r2 with hrdef
  have hr : 0 < r := lt_min (by positivity) hr2
  have hrε : r ≤ ε / 2 := min_le_left _ _
  have hrr2 : r ≤ r2 := min_le_right _ _
  have ha : ∀ y ∈ Icc (t - r) (t + r), ∀ x ∈ L, y ∈ h '' V x := by
    intro y hy x hx
    have hyb : y ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      obtain ⟨hy1, hy2⟩ := hy
      constructor <;> linarith
    exact mem_iInter₂.1 (hball hyb) x hx
  have hb : ∀ z, h z ∈ Icc (t - r) (t + r) → ∃ x ∈ L, z ∈ V x := by
    intro z hz
    apply hr2b
    rw [abs_le]
    obtain ⟨hz1, hz2⟩ := hz
    constructor <;> linarith
  -- the preimage of a level near `t`
  have hpre : ∀ y ∈ Icc (t - r) (t + r), {z | h z = y} = (fun x => g x y) '' L := by
    intro y hy
    ext z
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · intro hz
      obtain ⟨x, hx, hzx⟩ := hb z (hz ▸ hy)
      exact ⟨x, hx, by rw [← hz, hVleft x hx z hzx]⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z', hz'V, hz'⟩ := ha y hy x hx
      rw [← hz', hVleft x hx z' hz'V]
  have hinj : ∀ y ∈ Icc (t - r) (t + r), InjOn (fun x => g x y) L := by
    intro y hy x1 hx1 x2 hx2 heq
    by_contra hne12
    have hm1 : g x1 y ∈ V x1 := hVmaps x1 hx1 (ha y hy x1 hx1)
    have hm2 : g x2 y ∈ V x2 := hVmaps x2 hx2 (ha y hy x2 hx2)
    have hdis := hVdisj hx1 hx2 hne12
    simp only at heq
    rw [heq] at hm1
    exact Set.disjoint_left.1 hdis hm1 hm2
  set G : ℝ → ℝ → ℝ := fun x y => p (g x y) / |deriv h (g x y)| with hGdef
  have hsum : ∀ y ∈ Icc (t - r) (t + r), levelDens h p y = ∑ x ∈ hLfin.toFinset, G x y := by
    intro y hy
    unfold levelDens
    rw [hpre y hy, finsum_mem_image (hinj y hy), finsum_mem_eq_finite_toFinset_sum _ hLfin]
  have hfin : ∀ y ∈ Icc (t - r) (t + r), {z | h z = y}.Finite := fun y hy => by
    rw [hpre y hy]
    exact hLfin.image _
  have hmapsI : ∀ x ∈ L, MapsTo (g x) (Icc (t - r) (t + r)) (V x) := fun x hx y hy =>
    hVmaps x hx (ha y hy x hx)
  have hGcont : ∀ x ∈ L, ContinuousOn (G x) (Icc (t - r) (t + r)) := by
    intro x hx
    have hgc : ContinuousOn (g x) (Icc (t - r) (t + r)) := (hVgc x hx).mono fun y hy => ha y hy x hx
    have hpc : ContinuousOn (fun y => p (g x y)) (Icc (t - r) (t + r)) :=
      (hp.mono (hVU x hx)).comp hgc (hmapsI x hx)
    have hdc : ContinuousOn (fun y => |deriv h (g x y)|) (Icc (t - r) (t + r)) :=
      continuous_abs.comp_continuousOn (hcd.comp_continuousOn hgc)
    exact hpc.div hdc fun y hy => abs_ne_zero.2 (hVder x hx _ (hmapsI x hx hy))
  have hGpos : ∀ x ∈ L, ∀ y ∈ Icc (t - r) (t + r), 0 < G x y := fun x hx y hy =>
    div_pos (hVpos x hx _ (hmapsI x hx hy)) (abs_pos.2 (hVder x hx _ (hmapsI x hx hy)))
  have hcont : ContinuousOn (levelDens h p) (Icc (t - r) (t + r)) :=
    (continuousOn_finsetSum _ fun x hx => hGcont x (hLfin.mem_toFinset.1 hx)).congr fun y hy => hsum y hy
  have hLne : hLfin.toFinset.Nonempty := by
    obtain ⟨x0, hx0⟩ := hne
    exact ⟨x0, hLfin.mem_toFinset.2 hx0⟩
  have hdpos : ∀ y ∈ Icc (t - r) (t + r), 0 < levelDens h p y := fun y hy => by
    rw [hsum y hy]
    exact Finset.sum_pos (fun x hx => hGpos x (hLfin.mem_toFinset.1 hx) y hy) hLne
  have hIne : (Icc (t - r) (t + r)).Nonempty := nonempty_Icc.2 (by linarith)
  obtain ⟨ymin, hymin, hminOn⟩ := isCompact_Icc.exists_isMinOn hIne hcont
  obtain ⟨ymax, hymax, hmaxOn⟩ := isCompact_Icc.exists_isMaxOn hIne hcont
  refine ⟨hLfin, r, levelDens h p ymin, levelDens h p ymax, hr, hdpos ymin hymin,
    isMinOn_iff.1 hminOn ymax hymax, ?_, fun s hs => ⟨hfin s hs, isMinOn_iff.1 hminOn s hs,
      isMaxOn_iff.1 hmaxOn s hs⟩, hcont, ?_⟩
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := hb z hz
    exact hVder x hx z hzx
  · intro A hA hAI
    have hmeasPre : MeasurableSet (h ⁻¹' A) := hc.measurable hA
    rw [withDensity_apply _ hmeasPre]
    have hunion : h ⁻¹' A = ⋃ x ∈ hLfin.toFinset, (h ⁻¹' A ∩ V x) := by
      ext z
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, Finite.mem_toFinset, exists_prop]
      constructor
      · intro hz
        obtain ⟨x, hx, hzx⟩ := hb z (hAI hz)
        exact ⟨x, hx, hz, hzx⟩
      · rintro ⟨x, -, hz, -⟩
        exact hz
    have hcov : ∀ x ∈ L, ∫⁻ z in h ⁻¹' A ∩ V x, ENNReal.ofReal (p z) =
        ∫⁻ y in A, ENNReal.ofReal (G x y) := by
      intro x hx
      have hs_meas : MeasurableSet (h ⁻¹' A ∩ V x) := hmeasPre.inter (hVopen x hx).measurableSet
      have himg : h '' (h ⁻¹' A ∩ V x) = A := by
        ext y
        constructor
        · rintro ⟨z, ⟨hz, -⟩, rfl⟩
          exact hz
        · intro hy
          obtain ⟨z, hzV, rfl⟩ := ha y (hAI hy) x hx
          exact ⟨z, ⟨hy, hzV⟩, rfl⟩
      have hcv := lintegral_image_eq_lintegral_abs_deriv_mul hs_meas
        (fun z _ => ((hh.differentiable one_ne_zero) z).hasDerivAt.hasDerivWithinAt)
        ((hVinj x hx).mono inter_subset_right) (fun y => ENNReal.ofReal (G x y))
      rw [himg] at hcv
      rw [hcv]
      refine setLIntegral_congr_fun hs_meas fun z hz => ?_
      have hgz : g x (h z) = z := hVleft x hx z hz.2
      have hdz : |deriv h z| ≠ 0 := abs_ne_zero.2 (hVder x hx z hz.2)
      simp only [hGdef, hgz]
      rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_div_cancel₀ _ hdz]
    have haem : ∀ x ∈ hLfin.toFinset, AEMeasurable (fun y => ENNReal.ofReal (G x y)) (volume.restrict A) :=
      fun x hx => (((hGcont x (hLfin.mem_toFinset.1 hx)).aemeasurable measurableSet_Icc).mono_measure
        (Measure.restrict_mono hAI le_rfl)).ennreal_ofReal
    have hdisj' : Set.PairwiseDisjoint (↑hLfin.toFinset) (fun x => h ⁻¹' A ∩ V x) := by
      intro x hx y hy hxy
      exact (hVdisj (hLfin.mem_toFinset.1 hx) (hLfin.mem_toFinset.1 hy) hxy).mono
        inter_subset_right inter_subset_right
    rw [hunion, lintegral_biUnion_finset hdisj'
      (fun x hx => hmeasPre.inter (hVopen x (hLfin.mem_toFinset.1 hx)).measurableSet),
      Finset.sum_congr rfl (fun x hx => hcov x (hLfin.mem_toFinset.1 hx)),
      ← lintegral_finsetSum' _ haem]
    refine setLIntegral_congr_fun hA fun y hy => ?_
    rw [hsum y (hAI hy), ENNReal.ofReal_sum_of_nonneg
      (fun x hx => (hGpos x (hLfin.mem_toFinset.1 hx) y (hAI hy)).le)]

end StatFormal.Wave31tc.Core

namespace StatFormal.Wave31tc

open StatFormal.Wave12c

/-- `QDensity` survives shrinking the window. -/
lemma QDensity_mono {P : Measure ℝ} {f : ℝ → ℝ} {t r r' c C : ℝ} (hr : r' ≤ r) (hQ : QDensity P f t r c C) :
    QDensity P f t r' c C := by
  obtain ⟨g, hg, hb, hP⟩ := hQ
  have hsub : Icc (t - r') (t + r') ⊆ Icc (t - r) (t + r) := Icc_subset_Icc (by linarith) (by linarith)
  exact ⟨g, hg, fun s hs => hb s (hsub hs), fun A hA hAI => hP A hA (hAI.trans hsub)⟩

/-- `rem:qdens (v3)`, "`L` is compact", every dimension. -/
theorem level_compact : Claims.level_compact := by
  intro d h t hc hT ht
  have hpos : 0 < |t| / 2 := by positivity
  have hev := hT.eventually (Metric.ball_mem_nhds 0 hpos)
  rw [eventually_comap, eventually_atTop] at hev
  obtain ⟨R, hR⟩ := hev
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_eq hc continuous_const)
  refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin d))) (r := R)).subset ?_
  intro x hx
  have hx' : h x = t := hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  push Not at hlt
  have h2 := hR ‖x‖ hlt.le x rfl
  rw [Real.dist_eq, sub_zero, hx'] at h2
  have h3 : 0 < |t| := abs_pos.2 ht
  linarith

/-- `rem:qdens (v3)`, the univariate target with the explicit density. -/
theorem qdens_formula : Claims.qdens_formula := by
  intro h p U t hh hT hB ht hne hd hUo hLU hp hpos
  exact Core.formula_core hh hT hB ht hne hd hUo hLU hp hpos

/-- `rem:qdens (v3)`, the univariate target in the form (Q). -/
theorem qdens_univariate : Claims.qdens_univariate := by
  intro h p U t hh hT hB ht hne hd hUo hLU hp hpos
  obtain ⟨-, r, c, C, hr, hc, hcC, -, hbd, hcont, hmeas⟩ :=
    Core.formula_core hh hT hB ht hne hd hUo hLU hp hpos
  classical
  refine ⟨r, c, C, hr, hc, hcC, (Icc (t - r) (t + r)).piecewise (levelDens h p) 0,
    hcont.measurable_piecewise continuousOn_const measurableSet_Icc, fun s hs => ?_, fun A hA hAI => ?_⟩
  · rw [piecewise_eq_of_mem _ _ _ hs]
    exact ⟨(hbd s hs).2.1, (hbd s hs).2.2⟩
  · rw [hmeas A hA hAI]
    refine setLIntegral_congr_fun hA fun y hy => ?_
    rw [piecewise_eq_of_mem _ _ _ (hAI hy)]

/-- `rem:qdens (v3)`, (Q) and (Q′) with one common half-width, witness form. -/
theorem qdens_Q_Qprime : Claims.qdens_Q_Qprime := by
  intro H _ _ φ dstar p q U V tα uα hh hT hB ht hne hd hUo hLU hp hpos hu hneu hdu hVo hLV hq hposq
  obtain ⟨r1, c1, C1, hr1, hc1, hcC1, hQ1⟩ := qdens_univariate _ p U tα hh hT hB ht hne hd hUo hLU hp hpos
  obtain ⟨r2, c2, C2, hr2, hc2, -, hQ2⟩ := qdens_univariate _ q V uα hh hT hB hu hneu hdu hVo hLV hq hposq
  refine ⟨min r1 r2, c1, C1, c2, lt_min hr1 hr2, hc1, hcC1, hc2, QDensity_mono (min_le_left _ _) hQ1, ?_⟩
  obtain ⟨g, hg, hb, hP⟩ := QDensity_mono (min_le_right _ _) hQ2
  exact ⟨g, hg, fun s hs => (hb s hs).1, hP⟩

end StatFormal.Wave31tc
