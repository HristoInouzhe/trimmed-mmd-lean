import StatFormal.Archive.Wave23d.RouteCM
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Route — A `lem:app-cm-plans` (iii), (iv) gradient and conditional uniqueness (untrusted)

* Directional derivative `f'(x;h) = inf_{t>0} (f(x+th) − f(x))/t` (monotone quotient), sublinear and `L`-Lipschitz in
  `h`; `y ∈ ∂f(x) ⟺ ⟨y,·⟩ ≤ f'(x;·)`; Hahn–Banach on `ℝh` + Riesz give `y ∈ ∂f(x)` with `⟨y,h⟩ = f'(x;h)`.
* `∂f(x)` a singleton ⟺ `f'(x;·)` odd ⟺ `f` Gâteaux differentiable at `x`; so `D_fᶜ` lies in the multivalued set of the
  monotone graph of `∂f`, which is `A`-null (library cover by Lipschitz hypersurfaces).
* Borel: `f'(·;h)` is a pointwise limit of continuous functions; `D_f = ⋂_n {f'(x;u_n) + f'(x;−u_n) = 0}` (dense `u_n`);
  `∇f` is Borel because each `⟨h, ∇f⟩` is (weak measurability in a separable Hilbert space, proved via a dense sequence
  of the unit sphere and countable closed-ball covers).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave23d

open StatFormal.OTFD.WaveL1 (CycMon CMConc Graph LipNull)

section DD
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {f : H → ℝ} {L : ℝ}

/-- The difference quotient `(f(x + t h) − f(x))/t`. -/
def quot (f : H → ℝ) (x h : H) (t : ℝ) : ℝ := (f (x + t • h) - f x) / t

/-- The directional derivative `f'(x; h) = inf_{t > 0}` of the quotient. -/
def dd (f : H → ℝ) (x h : H) : ℝ := ⨅ t : Ioi (0 : ℝ), quot f x h t

variable (hf : ConvexOn ℝ univ f) (hL : ∀ x z, |f x - f z| ≤ L * ‖x - z‖)
include hf

lemma quot_mono (x h : H) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : quot f x h s ≤ quot f x h t := by
  have ht : 0 < t := hs.trans_le hst
  have hc := hf.2 (mem_univ x) (mem_univ (x + t • h)) (by
    have : 0 ≤ s / t := div_nonneg hs.le ht.le
    linarith [div_le_one_of_le₀ hst ht.le] : 0 ≤ 1 - s / t) (div_nonneg hs.le ht.le) (by ring)
  have e : (1 - s / t) • x + (s / t) • (x + t • h) = x + s • h := by
    rw [smul_add, smul_smul, div_mul_cancel₀ _ ht.ne', sub_smul, one_smul]; abel
  rw [e, smul_eq_mul, smul_eq_mul] at hc
  unfold quot
  rw [div_le_div_iff₀ hs ht]
  have : f (x + s • h) - f x ≤ s / t * (f (x + t • h) - f x) := by nlinarith
  have := mul_le_mul_of_nonneg_left this ht.le
  rw [show t * (s / t * (f (x + t • h) - f x)) = s * (f (x + t • h) - f x) by field_simp] at this
  linarith

omit hf in
lemma quot_lower (hL : ∀ x z, |f x - f z| ≤ L * ‖x - z‖) (x h : H) {t : ℝ} (ht : 0 < t) :
    -(L * ‖h‖) ≤ quot f x h t := by
  have := hL (x + t • h) x
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at this
  unfold quot
  rw [le_div_iff₀ ht]
  have := neg_abs_le (f (x + t • h) - f x)
  nlinarith

omit hf in
lemma quot_upper (hL : ∀ x z, |f x - f z| ≤ L * ‖x - z‖) (x h : H) {t : ℝ} (ht : 0 < t) :
    quot f x h t ≤ L * ‖h‖ := by
  have := hL (x + t • h) x
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at this
  unfold quot
  rw [div_le_iff₀ ht]
  have := le_abs_self (f (x + t • h) - f x)
  nlinarith

include hL

lemma bdd_quot (x h : H) : BddBelow (range fun t : Ioi (0 : ℝ) => quot f x h t) :=
  ⟨-(L * ‖h‖), by rintro _ ⟨t, rfl⟩; exact quot_lower hL x h t.2⟩

lemma dd_le_quot (x h : H) {t : ℝ} (ht : 0 < t) : dd f x h ≤ quot f x h t :=
  ciInf_le (bdd_quot hf hL x h) ⟨t, ht⟩

omit hf hL in
lemma le_dd {x h : H} {c : ℝ} (hc : ∀ t, 0 < t → c ≤ quot f x h t) : c ≤ dd f x h :=
  le_ciInf fun t => hc t t.2

lemma dd_bounds (x h : H) : -(L * ‖h‖) ≤ dd f x h ∧ dd f x h ≤ L * ‖h‖ :=
  ⟨le_dd fun t ht => quot_lower hL x h ht, (dd_le_quot hf hL x h one_pos).trans (quot_upper hL x h one_pos)⟩

/-- The quotient tends to `f'(x; h)` as `t ↓ 0`. -/
lemma tendsto_quot (x h : H) : Tendsto (quot f x h) (𝓝[>] 0) (𝓝 (dd f x h)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ha.trans_le (dd_le_quot hf hL x h ht)
  · obtain ⟨⟨t₀, ht₀⟩, hlt⟩ := exists_lt_of_ciInf_lt ha
    filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht
    exact (quot_mono hf x h ht.1 ht.2.le).trans_lt hlt

lemma dd_zero (x : H) : dd f x 0 = 0 := by
  have : ∀ t, quot f x 0 t = 0 := fun t => by simp [quot]
  simp [dd, this]

lemma dd_smul (x h : H) {c : ℝ} (hc : 0 < c) : dd f x (c • h) = c * dd f x h := by
  have e : ∀ t, quot f x (c • h) t = c * quot f x h (c * t) := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · simp [quot]
    · unfold quot; rw [smul_smul, mul_comm t c]; field_simp
  apply le_antisymm
  · rw [← div_le_iff₀' hc]
    refine le_dd fun t ht => ?_
    rw [div_le_iff₀' hc]
    have := dd_le_quot hf hL x (c • h) (div_pos ht hc)
    rw [e, mul_div_cancel₀ _ hc.ne'] at this
    exact this
  · refine le_dd fun t ht => ?_
    rw [e]
    exact mul_le_mul_of_nonneg_left (dd_le_quot hf hL x h (mul_pos hc ht)) hc.le

lemma dd_add (x h k : H) : dd f x (h + k) ≤ dd f x h + dd f x k := by
  have key : ∀ t, 0 < t → dd f x (h + k) ≤ quot f x h (2 * t) + quot f x k (2 * t) := by
    intro t ht
    refine (dd_le_quot hf hL x (h + k) ht).trans ?_
    have hc := hf.2 (mem_univ (x + (2 * t) • h)) (mem_univ (x + (2 * t) • k)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have e : (1 / 2 : ℝ) • (x + (2 * t) • h) + (1 / 2 : ℝ) • (x + (2 * t) • k) = x + t • (h + k) := by
      module
    rw [e, smul_eq_mul, smul_eq_mul] at hc
    unfold quot
    rw [← add_div, div_le_div_iff₀ ht (by positivity)]
    nlinarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨⟨t₁, ht₁⟩, h1⟩ := exists_lt_of_ciInf_lt (show dd f x h < dd f x h + ε / 2 by linarith)
  obtain ⟨⟨t₂, ht₂⟩, h2⟩ := exists_lt_of_ciInf_lt (show dd f x k < dd f x k + ε / 2 by linarith)
  set t := min t₁ t₂ / 2
  have ht : 0 < t := by simp only [t]; exact half_pos (lt_min ht₁ ht₂)
  have := key t ht
  have q1 := quot_mono hf x h (by positivity) (show 2 * t ≤ t₁ by simp only [t]; linarith [min_le_left t₁ t₂])
  have q2 := quot_mono hf x k (by positivity) (show 2 * t ≤ t₂ by simp only [t]; linarith [min_le_right t₁ t₂])
  simp only at h1 h2
  linarith

lemma dd_lip (x h k : H) : dd f x h ≤ dd f x k + L * ‖h - k‖ := by
  have hk : dd f x h - L * ‖h - k‖ ≤ dd f x k := by
    refine le_dd fun t ht => ?_
    have h1 := dd_le_quot hf hL x h ht
    have h2 := hL (x + t • h) (x + t • k)
    rw [show x + t • h - (x + t • k) = t • (h - k) by rw [smul_sub]; abel, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht] at h2
    have h3 : quot f x h t ≤ quot f x k t + L * ‖h - k‖ := by
      unfold quot
      rw [div_le_iff₀ ht, add_mul, div_mul_cancel₀ _ ht.ne']
      have := le_abs_self (f (x + t • h) - f (x + t • k))
      nlinarith
    linarith
  linarith

lemma mem_subdiff_iff (x y : H) : y ∈ subdiff f x ↔ ∀ h, ⟪y, h⟫ ≤ dd f x h := by
  constructor
  · intro hy h
    refine le_dd fun t ht => ?_
    have := hy (x + t • h)
    rw [add_sub_cancel_left, inner_smul_right] at this
    unfold quot
    rw [le_div_iff₀ ht]; linarith
  · intro hy z
    have := (hy (z - x)).trans (dd_le_quot hf hL x (z - x) one_pos)
    simp only [quot, one_smul, add_sub_cancel, div_one] at this
    linarith

/-- `f'(x; ·)` is odd once `f'(x; h) + f'(x; −h) = 0`; then every subgradient represents it. -/
lemma inner_eq_dd_of_odd {x y : H} (hy : y ∈ subdiff f x) (hodd : ∀ h, dd f x h + dd f x (-h) = 0) (h : H) :
    ⟪y, h⟫ = dd f x h := by
  have h1 := (mem_subdiff_iff hf hL x y).1 hy h
  have h2 := (mem_subdiff_iff hf hL x y).1 hy (-h)
  rw [inner_neg_right] at h2
  linarith [hodd h]

omit hf hL in
lemma eq_of_inner_le {g y : H} (h : ∀ v, ⟪y, v⟫ ≤ ⟪g, v⟫) : y = g := by
  have := h (y - g)
  have h0 : ⟪y - g, y - g⟫ ≤ 0 := by rw [inner_sub_left]; linarith
  rw [real_inner_self_eq_norm_sq] at h0
  exact sub_eq_zero.1 (norm_eq_zero.1 (by nlinarith [norm_nonneg (y - g)]))

/-- Right and left slopes give the Gâteaux derivative when `f'(x; ·) = ⟨g, ·⟩`. -/
lemma gatDiff_of_dd {x g : H} (hg : ∀ h, dd f x h = ⟪g, h⟫) : GatDiff f x g := by
  intro h
  rw [hasDerivAt_iff_tendsto_slope, ← nhdsLT_sup_nhdsGT]
  have hs : ∀ t, slope (fun t : ℝ => f (x + t • h)) 0 t = quot f x h t := by
    intro t; rw [slope_def_field]; simp only [quot, sub_zero, zero_smul, add_zero]
  rw [show slope (fun t : ℝ => f (x + t • h)) 0 = quot f x h from funext hs]
  refine Tendsto.sup ?_ ?_
  · have hn : Tendsto (fun t : ℝ => -t) (𝓝[<] 0) (𝓝[>] 0) := by
      have := tendsto_neg_nhdsLT (a := (0 : ℝ)); rwa [neg_zero] at this
    have h1 := (tendsto_quot hf hL x (-h)).comp hn
    have h2 := h1.neg
    rw [hg, inner_neg_right, neg_neg] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := (show t < 0 from ht).ne
    simp only [Function.comp, quot, smul_neg, neg_smul, neg_neg]
    field_simp
  · rw [← hg]; exact tendsto_quot hf hL x h

lemma dd_of_gatDiff {x g : H} (hg : GatDiff f x g) (h : H) : dd f x h = ⟪g, h⟫ := by
  have h1 := (hasDerivAt_iff_tendsto_slope.1 (hg h)).mono_left
    (nhdsWithin_mono _ (fun t (ht : 0 < t) => ht.ne'))
  have hs : ∀ t, slope (fun t : ℝ => f (x + t • h)) 0 t = quot f x h t := by
    intro t; rw [slope_def_field]; simp only [quot, sub_zero, zero_smul, add_zero]
  rw [show slope (fun t : ℝ => f (x + t • h)) 0 = quot f x h from funext hs] at h1
  exact tendsto_nhds_unique (tendsto_quot hf hL x h) h1

variable [CompleteSpace H]

/-- A linear minorant of `f'(x; ·)` is represented by a subgradient (Riesz). -/
lemma subgrad_of_linear (x : H) (g : H →ₗ[ℝ] ℝ) (hg : ∀ v, g v ≤ dd f x v) :
    ∃ y ∈ subdiff f x, ∀ v, ⟪y, v⟫ = g v := by
  have hb : ∀ v, ‖g v‖ ≤ max L 0 * ‖v‖ := by
    intro v
    have h1 := (hg v).trans (dd_bounds hf hL x v).2
    have h2 := (hg (-v)).trans (dd_bounds hf hL x (-v)).2
    rw [map_neg, norm_neg] at h2
    rw [Real.norm_eq_abs, abs_le]
    have : L * ‖v‖ ≤ max L 0 * ‖v‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    constructor <;> linarith
  set gc := g.mkContinuous (max L 0) hb
  refine ⟨(InnerProductSpace.toDual ℝ H).symm gc, ?_, fun v => ?_⟩
  · rw [mem_subdiff_iff hf hL]
    intro v
    rw [InnerProductSpace.toDual_symm_apply, LinearMap.mkContinuous_apply]
    exact hg v
  · rw [InnerProductSpace.toDual_symm_apply, LinearMap.mkContinuous_apply]

/-- **Hahn–Banach**: some subgradient attains `f'(x; h)`. -/
lemma exists_subgrad (x h : H) : ∃ y ∈ subdiff f x, ⟪y, h⟫ = dd f x h := by
  set N := dd f x
  have N_hom : ∀ c : ℝ, 0 < c → ∀ v, N (c • v) = c * N v := fun c hc v => dd_smul hf hL x v hc
  have N_add : ∀ v w, N (v + w) ≤ N v + N w := fun v w => dd_add hf hL x v w
  have hN0 : N 0 = 0 := dd_zero hf hL x
  by_cases hh : h = 0
  · subst hh
    obtain ⟨g, -, hg⟩ := exists_extension_of_le_sublinear (⟨⊥, 0⟩ : H →ₗ.[ℝ] ℝ) N N_hom N_add (by
      rintro ⟨z, hz⟩
      rw [Submodule.mem_bot] at hz
      subst hz
      simp [hN0])
    obtain ⟨y, hy, -⟩ := subgrad_of_linear hf hL x g hg
    exact ⟨y, hy, by rw [inner_zero_right, hN0]⟩
  · set f₀ : H →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton h (N h) hh
    have hdom : ∀ z : f₀.domain, ∃ c : ℝ, (z : H) = c • h ∧ f₀ z = c * N h := by
      rintro ⟨z, hz⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      exact ⟨c, rfl, (LinearPMap.mkSpanSingleton'_apply h (N h) _ c hz).trans (by simp)⟩
    obtain ⟨g, hgf, hg⟩ := exists_extension_of_le_sublinear f₀ N N_hom N_add (by
      intro z
      obtain ⟨c, hz, hfz⟩ := hdom z
      rw [hfz, hz]
      rcases lt_trichotomy c 0 with hc | rfl | hc
      · have e : c • h = (-c) • (-h) := by rw [smul_neg, neg_smul, neg_neg]
        rw [e, N_hom (-c) (by linarith)]
        have := N_add h (-h)
        rw [add_neg_cancel, hN0] at this
        nlinarith
      · simp [hN0]
      · rw [N_hom c hc])
    obtain ⟨y, hy, hyv⟩ := subgrad_of_linear hf hL x g hg
    refine ⟨y, hy, ?_⟩
    rw [hyv]
    have := hgf ⟨h, Submodule.mem_span_singleton_self h⟩
    rw [this]
    exact LinearPMap.mkSpanSingleton_apply ℝ ℝ hh (N h)

lemma gat_iff_odd (x : H) : x ∈ gatSet f ↔ ∀ h, dd f x h + dd f x (-h) = 0 := by
  constructor
  · rintro ⟨g, hg⟩ h
    rw [dd_of_gatDiff hf hL hg, dd_of_gatDiff hf hL hg, inner_neg_right, add_neg_cancel]
  · intro hodd
    obtain ⟨y, hy, -⟩ := exists_subgrad hf hL x 0
    exact ⟨y, gatDiff_of_dd hf hL fun h => (inner_eq_dd_of_odd hf hL hy hodd h).symm⟩

omit hf hL [CompleteSpace H] in
lemma gatDiff_gatGrad {x : H} (hx : x ∈ gatSet f) : GatDiff f x (gatGrad f x) := by
  unfold gatGrad; rw [dif_pos (show ∃ g, GatDiff f x g from hx)]; exact hx.choose_spec

lemma subdiff_eq_gatGrad {x : H} (hx : x ∈ gatSet f) : subdiff f x = {gatGrad f x} := by
  have hg := gatDiff_gatGrad hx
  ext y
  rw [mem_singleton_iff, mem_subdiff_iff hf hL]
  constructor
  · intro hy; exact eq_of_inner_le fun v => (hy v).trans_eq (dd_of_gatDiff hf hL hg v)
  · rintro rfl v; exact (dd_of_gatDiff hf hL hg v).symm.le

omit hf [CompleteSpace H] in
lemma continuous_of_lip : Continuous f := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨max L 0, le_max_right _ _⟩) fun x z => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact (hL x z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

end DD

/-! ### Weak measurability in a separable Hilbert space -/

section Pettis
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

lemma measurable_of_inner {G : X → H} (hG : ∀ h : H, Measurable fun x => ⟪h, G x⟫) : Measurable G := by
  by_cases hH : ∃ v : H, v ≠ 0
  · obtain ⟨v, hv⟩ := hH
    -- a dense sequence of the unit sphere
    have hne : Nonempty (Metric.sphere (0 : H) 1) :=
      ⟨⟨‖v‖⁻¹ • v, by simp [norm_smul, norm_ne_zero_iff.2 hv]⟩⟩
    obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (Metric.sphere (0 : H) 1)
    have hnorm : ∀ (w : H) (r : ℝ), ‖w‖ ≤ r ↔ ∀ m, ⟪(u m : H), w⟫ ≤ r := by
      intro w r
      constructor
      · intro h m
        have := real_inner_le_norm (u m : H) w
        rw [show ‖(u m : H)‖ = 1 from by simpa using (u m).2, one_mul] at this
        linarith
      · intro h
        by_contra hlt
        push Not at hlt
        have hw : w ≠ 0 := by
          rintro rfl; have := h 0; simp at this; rw [norm_zero] at hlt; linarith
        have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
        set e : Metric.sphere (0 : H) 1 := ⟨‖w‖⁻¹ • w, by simp [norm_smul, hw]⟩
        have he : ⟪(e : H), w⟫ = ‖w‖ := by
          simp only [e, inner_smul_left, real_inner_self_eq_norm_sq, conj_trivial]; field_simp
        have hδ : 0 < (‖w‖ - r) / ‖w‖ := div_pos (by linarith) hwpos
        obtain ⟨m, hm⟩ := hu.exists_dist_lt e hδ
        have h1 : |⟪(u m : H) - e, w⟫| ≤ ‖(u m : H) - e‖ * ‖w‖ := abs_real_inner_le_norm _ _
        have h2 : ‖(u m : H) - e‖ < (‖w‖ - r) / ‖w‖ := by
          rw [← dist_eq_norm]; rw [dist_comm] at hm; exact hm
        have h3 : ‖(u m : H) - e‖ * ‖w‖ < ‖w‖ - r := by
          rwa [lt_div_iff₀ hwpos] at h2
        have := h m
        rw [show (u m : H) = ((u m : H) - e) + e by abel, inner_add_left, he] at this
        have := neg_abs_le ⟪(u m : H) - e, w⟫
        linarith
    have hball : ∀ (c : H) (r : ℝ), MeasurableSet (G ⁻¹' Metric.closedBall c r) := by
      intro c r
      have : G ⁻¹' Metric.closedBall c r = ⋂ m, {x | ⟪(u m : H), G x⟫ - ⟪(u m : H), c⟫ ≤ r} := by
        ext x
        simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, Set.mem_iInter, Set.mem_ofPred_eq,
          hnorm, inner_sub_right]
      rw [this]
      exact MeasurableSet.iInter fun m => measurableSet_le ((hG _).sub_const _) measurable_const
    obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq H
    refine measurable_of_isOpen fun U hU => ?_
    set S := {p : ℕ × ℚ | 0 < p.2 ∧ Metric.closedBall (d p.1) (p.2 : ℝ) ⊆ U}
    have hU' : U = ⋃ p ∈ S, Metric.closedBall (d p.1) (p.2 : ℝ) := by
      apply le_antisymm
      · intro x hx
        obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
        obtain ⟨n, hn⟩ := hd.exists_dist_lt x (by positivity : 0 < ε / 4)
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
        refine Set.mem_biUnion (x := (n, q)) ⟨by simp only; exact_mod_cast (by linarith : (0 : ℝ) < q), ?_⟩ ?_
        · intro y hy
          apply hεU
          rw [Metric.mem_closedBall] at hy
          rw [Metric.mem_ball]
          calc dist y x ≤ dist y (d n) + dist (d n) x := dist_triangle _ _ _
            _ < ε := by rw [dist_comm] at hn; simp only at hy; linarith
        · rw [Metric.mem_closedBall]; simp only; linarith
      · exact Set.iUnion₂_subset fun p hp => hp.2
    rw [hU', Set.preimage_iUnion₂]
    exact MeasurableSet.biUnion (Set.to_countable S) fun p _ => hball _ _
  · push Not at hH
    have : G = fun _ => 0 := funext fun x => hH (G x)
    rw [this]; exact measurable_const

end Pettis

/-! ### (iii) -/

theorem cm_gateaux_thm : Claims.cm_gateaux := by
  intro H _ _ _ _ _ _ A f L hA hf hL
  have hfc : Continuous f := continuous_of_lip hL
  -- measurability of `x ↦ f'(x; h)`
  have hdd : ∀ h, Measurable fun x => dd f x h := by
    intro h
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n => by
        simp only [Set.mem_Ioi]; positivity⟩
    refine measurable_of_tendsto_metrizable (f := fun n x => quot f x h (1 / ((n : ℝ) + 1))) (fun n => ?_)
      (tendsto_pi_nhds.2 fun x => (tendsto_quot hf hL x h).comp ht)
    exact ((hfc.comp (continuous_id.add continuous_const)).sub hfc).measurable.div_const _
  -- `D_f` is Borel
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq H
  have hD : gatSet f = ⋂ n, {x | dd f x (u n) + dd f x (-u n) = 0} := by
    ext x
    rw [gat_iff_odd hf hL, Set.mem_iInter]
    constructor
    · intro h n; exact h (u n)
    · intro h
      have hφ : Continuous fun v => dd f x v + dd f x (-v) := by
        refine (LipschitzWith.of_dist_le_mul (K := (2 * max L 0).toNNReal) fun v w => ?_).continuous
        have a1 := dd_lip hf hL x v w
        have a2 := dd_lip hf hL x w v
        have a3 := dd_lip hf hL x (-v) (-w)
        have a4 := dd_lip hf hL x (-w) (-v)
        rw [show -v - -w = -(v - w) by abel, norm_neg] at a3
        rw [show -w - -v = -(w - v) by abel, norm_neg] at a4
        rw [norm_sub_rev] at a2 a4
        have : L * ‖v - w‖ ≤ max L 0 * ‖v - w‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        rw [Real.dist_eq, dist_eq_norm, abs_le]
        rw [Real.coe_toNNReal _ (by positivity)]
        constructor <;> linarith
      have := hφ.ext_on hu continuous_const (by rintro _ ⟨n, rfl⟩; exact h n)
      intro v; exact congrFun this v
  have hDm : MeasurableSet (gatSet f) := by
    rw [hD]
    exact MeasurableSet.iInter fun n => measurableSet_eq_fun ((hdd _).add (hdd _)) measurable_const
  refine ⟨hDm, ?_, fun x hx => subdiff_eq_gatGrad hf hL hx, ?_⟩
  · -- `D_fᶜ` lies in the multivalued set of the monotone graph of `∂f`
    set Γ : Set (H × H) := {p | ∀ z, f p.1 + ⟪p.2, z - p.1⟫ ≤ f z}
    have hmono : StatFormal.Potentials.IsMonotoneSet Γ :=
      isMonotoneSet_of_cycMon (StatFormal.OTFD.WaveL3.cycMon_subgradGraph f)
    refine measure_mono_null (fun x hx => ?_)
      (StatFormal.Potentials.measure_multivaluedSet_eq_zero (fun S hS => hA S hS) hmono)
    rw [Set.mem_compl_iff, gat_iff_odd hf hL] at hx
    push Not at hx
    obtain ⟨h, hh⟩ := hx
    obtain ⟨y₁, hy₁, e₁⟩ := exists_subgrad hf hL x h
    obtain ⟨y₂, hy₂, e₂⟩ := exists_subgrad hf hL x (-h)
    refine ⟨y₁, y₂, hy₁, hy₂, fun heq => hh ?_⟩
    rw [← heq, inner_neg_right] at e₂
    linarith
  · classical
    refine measurable_of_inner fun h => ?_
    have e : (fun x => ⟪h, gatGrad f x⟫) = fun x => if x ∈ gatSet f then dd f x h else 0 := by
      ext x
      split_ifs with hx
      · rw [real_inner_comm, dd_of_gatDiff hf hL (gatDiff_gatGrad hx)]
      · rw [gatGrad, dif_neg (show ¬∃ g, GatDiff f x g from hx), inner_zero_right]
    rw [e]
    exact Measurable.ite hDm (hdd h) measurable_const

/-! ### (iv): gradient and conditional uniqueness -/

theorem cm_graph_gradient_thm : Claims.cm_graph_gradient := by
  rintro H _ _ _ _ _ _ γ M hγ hA ⟨Γ, hΓm, hΓ, hΓ0⟩ hM
  set B := Metric.closedBall (0 : H) M
  set Γ' := Γ ∩ (univ ×ˢ B)
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hΓ'm : MeasurableSet Γ' := hΓm.inter (MeasurableSet.univ.prod hBm)
  have hΓ'0 : γ Γ'ᶜ = 0 := by
    have h2 : γ (univ ×ˢ B : Set (H × H))ᶜ = 0 := by
      have : (univ ×ˢ B : Set (H × H))ᶜ = Prod.snd ⁻¹' Bᶜ := by ext p; simp
      rw [this, ← Measure.snd_apply hBm.compl]; exact hM
    rw [Set.compl_inter]; exact measure_union_null hΓ0 h2
  have hΓ'cm : CycMon Γ' := StatFormal.OTFD.WaveL3.cycMon_mono hΓ Set.inter_subset_left
  have hne : Γ'.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.compl_empty, measure_univ] at hΓ'0
    exact one_ne_zero hΓ'0
  have hbd : ∀ p ∈ Γ', ‖p.2‖ ≤ M := fun p hp => mem_closedBall_zero_iff.1 hp.2.2
  obtain ⟨f, hfc, hfL, hsub⟩ := cm_rockafellar_thm H Γ' M hne hΓ'cm hbd
  have hMv : γ.fst (StatFormal.Potentials.multivaluedSet Γ') = 0 :=
    StatFormal.Potentials.measure_multivaluedSet_eq_zero (fun S hS => hA S hS) (isMonotoneSet_of_cycMon hΓ'cm)
  have hae : ∀ᵐ z ∂γ, z ∈ Γ' := (measure_eq_zero_iff_ae_notMem.1 hΓ'0).mono fun _ h => Set.notMem_compl_iff.1 h
  obtain ⟨T, hT, hγT, hTΓ⟩ := StatFormal.Potentials.exists_eq_graphPlan_of_ae_mem
    (⟨rfl, rfl⟩ : IsCoupling γ γ.fst γ.snd) hΓ'm hae hMv
  obtain ⟨-, hnull, hsd, -⟩ := cm_gateaux_thm H γ.fst f M hA hfc hfL
  refine ⟨T, f, hT, hγT, ?_, hfc, hfL, ?_⟩
  · conv_rhs => rw [hγT]
    exact (snd_graphPlan hT.aemeasurable).symm
  · filter_upwards [hTΓ, measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hxD
    have hxD' : x ∈ gatSet f := by simpa using hxD
    have hmem : T x ∈ subdiff f x := fun z => hsub (x, T x) hx z
    rw [hsd x hxD', mem_singleton_iff] at hmem
    rw [hmem]; exact gatDiff_gatGrad hxD'

theorem cm_unique_cond_thm : Claims.cm_unique_cond := by
  intro H _ _ _ _ _ _ γ γ' M hγ hγ' hfst hsnd hA hM hcm hcm' hGHS
  obtain ⟨T, f, hT, hγT, hmap, hfc, hfL, hgrad⟩ := cm_graph_gradient_thm H γ M hγ hA hcm hM
  obtain ⟨T', f', hT', hγT', hmap', hfc', hfL', hgrad'⟩ :=
    cm_graph_gradient_thm H γ' M hγ' (hfst ▸ hA) hcm' (hsnd ▸ hM)
  rw [hfst] at hγT' hmap' hgrad'
  rw [hsnd] at hmap'
  have hTT : T =ᵐ[γ.fst] T' := hGHS f f' T T' M M hfc hfc' hfL hfL' hT hT' hgrad hgrad' hmap hmap'
  rw [hγT']
  conv_rhs => rw [hγT]
  unfold Graph
  exact Measure.map_congr (hTT.mono fun x hx => by simp only [hx])

end StatFormal.Wave23d
