import StatFormal.Archive.Wave30ah.Statements
import StatFormal.Archive.Wave30z.RouteVertex

/-!
# Route — wave 30ah: `lem:Hprops` (untrusted)

One copy (`side`) of the limit process at a time, through `SideCons`: every exact linear relation of the hinges
that holds `μ`-almost surely (zero variance) is respected by the path (from the a.s. linear consistency
`ae_linCons` of wave 30z). Then
* (a), (b): wave 30z `Hfun_smul`;
* (c), `α = 0`: every `t ∈ q(f)` has `(u − t)_+ = u − t` a.s. (`u = ⟨f, φ⟩`; the CVaR objective at `t` does not
  exceed its value at `−κ`, which is `P u`), so `ℓ_{f,t} = ℓ_{f,−κ} − κ − t` a.s. and `𝔾ℓ_{f,t} = 𝔾ℓ_{f,−κ}`;
  `f ↦ 𝔾ℓ_{f,−κ}` respects every linear relation of `𝔹_r` (`ℓ_{f,−κ} = ⟨f, φ⟩ + κ`), so it is `⟨·, G⟩`; the law of
  `⟨u, G⟩` is the law of `‖u‖ 𝔾ℓ_{u/‖u‖, −κ}`;
* (d): `q(f) = {t_f}` makes `H(f) = β 𝔾ℓ_{f,t_f}`, whose law is the one-point law of `𝔾`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30ah

open StatFormal.TrimmedMMD.Concentration (region empirical)
open StatFormal.Wave30v (Ball ballNeg)
open StatFormal.Wave30z

section Side
variable {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] {φ : 𝒳 → E} {κ : ℝ}

/-- The path respects every `μ`-a.s. exact linear relation of the hinges on one copy of the joint index. -/
def SideCons (φ : 𝒳 → E) (μ : Measure 𝒳) (κ : ℝ) (side : Idx1 E κ → Idx2 E κ) (v : C(Idx2 E κ, ℝ)) : Prop :=
  ∀ (p : ℕ) (z : Fin p → Idx1 E κ) (u : Fin p → ℝ),
    Var[fun w => ∑ i, u i * hinge φ ((z i).1 : E) (z i).2 w; μ] = 0 → ∑ i, u i * v (side (z i)) = 0

lemma gpVar_inl (P Q : Measure 𝒳) [IsProbabilityMeasure Q] {p : ℕ} (z : Fin p → Idx1 E κ) (u : Fin p → ℝ) :
    gpVar φ P Q 1 1 (fun i => Sum.inl (z i)) u = Var[fun w => ∑ i, u i * hinge φ ((z i).1 : E) (z i).2 w; P] := by
  unfold gpVar
  have h1 : (fun w => ∑ i, u i * hingeP φ (Sum.inl (z i) : Idx2 E κ) w) =
      fun w => ∑ i, u i * hinge φ ((z i).1 : E) (z i).2 w := by
    funext w; simp only [hingeP, Sum.elim_inl]
  have h2 : (fun w => ∑ i, u i * hingeQ φ (Sum.inl (z i) : Idx2 E κ) w) = fun _ => 0 := by
    funext w; simp only [hingeQ, Sum.elim_inl, mul_zero, Finset.sum_const_zero]
  rw [h1, h2, variance_fun_const]; ring

lemma gpVar_inr (P Q : Measure 𝒳) [IsProbabilityMeasure P] {p : ℕ} (z : Fin p → Idx1 E κ) (u : Fin p → ℝ) :
    gpVar φ P Q 1 1 (fun i => Sum.inr (z i)) u = Var[fun w => ∑ i, u i * hinge φ ((z i).1 : E) (z i).2 w; Q] := by
  unfold gpVar
  have h1 : (fun w => ∑ i, u i * hingeP φ (Sum.inr (z i) : Idx2 E κ) w) = fun _ => 0 := by
    funext w; simp only [hingeP, Sum.elim_inr, mul_zero, Finset.sum_const_zero]
  have h2 : (fun w => ∑ i, u i * hingeQ φ (Sum.inr (z i) : Idx2 E κ) w) =
      fun w => ∑ i, u i * hinge φ ((z i).1 : E) (z i).2 w := by
    funext w; simp only [hingeQ, Sum.elim_inr]
  rw [h1, h2, variance_fun_const]; ring

lemma sideCons_inl {P Q : Measure 𝒳} [IsProbabilityMeasure Q] {v : C(Idx2 E κ, ℝ)} (hv : LinCons φ P Q κ v) :
    SideCons φ P κ Sum.inl v := fun p z u h => hv p _ u (by rw [gpVar_inl]; exact h)

lemma sideCons_inr {P Q : Measure 𝒳} [IsProbabilityMeasure P] {v : C(Idx2 E κ, ℝ)} (hv : LinCons φ P Q κ v) :
    SideCons φ Q κ Sum.inr v := fun p z u h => hv p _ u (by rw [gpVar_inr]; exact h)

lemma law_one_var {μ : Measure 𝒳} (c : ℝ) (a : Idx1 E κ) :
    Var[fun w => ∑ i, (![c] : Fin 1 → ℝ) i * hinge φ (((![a] : Fin 1 → Idx1 E κ) i).1 : E) ((![a] : Fin 1 → Idx1 E κ) i).2 w; μ] =
      c ^ 2 * Var[hinge φ (a.1 : E) a.2; μ] := by
  have : (fun w => ∑ i, (![c] : Fin 1 → ℝ) i * hinge φ (((![a] : Fin 1 → Idx1 E κ) i).1 : E) ((![a] : Fin 1 → Idx1 E κ) i).2 w) =
      fun w => c * hinge φ (a.1 : E) a.2 w := by
    funext w; simp
  rw [this, variance_const_mul]

lemma law_inl {P Q : Measure 𝒳} [IsProbabilityMeasure Q] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {𝔾 : Ω' → C(Idx2 E κ, ℝ)} (h𝔾 : IsLimitGP φ P Q 1 1 κ μ' 𝔾) (c : ℝ) (a : Idx1 E κ) :
    μ'.map (fun ω => c * 𝔾 ω (Sum.inl a)) = gaussianReal 0 (c ^ 2 * Var[hinge φ (a.1 : E) a.2; P]).toNNReal := by
  have h := h𝔾.2 1 (fun i => Sum.inl ((![a] : Fin 1 → Idx1 E κ) i)) ![c]
  rw [gpVar_inl, law_one_var] at h
  rw [← h]; congr 1; funext ω; simp

lemma law_inr {P Q : Measure 𝒳} [IsProbabilityMeasure P] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {𝔾 : Ω' → C(Idx2 E κ, ℝ)} (h𝔾 : IsLimitGP φ P Q 1 1 κ μ' 𝔾) (c : ℝ) (a : Idx1 E κ) :
    μ'.map (fun ω => c * 𝔾 ω (Sum.inr a)) = gaussianReal 0 (c ^ 2 * Var[hinge φ (a.1 : E) a.2; Q]).toNNReal := by
  have h := h𝔾.2 1 (fun i => Sum.inr ((![a] : Fin 1 → Idx1 E κ) i)) ![c]
  rw [gpVar_inr, law_one_var] at h
  rw [← h]; congr 1; funext ω; simp

variable (μ : Measure 𝒳) [IsProbabilityMeasure μ] (side : Idx1 E κ → Idx2 E κ) {v : C(Idx2 E κ, ℝ)}

lemma SideCons.rel_ae (hv : SideCons φ μ κ side v) (a b : Idx1 E κ) (l d : ℝ)
    (h : ∀ᵐ x ∂μ, hinge φ (a.1 : E) a.2 x = l * hinge φ (b.1 : E) b.2 x + d) : v (side a) = l * v (side b) := by
  have := hv 2 ![a, b] ![1, -l] ?_
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    linarith
  · have hfun : (fun w => ∑ i, (![1, -l] : Fin 2 → ℝ) i *
        hinge φ (((![a, b] : Fin 2 → Idx1 E κ) i).1 : E) ((![a, b] : Fin 2 → Idx1 E κ) i).2 w) =ᵐ[μ] fun _ => d := by
      filter_upwards [h] with w hw
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hw]
      ring
    rw [variance_congr hfun, variance_fun_const]

lemma SideCons.relProp (hv : SideCons φ μ κ side v) : RelProp φ κ side v :=
  fun a b l d h => hv.rel_ae μ side a b l d (ae_of_all _ h)

lemma hinge_low (hκ : ∀ x, ‖φ x‖ ≤ κ) {f : E} (hf : ‖f‖ ≤ 1) {t0 : ℝ} (ht0 : t0 = -κ) (x : 𝒳) :
    hinge φ f t0 x = ⟪f, φ x⟫ + κ := by
  have hb := (abs_le.1 (abs_inner_le_of_norm_le hκ hf x)).1
  unfold hinge; rw [ht0, sub_neg_eq_add]; exact max_eq_left (by linarith)

/-- `lem:Hprops` (c): at `α = 0`, `H(f) = 𝔾 ℓ_{f,−κ}`. -/
lemma Hfun_alpha0 (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hv : SideCons φ μ κ side v) (f : Ball E)
    (t0 : Icc (-κ) κ) (ht0 : (t0 : ℝ) = -κ) : Hfun φ 0 μ κ side v f = v (side (f, t0)) := by
  have hκ0 := kappa_nonneg hκ μ
  have hf : ‖(f : E)‖ ≤ 1 := mem_closedBall_zero_iff.1 f.2
  have hall : ∀ t ∈ argminSet φ 0 μ κ (f : E), v (side (f, t)) = v (side (f, t0)) := by
    intro t ht
    have h0 := hinge_low hκ hf ht0
    have hmin := (mem_argminSet_iff.1 ht) t0
    simp only [cvObj, sub_zero, div_one, one_mul] at hmin
    set g : 𝒳 → ℝ := fun x => hinge φ (f : E) t x - hinge φ (f : E) t0 x + (κ + t) with hg
    have hg0 : 0 ≤ᵐ[μ] g := ae_of_all _ fun x => by
      simp only [hg, Pi.zero_apply, h0]
      have := le_max_left (⟪(f : E), φ x⟫ - t) 0
      unfold hinge; linarith
    have hi1 := integrable_hinge hφ hκ μ (f : E) t
    have hi2 := integrable_hinge hφ hκ μ (f : E) t0
    have hi12 : Integrable (fun x => hinge φ (f : E) t x - hinge φ (f : E) t0 x) μ := hi1.sub hi2
    have hgi : Integrable g μ := hi12.add (integrable_const _)
    have hint : ∫ x, g x ∂μ = 0 := by
      refine le_antisymm ?_ (integral_nonneg_of_ae hg0)
      have : ∫ x, g x ∂μ = ∫ x, hinge φ (f : E) t x ∂μ - ∫ x, hinge φ (f : E) t0 x ∂μ + (κ + t) := by
        simp only [hg]
        rw [integral_add hi12 (integrable_const _), integral_sub hi1 hi2, integral_const, smul_eq_mul,
          probReal_univ, one_mul]
      rw [this]; linarith
    have hae := (integral_eq_zero_iff_of_nonneg_ae hg0 hgi).1 hint
    refine (hv.rel_ae μ side (f, t) (f, t0) 1 (-κ - t) ?_).trans (one_mul _)
    filter_upwards [hae] with x hx
    simp only [hg, Pi.zero_apply] at hx
    linarith
  unfold Hfun
  have hne := argminSet_nonempty hφ hκ hκ0 0 μ (f : E)
  have himg : (fun t => v (side (f, t))) '' argminSet φ 0 μ κ (f : E) = {v (side (f, t0))} := by
    ext y; constructor
    · rintro ⟨t, ht, rfl⟩; exact hall t ht
    · intro hy; obtain ⟨t, ht⟩ := hne; exact ⟨t, ht, (hall t ht).trans hy.symm⟩
  rw [himg, csInf_singleton]; try norm_num

variable [FiniteDimensional ℝ E] in
/-- `lem:Hprops` (c): `f ↦ 𝔾 ℓ_{f,−κ}` is `⟨·, G⟩` on `𝔹_r`. -/
lemma exists_G (hκ : ∀ x, ‖φ x‖ ≤ κ) (hv : SideCons φ μ κ side v) (t0 : Icc (-κ) κ) (ht0 : (t0 : ℝ) = -κ) :
    ∃ G : E, ∀ f : Ball E, ⟪(f : E), G⟫ = v (side (f, t0)) := by
  have hrel : ∀ (p : ℕ) (e : Fin p → E) (a : Fin p → ℝ), (∀ i, e i ∈ closedBall (0 : E) 1) →
      ∑ i, a i • e i = 0 → ∑ i, a i * (fun e => v (side (ballOf e, t0))) (e i) = 0 := by
    intro p e a he hsum
    apply hv p (fun i => (ballOf (e i), t0)) a
    have hfun : (fun w => ∑ i, a i * hinge φ (((fun i => (ballOf (e i), t0)) i).1 : E) ((fun i => (ballOf (e i), t0)) i).2 w) =
        fun _ => (∑ i, a i) * κ := by
      funext w
      have hh : ∀ i, hinge φ ((ballOf (e i) : Ball E) : E) t0 w = ⟪e i, φ w⟫ + κ := fun i => by
        have hei := mem_closedBall_zero_iff.1 (he i)
        rw [ballOf_coe hei]; exact hinge_low hκ hei ht0 w
      simp only [hh, mul_add, Finset.sum_add_distrib]
      have h2 : ∑ i, a i * ⟪e i, φ w⟫ = ⟪∑ i, a i • e i, φ w⟫ := by
        rw [sum_inner]; simp only [real_inner_smul_left]
      rw [h2, hsum, inner_zero_left, zero_add, Finset.sum_mul]
    rw [hfun, variance_fun_const]
  obtain ⟨G, hG⟩ := exists_inner_eq_of_relations (closedBall (0 : E) 1) (fun e => v (side (ballOf e, t0))) hrel
  refine ⟨G, fun f => ?_⟩
  rw [hG f f.2]
  have : (ballOf (f : E) : Ball E) = f := Subtype.ext (ballOf_coe (mem_closedBall_zero_iff.1 f.2))
  rw [this]

omit [IsProbabilityMeasure μ] in
lemma Hfun_singleton (α : ℝ) (f : Ball E) (tf : Icc (-κ) κ) (h : argminSet φ α μ κ (f : E) = {tf}) :
    Hfun φ α μ κ side v f = 1 / (1 - α) * v (side (f, tf)) := by
  unfold Hfun; rw [h, image_singleton, csInf_singleton]

/-- The law of `⟨u, G⟩`. -/
lemma law_inner (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} {𝔾 : Ω' → C(Idx2 E κ, ℝ)}
    (hlaw : ∀ (c : ℝ) (a : Idx1 E κ), μ'.map (fun ω => c * 𝔾 ω (side a)) =
      gaussianReal 0 (c ^ 2 * Var[hinge φ (a.1 : E) a.2; μ]).toNNReal)
    (t0 : Icc (-κ) κ) (ht0 : (t0 : ℝ) = -κ) (G : Ω' → E)
    (hG : ∀ᵐ ω ∂μ', ∀ f : Ball E, ⟪(f : E), G ω⟫ = 𝔾 ω (side (f, t0))) (u : E) :
    μ'.map (fun ω => ⟪u, G ω⟫) = gaussianReal 0 (Var[fun x => ⟪u, φ x⟫; μ]).toNNReal := by
  set s := ‖u‖
  set e := ‖u‖⁻¹ • u
  have he : ‖e‖ ≤ 1 := norm_normalize_le u
  have hu : u = s • e := (smul_normalize u).symm
  have hae : (fun ω => ⟪u, G ω⟫) =ᵐ[μ'] fun ω => s * 𝔾 ω (side (ballOf e, t0)) := by
    filter_upwards [hG] with ω hω
    rw [← hω (ballOf e), ballOf_coe he, hu, real_inner_smul_left]
  rw [Measure.map_congr hae, hlaw s (ballOf e, t0)]
  congr 2
  have hm : AEStronglyMeasurable (fun x => ⟪e, φ x⟫) μ :=
    (stronglyMeasurable_const.inner hφ).aestronglyMeasurable
  have h1 : Var[hinge φ ((ballOf e : Ball E) : E) t0; μ] = Var[fun x => ⟪e, φ x⟫; μ] := by
    have : hinge φ ((ballOf e : Ball E) : E) t0 = fun x => ⟪e, φ x⟫ + κ := by
      funext x; rw [ballOf_coe he]; exact hinge_low hκ he ht0 x
    rw [this, variance_add_const hm]
  have h2 : (fun x => ⟪u, φ x⟫) = fun x => s * ⟪e, φ x⟫ := by
    funext x; rw [hu, real_inner_smul_left]
  rw [h1, h2, variance_const_mul]

end Side

theorem boundary_Hprops : Claims.boundary_Hprops := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ Ω' _ μ' _ 𝔾 hφ hκ hα0 hα1 h𝔾
  have hκ0 := kappa_nonneg hκ P
  have hL := ae_linCons h𝔾
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a), (b)
    filter_upwards [hL] with ω hv
    have hRP := (sideCons_inl hv).relProp P Sum.inl
    have hRQ := (sideCons_inr hv).relProp Q Sum.inr
    refine ⟨fun f hf => ⟨?_, ?_⟩, fun f g c hc0 hc1 hgf => ⟨?_, ?_⟩⟩
    · have := Hfun_smul hφ hκ hα0 hα1 P Sum.inl continuous_inl (𝔾 ω) hRP f f le_rfl zero_le_one
        (by rw [hf, zero_smul])
      rw [this, zero_mul]
    · have := Hfun_smul hφ hκ hα0 hα1 Q Sum.inr continuous_inr (𝔾 ω) hRQ f f le_rfl zero_le_one
        (by rw [hf, zero_smul])
      rw [this, zero_mul]
    · exact Hfun_smul hφ hκ hα0 hα1 P Sum.inl continuous_inl (𝔾 ω) hRP f g hc0 hc1 hgf
    · exact Hfun_smul hφ hκ hα0 hα1 Q Sum.inr continuous_inr (𝔾 ω) hRQ f g hc0 hc1 hgf
  · -- (c)
    intro hα
    subst hα
    let t0 : Icc (-κ) κ := ⟨-κ, le_rfl, by linarith⟩
    classical
    let GP : Ω' → E := fun ω => if h : LinCons φ P Q κ (𝔾 ω) then
      (exists_G P Sum.inl hκ (sideCons_inl h) t0 rfl).choose else 0
    let GQ : Ω' → E := fun ω => if h : LinCons φ P Q κ (𝔾 ω) then
      (exists_G Q Sum.inr hκ (sideCons_inr h) t0 rfl).choose else 0
    have hGP : ∀ᵐ ω ∂μ', ∀ f : Ball E, ⟪(f : E), GP ω⟫ = 𝔾 ω (Sum.inl (f, t0)) := by
      filter_upwards [hL] with ω hv f
      simp only [GP, dite_eq_left hv]
      exact (exists_G P Sum.inl hκ (sideCons_inl hv) t0 rfl).choose_spec f
    have hGQ : ∀ᵐ ω ∂μ', ∀ f : Ball E, ⟪(f : E), GQ ω⟫ = 𝔾 ω (Sum.inr (f, t0)) := by
      filter_upwards [hL] with ω hv f
      simp only [GQ, dite_eq_left hv]
      exact (exists_G Q Sum.inr hκ (sideCons_inr hv) t0 rfl).choose_spec f
    refine ⟨GP, GQ, ?_, fun u => ⟨law_inner P Sum.inl hφ hκ (law_inl h𝔾) t0 rfl GP hGP u,
      law_inner Q Sum.inr hφ hκ (law_inr h𝔾) t0 rfl GQ hGQ u⟩⟩
    filter_upwards [hL, hGP, hGQ] with ω hv hP hQ f t ht
    have ht' : t = t0 := Subtype.ext ht
    subst ht'
    have e1 := Hfun_alpha0 P Sum.inl hφ hκ (sideCons_inl hv) f t0 rfl
    have e2 := Hfun_alpha0 Q Sum.inr hφ hκ (sideCons_inr hv) f t0 rfl
    exact ⟨e1, e1.trans (hP f).symm, e2, e2.trans (hQ f).symm⟩
  · -- (d), `P`
    intro f tf htf
    have hH : ∀ ω, Hfun φ α P κ Sum.inl (𝔾 ω) f = 1 / (1 - α) * 𝔾 ω (Sum.inl (f, tf)) := fun ω =>
      Hfun_singleton P Sum.inl α f tf htf
    refine ⟨hH, ?_⟩
    rw [show (fun ω => Hfun φ α P κ Sum.inl (𝔾 ω) f) = fun ω => 1 / (1 - α) * 𝔾 ω (Sum.inl (f, tf)) from funext hH,
      law_inl h𝔾]
  · -- (d), `Q`
    intro f tf htf
    have hH : ∀ ω, Hfun φ α Q κ Sum.inr (𝔾 ω) f = 1 / (1 - α) * 𝔾 ω (Sum.inr (f, tf)) := fun ω =>
      Hfun_singleton Q Sum.inr α f tf htf
    refine ⟨hH, ?_⟩
    rw [show (fun ω => Hfun φ α Q κ Sum.inr (𝔾 ω) f) = fun ω => 1 / (1 - α) * 𝔾 ω (Sum.inr (f, tf)) from funext hH,
      law_inr h𝔾]

end StatFormal.Wave30ah
