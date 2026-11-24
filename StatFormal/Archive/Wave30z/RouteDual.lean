import StatFormal.Archive.Wave30z.Statements
import StatFormal.Archive.Wave30v.RouteDelta
import StatFormal.Archive.Wave8a.RouteCvar

/-!
# Route — wave 30z `boundary_dual` (`thm:boundary` (a), the dual representation) (untrusted)

`A = 𝒞_α(μ)`, `B = 𝒞_α(ν)` (the frozen `region`) are nonempty (`g ≡ 1`), convex and bounded (`‖∫ g φ‖ ≤ βκ`).
* CVaR (`cvar_core`, Wave 8a `lem:cvar`): `h_A(f) = min_{t ∈ ℝ} cv_μ(f, t)`, `cv_μ(f, t) = t + β μ ℓ_{f,t}`.
  For `‖f‖ ≤ 1` the minimum over `ℝ` is a minimum over `[−κ, κ]`: for `t ≥ κ`, `ℓ_{f,t} = ℓ_{f,κ} = 0`, so
  `cv(t) = t ≥ κ = cv(κ)`; for `t ≤ −κ`, `ℓ_{f,t} = ℓ_{f,−κ} + (−κ − t)`, so `cv(t) = cv(−κ) + (β − 1)(−κ − t)`.
  Hence `Γ(g, t, s) = −cv_μ(−g, t) − cv_ν(g, s) ≤ −h_A(−g) − h_B(g)`, with equality for suitable `t, s`.
* Duality: `ψ(g) := −h_A(−g) − h_B(g) ≤ ⟨g, a − b⟩ ≤ ‖a − b‖`, so `Γ ≤ ψ ≤ dist(A, B)`; the closures are compact
  convex, and the nearest-point argument of Wave 30v `boundary_dist_dual` (`exists_dual_ge_setDist`, redone for any
  universe) gives `g*` with `ψ_{Ā,B̄}(g*) ≥ dist(Ā, B̄) ≥ dist(A, B)`; and `h_A ≤ h_{Ā}`. So `D = max_𝔹 ψ`, attained.
* Argmax: `Γ(θ) = D` iff `ψ(g) = D` (`g ∈ G*`) and `t, s` are CVaR minimisers on `[−κ, κ]`. Separated case
  (`D > 0`): `D = ψ(g) ≤ ⟨g, a − b⟩ ≤ ‖g‖ ‖a − b‖ ≤ D` forces `g = (a − b)/‖a − b‖`. Contact case: `D = 0` and
  `ψ(g) ≥ 0` iff `⟨g, b − a⟩ ≤ 0` on `B × A`, i.e. `G* = (B − A)° ∩ 𝔹`.
* Library: measurability, bounds and Lipschitz estimates for the hinge; continuity of `Γ` on `Θ`; nonemptiness
  of `argminSet`; integrals against, and normalisation of, the empirical measure.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30z

open StatFormal.TrimmedMMD.Concentration (region empirical)
open StatFormal.TrimmedMMD.Unconditional (setDist Dpop Demp)
open StatFormal.Wave30v (supFun Ball ballNeg polarSet coneHull supportFn dualObj valueFn)

section Hinge
variable {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma measurable_hinge {φ : 𝒳 → E} (hφ : StronglyMeasurable φ) (f : E) (t : ℝ) :
    Measurable (hinge φ f t) := by
  have h : Measurable fun x => ⟪f, φ x⟫ := (stronglyMeasurable_const.inner hφ).measurable
  exact (h.sub_const t).max measurable_const

omit [MeasurableSpace 𝒳] in
lemma hinge_nonneg (φ : 𝒳 → E) (f : E) (t : ℝ) (x : 𝒳) : 0 ≤ hinge φ f t x := le_max_right _ _

omit [MeasurableSpace 𝒳] in
lemma abs_inner_le_of_norm_le {φ : 𝒳 → E} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {f : E} (hf : ‖f‖ ≤ 1) (x : 𝒳) :
    |⟪f, φ x⟫| ≤ κ :=
  (abs_real_inner_le_norm f (φ x)).trans (by nlinarith [norm_nonneg f, norm_nonneg (φ x), hκ x])

omit [MeasurableSpace 𝒳] in
lemma abs_hinge_le {φ : 𝒳 → E} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {f : E} (hf : ‖f‖ ≤ 1) {t : ℝ}
    (ht : |t| ≤ κ) (x : 𝒳) : |hinge φ f t x| ≤ 2 * κ := by
  rw [abs_of_nonneg (hinge_nonneg φ f t x)]
  have h1 := abs_le.1 (abs_inner_le_of_norm_le hκ hf x)
  have h2 := abs_le.1 ht
  have h3 := abs_nonneg t
  exact max_le (by linarith) (by linarith)

omit [MeasurableSpace 𝒳] in
lemma abs_hinge_sub_le {φ : 𝒳 → E} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (f f' : E) (t t' : ℝ) (x : 𝒳) :
    |hinge φ f t x - hinge φ f' t' x| ≤ κ * ‖f - f'‖ + |t - t'| := by
  unfold hinge
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have h1 : |⟪f, φ x⟫ - ⟪f', φ x⟫| ≤ κ * ‖f - f'‖ := by
    rw [← inner_sub_left]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hκ x) (norm_nonneg _)
  have h2 : ⟪f, φ x⟫ - t - (⟪f', φ x⟫ - t') = (⟪f, φ x⟫ - ⟪f', φ x⟫) + (t' - t) := by ring
  rw [h2]
  refine (abs_add_le _ _).trans ?_
  rw [abs_sub_comm t' t]
  linarith

lemma integrable_hinge {φ : 𝒳 → E} (hφ : StronglyMeasurable φ) {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (μ : Measure 𝒳) [IsFiniteMeasure μ] (f : E) (t : ℝ) : Integrable (hinge φ f t) μ := by
  refine Integrable.of_bound (measurable_hinge hφ f t).aestronglyMeasurable (κ * ‖f‖ + |t|)
    (ae_of_all _ fun x => ?_)
  have h := abs_hinge_sub_le hκ f 0 t 0 x
  have h0 : hinge φ 0 0 x = 0 := by simp [hinge]
  rw [h0, sub_zero, sub_zero, sub_zero] at h
  rwa [Real.norm_eq_abs]

lemma abs_integral_hinge_sub_le {φ : 𝒳 → E} (hφ : StronglyMeasurable φ) {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (μ : Measure 𝒳) [IsFiniteMeasure μ] (f f' : E) (t t' : ℝ) :
    |∫ x, hinge φ f t x ∂μ - ∫ x, hinge φ f' t' x ∂μ| ≤ (κ * ‖f - f'‖ + |t - t'|) * μ.real univ := by
  rw [← integral_sub (integrable_hinge hφ hκ μ f t) (integrable_hinge hφ hκ μ f' t')]
  have := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun x => hinge φ f t x - hinge φ f' t' x) (C := κ * ‖f - f'‖ + |t - t'|)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_hinge_sub_le hκ f f' t t' x)
  rwa [Real.norm_eq_abs] at this

/-- `(f, t) ↦ μ ℓ_{f,t}` is (Lipschitz) continuous. -/
lemma continuous_integral_hinge {φ : 𝒳 → E} (hφ : StronglyMeasurable φ) {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (μ : Measure 𝒳) [IsFiniteMeasure μ] :
    Continuous (fun p : E × ℝ => ∫ x, hinge φ p.1 p.2 x ∂μ) := by
  set C := (|κ| + 1) * μ.real univ with hCdef
  have hm : 0 ≤ μ.real univ := measureReal_nonneg
  have hC : 0 ≤ C := by positivity
  refine (LipschitzWith.of_dist_le_mul (K := C.toNNReal) fun p q => ?_).continuous
  rw [Real.coe_toNNReal _ hC, Real.dist_eq]
  refine (abs_integral_hinge_sub_le hφ hκ μ _ _ _ _).trans ?_
  have h1 : ‖p.1 - q.1‖ ≤ dist p q := by rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_left _ _
  have h2 : |p.2 - q.2| ≤ dist p q := by rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_right _ _
  have h3 : κ * ‖p.1 - q.1‖ ≤ |κ| * dist p q :=
    calc κ * ‖p.1 - q.1‖ ≤ |κ| * ‖p.1 - q.1‖ := mul_le_mul_of_nonneg_right (le_abs_self κ) (norm_nonneg _)
      _ ≤ |κ| * dist p q := mul_le_mul_of_nonneg_left h1 (abs_nonneg κ)
  calc (κ * ‖p.1 - q.1‖ + |p.2 - q.2|) * μ.real univ ≤ ((|κ| + 1) * dist p q) * μ.real univ := by
        apply mul_le_mul_of_nonneg_right _ hm; linarith
    _ = C * dist p q := by rw [hCdef]; ring

/-- `Γ_{μ,ν}` is continuous on `Θ`. -/
lemma continuous_dualTrim {φ : 𝒳 → E} (hφ : StronglyMeasurable φ) {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (α : ℝ)
    (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Continuous (dualTrim φ α μ ν (κ := κ)) := by
  have hg : Continuous (fun θ : Theta E κ => (θ.1 : E)) := continuous_subtype_val.comp continuous_fst
  have ht : Continuous (fun θ : Theta E κ => (θ.2.1 : ℝ)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hs : Continuous (fun θ : Theta E κ => (θ.2.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have h1 := (continuous_integral_hinge hφ hκ μ).comp (hg.neg.prodMk ht)
  have h2 := (continuous_integral_hinge hφ hκ ν).comp (hg.prodMk hs)
  exact ((ht.neg.sub (continuous_const.mul h1)).sub hs).sub (continuous_const.mul h2)

/-- The CVaR objective `t ↦ t + β μ ℓ_{f,t}`. -/
def cvObj (φ : 𝒳 → E) (α : ℝ) (μ : Measure 𝒳) (f : E) (t : ℝ) : ℝ :=
  t + 1 / (1 - α) * ∫ x, hinge φ f t x ∂μ

lemma continuous_cvObj {φ : 𝒳 → E} (hφ : StronglyMeasurable φ) {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (α : ℝ)
    (μ : Measure 𝒳) [IsFiniteMeasure μ] (f : E) : Continuous (cvObj φ α μ f) :=
  continuous_id.add (continuous_const.mul
    ((continuous_integral_hinge hφ hκ μ).comp (continuous_const.prodMk continuous_id)))

lemma dualTrim_eq_cvObj (φ : 𝒳 → E) (α : ℝ) (μ ν : Measure 𝒳) {κ : ℝ} (θ : Theta E κ) :
    dualTrim φ α μ ν θ = -cvObj φ α μ (-(θ.1 : E)) θ.2.1 - cvObj φ α ν (θ.1 : E) θ.2.2 := by
  unfold dualTrim cvObj; ring

lemma mem_argminSet_iff {φ : 𝒳 → E} {α : ℝ} {μ : Measure 𝒳} {κ : ℝ} {f : E} {t : Icc (-κ) κ} :
    t ∈ argminSet φ α μ κ f ↔ ∀ t' : Icc (-κ) κ, cvObj φ α μ f t ≤ cvObj φ α μ f t' := Iff.rfl

lemma argminSet_nonempty {φ : 𝒳 → E} (hφ : StronglyMeasurable φ) {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hκ0 : 0 ≤ κ) (α : ℝ) (μ : Measure 𝒳) [IsFiniteMeasure μ] (f : E) :
    (argminSet φ α μ κ f).Nonempty := by
  have : Nonempty (Icc (-κ) κ) := ⟨⟨0, by constructor <;> linarith⟩⟩
  have hc : Continuous fun t : Icc (-κ) κ => cvObj φ α μ f t :=
    (continuous_cvObj hφ hκ α μ f).comp continuous_subtype_val
  obtain ⟨t, -, ht⟩ := isCompact_univ.exists_isMinOn univ_nonempty hc.continuousOn
  exact ⟨t, fun t' => ht (mem_univ t')⟩

/-- Clamping to `[−κ, κ]` does not increase the CVaR objective (`‖f‖ ≤ 1`, `β ≥ 1`). -/
lemma exists_Icc_cvObj_le {φ : 𝒳 → E} (hφ : StronglyMeasurable φ) {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hκ0 : 0 ≤ κ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (μ : Measure 𝒳) [IsProbabilityMeasure μ] {f : E}
    (hf : ‖f‖ ≤ 1) (t : ℝ) : ∃ t' : Icc (-κ) κ, cvObj φ α μ f t' ≤ cvObj φ α μ f t := by
  have hβ : 1 ≤ 1 / (1 - α) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hb := fun x => abs_le.1 (abs_inner_le_of_norm_le hκ hf x)
  by_cases h1 : κ ≤ t
  · refine ⟨⟨κ, by constructor <;> linarith⟩, ?_⟩
    have e : ∀ s, κ ≤ s → ∀ x, hinge φ f s x = 0 := fun s hs x => by
      unfold hinge; exact max_eq_right (by linarith [(hb x).2])
    unfold cvObj
    simp only
    rw [integral_congr_ae (ae_of_all _ (e κ le_rfl)), integral_congr_ae (ae_of_all _ (e t h1))]
    simp only [integral_zero, mul_zero, add_zero]
    exact h1
  by_cases h2 : t ≤ -κ
  · refine ⟨⟨-κ, by constructor <;> linarith⟩, ?_⟩
    have e : ∀ x, hinge φ f t x = hinge φ f (-κ) x + (-κ - t) := fun x => by
      unfold hinge
      rw [max_eq_left (by linarith [(hb x).1]), max_eq_left (by linarith [(hb x).1])]
      ring
    unfold cvObj
    simp only
    rw [integral_congr_ae (ae_of_all _ e), integral_add (integrable_hinge hφ hκ μ f (-κ))
      (integrable_const _), integral_const, probReal_univ, one_smul]
    nlinarith
  · exact ⟨⟨t, by constructor <;> linarith⟩, le_rfl⟩

lemma region_isBounded' (μ : Measure 𝒳) [IsFiniteMeasure μ] {φ : 𝒳 → E} {κ α : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) : Bornology.IsBounded (region φ α μ) := by
  refine (isBounded_closedBall (x := (0 : E)) (r := 1 / (1 - α) * κ * μ.real univ)).subset ?_
  rintro _ ⟨g, -, hgb, -, rfl⟩
  rw [mem_closedBall, dist_zero_right]
  refine norm_integral_le_of_norm_le_const (ae_of_all _ fun x => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hgb x).1]
  exact mul_le_mul (hgb x).2 (hκ x) (norm_nonneg _) ((hgb x).1.trans (hgb x).2)

/-- `lem:cvar` on `[−κ, κ]`: for `‖f‖ ≤ 1`, `h_{𝒞_α(μ)}(f) = min_{t ∈ [−κ, κ]} {t + β μ ℓ_{f,t}}`. -/
lemma isLeast_cvObj [CompleteSpace E] {φ : 𝒳 → E} (hφ : StronglyMeasurable φ) {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (μ : Measure 𝒳)
    [IsProbabilityMeasure μ] {f : E} (hf : ‖f‖ ≤ 1) :
    IsLeast (range fun t : Icc (-κ) κ => cvObj φ α μ f t) (supportFn (region φ α μ) f) := by
  have hY : Measurable fun x => ⟪f, φ x⟫ := (stronglyMeasurable_const.inner hφ).measurable
  obtain ⟨v, hv1, hv2⟩ := StatFormal.Wave8a.cvar_core μ hY (abs_inner_le_of_norm_le hκ hf) hα0 hα1
  have hset : (fun a => ⟪f, a⟫) '' region φ α μ =
      {r | ∃ g, StatFormal.TrimmedMMD.ZeroSet.IsTrimDensity μ α g ∧ r = ∫ x, g x * ⟪f, φ x⟫ ∂μ} := by
    ext r
    constructor
    · rintro ⟨_, ⟨g, hg, hgb, hg1, rfl⟩, rfl⟩
      exact ⟨g, ⟨hg, hgb, hg1⟩,
        StatFormal.TrimmedMMD.Concentration.inner_integral_smul μ hφ hκ hg hgb f⟩
    · rintro ⟨g, ⟨hg, hgb, hg1⟩, rfl⟩
      exact ⟨∫ x, g x • φ x ∂μ, ⟨g, hg, hgb, hg1, rfl⟩,
        StatFormal.TrimmedMMD.Concentration.inner_integral_smul μ hφ hκ hg hgb f⟩
  have hsv : supportFn (region φ α μ) f = v := by
    unfold supportFn; rw [hset]; exact hv1.csSup_eq
  rw [hsv]
  obtain ⟨⟨t0, ht0⟩, hlow⟩ := hv2
  refine ⟨?_, ?_⟩
  · obtain ⟨t', ht'⟩ := exists_Icc_cvObj_le hφ hκ hκ0 hα0 hα1 μ hf t0
    refine ⟨t', le_antisymm ?_ (hlow ⟨t', rfl⟩)⟩
    exact ht'.trans (le_of_eq ht0)
  · rintro _ ⟨t, rfl⟩
    exact hlow ⟨t, rfl⟩

end Hinge

section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma lipschitz_supportFn_le {S : Set E} (hne : S.Nonempty) {R : ℝ} (hR : S ⊆ closedBall 0 R) (g g' : E) :
    supportFn S g ≤ supportFn S g' + R * ‖g - g'‖ := by
  have hb : Bornology.IsBounded S := isBounded_closedBall.subset hR
  refine Wave30v.supportFn_le hne fun s hs => ?_
  have h1 := Wave30v.le_supportFn hb g' hs
  have hs' : ‖s‖ ≤ R := mem_closedBall_zero_iff.1 (hR hs)
  have h2 : ⟪g - g', s⟫ ≤ R * ‖g - g'‖ :=
    (real_inner_le_norm _ _).trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hs' (norm_nonneg _))
  rw [inner_sub_left] at h2
  linarith

lemma continuous_supportFn {S : Set E} (hS : Bornology.IsBounded S) (hne : S.Nonempty) :
    Continuous (supportFn S) := by
  obtain ⟨R, hR⟩ := hS.subset_closedBall 0
  obtain ⟨s, hs⟩ := hne
  have hR0 : 0 ≤ R := (norm_nonneg s).trans (mem_closedBall_zero_iff.1 (hR hs))
  refine (LipschitzWith.of_le_add_mul R.toNNReal fun g g' => ?_).continuous
  rw [Real.coe_toNNReal _ hR0, dist_eq_norm]
  exact lipschitz_supportFn_le ⟨s, hs⟩ hR g g'

lemma setDist_le_setDist_closure {A B : Set E} (hA : A.Nonempty) (hB : B.Nonempty) :
    setDist A B ≤ setDist (closure A) (closure B) := by
  refine Wave30v.le_setDist hA.closure hB.closure fun a ha b hb => ?_
  have hcl : IsClosed {p : E × E | setDist A B ≤ ‖p.1 - p.2‖} :=
    isClosed_le continuous_const (continuous_fst.sub continuous_snd).norm
  have hsub : A ×ˢ B ⊆ {p : E × E | setDist A B ≤ ‖p.1 - p.2‖} := fun p hp =>
    Wave30v.setDist_le' hp.1 hp.2
  have hab : (a, b) ∈ closure (A ×ˢ B) := by rw [closure_prod_eq]; exact ⟨ha, hb⟩
  exact closure_minimal hsub hcl hab

/-- `0 ≤ −h_A(−g) − h_B(g)` iff `g ∈ (B − A)°` (`⟨g, b⟩ ≤ ⟨g, a⟩` on `B × A`). -/
lemma dual_nonneg_iff {A B : Set E} (hAne : A.Nonempty) (hBne : B.Nonempty) (hAb : Bornology.IsBounded A)
    (hBb : Bornology.IsBounded B) (g : E) :
    0 ≤ -supportFn A (-g) - supportFn B g ↔ g ∈ polarSet (B - A) := by
  constructor
  · intro h0
    rintro _ ⟨b, hb, a, ha, rfl⟩
    have h1 := Wave30v.le_supportFn hAb (-g) ha
    have h2 := Wave30v.le_supportFn hBb g hb
    rw [inner_neg_left] at h1
    rw [inner_sub_right]
    linarith
  · intro hg
    have h1 : ∀ a ∈ A, supportFn B g ≤ ⟪g, a⟫ := fun a ha =>
      Wave30v.supportFn_le hBne fun b hb => by
        have := hg (b - a) ⟨b, hb, a, ha, rfl⟩
        rw [inner_sub_right] at this; linarith
    have h2 : supportFn A (-g) ≤ -supportFn B g :=
      Wave30v.supportFn_le hAne fun a ha => by rw [inner_neg_left]; linarith [h1 a ha]
    linarith

/-- `−h_A(−g) − h_B(g) ≤ dist(A, B)` on the unit ball. -/
lemma dual_le_setDist {A B : Set E} (hAne : A.Nonempty) (hBne : B.Nonempty) (hAb : Bornology.IsBounded A)
    (hBb : Bornology.IsBounded B) {g : E} (hg : ‖g‖ ≤ 1) :
    -supportFn A (-g) - supportFn B g ≤ setDist A B :=
  Wave30v.le_setDist hAne hBne fun _ ha _ hb => Wave30v.dual_le_norm hAb hBb hg ha hb

end Geometry

section Empirical
variable {𝒳 : Type*} [MeasurableSpace 𝒳]

lemma isProbabilityMeasure_empirical {n : ℕ} (x : Fin n → 𝒳) (hn : 1 ≤ n) :
    IsProbabilityMeasure (empirical x) := by
  have hn' : n ≠ 0 := by omega
  constructor
  have h1 : ENNReal.ofReal (1 / n) = (n : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn')), ENNReal.ofReal_one,
      ENNReal.ofReal_natCast, one_div]
  simp only [empirical, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, h1]
  exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hn') (ENNReal.natCast_ne_top n)

instance instIsProbabilityMeasureEmpirical {n : ℕ} [NeZero n] (x : Fin n → 𝒳) :
    IsProbabilityMeasure (empirical x) :=
  isProbabilityMeasure_empirical x (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))

lemma integral_empirical {n : ℕ} (x : Fin n → 𝒳) {h : 𝒳 → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ y, |h y| ≤ C) :
    ∫ w, h w ∂(empirical x) = (∑ i, h (x i)) / n := by
  unfold empirical
  rw [integral_finsetSum_measure fun i _ =>
    (Integrable.of_bound hh.aestronglyMeasurable C (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]; exact hC y)).smul_measure ENNReal.ofReal_ne_top]
  simp_rw [integral_smul_measure, integral_dirac' _ _ hh.stronglyMeasurable]
  rw [ENNReal.toReal_ofReal (by positivity), Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]; ring

end Empirical

section Main
variable {𝒳 : Type*} [MeasurableSpace 𝒳]

lemma kappa_nonneg {E : Type*} [NormedAddCommGroup E] {φ : 𝒳 → E} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (μ : Measure 𝒳) [IsProbabilityMeasure μ] : 0 ≤ κ := by
  have : Nonempty 𝒳 := nonempty_of_isProbabilityMeasure μ
  obtain ⟨x⟩ := this
  exact (norm_nonneg _).trans (hκ x)

/-- `Γ ≤ −h_A(−g) − h_B(g)`, with equality for suitable `t, s` (`lem:cvar` on `[−κ, κ]`). -/
lemma dualTrim_le_and_exists {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {φ : 𝒳 → E} (hφ : StronglyMeasurable φ) {κ α : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (μ ν : Measure 𝒳) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∀ θ : Theta E κ, dualTrim φ α μ ν θ ≤
        -supportFn (region φ α μ) (-(θ.1 : E)) - supportFn (region φ α ν) (θ.1 : E)) ∧
    (∀ g : Ball E, ∃ t s : Icc (-κ) κ, dualTrim φ α μ ν (g, t, s) =
        -supportFn (region φ α μ) (-(g : E)) - supportFn (region φ α ν) (g : E)) := by
  have hκ0 := kappa_nonneg hκ μ
  have hg1 : ∀ g : Ball E, ‖(g : E)‖ ≤ 1 := fun g => mem_closedBall_zero_iff.1 g.2
  have hg1' : ∀ g : Ball E, ‖-(g : E)‖ ≤ 1 := fun g => by rw [norm_neg]; exact hg1 g
  refine ⟨fun θ => ?_, fun g => ?_⟩
  · rw [dualTrim_eq_cvObj]
    have h1 := (isLeast_cvObj hφ hκ hκ0 hα0 hα1 μ (hg1' θ.1)).2 ⟨θ.2.1, rfl⟩
    have h2 := (isLeast_cvObj hφ hκ hκ0 hα0 hα1 ν (hg1 θ.1)).2 ⟨θ.2.2, rfl⟩
    linarith
  · obtain ⟨t, ht⟩ := (isLeast_cvObj hφ hκ hκ0 hα0 hα1 μ (hg1' g)).1
    obtain ⟨s, hs⟩ := (isLeast_cvObj hφ hκ hκ0 hα0 hα1 ν (hg1 g)).1
    refine ⟨t, s, ?_⟩
    rw [dualTrim_eq_cvObj]
    simp only at ht hs ⊢
    rw [ht, hs]

/-- Attainment in `lem:separation` for nonempty compact convex `A, B` (any real inner product space; the
nearest-point argument of Wave 30v `boundary_dist_dual`): some `‖g‖ ≤ 1` has `dist(A, B) ≤ −h_A(−g) − h_B(g)`. -/
lemma exists_dual_ge_setDist {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A B : Set E}
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hAc : IsCompact A) (hBc : IsCompact B) (hAcv : Convex ℝ A)
    (hBcv : Convex ℝ B) : ∃ g : E, ‖g‖ ≤ 1 ∧ setDist A B ≤ -supportFn A (-g) - supportFn B g := by
  obtain ⟨p, ⟨hpA, hpB⟩, hpmin⟩ := (hAc.prod hBc).exists_isMinOn (hAne.prod hBne)
    ((continuous_fst.sub continuous_snd).norm.continuousOn)
  set a := p.1; set b := p.2
  have hab : setDist A B = ‖a - b‖ := by
    refine le_antisymm (Wave30v.setDist_le' hpA hpB) (Wave30v.le_setDist hAne hBne fun a' ha' b' hb' => ?_)
    exact hpmin (show (a', b') ∈ A ×ˢ B from ⟨ha', hb'⟩)
  rw [hab]
  by_cases hd : ‖a - b‖ = 0
  · refine ⟨0, by simp, ?_⟩
    rw [hd, neg_zero, Wave30v.supportFn_zero hAne, Wave30v.supportFn_zero hBne]; simp
  · have hdpos : 0 < ‖a - b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    set d := ‖a - b‖ with hdd
    have hvA : ∀ w ∈ A, ⟪b - a, w - a⟫ ≤ 0 := by
      refine (norm_eq_iInf_iff_real_inner_le_zero hAcv hpA).1 ?_
      have : Nonempty A := ⟨⟨a, hpA⟩⟩
      have hbdd : BddBelow (Set.range fun w : A => ‖b - (w : E)‖) :=
        ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
      refine le_antisymm (le_ciInf fun w => ?_) (ciInf_le hbdd ⟨a, hpA⟩)
      rw [norm_sub_rev b a, norm_sub_rev b]
      exact hab.symm.trans_le (Wave30v.setDist_le' w.2 hpB)
    have hvB : ∀ w ∈ B, ⟪a - b, w - b⟫ ≤ 0 := by
      refine (norm_eq_iInf_iff_real_inner_le_zero hBcv hpB).1 ?_
      have : Nonempty B := ⟨⟨b, hpB⟩⟩
      have hbdd : BddBelow (Set.range fun w : B => ‖a - (w : E)‖) :=
        ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
      refine le_antisymm (le_ciInf fun w => ?_) (ciInf_le hbdd ⟨b, hpB⟩)
      exact hab.symm.trans_le (Wave30v.setDist_le' hpA w.2)
    set f := d⁻¹ • (a - b) with hf
    have hfn : ‖f‖ = 1 := by
      rw [hf, norm_smul, norm_inv, norm_norm, ← hdd]; exact inv_mul_cancel₀ hdpos.ne'
    have hfA : supportFn A (-f) ≤ -⟪f, a⟫ := by
      refine Wave30v.supportFn_le hAne fun w hw => ?_
      have := hvA w hw
      have h2 : ⟪f, w⟫ - ⟪f, a⟫ = d⁻¹ * (-⟪b - a, w - a⟫) := by
        rw [← inner_sub_right, hf, real_inner_smul_left, ← inner_neg_left, neg_sub]
      rw [inner_neg_left]
      nlinarith [inv_pos.2 hdpos]
    have hfB : supportFn B f ≤ ⟪f, b⟫ := by
      refine Wave30v.supportFn_le hBne fun w hw => ?_
      have := hvB w hw
      have h2 : ⟪f, w⟫ - ⟪f, b⟫ = d⁻¹ * ⟪a - b, w - b⟫ := by
        rw [← inner_sub_right, hf, real_inner_smul_left]
      nlinarith [inv_pos.2 hdpos]
    have hfab : ⟪f, a⟫ - ⟪f, b⟫ = d := by
      rw [← inner_sub_right, hf, real_inner_smul_left, real_inner_self_eq_norm_sq, ← hdd]
      field_simp
    exact ⟨f, hfn.le, by linarith⟩

lemma region_nonempty (μ : Measure 𝒳) [IsProbabilityMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {φ : 𝒳 → E} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) : (region φ α μ).Nonempty :=
  StatFormal.TrimmedMMD.Concentration.region_nonempty μ hα0 hα1

lemma convex_region (μ : Measure 𝒳) [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {φ : 𝒳 → E} (hφ : StronglyMeasurable φ) {κ α : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) :
    Convex ℝ (region φ α μ) :=
  StatFormal.TrimmedMMD.Concentration.region_convex μ hφ hκ

lemma isBounded_region (μ : Measure 𝒳) [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {φ : 𝒳 → E} {κ α : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) :
    Bornology.IsBounded (region φ α μ) :=
  region_isBounded' μ hκ

section Fin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {φ : 𝒳 → E} {κ α : ℝ}

omit [FiniteDimensional ℝ E] in
/-- `ψ(g) = −h_A(−g) − h_B(g) ≤ D` on the unit ball. -/
lemma dual_le_Dpop (_hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (g : Ball E) :
    -supportFn (region φ α P) (-(g : E)) - supportFn (region φ α Q) (g : E) ≤ Dpop φ P Q α :=
  dual_le_setDist (region_nonempty P hα0 hα1) (region_nonempty Q hα0 hα1) (isBounded_region P hκ)
    (isBounded_region Q hκ) (mem_closedBall_zero_iff.1 g.2)

/-- `D = max_{g ∈ 𝔹} ψ(g)` is attained. -/
lemma exists_dual_eq_Dpop (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ∃ g : Ball E, -supportFn (region φ α P) (-(g : E)) - supportFn (region φ α Q) (g : E) = Dpop φ P Q α := by
  have hAne := region_nonempty P hα0 hα1 (φ := φ)
  have hBne := region_nonempty Q hα0 hα1 (φ := φ)
  have hAb := isBounded_region P hκ (φ := φ) (α := α)
  have hBb := isBounded_region Q hκ (φ := φ) (α := α)
  obtain ⟨g, hg1, hg⟩ := exists_dual_ge_setDist hAne.closure hBne.closure hAb.isCompact_closure
    hBb.isCompact_closure (convex_region P hφ hκ).closure (convex_region Q hφ hκ).closure
  have h3 : ∀ (S : Set E), S.Nonempty → Bornology.IsBounded S → ∀ f : E,
      supportFn S f ≤ supportFn (closure S) f := fun S hS hSb f =>
    Wave30v.supportFn_le hS fun a ha => Wave30v.le_supportFn hSb.closure f (subset_closure ha)
  refine ⟨⟨g, mem_closedBall_zero_iff.2 hg1⟩, le_antisymm (dual_le_Dpop hφ hκ hα0 hα1 P Q _) ?_⟩
  have := setDist_le_setDist_closure hAne hBne
  have := h3 _ hAne hAb (-g)
  have := h3 _ hBne hBb g
  show setDist _ _ ≤ _
  linarith

lemma mem_Gstar_iff (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (g : Ball E) :
    g ∈ Gstar φ α P Q ↔
      -supportFn (region φ α P) (-(g : E)) - supportFn (region φ α Q) (g : E) = Dpop φ P Q α := by
  obtain ⟨g0, hg0⟩ := exists_dual_eq_Dpop hφ hκ hα0 hα1 P Q
  constructor
  · intro h
    exact le_antisymm (dual_le_Dpop hφ hκ hα0 hα1 P Q g) (hg0 ▸ h g0)
  · intro h g'
    rw [h]; exact dual_le_Dpop hφ hκ hα0 hα1 P Q g'

lemma Gstar_nonempty (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : (Gstar φ α P Q).Nonempty := by
  obtain ⟨g, hg⟩ := exists_dual_eq_Dpop hφ hκ hα0 hα1 P Q
  exact ⟨g, (mem_Gstar_iff hφ hκ hα0 hα1 P Q g).2 hg⟩

/-- The partial maximum of `Γ` over `(t, s) ∈ [−κ, κ]²` is `ψ(g) = −h_A(−g) − h_B(g)`. -/
lemma iSup_dualTrim_section (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (g : Ball E) :
    IsGreatest (range fun ts : Icc (-κ) κ × Icc (-κ) κ => dualTrim φ α P Q (g, ts.1, ts.2))
      (-supportFn (region φ α P) (-(g : E)) - supportFn (region φ α Q) (g : E)) := by
  obtain ⟨hle, hex⟩ := dualTrim_le_and_exists hφ hκ hα0 hα1 P Q (E := E)
  obtain ⟨t, s, hts⟩ := hex g
  exact ⟨⟨(t, s), hts⟩, by rintro _ ⟨ts, rfl⟩; exact hle (g, ts.1, ts.2)⟩

/-- `thm:boundary` (a), population form: `D = max_Θ Γ_{P,Q}`. -/
theorem isGreatest_dualTrim (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    IsGreatest (range (dualTrim φ α P Q (κ := κ))) (Dpop φ P Q α) := by
  obtain ⟨hle, hex⟩ := dualTrim_le_and_exists hφ hκ hα0 hα1 P Q (E := E)
  obtain ⟨g, hg⟩ := exists_dual_eq_Dpop hφ hκ hα0 hα1 P Q (E := E)
  obtain ⟨t, s, hts⟩ := hex g
  refine ⟨⟨(g, t, s), hts.trans hg⟩, ?_⟩
  rintro _ ⟨θ, rfl⟩
  exact (hle θ).trans (dual_le_Dpop hφ hκ hα0 hα1 P Q θ.1)

/-- The argmax of `Γ_{P,Q}`: `θ ∈ Θ₀` iff `θ.1 ∈ G*` and `t, s` are CVaR minimisers. -/
lemma dualTrim_eq_Dpop_iff (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (θ : Theta E κ) :
    dualTrim φ α P Q θ = Dpop φ P Q α ↔ (θ.1 ∈ Gstar φ α P Q ∧
      θ.2.1 ∈ argminSet φ α P κ (-(θ.1 : E)) ∧ θ.2.2 ∈ argminSet φ α Q κ (θ.1 : E)) := by
  have hκ0 := kappa_nonneg hκ P
  have hg1 : ‖(θ.1 : E)‖ ≤ 1 := mem_closedBall_zero_iff.1 θ.1.2
  have hg1' : ‖-(θ.1 : E)‖ ≤ 1 := by rw [norm_neg]; exact hg1
  have hLA := isLeast_cvObj hφ hκ hκ0 hα0 hα1 P hg1'
  have hLB := isLeast_cvObj hφ hκ hκ0 hα0 hα1 Q hg1
  have a1 := hLA.2 ⟨θ.2.1, rfl⟩
  have a2 := hLB.2 ⟨θ.2.2, rfl⟩
  simp only at a1 a2
  have a3 := dual_le_Dpop hφ hκ hα0 hα1 P Q θ.1
  have hargA : θ.2.1 ∈ argminSet φ α P κ (-(θ.1 : E)) ↔
      cvObj φ α P (-(θ.1 : E)) θ.2.1 = supportFn (region φ α P) (-(θ.1 : E)) := by
    rw [mem_argminSet_iff]
    constructor
    · intro h
      obtain ⟨t', ht'⟩ := hLA.1
      exact le_antisymm ((h t').trans (le_of_eq ht')) a1
    · intro h t'
      rw [h]; exact hLA.2 ⟨t', rfl⟩
  have hargB : θ.2.2 ∈ argminSet φ α Q κ (θ.1 : E) ↔
      cvObj φ α Q (θ.1 : E) θ.2.2 = supportFn (region φ α Q) (θ.1 : E) := by
    rw [mem_argminSet_iff]
    constructor
    · intro h
      obtain ⟨t', ht'⟩ := hLB.1
      exact le_antisymm ((h t').trans (le_of_eq ht')) a2
    · intro h t'
      rw [h]; exact hLB.2 ⟨t', rfl⟩
  rw [hargA, hargB, mem_Gstar_iff hφ hκ hα0 hα1 P Q, dualTrim_eq_cvObj]
  constructor
  · intro h
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    linarith

/-- Separated case: `G* = {(a − b)/‖a − b‖}` for any nearest pair `a ∈ A`, `b ∈ B`. -/
lemma Gstar_eq_singleton (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hD : 0 < Dpop φ P Q α) {a b : E}
    (ha : a ∈ region φ α P) (hb : b ∈ region φ α Q) (hab : ‖a - b‖ = Dpop φ P Q α) (g : Ball E) :
    g ∈ Gstar φ α P Q ↔ (g : E) = ‖a - b‖⁻¹ • (a - b) := by
  have hdpos : 0 < ‖a - b‖ := hab ▸ hD
  have key : ∀ g : Ball E, g ∈ Gstar φ α P Q → (g : E) = ‖a - b‖⁻¹ • (a - b) := by
    intro g hg
    rw [mem_Gstar_iff hφ hκ hα0 hα1 P Q] at hg
    have h1 := Wave30v.le_supportFn (isBounded_region P hκ) (-(g : E)) ha
    have h2 := Wave30v.le_supportFn (isBounded_region Q hκ) (g : E) hb
    rw [inner_neg_left] at h1
    have hg1 : ‖(g : E)‖ ≤ 1 := mem_closedBall_zero_iff.1 g.2
    have hcs : ⟪(g : E), a - b⟫ ≤ ‖a - b‖ :=
      (real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (a - b)])
    have hin : ⟪(g : E), a - b⟫ = ‖a - b‖ := by
      rw [inner_sub_right] at hcs ⊢; linarith
    set u := ‖a - b‖⁻¹ • (a - b) with hu
    have hun : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ hdpos.ne'
    have hgu : ⟪(g : E), u⟫ = 1 := by
      rw [hu, real_inner_smul_right, hin]; exact inv_mul_cancel₀ hdpos.ne'
    have hsq : ‖(g : E) - u‖ ^ 2 ≤ 0 := by
      rw [norm_sub_sq_real, hgu, hun]
      nlinarith [norm_nonneg (g : E)]
    have : ‖(g : E) - u‖ = 0 := by nlinarith [norm_nonneg ((g : E) - u)]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  refine ⟨key g, fun h => ?_⟩
  obtain ⟨g0, hg0⟩ := Gstar_nonempty hφ hκ hα0 hα1 P Q (E := E)
  have : g = g0 := Subtype.ext (h.trans (key g0 hg0).symm)
  rw [this]; exact hg0

/-- Contact case: `G* = (B − A)° ∩ 𝔹`. -/
lemma Gstar_iff_polar (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hAB : (region φ α P ∩ region φ α Q).Nonempty) (g : Ball E) :
    g ∈ Gstar φ α P Q ↔ (g : E) ∈ polarSet (region φ α Q - region φ α P) := by
  obtain ⟨z, hzA, hzB⟩ := hAB
  have hD : Dpop φ P Q α = 0 := by
    refine le_antisymm ?_ ?_
    · have := Wave30v.setDist_le' hzA hzB; rw [sub_self, norm_zero] at this; exact this
    · exact Wave30v.le_setDist ⟨z, hzA⟩ ⟨z, hzB⟩ fun _ _ _ _ => norm_nonneg _
  rw [mem_Gstar_iff hφ hκ hα0 hα1 P Q, ← dual_nonneg_iff (region_nonempty P hα0 hα1)
    (region_nonempty Q hα0 hα1) (isBounded_region P hκ) (isBounded_region Q hκ), hD]
  have := dual_le_Dpop hφ hκ hα0 hα1 P Q g
  rw [hD] at this
  constructor
  · intro h; exact h.ge
  · intro h; exact le_antisymm this h

end Fin

theorem boundary_dual : Claims.boundary_dual := by
  intro 𝒳 E _ _ _ _ φ κ α hφ hκ hα0 hα1
  refine ⟨fun P Q _ _ => isGreatest_dualTrim hφ hκ hα0 hα1 P Q, fun n m x y hn hm => ?_⟩
  have := isProbabilityMeasure_empirical x hn
  have := isProbabilityMeasure_empirical y hm
  exact isGreatest_dualTrim hφ hκ hα0 hα1 (empirical x) (empirical y)

end Main

end StatFormal.Wave30z
