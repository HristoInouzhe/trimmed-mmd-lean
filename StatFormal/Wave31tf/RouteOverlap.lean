import StatFormal.Wave31tf.Statements

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Route: wave 31tf, strict overlap (G6, untrusted)

Notation: `μ = P + Q`, `p = dP/dμ`, `q = dQ/dμ` (`dens`). Since `p + q = (P+Q).rnDeriv μ = 1` `μ`-a.e. (`rnDeriv_add`, `rnDeriv_self`), the guard `p + q > 0`
of `StrictOverlap` is a.e. true and `StrictOverlap P Q η` is equivalent to `η ≤ p ≤ 1 − η` `μ`-a.e. (`overlap_iff`); then `η ≤ q ≤ 1 − η` too.
* For measurable `B`: `P(B) = ∫_B p dμ` (`setIntegral_toReal_rnDeriv`), so `η μ(B) ≤ P(B) ≤ (1−η) μ(B)` and, as `μ = P + Q`,
  `η μ(B) ≤ Q(B) ≤ (1−η) μ(B)` (`set_bounds`).
* (i) `P(A) − Q(A) = 2P(A) − μ(A)`; from `P(A) ≤ (1−η)μ(A)` this is `≤ (1−2η) μ(A)`, from `P(Aᶜ) ≥ η μ(Aᶜ)` and `P(A) = 1 − P(Aᶜ)` it is
  `≤ (1−2η) μ(Aᶜ)`, and `min(μ(A), μ(Aᶜ)) ≤ 1` (`μ(A) + μ(Aᶜ) = 2`); the same for `Q(A) − P(A)` (`tv_le`).
* (ii) `P ≪ Q` and `Q ≪ P` (`Q(B) = 0 ⇒ μ(B) = 0 ⇒ P(B) = 0`); the chain rule `P.rnDeriv Q * Q.rnDeriv μ = P.rnDeriv μ` (`rnDeriv_mul_rnDeriv`) gives
  `r q = p` a.e. for `r = dP/dQ`, hence `r = p/q ∈ [η/(1−η), (1−η)/η]` (`η ≤ p, q ≤ 1−η`). A convex `f` on `[0,∞)` is continuous on `(0,∞)`
  (`ConvexOn.continuousOn`), hence bounded and measurable on `[a,b]`, `a = η/(1−η) ≤ 1 ≤ b = (1−η)/η`, so `f(r)` is `Q`-integrable (bounded, a.e. equal to
  the continuous `f ∘ clamp ∘ r`), and `f(r) ≤ max{f(a), f(b)}` (`ConvexOn.le_max_of_mem_Icc`), so `∫ f(r) dQ ≤ max{f(a), f(b)}`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave31tf

section Overlap

variable {𝒳 : Type} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

lemma measurable_dens (P μ : Measure 𝒳) : Measurable (dens P μ) :=
  (Measure.measurable_rnDeriv P μ).ennreal_toReal

lemma dens_nonneg (P μ : Measure 𝒳) (x : 𝒳) : 0 ≤ dens P μ x := ENNReal.toReal_nonneg

/-- `dP/d(P+Q) + dQ/d(P+Q) = 1` `(P+Q)`-a.e.: the guard `0 < p + q` of `StrictOverlap` is a.e. true. -/
lemma dens_add_eq_one : ∀ᵐ x ∂(P + Q), dens P (P + Q) x + dens Q (P + Q) x = 1 := by
  have h1 := Measure.rnDeriv_add P Q (P + Q)
  have h2 := Measure.rnDeriv_self (P + Q)
  have hP := Measure.rnDeriv_ne_top P (P + Q)
  have hQ := Measure.rnDeriv_ne_top Q (P + Q)
  filter_upwards [h1, h2, hP, hQ] with x e1 e2 hp hq
  have : (P + Q).rnDeriv (P + Q) x = P.rnDeriv (P + Q) x + Q.rnDeriv (P + Q) x := by
    rw [← Pi.add_apply, ← e1]
  unfold dens
  rw [← ENNReal.toReal_add hp hq, ← this, e2]
  simp

/-- Strict overlap is exactly `η ≤ dP/d(P+Q) ≤ 1 − η` `(P+Q)`-a.e. -/
lemma overlap_iff (η : ℝ) :
    StrictOverlap P Q η ↔ ∀ᵐ x ∂(P + Q), η ≤ dens P (P + Q) x ∧ dens P (P + Q) x ≤ 1 - η := by
  have hsum := dens_add_eq_one P Q
  unfold StrictOverlap
  constructor
  · intro h
    filter_upwards [h, hsum] with x hx hs
    rw [hs] at hx
    simpa using hx (by norm_num)
  · intro h
    filter_upwards [h, hsum] with x hx hs hpos
    rw [hs]
    simpa using hx

/-- Symmetry of strict overlap. -/
lemma overlap_symm {η : ℝ} (h : StrictOverlap P Q η) : StrictOverlap Q P η := by
  rw [overlap_iff] at h ⊢
  rw [add_comm Q P]
  filter_upwards [h, dens_add_eq_one P Q] with x hx hs
  have hq : dens Q (P + Q) x = 1 - dens P (P + Q) x := by linarith
  rw [hq]
  constructor <;> linarith [hx.1, hx.2]


lemma abscont_left : P ≪ P + Q := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)

lemma abscont_right : Q ≪ P + Q := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)

/-- `P(B) = ∫_B p dμ` -/
lemma real_eq_setIntegral (B : Set 𝒳) : P.real B = ∫ x in B, dens P (P + Q) x ∂(P + Q) :=
  (Measure.setIntegral_toReal_rnDeriv (abscont_left P Q) B).symm

/-- From `η ≤ p ≤ 1 − η` a.e.: `η μ(B) ≤ P(B) ≤ (1−η) μ(B)`. -/
lemma set_bounds {η : ℝ}
    (hb : ∀ᵐ x ∂(P + Q), η ≤ dens P (P + Q) x ∧ dens P (P + Q) x ≤ 1 - η) (B : Set 𝒳) :
    η * (P + Q).real B ≤ P.real B ∧ P.real B ≤ (1 - η) * (P + Q).real B := by
  have hint : IntegrableOn (dens P (P + Q)) B (P + Q) :=
    Measure.integrableOn_toReal_rnDeriv (measure_ne_top P B)
  have hc : ∀ c : ℝ, IntegrableOn (fun _ : 𝒳 => c) B (P + Q) := fun c => integrableOn_const (measure_ne_top _ _)
  rw [real_eq_setIntegral P Q B]
  constructor
  · calc η * (P + Q).real B = ∫ _ in B, η ∂(P + Q) := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in B, dens P (P + Q) x ∂(P + Q) := setIntegral_mono_ae (hc η) hint (hb.mono fun x hx => hx.1)
  · calc ∫ x in B, dens P (P + Q) x ∂(P + Q) ≤ ∫ _ in B, (1 - η) ∂(P + Q) :=
          setIntegral_mono_ae hint (hc (1 - η)) (hb.mono fun x hx => hx.2)
      _ = (1 - η) * (P + Q).real B := by rw [setIntegral_const, smul_eq_mul, mul_comm]

lemma real_add (B : Set 𝒳) : (P + Q).real B = P.real B + Q.real B := measureReal_add_apply

/-- (i) -/
lemma tv_le {η : ℝ} (hb : ∀ᵐ x ∂(P + Q), η ≤ dens P (P + Q) x ∧ dens P (P + Q) x ≤ 1 - η) :
    StatFormal.Distances.tvDist P Q ≤ 1 - 2 * η := by
  refine StatFormal.Distances.tvDist_le_of_forall fun A hA => ?_
  have h1 := set_bounds P Q hb A
  have h2 := set_bounds P Q hb Aᶜ
  have hμc : (P + Q).real Aᶜ = 2 - (P + Q).real A := by
    rw [measureReal_compl hA, real_add, probReal_univ, probReal_univ]; norm_num
  have hPc : P.real Aᶜ = 1 - P.real A := probReal_compl_eq_one_sub hA
  have hQ : Q.real A = (P + Q).real A - P.real A := by rw [real_add]; ring
  rw [hμc, hPc] at h2
  rw [abs_le, hQ]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]


/-- `P ≪ Q` under overlap. -/
lemma abscont_PQ {η : ℝ} (hη : 0 < η)
    (hb : ∀ᵐ x ∂(P + Q), η ≤ dens P (P + Q) x ∧ dens P (P + Q) x ≤ 1 - η) : P ≪ Q := by
  intro s hs
  set t := toMeasurable Q s with ht
  have htm : MeasurableSet t := measurableSet_toMeasurable Q s
  have hQt : Q t = 0 := by rw [ht, measure_toMeasurable]; exact hs
  have h1 := (set_bounds P Q hb t).2
  have hQ0 : Q.real t = 0 := by simp [Measure.real, hQt]
  have hμ := real_add P Q t
  have hP0 : P.real t = 0 := by
    have hpn : 0 ≤ P.real t := measureReal_nonneg
    nlinarith
  have hPt : P t = 0 := by
    have := (measureReal_eq_zero_iff (measure_ne_top P t)).1 hP0
    exact this
  exact measure_mono_null (subset_toMeasurable Q s) hPt

/-- `dP/dQ ∈ [η/(1−η), (1−η)/η]` `Q`-a.e. -/
lemma ratio_bounds {η : ℝ} (hη : 0 < η)
    (hb : ∀ᵐ x ∂(P + Q), η ≤ dens P (P + Q) x ∧ dens P (P + Q) x ≤ 1 - η) :
    ∀ᵐ x ∂Q, η / (1 - η) ≤ dens P Q x ∧ dens P Q x ≤ (1 - η) / η := by
  have hPQ : P ≪ Q := abscont_PQ P Q hη hb
  have hchain := Measure.rnDeriv_mul_rnDeriv (κ := P + Q) hPQ
  have hsum := dens_add_eq_one P Q
  have key : ∀ᵐ x ∂(P + Q), η / (1 - η) ≤ dens P Q x ∧ dens P Q x ≤ (1 - η) / η := by
    filter_upwards [hchain, hb, hsum] with x hc hbx hs
    have hmul : dens P Q x * dens Q (P + Q) x = dens P (P + Q) x := by
      have := congrArg ENNReal.toReal hc
      simpa [dens, ENNReal.toReal_mul] using this
    set p := dens P (P + Q) x with hp
    set q := dens Q (P + Q) x with hq
    set r := dens P Q x with hr
    have hqe : q = 1 - p := by linarith
    have hq1 : η ≤ q := by rw [hqe]; linarith [hbx.2]
    have hq2 : q ≤ 1 - η := by rw [hqe]; linarith [hbx.1]
    have hηle : η < 1 := by linarith [hbx.1, hbx.2, hq1]
    have h1η : 0 < 1 - η := by linarith
    have hqpos : 0 < q := lt_of_lt_of_le hη hq1
    constructor
    · rw [div_le_iff₀ h1η]
      -- η ≤ r (1-η), from r q = p, p ≥ η, q ≤ 1 - η
      have hr0 : 0 ≤ r := dens_nonneg _ _ _
      nlinarith [hbx.1, hq2, hr0]
    · rw [le_div_iff₀ hη]
      have hr0 : 0 ≤ r := dens_nonneg _ _ _
      nlinarith [hbx.2, hq1, hr0]
  exact key.filter_mono (abscont_right P Q).ae_le


/-- (ii) for the ordered pair: `FDivBound P Q η` from `η ≤ dP/d(P+Q) ≤ 1 − η`. -/
lemma fdiv_bound {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hb : ∀ᵐ x ∂(P + Q), η ≤ dens P (P + Q) x ∧ dens P (P + Q) x ≤ 1 - η) : FDivBound P Q η := by
  refine ⟨abscont_PQ P Q hη hb, ratio_bounds P Q hη hb, fun f hf hf1 => ?_⟩
  have hrb := ratio_bounds P Q hη hb
  have h1η : 0 < 1 - η := by linarith
  set a := η / (1 - η) with ha
  set b := (1 - η) / η with hbdef
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one h1η]; linarith
  have hb1 : 1 ≤ b := by rw [hbdef, one_le_div hη]; linarith
  have hab : a ≤ b := ha1.trans hb1
  have hfo : ConvexOn ℝ (Ioi (0 : ℝ)) f := hf.subset Ioi_subset_Ici_self (convex_Ioi 0)
  have hcont : ContinuousOn f (Icc a b) :=
    (hfo.continuousOn isOpen_Ioi).mono (fun y hy => lt_of_lt_of_le ha0 hy.1)
  set g : ℝ → ℝ := fun y => f (max a (min y b)) with hg
  have hgc : Continuous g :=
    hcont.comp_continuous (continuous_const.max (continuous_id.min continuous_const))
      (fun y => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩)
  have hae : ∀ᵐ x ∂Q, f (dens P Q x) = g (dens P Q x) := hrb.mono fun x hx => by
    simp only [hg]
    rw [min_eq_left hx.2, max_eq_right hx.1]
  have hmeas : AEStronglyMeasurable (fun x => f (dens P Q x)) Q :=
    ((hgc.measurable.comp (measurable_dens P Q)).aestronglyMeasurable).congr (hae.mono fun x hx => hx.symm)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hint : Integrable (fun x => f (dens P Q x)) Q :=
    Integrable.of_bound hmeas M (hrb.mono fun x hx => hM _ ⟨hx.1, hx.2⟩)
  refine ⟨hint, ?_⟩
  unfold fDiv
  calc ∫ x, f (dens P Q x) ∂Q ≤ ∫ _, max (f a) (f b) ∂Q :=
        integral_mono_ae hint (integrable_const _)
          (hrb.mono fun x hx => hf.le_max_of_mem_Icc ha0.le hb0.le hx)
    _ = max (f a) (f b) := by simp

end Overlap

theorem strict_overlap : Claims.strict_overlap := by
  intro 𝒳 _ P Q _ _ η hη hη2 h
  have hb := (overlap_iff P Q η).1 h
  have hb' := (overlap_iff Q P η).1 (overlap_symm P Q h)
  exact ⟨tv_le P Q hb, fdiv_bound P Q hη hη2 hb, fdiv_bound Q P hη hη2 hb'⟩

end StatFormal.Wave31tf
