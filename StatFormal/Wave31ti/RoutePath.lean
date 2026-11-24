import StatFormal.Wave31ti.Statements
import StatFormal.Archive.Wave18b.RouteConsistency
import StatFormal.Archive.TrimmedMMD.Concentration.Proofs

set_option linter.style.longLine false

/-!
# Route: wave 31ti, `lem:pathconvex` and `lem:marginexists` (untrusted)

Convexity: for weights `p, q ≥ 0`, `p + q = 1`, levels `α₀, α₁ ∈ [0,1)` and `α = pα₀ + qα₁`, put `c = p(1−α₀)/(1−α)`,
`d = q(1−α₁)/(1−α)`; then `c + d = 1` and `c/(1−α₀) + d/(1−α₁) = 1/(1−α)`, so `c•a₀ + d•a₁ ∈ 𝒞_α(P)` for `aᵢ ∈ 𝒞_{αᵢ}(P)` (mix the
densities), likewise for `Q`, and the triangle inequality gives `D_α ≤ cD_{α₀} + dD_{α₁}`, i.e. `u(α) ≤ p u(α₀) + q u(α₁)`.
Everything else is about a convex `u ≥ 0` on `[0,1)` with `u(α⋆) = 0` (and `u > 0` below `α⋆` for (i)).
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave31ti

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.ZeroSet StatFormal.Wave30tu

/-! ### Abstract facts about a convex function vanishing at `a` -/

section Abstract

variable {u : ℝ → ℝ} {a : ℝ}

lemma conv_mid (hu : ConvexOn ℝ (Ico 0 1) u) {x y : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) (hy : y ∈ Ico (0 : ℝ) 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : u ((1 - t) * x + t * y) ≤ (1 - t) * u x + t * u y := by
  have := hu.2 hx hy (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
  simpa [smul_eq_mul] using this

/-- `u(y)(a − x) ≤ (a − y)u(x)` for `0 ≤ x < y ≤ a < 1` when `u(a) = 0`. -/
lemma key_ineq (hu : ConvexOn ℝ (Ico 0 1) u) (ha1 : a < 1) (hua : u a = 0) {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x < y)
    (hya : y ≤ a) : u y * (a - x) ≤ (a - y) * u x := by
  have hax : 0 < a - x := by linarith
  set t := (y - x) / (a - x) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hax.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hax]; linarith
  have hyeq : (1 - t) * x + t * a = y := by
    rw [ht]; field_simp; ring
  have h := conv_mid hu ⟨hx0, by linarith⟩ ⟨by linarith, ha1⟩ ht0 ht1
  rw [hyeq, hua, mul_zero, add_zero] at h
  have h1t : (1 - t) * (a - x) = a - y := by
    rw [ht]; field_simp; ring
  calc u y * (a - x) ≤ (1 - t) * u x * (a - x) := mul_le_mul_of_nonneg_right h hax.le
    _ = (a - y) * u x := by rw [← h1t]; ring

lemma strictAnti_of (hu : ConvexOn ℝ (Ico 0 1) u) (ha1 : a < 1) (hua : u a = 0)
    (hpos : ∀ α ∈ Ico 0 a, 0 < u α) : StrictAntiOn u (Icc 0 a) := by
  intro x hx y hy hxy
  have hxa : x < a := lt_of_lt_of_le hxy hy.2
  have hk := key_ineq hu ha1 hua hx.1 hxy hy.2
  have hux := hpos x ⟨hx.1, hxa⟩
  have hax : 0 < a - x := by linarith
  -- `u y (a − x) ≤ (a − y) u x < (a − x) u x`
  have : u y * (a - x) < u x * (a - x) := by
    calc u y * (a - x) ≤ (a - y) * u x := hk
      _ < (a - x) * u x := mul_lt_mul_of_pos_right (by linarith) hux
      _ = u x * (a - x) := by ring
  exact lt_of_mul_lt_mul_right this hax.le

lemma secant_of (hu : ConvexOn ℝ (Ico 0 1) u) (ha1 : a < 1) (hua : u a = 0)
    (hpos : ∀ α ∈ Ico 0 a, 0 < u α) {α₁ α₂ : ℝ} (h0 : 0 ≤ α₁) (h12 : α₁ < α₂) (h2a : α₂ < a) :
    α₂ + (α₂ - α₁) * u α₂ / (u α₁ - u α₂) ≤ a := by
  have hsa := strictAnti_of hu ha1 hua hpos
  have hd : u α₂ < u α₁ := hsa ⟨h0, by linarith⟩ ⟨by linarith, h2a.le⟩ h12
  have hk := key_ineq hu ha1 hua h0 h12 h2a.le
  have hdpos : 0 < u α₁ - u α₂ := by linarith
  have : (α₂ - α₁) * u α₂ / (u α₁ - u α₂) ≤ a - α₂ := by
    rw [div_le_iff₀ hdpos]; nlinarith
  linarith

/-- `r(e) = u(a − e)/e` is nondecreasing on `(0,a]`. -/
lemma ratio_mono (hu : ConvexOn ℝ (Ico 0 1) u) (ha1 : a < 1) (hua : u a = 0) :
    MonotoneOn (fun e => u (a - e) / e) (Ioc 0 a) := by
  intro e₁ he₁ e₂ he₂ h12
  rcases h12.lt_or_eq with h | h
  · have hk := key_ineq hu ha1 hua (x := a - e₂) (y := a - e₁) (by linarith [he₂.2]) (by linarith) (by linarith [he₁.1])
    simp only
    rw [div_le_div_iff₀ he₁.1 he₂.1]
    have e1 : a - (a - e₂) = e₂ := by ring
    have e2 : a - (a - e₁) = e₁ := by ring
    rw [e1, e2] at hk
    linarith
  · simp [h]

end Abstract

/-! ### The regions -/

section Regions

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma setDist_nonneg0 (A B : Set H) : 0 ≤ setDist A B :=
  Real.sInf_nonneg (by rintro _ ⟨a, -, b, -, rfl⟩; exact norm_nonneg _)

lemma Dpop_nonneg0 (φ : 𝒳 → H) (P Q : Measure 𝒳) (α : ℝ) : 0 ≤ Dpop φ P Q α := setDist_nonneg0 _ _

lemma setDist_le_norm0 {A B : Set H} {a b : H} (ha : a ∈ A) (hb : b ∈ B) : setDist A B ≤ ‖a - b‖ :=
  csInf_le ⟨0, by rintro _ ⟨a, -, b, -, rfl⟩; exact norm_nonneg _⟩ ⟨a, ha, b, hb, rfl⟩

/-- A mixture of two densities at two levels. -/
lemma region_mix (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ : ℝ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) {α₀ α₁ α c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c + d = 1)
    (hcap : c / (1 - α₀) + d / (1 - α₁) ≤ 1 / (1 - α)) {a₀ a₁ : H} (ha₀ : a₀ ∈ region φ α₀ P)
    (ha₁ : a₁ ∈ region φ α₁ P) : c • a₀ + d • a₁ ∈ region φ α P := by
  obtain ⟨g₀, hg₀, hb₀, hi₀, rfl⟩ := ha₀
  obtain ⟨g₁, hg₁, hb₁, hi₁, rfl⟩ := ha₁
  have hI₀ := integrable_smul_of_bound P hφ hκ hg₀ hb₀
  have hI₁ := integrable_smul_of_bound P hφ hκ hg₁ hb₁
  have hgI : ∀ {g : 𝒳 → ℝ} {β : ℝ}, Measurable g → (∀ x, 0 ≤ g x ∧ g x ≤ β) → Integrable g P :=
    fun {g} {β} hg hb => Integrable.of_bound hg.aestronglyMeasurable β
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]; exact (hb x).2)
  refine ⟨fun x => c * g₀ x + d * g₁ x, (hg₀.const_mul c).add (hg₁.const_mul d), fun x => ?_, ?_, ?_⟩
  · have h0 := hb₀ x; have h1 := hb₁ x
    constructor
    · exact add_nonneg (mul_nonneg hc h0.1) (mul_nonneg hd h1.1)
    · calc c * g₀ x + d * g₁ x ≤ c * (1 / (1 - α₀)) + d * (1 / (1 - α₁)) := by
            gcongr
            · exact h0.2
            · exact h1.2
        _ = c / (1 - α₀) + d / (1 - α₁) := by ring
        _ ≤ 1 / (1 - α) := hcap
  · rw [integral_add ((hgI hg₀ hb₀).const_mul c) ((hgI hg₁ hb₁).const_mul d), integral_const_mul,
      integral_const_mul, hi₀, hi₁, mul_one, mul_one, hcd]
  · have e : ∀ x, (c * g₀ x + d * g₁ x) • φ x = c • (g₀ x • φ x) + d • (g₁ x • φ x) :=
      fun x => by rw [add_smul, smul_smul, smul_smul]
    simp_rw [e]
    rw [integral_add (f := fun x => c • (g₀ x • φ x)) (g := fun x => d • (g₁ x • φ x))
      (hI₀.smul c) (hI₁.smul d), integral_smul, integral_smul]

/-- `inf` of a convex combination of norms over two pairs of nonempty sets. -/
lemma setDist_le_comb {A B A₀ B₀ A₁ B₁ : Set H} (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (hA₁ : A₁.Nonempty)
    (hB₁ : B₁.Nonempty) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hmix : ∀ a₀ ∈ A₀, ∀ b₀ ∈ B₀, ∀ a₁ ∈ A₁, ∀ b₁ ∈ B₁, setDist A B ≤ c * ‖a₀ - b₀‖ + d * ‖a₁ - b₁‖) :
    setDist A B ≤ c * setDist A₀ B₀ + d * setDist A₁ B₁ := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set η := ε / (c + d + 1) with hη
  have hcd1 : 0 < c + d + 1 := by linarith
  have hη0 : 0 < η := div_pos hε hcd1
  have hne : ∀ {A' B' : Set H}, A'.Nonempty → B'.Nonempty → {r | ∃ a ∈ A', ∃ b ∈ B', r = ‖a - b‖}.Nonempty :=
    fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨_, a, ha, b, hb, rfl⟩
  obtain ⟨r₀, ⟨a₀, ha₀, b₀, hb₀, rfl⟩, hr₀⟩ := Real.lt_sInf_add_pos (hne hA₀ hB₀) hη0
  obtain ⟨r₁, ⟨a₁, ha₁, b₁, hb₁, rfl⟩, hr₁⟩ := Real.lt_sInf_add_pos (hne hA₁ hB₁) hη0
  have h := hmix a₀ ha₀ b₀ hb₀ a₁ ha₁ b₁ hb₁
  have hS0 : ‖a₀ - b₀‖ ≤ setDist A₀ B₀ + η := hr₀.le
  have hS1 : ‖a₁ - b₁‖ ≤ setDist A₁ B₁ + η := hr₁.le
  have hcdη : (c + d) * η < ε := by
    rw [hη, ← mul_div_assoc, div_lt_iff₀ hcd1]; nlinarith
  calc setDist A B ≤ c * ‖a₀ - b₀‖ + d * ‖a₁ - b₁‖ := h
    _ ≤ c * (setDist A₀ B₀ + η) + d * (setDist A₁ B₁ + η) := by gcongr
    _ = c * setDist A₀ B₀ + d * setDist A₁ B₁ + (c + d) * η := by ring
    _ < c * setDist A₀ B₀ + d * setDist A₁ B₁ + ε := by linarith

/-- Convexity of `u(α) = (1−α)D_α(P,Q)` on `[0,1)`. -/
lemma uPath_convex (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) : ConvexOn ℝ (Ico 0 1) (uPath φ P Q) := by
  refine ⟨convex_Ico 0 1, ?_⟩
  intro α₀ h₀ α₁ h₁ p q hp hq hpq
  simp only [smul_eq_mul]
  set α := p * α₀ + q * α₁ with hα
  have hβ0 : 0 < 1 - α₀ := by linarith [h₀.2]
  have hβ1 : 0 < 1 - α₁ := by linarith [h₁.2]
  have h1α : 1 - α = p * (1 - α₀) + q * (1 - α₁) := by rw [hα]; linear_combination (-1 : ℝ) * hpq
  have hβ : 0 < 1 - α := by
    rw [h1α]
    rcases eq_or_lt_of_le hp with hp0 | hp0
    · have : q = 1 := by linarith
      subst this; rw [← hp0]; simpa using hβ1
    · exact add_pos_of_pos_of_nonneg (mul_pos hp0 hβ0) (mul_nonneg hq hβ1.le)
  set c := p * (1 - α₀) / (1 - α) with hcdef
  set d := q * (1 - α₁) / (1 - α) with hddef
  have hc : 0 ≤ c := div_nonneg (mul_nonneg hp hβ0.le) hβ.le
  have hd : 0 ≤ d := div_nonneg (mul_nonneg hq hβ1.le) hβ.le
  have hcd : c + d = 1 := by
    rw [hcdef, hddef, ← add_div, ← h1α, div_self hβ.ne']
  have hcap : c / (1 - α₀) + d / (1 - α₁) ≤ 1 / (1 - α) := by
    have ec : c / (1 - α₀) = p / (1 - α) := by rw [hcdef]; field_simp
    have ed : d / (1 - α₁) = q / (1 - α) := by rw [hddef]; field_simp
    rw [ec, ed, ← add_div, hpq]
  have hD : Dpop φ P Q α ≤ c * Dpop φ P Q α₀ + d * Dpop φ P Q α₁ := by
    refine setDist_le_comb (region_nonempty P h₀.1 h₀.2) (region_nonempty Q h₀.1 h₀.2)
      (region_nonempty P h₁.1 h₁.2) (region_nonempty Q h₁.1 h₁.2) hc hd ?_
    intro a₀ ha₀ b₀ hb₀ a₁ ha₁ b₁ hb₁
    have hA := region_mix P hφ hκ hc hd hcd hcap ha₀ ha₁
    have hB := region_mix Q hφ hκ hc hd hcd hcap hb₀ hb₁
    refine (setDist_le_norm0 hA hB).trans ?_
    have e : c • a₀ + d • a₁ - (c • b₀ + d • b₁) = c • (a₀ - b₀) + d • (a₁ - b₁) := by
      simp only [smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hc, Real.norm_of_nonneg hd]
  have e1 : (1 - α) * c = p * (1 - α₀) := by rw [hcdef]; field_simp
  have e2 : (1 - α) * d = q * (1 - α₁) := by rw [hddef]; field_simp
  calc uPath φ P Q α = (1 - α) * Dpop φ P Q α := rfl
    _ ≤ (1 - α) * (c * Dpop φ P Q α₀ + d * Dpop φ P Q α₁) := mul_le_mul_of_nonneg_left hD hβ.le
    _ = p * ((1 - α₀) * Dpop φ P Q α₀) + q * ((1 - α₁) * Dpop φ P Q α₁) := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, e1, e2]; ring
    _ = p * uPath φ P Q α₀ + q * uPath φ P Q α₁ := rfl

lemma uPath_anti (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) :
    AntitoneOn (uPath φ P Q) (Ico 0 1) := by
  intro α hα α' hα' hle
  have hD := StatFormal.Wave18b.Dpop_anti P Q φ hα.1 hle hα'.2
  exact mul_le_mul (by linarith) hD (Dpop_nonneg0 _ _ _ _) (by linarith [hα.2])

lemma uPath_nonneg (P Q : Measure 𝒳) (φ : 𝒳 → H) {α : ℝ} (hα : α < 1) : 0 ≤ uPath φ P Q α :=
  mul_nonneg (by linarith) (Dpop_nonneg0 _ _ _ _)

end Regions

/-! ### The claims of `lem:pathconvex` -/

theorem pathconvex : Claims.pathconvex := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ hφ hκ
  exact ⟨uPath_convex P Q hφ hκ, uPath_anti P Q φ⟩

theorem pathconvex_emp : Claims.pathconvex_emp := by
  intro 𝒳 H _ _ _ _ _ φ κ n m hφ hκ hn hm x y
  haveI := isProbabilityMeasure_empirical (by omega : n ≠ 0) x
  haveI := isProbabilityMeasure_empirical (by omega : m ≠ 0) y
  exact ⟨uPath_convex (empirical x) (empirical y) hφ hκ, uPath_anti (empirical x) (empirical y) φ⟩

section Pair

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ : ℝ}

lemma uPath_tv (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (h1 : StatFormal.Distances.tvDist P Q < 1) :
    uPath φ P Q (StatFormal.Distances.tvDist P Q) = 0 := by
  have := StatFormal.TrimmedMMD.ZeroSet.zero_of_tv_le 𝒳 H P Q φ κ _ hφ hκ (StatFormal.Distances.tvDist_nonneg P Q) h1
    le_rfl
  simp [uPath, this]

lemma uPath_pos [TopologicalSpace.SeparableSpace H] (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hch : Characteristic φ) {α : ℝ} (hα : α ∈ Ico 0 (StatFormal.Distances.tvDist P Q))
    (h1 : StatFormal.Distances.tvDist P Q < 1) : 0 < uPath φ P Q α := by
  have hz := StatFormal.TrimmedMMD.ZeroSet.zeroeq 𝒳 H P Q φ κ α hφ hκ hch hα.1 (hα.2.trans h1)
  have hne : Dpop φ P Q α ≠ 0 := fun h => absurd (hz.1 h) (not_le.2 hα.2)
  exact mul_pos (by linarith [hα.2]) (lt_of_le_of_ne (Dpop_nonneg0 _ _ _ _) (Ne.symm hne))

end Pair

theorem pathconvex_i : Claims.pathconvex_i := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ hφ hκ hch h0 h1
  have hu := uPath_convex P Q hφ hκ
  have hua := uPath_tv hφ hκ h1
  have hpos : ∀ α ∈ Ico 0 (StatFormal.Distances.tvDist P Q), 0 < uPath φ P Q α :=
    fun α hα => uPath_pos hφ hκ hch hα h1
  exact ⟨strictAnti_of hu h1 hua hpos, fun α₁ α₂ h0' h12 h2 => secant_of hu h1 hua hpos h0' h12 h2⟩

/-- The part of (ii) about the limit `s`, for an abstract path. -/
lemma limit_facts {u D : ℝ → ℝ} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hu : ConvexOn ℝ (Ico 0 1) u) (hua : u a = 0)
    (huD : ∀ α, u α = (1 - α) * D α) (hD0 : ∀ α, 0 ≤ D α) :
    (∃ s : ℝ, Tendsto (fun e => u (a - e) / e) (𝓝[>] 0) (𝓝 s)) ∧
    ∀ s : ℝ, Tendsto (fun e => u (a - e) / e) (𝓝[>] 0) (𝓝 s) →
      0 ≤ s ∧ (∀ e ∈ Ioc 0 a, s ≤ u (a - e) / e) ∧
      ((∃ c₀ : ℝ, 0 < c₀ ∧ ∀ e ∈ Icc 0 a, c₀ * e ^ (1 : ℝ) ≤ D (a - e)) → 0 < s) ∧
      (0 < s → ∀ e ∈ Icc 0 a, s * e ^ (1 : ℝ) ≤ D (a - e)) := by
  have hmono := ratio_mono hu ha1 hua
  have hr0 : ∀ e ∈ Ioc 0 a, 0 ≤ u (a - e) / e := fun e he =>
    div_nonneg (by rw [huD]; exact mul_nonneg (by linarith [he.1]) (hD0 _)) he.1.le
  refine ⟨⟨_, (hmono.mono Ioo_subset_Ioc_self).tendsto_nhdsWithin_Ioo_right ⟨a / 2, by linarith, by linarith⟩
    ⟨0, by rintro _ ⟨e, he, rfl⟩; exact hr0 e ⟨he.1, he.2.le⟩⟩⟩, fun s hs => ?_⟩
  have hev : ∀ e ∈ Ioc 0 a, ∀ᶠ e' in 𝓝[>] (0 : ℝ), u (a - e') / e' ≤ u (a - e) / e := fun e he => by
    filter_upwards [Ioo_mem_nhdsGT he.1] with e' he'
    exact hmono ⟨he'.1, he'.2.le.trans he.2⟩ he he'.2.le
  have hle : ∀ e ∈ Ioc 0 a, s ≤ u (a - e) / e := fun e he => le_of_tendsto hs (hev e he)
  have hs0 : 0 ≤ s := ge_of_tendsto hs (by
    filter_upwards [Ioo_mem_nhdsGT ha0] with e he
    exact hr0 e ⟨he.1, he.2.le⟩)
  refine ⟨hs0, hle, ?_, ?_⟩
  · rintro ⟨c₀, hc₀, hb⟩
    have hge : ∀ e ∈ Ioo 0 a, (1 - a) * c₀ ≤ u (a - e) / e := fun e he => by
      rw [le_div_iff₀ he.1, huD]
      have h := hb e ⟨he.1.le, he.2.le⟩
      rw [Real.rpow_one] at h
      have h1 : (1 - a) * (c₀ * e) ≤ (1 - a) * D (a - e) := mul_le_mul_of_nonneg_left h (by linarith)
      have h2 : (1 - a) * D (a - e) ≤ (1 - (a - e)) * D (a - e) := mul_le_mul_of_nonneg_right (by linarith [he.1]) (hD0 _)
      nlinarith
    have : (1 - a) * c₀ ≤ s := ge_of_tendsto hs (by
      filter_upwards [Ioo_mem_nhdsGT ha0] with e he
      exact hge e he)
    have : 0 < (1 - a) * c₀ := mul_pos (by linarith) hc₀
    linarith
  · intro hspos e he
    rw [Real.rpow_one]
    rcases he.1.eq_or_lt with he0 | he0
    · rw [← he0, mul_zero]; exact hD0 _
    · have h := hle e ⟨he0, he.2⟩
      rw [le_div_iff₀ he0, huD] at h
      have h2 : (1 - (a - e)) * D (a - e) ≤ D (a - e) := by
        have : 1 - (a - e) ≤ 1 := by linarith [he.2]
        nlinarith [hD0 (a - e)]
      linarith

theorem pathconvex_ii : Claims.pathconvex_ii := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ hφ hκ h0 h1
  set a := StatFormal.Distances.tvDist P Q with ha
  have hu := uPath_convex P Q hφ hκ
  have hua := uPath_tv hφ hκ h1
  have huD : ∀ α, uPath φ P Q α = (1 - α) * Dpop φ P Q α := fun _ => rfl
  have hD0 : ∀ α, 0 ≤ Dpop φ P Q α := Dpop_nonneg0 φ P Q
  obtain ⟨hex, hall⟩ := limit_facts h0 h1 hu hua huD hD0
  refine ⟨ratio_mono hu h1 hua, hex, fun s hs => ?_, ?_⟩
  · obtain ⟨hs0, _, hiff, hpos⟩ := hall s hs
    refine ⟨hs0, ⟨fun ⟨c₀, hc₀, _, hb⟩ => ?_, fun h => ⟨s, h, le_rfl, hpos h⟩⟩, fun h => ⟨h, le_rfl, hpos h⟩⟩
    have := hiff ⟨c₀, hc₀, hb⟩
    linarith
  · intro e he
    rcases he.1.eq_or_lt with he0 | he0
    · have hDa : Dpop φ P Q a = 0 := by
        have := StatFormal.TrimmedMMD.ZeroSet.zero_of_tv_le 𝒳 H P Q φ κ _ hφ hκ (StatFormal.Distances.tvDist_nonneg P Q) h1 le_rfl
        exact this
      rw [← he0, sub_zero, hDa, mul_zero, zero_div]
    · have hmono := ratio_mono hu h1 hua
      have hr := hmono ⟨he0, he.2⟩ ⟨h0, le_rfl⟩ he.2
      simp only [sub_self] at hr
      -- `u(a − e)/e ≤ u(0)/a = D₀/a`
      have hu0 : uPath φ P Q 0 = Dpop φ P Q 0 := by simp [uPath]
      rw [hu0, div_le_div_iff₀ he0 h0, huD] at hr
      have hden : 0 < a * (1 - a) := mul_pos h0 (by linarith)
      rw [le_div_iff₀ hden]
      have hDe := hD0 (a - e)
      have hD00 := hD0 0
      -- `(1 − a + e) D(a−e) a ≤ D₀ e` and `1 − a ≤ 1 − a + e`
      have : (1 - a) * Dpop φ P Q (a - e) * a ≤ (1 - (a - e)) * Dpop φ P Q (a - e) * a := by
        have : (1 - a) * Dpop φ P Q (a - e) ≤ (1 - (a - e)) * Dpop φ P Q (a - e) :=
          mul_le_mul_of_nonneg_right (by linarith) hDe
        exact mul_le_mul_of_nonneg_right this h0.le
      nlinarith

theorem pathconvex_tangent : Claims.pathconvex_tangent := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ hφ hκ h0 h1 hs
  obtain ⟨-, -, hall, -⟩ := pathconvex_ii 𝒳 H P Q φ κ hφ hκ h0 h1
  obtain ⟨-, hiff, -⟩ := hall 0 hs
  have hno : ¬ ∃ c₀ : ℝ, PolyMargin φ P Q c₀ 1 := fun h => lt_irrefl _ (hiff.1 h)
  refine ⟨hno, fun c₀ γ hm => ?_⟩
  rcases hm.2.1.eq_or_lt with hγ | hγ
  · exact absurd ⟨c₀, hγ ▸ hm⟩ hno
  · exact hγ

/-! ### `lem:marginexists` -/

theorem marginexists : Claims.marginexists := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ hφ hκ hch h0 h1
  set a := StatFormal.Distances.tvDist P Q with ha
  have hcont := StatFormal.Wave18b.continuity_cont 𝒳 H P Q φ κ hφ hκ
  have hD0 : ∀ α, 0 ≤ Dpop φ P Q α := Dpop_nonneg0 φ P Q
  have hDa : Dpop φ P Q a = 0 :=
    StatFormal.TrimmedMMD.ZeroSet.zero_of_tv_le 𝒳 H P Q φ κ _ hφ hκ (StatFormal.Distances.tvDist_nonneg P Q) h1 le_rfl
  -- the minimum over `[ε,a]` of `ε' ↦ D(a − ε')` is at `ε' = ε` (the path is nonincreasing)
  have hleast : ∀ ε ∈ Icc (0 : ℝ) a,
      IsLeast ((fun e' => Dpop φ P Q (a - e')) '' Icc ε a) (Dpop φ P Q (a - ε)) := by
    intro ε hε
    refine ⟨⟨ε, ⟨le_rfl, hε.2⟩, rfl⟩, ?_⟩
    rintro _ ⟨e', he', rfl⟩
    exact StatFormal.Wave18b.Dpop_anti P Q φ (by linarith [he'.2]) (by linarith [he'.1]) (by linarith [hε.1])
  have hm : ∀ ε ∈ Icc (0 : ℝ) a, mRun φ P Q ε = Dpop φ P Q (a - ε) := fun ε hε => (hleast ε hε).csInf_eq
  have hω : ∀ ε ∈ Icc (0 : ℝ) a, omegaRun φ P Q ε = ε / a * Dpop φ P Q (a - ε) := fun ε hε => by
    simp only [omegaRun, ← ha, hm ε hε]
  have hpos : ∀ ε ∈ Ioc (0 : ℝ) a, 0 < Dpop φ P Q (a - ε) := fun ε hε => by
    have := uPath_pos hφ hκ hch (P := P) (Q := Q) (α := a - ε) ⟨by linarith [hε.2], by linarith [hε.1]⟩ h1
    exact pos_of_mul_pos_right this (by linarith [hε.1])
  have hcont' : ContinuousOn (fun ε => ε / a * Dpop φ P Q (a - ε)) (Icc 0 a) := by
    refine ((continuousOn_id.div_const a)).mul ?_
    refine hcont.comp (continuousOn_const.sub continuousOn_id) ?_
    intro ε hε; exact ⟨by linarith [hε.2], by linarith [hε.1]⟩
  have hsmono : StrictMonoOn (omegaRun φ P Q) (Icc 0 a) := by
    intro x hx y hy hxy
    rw [hω x hx, hω y hy]
    have hDy := hpos y ⟨by linarith [hx.1], hy.2⟩
    have hmon : Dpop φ P Q (a - x) ≤ Dpop φ P Q (a - y) :=
      StatFormal.Wave18b.Dpop_anti P Q φ (by linarith [hy.2]) (by linarith) (by linarith [hx.1])
    calc x / a * Dpop φ P Q (a - x) ≤ x / a * Dpop φ P Q (a - y) :=
          mul_le_mul_of_nonneg_left hmon (div_nonneg hx.1 h0.le)
      _ < y / a * Dpop φ P Q (a - y) := mul_lt_mul_of_pos_right (div_lt_div_of_pos_right hxy h0) hDy
  have hω0 : omegaRun φ P Q 0 = 0 := by simp [omegaRun]
  have hωle : ∀ ε ∈ Icc (0 : ℝ) a, omegaRun φ P Q ε ≤ Dpop φ P Q (a - ε) := fun ε hε => by
    rw [hω ε hε]
    have : ε / a ≤ 1 := (div_le_one h0).2 hε.2
    nlinarith [hD0 (a - ε), div_nonneg hε.1 h0.le]
  have hωc : ContinuousOn (omegaRun φ P Q) (Icc 0 a) := hcont'.congr fun ε hε => hω ε hε
  have hωnn : ∀ ε ∈ Icc (0 : ℝ) a, 0 ≤ omegaRun φ P Q ε := fun ε hε => by
    rw [hω ε hε]; exact mul_nonneg (div_nonneg hε.1 h0.le) (hD0 _)
  exact ⟨fun ε hε => (hm ε hε) ▸ hleast ε hε, hωc, hsmono, hω0, hωle, hsmono, hωc, hω0, hωnn, hωle⟩

end StatFormal.Wave31ti
