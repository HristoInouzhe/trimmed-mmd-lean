import StatFormal.Wave30tr.Statements
import StatFormal.Archive.TrimmedMMD.Concentration.Proofs
import StatFormal.Archive.TrimmedMMD.Unconditional.Proofs

/-!
# Route: Step 1 of Theorem A, the deterministic reduction (untrusted proof material)

For probability measures `P₁, Q₁` ("source") and `P₂, Q₂` ("target") and `α ∈ [0,1)`, `β = (1−α)⁻¹`:
if `(P₂ − P₁)(⟨−f,φ⟩ − q)₊ + (Q₂ − Q₁)(⟨f,φ⟩ − q')₊ ≤ S` for all `‖f‖ ≤ 1`, `|q|, |q'| ≤ κ`, then
`dist(𝒞_α(P₁), 𝒞_α(Q₁)) ≤ dist(𝒞_α(P₂), 𝒞_α(Q₂)) + β S` (`setDist_region_le`).

Route (the NOTE's Step 1, with `lem:separation` replaced by a projection argument valid for any nonempty convex sets,
so no attainment or weak compactness is needed): let `v` be the projection of `0` onto `closure(𝒞_α(P₁) − 𝒞_α(Q₁))`;
then `dist ≤ ‖v‖` and, for `f = v/‖v‖`, `⟨f, a − b⟩ ≥ ‖v‖` for all `a, b` (the separation inequality with equality
direction). The two support functions at `−f` (for `P₁`) and `f` (for `Q₁`) are attained at the CVaR witnesses of
`exists_cvar_witness` (`eq:cvar` + `lem:tcompact`, quantiles `q, q' ∈ [−κ, κ]`); for the target measures the same `q, q'`
give upper bounds (`integral_mul_le_cvar`). Subtracting gives the claim for every pair `a ∈ 𝒞_α(P₂)`, `b ∈ 𝒞_α(Q₂)`.
Applied with (source, target) = (empirical, population) this is part (a), and with the roles exchanged part (b).
-/

noncomputable section
open MeasureTheory Set
open scoped Pointwise

namespace StatFormal.Wave30tr

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.Concentration

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [InnerProductSpace ℝ H] in
theorem setDist_nonneg (A B : Set H) : 0 ≤ setDist A B :=
  Real.sInf_nonneg (by rintro _ ⟨a, -, b, -, rfl⟩; exact norm_nonneg _)

omit [InnerProductSpace ℝ H] in
theorem le_setDist_add {A B : Set H} (hA : A.Nonempty) (hB : B.Nonempty) {c : ℝ}
    (h : ∀ a ∈ A, ∀ b ∈ B, c ≤ ‖a - b‖) : c ≤ setDist A B := by
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  refine le_csInf ⟨_, a₀, ha₀, b₀, hb₀, rfl⟩ ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact h a ha b hb

variable {φ : 𝒳 → H} {κ α : ℝ}

/-- **Step 1 (deterministic reduction).** -/
theorem setDist_region_le [CompleteSpace H] (P₁ Q₁ P₂ Q₂ : Measure 𝒳) [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure Q₁] [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂]
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) {S : ℝ}
    (hS : ∀ (f : H) (q q' : ℝ), ‖f‖ ≤ 1 → |q| ≤ κ → |q'| ≤ κ →
      (∫ x, gTM φ (-f, q) x ∂P₂ - ∫ x, gTM φ (-f, q) x ∂P₁) +
        (∫ x, gTM φ (f, q') x ∂Q₂ - ∫ x, gTM φ (f, q') x ∂Q₁) ≤ S) :
    setDist (region φ α P₁) (region φ α Q₁) ≤
      setDist (region φ α P₂) (region φ α Q₂) + 1 / (1 - α) * S := by
  set β := 1 / (1 - α) with hβdef
  have hβ1 : 1 ≤ β := by rw [hβdef, le_div_iff₀ (by linarith)]; linarith
  have hβ0 : 0 ≤ β := by linarith
  have hκ0 : 0 ≤ κ := by
    obtain ⟨y⟩ := nonempty_of_isProbabilityMeasure P₁
    exact (norm_nonneg _).trans (hκ y)
  have hS0 : 0 ≤ S := by
    have := hS 0 0 0 (by simp) (by simp [hκ0]) (by simp [hκ0])
    simpa [gTM] using this
  set A₁ := region φ α P₁
  set B₁ := region φ α Q₁
  set A₂ := region φ α P₂
  set B₂ := region φ α Q₂
  have hA₁ : A₁.Nonempty := region_nonempty P₁ hα0 hα1
  have hB₁ : B₁.Nonempty := region_nonempty Q₁ hα0 hα1
  have hA₂ : A₂.Nonempty := region_nonempty P₂ hα0 hα1
  have hB₂ : B₂.Nonempty := region_nonempty Q₂ hα0 hα1
  -- projection of `0` onto the closure of `A₁ − B₁`
  set K := closure (A₁ - B₁) with hK
  have hKne : K.Nonempty := (hA₁.sub hB₁).closure
  have hKconv : Convex ℝ K := ((region_convex P₁ hφ hκ).sub (region_convex Q₁ hφ hκ)).closure
  have hKcomp : IsComplete K := isClosed_closure.isComplete
  obtain ⟨v, hvK, hv⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKcomp hKconv 0
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hKconv hvK).1 hv
  have hd1 : setDist A₁ B₁ ≤ ‖v‖ := by
    have hcl : K ⊆ {c | setDist A₁ B₁ ≤ ‖c‖} := by
      refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact setDist_le_norm ha hb
    exact hcl hvK
  by_cases hv0 : v = 0
  · rw [hv0, norm_zero] at hd1
    have := setDist_nonneg A₂ B₂
    have : 0 ≤ β * S := mul_nonneg hβ0 hS0
    linarith
  have hnpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  set f : H := ‖v‖⁻¹ • v with hfdef
  have hf1 : ‖f‖ ≤ 1 := by
    rw [hfdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnpos.ne']
  -- separation: `⟨f, a − b⟩ ≥ ‖v‖` on `A₁ × B₁`
  have hsep : ∀ a ∈ A₁, ∀ b ∈ B₁, ‖v‖ ≤ inner ℝ f (a - b) := by
    intro a ha b hb
    have h := hvi (a - b) (subset_closure ⟨a, ha, b, hb, rfl⟩)
    have h' : ‖v‖ ^ 2 ≤ inner ℝ v (a - b) := by
      have e : inner ℝ (0 - v) (a - b - v) = ‖v‖ ^ 2 - inner ℝ v (a - b) := by
        rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq]; ring
      linarith
    have e2 : inner ℝ f (a - b) = ‖v‖⁻¹ * inner ℝ v (a - b) := by
      rw [hfdef, real_inner_smul_left]
    rw [e2, le_inv_mul_iff₀ hnpos]
    nlinarith
  -- the CVaR witnesses at `−f` for `P₁` and at `f` for `Q₁`
  set Y₁ : 𝒳 → ℝ := fun x => inner ℝ (-f) (φ x) with hY₁
  set Y₂ : 𝒳 → ℝ := fun x => inner ℝ f (φ x) with hY₂
  have hY₁m : Measurable Y₁ := (stronglyMeasurable_const.inner hφ).measurable
  have hY₂m : Measurable Y₂ := (stronglyMeasurable_const.inner hφ).measurable
  have hYb : ∀ (u : H), ‖u‖ ≤ 1 → ∀ x, |inner ℝ u (φ x)| ≤ κ := fun u hu x =>
    (abs_real_inner_le_norm _ _).trans (by
      calc ‖u‖ * ‖φ x‖ ≤ 1 * κ := mul_le_mul hu (hκ x) (norm_nonneg _) zero_le_one
        _ = κ := one_mul κ)
  have hf1' : ‖-f‖ ≤ 1 := by rw [norm_neg]; exact hf1
  obtain ⟨q₁, hq₁, g₁, hg₁, hb₁, hi₁, hval₁⟩ :=
    exists_cvar_witness P₁ hY₁m (hYb (-f) hf1') hβ1
  obtain ⟨q₂, hq₂, g₂, hg₂, hb₂, hi₂, hval₂⟩ :=
    exists_cvar_witness Q₁ hY₂m (hYb f hf1) hβ1
  set a₁ := ∫ x, g₁ x • φ x ∂P₁
  set b₁ := ∫ x, g₂ x • φ x ∂Q₁
  have ha₁ : a₁ ∈ A₁ := ⟨g₁, hg₁, hb₁, hi₁, rfl⟩
  have hb₁' : b₁ ∈ B₁ := ⟨g₂, hg₂, hb₂, hi₂, rfl⟩
  have hia₁ : inner ℝ (-f) a₁ = q₁ + β * ∫ x, max (Y₁ x - q₁) 0 ∂P₁ := by
    rw [inner_integral_smul P₁ hφ hκ hg₁ hb₁ (-f)]; exact hval₁
  have hib₁ : inner ℝ f b₁ = q₂ + β * ∫ x, max (Y₂ x - q₂) 0 ∂Q₁ := by
    rw [inner_integral_smul Q₁ hφ hκ hg₂ hb₂ f]; exact hval₂
  have hlow : setDist A₁ B₁ ≤
      -q₁ - β * ∫ x, max (Y₁ x - q₁) 0 ∂P₁ - (q₂ + β * ∫ x, max (Y₂ x - q₂) 0 ∂Q₁) := by
    have h := hsep a₁ ha₁ b₁ hb₁'
    rw [inner_sub_right, hib₁] at h
    have : inner ℝ f a₁ = -inner ℝ (-f) a₁ := by rw [inner_neg_left, neg_neg]
    rw [this, hia₁] at h
    linarith
  have hSq := hS f q₁ q₂ hf1 hq₁ hq₂
  -- upper bounds for every target pair
  have key : ∀ a ∈ A₂, ∀ b ∈ B₂, setDist A₁ B₁ - β * S ≤ ‖a - b‖ := by
    rintro _ ⟨g, hg, hb, hi, rfl⟩ _ ⟨g', hg', hb', hi', rfl⟩
    have hu1 : inner ℝ (-f) (∫ x, g x • φ x ∂P₂) ≤ q₁ + β * ∫ x, max (Y₁ x - q₁) 0 ∂P₂ := by
      rw [inner_integral_smul P₂ hφ hκ hg hb (-f)]
      exact integral_mul_le_cvar P₂ hY₁m (hYb (-f) hf1') hg hb hi q₁
    have hu2 : inner ℝ f (∫ x, g' x • φ x ∂Q₂) ≤ q₂ + β * ∫ x, max (Y₂ x - q₂) 0 ∂Q₂ := by
      rw [inner_integral_smul Q₂ hφ hκ hg' hb' f]
      exact integral_mul_le_cvar Q₂ hY₂m (hYb f hf1) hg' hb' hi' q₂
    have hnorm : inner ℝ f ((∫ x, g x • φ x ∂P₂) - ∫ x, g' x • φ x ∂Q₂) ≤
        ‖(∫ x, g x • φ x ∂P₂) - ∫ x, g' x • φ x ∂Q₂‖ := by
      refine (real_inner_le_norm _ _).trans ?_
      calc ‖f‖ * ‖(∫ x, g x • φ x ∂P₂) - ∫ x, g' x • φ x ∂Q₂‖
          ≤ 1 * ‖(∫ x, g x • φ x ∂P₂) - ∫ x, g' x • φ x ∂Q₂‖ := by gcongr
        _ = _ := one_mul _
    rw [inner_sub_right] at hnorm
    have hneg : inner ℝ f (∫ x, g x • φ x ∂P₂) = -inner ℝ (-f) (∫ x, g x • φ x ∂P₂) := by
      rw [inner_neg_left, neg_neg]
    rw [hneg] at hnorm
    have hSq' : β * ((∫ x, max (Y₁ x - q₁) 0 ∂P₂ - ∫ x, max (Y₁ x - q₁) 0 ∂P₁) +
        (∫ x, max (Y₂ x - q₂) 0 ∂Q₂ - ∫ x, max (Y₂ x - q₂) 0 ∂Q₁)) ≤ β * S :=
      mul_le_mul_of_nonneg_left hSq hβ0
    nlinarith
  have := le_setDist_add hA₂ hB₂ key
  linarith

end StatFormal.Wave30tr
