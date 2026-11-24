import StatFormal.Archive.Wave20a.Statements

/-!
# Route — paper 2 `prop:translation` (untrusted)

* For every coupling `γ` of the two centres, `Σ γ_ij ⟨w, x⁰_i − x¹_j⟩ = g(w)` and `Σ γ_ij = 1`; translating the
  centres adds the constant `2 g s + s²`, `s = ⟨w, δ₀ − δ₁⟩`, to every coupling cost, so the infimum moves by it.
* (i): integrate the identity; `E⟨w, δ⟩ = 0`, `E⟨w, δ⟩² = Cov(δ)(w,w)` (`covarianceBilin_apply`).
* (ii): Cauchy–Schwarz for the positive form `⟨·, C ·⟩` (discriminant), attained at `u = ±√β w/|C^{1/2}w|`;
  `|g| ≤ Δ` by Jensen on every coupling.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave20a

open StatFormal.RobustEquality.Paper2.Seminorm

section Tr
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n₀ n₁ : ℕ}

/-- The coupling cost of `Deltafin`. -/
def tcost (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (w : E) (γ : Fin n₀ → Fin n₁ → ℝ) : ℝ :=
  ∑ i, ∑ j, γ i j * ⟪w, x₀ i - x₁ j⟫ ^ 2

lemma polytope_nonempty {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ} (h₀ : ProbW a₀) (h₁ : ProbW a₁) :
    (fun i j => a₀ i * a₁ j) ∈ Polytope a₀ a₁ := by
  refine ⟨fun i j => mul_nonneg (h₀.1 i) (h₁.1 j), fun i => ?_, fun j => ?_⟩
  · rw [← Finset.mul_sum, h₁.2, mul_one]
  · rw [← Finset.sum_mul, h₀.2, one_mul]

lemma poly_sum_one {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ} (h₀ : ProbW a₀) {γ} (hγ : γ ∈ Polytope a₀ a₁) :
    ∑ i, ∑ j, γ i j = 1 := by
  simp_rw [hγ.2.1]; exact h₀.2

lemma poly_first {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ} (h₀ : ProbW a₀) (h₁ : ProbW a₁) {γ}
    (hγ : γ ∈ Polytope a₀ a₁) (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (w : E) :
    ∑ i, ∑ j, γ i j * ⟪w, x₀ i - x₁ j⟫ = gapW a₀ x₀ a₁ x₁ w := by
  have e1 : ∑ i, ∑ j, γ i j * ⟪w, x₀ i⟫ = ⟪w, meanC a₀ x₀⟫ := by
    simp_rw [← Finset.sum_mul, hγ.2.1, meanC, inner_sum, inner_smul_right]
  have e2 : ∑ i, ∑ j, γ i j * ⟪w, x₁ j⟫ = ⟪w, meanC a₁ x₁⟫ := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hγ.2.2, meanC, inner_sum, inner_smul_right]
  simp_rw [inner_sub_right, mul_sub, Finset.sum_sub_distrib, e1, e2, gapW, inner_sub_right]

lemma tcost_nonneg {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ} {γ} (hγ : γ ∈ Polytope a₀ a₁)
    (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (w : E) : 0 ≤ tcost x₀ x₁ w γ :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hγ.1 i j) (sq_nonneg _)

lemma tcost_shift {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ} (h₀ : ProbW a₀) (h₁ : ProbW a₁) {γ}
    (hγ : γ ∈ Polytope a₀ a₁) (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (w δ₀ δ₁ : E) :
    tcost (fun i => x₀ i + δ₀) (fun j => x₁ j + δ₁) w γ =
      tcost x₀ x₁ w γ + (2 * gapW a₀ x₀ a₁ x₁ w * ⟪w, δ₀ - δ₁⟫ + ⟪w, δ₀ - δ₁⟫ ^ 2) := by
  have key : ∀ i j, (x₀ i + δ₀) - (x₁ j + δ₁) = (x₀ i - x₁ j) + (δ₀ - δ₁) := fun i j => by abel
  have hexp : ∀ i j, γ i j * ⟪w, (x₀ i + δ₀) - (x₁ j + δ₁)⟫ ^ 2 =
      γ i j * ⟪w, x₀ i - x₁ j⟫ ^ 2 + 2 * ⟪w, δ₀ - δ₁⟫ * (γ i j * ⟪w, x₀ i - x₁ j⟫) +
        ⟪w, δ₀ - δ₁⟫ ^ 2 * γ i j := fun i j => by
    rw [key, inner_add_right]; ring
  unfold tcost
  simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, poly_first h₀ h₁ hγ, poly_sum_one h₀ hγ]
  ring

/-- `Deltafin² = inf` of the coupling cost. -/
lemma deltafin_sq {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ} (h₀ : ProbW a₀) (h₁ : ProbW a₁)
    (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (w : E) :
    Deltafin a₀ x₀ a₁ x₁ w ^ 2 = ⨅ γ : Polytope a₀ a₁, tcost x₀ x₁ w γ := by
  haveI : Nonempty {γ : Fin n₀ → Fin n₁ → ℝ | (∀ i j, 0 ≤ γ i j) ∧ (∀ i, ∑ j, γ i j = a₀ i) ∧
      ∀ j, ∑ i, γ i j = a₁ j} := ⟨⟨_, polytope_nonempty h₀ h₁⟩⟩
  unfold Deltafin
  rw [Real.sq_sqrt]
  · rfl
  · exact le_ciInf fun γ => tcost_nonneg γ.2 x₀ x₁ w

lemma iInf_add_const' {ι : Type*} [Nonempty ι] (F : ι → ℝ) (hF : BddBelow (range F)) (c : ℝ) :
    (⨅ i, (F i + c)) = (⨅ i, F i) + c := by
  apply le_antisymm
  · obtain ⟨m, hm⟩ := hF
    have hB : BddBelow (range fun i => F i + c) :=
      ⟨m + c, by rintro _ ⟨j, rfl⟩; have := hm ⟨j, rfl⟩; simp only; linarith⟩
    have : (⨅ i, (F i + c)) - c ≤ ⨅ i, F i := le_ciInf fun i => by
      have := ciInf_le hB i
      linarith
    linarith
  · exact le_ciInf fun i => by have := ciInf_le hF i; linarith

theorem translation_identity_aux {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ} (h₀ : ProbW a₀) (h₁ : ProbW a₁)
    (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (w δ₀ δ₁ : E) :
    realised a₀ x₀ a₁ x₁ w δ₀ δ₁ =
      Deltafin a₀ x₀ a₁ x₁ w ^ 2 - gapW a₀ x₀ a₁ x₁ w ^ 2 + (gapW a₀ x₀ a₁ x₁ w + ⟪w, δ₀ - δ₁⟫) ^ 2 := by
  haveI : Nonempty (Polytope a₀ a₁) := ⟨⟨_, polytope_nonempty h₀ h₁⟩⟩
  unfold realised
  rw [deltafin_sq h₀ h₁, deltafin_sq h₀ h₁]
  have : (⨅ γ : Polytope a₀ a₁, tcost (fun i => x₀ i + δ₀) (fun j => x₁ j + δ₁) w γ) =
      ⨅ γ : Polytope a₀ a₁, (tcost x₀ x₁ w γ +
        (2 * gapW a₀ x₀ a₁ x₁ w * ⟪w, δ₀ - δ₁⟫ + ⟪w, δ₀ - δ₁⟫ ^ 2)) :=
    iInf_congr fun γ => tcost_shift h₀ h₁ γ.2 x₀ x₁ w δ₀ δ₁
  rw [this, iInf_add_const' _ ⟨0, by rintro _ ⟨γ, rfl⟩; exact tcost_nonneg γ.2 x₀ x₁ w⟩]
  ring

/-- `g(w)² ≤ Δ(w)²` (Jensen on every coupling). -/
lemma gap_sq_le {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ} (h₀ : ProbW a₀) (h₁ : ProbW a₁)
    (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (w : E) :
    gapW a₀ x₀ a₁ x₁ w ^ 2 ≤ Deltafin a₀ x₀ a₁ x₁ w ^ 2 := by
  haveI : Nonempty (Polytope a₀ a₁) := ⟨⟨_, polytope_nonempty h₀ h₁⟩⟩
  rw [deltafin_sq h₀ h₁]
  refine le_ciInf fun γ => ?_
  rw [← poly_first h₀ h₁ γ.2]
  have hγ := γ.2
  have key := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n₀ × Fin n₁))
    (fun p => √(γ.1 p.1 p.2)) (fun p => √(γ.1 p.1 p.2) * ⟪w, x₀ p.1 - x₁ p.2⟫)
  have hsq : ∀ p : Fin n₀ × Fin n₁, √(γ.1 p.1 p.2) * √(γ.1 p.1 p.2) = γ.1 p.1 p.2 :=
    fun p => Real.mul_self_sqrt (hγ.1 _ _)
  have hl : ∑ p : Fin n₀ × Fin n₁, √(γ.1 p.1 p.2) * (√(γ.1 p.1 p.2) * ⟪w, x₀ p.1 - x₁ p.2⟫) =
      ∑ i, ∑ j, γ.1 i j * ⟪w, x₀ i - x₁ j⟫ := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hsq (i, j)]
  have hr1 : ∑ p : Fin n₀ × Fin n₁, √(γ.1 p.1 p.2) ^ 2 = 1 := by
    rw [← poly_sum_one h₀ hγ, ← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Real.sq_sqrt (hγ.1 i j)]
  have hr2 : ∑ p : Fin n₀ × Fin n₁, (√(γ.1 p.1 p.2) * ⟪w, x₀ p.1 - x₁ p.2⟫) ^ 2 = tcost x₀ x₁ w γ.1 := by
    unfold tcost
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, Real.sq_sqrt (hγ.1 i j)]
  rw [hl, hr1, hr2, one_mul] at key
  exact key

lemma abs_gap_le {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ} (h₀ : ProbW a₀) (h₁ : ProbW a₁)
    (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (w : E) :
    |gapW a₀ x₀ a₁ x₁ w| ≤ Deltafin a₀ x₀ a₁ x₁ w := by
  have hD : 0 ≤ Deltafin a₀ x₀ a₁ x₁ w := Real.sqrt_nonneg _
  exact abs_le_of_sq_le_sq' (gap_sq_le h₀ h₁ x₀ x₁ w) hD |> fun h => abs_le.2 h

/-- Cauchy–Schwarz for a positive operator: `⟨w, C u⟩² ≤ ⟨w, C w⟩⟨u, C u⟩`. -/
lemma pos_cs [CompleteSpace E] {C : E →L[ℝ] E} (hC : C.IsPositive) (w u : E) :
    ⟪w, C u⟫ ^ 2 ≤ ⟪w, C w⟫ * ⟪u, C u⟫ := by
  have hsym : ∀ x y, ⟪C x, y⟫ = ⟪x, C y⟫ := fun x y => hC.isSymmetric x y
  have hq : ∀ t : ℝ, 0 ≤ ⟪u, C u⟫ * (t * t) + (2 * ⟪w, C u⟫) * t + ⟪w, C w⟫ := by
    intro t
    have := hC.inner_nonneg_right (w + t • u)
    have e : ⟪w + t • u, C (w + t • u)⟫ = ⟪u, C u⟫ * (t * t) + (2 * ⟪w, C u⟫) * t + ⟪w, C w⟫ := by
      simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        RCLike.conj_to_real]
      have : ⟪u, C w⟫ = ⟪w, C u⟫ := by rw [← hsym, real_inner_comm]
      rw [this]; ring
    linarith [e ▸ this]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith [hd]

end Tr

namespace Claims
end Claims

open Claims in
theorem translation_identity : Claims.translation_identity := by
  intro E _ _ n₀ n₁ a₀ x₀ a₁ x₁ w δ₀ δ₁ h₀ h₁
  exact translation_identity_aux h₀ h₁ x₀ x₁ w δ₀ δ₁

theorem translation_mean : Claims.translation_mean := by
  intro E _ _ _ _ _ _ Ω _ P _ n₀ n₁ a₀ x₀ a₁ x₁ w δ₀ δ₁ h₀ h₁ hm₀ hm₁ hL hmean
  set δ : Ω → E := fun ω => δ₀ ω - δ₁ ω with hδ
  have hδm : Measurable δ := hm₀.sub hm₁
  set g := gapW a₀ x₀ a₁ x₁ w
  set D := Deltafin a₀ x₀ a₁ x₁ w
  have hpt : ∀ ω, realised a₀ x₀ a₁ x₁ w (δ₀ ω) (δ₁ ω) =
      D ^ 2 + 2 * g * ⟪w, δ ω⟫ + ⟪w, δ ω⟫ ^ 2 := fun ω => by
    rw [translation_identity_aux h₀ h₁]; ring
  have hint : Integrable δ P := hL.integrable (by norm_num)
  have hin1 : Integrable (fun ω => ⟪w, δ ω⟫) P := hint.const_inner w
  have hin2 : Integrable (fun ω => ⟪w, δ ω⟫ ^ 2) P := by
    have : MemLp (fun ω => ⟪w, δ ω⟫) 2 P := hL.const_inner w
    exact this.integrable_sq
  have h1 : ∫ ω, ⟪w, δ ω⟫ ∂P = 0 := by
    rw [integral_inner hint, hmean, inner_zero_right]
  simp_rw [hpt]
  rw [integral_add (by
      exact (integrable_const _).add (hin1.const_mul _)) hin2,
    integral_add (integrable_const _) (hin1.const_mul _), integral_const_mul, h1]
  have hu : P.real univ = 1 := by simp [Measure.real]
  rw [integral_const, hu, one_smul, mul_zero, add_zero]
  congr 1
  have hLm : MemLp id 2 (P.map δ) := (memLp_map_measure_iff aestronglyMeasurable_id hδm.aemeasurable).2 hL
  rw [covarianceBilin_apply hLm]
  have hm0 : (P.map δ)[id] = 0 := by
    rw [integral_map hδm.aemeasurable aestronglyMeasurable_id]; exact hmean
  rw [hm0, integral_map hδm.aemeasurable (by
    exact (Continuous.aestronglyMeasurable (by fun_prop)))]
  simp [sq]

theorem translation_sup : Claims.translation_sup := by
  intro E _ _ _ n₀ n₁ a₀ x₀ a₁ x₁ w C β h₀ h₁ hC hβ
  set g := gapW a₀ x₀ a₁ x₁ w
  set D := Deltafin a₀ x₀ a₁ x₁ w
  set q := √⟪w, C w⟫
  have hq0 : 0 ≤ ⟪w, C w⟫ := hC.inner_nonneg_right w
  have hval : ∀ δ₀ δ₁ : E, realised a₀ x₀ a₁ x₁ w δ₀ δ₁ = D ^ 2 - g ^ 2 + (g + ⟪w, δ₀ - δ₁⟫) ^ 2 :=
    fun δ₀ δ₁ => translation_identity_aux h₀ h₁ x₀ x₁ w δ₀ δ₁
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- attainment
    by_cases hq : q = 0
    · refine ⟨0, 0, ⟨0, by simp, by simpa using hβ⟩, ?_⟩
      rw [hval, hq]; simp [sq_abs]
    · have hqp : 0 < q := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hq)
      set e : ℝ := if 0 ≤ g then 1 else -1
      have he2 : e ^ 2 = 1 := by by_cases hg : 0 ≤ g <;> simp [e, hg]
      have heg : e * g = |g| := by
        by_cases hg : 0 ≤ g
        · simp [e, hg, abs_of_nonneg hg]
        · simp [e, hg, abs_of_neg (not_le.1 hg)]
      set u : E := (e * √β / q) • w
      have hqq : q ^ 2 = ⟪w, C w⟫ := Real.sq_sqrt hq0
      refine ⟨C u, 0, ⟨u, by simp, ?_⟩, ?_⟩
      · simp only [u, map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
        have : e * √β / q * (e * √β / q * ⟪w, C w⟫) = e ^ 2 * (√β) ^ 2 * (⟪w, C w⟫ / q ^ 2) := by
          field_simp
        rw [this, he2, Real.sq_sqrt hβ, ← hqq, div_self (pow_ne_zero 2 hq)]; simp
      · rw [hval, sub_zero]
        simp only [u, map_smul, inner_smul_right]
        have : e * √β / q * ⟪w, C w⟫ = e * (√β * q) := by
          rw [← hqq]; field_simp
        rw [this]
        congr 1
        have : g + e * (√β * q) = e * (|g| + √β * q) := by
          rw [← heg]; linear_combination (-g) * he2
        rw [this, mul_pow, he2, one_mul]
  · -- upper bound
    rintro v ⟨δ₀, δ₁, ⟨u, hu, hβu⟩, rfl⟩
    rw [hval, hu]
    have hcs := pos_cs hC w u
    have huu : 0 ≤ ⟪u, C u⟫ := hC.inner_nonneg_right u
    have hs : |⟪w, C u⟫| ≤ √β * q := by
      rw [← Real.sqrt_sq_eq_abs]
      calc √(⟪w, C u⟫ ^ 2) ≤ √(⟪w, C w⟫ * ⟪u, C u⟫) := Real.sqrt_le_sqrt hcs
        _ = q * √⟪u, C u⟫ := by rw [Real.sqrt_mul hq0]
        _ ≤ q * √β := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hβu) (Real.sqrt_nonneg _)
        _ = √β * q := mul_comm _ _
    have : (g + ⟪w, C u⟫) ^ 2 ≤ (|g| + √β * q) ^ 2 := by
      rw [← sq_abs]
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact (abs_add_le _ _).trans (add_le_add_right hs _)
    linarith
  · have hg := abs_gap_le h₀ h₁ x₀ x₁ w
    have ha : 0 ≤ √β * q := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have : g ^ 2 = |g| ^ 2 := (sq_abs g).symm
    nlinarith [mul_le_mul_of_nonneg_right hg ha]

end StatFormal.Wave20a
