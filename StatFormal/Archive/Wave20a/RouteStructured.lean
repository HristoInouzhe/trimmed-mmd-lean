import StatFormal.Archive.Wave20a.Statements
import StatFormal.Archive.Wave20a.RouteTranslation
import StatFormal.Archive.RobustEquality.Paper2.Seminorm.Proofs

/-!
# Route — paper 2 `prop:structured` (untrusted)

* `⟨w, 𝔗_θ x − 𝔗_θ y⟩ = ⟨A_θᵀ w, x − y⟩`, so `Δ_θ(w) = Δ(A_θᵀ w)` (translations cancel); the groupwise
  infimum `inf_λ T⁰_s = β_s ‖(G_s⁻¹)ᵀ w‖²` is the certified `seminorm_wass` (any centre); `√·`, `+` and `(·)²` commute
  with `⨅`/`⨆` in `ℝ≥0∞` (monotone, continuous).
* weighted Minkowski `√Σc(f+g)² ≤ √Σcf² + √Σcg²` gives `Δ(v) ≤ Δ(v') + |v − v'|_{Σ₀} + |v − v'|_{Σ₁}` (couplings
  have the centres as marginals).
* all pieces of the cell bound are seminorms (`Seminorm.of`), so the bound is a maximum of squares of nonnegative
  convex functions.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave20a

open StatFormal.RobustEquality.Paper2.Seminorm

section W
variable {ι : Type*} [Fintype ι]

lemma wsqrt_add (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (f g : ι → ℝ) :
    √(∑ i, c i * (f i + g i) ^ 2) ≤ √(∑ i, c i * f i ^ 2) + √(∑ i, c i * g i ^ 2) := by
  have hn : ∀ F : ι → ℝ, ‖(WithLp.toLp 2 fun i => √(c i) * F i : EuclideanSpace ℝ ι)‖ = √(∑ i, c i * F i ^ 2) := by
    intro F
    rw [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (hc i)]
  have := norm_add_le (WithLp.toLp 2 fun i => √(c i) * f i : EuclideanSpace ℝ ι)
    (WithLp.toLp 2 fun i => √(c i) * g i)
  rw [hn, hn, ← WithLp.toLp_add] at this
  have e : (fun i => √(c i) * f i) + (fun i => √(c i) * g i) = fun i => √(c i) * (f i + g i) := by
    funext i; simp [mul_add]
  rw [e, hn] at this
  exact this

lemma wsqrt_smul (c : ι → ℝ) (f : ι → ℝ) (r : ℝ) :
    √(∑ i, c i * (r * f i) ^ 2) = |r| * √(∑ i, c i * f i ^ 2) := by
  have : ∑ i, c i * (r * f i) ^ 2 = r ^ 2 * ∑ i, c i * f i ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `w ↦ √(Σ c_i ℓ_i(w)²)` as a seminorm. -/
def wSemi (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ℓ : ι → E →ₗ[ℝ] ℝ) : Seminorm ℝ E :=
  Seminorm.of (fun w => √(∑ i, c i * ℓ i w ^ 2))
    (fun x y => by simpa [map_add] using wsqrt_add c hc (fun i => ℓ i x) (fun i => ℓ i y))
    (fun a x => by simpa [map_smul, Real.norm_eq_abs] using wsqrt_smul c (fun i => ℓ i x) a)

lemma wSemi_apply (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ℓ : ι → E →ₗ[ℝ] ℝ) (w : E) :
    wSemi c hc ℓ w = √(∑ i, c i * ℓ i w ^ 2) := rfl

end W

section S
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n₀ n₁ : ℕ}

/-- `v ↦ ⟨v, z⟫` as a linear map. -/
def innL (z : E) : E →ₗ[ℝ] ℝ := (innerSL ℝ z : E →L[ℝ] ℝ).toLinearMap.comp LinearMap.id

lemma innL_apply (z v : E) : innL z v = ⟪v, z⟫ := by
  simp [innL, real_inner_comm]

lemma smNorm_eq {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) (x : Fin n → E) (p v : E) :
    smNorm a x p v = wSemi a ha (fun i => innL (x i - p)) v := by
  simp [wSemi_apply, smNorm, innL_apply]

lemma gamNorm_eq {γ : Fin n₀ → Fin n₁ → ℝ} (hγ : ∀ i j, 0 ≤ γ i j) (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (v : E) :
    gamNorm γ x₀ x₁ v =
      wSemi (fun q : Fin n₀ × Fin n₁ => γ q.1 q.2) (fun q => hγ q.1 q.2) (fun q => innL (x₀ q.1 - x₁ q.2)) v := by
  simp only [wSemi_apply, gamNorm, innL_apply]
  congr 1
  rw [← Finset.univ_product_univ, Finset.sum_product]

/-- `√(coupling cost at v) ≤ √(cost at v') + |v−v'|_{Σ₀} + |v−v'|_{Σ₁}`. -/
lemma sqrt_tcost_le {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ} (h₀ : ProbW a₀) (h₁ : ProbW a₁) {γ}
    (hγ : γ ∈ Polytope a₀ a₁) (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (p v v' : E) :
    √(tcost x₀ x₁ v γ) ≤ √(tcost x₀ x₁ v' γ) + (smNorm a₀ x₀ p (v - v') + smNorm a₁ x₁ p (v - v')) := by
  have hc : ∀ q : Fin n₀ × Fin n₁, 0 ≤ γ q.1 q.2 := fun q => hγ.1 q.1 q.2
  have hT : ∀ u, tcost x₀ x₁ u γ = ∑ q : Fin n₀ × Fin n₁, γ q.1 q.2 * ⟪u, x₀ q.1 - x₁ q.2⟫ ^ 2 := by
    intro u; unfold tcost; rw [← Finset.univ_product_univ, Finset.sum_product]
  have h1 := wsqrt_add (fun q : Fin n₀ × Fin n₁ => γ q.1 q.2) hc (fun q => ⟪v', x₀ q.1 - x₁ q.2⟫)
    (fun q => ⟪v - v', x₀ q.1 - x₁ q.2⟫)
  have h2 := wsqrt_add (fun q : Fin n₀ × Fin n₁ => γ q.1 q.2) hc (fun q => ⟪v - v', x₀ q.1 - p⟫)
    (fun q => -⟪v - v', x₁ q.2 - p⟫)
  have e1 : ∀ q : Fin n₀ × Fin n₁, ⟪v', x₀ q.1 - x₁ q.2⟫ + ⟪v - v', x₀ q.1 - x₁ q.2⟫ = ⟪v, x₀ q.1 - x₁ q.2⟫ :=
    fun q => by rw [← inner_add_left]; simp
  have e2 : ∀ q : Fin n₀ × Fin n₁, ⟪v - v', x₀ q.1 - p⟫ + -⟪v - v', x₁ q.2 - p⟫ = ⟪v - v', x₀ q.1 - x₁ q.2⟫ :=
    fun q => by rw [← sub_eq_add_neg, ← inner_sub_right]; congr 1; abel
  simp only [e1] at h1
  simp only [e2] at h2
  have m0 : ∑ q : Fin n₀ × Fin n₁, γ q.1 q.2 * ⟪v - v', x₀ q.1 - p⟫ ^ 2 = ∑ i, a₀ i * ⟪v - v', x₀ i - p⟫ ^ 2 := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [← Finset.sum_mul, hγ.2.1 i]
  have m1 : ∑ q : Fin n₀ × Fin n₁, γ q.1 q.2 * (-⟪v - v', x₁ q.2 - p⟫) ^ 2 = ∑ j, a₁ j * ⟪v - v', x₁ j - p⟫ ^ 2 := by
    rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    simp_rw [neg_sq]
    rw [← Finset.sum_mul, hγ.2.2 j]
  rw [m0, m1] at h2
  rw [hT, hT]
  unfold smNorm
  exact h1.trans (add_le_add le_rfl h2)

lemma deltafin_lip {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ} (h₀ : ProbW a₀) (h₁ : ProbW a₁)
    (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (p v v' : E) :
    Deltafin a₀ x₀ a₁ x₁ v ≤ Deltafin a₀ x₀ a₁ x₁ v' + (smNorm a₀ x₀ p (v - v') + smNorm a₁ x₁ p (v - v')) := by
  set S := smNorm a₀ x₀ p (v - v') + smNorm a₁ x₁ p (v - v')
  have hS : 0 ≤ S := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hD' : 0 ≤ Deltafin a₀ x₀ a₁ x₁ v' := Real.sqrt_nonneg _
  have hD : 0 ≤ Deltafin a₀ x₀ a₁ x₁ v := Real.sqrt_nonneg _
  by_cases hlt : Deltafin a₀ x₀ a₁ x₁ v ≤ S
  · linarith
  push_neg at hlt
  have key : (Deltafin a₀ x₀ a₁ x₁ v - S) ^ 2 ≤ Deltafin a₀ x₀ a₁ x₁ v' ^ 2 := by
    haveI : Nonempty (Polytope a₀ a₁) := ⟨⟨_, polytope_nonempty h₀ h₁⟩⟩
    rw [deltafin_sq h₀ h₁ x₀ x₁ v']
    refine le_ciInf fun γ => ?_
    have h1 := sqrt_tcost_le h₀ h₁ γ.2 x₀ x₁ p v v'
    have h2 : Deltafin a₀ x₀ a₁ x₁ v ≤ √(tcost x₀ x₁ v γ) := by
      rw [← Real.sqrt_sq hD, deltafin_sq h₀ h₁]
      exact Real.sqrt_le_sqrt (ciInf_le ⟨0, by rintro _ ⟨g, rfl⟩; exact tcost_nonneg g.2 x₀ x₁ v⟩ γ)
    have h3 : Deltafin a₀ x₀ a₁ x₁ v - S ≤ √(tcost x₀ x₁ v' γ) := by linarith
    calc (Deltafin a₀ x₀ a₁ x₁ v - S) ^ 2 ≤ √(tcost x₀ x₁ v' γ) ^ 2 :=
          pow_le_pow_left₀ (by linarith) h3 2
      _ = tcost x₀ x₁ v' γ := Real.sq_sqrt (tcost_nonneg γ.2 x₀ x₁ v')
  have := Real.sqrt_le_sqrt key
  rw [Real.sqrt_sq (by linarith), Real.sqrt_sq hD'] at this
  linarith

/-- Translations cancel. -/
lemma deltafin_affine [CompleteSpace E] (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E)
    (A : E →L[ℝ] E) (b w : E) :
    Deltafin a₀ (fun i => A (x₀ i) + b) a₁ (fun j => A (x₁ j) + b) w =
      Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint A w) := by
  unfold Deltafin
  congr 1
  refine iInf_congr fun γ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, map_sub, add_sub_add_right_eq_sub]

end S

section E
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {n : ℕ}

lemma sqrtE_mono : Monotone sqrtE := fun x y h =>
  ENNReal.rpow_le_rpow (EReal.toENNReal_le_toENNReal h) (by norm_num)

lemma sqrtE_cont : Continuous sqrtE :=
  (ENNReal.continuous_rpow_const).comp EReal.continuous_toENNReal

lemma sqrtE_top : sqrtE ⊤ = ⊤ := by simp [sqrtE]

lemma sqrtE_coe {t : ℝ} (ht : 0 ≤ t) : sqrtE (t : EReal) = ENNReal.ofReal √t := by
  rw [sqrtE, EReal.real_coe_toENNReal, ENNReal.ofReal_rpow_of_nonneg ht (by norm_num), Real.sqrt_eq_rpow]

/-- `inf_{λ>0} √T⁰ = √β ‖(G⁻¹)ᵀ w‖`. -/
lemma iInf_sqrtT0 (G : E ≃L[ℝ] E) {β : ℝ} (hβ : 0 ≤ β) {a : Fin n → ℝ} (ha : ProbW a) (x : Fin n → E) (w : E) :
    (⨅ l : Set.Ioi (0 : ℝ), sqrtE (T0 G β a x w l)) =
      ENNReal.ofReal (√β * ‖ContinuousLinearMap.adjoint (G.symm : E →L[ℝ] E) w‖) := by
  have hw := (StatFormal.RobustEquality.Paper2.Seminorm.seminorm_wass E n β a x hβ ha.1 ha.2).1 G w
  have := sqrtE_mono.map_iInf_of_continuousAt (g := fun l : Set.Ioi (0 : ℝ) => T0 G β a x w l)
    sqrtE_cont.continuousAt sqrtE_top
  rw [Function.comp_def] at this
  rw [← this, hw, sqrtE_coe (mul_nonneg hβ (sq_nonneg _)), Real.sqrt_mul hβ, Real.sqrt_sq (norm_nonneg _)]

lemma sq_mono : Monotone fun x : ℝ≥0∞ => x ^ 2 := fun _ _ h => pow_le_pow_left₀ bot_le h 2

lemma iInf_sq {ι : Sort*} (g : ι → ℝ≥0∞) : (⨅ i, g i) ^ 2 = ⨅ i, g i ^ 2 :=
  sq_mono.map_iInf_of_continuousAt (ENNReal.continuous_pow 2).continuousAt (by simp)

lemma iSup_sq {ι : Sort*} (g : ι → ℝ≥0∞) : (⨆ i, g i) ^ 2 = ⨆ i, g i ^ 2 :=
  sq_mono.map_iSup_of_continuousAt (ENNReal.continuous_pow 2).continuousAt (by simp)

end E

theorem structured_value : Claims.structured_value := by
  intro E _ _ _ Θ _ n₀ n₁ G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A b w hβ₀ hβ₁ h₀ h₁
  unfold certStruct
  have hθ : ∀ θ, (⨅ (l₀ : Set.Ioi (0 : ℝ)) (l₁ : Set.Ioi (0 : ℝ)),
      (ENNReal.ofReal (Deltafin a₀ (fun i => A θ (x₀ i) + b θ) a₁ (fun j => A θ (x₁ j) + b θ) w) +
        sqrtE (T0 G₀ β₀ a₀ (fun i => A θ (x₀ i) + b θ) w l₀) +
        sqrtE (T0 G₁ β₁ a₁ (fun j => A θ (x₁ j) + b θ) w l₁)) ^ 2) =
      (ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A θ) w)) +
        ENNReal.ofReal (√β₀ * ‖ContinuousLinearMap.adjoint (G₀.symm : E →L[ℝ] E) w‖) +
        ENNReal.ofReal (√β₁ * ‖ContinuousLinearMap.adjoint (G₁.symm : E →L[ℝ] E) w‖)) ^ 2 := by
    intro θ
    rw [deltafin_affine, ← iInf_sqrtT0 G₀ hβ₀ h₀ (fun i => A θ (x₀ i) + b θ) w,
      ← iInf_sqrtT0 G₁ hβ₁ h₁ (fun j => A θ (x₁ j) + b θ) w]
    have e : ∀ (X : ℝ≥0∞) (s₀ s₁ : Set.Ioi (0 : ℝ) → ℝ≥0∞),
        X + (⨅ l, s₀ l) + (⨅ l, s₁ l) = ⨅ l₀, ⨅ l₁, (X + s₀ l₀ + s₁ l₁) := by
      intro X s₀ s₁
      rw [ENNReal.add_iInf (a := X), ENNReal.iInf_add]
      exact iInf_congr fun l₀ => by rw [ENNReal.add_iInf]
    rw [e, iInf_sq]
    refine iInf_congr fun l₀ => ?_
    rw [iInf_sq]
  simp_rw [hθ]
  rw [← iSup_sq, ENNReal.iSup_add, ENNReal.iSup_add]

theorem structured_cells : Claims.structured_cells := by
  intro E _ _ _ Θ n₀ n₁ J a₀ x₀ a₁ x₁ A cell θc p w h₀ h₁ hcov hθc
  refine iSup_le fun θ => ?_
  obtain ⟨j, hj⟩ := hcov θ
  refine le_trans ?_ (le_iSup _ j)
  have hl := deltafin_lip h₀ h₁ x₀ x₁ p (ContinuousLinearMap.adjoint (A θ) w)
    (ContinuousLinearMap.adjoint (A (θc j)) w)
  rw [← sub_apply, ← map_sub] at hl
  refine (ENNReal.ofReal_le_ofReal hl).trans ?_
  have hD : 0 ≤ Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w) := Real.sqrt_nonneg _
  have hs0 : 0 ≤ smNorm a₀ x₀ p (ContinuousLinearMap.adjoint (A θ - A (θc j)) w) := Real.sqrt_nonneg _
  have hs1 : 0 ≤ smNorm a₁ x₁ p (ContinuousLinearMap.adjoint (A θ - A (θc j)) w) := Real.sqrt_nonneg _
  rw [ENNReal.ofReal_add hD (add_nonneg hs0 hs1), ENNReal.ofReal_add hs0 hs1]
  unfold Lcell
  gcongr
  · exact le_iSup₂ (f := fun θ (_ : θ ∈ cell j) =>
      ENNReal.ofReal (smNorm a₀ x₀ p (ContinuousLinearMap.adjoint (A θ - A (θc j)) w))) θ hj
  · exact le_iSup₂ (f := fun θ (_ : θ ∈ cell j) =>
      ENNReal.ofReal (smNorm a₁ x₁ p (ContinuousLinearMap.adjoint (A θ - A (θc j)) w))) θ hj

end StatFormal.Wave20a

namespace StatFormal.Wave20a

open StatFormal.RobustEquality.Paper2.Seminorm

section Conv
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {n₀ n₁ : ℕ}

lemma smNorm_le {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) (x : Fin n → E) (p u : E) :
    smNorm a x p u ≤ √(∑ i, a i * ‖x i - p‖ ^ 2) * ‖u‖ := by
  unfold smNorm
  rw [show √(∑ i, a i * ‖x i - p‖ ^ 2) * ‖u‖ = √((∑ i, a i * ‖x i - p‖ ^ 2) * ‖u‖ ^ 2) by
    rw [Real.sqrt_mul (Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (sq_nonneg _)),
      Real.sqrt_sq (norm_nonneg u)]]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (ha i)
  have := abs_real_inner_le_norm u (x i - p)
  rw [← sq_abs]
  calc |⟪u, x i - p⟫| ^ 2 ≤ (‖u‖ * ‖x i - p‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    _ = ‖x i - p‖ ^ 2 * ‖u‖ ^ 2 := by ring

/-- The sup over a cell of seminorms `w ↦ q(T_θ w)`, `‖T_θ‖ ≤ C`, is a seminorm. -/
def supSemi {Θ : Type} (q : Seminorm ℝ E) (M : ℝ) (hq : ∀ u, q u ≤ M * ‖u‖) (hM : 0 ≤ M)
    (cell : Set Θ) [Nonempty cell] (T : Θ → E →L[ℝ] E) (C : ℝ) (hT : ∀ θ ∈ cell, ‖T θ‖ ≤ C) :
    Seminorm ℝ E :=
  have hb : ∀ w, BddAbove (range fun θ : cell => q (T θ w)) := fun w =>
    ⟨M * (C * ‖w‖), by
      rintro _ ⟨θ, rfl⟩
      refine (hq _).trans (mul_le_mul_of_nonneg_left ?_ hM)
      exact ((T θ).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hT θ θ.2) (norm_nonneg _))⟩
  Seminorm.of (fun w => ⨆ θ : cell, q (T θ w))
    (fun x y => ciSup_le fun θ => by
      rw [map_add]
      exact (map_add_le_add q _ _).trans (add_le_add (le_ciSup (hb x) θ) (le_ciSup (hb y) θ)))
    (fun a x => by
      simp only [map_smul, map_smul_eq_mul, Real.norm_eq_abs]
      rw [Real.mul_iSup_of_nonneg (abs_nonneg a)])

lemma supSemi_apply {Θ : Type} (q : Seminorm ℝ E) (M : ℝ) (hq : ∀ u, q u ≤ M * ‖u‖) (hM : 0 ≤ M)
    (cell : Set Θ) [Nonempty cell] (T : Θ → E →L[ℝ] E) (C : ℝ) (hT : ∀ θ ∈ cell, ‖T θ‖ ≤ C) (w : E) :
    supSemi q M hq hM cell T C hT w = ⨆ θ : cell, q (T θ w) := rfl

lemma ofReal_supSemi {Θ : Type} (q : Seminorm ℝ E) (M : ℝ) (hq : ∀ u, q u ≤ M * ‖u‖) (hM : 0 ≤ M)
    (cell : Set Θ) [Nonempty cell] (T : Θ → E →L[ℝ] E) (C : ℝ) (hT : ∀ θ ∈ cell, ‖T θ‖ ≤ C) (w : E) :
    ENNReal.ofReal (supSemi q M hq hM cell T C hT w) = ⨆ θ ∈ cell, ENNReal.ofReal (q (T θ w)) := by
  rw [supSemi_apply, iSup_subtype']
  have hb : BddAbove (range fun θ : cell => q (T θ w)) :=
    ⟨M * (C * ‖w‖), by
      rintro _ ⟨θ, rfl⟩
      refine (hq _).trans (mul_le_mul_of_nonneg_left ?_ hM)
      exact ((T θ).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hT θ θ.2) (norm_nonneg _))⟩
  exact ENNReal.ofReal_mono.map_ciSup_of_continuousAt ENNReal.continuous_ofReal.continuousAt hb

lemma convexOn_finite_iSup {J : ℕ} (F : Fin J → E → ℝ) (hF : ∀ j, ConvexOn ℝ univ (F j)) :
    ConvexOn ℝ univ (fun w => ⨆ j, F j w) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  rcases isEmpty_or_nonempty (Fin J) with hJ | hJ
  · simp
  refine ciSup_le fun j => ((hF j).2 (mem_univ x) (mem_univ y) ha hb hab).trans ?_
  simp only [smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (le_ciSup (f := fun j => F j x) (Set.finite_range _).bddAbove j) ha)
    (mul_le_mul_of_nonneg_left (le_ciSup (f := fun j => F j y) (Set.finite_range _).bddAbove j) hb)

lemma deltafin_le_gamNorm {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ} (h₀ : ProbW a₀) (h₁ : ProbW a₁) {γ}
    (hγ : γ ∈ Polytope a₀ a₁) (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (v : E) :
    Deltafin a₀ x₀ a₁ x₁ v ≤ gamNorm γ x₀ x₁ v := by
  have hD : 0 ≤ Deltafin a₀ x₀ a₁ x₁ v := Real.sqrt_nonneg _
  rw [← Real.sqrt_sq hD, deltafin_sq h₀ h₁]
  exact Real.sqrt_le_sqrt (ciInf_le (f := fun g : Polytope a₀ a₁ => tcost x₀ x₁ v g)
    ⟨0, by rintro _ ⟨g, rfl⟩; exact tcost_nonneg g.2 x₀ x₁ v⟩ ⟨γ, hγ⟩)

end Conv

theorem structured_convex : Claims.structured_convex := by
  intro E _ _ _ Θ n₀ n₁ J G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A b cell θc p γ hβ₀ hβ₁ h₀ h₁ hcov hθc ⟨C, hC⟩ hγ
  -- seminorms
  set q₀ : Seminorm ℝ E := wSemi a₀ h₀.1 (fun i => innL (x₀ i - p))
  set q₁ : Seminorm ℝ E := wSemi a₁ h₁.1 (fun i => innL (x₁ i - p))
  set M₀ := √(∑ i, a₀ i * ‖x₀ i - p‖ ^ 2)
  set M₁ := √(∑ i, a₁ i * ‖x₁ i - p‖ ^ 2)
  have hq₀ : ∀ u, q₀ u ≤ M₀ * ‖u‖ := fun u => by rw [← smNorm_eq h₀.1]; exact smNorm_le h₀.1 x₀ p u
  have hq₁ : ∀ u, q₁ u ≤ M₁ * ‖u‖ := fun u => by rw [← smNorm_eq h₁.1]; exact smNorm_le h₁.1 x₁ p u
  set T : Fin J → Θ → E →L[ℝ] E := fun j θ => ContinuousLinearMap.adjoint (A θ - A (θc j))
  have hT : ∀ j, ∀ θ ∈ cell j, ‖T j θ‖ ≤ C := fun j θ hθ => by
    simp only [T, LinearIsometryEquiv.norm_map]; exact hC j θ hθ
  have hne : ∀ j, Nonempty (cell j) := fun j => ⟨⟨θc j, hθc j⟩⟩
  set Ls : Fin J → Seminorm ℝ E := fun j =>
    @supSemi E _ _ Θ q₀ M₀ hq₀ (Real.sqrt_nonneg _) (cell j) (hne j) (T j) C (hT j) +
    @supSemi E _ _ Θ q₁ M₁ hq₁ (Real.sqrt_nonneg _) (cell j) (hne j) (T j) C (hT j)
  have hLs : ∀ j w, ENNReal.ofReal (Ls j w) = Lcell a₀ x₀ a₁ x₁ p A (cell j) (θc j) w := by
    intro j w
    haveI := hne j
    simp only [Ls, Seminorm.coe_add, Pi.add_apply]
    rw [ENNReal.ofReal_add (apply_nonneg _ _) (apply_nonneg _ _), ofReal_supSemi, ofReal_supSemi, Lcell]
    simp only [T, q₀, q₁, ← smNorm_eq h₀.1, ← smNorm_eq h₁.1]
  refine ⟨fun j => ⟨Ls j, hLs j⟩, ?_⟩
  -- the cell bound
  set N₀ : E → ℝ := fun w => √β₀ * ‖ContinuousLinearMap.adjoint (G₀.symm : E →L[ℝ] E) w‖
  set N₁ : E → ℝ := fun w => √β₁ * ‖ContinuousLinearMap.adjoint (G₁.symm : E →L[ℝ] E) w‖
  set g : Fin J → Seminorm ℝ E := fun j =>
    (wSemi (fun q : Fin n₀ × Fin n₁ => γ j q.1 q.2) (fun q => (hγ j).1 q.1 q.2)
      (fun q => innL (x₀ q.1 - x₁ q.2))).comp (ContinuousLinearMap.adjoint (A (θc j))).toLinearMap
  set nS : (E →L[ℝ] E) → Seminorm ℝ E := fun B => (normSeminorm ℝ E).comp B.toLinearMap
  set Q : Fin J → Seminorm ℝ E := fun j => g j + Ls j +
    nS (√β₀ • ContinuousLinearMap.adjoint (G₀.symm : E →L[ℝ] E)) +
    nS (√β₁ • ContinuousLinearMap.adjoint (G₁.symm : E →L[ℝ] E))
  have hQ : ∀ j w, Q j w = gamNorm (γ j) x₀ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w) + Ls j w + N₀ w + N₁ w := by
    intro j w
    show g j w + Ls j w + ‖(√β₀ • ContinuousLinearMap.adjoint (G₀.symm : E →L[ℝ] E)) w‖ +
      ‖(√β₁ • ContinuousLinearMap.adjoint (G₁.symm : E →L[ℝ] E)) w‖ = _
    rw [show g j w = gamNorm (γ j) x₀ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w) from
      (gamNorm_eq (hγ j).1 x₀ x₁ _).symm]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _)]
  set Cb : E → ℝ := fun w => ⨆ j, (Q j w) ^ 2
  refine ⟨Cb, ?_, ?_, ?_⟩
  · exact convexOn_finite_iSup _ fun j => (Q j).convexOn.pow (fun w _ => apply_nonneg _ _) 2
  · intro w
    rcases isEmpty_or_nonempty (Fin J) with hJ | hJ
    · simp [Cb, Real.iSup_of_isEmpty]
    rw [show ENNReal.ofReal (Cb w) = ⨆ j, ENNReal.ofReal ((Q j w) ^ 2) from
      ENNReal.ofReal_mono.map_ciSup_of_continuousAt ENNReal.continuous_ofReal.continuousAt
        (Set.finite_range _).bddAbove]
    refine iSup_congr fun j => ?_
    rw [ENNReal.ofReal_pow (apply_nonneg _ _), hQ]
    have h1 : 0 ≤ gamNorm (γ j) x₀ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w) := Real.sqrt_nonneg _
    have h2 : 0 ≤ Ls j w := apply_nonneg _ _
    have h3 : 0 ≤ N₀ w := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have h4 : 0 ≤ N₁ w := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    rw [ENNReal.ofReal_add (by positivity) h4, ENNReal.ofReal_add (by positivity) h3,
      ENNReal.ofReal_add h1 h2, hLs]
  · intro w
    rcases isEmpty_or_nonempty Θ with hΘ | hΘ
    · simp [certStruct]
    have hJ : Nonempty (Fin J) := ⟨(hcov (Classical.arbitrary Θ)).choose⟩
    rw [structured_value E Θ n₀ n₁ G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A b w hβ₀ hβ₁ h₀ h₁]
    have hc := structured_cells E Θ n₀ n₁ J a₀ x₀ a₁ x₁ A cell θc p w h₀ h₁ hcov hθc
    calc ((⨆ θ, ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A θ) w))) +
          ENNReal.ofReal (N₀ w) + ENNReal.ofReal (N₁ w)) ^ 2
        ≤ ((⨆ j, (ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w)) +
            Lcell a₀ x₀ a₁ x₁ p A (cell j) (θc j) w)) + ENNReal.ofReal (N₀ w) + ENNReal.ofReal (N₁ w)) ^ 2 := by
          gcongr
      _ = ⨆ j, (ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w)) +
            Lcell a₀ x₀ a₁ x₁ p A (cell j) (θc j) w + ENNReal.ofReal (N₀ w) + ENNReal.ofReal (N₁ w)) ^ 2 := by
          rw [ENNReal.iSup_add, ENNReal.iSup_add, iSup_sq]
      _ ≤ ⨆ j, ENNReal.ofReal ((Q j w) ^ 2) := by
          refine iSup_mono fun j => ?_
          rw [ENNReal.ofReal_pow (apply_nonneg _ _), hQ]
          have h1 : 0 ≤ gamNorm (γ j) x₀ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w) := Real.sqrt_nonneg _
          have h2 : 0 ≤ Ls j w := apply_nonneg _ _
          have h3 : 0 ≤ N₀ w := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
          have h4 : 0 ≤ N₁ w := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
          rw [ENNReal.ofReal_add (by positivity) h4, ENNReal.ofReal_add (by positivity) h3,
            ENNReal.ofReal_add h1 h2, hLs]
          gcongr
          exact deltafin_le_gamNorm h₀ h₁ (hγ j) x₀ x₁ _
      _ = ENNReal.ofReal (Cb w) :=
          (ENNReal.ofReal_mono.map_ciSup_of_continuousAt ENNReal.continuous_ofReal.continuousAt
            (Set.finite_range _).bddAbove).symm

end StatFormal.Wave20a
