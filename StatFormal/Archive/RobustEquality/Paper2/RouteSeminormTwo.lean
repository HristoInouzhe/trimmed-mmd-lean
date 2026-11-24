import StatFormal.Archive.RobustEquality.Paper2.RouteSeminorm2

/-!
# Route for paper2 `thm:seminorm` (iii) with two references (one per group)

`RouteSeminorm2.inf_Fbar`/`G_homog` use one reference and one centre size for both groups; here each
group `s` has its own centre `(a_s, x_s)` on `n_s` points, its own finite reference `(m_s, y_s)` on
`q_s` atoms and its own budget `r_s` (the regularisation `ε` is common).
* `inf_Fbar2`: `IsGLB {(Δ + √T₀(λ₀) + √T₁(λ₁))² | λ₀, λ₁ > 0} ((Δ + N₀ + N₁)²)`;
* `G_homog2`: `G = Δ + N₀ + N₁` is positively homogeneous of degree one.
-/

noncomputable section
open Finset Real

namespace StatFormal.RobustEquality.Paper2.Route

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ε : ℝ} {n₀ n₁ q₀ q₁ : ℕ} {r₀ r₁ : ℝ} {a₀ : Fin n₀ → ℝ} {x₀ : Fin n₀ → E}
  {a₁ : Fin n₁ → ℝ} {x₁ : Fin n₁ → E} {m₀ : Fin q₀ → ℝ} {y₀ : Fin q₀ → E}
  {m₁ : Fin q₁ → ℝ} {y₁ : Fin q₁ → E}

/-- **(iii)**, two references: `inf_{λ₀,λ₁} F̄ = G²` with `G = Δ + N₀ + N₁`. -/
theorem inf_Fbar2 (h₀ : Hyp ε a₀ m₀) (h₁ : Hyp ε a₁ m₁) (hF₀ : Feasible ε r₀ a₀ x₀ m₀ y₀)
    (hF₁ : Feasible ε r₁ a₁ x₁ m₁ y₁) (w : E) :
    IsGLB {v | ∃ l₀ l₁ : ℝ, 0 < l₀ ∧ 0 < l₁ ∧ v = (Deltafin a₀ x₀ a₁ x₁ w +
        √(Tfin ε r₀ a₀ x₀ m₀ y₀ w l₀) + √(Tfin ε r₁ a₁ x₁ m₁ y₁ w l₁)) ^ 2}
      ((Deltafin a₀ x₀ a₁ x₁ w + √(Nsq ε r₀ a₀ x₀ m₀ y₀ w) + √(Nsq ε r₁ a₁ x₁ m₁ y₁ w)) ^ 2) :=
  isGLB_sq_sum (Deltafin_nonneg _ _ _ _ w) _ _ (fun _ hl => Tfin_nonneg h₀ hF₀ w hl)
    (fun _ hl => Tfin_nonneg h₁ hF₁ w hl)

/-- **(iii)**, two references: `G` is positively homogeneous of degree one. -/
theorem G_homog2 (h₀ : Hyp ε a₀ m₀) (h₁ : Hyp ε a₁ m₁) (hF₀ : Feasible ε r₀ a₀ x₀ m₀ y₀)
    (hF₁ : Feasible ε r₁ a₁ x₁ m₁ y₁) (w : E) {t : ℝ} (ht : 0 < t) :
    Deltafin a₀ x₀ a₁ x₁ (t • w) + √(Nsq ε r₀ a₀ x₀ m₀ y₀ (t • w)) +
        √(Nsq ε r₁ a₁ x₁ m₁ y₁ (t • w)) =
      t * (Deltafin a₀ x₀ a₁ x₁ w + √(Nsq ε r₀ a₀ x₀ m₀ y₀ w) + √(Nsq ε r₁ a₁ x₁ m₁ y₁ w)) := by
  rw [Deltafin_homog _ _ _ _ _ ht, Nsq_homog h₀ hF₀ w ht, Nsq_homog h₁ hF₁ w ht,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht.le]
  ring

end StatFormal.RobustEquality.Paper2.Route
