import StatFormal.Archive.WaveP1d.Statements
import Mathlib.Basic.Real.Pointwise

/-!
# Route: robust equality paper 2 `prop:direction`, the disparity parenthesis and the `ρ` paragraph (untrusted)

* `Δ(tw) = |t|Δ(w)`: the coupling objective scales by `t²` and `√(t²X) = |t|√X`; seminorms are absolutely homogeneous.
* `ρ`: on the sphere `Δ_min + N̲ ≤ G(u)` and `G(u₀) ≤ Δ(u₀) + N̄`.
-/

set_option linter.style.longLine false

noncomputable section
open Finset

namespace StatFormal.WaveP1d

namespace RouteDirection

open StatFormal.RobustEquality.Paper2.Seminorm (Deltafin)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma deltafin_smul {n₀ n₁ : ℕ} (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E)
    (t : ℝ) (w : E) : Deltafin a₀ x₀ a₁ x₁ (t • w) = |t| * Deltafin a₀ x₀ a₁ x₁ w := by
  unfold Deltafin
  have : ∀ γ : Fin n₀ → Fin n₁ → ℝ, (∑ i, ∑ j, γ i j * (inner ℝ (t • w) (x₀ i - x₁ j)) ^ 2) =
      t ^ 2 * ∑ i, ∑ j, γ i j * (inner ℝ w (x₀ i - x₁ j)) ^ 2 := by
    intro γ
    simp only [real_inner_smul_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [this]
  rw [← Real.mul_iInf_of_nonneg (sq_nonneg t), Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

lemma deltafin_nonneg {n₀ n₁ : ℕ} (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E)
    (w : E) : 0 ≤ Deltafin a₀ x₀ a₁ x₁ w := Real.sqrt_nonneg _

end RouteDirection

open RouteDirection StatFormal.RobustEquality.Paper2.Seminorm

theorem direction_cert_homog : Claims.direction_cert_homog := by
  intro E _ _ n₀ n₁ a₀ x₀ a₁ x₁ N₀ N₁
  refine ⟨fun w => by have := deltafin_nonneg a₀ x₀ a₁ x₁ w; positivity, fun t w => ?_⟩
  rw [deltafin_smul, map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs]
  have : |t| * Deltafin a₀ x₀ a₁ x₁ w + |t| * N₀ w + |t| * N₁ w =
      |t| * (Deltafin a₀ x₀ a₁ x₁ w + N₀ w + N₁ w) := by ring
  rw [this, mul_pow, sq_abs]



theorem direction_rho : Claims.direction_rho := by
  intro E _ _ n₀ n₁ a₀ x₀ a₁ x₁ N₀ N₁ u₀ Nbar Nund Dmin Gsqmin hu₀ hNbar hNund hDmin hG hpos
  -- pointwise bounds on the sphere
  have hlow : ∀ u : E, ‖u‖ = 1 → Dmin + Nund ≤ Deltafin a₀ x₀ a₁ x₁ u + N₀ u + N₁ u := by
    intro u hu
    have h1 := hDmin.1 ⟨u, hu, rfl⟩
    have h2 := hNund.1 ⟨u, hu, rfl⟩
    linarith
  have hsq : (Dmin + Nund) ^ 2 ≤ Gsqmin := by
    refine hG.2 ?_
    rintro r ⟨u, hu, rfl⟩
    exact pow_le_pow_left₀ hpos.le (hlow u hu) 2
  have hGpos : 0 < Gsqmin := lt_of_lt_of_le (by positivity) hsq
  have hup : Deltafin a₀ x₀ a₁ x₁ u₀ + N₀ u₀ + N₁ u₀ ≤ Deltafin a₀ x₀ a₁ x₁ u₀ + Nbar := by
    have := hNbar.1 ⟨u₀, hu₀, rfl⟩
    linarith
  have hG0 : 0 < Deltafin a₀ x₀ a₁ x₁ u₀ + N₀ u₀ + N₁ u₀ := lt_of_lt_of_le hpos (hlow u₀ hu₀)
  refine ⟨hGpos, ?_⟩
  rw [div_pow]
  calc (Deltafin a₀ x₀ a₁ x₁ u₀ + N₀ u₀ + N₁ u₀) ^ 2 / Gsqmin
      ≤ (Deltafin a₀ x₀ a₁ x₁ u₀ + Nbar) ^ 2 / Gsqmin := by
        gcongr
    _ ≤ (Deltafin a₀ x₀ a₁ x₁ u₀ + Nbar) ^ 2 / (Dmin + Nund) ^ 2 := by
        gcongr

theorem direction_rho_iso : Claims.direction_rho_iso := by
  intro E _ _ n₀ n₁ a₀ x₀ a₁ x₁ N₀ N₁ u₀ c₀ c₁ Dmin Gsqmin hu₀ hN₀ hN₁ hc hDmin hG
  have hset : {r | ∃ u : E, ‖u‖ = 1 ∧ r = N₀ u + N₁ u} = {c₀ + c₁} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, hu, rfl⟩; rw [hN₀, hN₁, hu]; ring
    · rintro rfl; exact ⟨u₀, hu₀, by rw [hN₀, hN₁, hu₀]; ring⟩
  have hD0 : 0 ≤ Dmin := hDmin.2 (by rintro r ⟨u, _, rfl⟩; exact deltafin_nonneg a₀ x₀ a₁ x₁ u)
  have hmain := direction_rho E n₀ n₁ a₀ x₀ a₁ x₁ N₀ N₁ u₀ (c₀ + c₁) (c₀ + c₁) Dmin Gsqmin hu₀
    (by rw [hset]; exact isLUB_singleton) (by rw [hset]; exact isGLB_singleton) hDmin hG (by linarith)
  refine ⟨by rw [hset]; exact isGreatest_singleton, by rw [hset]; exact isLeast_singleton, hmain.2, ?_⟩
  refine hmain.2.trans ?_
  have hD := deltafin_nonneg a₀ x₀ a₁ x₁ u₀
  have h1 : (Deltafin a₀ x₀ a₁ x₁ u₀ + (c₀ + c₁)) / (Dmin + (c₀ + c₁)) ≤
      1 + Deltafin a₀ x₀ a₁ x₁ u₀ / (c₀ + c₁) := by
    rw [div_le_iff₀ (by linarith)]
    have : 1 + Deltafin a₀ x₀ a₁ x₁ u₀ / (c₀ + c₁) = (c₀ + c₁ + Deltafin a₀ x₀ a₁ x₁ u₀) / (c₀ + c₁) := by
      field_simp
    rw [this, div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith
  have h0 : 0 ≤ (Deltafin a₀ x₀ a₁ x₁ u₀ + (c₀ + c₁)) / (Dmin + (c₀ + c₁)) := by
    apply div_nonneg <;> linarith
  exact pow_le_pow_left₀ h0 h1 2

end StatFormal.WaveP1d
