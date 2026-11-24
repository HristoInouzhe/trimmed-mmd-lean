import StatFormal.Lib.LaplaceH1.Core
import StatFormal.Lib.LaplaceH1.Bounds

/-!
# The `H¹` form of the Laplace RKHS on `ℝ`, for any feature map (library, untrusted)

Let `H` be a real Hilbert space and `φ : ℝ → H` with `⟪φ x, φ y⟫ = e^{−|x−y|/σ}`, `σ > 0`. For `g ∈ H` and `f = ⟪g, φ ·⟫`:

* `rep_h1`: `f` is absolutely continuous on every interval, `f, f′ ∈ L²`, `∫ (f² + σ² f′²) ≤ 2σ ‖g‖²`, with equality when `g` lies
  in the closed span of `φ(ℝ)` — the RKHS norm of the Laplace kernel is the `H¹` norm `(1/(2σ)) ∫ (f² + σ² f′²)`.
  Proof: the Gram transfer (`TIKernel.gram_rep_le`, `TIKernel.gram_rep_eq`) to the explicit feature `ψ_σ` of `LaplaceH1.Feature`,
  where the identity is `LaplaceH1.witL_h1`;
* `rep_abs_le`: `|f| ≤ ‖g‖`; `rep_tendsto`: `f → 0` along `cocompact ℝ`;
* `rep_integral_abs_deriv_le`, `rep_eVariationOn_le`: `∫_a^b |f′| ≤ √(2(b − a)/σ) ‖g‖` and the same bound for the variation
  of `f` on `[a, b]` (`eq:laphone`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.LaplaceH1

open StatFormal.TIKernel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {σ : ℝ} {φ : ℝ → H}

lemma gram_lap (hσ : 0 < σ) (hφ : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) :
    ∀ x y, ⟪φ x, φ y⟫_ℝ = ⟪lapFeat σ x, lapFeat σ y⟫_ℝ := fun x y => by rw [hφ, lapFeat_gram hσ]

/-- Unit norms: `‖φ x‖ = 1`. -/
lemma norm_phi_eq_one (hφ : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) (x : ℝ) : ‖φ x‖ = 1 := by
  rw [norm_eq_sqrt_real_inner, hφ]; simp

/-- `|⟪g, φ x⟫| ≤ ‖g‖`. -/
lemma rep_abs_le (hφ : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) (g : H) (x : ℝ) : |⟪g, φ x⟫_ℝ| ≤ ‖g‖ := by
  have h := abs_real_inner_le_norm g (φ x)
  rwa [norm_phi_eq_one hφ, mul_one] at h

variable [CompleteSpace H]

/-- **The `H¹` form of the Laplace RKHS**: `f = ⟪g, φ ·⟫` is locally absolutely continuous, `f, f′ ∈ L²` and
`∫ (f² + σ² f′²) ≤ 2σ‖g‖²`, with equality for `g` in the closed span of `φ(ℝ)`. -/
theorem rep_h1 (hσ : 0 < σ) (hφ : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) (g : H) :
    (∀ a b, AbsolutelyContinuousOnInterval (fun x => ⟪g, φ x⟫_ℝ) a b) ∧ MemLp (fun x => ⟪g, φ x⟫_ℝ) 2 volume ∧
      MemLp (deriv fun x => ⟪g, φ x⟫_ℝ) 2 volume ∧
      ∫ x, ((⟪g, φ x⟫_ℝ) ^ 2 + σ ^ 2 * deriv (fun x => ⟪g, φ x⟫_ℝ) x ^ 2) ≤ 2 * σ * ‖g‖ ^ 2 ∧
      (g ∈ spanCl φ →
        ∫ x, ((⟪g, φ x⟫_ℝ) ^ 2 + σ ^ 2 * deriv (fun x => ⟪g, φ x⟫_ℝ) x ^ 2) = 2 * σ * ‖g‖ ^ 2) := by
  have hG := gram_lap hσ hφ
  have key : ∀ (f : ℝ → ℝ) (v : Lp ℝ 2 (volume : Measure ℝ)), f = witL σ v →
      (∀ a b, AbsolutelyContinuousOnInterval f a b) ∧ MemLp f 2 volume ∧ MemLp (deriv f) 2 volume ∧
        ∫ x, (f x ^ 2 + σ ^ 2 * deriv f x ^ 2) = 2 * σ * ‖v‖ ^ 2 := by
    rintro f v rfl; exact witL_h1 hσ v
  obtain ⟨u, hu, hrep⟩ := gram_rep_le hG g
  obtain ⟨h1, h2, h3, h4⟩ := key (fun x => ⟪g, φ x⟫_ℝ) u (funext fun x => (hrep x).symm)
  have hu2 : 2 * σ * ‖u‖ ^ 2 ≤ 2 * σ * ‖g‖ ^ 2 := by
    have : ‖u‖ ^ 2 ≤ ‖g‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
    nlinarith
  refine ⟨h1, h2, h3, h4.le.trans hu2, fun hg => ?_⟩
  obtain ⟨hn, hr⟩ := gram_rep_eq hG ⟨g, hg⟩
  have h5 := (key (fun x => ⟪g, φ x⟫_ℝ) (gramIso hG ⟨g, hg⟩) (funext fun x => (hr x).symm)).2.2.2
  rw [hn] at h5
  exact h5

/-- `f = ⟪g, φ ·⟫ → 0` along `cocompact ℝ` (Wave31tp L26). -/
lemma rep_tendsto (hσ : 0 < σ) (hφ : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) (g : H) :
    Tendsto (fun x => ⟪g, φ x⟫_ℝ) (cocompact ℝ) (𝓝 0) := by
  have hφ' : ∀ x y, ⟪φ x, φ y⟫_ℝ = (fun z : ℝ => Real.exp (-|z| / σ)) (x - y) := hφ
  have h := StatFormal.RKHSReg.rkhs_vanish_facts hφ' (laplaceProfile_continuous σ) (laplaceProfile_integrable hσ) g
  rwa [StatFormal.RKHSReg.comap_norm_atTop_eq_cocompact] at h

/-- `∫ f′² ≤ (2/σ)‖g‖²`. -/
lemma rep_integral_deriv_sq_le (hσ : 0 < σ) (hφ : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) (g : H) :
    ∫ x, deriv (fun x => ⟪g, φ x⟫_ℝ) x ^ 2 ≤ 2 * ‖g‖ ^ 2 / σ := by
  obtain ⟨-, h2, h3, h4, -⟩ := rep_h1 hσ hφ g
  rw [integral_add h2.integrable_sq (h3.integrable_sq.const_mul _), integral_const_mul] at h4
  have hf2 : 0 ≤ ∫ x, (⟪g, φ x⟫_ℝ) ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [le_div_iff₀ hσ]
  nlinarith

/-- `eq:laphone`: `∫_a^b |f′| ≤ √(2(b − a)/σ) ‖g‖`. -/
theorem rep_integral_abs_deriv_le (hσ : 0 < σ) (hφ : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) (g : H) {a b : ℝ}
    (hab : a ≤ b) : ∫ x in a..b, |deriv (fun x => ⟪g, φ x⟫_ℝ) x| ≤ √(2 * (b - a) / σ) * ‖g‖ := by
  obtain ⟨-, -, h3, -, -⟩ := rep_h1 hσ hφ g
  refine (integral_abs_le_sqrt h3 hab).trans ?_
  have hle := rep_integral_deriv_sq_le hσ hφ g
  calc √((b - a) * ∫ x, deriv (fun x => ⟪g, φ x⟫_ℝ) x ^ 2) ≤ √((b - a) * (2 * ‖g‖ ^ 2 / σ)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle (by linarith))
    _ = √(2 * (b - a) / σ) * ‖g‖ := by
        rw [show (b - a) * (2 * ‖g‖ ^ 2 / σ) = 2 * (b - a) / σ * ‖g‖ ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- The variation of `f` on `[a, b]` is at most `√(2(b − a)/σ) ‖g‖`. -/
theorem rep_eVariationOn_le (hσ : 0 < σ) (hφ : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ)) (g : H) {a b : ℝ}
    (hab : a ≤ b) :
    eVariationOn (fun x => ⟪g, φ x⟫_ℝ) (Icc a b) ≤ ENNReal.ofReal (√(2 * (b - a) / σ) * ‖g‖) :=
  eVariationOn_le_of_ac hab ((rep_h1 hσ hφ g).1 a b) (rep_integral_abs_deriv_le hσ hφ g hab)

end StatFormal.LaplaceH1
