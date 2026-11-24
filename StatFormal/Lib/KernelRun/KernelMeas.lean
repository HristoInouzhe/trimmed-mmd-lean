import StatFormal.Wave31tr.Statements

/-!
# Kernel-level QP value, witness and own-term values: joint measurability (library)

Library component (untrusted). A kernel family `kf : Θ → 𝒳 → 𝒳 → ℝ` on a measurable parameter space, jointly measurable in
`(θ, x, x′)`; no positive definiteness and no feature map. For maps `θ : Ω → Θ`, `x : Ω → 𝒳ⁿ`, `y : Ω → 𝒳ᵐ`, `w : Ω → ℝⁿ`,
`v : Ω → ℝᵐ` measurable in a parameter `ω` (the sample, or the sample and an evaluation point):

* `measurable_kf_comp`: `ω ↦ kf (θ ω) (a ω) (b ω)` is measurable (a composition);
* `measurable_kqpVal`: the kernel-level value `Wave31tr.kqpVal` (a square root of `max 0` of a finite sum) is measurable;
* `measurable_kwit`: the kernel-level witness `Wave31tr.kwit` evaluated at a measurable point is measurable;
* `measurable_kownX`, `measurable_kownY`: the own-term values (Algorithm S1 line 9) are measurable as maps into `ℝⁿ`, `ℝᵐ`.

This is the kernel analogue of `StatFormal.PaperRun.measurable_qpVal`, `measurable_witness_apply`, `measurable_ownX`,
`measurable_ownY` (chunk A1, `Lib/PaperRun/QPMeas.lean`), with `kf θ x x′` in place of `⟪φ x, φ x′⟫`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory

namespace StatFormal.KernelRun

open StatFormal.Wave31tr

variable {𝒳 Θ Ω : Type*} [MeasurableSpace 𝒳] [MeasurableSpace Θ] [MeasurableSpace Ω] {kf : Θ → 𝒳 → 𝒳 → ℝ}

/-- A jointly measurable kernel family composed with measurable maps is measurable. -/
theorem measurable_kf_comp (hkf : Measurable fun p : Θ × 𝒳 × 𝒳 => kf p.1 p.2.1 p.2.2) {θ : Ω → Θ} {a b : Ω → 𝒳}
    (hθ : Measurable θ) (ha : Measurable a) (hb : Measurable b) : Measurable fun ω => kf (θ ω) (a ω) (b ω) :=
  hkf.comp (hθ.prodMk (ha.prodMk hb))

variable (hkf : Measurable fun p : Θ × 𝒳 × 𝒳 => kf p.1 p.2.1 p.2.2) {n m : ℕ} {θ : Ω → Θ} {x : Ω → Fin n → 𝒳}
  {y : Ω → Fin m → 𝒳} {w : Ω → Fin n → ℝ} {v : Ω → Fin m → ℝ}
include hkf

/-- The kernel-level value `D̂ = √(max 0 (wᵀK_XXw − 2wᵀK_XYv + vᵀK_YYv))` is measurable. -/
theorem measurable_kqpVal (hθ : Measurable θ) (hx : Measurable x) (hy : Measurable y) (hw : Measurable w)
    (hv : Measurable v) : Measurable fun ω => kqpVal (kf (θ ω)) (x ω) (y ω) (w ω) (v ω) := by
  have hxi : ∀ i, Measurable fun ω => x ω i := fun i => (measurable_pi_apply i).comp hx
  have hyj : ∀ j, Measurable fun ω => y ω j := fun j => (measurable_pi_apply j).comp hy
  have hwi : ∀ i, Measurable fun ω => w ω i := fun i => (measurable_pi_apply i).comp hw
  have hvj : ∀ j, Measurable fun ω => v ω j := fun j => (measurable_pi_apply j).comp hv
  unfold kqpVal
  refine (measurable_const.max ?_).sqrt
  refine ((Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun i' _ => ?_).sub
    (measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_))).add
    (Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun j' _ => ?_)
  · exact ((hwi i).mul (hwi i')).mul (measurable_kf_comp hkf hθ (hxi i) (hxi i'))
  · exact ((hwi i).mul (hvj j)).mul (measurable_kf_comp hkf hθ (hxi i) (hyj j))
  · exact ((hvj j).mul (hvj j')).mul (measurable_kf_comp hkf hθ (hyj j) (hyj j'))

/-- The kernel-level witness `f̂(z) = D̂⁻¹(Σ w_i k(x_i,z) − Σ v_j k(y_j,z))` at a measurable point is measurable. -/
theorem measurable_kwit (hθ : Measurable θ) (hx : Measurable x) (hy : Measurable y) (hw : Measurable w)
    (hv : Measurable v) {z : Ω → 𝒳} (hz : Measurable z) :
    Measurable fun ω => kwit (kf (θ ω)) (x ω) (y ω) (w ω) (v ω) (z ω) := by
  have hxi : ∀ i, Measurable fun ω => x ω i := fun i => (measurable_pi_apply i).comp hx
  have hyj : ∀ j, Measurable fun ω => y ω j := fun j => (measurable_pi_apply j).comp hy
  have hwi : ∀ i, Measurable fun ω => w ω i := fun i => (measurable_pi_apply i).comp hw
  have hvj : ∀ j, Measurable fun ω => v ω j := fun j => (measurable_pi_apply j).comp hv
  unfold kwit
  exact (measurable_kqpVal hkf hθ hx hy hw hv).inv.mul
    ((Finset.measurable_sum _ fun i _ => (hwi i).mul (measurable_kf_comp hkf hθ (hxi i) hz)).sub
      (Finset.measurable_sum _ fun j _ => (hvj j).mul (measurable_kf_comp hkf hθ (hyj j) hz)))

/-- The own-term values at the `X`'s, `h̃_i = f̂(x_i) − w_i k(x_i,x_i)/D̂`, are measurable. -/
theorem measurable_kownX (hθ : Measurable θ) (hx : Measurable x) (hy : Measurable y) (hw : Measurable w)
    (hv : Measurable v) : Measurable fun ω => kownX (kf (θ ω)) (x ω) (y ω) (w ω) (v ω) := by
  refine Measurable.of_eval fun i => ?_
  have hxi : Measurable fun ω => x ω i := (measurable_pi_apply i).comp hx
  unfold kownX
  exact (measurable_kwit hkf hθ hx hy hw hv hxi).sub
    ((((measurable_pi_apply i).comp hw).mul (measurable_kf_comp hkf hθ hxi hxi)).div
      (measurable_kqpVal hkf hθ hx hy hw hv))

/-- The own-term values at the `Y`'s, `h̃′_j = f̂(y_j) + v_j k(y_j,y_j)/D̂`, are measurable. -/
theorem measurable_kownY (hθ : Measurable θ) (hx : Measurable x) (hy : Measurable y) (hw : Measurable w)
    (hv : Measurable v) : Measurable fun ω => kownY (kf (θ ω)) (x ω) (y ω) (w ω) (v ω) := by
  refine Measurable.of_eval fun j => ?_
  have hyj : Measurable fun ω => y ω j := (measurable_pi_apply j).comp hy
  unfold kownY
  exact (measurable_kwit hkf hθ hx hy hw hv hyj).add
    ((((measurable_pi_apply j).comp hv).mul (measurable_kf_comp hkf hθ hyj hyj)).div
      (measurable_kqpVal hkf hθ hx hy hw hv))

end StatFormal.KernelRun
