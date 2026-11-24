import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The real line as `EuclideanSpace ℝ (Fin 1)` (library, untrusted)

* `lineEmb x = x • e₀` (`e₀ = EuclideanSpace.single 0 1`): `(lineEmb x) 0 = x`, `‖lineEmb x − lineEmb y‖ = |x − y|`,
  `‖v − w‖² = (v 0 − w 0)²` on `ℝ¹`.
* `contDiff_comp_lineEmb`, `tendsto_comp_lineEmb_atTop`, `tendsto_comp_lineEmb_atBot`: a `C^k` function on `ℝ¹` tending to `0` as
  `‖v‖ → ∞` restricts to a `C^k` function on `ℝ` tending to `0` at `±∞`.
* `gauss_gram_line`: a feature map `φ : ℝ → ℋ` with Gram function `exp(−(x−y)²/(2σ²))` gives `ψ v = φ (v 0)` on `ℝ¹` with Gram
  function `exp(−‖v−w‖²/(2σ²))`, and `φ = ψ ∘ lineEmb`.
-/

noncomputable section
open Filter Topology Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.KernelFacts

/-- The embedding `x ↦ x • e₀` of `ℝ` into `ℝ¹ = EuclideanSpace ℝ (Fin 1)`. -/
def lineEmb (x : ℝ) : EuclideanSpace ℝ (Fin 1) := x • EuclideanSpace.single 0 1

@[simp] lemma lineEmb_apply (x : ℝ) : lineEmb x 0 = x := by simp [lineEmb]

lemma norm_lineEmb (x : ℝ) : ‖lineEmb x‖ = |x| := by
  simp [lineEmb, norm_smul]

/-- On `ℝ¹`, `‖v − w‖² = (v 0 − w 0)²`. -/
lemma norm_sub_sq_fin1 (v w : EuclideanSpace ℝ (Fin 1)) : ‖v - w‖ ^ 2 = (v 0 - w 0) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs]
  rfl

lemma contDiff_lineEmb {k : ℕ∞} : ContDiff ℝ k lineEmb := contDiff_id.smul contDiff_const

/-- A `C^k` function on `ℝ¹` restricts along `lineEmb` to a `C^k` function on `ℝ`. -/
lemma contDiff_comp_lineEmb {k : ℕ∞} {F : EuclideanSpace ℝ (Fin 1) → ℝ} (hF : ContDiff ℝ k F) :
    ContDiff ℝ k (F ∘ lineEmb) := hF.comp contDiff_lineEmb

lemma tendsto_lineEmb_atTop : Tendsto lineEmb atTop (comap (fun v => ‖v‖) atTop) := by
  rw [tendsto_comap_iff]
  have : (fun v : EuclideanSpace ℝ (Fin 1) => ‖v‖) ∘ lineEmb = fun x => |x| := funext norm_lineEmb
  rw [this]; exact tendsto_abs_atTop_atTop

lemma tendsto_lineEmb_atBot : Tendsto lineEmb atBot (comap (fun v => ‖v‖) atTop) := by
  rw [tendsto_comap_iff]
  have : (fun v : EuclideanSpace ℝ (Fin 1) => ‖v‖) ∘ lineEmb = fun x => |x| := funext norm_lineEmb
  rw [this]; exact tendsto_abs_atBot_atTop

/-- Decay as `‖v‖ → ∞` on `ℝ¹` gives decay at `+∞` along `lineEmb`. -/
lemma tendsto_comp_lineEmb_atTop {F : EuclideanSpace ℝ (Fin 1) → ℝ} {l : Filter ℝ}
    (hF : Tendsto F (comap (fun v => ‖v‖) atTop) l) : Tendsto (F ∘ lineEmb) atTop l :=
  hF.comp tendsto_lineEmb_atTop

/-- Decay as `‖v‖ → ∞` on `ℝ¹` gives decay at `−∞` along `lineEmb`. -/
lemma tendsto_comp_lineEmb_atBot {F : EuclideanSpace ℝ (Fin 1) → ℝ} {l : Filter ℝ}
    (hF : Tendsto F (comap (fun v => ‖v‖) atTop) l) : Tendsto (F ∘ lineEmb) atBot l :=
  hF.comp tendsto_lineEmb_atBot

/-- The Gaussian Gram function on `ℝ` transported to `ℝ¹`: `ψ v = φ (v 0)` has `⟪ψ v, ψ w⟫ = exp(−‖v−w‖²/(2σ²))`. -/
lemma gauss_gram_line {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {σ : ℝ} {φ : ℝ → H}
    (hk : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) (v w : EuclideanSpace ℝ (Fin 1)) :
    ⟪φ (v 0), φ (w 0)⟫_ℝ = Real.exp (-‖v - w‖ ^ 2 / (2 * σ ^ 2)) := by
  rw [hk, norm_sub_sq_fin1]

end StatFormal.KernelFacts
