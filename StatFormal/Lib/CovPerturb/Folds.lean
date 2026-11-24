import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import StatFormal.Lib.CovPerturb.LLN

/-!
# Frame errors of estimated eigenbases: almost surely and for arbitrary basis folds (untrusted library)

* `sq_frame_le`: `‖η ê_k − e_k‖² ≤ 8‖Ĝ − G‖²/s²` (Weyl + Bosq) for ordered complete eigenbases.
* `map_prefix_eq_pi`: the first `n` terms of an i.i.d. sequence have law `P^{⊗n}`.
* `tendsto_pi_betaB`: `P^{⊗n}{z : ε < C βₙ(z)²} → 0` — the measurable dominant of the covariance error tends to `0`
  in probability under the product law (through the strong law on `P^{⊗ℕ}`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped RealInnerProductSpace ENNReal

namespace StatFormal.CovPerturb

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Eigenvector perturbation, squared.** -/
theorem sq_frame_le {G Gh : H →L[ℝ] H} {e eh : ℕ → H} {lam mu : ℕ → ℝ}
    (he : Orthonormal ℝ e) (hesp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure)
    (hG : ∀ i, G (e i) = lam i • e i) (hlam : Antitone lam)
    (heh : Orthonormal ℝ eh) (hehsp : ⊤ ≤ (Submodule.span ℝ (Set.range eh)).topologicalClosure)
    (hGh : ∀ j, Gh (eh j) = mu j • eh j) (hmu : Antitone mu) {k : ℕ} {s : ℝ} (hs : 0 < s)
    (hsep : ∀ j, j ≠ k → s ≤ |lam j - lam k|) {η : ℝ} (hη : η = 1 ∨ η = -1)
    (hηc : η * ⟪eh k, e k⟫ = |⟪eh k, e k⟫|) :
    ‖η • eh k - e k‖ ^ 2 ≤ 8 * ‖Gh - G‖ ^ 2 / s ^ 2 := by
  have h1 := norm_sign_sub_sq_le (he.1 k) (heh.1 k) hη hηc
  have h2 := one_sub_sq_le_bosq he hesp hG hlam heh hehsp hGh hmu hs hsep
  calc ‖η • eh k - e k‖ ^ 2 ≤ 2 * (1 - ⟪eh k, e k⟫ ^ 2) := h1
    _ ≤ 2 * (4 * ‖Gh - G‖ ^ 2 / s ^ 2) := by gcongr
    _ = 8 * ‖Gh - G‖ ^ 2 / s ^ 2 := by ring

variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The prefix of length `n` of an i.i.d. sequence has the product law. -/
lemma map_prefix_eq_pi {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {Z : ℕ → Ω → H} {P : Measure H} (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z Pr)
    (hlaw : ∀ i, Pr.map (Z i) = P) (n : ℕ) :
    Pr.map (fun ω (i : Fin n) => Z i ω) = Measure.pi fun _ : Fin n => P := by
  have hind' : iIndepFun (fun i : Fin n => Z i) Pr := hind.precomp Fin.val_injective
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i : Fin n => (hZ i).aemeasurable)).1 hind']
  simp only [hlaw]

/-- **In probability under the product law.** -/
theorem tendsto_pi_betaB {P : Measure H} [IsProbabilityMeasure P] {e : ℕ → H} (he : Orthonormal ℝ e)
    (hsp : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) (h2 : MemLp id 2 P) (C : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => P) {z | ε < C * betaB P e z ^ 2}) atTop (𝓝 0) := by
  set Pr : Measure (ℕ → H) := Measure.infinitePi fun _ => P
  have hZ : ∀ i, Measurable (fun ω : ℕ → H => ω i) := fun i => measurable_pi_apply i
  have hind : iIndepFun (fun i (ω : ℕ → H) => ω i) Pr :=
    iIndepFun_infinitePi (P := fun _ => P) (X := fun _ => id) (fun _ => measurable_id)
  have hlaw : ∀ i, Pr.map (fun ω : ℕ → H => ω i) = P := fun i => Measure.infinitePi_map_eval _ i
  have hae := ae_tendsto_betaB hZ hind hlaw he hsp h2
  have hmeas : ∀ n, Measurable (fun z : Fin n → H => C * betaB P e z ^ 2) :=
    fun n => (measurable_betaB n).pow_const 2 |>.const_mul C
  have hconv : ∀ᵐ ω ∂Pr, Tendsto (fun n : ℕ => C * betaB P e (fun i : Fin n => ω i) ^ 2) atTop (𝓝 0) := by
    filter_upwards [hae] with ω hω
    have := (hω.pow 2).const_mul C
    simpa using this
  have hTIM := tendstoInMeasure_of_tendsto_ae (μ := Pr)
    (f := fun (n : ℕ) (ω : ℕ → H) => C * betaB P e (fun i : Fin n => ω i) ^ 2) (g := fun _ => 0)
    (fun n => ((hmeas n).comp (Measurable.of_eval fun i => measurable_pi_apply _)).aestronglyMeasurable) hconv
  have hT := hTIM (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => zero_le) fun n => ?_
  have hmap := map_prefix_eq_pi hZ hind hlaw n
  rw [← hmap, Measure.map_apply (Measurable.of_eval fun i => measurable_pi_apply _)
    (measurableSet_lt measurable_const (hmeas n))]
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hω ⊢
  rw [edist_dist, Real.dist_eq, sub_zero]
  exact ENNReal.ofReal_le_ofReal (hω.le.trans (le_abs_self _))

end StatFormal.CovPerturb
