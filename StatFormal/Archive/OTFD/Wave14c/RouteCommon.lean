import StatFormal.Archive.OTFD.Wave14c.Statements
import StatFormal.Archive.OTFD.Wave7a.RouteOOS
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap

/-!
# Route: shared lemmas for wave 14c (untrusted)

* `addIso c`: `x ↦ c + x` is an order isomorphism of `EReal` for real `c`, so it commutes with suprema.
* `subgrad_of_fderiv`: a convex differentiable `ψ` satisfies `ψ(u) + ⟨g, y − u⟩ ≤ ψ(y)` when `∇ψ(u) = g`
  (restrict to the segment and use the one-dimensional slope inequality).
* `boundary_dom`, `hsup_frontier`: the certified `band_boundary_sup` for `Q̂ = ½M⁻¹∇ψ`, `ψ` convex differentiable.
* `gap_le`, `softmax_mem_simplex`: the exact gap is below every value of the minimand; softmax weights are in `Δ_n`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory Set Finset Matrix
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave14c

open StatFormal.OTFD.Bands (simplex gap score softmax)
open StatFormal.OTFD.Bands2 (hsup)
open StatFormal.OTFD.Wave4 (dotCLM)

/-! ### `EReal` translation -/

lemma ereal_add_cancel (c : ℝ) (x : EReal) : ((-c : ℝ) : EReal) + ((c : EReal) + x) = x := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe x => rw [← EReal.coe_add, ← EReal.coe_add]; congr 1; ring

/-- `x ↦ c + x` as an order isomorphism of `EReal`. -/
def addIso (c : ℝ) : EReal ≃o EReal where
  toFun x := (c : EReal) + x
  invFun x := ((-c : ℝ) : EReal) + x
  left_inv x := ereal_add_cancel c x
  right_inv x := by
    have h := ereal_add_cancel (-c) x
    simpa using h
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      change (c : EReal) + x ≤ (c : EReal) + y at h
      have h' : ((-c : ℝ) : EReal) + ((c : EReal) + x) ≤ ((-c : ℝ) : EReal) + ((c : EReal) + y) := by
        gcongr
      rwa [ereal_add_cancel, ereal_add_cancel] at h'
    · intro h
      change (c : EReal) + x ≤ (c : EReal) + y
      gcongr

lemma add_biSup {ι : Type*} (c : ℝ) (A : Set ι) (g : ι → EReal) :
    (c : EReal) + ⨆ u ∈ A, g u = ⨆ u ∈ A, ((c : EReal) + g u) := by
  change addIso c (⨆ u ∈ A, g u) = ⨆ u ∈ A, addIso c (g u)
  rw [OrderIso.map_iSup]
  congr 1; ext u
  rw [OrderIso.map_iSup]

lemma add_biInf {ι : Type*} (c : ℝ) (A : Set ι) (g : ι → EReal) :
    (c : EReal) + ⨅ u ∈ A, g u = ⨅ u ∈ A, ((c : EReal) + g u) := by
  change addIso c (⨅ u ∈ A, g u) = ⨅ u ∈ A, addIso c (g u)
  rw [OrderIso.map_iInf]
  congr 1; ext u
  rw [OrderIso.map_iInf]

/-! ### Convex differentiable potentials -/

variable {K : ℕ}

lemma subgrad_of_fderiv {ψ : (Fin K → ℝ) → ℝ} {g u : Fin K → ℝ} (hc : ConvexOn ℝ univ ψ)
    (hd : HasFDerivAt ψ (dotCLM g) u) (y : Fin K → ℝ) : ψ u + g ⬝ᵥ (y - u) ≤ ψ y := by
  set φ : ℝ → ℝ := ψ ∘ AffineMap.lineMap u y with hφ
  have hφc : ConvexOn ℝ univ φ := by
    have := hc.comp_affineMap (AffineMap.lineMap u y)
    simpa [preimage_univ] using this
  have hline : HasDerivAt (fun s : ℝ => AffineMap.lineMap u y s) (y - u) 0 :=
    AffineMap.hasDerivAt_lineMap
  have hd' : HasFDerivAt ψ (dotCLM g) (AffineMap.lineMap u y (0 : ℝ)) := by
    simpa using hd
  have hder : HasDerivAt φ (dotCLM g (y - u)) 0 := hd'.comp_hasDerivAt (0 : ℝ) hline
  have hsl := hφc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hder
  rw [slope_def_field] at hsl
  simp only [hφ, Function.comp_apply, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    sub_zero, div_one] at hsl
  rw [StatFormal.OTFD.Wave4.dotCLM_apply] at hsl
  linarith

/-- Boundary domination for `Q̂ = ½M⁻¹∇ψ`, `ψ` convex differentiable (certified `band_boundary_sup`). -/
lemma boundary_dom (hK : 0 < K) {M : Matrix (Fin K) (Fin K) ℝ} (hM : M.PosDef) {ψ : (Fin K → ℝ) → ℝ}
    {T : (Fin K → ℝ) → Fin K → ℝ} (hc : ConvexOn ℝ univ ψ)
    (hd : ∀ u, HasFDerivAt ψ (dotCLM ((2 : ℝ) • (M *ᵥ T u))) u) {A : Set (Fin K → ℝ)} (hA : IsCompact A)
    (v : Fin K → ℝ) : ∀ u ∈ A, ∃ u' ∈ frontier A, v ⬝ᵥ T u ≤ v ⬝ᵥ T u' := by
  have hsub : ∀ u y, ψ u + (2 • (M *ᵥ T u)) ⬝ᵥ (y - u) ≤ ψ y := by
    intro u y
    have h := subgrad_of_fderiv hc (hd u) y
    have h2 : (2 • (M *ᵥ T u) : Fin K → ℝ) = (2 : ℝ) • (M *ᵥ T u) := by
      rw [two_smul, two_smul]
    rw [h2]; exact h
  intro u hu
  exact StatFormal.OTFD.Bands.band_boundary_sup K M ψ T hK hM hc hsub A hA v u hu

lemma hsup_frontier (hK : 0 < K) {M : Matrix (Fin K) (Fin K) ℝ} (hM : M.PosDef) {ψ : (Fin K → ℝ) → ℝ}
    {T : (Fin K → ℝ) → Fin K → ℝ} (hc : ConvexOn ℝ univ ψ)
    (hd : ∀ u, HasFDerivAt ψ (dotCLM ((2 : ℝ) • (M *ᵥ T u))) u) {A : Set (Fin K → ℝ)} (hA : IsCompact A)
    (v : Fin K → ℝ) : hsup T A v = hsup T (frontier A) v := by
  apply le_antisymm
  · apply iSup₂_le
    intro u hu
    obtain ⟨u', hu', hle⟩ := boundary_dom hK hM hc hd hA v u hu
    exact (EReal.coe_le_coe_iff.2 hle).trans (le_iSup₂ (f := fun u _ => ((v ⬝ᵥ T u : ℝ) : EReal)) u' hu')
  · exact biSup_mono fun u hu => hA.isClosed.frontier_subset hu

/-! ### Gaps and softmax -/

variable {n : ℕ}

lemma minand_nonneg (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (j : Fin n) (u : Fin K → ℝ) :
    0 ≤ (⨆ k, score a b k u) - score a b j u :=
  sub_nonneg.2 (le_ciSup (f := fun k => score a b k u) (Set.finite_range _).bddAbove j)

lemma gap_bdd (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (j : Fin n) :
    BddBelow ((fun u => (⨆ k, score a b k u) - score a b j u) '' A) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨u, -, rfl⟩
  exact minand_nonneg a b j u

lemma gap_le {a : Fin n → ℝ} {b : Fin n → Fin K → ℝ} {A : Set (Fin K → ℝ)} (j : Fin n) {u : Fin K → ℝ}
    (hu : u ∈ A) : gap a b A j ≤ (⨆ k, score a b k u) - score a b j u :=
  csInf_le (gap_bdd a b A j) ⟨u, hu, rfl⟩

lemma softmax_mem_simplex (hn : 0 < n) (x : Fin n → ℝ) : softmax x ∈ simplex n := by
  have hpos : 0 < ∑ k, Real.exp (x k) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Finset.sum_pos (fun k _ => Real.exp_pos _) Finset.univ_nonempty
  refine ⟨fun i => div_nonneg (Real.exp_pos _).le hpos.le, ?_⟩
  unfold softmax
  rw [← Finset.sum_div, div_self hpos.ne']

end StatFormal.OTFD.Wave14c
