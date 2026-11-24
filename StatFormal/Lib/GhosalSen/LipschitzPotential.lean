import StatFormal.Archive.OTFD.Wave22a.Statements
import TauCeti.Analysis.Convex.Subdifferential

/-!
# Lipschitz convex potentials from bounded pieces of a subdifferential graph

If `C` is a nonempty set of pairs `(x, y)` with `y ∈ ∂u(x)` for an extended-valued `u : E → EReal` and `‖y‖ ≤ M` on
`C`, then the supremum of the affine minorants `φ(z) = sup_{(x, y) ∈ C} u(x) + ⟨y, z − x⟩` is a real-valued convex
`M`-Lipschitz function with `y ∈ ∂φ(x)` for every `(x, y) ∈ C` (and `φ = u` on the first projection of `C`).
This is the standard device (Rockafellar, Convex Analysis, §24) turning the extended-valued Brenier/McCann potential
of a bounded target into an everywhere finite Lipschitz one.
-/

noncomputable section
open Set TauCeti
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.GhosalSen

open StatFormal.OTFD.Wave22a (IsSubgrad)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The subgradient inequality in real form between two points of the subdifferential graph. -/
theorem toReal_add_inner_le {u : E → EReal} {x x' y : E} (hy : y ∈ subdifferential (innerₗ E) u x)
    (hx' : u x' ≠ ⊤) : (u x).toReal + ⟪y, x' - x⟫ ≤ (u x').toReal := by
  have hbot : ∀ z, u z ≠ ⊥ := fun z => apply_ne_bot_of_mem_subdifferential (innerₗ E) hy z
  have := (mem_subdifferential_iff_forall_toReal_add_le (innerₗ E) hbot (ne_top_of_mem_subdifferential _ hy)).1 hy
    x' hx'
  simp only [innerₗ_apply_apply] at this
  rwa [real_inner_comm] at this

/-- The affine minorant attached to a pair of `C`. -/
def affPiece (u : E → EReal) (p : E × E) (z : E) : ℝ := (u p.1).toReal + ⟪p.2, z - p.1⟫

/-- The Lipschitz regularisation `φ(z) = sup_{p ∈ C} u(p.1) + ⟨p.2, z − p.1⟩`. -/
def lipPot (u : E → EReal) (C : Set (E × E)) (z : E) : ℝ := ⨆ p : C, affPiece u p z

variable {u : E → EReal} {C : Set (E × E)} {M : ℝ}

theorem affPiece_le_at {p q : E × E} (hp : p.2 ∈ subdifferential (innerₗ E) u p.1)
    (hq : q.2 ∈ subdifferential (innerₗ E) u q.1) : affPiece u p q.1 ≤ (u q.1).toReal :=
  toReal_add_inner_le hp (ne_top_of_mem_subdifferential _ hq)

theorem affPiece_le_add (hM : ∀ p ∈ C, ‖p.2‖ ≤ M) {p : E × E} (hp : p ∈ C) (z z' : E) :
    affPiece u p z ≤ affPiece u p z' + M * ‖z - z'‖ := by
  have h1 : affPiece u p z = affPiece u p z' + ⟪p.2, z - z'⟫ := by
    simp only [affPiece, inner_sub_right]; ring
  have h2 : ⟪p.2, z - z'⟫ ≤ ‖p.2‖ * ‖z - z'‖ := real_inner_le_norm _ _
  have h3 : ‖p.2‖ * ‖z - z'‖ ≤ M * ‖z - z'‖ := mul_le_mul_of_nonneg_right (hM p hp) (norm_nonneg _)
  linarith

theorem bddAbove_affPiece (hC : C ⊆ {p | p.2 ∈ subdifferential (innerₗ E) u p.1})
    (hM : ∀ p ∈ C, ‖p.2‖ ≤ M) {p₀ : E × E} (hp₀ : p₀ ∈ C) (z : E) :
    BddAbove (range fun p : C => affPiece u p z) := by
  refine ⟨(u p₀.1).toReal + M * ‖z - p₀.1‖, ?_⟩
  rintro - ⟨⟨p, hp⟩, rfl⟩
  have := affPiece_le_add (u := u) hM hp z p₀.1
  have h2 := affPiece_le_at (hC hp) (hC hp₀)
  dsimp only
  linarith

theorem le_lipPot (hC : C ⊆ {p | p.2 ∈ subdifferential (innerₗ E) u p.1}) (hM : ∀ p ∈ C, ‖p.2‖ ≤ M)
    {p : E × E} (hp : p ∈ C) (z : E) : affPiece u p z ≤ lipPot u C z :=
  le_ciSup (f := fun q : C => affPiece u q z) (bddAbove_affPiece hC hM hp z) ⟨p, hp⟩

theorem lipPot_le_add (hC : C ⊆ {p | p.2 ∈ subdifferential (innerₗ E) u p.1}) (hM : ∀ p ∈ C, ‖p.2‖ ≤ M)
    (hne : C.Nonempty) (z z' : E) : lipPot u C z ≤ lipPot u C z' + M * ‖z - z'‖ := by
  haveI : Nonempty C := hne.to_subtype
  refine ciSup_le fun ⟨p, hp⟩ => ?_
  have := affPiece_le_add (u := u) hM hp z z'
  have h2 := le_lipPot hC hM hp z'
  linarith

/-- **The regularised potential.** -/
theorem lipPot_spec (hC : C ⊆ {p | p.2 ∈ subdifferential (innerₗ E) u p.1}) (hM : ∀ p ∈ C, ‖p.2‖ ≤ M)
    (hne : C.Nonempty) :
    ConvexOn ℝ univ (lipPot u C) ∧ (∀ z z', |lipPot u C z - lipPot u C z'| ≤ M * ‖z - z'‖) ∧
      ∀ p ∈ C, IsSubgrad (lipPot u C) p.1 p.2 := by
  haveI : Nonempty C := hne.to_subtype
  refine ⟨⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, fun z z' => ?_, fun p hp z => ?_⟩
  · refine ciSup_le fun ⟨q, hq⟩ => ?_
    have hx := le_lipPot hC hM hq x
    have hy := le_lipPot hC hM hq y
    have : affPiece u q (a • x + b • y) = a * affPiece u q x + b * affPiece u q y := by
      simp only [affPiece]
      have : a • x + b • y - q.1 = a • (x - q.1) + b • (y - q.1) := by
        rw [smul_sub, smul_sub, ← add_sub_add_comm, ← add_smul, hab, one_smul]
      rw [this, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have : (u q.1).toReal = a * (u q.1).toReal + b * (u q.1).toReal := by rw [← add_mul, hab, one_mul]
      linarith
    rw [this, smul_eq_mul, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]
  · rw [abs_le]
    have h1 := lipPot_le_add hC hM hne z z'
    have h2 := lipPot_le_add hC hM hne z' z
    rw [norm_sub_rev] at h2
    constructor <;> linarith
  · -- `lipPot = u` at `p.1`
    have hval : lipPot u C p.1 ≤ (u p.1).toReal :=
      ciSup_le fun ⟨q, hq⟩ => affPiece_le_at (hC hq) (hC hp)
    have hz := le_lipPot hC hM hp z
    simp only [affPiece] at hz
    linarith

/-- Existence form. -/
theorem exists_lipschitz_of_subset_subdifferential (hC : C ⊆ {p | p.2 ∈ subdifferential (innerₗ E) u p.1})
    (hM : ∀ p ∈ C, ‖p.2‖ ≤ M) (hne : C.Nonempty) :
    ∃ φ : E → ℝ, ConvexOn ℝ univ φ ∧ (∀ z z', |φ z - φ z'| ≤ M * ‖z - z'‖) ∧ ∀ p ∈ C, IsSubgrad φ p.1 p.2 :=
  ⟨lipPot u C, lipPot_spec hC hM hne⟩

end StatFormal.GhosalSen
