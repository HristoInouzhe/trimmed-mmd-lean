import StatFormal.Archive.NNFibers.Wave1.Statements
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Proof route — `eq:dim`, `eq:codim-s`, `lem:codim-blockcount` (untrusted)
-/

noncomputable section
open Finset Module

namespace StatFormal.NNFibers.Wave1

variable {din dout q m j : ℕ}

/-- Group sums of the outgoing weights, `a ↦ (Σ_{g u = κ} a_u)_κ`. -/
def sumMap (g : Fin m → Fin q ⊕ Fin j) :
    (Fin m → Fin dout → ℝ) →ₗ[ℝ] (Fin q ⊕ Fin j → Fin dout → ℝ) where
  toFun a k := ∑ u ∈ univ.filter (fun u => g u = k), a u
  map_add' a b := by funext k; simp [Finset.sum_add_distrib]
  map_smul' c a := by funext k; simp [Finset.smul_sum]

/-- Outgoing weights putting `y κ` on the representative unit of group `κ`, `0` elsewhere. -/
def repOut (g : Fin m → Fin q ⊕ Fin j) (hg : Function.Surjective g) (y : Fin q ⊕ Fin j → Fin dout → ℝ) :
    Fin m → Fin dout → ℝ :=
  fun u => if u = Function.surjInv hg (g u) then y (g u) else 0

theorem sum_repOut (g : Fin m → Fin q ⊕ Fin j) (hg : Function.Surjective g)
    (y : Fin q ⊕ Fin j → Fin dout → ℝ) (k : Fin q ⊕ Fin j) :
    ∑ u ∈ univ.filter (fun u => g u = k), repOut g hg y u = y k := by
  have h1 : ∀ u ∈ univ.filter (fun u => g u = k),
      repOut g hg y u = if u = Function.surjInv hg k then y k else 0 := by
    intro u hu
    have hgu := (Finset.mem_filter.1 hu).2
    simp only [repOut, hgu]
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq']
  simp [Function.surjInv_eq hg k]

theorem sumMap_surjective (g : Fin m → Fin q ⊕ Fin j) (hg : Function.Surjective g) :
    Function.Surjective (sumMap (dout := dout) g) := fun y =>
  ⟨repOut g hg y, funext fun k => sum_repOut g hg y k⟩

theorem elim_zero_add (ω₁ ω₂ : Fin j → Fin din → ℝ) (k : Fin q ⊕ Fin j) :
    Sum.elim (0 : Fin q → Fin din → ℝ) (ω₁ + ω₂) k =
      Sum.elim (0 : Fin q → Fin din → ℝ) ω₁ k + Sum.elim (0 : Fin q → Fin din → ℝ) ω₂ k := by
  cases k <;> simp

theorem elim_zero_smul (c : ℝ) (ω₁ : Fin j → Fin din → ℝ) (k : Fin q ⊕ Fin j) :
    Sum.elim (0 : Fin q → Fin din → ℝ) (c • ω₁) k = c • Sum.elim (0 : Fin q → Fin din → ℝ) ω₁ k := by
  cases k <;> simp

/-- Parametrisation of the direction of `Γ̄_s`: free zero-group directions and balanced outputs. -/
def embed (g : Fin m → Fin q ⊕ Fin j) :
    ((Fin j → Fin din → ℝ) × LinearMap.ker (sumMap (dout := dout) g)) →ₗ[ℝ]
      (Fin m → Neuron din dout) where
  toFun p u := (Sum.elim (0 : Fin q → Fin din → ℝ) p.1 (g u), (p.2 : Fin m → Fin dout → ℝ) u)
  map_add' p p' := by
    funext u
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Pi.add_apply, Prod.fst_add]; exact elim_zero_add _ _ _
    · simp
  map_smul' c p := by
    funext u
    refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]; exact elim_zero_smul _ _ _
    · simp

theorem embed_injective (g : Fin m → Fin q ⊕ Fin j) (hg : Function.Surjective g) :
    Function.Injective (embed (din := din) (dout := dout) g) := by
  intro p p' h
  have h' : ∀ u, embed (din := din) (dout := dout) g p u = embed g p' u := fun u => congrFun h u
  refine Prod.ext ?_ (Subtype.ext (funext fun u => congrArg Prod.snd (h' u)))
  funext ℓ
  have := congrArg Prod.fst (h' (Function.surjInv hg (Sum.inr ℓ)))
  simpa [embed, Function.surjInv_eq hg (Sum.inr ℓ)] using this

theorem mem_range_embed (g : Fin m → Fin q ⊕ Fin j) (δ : Fin m → Neuron din dout) :
    δ ∈ LinearMap.range (embed (din := din) (dout := dout) g) ↔
      (∃ ω' : Fin j → Fin din → ℝ, ∀ u, (δ u).1 = Sum.elim (0 : Fin q → Fin din → ℝ) ω' (g u)) ∧
        ∀ k, ∑ u ∈ univ.filter (fun u => g u = k), (δ u).2 = 0 := by
  constructor
  · rintro ⟨⟨ω', a⟩, rfl⟩
    refine ⟨⟨ω', fun u => rfl⟩, fun k => ?_⟩
    have := congrFun (LinearMap.mem_ker.1 a.2) k
    change ∑ u ∈ univ.filter (fun u => g u = k), (a : Fin m → Fin dout → ℝ) u = 0
    simpa [sumMap] using this
  · rintro ⟨⟨ω', hω⟩, hs⟩
    refine ⟨⟨ω', ⟨fun u => (δ u).2, LinearMap.mem_ker.2 (funext fun k => hs k)⟩⟩, ?_⟩
    funext u
    exact Prod.ext (hω u).symm rfl

/-- A base point of `Γ̄_s`. -/
def basePt (θs : Fin q → Neuron din dout) (g : Fin m → Fin q ⊕ Fin j) (hg : Function.Surjective g) :
    Fin m → Neuron din dout :=
  fun u => (Sum.elim (fun i => (θs i).1) (0 : Fin j → Fin din → ℝ) (g u),
    repOut g hg (Sum.elim (fun i => (θs i).2) 0) u)

/-- The affine subspace `Γ̄_s`. -/
def closureAff (θs : Fin q → Neuron din dout) (g : Fin m → Fin q ⊕ Fin j) (hg : Function.Surjective g) :
    AffineSubspace ℝ (Fin m → Neuron din dout) :=
  AffineSubspace.mk' (basePt θs g hg) (LinearMap.range (embed g))

theorem coe_closureAff (θs : Fin q → Neuron din dout) (g : Fin m → Fin q ⊕ Fin j)
    (hg : Function.Surjective g) : (closureAff θs g hg : Set _) = closureSet θs g := by
  ext θ
  rw [SetLike.mem_coe, closureAff, AffineSubspace.mem_mk', vsub_eq_sub, mem_range_embed]
  simp only [closureSet, Set.mem_ofPred_eq]
  have hsum : ∀ k, ∑ u ∈ univ.filter (fun u => g u = k), ((θ - basePt θs g hg) u).2 =
      ∑ u ∈ univ.filter (fun u => g u = k), (θ u).2 - Sum.elim (fun i => (θs i).2) 0 k := by
    intro k
    simp only [Pi.sub_apply, Prod.snd_sub, Finset.sum_sub_distrib, basePt]
    rw [sum_repOut]
  simp only [hsum, sub_eq_zero]
  constructor
  · rintro ⟨⟨ω', hω⟩, hs⟩
    refine ⟨⟨ω', fun u => ?_⟩, fun i => by simpa using hs (Sum.inl i),
      fun ℓ => by simpa using hs (Sum.inr ℓ)⟩
    have := hω u
    simp only [Pi.sub_apply, Prod.fst_sub, basePt] at this
    cases hgu : g u with
    | inl i => rw [hgu] at this; simpa [sub_eq_zero] using this
    | inr ℓ => rw [hgu] at this; simpa using this
  · rintro ⟨⟨ω', hω⟩, hi, hℓ⟩
    refine ⟨⟨ω', fun u => ?_⟩, fun k => ?_⟩
    · simp only [Pi.sub_apply, Prod.fst_sub, basePt, hω u]
      cases g u <;> simp
    · cases k with
      | inl i => simpa using hi i
      | inr ℓ => simpa using hℓ ℓ

theorem finrank_theta : finrank ℝ (Fin m → Neuron din dout) = m * (din + dout) := by
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_prod]

theorem finrank_ker (g : Fin m → Fin q ⊕ Fin j) (hg : Function.Surjective g) :
    finrank ℝ (LinearMap.ker (sumMap (dout := dout) g)) + (q + j) * dout = m * dout := by
  have h := LinearMap.finrank_range_add_finrank_ker (sumMap (dout := dout) g)
  rw [LinearMap.range_eq_top.2 (sumMap_surjective g hg), finrank_top] at h
  have h1 : finrank ℝ (Fin q ⊕ Fin j → Fin dout → ℝ) = (q + j) * dout := by
    rw [Module.finrank_pi_fintype]; simp
  have h2 : finrank ℝ (Fin m → Fin dout → ℝ) = m * dout := by
    rw [Module.finrank_pi_fintype]; simp
  omega

theorem finrank_direction (θs : Fin q → Neuron din dout) (g : Fin m → Fin q ⊕ Fin j)
    (hg : Function.Surjective g) :
    finrank ℝ (closureAff θs g hg).direction + (q + j) * dout = j * din + m * dout := by
  rw [closureAff, AffineSubspace.direction_mk', LinearMap.finrank_range_of_inj (embed_injective g hg),
    Module.finrank_prod]
  have hj : finrank ℝ (Fin j → Fin din → ℝ) = j * din := by
    rw [Module.finrank_pi_fintype]; simp
  have := finrank_ker (dout := dout) g hg
  omega

theorem dim_closure : Claims.dim_closure := by
  intro din dout q m j θs g hg
  refine ⟨closureAff θs g hg, coe_closureAff θs g hg, ?_⟩
  have := finrank_direction θs g hg
  have h : ((finrank ℝ (closureAff θs g hg).direction : ℕ) : ℤ) + ((q : ℤ) + j) * dout =
      j * din + m * dout := by exact_mod_cast this
  linarith

theorem direction_eq (θs : Fin q → Neuron din dout) (g : Fin m → Fin q ⊕ Fin j)
    (hg : Function.Surjective g) (A : AffineSubspace ℝ (Fin m → Neuron din dout))
    (hA : (A : Set _) = closureSet θs g) : A = closureAff θs g hg :=
  SetLike.coe_injective (hA.trans (coe_closureAff θs g hg).symm)

theorem codim_blockcount : Claims.codim_blockcount := by
  intro din dout q m j θs g A hg hA
  rw [direction_eq θs g hg A hA, finrank_theta]
  have := finrank_direction θs g hg
  have h : ((finrank ℝ (closureAff θs g hg).direction : ℕ) : ℤ) + ((q : ℤ) + j) * dout =
      j * din + m * dout := by exact_mod_cast this
  push_cast
  constructor <;> linarith

theorem codim_balanced : Claims.codim_balanced := by
  intro d q m j θs g A hg hA
  have := (codim_blockcount d d q m j θs g A hg hA).2
  rw [this]; ring

end StatFormal.NNFibers.Wave1
