import StatFormal.Archive.Wave24a.Statements

/-!
# Route — B `lem:lin-lipschitz` (untrusted)

For `Γ = {z + τ(z)ν : z ⊥ ν}` put `w = Lν`, `P_ν v = v − (⟨ν,v⟩/‖ν‖²)ν`, `y = P_ν ∘ L⁻¹` (continuous linear, values
in `ν^⊥`) and `g(x) = ⟨L y(x), w⟩/‖w‖² + τ(y(x))`. Then `LΓ = {x + g(x)w : x ⊥ w}` (the paper's `A = L⁻¹(π|_{H'})⁻¹`
is `y` on `w^⊥`), and `g` is Lipschitz on all of `H`. The `𝒫^ℓ` equivalence: `(L#P)(S) = P(L⁻¹S)`, `L⁻¹S` is a
hypersurface, `‖Lx‖ ≤ ‖L‖‖x‖`, and the converse is the same statement for `L⁻¹`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave24a

open StatFormal.OTFD.Wave1 (IsLipHyp lipHyp PellClass)

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `P_ν v = v − (‖ν‖²)⁻¹ ⟨ν, v⟩ ν`. -/
def projPerp (ν : H) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H - (‖ν‖ ^ 2)⁻¹ • (innerSL ℝ ν).smulRight ν

lemma projPerp_apply (ν v : H) : projPerp ν v = v - ((‖ν‖ ^ 2)⁻¹ * ⟪ν, v⟫) • ν := by
  simp [projPerp, smul_smul]

lemma inner_projPerp (ν v : H) (hν : ν ≠ 0) : ⟪projPerp ν v, ν⟫ = 0 := by
  have h : ‖ν‖ ^ 2 ≠ 0 := by positivity
  rw [projPerp_apply, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm]
  simp only [conj_trivial]
  field_simp
  ring

lemma projPerp_add (ν a : H) (t : ℝ) (ha : ⟪a, ν⟫ = 0) (hν : ν ≠ 0) : projPerp ν (a + t • ν) = a := by
  have h : ‖ν‖ ^ 2 ≠ 0 := by positivity
  rw [projPerp_apply, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm, ha]
  rw [zero_add, show (‖ν‖ ^ 2)⁻¹ * (t * ‖ν‖ ^ 2) = t by field_simp]
  abel

theorem lin_lipschitz_aux (L : H ≃L[ℝ] H) {ν : H} (hν : ν ≠ 0) {τ : H → ℝ} {K : ℝ≥0}
    (hτ : LipschitzOnWith K τ {z | ⟪z, ν⟫ = 0}) : IsLipHyp (L '' lipHyp ν τ) := by
  set w := L ν with hw
  have hw0 : w ≠ 0 := by simpa [hw] using hν
  have hw2 : ‖w‖ ^ 2 ≠ 0 := by positivity
  set y : H →L[ℝ] H := (projPerp ν).comp (L.symm : H →L[ℝ] H) with hy
  have hyperp : ∀ x, ⟪y x, ν⟫ = 0 := fun x => inner_projPerp ν _ hν
  have hyL : ∀ (a : H) (t : ℝ), ⟪a, ν⟫ = 0 → y (L a + t • w) = a := by
    intro a t ha
    show projPerp ν (L.symm (L a + t • L ν)) = a
    rw [map_add, map_smul, L.symm_apply_apply, L.symm_apply_apply]
    exact projPerp_add ν a t ha hν
  set g : H → ℝ := fun x => ⟪L (y x), w⟫ / ‖w‖ ^ 2 + τ (y x) with hg
  refine ⟨w, hw0, g, ?_, ?_⟩
  · -- `g` is Lipschitz (on all of `H`)
    set ℓ : H →L[ℝ] ℝ := (‖w‖ ^ 2)⁻¹ • (innerSL ℝ w).comp ((L : H →L[ℝ] H).comp y) with hℓ
    have hℓe : (fun x => ⟪L (y x), w⟫ / ‖w‖ ^ 2) = ℓ := by
      funext x
      simp [hℓ, div_eq_mul_inv, real_inner_comm, mul_comm]
    have h1 : LipschitzWith ‖ℓ‖₊ (fun x => ⟪L (y x), w⟫ / ‖w‖ ^ 2) := by
      rw [hℓe]; exact ℓ.lipschitzWith
    have h2 : LipschitzOnWith (K * ‖y‖₊) (τ ∘ y) univ :=
      hτ.comp y.lipschitzWith.lipschitzOnWith (fun x _ => hyperp x)
    exact ⟨_, (h1.lipschitzOnWith.add h2).mono (subset_univ _)⟩
  · ext p
    constructor
    · rintro ⟨q, ⟨z, hz, rfl⟩, rfl⟩
      set c := ⟪L z + τ z • w, w⟫ / ‖w‖ ^ 2 with hc
      refine ⟨L z + (τ z - c) • w, ?_, ?_⟩
      · rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
        simp only [conj_trivial, hc, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp
        ring
      · have hyz : y (L z + (τ z - c) • w) = z := hyL z _ hz
        simp only [hg, hyz, map_add, map_smul, ← hw]
        rw [add_assoc, ← add_smul]
        congr 2
        simp only [hc, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, conj_trivial]
        field_simp
        ring
    · rintro ⟨x, hx, rfl⟩
      set z := y x with hz
      set d := (‖ν‖ ^ 2)⁻¹ * ⟪ν, L.symm x⟫ with hd
      have hzx : L.symm x = z + d • ν := by
        simp only [hz, hy, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
          projPerp_apply, hd]
        abel
      have hx' : x = L z + d • w := by
        have := congrArg L hzx
        simpa [hw] using this
      refine ⟨z + τ z • ν, ⟨z, hyperp x, rfl⟩, ?_⟩
      have hLz : ⟪L z, w⟫ = -(d * ‖w‖ ^ 2) := by
        have h0 : ⟪L z + d • w, w⟫ = 0 := hx' ▸ hx
        rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq] at h0
        simp only [conj_trivial] at h0
        linarith
      simp only [hg, ← hz, map_add, map_smul, ← hw, hLz]
      rw [hx', add_assoc, ← add_smul]
      congr 2
      field_simp
      ring

end

theorem lin_lipschitz : Claims.lin_lipschitz := by
  intro H _ _ L Γ ⟨ν, hν, τ, ⟨K, hK⟩, hΓ⟩
  subst hΓ
  exact lin_lipschitz_aux L hν hK

lemma pell_map {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (L : H ≃L[ℝ] H) {P : Measure H} (hP : PellClass P) : PellClass (P.map L) := by
  obtain ⟨hprob, hmom, hnull⟩ := hP
  set e := L.toHomeomorph.toMeasurableEquiv with he
  have hmap : P.map L = P.map e := rfl
  refine ⟨(Measure.isProbabilityMeasure_map_iff e.measurable.aemeasurable).2 hprob, ?_, ?_⟩
  · rw [hmap, lintegral_map_equiv]
    calc ∫⁻ x, ‖e x‖ₑ ^ 2 ∂P ≤ ∫⁻ x, (‖(L : H →L[ℝ] H)‖ₑ * ‖x‖ₑ) ^ 2 ∂P := by
          refine lintegral_mono fun x => ?_
          gcongr
          exact (L : H →L[ℝ] H).le_opENorm x
      _ = ‖(L : H →L[ℝ] H)‖ₑ ^ 2 * ∫⁻ x, ‖x‖ₑ ^ 2 ∂P := by
          simp_rw [mul_pow]
          exact lintegral_const_mul' _ _ (by simp)
      _ < ⊤ := ENNReal.mul_lt_top (by simp) hmom
  · intro S hS
    rw [hmap, e.map_apply]
    have hpre : e ⁻¹' S = L.symm '' S := by
      ext x; simp [he, ContinuousLinearEquiv.image_symm_eq_preimage]
    rw [hpre]
    exact hnull _ (lin_lipschitz H L.symm S hS)

theorem lin_lipschitz_pell : Claims.lin_lipschitz_pell := by
  intro H _ _ _ _ L P
  refine ⟨fun h => ?_, pell_map L⟩
  have h2 := pell_map L.symm h
  rwa [Measure.map_map L.symm.continuous.measurable L.continuous.measurable,
    show (L.symm ∘ L : H → H) = id from funext fun x => L.symm_apply_apply x, Measure.map_id] at h2

example : Claims.lin_lipschitz := lin_lipschitz
example : Claims.lin_lipschitz_pell := lin_lipschitz_pell

end StatFormal.Wave24a
