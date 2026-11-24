import StatFormal.Archive.OTFD.Wave14c.RouteCommon

/-!
# Route: B `prop:rk-linear-certificate` (untrusted)

`L(x_u) = L(𝔪) + ⟨b, Q̂(u)⟩` by linearity, and `c ↦ L(𝔪) + c` commutes with suprema in `EReal`. For the
entropic (resp. quadratic) map, `Q̂(u) = Σ_j q_j(u) Z_j` with `q(u)` the softmax (resp. simplex projection) of the
affine scores (certified Wave 7a `oos_ent_affine`, `oos_quad_affine`), `q(u) ∈ Δ_n` and `q_j(u) ≤ κ_j` (certified
Bands caps with `δ = δ_j ≤` the minimand at `u`), so `⟨b, Q̂(u)⟩ = Σ_j q_j(u) ℓ_j ≤` the knapsack value. Boundary:
certified `band_boundary_sup` with the Wave 7a potentials.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory Set Finset Matrix

namespace StatFormal.OTFD.Wave14c

open StatFormal.OTFD.Bands (simplex gap score softmax Qent IsSimplexProj)
open StatFormal.OTFD.Bands2 (hsup edgeUp)
open StatFormal.OTFD.Wave2 (cappedSimplex)
open StatFormal.OTFD.Wave7a (oosA oosB rawScore baryMap)

variable {K : ℕ} {F : Type} [AddCommGroup F] [Module ℝ F]

lemma L_recon (L : F →ₗ[ℝ] ℝ) (mo : F) (e : Fin K → F) (c : Fin K → ℝ) :
    L (recon mo e c) = L mo + lfCoef L e ⬝ᵥ c := by
  unfold recon lfCoef
  rw [map_add, map_sum]
  congr 1
  simp only [map_smul, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

lemma sup_L_recon (L : F →ₗ[ℝ] ℝ) (mo : F) (e : Fin K → F) (Q : (Fin K → ℝ) → Fin K → ℝ)
    (A : Set (Fin K → ℝ)) :
    (⨆ u ∈ A, ((L (recon mo e (Q u)) : ℝ) : EReal)) = edgeUp Q A (L mo) (lfCoef L e) := by
  unfold edgeUp hsup
  rw [add_biSup]
  congr 1; ext u; congr 1; ext _
  rw [L_recon, EReal.coe_add]

theorem rk_linear_identity : Claims.rk_linear_identity := by
  intro K F _ _ L mo e Q A
  refine ⟨fun u => L_recon L mo e (Q u), sup_L_recon L mo e Q A, fun u hu => ?_⟩
  rw [← sup_L_recon]
  exact le_iSup₂ (f := fun u _ => ((L (recon mo e (Q u)) : ℝ) : EReal)) u hu

variable {n : ℕ}

/-- `⟨b, Σ_j q_j Z_j⟩ ≤ max_{𝒫_κ} Σ_j q_j ⟨b, Z_j⟩` for `q ∈ 𝒫_κ`. -/
lemma dot_bary_le {κ q : Fin n → ℝ} (hq : q ∈ cappedSimplex κ) (Z : Fin n → Fin K → ℝ) (b : Fin K → ℝ) :
    ((b ⬝ᵥ ∑ j, q j • Z j : ℝ) : EReal) ≤ knapUp κ (fun j => b ⬝ᵥ Z j) := by
  have : b ⬝ᵥ ∑ j, q j • Z j = ∑ j, q j * (b ⬝ᵥ Z j) := by
    rw [dotProduct_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [dotProduct_smul, smul_eq_mul]
  rw [this]
  exact le_iSup₂ (f := fun q _ => ((∑ j, q j * (b ⬝ᵥ Z j) : ℝ) : EReal)) q hq

lemma edgeUp_le_cert {Q : (Fin K → ℝ) → Fin K → ℝ} {A : Set (Fin K → ℝ)} {κ : Fin n → ℝ}
    {Z : Fin n → Fin K → ℝ} (w : (Fin K → ℝ) → Fin n → ℝ)
    (hw : ∀ u ∈ A, w u ∈ cappedSimplex κ ∧ Q u = ∑ j, w u j • Z j) (mo : ℝ) (b : Fin K → ℝ) :
    edgeUp Q A mo b ≤ certUp κ Z mo b := by
  unfold edgeUp certUp
  gcongr
  apply iSup₂_le
  intro u hu
  rw [(hw u hu).2]
  exact dot_bary_le (hw u hu).1 Z b

theorem rk_linear_ent : Claims.rk_linear_ent := by
  intro n K ε M Z f A F _ _ L mo e hn hε hM hA
  refine edgeUp_le_cert (fun u => softmax (fun k => score (oosA M f Z) (oosB M Z) k u / ε)) ?_ _ _
  intro u hu
  refine ⟨⟨softmax_mem_simplex hn _, fun j => ?_⟩, StatFormal.OTFD.Wave7a.oos_ent_affine n K ε M Z f u hM⟩
  exact StatFormal.OTFD.Bands.band_cap_entropic n K _ _ ε _ j u hε (gap_le j hu)

theorem rk_linear_quad : Claims.rk_linear_quad := by
  intro n K m γ M Z f q A F _ _ L mo e hn hγ hm hM hA hq
  refine edgeUp_le_cert q ?_ _ _
  intro u hu
  have hp := (StatFormal.OTFD.Wave7a.oos_quad_affine n K (γ / m) M Z f u (q u) hM).1 (hq u)
  refine ⟨⟨hp.1, fun j => ?_⟩, rfl⟩
  exact StatFormal.OTFD.Bands.band_cap_quadratic n K m _ _ γ _ j u (q u) hγ hm (gap_le j hu) hp

lemma sup_frontier_of (L : F →ₗ[ℝ] ℝ) (mo : F) (e : Fin K → F) {Q : (Fin K → ℝ) → Fin K → ℝ}
    {A : Set (Fin K → ℝ)} (h : hsup Q A (lfCoef L e) = hsup Q (frontier A) (lfCoef L e)) :
    (⨆ u ∈ A, ((L (recon mo e (Q u)) : ℝ) : EReal)) = ⨆ u ∈ frontier A, ((L (recon mo e (Q u)) : ℝ) : EReal) := by
  rw [sup_L_recon, sup_L_recon]
  unfold edgeUp; rw [h]

theorem rk_linear_boundary : Claims.rk_linear_boundary := by
  intro n K m ε γ M Z f q A F _ _ L mo e hn hK hM hA
  refine ⟨fun hε => sup_frontier_of L mo e ?_, fun hγ hm hq => sup_frontier_of L mo e ?_⟩
  · obtain ⟨hc, hd⟩ := StatFormal.OTFD.Wave7a.oos_ent_potential n K ε M Z f hn hε hM
    exact hsup_frontier hK hM hc (fun u => by rw [← (hd u).2]; exact (hd u).1) hA _
  · have hlam : 0 < γ / m := div_pos hγ (Nat.cast_pos.2 hm)
    obtain ⟨hc, hd⟩ := StatFormal.OTFD.Wave7a.oos_quad_potential n K (γ / m) M Z f q hn hlam hM hq
    exact hsup_frontier hK hM hc (fun u => by rw [← (hd u).2]; exact (hd u).1) hA _

end StatFormal.OTFD.Wave14c
