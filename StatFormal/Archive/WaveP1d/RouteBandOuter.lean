import StatFormal.Archive.WaveP1d.Statements
import StatFormal.Archive.OTFD.Wave14c.RouteLinear
import StatFormal.Archive.OTFD.Wave14c.RouteNesting

/-!
# Route: otfd B `prop:band-certificate` (iv), the certified outer band (untrusted)

For `u ∈ A`, the weights `q(u)` of the entropic (softmax of the affine scores, certified Wave 7a `oos_ent_affine`) and
quadratic (simplex projection, `oos_quad_affine`) maps lie in the capped simplex: `q(u) ∈ Δ_n` and `q_j(u) ≤ κ_j` by
the certified caps of `prop:band-certificate` (iii) with `δ_j ≤ δ_j(p) ≤` the minimand at `u`. Hence
`⟨e(t), Q̂(u)⟩ = Σ_j q_j(u) ⟨e(t), Z_j⟩` lies between the knapsack minimum and maximum, for every `u ∈ A`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Finset Matrix

namespace StatFormal.WaveP1d

namespace RouteBandOuter

open StatFormal.OTFD.Bands (simplex gap score softmax Qent IsSimplexProj)
open StatFormal.OTFD.Bands2 (hsup edgeUp edgeLo band)
open StatFormal.OTFD.Wave2 (cappedSimplex)
open StatFormal.OTFD.Wave7a (oosA oosB rawScore baryMap)
open StatFormal.OTFD.Wave14c (knapUp knapLo certUp certLo entCaps quadCaps)

variable {n K : ℕ}

lemma knapLo_le_dot {κ q : Fin n → ℝ} (hq : q ∈ cappedSimplex κ) (Z : Fin n → Fin K → ℝ) (b : Fin K → ℝ) :
    knapLo κ (fun j => b ⬝ᵥ Z j) ≤ ((b ⬝ᵥ ∑ j, q j • Z j : ℝ) : EReal) := by
  have : b ⬝ᵥ ∑ j, q j • Z j = ∑ j, q j * (b ⬝ᵥ Z j) := by
    rw [dotProduct_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [dotProduct_smul, smul_eq_mul]
  rw [this]
  unfold knapLo
  exact iInf₂_le (f := fun q (_ : q ∈ cappedSimplex κ) => ((∑ j, q j * (b ⬝ᵥ Z j) : ℝ) : EReal)) q hq

lemma cert_le_edgeLo {Q : (Fin K → ℝ) → Fin K → ℝ} {A : Set (Fin K → ℝ)} {κ : Fin n → ℝ}
    {Z : Fin n → Fin K → ℝ} (w : (Fin K → ℝ) → Fin n → ℝ)
    (hw : ∀ u ∈ A, w u ∈ cappedSimplex κ ∧ Q u = ∑ j, w u j • Z j) (mo : ℝ) (b : Fin K → ℝ) :
    certLo κ Z mo b ≤ edgeLo Q A mo b := by
  unfold edgeLo certLo
  have hh : hsup Q A (-b) ≤ -knapLo κ (fun j => b ⬝ᵥ Z j) := by
    unfold hsup
    apply iSup₂_le
    intro u hu
    rw [(hw u hu).2, neg_dotProduct, EReal.coe_neg]
    exact EReal.neg_le_neg_iff.2 (knapLo_le_dot (hw u hu).1 Z b)
  rw [sub_eq_add_neg]
  gcongr
  calc knapLo κ (fun j => b ⬝ᵥ Z j) = -(-knapLo κ (fun j => b ⬝ᵥ Z j)) := (neg_neg _).symm
    _ ≤ -hsup Q A (-b) := EReal.neg_le_neg_iff.2 hh

end RouteBandOuter

open RouteBandOuter
open StatFormal.OTFD.Bands (simplex gap score softmax Qent IsSimplexProj)
open StatFormal.OTFD.Bands2 (hsup edgeUp edgeLo band)
open StatFormal.OTFD.Wave2 (cappedSimplex)
open StatFormal.OTFD.Wave7a (oosA oosB rawScore baryMap)
open StatFormal.OTFD.Wave14c (knapUp knapLo certUp certLo entCaps quadCaps)

theorem band_outer_ent : Claims.band_outer_ent := by
  intro n K ε M Z f A δ T mo e hn hε hM _hA hδ
  have hw : ∀ u ∈ A, softmax (fun k => score (oosA M f Z) (oosB M Z) k u / ε) ∈ cappedSimplex (entCaps ε δ) ∧
      Qent ε M Z f u = ∑ j, softmax (fun k => score (oosA M f Z) (oosB M Z) k u / ε) j • Z j := by
    intro u hu
    refine ⟨⟨StatFormal.OTFD.Wave14c.softmax_mem_simplex hn _, fun j => ?_⟩,
      StatFormal.OTFD.Wave7a.oos_ent_affine n K ε M Z f u hM⟩
    refine (StatFormal.OTFD.Bands.band_cap_entropic n K _ _ ε (δ j) j u hε ?_)
    exact (hδ j).trans (StatFormal.OTFD.Wave14c.gap_le j hu)
  have h1 : ∀ t, certLo (entCaps ε δ) Z (mo t) (e t) ≤ edgeLo (Qent ε M Z f) A (mo t) (e t) ∧
      edgeUp (Qent ε M Z f) A (mo t) (e t) ≤ certUp (entCaps ε δ) Z (mo t) (e t) := fun t =>
    ⟨cert_le_edgeLo _ hw _ _, StatFormal.OTFD.Wave14c.edgeUp_le_cert _ hw _ _⟩
  exact ⟨h1, StatFormal.OTFD.Wave14c.band_mono (fun t => (h1 t).1) (fun t => (h1 t).2)⟩



theorem band_outer_quad : Claims.band_outer_quad := by
  intro n K m γ M Z f q A δ T mo e hγ hm hM _hA hq hδ
  have hw : ∀ u ∈ A, q u ∈ cappedSimplex (quadCaps m γ δ) ∧ baryMap (q u) Z = ∑ j, q u j • Z j := by
    intro u hu
    have hp := (StatFormal.OTFD.Wave7a.oos_quad_affine n K (γ / m) M Z f u (q u) hM).1 (hq u)
    refine ⟨⟨hp.1, fun j => ?_⟩, rfl⟩
    exact StatFormal.OTFD.Bands.band_cap_quadratic n K m _ _ γ (δ j) j u (q u) hγ hm
      ((hδ j).trans (StatFormal.OTFD.Wave14c.gap_le j hu)) hp
  have h1 : ∀ t, certLo (quadCaps m γ δ) Z (mo t) (e t) ≤ edgeLo (fun u => baryMap (q u) Z) A (mo t) (e t) ∧
      edgeUp (fun u => baryMap (q u) Z) A (mo t) (e t) ≤ certUp (quadCaps m γ δ) Z (mo t) (e t) := fun t =>
    ⟨cert_le_edgeLo _ hw _ _, StatFormal.OTFD.Wave14c.edgeUp_le_cert _ hw _ _⟩
  exact ⟨h1, StatFormal.OTFD.Wave14c.band_mono (fun t => (h1 t).1) (fun t => (h1 t).2)⟩

end StatFormal.WaveP1d
