import StatFormal.Archive.OTFD.Wave14c.RouteCommon

/-!
# Route: B `prop:band-nesting` (untrusted)

`A ⊆ A'` shrinks the feasible set of the minimisation defining `δ_j` (`csInf_le_csInf`), the caps are
antitone functions of the gaps, and the knapsack value is a supremum over the capped simplex, which grows with the
caps. Dual caps: `σ_A ≤ σ_{A'}` (`csSup_le_csSup`, `A'` bounded), so each dual candidate's bound decreases.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory Set Finset Matrix

namespace StatFormal.OTFD.Wave14c

open StatFormal.OTFD.Bands (simplex gap score)
open StatFormal.OTFD.Bands2 (hsup edgeUp edgeLo band)
open StatFormal.OTFD.Wave2 (cappedSimplex)

variable {n K : ℕ}

lemma capped_mono {κ κ' : Fin n → ℝ} (h : ∀ j, κ j ≤ κ' j) : cappedSimplex κ ⊆ cappedSimplex κ' :=
  fun _ hq => ⟨hq.1, fun j => (hq.2 j).trans (h j)⟩

lemma knapUp_mono {κ κ' : Fin n → ℝ} (h : ∀ j, κ j ≤ κ' j) (c : Fin n → ℝ) : knapUp κ c ≤ knapUp κ' c :=
  biSup_mono fun _ hq => capped_mono h hq

lemma knapLo_mono {κ κ' : Fin n → ℝ} (h : ∀ j, κ j ≤ κ' j) (c : Fin n → ℝ) : knapLo κ' c ≤ knapLo κ c :=
  biInf_mono fun _ hq => capped_mono h hq

lemma certUp_mono {κ κ' : Fin n → ℝ} (h : ∀ j, κ j ≤ κ' j) (Z : Fin n → Fin K → ℝ) (mo : ℝ) (v : Fin K → ℝ) :
    certUp κ Z mo v ≤ certUp κ' Z mo v := by
  unfold certUp; gcongr; exact knapUp_mono h _

lemma certLo_mono {κ κ' : Fin n → ℝ} (h : ∀ j, κ j ≤ κ' j) (Z : Fin n → Fin K → ℝ) (mo : ℝ) (v : Fin K → ℝ) :
    certLo κ' Z mo v ≤ certLo κ Z mo v := by
  unfold certLo; gcongr; exact knapLo_mono h _

lemma band_mono {T : Type} {lo up lo' up' : T → EReal} (hlo : ∀ t, lo' t ≤ lo t) (hup : ∀ t, up t ≤ up' t) :
    band lo up ⊆ band lo' up' :=
  fun _ hy t => ⟨(hlo t).trans (hy t).1, (hy t).2.trans (hup t)⟩

lemma entCaps_mono {ε : ℝ} (hε : 0 < ε) {δ δ' : Fin n → ℝ} (h : ∀ j, δ' j ≤ δ j) :
    ∀ j, entCaps ε δ j ≤ entCaps ε δ' j := by
  intro j; unfold entCaps
  exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (neg_le_neg (h j)) hε.le)

lemma quadCaps_mono {m : ℕ} {γ : ℝ} (hγ : 0 < γ) {δ δ' : Fin n → ℝ} (h : ∀ j, δ' j ≤ δ j) :
    ∀ j, quadCaps m γ δ j ≤ quadCaps m γ δ' j := by
  intro j; unfold quadCaps
  refine max_le_max le_rfl (sub_le_sub_left ?_ 1)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (h j) (Nat.cast_nonneg m)) hγ.le

theorem nesting_gap : Claims.nesting_gap := by
  intro n K a b A A' j hA hAA'
  exact csInf_le_csInf (gap_bdd a b A' j) (hA.image _) (image_mono hAA')

theorem nesting_knapsack : Claims.nesting_knapsack := by
  intro n κ κ' c h
  exact ⟨knapUp_mono h c, knapLo_mono h c⟩

lemma gap_anti {a : Fin n → ℝ} {b : Fin n → Fin K → ℝ} {A A' : Set (Fin K → ℝ)} (hA : A.Nonempty) (h : A ⊆ A') :
    ∀ j, gap a b A' j ≤ gap a b A j :=
  fun j => nesting_gap n K a b A A' j hA h

theorem nesting_band_ent : Claims.nesting_band_ent := by
  intro n K a b Z A A' ε T mo e hA hAA' hε
  have hk := entCaps_mono hε (gap_anti (a := a) (b := b) hA hAA')
  exact ⟨hk, fun t => certUp_mono hk Z _ _, fun t => certLo_mono hk Z _ _,
    band_mono (fun t => certLo_mono hk Z _ _) (fun t => certUp_mono hk Z _ _)⟩

theorem nesting_band_quad : Claims.nesting_band_quad := by
  intro n K m a b Z A A' γ T mo e hA hAA' hγ _
  have hk := quadCaps_mono (m := m) hγ (gap_anti (a := a) (b := b) hA hAA')
  exact ⟨hk, fun t => certUp_mono hk Z _ _, fun t => certLo_mono hk Z _ _,
    band_mono (fun t => certLo_mono hk Z _ _) (fun t => certUp_mono hk Z _ _)⟩

theorem nesting_exact : Claims.nesting_exact := by
  intro K T Q A A' mo e h
  have hs : ∀ (v : Fin K → ℝ), hsup Q A v ≤ hsup Q A' v := fun v => biSup_mono fun _ hu => h hu
  have hup : ∀ t, edgeUp Q A (mo t) (e t) ≤ edgeUp Q A' (mo t) (e t) := by
    intro t; unfold edgeUp; gcongr; exact hs _
  have hlo : ∀ t, edgeLo Q A' (mo t) (e t) ≤ edgeLo Q A (mo t) (e t) := by
    intro t; unfold edgeLo; exact EReal.sub_le_sub le_rfl (hs _)
  exact ⟨hup, hlo, band_mono hlo hup⟩

lemma suppFnR_mono {A A' : Set (Fin K → ℝ)} (hA : A.Nonempty) (h : A ⊆ A') (hb : Bornology.IsBounded A')
    (v : Fin K → ℝ) : suppFnR A v ≤ suppFnR A' v := by
  have hcont : Continuous fun u : Fin K → ℝ => v ⬝ᵥ u := by fun_prop
  have hbdd : BddAbove ((fun u => v ⬝ᵥ u) '' A') :=
    ((hb.isCompact_closure.image hcont).bddAbove).mono (image_mono subset_closure)
  exact csSup_le_csSup hbdd (hA.image _) (image_mono h)

theorem nesting_dual : Claims.nesting_dual := by
  intro n K N m a b Z A A' W ε γ T mo e hA hAA' hb _ _ hε hγ _
  have hd : ∀ j, dualGap a b A' W j ≤ dualGap a b A W j := by
    intro j; unfold dualGap
    exact ciSup_mono (Set.finite_range _).bddAbove fun i =>
      sub_le_sub_left (suppFnR_mono hA hAA' hb _) _
  have hk := entCaps_mono hε hd
  have hq := quadCaps_mono (m := m) hγ hd
  exact ⟨hd, fun t => certUp_mono hk Z _ _, fun t => certLo_mono hk Z _ _,
    fun t => certUp_mono hq Z _ _, fun t => certLo_mono hq Z _ _⟩

end StatFormal.OTFD.Wave14c
