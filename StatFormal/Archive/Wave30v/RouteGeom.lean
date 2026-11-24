import StatFormal.Archive.Wave30v.RouteSup

/-!
# Route — wave 30v geometry: `boundary_contact_argmax`, `boundary_dist_dual`, `boundary_polar_infDist`,
# `boundary_tangent_cone` (untrusted)

* Contact: with `z ∈ A ∩ B`, `h_A(−g) + h_B(g) ≥ ⟨−g, z⟩ + ⟨g, z⟩ = 0`, and `= 0` iff `⟨g, b − a⟩ ≤ 0` on `B − A`.
* Duality: `−h_A(−g) − h_B(g) ≤ ⟨g, a − b⟩ ≤ ‖a − b‖`; equality at `g = (a* − b*)/‖a* − b*‖` for nearest points,
  by the variational inequalities of the projections (`norm_eq_iInf_iff_real_inner_le_zero`, as in Wave 17a).
* Moreau: `p = Π_K x`; the cone gives `⟨x − p, p⟩ = 0` and `x − p ∈ K°`; `g = (x − p)/‖x − p‖` attains.
* Tangent cones: `c(b − z) − d(a − z) = (c + d)(b' − a')` with `b' ∈ B`, `a' ∈ A` (convex combinations with `z`).
-/

set_option linter.style.longLine false

noncomputable section
open Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30v

open StatFormal.TrimmedMMD.Unconditional (setDist)

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma bddAbove_inner_image {S : Set E} (hS : Bornology.IsBounded S) (g : E) :
    BddAbove ((fun s => ⟪g, s⟫) '' S) := by
  obtain ⟨R, hR⟩ := hS.subset_closedBall 0
  refine ⟨‖g‖ * R, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hs' : ‖s‖ ≤ R := mem_closedBall_zero_iff.1 (hR hs)
  exact (real_inner_le_norm g s).trans (mul_le_mul_of_nonneg_left hs' (norm_nonneg g))

lemma le_supportFn {S : Set E} (hS : Bornology.IsBounded S) (g : E) {s : E} (hs : s ∈ S) :
    ⟪g, s⟫ ≤ supportFn S g := le_csSup (bddAbove_inner_image hS g) ⟨s, hs, rfl⟩

lemma supportFn_le {S : Set E} (hne : S.Nonempty) {g : E} {c : ℝ} (h : ∀ s ∈ S, ⟪g, s⟫ ≤ c) :
    supportFn S g ≤ c := csSup_le (hne.image _) (by rintro _ ⟨s, hs, rfl⟩; exact h s hs)

lemma supportFn_zero {S : Set E} (hne : S.Nonempty) : supportFn S 0 = 0 := by
  unfold supportFn
  simp only [inner_zero_left]
  rw [hne.image_const, csSup_singleton]

end

/-- (Route-only, moved from the draft statements by the wave-30v critic: a general library fact with no printed
label.) The contact argmax: if `A ∩ B ≠ ∅` (nonempty bounded `A, B`), then `−h_A(−g) − h_B(g) ≤ 0` for every `g`, with
equality iff `g ∈ (B − A)°`. Hence the value is `0` and its maximisers on the unit ball are `Ball ∩ (B − A)°`. -/
theorem boundary_contact_argmax :
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A B : Set E),
    Bornology.IsBounded A → Bornology.IsBounded B → (A ∩ B).Nonempty →
      ∀ g : E, -supportFn A (-g) - supportFn B g ≤ 0 ∧
        (-supportFn A (-g) - supportFn B g = 0 ↔ g ∈ polarSet (B - A)) := by
  intro E _ _ A B hA hB ⟨z, hzA, hzB⟩ g
  have hAne : A.Nonempty := ⟨z, hzA⟩
  have hBne : B.Nonempty := ⟨z, hzB⟩
  have h1 : ⟪-g, z⟫ ≤ supportFn A (-g) := le_supportFn hA (-g) hzA
  have h2 : ⟪g, z⟫ ≤ supportFn B g := le_supportFn hB g hzB
  rw [inner_neg_left] at h1
  refine ⟨by linarith, ⟨fun h0 => ?_, fun hg => ?_⟩⟩
  · rintro x ⟨b, hb, a, ha, rfl⟩
    have h3 : ⟪-g, a⟫ ≤ supportFn A (-g) := le_supportFn hA (-g) ha
    have h4 : ⟪g, b⟫ ≤ supportFn B g := le_supportFn hB g hb
    rw [inner_neg_left] at h3
    rw [inner_sub_right]
    linarith
  · have h3 : supportFn B g ≤ ⟪g, z⟫ := by
      refine supportFn_le hBne fun b hb => ?_
      have := hg (b - z) ⟨b, hb, z, hzA, rfl⟩
      rw [inner_sub_right] at this
      linarith
    have h4 : supportFn A (-g) ≤ -⟪g, z⟫ := by
      refine supportFn_le hAne fun a ha => ?_
      have := hg (z - a) ⟨z, hzB, a, ha, rfl⟩
      rw [inner_sub_right] at this
      rw [inner_neg_left]
      linarith
    linarith

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma setDist_le' {A B : Set E} {a b : E} (ha : a ∈ A) (hb : b ∈ B) : setDist A B ≤ ‖a - b‖ :=
  csInf_le ⟨0, by rintro _ ⟨a, -, b, -, rfl⟩; exact norm_nonneg _⟩ ⟨a, ha, b, hb, rfl⟩

lemma le_setDist {A B : Set E} (hA : A.Nonempty) (hB : B.Nonempty) {c : ℝ}
    (h : ∀ a ∈ A, ∀ b ∈ B, c ≤ ‖a - b‖) : c ≤ setDist A B := by
  obtain ⟨a, ha⟩ := hA; obtain ⟨b, hb⟩ := hB
  exact le_csInf ⟨_, a, ha, b, hb, rfl⟩ (by rintro _ ⟨a, ha, b, hb, rfl⟩; exact h a ha b hb)

/-- The dual objective at `g` is at most `‖a − b‖` for `‖g‖ ≤ 1`. -/
lemma dual_le_norm {A B : Set E} (hA : Bornology.IsBounded A) (hB : Bornology.IsBounded B) {g : E}
    (hg : ‖g‖ ≤ 1) {a b : E} (ha : a ∈ A) (hb : b ∈ B) :
    -supportFn A (-g) - supportFn B g ≤ ‖a - b‖ := by
  have h1 : ⟪-g, a⟫ ≤ supportFn A (-g) := le_supportFn hA (-g) ha
  have h2 : ⟪g, b⟫ ≤ supportFn B g := le_supportFn hB g hb
  rw [inner_neg_left] at h1
  have h3 : ⟪g, a - b⟫ ≤ ‖a - b‖ :=
    (real_inner_le_norm g (a - b)).trans (by nlinarith [norm_nonneg (a - b)])
  rw [inner_sub_right] at h3
  linarith

end

theorem boundary_dist_dual : Claims.boundary_dist_dual := by
  intro E _ _ _ A B hA hB hAne hBne hAc hBc hAcv hBcv hAeq hBeq
  have hAb := hAc.isBounded
  have hBb := hBc.isBounded
  have hval : ∀ g : Ball E, dualObj hA hB g = -supportFn A (-(g : E)) - supportFn B g := by
    intro g; simp [dualObj, hAeq, hBeq, ballNeg]
  apply le_antisymm
  · -- nearest points
    obtain ⟨p, ⟨hpA, hpB⟩, hpmin⟩ := (hAc.prod hBc).exists_isMinOn (hAne.prod hBne)
      ((continuous_fst.sub continuous_snd).norm.continuousOn)
    set a := p.1; set b := p.2
    have hab : setDist A B = ‖a - b‖ := by
      refine le_antisymm (setDist_le' hpA hpB) (le_setDist hAne hBne fun a' ha' b' hb' => ?_)
      exact hpmin (show (a', b') ∈ A ×ˢ B from ⟨ha', hb'⟩)
    rw [hab]
    unfold valueFn
    by_cases hd : ‖a - b‖ = 0
    · rw [hd]
      have : dualObj hA hB ⟨0, by simp⟩ = 0 := by
        rw [hval]; simp [supportFn_zero hAne, supportFn_zero hBne]
      rw [← this]; exact le_supFun _ _
    · have hdpos : 0 < ‖a - b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
      set d := ‖a - b‖ with hdd
      have hvA : ∀ w ∈ A, ⟪b - a, w - a⟫ ≤ 0 := by
        refine (norm_eq_iInf_iff_real_inner_le_zero hAcv hpA).1 ?_
        have : Nonempty A := ⟨⟨a, hpA⟩⟩
        have hbdd : BddBelow (Set.range fun w : A => ‖b - (w : E)‖) :=
          ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
        refine le_antisymm (le_ciInf fun w => ?_) (ciInf_le hbdd ⟨a, hpA⟩)
        rw [norm_sub_rev b a, norm_sub_rev b]
        exact hab.symm.trans_le (setDist_le' w.2 hpB)
      have hvB : ∀ w ∈ B, ⟪a - b, w - b⟫ ≤ 0 := by
        refine (norm_eq_iInf_iff_real_inner_le_zero hBcv hpB).1 ?_
        have : Nonempty B := ⟨⟨b, hpB⟩⟩
        have hbdd : BddBelow (Set.range fun w : B => ‖a - (w : E)‖) :=
          ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
        refine le_antisymm (le_ciInf fun w => ?_) (ciInf_le hbdd ⟨b, hpB⟩)
        exact hab.symm.trans_le (setDist_le' hpA w.2)
      set f := d⁻¹ • (a - b) with hf
      have hfn : ‖f‖ = 1 := by
        rw [hf, norm_smul, norm_inv, norm_norm, ← hdd]; exact inv_mul_cancel₀ hdpos.ne'
      have hfA : supportFn A (-f) ≤ -⟪f, a⟫ := by
        refine supportFn_le hAne fun w hw => ?_
        have := hvA w hw
        have h2 : ⟪f, w⟫ - ⟪f, a⟫ = d⁻¹ * (-⟪b - a, w - a⟫) := by
          rw [← inner_sub_right, hf, real_inner_smul_left, ← inner_neg_left, neg_sub]
        rw [inner_neg_left]
        nlinarith [inv_pos.2 hdpos]
      have hfB : supportFn B f ≤ ⟪f, b⟫ := by
        refine supportFn_le hBne fun w hw => ?_
        have := hvB w hw
        have h2 : ⟪f, w⟫ - ⟪f, b⟫ = d⁻¹ * ⟪a - b, w - b⟫ := by
          rw [← inner_sub_right, hf, real_inner_smul_left]
        nlinarith [inv_pos.2 hdpos]
      have hfab : ⟪f, a⟫ - ⟪f, b⟫ = d := by
        rw [← inner_sub_right, hf, real_inner_smul_left, real_inner_self_eq_norm_sq, ← hdd]
        field_simp
      have hmem : f ∈ closedBall (0 : E) 1 := by rw [mem_closedBall_zero_iff, hfn]
      have := le_supFun (dualObj hA hB) ⟨f, hmem⟩
      rw [hval] at this
      simp only at this
      linarith
  · unfold valueFn
    haveI : Nonempty (Ball E) := ⟨⟨0, by simp⟩⟩
    refine supFun_le fun g => ?_
    rw [hval]
    refine le_setDist hAne hBne fun a ha b hb => ?_
    exact dual_le_norm hAb hBb (mem_closedBall_zero_iff.1 g.2) ha hb

/-- (Route-only, moved from the draft statements by the wave-30v critic: a general library fact with no printed
label.) Moreau-type identity (why the polar appears): for a nonempty closed convex cone `K` in a real Hilbert space,
`sup {⟨g, x⟩ : g ∈ K°, ‖g‖ ≤ 1} = dist(x, K)` (`= ‖Π_{K°} x‖`). -/
theorem boundary_polar_infDist :
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (K : Set E),
    K.Nonempty → IsClosed K → Convex ℝ K → (∀ c : ℝ, 0 ≤ c → ∀ v ∈ K, c • v ∈ K) →
      ∀ x : E, sSup ((fun g => ⟪g, x⟫) '' (polarSet K ∩ closedBall 0 1)) = infDist x K := by
  intro E _ _ _ K hne hcl hcv hcone x
  obtain ⟨p, hpK, hp⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hcv x
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero hcv hpK).1 hp
  have hinf : infDist x K = ‖x - p‖ := by
    rw [infDist_eq_iInf, hp]
    simp only [dist_eq_norm]
  have h0K : (0 : E) ∈ K := by
    obtain ⟨k0, hk0⟩ := hne
    simpa using hcone 0 le_rfl k0 hk0
  have h2p : (2 : ℝ) • p ∈ K := hcone 2 (by norm_num) p hpK
  have hpp : ⟪x - p, p⟫ = 0 := by
    have a1 := hvar 0 h0K
    have a2 := hvar _ h2p
    rw [zero_sub, inner_neg_right] at a1
    rw [show (2 : ℝ) • p - p = p by module] at a2
    linarith
  have hpol : x - p ∈ polarSet K := by
    intro k hk
    have hkp : k + p ∈ K := by
      have hmid : (1 / 2 : ℝ) • k + (1 / 2 : ℝ) • p ∈ K := hcv hk hpK (by norm_num) (by norm_num) (by norm_num)
      have := hcone 2 (by norm_num) _ hmid
      rwa [show (2 : ℝ) • ((1 / 2 : ℝ) • k + (1 / 2 : ℝ) • p) = k + p by module] at this
    have := hvar _ hkp
    rwa [add_sub_cancel_right] at this
  rw [hinf]
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · by_cases hd : ‖x - p‖ = 0
    · refine ⟨0, ⟨fun _ _ => by simp, by simp⟩, ?_⟩
      simp [hd]
    · have hdpos : 0 < ‖x - p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
      refine ⟨‖x - p‖⁻¹ • (x - p), ⟨fun k hk => ?_, ?_⟩, ?_⟩
      · rw [real_inner_smul_left]
        exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (norm_nonneg _)) (hpol k hk)
      · rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hd]
      · simp only
        rw [real_inner_smul_left, show x = (x - p) + p by abel, inner_add_right, ← show x = (x - p) + p by abel,
          hpp, add_zero, real_inner_self_eq_norm_sq]
        field_simp
  · rintro _ ⟨g, ⟨hgK, hgB⟩, rfl⟩
    have hg1 : ‖g‖ ≤ 1 := mem_closedBall_zero_iff.1 hgB
    have h1 : ⟪g, p⟫ ≤ 0 := hgK p hpK
    have h2 : ⟪g, x - p⟫ ≤ ‖x - p‖ :=
      (real_inner_le_norm g (x - p)).trans (by nlinarith [norm_nonneg (x - p)])
    have : ⟪g, x⟫ = ⟪g, x - p⟫ + ⟪g, p⟫ := by rw [← inner_add_right, sub_add_cancel]
    linarith

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma closure_sub_closure_subset (X Y : Set E) : closure X - closure Y ⊆ closure (X - Y) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  have hab : (a, b) ∈ closure (X ×ˢ Y) := by rw [closure_prod_eq]; exact ⟨ha, hb⟩
  exact map_mem_closure (f := fun q : E × E => q.1 - q.2) (continuous_fst.sub continuous_snd) hab
    (fun q hq => ⟨q.1, hq.1, q.2, hq.2, rfl⟩)

lemma coneHull_sub_eq_subset {A B : Set E} {z : E} (hA : Convex ℝ A) (hB : Convex ℝ B) (hzA : z ∈ A)
    (hzB : z ∈ B) :
    {v | ∃ c : ℝ, 0 ≤ c ∧ ∃ s ∈ B, v = c • (s - z)} - {v | ∃ c : ℝ, 0 ≤ c ∧ ∃ s ∈ A, v = c • (s - z)} ⊆
      coneHull (B - A) := by
  rintro _ ⟨_, ⟨c, hc, b, hb, rfl⟩, _, ⟨d, hd, a, ha, rfl⟩, rfl⟩
  by_cases hs : c + d = 0
  · have hc0 : c = 0 := by linarith
    have hd0 : d = 0 := by linarith
    exact ⟨0, le_rfl, z - z, ⟨z, hzB, z, hzA, rfl⟩, by simp [hc0, hd0]⟩
  · have hspos : 0 < c + d := lt_of_le_of_ne (by linarith) (Ne.symm hs)
    refine ⟨c + d, hspos.le, (c / (c + d)) • b + (d / (c + d)) • z - ((d / (c + d)) • a + (c / (c + d)) • z),
      ⟨_, hB hb hzB (by positivity) (by positivity) (by field_simp), _,
        hA ha hzA (by positivity) (by positivity) (by field_simp; ring), rfl⟩, ?_⟩
    have e1 : (c + d) * (c / (c + d)) = c := by field_simp
    have e2 : (c + d) * (d / (c + d)) = d := by field_simp
    show c • (b - z) - d • (a - z) = _
    simp only [smul_sub, smul_add, smul_smul, e1, e2]
    abel

lemma coneHull_subset_sub {A B : Set E} {z : E} :
    coneHull (B - A) ⊆
      {v | ∃ c : ℝ, 0 ≤ c ∧ ∃ s ∈ B, v = c • (s - z)} - {v | ∃ c : ℝ, 0 ≤ c ∧ ∃ s ∈ A, v = c • (s - z)} := by
  rintro _ ⟨c, hc, _, ⟨b, hb, a, ha, rfl⟩, rfl⟩
  refine ⟨c • (b - z), ⟨c, hc, b, hb, rfl⟩, c • (a - z), ⟨c, hc, a, ha, rfl⟩, ?_⟩
  show c • (b - z) - c • (a - z) = c • (b - a)
  rw [← smul_sub]; congr 1; abel

end

theorem boundary_tangent_cone : Claims.boundary_tangent_cone := by
  intro E _ _ A B z hA hB hzA hzB
  apply le_antisymm
  · refine closure_minimal ((closure_sub_closure_subset _ _).trans ?_) isClosed_closure
    exact closure_mono (coneHull_sub_eq_subset hA hB hzA hzB)
  · refine closure_mono ((coneHull_subset_sub (z := z)).trans ?_)
    exact Set.sub_subset_sub subset_closure subset_closure

end StatFormal.Wave30v
