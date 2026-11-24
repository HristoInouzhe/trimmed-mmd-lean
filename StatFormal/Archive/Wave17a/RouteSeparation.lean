import StatFormal.Archive.Wave17a.Statements

/-!
# Route: TM `lem:separation` (untrusted)

* The inequality: `⟨f,a⟩ − ⟨f,b⟩ = ⟨f,a−b⟩ ≤ ‖a − b‖` for `‖f‖ ≤ 1`, then infimum over pairs.
* Nearest points: `(a, b) ↦ ‖a − b‖` is lower semicontinuous on `WeakSpace × WeakSpace` (it is a supremum of
  weakly continuous linear functionals), so it attains its minimum on the compact `A' × B'`.
* Attainment: the variational inequalities of the nearest points (`norm_eq_iInf_iff_real_inner_le_zero`) make
  `a*` minimise `⟨f*,·⟩` on `A` and `b*` maximise it on `B`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Filter Topology Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave17a

open StatFormal.TrimmedMMD.Unconditional (setDist)

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma setDist_bdd (A B : Set H) : BddBelow {r | ∃ a ∈ A, ∃ b ∈ B, r = ‖a - b‖} :=
  ⟨0, by rintro r ⟨a, -, b, -, rfl⟩; exact norm_nonneg _⟩

lemma setDist_le {A B : Set H} {a b : H} (ha : a ∈ A) (hb : b ∈ B) : setDist A B ≤ ‖a - b‖ :=
  csInf_le (setDist_bdd A B) ⟨a, ha, b, hb, rfl⟩

lemma setDist_nonneg (A B : Set H) (hA : A.Nonempty) (hB : B.Nonempty) : 0 ≤ setDist A B := by
  obtain ⟨a, ha⟩ := hA; obtain ⟨b, hb⟩ := hB
  exact le_csInf ⟨_, a, ha, b, hb, rfl⟩ (by rintro r ⟨a, -, b, -, rfl⟩; exact norm_nonneg _)

lemma ereal_le_coe_sInf {x : EReal} {T : Set ℝ} (hT : T.Nonempty) (h : ∀ r ∈ T, x ≤ (r : EReal)) :
    x ≤ ((sInf T : ℝ) : EReal) := by
  induction x using EReal.rec with
  | bot => exact bot_le
  | top => obtain ⟨r, hr⟩ := hT; exact absurd (h r hr) (by simp)
  | coe y => exact EReal.coe_le_coe_iff.2 (le_csInf hT fun r hr => EReal.coe_le_coe_iff.1 (h r hr))

end

theorem separation : Claims.separation := by
  intro H _ _ A B f hA hB hf
  unfold sepVal setDist
  obtain ⟨a₀, ha₀⟩ := hA; obtain ⟨b₀, hb₀⟩ := hB
  refine ereal_le_coe_sInf ⟨_, a₀, ha₀, b₀, hb₀, rfl⟩ ?_
  rintro r ⟨a, ha, b, hb, rfl⟩
  have h1 : (⨅ a ∈ A, ((⟪f, a⟫ : ℝ) : EReal)) ≤ ((⟪f, a⟫ : ℝ) : EReal) :=
    biInf_le (fun x => ((⟪f, x⟫ : ℝ) : EReal)) ha
  have h2 : ((⟪f, b⟫ : ℝ) : EReal) ≤ ⨆ b ∈ B, ((⟪f, b⟫ : ℝ) : EReal) :=
    le_biSup (fun x => ((⟪f, x⟫ : ℝ) : EReal)) hb
  refine (EReal.sub_le_sub h1 h2).trans ?_
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff, ← inner_sub_right]
  calc ⟪f, a - b⟫ ≤ ‖f‖ * ‖a - b‖ := real_inner_le_norm _ _
    _ ≤ 1 * ‖a - b‖ := by gcongr
    _ = ‖a - b‖ := one_mul _

lemma weak_inner_continuous {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (y : H) :
    Continuous fun w : WeakSpace ℝ H => ⟪y, (toWeakSpace ℝ H).symm w⟫ :=
  WeakBilin.eval_continuous (topDualPairing ℝ H).flip (innerSL ℝ y)

theorem separation_nearest_exists : Claims.separation_nearest_exists := by
  intro H _ _ A B hA hB hAc hBc
  let F : WeakSpace ℝ H × WeakSpace ℝ H → ℝ :=
    fun p => ‖(toWeakSpace ℝ H).symm p.1 - (toWeakSpace ℝ H).symm p.2‖
  have hF : LowerSemicontinuous F := by
    intro p c hc
    by_cases hc0 : c < 0
    · exact Eventually.of_forall fun p' => hc0.trans_le (norm_nonneg _)
    push Not at hc0
    set x := (toWeakSpace ℝ H).symm p.1 - (toWeakSpace ℝ H).symm p.2 with hx
    have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hc0 hc
    set y := ‖x‖⁻¹ • x
    let g : WeakSpace ℝ H × WeakSpace ℝ H → ℝ :=
      fun p' => ⟪y, (toWeakSpace ℝ H).symm p'.1⟫ - ⟪y, (toWeakSpace ℝ H).symm p'.2⟫
    have hg : Continuous g :=
      ((weak_inner_continuous y).comp continuous_fst).sub ((weak_inner_continuous y).comp continuous_snd)
    have hgp : g p = ‖x‖ := by
      show ⟪y, _⟫ - ⟪y, _⟫ = _
      rw [← inner_sub_right, ← hx, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    have hev : ∀ᶠ p' in 𝓝 p, c < g p' := hg.continuousAt.eventually (lt_mem_nhds (by rw [hgp]; exact hc))
    filter_upwards [hev] with p' hp'
    refine hp'.trans_le ?_
    simp only [g, F, ← inner_sub_right]
    have hy : ‖y‖ = 1 := by
      simp only [y, norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ hxpos.ne'
    calc _ ≤ ‖y‖ * ‖(toWeakSpace ℝ H).symm p'.1 - (toWeakSpace ℝ H).symm p'.2‖ := real_inner_le_norm _ _
      _ = _ := by rw [hy, one_mul]
  have hne : ((toWeakSpace ℝ H '' A) ×ˢ (toWeakSpace ℝ H '' B)).Nonempty :=
    (hA.image _).prod (hB.image _)
  obtain ⟨p, hp, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne (hAc.prod hBc) (hF.lowerSemicontinuousOn _)
  obtain ⟨⟨a, ha, hpa⟩, ⟨b, hb, hpb⟩⟩ := hp
  refine ⟨a, ha, b, hb, ?_⟩
  have hFp : F p = ‖a - b‖ := by simp [F, ← hpa, ← hpb]
  apply le_antisymm _ (setDist_le ha hb)
  refine le_csInf ⟨_, a, ha, b, hb, rfl⟩ ?_
  rintro r ⟨a', ha', b', hb', rfl⟩
  have := hmin (show (toWeakSpace ℝ H a', toWeakSpace ℝ H b') ∈ _ from ⟨⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩⟩)
  simp only [mem_setOf_eq, F, LinearEquiv.symm_apply_apply] at this
  rw [← hFp]; exact this

theorem separation_attained : Claims.separation_attained := by
  intro H _ _ _ A B a b hAconv hBconv _ _ hpos ha hb hab
  set d := ‖a - b‖ with hd
  have hdpos : 0 < d := hab ▸ hpos
  have hnorm : ‖d⁻¹ • (a - b)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, ← hd]; exact inv_mul_cancel₀ hdpos.ne'
  -- variational inequalities
  have hvA : ∀ w ∈ A, ⟪b - a, w - a⟫ ≤ 0 := by
    refine (norm_eq_iInf_iff_real_inner_le_zero hAconv ha).1 ?_
    have : Nonempty A := ⟨⟨a, ha⟩⟩
    have hbdd : BddBelow (Set.range fun w : A => ‖b - (w : H)‖) := ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    refine le_antisymm (le_ciInf fun w => ?_) (ciInf_le hbdd ⟨a, ha⟩)
    rw [norm_sub_rev b a, norm_sub_rev b]
    exact (hab.trans_le (setDist_le w.2 hb))
  have hvB : ∀ w ∈ B, ⟪a - b, w - b⟫ ≤ 0 := by
    refine (norm_eq_iInf_iff_real_inner_le_zero hBconv hb).1 ?_
    have : Nonempty B := ⟨⟨b, hb⟩⟩
    have hbdd : BddBelow (Set.range fun w : B => ‖a - (w : H)‖) := ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    refine le_antisymm (le_ciInf fun w => ?_) (ciInf_le hbdd ⟨b, hb⟩)
    exact (hab.trans_le (setDist_le ha w.2))
  set f := d⁻¹ • (a - b)
  have hinf : (⨅ x ∈ A, ((⟪f, x⟫ : ℝ) : EReal)) = ((⟪f, a⟫ : ℝ) : EReal) := by
    refine le_antisymm (biInf_le (fun x => ((⟪f, x⟫ : ℝ) : EReal)) ha) (le_iInf₂ fun w hw => EReal.coe_le_coe_iff.2 ?_)
    have := hvA w hw
    have h2 : ⟪f, w⟫ - ⟪f, a⟫ = d⁻¹ * (-⟪b - a, w - a⟫) := by
      rw [← inner_sub_right, real_inner_smul_left, ← inner_neg_left, neg_sub]
    nlinarith [inv_pos.2 hdpos]
  have hsup : (⨆ x ∈ B, ((⟪f, x⟫ : ℝ) : EReal)) = ((⟪f, b⟫ : ℝ) : EReal) := by
    refine le_antisymm (iSup₂_le fun w hw => EReal.coe_le_coe_iff.2 ?_) (le_biSup (fun x => ((⟪f, x⟫ : ℝ) : EReal)) hb)
    have := hvB w hw
    have h2 : ⟪f, w⟫ - ⟪f, b⟫ = d⁻¹ * ⟪a - b, w - b⟫ := by
      rw [← inner_sub_right, real_inner_smul_left]
    nlinarith [inv_pos.2 hdpos]
  refine ⟨hnorm, ?_⟩
  unfold sepVal
  rw [hinf, hsup, ← EReal.coe_sub, ← hab, EReal.coe_eq_coe_iff, ← inner_sub_right]
  simp only [f, real_inner_smul_left, real_inner_self_eq_norm_sq, ← hd]
  field_simp

end StatFormal.Wave17a
