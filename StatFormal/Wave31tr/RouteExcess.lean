import StatFormal.Wave31tr.RouteExcessSetting
import StatFormal.Wave30tz.Proofs
import StatFormal.Wave30tv.Proofs
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs

/-!
# Wave 31tr route (E1): Lemmas S4.17–S4.18 and Proposition 5.10 (i)–(ii) (untrusted)

* `excess_bathtub_route` (T38): the bathtub conditions `part_threshold_P/Q` and the library bathtub for sub-measures
  (`ExcessRamp.bathtub_le/ge`);
* `excess_identity_route` (T39): the library excess identity of a ramp (`ExcessRamp.ramp_excess_eq`) with
  `∫ f⋆ dP′ − ∫ f⋆ dQ′ = (1−α)D_α` (`parts_inner_diff`);
* `excess_i_route` (T40): (i-1) from T39 (the overshoot integrals are nonnegative); (i-2) Cauchy–Schwarz on the parts of mass
  `1 − α′` of any points of `𝒞_{α′}(P)`, `𝒞_{α′}(Q)` and T38(a), then the infimum; (Pr-0) the certified `pop_ramp_rkhs` and
  `eq:zeroeq`;
* `excess_ii_route` (T41): T40 (i-2) at `α′ = α⋆ − 2ε`, the power bounds, T40 (i-1), and the certified `lem_ramp_iii`.
In every (Pr) form, `D_α > 0` comes from `eq:zeroeq` (or from the margin in T41) and `u⋆ < t⋆` from `pop_ramp_rkhs`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31tr.RouteExcess

open StatFormal.Wave30tq StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.ZeroSet

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Common facts of the printed form -/

lemma dpop_nonneg (φ : 𝒳 → H) (P Q : Measure 𝒳) (α : ℝ) : 0 ≤ Dpop φ P Q α :=
  Real.sInf_nonneg fun _ ⟨_, _, _, _, hr⟩ => hr ▸ norm_nonneg _

/-- `D_α > 0` for `α < α⋆` under (A3) (`eq:zeroeq`). -/
lemma dpop_pos_of_lt_tv [CompleteSpace H] [TopologicalSpace.SeparableSpace H] {P Q : Measure 𝒳}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ α : ℝ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hchar : Characteristic φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hαtv : α < StatFormal.Distances.tvDist P Q) : 0 < Dpop φ P Q α := by
  have hz := StatFormal.TrimmedMMD.ZeroSet.zeroeq 𝒳 H P Q φ κ α hφ hκ hchar hα0 hα1
  rcases (dpop_nonneg φ P Q α).lt_or_eq with h | h
  · exact h
  · exact absurd (hz.1 h.symm) (not_le.2 hαtv)

/-- The printed cuts are `D_α` apart (certified `pop_ramp_rkhs`, with `D_φ = 2κ`). -/
lemma pop_gap [CompleteSpace H] {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {κ α : ℝ} {a b : H} {t u : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (ha : a ∈ region φ α P) (hb : b ∈ region φ α Q) (hab : ‖a - b‖ = Dpop φ P Q α) (hD : 0 < Dpop φ P Q α)
    (ht : IsLeast {q | IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) q} t)
    (hu : IsGreatest {q | IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α q} u) :
    Dpop φ P Q α ≤ t - u := by
  have hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ 2 * κ := fun x x' => (norm_sub_le _ _).trans (by linarith [hκ x, hκ x'])
  exact (StatFormal.Wave30tz.pop_ramp_rkhs 𝒳 H P Q φ κ (2 * κ) α a b t u hφ hκ hDφ hα0 hα1 ha hb hab hD ht hu).1

/-! ### T38: Lemma S4.17 -/

/-- Lemma S4.17, general form. -/
theorem bathtub_G [CompleteSpace H] {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {κ α : ℝ} {a b : H} {g h : 𝒳 → ℝ} {t u : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hD : 0 < Dpop φ P Q α) (hg : IsTrimDensity P α g) (ha : a = ∫ x, g x • φ x ∂P)
    (hh : IsTrimDensity Q α h) (hb : b = ∫ y, h y • φ y ∂Q) (hab : ‖a - b‖ = Dpop φ P Q α)
    (ht : IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) t)
    (hu : IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α u) :
    (∀ P'' : Measure 𝒳, P'' ≤ P →
        (∫ x, ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ ∂(trimMeasure P fun x => (1 - α) * g x)) +
            t * (P''.real univ - (1 - α)) ≤
          ∫ x, ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ ∂P'') ∧
      (∀ Q'' : Measure 𝒳, Q'' ≤ Q →
        ∫ y, ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ ∂Q'' ≤
          (∫ y, ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ ∂(trimMeasure Q fun y => (1 - α) * h y)) +
            u * (Q''.real univ - (1 - α))) ∧
      (trimMeasure P fun x => (1 - α) * g x).restrict {x | ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ < t} =
        P.restrict {x | ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ < t} ∧
      (trimMeasure P fun x => (1 - α) * g x) {x | t < ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ} = 0 ∧
      (trimMeasure Q fun y => (1 - α) * h y).restrict {y | u < ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ} =
        Q.restrict {y | u < ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ} ∧
      (trimMeasure Q fun y => (1 - α) * h y) {y | ⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ < u} = 0 := by
  have hc0 : 0 < ‖a - b‖ := hab ▸ hD
  have haR : a ∈ region φ α P := ⟨g, hg.1, hg.2.1, hg.2.2, ha⟩
  have hbR : b ∈ region φ α Q := ⟨h, hh.1, hh.2.1, hh.2.2, hb⟩
  obtain ⟨hP1, hP2⟩ := part_threshold_P hφ hκ hα0 hα1 hD hg ha hbR hab ht
  obtain ⟨hQ1, hQ2⟩ := part_threshold_Q hφ hκ hα0 hα1 hD hh hb haR hab hu
  have := part_finite hα1 hg
  have := part_finite hα1 hh
  have hFm := measurable_wit hφ (‖a - b‖⁻¹ • (a - b))
  have hFb := abs_wit_le hκ (norm_dir hc0)
  refine ⟨fun P'' hP'' => ?_, fun Q'' hQ'' => ?_, hP1, hP2, hQ1, hQ2⟩
  · have := StatFormal.ExcessRamp.bathtub_le hFm hFb hP1 hP2 P'' hP''
    rwa [part_real_univ hα1 hg] at this
  · have := StatFormal.ExcessRamp.bathtub_ge hFm hFb hQ1 hQ2 Q'' hQ''
    rwa [part_real_univ hα1 hh] at this

theorem excess_bathtub_route : Claims.excess_bathtub := by
  refine ⟨?_, ?_⟩
  · intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α a b g h t u hφ hκ hα0 hα1 hD hg ha hh hb hab ht hu
    exact bathtub_G hφ hκ hα0 hα1 hD hg ha hh hb hab ht hu
  · intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α a b g h t u hφ hκ hchar _ htv1 hα0 hαtv _ _ hab ht hu hg ha hh hb
    have hα1 : α < 1 := hαtv.trans htv1
    exact bathtub_G hφ hκ hα0 hα1 (dpop_pos_of_lt_tv hφ hκ hchar hα0 hα1 hαtv) hg ha hh hb hab ht.1 hu.1

/-! ### T39: Lemma S4.18 -/

/-- Lemma S4.18, general form. -/
theorem identity_G [CompleteSpace H] {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {κ α : ℝ} {a b : H} {t u : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hD : 0 < Dpop φ P Q α) (ha : a ∈ region φ α P) (hb : b ∈ region φ α Q) (hab : ‖a - b‖ = Dpop φ P Q α)
    (ht : IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) t)
    (hu : IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α u) (hut : u < t) :
    (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
        (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - α =
      (StatFormal.Wave31ti.uPath φ P Q α + (∫ x, max (u - ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) 0 ∂P) +
          ∫ y, max (⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ - t) 0 ∂Q) / (t - u) := by
  obtain ⟨g, hgm, hgb, hgi, ha'⟩ := ha
  obtain ⟨h, hhm, hhb, hhi, hb'⟩ := hb
  have hg : IsTrimDensity P α g := ⟨hgm, hgb, hgi⟩
  have hh : IsTrimDensity Q α h := ⟨hhm, hhb, hhi⟩
  have hc0 : 0 < ‖a - b‖ := hab ▸ hD
  have haR : a ∈ region φ α P := ⟨g, hg.1, hg.2.1, hg.2.2, ha'⟩
  have hbR : b ∈ region φ α Q := ⟨h, hh.1, hh.2.1, hh.2.2, hb'⟩
  obtain ⟨hP1, hP2⟩ := part_threshold_P hφ hκ hα0 hα1 hD hg ha' hbR hab ht
  obtain ⟨hQ1, hQ2⟩ := part_threshold_Q hφ hκ hα0 hα1 hD hh hb' haR hab hu
  have := part_finite hα1 hg
  have := part_finite hα1 hh
  have hFm := measurable_wit hφ (‖a - b‖⁻¹ • (a - b))
  have hFb := abs_wit_le hκ (norm_dir hc0)
  have key := StatFormal.ExcessRamp.ramp_excess_eq hFm hFb hut hP1 hP2 hQ1 hQ2
    (by rw [part_real_univ hα1 hh, part_real_univ hα1 hg])
  rw [part_real_univ hα1 hg, parts_inner_diff hφ hκ hα1 hg ha' hh hb' hc0,
    show (1 - α) * ‖a - b‖ = (1 - α) * Dpop φ P Q α by rw [hab],
    show (1 : ℝ) - (1 - α) = α by ring] at key
  simp only [ramp, clip, StatFormal.Wave31ti.uPath]
  exact key

theorem excess_identity_route : Claims.excess_identity := by
  refine ⟨?_, ?_⟩
  · intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α a b t u hφ hκ hα0 hα1 hD ha hb hab ht hu hut
    exact identity_G hφ hκ hα0 hα1 hD ha hb hab ht hu hut
  · intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α a b t u hφ hκ hchar _ htv1 hα0 hαtv ha hb hab ht hu
    have hα1 : α < 1 := hαtv.trans htv1
    have hD := dpop_pos_of_lt_tv hφ hκ hchar hα0 hα1 hαtv
    have hut : u < t := by linarith [pop_gap hφ hκ hα0 hα1 ha hb hab hD ht hu]
    exact identity_G hφ hκ hα0 hα1 hD ha hb hab ht.1 hu.1 hut

/-! ### T40: Proposition 5.10 (i) -/

/-- Proposition 5.10 (i-1), general form. -/
theorem excess_lower_G [CompleteSpace H] {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {φ : 𝒳 → H} {κ α : ℝ} {a b : H} {t u : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hD : 0 < Dpop φ P Q α) (ha : a ∈ region φ α P) (hb : b ∈ region φ α Q)
    (hab : ‖a - b‖ = Dpop φ P Q α) (ht : IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) t)
    (hu : IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α u) (hut : u < t) :
    (1 - α) * Dpop φ P Q α / (t - u) ≤
      (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
        (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - α := by
  rw [identity_G hφ hκ hα0 hα1 hD ha hb hab ht hu hut]
  refine div_le_div_of_nonneg_right ?_ (sub_pos.2 hut).le
  have h1 : 0 ≤ ∫ x, max (u - ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) 0 ∂P := integral_nonneg fun _ => le_max_right _ _
  have h2 : 0 ≤ ∫ y, max (⟪‖a - b‖⁻¹ • (a - b), φ y⟫_ℝ - t) 0 ∂Q := integral_nonneg fun _ => le_max_right _ _
  simp only [StatFormal.Wave31ti.uPath]
  linarith

/-- Proposition 5.10 (i-2), general form: `−(t − u)` is a subgradient of the rescaled path at `α`. -/
theorem subgradient_G [CompleteSpace H] {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {φ : 𝒳 → H} {κ α : ℝ} {a b : H} {t u : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hD : 0 < Dpop φ P Q α) (ha : a ∈ region φ α P) (hb : b ∈ region φ α Q)
    (hab : ‖a - b‖ = Dpop φ P Q α) (ht : IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - α) t)
    (hu : IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) α u) :
    ∀ α' ∈ Ico (0 : ℝ) 1, (1 - α) * Dpop φ P Q α - (t - u) * (α' - α) ≤ (1 - α') * Dpop φ P Q α' := by
  intro α' ⟨hα'0, hα'1⟩
  obtain ⟨g, hgm, hgb, hgi, ha'⟩ := ha
  obtain ⟨h, hhm, hhb, hhi, hb'⟩ := hb
  have hg : IsTrimDensity P α g := ⟨hgm, hgb, hgi⟩
  have hh : IsTrimDensity Q α h := ⟨hhm, hhb, hhi⟩
  have hc0 : 0 < ‖a - b‖ := hab ▸ hD
  obtain ⟨hA, hB, -, -, -, -⟩ := bathtub_G hφ hκ hα0 hα1 hD hg ha' hh hb' hab ht hu
  have hdiff := (parts_inner_diff hφ hκ hα1 hg ha' hh hb' hc0).trans
    (show (1 - α) * ‖a - b‖ = (1 - α) * Dpop φ P Q α by rw [hab])
  set f : H := ‖a - b‖⁻¹ • (a - b) with hf
  have hf1 : ‖f‖ = 1 := norm_dir hc0
  have h1α' : 0 < 1 - α' := by linarith
  set X := (1 - α) * Dpop φ P Q α - (t - u) * (α' - α) with hX
  have hle : X / (1 - α') ≤ Dpop φ P Q α' := by
    obtain ⟨a₀, ha₀⟩ := region_nonempty (φ := φ) P hα'0 hα'1
    obtain ⟨b₀, hb₀⟩ := region_nonempty (φ := φ) Q hα'0 hα'1
    refine le_csInf ⟨_, a₀, ha₀, b₀, hb₀, rfl⟩ ?_
    rintro _ ⟨a'', ⟨g'', hg''m, hg''b, hg''i, rfl⟩, b'', ⟨h'', hh''m, hh''b, hh''i, rfl⟩, rfl⟩
    have hg'' : IsTrimDensity P α' g'' := ⟨hg''m, hg''b, hg''i⟩
    have hh'' : IsTrimDensity Q α' h'' := ⟨hh''m, hh''b, hh''i⟩
    have := part_finite hα'1 hg''
    have := part_finite hα'1 hh''
    have hP'' := hA _ (part_le hα'1 hg'')
    have hQ'' := hB _ (part_le hα'1 hh'')
    rw [part_real_univ hα'1 hg''] at hP''
    rw [part_real_univ hα'1 hh''] at hQ''
    rw [inner_part hφ hκ hα'1 hg''] at hP''
    rw [inner_part hφ hκ hα'1 hh''] at hQ''
    have hcs : ⟪f, (∫ x, g'' x • φ x ∂P) - ∫ y, h'' y • φ y ∂Q⟫_ℝ ≤
        ‖(∫ x, g'' x • φ x ∂P) - ∫ y, h'' y • φ y ∂Q‖ :=
      (real_inner_le_norm _ _).trans (by rw [hf1, one_mul])
    rw [inner_sub_right] at hcs
    rw [div_le_iff₀ h1α']
    linarith [mul_le_mul_of_nonneg_left hcs h1α'.le]
  have := (div_le_iff₀ h1α').1 hle
  linarith

theorem excess_i_route : Claims.excess_i := by
  refine ⟨?_, ?_⟩
  · intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α a b t u hφ hκ hα0 hα1 hD ha hb hab ht hu
    exact ⟨fun hut => excess_lower_G hφ hκ hα0 hα1 hD ha hb hab ht hu hut,
      subgradient_G hφ hκ hα0 hα1 hD ha hb hab ht hu⟩
  · intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α a b t u hφ hκ hchar _ htv1 hα0 hαtv ha hb hab ht hu
    have hα1 : α < 1 := hαtv.trans htv1
    have hD := dpop_pos_of_lt_tv hφ hκ hchar hα0 hα1 hαtv
    have hgap := pop_gap hφ hκ hα0 hα1 ha hb hab hD ht hu
    have hut : u < t := by linarith
    exact ⟨⟨hgap, hD⟩, excess_lower_G hφ hκ hα0 hα1 hD ha hb hab ht.1 hu.1 hut,
      subgradient_G hφ hκ hα0 hα1 hD ha hb hab ht.1 hu.1⟩

/-! ### T41: Proposition 5.10 (ii) -/

/-- Proposition 5.10 (ii), general form. -/
theorem excess_ii_G [CompleteSpace H] {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {φ : 𝒳 → H} {κ γ c₁ c₂ ε₀ ε : ℝ} {a b : H} {t u : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (htv1 : StatFormal.Distances.tvDist P Q < 1) (hγ : 0 < γ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hε₀ : 0 < ε₀)
    (hε₀tv : ε₀ ≤ StatFormal.Distances.tvDist P Q)
    (hmar : ∀ e : ℝ, 0 < e → e ≤ ε₀ →
      c₁ * e ^ γ ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - e) ∧
        Dpop φ P Q (StatFormal.Distances.tvDist P Q - e) ≤ c₂ * e ^ γ)
    (hε : 0 < ε) (hεε₀ : ε ≤ ε₀ / 2)
    (ha : a ∈ region φ (StatFormal.Distances.tvDist P Q - ε) P) (hb : b ∈ region φ (StatFormal.Distances.tvDist P Q - ε) Q)
    (hab : ‖a - b‖ = Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε))
    (ht : IsQuantileAt P (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (1 - (StatFormal.Distances.tvDist P Q - ε)) t)
    (hu : IsQuantileAt Q (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) (StatFormal.Distances.tvDist P Q - ε) u) (hut : u < t) :
    (1 - StatFormal.Distances.tvDist P Q) * c₁ * ε / (2 ^ γ * c₂) ≤
        (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
          (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - (StatFormal.Distances.tvDist P Q - ε) ∧
      (∫ x, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u x ∂P) -
          (∫ y, ramp (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u y ∂Q) - (StatFormal.Distances.tvDist P Q - ε) ≤ ε := by
  set A := StatFormal.Distances.tvDist P Q with hA
  set α := A - ε with hαdef
  have hα0 : 0 ≤ α := by linarith
  have hα1 : α < 1 := by linarith
  have hDlo := (hmar ε hε (by linarith)).1
  have hEpos : 0 < ε ^ γ := Real.rpow_pos_of_pos hε γ
  have hD : 0 < Dpop φ P Q α := lt_of_lt_of_le (mul_pos hc₁ hEpos) hDlo
  refine ⟨?_, ?_⟩
  · have hi1 := excess_lower_G hφ hκ hα0 hα1 hD ha hb hab ht hu hut
    have hi2 := subgradient_G hφ hκ hα0 hα1 hD ha hb hab ht hu (A - 2 * ε) ⟨by linarith, by linarith⟩
    have hup := (hmar (2 * ε) (by linarith) (by linarith)).2
    have h2 : (2 * ε) ^ γ = 2 ^ γ * ε ^ γ := Real.mul_rpow (by norm_num) hε.le
    rw [h2] at hup
    have hDnn : 0 ≤ Dpop φ P Q (A - 2 * ε) := dpop_nonneg φ P Q _
    have hα'le : (1 - (A - 2 * ε)) * Dpop φ P Q (A - 2 * ε) ≤ Dpop φ P Q (A - 2 * ε) := by
      have : 1 - (A - 2 * ε) ≤ 1 := by linarith
      nlinarith
    have hαD : 0 ≤ (1 - α) * Dpop φ P Q α := mul_nonneg (by linarith) hD.le
    -- `(t − u) ε ≤ c₂ 2^γ ε^γ`
    have htu : (t - u) * ε ≤ c₂ * (2 ^ γ * ε ^ γ) := by
      have e : (t - u) * ((A - 2 * ε) - α) = -((t - u) * ε) := by rw [hαdef]; ring
      rw [e] at hi2
      linarith
    have hT : 0 < (2 : ℝ) ^ γ := Real.rpow_pos_of_pos (by norm_num) γ
    have hden : 0 < 2 ^ γ * c₂ := mul_pos hT hc₂
    have htu0 : 0 < t - u := sub_pos.2 hut
    refine le_trans ?_ hi1
    rw [div_le_div_iff₀ hden htu0]
    have h1A : 0 ≤ 1 - A := by linarith
    have hAα : 1 - A ≤ 1 - α := by linarith
    calc (1 - A) * c₁ * ε * (t - u) = (1 - A) * c₁ * ((t - u) * ε) := by ring
      _ ≤ (1 - A) * c₁ * (c₂ * (2 ^ γ * ε ^ γ)) :=
          mul_le_mul_of_nonneg_left htu (mul_nonneg h1A hc₁.le)
      _ = (1 - A) * (2 ^ γ * c₂) * (c₁ * ε ^ γ) := by ring
      _ ≤ (1 - A) * (2 ^ γ * c₂) * Dpop φ P Q α :=
          mul_le_mul_of_nonneg_left hDlo (mul_nonneg h1A hden.le)
      _ ≤ (1 - α) * (2 ^ γ * c₂) * Dpop φ P Q α := by
          have := mul_le_mul_of_nonneg_right hAα (mul_nonneg hden.le hD.le)
          nlinarith
      _ = (1 - α) * Dpop φ P Q α * (2 ^ γ * c₂) := by ring
  · have hFm := measurable_wit hφ (‖a - b‖⁻¹ • (a - b))
    have := (StatFormal.Wave30tv.lem_ramp_iii 𝒳 P Q (fun z => ⟪‖a - b‖⁻¹ • (a - b), φ z⟫_ℝ) t u hFm hut).2.2
    linarith

theorem excess_ii_route : Claims.excess_ii := by
  refine ⟨?_, ?_⟩
  · intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ γ c₁ c₂ ε₀ ε a b t u hφ hκ _ htv1 hγ hc₁ hc₂ hε₀ hε₀tv hmar hε hεε₀ ha hb hab ht hu hut
    exact excess_ii_G hφ hκ htv1 hγ hc₁ hc₂ hε₀ hε₀tv hmar hε hεε₀ ha hb hab ht hu hut
  · intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ γ c₁ c₂ ε₀ ε a b t u hφ hκ _ _ htv1 hγ hc₁ hc₂ hε₀ hε₀tv hmar hε hεε₀ ha hb hab ht hu
    have hα0 : 0 ≤ StatFormal.Distances.tvDist P Q - ε := by linarith
    have hα1 : StatFormal.Distances.tvDist P Q - ε < 1 := by linarith
    have hD : 0 < Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) :=
      lt_of_lt_of_le (mul_pos hc₁ (Real.rpow_pos_of_pos hε γ)) (hmar ε hε (by linarith)).1
    have hut : u < t := by linarith [pop_gap hφ hκ hα0 hα1 ha hb hab hD ht hu]
    exact excess_ii_G hφ hκ htv1 hγ hc₁ hc₂ hε₀ hε₀tv hmar hε hεε₀ ha hb hab ht.1 hu.1 hut

end StatFormal.Wave31tr.RouteExcess
