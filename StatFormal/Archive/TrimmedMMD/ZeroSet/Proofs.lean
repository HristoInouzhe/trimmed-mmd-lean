import StatFormal.Archive.TrimmedMMD.ZeroSet.Statements
import StatFormal.Lib.Distances.Hellinger
import StatFormal.Archive.TrimmedMMD.Unconditional.Proofs
import StatFormal.Archive.TrimmedMMD.ZeroSet.Attain

/-!
# Proofs: the zero set of `D_α` and `α* = TV(P,Q)`

* `tvintersect` (⇒): with `ρ = P + Q`, `p = dP/dρ`, `q = dQ/dρ`, `m = min(p,q)`, `c = 1 − TV`:
  `∫ m dρ = c` (`tvDist_eq_one_sub_integral_min`); `gP = m/(c p)` satisfies `p·gP = m/c` everywhere,
  so `P.withDensity gP = ρ.withDensity (m/c) = Q.withDensity gQ`.
  (⇐): the common trimming `R` has `(1−α) R ≤ P` and `(1−α) R ≤ Q`, so `P(A) − Q(A) ≥ −α`.
* `zero_of_tv_le`: the common trimming gives a common embedding, so `0` is in the distance set.
* `consistency_tv`, `consistency_tv_zero`: `zero_of_tv_le` at `α = TV`, then the certified
  `Unconditional.consistency_i` / `consistency_i_zero`.
* `zeroeq`: (⇐) is `zero_of_tv_le`; (⇒) by attainment (`ZeroSet/Attain.lean`:
  `exists_common_of_Dpop_eq_zero`, nested closed convex sets in `L²(P) × L²(Q)`), two trimmings with
  the same embedding; the trimmed measures are probability measures with equal mean
  embeddings, hence equal (`Characteristic`), and `tvDist_le_of_common` gives `TV ≤ α`.
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.TrimmedMMD.ZeroSet

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.Distances

section General

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

theorem IsTrimDensity.integrable {P : Measure 𝒳} [IsFiniteMeasure P] {α : ℝ} {g : 𝒳 → ℝ}
    (hg : IsTrimDensity P α g) : Integrable g P :=
  Integrable.of_mem_Icc 0 (1 / (1 - α)) hg.1.aemeasurable
    (ae_of_all _ fun x => ⟨(hg.2.1 x).1, (hg.2.1 x).2⟩)

/-- Change of reference measure for a trimming density. -/
theorem withDensity_ofReal_eq_rnDeriv {μ ρ : Measure 𝒳} [IsFiniteMeasure μ] [SigmaFinite ρ]
    (h : μ ≪ ρ) {g : 𝒳 → ℝ} (hg : Measurable g) :
    μ.withDensity (fun x => ENNReal.ofReal (g x)) =
      ρ.withDensity (fun x => ENNReal.ofReal ((μ.rnDeriv ρ x).toReal * g x)) := by
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ ρ h]
  rw [← withDensity_mul ρ (Measure.measurable_rnDeriv μ ρ) hg.ennreal_ofReal]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top μ ρ] with x hx
  simp only [Pi.mul_apply]
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]

/-- The mass of the trimmed measure on a measurable set. -/
theorem withDensity_ofReal_apply {P : Measure 𝒳} [IsFiniteMeasure P] {g : 𝒳 → ℝ}
    (hgi : Integrable g P) (hg0 : ∀ x, 0 ≤ g x) {A : Set 𝒳} (hA : MeasurableSet A) :
    P.withDensity (fun x => ENNReal.ofReal (g x)) A = ENNReal.ofReal (∫ x in A, g x ∂P) := by
  rw [withDensity_apply _ hA, ofReal_integral_eq_lintegral_ofReal hgi.integrableOn
    (ae_of_all _ hg0)]

/-- One-sided bound from a common trimming. -/
theorem sub_le_of_common {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {α : ℝ} (hα1 : α < 1) {gP gQ : 𝒳 → ℝ} (hP : IsTrimDensity P α gP)
    (hQ : IsTrimDensity Q α gQ)
    (hR : ∀ A, MeasurableSet A → ∫ x in A, gP x ∂P = ∫ x in A, gQ x ∂Q)
    {A : Set 𝒳} (hA : MeasurableSet A) : Q.real A - P.real A ≤ α := by
  have hc : 0 < 1 - α := by linarith
  set c := 1 / (1 - α) with hc_def
  have hkey : (1 - α) * c = 1 := by rw [hc_def]; field_simp
  have hPi := hP.integrable
  have hQi := hQ.integrable
  have bnd : ∀ (μ : Measure 𝒳) [IsProbabilityMeasure μ] (g : 𝒳 → ℝ), IsTrimDensity μ α g →
      ∀ B, MeasurableSet B → ∫ x in B, g x ∂μ ≤ c * μ.real B := by
    intro μ _ g hg B _
    calc ∫ x in B, g x ∂μ ≤ ∫ _ in B, c ∂μ :=
          setIntegral_mono hg.integrable.integrableOn (integrable_const c).integrableOn
            fun x => (hg.2.1 x).2
      _ = c * μ.real B := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hu := bnd P gP hP A hA
  have hv := bnd Q gQ hQ Aᶜ hA.compl
  have hsum : ∫ x in A, gP x ∂P + ∫ x in Aᶜ, gP x ∂P = 1 := by
    rw [integral_add_compl hA hPi, hP.2.2]
  rw [hR Aᶜ hA.compl] at hsum
  have hQc : Q.real Aᶜ = 1 - Q.real A := probReal_compl_eq_one_sub hA
  rw [hQc] at hv
  have h1 : (1 - α) * ∫ x in A, gP x ∂P ≤ P.real A := by
    have := mul_le_mul_of_nonneg_left hu hc.le
    rwa [← mul_assoc, hkey, one_mul] at this
  have h2 : (1 - α) * ∫ x in Aᶜ, gQ x ∂Q ≤ 1 - Q.real A := by
    have := mul_le_mul_of_nonneg_left hv hc.le
    rwa [← mul_assoc, hkey, one_mul] at this
  nlinarith

theorem tvDist_le_of_common {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {α : ℝ} (hα1 : α < 1) {gP gQ : 𝒳 → ℝ} (hP : IsTrimDensity P α gP)
    (hQ : IsTrimDensity Q α gQ)
    (hR : P.withDensity (fun x => ENNReal.ofReal (gP x)) =
      Q.withDensity (fun x => ENNReal.ofReal (gQ x))) : tvDist P Q ≤ α := by
  have hR' : ∀ A, MeasurableSet A → ∫ x in A, gP x ∂P = ∫ x in A, gQ x ∂Q := by
    intro A hA
    have h := congrArg (fun μ : Measure 𝒳 => μ A) hR
    rw [withDensity_ofReal_apply hP.integrable (fun x => (hP.2.1 x).1) hA,
      withDensity_ofReal_apply hQ.integrable (fun x => (hQ.2.1 x).1) hA] at h
    exact (ENNReal.ofReal_eq_ofReal_iff
      (setIntegral_nonneg hA fun x _ => (hP.2.1 x).1)
      (setIntegral_nonneg hA fun x _ => (hQ.2.1 x).1)).1 h
  refine tvDist_le_of_forall fun A hA => ?_
  rw [abs_le]
  constructor
  · have := sub_le_of_common hα1 hP hQ hR' hA
    linarith
  · have := sub_le_of_common hα1 hQ hP (fun B hB => (hR' B hB).symm) hA
    linarith

/-- (⇒) of `tvintersect`. -/
theorem exists_common_of_tvDist_le {P Q : Measure 𝒳} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {α : ℝ} (hα1 : α < 1) (htv : tvDist P Q ≤ α) :
    ∃ gP gQ : 𝒳 → ℝ, IsTrimDensity P α gP ∧ IsTrimDensity Q α gQ ∧
      P.withDensity (fun x => ENNReal.ofReal (gP x)) =
        Q.withDensity (fun x => ENNReal.ofReal (gQ x)) := by
  set ρ := P + Q with hρ
  have hPρ : P ≪ ρ := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQρ : Q ≪ ρ := Measure.AbsolutelyContinuous.rfl.add_right' P
  set p : 𝒳 → ℝ := fun x => (P.rnDeriv ρ x).toReal with hp
  set q : 𝒳 → ℝ := fun x => (Q.rnDeriv ρ x).toReal with hq
  have hpm : Measurable p := (Measure.measurable_rnDeriv P ρ).ennreal_toReal
  have hqm : Measurable q := (Measure.measurable_rnDeriv Q ρ).ennreal_toReal
  have hp0 : ∀ x, 0 ≤ p x := fun _ => ENNReal.toReal_nonneg
  have hq0 : ∀ x, 0 ≤ q x := fun _ => ENNReal.toReal_nonneg
  set m : 𝒳 → ℝ := fun x => min (p x) (q x) with hm
  have hmm : Measurable m := hpm.min hqm
  have htv' := tvDist_eq_one_sub_integral_min ρ hPρ hQρ
  set c := 1 - tvDist P Q with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hint : ∫ x, m x ∂ρ = c := by rw [hc, htv']; ring
  have hcα : 1 / c ≤ 1 / (1 - α) := one_div_le_one_div_of_le (by linarith) (by rw [hc]; linarith)
  -- the trimming densities
  have build : ∀ (μ : Measure 𝒳) [IsProbabilityMeasure μ] (r : 𝒳 → ℝ), μ ≪ ρ →
      (∀ x, r x = (μ.rnDeriv ρ x).toReal) → (∀ x, m x ≤ r x) →
      ∃ g : 𝒳 → ℝ, IsTrimDensity μ α g ∧
        μ.withDensity (fun x => ENNReal.ofReal (g x)) =
          ρ.withDensity (fun x => ENNReal.ofReal (m x / c)) := by
    intro μ _ r hμ hr hmr
    have hrm : Measurable r := by
      have : r = fun x => (μ.rnDeriv ρ x).toReal := funext hr
      rw [this]; exact (Measure.measurable_rnDeriv μ ρ).ennreal_toReal
    have hr0 : ∀ x, 0 ≤ r x := fun x => by rw [hr x]; exact ENNReal.toReal_nonneg
    have hm0 : ∀ x, 0 ≤ m x := fun x => le_min (hp0 x) (hq0 x)
    set g : 𝒳 → ℝ := fun x => m x / (c * r x) with hg
    have hgm : Measurable g := hmm.div (measurable_const.mul hrm)
    have hrg : ∀ x, r x * g x = m x / c := by
      intro x
      rcases (hr0 x).lt_or_eq with h | h
      · rw [hg]; field_simp
      · have : m x = 0 := le_antisymm (h ▸ hmr x) (hm0 x)
        rw [← h, this]; simp
    have hg0 : ∀ x, 0 ≤ g x := fun x => div_nonneg (hm0 x) (mul_nonneg hcpos.le (hr0 x))
    have hg1 : ∀ x, g x ≤ 1 / c := by
      intro x
      rcases (hr0 x).lt_or_eq with h | h
      · rw [hg, div_le_div_iff₀ (mul_pos hcpos h) hcpos]
        nlinarith [hmr x]
      · simp only [hg, ← h, mul_zero, div_zero]; positivity
    refine ⟨g, ⟨hgm, fun x => ⟨hg0 x, (hg1 x).trans hcα⟩, ?_⟩, ?_⟩
    · rw [← integral_rnDeriv_smul hμ]
      simp_rw [smul_eq_mul, ← hr, hrg]
      rw [integral_div, hint, div_self hcpos.ne']
    · rw [withDensity_ofReal_eq_rnDeriv hμ hgm]
      congr 1
      funext x
      rw [← hr, hrg]
  obtain ⟨gP, hgP, hRP⟩ := build P p hPρ (fun _ => rfl) fun x => min_le_left _ _
  obtain ⟨gQ, hgQ, hRQ⟩ := build Q q hQρ (fun _ => rfl) fun x => min_le_right _ _
  exact ⟨gP, gQ, hgP, hgQ, hRP.trans hRQ.symm⟩

end General

theorem tvintersect : Claims.tvintersect := by
  intro 𝒳 _ P Q _ _ α _ hα1
  exact ⟨exists_common_of_tvDist_le hα1, fun ⟨gP, gQ, hP, hQ, hR⟩ =>
    tvDist_le_of_common hα1 hP hQ hR⟩

/-- The embedding of a trimming is the mean of `φ` under the trimmed measure. -/
theorem integral_smul_eq_withDensity {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (P : Measure 𝒳) {g : 𝒳 → ℝ} (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (φ : 𝒳 → H) :
    ∫ x, g x • φ x ∂P = ∫ x, φ x ∂(P.withDensity fun x => ENNReal.ofReal (g x)) := by
  rw [integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hg0 _)]

theorem zero_of_tv_le : Claims.zero_of_tv_le := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ α _ _ _ hα1 htv
  obtain ⟨gP, gQ, hP, hQ, hR⟩ := exists_common_of_tvDist_le hα1 htv
  have ha : ∫ x, gP x • φ x ∂P ∈ region φ α P := ⟨gP, hP.1, hP.2.1, hP.2.2, rfl⟩
  have hb : ∫ x, gQ x • φ x ∂Q ∈ region φ α Q := ⟨gQ, hQ.1, hQ.2.1, hQ.2.2, rfl⟩
  have hab : ∫ x, gP x • φ x ∂P = ∫ x, gQ x • φ x ∂Q := by
    rw [integral_smul_eq_withDensity P hP.1 (fun x => (hP.2.1 x).1),
      integral_smul_eq_withDensity Q hQ.1 (fun x => (hQ.2.1 x).1), hR]
  refine le_antisymm ?_ (Real.sInf_nonneg ?_)
  · have := setDist_le_norm ha hb
    rwa [hab, sub_self, norm_zero] at this
  · rintro _ ⟨a, -, b, -, rfl⟩; exact norm_nonneg _

theorem consistency_tv : Claims.consistency_tv := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ n m hφ hκ hκpos hδ0 hδ1 hn hm htv
  have h0 := tvDist_nonneg P Q
  have hD := zero_of_tv_le 𝒳 H P Q φ κ (tvDist P Q) hφ hκ h0 htv le_rfl
  exact Unconditional.consistency_i 𝒳 H P Q φ κ δ (tvDist P Q) n m hφ hκ hκpos hδ0 hδ1 hn hm
    ⟨h0, htv⟩ hD

theorem consistency_tv_zero : Claims.consistency_tv_zero := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ n m hφ hκ hκpos hδ0 hδ1 hn hm htv
  have hD := zero_of_tv_le 𝒳 H P Q φ κ 0 hφ hκ le_rfl one_pos htv.le
  exact Unconditional.consistency_i_zero 𝒳 H P Q φ κ δ n m hφ hκ hκpos hδ0 hδ1 hn hm hD

theorem zeroeq : Claims.zeroeq := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α hφ hκ hchar hα0 hα1
  refine ⟨fun hD => ?_, zero_of_tv_le 𝒳 H P Q φ κ α hφ hκ hα0 hα1⟩
  obtain ⟨gP, gQ, hP, hQ, he⟩ := exists_common_of_Dpop_eq_zero hφ hκ hα0 hα1 hD
  have hprob : ∀ (μ : Measure 𝒳) [IsProbabilityMeasure μ] (g : 𝒳 → ℝ), IsTrimDensity μ α g →
      IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (g x)) := by
    intro μ _ g hg
    refine ⟨?_⟩
    rw [withDensity_ofReal_apply hg.integrable (fun x => (hg.2.1 x).1) MeasurableSet.univ,
      setIntegral_univ, hg.2.2, ENNReal.ofReal_one]
  have hR := hchar _ _ (hprob P gP hP) (hprob Q gQ hQ) (by
    rw [← integral_smul_eq_withDensity P hP.1 (fun x => (hP.2.1 x).1),
      ← integral_smul_eq_withDensity Q hQ.1 (fun x => (hQ.2.1 x).1), he])
  exact tvDist_le_of_common hα1 hP hQ hR

end StatFormal.TrimmedMMD.ZeroSet
