import StatFormal.Wave30tx.RouteBasic
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs
import StatFormal.Archive.Wave18b.Proofs
import StatFormal.Archive.Wave12c.RouteTrimConsist
import StatFormal.Wave30tn.Proofs
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Route: `rem:nearcontact (v2)` (a) (untrusted proof material)

Proof of the remark, Steps 1–3 (`C_recover.tex` §C.4), from `lem:contact` (taken as the hypothesis `Claims.contact`).

* `exists_weak_subseq`: bounded sequences in a separable Hilbert space have weakly convergent subsequences (sequential
  Banach–Alaoglu, `WeakDual.isSeqCompact_closedBall`, through `InnerProductSpace.toDual`).
* `no_L1_limit` (Steps 1–2): along `a_j ↑ α*` the trimmed embeddings `a_j = E_P[g_jφ]` tend to `μ_{R*}` (`ω_c → 0`), the
  trimming densities are `(1−a_j)⁻¹1_{A_j}` (`Wave30tn.popthreshold`), and an `L¹(P)` limit `h` of `1_{A_j}` would make
  `β*hP = R*` (A3), so that `dR*/dP ∈ {0, β*}` a.e., against the fractional hypothesis.
* `nearcontact_a_of` (Step 3): a bounded density along a sequence gives (weak limit `f̄`, `s_j → s̄`) `P(f̄ = s̄) = 0` and
  `1_{A_j} → 1{f̄ < s̄}` in `L¹(P)` by dominated convergence, contradicting `no_L1_limit`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace Pointwise

namespace StatFormal.Wave30tx.RNearA

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.Projection StatFormal.TrimmedMMD.ZeroSet StatFormal.Wave12c StatFormal.Wave30tx

/-! ### Weak sequential compactness -/

theorem exists_weak_subseq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (f : ℕ → H) (hf : ∀ j, ‖f j‖ ≤ 1) :
    ∃ (fbar : H) (ψ : ℕ → ℕ), StrictMono ψ ∧
      ∀ g : H, Tendsto (fun j => ⟪f (ψ j), g⟫_ℝ) atTop (𝓝 ⟪fbar, g⟫_ℝ) := by
  set T := InnerProductSpace.toDual ℝ H
  have hseq := WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) 1
  have hmem : ∀ j, StrongDual.toWeakDual (T (f j)) ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) 1 := by
    intro j
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
    change ‖T (f j)‖ ≤ 1
    rw [LinearIsometryEquiv.norm_map]
    exact hf j
  obtain ⟨w, -, ψ, hψ, hlim⟩ := hseq hmem
  refine ⟨T.symm (WeakDual.toStrongDual w), ψ, hψ, fun g => ?_⟩
  have h1 := ((WeakDual.eval_continuous g).tendsto w).comp hlim
  have e1 : ∀ j, ((fun x : WeakDual ℝ H => x g) ∘ ((fun j => StrongDual.toWeakDual (T (f j))) ∘ ψ)) j =
      ⟪f (ψ j), g⟫_ℝ := fun j => by
    simp only [Function.comp_apply, StrongDual.toWeakDual_apply]
    exact InnerProductSpace.toDual_apply_apply
  have e2 : w g = ⟪T.symm (WeakDual.toStrongDual w), g⟫_ℝ := by
    rw [InnerProductSpace.toDual_symm_apply]; rfl
  rw [e2] at h1
  exact h1.congr e1

/-! ### Generalities on the regions -/

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem region_mono {φ : 𝒳 → H} {P : Measure 𝒳} {α α' : ℝ} (hαα' : α ≤ α') (hα' : α' < 1) :
    region φ α P ⊆ region φ α' P := by
  rintro z ⟨g, hg, hgb, hg1, rfl⟩
  refine ⟨g, hg, fun x => ⟨(hgb x).1, (hgb x).2.trans ?_⟩, hg1, rfl⟩
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem integrable_smul_of_bdd {P : Measure 𝒳} [IsFiniteMeasure P] {φ : 𝒳 → H} {κ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {u : 𝒳 → ℝ} (hu : Integrable u P) :
    Integrable (fun x => u x • φ x) P := by
  refine Integrable.mono' (hu.norm.mul_const κ) (hu.aestronglyMeasurable.smul hφ.aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hκ x) (norm_nonneg _)

theorem norm_integral_smul_sub_le [CompleteSpace H] {P : Measure 𝒳} [IsFiniteMeasure P] {φ : 𝒳 → H}
    {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {u v : 𝒳 → ℝ} (hu : Integrable u P)
    (hv : Integrable v P) :
    ‖∫ x, u x • φ x ∂P - ∫ x, v x • φ x ∂P‖ ≤ κ * ∫ x, |u x - v x| ∂P := by
  rw [← integral_sub (integrable_smul_of_bdd hφ hκ hu) (integrable_smul_of_bdd hφ hκ hv)]
  have hint : Integrable (fun x => |u x - v x| * κ) P := ((hu.sub hv).abs).mul_const κ
  refine (norm_integral_le_of_norm_le hint (ae_of_all _ fun x => ?_)).trans ?_
  · rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hκ x) (abs_nonneg _)
  · rw [integral_mul_const, mul_comm]

theorem norm_le_of_mem_region {φ : 𝒳 → H} {P : Measure 𝒳} [IsProbabilityMeasure P] {κ α : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {z : H} (hz : z ∈ region φ α P) : ‖z‖ ≤ κ := by
  obtain ⟨g, hg, hgb, hg1, rfl⟩ := hz
  have hgi : Integrable g P := Integrable.of_bound hg.aestronglyMeasurable (1 / (1 - α))
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hgb x).1]; exact (hgb x).2)
  have hint : Integrable (fun x => g x * κ) P := hgi.mul_const κ
  refine (norm_integral_le_of_norm_le hint (ae_of_all _ fun x => ?_)).trans ?_
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hgb x).1]
    exact mul_le_mul_of_nonneg_left (hκ x) (hgb x).1
  · rw [integral_mul_const, hg1, one_mul]

/-! ### Steps 1–2: the indicators of the kept sets have no `L¹(P)` limit -/

set_option maxHeartbeats 1600000 in
theorem no_L1_limit [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {φ : 𝒳 → H} {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hchar : Characteristic φ)
    (h0 : 0 < StatFormal.Distances.tvDist P Q) (h1 : StatFormal.Distances.tvDist P Q < 1)
    (hfrac : 0 < P {x | 0 < ((contactLaw P Q).rnDeriv P x).toReal ∧
      ((contactLaw P Q).rnDeriv P x).toReal < 1 / (1 - StatFormal.Distances.tvDist P Q)})
    (hω : Tendsto (omegaC φ P Q) (𝓝[>] 0) (𝓝 0)) (hRs : IsProbabilityMeasure (contactLaw P Q))
    (dstar : ℝ → H) (s : ℝ → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, a j ∈ Ioo 0 (StatFormal.Distances.tvDist P Q))
    (hat : Tendsto a atTop (𝓝 (StatFormal.Distances.tvDist P Q)))
    (hd : ∀ j, IsMinNorm (region φ (a j) P - region φ (a j) Q) (dstar (a j)))
    (hq : ∀ j, IsQuantile P (witFn ((Dpop φ P Q (a j))⁻¹ • dstar (a j)) φ) (1 - a j) (s (a j)))
    (hat0 : ∀ j, P {x | witFn ((Dpop φ P Q (a j))⁻¹ • dstar (a j)) φ x = s (a j)} = 0)
    (h : 𝒳 → ℝ) (hh : Integrable h P)
    (hL : Tendsto (fun j => ∫ x, |{x | witFn ((Dpop φ P Q (a j))⁻¹ • dstar (a j)) φ x < s (a j)}.indicator
      (fun _ => (1 : ℝ)) x - h x| ∂P) atTop (𝓝 0)) : False := by
  set αs := StatFormal.Distances.tvDist P Q with hαs
  set β : ℝ := 1 / (1 - αs) with hβ
  have hη0 : 0 < 1 - αs := by linarith
  have hβ0 : 0 < β := by positivity
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ x₀)
  have ha1 : ∀ j, a j < 1 := fun j => by linarith [(ha j).2]
  -- the discrepancies
  set D : ℕ → ℝ := fun j => Dpop φ P Q (a j) with hDdef
  have hDn : ∀ j, D j = ‖dstar (a j)‖ := fun j => RBasic.Dpop_eq_norm (hd j)
  have hDpos : ∀ j, 0 < D j := by
    intro j
    have hne : D j ≠ 0 := fun h0' => by
      have := (zeroeq 𝒳 H P Q φ κ (a j) hφ hκ hchar (ha j).1.le (ha1 j)).1 h0'
      linarith [(ha j).2]
    exact lt_of_le_of_ne (by rw [hDn j]; exact norm_nonneg _) (Ne.symm hne)
  have hDα : Dpop φ P Q αs = 0 := zero_of_tv_le 𝒳 H P Q φ κ αs hφ hκ h0.le h1 le_rfl
  have hD0 : Tendsto D atTop (𝓝 0) := by
    have hlip : ∀ j, ‖D j‖ ≤ 4 * κ / (1 - αs) ^ 2 * ‖a j - αs‖ := by
      intro j
      have := StatFormal.Wave18b.continuity_lip 𝒳 H P Q φ κ (1 - αs) (a j) αs hφ hκ hη0 (by linarith)
        ⟨(ha j).1.le, by linarith [(ha j).2]⟩ ⟨h0.le, by linarith⟩
      rw [hDα, sub_zero] at this
      simpa only [Real.norm_eq_abs] using this
    have hlim : Tendsto (fun j => 4 * κ / (1 - αs) ^ 2 * ‖a j - αs‖) atTop (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hat).const_mul (4 * κ / (1 - αs) ^ 2)
    exact squeeze_zero_norm hlip hlim
  -- decomposition of the witnesses
  have hdec : ∀ j, ∃ g : 𝒳 → ℝ, ∃ b : H, IsTrimDensity P (a j) g ∧ b ∈ region φ (a j) Q ∧
      dstar (a j) = ∫ x, g x • φ x ∂P - b := by
    intro j
    obtain ⟨_, ⟨g, hg, hgb, hg1, rfl⟩, b, hb, hAb⟩ := (hd j).1
    exact ⟨g, b, ⟨hg, hgb, hg1⟩, hb, hAb.symm⟩
  choose g b hg hb hdg using hdec
  set A : ℕ → H := fun j => ∫ x, g j x • φ x ∂P with hAdef
  -- Step 1: `A_j → μ_{R*}`
  set μs := ∫ x, φ x ∂(contactLaw P Q) with hμs
  have hbdd : ∀ ε, BddAbove {r | ∃ z ∈ region φ αs P, Metric.infDist z (region φ αs Q) ≤ ε ∧
      r = ‖z - μs‖} := by
    intro ε
    refine ⟨κ + ‖μs‖, ?_⟩
    rintro r ⟨z, hz, -, rfl⟩
    exact (norm_sub_le _ _).trans (by linarith [norm_le_of_mem_region hφ hκ hz])
  have hA_le : ∀ j, ‖A j - μs‖ ≤ omegaC φ P Q (D j) := by
    intro j
    have hAm : A j ∈ region φ αs P :=
      region_mono (ha j).2.le h1 ⟨g j, (hg j).1, (hg j).2.1, (hg j).2.2, rfl⟩
    have hbm : b j ∈ region φ αs Q := region_mono (ha j).2.le h1 (hb j)
    refine le_csSup (hbdd _) ⟨A j, hAm, ?_, rfl⟩
    calc Metric.infDist (A j) (region φ αs Q) ≤ dist (A j) (b j) := Metric.infDist_le_dist_of_mem hbm
      _ = ‖A j - b j‖ := dist_eq_norm _ _
      _ = D j := by rw [hDn j, hdg j]
  have hAlim : Tendsto A atTop (𝓝 μs) := by
    have hωD : Tendsto (fun j => omegaC φ P Q (D j)) atTop (𝓝 0) :=
      hω.comp (tendsto_nhdsWithin_iff.2 ⟨hD0, Eventually.of_forall hDpos⟩)
    exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun j => norm_nonneg _) hA_le hωD)
  -- Step 2: the trimming densities are bang-bang
  set f : ℕ → 𝒳 → ℝ := fun j => witFn ((Dpop φ P Q (a j))⁻¹ • dstar (a j)) φ with hfdef
  set S : ℕ → Set 𝒳 := fun j => {x | f j x < s (a j)} with hSdef
  set I : ℕ → 𝒳 → ℝ := fun j => (S j).indicator (fun _ => (1 : ℝ)) with hIdef
  have hfm : ∀ j, Measurable (f j) := fun j => measurable_witFn hφ _
  have hSm : ∀ j, MeasurableSet (S j) := fun j => measurableSet_lt (hfm j) measurable_const
  have hIi : ∀ j, Integrable (I j) P := fun j => (integrable_const (1 : ℝ)).indicator (hSm j)
  have hf_eq : ∀ j x, f j x = (D j)⁻¹ * ⟪dstar (a j), φ x⟫_ℝ := fun j x => by
    simp only [hfdef, witFn, real_inner_smul_left, hDdef]
  have hlt_iff : ∀ j x, ⟪dstar (a j), φ x⟫_ℝ < D j * s (a j) ↔ f j x < s (a j) := fun j x => by
    rw [hf_eq, inv_mul_lt_iff₀ (hDpos j)]
  have hle_iff : ∀ j x, ⟪dstar (a j), φ x⟫_ℝ ≤ D j * s (a j) ↔ f j x ≤ s (a j) := fun j x => by
    rw [hf_eq, inv_mul_le_iff₀ (hDpos j)]
  have hg_ae : ∀ j, g j =ᵐ[P] fun x => 1 / (1 - a j) * I j x := by
    intro j
    have ht1 : P.real {x | ⟪dstar (a j), φ x⟫_ℝ < D j * s (a j)} ≤ 1 - a j := by
      have e : {x | ⟪dstar (a j), φ x⟫_ℝ < D j * s (a j)} = {x | f j x < s (a j)} := by
        ext x; exact hlt_iff j x
      rw [e]; exact (hq j).1
    have ht2 : 1 - a j ≤ P.real {x | ⟪dstar (a j), φ x⟫_ℝ ≤ D j * s (a j)} := by
      have e : {x | ⟪dstar (a j), φ x⟫_ℝ ≤ D j * s (a j)} = {x | f j x ≤ s (a j)} := by
        ext x; exact hle_iff j x
      rw [e]; exact (hq j).2
    obtain ⟨hlt, hgt⟩ := StatFormal.Wave30tn.popthreshold 𝒳 H P Q φ κ (a j) (a j) (D j * s (a j))
      (dstar (a j)) (A j) (b j) (g j) hφ hκ (ha j).1.le (ha1 j) (ha j).1.le (ha1 j) (hDpos j) (hd j).2
      (hg j) rfl (hb j) (hdg j) ht1 ht2
    have hne : ∀ᵐ x ∂P, x ∉ {x | f j x = s (a j)} := measure_eq_zero_iff_ae_notMem.1 (hat0 j)
    filter_upwards [hlt, hgt, hne] with x hx1 hx2 hx3
    change ¬ (f j x = s (a j)) at hx3
    by_cases hxs : f j x < s (a j)
    · have hxS : x ∈ S j := hxs
      rw [hx1 ((hlt_iff j x).2 hxs)]
      simp [hIdef, indicator_of_mem hxS]
    · have hxS : x ∉ S j := hxs
      have hgt' : s (a j) < f j x := lt_of_le_of_ne (not_lt.1 hxs) (Ne.symm hx3)
      have : D j * s (a j) < ⟪dstar (a j), φ x⟫_ℝ := by
        by_contra hc; exact absurd ((hle_iff j x).1 (not_lt.1 hc)) (not_le.2 hgt')
      rw [hx2 this]
      simp [hIdef, indicator_of_notMem hxS]
  -- a measurable version of `h`
  obtain ⟨h0', hh0m, hh0⟩ : ∃ h0' : 𝒳 → ℝ, Measurable h0' ∧ h =ᵐ[P] h0' :=
    ⟨hh.1.aemeasurable.mk h, hh.1.aemeasurable.measurable_mk, hh.1.aemeasurable.ae_eq_mk⟩
  have hh0i : Integrable h0' P := hh.congr hh0
  have hL0 : Tendsto (fun j => ∫ x, |I j x - h0' x| ∂P) atTop (𝓝 0) := by
    refine hL.congr fun j => integral_congr_ae ?_
    filter_upwards [hh0] with x hx
    simp only [hIdef, hSdef, hfdef, hx]
  have hdi : ∀ j, Integrable (fun x => |I j x - h0' x|) P := fun j => ((hIi j).sub hh0i).abs
  -- `h` is a.e. an indicator
  set mf : 𝒳 → ℝ := fun x => min |h0' x| |1 - h0' x| with hmf
  have hmfm : Measurable mf :=
    (continuous_abs.measurable.comp hh0m).min (continuous_abs.measurable.comp (measurable_const.sub hh0m))
  have hmfi : Integrable mf P := by
    refine Integrable.mono' hh0i.abs hmfm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) (abs_nonneg _))]
    exact min_le_left _ _
  have hmf_le : ∀ j x, mf x ≤ |I j x - h0' x| := by
    intro j x
    by_cases hx : x ∈ S j
    · simp only [hmf, hIdef, indicator_of_mem hx]; exact min_le_right _ _
    · simp only [hmf, hIdef, indicator_of_notMem hx, zero_sub, abs_neg]; exact min_le_left _ _
  have hmf0 : ∫ x, mf x ∂P = 0 := by
    refine le_antisymm (ge_of_tendsto' hL0 fun j => integral_mono hmfi (hdi j) (hmf_le j)) ?_
    exact integral_nonneg fun x => le_min (abs_nonneg _) (abs_nonneg _)
  have h01 : ∀ᵐ x ∂P, h0' x = 0 ∨ h0' x = 1 := by
    have := (integral_eq_zero_iff_of_nonneg (fun x => le_min (abs_nonneg _) (abs_nonneg _)) hmfi).1 hmf0
    filter_upwards [this] with x hx
    simp only [hmf, Pi.zero_apply] at hx
    rcases min_eq_iff.1 hx with ⟨h1', -⟩ | ⟨h2', -⟩
    · left; exact abs_eq_zero.1 h1'
    · right; have := abs_eq_zero.1 h2'; linarith
  have hh0nn : ∀ᵐ x ∂P, 0 ≤ h0' x := by
    filter_upwards [h01] with x hx; rcases hx with hx | hx <;> rw [hx] <;> norm_num
  -- `∫ h = 1 − α*`
  have hPS : ∀ j, P.real (S j) = 1 - a j := by
    intro j
    have hEq0 : P.real {x | f j x = s (a j)} = 0 := by
      have e : P {x | f j x = s (a j)} = 0 := hat0 j
      simp [measureReal_def, e]
    have hu : {x | f j x ≤ s (a j)} ⊆ S j ∪ {x | f j x = s (a j)} := by
      intro x hx
      rcases (le_iff_lt_or_eq.1 (show f j x ≤ s (a j) from hx)) with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    have := (measureReal_mono hu).trans (measureReal_union_le (μ := P) _ _)
    rw [hEq0, add_zero] at this
    exact le_antisymm (hq j).1 ((hq j).2.trans this)
  have hint_h : ∫ x, h0' x ∂P = 1 - αs := by
    have hlim1 : Tendsto (fun j => 1 - a j) atTop (𝓝 (∫ x, h0' x ∂P)) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hL0)
      have hIint : ∫ x, I j x ∂P = P.real (S j) := by
        simp only [hIdef]; rw [integral_indicator_const _ (hSm j), smul_eq_mul, mul_one]
      rw [← hPS j, ← hIint, ← integral_sub (hIi j) hh0i, Real.norm_eq_abs]
      exact abs_integral_le_integral_abs
    exact tendsto_nhds_unique hlim1 (tendsto_const_nhds.sub hat)
  -- Step 2 (end): `A_j → E_P[β*hφ]`
  have hc : Tendsto (fun j => 1 / (1 - a j)) atTop (𝓝 β) :=
    tendsto_const_nhds.div (tendsto_const_nhds.sub hat) (ne_of_gt hη0)
  have hgi : ∀ j, Integrable (g j) P := fun j => Integrable.of_bound (hg j).1.aestronglyMeasurable
    (1 / (1 - a j)) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((hg j).2.1 x).1]; exact ((hg j).2.1 x).2)
  have hbhi : Integrable (fun x => β * h0' x) P := hh0i.const_mul β
  have hA_le2 : ∀ j, ‖A j - ∫ x, (β * h0' x) • φ x ∂P‖ ≤
      κ * (|1 / (1 - a j) - β| + β * ∫ x, |I j x - h0' x| ∂P) := by
    intro j
    refine (norm_integral_smul_sub_le hφ hκ (hgi j) hbhi).trans (mul_le_mul_of_nonneg_left ?_ hκ0)
    have hcongr : ∫ x, |g j x - β * h0' x| ∂P = ∫ x, |1 / (1 - a j) * I j x - β * h0' x| ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hg_ae j] with x hx
      rw [hx]
    rw [hcongr]
    have hpt : ∀ x, |1 / (1 - a j) * I j x - β * h0' x| ≤ |1 / (1 - a j) - β| + β * |I j x - h0' x| := by
      intro x
      have hI0 : 0 ≤ I j x := indicator_nonneg (fun _ _ => zero_le_one) x
      have hI1 : I j x ≤ 1 := indicator_le_self' (fun _ _ => zero_le_one) x |>.trans (by norm_num)
      calc |1 / (1 - a j) * I j x - β * h0' x| = |(1 / (1 - a j) - β) * I j x + β * (I j x - h0' x)| := by
            ring_nf
        _ ≤ |(1 / (1 - a j) - β) * I j x| + |β * (I j x - h0' x)| := abs_add_le _ _
        _ ≤ |1 / (1 - a j) - β| + β * |I j x - h0' x| := by
            rw [abs_mul, abs_mul, abs_of_pos hβ0, abs_of_nonneg hI0]
            gcongr
            exact mul_le_of_le_one_right (abs_nonneg _) hI1
    have hi1 : Integrable (fun x => |1 / (1 - a j) * I j x - β * h0' x|) P :=
      (((hIi j).const_mul _).sub hbhi).abs
    have hi2 : Integrable (fun x => |1 / (1 - a j) - β| + β * |I j x - h0' x|) P :=
      (integrable_const _).add ((hdi j).const_mul β)
    refine (integral_mono hi1 hi2 hpt).trans (le_of_eq ?_)
    rw [integral_add (integrable_const _) ((hdi j).const_mul β), integral_const, integral_const_mul,
      probReal_univ, one_smul]
  have hAlim2 : Tendsto A atTop (𝓝 (∫ x, (β * h0' x) • φ x ∂P)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun j => norm_nonneg _) hA_le2 ?_)
    have h1' : Tendsto (fun j => |1 / (1 - a j) - β|) atTop (𝓝 0) := by
      simpa [Real.norm_eq_abs] using tendsto_iff_norm_sub_tendsto_zero.1 hc
    simpa using (h1'.add (hL0.const_mul β)).const_mul κ
  have hμeq : μs = ∫ x, (β * h0' x) • φ x ∂P := tendsto_nhds_unique hAlim hAlim2
  -- Step 2 (end): `β* h P = R*`
  set k : 𝒳 → ℝ≥0 := fun x => Real.toNNReal (β * h0' x) with hkdef
  have hkm : Measurable k := (measurable_const.mul hh0m).real_toNNReal
  set ν : Measure 𝒳 := P.withDensity (fun x => (k x : ℝ≥0∞)) with hνdef
  have hνφ : ∫ x, φ x ∂ν = ∫ x, (β * h0' x) • φ x ∂P := by
    rw [hνdef, integral_withDensity_eq_integral_smul hkm φ]
    refine integral_congr_ae ?_
    filter_upwards [hh0nn] with x hx
    rw [NNReal.smul_def, hkdef, Real.coe_toNNReal _ (mul_nonneg hβ0.le hx)]
  have hνprob : IsProbabilityMeasure ν := by
    constructor
    rw [hνdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hnn : 0 ≤ᵐ[P] fun x => β * h0' x := by
      filter_upwards [hh0nn] with x hx; exact mul_nonneg hβ0.le hx
    have := (ofReal_integral_eq_lintegral_ofReal hbhi hnn).symm
    change ∫⁻ x, ENNReal.ofReal (β * h0' x) ∂P = 1
    rw [this, integral_const_mul, hint_h, hβ, one_div, inv_mul_cancel₀ (ne_of_gt hη0), ENNReal.ofReal_one]
  have hνeq : ν = contactLaw P Q := hchar ν (contactLaw P Q) hνprob hRs (by rw [hνφ, ← hμeq])
  -- Step 2 (end): `dR*/dP ∈ {0, β*}` a.e.
  have hrn : (contactLaw P Q).rnDeriv P =ᵐ[P] fun x => (k x : ℝ≥0∞) := by
    rw [← hνeq, hνdef]
    exact Measure.rnDeriv_withDensity P hkm.coe_nnreal_ennreal
  have hnull : P {x | 0 < ((contactLaw P Q).rnDeriv P x).toReal ∧
      ((contactLaw P Q).rnDeriv P x).toReal < 1 / (1 - αs)} = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hrn, h01] with x hx hx01
    simp only [mem_setOf_eq, hx, ENNReal.coe_toReal, hkdef, not_and, not_lt]
    intro hpos
    rcases hx01 with hx0 | hx1
    · rw [hx0, mul_zero, Real.toNNReal_zero, NNReal.coe_zero] at hpos; exact absurd hpos (lt_irrefl 0)
    · rw [hx1, mul_one, Real.coe_toNNReal _ hβ0.le]
  exact absurd hfrac (by rw [hnull]; exact lt_irrefl 0)

/-! ### Step 3 and the claim -/

theorem quantile_abs_le {P : Measure 𝒳} [IsProbabilityMeasure P] {f : 𝒳 → ℝ} {p t K : ℝ}
    (hq : IsQuantile P f p t) (hp0 : 0 < p) (hp1 : p < 1) (hK : ∀ x, |f x| ≤ K) : |t| ≤ K := by
  rw [abs_le]
  constructor
  · by_contra hlt
    push Not at hlt
    have he : {x | f x ≤ t} = ∅ := by
      ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      linarith [(abs_le.1 (hK x)).1]
    have := hq.2
    rw [he, measureReal_empty] at this
    linarith
  · by_contra hlt
    push Not at hlt
    have he : {x | f x < t} = univ := by
      ext x; simp only [mem_setOf_eq, mem_univ, iff_true]
      linarith [(abs_le.1 (hK x)).2]
    have := hq.1
    rw [he, probReal_univ] at this
    linarith

set_option maxHeartbeats 3200000 in
theorem nearcontact_a_of (hc : StatFormal.Wave30tx.Claims.contact) : StatFormal.Wave30tx.Claims.nearcontact_a := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ dstar s hφ hκ hchar h0 h1 hfrac hd hq hev
  obtain ⟨-, -, hmemT, -, -, hω⟩ := hc 𝒳 H P Q φ κ hφ hκ hchar h1
  have hRs : IsProbabilityMeasure (contactLaw P Q) := hmemT.1.1
  set αs := StatFormal.Distances.tvDist P Q with hαs
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ x₀)
  have hIoo : ∀ᶠ α in 𝓝[<] αs, α ∈ Ioo 0 αs := Ioo_mem_nhdsLT h0
  have hev2 := hIoo.and hev
  -- (a), first statement
  have part1 : ∀ (a : ℕ → ℝ) (h : 𝒳 → ℝ), (∀ j, a j < αs) → Tendsto a atTop (𝓝 αs) → Integrable h P →
      ¬ Tendsto (fun j => ∫ x, |{x | witFn ((Dpop φ P Q (a j))⁻¹ • dstar (a j)) φ x < s (a j)}.indicator
        (fun _ => (1 : ℝ)) x - h x| ∂P) atTop (𝓝 0) := by
    intro a h hlt hat hh hL
    have hat' : Tendsto a atTop (𝓝[<] αs) := tendsto_nhdsWithin_iff.2 ⟨hat, Eventually.of_forall hlt⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hat'.eventually hev2)
    have hN' : ∀ j, a (j + N) ∈ Ioo 0 αs ∧
        P {x | witFn ((Dpop φ P Q (a (j + N)))⁻¹ • dstar (a (j + N))) φ x = s (a (j + N))} = 0 :=
      fun j => hN (j + N) (by omega)
    exact no_L1_limit P Q hφ hκ hchar h0 h1 hfrac hω hRs dstar s (fun j => a (j + N)) (fun j => (hN' j).1)
      ((tendsto_add_atTop_iff_nat N).2 hat) (fun j => hd _ ⟨(hN' j).1.1.le, (hN' j).1.2⟩)
      (fun j => hq _ ⟨(hN' j).1.1.le, (hN' j).1.2⟩) (fun j => (hN' j).2) h hh
      ((tendsto_add_atTop_iff_nat N).2 hL)
  refine ⟨part1, fun ρ hρ => ?_⟩
  -- (a), second statement
  by_contra hnt
  rw [ENNReal.tendsto_nhds_top_iff_nnreal] at hnt
  push Not at hnt
  obtain ⟨C, hC⟩ := hnt
  have hfr := hC.and_eventually hev2
  rw [(nhdsLT_basis αs).frequently_iff] at hfr
  choose y hy hyp using fun k : ℕ => hfr (αs - 1 / ((k : ℝ) + 1)) (by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith)
  have hyt : Tendsto y atTop (𝓝 αs) := by
    have hlo : Tendsto (fun k : ℕ => αs - 1 / ((k : ℝ) + 1)) atTop (𝓝 αs) := by
      simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds (fun k => (hy k).1.le)
      (fun k => (hy k).2.le)
  -- the normalised witnesses along the sequence
  set fk : ℕ → H := fun k => (Dpop φ P Q (y k))⁻¹ • dstar (y k) with hfk
  have hDpos : ∀ k, 0 < Dpop φ P Q (y k) := by
    intro k
    have hyk := (hyp k).2.1
    have hne : Dpop φ P Q (y k) ≠ 0 := fun h0' => by
      have := (zeroeq 𝒳 H P Q φ κ (y k) hφ hκ hchar hyk.1.le (by linarith [hyk.2])).1 h0'
      linarith [hyk.2]
    exact lt_of_le_of_ne (by rw [RBasic.Dpop_eq_norm (hd _ ⟨hyk.1.le, hyk.2⟩)]; exact norm_nonneg _)
      (Ne.symm hne)
  have hnorm : ∀ k, ‖fk k‖ = 1 := by
    intro k
    have hyk := (hyp k).2.1
    rw [hfk, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hDpos k),
      ← RBasic.Dpop_eq_norm (hd _ ⟨hyk.1.le, hyk.2⟩), inv_mul_cancel₀ (ne_of_gt (hDpos k))]
  obtain ⟨fbar, ψ1, hψ1, hw⟩ := exists_weak_subseq fk (fun k => le_of_eq (hnorm k))
  have hsb : ∀ k, s (y (ψ1 k)) ∈ Icc (-κ) κ := by
    intro k
    have hyk := (hyp (ψ1 k)).2.1
    have := quantile_abs_le (hq _ ⟨hyk.1.le, hyk.2⟩) (by linarith [hyk.2]) (by linarith [hyk.1])
      (K := κ) (fun x => by
        have := abs_witFn_le hκ (fk (ψ1 k)) x
        rwa [hnorm, one_mul] at this)
    exact abs_le.1 this
  obtain ⟨sbar, -, ψ2, hψ2, hst⟩ := (isCompact_Icc (a := -κ) (b := κ)).tendsto_subseq hsb
  set ψ := ψ1 ∘ ψ2 with hψ
  have hψm : StrictMono ψ := hψ1.comp hψ2
  set fj : ℕ → 𝒳 → ℝ := fun k => witFn (fk (ψ k)) φ with hfj
  set sj : ℕ → ℝ := fun k => s (y (ψ k)) with hsj
  set fb : 𝒳 → ℝ := witFn fbar φ with hfb
  have hconv : ∀ x, Tendsto (fun k => fj k x) atTop (𝓝 (fb x)) := fun x =>
    (hw (φ x)).comp hψ2.tendsto_atTop
  have hsconv : Tendsto sj atTop (𝓝 sbar) := hst
  have hfjm : ∀ k, Measurable (fj k) := fun k => measurable_witFn hφ _
  have hfbm : Measurable fb := measurable_witFn hφ _
  -- the density bound along the sequence
  set K' : ℝ≥0∞ := (C : ℝ≥0∞) + 1 with hK'
  have hK'top : K' ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, ENNReal.one_ne_top⟩
  have hdens : ∀ k, ∀ B : Set ℝ, MeasurableSet B → B ⊆ Icc (sj k - ρ) (sj k + ρ) →
      P (fj k ⁻¹' B) ≤ K' * volume B := by
    intro k B hB hBs
    have hle : densUpper P (fj k) (sj k - ρ) (sj k + ρ) < K' :=
      lt_of_le_of_lt (hyp (ψ k)).1 (ENNReal.lt_add_right ENNReal.coe_ne_top one_ne_zero)
    obtain ⟨b, hb, hbK⟩ := sInf_lt_iff.1 hle
    exact (hb B hB hBs).trans (mul_le_mul_of_nonneg_right hbK.le (zero_le))
  -- `P(f̄ = s̄) = 0`
  set E := {x | fb x = sbar} with hE
  have hPE_le : ∀ ε : ℝ, 0 < ε → 2 * ε ≤ ρ → P E ≤ K' * ENNReal.ofReal (4 * ε) := by
    intro ε hε hερ
    set G : ℕ → Set 𝒳 := fun k => fj k ⁻¹' Ioo (sj k - 2 * ε) (sj k + 2 * ε) with hG
    have hPG : ∀ k, P (G k) ≤ K' * ENNReal.ofReal (4 * ε) := by
      intro k
      have := hdens k (Ioo (sj k - 2 * ε) (sj k + 2 * ε)) measurableSet_Ioo
        (Ioo_subset_Icc_self.trans (Icc_subset_Icc (by linarith) (by linarith)))
      rwa [Real.volume_Ioo, show sj k + 2 * ε - (sj k - 2 * ε) = 4 * ε by ring] at this
    set T : ℕ → Set 𝒳 := fun N => ⋂ k, ⋂ (_ : N ≤ k), G k with hT
    have hTm : Monotone T := by
      intro N N' hNN' x hx
      simp only [hT, mem_iInter] at hx ⊢
      exact fun k hk => hx k (hNN'.trans hk)
    have hET : E ⊆ ⋃ N, T N := by
      intro x hx
      have hx' : fb x = sbar := hx
      have hlim : Tendsto (fun k => fj k x - sj k) atTop (𝓝 0) := by
        simpa [hx'] using (hconv x).sub hsconv
      have hev' : ∀ᶠ k in atTop, fj k x - sj k ∈ Ioo (-(2 * ε)) (2 * ε) :=
        hlim.eventually (Ioo_mem_nhds (by linarith) (by linarith))
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev'
      refine mem_iUnion.2 ⟨N, ?_⟩
      simp only [hT, mem_iInter]
      intro k hk
      have := hN k hk
      simp only [hG, mem_preimage, mem_Ioo]
      constructor <;> linarith [this.1, this.2]
    calc P E ≤ P (⋃ N, T N) := measure_mono hET
      _ = ⨆ N, P (T N) := hTm.measure_iUnion
      _ ≤ K' * ENNReal.ofReal (4 * ε) := iSup_le fun N =>
          (measure_mono (fun x hx => by
            simp only [hT, mem_iInter] at hx; exact hx N le_rfl)).trans (hPG N)
  have hPE : P E = 0 := by
    have hlim : Tendsto (fun ε : ℝ => K' * ENNReal.ofReal (4 * ε)) (𝓝[>] 0) (𝓝 (K' * ENNReal.ofReal (4 * 0))) := by
      refine ENNReal.Tendsto.const_mul ?_ (Or.inr hK'top)
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        ((continuous_const.mul continuous_id).tendsto 0 |>.mono_left nhdsWithin_le_nhds)
    rw [mul_zero, ENNReal.ofReal_zero, mul_zero] at hlim
    have hev3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P E ≤ K' * ENNReal.ofReal (4 * ε) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / 2 by positivity)] with ε hε
      exact hPE_le ε hε.1 (by linarith [hε.2])
    exact le_antisymm (ge_of_tendsto hlim hev3) (zero_le)
  -- dominated convergence: `1_{A_k} → 1{f̄ < s̄}` in `L¹(P)`
  set Ib : 𝒳 → ℝ := {x | fb x < sbar}.indicator (fun _ => (1 : ℝ)) with hIb
  have hIbm : MeasurableSet {x | fb x < sbar} := measurableSet_lt hfbm measurable_const
  have hIbi : Integrable Ib P := (integrable_const (1 : ℝ)).indicator hIbm
  set Fk : ℕ → 𝒳 → ℝ := fun k x => |{x | fj k x < sj k}.indicator (fun _ => (1 : ℝ)) x - Ib x| with hFk
  have hDCT : Tendsto (fun k => ∫ x, Fk k x ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P) (F := Fk) (f := fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ))
      (fun k => (continuous_abs.measurable.comp
        (((measurable_const.indicator (measurableSet_lt (hfjm k) measurable_const))).sub
          (measurable_const.indicator hIbm))).aestronglyMeasurable)
      (integrable_const _)
      (fun k => ae_of_all _ fun x => by
        simp only [hFk, hIb, Real.norm_eq_abs, abs_abs, Set.indicator_apply]
        split_ifs <;> norm_num)
      (by
        have hne : ∀ᵐ x ∂P, x ∉ E := measure_eq_zero_iff_ae_notMem.1 hPE
        filter_upwards [hne] with x hx
        have hx' : fb x ≠ sbar := hx
        have hlim : Tendsto (fun k => fj k x - sj k) atTop (𝓝 (fb x - sbar)) := (hconv x).sub hsconv
        rcases lt_or_gt_of_ne hx' with hlt | hgt
        · have hev' : ∀ᶠ k in atTop, fj k x - sj k < 0 := hlim.eventually (gt_mem_nhds (by linarith))
          refine tendsto_const_nhds.congr' (hev'.mono fun k hk => ?_)
          have h1' : fj k x < sj k := by linarith
          simp [hFk, hIb, Set.indicator_apply, h1', hlt]
        · have hev' : ∀ᶠ k in atTop, 0 < fj k x - sj k := hlim.eventually (lt_mem_nhds (by linarith))
          refine tendsto_const_nhds.congr' (hev'.mono fun k hk => ?_)
          have h1' : ¬ fj k x < sj k := by linarith
          have h2' : ¬ fb x < sbar := by linarith
          simp [hFk, hIb, Set.indicator_apply, h1', h2'])
    simpa using this
  exact part1 (fun k => y (ψ k)) Ib (fun k => (hy (ψ k)).2) (hyt.comp hψm.tendsto_atTop) hIbi hDCT

end StatFormal.Wave30tx.RNearA
