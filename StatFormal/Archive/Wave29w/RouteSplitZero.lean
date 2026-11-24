import StatFormal.Archive.Wave29w.Statements
import StatFormal.Lib.TrimmedMean.AlphaZero
import StatFormal.Lib.TrimmedMean.Population
import StatFormal.Archive.Wave22c.RouteSplit

/-!
# Route — trimmed MMD `thm:split` at `α = 0` (untrusted)

* `split_zero_means`: `Foundations/TrimmedMean/AlphaZero` (`capped n 0` is the uniform weight vector; the plug-in
  variance centred at the maximum is the sample variance).
* `split_zero_asymp_normal`: the population identification `sep = P h − Q h` from `Foundations/TrimmedMean/Population`
  `sepVal_eq` at the quantiles `q = ‖f‖κ'` (a `1`-quantile of `h` under `P`) and `q' = −‖f‖κ'` (a `0`-quantile under
  `Q`), where `(q − h)_+ = q − h`, `(h − q')_+ = h − q'`; then `clt_zero` (two-sample CLT, `clt_two_sample`).
* `split_zero_coverage`: `coverage_zero` (plug-in consistency + Slutsky + portmanteau).
* `split_zero_level`: coverage (`σ₀² > 0`: `coverage_zero`; `σ₀² = 0`: `coverage_zero_degenerate`, the lower
  limit equals `sep` a.s. eventually) fed into the certified frozen `Wave22c.split_level` at `α = 0`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatFormal.Wave29w

open StatFormal.Foundations.TrimmedMean StatFormal.Foundations.CLT
open StatFormal.Wave29i (splitStat splitSEn)
open StatFormal.Wave17a (sepVal)
open StatFormal.TrimmedMMD.Concentration (region)

theorem split_zero_means : Claims.split_zero_means := by
  intro n m v vx vy hn hm
  refine ⟨trimLo_zero hn v, trimUp_zero hn v, varLo_zero_centred hn v, ?_⟩
  change √(varLo n 0 vx / n + varLo m 0 (fun j => -vy j) / m) / (1 - 0) = _
  rw [varLo_zero_centred hn, varLo_zero_centred hm, sub_zero, div_one]
  have e : ∀ j, (-vy j - (∑ k, -vy k) / m) ^ 2 = (vy j - (∑ k, vy k) / m) ^ 2 := fun j => by
    rw [Finset.sum_neg_distrib]; ring
  simp only [e]

section Sep

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ' : ℝ} {f : H}

/-- At `α = 0` the population separation is the difference of means. -/
lemma sep_zero (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ') :
    sepVal f (region φ 0 P) (region φ 0 Q) = ((∫ x, ⟪f, φ x⟫ ∂P - ∫ x, ⟪f, φ x⟫ ∂Q : ℝ) : EReal) := by
  set q := ‖f‖ * κ'
  have hb : ∀ x, |⟪f, φ x⟫| ≤ q := abs_inner_le hκ f
  have hm := measurable_inner_comp hφ f
  have hint : ∀ R : Measure 𝒳, [IsProbabilityMeasure R] → Integrable (fun x => ⟪f, φ x⟫) R := fun R _ =>
    Integrable.of_bound hm.aestronglyMeasurable q (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have hle : ∀ x, ⟪f, φ x⟫ ≤ q := fun x => (le_abs_self _).trans (hb x)
  have hge : ∀ x, -q ≤ ⟪f, φ x⟫ := fun x => (neg_le_neg (hb x)).trans (neg_abs_le _)
  have h1 : P.real {x | ⟪f, φ x⟫ < q} ≤ 1 - 0 := by rw [sub_zero]; exact measureReal_le_one
  have h2 : 1 - 0 ≤ P.real {x | ⟪f, φ x⟫ ≤ q} := by
    have : {x | ⟪f, φ x⟫ ≤ q} = Set.univ := Set.eq_univ_of_forall hle
    rw [this, probReal_univ, sub_zero]
  have h3 : Q.real {x | ⟪f, φ x⟫ < -q} ≤ 0 := by
    have : {x | ⟪f, φ x⟫ < -q} = ∅ := Set.eq_empty_of_forall_notMem fun x hx => by
      simp only [Set.mem_ofPred_eq] at hx; linarith [hge x]
    rw [this, measureReal_empty]
  have h4 : 0 ≤ Q.real {x | ⟪f, φ x⟫ ≤ -q} := measureReal_nonneg
  rw [sepVal_eq P Q hφ hκ le_rfl zero_lt_one f h1 h2 h3 h4]
  congr 1
  have e1 : (fun x => max (q - ⟪f, φ x⟫) 0) = fun x => q - ⟪f, φ x⟫ :=
    funext fun x => max_eq_left (sub_nonneg.2 (hle x))
  have e2 : (fun x => max (⟪f, φ x⟫ - -q) 0) = fun x => ⟪f, φ x⟫ - -q :=
    funext fun x => max_eq_left (sub_nonneg.2 (hge x))
  rw [e1, e2, sub_zero, inv_one, one_mul, one_mul, integral_sub (integrable_const _) (hint P),
    integral_sub (hint Q) (integrable_const _), integral_const, integral_const, probReal_univ, probReal_univ,
    one_smul, one_smul]
  ring

end Sep

theorem split_zero_asymp_normal : Claims.split_zero_asymp_normal := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' κ f Ω _ μ _ X Y m hφ hκ hXm hYm hXi hYi hXY hXl hYl hκ0 hmr
  exact ⟨sep_zero hφ hκ, clt_zero ⟨hXm, hXi, hXl⟩ ⟨hYm, hYi, hYl⟩ hXY (measurable_inner_comp hφ f)
    (abs_inner_le hκ f) hκ0 hmr⟩

theorem split_zero_coverage : Claims.split_zero_coverage := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' κ f Ω _ μ _ X Y m hφ hκ hXm hYm hXi hYi hXY hXl hYl hκ0 hmr hσ z
  have key := coverage_zero ⟨hXm, hXi, hXl⟩ ⟨hYm, hYi, hYl⟩ hXY (measurable_inner_comp hφ f) (abs_inner_le hκ f)
    hκ0 hmr hσ z
  refine key.congr fun n => ?_
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, sep_zero hφ hκ, EReal.coe_le_coe_iff]
  rfl

theorem split_zero_level : Claims.split_zero_level := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' κ δ z f Ω _ μ _ X Y m hφ hκ hXm hYm hXi hYi hXY hXl hYl hκ0 hmr hz
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  have hm := measurable_inner_comp hφ f
  have hsep := sep_zero (P := P) (Q := Q) hφ hκ (f := f)
  set Tlo : ℕ → Ω → ℝ := fun n ω => splitStat φ f X Y m 0 n ω - z * splitSEn φ f X Y m 0 n ω with hTlo
  have hTm : ∀ n, Measurable (Tlo n) := fun n =>
    (measurable_statT hX hY hm le_rfl zero_lt_one m n).sub ((measurable_seHat hX hY hm 0 m n).const_mul z)
  set E : ℕ → Set Ω := fun n => {ω | ((Tlo n ω : ℝ) : EReal) ≤ sepVal f (region φ 0 P) (region φ 0 Q)} with hE
  have hEeq : ∀ n, E n = {ω | Tlo n ω ≤ ∫ x, ⟪f, φ x⟫ ∂P - ∫ x, ⟪f, φ x⟫ ∂Q} := fun n => by
    ext ω; simp only [hE, Set.mem_ofPred_eq, hsep, EReal.coe_le_coe_iff]
  have hEm : ∀ n, MeasurableSet (E n) := fun n => by
    rw [hEeq]; exact measurableSet_le (hTm n) measurable_const
  have hδ0 : 0 ≤ δ := hz ▸ measureReal_nonneg
  have h1 : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real (E n) := by
    intro η hη
    have hσ0 : 0 ≤ Var[fun x => ⟪f, φ x⟫; P] + Var[fun x => ⟪f, φ x⟫; Q] / κ :=
      add_nonneg (variance_nonneg _ _) (div_nonneg (variance_nonneg _ _) hκ0.le)
    rcases hσ0.lt_or_eq with hσ | hσ
    · have hcov := coverage_zero hX hY hXY hm (abs_inner_le hκ f) hκ0 hmr hσ z
      have hΦ : (gaussianReal 0 1).real (Iic z) = 1 - δ := by
        rw [← hz, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]; ring
      rw [hΦ] at hcov
      filter_upwards [hcov.eventually (Ioi_mem_nhds (show 1 - δ - η < 1 - δ by linarith))] with n hn
      rw [hEeq]
      exact le_of_lt hn
    · filter_upwards [coverage_zero_degenerate hX hY hm (abs_inner_le hκ f) hκ0 hmr hσ.symm z] with n hn
      have hae : ∀ᵐ ω ∂μ, ω ∈ E n := by
        filter_upwards [hn] with ω hω
        rw [hEeq]
        exact le_of_eq hω
      have h1 : μ (E n) = 1 := (prob_compl_eq_zero_iff (hEm n)).1 (ae_iff.1 hae)
      rw [measureReal_def, h1, ENNReal.toReal_one]
      linarith
  obtain ⟨a, b⟩ := StatFormal.Wave22c.split_level 𝒳 H P Q φ κ' 0 δ f Ω (fun _ => μ) Tlo E hφ hκ le_rfl
    zero_lt_one (fun _ => inferInstance) hEm (fun n ω hω => hω) h1
  exact ⟨h1, a, fun n ω hω hpos => b n ω hω hpos⟩

end StatFormal.Wave29w
