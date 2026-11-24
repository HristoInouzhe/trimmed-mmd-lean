import StatFormal.Archive.Wave30h.RouteOP
import StatFormal.Lib.DKW.Massart
import Mathlib.Probability.Independence.Basic

/-!
# Route — `lem:quantiles`, the Dvoretzky–Kiefer–Wolfowitz–Massart step (untrusted)

* `map_sample_eq_pi`: the first `n` terms of an i.i.d. sequence have law `F^{⊗n}`.
* `dkw_event`: for every `η > 0` there are `M ≥ 0` and, for every `n ≥ 1`, a measurable event of probability
  `≥ 1 − η` on which `|F_n(t) − F(t)| ≤ M/√n` for all `t` (the certified-library `DKW.Massart.massart` with the
  score `V(x) = e^x`, the bad set enlarged to its measurable hull).
* `quantiles_dkw`.
* `dkw_coords`: the same simultaneously for the `d` coordinates of an i.i.d. sequence in `ℝ^d`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave30h

open StatFormal.Wave9b (BigOP)
open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.Wave24f (marg)

lemma map_sample_eq_pi {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → E} {F : Measure E} (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X P)
    (hlaw : ∀ j, P.map (X j) = F) (n : ℕ) :
    P.map (fun ω (j : Fin n) => X j ω) = Measure.pi fun _ : Fin n => F := by
  have hind' : iIndepFun (fun j : Fin n => X j) P := hind.precomp Fin.val_injective
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun j : Fin n => (hX j).aemeasurable)).1 hind']
  simp only [hlaw]

/-- The DKW–Massart bound on the sample space: `F^{⊗n}{∃ t, c < |F_n(t) − F(t)|} ≤ 2e^{−2nc²}` (outer measure). -/
lemma massart_real (F : Measure ℝ) [IsProbabilityMeasure F] {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 0 ≤ c) :
    (Measure.pi fun _ : Fin n => F) {y | ∃ t, c < |empCdf y t - cdf F t|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * n * c ^ 2)) := by
  set V : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp x)
  have hV : Measurable V := ENNReal.measurable_ofReal.comp Real.measurable_exp
  have hVle : ∀ x t, V x ≤ V t ↔ x ≤ t := fun x t => by
    simp only [V]
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos t).le, Real.exp_le_exp]
  refine (measure_mono fun y hy => ?_).trans (StatFormal.DKW.Massart.massart F V hV hn hc)
  obtain ⟨t, ht⟩ := hy
  refine ⟨V t, ?_⟩
  have h1 : (Finset.univ.filter fun i => V (y i) ≤ V t) = Finset.univ.filter fun i => y i ≤ t := by
    ext i; simp [hVle]
  have h2 : {x | V x ≤ V t} = Iic t := by ext x; simp [hVle]
  rw [h1, h2, ← measureReal_def, ← cdf_eq_real]
  exact ht

/-- DKW in event form, with a nonnegative constant. -/
lemma dkw_event (F : Measure ℝ) [IsProbabilityMeasure F] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X P)
    (hlaw : ∀ j, P.map (X j) = F) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, 1 ≤ n → ∃ A : Set Ω, MeasurableSet A ∧ P Aᶜ ≤ ENNReal.ofReal η ∧
      ∀ ω ∈ A, ∀ t, |empCdf (fun j : Fin n => X j ω) t - cdf F t| ≤ M * (1 / Real.sqrt n) := by
  set M : ℝ := Real.sqrt (max 0 (Real.log (2 / η) / 2)) with hM
  refine ⟨M, Real.sqrt_nonneg _, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set c : ℝ := M * (1 / Real.sqrt n)
  have hc : 0 ≤ c := mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  set B : Set (Fin n → ℝ) := {y | ∃ t, c < |empCdf y t - cdf F t|}
  set T := toMeasurable (Measure.pi fun _ : Fin n => F) B
  have hsm : Measurable fun ω (j : Fin n) => X j ω := measurable_pi_iff.2 fun j => hX j
  refine ⟨((fun ω (j : Fin n) => X j ω) ⁻¹' T)ᶜ, (hsm (measurableSet_toMeasurable _ _)).compl, ?_, ?_⟩
  · simp only [compl_compl]
    rw [← Measure.map_apply hsm (measurableSet_toMeasurable _ _), map_sample_eq_pi hX hind hlaw n,
      measure_toMeasurable]
    refine (massart_real F hn hc).trans (ENNReal.ofReal_le_ofReal ?_)
    -- `2 e^{−2nc²} = 2 e^{−2M²} ≤ η`
    have hc2 : (n : ℝ) * c ^ 2 = M ^ 2 := by
      simp only [c]
      rw [mul_pow, div_pow, Real.sq_sqrt hnpos.le]; field_simp
    have hM2 : M ^ 2 = max 0 (Real.log (2 / η) / 2) := Real.sq_sqrt (le_max_left _ _)
    have : -2 * n * c ^ 2 ≤ Real.log (η / 2) := by
      have h1 : -2 * (n : ℝ) * c ^ 2 = -2 * M ^ 2 := by rw [mul_assoc, hc2]
      rw [h1, hM2]
      have : Real.log (η / 2) = -Real.log (2 / η) := by
        rw [← Real.log_inv, inv_div]
      rw [this]
      nlinarith [le_max_right 0 (Real.log (2 / η) / 2)]
    calc 2 * Real.exp (-2 * n * c ^ 2) ≤ 2 * Real.exp (Real.log (η / 2)) := by gcongr
      _ = η := by rw [Real.exp_log (by positivity)]; ring
  · intro ω hω t
    simp only [mem_compl_iff, mem_preimage] at hω
    by_contra hlt
    push_neg at hlt
    exact hω (subset_toMeasurable _ _ ⟨t, hlt⟩)

theorem quantiles_dkw : Claims.quantiles_dkw := by
  intro F _ Ω _ P _ X hX hind hlaw
  rw [bigOP_iff_compl (fun n => by positivity)]
  intro η hη
  obtain ⟨M, hM, hA⟩ := dkw_event F hX hind hlaw hη
  refine ⟨M, hM, 1, fun n hn => ?_⟩
  obtain ⟨A, hAm, hPA, hb⟩ := hA n hn
  refine ⟨A, hAm, hPA, fun ω hω => iSup_le fun t => ENNReal.ofReal_le_ofReal (hb ω hω t)⟩

/-- The coordinates of an i.i.d. sequence in `ℝ^d` are i.i.d. with the marginal laws. -/
lemma coord_iid {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Measure (Euc d)}
    {X : ℕ → Ω → Euc d} (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X P) (hlaw : ∀ j, P.map (X j) = μ)
    (i : Fin d) :
    (∀ j, Measurable fun ω => X j ω i) ∧ iIndepFun (fun j ω => X j ω i) P ∧
      ∀ j, P.map (fun ω => X j ω i) = marg μ i := by
  have hc : Measurable fun x : Euc d => x i := (EuclideanSpace.proj i).continuous.measurable
  refine ⟨fun j => hc.comp (hX j), hind.comp (fun _ x => x i) fun _ => hc, fun j => ?_⟩
  rw [marg, ← hlaw j, Measure.map_map hc (hX j)]; rfl

/-- DKW for all `d` coordinates simultaneously. -/
lemma dkw_coords {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {X : ℕ → Ω → Euc d} (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X P) (hlaw : ∀ j, P.map (X j) = μ) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, 1 ≤ n → ∃ A : Set Ω, MeasurableSet A ∧ P Aᶜ ≤ ENNReal.ofReal η ∧
      ∀ ω ∈ A, ∀ i t, |empCdf (fun j : Fin n => X j ω i) t - cdf (marg μ i) t| ≤ M * (1 / Real.sqrt n) := by
  have hη' : 0 < η / (d + 1) := by positivity
  have hprob : ∀ i, IsProbabilityMeasure (marg μ i) := fun i => by
    unfold marg; infer_instance
  choose M hM hA using fun i => by
    have := hprob i
    obtain ⟨hXi, hindi, hlawi⟩ := coord_iid hX hind hlaw i
    exact dkw_event (marg μ i) hXi hindi hlawi hη'
  refine ⟨∑ i, M i, Finset.sum_nonneg fun i _ => hM i, fun n hn => ?_⟩
  choose A hAm hPA hb using fun i => hA i n hn
  refine ⟨⋂ i, A i, MeasurableSet.iInter hAm, ?_, fun ω hω i t => ?_⟩
  · rw [compl_iInter]
    refine (measure_iUnion_fintype_le _ _).trans ?_
    calc ∑ i, P (A i)ᶜ ≤ ∑ _i : Fin d, ENNReal.ofReal (η / (d + 1)) := Finset.sum_le_sum fun i _ => hPA i
      _ = ENNReal.ofReal (d * (η / (d + 1))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (by
          rw [mul_div_assoc']; rw [div_le_iff₀ (by positivity)]; nlinarith)
  · refine (hb i ω (mem_iInter.1 hω i) t).trans ?_
    gcongr
    exact Finset.single_le_sum (fun i _ => hM i) (Finset.mem_univ i)

end StatFormal.Wave30h
