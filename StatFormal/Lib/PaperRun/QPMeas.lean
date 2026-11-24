import StatFormal.Wave31tr.Statements
import StatFormal.Lib.MeasurableSelection.Argmin
import StatFormal.Archive.Wave8a.RouteGeorep

/-!
# The quadratic program `eq:qp`: measurable exact minimizers and measurable derived quantities (library)

Library component (untrusted). `φ : 𝒳 → H` strongly measurable, `H` a real inner-product space. For maps `x : Ω → 𝒳ⁿ`,
`w : Ω → ℝⁿ`, … measurable in a parameter `ω` (the sample, or the sample and an evaluation point):

* `stronglyMeasurable_wsum`: `ω ↦ Σ_i w_i(ω) φ(x_i(ω))` is strongly measurable (jointly in the points and the weights);
* `measurable_qpVal`, `stronglyMeasurable_witness`, `measurable_ownX`, `measurable_ownY`, `measurable_witness_apply`: the value
  `D̂`, the witness `eq:witness`, the own-term values and `z ↦ ⟪f̂, φ z⟫` are measurable;
* `isCompact_capped`, `capped_unif`: the capped simplex `{w | IsCapped α w}` is compact, and nonempty (uniform weights) for
  `n ≥ 1`, `0 ≤ α < 1`;
* `exists_qpSel` (Aliprantis–Border Thm 18.19 via `exists_measurable_argmin_on`): a measurable selection of exact minimizers;
* `isCapped_iff`, `qp_eq_qpVal_sq`, `isQPMin_iff`: the two library encodings of `eq:qp` (`Wave30tz` and `TrimmedMMD.BangBang`) agree;
* `qpVal_eq_Demp`: at an exact minimizer `D̂ = Demp` (the certified `Wave8a.georep_qp`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.PaperRun

open StatFormal.Wave30tz StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.Unconditional

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Ω : Type*} [MeasurableSpace Ω] {φ : 𝒳 → H}

/-! ### Measurability of the derived quantities -/

/-- `ω ↦ Σ_i w_i(ω) φ(x_i(ω))` is strongly measurable. -/
theorem stronglyMeasurable_wsum (hφ : StronglyMeasurable φ) {n : ℕ} {x : Ω → Fin n → 𝒳} {w : Ω → Fin n → ℝ}
    (hx : Measurable x) (hw : Measurable w) : StronglyMeasurable fun ω => wsum φ (x ω) (w ω) := by
  unfold wsum
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).comp hw).stronglyMeasurable.smul (hφ.comp_measurable ((measurable_pi_apply i).comp hx))

/-- `ω ↦ wsum φ x w − wsum φ y v` is strongly measurable. -/
theorem stronglyMeasurable_diff (hφ : StronglyMeasurable φ) {n m : ℕ} {x : Ω → Fin n → 𝒳} {y : Ω → Fin m → 𝒳}
    {w : Ω → Fin n → ℝ} {v : Ω → Fin m → ℝ} (hx : Measurable x) (hy : Measurable y) (hw : Measurable w)
    (hv : Measurable v) : StronglyMeasurable fun ω => wsum φ (x ω) (w ω) - wsum φ (y ω) (v ω) :=
  (stronglyMeasurable_wsum hφ hx hw).sub (stronglyMeasurable_wsum hφ hy hv)

/-- `D̂ = qpVal` is measurable jointly in the points and the weights. -/
theorem measurable_qpVal (hφ : StronglyMeasurable φ) {n m : ℕ} {x : Ω → Fin n → 𝒳} {y : Ω → Fin m → 𝒳}
    {w : Ω → Fin n → ℝ} {v : Ω → Fin m → ℝ} (hx : Measurable x) (hy : Measurable y) (hw : Measurable w)
    (hv : Measurable v) : Measurable fun ω => qpVal φ (x ω) (y ω) (w ω) (v ω) :=
  (stronglyMeasurable_diff hφ hx hy hw hv).norm.measurable

/-- The witness `eq:witness` is strongly measurable. -/
theorem stronglyMeasurable_witness (hφ : StronglyMeasurable φ) {n m : ℕ} {x : Ω → Fin n → 𝒳} {y : Ω → Fin m → 𝒳}
    {w : Ω → Fin n → ℝ} {v : Ω → Fin m → ℝ} (hx : Measurable x) (hy : Measurable y) (hw : Measurable w)
    (hv : Measurable v) : StronglyMeasurable fun ω => witness φ (x ω) (y ω) (w ω) (v ω) :=
  (measurable_qpVal hφ hx hy hw hv).inv.stronglyMeasurable.smul (stronglyMeasurable_diff hφ hx hy hw hv)

/-- `ω ↦ ⟪f̂(ω), φ(z(ω))⟫` is measurable (the fitted witness evaluated at a measurable point). -/
theorem measurable_witness_apply (hφ : StronglyMeasurable φ) {n m : ℕ} {x : Ω → Fin n → 𝒳} {y : Ω → Fin m → 𝒳}
    {w : Ω → Fin n → ℝ} {v : Ω → Fin m → ℝ} {z : Ω → 𝒳} (hx : Measurable x) (hy : Measurable y) (hw : Measurable w)
    (hv : Measurable v) (hz : Measurable z) :
    Measurable fun ω => ⟪witness φ (x ω) (y ω) (w ω) (v ω), φ (z ω)⟫_ℝ :=
  ((stronglyMeasurable_witness hφ hx hy hw hv).inner (hφ.comp_measurable hz)).measurable

/-- The own-term values at the `X`'s are measurable. -/
theorem measurable_ownX (hφ : StronglyMeasurable φ) {n m : ℕ} {x : Ω → Fin n → 𝒳} {y : Ω → Fin m → 𝒳}
    {w : Ω → Fin n → ℝ} {v : Ω → Fin m → ℝ} (hx : Measurable x) (hy : Measurable y) (hw : Measurable w)
    (hv : Measurable v) : Measurable fun ω => ownX φ (x ω) (y ω) (w ω) (v ω) := by
  refine Measurable.of_eval fun i => ?_
  unfold ownX
  have hxi : Measurable fun ω => x ω i := (measurable_pi_apply i).comp hx
  exact (measurable_witness_apply hφ hx hy hw hv hxi).sub
    ((((measurable_pi_apply i).comp hw).mul ((hφ.comp_measurable hxi).norm.measurable.pow_const 2)).div
      (measurable_qpVal hφ hx hy hw hv))

/-- The own-term values at the `Y`'s are measurable. -/
theorem measurable_ownY (hφ : StronglyMeasurable φ) {n m : ℕ} {x : Ω → Fin n → 𝒳} {y : Ω → Fin m → 𝒳}
    {w : Ω → Fin n → ℝ} {v : Ω → Fin m → ℝ} (hx : Measurable x) (hy : Measurable y) (hw : Measurable w)
    (hv : Measurable v) : Measurable fun ω => ownY φ (x ω) (y ω) (w ω) (v ω) := by
  refine Measurable.of_eval fun j => ?_
  unfold ownY
  have hyj : Measurable fun ω => y ω j := (measurable_pi_apply j).comp hy
  exact (measurable_witness_apply hφ hx hy hw hv hyj).add
    ((((measurable_pi_apply j).comp hv).mul ((hφ.comp_measurable hyj).norm.measurable.pow_const 2)).div
      (measurable_qpVal hφ hx hy hw hv))

/-! ### The capped simplex -/

/-- The capped simplex is compact (closed and inside a box). -/
theorem isCompact_capped (n : ℕ) (α : ℝ) : IsCompact {w : Fin n → ℝ | IsCapped α w} := by
  refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1 / (n * (1 - α)))).of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {w : Fin n → ℝ | ∀ i, 0 ≤ w i ∧ w i ≤ 1 / (n * (1 - α))} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i =>
        (isClosed_le continuous_const (continuous_apply i)).inter (isClosed_le (continuous_apply i) continuous_const)
    have h2 : IsClosed {w : Fin n → ℝ | ∑ i, w i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  · intro w hw
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    exact hw.1

/-- Uniform weights are capped (`n ≥ 1`, `0 ≤ α < 1`; copy-adapted from the scratch check `PaperRunCheck.lean`). -/
theorem capped_unif {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {n : ℕ} (hn : 1 ≤ n) :
    IsCapped α (fun _ : Fin n => (1 : ℝ) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨fun i => ⟨by positivity, ?_⟩, ?_⟩
  · apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  · simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    field_simp

/-! ### The two encodings of `eq:qp` -/

theorem isCapped_iff (α : ℝ) {n : ℕ} (w : Fin n → ℝ) : IsCapped α w ↔ w ∈ capped n α := Iff.rfl

omit [MeasurableSpace 𝒳] in
theorem qp_eq_qpVal_sq (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) :
    qp (fun i => φ (x i)) (fun j => φ (y j)) (w, v) = qpVal φ x y w v ^ 2 := rfl

omit [MeasurableSpace 𝒳] in
theorem isQPMin_iff (φ : 𝒳 → H) (α : ℝ) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (w : Fin n → ℝ) (v : Fin m → ℝ) :
    IsQPMin φ α x y w v ↔ (w, v) ∈ capped n α ×ˢ capped m α ∧
      IsMinOn (qp (fun i => φ (x i)) (fun j => φ (y j))) (capped n α ×ˢ capped m α) (w, v) := by
  constructor
  · rintro ⟨hw, hv, hmin⟩
    refine ⟨⟨hw, hv⟩, fun p hp => ?_⟩
    simp only [Set.mem_ofPred_eq]
    rw [qp_eq_qpVal_sq]
    obtain ⟨p1, p2⟩ := p
    rw [show qp (fun i => φ (x i)) (fun j => φ (y j)) (p1, p2) = qpVal φ x y p1 p2 ^ 2 from rfl]
    exact pow_le_pow_left₀ (norm_nonneg _) (hmin p1 p2 hp.1 hp.2) 2
  · rintro ⟨⟨hw, hv⟩, hmin⟩
    refine ⟨hw, hv, fun w' v' hw' hv' => ?_⟩
    have := hmin (show (w', v') ∈ capped n α ×ˢ capped m α from ⟨hw', hv'⟩)
    simp only [Set.mem_ofPred_eq] at this
    rw [qp_eq_qpVal_sq, qp_eq_qpVal_sq] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

/-! ### Existence of a measurable selection, and `D̂ = Demp` -/

/-- **Measurable exact minimizers of `eq:qp`** (Aliprantis–Border Thm 18.19): for `n, m ≥ 1`, `0 ≤ α < 1`, a measurable selection
of exact minimizers exists (the objective is continuous in the weights and measurable in the sample; the feasible set is a fixed
nonempty compact set). -/
theorem exists_qpSel (hφ : StronglyMeasurable φ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ∃ σ : (Fin n → 𝒳) × (Fin m → 𝒳) → (Fin n → ℝ) × (Fin m → ℝ), StatFormal.Wave31tr.IsQPSel φ α σ := by
  set K : Set ((Fin n → ℝ) × (Fin m → ℝ)) := {w | IsCapped α w} ×ˢ {v | IsCapped α v} with hK
  have hKc : IsCompact K := (isCompact_capped n α).prod (isCompact_capped m α)
  have hKne : K.Nonempty := ⟨(_, _), capped_unif hα0 hα1 hn, capped_unif hα0 hα1 hm⟩
  obtain ⟨σ, hσm, hσK, hσmin, -⟩ := StatFormal.Foundations.MeasurableSelection.exists_measurable_argmin_on K hKc hKne
    (fun (p : (Fin n → 𝒳) × (Fin m → 𝒳)) (e : (Fin n → ℝ) × (Fin m → ℝ)) => qpVal φ p.1 p.2 e.1 e.2)
    (fun e _ => measurable_qpVal hφ measurable_fst measurable_snd measurable_const measurable_const)
    (fun p => by
      apply Continuous.continuousOn
      unfold qpVal wsum
      fun_prop)
  exact ⟨σ, hσm, fun p => ⟨(hσK p).1, (hσK p).2, fun w' v' hw' hv' => hσmin p (w', v') ⟨hw', hv'⟩⟩⟩

/-- At an exact minimizer, `D̂ = Demp` (the certified `Wave8a.georep_qp`: `Demp² = min qp`). -/
theorem qpVal_eq_Demp {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {x : Fin n → 𝒳} {y : Fin m → 𝒳} {w : Fin n → ℝ} {v : Fin m → ℝ} (h : IsQPMin φ α x y w v) :
    qpVal φ x y w v = Demp φ x y α := by
  obtain ⟨p, hp, hpmin, hD⟩ := StatFormal.Wave8a.georep_qp 𝒳 H φ α n m x y hφ hα0 hα1 hn hm
  obtain ⟨hwv, hmin⟩ := (isQPMin_iff φ α x y w v).mp h
  have e1 : qp (fun i => φ (x i)) (fun j => φ (y j)) (w, v) ≤ qp (φ ∘ x) (φ ∘ y) p := hmin hp
  have e2 : qp (φ ∘ x) (φ ∘ y) p ≤ qp (fun i => φ (x i)) (fun j => φ (y j)) (w, v) := hpmin hwv
  have hsq : qpVal φ x y w v ^ 2 = Demp φ x y α ^ 2 := by
    rw [← qp_eq_qpVal_sq, hD]; exact le_antisymm e1 e2
  have hD0 : 0 ≤ Demp φ x y α := by
    unfold Demp setDist
    exact Real.sInf_nonneg fun r ⟨a, _, b, _, hr⟩ => hr ▸ norm_nonneg _
  exact (pow_left_inj₀ (norm_nonneg _) hD0 two_ne_zero).mp hsq

end StatFormal.PaperRun
