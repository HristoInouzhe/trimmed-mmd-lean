import StatFormal.Wave30tn.RouteBootSeq
import StatFormal.Wave30tn.RouteLower

/-!
# Route — wave 30tn: `thm:split` (ii), the bootstrap clause for arbitrary sizes (untrusted)

* `boot_std_unif`: the sequential theorem `boot_std_seq` in uniform (`ε`–`δ`) form over all sizes `a, b ≥ N` (by
  contradiction over arbitrary data and size sequences; a side is admissible at tolerance `δ` if it is non-degenerate with
  plug-in variance and remainder `δ`-close, or exactly degenerate — `SideOK`).
* `tip0_bootStd`: if each side is admissible with probability `→ 1` at every tolerance, the bootstrap cdf of the
  standardised root converges in probability to `Φ(t)`.
* Inputs: for `α ∈ (0,1)` under `ass:split`, the library's one-sample `tip0_varLo`, `tip0_bootD` (quantile uniqueness, no
  ratio) on each side; for `α = 0`, `tip0_varLo_zero` and `bootD_zero`, and, when one variance vanishes, the sample is
  almost surely constant, so `A* ≡ D* ≡ 0` on that side (`ae_const_sample`).
* The `ŝe*/σ → 1` conjuncts are the frozen wave-30dd `split_boot_se_any`, `split_zero_boot_se_any`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open Finset Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatFormal.Wave30tn

open StatFormal.TrimmedMMD.BangBang StatFormal.Foundations.TrimmedMean StatFormal.Foundations.Bootstrap
open StatFormal.Foundations.CLT
open StatFormal.Wave29i (splitTrimLo splitTrimUp splitAss)
open StatFormal.Wave29l (splitBootRep)

/-- A side is admissible at tolerance `δ`. -/
def SideOK (a : ℕ) (α V : ℝ) (v : Fin a → ℝ) (δ : ℝ) : Prop :=
  (0 < V ∧ |varLo a α v - V| < δ ∧ (a : ℝ) * bAvg (fun I => bootD v α I ^ 2) < δ) ∨
    (V = 0 ∧ ∀ I, bootA v α I = 0 ∧ bootD v α I = 0)

/-- **Uniform bootstrap CLT for arbitrary sizes** (deterministic). -/
theorem boot_std_unif {α B VX VY : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hVX : 0 ≤ VX) (hVY : 0 ≤ VY)
    (hpos : 0 < VX + VY) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ N : ℕ, ∀ a ≥ N, ∀ b ≥ N, ∀ (vx : Fin a → ℝ) (vy : Fin b → ℝ), (∀ i, |vx i| ≤ B) → (∀ j, |vy j| ≤ B) →
      SideOK a α VX vx δ → SideOK b α VY (fun j => -vy j) δ →
      |bAvg (fun p => if stdRoot a b α vx vy (√(VX / a + VY / b) / (1 - α)) p ≤ t then (1 : ℝ) else 0) -
        (gaussianReal 0 1).real (Set.Iic t)| < ε := by
  by_contra hcon
  push Not at hcon
  choose a ha b hb vx vy hbx hby hsx hsy hbad using fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity) (k + 1)
  have hn : Tendsto a atTop atTop := tendsto_atTop_mono (fun k => (Nat.le_succ k).trans (ha k)) tendsto_id
  have hm : Tendsto b atTop atTop := tendsto_atTop_mono (fun k => (Nat.le_succ k).trans (hb k)) tendsto_id
  have ha0 : ∀ k, 0 < a k := fun k => lt_of_lt_of_le (Nat.succ_pos k) (ha k)
  have hb0 : ∀ k, 0 < b k := fun k => lt_of_lt_of_le (Nat.succ_pos k) (hb k)
  have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have conv : ∀ {u : ℕ → ℝ} {L : ℝ}, (∀ k, |u k - L| < 1 / ((k : ℝ) + 1)) → Tendsto u atTop (𝓝 L) :=
    fun {u L} hu => by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun k => norm_nonneg _) (fun k => by rw [Real.norm_eq_abs]; exact (hu k).le) h0
  have conv0 : ∀ {u : ℕ → ℝ}, (∀ k, 0 ≤ u k) → (∀ k, u k < 1 / ((k : ℝ) + 1)) → Tendsto u atTop (𝓝 0) :=
    fun {u} hu0 hu => squeeze_zero hu0 (fun k => (hu k).le) h0
  have side : ∀ {N : ℕ → ℕ} {V : ℝ} {v : (k : ℕ) → Fin (N k) → ℝ}, 0 ≤ V →
      (∀ k, SideOK (N k) α V (v k) (1 / ((k : ℝ) + 1))) → SideSeq N α V v := by
    intro N V v hV hk
    rcases hV.eq_or_lt with h | h
    · refine Or.inr ⟨h.symm, fun k I => ?_⟩
      rcases hk k with h' | h'
      · exact absurd h'.1 (by rw [← h]; exact lt_irrefl 0)
      · exact h'.2 I
    · refine Or.inl ⟨h, conv fun k => ?_, conv0 (fun k => mul_nonneg (Nat.cast_nonneg _) (bAvg_nonneg fun _ => sq_nonneg _))
        fun k => ?_⟩
      · rcases hk k with h' | h'
        · exact h'.2.1
        · exact absurd h'.1 h.ne'
      · rcases hk k with h' | h'
        · exact h'.2.2
        · exact absurd h'.1 h.ne'
  have hseq := boot_std_seq hn hm ha0 hb0 hα0 hα1 hbx hby (side hVX hsx) (side hVY hsy) hpos t
  have := (tendsto_iff_norm_sub_tendsto_zero.1 hseq).eventually (gt_mem_nhds hε)
  obtain ⟨k, hk⟩ := this.exists
  rw [Real.norm_eq_abs] at hk
  exact absurd (hbad k) (not_le.2 hk)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Bootstrap CLT in probability for arbitrary sizes.** -/
theorem tip0_bootStd {n m : ℕ → ℕ} (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    {α B VX VY : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hVX : 0 ≤ VX) (hVY : 0 ≤ VY) (hpos : 0 < VX + VY)
    {vx : (a : ℕ) → Ω → Fin a → ℝ} {vy : (b : ℕ) → Ω → Fin b → ℝ}
    (hbx : ∀ a ω i, |vx a ω i| ≤ B) (hby : ∀ b ω j, |vy b ω j| ≤ B)
    (hX : ∀ δ > 0, Tendsto (fun k => μ {ω | ¬ SideOK (n k) α VX (vx (n k) ω) δ}) atTop (𝓝 0))
    (hY : ∀ δ > 0, Tendsto (fun k => μ {ω | ¬ SideOK (m k) α VY (fun j => -vy (m k) ω j) δ}) atTop (𝓝 0)) (t : ℝ) :
    TIP0 μ (fun k ω => bAvg (fun p => if stdRoot (n k) (m k) α (vx (n k) ω) (vy (m k) ω)
        (√(VX / n k + VY / m k) / (1 - α)) p ≤ t then (1 : ℝ) else 0) - (gaussianReal 0 1).real (Set.Iic t)) := by
  intro ε hε
  obtain ⟨δ, hδ, N, hN⟩ := boot_std_unif (B := B) hα0 hα1 hVX hVY hpos t hε
  have hsum := (hX δ hδ).add (hY δ hδ)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hn.eventually_ge_atTop N, hm.eventually_ge_atTop N] with k hk1 hk2
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra hc
  push Not at hc
  obtain ⟨hc1, hc2⟩ := hc
  have := hN (n k) hk1 (m k) hk2 (vx (n k) ω) (vy (m k) ω) (hbx _ ω) (hby _ ω) hc1 hc2
  linarith

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {P : Measure 𝒳} [IsProbabilityMeasure P] {X : ℕ → Ω → 𝒳}

/-- A non-degenerate side is admissible with probability `→ 1`. -/
lemma side_nondeg {V α : ℝ} (hV : 0 < V) {v : (a : ℕ) → Ω → Fin a → ℝ}
    (h1 : TIP0 μ (fun a ω => varLo a α (v a ω) - V))
    (h2 : TIP0 μ (fun a ω => (a : ℝ) * bAvg (fun I : Fin a → Fin a => bootD (v a ω) α I ^ 2)))
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) :
    ∀ δ > 0, Tendsto (fun k => μ {ω | ¬ SideOK (n k) α V (v (n k) ω) δ}) atTop (𝓝 0) := by
  intro δ hδ
  have hsum := ((h1 δ hδ).comp hn).add ((h2 δ hδ).comp hn)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun k => ?_)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_union, Function.comp] at hω ⊢
  by_contra hc
  push Not at hc
  exact hω (Or.inl ⟨hV, hc.1, lt_of_le_of_lt (le_abs_self _) hc.2⟩)

/-- A degenerate side (almost surely `A* ≡ D* ≡ 0`) is admissible almost surely. -/
lemma side_deg {α : ℝ} {v : (a : ℕ) → Ω → Fin a → ℝ}
    (hae : ∀ᵐ ω ∂μ, ∀ a : ℕ, 0 < a → ∀ I, bootA (v a ω) α I = 0 ∧ bootD (v a ω) α I = 0)
    {n : ℕ → ℕ} (hn0 : ∀ k, 0 < n k) :
    ∀ δ > 0, Tendsto (fun k => μ {ω | ¬ SideOK (n k) α 0 (v (n k) ω) δ}) atTop (𝓝 0) := by
  intro δ _
  refine tendsto_const_nhds.congr fun k => ?_
  symm
  refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hae)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro h
  exact hω (Or.inr ⟨rfl, h (n k) (hn0 k)⟩)

/-- Constant data: `A* ≡ 0`. -/
lemma bootA_const {a : ℕ} {α : ℝ} {v : Fin a → ℝ} (hv : ∀ i j, v i = v j) (I : Fin a → Fin a) : bootA v α I = 0 := by
  unfold bootA
  have : v ∘ I = v := funext fun i => hv (I i) i
  rw [this, sub_self]

/-- `Var_P h = 0` makes the sample almost surely constant. -/
lemma ae_const_sample (hS : IIDSample μ P X) {h : 𝒳 → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B)
    (h0 : Var[h; P] = 0) : ∀ᵐ ω ∂μ, ∀ i, h (X i ω) = P[h] := by
  have hmem : MemLp h 2 P := MemLp.of_bound hm.aestronglyMeasurable B (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]; exact hB x)
  have hev : evariance h P = 0 := by rw [← ofReal_variance hmem, h0, ENNReal.ofReal_zero]
  have hae := (evariance_eq_zero_iff hm.aemeasurable).1 hev
  rw [ae_all_iff]
  intro i
  have hae' : ∀ᵐ x ∂(μ.map (X i)), h x = P[h] := by rw [hS.law i]; exact hae
  exact ae_of_ae_map (hS.meas i).aemeasurable hae'

lemma tendstoInMeasure_of_tip0' {A : ℕ → Ω → ℝ} {c : ℝ} (h : TIP0 μ (fun n ω => A n ω - c)) :
    TendstoInMeasure μ A atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simpa only [Real.norm_eq_abs] using h ε hε

lemma splitBootCdfStd_eq (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) (s t : ℝ) :
    splitBootCdfStd n m α vx vy s t = bAvg (fun p => if stdRoot n m α vx vy s p ≤ t then (1 : ℝ) else 0) := by
  have hc : (Fintype.card ((Fin n → Fin n) × (Fin m → Fin m)) : ℝ) = (n : ℝ) ^ n * (m : ℝ) ^ m := by
    simp [Fintype.card_prod]
  unfold splitBootCdfStd bAvg
  rw [hc, Fintype.sum_prod_type]
  rfl

end StatFormal.Wave30tn

namespace StatFormal.Wave30tn

open StatFormal.TrimmedMMD.BangBang StatFormal.Foundations.TrimmedMean StatFormal.Foundations.Bootstrap
open StatFormal.Foundations.CLT
open StatFormal.Wave29i (splitTrimLo splitTrimUp splitAss)
open StatFormal.Wave30da (splitSdAny)
open StatFormal.Wave30dd (splitSdZero)

theorem split_boot_ass_route : Claims.split_boot_ass := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' α q q' f Ω _ μ _ X Y n m hφ hκ hα0 hα1 hP hQ hXm hYm hXi hYi hXl hYl
    hn1 hm1 hn hm
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  set h : 𝒳 → ℝ := fun x => ⟪f, φ x⟫ with hhdef
  have hhm : Measurable h := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  obtain ⟨ha, hb⟩ := vars_pos_of_ass hhm hB hα0 hP hQ
  have hPu : UQ P h (1 - α) q := AssDens.uq hhm hP
  have hQu : UQ Q h α q' := AssDens.uq hhm hQ
  have hQ' : UQ Q (fun x => -h x) (1 - α) (-q') := by
    have := hQu.neg hhm; simpa only [sub_sub_cancel] using this
  refine ⟨StatFormal.Wave30dd.split_boot_se_any 𝒳 H P Q φ κ' α q q' f Ω μ X Y n m hφ hκ hα0.le hα1 hPu hQu ha hb
    hXm hYm hXi hYi hXl hYl hn1 hm1 hn hm, fun t => ?_⟩
  have hg' : (fun x => max (-q' - -h x) 0) = fun x => max (h x - q') 0 := funext fun x => by ring_nf
  set VX := Var[fun x => max (q - h x) 0; P]
  set VY := Var[fun x => max (h x - q') 0; Q]
  have hBn : ∀ x, |-h x| ≤ ‖f‖ * κ' := fun x => by rw [abs_neg]; exact hB x
  have sX := side_nondeg (v := fun a ω => smp X h a ω) ha (tip0_varLo hX hhm hB hα0.le hα1 hPu)
    (tip0_bootD hX hhm hB hα0.le hα1 hPu) hn
  have sY := side_nondeg (v := fun a ω => smp Y (fun x => -h x) a ω) (V := VY) hb
    (by have := tip0_varLo (h := fun x => -h x) hY hhm.neg hBn hα0.le hα1 hQ'; rwa [hg'] at this)
    (tip0_bootD (h := fun x => -h x) hY hhm.neg hBn hα0.le hα1 hQ') hm
  have key := tip0_bootStd (μ := μ) hn hm hα0.le hα1 ha.le hb.le (by linarith)
    (vx := fun a ω => smp X h a ω) (vy := fun b ω => smp Y h b ω) (fun a ω i => hB _) (fun b ω j => hB _)
    sX sY t
  refine tendstoInMeasure_of_tip0' (key.congr (Eventually.of_forall fun k ω => ?_))
  rw [splitBootCdfStd_eq]
  rfl

theorem split_zero_boot_any_route : Claims.split_zero_boot_any := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ' f Ω _ μ _ X Y n m hφ hκ hXm hYm hXi hYi hXl hYl hn1 hm1 hn hm hσ
  have hX : IIDSample μ P X := ⟨hXm, hXi, hXl⟩
  have hY : IIDSample μ Q Y := ⟨hYm, hYi, hYl⟩
  set h : 𝒳 → ℝ := fun x => ⟪f, φ x⟫ with hhdef
  have hhm : Measurable h := measurable_inner_comp hφ f
  have hB := abs_inner_le hκ f
  refine ⟨StatFormal.Wave30dd.split_zero_boot_se_any 𝒳 H P Q φ κ' f Ω μ X Y n m hφ hκ hXm hYm hXi hYi hXl hYl
    hn1 hm1 hn hm hσ, fun t => ?_⟩
  have hBn : ∀ x, |-h x| ≤ ‖f‖ * κ' := fun x => by rw [abs_neg]; exact hB x
  have hneg : Var[fun x => -h x; Q] = Var[h; Q] := variance_fun_neg
  have hVX := variance_nonneg h P
  have hVY := variance_nonneg h Q
  -- the remainder vanishes at `α = 0`
  have hD0 : ∀ {Z : ℕ → Ω → 𝒳} {g : 𝒳 → ℝ}, TIP0 μ (fun a ω => (a : ℝ) *
      bAvg (fun I : Fin a → Fin a => bootD (smp Z g a ω) 0 I ^ 2)) := by
    intro Z g ε hε
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with a ha
    have : Nonempty (Fin a → Fin a) := ⟨fun i => i⟩
    have e : {ω | ε ≤ |(a : ℝ) * bAvg (fun I : Fin a → Fin a => bootD (smp Z g a ω) 0 I ^ 2)|} = ∅ := by
      ext ω
      simp only [bootD_zero ha, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, bAvg_const, mul_zero,
        abs_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact hε
    rw [e, measure_empty]
  have sX : ∀ δ > 0, Tendsto (fun k => μ {ω | ¬ SideOK (n k) 0 Var[h; P] (smp X h (n k) ω) δ}) atTop (𝓝 0) := by
    rcases hVX.eq_or_lt with h0 | hpos
    · rw [← h0]
      refine side_deg ?_ (fun k => hn1 k)
      filter_upwards [ae_const_sample hX hhm hB h0.symm] with ω hω a ha I
      exact ⟨bootA_const (fun i j => by simp only [smp, hω]) I, bootD_zero ha _ I⟩
    · exact side_nondeg hpos (tip0_varLo_zero hX hhm hB) hD0 hn
  have sY : ∀ δ > 0, Tendsto (fun k => μ {ω | ¬ SideOK (m k) 0 Var[h; Q] (fun j => -smp Y h (m k) ω j) δ}) atTop
      (𝓝 0) := by
    rcases hVY.eq_or_lt with h0 | hpos
    · rw [← h0]
      refine side_deg (v := fun a ω j => -smp Y h a ω j) ?_ (fun k => hm1 k)
      filter_upwards [ae_const_sample hY hhm hB h0.symm] with ω hω a ha I
      exact ⟨bootA_const (fun i j => by simp only [smp, hω]) I, bootD_zero ha _ I⟩
    · refine side_nondeg (v := fun a ω => smp Y (fun x => -h x) a ω) hpos ?_ hD0 hm
      have := tip0_varLo_zero (h := fun x => -h x) hY hhm.neg hBn
      rwa [hneg] at this
  have key := tip0_bootStd (μ := μ) hn hm le_rfl zero_lt_one hVX hVY hσ
    (vx := fun a ω => smp X h a ω) (vy := fun b ω => smp Y h b ω) (fun a ω i => hB _) (fun b ω j => hB _)
    sX sY t
  refine tendstoInMeasure_of_tip0' (key.congr (Eventually.of_forall fun k ω => ?_))
  rw [splitBootCdfStd_eq]
  simp only [splitSdZero, sub_zero, div_one]
  rfl

end StatFormal.Wave30tn
