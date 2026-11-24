import StatFormal.Wave30tw.RouteTails

/-!
# Wave 30tw — route: continuity of the roots, of `τ^{P'}`, its grid form; `→ ∞` (untrusted proof material)

* `root_continuousWithinAt`: `r(x) = inf{t ≥ 0 : F(x,t) ≤ δ}` is continuous at `x₀` (within `S`) if `F(·,t)` is continuous at `x₀` for
  each `t ≥ 0`, `F(x,·)` is nonincreasing on `[0,∞)`, the admissible sets are nonempty on `S`, and `F(x₀,·)` takes values `< δ`
  arbitrarily close to the right of `r(x₀)`.
* That last condition holds for the three-event sums at levels in `(0,1)`, since each tail is strictly decreasing from every point
  where it lies in `(0,1)` (`sum3_strict`).
* `τ^{P'}`, `τ_grid` continuous on `(0,1)`; `t₁ → ∞` as `β → ∞` when the admissible set is nonempty (each `Ψ_H(t;β) → 1` for fixed
  `t`: McDiarmid's term `≥ e^{−2t²/(β²D²s')}`, Pinelis' term `≥ 2e^{−t²/b²}`); bounded otherwise (`t₁ = sInf ∅ = 0`, `t₂ ≤ 3`).
-/

noncomputable section
open MeasureTheory Real Set Filter Topology

namespace StatFormal.Wave30tw

open StatFormal.Wave30ts StatFormal.Wave30tp

/-! ### An abstract root lemma -/

theorem root_continuousWithinAt {X : Type*} [TopologicalSpace X] {S : Set X} {x0 : X} {F : X → ℝ → ℝ} {δ : ℝ}
    (hcont : ∀ t, 0 ≤ t → ContinuousWithinAt (fun x => F x t) S x0)
    (hanti : ∀ x ∈ S, AntitoneOn (F x) (Ici 0))
    (hne : ∀ x ∈ S, {t | 0 ≤ t ∧ F x t ≤ δ}.Nonempty)
    (hflat : ∀ t, sInf {t | 0 ≤ t ∧ F x0 t ≤ δ} < t →
      ∃ t', sInf {t | 0 ≤ t ∧ F x0 t ≤ δ} < t' ∧ t' < t ∧ F x0 t' < δ) :
    ContinuousWithinAt (fun x => sInf {t | 0 ≤ t ∧ F x t ≤ δ}) S x0 := by
  have hr0 : ∀ x, 0 ≤ sInf {t | 0 ≤ t ∧ F x t ≤ δ} := fun x => Real.sInf_nonneg fun t ht => ht.1
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases lt_or_ge a 0 with ha0 | ha0
    · exact Eventually.of_forall fun x => ha0.trans_le (hr0 x)
    set r0 := sInf {t | 0 ≤ t ∧ F x0 t ≤ δ}
    set a' := (a + r0) / 2 with ha'
    have ha'0 : 0 ≤ a' := by rw [ha']; linarith
    have haa' : a < a' := by rw [ha']; linarith
    have ha'r : a' < r0 := by rw [ha']; linarith
    have hF : δ < F x0 a' := by
      by_contra hc
      push Not at hc
      have : r0 ≤ a' := csInf_le (show BddBelow {t | 0 ≤ t ∧ F x0 t ≤ δ} from ⟨0, fun t ht => ht.1⟩) ⟨ha'0, hc⟩
      linarith
    have hev := (hcont a' ha'0).eventually (lt_mem_nhds hF)
    filter_upwards [hev, self_mem_nhdsWithin] with x hx hxS
    have : a' ≤ sInf {t | 0 ≤ t ∧ F x t ≤ δ} := le_csInf (hne x hxS) fun t ht => by
      by_contra hc
      push Not at hc
      have := hanti x hxS (mem_Ici.2 ht.1) (mem_Ici.2 ha'0) hc.le
      linarith [ht.2]
    linarith
  · obtain ⟨t', ht'r, ht'b, hF⟩ := hflat b hb
    have ht'0 : 0 ≤ t' := (hr0 x0).trans ht'r.le
    have hev := (hcont t' ht'0).eventually (gt_mem_nhds hF)
    filter_upwards [hev] with x hx
    exact (csInf_le (show BddBelow {t | 0 ≤ t ∧ F x t ≤ δ} from ⟨0, fun t ht => ht.1⟩) ⟨ht'0, hx.le⟩).trans_lt ht'b

/-- No flat stretch at a level in `(0,1)`: for `F` nonincreasing on `[0,∞)` and strictly decreasing from every `t ≥ 0` with
`0 < F(t) < 1`. -/
theorem flat_free {F : ℝ → ℝ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hanti : AntitoneOn F (Ici 0))
    (hstrict : ∀ t t', 0 ≤ t → t < t' → 0 < F t → F t < 1 → F t' < F t)
    (hne : {t | 0 ≤ t ∧ F t ≤ δ}.Nonempty) :
    ∀ t, sInf {t | 0 ≤ t ∧ F t ≤ δ} < t → ∃ t', sInf {t | 0 ≤ t ∧ F t ≤ δ} < t' ∧ t' < t ∧ F t' < δ := by
  intro t ht
  set r := sInf {t | 0 ≤ t ∧ F t ≤ δ} with hr
  have hr0 : 0 ≤ r := Real.sInf_nonneg fun t ht => ht.1
  set t1 := r + (t - r) / 3 with ht1
  set t2 := r + 2 * (t - r) / 3 with ht2
  have hrt1 : r < t1 := by rw [ht1]; linarith
  have ht12 : t1 < t2 := by rw [ht1, ht2]; linarith
  have ht1_0 : 0 ≤ t1 := by linarith
  obtain ⟨s, hs, hst1⟩ := exists_lt_of_csInf_lt hne hrt1
  have hF1 : F t1 ≤ δ := (hanti (mem_Ici.2 hs.1) (mem_Ici.2 ht1_0) hst1.le).trans hs.2
  refine ⟨t2, by linarith, by rw [ht2]; linarith, ?_⟩
  have h21 : F t2 ≤ F t1 := hanti (mem_Ici.2 ht1_0) (mem_Ici.2 (by linarith)) ht12.le
  rcases lt_or_ge (F t1) δ with h | h
  · exact h21.trans_lt h
  · have heq : F t1 = δ := le_antisymm hF1 h
    have := hstrict t1 t2 ht1_0 ht12 (by rw [heq]; exact hδ0) (by rw [heq]; exact hδ1)
    linarith

theorem sum3_strict {a b c a' b' c' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (haa : a' ≤ a) (hbb : b' ≤ b)
    (hcc : c' ≤ c) (sa : 0 < a → a < 1 → a' < a) (sb : 0 < b → b < 1 → b' < b) (sc : 0 < c → c < 1 → c' < c)
    (h0 : 0 < a + b + c) (h1 : a + b + c < 1) : a' + b' + c' < a + b + c := by
  rcases ha.lt_or_eq with ha' | ha'
  · have := sa ha' (by linarith); linarith
  rcases hb.lt_or_eq with hb' | hb'
  · have := sb hb' (by linarith); linarith
  have hc' : 0 < c := by rw [← ha', ← hb'] at h0; linarith
  have := sc hc' (by linarith)
  linarith

/-! ### The three-event sums -/

theorem psiH3_antitoneOn {D v ρbar β : ℝ} {n m : ℕ} (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hβ : 0 < β) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : AntitoneOn (fun t => psiH3 D v ρbar β t n m) (Ici 0) := by
  intro t ht t' _ htt
  unfold psiH3
  have h1 := psiH_antitone (D := D) hv hρ hβ (sNM_pos hn hm) (cNM_pos (m := m) hn) ht htt
  have h2 := psiH_antitone (D := D) hv hρ hβ (one_div_pos_nat hn) (one_div_pos_nat hn) ht htt
  have h3 := psiH_antitone (D := D) hv hρ hβ (one_div_pos_nat hm) (one_div_pos_nat hm) ht htt
  linarith

theorem psiH3_strict {D v ρbar β : ℝ} {n m : ℕ} (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hβ : 0 < β) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : ∀ t t', 0 ≤ t → t < t' → 0 < psiH3 D v ρbar β t n m → psiH3 D v ρbar β t n m < 1 →
      psiH3 D v ρbar β t' n m < psiH3 D v ρbar β t n m := by
  intro t t' ht htt h0 h1
  unfold psiH3 at *
  exact sum3_strict (psiH_nonneg _ _ _ _ _ _ _) (psiH_nonneg _ _ _ _ _ _ _) (psiH_nonneg _ _ _ _ _ _ _)
    (psiH_antitone hv hρ hβ (sNM_pos hn hm) (cNM_pos (m := m) hn) ht htt.le)
    (psiH_antitone hv hρ hβ (one_div_pos_nat hn) (one_div_pos_nat hn) ht htt.le)
    (psiH_antitone hv hρ hβ (one_div_pos_nat hm) (one_div_pos_nat hm) ht htt.le)
    (fun _ h => psiH_strict hρ hβ (sNM_pos hn hm) (cNM_pos (m := m) hn) ht htt h)
    (fun _ h => psiH_strict hρ hβ (one_div_pos_nat hn) (one_div_pos_nat hn) ht htt h)
    (fun _ h => psiH_strict hρ hβ (one_div_pos_nat hm) (one_div_pos_nat hm) ht htt h) h0 h1

theorem psiR3_strict {β : ℝ} {n m : ℕ} (hβ : 1 ≤ β) : ∀ t t', 0 ≤ t → t < t' → 0 < psiR3 β t n m →
    psiR3 β t n m < 1 → psiR3 β t' n m < psiR3 β t n m := by
  intro t t' _ htt h0 h1
  unfold psiR3 at *
  exact sum3_strict (psiR_nonneg hβ _ _) (psiR_nonneg hβ _ _) (psiR_nonneg hβ _ _)
    (psiR_antitone hβ _ htt.le) (psiR_antitone hβ _ htt.le) (psiR_antitone hβ _ htt.le)
    (fun a b => psiR_strict hβ htt a b) (fun a b => psiR_strict hβ htt a b) (fun a b => psiR_strict hβ htt a b) h0 h1

theorem psiR3_antitoneOn {β : ℝ} {n m : ℕ} (hβ : 1 ≤ β) : AntitoneOn (fun t => psiR3 β t n m) (Ici 0) := by
  intro t _ t' _ htt
  unfold psiR3
  have := psiR_antitone hβ [n] htt
  have := psiR_antitone hβ [m] htt
  have := psiR_antitone hβ [n, m] htt
  simp only at *
  linarith

theorem psiH3_continuousAt_beta {D v ρbar t β0 : ℝ} {n m : ℕ} (hρ : 0 ≤ ρbar) (ht : 0 ≤ t) (hβ0 : 0 < β0)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : ContinuousAt (fun β => psiH3 D v ρbar β t n m) β0 := by
  unfold psiH3
  exact ((psiH_continuousAt_const continuousAt_id continuousAt_const hβ0 ht hρ (sNM_pos hn hm)
    (cNM_pos (m := m) hn)).add (psiH_continuousAt_const continuousAt_id continuousAt_const hβ0 ht hρ
      (one_div_pos_nat hn) (one_div_pos_nat hn))).add
    (psiH_continuousAt_const continuousAt_id continuousAt_const hβ0 ht hρ (one_div_pos_nat hm) (one_div_pos_nat hm))

theorem psiR3_continuousAt {t β0 : ℝ} {n m : ℕ} (hβ0 : 1 < β0) : ContinuousAt (fun β => psiR3 β t n m) β0 := by
  unfold psiR3
  exact ((psiR_continuousAt t [n] hβ0).add (psiR_continuousAt t [m] hβ0)).add (psiR_continuousAt t [n, m] hβ0)

/-! ### The roots -/

theorem rootH_continuousOn {D v ρbar δ1 : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hρ : 0 ≤ ρbar)
    (hδ0 : 0 < δ1) (hδ1 : δ1 < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ContinuousOn (fun β => rootH D v ρbar β δ1 n m) (Ioi 1) := by
  by_cases hcase : 0 < D ∨ (0 < v ∧ 0 < ρbar)
  · intro β0 hβ0
    have hβ0' : (1 : ℝ) < β0 := hβ0
    exact root_continuousWithinAt (F := fun β t => psiH3 D v ρbar β t n m)
      (fun t ht => (psiH3_continuousAt_beta hρ ht (by linarith) hn hm).continuousWithinAt)
      (fun β hβ => psiH3_antitoneOn hv hρ (by linarith [show (1 : ℝ) < β from hβ]) hn hm)
      (fun β hβ => setH_nonempty hv hρ (le_of_lt hβ) hδ0 hn hm hcase)
      (flat_free hδ0 hδ1 (psiH3_antitoneOn hv hρ (by linarith) hn hm) (psiH3_strict hv hρ (by linarith) hn hm)
        (setH_nonempty hv hρ hβ0'.le hδ0 hn hm hcase))
  · push Not at hcase
    have hD0 : D = 0 := le_antisymm hcase.1 hD
    have hj : v = 0 ∨ ρbar = 0 := by
      rcases hv.lt_or_eq with h | h
      · right; exact le_antisymm (hcase.2 h) hρ
      · left; exact h.symm
    have h0 : ∀ β ∈ Ioi (1 : ℝ), rootH D v ρbar β δ1 n m = 0 := fun β hβ => by
      rw [rootH_eq, hD0, setH_empty hρ (by linarith [show (1 : ℝ) < β from hβ]) (by linarith) hn hm hj,
        Real.sInf_empty]
    exact continuousOn_const.congr h0

theorem rootR_continuousOn {δ2 : ℝ} {n m : ℕ} (hδ0 : 0 < δ2) (hδ1 : δ2 < 1) :
    ContinuousOn (fun β => rootR β δ2 n m) (Ioi 1) := by
  intro β0 hβ0
  have hβ0' : (1 : ℝ) < β0 := hβ0
  exact root_continuousWithinAt (F := fun β t => psiR3 β t n m)
    (fun _ _ => (psiR3_continuousAt hβ0').continuousWithinAt)
    (fun β hβ => psiR3_antitoneOn (le_of_lt hβ))
    (fun β hβ => ⟨3, three_mem_setR (le_of_lt hβ) hδ0.le n m⟩)
    (flat_free hδ0 hδ1 (psiR3_antitoneOn hβ0'.le) (psiR3_strict hβ0'.le) ⟨3, three_mem_setR hβ0'.le hδ0.le n m⟩)

theorem sharp_roots_continuous : Claims.sharp_roots_continuous :=
  ⟨fun _ _ _ _ _ _ hD hv hρ hδ0 hδ1 hn hm => rootH_continuousOn hD hv hρ hδ0 hδ1 hn hm,
    fun _ _ _ hδ0 hδ1 => rootR_continuousOn hδ0 hδ1⟩

/-! ### `τ^{P'}` -/

theorem beta_mapsTo : MapsTo (fun α : ℝ => 1 / (1 - α)) (Ioo 0 1) (Ioi 1) := fun α hα => by
  have h1 : 0 < 1 - α := by linarith [hα.2]
  show 1 < 1 / (1 - α)
  rw [lt_div_iff₀ h1]
  linarith [hα.1]

theorem one_lt_beta {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) : 1 < 1 / (1 - α) := beta_mapsTo hα

theorem IsSplit.levels {f δ : ℝ} (hf : IsSplit f) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < f * δ ∧ f * δ < 1 ∧ 0 < (1 - f) * δ ∧ (1 - f) * δ < 1 := by
  obtain ⟨h0, h1⟩ := IsSplit.bounds hf
  refine ⟨mul_pos h0 hδ0, ?_, mul_pos (by linarith) hδ0, ?_⟩ <;> nlinarith

theorem tauSplit_continuousOn {D v ρbar δ f : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hρ : 0 ≤ ρbar)
    (hf : IsSplit f) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ContinuousOn (fun α => tauSplit D v ρbar α δ f n m) (Ioo 0 1) := by
  obtain ⟨l1, l2, l3, l4⟩ := IsSplit.levels hf hδ0 hδ1
  have hbc := StatFormal.Wave30tu.Instance.one_div_one_sub_continuousOn
  unfold tauSplit
  exact ((rootH_continuousOn hD hv hρ l1 l2 hn hm).comp hbc beta_mapsTo).add
    (continuousOn_const.mul ((rootR_continuousOn l3 l4).comp hbc beta_mapsTo))

theorem isSplit_half : IsSplit (1 / 2) := Or.inl rfl
theorem isSplit_35 : IsSplit (3 / 5) := Or.inr (Or.inl rfl)
theorem isSplit_710 : IsSplit (7 / 10) := Or.inr (Or.inr (Or.inl rfl))
theorem isSplit_45 : IsSplit (4 / 5) := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
theorem isSplit_910 : IsSplit (9 / 10) := Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem tauPs_continuousOn {D v ρbar δ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) : ContinuousOn (fun α => tauPs D v ρbar α δ n m) (Ioo 0 1) := by
  refine ContinuousOn.congr ?_ (fun α hα => tauPs_pos_eq (D := D) (v := v) (ρbar := ρbar) (δ := δ) (n := n) (m := m)
    hα.1.ne')
  exact (tauSplit_continuousOn hD hv hρ isSplit_half hδ0 hδ1 hn hm).inf
    ((tauSplit_continuousOn hD hv hρ isSplit_35 hδ0 hδ1 hn hm).inf
      ((tauSplit_continuousOn hD hv hρ isSplit_710 hδ0 hδ1 hn hm).inf
        ((tauSplit_continuousOn hD hv hρ isSplit_45 hδ0 hδ1 hn hm).inf
          (tauSplit_continuousOn hD hv hρ isSplit_910 hδ0 hδ1 hn hm))))

theorem sharp_tau_continuous : Claims.sharp_tau_continuous :=
  fun _ _ _ _ _ _ hD hv hρ hδ0 hδ1 hn hm => tauPs_continuousOn hD hv hρ hδ0 hδ1 hn hm

/-! ### `→ ∞` -/

theorem psiPin_ge {a b2 t : ℝ} (ha : 0 < a) (hb : 0 < b2) (ht : 0 ≤ t) : 2 * exp (-(t ^ 2 / b2)) ≤ psiPin a b2 t := by
  unfold psiPin
  have hx : 0 ≤ t * a / b2 := by positivity
  have hlog : log (1 + t * a / b2) ≤ t * a / b2 := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + t * a / b2)
    linarith
  have hc : 0 ≤ t / a + b2 / a ^ 2 := by positivity
  have h := mul_le_mul_of_nonneg_left hlog hc
  have e : (t / a + b2 / a ^ 2) * (t * a / b2) = t ^ 2 / b2 + t / a := by field_simp
  have : -(t ^ 2 / b2) ≤ t / a - (t / a + b2 / a ^ 2) * log (1 + t * a / b2) := by linarith
  have := exp_le_exp.2 this
  linarith

theorem eventually_psiH_gt {D v ρbar s' c' T δ1 : ℝ} (hρ : 0 ≤ ρbar) (hs : 0 < s') (hc : 0 < c') (hT : 0 ≤ T)
    (hδ : δ1 < 1) : ∀ᶠ β in atTop, δ1 < psiH D v ρbar β s' c' T := by
  have hM : ∀ᶠ β in atTop, δ1 < psiMcD D v β s' T := by
    have hlim : Tendsto (fun β : ℝ => exp (-2 * T ^ 2 / (β ^ 2 * D ^ 2 * s'))) atTop (𝓝 1) := by
      by_cases hD : D = 0
      · subst hD; simp
      · have hD2 : 0 < D ^ 2 * s' := by positivity
        have h1 : Tendsto (fun β : ℝ => β ^ 2 * D ^ 2 * s') atTop atTop := by
          have := (tendsto_pow_atTop (two_ne_zero (α := ℕ))).atTop_mul_const hD2
          refine this.congr fun β => ?_
          ring
        have h2 : Tendsto (fun β : ℝ => -2 * T ^ 2 / (β ^ 2 * D ^ 2 * s')) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop h1
        have h3 := (Real.continuous_exp.tendsto 0).comp h2
        rw [Real.exp_zero] at h3
        exact h3
    filter_upwards [hlim.eventually (lt_mem_nhds hδ)] with β hβ
    refine hβ.trans_le ?_
    unfold psiMcD
    apply exp_le_exp.2
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hm0 : 0 ≤ max (T - √(β * v ^ 2 * s')) 0 := le_max_right _ _
    have hmT : max (T - √(β * v ^ 2 * s')) 0 ≤ T := max_le (by linarith [Real.sqrt_nonneg (β * v ^ 2 * s')]) hT
    nlinarith
  have hP : ∀ᶠ β in atTop, δ1 < psiPin (β * ρbar * c') (β * v ^ 2 * s') T := by
    rcases hρ.eq_or_lt with hρ0 | hρ0
    · subst hρ0
      simp only [mul_zero, zero_mul, psiPin_zero_a]
      exact Eventually.of_forall fun _ => by linarith
    by_cases hv : v = 0
    · subst hv
      filter_upwards [eventually_gt_atTop 0] with β hβ
      have := one_le_psiPin_of_junk (b2 := β * (0 : ℝ) ^ 2 * s') (mul_pos (mul_pos hβ hρ0) hc).le hT
        (Or.inr (by ring))
      linarith
    · have hv2 : 0 < v ^ 2 * s' := by positivity
      have h1 : Tendsto (fun β : ℝ => β * v ^ 2 * s') atTop atTop := by
        refine (tendsto_id.atTop_mul_const hv2).congr fun β => ?_
        simp; ring
      have h2 : Tendsto (fun β : ℝ => 2 * exp (-(T ^ 2 / (β * v ^ 2 * s')))) atTop (𝓝 2) := by
        have h3 : Tendsto (fun β : ℝ => T ^ 2 / (β * v ^ 2 * s')) atTop (𝓝 0) := tendsto_const_nhds.div_atTop h1
        have h4 : Tendsto (fun β : ℝ => -(T ^ 2 / (β * v ^ 2 * s'))) atTop (𝓝 0) := by simpa using h3.neg
        have h5 := ((Real.continuous_exp.tendsto 0).comp h4).const_mul 2
        rw [Real.exp_zero, mul_one] at h5
        exact h5
      filter_upwards [h2.eventually (lt_mem_nhds (by linarith : δ1 < 2)), eventually_gt_atTop 0] with β h4 h5
      exact h4.trans_le (psiPin_ge (mul_pos (mul_pos h5 hρ0) hc) (mul_pos h5 hv2 |>.trans_eq (by ring)) hT)
  filter_upwards [hM, hP] with β h1 h2
  exact lt_min h1 h2

theorem rootH_tendsto {D v ρbar δ1 : ℝ} {n m : ℕ} (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hδ0 : 0 < δ1) (hδ1 : δ1 < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (h : 0 < D ∨ (0 < v ∧ 0 < ρbar)) :
    Tendsto (fun β => rootH D v ρbar β δ1 n m) atTop atTop := by
  refine tendsto_atTop.2 fun T => ?_
  filter_upwards [eventually_psiH_gt (D := D) (v := v) (s' := sNM n m) (c' := cNM n m) (T := max T 0) hρ
    (sNM_pos hn hm) (cNM_pos (m := m) hn) (le_max_right _ _) hδ1, eventually_ge_atTop 1] with β hβ hβ1
  refine (le_max_left T 0).trans (le_csInf (setH_nonempty hv hρ hβ1 hδ0 hn hm h) fun t ht => ?_)
  by_contra hc
  push Not at hc
  have h1 := psiH_antitone (D := D) (β := β) hv hρ (by linarith) (sNM_pos hn hm) (cNM_pos (m := m) hn) ht.1 hc.le
  have h2 : psiH D v ρbar β (sNM n m) (cNM n m) t ≤ psiH3 D v ρbar β t n m := by
    have e1 := psiH_nonneg D v ρbar β (1 / (n : ℝ)) (1 / (n : ℝ)) t
    have e2 := psiH_nonneg D v ρbar β (1 / (m : ℝ)) (1 / (m : ℝ)) t
    unfold psiH3
    linarith
  have h3 : psiH3 D v ρbar β t n m ≤ δ1 := ht.2
  linarith

theorem not_tendsto_of_le {f : ℝ → ℝ} {C : ℝ} (h : ∀ α ∈ Ioo (0 : ℝ) 1, f α ≤ C) :
    ¬ Tendsto f (𝓝[<] 1) atTop := by
  intro ht
  have h1 := ht.eventually (eventually_gt_atTop C)
  have h2 : ∀ᶠ α in 𝓝[<] (1 : ℝ), α ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
  obtain ⟨α, hα1, hα2⟩ := (h1.and h2).exists
  linarith [h α hα2]

theorem tendsto_min_atTop {f g : ℝ → ℝ} {l : Filter ℝ} (hf : Tendsto f l atTop) (hg : Tendsto g l atTop) :
    Tendsto (fun x => min (f x) (g x)) l atTop :=
  tendsto_atTop.2 fun b => by
    filter_upwards [tendsto_atTop.1 hf b, tendsto_atTop.1 hg b] with x h1 h2
    exact le_min h1 h2

theorem rootR_le_three {β δ2 : ℝ} {n m : ℕ} (hβ : 1 ≤ β) (hδ : 0 ≤ δ2) : rootR β δ2 n m ≤ 3 :=
  csInf_le ⟨0, fun t ht => ht.1⟩ (three_mem_setR hβ hδ n m)

theorem tauPs_le_degenerate {v ρbar α δ : ℝ} {n m : ℕ} (hρ : 0 ≤ ρbar) (hj : v = 0 ∨ ρbar = 0)
    (hα : α ∈ Ioo (0 : ℝ) 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    tauPs 0 v ρbar α δ n m ≤ 3 * ρbar := by
  have hβ := one_lt_beta hα
  refine (tauPs_pos_le hα.1.ne' isSplit_half).trans ?_
  unfold tauSplit
  rw [rootH_eq, setH_empty hρ (by linarith) (by nlinarith) hn hm hj, Real.sInf_empty, zero_add]
  have := rootR_le_three (n := n) (m := m) hβ.le (by nlinarith : 0 ≤ (1 - 1 / 2) * δ)
  nlinarith

theorem tauPs_tendsto_iff {D v ρbar δ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Tendsto (fun α => tauPs D v ρbar α δ n m) (𝓝[<] 1) atTop ↔ (0 < D ∨ (0 < v ∧ 0 < ρbar)) := by
  constructor
  · intro ht
    by_contra hcase
    push Not at hcase
    have hD0 : D = 0 := le_antisymm hcase.1 hD
    have hj : v = 0 ∨ ρbar = 0 := by
      rcases hv.lt_or_eq with h | h
      · right; exact le_antisymm (hcase.2 h) hρ
      · left; exact h.symm
    subst hD0
    exact not_tendsto_of_le (fun α hα => tauPs_le_degenerate hρ hj hα hδ0 hδ1 hn hm) ht
  · intro hcase
    have hb := StatFormal.Wave30tu.Instance.tendsto_one_div_one_sub
    have hr : ∀ f, IsSplit f → Tendsto (fun α : ℝ => rootH D v ρbar (1 / (1 - α)) (f * δ) n m) (𝓝[<] 1) atTop :=
      fun f hf => by
        obtain ⟨l1, l2, -, -⟩ := IsSplit.levels hf hδ0 hδ1
        exact (rootH_tendsto hv hρ l1 l2 hn hm hcase).comp hb
    refine tendsto_atTop.2 fun T => ?_
    filter_upwards [tendsto_atTop.1 (hr _ isSplit_half) T, tendsto_atTop.1 (hr _ isSplit_35) T,
      tendsto_atTop.1 (hr _ isSplit_710) T, tendsto_atTop.1 (hr _ isSplit_45) T,
      tendsto_atTop.1 (hr _ isSplit_910) T, Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with α h1 h2 h3 h4 h5 hα
    refine le_tauPs_pos hα.1.ne' fun f hf => ?_
    have hle : ∀ g, rootH D v ρbar (1 / (1 - α)) (g * δ) n m ≤ tauSplit D v ρbar α δ g n m := fun g => by
      unfold tauSplit
      have := rootR_nonneg (1 / (1 - α)) ((1 - g) * δ) n m
      nlinarith
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · exact h1.trans (hle _)
    · exact h2.trans (hle _)
    · exact h3.trans (hle _)
    · exact h4.trans (hle _)
    · exact h5.trans (hle _)

theorem sharp_tau_tendsto : Claims.sharp_tau_tendsto :=
  fun _ _ _ _ _ _ hD hv hρ hδ0 hδ1 hn hm => tauPs_tendsto_iff hD hv hρ hδ0 hδ1 hn hm

/-! ### The grid form -/

theorem foldr_max_continuousOn {ι : Type*} (L : List ι) (g : ι → ℝ → ℝ) {s : Set ℝ}
    (h : ∀ i ∈ L, ContinuousOn (g i) s) : ContinuousOn (fun α => (L.map fun i => g i α).foldr max 0) s := by
  induction L with
  | nil => simpa using continuousOn_const
  | cons i L ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact (h i (by simp)).sup (ih fun j hj => h j (by simp [hj]))

theorem tauGrid_continuousOn {D : ℝ} {J : ℕ} {v ρ : ℕ → ℝ} {δ : ℝ} {n m : ℕ} (hD : 0 ≤ D)
    (hvρ : ∀ j < J, 0 ≤ v j ∧ 0 ≤ ρ j) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ContinuousOn (fun α => tauGrid D v ρ J α δ n m) (Ioo 0 1) := by
  unfold tauGrid
  refine foldr_max_continuousOn (List.range J) (fun j α => tauPs D (v j) (ρ j) α δ n m) fun j hj => ?_
  have hj' := List.mem_range.1 hj
  exact tauPs_continuousOn hD (hvρ j hj').1 (hvρ j hj').2 hδ0 hδ1 hn hm

theorem tauGrid_tendsto_iff {D : ℝ} {J : ℕ} {v ρ : ℕ → ℝ} {δ : ℝ} {n m : ℕ} (hD : 0 ≤ D)
    (hvρ : ∀ j < J, 0 ≤ v j ∧ 0 ≤ ρ j) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Tendsto (fun α => tauGrid D v ρ J α δ n m) (𝓝[<] 1) atTop ↔ ∃ j < J, 0 < D ∨ (0 < v j ∧ 0 < ρ j) := by
  constructor
  · intro ht
    by_contra hcase
    push Not at hcase
    have hC : 0 ≤ 3 * ∑ j ∈ Finset.range J, ρ j :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun j hj => (hvρ j (Finset.mem_range.1 hj)).2)
    refine not_tendsto_of_le (C := 3 * ∑ j ∈ Finset.range J, ρ j) (fun α hα => tauGrid_le hC fun j hj => ?_) ht
    obtain ⟨hD', hvj⟩ := hcase j hj
    have hD0 : D = 0 := le_antisymm hD' hD
    have hj0 : v j = 0 ∨ ρ j = 0 := by
      rcases (hvρ j hj).1.lt_or_eq with h | h
      · right; exact le_antisymm (hvj h) (hvρ j hj).2
      · left; exact h.symm
    subst hD0
    refine (tauPs_le_degenerate (hvρ j hj).2 hj0 hα hδ0 hδ1 hn hm).trans ?_
    have := Finset.single_le_sum (fun i hi => (hvρ i (Finset.mem_range.1 hi)).2) (Finset.mem_range.2 hj)
    linarith
  · rintro ⟨j, hj, hcase⟩
    exact tendsto_atTop_mono (fun α => le_tauGrid hj α δ n m)
      ((tauPs_tendsto_iff hD (hvρ j hj).1 (hvρ j hj).2 hδ0 hδ1 hn hm).2 hcase)

theorem grid_tau_continuous : Claims.grid_tau_continuous :=
  fun _ _ _ _ _ _ _ hD hvρ hδ0 hδ1 hn hm =>
    ⟨tauGrid_continuousOn hD hvρ hδ0 hδ1 hn hm, tauGrid_tendsto_iff hD hvρ hδ0 hδ1 hn hm⟩

end StatFormal.Wave30tw
