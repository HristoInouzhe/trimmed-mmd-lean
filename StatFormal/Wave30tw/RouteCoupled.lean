import StatFormal.Wave30tw.RouteRoots

/-!
# Wave 30tw — route: continuity of the coupled supremum `τ^{cpl}_{P'}` (untrusted proof material)

`G(α,u) = τ^{P'}(α; √(κ²−u), √(κ²+u))`.
* `G` is jointly continuous on `(0,1) × (−κ², κ²)` (the abstract root lemma on `ℝ × ℝ`, `v, ρ̄ > 0` there).
* Lower semicontinuity of `sup_u G(·,u)`: from continuity of each `G(·,u)`.
* Upper semicontinuity: compactness of `[0,κ²]` (`IsCompact.eventually_forall_of_forall_eventually`). At `u₀ < κ²` by joint
  continuity; at `u₀ = κ²`: `t₁ → 0` as `v = √(κ²−u) → 0` (Pinelis' term `→ 0` when `b² → 0`), uniformly for `β ≤ β̄`, `ρ̄ ≤ √(2κ²)` by
  monotonicity, so `G ≤ η + √(2κ²) t₂(β, (1−f*)δ) + η`, and `√(2κ²) min_f t₂ ≤ sup_u G` (limit `u ↑ κ²` of `ρ̄_u min_f t₂ ≤ G`).
-/

noncomputable section
open MeasureTheory Real Set Filter Topology

namespace StatFormal.Wave30tw

open StatFormal.Wave30ts StatFormal.Wave30tp

/-! ### `t₁ → 0` as `v → 0` -/

theorem psiPin_small_b {a t ε : ℝ} (ha : 0 < a) (ht : 0 < t) (hε : 0 < ε) :
    ∃ w, 0 < w ∧ ∀ b2, 0 < b2 → b2 ≤ w → psiPin a b2 t ≤ ε := by
  set Λ := 1 - a / t * log (ε / 2) with hΛ
  refine ⟨t * a / exp Λ, by positivity, fun b2 hb hbw => ?_⟩
  have h1 : exp Λ ≤ t * a / b2 := by
    rw [le_div_iff₀ hb]
    rw [le_div_iff₀ (exp_pos Λ)] at hbw
    linarith
  have hL : Λ ≤ log (1 + t * a / b2) := by
    rw [← Real.log_exp Λ]
    exact Real.log_le_log (exp_pos _) (by linarith)
  have hL0 : 0 ≤ log (1 + t * a / b2) := Real.log_nonneg (by linarith [show 0 ≤ t * a / b2 by positivity])
  unfold psiPin
  have hexp : t / a - (t / a + b2 / a ^ 2) * log (1 + t * a / b2) ≤ log (ε / 2) := by
    have e1 : 0 ≤ b2 / a ^ 2 * log (1 + t * a / b2) := mul_nonneg (by positivity) hL0
    have e2 : t / a * Λ ≤ t / a * log (1 + t * a / b2) := mul_le_mul_of_nonneg_left hL (by positivity)
    have e3 : t / a - t / a * Λ = log (ε / 2) := by rw [hΛ]; field_simp; ring
    nlinarith
  calc 2 * exp (t / a - (t / a + b2 / a ^ 2) * log (1 + t * a / b2)) ≤ 2 * exp (log (ε / 2)) := by
        gcongr
    _ = ε := by rw [exp_log (by positivity)]; ring

theorem psiH_small_v {D ρbar β s' c' t ε : ℝ} (hρ : 0 < ρbar) (hβ : 0 < β) (hs : 0 < s') (hc : 0 < c') (ht : 0 < t)
    (hε : 0 < ε) : ∃ w, 0 < w ∧ ∀ v, 0 < v → v < w → psiH D v ρbar β s' c' t ≤ ε := by
  obtain ⟨w, hw, hP⟩ := psiPin_small_b (mul_pos (mul_pos hβ hρ) hc) ht hε
  refine ⟨√(w / (β * s')), Real.sqrt_pos.2 (by positivity), fun v hv hvw => ?_⟩
  have hv2 : v ^ 2 < w / (β * s') := by
    have := (Real.lt_sqrt hv.le).1 hvw
    exact this
  have hb : β * v ^ 2 * s' ≤ w := by
    rw [lt_div_iff₀ (by positivity)] at hv2
    nlinarith
  exact (psiH_le_Pin _ _ _ _ _ _ _).trans (hP _ (by positivity) hb)

theorem rootH_small_v {D ρbar β δ1 η : ℝ} {n m : ℕ} (hρ : 0 < ρbar) (hβ : 0 < β) (hδ : 0 < δ1) (hη : 0 < η)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : ∃ w, 0 < w ∧ ∀ v, 0 < v → v < w → rootH D v ρbar β δ1 n m ≤ η := by
  have hε : 0 < δ1 / 3 := by positivity
  obtain ⟨w1, hw1, h1⟩ := psiH_small_v (D := D) (s' := sNM n m) (c' := cNM n m) hρ hβ (sNM_pos hn hm)
    (cNM_pos (m := m) hn) hη hε
  obtain ⟨w2, hw2, h2⟩ := psiH_small_v (D := D) (s' := 1 / (n : ℝ)) (c' := 1 / (n : ℝ)) hρ hβ (one_div_pos_nat hn)
    (one_div_pos_nat hn) hη hε
  obtain ⟨w3, hw3, h3⟩ := psiH_small_v (D := D) (s' := 1 / (m : ℝ)) (c' := 1 / (m : ℝ)) hρ hβ (one_div_pos_nat hm)
    (one_div_pos_nat hm) hη hε
  refine ⟨min w1 (min w2 w3), lt_min hw1 (lt_min hw2 hw3), fun v hv hvw => ?_⟩
  have hmem : η ∈ setH D v ρbar β δ1 n m := by
    refine ⟨hη.le, ?_⟩
    unfold psiH3
    have := h1 v hv (hvw.trans_le (min_le_left _ _))
    have := h2 v hv (hvw.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    have := h3 v hv (hvw.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  exact csInf_le ⟨0, fun t ht => ht.1⟩ hmem

/-! ### Joint continuity of `G` -/

/-- `G(α,u) = τ^{P'}(α,δ; √(κ²−u), √(κ²+u))`. -/
def Gc (D κ δ : ℝ) (n m : ℕ) (p : ℝ × ℝ) : ℝ := tauPs D (√(κ ^ 2 - p.2)) (√(κ ^ 2 + p.2)) p.1 δ n m

theorem rootH_joint_continuousAt {D κ δ1 : ℝ} {n m : ℕ} {p0 : ℝ × ℝ} (hD : 0 ≤ D) (hδ0 : 0 < δ1) (hδ1 : δ1 < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hp0 : p0 ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-κ ^ 2) (κ ^ 2)) :
    ContinuousAt (fun p : ℝ × ℝ => rootH D (√(κ ^ 2 - p.2)) (√(κ ^ 2 + p.2)) (1 / (1 - p.1)) δ1 n m) p0 := by
  set O := Ioo (0 : ℝ) 1 ×ˢ Ioo (-κ ^ 2) (κ ^ 2) with hO
  have hOo : IsOpen O := isOpen_Ioo.prod isOpen_Ioo
  have hV : ∀ p ∈ O, 0 < √(κ ^ 2 - p.2) := fun p hp => Real.sqrt_pos.2 (by linarith [hp.2.2])
  have hR : ∀ p ∈ O, 0 < √(κ ^ 2 + p.2) := fun p hp => Real.sqrt_pos.2 (by linarith [hp.2.1])
  have hB : ∀ p ∈ O, 1 < 1 / (1 - p.1) := fun p hp => one_lt_beta hp.1
  have hBc : ContinuousAt (fun p : ℝ × ℝ => 1 / (1 - p.1)) p0 :=
    continuousAt_const.div (continuousAt_const.sub continuousAt_fst) (by linarith [hp0.1.2])
  have hVc : ContinuousAt (fun p : ℝ × ℝ => √(κ ^ 2 - p.2)) p0 := (continuousAt_const.sub continuousAt_snd).sqrt
  have hRc : ContinuousAt (fun p : ℝ × ℝ => √(κ ^ 2 + p.2)) p0 := (continuousAt_const.add continuousAt_snd).sqrt
  have hB0 : 0 < 1 / (1 - p0.1) := by linarith [hB p0 hp0]
  have hcw := root_continuousWithinAt (S := O) (x0 := p0) (δ := δ1)
    (F := fun p t => psiH3 D (√(κ ^ 2 - p.2)) (√(κ ^ 2 + p.2)) (1 / (1 - p.1)) t n m)
    (fun t ht => by
      unfold psiH3
      exact (((psiH_continuousAt_pos hBc hVc hRc continuousAt_const hB0 (hV p0 hp0).ne' (hR p0 hp0) ht
        (sNM_pos hn hm) (cNM_pos (m := m) hn)).add (psiH_continuousAt_pos hBc hVc hRc continuousAt_const hB0
          (hV p0 hp0).ne' (hR p0 hp0) ht (one_div_pos_nat hn) (one_div_pos_nat hn))).add
        (psiH_continuousAt_pos hBc hVc hRc continuousAt_const hB0 (hV p0 hp0).ne' (hR p0 hp0) ht (one_div_pos_nat hm)
          (one_div_pos_nat hm))).continuousWithinAt)
    (fun p hp => psiH3_antitoneOn (hV p hp).le (hR p hp).le (by linarith [hB p hp]) hn hm)
    (fun p hp => setH_nonempty (hV p hp).le (hR p hp).le (hB p hp).le hδ0 hn hm (Or.inr ⟨hV p hp, hR p hp⟩))
    (flat_free hδ0 hδ1 (psiH3_antitoneOn (hV p0 hp0).le (hR p0 hp0).le hB0 hn hm)
      (psiH3_strict (hV p0 hp0).le (hR p0 hp0).le hB0 hn hm)
      (setH_nonempty (hV p0 hp0).le (hR p0 hp0).le (hB p0 hp0).le hδ0 hn hm (Or.inr ⟨hV p0 hp0, hR p0 hp0⟩)))
  exact hcw.continuousAt (hOo.mem_nhds hp0)

theorem Gc_continuousAt {D κ δ : ℝ} {n m : ℕ} {p0 : ℝ × ℝ} (hD : 0 ≤ D) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hp0 : p0 ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-κ ^ 2) (κ ^ 2)) :
    ContinuousAt (Gc D κ δ n m) p0 := by
  have hBc : ContinuousAt (fun p : ℝ × ℝ => 1 / (1 - p.1)) p0 :=
    continuousAt_const.div (continuousAt_const.sub continuousAt_fst) (by linarith [hp0.1.2])
  have hRc : ContinuousAt (fun p : ℝ × ℝ => √(κ ^ 2 + p.2)) p0 := (continuousAt_const.add continuousAt_snd).sqrt
  have hsplit : ∀ f, IsSplit f → ContinuousAt (fun p : ℝ × ℝ =>
      tauSplit D (√(κ ^ 2 - p.2)) (√(κ ^ 2 + p.2)) p.1 δ f n m) p0 := fun f hf => by
    obtain ⟨l1, l2, l3, l4⟩ := IsSplit.levels hf hδ0 hδ1
    unfold tauSplit
    have hRR : ContinuousAt (fun p : ℝ × ℝ => rootR (1 / (1 - p.1)) ((1 - f) * δ) n m) p0 := by
      have h1 : ContinuousAt (fun β => rootR β ((1 - f) * δ) n m) (1 / (1 - p0.1)) :=
        (rootR_continuousOn l3 l4).continuousAt (Ioi_mem_nhds (one_lt_beta hp0.1))
      exact h1.comp (f := fun p : ℝ × ℝ => 1 / (1 - p.1)) hBc
    exact (rootH_joint_continuousAt hD l1 l2 hn hm hp0).add (hRc.mul hRR)
  have hmin : ContinuousAt (fun p : ℝ × ℝ =>
      min (tauSplit D (√(κ ^ 2 - p.2)) (√(κ ^ 2 + p.2)) p.1 δ (1 / 2) n m)
        (min (tauSplit D (√(κ ^ 2 - p.2)) (√(κ ^ 2 + p.2)) p.1 δ (3 / 5) n m)
          (min (tauSplit D (√(κ ^ 2 - p.2)) (√(κ ^ 2 + p.2)) p.1 δ (7 / 10) n m)
            (min (tauSplit D (√(κ ^ 2 - p.2)) (√(κ ^ 2 + p.2)) p.1 δ (4 / 5) n m)
              (tauSplit D (√(κ ^ 2 - p.2)) (√(κ ^ 2 + p.2)) p.1 δ (9 / 10) n m))))) p0 :=
    (hsplit _ isSplit_half).min ((hsplit _ isSplit_35).min ((hsplit _ isSplit_710).min
    ((hsplit _ isSplit_45).min (hsplit _ isSplit_910))))
  refine ContinuousAt.congr_of_eventuallyEq hmin ?_
  have hne : ∀ᶠ p : ℝ × ℝ in 𝓝 p0, p.1 ≠ 0 :=
    (continuousAt_fst.eventually (isOpen_ne.mem_nhds hp0.1.1.ne')).mono fun p hp => hp
  filter_upwards [hne] with p hp
  unfold Gc
  rw [tauPs_pos_eq hp]

/-! ### The coupled supremum -/

theorem tauCpl_continuousOn {D κ δ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : ContinuousOn (fun α => tauCpl D κ α δ n m) (Ioo 0 1) := by
  by_cases hκ : κ = 0
  · subst hκ
    have h0 : ∀ α ∈ Ioo (0 : ℝ) 1, tauCpl D 0 α δ n m = 0 := fun α _ => by
      unfold tauCpl
      have : IsEmpty (Ico (0 : ℝ) ((0 : ℝ) ^ 2)) := ⟨fun u => by have := u.2; simp at this⟩
      exact Real.iSup_of_isEmpty _
    exact continuousOn_const.congr h0
  have hκ2 : 0 < κ ^ 2 := by positivity
  intro α0 hα0
  refine ContinuousAt.continuousWithinAt ?_
  have hIoo : Ioo (0 : ℝ) 1 ∈ 𝓝 α0 := isOpen_Ioo.mem_nhds hα0
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- lower semicontinuity
    have : Nonempty (Ico (0 : ℝ) (κ ^ 2)) := ⟨⟨0, le_rfl, hκ2⟩⟩
    obtain ⟨⟨u, hu⟩, hau⟩ := exists_lt_of_lt_ciSup (f := fun u : Ico (0 : ℝ) (κ ^ 2) =>
      tauPs D (√(κ ^ 2 - (u : ℝ))) (√(κ ^ 2 + (u : ℝ))) α0 δ n m) ha
    have hcont : ContinuousAt (fun α => tauPs D (√(κ ^ 2 - u)) (√(κ ^ 2 + u)) α δ n m) α0 :=
      (tauPs_continuousOn hD (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hδ0 hδ1 hn hm).continuousAt hIoo
    filter_upwards [hcont.eventually (lt_mem_nhds hau), hIoo] with α h1 h2
    exact h1.trans_le (le_tauCpl hD h2.1.le h2.2 hδ0 hδ1 hn hm hu)
  · -- upper semicontinuity
    set τ0 := tauCpl D κ α0 δ n m with hτ0
    set c := (τ0 + b) / 2 with hc
    have hτc : τ0 < c := by rw [hc]; linarith
    have hcb : c < b := by rw [hc]; linarith
    have hτ0n : 0 ≤ τ0 := tauCpl_nonneg _ _ _ _ _ _
    set η := (c - τ0) / 3 with hη
    have hη0 : 0 < η := by rw [hη]; linarith
    set ρmax := √(κ ^ 2 + κ ^ 2) with hρmax
    have hρmax0 : 0 < ρmax := Real.sqrt_pos.2 (by linarith)
    obtain ⟨fs, hfs, hfmin⟩ := min5_attained (fun f => rootR (1 / (1 - α0)) ((1 - f) * δ) n m)
    obtain ⟨l1, l2, l3, l4⟩ := IsSplit.levels hfs hδ0 hδ1
    obtain ⟨rs, hrs⟩ : ∃ rs, rs = rootR (1 / (1 - α0)) ((1 - fs) * δ) n m := ⟨_, rfl⟩
    -- `√(2κ²)·min_f t₂ ≤ τ₀`
    have hstep4 : ρmax * rs ≤ τ0 := by
      have hle : ∀ u ∈ Ico (0 : ℝ) (κ ^ 2), √(κ ^ 2 + u) * rs ≤ τ0 := fun u hu => by
        have h1 := tauPs_ge_repair (D := D) (v := √(κ ^ 2 - u)) (δ := δ) (n := n) (m := m) hα0.1.ne'
          (Real.sqrt_nonneg (κ ^ 2 + u))
        rw [hfmin, ← hrs] at h1
        exact h1.trans (le_tauCpl hD hα0.1.le hα0.2 hδ0 hδ1 hn hm hu)
      have hlim : Tendsto (fun u : ℝ => √(κ ^ 2 + u) * rs) (𝓝[<] (κ ^ 2)) (𝓝 (ρmax * rs)) :=
        (((continuous_const.add continuous_id).sqrt.mul continuous_const).tendsto (κ ^ 2)).mono_left nhdsWithin_le_nhds
      refine le_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT hκ2] with u hu
      exact hle u ⟨hu.1.le, hu.2⟩
    -- the uniform smallness of `t₁` near `u = κ²`
    set α1 := (α0 + 1) / 2 with hα1
    have hα01 : α0 < α1 := by rw [hα1]; linarith [hα0.2]
    have hα11 : α1 < 1 := by rw [hα1]; linarith [hα0.2]
    set β1 := 1 / (1 - α1) with hβ1
    have hβ1pos : 1 < β1 := one_lt_beta ⟨by linarith [hα0.1], hα11⟩
    obtain ⟨w, hw, hsmall⟩ := rootH_small_v (D := D) (δ1 := fs * δ) (n := n) (m := m) hρmax0 (by linarith) l1 hη0 hn hm
    have hRRc : ContinuousAt (fun α => ρmax * rootR (1 / (1 - α)) ((1 - fs) * δ) n m) α0 := by
      have h1 : ContinuousAt (fun β => rootR β ((1 - fs) * δ) n m) (1 / (1 - α0)) :=
        (rootR_continuousOn l3 l4).continuousAt (Ioi_mem_nhds (one_lt_beta hα0))
      have h2 : ContinuousAt (fun α : ℝ => 1 / (1 - α)) α0 :=
        continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by linarith [hα0.2])
      exact continuousAt_const.mul (h1.comp (f := fun α : ℝ => 1 / (1 - α)) h2)
    have hval : ρmax * rootR (1 / (1 - α0)) ((1 - fs) * δ) n m < ρmax * rs + η := by rw [← hrs]; linarith
    have hRRev : ∀ᶠ α in 𝓝 α0, ρmax * rootR (1 / (1 - α)) ((1 - fs) * δ) n m < ρmax * rs + η :=
      hRRc.eventually (gt_mem_nhds hval)
    have hP : ∀ u0 ∈ Icc (0 : ℝ) (κ ^ 2), ∀ᶠ z : ℝ × ℝ in 𝓝 (α0, u0),
        z.2 ∈ Ico (0 : ℝ) (κ ^ 2) → Gc D κ δ n m (z.1, z.2) < c := by
      intro u0 hu0
      rcases hu0.2.lt_or_eq with hlt | heq
      · have hp0 : (α0, u0) ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-κ ^ 2) (κ ^ 2) := ⟨hα0, by linarith [hu0.1], hlt⟩
        have hG0 : Gc D κ δ n m (α0, u0) < c :=
          (le_tauCpl hD hα0.1.le hα0.2 hδ0 hδ1 hn hm ⟨hu0.1, hlt⟩).trans_lt hτc
        filter_upwards [(Gc_continuousAt hD hδ0 hδ1 hn hm hp0).eventually (gt_mem_nhds hG0)] with z hz _
        exact hz
      · subst heq
        have e1 : ∀ᶠ z : ℝ × ℝ in 𝓝 (α0, κ ^ 2), z.1 ∈ Ioo (0 : ℝ) α1 :=
          continuousAt_fst.eventually (isOpen_Ioo.mem_nhds ⟨hα0.1, hα01⟩)
        have e2 : ∀ᶠ z : ℝ × ℝ in 𝓝 (α0, κ ^ 2), κ ^ 2 - w ^ 2 < z.2 :=
          continuousAt_snd.eventually (lt_mem_nhds (by simp; positivity))
        have e3 : ∀ᶠ z : ℝ × ℝ in 𝓝 (α0, κ ^ 2), ρmax * rootR (1 / (1 - z.1)) ((1 - fs) * δ) n m < ρmax * rs + η :=
          (continuous_fst.tendsto ((α0, κ ^ 2) : ℝ × ℝ)).eventually hRRev
        filter_upwards [e1, e2, e3] with z hz1 hz2 hz3 hzu
        have hz1' : z.1 ∈ Ioo (0 : ℝ) 1 := ⟨hz1.1, hz1.2.trans hα11⟩
        have hBz : 1 < 1 / (1 - z.1) := one_lt_beta hz1'
        have hBβ1 : 1 / (1 - z.1) ≤ β1 :=
          one_div_le_one_div_of_le (by linarith [hz1.2, hα11]) (by linarith [hz1.2])
        have hV : 0 < √(κ ^ 2 - z.2) := Real.sqrt_pos.2 (by linarith [hzu.2])
        have hVw : √(κ ^ 2 - z.2) < w := by
          rw [Real.sqrt_lt' hw]; linarith
        have hR : 0 < √(κ ^ 2 + z.2) := Real.sqrt_pos.2 (by linarith [hzu.1])
        have hRle : √(κ ^ 2 + z.2) ≤ ρmax := Real.sqrt_le_sqrt (by linarith [hzu.2])
        have hfs3 : fs * δ < 3 := by linarith
        have hH : rootH D (√(κ ^ 2 - z.2)) (√(κ ^ 2 + z.2)) (1 / (1 - z.1)) (fs * δ) n m ≤ η :=
          (rootH_mono_const hD hV le_rfl hR hRle hBz.le l1 hn hm).trans
            ((rootH_mono_beta hD hV.le hρmax0.le hBz.le hBβ1 l1 hfs3 hn hm).trans (hsmall _ hV hVw))
        have hRR : √(κ ^ 2 + z.2) * rootR (1 / (1 - z.1)) ((1 - fs) * δ) n m ≤
            ρmax * rootR (1 / (1 - z.1)) ((1 - fs) * δ) n m :=
          mul_le_mul_of_nonneg_right hRle (rootR_nonneg _ _ _ _)
        have hsplit : Gc D κ δ n m z ≤ tauSplit D (√(κ ^ 2 - z.2)) (√(κ ^ 2 + z.2)) z.1 δ fs n m :=
          tauPs_pos_le hz1'.1.ne' hfs
        unfold tauSplit at hsplit
        rw [hη] at hH hz3
        linarith
    have hall := (isCompact_Icc (a := (0 : ℝ)) (b := κ ^ 2)).eventually_forall_of_forall_eventually
      (P := fun α u => u ∈ Ico (0 : ℝ) (κ ^ 2) → Gc D κ δ n m (α, u) < c) hP
    filter_upwards [hall, hIoo] with α hα hαI
    refine (tauCpl_le (by linarith) fun u hu => (hα u (Ico_subset_Icc_self hu) hu).le).trans_lt hcb

theorem tauCpl_tendsto_iff {D κ δ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : Tendsto (fun α => tauCpl D κ α δ n m) (𝓝[<] 1) atTop ↔ κ ≠ 0 := by
  constructor
  · intro ht hκ
    subst hκ
    refine not_tendsto_of_le (C := 0) (fun α _ => tauCpl_le le_rfl fun u hu => ?_) ht
    exfalso
    have := hu.2
    simp at this
    linarith [hu.1]
  · intro hκ
    have hκ2 : 0 < κ ^ 2 := by positivity
    have habs : 0 < √(κ ^ 2 - 0) := Real.sqrt_pos.2 (by linarith)
    have habs' : 0 < √(κ ^ 2 + 0) := Real.sqrt_pos.2 (by linarith)
    have h0 := (tauPs_tendsto_iff (D := D) (v := √(κ ^ 2 - 0)) (ρbar := √(κ ^ 2 + 0)) hD habs.le habs'.le hδ0 hδ1 hn
      hm).2 (Or.inr ⟨habs, habs'⟩)
    refine tendsto_atTop_mono' _ ?_ h0
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with α hα
    exact le_tauCpl hD hα.1.le hα.2 hδ0 hδ1 hn hm ⟨le_rfl, hκ2⟩

theorem coupled_tau_continuous : Claims.coupled_tau_continuous :=
  fun _ _ _ _ _ hD hδ0 hδ1 hn hm =>
    ⟨tauCpl_continuousOn hD hδ0 hδ1 hn hm, tauCpl_tendsto_iff hD hδ0 hδ1 hn hm⟩

end StatFormal.Wave30tw
