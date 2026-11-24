import StatFormal.Wave31tu.RouteKLocalQ

/-!
# Wave 31tu, route K: Y20(c) `lap_local_c` and Y21 `local_rate` (untrusted proof material)

* `c_arith`: with `nπ ≥ 1/4`, `δ ∈ [0,1)` and `h = (1−δ)/(2(nπ)^{1/2})`: `h ∈ [0,1]`, `h(nπ)^{1/2} = (1−δ)/2` and
  `hπ = ½(1−δ)(π/n)^{1/2}`;
* `lap_local_c_route : Claims.lap_local_c` (S4 :1416-1417): `lap_local` at this `h`;
* `first_pair`, `second_pair`: the perturbed pair of `lap_local` (`lap_local_Q`) at `h = (1−δ)/(2(nπ)^{1/2})` (resp. with `m`, `π′`),
  packaged with the hypotheses of Theorem 5.11(i) it satisfies, its distance to `(P, Q)` and the probability bound;
* `local_rate_route : Claims.local_rate` (S4 :1024-1026, :1383): a radius `r ≤ r⋆` on which `p, q` are continuous and positive
  (from the continuity in `IsCross` and `p(x₀) = q(x₀) > 0`), the tail constant of `ExpTail`, `N₀ = ⌈1/(4 min{π, π′})⌉ + 1`; for
  `n ≤ m` the first sample is perturbed, for `m < n` the second; `c = ½(1−δ)min{π^{1/2}, π′^{1/2}}`, `C = max{π^{1/2}, π′^{1/2}}`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave31tu.RouteK

open StatFormal StatFormal.LocalLower StatFormal.Wave31tq StatFormal.Wave30tp

/-- The choice `h = (1−δ)/(2(Nπ)^{1/2})` for `Nπ ≥ 1/4`. -/
theorem c_arith {δ π N : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hN : 0 ≤ N) (hπ0 : 0 ≤ π) (hNπ : 1 / 4 ≤ N * π) :
    0 ≤ (1 - δ) / (2 * √(N * π)) ∧ (1 - δ) / (2 * √(N * π)) ≤ 1 ∧
      1 - δ - (1 - δ) / (2 * √(N * π)) * √(N * π) = (1 - δ) / 2 ∧
      (1 - δ) / (2 * √(N * π)) * π = (1 - δ) / 2 * √(π / N) := by
  have hs : (1 : ℝ) / 2 ≤ √(N * π) := by
    have h14 : √(1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h14]; exact Real.sqrt_le_sqrt hNπ
  have hs0 : 0 < √(N * π) := by linarith
  have hNpos : 0 < N := by
    rcases hN.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hNπ; norm_num at hNπ
  have hπpos : 0 < π := by
    rcases hπ0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hNπ; norm_num at hNπ
  refine ⟨div_nonneg (by linarith) (by positivity), ?_, ?_, ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  · field_simp; ring
  · rw [Real.sqrt_mul hN, Real.sqrt_div' π hN]
    have hsN : 0 < √N := Real.sqrt_pos.2 hNpos
    have hsπ : 0 < √π := Real.sqrt_pos.2 hπpos
    field_simp
    rw [Real.sq_sqrt hπ0]

theorem lap_local_c_route : Claims.lap_local_c := by
  intro P Q _ _ p q x₀ ℓ₀ rs cs r C' δ hcross hpx hexp hcond hr hrs hpc hqc hpos hδ0 hδ1 A₁ B₁ πh n m hnπ hh Ph
  obtain ⟨hπ, hall⟩ := lap_local_route P Q p q x₀ ℓ₀ rs cs r C' δ hcross hpx hexp hcond hr hrs hpc hqc hpos
  obtain ⟨h0, h1, e1, e2⟩ := c_arith hδ0 hδ1 (Nat.cast_nonneg n) hπ.le hnπ
  refine ⟨⟨h0, h1⟩, fun Ξ _ ρ _ T hT hval => ?_⟩
  obtain ⟨-, -, hprob, -, -, -, -, -, -, -, hlecam⟩ := hall hh ⟨h0, h1⟩
  have hP' : IsProbabilityMeasure Ph := hprob
  have := sampleLaw_isProb Ph Q n m
  have hb := hlecam n m Ξ ρ T hT hval
  calc (1 - δ) / 2 = 1 - δ - hh * √(n * πh) := e1.symm
    _ ≤ ((sampleLaw Ph Q n m).prod ρ).real {z | hh * πh ≤ Distances.tvDist Ph Q - T z} := hb
    _ = ((sampleLaw Ph Q n m).prod ρ).real {z | (1 - δ) / 2 * √(πh / n) ≤ Distances.tvDist Ph Q - T z} := by
        change ((sampleLaw Ph Q n m).prod ρ).real {z | (1 - δ) / (2 * √(n * πh)) * πh ≤ Distances.tvDist Ph Q - T z} = _
        rw [e2]

/-- The first-sample perturbed pair at `h = (1−δ)/(2(nπ)^{1/2})`, packaged. -/
theorem first_pair {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {p q : ℝ → ℝ}
    {x₀ ℓ₀ rs cs r C' δ : ℝ} (hcross : IsCross P Q p q x₀ ℓ₀) (hpx : 0 < p x₀) (hexp : ExpTailWith P Q x₀ C')
    (hcond : CondR p q x₀ rs cs) (hr : 0 < r) (hrs : r ≤ rs) (hpc : ContinuousOn p (Icc (x₀ - 2 * r) (x₀ + 2 * r)))
    (hqc : ContinuousOn q (Icc (x₀ - 2 * r) (x₀ + 2 * r))) (hpos : ∀ z ∈ Icc (x₀ - 2 * r) (x₀ + 2 * r), 0 < p z ∧ 0 < q z)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (n m : ℕ)
    (hnπ : 1 / 4 ≤ n * min (P.real (Ioo (x₀ + r) (x₀ + 2 * r))) (P.real (Ioo (x₀ - 2 * r) (x₀ - r)))) :
    ∃ (P' : Measure ℝ) (p' : ℝ → ℝ), ∃ _ : IsProbabilityMeasure P',
      IsCross P' Q p' q x₀ ℓ₀ ∧ 0 < p' x₀ ∧ ExpTail P' Q x₀ ∧ CondR p' q x₀ rs (cs / 2) ∧
      Distances.tvDist P' P =
        (1 - δ) / 2 * √(min (P.real (Ioo (x₀ + r) (x₀ + 2 * r))) (P.real (Ioo (x₀ - 2 * r) (x₀ - r))) / n) ∧
      ∀ (Ξ : Type) [MeasurableSpace Ξ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ] (T : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ),
        Measurable T → ((sampleLaw P Q n m).prod ρ).real {z | Distances.tvDist P Q < T z} ≤ δ →
          (1 - δ) / 2 ≤ ((sampleLaw P' Q n m).prod ρ).real
            {z | (1 - δ) / 2 * √(min (P.real (Ioo (x₀ + r) (x₀ + 2 * r))) (P.real (Ioo (x₀ - 2 * r) (x₀ - r))) / n) ≤
              Distances.tvDist P' Q - T z} := by
  obtain ⟨hπ, hall⟩ := lap_local_route P Q p q x₀ ℓ₀ rs cs r C' δ hcross hpx hexp hcond hr hrs hpc hqc hpos
  obtain ⟨h0, h1, -, e2⟩ := c_arith hδ0 hδ1 (Nat.cast_nonneg n) hπ.le hnπ
  obtain ⟨-, -, hprob, -, htvself, hcrossh, hpxh, htailh, hcondh, -, -⟩ := hall _ ⟨h0, h1⟩
  obtain ⟨-, hc⟩ := lap_local_c_route P Q p q x₀ ℓ₀ rs cs r C' δ hcross hpx hexp hcond hr hrs hpc hqc hpos hδ0 hδ1 n m hnπ
  refine ⟨_, _, hprob, hcrossh, hpxh, ⟨_, htailh.1, htailh.2⟩, hcondh, ?_, fun Ξ _ ρ _ T hT hval => hc Ξ ρ T hT hval⟩
  rw [htvself, e2]

/-- The second-sample perturbed pair at `h = (1−δ)/(2(mπ′)^{1/2})`, packaged (from `lap_local_Q`). -/
theorem second_pair {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {p q : ℝ → ℝ}
    {x₀ ℓ₀ rs cs r C' δ : ℝ} (hcross : IsCross P Q p q x₀ ℓ₀) (hpx : 0 < p x₀) (hexp : ExpTailWith P Q x₀ C')
    (hcond : CondR p q x₀ rs cs) (hr : 0 < r) (hrs : r ≤ rs) (hpc : ContinuousOn p (Icc (x₀ - 2 * r) (x₀ + 2 * r)))
    (hqc : ContinuousOn q (Icc (x₀ - 2 * r) (x₀ + 2 * r))) (hpos : ∀ z ∈ Icc (x₀ - 2 * r) (x₀ + 2 * r), 0 < p z ∧ 0 < q z)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (n m : ℕ)
    (hmπ : 1 / 4 ≤ m * min (Q.real (Ioo (x₀ + r) (x₀ + 2 * r))) (Q.real (Ioo (x₀ - 2 * r) (x₀ - r)))) :
    ∃ (Q' : Measure ℝ) (q' : ℝ → ℝ), ∃ _ : IsProbabilityMeasure Q',
      IsCross P Q' p q' x₀ ℓ₀ ∧ ExpTail P Q' x₀ ∧ CondR p q' x₀ rs (cs / 2) ∧
      Distances.tvDist Q' Q =
        (1 - δ) / 2 * √(min (Q.real (Ioo (x₀ + r) (x₀ + 2 * r))) (Q.real (Ioo (x₀ - 2 * r) (x₀ - r))) / m) ∧
      ∀ (Ξ : Type) [MeasurableSpace Ξ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ] (T : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ),
        Measurable T → ((sampleLaw P Q n m).prod ρ).real {z | Distances.tvDist P Q < T z} ≤ δ →
          (1 - δ) / 2 ≤ ((sampleLaw P Q' n m).prod ρ).real
            {z | (1 - δ) / 2 * √(min (Q.real (Ioo (x₀ + r) (x₀ + 2 * r))) (Q.real (Ioo (x₀ - 2 * r) (x₀ - r))) / m) ≤
              Distances.tvDist P Q' - T z} := by
  obtain ⟨hπ, hall⟩ := lap_local_Q_route P Q p q x₀ ℓ₀ rs cs r C' δ hcross hpx hexp hcond hr hrs hpc hqc hpos
  obtain ⟨h0, h1, e1, e2⟩ := c_arith hδ0 hδ1 (Nat.cast_nonneg m) hπ.le hmπ
  obtain ⟨-, -, hprob, -, htvself, hcrossh, htailh, hcondh, -, hlecam⟩ := hall _ ⟨h0, h1⟩
  refine ⟨_, _, hprob, hcrossh, ⟨_, htailh.1, htailh.2⟩, hcondh, ?_, fun Ξ _ ρ _ T hT hval => ?_⟩
  · rw [htvself, e2]
  · have hb := hlecam n m Ξ ρ T hT hval
    rw [e1, e2] at hb
    exact hb

/-- A radius `r ∈ (0, r⋆]` on which `p, q` are continuous and positive on `[x₀ − 2r, x₀ + 2r]`. -/
theorem exists_radius {P Q : Measure ℝ} {p q : ℝ → ℝ} {x₀ ℓ₀ rs : ℝ} (hcross : IsCross P Q p q x₀ ℓ₀) (hpx : 0 < p x₀)
    (hrs : 0 < rs) :
    ∃ r, 0 < r ∧ r ≤ rs ∧ ContinuousOn p (Icc (x₀ - 2 * r) (x₀ + 2 * r)) ∧
      ContinuousOn q (Icc (x₀ - 2 * r) (x₀ + 2 * r)) ∧ ∀ z ∈ Icc (x₀ - 2 * r) (x₀ + 2 * r), 0 < p z ∧ 0 < q z := by
  have hpq := RouteM.cross_zero hcross
  obtain ⟨-, -, -, -, -, -, ⟨r₀, hr₀, hpc, hqc⟩, -⟩ := hcross
  have hqx : 0 < q x₀ := hpq ▸ hpx
  obtain ⟨δ2, hδ2, hp2⟩ := StatFormal.MomentTrim.exists_half_lower hr₀ hpc hpx
  obtain ⟨δ3, hδ3, hq3⟩ := StatFormal.MomentTrim.exists_half_lower hr₀ hqc hqx
  set w := min rs (min r₀ (min δ2 δ3)) with hw
  have hw0 : 0 < w := lt_min hrs (lt_min hr₀ (lt_min hδ2 hδ3))
  have hw1 : w ≤ rs := min_le_left _ _
  have hw2 : w ≤ r₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hw3 : w ≤ δ2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hw4 : w ≤ δ3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsub : Icc (x₀ - 2 * (w / 4)) (x₀ + 2 * (w / 4)) ⊆ Ioo (x₀ - r₀) (x₀ + r₀) := fun z hz =>
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have habs : ∀ z ∈ Icc (x₀ - 2 * (w / 4)) (x₀ + 2 * (w / 4)), |z - x₀| < w := fun z hz => by
    rw [abs_lt]; constructor <;> linarith [hz.1, hz.2]
  refine ⟨w / 4, by positivity, by linarith, hpc.mono hsub, hqc.mono hsub, fun z hz => ⟨?_, ?_⟩⟩
  · have := hp2 z ((habs z hz).trans_le hw3); linarith
  · have := hq3 z ((habs z hz).trans_le hw4); linarith

theorem local_rate_route : Claims.local_rate := by
  intro P Q _ _ p q x₀ ℓ₀ rs cs δ hcross hpx hexp hcond hδ0 hδ1
  obtain ⟨r, hr, hrs, hpc, hqc, hpos⟩ := exists_radius hcross hpx hcond.1
  obtain ⟨C', hC', ht⟩ := hexp
  have hexpW : ExpTailWith P Q x₀ C' := ⟨hC', ht⟩
  have hπP := (lap_local_route P Q p q x₀ ℓ₀ rs cs r C' δ hcross hpx hexpW hcond hr hrs hpc hqc hpos).1
  have hπQ := (lap_local_Q_route P Q p q x₀ ℓ₀ rs cs r C' δ hcross hpx hexpW hcond hr hrs hpc hqc hpos).1
  set πh := min (P.real (Ioo (x₀ + r) (x₀ + 2 * r))) (P.real (Ioo (x₀ - 2 * r) (x₀ - r))) with hπh
  set πq := min (Q.real (Ioo (x₀ + r) (x₀ + 2 * r))) (Q.real (Ioo (x₀ - 2 * r) (x₀ - r))) with hπq
  have hμ : 0 < min πh πq := lt_min hπP hπQ
  have hδ' : 0 < 1 - δ := by linarith
  refine ⟨(1 - δ) / 2 * min √πh √πq, max √πh √πq,
    mul_pos (by linarith) (lt_min (Real.sqrt_pos.2 hπP) (Real.sqrt_pos.2 hπQ)),
    lt_max_of_lt_left (Real.sqrt_pos.2 hπP), ⌈1 / (4 * min πh πq)⌉₊ + 1, fun n m hN Ξ _ ρ _ T hT hval => ?_⟩
  have hN1 : 1 ≤ min n m := le_trans (Nat.le_add_left 1 _) hN
  have hNμ : 1 / 4 ≤ ((min n m : ℕ) : ℝ) * min πh πq := by
    have h1 : 1 / (4 * min πh πq) ≤ ((min n m : ℕ) : ℝ) := by
      refine (Nat.le_ceil _).trans ?_
      exact_mod_cast (Nat.le_add_right _ 1).trans hN
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  -- the two inequalities between the constants, for `π ∈ {πh, πq}` and `k = n ∧ m`
  have hdist : ∀ (k : ℕ) (π : ℝ), 0 < (k : ℝ) → 0 ≤ π → √π ≤ max √πh √πq →
      (1 - δ) / 2 * √(π / k) ≤ max √πh √πq / √(k : ℝ) := by
    intro k π hk hπ0 hle
    rw [Real.sqrt_div' π hk.le, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    have : (1 - δ) / 2 ≤ 1 := by linarith
    nlinarith [Real.sqrt_nonneg π]
  have hgap : ∀ (k : ℕ) (π : ℝ), 0 < (k : ℝ) → min √πh √πq ≤ √π →
      (1 - δ) / 2 * min √πh √πq / √(k : ℝ) ≤ (1 - δ) / 2 * √(π / k) := by
    intro k π hk hle
    rw [Real.sqrt_div' π hk.le, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by linarith)) (Real.sqrt_nonneg _)
  rcases le_or_gt n m with hnm | hmn
  · -- perturb the first sample
    have hNn : min n m = n := min_eq_left hnm
    rw [hNn] at hNμ hN1 ⊢
    have hk : (0 : ℝ) < n := by exact_mod_cast hN1
    have hnπ : 1 / 4 ≤ (n : ℝ) * πh := hNμ.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hk.le)
    obtain ⟨P', p', hP', hc1, hc2, hc3, hc4, htv, hprob⟩ :=
      first_pair hcross hpx hexpW hcond hr hrs hpc hqc hpos hδ0 hδ1 n m hnπ
    rw [← hπh] at htv hprob
    have := sampleLaw_isProb P' Q n m
    refine ⟨P', Q, p', q, rs, cs / 2, hP', inferInstance, hc1, hc2, hc3, hc4, ?_, ?_⟩
    · rw [htv, Distances.tvDist_self, add_zero]
      exact hdist n πh hk hπP.le (le_max_left _ _)
    · refine (hprob Ξ ρ T hT hval).trans (measureReal_mono fun z hz => ?_)
      simp only [mem_ofPred_eq] at hz ⊢
      exact (hgap n πh hk (min_le_left _ _)).trans hz
  · -- perturb the second sample
    have hNm : min n m = m := min_eq_right hmn.le
    rw [hNm] at hNμ hN1 ⊢
    have hk : (0 : ℝ) < m := by exact_mod_cast hN1
    have hmπ : 1 / 4 ≤ (m : ℝ) * πq := hNμ.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hk.le)
    obtain ⟨Q', q', hQ', hc1, hc3, hc4, htv, hprob⟩ :=
      second_pair hcross hpx hexpW hcond hr hrs hpc hqc hpos hδ0 hδ1 n m hmπ
    rw [← hπq] at htv hprob
    have := sampleLaw_isProb P Q' n m
    refine ⟨P, Q', p, q', rs, cs / 2, inferInstance, hQ', hc1, hpx, hc3, hc4, ?_, ?_⟩
    · rw [htv, Distances.tvDist_self, zero_add]
      exact hdist m πq hk hπQ.le (le_max_right _ _)
    · refine (hprob Ξ ρ T hT hval).trans (measureReal_mono fun z hz => ?_)
      simp only [mem_ofPred_eq] at hz ⊢
      exact (hgap m πq hk (min_le_right _ _)).trans hz

end StatFormal.Wave31tu.RouteK
