import StatFormal.Wave30tz.RouteFit
import StatFormal.Wave31tr.Statements

/-!
# Wave 31tr, chunk M3: T19 `fitted_ramp_fw` — Lemma 4 for a Frank–Wolfe point (untrusted route)

Copy-adapted from the certified `Wave30tz.fitted_ramp_route` (`Wave30tz/RouteFit.lean`). The exact minimality of `(w, v)` is
used there only through `A − B = D̂` with `A ≤ Σ w′_i h_i`, `Σ v′_j h′_j ≤ B` for capped `w′, v′` (the first-order conditions),
i.e. through the separation `min T − max U ≥ D̂` of the witness values. For a Frank–Wolfe point of gap `ρ` the separation is
`s ≥ (1 − ρ/2)D̂` (`sep_of_isFWPoint`, T18 (b)), so the empirical criterion at the fitted cuts is
`≥ (1 − ρ/2)D̂ − βD_φr − β²κ²r/D̂`; with `D̂ ≥ D_α − βZ⁻ ≥ (1 − ρ/2)D_α − βZ⁻ > 0` (the projection step `dpop_sub_le_qpVal`
needs only feasibility) and `(1 − ρ/2)D̂ ≥ (1 − ρ/2)D_α − βZ⁻`, Lemma 2 gives `θ ≥ Θ((1 − ρ/2)D_α)`. The own-term shift, the
near-quantile bound, the width and the excess are unchanged.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31tr.RouteFW

open StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30ty StatFormal.Wave30tp
open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.ZeroSet
open StatFormal.Wave30tz.Fit

section Sep

variable {𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The Frank–Wolfe separation** (T18 (b), the direction used by T19, T20): at a Frank–Wolfe point of gap `ρ` with `D̂ > 0`,
every capped `(w′, v′)` has `Σ w′_i f̂(x_i) − Σ v′_j f̂(y_j) ≥ (1 − ρ/2)D̂` (`2D̂² − 2D̂⟪f̂, e′⟫ ≤ ρD̂²`). -/
theorem sep_of_isFWPoint {φ : 𝒳 → H} {α ρ : ℝ} {n m : ℕ} {x : Fin n → 𝒳} {y : Fin m → 𝒳} {w : Fin n → ℝ}
    {v : Fin m → ℝ} (hfw : IsFWPoint φ α ρ x y w v) (hd : 0 < qpVal φ x y w v) {w' : Fin n → ℝ} {v' : Fin m → ℝ}
    (hw' : IsCapped α w') (hv' : IsCapped α v') :
    (1 - ρ / 2) * qpVal φ x y w v ≤
      ∑ i, w' i * ⟪witness φ x y w v, φ (x i)⟫_ℝ - ∑ j, v' j * ⟪witness φ x y w v, φ (y j)⟫_ℝ := by
  have h := hfw.2.2 w' v' hw' hv'
  set e := wsum φ x w - wsum φ y v with hedef
  have hd' : 0 < ‖e‖ := hd
  have hq : qpVal φ x y w v = ‖e‖ := rfl
  have hwit : witness φ x y w v = ‖e‖⁻¹ • e := rfl
  have hval : ∑ i, w' i * ⟪witness φ x y w v, φ (x i)⟫_ℝ - ∑ j, v' j * ⟪witness φ x y w v, φ (y j)⟫_ℝ =
      ‖e‖⁻¹ * ⟪e, wsum φ x w' - wsum φ y v'⟫_ℝ := by
    rw [← inner_wsum, ← inner_wsum, ← inner_sub_right, hwit, real_inner_smul_left]
  rw [hval, hq]
  rw [real_inner_self_eq_norm_sq] at h
  rw [le_inv_mul_iff₀ hd']
  linarith

end Sep

/-- **T19** (Lemma 4 for a Frank–Wolfe point; copy-adapted from the certified `Wave30tz.fitted_ramp_route`): the separation
`s ≥ (1 − ρ/2)D̂` (`sep_of_isFWPoint`) replaces the exact identity `A − B = D̂` and the first-order conditions, and
`(1 − ρ/2)D_α` replaces `D_α` in `Θ`. -/
theorem fitted_ramp_fw_route : Claims.fitted_ramp_fw := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ Dφ α ρ n m x y w v hφ hκ hDφ hα0 hα1 hn hm hρ0 hρ1 hfw hZm
  set D := Dpop φ P Q α with hDdef
  set Zp := hingeZ P Q φ hingePos hingePos 1 κ κ (x, y) with hZpdef
  set Zm := hingeZm P Q φ hingePos hingePos 1 κ κ (x, y) with hZmdef
  have hβ1 : 1 ≤ beta α := Wave30tz.one_le_beta hα0 hα1
  have hβ0 : 0 ≤ beta α := by linarith
  have h1 : D - beta α * Zm ≤ qpVal φ x y w v := dpop_sub_le_qpVal P Q hφ hκ hα0 hα1 x y hfw.1 hfw.2.1
  have hZm0 : 0 ≤ Zm := hingeZm_nonneg P Q hκ x y
  have h1ρ : 0 < 1 - ρ / 2 := by linarith
  have hβZm0 : 0 ≤ beta α * Zm := mul_nonneg hβ0 hZm0
  have hD0 : 0 < D := by
    by_contra hcon
    have : (1 - ρ / 2) * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1ρ.le (not_lt.1 hcon)
    linarith
  have hDD' : (1 - ρ / 2) * D ≤ D := by
    have : 0 ≤ ρ / 2 * D := mul_nonneg (by linarith) hD0.le
    linarith
  set Dh := qpVal φ x y w v with hDhdef
  have hDh : 0 < Dh := by linarith
  refine ⟨h1, hDh, fun t u hC => ?_⟩
  set e := wsum φ x w - wsum φ y v with hedef
  have hne : ‖e‖ = Dh := rfl
  set fh := witness φ x y w v with hfhdef
  have hfh : fh = Dh⁻¹ • e := rfl
  have hfh1 : ‖fh‖ = 1 := by
    rw [hfh, norm_smul, norm_inv, Real.norm_of_nonneg hDh.le, hne, inv_mul_cancel₀ hDh.ne']
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨z0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ z0)
  set F : 𝒳 → ℝ := fun z => ⟪fh, φ z⟫_ℝ with hFdef
  have hFm : Measurable F := (stronglyMeasurable_const.inner hφ).measurable
  have hFb : ∀ z, |F z| ≤ κ := abs_inner_le_of_norm hκ hfh1.le
  set h : Fin n → ℝ := fun i => F (x i) with hhdef
  set h' : Fin m → ℝ := fun j => F (y j) with hh'def
  -- the Frank–Wolfe separation `s ≥ (1 − ρ/2)D̂` (T18 (b))
  have hsep : ∀ w' v', IsCapped α w' → IsCapped α v' →
      (1 - ρ / 2) * Dh ≤ ∑ i, w' i * h i - ∑ j, v' j * h' j := fun w' v' hw' hv' => sep_of_isFWPoint hfw hDh hw' hv'
  -- finite CVaR duality: `max T − min U ≥ s`
  obtain ⟨tstar, w', hw', hw'eq⟩ := exists_critT_eq hn x hα0 hα1 hFm hFb
  obtain ⟨ustar, v', hv', hv'eq⟩ := exists_critU_eq hm y hα0 hα1 hFm hFb
  have hTU : (1 - ρ / 2) * Dh ≤ critT α h tstar - critU α h' ustar := by
    rw [← hw'eq, ← hv'eq]; exact hsep w' v' hw' hv'
  -- own terms
  set εX := beta α / n * κ ^ 2 / Dh with hεX
  set εY := beta α / m * κ ^ 2 / Dh with hεY
  have hεX0 : 0 ≤ εX := by positivity
  have hεY0 : 0 ≤ εY := by positivity
  have hown : ∀ (k : ℕ) (c : ℝ), 0 ≤ c → c ≤ 1 / (k * (1 - α)) → ∀ z,
      0 ≤ c * ‖φ z‖ ^ 2 / Dh ∧ c * ‖φ z‖ ^ 2 / Dh ≤ beta α / k * κ ^ 2 / Dh := by
    intro k c hc0 hc1 z
    rw [cap_eq] at hc1
    refine ⟨by positivity, ?_⟩
    gcongr
    exact hκ z
  have hownX : ∀ i, h i - εX ≤ ownX φ x y w v i ∧ ownX φ x y w v i ≤ h i := by
    intro i
    obtain ⟨a, b⟩ := hown n (w i) (hfw.1.1 i).1 (hfw.1.1 i).2 (x i)
    have : ownX φ x y w v i = h i - w i * ‖φ (x i)‖ ^ 2 / Dh := rfl
    rw [this]; constructor <;> linarith
  have hownY : ∀ j, h' j ≤ ownY φ x y w v j ∧ ownY φ x y w v j ≤ h' j + εY := by
    intro j
    obtain ⟨a, b⟩ := hown m (v j) (hfw.2.1.1 j).1 (hfw.2.1.1 j).2 (y j)
    have : ownY φ x y w v j = h' j + v j * ‖φ (y j)‖ ^ 2 / Dh := rfl
    rw [this]; constructor <;> linarith
  -- ranks
  have hp1 : 1 - α ≤ 1 := by linarith
  have hα1' : α ≤ 1 := hα1.le
  have hkL1 : 1 ≤ rkLo n (1 - α) := one_le_rkLo _ _
  have hkLn : rkLo n (1 - α) ≤ n := rkLo_le hn hp1
  have hkH1 : 1 ≤ rkHi n (1 - α) := one_le_rkHi hn _
  have hkHn : rkHi n (1 - α) ≤ n := rkHi_le _ _
  have hkLH : rkLo n (1 - α) ≤ rkHi n (1 - α) := rkLo_le_rkHi hn hp1
  have hjL1 : 1 ≤ rkLo m α := one_le_rkLo _ _
  have hjLm : rkLo m α ≤ m := rkLo_le hm hα1'
  have hjH1 : 1 ≤ rkHi m α := one_le_rkHi hm _
  have hjHm : rkHi m α ≤ m := rkHi_le _ _
  have hjLH : rkLo m α ≤ rkHi m α := rkLo_le_rkHi hm hα1'
  -- the cuts against the order statistics of the in-sample values
  obtain ⟨⟨ht1, ht2⟩, ⟨hu1, hu2⟩⟩ := hC
  have ht_lo : ordStat h (rkLo n (1 - α)) - εX ≤ t :=
    (ordStat_sub_le (fun i => (hownX i).1) hkL1 hkLn).trans ht1
  have ht_hi : t ≤ ordStat h (rkHi n (1 - α)) :=
    ht2.trans (ordStat_mono (fun i => (hownX i).2) hkH1 hkHn)
  have hu_lo : ordStat h' (rkLo m α) ≤ u :=
    (ordStat_mono (fun j => (hownY j).1) hjL1 hjLm).trans hu1
  have hu_hi : u ≤ ordStat h' (rkHi m α) + εY := by
    have := ordStat_sub_le (h := ownY φ x y w v) (h' := h') (ε := εY)
      (fun j => by linarith [(hownY j).2]) hjH1 hjHm
    linarith
  -- the range of the witness values
  have hrange : ∀ a b : 𝒳, F a - F b ≤ Dφ := by
    intro a b
    have : F a - F b = ⟪fh, φ a - φ b⟫_ℝ := by simp only [hFdef, inner_sub_right]
    rw [this]
    refine (real_inner_le_norm _ _).trans ?_
    rw [hfh1, one_mul]; exact hDφ a b
  have hR : ∀ i j, h i - h j ≤ Dφ := fun i j => hrange _ _
  have hR' : ∀ i j, h' i - h' j ≤ Dφ := fun i j => hrange _ _
  have hLip : max 1 (beta α - 1) ≤ beta α := max_le hβ1 (by linarith)
  -- the cuts are nearly optimal (Lemma 3)
  have hT : critT α h tstar - beta α / n * Dφ - beta α * εX ≤ critT α h t := by
    set t₀ := max t (ordStat h (rkLo n (1 - α))) with ht₀def
    have ht₀ : t₀ ∈ Icc (ordStat h (rkLo n (1 - α))) (ordStat h (rkHi n (1 - α))) :=
      ⟨le_max_right _ _, max_le ht_hi (ordStat_mono_rank h hkL1 hkLH hkHn)⟩
    have hb := critT_bracket hn hα0 hα1 h hR ht₀ tstar
    have hl := critT_lipschitz hα0 hα1 h t₀ t
    have hd : |t₀ - t| ≤ εX := by
      have h0 : t ≤ t₀ := le_max_left _ _
      have h2 : t₀ - t ≤ εX := by
        rcases le_total t (ordStat h (rkLo n (1 - α))) with hle | hle
        · rw [ht₀def, max_eq_right hle]; linarith
        · rw [ht₀def, max_eq_left hle]; linarith
      rw [abs_of_nonneg (by linarith)]; exact h2
    have h3 : |critT α h t₀ - critT α h t| ≤ beta α * εX :=
      hl.trans (mul_le_mul hLip hd (abs_nonneg _) hβ0)
    have := (abs_le.1 h3).2
    linarith
  have hU : critU α h' u ≤ critU α h' ustar + beta α / m * Dφ + beta α * εY := by
    set u₀ := min u (ordStat h' (rkHi m α)) with hu₀def
    have hu₀ : u₀ ∈ Icc (ordStat h' (rkLo m α)) (ordStat h' (rkHi m α)) :=
      ⟨le_min hu_lo (ordStat_mono_rank h' hjL1 hjLH hjHm), min_le_right _ _⟩
    have hb := critU_bracket hm hα0 hα1 h' hR' hu₀ ustar
    have hl := critU_lipschitz hα0 hα1 h' u u₀
    have hd : |u - u₀| ≤ εY := by
      have h0 : u₀ ≤ u := min_le_left _ _
      have h2 : u - u₀ ≤ εY := by
        rcases le_total u (ordStat h' (rkHi m α)) with hle | hle
        · rw [hu₀def, min_eq_left hle]; linarith
        · rw [hu₀def, min_eq_right hle]; linarith
      rw [abs_of_nonneg (by linarith)]; exact h2
    have h3 : |critU α h' u - critU α h' u₀| ≤ beta α * εY :=
      hl.trans (mul_le_mul hLip hd (abs_nonneg _) hβ0)
    have := (abs_le.1 h3).2
    linarith
  -- the empirical criterion at the fitted cuts
  have hθn : (1 - ρ / 2) * Dh - beta α * Dφ * (1 / n + 1 / m) - beta α ^ 2 * κ ^ 2 * (1 / n + 1 / m) / Dh ≤
      critT α h t - critU α h' u := by
    have e1 : beta α * εX + beta α * εY = beta α ^ 2 * κ ^ 2 * (1 / n + 1 / m) / Dh := by
      simp only [hεX, hεY]; ring
    have e2 : beta α / n * Dφ + beta α / m * Dφ = beta α * Dφ * (1 / n + 1 / m) := by ring
    linarith
  -- Lemma 2: the population criterion
  have hcu : -(beta α) * Zp ≤ theta P Q α F t u - (critT α h t - critU α h' u) :=
    (crit_uniform_route 𝒳 H P Q φ κ α n m x y fh t u hφ hκ hα0 hα1 hn hm hfh1.le).1
  have hDm : 0 < (1 - ρ / 2) * D - beta α * Zm := by linarith
  have hc0 : 0 ≤ beta α ^ 2 * κ ^ 2 * (1 / n + 1 / m) := by positivity
  have hdiv : beta α ^ 2 * κ ^ 2 * (1 / n + 1 / m) / Dh ≤
      beta α ^ 2 * κ ^ 2 * (1 / n + 1 / m) / ((1 - ρ / 2) * D - beta α * Zm) :=
    div_le_div_of_nonneg_left hc0 hDm (by linarith)
  have hA : (1 - ρ / 2) * D - beta α * Zm ≤ (1 - ρ / 2) * Dh := by
    have e1 := mul_le_mul_of_nonneg_left h1 h1ρ.le
    have e2 : 0 ≤ ρ / 2 * (beta α * Zm) := mul_nonneg (by linarith) hβZm0
    calc (1 - ρ / 2) * D - beta α * Zm ≤ (1 - ρ / 2) * D - beta α * Zm + ρ / 2 * (beta α * Zm) :=
          le_add_of_nonneg_right e2
      _ = (1 - ρ / 2) * (D - beta α * Zm) := by ring
      _ ≤ (1 - ρ / 2) * Dh := e1
  have hθ : fitTheta α ((1 - ρ / 2) * D) Zp Zm κ Dφ (1 / n + 1 / m) ≤ theta P Q α F t u := by
    unfold fitTheta
    linarith
  -- the width
  have hwidth : t - u ≤ Dφ := by
    obtain ⟨i, hi⟩ := exists_eq_ordStat h hkH1 hkHn
    obtain ⟨j, hj⟩ := exists_eq_ordStat h' hjL1 hjLm
    have := hrange (x i) (y j)
    have hi' : F (x i) = ordStat h (rkHi n (1 - α)) := hi
    have hj' : F (y j) = ordStat h' (rkLo m α) := hj
    linarith
  have hθle : theta P Q α F t u ≤ t - u := by
    rw [Elem.theta_eq P Q α (Elem.integrable_hinge hFm hFb t).1 (Elem.integrable_hinge hFm hFb u).2]
    have h1 : 0 ≤ ∫ z, max (t - F z) 0 ∂P := integral_nonneg fun _ => le_max_right _ _
    have h2 : 0 ≤ ∫ z, max (F z - u) 0 ∂Q := integral_nonneg fun _ => le_max_right _ _
    have h3 := mul_nonneg hβ0 h1
    have h4 := mul_nonneg hβ0 h2
    linarith only [h3, h4]
  refine ⟨hwidth, hθle, hθ, fun hΘpos => ?_⟩
  -- the excess of the ramp
  have hut : u < t := by linarith
  obtain ⟨-, h21⟩ := StatFormal.Wave30tq.lem2_1 𝒳 P Q α F t u hFm hα0 hα1 hut
  obtain ⟨-, h22⟩ := StatFormal.Wave30tq.lem2_2 𝒳 P Q α F t u hFm ⟨κ, hFb⟩ hα0 hα1 hut
  obtain ⟨h22e, -⟩ := StatFormal.Wave30tq.lem2_2 𝒳 P Q α F t u hFm ⟨κ, hFb⟩ hα0 hα1 hut
  have hβpos : 0 < beta α := by linarith
  have hclip : fitTheta α ((1 - ρ / 2) * D) Zp Zm κ Dφ (1 / n + 1 / m) ≤
      beta α * (t - u) * ((∫ z, ramp F t u z ∂P) - (∫ z, ramp F t u z ∂Q) - α) := by
    rw [← h21]; linarith
  have hpos : 0 < beta α * (t - u) := mul_pos hβpos (by linarith)
  refine ⟨hut, ?_⟩
  calc fitTheta α ((1 - ρ / 2) * D) Zp Zm κ Dφ (1 / n + 1 / m) / (beta α * Dφ)
      ≤ fitTheta α ((1 - ρ / 2) * D) Zp Zm κ Dφ (1 / n + 1 / m) / (beta α * (t - u)) :=
        div_le_div_of_nonneg_left hΘpos.le hpos (mul_le_mul_of_nonneg_left hwidth hβpos.le)
    _ ≤ _ := by rw [div_le_iff₀ hpos]; linarith

end StatFormal.Wave31tr.RouteFW
