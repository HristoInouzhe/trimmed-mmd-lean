import StatFormal.Lib.FrankWolfe.Gap
import StatFormal.Lib.FrankWolfe.Capped
import StatFormal.Wave31tr.Statements

/-!
# Wave 31tr, chunk M3: T18 `fw_gap`, `fw_exact` — the Frank–Wolfe gap identity (untrusted route)

At a capped pair `(w, v)` with `e = Σ w_i φ(x_i) − Σ v_j φ(y_j)`, `d = ‖e‖ = D̂ > 0` and `f̂ = e/d`:

* the extremes `μ = min_{w′} Σ w′_i f̂(x_i)`, `M = max_{v′} Σ v′_j f̂(y_j)` over the capped simplices are attained
  (`FrankWolfe.exists_isLeast_capped`, `exists_isGreatest_capped`), so `fwSep = μ − M` (`fwSep_eq`);
* (a), (b): the Frank–Wolfe gap of `‖e‖²` is `2d² − 2d(μ − M)` and is `≤ ρd²` iff `μ − M ≥ (1 − ρ/2)d`
  (`FrankWolfe.isGreatest_fwGap`, `fwGap_le_iff`, with `⟪e, c⟫ = d⟪f̂, c⟫`);
* `s ≤ D̂_α ≤ d` and `s = sep(f̂; 𝒞_α(P_n), 𝒞_α(Q_m))`: the empirical regions are the capped combinations
  (`FrankWolfe.region_empirical_eq_image`, the certified `Wave8a.georep_empirical`), on which `⟪f̂, a − b⟫ ≤ ‖a − b‖`
  (`‖f̂‖ = 1`) and the extremes are attained (`FrankWolfe.sepVal_eq_of_extremes`);
* (c): at an exact minimizer the first-order conditions `Wave30tz.Fit.qp_foc_x`, `qp_foc_y` make every linearized decrease
  `≤ 0` (`IsFWPoint 0`) and `w`, `v` themselves the extreme points, so `s = ⟪f̂, e⟫ = d`; `D̂ = 0` gives `f̂ = 0` and `s = 0`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr.RouteFW

open StatFormal.Wave30tz StatFormal.FrankWolfe StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.Concentration

section Gap

variable {𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `fwSep` at attained extremes: `s = μ − M`. -/
theorem fwSep_eq {φ : 𝒳 → H} {α : ℝ} {n m : ℕ} {x : Fin n → 𝒳} {y : Fin m → 𝒳} {f : H} {μ M : ℝ}
    (hμ : IsLeast ((fun w' : Fin n → ℝ => ∑ i, w' i * ⟪f, φ (x i)⟫_ℝ) '' {w' | IsCapped α w'}) μ)
    (hM : IsGreatest ((fun v' : Fin m → ℝ => ∑ j, v' j * ⟪f, φ (y j)⟫_ℝ) '' {v' | IsCapped α v'}) M) :
    fwSep φ α x y f = μ - M := by
  unfold fwSep
  rw [hμ.csInf_eq, hM.csSup_eq]

/-- The witness of a pair with `D̂ > 0` has norm `1`. -/
theorem norm_witness {φ : 𝒳 → H} {n m : ℕ} {x : Fin n → 𝒳} {y : Fin m → 𝒳} {w : Fin n → ℝ} {v : Fin m → ℝ}
    (hd : 0 < qpVal φ x y w v) : ‖witness φ x y w v‖ = 1 := by
  have hd' : 0 < ‖wsum φ x w - wsum φ y v‖ := hd
  change ‖‖wsum φ x w - wsum φ y v‖⁻¹ • (wsum φ x w - wsum φ y v)‖ = 1
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hd'.ne']

/-- `Σ w_i f̂(x_i) − Σ v_j f̂(y_j) = D̂` at the pair itself (`D̂ > 0`). -/
theorem sum_witness_sub {φ : 𝒳 → H} {n m : ℕ} {x : Fin n → 𝒳} {y : Fin m → 𝒳} {w : Fin n → ℝ} {v : Fin m → ℝ}
    (hd : 0 < qpVal φ x y w v) :
    ∑ i, w i * ⟪witness φ x y w v, φ (x i)⟫_ℝ - ∑ j, v j * ⟪witness φ x y w v, φ (y j)⟫_ℝ = qpVal φ x y w v := by
  have hd' : 0 < ‖wsum φ x w - wsum φ y v‖ := hd
  rw [← Fit.inner_wsum, ← Fit.inner_wsum, ← inner_sub_right]
  change ⟪‖wsum φ x w - wsum φ y v‖⁻¹ • (wsum φ x w - wsum φ y v), wsum φ x w - wsum φ y v⟫_ℝ =
    ‖wsum φ x w - wsum φ y v‖
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

/-- **T18 (c), first part**: an exact minimizer of `eq:qp` is a Frank–Wolfe point of gap `0` (the first-order conditions). -/
theorem isFWPoint_zero_of_isQPMin {φ : 𝒳 → H} {α : ℝ} {n m : ℕ} {x : Fin n → 𝒳} {y : Fin m → 𝒳} {w : Fin n → ℝ}
    {v : Fin m → ℝ} (hqp : IsQPMin φ α x y w v) : IsFWPoint φ α 0 x y w v := by
  refine ⟨hqp.1, hqp.2.1, fun w' v' hw' hv' => ?_⟩
  have h1 := Fit.qp_foc_x hqp hw'
  have h2 := Fit.qp_foc_y hqp hv'
  set e := wsum φ x w - wsum φ y v
  have e1 : ⟪e, wsum φ x w' - wsum φ x w⟫_ℝ = ⟪e, wsum φ x w'⟫_ℝ - ⟪e, wsum φ x w⟫_ℝ := inner_sub_right _ _ _
  have e2 : ⟪e, wsum φ y v - wsum φ y v'⟫_ℝ = ⟪e, wsum φ y v⟫_ℝ - ⟪e, wsum φ y v'⟫_ℝ := inner_sub_right _ _ _
  have e3 : ⟪e, e⟫_ℝ = ⟪e, wsum φ x w⟫_ℝ - ⟪e, wsum φ y v⟫_ℝ := inner_sub_right _ _ _
  have e4 : ⟪e, wsum φ x w' - wsum φ y v'⟫_ℝ = ⟪e, wsum φ x w'⟫_ℝ - ⟪e, wsum φ y v'⟫_ℝ := inner_sub_right _ _ _
  rw [zero_mul]
  linarith

/-- **T18 (c), second part**: at an exact minimizer `s = D̂` (`w`, `v` are the extreme points by the first-order conditions;
`D̂ = 0` gives `f̂ = 0` and `s = 0 − 0`). -/
theorem fwSep_eq_qpVal_of_isQPMin {φ : 𝒳 → H} {α : ℝ} {n m : ℕ} {x : Fin n → 𝒳} {y : Fin m → 𝒳} {w : Fin n → ℝ}
    {v : Fin m → ℝ} (hqp : IsQPMin φ α x y w v) : fwSep φ α x y (witness φ x y w v) = qpVal φ x y w v := by
  rcases (norm_nonneg (wsum φ x w - wsum φ y v)).eq_or_lt with h0 | hpos
  · have hq : qpVal φ x y w v = 0 := h0.symm
    have hw0 : witness φ x y w v = 0 := by unfold witness; rw [hq, inv_zero, zero_smul]
    have hμ : IsLeast ((fun w' : Fin n → ℝ => ∑ i, w' i * ⟪(0 : H), φ (x i)⟫_ℝ) '' {w' | IsCapped α w'}) 0 :=
      ⟨⟨w, hqp.1, by simp⟩, by rintro _ ⟨u, -, rfl⟩; simp⟩
    have hM : IsGreatest ((fun v' : Fin m → ℝ => ∑ j, v' j * ⟪(0 : H), φ (y j)⟫_ℝ) '' {v' | IsCapped α v'}) 0 :=
      ⟨⟨v, hqp.2.1, by simp⟩, by rintro _ ⟨u, -, rfl⟩; simp⟩
    rw [hw0, fwSep_eq hμ hM, hq, sub_zero]
  · have hd : 0 < qpVal φ x y w v := hpos
    set f := witness φ x y w v with hfdef
    have hinner : ∀ c : H, ⟪f, c⟫_ℝ = (qpVal φ x y w v)⁻¹ * ⟪wsum φ x w - wsum φ y v, c⟫_ℝ := fun c => by
      rw [hfdef]; unfold witness; rw [real_inner_smul_left]
    have hμ : IsLeast ((fun w' : Fin n → ℝ => ∑ i, w' i * ⟪f, φ (x i)⟫_ℝ) '' {w' | IsCapped α w'})
        (∑ i, w i * ⟪f, φ (x i)⟫_ℝ) := by
      refine ⟨⟨w, hqp.1, rfl⟩, ?_⟩
      rintro _ ⟨w', hw', rfl⟩
      have h0 := Fit.qp_foc_x hqp hw'
      have h2 : 0 ≤ ⟪f, wsum φ x w' - wsum φ x w⟫_ℝ := by
        rw [hinner]; exact mul_nonneg (inv_nonneg.2 hd.le) h0
      rw [inner_sub_right, Fit.inner_wsum, Fit.inner_wsum] at h2
      change ∑ i, w i * ⟪f, φ (x i)⟫_ℝ ≤ ∑ i, w' i * ⟪f, φ (x i)⟫_ℝ
      linarith
    have hM : IsGreatest ((fun v' : Fin m → ℝ => ∑ j, v' j * ⟪f, φ (y j)⟫_ℝ) '' {v' | IsCapped α v'})
        (∑ j, v j * ⟪f, φ (y j)⟫_ℝ) := by
      refine ⟨⟨v, hqp.2.1, rfl⟩, ?_⟩
      rintro _ ⟨v', hv', rfl⟩
      have h0 := Fit.qp_foc_y hqp hv'
      have h2 : 0 ≤ ⟪f, wsum φ y v - wsum φ y v'⟫_ℝ := by
        rw [hinner]; exact mul_nonneg (inv_nonneg.2 hd.le) h0
      rw [inner_sub_right, Fit.inner_wsum, Fit.inner_wsum] at h2
      change ∑ j, v' j * ⟪f, φ (y j)⟫_ℝ ≤ ∑ j, v j * ⟪f, φ (y j)⟫_ℝ
      linarith
    rw [fwSep_eq hμ hM]
    exact sum_witness_sub hd

/-- At a capped pair with `D̂ > 0`: the attained extremes of the witness values, and their transfer to the images of the
capped simplices under `wsum` read through `⟪f̂, ·⟫` (the form of `FrankWolfe.isGreatest_fwGap`). -/
theorem exists_extremes {φ : 𝒳 → H} {α : ℝ} {n m : ℕ} {x : Fin n → 𝒳} {y : Fin m → 𝒳} {w : Fin n → ℝ}
    {v : Fin m → ℝ} (hw : IsCapped α w) (hv : IsCapped α v) :
    ∃ μ M : ℝ,
      IsLeast ((fun w' : Fin n → ℝ => ∑ i, w' i * ⟪witness φ x y w v, φ (x i)⟫_ℝ) '' {w' | IsCapped α w'}) μ ∧
      IsGreatest ((fun v' : Fin m → ℝ => ∑ j, v' j * ⟪witness φ x y w v, φ (y j)⟫_ℝ) '' {v' | IsCapped α v'}) M ∧
      IsLeast ((fun w' : Fin n → ℝ => ⟪‖wsum φ x w - wsum φ y v‖⁻¹ • (wsum φ x w - wsum φ y v), wsum φ x w'⟫_ℝ) ''
        {w' | IsCapped α w'}) μ ∧
      IsGreatest ((fun v' : Fin m → ℝ => ⟪‖wsum φ x w - wsum φ y v‖⁻¹ • (wsum φ x w - wsum φ y v), wsum φ y v'⟫_ℝ) ''
        {v' | IsCapped α v'}) M := by
  obtain ⟨w₀, -, hμ⟩ := exists_isLeast_capped hw (fun i => ⟪witness φ x y w v, φ (x i)⟫_ℝ)
  obtain ⟨v₀, -, hM⟩ := exists_isGreatest_capped hv (fun j => ⟪witness φ x y w v, φ (y j)⟫_ℝ)
  refine ⟨_, _, hμ, hM, ?_, ?_⟩
  · have := image_inner_wsum φ x (witness φ x y w v) {w' | IsCapped α w'}
    change IsLeast ((fun w' : Fin n → ℝ => ⟪witness φ x y w v, wsum φ x w'⟫_ℝ) '' {w' | IsCapped α w'}) _
    rw [this]; exact hμ
  · have := image_inner_wsum φ y (witness φ x y w v) {v' | IsCapped α v'}
    change IsGreatest ((fun v' : Fin m → ℝ => ⟪witness φ x y w v, wsum φ y v'⟫_ℝ) '' {v' | IsCapped α v'}) _
    rw [this]; exact hM

end Gap

/-- **T18 (a), (b)**: the Frank–Wolfe gap identity, the criterion, `s ≤ D̂_α ≤ d`, and `s = sep(f̂; 𝒞_α(P_n), 𝒞_α(Q_m))`. -/
theorem fw_gap_route : Claims.fw_gap := by
  intro 𝒳 H _ _ _ _ φ α ρ n m x y w v hφ hw hv hd
  have hd' : 0 < ‖wsum φ x w - wsum φ y v‖ := hd
  obtain ⟨μ, M, hμ, hM, hμ', hM'⟩ := exists_extremes (φ := φ) (x := x) (y := y) hw hv
  have hs : fwSep φ α x y (witness φ x y w v) = μ - M := fwSep_eq hμ hM
  have hA := region_empirical_eq_image hφ x hw
  have hB := region_empirical_eq_image hφ y hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]
    exact isGreatest_fwGap hd' hμ' hM'
  · rw [hs]
    exact ⟨fun h => (fwGap_le_iff hd' hμ' hM' ρ).1 h.2.2, fun h => ⟨hw, hv, (fwGap_le_iff hd' hμ' hM' ρ).2 h⟩⟩
  · unfold Demp setDist
    rw [hA, hB, hs]
    refine le_csInf ⟨_, wsum φ x w, ⟨w, hw, rfl⟩, wsum φ y v, ⟨v, hv, rfl⟩, rfl⟩ ?_
    rintro _ ⟨_, ⟨w', hw', rfl⟩, _, ⟨v', hv', rfl⟩, rfl⟩
    have h1 : μ ≤ ∑ i, w' i * ⟪witness φ x y w v, φ (x i)⟫_ℝ := hμ.2 ⟨w', hw', rfl⟩
    have h2 : ∑ j, v' j * ⟪witness φ x y w v, φ (y j)⟫_ℝ ≤ M := hM.2 ⟨v', hv', rfl⟩
    have h3 : ⟪witness φ x y w v, wsum φ x w' - wsum φ y v'⟫_ℝ ≤ ‖wsum φ x w' - wsum φ y v'‖ :=
      (real_inner_le_norm _ _).trans (by rw [norm_witness hd, one_mul])
    rw [inner_sub_right, Fit.inner_wsum, Fit.inner_wsum] at h3
    linarith
  · unfold Demp
    rw [hA, hB]
    exact setDist_le_norm ⟨w, hw, rfl⟩ ⟨v, hv, rfl⟩
  · rw [hA, hB, hs]
    exact sepVal_eq_of_extremes (by rw [image_inner_image_wsum]; exact hμ) (by rw [image_inner_image_wsum]; exact hM)

/-- **T18 (c)**: an exact minimizer is an `IsFWPoint 0` with `s = d`; every `IsWitnessRun` is an `IsWitnessRunFW 0`. -/
theorem fw_exact_route : Claims.fw_exact := by
  refine ⟨fun 𝒳 H _ _ φ α n m x y w v hqp => ⟨isFWPoint_zero_of_isQPMin hqp, fwSep_eq_qpVal_of_isQPMin hqp⟩, ?_⟩
  intro 𝒳 H _ _ _ φ J n m α δ lmax s2 R hR
  obtain ⟨hadm, hwit, hlam⟩ := hR
  refine ⟨hadm, fun j k x y => ?_, hlam⟩
  obtain ⟨h1, h2⟩ := hwit j k x y
  refine ⟨h1, fun hn hm => ?_⟩
  obtain ⟨w, v, hqp, h3, h4⟩ := h2 hn hm
  exact ⟨w, v, isFWPoint_zero_of_isQPMin hqp, h3, h4⟩

end StatFormal.Wave31tr.RouteFW
