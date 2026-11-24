import StatFormal.Wave31tu.RouteKCore

/-!
# Wave 31tu, route K: Y20(a) `lap_local`, Lemma S4.28 for the first sample (untrusted proof material)

`P_h` moves the mass `hπ` of `P` from `B₁ = (x₀ − 2r, x₀ − r)` to `A₁ = (x₀ + r, x₀ + 2r)` (`π = min{P(A₁), P(B₁)} > 0`, as `p > 0`
on `[x₀ − 2r, x₀ + 2r]`). By the a.e. signs of `IsCross`, `q ≤ p` on `A₁` and `p ≤ q` on `B₁`, so `TV(P_h, Q) = α⋆ + hπ`
(`core_tv`); `P_h = P` near `x₀`, so continuity, the signs and the derivative at `x₀` are kept; `(5.1)` holds with `c⋆/2`
(`core_condR`), `p_h ≤ 2p` gives `2p̄`, the tail constant is `C′ + 2r + 2e` (`core_tail`), and Le Cam's step with
`TV(P_h^n, P^n) ≤ h√(nπ)` (`core_pi`, `lecam_first`) gives the probability bound: on `{T ≤ α⋆}` the error at `(P_h, Q)` is at least
`hπ`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave31tu.RouteK

open StatFormal StatFormal.LocalLower StatFormal.Wave31tq StatFormal.Wave30tp

/-- `0 < P(A₁)` and `0 < P(B₁)` for a density positive on `[x₀ − 2r, x₀ + 2r]`. -/
theorem real_A₁_B₁_pos {P : Measure ℝ} [IsProbabilityMeasure P] {p : ℝ → ℝ} (hpm : Measurable p)
    (hP : P = volume.withDensity fun x => ENNReal.ofReal (p x)) {x₀ r : ℝ} (hr : 0 < r)
    (hpos : ∀ z ∈ Icc (x₀ - 2 * r) (x₀ + 2 * r), 0 < p z) :
    0 < P.real (Ioo (x₀ + r) (x₀ + 2 * r)) ∧ 0 < P.real (Ioo (x₀ - 2 * r) (x₀ - r)) := by
  constructor
  · refine real_pos_of_density hpm hP measurableSet_Ioo (fun x hx => hpos x ⟨by linarith [hx.1], hx.2.le⟩) ?_
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.2 (by linarith)
  · refine real_pos_of_density hpm hP measurableSet_Ioo (fun x hx => hpos x ⟨hx.1.le, by linarith [hx.2]⟩) ?_
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.2 (by linarith)

theorem lap_local_route : Claims.lap_local := by
  intro P Q _ _ p q x₀ ℓ₀ rs cs r C' δ hcross hpx hexp hcond hr hrs hpc hqc hpos A₁ B₁ πh
  obtain ⟨hpm, hqm, hp0, hq0, hP, hQ, ⟨r₀, hr₀, hpc₀, hqc₀⟩, hsR, hsL, hd, hℓ⟩ := hcross
  have hA : MeasurableSet A₁ := measurableSet_Ioo
  have hB : MeasurableSet B₁ := measurableSet_Ioo
  have hAB : Disjoint A₁ B₁ := disjoint_A₁_B₁ hr
  obtain ⟨hPA, hPB⟩ := real_A₁_B₁_pos hpm hP hr (fun z hz => (hpos z hz).1)
  have hπ : 0 < πh := lt_min hPA hPB
  have hπA : πh ≤ P.real A₁ := min_le_left _ _
  have hπB : πh ≤ P.real B₁ := min_le_right _ _
  refine ⟨hπ, fun hh hh01 => ?_⟩
  intro ph Ph
  obtain ⟨hh0, hh1⟩ := hh01
  have hsA : ∀ᵐ x ∂volume, x ∈ A₁ → q x ≤ p x := by
    filter_upwards [hsR] with x hx hxA using hx (by linarith [hxA.1])
  have hsB : ∀ᵐ x ∂volume, x ∈ B₁ → p x ≤ q x := by
    filter_upwards [hsL] with x hx hxB using hx (by linarith [hxB.2])
  have hnotA : ∀ x, x < x₀ + r → x ∉ A₁ := fun x hx hxA => by linarith [hxA.1]
  have hnotB : ∀ x, x₀ - r < x → x ∉ B₁ := fun x hx hxB => by linarith [hxB.2]
  have hprob : IsProbabilityMeasure Ph := core_prob hpm hp0 hP hAB hA hB hπ hπA hπB hh0 hh1
  have htv : Distances.tvDist Ph Q = Distances.tvDist P Q + hh * πh :=
    core_tv hpm hqm hp0 hq0 hP hQ hAB hA hB hπ hπA hπB hh0 hh1 hsA hsB
  have hph0 : ∀ z, 0 ≤ ph z := core_nonneg hAB hp0 hπ hπA hπB hh0 hh1
  have hphm : Measurable ph := measurable_bump hpm hA hB
  have heq : ∀ x, |x - x₀| < r → ph x = p x := fun x hx => by
    rw [abs_lt] at hx
    exact core_eq_off (hnotA x (by linarith)) (hnotB x (by linarith))
  refine ⟨hph0, core_set hpm hp0 hP hAB hA hB hπ hπA hπB hh0 hh1, hprob, htv,
    core_tv_self hpm hp0 hP hAB hA hB hπ hπA hπB hh0 hh1, ?_, ?_,
    core_tail hpm hqm hp0 hq0 hP hQ hAB hA hB hπ hπA hπB hh0 hh1 hr (fun x hx => abs_lt_of_mem_A₁ hr hx)
      (fun x hx => abs_lt_of_mem_B₁ hr hx) hexp, ?_, ?_, ?_⟩
  · -- `IsCross P_h Q p_h q x₀ ℓ₀`
    refine ⟨hphm, hqm, hph0, hq0, rfl, hQ, ⟨min r₀ r, lt_min hr₀ hr, ?_, ?_⟩, ?_, ?_, ?_, hℓ⟩
    · refine (hpc₀.mono (Ioo_subset_Ioo (by linarith [min_le_left r₀ r]) (by linarith [min_le_left r₀ r]))).congr ?_
      intro x hx
      exact heq x (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2, min_le_right r₀ r])
    · exact hqc₀.mono (Ioo_subset_Ioo (by linarith [min_le_left r₀ r]) (by linarith [min_le_left r₀ r]))
    · filter_upwards [hsR] with x hx hxpos
      exact (hx hxpos).trans (core_ge_off hAB hp0 hπ hπA hπB hh0 hh1 (hnotB x (by linarith)))
    · filter_upwards [hsL] with x hx hxneg
      exact (core_le_off hAB hp0 hπ hπA hπB hh0 hh1 (hnotA x (by linarith))).trans (hx hxneg)
    · refine hd.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds (show x₀ - r < x₀ by linarith) (show x₀ < x₀ + r by linarith)] with x hx
      have : |x - x₀| < r := by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
      simp only [heq x this]
  · -- `0 < p_h(x₀)`
    rw [heq x₀ (by simpa using hr)]; exact hpx
  · -- `(5.1)` with `c⋆/2`
    obtain ⟨hrs0, hrs1, hcs, hc⟩ := hcond
    exact ⟨hrs0, hrs1, half_pos hcs, core_condR hp0 hq0 hAB hπ hπA hπB hh0 hh1 hsA hsB (w := fun x => min rs |x - x₀|)
      hcs.le (fun x => le_min hrs0.le (abs_nonneg _)) hc⟩
  · -- `2p̄`
    intro pbar hpbar z hz
    have h1 := core_le_two hAB hp0 hπ hπA hπB hh0 hh1 z
    have h2 := hpbar z hz
    have h3 := hq0 z
    change ph z + q z ≤ 2 * pbar
    linarith
  · -- Le Cam
    intro n m Ξ _ ρ _ T hT hval
    have := sampleLaw_isProb Ph Q n m
    have h1 := lecam_first ρ hT hval (core_pi hpm hp0 hP hAB hA hB hπ hπA hπB hh0 hh1 n)
    refine h1.trans (measureReal_mono fun z hz => ?_)
    simp only [mem_ofPred_eq] at hz ⊢
    rw [htv]
    linarith

end StatFormal.Wave31tu.RouteK
