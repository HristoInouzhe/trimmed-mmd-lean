import StatFormal.Wave31tu.RouteKLocal

/-!
# Wave 31tu, route K: Y20(b) `lap_local_Q`, Lemma S4.28 for the second sample (untrusted proof material)

The mirror of `lap_local`: `Q_h` moves the mass `hπ′` of `Q` from `A₁` to `B₁` (`π′ = min{Q(A₁), Q(B₁)}`). It is the core of
`RouteKCore` with the roles `f = q`, `g = p`, `A = B₁`, `B = A₁`, `π = π′` (`p ≤ q` a.e. on `B₁`, `q ≤ p` a.e. on `A₁`), read through
the symmetry of `TV` and of `|P − Q|` (`absPQ_comm`); the Le Cam step perturbs the second sample (`lecam_second`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave31tu.RouteK

open StatFormal StatFormal.LocalLower StatFormal.Wave31tq StatFormal.Wave30tp

theorem lap_local_Q_route : Claims.lap_local_Q := by
  intro P Q _ _ p q x₀ ℓ₀ rs cs r C' δ hcross hpx hexp hcond hr hrs hpc hqc hpos A₁ B₁ πq
  obtain ⟨hpm, hqm, hp0, hq0, hP, hQ, ⟨r₀, hr₀, hpc₀, hqc₀⟩, hsR, hsL, hd, hℓ⟩ := hcross
  have hA : MeasurableSet A₁ := measurableSet_Ioo
  have hB : MeasurableSet B₁ := measurableSet_Ioo
  have hBA : Disjoint B₁ A₁ := (disjoint_A₁_B₁ hr).symm
  obtain ⟨hQA, hQB⟩ := real_A₁_B₁_pos hqm hQ hr (fun z hz => (hpos z hz).2)
  have hπ : 0 < πq := lt_min hQA hQB
  have hπB : πq ≤ Q.real B₁ := min_le_right _ _
  have hπA : πq ≤ Q.real A₁ := min_le_left _ _
  refine ⟨hπ, fun hh hh01 => ?_⟩
  intro qh Qh
  obtain ⟨hh0, hh1⟩ := hh01
  -- the signs in the roles of the core: `g = p ≤ f = q` on `B₁`, `f = q ≤ g = p` on `A₁`
  have hsB₁ : ∀ᵐ x ∂volume, x ∈ B₁ → p x ≤ q x := by
    filter_upwards [hsL] with x hx hxB using hx (by linarith [hxB.2])
  have hsA₁ : ∀ᵐ x ∂volume, x ∈ A₁ → q x ≤ p x := by
    filter_upwards [hsR] with x hx hxA using hx (by linarith [hxA.1])
  have hnotA : ∀ x, x < x₀ + r → x ∉ A₁ := fun x hx hxA => by linarith [hxA.1]
  have hnotB : ∀ x, x₀ - r < x → x ∉ B₁ := fun x hx hxB => by linarith [hxB.2]
  have hprob : IsProbabilityMeasure Qh := core_prob hqm hq0 hQ hBA hB hA hπ hπB hπA hh0 hh1
  have htv : Distances.tvDist P Qh = Distances.tvDist P Q + hh * πq := by
    rw [Distances.tvDist_comm, Distances.tvDist_comm P Q]
    exact core_tv hqm hpm hq0 hp0 hQ hP hBA hB hA hπ hπB hπA hh0 hh1 hsB₁ hsA₁
  have hqh0 : ∀ z, 0 ≤ qh z := core_nonneg hBA hq0 hπ hπB hπA hh0 hh1
  have hqhm : Measurable qh := measurable_bump hqm hB hA
  have heq : ∀ x, |x - x₀| < r → qh x = q x := fun x hx => by
    rw [abs_lt] at hx
    exact core_eq_off (hnotB x (by linarith)) (hnotA x (by linarith))
  have hexp' : ExpTailWith Q P x₀ C' := ⟨hexp.1, fun t ht => by rw [absPQ_comm]; exact hexp.2 t ht⟩
  have htail := core_tail hqm hpm hq0 hp0 hQ hP hBA hB hA hπ hπB hπA hh0 hh1 hr (fun x hx => abs_lt_of_mem_B₁ hr hx)
    (fun x hx => abs_lt_of_mem_A₁ hr hx) hexp'
  refine ⟨hqh0, core_set hqm hq0 hQ hBA hB hA hπ hπB hπA hh0 hh1, hprob, htv,
    core_tv_self hqm hq0 hQ hBA hB hA hπ hπB hπA hh0 hh1, ?_,
    ⟨htail.1, fun t ht => by rw [absPQ_comm]; exact htail.2 t ht⟩, ?_, ?_, ?_⟩
  · -- `IsCross P Q_h p q_h x₀ ℓ₀`
    refine ⟨hpm, hqhm, hp0, hqh0, hP, rfl, ⟨min r₀ r, lt_min hr₀ hr, ?_, ?_⟩, ?_, ?_, ?_, hℓ⟩
    · exact hpc₀.mono (Ioo_subset_Ioo (by linarith [min_le_left r₀ r]) (by linarith [min_le_left r₀ r]))
    · refine (hqc₀.mono (Ioo_subset_Ioo (by linarith [min_le_left r₀ r]) (by linarith [min_le_left r₀ r]))).congr ?_
      intro x hx
      exact heq x (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2, min_le_right r₀ r])
    · filter_upwards [hsR] with x hx hxpos
      exact (core_le_off hBA hq0 hπ hπB hπA hh0 hh1 (hnotB x (by linarith))).trans (hx hxpos)
    · filter_upwards [hsL] with x hx hxneg
      exact (hx hxneg).trans (core_ge_off hBA hq0 hπ hπB hπA hh0 hh1 (hnotA x (by linarith)))
    · refine hd.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds (show x₀ - r < x₀ by linarith) (show x₀ < x₀ + r by linarith)] with x hx
      have : |x - x₀| < r := by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
      simp only [heq x this]
  · -- `(5.1)` with `c⋆/2`
    obtain ⟨hrs0, hrs1, hcs, hc⟩ := hcond
    have hc' : ∀ᵐ x ∂volume, cs * min rs |x - x₀| * (q x + p x) ≤ |q x - p x| := by
      filter_upwards [hc] with x hx
      rwa [add_comm (q x), abs_sub_comm (q x)]
    have h := core_condR hq0 hp0 hBA hπ hπB hπA hh0 hh1 hsB₁ hsA₁ (w := fun x => min rs |x - x₀|) hcs.le
      (fun x => le_min hrs0.le (abs_nonneg _)) hc'
    refine ⟨hrs0, hrs1, half_pos hcs, ?_⟩
    filter_upwards [h] with x hx
    change cs / 2 * min rs |x - x₀| * (p x + qh x) ≤ |p x - qh x|
    rw [add_comm (p x), abs_sub_comm (p x)]
    exact hx
  · -- `2p̄`
    intro pbar hpbar z hz
    have h1 := core_le_two hBA hq0 hπ hπB hπA hh0 hh1 z
    have h2 := hpbar z hz
    have h3 := hp0 z
    change p z + qh z ≤ 2 * pbar
    linarith
  · -- Le Cam, the second sample
    intro n m Ξ _ ρ _ T hT hval
    have := sampleLaw_isProb P Qh n m
    have h1 := lecam_second ρ hT hval (core_pi hqm hq0 hQ hBA hB hA hπ hπB hπA hh0 hh1 m)
    refine h1.trans (measureReal_mono fun z hz => ?_)
    simp only [mem_ofPred_eq] at hz ⊢
    rw [htv]
    linarith

end StatFormal.Wave31tu.RouteK
