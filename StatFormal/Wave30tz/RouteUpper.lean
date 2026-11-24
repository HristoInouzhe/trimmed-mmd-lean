import StatFormal.Wave30tz.RouteBet
import StatFormal.Wave30tv.Proofs

/-!
# Wave 30tz route: Proposition 1 (1), the upper side — untrusted

* `alphaLo_measurable`: `α̂_lo` is a function `F` of the finitely many rejection indicators,
  `F : (Fin J → Bool) → ℝ` is measurable (countable discrete domain), each rejection event is
  measurable (Wave 30tv `measurableSet_seqReject` with `U = Unit`, transported along `ω ↦ ((), ω)`);
* `gridBelow_event_subset`: by `grid_events_route` (part (a)), `{α_{j*} < α̂_lo}` lies inside the
  rejection event of the first level `α_{i₀} ≥ a` (which depends on `a` only), and is empty if
  there is no level `≥ a`;
* `reject_le_delta`: the level of a single test, the certified `Wave30tv.thm_betting` with
  `U = Unit`, `ν = δ_()` (the product with a Dirac mass on `Unit` is the measure itself);
* `lo_upper_route`: the three conjuncts (the third through `α_{j*} < a` for `a > 0`);
* `lo_strict_bound_route`: `strict_null_frac_route` (RouteBet) at the first level `α_{i₀} ≥ TV`
  with `ζ' = α_{i₀} − TV ≥ ζ`, then monotonicity in `ζ'` and `1 + α_{i₀} ≥ 1`.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.Wave30tz

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tp

namespace Upper

/-- `alphaLo` of measurable rejection events is measurable. -/
lemma alphaLo_measurable {Ω : Type*} [MeasurableSpace Ω] {J : ℕ} (α : Fin J → ℝ) (rej : Fin J → Ω → Prop)
    (hrej : ∀ j, MeasurableSet {ω | rej j ω}) :
    Measurable fun ω => StatFormal.TrimmedMMD.Lower.alphaLo α (fun j => rej j ω) := by
  classical
  have hF : Measurable fun b : Fin J → Bool => StatFormal.TrimmedMMD.Lower.alphaLo α (fun j => b j = true) :=
    measurable_of_countable _
  have hb : Measurable fun ω => fun j => decide (rej j ω) := by
    refine Measurable.of_eval fun j => measurable_to_bool ?_
    convert hrej j using 1
    ext ω
    simp
  have e : (fun ω => StatFormal.TrimmedMMD.Lower.alphaLo α (fun j => rej j ω)) =
      (fun b : Fin J → Bool => StatFormal.TrimmedMMD.Lower.alphaLo α (fun j => b j = true)) ∘
        (fun ω => fun j => decide (rej j ω)) := by
    funext ω
    simp only [Function.comp_apply, decide_eq_true_eq]
  rw [e]
  exact hF.comp hb

/-- `α_{j*} < a` when `a > 0`. -/
lemma gridBelow_lt {J : ℕ} (α : Fin J → ℝ) {a : ℝ} (ha : 0 < a) : gridBelow α a < a := by
  classical
  unfold gridBelow
  split_ifs with h
  · rw [Finset.sup'_lt_iff]
    intro j hj
    exact (Finset.mem_filter.1 hj).2
  · exact ha

/-- The event `{α_{j*} < α̂_lo}` is inside the rejection event of the first level `α_{i₀} ≥ a`. -/
lemma gridBelow_event_subset {Ω : Type*} {J : ℕ} (α : Fin J → ℝ) (hgrid : IsGrid α) (rej : Fin J → Ω → Prop) (a : ℝ)
    (i₀ : Fin J) (hi₀ : a ≤ α i₀) (hbelow : ∀ i < i₀, α i < a) :
    {ω | gridBelow α a < StatFormal.TrimmedMMD.Lower.alphaLo α (fun j => rej j ω)} ⊆ {ω | rej i₀ ω} := by
  intro ω hω
  obtain ⟨i₁, hi₁, hbelow₁, hrej⟩ := (grid_events_route J α (fun j => rej j ω) a hgrid).1 hω
  have e : i₁ = i₀ := by
    rcases lt_trichotomy i₁ i₀ with h | h | h
    · exact absurd (hbelow i₁ h) (not_lt.2 hi₁)
    · exact h
    · exact absurd (hbelow₁ i₀ h) (not_lt.2 hi₀)
  rw [e] at hrej
  exact hrej

/-- With no level `≥ a`, the event `{α_{j*} < α̂_lo}` is empty. -/
lemma gridBelow_event_empty {Ω : Type*} {J : ℕ} (α : Fin J → ℝ) (hgrid : IsGrid α) (rej : Fin J → Ω → Prop) (a : ℝ)
    (hno : ¬ ∃ i₀, a ≤ α i₀ ∧ ∀ i < i₀, α i < a) :
    {ω | gridBelow α a < StatFormal.TrimmedMMD.Lower.alphaLo α (fun j => rej j ω)} = ∅ := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hω
  obtain ⟨i₁, hi₁, hbelow₁, _⟩ := (grid_events_route J α (fun j => rej j ω) a hgrid).1 hω
  exact hno ⟨i₁, hi₁, hbelow₁⟩

variable {𝒳 : Type} [MeasurableSpace 𝒳] {n m N : ℕ}

/-- The rejection event of `rejects` is measurable. -/
lemma measurableSet_rejects {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)}
    {B : Fin N → Finset (Fin m)} {g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ}
    {lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ} {α δ c : ℝ}
    (hg : IsFitRule lx ly bat g) (hlam : IsFracRule lx ly bat α c lam) :
    MeasurableSet {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | rejects lam g bat A B α δ ω.1 ω.2} := by
  have hS := measurableSet_seqReject (A := A) (B := B) (δ := δ) hg hlam
  have hmk : Measurable fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => (((), ω) : Unit × ((Fin n → 𝒳) × (Fin m → 𝒳))) :=
    measurable_const.prodMk measurable_id
  exact hmk hS

/-- The level of one test (`thm:betting`, `U = Unit`). -/
lemma reject_le_delta (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)}
    {B : Fin N → Finset (Fin m)} {g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ}
    {lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ} {α δ c : ℝ}
    (hpair : IsBatchPairing lx ly bat A B) (hα : 0 ≤ α) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hg : IsFitRule lx ly bat g) (hlam : IsFracRule lx ly bat α c lam)
    (hTV : StatFormal.Distances.tvDist P Q ≤ α) :
    sampleLaw P Q n m {ω | rejects lam g bat A B α δ ω.1 ω.2} ≤ ENNReal.ofReal δ := by
  have h := StatFormal.Wave30tv.thm_betting 𝒳 Unit P Q (Measure.dirac ()) n m N lx ly bat A B α δ c
    (fun b _ => g b) (fun k _ => lam k) hpair hα hδ0 hδ1 hc0 hc1 hg hlam hTV
  have e : {ω : Unit × ((Fin n → 𝒳) × (Fin m → 𝒳)) |
      seqReject (fun k _ => lam k) (fun b _ => g b) bat A B α δ ω.1 ω.2.1 ω.2.2} =
      (univ : Set Unit) ×ˢ {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | rejects lam g bat A B α δ ω.1 ω.2} := by
    ext ⟨u, ω⟩
    cases u
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and]
    rfl
  rw [e, Measure.prod_prod, measure_univ, one_mul] at h
  exact h

end Upper

open Upper

/-- **Proposition 1 (1), upper side** (every `n, m`). -/
theorem lo_upper_route : Claims.lo_upper := by
  intro 𝒳 _ P Q _ _ J n m α δ lmax R hgrid hδ0 hδ1 hl0 hl1 hadm
  obtain ⟨hpair, hfit, hfrac⟩ := hadm
  have hS : ∀ j, MeasurableSet {ω : (Fin n → 𝒳) × (Fin m → 𝒳) |
      rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2} :=
    fun j => measurableSet_rejects (A := R.A) (B := R.B) (δ := δ) (hfit j) (hfrac j)
  have hmeas : Measurable fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => R.alphaLo α δ ω.1 ω.2 :=
    alphaLo_measurable α
      (fun j (ω : (Fin n → 𝒳) × (Fin m → 𝒳)) => rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2) hS
  set TV := StatFormal.Distances.tvDist P Q with hTVdef
  have hmain : sampleLaw P Q n m {ω | gridBelow α TV < R.alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal δ := by
    by_cases hex : ∃ i₀, TV ≤ α i₀ ∧ ∀ i < i₀, α i < TV
    · obtain ⟨i₀, hi₀, hbelow⟩ := hex
      calc sampleLaw P Q n m {ω | gridBelow α TV < R.alphaLo α δ ω.1 ω.2}
          ≤ sampleLaw P Q n m {ω | rejects (R.lam i₀) (R.g i₀) R.bat R.A R.B (α i₀) δ ω.1 ω.2} :=
            measure_mono (gridBelow_event_subset α hgrid
              (fun j (ω : (Fin n → 𝒳) × (Fin m → 𝒳)) => rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2)
              TV i₀ hi₀ hbelow)
        _ ≤ ENNReal.ofReal δ :=
            reject_le_delta P Q hpair (hgrid.2 i₀).1 hδ0 hδ1 hl0 hl1 (hfit i₀) (hfrac i₀) hi₀
    · have h0 := gridBelow_event_empty α hgrid
        (fun j (ω : (Fin n → 𝒳) × (Fin m → 𝒳)) => rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2) TV hex
      change sampleLaw P Q n m {ω | gridBelow α TV < StatFormal.TrimmedMMD.Lower.alphaLo α
        (fun j => rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2)} ≤ ENNReal.ofReal δ
      rw [h0, measure_empty]
      exact zero_le
  refine ⟨hmeas, hmain, fun _ hTV0 => ?_⟩
  refine le_trans (measure_mono ?_) hmain
  intro ω hω
  exact lt_of_lt_of_le (gridBelow_lt α hTV0) hω

/-- **Proposition 1 (1), upper side, the explicit strict-null bound of §5.** -/
theorem lo_strict_bound_route : Claims.lo_strict_bound := by
  intro 𝒳 _ P Q _ _ J n m α δ lmax s2 ζ R hgrid hδ0 hδ1 hl0 hl1 hs2 hadm hhi hζ hgap
  obtain ⟨hpair, hfit, hfrac⟩ := hadm
  set TV := StatFormal.Distances.tvDist P Q with hTVdef
  set L := Real.log (1 / δ) with hLdef
  by_cases hex : ∃ i₀, TV ≤ α i₀ ∧ ∀ i < i₀, α i < TV
  · obtain ⟨i₀, hi₀, hbelow⟩ := hex
    have hsub := gridBelow_event_subset α hgrid
      (fun j (ω : (Fin n → 𝒳) × (Fin m → 𝒳)) => rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2)
      TV i₀ hi₀ hbelow
    have hα0 : 0 ≤ α i₀ := (hgrid.2 i₀).1
    have hζ' : ζ ≤ α i₀ - TV := by linarith [hgap i₀ hi₀]
    have hζ'0 : 0 < α i₀ - TV := lt_of_lt_of_le hζ hζ'
    have hsn := strict_null_frac_route 𝒳 P Q n m R.N R.lx R.ly R.bat R.A R.B (α i₀) δ lmax s2 (α i₀ - TV)
      (R.g i₀) (R.lam i₀) hpair hα0 hδ0 hδ1 hl0 hl1 hs2 (hfit i₀) (hfrac i₀) (hhi i₀) hζ'0 (by linarith)
    obtain ⟨_, h2, h3, _⟩ := hsn
    refine ⟨?_, ?_⟩
    · refine (measure_mono hsub).trans (h2.trans (ENNReal.ofReal_le_ofReal ?_))
      apply Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le
      rw [div_div_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hl0.le
      nlinarith
    · refine (measure_mono hsub).trans (h3.trans (ENNReal.ofReal_le_ofReal ?_))
      apply Real.exp_le_exp.2
      apply neg_le_neg
      have : 0 ≤ √s2 * √(2 * R.N * L) := by positivity
      nlinarith
  · have h0 := gridBelow_event_empty α hgrid
      (fun j (ω : (Fin n → 𝒳) × (Fin m → 𝒳)) => rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2) TV hex
    change sampleLaw P Q n m {ω | gridBelow α TV < StatFormal.TrimmedMMD.Lower.alphaLo α
      (fun j => rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2)} ≤ _ ∧
      sampleLaw P Q n m {ω | gridBelow α TV < StatFormal.TrimmedMMD.Lower.alphaLo α
      (fun j => rejects (R.lam j) (R.g j) R.bat R.A R.B (α j) δ ω.1 ω.2)} ≤ _
    rw [h0, measure_empty]
    exact ⟨zero_le, zero_le⟩

example : Claims.lo_upper := lo_upper_route
example : Claims.lo_strict_bound := lo_strict_bound_route

end StatFormal.Wave30tz
