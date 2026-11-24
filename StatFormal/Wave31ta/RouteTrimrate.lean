import StatFormal.Wave31ta.Statements
import StatFormal.Wave30tx.Proofs
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Route (untrusted): `quantile_of_QDensity` and `cor_trimrate_v2` (wave 31ta)

* `quantile_of_QDensity`: a `p`-quantile `t` at which the law of `f` has a density bounded below by `c > 0` on `[t − ρ, t + ρ]` is the
  least element of `{s : p ≤ P(f ≤ s)}`: for `s < t`, `P(f ≤ s) ≤ P(f < t) − P(max(s, t−ρ) < f < t) < p`.
* `cor_trimrate_v2`: the frozen `Wave30tx.cor_trimrate` at the best constants. Two density versions on the window agree a.e., so every
  admissible lower (upper) constant is an a.e. lower (upper) bound of one fixed version `g₀`; the supremum `c*` (infimum `C*`) of the
  admissible constants is again an a.e. bound (rational approximation), and the clamped version `max c* (min C* g₀)` makes
  `(c*, C*)` admissible. Every bound of the conclusion is monotone in the constants, so the `N` of `cor_trimrate` at the best constants
  serves every admissible tuple.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31ta.RTrim

open StatFormal.Wave12c

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The core of `quantile_of_QDensity`: below a quantile with a positive density on its left, the distribution function is `< p`. -/
theorem cdf_lt_of_lt {P : Measure 𝒳} [IsProbabilityMeasure P] {f : 𝒳 → ℝ} {p t ρ c : ℝ} (hf : Measurable f)
    (hρ : 0 < ρ) (hc : 0 < c) (hq : StatFormal.Wave30tx.IsQuantile P f p t) (hd : QDensityLower P f t ρ c)
    {s : ℝ} (hs : s < t) : P.real {x | f x ≤ s} < p := by
  obtain ⟨g, hg, hgc, hrep⟩ := hd
  set a := max s (t - ρ) with ha
  have hat : a < t := max_lt hs (by linarith)
  have hsub : Ioo a t ⊆ Icc (t - ρ) (t + ρ) := fun r hr =>
    ⟨(le_max_right _ _).trans hr.1.le, by linarith [hr.2]⟩
  have hA : P (f ⁻¹' Ioo a t) = ∫⁻ r in Ioo a t, ENNReal.ofReal (g r) := hrep _ measurableSet_Ioo hsub
  have hlow : ENNReal.ofReal (c * (t - a)) ≤ P (f ⁻¹' Ioo a t) := by
    rw [hA]
    calc ENNReal.ofReal (c * (t - a)) = ∫⁻ _r in Ioo a t, ENNReal.ofReal c := by
          rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul hc.le]
      _ ≤ ∫⁻ r in Ioo a t, ENNReal.ofReal (g r) :=
          setLIntegral_mono (hg.ennreal_ofReal) fun r hr => ENNReal.ofReal_le_ofReal (hgc r (hsub hr))
  have hlowr : c * (t - a) ≤ P.real (f ⁻¹' Ioo a t) := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hlow
  have hpos : 0 < c * (t - a) := mul_pos hc (by linarith)
  have hdisj : Disjoint {x | f x ≤ s} (f ⁻¹' Ioo a t) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : a < f x := hx'.1
    have h2 : s ≤ a := le_max_left _ _
    have h3 : f x ≤ s := hx
    linarith
  have hunion : {x | f x ≤ s} ∪ f ⁻¹' Ioo a t ⊆ {x | f x < t} := by
    rintro x (hx | hx)
    · exact lt_of_le_of_lt (hx : f x ≤ s) hs
    · exact hx.2
  have h1 := measureReal_union (μ := P) hdisj (hf measurableSet_Ioo) (measure_ne_top _ _) (measure_ne_top _ _)
  have h2 := measureReal_mono (μ := P) hunion (measure_ne_top _ _)
  linarith [hq.1]

theorem quantile_eq {P : Measure 𝒳} [IsProbabilityMeasure P] {f : 𝒳 → ℝ} {p t ρ c : ℝ} (hf : Measurable f)
    (hρ : 0 < ρ) (hc : 0 < c) (hq : StatFormal.Wave30tx.IsQuantile P f p t) (hd : QDensityLower P f t ρ c) :
    quantileAt P f p = t := by
  refine IsLeast.csInf_eq ⟨hq.2, fun s hs => ?_⟩
  by_contra h
  push Not at h
  exact absurd (hs : p ≤ P.real {x | f x ≤ s}) (not_le.2 (cdf_lt_of_lt hf hρ hc hq hd h))

/-- Two density versions of the law of `f` on a measurable window agree a.e. (after `ofReal`) on the window. -/
theorem ae_ofReal_eq {P : Measure 𝒳} {f : 𝒳 → ℝ} {W : Set ℝ} (hW : MeasurableSet W) {g h : ℝ → ℝ}
    (hg : Measurable g) (hh : Measurable h)
    (hrg : ∀ A : Set ℝ, MeasurableSet A → A ⊆ W → P (f ⁻¹' A) = ∫⁻ s in A, ENNReal.ofReal (g s))
    (hrh : ∀ A : Set ℝ, MeasurableSet A → A ⊆ W → P (f ⁻¹' A) = ∫⁻ s in A, ENNReal.ofReal (h s)) :
    ∀ᵐ s ∂(volume.restrict W), ENNReal.ofReal (g s) = ENNReal.ofReal (h s) := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hg.ennreal_ofReal hh.ennreal_ofReal fun A hA _ => ?_
  rw [Measure.restrict_restrict hA, ← hrg _ (hA.inter hW) inter_subset_right,
    ← hrh _ (hA.inter hW) inter_subset_right]

/-- An admissible lower constant of one version is an a.e. lower bound of any other version. -/
theorem ae_lower {W : Set ℝ} (hW : MeasurableSet W) {g g0 : ℝ → ℝ}
    (heq : ∀ᵐ s ∂(volume.restrict W), ENNReal.ofReal (g s) = ENNReal.ofReal (g0 s)) {c : ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ W, c ≤ g s) : ∀ᵐ s ∂(volume.restrict W), c ≤ g0 s := by
  filter_upwards [heq, ae_restrict_mem hW] with s h1 h2
  have h3 := ENNReal.ofReal_le_ofReal (hg s h2)
  rw [h1] at h3
  rcases ENNReal.ofReal_le_ofReal_iff'.1 h3 with h | h
  · exact h
  · linarith

/-- An admissible upper constant of one version is an a.e. upper bound of any other version. -/
theorem ae_upper {W : Set ℝ} (hW : MeasurableSet W) {g g0 : ℝ → ℝ}
    (heq : ∀ᵐ s ∂(volume.restrict W), ENNReal.ofReal (g s) = ENNReal.ofReal (g0 s)) {c C : ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ W, c ≤ g s ∧ g s ≤ C) : ∀ᵐ s ∂(volume.restrict W), g0 s ≤ C := by
  filter_upwards [heq, ae_restrict_mem hW] with s h1 h2
  have h3 := ENNReal.ofReal_le_ofReal (hg s h2).2
  rw [h1] at h3
  rcases ENNReal.ofReal_le_ofReal_iff'.1 h3 with h | h
  · exact h
  · linarith [(hg s h2).1, (hg s h2).2]

/-- A lower density constant times the window length is at most `1`. -/
theorem const_mul_le_one {P : Measure 𝒳} [IsProbabilityMeasure P] {f : 𝒳 → ℝ} {t ρ c : ℝ} (hρ : 0 < ρ)
    (hc : 0 < c) (hd : QDensityLower P f t ρ c) : c * (2 * ρ) ≤ 1 := by
  obtain ⟨g, hg, hgc, hrep⟩ := hd
  have hA := hrep (Icc (t - ρ) (t + ρ)) measurableSet_Icc subset_rfl
  have hlow : ENNReal.ofReal (c * (2 * ρ)) ≤ P (f ⁻¹' Icc (t - ρ) (t + ρ)) := by
    rw [hA]
    calc ENNReal.ofReal (c * (2 * ρ)) = ∫⁻ _r in Icc (t - ρ) (t + ρ), ENNReal.ofReal c := by
          rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul hc.le]
          congr 1; ring
      _ ≤ ∫⁻ r in Icc (t - ρ) (t + ρ), ENNReal.ofReal (g r) :=
          setLIntegral_mono hg.ennreal_ofReal fun r hr => ENNReal.ofReal_le_ofReal (hgc r hr)
  have := hlow.trans prob_le_one
  exact (ENNReal.ofReal_le_one).1 this

/-- `(Q)` from a.e. bounds of a version (clamp it). -/
theorem qdensity_of_ae {P : Measure 𝒳} {f : 𝒳 → ℝ} {t ρ c C : ℝ} {g0 : ℝ → ℝ} (hg0 : Measurable g0)
    (hrep : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (t - ρ) (t + ρ) →
      P (f ⁻¹' A) = ∫⁻ s in A, ENNReal.ofReal (g0 s)) (hcC : c ≤ C)
    (hae : ∀ᵐ s ∂(volume.restrict (Icc (t - ρ) (t + ρ))), c ≤ g0 s ∧ g0 s ≤ C) : QDensity P f t ρ c C := by
  refine ⟨fun s => max c (min C (g0 s)), measurable_const.max (measurable_const.min hg0),
    fun s _ => ⟨le_max_left _ _, max_le hcC (min_le_left _ _)⟩, fun A hA hAW => ?_⟩
  rw [hrep A hA hAW]
  refine setLIntegral_congr_fun_ae hA ?_
  have h' := (ae_restrict_iff' measurableSet_Icc).1 hae
  filter_upwards [h'] with s hs hsA
  obtain ⟨h1, h2⟩ := hs (hAW hsA)
  rw [min_eq_right h2, max_eq_right h1]

/-- `(Q′)` from an a.e. lower bound of a version. -/
theorem qdensityLower_of_ae {P : Measure 𝒳} {f : 𝒳 → ℝ} {t ρ c : ℝ} {g0 : ℝ → ℝ} (hg0 : Measurable g0)
    (hrep : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (t - ρ) (t + ρ) →
      P (f ⁻¹' A) = ∫⁻ s in A, ENNReal.ofReal (g0 s))
    (hae : ∀ᵐ s ∂(volume.restrict (Icc (t - ρ) (t + ρ))), c ≤ g0 s) : QDensityLower P f t ρ c := by
  refine ⟨fun s => max c (g0 s), measurable_const.max hg0, fun s _ => le_max_left _ _, fun A hA hAW => ?_⟩
  rw [hrep A hA hAW]
  refine setLIntegral_congr_fun_ae hA ?_
  have h' := (ae_restrict_iff' measurableSet_Icc).1 hae
  filter_upwards [h'] with s hs hsA
  rw [max_eq_right (hs (hAW hsA))]

theorem qdensity_lower {P : Measure 𝒳} {f : 𝒳 → ℝ} {t ρ c C : ℝ} (h : QDensity P f t ρ c C) :
    QDensityLower P f t ρ c := by
  obtain ⟨g, hg, hb, hrep⟩ := h
  exact ⟨g, hg, fun s hs => (hb s hs).1, hrep⟩

/-- The supremum of a set of a.e. lower bounds is an a.e. lower bound (rational approximation). -/
theorem ae_le_sSup {μ : Measure ℝ} {S : Set ℝ} {g0 : ℝ → ℝ} (hne : S.Nonempty)
    (hS : ∀ c ∈ S, ∀ᵐ s ∂μ, c ≤ g0 s) : ∀ᵐ s ∂μ, sSup S ≤ g0 s := by
  have hq : ∀ q : ℚ, ∀ᵐ s ∂μ, (q : ℝ) < sSup S → (q : ℝ) ≤ g0 s := by
    intro q
    by_cases hlt : (q : ℝ) < sSup S
    · obtain ⟨c, hcS, hqc⟩ := exists_lt_of_lt_csSup hne hlt
      filter_upwards [hS c hcS] with s hs _ using hqc.le.trans hs
    · exact Eventually.of_forall fun s h => absurd h hlt
  filter_upwards [ae_all_iff.2 hq] with s hs
  exact le_of_forall_rat_lt_imp_le hs

/-- The infimum of a set of a.e. upper bounds is an a.e. upper bound. -/
theorem ae_sInf_le {μ : Measure ℝ} {S : Set ℝ} {g0 : ℝ → ℝ} (hne : S.Nonempty)
    (hS : ∀ C ∈ S, ∀ᵐ s ∂μ, g0 s ≤ C) : ∀ᵐ s ∂μ, g0 s ≤ sInf S := by
  have hq : ∀ q : ℚ, ∀ᵐ s ∂μ, sInf S < (q : ℝ) → g0 s ≤ (q : ℝ) := by
    intro q
    by_cases hlt : sInf S < (q : ℝ)
    · obtain ⟨C, hCS, hCq⟩ := exists_lt_of_csInf_lt hne hlt
      filter_upwards [hS C hCS] with s hs _ using hs.trans hCq.le
    · exact Eventually.of_forall fun s h => absurd h hlt
  filter_upwards [ae_all_iff.2 hq] with s hs
  exact le_of_forall_lt_rat_imp_le hs

theorem window_ne_zero {t ρ : ℝ} (hρ : 0 < ρ) : volume.restrict (Icc (t - ρ) (t + ρ)) ≠ 0 := by
  rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc, ENNReal.ofReal_eq_zero, not_le]
  linarith

end StatFormal.Wave31ta.RTrim

namespace StatFormal.Wave31ta

theorem quantile_of_QDensity : Claims.quantile_of_QDensity := by
  intro 𝒳 _ P _ f p t ρ c hf hρ hc hq hd
  exact RTrim.quantile_eq hf hρ hc hq hd

open StatFormal.Wave12c StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.BangBang
  StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Projection StatFormal.Wave4b in
theorem cor_trimrate_v2 : Claims.cor_trimrate_v2 := by
  intro ε hε0 hε1
  obtain ⟨Λ, hΛ, hmain⟩ := StatFormal.Wave30tx.cor_trimrate ε hε0 hε1
  refine ⟨Λ, hΛ, ?_⟩
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α ρ dstar hφ hκ hα0 hα1 hD hmin hρ
  have hf : Measurable (witFn dstar φ) := (stronglyMeasurable_const.inner hφ).measurable
  classical
  by_cases hadm : ∃ tα uα cf Cf cf' : ℝ, 0 < cf ∧ 0 < cf' ∧
      StatFormal.Wave30tx.IsQuantile P (witFn dstar φ) (1 - α) tα ∧ QDensity P (witFn dstar φ) tα ρ cf Cf ∧
      StatFormal.Wave30tx.IsQuantile Q (witFn dstar φ) α uα ∧ QDensityLower Q (witFn dstar φ) uα ρ cf'
  swap
  · exact ⟨0, fun tα uα cf Cf cf' h1 h2 h3 h4 h5 h6 => absurd ⟨tα, uα, cf, Cf, cf', h1, h2, h3, h4, h5, h6⟩ hadm⟩
  obtain ⟨t0, u0, c0, C0, c0', hc0, hc0', hq0, hQ0, hu0, hL0⟩ := hadm
  have ht0 : quantileAt P (witFn dstar φ) (1 - α) = t0 := RTrim.quantile_eq hf hρ hc0 hq0 (RTrim.qdensity_lower hQ0)
  have huq : quantileAt Q (witFn dstar φ) α = u0 := RTrim.quantile_eq hf hρ hc0' hu0 hL0
  have hW : MeasurableSet (Icc (t0 - ρ) (t0 + ρ)) := measurableSet_Icc
  have hW' : MeasurableSet (Icc (u0 - ρ) (u0 + ρ)) := measurableSet_Icc
  -- the `X` side: best constants
  obtain ⟨g0, hg0m, hg0b, hg0rep⟩ := hQ0
  set SA : Set ℝ := {c | 0 < c ∧ ∃ C, QDensity P (witFn dstar φ) t0 ρ c C} with hSA
  set SB : Set ℝ := {C | ∃ c, 0 < c ∧ QDensity P (witFn dstar φ) t0 ρ c C} with hSB
  have hc0A : c0 ∈ SA := ⟨hc0, C0, g0, hg0m, hg0b, hg0rep⟩
  have hC0B : C0 ∈ SB := ⟨c0, hc0, g0, hg0m, hg0b, hg0rep⟩
  have hAbdd : BddAbove SA := ⟨1 / (2 * ρ), fun c hc => by
    obtain ⟨hcpos, C, hQ⟩ := hc
    have h := RTrim.const_mul_le_one hρ hcpos (RTrim.qdensity_lower hQ)
    rw [le_div_iff₀ (by positivity)]; exact h⟩
  have hBbdd : BddBelow SB := ⟨0, fun C hC => by
    obtain ⟨c, hcpos, g, -, hb, -⟩ := hC
    have := hb t0 ⟨by linarith, by linarith⟩
    linarith [this.1, this.2]⟩
  have hAae : ∀ c ∈ SA, ∀ᵐ s ∂(volume.restrict (Icc (t0 - ρ) (t0 + ρ))), c ≤ g0 s := by
    rintro c ⟨hcpos, C, g, hgm, hgb, hgrep⟩
    exact RTrim.ae_lower hW (RTrim.ae_ofReal_eq hW hgm hg0m hgrep hg0rep) hcpos fun s hs => (hgb s hs).1
  have hBae : ∀ C ∈ SB, ∀ᵐ s ∂(volume.restrict (Icc (t0 - ρ) (t0 + ρ))), g0 s ≤ C := by
    rintro C ⟨c, hcpos, g, hgm, hgb, hgrep⟩
    exact RTrim.ae_upper hW (RTrim.ae_ofReal_eq hW hgm hg0m hgrep hg0rep) hcpos hgb
  set cs := sSup SA with hcs
  set Cs := sInf SB with hCs
  have hcs0 : 0 < cs := lt_of_lt_of_le hc0 (le_csSup hAbdd hc0A)
  have haeX : ∀ᵐ s ∂(volume.restrict (Icc (t0 - ρ) (t0 + ρ))), cs ≤ g0 s ∧ g0 s ≤ Cs := by
    filter_upwards [RTrim.ae_le_sSup ⟨c0, hc0A⟩ hAae, RTrim.ae_sInf_le ⟨C0, hC0B⟩ hBae] with s h1 h2
    exact ⟨h1, h2⟩
  have hcsCs : cs ≤ Cs := by
    have : (ae (volume.restrict (Icc (t0 - ρ) (t0 + ρ)))).NeBot := ae_neBot.2 (RTrim.window_ne_zero hρ)
    obtain ⟨s, hs1, hs2⟩ := haeX.exists
    exact hs1.trans hs2
  have hQs : QDensity P (witFn dstar φ) t0 ρ cs Cs := RTrim.qdensity_of_ae hg0m hg0rep hcsCs haeX
  -- the `Y` side
  obtain ⟨h0, hh0m, hh0b, hh0rep⟩ := hL0
  set SY : Set ℝ := {c | 0 < c ∧ QDensityLower Q (witFn dstar φ) u0 ρ c} with hSY
  have hc0Y : c0' ∈ SY := ⟨hc0', h0, hh0m, hh0b, hh0rep⟩
  have hYbdd : BddAbove SY := ⟨1 / (2 * ρ), fun c hc => by
    rw [le_div_iff₀ (by positivity)]; exact RTrim.const_mul_le_one hρ hc.1 hc.2⟩
  have hYae : ∀ c ∈ SY, ∀ᵐ s ∂(volume.restrict (Icc (u0 - ρ) (u0 + ρ))), c ≤ h0 s := by
    rintro c ⟨hcpos, g, hgm, hgb, hgrep⟩
    exact RTrim.ae_lower hW' (RTrim.ae_ofReal_eq hW' hgm hh0m hgrep hh0rep) hcpos hgb
  set cs' := sSup SY with hcs'
  have hcs0' : 0 < cs' := lt_of_lt_of_le hc0' (le_csSup hYbdd hc0Y)
  have hLs : QDensityLower Q (witFn dstar φ) u0 ρ cs' :=
    RTrim.qdensityLower_of_ae hh0m hh0rep (RTrim.ae_le_sSup ⟨c0', hc0Y⟩ hYae)
  -- the frozen corollary at the best constants
  have hQs' : QDensity P (witFn dstar φ) (quantileAt P (witFn dstar φ) (1 - α)) ρ cs Cs := by
    rw [ht0]; exact hQs
  obtain ⟨N, hN⟩ := hmain 𝒳 H P Q φ κ α ρ cs Cs cs' u0 dstar hφ hκ hα0 hα1 hD hmin hρ hcs0 hcs0' hQs' hu0 hLs
  refine ⟨N, fun tα uα cf Cf cf' hcf hcf' hqt hQt hqu hLu n m hn hm => ?_⟩
  have htα : tα = t0 := by
    rw [← ht0]; exact (RTrim.quantile_eq hf hρ hcf hqt (RTrim.qdensity_lower hQt)).symm
  have huα : uα = u0 := by
    rw [← huq]; exact (RTrim.quantile_eq hf hρ hcf' hqu hLu).symm
  subst htα huα
  have hcf_le : cf ≤ cs := le_csSup hAbdd ⟨hcf, Cf, hQt⟩
  have hCf_ge : Cs ≤ Cf := csInf_le hBbdd ⟨cf, hcf, hQt⟩
  have hcf'_le : cf' ≤ cs' := le_csSup hYbdd ⟨hcf', hLu⟩
  obtain ⟨E, hEm, hEp, hE⟩ := hN n m hn hm
  refine ⟨E, hEm, hEp, fun z hz pr hpr hmn => ?_⟩
  have hc := hE z hz pr hpr hmn
  rw [ht0] at hc
  dsimp only at hc ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  -- monotonicity in the constants
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ x)
  have h1α : 0 < 1 - α := by linarith
  have hmin_le : min cf cf' ≤ min cs cs' := min_le_min hcf_le hcf'_le
  have hsq : 0 < √((1 - α) * min cf cf') := Real.sqrt_pos.2 (mul_pos h1α (lt_min hcf hcf'))
  have hV : κ / (1 - α) + 1 / √((1 - α) * min cs cs') ≤ κ / (1 - α) + 1 / √((1 - α) * min cf cf') :=
    add_le_add le_rfl (one_div_le_one_div_of_le hsq
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hmin_le h1α.le)))
  have hV0 : 0 ≤ κ / (1 - α) + 1 / √((1 - α) * min cs cs') := by positivity
  have hq0 : 0 ≤ √((min n m : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hDq : 0 ≤ Dpop φ P Q α * √((min n m : ℕ) : ℝ) := mul_nonneg hD.le hq0
  have hCs0 : 0 ≤ Cs := hcs0.le.trans hcsCs
  have hCterm : Cs * (κ * (κ / (1 - α) + 1 / √((1 - α) * min cs cs')) + 1 / cs) ≤
      Cf * (κ * (κ / (1 - α) + 1 / √((1 - α) * min cf cf')) + 1 / cf) :=
    mul_le_mul hCf_ge (add_le_add (mul_le_mul_of_nonneg_left hV hκ0) (one_div_le_one_div_of_le hcf hcf_le))
      (by positivity) (hCs0.trans hCf_ge)
  have hR : Λ * (Cs * (κ * (κ / (1 - α) + 1 / √((1 - α) * min cs cs')) + 1 / cs) / √((min n m : ℕ) : ℝ)) ≤
      Λ * (Cf * (κ * (κ / (1 - α) + 1 / √((1 - α) * min cf cf')) + 1 / cf) / √((min n m : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hCterm hq0) hΛ.le
  refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hV hDq) hΛ.le),
    h3.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hV hq0) hΛ.le),
    h4.trans (ENNReal.ofReal_le_ofReal hR), fun ϑ ϑh hϑ hϑh => (h5 ϑ ϑh hϑ hϑh).trans hR⟩

end StatFormal.Wave31ta
