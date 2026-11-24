import StatFormal.Wave31tu.RouteTEvent
import StatFormal.Wave31tu.RouteTArith

/-!
# Wave 31tu route T: good ramps at every grid level and the bets (proof of Theorem S4.19, S4 :1354-1366; untrusted proof material)

* `empirical_comp_apply`, `intervalEvent_scale`, `integral_map_div`: the empirical law of `x/σ` is the image of that of `x`; the
  event of Lemma S4.23 is invariant under `x ↦ x/σ` (intervals go to intervals); `∫ F d(P∘(·/σ)⁻¹) = ∫ F(z/σ) dP`.
* `fit_transfer`: the conclusion of Proposition S4.27 for the data rescaled by `1/σ` (the kernel `e^{−|x−y|}`) gives it for the data
  (Claim Y17 `lap_rescale`: equal minimizers, witness values and own terms, so equal cut points and ramps as functions of `z/σ`).
* `good_ramp`: a genuine-quantile ramp rule whose every minimizer and every pair of genuine cut points give `u < t` and an excess
  `≥ e` bets, with excess `≥ e` (Claim Y10 `lap_clip` for `D̂ > 0`).
* `lower_of_fits`: on the event `𝓔_fit`, a fit property at every level `α⋆ − e`, `e ≥ ε`, of excess `κe/2`, and `κε/2 ≥ T_bet(J)`
  give `P(α̂ < a_ε) ≤ η` (Claim Y16 `lap_bets` with `ϱ = κε/2`, `ξ_j = (α⋆ − α_j)/ε`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tu.RouteT

open StatFormal.Wave30tq StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.Wave31tl StatFormal.TrimmedMMD.Concentration

/-- The empirical law of a transformed sample is the image of the empirical law. -/
lemma empirical_comp_apply {n : ℕ} (x : Fin n → ℝ) (f : ℝ → ℝ) (S : Set ℝ) :
    (empirical fun i => f (x i)) S = (empirical x) (f ⁻¹' S) := by
  simp only [empirical, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  rfl

/-- The event of Lemma S4.23 is invariant under the rescaling `x ↦ x/σ`. -/
lemma intervalEvent_scale {σ : ℝ} (hσ : 0 < σ) (P : Measure ℝ) {n : ℕ} (x : Fin n → ℝ) {c : ℝ}
    (h : IntervalEvent P x c) : IntervalEvent (P.map fun z => z / σ) (fun i => x i / σ) c := by
  intro I hI
  have hmeas : Measurable fun z : ℝ => z / σ := measurable_id.div_const σ
  have hmono : Monotone fun z : ℝ => z / σ := fun a b hab => div_le_div_of_nonneg_right hab hσ.le
  have hI' : ((fun z : ℝ => z / σ) ⁻¹' I).OrdConnected := hI.preimage_mono hmono
  have hIm : MeasurableSet I := hI.measurableSet
  have e1 : (empirical fun i => x i / σ).real I = (empirical x).real ((fun z => z / σ) ⁻¹' I) := by
    simp only [Measure.real]
    rw [empirical_comp_apply x (fun z => z / σ) I]
  have e2 : (P.map fun z => z / σ).real I = P.real ((fun z => z / σ) ⁻¹' I) := by
    simp only [Measure.real]; rw [Measure.map_apply hmeas hIm]
  rw [e1, e2]
  exact h _ hI'

/-- `∫ F d(P ∘ (·/σ)⁻¹) = ∫ F(z/σ) dP`. -/
lemma integral_map_div {σ : ℝ} (hσ : 0 < σ) (P : Measure ℝ) (F : ℝ → ℝ) :
    ∫ z, F z ∂(P.map fun z => z / σ) = ∫ z, F (z / σ) ∂P := by
  have e : (fun z : ℝ => z / σ) = fun z => z * σ⁻¹ := funext fun z => div_eq_mul_inv z σ
  rw [e]
  exact (measurableEmbedding_mulRight₀ (inv_ne_zero hσ.ne')).integral_map F

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Rescaling the conclusion of Proposition S4.27** (Claim Y17). -/
lemma fit_transfer (h17 : Claims.lap_rescale) {σ : ℝ} (hσ : 0 < σ) (φ : ℝ → H) (hφ : IsLaplaceFeature σ φ)
    (P Q : Measure ℝ) {n' m' : ℕ} (xs : Fin n' → ℝ) (ys : Fin m' → ℝ) (α e : ℝ)
    (h : ∀ w v, IsQPMin (fun u => φ (σ * u)) α (fun i => xs i / σ) (fun j => ys j / σ) w v →
      ∀ t u, GenuineCuts (fun u => φ (σ * u)) (fun i => xs i / σ) (fun j => ys j / σ) w v α t u →
        u < t ∧ e ≤ (∫ z, ramp (fitF (fun u => φ (σ * u)) (fun i => xs i / σ) (fun j => ys j / σ) w v) t u z
            ∂(P.map fun z => z / σ)) -
          (∫ z, ramp (fitF (fun u => φ (σ * u)) (fun i => xs i / σ) (fun j => ys j / σ) w v) t u z
            ∂(Q.map fun z => z / σ)) - α) :
    ∀ w v, IsQPMin φ α xs ys w v → ∀ t u, GenuineCuts φ xs ys w v α t u →
      u < t ∧ e ≤ (∫ z, ramp (fitF φ xs ys w v) t u z ∂P) - (∫ z, ramp (fitF φ xs ys w v) t u z ∂Q) - α := by
  intro w v hqp t u hcuts
  obtain ⟨-, ha, -⟩ := h17 H σ φ hσ hφ
  obtain ⟨hiff, -, hF, hoX, hoY⟩ := ha n' m' xs ys α w v
  have hramp : ∀ z, ramp (fitF φ xs ys w v) t u z =
      ramp (fitF (fun u => φ (σ * u)) (fun i => xs i / σ) (fun j => ys j / σ) w v) t u (z / σ) := by
    intro z; simp only [ramp, clip, hF z]
  have hcuts' : GenuineCuts (fun u => φ (σ * u)) (fun i => xs i / σ) (fun j => ys j / σ) w v α t u := by
    have eX : (fun i => fitF φ xs ys w v (xs i)) =
        fun i => fitF (fun u => φ (σ * u)) (fun i => xs i / σ) (fun j => ys j / σ) w v (xs i / σ) :=
      funext fun i => hF (xs i)
    have eY : (fun j => fitF φ xs ys w v (ys j)) =
        fun j => fitF (fun u => φ (σ * u)) (fun i => xs i / σ) (fun j => ys j / σ) w v (ys j / σ) :=
      funext fun j => hF (ys j)
    unfold GenuineCuts at hcuts ⊢
    rw [eX, eY, hoX, hoY] at hcuts
    exact hcuts
  obtain ⟨hut, hex⟩ := h w v (hiff.1 hqp) t u hcuts'
  refine ⟨hut, ?_⟩
  rw [integral_map_div hσ, integral_map_div hσ] at hex
  simp_rw [← hramp] at hex
  exact hex

/-- **A good fit makes the rule bet, with the excess** (Claim Y10 for `D̂ > 0`). -/
lemma good_ramp [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (h10 : Claims.lap_clip) {σ : ℝ} (hσ : 0 < σ)
    (φ : ℝ → H) (hφ : IsLaplaceFeature σ φ) (P Q : Measure ℝ) {n' m' : ℕ} (xs : Fin n' → ℝ) (ys : Fin m' → ℝ)
    (hn : 1 ≤ n') (hm : 1 ≤ m') (hxy : ∀ i j, xs i ≠ ys j) {α e : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {has : Prop}
    {g : ℝ → ℝ} (hrule : IsGenuineRamp φ α xs ys has g)
    (hfit : ∀ w v, IsQPMin φ α xs ys w v → ∀ t u, GenuineCuts φ xs ys w v α t u →
      u < t ∧ e ≤ (∫ z, ramp (fitF φ xs ys w v) t u z ∂P) - (∫ z, ramp (fitF φ xs ys w v) t u z ∂Q) - α) :
    has ∧ e ≤ (∫ z, g z ∂P) - (∫ z, g z ∂Q) - α := by
  obtain ⟨w, v, hqp, -, hpos⟩ := hrule.2 hn hm
  have hD : 0 < qpVal φ xs ys w v := (h10 H σ φ n' m' xs ys α w v hσ hφ hn hm hxy hα0 hα1 hqp).1
  obtain ⟨t, u, hcuts, hhas, hg⟩ := hpos hD
  obtain ⟨hut, hex⟩ := hfit w v hqp t u hcuts
  have hh : has := hhas.2 hut
  refine ⟨hh, ?_⟩
  rw [hg hh]
  exact hex

/-- **The bets** (S4 :1354-1366): from good fits at every level `α⋆ − e`, `e ≥ ε`, on `𝓔_fit`, and `κε/2 ≥ T_bet(J)`,
`P(α̂ < a_ε) ≤ η` (Claims Y4, Y10, Y16). -/
lemma lower_of_fits [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (h4 : Claims.lap_intervals)
    (h10 : Claims.lap_clip) (h16 : Claims.lap_bets) {σ : ℝ} (hσ : 0 < σ) (φ : ℝ → H) (hφ : IsLaplaceFeature σ φ)
    (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [NullSingletonClass P] [NullSingletonClass Q]
    {J n m : ℕ} {α : Fin J → ℝ} {δ s2 η ε κ c : ℝ} {R : LoRun ℝ J n m}
    (hgrid : IsGrid α) (hα0 : ∀ j, 0 < α j) (hJ : 1 ≤ J) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hs20 : 0 < s2) (hs24 : s2 ≤ 4)
    (hη0 : 0 < η) (hη1 : η < 1) (hrun : IsGenuineRun R φ α δ (1 / 2) s2) (hdef : IsDefaultRun R)
    (hN10 : 10 ≤ min n m) (hc : Real.log (16 * (((max n m : ℕ) : ℝ) + 1) ^ 2 / η) ≤ c) (hε : 0 < ε)
    (hTbet : Tbet (1 / 2) s2 (Real.log (1 / δ)) η J R.N ≤ κ * ε / 2)
    (hfit : ∀ (n' m' : ℕ) (xs : Fin n' → ℝ) (ys : Fin m' → ℝ), ((min n m : ℕ) : ℝ) / 5 ≤ n' →
      ((min n m : ℕ) : ℝ) / 5 ≤ m' → IntervalEvent P xs c → IntervalEvent Q ys c → (∀ i j, xs i ≠ ys j) →
      ∀ e, ε ≤ e → e < Distances.tvDist P Q → ∀ w v, IsQPMin φ (Distances.tvDist P Q - e) xs ys w v →
        ∀ t u, GenuineCuts φ xs ys w v (Distances.tvDist P Q - e) t u →
          u < t ∧ κ * e / 2 ≤ (∫ z, ramp (fitF φ xs ys w v) t u z ∂P) - (∫ z, ramp (fitF φ xs ys w v) t u z ∂Q) -
            (Distances.tvDist P Q - e)) :
    sampleLaw P Q n m {z | R.alphaLo α δ z.1 z.2 < gridFloor α (Distances.tvDist P Q - ε)} ≤ ENNReal.ofReal η := by
  classical
  obtain ⟨hbat, hsize, hNp⟩ := default_batches R hdef hrun.1.1 hN10
  have hNr : (10 : ℝ) ≤ ((min n m : ℕ) : ℝ) := by exact_mod_cast hN10
  have hone : ∀ b, 1 ≤ b → b ≤ 2 → 1 ≤ fitCard R.lx b ∧ 1 ≤ fitCard R.ly b := by
    intro b hb1 hb2
    obtain ⟨h1, h2, -, -⟩ := hsize b hb1 hb2
    have h1' : (1 : ℝ) ≤ fitCard R.lx b := by linarith
    have h2' : (1 : ℝ) ≤ fitCard R.ly b := by linarith
    exact ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
  obtain ⟨E, hEm, hEc, hEgood⟩ := fit_event h4 P Q R.lx R.ly hη0 hη1 (hone 1 le_rfl (by norm_num)).1
    (hone 1 le_rfl (by norm_num)).2 hc
  obtain ⟨h0, hh0, hgap⟩ := exists_gapsGe hgrid.1
  have hNpos : 1 ≤ R.N := by
    have : (1 : ℝ) ≤ R.N := by linarith
    exact_mod_cast this
  have hJeps : 0 < Jeps J ε h0 := lt_min (by exact_mod_cast hJ) (by positivity)
  have hJle : Jeps J ε h0 ≤ J := min_le_left _ _
  have hTb : Tbet (1 / 2) s2 (Real.log (1 / δ)) η (Jeps J ε h0) R.N ≤ κ * ε / 2 :=
    (Route.Tbet_mono (by norm_num) hs20 hη0 hJeps hJle).trans hTbet
  refine h16 ℝ P Q J n m α δ s2 η h0 ε (κ * ε / 2) R E hgrid hJ hδ0 hδ1 hs20 hs24 hη0 hη1 hh0 hgap hε hNpos hrun.1
    (fun j k x y z => ⟨(hrun.2.2 j k x y z).1, (hrun.2.2 j k x y z).2.1⟩) hEm hEc hTb ?_
  intro z hz j hj k
  obtain ⟨hxy, hev⟩ := hEgood z hz
  obtain ⟨hb1, hb2⟩ := hbat k
  obtain ⟨hev1, hev2⟩ := hev (R.bat k) hb1 hb2
  obtain ⟨hs1, hs2, -, -⟩ := hsize (R.bat k) hb1 hb2
  obtain ⟨hn', hm'⟩ := hone (R.bat k) hb1 hb2
  have hxy' : ∀ i i', fitSample R.lx (R.bat k) z.1 i ≠ fitSample R.ly (R.bat k) z.2 i' := fun i i' => hxy _ _
  have hαj0 := hα0 j
  have hαj1 := (hgrid.2 j).2
  have hf := hfit _ _ (fitSample R.lx (R.bat k) z.1) (fitSample R.ly (R.bat k) z.2) hs1 hs2 hev1 hev2 hxy'
    (Distances.tvDist P Q - α j) (by linarith) (by linarith)
  rw [sub_sub_cancel] at hf
  obtain ⟨hhas, hex⟩ := good_ramp h10 hσ φ hφ P Q _ _ hn' hm' hxy' hαj0 hαj1 (hrun.2.1 j k z.1 z.2) hf
  refine ⟨hhas, ?_⟩
  unfold condMean
  have e : κ * ε / 2 * ((Distances.tvDist P Q - α j) / ε) = κ * (Distances.tvDist P Q - α j) / 2 := by
    field_simp
  rw [e]
  linarith

end StatFormal.Wave31tu.RouteT
