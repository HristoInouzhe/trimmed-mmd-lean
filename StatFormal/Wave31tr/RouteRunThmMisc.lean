import StatFormal.Wave31tr.RouteRunAdm
import StatFormal.Wave31tl.RouteArith
import StatFormal.Wave30tx.Proofs
import StatFormal.Wave30tx.RouteAlpha
import StatFormal.Wave30tl.RouteCrossing
import StatFormal.Lib.PaperRunThm.EmpVar

/-!
# Wave 31tr, chunk A2, T31, T48 (c), T51 (untrusted route)

Proves `Claims.default_pairs_three_quarters` (T31), `Claims.alg_prior` (T48 (c)) and `Claims.trimming_at_lower` (T51).
* T31: the default batch sizes `n_[1] = b₂ − b₁`, `n_[2] = n − b₂` (`Wave31tl.Arith.counts`, `b₁ ≤ b₂ ≤ n` by A1's
  `nearestCuts_bounds`); with `|b₁ − n/4| ≤ ½`, `|b₂ − n/2| ≤ ½`: `|min(n_[1], m_[1]) − min(n,m)/4| ≤ 1` and
  `|min(n_[2], m_[2]) − min(n,m)/2| ≤ ½` (cases on the three minima).
* T48 (c): Algorithm S1's prior `algPrior R` is measurable (`has` measurable and `g` jointly measurable, A1's
  `has_measurableSet`, `g_measurable`; the variance is continuous, `Lib/PaperRunThm/EmpVar`), valued in `[10⁻⁴, ½]` where `has`
  holds (the ramp is `[0,1]`-valued, A1's `g_mem`, so each variance is at most `¼`, and the batch-size ratio is at most `1`
  in its branch) and `1` elsewhere, and a function of the batches before `b` (A1's `has_congr`, `g_congr`, `fitSample_congr`).
  The run with this prior is `R` with the fractions recomputed by `eq:fractions` (`withPrior`): same `has`, `g`, pairing.
* T51: the certified `Wave30tx.alphahat` at the constant threshold `τ ≡ 2κ` (valid: `D̂_α ≤ 2κ`, `Wave30tl.Demp_le_two_kappa`;
  the crossing set contains `0`); its event `E` (probability `≥ 1 − 2δ'`) carries both bounds at every level in `[0, α⋆]`, in
  particular at `α̃ z ≤ α⋆`; the union bound `Wave30tx.RAlpha.ofReal_le_inter` with `P(α̃ ≤ α⋆) ≥ 1 − δ`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tr.RouteRunThm

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tz StatFormal.Wave30tp StatFormal.Wave31tl
  StatFormal.Wave31tr.RouteRun StatFormal.PaperRun StatFormal.PaperRunThm

/-! ### T31 — the number of pairs of the default batches -/

theorem default_pairs_three_quarters_route : Claims.default_pairs_three_quarters := by
  intro n m b₁ b₂ c₁ c₂ hb hc
  obtain ⟨hb12, hb2n⟩ := nearestCuts_bounds hb
  obtain ⟨hc12, hc2m⟩ := nearestCuts_bounds hc
  obtain ⟨-, hx1, hx2⟩ := Arith.counts hb12 hb2n
  obtain ⟨-, hy1, hy2⟩ := Arith.counts hc12 hc2m
  unfold defaultPairs
  rw [hx1, hx2, hy1, hy2]
  obtain ⟨h1, h2⟩ := hb
  obtain ⟨h3, h4⟩ := hc
  rw [abs_le] at h1 h2 h3 h4 ⊢
  push_cast [Nat.cast_sub hb12, Nat.cast_sub hb2n, Nat.cast_sub hc12, Nat.cast_sub hc2m]
  rcases min_cases (n : ℝ) m with ⟨e1, f1⟩ | ⟨e1, f1⟩ <;>
  rcases min_cases ((b₂ : ℝ) - b₁) ((c₂ : ℝ) - c₁) with ⟨e2, f2⟩ | ⟨e2, f2⟩ <;>
  rcases min_cases ((n : ℝ) - b₂) ((m : ℝ) - c₂) with ⟨e3, f3⟩ | ⟨e3, f3⟩ <;>
  constructor <;> linarith

/-! ### T48 (c) — Algorithm S1's initial variance is a prior rule -/

section Prior

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {φ : 𝒳 → H} {J n m : ℕ} {R : LoRun 𝒳 J n m} {α : Fin J → ℝ} {δ lmax s2 w0 : ℝ}
  {v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ} {qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ} {nb : ℕ} {cx cy : ℕ → ℕ}

/-- `v · a / b ≤ v` for `0 ≤ v`, `0 ≤ a ≤ b` (also when `b = 0`, where the quotient is `0`). -/
theorem mul_div_le_self_of_le {v a b : ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a) (hab : a ≤ b) : v * a / b ≤ v := by
  rcases (ha.trans hab).eq_or_lt with hb | hb
  · rw [← hb, div_zero]; exact hv
  · rw [div_le_iff₀ hb]; exact mul_le_mul_of_nonneg_left hab hv

/-- `0 ≤ v · a / b` for `0 ≤ v`, `0 ≤ a`, `0 ≤ b`. -/
theorem mul_div_nonneg' {v a b : ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ v * a / b :=
  div_nonneg (mul_nonneg hv ha) hb

/-- The variance of the ramp at the fitting `X`'s (or `Y`'s) of batch `b` is in `[0, ¼]`. -/
theorem empVar_ramp_mem (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (j : Fin J) (b : ℕ) (x : Fin n → 𝒳)
    (y : Fin m → 𝒳) {k : ℕ} (z : Fin k → 𝒳) :
    0 ≤ empVar (fun i => R.g j b x y (z i)) ∧ empVar (fun i => R.g j b x y (z i)) ≤ 1 / 4 :=
  ⟨popVar_nonneg _, popVar_le_quarter _ fun i => g_mem hP j b x y (z i)⟩

/-- **T48 (c)**, the range: where `has` holds, Algorithm S1's prior is in `[10⁻⁴, ½]`. -/
theorem algPrior_mem (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (j : Fin J) (b : ℕ) (x : Fin n → 𝒳)
    (y : Fin m → 𝒳) (hh : R.has j b x y) : algPrior R j b x y ∈ Icc (1 / 10000 : ℝ) (1 / 2) := by
  classical
  obtain ⟨hX0, hX1⟩ := empVar_ramp_mem hP j b x y (fitSample R.lx b x)
  obtain ⟨hY0, hY1⟩ := empVar_ramp_mem hP j b x y (fitSample R.ly b y)
  have hnx : (0 : ℝ) ≤ batchCount R.lx b := Nat.cast_nonneg _
  have hny : (0 : ℝ) ≤ batchCount R.ly b := Nat.cast_nonneg _
  unfold algPrior
  rw [ite_eq_left hh]
  refine ⟨le_max_right _ _, max_le ?_ (by norm_num)⟩
  split_ifs with hle
  · have := mul_div_le_self_of_le hY0 hnx hle
    linarith
  · have := mul_div_le_self_of_le hX0 hny (le_of_lt (not_le.mp hle))
    linarith

/-- **T48 (c)**, the values: Algorithm S1's prior is in `[0, 4]` everywhere. -/
theorem algPrior_mem_04 (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (j : Fin J) (b : ℕ) (x : Fin n → 𝒳)
    (y : Fin m → 𝒳) : algPrior R j b x y ∈ Icc (0 : ℝ) 4 := by
  classical
  by_cases hh : R.has j b x y
  · obtain ⟨h1, h2⟩ := algPrior_mem hP j b x y hh
    exact ⟨by linarith, by linarith⟩
  · unfold algPrior
    rw [ite_eq_right hh]
    norm_num

/-- **T48 (c)**, dependence: Algorithm S1's prior of batch `b` depends only on the batches before `b`. -/
theorem algPrior_congr (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (j : Fin J) (b : ℕ) {x x' : Fin n → 𝒳}
    {y y' : Fin m → 𝒳} (hx : ∀ i, R.lx i < b → x i = x' i) (hy : ∀ i, R.ly i < b → y i = y' i) :
    algPrior R j b x y = algPrior R j b x' y' := by
  classical
  have hh := has_congr hP j b hx hy
  unfold algPrior
  rw [g_congr hP j b hx hy, fitSample_congr R.lx b hx, fitSample_congr R.ly b hy]
  by_cases h : R.has j b x y
  · rw [ite_eq_left h, ite_eq_left (hh.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hh.mpr h'))]

/-- **T48 (c)**, measurability of Algorithm S1's prior in the sample. -/
theorem algPrior_measurable (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (hφ : StronglyMeasurable φ)
    (hqt : IsQuantileRule qt) (hqu : IsQuantileRule qu) (j : Fin J) (b : ℕ) :
    Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => algPrior R j b p.1 p.2 := by
  classical
  have hset := has_measurableSet hP hφ hqt hqu j b
  have hg := g_measurable hP hφ hqt hqu j b
  have hvX : Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) =>
      empVar (fun i => R.g j b p.1 p.2 (fitSample R.lx b p.1 i)) := by
    refine (measurable_popVar _).comp (Measurable.of_eval fun i => ?_)
    exact hg.comp (measurable_id.prodMk ((measurable_pi_apply i).comp ((measurable_fitSample R.lx b).comp measurable_fst)))
  have hvY : Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) =>
      empVar (fun i => R.g j b p.1 p.2 (fitSample R.ly b p.2 i)) := by
    refine (measurable_popVar _).comp (Measurable.of_eval fun i => ?_)
    exact hg.comp (measurable_id.prodMk ((measurable_pi_apply i).comp ((measurable_fitSample R.ly b).comp measurable_snd)))
  unfold algPrior
  refine Measurable.ite hset (Measurable.max ?_ measurable_const) measurable_const
  by_cases hle : (batchCount R.lx b : ℝ) ≤ batchCount R.ly b
  · simp only [ite_eq_left hle]
    exact hvX.add ((hvY.mul_const _).div_const _)
  · simp only [ite_eq_right hle]
    exact hvY.add ((hvX.mul_const _).div_const _)

/-- **T48 (c)**: Algorithm S1's prior is a prior rule on every paper run. -/
theorem algPrior_isPriorRule (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (hφ : StronglyMeasurable φ)
    (hqt : IsQuantileRule qt) (hqu : IsQuantileRule qu) : IsPriorRule R.lx R.ly (algPrior R) :=
  fun j b => ⟨algPrior_measurable hP hφ hqt hqu j b, fun x y => algPrior_mem_04 hP j b x y,
    fun _ _ _ _ hx hy => algPrior_congr hP j b hx hy⟩

open Classical in
/-- The run `R` with its fractions recomputed by `eq:fractions` from the prior `v` (same labels, pairing, bets, ramps). -/
def withPrior (R : LoRun 𝒳 J n m) (α : Fin J → ℝ) (δ lmax s2 w0 : ℝ)
    (v : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) : LoRun 𝒳 J n m :=
  { R with
    lam := fun j k x y z => if hk : k < R.N then
      (if R.has j (R.bat ⟨k, hk⟩) x y then
        fracFormula lmax (α j) (Real.log (1 / δ)) R.N s2 w0 (v j (R.bat ⟨k, hk⟩) x y)
          (fun l : Fin k => if R.has j (R.bat (Fin.castLE hk.le l)) x y then 1 else 0) z
      else 0) else 0 }

/-- Replacing the prior of a paper run by any prior rule gives a paper run with the same bets and ramps. -/
theorem withPrior_isPaperRun (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy)
    {v : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ} (hv : IsPriorRule R.lx R.ly v) :
    IsPaperRun (withPrior R α δ lmax s2 w0 v) φ α δ lmax s2 w0 v qt qu nb cx cy := by
  classical
  obtain ⟨h1, h2, h3, h4, h5, -, σ, hσ, hhg, -⟩ := hP
  refine ⟨h1, h2, h3, h4, h5, hv, σ, hσ, hhg, fun j k x y z => ?_⟩
  change (if hk : (k : ℕ) < R.N then _ else _) = _
  rw [dite_eq_left (show (k : ℕ) < R.N from k.isLt)]
  rfl

end Prior

theorem alg_prior_route : Claims.alg_prior := by
  intro 𝒳 H _ _ _ _ φ κ J n m α δ lmax s2 w0 v0 qt qu nb cx cy R hφ _ _ _ _ _ _ _ _ hqt hqu hP
  have hv := algPrior_isPriorRule hP hφ hqt hqu
  exact ⟨hv, fun j b x y hh => algPrior_mem hP j b x y hh, withPrior R α δ lmax s2 w0 (algPrior R), rfl, rfl,
    withPrior_isPaperRun hP hv⟩

/-! ### T51 — the trimming read at a valid lower bound -/

theorem trimming_at_lower_route : Claims.trimming_at_lower := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ δ' n m αt hφ hκ hchar htv0 htv1 hδ0 hδ1 hδ'0 hδ'1 hn hm hαm hα0 hαP
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x₀)
  have hDle := fun (x : Fin n → 𝒳) (y : Fin m → 𝒳) => StatFormal.Wave30tl.Demp_le_two_kappa hκ hn hm x y
  have hvalid : StatFormal.Wave30tu.ValidThreshold φ n m δ (fun _ => 2 * κ) := by
    refine ⟨fun _ _ => by linarith, monotoneOn_const, fun a ha P' Q' _ _ _ => ?_⟩
    have e : {z : (Fin n → 𝒳) × (Fin m → 𝒳) | 2 * κ < StatFormal.TrimmedMMD.Unconditional.Demp φ z.1 z.2 a} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hDle z.1 z.2 a ha
    rw [e, measure_empty]
    exact zero_le
  have hne : ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
      (StatFormal.TrimmedMMD.crossSet (StatFormal.TrimmedMMD.Unconditional.Demp φ x y) fun _ => 2 * κ).Nonempty :=
    fun x y => ⟨0, ⟨le_rfl, one_pos⟩, hDle x y 0 ⟨le_rfl, one_pos⟩⟩
  obtain ⟨-, E, hEm, hEp, -, hB, -⟩ := StatFormal.Wave30tx.alphahat 𝒳 H P Q φ κ δ δ' (fun _ => 2 * κ) n m hφ hκ hchar
    htv0 htv1 hδ0 hδ1 hδ'0 hδ'1 hn hm hvalid continuousOn_const hne
  set TV := StatFormal.Distances.tvDist P Q with hTV
  have hA : MeasurableSet {z : (Fin n → 𝒳) × (Fin m → 𝒳) | αt z ≤ TV} := measurableSet_le hαm measurable_const
  have hprob : IsProbabilityMeasure (sampleLaw P Q n m) := by unfold sampleLaw; infer_instance
  have hAp : ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m {z | αt z ≤ TV} := by
    have hc : {z : (Fin n → 𝒳) × (Fin m → 𝒳) | αt z ≤ TV} = {z | TV < αt z}ᶜ := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
    rw [hc, prob_compl_eq_one_sub (measurableSet_lt measurable_const hαm), ENNReal.ofReal_sub _ hδ0.le,
      ENNReal.ofReal_one]
    exact tsub_le_tsub_left hαP 1
  refine ⟨E, hEm, ?_, fun z hz hzα pr hpr hmin => hB z hz (αt z) ⟨hα0 z, hzα⟩ pr hpr hmin⟩
  have h := StatFormal.Wave30tx.RAlpha.ofReal_le_inter (sampleLaw P Q n m) hEm hA hEp hAp
  rw [show 1 - 2 * δ' + (1 - δ) - 1 = 1 - δ - 2 * δ' by ring] at h
  exact h

end StatFormal.Wave31tr.RouteRunThm
