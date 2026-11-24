import StatFormal.Wave31tr.RouteAlpha0Gate
import StatFormal.Wave31tr.RouteAlpha0Ex
import StatFormal.Wave30tz.RouteLower
import StatFormal.Lib.Alpha0Witness.Gram
import StatFormal.Lib.Alpha0Witness.Deviation
import StatFormal.Lib.Alpha0Witness.Basic

/-!
# Wave 31tr, chunk M2: T17(a) `alpha0_reject_le`, T17(b) `alpha0_inconsistent` (untrusted route)

(a) The Gaussian feature map is continuous (`Alpha0Witness.continuous_of_gram`), of norm `1`, and
`f₀ = exWitness exP exQ = ⟪(μ_P − μ_Q)/‖μ_P − μ_Q‖, φ ·⟫` with `‖μ_P − μ_Q‖ = MMD` (`inner_meanEmb_sub`, `norm_sq_meanEmb_sub`).
The certified `alpha0_valid` with `F_b = f̂_{0,b}` (jointly measurable and predictable, `RouteAlpha0Gate`) bounds the rejection
probability by `δ + P(∃ k, α_j < KS⁺(f̂_{0,bat k}))`. For `α_j ≥ 2/5`, `KS⁺(f̂_{0,b}) > α_j` forces `KS⁺(f̂_{0,b}) ≠ 2/5`, hence
(T16(b), `ex_ks_stable_route`) some atom with `|f̂_{0,b} − f₀| ≥ g₀/2`, hence (normalization, `norm_normalize_sub_le`)
`‖meanDev_P‖ + ‖meanDev_Q‖ ≥ g₀·MMD/4` on the fitting sample of batch `b`. Markov with `E‖meanDev‖ ≤ 1/√k`
(`measure_meanDev_ge_le`, the fitting sample has law `P^{⊗n_{<b}}`: `Wave30tz.map_fitSample`), a union over the `≤ B_max + 1`
batches and `n_{<b} ≥ cn − C₀ → ∞` give `≤ ε` eventually. No strong law is needed.
(b) `α_i ≤ α̂` forces the rejection of `H_{0,α_i}` on a grid (`alphaLo_ge_rej`); with (a), `P(α̂ ≥ α_i) ≤ δ + ε` eventually, which
excludes `P(α̂ ≥ α_i) ≥ 1 − ε` for `ε = (1 − δ)/3`; `TV(exP, exQ) = 3/5` (`Wave30tz.tv_ex`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr.RouteAlpha0

open StatFormal.Wave30tz StatFormal.Wave30tp StatFormal.Alpha0Witness StatFormal.Concentration

section Gauss

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A feature map with the Gaussian Gram function is continuous. -/
theorem gaussFeat_continuous {φ : ℝ → H} (hk : ∀ a x, ⟪φ a, φ x⟫_ℝ = Real.exp (-(a - x) ^ 2 / 2)) : Continuous φ := by
  refine continuous_of_gram ?_
  have e : (fun p : ℝ × ℝ => ⟪φ p.1, φ p.2⟫_ℝ) = fun p => Real.exp (-(p.1 - p.2) ^ 2 / 2) := funext fun p => hk p.1 p.2
  rw [e]
  fun_prop

/-- A feature map with the Gaussian Gram function has unit norm. -/
theorem gaussFeat_norm {φ : ℝ → H} (hk : ∀ a x, ⟪φ a, φ x⟫_ℝ = Real.exp (-(a - x) ^ 2 / 2)) (x : ℝ) : ‖φ x‖ = 1 := by
  have h : ‖φ x‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hk]; simp
  rw [← Real.sqrt_sq (norm_nonneg (φ x)), h, Real.sqrt_one]

theorem gaussFeat_integrable {φ : ℝ → H} (hk : ∀ a x, ⟪φ a, φ x⟫_ℝ = Real.exp (-(a - x) ^ 2 / 2)) (P : Measure ℝ)
    [IsFiniteMeasure P] : Integrable φ P :=
  Integrable.of_bound (gaussFeat_continuous hk).stronglyMeasurable.aestronglyMeasurable 1
    (ae_of_all _ fun x => (gaussFeat_norm hk x).le)

variable [CompleteSpace H]

/-- `‖μ_P − μ_Q‖ = MMD(P,Q)` for Gaussian features. -/
theorem gauss_norm_meanEmb (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : ℝ → H}
    (hk : ∀ a x, ⟪φ a, φ x⟫_ℝ = Real.exp (-(a - x) ^ 2 / 2)) :
    ‖(∫ a, φ a ∂P) - ∫ b, φ b ∂Q‖ = mmdGauss P Q := by
  have hg : ∀ a x, Wave30tz.gaussK a x = ⟪φ a, φ x⟫_ℝ := fun a x => (hk a x).symm
  unfold mmdGauss
  simp_rw [hg]
  rw [← norm_sq_meanEmb_sub (gaussFeat_integrable hk P) (gaussFeat_integrable hk Q), Real.sqrt_sq (norm_nonneg _)]

/-- `f₀ = ⟪(μ_P − μ_Q)/‖μ_P − μ_Q‖, φ ·⟫` for Gaussian features. -/
theorem gauss_exWitness_eq (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : ℝ → H}
    (hk : ∀ a x, ⟪φ a, φ x⟫_ℝ = Real.exp (-(a - x) ^ 2 / 2)) (z : ℝ) :
    exWitness P Q z =
      ⟪‖(∫ a, φ a ∂P) - ∫ b, φ b ∂Q‖⁻¹ • ((∫ a, φ a ∂P) - ∫ b, φ b ∂Q), φ z⟫_ℝ := by
  have hg : ∀ a x, Wave30tz.gaussK a x = ⟪φ a, φ x⟫_ℝ := fun a x => (hk a x).symm
  unfold exWitness
  rw [real_inner_smul_left, inner_meanEmb_sub (gaussFeat_integrable hk P) (gaussFeat_integrable hk Q) z,
    gauss_norm_meanEmb P Q hk, div_eq_inv_mul]
  simp_rw [hg]

/-- **The deterministic step**: if the `α = 0` witness of a sample `(x, y)` has `KS⁺ ≠ 2/5` under the example laws, then the two
mean deviations sum to at least `g₀·MMD/4` (`g₀` a lower bound on the gaps of `f₀` on the atoms). -/
theorem meanDev_large_of_ks_ne {φ : ℝ → H} (hk : ∀ a x, ⟪φ a, φ x⟫_ℝ = Real.exp (-(a - x) ^ 2 / 2)) {g₀ : ℝ}
    (hg₀ : 0 < g₀) (hgap : ∀ a ∈ exAtoms, ∀ b ∈ exAtoms, a ≠ b → g₀ ≤ |exWitness exP exQ a - exWitness exP exQ b|)
    {p q : ℕ} (x : Fin p → ℝ) (y : Fin q → ℝ) (hne : ksPlus exP exQ (fun z => ⟪alphaZeroWit φ x y, φ z⟫_ℝ) ≠ 2 / 5) :
    g₀ * mmdGauss exP exQ / 4 ≤ ‖meanDev exP φ p x‖ + ‖meanDev exQ φ q y‖ := by
  by_contra hlt
  push Not at hlt
  apply hne
  refine ex_ks_stable_route.2.2.2 g₀ hg₀ hgap _ fun a _ => ?_
  set c : H := (∫ a, φ a ∂exP) - ∫ b, φ b ∂exQ with hc
  set d : H := (p : ℝ)⁻¹ • ∑ i, φ (x i) - (q : ℝ)⁻¹ • ∑ j, φ (y j) with hd
  have hcn : ‖c‖ = mmdGauss exP exQ := gauss_norm_meanEmb exP exQ hk
  have hc0 : 0 < ‖c‖ := hcn ▸ mmd_pos
  have hW : alphaZeroWit φ x y = ‖d‖⁻¹ • d := witness_unif φ x y
  have hdc : d - c = meanDev exP φ p x - meanDev exQ φ q y := by
    rw [hd, hc]; unfold meanDev; abel
  have hdc' : ‖d - c‖ < g₀ * ‖c‖ / 4 := by
    rw [hdc, hcn]
    exact (norm_sub_le _ _).trans_lt hlt
  rw [hW, gauss_exWitness_eq exP exQ hk a]
  calc |⟪‖d‖⁻¹ • d, φ a⟫_ℝ - ⟪‖c‖⁻¹ • c, φ a⟫_ℝ| ≤ ‖‖d‖⁻¹ • d - ‖c‖⁻¹ • c‖ * ‖φ a‖ := Alpha0Witness.abs_inner_sub_le _ _ _
    _ ≤ 2 * ‖d - c‖ / ‖c‖ * 1 := by
        rw [gaussFeat_norm hk a]
        exact mul_le_mul_of_nonneg_right (norm_normalize_sub_le (norm_pos_iff.1 hc0) d) zero_le_one
    _ < 2 * (g₀ * ‖c‖ / 4) / ‖c‖ * 1 := by gcongr
    _ = g₀ / 2 := by field_simp; ring

/-- **The probabilistic step**: for a batch with nonempty fitting sides, the two mean deviations of its fitting sample sum to at least
`t` with probability at most `2/(t√n_{<b}) + 2/(t√m_{<b})` (Markov). -/
theorem sampleLaw_meanDev_sum_ge {φ : ℝ → H} (hk : ∀ a x, ⟪φ a, φ x⟫_ℝ = Real.exp (-(a - x) ^ 2 / 2)) {n m : ℕ}
    (lx : Fin n → ℕ) (ly : Fin m → ℕ) (b : ℕ) (hn : fitCard lx b ≠ 0) (hm : fitCard ly b ≠ 0) {t : ℝ} (ht : 0 < t) :
    sampleLaw exP exQ n m {ω | t ≤ ‖meanDev exP φ (fitCard lx b) (fitSample lx b ω.1)‖ +
        ‖meanDev exQ φ (fitCard ly b) (fitSample ly b ω.2)‖} ≤
      ENNReal.ofReal (1 / (t / 2 * √(fitCard lx b : ℝ))) + ENNReal.ofReal (1 / (t / 2 * √(fitCard ly b : ℝ))) := by
  have hφ : StronglyMeasurable φ := (gaussFeat_continuous hk).stronglyMeasurable
  have hφ1 : ∀ x, ‖φ x‖ ≤ 1 := fun x => (gaussFeat_norm hk x).le
  unfold sampleLaw
  refine (prod_measure_le_add _ _ (fun x => ‖meanDev exP φ (fitCard lx b) (fitSample lx b x)‖)
    (fun y => ‖meanDev exQ φ (fitCard ly b) (fitSample ly b y)‖) t).trans ?_
  gcongr
  · exact measure_meanDev_ge_le exP hφ hφ1 hn (PaperRun.measurable_fitSample lx b) (Lower.map_fitSample exP lx b)
      (by positivity)
  · exact measure_meanDev_ge_le exQ hφ hφ1 hm (PaperRun.measurable_fitSample ly b) (Lower.map_fitSample exQ ly b)
      (by positivity)

end Gauss

/-- `1/(t/2 · √k) ≤ ε/(2B)` once `k ≥ (4B/(tε))²`. -/
theorem markov_term_le {t ε B k : ℝ} (ht : 0 < t) (hε : 0 < ε) (hB : 0 < B) (hk : (4 * B / (t * ε)) ^ 2 ≤ k) :
    1 / (t / 2 * √k) ≤ ε / (2 * B) := by
  have hpos : 0 < 4 * B / (t * ε) := by positivity
  have h1 : 4 * B / (t * ε) ≤ √k := by
    have := Real.sqrt_le_sqrt hk
    rwa [Real.sqrt_sq hpos.le] at this
  have hsk : 0 < √k := lt_of_lt_of_le hpos h1
  have h2 : 4 * B ≤ √k * (t * ε) := (div_le_iff₀ (by positivity)).1 h1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem alpha0_reject_le_route : Claims.alpha0_reject_le := by
  intro H _ _ _ _ φ J α δ lmax c C0 Bmax R hk hδ0 hδ1 hl0 hl1 hc hR hramp j hj ε hε
  have hφ : StronglyMeasurable φ := (gaussFeat_continuous hk).stronglyMeasurable
  obtain ⟨g₀, hg₀, hgap⟩ := exists_pos_le_gaps exAtoms (exWitness exP exQ) exWitness_injOn
  set t : ℝ := g₀ * mmdGauss exP exQ / 4 with ht
  have ht0 : 0 < t := by have := mmd_pos; positivity
  have hB0 : (0 : ℝ) < (Bmax : ℝ) + 1 := by positivity
  set M : ℝ := max 1 ((4 * ((Bmax : ℝ) + 1) / (t * ε)) ^ 2) with hM
  refine ⟨⌈(M + C0) / c⌉₊, fun n m hn hm => ?_⟩
  have hsize : ∀ n' : ℕ, ⌈(M + C0) / c⌉₊ ≤ n' → M ≤ c * n' - C0 := fun n' hn' => by
    have h1 : (M + C0) / c ≤ n' := (Nat.ceil_le).1 hn'
    rw [div_le_iff₀ hc] at h1
    linarith
  obtain ⟨hadm, hsz⟩ := hR n m
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMs : (4 * ((Bmax : ℝ) + 1) / (t * ε)) ^ 2 ≤ M := le_max_right _ _
  have hfx : ∀ k : Fin (R n m).N, M ≤ (fitCard (R n m).lx ((R n m).bat k) : ℝ) := fun k =>
    (hsize n hn).trans (hsz.2.1 k)
  have hfy : ∀ k : Fin (R n m).N, M ≤ (fitCard (R n m).ly ((R n m).bat k) : ℝ) := fun k =>
    (hsize m hm).trans (hsz.2.2.1 k)
  have hfx1 : ∀ k : Fin (R n m).N, 1 ≤ fitCard (R n m).lx ((R n m).bat k) := fun k => by
    exact_mod_cast hM1.trans (hfx k)
  have hfy1 : ∀ k : Fin (R n m).N, 1 ≤ fitCard (R n m).ly ((R n m).bat k) := fun k => by
    exact_mod_cast hM1.trans (hfy k)
  -- the certified validity bound of the variant, with `F_b = f̂_{0,b}`
  have hval := alpha0_valid_route ℝ exP exQ n m (R n m).N (R n m).lx (R n m).ly (R n m).bat (R n m).A (R n m).B (α j) δ lmax
    (alphaZeroFn φ (R n m).lx (R n m).ly) ((R n m).g j) ((R n m).lam j) hadm.1 (by linarith) hδ0 hδ1 hl0 hl1 (hadm.2.1 j)
    (hadm.2.2 j) (fun k => measurable_alphaZeroFn hφ (R n m).lx (R n m).ly ((R n m).bat k))
    (fun k x x' y y' hx hy => alphaZeroFn_congr φ _ _ _ hx hy) (fun k x y => hramp n m j k x y (hfx1 k) (hfy1 k))
  -- the bad event
  set I : Finset ℕ := Finset.univ.image (R n m).bat with hI
  set E : ℕ → Set ((Fin n → ℝ) × (Fin m → ℝ)) := fun b =>
    {ω | t ≤ ‖meanDev exP φ (fitCard (R n m).lx b) (fitSample (R n m).lx b ω.1)‖ +
      ‖meanDev exQ φ (fitCard (R n m).ly b) (fitSample (R n m).ly b ω.2)‖} with hE
  have hsub : {ω : (Fin n → ℝ) × (Fin m → ℝ) | ∃ k : Fin (R n m).N,
      α j < ksPlus exP exQ (alphaZeroFn φ (R n m).lx (R n m).ly ((R n m).bat k) ω.1 ω.2)} ⊆ ⋃ b ∈ I, E b := by
    rintro ω ⟨k, hks⟩
    refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ k))) ?_
    refine meanDev_large_of_ks_ne hk hg₀ hgap _ _ fun h => ?_
    have h' : ksPlus exP exQ (alphaZeroFn φ (R n m).lx (R n m).ly ((R n m).bat k) ω.1 ω.2) = 2 / 5 := h
    rw [h'] at hks
    linarith
  have hEb : ∀ b ∈ I, sampleLaw exP exQ n m (E b) ≤ ENNReal.ofReal (ε / ((Bmax : ℝ) + 1)) := by
    intro b hb
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hb
    refine (sampleLaw_meanDev_sum_ge hk _ _ _ (by have := hfx1 k; omega) (by have := hfy1 k; omega) ht0).trans ?_
    have e1 := markov_term_le ht0 hε hB0 (hMs.trans (hfx k))
    have e2 := markov_term_le ht0 hε hB0 (hMs.trans (hfy k))
    calc ENNReal.ofReal (1 / (t / 2 * √(fitCard (R n m).lx ((R n m).bat k) : ℝ))) +
          ENNReal.ofReal (1 / (t / 2 * √(fitCard (R n m).ly ((R n m).bat k) : ℝ)))
        ≤ ENNReal.ofReal (ε / (2 * ((Bmax : ℝ) + 1))) + ENNReal.ofReal (ε / (2 * ((Bmax : ℝ) + 1))) :=
          add_le_add (ENNReal.ofReal_le_ofReal e1) (ENNReal.ofReal_le_ofReal e2)
      _ = ENNReal.ofReal (ε / ((Bmax : ℝ) + 1)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          field_simp
          ring
  have hIcard : (I.card : ℝ) ≤ (Bmax : ℝ) + 1 := by
    have hsubI : I ⊆ Finset.range (Bmax + 1) := fun b hb => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hb
      exact Finset.mem_range.2 (Nat.lt_succ_of_le (hsz.1 k))
    have := Finset.card_le_card hsubI
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hbad : sampleLaw exP exQ n m {ω : (Fin n → ℝ) × (Fin m → ℝ) | ∃ k : Fin (R n m).N,
      α j < ksPlus exP exQ (alphaZeroFn φ (R n m).lx (R n m).ly ((R n m).bat k) ω.1 ω.2)} ≤ ENNReal.ofReal ε := by
    calc _ ≤ sampleLaw exP exQ n m (⋃ b ∈ I, E b) := measure_mono hsub
      _ ≤ ∑ b ∈ I, sampleLaw exP exQ n m (E b) := measure_biUnion_finset_le _ _
      _ ≤ ∑ b ∈ I, ENNReal.ofReal (ε / ((Bmax : ℝ) + 1)) := Finset.sum_le_sum hEb
      _ = I.card • ENNReal.ofReal (ε / ((Bmax : ℝ) + 1)) := Finset.sum_const _
      _ = ENNReal.ofReal (I.card • (ε / ((Bmax : ℝ) + 1))) := ENNReal.ofReal_nsmul.symm
      _ ≤ ENNReal.ofReal ε := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [nsmul_eq_mul]
          calc (I.card : ℝ) * (ε / ((Bmax : ℝ) + 1)) ≤ ((Bmax : ℝ) + 1) * (ε / ((Bmax : ℝ) + 1)) :=
                mul_le_mul_of_nonneg_right hIcard (by positivity)
            _ = ε := by field_simp
  calc _ ≤ _ := hval
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal ε := add_le_add le_rfl hbad
    _ = ENNReal.ofReal (δ + ε) := (ENNReal.ofReal_add hδ0.le hε.le).symm

/-- On a grid, `α_i ≤ α̂_lo` (with `α_i > 0`) forces the rejection of `H_{0,α_i}`. -/
theorem alphaLo_ge_rej {J : ℕ} {α : Fin J → ℝ} (hα : IsGrid α) {rej : Fin J → Prop} {i : Fin J} (hi : 0 < α i)
    (h : α i ≤ StatFormal.TrimmedMMD.Lower.alphaLo α rej) : rej i := by
  classical
  unfold StatFormal.TrimmedMMD.Lower.alphaLo at h
  split_ifs at h with hne
  · obtain ⟨j₀, hj₀, he⟩ := Finset.exists_mem_eq_sup' hne α
    rw [he] at h
    exact (Finset.mem_filter.1 hj₀).2 i (hα.1.le_iff_le.1 h)
  · linarith

theorem alpha0_inconsistent_route : Claims.alpha0_inconsistent := by
  intro H _ _ _ _ φ J α δ lmax c C0 Bmax R hk hgrid hδ0 hδ1 hl0 hl1 hc hR hramp
  refine ⟨tv_ex, fun i hi1 hi2 => ?_⟩
  have hbound : ∀ ε > 0, ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m →
      sampleLaw exP exQ n m {ω | α i ≤ (R n m).alphaLo α δ ω.1 ω.2} ≤ ENNReal.ofReal (δ + ε) := by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := alpha0_reject_le_route H φ J α δ lmax c C0 Bmax R hk hδ0 hδ1 hl0 hl1 hc hR hramp i hi1 ε hε
    refine ⟨N₀, fun n m hn hm => (measure_mono fun ω hω => ?_).trans (hN₀ n m hn hm)⟩
    exact alphaLo_ge_rej hgrid (by linarith) hω
  refine ⟨hbound, fun hcons => ?_⟩
  have hε : 0 < (1 - δ) / 3 := by linarith
  obtain ⟨N₀, hN₀⟩ := hcons _ hε
  obtain ⟨N₁, hN₁⟩ := hbound _ hε
  have h1 := hN₀ (max N₀ N₁) (max N₀ N₁) (le_max_left _ _) (le_max_left _ _)
  have h2 := hN₁ (max N₀ N₁) (max N₀ N₁) (le_max_right _ _) (le_max_right _ _)
  have hlt : ENNReal.ofReal (δ + (1 - δ) / 3) < ENNReal.ofReal (1 - (1 - δ) / 3) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  exact absurd (h1.trans h2) (not_le.2 hlt)

end StatFormal.Wave31tr.RouteAlpha0
