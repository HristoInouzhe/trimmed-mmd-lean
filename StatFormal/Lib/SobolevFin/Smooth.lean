import StatFormal.Lib.TIKernel.Native
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Smooth compactly supported functions have finite Sobolev functionals (library, untrusted)

On a finite-dimensional real inner-product space `V`, with Mathlib's Fourier transform `𝓕`
(`𝐞 t = e^{2πit}`):

* `integrable_sq_mul_sobolevWeight`: for a Schwartz function `F` and every `s ∈ ℝ`,
  `ξ ↦ ‖F ξ‖² (1 + 4π²‖ξ‖²)^s` is integrable. Proof: with `n = ⌈s⌉₊`, the weight is at most
  `(1 + 4π²‖ξ‖²)^n ≤ 2^n (1 + (4π²)^n ‖ξ‖^{2n})` (`sobolevWeight_le`), and `‖F‖² ≤ C ‖F‖` with
  `C = sup ‖F‖`, so the integrand is dominated by `C 2^n (‖F‖ + (4π²)^n ‖ξ‖^{2n} ‖F‖)`,
  integrable by `SchwartzMap.integrable_pow_mul`.
* `sobolevS_lt_top_of_schwartz`, `sobolevS_lt_top_of_contDiff` (Wave31tp L9; Folland,
  *Real Analysis*, Thm 8.22): a Schwartz `u`, in particular a `C^∞` compactly supported
  `g : V → ℂ` (`HasCompactSupport.toSchwartzMap`), has `sobolevS s u < ∞` for every `s ∈ ℝ`:
  `𝓕 u` is Schwartz (`SchwartzMap.fourier_coe`) and the L² transform `ft2 u` equals it a.e.
  (`FourierL2.fourier_toLp_ae`).
* `rep_of_contDiff_hasCompactSupport` and `containsSmoothCompact_of_spec` (Wave31tp L19 (b);
  Wendland, Cor. 10.13): under a spectral lower bound `c (1 + 4π²‖ξ‖²)^{−s} ≤ specDens k₀ ξ`,
  every real `C^∞` compactly supported function is represented in any feature map with profile
  `k₀`, with `‖g‖² ≤ sobolevS s g / c` (L9 and the Sobolev inclusion
  `TIKernel.sobolev_incl_facts`); on `ℝ^d = EuclideanSpace ℝ (Fin d)` this is the bridge
  `Wave31tg.ContainsSmoothCompact φ`.
-/

noncomputable section
open MeasureTheory Filter Topology Set FourierTransform SchwartzMap
open scoped ENNReal InnerProductSpace RealInnerProductSpace ContDiff

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace StatFormal.SobolevFin

open StatFormal.Wave31tp

/-- `(1 + t)^n ≤ 2^n (1 + t^n)` for `t ≥ 0`. -/
lemma one_add_pow_le {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : (1 + t) ^ n ≤ 2 ^ n * (1 + t ^ n) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (1 + t ^ n) := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg ht n])
  · calc (1 + t) ^ n ≤ (2 * t) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * t ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (1 + t ^ n) := by gcongr; linarith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- The Sobolev weight is dominated by a polynomial: `(1 + 4π²‖ξ‖²)^s ≤ 2^n (1 + (4π²)^n ‖ξ‖^{2n})` with `n = ⌈s⌉₊`. -/
lemma sobolevWeight_le (s : ℝ) (ξ : V) :
    (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s ≤
      2 ^ ⌈s⌉₊ * (1 + (4 * Real.pi ^ 2) ^ ⌈s⌉₊ * ‖ξ‖ ^ (2 * ⌈s⌉₊)) := by
  have h1 : 1 ≤ 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := le_add_of_nonneg_right (by positivity)
  calc (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (⌈s⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil s)
    _ = (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ ⌈s⌉₊ := Real.rpow_natCast _ _
    _ ≤ 2 ^ ⌈s⌉₊ * (1 + (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ ⌈s⌉₊) := one_add_pow_le (by positivity) _
    _ = _ := by rw [mul_pow, ← pow_mul]

/-- The Sobolev weight `ξ ↦ (1 + 4π²‖ξ‖²)^s` is continuous. -/
lemma continuous_sobolevWeight (s : ℝ) : Continuous (fun ξ : V => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s) :=
  (by fun_prop : Continuous fun ξ : V => 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2).rpow_const
    fun ξ => Or.inl (by positivity)

/-- A Schwartz function has every weighted L² norm finite: `ξ ↦ ‖F ξ‖² (1 + 4π²‖ξ‖²)^s` is integrable for every `s ∈ ℝ`. -/
theorem integrable_sq_mul_sobolevWeight (F : 𝓢(V, ℂ)) (s : ℝ) :
    Integrable (fun ξ => ‖F ξ‖ ^ 2 * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s) := by
  set n := ⌈s⌉₊
  set C := SchwartzMap.seminorm ℝ 0 0 F
  have hb : Integrable (fun ξ : V =>
      C * 2 ^ n * (‖ξ‖ ^ 0 * ‖F ξ‖ + (4 * Real.pi ^ 2) ^ n * (‖ξ‖ ^ (2 * n) * ‖F ξ‖))) :=
    ((F.integrable_pow_mul volume 0).add ((F.integrable_pow_mul volume (2 * n)).const_mul _)).const_mul _
  refine hb.mono' ((F.continuous.norm.pow 2).mul (continuous_sobolevWeight s)).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  have hF : ‖F ξ‖ ≤ C := norm_le_seminorm ℝ F ξ
  have hw := sobolevWeight_le s ξ
  have hw0 : 0 ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s := Real.rpow_nonneg (by positivity) s
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hw0)]
  calc ‖F ξ‖ ^ 2 * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s
      ≤ (C * ‖F ξ‖) * (2 ^ n * (1 + (4 * Real.pi ^ 2) ^ n * ‖ξ‖ ^ (2 * n))) := by
        rw [sq]
        gcongr
    _ = _ := by ring

/-- A Schwartz function `u : V → ℂ` has a finite Sobolev functional of every order `s ∈ ℝ`: its Fourier transform is a
Schwartz function and agrees a.e. with the L² transform `ft2 u`. -/
theorem sobolevS_lt_top_of_schwartz (u : 𝓢(V, ℂ)) (s : ℝ) : sobolevS s ⇑u < ⊤ := by
  have hae : ft2 ⇑u =ᵐ[volume] ⇑(𝓕 u : 𝓢(V, ℂ)) := by
    rw [TIKernel.ft2_eq' (u.memLp 2 volume), SchwartzMap.fourier_coe]
    exact FourierL2.fourier_toLp_ae u.integrable (u.memLp 2 volume)
  have hI := integrable_sq_mul_sobolevWeight (𝓕 u : 𝓢(V, ℂ)) s
  unfold sobolevS
  calc ∫⁻ ξ, ‖ft2 ⇑u ξ‖ₑ ^ 2 * ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s)
      = ∫⁻ ξ, ENNReal.ofReal (‖(𝓕 u : 𝓢(V, ℂ)) ξ‖ ^ 2 * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with ξ h
        rw [h, ENNReal.ofReal_mul (sq_nonneg _), ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ < ⊤ := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) s))).mp hI.hasFiniteIntegral

/-- **Wave31tp L9.** A `C^∞` compactly supported `g : V → ℂ` has a finite Sobolev functional `sobolevS s g` of every order
`s ∈ ℝ` (it is a Schwartz function, `HasCompactSupport.toSchwartzMap`). -/
theorem sobolevS_lt_top_of_contDiff {g : V → ℂ} (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) (s : ℝ) :
    sobolevS s g < ⊤ :=
  sobolevS_lt_top_of_schwartz (hgs.toSchwartzMap hg) s

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Wave31tp L19 (b), on any `V`.** Under the spectral lower bound `c (1 + 4π²‖ξ‖²)^{−s} ≤ specDens k₀ ξ` (`c > 0`), every
real `C^∞` compactly supported `f` is represented in any feature map `φ` with continuous integrable profile `k₀`, by some `g` with
`‖g‖² ≤ sobolevS s f / c`. -/
theorem rep_of_contDiff_hasCompactSupport {φ : V → H} {k₀ : V → ℝ} (hφ : ∀ x y, ⟪φ x, φ y⟫ = k₀ (x - y))
    (hc : Continuous k₀) (hi : Integrable k₀) {c s : ℝ} (hc0 : 0 < c)
    (hlow : ∀ ξ, c * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) ≤ specDens k₀ ξ) {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfs : HasCompactSupport f) :
    ∃ g : H, (∀ x, ⟪g, φ x⟫ = f x) ∧
      ENNReal.ofReal (‖g‖ ^ 2) ≤ sobolevS s (fun x => (f x : ℂ)) / ENNReal.ofReal c :=
  TIKernel.sobolev_incl_facts hφ hc hi hc0 hlow hf.continuous (hf.continuous.memLp_of_hasCompactSupport hfs)
    (sobolevS_lt_top_of_contDiff (Complex.ofRealCLM.contDiff.comp hf) (hfs.comp_left Complex.ofReal_zero) s)

/-- **Wave31tp L19 (b)**, the bridge of Wave 31tg: with a spectral lower bound, a feature map of a translation-invariant kernel
on `ℝ^d` represents every real `C^∞` compactly supported function (`Wave31tg.ContainsSmoothCompact φ`). -/
theorem containsSmoothCompact_of_spec {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → H} {k₀ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ∀ x y, ⟪φ x, φ y⟫ = k₀ (x - y)) (hc : Continuous k₀) (hi : Integrable k₀) {c s : ℝ} (hc0 : 0 < c)
    (hlow : ∀ ξ, c * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) ≤ specDens k₀ ξ) :
    Wave31tg.ContainsSmoothCompact φ :=
  fun _ hf hfs => (rep_of_contDiff_hasCompactSupport hφ hc hi hc0 hlow hf hfs).imp fun _ h => h.1

end Rep

end StatFormal.SobolevFin
