import StatFormal.Wave30tx.RouteBasic
import StatFormal.Archive.Wave12c.RouteTrimConsist
import StatFormal.Wave30tr.Proofs
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Route: `cor:trimrate (v2)` (untrusted proof material)

Markov's inequality on dyadic shells (the elementary rate theorem), with `lem:basicineq` and `lem:localmod` as hypotheses.

* Events: the two-sided event of Theorem A (`Wave30tr.thmA_twosided`, level `ε/4`, `D_φ = 2κ`), two Hoeffding bounds for the
  empirical cdf of `d*(X_i)` and two for `d*(Y_j)` at the deterministic points `t_α ± λ_X`, `u_α ± λ_Y` (level `ε/16` each), and
  the complements of the Markov sets `{c_i ≤ Z(2^{i+1}b)}`, `b = Λ₀V/(Dq)`, `i < K` (finitely many: `r̂ ≤ 2`). No measurability of
  `r̂` is needed: if `r̂ > b`, the first shell containing `r̂` puts the sample in one of the Markov sets.
* Constants depend on `ε` only: `ϰ = √(log(16/ε)/2) + 1`, `Λ₀ = (128 + 32ϰ)/ε`, `C_A = 2√2 + 4 + 2√log(8/ε)`, `Λ_w = C_A + 2Λ₀`,
  `Λ = max(4Λ_w, 2ϰ)`.
* Deterministic steps: the cut counts (`xcounts`, `ycounts`), the order-statistic bound (`Wave12c.tHat_bounds`), the band
  (`Wave12c.band_incl`, half-width `2κ‖d̂ − d*‖ + λ_X`) and the mass and density bounds with tie functions (`kept_bounds`).
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace Pointwise

namespace StatFormal.Wave30tx.RCor

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.Projection StatFormal.Wave12c
  StatFormal.Wave4b StatFormal.Wave30tp StatFormal.Wave30tr StatFormal.Wave30tx

section Helpers

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

theorem witFn_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (c : ℝ) (d : H) (φ : 𝒳 → H)
    (x : 𝒳) : witFn (c • d) φ x = c * witFn d φ x := by
  unfold witFn; rw [real_inner_smul_left]

theorem kfloor_lt {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : kfloor n α < n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hknp : (kfloor n α : ℝ) ≤ n * (1 - α) := Nat.floor_le (by nlinarith)
  have : (kfloor n α : ℝ) < n := by nlinarith
  exact_mod_cast this

/-- The `Y`-side margins from an `α`-quantile and a lower density bound. -/
theorem ymargins {Q : Measure 𝒳} [IsProbabilityMeasure Q] {f : 𝒳 → ℝ} (hf : Measurable f) {α u ρ c : ℝ}
    (hq : IsQuantile Q f α u) (hd : QDensityLower Q f u ρ c) {ε : ℝ} (hε0 : 0 < ε) (hερ : ε ≤ ρ) :
    α + c * ε ≤ Q.real {x | f x ≤ u + ε} ∧ Q.real {x | f x ≤ u - ε} ≤ α - c * ε := by
  obtain ⟨g, -, hg, hdd⟩ := hd
  constructor
  · have h2 := density_lower (P := Q) (f := f) hg hdd (a := u) (b := u + ε) (by linarith)
      (A := Ioc u (u + ε)) measurableSet_Ioc
      (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩) Real.volume_Ioc
    have hunion : {x | f x ≤ u + ε} = {x | f x ≤ u} ∪ f ⁻¹' Ioc u (u + ε) := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_preimage, Set.mem_Ioc]
      constructor
      · intro h; by_cases h' : f x ≤ u
        · exact Or.inl h'
        · exact Or.inr ⟨not_le.1 h', h⟩
      · rintro (h | h)
        · linarith
        · exact h.2
    have hdisj : Disjoint {x | f x ≤ u} (f ⁻¹' Ioc u (u + ε)) :=
      Set.disjoint_left.2 fun x hx hx' => by
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioc] at hx hx'; linarith [hx'.1]
    rw [hunion, measureReal_union hdisj (hf measurableSet_Ioc)]
    have : u + ε - u = ε := by ring
    rw [this] at h2
    linarith [hq.2]
  · have h2 := density_lower (P := Q) (f := f) hg hdd (a := u - ε) (b := u) (by linarith)
      (A := Ioo (u - ε) u) measurableSet_Ioo
      (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩) Real.volume_Ioo
    have hsub : {x | f x ≤ u - ε} ∪ f ⁻¹' Ioo (u - ε) u ⊆ {x | f x < u} := by
      rintro x (hx | hx)
      · simp only [Set.mem_ofPred_eq] at hx ⊢; linarith
      · simp only [Set.mem_preimage, Set.mem_Ioo] at hx; exact hx.2
    have hdisj : Disjoint {x | f x ≤ u - ε} (f ⁻¹' Ioo (u - ε) u) :=
      Set.disjoint_left.2 fun x hx hx' => by
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioo] at hx hx'; linarith [hx'.1]
    have h3 := measureReal_mono (μ := Q) hsub
    rw [measureReal_union hdisj (hf measurableSet_Ioo)] at h3
    have : u - (u - ε) = ε := by ring
    rw [this] at h2
    linarith [hq.1]

/-- The `X`-side counts at the cut (Step 2 of the proof of `thm:trimconsist`). -/
theorem xcounts {P : Measure 𝒳} {f : 𝒳 → ℝ} {n : ℕ} (hn : 1 ≤ n) {α q u cf sn : ℝ}
    (hα1 : α < 1) (hcfu : cf * u = sn + 1 / n)
    (hmar1 : (1 - α) + cf * u ≤ P.real {y | f y ≤ q + u})
    (hmar2 : P.real {y | f y ≤ q - u} ≤ (1 - α) - cf * u) (x : Fin n → 𝒳)
    (hza : P.real {y | f y ≤ q + u} - sn ≤ empCdf f x (q + u))
    (hzb : empCdf f x (q - u) ≤ P.real {y | f y ≤ q - u} + sn) :
    kfloor n α + 1 ≤ (Finset.univ.filter fun i => f (x i) ≤ q + u).card ∧
      (Finset.univ.filter fun i => f (x i) ≤ q - u).card < kfloor n α + 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set k := kfloor n α with hk
  have hknp : (k : ℝ) ≤ n * (1 - α) := Nat.floor_le (by nlinarith)
  have hknp1 : (n : ℝ) * (1 - α) < k + 1 := Nat.lt_floor_add_one _
  rw [empCdf_eq_card] at hza hzb
  constructor
  · have h2 : ((k : ℝ) + 1) ≤ ((Finset.univ.filter fun i => f (x i) ≤ q + u).card : ℝ) := by
      rw [hcfu] at hmar1
      have h4 : (n : ℝ)⁻¹ * ((1 - α) * n + 1) ≤
          (n : ℝ)⁻¹ * ((Finset.univ.filter fun i => f (x i) ≤ q + u).card : ℝ) := by
        have : (n : ℝ)⁻¹ * ((1 - α) * n + 1) = (1 - α) + 1 / n := by field_simp
        linarith
      have h5 := le_of_mul_le_mul_left h4 (by positivity)
      linarith
    exact_mod_cast h2
  · rw [hcfu] at hmar2
    have h4 : (n : ℝ)⁻¹ * ((Finset.univ.filter fun i => f (x i) ≤ q - u).card : ℝ) ≤
        (n : ℝ)⁻¹ * ((1 - α) * n - 1) := by
      have : (n : ℝ)⁻¹ * ((1 - α) * n - 1) = (1 - α) - 1 / n := by field_simp
      linarith
    have h5 := le_of_mul_le_mul_left h4 (by positivity)
    have h6 : ((Finset.univ.filter fun i => f (x i) ≤ q - u).card : ℝ) < k + 1 := by linarith
    exact_mod_cast h6

/-- The `Y`-side counts at the cut: `(m − m_α)`-th smallest, i.e. index `m − m_α − 1`. -/
theorem ycounts {Q : Measure 𝒳} {f : 𝒳 → ℝ} {m : ℕ} (hm : 1 ≤ m) {α u c sm v : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hcv : c * v = sm + 1 / m)
    (hmar1 : α + c * v ≤ Q.real {y | f y ≤ u + v})
    (hmar2 : Q.real {y | f y ≤ u - v} ≤ α - c * v) (y : Fin m → 𝒳)
    (hza : Q.real {y | f y ≤ u + v} - sm ≤ empCdf f y (u + v))
    (hzb : empCdf f y (u - v) ≤ Q.real {y | f y ≤ u - v} + sm) :
    m - kfloor m α - 1 + 1 ≤ (Finset.univ.filter fun j => f (y j) ≤ u + v).card ∧
      (Finset.univ.filter fun j => f (y j) ≤ u - v).card < m - kfloor m α - 1 + 1 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set k := kfloor m α with hk
  have hkm : k < m := kfloor_lt hm hα0 hα1
  have hknp : (k : ℝ) ≤ m * (1 - α) := Nat.floor_le (by nlinarith)
  have hknp1 : (m : ℝ) * (1 - α) < k + 1 := Nat.lt_floor_add_one _
  have hidx : m - k - 1 + 1 = m - k := by omega
  have hcast : ((m - k - 1 + 1 : ℕ) : ℝ) = m - k := by
    rw [hidx, Nat.cast_sub hkm.le]
  rw [empCdf_eq_card] at hza hzb
  constructor
  · have h2 : ((m - k - 1 + 1 : ℕ) : ℝ) ≤ ((Finset.univ.filter fun j => f (y j) ≤ u + v).card : ℝ) := by
      rw [hcast]
      rw [hcv] at hmar1
      have h4 : (m : ℝ)⁻¹ * (α * m + 1) ≤
          (m : ℝ)⁻¹ * ((Finset.univ.filter fun j => f (y j) ≤ u + v).card : ℝ) := by
        have : (m : ℝ)⁻¹ * (α * m + 1) = α + 1 / m := by field_simp
        linarith
      have h5 := le_of_mul_le_mul_left h4 (by positivity)
      nlinarith
    exact_mod_cast h2
  · rw [hcv] at hmar2
    have h4 : (m : ℝ)⁻¹ * ((Finset.univ.filter fun j => f (y j) ≤ u - v).card : ℝ) ≤
        (m : ℝ)⁻¹ * (α * m - 1) := by
      have : (m : ℝ)⁻¹ * (α * m - 1) = α - 1 / m := by field_simp
      linarith
    have h5 := le_of_mul_le_mul_left h4 (by positivity)
    have h6 : ((Finset.univ.filter fun j => f (y j) ≤ u - v).card : ℝ) < ((m - k - 1 + 1 : ℕ) : ℝ) := by
      rw [hcast]; nlinarith
    exact_mod_cast h6

/-- The mass and density bounds on a band of half-width `w ≤ ρ` that contains `Â △ A*` and the ties of `d̂`. -/
theorem kept_bounds {P : Measure 𝒳} [IsProbabilityMeasure P] {α ρ cf Cf w tα th : ℝ} {ds dh : 𝒳 → ℝ}
    (hds : Measurable ds) (hα1 : α < 1) (hcf : 0 ≤ cf) (hQ : QDensity P ds tα ρ cf Cf)
    (hw0 : 0 ≤ w) (hwρ : w ≤ ρ)
    (hincl : symmDiff {x | dh x < th} {x | ds x < tα} ⊆ {x | |ds x - tα| ≤ w})
    (hties : ∀ x, dh x = th → |ds x - tα| ≤ w) :
    P (symmDiff {x | dh x < th} {x | ds x < tα}) ≤ ENNReal.ofReal (2 * Cf * w) ∧
      ∀ ϑ ϑh : 𝒳 → ℝ, (∀ x, 0 ≤ ϑ x ∧ ϑ x ≤ 1 / (1 - α)) → (∀ x, 0 ≤ ϑh x ∧ ϑh x ≤ 1 / (1 - α)) →
        ∫ x, |plugDensityFn α ϑh dh th x - plugDensityFn α ϑ ds tα x| ∂P ≤ 2 * Cf * w / (1 - α) := by
  obtain ⟨g, -, hgb, hd⟩ := hQ
  have hCf : 0 ≤ Cf := by
    have := hgb tα ⟨by linarith, by linarith⟩
    linarith [this.1, this.2]
  have hRHS : 0 ≤ 2 * Cf * w := by positivity
  set B := {x | |ds x - tα| ≤ w} with hBdef
  have hBeq : B = ds ⁻¹' Icc (tα - w) (tα + w) := by
    ext x; simp only [hBdef, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, abs_le]
    constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
  have hBm : MeasurableSet B := by rw [hBeq]; exact hds measurableSet_Icc
  have hPB : P B ≤ ENNReal.ofReal (2 * Cf * w) := by
    rw [hBeq]
    have := density_upper (P := P) (f := ds) (fun s hs => (hgb s hs).2) hd
      (a := tα - w) (b := tα + w) (A := Icc (tα - w) (tα + w)) measurableSet_Icc
      (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩) Real.volume_Icc
    rwa [show Cf * (tα + w - (tα - w)) = 2 * Cf * w by ring] at this
  refine ⟨(measure_mono hincl).trans hPB, fun ϑ ϑh hϑ hϑh => ?_⟩
  have hβ : 0 < 1 / (1 - α) := one_div_pos.2 (by linarith)
  have hpt : ∀ x, |plugDensityFn α ϑh dh th x - plugDensityFn α ϑ ds tα x| ≤
      B.indicator (fun _ => 1 / (1 - α)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      have ha : 0 ≤ plugDensityFn α ϑh dh th x ∧ plugDensityFn α ϑh dh th x ≤ 1 / (1 - α) := by
        unfold plugDensityFn; split_ifs <;> first | exact ⟨hβ.le, le_rfl⟩ | exact hϑh x | exact ⟨le_rfl, hβ.le⟩
      have hb : 0 ≤ plugDensityFn α ϑ ds tα x ∧ plugDensityFn α ϑ ds tα x ≤ 1 / (1 - α) := by
        unfold plugDensityFn; split_ifs <;> first | exact ⟨hβ.le, le_rfl⟩ | exact hϑ x | exact ⟨le_rfl, hβ.le⟩
      rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    · rw [Set.indicator_of_notMem hx]
      have hnot : x ∉ symmDiff {x | dh x < th} {x | ds x < tα} := fun h => hx (hincl h)
      have hne1 : dh x ≠ th := fun h => hx (hties x h)
      have hne2 : ds x ≠ tα := fun h => hx (by simp [hBdef, h, hw0])
      simp only [Set.mem_symmDiff, Set.mem_ofPred_eq, not_or, not_and, not_not] at hnot
      unfold plugDensityFn
      by_cases hlt : dh x < th
      · have := hnot.1 hlt
        simp [hlt, this]
      · have hlt2 : ¬ ds x < tα := fun h => hlt (hnot.2 h)
        simp [hlt, hlt2, hne1, hne2]
  by_cases hint : Integrable (fun x => |plugDensityFn α ϑh dh th x - plugDensityFn α ϑ ds tα x|) P
  · calc ∫ x, |plugDensityFn α ϑh dh th x - plugDensityFn α ϑ ds tα x| ∂P
        ≤ ∫ x, B.indicator (fun _ => 1 / (1 - α)) x ∂P :=
          integral_mono hint ((integrable_const _).indicator hBm) hpt
      _ = P.real B * (1 / (1 - α)) := by rw [integral_indicator_const _ hBm, smul_eq_mul]
      _ ≤ (2 * Cf * w) * (1 / (1 - α)) := by
          gcongr
          exact ENNReal.toReal_le_of_le_ofReal hRHS hPB
      _ = 2 * Cf * w / (1 - α) := by ring
  · rw [integral_undef hint]
    have : 0 < 1 - α := by linarith
    positivity

/-! ### Arithmetic -/

/-- One Markov shell: `E Z(2^{i+1}b)/c_i ≤ (32 + 8ϰ)/Λ₀ · 2^{−i}`. -/
theorem shell_bound {κ β V c D q b Λ0 l ϰ : ℝ} (hκ : 0 ≤ κ) (hβ : 0 < β) (hV : 0 < V) (hc : 0 < c)
    (hD : 0 < D) (hq : 0 < q) (hΛ0 : 1 ≤ Λ0) (hϰ : 0 ≤ ϰ) (hl : 0 ≤ l)
    (hb : b = Λ0 * V / (D * q)) (hV1 : β * κ ≤ V) (hV2 : β / c ≤ V ^ 2) (hlq : q * D * l ≤ 2 * ϰ / c)
    (i : ℕ) :
    (2 * (√2 + 2) * κ * (2 ^ (i + 1) * b) + 2 * l) / q / (D * (2 ^ i * b) ^ 2 / (2 * β)) ≤
      (32 + 8 * ϰ) / Λ0 * (1 / 2) ^ i := by
  set T : ℝ := 2 ^ i with hT
  have hT1 : 1 ≤ T := one_le_pow₀ (by norm_num)
  have hT0 : 0 < T := by linarith
  have hΛ0' : 0 < Λ0 := by linarith
  have hhalf : ((1 : ℝ) / 2) ^ i = 1 / T := by rw [hT, one_div_pow]
  rw [hhalf, pow_succ, ← hT]
  have hs2 : √2 ≤ 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    · exact Real.sqrt_le_sqrt (by norm_num)
  have hs20 : 0 ≤ √2 := Real.sqrt_nonneg _
  have e : (2 * (√2 + 2) * κ * (T * 2 * b) + 2 * l) / q / (D * (T * b) ^ 2 / (2 * β)) =
      8 * (√2 + 2) * (β * κ) / (Λ0 * V * T) + 4 * β * (q * D * l) / (T ^ 2 * Λ0 ^ 2 * V ^ 2) := by
    rw [hb]; field_simp; ring
  rw [e]
  have h1 : 8 * (√2 + 2) * (β * κ) / (Λ0 * V * T) ≤ 32 / (Λ0 * T) := by
    have hbk : 0 ≤ β * κ := mul_nonneg hβ.le hκ
    have h4 : √2 + 2 ≤ 4 := by linarith
    have : 8 * (√2 + 2) * (β * κ) ≤ 32 * V := by
      have := mul_le_mul_of_nonneg_left h4 hbk
      nlinarith
    calc 8 * (√2 + 2) * (β * κ) / (Λ0 * V * T) ≤ 32 * V / (Λ0 * V * T) := by gcongr
      _ = 32 / (Λ0 * T) := by field_simp
  have h2 : 4 * β * (q * D * l) / (T ^ 2 * Λ0 ^ 2 * V ^ 2) ≤ 8 * ϰ / (Λ0 * T) := by
    have hnum : 4 * β * (q * D * l) ≤ 8 * ϰ * V ^ 2 := by
      have h3 : 4 * β * (q * D * l) ≤ 4 * β * (2 * ϰ / c) := by gcongr
      have h4 : 4 * β * (2 * ϰ / c) = 8 * ϰ * (β / c) := by ring
      have h5 : 8 * ϰ * (β / c) ≤ 8 * ϰ * V ^ 2 := by gcongr
      linarith
    have hden : Λ0 * T ≤ T ^ 2 * Λ0 ^ 2 := by
      have h1' : 1 ≤ Λ0 * T := one_le_mul_of_one_le_of_one_le hΛ0 hT1
      have : T ^ 2 * Λ0 ^ 2 = (Λ0 * T) * (Λ0 * T) := by ring
      rw [this]; exact le_mul_of_one_le_right (by linarith) h1'
    calc 4 * β * (q * D * l) / (T ^ 2 * Λ0 ^ 2 * V ^ 2) ≤ 8 * ϰ * V ^ 2 / (T ^ 2 * Λ0 ^ 2 * V ^ 2) := by
          gcongr
      _ = 8 * ϰ / (T ^ 2 * Λ0 ^ 2) := by field_simp
      _ ≤ 8 * ϰ / (Λ0 * T) := by gcongr
  calc 8 * (√2 + 2) * (β * κ) / (Λ0 * V * T) + 4 * β * (q * D * l) / (T ^ 2 * Λ0 ^ 2 * V ^ 2)
      ≤ 32 / (Λ0 * T) + 8 * ϰ / (Λ0 * T) := add_le_add h1 h2
    _ = (32 + 8 * ϰ) / Λ0 * (1 / T) := by field_simp

/-- `√(n∧m) λ ≤ ϰ/c` with `λ = c⁻¹(√(L/(2n)) + 1/n)`, `ϰ = √(L/2) + 1`, for `1 ≤ k ≤ n`. -/
theorem sqrt_mul_lam {c L : ℝ} {n k : ℕ} (hc : 0 < c) (hL : 0 ≤ L) (hk : 1 ≤ k) (hkn : k ≤ n) :
    √(k : ℝ) * (1 / c * (√(L / (2 * n)) + 1 / n)) ≤ (√(L / 2) + 1) / c := by
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 : √(k : ℝ) * √(L / (2 * n)) ≤ √(L / 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [show (k : ℝ) * (L / (2 * n)) = (k / n) * (L / 2) by field_simp]
    have : (k : ℝ) / n ≤ 1 := by rw [div_le_one hn0]; exact hkn'
    nlinarith [div_nonneg hL (by norm_num : (0:ℝ) ≤ 2)]
  have h2 : √(k : ℝ) * (1 / n) ≤ 1 := by
    have hsk : √(k : ℝ) ≤ k := by
      have h1k : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.2 hk0
      calc √(k : ℝ) ≤ √(k : ℝ) * √(k : ℝ) := le_mul_of_one_le_right (Real.sqrt_nonneg _) h1k
        _ = k := Real.mul_self_sqrt (by linarith)
    rw [mul_one_div, div_le_one hn0]; linarith
  rw [show √(k : ℝ) * (1 / c * (√(L / (2 * n)) + 1 / n)) =
    (√(k : ℝ) * √(L / (2 * n)) + √(k : ℝ) * (1 / n)) / c by ring]
  gcongr

/-- `√s ≤ √2/√(n∧m)`. -/
theorem sqrt_sNM_le_min {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    √(sNM n m) ≤ √2 / √((min n m : ℕ) : ℝ) := by
  have hk : (1 : ℝ) ≤ ((min n m : ℕ) : ℝ) := by exact_mod_cast le_min hn hm
  have hkn : ((min n m : ℕ) : ℝ) ≤ n := by exact_mod_cast min_le_left n m
  have hkm : ((min n m : ℕ) : ℝ) ≤ m := by exact_mod_cast min_le_right n m
  rw [← Real.sqrt_div (by norm_num)]
  refine Real.sqrt_le_sqrt ?_
  unfold sNM
  have h1 : 1 / (n : ℝ) ≤ 1 / ((min n m : ℕ) : ℝ) := one_div_le_one_div_of_le (by linarith) hkn
  have h2 : 1 / (m : ℝ) ≤ 1 / ((min n m : ℕ) : ℝ) := one_div_le_one_div_of_le (by linarith) hkm
  have : 2 / ((min n m : ℕ) : ℝ) = 1 / ((min n m : ℕ) : ℝ) + 1 / ((min n m : ℕ) : ℝ) := by ring
  linarith

/-- `e_n ≤ 1/√(n∧m)`. -/
theorem ek_le_min {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ek n ≤ 1 / √((min n m : ℕ) : ℝ) ∧ ek m ≤ 1 / √((min n m : ℕ) : ℝ) := by
  have hk : (0 : ℝ) < ((min n m : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one (le_min hn hm)
  have hkn : ((min n m : ℕ) : ℝ) ≤ n := by exact_mod_cast min_le_left n m
  have hkm : ((min n m : ℕ) : ℝ) ≤ m := by exact_mod_cast min_le_right n m
  constructor
  · refine (ek_le_inv_sqrt hn).trans (one_div_le_one_div_of_le (Real.sqrt_pos.2 hk) (Real.sqrt_le_sqrt hkn))
  · refine (ek_le_inv_sqrt hm).trans (one_div_le_one_div_of_le (Real.sqrt_pos.2 hk) (Real.sqrt_le_sqrt hkm))

/-- `τ^A(α,δ)` at `D_φ = 2κ` is at most `β̄κ(2√2 + 4 + 2√log(1/δ))/√(n∧m)`. -/
theorem tauA_le {κ α δ : ℝ} {n m : ℕ} (hκ : 0 ≤ κ) (hα1 : α < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    tauA κ (2 * κ) α δ n m ≤
      1 / (1 - α) * κ * (2 * √2 + 4 + 2 * √(Real.log (1 / δ))) / √((min n m : ℕ) : ℝ) := by
  have hk : (0 : ℝ) < ((min n m : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one (le_min hn hm)
  set q := √((min n m : ℕ) : ℝ) with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 hk
  have hL := StatFormal.Wave30tp.log_inv_nonneg hδ0 hδ1
  have hβ : 0 ≤ 1 / (1 - α) := by have : 0 < 1 - α := by linarith
                                  positivity
  have hs := sqrt_sNM_le_min hn hm
  obtain ⟨hen, hem⟩ := ek_le_min hn hm
  have hsL : √(sNM n m * Real.log (1 / δ) / 2) ≤ √(Real.log (1 / δ)) / q := by
    rw [show sNM n m * Real.log (1 / δ) / 2 = sNM n m * (Real.log (1 / δ) / 2) by ring,
      Real.sqrt_mul (StatFormal.Wave30tp.sNM_pos hn hm).le]
    calc √(sNM n m) * √(Real.log (1 / δ) / 2) ≤ √2 / q * √(Real.log (1 / δ) / 2) := by gcongr
      _ = √(Real.log (1 / δ)) / q := by
          rw [Real.sqrt_div hL]
          have : (0 : ℝ) < √2 := by positivity
          field_simp
  unfold tauA
  have hin : 2 * κ * √(sNM n m) + 2 * κ * (ek n + ek m) + 2 * κ * √(sNM n m * Real.log (1 / δ) / 2) ≤
      κ * (2 * √2 + 4 + 2 * √(Real.log (1 / δ))) / q := by
    have a1 : 2 * κ * √(sNM n m) ≤ 2 * κ * (√2 / q) := by gcongr
    have a2 : 2 * κ * (ek n + ek m) ≤ 2 * κ * (1 / q + 1 / q) := by gcongr
    have a3 : 2 * κ * √(sNM n m * Real.log (1 / δ) / 2) ≤ 2 * κ * (√(Real.log (1 / δ)) / q) := by gcongr
    have : κ * (2 * √2 + 4 + 2 * √(Real.log (1 / δ))) / q =
        2 * κ * (√2 / q) + 2 * κ * (1 / q + 1 / q) + 2 * κ * (√(Real.log (1 / δ)) / q) := by
      field_simp; ring
    linarith
  calc 1 / (1 - α) * (2 * κ * √(sNM n m) + 2 * κ * (ek n + ek m) +
        2 * κ * √(sNM n m * Real.log (1 / δ) / 2))
      ≤ 1 / (1 - α) * (κ * (2 * √2 + 4 + 2 * √(Real.log (1 / δ))) / q) := by gcongr
    _ = 1 / (1 - α) * κ * (2 * √2 + 4 + 2 * √(Real.log (1 / δ))) / q := by ring

/-- The scaled filter: `f*(x) ≤ a/D + b/D ⟺ d*(x) ≤ a + b` for `f* = D⁻¹d*`, `D > 0`. -/
theorem scale_le {D a b v : ℝ} (hD : 0 < D) : D⁻¹ * v ≤ a / D + b / D ↔ v ≤ a + b := by
  rw [show a / D + b / D = D⁻¹ * (a + b) by ring]
  exact mul_le_mul_iff_of_pos_left (inv_pos.2 hD)

theorem scale_le' {D a b v : ℝ} (hD : 0 < D) : D⁻¹ * v ≤ a / D - b / D ↔ v ≤ a - b := by
  rw [show a / D - b / D = D⁻¹ * (a - b) by ring]
  exact mul_le_mul_iff_of_pos_left (inv_pos.2 hD)

theorem abs_witFn_sub_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {φ : 𝒳 → H} {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (a b : H) (x : 𝒳) : |witFn a φ x - witFn b φ x| ≤ κ * ‖a - b‖ := by
  have e : witFn a φ x - witFn b φ x = witFn (a - b) φ x := by unfold witFn; rw [inner_sub_left]
  rw [e, mul_comm]; exact abs_witFn_le hκ (a - b) x

theorem scale_lt1 {D a v : ℝ} (hD : 0 < D) : D⁻¹ * v < a / D ↔ v < a := by
  rw [div_eq_inv_mul]; exact mul_lt_mul_iff_of_pos_left (inv_pos.2 hD)

theorem scale_le1 {D a v : ℝ} (hD : 0 < D) : D⁻¹ * v ≤ a / D ↔ v ≤ a := by
  rw [div_eq_inv_mul]; exact mul_le_mul_iff_of_pos_left (inv_pos.2 hD)

end Helpers

/-! ### The corollary -/

section Main

theorem prod_univ_real {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {n m : ℕ} (S : Set (Fin n → 𝒳)) (T : Set (Fin m → 𝒳)) :
    (sampleLaw P Q n m).real (S ×ˢ T) =
      (Measure.pi fun _ : Fin n => P).real S * (Measure.pi fun _ : Fin m => Q).real T := by
  simp [sampleLaw, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]

set_option maxHeartbeats 4000000 in
theorem cor_trimrate_of (hb : Claims.basicineq) (hl : Claims.localmod) : Claims.cor_trimrate := by
  intro ε hε0 hε1
  have hL16 : 0 ≤ Real.log (1 / (ε / 16)) := StatFormal.Wave30tp.log_inv_nonneg (by positivity) (by linarith)
  obtain ⟨ϰ, hϰdef⟩ : ∃ v : ℝ, v = √(Real.log (1 / (ε / 16)) / 2) + 1 := ⟨_, rfl⟩
  have hϰ1 : 1 ≤ ϰ := by rw [hϰdef]; have := Real.sqrt_nonneg (Real.log (1 / (ε / 16)) / 2); linarith
  obtain ⟨Λ0, hΛ0def⟩ : ∃ v : ℝ, v = (128 + 32 * ϰ) / ε := ⟨_, rfl⟩
  have hΛ01 : 1 ≤ Λ0 := by rw [hΛ0def, le_div_iff₀ hε0]; nlinarith
  have hL8 : 0 ≤ Real.log (1 / (ε / 4 / 2)) := StatFormal.Wave30tp.log_inv_nonneg (by positivity) (by linarith)
  obtain ⟨CA, hCAdef⟩ : ∃ v : ℝ, v = 2 * √2 + 4 + 2 * √(Real.log (1 / (ε / 4 / 2))) := ⟨_, rfl⟩
  have hCA : 0 ≤ CA := by rw [hCAdef]; positivity
  obtain ⟨Λw, hΛwdef⟩ : ∃ v : ℝ, v = CA + 2 * Λ0 := ⟨_, rfl⟩
  have hΛw0 : 0 ≤ Λw := by rw [hΛwdef]; linarith
  obtain ⟨Λ, hΛdef⟩ : ∃ v : ℝ, v = max (4 * Λw) (2 * ϰ) := ⟨_, rfl⟩
  have hΛw : Λw ≤ Λ := by rw [hΛdef]; exact le_max_of_le_left (by linarith)
  have hΛ0Λ : Λ0 ≤ Λ := by rw [hΛwdef] at hΛw; linarith
  have hΛ4 : 4 * Λw ≤ Λ := by rw [hΛdef]; exact le_max_left _ _
  have hΛϰ : 2 * ϰ ≤ Λ := by rw [hΛdef]; exact le_max_right _ _
  refine ⟨Λ, by linarith, ?_⟩
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ α ρ cf Cf cf' uα dstar hφ hκ hα0 hα1 hDpos hmin hρ hcf hcf' hQd hqY hQY
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x₀)
  have hD2 : ∀ x x', ‖φ x - φ x'‖ ≤ 2 * κ := fun x x' =>
    (norm_sub_le _ _).trans (by linarith [hκ x, hκ x'])
  have hDn : Dpop φ P Q α = ‖dstar‖ := RBasic.Dpop_eq_norm hmin
  have h1α : 0 < 1 - α := by linarith
  have hβ0 : 0 < 1 / (1 - α) := one_div_pos.2 h1α
  have hc0 : 0 < min cf cf' := lt_min hcf hcf'
  have hsq0 : 0 < √((1 - α) * min cf cf') := Real.sqrt_pos.2 (by positivity)
  have hV1 : 1 / (1 - α) * κ ≤ κ / (1 - α) + 1 / √((1 - α) * min cf cf') := by
    have : 1 / (1 - α) * κ = κ / (1 - α) := by ring
    have : 0 ≤ 1 / √((1 - α) * min cf cf') := by positivity
    linarith
  have hV0 : 0 < κ / (1 - α) + 1 / √((1 - α) * min cf cf') := by positivity
  have hV2 : 1 / (1 - α) / min cf cf' ≤ (κ / (1 - α) + 1 / √((1 - α) * min cf cf')) ^ 2 := by
    have h1 : 1 / (1 - α) / min cf cf' = (1 / √((1 - α) * min cf cf')) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by positivity)]; field_simp
    rw [h1]
    have : 0 ≤ κ / (1 - α) := by positivity
    gcongr
    linarith
  set D := Dpop φ P Q α with hDdef
  set V := κ / (1 - α) + 1 / √((1 - α) * min cf cf') with hVdef
  set f := witFn dstar φ with hfdef
  have hfm : Measurable f := measurable_witFn hφ dstar
  have hfK : ∀ x, |f x| ≤ ‖dstar‖ * κ := abs_witFn_le hκ dstar
  set tα := quantileAt P f (1 - α) with htαdef
  obtain ⟨g, -, hgb, hgd⟩ := id hQd
  obtain ⟨Q0, hQ0def⟩ : ∃ v : ℝ, v = CA * V / D + ϰ / (cf * ρ) + ϰ / (cf' * ρ) +
      (2 * κ * Λw * V + ϰ / cf) / ρ + 1 := ⟨_, rfl⟩
  have hQ0a : 0 ≤ CA * V / D := by positivity
  have hQ0b : 0 ≤ ϰ / (cf * ρ) := by positivity
  have hQ0c : 0 ≤ ϰ / (cf' * ρ) := by positivity
  have hQ0d : 0 ≤ (2 * κ * Λw * V + ϰ / cf) / ρ := by positivity
  have hQ0 : 0 < Q0 := by rw [hQ0def]; linarith
  refine ⟨⌈Q0 ^ 2⌉₊ + 1, fun n m hn hm => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
  have hn0 : n ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  have hk1 : 1 ≤ min n m := le_min hn1 hm1
  have hkR : (1 : ℝ) ≤ ((min n m : ℕ) : ℝ) := by exact_mod_cast hk1
  set q := √((min n m : ℕ) : ℝ) with hqdef
  have hq0 : 0 < q := Real.sqrt_pos.2 (by linarith)
  have hqQ0 : Q0 < q := by
    have h1 : Q0 ^ 2 < ((min n m : ℕ) : ℝ) := by
      have : ⌈Q0 ^ 2⌉₊ + 1 ≤ min n m := le_min hn hm
      have h2 : (Q0 ^ 2 : ℝ) ≤ ⌈Q0 ^ 2⌉₊ := Nat.le_ceil _
      have h3 : ((⌈Q0 ^ 2⌉₊ : ℕ) : ℝ) + 1 ≤ ((min n m : ℕ) : ℝ) := by
        have h4 : ((⌈Q0 ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ ((min n m : ℕ) : ℝ) := Nat.cast_le.2 this
        rwa [Nat.cast_add, Nat.cast_one] at h4
      linarith
    rw [hqdef, ← Real.sqrt_sq hQ0.le]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) h1
  -- the large-sample conditions
  have hCAq : CA * V / q < D := by
    rw [div_lt_iff₀ hq0]
    have : CA * V / D < q := by rw [hQ0def] at hqQ0; linarith
    rw [div_lt_iff₀ hDpos] at this; linarith
  -- the cut radii
  obtain ⟨lX, hlXdef⟩ : ∃ v : ℝ, v = 1 / cf * (√(Real.log (1 / (ε / 16)) / (2 * n)) + 1 / n) := ⟨_, rfl⟩
  obtain ⟨lY, hlYdef⟩ : ∃ v : ℝ, v = 1 / cf' * (√(Real.log (1 / (ε / 16)) / (2 * m)) + 1 / m) := ⟨_, rfl⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  have hlX0 : 0 < lX := by rw [hlXdef]; positivity
  have hlY0 : 0 < lY := by rw [hlYdef]; positivity
  have hcflX : cf * lX = √(Real.log (1 / (ε / 16)) / (2 * n)) + 1 / n := by rw [hlXdef]; field_simp
  have hcflY : cf' * lY = √(Real.log (1 / (ε / 16)) / (2 * m)) + 1 / m := by rw [hlYdef]; field_simp
  have hqlX : q * lX ≤ ϰ / cf := by
    rw [hlXdef, hϰdef]; exact sqrt_mul_lam hcf hL16 hk1 (min_le_left n m)
  have hqlY : q * lY ≤ ϰ / cf' := by
    rw [hlYdef, hϰdef]; exact sqrt_mul_lam hcf' hL16 hk1 (min_le_right n m)
  have hlXq : lX ≤ ϰ / cf / q := by rw [le_div_iff₀ hq0]; linarith
  have hlYq : lY ≤ ϰ / cf' / q := by rw [le_div_iff₀ hq0]; linarith
  have hlXρ : lX ≤ ρ := by
    refine hlXq.trans ?_
    rw [div_le_iff₀ hq0]
    have : ϰ / (cf * ρ) < q := by rw [hQ0def] at hqQ0; linarith
    rw [div_lt_iff₀ (by positivity)] at this
    rw [div_le_iff₀ hcf]; nlinarith
  have hlYρ : lY ≤ ρ := by
    refine hlYq.trans ?_
    rw [div_le_iff₀ hq0]
    have : ϰ / (cf' * ρ) < q := by rw [hQ0def] at hqQ0; linarith
    rw [div_lt_iff₀ (by positivity)] at this
    rw [div_le_iff₀ hcf']; nlinarith
  have hwρ : (2 * κ * Λw * V + ϰ / cf) / q ≤ ρ := by
    rw [div_le_iff₀ hq0]
    have : (2 * κ * Λw * V + ϰ / cf) / ρ < q := by rw [hQ0def] at hqQ0; linarith
    rw [div_lt_iff₀ hρ] at this; linarith
  -- margins
  have hmarX := margins (P := P) hfm hfK hα1 hα0.le g (fun s hs => (hgb s hs).1) hgd hlX0 hlXρ
  have hmarY := ymargins (Q := Q) hfm hqY hQY hlY0 hlYρ
  -- the Hoeffding events
  have hε16 : 0 < ε / 16 := by positivity
  have hε161 : ε / 16 ≤ 1 := by linarith
  obtain ⟨hEa, -⟩ := hoeffding_cdf P hfm (tα + lX) hn0 hε16 hε161
  obtain ⟨-, hEb⟩ := hoeffding_cdf P hfm (tα - lX) hn0 hε16 hε161
  obtain ⟨hEa', -⟩ := hoeffding_cdf Q hfm (uα + lY) hm0 hε16 hε161
  obtain ⟨-, hEb'⟩ := hoeffding_cdf Q hfm (uα - lY) hm0 hε16 hε161
  set Ea := {x : Fin n → 𝒳 | P.real {y | f y ≤ tα + lX} - √(Real.log (1 / (ε / 16)) / (2 * n)) ≤
    empCdf f x (tα + lX)} with hEadef
  set Eb := {x : Fin n → 𝒳 | empCdf f x (tα - lX) ≤ P.real {y | f y ≤ tα - lX} +
    √(Real.log (1 / (ε / 16)) / (2 * n))} with hEbdef
  set Ea' := {y : Fin m → 𝒳 | Q.real {y | f y ≤ uα + lY} - √(Real.log (1 / (ε / 16)) / (2 * m)) ≤
    empCdf f y (uα + lY)} with hEa'def
  set Eb' := {y : Fin m → 𝒳 | empCdf f y (uα - lY) ≤ Q.real {y | f y ≤ uα - lY} +
    √(Real.log (1 / (ε / 16)) / (2 * m))} with hEb'def
  have hmEa : MeasurableSet Ea := measurableSet_le measurable_const (measurable_empCdf hfm n _)
  have hmEb : MeasurableSet Eb := measurableSet_le (measurable_empCdf hfm n _) measurable_const
  have hmEa' : MeasurableSet Ea' := measurableSet_le measurable_const (measurable_empCdf hfm m _)
  have hmEb' : MeasurableSet Eb' := measurableSet_le (measurable_empCdf hfm m _) measurable_const
  -- Theorem A
  obtain ⟨Ep, Em, hEpm, hEmm, -, -, hEA, hA⟩ :=
    StatFormal.Wave30tr.thmA_twosided 𝒳 H φ κ (2 * κ) P Q (ε / 4) n m hφ hκ hD2 (by positivity)
      (by linarith) hn1 hm1
  -- the process `Z`
  set fs : H := D⁻¹ • dstar with hfsdef
  set ts := tα / D with htsdef
  set us := uα / D with husdef
  set l1 := lX / D with hl1def
  set l2 := lY / D with hl2def
  have hl10 : 0 ≤ l1 := by positivity
  have hl20 : 0 ≤ l2 := by positivity
  set b := Λ0 * V / (D * q) with hbdef
  have hb0 : 0 < b := by positivity
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (2 / b) (by norm_num : (1 : ℝ) < 2)
  have hKb : 2 ≤ 2 ^ K * b := by rw [div_lt_iff₀ hb0] at hK; linarith
  set Zr : ℝ → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun r z => Zloc P Q φ fs ts us κ r l1 l2 z with hZrdef
  set G : ℕ → Set ((Fin n → 𝒳) × (Fin m → 𝒳)) :=
    fun i => {z | D * (2 ^ i * b) ^ 2 / (2 * (1 / (1 - α))) ≤ Zr (2 ^ (i + 1) * b) z} with hGdef
  have hGm : ∀ i, MeasurableSet (G i) := fun i =>
    measurableSet_le measurable_const
      (hl 𝒳 H P Q φ κ fs ts us (2 ^ (i + 1) * b) l1 l2 n m hφ hκ (by positivity) hl10 hl20 hn1 hm1).1
  have hGp : ∀ i, (sampleLaw P Q n m).real (G i) ≤ (32 + 8 * ϰ) / Λ0 * (1 / 2) ^ i := by
    intro i
    obtain ⟨-, hZ0, -, -, hZint, hZE, -⟩ :=
      hl 𝒳 H P Q φ κ fs ts us (2 ^ (i + 1) * b) l1 l2 n m hφ hκ (by positivity) hl10 hl20 hn1 hm1
    set ci := D * (2 ^ i * b) ^ 2 / (2 * (1 / (1 - α))) with hcidef
    have hci : 0 < ci := by positivity
    have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hZ0) hZint ci
    have hs := sqrt_sNM_le_min hn1 hm1
    obtain ⟨hen, hem⟩ := ek_le_min hn1 hm1
    set ρi := 2 ^ (i + 1) * b with hρidef
    have hρi0 : 0 ≤ ρi := by positivity
    have hEZ : ∫ z, Zloc P Q φ fs ts us κ ρi l1 l2 z ∂(sampleLaw P Q n m) ≤
        (2 * (√2 + 2) * κ * ρi + 2 * (l1 + l2)) / q := by
      refine hZE.trans ?_
      have a1 : κ * ρi * √(sNM n m) ≤ κ * ρi * (√2 / q) := by gcongr
      have a2 : (κ * ρi + l1) * ek n ≤ (κ * ρi + l1) * (1 / q) := by gcongr
      have a3 : (κ * ρi + l2) * ek m ≤ (κ * ρi + l2) * (1 / q) := by gcongr
      have : (2 * (√2 + 2) * κ * ρi + 2 * (l1 + l2)) / q =
          2 * (κ * ρi * (√2 / q) + (κ * ρi + l1) * (1 / q) + (κ * ρi + l2) * (1 / q)) := by
        field_simp; ring
      rw [this]; linarith
    have hlq : q * D * (l1 + l2) ≤ 2 * ϰ / min cf cf' := by
      have e : q * D * (l1 + l2) = q * lX + q * lY := by
        rw [hl1def, hl2def]; field_simp
      have h1 : ϰ / cf ≤ ϰ / min cf cf' := div_le_div_of_nonneg_left (by linarith) hc0 (min_le_left _ _)
      have h2 : ϰ / cf' ≤ ϰ / min cf cf' := div_le_div_of_nonneg_left (by linarith) hc0 (min_le_right _ _)
      rw [e]
      have : 2 * ϰ / min cf cf' = ϰ / min cf cf' + ϰ / min cf cf' := by ring
      linarith
    have hsh := shell_bound (β := 1 / (1 - α)) (c := min cf cf') hκ0 hβ0 hV0 hc0 hDpos hq0 hΛ01
      (by linarith) (add_nonneg hl10 hl20) hbdef hV1 hV2 hlq i
    rw [← hρidef, ← hcidef] at hsh
    calc (sampleLaw P Q n m).real (G i) ≤ (∫ z, Zloc P Q φ fs ts us κ ρi l1 l2 z ∂(sampleLaw P Q n m)) / ci := by
          rw [le_div_iff₀ hci, mul_comm]; exact hmk
      _ ≤ (2 * (√2 + 2) * κ * ρi + 2 * (l1 + l2)) / q / ci := by gcongr
      _ ≤ (32 + 8 * ϰ) / Λ0 * (1 / 2) ^ i := hsh
  -- the event
  set A1 := Ep ∩ Em with hA1def
  set A2 : Set ((Fin n → 𝒳) × (Fin m → 𝒳)) := (Ea ∩ Eb) ×ˢ Set.univ with hA2def
  set A3 : Set ((Fin n → 𝒳) × (Fin m → 𝒳)) := Set.univ ×ˢ (Ea' ∩ Eb') with hA3def
  set A4 := ⋂ i ∈ Finset.range K, (G i)ᶜ with hA4def
  have hA1m : MeasurableSet A1 := hEpm.inter hEmm
  have hA2m : MeasurableSet A2 := (hmEa.inter hmEb).prod MeasurableSet.univ
  have hA3m : MeasurableSet A3 := MeasurableSet.univ.prod (hmEa'.inter hmEb')
  have hA4m : MeasurableSet A4 := Finset.measurableSet_biInter _ fun i _ => (hGm i).compl
  have hEm : MeasurableSet (A1 ∩ A2 ∩ A3 ∩ A4) := ((hA1m.inter hA2m).inter hA3m).inter hA4m
  refine ⟨A1 ∩ A2 ∩ A3 ∩ A4, hEm, ?_, ?_⟩
  · -- probability `≥ 1 − ε`
    set μ := sampleLaw P Q n m with hμdef
    have p1 : 1 - ε / 4 ≤ μ.real A1 := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hEA
    have pXs : 1 - ε / 8 ≤ (Measure.pi fun _ : Fin n => P).real (Ea ∩ Eb) := by
      have := prob_inter_ge (Measure.pi fun _ : Fin n => P) (S := Ea) hmEb
      linarith
    have pYs : 1 - ε / 8 ≤ (Measure.pi fun _ : Fin m => Q).real (Ea' ∩ Eb') := by
      have := prob_inter_ge (Measure.pi fun _ : Fin m => Q) (S := Ea') hmEb'
      linarith
    have p2 : 1 - ε / 8 ≤ μ.real A2 := by
      rw [hA2def, hμdef, prod_univ_real]; simpa using pXs
    have p3 : 1 - ε / 8 ≤ μ.real A3 := by
      rw [hA3def, hμdef, prod_univ_real]; simpa using pYs
    have p4 : ∑ i ∈ Finset.range K, μ.real (G i) ≤ ε / 2 := by
      calc ∑ i ∈ Finset.range K, μ.real (G i) ≤ ∑ i ∈ Finset.range K, (32 + 8 * ϰ) / Λ0 * (1 / 2) ^ i :=
            Finset.sum_le_sum fun i _ => hGp i
        _ = (32 + 8 * ϰ) / Λ0 * ∑ i ∈ Finset.range K, ((1 : ℝ) / 2) ^ i := by rw [Finset.mul_sum]
        _ ≤ (32 + 8 * ϰ) / Λ0 * 2 := by
            gcongr
            exact sum_geometric_two_le K
        _ = ε / 2 := by rw [hΛ0def]; field_simp; ring
    have hsub : (A1 ∩ A2 ∩ A3 ∩ A4)ᶜ ⊆ A1ᶜ ∪ A2ᶜ ∪ A3ᶜ ∪ ⋃ i ∈ Finset.range K, G i := by
      intro z hz
      by_contra hcon
      apply hz
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not, Set.mem_iUnion, not_exists] at hcon
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcon
      refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
      simp only [hA4def, Set.mem_iInter, Set.mem_compl_iff]
      exact fun i hi => h4 i hi
    have hc := measureReal_mono (μ := μ) hsub
    have hu1 := measureReal_union_le (μ := μ) (A1ᶜ ∪ A2ᶜ ∪ A3ᶜ) (⋃ i ∈ Finset.range K, G i)
    have hu2 := measureReal_union_le (μ := μ) (A1ᶜ ∪ A2ᶜ) A3ᶜ
    have hu3 := measureReal_union_le (μ := μ) A1ᶜ A2ᶜ
    have hu4 := measureReal_biUnion_finset_le (μ := μ) (Finset.range K) G
    rw [probReal_compl_eq_one_sub hA1m] at hu3
    rw [probReal_compl_eq_one_sub hA2m] at hu3
    rw [probReal_compl_eq_one_sub hA3m] at hu2
    rw [probReal_compl_eq_one_sub hEm] at hc
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    change 1 - ε ≤ μ.real _
    linarith
  · -- the deterministic consequences
    rintro z ⟨⟨⟨hzA, hz2⟩, hz3⟩, hz4⟩ pr hpr hprmin
    obtain ⟨⟨hza, hzb⟩, -⟩ := hz2
    obtain ⟨-, ⟨hza', hzb'⟩⟩ := hz3
    have hzG : ∀ i ∈ Finset.range K, z ∉ G i := by
      intro i hi hzi
      simp only [hA4def, Set.mem_iInter, Set.mem_compl_iff] at hz4
      exact hz4 i hi hzi
    set dh := witness φ z.1 z.2 pr with hdhdef
    set Dh := Demp φ z.1 z.2 α with hDhdef
    have hDhn : Dh = ‖dh‖ := RBasic.Demp_eq_norm hφ hα0.le hα1 hn1 hm1 z.1 z.2 hpr hprmin
    set τ := tauA κ (2 * κ) α (ε / 4 / 2) n m with hτdef
    have habs : |Dh - D| ≤ τ := hA z hzA α ⟨hα0.le, hα1⟩
    have hτle : τ ≤ CA * V / q := by
      have h := tauA_le (δ := ε / 4 / 2) hκ0 hα1 (by positivity) (by linarith) hn1 hm1
      rw [← hCAdef] at h
      calc τ ≤ 1 / (1 - α) * κ * CA / q := h
        _ ≤ V * CA / q := by gcongr
        _ = CA * V / q := by ring
    have hτD : τ < D := lt_of_le_of_lt hτle hCAq
    have hDhpos : 0 < Dh := by have := (abs_le.1 habs).1; linarith
    have hDh2 : Dh ≤ 2 * D := by have := (abs_le.1 habs).2; linarith
    have hkn : kfloor n α < n := kfloor_lt hn1 hα0 hα1
    have hkm : kfloor m α < m := kfloor_lt hm1 hα0 hα1
    -- the counts on the `d*`-scale
    have hcX := xcounts (P := P) (f := f) hn1 hα1 hcflX hmarX.1 hmarX.2 z.1 hza hzb
    have hcY := ycounts (Q := Q) (f := f) hm1 hα0 hα1 hcflY hmarY.1 hmarY.2 z.2 hza' hzb'
    -- the normalised witnesses
    set fh : H := Dh⁻¹ • dh with hfhdef
    have hfhn : ‖fh‖ = 1 := by
      rw [hfhdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hDhpos, ← hDhn,
        inv_mul_cancel₀ hDhpos.ne']
    have hfsn : ‖fs‖ = 1 := by
      rw [hfsdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hDpos, ← hDn]
      exact inv_mul_cancel₀ hDpos.ne'
    set r := ‖fh - fs‖ with hrdef
    have hr0 : 0 ≤ r := norm_nonneg _
    have hr2 : r ≤ 2 := by
      have := norm_sub_le fh fs; rw [hfhn, hfsn] at this; linarith
    have hwit : ∀ x, witFn fs φ x = D⁻¹ * f x := fun x => by rw [hfsdef, witFn_smul]
    -- the counts on the `f*`-scale
    have hAX : kfloor n α + 1 ≤ (Finset.univ.filter fun i => witFn fs φ (z.1 i) ≤ ts + l1).card := by
      have e : (Finset.univ.filter fun i => witFn fs φ (z.1 i) ≤ ts + l1) =
          Finset.univ.filter fun i => f (z.1 i) ≤ tα + lX :=
        Finset.filter_congr fun i _ => by rw [hwit, htsdef, hl1def]; exact scale_le hDpos
      rw [e]; exact hcX.1
    have hBX : (Finset.univ.filter fun i => witFn fs φ (z.1 i) ≤ ts - l1).card < kfloor n α + 1 := by
      have e : (Finset.univ.filter fun i => witFn fs φ (z.1 i) ≤ ts - l1) =
          Finset.univ.filter fun i => f (z.1 i) ≤ tα - lX :=
        Finset.filter_congr fun i _ => by rw [hwit, htsdef, hl1def]; exact scale_le' hDpos
      rw [e]; exact hcX.2
    have hAY : m - kfloor m α - 1 + 1 ≤ (Finset.univ.filter fun j => witFn fs φ (z.2 j) ≤ us + l2).card := by
      have e : (Finset.univ.filter fun j => witFn fs φ (z.2 j) ≤ us + l2) =
          Finset.univ.filter fun j => f (z.2 j) ≤ uα + lY :=
        Finset.filter_congr fun j _ => by rw [hwit, husdef, hl2def]; exact scale_le hDpos
      rw [e]; exact hcY.1
    have hBY : (Finset.univ.filter fun j => witFn fs φ (z.2 j) ≤ us - l2).card < m - kfloor m α - 1 + 1 := by
      have e : (Finset.univ.filter fun j => witFn fs φ (z.2 j) ≤ us - l2) =
          Finset.univ.filter fun j => f (z.2 j) ≤ uα - lY :=
        Finset.filter_congr fun j _ => by rw [hwit, husdef, hl2def]; exact scale_le' hDpos
      rw [e]; exact hcY.2
    have htX := tHat_bounds (fun i => witFn fh φ (z.1 i)) (fun i => witFn fs φ (z.1 i)) hkn
      (fun i => abs_witFn_sub_le hκ fh fs (z.1 i)) hAX hBX
    have htY := tHat_bounds (fun j => witFn fh φ (z.2 j)) (fun j => witFn fs φ (z.2 j))
      (k := m - kfloor m α - 1) (by omega) (fun j => abs_witFn_sub_le hκ fh fs (z.2 j)) hAY hBY
    -- the quantiles of `f*`
    have hqt : IsQuantile P (witFn fs φ) (1 - α) ts := by
      constructor
      · have e : {x | witFn fs φ x < ts} = {x | f x < tα} := by
          ext x; simp only [Set.mem_ofPred_eq, hwit, htsdef]; exact scale_lt1 hDpos
        rw [e]; exact quantile_lt_le P hfm hfK h1α (by linarith)
      · have e : {x | witFn fs φ x ≤ ts} = {x | f x ≤ tα} := by
          ext x; simp only [Set.mem_ofPred_eq, hwit, htsdef]; exact scale_le1 hDpos
        rw [e]; exact quantile_ge P hfm hfK h1α (by linarith)
    have hqu : IsQuantile Q (witFn fs φ) α us := by
      constructor
      · have e : {x | witFn fs φ x < us} = {x | f x < uα} := by
          ext x; simp only [Set.mem_ofPred_eq, hwit, husdef]; exact scale_lt1 hDpos
        rw [e]; exact hqY.1
      · have e : {x | witFn fs φ x ≤ us} = {x | f x ≤ uα} := by
          ext x; simp only [Set.mem_ofPred_eq, hwit, husdef]; exact scale_le1 hDpos
        rw [e]; exact hqY.2
    -- the basic inequality and the localised process
    obtain ⟨hb1, hb2⟩ := hb 𝒳 H P Q φ κ α ts us n m dstar hφ hκ hα0 hα1 hn1 hm1 hmin hDpos hqt hqu
      z.1 z.2 pr hpr hprmin hDhpos
    obtain ⟨-, -, hZub, hZmono, -, -, -⟩ :=
      hl 𝒳 H P Q φ κ fs ts us r l1 l2 n m hφ hκ hr0 hl10 hl20 hn1 hm1
    have hmem : ((fh, ord (fun i => witFn fh φ (z.1 i)) (kfloor n α),
        ordTop (fun j => witFn fh φ (z.2 j)) α) : H × ℝ × ℝ) ∈ rampPar fs ts us κ r l1 l2 :=
      ⟨le_rfl, htX, htY⟩
    have hZ := hZub z _ hmem
    have hbasic : D / 2 * r ^ 2 ≤ 1 / (1 - α) * Zr r z := by
      have h := hb1.trans hb2
      calc D / 2 * r ^ 2 ≤ 1 / (1 - α) * rampDev P Q φ fs ts us z (fh, ord (fun i => witFn fh φ (z.1 i))
            (kfloor n α), ordTop (fun j => witFn fh φ (z.2 j)) α) := h
        _ ≤ 1 / (1 - α) * Zr r z := mul_le_mul_of_nonneg_left hZ hβ0.le
    -- peeling: `r ≤ b`
    have hrb : r ≤ b := by
      by_contra hcon
      push_neg at hcon
      classical
      have hex : ∃ j : ℕ, r ≤ 2 ^ j * b := ⟨K, by linarith⟩
      have hj : r ≤ 2 ^ Nat.find hex * b := Nat.find_spec hex
      have hjK : Nat.find hex ≤ K := Nat.find_min' hex (by linarith)
      have hj0 : Nat.find hex ≠ 0 := by
        intro h; rw [h, pow_zero, one_mul] at hj; linarith
      obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have hmin' : ¬ r ≤ 2 ^ i * b := Nat.find_min hex (by omega)
      push_neg at hmin'
      have hiK : i ∈ Finset.range K := Finset.mem_range.2 (by omega)
      apply hzG i hiK
      have hρ0 : 0 ≤ 2 ^ (i + 1) * b := by positivity
      have hmono : Zr r z ≤ Zr (2 ^ (i + 1) * b) z := by
        have hj' : r ≤ 2 ^ (i + 1) * b := by rw [← Nat.succ_eq_add_one, ← hi]; exact hj
        exact hZmono z (Set.mem_Ici.2 hr0) (Set.mem_Ici.2 hρ0) hj'
      have hsq : (2 ^ i * b) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hmin'.le 2
      show D * (2 ^ i * b) ^ 2 / (2 * (1 / (1 - α))) ≤ Zr (2 ^ (i + 1) * b) z
      rw [div_le_iff₀ (by positivity)]
      have : D * (2 ^ i * b) ^ 2 ≤ D * r ^ 2 := mul_le_mul_of_nonneg_left hsq hDpos.le
      nlinarith
    -- the witness
    have hdh_eq : dh = Dh • fh := by
      rw [hfhdef, smul_inv_smul₀ hDhpos.ne']
    have hds_eq : dstar = D • fs := by
      rw [hfsdef, smul_inv_smul₀ hDpos.ne']
    have hwitb : ‖dh - dstar‖ ≤ Λw * V / q := by
      have e : dh - dstar = Dh • (fh - fs) + (Dh - D) • fs := by
        rw [hdh_eq, hds_eq, smul_sub, sub_smul]; abel
      calc ‖dh - dstar‖ ≤ ‖Dh • (fh - fs)‖ + ‖(Dh - D) • fs‖ := by rw [e]; exact norm_add_le _ _
        _ = Dh * r + |Dh - D| := by
            rw [norm_smul, norm_smul, hfsn, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hDhpos, mul_one]
        _ ≤ 2 * D * b + CA * V / q := by
            have : Dh * r ≤ 2 * D * b := mul_le_mul hDh2 hrb hr0 (by linarith)
            linarith
        _ = Λw * V / q := by rw [hbdef, hΛwdef]; field_simp; ring
    -- the kept set
    set Δ := κ * ‖dh - dstar‖ with hΔdef
    have hΔ : ∀ x, |witFn dh φ x - f x| ≤ Δ := fun x => abs_witFn_sub_le hκ dh dstar x
    have hΔle : Δ ≤ κ * (Λw * V / q) := mul_le_mul_of_nonneg_left hwitb hκ0
    have hth : |tHat φ dh α z.1 - tα| ≤ Δ + lX :=
      tHat_bounds (fun i => witFn dh φ (z.1 i)) (fun i => f (z.1 i)) hkn (fun i => hΔ (z.1 i)) hcX.1 hcX.2
    have hbd := band_incl (witFn dh φ) f hΔ hth (Λ := 2 * Δ + lX) (by linarith)
    have hw0 : 0 ≤ 2 * Δ + lX := by positivity
    have hwq : 2 * Δ + lX ≤ (2 * κ * Λw * V + ϰ / cf) / q := by
      have : (2 * κ * Λw * V + ϰ / cf) / q = 2 * (κ * (Λw * V / q)) + ϰ / cf / q := by ring
      linarith
    have hwρ' : 2 * Δ + lX ≤ ρ := hwq.trans hwρ
    have hkb := kept_bounds hfm hα1 hcf.le hQd hw0 hwρ' hbd.1 hbd.2
    have hCf : 0 ≤ Cf := by
      have := hgb tα ⟨by linarith, by linarith⟩
      linarith [this.1, this.2]
    have hfin : 2 * Cf * (2 * Δ + lX) ≤ Λ * (Cf * (κ * V + 1 / cf) / q) := by
      have h1 : 2 * Cf * (2 * Δ + lX) ≤ 2 * Cf * ((2 * κ * Λw * V + ϰ / cf) / q) := by gcongr
      have h2 : 2 * Cf * ((2 * κ * Λw * V + ϰ / cf) / q) =
          Cf * ((4 * Λw) * (κ * V) + (2 * ϰ) * (1 / cf)) / q := by ring
      have h3 : Cf * ((4 * Λw) * (κ * V) + (2 * ϰ) * (1 / cf)) / q ≤
          Cf * (Λ * (κ * V) + Λ * (1 / cf)) / q := by
        have hκV : 0 ≤ κ * V := by positivity
        have hcf1 : 0 ≤ 1 / cf := by positivity
        gcongr
      have h4 : Cf * (Λ * (κ * V) + Λ * (1 / cf)) / q = Λ * (Cf * (κ * V + 1 / cf) / q) := by ring
      linarith
    intro D' V' q' tα' dh' Dh' th'
    refine ⟨hDhpos, ?_, ?_, ?_, ?_⟩
    · show r ≤ Λ * (V / (D * q))
      calc r ≤ b := hrb
        _ = Λ0 * (V / (D * q)) := by rw [hbdef]; ring
        _ ≤ Λ * (V / (D * q)) := by gcongr
    · show ‖dh - dstar‖ ≤ Λ * (V / q)
      calc ‖dh - dstar‖ ≤ Λw * V / q := hwitb
        _ = Λw * (V / q) := by ring
        _ ≤ Λ * (V / q) := by gcongr
    · exact hkb.1.trans (ENNReal.ofReal_le_ofReal hfin)
    · intro ϑ ϑh hϑ hϑh
      have h := hkb.2 ϑ ϑh hϑ hϑh
      have h' : (1 - α) * ∫ x, |plugDensityFn α ϑh (witFn dh φ) (tHat φ dh α z.1) x -
          plugDensityFn α ϑ f tα x| ∂P ≤ 2 * Cf * (2 * Δ + lX) := by
        rw [le_div_iff₀ h1α] at h; linarith
      exact h'.trans hfin

end Main

end StatFormal.Wave30tx.RCor
