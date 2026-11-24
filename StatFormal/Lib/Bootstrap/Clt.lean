import StatFormal.Lib.Bootstrap.CharFun
import StatFormal.Lib.Bootstrap.Consistency

/-!
# The bootstrap CLT for the split statistic: deterministic sequential form (library)

For data sequences `v_x^{(k)} ∈ ℝ^{n_k}`, `v_y^{(k)} ∈ ℝ^{m_k}` (`|·| ≤ B`, `n_k → ∞`, `m_k/n_k → κ > 0`) whose
plug-in variances converge (`varLo → V_X`, `varLo(−v_y) → V_Y`) and whose bootstrap remainders vanish in the
bootstrap `L²` (`n_k E*[D_X*²] → 0`, `m_k E*[D_Y*²] → 0`), the bootstrap law of the root `√n (T̂* − T̂)` converges
weakly to `N(0, σ²)`, `σ² = (V_X + V_Y/κ)/β²`, so its cdf converges at every point (`boot_root_seq`).

Proof: `√n (T̂* − T̂) = −(√n/β)(A_X* + A_Y*) + (√n/β)(D_X* + D_Y*)` (duality, `boot_decomp`); the characteristic
function of the linear part factorises over the two independent resamples and over the draws
(`cAvg_prod_mul`, `cAvg_resample_exp`) and converges by `tendsto_cAvg_pow`; the remainder moves it by at most
`|s| √(E* Rem²) → 0`; Lévy's continuity theorem and the portmanteau theorem conclude.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open Finset Complex Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatFormal.Foundations.Bootstrap

open StatFormal.TrimmedMMD.BangBang StatFormal.Foundations.TrimmedMean

/-- The upper extreme trimmed mean `max_{w ∈ capped n α} Σ w_i v_i`. -/
abbrev tUp (n : ℕ) (α : ℝ) (v : Fin n → ℝ) : ℝ := sSup ((fun w => ∑ i, w i * v i) '' capped n α)

/-! ### Centred influence values -/

section Infl
variable {n : ℕ} (α : ℝ) (v : Fin n → ℝ)

/-- Centred influence values `g_ĉ(v_j) − P_n g_ĉ`, `g_c = (c − ·)_+`. -/
def infC (j : Fin n) : ℝ :=
  max (quantLo n α v - v j) 0 - (∑ i, max (quantLo n α v - v i) 0) / n

lemma infC_sum : ∑ j, infC α v j = 0 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    unfold infC
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

lemma abs_infC_le {B : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hv : ∀ i, |v i| ≤ B) (j : Fin n) : |infC α v j| ≤ 2 * B := by
  have hn : 0 < n := Fin.pos j
  have hc := abs_quantLo_le hn hα0 hα1 hv
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv j)
  have ha : ∀ i, 0 ≤ max (quantLo n α v - v i) 0 ∧ max (quantLo n α v - v i) 0 ≤ 2 * B := fun i =>
    ⟨le_max_right _ _, max_le (by have := neg_abs_le (v i); have := hv i; have := le_abs_self (quantLo n α v); linarith)
      (by linarith)⟩
  obtain ⟨m0, m1⟩ := avg_bounds hn (fun i => (ha i).1) fun i => (ha i).2
  unfold infC
  rw [abs_le]
  constructor <;> linarith [(ha j).1, (ha j).2]

lemma sum_infC_sq (hn : 0 < n) : (∑ j, infC α v j ^ 2) / n = varLo n α v := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set a : Fin n → ℝ := fun j => max (quantLo n α v - v j) 0
  set abar := (∑ i, a i) / n with habar
  have hsa : ∑ i, a i = n * abar := by rw [habar]; field_simp
  have e : ∀ j, infC α v j ^ 2 = a j ^ 2 + (-(2 * abar) * a j + abar ^ 2) := fun j => by
    simp only [infC]; ring
  simp only [e, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold varLo
  rw [hsa]
  field_simp
  ring

lemma natCast_mul_bootA (hn : 0 < n) (I : Fin n → Fin n) : (n : ℝ) * bootA v α I = ∑ i, infC α v (I i) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold bootA emean infC
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Function.comp]
  field_simp

end Infl

/-! ### Characteristic function of one linear side -/

theorem tendsto_char_side {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {α B : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {v : (k : ℕ) → Fin (N k) → ℝ} (hb : ∀ k i, |v k i| ≤ B) {V : ℝ}
    (hV : Tendsto (fun k => varLo (N k) α (v k)) atTop (𝓝 V)) {u : ℕ → ℝ} {ρ : ℝ}
    (hu : Tendsto (fun k => (N k : ℝ) * u k ^ 2) atTop (𝓝 ρ)) :
    Tendsto (fun k => cAvg (fun K : Fin (N k) → Fin (N k) => exp (↑(u k * (N k : ℝ) * bootA (v k) α K) * I)))
      atTop (𝓝 (exp (↑(-(ρ * V / 2))))) := by
  have hNpos : ∀ᶠ k in atTop, 0 < N k := hN.eventually_gt_atTop 0
  have hV' : Tendsto (fun k => (∑ j, infC α (v k) j ^ 2) / N k) atTop (𝓝 V) := by
    refine hV.congr' ?_
    filter_upwards [hNpos] with k hk
    exact (sum_infC_sq α (v k) hk).symm
  have key := tendsto_cAvg_pow hN (c := fun k => infC α (v k)) (C := 2 * B)
    (fun k j => abs_infC_le α (v k) hα0 hα1 (hb k) j) (fun k => infC_sum α (v k)) hu hV'
  refine key.congr' ?_
  filter_upwards [hNpos] with k hk
  rw [← cAvg_resample_exp]
  congr 1
  funext K
  rw [mul_assoc, natCast_mul_bootA α (v k) hk K]

/-! ### The sequential bootstrap CLT -/

lemma norm_exp_sub_exp_le (a b : ℝ) : ‖exp (↑a * I) - exp (↑b * I)‖ ≤ |a - b| := by
  have e : exp (↑a * I) - exp (↑b * I) = exp (↑b * I) * (exp (I * ↑(a - b)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast; ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  rwa [Real.norm_eq_abs] at this

lemma bAvg_prod_fst {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ] (F : ι → ℝ) :
    bAvg (fun p : ι × κ => F p.1) = bAvg F := by
  unfold bAvg
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  rw [← mul_sum]
  push_cast
  have : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma bAvg_prod_snd {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] (G : κ → ℝ) :
    bAvg (fun p : ι × κ => G p.2) = bAvg G := by
  unfold bAvg
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  simp only
  rw [Finset.sum_const, card_univ, nsmul_eq_mul]
  push_cast
  have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma bAvg_abs_le_sqrt {ι : Type*} [Fintype ι] [Nonempty ι] (F : ι → ℝ) :
    bAvg (fun i => |F i|) ≤ √(bAvg fun i => F i ^ 2) := by
  have h := bAvg_mul_sq_le (fun i => |F i|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sq_abs, bAvg_const] at h
  exact Real.le_sqrt_of_sq_le h

/-! ### The bootstrap root and its decomposition -/

/-- The bootstrap root `√n (T̂*(I, J) − T̂)`. -/
def bootRoot (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) (p : (Fin n → Fin n) × (Fin m → Fin m)) : ℝ :=
  √(n : ℝ) * ((tLo n α (vx ∘ p.1) - tUp m α (vy ∘ p.2)) - (tLo n α vx - tUp m α vy))

lemma bootRoot_decomp {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (vx : Fin n → ℝ)
    (vy : Fin m → ℝ) (p : (Fin n → Fin n) × (Fin m → Fin m)) :
    bootRoot n m α vx vy p = -(√(n : ℝ) / (1 - α)) * (bootA vx α p.1 + bootA (fun j => -vy j) α p.2) +
      √(n : ℝ) / (1 - α) * (bootD vx α p.1 + bootD (fun j => -vy j) α p.2) := by
  have h1 := boot_decomp vx hn hα0 hα1 p.1
  have h2 := boot_decomp (fun j => -vy j) hm hα0 hα1 p.2
  have e1 : tUp m α (vy ∘ p.2) = -tLo m α ((fun j => -vy j) ∘ p.2) := trimUp_eq hm hα0 hα1 _
  have e2 : tUp m α vy = -tLo m α (fun j => -vy j) := trimUp_eq hm hα0 hα1 vy
  have hβ : (1 - α) ≠ 0 := by linarith
  unfold bootRoot
  rw [e1, e2]
  linear_combination (norm := (field_simp; ring)) (√(n : ℝ) / (1 - α)) * h1 + (√(n : ℝ) / (1 - α)) * h2

/-- The characteristic function of the linear part of the root. -/
def linChar {n m : ℕ} (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) (a b : ℝ) : ℂ :=
  cAvg (fun p : (Fin n → Fin n) × (Fin m → Fin m) =>
    exp (↑(a * bootA vx α p.1) * I) * exp (↑(b * bootA (fun j => -vy j) α p.2) * I))

lemma linChar_eq {n m : ℕ} (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) (a b : ℝ) :
    linChar α vx vy a b = cAvg (fun K : Fin n → Fin n => exp (↑(a * bootA vx α K) * I)) *
      cAvg (fun K : Fin m → Fin m => exp (↑(b * bootA (fun j => -vy j) α K) * I)) := by
  have : Nonempty (Fin n → Fin n) := ⟨fun i => i⟩
  have : Nonempty (Fin m → Fin m) := ⟨fun i => i⟩
  unfold linChar
  rw [cAvg_prod_mul (fun K => exp (↑(a * bootA vx α K) * I)) (fun K => exp (↑(b * bootA (fun j => -vy j) α K) * I))]

/-- **Sequential bootstrap CLT** for the split root. -/
theorem boot_root_seq {n m : ℕ → ℕ} (hn : Tendsto n atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hmr : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 κ)) {α B VX VY : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {vx : (k : ℕ) → Fin (n k) → ℝ} {vy : (k : ℕ) → Fin (m k) → ℝ}
    (hbx : ∀ k i, |vx k i| ≤ B) (hby : ∀ k j, |vy k j| ≤ B)
    (hVX : Tendsto (fun k => varLo (n k) α (vx k)) atTop (𝓝 VX))
    (hVY : Tendsto (fun k => varLo (m k) α (fun j => -vy k j)) atTop (𝓝 VY))
    (hDX : Tendsto (fun k => (n k : ℝ) * bAvg (fun I => bootD (vx k) α I ^ 2)) atTop (𝓝 0))
    (hDY : Tendsto (fun k => (m k : ℝ) * bAvg (fun J => bootD (fun j => -vy k j) α J ^ 2)) atTop (𝓝 0))
    (hσ : 0 < (VX + VY / κ) / (1 - α) ^ 2) (t : ℝ) :
    Tendsto (fun k => bAvg (fun p => if bootRoot (n k) (m k) α (vx k) (vy k) p ≤ t then (1 : ℝ) else 0)) atTop
      (𝓝 ((gaussianReal 0 ((VX + VY / κ) / (1 - α) ^ 2).toNNReal).real (Set.Iic t))) := by
  set β := 1 - α with hβdef
  have hβ : 0 < β := by linarith
  set σ2 := (VX + VY / κ) / β ^ 2 with hσ2
  have hnr : Tendsto (fun k => (n k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hnpos : ∀ᶠ k in atTop, 0 < n k := hn.eventually_gt_atTop 0
  have hmr' : Tendsto (fun k => (m k : ℝ)) atTop atTop := by
    refine (Tendsto.pos_mul_atTop hκ hmr hnr).congr' ?_
    filter_upwards [hnpos] with k hk
    have : (n k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp
  have hm : Tendsto m atTop atTop := tendsto_natCast_atTop_iff.1 hmr'
  have hmpos : ∀ᶠ k in atTop, 0 < m k := hm.eventually_gt_atTop 0
  have hnm : Tendsto (fun k => (n k : ℝ) / m k) atTop (𝓝 κ⁻¹) := by
    refine (hmr.inv₀ hκ.ne').congr fun k => ?_
    rw [inv_div]
  have hne : ∀ k, Nonempty ((Fin (n k) → Fin (n k)) × (Fin (m k) → Fin (m k))) := fun k => ⟨(fun i => i, fun j => j)⟩
  set R : (k : ℕ) → (Fin (n k) → Fin (n k)) × (Fin (m k) → Fin (m k)) → ℝ :=
    fun k => bootRoot (n k) (m k) α (vx k) (vy k)
  let ν : ℕ → ProbabilityMeasure ℝ := fun k => ⟨bootLaw (R k), by haveI := hne k; exact bootLaw_isProb _⟩
  let ν₀ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 σ2.toNNReal, inferInstance⟩
  have hσ2' : ((σ2.toNNReal : ℝ≥0) : ℝ) = σ2 := Real.coe_toNNReal _ hσ.le
  have hconv : Tendsto ν atTop (𝓝 ν₀) := by
    refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun s => ?_
    have htarget : charFun (ν₀ : Measure ℝ) s = exp (((-(s ^ 2 / β ^ 2 * VX / 2) : ℝ) : ℂ) + ((-(s ^ 2 * κ⁻¹ / β ^ 2 * VY / 2) : ℝ) : ℂ)) := by
      change charFun (gaussianReal 0 σ2.toNNReal) s = _
      rw [charFun_gaussianReal, hσ2']
      congr 1
      simp only [hσ2]
      push_cast
      field_simp
      ring
    rw [htarget, Complex.exp_add]
    -- linear part
    set uX : ℕ → ℝ := fun k => -(s * √(n k : ℝ) / (β * n k))
    set uY : ℕ → ℝ := fun k => -(s * √(n k : ℝ) / (β * m k))
    have huX : Tendsto (fun k => (n k : ℝ) * uX k ^ 2) atTop (𝓝 (s ^ 2 / β ^ 2)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hnpos] with k hk
      have hk' : (0 : ℝ) < n k := by exact_mod_cast hk
      simp only [uX]
      rw [neg_sq, div_pow, mul_pow, mul_pow, Real.sq_sqrt hk'.le]
      field_simp
    have huY : Tendsto (fun k => (m k : ℝ) * uY k ^ 2) atTop (𝓝 (s ^ 2 * κ⁻¹ / β ^ 2)) := by
      refine ((hnm.const_mul (s ^ 2)).div_const (β ^ 2)).congr' ?_
      filter_upwards [hnpos, hmpos] with k hk hk2
      have hk' : (0 : ℝ) < n k := by exact_mod_cast hk
      have hk2' : (0 : ℝ) < m k := by exact_mod_cast hk2
      simp only [uY]
      rw [neg_sq, div_pow, mul_pow, mul_pow, Real.sq_sqrt hk'.le]
      field_simp
    have hX := tendsto_char_side hn hα0 hα1 hbx hVX huX
    have hY := tendsto_char_side hm hα0 hα1 (v := fun k j => -vy k j) (fun k j => by rw [abs_neg]; exact hby k j)
      hVY huY
    have hlin := hX.mul hY
    -- the linear characteristic function
    have hLlim : Tendsto (fun k => linChar α (vx k) (vy k) (uX k * (n k : ℝ)) (uY k * (m k : ℝ))) atTop
        (𝓝 (exp (((-(s ^ 2 / β ^ 2 * VX / 2) : ℝ) : ℂ)) * exp (((-(s ^ 2 * κ⁻¹ / β ^ 2 * VY / 2) : ℝ) : ℂ)))) :=
      hlin.congr fun k => (linChar_eq α (vx k) (vy k) _ _).symm
    -- the remainder
    set W : ℕ → ℝ := fun k => 2 * s ^ 2 / β ^ 2 * ((n k : ℝ) * bAvg (fun I => bootD (vx k) α I ^ 2) +
      (n k : ℝ) / m k * ((m k : ℝ) * bAvg (fun J => bootD (fun j => -vy k j) α J ^ 2)))
    have hW : Tendsto W atTop (𝓝 0) := by
      have := (hDX.add (hnm.mul hDY)).const_mul (2 * s ^ 2 / β ^ 2)
      simpa using this
    have hsW : Tendsto (fun k => √(W k)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hW
      rwa [Real.sqrt_zero] at this
    have hbound : ∀ᶠ k in atTop, ‖charFun (ν k : Measure ℝ) s - linChar α (vx k) (vy k) (uX k * (n k : ℝ)) (uY k * (m k : ℝ))‖ ≤ √(W k) := by
      filter_upwards [hnpos, hmpos] with k hk hk2
      have : Nonempty ((Fin (n k) → Fin (n k)) × (Fin (m k) → Fin (m k))) := hne k
      have : Nonempty (Fin (n k) → Fin (n k)) := ⟨fun i => i⟩
      have : Nonempty (Fin (m k) → Fin (m k)) := ⟨fun i => i⟩
      have hk' : (0 : ℝ) < n k := by exact_mod_cast hk
      have hk2' : (0 : ℝ) < m k := by exact_mod_cast hk2
      change ‖charFun (bootLaw (R k)) s - linChar α (vx k) (vy k) (uX k * (n k : ℝ)) (uY k * (m k : ℝ))‖ ≤ √(W k)
      rw [charFun_bootLaw]
      unfold linChar
      set M : (Fin (n k) → Fin (n k)) × (Fin (m k) → Fin (m k)) → ℝ :=
        fun p => s * (√(n k : ℝ) / β * (bootD (vx k) α p.1 + bootD (fun j => -vy k j) α p.2))
      have hpt : ∀ p, ‖exp (↑(s * R k p) * I) - exp (↑(uX k * (n k : ℝ) * bootA (vx k) α p.1) * I) *
          exp (↑(uY k * (m k : ℝ) * bootA (fun j => -vy k j) α p.2) * I)‖ ≤ |M p| := fun p => by
        rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add]
        refine (norm_exp_sub_exp_le _ _).trans (le_of_eq ?_)
        congr 1
        simp only [R, M, uX, uY]
        rw [bootRoot_decomp hk hk2 hα0 hα1, ← hβdef]
        field_simp
        ring
      refine (norm_cAvg_sub_cAvg_le _ _).trans ?_
      refine (bAvg_mono hpt).trans ((bAvg_abs_le_sqrt M).trans (Real.sqrt_le_sqrt ?_))
      -- `E* M² ≤ W`
      have hM : ∀ p, M p ^ 2 ≤ 2 * s ^ 2 / β ^ 2 * (n k : ℝ) * (bootD (vx k) α p.1 ^ 2 + bootD (fun j => -vy k j) α p.2 ^ 2) :=
        fun p => by
          simp only [M]
          rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hk'.le]
          have := sq_nonneg (bootD (vx k) α p.1 - bootD (fun j => -vy k j) α p.2)
          have h2 : (bootD (vx k) α p.1 + bootD (fun j => -vy k j) α p.2) ^ 2 ≤
              2 * (bootD (vx k) α p.1 ^ 2 + bootD (fun j => -vy k j) α p.2 ^ 2) := by nlinarith
          calc s ^ 2 * ((n k : ℝ) / β ^ 2 * (bootD (vx k) α p.1 + bootD (fun j => -vy k j) α p.2) ^ 2)
              ≤ s ^ 2 * ((n k : ℝ) / β ^ 2 * (2 * (bootD (vx k) α p.1 ^ 2 + bootD (fun j => -vy k j) α p.2 ^ 2))) := by
                gcongr
            _ = _ := by ring
      refine (bAvg_mono hM).trans (le_of_eq ?_)
      rw [bAvg_const_mul, bAvg_add, bAvg_prod_fst (fun I => bootD (vx k) α I ^ 2),
        bAvg_prod_snd (fun J => bootD (fun j => -vy k j) α J ^ 2)]
      simp only [W]
      field_simp
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hL' := tendsto_iff_norm_sub_tendsto_zero.1 hLlim
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ (by rw [← add_zero (0 : ℝ)]; exact hsW.add hL')
    filter_upwards [hbound] with k hk
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hk le_rfl)
  -- portmanteau
  have hv : σ2.toNNReal ≠ 0 := by rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hσ
  have : NullSingletonClass (ν₀ : Measure ℝ) := nullSingletonClass_gaussianReal hv
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv (E := Set.Iic t) (by
    rw [frontier_Iic]; exact measure_singleton _)
  have key' := (ENNReal.tendsto_toReal (measure_ne_top (ν₀ : Measure ℝ) _)).comp key
  refine key'.congr fun k => ?_
  simp only [Function.comp]
  change ((bootLaw (R k)) (Set.Iic t)).toReal = _
  rw [← measureReal_def, bootLaw_real_Iic]

end StatFormal.Foundations.Bootstrap
