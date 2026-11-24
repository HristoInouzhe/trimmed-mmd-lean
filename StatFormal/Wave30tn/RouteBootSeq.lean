import StatFormal.Lib.Bootstrap.CltProb
import StatFormal.Lib.Bootstrap.AlphaZero
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Route — wave 30tn: the bootstrap CLT of the split statistic for arbitrary sizes, deterministic form (untrusted)

For data `v_x^{(k)} ∈ ℝ^{n_k}`, `v_y^{(k)} ∈ ℝ^{m_k}` (`|·| ≤ B`, `n_k, m_k → ∞`, no ratio condition) and the standardisation
`s_k = √(V_X/n_k + V_Y/m_k)/β`, the bootstrap cdf of `(T̂* − T̂)/s_k` converges to `Φ` at every point
(`boot_std_seq`), provided each side is either non-degenerate (`V > 0`, plug-in variance `→ V`, `N E*[D*²] → 0`, the
hypotheses of the library's ratio-regime `boot_root_seq`) or exactly degenerate (`V = 0` and `A* ≡ D* ≡ 0`, which is
what happens for an almost surely constant sample).

Proof: `β(T̂* − T̂) = −(A_X* + A_Y*) + (D_X* + D_Y*)` (library `boot_decomp`); the characteristic function of the linear
part factorises over the two resamples (`linChar_eq`); with the share `w_k = (V_X/n_k)/S_k ∈ [0,1]`, along every
subsequence pick a further one with `w_k → w₀` (Bolzano–Weierstrass): the library's triangular-array limit
`tendsto_char_side` gives the factors `e^{−s²w₀/2}` and `e^{−s²(1−w₀)/2}` (a degenerate side is identically `1`), whose
product `e^{−s²/2}` does not depend on `w₀` (subsequence principle). The remainder moves the characteristic function by
at most `√(2s²(E*D_X²/S_k + E*D_Y²/S_k)) → 0` (`S_k ≥ V_X/n_k`). Lévy's continuity theorem and the portmanteau theorem
conclude, as in `boot_root_seq`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open Finset Complex Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave30tn

open StatFormal.TrimmedMMD.BangBang StatFormal.Foundations.TrimmedMean StatFormal.Foundations.Bootstrap

/-- One side of the root is admissible: non-degenerate with converging plug-in variance and vanishing remainder, or
exactly degenerate. -/
def SideSeq (N : ℕ → ℕ) (α V : ℝ) (v : (k : ℕ) → Fin (N k) → ℝ) : Prop :=
  (0 < V ∧ Tendsto (fun k => varLo (N k) α (v k)) atTop (𝓝 V) ∧
      Tendsto (fun k => (N k : ℝ) * bAvg (fun I => bootD (v k) α I ^ 2)) atTop (𝓝 0)) ∨
    (V = 0 ∧ ∀ k I, bootA (v k) α I = 0 ∧ bootD (v k) α I = 0)

lemma SideSeq.nonneg {N : ℕ → ℕ} {α V : ℝ} {v : (k : ℕ) → Fin (N k) → ℝ} (h : SideSeq N α V v) : 0 ≤ V := by
  rcases h with h | h
  · exact h.1.le
  · exact h.1.ge

/-- The standardised bootstrap root `(T̂*(I, J) − T̂)/s`. -/
def stdRoot (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) (s : ℝ) (p : (Fin n → Fin n) × (Fin m → Fin m)) : ℝ :=
  ((tLo n α (vx ∘ p.1) - tUp m α (vy ∘ p.2)) - (tLo n α vx - tUp m α vy)) / s

lemma rep_decomp {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (vx : Fin n → ℝ)
    (vy : Fin m → ℝ) (p : (Fin n → Fin n) × (Fin m → Fin m)) :
    (1 - α) * ((tLo n α (vx ∘ p.1) - tUp m α (vy ∘ p.2)) - (tLo n α vx - tUp m α vy)) =
      -(bootA vx α p.1 + bootA (fun j => -vy j) α p.2) + (bootD vx α p.1 + bootD (fun j => -vy j) α p.2) := by
  have h1 := boot_decomp vx hn hα0 hα1 p.1
  have h2 := boot_decomp (fun j => -vy j) hm hα0 hα1 p.2
  have e1 : tUp m α (vy ∘ p.2) = -tLo m α ((fun j => -vy j) ∘ p.2) := trimUp_eq hm hα0 hα1 _
  have e2 : tUp m α vy = -tLo m α (fun j => -vy j) := trimUp_eq hm hα0 hα1 vy
  rw [e1, e2]
  linear_combination h1 + h2

/-- The factor of one side along a subsequence on which its share converges. -/
lemma side_factor {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (hN0 : ∀ k, 0 < N k) {α B V : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {v : (k : ℕ) → Fin (N k) → ℝ} (hb : ∀ k i, |v k i| ≤ B) (hS : SideSeq N α V v)
    {σ : ℕ → ℝ} (hσ : ∀ k, 0 < σ k) {w : ℕ → ℝ} (hw : ∀ k, w k = (V / N k) / σ k ^ 2) {w₀ : ℝ}
    (hw₀ : Tendsto w atTop (𝓝 w₀)) (s : ℝ) :
    Tendsto (fun k => cAvg (fun K : Fin (N k) → Fin (N k) => exp (↑((-s / σ k) * bootA (v k) α K) * I))) atTop
      (𝓝 (exp ((-(s ^ 2 * w₀ / 2) : ℝ) : ℂ))) := by
  rcases hS with ⟨hV, hVl, -⟩ | ⟨hV0, hdeg⟩
  · set u : ℕ → ℝ := fun k => -s / (σ k * N k)
    have hu : Tendsto (fun k => (N k : ℝ) * u k ^ 2) atTop (𝓝 (s ^ 2 * w₀ / V)) := by
      refine ((hw₀.const_mul (s ^ 2)).div_const V).congr fun k => ?_
      have hNk : (0 : ℝ) < N k := by exact_mod_cast hN0 k
      have hsk := hσ k
      simp only [u, hw k]
      field_simp
    have key := tendsto_char_side hN hα0 hα1 hb hVl hu
    have e : -(s ^ 2 * w₀ / V * V / 2) = -(s ^ 2 * w₀ / 2) := by field_simp
    rw [e] at key
    refine key.congr fun k => ?_
    congr 1; funext K; congr 3
    have hNk : (N k : ℝ) ≠ 0 := by exact_mod_cast (hN0 k).ne'
    have hsk := (hσ k).ne'
    simp only [u]; field_simp
  · have hw0 : ∀ k, w k = 0 := fun k => by rw [hw k, hV0, zero_div, zero_div]
    have : w₀ = 0 := tendsto_nhds_unique hw₀ (tendsto_const_nhds.congr fun k => (hw0 k).symm)
    subst this
    refine tendsto_const_nhds.congr fun k => ?_
    have : Nonempty (Fin (N k) → Fin (N k)) := ⟨fun i => i⟩
    simp only [(hdeg k _).1, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_zero, zero_div,
      neg_zero]
    unfold cAvg
    rw [sum_const, card_univ, nsmul_eq_mul, mul_one]
    have : (Fintype.card (Fin (N k) → Fin (N k)) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

/-- **Sequential bootstrap CLT for arbitrary sizes** (standardised root). -/
theorem boot_std_seq {n m : ℕ → ℕ} (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hn0 : ∀ k, 0 < n k) (hm0 : ∀ k, 0 < m k) {α B VX VY : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {vx : (k : ℕ) → Fin (n k) → ℝ} {vy : (k : ℕ) → Fin (m k) → ℝ}
    (hbx : ∀ k i, |vx k i| ≤ B) (hby : ∀ k j, |vy k j| ≤ B)
    (hX : SideSeq n α VX vx) (hY : SideSeq m α VY (fun k j => -vy k j)) (hpos : 0 < VX + VY) (t : ℝ) :
    Tendsto (fun k => bAvg (fun p => if stdRoot (n k) (m k) α (vx k) (vy k)
        (√(VX / n k + VY / m k) / (1 - α)) p ≤ t then (1 : ℝ) else 0)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic t))) := by
  set β := 1 - α with hβdef
  have hβ : 0 < β := by linarith
  have hVX := hX.nonneg
  have hVY := hY.nonneg
  have hnr : ∀ k, (0 : ℝ) < n k := fun k => by exact_mod_cast hn0 k
  have hmr : ∀ k, (0 : ℝ) < m k := fun k => by exact_mod_cast hm0 k
  set S : ℕ → ℝ := fun k => VX / n k + VY / m k with hSdef
  have hS0 : ∀ k, 0 < S k := fun k => by
    have := hnr k; have := hmr k
    rcases hVX.eq_or_lt with h | h
    · have : 0 < VY := by linarith
      simp only [S, ← h, zero_div, zero_add]; positivity
    · have : 0 ≤ VY / m k := by positivity
      simp only [S]; have : 0 < VX / n k := by positivity
      linarith
  set σ : ℕ → ℝ := fun k => √(S k) with hσdef
  have hσ0 : ∀ k, 0 < σ k := fun k => Real.sqrt_pos.2 (hS0 k)
  have hσsq : ∀ k, σ k ^ 2 = S k := fun k => Real.sq_sqrt (hS0 k).le
  have hne : ∀ k, Nonempty ((Fin (n k) → Fin (n k)) × (Fin (m k) → Fin (m k))) := fun k => ⟨(fun i => i, fun j => j)⟩
  set R : (k : ℕ) → (Fin (n k) → Fin (n k)) × (Fin (m k) → Fin (m k)) → ℝ :=
    fun k => stdRoot (n k) (m k) α (vx k) (vy k) (√(VX / n k + VY / m k) / (1 - α))
  have hR : ∀ k p, R k p = (-(bootA (vx k) α p.1 + bootA (fun j => -vy k j) α p.2) +
      (bootD (vx k) α p.1 + bootD (fun j => -vy k j) α p.2)) / σ k := fun k p => by
    simp only [R, stdRoot]
    rw [← rep_decomp (hn0 k) (hm0 k) hα0 hα1 (vx k) (vy k) p]
    have := hσ0 k
    change _ / (σ k / β) = β * _ / σ k
    field_simp
  let ν : ℕ → ProbabilityMeasure ℝ := fun k => ⟨bootLaw (R k), by haveI := hne k; exact bootLaw_isProb _⟩
  let ν₀ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  -- shares
  set w : ℕ → ℝ := fun k => (VX / n k) / σ k ^ 2 with hwdef
  set w' : ℕ → ℝ := fun k => (VY / m k) / σ k ^ 2 with hw'def
  have hww' : ∀ k, w' k = 1 - w k := fun k => by
    simp only [w, w', hσsq k]; have := hS0 k; field_simp; simp only [S]; ring
  have hwI : ∀ k, w k ∈ Set.Icc (0 : ℝ) 1 := fun k => by
    have h1 : 0 ≤ VX / n k := div_nonneg hVX (hnr k).le
    have h2 : 0 ≤ VY / m k := div_nonneg hVY (hmr k).le
    simp only [w, hσsq k]
    exact ⟨div_nonneg h1 (hS0 k).le, (div_le_one (hS0 k)).2 (le_add_of_nonneg_right h2)⟩
  have hconv : Tendsto ν atTop (𝓝 ν₀) := by
    refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun s => ?_
    have htarget : charFun (ν₀ : Measure ℝ) s = exp ((-(s ^ 2 / 2) : ℝ) : ℂ) := by
      change charFun (gaussianReal 0 1) s = _
      rw [charFun_gaussianReal]
      congr 1; push_cast; ring
    rw [htarget]
    -- the linear part, by subsequences
    set L : ℕ → ℂ := fun k => linChar α (vx k) (vy k) (-s / σ k) (-s / σ k) with hLdef
    have hL : Tendsto L atTop (𝓝 (exp ((-(s ^ 2 / 2) : ℝ) : ℂ))) := by
      refine tendsto_of_subseq_tendsto fun ns hns => ?_
      obtain ⟨w₀, hw₀mem, ψ, hψ, hψt⟩ := tendsto_subseq_of_bounded (x := fun k => w (ns k))
        (Metric.isBounded_Icc (0 : ℝ) 1) (fun k => hwI (ns k))
      rw [closure_Icc] at hw₀mem
      refine ⟨ψ, ?_⟩
      have hNs : Tendsto (fun k => ns (ψ k)) atTop atTop := hns.comp hψ.tendsto_atTop
      have hXs : SideSeq (fun k => n (ns (ψ k))) α VX (fun k => vx (ns (ψ k))) := by
        rcases hX with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2.comp hNs, h3.comp hNs⟩
        · exact Or.inr ⟨h1, fun k I => h2 _ I⟩
      have hYs : SideSeq (fun k => m (ns (ψ k))) α VY (fun k j => -vy (ns (ψ k)) j) := by
        rcases hY with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2.comp hNs, h3.comp hNs⟩
        · exact Or.inr ⟨h1, fun k I => h2 _ I⟩
      have fX := side_factor (hn.comp hNs) (fun k => hn0 _) hα0 hα1 (fun k i => hbx _ i) hXs
        (σ := fun k => σ (ns (ψ k))) (fun k => hσ0 _) (w := fun k => w (ns (ψ k))) (fun k => rfl) hψt s
      have hw'₀ : Tendsto (fun k => w' (ns (ψ k))) atTop (𝓝 (1 - w₀)) :=
        (tendsto_const_nhds.sub hψt).congr fun k => (hww' _).symm
      have fY := side_factor (hm.comp hNs) (fun k => hm0 _) hα0 hα1
        (v := fun k j => -vy (ns (ψ k)) j) (fun k j => by rw [abs_neg]; exact hby _ j) hYs
        (σ := fun k => σ (ns (ψ k))) (fun k => hσ0 _) (w := fun k => w' (ns (ψ k))) (fun k => rfl) hw'₀ s
      have hprod := fX.mul fY
      rw [← Complex.exp_add, ← Complex.ofReal_add,
        show -(s ^ 2 * w₀ / 2) + -(s ^ 2 * (1 - w₀) / 2) = -(s ^ 2 / 2) by ring] at hprod
      refine hprod.congr fun k => ?_
      simp only [Function.comp, L]
      rw [linChar_eq]
    -- the remainder
    set W : ℕ → ℝ := fun k => 2 * s ^ 2 * (bAvg (fun I => bootD (vx k) α I ^ 2) / S k +
      bAvg (fun J => bootD (fun j => -vy k j) α J ^ 2) / S k) with hWdef
    have hside0 : ∀ {N : ℕ → ℕ} {V : ℝ} {v : (k : ℕ) → Fin (N k) → ℝ}, SideSeq N α V v → (∀ k, 0 < N k) →
        (∀ k, V / N k ≤ S k) → Tendsto (fun k => bAvg (fun I => bootD (v k) α I ^ 2) / S k) atTop (𝓝 0) := by
      intro N V v hS hN0 hle
      rcases hS with ⟨hV, -, hD⟩ | ⟨-, hdeg⟩
      · refine squeeze_zero (fun k => div_nonneg (bAvg_nonneg fun _ => sq_nonneg _) (hS0 k).le) (fun k => ?_)
          (by simpa using hD.div_const V)
        have hNk : (0 : ℝ) < N k := by exact_mod_cast hN0 k
        have hE := bAvg_nonneg fun I : Fin (N k) → Fin (N k) => sq_nonneg (bootD (v k) α I)
        rw [div_le_div_iff₀ (hS0 k) hV]
        have := hle k
        rw [div_le_iff₀ hNk] at this
        nlinarith
      · refine tendsto_const_nhds.congr fun k => ?_
        have : Nonempty (Fin (N k) → Fin (N k)) := ⟨fun i => i⟩
        simp only [(hdeg k _).2]
        rw [bAvg_const]; simp
    have hW : Tendsto W atTop (𝓝 0) := by
      have := ((hside0 hX hn0 fun k => le_add_of_nonneg_right (div_nonneg hVY (hmr k).le)).add
        (hside0 hY hm0 fun k => le_add_of_nonneg_left (div_nonneg hVX (hnr k).le))).const_mul (2 * s ^ 2)
      simpa using this
    have hsW : Tendsto (fun k => √(W k)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hW
      rwa [Real.sqrt_zero] at this
    have hbound : ∀ k, ‖charFun (ν k : Measure ℝ) s - L k‖ ≤ √(W k) := by
      intro k
      have : Nonempty ((Fin (n k) → Fin (n k)) × (Fin (m k) → Fin (m k))) := hne k
      have : Nonempty (Fin (n k) → Fin (n k)) := ⟨fun i => i⟩
      have : Nonempty (Fin (m k) → Fin (m k)) := ⟨fun i => i⟩
      change ‖charFun (bootLaw (R k)) s - L k‖ ≤ √(W k)
      rw [charFun_bootLaw]
      simp only [L]
      unfold linChar
      set M : (Fin (n k) → Fin (n k)) × (Fin (m k) → Fin (m k)) → ℝ :=
        fun p => s * ((bootD (vx k) α p.1 + bootD (fun j => -vy k j) α p.2) / σ k)
      have hpt : ∀ p, ‖exp (↑(s * R k p) * I) - exp (↑((-s / σ k) * bootA (vx k) α p.1) * I) *
          exp (↑((-s / σ k) * bootA (fun j => -vy k j) α p.2) * I)‖ ≤ |M p| := fun p => by
        rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add]
        refine (norm_exp_sub_exp_le _ _).trans (le_of_eq ?_)
        congr 1
        simp only [M]
        rw [hR k p]
        have := hσ0 k
        field_simp
        ring
      refine (norm_cAvg_sub_cAvg_le _ _).trans ?_
      refine (bAvg_mono hpt).trans ((bAvg_abs_le_sqrt M).trans (Real.sqrt_le_sqrt ?_))
      have hM : ∀ p, M p ^ 2 ≤ 2 * s ^ 2 / S k * (bootD (vx k) α p.1 ^ 2 + bootD (fun j => -vy k j) α p.2 ^ 2) :=
        fun p => by
          simp only [M]
          rw [mul_pow, div_pow, hσsq k]
          have := sq_nonneg (bootD (vx k) α p.1 - bootD (fun j => -vy k j) α p.2)
          have h2 : (bootD (vx k) α p.1 + bootD (fun j => -vy k j) α p.2) ^ 2 ≤
              2 * (bootD (vx k) α p.1 ^ 2 + bootD (fun j => -vy k j) α p.2 ^ 2) := by nlinarith
          have hS := hS0 k
          calc s ^ 2 * ((bootD (vx k) α p.1 + bootD (fun j => -vy k j) α p.2) ^ 2 / S k)
              ≤ s ^ 2 * (2 * (bootD (vx k) α p.1 ^ 2 + bootD (fun j => -vy k j) α p.2 ^ 2) / S k) := by gcongr
            _ = _ := by ring
      refine (bAvg_mono hM).trans (le_of_eq ?_)
      rw [bAvg_const_mul, bAvg_add, bAvg_prod_fst (fun I => bootD (vx k) α I ^ 2),
        bAvg_prod_snd (fun J => bootD (fun j => -vy k j) α J ^ 2)]
      simp only [W]
      have := hS0 k
      field_simp
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hL' := tendsto_iff_norm_sub_tendsto_zero.1 hL
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ (by rw [← add_zero (0 : ℝ)]; exact hsW.add hL')
    exact Eventually.of_forall fun k => (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (hbound k) le_rfl)
  -- portmanteau
  have : NullSingletonClass (ν₀ : Measure ℝ) := nullSingletonClass_gaussianReal one_ne_zero
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv (E := Set.Iic t) (by
    rw [frontier_Iic]; exact measure_singleton _)
  have key' := (ENNReal.tendsto_toReal (measure_ne_top (ν₀ : Measure ℝ) _)).comp key
  refine key'.congr fun k => ?_
  simp only [Function.comp]
  change ((bootLaw (R k)) (Set.Iic t)).toReal = _
  rw [← measureReal_def, bootLaw_real_Iic]

end StatFormal.Wave30tn
