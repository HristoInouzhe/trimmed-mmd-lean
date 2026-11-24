import StatFormal.Archive.Wave17a.Statements
import StatFormal.Archive.OTFD.Wave8c.RouteCubic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Route: otfd B `lem:interior-levels` (untrusted)

* The cubic law is `(∏_k 1/(2a_k)) · Leb` on the box, so for `0 ≤ tD_∞ ≤ a_min` the Euclidean ball of radius
  `tD_∞` lies in the box and `c_K(t) = κ t^N`, `κ = ∏_k (2a_k)⁻¹ · ω_N · D_∞^N` (`ω_N` the unit-ball volume).
* Interiority: `|u_k| ≤ ‖u‖₂`; the point `a_min e_{k₀}` is a boundary point of the box in the region.
* The level equivalence uses `τ = c_K^{-1}(p)` (`Wave8c` route: `p ≤ c_K(τ)`, minimality) and strict
  monotonicity / continuity of `κ t^N`.
* Vanishing: `c_K(a_min/D_∞) = ω_N ∏_k (a_min/(2a_k)) ≤ (√π/2)^N / Γ(N/2+1) ≤ (√π/2)^N → 0`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace StatFormal.Wave17a

open StatFormal.OTFD.Wave8c

section Cubic
variable {N : ℕ} {a : Fin N → ℝ}

lemma cubicLaw_eq (ha : ∀ k, 0 < a k) :
    cubicLaw a = (∏ k, ENNReal.ofReal (1 / (2 * a k))) • volume.restrict (cubeBox a) := by
  haveI : ∀ k, IsProbabilityMeasure (unifSym (a k)) := fun k => unifSym_prob (ha k)
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs), cubeBox, ← Set.pi_inter_distrib,
    volume_pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [unifSym, Measure.smul_apply, Measure.restrict_apply (hs k), smul_eq_mul]

lemma norm_toLp (u : Fin N → ℝ) : ‖WithLp.toLp 2 u‖ = Real.sqrt (∑ k, u k ^ 2) := by
  rw [EuclideanSpace.norm_eq]; simp

lemma ball_sub_box (ha : ∀ k, 0 < a k) {k₀ : Fin N} (hmin : ∀ k, a k₀ ≤ a k) {r : ℝ} (hr : r ≤ a k₀) :
    {u : Fin N → ℝ | Real.sqrt (∑ k, u k ^ 2) ≤ r} ⊆ cubeBox a := by
  intro u hu k _
  have h1 : |u k| ≤ Real.sqrt (∑ k, u k ^ 2) :=
    Real.abs_le_sqrt (Finset.single_le_sum (f := fun k => u k ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ k))
  have h2 : |u k| ≤ a k := h1.trans (le_trans hu (hr.trans (hmin k)))
  exact ⟨by linarith [neg_abs_le (u k)], (le_abs_self _).trans h2⟩

/-- The unit-ball volume `ω_N = √π^N / Γ(N/2+1)`. -/
def omegaN (N : ℕ) : ℝ := Real.sqrt Real.pi ^ N / Real.Gamma (N / 2 + 1)

lemma omegaN_pos (N : ℕ) : 0 < omegaN N :=
  div_pos (pow_pos (Real.sqrt_pos.2 Real.pi_pos) _) (Real.Gamma_pos_of_pos (by positivity))

lemma volume_euclid_ball (hN : 0 < N) {r : ℝ} (hr : 0 ≤ r) :
    volume {u : Fin N → ℝ | Real.sqrt (∑ k, u k ^ 2) ≤ r} = ENNReal.ofReal (omegaN N * r ^ N) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hset : {u : Fin N → ℝ | Real.sqrt (∑ k, u k ^ 2) ≤ r} =
      (WithLp.toLp 2) ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) r := by
    ext u; simp [norm_toLp]
  rw [hset, (PiLp.volume_preserving_toLp (Fin N)).measure_preimage measurableSet_closedBall.nullMeasurableSet,
    EuclideanSpace.volume_closedBall, Fintype.card_fin, ← ENNReal.ofReal_pow hr,
    ← ENNReal.ofReal_mul (by positivity), omegaN]
  congr 1; ring

/-- `c_K(t) = κ t^N` on `0 ≤ t D_∞ ≤ a_min`. -/
lemma cK_formula (ha : ∀ k, 0 < a k) {k₀ : Fin N} (hmin : ∀ k, a k₀ ≤ a k) {Dinf t : ℝ} (hD : 0 < Dinf)
    (ht : 0 ≤ t) (htD : t * Dinf ≤ a k₀) :
    cK a Dinf t = (∏ k, 1 / (2 * a k)) * omegaN N * Dinf ^ N * t ^ N := by
  have hN : 0 < N := Fin.pos k₀
  have hset : {u : Fin N → ℝ | rhoBox Dinf u ≤ t} = {u | Real.sqrt (∑ k, u k ^ 2) ≤ t * Dinf} := by
    ext u; simp only [mem_setOf_eq, rhoBox, div_le_iff₀ hD]
  rw [cK, hset, measureReal_def, cubicLaw_eq ha, Measure.smul_apply,
    Measure.restrict_apply' (show MeasurableSet (cubeBox a) from MeasurableSet.univ_pi fun k => measurableSet_Icc),
    inter_eq_left.2 (ball_sub_box ha hmin htD), volume_euclid_ball hN (mul_nonneg ht hD.le), smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_prod,
    ENNReal.toReal_ofReal (mul_nonneg (omegaN_pos N).le (pow_nonneg (mul_nonneg ht hD.le) _)),
    Finset.prod_congr rfl fun k _ => ENNReal.toReal_ofReal (by have := ha k; positivity)]
  rw [mul_pow]; ring

lemma kappa_pos (ha : ∀ k, 0 < a k) {Dinf : ℝ} (hD : 0 < Dinf) :
    0 < (∏ k, 1 / (2 * a k)) * omegaN N * Dinf ^ N :=
  mul_pos (mul_pos (Finset.prod_pos fun k _ => by have := ha k; positivity) (omegaN_pos N)) (pow_pos hD _)

end Cubic

theorem interior_levels_naive : Claims.interior_levels_naive := by
  intro K M p hp u hu
  have hcont : Continuous (mnorm M) := by
    unfold mnorm
    fun_prop
  exact interior_maximal (t := {u | mnorm M u < 1}) (fun x (hx : mnorm M x < 1) => le_of_lt hx)
    (isOpen_lt hcont continuous_const) (lt_of_le_of_lt hu hp)

theorem interior_levels_cubic : Claims.interior_levels_cubic := by
  intro N a Dinf p k₀ ha hmin hD hp0 hp1
  have hN : 0 < N := Fin.pos k₀
  have hset : CubicSetting a 1 Dinf := ⟨hN, ha, one_pos, hD⟩
  obtain ⟨hτ0, hτp, hτmin⟩ := tau_props hset hp0 hp1.le
  set τ := tauKp a Dinf p
  refine ⟨⟨fun hsub => ?_, fun hlt => ?_⟩, ⟨fun hlt => ?_, fun hlt => ?_⟩⟩
  · -- the point `a_min e_{k₀}`
    by_contra hge
    push Not at hge
    set u : Fin N → ℝ := Pi.single k₀ (a k₀)
    have hu : u ∈ cubicRegion a Dinf τ := by
      refine ⟨fun k _ => ?_, ?_⟩
      · by_cases hk : k = k₀
        · subst hk; simp [u, (ha k).le]
        · simp [u, hk, (ha k).le]
      · change Real.sqrt (∑ k, u k ^ 2) / Dinf ≤ τ
        rw [div_le_iff₀ hD]
        have : ∑ k, u k ^ 2 = a k₀ ^ 2 := by
          rw [Finset.sum_eq_single k₀ (fun b _ hb => by simp [u, hb]) (by simp)]; simp [u]
        rw [this, Real.sqrt_sq (ha k₀).le]; linarith
    have hint := hsub hu
    rw [cubeBox, interior_pi_set Set.finite_univ] at hint
    have := (hint k₀ (mem_univ _))
    simp only [interior_Icc, mem_Ioo] at this
    simp [u] at this
  · intro u ⟨_, hu⟩
    rw [cubeBox, interior_pi_set Set.finite_univ]
    intro k _
    change u k ∈ interior (Icc _ _)
    rw [interior_Icc]
    have hu' : Real.sqrt (∑ k, u k ^ 2) ≤ τ * Dinf := by
      have : rhoBox Dinf u ≤ τ := hu
      rwa [rhoBox, div_le_iff₀ hD] at this
    have h1 : |u k| ≤ Real.sqrt (∑ k, u k ^ 2) :=
      Real.abs_le_sqrt (Finset.single_le_sum (f := fun k => u k ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ k))
    have h2 : |u k| < a k := lt_of_le_of_lt (h1.trans hu') (lt_of_lt_of_le hlt (hmin k))
    exact ⟨by linarith [neg_abs_le (u k)], (le_abs_self _).trans_lt h2⟩
  · -- `τ D_∞ < a_min ⇒ p < c_K(a_min/D_∞)`
    set s := a k₀ / Dinf
    have hτs : τ < s := by rw [lt_div_iff₀ hD]; exact hlt
    have hs0 : 0 ≤ s := div_nonneg (ha k₀).le hD.le
    rw [cK_formula ha hmin hD hs0 (by rw [div_mul_cancel₀ _ hD.ne'])]
    rw [cK_formula ha hmin hD hτ0 hlt.le] at hτp
    have := kappa_pos ha hD (N := N)
    have hpow : τ ^ N < s ^ N := pow_lt_pow_left₀ hτs hτ0 hN.ne'
    nlinarith
  · -- `p < c_K(a_min/D_∞) ⇒ τ D_∞ < a_min`
    set s := a k₀ / Dinf
    have hs : 0 < s := div_pos (ha k₀) hD
    rw [cK_formula ha hmin hD hs.le (by rw [div_mul_cancel₀ _ hD.ne'])] at hlt
    set κ := (∏ k, 1 / (2 * a k)) * omegaN N * Dinf ^ N
    have hc : ContinuousAt (fun t : ℝ => κ * t ^ N) s := by fun_prop
    have hev : ∀ᶠ t in 𝓝[<] s, p < κ * t ^ N :=
      (hc.tendsto.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hlt)
    have hev2 : ∀ᶠ t in 𝓝[<] s, t ∈ Ioo 0 s := Ioo_mem_nhdsLT hs
    obtain ⟨t, ht1, ⟨ht0, hts⟩⟩ := (hev.and hev2).exists
    have htD : t * Dinf ≤ a k₀ := by
      have := (lt_div_iff₀ hD).1 hts; linarith
    have hcK : p ≤ cK a Dinf t := by rw [cK_formula ha hmin hD ht0.le htD]; exact ht1.le
    have := hτmin t hcK
    have := (lt_div_iff₀ hD).1 (lt_of_le_of_lt this hts)
    linarith

theorem interior_levels_vanish : Claims.interior_levels_vanish := by
  intro lam Dinf hlam hD
  set r := Real.sqrt Real.pi / 2
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [div_lt_one (by norm_num), Real.sqrt_lt' (by norm_num)]
    linarith [Real.pi_lt_four]
  have hlim : Tendsto (fun K : ℕ => r ^ (K + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp (tendsto_add_atTop_nat 1)
  refine squeeze_zero' (Eventually.of_forall fun K => measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with K hK
  set a : Fin (K + 1) → ℝ := fun k => lam k / 2
  have ha : ∀ k, 0 < a k := fun k => by have := hlam k; simp only [a]; positivity
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin (K + 1))) a
  have hmin : ∀ k, a k₀ ≤ a k := fun k => hk₀ ▸ Finset.inf'_le _ (Finset.mem_univ k)
  rw [hk₀]
  set s := a k₀ / Dinf K
  have hs0 : 0 ≤ s := div_nonneg (ha k₀).le (hD K).le
  rw [cK_formula ha hmin (hD K) hs0 (by rw [div_mul_cancel₀ _ (hD K).ne'])]
  -- `= ω_N ∏_k a_min/(2a_k)`
  have h1 : Dinf K ^ (K + 1) * s ^ (K + 1) = a k₀ ^ (K + 1) := by
    rw [← mul_pow, mul_div_cancel₀ _ (hD K).ne']
  have h2 : ∏ k, (a k₀ / (2 * a k)) = a k₀ ^ (K + 1) * ∏ k, 1 / (2 * a k) := by
    simp_rw [div_eq_mul_one_div (a k₀)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have heq : (∏ k, 1 / (2 * a k)) * omegaN (K + 1) * Dinf K ^ (K + 1) * s ^ (K + 1) =
      omegaN (K + 1) * ∏ k, (a k₀ / (2 * a k)) := by
    rw [show (∏ k, 1 / (2 * a k)) * omegaN (K + 1) * Dinf K ^ (K + 1) * s ^ (K + 1) =
      (∏ k, 1 / (2 * a k)) * omegaN (K + 1) * (Dinf K ^ (K + 1) * s ^ (K + 1)) by ring, h1, h2]
    ring
  rw [heq]
  have hprod : ∏ k, (a k₀ / (2 * a k)) ≤ (1 / 2) ^ (K + 1) := by
    calc ∏ k, (a k₀ / (2 * a k)) ≤ ∏ _k : Fin (K + 1), (1 / 2 : ℝ) :=
          Finset.prod_le_prod₀ (fun k _ => by have := ha k; have := ha k₀; positivity)
            fun k _ => by
              rw [div_le_iff₀ (by have := ha k; positivity)]; linarith [hmin k]
      _ = _ := by simp
  have hG : 1 ≤ Real.Gamma (((K + 1 : ℕ) : ℝ) / 2 + 1) := by
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hx : (2 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) / 2 + 1 := by push_cast; linarith
    calc (1 : ℝ) = Real.Gamma 2 := Real.Gamma_two.symm
      _ ≤ _ := Real.Gamma_strictMonoOn_Ici.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx
  have hω : omegaN (K + 1) ≤ Real.sqrt Real.pi ^ (K + 1) := by
    unfold omegaN
    exact div_le_self (by positivity) hG
  calc omegaN (K + 1) * ∏ k, (a k₀ / (2 * a k)) ≤ Real.sqrt Real.pi ^ (K + 1) * (1 / 2) ^ (K + 1) :=
        mul_le_mul hω hprod (Finset.prod_nonneg fun k _ => by have := ha k; have := ha k₀; positivity)
          (by positivity)
    _ = r ^ (K + 1) := by rw [← mul_pow]; ring

end StatFormal.Wave17a
