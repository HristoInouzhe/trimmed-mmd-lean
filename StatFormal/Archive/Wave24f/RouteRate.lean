import StatFormal.Archive.Wave24f.Statements
import StatFormal.Archive.OTFD.Wave16b.RouteRates
import StatFormal.Archive.OTFD.WaveL3.RouteHilbert
import StatFormal.Archive.OTFD.Wave8b.RouteNaive

/-!
# Route — A `cor:app-sample-rate` (untrusted)

`eq:app-rate-decomp` is the certified `Wave16b.rate_decomp` with `ι = ι_K` (an isometry for orthonormal `e`). The sieve
term is `(∫ ‖ι_K F_K(Π_K x) − 𝔽(x)‖² dP)^{1/2}` because every `X_i` has law `P`; it tends to `0` along `K_n → ∞` by the
certified `WaveL3.sieve_strong_limit_uncond`. The grid term tends to `0` by `ass:app-grid-stability`, and
`ENNReal.limsup_add_of_right_tendsto_zero` removes both.
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave24f

open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.Wave16b (rmsE)

section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `ι_K` as a linear isometry (orthonormal `e`). -/
def embedLI {e : ℕ → H} (he : Orthonormal ℝ e) (K : ℕ) : Euc K →ₗᵢ[ℝ] H where
  toFun := embed e K
  map_add' a b := by simp only [embed, PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp only [embed, PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
    RingHom.id_apply]
  norm_map' z := StatFormal.OTFD.Wave8b.norm_embed e he z

@[simp] lemma embedLI_apply {e : ℕ → H} (he : Orthonormal ℝ e) (K : ℕ) (z : Euc K) :
    embedLI he K z = embed e K z := rfl

end

/-- `rmsE` of `g(X_i)` with every `X_i` of law `Q` is at most `(∫ g² dQ)^{1/2}` (equality for `n ≥ 1`). -/
lemma rmsE_iid_le {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H] (Pr : Measure Ω) {n : ℕ}
    (X : Ω → Fin n → H) (Q : Measure H) (g : H → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hX : ∀ i, Measurable fun ω => X ω i) (hlaw : ∀ i, Pr.map (fun ω => X ω i) = Q) :
    rmsE Pr (fun ω i => g (X ω i)) ≤ (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂Q) ^ (1 / 2 : ℝ) := by
  unfold rmsE
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  refine ENNReal.rpow_le_rpow (le_of_eq ?_) (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpt : ∀ ω, ENNReal.ofReal ((1 / n : ℝ) * ∑ i, g (X ω i) ^ 2) =
      ∑ i, ENNReal.ofReal (1 / n : ℝ) * ENNReal.ofReal (g (X ω i) ^ 2) := by
    intro ω
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _),
      Finset.mul_sum]
  simp_rw [hpt]
  have hmeas : ∀ i, Measurable fun ω => ENNReal.ofReal (g (X ω i) ^ 2) := fun i =>
    ENNReal.measurable_ofReal.comp ((hg.comp (hX i)).pow_const 2)
  rw [lintegral_finsetSum _ (fun i _ => (hmeas i).const_mul _)]
  have hi : ∀ i, ∫⁻ ω, ENNReal.ofReal (1 / n : ℝ) * ENNReal.ofReal (g (X ω i) ^ 2) ∂Pr =
      ENNReal.ofReal (1 / n : ℝ) * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂Q := by
    intro i
    rw [lintegral_const_mul _ (hmeas i), ← hlaw i,
      lintegral_map (f := fun x => ENNReal.ofReal (g x ^ 2)) (ENNReal.measurable_ofReal.comp (hg.pow_const 2))
        (hX i)]
  simp_rw [hi]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  rw [show (n : ℝ) * (1 / n) = 1 by field_simp, ENNReal.ofReal_one, one_mul]

theorem app_sample_rate : Claims.app_sample_rate := by
  intro H _ _ _ _ _ _ e P μ F M FK Ω _ Pr _ Kn X Fhat Fm μgrid L α he hsp hL hP1 hμM hF hmap hcm hFK hpush
    hcmK hKn hX hlaw hm1 hm2 hα0 hα1 hgrid hgrid0
  -- the sieve error
  set s : (n : ℕ) → H → ℝ := fun n x => ‖embed e (Kn n) (FK (Kn n) (truncK e (Kn n) x)) - F x‖ with hs
  have hsm : ∀ n, Measurable (s n) := fun n =>
    ((((StatFormal.OTFD.WaveL1.continuous_embed e (Kn n)).measurable.comp
      ((hFK (Kn n)).comp (StatFormal.OTFD.WaveL1.continuous_truncK e (Kn n)).measurable)).sub hF)).norm
  -- three-term decomposition
  have hdec : ∀ n, rmsE Pr (fun ω i => ‖embed e (Kn n) (Fhat n ω i) - F (X n ω i)‖) ≤
      rmsE Pr (fun ω i => ‖Fhat n ω i - Fm n ω i‖) +
        (rmsE Pr (fun ω i => ‖Fm n ω i - FK (Kn n) (truncK e (Kn n) (X n ω i))‖) +
          (∫⁻ x, ENNReal.ofReal (s n x ^ 2) ∂(P : Measure H)) ^ (1 / 2 : ℝ)) := by
    intro n
    have h := StatFormal.OTFD.Wave16b.rate_decomp H (Kn n) n Ω Pr (embedLI he (Kn n)) (Fhat n) (Fm n)
      (fun ω i => FK (Kn n) (truncK e (Kn n) (X n ω i))) (fun ω i => F (X n ω i)) (hm1 n) (hm2 n)
      (fun i => (hsm n).comp (hX n i))
    simp only [embedLI_apply] at h
    refine h.trans ?_
    rw [add_assoc]
    gcongr
    exact rmsE_iid_le Pr (X n) (P : Measure H) (s n) (hsm n) (fun x => norm_nonneg _) (hX n) (hlaw n)
  -- the sieve term tends to zero
  have hsieve := StatFormal.OTFD.WaveL3.sieve_strong_limit_uncond H e P μ F M FK he hsp hL hP1 hμM hF hmap hcm
    hFK hpush hcmK
  have hs0 : Tendsto (fun n => (∫⁻ x, ENNReal.ofReal (s n x ^ 2) ∂(P : Measure H)) ^ (1 / 2 : ℝ)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (s n x ^ 2) ∂(P : Measure H)) atTop (𝓝 0) := by
      have := hsieve.comp hKn
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, hs]
      refine lintegral_congr fun x => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    have h2 := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    exact h2.comp h1
  have hgs : Tendsto (fun n => rmsE Pr (fun ω i => ‖Fm n ω i - FK (Kn n) (truncK e (Kn n) (X n ω i))‖) +
      (∫⁻ x, ENNReal.ofReal (s n x ^ 2) ∂(P : Measure H)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have hg : Tendsto (fun n => rmsE Pr (fun ω i => ‖Fm n ω i - FK (Kn n) (truncK e (Kn n) (X n ω i))‖))
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgrid0 (fun _ => bot_le) hgrid
    simpa using hg.add hs0
  constructor
  · calc limsup (fun n => rmsE Pr (fun ω i => ‖embed e (Kn n) (Fhat n ω i) - F (X n ω i)‖)) atTop
        ≤ limsup ((fun n => rmsE Pr (fun ω i => ‖Fhat n ω i - Fm n ω i‖)) +
            fun n => rmsE Pr (fun ω i => ‖Fm n ω i - FK (Kn n) (truncK e (Kn n) (X n ω i))‖) +
              (∫⁻ x, ENNReal.ofReal (s n x ^ 2) ∂(P : Measure H)) ^ (1 / 2 : ℝ)) atTop :=
          limsup_le_limsup (Eventually.of_forall hdec)
      _ = _ := ENNReal.limsup_add_of_right_tendsto_zero hgs _
  · intro hemp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => bot_le) hdec
    simpa using hemp.add hgs

end StatFormal.Wave24f
