import StatFormal.Archive.Wave20a.Statements
import StatFormal.Archive.RobustEquality.SemidualStrong.Proofs
import StatFormal.Archive.RobustEquality.Semidual.Proofs
import StatFormal.Lib.SemiDiscrete.Dual

/-!
# Route — JASA `lem:cert-coarse` (untrusted)

Dual proof (the paper's proof is primal gluing). With `f*` a maximiser of `J_μ` (certified strong duality),
`OT_ε(μ,P) = J_μ(f*)`. Put `h_z = Σ_{i∈I_z} (a_i/w_z) f*_i` and `f'_z = h_z − v_z`.
* bias–variance: `Σ_{i∈I_z} (a_i/w_z) |x_i − y|² = |x̄_z − y|² + v_z`;
* Jensen (convexity of `exp`) in each cluster: `Σ_{i∈I_z} a_i e^{(f_i − c_i(y))/ε} ≥ w_z e^{(f'_z − c̄_z(y))/ε}`,
  so `g_{f*}(y) ≤ ḡ_{f'}(y)` for the coarse soft-min; and `Σ a_i f*_i = Σ w_z f'_z + D_r`;
* hence `J_μ(f*) ≤ J̄(f') + D_r ≤ OT_ε(μ̄_r, P) + D_r` (certified weak duality for the coarse problem).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave20a

open StatFormal.RobustEquality StatFormal.RobustEquality.Semidual StatFormal.RobustEquality.SemidualStrong

section CoarseAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k r : ℕ}

lemma clW_pos {σ : Fin k → Fin r} {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) (hs : Function.Surjective σ)
    (z : Fin r) : 0 < clW σ a z := by
  obtain ⟨i, hi⟩ := hs z
  exact Finset.sum_pos (fun j _ => ha j) ⟨i, by simp [hi]⟩

lemma clW_sum (σ : Fin k → Fin r) (a : Fin k → ℝ) : ∑ z, clW σ a z = ∑ i, a i :=
  Finset.sum_fiberwise _ σ a

/-- bias–variance in a cluster. -/
lemma cl_biasvar {σ : Fin k → Fin r} {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) (hs : Function.Surjective σ)
    (x : Fin k → E) (z : Fin r) (y : E) :
    ∑ i ∈ (Finset.univ.filter (fun i => σ i = z)), (a i / clW σ a z) * ‖x i - y‖ ^ 2 = ‖clBar σ a x z - y‖ ^ 2 + clVar σ a x z := by
  set w := clW σ a z
  have hw : 0 < w := clW_pos ha hs z
  set xb := clBar σ a x z
  have hsum0 : ∑ i ∈ (Finset.univ.filter (fun i => σ i = z)), a i • (x i - xb) = 0 := by
    simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
    have : ∑ i ∈ (Finset.univ.filter (fun i => σ i = z)), a i • x i = w • xb := by
      simp only [xb, clBar, smul_smul]; rw [mul_inv_cancel₀ hw.ne', one_smul]
    rw [this]; simp [w, clW]
  have hexp : ∀ i, ‖x i - y‖ ^ 2 = ‖x i - xb‖ ^ 2 + 2 * ⟪x i - xb, xb - y⟫ + ‖xb - y‖ ^ 2 := by
    intro i
    have : x i - y = (x i - xb) + (xb - y) := by abel
    rw [this, norm_add_sq_real]
  have hcross : ∑ i ∈ (Finset.univ.filter (fun i => σ i = z)), a i * ⟪x i - xb, xb - y⟫ = 0 := by
    have := congrArg (fun v => ⟪v, xb - y⟫) hsum0
    simp only [sum_inner, inner_smul_left, RCLike.conj_to_real, inner_zero_left] at this
    exact this
  have hW : ∑ i ∈ (Finset.univ.filter (fun i => σ i = z)), a i = w := rfl
  have hterm : ∀ i, (a i / w) * ‖x i - y‖ ^ 2 = w⁻¹ * (a i * ‖x i - xb‖ ^ 2) +
      2 * w⁻¹ * (a i * ⟪x i - xb, xb - y⟫) + (w⁻¹ * ‖xb - y‖ ^ 2) * a i := fun i => by
    rw [hexp i]; ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hcross, hW]
  rw [clVar, show clW σ a z = w from rfl]
  field_simp
  ring

end CoarseAux

theorem cert_coarse : Claims.cert_coarse := by
  intro K _ d k r φ x a σ ε P _ hε ha hsum hs hφ ⟨R, hR⟩
  set c : Fin k → K → ℝ := fun i y => ‖x i - φ y‖ ^ 2 with hc
  set w := clW σ a with hwdef
  set cr : Fin r → K → ℝ := fun z y => ‖clBar σ a x z - φ y‖ ^ 2 with hcr
  have hwpos : ∀ z, 0 < w z := clW_pos ha hs
  have hwsum : ∑ z, w z = 1 := by rw [hwdef, clW_sum, hsum]
  -- bounds
  have hbd : ∀ (p : EuclideanSpace ℝ (Fin d)) (y : K), |‖p - φ y‖ ^ 2| ≤ (‖p‖ + R) ^ 2 := by
    intro p y
    rw [abs_of_nonneg (sq_nonneg _)]
    have h1 : ‖p - φ y‖ ≤ ‖p‖ + R := (norm_sub_le _ _).trans (by linarith [hR y])
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  set Bx := ∑ i, (‖x i‖ + R) ^ 2
  set Bb := ∑ z, (‖clBar σ a x z‖ + R) ^ 2
  have hSa : Setting ε a c := by
    refine ⟨hε, ha, hsum, fun i => ?_, Bx, fun i y => ?_⟩
    · exact (continuous_const.sub continuous_id).norm.pow 2 |>.measurable.comp hφ
    · exact (hbd (x i) y).trans (Finset.single_le_sum (f := fun i => (‖x i‖ + R) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  have hSw : Setting ε w cr := by
    refine ⟨hε, hwpos, hwsum, fun z => ?_, Bb, fun z y => ?_⟩
    · exact (continuous_const.sub continuous_id).norm.pow 2 |>.measurable.comp hφ
    · exact (hbd (clBar σ a x z) y).trans (Finset.single_le_sum
        (f := fun z => (‖clBar σ a x z‖ + R) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ z))
  -- strong duality for μ
  obtain ⟨fs, -, hOT, -⟩ := StatFormal.RobustEquality.SemidualStrong.strong_duality K k ε a c P hSa
  set h : Fin r → ℝ := fun z => ∑ i ∈ Finset.univ.filter (fun i => σ i = z), (a i / w z) * fs i
  set f' : Fin r → ℝ := fun z => h z - clVar σ a x z
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp at hsum
    · exact h0
  -- pointwise soft-min comparison
  have hg : ∀ y, gsoft ε a fs c y ≤ gsoft ε w f' cr y := by
    intro y
    have hcl : ∀ z, w z * Real.exp ((f' z - cr z y) / ε) ≤
        ∑ i ∈ Finset.univ.filter (fun i => σ i = z), a i * Real.exp ((fs i - c i y) / ε) := by
      intro z
      have hJ := convexOn_exp.map_sum_le (t := Finset.univ.filter (fun i => σ i = z))
        (w := fun i => a i / w z) (p := fun i => (fs i - c i y) / ε)
        (fun i _ => div_nonneg (ha i).le (hwpos z).le)
        (by rw [← Finset.sum_div]; exact div_self (hwpos z).ne') (fun i _ => mem_univ _)
      simp only [smul_eq_mul] at hJ
      have hlin : ∑ i ∈ Finset.univ.filter (fun i => σ i = z), a i / w z * ((fs i - c i y) / ε) =
          (f' z - cr z y) / ε := by
        have hb := cl_biasvar ha hs x z (φ y)
        rw [← hwdef] at hb
        have e1 : f' z - cr z y = ∑ i ∈ Finset.univ.filter (fun i => σ i = z), (a i / w z) * (fs i - c i y) := by
          show h z - clVar σ a x z - ‖clBar σ a x z - φ y‖ ^ 2 = _
          rw [show h z - clVar σ a x z - ‖clBar σ a x z - φ y‖ ^ 2 =
            h z - (‖clBar σ a x z - φ y‖ ^ 2 + clVar σ a x z) by ring, ← hb]
          simp only [h, c, mul_sub, Finset.sum_sub_distrib]
        rw [e1, Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hlin] at hJ
      have : w z * Real.exp ((f' z - cr z y) / ε) ≤
          w z * ∑ i ∈ Finset.univ.filter (fun i => σ i = z), a i / w z * Real.exp ((fs i - c i y) / ε) :=
        mul_le_mul_of_nonneg_left hJ (hwpos z).le
      refine this.trans_eq ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp [(hwpos z).ne']
    have hpos : 0 < ∑ z, w z * Real.exp ((f' z - cr z y) / ε) :=
      Finset.sum_pos (fun z _ => mul_pos (hwpos z) (Real.exp_pos _)) ⟨σ ⟨0, hk⟩, Finset.mem_univ _⟩
    have hle : ∑ z, w z * Real.exp ((f' z - cr z y) / ε) ≤ ∑ i, a i * Real.exp ((fs i - c i y) / ε) := by
      rw [← Finset.sum_fiberwise Finset.univ σ (fun i => a i * Real.exp ((fs i - c i y) / ε))]
      exact Finset.sum_le_sum fun z _ => hcl z
    unfold gsoft
    have := Real.log_le_log hpos hle
    nlinarith
  -- linear part
  have hlinsum : ∑ i, a i * fs i = ∑ z, w z * f' z + clD σ a x := by
    rw [← Finset.sum_fiberwise Finset.univ σ (fun i => a i * fs i), clD, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [f', h, mul_sub, Finset.mul_sum]
    have : ∀ i, w z * (a i / w z * fs i) = a i * fs i := fun i => by
      field_simp [(hwpos z).ne']
    simp_rw [this]; ring
  -- integrability
  have hBa : ∀ i y, |c i y| ≤ Bx := hSa.2.2.2.2.choose_spec |> fun _ => fun i y =>
    (hbd (x i) y).trans (Finset.single_le_sum (f := fun i => (‖x i‖ + R) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  have hBw : ∀ z y, |cr z y| ≤ Bb := fun z y =>
    (hbd (clBar σ a x z) y).trans (Finset.single_le_sum
        (f := fun z => (‖clBar σ a x z‖ + R) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ z))
  have SDa : StatFormal.Foundations.SemiDiscrete.SDHyp ε a c Bx :=
    ⟨hε, ha, hsum, hSa.2.2.2.1, hBa⟩
  have SDw : StatFormal.Foundations.SemiDiscrete.SDHyp ε w cr Bb :=
    ⟨hε, hwpos, hwsum, hSw.2.2.2.1, hBw⟩
  have hJ : Jdual ε a c P fs ≤ Jdual ε w cr P f' + clD σ a x := by
    unfold Jdual
    rw [hlinsum]
    have := integral_mono (SDa.integrable_gsoft (Q := P) fs) (SDw.integrable_gsoft (Q := P) f') hg
    linarith
  -- weak duality for the coarse problem
  have hweak : (Jdual ε w cr P f' : EReal) ≤ OTdisc ε w cr P := by
    refine le_sInf ?_
    rintro v ⟨γ, hγ, h1, h2, rfl⟩
    have := hγ
    exact StatFormal.RobustEquality.Semidual.semidual_weak K r w f' cr P γ ε hε hwpos hwsum
      hSw.2.2.2.1 ⟨Bb, hBw⟩ h1 h2
  rw [hOT]
  calc (Jdual ε a c P fs : EReal) ≤ ((Jdual ε w cr P f' + clD σ a x : ℝ) : EReal) := by
        exact_mod_cast hJ
    _ = (Jdual ε w cr P f' : EReal) + ((clD σ a x : ℝ) : EReal) := by push_cast; rfl
    _ ≤ OTdisc ε w cr P + ((clD σ a x : ℝ) : EReal) := by gcongr

end StatFormal.Wave20a
