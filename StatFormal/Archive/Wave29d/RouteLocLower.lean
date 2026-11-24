import StatFormal.Archive.Wave29d.Statements
import StatFormal.Archive.RobustEquality.SemidualStrong.Proofs
import StatFormal.Archive.RobustEquality.Semidual.Proofs
import StatFormal.Archive.RobustEquality.Lower.Proofs
import StatFormal.Lib.Distances.Product
import TauCeti.InformationTheory.KullbackLeibler.Finite

/-!
# Route — robust equality JASA `thm:loc-lower` (i), (ii) (untrusted)

(i) For each `z`, the alternative `P₁ = (1 − η)P₀ + ηδ_z` dominates `(1 − η)P₀`, so `P₁^m ≥ ½ P₀^m` for
`(1 − η)^m = ½`, and the event `{OT_ε(μ, P₁) ≤ ρ̂}` keeps `P₀^m`-probability `≥ 1 − 2δ ≥ ½ − δ`; the frozen subgradient
inequality gives `OT_ε(μ, P₁) ≥ OT_ε(μ, P₀) + η(g̃₀(z) − E_{P₀} g̃₀)`. Continuity from above over a maximising
sequence of `z` replaces `g̃₀(z)` by `sup_K g̃₀`. The expansion is `|e^x − 1 − x| ≤ x²` for `|x| ≤ 1`.

(ii) `OT_ε(μ, P_t) ≥ J_{P_t}(4R², 0) ≥ 4R² t` (weak duality), `OT_ε(μ, P₀) = max J ≤ ε log 2`; Pinsker with
tensorisation, `KL(P₀ ‖ P_t) ≤ KL(B₀ ‖ B_t) = −½ log(1 − 4t²) ≤ 4t²` through the two-point map; the variance from the
first-order condition (`u₀² = u₁²`); the envelope by direct evaluation.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology InformationTheory
open scoped ENNReal

namespace StatFormal.Wave29d

open StatFormal.RobustEquality.Semidual (gsoft muDisc)
open StatFormal.RobustEquality.SemidualStrong (OTdisc Jdual Setting)

namespace LocLower

variable {K : Type} [MeasurableSpace K] {k : ℕ}

/-- `g_f` is bounded under `Setting`. -/
lemma gsoft_abs_le {ε : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ} (hs : Setting ε a c) (f : Fin k → ℝ) :
    ∃ C, ∀ y, |gsoft ε a f c y| ≤ C := by
  obtain ⟨hε, ha, hsum, -, B, hB⟩ := hs
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hsum
    · exact h
  set F := ∑ i, |f i|
  refine ⟨ε * ((F + B) / ε), fun y => ?_⟩
  have hu : ∀ i, |(f i - c i y) / ε| ≤ (F + B) / ε := by
    intro i
    rw [abs_div, abs_of_pos hε]
    apply div_le_div_of_nonneg_right _ hε.le
    have h1 : |f i| ≤ F := Finset.single_le_sum (f := fun i => |f i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    calc |f i - c i y| ≤ |f i| + |c i y| := abs_sub _ _
      _ ≤ F + B := add_le_add h1 (hB i y)
  have := StatFormal.RobustEquality.Semidual.abs_log_S_le hk a ha hsum (fun i => (f i - c i y) / ε) _ hu
  unfold gsoft
  rw [abs_mul, abs_neg, abs_of_pos hε]
  exact mul_le_mul_of_nonneg_left this hε.le

lemma gsoft_integrable {ε : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ} (hs : Setting ε a c) (f : Fin k → ℝ)
    (Q : Measure K) [IsFiniteMeasure Q] : Integrable (gsoft ε a f c) Q := by
  obtain ⟨C, hC⟩ := gsoft_abs_le hs f
  exact Integrable.of_bound
    (StatFormal.RobustEquality.Semidual.measurable_gsoft ε a f c hs.2.2.2.1).aestronglyMeasurable C
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC y)

/-- `OT_ε(μ, Q) = J_Q(f*)` for any maximiser `f*`. -/
lemma OT_eq_J {ε : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ} (hs : Setting ε a c) (Q : Measure K)
    [IsProbabilityMeasure Q] {fs : Fin k → ℝ} (hmax : ∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs) :
    OTdisc ε a c Q = (Jdual ε a c Q fs : EReal) := by
  obtain ⟨fs', hmax', hval, -⟩ := StatFormal.RobustEquality.SemidualStrong.strong_duality _ k ε a c Q hs
  rw [hval, le_antisymm (hmax fs') (hmax' fs)]

/-- `J_Q(f) ≤ OT_ε(μ, Q)` for every `f` (weak duality, as an `EReal` inequality against the infimum). -/
lemma J_le_OT {ε : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ} (hs : Setting ε a c) (Q : Measure K)
    [IsProbabilityMeasure Q] (f : Fin k → ℝ) : (Jdual ε a c Q f : EReal) ≤ OTdisc ε a c Q := by
  obtain ⟨fs, hmax, hval, -⟩ := StatFormal.RobustEquality.SemidualStrong.strong_duality _ k ε a c Q hs
  rw [hval, EReal.coe_le_coe_iff]
  exact hmax f

/-- The two-measure domination `P₁ ≥ (1−η) P₀` lifts to `P₁^m(A) ≥ (1−η)^m P₀^m(A)`. -/
lemma real_pi_ge {m : ℕ} {P₀ P₁ : Measure K} [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] {c' : ℝ}
    (hc' : 0 ≤ c') (h : ENNReal.ofReal c' • P₀ ≤ P₁) (A : Set (Fin m → K)) :
    c' ^ m * (Measure.pi fun _ : Fin m => P₀).real A ≤ (Measure.pi fun _ : Fin m => P₁).real A := by
  have hle := StatFormal.RobustEquality.Lower.pi_smul_le h m
  have h1 := Measure.le_iff'.1 hle A
  rw [Measure.smul_apply, smul_eq_mul] at h1
  have h2 := ENNReal.toReal_mono (measure_ne_top _ _) h1
  rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hc'] at h2

end LocLower

open LocLower in
theorem loclower_unseen : Claims.loclower_unseen := by
  intro K _ k m ε δ a c ρ P₀ _ fs hset hm hρ hvalid hmax
  set g := gsoft ε a fs c with hg
  obtain ⟨C, hC⟩ := gsoft_abs_le hset fs
  have hgm : Measurable g := StatFormal.RobustEquality.Semidual.measurable_gsoft ε a fs c hset.2.2.2.1
  have hgi : Integrable g P₀ := gsoft_integrable hset fs P₀
  have hbdd : BddAbove (range g) := ⟨C, by rintro _ ⟨y, rfl⟩; exact (abs_le.1 (hC y)).2⟩
  haveI : Nonempty K := nonempty_of_isProbabilityMeasure P₀
  set S := ⨆ y, g y with hS
  set Eg := ∫ y, g y ∂P₀ with hEg
  have hGdef : canonGap ε a fs c P₀ = S - Eg := rfl
  have hEgS : Eg ≤ S := by
    have : ∫ y, g y ∂P₀ ≤ ∫ _y, S ∂P₀ := integral_mono hgi (integrable_const _) fun y => le_ciSup hbdd y
    simpa using this
  -- the strength `η = 1 − 2^{−1/m}`
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set q := (2 : ℝ) ^ (-(1 : ℝ) / m) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos two_pos _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by
    rw [neg_div]; exact neg_neg_of_pos (by positivity))
  have hqm : q ^ m = 1 / 2 := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul two_pos.le]
    rw [show -(1 : ℝ) / m * (m : ℝ) = -1 by field_simp]
    rw [Real.rpow_neg_one]; norm_num
  set η := 1 - q with hη
  -- OT at `P₀` is the real number `J₀`
  have hOT0 := OT_eq_J hset P₀ hmax
  set J₀ := Jdual ε a c P₀ fs
  -- the per-`z` bound
  have hz : ∀ z : K, 1 / 2 - δ ≤ (Measure.pi fun _ : Fin m => P₀).real
      {y | J₀ + η * (g z - Eg) ≤ ρ y} := by
    intro z
    set P₁ : Measure K := ENNReal.ofReal (1 - η) • P₀ + ENNReal.ofReal η • Measure.dirac z with hP₁
    have hP₁p : IsProbabilityMeasure P₁ := by
      constructor
      simp only [hP₁, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      simp
    have hsub := StatFormal.RobustEquality.SemidualStrong.subgradient K k ε a c P₀ P₁ fs hset hmax
    have hint : ∫ y, g y ∂P₁ = (1 - η) * Eg + η * g z := by
      rw [hP₁, integral_add_measure (hgi.smul_measure ENNReal.ofReal_ne_top)
        ((gsoft_integrable hset fs (Measure.dirac z)).smul_measure ENNReal.ofReal_ne_top),
        integral_smul_measure, integral_smul_measure, integral_dirac' _ _ hgm.stronglyMeasurable,
        ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]
    have hOT1 : ((J₀ + η * (g z - Eg) : ℝ) : EReal) ≤ OTdisc ε a c P₁ := by
      have : ((J₀ + η * (g z - Eg) : ℝ) : EReal) = OTdisc ε a c P₀ + ((∫ y, g y ∂P₁ - ∫ y, g y ∂P₀ : ℝ) : EReal) := by
        rw [hOT0, ← EReal.coe_add, hint]; congr 1; simp only [hEg]; ring
      rw [this]; exact hsub
    -- the event `A = {OT(P₁) ≤ ρ̂}`
    set A : Set (Fin m → K) := {y | OTdisc ε a c P₁ ≤ (ρ y : EReal)} with hA
    have hAsub : A ⊆ {y | J₀ + η * (g z - Eg) ≤ ρ y} := fun y hy => by
      have := hOT1.trans hy
      exact EReal.coe_le_coe_iff.1 this
    have hA1 : 1 - δ ≤ (Measure.pi fun _ : Fin m => P₁).real A := hvalid P₁ hP₁p
    have hdom : ENNReal.ofReal q • P₀ ≤ P₁ := by
      rw [hP₁, show q = 1 - η by rw [hη]; ring]; exact Measure.le_add_right le_rfl
    have hAm : MeasurableSet A := by
      have : A = (fun y => (ρ y : EReal)) ⁻¹' Ici (OTdisc ε a c P₁) := rfl
      rw [this]; exact (measurable_coe_real_ereal.comp hρ) measurableSet_Ici
    have hc := real_pi_ge (m := m) hq0.le hdom Aᶜ
    rw [hqm, measureReal_compl hAm, measureReal_compl hAm, probReal_univ, probReal_univ] at hc
    have hmono := measureReal_mono (μ := Measure.pi fun _ : Fin m => P₀) hAsub
    rcases le_or_gt (1 / 2) δ with hδ | hδ
    · exact le_trans (by linarith) measureReal_nonneg
    · linarith
  -- pass to the supremum: continuity from above
  set E : ℕ → Set (Fin m → K) := fun n => {y | J₀ + η * (S - 1 / ((n : ℝ) + 1) - Eg) ≤ ρ y} with hE
  have hη0 : 0 < η := by rw [hη]; linarith
  have hEn : ∀ n, 1 / 2 - δ ≤ (Measure.pi fun _ : Fin m => P₀).real (E n) := by
    intro n
    obtain ⟨z, hz'⟩ := exists_lt_of_lt_ciSup (f := g) (show S - 1 / ((n : ℝ) + 1) < S by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)
    refine (hz z).trans (measureReal_mono fun y hy => ?_)
    simp only [mem_setOf_eq, hE] at hy ⊢
    nlinarith
  have hEm : ∀ n, MeasurableSet (E n) := fun n => measurableSet_le measurable_const hρ
  have hanti : Antitone E := by
    intro n n' hnn' y hy
    simp only [mem_setOf_eq, hE] at hy ⊢
    have : 1 / ((n' : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnn' 1)
    nlinarith
  have hinter : (⋂ n, E n) = {y | J₀ + η * (S - Eg) ≤ ρ y} := by
    ext y
    simp only [mem_iInter, mem_setOf_eq, hE]
    constructor
    · intro h
      by_contra hlt
      push_neg at hlt
      -- `ρ y < J₀ + η (S − Eg)`; choose `n` with `η/(n+1)` below the gap
      have hgap : 0 < J₀ + η * (S - Eg) - ρ y := by linarith
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hgap hη0)
      have h1 := h n
      have : η * (1 / ((n : ℝ) + 1)) < J₀ + η * (S - Eg) - ρ y := by
        rw [lt_div_iff₀ hη0] at hn; linarith
      nlinarith
    · intro h n
      have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
      nlinarith
  have hlim := hanti.measure_iInter (μ := Measure.pi fun _ : Fin m => P₀) (fun n => (hEm n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩
  refine ⟨?_, ?_⟩
  · have hset' : {y | OTdisc ε a c P₀ + (((1 - q) * canonGap ε a fs c P₀ : ℝ) : EReal) ≤ (ρ y : EReal)} =
        ⋂ n, E n := by
      rw [hinter]; ext y
      simp only [mem_setOf_eq, hOT0, ← EReal.coe_add, EReal.coe_le_coe_iff, hGdef, hη]
    rw [hset', measureReal_def, hlim]
    rcases le_or_gt (1 / 2) δ with hδ | hδ
    · exact le_trans (by linarith) ENNReal.toReal_nonneg
    · rw [← ENNReal.ofReal_le_iff_le_toReal (by
        exact ne_top_of_le_ne_top (measure_ne_top (Measure.pi fun _ : Fin m => P₀) (E 0)) (iInf_le _ 0))]
      refine le_iInf fun n => ?_
      rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top (Measure.pi fun _ : Fin m => P₀) _)]
      exact hEn n
  · -- `1 − 2^{−1/m} ≥ x − x²`, `x = log 2/m`
    have hG0 : 0 ≤ canonGap ε a fs c P₀ := by rw [hGdef]; linarith
    set x := Real.log 2 / m with hx
    have hx0 : 0 ≤ x := div_nonneg (Real.log_nonneg one_le_two) hmR.le
    have hx1 : x ≤ 1 := by
      rw [hx, div_le_one hmR]
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      have : (1 : ℝ) ≤ m := Nat.one_le_cast.2 hm
      linarith
    have hqx : q = Real.exp (-x) := by
      rw [hq, Real.rpow_def_of_pos two_pos, hx]; congr 1; ring
    have hexp := Real.abs_exp_sub_one_sub_id_le (x := -x) (by rw [abs_neg, abs_of_nonneg hx0]; exact hx1)
    have hq' : x - x ^ 2 ≤ 1 - q := by
      rw [hqx]; have := (abs_le.1 hexp).2; nlinarith
    have : Real.log 2 * canonGap ε a fs c P₀ / m - Real.log 2 ^ 2 * canonGap ε a fs c P₀ / (m : ℝ) ^ 2 =
        (x - x ^ 2) * canonGap ε a fs c P₀ := by
      rw [hx]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hq' hG0

end StatFormal.Wave29d
