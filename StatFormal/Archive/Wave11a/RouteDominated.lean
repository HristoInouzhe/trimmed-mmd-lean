import StatFormal.Archive.Wave11a.Statements
import StatFormal.Lib.Tax.Tax
import StatFormal.Archive.RobustEquality.Gibbs
import StatFormal.Archive.RobustEquality.Tax.Proofs

/-!
# Wave 11a route: robust equality JASA `cor:dominated` (defensive mixtures)

Untrusted proof file. With `ν = (1−κ)ν₀ + κm`:
* upper bound: for `m = Q`, `κQ ≤ ν` gives `dQ/dν ≤ 1/κ`, so `KL(Q‖ν) ≤ log(1/κ)`;
* lower bound: for `Q` carried by a finite set `A` and atomless `ν₀`, `ν(A) = κ m(A) ≤ κ`; the Gibbs variational
  principle with `g = −u 1_{Aᶜ}` gives `KL(Q‖ν) ≥ −log(κ + e^{−u} ν(K))`, and `u → ∞`;
* (i) from `GhostAt` with `a_𝒩 = log(1/κ)`; (ii) from `lem:tax` and the upper bound; (iii) from
  `(1−κ)ν₀ + κm ≥ κm`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal

namespace StatFormal.Wave11a

open StatFormal.RobustEquality StatFormal.RobustEquality.Tax StatFormal.RobustEquality.SemidualStrong
  StatFormal.RobustEquality.Certificate

variable {K : Type} [MeasurableSpace K]

/-- The mixture `(1−κ)ν₀ + κm`. -/
abbrev mix (ν₀ : Measure K) (κ : ℝ) (m : Measure K) : Measure K :=
  ENNReal.ofReal (1 - κ) • ν₀ + ENNReal.ofReal κ • m

instance mix_finite (ν₀ : Measure K) [IsFiniteMeasure ν₀] (κ : ℝ) (m : Measure K) [IsFiniteMeasure m] :
    IsFiniteMeasure (mix ν₀ κ m) := by
  refine ⟨?_⟩
  simp only [mix, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

lemma mix_ge (ν₀ : Measure K) (κ : ℝ) (m : Measure K) : ENNReal.ofReal κ • m ≤ mix ν₀ κ m := by
  intro s
  simp only [mix, Measure.add_apply, Measure.smul_apply]
  exact le_add_self

lemma mix_univ_ne_zero (ν₀ : Measure K) {κ : ℝ} (hκ : 0 < κ) (m : Measure K) [IsProbabilityMeasure m] :
    mix ν₀ κ m univ ≠ 0 := by
  intro h
  have := (mix_ge ν₀ κ m) univ
  rw [h, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, nonpos_iff_eq_zero,
    ENNReal.ofReal_eq_zero] at this
  linarith

lemma mix_mem (ν₀ : Measure K) (κ : ℝ) (m : Measure K) [IsProbabilityMeasure m] :
    mix ν₀ κ m ∈ defMix ν₀ κ := ⟨m, inferInstance, rfl⟩

/-- `|t log t| ≤ 1 + M²` on `[0, M]`. -/
lemma abs_mul_log_le {t M : ℝ} (ht : 0 ≤ t) (htM : t ≤ M) : |t * Real.log t| ≤ 1 + M ^ 2 := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h; simp; positivity
  by_cases h1 : t ≤ 1
  · have := Real.abs_log_mul_self_lt t h h1
    rw [mul_comm]; nlinarith [sq_nonneg M]
  · push Not at h1
    have hl : 0 ≤ Real.log t := Real.log_nonneg h1.le
    have hl2 : Real.log t ≤ t := (Real.log_le_sub_one_of_pos h).trans (by linarith)
    rw [abs_of_nonneg (mul_nonneg ht hl)]
    nlinarith

/-- **Upper bound**: `KL(Q‖(1−κ)ν₀ + κQ) ≤ log(1/κ)`. -/
lemma klRef_mix_self_le (ν₀ : Measure K) [IsFiniteMeasure ν₀] {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (Q : Measure K) [IsProbabilityMeasure Q] :
    klRef Q (mix ν₀ κ Q) ≤ ((Real.log (1 / κ) : ℝ) : EReal) := by
  set ν := mix ν₀ κ Q with hν
  have hle : ENNReal.ofReal κ • Q ≤ ν := mix_ge ν₀ κ Q
  have hk0 : ENNReal.ofReal κ ≠ 0 := by simpa using hκ
  have hac : Q ≪ ν := by
    intro s hs
    have := hle s
    rw [hs, Measure.smul_apply, smul_eq_mul, nonpos_iff_eq_zero, mul_eq_zero] at this
    exact this.resolve_left hk0
  -- `κ · dQ/dν ≤ 1`
  have hrn : ∀ᵐ x ∂ν, (Q.rnDeriv ν x).toReal ≤ 1 / κ := by
    have h1 := Measure.rnDeriv_le_one_of_le hle
    have h2 := Measure.rnDeriv_smul_left' Q ν κ.toNNReal
    have hk : (κ.toNNReal : ℝ≥0∞) = ENNReal.ofReal κ := rfl
    filter_upwards [h1, h2] with x hx1 hx2
    rw [show ((κ.toNNReal) • Q) = ENNReal.ofReal κ • Q by
      rw [← hk]; rfl] at hx2
    rw [hx2] at hx1
    simp only [Pi.smul_apply, Pi.one_apply] at hx1
    have hfin : Q.rnDeriv ν x ≠ ⊤ := by
      intro ht
      rw [ht] at hx1
      simp [ENNReal.smul_top, hk0, not_le.2 hκ] at hx1
    have : κ * (Q.rnDeriv ν x).toReal ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top hx1
      rw [ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul] at this
      simpa [Real.toNNReal_of_nonneg hκ.le, hκ.le] using this
    rw [le_div_iff₀ hκ]; linarith
  have hrnQ : ∀ᵐ x ∂Q, (Q.rnDeriv ν x).toReal ≤ 1 / κ := hac.ae_le hrn
  have hint : Integrable (llr Q ν) Q := by
    rw [← integrable_rnDeriv_mul_log_iff hac]
    refine Integrable.of_bound (C := 1 + (1 / κ) ^ 2) ?_ ?_
    · exact ((Measure.measurable_rnDeriv Q ν).ennreal_toReal.mul
        (Measure.measurable_rnDeriv Q ν).ennreal_toReal.log).aestronglyMeasurable
    · filter_upwards [hrn] with x hx
      rw [Real.norm_eq_abs]
      exact abs_mul_log_le ENNReal.toReal_nonneg hx
  have hL : 0 ≤ Real.log (1 / κ) := Real.log_nonneg (by rw [le_div_iff₀ hκ]; linarith)
  have hbound : ∀ᵐ x ∂Q, llr Q ν x ≤ Real.log (1 / κ) := by
    filter_upwards [hrnQ] with x hx
    simp only [llr_def]
    rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := Q.rnDeriv ν x)) with h0 | hpos
    · rw [← h0, Real.log_zero]; exact hL
    · exact Real.log_le_log hpos hx
  unfold klRef
  rw [if_pos ⟨hac, hint⟩, EReal.coe_le_coe_iff]
  calc ∫ x, llr Q ν x ∂Q ≤ ∫ _x, Real.log (1 / κ) ∂Q := integral_mono_ae hint (integrable_const _) hbound
    _ = Real.log (1 / κ) := by simp

/-- **Lower bound**: if `Q` is carried by a measurable `A` with `ν(A) ≤ κ`, then `KL(Q‖ν) ≥ log(1/κ)`. -/
lemma klRef_ge_of_carrier (ν : Measure K) [IsFiniteMeasure ν] (hν : ν univ ≠ 0) {κ : ℝ} (hκ : 0 < κ)
    (Q : Measure K) [IsProbabilityMeasure Q] {A : Set K} (hA : MeasurableSet A) (hQA : Q Aᶜ = 0)
    (hνA : ν A ≤ ENNReal.ofReal κ) :
    ((Real.log (1 / κ) : ℝ) : EReal) ≤ klRef Q ν := by
  set C := ν.real univ with hC
  have hC0 : 0 ≤ C := measureReal_nonneg
  have hνAr : ν.real A ≤ κ := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hκ.le hνA
  -- the Gibbs bound at every `u ≥ 0`
  have key : ∀ u : ℝ, 0 ≤ u → ((-Real.log (κ + Real.exp (-u) * C) : ℝ) : EReal) ≤ klRef Q ν := by
    intro u hu
    set g : K → ℝ := Aᶜ.indicator (fun _ => -u) with hg
    have hgm : Measurable g := measurable_const.indicator hA.compl
    have hgb : ∀ x, |g x| ≤ u := fun x => by
      by_cases hx : x ∈ Aᶜ
      · simp [hg, hx, abs_of_nonneg hu]
      · simp [hg, hx, hu]
    obtain ⟨⟨-, hub⟩, -⟩ := StatFormal.RobustEquality.lem_gibbs K ν hν g hgm ⟨u, hgb⟩
    have hmem := hub ⟨Q, inferInstance, rfl⟩
    have hg0 : ∫ x, g x ∂Q = 0 := by
      refine integral_eq_zero_of_ae ?_
      have : ∀ᵐ x ∂Q, x ∉ Aᶜ := measure_eq_zero_iff_ae_notMem.1 hQA
      filter_upwards [this] with x hx
      simp [hg, hx]
    have hexpint : Integrable (fun x => Real.exp (g x)) ν :=
      Integrable.of_bound (C := Real.exp u) (hgm.exp.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.2 ((le_abs_self _).trans (hgb x)))
    have hZpos : 0 < ∫ x, Real.exp (g x) ∂ν := by
      have : NeZero ν := ⟨fun h => hν (by simp [h])⟩
      exact integral_exp_pos hexpint
    have hZle : ∫ x, Real.exp (g x) ∂ν ≤ κ + Real.exp (-u) * C := by
      have hpt : ∀ x, Real.exp (g x) ≤ A.indicator 1 x + Real.exp (-u) := fun x => by
        by_cases hx : x ∈ A
        · have : x ∉ Aᶜ := fun h => h hx
          simp [hg, hx, this, (Real.exp_pos (-u)).le]
        · have : x ∈ Aᶜ := hx
          simp [hg, hx, this]
      have hI1 : Integrable (A.indicator (1 : K → ℝ)) ν := (integrable_const (1 : ℝ)).indicator hA
      calc ∫ x, Real.exp (g x) ∂ν ≤ ∫ x, (A.indicator 1 x + Real.exp (-u)) ∂ν :=
            integral_mono hexpint (hI1.add (integrable_const _)) hpt
        _ = ν.real A + Real.exp (-u) * C := by
            rw [integral_add hI1 (integrable_const _),
              integral_indicator_one hA, integral_const, smul_eq_mul, hC, mul_comm]
        _ ≤ κ + Real.exp (-u) * C := by linarith
    have hlog : Real.log (∫ x, Real.exp (g x) ∂ν) ≤ Real.log (κ + Real.exp (-u) * C) :=
      Real.log_le_log hZpos hZle
    rw [hg0, EReal.coe_zero, zero_sub] at hmem
    have h2 : -klRef Q ν ≤ ((Real.log (κ + Real.exp (-u) * C) : ℝ) : EReal) :=
      hmem.trans (EReal.coe_le_coe_iff.2 hlog)
    rw [EReal.neg_le] at h2
    simpa using h2
  -- let `u → ∞`
  by_cases htop : klRef Q ν = ⊤
  · rw [htop]; exact le_top
  have hbot := StatFormal.Foundations.Tax.klRef_ne_bot Q ν
  obtain ⟨k, hk⟩ : ∃ k : ℝ, klRef Q ν = k := ⟨(klRef Q ν).toReal, (EReal.coe_toReal htop hbot).symm⟩
  rw [hk] at key ⊢
  rw [EReal.coe_le_coe_iff]
  have hlim : Filter.Tendsto (fun u : ℝ => -Real.log (κ + Real.exp (-u) * C)) Filter.atTop
      (nhds (-Real.log (κ + 0 * C))) := by
    refine ((tendsto_const_nhds.add (Real.tendsto_exp_neg_atTop_nhds_zero.mul_const C)).log ?_).neg
    simp; exact hκ.ne'
  rw [zero_mul, add_zero, ← Real.log_inv, ← one_div] at hlim
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with u hu
  exact EReal.coe_le_coe_iff.1 (key u hu)

/-- Finite sets are null for atomless `ν₀`. -/
lemma measure_finset_zero [MeasurableSingletonClass K] {ν₀ : Measure K} (hatom : ∀ y, ν₀ {y} = 0)
    (s : Finset K) : ν₀ (↑s : Set K) = 0 := by
  haveI : NullSingletonClass ν₀ := ⟨hatom⟩
  exact s.finite_toSet.measure_zero ν₀

/-- Every member of `𝒩_κ` charges a finitely supported `Q` at least `log(1/κ)`. -/
lemma klRef_mix_ge [MeasurableSingletonClass K] (ν₀ : Measure K) [IsFiniteMeasure ν₀]
    (hatom : ∀ y, ν₀ {y} = 0) {κ : ℝ} (hκ : 0 < κ) (m : Measure K) [IsProbabilityMeasure m]
    (Q : Measure K) [IsProbabilityMeasure Q] (hQ : FinSupp Q) :
    ((Real.log (1 / κ) : ℝ) : EReal) ≤ klRef Q (mix ν₀ κ m) := by
  obtain ⟨s, hs⟩ := hQ
  refine klRef_ge_of_carrier _ (mix_univ_ne_zero ν₀ hκ m) hκ Q s.measurableSet hs ?_
  simp only [mix, Measure.add_apply, Measure.smul_apply, measure_finset_zero hatom s, smul_eq_mul,
    mul_zero, zero_add]
  calc ENNReal.ofReal κ * m ↑s ≤ ENNReal.ofReal κ * 1 := by gcongr; exact prob_le_one
    _ = ENNReal.ofReal κ := mul_one _

theorem dom_tax_le : Claims.dom_tax_le := by
  intro K _ ν₀ _ κ Q _ hκ hκ1
  refine ⟨mix_mem ν₀ κ Q, klRef_mix_self_le ν₀ hκ hκ1 Q, ?_⟩
  exact (iInf₂_le _ (mix_mem ν₀ κ Q)).trans (klRef_mix_self_le ν₀ hκ hκ1 Q)

theorem dom_tax_finite : Claims.dom_tax_finite := by
  intro K _ _ ν₀ _ κ Q _ hκ hκ1 _ hatom hQ
  refine le_antisymm ((iInf₂_le _ (mix_mem ν₀ κ Q)).trans (klRef_mix_self_le ν₀ hκ hκ1 Q)) ?_
  refine le_iInf₂ fun ν hν => ?_
  obtain ⟨m, hm, rfl⟩ := hν
  exact klRef_mix_ge ν₀ hatom hκ m Q hQ

theorem dom_aN : Claims.dom_aN := by
  intro K _ _ _ ν₀ _ κ hκ hκ1 hν₀ hatom
  obtain ⟨y⟩ := ‹Nonempty K›
  have hfin : ∀ Q : Measure K, IsProbabilityMeasure Q → FinSupp Q →
      tax (defMix ν₀ κ) Q = ((Real.log (1 / κ) : ℝ) : EReal) := fun Q hQ hQs =>
    dom_tax_finite K ν₀ κ Q hκ hκ1 hν₀ hatom hQs
  refine le_antisymm ?_ ?_
  · have hd : FinSupp (Measure.dirac y) := ⟨{y}, by simp⟩
    exact (iInf₂_le (Measure.dirac y) ⟨inferInstance, hd⟩).trans_eq (hfin _ inferInstance hd)
  · exact le_iInf₂ fun Q hQ => (hfin Q hQ.1 hQ.2).ge

theorem dom_ball : Claims.dom_ball := by
  intro K _ k ε a c ν₀ _ κ r hs hκ hκ1
  rintro Q ⟨hQ, ν, hν, hW⟩
  haveI := hQ
  haveI : IsProbabilityMeasure ν := hν
  have hiff := EReal.le_sub_iff_add_le (a := OTdisc ε a c Q) (b := ((ε * Real.log (1 / κ) : ℝ) : EReal))
    (c := r) (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))
  rw [StatFormal.RobustEquality.Tax.tax_identity K k ε a c ν Q hs] at hW
  have hkl := StatFormal.Foundations.Tax.klRef_nonneg_of_prob Q ν
  have hεkl : 0 ≤ (ε : EReal) * klRef Q ν := mul_nonneg (EReal.coe_nonneg.2 hs.1.le) hkl
  have hOT : OTdisc ε a c Q ≤ r - ((ε * Real.log (1 / κ) : ℝ) : EReal) :=
    le_trans (le_add_of_nonneg_right hεkl) hW
  refine ⟨hQ, mix ν₀ κ Q, mix_mem ν₀ κ Q, ?_⟩
  rw [StatFormal.RobustEquality.Tax.tax_identity K k ε a c (mix ν₀ κ Q) Q hs]
  have hb : (ε : EReal) * klRef Q (mix ν₀ κ Q) ≤ ((ε * Real.log (1 / κ) : ℝ) : EReal) := by
    rw [EReal.coe_mul]
    exact StatFormal.Foundations.Tax.coe_mul_le_coe_mul hs.1.le (klRef_mix_self_le ν₀ hκ hκ1 Q)
  exact le_trans (add_le_add le_rfl hb) (hiff.1 hOT)

theorem dom_worst : Claims.dom_worst := by
  intro K _ k₀ k₁ ε a₀ c₀ a₁ c₁ ν₀ _ κ r₀ r₁ h hs₀ hs₁ hκ hκ1 _
  unfold worstPair
  refine iSup₂_le fun Q₀ hQ₀ => iSup₂_le fun Q₁ hQ₁ => ?_
  exact le_iSup₂_of_le Q₀ (dom_ball K k₀ ε a₀ c₀ ν₀ κ r₀ hs₀ hκ hκ1 hQ₀)
    (le_iSup₂_of_le Q₁ (dom_ball K k₁ ε a₁ c₁ ν₀ κ r₁ hs₁ hκ hκ1 hQ₁) le_rfl)

/-- `log κ + log ∫ e^f dm ≤ log ∫ e^f d((1−κ)ν₀ + κm)` for `f` measurable and bounded above. -/
lemma log_integral_mix_ge (ν₀ : Measure K) [IsFiniteMeasure ν₀] (m : Measure K) [IsProbabilityMeasure m]
    {κ : ℝ} (hκ : 0 < κ) {f : K → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, f z ≤ M) :
    Real.log κ + Real.log (∫ z, Real.exp (f z) ∂m) ≤ Real.log (∫ z, Real.exp (f z) ∂(mix ν₀ κ m)) := by
  have hint : ∀ (μ : Measure K) [IsFiniteMeasure μ], Integrable (fun z => Real.exp (f z)) μ := by
    intro μ _
    refine Integrable.of_bound hf.exp.aestronglyMeasurable (Real.exp M) (ae_of_all _ fun z => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (hM z)
  have hpos : 0 < ∫ z, Real.exp (f z) ∂m := integral_exp_pos (hint m)
  have hmix : κ * ∫ z, Real.exp (f z) ∂m ≤ ∫ z, Real.exp (f z) ∂(mix ν₀ κ m) := by
    simp only [mix]
    rw [integral_add_measure ((hint ν₀).smul_measure ENNReal.ofReal_ne_top)
      ((hint m).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal hκ.le, smul_eq_mul, smul_eq_mul]
    have : 0 ≤ (ENNReal.ofReal (1 - κ)).toReal * ∫ z, Real.exp (f z) ∂ν₀ :=
      mul_nonneg ENNReal.toReal_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le)
    linarith
  rw [← Real.log_mul hκ.ne' hpos.ne']
  exact Real.log_le_log (mul_pos hκ hpos) hmix

theorem dom_cert : Claims.dom_cert := by
  intro K _ n x c h ε r lam ν₀ _ κ hn hε hlam hκ hκ1 hc ⟨B, hB⟩ hh ⟨H, hH⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : 0 < lam * ε := mul_pos hlam hε
  have hmeas : ∀ i, Measurable fun z => ((h z - h (x i)) ^ 2 - lam * c (x i) z) / (lam * ε) := fun i =>
    (((hh.sub measurable_const).pow_const 2).sub
      ((hc.comp measurable_prodMk_left).const_mul lam)).div_const _
  have hbd : ∀ i z, ((h z - h (x i)) ^ 2 - lam * c (x i) z) / (lam * ε) ≤
      ((2 * H) ^ 2 + lam * B) / (lam * ε) := by
    intro i z
    refine div_le_div_of_nonneg_right ?_ hle.le
    have h1 := abs_le.1 (hH z)
    have h2 := abs_le.1 (hH (x i))
    have h3 := abs_le.1 (hB (x i) z)
    nlinarith
  have member : ∀ m : Measure K, IsProbabilityMeasure m →
      Tref1 x c h ε (r - ε * Real.log (1 / κ)) lam m ≤ Tref1 x c h ε r lam (mix ν₀ κ m) := by
    intro m hm
    unfold Tref1
    have key := fun i => log_integral_mix_ge ν₀ m hκ (hmeas i) (hbd i)
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum
    set Sm := ∑ i, Real.log (∫ z, Real.exp (((h z - h (x i)) ^ 2 - lam * c (x i) z) / (lam * ε)) ∂m)
    set Sν := ∑ i, Real.log (∫ z, Real.exp (((h z - h (x i)) ^ 2 - lam * c (x i) z) / (lam * ε))
      ∂(mix ν₀ κ m))
    have h2 : (n : ℝ)⁻¹ * (n * Real.log κ + Sm) ≤ (n : ℝ)⁻¹ * Sν :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hle.le
    have hL : Real.log (1 / κ) = -Real.log κ := by rw [one_div, Real.log_inv]
    rw [hL]
    linear_combination h3
  refine ⟨member, ?_⟩
  unfold StatFormal.Wave4b.sqrtT
  refine iSup₂_le fun m hm => ?_
  haveI : IsProbabilityMeasure m := hm
  exact le_iSup₂_of_le (mix ν₀ κ m) (mix_mem ν₀ κ m)
    (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (member m hm)))

theorem dom_valid : Claims.dom_valid := by
  intro K _ _ n ε α κ cost ν₀ _ r hG hn hε hκ hκ1 hν₀ hatom hcm ⟨B, hB⟩ hrm hvalid P hP
  haveI : Nonempty K := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    have h1 := hP.measure_univ
    rw [Set.univ_eq_empty_iff.2 hK, measure_empty] at h1
    exact zero_ne_one h1
  have hfin : ∀ ν ∈ defMix ν₀ κ, IsFiniteMeasure ν := by
    rintro ν ⟨m, hm, rfl⟩
    exact mix_finite ν₀ κ m
  obtain ⟨E, hE, hsub, hprob⟩ := hG hn hε hcm ⟨B, hB⟩ hfin hrm hvalid P hP
  have haN := dom_aN K ν₀ κ hκ hκ1 hν₀ hatom
  refine ⟨E, hE, fun x hx => ?_, hprob⟩
  have hx' := hsub hx
  simp only [Set.mem_setOf_eq, haN] at hx'
  have hs := StatFormal.Foundations.Tax.setting_centre (cost := cost) hn hε
    (fun x0 => (hcm.comp measurable_prodMk_left : Measurable (cost x0))) hB x
  refine ⟨hP, P, hP, ?_⟩
  rw [StatFormal.RobustEquality.Tax.tax_identity K n ε _ _ P P hs, StatFormal.Foundations.Tax.klRef_self P,
    mul_zero, add_zero, EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _)),
    EReal.coe_mul]
  exact hx'

example : Claims.dom_tax_finite := dom_tax_finite
example : Claims.dom_tax_le := dom_tax_le
example : Claims.dom_aN := dom_aN
example : Claims.dom_valid := dom_valid
example : Claims.dom_ball := dom_ball
example : Claims.dom_worst := dom_worst
example : Claims.dom_cert := dom_cert

end StatFormal.Wave11a
