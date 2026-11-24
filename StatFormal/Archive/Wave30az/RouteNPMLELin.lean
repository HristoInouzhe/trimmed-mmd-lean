import StatFormal.Archive.Wave30az.RouteNPMLE

/-!
# Route — paper 2 `thm:npmle`, linear rules and a general kernel: convexity, correction, the programme

* `Φ_y(z,w,λ) = λ(n⁻¹ Σ e^{z_i/(λε)} ψ_i(y) − 1)` with `ψ_i(y) = ∫ e^{φ_i} dκ_y`, `φ_i = gexp/(λε)` (`PhiK_eq`), so
  `Φ_y ≤ 0 ∀y` is dual feasibility of `v_i = e^{z_i/(λε)}` and `λr − n⁻¹Σz_i = λr + λε D(v)`.
* Convexity: the integrand is the certified finite `Phi` at one atom plus `λ` (jointly convex), integrated against
  `κ(y, ·)` (bounded continuous integrands on the compact `K`).
* Correction: `Φ_y(z') = (Φ_y(z) + λ)/max(1,V₀) − λ ≤ 0`, then weak duality (`npmle_weak`) bounds every value in
  the sup defining `T^𝒩_s`.
* Programme: `npmle_gen_duality` on the compact subtype `K` (continuous exponents of a linear rule).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave30az

open StatFormal.Wave29d (psiK npmleK lambdaK MixSettingK)
open StatFormal.Wave29d.LindsayGen
open StatFormal.RobustEquality.Paper2.Seminorm (gexp Phi)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  {L : Type} [MeasurableSpace L] {K : Set V} {n : ℕ}

lemma bdd_of_cont (hK : IsCompact K) {f : K → ℝ} (hf : Continuous f) : ∃ C, ∀ ξ, |f ξ| ≤ C := by
  haveI := isCompact_iff_compactSpace.1 hK
  obtain ⟨C, hC⟩ := (isCompact_univ.image hf).isBounded.exists_norm_le
  exact ⟨C, fun ξ => by rw [← Real.norm_eq_abs]; exact hC _ ⟨ξ, mem_univ _, rfl⟩⟩

lemma integrable_of_cont (hK : IsCompact K) (μ : Measure K) [IsFiniteMeasure μ] {f : K → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := bdd_of_cont hK hf
  exact Integrable.of_bound hf.measurable.aestronglyMeasurable C
    (Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hC ξ)

lemma continuous_gexp_sub (w : V) (l : ℝ) (x₀ : V) : Continuous fun ξ : K => gexp w l ((ξ : V) - x₀) := by
  unfold gexp
  have h1 : Continuous fun ξ : K => (ξ : V) - x₀ := continuous_subtype_val.sub continuous_const
  exact ((continuous_const.inner h1).pow 2).sub (continuous_const.mul (h1.norm.pow 2))

lemma continuous_phiLin (ε : ℝ) (x : Fin n → V) (w : V) (l : ℝ) (i : Fin n) :
    Continuous (phiLin K ε x w l i) := by
  unfold phiLin
  exact (continuous_gexp_sub w l (x i)).div_const _

lemma mixSetting_phiLin (hK : IsCompact K) (hn : 0 < n) (ε : ℝ) (κ : Kernel L K)
    (hκ : ∀ y, 0 < κ y univ ∧ κ y univ ≤ 1) (x : Fin n → V) (w : V) (l : ℝ) :
    MixSettingK κ (phiLin K ε x w l) := by
  refine ⟨hn, hκ, fun i => (continuous_phiLin ε x w l i).measurable, ?_⟩
  choose B hB using fun i => bdd_of_cont hK (continuous_phiLin (K := K) ε x w l i)
  refine ⟨∑ i, |B i|, fun i ξ => (hB i ξ).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun i => |B i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)

omit [BorelSpace V] in
lemma integrand_split (ε l : ℝ) (hl : 0 < l) (hε : 0 < ε) (x : Fin n → V) (z : Fin n → ℝ) (w : V) (i : Fin n)
    (ξ : K) : Real.exp ((z i + gexp w l ((ξ : V) - x i)) / (l * ε)) =
      Real.exp (z i / (l * ε)) * Real.exp (phiLin K ε x w l i ξ) := by
  rw [← Real.exp_add, phiLin, add_div]

lemma PhiK_eq (hK : IsCompact K) (ε l : ℝ) (hl : 0 < l) (hε : 0 < ε) (κ : Kernel L K)
    (x : Fin n → V) (z : Fin n → ℝ) (w : V) (y : L) :
    PhiK K ε κ x z w l y =
      l * ((1 / n : ℝ) * ∑ i, Real.exp (z i / (l * ε)) * psiK κ (phiLin K ε x w l) i y) - l := by
  unfold PhiK psiK
  simp_rw [integrand_split ε l hl hε x z w, integral_const_mul]
  ring

/-- Feasibility of `z` is dual feasibility of `v = e^{z/(λε)}`. -/
lemma feas_iff (hK : IsCompact K) (ε l : ℝ) (hl : 0 < l) (hε : 0 < ε) (κ : Kernel L K)
    (x : Fin n → V) (z : Fin n → ℝ) (w : V) (y : L) :
    PhiK K ε κ x z w l y ≤ 0 ↔
      (1 / n : ℝ) * ∑ i, Real.exp (z i / (l * ε)) * psiK κ (phiLin K ε x w l) i y ≤ 1 := by
  rw [PhiK_eq hK ε l hl hε κ x z w y]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

lemma dual_value (ε l : ℝ) (hl : 0 < l) (hε : 0 < ε) (z : Fin n → ℝ) :
    l * ε * -((1 / n : ℝ) * ∑ i, Real.log (Real.exp (z i / (l * ε)))) = -((1 / (n : ℝ)) * ∑ i, z i) := by
  simp_rw [Real.log_exp]
  rw [← Finset.sum_div]
  field_simp

/-! ### Convexity -/

theorem npmle_gen_convex : Claims.npmle_gen_convex := by
  intro V _ _ _ _ L _ K n ε κ x y hK hn hε hκ
  haveI : IsFiniteMeasure (κ y) := ⟨lt_of_le_of_lt hκ ENNReal.one_lt_top⟩
  set s : Set ((Fin n → ℝ) × V × ℝ) := Set.univ ×ˢ (Set.univ ×ˢ Set.Ioi 0) with hs
  have hsc : Convex ℝ s := convex_univ.prod (convex_univ.prod (convex_Ioi 0))
  -- the integrand
  set H : (Fin n → ℝ) × V × ℝ → K → ℝ := fun q ξ =>
    q.2.2 / n * ∑ i, Real.exp ((q.1 i + gexp q.2.1 q.2.2 ((ξ : V) - x i)) / (q.2.2 * ε)) with hH
  have hHphi : ∀ q ξ, H q ξ = Phi ε x (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (ξ : V)) q.1 q.2.1 q.2.2 + q.2.2 := by
    intro q ξ
    simp only [hH, Phi, Fin.sum_univ_one, one_mul]
    ring
  have hlin : ConvexOn ℝ s (fun q : (Fin n → ℝ) × V × ℝ => q.2.2) :=
    ⟨hsc, fun a _ b _ μ ν _ _ _ => by simp [smul_eq_mul]⟩
  have hHc : ∀ ξ : K, ConvexOn ℝ s (fun q => H q ξ) := by
    intro ξ
    have h := (StatFormal.RobustEquality.Paper2.Seminorm.npmle_convex V n 1 ε x (fun _ => 1) (fun _ => (ξ : V))
      hn hε (fun _ => zero_le_one)).add hlin
    simp_rw [hHphi]
    exact h
  have hHi : ∀ q, Integrable (H q) (κ y) := by
    intro q
    apply integrable_of_cont hK
    exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
      Real.continuous_exp.comp (((continuous_const.add (continuous_gexp_sub q.2.1 q.2.2 (x i)))).div_const _))
  have hPhiK : ∀ q : (Fin n → ℝ) × V × ℝ, PhiK K ε κ x q.1 q.2.1 q.2.2 y = ∫ ξ, H q ξ ∂(κ y) - q.2.2 := by
    intro q
    simp only [PhiK, hH]
    rw [integral_const_mul, integral_finset_sum]
    intro i _
    apply integrable_of_cont hK
    exact Real.continuous_exp.comp (((continuous_const.add (continuous_gexp_sub q.2.1 q.2.2 (x i)))).div_const _)
  refine ⟨hsc, fun q1 hq1 q2 hq2 a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rw [hPhiK, hPhiK, hPhiK]
  have hpt : ∀ ξ, H (a • q1 + b • q2) ξ ≤ a * H q1 ξ + b * H q2 ξ := fun ξ =>
    (hHc ξ).2 hq1 hq2 ha hb hab
  have hint := integral_mono (hHi (a • q1 + b • q2)) (g := fun ξ => a * H q1 ξ + b * H q2 ξ)
    (((hHi q1).const_mul a).add ((hHi q2).const_mul b)) hpt
  rw [integral_add ((hHi q1).const_mul a) ((hHi q2).const_mul b), integral_const_mul a, integral_const_mul b] at hint
  have e : (a • q1 + b • q2).2.2 = a * q1.2.2 + b * q2.2.2 := by simp [smul_eq_mul]
  rw [e]
  nlinarith

/-! ### The certified correction -/

theorem npmle_gen_correction : Claims.npmle_gen_correction := by
  intro V _ _ _ _ L _ _ K n ε r l V₀ κ x z w hK hn hε hl hκ hV
  have hS := mixSetting_phiLin hK hn ε κ hκ x w l
  set M := max 1 V₀ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM1
  set z' : Fin n → ℝ := fun i => z i - l * ε * Real.log M with hz'
  have hexp : ∀ i, Real.exp (z' i / (l * ε)) = Real.exp (z i / (l * ε)) / M := by
    intro i
    simp only [hz']
    rw [sub_div, mul_div_cancel_left₀ _ (by positivity : l * ε ≠ 0), Real.exp_sub, Real.exp_log hM0]
  have hfeas : ∀ y, PhiK K ε κ x z' w l y ≤ 0 := by
    intro y
    have h1 := hV y
    rw [PhiK_eq hK ε l hl hε κ x z' w y]
    rw [PhiK_eq hK ε l hl hε κ x z w y] at h1
    set S := (1 / n : ℝ) * ∑ i, Real.exp (z i / (l * ε)) * psiK κ (phiLin K ε x w l) i y with hSdef
    have hS' : (1 / n : ℝ) * ∑ i, Real.exp (z' i / (l * ε)) * psiK κ (phiLin K ε x w l) i y = S / M := by
      simp_rw [hexp, div_mul_eq_mul_div, ← Finset.sum_div]
      rw [hSdef]; ring
    rw [hS']
    have hSle : S ≤ V₀ := by
      have : (l * S - l) / l + 1 = S := by field_simp; ring
      linarith
    have : S / M ≤ 1 := by
      rw [div_le_one hM0]; exact hSle.trans (le_max_right _ _)
    nlinarith
  refine ⟨hfeas, ?_⟩
  -- weak duality against every reference of the class
  have hv : ∀ i, 0 < Real.exp (z' i / (l * ε)) := fun i => Real.exp_pos _
  have hvf : ∀ y, (1 / n : ℝ) * ∑ i, Real.exp (z' i / (l * ε)) * psiK κ (phiLin K ε x w l) i y ≤ 1 :=
    fun y => (feas_iff hK ε l hl hε κ x z' w y).1 (hfeas y)
  have hbound : lambdaK κ (phiLin K ε x w l) {m | IsProbabilityMeasure m} ≤
      -((1 / n : ℝ) * ∑ i, Real.log (Real.exp (z' i / (l * ε)))) := by
    rw [lambdaK_eq hS (M := {m : Measure L | IsProbabilityMeasure m}) (fun m hm => hm)]
    obtain ⟨y⟩ := (inferInstance : Nonempty L)
    refine csSup_le ⟨_, Measure.dirac y, (inferInstance : IsProbabilityMeasure (Measure.dirac y)), rfl⟩ ?_
    rintro _ ⟨m, hm, rfl⟩
    exact npmle_weak K L n κ _ m _ hS hm hv hvf
  unfold TK
  have hle := mul_le_mul_of_nonneg_left hbound (by positivity : (0 : ℝ) ≤ l * ε)
  rw [dual_value ε l hl hε z'] at hle
  linarith

/-! ### The convex semi-infinite programme -/

theorem npmle_gen_programme : Claims.npmle_gen_programme := by
  intro V _ _ _ _ L _ _ _ _ _ K n ε r κ x w hK hn hε hκ hF
  haveI := isCompact_iff_compactSpace.1 hK
  have hslice : ∀ l : ℝ, 0 < l →
      IsLeast {v | ∃ z : Fin n → ℝ, (∀ y, PhiK K ε κ x z w l y ≤ 0) ∧ v = l * r - (1 / (n : ℝ)) * ∑ i, z i}
        (TK K ε r κ x w l) := by
    intro l hl
    have hS := mixSetting_phiLin hK hn ε κ hκ x w l
    obtain ⟨⟨ms, hms, hmax⟩, hrest⟩ := npmle_gen_duality K L n κ (phiLin K ε x w l) hS
      (fun i => continuous_phiLin ε x w l i) hF
    obtain ⟨hlam, hfeas, hval, -⟩ := hrest ms hms hmax
    have hT : TK K ε r κ x w l = l * r + l * ε * npmleK κ (phiLin K ε x w l) ms := by
      unfold TK; rw [hlam]
    have hA : ∀ i, 0 < ∫ y', psiK κ (phiLin K ε x w l) i y' ∂ms := fun i => A_pos hS i
    refine ⟨⟨fun i => l * ε * Real.log (1 / ∫ y', psiK κ (phiLin K ε x w l) i y' ∂ms), fun y => ?_, ?_⟩, ?_⟩
    · rw [feas_iff hK ε l hl hε κ x _ w y]
      have e : ∀ i, Real.exp (l * ε * Real.log (1 / ∫ y', psiK κ (phiLin K ε x w l) i y' ∂ms) / (l * ε)) =
          1 / ∫ y', psiK κ (phiLin K ε x w l) i y' ∂ms := by
        intro i
        rw [mul_div_cancel_left₀ _ (by positivity : l * ε ≠ 0), Real.exp_log (one_div_pos.2 (hA i))]
      simp_rw [e]
      exact hfeas y
    · rw [hT, ← hval]
      rw [← Finset.mul_sum]
      ring
    · rintro v ⟨z, hz, rfl⟩
      have hvf : ∀ y, (1 / n : ℝ) * ∑ i, Real.exp (z i / (l * ε)) * psiK κ (phiLin K ε x w l) i y ≤ 1 :=
        fun y => (feas_iff hK ε l hl hε κ x z w y).1 (hz y)
      have hw := npmle_weak K L n κ _ ms _ hS hms (fun i => Real.exp_pos _) hvf
      have hle := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ l * ε)
      rw [dual_value ε l hl hε z] at hle
      rw [hT]
      linarith
  refine ⟨hslice, fun N2 => ?_⟩
  have hlb : lowerBounds {t | ∃ l : ℝ, 0 < l ∧ t = TK K ε r κ x w l} =
      lowerBounds {v | ∃ (l : ℝ) (z : Fin n → ℝ), 0 < l ∧ (∀ y, PhiK K ε κ x z w l y ≤ 0) ∧
        v = l * r - (1 / (n : ℝ)) * ∑ i, z i} := by
    ext b
    constructor
    · rintro hb _ ⟨l, z, hl, hz, rfl⟩
      exact (hb ⟨l, hl, rfl⟩).trans ((hslice l hl).2 ⟨z, hz, rfl⟩)
    · rintro hb _ ⟨l, hl, rfl⟩
      obtain ⟨z, hz, he⟩ := (hslice l hl).1
      rw [he]
      exact hb ⟨l, z, hl, hz, rfl⟩
  unfold IsGLB
  rw [hlb]

end StatFormal.Wave30az
