import StatFormal.Archive.RobustEquality.Certificate.Proofs
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Strong duality for a single reference (`prop:strong`(ii), Step 1)

Library component (robust equality, JASA). Untrusted library code; it imports the certified
`Certificate/Proofs.lean` (weak duality `lagrangian_bound`) and the frozen definitions `Tref1`,
`klRef`.

For a centre `P̂ = n⁻¹ Σ_i δ_{x_i}`, a finite reference `ν ≠ 0`, a bounded cost `c ≥ 0` and a
bounded measurable rule `h`, write `Ψ(λ) = Tref1 x c h ε r λ ν` and
`v(r) = sup {n⁻¹ Σ_i E_{Γ_i} f_h(x_i, ·) : n⁻¹ Σ_i (E_{Γ_i} c(x_i, ·) + ε KL(Γ_i‖ν)) ≤ r}`.

## Main result

* `strong_duality_single`: if `r > ρ_ν := −ε n⁻¹ Σ_i log ∫ e^{−c(x_i,·)/ε} dν` (the floor), then
  `inf_{λ>0} Ψ(λ) = v(r)` (both as a `IsGLB`/`IsLUB` of one real number).

## Proof (no supergradient, no Danskin)

The Gibbs kernels `Γ^s_i = ν.tilted (s f_h(x_i,·) − c(x_i,·)/ε)`, `s ≥ 0`, satisfy, with
`λ = 1/(εs)`, the identity `E_{Γ^s} f − λ (G(Γ^s) − r) = Ψ(λ)` (`EF_sub_eq_Tref1`), where the budget
`G(Γ^s)` is continuous in `s ∈ [0, ∞)` with `G(Γ^0) = ρ_ν` (`Gf_zero`) and `G(Γ^s) ≥ ρ_ν`
(`floor_le_Gf`). Either the budget is binding at some `s > 0` (then `Ψ(1/(εs)) = E_{Γ^s} f ≤ v(r)`),
or by the intermediate value theorem `G(Γ^s) ≤ r` for **every** `s > 0` — the boundary branch
`λ* = 0` — and then `E_{Γ^s} f ≥ Ψ(λ) − λ (r − ρ_ν) → inf Ψ` as `λ → 0`. This branch needs
neither `ν(K) ≤ 1` nor an essential-supremum computation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set Real
open scoped ENNReal

namespace StatFormal.Foundations.Strong

open StatFormal.RobustEquality StatFormal.RobustEquality.Certificate

variable {K : Type} [MeasurableSpace K]

/-! ### Tilted measures -/

theorem tilted_facts (ν : Measure K) [IsFiniteMeasure ν] [NeZero ν] {g : K → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ z, |g z| ≤ B) :
    IsProbabilityMeasure (ν.tilted g) ∧ ν.tilted g ≪ ν ∧
      Integrable (llr (ν.tilted g) ν) (ν.tilted g) ∧
      ∫ z, llr (ν.tilted g) ν z ∂(ν.tilted g) =
        (∫ z, g z ∂(ν.tilted g)) - Real.log (∫ z, Real.exp (g z) ∂ν) := by
  have hexp : Integrable (fun x => Real.exp (g x)) ν := by
    refine Integrable.of_bound (hg.exp.aestronglyMeasurable) (Real.exp B) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hB x))
  have hτ : IsProbabilityMeasure (ν.tilted g) := isProbabilityMeasure_tilted hexp
  have hac : ν.tilted g ≪ ν := tilted_absolutelyContinuous ν g
  have hll : llr (ν.tilted g) ν =ᵐ[ν.tilted g]
      fun x => g x - Real.log (∫ x, Real.exp (g x) ∂ν) :=
    hac.ae_le (log_rnDeriv_tilted_left_self hexp)
  have hgτ : Integrable g (ν.tilted g) := by
    refine Integrable.of_bound hg.aestronglyMeasurable B ?_
    exact Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x
  have hint : Integrable (llr (ν.tilted g) ν) (ν.tilted g) := by
    rw [integrable_congr hll]
    exact hgτ.sub (integrable_const _)
  refine ⟨hτ, hac, hint, ?_⟩
  rw [integral_congr_ae hll, integral_sub hgτ (integrable_const _)]
  simp

theorem klRef_tilted (ν : Measure K) [IsFiniteMeasure ν] [NeZero ν] {g : K → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ z, |g z| ≤ B) :
    klRef (ν.tilted g) ν =
      (((∫ z, g z ∂(ν.tilted g)) - Real.log (∫ z, Real.exp (g z) ∂ν) : ℝ) : EReal) := by
  obtain ⟨-, hac, hint, hval⟩ := tilted_facts ν hg hB
  rw [klRef, ite_eq_left ⟨hac, hint⟩, hval]

theorem integral_tilted_eq (ν : Measure K) (g φ : K → ℝ) :
    ∫ z, φ z ∂(ν.tilted g) = (∫ z, Real.exp (g z) * φ z ∂ν) / ∫ z, Real.exp (g z) ∂ν := by
  rw [integral_tilted, ← integral_div]
  congr 1; ext z
  rw [smul_eq_mul]; ring

/-! ### The Gibbs family -/

variable {n : ℕ}

/-- The exponent `s F_i − C_i/ε` of the Gibbs kernel. -/
def gExp (F C : Fin n → K → ℝ) (ε s : ℝ) (i : Fin n) (z : K) : ℝ := s * F i z - C i z / ε

/-- The Gibbs kernel `Γ^s_i = ν.tilted (s F_i − C_i/ε)`. -/
def Ker (ν : Measure K) (F C : Fin n → K → ℝ) (ε s : ℝ) (i : Fin n) : Measure K :=
  ν.tilted (gExp F C ε s i)

/-- `log Z_i(s)`. -/
def logZ (ν : Measure K) (F C : Fin n → K → ℝ) (ε s : ℝ) (i : Fin n) : ℝ :=
  Real.log (∫ z, Real.exp (gExp F C ε s i z) ∂ν)

/-- Expected objective `n⁻¹ Σ_i E_{Γ^s_i} F_i`. -/
def EF (ν : Measure K) (F C : Fin n → K → ℝ) (ε s : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, ∫ z, F i z ∂(Ker ν F C ε s i)

/-- Budget of the Gibbs kernel, `n⁻¹ Σ_i (E_{Γ^s_i} C_i + ε KL(Γ^s_i‖ν))`, in closed form. -/
def Gf (ν : Measure K) (F C : Fin n → K → ℝ) (ε s : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (ε * s * ∫ z, F i z ∂(Ker ν F C ε s i) - ε * logZ ν F C ε s i)

/-- The floor `ρ_ν = −ε n⁻¹ Σ_i log ∫ e^{−C_i/ε} dν`. -/
def floorRho (ν : Measure K) (C : Fin n → K → ℝ) (ε : ℝ) : ℝ :=
  -ε * ((n : ℝ)⁻¹ * ∑ i, Real.log (∫ z, Real.exp (-(C i z) / ε) ∂ν))

section Hyp

variable (ν : Measure K) [IsFiniteMeasure ν] [NeZero ν] {F C : Fin n → K → ℝ} {ε M : ℝ}

theorem measurable_gExp (hF : ∀ i, Measurable (F i)) (hC : ∀ i, Measurable (C i)) (s : ℝ)
    (i : Fin n) : Measurable (gExp F C ε s i) :=
  ((hF i).const_mul s).sub ((hC i).div_const ε)

omit [MeasurableSpace K] in
theorem abs_gExp_le (hε : 0 < ε) (hFb : ∀ i z, |F i z| ≤ M) (hCb : ∀ i z, |C i z| ≤ M)
    (s : ℝ) (i : Fin n) (z : K) : |gExp F C ε s i z| ≤ |s| * M + M / ε := by
  unfold gExp
  calc |s * F i z - C i z / ε| ≤ |s * F i z| + |C i z / ε| := abs_sub _ _
    _ = |s| * |F i z| + |C i z| / ε := by rw [abs_mul, abs_div, abs_of_pos hε]
    _ ≤ |s| * M + M / ε := by
        gcongr
        · exact hFb i z
        · exact hCb i z

theorem integral_gExp (_hε : 0 < ε) (hF : ∀ i, Measurable (F i)) (hC : ∀ i, Measurable (C i))
    (hFb : ∀ i z, |F i z| ≤ M) (hCb : ∀ i z, |C i z| ≤ M) (Γ : Measure K) [IsFiniteMeasure Γ]
    (s : ℝ) (i : Fin n) :
    ∫ z, gExp F C ε s i z ∂Γ = s * ∫ z, F i z ∂Γ - (∫ z, C i z ∂Γ) / ε := by
  have hFi : Integrable (F i) Γ := Integrable.of_bound (hF i).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hFb i z)
  have hCi : Integrable (C i) Γ := Integrable.of_bound (hC i).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hCb i z)
  unfold gExp
  rw [integral_sub (hFi.const_mul s) (hCi.div_const ε), integral_const_mul, integral_div]

/-- The budget of the Gibbs kernel is `Gf`. -/
theorem budget_Ker (hε : 0 < ε) (hF : ∀ i, Measurable (F i)) (hC : ∀ i, Measurable (C i))
    (hFb : ∀ i z, |F i z| ≤ M) (hCb : ∀ i z, |C i z| ≤ M) (s : ℝ) :
    ((n : ℝ)⁻¹ : EReal) * ∑ i, (((∫ z, C i z ∂(Ker ν F C ε s i) : ℝ) : EReal) +
      (ε : EReal) * klRef (Ker ν F C ε s i) ν) = ((Gf ν F C ε s : ℝ) : EReal) := by
  have hB := abs_gExp_le hε hFb hCb s
  have hkl : ∀ i, klRef (Ker ν F C ε s i) ν =
      (((∫ z, gExp F C ε s i z ∂(Ker ν F C ε s i)) - logZ ν F C ε s i : ℝ) : EReal) :=
    fun i => klRef_tilted ν (measurable_gExp hF hC s i) (hB i)
  have hprob : ∀ i, IsProbabilityMeasure (Ker ν F C ε s i) := fun i =>
    (tilted_facts ν (measurable_gExp hF hC s i) (hB i)).1
  simp only [hkl]
  have hsum : ∑ i, (((∫ z, C i z ∂(Ker ν F C ε s i) : ℝ) : EReal) + (ε : EReal) *
      (((∫ z, gExp F C ε s i z ∂(Ker ν F C ε s i)) - logZ ν F C ε s i : ℝ) : EReal)) =
      ((∑ i, ((∫ z, C i z ∂(Ker ν F C ε s i)) + ε * ((∫ z, gExp F C ε s i z ∂(Ker ν F C ε s i))
        - logZ ν F C ε s i)) : ℝ) : EReal) := by
    have := map_sum Real.toERealAddHom (fun i => (∫ z, C i z ∂(Ker ν F C ε s i)) +
      ε * ((∫ z, gExp F C ε s i z ∂(Ker ν F C ε s i)) - logZ ν F C ε s i)) Finset.univ
    simp only [Real.coe_toERealAddHom] at this
    rw [this]
    simp only [EReal.coe_add, EReal.coe_mul]
  rw [hsum, ← EReal.coe_inv, ← EReal.coe_mul, EReal.coe_eq_coe_iff]
  unfold Gf
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hprob i
  rw [integral_gExp hε hF hC hFb hCb]
  field_simp
  ring

omit [IsFiniteMeasure ν] [NeZero ν] in
/-- **The Lagrangian identity at the Gibbs kernel**: `E_{Γ^s} F − λ (G(Γ^s) − r) = Ψ(λ)` for
`λ = 1/(εs)`. -/
theorem EF_sub_eq (hε : 0 < ε) {lam : ℝ} (hlam : 0 < lam) (r : ℝ) :
    EF ν F C ε (1 / (lam * ε)) - lam * (Gf ν F C ε (1 / (lam * ε)) - r) =
      lam * r + lam * ε * ((n : ℝ)⁻¹ * ∑ i, logZ ν F C ε (1 / (lam * ε)) i) := by
  unfold EF Gf
  have hl : lam * ε ≠ 0 := (mul_pos hlam hε).ne'
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  field_simp
  ring

omit [IsFiniteMeasure ν] [NeZero ν] in
/-- `Gf 0 = ρ_ν`. -/
theorem Gf_zero : Gf ν F C ε 0 = floorRho ν C ε := by
  unfold Gf floorRho logZ gExp
  simp only [mul_zero, zero_mul, zero_sub, neg_div]
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

/-- **Floor**: the budget of every Gibbs kernel is at least `ρ_ν`. -/
theorem floor_le_Gf (hε : 0 < ε) (hF : ∀ i, Measurable (F i)) (hC : ∀ i, Measurable (C i))
    (hFb : ∀ i z, |F i z| ≤ M) (hCb : ∀ i z, |C i z| ≤ M) (s : ℝ) :
    floorRho ν C ε ≤ Gf ν F C ε s := by
  have hB := abs_gExp_le hε hFb hCb s
  have hper : ∀ i, -ε * Real.log (∫ z, Real.exp (-(C i z) / ε) ∂ν) ≤
      ε * s * (∫ z, F i z ∂(Ker ν F C ε s i)) - ε * logZ ν F C ε s i := by
    intro i
    obtain ⟨hprob, hac, hint, hval⟩ := tilted_facts ν (measurable_gExp hF hC s i) (hB i)
    have : IsProbabilityMeasure (Ker ν F C ε s i) := hprob
    have hg0m : Measurable fun z => -(C i z) / ε := (hC i).neg.div_const ε
    have hg0b : ∀ z, |-(C i z) / ε| ≤ M / ε := fun z => by
      rw [abs_div, abs_neg, abs_of_pos hε]
      exact div_le_div_of_nonneg_right (hCb i z) hε.le
    obtain ⟨h1, -⟩ := StatFormal.RobustEquality.gibbs_finite_case ν _ hg0m _ hg0b
      (Ker ν F C ε s i) hac hint
    have hCi : Integrable (C i) (Ker ν F C ε s i) := Integrable.of_bound
      (hC i).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hCb i z)
    simp only [Ker] at h1 ⊢
    rw [hval] at h1
    rw [integral_gExp hε hF hC hFb hCb] at h1
    have e : ∫ z, -(C i z) / ε ∂(ν.tilted (gExp F C ε s i)) =
        -(∫ z, C i z ∂(ν.tilted (gExp F C ε s i))) / ε := by
      rw [integral_div, integral_neg]
    rw [e] at h1
    unfold logZ
    have := (mul_le_mul_of_nonneg_left h1 hε.le)
    field_simp at this
    simp only [neg_div] at this ⊢
    linarith [this]
  unfold floorRho Gf
  rw [show -ε * ((n : ℝ)⁻¹ * ∑ i, Real.log (∫ z, Real.exp (-(C i z) / ε) ∂ν)) =
    (n : ℝ)⁻¹ * ∑ i, (-ε * Real.log (∫ z, Real.exp (-(C i z) / ε) ∂ν)) by
      rw [← Finset.mul_sum]; ring]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hper i)
    (inv_nonneg.2 (Nat.cast_nonneg n))

/-! ### Continuity in `s` -/

omit [NeZero ν] in
theorem continuousOn_integral_exp (hε : 0 < ε) (hF : ∀ i, Measurable (F i))
    (hC : ∀ i, Measurable (C i)) (hFb : ∀ i z, |F i z| ≤ M) (hCb : ∀ i z, |C i z| ≤ M)
    {φ : K → ℝ} (hφ : Measurable φ) {Mφ : ℝ} (hφb : ∀ z, |φ z| ≤ Mφ) (S : ℝ) (i : Fin n) :
    ContinuousOn (fun s => ∫ z, Real.exp (gExp F C ε s i z) * φ z ∂ν) (Icc 0 S) := by
  refine continuousOn_of_dominated (bound := fun _ => Real.exp (|S| * M + M / ε) * Mφ)
    (fun s _ => ((measurable_gExp hF hC s i).exp.mul hφ).aestronglyMeasurable)
    (fun s hs => Filter.Eventually.of_forall fun z => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun z => ?_)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (Real.exp_le_exp.2 ?_) (hφb z) (abs_nonneg _) (Real.exp_pos _).le
    refine (le_abs_self _).trans ((abs_gExp_le hε hFb hCb s i z).trans ?_)
    have : |s| ≤ |S| := by
      rw [abs_of_nonneg hs.1]; exact hs.2.trans (le_abs_self S)
    have hM : 0 ≤ M := (abs_nonneg _).trans (hFb i z)
    gcongr
  · unfold gExp
    fun_prop

theorem integral_exp_gExp_pos (hF : ∀ i, Measurable (F i)) (hC : ∀ i, Measurable (C i))
    (hε : 0 < ε) (hFb : ∀ i z, |F i z| ≤ M) (hCb : ∀ i z, |C i z| ≤ M) (s : ℝ) (i : Fin n) :
    0 < ∫ z, Real.exp (gExp F C ε s i z) ∂ν := by
  have hexp : Integrable (fun z => Real.exp (gExp F C ε s i z)) ν := by
    refine Integrable.of_bound ((measurable_gExp hF hC s i).exp.aestronglyMeasurable)
      (Real.exp (|s| * M + M / ε)) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (abs_gExp_le hε hFb hCb s i z))
  exact integral_exp_pos hexp

theorem continuousOn_Gf (hε : 0 < ε) (hF : ∀ i, Measurable (F i)) (hC : ∀ i, Measurable (C i))
    (hFb : ∀ i z, |F i z| ≤ M) (hCb : ∀ i z, |C i z| ≤ M) (S : ℝ) :
    ContinuousOn (fun s => Gf ν F C ε s) (Icc 0 S) := by
  have hZ : ∀ i, ContinuousOn (fun s => ∫ z, Real.exp (gExp F C ε s i z) ∂ν) (Icc 0 S) :=
    fun i => by
      have := continuousOn_integral_exp ν hε hF hC hFb hCb (φ := fun _ => (1 : ℝ))
        measurable_const (Mφ := 1) (fun _ => by simp) S i
      simpa using this
  have hN : ∀ i, ContinuousOn (fun s => ∫ z, Real.exp (gExp F C ε s i z) * F i z ∂ν) (Icc 0 S) :=
    fun i => continuousOn_integral_exp ν hε hF hC hFb hCb (hF i) (hFb i) S i
  have hpos := integral_exp_gExp_pos ν hF hC hε hFb hCb
  unfold Gf Ker logZ
  simp_rw [integral_tilted_eq]
  refine ContinuousOn.mul continuousOn_const (continuousOn_finsetSum _ fun i _ => ?_)
  refine ContinuousOn.sub ?_ ?_
  · exact (continuousOn_const.mul continuousOn_id).mul
      ((hN i).div (hZ i) fun s _ => (hpos s i).ne')
  · exact continuousOn_const.mul ((hZ i).log fun s _ => (hpos s i).ne')

theorem continuousOn_EF (hε : 0 < ε) (hF : ∀ i, Measurable (F i)) (hC : ∀ i, Measurable (C i))
    (hFb : ∀ i z, |F i z| ≤ M) (hCb : ∀ i z, |C i z| ≤ M) (S : ℝ) :
    ContinuousOn (fun s => EF ν F C ε s) (Icc 0 S) := by
  have hZ : ∀ i, ContinuousOn (fun s => ∫ z, Real.exp (gExp F C ε s i z) ∂ν) (Icc 0 S) :=
    fun i => by
      have := continuousOn_integral_exp ν hε hF hC hFb hCb (φ := fun _ => (1 : ℝ))
        measurable_const (Mφ := 1) (fun _ => by simp) S i
      simpa using this
  have hN : ∀ i, ContinuousOn (fun s => ∫ z, Real.exp (gExp F C ε s i z) * F i z ∂ν) (Icc 0 S) :=
    fun i => continuousOn_integral_exp ν hε hF hC hFb hCb (hF i) (hFb i) S i
  have hpos := integral_exp_gExp_pos ν hF hC hε hFb hCb
  unfold EF Ker
  simp_rw [integral_tilted_eq]
  exact ContinuousOn.mul continuousOn_const (continuousOn_finsetSum _ fun i _ =>
    (hN i).div (hZ i) fun s _ => (hpos s i).ne')

theorem EF_le (hε : 0 < ε) (hF : ∀ i, Measurable (F i)) (hC : ∀ i, Measurable (C i))
    (hFb : ∀ i z, |F i z| ≤ M) (hCb : ∀ i z, |C i z| ≤ M) (hn : 0 < n) (s : ℝ) :
    EF ν F C ε s ≤ M := by
  have hB := abs_gExp_le hε hFb hCb s
  unfold EF
  have hle : ∀ i, ∫ z, F i z ∂(Ker ν F C ε s i) ≤ M := fun i => by
    have : IsProbabilityMeasure (Ker ν F C ε s i) :=
      (tilted_facts ν (measurable_gExp hF hC s i) (hB i)).1
    have hFi : Integrable (F i) (Ker ν F C ε s i) := Integrable.of_bound
      (hF i).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hFb i z)
    calc ∫ z, F i z ∂(Ker ν F C ε s i) ≤ ∫ _z, M ∂(Ker ν F C ε s i) :=
          integral_mono hFi (integrable_const _) fun z => (le_abs_self _).trans (hFb i z)
      _ = M := by simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc (n : ℝ)⁻¹ * ∑ i, ∫ z, F i z ∂(Ker ν F C ε s i) ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, M :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hle i) (by positivity)
    _ = M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

end Hyp

/-! ### Strong duality -/

/-- **Strong duality for a single reference** (`prop:strong`(ii), Step 1, including the boundary
branch `λ* = 0`): above the floor, `inf_{λ>0} Ψ(λ)` equals the supremum of the coupling objective
over the kernels whose budget is at most `r`. -/
theorem strong_duality_single {n : ℕ} (hn : 0 < n) (x : Fin n → K) (c : K → K → ℝ)
    (hc : Measurable (Function.uncurry c)) (hc0 : ∀ a b, 0 ≤ c a b) {B : ℝ}
    (hB : ∀ a b, c a b ≤ B) {h : K → ℝ} (hh : Measurable h) {H : ℝ} (hH : ∀ z, |h z| ≤ H)
    {ε r : ℝ} (hε : 0 < ε) (ν : Measure K) [IsFiniteMeasure ν] (hν0 : ν Set.univ ≠ 0)
    (hr : floorRho ν (fun i z => c (x i) z) ε < r) :
    ∃ V : ℝ, IsGLB {t | ∃ lam : ℝ, 0 < lam ∧ t = Tref1 x c h ε r lam ν} V ∧
      IsLUB {t | ∃ Γ : Fin n → Measure K, (∀ i, IsProbabilityMeasure (Γ i)) ∧
        ((n : ℝ)⁻¹ : EReal) * ∑ i, (((∫ z, c (x i) z ∂(Γ i) : ℝ) : EReal) +
          (ε : EReal) * klRef (Γ i) ν) ≤ (r : EReal) ∧
        t = (n : ℝ)⁻¹ * ∑ i, ∫ z, (h z - h (x i)) ^ 2 ∂(Γ i)} V := by
  have : NeZero ν := ⟨fun h0 => hν0 (by simp [h0])⟩
  set F : Fin n → K → ℝ := fun i z => (h z - h (x i)) ^ 2 with hFdef
  set C : Fin n → K → ℝ := fun i z => c (x i) z with hCdef
  set M : ℝ := (2 * H) ^ 2 + |B| with hMdef
  have hF : ∀ i, Measurable (F i) := fun i => (hh.sub measurable_const).pow_const 2
  have hC : ∀ i, Measurable (C i) := fun i => hc.comp (measurable_const.prodMk measurable_id)
  have hFb : ∀ i z, |F i z| ≤ M := fun i z => by
    obtain ⟨s0, s1⟩ := sq_bound x hH i z
    rw [abs_of_nonneg s0]; exact s1.trans (le_add_of_nonneg_right (abs_nonneg _))
  have hCb : ∀ i z, |C i z| ≤ M := fun i z => by
    rw [abs_of_nonneg (hc0 _ _)]
    exact (hB _ _).trans ((le_abs_self B).trans (le_add_of_nonneg_left (sq_nonneg _)))
  have hgB := abs_gExp_le hε hFb hCb
  have hprob : ∀ s i, IsProbabilityMeasure (Ker ν F C ε s i) := fun s i =>
    (tilted_facts ν (measurable_gExp hF hC s i) (hgB s i)).1
  set SD := {t | ∃ lam : ℝ, 0 < lam ∧ t = Tref1 x c h ε r lam ν} with hSD
  set SP := {t | ∃ Γ : Fin n → Measure K, (∀ i, IsProbabilityMeasure (Γ i)) ∧
      ((n : ℝ)⁻¹ : EReal) * ∑ i, (((∫ z, c (x i) z ∂(Γ i) : ℝ) : EReal) +
        (ε : EReal) * klRef (Γ i) ν) ≤ (r : EReal) ∧
      t = (n : ℝ)⁻¹ * ∑ i, ∫ z, (h z - h (x i)) ^ 2 ∂(Γ i)} with hSP
  -- weak duality
  have hweak : ∀ t ∈ SP, ∀ d ∈ SD, t ≤ d := by
    rintro t ⟨Γ, hΓ, hbud, rfl⟩ d ⟨lam, hlam, rfl⟩
    exact lagrangian_bound hn x c hc hc0 hB hh hH hε hlam ν hν0 Γ hΓ hbud
  -- Gibbs kernels below the budget are admissible
  have hadm : ∀ s, Gf ν F C ε s ≤ r → EF ν F C ε s ∈ SP := fun s hs => by
    refine ⟨Ker ν F C ε s, hprob s, ?_, rfl⟩
    rw [budget_Ker ν hε hF hC hFb hCb s]
    exact EReal.coe_le_coe_iff.2 hs
  -- `Tref1` in terms of the Gibbs family
  have hT : ∀ lam, 0 < lam → Tref1 x c h ε r lam ν =
      EF ν F C ε (1 / (lam * ε)) - lam * (Gf ν F C ε (1 / (lam * ε)) - r) := fun lam hlam => by
    rw [EF_sub_eq ν hε hlam r]
    unfold Tref1 logZ gExp
    congr 3
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2; ext z; congr 1
    simp only [hFdef, hCdef]
    field_simp
  have h0 : Gf ν F C ε 0 < r := by rw [Gf_zero]; exact hr
  have hSPne : SP.Nonempty := ⟨_, hadm 0 h0.le⟩
  have hSDne : SD.Nonempty := ⟨_, 1, one_pos, rfl⟩
  have hbdd : BddBelow SD := ⟨_, fun d hd => hweak _ (hadm 0 h0.le) d hd⟩
  refine ⟨sInf SD, isGLB_csInf hSDne hbdd, fun t ht => le_csInf hSDne fun d hd => hweak t ht d hd,
    fun u hu => ?_⟩
  -- the attainment argument
  have hV : ∀ lam, 0 < lam → sInf SD ≤ Tref1 x c h ε r lam ν := fun lam hlam =>
    csInf_le hbdd ⟨lam, hlam, rfl⟩
  have hfl := floor_le_Gf ν hε hF hC hFb hCb
  refine le_of_forall_pos_le_add fun η hη => ?_
  by_cases hI : ∃ s, 0 < s ∧ Gf ν F C ε s = r
  · obtain ⟨s, hs, hGs⟩ := hI
    set lam := 1 / (s * ε) with hlamdef
    have hlam : 0 < lam := by positivity
    have hsl : 1 / (lam * ε) = s := by rw [hlamdef]; field_simp
    have := hT lam hlam
    rw [hsl, hGs, sub_self, mul_zero, sub_zero] at this
    have hle := hu (hadm s hGs.le)
    linarith [hV lam hlam]
  · -- the boundary branch: the budget is slack for every `s > 0`
    have hII : ∀ s, 0 < s → Gf ν F C ε s ≤ r := by
      intro s1 hs1
      by_contra hgt
      push Not at hgt
      obtain ⟨s, hsI, hsr⟩ := intermediate_value_Icc hs1.le
        (continuousOn_Gf ν hε hF hC hFb hCb s1) ⟨h0.le, hgt.le⟩
      rcases hsI.1.eq_or_lt with hs0 | hs0
      · rw [← hs0] at hsr; exact (ne_of_lt h0) hsr
      · exact hI ⟨s, hs0, hsr⟩
    have hρr : 0 < r - floorRho ν C ε := by linarith
    set lam := η / (r - floorRho ν C ε) with hlamdef
    have hlam : 0 < lam := div_pos hη hρr
    have hT' := hT lam hlam
    have hle := hu (hadm (1 / (lam * ε)) (hII _ (by positivity)))
    have hfl' := hfl (1 / (lam * ε))
    have hlη : lam * (r - floorRho ν C ε) = η := by rw [hlamdef]; field_simp
    have hmul : lam * floorRho ν C ε ≤ lam * Gf ν F C ε (1 / (lam * ε)) :=
      mul_le_mul_of_nonneg_left hfl' hlam.le
    have hVl := hV lam hlam
    linarith

end StatFormal.Foundations.Strong
