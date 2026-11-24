import StatFormal.Archive.OTFD.Wave16b.Statements
import StatFormal.Archive.RobustEquality.Certificate.Proofs
import StatFormal.Archive.Wave11a.Proofs
import StatFormal.Lib.Tax.Tax

/-!
# Route: paper2 `prop:band` (untrusted)

* Band: the certified groupwise bound `Certificate.group_W_le` (`W₂(h#P̂_s, h#P_s) ≤ √T_s` at the witnessing reference,
  `≤ sqrtT` over the class) and the `W₂` triangle inequality in both directions (the upper half is the certified
  `Certificate.certificate`).
* Selected rule: the event involves no rule; take `G' = G`.
* Deployment: `KernelWitness` ⇒ free-end ball (certified `kernel_iff`), the ball gives `OT_ε ≤ r` (`ballN_subset`, the
  free class has no tax), certified `cs_compose_ball` puts `Q_s` in the free-end ball of radius `(√r_s + √β_s)²`,
  `kernel_iff` back to a `KernelWitness`, and the band at `Q_s`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.OTFD.Wave16b

open StatFormal.RobustEquality.Certificate (KernelWitness centre group_W_le centre_isProb)
open StatFormal.Wave4b (InBall sqrtT nominal RefClass)
open StatFormal.Wave11a (freeClass)
open TauCeti (wassersteinEDist)

lemma ofReal_le_sqrtT {K : Type} [MeasurableSpace K] {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ)
    (ε r lam : ℝ) {N : Set (Measure K)} {ν : Measure K} (hν : ν ∈ N) :
    ENNReal.ofReal (√(StatFormal.RobustEquality.Certificate.Tref1 x c h ε r lam ν)) ≤ sqrtT x c h ε r lam N :=
  le_iSup₂ (f := fun ν (_ : ν ∈ N) => ENNReal.ofReal (√(StatFormal.RobustEquality.Certificate.Tref1 x c h ε r lam ν)))
    ν hν

theorem band : Claims.band := by
  intro K _ n₀ n₁ x₀ x₁ c ε r₀ r₁ N₀ N₁ P₀ P₁ hn₀ hn₁ hε hc hc0 ⟨B, hB⟩ hN₀ hN₁ hP₀ hP₁ h lam₀ lam₁ hh
    ⟨H, hH⟩ hl₀ hl₁
  obtain ⟨hP₀p, ν₀, hν₀, hW₀⟩ := hP₀
  obtain ⟨hP₁p, ν₁, hν₁, hW₁⟩ := hP₁
  obtain ⟨_, hν₀0, _⟩ := hN₀ ν₀ hν₀
  obtain ⟨_, hν₁0, _⟩ := hN₁ ν₁ hν₁
  have g₀ := (group_W_le hn₀ x₀ c hc hc0 hB hh hH hε hl₀ ν₀ P₀ hν₀0 hW₀).trans
    (ofReal_le_sqrtT x₀ c h ε r₀ lam₀ hν₀)
  have g₁ := (group_W_le hn₁ x₁ c hc hc0 hB hh hH hε hl₁ ν₁ P₁ hν₁0 hW₁).trans
    (ofReal_le_sqrtT x₁ c h ε r₁ lam₁ hν₁)
  have hd : Measurable fun z : ℝ × ℝ => edist z.1 z.2 := measurable_edist
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  haveI := centre_isProb hn₀ x₀
  haveI := centre_isProb hn₁ x₁
  set T₀ := sqrtT x₀ c h ε r₀ lam₀ N₀
  set T₁ := sqrtT x₁ c h ε r₁ lam₁ N₁
  have g₀' : wassersteinEDist 2 (P₀.map h) ((centre x₀).map h) ≤ T₀ := by
    rw [TauCeti.wassersteinEDist_comm hd]; exact g₀
  constructor
  · calc wassersteinEDist 2 (P₀.map h) (P₁.map h)
        ≤ wassersteinEDist 2 (P₀.map h) ((centre x₀).map h) +
            wassersteinEDist 2 ((centre x₀).map h) (P₁.map h) :=
          TauCeti.wassersteinEDist_triangle hd hp _ _ _
      _ ≤ T₀ + (nominal x₀ x₁ h + T₁) :=
          add_le_add g₀' ((TauCeti.wassersteinEDist_triangle hd hp _ ((centre x₁).map h) _).trans
            (add_le_add le_rfl g₁))
      _ = nominal x₀ x₁ h + T₀ + T₁ := by ring
  · have g₁' : wassersteinEDist 2 (P₁.map h) ((centre x₁).map h) ≤ T₁ := by
      rw [TauCeti.wassersteinEDist_comm hd]; exact g₁
    calc nominal x₀ x₁ h
        ≤ wassersteinEDist 2 ((centre x₀).map h) (P₀.map h) +
            wassersteinEDist 2 (P₀.map h) ((centre x₁).map h) :=
          TauCeti.wassersteinEDist_triangle hd hp _ _ _
      _ ≤ T₀ + (wassersteinEDist 2 (P₀.map h) (P₁.map h) + T₁) :=
          add_le_add g₀ ((TauCeti.wassersteinEDist_triangle hd hp _ (P₁.map h) _).trans
            (add_le_add le_rfl g₁'))
      _ = wassersteinEDist 2 (P₀.map h) (P₁.map h) + T₀ + T₁ := by ring

theorem band_selected : Claims.band_selected := by
  intro K Ω _ _ P n₀ n₁ x₀ x₁ c ε α r₀ r₁ N₀ N₁ P₀ P₁ hsel lam₀ lam₁ G hn₀ hn₁ hε hc hc0 hcB hN₀ hN₁ hrule
    hG hPG hball
  refine ⟨G, hG, hPG, fun ω hω => ?_⟩
  obtain ⟨hm, hb, hl₀, hl₁⟩ := hrule ω
  exact (band K n₀ n₁ (x₀ ω) (x₁ ω) c ε (r₀ ω) (r₁ ω) N₀ N₁ P₀ P₁ hn₀ hn₁ hε hc hc0 hcB hN₀ hN₁
    (hball ω hω).1 (hball ω hω).2 (hsel ω) (lam₀ ω) (lam₁ ω) hm hb hl₀ hl₁).1

section Deploy
variable {K : Type} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

lemma freeClass_ref : RefClass (freeClass : Set (Measure K)) := by
  intro ν hν
  haveI : IsProbabilityMeasure ν := hν
  exact ⟨inferInstance, by simp, by simp⟩

lemma dist_sq_bdd : ∃ B : ℝ, ∀ a b : K, |dist a b ^ 2| ≤ B := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 (isCompact_univ (X := K)).isBounded
  refine ⟨C ^ 2, fun a b => ?_⟩
  rw [abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ dist_nonneg (hC (mem_univ a) (mem_univ b)) 2

lemma dist_sq_meas (y : K) : Measurable ((fun a b : K => dist a b ^ 2) y) :=
  ((continuous_const.dist continuous_id).pow 2).measurable

/-- `P` in the free-end kernel ball of radius `r`, plus `W₂²(P,Q) ≤ β`, put `Q` in the free-end kernel ball of radius
`(√r + √β)²`. -/
lemma deploy_ball {n : ℕ} (hn : 0 < n) (x : Fin n → K) {ε r β : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) (hβ : 0 ≤ β)
    {P Q : Measure K} [IsProbabilityMeasure Q] (hP : InBall x (fun a b => dist a b ^ 2) ε r freeClass P)
    (hPQ : wassersteinEDist 2 P Q ^ 2 ≤ ENNReal.ofReal β) :
    InBall x (fun a b => dist a b ^ 2) ε ((√r + √β) ^ 2) freeClass Q := by
  obtain ⟨hPp, ν, hν, hW⟩ := hP
  haveI := hPp
  obtain ⟨B, hB⟩ := dist_sq_bdd (K := K)
  have hfin : ∀ ν ∈ (freeClass : Set (Measure K)), IsFiniteMeasure ν := fun ν hν => by
    haveI : IsProbabilityMeasure ν := hν; infer_instance
  have hball := (StatFormal.Wave11a.kernel_iff K n x (fun a b => dist a b ^ 2) ε r freeClass P hn hε
    dist_sq_meas ⟨B, hB⟩ hfin).2 ⟨ν, hν, hW⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ _i : Fin n, (1 : ℝ) / n = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have hset : StatFormal.RobustEquality.SemidualStrong.Setting ε (fun _ : Fin n => (1 : ℝ) / n)
      (fun i => (fun a b : K => dist a b ^ 2) (x i)) :=
    ⟨hε, fun _ => by positivity, hsum, fun i => dist_sq_meas (x i), ⟨B, fun i y => hB _ _⟩⟩
  have hOT := StatFormal.Foundations.Tax.ballN_subset hset hfin hball
  rw [StatFormal.Foundations.Tax.tax_eq_zero_of_mem (𝒩 := freeClass) (fun ν hν => hν) P (show P ∈ freeClass from hPp),
    mul_zero, add_zero] at hOT
  have hQ := StatFormal.Wave11a.cs_compose_ball K n ε (fun _ => (1 : ℝ) / n) x P Q r β hε
    (fun _ => by positivity) hsum hr hβ hOT hPQ
  obtain ⟨ν', hν', hW'⟩ := (StatFormal.Wave11a.kernel_iff K n x (fun a b => dist a b ^ 2) ε ((√r + √β) ^ 2)
    freeClass Q hn hε dist_sq_meas ⟨B, hB⟩ hfin).1 hQ
  exact ⟨inferInstance, ν', hν', hW'⟩

theorem band_deploy : Claims.band_deploy := by
  intro K _ _ _ _ n₀ n₁ x₀ x₁ ε r₀ r₁ β₀ β₁ P₀ P₁ Q₀ Q₁ _ _ hn₀ hn₁ hε hr₀ hr₁ hβ₀ hβ₁ hP₀ hP₁ hW₀ hW₁ h lam₀
    lam₁ hh hb hl₀ hl₁
  obtain ⟨B, hB⟩ := dist_sq_bdd (K := K)
  have hc : Measurable (Function.uncurry fun a b : K => dist a b ^ 2) := (continuous_dist.pow 2).measurable
  exact (band K n₀ n₁ x₀ x₁ (fun a b => dist a b ^ 2) ε _ _ freeClass freeClass Q₀ Q₁ hn₀ hn₁ hε hc
    (fun a b => by positivity) ⟨B, fun a b => (le_abs_self _).trans (hB a b)⟩ freeClass_ref freeClass_ref
    (deploy_ball hn₀ x₀ hε hr₀ hβ₀ hP₀ hW₀) (deploy_ball hn₁ x₁ hε hr₁ hβ₁ hP₁ hW₁) h lam₀ lam₁ hh hb hl₀ hl₁).1

end Deploy

end StatFormal.OTFD.Wave16b
