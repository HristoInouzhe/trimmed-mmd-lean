import StatFormal.Wave30tz.RouteHoeff
import StatFormal.Wave30tz.RouteElem

/-!
# Wave 30tz route: Lemmas 5 and 6 (`eq:betbounds`) — untrusted

The pair statistics `Z_k = pairStat`, the fractions `λ_k = fracAt` and the conditional means
`Δ_k = condMean` of an admissible fitting rule (`IsFitRule`) and admissible fractions
(`IsFracRule`) are functions of the coordinates `predSet (k+1)`, `predSet k`, `predSet k`
(Wave 30tv `predSet`); `hoeff_frac` is the conditional Hoeffding lemma `hoeff_cond` in these
terms. Auxiliary lemmas are in `StatFormal.Wave30tz.Bet`.

* `strict_null_core` / `strict_null_route` (Lemma 6): with `s = 2ζ/λ̄`, the factors
  `F_k = e^{sλ_k(Z_k − α)}` satisfy `E[V F_k] ≤ E[V]` (`hoeff_frac` with `r = sλ_k`, then
  `Δ_k − α ≤ −ζ` and `λ_k ≤ λ̄`), and `K_t ≤ e^{Σ λ_k(Z_k−α)}` (`1 + u ≤ eᵘ`), so
  `{K_t ≥ 1/δ} ⊆ {∏ F_k ≥ e^{sL}}`; `prod_ville` at `e^{sL}`.
* `bet_power_core` / `bet_power_route` (Lemma 5): with `x = Nλϱ − c_a N λ̄²(1+α)² − L > 0`
  and `s = x/(N λ̄²)`, the factors `F_k = e^{−sλ_k(Z_k − Δ_k) − s²λ_k²/2}` satisfy
  `E[V F_k] ≤ E[V]` (`hoeff_frac` with `r = −sλ_k`); on `E ∩ {K_N < 1/δ}` the Taylor step
  `log_lower` gives `∏_{k<N} F_k ≥ e^{x²/(2Nλ̄²)}`; `prod_ville` at that level.
* `strict_null_frac_route`, `bet_power_frac_route`: the fractions of `eq:fractions` (`lamHi`,
  `lamLo`), from the above; the second conjunct of `bet_power_frac` is `epsN_small_route`
  (RouteElem).
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.Wave30tz

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tp

/-! The auxiliary lemmas live in `StatFormal.Wave30tz.Bet`; the four targets in `StatFormal.Wave30tz`. -/
namespace Bet

section Infra

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {n m N : ℕ}
variable {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)}
  {B : Fin N → Finset (Fin m)} {g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ}
  {lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}

scoped instance sampleLaw_isProb (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (sampleLaw P Q n m) := by
  unfold sampleLaw; infer_instance

lemma fit_measurable (hg : IsFitRule lx ly bat g) (k : Fin N) :
    Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => g (bat k) p.1.1 p.1.2 p.2 :=
  (hg k).1.comp (((measurable_const (a := ())).prodMk measurable_fst).prodMk measurable_snd)

lemma fit_mem (hg : IsFitRule lx ly bat g) (k : Fin N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : 𝒳) :
    g (bat k) x y z ∈ Icc (0 : ℝ) 1 :=
  (hg k).2.1 () x y z

lemma fit_eq (hg : IsFitRule lx ly bat g) (k : Fin N) {ω ω' : (Fin n → 𝒳) × (Fin m → 𝒳)}
    (h : ∀ j ∈ predSet lx ly bat A B k, coord j ω = coord j ω') : g (bat k) ω.1 ω.2 = g (bat k) ω'.1 ω'.2 :=
  (hg k).2.2 () ω.1 ω'.1 ω.2 ω'.2
    (fun i hi => h (Sum.inl i) (before_subset_predSet k (show Sum.inl i ∈ before lx ly (bat k) from hi)))
    (fun j hj => h (Sum.inr j) (before_subset_predSet k (show Sum.inr j ∈ before lx ly (bat k) from hj)))

lemma fit_depOn (hg : IsFitRule lx ly bat g) (k : Fin N) :
    DepOn (predSet lx ly bat A B k) fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => g (bat k) ω.1 ω.2 :=
  fun _ _ h => fit_eq hg k h

lemma pairStat_measurable (hg : IsFitRule lx ly bat g) (k : Fin N) :
    Measurable fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => pairStat g bat A B ω.1 ω.2 k := by
  have hGm := fit_measurable hg k
  change Measurable fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => pairZ (g (bat k) ω.1 ω.2) A B ω.1 ω.2 k
  unfold pairZ blockMean
  refine Measurable.sub (Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _)
    (Measurable.div_const (Finset.measurable_sum _ fun j _ => ?_) _)
  · exact hGm.comp (measurable_id.prodMk ((measurable_pi_apply i).comp measurable_fst))
  · exact hGm.comp (measurable_id.prodMk ((measurable_pi_apply j).comp measurable_snd))

lemma pairStat_mem (hpair : IsBatchPairing lx ly bat A B) (hg : IsFitRule lx ly bat g) (k : Fin N)
    (x : Fin n → 𝒳) (y : Fin m → 𝒳) : pairStat g bat A B x y k ∈ Icc (-1 : ℝ) 1 :=
  pairZ_mem (fit_mem hg k x y) hpair.1 k x y

lemma pairStat_depOn (hpair : IsBatchPairing lx ly bat A B) (hg : IsFitRule lx ly bat g) (k : Fin N) :
    DepOn (predSet lx ly bat A B (k + 1)) fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => pairStat g bat A B ω.1 ω.2 k := by
  intro ω ω' h
  change pairZ (g (bat k) ω.1 ω.2) A B ω.1 ω.2 k = pairZ (g (bat k) ω'.1 ω'.2) A B ω'.1 ω'.2 k
  rw [fit_eq (A := A) (B := B) hg k fun j hj => h j (predSet_mono hpair.2.1 (Nat.le_succ _) hj)]
  exact pairZ_congr k
    (fun i hi => h (Sum.inl i) (blockSet_subset_predSet_succ k (Or.inl ⟨i, by exact_mod_cast hi, rfl⟩)))
    (fun j hj => h (Sum.inr j) (blockSet_subset_predSet_succ k (Or.inr ⟨j, by exact_mod_cast hj, rfl⟩)))

lemma frac_measurable {α c : ℝ} (hg : IsFitRule lx ly bat g) (hlam : IsFracRule lx ly bat α c lam) (k : Fin N) :
    Measurable fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => fracAt lam g bat A B ω.1 ω.2 k := by
  have hZ : Measurable fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => past (pairStat g bat A B ω.1 ω.2) k :=
    Measurable.of_eval fun i => pairStat_measurable hg (Fin.castLE k.isLt.le i)
  exact (hlam k).1.comp (((measurable_const (a := ())).prodMk measurable_id).prodMk hZ)

lemma frac_mem {α c : ℝ} (hlam : IsFracRule lx ly bat α c lam) (k : Fin N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    0 ≤ fracAt lam g bat A B x y k ∧ fracAt lam g bat A B x y k ≤ c / (1 + α) :=
  (hlam k).2.1 () x y _

lemma frac_depOn {α c : ℝ} (hpair : IsBatchPairing lx ly bat A B) (hg : IsFitRule lx ly bat g)
    (hlam : IsFracRule lx ly bat α c lam) (k : Fin N) :
    DepOn (predSet lx ly bat A B k) fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => fracAt lam g bat A B ω.1 ω.2 k := by
  intro ω ω' h
  change lam k ω.1 ω.2 (past (pairStat g bat A B ω.1 ω.2) k) = lam k ω'.1 ω'.2 (past (pairStat g bat A B ω'.1 ω'.2) k)
  have e : lam k ω.1 ω.2 = lam k ω'.1 ω'.2 := (hlam k).2.2 () ω.1 ω'.1 ω.2 ω'.2
    (fun i hi => h (Sum.inl i) (before_subset_predSet k (show Sum.inl i ∈ before lx ly (bat k) from hi)))
    (fun j hj => h (Sum.inr j) (before_subset_predSet k (show Sum.inr j ∈ before lx ly (bat k) from hj)))
  rw [e]
  congr 1
  funext i
  simp only [past]
  refine pairStat_depOn hpair hg _ ω ω' fun j hj => h j (predSet_mono hpair.2.1 ?_ hj)
  have := i.isLt
  simp only [Fin.val_castLE]
  omega

lemma condMean_measurable (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hg : IsFitRule lx ly bat g) (k : Fin N) :
    Measurable fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => condMean P Q g bat ω.1 ω.2 k :=
  (((fit_measurable hg k).stronglyMeasurable.integral_prod_right' (ν := P)).measurable).sub
    (((fit_measurable hg k).stronglyMeasurable.integral_prod_right' (ν := Q)).measurable)

lemma condMean_depOn (P Q : Measure 𝒳) (hg : IsFitRule lx ly bat g) (k : Fin N) :
    DepOn (predSet lx ly bat A B k) fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => condMean P Q g bat ω.1 ω.2 k := by
  intro ω ω' h
  change (∫ z, g (bat k) ω.1 ω.2 z ∂P) - ∫ z, g (bat k) ω.1 ω.2 z ∂Q =
    (∫ z, g (bat k) ω'.1 ω'.2 z ∂P) - ∫ z, g (bat k) ω'.1 ω'.2 z ∂Q
  rw [fit_eq hg k h]

lemma condMean_le_tv (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hg : IsFitRule lx ly bat g) (k : Fin N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    condMean P Q g bat x y k ≤ StatFormal.Distances.tvDist P Q := by
  have hm : Measurable fun z => g (bat k) x y z :=
    (fit_measurable hg k).comp ((measurable_const : Measurable fun _ : 𝒳 => (x, y)).prodMk measurable_id)
  exact delta_le_tv P Q hm (fit_mem hg k x y)

lemma condMean_mem (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hg : IsFitRule lx ly bat g) (k : Fin N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    condMean P Q g bat x y k ∈ Icc (-1 : ℝ) 1 := by
  have hm : Measurable fun z => g (bat k) x y z :=
    (fit_measurable hg k).comp ((measurable_const : Measurable fun _ : 𝒳 => (x, y)).prodMk measurable_id)
  have h1 := integral_mem_Icc P hm (fit_mem hg k x y)
  have h2 := integral_mem_Icc Q hm (fit_mem hg k x y)
  change (∫ z, g (bat k) x y z ∂P) - ∫ z, g (bat k) x y z ∂Q ∈ Icc (-1 : ℝ) 1
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The conditional Hoeffding lemma `hoeff_cond` for the pair statistic and the conditional mean of an admissible rule. -/
theorem hoeff_frac (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hpair : IsBatchPairing lx ly bat A B) (hg : IsFitRule lx ly bat g) (k : Fin N)
    {V r : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ} (hVm : Measurable V) (hVd : DepOn (predSet lx ly bat A B k) V)
    (hV0 : ∀ ω, 0 ≤ V ω) {K : ℝ} (hVb : ∀ ω, V ω ≤ K)
    (hrm : Measurable r) (hrd : DepOn (predSet lx ly bat A B k) r) {R : ℝ} (hrb : ∀ ω, |r ω| ≤ R) :
    ∫ ω, V ω * Real.exp (r ω * (pairStat g bat A B ω.1 ω.2 k - condMean P Q g bat ω.1 ω.2 k)) ∂(sampleLaw P Q n m) ≤
      ∫ ω, V ω * Real.exp (r ω ^ 2 / 2) ∂(sampleLaw P Q n m) :=
  hoeff_cond P Q hpair k (G := fun ω t => g (bat k) ω.1 ω.2 t) (fit_measurable hg k) (fit_depOn hg k)
    (fun ω t => fit_mem hg k ω.1 ω.2 t) hVm hVd hV0 hVb hrm hrd hrb

end Infra

/-! ### Lemma 6: strict nulls -/

section Lemma6

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {n m N : ℕ}
variable {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)}
  {B : Fin N → Finset (Fin m)} {g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ}
  {lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}

omit [MeasurableSpace 𝒳] in
/-- The rejection event in terms of `pairStat`, `fracAt`. -/
lemma rejects_iff {α δ : ℝ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    rejects lam g bat A B α δ x y ↔ ∃ t ≤ N, 1 / δ ≤ ∏ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t),
      (1 + fracAt lam g bat A B x y k * (pairStat g bat A B x y k - α)) := Iff.rfl

/-- Lemma 6 for `λ̄ > 0`, as a real-valued bound. -/
theorem strict_null_core (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hpair : IsBatchPairing lx ly bat A B) {α δ c hi ζ : ℝ} (hα : 0 ≤ α) (hδ0 : 0 < δ) (hc1 : c ≤ 1)
    (hg : IsFitRule lx ly bat g) (hlam : IsFracRule lx ly bat α c lam)
    (hhi : ∀ (k : Fin N) x y z, lam k x y z ≤ hi) (hζ : 0 < ζ)
    (hTV : StatFormal.Distances.tvDist P Q ≤ α - ζ) (hhi0 : 0 < hi) :
    (sampleLaw P Q n m).real {ω | rejects lam g bat A B α δ ω.1 ω.2} ≤
      Real.exp (-(2 * ζ * Real.log (1 / δ) / hi)) := by
  set μ := sampleLaw P Q n m with hμ
  set L := Real.log (1 / δ) with hLdef
  set s := 2 * ζ / hi with hsdef
  have hs : 0 < s := by positivity
  have hshi : s * hi = 2 * ζ := by rw [hsdef]; field_simp
  have h1α : 0 < 1 + α := by linarith
  have hcap : c / (1 + α) ≤ 1 := by
    rw [div_le_one h1α]; linarith
  set Z : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => pairStat g bat A B ω.1 ω.2 k with hZdef
  set Λ : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => fracAt lam g bat A B ω.1 ω.2 k with hΛdef
  set Δ : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => condMean P Q g bat ω.1 ω.2 k with hΔdef
  set F : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => Real.exp (s * (Λ k ω * (Z k ω - α))) with hFdef
  have hZm : ∀ k, Measurable (Z k) := fun k => pairStat_measurable hg k
  have hΛm : ∀ k, Measurable (Λ k) := fun k => frac_measurable hg hlam k
  have hΔm : ∀ k, Measurable (Δ k) := fun k => condMean_measurable P Q hg k
  have hΛb : ∀ k ω, 0 ≤ Λ k ω ∧ Λ k ω ≤ c / (1 + α) := fun k ω => frac_mem hlam k ω.1 ω.2
  have hΛhi : ∀ k ω, Λ k ω ≤ hi := fun k ω => hhi k _ _ _
  have hZb : ∀ k ω, Z k ω ∈ Icc (-1 : ℝ) 1 := fun k ω => pairStat_mem hpair hg k ω.1 ω.2
  have hΔα : ∀ k ω, Δ k ω - α ≤ -ζ := fun k ω => by
    have := condMean_le_tv P Q hg k ω.1 ω.2
    simp only [hΔdef]; linarith
  -- `|λ_k (Z_k − α)| ≤ 1`
  have hu : ∀ k ω, |Λ k ω * (Z k ω - α)| ≤ 1 := fun k ω => by
    have hl := hΛb k ω
    have hz := hZb k ω
    have hcapk : Λ k ω * (1 + α) ≤ c := by
      have := mul_le_mul_of_nonneg_right hl.2 h1α.le
      rwa [div_mul_cancel₀ c h1α.ne'] at this
    rw [abs_mul, abs_of_nonneg hl.1]
    have : |Z k ω - α| ≤ 1 + α := by rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
    calc Λ k ω * |Z k ω - α| ≤ Λ k ω * (1 + α) := mul_le_mul_of_nonneg_left this hl.1
      _ ≤ c := hcapk
      _ ≤ 1 := hc1
  have hFm : ∀ k, Measurable (F k) := fun k =>
    Real.measurable_exp.comp (measurable_const.mul ((hΛm k).mul ((hZm k).sub_const α)))
  have hFd : ∀ k : Fin N, DepOn (predSet lx ly bat A B (k + 1)) (F k) := fun k ω ω' h => by
    have e1 : Λ k ω = Λ k ω' :=
      frac_depOn hpair hg hlam k ω ω' fun j hj => h j (predSet_mono hpair.2.1 (Nat.le_succ _) hj)
    have e2 : Z k ω = Z k ω' := pairStat_depOn hpair hg k ω ω' h
    simp only [hFdef]
    rw [e1, e2]
  have hFb : ∀ k ω, 0 ≤ F k ω ∧ F k ω ≤ Real.exp s := fun k ω => by
    refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 ?_⟩
    have := (abs_le.1 (hu k ω)).2
    calc s * (Λ k ω * (Z k ω - α)) ≤ s * 1 := mul_le_mul_of_nonneg_left this hs.le
      _ = s := mul_one s
  -- the factors are supermartingale factors: `E[V F_k] ≤ E[V]`
  have hmean : ∀ k : Fin N, ∀ V : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ, Measurable V →
      DepOn (predSet lx ly bat A B k) V → (∀ ω, 0 ≤ V ω) → (∃ C, ∀ ω, V ω ≤ C) →
      ∫ ω, V ω * F k ω ∂μ ≤ ∫ ω, V ω ∂μ := by
    intro k V hVm hVd hV0 ⟨C, hC⟩
    set V' : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun ω => V ω * Real.exp (s * (Λ k ω * (Δ k ω - α))) with hV'def
    set r : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun ω => s * Λ k ω with hrdef
    have hΛd : DepOn (predSet lx ly bat A B k) (Λ k) := frac_depOn hpair hg hlam k
    have hΔd : DepOn (predSet lx ly bat A B k) (Δ k) := condMean_depOn P Q hg k
    have hV'm : Measurable V' :=
      hVm.mul (Real.measurable_exp.comp (measurable_const.mul ((hΛm k).mul ((hΔm k).sub_const α))))
    have hV'd : DepOn (predSet lx ly bat A B k) V' := fun ω ω' h => by
      have e0 : V ω = V ω' := hVd ω ω' h
      have e1 : Λ k ω = Λ k ω' := hΛd ω ω' h
      have e2 : Δ k ω = Δ k ω' := hΔd ω ω' h
      simp only [hV'def]; rw [e0, e1, e2]
    have hexp_le : ∀ ω, s * (Λ k ω * (Δ k ω - α)) ≤ 0 := fun ω =>
      mul_nonpos_of_nonneg_of_nonpos hs.le
        (mul_nonpos_of_nonneg_of_nonpos (hΛb k ω).1 (by linarith [hΔα k ω]))
    have hV'0 : ∀ ω, 0 ≤ V' ω := fun ω => mul_nonneg (hV0 ω) (Real.exp_pos _).le
    have hV'b : ∀ ω, V' ω ≤ C := fun ω => by
      calc V' ω ≤ V ω * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (hexp_le ω)) (hV0 ω)
        _ ≤ C := by rw [mul_one]; exact hC ω
    have hrm : Measurable r := measurable_const.mul (hΛm k)
    have hrd : DepOn (predSet lx ly bat A B k) r := fun ω ω' h => by
      have e1 : Λ k ω = Λ k ω' := hΛd ω ω' h
      simp only [hrdef]; rw [e1]
    have hrb : ∀ ω, |r ω| ≤ s := fun ω => by
      simp only [hrdef]
      rw [abs_of_nonneg (mul_nonneg hs.le (hΛb k ω).1)]
      calc s * Λ k ω ≤ s * 1 := mul_le_mul_of_nonneg_left ((hΛb k ω).2.trans hcap) hs.le
        _ = s := mul_one s
    have key := hoeff_frac P Q hpair hg k hV'm hV'd hV'0 hV'b hrm hrd hrb
    have hpt1 : ∀ ω, V ω * F k ω =
        V' ω * Real.exp (r ω * (pairStat g bat A B ω.1 ω.2 k - condMean P Q g bat ω.1 ω.2 k)) := fun ω => by
      change V ω * Real.exp (s * (Λ k ω * (Z k ω - α))) =
        V ω * Real.exp (s * (Λ k ω * (Δ k ω - α))) * Real.exp (s * Λ k ω * (Z k ω - Δ k ω))
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    have hpt2 : ∀ ω, V' ω * Real.exp (r ω ^ 2 / 2) ≤ V ω := fun ω => by
      change V ω * Real.exp (s * (Λ k ω * (Δ k ω - α))) * Real.exp ((s * Λ k ω) ^ 2 / 2) ≤ V ω
      rw [mul_assoc, ← Real.exp_add]
      have hsl : 0 ≤ s * Λ k ω := mul_nonneg hs.le (hΛb k ω).1
      have h1 : s * Λ k ω * (Δ k ω - α + ζ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hsl (by linarith [hΔα k ω])
      have h2 : s * Λ k ω * (s * (Λ k ω - hi)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hsl (mul_nonpos_of_nonneg_of_nonpos hs.le (by linarith [hΛhi k ω]))
      have h3 : s * Λ k ω * (s * hi) = s * Λ k ω * (2 * ζ) := by rw [hshi]
      have hneg : s * (Λ k ω * (Δ k ω - α)) + (s * Λ k ω) ^ 2 / 2 ≤ 0 := by nlinarith [h1, h2, h3]
      calc V ω * Real.exp (s * (Λ k ω * (Δ k ω - α)) + (s * Λ k ω) ^ 2 / 2) ≤ V ω * 1 :=
            mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 hneg) (hV0 ω)
        _ = V ω := mul_one _
    have hVi : Integrable V μ :=
      integrable_of_abs_le hVm C fun ω => by rw [abs_of_nonneg (hV0 ω)]; exact hC ω
    have hRi : Integrable (fun ω => V' ω * Real.exp (r ω ^ 2 / 2)) μ :=
      integrable_of_abs_le (hV'm.mul (Real.measurable_exp.comp ((hrm.pow_const 2).div_const 2))) C fun ω => by
        rw [abs_of_nonneg (mul_nonneg (hV'0 ω) (Real.exp_pos _).le)]
        exact (hpt2 ω).trans (hC ω)
    calc ∫ ω, V ω * F k ω ∂μ =
          ∫ ω, V' ω * Real.exp (r ω * (pairStat g bat A B ω.1 ω.2 k - condMean P Q g bat ω.1 ω.2 k)) ∂μ :=
          integral_congr_ae (ae_of_all _ hpt1)
      _ ≤ ∫ ω, V' ω * Real.exp (r ω ^ 2 / 2) ∂μ := key
      _ ≤ ∫ ω, V ω ∂μ := integral_mono hRi hVi hpt2
  -- the rejection event is inside `{∃ t ≤ N, ∏_{k<t} F_k ≥ e^{sL}}`
  have hfac : ∀ k ω, 0 ≤ 1 + Λ k ω * (Z k ω - α) := fun k ω => by linarith [(abs_le.1 (hu k ω)).1]
  have hsub : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | rejects lam g bat A B α δ ω.1 ω.2} ⊆
      {ω | ∃ t ≤ N, Real.exp (s * L) ≤ ∏ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), F k ω} := by
    intro ω hω
    obtain ⟨t, ht, hK⟩ := (rejects_iff ω.1 ω.2).1 hω
    refine ⟨t, ht, ?_⟩
    set S := Finset.univ.filter (fun k : Fin N => (k : ℕ) < t) with hS
    have hK' : 1 / δ ≤ ∏ k ∈ S, (1 + Λ k ω * (Z k ω - α)) := hK
    have hle : ∏ k ∈ S, (1 + Λ k ω * (Z k ω - α)) ≤ Real.exp (∑ k ∈ S, Λ k ω * (Z k ω - α)) := by
      rw [Real.exp_sum]
      exact Finset.prod_le_prod₀ (fun k _ => hfac k ω)
        (fun k _ => by linarith [Real.add_one_le_exp (Λ k ω * (Z k ω - α))])
    have hL : L ≤ ∑ k ∈ S, Λ k ω * (Z k ω - α) := by
      rw [← Real.exp_le_exp, hLdef, Real.exp_log (by positivity)]
      linarith
    calc Real.exp (s * L) ≤ Real.exp (s * ∑ k ∈ S, Λ k ω * (Z k ω - α)) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hL hs.le)
      _ = ∏ k ∈ S, F k ω := by rw [Finset.mul_sum, Real.exp_sum]
  have hV := prod_ville P Q hpair.2.1 F hFm hFd hFb hmean (Real.exp_pos (s * L))
  have hA : 0 < Real.exp (s * L) := Real.exp_pos _
  have hsL : s * L = 2 * ζ * L / hi := by rw [hsdef]; ring
  calc μ.real {ω | rejects lam g bat A B α δ ω.1 ω.2} ≤
        μ.real {ω | ∃ t ≤ N, Real.exp (s * L) ≤ ∏ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), F k ω} :=
        measureReal_mono hsub
    _ ≤ 1 / Real.exp (s * L) := by rw [le_div_iff₀ hA, mul_comm]; exact hV
    _ = Real.exp (-(2 * ζ * L / hi)) := by rw [one_div, ← Real.exp_neg, hsL]

/-- **Lemma 6** (`eq:betbounds`, second bound). -/
theorem _root_.StatFormal.Wave30tz.strict_null_route : Claims.strict_null := by
  intro 𝒳 _ P Q _ _ n m N lx ly bat A B α δ c hi ζ g lam hpair hα hδ0 hδ1 hc0 hc1 hg hlam hhi hζ hTV
  rcases le_or_gt hi 0 with hhi0 | hhi0
  · have hL : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
    have h1 : 1 ≤ Real.exp (-(2 * ζ * Real.log (1 / δ) / hi)) := by
      refine Real.one_le_exp ?_
      have : 2 * ζ * Real.log (1 / δ) / hi ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) hhi0
      linarith
    calc sampleLaw P Q n m {ω | rejects lam g bat A B α δ ω.1 ω.2} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h1
  · rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (strict_null_core P Q hpair hα hδ0 hc1 hg hlam hhi hζ hTV hhi0)

end Lemma6

/-! ### Lemma 5: power of the betting test -/

section Lemma5

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {n m N : ℕ}
variable {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)}
  {B : Fin N → Finset (Fin m)} {g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ}
  {lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}

/-- Lemma 5 when `x = Nλϱ − c_a N λ̄²(1+α)² − L > 0`, as a real-valued bound. -/
theorem bet_power_core (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hpair : IsBatchPairing lx ly bat A B) {α δ c lo hi a ρ : ℝ} (hα : 0 ≤ α) (hc1 : c ≤ 1)
    (hg : IsFitRule lx ly bat g) (hlam : IsFracRule lx ly bat α c lam)
    (hhi : ∀ (k : Fin N) x y z, lam k x y z ≤ hi) (ha : hi * (1 + α) ≤ a) (ha1 : a < 1) (hρ : 0 < ρ) {E : Set ((Fin n → 𝒳) × (Fin m → 𝒳))}
    (hE : ∀ ω ∈ E, ∀ k : Fin N, lo ≤ fracAt lam g bat A B ω.1 ω.2 k ∧ α + ρ ≤ condMean P Q g bat ω.1 ω.2 k)
    (hN : 1 ≤ N) (hhi0 : 0 < hi) {x : ℝ}
    (hxdef : x = N * lo * ρ - 1 / (2 * (1 - a) ^ 2) * N * hi ^ 2 * (1 + α) ^ 2 - Real.log (1 / δ)) (hx : 0 < x) :
    (sampleLaw P Q n m).real (E ∩ {ω | ¬ rejects lam g bat A B α δ ω.1 ω.2}) ≤
      Real.exp (-(x ^ 2 / (2 * N * hi ^ 2))) := by
  set μ := sampleLaw P Q n m with hμ
  set L := Real.log (1 / δ) with hLdef
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : (0 : ℝ) < N * hi ^ 2 := by positivity
  set s := x / (N * hi ^ 2) with hsdef
  have hs : 0 < s := div_pos hx hD
  have h1α : 0 < 1 + α := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le (mul_pos hhi0 h1α) ha
  have hcap : c / (1 + α) ≤ 1 := by
    rw [div_le_one h1α]; linarith
  set Z : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => pairStat g bat A B ω.1 ω.2 k with hZdef
  set Λ : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => fracAt lam g bat A B ω.1 ω.2 k with hΛdef
  set Δ : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => condMean P Q g bat ω.1 ω.2 k with hΔdef
  set F : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ :=
    fun k ω => Real.exp (-(s * Λ k ω) * (Z k ω - Δ k ω) - (-(s * Λ k ω)) ^ 2 / 2) with hFdef
  have hZm : ∀ k, Measurable (Z k) := fun k => pairStat_measurable hg k
  have hΛm : ∀ k, Measurable (Λ k) := fun k => frac_measurable hg hlam k
  have hΔm : ∀ k, Measurable (Δ k) := fun k => condMean_measurable P Q hg k
  have hΛb : ∀ k ω, 0 ≤ Λ k ω ∧ Λ k ω ≤ c / (1 + α) := fun k ω => frac_mem hlam k ω.1 ω.2
  have hΛ1 : ∀ k ω, Λ k ω ≤ 1 := fun k ω => (hΛb k ω).2.trans hcap
  have hΛhi : ∀ k ω, Λ k ω ≤ hi := fun k ω => hhi k _ _ _
  have hZb : ∀ k ω, Z k ω ∈ Icc (-1 : ℝ) 1 := fun k ω => pairStat_mem hpair hg k ω.1 ω.2
  have hΔb : ∀ k ω, Δ k ω ∈ Icc (-1 : ℝ) 1 := fun k ω => condMean_mem P Q hg k ω.1 ω.2
  have hZΔ : ∀ k ω, |Z k ω - Δ k ω| ≤ 2 := fun k ω => by
    rw [abs_le]; constructor <;> linarith [(hZb k ω).1, (hZb k ω).2, (hΔb k ω).1, (hΔb k ω).2]
  have hFm : ∀ k, Measurable (F k) := fun k =>
    Real.measurable_exp.comp (((measurable_const.mul (hΛm k)).neg.mul ((hZm k).sub (hΔm k))).sub
      (((measurable_const.mul (hΛm k)).neg.pow_const 2).div_const 2))
  have hFd : ∀ k : Fin N, DepOn (predSet lx ly bat A B (k + 1)) (F k) := fun k ω ω' h => by
    have hh : ∀ j ∈ predSet lx ly bat A B k, coord j ω = coord j ω' :=
      fun j hj => h j (predSet_mono hpair.2.1 (Nat.le_succ _) hj)
    have e1 : Λ k ω = Λ k ω' := frac_depOn hpair hg hlam k ω ω' hh
    have e2 : Z k ω = Z k ω' := pairStat_depOn hpair hg k ω ω' h
    have e3 : Δ k ω = Δ k ω' := condMean_depOn P Q hg k ω ω' hh
    simp only [hFdef]
    rw [e1, e2, e3]
  have hFb : ∀ k ω, 0 ≤ F k ω ∧ F k ω ≤ Real.exp (s * 1 * 2) := fun k ω => by
    refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 ?_⟩
    have hsl : 0 ≤ s * Λ k ω := mul_nonneg hs.le (hΛb k ω).1
    have h1 : -(s * Λ k ω) * (Z k ω - Δ k ω) ≤ s * 1 * 2 := by
      calc -(s * Λ k ω) * (Z k ω - Δ k ω) ≤ |-(s * Λ k ω) * (Z k ω - Δ k ω)| := le_abs_self _
        _ = s * Λ k ω * |Z k ω - Δ k ω| := by rw [abs_mul, abs_neg, abs_of_nonneg hsl]
        _ ≤ s * 1 * 2 := mul_le_mul (mul_le_mul_of_nonneg_left (hΛ1 k ω) hs.le) (hZΔ k ω) (abs_nonneg _)
            (by positivity)
    have h2 : 0 ≤ (-(s * Λ k ω)) ^ 2 / 2 := by positivity
    linarith
  -- the factors are supermartingale factors: `E[V F_k] ≤ E[V]`
  have hmean : ∀ k : Fin N, ∀ V : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ, Measurable V →
      DepOn (predSet lx ly bat A B k) V → (∀ ω, 0 ≤ V ω) → (∃ C, ∀ ω, V ω ≤ C) →
      ∫ ω, V ω * F k ω ∂μ ≤ ∫ ω, V ω ∂μ := by
    intro k V hVm hVd hV0 ⟨C, hC⟩
    set r : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun ω => -(s * Λ k ω) with hrdef
    set V' : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun ω => V ω * Real.exp (-(r ω ^ 2 / 2)) with hV'def
    have hΛd : DepOn (predSet lx ly bat A B k) (Λ k) := frac_depOn hpair hg hlam k
    have hrm : Measurable r := (measurable_const.mul (hΛm k)).neg
    have hrd : DepOn (predSet lx ly bat A B k) r := fun ω ω' h => by
      have e1 : Λ k ω = Λ k ω' := hΛd ω ω' h
      simp only [hrdef]; rw [e1]
    have hrb : ∀ ω, |r ω| ≤ s := fun ω => by
      simp only [hrdef]
      rw [abs_neg, abs_of_nonneg (mul_nonneg hs.le (hΛb k ω).1)]
      calc s * Λ k ω ≤ s * 1 := mul_le_mul_of_nonneg_left (hΛ1 k ω) hs.le
        _ = s := mul_one s
    have hV'm : Measurable V' := hVm.mul (Real.measurable_exp.comp ((hrm.pow_const 2).div_const 2).neg)
    have hV'd : DepOn (predSet lx ly bat A B k) V' := fun ω ω' h => by
      have e0 : V ω = V ω' := hVd ω ω' h
      have e1 : r ω = r ω' := hrd ω ω' h
      simp only [hV'def]; rw [e0, e1]
    have hV'0 : ∀ ω, 0 ≤ V' ω := fun ω => mul_nonneg (hV0 ω) (Real.exp_pos _).le
    have hV'b : ∀ ω, V' ω ≤ C := fun ω => by
      have : -(r ω ^ 2 / 2) ≤ 0 := by have := sq_nonneg (r ω); linarith
      calc V' ω ≤ V ω * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 this) (hV0 ω)
        _ ≤ C := by rw [mul_one]; exact hC ω
    have key := hoeff_frac P Q hpair hg k hV'm hV'd hV'0 hV'b hrm hrd hrb
    have hpt1 : ∀ ω, V ω * F k ω =
        V' ω * Real.exp (r ω * (pairStat g bat A B ω.1 ω.2 k - condMean P Q g bat ω.1 ω.2 k)) := fun ω => by
      change V ω * Real.exp (r ω * (Z k ω - Δ k ω) - r ω ^ 2 / 2) =
        V ω * Real.exp (-(r ω ^ 2 / 2)) * Real.exp (r ω * (Z k ω - Δ k ω))
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    have hpt2 : ∀ ω, V' ω * Real.exp (r ω ^ 2 / 2) = V ω := fun ω => by
      change V ω * Real.exp (-(r ω ^ 2 / 2)) * Real.exp (r ω ^ 2 / 2) = V ω
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    calc ∫ ω, V ω * F k ω ∂μ =
          ∫ ω, V' ω * Real.exp (r ω * (pairStat g bat A B ω.1 ω.2 k - condMean P Q g bat ω.1 ω.2 k)) ∂μ :=
          integral_congr_ae (ae_of_all _ hpt1)
      _ ≤ ∫ ω, V' ω * Real.exp (r ω ^ 2 / 2) ∂μ := key
      _ = ∫ ω, V ω ∂μ := integral_congr_ae (ae_of_all _ hpt2)
  -- on `E ∩ {K_N < 1/δ}`, `∏_{k<N} F_k ≥ e^{x²/(2Nλ̄²)}`
  set Cc : ℝ := 1 / (2 * (1 - a) ^ 2) * hi ^ 2 * (1 + α) ^ 2 with hCc
  set w : ℝ := s * lo * ρ - s * Cc - s ^ 2 * hi ^ 2 / 2 with hw
  have hS : Finset.univ.filter (fun k : Fin N => (k : ℕ) < N) = Finset.univ :=
    Finset.filter_true_of_mem fun k _ => k.isLt
  have hsub : E ∩ {ω | ¬ rejects lam g bat A B α δ ω.1 ω.2} ⊆
      {ω | ∃ t ≤ N, Real.exp (x ^ 2 / (2 * N * hi ^ 2)) ≤
        ∏ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), F k ω} := by
    rintro ω ⟨hωE, hωR⟩
    refine ⟨N, le_rfl, ?_⟩
    rw [hS]
    have hKN : ∏ k, (1 + Λ k ω * (Z k ω - α)) < 1 / δ := by
      by_contra hcon
      push Not at hcon
      exact hωR ((rejects_iff ω.1 ω.2).2 ⟨N, le_rfl, by rw [hS]; exact hcon⟩)
    have hlow : ∀ k, -a ≤ Λ k ω * (Z k ω - α) := fun k => by
      have hl := hΛb k ω
      have hz := hZb k ω
      have h1 : Λ k ω * (-(1 + α)) ≤ Λ k ω * (Z k ω - α) :=
        mul_le_mul_of_nonneg_left (by linarith [hz.1]) hl.1
      have h2 : Λ k ω * (1 + α) ≤ hi * (1 + α) := mul_le_mul_of_nonneg_right (hΛhi k ω) h1α.le
      linarith
    have hpos : ∀ k, 0 < 1 + Λ k ω * (Z k ω - α) := fun k => by linarith [hlow k]
    have hlogK : ∑ k, Real.log (1 + Λ k ω * (Z k ω - α)) < L := by
      rw [← Real.log_prod (fun k _ => (hpos k).ne'), hLdef]
      exact Real.log_lt_log (Finset.prod_pos fun k _ => hpos k) hKN
    have hterm : ∀ k, -s * Real.log (1 + Λ k ω * (Z k ω - α)) + w ≤
        -(s * Λ k ω) * (Z k ω - Δ k ω) - (-(s * Λ k ω)) ^ 2 / 2 := fun k => by
      have hl := hΛb k ω
      have hz := hZb k ω
      have hlog := log_lower_route a (Λ k ω * (Z k ω - α)) ha0.le ha1 (hlow k)
      have hu2 : (Λ k ω * (Z k ω - α)) ^ 2 ≤ hi ^ 2 * (1 + α) ^ 2 := by
        have h1 : |Λ k ω * (Z k ω - α)| ≤ hi * (1 + α) := by
          rw [abs_mul, abs_of_nonneg hl.1]
          have : |Z k ω - α| ≤ 1 + α := by rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
          exact mul_le_mul (hΛhi k ω) this (abs_nonneg _) hhi0.le
        rw [← sq_abs, ← mul_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have hcc : (Λ k ω * (Z k ω - α)) ^ 2 / (2 * (1 - a) ^ 2) ≤ Cc := by
        have hpos2 : (0 : ℝ) ≤ 1 / (2 * (1 - a) ^ 2) := by positivity
        have := mul_le_mul_of_nonneg_left hu2 hpos2
        calc (Λ k ω * (Z k ω - α)) ^ 2 / (2 * (1 - a) ^ 2) =
              1 / (2 * (1 - a) ^ 2) * (Λ k ω * (Z k ω - α)) ^ 2 := by ring
          _ ≤ 1 / (2 * (1 - a) ^ 2) * (hi ^ 2 * (1 + α) ^ 2) := this
          _ = Cc := by rw [hCc]; ring
      have hloρ : lo * ρ ≤ Λ k ω * (Δ k ω - α) := by
        have hE' := hE ω hωE k
        have h1 : ρ ≤ Δ k ω - α := by
          have := hE'.2
          change α + ρ ≤ Δ k ω at this
          linarith
        exact mul_le_mul hE'.1 h1 hρ.le hl.1
      have hξ : Λ k ω * (Z k ω - Δ k ω) ≤ Real.log (1 + Λ k ω * (Z k ω - α)) - lo * ρ + Cc := by
        have hsplit : Λ k ω * (Z k ω - α) = Λ k ω * (Z k ω - Δ k ω) + Λ k ω * (Δ k ω - α) := by ring
        linarith
      have hsq : (-(s * Λ k ω)) ^ 2 / 2 ≤ s ^ 2 * hi ^ 2 / 2 := by
        have : (s * Λ k ω) ^ 2 ≤ (s * hi) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hs.le hl.1) (mul_le_mul_of_nonneg_left (hΛhi k ω) hs.le) 2
        rw [neg_sq]
        linarith
      have hmul := mul_le_mul_of_nonneg_left hξ hs.le
      rw [hw]
      linarith
    have hsum : -s * L + N * w ≤ ∑ k, (-(s * Λ k ω) * (Z k ω - Δ k ω) - (-(s * Λ k ω)) ^ 2 / 2) := by
      have h1 : -s * ∑ k, Real.log (1 + Λ k ω * (Z k ω - α)) + N * w ≤
          ∑ k, (-(s * Λ k ω) * (Z k ω - Δ k ω) - (-(s * Λ k ω)) ^ 2 / 2) := by
        have := Finset.sum_le_sum (s := Finset.univ) fun k _ => hterm k
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← Finset.mul_sum] at this
        exact this
      have h2 := mul_lt_mul_of_pos_left hlogK hs
      linarith
    have hwx : -s * L + N * w = x ^ 2 / (2 * N * hi ^ 2) := by
      have e1 : -s * L + N * w = s * x - s ^ 2 * (N * hi ^ 2) / 2 := by
        rw [hw, hxdef, hCc]; ring
      rw [e1, hsdef]
      field_simp
      ring
    calc Real.exp (x ^ 2 / (2 * N * hi ^ 2)) ≤
          Real.exp (∑ k, (-(s * Λ k ω) * (Z k ω - Δ k ω) - (-(s * Λ k ω)) ^ 2 / 2)) :=
          Real.exp_le_exp.2 (hwx ▸ hsum)
      _ = ∏ k, F k ω := by rw [Real.exp_sum]
  have hA : 0 < Real.exp (x ^ 2 / (2 * N * hi ^ 2)) := Real.exp_pos _
  have hV := prod_ville P Q hpair.2.1 F hFm hFd hFb hmean hA
  calc μ.real (E ∩ {ω | ¬ rejects lam g bat A B α δ ω.1 ω.2}) ≤
        μ.real {ω | ∃ t ≤ N, Real.exp (x ^ 2 / (2 * N * hi ^ 2)) ≤
          ∏ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), F k ω} :=
        measureReal_mono hsub
    _ ≤ 1 / Real.exp (x ^ 2 / (2 * N * hi ^ 2)) := by rw [le_div_iff₀ hA, mul_comm]; exact hV
    _ = Real.exp (-(x ^ 2 / (2 * N * hi ^ 2))) := by rw [one_div, ← Real.exp_neg]

/-- **Lemma 5** (`eq:betbounds`, first bound). -/
theorem _root_.StatFormal.Wave30tz.bet_power_route : Claims.bet_power := by
  intro 𝒳 _ P Q _ _ n m N lx ly bat A B α δ c lo hi a ρ g lam E hpair hα hδ0 hδ1 hc0 hc1 hg hlam hhi ha ha1 hlo hρ
    _hEm hE
  have hL : 0 < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  set x : ℝ := (N : ℝ) * lo * ρ - 1 / (2 * (1 - a) ^ 2) * N * hi ^ 2 * (1 + α) ^ 2 - Real.log (1 / δ) with hxdef
  have hx' : x = (N : ℝ) * (lo * ρ - 1 / (2 * (1 - a) ^ 2) * hi ^ 2 * (1 + α) ^ 2) - Real.log (1 / δ) := by
    rw [hxdef]; ring
  rcases le_or_gt x 0 with hx | hx
  · rw [max_eq_right hx]
    have : Real.exp (-(0 : ℝ) ^ 2 / (2 * N * hi ^ 2)) = 1 := by simp
    rw [this, ENNReal.ofReal_one]
    exact prob_le_one
  · rw [max_eq_left hx.le]
    rcases E.eq_empty_or_nonempty with hE0 | ⟨ω₀, hω₀⟩
    · rw [hE0, Set.empty_inter, measure_empty]
      exact zero_le
    have hN : 1 ≤ N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · exfalso
        rw [h0, Nat.cast_zero, zero_mul, zero_sub] at hx'
        linarith
      · exact h0
    have hhi0 : 0 < hi := by
      have h1 := (hE ω₀ hω₀ ⟨0, hN⟩).1
      have h2 := hhi ⟨0, hN⟩ ω₀.1 ω₀.2 (past (pairStat g bat A B ω₀.1 ω₀.2) ⟨0, hN⟩)
      have hlohi : lo ≤ hi := h1.trans h2
      rcases eq_or_lt_of_le (hlo.trans hlohi) with h | h
      · exfalso
        have hi0 : hi = 0 := h.symm
        have hlo0 : lo = 0 := le_antisymm (hi0 ▸ hlohi) hlo
        rw [hi0, hlo0] at hx'
        have : x = -Real.log (1 / δ) := by rw [hx']; ring
        linarith
      · exact h
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal ((bet_power_core P Q hpair hα hc1 hg hlam hhi ha ha1 hρ hE hN hhi0
      hxdef hx).trans_eq ?_)
    rw [neg_div]

end Lemma5

/-! ### The fractions of `eq:fractions` -/

section Frac

/-- **Lemma 6 for `eq:fractions`** (`eq:betbounds`, second bound). -/
theorem _root_.StatFormal.Wave30tz.strict_null_frac_route : Claims.strict_null_frac := by
  intro 𝒳 _ P Q _ _ n m N lx ly bat A B α δ lmax s2 ζ g lam hpair hα hδ0 hδ1 hl0 hl1 hs2 hg hlam hhi hζ hTV
  have hL : 0 < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  set L := Real.log (1 / δ) with hLdef
  set lb := lamHi lmax α L s2 N with hlbdef
  have hrpow : ∀ u : ℝ, δ ^ (2 * ζ / u) = Real.exp (-(2 * ζ * L / u)) := fun u => by
    rw [Real.rpow_def_of_pos hδ0, hLdef, one_div, Real.log_inv]
    congr 1
    ring
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- no pairs: `K_0 = 1 < 1/δ`, the rejection event is empty
    have hempty : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | rejects lam g bat A B α δ ω.1 ω.2} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hω
      obtain ⟨t, _, hK⟩ := (rejects_iff ω.1 ω.2).1 hω
      rw [Finset.prod_eq_one fun k _ => absurd k.isLt (by omega)] at hK
      have : 1 < 1 / δ := by rw [lt_div_iff₀ hδ0]; linarith
      linarith
    rw [hempty, measure_empty]
    refine ⟨zero_le, zero_le, zero_le, fun h => ?_⟩
    exfalso
    rw [hN] at h
    exact absurd h (by norm_num)
  · have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h1α : 0 < 1 + α := by linarith
    have hcap : 0 < lmax / (1 + α) := div_pos hl0 h1α
    have hq : 0 < √(2 * L / (N * s2)) := Real.sqrt_pos.2 (by positivity)
    have hlb : 0 < lb := lt_min hcap hq
    have hlbcap : lb ≤ lmax / (1 + α) := min_le_left _ _
    have hlbq : lb ≤ √(2 * L / (N * s2)) := min_le_right _ _
    have hcore := strict_null_route 𝒳 P Q n m N lx ly bat A B α δ lmax lb ζ g lam hpair hα hδ0 hδ1 hl0 hl1 hg hlam
      hhi hζ hTV
    have h2ζL : 0 ≤ 2 * ζ * L := by positivity
    have b2 : Real.exp (-(2 * ζ * L / lb)) ≤ Real.exp (-(2 * ζ * L / (lmax / (1 + α)))) :=
      Real.exp_le_exp.2 (neg_le_neg (div_le_div_of_nonneg_left h2ζL hlb hlbcap))
    have hprod : √(2 * L / (N * s2)) * (√s2 * √(2 * N * L)) = 2 * L := by
      rw [← Real.sqrt_mul hs2.le, ← Real.sqrt_mul (by positivity)]
      rw [show 2 * L / (N * s2) * (s2 * (2 * N * L)) = (2 * L) ^ 2 by field_simp]
      exact Real.sqrt_sq (by positivity)
    have b3 : Real.exp (-(2 * ζ * L / lb)) ≤ Real.exp (-(ζ * √s2 * √(2 * N * L))) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      have e : ζ * √s2 * √(2 * N * L) = 2 * ζ * L / √(2 * L / (N * s2)) := by
        rw [eq_div_iff hq.ne']
        linear_combination ζ * hprod
      rw [e]
      exact div_le_div_of_nonneg_left h2ζL hlb hlbq
    refine ⟨?_, ?_, ?_, fun _ => ?_⟩
    · rw [hrpow]; exact hcore
    · rw [hrpow]; exact hcore.trans (ENNReal.ofReal_le_ofReal b2)
    · exact hcore.trans (ENNReal.ofReal_le_ofReal b3)
    · rw [hrpow]; exact b3

lemma exp_arg_le {x y D E : ℝ} (hxy : y ≤ x) (hE : 0 ≤ E) (hED : E ≤ 1 / D) :
    -(max x 0) ^ 2 / D ≤ -E * (max y 0) ^ 2 := by
  have hm : (max y 0) ^ 2 ≤ (max x 0) ^ 2 :=
    pow_le_pow_left₀ (le_max_right _ _) (max_le_max hxy le_rfl) 2
  calc -(max x 0) ^ 2 / D = -((max x 0) ^ 2 * (1 / D)) := by ring
    _ ≤ -((max y 0) ^ 2 * E) := neg_le_neg (mul_le_mul hm hED hE (sq_nonneg _))
    _ = -E * (max y 0) ^ 2 := by ring

/-- **Lemma 5 for `eq:fractions`** (`eq:betbounds`, first bound), and `ε_N(ϱ') → 0`. -/
theorem _root_.StatFormal.Wave30tz.bet_power_frac_route : Claims.bet_power_frac := by
  refine ⟨?_, epsN_small_route⟩
  intro 𝒳 _ P Q _ _ n m N lx ly bat A B α δ lmax s2 ρ g lam E hpair hα hδ0 hδ1 hl0 hl12 hs20 hs24 hg hlam hhi
    hNL hEm hE
  have hL : 0 < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  set L := Real.log (1 / δ) with hLdef
  have h1α : 0 < 1 + α := by linarith
  have hN : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNL
  rcases le_or_gt ρ 0 with hρ | hρ
  · have h1 : epsN s2 α L N ρ = 1 := by
      unfold epsN
      have h2 : ρ * √(N * L / 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hρ (Real.sqrt_nonneg _)
      have h3 : 0 ≤ 4 * L * (1 + α) ^ 2 / s2 := by positivity
      rw [max_eq_right (by linarith)]
      simp
    rw [h1, ENNReal.ofReal_one]
    exact prob_le_one
  · set lo := lamLo lmax α L s2 N with hlodef
    set hi := lamHi lmax α L s2 N with hhidef
    have hcap : 0 < lmax / (1 + α) := div_pos hl0 h1α
    have hq : 0 < √(2 * L / (N * s2)) := Real.sqrt_pos.2 (by positivity)
    have hhi0 : 0 < hi := lt_min hcap hq
    have hhicap : hi ≤ lmax / (1 + α) := min_le_left _ _
    have hhiq : hi ≤ √(2 * L / (N * s2)) := min_le_right _ _
    have hha : hi * (1 + α) ≤ lmax := by rwa [le_div_iff₀ h1α] at hhicap
    have hlo0 : 0 ≤ lo := le_min hcap.le (Real.sqrt_nonneg _)
    have hcore := bet_power_route 𝒳 P Q n m N lx ly bat A B α δ lmax lo hi lmax ρ g lam E hpair hα hδ0 hδ1 hl0
      (by linarith) hg hlam hhi hha (by linarith) hlo0 hρ hEm hE
    refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
    -- `λ_N = √(L/(2N))`
    have hlo_eq : lo = √(2 * L / (N * 4)) := by
      have hmax : max s2 4 = 4 := max_eq_right hs24
      have hsq : 2 * L / (N * 4) ≤ (lmax / (1 + α)) ^ 2 := by
        have hNL' := hNL
        rw [div_le_iff₀ (by positivity)] at hNL'
        rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      change min (lmax / (1 + α)) (√(2 * L / (N * max s2 4))) = √(2 * L / (N * 4))
      rw [hmax]
      apply min_eq_right
      calc √(2 * L / (N * 4)) ≤ √((lmax / (1 + α)) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = lmax / (1 + α) := Real.sqrt_sq hcap.le
    have hNlo : (N : ℝ) * lo = √(N * L / 2) := by
      rw [hlo_eq, show (N : ℝ) * L / 2 = N ^ 2 * (2 * L / (N * 4)) by field_simp; ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hN.le]
    have hNhi : (N : ℝ) * hi ^ 2 ≤ 2 * L / s2 := by
      have h1 : hi ^ 2 ≤ 2 * L / (N * s2) := by
        calc hi ^ 2 ≤ (√(2 * L / (N * s2))) ^ 2 := pow_le_pow_left₀ hhi0.le hhiq 2
          _ = 2 * L / (N * s2) := Real.sq_sqrt (by positivity)
      calc (N : ℝ) * hi ^ 2 ≤ N * (2 * L / (N * s2)) := mul_le_mul_of_nonneg_left h1 hN.le
        _ = 2 * L / s2 := by field_simp
    have hC : 1 / (2 * (1 - lmax) ^ 2) ≤ 2 := by
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith
    have hxy : ρ * √(N * L / 2) - L - 4 * L * (1 + α) ^ 2 / s2 ≤
        N * lo * ρ - 1 / (2 * (1 - lmax) ^ 2) * N * hi ^ 2 * (1 + α) ^ 2 - L := by
      have h1 : (N : ℝ) * lo * ρ = ρ * √(N * L / 2) := by rw [← hNlo]; ring
      have h2 : 1 / (2 * (1 - lmax) ^ 2) * N * hi ^ 2 * (1 + α) ^ 2 ≤ 4 * L * (1 + α) ^ 2 / s2 := by
        calc 1 / (2 * (1 - lmax) ^ 2) * N * hi ^ 2 * (1 + α) ^ 2 =
              1 / (2 * (1 - lmax) ^ 2) * (N * hi ^ 2) * (1 + α) ^ 2 := by ring
          _ ≤ 2 * (2 * L / s2) * (1 + α) ^ 2 := by
              have h0 : (0 : ℝ) ≤ 1 / (2 * (1 - lmax) ^ 2) := by positivity
              have h00 : (0 : ℝ) ≤ N * hi ^ 2 := by positivity
              exact mul_le_mul_of_nonneg_right (mul_le_mul hC hNhi h00 (by norm_num)) (by positivity)
          _ = 4 * L * (1 + α) ^ 2 / s2 := by ring
      linarith
    have hden0 : (0 : ℝ) < 2 * N * hi ^ 2 := by positivity
    have hfrac : s2 / (4 * L) ≤ 1 / (2 * N * hi ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) hden0, one_mul]
      have h1 := mul_le_mul_of_nonneg_left hNhi hs20.le
      rw [mul_div_cancel₀ _ hs20.ne'] at h1
      nlinarith
    unfold epsN
    exact Real.exp_le_exp.2 (exp_arg_le hxy (by positivity) hfrac)

end Frac

end Bet

end StatFormal.Wave30tz
