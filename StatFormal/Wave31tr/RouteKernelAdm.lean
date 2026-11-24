import StatFormal.Lib.KernelRun.KernelMeas
import StatFormal.Lib.PaperRun.Fitting
import StatFormal.Lib.PaperRun.Pairing
import StatFormal.Lib.PaperRunThm.UnitProd
import StatFormal.Wave30tz.RouteUpper

/-!
# Wave 31tr, chunk A3, T49 (a): the run as computed, at the kernel level, is admissible (untrusted route)

For a run with `IsKernelRun R kf θh …` (a measurable parameter space `Θ`, a jointly measurable kernel family `kf`, a parameter `θh b`
measurable and a function of the batches before `b`, any measurable capped weights) and quantile rules `qt`, `qu`:

* `kernelRun_spec`: the clauses of `IsKernelRun` in terms of the fitted quantities `kD` (`D̂ = kqpVal`), `kT` (`t̂`), `kU` (`û`),
  `kF` (the witness `kwit`) of the weights `kW = σ (θh b x y, fitting sample)`;
* `kHas_congr`, `kG_congr`, `kLam_congr`: `has`, `g` and the fractions depend only on the batches before the batch bet on (through
  `fitSample` and the dependence of `θh b`);
* `kHas_measurableSet`, `kG_measurable`, `kLam_measurable`: joint measurability on the whole sample space (`Lib/KernelRun/KernelMeas`:
  `kf (θh b x y) (x_i) z` is measurable as a composition, `kqpVal`, `kwit`, `kownX`, `kownY` are finite sums, products, quotients and a
  square root; the weights are measurable by hypothesis);
* `kG_mem`, `kLam_mem`: the ramp is `[0,1]`-valued whatever `kf` is (`û < t̂` on the bet), and the fractions lie in `[0, λ_max/(1+α)]`;
* `kernelRun_isAdmissible` (T49 (a), first half), and `kernel_run_valid_route`: composed with `Wave30tz.Upper.reject_le_delta`
  (the certified `Wave30tv.thm_betting` at `U = Unit`) and the certified `Wave30tv.cor_lower` (transported by `UnitProd`).

This is chunk A1's `RouteRunAdm` (T5 (a)) with `kf (θh b x y)` in place of `⟪φ·, φ·⟫`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tr.RouteKernel

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tz StatFormal.Wave30tp StatFormal.PaperRun StatFormal.KernelRun
  StatFormal.PaperRunThm

section Fitted

variable {𝒳 Θ : Type*} [MeasurableSpace 𝒳] [MeasurableSpace Θ]
variable {n m : ℕ} (kf : Θ → 𝒳 → 𝒳 → ℝ) (θh : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → Θ) (lx : Fin n → ℕ) (ly : Fin m → ℕ)
  (b : ℕ) (s : Θ × ((Fin (fitCard lx b) → 𝒳) × (Fin (fitCard ly b) → 𝒳)) → (Fin (fitCard lx b) → ℝ) × (Fin (fitCard ly b) → ℝ))

/-- The selected weights at the parameter and the fitting sample of batch `b`. -/
def kW (x : Fin n → 𝒳) (y : Fin m → 𝒳) : (Fin (fitCard lx b) → ℝ) × (Fin (fitCard ly b) → ℝ) :=
  s (θh b x y, (fitSample lx b x, fitSample ly b y))

/-- `D̂ = kqpVal` at the selected weights. -/
def kD (x : Fin n → 𝒳) (y : Fin m → 𝒳) : ℝ :=
  kqpVal (kf (θh b x y)) (fitSample lx b x) (fitSample ly b y) (kW θh lx ly b s x y).1 (kW θh lx ly b s x y).2

/-- The `X`-side cut `t̂ = qt n_{<b} (own-term values) a`. -/
def kT (q : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (a : ℝ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) : ℝ :=
  q (fitCard lx b) (kownX (kf (θh b x y)) (fitSample lx b x) (fitSample ly b y) (kW θh lx ly b s x y).1
    (kW θh lx ly b s x y).2) a

/-- The `Y`-side cut `û = qu m_{<b} (own-term values) a`. -/
def kU (q : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (a : ℝ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) : ℝ :=
  q (fitCard ly b) (kownY (kf (θh b x y)) (fitSample lx b x) (fitSample ly b y) (kW θh lx ly b s x y).1
    (kW θh lx ly b s x y).2) a

/-- The fitted kernel-level witness `kwit`. -/
def kF (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : 𝒳) : ℝ :=
  kwit (kf (θh b x y)) (fitSample lx b x) (fitSample ly b y) (kW θh lx ly b s x y).1 (kW θh lx ly b s x y).2 z

variable {kf θh lx ly b s}
variable (hkf : Measurable fun p : Θ × 𝒳 × 𝒳 => kf p.1 p.2.1 p.2.2)
  (hθ : Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => θh b p.1 p.2) (hs : Measurable s)

omit [MeasurableSpace Θ] in
theorem measurable_fitPair (lx : Fin n → ℕ) (ly : Fin m → ℕ) (b : ℕ) :
    Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => (fitSample lx b p.1, fitSample ly b p.2) :=
  ((measurable_fitSample lx b).comp measurable_fst).prodMk ((measurable_fitSample ly b).comp measurable_snd)

include hθ hs in
theorem measurable_kW : Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => kW θh lx ly b s p.1 p.2 :=
  hs.comp (hθ.prodMk (measurable_fitPair lx ly b))

include hkf hθ hs in
theorem measurable_kD : Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => kD kf θh lx ly b s p.1 p.2 :=
  measurable_kqpVal hkf hθ ((measurable_fitSample lx b).comp measurable_fst) ((measurable_fitSample ly b).comp measurable_snd)
    (measurable_fst.comp (measurable_kW hθ hs)) (measurable_snd.comp (measurable_kW hθ hs))

include hkf hθ hs in
theorem measurable_kT {q : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ} (hq : ∀ k a, Measurable fun h : Fin k → ℝ => q k h a) (a : ℝ) :
    Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => kT kf θh lx ly b s q a p.1 p.2 :=
  (hq _ a).comp (measurable_kownX hkf hθ ((measurable_fitSample lx b).comp measurable_fst)
    ((measurable_fitSample ly b).comp measurable_snd) (measurable_fst.comp (measurable_kW hθ hs))
    (measurable_snd.comp (measurable_kW hθ hs)))

include hkf hθ hs in
theorem measurable_kU {q : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ} (hq : ∀ k a, Measurable fun h : Fin k → ℝ => q k h a) (a : ℝ) :
    Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => kU kf θh lx ly b s q a p.1 p.2 :=
  (hq _ a).comp (measurable_kownY hkf hθ ((measurable_fitSample lx b).comp measurable_fst)
    ((measurable_fitSample ly b).comp measurable_snd) (measurable_fst.comp (measurable_kW hθ hs))
    (measurable_snd.comp (measurable_kW hθ hs)))

include hkf hθ hs in
theorem measurable_kF : Measurable fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => kF kf θh lx ly b s q.1.1 q.1.2 q.2 :=
  measurable_kwit hkf (hθ.comp measurable_fst) ((measurable_fitSample lx b).comp (measurable_fst.comp measurable_fst))
    ((measurable_fitSample ly b).comp (measurable_snd.comp measurable_fst))
    (measurable_fst.comp ((measurable_kW hθ hs).comp measurable_fst))
    (measurable_snd.comp ((measurable_kW hθ hs).comp measurable_fst)) measurable_snd

end Fitted

section Run

variable {𝒳 Θ : Type*} [MeasurableSpace 𝒳] [MeasurableSpace Θ] {kf : Θ → 𝒳 → 𝒳 → ℝ} {J n m : ℕ}
  {θh : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → Θ} {R : LoRun 𝒳 J n m} {α : Fin J → ℝ} {δ lmax s2 w0 : ℝ}
  {v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ} {qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ} {nb : ℕ} {cx cy : ℕ → ℕ}

open Classical in
/-- The clauses of `IsKernelRun` in terms of the fitted quantities of the selection. -/
theorem kernelRun_spec (hK : IsKernelRun R kf θh α δ lmax s2 w0 v0 qt qu nb cx cy) :
    ∃ σ : (j : Fin J) → (b : ℕ) → Θ × ((Fin (fitCard R.lx b) → 𝒳) × (Fin (fitCard R.ly b) → 𝒳)) →
        (Fin (fitCard R.lx b) → ℝ) × (Fin (fitCard R.ly b) → ℝ),
      (∀ j b, 1 ≤ fitCard R.lx b → 1 ≤ fitCard R.ly b → Measurable (σ j b)) ∧
      ∀ j b x y, (R.has j b x y ↔ (1 ≤ fitCard R.lx b ∧ 1 ≤ fitCard R.ly b ∧ 0 < kD kf θh R.lx R.ly b (σ j b) x y ∧
          kU kf θh R.lx R.ly b (σ j b) qu (α j) x y < kT kf θh R.lx R.ly b (σ j b) qt (1 - α j) x y)) ∧
        R.g j b x y = if R.has j b x y then
            ramp (kF kf θh R.lx R.ly b (σ j b) x y) (kT kf θh R.lx R.ly b (σ j b) qt (1 - α j) x y)
              (kU kf θh R.lx R.ly b (σ j b) qu (α j) x y)
          else fun _ => 0 := by
  obtain ⟨-, -, -, -, -, -, -, σ, hσ, hhg, -⟩ := hK
  exact ⟨σ, fun j b h1 h2 => (hσ j b h1 h2).1, hhg⟩

/-- The parameter clause of `IsKernelRun`. -/
theorem kernelRun_theta (hK : IsKernelRun R kf θh α δ lmax s2 w0 v0 qt qu nb cx cy) (b : ℕ) :
    Measurable (fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => θh b p.1 p.2) ∧
      ∀ x x' y y', (∀ i, R.lx i < b → x i = x' i) → (∀ j', R.ly j' < b → y j' = y' j') → θh b x y = θh b x' y' :=
  hK.2.2.2.2.2.2.1 b

/-- `has` of batch `b` depends only on the batches before `b`. -/
theorem kHas_congr (hK : IsKernelRun R kf θh α δ lmax s2 w0 v0 qt qu nb cx cy) (j : Fin J) (b : ℕ) {x x' : Fin n → 𝒳}
    {y y' : Fin m → 𝒳} (hx : ∀ i, R.lx i < b → x i = x' i) (hy : ∀ i, R.ly i < b → y i = y' i) :
    R.has j b x y ↔ R.has j b x' y' := by
  obtain ⟨σ, -, hhg⟩ := kernelRun_spec hK
  rw [(hhg j b x y).1, (hhg j b x' y').1]
  unfold kD kU kT kW
  rw [(kernelRun_theta hK b).2 x x' y y' hx hy, fitSample_congr R.lx b hx, fitSample_congr R.ly b hy]

/-- `g` of batch `b` depends only on the batches before `b`. -/
theorem kG_congr (hK : IsKernelRun R kf θh α δ lmax s2 w0 v0 qt qu nb cx cy) (j : Fin J) (b : ℕ) {x x' : Fin n → 𝒳}
    {y y' : Fin m → 𝒳} (hx : ∀ i, R.lx i < b → x i = x' i) (hy : ∀ i, R.ly i < b → y i = y' i) :
    R.g j b x y = R.g j b x' y' := by
  have hh := kHas_congr hK j b hx hy
  obtain ⟨σ, -, hhg⟩ := kernelRun_spec hK
  rw [(hhg j b x y).2, (hhg j b x' y').2, propext hh]
  unfold kF kU kT kW
  rw [(kernelRun_theta hK b).2 x x' y y' hx hy, fitSample_congr R.lx b hx, fitSample_congr R.ly b hy]

theorem kG_mem (hK : IsKernelRun R kf θh α δ lmax s2 w0 v0 qt qu nb cx cy) (j : Fin J) (b : ℕ) (x : Fin n → 𝒳)
    (y : Fin m → 𝒳) (z : 𝒳) : R.g j b x y z ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨σ, -, hhg⟩ := kernelRun_spec hK
  rw [(hhg j b x y).2]
  split_ifs with h
  · exact ramp_mem_Icc _ ((hhg j b x y).1.mp h).2.2.2 z
  · exact ⟨le_rfl, zero_le_one⟩

theorem kHas_measurableSet (hK : IsKernelRun R kf θh α δ lmax s2 w0 v0 qt qu nb cx cy)
    (hkf : Measurable fun p : Θ × 𝒳 × 𝒳 => kf p.1 p.2.1 p.2.2) (hqt : IsQuantileRule qt) (hqu : IsQuantileRule qu)
    (j : Fin J) (b : ℕ) : MeasurableSet {p : (Fin n → 𝒳) × (Fin m → 𝒳) | R.has j b p.1 p.2} := by
  obtain ⟨σ, hσ, hhg⟩ := kernelRun_spec hK
  have hθ := (kernelRun_theta hK b).1
  by_cases hfit : 1 ≤ fitCard R.lx b ∧ 1 ≤ fitCard R.ly b
  · have hs := hσ j b hfit.1 hfit.2
    have e : {p : (Fin n → 𝒳) × (Fin m → 𝒳) | R.has j b p.1 p.2} =
        {p | 0 < kD kf θh R.lx R.ly b (σ j b) p.1 p.2} ∩
          {p | kU kf θh R.lx R.ly b (σ j b) qu (α j) p.1 p.2 < kT kf θh R.lx R.ly b (σ j b) qt (1 - α j) p.1 p.2} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, (hhg j b p.1 p.2).1, hfit, true_and]
    rw [e]
    exact (measurableSet_lt measurable_const (measurable_kD hkf hθ hs)).inter
      (measurableSet_lt (measurable_kU hkf hθ hs hqu.1 _) (measurable_kT hkf hθ hs hqt.1 _))
  · have e : {p : (Fin n → 𝒳) × (Fin m → 𝒳) | R.has j b p.1 p.2} = ∅ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      obtain ⟨h1, h2, -⟩ := (hhg j b p.1 p.2).1.mp h
      exact hfit ⟨h1, h2⟩
    rw [e]; exact MeasurableSet.empty

open Classical in
theorem kG_measurable (hK : IsKernelRun R kf θh α δ lmax s2 w0 v0 qt qu nb cx cy)
    (hkf : Measurable fun p : Θ × 𝒳 × 𝒳 => kf p.1 p.2.1 p.2.2) (hqt : IsQuantileRule qt) (hqu : IsQuantileRule qu)
    (j : Fin J) (b : ℕ) : Measurable fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => R.g j b q.1.1 q.1.2 q.2 := by
  have hset := kHas_measurableSet hK hkf hqt hqu j b
  obtain ⟨σ, hσ, hhg⟩ := kernelRun_spec hK
  have hθ := (kernelRun_theta hK b).1
  by_cases hfit : 1 ≤ fitCard R.lx b ∧ 1 ≤ fitCard R.ly b
  · have hs := hσ j b hfit.1 hfit.2
    have e : (fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => R.g j b q.1.1 q.1.2 q.2) = fun q =>
        if R.has j b q.1.1 q.1.2 then
          (min (max (kF kf θh R.lx R.ly b (σ j b) q.1.1 q.1.2 q.2) (kU kf θh R.lx R.ly b (σ j b) qu (α j) q.1.1 q.1.2))
              (kT kf θh R.lx R.ly b (σ j b) qt (1 - α j) q.1.1 q.1.2) - kU kf θh R.lx R.ly b (σ j b) qu (α j) q.1.1 q.1.2) /
            (kT kf θh R.lx R.ly b (σ j b) qt (1 - α j) q.1.1 q.1.2 - kU kf θh R.lx R.ly b (σ j b) qu (α j) q.1.1 q.1.2)
        else 0 := by
      funext q
      rw [(hhg j b q.1.1 q.1.2).2]
      split_ifs <;> rfl
    rw [e]
    have hT : Measurable fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 =>
        kT kf θh R.lx R.ly b (σ j b) qt (1 - α j) q.1.1 q.1.2 := (measurable_kT hkf hθ hs hqt.1 (1 - α j)).comp measurable_fst
    have hU : Measurable fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 =>
        kU kf θh R.lx R.ly b (σ j b) qu (α j) q.1.1 q.1.2 := (measurable_kU hkf hθ hs hqu.1 (α j)).comp measurable_fst
    refine Measurable.ite (measurable_fst hset) ?_ measurable_const
    exact ((((measurable_kF hkf hθ hs).max hU).min hT).sub hU).div (hT.sub hU)
  · have e : (fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => R.g j b q.1.1 q.1.2 q.2) = fun _ => 0 := by
      funext q
      rw [(hhg j b q.1.1 q.1.2).2, ite_eq_right]
      intro h
      obtain ⟨h1, h2, -⟩ := (hhg j b q.1.1 q.1.2).1.mp h
      exact hfit ⟨h1, h2⟩
    rw [e]; exact measurable_const

open Classical in
/-- The fractions clause of `IsKernelRun`. -/
theorem kernelRun_lam (hK : IsKernelRun R kf θh α δ lmax s2 w0 v0 qt qu nb cx cy) :
    ∀ (j : Fin J) (k : Fin R.N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : Fin k → ℝ),
      R.lam j k x y z = if R.has j (R.bat k) x y then
          fracFormula lmax (α j) (Real.log (1 / δ)) R.N s2 w0 (v0 j (R.bat k) x y)
            (fun l : Fin k => if R.has j (R.bat (Fin.castLE k.isLt.le l)) x y then 1 else 0) z
        else 0 := by
  obtain ⟨-, -, -, -, -, -, -, σ, -, -, hlam⟩ := hK
  exact hlam

open Classical in
theorem kLam_measurable (hK : IsKernelRun R kf θh α δ lmax s2 w0 v0 qt qu nb cx cy)
    (hkf : Measurable fun p : Θ × 𝒳 × 𝒳 => kf p.1 p.2.1 p.2.2) (hqt : IsQuantileRule qt) (hqu : IsQuantileRule qu)
    (j : Fin J) (k : Fin R.N) :
    Measurable fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × (Fin k → ℝ) => R.lam j k q.1.1 q.1.2 q.2 := by
  have hprior := hK.2.2.2.2.2.1
  have e : (fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × (Fin k → ℝ) => R.lam j k q.1.1 q.1.2 q.2) = fun q =>
      if R.has j (R.bat k) q.1.1 q.1.2 then
        fracFormula lmax (α j) (Real.log (1 / δ)) R.N s2 w0 (v0 j (R.bat k) q.1.1 q.1.2)
          (fun l : Fin k => if R.has j (R.bat (Fin.castLE k.isLt.le l)) q.1.1 q.1.2 then 1 else 0) q.2
      else 0 := by
    funext q; exact kernelRun_lam hK j k q.1.1 q.1.2 q.2
  rw [e]
  refine Measurable.ite (measurable_fst (kHas_measurableSet hK hkf hqt hqu j (R.bat k))) ?_ measurable_const
  refine measurable_fracFormula _ _ _ _ _ _ ((hprior j (R.bat k)).1.comp measurable_fst) ?_ measurable_snd
  exact Measurable.of_eval fun l =>
    Measurable.ite (measurable_fst (kHas_measurableSet hK hkf hqt hqu j _)) measurable_const measurable_const

theorem kLam_mem (hK : IsKernelRun R kf θh α δ lmax s2 w0 v0 qt qu nb cx cy) (hl : 0 < lmax) (hα : ∀ j, 0 ≤ α j)
    (j : Fin J) (k : Fin R.N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : Fin k → ℝ) :
    0 ≤ R.lam j k x y z ∧ R.lam j k x y z ≤ lmax / (1 + α j) := by
  rw [kernelRun_lam hK]
  have hcap : 0 ≤ lmax / (1 + α j) := div_nonneg hl.le (by linarith [hα j])
  split_ifs
  · exact ⟨fracFormula_nonneg _ _ _ _ hl.le (hα j) _ _ _, fracFormula_le_cap _ _ _ _ _ _ _ _ _⟩
  · exact ⟨le_rfl, hcap⟩

open Classical in
/-- The fractions of pair `k` depend only on the batches before `bat k` (pairs numbered in the order of the batches). -/
theorem kLam_congr (hK : IsKernelRun R kf θh α δ lmax s2 w0 v0 qt qu nb cx cy) (j : Fin J) (k : Fin R.N) {x x' : Fin n → 𝒳}
    {y y' : Fin m → 𝒳} (hx : ∀ i, R.lx i < R.bat k → x i = x' i) (hy : ∀ i, R.ly i < R.bat k → y i = y' i) :
    R.lam j k x y = R.lam j k x' y' := by
  have hmono := hK.2.2.2.2.1.2.1
  have hprior := hK.2.2.2.2.2.1
  funext z
  rw [kernelRun_lam hK, kernelRun_lam hK, propext (kHas_congr hK j (R.bat k) hx hy), (hprior j (R.bat k)).2.2 x x' y y' hx hy]
  have he : (fun l : Fin k => if R.has j (R.bat (Fin.castLE k.isLt.le l)) x y then (1 : ℝ) else 0) =
      fun l : Fin k => if R.has j (R.bat (Fin.castLE k.isLt.le l)) x' y' then 1 else 0 := by
    funext l
    have hb : R.bat (Fin.castLE k.isLt.le l) ≤ R.bat k :=
      hmono (show Fin.castLE k.isLt.le l ≤ k from Fin.le_iff_val_le_val.mpr (by simp only [Fin.val_castLE]; omega))
    rw [propext (kHas_congr hK j _ (fun i hi => hx i (lt_of_lt_of_le hi hb)) (fun i hi => hy i (lt_of_lt_of_le hi hb)))]
  rw [he]

/-- **T49 (a), first half**: the run as computed, at the kernel level, is admissible. -/
theorem kernelRun_isAdmissible (hK : IsKernelRun R kf θh α δ lmax s2 w0 v0 qt qu nb cx cy)
    (hkf : Measurable fun p : Θ × 𝒳 × 𝒳 => kf p.1 p.2.1 p.2.2) (hqt : IsQuantileRule qt) (hqu : IsQuantileRule qu)
    (hl : 0 < lmax) (hα : ∀ j, 0 ≤ α j) : R.IsAdmissible α lmax := by
  refine ⟨(isBatchPairing_of_printed hK.2.2.2.2.1).1, fun j k => ⟨?_, fun _ x y z => kG_mem hK j _ x y z,
    fun _ x x' y y' hx hy => kG_congr hK j _ hx hy⟩, fun j k => ⟨?_, fun _ x y z => kLam_mem hK hl hα j k x y z,
    fun _ x x' y y' hx hy => kLam_congr hK j k hx hy⟩⟩
  · exact (kG_measurable hK hkf hqt hqu j (R.bat k)).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  · exact (kLam_measurable hK hkf hqt hqu j k).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

end Run

/-- **T49 (a)**: the run as computed is admissible, so Theorem 4.2 holds at every true null level and Corollary 4.3 holds. -/
theorem kernel_run_valid_route : Claims.kernel_run_valid := by
  intro 𝒳 Θ _ _ J n m kf θh α δ lmax s2 w0 v0 qt qu nb cx cy R hkf hgrid hδ0 hδ1 hl0 hl1 _ _ hqt hqu hK
  have hadm := kernelRun_isAdmissible hK hkf hqt hqu hl0 (fun j => (hgrid.2 j).1)
  refine ⟨hadm, fun P Q _ _ => ?_⟩
  obtain ⟨hpair, hfit, hfrac⟩ := hadm
  refine ⟨fun j hTV => Upper.reject_le_delta P Q hpair (hgrid.2 j).1 hδ0 hδ1 hl0 hl1 (hfit j) (hfrac j) hTV, ?_⟩
  have h := StatFormal.Wave30tv.cor_lower 𝒳 Unit P Q (Measure.dirac ()) n m R.N J R.lx R.ly R.bat R.A R.B α δ lmax
    (fun j b _ => R.g j b) (fun j k _ => R.lam j k) hpair hδ0 hδ1 hl0 hl1 (fun j => (hgrid.2 j).1) hfit hfrac
  refine (dirac_prod_unit_set ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))
    {ω | StatFormal.Distances.tvDist P Q < R.alphaLo α δ ω.1 ω.2} _ ?_).symm.trans_le h
  exact fun ω => Iff.rfl

end StatFormal.Wave31tr.RouteKernel
