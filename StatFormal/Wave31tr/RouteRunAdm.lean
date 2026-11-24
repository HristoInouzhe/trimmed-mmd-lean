import StatFormal.Wave31tr.RouteRunPairing
import StatFormal.Lib.PaperRun.Fitting

/-!
# Wave 31tr, chunk A1, T5 (part 1): the fitted quantities of a paper run, measurability and dependence (untrusted route)

For a run with `IsPaperRun` and quantile rules `qt`, `qu`:
* `paperRun_spec`: the clauses (3) of `IsPaperRun` in terms of the fitted quantities `fitD` (`D̂`), `fitT` (`t̂`), `fitU` (`û`),
  `fitF` (the witness `z ↦ ⟪f̂, φ z⟫`) of the selection;
* `has_fit`, `has_congr`, `g_congr`: no bet on an empty fitting side; `has` and `g` of batch `b` depend only on the batches `< b`
  (through `fitSample`);
* `has_measurableSet`, `g_measurable`: `{has}` is measurable and `g` is jointly measurable in the sample and the point, on the
  whole sample space (on a batch with an empty fitting side `has` is empty and `g = 0`; otherwise the guarded `IsQPSel`);
* `g_mem`: `g ∈ [0,1]`; `lam_measurable`, `lam_mem`, `lam_congr`: the fractions are jointly measurable, in `[0, λ_max/(1+α)]`, and
  depend only on the batches before the pair's batch.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr.RouteRun

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tz StatFormal.Wave31tl StatFormal.PaperRun

section Fitted

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {n m : ℕ} (φ : 𝒳 → H) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (b : ℕ)
  (s : (Fin (fitCard lx b) → 𝒳) × (Fin (fitCard ly b) → 𝒳) → (Fin (fitCard lx b) → ℝ) × (Fin (fitCard ly b) → ℝ))

/-- The selected weights at the fitting sample of batch `b`. -/
def fitW (x : Fin n → 𝒳) (y : Fin m → 𝒳) : (Fin (fitCard lx b) → ℝ) × (Fin (fitCard ly b) → ℝ) :=
  s (fitSample lx b x, fitSample ly b y)

/-- `D̂` at the selected weights. -/
def fitD (x : Fin n → 𝒳) (y : Fin m → 𝒳) : ℝ :=
  qpVal φ (fitSample lx b x) (fitSample ly b y) (fitW lx ly b s x y).1 (fitW lx ly b s x y).2

/-- The `X`-side cut `t̂ = qt n_{<b} (own-term values) a`. -/
def fitT (q : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (a : ℝ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) : ℝ :=
  q (fitCard lx b) (ownX φ (fitSample lx b x) (fitSample ly b y) (fitW lx ly b s x y).1 (fitW lx ly b s x y).2) a

/-- The `Y`-side cut `û = qu m_{<b} (own-term values) a`. -/
def fitU (q : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (a : ℝ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) : ℝ :=
  q (fitCard ly b) (ownY φ (fitSample lx b x) (fitSample ly b y) (fitW lx ly b s x y).1 (fitW lx ly b s x y).2) a

/-- The fitted witness as a function, `z ↦ ⟪f̂, φ z⟫`. -/
def fitF (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : 𝒳) : ℝ :=
  ⟪witness φ (fitSample lx b x) (fitSample ly b y) (fitW lx ly b s x y).1 (fitW lx ly b s x y).2, φ z⟫_ℝ

variable {φ lx ly b s}

theorem measurable_fitW (hs : Measurable s) :
    Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => fitW lx ly b s p.1 p.2 :=
  hs.comp (((measurable_fitSample lx b).comp measurable_fst).prodMk ((measurable_fitSample ly b).comp measurable_snd))

theorem measurable_fitD (hφ : StronglyMeasurable φ) (hs : Measurable s) :
    Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => fitD φ lx ly b s p.1 p.2 :=
  measurable_qpVal hφ ((measurable_fitSample lx b).comp measurable_fst) ((measurable_fitSample ly b).comp measurable_snd)
    (measurable_fst.comp (measurable_fitW hs)) (measurable_snd.comp (measurable_fitW hs))

theorem measurable_fitT (hφ : StronglyMeasurable φ) (hs : Measurable s) {q : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ}
    (hq : ∀ k a, Measurable fun h : Fin k → ℝ => q k h a) (a : ℝ) :
    Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => fitT φ lx ly b s q a p.1 p.2 :=
  (hq _ a).comp (measurable_ownX hφ ((measurable_fitSample lx b).comp measurable_fst)
    ((measurable_fitSample ly b).comp measurable_snd) (measurable_fst.comp (measurable_fitW hs))
    (measurable_snd.comp (measurable_fitW hs)))

theorem measurable_fitU (hφ : StronglyMeasurable φ) (hs : Measurable s) {q : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ}
    (hq : ∀ k a, Measurable fun h : Fin k → ℝ => q k h a) (a : ℝ) :
    Measurable fun p : (Fin n → 𝒳) × (Fin m → 𝒳) => fitU φ lx ly b s q a p.1 p.2 :=
  (hq _ a).comp (measurable_ownY hφ ((measurable_fitSample lx b).comp measurable_fst)
    ((measurable_fitSample ly b).comp measurable_snd) (measurable_fst.comp (measurable_fitW hs))
    (measurable_snd.comp (measurable_fitW hs)))

theorem measurable_fitF (hφ : StronglyMeasurable φ) (hs : Measurable s) :
    Measurable fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => fitF φ lx ly b s q.1.1 q.1.2 q.2 :=
  measurable_witness_apply hφ ((measurable_fitSample lx b).comp (measurable_fst.comp measurable_fst))
    ((measurable_fitSample ly b).comp (measurable_snd.comp measurable_fst))
    (measurable_fst.comp ((measurable_fitW hs).comp measurable_fst)) (measurable_snd.comp ((measurable_fitW hs).comp measurable_fst))
    measurable_snd

end Fitted

section Run

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {φ : 𝒳 → H} {J n m : ℕ} {R : LoRun 𝒳 J n m} {α : Fin J → ℝ} {δ lmax s2 w0 : ℝ}
  {v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ} {qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ} {nb : ℕ} {cx cy : ℕ → ℕ}

open Classical in
/-- The clauses (3) of `IsPaperRun` in terms of the fitted quantities of the selection. -/
theorem paperRun_spec (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) :
    ∃ σ : (j : Fin J) → (b : ℕ) → (Fin (fitCard R.lx b) → 𝒳) × (Fin (fitCard R.ly b) → 𝒳) →
        (Fin (fitCard R.lx b) → ℝ) × (Fin (fitCard R.ly b) → ℝ),
      (∀ j b, 1 ≤ fitCard R.lx b → 1 ≤ fitCard R.ly b → IsQPSel φ (α j) (σ j b)) ∧
      ∀ j b x y, (R.has j b x y ↔ (1 ≤ fitCard R.lx b ∧ 1 ≤ fitCard R.ly b ∧ 0 < fitD φ R.lx R.ly b (σ j b) x y ∧
          fitU φ R.lx R.ly b (σ j b) qu (α j) x y < fitT φ R.lx R.ly b (σ j b) qt (1 - α j) x y)) ∧
        R.g j b x y = if R.has j b x y then
            ramp (fitF φ R.lx R.ly b (σ j b) x y) (fitT φ R.lx R.ly b (σ j b) qt (1 - α j) x y)
              (fitU φ R.lx R.ly b (σ j b) qu (α j) x y)
          else fun _ => 0 := by
  obtain ⟨-, -, -, -, -, -, σ, hσ, hhg, -⟩ := hP
  exact ⟨σ, hσ, hhg⟩

theorem has_fit (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) {j : Fin J} {b : ℕ} {x : Fin n → 𝒳}
    {y : Fin m → 𝒳} (h : R.has j b x y) : 1 ≤ fitCard R.lx b ∧ 1 ≤ fitCard R.ly b := by
  obtain ⟨σ, -, hhg⟩ := paperRun_spec hP
  obtain ⟨h1, h2, -⟩ := (hhg j b x y).1.mp h
  exact ⟨h1, h2⟩

/-- `has` of batch `b` depends only on the batches before `b`. -/
theorem has_congr (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (j : Fin J) (b : ℕ) {x x' : Fin n → 𝒳}
    {y y' : Fin m → 𝒳} (hx : ∀ i, R.lx i < b → x i = x' i) (hy : ∀ i, R.ly i < b → y i = y' i) :
    R.has j b x y ↔ R.has j b x' y' := by
  obtain ⟨σ, -, hhg⟩ := paperRun_spec hP
  rw [(hhg j b x y).1, (hhg j b x' y').1]
  unfold fitD fitU fitT fitW
  rw [fitSample_congr R.lx b hx, fitSample_congr R.ly b hy]

/-- `g` of batch `b` depends only on the batches before `b`. -/
theorem g_congr (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (j : Fin J) (b : ℕ) {x x' : Fin n → 𝒳}
    {y y' : Fin m → 𝒳} (hx : ∀ i, R.lx i < b → x i = x' i) (hy : ∀ i, R.ly i < b → y i = y' i) :
    R.g j b x y = R.g j b x' y' := by
  have hh := has_congr hP j b hx hy
  obtain ⟨σ, -, hhg⟩ := paperRun_spec hP
  rw [(hhg j b x y).2, (hhg j b x' y').2, propext hh]
  unfold fitF fitU fitT fitW
  rw [fitSample_congr R.lx b hx, fitSample_congr R.ly b hy]

theorem g_mem (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (j : Fin J) (b : ℕ) (x : Fin n → 𝒳)
    (y : Fin m → 𝒳) (z : 𝒳) : R.g j b x y z ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨σ, -, hhg⟩ := paperRun_spec hP
  rw [(hhg j b x y).2]
  split_ifs with h
  · exact ramp_mem_Icc _ ((hhg j b x y).1.mp h).2.2.2 z
  · exact ⟨le_rfl, zero_le_one⟩

theorem has_measurableSet (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (hφ : StronglyMeasurable φ)
    (hqt : IsQuantileRule qt) (hqu : IsQuantileRule qu) (j : Fin J) (b : ℕ) :
    MeasurableSet {p : (Fin n → 𝒳) × (Fin m → 𝒳) | R.has j b p.1 p.2} := by
  obtain ⟨σ, hσ, hhg⟩ := paperRun_spec hP
  by_cases hfit : 1 ≤ fitCard R.lx b ∧ 1 ≤ fitCard R.ly b
  · have hs := (hσ j b hfit.1 hfit.2).1
    have e : {p : (Fin n → 𝒳) × (Fin m → 𝒳) | R.has j b p.1 p.2} =
        {p | 0 < fitD φ R.lx R.ly b (σ j b) p.1 p.2} ∩
          {p | fitU φ R.lx R.ly b (σ j b) qu (α j) p.1 p.2 < fitT φ R.lx R.ly b (σ j b) qt (1 - α j) p.1 p.2} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, (hhg j b p.1 p.2).1, hfit, true_and]
    rw [e]
    exact (measurableSet_lt measurable_const (measurable_fitD hφ hs)).inter
      (measurableSet_lt (measurable_fitU hφ hs hqu.1 _) (measurable_fitT hφ hs hqt.1 _))
  · have e : {p : (Fin n → 𝒳) × (Fin m → 𝒳) | R.has j b p.1 p.2} = ∅ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      obtain ⟨h1, h2, -⟩ := (hhg j b p.1 p.2).1.mp h
      exact hfit ⟨h1, h2⟩
    rw [e]; exact MeasurableSet.empty

open Classical in
theorem g_measurable (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (hφ : StronglyMeasurable φ)
    (hqt : IsQuantileRule qt) (hqu : IsQuantileRule qu) (j : Fin J) (b : ℕ) :
    Measurable fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => R.g j b q.1.1 q.1.2 q.2 := by
  have hset := has_measurableSet hP hφ hqt hqu j b
  obtain ⟨σ, hσ, hhg⟩ := paperRun_spec hP
  by_cases hfit : 1 ≤ fitCard R.lx b ∧ 1 ≤ fitCard R.ly b
  · have hs := (hσ j b hfit.1 hfit.2).1
    have e : (fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => R.g j b q.1.1 q.1.2 q.2) = fun q =>
        if R.has j b q.1.1 q.1.2 then
          (min (max (fitF φ R.lx R.ly b (σ j b) q.1.1 q.1.2 q.2) (fitU φ R.lx R.ly b (σ j b) qu (α j) q.1.1 q.1.2))
              (fitT φ R.lx R.ly b (σ j b) qt (1 - α j) q.1.1 q.1.2) - fitU φ R.lx R.ly b (σ j b) qu (α j) q.1.1 q.1.2) /
            (fitT φ R.lx R.ly b (σ j b) qt (1 - α j) q.1.1 q.1.2 - fitU φ R.lx R.ly b (σ j b) qu (α j) q.1.1 q.1.2)
        else 0 := by
      funext q
      rw [(hhg j b q.1.1 q.1.2).2]
      split_ifs <;> rfl
    rw [e]
    have hT : Measurable fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 =>
        fitT φ R.lx R.ly b (σ j b) qt (1 - α j) q.1.1 q.1.2 := (measurable_fitT hφ hs hqt.1 (1 - α j)).comp measurable_fst
    have hU : Measurable fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 =>
        fitU φ R.lx R.ly b (σ j b) qu (α j) q.1.1 q.1.2 := (measurable_fitU hφ hs hqu.1 (α j)).comp measurable_fst
    refine Measurable.ite (measurable_fst hset) ?_ measurable_const
    exact ((((measurable_fitF hφ hs).max hU).min hT).sub hU).div (hT.sub hU)
  · have e : (fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => R.g j b q.1.1 q.1.2 q.2) = fun _ => 0 := by
      funext q
      rw [(hhg j b q.1.1 q.1.2).2, ite_eq_right]
      intro h
      obtain ⟨h1, h2, -⟩ := (hhg j b q.1.1 q.1.2).1.mp h
      exact hfit ⟨h1, h2⟩
    rw [e]; exact measurable_const

open Classical in
/-- The fractions clause of `IsPaperRun`. -/
theorem paperRun_lam (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) :
    ∀ (j : Fin J) (k : Fin R.N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : Fin k → ℝ),
      R.lam j k x y z = if R.has j (R.bat k) x y then
          fracFormula lmax (α j) (Real.log (1 / δ)) R.N s2 w0 (v0 j (R.bat k) x y)
            (fun l : Fin k => if R.has j (R.bat (Fin.castLE k.isLt.le l)) x y then 1 else 0) z
        else 0 := by
  obtain ⟨-, -, -, -, -, -, σ, -, -, hlam⟩ := hP
  exact hlam

open Classical in
theorem lam_measurable (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (hφ : StronglyMeasurable φ)
    (hqt : IsQuantileRule qt) (hqu : IsQuantileRule qu) (j : Fin J) (k : Fin R.N) :
    Measurable fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × (Fin k → ℝ) => R.lam j k q.1.1 q.1.2 q.2 := by
  have hprior := hP.2.2.2.2.2.1
  have e : (fun q : ((Fin n → 𝒳) × (Fin m → 𝒳)) × (Fin k → ℝ) => R.lam j k q.1.1 q.1.2 q.2) = fun q =>
      if R.has j (R.bat k) q.1.1 q.1.2 then
        fracFormula lmax (α j) (Real.log (1 / δ)) R.N s2 w0 (v0 j (R.bat k) q.1.1 q.1.2)
          (fun l : Fin k => if R.has j (R.bat (Fin.castLE k.isLt.le l)) q.1.1 q.1.2 then 1 else 0) q.2
      else 0 := by
    funext q; exact paperRun_lam hP j k q.1.1 q.1.2 q.2
  rw [e]
  refine Measurable.ite (measurable_fst (has_measurableSet hP hφ hqt hqu j (R.bat k))) ?_ measurable_const
  refine measurable_fracFormula _ _ _ _ _ _ ((hprior j (R.bat k)).1.comp measurable_fst) ?_ measurable_snd
  exact Measurable.of_eval fun l =>
    Measurable.ite (measurable_fst (has_measurableSet hP hφ hqt hqu j _)) measurable_const measurable_const

theorem lam_mem (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (hl : 0 < lmax) (hα : ∀ j, 0 ≤ α j)
    (j : Fin J) (k : Fin R.N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : Fin k → ℝ) :
    0 ≤ R.lam j k x y z ∧ R.lam j k x y z ≤ lmax / (1 + α j) := by
  rw [paperRun_lam hP]
  have hcap : 0 ≤ lmax / (1 + α j) := div_nonneg hl.le (by linarith [hα j])
  split_ifs
  · exact ⟨fracFormula_nonneg _ _ _ _ hl.le (hα j) _ _ _, fracFormula_le_cap _ _ _ _ _ _ _ _ _⟩
  · exact ⟨le_rfl, hcap⟩

open Classical in
/-- The fractions of pair `k` depend only on the batches before `bat k` (pairs numbered in the order of the batches). -/
theorem lam_congr (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (j : Fin J) (k : Fin R.N) {x x' : Fin n → 𝒳}
    {y y' : Fin m → 𝒳} (hx : ∀ i, R.lx i < R.bat k → x i = x' i) (hy : ∀ i, R.ly i < R.bat k → y i = y' i) :
    R.lam j k x y = R.lam j k x' y' := by
  have hmono := hP.2.2.2.2.1.2.1
  have hprior := hP.2.2.2.2.2.1
  funext z
  rw [paperRun_lam hP, paperRun_lam hP, propext (has_congr hP j (R.bat k) hx hy), (hprior j (R.bat k)).2.2 x x' y y' hx hy]
  have he : (fun l : Fin k => if R.has j (R.bat (Fin.castLE k.isLt.le l)) x y then (1 : ℝ) else 0) =
      fun l : Fin k => if R.has j (R.bat (Fin.castLE k.isLt.le l)) x' y' then 1 else 0 := by
    funext l
    have hb : R.bat (Fin.castLE k.isLt.le l) ≤ R.bat k :=
      hmono (show Fin.castLE k.isLt.le l ≤ k from Fin.le_iff_val_le_val.mpr (by simp only [Fin.val_castLE]; omega))
    rw [propext (has_congr hP j _ (fun i hi => hx i (lt_of_lt_of_le hi hb)) (fun i hi => hy i (lt_of_lt_of_le hi hb)))]
  rw [he]

/-- **T5 (a)**: a paper run with quantile rules is admissible. -/
theorem paperRun_isAdmissible (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (hφ : StronglyMeasurable φ)
    (hqt : IsQuantileRule qt) (hqu : IsQuantileRule qu) (hl : 0 < lmax) (hα : ∀ j, 0 ≤ α j) :
    R.IsAdmissible α lmax := by
  refine ⟨(isBatchPairing_of_printed hP.2.2.2.2.1).1, fun j k => ⟨?_, fun _ x y z => g_mem hP j _ x y z,
    fun _ x x' y y' hx hy => g_congr hP j _ hx hy⟩, fun j k => ⟨?_, fun _ x y z => lam_mem hP hl hα j k x y z,
    fun _ x x' y y' hx hy => lam_congr hP j k hx hy⟩⟩
  · exact (g_measurable hP hφ hqt hqu j (R.bat k)).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  · exact (lam_measurable hP hφ hqt hqu j k).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

end Run

end StatFormal.Wave31tr.RouteRun
