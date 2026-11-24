import StatFormal.Wave31tr.RouteRunAdm

/-!
# Wave 31tr, chunk A1, T5 (part 2): the paper's run is admissible and a witness run (untrusted route)

Proves `Claims.paperRun_admissible`:
* (a) `paperRun_isAdmissible` (part 1, `RouteRunAdm.lean`);
* (b) `paperRun_witnessRamp` (the selected exact minimizer; the cut rules at `1−α_j` and `α_j` land in the (C) brackets
  `CutsC` by `IsQuantileRule`) and `paperRun_frac_bounds` (`λ ≤ λ̄_N` for every past; `λ ≥ λ_N` on a batch bet on, for pasts in
  `[−1,1]`, from the certified `Wave30tz.fractions_bounds` via `fracFormula_indicator`; `λ = 0` elsewhere);
* (c) `paperRun_default` (nearest-integer boundaries: `cutLabel 2 = defaultLabel`, `N = defaultPairs`);
* (d) `paperRun_sized` (`n_{<b} = c_b ≥ π_b n − 1 ≥ c n − 2` and `N ≥ min(n_1, m_1) ≥ c min(n,m) − 2`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr.RouteRun

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tz StatFormal.Wave31tl StatFormal.PaperRun

section Run

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {φ : 𝒳 → H} {J n m : ℕ} {R : LoRun 𝒳 J n m} {α : Fin J → ℝ} {δ lmax s2 w0 : ℝ}
  {v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ} {qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ} {nb : ℕ} {cx cy : ℕ → ℕ}

/-- **T5 (b)**, the ramps: on every batch, the run's rule is a witness ramp (an exact minimizer, cut points in the (C) brackets). -/
theorem paperRun_witnessRamp (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (hqt : IsQuantileRule qt)
    (hqu : IsQuantileRule qu) (hgrid : IsGrid α) (j : Fin J) (b : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    IsWitnessRamp φ (α j) (fitSample R.lx b x) (fitSample R.ly b y) (R.has j b x y) (R.g j b x y) := by
  obtain ⟨σ, hσ, hhg⟩ := paperRun_spec hP
  have hα := hgrid.2 j
  refine ⟨fun h hh => ?_, fun h1 h2 => ⟨(fitW R.lx R.ly b (σ j b) x y).1, (fitW R.lx R.ly b (σ j b) x y).2,
    (hσ j b h1 h2).2 _, fun h0 hh => ?_, fun hpos => ⟨fitT φ R.lx R.ly b (σ j b) qt (1 - α j) x y,
      fitU φ R.lx R.ly b (σ j b) qu (α j) x y,
      ⟨hqt.2 _ _ _ h1 (by linarith) (by linarith), hqu.2 _ _ _ h2 hα.1 hα.2.le⟩, ?_, fun hh => ?_⟩⟩⟩
  · obtain ⟨a1, a2, -⟩ := (hhg j b x y).1.mp hh
    omega
  · have := ((hhg j b x y).1.mp hh).2.2.1
    exact absurd h0 (ne_of_gt this)
  · rw [(hhg j b x y).1]
    exact ⟨fun h => h.2.2.2, fun h => ⟨h1, h2, hpos, h⟩⟩
  · rw [(hhg j b x y).2, ite_eq_left hh]
    rfl

/-- **T5 (b)**, the fractions: `λ ≤ λ̄_N` always, `λ ≥ λ_N` on a batch bet on (pasts in `[−1,1]`), `λ = 0` elsewhere. -/
theorem paperRun_frac_bounds (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (hgrid : IsGrid α)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hl : 0 < lmax) (hs2 : 0 < s2) (hw0 : 0 < w0) (j : Fin J) (k : Fin R.N)
    (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : Fin k → ℝ) :
    R.lam j k x y z ≤ lamHi lmax (α j) (Real.log (1 / δ)) s2 R.N ∧
    (R.has j (R.bat k) x y → (∀ l, z l ∈ Icc (-1 : ℝ) 1) →
      lamLo lmax (α j) (Real.log (1 / δ)) s2 R.N ≤ R.lam j k x y z) ∧
    (¬ R.has j (R.bat k) x y → R.lam j k x y z = 0) := by
  classical
  have hL : 0 ≤ Real.log (1 / δ) := (Real.log_pos (one_lt_one_div hδ0 hδ1)).le
  have hN : 1 ≤ R.N := Nat.one_le_iff_ne_zero.mpr k.pos.ne'
  have hprior := hP.2.2.2.2.2.1
  have hα := hgrid.2 j
  refine ⟨?_, fun hh hz => ?_, fun hh => ?_⟩
  · rw [paperRun_lam hP]
    split_ifs
    · exact fracFormula_le_lamHi _ _ _ hL hN hs2 _ _ _
    · unfold lamHi
      exact le_min (div_nonneg hl.le (by linarith [hα.1])) (Real.sqrt_nonneg _)
  · rw [paperRun_lam hP, ite_eq_left hh]
    have he : (fun l : Fin k => if R.has j (R.bat (Fin.castLE k.isLt.le l)) x y then (1 : ℝ) else 0) =
        fun l => if l ∈ (Finset.univ.filter fun l : Fin k => R.has j (R.bat (Fin.castLE k.isLt.le l)) x y) then 1 else 0 := by
      funext l; simp
    rw [he]
    exact lamLo_le_fracFormula lmax (α j) _ R.N s2 w0 (v0 j (R.bat k) x y) _ z hw0 ((hprior j (R.bat k)).2.1 x y).1
      ((hprior j (R.bat k)).2.1 x y).2 hα.1 hα.2 hz hs2 hL
  · rw [paperRun_lam hP, ite_eq_right hh]

/-- **T5 (c)**: with `nb = 2` and nearest-integer boundaries the run is a default run. -/
theorem paperRun_default (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (hnb : nb = 2)
    (hcx : NearestCuts n (cx 1) (cx 2)) (hcy : NearestCuts m (cy 1) (cy 2)) : IsDefaultRun R := by
  subst hnb
  obtain ⟨-, -, hlx, hly, hpair, -⟩ := hP
  refine ⟨cx 1, cx 2, cy 1, cy 2, hcx, hcy, fun i => (hlx i).trans (cutLabel_two_eq_default hcx i),
    fun j => (hly j).trans (cutLabel_two_eq_default hcy j), ?_⟩
  rw [hpair.1, defaultPairs, show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} by decide, Finset.sum_insert (by decide),
    Finset.sum_singleton]

/-- The size bound of one side for (d): `n_{<b} = c_b ≥ c n − 2` for `b ∈ [1, nb]`, and `n_1 ≥ c n − 2`. -/
theorem sized_side {p : ℕ} {c : ℕ → ℕ} {π : ℕ → ℝ} {cc : ℝ} (hc : IsBoundaries nb p c) (hnb : 1 ≤ nb)
    (hπ : IsFractions nb π) (hnear : BoundariesNear nb π p c) (hcc : ∀ b, b ≤ nb → cc ≤ π (b + 1) - π b) :
    (∀ b ∈ Set.Icc 1 nb, cc * p - 2 ≤ fitCard (fun i : Fin p => cutLabel nb c i) b) ∧
      cc * p - 2 ≤ batchCount (fun i : Fin p => cutLabel nb c i) 1 := by
  obtain ⟨h0, h1, hmono⟩ := hπ
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hπ1 : cc ≤ π 1 := by have := hcc 0 (Nat.zero_le _); rw [h0] at this; simpa using this
  refine ⟨fun b hb => ?_, ?_⟩
  · rw [fitCard_cutLabel hc (by have := hb.2; omega), extBnd_of_mem hb]
    have e1 := (abs_le.mp (hnear b hb)).1
    have hπb : π 1 ≤ π b := hmono.monotoneOn ⟨by omega, by omega⟩ ⟨by omega, by have := hb.2; omega⟩ hb.1
    have := mul_le_mul_of_nonneg_right (hπ1.trans hπb) hp
    linarith
  · rw [batchCount_cutLabel hc hnb, Nat.cast_sub (extBnd_mono hc (show 1 ≤ 1 + 1 by norm_num)),
      extBnd_of_mem ⟨le_rfl, hnb⟩]
    have e1 := (abs_le.mp (hnear 1 ⟨le_rfl, hnb⟩)).2
    have hc1 : cc ≤ π 2 - π 1 := hcc 1 hnb
    have e2 : π 2 * p - 1 ≤ (extBnd nb p c 2 : ℝ) := by
      unfold extBnd
      rw [ite_eq_right (by norm_num)]
      split_ifs with h2
      · exact (abs_le.mp (hnear 2 ⟨by norm_num, h2⟩)).1 |> fun h => by linarith
      · have : nb = 1 := by omega
        subst this
        rw [show (2 : ℕ) = 1 + 1 by norm_num, h1]
        linarith
    have := mul_le_mul_of_nonneg_right hc1 hp
    show cc * p - 2 ≤ (extBnd nb p c (1 + 1) : ℝ) - c 1
    linarith

/-- **T5 (d)**: at fractions fixed in advance (`nb ≥ 1`, any rounding) the run is sized with `c = min_b (π_{b+1} − π_b)`,
`C₀ = 2`, `B = nb`. -/
theorem paperRun_sized (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (hnb : 1 ≤ nb) (π : ℕ → ℝ)
    (hπ : IsFractions nb π) (hbx : BoundariesNear nb π n cx) (hby : BoundariesNear nb π m cy) :
    R.IsSizedRun (⨅ b : Fin (nb + 1), (π (b + 1) - π b)) 2 nb := by
  obtain ⟨hcx, hcy, hlx, hly, hpair, -⟩ := hP
  have hLx : R.lx = fun i : Fin n => cutLabel nb cx i := funext hlx
  have hLy : R.ly = fun j : Fin m => cutLabel nb cy j := funext hly
  set cc := ⨅ b : Fin (nb + 1), (π (b + 1) - π b) with hcc
  have hbdd : BddBelow (Set.range fun b : Fin (nb + 1) => π (b + 1) - π b) := (Set.finite_range _).bddBelow
  have hcc_le : ∀ b, b ≤ nb → cc ≤ π (b + 1) - π b := fun b hb =>
    ciInf_le hbdd (⟨b, by omega⟩ : Fin (nb + 1))
  have hcc0 : 0 ≤ cc := le_ciInf fun b => by
    have := hπ.2.2 (show (b : ℕ) ∈ Set.Icc 0 (nb + 1) from ⟨by omega, by omega⟩)
      (show (b : ℕ) + 1 ∈ Set.Icc 0 (nb + 1) from ⟨by omega, by omega⟩) (by omega)
    linarith
  obtain ⟨sx1, sx2⟩ := sized_side hcx hnb hπ hbx hcc_le
  obtain ⟨sy1, sy2⟩ := sized_side hcy hnb hπ hby hcc_le
  refine ⟨fun k => (hpair.2.2.1 k).2, fun k => ?_, fun k => ?_, ?_⟩
  · rw [hLx]; exact sx1 _ ⟨(hpair.2.2.1 k).1, (hpair.2.2.1 k).2⟩
  · rw [hLy]; exact sy1 _ ⟨(hpair.2.2.1 k).1, (hpair.2.2.1 k).2⟩
  · have h1mem : (1 : ℕ) ∈ Finset.Icc 1 nb := Finset.mem_Icc.mpr ⟨le_rfl, hnb⟩
    have hge : min (batchCount R.lx 1) (batchCount R.ly 1) ≤ R.N := by
      rw [hpair.1]
      exact Finset.single_le_sum (f := fun b => min (batchCount R.lx b) (batchCount R.ly b)) (fun _ _ => Nat.zero_le _) h1mem
    rw [← hLx] at sx2
    rw [← hLy] at sy2
    have hmn : cc * ((min n m : ℕ) : ℝ) ≤ cc * n ∧ cc * ((min n m : ℕ) : ℝ) ≤ cc * m :=
      ⟨mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_left n m) hcc0,
        mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right n m) hcc0⟩
    calc cc * ((min n m : ℕ) : ℝ) - 2 ≤ min (batchCount R.lx 1 : ℝ) (batchCount R.ly 1) :=
          le_min (by linarith [hmn.1]) (by linarith [hmn.2])
      _ = ((min (batchCount R.lx 1) (batchCount R.ly 1) : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ R.N := by exact_mod_cast hge

end Run

theorem paperRun_admissible_route : Claims.paperRun_admissible := by
  intro 𝒳 H _ _ _ _ φ κ J n m α δ lmax s2 w0 v0 qt qu nb cx cy R hφ _ hgrid hδ0 hδ1 hl0 _ hs2 hw0 hqt hqu hP
  have hadm := paperRun_isAdmissible hP hφ hqt hqu hl0 (fun j => (hgrid.2 j).1)
  exact ⟨hadm, ⟨hadm, fun j k x y => paperRun_witnessRamp hP hqt hqu hgrid j _ x y,
    fun j k x y z => paperRun_frac_bounds hP hgrid hδ0 hδ1 hl0 hs2 hw0 j k x y z⟩,
    fun hnb hcx' hcy' => paperRun_default hP hnb hcx' hcy', fun π hnb hπ hbx hby => paperRun_sized hP hnb π hπ hbx hby⟩

end StatFormal.Wave31tr.RouteRun
