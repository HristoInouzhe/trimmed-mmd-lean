import StatFormal.Wave30tu.Full.Statements
import StatFormal.Wave30tu.Instance.Route
import StatFormal.Wave30ts.Proofs

/-!
# Wave 30tu, full instance — the paper's full `τ_{n,m}` (untrusted proof route)

The certified Wave 30ts `corollary_C`, `corollary_C_coupled`, `corollary_C_grid` (validity, monotonicity, one event of the minimum),
with `τ^A` nonnegative, nondecreasing and valid (Wave 30tr `tauA_scale`, `thmA` through Wave 30tu `upper_valid`), and the kernel
constants `v = √min(κ², D²/2)`, `ρ̄ = D` admissible (Wave 30tp `kernel_consts`). The printed results are the generic Wave 30tu claims.
Rate condition: at the Gaussian constants `v = κ`; the three candidates at `α = 0` are `> √2κ`, `> √2κ` and `≥ √2κ` (Wave 30tu
`ratecond_tauA`, `ratecond_closed`, `ratecond_sharp`, after identifying the two encodings of `Ψ_H`), and each is nondecreasing.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace StatFormal.Wave30tu.Full

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tl StatFormal.Wave30tu
open StatFormal.Wave30tu.Instance

section Thr

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem tauA_props {φ : 𝒳 → H} {κ D δ : ℝ} {n m : ℕ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (x0 : 𝒳) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ StatFormal.Wave30tr.tauA κ D α δ n m) ∧
      MonotoneOn (fun α => StatFormal.Wave30tr.tauA κ D α δ n m) (Ico 0 1) ∧
      StatFormal.Wave30ts.IsValidThreshold φ n m δ (fun α => StatFormal.Wave30tr.tauA κ D α δ n m) :=
  let h := tauA_valid hφ hκ hD x0 hδ0 hδ1 hn hm
  ⟨h.1, h.2.1, h.2.2⟩

theorem kconsts {φ : 𝒳 → H} {κ D : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) : StatFormal.Wave30tp.KernelConsts φ D (√(min (κ ^ 2) (D ^ 2 / 2))) D :=
  (StatFormal.Wave30tp.kernel_consts 𝒳 H φ κ D hφ hκ hD).1

end Thr

theorem tauFull_threshold : Claims.tauFull_threshold := by
  intro 𝒳 H _ _ _ _ _ φ κ D δ n m hne hφ hκ hD hδ0 hδ1 hn hm
  obtain ⟨x0⟩ := hne
  haveI : Nonempty 𝒳 := ⟨x0⟩
  obtain ⟨-, hD0⟩ := consts_nonneg hκ hD x0
  obtain ⟨hnn, hmono, hval⟩ := tauA_props hφ hκ hD x0 hδ0 hδ1 hn hm
  obtain ⟨hV, hM, hN, hO⟩ := StatFormal.Wave30ts.corollary_C 𝒳 H φ κ D (√(min (κ ^ 2) (D ^ 2 / 2))) D _ δ n m hφ hκ
    (kconsts hφ hκ hD) hδ0 hδ1 hn hm hnn hmono hval
  refine ⟨⟨hN, hM, hV⟩, fun α _ => min_le_left _ _, fun h2κ α hα => (min_le_left _ _).trans
    (StatFormal.Wave30tr.thmA_compare κ D α δ n m hD0 h2κ hα.1 hα.2 hδ0 hδ1 hn hm), fun P Q hP hQ => ?_⟩
  obtain ⟨E, hEm, hEp, hE⟩ := hO P Q hP hQ
  exact ⟨E, hEm, hEp, fun z hz => (hE z hz).1⟩

theorem tauFullCpl_threshold : Claims.tauFullCpl_threshold := by
  intro 𝒳 H _ _ _ _ _ φ κ D δ n m hne hφ hκ hD hk0 hdiag hδ0 hδ1 hn hm
  obtain ⟨x0⟩ := hne
  haveI : Nonempty 𝒳 := ⟨x0⟩
  obtain ⟨-, hD0⟩ := consts_nonneg hκ hD x0
  obtain ⟨hnn, hmono, hval⟩ := tauA_props hφ hκ hD x0 hδ0 hδ1 hn hm
  obtain ⟨hV, hM, hN, hO⟩ := StatFormal.Wave30ts.corollary_C_coupled 𝒳 H φ κ D (√(min (κ ^ 2) (D ^ 2 / 2))) D _ δ n m
    hφ hκ (kconsts hφ hκ hD) hk0 hdiag hδ0 hδ1 hn hm hnn hmono hval
  refine ⟨⟨hN, hM, hV⟩, fun α _ => min_le_left _ _, fun h2κ α hα => (min_le_left _ _).trans
    (StatFormal.Wave30tr.thmA_compare κ D α δ n m hD0 h2κ hα.1 hα.2 hδ0 hδ1 hn hm), fun P Q hP hQ => ?_⟩
  obtain ⟨E, hEm, hEp, hE⟩ := hO P Q hP hQ
  exact ⟨E, hEm, hEp, fun z hz => (hE z hz).1⟩

theorem tauFullGrid_threshold : Claims.tauFullGrid_threshold := by
  intro 𝒳 H _ _ _ _ _ φ κ D J lo hi vg ρg δ n m hne hφ hκ hD hk0 hdiag hcov hcell hδ0 hδ1 hn hm
  obtain ⟨x0⟩ := hne
  haveI : Nonempty 𝒳 := ⟨x0⟩
  obtain ⟨-, hD0⟩ := consts_nonneg hκ hD x0
  obtain ⟨hnn, hmono, hval⟩ := tauA_props hφ hκ hD x0 hδ0 hδ1 hn hm
  obtain ⟨hV, hM, hN, hO⟩ := StatFormal.Wave30ts.corollary_C_grid 𝒳 H φ κ D (√(min (κ ^ 2) (D ^ 2 / 2))) D J lo hi vg ρg
    _ δ n m hφ hκ (kconsts hφ hκ hD) hk0 hdiag hcov hcell hδ0 hδ1 hn hm hnn hmono hval
  refine ⟨⟨hN, hM, hV⟩, fun α _ => min_le_left _ _, fun h2κ α hα => (min_le_left _ _).trans
    (StatFormal.Wave30tr.thmA_compare κ D α δ n m hD0 h2κ hα.1 hα.2 hδ0 hδ1 hn hm), fun P Q hP hQ => ?_⟩
  obtain ⟨E, hEm, hEp, hE⟩ := hO P Q hP hQ
  exact ⟨E, hEm, hEp, fun z hz => (hE z hz).1⟩

section Inst

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem full_valid (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ D δ : ℝ} {n m : ℕ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : ValidThreshold φ n m δ (fun α => tauFull κ D α δ n m) :=
  (tauFull_threshold 𝒳 H φ κ D δ n m (nonempty_of_isProbabilityMeasure P) hφ hκ hD hδ0 hδ1 hn hm).1

theorem full_le_tau (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ D δ : ℝ} {n m : ℕ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (h2κ : D ≤ 2 * κ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ∀ α ∈ Ico (0 : ℝ) 1, tauFull κ D α δ n m ≤ tau κ α δ n m :=
  (tauFull_threshold 𝒳 H φ κ D δ n m (nonempty_of_isProbabilityMeasure P) hφ hκ hD hδ0 hδ1 hn hm).2.2.1 h2κ

end Inst

theorem consistency_i_full : Claims.consistency_i_full := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ n m hφ hκ hD htv hδ0 hδ1 hn hm
  exact StatFormal.Wave30tu.consistency_i 𝒳 H P Q φ κ δ _ n m hφ hκ htv hδ0 hδ1 hn hm
    (full_valid P hφ hκ hD hδ0 hδ1 hn hm)

theorem consistency_ii_full : Claims.consistency_ii_full := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ hφ hκ hD h2κ hchar htv0 htv hδ0 hδ1 ε hε η hη0 hη1
  exact StatFormal.Wave30tu.consistency_ii 𝒳 H P Q φ κ δ (fun n m α => tauFull κ D α δ n m)
    (fun n m η α => StatFormal.Wave30tr.tauA κ D α η n m) hφ hκ hchar htv0 htv hδ0 hδ1
    (fun n m hn hm => ⟨full_valid P hφ hκ hD hδ0 hδ1 hn hm, full_le_tau P hφ hκ hD h2κ hδ0 hδ1 hn hm⟩)
    (fun n m hn hm η hη0 hη1 => ⟨(tauA_lower P Q hφ hκ hD hη0 hη1 hn hm).2,
      (tauNM_le_tau P hκ hD h2κ hη0 hη1 hn hm).1⟩) ε hε η hη0 hη1

theorem cor_consistency_full : Claims.cor_consistency_full := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D ι l n m δ hφ hκ hD h2κ hchar htv hn hm hδ0 hδ hrate e he
  exact StatFormal.Wave30tu.cor_consistency 𝒳 H P Q φ κ (fun n m d α => tauFull κ D α d n m)
    (fun n m d α => StatFormal.Wave30tr.tauA κ D α d n m) ι l n m δ hφ hκ hchar htv
    (fun n m hn hm d hd0 hd1 => ⟨full_valid P hφ hκ hD hd0 hd1 hn hm, full_le_tau P hφ hκ hD h2κ hd0 hd1 hn hm,
      (tauA_lower P Q hφ hκ hD hd0 hd1 hn hm).2, (tauNM_le_tau P hκ hD h2κ hd0 hd1 hn hm).1⟩)
    hn hm hδ0 hδ hrate e he

theorem rate_full : Claims.rate_full := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ δ' ω n m ε hφ hκ hD htv hmar hδ0 hδ1 hδ'0 hδ'1 hn hm hε hωε
  exact StatFormal.Wave30tu.rate 𝒳 H P Q φ κ δ δ' _ _ ω n m ε hφ hκ htv hmar hδ0 hδ1 hδ'0 hδ'1 hn hm
    (full_valid P hφ hκ hD hδ0 hδ1 hn hm) (tauA_lower P Q hφ hκ hD hδ'0 hδ'1 hn hm).2 hε hωε

theorem confset_full : Claims.confset_full := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ δ' ω n m hφ hκ hD htv hmar hδ0 hδ1 hδ'0 hδ'1 hn hm
  exact StatFormal.Wave30tu.confset 𝒳 H P Q φ κ δ δ' _ _ ω n m hφ hκ htv hmar hδ0 hδ1 hδ'0 hδ'1 hn hm
    (full_valid P hφ hκ hD hδ0 hδ1 hn hm) (tauA_lower P Q hφ hκ hD hδ'0 hδ'1 hn hm).2

theorem upperfs_interval_full : Claims.upperfs_interval_full := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ ω n m hφ hκ hD htv hmar hδ0 hδ1 hn hm
  exact StatFormal.Wave30tu.upperfs_interval 𝒳 H P Q φ κ δ _ _ ω n m hφ hκ htv hmar hδ0 hδ1 hn hm
    (full_valid P hφ hκ hD hδ0 hδ1 hn hm) (tauA_lower P Q hφ hκ hD hδ0 hδ1 hn hm).2

/-! ### The rate-condition example at the full `τ_{n,n}` -/

theorem v_gauss {κ : ℝ} (hκ : 0 < κ) : √(min (κ ^ 2) ((√2 * κ) ^ 2 / 2)) = κ := by
  have h : (√2 * κ) ^ 2 / 2 = κ ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring
  rw [h, min_self, Real.sqrt_sq hκ.le]

theorem psiH_eq (D v ρ β s c t : ℝ) :
    StatFormal.Wave30ts.psiH D v ρ β s c t = StatFormal.Wave30tu.psiH v D ρ β s c t := by
  simp only [StatFormal.Wave30ts.psiH, StatFormal.Wave30ts.psiMcD, StatFormal.Wave30ts.psiPin,
    StatFormal.Wave30tu.psiH, StatFormal.Wave30tu.psiMcD, StatFormal.Wave30tu.psiPin, neg_mul]

theorem mcd_root_mem {κ v ρ : ℝ} {n : ℕ} (hκ : 0 < κ) (hv : 0 ≤ v) (hn : 1 ≤ n) :
    StatFormal.Wave30ts.psiH (√2 * κ) v ρ 1 (StatFormal.Wave30tp.sNM n n) (StatFormal.Wave30tp.cNM n n)
      (√(1 * v ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ))) + 1 * (√2 * κ)) ≤ Real.exp (-(n : ℝ)) := by
  rw [psiH_eq]
  refine (min_le_left _ _).trans (le_of_eq ?_)
  show StatFormal.Wave30tu.psiMcD v (√2 * κ) 1 (1 / (n : ℝ) + 1 / (n : ℝ))
    (√(1 * v ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ))) + 1 * (√2 * κ)) = _
  unfold StatFormal.Wave30tu.psiMcD
  congr 1
  have hmax : max (√(1 * v ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ))) + 1 * (√2 * κ) -
      √(1 * v ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ)))) 0 = √2 * κ := by
    rw [add_sub_cancel_left, one_mul]; exact max_eq_left (by positivity)
  have hk : (√2 * κ) ^ 2 = 2 * κ ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have hn' : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  rw [hmax, hk, s_eq]
  field_simp

theorem tauPs0_le {κ v ρ : ℝ} {n : ℕ} (hκ : 0 < κ) (hv : 0 ≤ v) (hn : 1 ≤ n) :
    StatFormal.Wave30ts.tauPs (√2 * κ) v ρ 0 (Real.exp (-(n : ℝ))) n n ≤
      √(1 * v ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ))) + 1 * (√2 * κ) := by
  simp only [StatFormal.Wave30ts.tauPs, if_pos rfl]
  exact csInf_le ⟨0, fun t ht => ht.1⟩ ⟨by positivity, mcd_root_mem hκ hv hn⟩

theorem tauPs0_ge {κ v ρ : ℝ} {n : ℕ} (hκ : 0 < κ) (hv : κ ≤ v) (hρ : 0 < ρ) (hn : 1 ≤ n) :
    √2 * κ ≤ StatFormal.Wave30ts.tauPs (√2 * κ) v ρ 0 (Real.exp (-(n : ℝ))) n n := by
  simp only [StatFormal.Wave30ts.tauPs, if_pos rfl]
  refine le_csInf ⟨_, ⟨by positivity, mcd_root_mem hκ (hκ.le.trans hv) hn⟩⟩ fun t ht => ?_
  obtain ⟨ht0, h⟩ := ht
  rw [psiH_eq] at h
  rcases min_le_iff.1 h with h1 | h1
  · have h2 := StatFormal.Wave30tu.ratecond_mcd v (√2 * κ) 1 t n (by linarith) (by positivity) le_rfl hn h1
    have h3 := Real.sqrt_nonneg (1 * v ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ)))
    linarith
  · have h2 := StatFormal.Wave30tu.ratecond_pin v ρ 1 t n (by linarith) hρ le_rfl ht0 hn h1
    have h3 : √2 * κ ≤ √2 * v := mul_le_mul_of_nonneg_left hv (Real.sqrt_nonneg _)
    linarith

/-- The three general candidates at `α = 0`, Gaussian constants, `δ = e^{−n}`. -/
theorem cands_zero {κ : ℝ} {n : ℕ} (hκ0 : 0 < κ) (hn : 1 ≤ n) :
    √2 * κ < StatFormal.Wave30tr.tauA κ (√2 * κ) 0 (Real.exp (-(n : ℝ))) n n ∧
      √2 * κ < StatFormal.Wave30tp.tauP (√2 * κ) (√(min (κ ^ 2) ((√2 * κ) ^ 2 / 2))) (√2 * κ) 0
        (Real.exp (-(n : ℝ))) n n ∧
      √2 * κ ≤ StatFormal.Wave30ts.tauPs (√2 * κ) (√(min (κ ^ 2) ((√2 * κ) ^ 2 / 2))) (√2 * κ) 0
        (Real.exp (-(n : ℝ))) n n := by
  have hv := v_gauss hκ0
  have hD0 : 0 ≤ √2 * κ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have := StatFormal.Wave30tu.ratecond_tauA κ (√2 * κ) (StatFormal.Wave30tr.ek n) (StatFormal.Wave30tr.ek n) n
      hκ0 hD0 (ek_nonneg n) (ek_nonneg n) hn
    simp only [StatFormal.Wave30tr.tauA, StatFormal.Wave30tp.sNM, sub_zero, div_one, one_mul]
    exact lt_of_eq_of_lt this.1.symm this.2
  · rw [hv]
    have := StatFormal.Wave30tu.ratecond_closed κ (√2 * κ) n hκ0 hD0 hn
    simp only [StatFormal.Wave30tp.tauP, if_pos rfl, StatFormal.Wave30tp.sNM]
    exact lt_of_lt_of_eq this.2 this.1.symm
  · rw [hv]
    exact tauPs0_ge hκ0 le_rfl (by positivity) hn

theorem tauCpl0_ge {κ : ℝ} {n : ℕ} (hκ : 0 < κ) (hn : 1 ≤ n) :
    √2 * κ ≤ StatFormal.Wave30ts.tauCpl (√2 * κ) κ 0 (Real.exp (-(n : ℝ))) n n := by
  unfold StatFormal.Wave30ts.tauCpl
  have hk2 : (0 : ℝ) < κ ^ 2 := by positivity
  have hs := s_pos hn
  have hbdd : BddAbove (range fun u : Ico (0 : ℝ) (κ ^ 2) =>
      StatFormal.Wave30ts.tauPs (√2 * κ) (√(κ ^ 2 - (u : ℝ))) (√(κ ^ 2 + (u : ℝ))) 0 (Real.exp (-(n : ℝ))) n n) := by
    refine ⟨√(1 * κ ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ))) + 1 * (√2 * κ), ?_⟩
    rintro _ ⟨u, rfl⟩
    refine (tauPs0_le hκ (Real.sqrt_nonneg _) hn).trans ?_
    have h1 : (√(κ ^ 2 - (u : ℝ))) ^ 2 ≤ κ ^ 2 := by
      rw [Real.sq_sqrt (by linarith [u.2.2])]; linarith [u.2.1]
    have h2 : 1 * √(κ ^ 2 - (u : ℝ)) ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ)) ≤ 1 * κ ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ)) := by
      nlinarith
    have := Real.sqrt_le_sqrt h2
    linarith
  refine le_trans ?_ (le_ciSup hbdd ⟨0, le_rfl, hk2⟩)
  show √2 * κ ≤ StatFormal.Wave30ts.tauPs (√2 * κ) (√(κ ^ 2 - 0)) (√(κ ^ 2 + 0)) 0 (Real.exp (-(n : ℝ))) n n
  rw [sub_zero, add_zero, Real.sqrt_sq hκ.le]
  exact tauPs0_ge hκ le_rfl hκ hn

theorem foldr_max_ge {l : List ℝ} {x : ℝ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with h | h
    · rw [h]; exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem tauGrid0_ge {κ : ℝ} {J : ℕ} {lo hi vg ρg : ℕ → ℝ} {n : ℕ} (hκ : 0 < κ) (hn : 1 ≤ n)
    (hcov : ∀ u ∈ Icc (0 : ℝ) (κ ^ 2), ∃ j < J, lo j ≤ u ∧ u ≤ hi j)
    (hcell : ∀ j < J, 0 ≤ vg j ∧ κ ^ 2 - lo j ≤ vg j ^ 2 ∧ min (√(κ ^ 2 + hi j)) (√2 * κ) ≤ ρg j) :
    √2 * κ ≤ StatFormal.Wave30ts.tauGrid (√2 * κ) vg ρg J 0 (Real.exp (-(n : ℝ))) n n := by
  obtain ⟨j, hj, hlo, hhi⟩ := hcov 0 ⟨le_rfl, by positivity⟩
  obtain ⟨hv0, hv, hρ⟩ := hcell j hj
  have hvk : κ ≤ vg j := by
    have h1 : κ ^ 2 ≤ vg j ^ 2 := by linarith
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hκ.le, Real.sqrt_sq hv0] at this
  have hρpos : 0 < ρg j := by
    have h1 : 0 < √(κ ^ 2 + hi j) := Real.sqrt_pos.2 (by nlinarith)
    have h2 : 0 < √2 * κ := by positivity
    exact lt_of_lt_of_le (lt_min h1 h2) hρ
  refine (tauPs0_ge hκ hvk hρpos hn).trans ?_
  unfold StatFormal.Wave30ts.tauGrid
  exact foldr_max_ge (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)

theorem exp_neg_lt_one {n : ℕ} (hn : 1 ≤ n) : Real.exp (-(n : ℝ)) < 1 :=
  Real.exp_lt_one_iff.2 (by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith)

theorem ratecond_full : Claims.ratecond_full := by
  intro 𝒳 H _ _ _ _ _ φ κ n hφ hκ hD hκ0 hn
  have hδ0 : 0 < Real.exp (-(n : ℝ)) := Real.exp_pos _
  have hδ1 := exp_neg_lt_one hn
  have hD0 : 0 ≤ √2 * κ := by positivity
  have z0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, one_pos⟩
  obtain ⟨hA0, hP0, hS0⟩ := cands_zero hκ0 hn
  obtain ⟨-, hAm, -⟩ := StatFormal.Wave30tr.tauA_scale κ (√2 * κ) _ n n hκ0.le hD0 hδ0 hδ1 hn hn
  obtain ⟨hPm, -⟩ := StatFormal.Wave30tp.plugin_monotone (√2 * κ) (√(min (κ ^ 2) ((√2 * κ) ^ 2 / 2))) (√2 * κ) _ n n
    hD0 (Real.sqrt_nonneg _) hD0 hδ0 hδ1 hn hn
  obtain ⟨hSm, -⟩ := StatFormal.Wave30ts.sharp_tau_monotone (√2 * κ) (√(min (κ ^ 2) ((√2 * κ) ^ 2 / 2))) (√2 * κ) _ n n
    hD0 (Real.sqrt_nonneg _) hD0 hδ0 hδ1 hn hn
  have hmin : ∀ α ∈ Ico (0 : ℝ) 1, √2 * κ ≤ tauFull κ (√2 * κ) α (Real.exp (-(n : ℝ))) n n := by
    intro α hα
    have a1 := hAm z0 hα hα.1
    have a2 := hPm z0 hα hα.1
    have a3 := hSm z0 hα hα.1
    simp only [tauFull, le_min_iff]
    exact ⟨by linarith, by linarith, by linarith⟩
  refine ⟨hmin, fun x y => ?_⟩
  have h0 : (0 : ℝ) ∈ crossSet (Demp φ x y) (fun α => tauFull κ (√2 * κ) α (Real.exp (-(n : ℝ))) n n) :=
    ⟨z0, (Demp_le_D hφ hD hn hn x y z0).trans (hmin 0 z0)⟩
  exact le_antisymm (alphaHat_le_of_mem h0) (alphaHat_nonneg ⟨0, h0⟩)

theorem ratecond_full_cpl : Claims.ratecond_full_cpl := by
  intro 𝒳 H _ _ _ _ _ φ κ n hne hφ hκ hD hk0 hdiag hκ0 hn
  have hδ0 : 0 < Real.exp (-(n : ℝ)) := Real.exp_pos _
  have hδ1 := exp_neg_lt_one hn
  have z0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, one_pos⟩
  obtain ⟨hA0, hP0, hS0⟩ := cands_zero hκ0 hn
  have hC0 := tauCpl0_ge hκ0 hn
  have hmono := (tauFullCpl_threshold 𝒳 H φ κ (√2 * κ) _ n n hne hφ hκ hD hk0 hdiag hδ0 hδ1 hn hn).1.2.1
  have hmin0 : √2 * κ ≤ tauFullCpl κ (√2 * κ) 0 (Real.exp (-(n : ℝ))) n n := by
    simp only [tauFullCpl, le_min_iff]
    exact ⟨hA0.le, hP0.le, hS0, hC0⟩
  have hmin : ∀ α ∈ Ico (0 : ℝ) 1, √2 * κ ≤ tauFullCpl κ (√2 * κ) α (Real.exp (-(n : ℝ))) n n :=
    fun α hα => hmin0.trans (hmono z0 hα hα.1)
  refine ⟨hmin, fun x y => ?_⟩
  have h0 : (0 : ℝ) ∈ crossSet (Demp φ x y) (fun α => tauFullCpl κ (√2 * κ) α (Real.exp (-(n : ℝ))) n n) :=
    ⟨z0, (Demp_le_D hφ hD hn hn x y z0).trans (hmin 0 z0)⟩
  exact le_antisymm (alphaHat_le_of_mem h0) (alphaHat_nonneg ⟨0, h0⟩)

theorem ratecond_full_grid : Claims.ratecond_full_grid := by
  intro 𝒳 H _ _ _ _ _ φ κ J lo hi vg ρg n hne hφ hκ hD hk0 hdiag hcov hcell hκ0 hn
  have hδ0 : 0 < Real.exp (-(n : ℝ)) := Real.exp_pos _
  have hδ1 := exp_neg_lt_one hn
  have z0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, one_pos⟩
  obtain ⟨hA0, hP0, hS0⟩ := cands_zero hκ0 hn
  have hG0 := tauGrid0_ge (n := n) hκ0 hn hcov hcell
  have hmono := (tauFullGrid_threshold 𝒳 H φ κ (√2 * κ) J lo hi vg ρg _ n n hne hφ hκ hD hk0 hdiag hcov hcell
    hδ0 hδ1 hn hn).1.2.1
  have hmin0 : √2 * κ ≤ tauFullGrid κ (√2 * κ) vg ρg J 0 (Real.exp (-(n : ℝ))) n n := by
    simp only [tauFullGrid, le_min_iff]
    exact ⟨hA0.le, hP0.le, hS0, hG0⟩
  have hmin : ∀ α ∈ Ico (0 : ℝ) 1, √2 * κ ≤ tauFullGrid κ (√2 * κ) vg ρg J α (Real.exp (-(n : ℝ))) n n :=
    fun α hα => hmin0.trans (hmono z0 hα hα.1)
  refine ⟨hmin, fun x y => ?_⟩
  have h0 : (0 : ℝ) ∈ crossSet (Demp φ x y) (fun α => tauFullGrid κ (√2 * κ) vg ρg J α (Real.exp (-(n : ℝ))) n n) :=
    ⟨z0, (Demp_le_D hφ hD hn hn x y z0).trans (hmin 0 z0)⟩
  exact le_antisymm (alphaHat_le_of_mem h0) (alphaHat_nonneg ⟨0, h0⟩)

end StatFormal.Wave30tu.Full
