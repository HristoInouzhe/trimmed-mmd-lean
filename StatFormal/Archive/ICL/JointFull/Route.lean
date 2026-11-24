import StatFormal.Archive.ICL.JointFull.Statements
import StatFormal.Lib.Concentration.Symmetrization
import StatFormal.Lib.Concentration.Massart
import StatFormal.Lib.Concentration.RademacherAbs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Route for ICL `thm:joint` with the coverage term (helpers, untrusted)

* `mcdiarmid_tail_nonneg`: McDiarmid tail for bounded differences `c ≥ 0` (the case `c = 0` by a
  decreasing intersection of the `c + 1/(k+1)` events);
* `map_sample_eq_pi`: an independent identically distributed sample has joint law `μ^{⊗m}`;
* risk term: `abs_devJ_le_iSup` (linearity in the law) and `integral_iSup_risk_le`
  (`E D_A ≤ 4 B √(2M log n/m)`, symmetrisation + Massart over the `≤ nᴹ` vectors);
* coverage term (see the second part of the file): `E D_Φ ≤ 4 (K_max/K_min) √(2 log(2n)/m)`
  (symmetrisation, absolute-value contraction with `u ↦ K_min log(max u K_min / K_min)`,
  vertices of the simplex, Massart over the `2n` vectors `±(k_j(Z_i))_i`), with the supremum taken
  over a countable dense subset of the simplex.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Finset

namespace StatFormal.ICL.JointFull

open StatFormal.ICL.Joint StatFormal.Concentration

/-! ### Generic tools -/

theorem mcdiarmid_tail_nonneg {β : Type*} [MeasurableSpace β] (ν : Measure β)
    [IsProbabilityMeasure ν] {m : ℕ} (hm : m ≠ 0) (F : (Fin m → β) → ℝ) (hF : Measurable F)
    {c : ℝ} (hc : 0 ≤ c) (hosc : ∀ x i b, |F (Function.update x i b) - F x| ≤ c) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal (1 - δ) ≤ (Measure.pi fun _ : Fin m => ν)
      {x | F x ≤ (∫ y, F y ∂Measure.pi fun _ : Fin m => ν) + c * √(m * log (1 / δ) / 2)} := by
  set Pm := Measure.pi fun _ : Fin m => ν
  set E := ∫ y, F y ∂Pm
  set s := √(m * log (1 / δ) / 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  set A : ℕ → Set (Fin m → β) := fun k => {x | F x ≤ E + (c + 1 / ((k : ℝ) + 1)) * s} with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k => measurableSet_le hF measurable_const
  have hAp : ∀ k, ENNReal.ofReal (1 - δ) ≤ Pm (A k) := by
    intro k
    have h := mcdiarmid_tail ν hm F hF (c := c + 1 / ((k : ℝ) + 1)) (by linarith [hpos k])
      (fun x i b => (hosc x i b).trans (by linarith [hpos k])) hδ0 hδ1
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    exact h
  have hanti : Antitone A := by
    intro i j hij x hx
    simp only [hA, Set.mem_ofPred_eq] at hx ⊢
    have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by gcongr
    have : (c + 1 / ((j : ℝ) + 1)) * s ≤ (c + 1 / ((i : ℝ) + 1)) * s :=
      mul_le_mul_of_nonneg_right (by linarith) hs0
    linarith
  have hset : {x | F x ≤ E + c * s} = ⋂ k, A k := by
    ext x
    simp only [hA, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h k
      have : c * s ≤ (c + 1 / ((k : ℝ) + 1)) * s :=
        mul_le_mul_of_nonneg_right (by linarith [hpos k]) hs0
      linarith
    · intro h
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos hε (by linarith : (0 : ℝ) < s + 1))
      have h1 := h k
      have h2 : 1 / ((k : ℝ) + 1) * s < ε := by
        calc 1 / ((k : ℝ) + 1) * s ≤ ε / (s + 1) * s :=
              mul_le_mul_of_nonneg_right hk.le hs0
          _ < ε := by
              rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
      nlinarith
  rw [hset, hanti.measure_iInter (fun k => (hAm k).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
  exact le_iInf hAp

theorem map_sample_eq_pi {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : Measure Z) {m : ℕ} (X : Fin m → Ω → Z)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ) :
    P.map (fun ω i => X i ω) = Measure.pi (fun _ : Fin m => μ) := by
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).1 hind]
  congr 1; funext i; exact hlaw i

/-! ### Risk term -/

theorem abs_devJ_le_iSup {ι Z : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] {m : ℕ} (L : ι → Z → ℝ) {B : ℝ}
    (hB : ∀ j z, 0 ≤ L j z ∧ L j z ≤ B) (law : ι → ℝ) (hlaw : ProbVec law) (zs : Fin m → Z) :
    |devJ μ m L law zs| ≤ ⨆ j, |empDev μ L m zs j| := by
  have hB' : ∀ j z, |L j z| ≤ B := fun j z => by
    rw [abs_of_nonneg (hB j z).1]; exact (hB j z).2
  have hbdd : BddAbove (Set.range fun j => |empDev μ L m zs j|) :=
    bddAbove_of_abs_le (C := 2 * B) fun j => by rw [abs_abs]; exact abs_empDev_le μ hB' zs j
  set S := ⨆ j, |empDev μ L m zs j|
  have hd : ∀ j, (1 / (m : ℝ)) * ∑ i, L j (zs i) - ∫ z, L j z ∂μ = empDev μ L m zs j := by
    intro j; rw [empDev, one_div]
  unfold devJ
  simp_rw [hd]
  calc |∑ j, law j * empDev μ L m zs j| ≤ ∑ j, |law j * empDev μ L m zs j| :=
        abs_sum_le_sum_abs _ _
    _ = ∑ j, law j * |empDev μ L m zs j| := by
        refine sum_congr rfl fun j _ => ?_; rw [abs_mul, abs_of_nonneg (hlaw.1 j)]
    _ ≤ ∑ j, law j * S := sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (le_ciSup hbdd j) (hlaw.1 j)
    _ = S := by rw [← sum_mul, hlaw.2, one_mul]

theorem log_two_mul_pow_le {n M : ℕ} (hn : 2 ≤ n) (hM : 1 ≤ M) :
    log (2 * (n : ℝ) ^ M) ≤ 2 * M * log n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have h1 : log 2 ≤ log n := Real.log_le_log (by norm_num) hn'
  have h2 : 0 ≤ log (n : ℝ) := Real.log_nonneg (by linarith)
  nlinarith

/-- Massart bound for the Rademacher average of a finite class at a fixed sample. -/
theorem radE_iSup_abs_finite_le {ι Z : Type*} [Fintype ι] [Nonempty ι] {m : ℕ} (hm : m ≠ 0)
    (L : ι → Z → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j z, |L j z| ≤ B) (zs : Fin m → Z) :
    radE (fun σ => ⨆ t, |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * L t (zs i)|) ≤
      B * √(2 * log (2 * Fintype.card ι)) / √m := by
  classical
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
  set V : Finset (Fin m → ℝ) := univ.image (fun t => fun i => L t (zs i)) with hVdef
  have hV : V.Nonempty := univ_nonempty.image _
  have hR : ∀ v ∈ V, ∑ i, v i ^ 2 ≤ (B * √m) ^ 2 := by
    intro v hv
    obtain ⟨t, -, rfl⟩ := mem_image.1 hv
    rw [mul_pow, Real.sq_sqrt hmpos.le]
    calc ∑ i, L t (zs i) ^ 2 ≤ ∑ _i : Fin m, B ^ 2 := sum_le_sum fun i _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB _ _) 2
      _ = B ^ 2 * m := by simp [Finset.sum_const]; ring
  have hpt : ∀ σ : Fin m → Bool, (⨆ t, |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * L t (zs i)|) ≤
      (m : ℝ)⁻¹ * V.sup' hV (fun v => |rsum v σ|) := by
    intro σ
    refine ciSup_le fun t => ?_
    rw [abs_mul, abs_inv, Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    show |rsum (fun i => L t (zs i)) σ| ≤ _
    exact le_sup' (fun v => |rsum v σ|) (show (fun i => L t (zs i)) ∈ V from
      mem_image_of_mem (fun t => fun i => L t (zs i)) (mem_univ t))
  have hcard : (V.card : ℝ) ≤ Fintype.card ι := by
    have := card_image_le (s := (univ : Finset ι)) (f := fun t => fun i => L t (zs i))
    rw [card_univ] at this
    exact_mod_cast this
  have hVpos : (0 : ℝ) < V.card := Nat.cast_pos.2 hV.card_pos
  calc radE (fun σ => ⨆ t, |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * L t (zs i)|)
      ≤ radE (fun σ => (m : ℝ)⁻¹ * V.sup' hV (fun v => |rsum v σ|)) := radE_mono hpt
    _ = (m : ℝ)⁻¹ * radE (fun σ => V.sup' hV (fun v => |rsum v σ|)) := radE_const_mul _ _
    _ ≤ (m : ℝ)⁻¹ * (B * √m * √(2 * log (2 * V.card))) :=
        mul_le_mul_of_nonneg_left (radE_sup_abs_le_massart V hV (by positivity) hR)
          (by positivity)
    _ ≤ (m : ℝ)⁻¹ * (B * √m * √(2 * log (2 * Fintype.card ι))) := by
        gcongr
    _ = B * √(2 * log (2 * Fintype.card ι)) / √m := by
        have hsp : 0 < √(m : ℝ) := Real.sqrt_pos.2 hmpos
        rw [show (m : ℝ)⁻¹ = (√(m : ℝ))⁻¹ * (√(m : ℝ))⁻¹ by
          rw [← mul_inv, Real.mul_self_sqrt hmpos.le]]
        field_simp

theorem integral_iSup_risk_le {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {n M m : ℕ} (hn : 2 ≤ n) (hM : 1 ≤ M) (hm : m ≠ 0)
    (L : (Fin M → Fin n) → Z → ℝ) (hLm : ∀ j, Measurable (L j)) {B : ℝ}
    (hB : ∀ j z, 0 ≤ L j z ∧ L j z ≤ B) :
    ∫ zs, ⨆ t, |empDev μ L m zs t| ∂(Measure.pi fun _ : Fin m => μ) ≤
      4 * B * √(2 * M * log n / m) := by
  haveI : Nonempty (Fin M → Fin n) := ⟨fun _ => ⟨0, by omega⟩⟩
  have hB' : ∀ j z, |L j z| ≤ B := fun j z => by
    rw [abs_of_nonneg (hB j z).1]; exact (hB j z).2
  have hB0 : 0 ≤ B := by
    obtain ⟨z⟩ := nonempty_of_isProbabilityMeasure μ
    obtain ⟨j⟩ := ‹Nonempty (Fin M → Fin n)›
    exact (hB j z).1.trans (hB j z).2
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
  have hsym := integral_iSup_abs_empDev_le μ hLm hB' hm
  have hcardι : (Fintype.card (Fin M → Fin n) : ℝ) = (n : ℝ) ^ M := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
  set K := B * √(2 * log (2 * (n : ℝ) ^ M)) / √m with hK
  have hrad : ∀ zs : Fin m → Z,
      radE (fun σ => ⨆ t, |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * L t (zs i)|) ≤ K := by
    intro zs
    have := radE_iSup_abs_finite_le hm L hB0 hB' zs
    rwa [hcardι] at this
  have hint : ∫ zs, radE (fun σ => ⨆ t, |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * L t (zs i)|)
      ∂(Measure.pi fun _ : Fin m => μ) ≤ K := by
    have := integral_mono_of_nonneg (μ := Measure.pi fun _ : Fin m => μ)
      (f := fun zs => radE (fun σ => ⨆ t, |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * L t (zs i)|))
      (g := fun _ => K)
      (ae_of_all _ fun zs => radE_nonneg fun σ =>
        le_ciSup_of_le (bddAbove_of_abs_le
          (f := fun t : Fin M → Fin n => |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * L t (zs i)|)
          (C := B) fun t => by
          rw [abs_abs]
          exact abs_mean_le hm fun i => abs_rsign_mul_le hB' (σ i) t (zs i))
          (Classical.arbitrary _) (abs_nonneg _))
      (integrable_const K) (ae_of_all _ hrad)
    rwa [integral_const, probReal_univ, one_smul] at this
  have hlog := log_two_mul_pow_le hn hM
  have hK2 : 2 * K ≤ 4 * B * √(2 * M * log n / m) := by
    have hsqrt : √(2 * log (2 * (n : ℝ) ^ M)) / √m ≤ 2 * √(2 * M * log n / m) := by
      rw [← Real.sqrt_div' _ hmpos.le]
      rw [show (2 : ℝ) * √(2 * M * log n / m) = √(2 ^ 2 * (2 * M * log n / m)) by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt
      have hln : 0 ≤ (M : ℝ) * log n := mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
      rw [show (2 : ℝ) ^ 2 * (2 * M * log n / m) = (8 * (M * log n)) / m by ring]
      exact div_le_div_of_nonneg_right (by nlinarith) hmpos.le
    rw [hK, mul_div_assoc]
    have := mul_le_mul_of_nonneg_left hsqrt hB0
    linarith
  linarith

/-! ### Coverage term -/

/-- The probability simplex on `Fin n`. -/
def simplex (n : ℕ) : Set (Fin n → ℝ) := {w | ProbVec w}

/-- `ρ(z; w) = Σ_j w_j k_j(z)`. -/
def rho {Z : Type*} {n : ℕ} (k : Fin n → Z → ℝ) (w : Fin n → ℝ) (z : Z) : ℝ := ∑ j, w j * k j z

/-- The shifted log-coverage class `log(ρ(·; w)/K_min)`. -/
def gcov {Z : Type*} {n : ℕ} (k : Fin n → Z → ℝ) (Kmin : ℝ) (w : Fin n → ℝ) (z : Z) : ℝ :=
  log (rho k w z / Kmin)

section Coverage

variable {Z : Type*} [MeasurableSpace Z] {n : ℕ} {k : Fin n → Z → ℝ} {Kmin Kmax : ℝ}

theorem rho_mem (hk : ∀ j z, Kmin ≤ k j z ∧ k j z ≤ Kmax) {w : Fin n → ℝ} (hw : w ∈ simplex n)
    (z : Z) : Kmin ≤ rho k w z ∧ rho k w z ≤ Kmax := by
  constructor
  · calc Kmin = ∑ j, w j * Kmin := by rw [← sum_mul, hw.2, one_mul]
      _ ≤ rho k w z := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hk j z).1 (hw.1 j)
  · calc rho k w z ≤ ∑ j, w j * Kmax :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hk j z).2 (hw.1 j)
      _ = Kmax := by rw [← sum_mul, hw.2, one_mul]

theorem gcov_mem (hK : 0 < Kmin) (hk : ∀ j z, Kmin ≤ k j z ∧ k j z ≤ Kmax) {w : Fin n → ℝ}
    (hw : w ∈ simplex n) (z : Z) :
    0 ≤ gcov k Kmin w z ∧ gcov k Kmin w z ≤ log (Kmax / Kmin) := by
  have h := rho_mem hk hw z
  constructor
  · exact Real.log_nonneg (by rw [le_div_iff₀ hK]; linarith [h.1])
  · exact Real.log_le_log (div_pos (by linarith [h.1]) hK)
      (div_le_div_of_nonneg_right h.2 hK.le)

theorem measurable_gcov (hkm : ∀ j, Measurable (k j)) (Kmin : ℝ) (w : Fin n → ℝ) :
    Measurable (gcov k Kmin w) :=
  ((Finset.measurable_fun_sum _ fun j _ => (hkm j).const_mul (w j)).div_const _).log

theorem abs_log_sub_log_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : |log x - log y| ≤ |x - y| := by
  have key : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → b ≤ a → log a - log b ≤ a - b := by
    intro a b ha hb hab
    rw [← Real.log_div (by linarith) (by linarith)]
    refine (Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))).trans ?_
    rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
    nlinarith
  rcases le_total y x with h | h
  · have := key x y hx hy h
    have hl : log y ≤ log x := Real.log_le_log (by linarith) h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; exact this
  · have := key y x hy hx h
    have hl : log x ≤ log y := Real.log_le_log (by linarith) h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

theorem abs_gcov_sub_le (hK : 0 < Kmin) (hk : ∀ j z, Kmin ≤ k j z ∧ k j z ≤ Kmax)
    {w w' : Fin n → ℝ} (hw : w ∈ simplex n) (hw' : w' ∈ simplex n) {η : ℝ}
    (hη : ∀ j, |w j - w' j| ≤ η) (z : Z) :
    |gcov k Kmin w z - gcov k Kmin w' z| ≤ n * η * Kmax / Kmin := by
  have h1 := rho_mem hk hw z
  have h2 := rho_mem hk hw' z
  have hKmax : 0 ≤ Kmax := by linarith [h1.1, h1.2]
  refine (abs_log_sub_log_le (by rw [le_div_iff₀ hK]; linarith [h1.1])
    (by rw [le_div_iff₀ hK]; linarith [h2.1])).trans ?_
  rw [← sub_div, abs_div, abs_of_pos hK]
  refine div_le_div_of_nonneg_right ?_ hK.le
  unfold rho
  rw [← sum_sub_distrib]
  calc |∑ j, (w j * k j z - w' j * k j z)| ≤ ∑ j, |w j * k j z - w' j * k j z| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, η * Kmax := sum_le_sum fun j _ => by
        rw [← sub_mul, abs_mul]
        have hkj : |k j z| ≤ Kmax := by
          rw [abs_of_nonneg (by linarith [(hk j z).1])]; exact (hk j z).2
        exact mul_le_mul (hη j) hkj (abs_nonneg _) ((abs_nonneg _).trans (hη j))
    _ = n * η * Kmax := by simp [Finset.sum_const]; ring

/-- `log ρ` and the shifted class have the same deviation. -/
theorem empDev_log_rho (μ : Measure Z) [IsProbabilityMeasure μ] (hK : 0 < Kmin)
    (hk : ∀ j z, Kmin ≤ k j z ∧ k j z ≤ Kmax) (hkm : ∀ j, Measurable (k j)) {m : ℕ}
    (hm : m ≠ 0) {w : Fin n → ℝ} (hw : w ∈ simplex n) (zs : Fin m → Z) :
    -(1 / (m : ℝ)) * ∑ i, log (rho k w (zs i)) + ∫ z, log (rho k w z) ∂μ =
      -empDev μ (gcov k Kmin) m zs w := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hsplit : ∀ z, gcov k Kmin w z = log (rho k w z) - log Kmin := fun z => by
    rw [gcov, Real.log_div (by linarith [(rho_mem hk hw z).1]) hK.ne']
  have hlogm : Measurable fun z => log (rho k w z) :=
    (Finset.measurable_fun_sum _ fun j _ => (hkm j).const_mul (w j)).log
  have hlogb : ∀ z, |log (rho k w z)| ≤ |log Kmin| + |log Kmax| := fun z => by
    have h := rho_mem hk hw z
    have h1 : log Kmin ≤ log (rho k w z) := Real.log_le_log hK h.1
    have h2 : log (rho k w z) ≤ log Kmax := Real.log_le_log (by linarith [h.1]) h.2
    rw [abs_le]; constructor
    · linarith [neg_abs_le (log Kmin), abs_nonneg (log Kmax)]
    · linarith [le_abs_self (log Kmax), abs_nonneg (log Kmin)]
  have hint : Integrable (fun z => log (rho k w z)) μ :=
    Integrable.of_bound hlogm.aestronglyMeasurable _ (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact hlogb z)
  simp only [empDev, hsplit]
  rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  ring

theorem oneSlot_mem {M : ℕ} (hM : 1 ≤ M) {law : (Fin M → Fin n) → ℝ} (hlaw : ProbVec law) :
    oneSlot law ∈ simplex n := by
  classical
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨fun j => mul_nonneg (by positivity) (sum_nonneg fun t _ =>
    mul_nonneg (hlaw.1 t) (Nat.cast_nonneg _)), ?_⟩
  unfold oneSlot
  rw [← mul_sum, Finset.sum_comm]
  have hc : ∀ t : Fin M → Fin n, ∑ j, law t * ((univ.filter fun s => t s = j).card : ℝ) =
      law t * M := by
    intro t
    rw [← mul_sum]
    congr 1
    have := card_eq_sum_card_fiberwise (f := t) (s := univ) (t := univ)
      (fun _ _ => Finset.mem_coe.2 (mem_univ _))
    rw [card_univ, Fintype.card_fin] at this
    exact_mod_cast this.symm
  simp_rw [hc]
  rw [← sum_mul, hlaw.2, one_mul, one_div, inv_mul_cancel₀ hMR.ne']

theorem iSup_abs_mul {T : Type*} [Nonempty T] {c : ℝ} (hc : 0 ≤ c) (f : T → ℝ) :
    (⨆ t, |c * f t|) = c * ⨆ t, |f t| := by
  simp_rw [abs_mul, abs_of_nonneg hc]
  exact (Real.mul_iSup_of_nonneg hc _).symm

/-- Device (b): the supremum over the simplex is controlled by a countable dense subset. -/
theorem abs_empDev_le_iSup_dense (μ : Measure Z) [IsProbabilityMeasure μ] (hK : 0 < Kmin)
    (hk : ∀ j z, Kmin ≤ k j z ∧ k j z ≤ Kmax) (hkm : ∀ j, Measurable (k j)) {m : ℕ}
    (hm : m ≠ 0) (T₀ : Set (Fin n → ℝ)) [Nonempty T₀] (hT₀ : T₀ ⊆ simplex n)
    (hdense : simplex n ⊆ closure T₀) {w : Fin n → ℝ} (hw : w ∈ simplex n) (zs : Fin m → Z) :
    |empDev μ (gcov k Kmin) m zs w| ≤
      ⨆ b : T₀, |empDev μ (fun b : T₀ => gcov k Kmin b.1) m zs b| := by
  have hgB : ∀ (b : T₀) z, |gcov k Kmin b.1 z| ≤ log (Kmax / Kmin) := fun b z => by
    have h := gcov_mem hK hk (hT₀ b.2) z
    rw [abs_of_nonneg h.1]; exact h.2
  have hbdd : BddAbove (Set.range fun b : T₀ =>
      |empDev μ (fun b : T₀ => gcov k Kmin b.1) m zs b|) :=
    bddAbove_of_abs_le (C := 2 * log (Kmax / Kmin)) fun b => by
      rw [abs_abs]; exact abs_empDev_le μ hgB zs b
  have hKmax : 0 ≤ Kmax := by
    obtain ⟨z⟩ := nonempty_of_isProbabilityMeasure μ
    obtain ⟨b⟩ := ‹Nonempty T₀›
    have := rho_mem hk (hT₀ b.2) z
    linarith [this.1, this.2]
  set Lc := 2 * n * Kmax / Kmin with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set η := ε / (Lc + 1) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 (hdense hw) η hη
  have hη' : ∀ j, |w j - b j| ≤ η := fun j => by
    rw [← Real.dist_eq]; exact (dist_le_pi_dist w b j).trans hdist.le
  set C := n * η * Kmax / Kmin with hC
  have hpt : ∀ z, |gcov k Kmin w z - gcov k Kmin b z| ≤ C := fun z =>
    abs_gcov_sub_le hK hk hw (hT₀ hb) hη' z
  have hint : ∀ v ∈ simplex n, Integrable (gcov k Kmin v) μ := fun v hv =>
    Integrable.of_bound (measurable_gcov hkm Kmin v).aestronglyMeasurable (log (Kmax / Kmin))
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (gcov_mem hK hk hv z).1]
        exact (gcov_mem hK hk hv z).2)
  have hdiff : |empDev μ (gcov k Kmin) m zs w - empDev μ (gcov k Kmin) m zs b| ≤ 2 * C := by
    have heq : empDev μ (gcov k Kmin) m zs w - empDev μ (gcov k Kmin) m zs b =
        (m : ℝ)⁻¹ * ∑ i, (gcov k Kmin w (zs i) - gcov k Kmin b (zs i)) -
          ∫ z, (gcov k Kmin w z - gcov k Kmin b z) ∂μ := by
      rw [integral_sub (hint w hw) (hint b (hT₀ hb)), sum_sub_distrib]
      simp only [empDev]; ring
    rw [heq]
    refine (abs_sub _ _).trans ?_
    have h1 := abs_mean_le hm fun i => hpt (zs i)
    have h2 : |∫ z, (gcov k Kmin w z - gcov k Kmin b z) ∂μ| ≤ C := by
      have := norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun z => gcov k Kmin w z - gcov k Kmin b z) (C := C)
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hpt z)
      simpa [Real.norm_eq_abs] using this
    linarith
  have hb' : |empDev μ (gcov k Kmin) m zs b| ≤
      ⨆ b : T₀, |empDev μ (fun b : T₀ => gcov k Kmin b.1) m zs b| :=
    le_ciSup hbdd ⟨b, hb⟩
  have h2C : 2 * C < ε := by
    have : 2 * C = Lc * η := by rw [hC, hLc]; ring
    rw [this, hηdef, mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  have := abs_sub_abs_le_abs_sub (empDev μ (gcov k Kmin) m zs w) (empDev μ (gcov k Kmin) m zs b)
  linarith

theorem abs_iSup_abs_empDev_update_le {T : Type*} [Nonempty T] (μ : Measure Z)
    [IsProbabilityMeasure μ] {g : T → Z → ℝ} {B : ℝ} (hg : ∀ t z, 0 ≤ g t z ∧ g t z ≤ B)
    {m : ℕ} (zs : Fin m → Z) (i : Fin m) (b : Z) :
    |(⨆ t, |empDev μ g m (Function.update zs i b) t|) - (⨆ t, |empDev μ g m zs t|)| ≤
      B / m := by
  have hB : ∀ t z, |g t z| ≤ B := fun t z => by rw [abs_of_nonneg (hg t z).1]; exact (hg t z).2
  refine abs_iSup_sub_iSup_le (bddAbove_of_abs_le (C := 2 * B) fun t => by
      rw [abs_abs]; exact abs_empDev_le μ hB _ t)
    (bddAbove_of_abs_le (C := 2 * B) fun t => by rw [abs_abs]; exact abs_empDev_le μ hB _ t)
    fun t => (abs_abs_sub_abs_le _ _).trans ?_
  rw [empDev_update_sub, abs_mul, abs_inv, Nat.abs_cast, div_eq_inv_mul]
  gcongr
  rw [abs_le]; constructor <;> linarith [hg t b, hg t (zs i)]

/-- Rademacher average of the coverage class at a fixed sample
(contraction with `u ↦ K_min log(max u K_min/K_min)`, then Massart over the `k_j`). -/
theorem radE_cov_le (hK : 0 < Kmin) (hk : ∀ j z, Kmin ≤ k j z ∧ k j z ≤ Kmax) (hn : 1 ≤ n)
    {m : ℕ} (hm : m ≠ 0) (T₀ : Set (Fin n → ℝ)) [Nonempty T₀] (hT₀ : T₀ ⊆ simplex n)
    (zs : Fin m → Z) :
    radE (fun σ => ⨆ b : T₀, |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * gcov k Kmin b.1 (zs i)|) ≤
      2 * (Kmax / Kmin) * √(2 * log (2 * n)) / √m := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hKmax : 0 ≤ Kmax := by
    obtain ⟨j⟩ := ‹Nonempty (Fin n)›
    linarith [(hk j (zs ⟨0, Nat.pos_of_ne_zero hm⟩)).1, (hk j (zs ⟨0, Nat.pos_of_ne_zero hm⟩)).2]
  set φ : Fin m → ℝ → ℝ := fun _ u => Kmin * log (max u Kmin / Kmin) with hφdef
  have hφ : ∀ i x y, |φ i x - φ i y| ≤ |x - y| := by
    intro i x y
    simp only [hφdef]
    rw [← mul_sub, abs_mul, abs_of_pos hK]
    have h1 : 1 ≤ max x Kmin / Kmin := by rw [le_div_iff₀ hK]; simp
    have h2 : 1 ≤ max y Kmin / Kmin := by rw [le_div_iff₀ hK]; simp
    calc Kmin * |log (max x Kmin / Kmin) - log (max y Kmin / Kmin)|
        ≤ Kmin * |max x Kmin / Kmin - max y Kmin / Kmin| :=
          mul_le_mul_of_nonneg_left (abs_log_sub_log_le h1 h2) hK.le
      _ = |max x Kmin - max y Kmin| := by
          rw [← sub_div, abs_div, abs_of_pos hK]; field_simp
      _ ≤ |x - y| := abs_max_sub_max_le_abs _ _ _
  have hφ0 : ∀ i, φ i 0 = 0 := fun i => by simp [hφdef, max_eq_right hK.le, div_self hK.ne']
  set a : T₀ → Fin m → ℝ := fun b i => rho k b.1 (zs i) with hadef
  have ha : ∀ b i, |a b i| ≤ Kmax := fun b i => by
    have h := rho_mem hk (hT₀ b.2) (zs i)
    rw [abs_of_nonneg (by linarith [h.1])]; exact h.2
  have hga : ∀ (b : T₀) i, gcov k Kmin b.1 (zs i) = Kmin⁻¹ * φ i (a b i) := fun b i => by
    have h := rho_mem hk (hT₀ b.2) (zs i)
    simp only [hφdef, hadef, gcov, max_eq_left h.1]
    field_simp
  have hc : (0 : ℝ) ≤ (m : ℝ)⁻¹ * Kmin⁻¹ := by positivity
  have hrew : ∀ σ : Fin m → Bool,
      (⨆ b : T₀, |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * gcov k Kmin b.1 (zs i)|) =
        (m : ℝ)⁻¹ * Kmin⁻¹ * ⨆ b : T₀, |∑ i, rsign (σ i) * φ i (a b i)| := by
    intro σ
    rw [← iSup_abs_mul hc]
    congr 1; funext b; congr 1
    simp_rw [hga, mul_sum]
    exact sum_congr rfl fun i _ => by ring
  simp_rw [hrew]
  rw [radE_const_mul]
  have hcon := radE_iSup_abs_contraction a ha φ hφ hφ0
  -- vertices: `sup_b |∑ σᵢ ρ_b(zᵢ)| ≤ sup_j |∑ σᵢ k_j(zᵢ)|`
  have hk' : ∀ j z, |k j z| ≤ Kmax := fun j z => by
    rw [abs_of_nonneg (by linarith [(hk j z).1, hK])]; exact (hk j z).2
  have hvert : ∀ σ : Fin m → Bool, (⨆ b : T₀, |∑ i, rsign (σ i) * a b i|) ≤
      (m : ℝ) * ⨆ j, |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * k j (zs i)| := by
    intro σ
    rw [iSup_abs_mul (by positivity), ← mul_assoc, mul_inv_cancel₀ hmpos.ne', one_mul]
    have hbddj : BddAbove (Set.range fun j => |∑ i, rsign (σ i) * k j (zs i)|) :=
      bddAbove_of_abs_le (C := m * Kmax) fun j => by
        rw [abs_abs]
        refine (abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i, |rsign (σ i) * k j (zs i)| ≤ ∑ _i : Fin m, Kmax := sum_le_sum fun i _ => by
              rw [abs_mul, abs_rsign, one_mul]; exact hk' _ _
          _ = m * Kmax := by simp [Finset.sum_const]
    refine ciSup_le fun b => ?_
    have hb := hT₀ b.2
    have heq : ∑ i, rsign (σ i) * a b i = ∑ j, b.1 j * ∑ i, rsign (σ i) * k j (zs i) := by
      simp only [hadef, rho, mul_sum]
      rw [Finset.sum_comm]
      exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring
    rw [heq]
    calc |∑ j, b.1 j * ∑ i, rsign (σ i) * k j (zs i)|
        ≤ ∑ j, b.1 j * |∑ i, rsign (σ i) * k j (zs i)| := by
          refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun j _ => ?_))
          rw [abs_mul, abs_of_nonneg (hb.1 j)]
      _ ≤ ∑ j, b.1 j * ⨆ j, |∑ i, rsign (σ i) * k j (zs i)| :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (le_ciSup hbddj j) (hb.1 j)
      _ = ⨆ j, |∑ i, rsign (σ i) * k j (zs i)| := by rw [← sum_mul, hb.2, one_mul]
  have hmass := radE_iSup_abs_finite_le hm k hKmax hk' zs
  rw [Fintype.card_fin] at hmass
  calc (m : ℝ)⁻¹ * Kmin⁻¹ * radE (fun σ => ⨆ b : T₀, |∑ i, rsign (σ i) * φ i (a b i)|)
      ≤ (m : ℝ)⁻¹ * Kmin⁻¹ * (2 * radE (fun σ => ⨆ b : T₀, |∑ i, rsign (σ i) * a b i|)) :=
        mul_le_mul_of_nonneg_left hcon hc
    _ ≤ (m : ℝ)⁻¹ * Kmin⁻¹ * (2 * radE (fun σ : Fin m → Bool =>
          (m : ℝ) * ⨆ j, |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * k j (zs i)|)) := by
        gcongr
        exact radE_mono hvert
    _ = 2 * Kmin⁻¹ * radE (fun σ : Fin m → Bool =>
          ⨆ j, |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * k j (zs i)|) := by
        rw [radE_const_mul]; field_simp
    _ ≤ 2 * Kmin⁻¹ * (Kmax * √(2 * log (2 * n)) / √m) := by gcongr
    _ = 2 * (Kmax / Kmin) * √(2 * log (2 * n)) / √m := by ring

theorem integral_iSup_cov_le (μ : Measure Z) [IsProbabilityMeasure μ] (hK : 0 < Kmin)
    (hk : ∀ j z, Kmin ≤ k j z ∧ k j z ≤ Kmax) (hkm : ∀ j, Measurable (k j)) (hn : 1 ≤ n)
    {m : ℕ} (hm : m ≠ 0) (T₀ : Set (Fin n → ℝ)) [Countable T₀] [Nonempty T₀]
    (hT₀ : T₀ ⊆ simplex n) :
    ∫ zs, ⨆ b : T₀, |empDev μ (fun b : T₀ => gcov k Kmin b.1) m zs b|
      ∂(Measure.pi fun _ : Fin m => μ) ≤ 4 * (Kmax / Kmin) * √(2 * log (2 * n) / m) := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
  have hgB : ∀ (b : T₀) z, |gcov k Kmin b.1 z| ≤ log (Kmax / Kmin) := fun b z => by
    have h := gcov_mem hK hk (hT₀ b.2) z
    rw [abs_of_nonneg h.1]; exact h.2
  have hsym := integral_iSup_abs_empDev_le μ (g := fun b : T₀ => gcov k Kmin b.1)
    (fun b => measurable_gcov hkm Kmin b.1) hgB hm
  set K := 2 * (Kmax / Kmin) * √(2 * log (2 * n)) / √m with hKdef
  have hint : ∫ zs, radE (fun σ => ⨆ b : T₀,
      |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * gcov k Kmin b.1 (zs i)|)
      ∂(Measure.pi fun _ : Fin m => μ) ≤ K := by
    have := integral_mono_of_nonneg (μ := Measure.pi fun _ : Fin m => μ)
      (f := fun zs => radE (fun σ => ⨆ b : T₀,
        |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * gcov k Kmin b.1 (zs i)|))
      (g := fun _ => K)
      (ae_of_all _ fun zs => radE_nonneg fun σ =>
        le_ciSup_of_le (bddAbove_of_abs_le
          (f := fun b : T₀ => |(m : ℝ)⁻¹ * ∑ i, rsign (σ i) * gcov k Kmin b.1 (zs i)|)
          (C := log (Kmax / Kmin)) fun b => by
            rw [abs_abs]
            exact abs_mean_le hm fun i => abs_rsign_mul_le hgB (σ i) b (zs i))
          (Classical.arbitrary _) (abs_nonneg _))
      (integrable_const K) (ae_of_all _ fun zs => radE_cov_le hK hk hn hm T₀ hT₀ zs)
    rwa [integral_const, probReal_univ, one_smul] at this
  have hfin : 2 * K = 4 * (Kmax / Kmin) * √(2 * log (2 * n) / m) := by
    rw [hKdef, Real.sqrt_div' _ hmpos.le]; ring
  linarith

end Coverage

end StatFormal.ICL.JointFull
