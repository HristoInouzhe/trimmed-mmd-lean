import StatFormal.Archive.Wave15b.Statements

/-!
# Route: B `lem:app-dual-sandwich` and C `lem:weighted-duality` (untrusted)

* Fenchel–Young `X^*(u) ≥ ⟨u, z⟩ − X(z)` (lower bound, integrated against every plan);
* on the grid (in `𝒰`) `X^* ≤ χ` (biconjugate below the function), and `X(Z_i) ≤ (‖Z_i‖² − f_i)/2` for `i ∈ I`;
* `∫‖u − z‖² dπ = M₂(μ) + M₂(P̂) − 2∫⟨u, z⟩ dπ` for every plan, so `W₂² ≥ M₂ + M₂ − 2𝒞`;
* log-mean-exp between the maximum minus `log N` and the maximum; the quadratic potential between `χ − λ/4` and `χ`
  (vertex `e_{i*}` and `‖q‖² ≥ 0`);
* the B lemma is the C lemma at `w = (1/n, …, 1/n)` (`I = {1..n}`), plus the entropic gap conversion.
-/

set_option linter.style.longLine false

noncomputable section
open Finset Set
open scoped InnerProductSpace

namespace StatFormal.Wave15b

open StatFormal.RobustEquality.Paper2.Alternating (Plans)

section Lemmas

variable {K m n : ℕ}

lemma du_coe_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    ((∑ i ∈ s, g i : ℝ) : EReal) = ∑ i ∈ s, (g i : EReal) :=
  map_sum Real.toERealAddHom g s

lemma du_posRows_nonempty {w : Fin n → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    (posRows w).Nonempty := by
  by_contra h
  have hle : ∀ i, w i ≤ 0 := fun i => by
    by_contra hc
    exact h ⟨i, by simp only [posRows, Finset.mem_filter, Finset.mem_univ, true_and]; linarith⟩
  have : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => hle i
  linarith

lemma du_mem_posRows {w : Fin n → ℝ} {i : Fin n} : i ∈ posRows w ↔ 0 < w i := by
  simp [posRows]

lemma du_ell_le (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) {I : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ I) (u : EuclideanSpace ℝ (Fin K)) : ellAff Z f i u ≤ chiI I Z f u :=
  le_ciSup (f := fun i : I => ellAff Z f i u) (Set.finite_range _).bddAbove ⟨i, hi⟩

lemma du_chi_attained {I : Finset (Fin n)} (hI : I.Nonempty) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (f : Fin n → ℝ) (u : EuclideanSpace ℝ (Fin K)) : ∃ i ∈ I, chiI I Z f u = ellAff Z f i u := by
  have : Nonempty I := ⟨⟨hI.choose, hI.choose_spec⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i : I => ellAff Z f i u)
  exact ⟨i, i.2, by rw [chiI, ← hi]⟩

lemma du_conj_bdd {U : Set (EuclideanSpace ℝ (Fin K))} (hU : Bornology.IsBounded U) {I : Finset (Fin n)}
    (hI : I.Nonempty) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin K)) :
    BddAbove ((fun u => ⟪u, z⟫_ℝ - chiI I Z f u) '' U) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hU
  obtain ⟨i0, hi0⟩ := hI
  refine ⟨R * ‖z - Z i0‖ + (‖Z i0‖ ^ 2 - f i0) / 2, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have h1 := du_ell_le Z f hi0 u
  have h2 : ⟪u, z⟫_ℝ - ellAff Z f i0 u = ⟪u, z - Z i0⟫_ℝ + (‖Z i0‖ ^ 2 - f i0) / 2 := by
    unfold ellAff; rw [inner_sub_right]; ring
  have h3 : ⟪u, z - Z i0⟫_ℝ ≤ R * ‖z - Z i0‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hR u hu) (norm_nonneg _))
  simp only
  linarith

lemma du_le_conjU {U : Set (EuclideanSpace ℝ (Fin K))} (hU : Bornology.IsBounded U) {I : Finset (Fin n)}
    (hI : I.Nonempty) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) {u : EuclideanSpace ℝ (Fin K)}
    (hu : u ∈ U) (z : EuclideanSpace ℝ (Fin K)) : ⟪u, z⟫_ℝ - chiI I Z f u ≤ conjU U (chiI I Z f) z :=
  le_csSup (du_conj_bdd hU hI Z f z) ⟨u, hu, rfl⟩

lemma du_conjU_data {U : Set (EuclideanSpace ℝ (Fin K))} (hne : U.Nonempty) {I : Finset (Fin n)}
    (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) {i : Fin n} (hi : i ∈ I) :
    conjU U (chiI I Z f) (Z i) ≤ (‖Z i‖ ^ 2 - f i) / 2 := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨u, -, rfl⟩
  have := du_ell_le Z f hi u
  unfold ellAff at this
  simp only
  linarith

lemma du_fy (X : EuclideanSpace ℝ (Fin K) → ℝ) (u z : EuclideanSpace ℝ (Fin K)) :
    ((⟪u, z⟫_ℝ - X z : ℝ) : EReal) ≤ conjE X u :=
  le_iSup (fun z => ((⟪u, z⟫_ℝ - X z : ℝ) : EReal)) z

lemma du_conjE_le {U : Set (EuclideanSpace ℝ (Fin K))} (hU : Bornology.IsBounded U) {I : Finset (Fin n)}
    (hI : I.Nonempty) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) {u : EuclideanSpace ℝ (Fin K)}
    (hu : u ∈ U) : conjE (conjU U (chiI I Z f)) u ≤ ((chiI I Z f u : ℝ) : EReal) := by
  refine iSup_le fun z => EReal.coe_le_coe_iff.2 ?_
  have := du_le_conjU hU hI Z f hu z
  linarith

lemma du_prod_plan {β : Fin m → ℝ} {w : Fin n → ℝ} (hβ0 : ∀ j, 0 ≤ β j) (hβ1 : ∑ j, β j = 1)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) : (fun j i => β j * w i) ∈ Plans β w := by
  refine ⟨fun j i => mul_nonneg (hβ0 j) (hw0 i), fun j => ?_, fun i => ?_⟩
  · rw [← Finset.mul_sum, hw1, mul_one]
  · rw [← Finset.sum_mul, hβ1, one_mul]

lemma du_cost_eq {β : Fin m → ℝ} {w : Fin n → ℝ} {π : Fin m → Fin n → ℝ} (hπ : π ∈ Plans β w)
    (ug : Fin m → EuclideanSpace ℝ (Fin K)) (Z : Fin n → EuclideanSpace ℝ (Fin K)) :
    costSum ug Z π = ∑ j, β j * ‖ug j‖ ^ 2 + ∑ i, w i * ‖Z i‖ ^ 2 - 2 * corrSum ug Z π := by
  unfold costSum corrSum
  have : ∀ j i, π j i * ‖ug j - Z i‖ ^ 2 =
      π j i * ‖ug j‖ ^ 2 + π j i * ‖Z i‖ ^ 2 - 2 * (π j i * ⟪ug j, Z i⟫_ℝ) := by
    intro j i; rw [norm_sub_sq_real]; ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ j, ∑ i, π j i * ‖ug j‖ ^ 2 = ∑ j, β j * ‖ug j‖ ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul, hπ.2.1 j]
  have h2 : ∑ j, ∑ i, π j i * ‖Z i‖ ^ 2 = ∑ i, w i * ‖Z i‖ ^ 2 := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul, hπ.2.2 i]
  rw [h1, h2]

lemma du_cost_nonneg {β : Fin m → ℝ} {w : Fin n → ℝ} {π : Fin m → Fin n → ℝ} (hπ : π ∈ Plans β w)
    (ug : Fin m → EuclideanSpace ℝ (Fin K)) (Z : Fin n → EuclideanSpace ℝ (Fin K)) : 0 ≤ costSum ug Z π :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => mul_nonneg (hπ.1 j i) (sq_nonneg _)

/-- `f_i − ‖u − Z_i‖² = 2ℓ_i(u) − ‖u‖²`. -/
lemma du_expand (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) (i : Fin n)
    (u : EuclideanSpace ℝ (Fin K)) : f i - ‖u - Z i‖ ^ 2 = 2 * ellAff Z f i u - ‖u‖ ^ 2 := by
  unfold ellAff; rw [norm_sub_sq_real]; ring

/-- The log-mean-exp sandwich `0 ≤ φ̂ − φ⁰ ≤ ε log N`. -/
lemma du_soft_hard {ε : ℝ} (hε : 0 < ε) {I : Finset (Fin n)} (hI : I.Nonempty)
    (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) (u : EuclideanSpace ℝ (Fin K)) :
    0 ≤ phiSoft ε I Z f u - phiHard I Z f u ∧
      phiSoft ε I Z f u - phiHard I Z f u ≤ ε * Real.log I.card := by
  obtain ⟨i0, hi0, hχ⟩ := du_chi_attained hI Z f u
  set χ := chiI I Z f u
  set Mx := (2 * χ - ‖u‖ ^ 2) / ε
  set S := ∑ i ∈ I, Real.exp ((f i - ‖u - Z i‖ ^ 2) / ε)
  have hN : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
  have hL : ∀ i ∈ I, (f i - ‖u - Z i‖ ^ 2) / ε ≤ Mx := by
    intro i hi
    rw [du_expand]
    exact div_le_div_of_nonneg_right (by linarith [du_ell_le Z f hi u]) hε.le
  have hL0 : (f i0 - ‖u - Z i0‖ ^ 2) / ε = Mx := by rw [du_expand, ← hχ]
  have hS1 : Real.exp Mx ≤ S := by
    rw [← hL0]
    exact Finset.single_le_sum (f := fun i => Real.exp ((f i - ‖u - Z i‖ ^ 2) / ε))
      (fun i _ => (Real.exp_pos _).le) hi0
  have hS2 : S ≤ I.card * Real.exp Mx := by
    have := Finset.sum_le_card_nsmul I (fun i => Real.exp ((f i - ‖u - Z i‖ ^ 2) / ε)) (Real.exp Mx)
      fun i hi => Real.exp_le_exp.2 (hL i hi)
    simpa [nsmul_eq_mul] using this
  have hSpos : 0 < S := lt_of_lt_of_le (Real.exp_pos _) hS1
  have hlogS1 : Mx ≤ Real.log S := by
    rw [← Real.log_exp Mx]; exact Real.log_le_log (Real.exp_pos _) hS1
  have hlogS2 : Real.log S ≤ Real.log I.card + Mx := by
    have := Real.log_le_log hSpos hS2
    rwa [Real.log_mul hN.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  have hsoft : phiSoft ε I Z f u = -ε * (Real.log S - Real.log I.card) := by
    unfold phiSoft
    rw [Real.log_mul (by positivity) hSpos.ne', one_div, Real.log_inv]
    ring
  have hhard : phiHard I Z f u = -ε * Mx := by
    unfold phiHard; simp only [Mx]; field_simp; ring
  rw [hsoft, hhard]
  constructor <;> nlinarith

/-- The quadratic potential: `χ − λ/4 ≤ g ≤ χ`. -/
lemma du_quad_bounds {lam : ℝ} (hlam : 0 ≤ lam) {I : Finset (Fin n)} (hI : I.Nonempty)
    (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) (u : EuclideanSpace ℝ (Fin K)) :
    0 ≤ chiI I Z f u - gQuad lam I Z f u ∧ chiI I Z f u - gQuad lam I Z f u ≤ lam / 4 := by
  classical
  obtain ⟨i0, hi0, hχ⟩ := du_chi_attained hI Z f u
  set χ := chiI I Z f u
  set F := fun q : Fin n → ℝ => ∑ i, q i * scoreC Z f i u - lam / 2 * ∑ i, q i ^ 2
  have hs : ∀ i, scoreC Z f i u = 2 * ellAff Z f i u := by
    intro i; unfold scoreC ellAff; rw [real_inner_comm]; ring
  have hup : ∀ q ∈ simplexOn I, F q ≤ 2 * χ := by
    intro q hq
    obtain ⟨hq0, hqI, hq1⟩ := hq
    have h1 : ∑ i, q i * scoreC Z f i u ≤ ∑ i, q i * (2 * χ) := by
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : i ∈ I
      · rw [hs]; exact mul_le_mul_of_nonneg_left (by linarith [du_ell_le Z f hi u]) (hq0 i)
      · rw [hqI i hi]; simp
    rw [← Finset.sum_mul, hq1, one_mul] at h1
    have h2 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    simp only [F]
    nlinarith
  let e : Fin n → ℝ := fun i => if i = i0 then 1 else 0
  have he : e ∈ simplexOn I := by
    refine ⟨fun i => by simp only [e]; split_ifs <;> norm_num, fun i hi => ?_, by simp [e]⟩
    simp only [e]; rw [if_neg]; rintro rfl; exact hi hi0
  have hFe : F e = 2 * χ - lam / 2 := by
    simp only [F, e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have : ∑ i, (if i = i0 then (1 : ℝ) else 0) ^ 2 = 1 := by
      simp [ite_pow]
    rw [this, hs, ← hχ]; ring
  have hbdd : BddAbove (F '' simplexOn I) := ⟨2 * χ, by rintro _ ⟨q, hq, rfl⟩; exact hup q hq⟩
  have hsup1 : sSup (F '' simplexOn I) ≤ 2 * χ :=
    csSup_le ⟨_, ⟨e, he, rfl⟩⟩ (by rintro _ ⟨q, hq, rfl⟩; exact hup q hq)
  have hsup2 : 2 * χ - lam / 2 ≤ sSup (F '' simplexOn I) := by
    rw [← hFe]; exact le_csSup hbdd ⟨e, he, rfl⟩
  have hg : gQuad lam I Z f u = (1 / 2) * sSup (F '' simplexOn I) := rfl
  rw [hg]
  constructor <;> linarith

end Lemmas

/-! ### C `lem:weighted-duality` -/

theorem weighted_duality : Claims.weighted_duality := by
  intro K m n β ug w Z f U ζ hβ0 hβ1 hw0 hw1 hU hug hgap
  have hI := du_posRows_nonempty hw0 hw1
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hβ1
    · exact h
  have hUne : U.Nonempty := ⟨ug ⟨0, hm⟩, hug _⟩
  set I := posRows w
  set χ := chiI I Z f
  set X := conjU U χ
  have hfin : ∀ j, conjE X (ug j) = ((conjE X (ug j)).toReal : EReal) := by
    intro j
    refine (EReal.coe_toReal ?_ ?_).symm
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (du_conjE_le hU hI Z f (hug j))
    · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (du_fy X (ug j) 0)
  set x : Fin m → ℝ := fun j => (conjE X (ug j)).toReal
  have hfin' : ∀ j, conjE X (ug j) = (x j : EReal) := fun j => hfin j
  have hmid : midTerm β ug w Z X = ((∑ j, β j * x j + ∑ i, w i * X (Z i) : ℝ) : EReal) := by
    unfold midTerm
    rw [EReal.coe_add]
    congr 1
    rw [du_coe_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [EReal.coe_mul, hfin' j]
  have hxle : ∀ j, x j ≤ χ (ug j) := fun j =>
    EReal.coe_le_coe_iff.1 ((hfin' j).symm.trans_le (du_conjE_le hU hI Z f (hug j)))
  have hfy : ∀ j i, ⟪ug j, Z i⟫_ℝ ≤ x j + X (Z i) := fun j i => by
    have := EReal.coe_le_coe_iff.1 ((du_fy X (ug j) (Z i)).trans_eq (hfin' j))
    linarith
  have hcorr : ∀ π ∈ Plans β w, corrSum ug Z π ≤ ∑ j, β j * x j + ∑ i, w i * X (Z i) := by
    intro π hπ
    unfold corrSum
    calc ∑ j, ∑ i, π j i * ⟪ug j, Z i⟫_ℝ ≤ ∑ j, ∑ i, π j i * (x j + X (Z i)) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hfy j i) (hπ.1 j i)
      _ = ∑ j, β j * x j + ∑ i, w i * X (Z i) := by
          simp only [mul_add, Finset.sum_add_distrib]
          congr 1
          · exact Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul, hπ.2.1 j]
          · rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul, hπ.2.2 i]
  have hne : (Plans β w).Nonempty := ⟨_, du_prod_plan hβ0 hβ1 hw0 hw1⟩
  have hbdd : BddAbove (corrSum ug Z '' Plans β w) :=
    ⟨_, by rintro _ ⟨π, hπ, rfl⟩; exact hcorr π hπ⟩
  refine ⟨?_, ?_⟩
  · rw [hmid]
    exact EReal.coe_le_coe_iff.2 (csSup_le (hne.image _) (by rintro _ ⟨π, hπ, rfl⟩; exact hcorr π hπ))
  · rw [hmid]
    apply EReal.coe_le_coe_iff.2
    set M := ∑ j, β j * ‖ug j‖ ^ 2 + ∑ i, w i * ‖Z i‖ ^ 2
    have hW : M - 2 * maxCorr β ug w Z ≤ w2sq β ug w Z := by
      refine le_csInf (hne.image _) ?_
      rintro _ ⟨π, hπ, rfl⟩
      have := le_csSup hbdd ⟨π, hπ, rfl⟩
      rw [du_cost_eq hπ]
      unfold maxCorr at *
      linarith
    have hx : ∑ j, β j * x j ≤ ∑ j, β j * χ (ug j) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hxle j) (hβ0 j)
    have hX : ∑ i, w i * X (Z i) ≤ ∑ i, w i * ((‖Z i‖ ^ 2 - f i) / 2) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rcases (hw0 i).lt_or_eq with h | h
      · exact mul_le_mul_of_nonneg_left (du_conjU_data hUne Z f (du_mem_posRows.2 h)) (hw0 i)
      · rw [← h]; simp
    have e1 : ∑ j, β j * χ (ug j) =
        (∑ j, β j * ‖ug j‖ ^ 2 - ∑ j, β j * phiHard I Z f (ug j)) / 2 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by unfold phiHard; ring
    have e2 : ∑ i, w i * ((‖Z i‖ ^ 2 - f i) / 2) = (∑ i, w i * ‖Z i‖ ^ 2 - ∑ i, w i * f i) / 2 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1] at hx
    rw [e2] at hX
    linarith

/-- The literal reading without "grid ⊂ `𝒰_K`" fails. -/
theorem weighted_duality_grid_needed : Claims.weighted_duality_grid_needed := by
  have hpos : posRows (fun _ : Fin 1 => (1 : ℝ)) = Finset.univ := by
    ext i; simp [posRows]
  have hchi : ∀ u : EuclideanSpace ℝ (Fin 1), chiI (posRows (fun _ : Fin 1 => (1 : ℝ))) ![!₂[(0 : ℝ)]]
      (fun _ => 0) u = 0 := by
    intro u
    unfold chiI ellAff
    have : ∀ i : Fin 1, ![!₂[(0 : ℝ)]] i = 0 := by
      intro i; fin_cases i; ext k; fin_cases k; simp
    simp only [this, inner_zero_right, norm_zero]
    norm_num
  set X := conjU (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (chiI (posRows (fun _ : Fin 1 => (1 : ℝ))) ![!₂[(0 : ℝ)]] (fun _ => 0))
  have hXle : ∀ z, X z ≤ ‖z‖ := by
    intro z
    refine csSup_le ⟨_, ⟨0, Metric.mem_closedBall_self zero_le_one, rfl⟩⟩ ?_
    rintro _ ⟨u, hu, rfl⟩
    simp only [hchi, sub_zero]
    have hu' : ‖u‖ ≤ 1 := by simpa using hu
    calc ⟪u, z⟫_ℝ ≤ ‖u‖ * ‖z‖ := real_inner_le_norm _ _
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hu' (norm_nonneg _)
      _ = ‖z‖ := one_mul _
  have htop : conjE X (![!₂[(2 : ℝ)]] 0) = ⊤ := by
    rw [EReal.eq_top_iff_forall_lt]
    intro y
    set t := max y 0 + 1
    have ht : 0 ≤ t := by positivity
    refine lt_of_lt_of_le ?_ (du_fy X _ (!₂[t]))
    apply EReal.coe_lt_coe_iff.2
    have hin : ⟪![!₂[(2 : ℝ)]] 0, !₂[t]⟫_ℝ = 2 * t := by
      simp [PiLp.inner_apply]; ring
    have hn : ‖(!₂[t] : EuclideanSpace ℝ (Fin 1))‖ = t := by
      rw [EuclideanSpace.norm_eq]; simp [Real.sqrt_sq ht]
    have := hXle (!₂[t])
    rw [hn] at this
    rw [hin]
    have : y < t := by simp only [t]; linarith [le_max_left y 0]
    linarith
  have hmid : midTerm (fun _ : Fin 1 => (1 : ℝ)) ![!₂[(2 : ℝ)]] (fun _ : Fin 1 => (1 : ℝ)) ![!₂[(0 : ℝ)]] X = ⊤ := by
    unfold midTerm
    rw [Fin.sum_univ_one, htop, EReal.coe_one, one_mul, EReal.top_add_coe]
  refine ⟨?_, hmid, ?_⟩
  · -- `W₂²(δ₂, δ₀) ≤ 4 = φ⁰(2)`
    have hplan : (fun _ _ => (1 : ℝ)) ∈ Plans (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) :=
      ⟨fun _ _ => zero_le_one, fun _ => by simp, fun _ => by simp⟩
    have hw : w2sq (fun _ : Fin 1 => (1 : ℝ)) ![!₂[(2 : ℝ)]] (fun _ : Fin 1 => (1 : ℝ)) ![!₂[(0 : ℝ)]] ≤
        costSum ![!₂[(2 : ℝ)]] ![!₂[(0 : ℝ)]] (fun _ _ => (1 : ℝ)) :=
      csInf_le ⟨0, by rintro _ ⟨π, hπ, rfl⟩; exact du_cost_nonneg hπ _ _⟩ ⟨_, hplan, rfl⟩
    have hc : costSum ![!₂[(2 : ℝ)]] ![!₂[(0 : ℝ)]] (fun _ _ => (1 : ℝ)) = 4 := by
      unfold costSum
      simp only [Fin.sum_univ_one, one_mul, Matrix.cons_val_zero]
      rw [EuclideanSpace.norm_eq]
      simp
      norm_num
    have hh : phiHard (posRows (fun _ : Fin 1 => (1 : ℝ))) ![!₂[(0 : ℝ)]] (fun _ => 0) (![!₂[(2 : ℝ)]] 0) = 4 := by
      unfold phiHard
      rw [hchi, EuclideanSpace.norm_eq]
      simp
      norm_num
    simp only [Fin.sum_univ_one, one_mul, sub_zero, add_zero, hh]
    linarith
  · rw [hmid]
    exact not_le.2 (EReal.coe_lt_top _)

/-! ### Entropic and quadratic fits, gauges -/

theorem weighted_entropic : Claims.weighted_entropic := by
  intro K m n ε w Z f hε hw0 hw1
  have hI := du_posRows_nonempty hw0 hw1
  have hsh := du_soft_hard hε hI Z f
  refine ⟨by simpa using Finset.card_le_univ (posRows w), hsh, fun u => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hsh u
    unfold phiHard at h1 h2
    rw [abs_le]
    constructor <;> linarith
  · intro β ug r hβ0 hβ1 hsoft
    have : ∑ j, β j * phiSoft ε (posRows w) Z f (ug j) ≤
        ∑ j, β j * phiHard (posRows w) Z f (ug j) + ε * Real.log (posRows w).card := by
      have hle : ∀ j, β j * phiSoft ε (posRows w) Z f (ug j) ≤
          β j * phiHard (posRows w) Z f (ug j) + β j * (ε * Real.log (posRows w).card) :=
        fun j => by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith [(hsh (ug j)).2]) (hβ0 j)
      calc _ ≤ ∑ j, (β j * phiHard (posRows w) Z f (ug j) + β j * (ε * Real.log (posRows w).card)) :=
            Finset.sum_le_sum fun j _ => hle j
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hβ1, one_mul]
    linarith

theorem weighted_quadratic : Claims.weighted_quadratic := by
  intro K m n lam w Z f hlam hw0 hw1
  have hI := du_posRows_nonempty hw0 hw1
  have hq := du_quad_bounds hlam hI Z f
  have hQ : ∀ u, 0 ≤ phiQuad lam (posRows w) Z f u - phiHard (posRows w) Z f u ∧
      phiQuad lam (posRows w) Z f u - phiHard (posRows w) Z f u ≤ lam / 2 := by
    intro u
    obtain ⟨h1, h2⟩ := hq u
    unfold phiQuad phiHard
    constructor <;> linarith
  refine ⟨hq, hQ, fun β ug r hβ0 hβ1 hsoft => ?_⟩
  have : ∑ j, β j * phiQuad lam (posRows w) Z f (ug j) ≤
      ∑ j, β j * phiHard (posRows w) Z f (ug j) + lam / 2 := by
    have hle : ∀ j, β j * phiQuad lam (posRows w) Z f (ug j) ≤
        β j * phiHard (posRows w) Z f (ug j) + β j * (lam / 2) :=
      fun j => by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith [(hQ (ug j)).2]) (hβ0 j)
    calc _ ≤ ∑ j, (β j * phiHard (posRows w) Z f (ug j) + β j * (lam / 2)) :=
          Finset.sum_le_sum fun j _ => hle j
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hβ1, one_mul]
  linarith

section KL

variable {n m : ℕ}

/-- `p log(p/q) ≥ p − q` for `p, q ≥ 0` with `p > 0 ⇒ q > 0`. -/
lemma du_gibbs_term {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p → 0 < q) :
    p - q ≤ p * Real.log (p / q) := by
  rcases hp.lt_or_eq with hp' | hp'
  · have hq' := hpq hp'
    have h := Real.log_le_sub_one_of_pos (div_pos hq' hp')
    have e : Real.log (p / q) = -Real.log (q / p) := by
      rw [← Real.log_inv, inv_div]
    rw [e]
    have : p * (q / p - 1) = q - p := by field_simp
    nlinarith
  · rw [← hp']; simp [hq]

end KL

theorem weighted_entropy_gauge : Claims.weighted_entropy_gauge := by
  intro n m π w b hπ0 hrow hw0 hw1 hb
  have hI := du_posRows_nonempty hw0 hw1
  have hN : (0 : ℝ) < (posRows w).card := by exact_mod_cast hI.card_pos
  have hzero : ∀ i j, w i = 0 → π i j = 0 := by
    intro i j hwi
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hπ0 i j).1 ((hrow i).trans hwi) j (mem_univ _)
    exact this
  have hu : ∀ i, 0 < w i → unifOn (posRows w) i = 1 / (posRows w).card := by
    intro i hi; simp [unifOn, du_mem_posRows.2 hi]
  refine ⟨?_, fun hcol hb1 => ?_⟩
  · unfold klMat klVec
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases (hw0 i).lt_or_eq with hwi | hwi
    · have hui := hu i hwi
      have hupos : 0 < unifOn (posRows w) i := by rw [hui]; positivity
      have hterm : ∀ j, π i j * Real.log (π i j / (unifOn (posRows w) i * b j)) =
          π i j * Real.log (π i j / (w i * b j)) + π i j * Real.log (w i / unifOn (posRows w) i) := by
        intro j
        rcases (hπ0 i j).lt_or_eq with hp | hp
        · rw [← mul_add, ← Real.log_mul (by have := hb j; positivity) (by positivity)]
          congr 2
          field_simp
        · rw [← hp]; simp
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, ← Finset.sum_mul, hrow i]
    · have : ∀ j, π i j = 0 := fun j => hzero i j hwi.symm
      simp [this, ← hwi]
  · have hk1 : 0 ≤ klMat π (fun i j => w i * b j) := by
      unfold klMat
      have hs : ∑ i, ∑ j, (π i j - w i * b j) ≤ ∑ i, ∑ j, π i j * Real.log (π i j / (w i * b j)) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        refine du_gibbs_term (hπ0 i j) (mul_nonneg (hw0 i) (hb j).le) fun hp => ?_
        rcases (hw0 i).lt_or_eq with hwi | hwi
        · exact mul_pos hwi (hb j)
        · exact absurd (hzero i j hwi.symm) hp.ne'
      have h0 : ∑ i, ∑ j, (π i j - w i * b j) = 0 := by
        simp only [Finset.sum_sub_distrib, hrow, ← Finset.mul_sum, hb1, mul_one, hw1, sub_self,
          Finset.sum_const_zero]
      linarith
    have hk2 : 0 ≤ klVec w (unifOn (posRows w)) := by
      unfold klVec
      have hs : ∑ i, (w i - unifOn (posRows w) i) ≤ ∑ i, w i * Real.log (w i / unifOn (posRows w) i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine du_gibbs_term (hw0 i) (by unfold unifOn; split_ifs <;> positivity) fun hp => ?_
        rw [hu i hp]; positivity
      have hsum : ∑ i, unifOn (posRows w) i = 1 := by
        unfold unifOn
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        field_simp
      have h0 : ∑ i, (w i - unifOn (posRows w) i) = 0 := by
        rw [Finset.sum_sub_distrib, hw1, hsum, sub_self]
      linarith
    refine ⟨hk1, hk2, ?_⟩
    have hid : klMat π (fun i j => unifOn (posRows w) i * b j) =
        klMat π (fun i j => w i * b j) + klVec w (unifOn (posRows w)) := by
      -- the identity proved in the first part
      unfold klMat klVec
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases (hw0 i).lt_or_eq with hwi | hwi
      · have hui := hu i hwi
        have hupos : 0 < unifOn (posRows w) i := by rw [hui]; positivity
        have hterm : ∀ j, π i j * Real.log (π i j / (unifOn (posRows w) i * b j)) =
            π i j * Real.log (π i j / (w i * b j)) + π i j * Real.log (w i / unifOn (posRows w) i) := by
          intro j
          rcases (hπ0 i j).lt_or_eq with hp | hp
          · rw [← mul_add, ← Real.log_mul (by have := hb j; positivity) (by positivity)]
            congr 2
            field_simp
          · rw [← hp]; simp
        rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, ← Finset.sum_mul, hrow i]
      · have : ∀ j, π i j = 0 := fun j => hzero i j hwi.symm
        simp [this, ← hwi]
    rw [hid]; linarith

theorem weighted_counting_gauge : Claims.weighted_counting_gauge := by
  intro K m n ε I Z f u hm hI
  have hN : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  have hS : 0 < ∑ i ∈ I, Real.exp ((f i - ‖u - Z i‖ ^ 2) / ε) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) hI
  unfold phiSoft
  rw [Real.log_mul (by positivity) hS.ne', Real.log_mul hN.ne' hM.ne', one_div, one_div, Real.log_inv,
    Real.log_inv]
  ring

/-! ### B `lem:app-dual-sandwich` -/

theorem dual_sandwich : Claims.dual_sandwich := by
  intro K m n β ug Z f U ε r hn hβ0 hβ1 hU hug hε hsoft
  have hw0 : ∀ i, 0 ≤ unifW n i := fun i => by unfold unifW; positivity
  have hw1 : ∑ i, unifW n i = 1 := by
    unfold unifW; rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hpos : posRows (unifW n) = Finset.univ := by
    ext i; simp only [posRows, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    unfold unifW; positivity
  have hcard : ((posRows (unifW n)).card : ℝ) = n := by rw [hpos]; simp
  have hf : (1 / (n : ℝ)) * ∑ i, f i = ∑ i, unifW n i * f i := by
    rw [Finset.mul_sum]; rfl
  -- entropic gap → hard gap `ζ = r + ε log n`
  have hgap := (weighted_entropic K m n ε (unifW n) Z f hε hw0 hw1).2.2.2 β ug r hβ0 hβ1
    (by rw [hpos, ← hf]; exact hsoft)
  rw [hcard] at hgap
  have := weighted_duality K m n β ug (unifW n) Z f U (r + ε * Real.log n) hβ0 hβ1 hw0 hw1 hU hug hgap
  rw [hpos] at this
  refine ⟨this.1, this.2.trans_eq ?_⟩
  congr 1; ring

end StatFormal.Wave15b
