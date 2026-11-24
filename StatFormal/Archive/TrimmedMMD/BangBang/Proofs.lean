import StatFormal.Archive.TrimmedMMD.BangBang.Statements
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Fin.Rev

/-!
# Proofs — trimmed MMD: extreme trimmed means and the bang-bang trimming
-/

noncomputable section
open Finset

namespace StatFormal.TrimmedMMD.BangBang

/-! ### Arithmetic facts about `c` and `k` -/

lemma cap_facts {n : ℕ} {α : ℝ} (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < cap n α ∧ (kfloor n α : ℝ) * cap n α ≤ 1 ∧ 1 < ((kfloor n α : ℝ) + 1) * cap n α ∧
      kfloor n α ≤ n ∧ (kfloor n α = n → (n : ℝ) * cap n α = 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : 0 < (n : ℝ) * (1 - α) := mul_pos hnR (by linarith)
  have hNn : (n : ℝ) * (1 - α) ≤ n := by nlinarith
  have hk : ((kfloor n α : ℕ) : ℝ) ≤ (n : ℝ) * (1 - α) := Nat.floor_le hN.le
  have hk1 : (n : ℝ) * (1 - α) < (kfloor n α : ℝ) + 1 := Nat.lt_floor_add_one _
  have hc : cap n α = 1 / ((n : ℝ) * (1 - α)) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hc]; positivity
  · rw [hc, mul_one_div, div_le_one hN]; exact hk
  · rw [hc, mul_one_div, one_lt_div hN]; exact hk1
  · exact Nat.floor_le_of_le hNn
  · intro he
    rw [he] at hk
    have : (n : ℝ) * (1 - α) = n := le_antisymm hNn hk
    rw [hc, this]; field_simp

/-! ### The greedy (bang-bang) point -/

lemma sum_range_ge (n k : ℕ) (F : ℕ → ℝ) :
    ∑ j ∈ range n, (if n - k ≤ j then F j else 0) = ∑ j ∈ Ico (n - k) n, F j := by
  rw [← Finset.sum_filter]
  congr 1
  ext j; simp only [mem_filter, mem_range, mem_Ico]; omega

lemma sum_range_eq (n k : ℕ) (F : ℕ → ℝ) :
    ∑ j ∈ range n, (if j + 1 = n - k then F j else 0) =
      if k < n then F (n - k - 1) else 0 := by
  by_cases hk : k < n
  · rw [ite_eq_left hk]
    have : ∀ j, (j + 1 = n - k) ↔ (n - k - 1 = j) := fun j => by omega
    simp_rw [this]
    rw [Finset.sum_ite_eq]
    simp only [mem_range, ite_eq_left_iff]
    intro h; omega
  · rw [ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (by omega)]

lemma greedy {n k : ℕ} {c : ℝ} (hn : 0 < n) (hc : 0 < c) (hkc : (k : ℝ) * c ≤ 1)
    (hk1 : 1 < ((k : ℝ) + 1) * c) (hkn : k ≤ n) (hkn' : k = n → (n : ℝ) * c = 1)
    (u : Fin n → ℝ) (τ : Equiv.Perm (Fin n)) (hmono : Monotone (u ∘ τ))
    (f : ℕ → ℝ) (hf : ∀ j (h : j < n), f j = u (τ ⟨j, h⟩)) :
    ∃ w : Fin n → ℝ, (∀ i, 0 ≤ w i ∧ w i ≤ c) ∧ ∑ i, w i = 1 ∧
      (∀ i, u (τ ⟨n - k - 1, by omega⟩) < u i → w i = c) ∧
      (∀ i, u i < u (τ ⟨n - k - 1, by omega⟩) → w i = 0) ∧
      ∑ i, w i * u i = c * ∑ j ∈ Ico (n - k) n, f j +
        (if k < n then (1 - k * c) * f (n - k - 1) else 0) := by
  set g : ℕ → ℝ := fun j => (if n - k ≤ j then c else 0) +
    (if j + 1 = n - k then 1 - k * c else 0) with hg
  refine ⟨fun i => g (τ.symm i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [hg]
    constructor
    · split_ifs <;> nlinarith
    · split_ifs <;> first | omega | nlinarith
  · rw [Equiv.sum_comp τ.symm (fun j => g j), Fin.sum_univ_eq_sum_range g n]
    simp only [hg, Finset.sum_add_distrib]
    rw [sum_range_ge n k (fun _ => c), sum_range_eq n k (fun _ => 1 - k * c)]
    simp only [sum_const, Nat.card_Ico, nsmul_eq_mul]
    by_cases hk : k < n
    · rw [ite_eq_left hk, show n - (n - k) = k by omega]; ring
    · rw [ite_eq_right hk, show n - (n - k) = n by omega, add_zero]
      rw [hkn' (by omega)]
  · intro i hi
    have hj : n - k - 1 < (τ.symm i : ℕ) := by
      by_contra hcon
      have hle : (τ.symm i) ≤ (⟨n - k - 1, by omega⟩ : Fin n) := by
        rw [Fin.le_def]; simp only; omega
      have := hmono hle
      simp only [Function.comp, Equiv.apply_symm_apply] at this
      linarith
    simp only [hg]
    rw [ite_eq_left (by omega), ite_eq_right (by omega), add_zero]
  · intro i hi
    have hj : (τ.symm i : ℕ) < n - k - 1 := by
      by_contra hcon
      have hle : (⟨n - k - 1, by omega⟩ : Fin n) ≤ (τ.symm i) := by
        rw [Fin.le_def]; simp only; omega
      have := hmono hle
      simp only [Function.comp, Equiv.apply_symm_apply] at this
      linarith
    simp only [hg]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
  · rw [← Equiv.sum_comp τ (fun i => g (τ.symm i) * u i)]
    simp only [Equiv.symm_apply_apply]
    have : ∀ j : Fin n, g j * u (τ j) = g j * f j := fun j => by
      rw [hf j j.2]
    rw [Finset.sum_congr rfl (fun j _ => this j), Fin.sum_univ_eq_sum_range (fun j => g j * f j) n]
    simp only [hg, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    rw [sum_range_ge n k (fun j => c * f j), sum_range_eq n k (fun j => (1 - k * c) * f j),
      Finset.mul_sum]

/-! ### Exchange argument -/

lemma exch_term {n : ℕ} {c θ : ℝ} {u w w' : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i ∧ w i ≤ c)
    (h1 : ∀ i, θ < u i → w' i = c) (h2 : ∀ i, u i < θ → w' i = 0) (i : Fin n) :
    (w i - w' i) * (u i - θ) ≤ 0 := by
  rcases lt_trichotomy (u i) θ with h | h | h
  · rw [h2 i h, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (hw i).1 (by linarith)
  · rw [h, sub_self, mul_zero]
  · rw [h1 i h]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [(hw i).2]) (by linarith)

lemma exch_sum {n : ℕ} (θ : ℝ) (u w w' : Fin n → ℝ) (hs : ∑ i, w i = 1)
    (hs' : ∑ i, w' i = 1) :
    ∑ i, w i * u i - ∑ i, w' i * u i = ∑ i, (w i - w' i) * (u i - θ) := by
  have : ∀ i, (w i - w' i) * (u i - θ) = w i * u i - w' i * u i - θ * w i + θ * w' i :=
    fun i => by ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, hs']
  ring

lemma tied_sum {n : ℕ} {c θ : ℝ} {u w : Fin n → ℝ} (hs : ∑ i, w i = 1)
    (h1 : ∀ i, θ < u i → w i = c) (h2 : ∀ i, u i < θ → w i = 0) :
    ∑ i ∈ univ.filter (fun i => u i = θ), w i =
      1 - c * (univ.filter (fun i => θ < u i)).card := by
  have hsplit : ∀ i, w i = (if u i = θ then w i else 0) + (if θ < u i then c else 0) := by
    intro i
    rcases lt_trichotomy (u i) θ with h | h | h
    · rw [ite_eq_right h.ne, ite_eq_right (by linarith), h2 i h]; ring
    · rw [ite_eq_left h, ite_eq_right (by linarith)]; ring
    · rw [ite_eq_right h.ne', ite_eq_left h, h1 i h]; ring
  have := hs
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, Finset.sum_ite,
    Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const_zero, add_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul] at this
  linarith

/-- Linear optimisation over the capped simplex: structure of every maximiser. -/
lemma lp_argmax {n k : ℕ} {c : ℝ} (hn : 0 < n) (hc : 0 < c) (hkc : (k : ℝ) * c ≤ 1)
    (hk1 : 1 < ((k : ℝ) + 1) * c) (hkn : k ≤ n) (hkn' : k = n → (n : ℝ) * c = 1)
    (u : Fin n → ℝ) (τ : Equiv.Perm (Fin n)) (hmono : Monotone (u ∘ τ))
    (θ : ℝ) (hθ : θ = u (τ ⟨n - k - 1, by omega⟩))
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ c) (hs : ∑ i, w i = 1)
    (hmax : ∀ w' : Fin n → ℝ, (∀ i, 0 ≤ w' i ∧ w' i ≤ c) → ∑ i, w' i = 1 →
      ∑ i, w' i * u i ≤ ∑ i, w i * u i) :
    (∀ i, θ < u i → w i = c) ∧ (∀ i, u i < θ → w i = 0) ∧
      ∑ i ∈ univ.filter (fun i => u i = θ), w i =
        1 - c * (univ.filter (fun i => θ < u i)).card := by
  obtain ⟨w', hw', hs', h1, h2, -⟩ :=
    greedy hn hc hkc hk1 hkn hkn' u τ hmono
      (fun j => if h : j < n then u (τ ⟨j, h⟩) else 0) (fun _ h => dite_eq_left h)
  rw [← hθ] at h1 h2
  have hle := hmax w' hw' hs'
  have hterm := exch_term (c := c) (θ := θ) (u := u) (w := w) (w' := w') hw h1 h2
  have hid := exch_sum θ u w w' hs hs'
  have hsum0 : ∑ i, (w i - w' i) * (u i - θ) = 0 := by
    have : ∑ i, (w i - w' i) * (u i - θ) ≤ 0 := Finset.sum_nonpos (fun i _ => hterm i)
    linarith
  rw [Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hterm i)] at hsum0
  have g1 : ∀ i, θ < u i → w i = c := by
    intro i hi
    have := hsum0 i (mem_univ _)
    rw [h1 i hi] at this
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have g2 : ∀ i, u i < θ → w i = 0 := by
    intro i hi
    have := hsum0 i (mem_univ _)
    rw [h2 i hi] at this
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  exact ⟨g1, g2, tied_sum hs g1 g2⟩

/-! ### Trimmed-mean claims -/

theorem trimmedmean_value : Claims.trimmedmean_value := by
  intro n v α hn hα0 hα1
  obtain ⟨hc, hkc, hk1, hkn, hkn'⟩ := cap_facts hn hα0 hα1
  obtain ⟨w', hw', hs', h1, h2, hval⟩ :=
    greedy hn hc hkc hk1 hkn hkn' v (Tuple.sort v) (Tuple.monotone_sort v) (ord v)
      (fun j h => by simp [ord, h])
  refine ⟨⟨w', ⟨hw', hs'⟩, hval⟩, ?_⟩
  rintro _ ⟨w, ⟨hw, hs⟩, rfl⟩
  show _ ≤ _
  rw [← hval]
  have hterm := exch_term hw h1 h2
  have hid := exch_sum (v (Tuple.sort v ⟨n - kfloor n α - 1, by omega⟩)) v w w' hs hs'
  have := Finset.sum_nonpos (fun i (_ : i ∈ univ) => hterm i)
  linarith

theorem trimmedmean_argmax : Claims.trimmedmean_argmax := by
  intro n v α w hn hα0 hα1 _ hmax hw θ
  obtain ⟨hc, hkc, hk1, hkn, hkn'⟩ := cap_facts hn hα0 hα1
  exact lp_argmax hn hc hkc hk1 hkn hkn' v (Tuple.sort v) (Tuple.monotone_sort v) θ
    (by show ord v _ = _; unfold ord; rw [dite_eq_left (by omega)])
    w hw.1 hw.2 (fun w' hw' hs' => (isMaxOn_iff.1 hmax) w' ⟨hw', hs'⟩)

/-! ### Bang-bang trimming -/

section BangBang

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n m : ℕ}

/-- The witness `Σ w_i x_i − Σ v_j y_j`. -/
def dvec (x : Fin n → E) (y : Fin m → E) (p : (Fin n → ℝ) × (Fin m → ℝ)) : E :=
  ∑ i, p.1 i • x i - ∑ j, p.2 j • y j

/-- The segment point `p + s (p' − p)`. -/
def seg (p p' : (Fin n → ℝ) × (Fin m → ℝ)) (s : ℝ) : (Fin n → ℝ) × (Fin m → ℝ) :=
  (fun i => p.1 i + s * (p'.1 i - p.1 i), fun j => p.2 j + s * (p'.2 j - p.2 j))

lemma capped_seg {N : ℕ} {α : ℝ} {w w' : Fin N → ℝ} (hw : w ∈ capped N α)
    (hw' : w' ∈ capped N α) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (fun i => w i + s * (w' i - w i)) ∈ capped N α := by
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.2 hs1) (hw.1 i).1, mul_nonneg hs0 (hw'.1 i).1]
  · nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 (hw.1 i).2),
      mul_nonneg hs0 (sub_nonneg.2 (hw'.1 i).2)]
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hw.2, hw'.2]
    ring

lemma capped_compact (N : ℕ) (α : ℝ) : IsCompact (capped N α) := by
  have : capped N α = Set.Icc (0 : Fin N → ℝ) (fun _ => cap N α) ∩ {w | ∑ i, w i = 1} := by
    ext w; simp [capped, Pi.le_def, forall_and]
  rw [this]
  exact isCompact_Icc.inter_right
    (isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)

lemma dvec_seg (x : Fin n → E) (y : Fin m → E) (p p' : (Fin n → ℝ) × (Fin m → ℝ)) (s : ℝ) :
    dvec x y (seg p p' s) = dvec x y p + s • (dvec x y p' - dvec x y p) := by
  simp only [dvec, seg, add_smul, mul_smul, sub_smul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.smul_sum, smul_sub]
  abel

lemma inner_dvec (x : Fin n → E) (y : Fin m → E) (D : E) (q : (Fin n → ℝ) × (Fin m → ℝ)) :
    inner ℝ D (dvec x y q) =
      ∑ i, q.1 i * inner ℝ D (x i) - ∑ j, q.2 j * inner ℝ D (y j) := by
  simp [dvec, inner_sub_right, inner_sum, real_inner_smul_right]

lemma nonneg_of_forall_small {t A : ℝ} (hA : 0 ≤ A)
    (h : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ 2 * s * t + s ^ 2 * A) : 0 ≤ t := by
  by_contra ht
  replace ht := not_le.1 ht
  set s := min 1 (-t / (A + 1)) with hs
  have hs0 : 0 < s := lt_min one_pos (div_pos (neg_pos.mpr ht) (by linarith))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hs2 : s * (A + 1) ≤ -t := by
    have := min_le_right 1 (-t / (A + 1))
    rw [← hs, le_div_iff₀ (by linarith)] at this
    exact this
  have h3 := mul_le_mul_of_nonneg_left hs2 hs0.le
  have h4 := h s hs0 hs1
  have h5 : s * t < 0 := mul_neg_of_pos_of_neg hs0 ht
  nlinarith

lemma first_order {α β : ℝ} (x : Fin n → E) (y : Fin m → E) {p p' : (Fin n → ℝ) × (Fin m → ℝ)}
    (hp : p ∈ capped n α ×ˢ capped m β) (hp' : p' ∈ capped n α ×ˢ capped m β)
    (hmin : IsMinOn (qp x y) (capped n α ×ˢ capped m β) p) :
    0 ≤ inner ℝ (dvec x y p) (dvec x y p' - dvec x y p) := by
  apply nonneg_of_forall_small (A := ‖dvec x y p' - dvec x y p‖ ^ 2) (by positivity)
  intro s hs0 hs1
  have hmem : seg p p' s ∈ capped n α ×ˢ capped m β :=
    ⟨capped_seg hp.1 hp'.1 hs0.le hs1, capped_seg hp.2 hp'.2 hs0.le hs1⟩
  have := (isMinOn_iff.1 hmin) _ hmem
  have e1 : qp x y (seg p p' s) = ‖dvec x y (seg p p' s)‖ ^ 2 := rfl
  have e0 : qp x y p = ‖dvec x y p‖ ^ 2 := rfl
  rw [e1, e0, dvec_seg, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs] at this
  linarith

end BangBang

theorem bangbang_i : Claims.bangbang_i := by
  intro E _ _ n m x y α β hn hm hα0 hα1 hβ0 hβ1
  obtain ⟨hc, hkc, hk1, hkn, hkn'⟩ := cap_facts hn hα0 hα1
  obtain ⟨hc', hkc', hk1', hkm, hkm'⟩ := cap_facts hm hβ0 hβ1
  constructor
  · apply IsCompact.exists_isMinOn ((capped_compact n α).prod (capped_compact m β))
    · obtain ⟨w0, hw0, hs0, -⟩ := greedy hn hc hkc hk1 hkn hkn' (fun _ => (0 : ℝ)) 1
        monotone_const (fun _ => 0) (fun _ _ => rfl)
      obtain ⟨v0, hv0, hs0', -⟩ := greedy hm hc' hkc' hk1' hkm hkm' (fun _ => (0 : ℝ)) 1
        monotone_const (fun _ => 0) (fun _ _ => rfl)
      exact ⟨(w0, v0), ⟨hw0, hs0⟩, ⟨hv0, hs0'⟩⟩
    · apply Continuous.continuousOn
      unfold qp
      fun_prop
  · intro p hp p' hp' hmin hmin'
    have h1 := first_order x y hp hp' hmin
    have h2 := first_order x y hp' hp hmin'
    change dvec x y p = dvec x y p'
    set D := dvec x y p
    set D' := dvec x y p'
    have h0 : inner ℝ (D' - D) (D' - D) = -(inner ℝ D (D' - D) + inner ℝ D' (D - D')) := by
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]; ring
    have h3 : inner ℝ (D' - D) (D' - D) = 0 :=
      le_antisymm (by linarith) real_inner_self_nonneg
    rw [inner_self_eq_zero, sub_eq_zero] at h3
    exact h3.symm

theorem bangbang_ii : Claims.bangbang_ii := by
  intro E _ _ n m x y α β p hn hm hα0 hα1 hβ0 hβ1 hkn hkm hp hmin _ d dx dy θx θy
  obtain ⟨hc, hkc, hk1, hkn0, hkn'⟩ := cap_facts hn hα0 hα1
  obtain ⟨hc', hkc', hk1', hkm0, hkm'⟩ := cap_facts hm hβ0 hβ1
  have hd : d = dvec x y p := rfl
  have hdx : ∀ i, dx i = inner ℝ d (x i) := fun i => rfl
  have hdy : ∀ j, dy j = inner ℝ d (y j) := fun j => rfl
  -- `w` minimises `Σ w'_i dx_i`
  have hwmax : ∀ w' : Fin n → ℝ, (∀ i, 0 ≤ w' i ∧ w' i ≤ cap n α) → ∑ i, w' i = 1 →
      ∑ i, w' i * (fun i => -dx i) i ≤ ∑ i, p.1 i * (fun i => -dx i) i := by
    intro w' hw' hs'
    have hp' : (w', p.2) ∈ capped n α ×ˢ capped m β := ⟨⟨hw', hs'⟩, hp.2⟩
    have := first_order x y hp hp' hmin
    rw [inner_sub_right, inner_dvec, inner_dvec, ← hd] at this
    simp only [mul_neg, Finset.sum_neg_distrib, hdx]
    linarith
  -- `v` maximises `Σ v'_j dy_j`
  have hvmax : ∀ v' : Fin m → ℝ, (∀ j, 0 ≤ v' j ∧ v' j ≤ cap m β) → ∑ j, v' j = 1 →
      ∑ j, v' j * dy j ≤ ∑ j, p.2 j * dy j := by
    intro v' hv' hs'
    have hp' : (p.1, v') ∈ capped n α ×ˢ capped m β := ⟨hp.1, ⟨hv', hs'⟩⟩
    have := first_order x y hp hp' hmin
    rw [inner_sub_right, inner_dvec, inner_dvec, ← hd] at this
    simp only [hdy]
    linarith
  have hmonoX : Monotone ((fun i => -dx i) ∘ (Fin.revPerm.trans (Tuple.sort dx))) := by
    intro a b hab
    have := Tuple.monotone_sort dx (Fin.rev_le_rev.2 hab)
    simp only [Function.comp, Equiv.trans_apply, Fin.revPerm_apply] at this ⊢
    linarith
  have RX := lp_argmax hn hc hkc hk1 hkn0 hkn' (fun i => -dx i)
    (Fin.revPerm.trans (Tuple.sort dx)) hmonoX (-θx)
    (by
      show -ord dx (kfloor n α) = _
      unfold ord
      rw [dite_eq_left hkn]
      simp only [Equiv.trans_apply, Fin.revPerm_apply, neg_inj]
      congr 2
      ext
      simp only [Fin.val_rev]
      omega)
    p.1 hp.1.1 hp.1.2 hwmax
  have RY := lp_argmax hm hc' hkc' hk1' hkm0 hkm' dy (Tuple.sort dy) (Tuple.monotone_sort dy) θy
    (by show ord dy _ = _; unfold ord; rw [dite_eq_left (by omega)])
    p.2 hp.2.1 hp.2.2 hvmax
  obtain ⟨X1, X2, X3⟩ := RX
  obtain ⟨Y1, Y2, Y3⟩ := RY
  have e1 : univ.filter (fun i => (fun i => -dx i) i = -θx) = univ.filter (fun i => dx i = θx) := by
    ext i; simp [neg_inj]
  have e2 : univ.filter (fun i => -θx < (fun i => -dx i) i) =
      univ.filter (fun i => dx i < θx) := by
    ext i; simp [neg_lt_neg_iff]
  rw [e1, e2] at X3
  refine ⟨fun i hi => X1 i (by linarith), fun i hi => X2 i (by linarith),
    X3, Y1, Y2, Y3⟩

end StatFormal.TrimmedMMD.BangBang
