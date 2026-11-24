import StatFormal.Archive.WaveP1d.Statements
import StatFormal.Archive.TrimmedMMD.BangBang.Proofs

/-!
# Route: trimmed MMD `prop:bangbang` (ii) residual mass, (iii) and its "face" sentence (untrusted)

* Residual mass: with `g = d ∘ σ` sorted (`Tuple.sort`), `#{i : d_i < g_k} ≤ k`, with equality when `g_{k−1} < g_k` (or
  `k = 0`) and strict inequality when `g_{k−1} = g_k`; combined with the certified tie identity of `bangbang_ii`.
* (iii): the objective is `≥ 0`, so at minimum value `0` the minimisers are the zero set `{Σ w x = Σ v y}`.
* Residual mass of `v`: the mirror count `#{j : d_j > g_{m−k−1}} ≤ k` (sorted `g`), combined with the `v` tie identity
  of `bangbang_ii`.
* Not a face: `X = Y = (a, b)`, `a ≠ b`, `α = β = ½` (caps `1`); `((½,½),(½,½))` has value `0` and is the midpoint of
  `((1,0),(0,1))` and `((0,1),(1,0))`, whose value `‖a − b‖² > 0` is not minimal.
-/

set_option linter.style.longLine false

noncomputable section
open Finset

namespace StatFormal.WaveP1d

namespace RouteBangBang

open StatFormal.TrimmedMMD.BangBang

/-- Counting below an order statistic. -/
lemma card_lt_ord {n : ℕ} (d : Fin n → ℝ) (k : ℕ) (hk : k < n) :
    (univ.filter (fun i => d i < ord d k)).card ≤ k ∧
    ((k = 0 ∨ ord d (k - 1) < ord d k) → (univ.filter (fun i => d i < ord d k)).card = k) ∧
    (0 < k → ord d (k - 1) = ord d k → (univ.filter (fun i => d i < ord d k)).card < k) := by
  set σ := Tuple.sort d
  set g : Fin n → ℝ := d ∘ σ with hg
  have hmono : Monotone g := Tuple.monotone_sort d
  have hord : ∀ j (hj : j < n), ord d j = g ⟨j, hj⟩ := fun j hj => by simp [ord, hj, hg, σ]
  have hmap : (univ.filter (fun i => d i < ord d k)) =
      (univ.filter (fun j => g j < ord d k)).map σ.toEmbedding := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply, hg, Function.comp]
    constructor
    · intro h; exact ⟨σ.symm i, by simpa using h, by simp⟩
    · rintro ⟨j, hj, rfl⟩; exact hj
  rw [hmap, card_map, hord k hk]
  have hsub : (univ.filter (fun j => g j < g ⟨k, hk⟩)) ⊆ univ.filter (fun j : Fin n => (j : ℕ) < k) := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    by_contra hcon
    push Not at hcon
    exact absurd (hmono (show (⟨k, hk⟩ : Fin n) ≤ j from hcon)) (not_le.2 hj)
  have hcardk : (univ.filter (fun j : Fin n => (j : ℕ) < k)).card = k := by
    rw [Fin.card_filter_val_lt]; omega
  refine ⟨(card_le_card hsub).trans hcardk.le, ?_, ?_⟩
  · intro h
    refine le_antisymm ((card_le_card hsub).trans hcardk.le) ?_
    calc k = _ := hcardk.symm
      _ ≤ _ := card_le_card fun j hj => ?_
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    rcases h with h0 | hlt
    · omega
    · have hk1 : k - 1 < n := by omega
      rw [hord (k - 1) hk1] at hlt
      exact lt_of_le_of_lt (hmono (show j ≤ (⟨k - 1, hk1⟩ : Fin n) from by
        show (j : ℕ) ≤ k - 1; omega)) hlt
  · intro hk0 heq
    have hk1 : k - 1 < n := by omega
    rw [hord (k - 1) hk1] at heq
    have hsub' : (univ.filter (fun j => g j < g ⟨k, hk⟩)) ⊆
        (univ.filter (fun j : Fin n => (j : ℕ) < k)).erase ⟨k - 1, hk1⟩ := by
      intro j hj
      refine mem_erase.2 ⟨?_, hsub hj⟩
      rintro rfl
      simp only [mem_filter, mem_univ, true_and] at hj
      exact absurd heq (ne_of_lt hj)
    have hmem : (⟨k - 1, hk1⟩ : Fin n) ∈ univ.filter (fun j : Fin n => (j : ℕ) < k) := by
      simp only [mem_filter, mem_univ, true_and]; show k - 1 < k; omega
    calc _ ≤ _ := card_le_card hsub'
      _ < k := by rw [card_erase_of_mem hmem, hcardk]; omega


/-- Counting above an order statistic (the mirror of `card_lt_ord`). -/
lemma card_gt_ord {m : ℕ} (d : Fin m → ℝ) (k : ℕ) (hk : k < m) :
    (univ.filter (fun j => ord d (m - k - 1) < d j)).card ≤ k ∧
    ((k = 0 ∨ ord d (m - k - 1) < ord d (m - k)) → (univ.filter (fun j => ord d (m - k - 1) < d j)).card = k) ∧
    (0 < k → ord d (m - k) = ord d (m - k - 1) → (univ.filter (fun j => ord d (m - k - 1) < d j)).card < k) := by
  set σ := Tuple.sort d
  set g : Fin m → ℝ := d ∘ σ with hg
  have hmono : Monotone g := Tuple.monotone_sort d
  have hord : ∀ j (hj : j < m), ord d j = g ⟨j, hj⟩ := fun j hj => by simp [ord, hj, hg, σ]
  have hr : m - k - 1 < m := by omega
  have hmap : (univ.filter (fun j => ord d (m - k - 1) < d j)) =
      (univ.filter (fun j => ord d (m - k - 1) < g j)).map σ.toEmbedding := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply, hg, Function.comp]
    constructor
    · intro h; exact ⟨σ.symm i, by simpa using h, by simp⟩
    · rintro ⟨j, hj, rfl⟩; exact hj
  rw [hmap, card_map, hord (m - k - 1) hr]
  have hsub : (univ.filter (fun j => g ⟨m - k - 1, hr⟩ < g j)) ⊆
      univ.filter (fun j : Fin m => m - k ≤ (j : ℕ)) := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    by_contra hcon
    push Not at hcon
    exact absurd (hmono (show j ≤ (⟨m - k - 1, hr⟩ : Fin m) from by show (j : ℕ) ≤ m - k - 1; omega))
      (not_le.2 hj)
  have hcardk : (univ.filter (fun j : Fin m => m - k ≤ (j : ℕ))).card = k := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
      (fun j : Fin m => (j : ℕ) < m - k)
    have h2 : (univ.filter (fun j : Fin m => (j : ℕ) < m - k)).card = m - k := by
      rw [Fin.card_filter_val_lt]; omega
    have h3 : (univ.filter (fun j : Fin m => ¬ (j : ℕ) < m - k)) =
        univ.filter (fun j : Fin m => m - k ≤ (j : ℕ)) := by
      ext j; simp
    rw [h3, h2, card_univ, Fintype.card_fin] at h1
    omega
  refine ⟨(card_le_card hsub).trans hcardk.le, ?_, ?_⟩
  · intro h
    refine le_antisymm ((card_le_card hsub).trans hcardk.le) ?_
    rcases Nat.eq_zero_or_pos k with h0 | hkpos
    · omega
    · have hlt := h.resolve_left (by omega)
      have hk0 : m - k < m := by omega
      rw [hord (m - k) hk0] at hlt
      calc k = _ := hcardk.symm
        _ ≤ _ := card_le_card fun j hj => ?_
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      exact lt_of_lt_of_le hlt (hmono (show (⟨m - k, hk0⟩ : Fin m) ≤ j from hj))
  · intro hk0 heq
    have hk1 : m - k < m := by omega
    rw [hord (m - k) hk1] at heq
    have hsub' : (univ.filter (fun j => g ⟨m - k - 1, hr⟩ < g j)) ⊆
        (univ.filter (fun j : Fin m => m - k ≤ (j : ℕ))).erase ⟨m - k, hk1⟩ := by
      intro j hj
      refine mem_erase.2 ⟨?_, hsub hj⟩
      rintro rfl
      simp only [mem_filter, mem_univ, true_and] at hj
      exact absurd heq (ne_of_gt hj)
    have hmem : (⟨m - k, hk1⟩ : Fin m) ∈ univ.filter (fun j : Fin m => m - k ≤ (j : ℕ)) := by
      simp only [mem_filter, mem_univ, true_and]; exact le_rfl
    calc _ ≤ _ := card_le_card hsub'
      _ < k := by rw [card_erase_of_mem hmem, hcardk]; omega

end RouteBangBang

open RouteBangBang StatFormal.TrimmedMMD.BangBang

theorem bangbang_residual : Claims.bangbang_residual := by
  intro E _ _ n m x y α β p hn hm hα0 hα1 hβ0 hβ1 hkn hkm hp hmin hpos d dx θx
  have hii := StatFormal.TrimmedMMD.BangBang.bangbang_ii E n m x y α β p hn hm hα0 hα1 hβ0 hβ1 hkn hkm hp hmin hpos
  have hres : ∑ i ∈ univ.filter (fun i => dx i = θx), p.1 i =
      1 - cap n α * (univ.filter (fun i => dx i < θx)).card := hii.2.2.1
  have hc := (cap_facts hn hα0 hα1).1
  obtain ⟨hle, heq, hlt⟩ := card_lt_ord dx (kfloor n α) hkn
  rw [hres]
  refine ⟨?_, fun h => ?_, fun h0 h1 => ?_⟩
  · have : ((univ.filter (fun i => dx i < θx)).card : ℝ) ≤ kfloor n α := by exact_mod_cast hle
    nlinarith
  · rw [heq h]; ring
  · have : ((univ.filter (fun i => dx i < θx)).card : ℝ) < kfloor n α := by exact_mod_cast hlt h0 h1
    nlinarith



theorem bangbang_residual_v : Claims.bangbang_residual_v := by
  intro E _ _ n m x y α β p hn hm hα0 hα1 hβ0 hβ1 hkn hkm hp hmin hpos d dy θy
  have hii := StatFormal.TrimmedMMD.BangBang.bangbang_ii E n m x y α β p hn hm hα0 hα1 hβ0 hβ1 hkn hkm hp hmin hpos
  have hres : ∑ j ∈ univ.filter (fun j => dy j = θy), p.2 j =
      1 - cap m β * (univ.filter (fun j => θy < dy j)).card := hii.2.2.2.2.2
  have hc := (cap_facts hm hβ0 hβ1).1
  obtain ⟨hle, heq, hlt⟩ := card_gt_ord dy (kfloor m β) hkm
  rw [hres]
  refine ⟨?_, fun h => ?_, fun h0 h1 => ?_⟩
  · have : ((univ.filter (fun j => θy < dy j)).card : ℝ) ≤ kfloor m β := by exact_mod_cast hle
    nlinarith
  · rw [heq h]; ring
  · have : ((univ.filter (fun j => θy < dy j)).card : ℝ) < kfloor m β := by exact_mod_cast hlt h0 h1
    nlinarith


theorem bangbang_iii : Claims.bangbang_iii := by
  intro E _ _ n m x y α β p₀ _hn _hm _hα0 _hα1 _hβ0 _hβ1 hp₀ _hmin₀ hzero
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hp, hmin⟩
    refine ⟨hp, ?_⟩
    have h1 : qp x y p ≤ qp x y p₀ := hmin hp₀
    rw [hzero] at h1
    have h2 : qp x y p = 0 := le_antisymm h1 (by unfold qp; positivity)
    unfold qp at h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  · rintro ⟨hp, heq⟩
    refine ⟨hp, fun q _ => ?_⟩
    show qp x y p ≤ qp x y q
    have : qp x y p = 0 := by unfold qp; rw [heq, sub_self, norm_zero]; norm_num
    rw [this]; unfold qp; positivity


theorem bangbang_iii_not_face : Claims.bangbang_iii_not_face := by
  intro E _ _ a b hab
  have hc : cap 2 (1 / 2) = 1 := by norm_num [cap]
  have hmemC : ∀ (w v : Fin 2 → ℝ), (∀ i, 0 ≤ w i ∧ w i ≤ 1) → w 0 + w 1 = 1 →
      (∀ i, 0 ≤ v i ∧ v i ≤ 1) → v 0 + v 1 = 1 → (w, v) ∈ capped 2 (1 / 2) ×ˢ capped 2 (1 / 2) := by
    intro w v hw hws hv hvs
    refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun i => ?_, ?_⟩⟩
    · rw [hc]; exact hw i
    · simpa [Fin.sum_univ_two] using hws
    · rw [hc]; exact hv i
    · simpa [Fin.sum_univ_two] using hvs
  have hnn : ∀ q, 0 ≤ qp ![a, b] ![a, b] q := fun q => by unfold qp; positivity
  set P0 : (Fin 2 → ℝ) × (Fin 2 → ℝ) := (![1 / 2, 1 / 2], ![1 / 2, 1 / 2]) with hP0def
  have hP0 : P0 ∈ capped 2 (1 / 2) ×ˢ capped 2 (1 / 2) :=
    hmemC _ _ (fun i => by fin_cases i <;> norm_num) (by norm_num) (fun i => by fin_cases i <;> norm_num)
      (by norm_num)
  have hq0 : qp ![a, b] ![a, b] P0 = 0 := by simp [qp, hP0def]
  have hmin0 : IsMinOn (qp ![a, b] ![a, b]) (capped 2 (1 / 2) ×ˢ capped 2 (1 / 2)) P0 :=
    fun q _ => by change qp ![a, b] ![a, b] P0 ≤ qp ![a, b] ![a, b] q; rw [hq0]; exact hnn q
  refine ⟨⟨P0, hP0, hmin0, hq0⟩, fun hext => ?_⟩
  have hA : ((![1, 0] : Fin 2 → ℝ), (![0, 1] : Fin 2 → ℝ)) ∈ capped 2 (1 / 2) ×ˢ capped 2 (1 / 2) :=
    hmemC _ _ (fun i => by fin_cases i <;> norm_num) (by norm_num) (fun i => by fin_cases i <;> norm_num)
      (by norm_num)
  have hB : ((![0, 1] : Fin 2 → ℝ), (![1, 0] : Fin 2 → ℝ)) ∈ capped 2 (1 / 2) ×ˢ capped 2 (1 / 2) :=
    hmemC _ _ (fun i => by fin_cases i <;> norm_num) (by norm_num) (fun i => by fin_cases i <;> norm_num)
      (by norm_num)
  have hseg : P0 ∈ openSegment ℝ ((![1, 0] : Fin 2 → ℝ), (![0, 1] : Fin 2 → ℝ))
      ((![0, 1] : Fin 2 → ℝ), (![1, 0] : Fin 2 → ℝ)) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [hP0def]
    ext i <;> fin_cases i <;> simp <;> norm_num
  have hAmin := (hext.2 hA hB ⟨hP0, hmin0⟩ hseg).2
  have hle : qp ![a, b] ![a, b] ((![1, 0] : Fin 2 → ℝ), (![0, 1] : Fin 2 → ℝ)) ≤ 0 := by
    have h := hAmin hP0
    change qp ![a, b] ![a, b] ((![1, 0] : Fin 2 → ℝ), (![0, 1] : Fin 2 → ℝ)) ≤ qp ![a, b] ![a, b] P0 at h
    rwa [hq0] at h
  have hval : qp ![a, b] ![a, b] ((![1, 0] : Fin 2 → ℝ), (![0, 1] : Fin 2 → ℝ)) = ‖a - b‖ ^ 2 := by
    simp [qp, Fin.sum_univ_two]
  rw [hval] at hle
  have : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact hab (sub_eq_zero.1 (norm_eq_zero.1 this))

end StatFormal.WaveP1d
