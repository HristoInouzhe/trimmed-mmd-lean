import StatFormal.Archive.OTFD.Bands2.Statements
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Route: `prop:band-saturation` (saturation caps) and its preamble claims
-/

noncomputable section
open Finset

namespace StatFormal.OTFD.Bands2

open StatFormal.OTFD.Bands

variable {n : ℕ}

/-- Variational inequality of the simplex projection: if `q_j > 0` then `q_j − x_j ≤ q_k − x_k`. -/
lemma proj_var (x q : Fin n → ℝ) (hq : IsSimplexProj x q) (j k : Fin n) (hqj : 0 < q j) :
    q j - x j ≤ q k - x k := by
  by_cases hkj : k = j
  · subst hkj; exact le_rfl
  have hq0 := hq.1.1
  have hq1 := hq.1.2
  by_contra hcon
  push Not at hcon
  set c := (q j - x j) - (q k - x k) with hc
  have hc0 : 0 < c := by linarith
  set ε := min (q j) (c / 2) with hε
  have hε0 : 0 < ε := lt_min hqj (by linarith)
  have hεq : ε ≤ q j := min_le_left _ _
  have hεc : ε ≤ c / 2 := min_le_right _ _
  set e : Fin n → ℝ := fun i => (if i = k then 1 else 0) - (if i = j then 1 else 0) with he
  set q' : Fin n → ℝ := fun i => q i + ε * e i with hq'
  have hmem : q' ∈ simplex n := by
    refine ⟨fun i => ?_, ?_⟩
    · simp only [hq', he]
      by_cases hik : i = k
      · subst hik
        simp [hkj]
        linarith [hq0 i]
      · by_cases hij : i = j
        · subst hij; simp [hik]; linarith
        · simp [hik, hij, hq0 i]
    · simp only [hq', he, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, hq1]
      ring
  have hopt := hq.2 q' hmem
  have hpt : ∀ i, (q' i - x i) ^ 2 = (q i - x i) ^ 2 + 2 * ε * (e i * (q i - x i)) +
      ε ^ 2 * ((if i = k then 1 else 0) + (if i = j then 1 else 0)) := by
    intro i
    simp only [hq', he]
    by_cases hik : i = k
    · subst hik; simp [hkj]; ring
    · by_cases hij : i = j
      · subst hij; simp [hik]; ring
      · simp [hik, hij]
  rw [Finset.sum_congr rfl fun i _ => hpt i] at hopt
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, he, sub_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hopt
  nlinarith

lemma proj_le_one (x q : Fin n → ℝ) (hq : IsSimplexProj x q) (i : Fin n) : q i ≤ 1 := by
  have := Finset.single_le_sum (f := q) (fun i _ => hq.1.1 i) (Finset.mem_univ i)
  linarith [hq.1.2]

lemma satF_strictMono (lam : ℝ) (G : Fin n → ℝ) (j : Fin n) : StrictMono (satF lam G j) := by
  intro c d hcd
  unfold satF
  have : ∑ l ∈ univ.erase j, max 0 (c - G l / lam) ≤ ∑ l ∈ univ.erase j, max 0 (d - G l / lam) :=
    Finset.sum_le_sum fun l _ => max_le_max le_rfl (by linarith)
  linarith

lemma satF_continuous (lam : ℝ) (G : Fin n → ℝ) (j : Fin n) : Continuous (satF lam G j) := by
  unfold satF
  refine continuous_id.add (continuous_finsetSum _ fun l _ => ?_)
  exact continuous_const.max (continuous_id.sub continuous_const)

lemma satF_one_ge (lam : ℝ) (G : Fin n → ℝ) (j : Fin n) : 1 ≤ satF lam G j 1 := by
  unfold satF
  have : 0 ≤ ∑ l ∈ univ.erase j, max 0 (1 - G l / lam) :=
    Finset.sum_nonneg fun l _ => le_max_left _ _
  linarith

/-- When `F_j(0) < 1`, the cap is a root in `(0, 1]`. -/
lemma satCapQuad_root (lam : ℝ) (G : Fin n → ℝ) (j : Fin n) (h0 : satF lam G j 0 < 1) :
    0 < satCapQuad lam G j ∧ satCapQuad lam G j ≤ 1 ∧ satF lam G j (satCapQuad lam G j) = 1 := by
  have hmono := satF_strictMono lam G j
  have hcont := satF_continuous lam G j
  have hS : satCapQuad lam G j = sInf {c | 1 ≤ satF lam G j c} := by
    unfold satCapQuad; rw [if_neg (not_le.mpr h0)]
  set S := {c | 1 ≤ satF lam G j c} with hSdef
  have h1S : (1 : ℝ) ∈ S := satF_one_ge lam G j
  have hpos : ∀ c ∈ S, 0 < c := by
    intro c hc
    by_contra hc0
    push Not at hc0
    have := hmono.monotone hc0
    simp only [hSdef, Set.mem_ofPred_eq] at hc
    linarith
  have hbdd : BddBelow S := ⟨0, fun c hc => (hpos c hc).le⟩
  have hclosed : IsClosed S := isClosed_le continuous_const hcont
  have hmem : sInf S ∈ S := hclosed.csInf_mem ⟨1, h1S⟩ hbdd
  have hle1 : sInf S ≤ 1 := csInf_le hbdd h1S
  have hκpos : 0 < sInf S := hpos _ hmem
  rw [hS]
  refine ⟨hκpos, hle1, ?_⟩
  -- intermediate value on `[0, κ]`
  have hmemS : 1 ≤ satF lam G j (sInf S) := hmem
  obtain ⟨c, hc, hFc⟩ := intermediate_value_Icc hκpos.le hcont.continuousOn
    ⟨h0.le, hmemS⟩
  have hcS : c ∈ S := by simp only [hSdef, Set.mem_ofPred_eq]; rw [hFc]
  have : sInf S ≤ c := csInf_le hbdd hcS
  have hceq : c = sInf S := le_antisymm hc.2 this
  rw [← hceq, hFc]

lemma satCapQuad_nonneg (lam : ℝ) (G : Fin n → ℝ) (j : Fin n) : 0 ≤ satCapQuad lam G j := by
  by_cases h : 1 ≤ satF lam G j 0
  · unfold satCapQuad; rw [if_pos h]
  · exact (satCapQuad_root lam G j (not_le.mp h)).1.le

/-- `F_j(q_j) ≤ 1` whenever `q_j > 0`. -/
lemma satF_le_one {K m : ℕ} (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (γ : ℝ) (G : Fin n → ℝ)
    (j : Fin n) (u : Fin K → ℝ) (q : Fin n → ℝ) (hγ : 0 < γ) (hm : 0 < m)
    (hG : ∀ l, l ≠ j → score a b j u - score a b l u ≤ G l)
    (hq : IsSimplexProj (fun k => score a b k u / (γ / m)) q) (hqj : 0 < q j) :
    satF (γ / m) G j (q j) ≤ 1 := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hlam : 0 < γ / m := div_pos hγ hmr
  have hsum : q j + ∑ l ∈ univ.erase j, q l = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ j)]; exact hq.1.2
  unfold satF
  have : ∑ l ∈ univ.erase j, max 0 (q j - G l / (γ / m)) ≤ ∑ l ∈ univ.erase j, q l := by
    refine Finset.sum_le_sum fun l hl => ?_
    have hlj : l ≠ j := Finset.ne_of_mem_erase hl
    have hv := proj_var _ q hq j l hqj
    have hG' : (score a b j u - score a b l u) / (γ / m) ≤ G l / (γ / m) :=
      div_le_div_of_nonneg_right (hG l hlj) hlam.le
    have hsplit : (score a b j u - score a b l u) / (γ / m) =
        score a b j u / (γ / m) - score a b l u / (γ / m) := sub_div _ _ _
    refine max_le (hq.1.1 l) ?_
    linarith
  linarith

namespace Claims

theorem sat_gap_closed_form_proof : sat_gap_closed_form := by
  intro n K a b A j l σ h
  have key : ∀ u, score a b j u - score a b l u = a j - a l + (b j - b l) ⬝ᵥ u := by
    intro u; unfold score; rw [sub_dotProduct]; ring
  obtain ⟨⟨u0, hu0, hu0σ⟩, hub⟩ := h
  refine ⟨⟨u0, hu0, by simp only [key, hu0σ]⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have := hub ⟨u, hu, rfl⟩
  simp only [key]
  linarith

theorem sat_cap_entropic_proof : sat_cap_entropic := by
  intro n K a b ε G j u hε hG
  set x : Fin n → ℝ := fun k => score a b k u / ε with hx
  unfold softmax satCapEnt
  set W := ∑ l ∈ univ.erase j, Real.exp (-G l / ε)
  have hW : 0 ≤ W := Finset.sum_nonneg fun l _ => (Real.exp_pos _).le
  have hS : ∑ k, Real.exp (x k) = Real.exp (x j) + ∑ l ∈ univ.erase j, Real.exp (x l) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have hSpos : 0 < ∑ k, Real.exp (x k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j, Finset.mem_univ j⟩
  rw [div_le_iff₀ hSpos, inv_mul_eq_div, le_div_iff₀ (by linarith), hS, mul_add, mul_one,
    Finset.mul_sum]
  have : ∑ l ∈ univ.erase j, Real.exp (x j) * Real.exp (-G l / ε) ≤
      ∑ l ∈ univ.erase j, Real.exp (x l) := by
    refine Finset.sum_le_sum fun l hl => ?_
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := hG l (Finset.ne_of_mem_erase hl)
    simp only [hx]
    have hr : score a b j u / ε + -G l / ε = (score a b j u - G l) / ε := by ring
    rw [hr]
    apply div_le_div_of_nonneg_right _ hε.le
    linarith
  linarith

theorem sat_cap_quadratic_proof : sat_cap_quadratic := by
  intro n K m a b γ G j u q hγ hm hG hq
  have hmono := satF_strictMono (γ / m) G j
  by_cases h0 : 1 ≤ satF (γ / m) G j 0
  · have hκ : satCapQuad (γ / m) G j = 0 := by unfold satCapQuad; rw [if_pos h0]
    rw [hκ]
    by_contra hpos
    push Not at hpos
    have h1 := satF_le_one a b γ G j u q hγ hm hG hq hpos
    have h2 := hmono hpos
    linarith
  · obtain ⟨hκ0, -, hκ1⟩ := satCapQuad_root (γ / m) G j (not_le.mp h0)
    by_cases hqj : q j ≤ 0
    · linarith
    push Not at hqj
    have h1 := satF_le_one a b γ G j u q hγ hm hG hq hqj
    rw [← hκ1] at h1
    exact hmono.le_iff_le.mp h1

theorem sat_root_proof : sat_root := by
  intro n lam G j _
  exact ⟨satF_strictMono lam G j, satCapQuad_root lam G j⟩

theorem sat_mono_proof : sat_mono := by
  intro n ε lam G G' j hε hlam hGG
  constructor
  · unfold satCapEnt
    have hle : ∑ l ∈ univ.erase j, Real.exp (-G' l / ε) ≤ ∑ l ∈ univ.erase j, Real.exp (-G l / ε) :=
      Finset.sum_le_sum fun l _ => Real.exp_le_exp.mpr
        (div_le_div_of_nonneg_right (by linarith [hGG l]) hε.le)
    have hpos : 0 < 1 + ∑ l ∈ univ.erase j, Real.exp (-G' l / ε) := by
      have := Finset.sum_nonneg fun l (_ : l ∈ univ.erase j) => (Real.exp_pos (-G' l / ε)).le
      linarith
    exact inv_anti₀ hpos (by linarith)
  · have hF : ∀ c, satF lam G' j c ≤ satF lam G j c := by
      intro c
      unfold satF
      have : ∑ l ∈ univ.erase j, max 0 (c - G' l / lam) ≤ ∑ l ∈ univ.erase j, max 0 (c - G l / lam) :=
        Finset.sum_le_sum fun l _ => max_le_max le_rfl (by
          have : G l / lam ≤ G' l / lam := div_le_div_of_nonneg_right (hGG l) hlam.le
          linarith)
      linarith
    by_cases h0 : 1 ≤ satF lam G j 0
    · have : satCapQuad lam G j = 0 := by unfold satCapQuad; rw [if_pos h0]
      rw [this]; exact satCapQuad_nonneg lam G' j
    · have h0' : satF lam G' j 0 < 1 := lt_of_le_of_lt (hF 0) (not_le.mp h0)
      obtain ⟨-, -, hκ⟩ := satCapQuad_root lam G j (not_le.mp h0)
      obtain ⟨-, -, hκ'⟩ := satCapQuad_root lam G' j h0'
      have : satF lam G' j (satCapQuad lam G j) ≤ satF lam G' j (satCapQuad lam G' j) := by
        rw [hκ']; exact (hF _).trans hκ.le
      exact (satF_strictMono lam G' j).le_iff_le.mp this

theorem sparsemax_vertex_proof : sparsemax_vertex := by
  intro n x q j hx hq
  have hzero : ∀ l, l ≠ j → q l = 0 := by
    intro l hlj
    by_contra hne
    have hpos : 0 < q l := lt_of_le_of_ne (hq.1.1 l) (Ne.symm hne)
    have hv := proj_var x q hq l j hpos
    have h1 := proj_le_one x q hq j
    have h2 := hx l hlj
    linarith
  have hsum : q j + ∑ l ∈ univ.erase j, q l = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ j)]; exact hq.1.2
  have hrest : ∑ l ∈ univ.erase j, q l = 0 :=
    Finset.sum_eq_zero fun l hl => hzero l (Finset.ne_of_mem_erase hl)
  funext i
  by_cases hij : i = j
  · subst hij; rw [Pi.single_eq_same]; linarith
  · rw [Pi.single_eq_of_ne hij]; exact hzero i hij

theorem softmax_not_vertex_proof : softmax_not_vertex := by
  intro n x j hn
  unfold softmax
  have hSpos : 0 < ∑ k, Real.exp (x k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j, Finset.mem_univ j⟩
  refine ⟨div_pos (Real.exp_pos _) hSpos, ?_⟩
  rw [div_lt_one hSpos]
  obtain ⟨l, hl⟩ : ∃ l : Fin n, l ≠ j := by
    by_cases h : j = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h h'.symm⟩
  have hS : ∑ k, Real.exp (x k) = Real.exp (x j) + ∑ k ∈ univ.erase j, Real.exp (x k) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have : Real.exp (x l) ≤ ∑ k ∈ univ.erase j, Real.exp (x k) :=
    Finset.single_le_sum (f := fun k => Real.exp (x k)) (fun k _ => (Real.exp_pos _).le)
      (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩)
  linarith [Real.exp_pos (x l)]

end Claims

theorem sat_gap_closed_form : Claims.sat_gap_closed_form := Claims.sat_gap_closed_form_proof
theorem sat_cap_entropic : Claims.sat_cap_entropic := Claims.sat_cap_entropic_proof
theorem sat_cap_quadratic : Claims.sat_cap_quadratic := Claims.sat_cap_quadratic_proof
theorem sat_root : Claims.sat_root := Claims.sat_root_proof
theorem sat_mono : Claims.sat_mono := Claims.sat_mono_proof
theorem sparsemax_vertex : Claims.sparsemax_vertex := Claims.sparsemax_vertex_proof
theorem softmax_not_vertex : Claims.softmax_not_vertex := Claims.softmax_not_vertex_proof

end StatFormal.OTFD.Bands2
