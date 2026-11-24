import StatFormal.Archive.OTFD.Bands.Statements
import StatFormal.Archive.OTFD.Bands.Tilt
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Monotone
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.BigOperators.Field

/-!
# Proofs: `prop:band-boundary`, `prop:band-certificate`, `lem:ext-solver-error`
-/

noncomputable section
open Finset Matrix

namespace StatFormal.OTFD.Bands

section Boundary

variable {K : ℕ} {M : Matrix (Fin K) (Fin K) ℝ}

lemma transpose_eq (hM : M.PosDef) : Mᵀ = M :=
  (conjTranspose_eq_transpose_of_trivial M).symm.trans hM.isHermitian

lemma mul_inv_eq' (hM : M.PosDef) : M * M⁻¹ = 1 :=
  mul_nonsing_inv M ((isUnit_iff_isUnit_det M).mp hM.isUnit)

lemma mulVec_dot_inv (hM : M.PosDef) (a v : Fin K → ℝ) :
    (M *ᵥ a) ⬝ᵥ (M⁻¹ *ᵥ v) = a ⬝ᵥ v := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, transpose_eq hM, mulVec_mulVec,
    mul_inv_eq' hM, one_mulVec, dotProduct_comm]

end Boundary

namespace Claims

theorem band_boundary_mono_proof : band_boundary_mono := by
  intro K M ψ T hM _ hsub u v s s' hss'
  set w := M⁻¹ *ᵥ v
  have h1 := hsub (u + s • w) (u + s' • w)
  have h2 := hsub (u + s' • w) (u + s • w)
  have e1 : (u + s' • w) - (u + s • w) = (s' - s) • w := by rw [sub_smul]; abel
  have e2 : (u + s • w) - (u + s' • w) = (s - s') • w := by rw [sub_smul]; abel
  have hd : ∀ a, (M *ᵥ a) ⬝ᵥ w = a ⬝ᵥ v := fun a => mulVec_dot_inv hM a v
  have h2s : ∀ X Y : Fin K → ℝ, (2 • X) ⬝ᵥ Y = 2 * (X ⬝ᵥ Y) := by
    intro X Y; rw [two_nsmul, add_dotProduct]; ring
  rw [e1, h2s, dotProduct_smul, smul_eq_mul, hd] at h1
  rw [e2, h2s, dotProduct_smul, smul_eq_mul, hd] at h2
  show v ⬝ᵥ T (u + s • w) ≤ v ⬝ᵥ T (u + s' • w)
  rw [dotProduct_comm v, dotProduct_comm v]
  rcases hss'.lt_or_eq with h | h
  · have hpos : 0 < s' - s := sub_pos.mpr h
    nlinarith
  · rw [h]

theorem band_boundary_sup_proof : band_boundary_sup := by
  intro K M ψ T hK hM hconv hsub A hA v u hu
  have mono := band_boundary_mono_proof K M ψ T hM hconv hsub
  by_cases hv : v = 0
  · subst hv
    have hne : A ≠ Set.univ := by
      intro hAu
      obtain ⟨B, hB⟩ := hA.bddAbove_image (f := fun p : Fin K → ℝ => p ⟨0, hK⟩)
        (continuous_apply _).continuousOn
      have : B + 1 ≤ B := hB ⟨fun _ => B + 1, by rw [hAu]; trivial, rfl⟩
      linarith
    obtain ⟨u', hu'⟩ := nonempty_frontier_iff.mpr ⟨⟨u, hu⟩, hne⟩
    exact ⟨u', hu', by simp⟩
  · set w := M⁻¹ *ᵥ v
    have hw : w ≠ 0 := by
      intro h0
      apply hv
      have : M *ᵥ w = v := by
        simp only [w, mulVec_mulVec, mul_inv_eq' hM, one_mulVec]
      rw [← this, h0, mulVec_zero]
    have hww : 0 < w ⬝ᵥ w := by
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
      have h1 := Finset.single_le_sum (f := fun i => w i * w i) (fun i _ => mul_self_nonneg (w i))
        (Finset.mem_univ k)
      have h2 := mul_self_pos.mpr hk
      simp only [dotProduct]
      linarith
    set g : ℝ → (Fin K → ℝ) := fun s => u + s • w with hg
    have hgc : Continuous g := by fun_prop
    set S : Set ℝ := Set.Ici 0 ∩ g ⁻¹' A
    have hSc : IsClosed S := isClosed_Ici.inter (hA.isClosed.preimage hgc)
    have hSne : S.Nonempty := ⟨0, Set.mem_Ici.mpr le_rfl, by simpa [g] using hu⟩
    obtain ⟨B, hB⟩ := hA.bddAbove_image (f := fun p : Fin K → ℝ => w ⬝ᵥ p)
      (by fun_prop : Continuous fun p : Fin K → ℝ => w ⬝ᵥ p).continuousOn
    have hSb : BddAbove S := by
      refine ⟨(B - w ⬝ᵥ u) / (w ⬝ᵥ w), fun s hs => ?_⟩
      have := hB ⟨g s, hs.2, rfl⟩
      simp only [g, dotProduct_add, dotProduct_smul, smul_eq_mul] at this
      rw [le_div_iff₀ hww]
      linarith
    set s0 := sSup S
    have hs0 : s0 ∈ S := hSc.csSup_mem hSne hSb
    refine ⟨g s0, ?_, ?_⟩
    · refine ⟨subset_closure hs0.2, fun hint => ?_⟩
      have hn : g ⁻¹' interior A ∈ nhds s0 :=
        hgc.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint)
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
      have hin : s0 + ε / 2 ∈ g ⁻¹' interior A := by
        apply hball
        rw [Metric.mem_ball, Real.dist_eq]
        rw [show s0 + ε / 2 - s0 = ε / 2 by ring, abs_of_pos (by linarith)]
        linarith
      have hmem : s0 + ε / 2 ∈ S := ⟨by have := hs0.1; simp only [Set.mem_Ici] at this ⊢; linarith,
        show g (s0 + ε / 2) ∈ A from interior_subset hin⟩
      have := le_csSup hSb hmem
      linarith
    · have h0 : (0 : ℝ) ≤ s0 := hs0.1
      have := mono u v h0
      simpa using this

lemma le_iSup_fin {n : ℕ} (f : Fin n → ℝ) (k : Fin n) : f k ≤ ⨆ i, f i :=
  le_ciSup (Finite.bddAbove_range f) k

lemma iInf_le_fin {n : ℕ} (f : Fin n → ℝ) (k : Fin n) : ⨅ i, f i ≤ f k :=
  ciInf_le (Finite.bddBelow_range f) k

theorem band_gap_zero_iff_proof : band_gap_zero_iff := by
  intro n K a b A j hA hne
  have : Nonempty (Fin n) := ⟨j⟩
  set F : (Fin K → ℝ) → ℝ := fun u => (⨆ k, score a b k u) - score a b j u with hF
  have hF0 : ∀ u, 0 ≤ F u := fun u => sub_nonneg.mpr (le_iSup_fin (fun k => score a b k u) j)
  have hgap : gap a b A j = sInf (F '' A) := rfl
  have hnn : 0 ≤ gap a b A j := by
    rw [hgap]
    exact le_csInf (hne.image F) (by rintro _ ⟨u, _, rfl⟩; exact hF0 u)
  refine ⟨hnn, ⟨fun h0 => ?_, fun ⟨u, hu, hk⟩ => ?_⟩⟩
  · have hsup : (fun u => ⨆ k, score a b k u) =
        fun u => (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty
          (fun k => score a b k u) := by
      ext u
      rw [Finset.sup'_univ_eq_ciSup]
    have hFc : Continuous F := by
      have : Continuous fun u => (⨆ k, score a b k u) := by
        rw [hsup]
        exact Continuous.finset_sup'_apply _ fun k _ => by unfold score; fun_prop
      exact this.sub (by unfold score; fun_prop)
    obtain ⟨u0, hu0, hmin⟩ := hA.exists_isMinOn hne hFc.continuousOn
    have hleast : IsLeast (F '' A) (F u0) :=
      ⟨⟨u0, hu0, rfl⟩, by rintro _ ⟨u, hu, rfl⟩; exact hmin hu⟩
    rw [hgap, hleast.csInf_eq] at h0
    refine ⟨u0, hu0, fun k => ?_⟩
    have := le_iSup_fin (fun k => score a b k u0) k
    simp only [hF] at h0
    linarith
  · have hFu : F u ≤ 0 := by
      simp only [hF, sub_nonpos]
      exact ciSup_le hk
    have : gap a b A j ≤ F u := by
      rw [hgap]
      exact csInf_le ⟨0, by rintro _ ⟨u, _, rfl⟩; exact hF0 u⟩ ⟨u, hu, rfl⟩
    linarith

theorem band_dual_cert_proof : band_dual_cert := by
  intro n K a b A j w σA hne hw hσ
  have : Nonempty (Fin n) := ⟨j⟩
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨u, hu, rfl⟩
  have h1 : ∑ k, w k * score a b k u ≤ ⨆ k, score a b k u := by
    calc ∑ k, w k * score a b k u ≤ ∑ k, w k * ⨆ i, score a b i u :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (le_iSup_fin (fun i => score a b i u) k) (hw.1 k)
      _ = ⨆ k, score a b k u := by rw [← Finset.sum_mul, hw.2, one_mul]
  have h2 : ∑ k, w k * score a b k u = ∑ k, w k * a k + (∑ k, w k • b k) ⬝ᵥ u := by
    simp only [score, mul_add, Finset.sum_add_distrib, sum_dotProduct, smul_dotProduct,
      smul_eq_mul]
  have h3 := hσ u hu
  rw [sub_dotProduct] at h3
  show ∑ k, w k * a k - a j - σA ≤ (⨆ k, score a b k u) - score a b j u
  simp only [score] at h1 h2 ⊢
  linarith

theorem band_cap_entropic_proof : band_cap_entropic := by
  intro n K a b ε δ j u hε hδ
  have : Nonempty (Fin n) := ⟨j⟩
  obtain ⟨k, hk⟩ := exists_eq_ciSup_of_finite (f := fun k => score a b k u)
  unfold softmax
  have hsum : Real.exp (score a b k u / ε) ≤ ∑ i, Real.exp (score a b i u / ε) :=
    Finset.single_le_sum (f := fun i => Real.exp (score a b i u / ε))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ k)
  calc Real.exp (score a b j u / ε) / ∑ i, Real.exp (score a b i u / ε)
      ≤ Real.exp (score a b j u / ε) / Real.exp (score a b k u / ε) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hsum
    _ = Real.exp ((score a b j u - score a b k u) / ε) := by rw [← Real.exp_sub, sub_div]
    _ ≤ Real.exp (-δ / ε) := by
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ hε.le
        linarith

theorem band_cap_quadratic_proof : band_cap_quadratic := by
  intro n K m a b γ δ j u q hγ hm hδ hq
  have : Nonempty (Fin n) := ⟨j⟩
  obtain ⟨k, hk⟩ := exists_eq_ciSup_of_finite (f := fun k => score a b k u)
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  set x : Fin n → ℝ := fun k => score a b k u / (γ / m) with hx
  have hq0 := hq.1.1
  have hq1 := hq.1.2
  have hle1 : ∀ i, q i ≤ 1 := fun i => by
    have := Finset.single_le_sum (f := q) (fun i _ => hq0 i) (Finset.mem_univ i)
    linarith
  by_cases hqj : q j ≤ 0
  · exact hqj.trans (le_max_left _ _)
  push Not at hqj
  by_cases hkj : k = j
  · subst hkj
    have hδ0 : δ ≤ 0 := by rw [← hk] at hδ; linarith
    have : m * δ / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith) hγ.le
    exact (hle1 k).trans (by linarith [le_max_right 0 (1 - m * δ / γ)])
  -- variational inequality
  have hvar : q j - x j ≤ q k - x k := by
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
  have hxk : x k - x j = (score a b k u - score a b j u) * m / γ := by
    simp only [hx]
    field_simp
  have hδ' : m * δ / γ ≤ x k - x j := by
    rw [hxk]
    apply div_le_div_of_nonneg_right _ hγ.le
    rw [hk]
    nlinarith
  have := hle1 k
  exact le_max_of_le_right (by linarith)

lemma dot_Qent {n K : ℕ} (ε : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ)
    (g : Fin n → ℝ) (u v : Fin K → ℝ) :
    v ⬝ᵥ Qent ε M Z g u =
      (∑ i, Real.exp ((g i - mnormSq M (u - Z i)) / ε) * (v ⬝ᵥ Z i)) /
        ∑ i, Real.exp ((g i - mnormSq M (u - Z i)) / ε) := by
  unfold Qent softmax
  rw [dotProduct_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_smul, smul_eq_mul]
  ring

lemma tanh_eq_sqrt (A : ℝ) :
    Real.tanh (A / 4) = (√(Real.exp A) - 1) / (√(Real.exp A) + 1) := by
  rw [tanh_formula, ← Real.exp_half]
  ring_nf

theorem ext_solver_error_proof : ext_solver_error := by
  intro n K ε M Z f f' u v hn hε hM
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [dotProduct_sub, dot_Qent, dot_Qent]
  set a : Fin n → ℝ := fun i => Real.exp ((f i - mnormSq M (u - Z i)) / ε) with ha
  set t : Fin n → ℝ := fun i => Real.exp (-(f i - f' i) / ε) with ht
  have hat : ∀ i, Real.exp ((f' i - mnormSq M (u - Z i)) / ε) = a i * t i := by
    intro i
    simp only [ha, ht]
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [hat]
  set dmax := ⨆ j, (f j - f' j)
  set dmin := ⨅ j, (f j - f' j)
  set t0 := Real.exp (-dmax / ε)
  set R := Real.exp ((dmax - dmin) / ε)
  have hT : Real.tanh ((dmax - dmin) / (4 * ε)) = (√R - 1) / (√R + 1) := by
    rw [show (dmax - dmin) / (4 * ε) = ((dmax - dmin) / ε) / 4 by field_simp]
    exact tanh_eq_sqrt _
  rw [hT]
  refine tilt_bound a t (fun i => v ⬝ᵥ Z i) t0 R _ _ (fun i => Real.exp_pos _)
    (Real.exp_pos _) (fun i => ⟨?_, ?_⟩) (fun i => ⟨iInf_le_fin (fun j => v ⬝ᵥ Z j) i, le_iSup_fin (fun j => v ⬝ᵥ Z j) i⟩)
  · simp only [ht, t0]
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hε.le
    linarith [le_iSup_fin (fun j => f j - f' j) i]
  · simp only [ht, t0, R]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hε.le
    linarith [iInf_le_fin (fun j => f j - f' j) i]

lemma iSup_two (F : Fin 2 → ℝ) : (⨆ j, F j) = max (F 0) (F 1) := by
  refine le_antisymm (ciSup_le fun j => ?_) (max_le (le_iSup_fin F 0) (le_iSup_fin F 1))
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_right _ _

lemma iInf_two (F : Fin 2 → ℝ) : (⨅ j, F j) = min (F 0) (F 1) := by
  refine le_antisymm (le_min (iInf_le_fin F 0) (iInf_le_fin F 1)) (le_ciInf fun j => ?_)
  fin_cases j
  · exact min_le_left _ _
  · exact min_le_right _ _

lemma softmax_two (x : Fin 2 → ℝ) :
    softmax x 0 = Real.exp (x 0 - x 1) / (Real.exp (x 0 - x 1) + 1) ∧
      softmax x 1 = 1 - softmax x 0 := by
  unfold softmax
  rw [Fin.sum_univ_two]
  have h0 := Real.exp_pos (x 0)
  have h1 := Real.exp_pos (x 1)
  have he : Real.exp (x 0 - x 1) = Real.exp (x 0) / Real.exp (x 1) := Real.exp_sub _ _
  rw [he]
  constructor
  · field_simp
  · field_simp
    ring

lemma dot_Qent_two {K : ℕ} (ε : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin 2 → Fin K → ℝ)
    (f f' : Fin 2 → ℝ) (u v : Fin K → ℝ) :
    v ⬝ᵥ (Qent ε M Z f u - Qent ε M Z f' u) =
      (softmax (fun j => (f j - mnormSq M (u - Z j)) / ε) 0 -
        softmax (fun j => (f' j - mnormSq M (u - Z j)) / ε) 0) * (v ⬝ᵥ Z 0 - v ⬝ᵥ Z 1) := by
  unfold Qent
  rw [dotProduct_sub, dotProduct_sum, dotProduct_sum, Fin.sum_univ_two, Fin.sum_univ_two,
    (softmax_two _).2, (softmax_two (fun j => (f' j - mnormSq M (u - Z j)) / ε)).2]
  simp only [dotProduct_smul, smul_eq_mul]
  ring

lemma mnormSq_smul {K : ℕ} (M : Matrix (Fin K) (Fin K) ℝ) (c : ℝ) (x : Fin K → ℝ) :
    mnormSq M (c • x) = c ^ 2 * mnormSq M x := by
  unfold mnormSq
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem ext_solver_sharp_proof : ext_solver_sharp := by
  intro K ε M Z f f' v hε hM
  rw [iSup_two, iInf_two, iSup_two, iInf_two, max_sub_min_eq_abs, max_sub_min_eq_abs]
  by_cases hZ : Z 0 = Z 1
  · refine ⟨0, ?_⟩
    rw [dot_Qent_two, hZ]
    simp
  set Dz := Z 0 - Z 1 with hDz
  have hD0 : Dz ≠ 0 := sub_ne_zero.mpr hZ
  set w := mnormSq M Dz with hw
  have hwpos : 0 < w := by
    have := hM.dotProduct_mulVec_pos hD0
    simpa [hw, mnormSq] using this
  set Δ := (f 0 - f' 0) - (f 1 - f' 1) with hΔ
  set τ := (Δ / 2 - (f 0 - f 1) + w) / (2 * w) with hτ
  refine ⟨Z 1 + τ • Dz, ?_⟩
  have hu0 : Z 1 + τ • Dz - Z 0 = (τ - 1) • Dz := by
    ext i
    simp only [hDz, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hu1 : Z 1 + τ • Dz - Z 1 = τ • Dz := add_sub_cancel_left _ _
  rw [dot_Qent_two, (softmax_two _).1, (softmax_two _).1]
  simp only [hu0, hu1, mnormSq_smul]
  have hx : (f 0 - (τ - 1) ^ 2 * w) / ε - (f 1 - τ ^ 2 * w) / ε = Δ / (2 * ε) := by
    rw [hτ]
    field_simp
    ring
  have hx' : (f' 0 - (τ - 1) ^ 2 * w) / ε - (f' 1 - τ ^ 2 * w) / ε = -(Δ / (2 * ε)) := by
    rw [hτ, hΔ]
    field_simp
    ring
  rw [hx, hx', Real.exp_neg]
  have hE := Real.exp_pos (Δ / (2 * ε))
  have htanh : Real.tanh (Δ / (4 * ε)) =
      Real.exp (Δ / (2 * ε)) / (Real.exp (Δ / (2 * ε)) + 1) -
        (Real.exp (Δ / (2 * ε)))⁻¹ / ((Real.exp (Δ / (2 * ε)))⁻¹ + 1) := by
    rw [tanh_formula, show 2 * (Δ / (4 * ε)) = Δ / (2 * ε) by field_simp; ring]
    field_simp
    ring
  rw [← htanh, abs_mul, abs_tanh, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 4 * ε),
    abs_sub_comm (v ⬝ᵥ Z 1), abs_sub_comm (f 1 - f' 1)]

end Claims

end StatFormal.OTFD.Bands

namespace StatFormal.OTFD.Bands

theorem band_boundary_mono : Claims.band_boundary_mono := Claims.band_boundary_mono_proof
theorem band_boundary_sup : Claims.band_boundary_sup := Claims.band_boundary_sup_proof
theorem band_gap_zero_iff : Claims.band_gap_zero_iff := Claims.band_gap_zero_iff_proof
theorem band_dual_cert : Claims.band_dual_cert := Claims.band_dual_cert_proof
theorem band_cap_entropic : Claims.band_cap_entropic := Claims.band_cap_entropic_proof
theorem band_cap_quadratic : Claims.band_cap_quadratic := Claims.band_cap_quadratic_proof
theorem ext_solver_error : Claims.ext_solver_error := Claims.ext_solver_error_proof
theorem ext_solver_sharp : Claims.ext_solver_sharp := Claims.ext_solver_sharp_proof

end StatFormal.OTFD.Bands
