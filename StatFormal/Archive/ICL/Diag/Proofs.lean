import StatFormal.Archive.ICL.Diag.Statements
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Proofs: `cor:oracle`, `prop:diag-vertex`, `prop:diag-cap` (untrusted proof file)

Routes (the paper's):
* oracle: order algebra on infima;
* diag-vertex: a non-vertex minimiser `w` has two positive coordinates `i ≠ j`; along
  `v = e_i − e_j` the objective `G(t) = F(w + t v) − λ KL(w + t v)` has
  `G'' ≤ 2 L_F − λ (1/(w_i+t) + 1/(w_j−t)) ≤ 2 L_F − 4 λ < 0`, so it is strictly concave near `0`
  and `G(t) + G(−t) < 2 G(0)` contradicts minimality;
* diag-cap: `KL ≤ log c` on `C_c` with equality at the uniform law on `S`, and the fractional
  knapsack (threshold) argument for the linear part.
-/

noncomputable section
open Finset Real

namespace StatFormal.ICL.Diag

theorem oracle : Claims.oracle := by
  intro ι S Jm Jp dev εopt wh hwh hdev hbdd hmin
  have hne : (Jp '' S).Nonempty := ⟨_, wh, hwh, rfl⟩
  have hbddm : BddBelow (Jm '' S) := by
    obtain ⟨b, hb⟩ := hbdd
    refine ⟨b - dev, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have := hb ⟨w, hw, rfl⟩
    have := (abs_le.mp (hdev w hw)).1
    linarith
  have h1 : sInf (Jm '' S) - dev ≤ sInf (Jp '' S) := by
    refine le_csInf hne ?_
    rintro _ ⟨w, hw, rfl⟩
    have := csInf_le hbddm ⟨w, hw, rfl⟩
    have := (abs_le.mp (hdev w hw)).2
    linarith
  have := (abs_le.mp (hdev wh hwh)).1
  linarith

theorem diag_cap : Claims.diag_cap := by
  intro n k c lam cost S hn hc hk hlam hS hcost
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkpos : (0 : ℝ) < k := by rw [hk]; positivity
  have hinv : (1 / k : ℝ) = c / n := by rw [hk]; field_simp
  set u : Fin n → ℝ := fun i => if i ∈ S then (1 / k : ℝ) else 0 with hu
  have husum : ∑ i, u i = 1 := by
    simp only [hu]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, hS, nsmul_eq_mul]
    field_simp
  have hmem : u ∈ capSet n c := by
    refine ⟨⟨fun i => ?_, husum⟩, fun i => ?_⟩
    · simp only [hu]; split_ifs <;> positivity
    · simp only [hu]; split_ifs
      · rw [hinv]
      · positivity
  refine ⟨hmem, fun w hw => ?_⟩
  -- the KL part
  have hklu : klUnif n u = Real.log c := by
    unfold klUnif
    have : ∀ i, u i * Real.log (n * u i) = u i * Real.log c := by
      intro i
      simp only [hu]
      split_ifs
      · rw [hinv]; congr 2; field_simp
      · simp
    simp_rw [this]
    rw [← Finset.sum_mul, husum, one_mul]
  have hklw : klUnif n w ≤ Real.log c := by
    unfold klUnif
    have : ∀ i, w i * Real.log (n * w i) ≤ w i * Real.log c := by
      intro i
      rcases (hw.1.1 i).eq_or_lt with h | h
      · rw [← h]; simp
      · refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) h.le
        have := hw.2 i
        rw [le_div_iff₀ hnR] at this
        linarith
    calc ∑ i, w i * Real.log (n * w i) ≤ ∑ i, w i * Real.log c := Finset.sum_le_sum fun i _ => this i
      _ = Real.log c := by rw [← Finset.sum_mul, hw.1.2, one_mul]
  -- the linear part (threshold argument)
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos, hS]; exact_mod_cast hkpos
  obtain ⟨i0, hi0, hmax⟩ := S.exists_max_image cost hSne
  set τ := cost i0
  have hterm : ∀ i, 0 ≤ (cost i - τ) * (w i - u i) := by
    intro i
    by_cases hi : i ∈ S
    · have h1 : cost i - τ ≤ 0 := by linarith [hmax i hi]
      have h2 : w i - u i ≤ 0 := by
        simp only [hu, ite_eq_left hi]; rw [hinv]; linarith [hw.2 i]
      exact mul_nonneg_of_nonpos_of_nonpos h1 h2
    · have h1 : 0 ≤ cost i - τ := by linarith [hcost i0 hi0 i hi]
      have h2 : 0 ≤ w i - u i := by
        simp only [hu, ite_eq_right hi]; linarith [hw.1.1 i]
      exact mul_nonneg h1 h2
  have hexp : ∑ i, (cost i - τ) * (w i - u i) =
      (∑ i, cost i * w i) - (∑ i, cost i * u i) - τ * ((∑ i, w i) - ∑ i, u i) := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  have hlin : ∑ i, cost i * u i ≤ ∑ i, cost i * w i := by
    have := Finset.sum_nonneg fun i (_ : i ∈ univ) => hterm i
    rw [hexp, hw.1.2, husum, sub_self, mul_zero, sub_zero] at this
    linarith
  have hkl : lam * klUnif n w ≤ lam * klUnif n u := by
    rw [hklu]; exact mul_le_mul_of_nonneg_left hklw hlam
  show ∑ i, cost i * u i - lam * klUnif n u ≤ ∑ i, cost i * w i - lam * klUnif n w
  linarith

/-! ### `prop:diag-vertex` -/

/-- Derivative of one entropy term along a line. -/
lemma hasDerivAt_entropy_term (n : ℝ) (hn : 0 < n) (a b t : ℝ) (h : b = 0 ∨ 0 < a + t * b) :
    HasDerivAt (fun s => (a + s * b) * Real.log (n * (a + s * b)))
      (b * (Real.log (n * (a + t * b)) + 1)) t := by
  rcases h with h | h
  · subst h
    simp only [mul_zero, add_zero, zero_mul]
    exact hasDerivAt_const _ _
  · have hx : HasDerivAt (fun s => a + s * b) b t := by
      simpa using ((hasDerivAt_id t).mul_const b).const_add a
    have hlog := (hx.const_mul n).log (by positivity)
    convert hx.mul hlog using 1
    have hne := h.ne'
    have e : (a + t * b) * (b / (a + t * b)) = b := by field_simp
    rw [mul_div_mul_left _ _ hn.ne', e]
    ring

/-- Derivative of the first derivative of one entropy term. -/
lemma hasDerivAt_entropy_term' (n : ℝ) (hn : 0 < n) (a b t : ℝ) (h : b = 0 ∨ 0 < a + t * b) :
    HasDerivAt (fun s => b * (Real.log (n * (a + s * b)) + 1)) (b ^ 2 / (a + t * b)) t := by
  rcases h with h | h
  · subst h
    simp only [zero_mul]
    convert hasDerivAt_const t (0 : ℝ) using 1
    simp
  · have hx : HasDerivAt (fun s => a + s * b) b t := by
      simpa using ((hasDerivAt_id t).mul_const b).const_add a
    have hlog := (((hx.const_mul n).log (by positivity)).add_const 1).const_mul b
    convert hlog using 1
    have hne := h.ne'
    have hn' := hn.ne'
    field_simp

lemma inv_add_inv_ge_four {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y ≤ 1) :
    4 ≤ 1 / x + 1 / y := by
  rw [div_add_div _ _ hx.ne' hy.ne', le_div_iff₀ (mul_pos hx hy)]
  nlinarith [sq_nonneg (x - y)]

theorem diag_vertex : Claims.diag_vertex := by
  intro n F LF lam hF hHess hlam hlt w hw hmin
  by_contra hcon
  push Not at hcon
  -- a positive coordinate
  obtain ⟨i, hi⟩ : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    have : ∑ l, w l = 0 := Finset.sum_eq_zero fun l _ => le_antisymm (h l) (hw.1 l)
    rw [hw.2] at this; exact one_ne_zero this
  -- a second positive coordinate
  obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ 0 < w j := by
    by_contra h
    push Not at h
    apply hcon i
    have hz : ∀ l, l ≠ i → w l = 0 := fun l hl => le_antisymm (h l hl) (hw.1 l)
    have hwi : w i = 1 := by
      rw [← hw.2, Finset.sum_eq_single i (fun l _ hl => hz l hl) (by simp)]
    funext l
    by_cases hl : l = i
    · subst hl; simp [hwi]
    · simp [hz l hl, hl]
  have hij : i ≠ j := Ne.symm hji
  have hnR : (0 : ℝ) < n := by
    have : 0 < n := Fin.pos i
    exact_mod_cast this
  -- the direction `v = e_i − e_j`
  set v : Fin n → ℝ := Pi.single i 1 - Pi.single j 1 with hvdef
  have hvi : v i = 1 := by simp [hvdef, hij]
  have hvj : v j = -1 := by simp [hvdef, hji]
  have hvo : ∀ l, l ≠ i → l ≠ j → v l = 0 := by
    intro l hli hlj; simp [hvdef, hli, hlj]
  have hv0 : ∑ l, v l = 0 := by simp [hvdef, Finset.sum_sub_distrib]
  have hv2 : ∑ l, v l ^ 2 = 2 := by
    have : ∀ l, v l ^ 2 = (Pi.single i (1 : ℝ) : Fin n → ℝ) l + (Pi.single j (1 : ℝ) : Fin n → ℝ) l := by
      intro l
      by_cases hli : l = i
      · subst hli; simp [hvi, hij]
      by_cases hlj : l = j
      · subst hlj; simp [hvj, hji]
      simp [hvo l hli hlj, hli, hlj]
    simp_rw [this]
    rw [Finset.sum_add_distrib]
    simp; norm_num
  set δ := min (w i) (w j) with hδ
  have hδpos : 0 < δ := lt_min hi hj
  set D : Set ℝ := Set.Ioo (-δ) δ with hD
  -- along the segment the coordinates are positive or unchanged
  have hcoord : ∀ t ∈ D, ∀ l, v l = 0 ∨ 0 < w l + t * v l := by
    intro t ht l
    by_cases hli : l = i
    · subst hli; right; rw [hvi]
      have := ht.1; have := min_le_left (w l) (w j); linarith
    by_cases hlj : l = j
    · subst hlj; right; rw [hvj]
      have := ht.2; have := min_le_right (w i) (w l); linarith
    left; exact hvo l hli hlj
  have hseg : ∀ t ∈ D, w + t • v ∈ simplex n := by
    intro t ht
    refine ⟨fun l => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases hcoord t ht l with h | h
      · rw [h, mul_zero, add_zero]; exact hw.1 l
      · exact h.le
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hw.2, hv0, mul_zero, add_zero]
  -- the objective along the segment
  set f : ℝ → ℝ := fun t => F (w + t • v) with hfdef
  set ψ : ℝ → ℝ := fun t => ∑ l, (w l + t * v l) * Real.log (n * (w l + t * v l)) with hψdef
  set ψ1 : ℝ → ℝ := fun t => ∑ l, v l * (Real.log (n * (w l + t * v l)) + 1) with hψ1def
  set ψ2 : ℝ → ℝ := fun t => ∑ l, v l ^ 2 / (w l + t * v l) with hψ2def
  have hklψ : ∀ t, klUnif n (w + t • v) = ψ t := by
    intro t; simp [klUnif, hψdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  set G : ℝ → ℝ := fun t => f t - lam * ψ t with hGdef
  have hψd : ∀ t ∈ D, HasDerivAt ψ (ψ1 t) t := by
    intro t ht
    have := HasDerivAt.fun_sum (u := univ) (fun l _ =>
      hasDerivAt_entropy_term n hnR (w l) (v l) t (hcoord t ht l))
    simpa [hψdef, hψ1def] using this
  have hψ1d : ∀ t ∈ D, HasDerivAt ψ1 (ψ2 t) t := by
    intro t ht
    have := HasDerivAt.fun_sum (u := univ) (fun l _ =>
      hasDerivAt_entropy_term' n hnR (w l) (v l) t (hcoord t ht l))
    simpa [hψ1def, hψ2def] using this
  -- `f` is `C²`
  have hfC : ContDiff ℝ 2 f :=
    hF.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hf1 : Differentiable ℝ f := hfC.differentiable (by norm_num)
  have hf2 : Differentiable ℝ (deriv f) := by
    have h := (contDiff_succ_iff_deriv (n := 1)).mp (hfC.of_le (by norm_num))
    exact h.2.2.differentiable (by norm_num)
  -- the Hessian bound along the segment
  have hfpp : ∀ s ∈ D, deriv (deriv f) s ≤ LF * 2 := by
    intro s hs
    have h := hHess (w + s • v) (hseg s hs) v hv0
    rw [hv2] at h
    have h1 : (fun t : ℝ => F (w + s • v + t • v)) = fun t => f (t + s) := by
      funext t; simp only [hfdef]; congr 1; rw [add_smul]; abel
    have h2 : deriv (fun t => f (t + s)) = fun t => deriv f (t + s) := by
      funext t; exact deriv_comp_add_const ..
    rw [h1, h2, deriv_comp_add_const, zero_add] at h
    exact h
  -- the entropy curvature along the segment
  have hpair : w i + w j ≤ 1 := by
    rw [← hw.2, ← Finset.sum_pair hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun l _ _ => hw.1 l)
  have hψ2 : ∀ t ∈ D, 4 ≤ ψ2 t := by
    intro t ht
    have hti : 0 < w i + t * v i := by
      rcases hcoord t ht i with h | h
      · rw [hvi] at h; norm_num at h
      · exact h
    have htj : 0 < w j + t * v j := by
      rcases hcoord t ht j with h | h
      · rw [hvj] at h; norm_num at h
      · exact h
    have hnn : ∀ l ∈ (univ : Finset (Fin n)), l ∉ ({i, j} : Finset (Fin n)) →
        0 ≤ v l ^ 2 / (w l + t * v l) := by
      intro l _ _
      rcases hcoord t ht l with h | h
      · rw [h]; simp
      · positivity
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {i, j}) hnn
    rw [Finset.sum_pair hij] at hsub
    rw [hvi] at hti
    rw [hvj] at htj
    rw [hvi, hvj] at hsub
    have h4 := inv_add_inv_ge_four hti htj (by linarith)
    simp only [hψ2def]
    norm_num at hsub h4 ⊢
    linarith
  -- strict concavity of `G` on `D`
  have hDopen : IsOpen D := isOpen_Ioo
  have hGd : ∀ t ∈ D, HasDerivAt G (deriv f t - lam * ψ1 t) t := by
    intro t ht
    exact (hf1 t).hasDerivAt.sub ((hψd t ht).const_mul lam)
  have hGpp : ∀ t ∈ D, deriv^[2] G t < 0 := by
    intro t ht
    have hev : deriv G =ᶠ[nhds t] fun s => deriv f s - lam * ψ1 s := by
      filter_upwards [hDopen.mem_nhds ht] with s hs
      exact (hGd s hs).deriv
    have hd2 : HasDerivAt (fun s => deriv f s - lam * ψ1 s)
        (deriv (deriv f) t - lam * ψ2 t) t :=
      (hf2 t).hasDerivAt.sub ((hψ1d t ht).const_mul lam)
    show deriv (deriv G) t < 0
    rw [hev.deriv_eq, hd2.deriv]
    have := hfpp t ht
    have := hψ2 t ht
    nlinarith
  have hGc : ContinuousOn G D := fun t ht => (hGd t ht).continuousAt.continuousWithinAt
  have hconc : StrictConcaveOn ℝ D G :=
    strictConcaveOn_of_deriv2_neg (convex_Ioo _ _) hGc
      (fun t ht => hGpp t (interior_subset ht))
  have hp : δ / 2 ∈ D := ⟨by linarith, by linarith⟩
  have hm : -(δ / 2) ∈ D := ⟨by linarith, by linarith⟩
  have hlt' := hconc.2 hp hm (by linarith) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hzero : (1 / 2 : ℝ) • (δ / 2) + (1 / 2 : ℝ) • -(δ / 2) = 0 := by
    simp only [smul_eq_mul]; ring
  rw [hzero] at hlt'
  simp only [smul_eq_mul] at hlt'
  -- minimality
  have hG0 : G 0 = F w - lam * klUnif n w := by
    simp only [hGdef, hfdef, ← hklψ, zero_smul, add_zero]
  have hGt : ∀ t ∈ D, G 0 ≤ G t := by
    intro t ht
    rw [hG0]
    have := hmin _ (hseg t ht)
    simp only [hGdef, hfdef, ← hklψ]
    exact this
  have := hGt _ hp
  have := hGt _ hm
  linarith

theorem diag_vertex_linear : Claims.diag_vertex_linear := by
  intro n cost lam hlam w hw hmin
  refine diag_vertex n (fun x => ∑ i, cost i * x i) 0 lam ?_ ?_ hlam.le (by simpa using hlam) w hw
    hmin
  · exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_apply ℝ ℝ i)
  · intro w' _ v _
    have : (fun t : ℝ => ∑ i, cost i * (w' + t • v) i) =
        fun t => (∑ i, cost i * w' i) + t * ∑ i, cost i * v i := by
      funext t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    have h1 : deriv (fun t : ℝ => (∑ i, cost i * w' i) + t * ∑ i, cost i * v i) =
        fun _ => ∑ i, cost i * v i := by
      funext t
      simp
    rw [h1]
    simp

end StatFormal.ICL.Diag

namespace StatFormal.ICL.Diag
example : Claims.oracle := oracle
example : Claims.diag_vertex := diag_vertex
example : Claims.diag_vertex_linear := diag_vertex_linear
example : Claims.diag_cap := diag_cap
end StatFormal.ICL.Diag
