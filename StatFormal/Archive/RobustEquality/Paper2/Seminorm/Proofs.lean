import StatFormal.Archive.RobustEquality.Paper2.Seminorm.Statements
import StatFormal.Archive.RobustEquality.Paper2.RouteSeminormTwo
import StatFormal.Archive.RobustEquality.Paper2.RouteSeminormEx
import StatFormal.Archive.RobustEquality.Paper2.RouteNPMLE

/-!
# Proofs: paper 2 `thm:seminorm` (i)–(iii), (iv)(a),(c) and `thm:npmle` (finite `L`)

The frozen definitions are verbatim copies of the route definitions (namespace `…Paper2.Route`),
so the route theorems apply up to definitional unfolding; the bridges below handle the new
definitions (`FinSetting`, `T0`, `nuMix`).
-/

noncomputable section
open Finset Real ContinuousLinearMap

namespace StatFormal.RobustEquality.Paper2.Seminorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hyp_of {n q : ℕ} {ε : ℝ} {a : Fin n → ℝ} {m : Fin q → ℝ} (h : FinSetting ε a m) :
    Route.Hyp ε a m := by
  obtain ⟨hε, ha, hs, hq, hm, hmass⟩ := h
  exact ⟨hε, ha, hs, hq, hm, hmass⟩

/-! ### `thm:seminorm` -/

theorem seminorm_T : Claims.seminorm_T := by
  intro E _ _ n q ε r a x m y h
  have H := hyp_of h
  exact ⟨Route.Tfin_convex H.hε H.ha x H.hq H.hm y,
    fun w l _ => Route.Tfin_neg ε r a x m y w l,
    fun w l t _ ht => Route.Tfin_homog ε r a x m y w l ht⟩

theorem seminorm_N : Claims.seminorm_N := by
  intro E _ _ n q ε r a x m y h hF
  have H := hyp_of h
  have hF' : Route.Feasible ε r a x m y := hF
  refine ⟨fun w l hl => Route.Tfin_nonneg H hF' w hl, fun w => ?_,
    fun w => Route.Nsq_nonneg H hF' w, Route.seminormN H hF', fun w => rfl,
    Route.seminormN_le H hF'⟩
  have hset : {v | ∃ l : ℝ, 0 < l ∧ v = Tfin ε r a x m y w l} =
      Set.range fun l : Set.Ioi (0 : ℝ) => Tfin ε r a x m y w l := by
    ext v
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨⟨l, hl⟩, rfl⟩
    · rintro ⟨l, rfl⟩; exact ⟨l, l.2, rfl⟩
  rw [hset]
  exact isGLB_ciInf (Route.bdd_T H hF' w)

theorem seminorm_G : Claims.seminorm_G := by
  intro E _ _ n₀ n₁ q₀ q₁ ε r₀ r₁ a₀ x₀ m₀ y₀ a₁ x₁ m₁ y₁ h₀ h₁ hF₀ hF₁
  exact ⟨fun w => Route.inf_Fbar2 (hyp_of h₀) (hyp_of h₁) hF₀ hF₁ w,
    fun w t ht => Route.G_homog2 (hyp_of h₀) (hyp_of h₁) hF₀ hF₁ w ht⟩

/-- A probability average of a constant `0` or `⊤` in `EReal` is that constant. -/
lemma sum_mul_zero_or_top {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1)
    {S : EReal} (hS : S = 0 ∨ S = ⊤) : ∑ i, ((a i : ℝ) : EReal) * S = S := by
  rcases hS with rfl | rfl
  · simp
  · obtain ⟨i0, -, hi0⟩ : ∃ i ∈ (univ : Finset (Fin n)), (0 : ℝ) < a i := by
      have : ∑ _i : Fin n, (0 : ℝ) < ∑ i, a i := by simp [hs]
      exact Finset.exists_lt_of_sum_lt this
    have hnn : ∀ i, 0 ≤ ((a i : ℝ) : EReal) * ⊤ := fun i => by
      rcases eq_or_lt_of_le (ha i) with h | h
      · rw [← h]; simp
      · rw [EReal.coe_mul_top_of_pos h]; exact le_top
    refine top_le_iff.mp ?_
    calc (⊤ : EReal) = ((a i0 : ℝ) : EReal) * ⊤ := (EReal.coe_mul_top_of_pos hi0).symm
      _ ≤ ∑ i, ((a i : ℝ) : EReal) * ⊤ :=
        Finset.single_le_sum (f := fun i => ((a i : ℝ) : EReal) * ⊤) (fun i _ => hnn i)
          (mem_univ i0)

lemma T0_eq [CompleteSpace E] {n : ℕ} (A : E ≃L[ℝ] E) (β : ℝ) {a : Fin n → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1) (x : Fin n → E) (w : E) {l : ℝ} (hl : 0 < l) :
    T0 A β a x w l = Route.T0full A β w l := by
  unfold T0 Route.T0full
  congr 1
  rw [Finset.sum_congr rfl fun i _ => by rw [Route.anchor_sup_eq A w l (x i)]]
  refine sum_mul_zero_or_top ha hs ?_
  rw [Route.sup_quad A w hl]
  split_ifs <;> simp

theorem seminorm_wass : Claims.seminorm_wass := by
  intro E _ _ _ n β a x hβ ha hs
  have key : ∀ (A : E ≃L[ℝ] E) (w : E), (⨅ l : Set.Ioi (0 : ℝ), T0 A β a x w l) =
      ((β * ‖(adjoint (A.symm : E →L[ℝ] E)) w‖ ^ 2 : ℝ) : EReal) := by
    intro A w
    rw [← Route.inf_T0 A hβ w]
    exact iInf_congr fun l => T0_eq A β ha hs x w l.2
  refine ⟨key, fun w => ?_⟩
  rw [key]
  have : (adjoint (((ContinuousLinearEquiv.refl ℝ E).symm : E ≃L[ℝ] E) : E →L[ℝ] E)) w = w := by
    simp [ContinuousLinearMap.adjoint_id]
  rw [this]

/-! ### `thm:npmle` -/

theorem npmle_duality : Claims.npmle_duality := by
  intro n p ψ hn hp hψ
  refine ⟨?_, fun ms hms hmax => ?_⟩
  · obtain ⟨ms, hms, h1, h2, -, -⟩ := Route.npmle_duality hn hp hψ
    exact ⟨ms, hms, h1, h2⟩
  · have hA : ∀ i, 0 < ∑ y, ms y * ψ i y := Route.A_pos hψ hms
    refine ⟨⟨fun i => by have := hA i; positivity, fun y => ?_⟩, ?_⟩
    · have := Route.foc_npmle hn hψ hms hmax y
      refine le_trans (le_of_eq ?_) this
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    · simp only [Dval, Lval, one_div, Real.log_inv, Finset.sum_neg_distrib, mul_neg, neg_neg]

theorem npmle_convex : Claims.npmle_convex := by
  intro E _ _ n s ε x κ ξ _ hε hκ
  exact Route.Phi_convex hε x hκ ξ

/-- `ψ_i(y) = Σ_k κ_{yk} e^{gexp(w, λ, ξ_k − x_i)/(λε)}` for a finite kernel. -/
def psiK {n p s : ℕ} (ε : ℝ) (x : Fin n → E) (κ : Fin p → Fin s → ℝ) (ξ : Fin s → E) (w : E)
    (l : ℝ) : Fin n → Fin p → ℝ :=
  fun i y => ∑ k, κ y k * Real.exp (gexp w l (ξ k - x i) / (l * ε))

lemma psiK_pos {n p s : ℕ} (ε : ℝ) (x : Fin n → E) {κ : Fin p → Fin s → ℝ} (ξ : Fin s → E)
    (w : E) (l : ℝ) (hκ : ∀ y k, 0 ≤ κ y k) (hκ1 : ∀ y, 0 < ∑ k, κ y k) :
    ∀ i y, 0 < psiK ε x κ ξ w l i y := by
  intro i y
  obtain ⟨k0, -, hk0⟩ : ∃ k ∈ (univ : Finset (Fin s)), (0 : ℝ) < κ y k := by
    have : ∑ _k : Fin s, (0 : ℝ) < ∑ k, κ y k := by simpa using hκ1 y
    exact Finset.exists_lt_of_sum_lt this
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hκ y k) (Real.exp_pos _).le)
    ⟨k0, mem_univ _, mul_pos hk0 (Real.exp_pos _)⟩

lemma Phi_eq {n p s : ℕ} (ε : ℝ) (x : Fin n → E) (κ : Fin p → Fin s → ℝ) (ξ : Fin s → E)
    (z : Fin n → ℝ) (w : E) (l : ℝ) (y : Fin p) :
    Phi ε x (κ y) ξ z w l =
      l * ((1 / (n : ℝ)) * ∑ i, Real.exp (z i / (l * ε)) * psiK ε x κ ξ w l i y - 1) := by
  simp only [Phi, psiK]
  have e : ∀ i k, κ y k * Real.exp ((z i + gexp w l (ξ k - x i)) / (l * ε)) =
      Real.exp (z i / (l * ε)) * (κ y k * Real.exp (gexp w l (ξ k - x i) / (l * ε))) := by
    intro i k
    rw [add_div, Real.exp_add]
    ring
  simp_rw [e, ← Finset.mul_sum]
  ring

lemma Tfin_mix {n p s : ℕ} (ε r : ℝ) (x : Fin n → E) (κ : Fin p → Fin s → ℝ) (ξ : Fin s → E)
    (w : E) (l : ℝ) (m : Fin p → ℝ) :
    Tfin ε r (fun _ => 1 / (n : ℝ)) x (nuMix κ m) ξ w l =
      l * r + l * ε * Lval (psiK ε x κ ξ w l) m := by
  simp only [Tfin, lse, nuMix, Lval, psiK]
  have e : ∀ i, ∑ k, (∑ y, m y * κ y k) * Real.exp (gexp w l (ξ k - x i) / (l * ε)) =
      ∑ y, m y * ∑ k, κ y k * Real.exp (gexp w l (ξ k - x i) / (l * ε)) := by
    intro i
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl fun i _ => by rw [e i]]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem npmle_correction : Claims.npmle_correction := by
  intro E _ _ n p s ε r l V x κ ξ z w hn hp hε hl hκ hκ1 hV
  have hψ := psiK_pos ε x ξ w l hκ hκ1
  have hτ : 0 < l * ε := mul_pos hl hε
  have hV' : ∀ y, (1 / (n : ℝ)) * ∑ i, Real.exp (z i / (l * ε)) * psiK ε x κ ξ w l i y ≤ V := by
    intro y
    have h := hV y
    rw [Phi_eq] at h
    have e : ∀ X : ℝ, l * (X - 1) / l + 1 = X := fun X => by field_simp; ring
    rwa [e] at h
  refine ⟨fun y => ?_, fun m hm => ?_⟩
  · set M := max 1 V
    have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
    rw [Phi_eq]
    have hexp : ∀ i, Real.exp ((z i - l * ε * Real.log M) / (l * ε)) =
        Real.exp (z i / (l * ε)) / M := fun i => by
      rw [sub_div, mul_div_cancel_left₀ _ hτ.ne', Real.exp_sub, Real.exp_log hM]
    simp_rw [hexp]
    have hS : (1 / (n : ℝ)) * ∑ i, Real.exp (z i / (l * ε)) / M * psiK ε x κ ξ w l i y =
        ((1 / (n : ℝ)) * ∑ i, Real.exp (z i / (l * ε)) * psiK ε x κ ξ w l i y) / M := by
      rw [mul_div_assoc, Finset.sum_div]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hS]
    have h1 : ((1 / (n : ℝ)) * ∑ i, Real.exp (z i / (l * ε)) * psiK ε x κ ξ w l i y) / M ≤ 1 := by
      rw [div_le_one hM]
      exact (hV' y).trans (le_max_right _ _)
    exact mul_nonpos_of_nonneg_of_nonpos hl.le (by linarith)
  · rw [Tfin_mix]
    exact Route.correction hn hψ hε hl z hV' hm

/-- `thm:npmle` programme, for one multiplier `λ > 0`. -/
lemma programme_l {n p s : ℕ} (ε r : ℝ) (x : Fin n → E) (κ : Fin p → Fin s → ℝ) (ξ : Fin s → E)
    (w : E) (hn : 0 < n) (hp : 0 < p) (hε : 0 < ε) (hκ : ∀ y k, 0 ≤ κ y k)
    (hκ1 : ∀ y, 0 < ∑ k, κ y k) {l : ℝ} (hl : 0 < l) :
    (∃ t, IsGreatest
      {v | ∃ m ∈ simplex p, v = Tfin ε r (fun _ => 1 / (n : ℝ)) x (nuMix κ m) ξ w l} t) ∧
    ∀ t, IsGreatest
      {v | ∃ m ∈ simplex p, v = Tfin ε r (fun _ => 1 / (n : ℝ)) x (nuMix κ m) ξ w l} t →
      IsLeast {v | ∃ z : Fin n → ℝ, (∀ y, Phi ε x (κ y) ξ z w l ≤ 0) ∧
        v = l * r - (1 / (n : ℝ)) * ∑ i, z i} t := by
  have hψ := psiK_pos ε x ξ w l hκ hκ1
  have hτ : 0 < l * ε := mul_pos hl hε
  set ψ := psiK ε x κ ξ w l with hψdef
  refine ⟨?_, ?_⟩
  · obtain ⟨ms, hms, hmax⟩ := Route.exists_max_Lval hp hψ
    refine ⟨_, ⟨ms, hms, rfl⟩, ?_⟩
    rintro v ⟨m, hm, rfl⟩
    rw [Tfin_mix, Tfin_mix]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hmax m hm) hτ.le)
  · rintro t ⟨⟨m0, hm0, rfl⟩, hub⟩
    have hmax : ∀ m ∈ simplex p, Lval ψ m ≤ Lval ψ m0 := by
      intro m hm
      have h := hub ⟨m, hm, rfl⟩
      rw [Tfin_mix, Tfin_mix] at h
      exact le_of_mul_le_mul_left (by linarith) hτ
    have hA : ∀ i, 0 < ∑ y, m0 y * ψ i y := Route.A_pos hψ hm0
    rw [Tfin_mix]
    refine ⟨⟨fun i => -(l * ε) * Real.log (∑ y, m0 y * ψ i y), fun y => ?_, ?_⟩, ?_⟩
    · rw [Phi_eq]
      have hexp : ∀ i, Real.exp (-(l * ε) * Real.log (∑ y, m0 y * ψ i y) / (l * ε)) =
          (∑ y, m0 y * ψ i y)⁻¹ := fun i => by
        rw [neg_mul, neg_div, mul_div_cancel_left₀ _ hτ.ne', Real.exp_neg, Real.exp_log (hA i)]
      simp_rw [hexp]
      have hf := Route.foc_npmle hn hψ hm0 hmax y
      have e : ∑ i, (∑ y, m0 y * ψ i y)⁻¹ * ψ i y = ∑ i, ψ i y / ∑ y', m0 y' * ψ i y' :=
        Finset.sum_congr rfl fun i _ => by rw [inv_mul_eq_div]
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos hl.le (by linarith)
    · simp only [Lval]
      rw [← Finset.mul_sum]
      ring
    · rintro v ⟨z, hz, rfl⟩
      set u : Fin n → ℝ := fun i => Real.exp (z i / (l * ε))
      have hu : Route.DualFeas ψ u := by
        refine ⟨fun i => Real.exp_pos _, fun y => ?_⟩
        have h := hz y
        rw [Phi_eq] at h
        have : (1 / (n : ℝ)) * ∑ i, u i * ψ i y - 1 ≤ 0 := by
          by_contra hc
          push Not at hc
          have := mul_pos hl hc
          linarith
        linarith
      have hw := Route.weak_duality hn hψ hm0 hu
      have hD : l * ε * Route.Dval u = -((1 / (n : ℝ)) * ∑ i, z i) := by
        simp only [Route.Dval, u, Real.log_exp]
        rw [← Finset.sum_div]
        field_simp
      have := mul_le_mul_of_nonneg_left hw hτ.le
      change l * r + l * ε * Route.Lval ψ m0 ≤ l * r - (1 / (n : ℝ)) * ∑ i, z i
      linarith

theorem npmle_programme : Claims.npmle_programme := by
  intro E _ _ n p s ε r x κ ξ w hn hp hε hκ hκ1
  have per := fun (l : ℝ) (hl : 0 < l) => programme_l ε r x κ ξ w hn hp hε hκ hκ1 hl
  refine ⟨per, fun N2 => ?_⟩
  have hlb : lowerBounds {t | ∃ l : ℝ, 0 < l ∧ IsGreatest
      {v | ∃ m ∈ simplex p, v = Tfin ε r (fun _ => 1 / (n : ℝ)) x (nuMix κ m) ξ w l} t} =
      lowerBounds {v | ∃ (l : ℝ) (z : Fin n → ℝ), 0 < l ∧ (∀ y, Phi ε x (κ y) ξ z w l ≤ 0) ∧
        v = l * r - (1 / (n : ℝ)) * ∑ i, z i} := by
    ext b
    constructor
    · rintro hb v ⟨l, z, hl, hz, rfl⟩
      obtain ⟨t, ht⟩ := (per l hl).1
      exact (hb ⟨l, hl, ht⟩).trans (((per l hl).2 t ht).2 ⟨z, hz, rfl⟩)
    · rintro hb t ⟨l, hl, ht⟩
      obtain ⟨z, hz, hzt⟩ := ((per l hl).2 t ht).1
      exact hb ⟨l, z, hl, hz, hzt⟩
  unfold IsGLB
  rw [hlb]

/-! ### Gate checks -/

example : Claims.seminorm_T := seminorm_T
example : Claims.seminorm_N := seminorm_N
example : Claims.seminorm_G := seminorm_G
example : Claims.seminorm_wass := seminorm_wass
example : Claims.npmle_duality := npmle_duality
example : Claims.npmle_convex := npmle_convex
example : Claims.npmle_correction := npmle_correction
example : Claims.npmle_programme := npmle_programme

end StatFormal.RobustEquality.Paper2.Seminorm
