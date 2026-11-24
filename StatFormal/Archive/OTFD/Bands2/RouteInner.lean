import StatFormal.Archive.OTFD.Bands2.Statements
import StatFormal.Archive.OTFD.Bands.Proofs

/-!
# Route: `prop:band-inner-certificate` and `cor:ext-solver-certified`
-/

noncomputable section
open Finset

namespace StatFormal.OTFD.Bands2

open StatFormal.OTFD.Bands

variable {n K : ℕ}

lemma hsup_mono (Q : (Fin K → ℝ) → Fin K → ℝ) {F A : Set (Fin K → ℝ)} (h : F ⊆ A)
    (v : Fin K → ℝ) : hsup Q F v ≤ hsup Q A v :=
  biSup_mono fun _ hu => h hu

lemma le_hsup (Q : (Fin K → ℝ) → Fin K → ℝ) {A : Set (Fin K → ℝ)} {u : Fin K → ℝ} (hu : u ∈ A)
    (v : Fin K → ℝ) : ((v ⬝ᵥ Q u : ℝ) : EReal) ≤ hsup Q A v :=
  le_biSup (fun u => ((v ⬝ᵥ Q u : ℝ) : EReal)) hu

/-- Perturbation of a supremum: if `ψ ≤ φ + T` pointwise on `S ⊆ S'`, then
`sup_S ψ ≤ sup_{S'} φ + T`. -/
lemma hsup_le_add (Q Q' : (Fin K → ℝ) → Fin K → ℝ) {S S' : Set (Fin K → ℝ)} (hS : S ⊆ S')
    (v : Fin K → ℝ) (T : ℝ) (h : ∀ u, v ⬝ᵥ Q' u ≤ v ⬝ᵥ Q u + T) :
    hsup Q' S v ≤ hsup Q S' v + (T : EReal) := by
  unfold hsup
  refine iSup₂_le fun u hu => ?_
  calc ((v ⬝ᵥ Q' u : ℝ) : EReal) ≤ ((v ⬝ᵥ Q u + T : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (h u)
    _ = ((v ⬝ᵥ Q u : ℝ) : EReal) + (T : EReal) := EReal.coe_add _ _
    _ ≤ (⨆ u ∈ S', ((v ⬝ᵥ Q u : ℝ) : EReal)) + (T : EReal) := by
        gcongr
        exact le_biSup (fun u => ((v ⬝ᵥ Q u : ℝ) : EReal)) (hS hu)

lemma up_aux (mo ub T : ℝ) (X Y Z : EReal) (hYX : Y ≤ X + T) (hZY : Z ≤ Y + T)
    (hub : (mo : EReal) + X ≤ ub) :
    (mo : EReal) + Z - T ≤ (mo : EReal) + Y ∧ (mo : EReal) + Y ≤ (ub : EReal) + T := by
  induction X using EReal.rec <;> induction Y using EReal.rec <;> induction Z using EReal.rec <;>
    try simp_all
  all_goals (try norm_cast at *)
  all_goals (try constructor) <;> linarith

lemma lo_aux (mo lb T : ℝ) (X Y Z : EReal) (hYX : Y ≤ X + T) (hZY : Z ≤ Y + T)
    (hlb : (lb : EReal) ≤ (mo : EReal) - X) :
    (lb : EReal) - T ≤ (mo : EReal) - Y ∧ (mo : EReal) - Y ≤ (mo : EReal) - Z + T := by
  induction X using EReal.rec <;> induction Y using EReal.rec <;> induction Z using EReal.rec <;>
    try simp_all
  all_goals (try norm_cast at *)
  all_goals (try constructor) <;> linarith

lemma tanh_mono {x y : ℝ} (h : x ≤ y) : Real.tanh x ≤ Real.tanh y := by
  rw [tanh_formula, tanh_formula]
  have hA := Real.exp_pos (2 * x)
  have hB := Real.exp_pos (2 * y)
  have hAB : Real.exp (2 * x) ≤ Real.exp (2 * y) := Real.exp_le_exp.mpr (by linarith)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma range_nonneg [Nonempty (Fin n)] (Z : Fin n → Fin K → ℝ) (v : Fin K → ℝ) :
    0 ≤ (⨆ j, v ⬝ᵥ Z j) - ⨅ j, v ⬝ᵥ Z j := by
  obtain ⟨j⟩ := ‹Nonempty (Fin n)›
  linarith [le_ciSup (Set.finite_range (fun j => v ⬝ᵥ Z j)).bddAbove j,
    ciInf_le (Set.finite_range (fun j => v ⬝ᵥ Z j)).bddBelow j]

/-- Pointwise solver bound with the user's `Δ ≥ osc(f − f')`. -/
lemma solver_pt (ε Δ : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ)
    (f f' : Fin n → ℝ) (u v : Fin K → ℝ) (hn : 0 < n) (hε : 0 < ε) (hM : M.PosDef)
    (hΔ : osc (f - f') ≤ Δ) :
    |v ⬝ᵥ (Qent ε M Z f u - Qent ε M Z f' u)| ≤ solverT ε Δ Z v := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine (Claims.ext_solver_error_proof n K ε M Z f f' u v hn hε hM).trans ?_
  unfold solverT
  apply mul_le_mul_of_nonneg_right _ (range_nonneg Z v)
  apply tanh_mono
  apply div_le_div_of_nonneg_right _ (by linarith)
  simpa [osc] using hΔ

namespace Claims

theorem inner_le_exact_proof : inner_le_exact := by
  intro K Q A F mo v hFA
  refine ⟨?_, ?_⟩
  · unfold edgeUp; gcongr; exact hsup_mono Q hFA v
  · unfold edgeLo; exact EReal.sub_le_sub le_rfl (hsup_mono Q hFA _)

lemma gap_aux (mo ub lb r r' : ℝ) (I H I' H' : EReal) (hIH : I ≤ H) (hIH' : I' ≤ H')
    (hr : (r : EReal) ≤ I) (hr' : (r' : EReal) ≤ I') (hub : (mo : EReal) + H ≤ ub)
    (hlb : (lb : EReal) ≤ (mo : EReal) - H') :
    0 ≤ ((ub : EReal) - ((mo : EReal) + I)) + (((mo : EReal) - I') - lb) ∧
    ((ub : EReal) - ((mo : EReal) + I)) + (((mo : EReal) - I') - lb) ≠ ⊤ ∧
    (((ub : EReal) - ((mo : EReal) + I)) + (((mo : EReal) - I') - lb) = 0 →
      (mo : EReal) + I = (mo : EReal) + H ∧ (mo : EReal) + H = ub ∧
      (mo : EReal) - I' = (mo : EReal) - H' ∧ (mo : EReal) - H' = lb) := by
  induction I using EReal.rec <;> induction H using EReal.rec <;>
    induction I' using EReal.rec <;> induction H' using EReal.rec <;> try simp_all
  rename_i i h i' h'
  norm_cast at *
  refine ⟨by linarith, EReal.coe_ne_top _, fun hgap => ⟨by linarith, by linarith, by linarith,
    by linarith⟩⟩

theorem inner_gap_proof : inner_gap := by
  intro K Q A F mo v ub lb hFA hF hub hlb
  obtain ⟨u0, hu0⟩ := hF
  exact gap_aux mo ub lb _ _ _ _ _ _ (hsup_mono Q hFA v) (hsup_mono Q hFA (-v))
    (le_hsup Q hu0 v) (le_hsup Q hu0 (-v)) hub hlb

theorem solver_sandwich_up_proof : solver_sandwich_up := by
  intro n K ε Δ mo ub M Z f fstar A F v hn hε hM hFA hΔ hub
  have hpt := fun u => solver_pt ε Δ M Z f fstar u v hn hε hM hΔ
  have h1 : hsup (Qent ε M Z fstar) A v ≤ hsup (Qent ε M Z f) A v + (solverT ε Δ Z v : EReal) :=
    hsup_le_add _ _ subset_rfl v _ fun u => by
      have := (abs_le.mp (hpt u)).1; rw [dotProduct_sub] at this; linarith
  have h2 : hsup (Qent ε M Z f) F v ≤ hsup (Qent ε M Z fstar) A v + (solverT ε Δ Z v : EReal) :=
    hsup_le_add _ _ hFA v _ fun u => by
      have := (abs_le.mp (hpt u)).2; rw [dotProduct_sub] at this; linarith
  exact up_aux mo ub _ _ _ _ h1 h2 hub

theorem solver_sandwich_lo_proof : solver_sandwich_lo := by
  intro n K ε Δ mo lb M Z f fstar A F v hn hε hM hFA hΔ hlb
  have hpt : ∀ u, |(-v) ⬝ᵥ (Qent ε M Z f u - Qent ε M Z fstar u)| ≤ solverT ε Δ Z v := fun u => by
    rw [neg_dotProduct, abs_neg]; exact solver_pt ε Δ M Z f fstar u v hn hε hM hΔ
  have h1 : hsup (Qent ε M Z fstar) A (-v) ≤
      hsup (Qent ε M Z f) A (-v) + (solverT ε Δ Z v : EReal) :=
    hsup_le_add _ _ subset_rfl (-v) _ fun u => by
      have := (abs_le.mp (hpt u)).1; rw [dotProduct_sub] at this; linarith
  have h2 : hsup (Qent ε M Z f) F (-v) ≤
      hsup (Qent ε M Z fstar) A (-v) + (solverT ε Δ Z v : EReal) :=
    hsup_le_add _ _ hFA (-v) _ fun u => by
      have := (abs_le.mp (hpt u)).2; rw [dotProduct_sub] at this; linarith
  exact lo_aux mo lb _ _ _ _ h1 h2 hlb

end Claims

theorem inner_le_exact : Claims.inner_le_exact := Claims.inner_le_exact_proof
theorem inner_gap : Claims.inner_gap := Claims.inner_gap_proof
theorem solver_sandwich_up : Claims.solver_sandwich_up := Claims.solver_sandwich_up_proof
theorem solver_sandwich_lo : Claims.solver_sandwich_lo := Claims.solver_sandwich_lo_proof

end StatFormal.OTFD.Bands2
