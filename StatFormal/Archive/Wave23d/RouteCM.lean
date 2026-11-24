import StatFormal.Archive.Wave23d.Statements
import StatFormal.Archive.OTFD.WaveL3.RouteCycMon
import StatFormal.Lib.Potentials.HilbertUniqueness

/-!
# Route — A `lem:app-cm-plans` (i), (ii), (iv) first sentence (untrusted)

* (i) The cyclic sum is continuous in the `m` points and `closure (pi Γ) = pi (closure Γ)`; the transpose is the
  certified wave-L3 `cycMon_swap`; the support lies in the closure of any conull set.
* (ii) Rockafellar's chain functional `f(x) = sup_w [⟨y_n, x − x_n⟩ + Σ_{i<n} ⟨y_i, x_{i+1} − x_i⟩]` over chains
  `w 0 = p₀, …, w n` in `Γ`: a supremum of `M`-Lipschitz affine functions, bounded by `M‖x − x₀‖` (the closed chain is a
  cycle), and appending `(x, y) ∈ Γ` gives `y ∈ ∂f(x)`.
* (iv) Two-cycles make `Γ` monotone; the library (`measure_multivaluedSet_eq_zero`, `exists_eq_graphPlan_of_ae_mem`)
  gives the graph plan. No moment is used.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology Finset TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave23d

open StatFormal.OTFD.WaveL1 (CycMon CMConc Graph LipNull)

section CM
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cm_closure_thm : Claims.cm_closure := by
  intro E _ _ Γ hΓ m z hz
  set F : (Fin m → E × E) → ℝ := fun z => ∑ i, ⟪(z i).2, (z (finRotate m i)).1 - (z i).1⟫
  have hF : Continuous F := by
    refine continuous_finset_sum _ fun i _ => ?_
    exact (continuous_snd.comp (continuous_apply i)).inner
      ((continuous_fst.comp (continuous_apply _)).sub (continuous_fst.comp (continuous_apply i)))
  have hclosed : IsClosed {z : Fin m → E × E | F z ≤ 0} := isClosed_le hF continuous_const
  have hsub : Set.pi univ (fun _ => Γ) ⊆ {z : Fin m → E × E | F z ≤ 0} := fun z hz' =>
    hΓ m z fun i => hz' i (mem_univ i)
  have hmem : z ∈ closure (Set.pi univ (fun _ : Fin m => Γ)) := by
    rw [closure_pi_set]; exact fun i _ => hz i
  exact hclosed.closure_subset_iff.2 hsub hmem

theorem cm_transpose_thm : Claims.cm_transpose := by
  intro E _ _ Γ hΓ
  exact StatFormal.OTFD.WaveL3.cycMon_swap hΓ

theorem cm_support_thm : Claims.cm_support := by
  rintro E _ _ _ π ⟨Γ, -, hΓ, hΓ0⟩
  have hcl : CycMon (closure Γ) := cm_closure_thm E Γ hΓ
  refine StatFormal.OTFD.WaveL3.cycMon_mono hcl (Measure.support_subset_of_isClosed isClosed_closure ?_)
  exact mem_of_superset (mem_ae_iff.2 hΓ0) subset_closure

end CM

/-! ### (ii) Rockafellar's construction -/

section Rockafellar
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The chain value `⟨y_n, x − x_n⟩ + Σ_{i<n} ⟨y_i, x_{i+1} − x_i⟩` of `w : Fin (n+1) → H × H`. -/
def chainVal {n : ℕ} (w : Fin (n + 1) → H × H) (x : H) : ℝ :=
  ⟪(w (Fin.last n)).2, x - (w (Fin.last n)).1⟫ +
    ∑ i : Fin n, ⟪(w i.castSucc).2, (w i.succ).1 - (w i.castSucc).1⟫

/-- Closing a chain at its base point gives the cyclic sum. -/
lemma chainVal_cycle {n : ℕ} (w : Fin (n + 1) → H × H) :
    chainVal w (w 0).1 = ∑ i : Fin (n + 1), ⟪(w i).2, (w (finRotate (n + 1) i)).1 - (w i).1⟫ := by
  rw [Fin.sum_univ_castSucc, chainVal, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [finRotate_of_lt (by simp)]
    congr 3
  · rw [finRotate_last]

lemma chainVal_le {Γ : Set (H × H)} (hΓ : CycMon Γ) {n : ℕ} {w : Fin (n + 1) → H × H} (hw : ∀ i, w i ∈ Γ) :
    chainVal w (w 0).1 ≤ 0 := by
  rw [chainVal_cycle]; exact hΓ (n + 1) w hw

lemma chainVal_snoc {n : ℕ} (w : Fin (n + 1) → H × H) (q : H × H) (z : H) :
    chainVal (Fin.snoc w q : Fin (n + 2) → H × H) z = chainVal w q.1 + ⟪q.2, z - q.1⟫ := by
  simp only [chainVal, Fin.snoc_last]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
  have : ∀ i : Fin n, (Fin.snoc w q : Fin (n + 2) → H × H) i.castSucc.succ = w i.succ := by
    intro i
    rw [show i.castSucc.succ = (i.succ).castSucc from rfl, Fin.snoc_castSucc]
  simp only [this]
  ring

lemma chainVal_sub {n : ℕ} (w : Fin (n + 1) → H × H) (x z : H) :
    chainVal w x - chainVal w z = ⟪(w (Fin.last n)).2, x - z⟫ := by
  simp only [chainVal, inner_sub_right]; ring

/-- The chain values at `x` of chains in `Γ` from the base point `p₀`. -/
def chainSet (Γ : Set (H × H)) (p₀ : H × H) (x : H) : Set ℝ :=
  {r | ∃ (n : ℕ) (w : Fin (n + 1) → H × H), w 0 = p₀ ∧ (∀ i, w i ∈ Γ) ∧ r = chainVal w x}

/-- Rockafellar's potential `f(x) = sup chainSet`. -/
def rockPot (Γ : Set (H × H)) (p₀ : H × H) (x : H) : ℝ := sSup (chainSet Γ p₀ x)

variable {Γ : Set (H × H)} {p₀ : H × H} {M : ℝ}

lemma chainSet_nonempty (hp : p₀ ∈ Γ) (x : H) : (chainSet Γ p₀ x).Nonempty :=
  ⟨_, 0, fun _ => p₀, rfl, fun _ => hp, rfl⟩

lemma chainVal_le_bound (hΓ : CycMon Γ) (hM : ∀ p ∈ Γ, ‖p.2‖ ≤ M) {n : ℕ} {w : Fin (n + 1) → H × H}
    (h0 : w 0 = p₀) (hw : ∀ i, w i ∈ Γ) (x : H) : chainVal w x ≤ M * ‖x - p₀.1‖ := by
  have h1 := chainVal_sub w x p₀.1
  have h2 : chainVal w p₀.1 ≤ 0 := by rw [← h0]; exact chainVal_le hΓ hw
  have h3 : ⟪(w (Fin.last n)).2, x - p₀.1⟫ ≤ M * ‖x - p₀.1‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM _ (hw _)) (norm_nonneg _))
  linarith

lemma chainSet_bdd (hΓ : CycMon Γ) (hM : ∀ p ∈ Γ, ‖p.2‖ ≤ M) (x : H) : BddAbove (chainSet Γ p₀ x) :=
  ⟨M * ‖x - p₀.1‖, by rintro r ⟨n, w, h0, hw, rfl⟩; exact chainVal_le_bound hΓ hM h0 hw x⟩

lemma chainVal_le_rockPot (hΓ : CycMon Γ) (hM : ∀ p ∈ Γ, ‖p.2‖ ≤ M) {n : ℕ} {w : Fin (n + 1) → H × H}
    (h0 : w 0 = p₀) (hw : ∀ i, w i ∈ Γ) (x : H) : chainVal w x ≤ rockPot Γ p₀ x :=
  le_csSup (chainSet_bdd hΓ hM x) ⟨n, w, h0, hw, rfl⟩

lemma rockPot_le_add (hp : p₀ ∈ Γ) (hΓ : CycMon Γ) (hM : ∀ p ∈ Γ, ‖p.2‖ ≤ M) (x z : H) :
    rockPot Γ p₀ x ≤ rockPot Γ p₀ z + M * ‖x - z‖ := by
  refine csSup_le (chainSet_nonempty hp x) ?_
  rintro r ⟨n, w, h0, hw, rfl⟩
  have h1 := chainVal_sub w x z
  have h3 : ⟪(w (Fin.last n)).2, x - z⟫ ≤ M * ‖x - z‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM _ (hw _)) (norm_nonneg _))
  have := chainVal_le_rockPot hΓ hM h0 hw z
  linarith

end Rockafellar

theorem cm_rockafellar_thm : Claims.cm_rockafellar := by
  intro H _ _ Γ M ⟨p₀, hp⟩ hΓ hM
  refine ⟨rockPot Γ p₀, ⟨convex_univ, ?_⟩, ?_, ?_⟩
  · intro x _ z _ a b ha hb hab
    refine csSup_le (chainSet_nonempty hp _) ?_
    rintro r ⟨n, w, h0, hw, rfl⟩
    have e : chainVal w (a • x + b • z) = a * chainVal w x + b * chainVal w z := by
      have h1 := chainVal_sub w (a • x + b • z) z
      have h2 := chainVal_sub w x z
      have : a • x + b • z - z = a • (x - z) := by
        rw [show b = 1 - a by linarith, sub_smul, one_smul, smul_sub]; abel
      rw [this, inner_smul_right] at h1
      linear_combination h1 - a * h2 - (chainVal w z) * hab
    rw [e, smul_eq_mul, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (chainVal_le_rockPot hΓ hM h0 hw x) ha)
      (mul_le_mul_of_nonneg_left (chainVal_le_rockPot hΓ hM h0 hw z) hb)
  · intro x z
    have h1 := rockPot_le_add hp hΓ hM x z
    have h2 := rockPot_le_add hp hΓ hM z x
    rw [norm_sub_rev] at h2
    rw [abs_le]; constructor <;> linarith
  · intro q hq z
    have : rockPot Γ p₀ q.1 ≤ rockPot Γ p₀ z - ⟪q.2, z - q.1⟫ := by
      refine csSup_le (chainSet_nonempty hp _) ?_
      rintro r ⟨n, w, h0, hw, rfl⟩
      have hsnoc := chainVal_snoc w q z
      have h0' : (Fin.snoc w q : Fin (n + 2) → H × H) 0 = p₀ := by
        rw [show (0 : Fin (n + 2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc, h0]
      have hw' : ∀ i, (Fin.snoc w q : Fin (n + 2) → H × H) i ∈ Γ := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [Fin.snoc_last]; exact hq
        · rw [Fin.snoc_castSucc]; exact hw j
      have := chainVal_le_rockPot hΓ hM h0' hw' z
      linarith
    linarith

/-! ### (iv) the graph plan, moment-free -/

lemma isMonotoneSet_of_cycMon {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {Γ : Set (H × H)}
    (hΓ : CycMon Γ) : StatFormal.Potentials.IsMonotoneSet Γ := by
  intro p hp q hq
  have h := hΓ 2 ![p, q] (fun i => by fin_cases i <;> simpa)
  simp only [Fin.sum_univ_two] at h
  have h0 : finRotate 2 0 = 1 := rfl
  have h1 : finRotate 2 1 = 0 := rfl
  rw [h0, h1] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have : ⟪p.2 - q.2, p.1 - q.1⟫ = -(⟪p.2, q.1 - p.1⟫ + ⟪q.2, p.1 - q.1⟫) := by
    simp only [inner_sub_left, inner_sub_right]; ring
  rw [this]; linarith

theorem cm_graph_exists_thm : Claims.cm_graph_exists := by
  rintro H _ _ _ _ _ _ γ hγ hA ⟨Γ, hΓm, hΓ, hΓ0⟩
  have hM : γ.fst (StatFormal.Potentials.multivaluedSet Γ) = 0 :=
    StatFormal.Potentials.measure_multivaluedSet_eq_zero (fun S hS => hA S hS) (isMonotoneSet_of_cycMon hΓ)
  have hae : ∀ᵐ z ∂γ, z ∈ Γ := (measure_eq_zero_iff_ae_notMem.1 hΓ0).mono fun _ h => Set.notMem_compl_iff.1 h
  obtain ⟨T, hT, hγT, -⟩ := StatFormal.Potentials.exists_eq_graphPlan_of_ae_mem
    (⟨rfl, rfl⟩ : IsCoupling γ γ.fst γ.snd) hΓm hae hM
  refine ⟨T, hT, hγT, ?_⟩
  conv_rhs => rw [hγT]
  exact (snd_graphPlan hT.aemeasurable).symm

end StatFormal.Wave23d
