import StatFormal.Archive.OTFD.Ranks.Statements
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Proofs for `StatFormal.OTFD.Ranks.Claims`

* `invariant_perm_uniform`: every fibre of `σ` has the mass of the fibre over `1`;
  the fibres partition `Ω`.
* `fixedK_df`: equivariance `cost u (z ∘ τ) (σ * τ) = cost u z σ`; on the uniqueness set
  `sel (z ∘ τ) = sel z * τ`; exchangeability transfers the fibre masses.
* `unique_forces_distinct`: a repeated grid point (resp. sample point) yields a second minimiser
  `swap j k * σ` (resp. `σ * swap i j`).
* `nonatomic_not_sufficient`: `u = (-e₀, e₀)`, `ν` = uniform law on `{0} × [0,1]` (the bisector).
-/

noncomputable section
open MeasureTheory

namespace StatFormal.OTFD.Ranks

section General

variable {E : Type*} [NormedAddCommGroup E]

lemma cost_comp {n : ℕ} (u z : Fin n → E) (σ τ : Equiv.Perm (Fin n)) :
    cost u (z ∘ τ) (σ * τ) = cost u z σ := by
  unfold cost
  exact Equiv.sum_comp τ (fun i => ‖z i - u (σ i)‖ ^ 2)

lemma isMin_comp_iff {n : ℕ} (u z : Fin n → E) (σ τ : Equiv.Perm (Fin n)) :
    IsMin u (z ∘ τ) (σ * τ) ↔ IsMin u z σ := by
  constructor
  · intro h ρ
    have := h (ρ * τ)
    rwa [cost_comp, cost_comp] at this
  · intro h ρ
    have e := cost_comp u z (ρ * τ⁻¹) τ
    rw [inv_mul_cancel_right] at e
    rw [cost_comp, e]
    exact h _

lemma sel_comp {n : ℕ} (u : Fin n → E) (sel : (Fin n → E) → Equiv.Perm (Fin n))
    (hsel : ∀ z, IsMin u z (sel z)) (z : Fin n → E) (hz : UniqueMin u z)
    (τ : Equiv.Perm (Fin n)) : sel (z ∘ τ) = sel z * τ := by
  obtain ⟨σ, -, hσ⟩ := hz
  have h1 : sel (z ∘ τ) * τ⁻¹ = sel z := by
    have a : IsMin u z (sel (z ∘ τ) * τ⁻¹) := by
      rw [← isMin_comp_iff u z _ τ, inv_mul_cancel_right]
      exact hsel _
    rw [hσ _ a, hσ _ (hsel z)]
  rw [← h1, inv_mul_cancel_right]

end General

theorem invariant_perm_uniform : Claims.invariant_perm_uniform := by
  intro Ω _ P _ n σ hmeas hinv h
  have hall : ∀ g, P {ω | σ ω = g} = P {ω | σ ω = 1} := by
    intro g
    rw [← hinv g⁻¹ 1]
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, mul_inv_eq_one]
  have hsum := sum_measure_preimage_singleton (μ := P) (f := σ) Finset.univ
    (fun g _ => hmeas g)
  simp only [Finset.coe_univ, Set.preimage_univ, measure_univ] at hsum
  have hsum' : ∑ _g : Equiv.Perm (Fin n), P {ω | σ ω = 1} = 1 := by
    rw [← hsum]
    exact Finset.sum_congr rfl (fun g _ => (hall g).symm)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    at hsum'
  rw [hall h, mul_comm] at *
  exact ENNReal.eq_inv_of_mul_eq_one_left hsum'

theorem fixedK_df : Claims.fixedK_df := by
  intro E _ _ _ _ Ω _ P _ n u Z sel hZ hsel hfib hexch huniq h
  have hmZ : ∀ g, MeasurableSet {ω | sel (Z ω) = g} := fun g => hZ (hfib g)
  refine invariant_perm_uniform Ω P n (fun ω => sel (Z ω)) hmZ ?_ h
  intro π g
  have hZτ : Measurable (fun ω => Z ω ∘ π) :=
    Measurable.of_eval (fun i => (measurable_pi_apply (π i)).comp hZ)
  have hae : {ω | sel (Z ω) * π = g} =ᵐ[P] {ω | sel (Z ω ∘ π) = g} := by
    filter_upwards [huniq] with ω hω
    rw [sel_comp u sel hsel (Z ω) hω π]
  rw [measure_congr hae]
  have e1 : P {ω | sel (Z ω ∘ π) = g} = P.map (fun ω => Z ω ∘ π) {z | sel z = g} := by
    rw [Measure.map_apply hZτ (hfib g)]; rfl
  have e2 : P {ω | sel (Z ω) = g} = P.map Z {z | sel z = g} := by
    rw [Measure.map_apply hZ (hfib g)]; rfl
  rw [e1, e2, hexch π]

theorem unique_forces_distinct : Claims.unique_forces_distinct := by
  intro E _ _ n u z ⟨σ, hσ, huniq⟩
  constructor
  · intro j k hjk
    by_contra hne
    have hc : cost u z (Equiv.swap j k * σ) = cost u z σ := by
      unfold cost
      refine Finset.sum_congr rfl (fun i _ => ?_)
      congr 3
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      rcases eq_or_ne (σ i) j with h1 | h1
      · rw [h1, Equiv.swap_apply_left, hjk]
      rcases eq_or_ne (σ i) k with h2 | h2
      · rw [h2, Equiv.swap_apply_right, hjk]
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    have hm : IsMin u z (Equiv.swap j k * σ) := fun τ => hc ▸ hσ τ
    have := huniq _ hm
    rw [mul_eq_right, Equiv.swap_eq_one_iff] at this
    exact hne this
  · intro i j hij
    by_contra hne
    have hz : z ∘ Equiv.swap i j = z := by
      funext k
      simp only [Function.comp_apply]
      rcases eq_or_ne k i with h1 | h1
      · rw [h1, Equiv.swap_apply_left, hij]
      rcases eq_or_ne k j with h2 | h2
      · rw [h2, Equiv.swap_apply_right, hij]
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    have hc : cost u z (σ * Equiv.swap i j) = cost u z σ := by
      conv_lhs => rw [← hz]
      exact cost_comp u z σ _
    have hm : IsMin u z (σ * Equiv.swap i j) := fun τ => hc ▸ hσ τ
    have := huniq _ hm
    rw [mul_eq_left, Equiv.swap_eq_one_iff] at this
    exact hne this

section Counterexample

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- The grid: `u 0 = -e₀`, `u 1 = e₀`. -/
def uCE : Fin 2 → E2 := fun i => if i = 0 then EuclideanSpace.single 0 (-1) else
  EuclideanSpace.single 0 1

/-- Embedding of `ℝ` onto the bisector `{x₀ = 0}`. -/
def emb (t : ℝ) : E2 := t • EuclideanSpace.single 1 (1 : ℝ)

lemma emb_injective : Function.Injective emb := by
  intro s t h
  have := congrArg (fun x : E2 => x 1) h
  simpa [emb] using this

lemma emb_measurable : Measurable emb := by
  exact (continuous_id.smul continuous_const).measurable

/-- Uniform law on `[0,1]` pushed to the bisector. -/
def νCE : Measure E2 := (volume.restrict (Set.Icc (0 : ℝ) 1)).map emb

lemma norm_sub_uCE (x : E2) (hx : x 0 = 0) (j : Fin 2) :
    ‖x - uCE j‖ ^ 2 = ‖x‖ ^ 2 + 1 := by
  fin_cases j <;>
  simp [uCE, norm_sub_sq_real, EuclideanSpace.inner_single_right, hx]

end Counterexample

theorem nonatomic_not_sufficient : Claims.nonatomic_not_sufficient := by
  refine ⟨uCE, νCE, ?_, ?_, ?_, ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h
      norm_num [uCE] at this
    · have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h
      norm_num [uCE] at this
    · rfl
  · refine ⟨?_⟩
    rw [νCE, Measure.map_apply emb_measurable MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num
  · refine ⟨fun x => ?_⟩
    rw [νCE, Measure.map_apply emb_measurable (measurableSet_singleton x)]
    exact (Set.subsingleton_singleton.preimage emb_injective).measure_zero _
  · have : IsProbabilityMeasure νCE := by
      refine ⟨?_⟩
      rw [νCE, Measure.map_apply emb_measurable MeasurableSet.univ, Set.preimage_univ,
        Measure.restrict_apply_univ, Real.volume_Icc]
      norm_num
    have hν : ∀ᵐ x ∂νCE, x 0 = 0 := by
      rw [ae_iff, νCE, Measure.map_apply emb_measurable]
      · have : emb ⁻¹' {a | ¬a 0 = 0} = ∅ := by
          ext t; simp [emb]
        rw [this, measure_empty]
      · exact (isClosed_eq (PiLp.continuous_apply 2 _ 0) continuous_const).measurableSet.compl
    have hall : ∀ᵐ z ∂(Measure.pi fun _ : Fin 2 => νCE), ∀ i, z i 0 = 0 := by
      rw [ae_all_iff]
      intro i
      exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin 2 => νCE) i).ae hν
    filter_upwards [hall] with z hz
    rintro ⟨σ, -, huniq⟩
    have hconst : ∀ ρ : Equiv.Perm (Fin 2), cost uCE z ρ = ∑ i, (‖z i‖ ^ 2 + 1) := by
      intro ρ
      unfold cost
      exact Finset.sum_congr rfl (fun i _ => norm_sub_uCE (z i) (hz i) (ρ i))
    have hmin : ∀ ρ, IsMin uCE z ρ := fun ρ τ => by rw [hconst, hconst]
    have h1 := huniq 1 (hmin 1)
    have h2 := huniq (Equiv.swap 0 1) (hmin _)
    have : (1 : Equiv.Perm (Fin 2)) = Equiv.swap 0 1 := h1.trans h2.symm
    exact absurd this (by decide)

end StatFormal.OTFD.Ranks
