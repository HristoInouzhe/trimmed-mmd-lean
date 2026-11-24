import StatFormal.Archive.WaveP3a.Statements
import StatFormal.Archive.OTFD.Wave12a.RouteEntropic

/-!
# Route: R `thm:region-breakdown`, band half

The band edges' sup-norm and the region sup are comparable up to constants of the evaluation functionals:
`bandSup ≤ C · regionSup` (`‖e(t)‖ ≤ C`) and `regionSup ≤ L · bandSup` (`L` the antilipschitz constant of
`y ↦ (⟨b, y⟩)_{b ∈ B}` for a basis `B ⊆ range e`). So both explode for the same contaminations.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ENNReal

namespace StatFormal.WaveP3a

open StatFormal.OTFDR (piCond Qhat)
open StatFormal.OTFDR.Lift (Contam Explodes BP)
open StatFormal.OTFD.Wave6b (regionSup norm_qhat_le bdd_region)

variable {K n : ℕ} {𝒯 : Type} {ε : ℝ} {fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ}
  {A : Set (EuclideanSpace ℝ (Fin K))} {e : 𝒯 → EuclideanSpace ℝ (Fin K)}

lemma inner_qhat_le (Z' : Fin n → EuclideanSpace ℝ (Fin K)) (v : EuclideanSpace ℝ (Fin K)) (u) :
    |⟪v, Qhat Z' (fsel Z') ε u⟫_ℝ| ≤ ‖v‖ * ∑ i, ‖Z' i‖ :=
  (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_qhat_le _ _ _ _) (norm_nonneg _))

lemma bdd_inner (Z' : Fin n → EuclideanSpace ℝ (Fin K)) (v : EuclideanSpace ℝ (Fin K)) :
    BddAbove (range fun u : A => ⟪v, Qhat Z' (fsel Z') ε u⟫_ℝ) :=
  ⟨‖v‖ * ∑ i, ‖Z' i‖, by rintro _ ⟨u, rfl⟩; exact (le_abs_self _).trans (inner_qhat_le _ _ _)⟩

lemma abs_sup_inner_le (hAne : A.Nonempty) (Z' : Fin n → EuclideanSpace ℝ (Fin K)) (v : EuclideanSpace ℝ (Fin K))
    (M : ℝ) (hM : ∀ u ∈ A, |⟪v, Qhat Z' (fsel Z') ε u⟫_ℝ| ≤ M) :
    |⨆ u : A, ⟪v, Qhat Z' (fsel Z') ε u⟫_ℝ| ≤ M := by
  have : Nonempty A := hAne.to_subtype
  obtain ⟨u₀, hu₀⟩ := hAne
  rw [abs_le]
  constructor
  · have h1 := le_ciSup (bdd_inner (A := A) (fsel := fsel) (ε := ε) Z' v) ⟨u₀, hu₀⟩
    have h2 := (abs_le.mp (hM u₀ hu₀)).1
    exact h2.trans h1
  · exact ciSup_le fun u => (le_abs_self _).trans (hM u u.2)

lemma regionSup_nonneg (hAne : A.Nonempty) (Z' : Fin n → EuclideanSpace ℝ (Fin K)) :
    0 ≤ regionSup ε fsel A Z' := by
  obtain ⟨u, hu⟩ := hAne
  exact (norm_nonneg _).trans (le_ciSup (bdd_region (fsel := fsel) (ε := ε) (A := A) Z') ⟨u, hu⟩)

lemma norm_qhat_le_regionSup (Z' : Fin n → EuclideanSpace ℝ (Fin K)) {u} (hu : u ∈ A) :
    ‖Qhat Z' (fsel Z') ε u‖ ≤ regionSup ε fsel A Z' :=
  le_ciSup (bdd_region (fsel := fsel) (ε := ε) (A := A) Z') ⟨u, hu⟩

/-- The edge terms at `t` are bounded by `‖e t‖ · regionSup`. -/
lemma edge_le (hAne : A.Nonempty) (Z' : Fin n → EuclideanSpace ℝ (Fin K)) (t : 𝒯) :
    max |⨆ u : A, ⟪e t, Qhat Z' (fsel Z') ε u⟫_ℝ| |-⨆ u : A, ⟪-e t, Qhat Z' (fsel Z') ε u⟫_ℝ| ≤
      ‖e t‖ * regionSup ε fsel A Z' := by
  have hb : ∀ v : EuclideanSpace ℝ (Fin K), ‖v‖ = ‖e t‖ → ∀ u ∈ A,
      |⟪v, Qhat Z' (fsel Z') ε u⟫_ℝ| ≤ ‖e t‖ * regionSup ε fsel A Z' := fun v hv u hu =>
    (abs_real_inner_le_norm _ _).trans (by
      rw [hv]; exact mul_le_mul_of_nonneg_left (norm_qhat_le_regionSup Z' hu) (norm_nonneg _))
  refine max_le (abs_sup_inner_le hAne Z' _ _ (hb _ rfl)) ?_
  rw [abs_neg]
  exact abs_sup_inner_le hAne Z' _ _ (hb _ (norm_neg _))

lemma bdd_edges (hAne : A.Nonempty) (hC : ∃ C : ℝ, ∀ t, ‖e t‖ ≤ C) (Z' : Fin n → EuclideanSpace ℝ (Fin K)) :
    BddAbove (range fun t => max |⨆ u : A, ⟪e t, Qhat Z' (fsel Z') ε u⟫_ℝ|
      |-⨆ u : A, ⟪-e t, Qhat Z' (fsel Z') ε u⟫_ℝ|) := by
  obtain ⟨C, hC⟩ := hC
  refine ⟨C * regionSup ε fsel A Z', ?_⟩
  rintro _ ⟨t, rfl⟩
  exact (edge_le hAne Z' t).trans (mul_le_mul_of_nonneg_right (hC t) (regionSup_nonneg hAne Z'))

lemma bandSup_nonneg (Z' : Fin n → EuclideanSpace ℝ (Fin K)) : 0 ≤ bandSup ε fsel A e Z' :=
  Real.iSup_nonneg fun _ => (abs_nonneg _).trans (le_max_left _ _)

lemma bandSup_le (hAne : A.Nonempty) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖e t‖ ≤ C)
    (Z' : Fin n → EuclideanSpace ℝ (Fin K)) : bandSup ε fsel A e Z' ≤ C * regionSup ε fsel A Z' :=
  Real.iSup_le (fun t => (edge_le hAne Z' t).trans
    (mul_le_mul_of_nonneg_right (hC t) (regionSup_nonneg hAne Z')))
    (mul_nonneg hC0 (regionSup_nonneg hAne Z'))

/-- A basis inside `range e` and the antilipschitz constant of the evaluation map. -/
lemma exists_eval_bound (hspan : Submodule.span ℝ (Set.range e) = ⊤) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ s : Finset 𝒯, ∀ y : EuclideanSpace ℝ (Fin K),
      ‖y‖ ≤ L * ∑ t ∈ s, |⟪e t, y⟫_ℝ| := by
  classical
  obtain ⟨b, hb, hbspan, hbli⟩ := exists_linearIndependent ℝ (Set.range e)
  have hfin : b.Finite := hbli.setFinite
  -- choose a preimage for each basis vector
  have hpre : ∀ x : b, ∃ t, e t = x := fun x => hb x.2
  choose τ hτ using hpre
  have : Fintype b := hfin.fintype
  let s : Finset 𝒯 := Finset.univ.image τ
  let F : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] (b → ℝ) :=
    { toFun := fun y x => ⟪(x : EuclideanSpace ℝ (Fin K)), y⟫_ℝ
      map_add' := fun y z => by ext x; simp [inner_add_right]
      map_smul' := fun c y => by ext x; simp [inner_smul_right] }
  have hker : LinearMap.ker F = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    have hy' : ∀ x ∈ b, ⟪x, y⟫_ℝ = 0 := fun x hx => congrFun hy ⟨x, hx⟩
    have hall : ∀ w ∈ Submodule.span ℝ b, ⟪w, y⟫_ℝ = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact hy' x hx
      | zero => simp
      | add x z _ _ hx hz => rw [inner_add_left, hx, hz, add_zero]
      | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
    have hyy := hall y (by rw [hbspan, hspan]; trivial)
    exact inner_self_eq_zero.mp hyy
  obtain ⟨L, hL0, hL⟩ := F.exists_antilipschitzWith hker
  refine ⟨L, L.2, s, fun y => ?_⟩
  have h1 : ‖y‖ ≤ L * ‖F y‖ := by
    have := hL.le_mul_dist y 0
    simpa [dist_eq_norm] using this
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ L.2)
  rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
  intro x
  have hx : (x : EuclideanSpace ℝ (Fin K)) = e (τ x) := (hτ x).symm
  change ‖⟪(x : EuclideanSpace ℝ (Fin K)), y⟫_ℝ‖ ≤ _
  rw [Real.norm_eq_abs, hx]
  exact Finset.single_le_sum (f := fun t => |⟪e t, y⟫_ℝ|) (fun _ _ => abs_nonneg _)
    (Finset.mem_image_of_mem τ (Finset.mem_univ x))

lemma regionSup_le (hAne : A.Nonempty) (hC : ∃ C : ℝ, ∀ t, ‖e t‖ ≤ C)
    (hspan : Submodule.span ℝ (Set.range e) = ⊤) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ Z' : Fin n → EuclideanSpace ℝ (Fin K),
      regionSup ε fsel A Z' ≤ L * bandSup ε fsel A e Z' := by
  obtain ⟨L, hL0, s, hs⟩ := exists_eval_bound hspan
  refine ⟨L * s.card, mul_nonneg hL0 (Nat.cast_nonneg _), fun Z' => ?_⟩
  have : Nonempty A := hAne.to_subtype
  refine ciSup_le fun u => ?_
  refine (hs _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hL0
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun t _ => ?_
  have hup : ⟪e t, Qhat Z' (fsel Z') ε u⟫_ℝ ≤ ⨆ u : A, ⟪e t, Qhat Z' (fsel Z') ε u⟫_ℝ :=
    le_ciSup (bdd_inner (A := A) (fsel := fsel) (ε := ε) Z' (e t)) u
  have hlo : ⟪-e t, Qhat Z' (fsel Z') ε u⟫_ℝ ≤ ⨆ u : A, ⟪-e t, Qhat Z' (fsel Z') ε u⟫_ℝ :=
    le_ciSup (bdd_inner (A := A) (fsel := fsel) (ε := ε) Z' (-e t)) u
  have hmax : max |⨆ u : A, ⟪e t, Qhat Z' (fsel Z') ε u⟫_ℝ| |-⨆ u : A, ⟪-e t, Qhat Z' (fsel Z') ε u⟫_ℝ| ≤
      bandSup ε fsel A e Z' := le_ciSup (bdd_edges hAne hC Z') t
  refine le_trans ?_ hmax
  have hneg : ⟪-e t, Qhat Z' (fsel Z') ε u⟫_ℝ = -⟪e t, Qhat Z' (fsel Z') ε u⟫_ℝ := inner_neg_left _ _
  set a := ⟪e t, Qhat Z' (fsel Z') ε u⟫_ℝ
  set S1 := ⨆ u : A, ⟪e t, Qhat Z' (fsel Z') ε u⟫_ℝ
  set S2 := ⨆ u : A, ⟪-e t, Qhat Z' (fsel Z') ε u⟫_ℝ
  have h1 := le_abs_self S1
  have h2 := le_abs_self S2
  have h3 := le_max_left |S1| |-S2|
  have h4 := le_max_right |S1| |-S2|
  have h5 : |-S2| = |S2| := abs_neg _
  rw [abs_le]
  constructor <;> linarith

/-- Two nonnegative estimators that dominate each other up to constants explode together. -/
lemma explodes_iff {X : Type*} {S S' : (Fin n → X) → ℝ} {Z : Fin n → X} {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hS : ∀ Z', 0 ≤ S Z') (hS' : ∀ Z', 0 ≤ S' Z') (h1 : ∀ Z', S Z' ≤ c * S' Z') (h2 : ∀ Z', S' Z' ≤ c' * S Z')
    (ℓ : ℕ) : Explodes S Z ℓ ↔ Explodes S' Z ℓ := by
  unfold Explodes
  constructor
  · intro h hb
    apply h
    obtain ⟨M, hM⟩ := hb
    refine ⟨c * M, ?_⟩
    rintro _ ⟨Z', hZ', rfl⟩
    have := hM ⟨Z', hZ', rfl⟩
    simp only [Real.norm_eq_abs, abs_of_nonneg (hS Z'), abs_of_nonneg (hS' Z')] at this ⊢
    exact (h1 Z').trans (mul_le_mul_of_nonneg_left this hc)
  · intro h hb
    apply h
    obtain ⟨M, hM⟩ := hb
    refine ⟨c' * M, ?_⟩
    rintro _ ⟨Z', hZ', rfl⟩
    have := hM ⟨Z', hZ', rfl⟩
    simp only [Real.norm_eq_abs, abs_of_nonneg (hS Z'), abs_of_nonneg (hS' Z')] at this ⊢
    exact (h2 Z').trans (mul_le_mul_of_nonneg_left this hc')

lemma BP_congr {X : Type*} {S S' : (Fin n → X) → ℝ} {Z : Fin n → X}
    (h : Explodes S Z = Explodes S' Z) : BP S Z = BP S' Z := by
  classical
  unfold BP
  by_cases h1 : ∃ ℓ, 1 ≤ ℓ ∧ Explodes S Z ℓ
  · have h2 : ∃ ℓ, 1 ≤ ℓ ∧ Explodes S' Z ℓ := by rw [← h]; exact h1
    rw [dif_pos h1, dif_pos h2]
    congr 2
    exact Nat.find_congr' (fun {ℓ} => by rw [h])
  · have h2 : ¬ ∃ ℓ, 1 ≤ ℓ ∧ Explodes S' Z ℓ := by rw [← h]; exact h1
    rw [dif_neg h1, dif_neg h2]

theorem band_region_bp_eq : Claims.band_region_bp_eq := by
  intro K n 𝒯 ε fsel Z A e hAne hC hspan
  obtain ⟨C, hC'⟩ := hC
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  obtain ⟨L, hL0, hL⟩ := regionSup_le (n := n) (ε := ε) (fsel := fsel) hAne ⟨C, hC'⟩ hspan
  have key : Explodes (bandSup ε fsel A e) Z = Explodes (regionSup ε fsel A) Z := by
    funext ℓ
    exact propext (explodes_iff hC0 hL0 (bandSup_nonneg) (regionSup_nonneg hAne)
      (bandSup_le hAne hC0 (fun t => (hC' t).trans (le_max_left _ _))) hL ℓ)
  exact BP_congr key

theorem band_bp_unconditional : Claims.band_bp_unconditional := by
  intro K n 𝒯 ν _ ε fsel Z A e hK hn hac hset hA hAne hC hspan
  rw [band_region_bp_eq K n 𝒯 ε fsel Z A e hAne hC hspan]
  exact OTFD.Wave12a.region_bp_unconditional K n ν ε fsel Z A hK hn hac hset hA hAne

theorem band_bp_general_unconditional : Claims.band_bp_general_unconditional := by
  intro K n 𝒯 ν _ ε fsel Z A e hK hn hset hA hAne hC hspan
  rw [band_region_bp_eq K n 𝒯 ε fsel Z A e hAne hC hspan]
  exact OTFD.Wave12a.region_bp_general_unconditional K n ν ε fsel Z A hK hn hset hA hAne

end StatFormal.WaveP3a
