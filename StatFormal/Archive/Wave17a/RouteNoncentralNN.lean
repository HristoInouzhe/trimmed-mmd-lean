import StatFormal.Archive.Wave17a.RouteNoncentral
import StatFormal.Archive.NNFibers.Wave1.RouteCodim
import Mathlib.Algebra.Order.Chebyshev

/-!
# Route: NN `prop:noncentral-tube` for `Γ̄_s`, and `eq:lambda-s` (untrusted)

* `eq:lambda-s`: for `θ ∈ Γ̄_s`, `‖θ‖² ≥ Σ_i (n_i‖ω_i‖² + ‖Σ_{u∈G_i} a_u‖²/n_i)` (Cauchy–Schwarz per group,
  `(Σ x)² ≤ n Σ x²`), with equality at `θ*` (copies `(ω_i, a_i/n_i)`, zero-type units `0`).
* The proposition: the coordinate map `eucPar` is a linear equivalence onto `ℝ^{m(d_in+d_out)}`, so `Γ̄_s` is mapped
  to an affine subspace with the same direction dimension (certified `codim_blockcount` for the codimension), and the
  Gaussian–affine core applies.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric Finset
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave17a

open StatFormal.NNFibers.Wave1

variable {din dout q m j : ℕ}

/-- `‖v‖² = Σ_k v_k²` on `ℝ^d = Fin d → ℝ`. -/
def sqn {d : ℕ} (v : Fin d → ℝ) : ℝ := ∑ k, v k ^ 2

lemma sqn_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ sqn v := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma norm_eucPar_sq (θ : Fin m → Neuron din dout) :
    ‖eucPar θ‖ ^ 2 = ∑ u, (sqn (θ u).1 + sqn (θ u).2) := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Fintype.sum_sum_type]
  simp [eucPar, sqn, Real.norm_eq_abs, sq_abs]

/-- The group sizes `n_i`. -/
def nsz (g : Fin m → Fin q ⊕ Fin j) (i : Fin q) : ℕ := (univ.filter fun u => g u = Sum.inl i).card

lemma nsz_pos {g : Fin m → Fin q ⊕ Fin j} (hg : Function.Surjective g) (i : Fin q) : 0 < nsz g i := by
  obtain ⟨u, hu⟩ := hg (Sum.inl i)
  exact Finset.card_pos.2 ⟨u, Finset.mem_filter.2 ⟨mem_univ _, hu⟩⟩

/-- The nearest point `θ*`. -/
def thetaStar (θs : Fin q → Neuron din dout) (g : Fin m → Fin q ⊕ Fin j) : Fin m → Neuron din dout :=
  fun u => Sum.elim (fun i => ((θs i).1, (1 / (nsz g i : ℝ)) • (θs i).2)) (fun _ => (0, 0)) (g u)

lemma sum_filter_const (g : Fin m → Fin q ⊕ Fin j) (s : Fin q ⊕ Fin j) {M : Type*} [AddCommMonoid M]
    [Module ℝ M] (F : Fin q ⊕ Fin j → M) :
    ∑ u ∈ univ.filter (fun u => g u = s), F (g u) = (univ.filter fun u => g u = s).card • F s := by
  rw [Finset.sum_congr rfl fun u hu => by rw [(Finset.mem_filter.1 hu).2], Finset.sum_const]

lemma thetaStar_mem (θs : Fin q → Neuron din dout) {g : Fin m → Fin q ⊕ Fin j} (hg : Function.Surjective g) :
    thetaStar θs g ∈ closureSet θs g := by
  refine ⟨⟨fun _ => 0, fun u => ?_⟩, fun i => ?_, fun ℓ => ?_⟩
  · simp only [thetaStar]; rcases g u with i | ℓ <;> rfl
  · have := sum_filter_const g (Sum.inl i)
      (fun s => (Sum.elim (fun i => ((θs i).1, (1 / (nsz g i : ℝ)) • (θs i).2)) (fun _ => (0, 0)) s).2)
    simp only [thetaStar]
    rw [this]
    simp only [Sum.elim_inl]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have hn : ((univ.filter fun u => g u = Sum.inl i).card : ℝ) ≠ 0 := by
      have := nsz_pos hg i; unfold nsz at this; positivity
    rw [show nsz g i = (univ.filter fun u => g u = Sum.inl i).card from rfl, mul_one_div_cancel hn, one_smul]
  · have := sum_filter_const g (Sum.inr ℓ)
      (fun s => (Sum.elim (fun i => ((θs i).1, (1 / (nsz g i : ℝ)) • (θs i).2)) (fun _ => (0, 0)) s).2)
    simp only [thetaStar]
    rw [this]
    simp

/-- Splitting a sum over units by group. -/
lemma sum_by_group (g : Fin m → Fin q ⊕ Fin j) (F : Fin m → ℝ) :
    ∑ u, F u = ∑ i, ∑ u ∈ univ.filter (fun u => g u = Sum.inl i), F u +
      ∑ ℓ, ∑ u ∈ univ.filter (fun u => g u = Sum.inr ℓ), F u := by
  rw [← Finset.sum_fiberwise univ g F, Fintype.sum_sum_type]

lemma norm_thetaStar (θs : Fin q → Neuron din dout) {g : Fin m → Fin q ⊕ Fin j} (hg : Function.Surjective g) :
    ‖eucPar (thetaStar θs g)‖ ^ 2 = lamS θs g := by
  rw [norm_eucPar_sq, sum_by_group g]
  have h2 : ∀ ℓ : Fin j, ∑ u ∈ univ.filter (fun u => g u = Sum.inr ℓ),
      (sqn (thetaStar θs g u).1 + sqn (thetaStar θs g u).2) = 0 := by
    intro ℓ
    refine Finset.sum_eq_zero fun u hu => ?_
    simp [thetaStar, (Finset.mem_filter.1 hu).2, sqn]
  simp only [h2, Finset.sum_const_zero, add_zero, lamS]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∀ u ∈ univ.filter (fun u => g u = Sum.inl i),
      sqn (thetaStar θs g u).1 + sqn (thetaStar θs g u).2 =
        sqn (θs i).1 + (1 / (nsz g i : ℝ)) ^ 2 * sqn (θs i).2 := by
    intro u hu
    simp only [thetaStar, (Finset.mem_filter.1 hu).2, Sum.elim_inl, sqn, Pi.smul_apply, smul_eq_mul, mul_pow,
      Finset.mul_sum]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
  have hn : (0 : ℝ) < nsz g i := by exact_mod_cast nsz_pos hg i
  unfold nsz at hn ⊢
  simp only [sqn]
  field_simp

lemma norm_ge_lamS (θs : Fin q → Neuron din dout) {g : Fin m → Fin q ⊕ Fin j} (hg : Function.Surjective g)
    {θ : Fin m → Neuron din dout} (hθ : θ ∈ closureSet θs g) : lamS θs g ≤ ‖eucPar θ‖ ^ 2 := by
  obtain ⟨⟨ω', hω'⟩, hsum, -⟩ := hθ
  rw [norm_eucPar_sq, sum_by_group g]
  have hz : 0 ≤ ∑ ℓ, ∑ u ∈ univ.filter (fun u => g u = Sum.inr ℓ), (sqn (θ u).1 + sqn (θ u).2) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (sqn_nonneg _) (sqn_nonneg _)
  refine le_trans ?_ (le_add_of_nonneg_right hz)
  unfold lamS
  refine Finset.sum_le_sum fun i _ => ?_
  set G := univ.filter (fun u => g u = Sum.inl i)
  have hn : (0 : ℝ) < G.card := by exact_mod_cast nsz_pos hg i
  rw [Finset.sum_add_distrib]
  have hω : ∀ u ∈ G, sqn (θ u).1 = sqn (θs i).1 := by
    intro u hu; rw [hω' u, (Finset.mem_filter.1 hu).2]; rfl
  rw [Finset.sum_congr rfl hω, Finset.sum_const, nsmul_eq_mul]
  refine add_le_add le_rfl ?_
  rw [div_le_iff₀ hn, ← hsum i]
  -- Cauchy–Schwarz coordinatewise
  simp only [sqn, Finset.sum_apply]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  have := sq_sum_le_card_mul_sum_sq (s := G) (f := fun u => (θ u).2 k)
  linarith

theorem lambda_s : Claims.lambda_s := by
  intro din dout q m j θs g hg
  set S := eucPar '' closureSet θs g
  have hmem : eucPar (thetaStar θs g) ∈ S := ⟨_, thetaStar_mem θs hg, rfl⟩
  have hL0 : 0 ≤ lamS θs g := by rw [← norm_thetaStar θs hg]; positivity
  apply le_antisymm
  · have h1 : infDist 0 S ≤ ‖eucPar (thetaStar θs g)‖ := by
      refine (infDist_le_dist_of_mem hmem).trans_eq ?_
      rw [dist_comm, dist_zero_right]
    calc infDist 0 S ^ 2 ≤ ‖eucPar (thetaStar θs g)‖ ^ 2 := pow_le_pow_left₀ infDist_nonneg h1 2
      _ = _ := norm_thetaStar θs hg
  · have h1 : Real.sqrt (lamS θs g) ≤ infDist 0 S := by
      refine (le_infDist ⟨_, hmem⟩).2 fun y hy => ?_
      obtain ⟨θ, hθ, rfl⟩ := hy
      rw [dist_comm, dist_zero_right, ← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (norm_ge_lamS θs hg hθ)
    calc lamS θs g = Real.sqrt (lamS θs g) ^ 2 := (Real.sq_sqrt hL0).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2

/-- `eucPar` as a linear equivalence. -/
def eucParL : (Fin m → Neuron din dout) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m × (Fin din ⊕ Fin dout)) where
  toFun := eucPar
  invFun y := fun u => (fun k => y (u, Sum.inl k), fun k => y (u, Sum.inr k))
  map_add' x y := by ext ⟨u, k | k⟩ <;> rfl
  map_smul' c x := by ext ⟨u, k | k⟩ <;> rfl
  left_inv x := by funext u; rfl
  right_inv y := by ext ⟨u, k | k⟩ <;> rfl

theorem noncentral_tube : Claims.noncentral_tube := by
  intro din dout q m j θs g σ δ hg hσ hδ
  set E := EuclideanSpace ℝ (Fin m × (Fin din ⊕ Fin dout))
  obtain ⟨A, hA, -⟩ := dim_closure din dout q m j θs g hg
  obtain ⟨hcod, -⟩ := codim_blockcount din dout q m j θs g A hg hA
  set V : AffineSubspace ℝ E := A.map (eucParL (din := din) (dout := dout) (m := m)).toLinearMap.toAffineMap
  have hV : (V : Set E) = eucPar '' closureSet θs g := by
    rw [AffineSubspace.coe_map, hA]; rfl
  have hne : (V : Set E).Nonempty := hV ▸ ⟨_, thetaStar θs g, thetaStar_mem θs hg, rfl⟩
  have hcore := noncentral_tube_affine E V σ δ hne hσ hδ
  rw [hV, lambda_s din dout q m j θs g hg] at hcore
  convert hcore using 3
  -- the codimension
  have hdir : Module.finrank ℝ V.direction = Module.finrank ℝ A.direction := by
    rw [AffineSubspace.map_direction]
    exact LinearEquiv.finrank_map_eq _ _
  have hfin : Module.finrank ℝ E = Module.finrank ℝ (Fin m → Neuron din dout) :=
    (LinearEquiv.finrank_eq (eucParL (din := din) (dout := dout) (m := m))).symm
  have hle : Module.finrank ℝ V.direction ≤ Module.finrank ℝ E := Submodule.finrank_le _
  have hjm : j ≤ m := by
    have := Fintype.card_le_of_surjective g hg
    simp at this; omega
  rw [hdir] at hle ⊢
  rw [hfin] at hle ⊢
  zify [hle, hjm]
  linarith

end StatFormal.Wave17a
