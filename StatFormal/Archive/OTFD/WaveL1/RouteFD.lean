import StatFormal.Archive.OTFD.WaveL1.RoutePlanStab
import StatFormal.Lib.OTLimits.Quadratic

/-!
# Route (wave L1): finite dimension — uniqueness of cyclically monotone couplings

Untrusted route file. The paper's cyclical monotonicity (cycles of inner products) implies Tau
Ceti's `c`-cyclical monotonicity (all permutations) for `c = ‖x − y‖²/2`, through Rüschendorf's
potential (`TauCeti.rockafellarPotential`, whose base-point identity is reproved here from cycles
only). In `ℝ^d`, with `P ≪ Leb` and finite second moments, every coupling concentrated on a
cyclically monotone set is then optimal (Tau Ceti, Knott–Smith) and hence unique (Tau Ceti,
Brenier), which discharges `BrenierUniq`.
-/

open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL1

section CM

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real quadratic cost `‖x − y‖²/2`. -/
noncomputable abbrev qc (E : Type*) [NormedAddCommGroup E] : E × E → ℝ := fun p => ‖p.1 - p.2‖ ^ 2 / 2

theorem qc_sub (a b y : E) :
    qc E (a, y) - qc E (b, y) = (‖a‖ ^ 2 - ‖b‖ ^ 2) / 2 - ⟪y, a - b⟫ := by
  simp only [qc, norm_sub_sq_real, inner_sub_right, real_inner_comm a y, real_inner_comm b y]
  ring

theorem sum_qc_rot {m : ℕ} (z : Fin m → E × E) :
    ∑ i, qc E ((z (finRotate m i)).1, (z i).2) - ∑ i, qc E ((z i).1, (z i).2) =
      -∑ i, ⟪(z i).2, (z (finRotate m i)).1 - (z i).1⟫ := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [qc_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_sub_distrib,
    Equiv.sum_comp (finRotate m) (fun i => ‖(z i).1‖ ^ 2)]
  ring

/-- The chain value at the base point is minus the cyclic sum. -/
theorem chainValue_eq {n : ℕ} (w : Fin (n + 1) → E × E) :
    rockafellarChainValue (qc E) w (w 0).1 =
      -∑ i, ⟪(w i).2, (w (finRotate (n + 1) i)).1 - (w i).1⟫ := by
  rw [← sum_qc_rot, rockafellarChainValue_def]
  have hrot : ∑ i, qc E ((w (finRotate (n + 1) i)).1, (w i).2) =
      qc E ((w 0).1, (w (Fin.last n)).2) + ∑ i : Fin n, qc E ((w i.succ).1, (w i.castSucc).2) := by
    rw [Fin.sum_univ_castSucc, add_comm]
    congr 1
    · rw [finRotate_last]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [finRotate_succ_apply, Fin.coeSucc_eq_succ]
  rw [hrot]

theorem chainValue_nonneg {S : Set (E × E)} (hS : CycMon S) {n : ℕ} {w : Fin (n + 1) → E × E}
    (hw : ∀ i, w i ∈ S) : 0 ≤ rockafellarChainValue (qc E) w (w 0).1 := by
  rw [chainValue_eq]
  exact neg_nonneg.2 (hS (n + 1) w hw)

theorem rockafellarPotential_self_of_cycMon {S : Set (E × E)} (hS : CycMon S) {p : E × E}
    (hp : p ∈ S) : rockafellarPotential (qc E) S p p.1 = 0 := by
  refine le_antisymm ?_ (le_rockafellarPotential fun n w hw0 hw => ?_)
  · simpa using rockafellarPotential_le_sub (c := qc E) hp p.1
  · have h := chainValue_nonneg hS hw
    rw [hw0] at h
    exact_mod_cast h

theorem subset_cSuperdifferential_of_cycMon {S : Set (E × E)} (hS : CycMon S) {p : E × E}
    (hp : p ∈ S) : S ⊆ cSuperdifferential (qc E) (rockafellarPotential (qc E) S p) := by
  set c := qc E
  set φ := rockafellarPotential c S p
  have hstep : ∀ q ∈ S, ∀ x : E, φ x ≤ φ q.1 + ((c (x, q.2) - c q : ℝ) : EReal) :=
    fun q hq x => rockafellarPotential_le_add hq x
  rintro ⟨x, y⟩ hxy
  have htop : φ x ≠ ⊤ := by
    refine ne_top_of_le_ne_top (EReal.coe_ne_top _) (rockafellarPotential_le_sub hp x)
  have hzero : φ p.1 = 0 := rockafellarPotential_self_of_cycMon hS hp
  have hbot : φ x ≠ ⊥ := by
    intro hbot
    have h := hstep (x, y) hxy p.1
    rw [hbot, hzero] at h
    simp at h
  set b : ℝ := (φ x).toReal
  have hb : φ x = (b : EReal) := (EReal.coe_toReal htop hbot).symm
  have hle : ∀ x' : E, ((c (x, y) : EReal)) - φ x ≤ (c (x', y) : EReal) - φ x' := by
    intro x'
    have h := hstep (x, y) hxy x'
    rw [hb] at h ⊢
    have hcoe : ((c (x', y) : EReal)) -
        ((b + (c (x', y) - c (x, y)) : ℝ) : EReal) = (c (x, y) : EReal) - (b : EReal) := by
      rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
      ring
    calc (c (x, y) : EReal) - (b : EReal)
        = ((c (x', y) : ℝ) : EReal) - ((b + (c (x', y) - c (x, y)) : ℝ) : EReal) := hcoe.symm
      _ ≤ ((c (x', y) : ℝ) : EReal) - φ x' := by
          refine EReal.sub_le_sub le_rfl ?_
          rw [EReal.coe_add]
          exact h
  have htrans : cTransform c φ y = (c (x, y) : EReal) - φ x :=
    le_antisymm (cTransform_le c φ x y) (le_cTransform fun x' => hle x')
  exact mem_cSuperdifferential_of_cTransform_eq hb htrans

/-- **Paper cyclical monotonicity implies Tau Ceti's** (all permutations), quadratic cost. -/
theorem isCyclicallyMonotone_of_cycMon {S : Set (E × E)} (hS : CycMon S) :
    IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · exact isCyclicallyMonotone_empty _
  · exact (isCyclicallyMonotone_cSuperdifferential (qc E) _).mono
      (subset_cSuperdifferential_of_cycMon hS hp)

end CM

section FD

variable {d : ℕ}

theorem memLp_id_of_mom2 {P : Measure (Euc d)} (h : Mom2 P ≠ ∞) : MemLp id 2 P :=
  memLp_of_mom2 measurable_id (by rwa [Measure.map_id])

/-- **Uniqueness of cyclically monotone couplings in `ℝ^d`** (Brenier, via Tau Ceti): for `P ≪ Leb`
with finite second moments, every coupling of `P` and `μ` concentrated on a Borel cyclically
monotone set is the graph plan of any `P`-a.e. cyclically monotone `F` pushing `P` to `μ`. -/
theorem brenierUniq_fd {P μ : Measure (Euc d)} [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    {F : Euc d → Euc d} (hac : P ≪ volume) (hP2 : Mom2 P ≠ ∞) (hμ2 : Mom2 μ ≠ ∞)
    (hF : Measurable F) (hmap : P.map F = μ) (hcm : IsCMMapAE P F) : BrenierUniq P μ F := by
  intro π _ hfst hsnd ⟨Γ, _, hΓ, hΓ0⟩
  have hPL := memLp_id_of_mom2 hP2
  have hμL := memLp_id_of_mom2 hμ2
  have hopt : IsOptimalCoupling (fun z : Euc d × Euc d => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      π P μ :=
    IsCoupling.isOptimalCoupling_of_isCyclicallyMonotone_norm_sub_sq_div_two ⟨hfst, hsnd⟩ hPL hμL
      (isCyclicallyMonotone_of_cycMon hΓ) ((measure_eq_zero_iff_ae_notMem.1 hΓ0).mono fun _ h => Set.notMem_compl_iff.1 h)
  obtain ⟨Γ', _, hΓ', hΓ'0⟩ := cmConc_graph hF hcm
  have hopt' : IsOptimalCoupling (fun z : Euc d × Euc d => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      (Graph P F) P μ :=
    IsCoupling.isOptimalCoupling_of_isCyclicallyMonotone_norm_sub_sq_div_two
      ⟨graph_fst hF, (graph_snd hF).trans hmap⟩ hPL hμL
      (isCyclicallyMonotone_of_cycMon hΓ') ((measure_eq_zero_iff_ae_notMem.1 hΓ'0).mono fun _ h => Set.notMem_compl_iff.1 h)
  exact hopt.unique (ρ := volume) hac hopt'
    (StatFormal.OTLimits.transportCost_quadCost_ne_top P μ hP2 hμ2)

/-- A probability law carried by a closed ball has a finite second moment. -/
theorem mom2_of_ball {μ : ProbabilityMeasure (Euc d)} {M : ℝ}
    (h : (μ : Measure (Euc d)) (Metric.closedBall 0 M)ᶜ = 0) : Mom2 (μ : Measure (Euc d)) ≠ ∞ :=
  mom2_ne_top_of_bounded h

end FD

theorem brenier_uniq_fd : Claims.brenier_uniq_fd := by
  intro d P μ F hac hP2 hμ2 hF hmap hcm
  exact brenierUniq_fd hac hP2 hμ2 hF hmap hcm

/-! ### A `lem:plan-stability-H` in `ℝ^d` -/

theorem plan_stab_fd_a : Claims.plan_stab_fd_a := by
  intro d P μ F M α ν π G hac hP2 hμM hF hmap hcm hα hν hfst hsnd hcmπ hG
  exact tendsto_of_cmConc (brenierUniq_fd hac hP2 (mom2_of_ball hμM) hF hmap hcm) hα hν hfst hsnd
    hcmπ hG

theorem plan_stab_fd_b : Claims.plan_stab_fd_b := by
  intro d P μ F M ν π hac hP2 hF hmap hcm hν hM hfst hsnd hcmπ
  obtain ⟨hμM, hmom⟩ := tendsto_mom2_of_bounded hν hM
  exact tendsto_L2_of_cmConc hF (brenierUniq_fd hac hP2 (mom2_of_ball hμM) hF hmap hcm) hν hmom
    (mom2_of_ball hμM) hfst hsnd hcmπ

theorem plan_stab_fd_b_map : Claims.plan_stab_fd_b_map := by
  intro d P μ F M ν T hac hP2 hF hmap hcm hν hM hT hTν hTcm
  exact tendsto_L2_map hF hT hTν hTcm fun π hfst hsnd hcmπ =>
    plan_stab_fd_b d P μ F M ν π hac hP2 hF hmap hcm hν hM hfst hsnd hcmπ

/-! ### R `lem:plan-w2` in `ℝ^d` -/

theorem plan_w2_fd_a : Claims.plan_w2_fd_a := by
  intro d P μ F α ν π G hac hP2 hμ2 hF hmap hcm hα hν hfst hsnd hcmπ hG
  exact tendsto_of_cmConc (brenierUniq_fd hac hP2 hμ2 hF hmap hcm) hα.1 hν.1 hfst hsnd hcmπ hG

theorem plan_w2_fd_b : Claims.plan_w2_fd_b := by
  intro d P μ F ν π hac hP2 hμ2 hF hmap hcm hν hfst hsnd hcmπ
  exact tendsto_L2_of_cmConc hF (brenierUniq_fd hac hP2 hμ2 hF hmap hcm) hν.1 hν.2 hμ2 hfst hsnd
    hcmπ

theorem plan_w2_fd_b_map : Claims.plan_w2_fd_b_map := by
  intro d P μ F ν T hac hP2 hμ2 hF hmap hcm hν hT hTν hTcm
  exact tendsto_L2_map hF hT hTν hTcm fun π hfst hsnd hcmπ =>
    plan_w2_fd_b d P μ F ν π hac hP2 hμ2 hF hmap hcm hν hfst hsnd hcmπ

end StatFormal.OTFD.WaveL1
