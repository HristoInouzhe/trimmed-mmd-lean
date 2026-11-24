import StatFormal.Archive.Wave30v.Statements

/-!
# Route — wave 30v `boundary_sup_hadamard` (untrusted)

The sup functional on `C(Θ, ℝ)`, `Θ` compact: lower bound from a maximiser `θ₀` of `h` on `argmax z`
(`sup(z + t k) ≥ z θ₀ + t k θ₀`); upper bound by splitting `Θ` into the open set `{h < M + ε}` (where
`z ≤ sup z` and `k ≤ h + ‖k − h‖`) and its compact complement `F`, on which `z ≤ sup z − δ` for some `δ > 0`
(`F` misses `argmax z`), so that its contribution is eventually below the bound.
-/

set_option linter.style.longLine false

noncomputable section
open Set Filter Topology

namespace StatFormal.Wave30v

section SupDefs
variable {Θ : Type*} [TopologicalSpace Θ]

/-- The set of maximisers of `z`. -/
def argmaxSet (z : C(Θ, ℝ)) : Set Θ := {θ | z θ = supFun z}

/-- The directional derivative of the sup functional at `z` in the direction `h`: `sup_{θ ∈ argmax z} h(θ)`. -/
def supDeriv (z h : C(Θ, ℝ)) : ℝ := sSup (h '' argmaxSet z)

end SupDefs

section
variable {Θ : Type*} [TopologicalSpace Θ] [CompactSpace Θ]

lemma bddAbove_range_cm (z : C(Θ, ℝ)) : BddAbove (range z) := (isCompact_range z.continuous).bddAbove

lemma le_supFun (z : C(Θ, ℝ)) (θ : Θ) : z θ ≤ supFun z := le_csSup (bddAbove_range_cm z) ⟨θ, rfl⟩

lemma supFun_le [Nonempty Θ] {z : C(Θ, ℝ)} {c : ℝ} (h : ∀ θ, z θ ≤ c) : supFun z ≤ c :=
  csSup_le (range_nonempty _) (by rintro _ ⟨θ, rfl⟩; exact h θ)

lemma exists_eq_supFun [Nonempty Θ] (z : C(Θ, ℝ)) : ∃ θ, z θ = supFun z := by
  obtain ⟨θ, hθ⟩ := (isCompact_range z.continuous).sSup_mem (range_nonempty _)
  exact ⟨θ, hθ⟩

lemma isCompact_argmaxSet (z : C(Θ, ℝ)) : IsCompact (argmaxSet z) :=
  (isClosed_eq z.continuous continuous_const).isCompact

lemma argmaxSet_nonempty [Nonempty Θ] (z : C(Θ, ℝ)) : (argmaxSet z).Nonempty := exists_eq_supFun z

lemma le_supDeriv {z h : C(Θ, ℝ)} {θ : Θ} (hθ : θ ∈ argmaxSet z) : h θ ≤ supDeriv z h :=
  le_csSup ((isCompact_argmaxSet z).image h.continuous).bddAbove ⟨θ, hθ, rfl⟩

lemma exists_supDeriv [Nonempty Θ] (z h : C(Θ, ℝ)) : ∃ θ ∈ argmaxSet z, h θ = supDeriv z h := by
  obtain ⟨θ, hθ, he⟩ :=
    ((isCompact_argmaxSet z).image h.continuous).sSup_mem ((argmaxSet_nonempty z).image _)
  exact ⟨θ, hθ, he⟩

lemma supDeriv_le [Nonempty Θ] {z h : C(Θ, ℝ)} {c : ℝ} (hc : ∀ θ ∈ argmaxSet z, h θ ≤ c) :
    supDeriv z h ≤ c :=
  csSup_le ((argmaxSet_nonempty z).image _) (by rintro _ ⟨θ, hθ, rfl⟩; exact hc θ hθ)

lemma apply_le_add_norm (k h : C(Θ, ℝ)) (θ : Θ) : k θ ≤ h θ + ‖k - h‖ := by
  have := ContinuousMap.norm_coe_le_norm (k - h) θ
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs] at this
  linarith [le_abs_self (k θ - h θ)]

lemma apply_le_norm (k : C(Θ, ℝ)) (θ : Θ) : k θ ≤ ‖k‖ := by
  have := ContinuousMap.norm_coe_le_norm k θ
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

/-- `|sup f − sup g| ≤ ‖f − g‖`. -/
lemma supFun_sub_le [Nonempty Θ] (f g : C(Θ, ℝ)) : supFun f ≤ supFun g + ‖f - g‖ :=
  supFun_le fun θ => by linarith [apply_le_add_norm f g θ, le_supFun g θ]

lemma lipschitz_supFun [Nonempty Θ] : LipschitzWith 1 (supFun : C(Θ, ℝ) → ℝ) := by
  refine LipschitzWith.of_le_add_mul 1 fun f g => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm]
  exact supFun_sub_le f g

lemma supDeriv_sub_le [Nonempty Θ] (z f g : C(Θ, ℝ)) : supDeriv z f ≤ supDeriv z g + ‖f - g‖ :=
  supDeriv_le fun θ hθ => by linarith [apply_le_add_norm f g θ, le_supDeriv (h := g) hθ]

lemma lipschitz_supDeriv [Nonempty Θ] (z : C(Θ, ℝ)) : LipschitzWith 1 (supDeriv z) := by
  refine LipschitzWith.of_le_add_mul 1 fun f g => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm]
  exact supDeriv_sub_le z f g

end

/-- (Route-only, moved from the draft statements by the wave-30v critic: a general library fact with no printed
label.) The sup functional is Hadamard directionally differentiable (Danskin; Römisch 2006; Cárcamo–Cuevas–Rodríguez
2020 Thm 2.1): on `C(Θ, ℝ)`, `Θ` compact and nonempty, at every `z`, with derivative
`h ↦ sup_{θ ∈ argmax z} h(θ)`. -/
theorem boundary_sup_hadamard :
  ∀ (Θ : Type) [TopologicalSpace Θ] [CompactSpace Θ] [Nonempty Θ] (z : C(Θ, ℝ)),
    HasHadamardDirDeriv supFun z (supDeriv z) := by
  intro Θ _ _ _ z h t k ht ht0 hk
  obtain ⟨θ0, hθ0, hM⟩ := exists_supDeriv z h
  set M := supDeriv z h with hMdef
  -- lower bound
  have hlow : ∀ n, k n θ0 ≤ (supFun (z + t n • k n) - supFun z) / t n := by
    intro n
    rw [le_div_iff₀ (ht n)]
    have h1 := le_supFun (z + t n • k n) θ0
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul] at h1
    have h2 : z θ0 = supFun z := hθ0
    nlinarith
  have hkθ : Tendsto (fun n => k n θ0) atTop (𝓝 (h θ0)) :=
    ((continuous_eval_const θ0).tendsto h).comp hk
  -- upper bound
  have hup : ∀ ε > 0, ∀ᶠ n in atTop, (supFun (z + t n • k n) - supFun z) / t n ≤ M + ε + ‖k n - h‖ := by
    intro ε hε
    set F := {θ | M + ε ≤ h θ} with hF
    have hFc : IsCompact F := (isClosed_le continuous_const h.continuous).isCompact
    obtain ⟨δ, hδ, hFδ⟩ : ∃ δ > 0, ∀ θ ∈ F, z θ ≤ supFun z - δ := by
      rcases F.eq_empty_or_nonempty with hFe | hFne
      · exact ⟨1, one_pos, by simp [hFe]⟩
      · obtain ⟨θ1, hθ1F, hmax⟩ := hFc.exists_isMaxOn hFne z.continuous.continuousOn
        have hlt : z θ1 < supFun z := by
          refine lt_of_le_of_ne (le_supFun z θ1) (fun heq => ?_)
          have h3 := le_supDeriv (h := h) (show θ1 ∈ argmaxSet z from heq)
          have h4 : M + ε ≤ h θ1 := hθ1F
          linarith
        refine ⟨supFun z - z θ1, by linarith, fun θ hθ => ?_⟩
        have := hmax hθ
        simp only [mem_ofPred_eq] at this
        linarith
    have hev : ∀ᶠ n in atTop, t n * (‖k n‖ + |M|) < δ := by
      have : Tendsto (fun n => t n * (‖k n‖ + |M|)) atTop (𝓝 (0 * (‖h‖ + |M|))) :=
        ht0.mul (hk.norm.add_const _)
      rw [zero_mul] at this
      exact this.eventually (gt_mem_nhds hδ)
    filter_upwards [hev] with n hn
    rw [div_le_iff₀ (ht n)]
    have hb : supFun (z + t n • k n) ≤ supFun z + (M + ε + ‖k n - h‖) * t n := by
      apply supFun_le
      intro θ
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
      have hkh := apply_le_add_norm (k n) h θ
      have htn := ht n
      have hnn := norm_nonneg (k n - h)
      by_cases hθ : θ ∈ F
      · have h1 := hFδ θ hθ
        have h2 : t n * k n θ ≤ t n * ‖k n‖ := mul_le_mul_of_nonneg_left (apply_le_norm _ _) htn.le
        have h3 : -(t n * |M|) ≤ t n * M := by nlinarith [neg_abs_le M]
        have h4 : 0 ≤ t n * (ε + ‖k n - h‖) := by positivity
        nlinarith
      · have h1 := le_supFun z θ
        have h5 : h θ < M + ε := lt_of_not_ge hθ
        have h2 : t n * k n θ ≤ t n * (M + ε + ‖k n - h‖) :=
          mul_le_mul_of_nonneg_left (by linarith) htn.le
        nlinarith
    linarith
  -- combine
  have hMθ : M = h θ0 := hM.symm
  rw [hMθ]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hkθ.eventually (lt_mem_nhds ha)] with n hn
    exact lt_of_lt_of_le hn (hlow n)
  · have hε : 0 < (b - h θ0) / 3 := by linarith
    have hk' : ∀ᶠ n in atTop, ‖k n - h‖ < (b - h θ0) / 3 := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hk).eventually (gt_mem_nhds hε)
      exact this
    filter_upwards [hup _ hε, hk'] with n h1 h2
    rw [hMθ] at h1
    linarith

end StatFormal.Wave30v
