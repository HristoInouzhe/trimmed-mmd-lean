import StatFormal.Archive.Wave23a.Statements

/-!
# Route — ICL `thm:score`, deterministic argmin core (untrusted)

Compactness gives the minima; uniform closeness `|J_n − J| ≤ δ` gives `|inf J_n − inf J| ≤ δ`; at a cluster point
`θ` with `J θ > J θ' + 3η`, continuity and the near-minimality of `θ̂_n` give a contradiction once
`ε_n + 2δ_n < η`.
-/

noncomputable section
open Set Filter Topology

namespace StatFormal.Wave23a

theorem score_argmin : Claims.score_argmin := by
  intro Θ _ _ _ J Jn θn εn hJ hunif hε hmin
  have hcomp : IsCompact (univ : Set Θ) := isCompact_univ
  -- minima
  obtain ⟨θs, -, hθs⟩ := hcomp.exists_isMinOn univ_nonempty hJ.continuousOn
  have hθs' : ∀ θ', J θs ≤ J θ' := fun θ' => hθs (mem_univ θ')
  have hJbdd : BddBelow (range J) := ⟨J θs, by rintro _ ⟨θ, rfl⟩; exact hθs' θ⟩
  have hinfJ : (⨅ θ, J θ) = J θs :=
    le_antisymm (ciInf_le hJbdd θs) (le_ciInf hθs')
  have hunif' : ∀ δ > 0, ∀ᶠ n in atTop, ∀ θ, |Jn n θ - J θ| < δ := by
    intro δ hδ
    have := Metric.tendstoUniformly_iff.1 hunif δ hδ
    filter_upwards [this] with n hn θ
    have := hn θ
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this
  refine ⟨⟨θs, hθs'⟩, fun n hc => ?_, ?_, ?_⟩
  · obtain ⟨θ, -, hθ⟩ := hcomp.exists_isMinOn univ_nonempty hc.continuousOn
    exact ⟨θ, fun θ' => hθ (mem_univ θ')⟩
  · rw [hinfJ, Metric.tendsto_atTop']
    intro δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif' (δ / 2) (by linarith))
    refine ⟨N, fun n hn => ?_⟩
    have hb := hN n hn.le
    have hbdd : BddBelow (range (Jn n)) := by
      refine ⟨J θs - δ / 2, ?_⟩
      rintro _ ⟨θ, rfl⟩
      have := hb θ
      have := hθs' θ
      rw [abs_lt] at *
      linarith [(hb θ)]
    have hlo : J θs - δ / 2 ≤ ⨅ θ, Jn n θ := by
      refine le_ciInf fun θ => ?_
      have h1 := (abs_lt.1 (hb θ)).1
      linarith [hθs' θ]
    have hhi : (⨅ θ, Jn n θ) ≤ J θs + δ / 2 := by
      refine (ciInf_le hbdd θs).trans ?_
      have h1 := (abs_lt.1 (hb θs)).2
      linarith
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  · intro θ hθ θ'
    by_contra hlt
    push_neg at hlt
    set η := (J θ - J θ') / 3 with hη
    have hηpos : 0 < η := by rw [hη]; linarith
    have hU : {z | J θ - η < J z} ∈ 𝓝 θ :=
      (isOpen_lt continuous_const hJ).mem_nhds (by simp only [mem_setOf_eq]; linarith)
    have hfreq := (mapClusterPt_iff_frequently.1 hθ) _ hU
    have hev1 := hunif' (η / 3) (by linarith)
    have hev2 : ∀ᶠ n in atTop, εn n < η / 3 := (hε.eventually (gt_mem_nhds (by linarith)))
    obtain ⟨n, hn1, hn2, hn3⟩ := (hfreq.and_eventually (hev1.and hev2)).exists
    have hA := hmin n θ'
    have hB := (abs_lt.1 (hn2 (θn n))).1
    have hC := (abs_lt.1 (hn2 θ')).2
    simp only [mem_setOf_eq] at hn1
    linarith

end StatFormal.Wave23a
