import StatFormal.Archive.Wave30v.RouteValue
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Route — wave 30v `boundary_delta_method`, `boundary_limit`, `boundary_conditional` (untrusted)

* Delta method: with `X_k = r_k(Z_k − z)`, `r_k(Φ(Z_k) − Φ(z)) = g_k(X_k)`, `g_k(x) = r_k(Φ(z + x/r_k) − Φ(z))`.
  `Φ'(X_k) ⇒ Φ'(𝕃)` (continuous mapping); `g_k → Φ'` uniformly on compacts (Hadamard + sequential compactness,
  by contradiction); the laws of `X_k` are tight (converse Prokhorov: a convergent sequence with its limit is
  compact in the space of probability measures on a Polish space), so `g_k(X_k) − Φ'(X_k) → 0` in probability;
  Slutsky (`tendstoInDistribution_of_tendstoInMeasure_sub`).
* Limit law: the delta method for `valueFn` at `(h_A, h_B)` (`boundary_value_hadamard`), with
  `valueFn(hA_k, hB_k) = dist(A_k, B_k)` (`boundary_dist_dual`) and `valueFn(h_A, h_B) = 0`.
* Conditional (as printed): `dist(s y, T) = s dist(y, T)` for a cone, continuous mapping and Slutsky; Moreau for
  `cl T`.
-/

set_option linter.style.longLine false

noncomputable section
open Set Filter Topology Metric MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace Pointwise ENNReal

namespace StatFormal.Wave30v

open StatFormal.TrimmedMMD.Unconditional (setDist)

/-- Hadamard directional differentiability ⇒ the rescaled difference quotients converge to `Φ'` uniformly on
compact sets. -/
lemma hadamard_unif_on_compact {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Φ Φ' : V → ℝ} {z : V}
    (hΦ' : Continuous Φ') (hH : HasHadamardDirDeriv Φ z Φ') {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hrt : Tendsto r atTop atTop) {C : Set V} (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ C, |r k * (Φ (z + (r k)⁻¹ • x) - Φ z) - Φ' x| < ε := by
  by_contra hne
  rw [Filter.not_eventually] at hne
  obtain ⟨φ, hφ, hP⟩ := Filter.extraction_of_frequently_atTop hne
  have hP' : ∀ n, ∃ x ∈ C, ε ≤ |r (φ n) * (Φ (z + (r (φ n))⁻¹ • x) - Φ z) - Φ' x| := by
    intro n; have := hP n; push_neg at this; exact this
  choose x hxC hx using hP'
  obtain ⟨a, -, ψ, hψ, hlim⟩ := hC.tendsto_subseq hxC
  have hrφψ : Tendsto (fun n => r (φ (ψ n))) atTop atTop := hrt.comp (hφ.comp hψ).tendsto_atTop
  have ht0 : Tendsto (fun n => (r (φ (ψ n)))⁻¹) atTop (𝓝 0) := hrφψ.inv_tendsto_atTop
  have h1 := hH a (fun n => (r (φ (ψ n)))⁻¹) (x ∘ ψ) (fun n => inv_pos.2 (hr _)) ht0 hlim
  have h2 : Tendsto (fun n => Φ' (x (ψ n))) atTop (𝓝 (Φ' a)) := (hΦ'.tendsto a).comp hlim
  have h3 := h1.sub h2
  rw [sub_self] at h3
  have h4 : Tendsto (fun n => r (φ (ψ n)) * (Φ (z + (r (φ (ψ n)))⁻¹ • x (ψ n)) - Φ z) - Φ' (x (ψ n)))
      atTop (𝓝 0) := by
    refine h3.congr fun n => ?_
    simp only [Function.comp, div_inv_eq_mul]
    ring
  obtain ⟨n, hn⟩ := ((h4.abs).eventually (gt_mem_nhds (by rw [abs_zero]; exact hε))).exists
  exact absurd (hx (ψ n)) (not_le.2 hn)

/-- (Route-only, moved from the draft statements by the wave-30v critic: a general library fact with no printed
label.) The delta method for Hadamard directionally differentiable maps (Shapiro 1991; Dümbgen 1993; Fang–Santos 2019
Thm 2.1): on a complete separable normed space `V`, if `Φ` (continuous) is Hadamard directionally differentiable
at `z` with continuous derivative `Φ'`, `r_k → ∞`, and `r_k (Z_k − z) ⇒ 𝕃`, then
`r_k (Φ(Z_k) − Φ(z)) ⇒ Φ'(𝕃)`. -/
theorem boundary_delta_method :
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [TopologicalSpace.SeparableSpace V]
    [MeasurableSpace V] [BorelSpace V] (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (μ' : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (Φ Φ' : V → ℝ) (z : V) (Z : ℕ → Ω → V) (𝕃 : Ω' → V) (r : ℕ → ℝ),
    Continuous Φ → Continuous Φ' → HasHadamardDirDeriv Φ z Φ' → (∀ k, 0 < r k) → Tendsto r atTop atTop →
    TendstoInDistribution (fun k ω => r k • (Z k ω - z)) atTop 𝕃 (fun _ => μ) μ' →
      TendstoInDistribution (fun k ω => r k * (Φ (Z k ω) - Φ z)) atTop (fun ω => Φ' (𝕃 ω)) (fun _ => μ) μ' := by
  intro V _ _ _ _ _ _ Ω Ω' _ _ μ μ' _ _ Φ Φ' z Z 𝕃 r hΦ hΦ' hH hr hrt hX
  haveI : SecondCountableTopology V := UniformSpace.secondCountable_of_separable V
  set X : ℕ → Ω → V := fun k ω => r k • (Z k ω - z) with hXdef
  have hXae : ∀ k, AEMeasurable (X k) μ := hX.forall_aemeasurable
  have hZrep : ∀ k ω, Z k ω = z + (r k)⁻¹ • X k ω := by
    intro k ω
    simp only [X, smul_smul, inv_mul_cancel₀ (hr k).ne', one_smul, add_sub_cancel]
  set g : ℕ → V → ℝ := fun k x => r k * (Φ (z + (r k)⁻¹ • x) - Φ z) with hg
  have hY : ∀ k, (fun ω => r k * (Φ (Z k ω) - Φ z)) = g k ∘ X k := by
    intro k; funext ω; simp only [g, Function.comp, ← hZrep]
  have hgc : ∀ k, Continuous (g k) := fun k =>
    continuous_const.mul ((hΦ.comp (continuous_const.add (continuous_const.smul continuous_id))).sub continuous_const)
  have hW := hX.continuous_comp hΦ'
  refine tendstoInDistribution_of_tendstoInMeasure_sub (fun k ω => r k * (Φ (Z k ω) - Φ z)) (Φ' ∘ 𝕃) hW ?_ ?_
  · rw [tendstoInMeasure_iff_dist]
    intro ε hε
    rw [ENNReal.tendsto_atTop_zero]
    intro η hη
    -- tightness of the laws of `X_k`
    obtain ⟨C, hC, hCη⟩ : ∃ C, IsCompact C ∧ ∀ k, (μ.map (X k)) Cᶜ ≤ η := by
      let ν : ℕ → ProbabilityMeasure V := fun k => ⟨μ.map (X k), inferInstance⟩
      let ν₀ : ProbabilityMeasure V := ⟨μ'.map 𝕃, inferInstance⟩
      have hν : Tendsto ν atTop (𝓝 ν₀) := hX.tendsto
      have hcomp : IsCompact (closure (insert ν₀ (range ν))) := by
        have := hν.isCompact_insert_range
        rwa [this.isClosed.closure_eq]
      have htight := isTightMeasureSet_of_isCompact_closure hcomp
      rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
      obtain ⟨C, hC, hCη⟩ := htight η hη
      exact ⟨C, hC, fun k => hCη _ ⟨ν k, mem_insert_of_mem _ ⟨k, rfl⟩, rfl⟩⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hadamard_unif_on_compact hΦ' hH hr hrt hC hε)
    refine ⟨N, fun k hk => ?_⟩
    calc μ {ω | ε ≤ dist (((fun k ω => r k * (Φ (Z k ω) - Φ z)) - fun n => Φ' ∘ X n) k ω) ((0 : Ω → ℝ) ω)}
        ≤ μ (X k ⁻¹' Cᶜ) := by
          refine measure_mono fun ω hω => ?_
          simp only [mem_ofPred_eq, Pi.sub_apply, Pi.zero_apply, Real.dist_eq, sub_zero, Function.comp] at hω
          intro hmem
          have := hN k hk (X k ω) hmem
          rw [hZrep k ω] at hω
          exact absurd hω (not_le.2 this)
      _ = (μ.map (X k)) Cᶜ :=
          (Measure.map_apply_of_aemeasurable (hXae k) hC.isClosed.measurableSet.compl).symm
      _ ≤ η := hCη k
  · intro k
    rw [hY k]
    exact (hgc k).measurable.comp_aemeasurable (hXae k)

/-- (Route-only, moved from the draft statements by the wave-30v critic: a general library fact with no printed
label.) The abstract sup-functional delta method (the deterministic-plus-CMT core of "Theorem A" of the wave-30v
report): for a compact metric index set `Θ` and random continuous processes `Γ_k` with `r_k(Γ_k − Γ) ⇒ 𝕃` in
`C(Θ, ℝ)` (a HYPOTHESIS), `r_k → ∞`, `r_k(sup Γ_k − sup Γ) ⇒ sup_{θ ∈ argmax Γ} 𝕃(θ)`. Theorem A itself (the
UNCONDITIONAL limit of `√N D̂` at the contact level) is NOT formalised: it additionally needs the `lem:cvar` lift
`D̂ = sup_Θ Γ_{P_n,Q_m}` with `Θ = Ball × [−κ, κ]²`, `Γ_{μ,ν}(g, t, s) = −t − β μ(⟨−g, φ⟩ − t)_+ − s − β ν(⟨g, φ⟩ − s)_+`,
and the Donsker CLT for that class in `C(Θ)`; both are report-side arguments only. -/
theorem boundary_sup_limit :
  ∀ (Θ : Type) [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    [MeasurableSpace C(Θ, ℝ)] [BorelSpace C(Θ, ℝ)]
    (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω) (μ' : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (Γ : C(Θ, ℝ)) (Γk : ℕ → Ω → C(Θ, ℝ)) (𝕃 : Ω' → C(Θ, ℝ))
    (r : ℕ → ℝ), (∀ k, 0 < r k) → Tendsto r atTop atTop →
    TendstoInDistribution (fun k ω => r k • (Γk k ω - Γ)) atTop 𝕃 (fun _ => μ) μ' →
      TendstoInDistribution (fun k ω => r k * (supFun (Γk k ω) - supFun Γ)) atTop (fun ω => supDeriv Γ (𝕃 ω))
        (fun _ => μ) μ' := by
  intro Θ _ _ _ _ _ Ω Ω' _ _ μ μ' _ _ Γ Γk 𝕃 r hr hrt hconv
  exact boundary_delta_method C(Θ, ℝ) Ω Ω' μ μ' supFun (supDeriv Γ) Γ Γk 𝕃 r lipschitz_supFun.continuous
    (lipschitz_supDeriv Γ).continuous (boundary_sup_hadamard Θ Γ) hr hrt hconv

theorem boundary_limit : Claims.boundary_limit := by
  intro E _ _ _ _ _ Ω Ω' _ _ μ μ' _ _ A B hA hB Ak Bk hAk hBk H r hAne hBne hAc hBc hAcv hBcv hAB hAeq
    hBeq hk hAkeq hBkeq hr hrt hconv
  have hAb := hAc.isBounded
  have hBb := hBc.isBounded
  obtain ⟨hsup, hHad⟩ := boundary_value_hadamard E A B hA hB hAne hBne hAb hBb hAB hAeq hBeq
  have hd := boundary_delta_method (C(Ball E, ℝ) × C(Ball E, ℝ)) Ω Ω' μ μ' valueFn (valueDeriv A B) (hA, hB)
    (fun k ω => (hAk k ω, hBk k ω)) H r continuous_valueFn
    (continuous_valueDeriv hAb hBb hAB hAeq hBeq) hHad hr hrt hconv
  have heq : (fun k ω => r k * setDist (Ak k ω) (Bk k ω)) =
      fun k ω => r k * (valueFn (hAk k ω, hBk k ω) - valueFn (hA, hB)) := by
    funext k ω
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hk k ω
    rw [hsup, sub_zero, boundary_dist_dual E (Ak k ω) (Bk k ω) (hAk k ω) (hBk k ω) h1 h2 h3 h4 h5 h6
      (hAkeq k ω) (hBkeq k ω)]
  rw [heq]
  exact hd

theorem boundary_limit_linear : Claims.boundary_limit_linear := by
  intro E _ _ _ _ _ Ω Ω' _ _ μ μ' _ _ A B hA hB Ak Bk hAk hBk GA GB r hAne hBne hAc hBc hAcv hBcv hAB hAeq
    hBeq hk hAkeq hBkeq hr hrt hconv
  have h := boundary_limit E Ω Ω' μ μ' A B hA hB Ak Bk hAk hBk _ r hAne hBne hAc hBc hAcv hBcv hAB hAeq hBeq hk
    hAkeq hBkeq hr hrt hconv
  have heq : (fun ω => valueDeriv A B (linDir (GA ω), linDir (GB ω))) =
      fun ω => infDist (GA ω - GB ω) (closure (coneHull (B - A))) :=
    funext fun ω => boundary_translation E A B hAne hBne hAcv hBcv hAB (GA ω) (GB ω)
  rw [heq] at h
  exact h

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma polarSet_closure (T : Set E) : polarSet (closure T) = polarSet T := by
  ext g
  constructor
  · intro hg s hs; exact hg s (subset_closure hs)
  · intro hg v hv
    have hcl : IsClosed {v : E | ⟪g, v⟫ ≤ 0} := isClosed_le (continuous_const.inner continuous_id) continuous_const
    exact closure_minimal (fun s hs => hg s hs) hcl hv

end

theorem boundary_conditional : Claims.boundary_conditional := by
  intro E _ _ _ _ _ Ω Ω' _ _ μ μ' _ _ T u v D X s hTne hcone hs hD hB2 hB3
  have hhom : ∀ c : ℝ, 0 < c → ∀ y : E, infDist (c • y) T = c * infDist y T := by
    intro c hc y
    have hcT : c • T = T := by
      ext w; constructor
      · rintro ⟨w', hw', rfl⟩; exact hcone c hc w' hw'
      · intro hw
        exact ⟨c⁻¹ • w, hcone _ (inv_pos.2 hc) w hw, by simp [smul_smul, mul_inv_cancel₀ hc.ne']⟩
    have := infDist_smul₀ (𝕜 := ℝ) hc.ne' T y
    rwa [hcT, Real.norm_eq_abs, abs_of_pos hc] at this
  refine ⟨?_, ?_⟩
  · have hW := hB2.continuous_comp (continuous_infDist_pt T)
    simp_rw [infDist_closure]
    refine tendstoInDistribution_of_tendstoInMeasure_sub (fun k ω => s k * D k ω) _ hW ?_ ?_
    · have : (fun k ω => s k * D k ω) - (fun n => (fun x => infDist x T) ∘ fun ω => s n • (u n ω - v n ω)) =
          fun k ω => s k * (D k ω - infDist (u k ω - v k ω) T) := by
        funext k ω
        simp only [Pi.sub_apply, Function.comp]
        rw [hhom _ (hs k)]
        ring
      rw [this]; exact hB3
    · intro k; exact (hD k).const_mul _
  · intro hcv x
    obtain ⟨w, hw⟩ := hTne
    have h0 : (0 : E) ∈ closure T := by
      have ht : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • w) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const w
        rwa [zero_smul] at this
      exact mem_closure_of_tendsto ht (Eventually.of_forall fun n => hcone _ (by positivity) w hw)
    have hconeK : ∀ c : ℝ, 0 ≤ c → ∀ w ∈ closure T, c • w ∈ closure T := by
      intro c hc w' hw'
      rcases hc.lt_or_eq with hc | hc
      · exact map_mem_closure (f := fun y : E => c • y) (continuous_const_smul c) hw'
          (fun w'' hw'' => hcone c hc w'' hw'')
      · rw [← hc, zero_smul]; exact h0
    rw [← boundary_polar_infDist E (closure T) ⟨w, subset_closure hw⟩ isClosed_closure hcv.closure hconeK x,
      polarSet_closure]

end StatFormal.Wave30v
