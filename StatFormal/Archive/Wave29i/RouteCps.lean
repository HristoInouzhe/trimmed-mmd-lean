import StatFormal.Archive.Wave29i.Statements
import StatFormal.Archive.ICL.CPS
import StatFormal.Archive.WaveP1d.RouteCPS
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Route — ICL `prop:cps-gradient`: the Frank–Wolfe gap with coverage; the infinite gap with `λ_KL > 0` (untrusted)

* `π_k = Σ_{S ∋ k} Π_w(S) = G(w; 1{k ∈ ·})`, so the certified `cps_gradient` differentiates the inclusion
  probabilities: `∂π_k/∂w_ℓ = e_{M−1}(w_{−ℓ})/e_M(w) (V_ℓ(1_k) − π_k)`; at the fixed prompt (certified WaveP1d
  `cps_fixed_prompt`, applied to the indicator losses) this is `0` for `ℓ ∈ P` and, for `ℓ ∉ P`, `M²` at `k = ℓ`,
  `−M` at `k ∈ P`, `0` otherwise.
* The coverage `Φ_m(π/M)` is differentiated by the chain rule (`log` of coverages `> 0`); its `w_ℓ`-derivative is
  `Σ_k c_k ∂π_k/∂w_ℓ /M = M(c_ℓ − c̄_P)` off `P` and `0` on `P`. The mean risk is `G(w; L̄)` with `L̄` the average of
  the per-query losses, and the risk part is the certified fixed-prompt formula.
* Gap: `⟨w, g⟩ = 0` (`g = 0` on `P`, `w = 0` off `P`), so the gap is `−min_ℓ g_ℓ`.
* `λ_KL > 0`, `w_ℓ = 0`: `KL(w + t e_ℓ | u_n) − KL(w | u_n) = t log(nt)`, so the difference quotient is a convergent
  term plus `λ_KL log(nt) → −∞`.
-/

set_option linter.style.longLine false

noncomputable section
open Finset Filter Topology

namespace StatFormal.Wave29i

open StatFormal.ICL

section Aux
variable {Z : Type*} {n M m : ℕ}

/-- The indicator loss `S ↦ 1{k ∈ S}`. -/
def indL (k : Fin n) : Finset (Fin n) → ℝ := fun S => if k ∈ S then 1 else 0

lemma incl_eq_Grisk (w : Fin n → ℝ) (M : ℕ) (k : Fin n) : incl w M k = Grisk w M (indL k) := by
  unfold incl Grisk indL
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs <;> simp

lemma Grisk_mean (w : Fin n → ℝ) (M : ℕ) (L : Fin m → Finset (Fin n) → ℝ) :
    (1 / (m : ℝ)) * ∑ i, Grisk w M (L i) = Grisk w M (fun S => (1 / (m : ℝ)) * ∑ i, L i S) := by
  unfold Grisk
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun i _ => by ring

/-- `jSwor` splits into the mean risk, the coverage and the relative entropy. -/
lemma jSwor_split (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (z : Fin n → Z) (zt : Fin m → Z) (lcov lKL : ℝ)
    (w : Fin n → ℝ) :
    StatFormal.Wave11b.jSwor L K z zt lcov lKL w =
      Grisk w M (fun S => (1 / (m : ℝ)) * ∑ i, StatFormal.Wave11b.lossSub L (zt i) z S) +
        lcov * cpsPhiM K z zt (fun l => incl w M l / M) + lKL * StatFormal.ICL.Diag.klUnif n w := by
  unfold StatFormal.Wave11b.jSwor cpsPhiM
  rw [Grisk_mean]

lemma hasDerivAt_update_apply (x : Fin n → ℝ) (k l : Fin n) (y : ℝ) :
    HasDerivAt (fun t => Function.update x k t l) (if l = k then 1 else 0) y := by
  by_cases h : l = k
  · subst h
    simp only [Function.update_self, if_true]
    exact hasDerivAt_id y
  · simp only [Function.update_of_ne h, if_neg h]
    exact hasDerivAt_const _ _

/-- The coverages at the one-slot marginal are positive. -/
lemma cov_pos {w : Fin n → ℝ} (hM : 1 ≤ M) (hD : InDeltaM w M) {K : Z → Z → ℝ} (hK : ∀ x y, 0 < K x y)
    (z : Fin n → Z) (x : Z) : 0 < ∑ l, incl w M l / M * K x (z l) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hnn : ∀ l, 0 ≤ incl w M l := fun l =>
    Finset.sum_nonneg fun S hS => (cps_wellPosed n M w hD).2.1 S (Finset.mem_filter.1 hS).1
  have hsum := (cps_incl n M w hM hD).2
  have hex : ∃ l, 0 < incl w M l := by
    by_contra h
    push_neg at h
    have : ∑ l, incl w M l ≤ 0 := Finset.sum_nonpos fun l _ => h l
    linarith
  obtain ⟨l0, hl0⟩ := hex
  refine Finset.sum_pos' (fun l _ => mul_nonneg (div_nonneg (hnn l) hM'.le) (hK _ _).le)
    ⟨l0, Finset.mem_univ _, mul_pos (div_pos hl0 hM') (hK _ _)⟩

/-- The `w_ℓ`-derivative of an inclusion probability at `w ∈ Δ^(M)`. -/
def dIncl (w : Fin n → ℝ) (M : ℕ) (ℓ k : Fin n) : ℝ :=
  esym w (univ.erase ℓ) (M - 1) / esym w univ M * (Vrisk w M (indL k) ℓ - Grisk w M (indL k))

lemma hasDerivAt_incl {w : Fin n → ℝ} (hM : 1 ≤ M) (hD : InDeltaM w M) (ℓ k : Fin n) :
    HasDerivAt (fun t => incl (Function.update w ℓ t) M k) (dIncl w M ℓ k) (w ℓ) := by
  have h := (cps_gradient n M w (indL k) hM hD).1 ℓ
  simp_rw [incl_eq_Grisk]
  exact h

/-- The `w_ℓ`-derivative of the coverage term `Φ_m(π/M)` at `w ∈ Δ^(M)`. -/
lemma hasDerivAt_cov {w : Fin n → ℝ} (hM : 1 ≤ M) (hD : InDeltaM w M) {K : Z → Z → ℝ}
    (hK : ∀ x y, 0 < K x y) (z : Fin n → Z) (zt : Fin m → Z) (ℓ : Fin n) :
    HasDerivAt (fun t => cpsPhiM K z zt (fun l => incl (Function.update w ℓ t) M l / M))
      (-(1 / (m : ℝ)) * ∑ i, (∑ l, dIncl w M ℓ l / M * K (zt i) (z l)) /
        (∑ l, incl w M l / M * K (zt i) (z l))) (w ℓ) := by
  unfold cpsPhiM
  refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun i _ => ?_)
  have hin : HasDerivAt (fun t => ∑ l, incl (Function.update w ℓ t) M l / M * K (zt i) (z l))
      (∑ l, dIncl w M ℓ l / M * K (zt i) (z l)) (w ℓ) :=
    HasDerivAt.fun_sum fun l _ => ((hasDerivAt_incl hM hD ℓ l).div_const _).mul_const _
  have hval : (∑ l, incl (Function.update w ℓ (w ℓ)) M l / M * K (zt i) (z l)) =
      ∑ l, incl w M l / M * K (zt i) (z l) := by
    rw [Function.update_eq_self]
  have hpos := cov_pos hM hD hK z (zt i)
  have := hin.log (by rw [hval]; exact hpos.ne')
  rw [hval] at this
  exact this

end Aux

/-! ### The fixed prompt -/

section Fixed
variable {Z : Type*} {n M m : ℕ}

lemma fixed_facts (P : Finset (Fin n)) (hM : 1 ≤ M) (hP : P.card = M) :
    let w : Fin n → ℝ := fun j => if j ∈ P then 1 / (M : ℝ) else 0
    InDeltaM w M ∧ (∀ k, incl w M k = if k ∈ P then 1 else 0) ∧
      (∀ ℓ ∈ P, ∀ k, dIncl w M ℓ k = 0) ∧
      (∀ ℓ ∉ P, ∀ k, dIncl w M ℓ k = if k = ℓ then (M : ℝ) ^ 2 else if k ∈ P then -(M : ℝ) else 0) := by
  intro w
  have hf := fun k => StatFormal.WaveP1d.cps_fixed_prompt n M P (indL k) hM hP
  have hn : 0 < n := by
    have := Finset.card_le_univ P
    simp only [Fintype.card_fin] at this
    omega
  have hD : InDeltaM w M := (hf ⟨0, hn⟩).1
  refine ⟨hD, fun k => ?_, fun ℓ hℓ k => (hf k).2.2.2.1 ℓ hℓ, fun ℓ hℓ k => ?_⟩
  · rw [incl_eq_Grisk, (hf k).2.1]; rfl
  · obtain ⟨-, hG, -, -, hout, -⟩ := hf k
    obtain ⟨hratio, hV⟩ := hout ℓ hℓ
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    unfold dIncl
    rw [hratio, hV, hG]
    have hsum : ∑ k' ∈ P, indL k (insert ℓ (P.erase k')) =
        if k = ℓ then (M : ℝ) else if k ∈ P then ((M : ℝ) - 1) else 0 := by
      unfold indL
      by_cases hkl : k = ℓ
      · subst hkl
        simp [hP]
      · by_cases hkP : k ∈ P
        · have : ∀ k' ∈ P, (if k ∈ insert ℓ (P.erase k') then (1 : ℝ) else 0) = if k' ∈ P.erase k then 1 else 0 := by
            intro k' hk'
            simp only [mem_insert, mem_erase, hkl, false_or]
            by_cases h : k' = k
            · subst h; simp
            · simp [h, Ne.symm h, hkP, hk']
          rw [Finset.sum_congr rfl this, Finset.sum_ite_mem, Finset.inter_eq_right.2 (Finset.erase_subset k P),
            Finset.sum_const, card_erase_of_mem hkP, hP, nsmul_eq_mul, mul_one, if_neg hkl, if_pos hkP,
            Nat.cast_sub hM, Nat.cast_one]
        · have : ∀ k' ∈ P, (if k ∈ insert ℓ (P.erase k') then (1 : ℝ) else 0) = 0 := by
            intro k' _
            simp [hkl, hkP]
          rw [Finset.sum_congr rfl this]
          simp [hkl, hkP]
    rw [hsum]
    by_cases hkl : k = ℓ
    · subst hkl
      simp only [indL, if_neg hℓ, if_true, sub_zero]
      field_simp
    · by_cases hkP : k ∈ P
      · simp only [indL, if_neg hkl, if_pos hkP]
        field_simp
        ring
      · simp [indL, hkl, hkP]

theorem cps_cov_fixed_prompt : Claims.cps_cov_fixed_prompt := by
  intro Z n M m P z zt L K lcov hM hP hK w Lb wbar c cP g
  obtain ⟨hD, hincl, hdin, hdout⟩ := fixed_facts (n := n) P hM hP
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hPne : P.Nonempty := card_pos.1 (by omega)
  have hrisk := StatFormal.WaveP1d.cps_fixed_prompt n M P Lb hM hP
  obtain ⟨-, -, -, hgin, hgout, -⟩ := hrisk
  -- the coverages at `w̄`
  have hρ : ∀ i, 0 < ∑ l, wbar l * K (zt i) (z l) := fun i => cov_pos hM hD hK z (zt i)
  refine ⟨fun k => ?_, fun ℓ => ?_, ?_⟩
  · -- `c = ∇Φ_m(w̄)`
    unfold cpsPhiM
    refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun i _ => ?_)
    have hin : HasDerivAt (fun t => ∑ l, Function.update wbar k t l * K (zt i) (z l)) (K (zt i) (z k)) (wbar k) := by
      have := HasDerivAt.fun_sum (u := univ) fun l _ => (hasDerivAt_update_apply wbar k l (wbar k)).mul_const
        (K (zt i) (z l))
      convert this using 1
      simp
    have hval : (∑ l, Function.update wbar k (wbar k) l * K (zt i) (z l)) = ∑ l, wbar l * K (zt i) (z l) := by
      rw [Function.update_eq_self]
    have := hin.log (by rw [hval]; exact (hρ i).ne')
    rw [hval] at this
    exact this
  · -- the partial derivatives of `J_m`
    have hsplit : (fun t => StatFormal.Wave11b.jSwor L K z zt lcov 0 (Function.update w ℓ t)) =
        fun t => Grisk (Function.update w ℓ t) M Lb +
          lcov * cpsPhiM K z zt (fun l => incl (Function.update w ℓ t) M l / M) := by
      funext t
      rw [jSwor_split]
      ring
    rw [hsplit]
    have hG := (cps_gradient n M w Lb hM hD).1 ℓ
    have hC := (hasDerivAt_cov hM hD hK z zt ℓ).const_mul lcov
    convert hG.add hC using 1
    by_cases hℓ : ℓ ∈ P
    · have h1 : esym w (univ.erase ℓ) (M - 1) / esym w univ M * (Vrisk w M Lb ℓ - Grisk w M Lb) = 0 :=
        hgin ℓ hℓ
      simp only [g, if_pos hℓ, h1, hdin ℓ hℓ, zero_div, zero_mul, Finset.sum_const_zero, mul_zero, zero_add]
    · obtain ⟨hratio, -⟩ := hgout ℓ hℓ
      have hr : esym w (univ.erase ℓ) (M - 1) / esym w univ M = (M : ℝ) ^ 2 := hratio
      simp only [g, if_neg hℓ]
      rw [hr]
      congr 1
      -- the coverage derivative off the prompt
      have hnum : ∀ i, ∑ l, dIncl w M ℓ l / M * K (zt i) (z l) =
          M * K (zt i) (z ℓ) - ∑ k ∈ P, K (zt i) (z k) := by
        intro i
        have : ∀ l, dIncl w M ℓ l / M * K (zt i) (z l) =
            (if l = ℓ then M * K (zt i) (z ℓ) else 0) - (if l ∈ P then K (zt i) (z l) else 0) := by
          intro l
          rw [hdout ℓ hℓ l]
          by_cases hl : l = ℓ
          · subst hl
            simp only [if_true, if_neg hℓ, sub_zero]
            field_simp
          · by_cases hlP : l ∈ P
            · simp only [if_neg hl, if_pos hlP, zero_sub]
              field_simp
            · simp [hl, hlP]
        rw [Finset.sum_congr rfl fun l _ => this l, Finset.sum_sub_distrib, Finset.sum_ite_eq' univ ℓ,
          Finset.sum_ite_mem, Finset.univ_inter]
        simp
      set ρ : Fin m → ℝ := fun i => ∑ l, incl w M l / M * K (zt i) (z l) with hρdef
      have e1 : ∑ k ∈ P, c k = -(1 / (m : ℝ)) * ∑ i, (∑ k ∈ P, K (zt i) (z k)) / ρ i := by
        simp only [c]
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_div]
      have e2 : (M : ℝ) * c ℓ = -(1 / (m : ℝ)) * ∑ i, ((M : ℝ) * K (zt i) (z ℓ)) / ρ i := by
        simp only [c]
        rw [mul_left_comm, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      have e3 : (M : ℝ) * (c ℓ - cP) = (M : ℝ) * c ℓ - ∑ k ∈ P, c k := by
        simp only [cP]
        field_simp
      rw [mul_assoc, e3, e1, e2]
      simp only [w] at hnum ⊢
      simp_rw [hnum]
      congr 1
      rw [Finset.sum_congr rfl fun i _ => sub_div _ _ (ρ i), Finset.sum_sub_distrib]
      ring
  · -- the gap
    have hgin' : ∀ ℓ ∈ P, g ℓ = 0 := fun ℓ hℓ => by simp [g, hℓ]
    have hgout' : ∀ ℓ ∉ P, g ℓ = -((M : ℝ) ^ 2 * (Grisk w M Lb - Vrisk w M Lb ℓ) + lcov * M * (cP - c ℓ)) :=
      fun ℓ hℓ => by simp only [g, if_neg hℓ]; ring
    have heuler : ∑ ℓ, w ℓ * g ℓ = 0 := by
      refine Finset.sum_eq_zero fun ℓ _ => ?_
      by_cases hℓ : ℓ ∈ P
      · rw [hgin' ℓ hℓ, mul_zero]
      · simp [w, hℓ]
    rw [heuler, zero_sub]
    have : Nonempty (Fin n) := ⟨hPne.choose⟩
    obtain ⟨ℓ₀, hℓ₀⟩ := exists_eq_ciInf_of_finite (f := g)
    rw [← hℓ₀]
    have hle : ∀ ℓ, g ℓ₀ ≤ g ℓ := fun ℓ => hℓ₀ ▸ ciInf_le (Set.finite_range g).bddBelow ℓ
    refine ⟨?_, ?_⟩
    · by_cases h : ℓ₀ ∈ P
      · rw [hgin' ℓ₀ h, neg_zero]; exact Set.mem_insert _ _
      · refine Set.mem_insert_of_mem _ ⟨ℓ₀, h, ?_⟩
        simp only [hgout' ℓ₀ h, neg_neg]
    · rintro a (rfl | ⟨ℓ, hℓ, rfl⟩)
      · obtain ⟨k, hk⟩ := hPne
        have := hle k; rw [hgin' k hk] at this; linarith
      · have := hle ℓ; rw [hgout' ℓ hℓ] at this
        linarith

end Fixed

/-! ### `λ_KL > 0`: the gap is infinite on faces -/

theorem cps_kl_gap_infinite : Claims.cps_kl_gap_infinite := by
  intro Z n M m w z zt L K lcov lKL ℓ hM hD hK hKL hwℓ
  set Lb : Finset (Fin n) → ℝ := fun S => (1 / (m : ℝ)) * ∑ i, StatFormal.Wave11b.lossSub L (zt i) z S
  set A : ℝ → ℝ := fun t => Grisk (Function.update w ℓ t) M Lb +
    lcov * cpsPhiM K z zt (fun l => incl (Function.update w ℓ t) M l / M) with hA
  obtain ⟨a, ha⟩ : ∃ a, HasDerivAt A a (w ℓ) :=
    ⟨_, ((cps_gradient n M w Lb hM hD).1 ℓ).add ((hasDerivAt_cov hM hD hK z zt ℓ).const_mul lcov)⟩
  rw [hwℓ] at ha
  have hn : 0 < n := by
    have := hD.2.2
    have h2 : (univ.filter fun j => w j ≠ 0).card ≤ n := (card_filter_le _ _).trans (by simp)
    omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- the relative entropy along the coordinate
  have hkl : ∀ t, StatFormal.ICL.Diag.klUnif n (Function.update w ℓ t) - StatFormal.ICL.Diag.klUnif n w =
      t * Real.log (n * t) := by
    intro t
    unfold StatFormal.ICL.Diag.klUnif
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single ℓ]
    · simp [hwℓ]
    · intro j _ hj
      simp [Function.update_of_ne hj]
    · simp
  have hJ : ∀ t, StatFormal.Wave11b.jSwor L K z zt lcov lKL (Function.update w ℓ t) =
      A t + lKL * StatFormal.ICL.Diag.klUnif n (Function.update w ℓ t) := fun t => by
    rw [jSwor_split]
  have hJ0 : StatFormal.Wave11b.jSwor L K z zt lcov lKL w = A 0 + lKL * StatFormal.ICL.Diag.klUnif n w := by
    rw [jSwor_split, hA]
    simp only
    rw [← hwℓ, Function.update_eq_self]
  have hslope : Tendsto (slope A 0) (𝓝[>] 0) (𝓝 a) :=
    (hasDerivAt_iff_tendsto_slope.1 ha).mono_left (nhdsWithin_mono _ fun t ht => ne_of_gt ht)
  have hlog : Tendsto (fun t : ℝ => Real.log (n * t)) (𝓝[>] 0) atBot := by
    refine Real.tendsto_log_nhdsGT_zero.comp ?_
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => (n : ℝ) * t) (𝓝 0) (𝓝 ((n : ℝ) * 0)) := (continuous_const_mul _).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact mul_pos hn' ht
  have hmain : Tendsto (fun t => slope A 0 t + lKL * Real.log (n * t)) (𝓝[>] 0) atBot :=
    hslope.add_atBot (hlog.const_mul_atBot hKL)
  have hquot : Tendsto (fun t => (StatFormal.Wave11b.jSwor L K z zt lcov lKL (Function.update w ℓ t) -
      StatFormal.Wave11b.jSwor L K z zt lcov lKL w) / t) (𝓝[>] 0) atBot := by
    refine hmain.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [hJ, hJ0, slope_def_field, sub_zero]
    have h := hkl t
    rw [show A t + lKL * StatFormal.ICL.Diag.klUnif n (Function.update w ℓ t) - (A 0 + lKL *
      StatFormal.ICL.Diag.klUnif n w) = (A t - A 0) + lKL * (StatFormal.ICL.Diag.klUnif n (Function.update w ℓ t) -
        StatFormal.ICL.Diag.klUnif n w) by ring, h]
    field_simp [ht.ne']
  refine ⟨hquot, fun d hd => ?_⟩
  rw [hwℓ] at hd
  have h1 := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left (nhdsWithin_mono _ fun t (ht : 0 < t) => ne_of_gt ht)
  have h2 : Tendsto (slope (fun t => StatFormal.Wave11b.jSwor L K z zt lcov lKL (Function.update w ℓ t)) 0)
      (𝓝[>] 0) atBot := by
    refine hquot.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [slope_def_field, sub_zero]
    congr 2
    rw [← hwℓ, Function.update_eq_self]
  exact not_tendsto_nhds_of_tendsto_atBot h2 d h1

end StatFormal.Wave29i
