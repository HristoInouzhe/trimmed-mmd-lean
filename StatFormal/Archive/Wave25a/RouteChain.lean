import StatFormal.Archive.Wave25a.Statements
import StatFormal.Archive.Wave15b.RouteCertOdds
import StatFormal.Archive.Wave19b.RouteCertStructure
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Route — robust equality JASA `thm:cert-chain`, deterministic core (untrusted)

Sort `u = f* − f̂` decreasingly by a permutation `σ`; the upper level sets are the chain sets `U_l = σ({0..l−1})` and
`Σ_i ∇J_i u_i = Σ_{l=1}^{r−1} (u_{σ(l−1)} − u_{σ l}) G(U_l)` (Abel summation, `Σ ∇J = 0`). Each term: the gap
`s_l = u_{σ(l−1)} − u_{σ l} ≥ 0` separates `U_l` from its complement, so `lem:cert-odds` gives
`m_0(U_l) ≤ m_{s_l}(U_l) ≤ w(U_l)`, `0 ≤ G(U_l) = w(U_l) − m_0(U_l) ≤ Ḡ(U_l)`; every grid point `g ≥ 1` with
`m̲_g > w` has `s_g > s_l` (monotonicity of `m_s` in `s`), and `s_l ≤ b_X + osc f̂`, so `s_l ≤ s̄(U_l)`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

namespace StatFormal.Wave25a

open StatFormal.RobustEquality.Semidual (gsoft)
open StatFormal.RobustEquality.SemidualStrong (OTdisc Jdual Setting)
open StatFormal.Wave15b (mOdds phiOdds piCond)

section Abel

/-- Abel summation with a trailing term. -/
lemma abel_aux (F B : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ range n, F j * B j =
      ∑ l ∈ Ico 1 n, (B (l - 1) - B l) * ∑ j ∈ range l, F j + B (n - 1) * ∑ j ∈ range n, F j := by
  induction n, hn using Nat.le_induction with
  | base => simp [mul_comm]
  | succ n hn ih =>
    rw [sum_range_succ, ih, sum_Ico_succ_top hn, sum_range_succ]
    simp only [Nat.add_sub_cancel]
    ring

lemma abel_zero (F B : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (h0 : ∑ j ∈ range n, F j = 0) :
    ∑ j ∈ range n, F j * B j = ∑ l ∈ Ico 1 n, (B (l - 1) - B l) * ∑ j ∈ range l, F j := by
  rw [abel_aux F B n hn, h0, mul_zero, add_zero]

lemma telescope (B : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) : ∑ l ∈ Ico 1 n, (B (l - 1) - B l) = B 0 - B (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [sum_Ico_succ_top hn, ih]
    simp only [Nat.add_sub_cancel]
    ring

lemma Ioo_eq_Ico (r : ℕ) : Ioo 0 r = Ico 1 r := by ext l; simp; omega

end Abel

section Perm

variable {r : ℕ}

/-- `j ↦ v(σ j)` extended by `0`. -/
def pext (σ : Equiv.Perm (Fin r)) (v : Fin r → ℝ) (j : ℕ) : ℝ := if h : j < r then v (σ ⟨j, h⟩) else 0

lemma pext_lt (σ : Equiv.Perm (Fin r)) (v : Fin r → ℝ) {j : ℕ} (h : j < r) : pext σ v j = v (σ ⟨j, h⟩) := by
  simp [pext, h]

lemma sum_eq_range (σ : Equiv.Perm (Fin r)) (v : Fin r → ℝ) : ∑ i, v i = ∑ j ∈ range r, pext σ v j := by
  rw [← Equiv.sum_comp σ, ← Fin.sum_univ_eq_sum_range (pext σ v) r]
  refine sum_congr rfl fun j _ => ?_
  rw [pext_lt σ v j.2]

lemma sum_chainSet (σ : Equiv.Perm (Fin r)) (v : Fin r → ℝ) {l : ℕ} (hl : l ≤ r) :
    ∑ i ∈ chainSet σ l, v i = ∑ j ∈ range l, pext σ v j := by
  unfold chainSet
  rw [sum_filter, ← Equiv.sum_comp σ]
  simp only [Equiv.symm_apply_apply]
  have : ∑ j ∈ range l, pext σ v j = ∑ j ∈ range r, if j < l then pext σ v j else 0 := by
    rw [← sum_filter]; congr 1; ext j; simp; omega
  rw [this, ← Fin.sum_univ_eq_sum_range (fun j => if j < l then pext σ v j else 0) r]
  refine sum_congr rfl fun j _ => ?_
  rw [pext_lt σ v j.2]

lemma mem_chainSet (σ : Equiv.Perm (Fin r)) (l : ℕ) (i : Fin r) : i ∈ chainSet σ l ↔ ((σ.symm i : Fin r) : ℕ) < l := by
  simp [chainSet]

end Perm

section Odds

variable {Y : Type*} [MeasurableSpace Y] {k : ℕ}

lemma mOdds_mono {ε : ℝ} (hε : 0 < ε) {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) (hk : 0 < k) (f : Fin k → ℝ)
    {c : Fin k → Y → ℝ} (hc : ∀ i, Measurable (c i)) (P : Measure Y) [IsFiniteMeasure P] {U : Finset (Fin k)}
    (hU : U.Nonempty) {s s' : ℝ} (h : s ≤ s') : mOdds ε s a f c P U ≤ mOdds ε s' a f c P U := by
  unfold mOdds
  have hint : ∀ t, Integrable (fun y => phiOdds ε t (∑ i ∈ U, piCond ε a f c y i)) P := fun t =>
    StatFormal.Wave15b.integrable_of_unit (StatFormal.Wave15b.phi_meas (StatFormal.Wave15b.sumU_meas f hc U))
      (fun y => (StatFormal.Wave15b.phiOdds_mem (StatFormal.Wave15b.piCond_sumU_pos ha f c y hU)
        (StatFormal.Wave15b.piCond_sumU_le hε ha hk f c y U)).1)
      (fun y => (StatFormal.Wave15b.phiOdds_mem (StatFormal.Wave15b.piCond_sumU_pos ha f c y hU)
        (StatFormal.Wave15b.piCond_sumU_le hε ha hk f c y U)).2)
  exact integral_mono (hint s) (hint s') fun y =>
    StatFormal.Wave15b.phiOdds_mono hε (StatFormal.Wave15b.piCond_sumU_pos ha f c y hU)
      (StatFormal.Wave15b.piCond_sumU_le hε ha hk f c y U) h

end Odds

lemma le_iSup_fin {r : ℕ} (v : Fin r → ℝ) (i : Fin r) : v i ≤ ⨆ j, v j :=
  le_ciSup (Set.finite_range v).bddAbove i

lemma iInf_le_fin {r : ℕ} (v : Fin r → ℝ) (i : Fin r) : ⨅ j, v j ≤ v i :=
  ciInf_le (Set.finite_range v).bddBelow i

theorem chain_gap : Claims.chain_gap := by
  intro K _ r S ε w c P _ fs fh s mlow bX hset hmax hs0 hbX hlow
  obtain ⟨hε, hw, hw1, hcm, hcB⟩ := hset
  haveI : Nonempty (Fin r) := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp at hw1
    · exact ⟨⟨0, h⟩⟩
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp at hw1
    · exact h
  set u : Fin r → ℝ := fun i => fs i - fh i with hu
  -- the sorting permutation
  set σ : Equiv.Perm (Fin r) := Tuple.sort (fun i => -u i) with hσ
  have hmono : Monotone ((fun i => -u i) ∘ σ) := Tuple.monotone_sort _
  have hanti : ∀ j j' : Fin r, j ≤ j' → u (σ j') ≤ u (σ j) := fun j j' h => by
    have := hmono h; simp only [Function.comp] at this; linarith
  set G : Fin r → ℝ := fun i => StatFormal.Wave15b.gradJ ε w fh c P i with hG
  set B : ℕ → ℝ := pext σ u with hB
  set F : ℕ → ℝ := pext σ G with hF
  set smax := bX + osc fh
  have hfoc := (StatFormal.RobustEquality.SemidualStrong.maximiser_foc K r ε w c P fs
    ⟨hε, hw, hw1, hcm, hcB⟩ hmax).2
  -- per-level facts
  have hlevel : ∀ l ∈ Ico 1 r, 0 ≤ B (l - 1) - B l ∧
      B (l - 1) - B l ≤ sBar s mlow w smax (chainSet σ l) ∧
      0 ≤ ∑ i ∈ chainSet σ l, G i ∧ ∑ i ∈ chainSet σ l, G i ≤ gBar mlow w (chainSet σ l) := by
    intro l hl
    rw [mem_Ico] at hl
    have hl1 : l - 1 < r := by omega
    have hl2 : l < r := hl.2
    have hBl1 : B (l - 1) = u (σ ⟨l - 1, hl1⟩) := pext_lt σ u hl1
    have hBl : B l = u (σ ⟨l, hl2⟩) := pext_lt σ u hl2
    set U := chainSet σ l with hUdef
    have hUne : U.Nonempty := ⟨σ ⟨0, hr⟩, by rw [mem_chainSet]; simp; omega⟩
    have hUnu : U ≠ univ := fun h => by
      have : σ ⟨l, hl2⟩ ∈ U := h ▸ mem_univ _
      rw [mem_chainSet] at this; simp at this
    have hgap0 : 0 ≤ B (l - 1) - B l := by
      rw [hBl1, hBl]; linarith [hanti ⟨l - 1, hl1⟩ ⟨l, hl2⟩ (by simp [Fin.le_def])]
    have hgap : ∀ i ∈ U, ∀ j ∉ U, B (l - 1) - B l ≤ (fs i - fh i) - (fs j - fh j) := by
      intro i hi j hj
      rw [mem_chainSet] at hi hj
      have h1 : u (σ ⟨l - 1, hl1⟩) ≤ u i := by
        have := hanti (σ.symm i) ⟨l - 1, hl1⟩ (by simp [Fin.le_def]; omega)
        simpa using this
      have h2 : u j ≤ u (σ ⟨l, hl2⟩) := by
        have := hanti ⟨l, hl2⟩ (σ.symm j) (by simp [Fin.le_def]; omega)
        simpa using this
      rw [hBl1, hBl]; simp only [hu] at h1 h2 ⊢; linarith
    obtain ⟨hm1, hm2, hm3⟩ := StatFormal.Wave15b.cert_odds_mean K r ε w fs fh c P U (B (l - 1) - B l)
      ⟨hε, hw, hw1, hcm, hcB⟩ hmax hUne hgap0 hgap
    have hGU : ∑ i ∈ U, G i = ∑ i ∈ U, w i - mOdds ε 0 w fh c P U := hm2
    refine ⟨hgap0, ?_, by rw [hGU]; linarith, ?_⟩
    · -- `s_l ≤ s̄(U)`
      unfold sBar
      rw [Finset.le_fold_min]
      refine ⟨?_, fun g hg => ?_⟩
      · -- `s_l ≤ b_X + osc f̂`
        rw [hBl1, hBl]
        simp only [hu]
        have h1 := hfoc (σ ⟨l - 1, hl1⟩) (σ ⟨l, hl2⟩) bX (fun y => hbX _ _ y)
        have h2 := le_iSup_fin fh (σ ⟨l, hl2⟩)
        have h3 := iInf_le_fin fh (σ ⟨l - 1, hl1⟩)
        show _ ≤ bX + osc fh
        unfold osc; linarith
      · rw [mem_filter] at hg
        obtain ⟨-, hg1, hg2⟩ := hg
        by_contra hlt'
        have hlt := not_le.1 hlt'
        have hmo := mOdds_mono hε hw hr fh hcm P hUne hlt.le
        have := hlow g U hUne hUnu
        linarith
    · -- `G(U) ≤ Ḡ(U)`
      unfold gBar
      have := hlow 0 U hUne hUnu
      rw [hs0] at this
      rw [hGU]; linarith
  -- Abel summation
  have hsumG : ∑ j ∈ range r, F j = 0 := by
    rw [← sum_eq_range σ G]
    have := (StatFormal.Wave19b.cert_structure_ii_grad K r ε w c P fh
      ⟨hε, hw, hw1, hcm, hcB⟩).2
    exact this
  have habel : ∑ i, G i * u i = ∑ l ∈ Ico 1 r, (B (l - 1) - B l) * ∑ i ∈ chainSet σ l, G i := by
    rw [sum_eq_range σ (fun i => G i * u i)]
    have : ∀ j, pext σ (fun i => G i * u i) j = F j * B j := fun j => by
      simp only [pext, hF, hB]; split_ifs <;> simp
    simp_rw [this]
    rw [abel_zero F B r hr hsumG]
    refine sum_congr rfl fun l hl => ?_
    rw [sum_chainSet σ G (by rw [mem_Ico] at hl; omega)]
  have hgapJ := StatFormal.Wave19b.cert_structure_ii_gap K r ε w c P fs fh
    ⟨hε, hw, hw1, hcm, hcB⟩ hmax
  have hG19 : ∀ i, StatFormal.Wave19b.gradJ ε w c P fh i = G i := fun i => rfl
  constructor
  · refine hgapJ.2.trans ?_
    simp only [hG19]
    rw [EReal.coe_le_coe_iff]
    change ∑ i, G i * u i ≤ _
    rw [habel]
    refine le_trans ?_ (le_sup' (fun σ' : Equiv.Perm (Fin r) => ∑ l ∈ Ioo 0 r,
      sBar s mlow w smax (chainSet σ' l) * max 0 (gBar mlow w (chainSet σ' l))) (mem_univ σ))
    rw [Ioo_eq_Ico]
    refine sum_le_sum fun l hl => ?_
    obtain ⟨h0, h1, h2, h3⟩ := hlevel l hl
    exact mul_le_mul h1 (le_trans h3 (le_max_right _ _)) h2 (le_trans h0 h1)
  · -- oscillation
    have hosc : osc u = B 0 - B (r - 1) := by
      have hmaxu : (⨆ i, u i) = u (σ ⟨0, hr⟩) := by
        refine le_antisymm (ciSup_le fun i => ?_) (le_iSup_fin u _)
        have := hanti ⟨0, hr⟩ (σ.symm i) (by simp [Fin.le_def])
        simpa using this
      have hminu : (⨅ i, u i) = u (σ ⟨r - 1, by omega⟩) := by
        refine le_antisymm (iInf_le_fin u _) (le_ciInf fun i => ?_)
        have := hanti (σ.symm i) ⟨r - 1, by omega⟩ (by simp [Fin.le_def]; omega)
        simpa using this
      unfold osc; rw [hmaxu, hminu, show B 0 = u (σ ⟨0, hr⟩) from pext_lt σ u hr,
        show B (r - 1) = u (σ ⟨r - 1, by omega⟩) from pext_lt σ u (by omega)]
    change osc u ≤ _
    rw [hosc, ← telescope B r hr]
    refine le_trans ?_ (le_sup' (fun σ' : Equiv.Perm (Fin r) => ∑ l ∈ Ioo 0 r,
      if 0 ≤ gBar mlow w (chainSet σ' l) then sBar s mlow w smax (chainSet σ' l) else 0) (mem_univ σ))
    rw [Ioo_eq_Ico]
    refine sum_le_sum fun l hl => ?_
    obtain ⟨h0, h1, h2, h3⟩ := hlevel l hl
    rw [if_pos (le_trans h2 h3)]
    exact h1

end StatFormal.Wave25a
