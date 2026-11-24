import StatFormal.Wave31tu.Statements
import StatFormal.Wave31to.Proofs
import StatFormal.Wave31tl.Proofs
import StatFormal.Lib.ExpMargin.GenInv
import StatFormal.Lib.ExpMargin.Eventually

/-!
# Wave 31tu route R: Proposition S4.8 (ii), the logarithmic rate under an exponential margin (S4 :470-487, proof :514-526;
untrusted proof material)

* `newrates_ii_exp_route`: for `n∧m ≥ n₀ = max{10, ⌈M₀⌉}`, part (i) in the form of Theorem 5.7 (ii) (certified
  `Wave31to.newrates_ii_b`, with `Δ_φ = 2κ` and `B = 2`, the default batches by `Wave31tl.lorate_batches`) gives
  `α⋆ − h − ω^←(t_{n,m}) ≤ α̂ ≤ α⋆` with probability `≥ 1 − δ − η`; Theorem 5.7 (iii) (`Wave31tl.lorate_iii`) and `J ≤ (n∧m)^b`
  give `t_{n,m} ≤ K√((A + b log M)/M)`, `M = n∧m`, `K = 1000β⋆κ/v²_min`, `A = 1 + log(1/δ) + log(1/η)`, which is at most
  `M^{−c′/c} = exp(−c′/(c/log M))` for `M ≥ M₀` (`ExpMargin.eventually_sqrt_log_div_le_rpow`, `c′/c < ½`); with `c/log M < ε₀`
  (`log M > c/ε₀`), the generalized inverse of the exponential margin is at most `c/log M` (`ExpMargin.sSup_le_of_le_exp_of_lt`).
  `n₀` depends only on `κ, α⋆, c′, ε₀, b, η, δ, v²_min, c`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter

namespace StatFormal.Wave31tu.RouteR

open StatFormal.Wave30tq StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.Wave31tl StatFormal.TrimmedMMD.Unconditional

/-- **Y25, Proposition S4.8 (ii)**: the rate `c/log(n∧m)` for every `c > 2c′` under a margin `ω ≥ exp(−c′/ε)` on `(0, ε₀]`, grids
with at most `(n∧m)^b` levels. -/
theorem newrates_ii_exp_route : Claims.newrates_ii_exp := by
  intro κ αs c' ε₀ b η δ s2 c hκ hc' hε₀ hε₀a hαs1 hb hη0 hη1 hδ0 hδ1 hs20 hs24 hcc
  have hc : 0 < c := by linarith
  have hαs0 : 0 < αs := hε₀.trans_le hε₀a
  have hθ : c' / c < 1 / 2 := by rw [div_lt_iff₀ hc]; linarith
  have hβ : 0 < beta αs := by unfold beta; exact div_pos one_pos (by linarith)
  have hK : 0 ≤ 1000 * beta αs * κ / s2 := by positivity
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 ((ExpMargin.eventually_lt_log (c / ε₀)).and
    (ExpMargin.eventually_sqrt_log_div_le_rpow hK (1 + Real.log (1 / δ) + Real.log (1 / η)) b hθ))
  refine ⟨max 10 ⌈M₀⌉₊, ?_⟩
  intro 𝒳 H _ _ _ _ _ φ P Q _ _ ω J n m α h R hφ hκφ htv hmono hω0 hωu hωexp hgrid hJ hJb hrun hdef hn₀ hmesh
  set M : ℝ := ((min n m : ℕ) : ℝ) with hMdef
  have hM10 : 10 ≤ min n m := (le_max_left _ _).trans hn₀
  have hMM₀ : M₀ ≤ M := (Nat.le_ceil M₀).trans (by rw [hMdef]; exact_mod_cast (le_max_right _ _).trans hn₀)
  obtain ⟨hlogM, hrate⟩ := hM₀ M hMM₀
  have hM0 : 0 < M := by rw [hMdef]; exact_mod_cast (by omega : 0 < min n m)
  -- the default batches
  obtain ⟨bn1, bn2, bm1, bm2, hcn, hcm, hlx, hly, hN⟩ := hdef
  have hlxe : R.lx = fun i : Fin n => defaultLabel bn1 bn2 i := funext hlx
  have hlye : R.ly = fun j : Fin m => defaultLabel bm1 bm2 j := funext hly
  obtain ⟨hn1', hm1', hr1', hN'⟩ := Wave31tl.lorate_batches n m bn1 bn2 bm1 bm2 hM10 hcn hcm
  have hB : ∀ k, R.bat k ≤ 2 := by
    intro k
    obtain ⟨i, hi⟩ := hrun.1.1.1.1 k
    rw [← hrun.1.1.2.2.2.1 k i hi, hlx]
    exact Arith.label_le_two _ _ _
  have hn1 : 1 ≤ fitCard R.lx 1 := by rw [hlxe]; exact hn1'
  have hm1 : 1 ≤ fitCard R.ly 1 := by rw [hlye]; exact hm1'
  have hr1 : rOne R.lx R.ly ≤ 1 := by rw [hlxe, hlye]; exact hr1'.trans (min_le_left _ _)
  have hNr : (1 : ℝ) ≤ R.N := by
    rw [hN, hlxe, hlye]
    have : (10 : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast hM10
    linarith
  have hN1 : 1 ≤ R.N := by exact_mod_cast hNr
  -- part (i) in the form of Theorem 5.7 (ii)
  have hDφ : ∀ x x', ‖φ x - φ x'‖ ≤ 2 * κ := fun x x' => (norm_sub_le _ _).trans (by linarith [hκφ x, hκφ x'])
  have hmono' : MonotoneOn ω (Icc 0 (Distances.tvDist P Q)) := by rw [htv]; exact hmono
  have hω0' : ∀ e ∈ Icc (0 : ℝ) (Distances.tvDist P Q), 0 ≤ ω e := by rw [htv]; exact hω0
  have hωu' : ∀ e ∈ Icc (0 : ℝ) (Distances.tvDist P Q), ω e ≤ Wave31ti.uPath φ P Q (Distances.tvDist P Q - e) := by
    rw [htv]; exact hωu
  have hαs1' : Distances.tvDist P Q < 1 := by rw [htv]; exact hαs1
  have hmesh' : MeshBelowLe α (Distances.tvDist P Q) h := by rw [htv]; exact hmesh
  obtain ⟨E, hEm, hEp, hE⟩ := Wave31to.newrates_ii_b 𝒳 H φ κ (2 * κ) P Q ω J n m α δ s2 η h R 2 hφ hκφ hDφ le_rfl
    hmono' hω0' hωu' hαs1' hgrid hJ hδ0 hδ1 hs20 hs24 hrun hB hn1 hm1 hr1 hN1 hη0 hη1 hmesh'
  -- the bound on `t_{n,m}`
  have ht : tNM κ (2 * κ) αs s2 δ η (rOne R.lx R.ly) 2 J R.N ≤
      1000 * beta αs * κ / s2 * √((1 + Real.log (1 / δ) + Real.log (J / η)) / M) := by
    have := (Wave31tl.lorate_iii κ (2 * κ) 1 1 αs s2 δ η J n m bn1 bn2 bm1 bm2 (by linarith) le_rfl one_pos le_rfl
      hαs0.le hαs1 hs20 hs24 hδ0 hδ1 hη0 hη1 hJ hM10 hcn hcm).1
    rw [hN, hlxe, hlye]
    exact this
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hlogJ : Real.log (J / η) ≤ Real.log (1 / η) + b * Real.log M := by
    rw [Real.log_div hJ0.ne' hη0.ne', one_div, Real.log_inv]
    have : Real.log J ≤ b * Real.log M := by
      rw [← Real.log_rpow hM0]
      exact Real.log_le_log hJ0 hJb
    linarith
  have hS : (1 + Real.log (1 / δ) + Real.log (J / η)) / M ≤
      (1 + Real.log (1 / δ) + Real.log (1 / η) + b * Real.log M) / M :=
    div_le_div_of_nonneg_right (by linarith) hM0.le
  have ht2 : tNM κ (2 * κ) αs s2 δ η (rOne R.lx R.ly) 2 J R.N ≤ M ^ (-(c' / c)) :=
    ht.trans ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hS) hK).trans hrate)
  -- the generalized inverse of the exponential margin
  have hcε : 0 < c / ε₀ := div_pos hc hε₀
  have hlogpos : 0 < Real.log M := hcε.trans hlogM
  have hx : 0 < c / Real.log M := div_pos hc hlogpos
  have hxε : c / Real.log M < ε₀ := by
    rw [div_lt_iff₀ hlogpos]
    have := (div_lt_iff₀ hε₀).1 hlogM
    linarith
  have hg : Wave31to.genInv ω αs (tNM κ (2 * κ) αs s2 δ η (rOne R.lx R.ly) 2 J R.N) ≤ c / Real.log M :=
    ExpMargin.sSup_le_of_le_exp_of_lt hmono hε₀ hε₀a hc' hωexp hx hxε
      (by rw [ExpMargin.exp_neg_div_div_log hM0]; exact ht2)
  refine ⟨E, hEm, hEp, fun z hz => ?_⟩
  have h1 := hE hz
  rw [htv] at h1
  exact ⟨by linarith [h1.1], h1.2⟩

end StatFormal.Wave31tu.RouteR
