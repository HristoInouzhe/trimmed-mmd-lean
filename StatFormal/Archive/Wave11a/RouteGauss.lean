import StatFormal.Archive.Wave11a.Statements
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue

/-!
# Wave 11a route: robust equality JASA `prop:ep-gauss` (the `λ`-optimisation)

Untrusted proof file. With `s = 1 − A/λ` and `x* > 1` the root of `x − log x = 1 + 2β/ε`, the tangent-line
inequality `−log s ≥ 1 + log x* − s x*` gives `T(λ) ≥ A ε x*/2` for every `λ > A`, with equality at
`λ* = A x*/(x* − 1)`; `log x ≤ x/2` gives `x* ≤ 2 + 4β/ε`; the root bounds are elementary.
-/

set_option linter.style.longLine false

noncomputable section
open Real Set

namespace StatFormal.Wave11a

lemma log_le_half (x : ℝ) (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have h1 : Real.log x = 2 * Real.log (√x) := by
    rw [Real.log_sqrt hx.le]; ring
  have h2 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hx)
  have h3 : (√x - 2) ^ 2 ≥ 0 := sq_nonneg _
  have h4 : (√x) ^ 2 = x := Real.sq_sqrt hx.le
  nlinarith

lemma sub_log_strictMonoOn : StrictMonoOn (fun x : ℝ => x - Real.log x) (Ici 1) := by
  intro x hx y hy hxy
  simp only [mem_Ici] at hx hy
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hq : 0 < y / x := div_pos hy0 hx0
  have hq1 : y / x ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq hx0.ne'] at h; linarith
  have hl := Real.log_lt_sub_one_of_pos hq hq1
  rw [Real.log_div hy0.ne' hx0.ne'] at hl
  have : y / x - 1 ≤ y - x := by
    rw [div_sub_one hx0.ne', div_le_iff₀ hx0]
    nlinarith
  simp only
  linarith

theorem gauss_xstar : Claims.gauss_xstar := by
  intro β ε hβ hε
  set t := 1 + 2 * β / ε with ht
  have ht1 : 1 < t := by have : 0 < 2 * β / ε := by positivity
                         linarith
  set M := 2 + 4 * β / ε with hM
  have hM1 : 1 ≤ M := by have : 0 < 4 * β / ε := by positivity
                         linarith
  have hfM : t ≤ M - Real.log M := by
    have := log_le_half M (by linarith)
    have : M / 2 = t := by rw [hM, ht]; ring
    linarith
  have hcont : ContinuousOn (fun x : ℝ => x - Real.log x) (Icc 1 M) :=
    continuousOn_id.sub (Real.continuousOn_log.mono fun z hz => by
      simp only [mem_Icc] at hz; simp only [mem_compl_iff, mem_singleton_iff]; linarith [hz.1])
  have hf1 : (fun x : ℝ => x - Real.log x) 1 ≤ t := by
    change (1 : ℝ) - Real.log 1 ≤ t
    rw [Real.log_one]; linarith
  obtain ⟨x, hxI, hx⟩ := intermediate_value_Icc hM1 hcont ⟨hf1, hfM⟩
  have hx1 : 1 < x := by
    rcases eq_or_lt_of_le hxI.1 with h | h
    · subst h; simp at hx; linarith
    · exact h
  refine ⟨x, ⟨hx1, hx⟩, ?_⟩
  rintro y ⟨hy1, hy⟩
  exact sub_log_strictMonoOn.injOn (mem_Ici.2 hy1.le) (mem_Ici.2 hx1.le) (by change y - Real.log y = x - Real.log x; rw [hy]; exact hx.symm)

section Core
variable {A β ε xs : ℝ}

lemma beta_eq (hε : 0 < ε) (hxs : xs - Real.log xs = 1 + 2 * β / ε) :
    β = ε / 2 * (xs - 1 - Real.log xs) := by
  have : 2 * β / ε = xs - Real.log xs - 1 := by linarith
  field_simp at this
  linarith

lemma value_eq (hε : 0 < ε) (hxs : xs - Real.log xs = 1 + 2 * β / ε) :
    A * (β + ε / 2 * (1 + Real.log xs)) = A * ε * xs / 2 := by
  rw [beta_eq hε hxs]; ring

/-- The lower bound `T(λ) ≥ A ε x*/2` for every `λ > A ≥ 0`. -/
lemma Tgauss_ge (hA : 0 ≤ A) (hε : 0 < ε) (hxs1 : 1 < xs)
    (hxs : xs - Real.log xs = 1 + 2 * β / ε) {lam : ℝ} (hlam : A < lam) :
    A * ε * xs / 2 ≤ Tgauss A β ε lam := by
  have hl0 : 0 < lam := lt_of_le_of_lt hA hlam
  set s := 1 - A / lam with hs
  have hs0 : 0 < s := by
    rw [hs, sub_pos, div_lt_one hl0]; exact hlam
  have hxs0 : 0 < xs := by linarith
  -- tangent line of `log` at `1/xs`: `log s ≤ log(1/xs) + (s − 1/xs) xs`
  have htan : Real.log s ≤ -Real.log xs + s * xs - 1 := by
    have h := Real.log_le_sub_one_of_pos (mul_pos hs0 hxs0)
    rw [Real.log_mul hs0.ne' hxs0.ne'] at h
    linarith
  have hls : lam * s = lam - A := by rw [hs]; field_simp
  unfold Tgauss
  rw [← hs]
  have hβ := beta_eq hε hxs
  have key : lam * ε / 2 * Real.log s ≤ lam * ε / 2 * (-Real.log xs + s * xs - 1) :=
    mul_le_mul_of_nonneg_left htan (by positivity)
  have e : lam * ε / 2 * (-Real.log xs + s * xs - 1) = ε / 2 * ((lam * s) * xs) - lam * ε / 2 * (Real.log xs + 1) := by ring
  rw [e, hls] at key
  rw [hβ]
  nlinarith

lemma Tgauss_attain (hA : 0 < A) (hε : 0 < ε) (hxs1 : 1 < xs)
    (hxs : xs - Real.log xs = 1 + 2 * β / ε) :
    A < A * xs / (xs - 1) ∧ Tgauss A β ε (A * xs / (xs - 1)) = A * ε * xs / 2 := by
  have hd : 0 < xs - 1 := by linarith
  have hxs0 : 0 < xs := by linarith
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hd]; nlinarith
  · unfold Tgauss
    have h1 : 1 - A / (A * xs / (xs - 1)) = xs⁻¹ := by
      field_simp; ring
    rw [h1, Real.log_inv, beta_eq hε hxs]
    field_simp
    ring

end Core

theorem gauss_inf : Claims.gauss_inf := by
  intro d w β ε xs hβ hε hxs1 hxs
  set A := ‖w‖ ^ 2 with hAdef
  have hA : 0 ≤ A := by positivity
  have hval := value_eq (A := A) hε hxs
  have hlow : ∀ v ∈ Tgauss A β ε '' Ioi A, A * (β + ε / 2 * (1 + Real.log xs)) ≤ v := by
    rintro v ⟨lam, hlam, rfl⟩
    rw [hval]; exact Tgauss_ge hA hε hxs1 hxs hlam
  have hleast : w ≠ 0 → IsLeast (Tgauss A β ε '' Ioi A) (A * (β + ε / 2 * (1 + Real.log xs))) := by
    intro hw
    have hA0 : 0 < A := by rw [hAdef]; positivity
    obtain ⟨h1, h2⟩ := Tgauss_attain hA0 hε hxs1 hxs
    exact ⟨⟨_, h1, by rw [h2, hval]⟩, hlow⟩
  refine ⟨⟨hlow, ?_⟩, hval, hleast⟩
  intro b hb
  by_cases hw : w = 0
  · have hA0 : A = 0 := by rw [hAdef, hw]; simp
    rw [hA0, zero_mul]
    by_contra hpos
    push Not at hpos
    have hmem : Tgauss A β ε (b / (2 * β)) ∈ Tgauss A β ε '' Ioi A :=
      ⟨_, by rw [hA0]; exact mem_Ioi.2 (by positivity), rfl⟩
    have := hb hmem
    unfold Tgauss at this
    rw [hA0, zero_div, sub_zero, Real.log_one, mul_zero, sub_zero] at this
    field_simp at this
    linarith
  · exact hb (hleast hw).1

theorem gauss_bounds : Claims.gauss_bounds := by
  intro d w β ε xs hβ hε hxs1 hxs
  have hA : 0 ≤ ‖w‖ ^ 2 := by positivity
  have hl0 : 0 ≤ Real.log xs := Real.log_nonneg hxs1.le
  have hxsM : xs ≤ 2 + 4 * β / ε := by
    have := log_le_half xs (by linarith)
    have e : 2 + 4 * β / ε = 2 * (1 + 2 * β / ε) := by ring
    rw [e]; linarith
  have hlog : Real.log xs ≤ Real.log (2 + 4 * β / ε) := Real.log_le_log (by linarith) hxsM
  refine ⟨mul_le_mul_of_nonneg_left ?_ hA, mul_le_mul_of_nonneg_left ?_ hA⟩
  · nlinarith
  · nlinarith

theorem gauss_root : Claims.gauss_root := by
  intro d w β ε xs hβ hε hxs1 hxs
  set W := ‖w‖ with hW
  have hW0 : 0 ≤ W := norm_nonneg _
  set L := Real.log (2 + 4 * β / ε)
  set b0 := ε / 2 * (1 + Real.log xs) with hb0
  set b1 := ε * (1 + L) / 2 with hb1
  have hl0 : 0 ≤ Real.log xs := Real.log_nonneg hxs1.le
  have hxsM : xs ≤ 2 + 4 * β / ε := by
    have := log_le_half xs (by linarith)
    have e : 2 + 4 * β / ε = 2 * (1 + 2 * β / ε) := by ring
    rw [e]; linarith
  have hlog : Real.log xs ≤ L := Real.log_le_log (by linarith) hxsM
  have hb0pos : ε / 2 ≤ b0 := by rw [hb0]; nlinarith
  have hb01 : b0 ≤ b1 := by rw [hb0, hb1]; nlinarith
  set u := √(β + b0) with hu
  set v := √β with hv
  have hu2 : u ^ 2 = β + b0 := Real.sq_sqrt (by linarith)
  have hv2 : v ^ 2 = β := Real.sq_sqrt hβ.le
  have hv0 : 0 < v := Real.sqrt_pos.2 hβ
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hvu : v ≤ u := Real.sqrt_le_sqrt (by linarith)
  have hsq : √(W ^ 2 * (β + b0)) = W * u := by
    rw [Real.sqrt_mul (sq_nonneg W), Real.sqrt_sq hW0]
  have hdiff : u - v = b0 / (u + v) := by
    rw [eq_div_iff (by linarith)]; nlinarith
  rw [hsq, ← mul_sub]
  constructor
  · -- `ε/(4√(β+ε)) ≤ u − v`
    set p := √(β + ε) with hp
    have hp2 : p ^ 2 = β + ε := Real.sq_sqrt (by linarith)
    have hp0 : 0 < p := Real.sqrt_pos.2 (by linarith)
    have hmain : ε / (4 * p) ≤ u - v := by
      rw [hdiff, div_le_div_iff₀ (by positivity) (by linarith)]
      -- `ε (u + v) ≤ b0 · 4p`; it suffices `ε u ≤ 2 p b0`
      have h2 : ε * u ≤ 2 * p * b0 := by
        have hsq' : (ε * u) ^ 2 ≤ (2 * p * b0) ^ 2 := by
          have e1 : (ε * u) ^ 2 = ε ^ 2 * (β + b0) := by rw [mul_pow, hu2]
          have e2 : (2 * p * b0) ^ 2 = 4 * (β + ε) * b0 ^ 2 := by rw [mul_pow, mul_pow, hp2]; ring
          rw [e1, e2]
          have q1 : 0 ≤ 4 * b0 ^ 2 - ε ^ 2 := by nlinarith
          have q2 : 0 ≤ 4 * b0 - ε := by linarith
          nlinarith [mul_nonneg hβ.le q1, mul_nonneg (mul_nonneg hε.le (by linarith : (0:ℝ) ≤ b0)) q2]
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq'
      nlinarith
    calc W * ε / (4 * p) = W * (ε / (4 * p)) := by ring
      _ ≤ W * (u - v) := mul_le_mul_of_nonneg_left hmain hW0
  · refine mul_le_mul_of_nonneg_left (le_min ?_ ?_) hW0
    · -- `u − v ≤ √b0 ≤ √b1`
      have h1 : u ≤ v + √b0 := by
        rw [hu]
        rw [Real.sqrt_le_iff]
        have hs0 : (√b0) ^ 2 = b0 := Real.sq_sqrt (by linarith)
        have : 0 ≤ √b0 := Real.sqrt_nonneg _
        constructor
        · positivity
        · nlinarith
      have h2 : √b0 ≤ √b1 := Real.sqrt_le_sqrt hb01
      linarith
    · -- `u − v = b0/(u+v) ≤ b0/(2v) ≤ b1/(2v)`
      rw [hdiff]
      have e : ε * (1 + L) / (4 * v) = b1 / (2 * v) := by rw [hb1]; ring
      rw [e, div_le_div_iff₀ (by linarith) (by positivity)]
      have : 0 ≤ b0 := by linarith
      nlinarith

end StatFormal.Wave11a
