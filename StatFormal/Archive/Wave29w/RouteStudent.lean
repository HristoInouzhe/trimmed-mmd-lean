import StatFormal.Archive.Wave29w.Statements
import StatFormal.Archive.Wave29f.RouteStudentBreak

/-!
# Route — R `thm:student` (ii): the region of content exactly `p` (untrusted)

`F_{K,ν}` is the distribution function of the atomless law `fLaw` (Wave 29f route `fLaw_noAtoms`), so it is
left-continuous: `F(q) = fLaw(Iic q) = fLaw(Iio q) = sup_n F(q − 1/(n+1)) ≤ p` at `q = F^{-1}(p)` (every `x < q` has
`F(x) < p`), while `F(q) ≥ p` by right-continuity (Wave 23d `fQuant_spec`). The content of the ellipsoid is
`F(r²/K)` (Wave 23d `student_content_aux`), and the minimality is Wave 23d `content_lt` / `content_rp`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave29w

open StatFormal.Wave23d (studentLaw fCDF fQuant fLaw)

/-- `F_{K,ν}(F_{K,ν}^{-1}(p)) = p`. -/
lemma fCDF_fQuant {K : ℕ} {ν p : ℝ} (hK : 0 < K) (hν : 0 < ν) (hp : 0 < p) (hp1 : p < 1) :
    fCDF K ν (fQuant K ν p) = p := by
  obtain ⟨_, hge, hlt⟩ := StatFormal.Wave23d.fQuant_spec (K := K) hν hp hp1
  set q := fQuant K ν p
  have := StatFormal.Wave23d.isProb_fLaw (K := K) hν
  have := StatFormal.Wave29f.fLaw_noAtoms hK hν
  refine le_antisymm ?_ hge
  -- `fLaw (Iic q) = fLaw (Iio q) ≤ ofReal p`
  have hIio : fLaw K ν (Iio q) = fLaw K ν (Iic q) := measure_congr Iio_ae_eq_Iic
  set s : ℕ → Set ℝ := fun n => Iic (q - 1 / ((n : ℝ) + 1))
  have hmono : Monotone s := by
    intro a b hab x hx
    simp only [s, mem_Iic] at hx ⊢
    have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
    linarith
  have hU : (⋃ n, s n) = Iio q := by
    ext x
    simp only [s, mem_iUnion, mem_Iic, mem_Iio]
    constructor
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨n, by linarith⟩
  have hlim := tendsto_measure_iUnion_atTop (μ := fLaw K ν) hmono
  rw [hU, hIio] at hlim
  have hle : ∀ n, (fLaw K ν ∘ s) n ≤ ENNReal.ofReal p := fun n => by
    simp only [Function.comp_apply, s]
    rw [StatFormal.Wave23d.fLaw_Iic hν]
    refine ENNReal.ofReal_le_ofReal (hlt _ ?_).le
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have h1 : fLaw K ν (Iic q) ≤ ENNReal.ofReal p := le_of_tendsto' hlim hle
  rw [StatFormal.Wave23d.fLaw_Iic hν, ENNReal.ofReal_le_ofReal_iff hp.le] at h1
  exact h1

theorem student_region_exact : Claims.student_region_exact := by
  intro K ν A p hK hν hp hp1
  have hF := fCDF_fQuant hK hν hp hp1
  refine ⟨hF, ?_, fun r hr => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [StatFormal.Wave23d.student_content_aux hK hν A (Real.sqrt_nonneg _),
      StatFormal.Wave23d.rp_sq hK hν hp hp1, hF]
  · by_contra hlt
    push_neg at hlt
    exact absurd h (not_le.2 (StatFormal.Wave23d.content_lt hK hν A hp hp1 hr hlt))
  · refine (StatFormal.Wave23d.content_rp hK hν A hp hp1).trans (measure_mono fun u hu => ?_)
    simp only [mem_ofPred_eq] at hu ⊢
    exact hu.trans h

end StatFormal.Wave29w
