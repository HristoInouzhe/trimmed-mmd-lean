import StatFormal.Wave30tz.RouteExample
import StatFormal.Lib.Alpha0Witness.KSLocal
import StatFormal.Wave31tr.Statements

/-!
# Wave 31tr, chunk M2: T16(b) `ex_ks_stable` (untrusted route)

The 24 atoms of the example and the values of `f₀ = exWitness exP exQ` there, from the interval bounds of the certified
`alpha0_example` route (`Wave30tz.RouteExample`: `η = e^{−50} ≤ 1/1301`, `E = e^{−1/8} ∈ [7/8, 8/9]`): with `wit = MMD · f₀`,
`wit(300) ≤ 3η/5 − 3/10 < −3η/5 ≤ wit(−100) ≤ 3η/5 < wit(20 + 10i) − (i − 1)/1050`, `|wit(20 + 10i) − i/1050| ≤ 3η/5`,
`wit(20 + 10i) ≤ 20/1050 + 3η/5 < wit(1/2) < wit(0)`; so the 24 values are distinct (`6η/5 < 1/1050`). Then `KS⁺` is locally
constant there (`Alpha0Witness.ksPlus_eq_of_close`), and `KS⁺(f₀) = 2/5` (`Wave30tz.ks_ex`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tr.RouteAlpha0

open StatFormal.Wave30tz StatFormal.Alpha0Witness

/-! ### The atoms -/

theorem mem_exAtoms {a : ℝ} (ha : a ∈ exAtoms) :
    a = -100 ∨ a = 0 ∨ a = 1 / 2 ∨ a = 300 ∨ ∃ i ∈ Finset.Icc (1 : ℕ) 20, 20 + 10 * (i : ℝ) = a := by
  unfold exAtoms at ha
  rcases Finset.mem_union.1 ha with h | h
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h
    tauto
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_image.1 h))))

theorem mem_exAtoms_of_small {a : ℝ} (h : a = -100 ∨ a = 0 ∨ a = 1 / 2 ∨ a = 300) : a ∈ exAtoms := by
  unfold exAtoms
  refine Finset.mem_union.2 (Or.inl ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact h

theorem mem_exAtoms_mid {i : ℕ} (hi : i ∈ Finset.Icc (1 : ℕ) 20) : 20 + 10 * (i : ℝ) ∈ exAtoms := by
  unfold exAtoms
  exact Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨i, hi, rfl⟩))

theorem exAtoms_card : exAtoms.card = 24 := by
  unfold exAtoms
  have hinj : Function.Injective fun i : ℕ => 20 + 10 * (i : ℝ) := fun i j h => by
    have h' : (i : ℝ) = j := by simp only at h; linarith
    exact_mod_cast h'
  have hdisj : Disjoint ({-100, 0, 1 / 2, 300} : Finset ℝ) ((Finset.Icc (1 : ℕ) 20).image fun i : ℕ => 20 + 10 * (i : ℝ)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨h1, h2⟩ := mem_Icc_cast hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with h | h | h | h <;> linarith
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj, Nat.card_Icc,
    Finset.card_insert_of_notMem (by norm_num), Finset.card_insert_of_notMem (by norm_num),
    Finset.card_insert_of_notMem (by norm_num), Finset.card_singleton]

/-- Both laws are carried by the atoms. -/
theorem exP_compl_atoms : exP (↑exAtoms : Set ℝ)ᶜ = 0 := by
  have h0 : ∀ a ∈ exAtoms, ind (↑exAtoms : Set ℝ)ᶜ a = 0 := fun a ha =>
    ind_of_notMem fun h => h (Finset.mem_coe.2 ha)
  rw [exP_apply]
  unfold pm
  rw [h0 0 (mem_exAtoms_of_small (by norm_num)), h0 (-100) (mem_exAtoms_of_small (by norm_num)),
    Finset.sum_congr rfl fun i hi => by rw [h0 _ (mem_exAtoms_mid hi)]]
  simp

theorem exQ_compl_atoms : exQ (↑exAtoms : Set ℝ)ᶜ = 0 := by
  have h0 : ∀ a ∈ exAtoms, ind (↑exAtoms : Set ℝ)ᶜ a = 0 := fun a ha =>
    ind_of_notMem fun h => h (Finset.mem_coe.2 ha)
  rw [exQ_apply]
  unfold qm
  rw [h0 (1 / 2) (mem_exAtoms_of_small (by norm_num)), h0 300 (mem_exAtoms_of_small (by norm_num)),
    h0 (-100) (mem_exAtoms_of_small (by norm_num))]
  simp

/-! ### The values of the unnormalized witness at the atoms -/

theorem wit_m100_bounds : -(3 / 5 * Real.exp (-50)) ≤ wit (-100) ∧ wit (-100) ≤ 3 / 5 * Real.exp (-50) := by
  have h1 : Wave30tz.gaussK 0 (-100) ≤ Real.exp (-50) := gaussK_far (by norm_num)
  have h2 : midSum (-100) ≤ Real.exp (-50) / 5 := midSum_far fun j hj => by
    obtain ⟨h1, _⟩ := mem_Icc_cast hj
    nlinarith
  have h3 : Wave30tz.gaussK (1 / 2) (-100) ≤ Real.exp (-50) := gaussK_far (by norm_num)
  have h4 : Wave30tz.gaussK 300 (-100) ≤ Real.exp (-50) := gaussK_far (by norm_num)
  have p1 := (gaussK_pos 0 (-100)).le
  have p2 := midSum_nonneg (-100)
  have p3 := (gaussK_pos (1 / 2) (-100)).le
  have p4 := (gaussK_pos 300 (-100)).le
  unfold wit
  constructor <;> linarith

theorem midSum_diag_ge {i : ℕ} (hi : i ∈ Finset.Icc (1 : ℕ) 20) : (i : ℝ) / 1050 ≤ midSum (20 + 10 * (i : ℝ)) := by
  have h := Finset.single_le_sum (f := fun j : ℕ => (j : ℝ) / 1050 * Wave30tz.gaussK (20 + 10 * (j : ℝ)) (20 + 10 * (i : ℝ)))
    (fun j _ => mul_nonneg (div_nonneg (Nat.cast_nonneg j) (by norm_num)) (gaussK_pos _ _).le) hi
  simp only [gaussK_self, mul_one] at h
  exact h

theorem wit_mid_bounds {i : ℕ} (hi : i ∈ Finset.Icc (1 : ℕ) 20) :
    (i : ℝ) / 1050 - 3 / 5 * Real.exp (-50) ≤ wit (20 + 10 * (i : ℝ)) ∧
      wit (20 + 10 * (i : ℝ)) ≤ (i : ℝ) / 1050 + 3 / 5 * Real.exp (-50) := by
  obtain ⟨hi1, hi2⟩ := mem_Icc_cast hi
  have h1 : Wave30tz.gaussK 0 (20 + 10 * (i : ℝ)) ≤ Real.exp (-50) := gaussK_far (by nlinarith)
  have h2 := midSum_diag hi
  have h2' := midSum_diag_ge hi
  have h3 : Wave30tz.gaussK (1 / 2) (20 + 10 * (i : ℝ)) ≤ Real.exp (-50) := gaussK_far (by nlinarith)
  have h4 : Wave30tz.gaussK 300 (20 + 10 * (i : ℝ)) ≤ Real.exp (-50) := gaussK_far (by nlinarith)
  have p1 := (gaussK_pos 0 (20 + 10 * (i : ℝ))).le
  have p3 := (gaussK_pos (1 / 2) (20 + 10 * (i : ℝ))).le
  have p4 := (gaussK_pos 300 (20 + 10 * (i : ℝ))).le
  unfold wit
  constructor <;> linarith

/-- The unnormalized witness takes 24 distinct values on the atoms. -/
theorem wit_injOn : Set.InjOn wit ↑exAtoms := by
  intro a ha b hb hab
  have hη := eta_le
  have hη0 := eta_pos
  have hE := E_ge
  have h300 := wit_300_le
  obtain ⟨hm1, hm2⟩ := wit_m100_bounds
  have hh := wit_half_ge
  have h0 := wit_half_lt_zero
  rcases mem_exAtoms (Finset.mem_coe.1 ha) with rfl | rfl | rfl | rfl | ⟨i, hi, rfl⟩ <;>
  rcases mem_exAtoms (Finset.mem_coe.1 hb) with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩
  all_goals first
    | (exfalso; linarith)
    | (obtain ⟨hi1, hi2⟩ := mem_Icc_cast hi
       obtain ⟨l1, u1⟩ := wit_mid_bounds hi
       exfalso; linarith)
    | (obtain ⟨hj1, hj2⟩ := mem_Icc_cast hj
       obtain ⟨l2, u2⟩ := wit_mid_bounds hj
       exfalso; linarith)
    | (obtain ⟨l1, u1⟩ := wit_mid_bounds hi
       obtain ⟨l2, u2⟩ := wit_mid_bounds hj
       have hij : i = j := by
         rcases lt_trichotomy i j with h | h | h
         · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
           exfalso; linarith
         · exact h
         · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
           exfalso; linarith
       rw [hij])
    | rfl

theorem exWitness_injOn : Set.InjOn (exWitness exP exQ) ↑exAtoms := by
  intro a ha b hb hab
  rw [exWitness_eq, exWitness_eq, div_left_inj' mmd_pos.ne'] at hab
  exact wit_injOn ha hb hab

/-! ### T16(b) -/

theorem ex_ks_stable_route : Claims.ex_ks_stable := by
  refine ⟨exAtoms_card, exWitness_injOn, ks_ex, fun g₀ hg₀ hgap f hclose => ?_⟩
  rw [ksPlus_eq_of_close exP exQ exP_compl_atoms exQ_compl_atoms hg₀ hgap hclose, ks_ex]

end StatFormal.Wave31tr.RouteAlpha0
