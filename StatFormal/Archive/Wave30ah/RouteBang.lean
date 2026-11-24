import StatFormal.Archive.Wave30ah.Statements
import StatFormal.Archive.TrimmedMMD.BangBang.Proofs

/-!
# Route — wave 30ah: `prop:bangbang`, "`𝒯_α` is nonempty, convex and compact" (untrusted)

Nonempty: the certified `bangbang_i`. Convex: the witness `d̂` is the same at all minimisers (`bangbang_i`), and it
is affine along segments, so it is constant on the segment between two minimisers and the objective `‖d̂‖²` keeps
its minimal value there. Compact: a closed subset (intersection of the closed sublevel sets `{qp ≤ qp r}`) of the
compact product of capped simplices.
-/

set_option linter.style.longLine false

noncomputable section
open Set

namespace StatFormal.Wave30ah

open StatFormal.TrimmedMMD.BangBang

theorem bangbang_set : Claims.bangbang_set := by
  intro E _ _ n m x y α β hn hm hα0 hα1 hβ0 hβ1
  obtain ⟨hex, huniq⟩ := StatFormal.TrimmedMMD.BangBang.bangbang_i E n m x y α β hn hm hα0 hα1 hβ0 hβ1
  set D := capped n α ×ˢ capped m β with hD
  have hDc : IsCompact D := (capped_compact n α).prod (capped_compact m β)
  have hqc : Continuous (qp x y) := by unfold qp; fun_prop
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨p, hp, hmin⟩ := hex; exact ⟨p, hp, hmin⟩
  · intro p hp p' hp' a b ha hb hab
    have hseg : a • p + b • p' = seg p p' b := by
      have ha' : a = 1 - b := by linarith
      ext i <;> simp [seg, ha'] <;> ring
    rw [hseg]
    have hmem : seg p p' b ∈ D :=
      ⟨capped_seg hp.1.1 hp'.1.1 hb (by linarith), capped_seg hp.1.2 hp'.1.2 hb (by linarith)⟩
    refine ⟨hmem, ?_⟩
    have hd : dvec x y p' = dvec x y p := (huniq p hp.1 p' hp'.1 hp.2 hp'.2).symm
    have hval : qp x y (seg p p' b) = qp x y p := by
      change ‖dvec x y (seg p p' b)‖ ^ 2 = ‖dvec x y p‖ ^ 2
      rw [dvec_seg, hd, sub_self, smul_zero, add_zero]
    intro r hr
    simp only [mem_ofPred_eq]
    rw [hval]; exact hp.2 hr
  · have hcl : IsClosed (trimSetEmp x y α β) := by
      have : trimSetEmp x y α β = D ∩ ⋂ r ∈ D, {p | qp x y p ≤ qp x y r} := by
        ext p; simp only [trimSetEmp, mem_inter_iff, mem_iInter, mem_ofPred_eq, IsMinOn, IsMinFilter,
          Filter.eventually_principal]
        rfl
      rw [this]
      exact hDc.isClosed.inter (isClosed_biInter fun r _ => isClosed_le hqc continuous_const)
    exact hDc.of_isClosed_subset hcl fun p hp => hp.1

end StatFormal.Wave30ah
