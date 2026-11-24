import StatFormal.Archive.RobustEquality.Tax.Statements
import StatFormal.Lib.Tax.Ghost

/-!
# Proofs: `lem:tax` and `thm:ghost` (atomless classes) (untrusted proof file)

The frozen `Wdisc`, `tax`, `ballN` are definitionally the library's
`StatFormal.Foundations.Tax.{Wdisc, tax, ballN}`. Routes: the chain rule of relative entropy
(`Foundations.Tax.klRef_chain`) for `lem:tax`; for `thm:ghost`, the finite-support transfer
`Foundations.Tax.prob_ge_of_empMeasure` (ghost sample + birthday bound) and infinite tax of
finitely supported laws against atomless references.
-/

namespace StatFormal.RobustEquality.Tax

theorem tax_identity : Claims.tax_identity := by
  intro K _ k ε a c ν Q _ _ hs
  exact StatFormal.Foundations.Tax.Wdisc_eq hs ν Q

theorem tax_ball : Claims.tax_ball := by
  intro K _ k ε a c 𝒩 r Q _ hs hN
  refine ⟨fun hQ => StatFormal.Foundations.Tax.ballN_subset hs hN hQ, fun hatt h => ?_⟩
  exact (StatFormal.Foundations.Tax.mem_ballN_iff_of_attained hs hN r Q hatt).2 h

theorem ghost_atomless : Claims.ghost_atomless := by
  intro K _ _ n ε α cost 𝒩 r hn hε hcm hcb hN hatom hr hvalid P hP
  exact StatFormal.Foundations.Tax.ghost_atomless hn hε hcm hcb 𝒩 hN hatom r hr hvalid P

example : Claims.tax_identity := tax_identity
example : Claims.tax_ball := tax_ball
example : Claims.ghost_atomless := ghost_atomless

end StatFormal.RobustEquality.Tax
