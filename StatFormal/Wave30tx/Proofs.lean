import StatFormal.Wave30tx.RouteSep
import StatFormal.Wave30tx.RouteBasicIneq
import StatFormal.Wave30tx.RouteLocal
import StatFormal.Wave30tx.RouteRate
import StatFormal.Wave30tx.RouteCor
import StatFormal.Wave30tx.RouteContact
import StatFormal.Wave30tx.RouteAlpha
import StatFormal.Wave30tx.RouteNearA
import StatFormal.Wave30tx.RouteNearB

/-!
# Proofs — wave 30tx (untrusted; each theorem has the type of its frozen claim)

Routes: `RouteSep` (`lem:sepmargin`), `RouteBasicIneq` (`lem:basicineq`, CVaR duality on the regions), `RouteLocal`
(`lem:localmod`: symmetrisation, coordinatewise contraction, McDiarmid), `RouteRate` (`thm:trimrate`, its last sentence, the (A3)
parenthetical), `RouteCor` (`cor:trimrate`, Markov on shells), `RouteContact` (`lem:contact`, `P ⊓ Q`, the density form),
`RouteAlpha` (`prop:alphahat`), `RouteNearA`, `RouteNearB` (`rem:nearcontact` (a), (b), the latter with the analyticity of the
Gaussian witness functions along lines).
-/

namespace StatFormal.Wave30tx

theorem sepmargin : Claims.sepmargin := RSep.sepmargin

theorem basicineq : Claims.basicineq := RBasicIneq.basicineq

theorem localmod : Claims.localmod := RLocal.localmod

theorem trimrate : Claims.trimrate := RRate.trimrate_of basicineq localmod

theorem trimrate_inter : Claims.trimrate_inter := RRate.trimrate_inter_of basicineq localmod

theorem trimrate_A3 : Claims.trimrate_A3 := RRate.trimrate_A3

theorem cor_trimrate : Claims.cor_trimrate := RCor.cor_trimrate_of basicineq localmod

theorem contact_compact : Claims.contact_compact := RContact.contact_compact

theorem contact : Claims.contact := RContact.contact

theorem nearcontact_densities : Claims.nearcontact_densities := RContact.nearcontact_densities

theorem nearcontact_a : Claims.nearcontact_a := RNearA.nearcontact_a_of contact

theorem nearcontact_b : Claims.nearcontact_b := RNearB.nearcontact_b_of contact nearcontact_densities

theorem alphahat : Claims.alphahat := RAlpha.alphahat_of contact

theorem alphahat_schedule : Claims.alphahat_schedule := RAlpha.alphahat_schedule_of contact

end StatFormal.Wave30tx
