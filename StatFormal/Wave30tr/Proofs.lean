import StatFormal.Wave30tr.Statements
import StatFormal.Wave30tr.RouteEk
import StatFormal.Wave30tr.RouteDet
import StatFormal.Wave30tr.RouteEvents
import StatFormal.Wave30tr.RouteConst

/-!
# Proofs: wave 30tr, NOTE Theorem A (one joint one-sided two-sample supremum)

`thmA` is `RouteEvents.thmA_core` (Step 1 `RouteDet`, Steps 2–3 `RouteEvents`); `thmA_twosided` applies it at `δ/2` and
the certified union bound `TrimmedMMD.event_prob`; the constants are in `RouteConst` and `RouteEk`.
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave30tr

open StatFormal.TrimmedMMD.Unconditional

theorem thmA : Claims.thmA := by
  intro 𝒳 H _ _ _ _ _ φ κ D P Q _ _ δ n m hφ hκ hD hδ0 hδ1 hn hm
  exact thmA_core P Q hφ hκ hD hδ0 hδ1 hn hm

theorem thmA_twosided : Claims.thmA_twosided := by
  intro 𝒳 H _ _ _ _ _ φ κ D P Q _ _ δ n m hφ hκ hD hδ0 hδ1 hn hm
  obtain ⟨Ep, Em, hEpm, hEpp, hEmm, hEmp, ha, hb⟩ :=
    thmA_core (δ := δ / 2) P Q hφ hκ hD (by positivity) (by linarith) hn hm
  refine ⟨Ep, Em, hEpm, hEmm, hEpp, hEmp,
    StatFormal.TrimmedMMD.event_prob _ _ δ Ep Em hδ0 hδ1 hEpm hEmm hEpp hEmp, ?_⟩
  rintro z ⟨hzp, hzm⟩ α hα
  have h1 := (ha z hzp α hα).1
  have h2 := hb z hzm α hα
  rw [abs_le]; constructor <;> linarith

example : Claims.ek_closed := ek_closed
example : Claims.ek_le := ek_le
example : Claims.ek_tendsto := ek_tendsto
example : Claims.thmA := thmA
example : Claims.thmA_twosided := thmA_twosided
example : Claims.thmA_compare := thmA_compare
example : Claims.thmA_compare_half := thmA_compare_half
example : Claims.tauA_scale := tauA_scale

end StatFormal.Wave30tr
