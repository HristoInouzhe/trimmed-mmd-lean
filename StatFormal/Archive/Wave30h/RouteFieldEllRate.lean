import StatFormal.Archive.Wave30h.RouteFieldEll
import StatFormal.Archive.Wave30h.RouteFieldJ

/-! # Route — `cor:field-ell`, the rate: `fieldell_rate_of` discharged by the journal `fieldJ_rate` (untrusted) -/

namespace StatFormal.Wave30h

theorem fieldell_rate : Claims.fieldell_rate := fieldell_rate_of fieldJ_rate

end StatFormal.Wave30h
