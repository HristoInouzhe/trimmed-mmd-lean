import StatFormal.Wave31tp.Statements
import StatFormal.Lib.NativeChar.Char

/-!
# Wave 31tp, route N: the native-space characterisation (untrusted proof file)

L18 (`native_char`, Wendland Thm 10.12, eq:newnative with `=`) from `Lib/NativeChar/Char.lean`: part (a) is
`NativeChar.native_le_norm`, part (b) is `NativeChar.native_char_rep`.
-/

noncomputable section
open MeasureTheory FourierTransform

namespace StatFormal.Wave31tp.RouteN

theorem native_char_route : Claims.native_char := by
  intro V _ _ _ _ _ H _ _ _ φ k₀ hc hi hφ
  exact ⟨fun g => NativeChar.native_le_norm hφ hc hi g, fun f hfc => NativeChar.native_char_rep hφ hc hi f hfc⟩

end StatFormal.Wave31tp.RouteN
