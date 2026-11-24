import StatFormal.Wave30tx.Statements
import StatFormal.Archive.Wave30az.RouteWitness
import StatFormal.Wave30tl.RouteCrossing

/-!
# Route: shared helpers for wave 30tx (untrusted proof material)

* `Dpop_eq_norm`: for a minimum-norm element `d*` of `𝒞_α(P) − 𝒞_α(Q)`, `D_{α,k}(P,Q) = ‖d*‖`.
* `Demp_eq_norm`: at a minimiser of `eq:qp`, `D̂_{α,k} = ‖d̂‖` (`prop:bangbang`(i) via `Wave30az.witness_isMinNorm_gen`,
  no measurable singletons needed).
-/

noncomputable section
open MeasureTheory Set
open scoped Pointwise

namespace StatFormal.Wave30tx.RBasic

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.Projection

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem setDist_eq_of_isMinNorm {A B : Set H} {d : H} (hd : IsMinNorm (A - B) d) :
    setDist A B = ‖d‖ := by
  obtain ⟨⟨a, ha, b, hb, hab⟩, hmin⟩ := hd
  unfold setDist
  refine IsLeast.csInf_eq ⟨⟨a, ha, b, hb, by rw [← hab]⟩, ?_⟩
  rintro r ⟨a', ha', b', hb', rfl⟩
  exact hmin _ ⟨a', ha', b', hb', rfl⟩

theorem Dpop_eq_norm {φ : 𝒳 → H} {P Q : Measure 𝒳} {α : ℝ} {d : H}
    (hd : IsMinNorm (region φ α P - region φ α Q) d) : Dpop φ P Q α = ‖d‖ :=
  setDist_eq_of_isMinNorm hd

theorem witness_isMinNorm {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳) {pr : (Fin n → ℝ) × (Fin m → ℝ)}
    (hpr : pr ∈ capped n α ×ˢ capped m α)
    (hmin : IsMinOn (qp (fun i => φ (x i)) (fun j => φ (y j))) (capped n α ×ˢ capped m α) pr) :
    IsMinNorm (region φ α (empirical x) - region φ α (empirical y)) (StatFormal.Wave4b.witness φ x y pr) :=
  StatFormal.Wave30az.witness_isMinNorm_gen hn hm x y hφ hα0 hα1 hα0 hα1 hpr hmin

theorem Demp_eq_norm {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳) {pr : (Fin n → ℝ) × (Fin m → ℝ)}
    (hpr : pr ∈ capped n α ×ˢ capped m α)
    (hmin : IsMinOn (qp (fun i => φ (x i)) (fun j => φ (y j))) (capped n α ×ˢ capped m α) pr) :
    Demp φ x y α = ‖StatFormal.Wave4b.witness φ x y pr‖ :=
  setDist_eq_of_isMinNorm (witness_isMinNorm hφ hα0 hα1 hn hm x y hpr hmin)

end StatFormal.Wave30tx.RBasic
