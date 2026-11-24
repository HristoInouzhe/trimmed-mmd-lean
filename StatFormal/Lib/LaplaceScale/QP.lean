import StatFormal.Wave30tz.Statements

/-!
# The quadratic program of the trimmed witness sees only the feature vectors (library, untrusted)

The objects of the quadratic program `eq:qp` of a two-sample `(x, y)` with feature map `φ` — the weighted sums `wsum`, the
value `qpVal`, the minimizer predicate `IsQPMin`, the witness `witness` and its own-term values `ownX`, `ownY` — are functions
of the feature vectors `φ(x_i)`, `φ(y_j)` alone. Two (feature map, sample) pairs with the same feature vectors, possibly on
different sample spaces, give the same objects (`wsum_congr`, `qpVal_congr`, `isQPMin_congr`, `witness_congr`, `ownX_congr`,
`ownY_congr`).

Typical use: rescaling the data, `x ↦ x/σ` with the feature map `φ_σ(u) = φ(σu)`, leaves every one of these objects unchanged.
-/

set_option linter.style.longLine false

noncomputable section

namespace StatFormal.LaplaceScale

open StatFormal.Wave30tz

variable {𝒳 𝒴 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {φ : 𝒳 → H} {ψ : 𝒴 → H} {n m : ℕ} {x : Fin n → 𝒳} {x' : Fin n → 𝒴} {y : Fin m → 𝒳} {y' : Fin m → 𝒴}

/-- Equal feature vectors give equal weighted sums `Σ_i w_i φ(x_i)`. -/
theorem wsum_congr (hx : ∀ i, ψ (x' i) = φ (x i)) (w : Fin n → ℝ) : wsum ψ x' w = wsum φ x w := by
  simp only [wsum, hx]

/-- Equal feature vectors give equal values `‖Σ_i w_iφ(x_i) − Σ_j v_jφ(y_j)‖` of the quadratic program. -/
theorem qpVal_congr (hx : ∀ i, ψ (x' i) = φ (x i)) (hy : ∀ j, ψ (y' j) = φ (y j)) (w : Fin n → ℝ) (v : Fin m → ℝ) :
    qpVal ψ x' y' w v = qpVal φ x y w v := by
  simp only [qpVal, wsum_congr hx, wsum_congr hy]

/-- Equal feature vectors give the same minimizers of the quadratic program. -/
theorem isQPMin_congr (hx : ∀ i, ψ (x' i) = φ (x i)) (hy : ∀ j, ψ (y' j) = φ (y j)) (α : ℝ) (w : Fin n → ℝ)
    (v : Fin m → ℝ) : IsQPMin ψ α x' y' w v ↔ IsQPMin φ α x y w v := by
  simp only [IsQPMin, qpVal_congr hx hy]

/-- Equal feature vectors give the same witness `(Σ_i w_iφ(x_i) − Σ_j v_jφ(y_j))/D̂`. -/
theorem witness_congr (hx : ∀ i, ψ (x' i) = φ (x i)) (hy : ∀ j, ψ (y' j) = φ (y j)) (w : Fin n → ℝ) (v : Fin m → ℝ) :
    witness ψ x' y' w v = witness φ x y w v := by
  simp only [witness, qpVal_congr hx hy, wsum_congr hx, wsum_congr hy]

/-- Equal feature vectors give the same own-term values at the `X`'s. -/
theorem ownX_congr (hx : ∀ i, ψ (x' i) = φ (x i)) (hy : ∀ j, ψ (y' j) = φ (y j)) (w : Fin n → ℝ) (v : Fin m → ℝ) :
    ownX ψ x' y' w v = ownX φ x y w v := by
  funext i
  simp only [ownX, witness_congr hx hy, qpVal_congr hx hy, hx]

/-- Equal feature vectors give the same own-term values at the `Y`'s. -/
theorem ownY_congr (hx : ∀ i, ψ (x' i) = φ (x i)) (hy : ∀ j, ψ (y' j) = φ (y j)) (w : Fin n → ℝ) (v : Fin m → ℝ) :
    ownY ψ x' y' w v = ownY φ x y w v := by
  funext j
  simp only [ownY, witness_congr hx hy, qpVal_congr hx hy, hy]

end StatFormal.LaplaceScale
