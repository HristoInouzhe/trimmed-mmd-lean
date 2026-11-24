import StatFormal.Archive.Wave28b.Statements
import StatFormal.Lib.CLT.PlugIn
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Route — the first two `θ`-derivatives of the i.i.d.-context objective (untrusted)

For a pool `x_0, …, x_{n−1}` (`n ≥ 1`) and validation points `y_0, …, y_{m−1}`, the frozen Wave 28b `jScoreIid`
(the frozen Wave 11b `jIid` at the score weights) is
`J^iid(θ) = V(θ) c(θ)^{−M} − λ_cov m^{−1} Σ_i (log e(θ, y_i) − log c(θ)) + λ_KL (f(θ)/c(θ) − log c(θ))`
with `c = P_n s_θ`, `V = m^{−1} Σ_i n^{−M} Σ_j ∏_k s_θ(x_{j_k}) L(y_i; x_j)`, `e(θ, z) = P_n(s_θ K(z, ·))`,
`f = P_n(s_θ log s_θ)` (`jScoreIid_rep`). Its first and second derivatives are the explicit formulas `jF1`, `jF2`
of the derivative pieces (`hasDerivAt_jScoreIid`, `hasDerivAt_gE`). The population analogues `D1`, `D2` are the
same formulas with `P₀` in place of `P_n`, `P_m`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal Real

namespace StatFormal.Wave28f

open StatFormal.Foundations.CLT

/-! ### Real formulas -/

/-- `c^{−(M+k)}`. -/
def zI (M k : ℕ) (c : ℝ) : ℝ := (c ^ (M + k))⁻¹

/-- `d/dθ [v c^{−M}]`. -/
def zD1 (M : ℕ) (v v1 c c1 : ℝ) : ℝ := v1 * zI M 0 c + v * (-(M : ℝ) * zI M 1 c * c1)

/-- `d²/dθ² [v c^{−M}]`. -/
def zD2 (M : ℕ) (v v1 v2 c c1 c2 : ℝ) : ℝ :=
  v2 * zI M 0 c + v1 * (-(M : ℝ) * zI M 1 c * c1) +
    (v1 * (-(M : ℝ) * zI M 1 c * c1) + v * (-(M : ℝ) * (-((M : ℝ) + 1) * zI M 2 c * c1 * c1 + zI M 1 c * c2)))

/-- `d/dθ log e`. -/
def lD1 (e e1 : ℝ) : ℝ := e1 / e

/-- `d²/dθ² log e`. -/
def lD2 (e e1 e2 : ℝ) : ℝ := (e2 * e - e1 * e1) / e ^ 2

/-- `d/dθ (f/c)`. -/
def qD1 (f f1 c c1 : ℝ) : ℝ := (f1 * c - f * c1) / c ^ 2

/-- `d²/dθ² (f/c)`. -/
def qD2 (f f1 f2 c c1 c2 : ℝ) : ℝ :=
  ((f2 * c + f1 * c1 - (f1 * c1 + f * c2)) * c ^ 2 - (f1 * c - f * c1) * (2 * c * c1)) / (c ^ 2) ^ 2

/-- The first derivative of the objective as a function of its pieces. -/
def jF1 (M : ℕ) (lc lK V V1 c c1 cv1 f f1 : ℝ) : ℝ :=
  zD1 M V V1 c c1 + lc * (-cv1) + lK * (qD1 f f1 c c1 - lD1 c c1)

/-- The second derivative of the objective as a function of its pieces. -/
def jF2 (M : ℕ) (lc lK V V1 V2 c c1 c2 cv2 f f1 f2 : ℝ) : ℝ :=
  zD2 M V V1 V2 c c1 c2 + lc * (-cv2) + lK * (qD2 f f1 f2 c c1 c2 - lD2 c c1 c2)

/-! ### Calculus of the formulas -/

section Calc
variable {M : ℕ} {t : ℝ}

lemma hasDerivAt_zI (k : ℕ) {c : ℝ → ℝ} {c1 : ℝ} (hc : HasDerivAt c c1 t) (hpos : 0 < c t) :
    HasDerivAt (fun t => zI M k (c t)) (-((M : ℝ) + k) * zI M (k + 1) (c t) * c1) t := by
  have h := (hc.fun_pow (M + k)).fun_inv (pow_ne_zero _ hpos.ne')
  unfold zI
  convert h using 1
  rcases Nat.eq_zero_or_pos (M + k) with h0 | hpos'
  · have hM : M = 0 := by omega
    have hk : k = 0 := by omega
    subst hM hk; simp
  · obtain ⟨N, hN⟩ : ∃ N, M + k = N + 1 := ⟨M + k - 1, by omega⟩
    have hc0 := hpos.ne'
    rw [show M + (k + 1) = N + 2 by omega, hN, Nat.add_sub_cancel]
    have : ((M : ℝ) + k) = (N : ℝ) + 1 := by exact_mod_cast hN
    rw [this]
    push_cast
    field_simp
    ring

lemma hasDerivAt_zD0 {V c : ℝ → ℝ} {V1 c1 : ℝ} (hV : HasDerivAt V V1 t) (hc : HasDerivAt c c1 t)
    (hpos : 0 < c t) : HasDerivAt (fun t => V t * zI M 0 (c t)) (zD1 M (V t) V1 (c t) c1) t := by
  have := hV.mul (hasDerivAt_zI (M := M) 0 hc hpos)
  convert this using 1
  unfold zD1; push_cast; ring

lemma hasDerivAt_zD1 {V V1 c c1 : ℝ → ℝ} {V2 c2 : ℝ} (hV : HasDerivAt V (V1 t) t) (hV1 : HasDerivAt V1 V2 t)
    (hc : HasDerivAt c (c1 t) t) (hc1 : HasDerivAt c1 c2 t) (hpos : 0 < c t) :
    HasDerivAt (fun t => zD1 M (V t) (V1 t) (c t) (c1 t)) (zD2 M (V t) (V1 t) V2 (c t) (c1 t) c2) t := by
  unfold zD1
  have h1 := hV1.mul (hasDerivAt_zI (M := M) 0 hc hpos)
  have h2 := hV.mul ((((hasDerivAt_zI (M := M) 1 hc hpos).const_mul (-(M : ℝ))).mul hc1))
  convert h1.add h2 using 1
  simp only [Pi.mul_apply]
  unfold zD2; push_cast; ring

lemma hasDerivAt_lD0 {e : ℝ → ℝ} {e1 : ℝ} (he : HasDerivAt e e1 t) (hpos : 0 < e t) :
    HasDerivAt (fun t => Real.log (e t)) (lD1 (e t) e1) t := he.log hpos.ne'

lemma hasDerivAt_lD1 {e e1 : ℝ → ℝ} {e2 : ℝ} (he : HasDerivAt e (e1 t) t) (he1 : HasDerivAt e1 e2 t)
    (hpos : 0 < e t) : HasDerivAt (fun t => lD1 (e t) (e1 t)) (lD2 (e t) (e1 t) e2) t := by
  unfold lD1 lD2
  exact he1.fun_div he hpos.ne'

lemma hasDerivAt_qD0 {f c : ℝ → ℝ} {f1 c1 : ℝ} (hf : HasDerivAt f f1 t) (hc : HasDerivAt c c1 t)
    (hpos : 0 < c t) : HasDerivAt (fun t => f t / c t) (qD1 (f t) f1 (c t) c1) t := by
  unfold qD1
  exact hf.fun_div hc hpos.ne'

lemma hasDerivAt_qD1 {f f1 c c1 : ℝ → ℝ} {f2 c2 : ℝ} (hf : HasDerivAt f (f1 t) t) (hf1 : HasDerivAt f1 f2 t)
    (hc : HasDerivAt c (c1 t) t) (hc1 : HasDerivAt c1 c2 t) (hpos : 0 < c t) :
    HasDerivAt (fun t => qD1 (f t) (f1 t) (c t) (c1 t)) (qD2 (f t) (f1 t) f2 (c t) (c1 t) c2) t := by
  unfold qD1 qD2
  have hnum := (hf1.mul hc).sub (hf.mul hc1)
  have hden := hc.fun_pow 2
  convert hnum.fun_div hden (pow_ne_zero 2 hpos.ne') using 1
  simp only [Pi.mul_apply, Pi.sub_apply]
  push_cast
  ring

end Calc

/-! ### Products over the context slots -/

section Prod
variable {Z : Type*} {M : ℕ}

/-- `∏_k s_θ(t_k)`. -/
def pr0 (s : ℝ → Z → ℝ) (θ : ℝ) (t : Fin M → Z) : ℝ := ∏ k, s θ (t k)

/-- `d/dθ ∏_k s_θ(t_k)`. -/
def pr1 (s s1 : ℝ → Z → ℝ) (θ : ℝ) (t : Fin M → Z) : ℝ := ∑ k, (∏ l ∈ univ.erase k, s θ (t l)) * s1 θ (t k)

/-- `d²/dθ² ∏_k s_θ(t_k)`. -/
def pr2 (s s1 s2 : ℝ → Z → ℝ) (θ : ℝ) (t : Fin M → Z) : ℝ :=
  ∑ k, ((∑ l ∈ univ.erase k, (∏ q ∈ (univ.erase k).erase l, s θ (t q)) * s1 θ (t l)) * s1 θ (t k) +
    (∏ l ∈ univ.erase k, s θ (t l)) * s2 θ (t k))

lemma hasDerivAt_finsetProd {u : Finset (Fin M)} {f f' : Fin M → ℝ → ℝ} {θ : ℝ}
    (hf : ∀ k, HasDerivAt (f k) (f' k θ) θ) :
    HasDerivAt (fun θ => ∏ l ∈ u, f l θ) (∑ k ∈ u, (∏ l ∈ u.erase k, f l θ) * f' k θ) θ := by
  have := HasDerivAt.fun_finsetProd (u := u) (f := f) (f' := fun k => f' k θ) (fun k _ => hf k)
  simpa only [smul_eq_mul] using this

lemma hasDerivAt_pr0 {s s1 : ℝ → Z → ℝ} {θ : ℝ} (hs : ∀ w, HasDerivAt (fun θ => s θ w) (s1 θ w) θ)
    (t : Fin M → Z) : HasDerivAt (fun θ => pr0 s θ t) (pr1 s s1 θ t) θ := by
  unfold pr0 pr1
  have := hasDerivAt_finsetProd (u := univ) (f := fun k θ => s θ (t k)) (f' := fun k θ => s1 θ (t k))
    (θ := θ) fun k => hs (t k)
  exact this

lemma hasDerivAt_pr1 {s s1 s2 : ℝ → Z → ℝ} {θ : ℝ} (hs : ∀ w, HasDerivAt (fun θ => s θ w) (s1 θ w) θ)
    (hs1 : ∀ w, HasDerivAt (fun θ => s1 θ w) (s2 θ w) θ) (t : Fin M → Z) :
    HasDerivAt (fun θ => pr1 s s1 θ t) (pr2 s s1 s2 θ t) θ := by
  unfold pr1 pr2
  refine HasDerivAt.fun_sum fun k _ => ?_
  exact (hasDerivAt_finsetProd (u := univ.erase k) (f := fun l θ => s θ (t l)) (f' := fun l θ => s1 θ (t l))
    (θ := θ) fun l => hs (t l)).mul (hs1 (t k))

end Prod

/-! ### The empirical and population pieces -/

section Pieces
variable {Z : Type*} {M : ℕ}

/-- `P_n φ_θ`. -/
def cE (φ : ℝ → Z → ℝ) (x : ℕ → Z) (n : ℕ) (θ : ℝ) : ℝ := pAvg (fun i : Fin n => x i) (φ θ)

/-- `m^{−1} Σ_i n^{−M} Σ_j pr_θ(x_j) L(y_i; x_j)`. -/
def VE (pr : ℝ → (Fin M → Z) → ℝ) (L : Z → (Fin M → Z) → ℝ) (x y : ℕ → Z) (n m : ℕ) (θ : ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i : Fin m, vstat (fun t => pr θ t * L (y i) t) (fun j : Fin n => x j)

/-- `e(θ, z) = P_n(φ_θ K(z, ·))`. -/
def eE (φ : ℝ → Z → ℝ) (K : Z → Z → ℝ) (x : ℕ → Z) (n : ℕ) (θ : ℝ) (z : Z) : ℝ :=
  pAvg (fun i : Fin n => x i) (fun w => φ θ w * K z w)

/-- `s log s` and its first two derivatives. -/
def sl0 (s : ℝ → Z → ℝ) (θ : ℝ) (w : Z) : ℝ := s θ w * Real.log (s θ w)
def sl1 (s s1 : ℝ → Z → ℝ) (θ : ℝ) (w : Z) : ℝ := s1 θ w * Real.log (s θ w) + s θ w * (s1 θ w / s θ w)
def sl2 (s s1 s2 : ℝ → Z → ℝ) (θ : ℝ) (w : Z) : ℝ :=
  s2 θ w * Real.log (s θ w) + s1 θ w * (s1 θ w / s θ w) +
    (s1 θ w * (s1 θ w / s θ w) + s θ w * ((s2 θ w * s θ w - s1 θ w * s1 θ w) / s θ w ^ 2))

/-- The coverage term `m^{−1} Σ_i (log e(θ, y_i) − log c(θ))` and its derivatives. -/
def cv0 (s : ℝ → Z → ℝ) (K : Z → Z → ℝ) (x y : ℕ → Z) (n m : ℕ) (θ : ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i : Fin m, (Real.log (eE s K x n θ (y i)) - Real.log (cE s x n θ))
def cv1 (s s1 : ℝ → Z → ℝ) (K : Z → Z → ℝ) (x y : ℕ → Z) (n m : ℕ) (θ : ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i : Fin m, (lD1 (eE s K x n θ (y i)) (eE s1 K x n θ (y i)) - lD1 (cE s x n θ) (cE s1 x n θ))
def cv2 (s s1 s2 : ℝ → Z → ℝ) (K : Z → Z → ℝ) (x y : ℕ → Z) (n m : ℕ) (θ : ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i : Fin m, (lD2 (eE s K x n θ (y i)) (eE s1 K x n θ (y i)) (eE s2 K x n θ (y i)) -
    lD2 (cE s x n θ) (cE s1 x n θ) (cE s2 x n θ))

/-- The explicit first derivative of `J^iid_{n,m}`. -/
def gE (M : ℕ) (s s1 : ℝ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (x y : ℕ → Z) (n m : ℕ)
    (lc lK θ : ℝ) : ℝ :=
  jF1 M lc lK (VE (pr0 s) L x y n m θ) (VE (pr1 s s1) L x y n m θ) (cE s x n θ) (cE s1 x n θ)
    (cv1 s s1 K x y n m θ) (cE (sl0 s) x n θ) (cE (sl1 s s1) x n θ)

/-- The explicit second derivative of `J^iid_{n,m}`. -/
def hE (M : ℕ) (s s1 s2 : ℝ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (x y : ℕ → Z) (n m : ℕ)
    (lc lK θ : ℝ) : ℝ :=
  jF2 M lc lK (VE (pr0 s) L x y n m θ) (VE (pr1 s s1) L x y n m θ) (VE (pr2 s s1 s2) L x y n m θ)
    (cE s x n θ) (cE s1 x n θ) (cE s2 x n θ) (cv2 s s1 s2 K x y n m θ) (cE (sl0 s) x n θ)
    (cE (sl1 s s1) x n θ) (cE (sl2 s s1 s2) x n θ)

variable [MeasurableSpace Z]

/-- `P₀ φ_θ`. -/
def cP (P0 : Measure Z) (φ : ℝ → Z → ℝ) (θ : ℝ) : ℝ := ∫ w, φ θ w ∂P0

/-- `∫∫ pr_θ(t) L(y; t) dP₀^{⊗M}(t) dP₀(y)`. -/
def VP (P0 : Measure Z) (pr : ℝ → (Fin M → Z) → ℝ) (L : Z → (Fin M → Z) → ℝ) (θ : ℝ) : ℝ :=
  ∫ y, hMean P0 (fun t => pr θ t * L y t) ∂P0

/-- `P₀(φ_θ K(z, ·))`. -/
def eP (P0 : Measure Z) (φ : ℝ → Z → ℝ) (K : Z → Z → ℝ) (θ : ℝ) (z : Z) : ℝ := ∫ w, φ θ w * K z w ∂P0

def cvP1 (P0 : Measure Z) (s s1 : ℝ → Z → ℝ) (K : Z → Z → ℝ) (θ : ℝ) : ℝ :=
  ∫ y, lD1 (eP P0 s K θ y) (eP P0 s1 K θ y) ∂P0 - lD1 (cP P0 s θ) (cP P0 s1 θ)
def cvP2 (P0 : Measure Z) (s s1 s2 : ℝ → Z → ℝ) (K : Z → Z → ℝ) (θ : ℝ) : ℝ :=
  ∫ y, lD2 (eP P0 s K θ y) (eP P0 s1 K θ y) (eP P0 s2 K θ y) ∂P0 - lD2 (cP P0 s θ) (cP P0 s1 θ) (cP P0 s2 θ)

/-- The population first derivative. -/
def D1 (M : ℕ) (P0 : Measure Z) (s s1 : ℝ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (lc lK θ : ℝ) : ℝ :=
  jF1 M lc lK (VP P0 (pr0 s) L θ) (VP P0 (pr1 s s1) L θ) (cP P0 s θ) (cP P0 s1 θ) (cvP1 P0 s s1 K θ)
    (cP P0 (sl0 s) θ) (cP P0 (sl1 s s1) θ)

/-- The population second derivative. -/
def D2 (M : ℕ) (P0 : Measure Z) (s s1 s2 : ℝ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ)
    (lc lK θ : ℝ) : ℝ :=
  jF2 M lc lK (VP P0 (pr0 s) L θ) (VP P0 (pr1 s s1) L θ) (VP P0 (pr2 s s1 s2) L θ) (cP P0 s θ) (cP P0 s1 θ)
    (cP P0 s2 θ) (cvP2 P0 s s1 s2 K θ) (cP P0 (sl0 s) θ) (cP P0 (sl1 s s1) θ) (cP P0 (sl2 s s1 s2) θ)

end Pieces

/-! ### Derivatives of the pieces -/

section DerivPieces
variable {Z : Type*} {M : ℕ} {s s1 s2 : ℝ → Z → ℝ} {L : Z → (Fin M → Z) → ℝ} {K : Z → Z → ℝ} {x y : ℕ → Z}
  {n m : ℕ} {θ : ℝ}

lemma hasDerivAt_pAvg {k : ℕ} (z : Fin k → Z) {φ φ' : ℝ → Z → ℝ}
    (h : ∀ w, HasDerivAt (fun θ => φ θ w) (φ' θ w) θ) :
    HasDerivAt (fun θ => pAvg z (φ θ)) (pAvg z (φ' θ)) θ := by
  unfold pAvg
  exact (HasDerivAt.fun_sum fun l _ => h (z l)).const_mul _

lemma hasDerivAt_cE {φ φ' : ℝ → Z → ℝ} (h : ∀ w, HasDerivAt (fun θ => φ θ w) (φ' θ w) θ) :
    HasDerivAt (fun θ => cE φ x n θ) (cE φ' x n θ) θ := hasDerivAt_pAvg _ h

lemma hasDerivAt_eE {φ φ' : ℝ → Z → ℝ} (h : ∀ w, HasDerivAt (fun θ => φ θ w) (φ' θ w) θ) (z : Z) :
    HasDerivAt (fun θ => eE φ K x n θ z) (eE φ' K x n θ z) θ :=
  hasDerivAt_pAvg (φ := fun θ w => φ θ w * K z w) (φ' := fun θ w => φ' θ w * K z w) _
    fun w => (h w).mul_const _

lemma hasDerivAt_VE {pr pr' : ℝ → (Fin M → Z) → ℝ} (h : ∀ t, HasDerivAt (fun θ => pr θ t) (pr' θ t) θ) :
    HasDerivAt (fun θ => VE pr L x y n m θ) (VE pr' L x y n m θ) θ := by
  unfold VE vstat
  refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun i _ => HasDerivAt.const_mul _
    (HasDerivAt.fun_sum fun j _ => (h _).mul_const _))

lemma hasDerivAt_sl0 (hs : ∀ w, HasDerivAt (fun θ => s θ w) (s1 θ w) θ) (hpos : ∀ w, 0 < s θ w) (w : Z) :
    HasDerivAt (fun θ => sl0 s θ w) (sl1 s s1 θ w) θ := by
  unfold sl0 sl1
  exact (hs w).mul ((hs w).log (hpos w).ne')

lemma hasDerivAt_sl1 (hs : ∀ w, HasDerivAt (fun θ => s θ w) (s1 θ w) θ)
    (hs1 : ∀ w, HasDerivAt (fun θ => s1 θ w) (s2 θ w) θ) (hpos : ∀ w, 0 < s θ w) (w : Z) :
    HasDerivAt (fun θ => sl1 s s1 θ w) (sl2 s s1 s2 θ w) θ := by
  unfold sl1 sl2
  have h1 := (hs1 w).mul ((hs w).log (hpos w).ne')
  have h2 := (hs w).mul ((hs1 w).fun_div (hs w) (hpos w).ne')
  exact h1.add h2

variable {sm Kmin : ℝ}

lemma cE_ge (hn : 1 ≤ n) {φ : ℝ → Z → ℝ} (hφ : ∀ w, sm ≤ φ θ w) : sm ≤ cE φ x n θ :=
  pAvg_ge hn hφ _

lemma eE_ge (hn : 1 ≤ n) (hsm : 0 < sm) (hs : ∀ w, sm ≤ s θ w) (hK : ∀ z w, Kmin ≤ K z w) (hKm : 0 < Kmin)
    (z : Z) : sm * Kmin ≤ eE s K x n θ z :=
  pAvg_ge hn (fun w => mul_le_mul (hs w) (hK z w) hKm.le ((hsm.le.trans (hs w)))) _

lemma hasDerivAt_cv0 (hn : 1 ≤ n) (hsm : 0 < sm) (hs : ∀ w, HasDerivAt (fun θ => s θ w) (s1 θ w) θ)
    (hsb : ∀ w, sm ≤ s θ w) (hK : ∀ z w, Kmin ≤ K z w) (hKm : 0 < Kmin) :
    HasDerivAt (fun θ => cv0 s K x y n m θ) (cv1 s s1 K x y n m θ) θ := by
  unfold cv0 cv1
  refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun i _ => ?_)
  exact (hasDerivAt_lD0 (hasDerivAt_eE (K := K) (x := x) (n := n) hs (y i))
    (lt_of_lt_of_le (by positivity) (eE_ge hn hsm hsb hK hKm (y i)))).sub
    (hasDerivAt_lD0 (hasDerivAt_cE (x := x) (n := n) hs) (hsm.trans_le (cE_ge hn hsb)))

lemma hasDerivAt_cv1 (hn : 1 ≤ n) (hsm : 0 < sm) (hs : ∀ w, HasDerivAt (fun θ => s θ w) (s1 θ w) θ)
    (hs1 : ∀ w, HasDerivAt (fun θ => s1 θ w) (s2 θ w) θ)
    (hsb : ∀ w, sm ≤ s θ w) (hK : ∀ z w, Kmin ≤ K z w) (hKm : 0 < Kmin) :
    HasDerivAt (fun θ => cv1 s s1 K x y n m θ) (cv2 s s1 s2 K x y n m θ) θ := by
  unfold cv1 cv2
  refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun i _ => ?_)
  exact (hasDerivAt_lD1 (hasDerivAt_eE (K := K) (x := x) (n := n) hs (y i))
    (hasDerivAt_eE (K := K) (x := x) (n := n) hs1 (y i))
    (lt_of_lt_of_le (by positivity) (eE_ge hn hsm hsb hK hKm (y i)))).sub
    (hasDerivAt_lD1 (hasDerivAt_cE (x := x) (n := n) hs) (hasDerivAt_cE (x := x) (n := n) hs1)
      (hsm.trans_le (cE_ge hn hsb)))

/-- The representation of `J^iid` by its pieces. -/
def jRep (M : ℕ) (s : ℝ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (x y : ℕ → Z) (n m : ℕ)
    (lc lK θ : ℝ) : ℝ :=
  VE (pr0 s) L x y n m θ * zI M 0 (cE s x n θ) + lc * (-cv0 s K x y n m θ) +
    lK * (cE (sl0 s) x n θ / cE s x n θ - Real.log (cE s x n θ))

lemma hasDerivAt_jRep (hn : 1 ≤ n) (hsm : 0 < sm) (hs : ∀ w, HasDerivAt (fun θ => s θ w) (s1 θ w) θ)
    (hsb : ∀ w, sm ≤ s θ w) (hK : ∀ z w, Kmin ≤ K z w) (hKm : 0 < Kmin) (lc lK : ℝ) :
    HasDerivAt (fun θ => jRep M s L K x y n m lc lK θ) (gE M s s1 L K x y n m lc lK θ) θ := by
  have hpos : ∀ w, 0 < s θ w := fun w => hsm.trans_le (hsb w)
  have hc := hasDerivAt_cE (x := x) (n := n) hs
  have hcpos : 0 < cE s x n θ := hsm.trans_le (cE_ge hn hsb)
  have h1 := hasDerivAt_zD0 (M := M) (hasDerivAt_VE (L := L) (x := x) (y := y) (n := n) (m := m)
    (fun t => hasDerivAt_pr0 hs t)) hc hcpos
  have h2 := (hasDerivAt_cv0 (x := x) (y := y) (m := m) hn hsm hs hsb hK hKm).neg.const_mul lc
  have h3 := ((hasDerivAt_qD0 (hasDerivAt_cE (x := x) (n := n) (hasDerivAt_sl0 hs hpos)) hc hcpos).sub
    (hasDerivAt_lD0 hc hcpos)).const_mul lK
  unfold jRep gE jF1
  exact (h1.add h2).add h3

lemma hasDerivAt_gE (hn : 1 ≤ n) (hsm : 0 < sm) (hs : ∀ w, HasDerivAt (fun θ => s θ w) (s1 θ w) θ)
    (hs1 : ∀ w, HasDerivAt (fun θ => s1 θ w) (s2 θ w) θ)
    (hsb : ∀ w, sm ≤ s θ w) (hK : ∀ z w, Kmin ≤ K z w) (hKm : 0 < Kmin) (lc lK : ℝ) :
    HasDerivAt (fun θ => gE M s s1 L K x y n m lc lK θ) (hE M s s1 s2 L K x y n m lc lK θ) θ := by
  have hpos : ∀ w, 0 < s θ w := fun w => hsm.trans_le (hsb w)
  have hc := hasDerivAt_cE (x := x) (n := n) hs
  have hc1 := hasDerivAt_cE (x := x) (n := n) hs1
  have hcpos : 0 < cE s x n θ := hsm.trans_le (cE_ge hn hsb)
  have h1 := hasDerivAt_zD1 (M := M) (hasDerivAt_VE (L := L) (x := x) (y := y) (n := n) (m := m)
    (fun t => hasDerivAt_pr0 hs t)) (hasDerivAt_VE (L := L) (x := x) (y := y) (n := n) (m := m)
    (fun t => hasDerivAt_pr1 hs hs1 t)) hc hc1 hcpos
  have h2 := (hasDerivAt_cv1 (x := x) (y := y) (m := m) hn hsm hs hs1 hsb hK hKm).neg.const_mul lc
  have h3 := ((hasDerivAt_qD1 (hasDerivAt_cE (x := x) (n := n) (hasDerivAt_sl0 hs hpos))
    (hasDerivAt_cE (x := x) (n := n) (hasDerivAt_sl1 hs hs1 hpos)) hc hc1 hcpos).sub
    (hasDerivAt_lD1 hc hc1 hcpos)).const_mul lK
  unfold gE hE jF1 jF2
  exact (h1.add h2).add h3

end DerivPieces

/-! ### The representation of `J^iid_{n,m}` -/

section Rep
variable {Z : Type*} {M : ℕ}

lemma jScoreIid_rep {s : ℝ → Z → ℝ} (L : Z → (Fin M → Z) → ℝ) {K : Z → Z → ℝ} (hpos : ∀ θ w, 0 < s θ w)
    (hKpos : ∀ z w, 0 < K z w) (x y : ℕ → Z) {n : ℕ} (hn : 1 ≤ n) (m : ℕ) (lc lK θ : ℝ) :
    StatFormal.Wave28b.jScoreIid s L K x y n m lc lK θ = jRep M s L K x y n m lc lK θ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set S : ℝ := ∑ l : Fin n, s θ (x l) with hS
  have hSpos : 0 < S := Finset.sum_pos (fun l _ => hpos θ (x l)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hc : cE s x n θ = (n : ℝ)⁻¹ * S := rfl
  have hcpos : 0 < cE s x n θ := by rw [hc]; positivity
  -- risk
  have hrisk : (1 / (m : ℝ)) * ∑ i : Fin m, ∑ j : Fin M → Fin n,
      StatFormal.ICL.Cond.iidLaw (StatFormal.Wave11b.wScore s (fun i : Fin n => x i) θ) M j *
        L ((fun i : Fin m => y i) i) ((fun i : Fin n => x i) ∘ j) =
      VE (pr0 s) L x y n m θ * zI M 0 (cE s x n θ) := by
    unfold VE vstat zI pr0 StatFormal.ICL.Cond.iidLaw StatFormal.Wave11b.wScore
    rw [hc, Nat.add_zero]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    dsimp only [Function.comp_apply]
    rw [← hS]
    simp only [mul_pow, inv_pow]
    field_simp
  -- coverage
  have hcov : ∀ z : Z, ∑ l : Fin n, StatFormal.Wave11b.wScore s (fun i : Fin n => x i) θ l * K z (x l) =
      eE s K x n θ z / cE s x n θ := by
    intro z
    unfold StatFormal.Wave11b.wScore eE pAvg
    rw [hc]
    dsimp only
    rw [← hS, mul_div_mul_left _ _ (inv_ne_zero hn0.ne'), Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hepos : ∀ z, 0 < eE s K x n θ z := fun z =>
    mul_pos (inv_pos.2 hn0) (Finset.sum_pos (fun l _ => mul_pos (hpos θ _) (hKpos z _)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
  -- relative entropy
  have hkl : StatFormal.ICL.Diag.klUnif n (StatFormal.Wave11b.wScore s (fun i : Fin n => x i) θ) =
      cE (sl0 s) x n θ / cE s x n θ - Real.log (cE s x n θ) := by
    unfold StatFormal.ICL.Diag.klUnif StatFormal.Wave11b.wScore
    have hlog : ∀ l : Fin n, Real.log ((n : ℝ) * (s θ (x l) / S)) = Real.log (s θ (x l)) - Real.log (cE s x n θ) := by
      intro l
      rw [hc, show (n : ℝ) * (s θ (x l) / S) = s θ (x l) / ((n : ℝ)⁻¹ * S) by field_simp,
        Real.log_div (hpos θ (x l)).ne' (by positivity)]
    dsimp only
    rw [← hS]
    simp_rw [hlog, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, ← hS, div_self hSpos.ne', one_mul]
    unfold cE sl0 pAvg
    dsimp only
    rw [← hS, mul_div_mul_left _ _ (inv_ne_zero hn0.ne'), Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  unfold StatFormal.Wave28b.jScoreIid StatFormal.Wave11b.jIid jRep cv0
  rw [hrisk, hkl]
  simp_rw [hcov]
  have hl : ∀ i : Fin m, Real.log (eE s K x n θ (y i) / cE s x n θ) =
      Real.log (eE s K x n θ (y i)) - Real.log (cE s x n θ) := fun i =>
    Real.log_div (hepos _).ne' hcpos.ne'
  simp_rw [hl]
  rw [one_div]
  ring

end Rep

end StatFormal.Wave28f
