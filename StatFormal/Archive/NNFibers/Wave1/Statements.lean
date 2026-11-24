import StatFormal.Archive.NNFibers.Statements
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# FROZEN STATEMENTS — embedded solution fibers, wave 1: exhaustion, exact decomposition, codimension

Source: `proliferation-and-geometry-in-nns/paper_revised.tex` (verbatim in
`inventory/extracted/proliferation-nns.md`): `eq:net` (l.341), `ass:ident` (l.368), splittings and zero-type
groups (l.443-452), `def:structures`, `def:pieces`, `eq:dim` (l.454-488), `lem:min-reduced` (l.506),
`eq:data` (l.521), `lem:exhaust` (l.559), `ass:meas` (l.641), `thm:decomp` with the display before it
(l.660-678), `eq:codim-s` (l.893), `lem:codim-blockcount` (l.1100). Results are for activations satisfying
`ass:ident` (e.g. `σ = exp`, `prop:exp-ident`); `rmk:symmetry-factor` (corrected 2026-10-13) — the
`tanh` failure — is the frozen `NNFibers.Claims.symmetry_factor_false`.

Covered:
* `min_reduced`: `lem:min-reduced` (functionally minimal ⇒ distinct incoming weights, nonzero outgoing);
* `lam_subset_fiber`: `Λ^m_q ⊆ F^m_q` for **every** activation (first half of `lem:exhaust`);
* `exhaust`: `lem:exhaust`, `Λ^m_q = F^m_q` under `ass:ident` (with `ρ(θ*_q) = q`);
* `card_labPart`: `|𝒟_{q,m}| = T(q,m)` (frozen `T`; the counting side of `prop:disjoint`);
* `pq_sum`: `p_q(m) = Σ_Γ μ_m(B(Γ)) = T(q,m)·E_{Γ∼U_{q,m}}[μ_m(B(Γ))]` (display before `thm:decomp`);
* `decomp`: `thm:decomp`;
* `dim_closure`: `Γ̄_s` is a (nonempty) affine subspace of dimension `j·d_in + (m−q−j)·d_out` (`eq:dim`);
* `codim_blockcount`: `eq:codim-s` and `eq:codim-K`; `codim_balanced`: `c_s = d(m+q)` when `d_in = d_out = d`.
Not covered (declared): `ass:UA` (not needed: the claims hold for every `σ : ℝ → ℝ`, generalisation);
`prop:exp-ident` (`σ = exp` satisfies `ass:ident`); the geometric half of `prop:disjoint` (pieces ↔ labelled
partitions, disjointness), so in `decomp` the piece set `𝒞_{q,m}` *is* `𝒟_{q,m}`; that `Γ̃_s` is dense in
`Γ̄_s`; the training map `A_m` and the family rule (only the resulting basins `B_q`, `B(Γ)` enter).

Encodings (see card):
* a parameter of width `m` is `θ : Fin m → (ℝ^{d_in} × ℝ^{d_out})` (unit `u` = `(ω_u, a_u)`), `ℝ^d = Fin d → ℝ`;
  `f_θ(x) = Σ_u σ(ω_u·x) a_u`; `θ ∼ θ*` is equality of functions on all of `ℝ^{d_in}`;
* `ρ(θ*) = q` is "no network of width `q' < q` represents `f_{θ*}`";
* `ass:ident`'s finite compositions are the inductive closure `Generated` on parameters of any width written as
  lists of units: a permutation (`List.Perm`), a splitting of any unit into `n ≥ 1` copies with the same
  incoming weight and outgoing weights summing to the original, an appended zero-type group of `b ≥ 1` units
  with a common (arbitrary) incoming weight and outgoing weights summing to `0`;
* a canonical piece `P_π Γ̃_s` (all structures `s ∈ 𝒮_{q,m}`, all unit permutations) is encoded by a surjective
  group map `g : Fin m → Fin q ⊕ Fin j` (`inl i`: a copy of original unit `i`; `inr ℓ`: the `ℓ`-th zero-type
  group) and free directions `ω'`; surjectivity is `n_i, b_ℓ ≥ 1`, and ordering the zero-type groups by size
  (`b_1 ≤ … ≤ b_j`) changes nothing since the `ω'_ℓ` are free. `Λ^m_q` keeps the non-redundancy inequalities;
  `Γ̄_s` (`closureSet`) drops them;
* `𝒞_{q,m} ≅ 𝒟_{q,m}` (`eq:data`) is the type `LabPart q m` of partitions of `Fin m` with an injective labelling
  of `q` blocks; `U_{q,m}` is uniform on it (average = sum / cardinality);
* `ass:meas`: `B_q` measurable, the piece rule a total function `B_q → 𝒞_{q,m}` (modelled on all of `Ω`; only its
  values on `B_q` matter) with measurable fibres in `B_q`; `B(Γ) := {x ∈ B_q | rule x = Γ}`, so the partition
  and the consistency clause hold by construction; `μ_m` a probability measure; `p_q = μ_m.real B_q`;
* the setting `r < k < m` of the paper is assumed in `decomp`. Since the identity alone would survive `p_k = 0`
  through `x/0 = 0`, `decomp` also concludes `T(k,m) > 0` and `E_{U_{k,m}}[μ_m(B(Γ))] > 0`, so `0 < p_k` is
  load-bearing and both denominators are certified genuine;
* `T(q,m) = |𝒞_{q,m}|` (pieces ↔ labelled partitions) rests on the geometric half of `prop:disjoint`, which is
  declared and **not covered**: `decomp` and `pq_sum` are stated over `𝒟_{q,m}` and do not reference `σ`, `net`
  or `InLam`;
* dimensions/codimensions are `Module.finrank` of the direction, stated in `ℤ` (no `ℕ` subtraction).
Hash-lock: DRAFT, not yet in `certify/statements.lock`; on approval this becomes `Wave1/Statements.lean`.
-/

noncomputable section
open Finset MeasureTheory

namespace StatFormal.NNFibers.Wave1

/-- A hidden unit `(ω, a)`: incoming weight `ω ∈ ℝ^{d_in}`, outgoing weight `a ∈ ℝ^{d_out}`. -/
abbrev Neuron (din dout : ℕ) : Type := (Fin din → ℝ) × (Fin dout → ℝ)

/-- `eq:net`: `f_θ(x) = Σ_u a_u σ(ω_u · x)`. -/
def net {din dout m : ℕ} (σ : ℝ → ℝ) (θ : Fin m → Neuron din dout) (x : Fin din → ℝ) : Fin dout → ℝ :=
  ∑ u, σ (∑ k, (θ u).1 k * x k) • (θ u).2

/-- `ρ(θ) = q` for `θ ∈ Θ_q`: no narrower network represents `f_θ`. -/
def FunctionallyMinimal {din dout q : ℕ} (σ : ℝ → ℝ) (θ : Fin q → Neuron din dout) : Prop :=
  ∀ q' < q, ∀ ϑ : Fin q' → Neuron din dout, net σ ϑ ≠ net σ θ

/-- The closure of `{θ*}` under `ass:ident`'s operations (i)–(iii), on lists of units. -/
inductive Generated {din dout : ℕ} (θs : List (Neuron din dout)) : List (Neuron din dout) → Prop
  | base : Generated θs θs
  | perm {l l' : List (Neuron din dout)} : Generated θs l → l.Perm l' → Generated θs l'
  | split {l₁ l₂ : List (Neuron din dout)} {v : Neuron din dout} (c : List (Fin dout → ℝ)) :
      Generated θs (l₁ ++ v :: l₂) → c ≠ [] → c.sum = v.2 →
      Generated θs (l₁ ++ c.map (fun a => (v.1, a)) ++ l₂)
  | zero {l : List (Neuron din dout)} (ω' : Fin din → ℝ) (c : List (Fin dout → ℝ)) :
      Generated θs l → c ≠ [] → c.sum = 0 → Generated θs (l ++ c.map (fun a => (ω', a)))

/-- `ass:ident` for the representative `θ*_q` at width `m`. -/
def AssIdent {din dout q : ℕ} (σ : ℝ → ℝ) (θs : Fin q → Neuron din dout) (m : ℕ) : Prop :=
  FunctionallyMinimal σ θs ∧
    ∀ θ : Fin m → Neuron din dout, net σ θ = net σ θs → Generated (List.ofFn θs) (List.ofFn θ)

/-- `θ ∈ Λ^m_q` (`def:pieces`, `eq:Lambda`): `θ` lies in some canonical piece `P_π Γ̃_s(θ*_q)`. -/
def InLam {din dout q m : ℕ} (θs : Fin q → Neuron din dout) (θ : Fin m → Neuron din dout) : Prop :=
  ∃ (j : ℕ) (g : Fin m → Fin q ⊕ Fin j) (ω' : Fin j → Fin din → ℝ),
    Function.Surjective g ∧ Function.Injective ω' ∧ (∀ ℓ i, ω' ℓ ≠ (θs i).1) ∧
    (∀ u, (θ u).1 = Sum.elim (fun i => (θs i).1) ω' (g u)) ∧
    (∀ i, ∑ u ∈ univ.filter (fun u => g u = Sum.inl i), (θ u).2 = (θs i).2) ∧
    (∀ ℓ, ∑ u ∈ univ.filter (fun u => g u = Sum.inr ℓ), (θ u).2 = 0)

/-- `Γ̄_s(θ*_q)`: the equalities of `def:pieces` for the group map `g`, without the collision inequalities. -/
def closureSet {din dout q m j : ℕ} (θs : Fin q → Neuron din dout) (g : Fin m → Fin q ⊕ Fin j) :
    Set (Fin m → Neuron din dout) :=
  {θ | (∃ ω' : Fin j → Fin din → ℝ, ∀ u, (θ u).1 = Sum.elim (fun i => (θs i).1) ω' (g u)) ∧
    (∀ i, ∑ u ∈ univ.filter (fun u => g u = Sum.inl i), (θ u).2 = (θs i).2) ∧
    (∀ ℓ, ∑ u ∈ univ.filter (fun u => g u = Sum.inr ℓ), (θ u).2 = 0)}

/-- `eq:data`: labelled partitions `(π, ι)` of `[m]` with `q` injectively labelled blocks. -/
abbrev LabPart (q m : ℕ) : Type := Σ P : Finpartition (univ : Finset (Fin m)), (Fin q ↪ P.parts)

/-- `B(Γ)`: initialisations assigned to family `q` (`B_q`) whose piece rule returns `Γ`. -/
def pieceBasin {Ω : Type*} {q m : ℕ} (B : Set Ω) (rule : Ω → LabPart q m) (Γ : LabPart q m) : Set Ω :=
  {x | x ∈ B ∧ rule x = Γ}

/-- `E_{Γ∼U_{q,m}}[μ_m(B(Γ))]`. -/
def avgBasin {Ω : Type*} [MeasurableSpace Ω] {q m : ℕ} (μ : Measure Ω) (B : Set Ω)
    (rule : Ω → LabPart q m) : ℝ :=
  (∑ Γ, μ.real (pieceBasin B rule Γ)) / Fintype.card (LabPart q m)

namespace Claims

/-- `lem:min-reduced`. -/
def min_reduced : Prop :=
  ∀ (din dout q : ℕ) (σ : ℝ → ℝ) (θs : Fin q → Neuron din dout), FunctionallyMinimal σ θs →
    Function.Injective (fun i => (θs i).1) ∧ ∀ i, (θs i).2 ≠ 0

/-- `lem:exhaust`, inclusion `Λ^m_q ⊆ F^m_q` ("by construction"), for any activation and any `θ*`. -/
def lam_subset_fiber : Prop :=
  ∀ (din dout q m : ℕ) (σ : ℝ → ℝ) (θs : Fin q → Neuron din dout) (θ : Fin m → Neuron din dout),
    InLam θs θ → net σ θ = net σ θs

/-- `lem:exhaust`: under `ass:ident`, `Λ^m_q = F^m_q := {θ ∈ Θ_m : f_θ ≡ f_{θ*_q}}`. -/
def exhaust : Prop :=
  ∀ (din dout q m : ℕ) (σ : ℝ → ℝ) (θs : Fin q → Neuron din dout), AssIdent σ θs m →
    {θ : Fin m → Neuron din dout | InLam θs θ} = {θ | net σ θ = net σ θs}

/-- `|𝒟_{q,m}| = T(q,m)`. -/
def card_labPart : Prop :=
  ∀ q m : ℕ, Fintype.card (LabPart q m) = StatFormal.NNFibers.T q m

/-- Display before `thm:decomp`: `p_q(m) = Σ_Γ μ_m(B(Γ)) = T(q,m) E_{U_{q,m}}[μ_m(B(Γ))]`. -/
def pq_sum : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (q m : ℕ) (B : Set Ω)
    (rule : Ω → LabPart q m), q ≤ m → MeasurableSet B → (∀ Γ, MeasurableSet (pieceBasin B rule Γ)) →
      μ.real B = ∑ Γ, μ.real (pieceBasin B rule Γ) ∧
      μ.real B = (StatFormal.NNFibers.T q m : ℝ) * avgBasin μ B rule

/-- `thm:decomp`: if `p_k(m) > 0`, both denominators are genuine (`T(k,m) > 0`, `E_{U_{k,m}}[μ_m(B(Γ))] > 0`)
and `Q_{r,k}(m) = T(r,m)/T(k,m) · H_{r,k}(m)`. -/
def decomp : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (r k m : ℕ) (Br Bk : Set Ω)
    (ruler : Ω → LabPart r m) (rulek : Ω → LabPart k m), r < k → k < m →
    MeasurableSet Br → MeasurableSet Bk →
    (∀ Γ, MeasurableSet (pieceBasin Br ruler Γ)) → (∀ Γ, MeasurableSet (pieceBasin Bk rulek Γ)) →
    0 < μ.real Bk →
      0 < (StatFormal.NNFibers.T k m : ℝ) ∧ 0 < avgBasin μ Bk rulek ∧
      μ.real Br / μ.real Bk = ((StatFormal.NNFibers.T r m : ℝ) / StatFormal.NNFibers.T k m) *
        (avgBasin μ Br ruler / avgBasin μ Bk rulek)

/-- `eq:dim`: `Γ̄_s` is an affine subspace of `Θ_m` of dimension `j·d_in + (m−q−j)·d_out`. -/
def dim_closure : Prop :=
  ∀ (din dout q m j : ℕ) (θs : Fin q → Neuron din dout) (g : Fin m → Fin q ⊕ Fin j),
    Function.Surjective g →
      ∃ A : AffineSubspace ℝ (Fin m → Neuron din dout), (A : Set _) = closureSet θs g ∧
        (Module.finrank ℝ A.direction : ℤ) = j * din + ((m : ℤ) - q - j) * dout

/-- `eq:codim-s` and `lem:codim-blockcount` (`eq:codim-K`, `K = q + j`): the codimension of `Γ̄_s` in `Θ_m`. -/
def codim_blockcount : Prop :=
  ∀ (din dout q m j : ℕ) (θs : Fin q → Neuron din dout) (g : Fin m → Fin q ⊕ Fin j)
    (A : AffineSubspace ℝ (Fin m → Neuron din dout)),
    Function.Surjective g → (A : Set _) = closureSet θs g →
      (Module.finrank ℝ (Fin m → Neuron din dout) : ℤ) - Module.finrank ℝ A.direction
          = ((m : ℤ) - j) * din + ((q : ℤ) + j) * dout ∧
      (Module.finrank ℝ (Fin m → Neuron din dout) : ℤ) - Module.finrank ℝ A.direction
          = ((m : ℤ) + q) * din + ((q : ℤ) + j) * ((dout : ℤ) - din)

/-- `lem:codim-blockcount`, last clause: when `d_in = d_out = d`, `c_s = d(m+q)` for every structure. -/
def codim_balanced : Prop :=
  ∀ (d q m j : ℕ) (θs : Fin q → Neuron d d) (g : Fin m → Fin q ⊕ Fin j)
    (A : AffineSubspace ℝ (Fin m → Neuron d d)),
    Function.Surjective g → (A : Set _) = closureSet θs g →
      (Module.finrank ℝ (Fin m → Neuron d d) : ℤ) - Module.finrank ℝ A.direction = (d : ℤ) * (m + q)

end Claims
end StatFormal.NNFibers.Wave1
