import StatFormal.Archive.OTFD.Wave7a.Statements
import StatFormal.Archive.OTFD.Wave4.RouteCertificate
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Lattice
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Route: B `lem:oos-potential`

* (a) `‖u − Z_j‖²_M = ‖u‖²_M − ⟨b_j,u⟩ + ‖Z_j‖²_M` (`M` symmetric), and both softmax and the simplex
  projection are invariant to a common shift of the scores.
* (b) The subgradient inequality `ψ(y) ≥ ψ(u) + ⟨Σ_j q_j(u) b_j, y − u⟩` (Jensen for log-sum-exp, the maximising
  property of the projection for `Φ`), plus continuity of the weights, gives convexity and differentiability
  (the frozen-route lemmas `convexOn_of_subgrad`, `hasFDerivAt_of_subgrad` of Wave 4).
* (c) Moreau envelope of the Laguerre potential: proximal points exist (compact sublevel set), satisfy the
  variational inequality `φ(z) ≥ φ(p) + ⟨(y − p)/ε₀, z − p⟩` (limit `t ↓ 0` along a segment), hence are unique and
  firmly nonexpansive; the envelope then has the subgradient `(y − P(y))/ε₀`, which is Lipschitz.
-/

noncomputable section
open Finset Matrix Filter Topology Set

namespace StatFormal.OTFD.Wave7a

open StatFormal.OTFD.Bands StatFormal.OTFD.Wave4 StatFormal.OTFD.Wave2

variable {n K : ℕ}

/-! ### (a) affine scores -/

lemma transpose_of_posDef {M : Matrix (Fin K) (Fin K) ℝ} (hM : M.PosDef) : Mᵀ = M := by
  have := hM.isHermitian.eq
  rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma mnormSq_sub {M : Matrix (Fin K) (Fin K) ℝ} (hM : M.PosDef) (u z : Fin K → ℝ) :
    mnormSq M (u - z) = mnormSq M u - ((2 : ℝ) • (M *ᵥ z)) ⬝ᵥ u + mnormSq M z := by
  have hs : u ⬝ᵥ (M *ᵥ z) = z ⬝ᵥ (M *ᵥ u) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, transpose_of_posDef hM, dotProduct_comm]
  unfold mnormSq
  rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct, smul_eq_mul,
    dotProduct_comm (M *ᵥ z) u, hs]
  ring

lemma score_oos (M : Matrix (Fin K) (Fin K) ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (k : Fin n)
    (u : Fin K → ℝ) (hM : M.PosDef) :
    f k - mnormSq M (u - Z k) = score (oosA M f Z) (oosB M Z) k u - mnormSq M u := by
  rw [mnormSq_sub hM]; unfold score oosA oosB; ring

lemma softmax_shift (x : Fin n → ℝ) (c : ℝ) (j : Fin n) :
    softmax (fun k => x k - c) j = softmax x j := by
  unfold softmax
  simp only [Real.exp_sub]
  rw [← Finset.sum_div]
  have : 0 < Real.exp c := Real.exp_pos c
  rw [div_div_div_cancel_right₀ this.ne']

theorem oos_ent_affine : Claims.oos_ent_affine := by
  intro n K ε M Z f u hM
  unfold Qent
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (fun k => (f k - mnormSq M (u - Z k)) / ε) =
      fun k => score (oosA M f Z) (oosB M Z) k u / ε - mnormSq M u / ε := by
    funext k; rw [score_oos M f Z k u hM, sub_div]
  rw [e, softmax_shift]

lemma isSimplexProj_shift (x q : Fin n → ℝ) (c : ℝ) :
    IsSimplexProj (fun k => x k - c) q ↔ IsSimplexProj x q := by
  have key : ∀ r ∈ simplex n, ∑ i, (r i - (x i - c)) ^ 2 =
      ∑ i, (r i - x i) ^ 2 + (2 * c * (1 - ∑ i, x i) + n * c ^ 2) := by
    intro r hr
    have e : ∀ i, (r i - (x i - c)) ^ 2 = (r i - x i) ^ 2 + 2 * c * r i - 2 * c * x i + c ^ 2 :=
      fun i => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hr.2,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  unfold IsSimplexProj
  constructor
  · rintro ⟨hq, h⟩
    refine ⟨hq, fun q' hq' => ?_⟩
    have := h q' hq'
    rw [key q hq, key q' hq'] at this
    linarith
  · rintro ⟨hq, h⟩
    refine ⟨hq, fun q' hq' => ?_⟩
    have := h q' hq'
    rw [key q hq, key q' hq']
    linarith

lemma rawScore_eq (lam : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ)
    (u : Fin K → ℝ) (hM : M.PosDef) :
    rawScore lam M f Z u = fun k => score (oosA M f Z) (oosB M Z) k u / lam - mnormSq M u / lam := by
  funext k; unfold rawScore; rw [score_oos M f Z k u hM, sub_div]

theorem oos_quad_affine : Claims.oos_quad_affine := by
  intro n K lam M Z f u q hM
  rw [rawScore_eq lam M f Z u hM]
  exact isSimplexProj_shift _ q _

lemma isCompact_simplex' (n : ℕ) : IsCompact (simplex n) := by
  have hsub : simplex n ⊆ Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1 := by
    intro m hm y _
    refine ⟨hm.1 y, ?_⟩
    rw [← hm.2]
    exact Finset.single_le_sum (f := m) (fun y _ => hm.1 y) (mem_univ y)
  have hclosed : IsClosed (simplex n) := by
    have : simplex n = (⋂ y, {m : Fin n → ℝ | 0 ≤ m y}) ∩ {m | ∑ y, m y = 1} := by
      ext m; simp [simplex]
    rw [this]
    exact (isClosed_iInter fun y => isClosed_le continuous_const (continuous_apply y)).inter
      (isClosed_eq (continuous_finsetSum _ fun y _ => continuous_apply y) continuous_const)
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hclosed hsub

lemma vertex_mem (hn : 0 < n) : (fun y : Fin n => if y = ⟨0, hn⟩ then (1 : ℝ) else 0) ∈ simplex n := by
  refine ⟨fun y => ?_, ?_⟩
  · show (0 : ℝ) ≤ if y = ⟨0, hn⟩ then 1 else 0
    split_ifs <;> norm_num
  · simp

theorem simplex_proj_exists_unique : Claims.simplex_proj_exists_unique := by
  intro n x hn
  have hc : Continuous fun q : Fin n → ℝ => ∑ i, (q i - x i) ^ 2 :=
    continuous_finsetSum _ fun i _ => ((continuous_apply i).sub continuous_const).pow 2
  obtain ⟨q, hq, hmin⟩ := (isCompact_simplex' n).exists_isMinOn ⟨_, vertex_mem hn⟩ hc.continuousOn
  refine ⟨q, ⟨hq, fun q' hq' => hmin hq'⟩, fun q' hq' => ?_⟩
  have h := proj_lip hq' ⟨hq, fun q'' hq'' => hmin hq''⟩
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at h
  have h0 : ∑ i, (q' i - q i) ^ 2 = 0 := le_antisymm h (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _] at h0
  funext i
  have := h0 i (mem_univ i)
  exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)

/-! ### (b) potentials -/

lemma score_sub' (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (i : Fin n) (u y : Fin K → ℝ) :
    score a b i y - score a b i u = b i ⬝ᵥ (y - u) := by
  unfold score; rw [dotProduct_sub]; ring

lemma weighted_dot' (w : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (d : Fin K → ℝ) :
    ∑ i, w i * (b i ⬝ᵥ d) = (∑ i, w i • b i) ⬝ᵥ d := by
  rw [sum_dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_dotProduct, smul_eq_mul]

lemma sum_smul_oosB (w : Fin n → ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) :
    ∑ j, w j • oosB M Z j = (2 : ℝ) • (M *ᵥ ∑ j, w j • Z j) := by
  rw [mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold oosB
  rw [mulVec_smul, smul_comm]

lemma softmax_score_cont (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (ε : ℝ) (hn : 0 < n) (j : Fin n) :
    Continuous fun u => softmax (fun k => score a b k u / ε) j := by
  unfold softmax
  refine Continuous.div ?_ ?_ fun u => ?_
  · exact Real.continuous_exp.comp ((score_cont _ _ j).div_const ε)
  · exact continuous_finsetSum _ fun k _ => Real.continuous_exp.comp ((score_cont _ _ k).div_const ε)
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact (Finset.sum_pos (fun k _ => Real.exp_pos _) univ_nonempty).ne'

theorem oos_ent_potential : Claims.oos_ent_potential := by
  intro n K ε M Z f hn hε hM
  set a := oosA M f Z
  set b := oosB M Z
  set g : (Fin K → ℝ) → Fin K → ℝ := fun u => ∑ j, softmax (fun k => score a b k u / ε) j • b j
  have hsub : ∀ u y, scorePot lse ε a b u + g u ⬝ᵥ (y - u) ≤ scorePot lse ε a b y := by
    intro u y
    have hj := lse_jensen hn (fun k => score a b k u / ε) (fun k => score a b k y / ε)
    have hsum : ∑ i, softmax (fun k => score a b k u / ε) i * (score a b i y / ε - score a b i u / ε) =
        (∑ i, softmax (fun k => score a b k u / ε) i * (b i ⬝ᵥ (y - u))) / ε := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_div, score_sub']; ring
    rw [hsum, weighted_dot'] at hj
    have h2 := (div_le_iff₀' hε).1 hj
    unfold scorePot lse
    rw [mul_sub] at h2
    linarith
  have hg : Continuous g :=
    continuous_finsetSum _ fun j _ => (softmax_score_cont a b ε hn j).smul continuous_const
  refine ⟨convexOn_of_subgrad hsub, fun u => ⟨hasFDerivAt_of_subgrad hsub hg u, ?_⟩⟩
  rw [sum_smul_oosB, oos_ent_affine n K ε M Z f u hM]

lemma proj_cont' {x : (Fin K → ℝ) → Fin n → ℝ} (hx : Continuous x) {q : (Fin K → ℝ) → Fin n → ℝ}
    (hq : ∀ u, IsSimplexProj (x u) (q u)) : Continuous q := by
  have hxc : ∀ k, Continuous fun u => x u k := fun k => (continuous_apply k).comp hx
  refine continuous_pi fun i => continuous_iff_continuousAt.2 fun u => ?_
  have hh : Continuous fun u' => Real.sqrt (∑ k, (x u' k - x u k) ^ 2) :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ fun k _ => ((hxc k).sub continuous_const).pow 2)
  have h0 : Real.sqrt (∑ k, (x u k - x u k) ^ 2) = 0 := by simp
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun u' => ?_) (h0 ▸ hh.tendsto u)
  rw [Real.dist_eq]
  apply Real.abs_le_sqrt
  calc (q u' i - q u i) ^ 2 ≤ ∑ k, (q u' k - q u k) ^ 2 :=
        Finset.single_le_sum (f := fun k => (q u' k - q u k) ^ 2) (fun k _ => sq_nonneg _)
          (Finset.mem_univ i)
    _ ≤ ∑ k, (x u' k - x u k) ^ 2 := proj_lip (hq u') (hq u)

lemma quadPhi_eq {x q : Fin n → ℝ} (hq : IsSimplexProj x q) :
    quadPhi x = ∑ i, q i * x i - (∑ i, q i ^ 2) / 2 := by
  unfold quadPhi
  refine IsGreatest.csSup_eq ⟨⟨q, hq.1, rfl⟩, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact proj_max hq hp

theorem oos_quad_potential : Claims.oos_quad_potential := by
  intro n K lam M Z f q hn hlam hM hq
  set a := oosA M f Z
  set b := oosB M Z
  set x : (Fin K → ℝ) → Fin n → ℝ := fun u k => score a b k u / lam with hx
  have hq' : ∀ u, IsSimplexProj (x u) (q u) := fun u =>
    (oos_quad_affine n K lam M Z f u (q u) hM).1 (hq u)
  set g : (Fin K → ℝ) → Fin K → ℝ := fun u => ∑ j, q u j • b j
  have hsub : ∀ u y, scorePot quadPhi lam a b u + g u ⬝ᵥ (y - u) ≤ scorePot quadPhi lam a b y := by
    intro u y
    have hmax := proj_max (hq' y) (hq' u).1
    unfold scorePot
    change lam * quadPhi (x u) + _ ≤ lam * quadPhi (x y)
    rw [quadPhi_eq (hq' u), quadPhi_eq (hq' y)]
    have hlin : lam * (∑ i, q u i * x y i - ∑ i, q u i * x u i) = g u ⬝ᵥ (y - u) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← weighted_dot']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← score_sub' a b i u y, hx]
      field_simp
    rw [← hlin]
    have := mul_le_mul_of_nonneg_left hmax hlam.le
    nlinarith
  have hxc : Continuous x := continuous_pi fun k => (score_cont a b k).div_const lam
  have hqc := proj_cont' hxc hq'
  have hg : Continuous g :=
    continuous_finsetSum _ fun j _ => ((continuous_apply j).comp hqc).smul continuous_const
  refine ⟨convexOn_of_subgrad hsub, fun u => ⟨hasFDerivAt_of_subgrad hsub hg u, ?_⟩⟩
  rw [sum_smul_oosB]; rfl

/-! ### (c) Moreau envelope of the Laguerre potential -/

lemma dot_self_nonneg (v : Fin K → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

lemma limit_aux {A B : ℝ} (h : ∀ t : ℝ, 0 < t → t < 1 → A ≤ t * B) : A ≤ 0 := by
  by_contra hA
  push_neg at hA
  rcases le_or_gt B 0 with hB | hB
  · have := h (1 / 2) (by norm_num) (by norm_num); nlinarith
  · set t := min (1 / 2 : ℝ) (A / (2 * B))
    have ht0 : 0 < t := lt_min (by norm_num) (div_pos hA (by linarith))
    have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have h1 := h t ht0 ht1
    have h2 : t * B ≤ A / 2 := by
      calc t * B ≤ (A / (2 * B)) * B := mul_le_mul_of_nonneg_right (min_le_right _ _) hB.le
        _ = A / 2 := by field_simp
    linarith

section Moreau
variable {φ : (Fin K → ℝ) → ℝ} {ε : ℝ}

lemma prox_VI (hconv : ConvexOn ℝ Set.univ φ) (hε : 0 < ε) {y p : Fin K → ℝ} (hp : IsProx φ ε y p)
    (z : Fin K → ℝ) : φ p + (y - p) ⬝ᵥ (z - p) / ε ≤ φ z := by
  have key : ∀ t : ℝ, 0 < t → t < 1 →
      φ p - φ z - (p - y) ⬝ᵥ (z - p) / ε ≤ t * ((z - p) ⬝ᵥ (z - p) / (2 * ε)) := by
    intro t ht0 ht1
    have hc := hconv.2 (mem_univ p) (mem_univ z) (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le
      (by ring : 1 - t + t = 1)
    have hpz := hp ((1 - t) • p + t • z)
    unfold proxObj at hpz
    have e : (1 - t) • p + t • z - y = (p - y) + t • (z - p) := by
      ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e] at hpz
    have e2 : ((p - y) + t • (z - p)) ⬝ᵥ ((p - y) + t • (z - p)) = (p - y) ⬝ᵥ (p - y) +
        2 * t * ((p - y) ⬝ᵥ (z - p)) + t ^ 2 * ((z - p) ⬝ᵥ (z - p)) := by
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        dotProduct_comm (z - p) (p - y)]
      ring
    rw [e2] at hpz
    simp only [smul_eq_mul] at hc
    have h1 : t * (φ p - φ z) ≤
        t * ((2 * ((p - y) ⬝ᵥ (z - p)) + t * ((z - p) ⬝ᵥ (z - p))) / (2 * ε)) := by
      have e3 : ((p - y) ⬝ᵥ (p - y) + 2 * t * ((p - y) ⬝ᵥ (z - p)) + t ^ 2 * ((z - p) ⬝ᵥ (z - p))) /
          (2 * ε) = (p - y) ⬝ᵥ (p - y) / (2 * ε) +
          t * ((2 * ((p - y) ⬝ᵥ (z - p)) + t * ((z - p) ⬝ᵥ (z - p))) / (2 * ε)) := by ring
      rw [e3] at hpz
      nlinarith
    have h2 := le_of_mul_le_mul_left h1 ht0
    have e5 : (2 * ((p - y) ⬝ᵥ (z - p)) + t * ((z - p) ⬝ᵥ (z - p))) / (2 * ε) =
        ((p - y) ⬝ᵥ (z - p)) / ε + t * ((z - p) ⬝ᵥ (z - p) / (2 * ε)) := by
      field_simp
    rw [e5] at h2
    linarith
  have := limit_aux key
  have hyp : (y - p) ⬝ᵥ (z - p) = -((p - y) ⬝ᵥ (z - p)) := by rw [← neg_sub, neg_dotProduct]
  rw [hyp, neg_div]
  linarith

lemma prox_strong (hconv : ConvexOn ℝ Set.univ φ) (hε : 0 < ε) {y p : Fin K → ℝ} (hp : IsProx φ ε y p)
    (z : Fin K → ℝ) : proxObj φ ε y p + (z - p) ⬝ᵥ (z - p) / (2 * ε) ≤ proxObj φ ε y z := by
  have h := prox_VI hconv hε hp z
  unfold proxObj
  have e : z - y = (z - p) + (p - y) := by abel
  rw [e]
  have e2 : ((z - p) + (p - y)) ⬝ᵥ ((z - p) + (p - y)) =
      (z - p) ⬝ᵥ (z - p) + 2 * ((p - y) ⬝ᵥ (z - p)) + (p - y) ⬝ᵥ (p - y) := by
    simp only [add_dotProduct, dotProduct_add, dotProduct_comm (z - p) (p - y)]; ring
  have hyp : (y - p) ⬝ᵥ (z - p) = -((p - y) ⬝ᵥ (z - p)) := by rw [← neg_sub, neg_dotProduct]
  rw [e2]
  rw [hyp] at h
  have : (z - p) ⬝ᵥ (z - p) / (2 * ε) + 2 * ((p - y) ⬝ᵥ (z - p)) / (2 * ε) =
      ((z - p) ⬝ᵥ (z - p) + 2 * ((p - y) ⬝ᵥ (z - p))) / (2 * ε) := by ring
  have e3 : 2 * ((p - y) ⬝ᵥ (z - p)) / (2 * ε) = ((p - y) ⬝ᵥ (z - p)) / ε := by field_simp
  have e4 : ((z - p) ⬝ᵥ (z - p) + 2 * ((p - y) ⬝ᵥ (z - p)) + (p - y) ⬝ᵥ (p - y)) / (2 * ε) =
      (z - p) ⬝ᵥ (z - p) / (2 * ε) + 2 * ((p - y) ⬝ᵥ (z - p)) / (2 * ε) +
        (p - y) ⬝ᵥ (p - y) / (2 * ε) := by ring
  rw [e4, e3]
  rw [neg_div] at h
  linarith

lemma prox_firm (hconv : ConvexOn ℝ Set.univ φ) (hε : 0 < ε) {y y' p p' : Fin K → ℝ}
    (hp : IsProx φ ε y p) (hp' : IsProx φ ε y' p') :
    ((y - p) - (y' - p')) ⬝ᵥ ((y - p) - (y' - p')) ≤ (y - y') ⬝ᵥ (y - y') := by
  have v1 := prox_VI hconv hε hp p'
  have v2 := prox_VI hconv hε hp' p
  set a := y - p
  set b := y' - p'
  set w := p - p'
  have hpp : p' - p = -w := by simp [w]
  rw [hpp, dotProduct_neg, neg_div] at v1
  have hsum : (a - b) ⬝ᵥ w ≥ 0 := by
    have h2 : (b ⬝ᵥ w - a ⬝ᵥ w) / ε ≤ 0 := by rw [sub_div]; linarith
    have h3 := (div_le_iff₀ hε).1 h2
    rw [sub_dotProduct]; linarith
  have hyy : y - y' = (a - b) + w := by simp only [a, b, w]; abel
  rw [hyy]
  simp only [add_dotProduct, dotProduct_add, dotProduct_comm w (a - b)]
  nlinarith [dot_self_nonneg w]

lemma env_eq {P : (Fin K → ℝ) → Fin K → ℝ} (hP : ∀ y, IsProx φ ε y (P y)) (y : Fin K → ℝ) :
    moreauEnv φ ε y = proxObj φ ε y (P y) := by
  unfold moreauEnv
  refine le_antisymm (ciInf_le ⟨proxObj φ ε y (P y), ?_⟩ (P y)) (le_ciInf (hP y))
  rintro _ ⟨z, rfl⟩; exact hP y z

lemma env_subgrad (hconv : ConvexOn ℝ Set.univ φ) (hε : 0 < ε) {P : (Fin K → ℝ) → Fin K → ℝ}
    (hP : ∀ y, IsProx φ ε y (P y)) (y y' : Fin K → ℝ) :
    moreauEnv φ ε y + (ε⁻¹ • (y - P y)) ⬝ᵥ (y' - y) ≤ moreauEnv φ ε y' := by
  rw [env_eq hP, env_eq hP]
  have v := prox_VI hconv hε (hP y) (P y')
  unfold proxObj
  set p := P y
  set p' := P y'
  have hid : (y - p) ⬝ᵥ (p' - p) / ε + (p' - y') ⬝ᵥ (p' - y') / (2 * ε) -
      (p - y) ⬝ᵥ (p - y) / (2 * ε) - (ε⁻¹ • (y - p)) ⬝ᵥ (y' - y) =
      ((y - p) - (y' - p')) ⬝ᵥ ((y - p) - (y' - p')) / (2 * ε) := by
    simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_div, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  have hnn : 0 ≤ ((y - p) - (y' - p')) ⬝ᵥ ((y - p) - (y' - p')) / (2 * ε) :=
    div_nonneg (dot_self_nonneg _) (by linarith)
  linarith

end Moreau

lemma lipschitz_of_sq {m : ℕ} {G : (Fin K → ℝ) → Fin m → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y y', (G y - G y') ⬝ᵥ (G y - G y') ≤ c * ((y - y') ⬝ᵥ (y - y'))) :
    LipschitzWith (Real.toNNReal (Real.sqrt (c * K))) G := by
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  set w := y - y'
  have hD : w ⬝ᵥ w ≤ K * ‖w‖ ^ 2 := by
    unfold dotProduct
    calc ∑ i, w i * w i ≤ ∑ _i : Fin K, ‖w‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := norm_le_pi_norm w i
          rw [Real.norm_eq_abs] at this
          nlinarith [abs_nonneg (w i), abs_mul_abs_self (w i)]
      _ = K * ‖w‖ ^ 2 := by simp
  have hb : Real.sqrt ((G y - G y') ⬝ᵥ (G y - G y')) ≤ Real.sqrt (c * K) * ‖w‖ := by
    rw [← Real.sqrt_sq (norm_nonneg w), ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    calc (G y - G y') ⬝ᵥ (G y - G y') ≤ c * (w ⬝ᵥ w) := h y y'
      _ ≤ c * (K * ‖w‖ ^ 2) := mul_le_mul_of_nonneg_left hD hc
      _ = c * K * ‖w‖ ^ 2 := by ring
  refine le_trans ?_ hb
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  unfold dotProduct
  have := Finset.single_le_sum (f := fun j => (G y - G y') j * (G y - G y') j)
    (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
  simpa [sq] using this

section Laguerre
variable {β : Fin n → Fin K → ℝ} {θ : Fin n → ℝ}

lemma laguerre_cont (hn : 0 < n) : Continuous (laguerre β θ) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have e : laguerre β θ = fun y => univ.sup' univ_nonempty (fun j => β j ⬝ᵥ y - θ j) := by
    funext y; unfold laguerre; rw [Finset.sup'_univ_eq_ciSup]
  rw [e]
  exact Continuous.finset_sup'_apply _ fun j _ => (continuous_const.dotProduct continuous_id).sub
    continuous_const

lemma laguerre_convex (hn : 0 < n) : ConvexOn ℝ Set.univ (laguerre β θ) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
  unfold laguerre
  refine ciSup_le fun j => ?_
  have ha := le_ciSup (Finite.bddAbove_range fun j => β j ⬝ᵥ a - θ j) j
  have hb := le_ciSup (Finite.bddAbove_range fun j => β j ⬝ᵥ b - θ j) j
  have e : β j ⬝ᵥ (s • a + t • b) - θ j = s * (β j ⬝ᵥ a - θ j) + t * (β j ⬝ᵥ b - θ j) := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have : θ j = (s + t) * θ j := by rw [hst, one_mul]
    nth_rw 1 [this]; ring
  rw [e, smul_eq_mul, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left ha hs) (mul_le_mul_of_nonneg_left hb ht)

lemma laguerre_lower (hn : 0 < n) (y : Fin K → ℝ) :
    ∃ k, ∀ z, laguerre β θ y + β k ⬝ᵥ (z - y) ≤ laguerre β θ z := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨k, hk⟩ := exists_eq_ciSup_of_finite (f := fun j => β j ⬝ᵥ y - θ j)
  refine ⟨k, fun z => ?_⟩
  unfold laguerre
  rw [← hk, dotProduct_sub]
  have := le_ciSup (Finite.bddAbove_range fun j => β j ⬝ᵥ z - θ j) k
  linarith

lemma prox_exists (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (y : Fin K → ℝ) :
    ∃ p, IsProx (laguerre β θ) ε y p := by
  set F := proxObj (laguerre β θ) ε y
  have hF : Continuous F := by
    unfold F proxObj
    exact (laguerre_cont hn).add (((continuous_id.sub continuous_const).dotProduct
      (continuous_id.sub continuous_const)).div_const _)
  obtain ⟨k, hk⟩ := laguerre_lower (β := β) (θ := θ) hn y
  set S := {z | F z ≤ F y}
  set R := Real.sqrt (4 * ε ^ 2 * (β k ⬝ᵥ β k))
  have hFy : F y = laguerre β θ y := by simp [F, proxObj]
  have hsub : S ⊆ Metric.closedBall y R := by
    intro z hz
    simp only [S, mem_setOf_eq, hFy] at hz
    set h := z - y
    have h1 : β k ⬝ᵥ h + h ⬝ᵥ h / (2 * ε) ≤ 0 := by
      have := hk z
      unfold F proxObj at hz
      linarith
    have h2 : h ⬝ᵥ h ≤ 4 * ε ^ 2 * (β k ⬝ᵥ β k) := by
      have hm : h ⬝ᵥ h ≤ -(2 * ε) * (β k ⬝ᵥ h) := by
        have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * ε)
        rw [mul_add, mul_div_cancel₀ _ (by positivity : (2 * ε) ≠ 0), mul_zero] at this
        linarith
      have amgm : -(2 * ε) * (β k ⬝ᵥ h) ≤ 2 * ε ^ 2 * (β k ⬝ᵥ β k) + h ⬝ᵥ h / 2 := by
        unfold dotProduct
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (h i + 2 * ε * β k i)]
      linarith
    rw [Metric.mem_closedBall, dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    refine le_trans ?_ h2
    have := Finset.single_le_sum (f := fun j => h j * h j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
    rw [sq]; exact this
  have hScl : IsClosed S := isClosed_le hF continuous_const
  have hScpt : IsCompact S := (isCompact_closedBall y R).of_isClosed_subset hScl hsub
  obtain ⟨p, hpS, hmin⟩ := hScpt.exists_isMinOn ⟨y, show F y ≤ F y from le_refl _⟩ hF.continuousOn
  refine ⟨p, fun z => ?_⟩
  by_cases hz : z ∈ S
  · exact hmin hz
  · simp only [S, mem_setOf_eq, not_le] at hz
    exact le_trans hpS hz.le

end Laguerre

theorem karp_prox_unique : Claims.karp_prox_unique := by
  intro n K β θ ε₀ y hn hε
  obtain ⟨p, hp⟩ := prox_exists (β := β) (θ := θ) hn hε y
  refine ⟨p, hp, fun z hz => ?_⟩
  have h1 := prox_strong (laguerre_convex hn) hε hp z
  have h2 := hz p
  have h3 : (z - p) ⬝ᵥ (z - p) / (2 * ε₀) ≤ 0 := by linarith
  have h4 : (z - p) ⬝ᵥ (z - p) = 0 :=
    le_antisymm (by
      have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 2 * ε₀)
      rwa [mul_div_cancel₀ _ (by positivity : (2 * ε₀) ≠ 0), mul_zero] at this) (dot_self_nonneg _)
  exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 h4)

lemma env_grad_lip {n K : ℕ} {β : Fin n → Fin K → ℝ} {θ : Fin n → ℝ} {ε₀ : ℝ}
    {P : (Fin K → ℝ) → Fin K → ℝ} (hn : 0 < n) (hε : 0 < ε₀)
    (hP : ∀ y, IsProx (laguerre β θ) ε₀ y (P y)) :
    ∃ C, LipschitzWith C (fun y => ε₀⁻¹ • (y - P y)) := by
  refine ⟨_, lipschitz_of_sq (c := ε₀⁻¹ ^ 2) (by positivity) fun y y' => ?_⟩
  have h := prox_firm (laguerre_convex hn) hε (hP y) (hP y')
  have e : ε₀⁻¹ • (y - P y) - ε₀⁻¹ • (y' - P y') = ε₀⁻¹ • ((y - P y) - (y' - P y')) := by
    simp only [smul_sub]
  rw [e, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem karp_env_grad : Claims.karp_env_grad := by
  intro n K β θ ε₀ P hn hε hP y
  obtain ⟨C, hC⟩ := env_grad_lip hn hε hP
  exact hasFDerivAt_of_subgrad (env_subgrad (laguerre_convex hn) hε hP) hC.continuous y

lemma lip_mulVec (A : Matrix (Fin K) (Fin K) ℝ) : ∃ C, LipschitzWith C (fun u => A *ᵥ u) := by
  exact ⟨_, (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).lipschitz⟩

theorem karp_potential : Claims.karp_potential := by
  intro n K β θ ε₀ σ M L P hn hε hσ hM hLM hP
  have hdet : IsUnit L.det := by
    have h := hM.det_pos
    rw [← hLM, det_mul, det_transpose] at h
    exact isUnit_iff_ne_zero.2 fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h
  set g : (Fin K → ℝ) → Fin K → ℝ := fun y => ε₀⁻¹ • (y - P y)
  set B : Matrix (Fin K) (Fin K) ℝ := (2 / σ) • L.transpose
  set G : (Fin K → ℝ) → Fin K → ℝ := fun u => B *ᵥ g (L *ᵥ u)
  have hG : ∀ u, (2 : ℝ) • (M *ᵥ karpMap σ ε₀ L P u) = G u := by
    intro u
    unfold karpMap
    rw [mulVec_smul, mulVec_mulVec, ← hLM, Matrix.mul_assoc, mul_nonsing_inv L hdet, Matrix.mul_one,
      smul_smul]
    simp only [G, B, g, smul_mulVec]
    congr 1
  have hGfun : (fun u => (2 : ℝ) • (M *ᵥ karpMap σ ε₀ L P u)) = G := funext hG
  have hsub : ∀ u y, karpPot σ ε₀ L (laguerre β θ) u + G u ⬝ᵥ (y - u) ≤
      karpPot σ ε₀ L (laguerre β θ) y := by
    intro u y
    have h := env_subgrad (laguerre_convex hn) hε hP (L *ᵥ u) (L *ᵥ y)
    unfold karpPot
    have e : G u ⬝ᵥ (y - u) = (2 / σ) * (g (L *ᵥ u) ⬝ᵥ (L *ᵥ y - L *ᵥ u)) := by
      simp only [G, B, smul_mulVec, smul_dotProduct, smul_eq_mul]
      rw [← mulVec_sub, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
    rw [e]
    have h2 : 0 < 2 / σ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h h2.le]
  obtain ⟨C1, h1⟩ := lip_mulVec L
  obtain ⟨C2, h2⟩ := env_grad_lip hn hε hP
  obtain ⟨C3, h3⟩ := lip_mulVec B
  have hGl : LipschitzWith (C3 * (C2 * C1)) G := h3.comp (h2.comp h1)
  refine ⟨convexOn_of_subgrad hsub, fun u => ?_, ⟨_, hGfun ▸ hGl⟩⟩
  rw [hG u]
  exact hasFDerivAt_of_subgrad hsub hGl.continuous u

end StatFormal.OTFD.Wave7a
