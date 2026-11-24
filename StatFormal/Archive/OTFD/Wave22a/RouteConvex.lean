import StatFormal.Archive.OTFD.Wave22a.Statements
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Route — otfd A `cor:app-ghs-lipschitz`, `thm:sieve-convergence` (convex-analysis cores; untrusted)

* `ψ̃ = sup_{y∈S}(⟨·,y⟩ − b y)`: each affine piece is `≤ ψ̃(x') + L‖x − x'‖`, whence finiteness, convexity and the
  Lipschitz bound;
* subgradients: Hahn–Banach separation of `y₀ ∉ closure (conv S)` by `⟨h,·⟩` (Riesz), tested at `x − h`;
* `ℝ^K`: a maximising sequence of slopes has a convergent subsequence; its limit is a subgradient;
* cube: test the subgradient inequality at `x ± e_k`; `int C_λ = ∅` since `x ± (r/2)e_k ∈ C_λ` forces `λ_k ≥ r/2`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.Wave22a

open StatFormal.OTFD.Wave1 (truncK)

section Sup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma bdd_supAff {S : Set H} {b : H → ℝ} {L : ℝ} {x₀ : H} (hL : ∀ y ∈ S, ‖y‖ ≤ L)
    (h0 : BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y)) (x : H) :
    BddAbove (range fun y : S => ⟪x, (y : H)⟫ - b y) := by
  obtain ⟨C, hC⟩ := h0
  refine ⟨C + ‖x - x₀‖ * L, ?_⟩
  rintro _ ⟨y, rfl⟩
  have h1 : ⟪x₀, (y : H)⟫ - b y ≤ C := hC ⟨y, rfl⟩
  have h2 : ⟪x - x₀, (y : H)⟫ ≤ ‖x - x₀‖ * L :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hL y y.2) (norm_nonneg _))
  have : ⟪x, (y : H)⟫ = ⟪x₀, (y : H)⟫ + ⟪x - x₀, (y : H)⟫ := by
    rw [inner_sub_left]; ring
  simp only
  linarith

lemma le_supAff {S : Set H} {b : H → ℝ} {L : ℝ} {x₀ : H} (hL : ∀ y ∈ S, ‖y‖ ≤ L)
    (h0 : BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y)) (x : H) (y : S) :
    ⟪x, (y : H)⟫ - b y ≤ supAff S b x :=
  le_ciSup (bdd_supAff hL h0 x) y

lemma supAff_le_add {S : Set H} {b : H → ℝ} {L : ℝ} {x₀ : H} (hS : S.Nonempty)
    (hL : ∀ y ∈ S, ‖y‖ ≤ L) (h0 : BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y)) (x x' : H) :
    supAff S b x ≤ supAff S b x' + L * ‖x - x'‖ := by
  have : Nonempty S := hS.to_subtype
  refine ciSup_le fun y => ?_
  have h1 := le_supAff hL h0 x' y
  have h2 : ⟪x - x', (y : H)⟫ ≤ L * ‖x - x'‖ := by
    have := (real_inner_le_norm (x - x') (y : H)).trans
      (mul_le_mul_of_nonneg_left (hL y y.2) (norm_nonneg _))
    linarith
  have : ⟪x, (y : H)⟫ = ⟪x', (y : H)⟫ + ⟪x - x', (y : H)⟫ := by rw [inner_sub_left]; ring
  linarith

lemma supAff_lip {S : Set H} {b : H → ℝ} {L : ℝ} {x₀ : H} (hS : S.Nonempty)
    (hL : ∀ y ∈ S, ‖y‖ ≤ L) (h0 : BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y)) (x x' : H) :
    |supAff S b x - supAff S b x'| ≤ L * ‖x - x'‖ := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [supAff_le_add hS hL h0 x x']
  · have := supAff_le_add hS hL h0 x' x
    rw [norm_sub_rev] at this
    linarith

lemma supAff_convex {S : Set H} {b : H → ℝ} {L : ℝ} {x₀ : H} (hS : S.Nonempty)
    (hL : ∀ y ∈ S, ‖y‖ ≤ L) (h0 : BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y)) :
    ConvexOn ℝ univ (supAff S b) := by
  have : Nonempty S := hS.to_subtype
  refine ⟨convex_univ, fun x _ x' _ a c ha hc hac => ?_⟩
  refine ciSup_le fun y => ?_
  have h1 := le_supAff hL h0 x y
  have h2 := le_supAff hL h0 x' y
  have : ⟪a • x + c • x', (y : H)⟫ - b y =
      a * (⟪x, (y : H)⟫ - b y) + c * (⟪x', (y : H)⟫ - b y) := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have : b y = (a + c) * b y := by rw [hac, one_mul]
    linarith
  rw [this, smul_eq_mul, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hc)

lemma supAff_sub_le {S : Set H} {b : H → ℝ} {L : ℝ} {x₀ : H} (hS : S.Nonempty)
    (hL : ∀ y ∈ S, ‖y‖ ≤ L) (h0 : BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y))
    (x h : H) (u : ℝ) (hu : ∀ y ∈ S, u < ⟪h, y⟫) :
    supAff S b (x - h) ≤ supAff S b x - u := by
  have : Nonempty S := hS.to_subtype
  refine ciSup_le fun y => ?_
  have h1 := le_supAff hL h0 x y
  have h2 := hu y y.2
  have : ⟪x - h, (y : H)⟫ = ⟪x, (y : H)⟫ - ⟪h, (y : H)⟫ := inner_sub_left _ _ _
  linarith

lemma subgrad_mem_closure [CompleteSpace H] {S : Set H} {b : H → ℝ} {L : ℝ} {x₀ : H}
    (hS : S.Nonempty) (hL : ∀ y ∈ S, ‖y‖ ≤ L)
    (h0 : BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y)) (x y₀ : H)
    (hy : IsSubgrad (supAff S b) x y₀) : y₀ ∈ closure (convexHull ℝ S) := by
  by_contra hny
  obtain ⟨f, u, hfu, hf⟩ := geometric_hahn_banach_point_closed
    ((convex_convexHull ℝ S).closure) isClosed_closure hny
  set h : H := (InnerProductSpace.toDual ℝ H).symm f
  have hh : ∀ v, ⟪h, v⟫ = f v := fun v => InnerProductSpace.toDual_symm_apply
  have hS' : ∀ y ∈ S, u < ⟪h, y⟫ := fun y hyS => by
    rw [hh]; exact hf y (subset_closure (subset_convexHull ℝ S hyS))
  have h1 := supAff_sub_le hS hL h0 x h u hS'
  have h2 := hy (x - h)
  have : ⟪y₀, x - h - x⟫ = -⟪h, y₀⟫ := by
    rw [sub_sub_cancel_left, inner_neg_right, real_inner_comm]
  rw [this, hh] at h2
  linarith

end Sup

theorem ghs_lip_finite : Claims.ghs_lip_finite := by
  intro H _ _ S b L x₀ _ hL h0 x
  exact bdd_supAff hL h0 x

theorem ghs_lip : Claims.ghs_lip := by
  intro H _ _ S b L x₀ hS hL h0
  exact ⟨supAff_convex hS hL h0, supAff_lip hS hL h0⟩

theorem ghs_lip_subgrad : Claims.ghs_lip_subgrad := by
  intro H _ _ _ S b L x₀ hS hL h0 x y hy
  exact subgrad_mem_closure hS hL h0 x y hy

theorem ghs_lip_grad : Claims.ghs_lip_grad := by
  intro H _ _ _ S b L x₀ hS hL h0 x g hg
  obtain ⟨y, hyS⟩ := hS
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL y hyS)
  have hlip : LipschitzWith (Real.toNNReal L) (supAff S b) := by
    refine LipschitzWith.of_dist_le_mul fun a a' => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL0]
    exact supAff_lip ⟨y, hyS⟩ hL h0 a a'
  have hfd := hasGradientAt_iff_hasFDerivAt.mp hg
  have := hfd.le_of_lipschitz hlip
  rw [LinearIsometryEquiv.norm_map, Real.coe_toNNReal _ hL0] at this
  exact this

theorem sieve_subdiff_nonempty : Claims.sieve_subdiff_nonempty := by
  intro K S b L x₀ hS hL h0 z
  have : Nonempty S := hS.to_subtype
  have hlt : ∀ n : ℕ, ∃ y : S, supAff S b z - 1 / ((n : ℝ) + 1) < ⟪z, (y : EuclideanSpace ℝ (Fin K))⟫ - b y :=
    fun n => exists_lt_of_lt_ciSup (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      unfold supAff; linarith)
  choose y hy using hlt
  have hmem : ∀ n, (y n : EuclideanSpace ℝ (Fin K)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin K)) L :=
    fun n => by rw [mem_closedBall_zero_iff]; exact hL _ (y n).2
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  refine ⟨a, fun w => ?_⟩
  have hw : ∀ n, supAff S b z + ⟪(y (φ n) : EuclideanSpace ℝ (Fin K)), w - z⟫ - 1 / ((φ n : ℝ) + 1) ≤
      supAff S b w := by
    intro n
    have h1 := le_supAff hL h0 w (y (φ n))
    have h2 := hy (φ n)
    have : ⟪w, (y (φ n) : EuclideanSpace ℝ (Fin K))⟫ =
        ⟪z, (y (φ n) : EuclideanSpace ℝ (Fin K))⟫ + ⟪(y (φ n) : EuclideanSpace ℝ (Fin K)), w - z⟫ := by
      have e1 := real_inner_comm w (y (φ n) : EuclideanSpace ℝ (Fin K))
      have e2 := real_inner_comm z (y (φ n) : EuclideanSpace ℝ (Fin K))
      rw [inner_sub_right]; linarith
    linarith
  have hT : Tendsto (fun n => supAff S b z + ⟪(y (φ n) : EuclideanSpace ℝ (Fin K)), w - z⟫ -
      1 / ((φ n : ℝ) + 1)) atTop (𝓝 (supAff S b z + ⟪a, w - z⟫ - 0)) := by
    have hA : Tendsto (fun n => ⟪(y (φ n) : EuclideanSpace ℝ (Fin K)), w - z⟫) atTop (𝓝 ⟪a, w - z⟫) :=
      Filter.Tendsto.inner (𝕜 := ℝ) hlim tendsto_const_nhds
    have hB : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
    exact (tendsto_const_nhds.add hA).sub hB
  rw [sub_zero] at hT
  exact le_of_tendsto' hT hw

section Cube
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma truncK_add_smul (e : ℕ → H) (K : ℕ) (x v : H) (t : ℝ) :
    truncK e K (x + t • v) = truncK e K x + t • truncK e K v := by
  ext j
  simp [truncK, inner_add_right, inner_smul_right]

lemma inner_truncK_basis {e : ℕ → H} (he : Orthonormal ℝ e) (K k : ℕ) (z : EuclideanSpace ℝ (Fin K)) :
    ⟪truncK e K (e k), z⟫ = if h : k < K then z ⟨k, h⟩ else 0 := by
  rw [PiLp.inner_apply]
  simp only [truncK, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial]
  have hor := orthonormal_iff_ite.mp he
  split_ifs with hk
  · rw [Finset.sum_eq_single ⟨k, hk⟩]
    · rw [hor]; simp
    · intro j _ hj
      have hjk : (j : ℕ) ≠ k := fun hjk => hj (Fin.ext hjk)
      rw [hor]; simp [hjk]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    have hjk : (j : ℕ) ≠ k := fun hjk => hk (hjk ▸ j.2)
    rw [hor]; simp [hjk]

end Cube

theorem sieve_subgrad_cube : Claims.sieve_subgrad_cube := by
  intro H _ _ e lam K S b x₀ he hlam hS hbox h0 x y hy k
  have : Nonempty S := hS.to_subtype
  set Lb : ℝ := √(∑ k : Fin K, lam k ^ 2)
  have hL : ∀ z ∈ S, ‖z‖ ≤ Lb := by
    intro z hz
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
    have := pow_le_pow_left₀ (abs_nonneg _) (hbox z hz j) 2
    rwa [sq_abs] at this
  set B : ℝ := if k < K then lam k else 0
  have hB : B ≤ lam k := by
    simp only [B]; split_ifs
    · exact le_rfl
    · exact hlam k
  have hz : ∀ z ∈ S, |⟪truncK e K (e k), z⟫| ≤ B := by
    intro z hzS
    rw [inner_truncK_basis he]
    simp only [B]
    split_ifs with hk
    · exact hbox z hzS ⟨k, hk⟩
    · simp
  have hstep : ∀ t : ℝ, t * ⟪y, e k⟫ ≤ |t| * B := by
    intro t
    have h1 := hy (x + t • e k)
    simp only [add_sub_cancel_left, inner_smul_right] at h1
    have h2 : supAff S b (truncK e K (x + t • e k)) ≤ supAff S b (truncK e K x) + |t| * B := by
      refine ciSup_le fun z => ?_
      have := le_supAff hL h0 (truncK e K x) z
      rw [truncK_add_smul, inner_add_left, real_inner_smul_left]
      have h3 : t * ⟪truncK e K (e k), (z : EuclideanSpace ℝ (Fin K))⟫ ≤ |t| * B := by
        calc t * ⟪truncK e K (e k), (z : EuclideanSpace ℝ (Fin K))⟫
            ≤ |t * ⟪truncK e K (e k), (z : EuclideanSpace ℝ (Fin K))⟫| := le_abs_self _
          _ = |t| * |⟪truncK e K (e k), (z : EuclideanSpace ℝ (Fin K))⟫| := abs_mul _ _
          _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hz z z.2) (abs_nonneg t)
      linarith
    linarith
  have hp := hstep 1
  have hm := hstep (-1)
  simp only [one_mul, abs_one, neg_mul, abs_neg] at hp hm
  exact (abs_le.mpr ⟨by linarith, hp⟩).trans hB

theorem cube_interior_empty : Claims.cube_interior_empty := by
  intro H _ _ e lam he hlam
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hk : ∀ k, r / 2 ≤ lam k := by
    intro k
    have hn : ‖e k‖ = 1 := he.1 k
    have hmem : ∀ s : ℝ, |s| < r → x + s • e k ∈ cubeH e lam := fun s hs =>
      hball (by rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hn, mul_one,
        Real.norm_eq_abs]; exact hs)
    have h1 := hmem (r / 2) (by rw [abs_of_pos (by linarith)]; linarith) k
    have h2 := hmem (-(r / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith) k
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hn] at h1 h2
    rw [abs_le] at h1 h2
    linarith [h1.2, h2.1]
  have := (hlam.eventually (gt_mem_nhds (half_pos hr))).exists
  obtain ⟨k, hk'⟩ := this
  linarith [hk k]

end StatFormal.OTFD.Wave22a
