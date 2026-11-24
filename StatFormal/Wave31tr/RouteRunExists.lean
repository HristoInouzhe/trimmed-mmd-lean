import StatFormal.Wave31tr.RouteRunPairing
import StatFormal.Wave31tr.RouteRunQP

/-!
# Wave 31tr, chunk A1, T4: the paper's run exists (untrusted route)

Proves `Claims.paperRun_exists`, `Claims.paperRun_exists_printed`, `Claims.paperRun_exists_fractions`. Construction (route of
`NEW_STATEMENTS_31tr.md` T4): the pairing of `exists_printedPairing` (T2 (a)); at every level and batch a measurable exact-QP
selection (`exists_qpSel`, T3) when both fitting sides are nonempty and a constant map otherwise (the B1 guard asks nothing
there); `has`, `g`, `lam` defined by the formulas of `IsPaperRun` (`cHas`, `cRun`). No property of the cut rules is used.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr.RouteRun

open StatFormal.Wave30tq StatFormal.Wave30tz StatFormal.Wave31tl StatFormal.PaperRun

section Construction

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The betting indicator of the construction: both fitting sides nonempty, `D̂ > 0` and `û < t̂`. -/
def cHas (φ : 𝒳 → H) {J n m : ℕ} (α : Fin J → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ) (lx : Fin n → ℕ)
    (ly : Fin m → ℕ)
    (σ : (j : Fin J) → (b : ℕ) → (Fin (fitCard lx b) → 𝒳) × (Fin (fitCard ly b) → 𝒳) →
      (Fin (fitCard lx b) → ℝ) × (Fin (fitCard ly b) → ℝ))
    (j : Fin J) (b : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) : Prop :=
  1 ≤ fitCard lx b ∧ 1 ≤ fitCard ly b ∧
    0 < qpVal φ (fitSample lx b x) (fitSample ly b y) (σ j b (fitSample lx b x, fitSample ly b y)).1
      (σ j b (fitSample lx b x, fitSample ly b y)).2 ∧
    qu (fitCard ly b) (ownY φ (fitSample lx b x) (fitSample ly b y)
        (σ j b (fitSample lx b x, fitSample ly b y)).1 (σ j b (fitSample lx b x, fitSample ly b y)).2) (α j) <
      qt (fitCard lx b) (ownX φ (fitSample lx b x) (fitSample ly b y)
        (σ j b (fitSample lx b x, fitSample ly b y)).1 (σ j b (fitSample lx b x, fitSample ly b y)).2) (1 - α j)

open Classical in
/-- The run of the construction, with the formulas of `IsPaperRun` (3)–(4) for `has`, `g`, `lam`. -/
def cRun (φ : 𝒳 → H) {J n m : ℕ} (α : Fin J → ℝ) (δ lmax s2 w0 : ℝ)
    (v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ) (qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ)
    (lx : Fin n → ℕ) (ly : Fin m → ℕ) (N : ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m))
    (σ : (j : Fin J) → (b : ℕ) → (Fin (fitCard lx b) → 𝒳) × (Fin (fitCard ly b) → 𝒳) →
      (Fin (fitCard lx b) → ℝ) × (Fin (fitCard ly b) → ℝ)) : LoRun 𝒳 J n m where
  lx := lx
  ly := ly
  N := N
  bat := bat
  A := A
  B := B
  has := cHas φ α qt qu lx ly σ
  g := fun j b x y => if cHas φ α qt qu lx ly σ j b x y then
      ramp (fun z => ⟪witness φ (fitSample lx b x) (fitSample ly b y)
          (σ j b (fitSample lx b x, fitSample ly b y)).1 (σ j b (fitSample lx b x, fitSample ly b y)).2, φ z⟫_ℝ)
        (qt (fitCard lx b) (ownX φ (fitSample lx b x) (fitSample ly b y)
          (σ j b (fitSample lx b x, fitSample ly b y)).1 (σ j b (fitSample lx b x, fitSample ly b y)).2) (1 - α j))
        (qu (fitCard ly b) (ownY φ (fitSample lx b x) (fitSample ly b y)
          (σ j b (fitSample lx b x, fitSample ly b y)).1 (σ j b (fitSample lx b x, fitSample ly b y)).2) (α j))
    else fun _ => 0
  lam := fun j k x y z => if hk : k < N then
      (if cHas φ α qt qu lx ly σ j (bat ⟨k, hk⟩) x y then
        fracFormula lmax (α j) (Real.log (1 / δ)) N s2 w0 (v0 j (bat ⟨k, hk⟩) x y)
          (fun l : Fin k => if cHas φ α qt qu lx ly σ j (bat (Fin.castLE hk.le l)) x y then 1 else 0) z
      else 0)
    else 0

/-- A family of measurable exact-QP selections, one per level and batch, required only on nonempty fitting sides. -/
theorem exists_sel_family {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {J n m : ℕ} {α : Fin J → ℝ}
    (hα : ∀ j, 0 ≤ α j ∧ α j < 1) (lx : Fin n → ℕ) (ly : Fin m → ℕ) :
    ∃ σ : (j : Fin J) → (b : ℕ) → (Fin (fitCard lx b) → 𝒳) × (Fin (fitCard ly b) → 𝒳) →
        (Fin (fitCard lx b) → ℝ) × (Fin (fitCard ly b) → ℝ),
      ∀ j b, 1 ≤ fitCard lx b → 1 ≤ fitCard ly b → IsQPSel φ (α j) (σ j b) := by
  classical
  refine ⟨fun j b => if h : 1 ≤ fitCard lx b ∧ 1 ≤ fitCard ly b then
      Classical.choose (exists_qpSel hφ (hα j).1 (hα j).2 h.1 h.2) else fun _ => (0, 0), fun j b h1 h2 => ?_⟩
  dsimp only
  rw [dite_eq_left ⟨h1, h2⟩]
  exact Classical.choose_spec (exists_qpSel hφ (hα j).1 (hα j).2 h1 h2)

end Construction

theorem paperRun_exists_route : Claims.paperRun_exists := by
  intro 𝒳 H _ _ _ _ φ J n m α δ lmax s2 w0 v0 qt qu nb cx cy hφ hα _ _ _ _ _ _ hcx hcy hv0
  obtain ⟨N, bat, A, B, hP, -⟩ := exists_printedPairing nb (fun i : Fin n => cutLabel nb cx i)
    (fun j : Fin m => cutLabel nb cy j) cx cy (fun b hb => cutLabel_batch_interval hcx hb)
    (fun b hb => cutLabel_batch_interval hcy hb)
  obtain ⟨σ, hσ⟩ := exists_sel_family hφ hα (fun i : Fin n => cutLabel nb cx i) (fun j : Fin m => cutLabel nb cy j)
  exact ⟨cRun φ α δ lmax s2 w0 v0 qt qu _ _ N bat A B σ, hcx, hcy, fun i => rfl, fun j => rfl, hP, hv0, σ, hσ,
    fun j b x y => ⟨Iff.rfl, rfl⟩, fun j k x y z => dite_eq_left k.isLt⟩

/-- The constant prior `v₀ ≡ 1` is a prior rule. -/
theorem prior_one {𝒳 : Type*} [MeasurableSpace 𝒳] {J n m : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ) :
    IsPriorRule (J := J) lx ly (fun _ _ (_ : Fin n → 𝒳) (_ : Fin m → 𝒳) => (1 : ℝ)) := fun _ _ =>
  ⟨measurable_const, fun _ _ => ⟨by norm_num, by norm_num⟩, fun _ _ _ _ _ _ => rfl⟩

/-- Explicit nearest-integer boundaries: `⌊(n+2)/4⌋` and `⌊(n+1)/2⌋`. -/
def nearCut (n : ℕ) (b : ℕ) : ℕ := if b = 1 then (n + 2) / 4 else (n + 1) / 2

theorem nearCut_nearest (n : ℕ) : NearestCuts n (nearCut n 1) (nearCut n 2) := by
  unfold NearestCuts nearCut
  simp only [ite_true, show (2 : ℕ) ≠ 1 by decide, ite_false]
  have h1 : 4 * ((n + 2) / 4) ≤ n + 2 := Nat.mul_div_le (n + 2) 4
  have h2 : n + 2 < 4 * ((n + 2) / 4) + 4 := by omega
  have h3 : 2 * ((n + 1) / 2) ≤ n + 1 := Nat.mul_div_le (n + 1) 2
  have h4 : n + 1 < 2 * ((n + 1) / 2) + 2 := by omega
  have r1 : (4 : ℝ) * ((n + 2) / 4 : ℕ) ≤ n + 2 := by exact_mod_cast h1
  have r2 : (n : ℝ) + 2 < 4 * ((n + 2) / 4 : ℕ) + 4 := by exact_mod_cast h2
  have r3 : (2 : ℝ) * ((n + 1) / 2 : ℕ) ≤ n + 1 := by exact_mod_cast h3
  have r4 : (n : ℝ) + 1 < 2 * ((n + 1) / 2 : ℕ) + 2 := by exact_mod_cast h4
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem nearCut_boundaries (n : ℕ) : IsBoundaries 2 n (nearCut n) := by
  refine ⟨fun a ha b hb hab => ?_, fun b hb => ?_⟩
  · obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
    interval_cases a <;> interval_cases b <;> simp [nearCut] <;> omega
  · obtain ⟨hb1, hb2⟩ := hb
    interval_cases b <;> simp [nearCut] <;> omega

theorem paperRun_exists_printed_route : Claims.paperRun_exists_printed := by
  intro 𝒳 H _ _ _ _ φ J n m α δ s2 hφ hα hδ0 hδ1 hs2
  obtain ⟨R, hR⟩ := paperRun_exists_route 𝒳 H φ J n m α δ (1 / 2) s2 20 (fun _ _ _ _ => 1) lowQ highQ 2 (nearCut n)
    (nearCut m) hφ hα hδ0 hδ1 (by norm_num) (by norm_num) hs2 (by norm_num) (nearCut_boundaries n) (nearCut_boundaries m)
    (prior_one _ _)
  exact ⟨R, nearCut n, nearCut m, nearCut_nearest n, nearCut_nearest m, hR⟩

/-- Boundaries `⌊π_b n⌋` at fractions fixed in advance. -/
theorem floor_boundaries {nb : ℕ} {π : ℕ → ℝ} (hπ : IsFractions nb π) (n : ℕ) :
    IsBoundaries nb n (fun b => ⌊π b * n⌋₊) ∧ BoundariesNear nb π n (fun b => ⌊π b * n⌋₊) := by
  obtain ⟨h0, h1, hmono⟩ := hπ
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos : ∀ b ∈ Set.Icc 1 nb, 0 ≤ π b := fun b hb => by
    have := hmono (show 0 ∈ Set.Icc 0 (nb + 1) from ⟨le_rfl, by omega⟩)
      (show b ∈ Set.Icc 0 (nb + 1) from ⟨by omega, by have := hb.2; omega⟩) (by have := hb.1; omega)
    rw [h0] at this; exact this.le
  have hle1 : ∀ b ∈ Set.Icc 1 nb, π b ≤ 1 := fun b hb => by
    have := hmono (show b ∈ Set.Icc 0 (nb + 1) from ⟨by omega, by have := hb.2; omega⟩)
      (show nb + 1 ∈ Set.Icc 0 (nb + 1) from ⟨by omega, le_rfl⟩) (by have := hb.2; omega)
    rw [h1] at this; exact this.le
  refine ⟨⟨fun a ha b hb hab => ?_, fun b hb => ?_⟩, fun b hb => ?_⟩
  · exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right
      (hmono.monotoneOn ⟨by omega, by have := ha.2; omega⟩ ⟨by omega, by have := hb.2; omega⟩ hab) hn)
  · exact Nat.floor_le_of_le (by nlinarith [hle1 b hb])
  · have hx : 0 ≤ π b * n := mul_nonneg (hpos b hb) hn
    have e1 := Nat.floor_le hx
    have e2 := Nat.lt_floor_add_one (π b * n)
    rw [abs_le]; constructor <;> linarith

theorem paperRun_exists_fractions_route : Claims.paperRun_exists_fractions := by
  intro 𝒳 H _ _ _ _ φ J α δ lmax s2 w0 nb π hφ hα hδ hl0 hl1 hs2 hw0 _ hπ
  have h : ∀ n m : ℕ, ∃ R : LoRun 𝒳 (J n m) n m, IsPaperRun R φ (α n m) (δ n m) lmax s2 w0 (fun _ _ _ _ => 1) lowQ highQ nb
      (fun b => ⌊π b * n⌋₊) (fun b => ⌊π b * m⌋₊) := fun n m =>
    paperRun_exists_route 𝒳 H φ (J n m) n m (α n m) (δ n m) lmax s2 w0 (fun _ _ _ _ => 1) lowQ highQ nb _ _ hφ (hα n m)
      (hδ n m).1 (hδ n m).2 hl0 hl1 hs2 hw0 (floor_boundaries hπ n).1 (floor_boundaries hπ m).1 (prior_one _ _)
  choose R hR using h
  exact ⟨R, fun n _ b => ⌊π b * n⌋₊, fun _ m b => ⌊π b * m⌋₊, fun n m =>
    ⟨(floor_boundaries hπ n).2, (floor_boundaries hπ m).2, hR n m⟩⟩

end StatFormal.Wave31tr.RouteRun
