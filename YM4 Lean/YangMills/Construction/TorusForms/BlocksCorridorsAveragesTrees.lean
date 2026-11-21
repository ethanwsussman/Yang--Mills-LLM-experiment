import YangMills.Construction.Lattice.PeriodicLatticeForms
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace BlockSpin
open Lattice
def blockOffset (S : LatticeParameters) (n : ℕ) : ℕ := S.offset * (S.L ^ n - 1) / (S.L - 1)
theorem blockOffset_mul (S : LatticeParameters) (n : ℕ) :
    blockOffset S n * (S.L - 1) = S.offset * (S.L ^ n - 1) := by
  have hdiv : S.L - 1 ∣ S.L ^ n - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow S.L 1 n
  exact Nat.div_mul_cancel (Dvd.dvd.mul_left hdiv _)
structure IsBlockSpacing (S : LatticeParameters) (n : ℕ) (ℓ : Fin S.d → ℝ) (ε ε' : ℝ) : Prop where
  spacing_eq : ε' = (S.L : ℝ) ^ n * ε
  ratio_mem : ∀ μ, ∃ N : ℕ, 2 ≤ N ∧ ℓ μ / ε' = N
section Blocks
variable (S : LatticeParameters) {ℓ : Fin S.d → ℝ} {ε ε' : ℝ}
variable {S} in
theorem IsBlockSpacing.isCommensurateSpacing {n : ℕ} [hε : IsCommensurateSpacing ℓ ε]
    (h : IsBlockSpacing S n ℓ ε ε') : IsCommensurateSpacing ℓ ε' where
  periods_pos := hε.periods_pos
  spacing_pos := by
    have hL : (0 : ℝ) < S.L := by exact_mod_cast lt_of_lt_of_le two_pos S.two_le_L
    rw [h.spacing_eq]
    exact mul_pos (pow_pos hL n) hε.spacing_pos
  ratio_mem μ := by
    obtain ⟨N, hN, hr⟩ := h.ratio_mem μ
    exact ⟨N, by omega, hr⟩
variable {S} in
theorem IsBlockSpacing.latticeSubgroup_le {n : ℕ} (h : IsBlockSpacing S n ℓ ε ε') :
    latticeSubgroup ℓ ε' ≤ latticeSubgroup ℓ ε := by
  refine AddSubgroup.map_mono ?_
  intro v hv
  refine (AddSubgroup.mem_pi _).mpr fun μ _ => ?_
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp ((AddSubgroup.mem_pi _).mp hv μ (Set.mem_univ μ))
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨k * (S.L : ℤ) ^ n, ?_⟩
  rw [← hk, h.spacing_eq, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  ring
variable {S} in
def IsBlockSpacing.toFineSite {n : ℕ} (h : IsBlockSpacing S n ℓ ε ε') (y : LatticeSite ℓ ε') :
    LatticeSite ℓ ε :=
  ⟨y, h.latticeSubgroup_le y.2⟩
def gridPoint {d : ℕ} (ℓ : Fin d → ℝ) (ε : ℝ) (σ : Fin d → ℤ) : LatticeSite ℓ ε :=
  ⟨torusMk ℓ fun μ => (σ μ : ℝ) * ε, AddSubgroup.mem_map_of_mem _ <|
    (AddSubgroup.mem_pi _).mpr fun μ _ =>
      AddSubgroup.mem_zmultiples_iff.mpr ⟨σ μ, by simp [zsmul_eq_mul]⟩⟩
def InBlockIndexRange (n : ℕ) (σ : Fin S.d → ℤ) : Prop :=
  ∀ μ, -(blockOffset S n : ℤ) ≤ σ μ ∧ σ μ ≤ (S.L : ℤ) ^ n - 1 - blockOffset S n
def blockOf (n : ℕ) (ε : ℝ) (y : LatticeSite ℓ ε') : Set (LatticeSite ℓ ε) :=
  {x | ∃ σ, InBlockIndexRange S n σ ∧
    (x : PeriodicTorus ℓ) = (y : PeriodicTorus ℓ) + (gridPoint ℓ ε σ : PeriodicTorus ℓ)}
def blockUnion (n : ℕ) (ε : ℝ) (Y : Set (LatticeSite ℓ ε')) : Set (LatticeSite ℓ ε) :=
  ⋃ y ∈ Y, blockOf S n ε y
def LinkInside (b : Link ℓ ε) (X : Set (LatticeSite ℓ ε)) : Prop := b.ends ⊆ X
def PlaquetteWithin (p : LatticePlaquette ℓ ε) (X : Set (LatticeSite ℓ ε)) : Prop :=
  p.vertices ⊆ X
def linkCorridor (n : ℕ) (ε : ℝ) (c : Link ℓ ε') : Set (Link ℓ ε) :=
  {b | b.2 = c.2 ∧ b.1 ∈ blockOf S n ε c.1 ∧ b.head ∈ blockOf S n ε c.head}
def PlaquetteInLinkCorridor (n : ℕ) (p : LatticePlaquette ℓ ε) (c : Link ℓ ε') : Prop :=
  ∃ b ∈ p.boundaryLinks, ∃ b' ∈ p.boundaryLinks, b ≠ b' ∧
    b ∈ linkCorridor S n ε c ∧ b' ∈ linkCorridor S n ε c
open Classical in
def blockAverage0 (n : ℕ) (ε ε' : ℝ) [IsCommensurateSpacing ℓ ε] :
    Cochain0 ℓ ε →ₗ[ℝ] Cochain0 ℓ ε' where
  toFun φ y := ((S.L : ℝ) ^ (n * S.d))⁻¹ * ∑ x ∈ Finset.univ.filter (· ∈ blockOf S n ε y), φ x
  map_add' f g := by
    funext y
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
open Classical in
def blockAverage1 (n : ℕ) (ε ε' : ℝ) [IsCommensurateSpacing ℓ ε] :
    Cochain1 ℓ ε →ₗ[ℝ] Cochain1 ℓ ε' where
  toFun A b := ((S.L : ℝ) ^ (n * (S.d + 1)))⁻¹ *
    ∑ x ∈ Finset.univ.filter (· ∈ blockOf S n ε b.1),
      ∑ k ∈ Finset.range (S.L ^ n), A (x + k • latticeStep ℓ ε b.2, b.2)
  map_add' f g := by
    funext b
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
def rescaledAdjoint (d : ℕ) (ε ε' : ℝ) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  ((ε' / ε) ^ d) • latticeAdjoint T
def blockAverage0Adjoint (n : ℕ) (ε ε' : ℝ) [IsCommensurateSpacing ℓ ε]
    [IsCommensurateSpacing ℓ ε'] : Cochain0 ℓ ε' →ₗ[ℝ] Cochain0 ℓ ε :=
  rescaledAdjoint S.d ε ε' (blockAverage0 S n ε ε')
def linkDomain (n : ℕ) (ε : ℝ) (b : Link ℓ ε') : Set (Link ℓ ε) :=
  {a | ∃ x ∈ blockOf S n ε b.1, ∃ k : ℕ, k < S.L ^ n ∧ a = (x + k • latticeStep ℓ ε b.2, b.2)}
end Blocks
section Contours
variable {d : ℕ} {ℓ : Fin d → ℝ} {ε : ℝ}
def unitStep (x : LatticeSite ℓ ε) (μ : Fin d) (forward : Bool) : LinkStep ℓ ε :=
  ⟨if forward then (x, μ) else (x - latticeStep ℓ ε μ, μ), forward⟩
theorem unitStep_source (x : LatticeSite ℓ ε) (μ : Fin d) (forward : Bool) :
    (unitStep x μ forward).source = x := by
  cases forward <;> simp [unitStep, LinkStep.source, Link.head]
def stepsOfMoves : LatticeSite ℓ ε → List (Fin d × Bool) → List (LinkStep ℓ ε)
  | _, [] => []
  | x, m :: ms => unitStep x m.1 m.2 :: stepsOfMoves (unitStep x m.1 m.2).target ms
theorem isWalkFrom_stepsOfMoves (x : LatticeSite ℓ ε) (ms : List (Fin d × Bool)) :
    IsWalkFrom x (stepsOfMoves x ms) := by
  induction ms generalizing x with
  | nil => trivial
  | cons m ms ih => exact ⟨unitStep_source x m.1 m.2, ih _⟩
def axisMoves (σ : Fin d → ℤ) : List (Fin d × Bool) :=
  (List.finRange d).reverse.flatMap fun μ => List.replicate (σ μ).natAbs (μ, decide (0 ≤ σ μ))
def axisPath (x : LatticeSite ℓ ε) (σ : Fin d → ℤ) : LatticePath ℓ ε :=
  ⟨x, stepsOfMoves x (axisMoves σ), isWalkFrom_stepsOfMoves x _⟩
def CoordinateAgrees (x y : PeriodicTorus ℓ) (m : Fin d) : Prop :=
  ∃ u : Fin d → ℝ, torusMk ℓ u = x - y ∧ u m = 0
end Contours
section Trees
variable (S : LatticeParameters) {ℓ : Fin S.d → ℝ} {ε ε' : ℝ}
def blockContour (h : IsBlockSpacing S 1 ℓ ε ε') (y : LatticeSite ℓ ε') {x : LatticeSite ℓ ε}
    (hx : x ∈ blockOf S 1 ε y) : LatticePath ℓ ε :=
  axisPath (h.toFineSite y) (Classical.choose hx)
def blockTree (h : IsBlockSpacing S 1 ℓ ε ε') (y : LatticeSite ℓ ε') : Set (Link ℓ ε) :=
  {b | ∃ (x : LatticeSite ℓ ε) (hx : x ∈ blockOf S 1 ε y),
    ∃ t ∈ (blockContour S h y hx).2, t.1 = b}
def blockTreeByCoordinates (ε : ℝ) (y : LatticeSite ℓ ε') : Set (Link ℓ ε) :=
  {b | LinkInside S b (blockOf S 1 ε y) ∧
    ∀ m, m < b.2 → CoordinateAgrees (b.1 : PeriodicTorus ℓ) (y : PeriodicTorus ℓ) m}
end Trees
end BlockSpin
end YangMills.Construction
