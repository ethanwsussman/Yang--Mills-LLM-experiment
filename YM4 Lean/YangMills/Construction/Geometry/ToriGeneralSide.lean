import YangMills.Construction.Blocking.DimFourOddBlockingFactorGeThirteen
import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace GeneralTorus
open YangMills.Construction.TorusMetric YangMills.Construction.Blocking
def IsEvenMultipleOf (S s : ℝ) : Prop := ∃ k : ℕ, 0 < k ∧ S = 2 * k * s
def spacingLattice (S s : ℝ) : AddSubgroup (Torus4 S) where
  carrier := {x | ∃ k : Fin 4 → ℤ, x = torusProj S fun μ => s * (k μ : ℝ)}
  add_mem' := by
    rintro _ _ ⟨k, rfl⟩ ⟨k', rfl⟩
    refine ⟨k + k', funext fun μ => ?_⟩
    simp only [torusProj, Pi.add_apply, Int.cast_add, mul_add, AddCircle.coe_add]
  zero_mem' := ⟨0, funext fun μ => by simp [torusProj]⟩
  neg_mem' := by
    rintro _ ⟨k, rfl⟩
    refine ⟨-k, funext fun μ => ?_⟩
    simp [torusProj]
abbrev LatticeSite (S σ : ℝ) : Type := ↥(spacingLattice S σ)
def supCube {S : ℝ} (s : ℝ) (y : Torus4 S) : Set (Torus4 S) :=
  {x | torusSupNorm (x - y) ≤ s / 2}
def coordPoint (S : ℝ) (μ : Fin 4) (t : ℝ) : Torus4 S := torusProj S (Pi.single μ t)
def unitStep (S σ : ℝ) (μ : Fin 4) : LatticeSite S σ :=
  ⟨coordPoint S μ σ, ⟨Pi.single μ 1, funext fun ν => by
    by_cases h : ν = μ
    · subst h; simp [coordPoint, torusProj]
    · simp [coordPoint, torusProj, Pi.single_eq_of_ne h]⟩⟩
@[ext]
structure LatticeBond (S σ : ℝ) where
  src : LatticeSite S σ
  tgt : LatticeSite S σ
  isAdjacent : ∃ μ : Fin 4, tgt - src = unitStep S σ μ ∨ tgt - src = -unitStep S σ μ
variable {S σ σ' : ℝ}
namespace LatticeBond
def IsPositivelyOriented (b : LatticeBond S σ) : Prop := ∃ μ : Fin 4, b.tgt - b.src = unitStep S σ μ
def flip (b : LatticeBond S σ) : LatticeBond S σ where
  src := b.tgt
  tgt := b.src
  isAdjacent := by
    obtain ⟨μ, h | h⟩ := b.isAdjacent
    · exact ⟨μ, Or.inr (by rw [← h]; abel)⟩
    · exact ⟨μ, Or.inl (by rw [← neg_eq_iff_eq_neg.mpr h]; abel)⟩
def plus (x : LatticeSite S σ) (μ : Fin 4) : LatticeBond S σ :=
  ⟨x, x + unitStep S σ μ, μ, Or.inl (by abel)⟩
end LatticeBond
@[ext]
structure LatticePlaquette (S σ : ℝ) where
  basePoint : LatticeSite S σ
  dir₁ : Fin 4
  dir₂ : Fin 4
  dir₁_lt_dir₂ : dir₁ < dir₂
namespace LatticePlaquette
def cornerSet (p : LatticePlaquette S σ) : Set (LatticeSite S σ) :=
  {p.basePoint, p.basePoint + unitStep S σ p.dir₁,
    p.basePoint + unitStep S σ p.dir₁ + unitStep S σ p.dir₂,
    p.basePoint + unitStep S σ p.dir₂}
def boundaryBonds (p : LatticePlaquette S σ) : List (LatticeBond S σ) :=
  [LatticeBond.plus p.basePoint p.dir₁,
    LatticeBond.plus (p.basePoint + unitStep S σ p.dir₁) p.dir₂,
    (LatticeBond.plus (p.basePoint + unitStep S σ p.dir₂) p.dir₁).flip,
    (LatticeBond.plus p.basePoint p.dir₂).flip]
end LatticePlaquette
def latticeBlock (σ σ' : ℝ) (y : Torus4 S) : Set (Torus4 S) :=
  supCube σ y ∩ (spacingLattice S σ' : Set (Torus4 S))
def sitesIn (σ : ℝ) (X : Set (Torus4 S)) : Set (LatticeSite S σ) :=
  {x | (x : Torus4 S) ∈ X}
def IsUnionOfCubes (π : Set (Set (Torus4 S))) (X : Set (Torus4 S)) : Prop :=
  ∃ C ⊆ π, X = ⋃₀ C
def closedComplement (X : Set (Torus4 S)) : Set (Torus4 S) := closure Xᶜ
structure ScaleData where
  L : ℕ
  blocking : DimFourOddBlockingFactorGeThirteen 4 L
  baseSpacing : ℝ
  baseSpacing_pos : 0 < baseSpacing
  lastLevel : ℕ
  blockCount : ℕ
  blockCount_pow : ∃ k : ℕ, blockCount = L ^ k
  gapCount : ℕ
  gapCount_pow : ∃ k : ℕ, gapCount = L ^ k
  torusSide : ℝ
  torusSide_evenMultiple : IsEvenMultipleOf torusSide ((L : ℝ) ^ lastLevel * baseSpacing)
namespace ScaleData
variable (D : ScaleData)
def levelSpacing (n : ℕ) : ℝ := (D.L : ℝ) ^ n * D.baseSpacing
abbrev Space : Type := Torus4 D.torusSide
def AdmitsPartition (s : ℝ) : Prop := 0 < s ∧ IsEvenMultipleOf D.torusSide s
def cubePartition (s : ℝ) : Set (Set D.Space) :=
  {Q | D.AdmitsPartition s ∧ ∃ y ∈ spacingLattice D.torusSide s, Q = supCube s y}
def levelSublattice (n : ℕ) : AddSubgroup D.Space := spacingLattice D.torusSide (D.levelSpacing n)
abbrev SiteAt (n : ℕ) : Type := LatticeSite D.torusSide (D.levelSpacing n)
abbrev BondAt (n : ℕ) : Type := LatticeBond D.torusSide (D.levelSpacing n)
abbrev PlaquetteAt (n : ℕ) : Type := LatticePlaquette D.torusSide (D.levelSpacing n)
abbrev baseLattice : AddSubgroup D.Space := D.levelSublattice 0
def blockLength (n : ℕ) : ℝ := (D.blockCount : ℝ) * D.levelSpacing n
def blockPartition (n : ℕ) : Set (Set D.Space) := D.cubePartition (D.blockLength n)
def IsStdPartition (π : Set (Set D.Space)) : Prop :=
  ∃ n : ℕ, (D.AdmitsPartition (D.levelSpacing n) ∧ π = D.cubePartition (D.levelSpacing n)) ∨
    (D.AdmitsPartition (D.blockLength n) ∧ π = D.blockPartition n)
def cubeAt (n : ℕ) (y : D.Space) : Set D.Space := supCube (D.levelSpacing n) y
def baseBlock (n : ℕ) (y : D.Space) : Set D.Space :=
  latticeBlock (D.levelSpacing n) (D.levelSpacing 0) y
def coarseBlock (k : ℕ) (y : D.Space) : Set D.Space :=
  latticeBlock (D.levelSpacing (k + 1)) (D.levelSpacing k) y
end ScaleData
structure SeparatedChain (D : ScaleData) where
  set : ℕ → Set D.Space
  mono : ∀ n, n < D.lastLevel → set (n + 1) ⊆ set n
  cubeUnion : ∀ n, n ≤ D.lastLevel → (set n).Nonempty → IsUnionOfCubes (D.blockPartition n) (set n)
  separation : ∀ n, n < D.lastLevel →
    ENNReal.ofReal ((D.gapCount : ℝ) * D.blockLength n) <
      setSupDist (closedComplement (set n)) (set (n + 1))
  eq_empty_of_gt : ∀ n, D.lastLevel < n → set n = ∅
namespace SeparatedChain
variable {D : ScaleData} (B : SeparatedChain D)
def lastNonempty : ℕ := sSup {n | n ≤ D.lastLevel ∧ (B.set n).Nonempty}
def shell (n : ℕ) : Set D.Space :=
  open Classical in
  if n < D.lastLevel then closure (B.set n \ B.set (n + 1))
  else if n = D.lastLevel then B.set n else ∅
def shellSites (n : ℕ) : Set D.Space := (D.levelSublattice n : Set D.Space) ∩ B.shell n
def shellSitesUnion : Set D.Space := ⋃ n ∈ Iic D.lastLevel, B.shellSites n
def localSpacing (y : D.Space) : ℝ := D.levelSpacing (sInf {n | y ∈ B.shellSites n})
def localCube (y : D.Space) : Set D.Space := supCube (B.localSpacing y) y
def localDoubleCube (y : D.Space) : Set D.Space := supCube (2 * B.localSpacing y) y
def scaledLength (Γ : List LiftedSegment) : ℝ :=
  ∑ n ∈ Finset.Icc 1 D.lastLevel, (D.levelSpacing n)⁻¹ * pathLengthIn D.torusSide Γ (B.shell n) +
    (D.levelSpacing 0)⁻¹ * pathLengthIn D.torusSide Γ (B.set 1)ᶜ
def scaledDist (y y' : D.Space) : ℝ :=
  sInf {r | ∃ Γ : List LiftedSegment, IsTreeGraph D.torusSide Γ ∧ y ∈ segmentsSupport D.torusSide Γ ∧
    y' ∈ segmentsSupport D.torusSide Γ ∧ r = B.scaledLength Γ}
end SeparatedChain
def physicalInLevelUnits (L : ℕ) (hL : DimFourOddBlockingFactorGeThirteen 4 L) (m K t : ℕ)
    (_ : t ≤ K) (m' r : ℕ) : ScaleData where
  L := L
  blocking := hL
  baseSpacing := (L : ℝ) ^ (-(t : ℤ))
  baseSpacing_pos := by
    have : (0 : ℝ) < L := by exact_mod_cast (by have := hL.thirteen_le; omega)
    positivity
  lastLevel := t
  blockCount := L ^ m'
  blockCount_pow := ⟨m', rfl⟩
  gapCount := L ^ r
  gapCount_pow := ⟨r, rfl⟩
  torusSide := 2 * (L : ℝ) ^ (m + K - t)
  torusSide_evenMultiple := by
    have hpos : 0 < L := by have := hL.thirteen_le; omega
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    refine ⟨L ^ (m + K - t), pow_pos hpos _, ?_⟩
    rw [zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hL0)]
    push_cast
    ring
end GeneralTorus
end YangMills.Construction
