import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.MetricNotions
variable {X Y : Type*} (d : X → X → ℝ) (d' : Y → Y → ℝ)
def IsOpenWrt (Z : Set X) : Prop := ∀ x ∈ Z, ∃ r : ℝ, 0 < r ∧ ∀ y, d x y < r → y ∈ Z
def IsClosedWrt (Z : Set X) : Prop := IsOpenWrt d Zᶜ
def closureWrt (Z : Set X) : Set X := {x | ∀ r : ℝ, 0 < r → ∃ y ∈ Z, d x y < r}
def IsCompactWrt (Z : Set X) : Prop :=
  ∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpenWrt d U) → Z ⊆ ⋃₀ 𝒰 →
    ∃ 𝒰' ⊆ 𝒰, 𝒰'.Finite ∧ Z ⊆ ⋃₀ 𝒰'
def IsContinuousWrt (f : X → Y) : Prop :=
  ∀ x, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y, d x y < δ → d' (f x) (f y) < ε
end YangMills.Construction.MetricNotions
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
def torusEuclidDist (L m : ℕ) (x y : FourTorus L m) : ℝ := TorusMetric.torusEuclidNorm (x - y)
def IsTorusIsometry (s : FourTorus L m → FourTorus L m) : Prop :=
  ∀ x y, torusEuclidDist L m (s x) (s y) = torusEuclidDist L m x y
structure TorusLatticeSymmetry (L m K : ℕ) where
  toFun : FourTorus L m → FourTorus L m
  dist_eq : IsTorusIsometry toFun
  image_eq : toFun '' (sublattice L m (K : ℤ) : Set (FourTorus L m)) = sublattice L m (K : ℤ)
namespace TorusLatticeSymmetry
variable (s : TorusLatticeSymmetry L m K)
def pointMap (x : Site L m (K : ℤ)) : Site L m (K : ℤ) :=
  ⟨s.toFun x, by
    have h : s.toFun x ∈ s.toFun '' (sublattice L m (K : ℤ) : Set (FourTorus L m)) := ⟨x, x.2, rfl⟩
    rw [s.image_eq] at h
    exact h⟩
def pairMap (b : Site L m (K : ℤ) × Site L m (K : ℤ)) : Site L m (K : ℤ) × Site L m (K : ℤ) :=
  (s.pointMap b.1, s.pointMap b.2)
end TorusLatticeSymmetry
end YangMills.Construction.PeriodicLattice
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def euclidDist (x y : AmbientSpace) : ℝ := TorusMetric.euclidNormVec (x - y)
def IsSpaceIsometry (s : AmbientSpace → AmbientSpace) : Prop :=
  ∀ x y, euclidDist (s x) (s y) = euclidDist x y
def LatticeSymmetry.pairMap (s : LatticeSymmetry a) (b : LatticePoint a × LatticePoint a) :
    LatticePoint a × LatticePoint a :=
  (s.pointMap b.1, s.pointMap b.2)
end YangMills.Construction.InfiniteLattice
