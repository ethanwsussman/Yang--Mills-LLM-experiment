import YangMills.Construction.Geometry.BoxChart
import YangMills.Construction.Lattice.BlocksAndCorridors
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def standardCubePartition (L m : ℕ) (i : ℤ) : Set (Set (FourTorus L m)) :=
  range (cubeAround : Site L m i → Set (FourTorus L m))
def scaledCubeIndex (K k n : ℕ) : ℤ := levelDepth K k - n
def coarseCubeIndex (K m' j : ℕ) : ℤ := scaledCubeIndex K j m'
theorem meshSize_scaledCubeIndex (hL : L ≠ 0) (K k n : ℕ) :
    meshSize L (scaledCubeIndex K k n) = (L : ℝ) ^ n * meshSize L (levelDepth K k) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  simp only [meshSize, scaledCubeIndex, sub_eq_add_neg, neg_add, neg_neg]
  rw [zpow_add₀ hL', zpow_natCast, mul_comm]
def partitionCubesIn (i : ℤ) (X : Set (FourTorus L m)) : Set (Set (FourTorus L m)) :=
  {Q | Q ∈ standardCubePartition L m i ∧ Q ⊆ X}
def IsPartitionRegion (i : ℤ) (X : Set (FourTorus L m)) : Prop :=
  ∃ C ⊆ standardCubePartition L m i, X = ⋃₀ C
def complementRegion (i : ℤ) (X : Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃₀ (standardCubePartition L m i \ partitionCubesIn i X)
def CubesMeet (Q Q' : Set (FourTorus L m)) : Prop := (Q ∩ Q').Nonempty
def IsCubeFace (i : ℤ) (F Q : Set (FourTorus L m)) : Prop :=
  ∃ y : Site L m i, Q = cubeAround y ∧ ∃ (μ : Fin 4) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
    F = {x | x ∈ Q ∧ x μ = (y : FourTorus L m) μ +
      ((ε * meshSize L i / 2 : ℝ) : AddCircle (torusSide L m))}
def CubesShareFace (i : ℤ) (Q Q' : Set (FourTorus L m)) : Prop :=
  IsCubeFace i (Q ∩ Q') Q ∧ IsCubeFace i (Q ∩ Q') Q'
def CubeIntersects (Q Y : Set (FourTorus L m)) : Prop := (Q ∩ Y).Nonempty
def RegionsMeet (i : ℤ) (X X' : Set (FourTorus L m)) : Prop :=
  ∃ Q ∈ partitionCubesIn i X, ∃ Q' ∈ partitionCubesIn i X', CubesMeet Q Q'
def IsCubeChainIn (i : ℤ) (X : Set (FourTorus L m)) (c : List (Set (FourTorus L m))) : Prop :=
  (∀ Q ∈ c, Q ∈ partitionCubesIn i X) ∧ c.IsChain CubesMeet
def IsFaceChainIn (i : ℤ) (X : Set (FourTorus L m)) (c : List (Set (FourTorus L m))) : Prop :=
  (∀ Q ∈ c, Q ∈ partitionCubesIn i X) ∧ c.IsChain (CubesShareFace i)
def ChainConnectedIn (i : ℤ) (X Q Q' : Set (FourTorus L m)) : Prop :=
  ∃ c, IsCubeChainIn i X c ∧ c.head? = some Q ∧ c.getLast? = some Q'
def FaceChainConnectedIn (i : ℤ) (X Q Q' : Set (FourTorus L m)) : Prop :=
  ∃ c, IsFaceChainIn i X c ∧ c.head? = some Q ∧ c.getLast? = some Q'
def IsFaceConnectedRegion (i : ℤ) (X : Set (FourTorus L m)) : Prop :=
  X.Nonempty ∧ ∀ Q ∈ partitionCubesIn i X, ∀ Q' ∈ partitionCubesIn i X,
    FaceChainConnectedIn i X Q Q'
def regionComponents (i : ℤ) (X : Set (FourTorus L m)) : Set (Set (FourTorus L m)) :=
  {C | ∃ Q ∈ partitionCubesIn i X, C = ⋃₀ {Q' | ChainConnectedIn i X Q Q'}}
def addCubeLayer (i : ℤ) (X : Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃₀ {Q | Q ∈ standardCubePartition L m i ∧ ∃ Q' ∈ partitionCubesIn i X, CubesMeet Q Q'}
def peelCubeLayer (i : ℤ) (X : Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃₀ {Q | Q ∈ partitionCubesIn i X ∧
    ¬∃ Q' ∈ partitionCubesIn i (complementRegion i X), CubesMeet Q Q'}
def layerEnlargement (i : ℤ) (X : Set (FourTorus L m)) : ℤ → Set (FourTorus L m)
  | Int.ofNat n => (addCubeLayer i)^[n] X
  | Int.negSucc n => (peelCubeLayer i)^[n + 1] X
def cubeHull (i : ℤ) (Y : Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃₀ {Q | Q ∈ standardCubePartition L m i ∧ CubeIntersects Q Y}
def IsPartitionBox (i : ℤ) (X : Set (FourTorus L m)) : Prop :=
  IsPartitionRegion i X ∧ Nonempty (TorusBox.BoxChart (torusSide L m) X)
def cornerCube (y : Fin 4 → ℝ) (t : ℝ) : Set (Fin 4 → ℝ) :=
  TorusBox.boxOfIntervals y fun μ => y μ + t
def LiesInCornerCube (L m : ℕ) (i : ℤ) (C : Set (FourTorus L m)) (y : Fin 4 → ℝ) : Prop :=
  C ⊆ TorusMetric.torusProj (torusSide L m) '' cornerCube y (100 * meshSize L i)
def IsSmallRegionComponent (i : ℤ) (X C : Set (FourTorus L m)) : Prop :=
  C ∈ regionComponents i X ∧ 100 * meshSize L i < torusSide L m ∧ ∃ y, LiesInCornerCube L m i C y
def liftToCornerCube (i : ℤ) (C : Set (FourTorus L m)) (y : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  {v | v ∈ cornerCube y (100 * meshSize L i) ∧ TorusMetric.torusProj (torusSide L m) v ∈ C}
def boundingBox (A : Set (Fin 4 → ℝ)) : Set (Fin 4 → ℝ) :=
  ⋂₀ {P | A ⊆ P ∧ ∃ a b, P = TorusBox.boxOfIntervals a b}
def componentBox (i : ℤ) (C : Set (FourTorus L m)) : Set (FourTorus L m) :=
  TorusMetric.torusProj (torusSide L m) ''
    boundingBox (liftToCornerCube i C (Classical.epsilon (LiesInCornerCube L m i C)))
def boxingOnce (i : ℤ) (X : Set (FourTorus L m)) : Set (FourTorus L m) :=
  X ∪ ⋃₀ (componentBox i '' {C | IsSmallRegionComponent i X C})
def boxClosure (i : ℤ) (X : Set (FourTorus L m)) : Set (FourTorus L m) :=
  (boxingOnce i)^[sInf {n | (boxingOnce i)^[n + 1] X = (boxingOnce i)^[n] X}] X
end YangMills.Construction.PeriodicLattice
