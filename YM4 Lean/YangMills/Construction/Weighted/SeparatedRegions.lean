import YangMills.Construction.Blocking.FourDimOddFactor
import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace Weighted
structure TorusData where
  L : ℕ
  blocking : YangMills.Construction.Blocking.FourDimOddFactor 4 L
  blockNumber : ℕ
  blockNumber_power : ∃ k : ℕ, blockNumber = L ^ k
  le_blockNumber : L ≤ blockNumber
  gapNumber : ℕ
  gapNumber_power : ∃ k : ℕ, gapNumber = L ^ k
  le_gapNumber : L ≤ gapNumber
  bareSpacing : ℝ
  bareSpacing_pos : 0 < bareSpacing
  top : ℕ
  side : ℝ
  side_multiple : ∃ k : ℕ, 0 < k ∧
    side = 2 * k * ((blockNumber : ℝ) * ((L : ℝ) ^ top * bareSpacing))
namespace TorusData
variable (D : TorusData)
def scale (n : ℕ) : ℝ := (D.L : ℝ) ^ n * D.bareSpacing
abbrev Space : Type := Torus4 D.side
def latticeAt (σ : ℝ) : Set D.Space :=
  {x | ∃ k : Fin 4 → ℤ, x = torusProj D.side fun μ => σ * (k μ : ℝ)}
def cubeAround (σ : ℝ) (y : D.Space) : Set D.Space := {x | torusSupNorm (x - y) ≤ σ / 2}
def partitionAt (σ : ℝ) : Set (Set D.Space) := D.cubeAround σ '' D.latticeAt σ
def IsCubeUnionAt (σ : ℝ) (X : Set D.Space) : Prop :=
  ∃ C ⊆ D.partitionAt σ, X = ⋃₀ C
def closedComplement (X : Set D.Space) : Set D.Space := closure Xᶜ
end TorusData
structure SeparatedChain (D : TorusData) where
  stage : ℕ → Set D.Space
  decreasing : ∀ n, n < D.top → stage (n + 1) ⊆ stage n
  cubeUnion : ∀ n, n ≤ D.top →
    D.IsCubeUnionAt ((D.blockNumber : ℝ) * D.scale n) (stage n)
  separated : ∀ n, n < D.top →
    ENNReal.ofReal ((D.gapNumber : ℝ) * (D.blockNumber : ℝ) * D.scale n) <
      setSupDist (D.closedComplement (stage n)) (stage (n + 1))
  empty_above : ∀ n, D.top < n → stage n = ∅
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def layer (n : ℕ) : Set D.Space :=
  if n < D.top then closure (B.stage n \ B.stage (n + 1))
  else if n = D.top then B.stage n else ∅
def layerSites (n : ℕ) : Set D.Space := D.latticeAt (D.scale n) ∩ B.layer n
def allSites : Set D.Space := ⋃ n ∈ Finset.range (D.top + 1), B.layerSites n
def siteScale (y : D.Space) : ℝ := D.scale (sInf {n | y ∈ B.layerSites n})
def siteCube (y : D.Space) : Set D.Space := D.cubeAround (B.siteScale y) y
def weightedLength (Γ : List LiftedSegment) : ℝ :=
  ∑ n ∈ Finset.Icc 1 D.top, (D.scale n)⁻¹ * pathLengthIn D.side Γ (B.layer n) +
    (D.scale 0)⁻¹ * pathLengthIn D.side Γ (B.stage 1)ᶜ
def weightedDistance (x x' : D.Space) : ℝ :=
  sInf {r | ∃ Γ : List LiftedSegment, IsTreeGraph D.side Γ ∧ x ∈ segmentsSupport D.side Γ ∧
    x' ∈ segmentsSupport D.side Γ ∧ r = B.weightedLength Γ}
end SeparatedChain
end Weighted
end YangMills.Construction
