import YangMills.Construction.Conventions.PositiveConstant
import YangMills.Construction.Towers.ChartAtTheTrivialConfigurationDefs
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATower
import YangMills.Construction.Towers.PeriodicExtensionsLocalKernelsAndKernelsThatDescend
import YangMills.Construction.Towers.SignsOfTheLeftChartAndOfTheDifferentialsOfTheAverages
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
open PeriodicOperators (PeriodicData)
abbrev remainderIndex (L k : ℕ) : PeriodicData := PeriodicOperators.colourEdges L k 0
def IsRemainderConst {C : Type*} (L : C → ℕ) (x : C → ℝ) : Prop :=
  Conventions.DependsOnlyThrough x L
section FiniteSide
variable {L n k : ℕ}
def remainderCoeffs (B : Edge L n k 0 → Matrices.ComplexMatrix2) :
    (remainderIndex L k).Carrier → ℂ :=
  fun ι => (edgePauliCoordinates L n k 0).coeffs B
    (ι.1, LocalKernels.projPositiveEdge L n k 0 ι.2)
def remainderQuotField (B : Edge L n k 0 → Matrices.ComplexMatrix2) :
    (remainderIndex L k).QuotMod (2 * L ^ n) → ℂ :=
  Classical.epsilon fun f => ∀ κ : (remainderIndex L k).Carrier,
    f ((remainderIndex L k).mkQuot (2 * L ^ n) κ) = remainderCoeffs B κ
def scaledRemainderForm (a : Edge L n k 0 → Matrices.ComplexMatrix2) :
    Edge L n k 0 → Matrices.ComplexMatrix2 :=
  finestMesh L k • a
def remainderGaugeField (a : Edge L n k 0 → Matrices.ComplexMatrix2) :
    Edge L n k 0 → Matrices.ComplexMatrix2 :=
  IdentityExpChart.expForm (scaledRemainderForm a)
def edgesOverEdge (c : Edge L n k k) : Set (Edge L n k 0) :=
  PeriodicLattice.bondsInside
    (PeriodicLattice.refinedBlock k c.source ∪ PeriodicLattice.refinedBlock k c.target)
end FiniteSide
namespace FullSpace
variable {L k : ℕ}
def scaledRemainderForm (a : Edge L k 0 → Matrices.ComplexMatrix2) :
    Edge L k 0 → Matrices.ComplexMatrix2 :=
  finestMesh L k • a
def remainderGaugeField (a : Edge L k 0 → Matrices.ComplexMatrix2) :
    Edge L k 0 → Matrices.ComplexMatrix2 :=
  expForm (scaledRemainderForm a)
def edgesOverEdge (c : Edge L k k) : Set (Edge L k 0) :=
  {b | (b.initial : InfiniteLattice.AmbientSpace) ∈
        cubeOfOrder L (meshAt L k 0) k c.initial ∪
          cubeOfOrder L (meshAt L k 0) k c.terminal ∧
      (b.terminal : InfiniteLattice.AmbientSpace) ∈
        cubeOfOrder L (meshAt L k 0) k c.initial ∪
          cubeOfOrder L (meshAt L k 0) k c.terminal}
end FullSpace
end Tower
end YangMills.Construction
end
