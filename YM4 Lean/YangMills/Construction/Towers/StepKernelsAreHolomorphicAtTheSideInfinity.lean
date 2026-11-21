import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.CovariantLinearAverages
import YangMills.Construction.Towers.PolydiscsOfDoubleBlocks
import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.StepKernelHolomorphy
variable {L k j : ℕ}
def kernelCoeff (V : Edge L k j → Matrices.ComplexMatrix2) (c : Edge L k (j + 1))
    (b : PositiveEdge (meshAt L k j)) (a a' : Fin 3) : ℂ :=
  pauliCoeff a' (covariantSmoothingDeriv V (basisForm a b) c)
def contourConjCoeff (V : Edge L k j → Matrices.ComplexMatrix2) (y : Vertex L k (j + 1))
    (x : Vertex L k j) (a a' : Fin 3) : ℂ :=
  pauliCoeff a' (Matrices.ComplexMatrix2.conjugateBy (complexContourMean L V y x)
    (Matrices.ComplexMatrix2.pauliFamily a))
def IsHolomorphicInValues (r : ℝ) (c : Edge L k (j + 1))
    (h : (Edge L k j → Matrices.ComplexMatrix2) → ℂ) : Prop :=
  ∃ _ : Fintype (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c),
    ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      Matrices.GroupLieProduct.IsHolomorphicToCoords β LeftChartFields.scalarCoords
        (DoubleBlockPolydisc.leftComponents ⁻¹'
          DoubleBlockPolydisc.Infinite.polydiscPositive L k j r c)
        fun p => h (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c
          (DoubleBlockPolydisc.leftComponents p))
def DependsOnlyOnDoubleBlock (r : ℝ) (c : Edge L k (j + 1))
    (h : (Edge L k j → Matrices.ComplexMatrix2) → ℂ) : Prop :=
  ∀ V ∈ smallComplexFields L k j, V ∈ nearIdentityPolydisc L k j r c →
    h V = h (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c fun b => V b)
structure KernelHolomorphyAt (L k j : ℕ) (c : Edge L k (j + 1)) : Prop where
  isRelativelyOpen_polydisc : Matrices.ComplexMatrix2.IsRelativelyOpen
    (Matrices.GroupLieProduct.unimodularPi
      (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c))
    (DoubleBlockPolydisc.Infinite.polydiscPositive L k j (3 / 4 * polydiscRadius L) c)
  holomorphic_kernel : ∀ b : PositiveEdge (meshAt L k j),
    b.1 ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c → ∀ a a' : Fin 3,
      IsHolomorphicInValues (3 / 4 * polydiscRadius L) c
        fun V => kernelCoeff V c b a a'
  local_kernel : ∀ b : PositiveEdge (meshAt L k j),
    b.1 ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c → ∀ a a' : Fin 3,
      DependsOnlyOnDoubleBlock (3 / 4 * polydiscRadius L) c
        fun V => kernelCoeff V c b a a'
  holomorphic_conj : ∀ y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))),
    ∀ x ∈ cubeVertices L (meshAt L k j) y, ∀ a a' : Fin 3,
      IsHolomorphicInValues (3 / 4 * polydiscRadius L) c
        fun V => contourConjCoeff V y x a a'
  local_conj : ∀ y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))),
    ∀ x ∈ cubeVertices L (meshAt L k j) y, ∀ a a' : Fin 3,
      DependsOnlyOnDoubleBlock (3 / 4 * polydiscRadius L) c
        fun V => contourConjCoeff V y x a a'
def KernelsHolomorphic : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    ∀ c : Edge L k (j + 1), c.IsPositivelyOriented → KernelHolomorphyAt L k j c
end YangMills.Construction.Tower.FullSpace.StepKernelHolomorphy
end
