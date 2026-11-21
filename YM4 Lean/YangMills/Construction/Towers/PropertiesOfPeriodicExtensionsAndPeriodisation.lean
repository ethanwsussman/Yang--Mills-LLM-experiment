import YangMills.Construction.Towers.CovariantAveragesAsDifferentials
import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import YangMills.Construction.Towers.PeriodicExtensionsLocalKernelsAndKernelsThatDescend
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace LocalKernels
open PeriodicOperators (KernelMatrix applyKernel compKernel periodization)
namespace Periodisation
def periodSide (L n : ℕ) : ℕ := 2 * L ^ n
section Brackets
variable {k : ℕ} (L n : ℕ)
abbrev Idx (I : WeightedIndexSet k) : Type := (I.toPeriodicData L).Carrier
def weightedBracket (I : WeightedIndexSet k) (f g : Idx L I → ℂ) : ℂ :=
  PeriodicOperators.wPairing (I.toPeriodicData L).weightOf f g
def quotBracket (I : WeightedIndexSet k) (f g : I.ImageCarrier L n → ℂ) : ℂ :=
  PeriodicOperators.wPairing (I.imageWeight L n) f g
def kernelT (I I' : WeightedIndexSet k) (T : KernelMatrix (Idx L I) (Idx L I')) :
    KernelMatrix (Idx L I') (Idx L I) :=
  PeriodicOperators.wTranspose (I.toPeriodicData L).weightOf (I'.toPeriodicData L).weightOf T
def quotMatrixT (I I' : WeightedIndexSet k)
    (M : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n)) :
    KernelMatrix (I'.ImageCarrier L n) (I.ImageCarrier L n) :=
  PeriodicOperators.wTranspose (I.imageWeight L n) (I'.imageWeight L n) M
abbrev IsRLocal (I I' : WeightedIndexSet k) (R : ℝ) (T : KernelMatrix (Idx L I) (Idx L I')) : Prop :=
  IsLocalKernel (I.toPeriodicData L) (I'.toPeriodicData L) R T
end Brackets
def IsRepresentedBy {N N' : Type} (D : Set (N → ℂ)) (φ : (N → ℂ) → N' → ℂ) (T : KernelMatrix N N') :
    Prop :=
  ∀ f ∈ D, φ f = applyKernel T f
structure CellClass (k : ℕ) where
  level : ℕ
  level_le : level ≤ k
  cellType : CellType
namespace CellClass
open Tower
variable {k : ℕ} (L n : ℕ)
def vertexClass (k j : ℕ) (h : j ≤ k) : CellClass k := ⟨j, h, .vertex⟩
def edgeClass (k j : ℕ) (h : j ≤ k) : CellClass k := ⟨j, h, .edge⟩
def colourComponent (A : CellClass k) : Component k :=
  ⟨A.level, A.level_le, A.cellType, true, 1, one_pos⟩
def colourPairs (A : CellClass k) : WeightedIndexSet k :=
  WeightedIndexSet.ofComponent A.colourComponent
def fullSpace : CellClass k → PairedFunctionSpace
  | ⟨j, _, .vertex⟩ => pairedFunctions (FullSpace.Vertex L k j)
  | ⟨j, _, .edge⟩ => FullSpace.edgePairedSpace (meshAt L k j)
  | ⟨j, _, .face⟩ => pairedFunctions (FullSpace.Face L k j)
def quotSpace : CellClass k → PairedFunctionSpace
  | ⟨j, _, .vertex⟩ => pairedFunctions (Vertex L n k j)
  | ⟨j, _, .edge⟩ => edgePairedSpace L n k j
  | ⟨j, _, .face⟩ => pairedFunctions (Face L n k j)
def cellFn : (A : CellClass k) → ((fullSpace L A).index → Matrices.ComplexMatrix2) →
    Cell L k A.level A.cellType → Matrices.ComplexMatrix2
  | ⟨_, _, .vertex⟩, f => f
  | ⟨_, _, .edge⟩, f => FullSpace.restrictToPositiveEdges f
  | ⟨_, _, .face⟩, f => f
def quotCellFn : (A : CellClass k) → ((quotSpace L n A).index → Matrices.ComplexMatrix2) →
    QuotientCell L n k A.level A.cellType → Matrices.ComplexMatrix2
  | ⟨_, _, .vertex⟩, f => f
  | ⟨_, _, .edge⟩, f => restrictToPositiveEdges f
  | ⟨_, _, .face⟩, f => f
def coeffsOn (A : CellClass k) (f : (fullSpace L A).index → Matrices.ComplexMatrix2) :
    Idx L A.colourPairs → ℂ :=
  fun ι => toPauliCoeffs (cellFn L A f) ι.2
def quotCoeffsOn (A : CellClass k) (f : (quotSpace L n A).index → Matrices.ComplexMatrix2) :
    A.colourPairs.ImageCarrier L n → ℂ :=
  fun κ => toPauliCoeffs (quotCellFn L n A f) κ.2.1
def ofCoeffs (A : CellClass k) (g : Idx L A.colourPairs → ℂ) :
    Cell L k A.level A.cellType → Matrices.ComplexMatrix2 :=
  ofPauliCoeffs fun ι => g ⟨(), ι⟩
def ofQuotCoeffs (A : CellClass k) (g : A.colourPairs.ImageCarrier L n → ℂ) :
    QuotientCell L n k A.level A.cellType → Matrices.ComplexMatrix2 :=
  open Classical in ofPauliCoeffs fun ι =>
    if h : ι ∈ A.colourComponent.image L n then g ⟨(), ⟨ι, h⟩⟩ else 0
end CellClass
section EvaluationMaps
open Tower
variable {k : ℕ} (L n : ℕ) (A A' : CellClass k)
def IsRepresentedOnPairs (φ : (CellClass.fullSpace L A).complexSubmodule →
      (CellClass.fullSpace L A').index → Matrices.ComplexMatrix2)
    (T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs)) : Prop :=
  ∀ f : (CellClass.fullSpace L A).complexSubmodule,
    φ f ∈ (CellClass.fullSpace L A').complexSubmodule ∧
      CellClass.coeffsOn L A' (φ f) = applyKernel T (CellClass.coeffsOn L A f)
def DescendsToMapOnPairs (T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs))
    (φ : (CellClass.quotSpace L n A).complexSubmodule →ₗ[ℂ]
      (CellClass.quotSpace L n A').complexSubmodule) : Prop :=
  ∃ M : KernelMatrix (A.colourPairs.ImageCarrier L n) (A'.colourPairs.ImageCarrier L n),
    (∀ f : (CellClass.quotSpace L n A).complexSubmodule,
      CellClass.quotCoeffsOn L n A' (φ f) = applyKernel M (CellClass.quotCoeffsOn L n A f)) ∧
    KernelDescends L n A.colourPairs A'.colourPairs T M
def Periodizes (R : ℝ)
    (φFull : ((CellClass.fullSpace L A).index → Matrices.ComplexMatrix2) →
      (CellClass.fullSpace L A').index → Matrices.ComplexMatrix2)
    (φQuot : ((CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2) →
      (CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2) : Prop :=
  ∃ (T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs))
    (φ : (CellClass.quotSpace L n A).complexSubmodule →ₗ[ℂ]
      (CellClass.quotSpace L n A').complexSubmodule),
    IsRLocal L A.colourPairs A'.colourPairs R T ∧
    IsRepresentedOnPairs L A A' (fun f => φFull f) T ∧
    (∀ f : (CellClass.quotSpace L n A).complexSubmodule,
      (φ f : (CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2) = φQuot f) ∧
    DescendsToMapOnPairs L n A A' T φ ∧
    DescendsToMapOnPairs L n A' A (kernelT L A.colourPairs A'.colourPairs T)
      (PairedFunctionSpace.transposeMap φ)
end EvaluationMaps
section Images
open Tower
def ProjCellsClassified (L n k j : ℕ) : Prop :=
  ∀ c : CellType,
    Function.Surjective (Cell.proj n : Cell L k j c → QuotientCell L n k j c) ∧
    ∀ x y : Cell L k j c,
      Cell.proj n x = Cell.proj n y ↔
        ∃ v : Fin 4 → ℤ, y = Cell.translate (periodSide L n • v) x
def ProjEdgesCompatible (L n k j : ℕ) : Prop :=
  (∀ b : FullSpace.Edge L k j,
    (FullSpace.projEdge L n k j b).source = FullSpace.projVertex L n k j b.initial ∧
    (FullSpace.projEdge L n k j b).target = FullSpace.projVertex L n k j b.terminal) ∧
  (∀ b : PeriodicOperators.PosEdge L k j,
    (projPositiveEdge L n k j b).1 = FullSpace.projEdge L n k j b.1) ∧
  ∀ p : FullSpace.Face L k j,
    faceEdges (FullSpace.projFace L n k j p) =
      (FullSpace.faceEdges p).map (FullSpace.projEdge L n k j)
def QuotientClassesPeriodic (L n : ℕ) {k : ℕ} (I : WeightedIndexSet k) : Prop :=
  Finite (I.ImageCarrier L n) ∧
  (∃ φ : (I.toPeriodicData L).QuotMod (periodSide L n) → I.ImageCarrier L n,
    Function.Bijective φ ∧
      ∀ ι, φ ((I.toPeriodicData L).mkQuot (periodSide L n) ι) = I.proj L n ι) ∧
  BijOn (I.lift L n (E := ℂ)) univ
    {g | ∀ (v : Fin 4 → ℤ) (ι : Idx L I),
      g ((I.toPeriodicData L).translate (periodSide L n • v) ι) = g ι}
end Images
section Kernels
variable {k : ℕ} (L n : ℕ)
def MatrixEqPeriodSum (I I' : WeightedIndexSet k)
    (T : KernelMatrix (Idx L I) (Idx L I'))
    (M : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n)) : Prop :=
  (∀ (ι' : Idx L I') (ι : Idx L I),
    M (I'.proj L n ι') (I.proj L n ι) =
      periodization (I.toPeriodicData L) (I'.toPeriodicData L) T (periodSide L n) ι' ι) ∧
  ∀ M' : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n),
    KernelDescends L n I I' T M' → M' = M
def DescendsAlgebra : Prop :=
  ∀ (I I' I'' : WeightedIndexSet k) (R : ℝ), 0 ≤ R →
    ∀ (T T' : KernelMatrix (Idx L I) (Idx L I'))
      (S : KernelMatrix (Idx L I'') (Idx L I))
      (M M' : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n))
      (N : KernelMatrix (I''.ImageCarrier L n) (I.ImageCarrier L n)),
      IsRLocal L I I' R T → IsRLocal L I I' R T' → IsRLocal L I'' I R S →
      KernelDescends L n I I' T M → KernelDescends L n I I' T' M' →
      KernelDescends L n I'' I S N →
        MatrixEqPeriodSum L n I I' T M ∧
        IsRLocal L I I' R (T + T') ∧ KernelDescends L n I I' (T + T') (M + M') ∧
        IsRLocal L I'' I' (2 * R) (compKernel T S) ∧
        KernelDescends L n I'' I' (compKernel T S) (compKernel M N) ∧
        (2 * R < (periodSide L n : ℝ) →
          (∀ (ι' : Idx L I') (ι : Idx L I) (v : Fin 4 → ℤ),
            T ((I'.toPeriodicData L).translate (periodSide L n • v) ι')
              ((I.toPeriodicData L).translate (periodSide L n • v) ι) = T ι' ι) ∧
          IsRLocal L I' I R (kernelT L I I' T) ∧
          KernelDescends L n I' I (kernelT L I I' T) (quotMatrixT L n I I' M))
def LocalKernelFacts : Prop :=
  ∀ (I I' : WeightedIndexSet k) (R : ℝ), 0 ≤ R →
    ∀ T : KernelMatrix (Idx L I) (Idx L I'), IsRLocal L I I' R T →
      (∀ (f : Idx L I → ℂ) (ι' : Idx L I'),
        (Function.support fun ι => T ι' ι * f ι).Finite) ∧
      (∀ f : Idx L I → ℂ, PeriodicOperators.HasFiniteSupport f →
        PeriodicOperators.HasFiniteSupport (applyKernel T f)) ∧
      IsRLocal L I' I R (kernelT L I I' T) ∧
      ∀ (g : Idx L I' → ℂ) (f : Idx L I → ℂ), PeriodicOperators.HasFiniteSupport f →
        weightedBracket L I (applyKernel (kernelT L I I' T) g) f =
          weightedBracket L I' g (applyKernel T f)
def LinearMapHasMatrix : Prop :=
  ∀ (I I' : WeightedIndexSet k) (φ : (I.ImageCarrier L n → ℂ) →ₗ[ℂ] (I'.ImageCarrier L n → ℂ)),
    ∃! M : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n), IsRepresentedBy univ φ M
open Tower in
def PairBracketTranspose : Prop :=
  ∀ A A' : CellClass k, A.cellType ≠ .face → A'.cellType ≠ .face →
    (∀ f g : (CellClass.fullSpace L A).complexSubmodule,
      ((CellClass.fullSpace L A).IsFinitelySupported f ∨
          (CellClass.fullSpace L A).IsFinitelySupported g) →
        weightedBracket L A.colourPairs (CellClass.coeffsOn L A f) (CellClass.coeffsOn L A g) =
          (CellClass.fullSpace L A).pair f g) ∧
    ∀ R : ℝ, 0 ≤ R → ∀ T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs),
      IsRLocal L A.colourPairs A'.colourPairs R T →
        ∃ (φ : (CellClass.fullSpace L A).complexSubmodule →ₗ[ℂ]
              (CellClass.fullSpace L A').complexSubmodule)
          (ψ : (CellClass.fullSpace L A').complexSubmodule →ₗ[ℂ]
              (CellClass.fullSpace L A).complexSubmodule),
          IsRepresentedOnPairs L A A' (fun f => φ f) T ∧
          IsRepresentedOnPairs L A' A (fun f => ψ f) (kernelT L A.colourPairs A'.colourPairs T) ∧
          PairedFunctionSpace.PreservesFiniteSupport φ ∧ PairedFunctionSpace.IsTransposeMap φ ψ ∧
          ψ = PairedFunctionSpace.transposeMap φ
end Kernels
section Bilinear
variable {k : ℕ} (L n : ℕ)
def IsBilinearKernel (I I' I'' : WeightedIndexSet k)
    (H : (Idx L I → ℂ) → (Idx L I' → ℂ) → Idx L I'' → ℂ) (w : I''.ImageCarrier L n → ℂ)
    (T : KernelMatrix (Idx L I') (Idx L I)) : Prop :=
  ∀ (f : Idx L I → ℂ) (f' : Idx L I' → ℂ),
    PeriodicOperators.HasFiniteSupport f → PeriodicOperators.HasFiniteSupport f' →
      weightedBracket L I f (applyKernel T f') = weightedBracket L I'' (I''.lift L n w) (H f f')
def IsBilinearMatrix (I I' I'' : WeightedIndexSet k)
    (H : (I.ImageCarrier L n → ℂ) →ₗ[ℂ] (I'.ImageCarrier L n → ℂ) →ₗ[ℂ]
      (I''.ImageCarrier L n → ℂ))
    (w : I''.ImageCarrier L n → ℂ)
    (M : KernelMatrix (I'.ImageCarrier L n) (I.ImageCarrier L n)) : Prop :=
  ∀ (f : I.ImageCarrier L n → ℂ) (f' : I'.ImageCarrier L n → ℂ),
    quotBracket L n I f (applyKernel M f') = quotBracket L n I'' w (H f f')
def BilinearDescends : Prop :=
  ∀ (I I' I'' : WeightedIndexSet k) (R : ℝ), 0 ≤ R → 4 * R < (periodSide L n : ℝ) →
    ∀ (H : (Idx L I → ℂ) → (Idx L I' → ℂ) → Idx L I'' → ℂ)
      (Hq : (I.ImageCarrier L n → ℂ) →ₗ[ℂ] (I'.ImageCarrier L n → ℂ) →ₗ[ℂ]
        (I''.ImageCarrier L n → ℂ))
      (w : I''.ImageCarrier L n → ℂ),
      IsLocalBilinear (I.toPeriodicData L) (I'.toPeriodicData L) (I''.toPeriodicData L) R H →
      (∀ (f : I.ImageCarrier L n → ℂ) (f' : I'.ImageCarrier L n → ℂ),
        H (I.lift L n f) (I'.lift L n f') = I''.lift L n (Hq f f')) →
      (∀ (f : Idx L I → ℂ) (f' : Idx L I' → ℂ),
        PeriodicOperators.HasFiniteSupport f → PeriodicOperators.HasFiniteSupport f' →
          PeriodicOperators.HasFiniteSupport (H f f')) ∧
      (∃! T, IsBilinearKernel L n I I' I'' H w T) ∧
      (∃! M, IsBilinearMatrix L n I I' I'' Hq w M) ∧
      ∀ T M, IsBilinearKernel L n I I' I'' H w T →
        IsBilinearMatrix L n I I' I'' Hq w M →
          IsRLocal L I' I (2 * R) T ∧ KernelDescends L n I' I T M ∧
          KernelDescends L n I I' (kernelT L I' I T) (quotMatrixT L n I' I M)
end Bilinear
section Action
open Tower
variable (L n k j : ℕ) (h : j ≤ k)
def IsBracketKernel (V J : Edge L n k j → Matrices.ComplexMatrix2)
    (T : KernelMatrix (Idx L (CellClass.edgeClass k j h).colourPairs)
      (Idx L (CellClass.vertexClass k j h).colourPairs)) : Prop :=
  ∀ l ∈ Matrices.GroupLieProduct.tracelessFunctions (FullSpace.Vertex L k j), HasFiniteSupp l →
    ∀ B ∈ FullSpace.complexEdgeForms (meshAt L k j),
      HasFiniteSupp (FullSpace.restrictToPositiveEdges B) →
        traceFinsumPairing l (CellClass.ofCoeffs L (CellClass.vertexClass k j h)
            (applyKernel T (CellClass.coeffsOn L (CellClass.edgeClass k j h) B))) =
          FullSpace.finiteEdgePairing (liftGaugeField L n k j J)
            (FullSpace.levelBracketTerm (liftGaugeField L n k j V) l B)
def IsBracketMatrix (V J : Edge L n k j → Matrices.ComplexMatrix2)
    (M : KernelMatrix ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L n)
      ((CellClass.vertexClass k j h).colourPairs.ImageCarrier L n)) : Prop :=
  ∀ l ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L n k j),
    ∀ B ∈ complexEdgeForms L n k j,
      traceFinsumPairing l (CellClass.ofQuotCoeffs L n (CellClass.vertexClass k j h)
          (applyKernel M (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) B))) =
        edgeFormPairing J (levelBracketTerm V l B)
def BracketTermsFormed (V : Edge L n k j → Matrices.ComplexMatrix2) : Prop :=
  ∀ l ∈ Matrices.GroupLieProduct.tracelessFunctions (FullSpace.Vertex L k j), HasFiniteSupp l →
    ∀ B ∈ FullSpace.complexEdgeForms (meshAt L k j),
      HasFiniteSupp (FullSpace.restrictToPositiveEdges B) →
        FullSpace.levelBracketTerm (liftGaugeField L n k j V) l B ∈
            FullSpace.complexEdgeForms (meshAt L k j) ∧
          HasFiniteSupp (FullSpace.restrictToPositiveEdges
            (FullSpace.levelBracketTerm (liftGaugeField L n k j V) l B))
def CovDiffDescends (V : Edge L n k j → Matrices.ComplexMatrix2) : Prop :=
  Periodizes L n (CellClass.vertexClass k j h) (CellClass.edgeClass k j h) 2
    (FullSpace.covDiff (liftGaugeField L n k j V))
    (covDiff V)
def HessianDescends (V : Edge L n k j → Matrices.ComplexMatrix2) : Prop :=
  Periodizes L n (CellClass.edgeClass k j h) (CellClass.edgeClass k j h) 2
    (FullSpace.complexHessianOperator (liftGaugeField L n k j V))
    (complexHessianOperator V)
def BracketKernelDescends (V J : Edge L n k j → Matrices.ComplexMatrix2) : Prop :=
  (∃! T, IsBracketKernel L n k j h V J T) ∧
  (∃! M, IsBracketMatrix L n k j h V J M) ∧
  ∀ T M, IsBracketKernel L n k j h V J T → IsBracketMatrix L n k j h V J M →
    IsRLocal L (CellClass.edgeClass k j h).colourPairs
      (CellClass.vertexClass k j h).colourPairs 2 T ∧
    KernelDescends L n (CellClass.edgeClass k j h).colourPairs
      (CellClass.vertexClass k j h).colourPairs T M ∧
    KernelDescends L n (CellClass.vertexClass k j h).colourPairs
      (CellClass.edgeClass k j h).colourPairs
      (kernelT L (CellClass.edgeClass k j h).colourPairs
        (CellClass.vertexClass k j h).colourPairs T)
      (quotMatrixT L n (CellClass.edgeClass k j h).colourPairs
        (CellClass.vertexClass k j h).colourPairs M)
def HessianDataDescend : Prop :=
  ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup, ∀ J ∈ complexEdgeForms L n k j,
    BracketTermsFormed L n k j V ∧
    CovDiffDescends L n k j h V ∧
    HessianDescends L n k j h V ∧
    BracketKernelDescends L n k j h V J
end Action
section Averages
open Tower
open Tower.AsDifferentials (boundedSubmodule complexQuadraticTerm)
variable (L n k : ℕ)
def zeroExtend (g : Vertex L n k k → Matrices.ComplexMatrix2) :
    Vertex L n k 0 → Matrices.ComplexMatrix2 :=
  open Classical in fun x => if h : ∃ y : Vertex L n k k, y.1 = x.1 then g h.choose else 0
def fullZeroExtend (g : FullSpace.Vertex L k k → Matrices.ComplexMatrix2) :
    FullSpace.Vertex L k 0 → Matrices.ComplexMatrix2 :=
  open Classical in fun x =>
    if h : ∃ y : FullSpace.Vertex L k k, y.1 = x.1 then g h.choose else 0
abbrev edgesAtZero : CellClass k := CellClass.edgeClass k 0 (Nat.zero_le k)
abbrev verticesAtZero : CellClass k := CellClass.vertexClass k 0 (Nat.zero_le k)
def IsQuadraticKernel (U : Edge L n k 0 → Matrices.ComplexMatrix2)
    (μ : Edge L n k k → Matrices.ComplexMatrix2)
    (T : KernelMatrix (Idx L (edgesAtZero k).colourPairs) (Idx L (edgesAtZero k).colourPairs)) :
    Prop :=
  ∀ B ∈ FullSpace.complexEdgeForms (meshAt L k 0),
    HasFiniteSupp (FullSpace.restrictToPositiveEdges B) →
    ∀ B' ∈ FullSpace.complexEdgeForms (meshAt L k 0),
      HasFiniteSupp (FullSpace.restrictToPositiveEdges B') →
        traceFinsumPairing (FullSpace.restrictToPositiveEdges B)
            (CellClass.ofCoeffs L (edgesAtZero k)
              (applyKernel T (CellClass.coeffsOn L (edgesAtZero k) B'))) =
          traceFinsumPairing (FullSpace.restrictToPositiveEdges (liftGaugeField L n k k μ))
            (FullSpace.AsDifferentials.complexQuadraticTerm L k
              (liftGaugeField L n k 0 U) B B')
def IsQuadraticMatrix (U : Edge L n k 0 → Matrices.ComplexMatrix2)
    (μ : Edge L n k k → Matrices.ComplexMatrix2)
    (M : KernelMatrix ((edgesAtZero k).colourPairs.ImageCarrier L n)
      ((edgesAtZero k).colourPairs.ImageCarrier L n)) : Prop :=
  ∀ B ∈ complexEdgeForms L n k 0, ∀ B' ∈ complexEdgeForms L n k 0,
    traceFinsumPairing (restrictToPositiveEdges B) (CellClass.ofQuotCoeffs L n (edgesAtZero k)
        (applyKernel M (CellClass.quotCoeffsOn L n (edgesAtZero k) B'))) =
      traceFinsumPairing (restrictToPositiveEdges μ) (complexQuadraticTerm L n k U B B')
def QuadraticTermsFormed (U : Edge L n k 0 → Matrices.ComplexMatrix2) : Prop :=
  (∀ B ∈ boundedSubmodule (complexEdgeForms L n k 0),
    ∀ B' ∈ boundedSubmodule (complexEdgeForms L n k 0),
      ∀ c, complexQuadraticTerm L n k U B B' c ∈ Matrices.ComplexMatrix2.traceless) ∧
  (∀ B ∈ boundedSubmodule (FullSpace.complexEdgeForms (meshAt L k 0)),
    ∀ B' ∈ boundedSubmodule (FullSpace.complexEdgeForms (meshAt L k 0)), ∀ c,
      FullSpace.AsDifferentials.complexQuadraticTerm L k
        (liftGaugeField L n k 0 U) B B' c ∈ Matrices.ComplexMatrix2.traceless) ∧
  ∀ B ∈ FullSpace.complexEdgeForms (meshAt L k 0),
    HasFiniteSupp (FullSpace.restrictToPositiveEdges B) →
    ∀ B' ∈ FullSpace.complexEdgeForms (meshAt L k 0),
      HasFiniteSupp (FullSpace.restrictToPositiveEdges B') →
        HasFiniteSupp (FullSpace.AsDifferentials.complexQuadraticTerm L k
          (liftGaugeField L n k 0 U) B B')
def IteratesDescend (U : Edge L n k 0 → Matrices.ComplexMatrix2) : Prop :=
  ∀ (j : ℕ) (h : j ≤ k), 1 ≤ j →
    Periodizes L n (edgesAtZero k) (CellClass.edgeClass k j h) 6
      (FullSpace.complexIterDeriv L k j (liftGaugeField L n k 0 U))
      (complexIterDeriv L n k j U) ∧
    Periodizes L n (edgesAtZero k) (CellClass.edgeClass k j h) 6
      (FullSpace.iterCovariantDeriv L k (liftGaugeField L n k 0 U) j)
      (iterCovariantDeriv L n k U j) ∧
    Periodizes L n (verticesAtZero k) (CellClass.vertexClass k j h) 6
      (FullSpace.iterAdjointCubeAverage L k (liftGaugeField L n k 0 U) j)
      (iterAdjointCubeAverage L n k U j) ∧
    Periodizes L n (edgesAtZero k) (CellClass.vertexClass k j h) 6
      (FullSpace.iterContourLogDrift L k (liftGaugeField L n k 0 U) j)
      (iterContourLogDrift L n k U j)
def ComplexIterLift (U : Edge L n k 0 → Matrices.ComplexMatrix2) : Prop :=
  ∀ j ≤ k, FullSpace.complexIter L k j (liftGaugeField L n k 0 U) =
    liftGaugeField L n k j (PeriodicLattice.complexBlockFieldAtLevel j U)
def ZeroExtendDescends : Prop :=
  Periodizes L n (CellClass.vertexClass k k le_rfl) (verticesAtZero k) 6
    (fullZeroExtend L k) (zeroExtend L n k)
def QuadraticKernelDescends (U : Edge L n k 0 → Matrices.ComplexMatrix2)
    (μ : Edge L n k k → Matrices.ComplexMatrix2) : Prop :=
  (∃! T, IsQuadraticKernel L n k U μ T) ∧
  (∃! M, IsQuadraticMatrix L n k U μ M) ∧
  ∀ T M, IsQuadraticKernel L n k U μ T → IsQuadraticMatrix L n k U μ M →
    IsRLocal L (edgesAtZero k).colourPairs (edgesAtZero k).colourPairs 6 T ∧
    KernelDescends L n (edgesAtZero k).colourPairs (edgesAtZero k).colourPairs T M ∧
    KernelDescends L n (edgesAtZero k).colourPairs (edgesAtZero k).colourPairs
      (kernelT L (edgesAtZero k).colourPairs (edgesAtZero k).colourPairs T)
      (quotMatrixT L n (edgesAtZero k).colourPairs (edgesAtZero k).colourPairs M)
def MeansDescend : Prop :=
  ∀ U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup,
    (U ∈ smallIterateFields L n k ↔
      liftGaugeField L n k 0 U ∈ FullSpace.smallIterateFields L k) ∧
    (U ∈ smallIterateFields L n k → ∀ μ ∈ complexEdgeForms L n k k,
      ComplexIterLift L n k U ∧
      QuadraticTermsFormed L n k U ∧
      IteratesDescend L n k U ∧
      ZeroExtendDescends L n k ∧
      QuadraticKernelDescends L n k U μ)
end Averages
end Periodisation
end LocalKernels
end YangMills.Construction
end
