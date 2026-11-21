import YangMills.Construction.PeriodicOperators.SymmetricKernelOfAQuadraticForm
import YangMills.Construction.Towers.ChartAtTheTrivialConfigurationDefs
import YangMills.Construction.Towers.CovariantAveragesAsDifferentials
import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import YangMills.Construction.Towers.SignsOfTheLeftChartAndOfTheDifferentialsOfTheAverages
import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
def blockSaddle {N N' : Type} (X : KernelMatrix N N) (M : KernelMatrix N N') :
    KernelMatrix (N ⊕ N') (N ⊕ N') :=
  saddleMatrix X (swapKernel M) M
end PeriodicOperators
namespace LocalKernels
inductive FieldComponent
  | background
  | source
  | coarse
def colouredEdgeComponent (L k j : ℕ) (hL : 0 < L) (hj : j ≤ k) : Component k where
  level := j
  level_le := hj
  cellType := .edge
  hasColour := true
  weight := YangMills.Construction.Tower.meshAt L k j ^ 4
  weight_pos := pow_pos (zpow_pos (Nat.cast_pos.2 hL) _) 4
def fieldIndices (L k : ℕ) (hL : 0 < L) : WeightedIndexSet k where
  Slot := FieldComponent
  finite_slot := Finite.of_injective
    (fun p : FieldComponent => match p with
      | .background => (0 : Fin 3)
      | .source => 1
      | .coarse => 2)
    (by
      intro a b h
      cases a <;> cases b <;> first | rfl | exact absurd h (by decide))
  comp := fun
    | .background => colouredEdgeComponent L k 0 hL (Nat.zero_le k)
    | .source => colouredEdgeComponent L k 0 hL (Nat.zero_le k)
    | .coarse => colouredEdgeComponent L k k hL le_rfl
abbrev FieldIdx (L k : ℕ) (hL : 0 < L) : Type := ((fieldIndices L k hL).toPeriodicData L).Carrier
end LocalKernels
namespace Tower
open YangMills.Construction.PeriodicOperators (KernelMatrix compKernel blockSaddle swapKernel
  kernelPairing IsSymmKernel)
open YangMills.Construction.LocalKernels (FieldIdx FieldComponent)
open YangMills.Construction.Matrices (ComplexMatrix2)
section FiniteSide
variable {L n k : ℕ}
abbrev PeriodicField (L n k : ℕ) : Type :=
  complexEdgeForms L n k 0 × complexEdgeForms L n k 0 × complexEdgeForms L n k k
abbrev RealPeriodicField (L n k : ℕ) : Type :=
  edgeFormSpace L n k 0 × edgeFormSpace L n k 0 × edgeFormSpace L n k k
def PeriodicField.RealizedBy (ζ : PeriodicField L n k) (r : RealPeriodicField L n k) : Prop :=
  (ζ.1 : Edge L n k 0 → ComplexMatrix2) = r.1 ∧ (ζ.2.1 : Edge L n k 0 → ComplexMatrix2) = r.2.1 ∧
    (ζ.2.2 : Edge L n k k → ComplexMatrix2) = r.2.2
def PeriodicField.pauliCoeffs (hL : 0 < L) (ζ : PeriodicField L n k) : FieldIdx L k hL → ℂ
  | ⟨.background, ι⟩ => (edgePauliCoordinates L n k 0).coeffs ζ.1.1
      (ι.1, YangMills.Construction.LocalKernels.projPositiveEdge L n k 0 ι.2)
  | ⟨.source, ι⟩ => (edgePauliCoordinates L n k 0).coeffs ζ.2.1.1
      (ι.1, YangMills.Construction.LocalKernels.projPositiveEdge L n k 0 ι.2)
  | ⟨.coarse, ι⟩ => (edgePauliCoordinates L n k k).coeffs ζ.2.2.1
      (ι.1, YangMills.Construction.LocalKernels.projPositiveEdge L n k k ι.2)
def PeriodicField.onQuotient (hL : 0 < L) (ζ : PeriodicField L n k) :
    ((YangMills.Construction.LocalKernels.fieldIndices L k hL).toPeriodicData L).QuotMod
      (2 * L ^ n) → ℂ :=
  Classical.epsilon fun f => ∀ κ : FieldIdx L k hL,
    f (((YangMills.Construction.LocalKernels.fieldIndices L k hL).toPeriodicData L).mkQuot
        (2 * L ^ n) κ) =
      ζ.pauliCoeffs hL κ
def fieldFunctional (ζ : RealPeriodicField L n k) : ℝ :=
  backgroundFunctional
    (YangMills.Construction.IdentityExpChart.expForm (ζ.1 : Edge L n k 0 → ComplexMatrix2))
    ζ.2.1 ζ.2.2
def fieldFunctionalDeriv (L n k : ℕ) (ζ : RealPeriodicField L n k) : ℝ :=
  deriv (fun t : ℝ => fieldFunctional (t • ζ)) 0
def fieldFunctionalSecondDeriv (L n k : ℕ) (ζ ζ' : RealPeriodicField L n k) : ℝ :=
  deriv (fun s : ℝ => deriv (fun t : ℝ => fieldFunctional (s • ζ + t • ζ')) 0) 0
def IsComplexSecondDeriv (L n k : ℕ)
    (β : PeriodicField L n k →ₗ[ℂ] PeriodicField L n k →ₗ[ℂ] ℂ) : Prop :=
  ∀ (ζ ζ' : PeriodicField L n k) (r r' : RealPeriodicField L n k), ζ.RealizedBy r →
    ζ'.RealizedBy r' → β ζ ζ' = (fieldFunctionalSecondDeriv L n k r r' : ℂ)
def complexSecondDeriv (L n k : ℕ) :
    PeriodicField L n k →ₗ[ℂ] PeriodicField L n k →ₗ[ℂ] ℂ :=
  Classical.epsilon (IsComplexSecondDeriv L n k)
end FiniteSide
namespace FullSpace
open YangMills.Construction.Tower.FullSpace.AsDifferentials (complexQuadraticTerm)
section Infinite
variable {L k : ℕ}
abbrev FullField (L k : ℕ) : Type :=
  complexEdgeForms (meshAt L k 0) × complexEdgeForms (meshAt L k 0) ×
    complexEdgeForms (meshAt L k k)
def FullField.IsCompactValued (ζ : FullField L k) : Prop :=
  (ζ.1 : Edge L k 0 → ComplexMatrix2) ∈ edgeFormSpace (meshAt L k 0) ∧
    (ζ.2.1 : Edge L k 0 → ComplexMatrix2) ∈ edgeFormSpace (meshAt L k 0) ∧
    (ζ.2.2 : Edge L k k → ComplexMatrix2) ∈ edgeFormSpace (meshAt L k k)
def FullField.gaugeField (ζ : FullField L k) : Edge L k 0 → ComplexMatrix2 :=
  expForm (ζ.1 : Edge L k 0 → ComplexMatrix2)
def FullField.pauliCoeffs (hL : 0 < L) (ζ : FullField L k) : FieldIdx L k hL → ℂ
  | ⟨.background, ι⟩ => (edgePauliCoordinates L k 0).coeffs ζ.1.1 ι
  | ⟨.source, ι⟩ => (edgePauliCoordinates L k 0).coeffs ζ.2.1.1 ι
  | ⟨.coarse, ι⟩ => (edgePauliCoordinates L k k).coeffs ζ.2.2.1 ι
def zeroExtend (g : Vertex L k k → ComplexMatrix2) : Vertex L k 0 → ComplexMatrix2 :=
  open Classical in
  fun x => if h : ∃ y : Vertex L k k, y.1 = x.1 then g h.choose else 0
def gaugeParam (U B : Edge L k 0 → ComplexMatrix2) : Vertex L k 0 → ComplexMatrix2 :=
  zeroExtend (iterContourLogDrift L k U k B)
def shiftedForm (U B : Edge L k 0 → ComplexMatrix2) : Edge L k 0 → ComplexMatrix2 :=
  B + covDiff U (gaugeParam U B)
def sourceForm (U J : Edge L k 0 → ComplexMatrix2) (μ : Edge L k k → ComplexMatrix2)
    (B : Edge L k 0 → ComplexMatrix2) : ℂ :=
  2 * finiteEdgePairing J (levelBracketTerm U (gaugeParam U B) B) +
    finiteEdgePairing J (levelBracketTerm U (gaugeParam U B)
      (covDiff U (gaugeParam U B))) -
    traceFinsumPairing (restrictToPositiveEdges μ)
      (complexQuadraticTerm L k U (shiftedForm U B) (shiftedForm U B))
def hessianForm (U J : Edge L k 0 → ComplexMatrix2) (μ : Edge L k k → ComplexMatrix2)
    (B : Edge L k 0 → ComplexMatrix2) : ℂ :=
  backgroundForm L k U B B + sourceForm U J μ B
def IsHessianKernel (U J : Edge L k 0 → ComplexMatrix2) (μ : Edge L k k → ComplexMatrix2)
    (X : KernelMatrix (Fin 3 × PositiveEdge (meshAt L k 0))
      (Fin 3 × PositiveEdge (meshAt L k 0))) : Prop :=
  IsSymmKernel (fun _ => 1) X ∧
    ∀ B ∈ complexEdgeForms (meshAt L k 0), HasFiniteSupp (restrictToPositiveEdges B) →
      kernelPairing (fun _ => 1) X ((edgePauliCoordinates L k 0).coeffs B) ((edgePauliCoordinates L k 0).coeffs B) =
        hessianForm U J μ B
def hessianKernel (U J : Edge L k 0 → ComplexMatrix2) (μ : Edge L k k → ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge (meshAt L k 0))
      (Fin 3 × PositiveEdge (meshAt L k 0)) :=
  Classical.epsilon (IsHessianKernel U J μ)
def hessianSaddle (U J : Edge L k 0 → ComplexMatrix2) (μ : Edge L k k → ComplexMatrix2) :
    KernelMatrix
      (Fin 3 × PositiveEdge (meshAt L k 0) ⊕ Fin 3 × PositiveEdge (meshAt L k k))
      (Fin 3 × PositiveEdge (meshAt L k 0) ⊕ Fin 3 × PositiveEdge (meshAt L k k)) :=
  blockSaddle (hessianKernel U J μ) (iterCovariantKernel L k U)
def vectorOp (ζ : FullField L k) :
    KernelMatrix
      (Fin 3 × PositiveEdge (meshAt L k 0) ⊕ Fin 3 × PositiveEdge (meshAt L k k))
      (Fin 3 × PositiveEdge (meshAt L k 0) ⊕ Fin 3 × PositiveEdge (meshAt L k k)) :=
  hessianSaddle ζ.gaugeField ζ.2.1 ζ.2.2
def ghostOp (ζ : FullField L k) :
    KernelMatrix (Fin 3 × Vertex L k 0 ⊕ Fin 3 × Vertex L k k)
      (Fin 3 × Vertex L k 0 ⊕ Fin 3 × Vertex L k k) :=
  laplacianSaddle L k ζ.gaugeField
def backgroundOfCoeffs (hL : 0 < L) (f : FieldIdx L k hL → ℂ) : Edge L k 0 → ComplexMatrix2 :=
  (edgePauliCoordinates L k 0).ofCoeffs fun ι => f ⟨.background, ι⟩
def sourceOfCoeffs (hL : 0 < L) (f : FieldIdx L k hL → ℂ) : Edge L k 0 → ComplexMatrix2 :=
  (edgePauliCoordinates L k 0).ofCoeffs fun ι => f ⟨.source, ι⟩
def coarseOfCoeffs (hL : 0 < L) (f : FieldIdx L k hL → ℂ) : Edge L k k → ComplexMatrix2 :=
  (edgePauliCoordinates L k k).ofCoeffs fun ι => f ⟨.coarse, ι⟩
def vectorOpOfCoeffs (hL : 0 < L) (f : FieldIdx L k hL → ℂ) :
    KernelMatrix
      (Fin 3 × PositiveEdge (meshAt L k 0) ⊕ Fin 3 × PositiveEdge (meshAt L k k))
      (Fin 3 × PositiveEdge (meshAt L k 0) ⊕ Fin 3 × PositiveEdge (meshAt L k k)) :=
  hessianSaddle (expForm (backgroundOfCoeffs hL f)) (sourceOfCoeffs hL f)
    (coarseOfCoeffs hL f)
def ghostOpOfCoeffs (hL : 0 < L) (f : FieldIdx L k hL → ℂ) :
    KernelMatrix (Fin 3 × Vertex L k 0 ⊕ Fin 3 × Vertex L k k)
      (Fin 3 × Vertex L k 0 ⊕ Fin 3 × Vertex L k k) :=
  laplacianSaddle L k (expForm (backgroundOfCoeffs hL f))
end Infinite
end FullSpace
end Tower
end YangMills.Construction
end
