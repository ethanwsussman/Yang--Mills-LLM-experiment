import YangMills.Construction.Towers.TheDensityIsABoundedLinearFunctional
import Mathlib
set_option autoImplicit false
open Filter YangMills.Construction.OperatorCalculus YangMills.Construction.OneLoopNotation YangMills.Construction.Tower.UnitLatticeL2
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
section HilbertMaps
variable {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E']
  [InnerProductSpace ℂ E']
def IsConjLinear (W : E → E') : Prop :=
  (∀ f g : E, W (f + g) = W f + W g) ∧ ∀ (c : ℂ) (f : E), W (c • f) = conj c • W f
def IsNormBounded (W : E → E') : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f : E, ‖W f‖ ≤ C * ‖f‖
def IsBddOpMap (M : E → E) : Prop :=
  ∃ B : BddOp E, ∀ ψ : E, B ψ = M ψ
def toBddOp (M : E → E) : BddOp E :=
  Classical.epsilon fun B : BddOp E => ∀ ψ : E, B ψ = M ψ
def IsUnitaryMap (V : E → E) : Prop :=
  IsLinearMap ℂ V ∧ Function.Bijective V ∧ ∀ f : E, ‖V f‖ = ‖f‖
variable [CompleteSpace E]
def ShiftedHalfPositive (z : ℝ) (T : BddOp E) : Prop :=
  IsSelfAdjointOp T ∧ IsBoundedBelowBy (addScalar T z) (z / 2)
end HilbertMaps
section LogFacts
variable (E E' : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
def LogShiftedProps (z : ℝ) : Prop :=
  ∀ T : BddOp E, ShiftedHalfPositive z T →
    (∀ w : ℝ, 0 ≤ w →
      IsTwoSidedInverse (addScalar (addScalar T z) w) (inverseOp (addScalar (addScalar T z) w)) ∧
        ‖inverseOp (addScalar (addScalar T z) w)‖ ≤ (z / 2 + w)⁻¹) ∧
    IsSelfAdjointOp (opLog (addScalar T z)) ∧
    (∀ y : ℝ, 0 < y → NormContinuousOn (resolventDiff (addScalar T z)) 0 y) ∧
    IntegrableOnHalfLine (fun w => ‖resolventDiff (addScalar T z) w‖) ∧
    (∀ r : ℝ, 0 < r → RiemannSumsTendsto (resolventDiff (addScalar T z)) 0 r
      (opIntegral (resolventDiff (addScalar T z)) 0 r)) ∧
    IsLogOf (addScalar T z) (opLog (addScalar T z)) ∧
    ∀ (f : E) (c : ℂ), f ≠ 0 → T f = c • f →
      (c + (z : ℂ)).im = 0 ∧ z / 2 ≤ (c + (z : ℂ)).re ∧
        opLog (addScalar T z) f = ((Real.log (c + (z : ℂ)).re : ℝ) : ℂ) • f
def LogEqIntegralIoi (z : ℝ) : Prop :=
  ∀ T : BddOp E, ShiftedHalfPositive z T →
    opLog (addScalar T z) = opIntegralIoi (resolventDiff (addScalar T z))
def LogCommIntertwiner (z : ℝ) : Prop :=
  ∀ (T : BddOp E) (T' : BddOp E') (V : E → E'),
    ShiftedHalfPositive z T → ShiftedHalfPositive z T' →
    (IsLinearMap ℂ V ∨ IsConjLinear V) → IsNormBounded V →
    (∀ f : E, V (T f) = T' (V f)) →
    ∀ f : E, V (opLog (addScalar T z) f) = opLog (addScalar T' z) (V f)
end LogFacts
def IsWeightMatrix (t : Matrices.ComplexMatrix2) : Prop :=
  t = Matrices.ComplexMatrix2.pauliFamily 2 ∨ t = raisingPauli ∨ t = loweringPauli
def pointwiseStar {ι : Type} (f : L2Field ι) : L2Field ι :=
  Classical.epsilon fun g : L2Field ι => ofCoords g = fieldStar (ofCoords f)
section Tensors
variable {L : ℕ}
def vertexTensor (v : VectorL2 L 1) (X : Matrices.ComplexMatrix2) :
    L2Field (FullSpace.Vertex L 0 0) :=
  Classical.epsilon fun f : L2Field (FullSpace.Vertex L 0 0) =>
    ∀ x : FullSpace.Vertex L 0 0, ofCoords f x = v x 0 • X
def edgeTensor (v : VectorL2 L 4) (X : Matrices.ComplexMatrix2) :
    L2Field (PeriodicOperators.PosEdge L 0 0) :=
  Classical.epsilon fun f : L2Field (PeriodicOperators.PosEdge L 0 0) =>
    ∀ (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
      ofCoords f (FullSpace.forwardEdge x μ) = v x μ • X
end Tensors
section Weights
variable {L K : ℕ} {ι : Type}
def IsSectorTriple (tensor : VectorL2 L K → Matrices.ComplexMatrix2 → L2Field ι)
    (S : BddOp (L2Field ι))
    (S₀ Sp Sm : VectorL2 L K → VectorL2 L K) : Prop :=
  (∀ v, S (tensor v (Matrices.ComplexMatrix2.pauliFamily 2)) =
      tensor (S₀ v) (Matrices.ComplexMatrix2.pauliFamily 2)) ∧
  (∀ v, S (tensor v raisingPauli) = tensor (Sp v) raisingPauli) ∧
  ∀ v, S (tensor v loweringPauli) = tensor (Sm v) loweringPauli
def LogRestrictsToSector (tensor : VectorL2 L K → Matrices.ComplexMatrix2 → L2Field ι)
    (z : ℝ) : Prop :=
  ∀ t : Matrices.ComplexMatrix2, IsWeightMatrix t →
    ∀ (T : BddOp (L2Field ι)) (T' : VectorL2 L K → VectorL2 L K),
      ShiftedHalfPositive z T → (∀ v, T (tensor v t) = tensor (T' v) t) →
      IsBddOpMap T' ∧ ShiftedHalfPositive z (toBddOp T') ∧
        ∀ v, opLog (addScalar T z) (tensor v t) =
          tensor (opLog (addScalar (toBddOp T') z) v) t
def TraceSplitsBySector
    (tensor : VectorL2 L K → Matrices.ComplexMatrix2 → L2Field ι)
    (pos : Fin 3 × ι → InfiniteLattice.AmbientSpace) : Prop :=
  ∀ (S : BddOp (L2Field ι)) (S₀ Sp Sm : VectorL2 L K → VectorL2 L K),
    IsSectorTriple tensor S S₀ Sp Sm →
    IsBddOpMap S₀ ∧ IsBddOpMap Sp ∧ IsBddOpMap Sm ∧
      ∀ x : FullSpace.Vertex L 0 0, traceAt pos S x =
        vecTraceAt (toBddOp S₀) x + vecTraceAt (toBddOp Sp) x + vecTraceAt (toBddOp Sm) x
def TraceStarConj
    (tensor : VectorL2 L K → Matrices.ComplexMatrix2 → L2Field ι)
    (pos : Fin 3 × ι → InfiniteLattice.AmbientSpace) : Prop :=
  ∀ S : BddOp (L2Field ι),
    IsBddOpMap (fun f => pointwiseStar (S (pointwiseStar f))) ∧
    (∀ x : FullSpace.Vertex L 0 0,
      traceAt pos (toBddOp fun f => pointwiseStar (S (pointwiseStar f))) x =
        conj (traceAt pos S x)) ∧
    (IsSelfAdjointOp S → ∀ x : FullSpace.Vertex L 0 0,
      (traceAt pos S x).im = 0 ∧
        traceAt pos (toBddOp fun f => pointwiseStar (S (pointwiseStar f))) x =
          traceAt pos S x) ∧
    ∀ S₀ Sp Sm : VectorL2 L K → VectorL2 L K,
      IsSectorTriple tensor S S₀ Sp Sm → IsSelfAdjointOp S →
      (∀ f, S (pointwiseStar f) = pointwiseStar (S f)) →
      ∀ x : FullSpace.Vertex L 0 0,
        vecTraceAt (toBddOp Sm) x = vecTraceAt (toBddOp Sp) x
def AbelianLogDecomposition
    (tensor : VectorL2 L K → Matrices.ComplexMatrix2 → L2Field ι)
    (pos : Fin 3 × ι → InfiniteLattice.AmbientSpace) (z : ℝ)
    (T : BddOp (L2Field ι)) : Prop :=
  ShiftedHalfPositive z T ∧
  (∀ f : L2Field ι, IsNeutral (ofCoords f) →
    IsNeutral (ofCoords (opLog (addScalar T z) f))) ∧
  (∀ f : L2Field ι, IsPositivelyCharged (ofCoords f) →
    IsPositivelyCharged (ofCoords (opLog (addScalar T z) f))) ∧
  (∀ f : L2Field ι, IsNegativelyCharged (ofCoords f) →
    IsNegativelyCharged (ofCoords (opLog (addScalar T z) f))) ∧
  (∀ f : L2Field ι,
    opLog (addScalar T z) (pointwiseStar f) = pointwiseStar (opLog (addScalar T z) f)) ∧
  (∃! S : (VectorL2 L K → VectorL2 L K) × (VectorL2 L K → VectorL2 L K) ×
      (VectorL2 L K → VectorL2 L K),
    IsSectorTriple tensor T S.1 S.2.1 S.2.2) ∧
  ∀ S₀ Sp Sm : VectorL2 L K → VectorL2 L K, IsSectorTriple tensor T S₀ Sp Sm →
    (IsBddOpMap S₀ ∧ ShiftedHalfPositive z (toBddOp S₀)) ∧
    (IsBddOpMap Sp ∧ ShiftedHalfPositive z (toBddOp Sp)) ∧
    (IsBddOpMap Sm ∧ ShiftedHalfPositive z (toBddOp Sm)) ∧
    (∀ v, opLog (addScalar T z) (tensor v (Matrices.ComplexMatrix2.pauliFamily 2)) =
      tensor (opLog (addScalar (toBddOp S₀) z) v) (Matrices.ComplexMatrix2.pauliFamily 2)) ∧
    (∀ v, opLog (addScalar T z) (tensor v raisingPauli) =
      tensor (opLog (addScalar (toBddOp Sp) z) v) raisingPauli) ∧
    (∀ v, opLog (addScalar T z) (tensor v loweringPauli) =
      tensor (opLog (addScalar (toBddOp Sm) z) v) loweringPauli) ∧
    ∀ x : FullSpace.Vertex L 0 0,
      traceAt pos (opLog (addScalar T z)) x =
          vecTraceAt (opLog (addScalar (toBddOp S₀) z)) x +
            vecTraceAt (opLog (addScalar (toBddOp Sp) z)) x +
            vecTraceAt (opLog (addScalar (toBddOp Sm) z)) x ∧
        vecTraceAt (opLog (addScalar (toBddOp Sm) z)) x =
          vecTraceAt (opLog (addScalar (toBddOp Sp) z)) x
end Weights
section Symmetries
variable {L : ℕ}
def vertexAdd (a : Fin 4 → ℤ) (x : FullSpace.Vertex L 0 0) : FullSpace.Vertex L 0 0 :=
  FullSpace.vertexImage (PeriodicOperators.intShift a) x
def gaugeVertexFn (u : FullSpace.Vertex L 0 0 → Matrices.ComplexMatrix2)
    (f : L2Field (FullSpace.Vertex L 0 0)) : L2Field (FullSpace.Vertex L 0 0) :=
  Classical.epsilon fun g : L2Field (FullSpace.Vertex L 0 0) =>
    ofCoords g = FullSpace.adjointVertexFn u (ofCoords f)
def gaugeEdgeFn (u : FullSpace.Vertex L 0 0 → Matrices.ComplexMatrix2)
    (f : L2Field (PeriodicOperators.PosEdge L 0 0)) : L2Field (PeriodicOperators.PosEdge L 0 0) :=
  Classical.epsilon fun g : L2Field (PeriodicOperators.PosEdge L 0 0) =>
    ∀ e : PeriodicOperators.PosEdge L 0 0, ofCoords g e =
      FullSpace.adjointForm u (formOfPositiveValues (ofCoords f)) e.1
def lpShift {J : Type} (τ : J → J) (f : lp (fun _ : J => ℂ) 2) : lp (fun _ : J => ℂ) 2 :=
  Classical.epsilon fun g : lp (fun _ : J => ℂ) 2 => ∀ j : J, g (τ j) = f j
def vertexShift (a : Fin 4 → ℤ) (f : L2Field (FullSpace.Vertex L 0 0)) :
    L2Field (FullSpace.Vertex L 0 0) :=
  lpShift ((PeriodicOperators.colourVertices L 0 0).translate a) f
def edgeShift (a : Fin 4 → ℤ) (f : L2Field (PeriodicOperators.PosEdge L 0 0)) :
    L2Field (PeriodicOperators.PosEdge L 0 0) :=
  lpShift ((PeriodicOperators.colourEdges L 0 0).translate a) f
def PreservesTraceDensity {ι : Type} (pos : Fin 3 × ι → InfiniteLattice.AmbientSpace)
    (V : L2Field ι → L2Field ι) (a : Fin 4 → ℤ) : Prop :=
  IsUnitaryMap V ∧
  ∀ S : BddOp (L2Field ι),
    IsBddOpMap (fun f => V (S (Function.invFun V f))) ∧
    ∀ x : FullSpace.Vertex L 0 0,
      traceAt pos (toBddOp fun f => V (S (Function.invFun V f))) (vertexAdd a x) =
        traceAt pos S x
def DensityInvariance (z : ℝ)
    (Vv : L2Field (FullSpace.Vertex L 0 0) → L2Field (FullSpace.Vertex L 0 0))
    (Ve : L2Field (PeriodicOperators.PosEdge L 0 0) → L2Field (PeriodicOperators.PosEdge L 0 0))
    (a : Fin 4 → ℤ) : Prop :=
  PreservesTraceDensity (L := L) (vertexPos L) Vv a ∧
  PreservesTraceDensity (L := L) (edgePos L) Ve a ∧
  ∀ θ θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
    DensityDefined (L := L) z θ →
    (∀ f, Vv (laplacianOp θ f) = laplacianOp θ' (Vv f)) →
    (∀ f, Ve (massiveOp θ f) = massiveOp θ' (Ve f)) →
    DensityDefined (L := L) z θ' ∧
      ∀ x : FullSpace.Vertex L 0 0, densityAt z θ' (vertexAdd a x) = densityAt z θ x
end Symmetries
end YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
end
