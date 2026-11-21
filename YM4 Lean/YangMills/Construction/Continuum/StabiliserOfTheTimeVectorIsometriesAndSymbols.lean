import YangMills.Construction.Continuum.SymbolsOfFourSpaceWithATimeAxis
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusTransport TorusTransport.TupleVectors
namespace TimeAxisSymbols
def spatialPart (w : timeAxisStabilizer) (a : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => w.1.1 (spaceTimePoint a 0) i.castSucc
namespace StabilizerAction
def RestrictsTo (w : timeAxisStabilizer) (φ : (Fin 3 → ℝ) → Fin 3 → ℝ) : Prop :=
  ∀ a, w.1.1 (spaceTimePoint a 0) = spaceTimePoint (φ a) 0
def StabilizerSubgroup : Prop :=
  ∃ H : Subgroup hyperoctahedral,
    (H : Set hyperoctahedral) = {w | w.1 timeAxisVec = timeAxisVec} ∧
    H = timeAxisStabilizer
def PreservesTimeCoord : Prop :=
  ∀ (w : timeAxisStabilizer) (x : Fin 4 → ℝ), w.1.1 x 3 = x 3
def SpatialPartUnique : Prop :=
  ∀ w : timeAxisStabilizer,
    (∃! φ : (Fin 3 → ℝ) → Fin 3 → ℝ, RestrictsTo w φ) ∧
      RestrictsTo w (spatialPart w)
def SpatialPartOrthogonal : Prop :=
  ∀ w : timeAxisStabilizer,
    IsLinearMap ℝ (spatialPart w) ∧
      ∃ S ∈ Matrix.orthogonalGroup (Fin 3) ℝ, spatialPart w = Matrix.mulVec S
def ActionOnPoints : Prop :=
  ∀ (w : timeAxisStabilizer) (a : Fin 3 → ℝ) (t : ℝ),
    w.1.1 (spaceTimePoint a t) = spaceTimePoint (spatialPart w a) t
def SpatialPartMul : Prop :=
  ∀ (w w' : timeAxisStabilizer) (a : Fin 3 → ℝ),
    spatialPart (w * w') a = spatialPart w (spatialPart w' a)
def SpatialPartAdjoint : Prop :=
  ∀ (w : timeAxisStabilizer) (a p : Fin 3 → ℝ),
    dotProduct (spatialPart w a) p = dotProduct a (spatialPart w⁻¹ p)
def CommRelations : Prop :=
  ∀ (w : timeAxisStabilizer) (a : Fin 3 → ℝ) (t : ℝ),
    timeReflect ∘ ⇑w.1.1 = ⇑w.1.1 ∘ timeReflect ∧
    timeReflect ∘ ⇑(translationEquiv (spaceTimePoint a 0)) =
      ⇑(translationEquiv (spaceTimePoint a 0)) ∘ timeReflect ∧
    timeReflect ∘ ⇑(translationEquiv (t • timeAxisVec)) =
      ⇑(translationEquiv ((-t) • timeAxisVec)) ∘ timeReflect ∧
    ⇑w.1.1 ∘ ⇑(translationEquiv (spaceTimePoint a 0)) =
      ⇑(translationEquiv (spaceTimePoint (spatialPart w a) 0)) ∘ ⇑w.1.1 ∧
    ⇑w.1.1 ∘ ⇑(translationEquiv (t • timeAxisVec)) =
      ⇑(translationEquiv (t • timeAxisVec)) ∘ ⇑w.1.1
def PreserveUpperHalf : Prop :=
  ∀ (w : timeAxisStabilizer) (a : Fin 3 → ℝ) (t : ℝ), 0 ≤ t →
    Set.MapsTo (translationEquiv (t • timeAxisVec)) posTimeHalf posTimeHalf ∧
    Set.MapsTo (translationEquiv (spaceTimePoint a 0)) posTimeHalf posTimeHalf ∧
    Set.MapsTo w.1.1 posTimeHalf posTimeHalf
def ReflectSwapsHalves : Prop :=
  timeReflect '' posTimeHalf = {x | x 3 < 0} ∧ timeReflect '' {x | x 3 < 0} = posTimeHalf
def MotionsOnSymbols (D : TransportData) : Prop :=
  ∀ (s s' : (Fin 4 → ℝ) → Fin 4 → ℝ) (hs : IsEuclideanMotion s)
    (hs' : IsEuclideanMotion s') (X Y : SpaceTimeSymbol D),
    actAny hs X.1 ∈ spaceTimeSymbols D ∧
    (∀ i : Fin X.len, (motionSymbol hs X).supp i = s '' X.supp i) ∧
    (∃ hss : IsEuclideanMotion (s ∘ s'),
      motionSymbol hs (motionSymbol hs' X) = motionSymbol hss X) ∧
    ∀ hd : AppendDefined D X.1 Y.1,
      ∃ hd' : AppendDefined D (motionSymbol hs X).1 (motionSymbol hs Y).1,
        sepAppend (motionSymbol hs X) (motionSymbol hs Y) hd' =
          motionSymbol hs (sepAppend X Y hd)
def Statement : Prop :=
  (StabilizerSubgroup ∧ PreservesTimeCoord ∧ SpatialPartUnique ∧
    SpatialPartOrthogonal ∧ ActionOnPoints ∧ SpatialPartMul ∧ SpatialPartAdjoint) ∧
  (CommRelations ∧ PreserveUpperHalf ∧ ReflectSwapsHalves) ∧
  ∀ D : TransportData, MotionsOnSymbols D
end StabilizerAction
end TimeAxisSymbols
end YangMills.Construction
end
