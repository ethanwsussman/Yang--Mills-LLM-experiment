import YangMills.Construction.PeriodicOperators.RulesOfTheCalculusOfJets
import YangMills.Construction.Towers.IteratedAveragesOfSmallRegularFields
import YangMills.Construction.Towers.OperatorFunctionsOfTheScaledPictureDefs
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions
open PeriodicOperators
open Tower.FullSpace.BackgroundJets (gaugeFieldOfForm)
open PeriodicOperators.StripSymbols (openStripInterior)
structure ScaledOperatorsAreLocal (L k : ℕ) : Prop where
  periodic : IsPeriodic (colourVertices L k 0) ∧ IsPeriodic (colourEdges L k 0) ∧
    IsPeriodic (colourFaces L k 0) ∧ IsPeriodic (colourVertices L k k) ∧
    IsPeriodic (colourEdges L k k)
  gaugeField_mem : ∀ a, gaugeFieldOfForm L k a ∈
    Tower.FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup
  D_local : IsLocalEntire L k (colourVertices L k 0) (colourEdges L k 0)
    fun a => (Tower.FullSpace.rescaledOperators L k (gaugeFieldOfForm L k a)).D
  holonomyDefect_local : IsLocalEntire L k (colourEdges L k 0) (colourFaces L k 0)
    fun a => Tower.FullSpace.holonomyDefectKernel L k (gaugeFieldOfForm L k a)
  halfFaceTrace_local :
    IsLocalEntire L k (colourFaces L k 0) (colourFaces L k 0)
      fun a => Tower.FullSpace.halfFaceTraceKernel L k (gaugeFieldOfForm L k a)
  curvature_local : IsLocalEntire L k (colourEdges L k 0) (colourEdges L k 0)
    fun a => Tower.FullSpace.curvatureKernel (gaugeFieldOfForm L k a)
  H_local : IsLocalEntire L k (colourEdges L k 0) (colourEdges L k 0)
    fun a => (Tower.FullSpace.rescaledOperators L k (gaugeFieldOfForm L k a)).H
  K_local : IsLocalEntire L k (colourEdges L k 0) (colourEdges L k 0)
    fun a => (Tower.FullSpace.rescaledOperators L k (gaugeFieldOfForm L k a)).K
  Delta_local : IsLocalEntire L k (colourVertices L k 0) (colourVertices L k 0)
    fun a => (Tower.FullSpace.rescaledOperators L k (gaugeFieldOfForm L k a)).Delta
  Q_local : ∀ r c : ℝ, Tower.IteratedSmallFieldMeans.AdmissibleConstants L r c →
    IsLocalBelowNorm L k (colourEdges L k 0) (colourEdges L k k)
      (fun a => (Tower.FullSpace.rescaledOperators L k (gaugeFieldOfForm L k a)).Q)
      (Tower.finestMesh L k * r)
  R_local : ∀ r c : ℝ, Tower.IteratedSmallFieldMeans.AdmissibleConstants L r c →
    IsLocalBelowNorm L k (colourVertices L k 0) (colourVertices L k k)
      (fun a => (Tower.FullSpace.rescaledOperators L k (gaugeFieldOfForm L k a)).R)
      (Tower.finestMesh L k * r)
structure JetHolomorphyClosure (δ : ℝ) (P : Set (Coordinates.ComplexCoordinates 4))
    (I I' I'' : PeriodicData) : Prop where
  add : ∀ T S : Coordinates.ComplexCoordinates 4 → JetQuad I I', JetFamilyHolomorphic δ P T →
    JetFamilyHolomorphic δ P S → JetFamilyHolomorphic δ P fun p => (T p).add (S p)
  mul : ∀ (T : Coordinates.ComplexCoordinates 4 → JetQuad I I')
      (S : Coordinates.ComplexCoordinates 4 → JetQuad I'' I),
    JetFamilyHolomorphic δ P T → JetFamilyHolomorphic δ P S →
      JetFamilyHolomorphic δ P fun p => JetQuad.mul p (T p) (S p)
  transpose : ∀ T : Coordinates.ComplexCoordinates 4 → JetQuad I I', JetFamilyHolomorphic δ P T →
    JetFamilyHolomorphic δ P fun p => JetQuad.transposeAt p (T p)
  inv : ∀ T : Coordinates.ComplexCoordinates 4 → JetQuad I I, JetFamilyHolomorphic δ P T →
    (∀ p ∈ P, JetQuad.IsInvertibleJet δ p (T p)) →
      JetFamilyHolomorphic δ P fun p => JetQuad.invJet p (T p)
  traceNumber_holomorphic : ∀ T : Coordinates.ComplexCoordinates 4 → JetQuad I I,
    JetFamilyHolomorphic δ P T →
    (⨆ p ∈ P, JetQuad.jetNorm δ p (T p)) < ⊤ →
      Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ => JetQuad.traceNumber (T p)
def ScaledOperatorFunctionsClaim : Prop :=
  (∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ScaledOperatorsAreLocal L k ∧
      ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
        JetComponentsHolomorphic L k I I') ∧
  ∀ δ : ℝ, 0 < δ → ∀ P : Set (Coordinates.ComplexCoordinates 4), IsOpen P → P ⊆ openStripInterior δ →
    ∀ I I' I'' : PeriodicData, IsPeriodic I → IsPeriodic I' → IsPeriodic I'' →
      JetHolomorphyClosure δ P I I' I''
end YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions
end
