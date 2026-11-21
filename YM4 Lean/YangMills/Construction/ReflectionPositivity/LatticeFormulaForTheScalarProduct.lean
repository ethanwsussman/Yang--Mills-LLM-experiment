import YangMills.Construction.Conventions.ContinuumLimitsOfLatticeApproximationsDefs
import YangMills.Construction.InfiniteLattice.LinkAndSitePicturesWithACoordinateAsTime
import YangMills.Construction.Lattice.AdicGridPoints
import YangMills.Construction.ReflectionPositivity.BoundedLatticeApproximationsAndTheirC1Constants
import YangMills.Construction.ReflectionPositivity.FormOfAFunctionalOnSeparatedTuples
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
open scoped ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LatticeScalarProduct
open YangMills.Construction.ContractionUnitary (zpowOp)
open YangMills.Construction.ReflectionPositivity.AxisMirror (MirrorData)
open YangMills.Construction.ReflectionPositivity.TupleForm (PositiveSpan reflectionForm reflectConj)
open YangMills.Construction.InfiniteLattice (GaugeField AmbientSpace refinedSpacing latticeSubgroup)
open YangMills.Construction.LimitConventions (ApproxTriple)
open YangMills.Construction.ReflectionPositivity.ApproximatingSequences (LatticeApproximation)
open YangMills.Construction.LatticeConventions (Spacing conjFun timeAxis)
open YangMills.Construction.LatticeConventions.SiteFrame (TimeSiteHilbertSpace upperSpace timeClass
  timeReflection spatialShift timeTransferOperator)
open YangMills.Construction.OneLoopNotation (BddOp)
open YangMills.Construction.SeparatedTuples (FormalSpan TupleFunctional SepTuple push pushSpan formalMul)
section SingleLattice
variable (a : Spacing)
def conjReflMulShift (F G : GaugeField (a : ℝ) → ℂ) (v : AmbientSpace) :
    GaugeField (a : ℝ) → ℂ :=
  open Classical in
  if hv : v ∈ latticeSubgroup (a : ℝ) then
    fun U => conjFun ((timeReflection a).actOn F) U *
      (YangMills.Construction.InfiniteLattice.shift ⟨v, hv⟩).actOn G U
  else 0
variable (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν]
def siteClassOf (F : GaugeField (a : ℝ) → ℂ) : TimeSiteHilbertSpace a ν :=
  open Classical in
  if h : F ∈ upperSpace a timeAxis then timeClass a ν ⟨F, h⟩ else 0
def transferShiftOp (m : ℕ) (y : YangMills.Construction.LatticeConventions.SpatialDirection → ℤ) :
    BddOp (TimeSiteHilbertSpace a ν) :=
  timeTransferOperator a ν ^ m *
    (zpowOp (spatialShift a ν 0) (y 0) * zpowOp (spatialShift a ν 1) (y 1) *
      zpowOp (spatialShift a ν 2) (y 2))
end SingleLattice
def intDiv (x a : ℝ) : ℤ := ⌊x / a⌋
abbrev meshOf (D : MirrorData) (K : ℕ+) : Spacing :=
  ⟨refinedSpacing D.L K, by
    have hL : (0 : ℝ) < (D.L : ℝ) := by
      have h := D.isAdmissible.2
      exact_mod_cast (by omega : 0 < D.L)
    unfold refinedSpacing YangMills.Construction.PeriodicLattice.meshSize
    exact zpow_pos hL _⟩
section Approximating
variable (D : MirrorData) (T : ApproxTriple D.L)
abbrev meshAt (j : ℕ+) : Spacing := meshOf D (T.cutoff j)
def latticeExpectation (Z W : FormalSpan) (v : AmbientSpace) (j : ℕ+) : ℂ :=
  ∫ U, conjReflMulShift (meshAt D T j) (T.spanRep j Z)
    (T.spanRep j W) v U ∂T.state j
def transferMatrixElement (Z W : FormalSpan) (v : AmbientSpace) (j : ℕ+) : ℂ :=
  letI : IsProbabilityMeasure (T.state j) := T.isProbabilityMeasure_state j
  ⟪siteClassOf (meshAt D T j) (T.state j) (T.spanRep j Z),
    transferShiftOp (meshAt D T j) (T.state j)
        (intDiv (YangMills.Construction.TimeAxis.timeComponent v) (refinedSpacing D.L (T.cutoff j))).toNat
        (fun i => intDiv (v i.castSucc) (refinedSpacing D.L (T.cutoff j)))
      (siteClassOf (meshAt D T j) (T.state j) (T.spanRep j W))⟫_ℂ
def classInner (Z W : FormalSpan) (j : ℕ+) : ℂ :=
  letI : IsProbabilityMeasure (T.state j) := T.isProbabilityMeasure_state j
  ⟪siteClassOf (meshAt D T j) (T.state j) (T.spanRep j Z),
    siteClassOf (meshAt D T j) (T.state j) (T.spanRep j W)⟫_ℂ
end Approximating
def SupportedAbove (δ : ℝ) (Z : FormalSpan) : Prop :=
  ∀ X ∈ Z.support, ∀ f ∈ X.1, tsupport f ⊆ {x | 2 * δ ≤ YangMills.Construction.TimeAxis.timeComponent x}
def reflMulShift (Z : PositiveSpan) (W : FormalSpan) (v : AmbientSpace) : FormalSpan :=
  formalMul (reflectConj Z) (pushSpan (YangMills.Construction.SeparatedTuples.translate v) W)
def ReflMulShiftComposable (Z W : FormalSpan) (v : AmbientSpace) : Prop :=
  ∀ X ∈ Z.support, ∀ Y ∈ W.support, SepTuple.Composable (push YangMills.Construction.TimeAxis.timeReflection X)
    (push (YangMills.Construction.SeparatedTuples.translate v) Y)
def LatticeRepresentatives (D : MirrorData) (T : ApproxTriple D.L)
    (Z W : PositiveSpan) (δ : ℝ) : Prop :=
  ∀ j, refinedSpacing D.L (T.cutoff j) ≤ δ →
    T.spanRep j Z.1 ∈ upperSpace (meshAt D T j) timeAxis ∧
    T.spanRep j W.1 ∈ upperSpace (meshAt D T j) timeAxis ∧
    ∀ v ∈ latticeSubgroup (refinedSpacing D.L (T.cutoff j)),
      0 ≤ YangMills.Construction.TimeAxis.timeComponent v →
      ReflMulShiftComposable Z.1 W.1 v ∧
      conjReflMulShift (meshAt D T j) (T.spanRep j Z.1)
          (T.spanRep j W.1) v =
        T.spanRep j (reflMulShift Z W.1 v)
def AdicLimitFormula (D : MirrorData) (T : ApproxTriple D.L) (σ : TupleFunctional)
    (Z W : PositiveSpan) : Prop :=
  ∀ v : AmbientSpace, (∀ μ, v μ ∈ YangMills.Construction.PeriodicLattice.adicGridPoints D.L) →
    0 ≤ YangMills.Construction.TimeAxis.timeComponent v →
    (∀ᶠ j in atTop, ∀ μ, ∃ m : ℤ, v μ / refinedSpacing D.L (T.cutoff j) = m) ∧
    Tendsto (latticeExpectation D T Z.1 W.1 v) atTop (𝓝 (σ.spanExtension (reflMulShift Z W.1 v))) ∧
    Tendsto (transferMatrixElement D T Z.1 W.1 v) atTop (𝓝 (σ.spanExtension (reflMulShift Z W.1 v)))
def ZeroShiftFormula (D : MirrorData) (T : ApproxTriple D.L) (σ : TupleFunctional)
    (Z W : PositiveSpan) : Prop :=
  reflectionForm σ Z W = σ.spanExtension (formalMul (reflectConj Z) W.1) ∧
  Tendsto (classInner D T Z.1 W.1) atTop
    (𝓝 (σ.spanExtension (formalMul (reflectConj Z) W.1))) ∧
  0 ≤ σ.spanExtension (formalMul (reflectConj Z) Z.1)
def LatticeFormula : Prop :=
  ∀ (D : MirrorData) (T : ApproxTriple D.L) (σ : TupleFunctional),
    T.IsReflPos → LatticeApproximation.IsBoundedForSomeM D T → T.ConvergesTo σ →
    ∀ Z W : PositiveSpan,
      (∃ δ : ℝ, 0 < δ ∧ SupportedAbove δ Z.1 ∧ SupportedAbove δ W.1) ∧
      ∀ δ : ℝ, 0 < δ → SupportedAbove δ Z.1 → SupportedAbove δ W.1 →
        LatticeRepresentatives D T Z W δ ∧ AdicLimitFormula D T σ Z W ∧
          ZeroShiftFormula D T σ Z W
end YangMills.Construction.ReflectionPositivity.LatticeScalarProduct
end
