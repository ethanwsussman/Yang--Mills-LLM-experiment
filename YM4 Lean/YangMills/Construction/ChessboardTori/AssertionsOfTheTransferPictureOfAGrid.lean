import YangMills.Construction.ChessboardTori.AssertionsOfTheTransferPicture
import YangMills.Construction.ChessboardTori.TransferPictureInOneDirection
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
namespace TransferSetup
variable {D : ChessboardSetup} (T : TransferSetup D)
def SliceTimesAndWalls : Prop :=
  (∀ x ∈ AddSubgroup.zmultiples D.mesh, ∃! i : ℤ, T.sliceTime i = x) ∧
  (∀ i : ℤ, T.sliceTime i ∈ AddSubgroup.zmultiples D.mesh) ∧
  ∀ k : ℤ,
    T.grid.wall T.axis k =
      {x | x T.axis = T.sliceTime (k * (T.ratioNat : ℤ)) + D.mesh / 2} ∧
    ∀ x ∈ D.gridPoints,
      (T.grid.origin T.axis + (k : ℝ) * T.grid.cellSide < x T.axis ∧
        x T.axis < T.grid.origin T.axis + ((k : ℝ) + 1) * T.grid.cellSide) ↔
      ∃ s : ℤ, 1 ≤ s ∧ s ≤ (T.ratioNat : ℤ) ∧ x T.axis = T.sliceTime (k * (T.ratioNat : ℤ) + s)
def SlabEdgesAndFields (m : SlabCount) : Prop :=
  Function.Injective (T.edgeOfSlices m) ∧
  range (T.edgeOfSlices m) = {e | e.IsForward} ∧
  IsHomeomorph (T.slabDecomposition m) ∧
  Measure.map (T.slabDecomposition m) (T.torusPeriods m).haarMeasure =
    (Measure.pi fun _ : ZMod (m : ℕ) => T.slabHaar).prod
      (Measure.pi fun _ : ZMod (m : ℕ) => T.siteHaar) ∧
  ∀ k : ZMod (m : ℕ), Function.Surjective (T.slabRestriction m k)
def FacesAndEnergies (m : SlabCount) : Prop :=
  Function.Bijective (T.faceOfSlices m) ∧
  ∀ U : (T.torusPeriods m).GaugeConfig,
    (∀ (i : T.SliceLabel m) (q : T.TransverseFace),
      (T.torusPeriods m).faceEnergy U (T.sliceFace m i q) =
        T.faceAction q (T.sliceField m U i)) ∧
    ∀ (i : T.SliceLabel m) (b : T.PositiveTransverseEdge),
      (((T.torusPeriods m).faceEnergy U (T.axialFace m i b) : ℝ) : ℂ) =
        1 - (1 / 2) * Matrices.ComplexMatrix2.fullTrace (T.axialHolonomy (T.sliceField m U i)
          (T.sliceField m U (i + 1)) (T.axialField m U i) b : Matrices.ComplexMatrix2)
def FacePartition (m : SlabCount) : Prop :=
  (∀ f : (T.torusPeriods m).Face,
    T.IsCrossingFace m f ∨ ∃! k : ZMod (m : ℕ), T.IsInSlab m k f) ∧
  (∀ f : (T.torusPeriods m).Face, T.IsCrossingFace m f ↔
    ∃ (k : ZMod (m : ℕ)) (b : T.PositiveTransverseEdge),
      f = T.axialFace m (T.slabSliceIndex m k 0) b) ∧
  ∀ (k : ZMod (m : ℕ)) (f : (T.torusPeriods m).Face), T.IsInSlab m k f ↔
    (∃ s : ℤ, 1 ≤ s ∧ s ≤ (T.ratioNat : ℤ) ∧ ∃ q : T.TransverseFace,
      f = T.sliceFace m (T.slabSliceIndex m k s) q) ∨
    (∃ s : ℤ, 1 ≤ s ∧ s ≤ (T.ratioNat : ℤ) - 1 ∧ ∃ b : T.PositiveTransverseEdge,
      f = T.axialFace m (T.slabSliceIndex m k s) b)
def BoltzmannFactorization (m : SlabCount) : Prop :=
  ∀ U : (T.torusPeriods m).GaugeConfig,
    (∀ (k : ZMod (m : ℕ)) (b : T.PositiveTransverseEdge),
      boltzmannFactor D (T.axialHolonomy (T.sliceField m U (T.slabSliceIndex m k 0))
          (T.sliceField m U (T.slabSliceIndex m k 1)) (T.axialField m U (T.slabSliceIndex m k 0)) b) =
        Complex.exp (-(D.β : ℂ) *
          ((T.torusPeriods m).faceEnergy U (T.axialFace m (T.slabSliceIndex m k 0) b) : ℂ))) ∧
    (∀ k : ZMod (m : ℕ),
      (∏ᶠ (f : (T.torusPeriods m).Face) (_ : T.IsInSlab m k f),
          Complex.exp (-(D.β : ℂ) * ((T.torusPeriods m).faceEnergy U f : ℂ))) =
        T.wilsonSlabBoltzmann (T.slabRestriction m k U)) ∧
    Complex.exp (-(D.β : ℂ) * ((T.torusPeriods m).wilsonAction U : ℂ)) =
      ∏ k : ZMod (m : ℕ), (T.wilsonSlabBoltzmann (T.slabRestriction m k U) *
        ∏ b : T.PositiveTransverseEdge,
          boltzmannFactor D (T.axialHolonomy (T.sliceField m U (T.slabSliceIndex m k 0))
            (T.sliceField m U (T.slabSliceIndex m k 1))
            (T.axialField m U (T.slabSliceIndex m k 0)) b))
def SlabBoltzmannBounds : Prop :=
  Continuous T.wilsonSlabBoltzmann ∧
  ∀ η : T.SlabConfig,
    (T.wilsonSlabBoltzmann η).im = 0 ∧ 0 < (T.wilsonSlabBoltzmann η).re ∧
      (T.wilsonSlabBoltzmann η).re ≤ 1
end TransferSetup
def GridTransferAssertions.Statement : Prop :=
  ∀ (D : ChessboardSetup) (T : TransferSetup D), T.grid.IsCoarse → ∀ m : SlabCount,
    T.SliceTimesAndWalls ∧
    T.SlabEdgesAndFields m ∧
    T.FacesAndEnergies m ∧
    T.FacePartition m ∧
    T.SlabReversalProperties ∧
    T.BoltzmannFactorization m ∧
    T.SlabBoltzmannBounds
end YangMills.Construction.ChessboardTori
end
