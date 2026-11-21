import YangMills.Construction.ChessboardTori.TransferPicture
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
namespace TransferSetup
variable {D : ChessboardSetup} (T : TransferSetup D)
instance isProbabilityMeasure_slabHaar : IsProbabilityMeasure T.slabHaar := by
  unfold slabHaar
  infer_instance
def sliceTimeClass (m : SlabCount) (i : T.SliceLabel m) :
    AddCircle (((m : ℕ) : ℝ) * T.grid.cellSide) :=
  ((T.sliceTime (i.cast : ℤ) : ℝ) : AddCircle (((m : ℕ) : ℝ) * T.grid.cellSide))
def meshMultiples (m : SlabCount) :
    AddSubgroup (AddCircle (((m : ℕ) : ℝ) * T.grid.cellSide)) :=
  AddSubgroup.zmultiples ((D.mesh : ℝ) : AddCircle (((m : ℕ) : ℝ) * T.grid.cellSide))
def SliceTimesAndSlabs (m : SlabCount) : Prop :=
  range T.sliceTime = (AddSubgroup.zmultiples D.mesh : Set ℝ) ∧
  (∀ i : ℤ, T.sliceTime (i + ((m : ℕ) : ℤ) * (T.ratioNat : ℤ)) =
    T.sliceTime i + ((m : ℕ) : ℝ) * T.grid.cellSide) ∧
  BijOn (T.sliceTimeClass m) univ
    (T.meshMultiples m : Set (AddCircle (((m : ℕ) : ℝ) * T.grid.cellSide))) ∧
  (∀ k : ℤ,
    T.grid.wall T.axis k =
      {x | x T.axis = T.sliceTime (k * (T.ratioNat : ℤ)) + D.mesh / 2} ∧
    T.sliceTime (k * (T.ratioNat : ℤ)) < T.sliceTime (k * (T.ratioNat : ℤ)) + D.mesh / 2 ∧
    T.sliceTime (k * (T.ratioNat : ℤ)) + D.mesh / 2 < T.sliceTime (k * (T.ratioNat : ℤ) + 1)) ∧
  ∀ i : T.SliceLabel m, ∃! k : ZMod (m : ℕ), i ∈ T.slabSet m k
def edgeOfSlices (m : SlabCount) :
    (T.SliceLabel m × T.PositiveTransverseEdge) ⊕ (T.SliceLabel m × T.TransverseSite) →
      (T.torusPeriods m).DirectedEdge
  | .inl (i, b) => T.sliceEdge m i b
  | .inr (i, y) => T.axialEdge m i y
def sliceAndAxialFields (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig) :
    T.SliceLabel m → T.EdgeField × T.SiteField :=
  fun i => (T.sliceField m U i, T.axialField m U i)
def EdgesAndFields (m : SlabCount) : Prop :=
  Function.Injective (T.edgeOfSlices m) ∧
  range (T.edgeOfSlices m) = {l | l.IsForward} ∧
  IsHomeomorph (T.sliceAndAxialFields m) ∧
  Measure.map (T.sliceAndAxialFields m) (T.torusPeriods m).haarMeasure =
    Measure.pi fun _ : T.SliceLabel m => T.edgeHaar.prod T.siteHaar
def faceOfSlices (m : SlabCount) :
    (T.SliceLabel m × T.TransverseFace) ⊕ (T.SliceLabel m × T.PositiveTransverseEdge) →
      (T.torusPeriods m).Face
  | .inl (i, q) => T.sliceFace m i q
  | .inr (i, b) => T.axialFace m i b
def FacesOfSlices (m : SlabCount) : Prop :=
  Function.Bijective (T.faceOfSlices m) ∧
  (∀ (i : T.SliceLabel m) (q : T.TransverseFace),
    (∀ U : (T.torusPeriods m).GaugeConfig,
      (T.torusPeriods m).faceEnergy U (T.sliceFace m i q) =
        T.faceAction q (T.sliceField m U i)) ∧
    (T.torusPeriods m).faceCenter (T.sliceFace m i q) =
      T.torusPoint m (T.sliceTime (i.cast : ℤ)) (T.faceCentre q)) ∧
  ∀ (i : T.SliceLabel m) (b : T.PositiveTransverseEdge),
    (T.torusPeriods m).faceCenter (T.axialFace m i b) =
      T.torusPoint m (T.sliceTime (i.cast : ℤ) + D.mesh / 2) (T.edgeMidpoint b) ∧
    ∀ U : (T.torusPeriods m).GaugeConfig,
      (((T.torusPeriods m).faceEnergy U (T.axialFace m i b) : ℝ) : ℂ) =
        1 - (1 / 2) * Matrices.ComplexMatrix2.fullTrace (T.axialHolonomy (T.sliceField m U i)
          (T.sliceField m U (i + 1)) (T.axialField m U i) b : Matrices.ComplexMatrix2)
def CrossingFaces (m : SlabCount) : Prop :=
  (∀ p : (T.torusPeriods m).Face,
    (∃! k : ZMod (m : ℕ), T.IsInSlab m k p) ∨ T.IsCrossingFace m p) ∧
  (∀ p : (T.torusPeriods m).Face, T.IsCrossingFace m p ↔
    ∃ (k : ZMod (m : ℕ)) (b : T.PositiveTransverseEdge),
      p = T.axialFace m (T.slabSliceIndex m k 0) b) ∧
  ∀ p' : D.Plaquette,
    ((∃ b : D.Link, D.IsEdgeOf b p' ∧ ∃ k : ℤ, T.grid.Straddles b T.axis k) ↔
      T.IsCrossingFace m ((T.torusPeriods m).projFace p')) ∧
    ∀ b : D.Link, D.IsEdgeOf b p' → ∀ k : ℤ, T.grid.Straddles b T.axis k →
      p'.center ∈ T.grid.wall T.axis k
def SlabReversalProperties : Prop :=
  IsHomeomorph T.slabReverse ∧ Function.Involutive T.slabReverse ∧
  MeasurePreserving T.slabReverse T.slabHaar T.slabHaar ∧
  ∀ Φ Φ' : T.SlabConfig → ℂ, T.IsBoundedMeasurable Φ → T.IsBoundedMeasurable Φ' →
    T.IsBoundedMeasurable (T.reflectConj Φ) ∧ T.reflectConj (T.reflectConj Φ) = Φ ∧
    T.reflectConj (Φ * Φ') = T.reflectConj Φ * T.reflectConj Φ' ∧
    ⨆ η, ‖T.reflectConj Φ η‖ = ⨆ η, ‖Φ η‖
def slabDecomposition (m : SlabCount) (U : (T.torusPeriods m).GaugeConfig) :
    (ZMod (m : ℕ) → T.SlabConfig) × (ZMod (m : ℕ) → T.SiteField) :=
  (fun k => T.slabRestriction m k U, fun k => T.axialField m U (T.slabSliceIndex m k 0))
def SlabDecompositionProperties (m : SlabCount) : Prop :=
  IsHomeomorph (T.slabDecomposition m) ∧
  Measure.map (T.slabDecomposition m) (T.torusPeriods m).haarMeasure =
    (Measure.pi fun _ : ZMod (m : ℕ) => T.slabHaar).prod
      (Measure.pi fun _ : ZMod (m : ℕ) => T.siteHaar) ∧
  ∀ (U : (T.torusPeriods m).GaugeConfig) (k : ZMod (m : ℕ)) (b : T.PositiveTransverseEdge),
    boltzmannFactor D (T.axialHolonomy (T.sliceField m U (T.slabSliceIndex m k 0))
        (T.sliceField m U (T.slabSliceIndex m k 1)) (T.axialField m U (T.slabSliceIndex m k 0)) b) =
      Complex.exp (-(D.β : ℂ) *
        ((T.torusPeriods m).faceEnergy U (T.axialFace m (T.slabSliceIndex m k 0) b) : ℂ))
def FacesInSlab (m : SlabCount) : Prop :=
  ∀ k : ZMod (m : ℕ),
    (∀ p : (T.torusPeriods m).Face, T.IsInSlab m k p ↔
      (∃ j : ℤ, 1 ≤ j ∧ j ≤ (T.ratioNat : ℤ) ∧ ∃ q : T.TransverseFace,
        p = T.sliceFace m (T.slabSliceIndex m k j) q) ∨
      (∃ j : ℤ, 1 ≤ j ∧ j ≤ (T.ratioNat : ℤ) - 1 ∧ ∃ b : T.PositiveTransverseEdge,
        p = T.axialFace m (T.slabSliceIndex m k j) b)) ∧
    ∀ U : (T.torusPeriods m).GaugeConfig,
      (∀ (j : Fin T.ratioNat) (q : T.TransverseFace),
        (T.torusPeriods m).faceEnergy U
            (T.sliceFace m (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1)) q) =
          T.slabFaceAction j q (T.slabRestriction m k U)) ∧
      ∀ (j : Fin (T.ratioNat - 1)) (b : T.PositiveTransverseEdge),
        (((T.torusPeriods m).faceEnergy U
            (T.axialFace m (T.slabSliceIndex m k (((j : ℕ) : ℤ) + 1)) b) : ℝ) : ℂ) =
          T.slabAxialAction j b (T.slabRestriction m k U)
def SlabBoltzmannWeights (m : SlabCount) : Prop :=
  ∀ w : (T.torusPeriods m).Face → ℂ, (∃ C : ℝ, ∀ p, ‖w p‖ ≤ C) →
    (∀ k : ZMod (m : ℕ),
      Continuous (T.slabBoltzmann m w k) ∧ (∃ C : ℝ, ∀ η, ‖T.slabBoltzmann m w k η‖ ≤ C) ∧
      ∀ U : (T.torusPeriods m).GaugeConfig,
        T.slabBoltzmann m w k (T.slabRestriction m k U) =
          ∏ᶠ (p : (T.torusPeriods m).Face) (_ : T.IsInSlab m k p),
            Complex.exp ((w p - (D.β : ℂ)) * ((T.torusPeriods m).faceEnergy U p : ℂ))) ∧
    ((∀ p, T.IsCrossingFace m p → w p = 0) →
      ∫ U, Complex.exp (∑ᶠ p : (T.torusPeriods m).Face,
          (w p - (D.β : ℂ)) * ((T.torusPeriods m).faceEnergy U p : ℂ))
        ∂(T.torusPeriods m).haarMeasure =
      T.slabProductIntegral m fun k => T.slabBoltzmann m w k)
end TransferSetup
def GaugeGroupTraceFacts : Prop :=
  ∀ u : Conventions.StandingParameters.gaugeGroup,
    (Matrices.ComplexMatrix2.fullTrace (u : Matrices.ComplexMatrix2)).im = 0 ∧
    ‖Matrices.ComplexMatrix2.fullTrace (u : Matrices.ComplexMatrix2)‖ ≤ 2 ∧
    Matrices.ComplexMatrix2.fullTrace
        ((u⁻¹ : Conventions.StandingParameters.gaugeGroup) : Matrices.ComplexMatrix2) =
      Matrices.ComplexMatrix2.fullTrace (u : Matrices.ComplexMatrix2)
def TransferAssertions.Statement : Prop :=
  ∀ (D : ChessboardSetup) (T : TransferSetup D) (m : SlabCount),
    T.SliceTimesAndSlabs m ∧
    T.EdgesAndFields m ∧
    GaugeGroupTraceFacts ∧ T.FacesOfSlices m ∧
    T.CrossingFaces m ∧
    T.SlabReversalProperties ∧
    T.SlabDecompositionProperties m ∧
    T.FacesInSlab m ∧ T.SlabBoltzmannWeights m
end YangMills.Construction.ChessboardTori
end
