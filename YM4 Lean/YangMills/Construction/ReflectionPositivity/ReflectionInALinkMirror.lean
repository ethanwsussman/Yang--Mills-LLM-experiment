import YangMills.Construction.Lattice.ConsistencyOfLiftsAndAveragesSetting
import YangMills.Construction.Lattice.ParallelBondsAndSidesOfAPlaquette
import YangMills.Construction.ReflectionPositivity.HeightOverALinkPosition
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkReflection
variable {D : MirrorData}
abbrev gaugeFieldSpace (D : MirrorData) : Set D.BondField :=
  PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)
def IsBoundedMeasurableOnGaugeFields {E : Type*} [Norm E] [MeasurableSpace E]
    (F : D.BondField → E) : Prop :=
  TestFunctions.IsBoundedFun (fun V : gaugeFieldSpace D => F V) ∧
    Measurable[borel (gaugeFieldSpace D)] fun V : gaugeFieldSpace D => F V
def ActsOnTorus (C : LinkLevel D) : Prop :=
  Function.Involutive C.refl ∧ D.IsDistPreserving C.refl ∧
    C.refl '' (D.latticeSubgroup : Set D.Torus) = D.latticeSubgroup ∧
    (∀ y, C.centeredRep y ≠ C.pos - D.side / 2 →
      C.centeredRep (C.refl y) = 2 * C.pos - C.centeredRep y) ∧
    C.refl '' C.openSlab .pos = C.openSlab .neg ∧ C.refl '' C.openSlab .neg = C.openSlab .pos
def ActsOnBonds (C : LinkLevel D) (s : D.Symmetry) : Prop :=
  (∀ b : D.DirectedBond, ((MirrorData.Symmetry.bondImage s b).source : D.Torus) = C.refl b.source ∧
    ((MirrorData.Symmetry.bondImage s b).target : D.Torus) = C.refl b.target) ∧
  Function.Involutive (MirrorData.Symmetry.bondImage s) ∧
  (∀ b : D.DirectedBond, MirrorData.Symmetry.bondImage s b.opposite =
    (MirrorData.Symmetry.bondImage s b).opposite) ∧
  ∀ (b : D.DirectedBond) (ν : Fin 4), b.IsPositivelyOriented → b.IsParallelToAxis ν →
    (MirrorData.Symmetry.bondImage s b).IsParallelToAxis ν ∧
    (ν ≠ D.dir → (MirrorData.Symmetry.bondImage s b).IsPositivelyOriented) ∧
    (ν = D.dir → (MirrorData.Symmetry.bondImage s b).IsNegativelyOriented)
def ActsOnGaugeFields (s : D.Symmetry) : Prop :=
  (∀ V ∈ gaugeFieldSpace D, MirrorData.Symmetry.pullback s V ∈ gaugeFieldSpace D ∧
    (∀ b, MirrorData.Symmetry.pullback s V b = V (MirrorData.Symmetry.bondImage s b)) ∧
    MirrorData.Symmetry.pullback s (MirrorData.Symmetry.pullback s V) = V) ∧
  ∃ h : gaugeFieldSpace D ≃ₜ gaugeFieldSpace D,
    ∀ V : gaugeFieldSpace D, (h V : D.BondField) = MirrorData.Symmetry.pullback s V
def ActsOnPlaquettes (C : LinkLevel D) (s : D.Symmetry) : Prop :=
  (∀ p : D.Face,
    MirrorData.Symmetry.IsFaceImage s p (MirrorData.Symmetry.faceImage s p)) ∧
  Function.Involutive (MirrorData.Symmetry.faceImage s) ∧
  (∀ p : D.Face,
    (MirrorData.Symmetry.faceImage s p).barycenter = C.refl p.barycenter) ∧
  (∀ V ∈ gaugeFieldSpace D, ∀ p : D.Face,
    PeriodicLattice.plaquetteCost (MirrorData.Symmetry.pullback s V) p =
      PeriodicLattice.plaquetteCost V (MirrorData.Symmetry.faceImage s p)) ∧
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : D.Torus → E),
    TestFunctions.IsBoundedFun f → ∀ V ∈ gaugeFieldSpace D,
      PeriodicLattice.smearedObservable f (MirrorData.Symmetry.pullback s V) =
        PeriodicLattice.smearedObservable (f ∘ C.refl) V
def PreservesExpectations (s : D.Symmetry) : Prop :=
  (∀ F : D.BondField → ℝ, IsBoundedMeasurableOnGaugeFields F →
    PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling (F ∘ MirrorData.Symmetry.pullback s) =
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling F) ∧
  ∀ F : D.BondField → ℂ, IsBoundedMeasurableOnGaugeFields F →
    PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling (F ∘ MirrorData.Symmetry.pullback s) =
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling F
def LinkReflectionProperties : Prop :=
  ∀ (D : MirrorData) (C : LinkLevel D), ActsOnTorus C ∧
    ∃ s : D.Symmetry, s.toFun = C.refl ∧ ActsOnBonds C s ∧ ActsOnGaugeFields s ∧
      ActsOnPlaquettes C s ∧ PreservesExpectations s
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkReflection
end
