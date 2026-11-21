import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance
open MirrorData.Symmetry
variable {D : MirrorData}
abbrev gaugeFieldSet (D : MirrorData) : Set D.BondField :=
  PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)
def IsAffine (s : D.Symmetry) : Prop :=
  ∃ R : PeriodicLattice.SignedFrame, ∃ v ∈ PeriodicLattice.meshVectors D.L ((D.K : ℕ) : ℤ),
    ∀ x : Fin 4 → ℝ, s.toFun (D.proj x) = D.proj (R.actOnVector x + v)
def AffineMapsExhaustSymmetries (D : MirrorData) : Prop :=
  (∀ R : PeriodicLattice.SignedFrame, ∀ v ∈ PeriodicLattice.meshVectors D.L ((D.K : ℕ) : ℤ),
    ∃ s : D.Symmetry, ∀ x : Fin 4 → ℝ,
      s.toFun (D.proj x) = D.proj (R.actOnVector x + v)) ∧
  range (fun s : D.Symmetry => s.toFun) =
    (fun σ : D.Torus ≃ D.Torus => (σ : D.Torus → D.Torus)) ''
      PeriodicLattice.latticeIsometries D.L D.m ((D.K : ℕ) : ℤ)
def IsInverseSymmetry (s t : D.Symmetry) : Prop :=
  Function.LeftInverse t.toFun s.toFun ∧ Function.RightInverse t.toFun s.toFun
def ActsOnBonds (s : D.Symmetry) : Prop :=
  Function.Bijective (bondImage s) ∧
    ∀ b : D.DirectedBond, bondImage s b.opposite = (bondImage s b).opposite
def ActsOnGaugeFields (s t : D.Symmetry) : Prop :=
  (∀ U ∈ gaugeFieldSet D, pullback s U ∈ gaugeFieldSet D ∧
    pullback t (pullback s U) = U ∧ pullback s (pullback t U) = U) ∧
  (∃ h : gaugeFieldSet D ≃ₜ gaugeFieldSet D,
    ∀ U : gaugeFieldSet D, (h U : D.BondField) = pullback s U) ∧
  ∃ σ : D.Torus ≃ D.Torus, (σ : D.Torus → D.Torus) = t.toFun ∧
    ∀ U ∈ gaugeFieldSet D, pullback s U = PeriodicLattice.transportGaugeField σ U
def ActsOnFaces (s t : D.Symmetry) : Prop :=
  (∀ p : D.Face, IsFaceImage s p (faceImage s p)) ∧
  Function.Bijective (faceImage s) ∧
  Function.LeftInverse (faceImage t) (faceImage s) ∧
  Function.RightInverse (faceImage t) (faceImage s) ∧
  ∀ p : D.Face,
    (∀ U ∈ gaugeFieldSet D, PeriodicLattice.plaquetteCost (pullback s U) p =
      PeriodicLattice.plaquetteCost U (faceImage s p)) ∧
    (faceImage s p).barycenter = s.toFun p.barycenter
def CommutesWithObservables (s t : D.Symmetry) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : D.Torus → E),
    TestFunctions.IsBoundedFun f → ∀ U ∈ gaugeFieldSet D,
      PeriodicLattice.smearedObservable f (pullback s U) =
        PeriodicLattice.smearedObservable (f ∘ t.toFun) U
def PreservesExpectations (s : D.Symmetry) : Prop :=
  (∀ Υ : D.BondField → ℝ, TestFunctions.IsBoundedFun (fun U : gaugeFieldSet D => Υ U) →
    Measurable[borel (gaugeFieldSet D)] (fun U : gaugeFieldSet D => Υ U) →
    PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling (Υ ∘ pullback s) =
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling Υ) ∧
  ∀ Υ : D.BondField → ℂ, TestFunctions.IsBoundedFun (fun U : gaugeFieldSet D => Υ U) →
    Measurable[borel (gaugeFieldSet D)] (fun U : gaugeFieldSet D => Υ U) →
    PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling (Υ ∘ pullback s) =
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling Υ
def ActsOnCentredObservables (s t : D.Symmetry) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : D.Torus → E),
    TestFunctions.IsBoundedFun f →
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
          (PeriodicLattice.smearedObservable (f ∘ s.toFun)) =
        PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
          (PeriodicLattice.smearedObservable f) ∧
      ∀ U ∈ gaugeFieldSet D,
        D.centredObservable f (pullback s U) = D.centredObservable (f ∘ t.toFun) U
def PreservesConnectedSchwinger (s : D.Symmetry) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (f : Fin n → D.Torus → ℝ) (d : ℝ),
    (∀ i, TestFunctions.IsBoundedFun (f i)) → (∀ i, Measurable (f i)) →
    TestFunctions.HasSeparatedSupportsTorus f d →
      (∀ i, TestFunctions.IsBoundedFun (f i ∘ s.toFun)) ∧ (∀ i, Measurable (f i ∘ s.toFun)) ∧
      TestFunctions.HasSeparatedSupportsTorus (fun i => f i ∘ s.toFun) d ∧
      SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling (fun i => f i ∘ s.toFun) =
        SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling f
def PreservesGibbsFunctional (s : D.Symmetry) : Prop :=
  ∀ (q : ℕ) (h : Fin q → D.Torus → ℝ), MirrorData.IsAdmissibleArg h →
    MirrorData.IsAdmissibleArg (fun l => h l ∘ s.toFun) ∧
      D.gibbsFunctional (fun l => h l ∘ s.toFun) = D.gibbsFunctional h
def SymmetryCovariance : Prop :=
  ∀ D : MirrorData, AffineMapsExhaustSymmetries D ∧
    ∀ s : D.Symmetry, IsAffine s ∧ Function.Bijective s.toFun ∧
      ∃ t : D.Symmetry, IsInverseSymmetry s t ∧ ActsOnBonds s ∧ ActsOnGaugeFields s t ∧
        ActsOnFaces s t ∧ CommutesWithObservables s t ∧ PreservesExpectations s ∧
        ActsOnCentredObservables s t ∧ PreservesConnectedSchwinger s ∧
        PreservesGibbsFunctional s
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance
end
