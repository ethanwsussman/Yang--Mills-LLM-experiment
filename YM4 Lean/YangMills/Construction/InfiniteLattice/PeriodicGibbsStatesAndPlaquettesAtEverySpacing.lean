import YangMills.Construction.InfiniteLattice.DictionaryBetweenSpacings
import YangMills.Construction.InfiniteLattice.UnitLatticeIsometriesAndPlaquettes
import YangMills.Construction.ReflectionPositivity.OneLatticeAtEverySpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Pointwise
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicGibbsAtEverySpacing
open GibbsAtFixedSpacing (BorelProb)
open CutoffLattice (faceLinks)
open ReflectionPositivity.MirrorHyperplanes (IsHalfIntMultiple IsIntMultiple IsReflectionPositiveAcross MirrorPair)
open ReflectionPositivity.LatticeAtSpacing (IsErgodicState reflectionPositiveSet)
open CutoffStructure (IsContinuousInLinks)
variable {a : ℝ}
def rescaledMirror (ha : 0 < a) (M : MirrorPair a) : MirrorPair 1 where
  normal := M.normal
  height := M.height / a
  admissible := by
    rcases M.admissible with ⟨hn, q, hq⟩ | ⟨hn, q, hq⟩
    · exact Or.inl ⟨hn, q, by rw [hq]; field_simp⟩
    · exact Or.inr ⟨hn, q, by rw [hq]; field_simp⟩
def RescalingTransfersProperties (ha : 0 < a) (μ : BorelProb a) (M : MirrorPair a) (β : ℝ) : Prop :=
  (IsShiftInvariant μ.1 ↔ IsShiftInvariant (pushToUnit μ.1)) ∧
    ((rescaledMirror ha M).hyperplane = a⁻¹ • M.hyperplane ∧
      a⁻¹ • M.hyperplane = inverseScaling ha '' M.hyperplane ∧
      (IsReflectionPositiveAcross μ.1 M ↔
        IsReflectionPositiveAcross (pushToUnit μ.1) (rescaledMirror ha M))) ∧
    (IsGibbs β μ.1 ↔ IsGibbs β (pushToUnit μ.1)) ∧
    (IsPeriodicGibbs β μ.1 ↔ IsPeriodicGibbs β (pushToUnit μ.1)) ∧
    (IsExtremalPeriodicGibbs β μ.1 ↔ IsExtremalPeriodicGibbs β (pushToUnit μ.1)) ∧
    (IsErgodicState μ ↔ IsErgodicState (GaugeFieldProbability.toUnit μ))
def PushforwardFormulas (μ : BorelProb a) : Prop :=
  ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
    ∫ U, F (gaugeFieldRescale a U) ∂μ.1 = ∫ U, F U ∂(pushToUnit μ.1) ∧
      (IsShiftInvariant μ.1 →
        condExpShiftInvariant μ.1 (F ∘ gaugeFieldRescale a) =ᵐ[μ.1]
          condExpShiftInvariant (pushToUnit μ.1) F ∘ gaugeFieldRescale a)
def SymmetriesAreLatticeMotions (a : ℝ) : Prop :=
  (∀ s : AmbientSpace → AmbientSpace, (∃ g : LatticeSymmetry a, g.toFun = s) ↔ s ∈ affineHyperoctahedralMaps a) ∧
    hyperoctahedralLinearGroup =
      Subgroup.closure UnitSymmetriesAndFaces.axisAndDiagonalReflections
def ReflectionPositiveStatesAreSymmetric (a : ℝ) : Prop :=
  ∀ μ ∈ reflectionPositiveSet a, ∀ g : LatticeSymmetry a, IsSymmetricUnder μ.1 g
def FaceEnergyIsContinuousAndBounded (a : ℝ) : Prop :=
  ∀ p : ElementaryPlaquette a,
    IsContinuousInLinks (faceLinks p) (fun U : GaugeField a => faceEnergy U p) ∧
      ∀ U : GaugeField a, 0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2
def SymmetriesTransportFaces (a : ℝ) : Prop :=
  ∀ (g : LatticeSymmetry a) (p : ElementaryPlaquette a),
    (∃! q : ElementaryPlaquette a, q.cornerSet = g.pointMap '' p.cornerSet) ∧
      (g.plaquetteMap p).cornerSet = g.pointMap '' p.cornerSet ∧
      (g.plaquetteMap p).center = g.toFun p.center ∧
      g.actOn (fun U : GaugeField a => faceEnergy U p) =
        fun U : GaugeField a => faceEnergy U (g.plaquetteMap p)
def SymmetriesTransitiveOnFaces (a : ℝ) : Prop :=
  ∀ p p' : ElementaryPlaquette a, ∃ g : LatticeSymmetry a, g.plaquetteMap p = p'
def FaceEnergyMeansAgree (a : ℝ) : Prop :=
  ∀ μ ∈ reflectionPositiveSet a, ∀ p p' : ElementaryPlaquette a,
    ∫ U : GaugeField a, faceEnergy U p ∂μ.1 =
      ∫ U : GaugeField a, faceEnergy U p' ∂μ.1
def PeriodicGibbsConvex (a β : ℝ) : Prop :=
  ∀ μ₁ μ₂ : Measure (GaugeField a), IsPeriodicGibbs β μ₁ → IsPeriodicGibbs β μ₂ →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      IsPeriodicGibbs β (ENNReal.ofReal t • μ₁ + ENNReal.ofReal (1 - t) • μ₂)
def ExtremalImpliesErgodic (a β : ℝ) : Prop :=
  ∀ μ : BorelProb a, IsExtremalPeriodicGibbs β μ.1 → IsErgodicState μ
def ErgodicImpliesExtremal (a β : ℝ) : Prop :=
  (∀ μ : Measure (GaugeField a), IsPeriodicGibbs β μ → IsShiftInvariant μ) →
    ∀ μ : BorelProb a, IsPeriodicGibbs β μ.1 → IsErgodicState μ → IsExtremalPeriodicGibbs β μ.1
def Statement : Prop :=
  ∀ (a : ℝ) (ha : 0 < a),
    (∀ (μ : BorelProb a) (M : MirrorPair a) (β : ℝ), 0 < β → RescalingTransfersProperties ha μ M β) ∧
      (∀ μ : BorelProb a, PushforwardFormulas μ) ∧
      SymmetriesAreLatticeMotions a ∧
      ReflectionPositiveStatesAreSymmetric a ∧
      FaceEnergyIsContinuousAndBounded a ∧
      SymmetriesTransportFaces a ∧
      SymmetriesTransitiveOnFaces a ∧
      FaceEnergyMeansAgree a ∧
      ∀ β : ℝ, 0 < β →
        PeriodicGibbsConvex a β ∧ ExtremalImpliesErgodic a β ∧ ErgodicImpliesExtremal a β
end YangMills.Construction.InfiniteLattice.PeriodicGibbsAtEverySpacing
end
