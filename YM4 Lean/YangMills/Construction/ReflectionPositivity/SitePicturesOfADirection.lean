import YangMills.Construction.InfiniteLattice.ShiftInvariantConditioningAndPlateau
import YangMills.Construction.ReflectionPositivity.ReflectionGroupAndCubeReflectionSize
import YangMills.Construction.ReflectionPositivity.SetOfTheSpectralVariablesThatCarriesTheSpectrum
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField AmbientSpace LatticePoint axisStep shift
  halfSpaceLocalObservables observableSupNorm unitRegionObservables IsBoundedObservable
  UnitLatticeSymmetry condExpGiven shiftInvariantSigma)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass siteReflect)
open YangMills.Construction.FormHilbert (StrongTendsto)
def axisSignFlip (ε : Fin 4 → ℤˣ) (x : AmbientSpace) : AmbientSpace :=
  fun i => ((ε i : ℤ) : ℝ) * x i
def cubeObservableSpace (r : ℕ+) : Submodule ℂ (GaugeField (1 : ℝ) → ℂ) where
  carrier := unitRegionObservables (cubeOfRadius r)
  add_mem' := by
    rintro F G ⟨hF, mF⟩ ⟨hG, mG⟩
    exact ⟨hF.add hG, Measurable.add mF mG⟩
  zero_mem' := ⟨⟨measurable_const, 0, fun _ => by simp⟩, measurable_const⟩
  smul_mem' := by
    rintro a F ⟨hF, mF⟩
    exact ⟨hF.const_smul a, Measurable.const_smul mF a⟩
def reflectedCorrelation (meas : unitPositiveClass) (μ : Fin 4)
    (F : GaugeField (1 : ℝ) → ℂ) (v : LatticePoint (1 : ℝ)) : ℂ :=
  ∫ U, conj ((siteReflect μ).actOn F U) * (shift v).actOn F U
    ∂(meas : Measure (GaugeField (1 : ℝ)))
namespace SiteReflectionPair
variable (meas : unitPositiveClass) (μ : Fin 4) (r : ℕ+)
def CubeFacts : Prop :=
  (∀ g : Equiv.Perm AmbientSpace, g ∈ axisReflectionGroup ↔ ∃ ε, ⇑g = axisSignFlip ε) ∧
  Nat.card axisReflectionGroup = 16 ∧
  (∀ ε, ∃ s : UnitLatticeSymmetry, s.toFun = axisSignFlip ε) ∧
  (∀ γ : axisReflectionGroup,
    (axisReflectionGroup.toUnitLatticeSymmetry γ).setImage (cubeOfRadius r) = cubeOfRadius r) ∧
  (∀ γ : axisReflectionGroup, ∀ F ∈ unitRegionObservables (cubeOfRadius r),
    (axisReflectionGroup.toUnitLatticeSymmetry γ).actOn F ∈
      unitRegionObservables (cubeOfRadius r)) ∧
  ∀ F ∈ unitRegionObservables (cubeOfRadius r),
    (shift ((r : ℕ) • axisStep (1 : ℝ) μ)).actOn F ∈
        unitRegionObservables {x | 0 ≤ x μ ∧ x μ ≤ 2 * (r : ℝ)} ∧
      (shift ((r : ℕ) • axisStep (1 : ℝ) μ)).actOn F ∈ halfSpaceLocalObservables μ ∧
      ‖cubeVector meas μ r F‖ ≤ observableSupNorm F
def SpectralSupport : Prop :=
  (∃ hC : IsClosed (imageInSpectrum μ (siteCone μ)),
    (ReflectionPair.site.jointPVM meas μ).IsSupportedOn ⟨_, hC.measurableSet⟩) ∧
  (∀ x ∈ siteCone μ,
    (x.1 = 0 → x.2 = 0) ∧
    (x.1 ≠ ⊤ → (∀ l, Real.cosh x.1.toReal + Real.cos (x.2 l) ≥ 2) ∧
      x.1.toReal ≥ slopeConstant * angleSupNorm μ x.2)) ∧
  (∀ l : TransverseAxis μ,
    ReflectionPair.site.shiftOp meas μ l * groundProjection μ ReflectionPair.site meas =
        groundProjection μ ReflectionPair.site meas ∧
      groundProjection μ ReflectionPair.site meas * ReflectionPair.site.shiftOp meas μ l =
        groundProjection μ ReflectionPair.site meas) ∧
  (∀ n : ℕ, ReflectionPair.site.transferOp meas μ ^ n * groundProjection μ ReflectionPair.site meas =
    groundProjection μ ReflectionPair.site meas) ∧
  StrongTendsto (fun n => ReflectionPair.site.transferOp meas μ ^ n)
    (groundProjection μ ReflectionPair.site meas)
def MultiStepBound : Prop :=
  ∀ (l : TransverseAxis μ) (k : ℕ), 1 ≤ k →
    (1 - ReflectionPair.site.transferOp meas μ ^ k) ^ 2 ≥
      ReflectionPair.site.transferOp meas μ ^ k *
        ((2 : ℂ) • 1 - ReflectionPair.site.shiftOp meas μ l ^ k -
          star (ReflectionPair.site.shiftOp meas μ l) ^ k) ∧
    ∀ F ∈ halfSpaceLocalObservables μ,
      0 ≤ reflectedCorrelation meas μ F 0 -
        4 * reflectedCorrelation meas μ F (k • axisStep (1 : ℝ) μ) +
        reflectedCorrelation meas μ F ((2 * k) • axisStep (1 : ℝ) μ) +
        reflectedCorrelation meas μ F (k • axisStep (1 : ℝ) μ + k • axisStep (1 : ℝ) l.1) +
        reflectedCorrelation meas μ F (k • axisStep (1 : ℝ) μ - k • axisStep (1 : ℝ) l.1)
def GroundStateFacts : Prop :=
  (∀ F ∈ halfSpaceLocalObservables μ, ∀ H ∈ halfSpaceLocalObservables μ,
    inner ℂ (ReflectionPair.site.obsClass meas μ F)
        (groundProjection μ ReflectionPair.site meas (ReflectionPair.site.obsClass meas μ H)) =
      ∫ U, conj (condExpGiven meas (shiftInvariantSigma 1) F U) *
        condExpGiven meas (shiftInvariantSigma 1) H U
        ∂(meas : Measure (GaugeField (1 : ℝ)))) ∧
  ∀ F : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable F → ∀ v : LatticePoint (1 : ℝ),
    condExpGiven meas (shiftInvariantSigma 1) ((siteReflect μ).actOn F)
        =ᵐ[(meas : Measure (GaugeField (1 : ℝ)))] condExpGiven meas (shiftInvariantSigma 1) F ∧
      condExpGiven meas (shiftInvariantSigma 1) F
        =ᵐ[(meas : Measure (GaugeField (1 : ℝ)))]
          condExpGiven meas (shiftInvariantSigma 1) ((shift v).actOn F)
def CubeCorrelations : Prop :=
  (∀ F ∈ unitRegionObservables (cubeOfRadius r), ∀ G ∈ unitRegionObservables (cubeOfRadius r),
    ∀ y : Fin 4 → ℤ, 2 * (r : ℤ) ≤ y μ →
      ∫ U, conj (F U) * (shift (intPoint y)).actOn G U
          ∂(meas : Measure (GaugeField (1 : ℝ))) =
        inner ℂ (cubeVector meas μ r ((siteReflect μ).actOn F))
          ((ReflectionPair.site.transferOp meas μ ^ (y μ - 2 * (r : ℤ)).toNat *
            ReflectionPair.site.shiftMonomial meas μ (y - y μ • Pi.single μ 1))
            (cubeVector meas μ r G))) ∧
  (∀ F ∈ unitRegionObservables (cubeOfRadius r), ∀ G ∈ unitRegionObservables (cubeOfRadius r),
    ∀ y : Fin 4 → ℤ,
      ∫ U, conj (F U) * (shift (intPoint (-y))).actOn G U
          ∂(meas : Measure (GaugeField (1 : ℝ))) =
        conj (∫ U, conj (G U) * (shift (intPoint y)).actOn F U
          ∂(meas : Measure (GaugeField (1 : ℝ))))) ∧
  ∀ F ∈ unitRegionObservables (cubeOfRadius r),
    ((‖cubeVector meas μ r F‖ ^ 2 : ℝ) : ℂ) =
      ∫ U, conj ((siteReflect μ).actOn F U) *
        (shift ((2 * (r : ℕ)) • axisStep (1 : ℝ) μ)).actOn F U
        ∂(meas : Measure (GaugeField (1 : ℝ)))
def ReflectionNormFacts : Prop :=
  (∃ p : Seminorm ℂ (cubeObservableSpace r), ∀ F : cubeObservableSpace r,
    p F = cubeReflectionNorm meas r (F : GaugeField (1 : ℝ) → ℂ) ^ (1 / 2 : ℝ)) ∧
  (∀ γ : axisReflectionGroup, ∀ F ∈ unitRegionObservables (cubeOfRadius r),
    cubeReflectionNorm meas r ((axisReflectionGroup.toUnitLatticeSymmetry γ).actOn F) =
      cubeReflectionNorm meas r F) ∧
  ∀ F ∈ unitRegionObservables (cubeOfRadius r), cubeReflectionNorm meas r F ≤ observableSupNorm F ^ 2
def Conclusion : Prop :=
  ∀ (meas : unitPositiveClass) (μ : Fin 4) (r : ℕ+),
    CubeFacts meas μ r ∧ SpectralSupport meas μ ∧ MultiStepBound meas μ ∧ GroundStateFacts meas μ ∧
      CubeCorrelations meas μ r ∧ ReflectionNormFacts meas r
end SiteReflectionPair
end YangMills.Construction.ReflectionPositivity.DirectionPictures
