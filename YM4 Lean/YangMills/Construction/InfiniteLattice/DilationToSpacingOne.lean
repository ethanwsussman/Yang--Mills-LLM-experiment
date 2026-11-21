import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.ImageOfAStateUnderTheDilation
import YangMills.Construction.InfiniteLattice.OneLatticeAtOneSpacing
import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.InfiniteLattice YangMills.Construction.NormalFamilies
open scoped Matrix
noncomputable section
namespace YangMills.Construction.UnitSpacing
variable {a : ℝ}
def conjugateByScaling (a : ℝ) (f : AmbientSpace → AmbientSpace) : AmbientSpace → AmbientSpace :=
  fun x => scaleByInv a (f (a • x))
def precompRescale (ha : 0 < a) (F : GaugeField 1 → ℂ) : GaugeField a → ℂ :=
  F ∘ fieldRescale ha
theorem rescaledLink_isPositivelyOriented (ha : 0 < a) {b : Link a} (hb : b.IsPositivelyOriented) :
    (rescaledLink ha b).IsPositivelyOriented := by
  obtain ⟨μ, h⟩ := hb
  refine ⟨μ, ?_⟩
  change pointScale a⁻¹ (one_eq_inv_mul_spacing ha) b.terminal -
    pointScale a⁻¹ (one_eq_inv_mul_spacing ha) b.initial = axisStep 1 μ
  rw [← pointScale_sub, h, pointScale_axisStep]
open Classical in
def rescaledWindow (ha : 0 < a) (W : LinkWindow a) : LinkWindow 1 where
  links := W.links.image (rescaledLink ha)
  isPositive b hb := by
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    exact rescaledLink_isPositivelyOriented ha (W.isPositive b' hb')
def LatticeStructureTransfers (ha : 0 < a) : Prop :=
  Function.Bijective (pointRescale ha) ∧
    Function.Bijective (rescaledLink ha) ∧
    BijOn (rescaledLink ha) (positiveLinks a) (positiveLinks 1) ∧
    Function.Bijective (rescaledPlaquette ha) ∧
    (∀ p : ElementaryPlaquette a,
      pointRescale ha '' p.cornerSet = (rescaledPlaquette ha p).cornerSet ∧
        rescaledLink ha '' p.linkSet = (rescaledPlaquette ha p).linkSet) ∧
    (∃ e : GaugeField a ≃ₜ GaugeField 1, ⇑e = fieldRescale ha) ∧
    ∀ (p : ElementaryPlaquette a) (U : GaugeField a),
      faceEnergy (fieldRescale ha U) (rescaledPlaquette ha p) = faceEnergy U p
def ObservablesTransfer (ha : 0 < a) : Prop :=
  BijOn (precompRescale ha) {F | IsBoundedObservable F} {F | IsBoundedObservable F} ∧
    (∀ S : Set AmbientSpace,
      precompRescale ha '' regionObservables 1 (scaleByInvImage a S) = regionObservables a S) ∧
    precompRescale ha '' continuousLocalFunctions 1 = continuousLocalFunctions a
def SymmetriesTransfer (ha : 0 < a) : Prop :=
  ∀ r : LatticeSymmetry a, ∃ r' : LatticeSymmetry 1,
    r'.toFun = conjugateByScaling a r.toFun ∧
      ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
        r.actOn (precompRescale ha F) = precompRescale ha (r'.actOn F)
def SymmetryConjugates (ha : 0 < a) : Prop :=
  (∀ v : LatticePoint a,
    conjugateByScaling a (shift v).toFun = (shift (pointRescale ha v)).toFun) ∧
    (∀ w ∈ hyperoctahedralLinearGroup, conjugateByScaling a w = w) ∧
    ∀ n ∈ normalSet, ∀ c : ℝ,
      conjugateByScaling a (reflectAcross n c) = reflectAcross n (c / a)
def MirrorsTransfer (a : ℝ) : Prop :=
  (∀ n ∈ normalSet, ∀ x : LatticePoint a, ∃ k : ℤ, linearHeight n (x : AmbientSpace) = (k : ℝ) * a) ∧
    (∀ n ∈ normalSet, ∀ c : ℝ, IsAllowedLevel a n c ↔ IsAllowedLevel 1 n (c / a)) ∧
    (∀ P : NormalLevelPair a, ∃ P' : NormalLevelPair 1,
      P'.normal = P.normal ∧ P'.level = P.level / a ∧
        (∃ r : LatticeSymmetry a, r.toFun = reflectAcross P.normal P.level) ∧
        (P.IsSitePair ↔ P'.IsSitePair) ∧
        (P.IsLinkPair ↔ P'.IsLinkPair) ∧
        (P.IsDiagonalPair ↔ P'.IsDiagonalPair) ∧
        IsLatticeMirror a {x | P.normal ⬝ᵥ x = P.level} ∧
        ∀ ε : ℤˣ, scaleByInvImage a (closedHalfSpace P.normal P.level ε) =
          closedHalfSpace P.normal (P.level / a) ε) ∧
    ∀ H : Set AmbientSpace, IsLatticeMirror a H →
      ∃ P : NormalLevelPair a, H = {x | P.normal ⬝ᵥ x = P.level}
def KernelAndGaugeTransfer (ha : 0 < a) (β : ℝ) : Prop :=
  (∀ (W : LinkWindow a) (F : GaugeField 1 → ℂ), IsBoundedObservable F →
    W.conditionalExpectation ha β (precompRescale ha F) =
      (rescaledWindow ha W).conditionalExpectation one_pos β F ∘ fieldRescale ha) ∧
    ∀ h : GaugeTransform a, ∃ h' : GaugeTransform 1,
      (∀ x : LatticePoint 1, h'.toFun x = h.toFun (pointScale a (mul_one a).symm x)) ∧
        ∀ U : GaugeField a,
          fieldRescale ha (h.act U) = h'.act (fieldRescale ha U)
def GibbsClassesTransfer (ha : 0 < a) (β : ℝ) : Prop :=
  (∀ ν ∈ gibbsClass ha β, dilatedState ha ν ∈ gibbsClass one_pos β) ∧
    (∀ ν' ∈ gibbsClass (a := 1) one_pos β,
      ∃ ν ∈ gibbsClass ha β, dilatedState ha ν = ν' ∧
        ∀ ν₂ : Measure (GaugeField a), IsProbabilityMeasure ν₂ →
          dilatedState ha ν₂ = ν' → ν₂ = ν) ∧
    (∀ Q : AddSubgroup (LatticePoint a),
      dilatedState ha '' subgroupInvariantGibbsClass ha β Q =
        subgroupInvariantGibbsClass one_pos β (subgroupRescale ha Q)) ∧
    dilatedState ha '' periodicGibbsClass ha β = periodicGibbsClass one_pos β
def PeriodSublatticesTransfer (ha : 0 < a) (β : ℝ) : Prop :=
  (∀ Γ : AddSubgroup (LatticePoint a),
    (∃ P : PeriodSublattice a, P.periods = Γ) ↔
      ∃ P' : PeriodSublattice 1, P'.periods = subgroupRescale ha Γ) ∧
    ∀ (P : PeriodSublattice a) (P' : PeriodSublattice 1), P'.periods = subgroupRescale ha P.periods →
      (∃ e : P.QuotientTorus → P'.QuotientTorus, Function.Bijective e ∧
        ∀ x : LatticePoint a, e (P.quotientMap x) = P'.quotientMap (pointRescale ha x)) ∧
        dilatedState ha (P.liftedGibbsMeasure β) = P'.liftedGibbsMeasure β
def ScalingToUnitSpacing : Prop :=
  ∀ (a β : ℝ) (ha : 0 < a), 0 < β →
    LatticeStructureTransfers ha ∧
      ObservablesTransfer ha ∧
      SymmetriesTransfer ha ∧
      SymmetryConjugates ha ∧
      MirrorsTransfer a ∧
      KernelAndGaugeTransfer ha β ∧
      GibbsClassesTransfer ha β ∧
      PeriodSublatticesTransfer ha β
end YangMills.Construction.UnitSpacing
