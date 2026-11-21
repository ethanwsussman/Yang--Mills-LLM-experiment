import YangMills.Construction.InfiniteLattice.ObjectsAtOneSpacingAndThoseOfTheDefinitionsProof
import YangMills.Construction.ReflectionPositivity.ReflectionGroupAndCubeReflectionSize
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ComplexConjugate ComplexOrder Matrix Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LatticeAtSpacing
open YangMills.Construction.InfiniteLattice (AmbientSpace GaugeField Link LatticeSymmetry LatticeMirror
  regionObservables IsLocalObservable shiftInvariantSigma IsPeriodicMeasure IsShiftInvariant
  LinkVariables positiveLinkSet positiveLinksWithin restrictField gluedField trivialField scaledCube)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb continuousFns)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (MirrorPair basisVec
  IsReflectionPositiveAcross)
open YangMills.Construction.ReflectionPositivity.DirectionPictures (axisReflectionGroup)
variable {a : ℝ}
theorem tendsto_nhds_iff_tendstoWeak (ν : ℕ → BorelProb a) (μ : BorelProb a) :
    Tendsto ν atTop (𝓝 μ) ↔ BorelProb.TendstoWeak ν μ := by apply _root_.YangMills.Construction.InfiniteLattice.FixedSpacing.tendsto_iff_tendstoWeak <;> assumption
abbrev RegionLinkVariables (a : ℝ) (S : Set AmbientSpace) : Type :=
  LinkVariables ↥(positiveLinksWithin a S)
theorem borelSpace_regionLinkVariables (a : ℝ) (S : Set AmbientSpace) :
    BorelSpace (RegionLinkVariables a S) := by
  have : SecondCountableTopology YangMills.Construction.Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact Pi.borelSpace
theorem subsingleton_regionLinkVariables {S : Set AmbientSpace}
    (h : positiveLinksWithin a S = ∅) : Subsingleton (RegionLinkVariables a S) := by
  have : IsEmpty ↥(positiveLinksWithin a S) := Set.isEmpty_coe_sort.mpr h
  infer_instance
def restrictToRegion (S : Set AmbientSpace) (U : GaugeField a) : RegionLinkVariables a S :=
  restrictField U (positiveLinksWithin a S)
def extendFromRegion (ha : 0 < a) (S : Set AmbientSpace) (V : RegionLinkVariables a S) :
    GaugeField a :=
  gluedField ha inter_subset_left V (trivialField a)
theorem extendFromRegion_of_mem (ha : 0 < a) (S : Set AmbientSpace) (V : RegionLinkVariables a S)
    (b : ↥(positiveLinksWithin a S)) : extendFromRegion ha S V b = V b :=
  YangMills.Construction.InfiniteLattice.gluedField_apply_of_mem ha inter_subset_left V _ b
theorem extendFromRegion_of_notMem (ha : 0 < a) (S : Set AmbientSpace) (V : RegionLinkVariables a S)
    {b : Link a} (hb : b ∈ positiveLinkSet a \ positiveLinksWithin a S) :
    extendFromRegion ha S V b = 1 :=
  YangMills.Construction.InfiniteLattice.gluedField_apply_of_notMem ha inter_subset_left V _ hb
theorem extendFromRegion_opposite (ha : 0 < a) (S : Set AmbientSpace) (V : RegionLinkVariables a S)
    (b : Link a) : extendFromRegion ha S V b.opposite = (extendFromRegion ha S V b)⁻¹ :=
  (extendFromRegion ha S V).2 b
def _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.MirrorPair.upperHalf
    (P : MirrorPair a) : Set AmbientSpace :=
  {x | P.height ≤ P.normal ⬝ᵥ x}
def _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.MirrorPair.lowerHalf
    (P : MirrorPair a) : Set AmbientSpace :=
  {x | P.normal ⬝ᵥ x ≤ P.height}
theorem reflect_apply (P : MirrorPair a) (x : AmbientSpace) :
    P.reflect.toFun x =
      x - (2 * (P.normal ⬝ᵥ P.normal)⁻¹ * (P.normal ⬝ᵥ x - P.height)) • P.normal := by
  change YangMills.Construction.InfiniteLattice.hyperplaneReflect P.normal P.height x = _
  rw [YangMills.Construction.InfiniteLattice.hyperplaneReflect]
  congr 2
  ring
theorem isReflectionPositiveAcross_iff (ν : BorelProb a) (P : MirrorPair a) :
    IsReflectionPositiveAcross ν.1 P ↔
      (∀ F : GaugeField a → ℂ, IsLocalObservable F → F ∈ regionObservables a P.upperHalf →
        0 ≤ ν.integral fun U => conj (P.reflect.actOn F U) * F U) ∧
      ∀ F : GaugeField a → ℂ, IsLocalObservable F → F ∈ regionObservables a P.lowerHalf →
        0 ≤ ν.integral fun U => conj (P.reflect.actOn F U) * F U := by
  constructor
  · rintro ⟨-, h⟩
    exact ⟨fun F hl hF => h _ (Or.inl rfl) F hF.1 hl hF.2,
      fun F hl hF => h _ (Or.inr rfl) F hF.1 hl hF.2⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨ν.2, fun H hH F ho hl hm => ?_⟩
    rcases hH with rfl | rfl
    · exact h₁ F hl ⟨ho, hm⟩
    · exact h₂ F hl ⟨ho, hm⟩
def reflectionPositiveSet (a : ℝ) : Set (BorelProb a) :=
  {ν | IsShiftInvariant ν.1 ∧ ∀ (P : MirrorPair a) (F : GaugeField a → ℂ),
    IsLocalObservable F → F ∈ regionObservables a P.upperHalf →
      0 ≤ ν.integral fun U => conj (P.reflect.actOn F U) * F U}
def IsErgodicState (ν : BorelProb a) : Prop :=
  IsPeriodicMeasure ν.1 ∧
    ∀ I : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] I → ν.1 I = 0 ∨ ν.1 I = 1
def coordinateMirror (a : ℝ) (μ : Fin 4) : MirrorPair a where
  normal := basisVec μ
  height := 0
  admissible := Or.inl ⟨⟨μ, rfl⟩, 0, by simp⟩
def coordinateReflect (a : ℝ) (μ : Fin 4) : LatticeSymmetry a := (coordinateMirror a μ).reflect
theorem coordinateReflect_toFun (a : ℝ) (μ : Fin 4) :
    (coordinateReflect a μ).toFun =
      (YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.siteReflect μ).toFun :=
  rfl
theorem coordinateReflect_apply (a : ℝ) (μ : Fin 4) (x : AmbientSpace) :
    (coordinateReflect a μ).toFun x = x - (2 * x μ) • basisVec μ := by
  rw [coordinateReflect_toFun]
  exact YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.siteReflect_apply μ x
theorem image_latticeSubgroup_subset {g : Equiv.Perm AmbientSpace} (hg : g ∈ axisReflectionGroup)
    (a : ℝ) :
    g '' (YangMills.Construction.InfiniteLattice.latticeSubgroup a : Set AmbientSpace) ⊆
      YangMills.Construction.InfiniteLattice.latticeSubgroup a := by
  obtain ⟨ε, hε⟩ :=
    YangMills.Construction.ReflectionPositivity.DirectionPictures.exists_signs_of_mem_axisReflectionGroup hg
  rintro _ ⟨y, ⟨n, hn⟩, rfl⟩
  refine ⟨fun i => (ε i : ℤ) * n i, fun i => ?_⟩
  rw [hε, hn]
  push_cast
  ring
def axisReflectionSymmetry (a : ℝ) (γ : axisReflectionGroup) : LatticeSymmetry a where
  toFun := γ.1
  preservesDist :=
    (YangMills.Construction.ReflectionPositivity.DirectionPictures.axisReflectionGroup_isometry γ.2).1
  image_eq := by
    refine Subset.antisymm (image_latticeSubgroup_subset γ.2 a) fun x hx => ?_
    exact ⟨γ.1⁻¹ x, image_latticeSubgroup_subset (inv_mem γ.2) a ⟨x, hx, rfl⟩, by simp⟩
def cubeHalfWidth (a : ℝ) (r : ℕ+) : ℝ := (r : ℝ) * a
theorem centeredCube_eq (ha : 0 < a) (r : ℕ+) :
    scaledCube a r = {x | YangMills.Construction.GibbsAtFixedSpacing.linfNorm x ≤ cubeHalfWidth a r} := by
  ext x
  rw [YangMills.Construction.InfiniteLattice.mem_centeredCube ha, mem_ofPred_eq,
    YangMills.Construction.GibbsAtFixedSpacing.linfNorm, Finset.sup'_le_iff]
  simp [cubeHalfWidth, abs_le]
end YangMills.Construction.ReflectionPositivity.LatticeAtSpacing
