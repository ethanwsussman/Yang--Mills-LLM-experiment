import YangMills.Construction.ReflectionPositivity.LinkCubeAndItsCubeVectors
import YangMills.Construction.ReflectionPositivity.SitePicturesOfADirection
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField UnitLatticeSymmetry unitRegionObservables
  observableSupNorm)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass linkReflect
  siteReflect)
def linkBlockObservables (r : ℕ+) : Submodule ℂ (GaugeField (1 : ℝ) → ℂ) where
  carrier := unitRegionObservables (linkBlock r)
  add_mem' := by
    rintro A B ⟨oA, mA⟩ ⟨oB, mB⟩
    exact ⟨oA.add oB, Measurable.add mA mB⟩
  zero_mem' := ⟨⟨measurable_const, 0, fun _ => by simp⟩, measurable_const⟩
  smul_mem' := by
    rintro a A ⟨oA, mA⟩
    exact ⟨oA.const_smul a, Measurable.const_smul mA a⟩
def evenPartUnder (θ : UnitLatticeSymmetry) (A : GaugeField (1 : ℝ) → ℂ) :
    GaugeField (1 : ℝ) → ℂ :=
  (1 / 2 : ℂ) • (A + θ.actOn A)
def oddPartUnder (θ : UnitLatticeSymmetry) (A : GaugeField (1 : ℝ) → ℂ) :
    GaugeField (1 : ℝ) → ℂ :=
  (1 / 2 : ℂ) • (A - θ.actOn A)
namespace CubeVectorLinearity
variable (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+)
def SiteCase : Prop :=
  (cubeObservableSpace r : Set (GaugeField (1 : ℝ) → ℂ)) = unitRegionObservables (cubeOfRadius r) ∧
  (∃ L : cubeObservableSpace r →ₗ[ℂ] ReflectionPair.site.Hilb ν μ,
    ∀ A : cubeObservableSpace r, L A = cubeVector ν μ r A) ∧
  ∀ A ∈ unitRegionObservables (cubeOfRadius r),
    evenPartUnder (siteReflect μ) A ∈ unitRegionObservables (cubeOfRadius r) ∧
    oddPartUnder (siteReflect μ) A ∈ unitRegionObservables (cubeOfRadius r) ∧
    (siteReflect μ).actOn (evenPartUnder (siteReflect μ) A) =
      evenPartUnder (siteReflect μ) A ∧
    (siteReflect μ).actOn (oddPartUnder (siteReflect μ) A) =
      -oddPartUnder (siteReflect μ) A ∧
    cubeVector ν μ r A =
      cubeVector ν μ r (evenPartUnder (siteReflect μ) A) +
        cubeVector ν μ r (oddPartUnder (siteReflect μ) A) ∧
    cubeReflectionNorm ν r (evenPartUnder (siteReflect μ) A) ≤ cubeReflectionNorm ν r A ∧
    cubeReflectionNorm ν r (oddPartUnder (siteReflect μ) A) ≤
      cubeReflectionNorm ν r A
def LinkCase : Prop :=
  (linkBlockObservables r : Set (GaugeField (1 : ℝ) → ℂ)) = unitRegionObservables (linkBlock r) ∧
  (∃ L : linkBlockObservables r →ₗ[ℂ] ReflectionPair.link.Hilb ν μ,
    ∀ A : linkBlockObservables r, L A = linkBlockVector ν μ r A) ∧
  ∀ A ∈ unitRegionObservables (linkBlock r),
    evenPartUnder (linkReflect μ) A ∈ unitRegionObservables (linkBlock r) ∧
    oddPartUnder (linkReflect μ) A ∈ unitRegionObservables (linkBlock r) ∧
    (linkReflect μ).actOn (evenPartUnder (linkReflect μ) A) =
      evenPartUnder (linkReflect μ) A ∧
    (linkReflect μ).actOn (oddPartUnder (linkReflect μ) A) =
      -oddPartUnder (linkReflect μ) A ∧
    linkBlockVector ν μ r A =
      linkBlockVector ν μ r (evenPartUnder (linkReflect μ) A) +
        linkBlockVector ν μ r (oddPartUnder (linkReflect μ) A) ∧
    observableSupNorm (evenPartUnder (linkReflect μ) A) ≤ observableSupNorm A ∧
    observableSupNorm (oddPartUnder (linkReflect μ) A) ≤ observableSupNorm A
def Statement : Prop :=
  ∀ (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+), SiteCase ν μ r ∧ LinkCase ν μ r
end CubeVectorLinearity
end YangMills.Construction.ReflectionPositivity.DirectionPictures
