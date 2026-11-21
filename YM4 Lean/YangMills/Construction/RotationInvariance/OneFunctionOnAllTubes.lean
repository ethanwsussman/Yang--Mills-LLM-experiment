import YangMills.Construction.ForwardTube.SuccessiveTubeDomainsAndLabelledPoints
import YangMills.Construction.RotationInvariance.TubesOfTheFramesAndOrderings
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace ForwardTube
def addConstTuple {n : ℕ} (z : Fin n → ℂ × ℂ) (u : ℂ × ℂ) : Fin n → ℂ × ℂ :=
  fun i => z i + u
end ForwardTube
namespace RealPlane
def translateTuple {n : ℕ} (y : Fin n → RealPlane) (u : RealPlane) :
    Fin n → RealPlane :=
  fun i => y i + u
def coincidenceSubspace {n : ℕ} (i j k l : Fin n) : Submodule ℝ (Fin n → RealPlane) where
  carrier := {y | y i 0 = y j 0 ∧ y k 1 = y l 1}
  add_mem' := by
    rintro a b ⟨ha₀, ha₁⟩ ⟨hb₀, hb₁⟩
    exact ⟨by simp [ha₀, hb₀], by simp [ha₁, hb₁]⟩
  zero_mem' := by simp
  smul_mem' := by
    rintro c a ⟨ha₀, ha₁⟩
    exact ⟨by simp [ha₀], by simp [ha₁]⟩
end RealPlane
namespace EuclideanFunctionals
open ForwardTube
def ExtendsOrderedKernels (S : ConnFamily) {q : ℕ} (φ : Fin (q + 1) → realLabels)
    (K : (Fin (q + 1) → ℂ × ℂ) → ℂ) : Prop :=
  ∀ (υ : rightAngleMultiples) (σ : Equiv.Perm (Fin (q + 1))),
    ∀ z ∈ orderedTube υ σ, K z = orderedFrameKernel S υ σ z φ
def unionKernel (S : ConnFamily) {q : ℕ} (φ : Fin (q + 1) → realLabels) :
    (Fin (q + 1) → ℂ × ℂ) → ℂ :=
  Classical.epsilon (ExtendsOrderedKernels S φ)
namespace UnionKernel
variable {q : ℕ}
def StableOpenCone (υ : rightAngleMultiples) (σ : Equiv.Perm (Fin (q + 1))) : Prop :=
  IsOpen (orderedTube υ σ) ∧ Convex ℝ (orderedTube υ σ) ∧
    (∀ z ∈ orderedTube υ σ, ∀ t : ℝ, 0 < t → t • z ∈ orderedTube υ σ) ∧
    ∀ z ∈ orderedTube υ σ,
      (∀ u : ℂ × ℂ, addConstTuple z u ∈ orderedTube υ σ) ∧
      (∀ s : ℝ, imagBoostTuple s z ∈ orderedTube υ σ) ∧
      embedPlaneTuple (tupleRe z) ∈ orderedTube υ σ
def RealLocusOrdered (υ : rightAngleMultiples) (σ : Equiv.Perm (Fin (q + 1))) : Prop :=
  realLocus (orderedTube υ σ) =
    embedPlaneTuple '' {y | ∀ i : Fin q,
      inner ℝ (rotatedDirection υ) (y (σ i.castSucc)) < inner ℝ (rotatedDirection υ) (y (σ i.succ))}
def IntegralRepresentation (S : ConnFamily) (υ : rightAngleMultiples)
    (σ : Equiv.Perm (Fin (q + 1))) (φ : Fin (q + 1) → realLabels) : Prop :=
  ∀ f : Fin (q + 1) → RealPlane → ℂ, (∀ i, f i ∈ complexProfiles) →
    (∀ y : Fin (q + 1) → RealPlane, (∀ i, y i ∈ tsupport (f i)) →
      embedPlaneTuple y ∈ orderedTube υ σ) →
    ((∀ i, f i ≠ 0) → Pairwise fun i j => Disjoint (tsupport (f i)) (tsupport (f j))) ∧
    ((Pairwise fun i j => Disjoint (tsupport (f i)) (tsupport (f j))) →
      ComplexComponents (fun i => productFunction (f i) (φ i)) ∧
      centeredFnAtProducts S f φ =
        profileIntegral f fun y => orderedFrameKernel S υ σ (embedPlaneTuple y) φ)
def AgreeOnOverlaps (S : ConnFamily) (υ υ' : rightAngleMultiples)
    (σ σ' : Equiv.Perm (Fin (q + 1))) (φ : Fin (q + 1) → realLabels) : Prop :=
  ∀ z ∈ orderedTube υ σ ∩ orderedTube υ' σ',
    orderedFrameKernel S υ σ z φ = orderedFrameKernel S υ' σ' z φ
def UniqueExtension (S : ConnFamily) (φ : Fin (q + 1) → realLabels) : Prop :=
  ExtendsOrderedKernels S φ (unionKernel S φ) ∧
    (∀ K : (Fin (q + 1) → ℂ × ℂ) → ℂ, ExtendsOrderedKernels S φ K →
      ∀ z ∈ orderedTubeUnion q, K z = unionKernel S φ z) ∧
    IsOpen (orderedTubeUnion q) ∧
    HolomorphicOnTuples (orderedTubeUnion q) (unionKernel S φ) ∧
    ∀ z ∈ orderedTubeUnion q,
      IsMultilinearLabels fun ψ : Fin (q + 1) → realLabels => unionKernel S ψ z
def Invariance (S : ConnFamily) (σ : Equiv.Perm (Fin (q + 1)))
    (φ : Fin (q + 1) → realLabels) : Prop :=
  permuteTuple σ '' orderedTubeUnion q = orderedTubeUnion q ∧
    (∀ u : ℂ × ℂ, (fun z => addConstTuple z u) '' orderedTubeUnion q =
      orderedTubeUnion q) ∧
    (∀ s : ℝ, imagBoostTuple s '' orderedTubeUnion q = orderedTubeUnion q) ∧
    ∀ z ∈ orderedTubeUnion q,
      unionKernel S (permuteTuple σ φ) (permuteTuple σ z) = unionKernel S φ z ∧
      ∀ u : ℂ × ℂ, unionKernel S φ (addConstTuple z u) = unionKernel S φ z
def OrderedTuplesCharacterization (θ : openingAngles) (q : ℕ) : Prop :=
  orderedRealTuples q =
      {y | Function.Injective (fun i => y i 0) ∨ Function.Injective (fun i => y i 1)} ∧
    (orderedRealTuples q)ᶜ =
      ⋃ (i : Fin (q + 1)) (j : Fin (q + 1)) (_ : i < j) (k : Fin (q + 1)) (l : Fin (q + 1))
        (_ : k < l), (coincidenceSubspace i j k l : Set (Fin (q + 1) → RealPlane)) ∧
    (∀ i j k l : Fin (q + 1), i < j → k < l →
      Module.finrank ℝ ((Fin (q + 1) → RealPlane) ⧸ coincidenceSubspace i j k l) = 2) ∧
    (∀ (y : Fin (q + 1) → RealPlane) (i j : Fin (q + 1)), i ≠ j → y i = y j →
      y ∈ (orderedRealTuples q)ᶜ) ∧
    orderedRealTuples q ⊆ injectivePointTuples (q + 1) ∧
    (∀ y ∈ injectivePointTuples (q + 1),
      y ∉ orderedRealTuples q ↔ TimesCoincide y ∧ AbscissasCoincide y) ∧
    (∀ y ∈ injectivePointTuples (q + 1), y ∉ orderedRealTuples q →
      ∀ (υ : rightAngleMultiples) (σ : Equiv.Perm (Fin (q + 1))),
        embedPlaneTuple y ∉ orderedTube υ σ) ∧
    IsOpen (orderedRealTuples q) ∧ Dense (orderedRealTuples q) ∧
    IsConnected (orderedRealTuples q) ∧
    (∀ (σ : Equiv.Perm (Fin (q + 1))) (y : Fin (q + 1) → RealPlane),
      y ∈ orderedRealTuples q ↔ permuteTuple σ y ∈ orderedRealTuples q) ∧
    (∀ (u : RealPlane) (y : Fin (q + 1) → RealPlane),
      y ∈ orderedRealTuples q ↔ translateTuple y u ∈ orderedRealTuples q) ∧
    pencilSet θ (q + 1) ⊆ embedPlaneTuple ⁻¹' orderedTube rightAngleZero 1 ∧
    pencilSet θ (q + 1) ⊆ orderedRealTuples q
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S) (q : ℕ), 1 ≤ q →
    ∀ (φ : Fin (q + 1) → realLabels) (υ υ' : rightAngleMultiples)
      (σ σ' : Equiv.Perm (Fin (q + 1))),
      HolomorphicOnTuples (orderedTube υ σ) (fun z => orderedFrameKernel S υ σ z φ) ∧
      StableOpenCone υ σ ∧
      RealLocusOrdered υ σ ∧
      IntegralRepresentation S υ σ φ ∧
      AgreeOnOverlaps S υ υ' σ σ' φ ∧
      UniqueExtension S φ ∧
      Invariance S σ φ ∧
      OrderedTuplesCharacterization d.angle q
end UnionKernel
end EuclideanFunctionals
end YangMills.Construction
end
