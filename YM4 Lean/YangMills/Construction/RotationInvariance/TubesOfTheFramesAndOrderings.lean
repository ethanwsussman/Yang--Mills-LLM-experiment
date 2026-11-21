import YangMills.Construction.RotationInvariance.KernelsOfTheFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace ForwardTube
def complexDifferences {q : ℕ} (z : Fin (q + 1) → ℂ × ℂ) : Fin q → ℂ × ℂ :=
  fun i => z i.succ - z i.castSucc
theorem complexDifferences_embedPlaneTuple {q : ℕ} (x : Fin (q + 1) → RealPlane) :
    complexDifferences (embedPlaneTuple x) = embedPlaneTuple (successiveDifferences x) := by
  funext i
  simp [complexDifferences, embedPlaneTuple, successiveDifferences, embedPlane, Fin.succ,
    Fin.castSucc, Fin.castAdd, Fin.castLE]
def orderedTube (k : rightAngleMultiples) {q : ℕ} (σ : Equiv.Perm (Fin (q + 1))) :
    Set (Fin (q + 1) → ℂ × ℂ) :=
  {z | ∀ i : Fin q, z (σ i.succ) - z (σ i.castSucc) ∈ rotatedForwardTube k}
theorem mem_orderedTube_iff (k : rightAngleMultiples) {q : ℕ}
    (σ : Equiv.Perm (Fin (q + 1))) (z : Fin (q + 1) → ℂ × ℂ) :
    z ∈ orderedTube k σ ↔
      complexDifferences (permuteTuple σ z) ∈ rotatedTubePow k q := by
  simp [orderedTube, rotatedTubePow, complexDifferences, permuteTuple,
    Set.mem_pi]
def orderedTubeUnion (q : ℕ) : Set (Fin (q + 1) → ℂ × ℂ) :=
  ⋃ (k : rightAngleMultiples) (σ : Equiv.Perm (Fin (q + 1))), orderedTube k σ
def orderedRealTuples (q : ℕ) : Set (Fin (q + 1) → RealPlane) :=
  embedPlaneTuple ⁻¹' orderedTubeUnion q
end ForwardTube
namespace EuclideanFunctionals
open ForwardTube
def orderedFrameKernel (F : ConnFamily) (k : rightAngleMultiples) {q : ℕ}
    (σ : Equiv.Perm (Fin (q + 1))) (z : Fin (q + 1) → ℂ × ℂ)
    (a : Fin (q + 1) → realLabels) : ℂ :=
  frameKernel F k (permuteTuple σ a) (complexDifferences (permuteTuple σ z))
theorem orderedFrameKernel_eq (F : ConnFamily) (k : rightAngleMultiples) {q : ℕ}
    (σ : Equiv.Perm (Fin (q + 1))) (z : Fin (q + 1) → ℂ × ℂ)
    (a : Fin (q + 1) → realLabels) :
    orderedFrameKernel F k σ z a =
      planeKernel F (permuteTuple σ a)
        (unrotate k (complexDifferences (permuteTuple σ z))) :=
  rfl
end EuclideanFunctionals
end YangMills.Construction
end
