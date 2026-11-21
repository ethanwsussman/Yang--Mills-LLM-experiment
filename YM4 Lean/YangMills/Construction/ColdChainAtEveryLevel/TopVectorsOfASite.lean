import YangMills.Construction.ColdChainAtEveryLevel.ReferenceAndCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def leadingEigenvectorLineStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide → IsAdmissibleAmbient F →
    1024 ≤ m → IsOrthantRegular S m →
    ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V → ∀ x ∈ sitesOfCells S 0,
      (∃ f, IsLeadingEigenvector S V x f) ∧
      ∀ f g, IsLeadingEigenvector S V x f → IsLeadingEigenvector S V x g →
        f (enclosingCell x) ≠ 0 ∧ ∃ q : UnitQuaternion, ∀ y ∈ S, g y = f y * (q : ℍ[ℝ])
end YangMills.Construction.BlockAverages
end
