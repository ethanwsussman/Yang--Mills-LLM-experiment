import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace PatchFrames
open BlockAverages GaugeMap LatticeFractionalIntegration
variable {F : BlockFrame}
def leadingTransport (S : Finset F.Cell) (V : F.GaugeField F.top) (s s' : F.Site 0) : UnitQuaternion :=
  polarUnit (quaternionPairing S (leadingFrame S V s) (leadingFrame S V s'))
structure IsPatchFrame (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (R : Lattice4 → Lattice4 → UnitQuaternion)
    (Cs r : ℝ) : Prop where
  symm_inv : ∀ a b, R b a = (R a b)⁻¹
  norm_sub_one_le : ∀ a ∈ patchDomain S z, ∀ b ∈ patchDomain S z, (supNorm (b - a) : ℝ) ≤ r * cellSideLength F →
    ‖((R a b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Cs * (supNorm (b - a) / cellSideLength F)
  leadingTransport_eq : ∀ a ∈ patchDomain S z, ∀ b ∈ patchDomain S z, (supNorm (b - a) : ℝ) ≤ r * cellSideLength F →
    leadingTransport S V (patchSite S z a) (patchSite S z b) =
      frameChange S V z (patchSite S z a) * R a b * (frameChange S V z (patchSite S z b))⁻¹
  norm_second_diff_le : 1 ≤ r * cellSideLength F → ∀ a e e' : Lattice4, supNorm e = 1 → supNorm e' = 1 →
    a ∈ patchDomain S z → a + e ∈ patchDomain S z → a + e' ∈ patchDomain S z → a + e' + e ∈ patchDomain S z →
    ‖((R a (a + e) : UnitQuaternion) : ℍ[ℝ]) - ((R (a + e') (a + e' + e) : UnitQuaternion) : ℍ[ℝ])‖ ≤
      Cs / (cellSideLength F : ℝ) ^ 2
def patchFrameExistenceStatement : Prop :=
  ∃ C r c : ℝ, 0 < C ∧ 0 < r ∧ 0 < c ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide →
    IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m → ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c →
      IsCold S F.top s V → ∀ z ∈ S,
        ∃ R : Lattice4 → Lattice4 → UnitQuaternion, IsPatchFrame S V z R (C * s) r
end PatchFrames
end YangMills.Construction
end
