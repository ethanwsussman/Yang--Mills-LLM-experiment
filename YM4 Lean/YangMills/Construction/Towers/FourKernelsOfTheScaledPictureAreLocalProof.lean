import YangMills.Construction.Towers.FourKernelsOfTheScaledPictureAreLocal
import YangMills.Construction.Towers.HalfPlaquetteTraceKernelOfAFieldIsLocal
import YangMills.Construction.Towers.HessianCurvatureKernelOfAFieldIsLocal
import YangMills.Construction.Towers.ScaledDifferenceKernelOfAFieldIsLocal
import YangMills.Construction.Towers.TransportDefectKernelOfAFieldIsLocal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ScaledKernelsLocal
open PeriodicOperators
open ScaledOperatorFunctions
open EntireDependence
theorem isLocalEntire_of_allRadii {L k : ℕ} {I I' : PeriodicData}
    {T : ((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
    (h : IsLocalAllRadii L k I I' T) : IsLocalEntire L k I I' T :=
  ⟨⟨1, 2 * finestMesh L k, h.1 1 one_pos⟩, h.2⟩
theorem fourKernelsLocal_holds
    (hD : RescaledDifferenceLocality.RescaledDifferenceKernelIsLocal)
    (hE : HolonomyDefectLocality.KernelIsLocal)
    (hz : HalfFaceTraceLocality.HalfFaceTraceKernelIsLocal)
    (hf : CurvatureKernelLocality.CurvatureKernelIsLocal) : FourKernelsLocal :=
  fun L hL k hk => ⟨isLocalEntire_of_allRadii (hD L hL k hk), isLocalEntire_of_allRadii (hE L hL k hk),
    isLocalEntire_of_allRadii (hz L hL k hk), isLocalEntire_of_allRadii (hf L hL k hk)⟩
end YangMills.Construction.Tower.FullSpace.ScaledKernelsLocal
end
