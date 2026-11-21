import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusTheorem
import YangMills.Construction.SpectralTheory.BoundedBorelCalculus
import YangMills.Construction.SpectralTheory.CommutationWithBoundedIntegrals
import YangMills.Construction.SpectralTheory.EssentialSupportOfSpectralMeasure
import YangMills.Construction.SpectralTheory.KernelAndPositivityOfSpectralIntegrals
import YangMills.Construction.SpectralTheory.MarginalsOfSpectralMeasure
import YangMills.Construction.SpectralTheory.SpectralMeasurePushforwardTheorem
import YangMills.Construction.SpectralTheory.StrongConvergenceOfBoundedIntegrals
import YangMills.Construction.SpectralTheory.UnboundedFunctionalCalculusStatement
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.BorelCalculus
theorem borelCalculusTheorem_of_parts
    (hBounded : SpectralTheory.BoundedBorelCalculus.BoundedBorelCalculusHolds)
    (hStrong : StrongConvergenceHolds)
    (hCommute : SpectralTheory.CommutationWithBoundedIntegrals.CommutesWithBoundedIntegralsHolds)
    (hUnbounded : UnboundedFunctionalCalculusHolds)
    (hKernel : SpectralKernelPositivityTheorem)
    (hPush : SpectralPushforwardTheorem)
    (hSupp : EssSupportHolds)
    (hMarg : MarginalsHold) :
    BorelCalculusTheorem :=
  fun H _ _ _ n =>
    ⟨fun Y E => ⟨hBounded H n Y E, hStrong H n Y E, hCommute H n Y E, hUnbounded H n Y E,
      hKernel H n Y E, hPush H n Y E, hSupp H n Y E⟩, fun E => hMarg H n E⟩
end YangMills.Construction.BorelCalculus
