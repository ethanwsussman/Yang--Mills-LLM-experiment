import YangMills.Construction.Towers.TheFreePropagatorsAndTheirRoots
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.BackgroundFieldResponse
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
def xiInv (L k : ℕ) : KernelMatrix (colourEdges L k 0).Carrier (colourEdges L k 0).Carrier :=
  periodicInverse (colourEdges L k 0) (trivialRescaledOperators L k).Xi
def blockCovariance (L k : ℕ) :
    KernelMatrix (colourEdges L k k).Carrier (colourEdges L k k).Carrier :=
  compKernel (compKernel (trivialRescaledOperators L k).Q (xiInv L k)) (trivialRescaledOperators L k).Qt
def blockCovarianceInv (L k : ℕ) :
    KernelMatrix (colourEdges L k k).Carrier (colourEdges L k k).Carrier :=
  periodicInverse (colourEdges L k k) (blockCovariance L k)
def responseKernel (L k : ℕ) : KernelMatrix (colourEdges L k k).Carrier (colourEdges L k 0).Carrier :=
  compKernel (compKernel (xiInv L k) (trivialRescaledOperators L k).Qt) (blockCovarianceInv L k)
def responseDefect (L k : ℕ) :
    KernelMatrix (colourEdges L k k).Carrier (colourEdges L k k).Carrier :=
  fun ι' ι => blockCovarianceInv L k ι' ι - idKernel (colourEdges L k k) ι' ι
end YangMills.Construction.Tower.BackgroundFieldResponse
end
