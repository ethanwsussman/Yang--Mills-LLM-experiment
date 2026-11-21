import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctional
import Mathlib
set_option autoImplicit false
open YangMills.Construction.EuclideanSpectral
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.SymmEuclidFunctional
variable {c : SharpScale} {S : ConnFamily} (σ : SymmEuclidFunctional c S)
abbrev hilbertSpace : Type := σ.space
abbrev system : OSData σ.hilbertSpace S := σ.osData
def jointSpecMeasure : ProjMeasure σ.hilbertSpace 4 :=
  σ.system.pvm
def SupportsJointSpec (B : BorelSubset 4) : Prop :=
  ProjMeasure.Supports B σ.jointSpecMeasure
end YangMills.Construction.EuclideanFunctionals.SymmEuclidFunctional
