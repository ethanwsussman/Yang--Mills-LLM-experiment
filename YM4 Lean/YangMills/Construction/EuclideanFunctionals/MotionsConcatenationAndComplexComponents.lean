import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import Mathlib
set_option autoImplicit false
open scoped Pointwise
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.Motions
def mulLeft : List FreeSep → FreeSep
  | [] => toFree []
  | A :: L => L.foldl (fun B C => freeMul B C) A
end YangMills.Construction.EuclideanFunctionals.Motions
