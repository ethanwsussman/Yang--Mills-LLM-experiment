import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
def lowerBy {c : ℝ} (_hc : 0 < c) (F : freeSpanIn {x | c < x 3}) : FreeSep :=
  (EuclidMotion.transl ((-c) • timeVec)).actFree F.1
def loweredNorm {M : SharpScale} {S : ConnFamily} (σ : SymmEuclidFunctional M S) {c : ℝ}
    (hc : 0 < c) (F : freeSpanIn {x | c < x 3}) : ℝ :=
  ‖classOrZero σ.osData.cls (lowerBy hc F)‖
end YangMills.Construction.EuclideanFunctionals
