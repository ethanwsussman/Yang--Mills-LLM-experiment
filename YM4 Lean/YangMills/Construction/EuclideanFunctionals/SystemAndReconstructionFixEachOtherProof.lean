import YangMills.Construction.EuclideanFunctionals.SystemAndReconstructionFixEachOther
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.MutualDetermination
open YangMills.Construction.EuclideanFunctionals.DefinitionComparison
open YangMills.Construction.SettingsComparison (IsSameMeasure)
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] {S : ConnFamily}
theorem projMeasure_ext {G G' : EuclideanSpectral.ProjMeasure ℋ 4}
    (hGG : ∀ B, ⇑(G B) = ⇑(G' B)) : G = G' := by
  have hfun : G.toFun = G'.toFun :=
    funext fun B => LinearMap.ext fun v => congrFun (hGG B) v
  cases G
  cases G'
  cases hfun
  rfl
theorem osData_ext {a b : OSData ℋ S} (hcl : a.cls = b.cls)
    (hpv : a.pvm = b.pvm) (hrot : a.rotOp = b.rotOp) :
    a = b := by
  cases a
  cases b
  cases hcl
  cases hpv
  cases hrot
  rfl
theorem osReconstruction_ext {a b : OSReconstruction ℋ S} (hcl : a.cls = b.cls)
    (hham : a.ham = b.ham) (hmom : a.mom = b.mom)
    (hrot : a.rotOp = b.rotOp) : a = b := by
  cases a
  cases b
  cases hcl
  cases hham
  cases hmom
  cases hrot
  rfl
omit [CompleteSpace ℋ] in
theorem classOrZero_apply_mem (cl : finCombIn upperHalf →ₗ[ℂ] ℋ)
    (F : finCombIn upperHalf) : readClass cl F.1 = cl F := by
  simp [readClass, F.2]
theorem osData_unique {R : OSReconstruction ℋ S} {d d' : OSData ℋ S}
    (hd : Corresponds R d) (hd' : Corresponds R d') : d = d' := by
  refine osData_ext (LinearMap.ext fun F => ?_) (projMeasure_ext fun B => ?_)
    (funext fun w => (hd.rotOp_eq w).symm.trans (hd'.rotOp_eq w))
  · have e := (hd.cls_eq F.1).symm.trans (hd'.cls_eq F.1)
    rwa [classOrZero_of_mem _ F.2, classOrZero_of_mem _ F.2] at e
  · exact (hd.measure_eq B).trans (hd'.measure_eq B).symm
theorem osReconstruction_unique {R R' : OSReconstruction ℋ S} {d : OSData ℋ S}
    (hR : Corresponds R d) (hR' : Corresponds R' d) : R = R' := by
  refine osReconstruction_ext (LinearMap.ext fun F => ?_) (hR.ham_eq.trans hR'.ham_eq.symm)
    (funext fun j => (hR.mom_eq j).trans (hR'.mom_eq j).symm)
    (funext fun w => (hR.rotOp_eq w).trans (hR'.rotOp_eq w).symm)
  have e := (hR.cls_eq F.1).trans (hR'.cls_eq F.1).symm
  rwa [classOrZero_apply_mem, classOrZero_apply_mem] at e
theorem holds_proof : Holds := fun _ _ _ _ _ =>
  ⟨fun _ _ _ hd hd' => osData_unique hd hd', fun _ _ _ hR hR' => osReconstruction_unique hR hR'⟩
end YangMills.Construction.EuclideanFunctionals.MutualDetermination
