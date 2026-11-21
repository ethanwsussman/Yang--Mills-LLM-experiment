import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctionalWithReconstruction
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open YangMills.Construction.HilbertSpaceBasics (UnboundedOp)
open YangMills.Construction.BorelSpectral
namespace SpectralPoint
abbrev EMPoints : Set (Fin 4 → ℝ) := univ
abbrev EPlanePoints : Set (Fin 2 → ℝ) := univ
def energyOf (p : EMPoints) : ℝ := p.1 0
def momentumOf (p : EMPoints) : Fin 3 → ℝ := fun j => p.1 j.succ
def dot3 (v q : Fin 3 → ℝ) : ℝ := ∑ j, v j * q j
def dotR4 (v : R4) (q : Fin 3 → ℝ) : ℝ := dot3 (fun j => v j.castSucc) q
def basisVec (j : Fin 3) : Fin 3 → ℝ := Pi.single j 1
theorem measurable_energyOf : Measurable energyOf :=
  (measurable_pi_apply 0).comp measurable_subtype_coe
theorem measurable_momentumOf_apply (j : Fin 3) : Measurable fun p : EMPoints => momentumOf p j :=
  (measurable_pi_apply j.succ).comp measurable_subtype_coe
theorem measurable_dot3_momentumOf (n : Fin 3 → ℝ) :
    Measurable fun p : EMPoints => dot3 n (momentumOf p) :=
  Finset.measurable_fun_sum _ fun j _ => (measurable_momentumOf_apply j).const_mul (n j)
def nonnegEnergy : BorelSubsets EMPoints :=
  ⟨{p | 0 ≤ energyOf p}, measurableSet_le measurable_const measurable_energyOf⟩
def belowAbsMomentum (n : Fin 3 → ℝ) : BorelSubsets EMPoints :=
  ⟨{p | energyOf p < |dot3 n (momentumOf p)|},
    measurableSet_lt measurable_energyOf (measurable_dot3_momentumOf n).abs⟩
def pyramid : BorelSubsets EMPoints :=
  ⟨{p | ∀ j : Fin 3, |momentumOf p j| ≤ energyOf p}, by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le (measurable_momentumOf_apply j).abs measurable_energyOf⟩
def wedge : BorelSubsets EPlanePoints :=
  ⟨{p | |p.1 1| ≤ p.1 0},
    measurableSet_le ((measurable_pi_apply 1).comp measurable_subtype_coe).abs
      ((measurable_pi_apply 0).comp measurable_subtype_coe)⟩
end SpectralPoint
namespace EuclidFunctionalWithRecon
open SpectralPoint
open YangMills.Construction.SpectralTheorem (spectralIntegralOp)
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
def jointMeasure : SpectralMeasure EMPoints σ.space :=
  hamMomMeasure σ.recon.ham σ.recon.mom
def spectralMeasureAt (ψ : σ.space) : Measure EMPoints := σ.jointMeasure.diagMeasure ψ
def planeMeasure : SpectralMeasure EPlanePoints σ.space :=
  YangMills.Construction.ResolvedOps.jointSpectralMeasure (by norm_num)
    ![σ.recon.ham, σ.recon.mom 0]
def dirMomentum (n : Fin 3 → ℝ) : UnboundedOp σ.space :=
  spectralIntegralOp σ.jointMeasure fun p => ((dot3 n (SpectralPoint.momentumOf p) : ℝ) : ℂ)
def HamGeAbsDirMomentum (n : Fin 3 → ℝ) : Prop :=
  σ.jointMeasure (belowAbsMomentum n) = 0
def HamGeAbsMomentum (j : Fin 3) : Prop := σ.HamGeAbsDirMomentum (basisVec j)
def ConeCondition : Prop := σ.HamGeAbsMomentum 0
def borelCalculus (C : BorelSubsets EMPoints) (f : C.1 → ℂ) : UnboundedOp σ.space :=
  σ.jointMeasure.setIntegralOp C f
end EuclidFunctionalWithRecon
end YangMills.Construction.EuclideanFunctionals
