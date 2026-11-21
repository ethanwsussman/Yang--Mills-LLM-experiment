import YangMills.Construction.InfiniteLattice.ObservablesAndIsometriesAtOneSpacing
import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def FaceEnergyAndExponentialCovariance : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ r : LatticeSymmetry a, r.toFun ∈ affineHyperoctahedralMaps a →
    (∀ p : ElementaryPlaquette a,
      (r.plaquetteMap p).center = r.toFun p.center ∧
      r.actOn (fun U : GaugeField a => faceEnergy U p) =
        (fun U : GaugeField a => faceEnergy U (r.plaquetteMap p)) ∧
      ∀ U : GaugeField a,
        faceEnergy (r.pullbackField U) p = faceEnergy U (r.plaquetteMap p)) ∧
    ∀ v v' : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported v →
      IsBoundedBorelCompactlySupported v' →
      r.actOn (fun U : GaugeField a => Complex.exp (smearedEnergy v U)) =
          (fun U : GaugeField a => Complex.exp (smearedEnergy (r.pushforwardFun v) U)) ∧
      (fun U : GaugeField a => conj (Complex.exp (smearedEnergy v U))) =
          (fun U : GaugeField a => Complex.exp (smearedEnergy (fun x => conj (v x)) U)) ∧
      (fun U : GaugeField a =>
          Complex.exp (smearedEnergy v U) * Complex.exp (smearedEnergy v' U)) =
        (fun U : GaugeField a => Complex.exp (smearedEnergy (v + v') U))
end InfiniteLattice
end YangMills.Construction
end
