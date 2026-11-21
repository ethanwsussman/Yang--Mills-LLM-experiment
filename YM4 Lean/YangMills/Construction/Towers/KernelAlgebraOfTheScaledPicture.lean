import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
open PeriodicOperators (KernelMatrix applyKernel compKernel unitKernel RowFinite CompSummable)
open RescaledConditions (complementProj gaugeFixedKernel)
namespace RescaledKernelAlgebra
variable {S₀ B₀ S B : Type}
structure FactorsRowFinite (p : RescaledOperators S₀ B₀ S B) : Prop where
  D : RowFinite p.D
  Dt : RowFinite p.Dt
  R : RowFinite p.R
  Rt : RowFinite p.Rt
  H : RowFinite p.H
def gaugeProjection (p : RescaledOperators S₀ B₀ S B) : KernelMatrix (Fin 3 × S₀) (Fin 3 × S₀) :=
  compKernel p.Rt p.R
def gaugeCorrection (p : RescaledOperators S₀ B₀ S B) : KernelMatrix (Fin 3 × B₀) (Fin 3 × B₀) :=
  compKernel (compKernel p.D (complementProj p)) p.Dt
structure ProjectionConsequences (p : RescaledOperators S₀ B₀ S B) : Prop where
  proj_summable : CompSummable p.Rt p.R
  proj_row_finite : RowFinite (gaugeProjection p)
  proj_idem : compKernel (gaugeProjection p) (gaugeProjection p) = gaugeProjection p
  proj_symm : ∀ ι ι', gaugeProjection p ι ι' = gaugeProjection p ι' ι
  complementProj_row_finite : RowFinite (complementProj p)
  comp_assoc : gaugeCorrection p = compKernel p.D (compKernel (complementProj p) p.Dt)
  X_eq : p.X = gaugeFixedKernel p
  correction_symm : ∀ ι ι', gaugeCorrection p ι ι' = gaugeCorrection p ι' ι
  correction_row_finite : RowFinite (gaugeCorrection p)
  pairing_eq : ∀ c : Fin 3 × B₀ → ℂ, PeriodicOperators.HasFiniteSupport c →
    PeriodicOperators.wPairing (meshWeight p.eta) c (applyKernel (gaugeFixedKernel p) c) =
      PeriodicOperators.wPairing (meshWeight p.eta) c (applyKernel p.H c) +
        PeriodicOperators.wPairing (meshWeight p.eta)
          (applyKernel (complementProj p) (applyKernel p.Dt c))
          (applyKernel (complementProj p) (applyKernel p.Dt c))
def Claim : Prop :=
  ∀ (S₀ B₀ S B : Type) (p : RescaledOperators S₀ B₀ S B), 0 < p.eta → 0 < p.coarse →
    FactorsRowFinite p → compKernel p.R p.Rt = unitKernel (Fin 3 × S) → ProjectionConsequences p
end RescaledKernelAlgebra
end Tower
end YangMills.Construction
end
