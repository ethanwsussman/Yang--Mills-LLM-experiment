import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
structure JetDomainSymmetries (δ : ℝ) (p : Fin 4 → ℂ) : Prop where
  mem_addShift : ∀ κ ∈ stripAddShift δ p,
    κ ∈ imStrip (2 * δ) ∧ κ + p ∈ imStrip (2 * δ) ∧ -κ - p ∈ stripAddShift δ p
  mem_subShift : ∀ κ ∈ stripSubShift δ p,
    κ ∈ imStrip (2 * δ) ∧ κ - p ∈ imStrip (2 * δ) ∧ -κ + p ∈ stripSubShift δ p
  mem_real : ∀ κ ∈ realDualPoints,
    κ ∈ imStrip (2 * δ) ∩ stripAddShift δ p ∩ stripSubShift δ p ∧ κ - p ∈ stripAddShift δ p ∧
      κ + p ∈ stripSubShift δ p
  neg_image_strip : (fun κ : Fin 4 → ℂ => -κ) '' imStrip (2 * δ) = imStrip (2 * δ)
  neg_image_real : (fun κ : Fin 4 → ℂ => -κ) '' realDualPoints = realDualPoints
structure ProductJetArguments (δ : ℝ) (p : Fin 4 → ℂ) : Prop where
  comp00 : ∀ κ ∈ imStrip (2 * δ), κ ∈ imStrip (2 * δ) ∧ κ ∈ imStrip (2 * δ)
  comp10 : ∀ κ ∈ stripAddShift δ p,
    κ ∈ stripAddShift δ p ∧ κ ∈ imStrip (2 * δ) ∧ κ + p ∈ imStrip (2 * δ) ∧ κ ∈ stripAddShift δ p
  comp01 : ∀ κ ∈ stripSubShift δ p,
    κ ∈ stripSubShift δ p ∧ κ ∈ imStrip (2 * δ) ∧ κ - p ∈ imStrip (2 * δ) ∧ κ ∈ stripSubShift δ p
  comp11 : ∀ κ ∈ realDualPoints,
    κ ∈ realDualPoints ∧ κ ∈ imStrip (2 * δ) ∧ κ ∈ imStrip (2 * δ) ∧ κ ∈ realDualPoints ∧
      κ - p ∈ stripAddShift δ p ∧ κ ∈ stripSubShift δ p ∧ κ + p ∈ stripSubShift δ p ∧
        κ ∈ stripAddShift δ p
structure TransposeJetArguments (δ : ℝ) (p : Fin 4 → ℂ) : Prop where
  comp00 : ∀ κ ∈ imStrip (2 * δ), -κ ∈ imStrip (2 * δ)
  comp10 : ∀ κ ∈ stripAddShift δ p, -κ - p ∈ stripAddShift δ p
  comp01 : ∀ κ ∈ stripSubShift δ p, -κ + p ∈ stripSubShift δ p
  comp11 : ∀ κ ∈ realDualPoints, -κ ∈ realDualPoints
open JetQuad in
def JetArgumentsAndEqualJets : Prop :=
  (∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
    JetDomainSymmetries δ p ∧ ProductJetArguments δ p ∧
      TransposeJetArguments δ p) ∧
  (∀ (δ : ℝ) (p : Fin 4 → ℂ) (I I' : PeriodicData), IsPeriodic I → IsPeriodic I' →
    ∀ T T' : JetQuad I I', IsJet δ p T → IsJet δ p T' → EqAsJet δ p T T' →
      jetNorm δ p T = jetNorm δ p T' ∧
      (∀ z : ℂ, EqAsJet δ p (smul z T) (smul z T')) ∧
      EqAsJet δ p (transposeAt p T) (transposeAt p T') ∧
      (∀ S S' : JetQuad I I', IsJet δ p S → IsJet δ p S' → EqAsJet δ p S S' →
        EqAsJet δ p (add T S) (add T' S')) ∧
      (∀ I'' : PeriodicData, IsPeriodic I'' → ∀ S S' : JetQuad I'' I,
        IsJet δ p S → IsJet δ p S' → EqAsJet δ p S S' →
          EqAsJet δ p (mul p T S) (mul p T' S'))) ∧
  (∀ (δ : ℝ) (p : Fin 4 → ℂ) (I : PeriodicData), IsPeriodic I →
    ∀ T T' : JetQuad I I, IsJet δ p T → IsJet δ p T' → EqAsJet δ p T T' →
      traceNumber T = traceNumber T' ∧
      (IsInvertibleJet δ p T →
        IsInvertibleJet δ p T' ∧
        EqAsJet δ p (zeroPartInv T) (zeroPartInv T') ∧
        EqAsJet δ p (normalize p T) (normalize p T') ∧
        logNumber p T = logNumber p T'))
end YangMills.Construction.PeriodicOperators
end
