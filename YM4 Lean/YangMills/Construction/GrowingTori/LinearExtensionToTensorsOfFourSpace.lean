import YangMills.Construction.GrowingTori.BoundFunctionsHierarchiesAndCentredMomentsOfFourSpace
import YangMills.Construction.GrowingTori.TensorsAndCentredLatticePolynomials
import Mathlib
noncomputable section
namespace YangMills.Construction.ToriLimits.TensorExtension
open PeriodicSpace
abbrev realTensor (Y : PeriodicSpace.Params) {q : ℕ} (X : Fin q → RealFn) :
    (Fin q → Kind.euclidean.Pt Y) → ℂ :=
  Kind.tensorFn Y Kind.euclidean fun i y => ((X i y : ℝ) : ℂ)
def RespectsTensorRelations (D : TorusTransport.TransportData) (Y : PeriodicSpace.Params) {q : ℕ}
    (Ψ : TestTupleClass.sep.members D.toStandingParameters q → ℝ) : Prop :=
  ∀ (B : Type) [Fintype B] (c : B → ℂ) (X : B → TestTupleClass.sep.members D.toStandingParameters q),
    ∑ b, c b • realTensor Y (X b).1 = 0 → ∑ b, c b * ((Ψ (X b) : ℝ) : ℂ) = 0
def ExistsUniqueLinearExtension (D : TorusTransport.TransportData) (Y : PeriodicSpace.Params) {q : ℕ}
    (Ψ : TestTupleClass.sep.members D.toStandingParameters q → ℝ) : Prop :=
  ∃! T : sepTensorSpanOn Y q Set.univ →ₗ[ℂ] ℂ,
    ∀ X : TestTupleClass.sep.members D.toStandingParameters q,
      ∃ hX : realTensor Y X.1 ∈ sepTensorSpanOn Y q Set.univ,
        T ⟨realTensor Y X.1, hX⟩ = ((Ψ X : ℝ) : ℂ)
def Holds : Prop :=
  ∀ (D : TorusTransport.TransportData) (Y : PeriodicSpace.Params) (q : ℕ) (hq : 1 ≤ q)
    (Ψ : TestTupleClass.sep.members D.toStandingParameters q → ℝ),
    IsClassMultilinear D .sep hq Ψ →
      RespectsTensorRelations D Y Ψ ∧ ExistsUniqueLinearExtension D Y Ψ
end YangMills.Construction.ToriLimits.TensorExtension
end
