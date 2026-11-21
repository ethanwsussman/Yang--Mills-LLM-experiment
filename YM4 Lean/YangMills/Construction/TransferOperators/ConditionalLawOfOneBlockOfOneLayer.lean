import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import YangMills.Construction.InfiniteLattice.WilsonSpecificationOnObservablesVersionsAndTrivialMeasures
import YangMills.Construction.TransferOperators.ConditioningOnAllBondsButOneBlockOfOneLayer
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set InfiniteLattice
namespace TransferOperators
variable {μ : Fin 4}
def Block.sliceDensity (B : Block μ) (β : ℝ)
    (η : ↥(B.thickened \ (B.links : Set (SliceLink μ))) → Matrices.ComplexMatrix2.specialUnitary)
    (w' w v : B.links → Matrices.ComplexMatrix2.specialUnitary) : ℂ :=
  Complex.exp (-B.sliceEnergy β v η) * linkProductKernel β w' v * linkProductKernel β v w
namespace Stack
variable (S : Stack) (B : Block μ)
def densityAt (β : ℝ) (U : GaugeField 1) (j : ℤ)
    (v : B.links → Matrices.ComplexMatrix2.specialUnitary) : ℂ :=
  B.sliceDensity β (S.rimValues B U j) (S.blockValues B U (j - 1))
    (S.blockValues B U (j + 1)) v
theorem localPartition_eq_integral_densityAt (β : ℝ) (U : GaugeField 1) (j : ℤ) :
    S.localPartition B β U j =
      ∫ v : B.links → Matrices.ComplexMatrix2.specialUnitary, S.densityAt B β U j v
        ∂Matrices.ComplexMatrix2.haarPi B.links :=
  rfl
def blockAverage (β : ℝ) (j : ℤ) (F : GaugeField 1 → ℂ) (U : GaugeField 1) : ℂ :=
  1 / S.localPartition B β U j *
    ∫ v : B.links → Matrices.ComplexMatrix2.specialUnitary,
      F (S.withTransported B U j v) * S.densityAt B β U j v
    ∂Matrices.ComplexMatrix2.haarPi B.links
def ReplacementPreservesTransport (j : ℤ) : Prop :=
  ∀ (U : GaugeField 1) (v : B.links → Matrices.ComplexMatrix2.specialUnitary),
    (∀ j' ∈ S.levels, ∀ y : SliceSite μ,
      S.parallelTransport μ (S.withTransported B U j v) j' y = S.parallelTransport μ U j' y) ∧
    (∀ b : B.links, S.transportedLinkVariable μ (S.withTransported B U j v) j b.1 = v b) ∧
    ∀ j' ∈ S.levels, ∀ b' : SliceLink μ, ¬ (j' = j ∧ b' ∈ B.links) →
      S.transportedLinkVariable μ (S.withTransported B U j v) j' b' =
        S.transportedLinkVariable μ U j' b'
def BlockAverageIsCondExp (β : ℝ) (j : ℤ) : Prop :=
  ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
    (∀ U, S.blockAverage B β j F U =
      (B.sliceWindow j).conditionalExpectation zero_lt_one β F U) ∧
    Measurable[B.complementSigma j] (S.blockAverage B β j F) ∧
    ∀ ν ∈ gibbsClass (a := 1) zero_lt_one β,
      ν[F | B.complementSigma j] =ᵐ[ν] S.blockAverage B β j F ∧
      IsCondExpRepresentative ν (B.complementSigma j) F (S.blockAverage B β j F) ∧
      ∫ U, S.blockAverage B β j F U ∂ν = ∫ U, F U ∂ν
def DensitySymmetricInNeighbours (β : ℝ) (j : ℤ) : Prop :=
  (∀ U U' : GaugeField 1, S.rimValues B U j = S.rimValues B U' j →
    S.blockValues B U (j - 1) = S.blockValues B U' (j - 1) →
    S.blockValues B U (j + 1) = S.blockValues B U' (j + 1) →
    S.densityAt B β U j = S.densityAt B β U' j) ∧
  ∀ (η : ↥(B.thickened \ (B.links : Set (SliceLink μ))) → Matrices.ComplexMatrix2.specialUnitary)
    (w' w v : B.links → Matrices.ComplexMatrix2.specialUnitary),
    B.sliceDensity β η w' w v = B.sliceDensity β η w w' v
end Stack
def BlockConditionalLawStatement : Prop :=
  ∀ (μ : Fin 4) (β : ℝ), 0 < β → ∀ (S : Stack) (j : ℤ), S.IsInteriorLevel j → ∀ B : Block μ,
    S.ReplacementPreservesTransport B j ∧
    S.BlockAverageIsCondExp B β j ∧
    S.DensitySymmetricInNeighbours B β j
end TransferOperators
end YangMills.Construction
end
