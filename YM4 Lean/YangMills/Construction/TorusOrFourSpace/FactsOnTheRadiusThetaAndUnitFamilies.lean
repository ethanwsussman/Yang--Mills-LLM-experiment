import YangMills.Construction.TorusOrFourSpace.BoundFunctionsAndEffectiveConstants
import YangMills.Construction.TorusOrFourSpace.UnitFamiliesAndTheirNumbers
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
def IsTorusRescaling (D : Params) (F : (Fin 4 → ℝ) → ℝ) (χ : Pt D torus → ℝ) : Prop :=
  ∀ x, χ (quotMap D torus x) = F (D.side⁻¹ • x)
def scaledCenter (D : Params) (z : Fin 4 → ℝ) : Pt D torus :=
  quotMap D torus (D.side • z)
def ThetaNumberGeOne : Prop :=
  ∀ (D : Params) (θ : RadiusRatio) (P : TorusPartitionChoice D θ) (E : Kind),
    thetaNumber P E ∈ Set.Ici (1 : ℝ)
def EffConstFinite : Prop :=
  (∀ (D : Params) (θ : RadiusRatio) (P : TorusPartitionChoice D θ) (E : Kind)
      (C : BoundFamily) (n : ℕ), 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R →
      effConst P E C n d R ∈ Set.Ici (0 : ℝ)) ∧
    (∀ (D : Params) (R : ℝ), 0 < R → R ∈ allowedRadii D euclidean) ∧
    (∀ (D : Params) (θ : RadiusRatio) (P : TorusPartitionChoice D θ) (C : BoundFamily)
      (n : ℕ), 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R →
      effConst P euclidean C n d R = C.val n d R)
def RadiusThetaDependence : Prop :=
  (∀ (D D' : Params) (θ θ' : RadiusRatio),
      ballRadius D θ euclidean = ballRadius D' θ' euclidean) ∧
    (∀ (D D' : Params) (θ : RadiusRatio), D.L = D'.L → D.m = D'.m →
      ballRadius D θ torus = ballRadius D' θ torus) ∧
    (∀ (D D' : Params) (θ θ' : RadiusRatio) (P : TorusPartitionChoice D θ)
      (P' : TorusPartitionChoice D' θ'),
      thetaNumber P euclidean = thetaNumber P' euclidean) ∧
    (∀ (D : Params) (θ θ' : RadiusRatio) (P : TorusPartitionChoice D θ)
      (P' : TorusPartitionChoice D θ') (e : P.Idx ≃ P'.Idx),
      (∀ a, P.bump a = P'.bump (e a)) →
        thetaNumber P torus = thetaNumber P' torus)
def PartitionFromUnitFamily : Prop :=
  ∀ (D : Params) (θ : RadiusRatio) (B : Type) [Fintype B] (X : B → (Fin 4 → ℝ) → ℝ),
    IsPeriodicPartition θ X →
    ∀ (z : B → Fin 4 → ℝ) (ρ : B → ℝ),
      (∀ b, ρ b ∈ Set.Ioo (0 : ℝ) θ.val) →
      (∀ b x, X b x ≠ 0 → ∃ k : Fin 4 → ℤ,
        TorusMetric.euclidNormVec (x - z b - fun μ => (k μ : ℝ)) ≤ ρ b) →
      gradSupBound X ≠ ∞ ∧
      partitionConstant D.M X ≠ ∞ ∧
      (∀ b, ∃! χ : Pt D torus → ℝ, IsTorusRescaling D (X b) χ) ∧
      ∀ χ : B → Pt D torus → ℝ, (∀ b, IsTorusRescaling D (X b) (χ b)) →
        BallsCoverTorus D (fun b => scaledCenter D (z b)) (ballRadius D θ torus) ∧
        IsSubordinatePartitionOfUnity D (fun b => scaledCenter D (z b))
          (ballRadius D θ torus) χ ∧
        (∀ b, supportQ D torus (χ b) ⊆
          torusBall D (scaledCenter D (z b)) (ballRadius D θ torus)) ∧
        (∃ P : TorusPartitionChoice D θ, ∃ c : Fin P.numBalls ≃ B, ∃ e : P.Idx ≃ B,
          (∀ j, P.center j = scaledCenter D (z (c j))) ∧
            ∀ a, P.bump a = χ (e a)) ∧
        (∀ b, ENNReal.ofReal (lipConstQ D torus (χ b)) ≤
          gradSupBound X / ENNReal.ofReal D.side) ∧
        gradSupBound X / ENNReal.ofReal D.side ≤ gradSupBound X ∧
        ENNReal.ofReal (∑ b, (1 + 40 * D.M * lipConstQ D torus (χ b))) ≤
          partitionConstant D.M X ∧
        ∀ P : TorusPartitionChoice D θ, (∃ e : P.Idx ≃ B, ∀ a, P.bump a = χ (e a)) →
          ENNReal.ofReal (thetaNumber P torus) ≤ partitionConstant D.M X
def PeriodicPartitionsExist : Prop :=
  ∀ θ : RadiusRatio, ∃ (B : Type) (_ : Fintype B) (X : B → (Fin 4 → ℝ) → ℝ), IsPeriodicPartition θ X
def RadiusThetaFacts.Claim : Prop :=
  ThetaNumberGeOne ∧ EffConstFinite ∧
    RadiusThetaDependence ∧ PartitionFromUnitFamily ∧
    PeriodicPartitionsExist
end YangMills.Construction.PeriodicSpace
