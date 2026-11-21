import YangMills.Construction.Analysis.EuclideanNormsConesAndSummableFamilies
import YangMills.Construction.RotationInvariance.RadialBumpsAtALengthAndTheirFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.PlateSmearing
open RealPlane ForwardTube
variable {m : SharpScale} {S : ConnFamily}
def mollifiedProfile (f : RealPlane → ℂ) (ρ : ℕ+ → RealPlane → ℝ) (k : ℕ+) :
    RealPlane → ℂ :=
  RealPlane.convolve f (RealPlane.ofRealFun (ρ k))
def mollifiedProducts {n : ℕ} (f : Fin n → RealPlane → ℂ) (ρ : ℕ+ → RealPlane → ℝ)
    (ψ : Fin n → RealPlane → ℝ) (k : ℕ+) (i : Fin n) : R4 → ℂ :=
  RealPlane.productFunction (mollifiedProfile (f i) ρ k) (ψ i)
def complexDifferences {q : ℕ} (x : Fin (q + 1) → RealPlane) : Fin q → ℂ × ℂ :=
  fun i => ForwardTube.embedPlane (RealPlane.successiveDifferences x i)
def IsSeparatedEnvelope {n : ℕ} (ε : ℝ) (K : Fin n → Set R4)
    (f : Fin n → RealPlane → ℂ) (ρ : ℕ+ → RealPlane → ℝ)
    (ψ : Fin n → RealPlane → ℝ) : Prop :=
  (∀ i, IsCompact (K i)) ∧
    (Pairwise fun k l => ENNReal.ofReal (ε / 2) ≤ Euclidean.euclidSetDist (K k) (K l)) ∧
    ∀ i, supp (RealPlane.productFunction (f i) (ψ i)) ⊆ K i ∧
      ∀ k, supp (mollifiedProducts f ρ ψ k i) ⊆ K i
def MollifiedIdentityAt {q : ℕ} (D : PlaneDataWithAperture m S) (ε : ℝ)
    (f : Fin (q + 1) → RealPlane → ℂ) (ρ : ℕ+ → RealPlane → ℝ)
    (ψ : Fin (q + 1) → RealPlane → ℝ) (k : ℕ+) : Prop :=
  (∀ i, mollifiedProfile (f i) ρ k ∈ RealPlane.complexProfiles) ∧
    (Pairwise fun a c =>
      Disjoint (supp (mollifiedProducts f ρ ψ k a)) (supp (mollifiedProducts f ρ ψ k c))) ∧
    (∀ x : Fin (q + 1) → RealPlane, (∀ i, x i ∈ tsupport (f i)) →
      complexDifferences x ∈ ForwardTube.shiftedForwardTubePow q ε) ∧
    centeredFnFree S (complexTuple (mollifiedProducts f ρ ψ k)) =
      RealPlane.profileIntegral f fun x => D.mollifiedKernel ε ρ ψ k (complexDifferences x)
def PlateSmearingStatement : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (D : PlaneDataWithAperture m S) (q : ℕ), 1 ≤ q →
    ∀ ψ : Fin (q + 1) → RealPlane → ℝ, (∀ i, ψ i ∈ RealPlane.realLabels) →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∀ ρ : ℕ+ → RealPlane → ℝ, D.IsRadialMollifier ε ρ →
    ∀ f : Fin (q + 1) → RealPlane → ℂ, (∀ i, f i ∈ RealPlane.complexProfiles) →
      RealPlane.TimeSeparated ε f →
      (∃ K : Fin (q + 1) → Set R4, IsSeparatedEnvelope ε K f ρ ψ) ∧
        ∀ k : ℕ+, MollifiedIdentityAt D ε f ρ ψ k
end YangMills.Construction.EuclideanFunctionals.PlateSmearing
end
