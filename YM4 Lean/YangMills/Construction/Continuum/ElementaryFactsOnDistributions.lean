import YangMills.Construction.Continuum.OrderZeroTestFunctionsOnCoordinateSpacesAndGenerators
import Mathlib
set_option autoImplicit false
open Filter Topology TopologicalSpace YangMills.Construction.ReflectionSpaces.Euclidean
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.DistributionBasics
variable {n : ℕ}
def IsSignedPermMatrix (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ), (∀ k, s k = 1 ∨ s k = -1) ∧
    ∀ i k, P i k = if i = σ k then s k else 0
def signedAffine (P : Matrix (Fin n) (Fin n) ℝ) (b : Coord n) : Coord n → Coord n :=
  fun x => P.mulVec x + b
def IsSeqContinuous {W : Opens (Coord n)} (T : Distribution W) : Prop :=
  ∀ (G : YangMills.Construction.TorusTransport.PositiveNat → testFunctionSpace W)
    (F : testFunctionSpace W),
    TendstoInTest G F → Tendsto (fun t => T.form (G t)) atTop (𝓝 (T.form F))
def RestrictPreservesOrder {W : Opens (Coord n)} (T : Distribution W) : Prop :=
  ∀ (U : Opens (Coord n)) (hU : U ≤ W) (m : ℕ),
    T.HasOrderLE m → (T.restrict hU).HasOrderLE m
def FiniteCombinationsClosed (W : Opens (Coord n)) : Prop :=
  ∀ (ι : Type) (s : Finset ι) (c : ι → ℂ) (T : ι → Distribution W),
    ∃ S : Distribution W, S.form = ∑ i ∈ s, c i • (T i).form
def PreservesSupportNormLimit {V W : Opens (Coord n)} (ψ : Coord n → Coord n)
    (Φ : testFunctionSpace V → testFunctionSpace W) : Prop :=
  Function.Bijective Φ ∧
    (∀ H : testFunctionSpace V,
      tsupport (Φ H : Coord n → ℂ) = ψ ⁻¹' tsupport (H : Coord n → ℂ)) ∧
    (∀ (k : ℕ) (H : testFunctionSpace V),
      cNorm k (Φ H : Coord n → ℂ) = cNorm k (H : Coord n → ℂ)) ∧
    ∀ (G : YangMills.Construction.TorusTransport.PositiveNat → testFunctionSpace V)
      (H : testFunctionSpace V),
      TendstoInTest G H → TendstoInTest (fun t => Φ (G t)) (Φ H)
def TestFunctionPullback (ψ : Coord n → Coord n) (V W : Opens (Coord n)) : Prop :=
  (∃ Φ : testFunctionSpace V →ₗ[ℂ] testFunctionSpace W,
    (∀ H : testFunctionSpace V, (Φ H : Coord n → ℂ) = (H : Coord n → ℂ) ∘ ψ) ∧
      PreservesSupportNormLimit ψ Φ) ∧
  ∃ Φ : testFunctionSpace V →ₛₗ[starRingEnd ℂ] testFunctionSpace W,
    (∀ (H : testFunctionSpace V) (x : Coord n),
      (Φ H : Coord n → ℂ) x = conj ((H : Coord n → ℂ) (ψ x))) ∧
      PreservesSupportNormLimit ψ Φ
def DistributionPullback (ψ : Coord n → Coord n) {W : Opens (Coord n)} (V : Opens (Coord n))
    (T : Distribution W) : Prop :=
  ∃ S : Distribution V,
    (∀ H : testFunctionSpace V, ∃ h : (H : Coord n → ℂ) ∘ ψ ∈ testFunctionSpace W,
      S.form H = T.form ⟨_, h⟩) ∧
    ∀ m : ℕ, T.HasOrderLE m → S.HasOrderLE m
def ElementaryFacts : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ W : Opens (Coord n),
    FiniteCombinationsClosed W ∧
    (∀ T : Distribution W, IsSeqContinuous T ∧ RestrictPreservesOrder T) ∧
    ∀ P : Matrix (Fin n) (Fin n) ℝ, IsSignedPermMatrix P → ∀ b : Coord n,
      IsOpen (signedAffine P b '' (W : Set (Coord n))) ∧
      ∀ V : Opens (Coord n), (V : Set (Coord n)) = signedAffine P b '' (W : Set (Coord n)) →
        TestFunctionPullback (signedAffine P b) V W ∧
        ∀ T : Distribution W, DistributionPullback (signedAffine P b) V T
end YangMills.Construction.DistributionBasics
end
