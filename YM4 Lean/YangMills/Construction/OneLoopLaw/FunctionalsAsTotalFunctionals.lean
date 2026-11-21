import YangMills.Construction.OneLoopLaw.CoefficientOfAFunctional
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.OneLoopLaw.TorusFamilies
open YangMills.Construction.PeriodicOperators.Tempered YangMills.Construction.EffectiveAction
open YangMills.Construction.OneLoopLaw.FunctionalStiffness YangMills.Construction.Conventions
open YangMills.Construction.Matrices
variable {L : ℕ}
def RescaledLatticeIdentification (hL : 0 < L) {K j : ℕ} (hj : j ≤ K) (m : ℕ) : Prop :=
  PeriodicLattice.torusSide L (m + (K - j)) = PeriodicLattice.torusSide L m * (L : ℝ) ^ (K - j) ∧
    PeriodicLattice.torusSide L (m + (K - j)) ∈ PeriodicLattice.torusSides L ∧
    ∀ q : IntPoint,
      siteRescale hL hj m (projectSite L m K j q) = projectSite L (m + (K - j)) 0 0 q
def rescaledForm (hL : 0 < L) {K j : ℕ} (hj : j ≤ K) (m : ℕ)
    (B : PeriodicLattice.BondAtLevel L m K j → ComplexMatrix2) : UnitEdge L (m + (K - j)) → ComplexMatrix2 :=
  B ∘ (bondRescale hL hj m).symm
def TorusPolarizationMatches (hL : 0 < L) {K j : ℕ} (hj : j ≤ K) (F : FieldFamily L) : Prop :=
  ∀ᶠ m in atTop, ∀ B B' : PeriodicLattice.BondAtLevel L m K j → ComplexMatrix2,
    PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra B →
      PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra B' →
        ((torusPolarization (torusFamily hL hj F) m B B' : ℝ) : ℂ) =
          complexHessian F (m + (K - j)) (rescaledForm hL hj m B) (rescaledForm hL hj m B')
def KernelStiffnessIndependent (hL : 0 < L) {K j K' j' : ℕ} (hj : j ≤ K) (hj' : j' ≤ K')
    (F : FieldFamily L) (t : Fin 3 → ComplexMatrix2.LieElement) : Prop :=
  (∀ P, HasKernelLimit t (torusFamily hL hj F) P ↔
    HasKernelLimit t (torusFamily hL hj' F) P) ∧
  ∀ c, IsTorusStiffnessWith t (torusFamily hL hj F) c ↔
    IsTorusStiffnessWith t (torusFamily hL hj' F) c
def TorusFamilyProperties : Prop :=
  ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ (hL : 0 < L) (F : FieldFamily L), IsLatticeFunctional L F →
    (∀ K j : ℕ, 0 < K → ∀ hj : j ≤ K,
      (∀ m : ℕ, 0 < m → RescaledLatticeIdentification hL hj m) ∧
        IsTorusFunctional L K j (torusFamily hL hj F) ∧
        TorusPolarizationMatches hL hj F) ∧
    ∀ K j K' j' : ℕ, 0 < K → 0 < K' → ∀ (hj : j ≤ K) (hj' : j' ≤ K'),
      ∀ t : Fin 3 → ComplexMatrix2.LieElement, Orthonormal ℝ t → KernelStiffnessIndependent hL hj hj' F t
end YangMills.Construction.OneLoopLaw.TorusFamilies
end
