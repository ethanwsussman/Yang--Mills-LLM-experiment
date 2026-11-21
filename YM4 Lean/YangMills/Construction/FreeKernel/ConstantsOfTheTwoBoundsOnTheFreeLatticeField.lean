import YangMills.Construction.Lattice.AxisBivectorBasis
import YangMills.Construction.Lattice.BackgroundCurvatureAndTheThreeCovariances
import YangMills.Construction.Lattice.PlaquettesInAxisPlanes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
structure FreeFieldTwoBounds (L : ℕ) (C δ : ℝ) : Prop where
  one_le_const : 1 ≤ C
  rate_mem : δ ∈ Ioc (0 : ℝ) 1
  free_cov_bound : ∀ S : Conventions.StandingParameters, S.L = L →
    ∀ p q : Plaquette S.L S.m ((S.K : ℕ) : ℤ),
    2 * meshSize S.L (S.K : ℕ) ≤ barycenterDist p q →
    barycenterDist p q ≤ torusSide S.L S.m / 4 →
    |freeCurvatureCovariance p q - meshSize S.L (S.K : ℕ) ^ 4 *
        continuumCurvatureKernel p.axisPlane q.axisPlane (barycenterDisplacement p q)| ≤
      C * (meshSize S.L (S.K : ℕ) / barycenterDist p q +
          (barycenterDist p q / torusSide S.L S.m) ^ 4) *
        naturalEntryScale (L := S.L) (m := S.m) (K := S.K) p q
  fluct_cov_bound : ∀ S : Conventions.StandingParameters, S.L = L → ∀ s : ℕ, s ≤ S.K →
    ∀ p q : Plaquette S.L S.m ((S.K : ℕ) : ℤ),
    meshSize S.L (s : ℤ) ≤ barycenterDist p q →
    |fluctuationCurvatureCovariance S s p q| ≤
      C * (meshSize S.L (S.K : ℕ) / meshSize S.L (s : ℤ)) ^ 4 *
        Real.exp (-(δ * (barycenterDist p q / meshSize S.L (s : ℤ))))
def freeFieldConstantPair (L : ℕ) : ℝ × ℝ :=
  Classical.epsilon fun x : ℝ × ℝ => FreeFieldTwoBounds L x.1 x.2
def freeFieldConstant (L : ℕ) : ℝ := (freeFieldConstantPair L).1
def freeFieldRate (L : ℕ) : ℝ := (freeFieldConstantPair L).2
end YangMills.Construction.PeriodicLattice
end
