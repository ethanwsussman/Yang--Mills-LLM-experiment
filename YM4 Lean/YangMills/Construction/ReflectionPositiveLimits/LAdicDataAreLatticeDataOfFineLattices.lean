import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.ReflectionPositiveLimits.LAdicNumbersAndLAdicMirrors
import YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
open PeriodicLattice (adicGridPoints meshSize)
open MirrorHyperplanes (MirrorPair)
def NormalMirror.IsMirrorPlaneAt (M : NormalMirror) (a : ℝ) : Prop :=
  ∃ P : MirrorPair a, P.normal = M.normal ∧ P.height = M.offset
namespace FineLatticeAdicData
variable (L : ℕ) (K : ℕ+ → ℕ+)
def AdicGridDenseSubgroup : Prop :=
  (∃ G : AddSubgroup ℝ, (G : Set ℝ) = adicGridPoints L) ∧
    Dense (adicGridPoints L) ∧
    adicGridPoints L = ⋃ j : ℕ+, {x : ℝ | ∃ n : ℤ, x = (n : ℝ) * meshSize L ((K j : ℕ) : ℤ)}
def ScaledLatticesMonotone : Prop :=
  ∀ K₁ K₂ : ℕ+, K₁ ≤ K₂ → scaledLattice L K₁ ≤ scaledLattice L K₂
def AdicGridEventuallyInLattice : Prop :=
  ∀ v : Space, (∀ μ, v μ ∈ adicGridPoints L) →
    ∃ j₀ : ℕ+, ∀ j, j₀ ≤ j → v ∈ scaledLattice L (K j)
def PosAdicEventuallyMeshMultiple : Prop :=
  ∀ t ∈ posAdicGridPoints L,
    ∃ j₀ : ℕ+, ∀ j, j₀ ≤ j →
      ∃ n : ℕ, 0 < n ∧ t / meshSize L ((K j : ℕ) : ℤ) = (n : ℝ)
def AdicMirrorEventuallyLatticeMirror : Prop :=
  ∀ M : NormalMirror, IsAdicMirror L M →
    ∃ j₀ : ℕ+, ∀ j, j₀ ≤ j →
      M.IsMirrorPlaneAt (meshSize L ((K j : ℕ) : ℤ)) ∧
        M.reflectPt '' (scaledLattice L (K j) : Set Space) = scaledLattice L (K j)
def MirrorPairPreservesLattice : Prop :=
  ∀ a : ℝ, 0 < a → ∀ P : MirrorPair a,
    P.reflect.toFun '' (InfiniteLattice.latticeSubgroup a : Set Space) =
      InfiniteLattice.latticeSubgroup a
def AdicDataLatticeData : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ K : ℕ+ → ℕ+, StrictMono K →
    AdicGridDenseSubgroup L K ∧
      ScaledLatticesMonotone L ∧
      AdicGridEventuallyInLattice L K ∧
      PosAdicEventuallyMeshMultiple L K ∧
      AdicMirrorEventuallyLatticeMirror L K ∧
      MirrorPairPreservesLattice
end FineLatticeAdicData
end YangMills.Construction.ReflectionPositivity
