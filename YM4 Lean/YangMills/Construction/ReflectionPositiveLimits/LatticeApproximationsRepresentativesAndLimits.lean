import YangMills.Construction.ReflectionPositiveLimits.NormsReflectionsCubesAndLatticesOfFourSpace
import YangMills.Construction.ReflectionPositivity.OneLatticeAtEverySpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
open InfiniteLattice (ElementaryPlaquette faceEnergy smearedEnergy)
open GibbsAtFixedSpacing (BorelProb)
structure LatticeSequence (L : ℕ) where
  level : ℕ+ → ℕ+
  level_strictMono : StrictMono level
  measure : ∀ j, BorelProb (PeriodicLattice.meshSize L ((level j : ℕ) : ℤ))
  shift : ℕ+ → ℝ
namespace LatticeSequence
variable {L : ℕ} (A : LatticeSequence L)
abbrev Fields (j : ℕ+) : Type := GaugeFieldsAtLevel L (A.level j : ℕ)
def smeared (j : ℕ+) (f : ScalarField) (U : A.Fields j) : ℝ :=
  ∑ᶠ p : ElementaryPlaquette (PeriodicLattice.meshSize L ((A.level j : ℕ) : ℤ)),
    f p.center * (faceEnergy U p - A.shift j)
def rep (j : ℕ+) (X : Tuple) : A.Fields j → ℝ :=
  (X.1.map (A.smeared j)).prod
def repComb (j : ℕ+) : TupleComb →ₗ[ℂ] (A.Fields j → ℂ) :=
  Finsupp.linearCombination ℂ fun X U => ((A.rep j X U : ℝ) : ℂ)
theorem repComb_basisOf (j : ℕ+) (X : Tuple) (U : A.Fields j) :
    A.repComb j (basisOf X) U = ((A.rep j X U : ℝ) : ℂ) := by
  simp [repComb, basisOf]
def mean (j : ℕ+) (X : Tuple) : ℝ :=
  ∫ U, A.rep j X U ∂(A.measure j).1
theorem integral_rep (j : ℕ+) (X : Tuple) :
    (A.measure j).integral (fun U => ((A.rep j X U : ℝ) : ℂ)) =
      ((A.mean j X : ℝ) : ℂ) :=
  integral_ofReal
def IsRP : Prop :=
  ∀ j, A.measure j ∈
    LatticeAtSpacing.reflectionPositiveSet (PeriodicLattice.meshSize L ((A.level j : ℕ) : ℤ))
def IsErgodicSeq : Prop :=
  A.IsRP ∧ ∀ j, LatticeAtSpacing.IsErgodicState (A.measure j)
def HasLimit (σ : Tuple → ℝ) : Prop :=
  IsNormalizedFunctional σ ∧ ∀ X, Tendsto (fun j => A.mean j X) atTop (𝓝 (σ X))
end LatticeSequence
def centeredProduct (L K : ℕ) (ρ : BorelProb (PeriodicLattice.meshSize L (K : ℤ))) (X : Tuple) :
    GaugeFieldsAtLevel L K → ℝ :=
  (X.1.map fun f U => smearedEnergy f U - ∫ V, smearedEnergy f V ∂ρ.1).prod
end YangMills.Construction.ReflectionPositivity
