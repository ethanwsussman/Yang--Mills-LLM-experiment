import YangMills.Construction.InfiniteLattice.FrameOfTheLatticeAtASpacing
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAndPlaquettesAtEverySpacing
import YangMills.Construction.ReflectionPositivity.ClassesAndMatrixElementsAtASpacing
import YangMills.Construction.ReflectionPositivity.EnergyMomentumBoundAtCoarseStepsAndInverseSquareLaw
import YangMills.Construction.ReflectionPositivity.WhatIsTakenFromOneLattice
import YangMills.Construction.ReflectionPositivity.ZeroEnergyIsTheInvariantFieldAtASpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet)
open YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare
variable {a : ℝ}
theorem transversePow_natCast (ν : Measure (GaugeField a)) (μ : Fin 4)
    (l : TransverseAxis μ) (k : ℕ) :
    ScaledPair.transversePow ν μ l (k : ℤ) =
      ScaledPair.shiftOp ν μ l ^ k := by
  unfold ScaledPair.transversePow ScaledPair.shiftOp
    ReflectionPair.shiftOp
  rw [zpow_natCast]
  rfl
theorem transversePow_neg_natCast (ν : Measure (GaugeField a)) (μ : Fin 4)
    (l : TransverseAxis μ) (k : ℕ) :
    ScaledPair.transversePow ν μ l (-(k : ℤ)) =
      star (ScaledPair.shiftOp ν μ l) ^ k := by
  unfold ScaledPair.transversePow ScaledPair.shiftOp
    ReflectionPair.shiftOp
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  rfl
theorem energyMomentumOp_eq_sub (ν : BorelProb a) (μ : Fin 4) (l : TransverseAxis μ) (k : ℕ+) :
    ScaledPair.energyMomentumOp ν.1 μ l k =
      energyOpCoarse ν μ k - momentumOpCoarse ν μ l k := by
  unfold ScaledPair.energyMomentumOp energyOpCoarse momentumOpCoarse
  rw [transversePow_natCast, transversePow_neg_natCast]
theorem singleLatticeInputs_holds
    (hMain : CoarseStepsInverseSquare.CombinedBound)
    (hSame : ScaledClassesTheorem)
    (hSpacing : YangMills.Construction.InfiniteLattice.PeriodicGibbsAtEverySpacing.Statement)
    (hFrame : YangMills.Construction.ReflectionPositivity.LatticeAtSpacing.LatticeFrameAtSpacing)
    (hZero : GroundStatesShiftInvariantAtMesh) :
    singleLatticeInputs := by
  intro a ha ν hν
  obtain ⟨hcoarse, hsizes, hlaw⟩ := (hMain a ha).1 ν hν
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F hF s
    exact (hSpacing a ha).2.2.2.1 ν hν s F hF
  · intro μ
    refine ⟨fun F F' lF hF lF' hF' n w hw => ?_, ?_, ?_⟩
    · exact (hSame a ha ν hν μ).2.1.1 F ⟨hF, lF⟩ F' ⟨hF', lF'⟩ n w hw
    · exact (ReflectionPair.site.opFamily (unitRepresentative ν.1) μ).zero_le_A
    · exact (ReflectionPair.site.opFamily (unitRepresentative ν.1) μ).A_le_one
  · intro μ l k
    obtain ⟨hI, hP, -, -, hC⟩ := hcoarse μ l k k.pos
    refine ⟨?_, fun F lF hF => ⟨hP F ⟨hF, lF⟩, ?_⟩⟩
    · rw [energyMomentumOp_eq_sub]
      exact sub_nonneg.mpr hI
    · rw [energyMomentumOp_eq_sub]
      exact hC.2.1 F ⟨hF, lF⟩
  · refine ⟨fun _ => rfl, fun r A hA => ?_⟩
    obtain ⟨-, -, h3, -, h5, -, -⟩ := (hsizes r).2.1 A hA
    have key : ∀ p : Fin 4 × axisReflectionGroup,
        cubeReflectedCorrelation ν p.1 r (axisReflectObs p.2 A) =
          (((cubeReflectedCorrelation ν p.1 r (axisReflectObs p.2 A)).re : ℝ) : ℂ) := by
      intro p
      rw [← (h3 p.1 p.2).2, Complex.ofReal_re]
    refine ⟨fun B hB y hy => ?_, fun B _ => rfl, ⟨?_, ?_⟩, ?_, fun μ γ => ((h3 μ γ).2).symm⟩
    · exact ((hlaw r A hA B hB 0).2.1 y hy).trans_eq (mul_assoc _ _ _).symm
    · obtain ⟨p, hp⟩ := h5.1
      exact ⟨p, (key p).trans (congrArg _ hp)⟩
    · rintro _ ⟨p, rfl⟩
      refine (key p).le.trans (Complex.real_le_real.mpr ?_)
      exact h5.2 ⟨p, rfl⟩
    · obtain ⟨⟨p, hp⟩, -⟩ := isGreatest_scaledCubeReflectionSize ha ν.1 r A
      rw [← hp]
      exact sq_nonneg _
  · intro hE
    have h := ((hFrame a ha).2.2.2.2 ν hE).2 hν.1
    exact ⟨fun B hB => (h B B hB hB).1, fun A B hA hB => (h A B hA hB).2.1⟩
  · intro F hF μ v
    exact (hZero a ha ν hν μ).2.1 F hF v
end YangMills.Construction.ReflectionPositivity.DirectionPictures
