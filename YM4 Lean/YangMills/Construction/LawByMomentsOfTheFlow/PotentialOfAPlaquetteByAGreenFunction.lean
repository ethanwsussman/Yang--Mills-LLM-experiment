import YangMills.Construction.FreeKernel.KernelsAndAbbreviationsInFourDimensions
import YangMills.Construction.FreeKernel.UnitLatticeHeatKernel
import YangMills.Construction.LawByMomentsOfTheFlow.CyclicFormulaOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open PeriodicLattice.ShortDistanceTwoPoint
section Sites
variable {R : Type} [CommRing R]
def plaquetteCurlAt (B : (Fin 4 → R) → Fin 4 → ℝ) (x : Fin 4 → R) (a b : Fin 4) : ℝ :=
  B x a + B (x + unitVector a) b - B (x + unitVector b) a - B x b
def greenPlaquettePotential (g : (Fin 4 → R) → ℝ) (y : Fin 4 → R) (c d : Fin 4) : (Fin 4 → R) → Fin 4 → ℝ :=
  fun x μ => (if μ = d then g (x - y - unitVector c) - g (x - y) else 0) -
    (if μ = c then g (x - y - unitVector d) - g (x - y) else 0)
def secondDiffMatrix (g : (Fin 4 → R) → ℝ) (z : Fin 4 → R) (ν ν' : Fin 4) : ℝ :=
  FourDimKernel.mixedSecondDiff ν ν' g z
end Sites
def planePairEntry (D : Fin 4 → Fin 4 → ℝ) (p q : CyclicFormula.OrderedDirectionPair) : ℝ :=
  -(if p.1.2 = q.1.2 then D p.1.1 q.1.1 else 0) + (if p.1.2 = q.1.1 then D p.1.1 q.1.2 else 0) +
    (if p.1.1 = q.1.2 then D p.1.2 q.1.1 else 0) - (if p.1.1 = q.1.1 then D p.1.2 q.1.2 else 0)
def latticeGreen (z : Fin 4 → ℤ) : ℝ :=
  ∫ T in Set.Ioi (0 : ℝ), FreeKernel.UnitLattice.latticeHeatKernel T z
end YangMills.Construction.MomentLaw
end
