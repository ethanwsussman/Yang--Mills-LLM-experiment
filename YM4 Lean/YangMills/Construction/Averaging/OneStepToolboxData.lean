import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Lattice.InvertibleContourVariables
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicLattice YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Averaging.OneStep
def halfBlockingFactor (L : ℕ) : ℝ := ((L : ℝ) - 1) / 2
abbrev radiusCeiling (L : ℕ) : ℝ := averagingRadiusCap L
def averagingAtRadius {L m : ℕ} {j j' : ℤ} (U : Bond L m j' → ComplexMatrix2) :
    Bond L m j → ComplexMatrix2 :=
  blockAverage (YangMills.Construction.Averaging.smoothingRadius L) U
structure Parameters (d N L K m : ℕ) (G : Submonoid ComplexMatrix2) : Prop where
  dim_eq : d = 4
  size_eq : N = 2
  group_eq : G = ComplexMatrix2.specialUnitary
  odd_L : Odd L
  thirteen_le_L : 13 ≤ L
  K_pos : 0 < K
  m_pos : 0 < m
namespace Parameters
variable {d N L K m : ℕ} {G : Submonoid ComplexMatrix2}
theorem smoothingRadius_pos (h : Parameters d N L K m G) :
    0 < YangMills.Construction.Averaging.smoothingRadius L :=
  (YangMills.Construction.Averaging.isSmoothingRadius_smoothingRadius h.odd_L h.thirteen_le_L).1
theorem smoothingRadius_le (h : Parameters d N L K m G) :
    YangMills.Construction.Averaging.smoothingRadius L ≤ radiusCeiling L :=
  (YangMills.Construction.Averaging.isSmoothingRadius_smoothingRadius h.odd_L h.thirteen_le_L).2
end Parameters
end YangMills.Construction.Averaging.OneStep
end
