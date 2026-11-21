import YangMills.Construction.SeparatedSequences.ClassesFramesNormsAndKernels
import YangMills.Construction.SeparatedSequences.SiteSumThresholds
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
noncomputable section
namespace SeparatedClasses
def ApexDistanceBoundsStatement : Prop :=
  ∀ (C : ClassData), C.L ≤ C.blockSize → ∀ Ω ∈ C.separatedClass,
    (∀ y y' : C.Apex Ω,
      ENNReal.ofReal ((C.gapSize : ℝ) * (C.blockSize : ℝ) *
          max (|(y.level : ℝ) - (y'.level : ℝ)| - 1) 0) ≤
        C.chainDist Ω y.point y'.point) ∧
    ∀ a : ℝ, 0 < a →
      (∀ s : ℝ, 0 ≤ s →
        s * Real.log (C.L : ℝ) ≤ a * ((C.gapSize : ℝ) * (C.blockSize : ℝ)) →
        ∀ y y' : C.Apex Ω,
          max (y.mesh / y'.mesh) (y'.mesh / y.mesh) ^ s ≤
            (C.L : ℝ) ^ s * Real.exp (a * (C.chainDist Ω y.point y'.point).toReal)) ∧
      (SeparatedSequences.siteSumThreshold 4 C.L a ≤ (C.gapSize : ℝ) * (C.blockSize : ℝ) →
        ∀ y : C.Apex Ω,
          ∑ᶠ y'' : C.Apex Ω, Real.exp (-a * (C.chainDist Ω y.point y''.point).toReal) ≤
            SeparatedSequences.siteSumMajorant 4 C.L a)
end SeparatedClasses
end
end YangMills.Construction
