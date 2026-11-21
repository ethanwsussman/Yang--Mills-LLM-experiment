import YangMills.Construction.PeriodicOperators.ExpansionsOfTheComponentsOfAJet
import YangMills.Construction.Towers.AveragesAreBoundedBelowTheRadius
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.LocalizedBackgrounds
def edgeFibre (L k : ℕ) (P : Set (YangMills.Construction.PeriodicOperators.PosEdge L k 0)) :
    Set (YangMills.Construction.Tower.remainderIndex L k).Carrier :=
  {i | i.2 ∈ P}
def LocalizedBackgroundBound : Prop :=
  ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ q ∈ YangMills.Construction.Tower.FullSpace.BackgroundJets.momentumPolydisc
        YangMills.Construction.Tower.FullSpace.BackgroundJets.stripHalfWidth,
    ∀ (μ : Fin 4) (y : YangMills.Construction.InfiniteLattice.AmbientSpace) (r : ℝ), 0 ≤ r →
    ∀ P : Set (YangMills.Construction.PeriodicOperators.PosEdge L k 0),
      (∀ i ∈ edgeFibre L k P, ∀ ν,
          |(YangMills.Construction.Tower.remainderIndex L k).pos i ν - y ν| ≤ r) →
      ∀ C : ℝ, YangMills.Construction.Tower.ResponseProperties.ResponseBound C →
        YangMills.Construction.Tower.FullSpace.SubRadiusMeanBounds.fineFieldNorm L k
            ((edgeFibre L k P).indicator
              (YangMills.Construction.PeriodicOperators.phaseField
                (YangMills.Construction.Tower.remainderIndex L k) q
                (YangMills.Construction.Tower.FullSpace.BackgroundJets.scaledResponseField L k q μ) y)) ≤
          ENNReal.ofReal (Real.exp (4 * YangMills.Construction.Tower.FullSpace.BackgroundJets.stripHalfWidth * r) * C)
end YangMills.Construction.Tower.FullSpace.LocalizedBackgrounds
end
