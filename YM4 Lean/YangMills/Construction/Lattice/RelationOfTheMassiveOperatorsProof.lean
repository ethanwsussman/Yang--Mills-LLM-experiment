import YangMills.Construction.Lattice.DifferenceOperatorsOfTheBareLattice
import YangMills.Construction.Lattice.ExistenceOfTheOperatorsOfASeparatedSequence
import YangMills.Construction.Lattice.GaugeInvarianceOfTheConditionsOfASequence
import YangMills.Construction.Lattice.KernelOfTheSiteAverageOfASequence
import YangMills.Construction.Lattice.RelationOfTheMassiveOperators
import YangMills.Construction.Lattice.RepresentationOfTheGaugeProjections
import YangMills.Construction.Lattice.SymmetryOfTheDirichletSiteOperators
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators FiniteDimReal
  SeparatedSequences SeparatedSequences.BaseParameters
noncomputable section
namespace SeparatedSequences.MassiveRelation
theorem latticeInner_comm {L t : ℕ} {ι : Type} (u v : ι → ℝ) :
    latticeInner L t u v = latticeInner L t v u := by
  unfold latticeInner
  congr 1
  exact finsum_congr fun i => mul_comm _ _
variable (P : BaseParameters) (Ω : ℕ → Set P.Torus) (φ : BondFrame)
theorem eq_zero_of_inner_eq_zero
    (hp : IsPosDefFor (P.restrictedZeroInner Ω) (P.zeroGreen Ω))
    (h : P.RegionZeroForms Ω) (ho : ∀ g, P.restrictedZeroInner Ω g h = 0) : h = 0 := by
  by_contra hne
  have hpos := hp.2 h hne
  rw [hp.1 h h, ho] at hpos
  exact lt_irrefl _ hpos
end SeparatedSequences.MassiveRelation
end
end YangMills.Construction
