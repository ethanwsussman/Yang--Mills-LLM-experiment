import YangMills.Construction.DirichletOperator.PropagatorOfASequenceOfRegions
import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction
namespace GeneralTorus
namespace GreenBounds
structure LevelUnitChain (L : ℕ) where
  blocking : Blocking.DimFourOddBlockingFactorGeThirteen 4 L
  K : ℕ
  K_pos : 0 < K
  m : ℕ
  m_pos : 0 < m
  t : ℕ
  t_le : t ≤ K
  blockExp : ℕ
  gapExp : ℕ
  L_le_gap : L ≤ L ^ gapExp
  chain : SeparatedChain
    (physicalInLevelUnits L blocking m K t t_le blockExp gapExp)
  choice : BondSetChoice
namespace LevelUnitChain
variable {L : ℕ} (s : LevelUnitChain L)
abbrev data : ScaleData := physicalInLevelUnits L s.blocking s.m s.K s.t s.t_le s.blockExp s.gapExp
def setting : GaugeSetting where
  data := s.data
  chain := s.chain
  L_le_gapCount := s.L_le_gap
  choice := s.choice
  mass := 1
  mass_pos := one_pos
def scales : SeparatedSequences.ScaleData where
  levels := s.K
  top := s.t
  unitLevel := s.t
  blockExp := s.blockExp
  top_le := s.t_le
  unitLevel_le := s.t_le
include s in
theorem cast_blockingFactor_ne_zero : (L : ℝ) ≠ 0 := by
  have := s.blocking.thirteen_le
  exact_mod_cast (by omega : L ≠ 0)
theorem torusSide_ne_zero : s.data.torusSide ≠ 0 := by
  change 2 * (L : ℝ) ^ (s.m + s.K - s.t) ≠ 0
  exact mul_ne_zero two_ne_zero (pow_ne_zero _ s.cast_blockingFactor_ne_zero)
theorem physicalTorusSide_ne_zero : PeriodicLattice.torusSide L s.m ≠ 0 :=
  mul_ne_zero two_ne_zero (pow_ne_zero _ s.cast_blockingFactor_ne_zero)
def dilation : s.data.Space ≃+ PeriodicLattice.FourTorus L s.m :=
  AddEquiv.piCongrRight fun _ =>
    AddCircle.equivAddCircle _ _ s.torusSide_ne_zero s.physicalTorusSide_ne_zero
def baseRegion : Set (PeriodicLattice.FourTorus L s.m) := s.dilation '' s.chain.set 0
def baseRegionBonds : Set (SeparatedSequences.FineBond L s.m s.scales) :=
  {b | b ∈ (PeriodicLattice.bondsMeeting s.baseRegion :
      Set (SeparatedSequences.FineBond L s.m s.scales)) ∧
    b.IsPositivelyOriented}
def Corresponds (c : s.data.BaseBond) (b : SeparatedSequences.FineBond L s.m s.scales) : Prop :=
  s.dilation (c.1.src : s.data.Space) = (b.source : PeriodicLattice.FourTorus L s.m) ∧
    s.dilation (c.1.tgt : s.data.Space) = (b.target : PeriodicLattice.FourTorus L s.m)
open Classical in
def toMatrixBondFun (f : s.data.BaseBond → ℂ) (b : SeparatedSequences.FineBond L s.m s.scales) :
    Matrices.ComplexMatrix2 :=
  if h : ∃ c, s.Corresponds c b then f h.choose • (1 : Matrices.ComplexMatrix2) else 0
def grad (A : s.data.BondField) (x : s.data.BaseSite) (μ ν : Fin 4) : ℝ :=
  s.data.forwardDiff ν (s.data.formComponent μ A) x
def cutoffGrad (ζ : s.data.Space → ℂ) (A : s.data.BondField) (ν : Fin 4)
    (c : s.data.BaseBond) : ℂ :=
  ζ (c.1.src : s.data.Space) * (s.grad A c.1.src (ScaleData.posBondDir c) ν : ℝ)
def cutoffGradSeminorm (α : ℝ) (ζ : s.data.Space → ℂ) (A : s.data.BondField)
    (path : PeriodicLattice.SiteAtLevel L s.m s.scales.levels 0 →
      PeriodicLattice.SiteAtLevel L s.m s.scales.levels 0 →
      List (SeparatedSequences.FineBond L s.m s.scales)) : ℝ≥0∞ :=
  ⨆ ν, SeparatedSequences.bondTransportHolderSeminorm s.scales s.baseRegion s.baseRegionBonds α
    PeriodicLattice.trivialGaugeField path (s.toMatrixBondFun (s.cutoffGrad ζ A ν))
def cutoffSize (α lam : ℝ) (ζ : s.data.Space → ℂ) : ℝ≥0∞ :=
  SeparatedSequences.scaledHolderSeminorm s.scales α lam (ζ ∘ s.dilation.symm) +
    SeparatedSequences.complexSupNorm (ζ ∘ s.dilation.symm)
def IsSmoothSupportedInDoubleCube (y : s.data.Space) (ζ : s.data.Space → ℂ) : Prop :=
  ContDiff ℝ ∞ (ζ ∘ TorusMetric.torusProj s.data.torusSide) ∧
    tsupport ζ ⊆ s.chain.localDoubleCube y
def expDecay (δ : ℝ) (y y' : s.data.Space) : ℝ :=
  Real.exp (-δ * s.chain.scaledDist y y')
end LevelUnitChain
structure GreenConstants where
  rate : ℝ
  bound : ℝ
  blockLower : ℝ
  gapLower : ℝ
  holderBound : ℝ → ℝ
namespace GreenConstants
variable (c : GreenConstants) {L : ℕ}
def AboveLowerBounds (s : LevelUnitChain L) : Prop :=
  c.blockLower ≤ (s.data.blockCount : ℝ) ∧
    c.gapLower ≤ (s.data.gapCount : ℝ) * (s.data.blockCount : ℝ)
structure BoundsAt (s : LevelUnitChain L) (y y' : s.data.Space) (J : ↥s.setting.formSubspace) :
    Prop where
  bond_le : ∀ b ∈ s.setting.bondSet, s.chain.LiesInCell b y →
    |(s.setting.greenOp J).1 b| ≤
      c.bound * s.chain.localSpacing y ^ 2 * s.expDecay c.rate y y' * s.data.bondSupNorm J.1
  grad_le : ∀ x : s.data.BaseSite, (x : s.data.Space) ∈ s.chain.localCube y → ∀ μ ν : Fin 4,
    |s.grad (s.setting.greenOp J).1 x μ ν| ≤
      c.bound * s.chain.localSpacing y * s.expDecay c.rate y y' * s.data.bondSupNorm J.1
  holder_le : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ : s.data.Space → ℂ,
    s.IsSmoothSupportedInDoubleCube y ζ →
    ∀ path, SeparatedSequences.IsGeodesicChoice s.scales path →
      s.cutoffGradSeminorm α ζ (s.setting.greenOp J).1 path ≤
        ENNReal.ofReal (c.holderBound α * s.chain.localSpacing y ^ (1 - α) *
            s.expDecay c.rate y y' * s.data.bondSupNorm J.1) *
          s.cutoffSize α (s.chain.localSpacing y) ζ
structure HoldsFor (s : LevelUnitChain L) : Prop where
  lap_pos : ∀ A : ↥s.setting.formSubspace, A ≠ 0 →
    0 < s.setting.formInner A (s.setting.gaugeLap A)
  lap_isUnit : IsUnit s.setting.gaugeLap
  boundsAt : ∀ y ∈ s.chain.shellSitesUnion, ∀ y' ∈ s.chain.shellSitesUnion,
    ∀ J : ↥s.setting.formSubspace, s.setting.SupportedInCell J y' → c.BoundsAt s y y' J
structure Valid (L : ℕ) : Prop where
  rate_pos : 0 < c.rate
  one_le_bound : 1 ≤ c.bound
  holdsFor : ∀ s : LevelUnitChain L, c.AboveLowerBounds s → c.HoldsFor s
end GreenConstants
def ofPropagator (L : ℕ) (c : Propagator.PropagatorConstants) : GreenConstants :=
  ⟨c.δ, c.B, max c.blockLower L, c.gapLower, c.Bα⟩
def chosen (L : ℕ) : GreenConstants :=
  ofPropagator L (Propagator.SequenceOfRegions.chosenConstants L)
end GreenBounds
def GreenBoundsStatement : Prop :=
  ∀ L : ℕ, Blocking.DimFourOddBlockingFactorGeThirteen 4 L →
    (GreenBounds.chosen L).Valid L
end GeneralTorus
end YangMills.Construction
