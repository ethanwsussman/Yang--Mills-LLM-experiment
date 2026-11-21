import YangMills.Construction.BoundsOnEverySide.SeparatedLimitsUnderABound
import YangMills.Construction.Continuum.FunctionalsWithAOnePointFunction
import YangMills.Construction.Continuum.GrowthConditionFromAPowerBoundOnSeparatedTuples
import YangMills.Construction.InfiniteLattice.RepresentativeOfATupleAtACutoff
import YangMills.Construction.LimitTheorem.ConstantsOfTheTheoremBehindThereAre
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.LimitAlongPeriodicGibbsStatesIsTheLimitOfABoundedApproximation
import YangMills.Construction.ReflectionPositivity.RateConstantAndRateFunction
import YangMills.Construction.SystemsWithFiveBounds.OnePointOfALimitAtNumbers
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
section
open MeasureTheory Filter InfiniteLattice
open scoped Topology ComplexOrder Matrix
noncomputable section
namespace WindowLimits
open LatticeConventions (NormalHyperplane)
open LimitConventions (ApproxTriple)
open ReflectionPositivity.ApproximatingSequences (LatticeApproximation)
open FirstPassageSeqs (originPlaquette)
open LimitTheorem (evalOnMap)
open SeparatedTuples (TupleFunctional SepTuple)
structure CutoffCouplingSequence (L : ℕ) where
  K : ℕ+ → ℕ+
  tendsto_K : Tendsto K atTop atTop
  β : ℕ+ → ℝ
  β_pos : ∀ j, 0 < β j
namespace CutoffCouplingSequence
variable {L : ℕ} (Q : CutoffCouplingSequence L)
abbrev mesh (j : ℕ+) : ℝ := PeriodicLattice.meshSize L ((Q.K j : ℕ) : ℤ)
abbrev Fields (j : ℕ+) : Type := GaugeField (Q.mesh j)
abbrev gibbsStates (j : ℕ+) : Set (Measure (Q.Fields j)) :=
  periodicGibbsSet L (Q.K j) (Q.β j)
def pairedValue (ρ ν : ∀ j, Measure (Q.Fields j)) (j : ℕ+) (X : TestSpaces.SepTuple) : ℝ :=
  ∫ U, CutoffRepresentative.centredProduct L (Q.K j) (ν j) X U ∂ρ j
def HasLimit (ρ ν : ∀ j, Measure (Q.Fields j)) (σ : TupleFunctional) : Prop :=
  ∀ X, Tendsto (fun j => Q.pairedValue ρ ν j X) atTop (𝓝 (evalOnMap σ X))
def meanFaceEnergy (ν : ∀ j, Measure (Q.Fields j)) (j : ℕ+) : ℝ :=
  ∫ U, faceEnergy U (originPlaquette (Q.mesh j)) ∂ν j
def latticeApprox (ρ ν : ∀ j, Measure (Q.Fields j)) (hρ : ∀ j, ρ j ∈ Q.gibbsStates j) :
    ApproxTriple L where
  cutoff := Q.K
  tendsto_cutoff := Q.tendsto_K
  state := ρ
  isProbabilityMeasure_state j := (hρ j).1.1
  offset := Q.meanFaceEnergy ν
end CutoffCouplingSequence
abbrev unitAxisMirrorData {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) :
    ReflectionPositivity.AxisMirror.MirrorData where
  L := L
  isAdmissible := hL
  K := 1
  m := 1
  β := 1
  β_pos := one_pos
section OfTheStates
variable {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (Q : CutoffCouplingSequence L)
structure StatesApproximation (ρ ν : ∀ j, Measure (Q.Fields j))
    (hρ : ∀ j, ρ j ∈ Q.gibbsStates j) : Prop where
  meanFaceEnergy_eq : ∀ (j : ℕ+) (p : ElementaryPlaquette (Q.mesh j)),
    ∫ U, faceEnergy U p ∂ν j = Q.meanFaceEnergy ν j
  isReflPos : ApproxTriple.IsReflPos (Q.latticeApprox ρ ν hρ)
  smearedField_eq : ∀ (j : ℕ+) (f : AmbientSpace → ℝ), IsBoundedBorelCompactlySupported f →
    ∀ U : Q.Fields j,
    LatticeApproximation.smearedField (Q.latticeApprox ρ ν hρ) j f U =
      smearedEnergy f U - ∫ V, smearedEnergy f V ∂ν j
variable {Q} {ρ ν : ∀ j, Measure (Q.Fields j)} {hρ : ∀ j, ρ j ∈ Q.gibbsStates j}
end OfTheStates
end WindowLimits
end
end
section
noncomputable section
open Filter MeasureTheory Topology
open scoped ComplexOrder ENNReal InnerProductSpace NNReal
namespace WindowLimits
section Neighbourhoods
open Metric
open TorusMetric TimeAxis
open InfiniteLattice (AmbientSpace)
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
end Neighbourhoods
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace WindowLimits
open LimitConventions (cubicMotionGroup)
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
section ALimit
variable    {σ : TupleFunctional}
structure LimitSymmetries (σ : TupleFunctional) : Prop where
  isPermInvariant : σ.IsPermInvariant
  isEntrywiseLinear : σ.IsEntrywiseLinear
  isAdmissiblyContinuous : σ.IsAdmissiblyContinuous
  motion_invariant : ∀ r, _root_.YangMills.Construction.LimitTheorem.IsHyperoctahedralMotion r → _root_.YangMills.Construction.LimitTheorem.IsMotionInvariant σ r
  reflectionPositive : ∀ M : Mirrors.ReflectingHyperplane, σ.IsReflectionPositive M
  reflection_invariant : ∀ M : Mirrors.ReflectingHyperplane, σ.IsInvariant M.reflect
end ALimit
end WindowLimits
end
end
section
open Set
noncomputable section
namespace SystemsWithFiveBounds
open SeparatedTuples (SepTuple)
open LimitTheorem (ExistentialConstants)
namespace BoundConstants
variable (N : BoundConstants)
def separationWeightAt (d : ℝ) : ℝ := max 1 (d ^ (-(N.sepExponent : ℤ)))
def growthWeightAt (d : ℝ) : ℝ := Real.exp (N.aStar * N.separationWeightAt d)
end BoundConstants
def existentialConstantsAt (M : ℝ) (N : BoundConstants) (cBar : ℝ) (cl r : SepTuple → SepTuple → ℝ) :
    ExistentialConstants where
  perBall := fun n d R => N.cumulantBound n d R
  A := fun d _ => N.growthWeightAt d
  B := N.ballConst
  κStar := N.factorialExponent + 1
  kE := 10 + N.sepExponent
  cE := 1 + 2 * SeparatedBound.extFactorAbs
  CE := TestSpaces.onePointConst (10 + N.sepExponent)
    (SeparatedPowerBound.powerBase M N.sepExponent (N.aStar * N.ballConst 1)) cBar
  κ := 20 + N.factorialExponent
  clusterConst := cl
  clusterRadius := r
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily)
open Probability (IsBoundedRealRV)
open LimitTheorem (evalOnMap)
open WindowLimits
open TestFunctions
open SeparatedTuples (TupleFunctional)
def standingParamsOfFamily (F : StatedSideFamily) : Conventions.StandingParameters := ⟨F.L, F.admissible, 1, 1⟩
def blockWeight (N : BoundConstants) (d R : ℝ) {n : ℕ} (J : Finset (Fin n)) : ℝ :=
  if J.card = 1 then N.onePointConst R else N.cumulantBound J.card d R
def momentWeight (N : BoundConstants) (n : ℕ) (d R : ℝ) : ℝ :=
  ∑ π : SetPartition.Partitions (Finset.univ : Finset (Fin n)), ∏ J ∈ π.parts, blockWeight N d R J
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily GibbsStateSequence unitMassBumps)
open LimitConventions (cubicMotionGroup)
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
open WindowLimits
open TestFunctions
open LimitTheorem
structure WindowStates (F : StatedSideFamily) where
  K : ℕ+ → ℕ+
  tendsto_K : Tendsto K atTop atTop
  β : ℕ+ → ℝ
  isFirstPassage : ∀ j, F.IsFirstPassage (K j) (β j)
  ρ : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize F.L ((K j : ℕ) : ℤ)))
  ν : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize F.L ((K j : ℕ) : ℤ)))
  ρ_mem : ∀ j, ρ j ∈ periodicGibbsSet F.L (K j) (β j)
  ν_mem : ∀ j, ν j ∈ periodicGibbsSet F.L (K j) (β j)
  ρ_state : ∀ j, ρ j ∈ F.stateSet F.L (K j) (β j)
  ν_state : ∀ j, ν j ∈ F.stateSet F.L (K j) (β j)
namespace WindowStates
variable {F : StatedSideFamily} (Q : WindowStates F)
@[reducible] def toCutoffCouplingSequence : CutoffCouplingSequence F.L :=
  ⟨Q.K, Q.tendsto_K, Q.β, fun j => F.pos_of_isFirstPassage _ _ (Q.isFirstPassage j)⟩
def HasLimit (σ : TupleFunctional) : Prop := Q.toCutoffCouplingSequence.HasLimit Q.ρ Q.ν σ
end WindowStates
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace WindowLimits
open BoundsOnEverySide TestFunctions
open LimitTheorem
open BoundsOnEverySide TestFunctions
open LimitTheorem
open SeparatedTuples (TupleFunctional SepTuple IsDisjointlySupported RealValued)
open TestSpaces (SepTupleOfCard)
open Probability (IsBoundedRealRV)
section Neighbourhoods
open Metric TorusMetric
theorem exists_open_nbhds_separated_bounded {k : ℕ} (K : Fin k → Set AmbientSpace)
    (hc : ∀ i, IsCompact (K i)) (hd : ∀ i l, i ≠ l → Disjoint (K i) (K l)) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∃ O : Fin k → Set AmbientSpace, (∀ i, IsOpen (O i)) ∧ (∀ i, K i ⊆ O i) ∧
      (∀ i l, i ≠ l → ∀ x ∈ O i, ∀ y ∈ O l, δ ≤ euclidNormVec (x - y)) ∧
      ∀ i, ∀ x ∈ O i, euclidNormVec x ≤ R := by
  have e₁ : ∀ i l, ∀ᶠ ε in 𝓝[>] (0 : ℝ), i ≠ l → Disjoint (thickening ε (K i)) (thickening ε (K l)) := by
    intro i l
    by_cases hil : i = l
    · exact Eventually.of_forall fun _ h => absurd hil h
    · obtain ⟨δ, hδ, hdis⟩ := (hd i l hil).exists_thickenings (hc i) (hc l).isClosed
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε _
      exact hdis.mono (thickening_mono hε.2.le _) (thickening_mono hε.2.le _)
  have e₃ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, h₁, hε⟩ := ((eventually_all.2 fun i => eventually_all.2 (e₁ i)).and e₃).exists
  have hδ : 0 < ε / 2 := half_pos hε
  have hb : Bornology.IsBounded (⋃ i, thickening (ε / 2) (K i)) :=
    Bornology.isBounded_iUnion.2 fun i => (hc i).isBounded.thickening
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  have hC' : ∀ i, ∀ x ∈ thickening (ε / 2) (K i), euclidNormVec x ≤ 2 * |C| + 1 := by
    intro i x hx
    have hn := hC x (Set.mem_iUnion.2 ⟨i, hx⟩)
    have hcoord : ∀ μ, x μ ^ 2 ≤ |C| ^ 2 := fun μ => by
      rw [← sq_abs (x μ)]
      have : |x μ| ≤ |C| := ((norm_le_pi_norm x μ).trans hn).trans (le_abs_self C)
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [Fin.sum_univ_four]
    nlinarith [hcoord 0, hcoord 1, hcoord 2, hcoord 3, abs_nonneg C]
  refine ⟨ε / 2, 2 * |C| + 1, hδ, by positivity, fun i => thickening (ε / 2) (K i),
    fun i => isOpen_thickening, fun i => self_subset_thickening hδ _, ?_, hC'⟩
  intro i l hil x hx y hy
  by_contra hlt
  rw [not_le] at hlt
  have hxy : dist x y < ε / 2 := (dist_pi_lt_iff hδ).2 fun μ => by
    rw [Real.dist_eq]
    exact (abs_apply_le_euclidNormVec (x - y) μ).trans_lt hlt
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.1 hy
  obtain ⟨w, hw, hxw⟩ := mem_thickening_iff.1 hx
  have a₁ : x ∈ thickening ε (K i) := mem_thickening_iff.2 ⟨w, hw, by linarith⟩
  have a₂ : x ∈ thickening ε (K l) := mem_thickening_iff.2 ⟨z, hz, by linarith [dist_triangle x y z]⟩
  exact Set.disjoint_left.1 (h₁ i l hil) a₁ a₂
end Neighbourhoods
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace WindowLimits
open SeparatedTuples (TupleFunctional SepTuple RealValued)
open TestSpaces (SepTupleOfCard)
open TorusMetric (euclidNormVec)
open TestFunctions (closedBallR4 setDistR4 sharpNormR4 HasSeparatedSupportsR4)
open BoundsOnEverySide
open LimitTheorem
theorem exists_support_ball_and_gap (X : SepTuple) : ∃ d R : ℝ, 0 < d ∧ 0 < R ∧
    (∀ f ∈ X.1, tsupport f ⊆ closedBallR4 0 R) ∧
    X.1.Pairwise fun f g => ENNReal.ofReal d ≤ setDistR4 (tsupport f) (tsupport g) := by
  have hd : ∀ i l : Fin X.1.length, i ≠ l → Disjoint (tsupport (X.1.get i)) (tsupport (X.1.get l)) := by
    intro i l hil
    rcases lt_or_gt_of_ne hil with hlt | hlt
    · exact List.pairwise_iff_get.1 X.2.2 i l hlt
    · exact (List.pairwise_iff_get.1 X.2.2 l i hlt).symm
  obtain ⟨δ, R, hδ, hR, O, -, hKO, h₂, h₃⟩ := exists_open_nbhds_separated_bounded
    (fun i : Fin X.1.length => tsupport (X.1.get i)) (fun i => (X.2.1 _ (List.get_mem _ _)).2) hd
  refine ⟨δ, R, hδ, hR, fun f hf x hx => ?_, List.pairwise_iff_get.2 fun i l hil => ?_⟩
  · obtain ⟨i, rfl⟩ := List.get_of_mem hf
    show euclidNormVec (x - 0) ≤ R
    rw [sub_zero]
    exact h₃ i x (hKO i hx)
  · exact le_iInf₂ fun x hx => le_iInf₂ fun y hy =>
      ENNReal.ofReal_le_ofReal (h₂ i l hil.ne x (hKO i hx) y (hKO l hy))
def supportGapOf (X : SepTuple) : ℝ := (exists_support_ball_and_gap X).choose
def supportRadiusOf (X : SepTuple) : ℝ := (exists_support_ball_and_gap X).choose_spec.choose
def enclosingSideOf (X Y : SepTuple) : ℕ :=
  ⌈supportRadiusOf X + supportRadiusOf Y + supportGapOf X + supportGapOf Y⌉₊ + 1
def clusteringRadiusOf (X Y : SepTuple) : ℝ := 8 * (enclosingSideOf X Y : ℝ)
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily)
open SeparatedTuples (TupleFunctional SepTuple RealValued)
open TestSpaces (SepTupleOfCard)
open TorusMetric (euclidNormVec)
open TestFunctions (closedBallR4 setDistR4 sharpNormR4 HasSeparatedSupportsR4)
open WindowLimits
open LimitTheorem
def sizeWeight (M : ℝ) (N : BoundConstants) (X : SepTuple) : ℝ :=
  |momentWeight N (X.1.length + X.1.length) (supportGapOf X) (supportRadiusOf X)| *
    ((X.1.map (sharpNormR4 M)).prod) ^ 2
def clusteringConstOf (M : ℝ) (N : BoundConstants) (X Y : SepTuple) : ℝ :=
  1 + 32 * |SmearingFilter.spectralRateConst| * (enclosingSideOf X Y : ℝ) ^ 2 *
    √(sizeWeight M N X) * √(sizeWeight M N Y)
abbrev existentialConstants (M : ℝ) (N : BoundConstants) : ExistentialConstants :=
  existentialConstantsAt M N (unitBallBound M N) (clusteringConstOf M N) clusteringRadiusOf
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace WindowLimits
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
open BoundsOnEverySide TestFunctions
open LimitTheorem
def connectedFamilyOf (s₀ : Conventions.StandingParameters) (σ : TestSpaces.SepTuple → ℝ) :
    AmbientPoints.TupleMapFamily s₀ .euclidean := fun n _ f =>
  TestSpaces.cumulant σ ⟨f.1, (AmbientPoints.mem_separatedTuples_r4_iff f.1).1 f.2⟩
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily)
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
section ALimit
variable {F : StatedSideFamily} {N : BoundConstants} (Q : WindowStates F) {σ : TupleFunctional}
def WindowStates.toGibbsStateSequence : BoundsOnEverySide.GibbsStateSequence F.L := ⟨Q.K, Q.β, Q.ρ, Q.ρ_mem⟩
end ALimit
end SystemsWithFiveBounds
end
end
end YangMills.Construction
