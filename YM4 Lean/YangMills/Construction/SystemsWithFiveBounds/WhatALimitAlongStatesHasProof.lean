import YangMills.Construction.ChessboardTori.JensenAgainstTheChessboardProof
import YangMills.Construction.InfiniteLattice.ExpectationOfTheObservableInAPeriodicGibbsState
import YangMills.Construction.InfiniteLattice.WhatIsReadOfAPeriodicGibbsState
import YangMills.Construction.ReflectionPositivity.RecentringOfTheLimitOfALatticeApproximation
import YangMills.Construction.ReflectionPositivity.SymmetriesAndMirrorsOfTheLimit
import YangMills.Construction.SystemsWithFiveBounds.ConditionsAtFixedConstantsProof
import YangMills.Construction.SystemsWithFiveBounds.ListOfTheReconstructionOfALimit
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
section Mirrors
variable {a : ℝ}
private theorem latticeSymmetry_ext {s t : LatticeSymmetry a} (h : s.toFun = t.toFun) : s = t := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
private theorem isRegionMeasurable_mono {S T : Set AmbientSpace} (h : S ⊆ T) {A : GaugeField a → ℂ}
    (hA : IsRegionMeasurable S A) : IsRegionMeasurable T A := by apply _root_.YangMills.Construction.ChessboardTori.JensenChessboardBound.isRegionMeasurable_mono <;> assumption
private theorem hyperplaneReflect_neg_neg (n : AmbientSpace) (c : ℝ) :
    hyperplaneReflect (-n) (-c) = hyperplaneReflect n c := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.hyperplaneReflect_neg <;> assumption
private theorem exists_latticeMirror (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror a) :
    ∃ P : LatticeMirror a, P.symmetry.toFun = Q.reflect ∧ Q.upperHalfSpace ∈ P.halfSpaces := by
  have same : ∀ F : ReflectionClass, F.IsAdmissibleLevel a Q.level → F.realNormal = Q.normal →
      ∃ P : LatticeMirror a, P.symmetry.toFun = Q.reflect ∧ Q.upperHalfSpace ∈ P.halfSpaces := by
    intro F h hn
    refine ⟨⟨F, Q.level, h⟩, ?_, Or.inl ?_⟩
    · rw [NormalHyperplane.reflect_eq_hyperplaneReflect]
      show hyperplaneReflect F.realNormal Q.level = _
      rw [hn]
    · show Q.upperHalfSpace = {x | Q.level ≤ F.realNormal ⬝ᵥ x}
      rw [hn]
      rfl
  have opp : ∀ F : ReflectionClass, F.IsAdmissibleLevel a (-Q.level) → F.realNormal = -Q.normal →
      ∃ P : LatticeMirror a, P.symmetry.toFun = Q.reflect ∧ Q.upperHalfSpace ∈ P.halfSpaces := by
    intro F h hn
    refine ⟨⟨F, -Q.level, h⟩, ?_, Or.inr ?_⟩
    · rw [NormalHyperplane.reflect_eq_hyperplaneReflect]
      show hyperplaneReflect F.realNormal (-Q.level) = _
      rw [hn, hyperplaneReflect_neg_neg]
    · show Q.upperHalfSpace = {x | F.realNormal ⬝ᵥ x ≤ -Q.level}
      rw [hn]
      ext x
      simp only [Set.mem_ofPred_eq, neg_dotProduct, neg_le_neg_iff]
      rfl
  rcases Q.normal_valid with ⟨μ, hμ⟩ | ⟨μ, lam, hne, hd | hd⟩
  · obtain ⟨q, hq⟩ := hQ.1 ⟨μ, hμ⟩
    refine same (.axial μ) ⟨q, hq⟩ ?_
    rw [hμ]
    funext κ
    simp [ReflectionClass.realNormal, ReflectionClass.intNormal, LatticeConventions.basisVector,
      Pi.single_apply]
  · obtain ⟨q, hq⟩ := hQ.2 ⟨μ, lam, hne, Or.inl hd⟩
    rcases lt_or_gt_of_ne hne with h | h
    · refine same (.diagonal μ lam h 1) ⟨q, hq⟩ ?_
      rw [hd]
      funext κ
      simp [ReflectionClass.realNormal, ReflectionClass.intNormal, LatticeConventions.basisVector,
        Pi.single_apply]
    · refine same (.diagonal lam μ h 1) ⟨q, hq⟩ ?_
      rw [hd]
      funext κ
      simp [ReflectionClass.realNormal, ReflectionClass.intNormal, LatticeConventions.basisVector,
        Pi.single_apply, add_comm]
  · obtain ⟨q, hq⟩ := hQ.2 ⟨μ, lam, hne, Or.inr hd⟩
    rcases lt_or_gt_of_ne hne with h | h
    · refine same (.diagonal μ lam h (-1)) ⟨q, hq⟩ ?_
      rw [hd]
      funext κ
      simp [ReflectionClass.realNormal, ReflectionClass.intNormal, LatticeConventions.basisVector,
        Pi.single_apply, sub_eq_add_neg]
    · refine opp (.diagonal lam μ h (-1)) ⟨-q, by rw [hq]; push_cast; ring⟩ ?_
      rw [hd]
      funext κ
      simp [ReflectionClass.realNormal, ReflectionClass.intNormal, LatticeConventions.basisVector,
        Pi.single_apply, sub_eq_add_neg]
private theorem isReflectionPositiveAcross_of_mirrors (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (h : ∀ P : LatticeMirror a, ReflectionPositiveAtMirror ν P) (Q : NormalHyperplane)
    (hQ : Q.IsLatticeMirror a) : NormalHyperplane.IsReflectionPositiveAcrossMirror hQ ν := by
  intro F
  obtain ⟨P, hP, hS⟩ := exists_latticeMirror Q hQ
  obtain ⟨B, hB, hF, hm⟩ : ∃ B : Set AmbientSpace, Bornology.IsBounded B ∧ IsBoundedObservable F.1 ∧
      IsRegionMeasurable (Q.upperHalfSpace ∩ B) F.1 := by
    have hmem := F.2
    simp only [localRegionObservables, Set.mem_iUnion] at hmem
    obtain ⟨B, hB, hF⟩ := hmem
    exact ⟨B, hB, hF.1, hF.2⟩
  have hpos := (h P).2 F.1 hF ⟨B, hB, isRegionMeasurable_mono Set.inter_subset_right hm⟩
    ⟨_, hS, isRegionMeasurable_mono Set.inter_subset_left hm⟩
  have he : NormalHyperplane.reflectSymmetry hQ = P.symmetry :=
    latticeSymmetry_ext hP.symm
  have hform : NormalHyperplane.reflectionForm hQ ν F F =
      ∫ U, F.1 U * (starRingEnd ℂ) (P.symmetry.actOn F.1 U) ∂ν := by
    unfold NormalHyperplane.reflectionForm
    rw [he]
    exact integral_congr_ae (Eventually.of_forall fun U => mul_comm _ _)
  rw [hform]
  have hle := Complex.le_def.1 hpos
  exact ⟨hle.2.symm, hle.1⟩
private theorem isShiftInvariant_of_motions (ν : Measure (GaugeField a))
    (h : ∀ r : latticeMotions a, IsSymmetricUnder ν (latticeMotionSymmetry r)) :
    IsShiftInvariant ν := by
  intro v
  have hr : (fun x : AmbientSpace => x + (v : AmbientSpace)) ∈ latticeMotions a :=
    ⟨LinearMap.id, ⟨1, fun κ => Or.inl rfl⟩, v, v.2, fun x => rfl⟩
  have hinv := h ⟨_, hr⟩
  rwa [show latticeMotionSymmetry ⟨_, hr⟩ = shift v from latticeSymmetry_ext rfl] at hinv
end Mirrors
section Observables
variable {a : ℝ}
private theorem finite_centers_ne_zero (ha : 0 < a) {f : AmbientSpace → ℝ} (hf : HasCompactSupport f) :
    {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.finite_center_support <;> assumption
private theorem finsum_mul_sub_eq (ha : 0 < a) {f : AmbientSpace → ℝ} (hf : HasCompactSupport f)
    (U : GaugeField a) (c : ℝ) :
    ∑ᶠ p : ElementaryPlaquette a, f p.center * (faceEnergy U p - c) =
      smearedEnergy f U - c * ∑ᶠ p : ElementaryPlaquette a, f p.center := by
  have hfin := finite_centers_ne_zero ha hf
  have h₁ : (Function.support fun p : ElementaryPlaquette a =>
      faceEnergy U p • f p.center).Finite := by
    refine hfin.subset fun p hp => ?_
    have hp' : faceEnergy U p • f p.center ≠ 0 := hp
    show f p.center ≠ 0
    exact fun h0 => hp' (by simp [h0])
  have h₂ : (Function.support fun p : ElementaryPlaquette a => c * f p.center).Finite := by
    refine hfin.subset fun p hp => ?_
    have hp' : c * f p.center ≠ 0 := hp
    show f p.center ≠ 0
    exact fun h0 => hp' (by simp [h0])
  unfold smearedEnergy
  rw [mul_finsum, ← finsum_sub_distrib h₁ h₂]
  exact finsum_congr fun p => by simp only [smul_eq_mul]; ring
end Observables
private theorem mem_compactTestFunctions {f : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) :
    f ∈ compactTestFunctions := by
  obtain ⟨h₁, h₂, -⟩ := hf
  exact ⟨h₁.continuous.measurable, h₂.exists_bound_of_continuous h₁.continuous, h₂⟩
section OfTheStates
variable {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (Q : CutoffCouplingSequence L)
include hL in
private theorem mesh_pos (j : ℕ+) : 0 < Q.mesh j := by
  have hL' : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 13) hL.2
  exact zpow_pos (by exact_mod_cast hL') _
include hL in
private theorem integral_smearedEnergy (hE : InfiniteLattice.PeriodicGibbsObservableExpectation)
    {j : ℕ+} {ν : Measure (Q.Fields j)}
    (hν : ν ∈ Q.gibbsStates j) {f : AmbientSpace → ℝ} (hf : IsBoundedBorelCompactlySupported f) :
    ∫ U, smearedEnergy f U ∂ν = meanFaceEnergy (L := L) (K := Q.K j) ν *
      ∑ᶠ p : ElementaryPlaquette (Q.mesh j), f p.center := by
  have e := ((hE.1 L (Q.K j) (Q.β j) hL (Q.β_pos j) ν hν).2.2.2 f hf).1
  have e' : ((∫ U, smearedEnergy f U ∂ν : ℝ) : ℂ) =
      ((meanFaceEnergy (L := L) (K := Q.K j) ν *
        ∑ᶠ p : ElementaryPlaquette (Q.mesh j), f p.center : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, Complex.ofReal_mul]
    exact e
  exact_mod_cast e'
include hL in
private theorem statesApproximation_of (hE : InfiniteLattice.PeriodicGibbsObservableExpectation)
    (hS : InfiniteLattice.PeriodicGibbsConsequences.SymmetriesAndConstantFaceMean)
    (ρ ν : ∀ j, Measure (Q.Fields j)) (hρ : ∀ j, ρ j ∈ Q.gibbsStates j)
    (hν : ∀ j, ν j ∈ Q.gibbsStates j) : StatesApproximation Q ρ ν hρ := by
  have hmean : ∀ (j : ℕ+) (p : ElementaryPlaquette (Q.mesh j)), ∫ U, faceEnergy U p ∂ν j =
      meanFaceEnergy (L := L) (K := Q.K j) (ν j) := fun j p =>
    (hE.1 L (Q.K j) (Q.β j) hL (Q.β_pos j) (ν j) (hν j)).2.2.1 p
  have hfield : ∀ (j : ℕ+) (f : AmbientSpace → ℝ), IsBoundedBorelCompactlySupported f →
      ∀ U : Q.Fields j, LatticeApproximation.smearedField (Q.latticeApprox ρ ν hρ) j f U =
        smearedEnergy f U - ∫ V, smearedEnergy f V ∂ν j := by
    intro j f hf U
    rw [integral_smearedEnergy hL Q hE (hν j) hf, ← hmean j (originPlaquette _)]
    refine Eq.trans ?_ (finsum_mul_sub_eq (mesh_pos hL Q j) hf.2.2 U _)
    refine finsum_congr fun p => ?_
    simp only [RCLike.ofReal_real_eq_id, id]
    rfl
  refine ⟨?_, ?_, hfield⟩
  · intro j p
    rw [hmean j p]
    exact (hmean j (originPlaquette _)).symm
  · intro j
    have hSj := hS (Q.mesh j) (mesh_pos hL Q j) (Q.β j) (Q.β_pos j) (ρ j) (hρ j)
    have : IsProbabilityMeasure (ρ j) := (hρ j).1.1
    exact ⟨isShiftInvariant_of_motions _ hSj.1.1, fun H hH =>
      isReflectionPositiveAcross_of_mirrors _ (fun P => (hSj.1.2 P).2) H hH⟩
variable {Q} {ρ ν : ∀ j, Measure (Q.Fields j)} {hρ : ∀ j, ρ j ∈ Q.gibbsStates j}
private theorem hasLimit_latticeApprox (A : StatesApproximation Q ρ ν hρ) {σ : TupleFunctional}
    (hσ : Q.HasLimit ρ ν σ) : ApproxTriple.ConvergesTo (Q.latticeApprox ρ ν hρ) σ := by apply _root_.YangMills.SharedProofs.p60486 <;> assumption
include hL in
private theorem isBoundedForSomeM_latticeApprox
    (hB : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (A : StatesApproximation Q ρ ν hρ) {σ : TupleFunctional} (hσ : Q.HasLimit ρ ν σ) :
    LatticeApproximation.IsBoundedForSomeM (unitAxisMirrorData hL) (Q.latticeApprox ρ ν hρ) :=
  (hB.1 (unitAxisMirrorData hL) (Q.latticeApprox ρ ν hρ) fun X => ⟨σ X, hasLimit_latticeApprox A hσ X⟩).2
end OfTheStates
end WindowLimits
end
end
section
noncomputable section
open Filter MeasureTheory Topology
open scoped ComplexOrder ENNReal InnerProductSpace NNReal
namespace WindowLimits
section TheList
open Filter MeasureTheory InfiniteLattice
open SeparatedTuples hiding conjugation
open ReflectionPositivity.TupleForm SpectralTheory
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass spanClass spaceShift
  timeShift timeBasisVec vacuum)
open ReflectionPositivity.PairMeasureOperators (pairHamiltonian pairMomentum energyMomentumPair)
open LimitConventions (SpaceVec octahedralGroup3 timeExtension)
open HilbertSpaceBasics (IsPosSemidef)
private def linearEquivOfHyperoctahedral (w : TorusTransport.hyperoctahedral) : AmbientSpace ≃ₗ[ℝ] AmbientSpace :=
  { TorusTransport.hyperoctahedralLinear w with
    invFun := w.1.symm
    left_inv := w.1.left_inv
    right_inv := w.1.right_inv }
end TheList
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace WindowLimits
open BoundsOnEverySide TestFunctions
open LimitTheorem
open LimitConventions (cubicMotionGroup)
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
private theorem sharpNormR4_nonneg (M : ℝ) (f : (Fin 4 → ℝ) → ℝ) : 0 ≤ sharpNormR4 M f := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.sharpNormR4_nonneg <;> assumption
private theorem isMotionInvariant_of_group {σ : TupleFunctional}
    (h : ∀ r ∈ cubicMotionGroup, σ.IsInvariant r) (r : Motions.RigidMotion)
    (hr : IsHyperoctahedralMotion r) : IsMotionInvariant σ r := by
  obtain ⟨w, hw⟩ := hr
  have hmem : linearEquivOfHyperoctahedral w ∈ InfiniteLattice.hyperoctahedralLinearGroup :=
    (LimitConventions.mem_hyperoctahedralLinearGroup_iff_toEquiv _).2 w.2
  let g : Equiv.Perm AmbientSpace := (linearEquivOfHyperoctahedral w).toEquiv.trans (Equiv.addRight r.shift)
  have hg : g ∈ cubicMotionGroup := ⟨linearEquivOfHyperoctahedral w, hmem, r.shift, fun x => rfl⟩
  have e : (⇑g : AmbientSpace → AmbientSpace) = r.toFun := by
    funext x
    show w.1 x + r.shift = r.mat.mulVec x + r.shift
    rw [hw x]
  have := h g hg
  rw [e] at this
  exact this
section Riemann
private theorem supNorm_le_euclidNormVec (v : Fin 4 → ℝ) : ‖v‖ ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
private theorem euclidNormVec_le (v : Fin 4 → ℝ) : TorusMetric.euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
private theorem tendsto_realRiemannSum (hE : InfiniteLattice.PeriodicGibbsObservableExpectation)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {f : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) :
    Tendsto (fun J : ℕ => realRiemannSum L J f) atTop (𝓝 ((∫ x, f x : ℝ) : ℂ)) := by
  obtain ⟨h₁, h₂, -⟩ := hf
  obtain ⟨C, hC⟩ := h₁.lipschitzWith_of_hasCompactSupport h₂ one_ne_zero
  have hLip : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f := by
    refine ⟨C, C.2, fun x y => ?_⟩
    have h := hC.dist_le_mul x y
    rw [dist_eq_norm, dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_left (supNorm_le_euclidNormVec _) C.2)
  obtain ⟨r, hr⟩ := h₂.isCompact.isBounded.subset_closedBall (0 : Fin 4 → ℝ)
  have hsupp : TorusCovering.IsSupportedIn f
      (TestFunctions.closedBallR4 (0 : Fin 4 → ℝ) (2 * |r| + 1)) := by
    intro x hx
    have hn : ‖x‖ ≤ r := by simpa using hr hx
    have h2 := euclidNormVec_le (x - 0)
    have h3 : ‖x - 0‖ ≤ |r| := by simpa using hn.trans (le_abs_self r)
    show TorusMetric.euclidNormVec (x - 0) ≤ 2 * |r| + 1
    linarith
  exact (hE.2 L hL f 0 (2 * |r| + 1) (by positivity) hLip hsupp).2
end Riemann
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
private theorem one_le_separationWeightAt (d : ℝ) : 1 ≤ N.separationWeightAt d := le_max_left _ _
private theorem cumulantBound_eq (n : ℕ) (d R : ℝ) :
    N.cumulantBound n d R =
      (N.aStar * N.separationWeightAt d * N.ballConst R) ^ n * (n.factorial : ℝ) ^ N.factorialExponent := rfl
variable {N}
private theorem cumulantBound_le_growthBound (h : N.Admissible) (n : ℕ) (d : ℝ) {R : ℝ} (hR : 0 < R) :
    N.cumulantBound n d R ≤
      N.growthWeightAt d * N.ballConst R ^ n * (n.factorial : ℝ) ^ (N.factorialExponent + 1) := by
  have h₁ := h.aStar_pos
  have h₂ := h.ballConst_pos R hR
  have h₃ : 0 < N.separationWeightAt d := lt_of_lt_of_le one_pos (N.one_le_separationWeightAt d)
  have hc : 0 ≤ N.aStar * N.separationWeightAt d := by positivity
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hp : (N.aStar * N.separationWeightAt d) ^ n ≤ N.growthWeightAt d * (n.factorial : ℝ) := by
    have := Real.pow_div_factorial_le_exp _ hc n
    rwa [div_le_iff₀ hf] at this
  rw [cumulantBound_eq, mul_pow, Real.rpow_add hf, Real.rpow_one]
  have hB : 0 ≤ N.ballConst R ^ n := by positivity
  have hF : 0 ≤ (n.factorial : ℝ) ^ N.factorialExponent := by positivity
  calc (N.aStar * N.separationWeightAt d) ^ n * N.ballConst R ^ n * (n.factorial : ℝ) ^ N.factorialExponent
      ≤ N.growthWeightAt d * (n.factorial : ℝ) * N.ballConst R ^ n * (n.factorial : ℝ) ^ N.factorialExponent :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hB) hF
    _ = _ := by ring
end BoundConstants
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily GibbsStateSequence unitMassBumps)
open WindowLimits
open TestFunctions
open LimitTheorem
open SystemsWithFiveBounds.GibbsLimitInheritance (unitIntegralTestFunctions)
open LimitConventions (cubicMotionGroup)
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
namespace WindowStates
variable {F : StatedSideFamily} (Q : WindowStates F)
private theorem statesApproximation' (hE : InfiniteLattice.PeriodicGibbsObservableExpectation)
    (hS : InfiniteLattice.PeriodicGibbsConsequences.SymmetriesAndConstantFaceMean) :
    StatesApproximation Q.toCutoffCouplingSequence Q.ρ Q.ν Q.ρ_mem :=
  statesApproximation_of F.admissible Q.toCutoffCouplingSequence hE hS Q.ρ Q.ν Q.ρ_mem Q.ν_mem
end WindowStates
section ALimit
variable {F : StatedSideFamily} {N : BoundConstants} (Q : WindowStates F) {σ : TupleFunctional}
private theorem pairedValue_singleton (hM : SmearedObservablesWellDefined)
    (j : ℕ+) (X : SepTupleOfCard 1) :
    Q.toCutoffCouplingSequence.pairedValue Q.ρ Q.ν j ⟨1, X⟩ =
      (∫ U, smearedEnergy (X.1 0) U ∂Q.ρ j) - ∫ U, smearedEnergy (X.1 0) U ∂Q.ν j := by apply _root_.YangMills.SharedProofs.p1691 <;> assumption
private theorem tendsto_K_nat : Tendsto (fun j => ((Q.K j : ℕ+) : ℕ)) atTop atTop := by apply _root_.YangMills.SharedProofs.p107289 <;> assumption
private theorem exists_onePoint_eq (hE : InfiniteLattice.PeriodicGibbsObservableExpectation)
    (hM : SmearedObservablesWellDefined)
    (hσ : Q.HasLimit σ) :
    ∃ c : ℝ, ∀ X : SepTupleOfCard 1, evalOnMap σ ⟨1, X⟩ = c * ∫ x, X.1 0 x := by
  have hL := F.admissible
  let z : ℕ+ → ℂ := fun j =>
    6 * ((refinedSpacing F.L (Q.K j) : ℂ) ^ 4)⁻¹ *
        (meanFaceEnergy (L := F.L) (K := Q.K j) (Q.ρ j) : ℂ) -
      6 * ((refinedSpacing F.L (Q.K j) : ℂ) ^ 4)⁻¹ *
        (meanFaceEnergy (L := F.L) (K := Q.K j) (Q.ν j) : ℂ)
  have hmoment : ∀ (X : SepTupleOfCard 1) (j : ℕ+),
      ((Q.toCutoffCouplingSequence.pairedValue Q.ρ Q.ν j ⟨1, X⟩ : ℝ) : ℂ) =
        z j * realRiemannSum F.L (Q.K j) (X.1 0) := by
    intro X j
    have hT := mem_compactTestFunctions (X.2.1 0)
    have e₁ := (hE.1 F.L (Q.K j) (Q.β j) hL (Q.toCutoffCouplingSequence.β_pos j) (Q.ρ j) (Q.ρ_mem j)).2.2.2 _ hT
    have e₂ := (hE.1 F.L (Q.K j) (Q.β j) hL (Q.toCutoffCouplingSequence.β_pos j) (Q.ν j) (Q.ν_mem j)).2.2.2 _ hT
    rw [pairedValue_singleton Q hM, Complex.ofReal_sub, ← integral_complex_ofReal, ← integral_complex_ofReal]
    refine (congrArg₂ (· - ·) (e₁.1.trans e₁.2) (e₂.1.trans e₂.2)).trans ?_
    simp only [z]
    ring
  have htend : ∀ X : SepTupleOfCard 1,
      Tendsto (fun j => z j * realRiemannSum F.L (Q.K j) (X.1 0)) atTop
        (𝓝 ((evalOnMap σ ⟨1, X⟩ : ℝ) : ℂ)) := fun X =>
    ((Complex.continuous_ofReal.tendsto _).comp (hσ ⟨1, X⟩)).congr fun j => hmoment X j
  have hriem : ∀ X : SepTupleOfCard 1,
      Tendsto (fun j : ℕ+ => realRiemannSum F.L (Q.K j) (X.1 0)) atTop
        (𝓝 ((∫ x, X.1 0 x : ℝ) : ℂ)) := fun X =>
    (tendsto_realRiemannSum hE hL (X.2.1 0)).comp (tendsto_K_nat Q)
  let b : ContDiffBump (0 : Fin 4 → ℝ) := ⟨1, 2, one_pos, by norm_num⟩
  have hstar : b.normed volume ∈
      TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) :=
    ⟨b.contDiff_normed, b.hasCompactSupport_normed, Set.subset_univ _⟩
  have hone : ∫ x, b.normed volume x = 1 := b.integral_normed
  set Xs : SepTupleOfCard 1 := TestSpaces.singletonSepTuple _ hstar with hXs
  have hz : Tendsto z atTop (𝓝 ((evalOnMap σ ⟨1, Xs⟩ : ℝ) : ℂ)) := by
    have h₁ := hriem Xs
    have e₁ : ∫ x, Xs.1 0 x = 1 := hone
    rw [e₁, Complex.ofReal_one] at h₁
    have h₂ := (htend Xs).div h₁ one_ne_zero
    rw [div_one] at h₂
    refine h₂.congr' ?_
    filter_upwards [h₁.eventually (isOpen_ne.mem_nhds (one_ne_zero : (1 : ℂ) ≠ 0))] with j hj
    exact mul_div_cancel_right₀ _ hj
  refine ⟨evalOnMap σ ⟨1, Xs⟩, fun X => ?_⟩
  have h := tendsto_nhds_unique (htend X) (hz.mul (hriem X))
  exact_mod_cast h
private theorem perBallBounds_of_limit (hInh : GibbsLimitInheritance.InheritanceTheorem) (B : BoundsHoldAt F N)
    (hσ : Q.HasLimit σ) (cBar : ℝ) (cl r : SepTuple → SepTuple → ℝ) (E : LawConstants) :
    PerBallBoundsAt F.M ((existentialConstantsAt F.M N cBar cl r).toConditionConstants E) σ := by
  obtain ⟨-, -, hC1, -, -⟩ := hInh.1 F.L F.admissible F.M 0 Q.K Q.ρ Q.ν σ (fun j => (Q.ρ_mem j).1.1) hσ
  refine hC1 _ fun j n hn d hd R hR f hL hb hs => ?_
  have h₀ := B.cumulant_le (Q.K j) (Q.β j) (Q.isFirstPassage j) (Q.ρ j) (Q.ρ_state j) n hn R d hR hd f hL hb hs
  have hq : 0 ≤ ∏ i, sharpNormR4 F.M (f i) :=
    Finset.prod_nonneg fun i _ => sharpNormR4_nonneg _ _
  exact ⟨h₀, h₀.trans (mul_le_mul_of_nonneg_right (BoundConstants.cumulantBound_le_growthBound B.admissible_constants n d hR) hq)⟩
private theorem isSepFunctional_of_limit (hE : InfiniteLattice.PeriodicGibbsObservableExpectation)
    (hS : InfiniteLattice.PeriodicGibbsConsequences.SymmetriesAndConstantFaceMean)
    (hB : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (hR : ReflectionPositivity.LimitCentring.LimitCentringTheorem) (hσ : Q.HasLimit σ) :
    TestSpaces.IsSepFunctional (evalOnMap σ) := by
  have A₀ := Q.statesApproximation' hE hS
  have hl := hasLimit_latticeApprox A₀ hσ
  have hb := isBoundedForSomeM_latticeApprox F.admissible hB A₀ hσ
  have hl' : LimitConventions.ApproxTriple.ConvergesTo
      (Q.toCutoffCouplingSequence.latticeApprox Q.ρ Q.ν Q.ρ_mem)
      (fun X => evalOnMap σ (TupleLists.ofList X)) := by
    have e : (fun X => evalOnMap σ (TupleLists.ofList X)) = ⇑σ := by
      funext X
      unfold evalOnMap
      rw [TupleLists.toList_ofList]
    rw [e]
    exact hl
  obtain ⟨hs, -⟩ := hR.2 (unitAxisMirrorData F.admissible) _ (evalOnMap σ) hb
    A₀.isReflPos hl'
  exact hs
private theorem limitSymmetries_of_limit (hE : InfiniteLattice.PeriodicGibbsObservableExpectation)
    (hS : InfiniteLattice.PeriodicGibbsConsequences.SymmetriesAndConstantFaceMean)
    (hB : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (hF : ReflectionPositivity.LimitSymmetries.LimitHasSymmetries) (hσ : Q.HasLimit σ) :
    WindowLimits.LimitSymmetries σ := by
  have A₀ := Q.statesApproximation' hE hS
  have hl := hasLimit_latticeApprox A₀ hσ
  have hb := isBoundedForSomeM_latticeApprox F.admissible hB A₀ hσ
  obtain ⟨h₀, ⟨h₁, h₂, h₃⟩, ⟨h₄, h₅⟩, h₆⟩ := hF (unitAxisMirrorData F.admissible) _ σ hb
    A₀.isReflPos hl
  exact ⟨h₁, h₂, h₃, isMotionInvariant_of_group h₄, fun M => (h₆ M).2, fun M => (h₅ M).2⟩
private theorem reconstructionProperties_of_limit (hList : LimitReconstructionProperties)
    (hE : InfiniteLattice.PeriodicGibbsObservableExpectation)
    (hS : InfiniteLattice.PeriodicGibbsConsequences.SymmetriesAndConstantFaceMean)
    (hB : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (hσ : Q.HasLimit σ) : ReconstructionProperties σ := by
  have A₀ := Q.statesApproximation' hE hS
  exact hList F.admissible (standingParamsOfFamily F) _ σ (isBoundedForSomeM_latticeApprox F.admissible hB A₀ hσ)
    A₀.isReflPos (hasLimit_latticeApprox A₀ hσ)
end ALimit
end SystemsWithFiveBounds
end
end
noncomputable section
namespace SystemsWithFiveBounds
theorem windowLimitProperties_holds
    (hList : LimitReconstructionProperties)
    (h1 : InfiniteLattice.PeriodicGibbsObservableExpectation)
    (h2 : InfiniteLattice.PeriodicGibbsConsequences.SymmetriesAndConstantFaceMean)
    (h3 : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (h4 : ReflectionPositivity.LimitCentring.LimitCentringTheorem)
    (h5 : ReflectionPositivity.LimitSymmetries.LimitHasSymmetries)
    (h6 : PeriodicGibbsLimits.ObservablesAndMomentsDefined.Statement)
    (h7 : SystemsWithFiveBounds.GibbsLimitInheritance.InheritanceTheorem) :
    WindowLimitProperties :=
  show WindowLimitConditions from
  { approximation := fun Q => Q.statesApproximation' h1 h2
    limit_conditions := fun Q _ hσ =>
      { isSepFunctional := isSepFunctional_of_limit Q h1 h2 h3 h4 hσ
        symmetries := limitSymmetries_of_limit Q h1 h2 h3 h5 hσ
        reconstruction := reconstructionProperties_of_limit Q hList h1 h2 h3 hσ
        onePoint_eq := exists_onePoint_eq Q h1 (smearedObservablesWellDefined_of h6) hσ
        perBall := fun _ B cBar cl r E => perBallBounds_of_limit Q h7 B hσ cBar cl r E } }
end SystemsWithFiveBounds
end
end YangMills.Construction
