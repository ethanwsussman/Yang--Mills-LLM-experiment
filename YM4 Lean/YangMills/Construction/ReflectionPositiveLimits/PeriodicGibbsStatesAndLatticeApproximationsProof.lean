import YangMills.Construction.InfiniteLattice.AllMirrorsOfPeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.LatticeMirrorsAndTwoFormsOfReflectionPositivity
import YangMills.Construction.InfiniteLattice.SpacePlaquettesFunctionsOfPlaquettesAndLatticeIsometries
import YangMills.Construction.ReflectionPositiveLimits.PeriodicGibbsStatesAndLatticeApproximations
import YangMills.Construction.ReflectionPositiveLimits.RepresentativesOfSeparatedTuples
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.PeriodicGibbs
open YangMills.Construction.InfiniteLattice (GaugeField IsPeriodicGibbs LatticeSymmetry LatticeMirror ElementaryPlaquette faceEnergy smearedEnergy)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (MirrorPair)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet)
open YangMills.Construction.LatticeConventions (NormalHyperplane IsAxialNormal IsFaceDiagonalNormal Point)
open YangMills.Construction.LatticeConventions.NormalHyperplane (IsReflectionPositiveAcrossMirror reflectSymmetry)
variable {a : ℝ}
theorem not_isAxialNormal_of_isFaceDiagonalNormal {v : Point} (h₁ : IsAxialNormal v)
    (h₂ : IsFaceDiagonalNormal v) : False := by
  obtain ⟨μ, rfl⟩ := h₁
  obtain ⟨α, κ, hne, h | h⟩ := h₂
  · have hα : (Pi.single μ (1 : ℝ) : Point) α =
        (Pi.single α (1 : ℝ) : Point) α + (Pi.single κ (1 : ℝ) : Point) α := congrFun h α
    have hκ : (Pi.single μ (1 : ℝ) : Point) κ =
        (Pi.single α (1 : ℝ) : Point) κ + (Pi.single κ (1 : ℝ) : Point) κ := congrFun h κ
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at hα
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne.symm] at hκ
    rcases eq_or_ne α μ with rfl | h₃
    · rw [Pi.single_eq_of_ne hne.symm] at hκ
      norm_num at hκ
    · rw [Pi.single_eq_of_ne h₃] at hα
      norm_num at hα
  · have hα : (Pi.single μ (1 : ℝ) : Point) α =
        (Pi.single α (1 : ℝ) : Point) α - (Pi.single κ (1 : ℝ) : Point) α := congrFun h α
    have hκ : (Pi.single μ (1 : ℝ) : Point) κ =
        (Pi.single α (1 : ℝ) : Point) κ - (Pi.single κ (1 : ℝ) : Point) κ := congrFun h κ
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at hα
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne.symm] at hκ
    rcases eq_or_ne α μ with rfl | h₃
    · rw [Pi.single_eq_of_ne hne.symm] at hκ
      norm_num at hκ
    · rw [Pi.single_eq_of_ne h₃] at hα
      norm_num at hα
def toNormalHyperplane (P : MirrorPair a) : NormalHyperplane where
  normal := P.normal
  level := P.height
  normal_valid := by
    rcases P.admissible with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
theorem toNormalHyperplane_isLatticeMirror (P : MirrorPair a) :
    (toNormalHyperplane P).IsLatticeMirror a := by
  constructor
  · intro hc
    rcases P.admissible with ⟨-, q, hq⟩ | ⟨hd, -⟩
    · exact ⟨q, hq⟩
    · exact (not_isAxialNormal_of_isFaceDiagonalNormal hc hd).elim
  · intro hd
    rcases P.admissible with ⟨hc, -⟩ | ⟨-, q, hq⟩
    · exact (not_isAxialNormal_of_isFaceDiagonalNormal hc hd).elim
    · exact ⟨q, hq⟩
theorem reflectSymmetry_toNormalHyperplane (P : MirrorPair a) :
    reflectSymmetry (toNormalHyperplane_isLatticeMirror P) = P.reflect :=
  MirrorHyperplanes.latticeSymmetry_ext (NormalHyperplane.reflect_eq_hyperplaneReflect _)
theorem shiftInvariant_and_reflectionPositive
    (h₁ : InfiniteLattice.PeriodicGibbsSymmetries.Statement)
    (ha : 0 < a) {β : ℝ} (hβ : 0 < β) {ν : Measure (GaugeField a)}
    (hν : IsPeriodicGibbs β ν) :
    InfiniteLattice.IsShiftInvariant ν ∧
      InfiniteLattice.PeriodicGibbsSymmetries.IsReflectionPositiveAtAllMirrors ν := by
  obtain ⟨hm, hc, -⟩ := h₁ a ha β hβ
  refine ⟨?_, (hm ν hν).2⟩
  have h : ν ∈ InfiniteLattice.PeriodicGibbsSymmetries.periodicStates a β := hν
  rw [hc] at h
  exact h.2
theorem reflectionPositive_of_allMirrors
    (h₂ : LatticeConventions.LatticeMirrorsAndReflectionPositivity.Statement)
    (ha : 0 < a) {ν : Measure (GaugeField a)} [IsProbabilityMeasure ν]
    (hp : InfiniteLattice.PeriodicGibbsSymmetries.IsReflectionPositiveAtAllMirrors ν)
    {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a) : IsReflectionPositiveAcrossMirror hQ ν := by
  obtain ⟨-, -, -, -, -, -, hl, -, -⟩ := h₂ ⟨a, ha⟩
  intro F
  have hF : F.1 ∈ {F : GaugeField a → ℂ | InfiniteLattice.IsBoundedObservable F ∧
      InfiniteLattice.IsLocalObservable F ∧
        InfiniteLattice.IsRegionMeasurable Q.upperHalfSpace F} := by
    rw [← hl]
    exact F.2
  have h := (hp Q hQ).2.1 F.1 ⟨hF.1, hF.2.2⟩
  have h' : (0 : ℂ) ≤ NormalHyperplane.reflectionForm hQ ν F F := h
  exact ⟨(Complex.le_def.1 h').2.symm, (Complex.le_def.1 h').1⟩
theorem smearedEnergy_sub_integral
    (h₄ : InfiniteLattice.CutoffStructure.FieldSpaceAndSymmetries)
    (ha : 0 < a) (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] {m : ℝ}
    (hm : ∀ p : ElementaryPlaquette a, ∫ U, faceEnergy U p ∂ν = m) {f : ScalarField}
    (hf : IsCompact (tsupport f)) (U : GaugeField a) :
    smearedEnergy f U - ∫ V, smearedEnergy f V ∂ν =
      ∑ᶠ p : ElementaryPlaquette a, f p.center * (faceEnergy U p - m) := by
  obtain ⟨hs, hp, hc, -⟩ := h₄ a ha
  have : CompactSpace (GaugeField a) := hs.2.2.2.2.2.2.1
  have hfin : {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite :=
    ((hp.2.2 _ hf.isBounded).2).subset fun _ h => subset_tsupport f h
  have hsum : ∀ V : GaugeField a, smearedEnergy f V =
      ∑ p ∈ hfin.toFinset, faceEnergy V p * f p.center := by
    intro V
    refine (finsum_eq_sum_of_support_subset _ fun p hp' => ?_).trans
      (Finset.sum_congr rfl fun _ _ => smul_eq_mul _ _)
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    intro h
    exact hp' (by simp [show f p.center = 0 from h])
  have hint : ∀ p : ElementaryPlaquette a, Integrable (fun V : GaugeField a => faceEnergy V p) ν :=
    fun p => ((hc p).2.2.1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmean : ∫ V, smearedEnergy f V ∂ν = ∑ p ∈ hfin.toFinset, m * f p.center := by
    simp_rw [hsum]
    rw [integral_finsetSum _ fun p _ => (hint p).mul_const _]
    exact Finset.sum_congr rfl fun p _ => by rw [integral_mul_const, hm]
  rw [hmean, hsum U, ← Finset.sum_sub_distrib,
    finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ fun p hp' => ?_]
  · exact Finset.sum_congr rfl fun p _ => by ring
  · rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    intro h
    exact hp' (by simp [show f p.center = 0 from h])
def basePlaquette (a : ℝ) : ElementaryPlaquette a := ⟨0, 0, 1, by decide⟩
theorem reflectionPositive_of_periodicGibbs
    (h₁ : InfiniteLattice.PeriodicGibbsSymmetries.Statement)
    (h₂ : LatticeConventions.LatticeMirrorsAndReflectionPositivity.Statement)
    (ha : 0 < a) {β : ℝ} (hβ : 0 < β) (ν : BorelProb a) (hν : IsPeriodicGibbs β ν.1) :
    ν ∈ reflectionPositiveSet a ∧ InfiniteLattice.IsShiftInvariant ν.1 ∧
      ∀ P : LatticeMirror a, InfiniteLattice.IsReflectionPositiveAt ν.1 P := by
  have : IsProbabilityMeasure ν.1 := ν.2
  obtain ⟨ht, hp⟩ := shiftInvariant_and_reflectionPositive h₁ ha hβ hν
  refine ⟨⟨ht, fun P F _ hF => ?_⟩, ht, fun M => ?_⟩
  · have h := (hp _ (toNormalHyperplane_isLatticeMirror P)).2.1 F hF
    have hr := reflectSymmetry_toNormalHyperplane P
    rw [LatticeConventions.MirrorSideIndependence.reflectedPairing, hr] at h
    exact h
  · obtain ⟨hmir, -, -, -, -, -, -, -, hw⟩ := h₂ ⟨a, ha⟩
    obtain ⟨Q, hQ, hpts⟩ := (hmir M.plane).1 ⟨M, rfl⟩
    exact ((hw Q hQ M hpts.symm ν.1).1).2 (reflectionPositive_of_allMirrors h₂ ha hp hQ)
theorem symmetric_and_centered_of_periodicGibbs
    (h₁ : InfiniteLattice.PeriodicGibbsSymmetries.Statement)
    (h₂ : LatticeConventions.LatticeMirrorsAndReflectionPositivity.Statement)
    (h₃ : LatticeConventions.LatticeSymmetryInvarianceAndEqualFaceMeans)
    (h₄ : InfiniteLattice.CutoffStructure.FieldSpaceAndSymmetries)
    (ha : 0 < a) {β : ℝ} (hβ : 0 < β) (ν : BorelProb a) (hν : IsPeriodicGibbs β ν.1) :
    (∀ r : LatticeSymmetry a, InfiniteLattice.IsSymmetricUnder ν.1 r) ∧
      ∃ m : ℝ, (∀ p : ElementaryPlaquette a, ∫ U, faceEnergy U p ∂ν.1 = m) ∧
        ∀ f ∈ continuousCompact, ∀ U : GaugeField a,
          smearedEnergy f U - ∫ V, smearedEnergy f V ∂ν.1 =
            ∑ᶠ p : ElementaryPlaquette a, f p.center * (faceEnergy U p - m) := by
  have : IsProbabilityMeasure ν.1 := ν.2
  obtain ⟨ht, hp⟩ := shiftInvariant_and_reflectionPositive h₁ ha hβ hν
  obtain ⟨hi, hm⟩ := h₃ ⟨a, ha⟩ ν.1 ht fun Q hQ => reflectionPositive_of_allMirrors h₂ ha hp hQ
  have hmean : ∀ p : ElementaryPlaquette a, ∫ U, faceEnergy U p ∂ν.1 =
      ∫ U, faceEnergy U (basePlaquette a) ∂ν.1 := fun p => hm p _
  exact ⟨hi, _, hmean, fun f hf U => smearedEnergy_sub_integral h₄ ha ν.1 hmean hf.2 U⟩
theorem periodicGibbsTheorem_holds
    (h₁ : InfiniteLattice.PeriodicGibbsSymmetries.Statement)
    (h₂ : LatticeConventions.LatticeMirrorsAndReflectionPositivity.Statement)
    (h₃ : LatticeConventions.LatticeSymmetryInvarianceAndEqualFaceMeans)
    (h₄ : InfiniteLattice.CutoffStructure.FieldSpaceAndSymmetries)
    (h₅ : TupleRepresentatives.Statement) : periodicGibbsTheorem := by
  intro L hL
  have hpos : ∀ K : ℕ+, 0 < PeriodicLattice.meshSize L ((K : ℕ) : ℤ) := fun K => by
    have h : 0 < L := by have := hL.2; omega
    exact zpow_pos (by exact_mod_cast h) _
  have hb : PeriodicGibbsCentered L := fun K β hβ ν hν =>
    symmetric_and_centered_of_periodicGibbs h₁ h₂ h₃ h₄ (hpos K) hβ ν hν
  refine ⟨fun K β hβ ν hν => reflectionPositive_of_periodicGibbs h₁ h₂ (hpos K) hβ ν hν, hb, ?_⟩
  intro K hK β hβ ρ ν hρ hν
  choose hinv m hm hcentre using fun j => hb (K j) (β j) (hβ j) (ν j) (hν j)
  refine ⟨m, hm, ?_⟩
  intro A
  have hrep : ∀ j, (∀ f ∈ continuousCompact, A.smeared j f =
        fun U => smearedEnergy f U - ∫ V, smearedEnergy f V ∂(ν j).1) ∧
      ∀ X : Tuple, A.rep j X = centeredProduct L (K j : ℕ) (ν j) X := by
    intro j
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ := h₅ L hL.1 hL.2 A j
    exact h (ν j) (fun p q => (hm j p).trans (hm j q).symm) fun p => (hm j p).symm
  refine ⟨fun j => (reflectionPositive_of_periodicGibbs h₁ h₂ (hpos (K j)) (hβ j) (ρ j) (hρ j)).1,
    fun j f hf U => congrFun ((hrep j).1 f hf) U, fun j X => (hrep j).2 X, fun σ hσ => ?_⟩
  have e : ∀ (X : Tuple) (j : ℕ+), A.mean j X =
      ∫ U, centeredProduct L (K j : ℕ) (ν j) X U ∂(ρ j).1 := fun X j => by
    rw [LatticeSequence.mean, (hrep j).2 X]
    rfl
  exact ⟨fun h X => (tendsto_congr (e X)).1 (h.2 X),
    fun h => ⟨hσ, fun X => (tendsto_congr (e X)).2 (h X)⟩⟩
end YangMills.Construction.ReflectionPositivity.PeriodicGibbs
