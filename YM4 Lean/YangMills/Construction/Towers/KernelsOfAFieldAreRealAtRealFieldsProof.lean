import YangMills.Construction.Lattice.OrthonormalCoordinatesOfFunctionsOnBonds
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometriesProof
import YangMills.Construction.Towers.IsometryCovarianceOfTheCovariantAveragesOnTheWholeLatticeProof
import YangMills.Construction.Towers.KernelsFieldsAndPropertiesOfTheTwoOperators
import YangMills.Construction.Towers.TransposesOfTheCovariantDifferenceAndOfTheDifferences
import Mathlib
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAndTheTwoDeterminants
set_option autoImplicit false

section
open Set
noncomputable section
namespace YangMills.Construction.Tower.RealFieldKernels
open TwoOperators (realCoeffs)
open CovDiffTransposes (matrixKernel)
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ ζ ∈ realCoeffs L,
    FullSpace.expField ζ ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.compactGaugeGroup ∧
    (∀ ι' ι, (matrixKernel (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.edgePauliCoordinates L 0 0)
      (FullSpace.covDiff (FullSpace.expField ζ)) ι' ι).im = 0) ∧
    ∀ ι' ι, (FullSpace.complexHessianKernel (FullSpace.expField ζ) ι' ι).im = 0
end YangMills.Construction.Tower.RealFieldKernels
end
end

open Set
noncomputable section
namespace YangMills.Construction.Tower.RealFieldKernels
open Matrices (ComplexMatrix2)
open TwoOperators (realCoeffs)
open CovDiffTransposes (matrixKernel)
open BondFunctions.Coordinates (pauliFamily_mem_hermitianTraceless)
private theorem meshAt_zero_ne_zero (L : ℕ) : meshAt L 0 0 ≠ 0 := by
  simp [meshAt]
private theorem not_isPositivelyOriented_opposite {a : ℝ} (ha : a ≠ 0)
    {b : InfiniteLattice.Link a} (h : b.IsPositivelyOriented) :
    ¬b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.PolydiscSmoothing.not_opposite_isPositivelyOriented <;> assumption
private theorem isPositivelyOriented_opposite_of_not {a : ℝ} {b : InfiniteLattice.Link a}
    (h : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
private theorem pauliCoeff_im_eq_zero {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) (a : Fin 3) :
    (pauliCoeff a X).im = 0 := by
  obtain ⟨hh, ht⟩ := id hX
  have hs : X ∈ ComplexMatrix2.traceless := ht
  have h₁₀ : X 1 0 = star (X 0 1) := congrFun (congrFun hh 1) 0
  have h₀₀ : X 0 0 = star (X 0 0) := congrFun (congrFun hh 0) 0
  have hi : (X 0 0).im = 0 := by
    have := congrArg Complex.im h₀₀
    simp at this
    linarith
  rw [pauliCoeff, dif_pos hs]
  fin_cases a
  · simp [OneLoop.pauliCoordinateEquiv, h₁₀]
  · simp [OneLoop.pauliCoordinateEquiv, h₁₀, Complex.div_im]
  · simpa [OneLoop.pauliCoordinateEquiv] using hi
abbrev _root_.YangMills.SharedProofs.p23717 := @pauliCoeff_im_eq_zero
private theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
private theorem matExp_I_smul_mem {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
private theorem expField_mem {L : ℕ}
    {ζ : (PeriodicOperators.colourEdges L 0 0).Carrier → ℂ} (hζ : ζ ∈ realCoeffs L) :
    FullSpace.expField ζ ∈
      FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.compactGaugeGroup := by
  classical
  obtain ⟨hv, hr⟩ : (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs ζ ∈
      FullSpace.edgeFormSpace (meshAt L 0 0) := hζ
  set A := (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs ζ with hA
  have pos : ∀ {b : FullSpace.Edge L 0 0}, b.IsPositivelyOriented →
      FullSpace.expField ζ b = ComplexMatrix2.matExp (Complex.I • A b) := by
    intro b h
    simp [FullSpace.expField, FullSpace.expTwist, h, hA]
  have neg : ∀ {b : FullSpace.Edge L 0 0}, ¬b.IsPositivelyOriented →
      FullSpace.expField ζ b = (ComplexMatrix2.matExp (Complex.I • A b.opposite))⁻¹ := by
    intro b h
    simp [FullSpace.expField, FullSpace.expTwist, h, hA]
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases h : b.IsPositivelyOriented
    · rw [pos h]
      exact matExp_I_smul_mem (hv b h)
    · have hb := hv _ (isPositivelyOriented_opposite_of_not h)
      rw [neg h, matExp_inv, ← smul_neg]
      exact matExp_I_smul_mem (ComplexMatrix2.hermitianTraceless.neg_mem hb)
  · by_cases h : b.IsPositivelyOriented
    · rw [neg (not_isPositivelyOriented_opposite (meshAt_zero_ne_zero L) h), pos h]
      rfl
    · rw [pos (isPositivelyOriented_opposite_of_not h), neg h, matExp_inv, matExp_inv, neg_neg]
private theorem ofPauliCoeffs_mem_of_zero_or_one {σ : Type} {c : Fin 3 × σ → ℂ}
    (hc : ∀ κ, c κ = 0 ∨ c κ = 1) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.hermitianTraceless := by
  refine ComplexMatrix2.hermitianTraceless.sum_mem fun a _ => ?_
  rcases hc (a, x) with h | h
  · simp [h, ComplexMatrix2.hermitianTraceless.zero_mem]
  · simpa [h] using pauliFamily_mem_hermitianTraceless a
private theorem extendOddly_of_positive {a : ℝ} (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (h : b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_of_pos <;> assumption
private theorem covDiff_of_positive {a : ℝ} (U : InfiniteLattice.Link a → ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2) {b : InfiniteLattice.Link a}
    (h : b.IsPositivelyOriented) :
    FullSpace.covDiff U l b = ComplexMatrix2.conjugateBy (U b) (l b.terminal) - l b.initial :=
  extendOddly_of_positive _ h
private theorem covDiff_mem_of_positive {a : ℝ} {U : InfiniteLattice.Link a → ComplexMatrix2}
    (hU : ∀ b, U b ∈ PeriodicLattice.compactGaugeGroup)
    {c : Fin 3 × InfiniteLattice.LatticePoint a → ℂ}
    (hc : ∀ κ, c κ = 0 ∨ c κ = 1) {b : InfiniteLattice.Link a} (h : b.IsPositivelyOriented) :
    FullSpace.covDiff U (ofPauliCoeffs c) b ∈ ComplexMatrix2.hermitianTraceless := by
  rw [covDiff_of_positive _ _ h]
  exact ComplexMatrix2.hermitianTraceless.sub_mem
    (ComplexMatrix2.conjugateBy_mem_hermitianTraceless (hU _) _
      (ofPauliCoeffs_mem_of_zero_or_one hc _))
    (ofPauliCoeffs_mem_of_zero_or_one hc _)
private theorem extendOddly_opposite {a : ℝ} (ha : a ≠ 0)
    (f : InfiniteLattice.Link a → ComplexMatrix2) (b : InfiniteLattice.Link a) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.IsometryEquivariance.extendOddly_opposite <;> assumption
private theorem basisForm_mem {L : ℕ} (a : Fin 3)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.basisForm (L := L) (k := 0) (j := 0) a b ∈
      FullSpace.edgeFormSpace (meshAt L 0 0) := by
  classical
  refine ⟨fun b' h => ?_, fun b' => extendOddly_opposite (meshAt_zero_ne_zero L) _ b'⟩
  rw [FullSpace.basisForm, extendOddly_of_positive _ h]
  split_ifs
  · exact pauliFamily_mem_hermitianTraceless a
  · exact ComplexMatrix2.hermitianTraceless.zero_mem
private theorem basisForm_finiteSupport {L : ℕ} (a : Fin 3)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.HasFiniteEdgeSupport (FullSpace.basisForm (L := L) (k := 0) (j := 0) a b) := by
  classical
  refine (Set.finite_singleton b.1).subset ?_
  rintro b' ⟨h, hne⟩
  by_contra hb
  apply hne
  rw [FullSpace.basisForm, extendOddly_of_positive _ h,
    if_neg fun e => hb (Set.mem_singleton_iff.mpr e)]
abbrev _root_.YangMills.SharedProofs.p37344 := @basisForm_finiteSupport
theorem holds (hD : HessianDeterminants.HessianSymmAndDetsPositive) : Statement := by
  classical
  intro L hL ζ hζ
  have hU := expField_mem hζ
  refine ⟨hU, fun ι' ι => ?_, fun ι' ι => ?_⟩
  · have hb := ι'.2.2
    refine pauliCoeff_im_eq_zero ?_ ι'.1
    change FullSpace.covDiff (FullSpace.expField ζ) _ ι'.2.1 ∈ ComplexMatrix2.hermitianTraceless
    refine covDiff_mem_of_positive hU.1 (fun κ => ?_) hb
    by_cases h : κ = ι
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  · exact ((hD L hL).1 0 0 le_rfl).2.2 _ hU _ (basisForm_mem ι'.1 ι'.2)
      (basisForm_finiteSupport ι'.1 ι'.2) _ (basisForm_mem ι.1 ι.2)
      (basisForm_finiteSupport ι.1 ι.2)
end YangMills.Construction.Tower.RealFieldKernels
end
