import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocal
import YangMills.Construction.Towers.ComponentsOfTheJetAlongHolomorphicAmplitudes
import YangMills.Construction.Towers.FourKernelsOfTheScaledPictureAreLocal
import YangMills.Construction.Towers.InversesOfJetsWithHolomorphicComponents
import YangMills.Construction.Towers.SumsProductsAndTransposesOfJetsWithHolomorphicComponents
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheScaledPictureAndTheirJets
import YangMills.Construction.Towers.ThreeOperatorsOfTheScaledPictureAreLocal
import YangMills.Construction.Towers.TraceNumberOfJetsWithHolomorphicComponents
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions
open PeriodicOperators
open BackgroundJets (gaugeFieldOfForm)
theorem fullTrace_sum_smul_pauliFamily (c : Fin 3 → ℂ) :
    Matrices.ComplexMatrix2.fullTrace (∑ a, c a • Matrices.ComplexMatrix2.pauliFamily a) = 0 := by
  have h : ∀ a : Fin 3, Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by
    intro a
    change Matrix.trace (Matrices.ComplexMatrix2.pauliFamily a) = 0
    fin_cases a <;> simp [Matrices.ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
      OneLoop.pauliZ, Matrix.trace_fin_two]
  exact Submodule.sum_mem Matrices.ComplexMatrix2.traceless fun a _ =>
    Submodule.smul_mem Matrices.ComplexMatrix2.traceless (c a) (h a)
theorem gaugeFieldOfForm_mem (hExp : Matrices.ComplexMatrix2.ExpLogEstimates) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) (ζ : (remainderIndex L k).Carrier → ℂ) :
    gaugeFieldOfForm L k ζ ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup := by
  classical
  have ha : 0 < meshAt L k 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast (by have := hL.2; omega : 0 < L)
    exact zpow_pos this _
  set A := (edgePauliCoordinates L k 0).ofCoeffs ζ with hA
  have hpos : ∀ b : Edge L k 0, b.IsPositivelyOriented →
      gaugeFieldOfForm L k ζ b = Matrices.ComplexMatrix2.matExp (Complex.I • A b) := by
    intro b hb
    simp [gaugeFieldOfForm, expForm, expTwist, hb, hA]
  have hneg : ∀ b : Edge L k 0, ¬b.IsPositivelyOriented →
      gaugeFieldOfForm L k ζ b = (Matrices.ComplexMatrix2.matExp (Complex.I • A b.opposite))⁻¹ := by
    intro b hb
    simp [gaugeFieldOfForm, expForm, expTwist, hb, hA]
  have htr : ∀ b : Edge L k 0, b.IsPositivelyOriented → Matrices.ComplexMatrix2.fullTrace (A b) = 0 := by
    intro b hb
    have e : A b = ∑ a, ζ (a, ⟨b, hb⟩) • Matrices.ComplexMatrix2.pauliFamily a := by
      simp [hA, edgePauliCoordinates, extendOddly, hb, ofPauliCoeffs]
    rw [e]
    exact fullTrace_sum_smul_pauliFamily _
  have hdet : ∀ b : Edge L k 0, b.IsPositivelyOriented →
      (Matrices.ComplexMatrix2.matExp (Complex.I • A b)).det = 1 := by
    intro b hb
    rw [hExp.2.2.2.2.2.1]
    have : Matrices.ComplexMatrix2.fullTrace (Complex.I • A b) = 0 := by
      change Matrix.trace (Complex.I • A b) = 0
      rw [Matrix.trace_smul]
      have := htr b hb
      simp only [Matrices.ComplexMatrix2.fullTrace] at this
      simp [this]
    rw [this, Complex.exp_zero]
  have hrev : ∀ b : Edge L k 0, ¬b.IsPositivelyOriented → b.opposite.IsPositivelyOriented := by
    intro b hb
    rcases InfiniteLattice.mem_positiveLinks_or_opposite_mem b with h | h
    · exact absurd (InfiniteLattice.mem_positiveLinks_iff.1 h) hb
    · exact InfiniteLattice.mem_positiveLinks_iff.1 h
  have hrev' : ∀ b : Edge L k 0, b.IsPositivelyOriented → ¬b.opposite.IsPositivelyOriented := by
    intro b hb h
    exact InfiniteLattice.opposite_notMem_positiveLinks ha
      (InfiniteLattice.mem_positiveLinks_iff.2 hb)
      (InfiniteLattice.mem_positiveLinks_iff.2 h)
  refine ⟨fun b => ?_, fun b => ?_⟩
  · change (gaugeFieldOfForm L k ζ b).det = 1
    by_cases hb : b.IsPositivelyOriented
    · rw [hpos b hb, hdet b hb]
    · rw [hneg b hb, Matrix.det_nonsing_inv, hdet _ (hrev b hb)]
      simp
  · by_cases hb : b.IsPositivelyOriented
    · rw [hneg _ (hrev' b hb), hpos b hb]
      rfl
    · rw [hpos _ (hrev b hb), hneg b hb, Matrix.nonsing_inv_nonsing_inv]
      rw [hdet _ (hrev b hb)]
      exact isUnit_one
theorem claim_of_parts (h₁ : ScaledKernelsLocal.FourKernelsLocal)
    (h₂ : ThreeLocalOperators.LocalEntireOperators)
    (h₃ : ScaledMeansLocality.MeansAreLocal)
    (h₄ : JetAlongAmplitudes.JetComponentsHolomorphicAlongAmplitudes)
    (h₅ : JetClosure.JetOpsClosed)
    (h₆ : InvertibleJetInverseHolomorphic)
    (h₇ : JetTraceHolomorphy.Claim)
    (hT : TowerIndexSets.Claim) (hExp : Matrices.ComplexMatrix2.ExpLogEstimates) :
    ScaledOperatorFunctionsClaim := by
  refine ⟨fun L hL k hk => ⟨?_, fun I I' hI hI' => h₄ L hL k hk I I' hI hI'⟩,
    fun δ hδ P hP hPs I I' I'' hI hI' hI'' => ?_⟩
  · obtain ⟨hD, hE, hz, hf⟩ := h₁ L hL k hk
    obtain ⟨hH, hK, hΔ⟩ := h₂ L hL k hk
    have t₀ := hT L hL k 0 (Nat.zero_le k)
    have t₁ := hT L hL k k le_rfl
    exact
      { periodic := ⟨t₀.1, t₀.2.1, t₀.2.2, t₁.1, t₁.2.1⟩
        gaugeField_mem := gaugeFieldOfForm_mem hExp hL k
        D_local := hD
        holonomyDefect_local := hE
        halfFaceTrace_local := hz
        curvature_local := hf
        H_local := hH
        K_local := hK
        Delta_local := hΔ
        Q_local := fun ρ C h => (h₃ L hL k hk ρ C h).1
        R_local := fun ρ C h => (h₃ L hL k hk ρ C h).2 }
  · obtain ⟨hs, hp, ht⟩ := h₅ δ hδ P hP hPs I I' I'' hI hI' hI''
    exact
      { add := hs
        mul := hp
        transpose := ht
        inv := h₆ δ hδ P hP hPs I hI
        traceNumber_holomorphic := h₇ δ hδ P hP hPs I hI }
end YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions
end
