import YangMills.Construction.OneLoopLaw.GaugeColourMomentaAndDifferencesOfFunctionalsProof
import YangMills.Construction.OneLoopLaw.PolarisationIsInvariantUnderIsometries
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.OneLoopLaw.ComplexHessianInvariance
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators.Tempered
open YangMills.Construction.Matrices
variable {L n : ℕ}
abbrev tangentPush (σ : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (B : UnitEdge L n → ComplexMatrix2) : UnitEdge L n → ComplexMatrix2 :=
  isometryOnTangent (k := 0) (j := 0) σ (identityField L n) B
theorem tangentEdgeValue_identityField (B : UnitEdge L n → ComplexMatrix2) (b : UnitEdge L n) :
    tangentEdgeValue (k := 0) (j := 0) (identityField L n) B b =
      open Classical in if b.IsPositivelyOriented then B b else -B b.opposite := by
  simp [tangentEdgeValue, identityField, ComplexMatrix2.conjugateBy]
theorem tangentPush_odd_map (σ : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (φ : ComplexMatrix2 → ComplexMatrix2) (hφ : ∀ X, φ (-X) = -φ X)
    (B : UnitEdge L n → ComplexMatrix2) :
    tangentPush σ (fun b => φ (B b)) = fun b => φ (tangentPush σ B b) := by
  funext b
  simp only [tangentPush, isometryOnTangent, extendOddly, tangentEdgeValue_identityField]
  split_ifs <;> simp [hφ]
theorem tangentPush_linearCombination
    (σ : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n) (a c : ℂ)
    (R R' : UnitEdge L n → ComplexMatrix2) :
    tangentPush σ (a • R + c • R') = a • tangentPush σ R + c • tangentPush σ R' := by
  funext b
  simp only [tangentPush, isometryOnTangent, extendOddly, tangentEdgeValue_identityField,
    Pi.add_apply, Pi.smul_apply]
  split_ifs <;> simp [smul_neg, add_comm]
theorem realComponent_mem_edgeFormSpace {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) : realComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p16359 <;> assumption
theorem imagComponent_mem_edgeFormSpace {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) : imagComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p9724 <;> assumption
theorem mem_complexEdgeForms_of_mem_edgeFormSpace {R : UnitEdge L n → ComplexMatrix2}
    (hR : R ∈ edgeFormSpace L n 0 0) : R ∈ complexEdgeForms L n 0 0 := by apply _root_.YangMills.DeltaSharedProofs.p8199 <;> assumption
theorem expTwist_identityField {X : UnitEdge L n → ComplexMatrix2}
    (hX : ∀ b : UnitEdge L n, X b.opposite = -X b) :
    PeriodicLattice.expTwist X (identityField L n) =
      fun b => ComplexMatrix2.matExp (Complex.I • X b) := by apply _root_.YangMills.SharedProofs.p79696 <;> assumption
theorem expTwist_identityField_mem_fieldSpace
    (hexp : ∀ Y ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.specialUnitary)
    {X : UnitEdge L n → ComplexMatrix2} (hX : X ∈ edgeFormSpace L n 0 0) :
    PeriodicLattice.expTwist X (identityField L n) ∈ fieldSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p92839 <;> assumption
theorem identityField_mem_fieldsIn :
    identityField L n ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.DeltaSharedProofs.p33329 <;> assumption
theorem hessianAtIdentity_tangentPush
    (hexp : ∀ Y ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.specialUnitary)
    (hiso : LeftChartFacts.IsometryEquivarianceForms L n 0 0) {F : FieldFamily L}
    (hF : IsAdmissibleMember (F n))
    {σ : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hσ : IsDistancePreserving σ) (hσ' : MapsSublatticeOnto 0 0 σ)
    {R R' : UnitEdge L n → ComplexMatrix2} (hR : R ∈ edgeFormSpace L n 0 0)
    (hR' : R' ∈ edgeFormSpace L n 0 0) :
    hessianAtIdentity F n (tangentPush σ R) (tangentPush σ R') = hessianAtIdentity F n R R' := by
  have hcomb : ∀ p : ℝ × ℝ,
      algebraMap ℝ ℂ p.1 • R + algebraMap ℝ ℂ p.2 • R' ∈ edgeFormSpace L n 0 0 := by
    intro p
    rw [algebraMap_smul, algebraMap_smul]
    exact (edgeFormSpace L n 0 0).add_mem ((edgeFormSpace L n 0 0).smul_mem _ hR)
      ((edgeFormSpace L n 0 0).smul_mem _ hR')
  have htend : Tendsto (fun p : ℝ × ℝ => PeriodicLattice.expTwist
        (algebraMap ℝ ℂ p.1 • R + algebraMap ℝ ℂ p.2 • R') (identityField L n))
      (𝓝 (0, 0)) (𝓝[fieldSpace L n 0 0] fun _ => (1 : ComplexMatrix2)) := by
    refine tendsto_nhdsWithin_iff.2
      ⟨?_, Eventually.of_forall fun p => expTwist_identityField_mem_fieldSpace hexp (hcomb p)⟩
    refine tendsto_pi_nhds.2 fun b => ?_
    simp only [expTwist_identityField (hcomb _).2]
    have hc : Continuous fun p : ℝ × ℝ => ComplexMatrix2.matExp (Complex.I •
        ((algebraMap ℝ ℂ p.1 • R + algebraMap ℝ ℂ p.2 • R') b)) := by
      let _ : NormedAlgebra ℚ ComplexMatrix2 := NormedAlgebra.restrictScalars ℚ ℂ ComplexMatrix2
      refine NormedSpace.exp_continuous.comp ?_
      simp only [Pi.add_apply, Pi.smul_apply]
      fun_prop
    have h0 := hc.tendsto ((0 : ℝ), (0 : ℝ))
    simpa using h0
  have hkey : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      F n (PeriodicLattice.expTwist
          (algebraMap ℝ ℂ p.1 • tangentPush σ R + algebraMap ℝ ℂ p.2 • tangentPush σ R')
          (identityField L n)) =
        F n (PeriodicLattice.expTwist (algebraMap ℝ ℂ p.1 • R + algebraMap ℝ ℂ p.2 • R')
          (identityField L n)) := by
    filter_upwards [htend.eventually hF.symmetry] with p hp
    have hone : pushField (k := 0) (j := 0) σ (identityField L n) = identityField L n := rfl
    have hact := (hiso σ hσ hσ' _ identityField_mem_fieldsIn).1 _
      (mem_complexEdgeForms_of_mem_edgeFormSpace (hcomb p))
    have hlin : isometryOnTangent (k := 0) (j := 0) σ (identityField L n)
        (algebraMap ℝ ℂ p.1 • R + algebraMap ℝ ℂ p.2 • R') =
          algebraMap ℝ ℂ p.1 • tangentPush σ R + algebraMap ℝ ℂ p.2 • tangentPush σ R' :=
      tangentPush_linearCombination σ _ _ R R'
    rw [hone, hlin] at hact
    rw [hact]
    exact hp σ hσ hσ'
  have hcurry := hkey.curry_nhds
  have hinner : (fun s : ℝ => deriv (fun t : ℝ => F n (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ s • tangentPush σ R + algebraMap ℝ ℂ t • tangentPush σ R')
        (identityField L n))) 0) =ᶠ[𝓝 0]
      fun s : ℝ => deriv (fun t : ℝ => F n (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ s • R + algebraMap ℝ ℂ t • R') (identityField L n))) 0 := by
    filter_upwards [hcurry] with s hs
    exact Filter.EventuallyEq.deriv_eq hs
  exact hinner.deriv_eq
theorem statement_holds (h₁ : LeftChartFacts.HoldEverywhere)
    (h₂ : ComplexMatrix2.UnitaryLogarithmProperties) : Statement := by
  intro L n hL hn F hF σ hσ hσ' B hB B' hB'
  have hexp : ∀ Y ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.specialUnitary :=
    fun Y hY => (h₂.1 Y hY).2.2.2
  have hiso : LeftChartFacts.IsometryEquivarianceForms L n 0 0 :=
    ((h₁ L 0 0 0 0 hL le_rfl le_rfl le_rfl).2.1 n hn).2.2.2.2.2
  have hre : ∀ A : UnitEdge L n → ComplexMatrix2,
      realComponent (tangentPush σ A) = tangentPush σ (realComponent A) := by
    intro A
    refine (tangentPush_odd_map σ (fun X => (2⁻¹ : ℂ) • (X + X.conjTranspose))
      (fun X => ?_) A).symm
    simp only [Matrix.conjTranspose_neg, ← neg_add, smul_neg]
  have him : ∀ A : UnitEdge L n → ComplexMatrix2,
      imagComponent (tangentPush σ A) = tangentPush σ (imagComponent A) := by
    intro A
    refine (tangentPush_odd_map σ (fun X => (2 * Complex.I)⁻¹ • (X - X.conjTranspose))
      (fun X => ?_) A).symm
    simp only [Matrix.conjTranspose_neg, sub_neg_eq_add, ← smul_neg, neg_sub, neg_add_eq_sub]
  have hrp := fun {R R' : UnitEdge L n → ComplexMatrix2} (hR : R ∈ edgeFormSpace L n 0 0)
      (hR' : R' ∈ edgeFormSpace L n 0 0) => hessianAtIdentity_tangentPush hexp hiso hF hσ hσ' hR hR'
  have a₁ := realComponent_mem_edgeFormSpace hB
  have a₂ := imagComponent_mem_edgeFormSpace hB
  have a₃ := realComponent_mem_edgeFormSpace hB'
  have a₄ := imagComponent_mem_edgeFormSpace hB'
  simp only [complexHessian]
  rw [hre B, him B, hre B', him B', hrp a₁ a₃, hrp a₂ a₄, hrp a₁ a₄, hrp a₂ a₃]
end YangMills.Construction.OneLoopLaw.ComplexHessianInvariance
end
