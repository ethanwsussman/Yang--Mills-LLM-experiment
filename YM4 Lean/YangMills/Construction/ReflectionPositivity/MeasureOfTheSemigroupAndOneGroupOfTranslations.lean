import YangMills.Construction.ReflectionPositivity.SymmetricFunctionalsWithAContraction
import YangMills.Construction.SpectralTheory.FunctionalCalculus
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal
noncomputable section
namespace YangMills.Construction
namespace SpectralTheory
namespace SpectralMeasureOn
variable {d : ℕ} [NeZero d] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
open scoped Classical in
def dirac (S : BorelSets d) (x₀ : Fin d → ℝ) (hx : x₀ ∈ S.1) : SpectralMeasureOn S H where
  toFun B := if x₀ ∈ B.1 then 1 else 0
  isStarProjection B := by
    split_ifs
    · exact IsStarProjection.one _
    · exact IsStarProjection.zero _
  map_empty := by simp
  map_whole := by simp [hx]
  map_inter B C := by
    by_cases hB : x₀ ∈ B.1 <;> by_cases hC : x₀ ∈ C.1 <;> simp [hB, hC]
  tendsto_sum B hdisj v := by
    by_cases hex : ∃ k, x₀ ∈ (B k).1
    · obtain ⟨k, hk⟩ := hex
      have hmem : x₀ ∈ ⋃ k, (B k).1 := mem_iUnion.mpr ⟨k, hk⟩
      have hsum := hasSum_single (f := fun l =>
        (if x₀ ∈ (B l).1 then (1 : H →L[ℂ] H) else 0) v) k (fun l hl => by
          have : x₀ ∉ (B l).1 := fun hl' => Set.disjoint_left.mp (hdisj hl) hl' hk
          simp [this])
      simpa [hk, hmem] using hsum.tendsto_sum_nat
    · have hmem : x₀ ∉ ⋃ k, (B k).1 := fun hm => hex (mem_iUnion.mp hm)
      have hnot : ∀ k, x₀ ∉ (B k).1 := fun k hk => hex ⟨k, hk⟩
      simp [hmem, hnot]
end SpectralMeasureOn
end SpectralTheory
namespace ReflectionPositivity
namespace ShiftSpectralMeasure
open SeparatedTuples ReflectionPositivity.TupleForm ReflectionPositivity.Reconstruction
  ReflectionPositivity.ContractionFunctionals SpectralTheory
open HilbertSpaceBasics (IsPosSemidef ofBounded)
def energyMomentumRegion : BorelSets 2 :=
  ⟨nonnegHalfPlane, measurableSet_nonnegHalfPlane⟩
def energyProj (p : Fin 2 → ℝ) : Fin 1 → ℝ :=
  fun _ => p 0
def momentumProj (p : Fin 2 → ℝ) : Fin 1 → ℝ :=
  fun _ => p 1
theorem measurable_energyProj : Measurable energyProj :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply 0
theorem measurable_momentumProj : Measurable momentumProj :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply 1
def toLineBorel (S : BorelSpectral.BorelSubsets ℝ) : BorelSets 1 :=
  ⟨{x | x 0 ∈ S.1}, (measurable_pi_apply 0) S.2⟩
section Objects
variable (φ : TupleFunctional) (hφ : IsPosSemidef (reflectionForm φ))
def IsShiftSpectralMeasure (k : Fin 3)
    (P : SpectralMeasureOn energyMomentumRegion (PhysicalSpace φ hφ)) : Prop :=
  ∀ (t : ℝ≥0) (s : ℝ),
    ofBounded (timeShift φ hφ t * spaceShift φ hφ (s • spatialBasisVec k)) =
      P.extend.functionalCalculusOn energyMomentumRegion fun p =>
        Complex.exp (((-(t : ℝ) * p.1 0 : ℝ) : ℂ) + Complex.I * ((s * p.1 1 : ℝ) : ℂ))
def shiftSpectralMeasure (k : Fin 3) :
    SpectralMeasureOn energyMomentumRegion (PhysicalSpace φ hφ) :=
  haveI : Nonempty (SpectralMeasureOn energyMomentumRegion (PhysicalSpace φ hφ)) :=
    ⟨SpectralMeasureOn.dirac energyMomentumRegion 0
      (by simp [energyMomentumRegion, nonnegHalfPlane])⟩
  Classical.epsilon (IsShiftSpectralMeasure φ hφ k)
def energyOp (k : Fin 3) : UnboundedOperator (PhysicalSpace φ hφ) :=
  (shiftSpectralMeasure φ hφ k).extend.coordinateOp 0
def momentumOp (k : Fin 3) : UnboundedOperator (PhysicalSpace φ hφ) :=
  (shiftSpectralMeasure φ hφ k).extend.coordinateOp 1
def energyMarginal (k : Fin 3) (B : BorelSets 1) :
    PhysicalSpace φ hφ →L[ℂ] PhysicalSpace φ hφ :=
  (shiftSpectralMeasure φ hφ k).extend.pushforward energyProj measurable_energyProj B
def momentumMarginal (k : Fin 3) (B : BorelSets 1) :
    PhysicalSpace φ hφ →L[ℂ] PhysicalSpace φ hφ :=
  (shiftSpectralMeasure φ hφ k).extend.pushforward momentumProj measurable_momentumProj B
end Objects
def ExistsUniqueShiftMeasure (φ : TupleFunctional) (hφ : IsPosSemidef (reflectionForm φ))
    (k : Fin 3) : Prop :=
  (∃! P, IsShiftSpectralMeasure φ hφ k P) ∧
    IsShiftSpectralMeasure φ hφ k (shiftSpectralMeasure φ hφ k)
def EnergyOpProperties (φ : TupleFunctional) (hφ : IsPosSemidef (reflectionForm φ))
    (k : Fin 3) : Prop :=
  (∃ Q : ProjectionMeasure 1 (PhysicalSpace φ hφ),
    (∀ B, Q B = energyMarginal φ hφ k B) ∧ HasSpectralResolution (energyOp φ hφ k) Q ∧
      Q.IsConcentratedOn nonnegReals ∧
      ∀ t : ℝ≥0, Q.expNegMulOp t = ofBounded (timeShift φ hφ t)) ∧
    IsPositiveOp (energyOp φ hφ k) ∧
    ∀ (T : UnboundedOperator (PhysicalSpace φ hφ)) (Q : ProjectionMeasure 1 (PhysicalSpace φ hφ)),
      HasSpectralResolution T Q → Q.IsConcentratedOn nonnegReals →
        (∀ t : ℝ≥0, Q.expNegMulOp t = ofBounded (timeShift φ hφ t)) →
          T = energyOp φ hφ k
def MomentumOpProperties (φ : TupleFunctional) (hφ : IsPosSemidef (reflectionForm φ))
    (k : Fin 3) : Prop :=
  (∃ Q : ProjectionMeasure 1 (PhysicalSpace φ hφ),
    (∀ B, Q B = momentumMarginal φ hφ k B) ∧ HasSpectralResolution (momentumOp φ hφ k) Q ∧
      ∀ s : ℝ, Q.expIMulOp s = ofBounded (spaceShift φ hφ (s • spatialBasisVec k))) ∧
    ∀ (T : UnboundedOperator (PhysicalSpace φ hφ)) (Q : ProjectionMeasure 1 (PhysicalSpace φ hφ)),
      HasSpectralResolution T Q →
        (∀ s : ℝ, Q.expIMulOp s = ofBounded (spaceShift φ hφ (s • spatialBasisVec k))) →
          T = momentumOp φ hφ k
def VacuumAnnihilated (φ : TupleFunctional) (hφ : IsPosSemidef (reflectionForm φ))
    (k : Fin 3) : Prop :=
  (∃ hv : vacuum φ hφ ∈ (energyOp φ hφ k).domain,
    energyOp φ hφ k ⟨vacuum φ hφ, hv⟩ = 0) ∧
  ∃ hv : vacuum φ hφ ∈ (momentumOp φ hφ k).domain,
    momentumOp φ hφ k ⟨vacuum φ hφ, hv⟩ = 0
def AgreesWithReconstruction (φ : TupleFunctional) (hφ : IsPosSemidef (reflectionForm φ))
    (k : Fin 3) : Prop :=
  (∀ B : BorelSubsets energyMomentumRegion, shiftSpectralMeasure φ hφ k B =
    jointSpectralMeasure φ hφ k ⟨Subtype.val ⁻¹' B.1, measurable_subtype_coe B.2.1⟩) ∧
  (∀ S : BorelSpectral.BorelSubsets ℝ,
    energyMarginal φ hφ k (toLineBorel S) = jointSpectralMeasure φ hφ k (energyBand S) ∧
      energyMarginal φ hφ k (toLineBorel S) =
        SpectralTheorem.spectralMeasure (hamiltonian φ hφ)
          (BorelSpectral.realLineSet S)) ∧
  ∀ S : BorelSpectral.BorelSubsets ℝ,
    momentumMarginal φ hφ k (toLineBorel S) = jointSpectralMeasure φ hφ k (momentumBand S) ∧
      momentumMarginal φ hφ k (toLineBorel S) =
        SpectralTheorem.spectralMeasure (momentum φ hφ k)
          (BorelSpectral.realLineSet S)
def ShiftSpectralMeasureTheorem : Prop :=
  ∀ φ : TupleFunctional, IsAdmissible φ → ∃ hφ : IsPosSemidef (reflectionForm φ),
    (∀ k : Fin 3, ExistsUniqueShiftMeasure φ hφ k ∧ EnergyOpProperties φ hφ k ∧
      MomentumOpProperties φ hφ k ∧ VacuumAnnihilated φ hφ k ∧ AgreesWithReconstruction φ hφ k) ∧
    ∀ k l : Fin 3, energyOp φ hφ k = energyOp φ hφ l
end ShiftSpectralMeasure
end ReflectionPositivity
end YangMills.Construction
