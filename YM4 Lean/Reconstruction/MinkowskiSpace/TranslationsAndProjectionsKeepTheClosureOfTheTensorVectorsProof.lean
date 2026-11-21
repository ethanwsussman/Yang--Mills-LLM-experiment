import YangMills.Construction.HilbertSpaces.CalculusOfAProjectionValuedMeasureWithBoundedFunctionsProof
import Reconstruction.MinkowskiSpace.ClosureOfTheTensorVectorsAndTheEuclideanVectors
import Reconstruction.MinkowskiSpace.TranslationsAndMeasureOnTheTensorVectorsProof
import Reconstruction.MinkowskiSpace.TranslationsAndProjectionsKeepTheClosureOfTheTensorVectors
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.RealPointVectors.ClosureInvariance
open MinkowskiSpace FieldForms TestSpaces OneLoopNotation ComplexHilbert ProjectionMeasures
  HilbertToolkit PVMCalculus WightmanTheory RealPointVectors
theorem diffCoords_wickMapTuple_mem_futureTube {m : ℕ} {x : TestSpaces.PointTuple (m + 1)}
    (hx : x ∈ increasingPositiveTimes (m + 1)) (i : Fin (m + 1)) :
    MinkowskiSpace.diffCoords (wickMapTuple (tupleToComplex x)) i ∈ futureTube := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have hpos : 0 < x 0 3 := hx.2 (Nat.succ_pos m)
    have him : MinkowskiSpace.imPart
        (MinkowskiSpace.diffCoords (wickMapTuple (tupleToComplex x)) 0) =
          mkTimeSpace (x 0 3) 0 := by
      funext μ
      fin_cases μ <;>
        simp [MinkowskiSpace.imPart, MinkowskiSpace.diffCoords, wickMapTuple, tupleToComplex,
          wickMap, MinkowskiSpace.toComplex, mkTimeSpace, Fin.cons]
      all_goals rfl
    change coneGap (MinkowskiSpace.imPart
      (MinkowskiSpace.diffCoords (wickMapTuple (tupleToComplex x)) 0)) > 0
    rw [him]
    simpa [coneGap, spacePart, mkTimeSpace, spaceNorm] using hpos
  · exact wickDiffs_mem_futureTube hx.1 j
theorem add_mem_futureTube (hC : MinkowskiSpace.ConeTubeLorentz.ConesTubeConvex)
    {ζ ω : ComplexVec4} (hζ : ζ ∈ futureTube)
    (hω : MinkowskiSpace.imPart ω ∈ closedFutureCone) : ζ + ω ∈ futureTube := by
  have h := hC.2.2.2.2.1 _ hω _ hζ
  have him : MinkowskiSpace.imPart (ζ + ω) =
      MinkowskiSpace.imPart ω + MinkowskiSpace.imPart ζ := by
    funext μ
    simp [MinkowskiSpace.imPart, add_comm]
  show MinkowskiSpace.imPart (ζ + ω) ∈ futureCone
  rw [him]
  exact h
theorem diffCoords_add_mem_futureTube (hC : MinkowskiSpace.ConeTubeLorentz.ConesTubeConvex)
    {m : ℕ} {z : Fin (m + 1) → ComplexVec4} {ω : ComplexVec4}
    (hz : ∀ i, MinkowskiSpace.diffCoords z i ∈ futureTube)
    (hω : MinkowskiSpace.imPart ω ∈ closedFutureCone) (i : Fin (m + 1)) :
    MinkowskiSpace.diffCoords (fun k => z k + ω) i ∈ futureTube := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact add_mem_futureTube hC (hz 0) hω
  · have h := hz j.succ
    have heq : MinkowskiSpace.diffCoords (fun k => z k + ω) j.succ =
        MinkowskiSpace.diffCoords z j.succ := by
      simp [MinkowskiSpace.diffCoords, MinkowskiSpace.successiveDiffs]
    rw [heq]
    exact h
theorem cexp_minkowskiForm_eq_expChar (b p : Fin 4 → ℝ) :
    Complex.exp (Complex.I * minkowskiForm (MinkowskiSpace.toComplex ![b 0, -b 1, -b 2, -b 3])
      (MinkowskiSpace.toComplex p)) = expChar b p := by
  have h : minkowskiForm (MinkowskiSpace.toComplex ![b 0, -b 1, -b 2, -b 3])
      (MinkowskiSpace.toComplex p) = (dotFour b p : ℂ) := by
    simp [minkowskiForm, spaceBilin, spacePart, MinkowskiSpace.toComplex, dotFour,
      Fin.sum_univ_four, Fin.sum_univ_three]
    ring
  rw [h, expChar]
theorem isBddMeasurableFun_expChar (b : Fin 4 → ℝ) :
    IsBddMeasurableFun (expChar b) := by apply _root_.YangMills.Construction.PVMCalculus.isBddMeasurableFun_expChar <;> assumption
section Calculus
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem pvmIntegral_indicator_of_isSupportedOn {E : FourBorelSet → BddOp H} {Δ₀ : FourBorelSet}
    (hI : PvmIntegralBasic E Δ₀) (hR : PvmIntegralRules E)
    (hc : IsSupportedOn E Δ₀) {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u) :
    pvmIntegral E (Δ₀.1.indicator u) = pvmIntegral E u := by apply _root_.YangMills.Construction.TensorTranslations.pvmIntegral_indicator_of_isSupportedOn <;> assumption
end Calculus
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K} {℘ C : ℝ}
theorem map_mem_of_mem_closedLinSpan (B : BddOp K) {S : Set K} {Y : Submodule ℂ K}
    (hY : IsClosed (Y : Set K)) (hS : ∀ v ∈ S, B v ∈ Y) {v : K}
    (hv : v ∈ SesquilinearForms.closedLinSpan S) : B v ∈ Y := by
  have hle : Submodule.span ℂ S ≤ Y.comap (B : K →ₗ[ℂ] K) :=
    Submodule.span_le.2 fun w hw => hS w hw
  have hv' : v ∈ closure (Submodule.span ℂ S : Set K) := by
    rw [← seqClosureOf_eq_closure]
    exact hv
  have h := map_mem_closure B.continuous hv' (t := (Y : Set K)) fun w hw => hle hw
  rwa [hY.closure_eq] at h
theorem closure_invariant_of_isBoundedFieldForm
    (hClosure : RealPointVectors.TensorClosure.Statement)
    (hProducts : FieldProductProperties)
    (hCalculus : BoundedFunctionalCalculus)
    (hHilbert : HilbertCompletionExtensionRiesz)
    (hCone : MinkowskiSpace.ConeTubeLorentz.Statement)
    (hf : IsBoundedFieldForm E Ω A ℘ C) :
    (∀ ζ : ComplexVec4, MinkowskiSpace.imPart ζ ∈ closedFutureCone →
      ∀ v ∈ tensorDomainClosure E Ω A, spectralTranslation E ζ v ∈ tensorDomainClosure E Ω A) ∧
    ∀ Δ : FourBorelSet, ∀ v ∈ tensorDomainClosure E Ω A, E Δ v ∈ tensorDomainClosure E Ω A := by
  obtain ⟨hspan, -, hvec⟩ := hClosure E Ω A ℘ C hf
  obtain ⟨-, -, -, -, -, -, -, -, -, hscalar, -⟩ := hProducts K E Ω A ℘ C hf
  obtain ⟨hMS, hI, hR, -, -, -, -, -, -, -⟩ :=
    (hCalculus.2 K).2 E closedFutureConeBorel hf.isPVM hf.supportedOn
  have hCones := hCone.2.1
  let Y : Submodule ℂ K := (tensorDomain E Ω A).topologicalClosure
  have hYset : (Y : Set K) = tensorDomainClosure E Ω A := by
    show closure _ = _
    rw [tensorDomainClosure, seqClosureOf_eq_closure]
    rfl
  have hYclosed : IsClosed (Y : Set K) := Submodule.isClosed_topologicalClosure _
  have hmemY : ∀ {v : K}, v ∈ Y ↔ v ∈ tensorDomainClosure E Ω A := by
    intro v
    rw [← hYset]
    rfl
  have hsubset : euclideanStates E Ω A ⊆ tensorDomainClosure E Ω A := by
    intro v hv
    rw [hspan, SesquilinearForms.closedLinSpan, seqClosureOf_eq_closure]
    exact subset_closure (Submodule.subset_span hv)
  have htrans : ∀ ζ : ComplexVec4, MinkowskiSpace.imPart ζ ∈ closedFutureCone →
      ∀ v ∈ tensorDomainClosure E Ω A, spectralTranslation E ζ v ∈ tensorDomainClosure E Ω A := by
    intro ζ hζ v hv
    rw [← hmemY]
    rw [hspan] at hv
    refine map_mem_of_mem_closedLinSpan _ hYclosed ?_ hv
    rintro w ⟨m, x, hx, rfl⟩
    rw [hmemY]
    cases m with
    | zero =>
      have h : spectralTranslation E ζ Ω = Ω :=
        (hscalar 0 0 (fun i => i.elim0) (fun i => i.elim0) ζ
          (fun i => i.elim0) (fun i => i.elim0) hζ).1
      show spectralTranslation E ζ Ω ∈ _
      rw [h]
      exact hsubset ⟨0, x, hx, rfl⟩
    | succ m =>
      have hdiff := diffCoords_wickMapTuple_mem_futureTube hx
      have hz : wickMapTuple (tupleToComplex x) ∈ diffCoordsInTube (m + 1) :=
        fun i _ => hdiff i
      have h := (hscalar (m + 1) 0 _ (fun i => i.elim0) ζ hz (fun i => i.elim0) hζ).1
      rw [h]
      exact hvec m _ (diffCoords_add_mem_futureTube hCones hdiff hζ)
  refine ⟨htrans, ?_⟩
  intro Δ v hv
  have hperp := ((hHilbert.2.2.1 K).1 Y ((isClosedSet_iff _).2 hYclosed)).2
  have hgoal : E Δ v ∈ orthSet (orthSet (Y : Set K)) := by
    intro χ hχ
    have hzero : spectralScalarMeasure E χ v Δ = 0 := by
      refine hCalculus.1 _ (hMS.2.2.2 χ v).2 (fun b => ?_) Δ
      have hb := isBddMeasurableFun_expChar b
      rw [← (hI.1 _ hb).1 χ v]
      have hT : spectralTranslation E (MinkowskiSpace.toComplex ![b 0, -b 1, -b 2, -b 3]) =
          pvmIntegral E (expChar b) := by
        rw [← pvmIntegral_indicator_of_isSupportedOn hI hR hf.supportedOn hb]
        show pvmIntegral E _ = pvmIntegral E _
        congr 2
        funext p
        exact cexp_minkowskiForm_eq_expChar b p
      rw [← hT]
      refine hχ _ (hmemY.2 (htrans _ ?_ v hv))
      show coneGap _ ≥ 0
      simp [coneGap, MinkowskiSpace.imPart, MinkowskiSpace.toComplex, spacePart, spaceNorm]
    have hz : ⟪χ, E Δ v⟫_ℂ = 0 := hzero
    exact inner_eq_zero_symm.1 hz
  rw [hperp] at hgoal
  exact hmemY.1 hgoal
theorem closureInvarianceStatement_holds
    (hClosure : RealPointVectors.TensorClosure.Statement)
    (hProducts : FieldProductProperties)
    (hCalculus : BoundedFunctionalCalculus)
    (hHilbert : HilbertCompletionExtensionRiesz)
    (hCone : MinkowskiSpace.ConeTubeLorentz.Statement) : ClosureInvarianceStatement :=
  fun _ _ _ _ _ hf => closure_invariant_of_isBoundedFieldForm hClosure hProducts hCalculus hHilbert hCone hf
end YangMills.Construction.RealPointVectors.ClosureInvariance
