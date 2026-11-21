import YangMills.Construction.HilbertSpaces.CommutingPairsOfAContractionAndAUnitary
import YangMills.Construction.SpectralMeasures.ProjectionValuedMeasuresOnASigmaAlgebra
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory
open YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert
open YangMills.Construction.SpectralMeasures
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.ContractionUnitary
def radialCoord : intervalCircle → ℂ := fun p => ((p.1.1 : ℝ) : ℂ)
def angularCoord : intervalCircle → ℂ := fun p => p.1.2
def projIcc : intervalCircle → Set.Icc (0 : ℝ) 1 := fun p => ⟨p.1.1, p.2.1⟩
theorem measurable_projIcc : Measurable projIcc :=
  Measurable.subtype_mk (measurable_fst.comp measurable_subtype_coe)
def tube (Y : MeasSet (Set.Icc (0 : ℝ) 1)) : MeasSet intervalCircle :=
  ⟨projIcc ⁻¹' Y.1, measurable_projIcc Y.2⟩
def basePt : intervalCircle :=
  ⟨(0, 1), ⟨Set.left_mem_Icc.mpr zero_le_one, by simp [circleSet]⟩⟩
section Measure
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open scoped Classical in
variable (H) in
def diracPVM : PVM intervalCircle H where
  toFun Y := if basePt ∈ Y.1 then 1 else 0
  isPVM :=
    { isOrthProj := fun Y => by
        split_ifs
        · exact ⟨fun φ ψ => by simp, by simp⟩
        · exact ⟨fun φ ψ => by simp, by simp⟩
      map_univ := by
        simp only [Set.mem_univ, if_true]
        rfl
      map_inter := fun Y Y' => by
        by_cases h : basePt ∈ Y.1 <;> by_cases h' : basePt ∈ Y'.1 <;> simp [h, h']
      countablyAdditive := fun ψ Y hd => by
        by_cases h : ∃ k, basePt ∈ (Y k).1
        · obtain ⟨k, hk⟩ := h
          have hu : basePt ∈ ⋃ k, (Y k).1 := Set.mem_iUnion.mpr ⟨k, hk⟩
          have hs := hasSum_single (f := fun l => diagForm
            (fun Y : MeasSet intervalCircle =>
              if basePt ∈ Y.1 then (1 : BddOp H) else 0) ψ (Y l)) k (fun l hl => by
              have h₁ : basePt ∉ (Y l).1 := fun hl' =>
                Set.disjoint_left.mp (hd hl) hl' hk
              simp [diagForm, h₁])
          simpa [diagForm, hk, hu] using hs
        · have hu : basePt ∉ ⋃ k, (Y k).1 := fun hu => h (Set.mem_iUnion.mp hu)
          have h' : ∀ k, basePt ∉ (Y k).1 := fun k hk => h ⟨k, hk⟩
          simp [diagForm, h', hu, hasSum_zero] }
def IsJointSpectralMeasure (A V : BddOp H) (E : PVM intervalCircle H) : Prop :=
  E.bddIntegral radialCoord = A ∧ E.bddIntegral angularCoord = V
def jointSpectralMeasure (A V : BddOp H) : PVM intervalCircle H :=
  haveI : Nonempty (PVM intervalCircle H) := ⟨diracPVM H⟩
  Classical.epsilon (IsJointSpectralMeasure A V)
end Measure
namespace JointSpectral
def statement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A V : BddOp H), IsCommutingPair A V →
    ((∃! E : PVM intervalCircle H, IsJointSpectralMeasure A V E) ∧
      IsJointSpectralMeasure A V (jointSpectralMeasure A V)) ∧
    (∀ c : Coeffs,
      (jointSpectralMeasure A V).bddIntegral (evalPoly c) = evalPolyOp c A V) ∧
    ((∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
        (A' V' : BddOp H') (B : BddOpBetween H H'),
        IsCommutingPair A' V' → B ∘L A = A' ∘L B → B ∘L V = V' ∘L B →
        (∀ f : intervalCircle → ℂ, IsBddMeasurable f →
          B ∘L (jointSpectralMeasure A V).bddIntegral f =
            (jointSpectralMeasure A' V').bddIntegral f ∘L B) ∧
        ∀ hB : IsUnitaryMap (B : H →ₗ[ℂ] H'),
          (jointSpectralMeasure A' V').toFun = (jointSpectralMeasure A V).conj hB) ∧
      (∀ C : BddOp H, C * A = A * C → C * V = V * C →
        ∀ f : intervalCircle → ℂ, IsBddMeasurable f →
          C * (jointSpectralMeasure A V).bddIntegral f =
            (jointSpectralMeasure A V).bddIntegral f * C)) ∧
    (∀ V' : BddOp H, IsUnitaryMap (V' : H →ₗ[ℂ] H) → A * V' = V' * A →
      (∀ g : Set.Icc (0 : ℝ) 1 → ℂ, IsBddMeasurable g →
        (jointSpectralMeasure A V).bddIntegral (g ∘ projIcc) =
          (jointSpectralMeasure A V').bddIntegral (g ∘ projIcc)) ∧
      ∀ Y : MeasSet (Set.Icc (0 : ℝ) 1),
        jointSpectralMeasure A V (tube Y) = jointSpectralMeasure A V' (tube Y)) ∧
    IsOrthProjOnto (jointSpectralMeasure A V (tube ⟨{0}, measurableSet_singleton 0⟩))
      (LinearMap.ker (A : H →ₗ[ℂ] H))
end JointSpectral
end YangMills.Construction.ContractionUnitary
end
