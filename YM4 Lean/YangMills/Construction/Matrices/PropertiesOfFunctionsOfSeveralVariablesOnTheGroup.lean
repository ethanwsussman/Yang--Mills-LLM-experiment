import YangMills.Construction.HilbertSpace.FormsAndOperators
import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open Matrices.ComplexMatrix2 HilbertSpaceBasics
namespace SpinHarmonics.SeveralVariables
section Spaces
variable {J : Type} [Finite J]
theorem finite_indicesWithSpins (l : J → HalfNatural) :
    {α : PeterWeylIndex J | spins α = l}.Finite := by
  refine (Set.Finite.pi' fun b => finite_labelsBounded (l b)).subset fun α hα b => ?_
  have hb : (α b).spin = l b := congrFun hα b
  simp [hb]
def indicesWithSpins (l : J → HalfNatural) : Finset (PeterWeylIndex J) :=
  (finite_indicesWithSpins l).toFinset
def prodCoeffSpanL2 (l : J → HalfNatural) : Submodule ℂ (HaarL2 J) :=
  (prodCoeffSpan l).map (ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ).toLinearMap
variable (J) in
def truncatedCoeffSpanL2 (ϰ : HalfNatural) : Submodule ℂ (HaarL2 J) :=
  (truncatedCoeffSpan J ϰ).map (ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ).toLinearMap
def biTranslate (g g' u : J → specialUnitary) : J → specialUnitary :=
  fun b => g b * u b * g' b
def IsRealizedIn (F : (J → specialUnitary) → ℂ) (E : Submodule ℂ C(J → specialUnitary, ℂ)) :
    Prop :=
  ∃ H ∈ E, ∀ u, F u = H u
def nearbySpinSpan (B : Set J) (D : ↥B → ℕ) (l : J → HalfNatural) :
    Submodule ℂ C(J → specialUnitary, ℂ) :=
  ⨆ (l' : J → HalfNatural) (_ : (∀ b : ↥B, |(l' b).toReal - (l b).toReal| ≤ (D b : ℝ) / 2) ∧
    ∀ b, b ∉ B → l' b = l b), prodCoeffSpan l'
end Spaces
section Requirements
variable {J : Type} [Finite J]
def OrthonormalBasisAndProjections (l : J → HalfNatural) (ϰ : HalfNatural) : Prop :=
  Orthonormal ℂ (peterWeylVec : PeterWeylIndex J → HaarL2 J) ∧
  LinearIndependent ℂ (fun α : {α : PeterWeylIndex J // spins α = l} => peterWeylFn α.1) ∧
  Submodule.span ℂ (peterWeylFn '' {α : PeterWeylIndex J | spins α = l}) =
    prodCoeffSpan l ∧
  (∀ u u' : J → specialUnitary, isotypicKernel l u u' =
    ∑ α ∈ indicesWithSpins l, peterWeylFn α u * star (peterWeylFn α u')) ∧
  (∀ u u' : J → specialUnitary,
    (isotypicKernel l u u').im = 0 ∧ isotypicKernel l u u' = isotypicKernel l u' u) ∧
  IsOrthProjOnto (isotypicProj l) (prodCoeffSpanL2 l : Set _) ∧
  IsOrthProjOnto (truncationProj J ϰ) (truncatedCoeffSpanL2 J ϰ : Set _) ∧
  Pairwise fun l₁ l₂ : J → HalfNatural =>
    prodCoeffSpanL2 l₁ ⟂ prodCoeffSpanL2 l₂
variable (J) in
def PeterWeylExpansion : Prop :=
  ∀ F : HaarL2 J,
    HasSum (fun α : PeterWeylIndex J =>
      (inner ℂ (peterWeylVec α) F : ℂ) • peterWeylVec α) F ∧
    HasSum (fun l : J → HalfNatural => isotypicProj l F) F ∧
    HasSum (fun α : PeterWeylIndex J => ‖(inner ℂ (peterWeylVec α) F : ℂ)‖ ^ 2) (‖F‖ ^ 2)
def IsotypicProjCommutesBiTranslate (l : J → HalfNatural) : Prop :=
  ∀ (g g' : J → specialUnitary) (F : HaarL2 J),
    MemLp (fun u => F (biTranslate g g' u)) 2 (haarPi J) ∧
    isotypicProj l (toHaarL2 fun u => F (biTranslate g g' u)) =
      toHaarL2 fun u => isotypicProj l F (biTranslate g g' u)
def KernelDiagonalEqDim (l : J → HalfNatural) (ϰ : HalfNatural) : Prop :=
  (∀ u : J → specialUnitary,
    ((truncatedDim J ϰ : ℝ) : ℂ) = truncationKernel ϰ u u ∧
    truncatedDim J ϰ = ∑ α ∈ boundedIndices J ϰ, ‖peterWeylFn α u‖ ^ 2 ∧
    isotypicKernel l u u = ((∏ᶠ b, (2 * (l b).toReal + 1) ^ 2 : ℝ) : ℂ)) ∧
  truncatedDim J ϰ = (Module.finrank ℂ (truncatedCoeffSpan J ϰ) : ℝ) ∧
  (∏ᶠ b, (2 * (l b).toReal + 1) ^ 2 : ℝ) = (Module.finrank ℂ (prodCoeffSpan l) : ℝ)
def IsStarClosedPolySpan (E : Submodule ℂ C(J → specialUnitary, ℂ)) : Prop :=
  FiniteDimensional ℂ E ∧ (∀ F ∈ E, IsEntryPolynomial (F : (J → specialUnitary) → ℂ)) ∧
    ∀ F ∈ E, star F ∈ E
def PolyMulShiftsSpins (l : J → HalfNatural) : Prop :=
  (∀ (B : Set J), B.Nonempty → ∀ (D : ↥B → ℕ) (f : (↥B → specialUnitary) → ℂ),
    HasDegreeBound D f →
    ∀ ψ ∈ prodCoeffSpan l,
      IsRealizedIn (fun u => pullFromPart B f u * ψ u) (nearbySpinSpan B D l)) ∧
  ∀ (D : ℕ) (F : (J → specialUnitary) → ℂ), HasDegreeBound (fun _ : J => D) F →
    IsRealizedIn F (truncatedCoeffSpan J ⟨D⟩)
variable (J) in
def PolyHasFiniteDegrees : Prop :=
  ∀ F : (J → specialUnitary) → ℂ, IsEntryPolynomial F →
    (∃ ϰ' : HalfNatural, IsRealizedIn F (truncatedCoeffSpan J ϰ')) ∧
      ∃ D : J → ℕ, HasDegreeBound D F
variable (J) in
def RealPolyDense : Prop :=
  (∀ c : ℝ, IsRealEntryPolynomial fun _ : J → specialUnitary => (c : ℂ)) ∧
  (∀ F H : (J → specialUnitary) → ℂ, IsRealEntryPolynomial F → IsRealEntryPolynomial H →
    IsRealEntryPolynomial (fun u => F u + H u) ∧ IsRealEntryPolynomial (fun u => F u * H u)) ∧
  (∀ (c : ℝ) (F : (J → specialUnitary) → ℂ), IsRealEntryPolynomial F →
    IsRealEntryPolynomial fun u => (c : ℂ) * F u) ∧
  (∀ u u' : J → specialUnitary, u ≠ u' →
    ∃ F : (J → specialUnitary) → ℂ, IsRealEntryPolynomial F ∧ F u ≠ F u') ∧
  ∀ (f : C(J → specialUnitary, ℝ)) (ε : ℝ), 0 < ε →
    ∃ F : (J → specialUnitary) → ℂ, IsRealEntryPolynomial F ∧ ∀ u, ‖F u - (f u : ℂ)‖ < ε
variable (J) in
def RealPolyDisjointUnionSplit : Prop :=
  ∀ (n : ℕ) (P : Fin n → Set J), (∀ ρ, (P ρ).Nonempty) → Pairwise (Function.onFun Disjoint P) →
    (⋃ ρ, P ρ) = Set.univ → ∀ F : (J → specialUnitary) → ℂ, IsRealEntryPolynomial F →
      ∃ (m : ℕ) (f : Fin m → (ρ : Fin n) → (↥(P ρ) → specialUnitary) → ℂ),
        (∀ k ρ, IsRealEntryPolynomial (f k ρ)) ∧
        ∀ u, F u = ∑ k, ∏ ρ, f k ρ (restrictTo (P ρ) u)
def TensorOneSeriesConverges (B : Set J) (X : HaarL2 ↥B →L[ℂ] HaarL2 ↥B) : Prop :=
  (∀ F : HaarL2 J,
    (∀ γ : PeterWeylIndex ↥Bᶜ,
      MemLp (partialCoeff B γ F) 2 (haarPi ↥B) ∧
      MemLp (tensorFn B (X (toHaarL2 (partialCoeff B γ F))) (peterWeylFn γ)) 2
        (haarPi J)) ∧
    Summable (tensorSeriesTerm B X F) ∧
    tensorOne B X F = tensorOneApply B X F) ∧
  ‖tensorOne B X‖ ≤ ‖X‖
open Classical in
def TensorOneOnProducts (B : Set J) (X : HaarL2 ↥B →L[ℂ] HaarL2 ↥B) : Prop :=
  (∀ (φ : HaarL2 ↥B) (ω : HaarL2 ↥Bᶜ),
    MemLp (tensorFn B φ ω) 2 (haarPi J) ∧
    tensorOne B X (toHaarL2 (tensorFn B φ ω)) =
      toHaarL2 (tensorFn B (X φ) ω)) ∧
  ∀ (α α' : PeterWeylIndex ↥B) (γ γ' : PeterWeylIndex ↥Bᶜ),
    peterWeylEntry (tensorOne B X) (glue B α γ) (glue B α' γ') =
      peterWeylEntry X α α' * if γ = γ' then 1 else 0
variable (J) in
def OpDeterminedByEntries : Prop :=
  ∀ A A' : HaarL2 J →L[ℂ] HaarL2 J,
    (∀ α α' : PeterWeylIndex J, peterWeylEntry A α α' = peterWeylEntry A' α α') → A = A'
def TensorOneKernelOp (B : Set J) (X : HaarL2 ↥B →L[ℂ] HaarL2 ↥B) : Prop :=
  ∀ K : C((↥B → specialUnitary) × (↥B → specialUnitary), ℂ), X = Schatten.kernelOp (haarPi ↥B) K →
    (∀ F : HaarL2 J, ∀ᵐ u ∂haarPi J,
      tensorOne B X F u = ∫ v', K (restrictTo B u, v') *
        F (glue B v' (restrictTo Bᶜ u)) ∂haarPi ↥B) ∧
    ∀ F : C(J → specialUnitary, ℂ),
      Continuous fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) =>
        ∫ v', K (p.1, v') * F (glue B v' p.2) ∂haarPi ↥B
def TensorOneDisjointCommute (B : Set J) (X : HaarL2 ↥B →L[ℂ] HaarL2 ↥B) : Prop :=
  ∀ B' : Set J, B'.Nonempty → B' ⊆ Bᶜ →
    ∀ X' : HaarL2 ↥B' →L[ℂ] HaarL2 ↥B',
      Commute (tensorOne B X) (tensorOne B' X')
end Requirements
end SpinHarmonics.SeveralVariables
end YangMills.Construction
end
