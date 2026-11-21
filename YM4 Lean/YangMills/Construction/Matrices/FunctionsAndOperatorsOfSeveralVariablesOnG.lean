import YangMills.Construction.HilbertSpace.SchattenTraceKernels
import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction
namespace SpinHarmonics
instance haarPi_isProbabilityMeasure (ι : Type) [Countable ι] :
    IsProbabilityMeasure (haarPi ι) := by
  unfold haarPi
  infer_instance
instance specialUnitary_secondCountableTopology : SecondCountableTopology specialUnitary :=
  haveI : SecondCountableTopology ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _
abbrev HaarL2 (ι : Type) [Countable ι] : Type := Lp ℂ 2 (haarPi ι)
def toHaarL2 {ι : Type} [Countable ι] (f : (ι → specialUnitary) → ℂ) : HaarL2 ι :=
  open Classical in if hf : MemLp f 2 (haarPi ι) then hf.toLp f else 0
section Products
variable {ι : Type} [Finite ι]
def weightSum (s : ι → HalfNatural) : ℝ := ∑ᶠ i, (s i).toReal
theorem continuous_finprod_apply_coord (f : ι → specialUnitary → ℂ) (hf : ∀ i, Continuous (f i)) :
    Continuous fun g : ι → specialUnitary => ∏ᶠ i, f i (g i) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  simp only [finprod_eq_prod_of_fintype]
  exact continuous_finsetProd _ fun i _ => (hf i).comp (continuous_apply i)
def coordProduct (φ : ι → C(specialUnitary, ℂ)) : C(ι → specialUnitary, ℂ) :=
  ⟨fun g => ∏ᶠ i, φ i (g i), continuous_finprod_apply_coord _ fun i => (φ i).continuous⟩
def prodCoeffSpan (s : ι → HalfNatural) : Submodule ℂ C(ι → specialUnitary, ℂ) :=
  Submodule.span ℂ {F | ∃ φ : ι → C(specialUnitary, ℂ), (∀ i, φ i ∈ coeffSpan (s i)) ∧
    F = coordProduct φ}
def isotypicKernel (s : ι → HalfNatural) (g h : ι → specialUnitary) : ℂ :=
  ∏ᶠ i, ((2 * (s i).toReal + 1 : ℝ) : ℂ) * spinCharacter (s i) (g i * (h i)⁻¹)
def isotypicProj (s : ι → HalfNatural) : HaarL2 ι →L[ℂ] HaarL2 ι :=
  Schatten.kernelOp (haarPi ι) fun p => isotypicKernel s p.1 p.2
theorem finite_setOf_toReal_le (κ : HalfNatural) :
    {t : HalfNatural | t.toReal ≤ κ.toReal}.Finite := by
  refine (Set.finite_range fun n : Fin (κ.doubled + 1) => (⟨n⟩ : HalfNatural)).subset fun t ht => ?_
  have hle : t.doubled ≤ κ.doubled := by
    have h₁ : (t.doubled : ℝ) / 2 ≤ (κ.doubled : ℝ) / 2 := ht
    have h₂ : (t.doubled : ℝ) ≤ κ.doubled := by linarith
    exact_mod_cast h₂
  exact ⟨⟨t.doubled, Nat.lt_succ_of_le hle⟩, rfl⟩
variable (ι) in
theorem finite_weightsBounded (κ : HalfNatural) :
    {s : ι → HalfNatural | ∀ i, (s i).toReal ≤ κ.toReal}.Finite :=
  Set.Finite.pi' fun _ => finite_setOf_toReal_le κ
variable (ι) in
def boundedWeights (κ : HalfNatural) : Finset (ι → HalfNatural) :=
  (finite_weightsBounded ι κ).toFinset
theorem mem_boundedWeights {κ : HalfNatural} {s : ι → HalfNatural} :
    s ∈ boundedWeights ι κ ↔ ∀ i, (s i).toReal ≤ κ.toReal :=
  Set.Finite.mem_toFinset _
variable (ι) in
def truncationProj (κ : HalfNatural) : HaarL2 ι →L[ℂ] HaarL2 ι :=
  ∑ s ∈ boundedWeights ι κ, isotypicProj s
def truncationKernel (κ : HalfNatural) (g h : ι → specialUnitary) : ℂ :=
  ∑ s ∈ boundedWeights ι κ, isotypicKernel s g h
variable (ι) in
def truncatedCoeffSpan (κ : HalfNatural) : Submodule ℂ C(ι → specialUnitary, ℂ) :=
  ⨆ s ∈ boundedWeights ι κ, prodCoeffSpan s
variable (ι) in
def truncatedDim (κ : HalfNatural) : ℝ :=
  ∑ s ∈ boundedWeights ι κ, ∏ᶠ i, (2 * (s i).toReal + 1) ^ 2
end Products
structure PeterWeylLabel where
  spin : HalfNatural
  rowIdx : Fin (spin.doubled + 1)
  colIdx : Fin (spin.doubled + 1)
abbrev PeterWeylIndex (ι : Type) : Type := ι → PeterWeylLabel
section Basis
variable {ι : Type} [Finite ι]
def spins (α : PeterWeylIndex ι) : ι → HalfNatural := fun i => (α i).spin
def normalizedCoeff (e : PeterWeylLabel) : C(specialUnitary, ℂ) :=
  ((Real.sqrt (2 * e.spin.toReal + 1) : ℝ) : ℂ) • spinCoeffMap e.spin e.rowIdx e.colIdx
def peterWeylFn (α : PeterWeylIndex ι) : C(ι → specialUnitary, ℂ) :=
  coordProduct fun i => normalizedCoeff (α i)
def peterWeylVec (α : PeterWeylIndex ι) : HaarL2 ι :=
  ContinuousMap.toLp (E := ℂ) 2 (haarPi ι) ℂ (peterWeylFn α)
theorem finite_labelsBounded (κ : HalfNatural) :
    {e : PeterWeylLabel | e.spin.toReal ≤ κ.toReal}.Finite := by
  have hfin : Finite {t : HalfNatural // t.toReal ≤ κ.toReal} :=
    (finite_setOf_toReal_le κ).to_subtype
  refine Set.Finite.subset (Set.finite_range fun x :
    (Σ t : {t : HalfNatural // t.toReal ≤ κ.toReal}, Fin (t.1.doubled + 1) × Fin (t.1.doubled + 1)) =>
      (⟨x.1.1, x.2.1, x.2.2⟩ : PeterWeylLabel)) ?_
  · rintro ⟨t, a, c⟩ ht
    exact ⟨⟨⟨t, ht⟩, a, c⟩, rfl⟩
variable (ι) in
theorem finite_indicesBounded (κ : HalfNatural) :
    {α : PeterWeylIndex ι | ∀ i, (α i).spin.toReal ≤ κ.toReal}.Finite :=
  Set.Finite.pi' fun _ => finite_labelsBounded κ
variable (ι) in
def boundedIndices (κ : HalfNatural) : Finset (PeterWeylIndex ι) :=
  (finite_indicesBounded ι κ).toFinset
theorem mem_boundedIndices {κ : HalfNatural} {α : PeterWeylIndex ι} :
    α ∈ boundedIndices ι κ ↔ ∀ i, (α i).spin.toReal ≤ κ.toReal :=
  Set.Finite.mem_toFinset _
def peterWeylEntry (T : HaarL2 ι →L[ℂ] HaarL2 ι) (α β : PeterWeylIndex ι) : ℂ :=
  inner ℂ (peterWeylVec α) (T (peterWeylVec β))
end Basis
section Part
variable {ι : Type}
def restrictTo {X : Type*} (S : Set ι) (g : ι → X) : ↥S → X := fun i => g i
open Classical in
def glue {X : Type*} (S : Set ι) (v : ↥S → X) (w : ↥Sᶜ → X) : ι → X :=
  fun i => if hi : i ∈ S then v ⟨i, hi⟩ else w ⟨i, hi⟩
theorem glue_of_mem {X : Type*} (S : Set ι) (v : ↥S → X) (w : ↥Sᶜ → X) (i : ↥S) :
    glue S v w i = v i :=
  dif_pos i.2
theorem glue_of_notMem {X : Type*} (S : Set ι) (v : ↥S → X) (w : ↥Sᶜ → X) (i : ↥Sᶜ) :
    glue S v w i = w i :=
  dif_neg i.2
def splitEquiv {X : Type*} (S : Set ι) : (ι → X) ≃ (↥S → X) × (↥Sᶜ → X) where
  toFun g := (restrictTo S g, restrictTo Sᶜ g)
  invFun p := glue S p.1 p.2
  left_inv g := by
    funext i
    by_cases hi : i ∈ S
    · exact glue_of_mem S _ _ ⟨i, hi⟩
    · exact glue_of_notMem S _ _ ⟨i, hi⟩
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext i
      exact glue_of_mem S _ _ i
    · funext i
      exact glue_of_notMem S _ _ i
def tensorFn (S : Set ι) (φ : (↥S → specialUnitary) → ℂ) (ω : (↥Sᶜ → specialUnitary) → ℂ)
    (g : ι → specialUnitary) : ℂ :=
  φ (restrictTo S g) * ω (restrictTo Sᶜ g)
theorem tensorFn_glue (S : Set ι) (φ : (↥S → specialUnitary) → ℂ) (ω : (↥Sᶜ → specialUnitary) → ℂ)
    (v : ↥S → specialUnitary) (w : ↥Sᶜ → specialUnitary) :
    tensorFn S φ ω (glue S v w) = φ v * ω w := by
  have h := (splitEquiv (X := specialUnitary) S).right_inv (v, w)
  have h₁ : restrictTo S (glue S v w) = v := congrArg Prod.fst h
  have h₂ : restrictTo Sᶜ (glue S v w) = w := congrArg Prod.snd h
  rw [tensorFn, h₁, h₂]
variable [Finite ι]
theorem finprod_eq_mul_finprod_subtype_compl (S : Set ι) (f : ι → ℂ) :
    ∏ᶠ i, f i = (∏ᶠ i : ↥S, f i) * ∏ᶠ i : ↥Sᶜ, f i := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  simp only [finprod_eq_prod_of_fintype]
  exact (Fintype.prod_subtype_mul_prod_subtype (· ∈ S) f).symm
theorem peterWeylFn_glue (S : Set ι) (α : PeterWeylIndex ↥S) (γ : PeterWeylIndex ↥Sᶜ)
    (g : ι → specialUnitary) :
    peterWeylFn (glue S α γ) g = tensorFn S (peterWeylFn α) (peterWeylFn γ) g := by
  change (∏ᶠ i, normalizedCoeff (glue S α γ i) (g i)) =
    (∏ᶠ i : ↥S, normalizedCoeff (α i) (g i)) * ∏ᶠ i : ↥Sᶜ, normalizedCoeff (γ i) (g i)
  rw [finprod_eq_mul_finprod_subtype_compl S]
  congr 1
  · exact finprod_congr fun i => by rw [glue_of_mem]
  · exact finprod_congr fun i => by rw [glue_of_notMem]
def partialCoeff (S : Set ι) (γ : PeterWeylIndex ↥Sᶜ) (F : HaarL2 ι)
    (v : ↥S → specialUnitary) : ℂ :=
  ∫ w, star (peterWeylFn γ w) * F (glue S v w) ∂haarPi ↥Sᶜ
def tensorSeriesTerm (S : Set ι) (T : HaarL2 ↥S →L[ℂ] HaarL2 ↥S)
    (F : HaarL2 ι) (γ : PeterWeylIndex ↥Sᶜ) : HaarL2 ι :=
  toHaarL2 (tensorFn S (T (toHaarL2 (partialCoeff S γ F))) (peterWeylFn γ))
def applyOnAll (S : Set ι) (hS : ∀ i, i ∈ S)
    (T : HaarL2 ↥S →L[ℂ] HaarL2 ↥S) (F : HaarL2 ι) : HaarL2 ι :=
  toHaarL2 fun g => T (toHaarL2 fun v => F fun i => v ⟨i, hS i⟩) (restrictTo S g)
open Classical in
def tensorOneApply (S : Set ι) (T : HaarL2 ↥S →L[ℂ] HaarL2 ↥S)
    (F : HaarL2 ι) : HaarL2 ι :=
  if hS : ∀ i, i ∈ S then applyOnAll S hS T F else ∑' γ, tensorSeriesTerm S T F γ
def tensorOne (S : Set ι) (T : HaarL2 ↥S →L[ℂ] HaarL2 ↥S) : HaarL2 ι →L[ℂ] HaarL2 ι :=
  Classical.epsilon fun U => ∀ F, U F = tensorOneApply S T F
def pullFromPart (S : Set ι) (f : (↥S → specialUnitary) → ℂ) (g : ι → specialUnitary) : ℂ :=
  f (restrictTo S g)
end Part
section Polynomials
variable {ι : Type} [Finite ι]
def IsRealEntryPolynomial (F : (ι → specialUnitary) → ℂ) : Prop :=
  IsEntryPolynomial F ∧ ∀ g, (F g).im = 0
def entryFns : Set (specialUnitary → ℂ) :=
  {f | ∃ a b : Fin 2, f = (fun g : specialUnitary => (g : ComplexMatrix2) a b) ∨
    f = (fun g : specialUnitary => star ((g : ComplexMatrix2) a b)) ∨
    f = fun g : specialUnitary => ((g⁻¹ : specialUnitary) : ComplexMatrix2) a b}
def IsEntryMonomial (d : ℕ) (M : specialUnitary → ℂ) : Prop :=
  ∃ w : List (specialUnitary → ℂ), w.length ≤ d ∧ (∀ f ∈ w, f ∈ entryFns) ∧
    ∀ g, M g = (w.map fun f => f g).prod
def HasDegreeBound (d : ι → ℕ) (F : (ι → specialUnitary) → ℂ) : Prop :=
  IsEntryPolynomial F ∧ F ∈ Submodule.span ℂ {P : (ι → specialUnitary) → ℂ |
    ∃ M : ι → specialUnitary → ℂ, (∀ i, IsEntryMonomial (d i) (M i)) ∧ P = fun g => ∏ᶠ i, M i (g i)}
end Polynomials
end SpinHarmonics
end YangMills.Construction
