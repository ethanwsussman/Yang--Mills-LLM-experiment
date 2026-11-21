import YangMills.Construction.Continuum.ReflectionOfTestFunctionsTensorsAndOrderZero
import Reconstruction.MinkowskiSpace.ScalarProductsAndDensityOfTheTensorVectors
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.TensorVecInner
theorem valToFun_tensorVal {m : ℕ} (f : Fin m → (Fin 4 → ℝ) → ℂ) :
    HyperplaneReflection.valToFun (RealPointVectors.tensorVal f) = TestSpaces.tensorProd f :=
  HyperplaneReflection.valToFun_funToVal _
theorem valToFun_starVal_tensorVal {m : ℕ} (g : Fin m → (Fin 4 → ℝ) → ℂ) :
    HyperplaneReflection.valToFun (RealPointVectors.starVal (RealPointVectors.tensorVal g)) =
      TestSpaces.tensorProd fun i x => conj (g (Fin.rev i) x) := by
  cases m with
  | zero =>
    funext x
    simp [HyperplaneReflection.valToFun, RealPointVectors.starVal, RealPointVectors.starScalar,
      RealPointVectors.tensorVal, HyperplaneReflection.funToVal, TestSpaces.tensorProd]
  | succ m =>
    funext y
    show conj (TestSpaces.tensorProd g fun i => y (Fin.rev i)) = _
    simp only [TestSpaces.tensorProd, map_prod]
    exact Fintype.prod_equiv Fin.revPerm _ _ fun i => by simp
theorem tensorFun_tensorProd {k m : ℕ} (a : Fin k → (Fin 4 → ℝ) → ℂ)
    (b : Fin m → (Fin 4 → ℝ) → ℂ) :
    TestSpaces.tensorFun (TestSpaces.tensorProd a) (TestSpaces.tensorProd b) =
      TestSpaces.tensorProd (Fin.append a b) := by apply _root_.YangMills.Construction.TorusTransport.TestFunctionOrders.tensor_prodTensor <;> assumption
theorem tensorVal_starVal_tensorVal {k m : ℕ} (g : Fin k → (Fin 4 → ℝ) → ℂ)
    (f : Fin m → (Fin 4 → ℝ) → ℂ) :
    HyperplaneReflection.tensorVal (RealPointVectors.starVal (RealPointVectors.tensorVal g))
        (RealPointVectors.tensorVal f) =
      RealPointVectors.tensorVal (Fin.append (fun i x => conj (g (Fin.rev i) x)) f) := by
  rw [HyperplaneReflection.tensorVal, valToFun_starVal_tensorVal, valToFun_tensorVal,
    tensorFun_tensorProd]
  rfl
section InnerForm
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) (Ω : K)
  (A : ℝ → OneLoopNotation.BddOp K)
theorem image_tensorDomainIn :
    Subtype.val '' (FieldFormHilbert.tensorDomainIn E Ω A :
        Set (FieldFormHilbert.tensorHilbert E Ω A)) =
      (RealPointVectors.tensorDomain E Ω A : Set K) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hv
    exact ⟨⟨v, Submodule.le_topologicalClosure _ hv⟩, hv, rfl⟩
theorem image_range_tensorVec :
    (FieldFormHilbert.tensorHilbert E Ω A).subtype ''
        (Set.range fun p : Σ m : ℕ, (Fin m → WightmanTheory.TestFn) =>
          FieldFormHilbert.tensorVec E Ω A p.2) =
      RealPointVectors.tensorStates E Ω A := by
  ext v
  constructor
  · rintro ⟨_, ⟨⟨m, g⟩, rfl⟩, rfl⟩
    exact ⟨m, fun i => (g i).1, fun i => (g i).2, rfl⟩
  · rintro ⟨m, f, hf, rfl⟩
    exact ⟨_, ⟨⟨m, fun i => ⟨f i, hf i⟩⟩, rfl⟩, rfl⟩
theorem tensorDomainIn_eq_span : FieldFormHilbert.tensorDomainIn E Ω A = Submodule.span ℂ
    (Set.range fun p : Σ m : ℕ, (Fin m → WightmanTheory.TestFn) =>
      FieldFormHilbert.tensorVec E Ω A p.2) := by
  apply Submodule.map_injective_of_injective
    (FieldFormHilbert.tensorHilbert E Ω A).injective_subtype
  rw [Submodule.map_span, image_range_tensorVec, FieldFormHilbert.tensorDomainIn,
    Submodule.map_comap_subtype]
  exact inf_eq_right.mpr (Submodule.le_topologicalClosure _)
theorem dense_tensorDomainIn :
    Dense (FieldFormHilbert.tensorDomainIn E Ω A :
      Set (FieldFormHilbert.tensorHilbert E Ω A)) := by
  intro x
  rw [closure_subtype, image_tensorDomainIn]
  exact x.2
theorem eq_zero_of_inner_tensorVec_eq_zero (v : FieldFormHilbert.tensorHilbert E Ω A)
    (hv : v ∈ FieldFormHilbert.tensorDomainIn E Ω A)
    (hperp : ∀ (m : ℕ) (g : Fin m → WightmanTheory.TestFn),
      ⟪FieldFormHilbert.tensorVec E Ω A g, v⟫_ℂ = 0) : v = 0 := by
  have hall : ∀ w ∈ FieldFormHilbert.tensorDomainIn E Ω A, ⟪w, v⟫_ℂ = 0 := by
    intro w hw
    rw [tensorDomainIn_eq_span] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact hperp p.1 p.2
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  exact inner_self_eq_zero.mp (hall v hv)
end InnerForm
theorem claim_holds (hV : RealPointVectors.BoundaryVectorsStatement) : Claim := by
  intro K _ _ _ E Ω A P C hF
  have V := hV E Ω A P C hF
  refine
    { conj_mem_schwartz := ?_
      tensorVec_fin_zero := ?_
      inner_tensorVec := ?_
      domain_eq_span := tensorDomainIn_eq_span E Ω A
      dense_domain := dense_tensorDomainIn E Ω A
      eq_zero_of_inner_eq_zero := eq_zero_of_inner_tensorVec_eq_zero E Ω A }
  · intro f
    have h := V.starVal_mem 1 (WightmanTheory.asOnePointFn f.1) f.2
    have e : WightmanTheory.asOnePointFn (fun x => conj (f.1 x)) =
        RealPointVectors.starFun (WightmanTheory.asOnePointFn f.1) := by
      funext y
      simp [WightmanTheory.asOnePointFn, RealPointVectors.starFun]
    show WightmanTheory.asOnePointFn (fun x => conj (f.1 x)) ∈ TestSpaces.schwartzSet 1
    rw [e]
    exact h
  · intro f
    show WightmanReconstruction.scalarOfOrderZero
      (RealPointVectors.tensorVal fun i => (f i).1) • Ω = Ω
    have e : WightmanReconstruction.scalarOfOrderZero
        (RealPointVectors.tensorVal fun i => (f i).1) = 1 := by
      simp [WightmanReconstruction.scalarOfOrderZero, RealPointVectors.tensorVal,
        HyperplaneReflection.funToVal, TestSpaces.tensorProd]
    rw [e, one_smul]
  · intro k m g f
    have e := V.inner_testState_eq k m (RealPointVectors.tensorVal fun i => (g i).1)
      (RealPointVectors.tensorVal fun i => (f i).1)
      (V.tensorVal_mem k _ fun i => (g i).2) (V.tensorVal_mem m _ fun i => (f i).2)
    rw [tensorVal_starVal_tensorVal] at e
    exact e
end YangMills.Construction.TensorVecInner
