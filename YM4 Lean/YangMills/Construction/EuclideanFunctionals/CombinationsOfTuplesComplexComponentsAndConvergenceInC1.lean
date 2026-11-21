import YangMills.Construction.EuclideanFunctionals.TensorsAndTensorComponentsOfTheFreeSpace
import Mathlib
set_option autoImplicit false
open Filter
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
def spatialProj : R4 →ₗ[ℝ] Fin 3 → ℝ := LinearMap.funLeft ℝ ℝ Fin.castSucc
theorem spatialProj_timeFlip (x : R4) :
    spatialProj (timeFlip x) = spatialProj x ∧ timeFlip x 3 = -x 3 := by
  constructor
  · funext i
    fin_cases i <;> simp [spatialProj, LinearMap.funLeft, timeFlip_apply, PeriodicLattice.coordVec]
  · rw [timeFlip_apply]
    simp [PeriodicLattice.coordVec]
    ring
def sepNIn (n : ℕ) (O : Set R4) : Set FnList := sepN n ∩ sepIn O
def finCombIn (O : Set R4) : Submodule ℂ FreeSep :=
  Finsupp.supported ℂ ℂ {X : sepAll | X.1 ∈ sepIn O}
theorem finCombIn_eq_freeSpanIn (O : Set R4) : finCombIn O = freeSpanIn O := by
  apply le_antisymm
  · rw [finCombIn, Finsupp.supported_eq_span_single]
    refine Submodule.span_mono ?_
    rintro _ ⟨X, hX, rfl⟩
    exact ⟨X.1, hX, toFree_of_mem X.2⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨X, hX, rfl⟩
    rw [toFree_of_mem hX.1]
    exact Finsupp.single_mem_supported ℂ 1 hX
def combSupp (F : FreeSep) : Set R4 :=
  ⋃ X ∈ F.support, ⋃ f ∈ X.1, supp f
def MulDefined (F A : FreeSep) : Prop :=
  Disjoint (combSupp F) (combSupp A)
def freeMul3 (F A A' : FreeSep) : FreeSep := freeMul (freeMul F A) A'
def reOrImPart (ε : Fin 2) (h : R4 → ℂ) : R4 → ℝ :=
  if ε = 0 then fun x => (h x).re else fun x => (h x).im
def IsRealValued (h : R4 → ℂ) : Prop := ∀ x, (h x).im = 0
structure ComplexComponents {n : ℕ} (h : Fin n → R4 → ℂ) : Prop where
  one_le : 1 ≤ n
  mem : ∀ l, h l ∈ C1c ℂ
  disjoint : Pairwise fun k l => Disjoint (supp (h k)) (supp (h l))
open Classical in
def admissibleSigns {n : ℕ} (h : Fin n → R4 → ℂ) : Finset (Fin n → Fin 2) :=
  Finset.univ.filter fun ε => ∀ l, IsRealValued (h l) → ε l = 0
open Classical in
def complexTuple {n : ℕ} (h : Fin n → R4 → ℂ) : FreeSep :=
  if ∀ l, IsRealValued (h l) then toFree (List.ofFn fun l x => (h l x).re)
  else ∑ ε ∈ admissibleSigns h,
    (Complex.I ^ ∑ l, (ε l : ℕ)) • toFree (List.ofFn fun l => reOrImPart (ε l) (h l))
def IsNullElem (F : FreeSep) : Prop :=
  tensorCompZero F = 0 ∧ ∀ q, 1 ≤ q → tensorComp q F = 0
def sepTensors (q : ℕ) : Set (TestSpaces.PointTuple q → ℂ) :=
  {A | ∃ h : Fin q → R4 → ℂ, (∀ l, h l ∈ C1c ℂ) ∧
    (Pairwise fun k l => Disjoint (supp (h k)) (supp (h l))) ∧ A = tensorOfFns h}
open Classical in
def sepTensorSpan (q : ℕ) : Submodule ℂ (TestSpaces.PointTuple q → ℂ) :=
  if q = 0 then ⊤ else Submodule.span ℂ (sepTensors q)
def translateArgs (z : R4) {q : ℕ} (A : TestSpaces.PointTuple q → ℂ) :
    TestSpaces.PointTuple q → ℂ :=
  fun x => A fun l => x l - z
theorem translateArgs_zero (z : R4) (A : TestSpaces.PointTuple 0 → ℂ) :
    translateArgs z A = A := by
  funext x
  exact congrArg A (funext fun l => l.elim0)
def flipConj (F : FreeSep) : FreeSep := timeFlip.actFree (freeConj F)
def TendstoC1 (hs : ℕ → R4 → ℂ) (h : R4 → ℂ) : Prop :=
  TendstoUniformly hs h atTop ∧
    ∀ μ : Fin 4, TendstoUniformly (fun j x => fderiv ℝ (hs j) x (Pi.single μ 1))
      (fun x => fderiv ℝ h x (Pi.single μ 1)) atTop
end YangMills.Construction.EuclideanFunctionals
