import YangMills.Construction.EuclideanFunctionals.PulledDownNormsTheInsertionValueAndClassesOfTensors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.HeightTuples
def ComponentsMatchAbove (c : ℝ) (F : FreeSep) : Prop :=
  ∃ F' ∈ finCombIn {x | c < x 3}, SameTensors F' F
def disjointTensorsAbove (c : ℝ) (q : ℕ) : Set (TestSpaces.PointTuple q → ℂ) :=
  {A | ∃ f : Fin q → R4 → ℝ, (∀ l, f l ∈ C1c ℝ) ∧
    (Pairwise fun k l => Disjoint (supp (f k)) (supp (f l))) ∧
    (∀ l, supp (f l) ⊆ {x | c < x 3}) ∧
    A = tensorOfFns fun l x => ((f l x : ℝ) : ℂ)}
def SpannedByTensorsAbove (c : ℝ) (F : FreeSep) : Prop :=
  ∀ q, 1 ≤ q → tensorComp q F ∈ Submodule.span ℂ (disjointTensorsAbove c q)
def ComponentsSupportedAbove (c : ℝ) (F : FreeSep) : Prop :=
  ∀ q, 1 ≤ q → tsupport (tensorComp q F) ⊆ {x | ∀ l, c < x l 3}
def HeightConditionsEquiv (c : ℝ) : Prop :=
  ∀ F ∈ finCombIn upperHalf,
    (ComponentsMatchAbove c F ↔ SpannedByTensorsAbove c F) ∧
      (ComponentsMatchAbove c F ↔ ComponentsSupportedAbove c F)
variable {m : SharpScale} {S : ConnFamily}
def ValueDependsOnComponents (S : ConnFamily) : Prop :=
  ∀ F' F'' : FreeSep, SameTensors F' F'' →
    centeredFnFree S F' = centeredFnFree S F''
def FormsClassesDependOnComponents (σ : EuclidFunctionalWithRecon m S) : Prop :=
  ∀ F' ∈ finCombIn upperHalf, ∀ F'' ∈ finCombIn upperHalf,
    SameTensors F' F'' →
      (∀ A ∈ finCombIn upperHalf,
        osForm S F' A = osForm S F'' A ∧
          osForm S A F' = osForm S A F'') ∧
      reconClass σ F' = reconClass σ F''
def AgreeAtHeight (σ : EuclidFunctionalWithRecon m S) (c : ℝ)
    (F' F'' : FreeSep) : Prop :=
  reconClass σ (pullDown c F') = reconClass σ (pullDown c F'') ∧
    heightNorm σ c F' = heightNorm σ c F'' ∧
    ∀ A ∈ finCombIn {x | c < x 3}, ∀ h ∈ C1c ℂ,
      supp h ⊆ {x | |x 3| < c} →
        insertion S F' h A = insertion S F'' h A ∧
          insertion S A h F' = insertion S A h F''
def DependsOnComponents (σ : EuclidFunctionalWithRecon m S) (c : ℝ) : Prop :=
  ValueDependsOnComponents S ∧ FormsClassesDependOnComponents σ ∧
    (∀ F' ∈ finCombIn {x | c < x 3}, ∀ F'' ∈ finCombIn {x | c < x 3},
      SameTensors F' F'' → AgreeAtHeight σ c F' F'') ∧
    ∀ F ∈ finCombIn upperHalf, ComponentsSupportedAbove c F →
      ∀ F' ∈ finCombIn {x | c < x 3}, SameTensors F' F →
        reconClass σ F' = reconClass σ F ∧
          ∀ F'' ∈ finCombIn {x | c < x 3}, SameTensors F'' F →
            AgreeAtHeight σ c F' F''
def liftedSet (c : ℝ) : Set FreeSep :=
  {F | F ∈ finCombIn upperHalf ∧ ComponentsMatchAbove c F}
def raise (c : ℝ) : FreeSep →ₗ[ℂ] FreeSep := (EuclidMotion.transl (c • timeVec)).actFree
def RaiseBijectiveModNull (c : ℝ) (W : Submodule ℂ FreeSep) : Prop :=
  (∀ A ∈ finCombIn upperHalf, raise c A ∈ W) ∧
    (∀ A ∈ finCombIn upperHalf, ∀ A' ∈ finCombIn upperHalf,
      IsNullElem (A - A') ↔ IsNullElem (raise c A - raise c A')) ∧
    (∀ G ∈ W, ∃ A ∈ finCombIn upperHalf, IsNullElem (G - raise c A)) ∧
    ∀ F ∈ finCombIn {x | c < x 3},
      pullDown c F ∈ finCombIn upperHalf ∧
        ∀ A ∈ finCombIn upperHalf,
          (IsNullElem (raise c A - F) ↔ IsNullElem (A - pullDown c F))
def LiftedSubspace (c : ℝ) : Prop :=
  ∃ W : Submodule ℂ FreeSep, (W : Set FreeSep) = liftedSet c ∧
    finCombIn {x | c < x 3} ≤ W ∧
    (∀ N ∈ finCombIn upperHalf, IsNullElem N → N ∈ W) ∧
    (∀ G ∈ W, ∃ F ∈ finCombIn {x | c < x 3}, ∃ N ∈ finCombIn upperHalf,
      IsNullElem N ∧ G = F + N) ∧
    (∀ A ∈ finCombIn upperHalf, IsNullElem A ↔ IsNullElem (raise c A)) ∧
    RaiseBijectiveModNull c W
def PullDownClassesDense (σ : EuclidFunctionalWithRecon m S) (c : ℝ) : Prop :=
  {v | ∃ F ∈ finCombIn {x | c < x 3}, v = reconClass σ (pullDown c F)} =
      {v | ∃ A ∈ finCombIn upperHalf, v = reconClass σ A} ∧
    Dense {v | ∃ A ∈ finCombIn upperHalf, v = reconClass σ A}
def HeightTuplesLemma : Prop :=
  ∀ c : ℝ, 0 < c →
    HeightConditionsEquiv c ∧ LiftedSubspace c ∧
      ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S),
        DependsOnComponents σ c ∧ PullDownClassesDense σ c
end YangMills.Construction.EuclideanFunctionals.HeightTuples
