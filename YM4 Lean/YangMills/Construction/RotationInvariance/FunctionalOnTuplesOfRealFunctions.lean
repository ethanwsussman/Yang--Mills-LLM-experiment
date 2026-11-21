import YangMills.Construction.EuclideanFunctionals.MotionsConcatenationAndComplexComponents
import YangMills.Construction.RotationInvariance.ApertureTimeGapsAndComplexAnalysisInThePlane
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.RealTuples
def ofRealFns {n : ℕ} (h : Fin n → R4 → ℝ) : FreeSep :=
  complexTuple (cplxEntries (List.ofFn h) List.length_ofFn)
def ofRealFn (f : R4 → ℝ) : FreeSep :=
  ofRealFns fun _ : Fin 1 => f
def singletonsOf {n : ℕ} (h : Fin n → R4 → ℝ) : List FreeSep :=
  List.ofFn fun l => ofRealFn (h l)
def LinearInArgument (S : ConnFamily) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (i : Fin n) (f : Fin n → R4 → ℝ) (g : R4 → ℝ),
    List.ofFn f ∈ sepN n → List.ofFn (Function.update f i g) ∈ sepN n →
    ∀ a a' : ℝ,
      List.ofFn (Function.update f i (a • f i + a' • g)) ∈ sepN n ∧
      centeredAt S (List.ofFn (Function.update f i (a • f i + a' • g))) =
        a * centeredAt S (List.ofFn f) +
          a' * centeredAt S (List.ofFn (Function.update f i g))
def RealAndZeroAtZeroComponent (S : ConnFamily) : Prop :=
  ∀ X ∈ sepAll, centeredFnFree S (toFree X) = (centeredAt S X : ℂ) ∧
    ((0 : R4 → ℝ) ∈ X → centeredAt S X = 0)
def RealTupleEvaluations {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ h : Fin n → R4 → ℝ, (∀ l, h l ∈ C1c ℝ) →
    (Pairwise fun k l => Disjoint (supp (h k)) (supp (h l))) →
    List.ofFn h ∈ sepN n ∧
    ComplexComponents (cplxEntries (List.ofFn h) List.length_ofFn) ∧
    centeredFnFree S (ofRealFns h) =
      centeredFnFree S (toFree (List.ofFn h)) ∧
    (∀ (k : ℕ) (hk : k + 1 < n),
      MulDefined
        (Motions.mulLeft
          ((singletonsOf h).take (k + 1)))
        (ofRealFn (h ⟨k + 1, hk⟩))) ∧
    ofRealFns h =
      Motions.mulLeft (singletonsOf h) ∧
    ((∀ l, supp (h l) ⊆ upperHalf) →
      ∃ (hX' : ofRealFns h ∈ finCombIn upperHalf)
        (hX : toFree (List.ofFn h) ∈ finCombIn upperHalf),
        d.base.sigma.recon.cls ⟨ofRealFns h, hX'⟩ =
          d.base.sigma.recon.cls ⟨toFree (List.ofFn h), hX⟩)
def realFunctionTuples : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S),
    LinearInArgument S ∧ RealAndZeroAtZeroComponent S ∧ RealTupleEvaluations d
end YangMills.Construction.EuclideanFunctionals.RealTuples
