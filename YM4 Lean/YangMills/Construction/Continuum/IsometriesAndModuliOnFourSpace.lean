import YangMills.Construction.Continuum.ClassesOfTuples
import YangMills.Construction.Continuum.IsometriesOfFourSpaceAndOfATorusReflectionsAndInducedMaps
import YangMills.Construction.Continuum.TranslationModulus
import Mathlib
set_option autoImplicit false
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction.TorusTransport
def reflectAcross (n : Fin 4 → ℝ) (c : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  x - (2 * (scalarProd n x - c)) • n
def IsRootDirection (n : Fin 4 → ℝ) : Prop :=
  (∃ i : Fin 4, n = basisVec i) ∨
    ∃ i j : Fin 4, i < j ∧
      (n = (Real.sqrt 2)⁻¹ • (basisVec i + basisVec j) ∨
        n = (Real.sqrt 2)⁻¹ • (basisVec i - basisVec j))
def swapLast (i : Fin 4) : hyperoctahedral :=
  ⟨TorusLifts.signedCoordinateEquiv (Equiv.swap i 3) 1, ⟨_, _, rfl⟩⟩
theorem swapLast_apply (i j : Fin 4) (x : Fin 4 → ℝ) :
    (swapLast i).1 x j = x (Equiv.swap i 3 j) := by
  simp [swapLast, signedCoordinateEquiv_apply]
def halfSpaceNormalize (i : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  (swapLast i).1 (x - c • basisVec i)
namespace MotionFacts
variable (D : TransportData)
def CompInvariance (s : (Fin 4 → ℝ) → Fin 4 → ℝ)
    (h : ComplexFun (Fin 4 → ℝ)) : Prop :=
  Domain.euclidean.fnSupport D (h ∘ s) = s ⁻¹' Domain.euclidean.fnSupport D h ∧
    ennSupNorm (h ∘ s) = ennSupNorm h ∧
    Domain.euclidean.lipConst D (h ∘ s) = Domain.euclidean.lipConst D h ∧
    Domain.euclidean.ennSharpNorm D (h ∘ s) = Domain.euclidean.ennSharpNorm D h ∧
    (Domain.euclidean.IsC1On D h → Domain.euclidean.IsC1On D (h ∘ s)) ∧
    (ContDiff ℝ ∞ h → ContDiff ℝ ∞ (h ∘ s))
def AdmissibleSetsInvariance (s : (Fin 4 → ℝ) → Fin 4 → ℝ) {q : ℕ+} (d R : ℝ)
    (hd : 0 < d) (hR : 0 < R) (A : Fin q → Set (Fin 4 → ℝ)) : Prop :=
  IsAdmissibleSets D d R hd hR (fun l => s ⁻¹' A l) ∧
    (fun h : Fin q → RealFun (Fin 4 → ℝ) => familyComp h s) ''
        Set.univ.pi (fun l => lipschitzSupportedIn (A l)) =
      Set.univ.pi (fun l => lipschitzSupportedIn (s ⁻¹' A l)) ∧
    (fun h : Fin q → RealFun (Fin 4 → ℝ) => familyComp h s) ''
        Set.univ.pi (fun l => c1SupportedIn (A l)) =
      Set.univ.pi (fun l => c1SupportedIn (s ⁻¹' A l))
def SepFamiliesInvariance (s : (Fin 4 → ℝ) → Fin 4 → ℝ) (n : ℕ+) : Prop :=
  (fun h : Domain.euclidean.FnFamily D n ℝ => (familyComp h s : Domain.euclidean.FnFamily D n ℝ)) ''
      Domain.euclidean.sepC1Families D n = Domain.euclidean.sepC1Families D n ∧
    ∀ (hn : 2 ≤ (n : ℕ)) (h : Domain.euclidean.FnFamily D n ℝ)
      (hh : h ∈ Domain.euclidean.sepC1Families D n),
      ∃ hs : (familyComp h s : Domain.euclidean.FnFamily D n ℝ) ∈
          Domain.euclidean.sepC1Families D n,
        Domain.euclidean.supportGap D hn (familyComp h s) hs.1 =
          Domain.euclidean.supportGap D hn h hh.1
def MotionInvariance : Prop :=
  ∀ s : (Fin 4 → ℝ) → Fin 4 → ℝ, IsEuclideanMotion s →
    (∀ h : ComplexFun (Fin 4 → ℝ), Domain.euclidean.LipschitzOn D h →
      IsCompact (Domain.euclidean.fnSupport D h) → CompInvariance D s h) ∧
    (∀ (q : ℕ+) (d R : ℝ) (hd : 0 < d) (hR : 0 < R) (A : Fin q → Set (Fin 4 → ℝ)),
      IsAdmissibleSets D d R hd hR A → AdmissibleSetsInvariance D s d R hd hR A) ∧
    ∀ n : ℕ+, SepFamiliesInvariance D s n
def TranslationModulusProps : Prop :=
  ∀ f : realC1Compact,
    Monotone (D.translationModulus f) ∧
    Filter.Tendsto (D.translationModulus f) (𝓝 0) (𝓝 0) ∧
    (∀ a b : Fin 4 → ℝ,
      Domain.euclidean.ennSharpNorm D
          (Domain.euclidean.translateFn D a f.1 - Domain.euclidean.translateFn D b f.1) ≤
        D.translationModulus f (Real.toNNReal (euclidNorm (a - b)))) ∧
    ∀ s : (Fin 4 → ℝ) → Fin 4 → ℝ, IsEuclideanMotion s →
      ∃ hs : f.1 ∘ s ∈ realC1Compact,
        D.translationModulus ⟨f.1 ∘ s, hs⟩ = D.translationModulus f
def ParallelReflect : Prop :=
  ∀ (i : Fin 4) (c c' : ℝ),
    (∀ f : ComplexFun (Fin 4 → ℝ),
      f ∘ hyperplaneReflect i c' =
          Domain.euclidean.translateFn D ((2 * (c' - c)) • basisVec i) (f ∘ hyperplaneReflect i c) ∧
        Domain.euclidean.fnSupport D (f ∘ hyperplaneReflect i c') =
          translationEquiv ((2 * (c' - c)) • basisVec i) ''
            (hyperplaneReflect i c '' Domain.euclidean.fnSupport D f)) ∧
    ∀ f : realC1Compact,
      Domain.euclidean.ennSharpNorm D (f.1 ∘ hyperplaneReflect i c' - f.1 ∘ hyperplaneReflect i c) ≤
        D.translationModulus f (Real.toNNReal (2 * |c' - c|))
def ReflectTranslateCommute (n : Fin 4 → ℝ) (f : ComplexFun (Fin 4 → ℝ))
    (b : Fin 4 → ℝ) (c : ℝ) : Prop :=
  Domain.euclidean.translateFn D b (f ∘ reflectAcross n 0) =
      Domain.euclidean.translateFn D (reflectAcross n 0 b) f ∘ reflectAcross n 0 ∧
    Domain.euclidean.translateFn D (-(c • n)) (f ∘ reflectAcross n c) =
      Domain.euclidean.translateFn D (-(c • n)) f ∘ reflectAcross n 0
def HyperplaneReflectProps : Prop :=
  (∀ n : Fin 4 → ℝ, euclidNorm n = 1 → ∀ (f : ComplexFun (Fin 4 → ℝ))
      (b : Fin 4 → ℝ) (c : ℝ), ReflectTranslateCommute D n f b c) ∧
    (∀ (f : ComplexFun (Fin 4 → ℝ)) (t : ℝ),
      Domain.euclidean.translateFn D (-(t • basisVec 3)) (f ∘ timeReflect) =
        Domain.euclidean.translateFn D (t • basisVec 3) f ∘ timeReflect) ∧
    (∀ (f : ComplexFun (Fin 4 → ℝ)) (b : Fin 4 → ℝ), scalarProd b (basisVec 3) = 0 →
      Domain.euclidean.translateFn D b (f ∘ timeReflect) =
        Domain.euclidean.translateFn D b f ∘ timeReflect) ∧
    ∀ n : Fin 4 → ℝ, euclidNorm n = 1 → IsRootDirection n →
      ∃ w : hyperoctahedral, ⇑w.1 = reflectAcross n 0
def HalfSpaceTimeReflect : Prop :=
  ∀ (i : Fin 4) (c : ℝ),
    halfSpaceNormalize i c ∈ affineHyperoctahedral ∧
      halfSpaceNormalize i c '' {x | c < x i} = {x | 0 < x 3} ∧
      halfSpaceNormalize i c ∘ hyperplaneReflect i c = timeReflect ∘ halfSpaceNormalize i c
def Statement : Prop :=
  ∀ D : TransportData, MotionInvariance D ∧ TranslationModulusProps D ∧ ParallelReflect D ∧
    HyperplaneReflectProps D ∧ HalfSpaceTimeReflect
end MotionFacts
end YangMills.Construction.TorusTransport
end
