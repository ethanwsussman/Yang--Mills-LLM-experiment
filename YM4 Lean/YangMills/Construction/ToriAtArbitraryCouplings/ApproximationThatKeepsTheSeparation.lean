import YangMills.Construction.ToriAtArbitraryCouplings.ChoicesOfCountableDenseSets
import YangMills.Construction.ToriAtArbitraryCouplings.TheCountableFamilyAdaptedToSupports
import YangMills.Construction.ToriAtArbitraryCouplings.TheSeparationAtEveryLength
import YangMills.Construction.ToriAtArbitraryCouplings.TheVectorSpacesOfClassC1AndTheNeighbourhoodsAtASide
import Mathlib
set_option autoImplicit false
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace TorusSide
variable (s : TorusSide)
def approxDefect (m' : ℕ) (E : Ambient) {n : ℕ} (f : Fin n → s.Point E → ℝ) (ε : ℝ) : ℝ :=
  ∑ i, 80 * (cubeEdge s.L m' : ℝ) * ε *
    ∏ l ∈ Finset.univ.erase i, (s.sharpNormAt m' E (f l) + 80 * (cubeEdge s.L m' : ℝ) * ε)
def supportThickening (E : Ambient) {n : ℕ} (f : Fin n → s.Point E → ℝ) (d : ℝ) (i : Fin n) :
    Set (s.Point E) :=
  s.closedThickening E (s.closedSupport E (f i)) (d / 3)
def IsSeparatedApproximation (E : Ambient)
    (D : s.supportFamily E → Set (s.Point E → ℝ)) {n : ℕ} (f : Fin n → s.Point E → ℝ) (d ε : ℝ)
    (φ : Fin n → s.Point E → ℝ) : Prop :=
  List.ofFn φ ∈ s.adaptedTupleSet E D ∧
    ∀ i, s.closedSupport E (φ i) ⊆ s.supportThickening E f d i ∧ s.c1NormOn E (f i - φ i) ≤ ε
def BoundedFormsMoveLittle (m' : ℕ) (E : Ambient) {n : ℕ} (f φ : Fin n → s.Point E → ℝ)
    (d ε : ℝ) : Prop :=
  ∃ (hf : ∀ i, f i ∈ s.c1Submodule E (s.supportThickening E f d i))
    (hφ : ∀ i, φ i ∈ s.c1Submodule E (s.supportThickening E f d i)),
    ∀ c : ℝ, 0 ≤ c →
      ∀ Ψ : MultilinearMap ℝ
          (fun i => s.c1Submodule E (s.supportThickening E f d i)) ℝ,
        (∀ h : (i : Fin n) → s.c1Submodule E (s.supportThickening E f d i),
          |Ψ h| ≤ c * ∏ l, s.sharpNormAt m' E (h l : s.Point E → ℝ)) →
        |Ψ (fun i => ⟨f i, hf i⟩) - Ψ (fun i => ⟨φ i, hφ i⟩)| ≤
          c * s.approxDefect m' E f ε
end TorusSide
namespace SeparatedApproximation
def Statement : Prop :=
  ∀ (s : TorusSide), 8 * 105 ^ 4 ≤ s.L → ∀ (m' : ℕ) (E : Ambient)
    (D : s.supportFamily E → Set (s.Point E → ℝ)), s.IsCountableC1DenseChoice E D →
    ∀ (n : ℕ), 1 ≤ n → ∀ f : Fin n → s.Point E → ℝ, List.ofFn f ∈ s.sepOfLength E n →
    ∀ d : ℝ, 0 < d → ENNReal.ofReal d ≤ s.gapAllLengths E (List.ofFn f) →
    ∀ ε : ℝ, 0 < ε →
      (∀ i, s.IsCompactWrt E (s.supportThickening E f d i)) ∧
      (∀ i k, i ≠ k → ENNReal.ofReal (d / 3) ≤
        s.setDist E (s.supportThickening E f d i) (s.supportThickening E f d k)) ∧
      (∃ φ : Fin n → s.Point E → ℝ, s.IsSeparatedApproximation E D f d ε φ ∧
        s.BoundedFormsMoveLittle m' E f φ d ε) ∧
      Filter.Tendsto (s.approxDefect m' E f) (𝓝[>] 0) (𝓝 0)
end SeparatedApproximation
end YangMills.Construction.ToriAtArbitraryCouplings
end
