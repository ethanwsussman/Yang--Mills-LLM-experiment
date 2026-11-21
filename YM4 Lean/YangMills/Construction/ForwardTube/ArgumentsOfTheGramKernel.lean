import YangMills.Construction.ForwardTube.RotatedDirectionsAndSeparatedSets
import YangMills.Construction.ForwardTube.SuccessiveTubeDomainsAndLabelledPoints
import YangMills.Construction.Rotation.LabelledPointConfigurations
import Mathlib
set_option autoImplicit false
open Complex (I)
noncomputable section
namespace YangMills.Construction.ForwardTube
variable {n n' : ℕ}
def realTuple (a : Fin n → RealPlane) : Fin n → ℂ × ℂ := fun i => embedPlane (a i)
def gramKernelArgs (x : Fin n → ℂ × ℂ) (y : Fin n' → ℂ × ℂ) : Fin (n + n' - 1) → ℂ × ℂ :=
  fun k =>
    if hlt : (k : ℕ) + 1 < n then
      tubeStar (x ⟨n - 1 - k, by omega⟩ - x ⟨n - 2 - k, by omega⟩)
    else if heq : (k : ℕ) + 1 = n then
      tubeStar (x ⟨0, by omega⟩) + y ⟨0, by omega⟩
    else
      y ⟨k + 1 - n, by omega⟩ - y ⟨k - n, by omega⟩
def reflectAppend (a : Fin n → RealPlane) (b : Fin n' → RealPlane) :
    Fin (n + n') → RealPlane :=
  Fin.append (fun i => RealPlane.reflectFirst (a (Fin.rev i))) b
def GramKernelArgsFacts : Prop :=
  (∀ (n : ℕ) (hn : 1 ≤ n),
    successiveDomain n ∩ Set.range (realTuple (n := n)) =
        realTuple '' {a : Fin n → RealPlane |
          0 < a ⟨0, hn⟩ 0 ∧ StrictMono fun i => a i 0} ∧
      successiveDomain n ∩ Set.range (realTuple (n := n)) =
        realTuple '' {a : Fin n → RealPlane |
          (∀ i, a i ∈ RealPlane.openRightHalf) ∧ StrictMono fun i => a i 0}) ∧
  (∀ n n' : ℕ, 2 ≤ n + n' →
    ∀ x ∈ successiveDomain n, ∀ y ∈ successiveDomain n', ∀ k,
      gramKernelArgs x y k ∈ forwardTube) ∧
  (∀ n n' : ℕ, 2 ≤ n + n' →
    ∀ (a : Fin n → RealPlane) (b : Fin n' → RealPlane),
      realTuple a ∈ successiveDomain n → realTuple b ∈ successiveDomain n' →
      (∀ k, gramKernelArgs (realTuple a) (realTuple b) k =
        embedPlane (RealPlane.successiveDifferences (reflectAppend a b) k)) ∧
      (∀ i : Fin n, reflectAppend a b (Fin.castAdd n' (Fin.rev i)) 0 = -a i 0) ∧
      (∀ j : Fin n', reflectAppend a b (Fin.natAdd n j) 0 = b j 0) ∧
      (StrictMono fun k => reflectAppend a b k 0) ∧
      (∀ i : Fin n, reflectAppend a b (Fin.castAdd n' i) 0 < 0) ∧
      ∀ j : Fin n', 0 < reflectAppend a b (Fin.natAdd n j) 0) ∧
  ((∀ (s : ℝ) (n : ℕ), 1 ≤ n →
      imagBoostTuple s '' successiveDomain n = successiveDomain n) ∧
    ∀ (s : ℝ) (n n' : ℕ), 2 ≤ n + n' →
      ∀ x ∈ successiveDomain n, ∀ y ∈ successiveDomain n', ∀ k,
        gramKernelArgs (imagBoostTuple s x) (imagBoostTuple s y) k =
          imagBoost s (gramKernelArgs x y k)) ∧
  (∀ (t : ℝ) (v : ℂ × ℂ),
      tubeStar (complexBoost (t : ℂ) v) = complexBoost ((-t : ℝ) : ℂ) (tubeStar v)) ∧
    ∀ t : ℝ, (∀ m : ℤ, t ≠ m * (2 * Real.pi)) → complexBoost (t : ℂ) '' forwardTube ≠ forwardTube
end YangMills.Construction.ForwardTube
end
