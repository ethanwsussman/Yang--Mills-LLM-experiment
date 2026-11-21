import YangMills.Construction.RotationInvariance.EntireFunctionOfTheAngleOnAPencil
import YangMills.Construction.RotationInvariance.GramKernelOnLabelledTubePoints
import Mathlib
set_option autoImplicit false
open Complex (I)
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace RealPlane
variable {k l : ℕ}
def cutLowerPoints (y : Fin (k + l) → RealPlane) : Fin k → RealPlane :=
  fun i => reflectFirst (y (Fin.castAdd l (Fin.rev i)))
def cutUpperPoints (y : Fin (k + l) → RealPlane) : Fin l → RealPlane :=
  fun j => y (Fin.natAdd k j)
def cutLowerLabels {α : Type*} (φ : Fin (k + l) → α) : Fin k → α :=
  fun i => φ (Fin.castAdd l (Fin.rev i))
def cutUpperLabels {α : Type*} (φ : Fin (k + l) → α) : Fin l → α :=
  fun j => φ (Fin.natAdd k j)
def doubledLowerLabels {α : Type*} (φ : Fin (k + l) → α) : Fin (k + k) → α :=
  Fin.append (fun i => φ (Fin.castAdd l i)) (fun i => φ (Fin.castAdd l (Fin.rev i)))
def doubledUpperLabels {α : Type*} (φ : Fin (k + l) → α) : Fin (l + l) → α :=
  Fin.append (fun j => φ (Fin.natAdd k (Fin.rev j))) (fun j => φ (Fin.natAdd k j))
def doubledLabels {n : ℕ} {α : Type*} (φ : Fin n → α) : Fin (n + n) → α :=
  Fin.append (fun i => φ (Fin.rev i)) φ
end RealPlane
namespace ForwardTube
def ofRealPoints {n : ℕ} (a : Fin n → RealPlane) (h : realTuple a ∈ successiveDomain n)
    (φ : Fin n → PointLabel) : LabelledTuple :=
  LabelledTuple.mk ⟨realTuple a, h⟩ φ
end ForwardTube
namespace EuclideanFunctionals
open ForwardTube
namespace MirrorCut
def SectorProperties (φ₀ : openingAngles) : Prop :=
  Convex ℝ (coneSector φ₀) ∧
  coneSector φ₀ ⊆ openRightHalf ∧
  (∀ v ∈ coneSector φ₀, -reflectFirst v ∈ coneSector φ₀) ∧
  (∀ v : RealPlane, (-reflectFirst v) 0 = v 0 ∧ (-reflectFirst v) 1 = -v 1) ∧
  (∀ c : ℝ, 0 < c → ∀ v ∈ coneSector φ₀, c • v ∈ coneSector φ₀) ∧
  ∀ c : ℝ, 0 < c → (!₂[c, 0] : RealPlane) ∈ coneSector φ₀
def CutDisplay {k l : ℕ} (y : Fin (k + 1 + (l + 1)) → RealPlane) : Prop :=
  cutUpperPoints y 0 = (1 / 2 : ℝ) • successiveDifferences y ⟨k, by omega⟩ ∧
  cutLowerPoints y 0 = -reflectFirst ((1 / 2 : ℝ) • successiveDifferences y ⟨k, by omega⟩) ∧
  (∀ (j : ℕ) (hj : j + 1 < l + 1),
    cutUpperPoints y ⟨j + 1, hj⟩ - cutUpperPoints y ⟨j, by omega⟩ =
      successiveDifferences y ⟨k + 1 + j, by omega⟩) ∧
  ∀ (i : ℕ) (hi : i + 1 < k + 1),
    cutLowerPoints y ⟨i + 1, hi⟩ - cutLowerPoints y ⟨i, by omega⟩ =
      -reflectFirst (successiveDifferences y ⟨k - 1 - i, by omega⟩)
def CutVectorsInSector (φ₀ : openingAngles) {k l : ℕ}
    (y : Fin (k + 1 + (l + 1)) → RealPlane) : Prop :=
  cutUpperPoints y 0 ∈ coneSector φ₀ ∧
  cutLowerPoints y 0 ∈ coneSector φ₀ ∧
  (∀ (j : ℕ) (hj : j + 1 < l + 1),
    cutUpperPoints y ⟨j + 1, hj⟩ - cutUpperPoints y ⟨j, by omega⟩ ∈ coneSector φ₀) ∧
  ∀ (i : ℕ) (hi : i + 1 < k + 1),
    cutLowerPoints y ⟨i + 1, hi⟩ - cutLowerPoints y ⟨i, by omega⟩ ∈ coneSector φ₀
def DoubledIsPencil (φ₀ : openingAngles) {p : ℕ} (a : Fin (p + 1) → RealPlane) : Prop :=
  reflectAppend a a ∈ pencilSet φ₀ (p + 1 + (p + 1)) ∧
  (∀ (i : ℕ) (hi : i + 1 < p + 1),
    successiveDifferences (reflectAppend a a) ⟨p + 1 + i, by omega⟩ =
      a ⟨i + 1, hi⟩ - a ⟨i, by omega⟩) ∧
  (∀ (i : ℕ) (hi : i + 1 < p + 1),
    successiveDifferences (reflectAppend a a) ⟨p - 1 - i, by omega⟩ =
      -reflectFirst (a ⟨i + 1, hi⟩ - a ⟨i, by omega⟩)) ∧
  successiveDifferences (reflectAppend a a) ⟨p, by omega⟩ = a 0 - reflectFirst (a 0) ∧
  a 0 - reflectFirst (a 0) = !₂[2 * a 0 0, 0]
def GramKernelThreeValues (S : ConnFamily) (φ₀ : openingAngles) {k l : ℕ}
    (y : Fin (k + 1 + (l + 1)) → RealPlane) (φ : Fin (k + 1 + (l + 1)) → realLabels)
    (hx : realTuple (cutLowerPoints y) ∈ successiveDomain (k + 1))
    (hz : realTuple (cutUpperPoints y) ∈ successiveDomain (l + 1)) : Prop :=
  ∀ s : ℝ,
    gramKernelImag S s
        (ofRealPoints (cutLowerPoints y) hx (cutLowerLabels φ))
        (ofRealPoints (cutUpperPoints y) hz (cutUpperLabels φ)) =
      planeKernel S (q := k + 1 + l) φ
        (complexBoostTuple (I * (s : ℂ)) (planeTupleDiffs (q := k + 1 + l) y)) ∧
    planeKernel S (q := k + 1 + l) φ
        (complexBoostTuple (I * (s : ℂ)) (planeTupleDiffs (q := k + 1 + l) y)) =
      angleFunction S φ₀ (q := k + 1 + l) y φ (I * (s : ℂ)) ∧
    gramKernelImag S s
        (ofRealPoints (cutLowerPoints y) hx (cutLowerLabels φ))
        (ofRealPoints (cutLowerPoints y) hx (cutLowerLabels φ)) =
      angleFunction S φ₀ (q := k + 1 + k)
        (reflectAppend (n := k + 1) (n' := k + 1) (cutLowerPoints y)
          (cutLowerPoints y))
        (doubledLowerLabels φ) (I * (s : ℂ)) ∧
    gramKernelImag S s
        (ofRealPoints (cutUpperPoints y) hz (cutUpperLabels φ))
        (ofRealPoints (cutUpperPoints y) hz (cutUpperLabels φ)) =
      angleFunction S φ₀ (q := l + 1 + l)
        (reflectAppend (n := l + 1) (n' := l + 1) (cutUpperPoints y)
          (cutUpperPoints y))
        (doubledUpperLabels φ) (I * (s : ℂ))
def PencilMirrorCut (S : ConnFamily) (φ₀ : openingAngles) {k l : ℕ}
    (y : Fin (k + 1 + (l + 1)) → RealPlane) (φ : Fin (k + 1 + (l + 1)) → realLabels) : Prop :=
  CutDisplay y ∧
  CutVectorsInSector φ₀ y ∧
  realTuple (cutLowerPoints y) ∈ successiveDomain (k + 1) ∧
  realTuple (cutUpperPoints y) ∈ successiveDomain (l + 1) ∧
  reflectAppend (cutLowerPoints y) (cutUpperPoints y) = y ∧
  gramLabelOrder (cutLowerLabels φ) (cutUpperLabels φ) = φ ∧
  DoubledIsPencil φ₀ (cutLowerPoints y) ∧
  DoubledIsPencil φ₀ (cutUpperPoints y) ∧
  ∀ hx hz, GramKernelThreeValues S φ₀ y φ hx hz
def OneSideEmpty (S : ConnFamily) (φ₀ : openingAngles) {q : ℕ} (y : Fin (q + 1) → RealPlane)
    (φ : Fin (q + 1) → realLabels) : Prop :=
  realTuple y ∈ successiveDomain (q + 1) ∧
  reflectAppend y y ∈ pencilSet φ₀ (q + 1 + (q + 1)) ∧
  ∀ (hz : realTuple y ∈ successiveDomain (q + 1)) (s : ℝ),
    gramKernelImag S s LabelledTuple.nil LabelledTuple.nil = 1 ∧
    gramKernelImag S s LabelledTuple.nil (ofRealPoints y hz φ) =
      angleFunction S φ₀ y φ (I * (s : ℂ)) ∧
    gramKernelImag S s (ofRealPoints y hz φ) (ofRealPoints y hz φ) =
      angleFunction S φ₀ (q := q + 1 + q) (reflectAppend (n := q + 1) (n' := q + 1) y y)
        (doubledLabels φ) (I * (s : ℂ))
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S),
    SectorProperties d.angle ∧
    (∀ (k l : ℕ), ∀ y ∈ pencilSet d.angle (k + 1 + (l + 1)),
      y (Fin.castAdd (l + 1) (Fin.last k)) + y (Fin.natAdd (k + 1) 0) = 0 →
      ∀ φ : Fin (k + 1 + (l + 1)) → realLabels, PencilMirrorCut S d.angle y φ) ∧
    ∀ (q : ℕ), 1 ≤ q → ∀ y ∈ pencilSet d.angle (q + 1), y 0 ∈ coneSector d.angle →
      ∀ φ : Fin (q + 1) → realLabels, OneSideEmpty S d.angle y φ
end MirrorCut
end EuclideanFunctionals
end YangMills.Construction
end
