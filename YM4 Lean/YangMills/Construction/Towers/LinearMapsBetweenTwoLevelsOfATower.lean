import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.LinearMapsAtTheTrivialConfiguration
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace Tower
def levelwiseComposition {F : ℕ → Type*} (step : ∀ j, F j → F (j + 1)) {i l : ℕ} (h : i ≤ l) :
    F i → F l :=
  Nat.leRec (motive := fun m _ => F i → F m) id (fun m _ g => step m ∘ g) h
theorem levelwiseComposition_self {F : ℕ → Type*} (step : ∀ j, F j → F (j + 1)) (i : ℕ) :
    levelwiseComposition step (le_refl i) = id := by
  simp [levelwiseComposition]
theorem levelwiseComposition_succ {F : ℕ → Type*} (step : ∀ j, F j → F (j + 1)) {i l : ℕ}
    (hil : i ≤ l) (hil' : i ≤ l + 1) :
    levelwiseComposition step hil' = step l ∘ levelwiseComposition step hil := by
  simp [levelwiseComposition, Nat.leRec_succ, hil]
namespace TwoLevelMaps
section FiniteSide
open PeriodicLattice (FourTorus refinedBlock crossingPath sitesIn)
def linearSmoothingBetween (L m k : ℕ) {i l : ℕ} (h : i ≤ l) :
    (Edge L m k i → Matrices.ComplexMatrix2) → Edge L m k l → Matrices.ComplexMatrix2 :=
  levelwiseComposition (F := fun j => Edge L m k j → Matrices.ComplexMatrix2)
    (linearSmoothing L m k) h
def crossingSmoothingBetween (L m k : ℕ) {i l : ℕ} (h : i ≤ l) :
    (Edge L m k i → Matrices.ComplexMatrix2) → Edge L m k l → Matrices.ComplexMatrix2 :=
  levelwiseComposition (F := fun j => Edge L m k j → Matrices.ComplexMatrix2)
    (crossingSmoothing L m k) h
def vertexSmoothingBetween (L m k : ℕ) {i l : ℕ} (h : i ≤ l) :
    (Vertex L m k i → Matrices.ComplexMatrix2) → Vertex L m k l → Matrices.ComplexMatrix2 :=
  levelwiseComposition (F := fun j => Vertex L m k j → Matrices.ComplexMatrix2)
    (vertexSmoothing L m k) h
def cubeContourAverageBetween (L m k : ℕ) {i l : ℕ} (_h : i ≤ l)
    (A : Edge L m k i → Matrices.ComplexMatrix2) : Vertex L m k l → Matrices.ComplexMatrix2 :=
  ∑ t ∈ Finset.range (l - i), restrictVertexFunction l
    (cubeContourAverage L m k (i + t) (crossingSmoothingBetween L m k (Nat.le_add_right i t) A))
def complexRestriction (L m k i l : ℕ) :
    (pairedFunctions (Vertex L m k i)).complexSubmodule →ₗ[ℂ]
      (pairedFunctions (Vertex L m k l)).complexSubmodule where
  toFun f := ⟨restrictVertexFunction l f.1, fun _ _ => f.2 _ (mem_univ _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def extendByZero {L m k i l : ℕ} (g : Vertex L m k l → Matrices.ComplexMatrix2) :
    Vertex L m k i → Matrices.ComplexMatrix2 :=
  open Classical in
  fun x => if hx : ∃ y : Vertex L m k l, (y : FourTorus L m) = x then g hx.choose else 0
structure OneStepRelations (L m k i : ℕ) : Prop where
  linearSmoothing_eq : ∀ A ∈ complexEdgeForms L m k i,
    linearSmoothing L m k i A =
      crossingSmoothing L m k i A - vertexCoboundary (cubeContourAverage L m k i A)
  linearSmoothing_coboundary : ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k i),
    linearSmoothing L m k i (vertexCoboundary f) =
      vertexCoboundary (restrictVertexFunction (i + 1) f)
  crossingSmoothing_coboundary :
    ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k i),
      crossingSmoothing L m k i (vertexCoboundary f) =
        vertexCoboundary (vertexSmoothing L m k i f)
  cubeContourAverage_coboundary :
    ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k i),
      cubeContourAverage L m k i (vertexCoboundary f) =
        vertexSmoothing L m k i f - restrictVertexFunction (i + 1) f
  cubeContourAverage_of_constant : ∀ A ∈ complexEdgeForms L m k i,
    ∀ a : Fin 4 → Matrices.ComplexMatrix2,
    (∀ (x : Vertex L m k i) (μ : Fin 4), A (PeriodicLattice.Bond.forwardFrom x μ) = a μ) →
      cubeContourAverage L m k i A = 0
structure CompositeRelations (L m k n j : ℕ) : Prop where
  linearSmoothing_eq : ∀ A ∈ complexEdgeForms L m k (j - n),
    linearSmoothingBetween L m k (Nat.sub_le j n) A =
      crossingSmoothingBetween L m k (Nat.sub_le j n) A - vertexCoboundary
        (cubeContourAverageBetween L m k (Nat.sub_le j n) A)
  linearSmoothing_coboundary :
    ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k (j - n)),
      linearSmoothingBetween L m k (Nat.sub_le j n) (vertexCoboundary f) = vertexCoboundary
        (restrictVertexFunction j f)
  crossingSmoothing_coboundary :
    ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k (j - n)),
      crossingSmoothingBetween L m k (Nat.sub_le j n) (vertexCoboundary f) =
        vertexCoboundary (vertexSmoothingBetween L m k (Nat.sub_le j n) f)
  vertexSmoothing_eq :
    ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k (j - n)),
      ∀ y : Vertex L m k j, vertexSmoothingBetween L m k (Nat.sub_le j n) f y =
        ((L : ℂ) ^ (4 * n))⁻¹ •
          ∑ᶠ x ∈ (sitesIn (refinedBlock n y) : Set (Vertex L m k (j - n))), f x
  crossingSmoothing_eq : ∀ A ∈ complexEdgeForms L m k (j - n), ∀ c : Edge L m k j,
    crossingSmoothingBetween L m k (Nat.sub_le j n) A c =
      ((L : ℂ) ^ (4 * n))⁻¹ •
        ∑ᶠ x ∈ (sitesIn (refinedBlock n c.source) : Set (Vertex L m k (j - n))),
          edgeFormPathSum A (crossingPath c x)
  crossingPath_length : ∀ (c : Edge L m k j) (x : Vertex L m k (j - n)),
    (x : FourTorus L m) ∈ refinedBlock n c.source → (crossingPath c x).length = L ^ n
  crossingSmoothing_norm_le : ∀ A ∈ complexEdgeForms L m k (j - n),
    maxOperatorNorm (crossingSmoothingBetween L m k (Nat.sub_le j n) A) ≤
      (L : ℝ≥0∞) ^ n * maxOperatorNorm A
  cubeContourAverage_norm_le : ∀ A ∈ complexEdgeForms L m k (j - n),
    maxOperatorNorm (cubeContourAverageBetween L m k (Nat.sub_le j n) A) ≤
      2 * (L : ℝ≥0∞) ^ n * maxOperatorNorm A
  linearSmoothing_norm_le : ∀ A ∈ complexEdgeForms L m k (j - n),
    maxOperatorNorm (linearSmoothingBetween L m k (Nat.sub_le j n) A) ≤
      5 * (L : ℝ≥0∞) ^ n * maxOperatorNorm A
  of_constant : ∀ A ∈ complexEdgeForms L m k (j - n), ∀ a : Fin 4 → Matrices.ComplexMatrix2,
    (∀ (x : Vertex L m k (j - n)) (μ : Fin 4), A (PeriodicLattice.Bond.forwardFrom x μ) = a μ) →
      linearSmoothingBetween L m k (Nat.sub_le j n) A =
        crossingSmoothingBetween L m k (Nat.sub_le j n) A ∧
      crossingSmoothingBetween L m k (Nat.sub_le j n) A ∈ complexEdgeForms L m k j ∧
      ∀ (x : Vertex L m k j) (μ : Fin 4),
        crossingSmoothingBetween L m k (Nat.sub_le j n) A (PeriodicLattice.Bond.forwardFrom x μ) =
          (L : ℂ) ^ n • a μ
  linearSmoothing_mapsTo_surjOn : MapsTo (linearSmoothingBetween L m k (Nat.sub_le j n))
      (complexEdgeForms L m k (j - n)) (complexEdgeForms L m k j) ∧
    SurjOn (linearSmoothingBetween L m k (Nat.sub_le j n))
      (complexEdgeForms L m k (j - n)) (complexEdgeForms L m k j)
  crossingSmoothing_mapsTo_surjOn : MapsTo (crossingSmoothingBetween L m k (Nat.sub_le j n))
      (complexEdgeForms L m k (j - n)) (complexEdgeForms L m k j) ∧
    SurjOn (crossingSmoothingBetween L m k (Nat.sub_le j n))
      (complexEdgeForms L m k (j - n)) (complexEdgeForms L m k j)
  linearSmoothing_mapsTo_surjOn_real : MapsTo (linearSmoothingBetween L m k (Nat.sub_le j n))
      (edgeFormSpace L m k (j - n)) (edgeFormSpace L m k j) ∧
    SurjOn (linearSmoothingBetween L m k (Nat.sub_le j n))
      (edgeFormSpace L m k (j - n)) (edgeFormSpace L m k j)
  crossingSmoothing_mapsTo_surjOn_real : MapsTo (crossingSmoothingBetween L m k (Nat.sub_le j n))
      (edgeFormSpace L m k (j - n)) (edgeFormSpace L m k j) ∧
    SurjOn (crossingSmoothingBetween L m k (Nat.sub_le j n))
      (edgeFormSpace L m k (j - n)) (edgeFormSpace L m k j)
  restriction_preservesFiniteSupport : PairedFunctionSpace.PreservesFiniteSupport
    (complexRestriction L m k (j - n) j)
  restriction_isTransposeMap : PairedFunctionSpace.IsTransposeMap
    (complexRestriction L m k (j - n) j)
    (PairedFunctionSpace.transposeMap (complexRestriction L m k (j - n) j))
  transposeMap_eq : ∀ g : (pairedFunctions (Vertex L m k j)).complexSubmodule,
    (PairedFunctionSpace.transposeMap (complexRestriction L m k (j - n) j) g).1 =
      extendByZero g.1
  restrict_transposeMap : ∀ g : (pairedFunctions (Vertex L m k j)).complexSubmodule,
    restrictVertexFunction j
      (PairedFunctionSpace.transposeMap (complexRestriction L m k (j - n) j) g).1 = g.1
structure CompositesFromBase (L m k n : ℕ) : Prop where
  linearSmoothing_eq : ∀ A ∈ edgeFormSpace L m k 0,
    linearSmoothingBetween L m k (Nat.zero_le n) A = linearSmoothingIter L m k n A
  crossingSmoothing_eq : ∀ A ∈ edgeFormSpace L m k 0,
    crossingSmoothingBetween L m k (Nat.zero_le n) A = crossingSmoothingIter L m k n A
  vertexSmoothing_eq : ∀ f ∈ vertexFunctionSpace L m k 0,
    vertexSmoothingBetween L m k (Nat.zero_le n) f = vertexSmoothingIter L m k n f
  cubeContourAverage_eq : ∀ A ∈ edgeFormSpace L m k 0,
    cubeContourAverageBetween L m k (Nat.zero_le n) A = cubeContourAverageIter L m k n A
end FiniteSide
end TwoLevelMaps
namespace FullSpace
namespace TwoLevelMaps
def linearSmoothingBetween (L k : ℕ) {i l : ℕ} (h : i ≤ l) :
    (Edge L k i → Matrices.ComplexMatrix2) → Edge L k l → Matrices.ComplexMatrix2 :=
  levelwiseComposition (F := fun j => Edge L k j → Matrices.ComplexMatrix2)
    (fun _ => linearSmoothing L) h
def crossingSmoothingBetween (L k : ℕ) {i l : ℕ} (h : i ≤ l) :
    (Edge L k i → Matrices.ComplexMatrix2) → Edge L k l → Matrices.ComplexMatrix2 :=
  levelwiseComposition (F := fun j => Edge L k j → Matrices.ComplexMatrix2)
    (fun _ => crossingSmoothing L) h
def vertexSmoothingBetween (L k : ℕ) {i l : ℕ} (h : i ≤ l) :
    (Vertex L k i → Matrices.ComplexMatrix2) → Vertex L k l → Matrices.ComplexMatrix2 :=
  levelwiseComposition (F := fun j => Vertex L k j → Matrices.ComplexMatrix2)
    (fun _ => vertexSmoothing L) h
def cubeContourAverageBetween (L k : ℕ) {i l : ℕ} (_h : i ≤ l)
    (A : Edge L k i → Matrices.ComplexMatrix2) : Vertex L k l → Matrices.ComplexMatrix2 :=
  ∑ t ∈ Finset.range (l - i), restrictVertexFunction (meshAt L k l)
    (cubeContourAverage (a := meshAt L k (i + t + 1)) L
      (crossingSmoothingBetween L k (Nat.le_add_right i t) A))
def complexRestriction (L k i l : ℕ) :
    (pairedFunctions (Vertex L k i)).complexSubmodule →ₗ[ℂ]
      (pairedFunctions (Vertex L k l)).complexSubmodule where
  toFun f := ⟨restrictVertexFunction (meshAt L k l) f.1, fun _ _ => f.2 _ (mem_univ _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def extendByZero {L k i l : ℕ} (g : Vertex L k l → Matrices.ComplexMatrix2) :
    Vertex L k i → Matrices.ComplexMatrix2 :=
  open Classical in
  fun x => if hx : ∃ y : Vertex L k l, (y : AmbientSpace) = x then g hx.choose else 0
def verticesOfCubeOfOrder (L k n j : ℕ) (y : Vertex L k j) : Set (Vertex L k (j - n)) :=
  {x | (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n y}
structure OneStepRelations (L k i : ℕ) : Prop where
  linearSmoothing_eq : ∀ A ∈ complexEdgeForms (meshAt L k i),
    linearSmoothing (a := meshAt L k (i + 1)) L A =
      crossingSmoothing (a := meshAt L k (i + 1)) L A - vertexCoboundary
        (cubeContourAverage (a := meshAt L k (i + 1)) L A)
  linearSmoothing_coboundary :
    ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L k i),
      linearSmoothing (a := meshAt L k (i + 1)) L (vertexCoboundary f) =
        vertexCoboundary (restrictVertexFunction (meshAt L k (i + 1)) f)
  crossingSmoothing_coboundary :
    ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L k i),
      crossingSmoothing (a := meshAt L k (i + 1)) L (vertexCoboundary f) =
        vertexCoboundary (vertexSmoothing (a := meshAt L k (i + 1)) L f)
  cubeContourAverage_coboundary :
    ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L k i),
      cubeContourAverage (a := meshAt L k (i + 1)) L (vertexCoboundary f) =
        vertexSmoothing (a := meshAt L k (i + 1)) L f -
          restrictVertexFunction (meshAt L k (i + 1)) f
  cubeContourAverage_of_constant : ∀ A ∈ complexEdgeForms (meshAt L k i),
    ∀ a : Fin 4 → Matrices.ComplexMatrix2,
    (∀ (x : Vertex L k i) (μ : Fin 4), A (InfiniteLattice.Link.forwardFrom x μ) = a μ) →
      cubeContourAverage (a := meshAt L k (i + 1)) L A = 0
structure CompositeRelations (L k n j : ℕ) : Prop where
  linearSmoothing_eq : ∀ A ∈ complexEdgeForms (meshAt L k (j - n)),
    linearSmoothingBetween L k (Nat.sub_le j n) A =
      crossingSmoothingBetween L k (Nat.sub_le j n) A - vertexCoboundary
        (cubeContourAverageBetween L k (Nat.sub_le j n) A)
  linearSmoothing_coboundary :
    ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L k (j - n)),
      linearSmoothingBetween L k (Nat.sub_le j n) (vertexCoboundary f) = vertexCoboundary
        (restrictVertexFunction (meshAt L k j) f)
  crossingSmoothing_coboundary :
    ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L k (j - n)),
      crossingSmoothingBetween L k (Nat.sub_le j n) (vertexCoboundary f) =
        vertexCoboundary (vertexSmoothingBetween L k (Nat.sub_le j n) f)
  vertexSmoothing_eq :
    ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L k (j - n)),
      ∀ y : Vertex L k j, vertexSmoothingBetween L k (Nat.sub_le j n) f y =
        ((L : ℂ) ^ (4 * n))⁻¹ • ∑ᶠ x ∈ verticesOfCubeOfOrder L k n j y, f x
  crossingSmoothing_eq : ∀ A ∈ complexEdgeForms (meshAt L k (j - n)), ∀ c : Edge L k j,
    crossingSmoothingBetween L k (Nat.sub_le j n) A c =
      ((L : ℂ) ^ (4 * n))⁻¹ • ∑ᶠ x ∈ verticesOfCubeOfOrder L k n j c.initial,
        edgeFormPathSum A (crossingPath c x)
  crossingPath_length : ∀ (c : Edge L k j) (x : Vertex L k (j - n)),
    (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial →
      (crossingPath c x).length = L ^ n
  crossingSmoothing_norm_le : ∀ A ∈ complexEdgeForms (meshAt L k (j - n)),
    maxOperatorNorm (crossingSmoothingBetween L k (Nat.sub_le j n) A) ≤
      (L : ℝ≥0∞) ^ n * maxOperatorNorm A
  cubeContourAverage_norm_le : ∀ A ∈ complexEdgeForms (meshAt L k (j - n)),
    maxOperatorNorm (cubeContourAverageBetween L k (Nat.sub_le j n) A) ≤
      2 * (L : ℝ≥0∞) ^ n * maxOperatorNorm A
  linearSmoothing_norm_le : ∀ A ∈ complexEdgeForms (meshAt L k (j - n)),
    maxOperatorNorm (linearSmoothingBetween L k (Nat.sub_le j n) A) ≤
      5 * (L : ℝ≥0∞) ^ n * maxOperatorNorm A
  of_constant : ∀ A ∈ complexEdgeForms (meshAt L k (j - n)),
    ∀ a : Fin 4 → Matrices.ComplexMatrix2,
    (∀ (x : Vertex L k (j - n)) (μ : Fin 4), A (InfiniteLattice.Link.forwardFrom x μ) = a μ) →
      linearSmoothingBetween L k (Nat.sub_le j n) A =
        crossingSmoothingBetween L k (Nat.sub_le j n) A ∧
      crossingSmoothingBetween L k (Nat.sub_le j n) A ∈ complexEdgeForms (meshAt L k j) ∧
      ∀ (x : Vertex L k j) (μ : Fin 4),
        crossingSmoothingBetween L k (Nat.sub_le j n) A (InfiniteLattice.Link.forwardFrom x μ) =
          (L : ℂ) ^ n • a μ
  linearSmoothing_mapsTo_surjOn : MapsTo (linearSmoothingBetween L k (Nat.sub_le j n))
      (complexEdgeForms (meshAt L k (j - n))) (complexEdgeForms (meshAt L k j)) ∧
    SurjOn (linearSmoothingBetween L k (Nat.sub_le j n))
      (complexEdgeForms (meshAt L k (j - n))) (complexEdgeForms (meshAt L k j))
  crossingSmoothing_mapsTo_surjOn : MapsTo (crossingSmoothingBetween L k (Nat.sub_le j n))
      (complexEdgeForms (meshAt L k (j - n))) (complexEdgeForms (meshAt L k j)) ∧
    SurjOn (crossingSmoothingBetween L k (Nat.sub_le j n))
      (complexEdgeForms (meshAt L k (j - n))) (complexEdgeForms (meshAt L k j))
  linearSmoothing_mapsTo_surjOn_real : MapsTo (linearSmoothingBetween L k (Nat.sub_le j n))
      (edgeFormSpace (meshAt L k (j - n))) (edgeFormSpace (meshAt L k j)) ∧
    SurjOn (linearSmoothingBetween L k (Nat.sub_le j n))
      (edgeFormSpace (meshAt L k (j - n))) (edgeFormSpace (meshAt L k j))
  crossingSmoothing_mapsTo_surjOn_real : MapsTo (crossingSmoothingBetween L k (Nat.sub_le j n))
      (edgeFormSpace (meshAt L k (j - n))) (edgeFormSpace (meshAt L k j)) ∧
    SurjOn (crossingSmoothingBetween L k (Nat.sub_le j n))
      (edgeFormSpace (meshAt L k (j - n))) (edgeFormSpace (meshAt L k j))
  restriction_preservesFiniteSupport : PairedFunctionSpace.PreservesFiniteSupport
    (complexRestriction L k (j - n) j)
  restriction_isTransposeMap : PairedFunctionSpace.IsTransposeMap
    (complexRestriction L k (j - n) j)
    (PairedFunctionSpace.transposeMap (complexRestriction L k (j - n) j))
  transposeMap_eq : ∀ g : (pairedFunctions (Vertex L k j)).complexSubmodule,
    (PairedFunctionSpace.transposeMap (complexRestriction L k (j - n) j) g).1 =
      extendByZero g.1
  restrict_transposeMap : ∀ g : (pairedFunctions (Vertex L k j)).complexSubmodule,
    restrictVertexFunction (meshAt L k j)
      (PairedFunctionSpace.transposeMap (complexRestriction L k (j - n) j) g).1 = g.1
structure CompositesFromBase (L k n : ℕ) : Prop where
  linearSmoothing_eq : ∀ A ∈ edgeFormSpace (meshAt L k 0),
    linearSmoothingBetween L k (Nat.zero_le n) A = linearSmoothingIter L k n A
  crossingSmoothing_eq : ∀ A ∈ edgeFormSpace (meshAt L k 0),
    crossingSmoothingBetween L k (Nat.zero_le n) A = crossingSmoothingIter L k n A
  vertexSmoothing_eq : ∀ f ∈ vertexFunctionSpace (meshAt L k 0),
    vertexSmoothingBetween L k (Nat.zero_le n) f = vertexSmoothingIter L k n f
  cubeContourAverage_eq : ∀ A ∈ edgeFormSpace (meshAt L k 0),
    cubeContourAverageBetween L k (Nat.zero_le n) A = cubeContourAverageIter L k n A
end TwoLevelMaps
end FullSpace
def TwoLevelMaps.Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ m : ℕ, 0 < m →
      (∀ i : ℕ, i + 1 ≤ k → TwoLevelMaps.OneStepRelations L m k i) ∧
      (∀ n j : ℕ, 1 ≤ j → n ≤ j → j ≤ k → TwoLevelMaps.CompositeRelations L m k n j) ∧
      ∀ n : ℕ, n ≤ k → TwoLevelMaps.CompositesFromBase L m k n) ∧
    (∀ i : ℕ, i + 1 ≤ k → FullSpace.TwoLevelMaps.OneStepRelations L k i) ∧
    (∀ n j : ℕ, 1 ≤ j → n ≤ j → j ≤ k → FullSpace.TwoLevelMaps.CompositeRelations L k n j) ∧
    ∀ n : ℕ, n ≤ k → FullSpace.TwoLevelMaps.CompositesFromBase L k n
end Tower
end YangMills.Construction
end
