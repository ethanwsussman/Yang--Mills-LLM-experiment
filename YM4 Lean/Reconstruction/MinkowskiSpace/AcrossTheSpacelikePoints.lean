import Reconstruction.MinkowskiSpace.WightmanTheoriesOfOneHermitianScalarField
import Reconstruction.MinkowskiSpace.EuclideanFieldFormsAndWhatAFormRepresents
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.FieldForms
open MinkowskiSpace OneLoopNotation ProjectionMeasures WightmanTheory
def spacelikeSlab {b : ℕ} (j : Fin b) : Set (Fin b → ComplexVec4) :=
  {ζ | ζ j ∈ MinkowskiSpace.toComplex '' spacelikeSet ∧ ∀ k, k ≠ j → ζ k ∈ futureTube}
def maxBoostAngle {b : ℕ} (j : Fin b) (ζ : Fin b → ComplexVec4) : ℝ :=
  if h : (Finset.univ.erase j).Nonempty then
    min 1 ((Finset.univ.erase j).inf' h fun k => tubeGap (ζ k) / (2 * l1Norm (ζ k)))
  else 1
theorem rePart_mem_spacelikeSet_of_mem_spacelikeSlab {b : ℕ} {j : Fin b}
    {ζ : Fin b → ComplexVec4} (hζ : ζ ∈ spacelikeSlab j) :
    MinkowskiSpace.rePart (ζ j) ∈ spacelikeSet := by
  obtain ⟨⟨y, hy, hye⟩, _⟩ := hζ
  have hre : MinkowskiSpace.rePart (ζ j) = y := by
    rw [← hye]
    funext μ
    simp [MinkowskiSpace.rePart, MinkowskiSpace.toComplex]
  rwa [hre]
theorem spaceNorm_normalized_spacePart {y : RealVec4} (hy : y ∈ spacelikeSet) :
    spaceNorm (fun i => spacePart y i / spaceNorm (spacePart y)) = 1 := by
  have hpos : 0 < spaceNorm (spacePart y) :=
    lt_of_le_of_lt (abs_nonneg _) ((isSpacelikeVec_iff y).1 hy)
  have hsq : ∑ i, spacePart y i ^ 2 = spaceNorm (spacePart y) ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)).symm
  have hone : ∑ i, (spacePart y i / spaceNorm (spacePart y)) ^ 2 = 1 := by
    simp only [div_pow]
    rw [← Finset.sum_div, hsq]
    exact div_self (pow_ne_zero 2 hpos.ne')
  change Real.sqrt (∑ i, (spacePart y i / spaceNorm (spacePart y)) ^ 2) = 1
  rw [hone, Real.sqrt_one]
def spacelikeUnitDir {b : ℕ} (j : Fin b) (ζ : Fin b → ComplexVec4)
    (hζ : ζ ∈ spacelikeSlab j) : unitSphere3 :=
  ⟨fun i => spacePart (MinkowskiSpace.rePart (ζ j)) i /
      spaceNorm (spacePart (MinkowskiSpace.rePart (ζ j))),
    spaceNorm_normalized_spacePart (rePart_mem_spacelikeSet_of_mem_spacelikeSlab hζ)⟩
def imagBoostTuple {b : ℕ} (v : unitSphere3) (a : ℝ) (ζ : Fin b → ComplexVec4) :
    Fin b → ComplexVec4 :=
  mulVecTuple (boostMatrix v (Complex.I * (a : ℂ))) ζ
def spacelikeContinuation {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K)
    {b : ℕ} (j : Fin b) (ζ : Fin b → ComplexVec4) : ℂ :=
  open Classical in
  if hζ : ζ ∈ spacelikeSlab j then
    vacuumExpectation E Ω A (b + 1)
      (imagBoostTuple (spacelikeUnitDir j ζ hζ) (maxBoostAngle j ζ) ζ)
  else 0
def tupleBall {b : ℕ} (ζ₀ : Fin b → ComplexVec4) (r : ℝ) : Set (Fin b → ComplexVec4) :=
  {ζ | ∑ k, ∑ μ, ‖ζ k μ - ζ₀ k μ‖ ^ 2 < r ^ 2}
def timeLiftedTuple {b : ℕ} (j : Fin b) (ε : ℝ) (ζ : Fin b → ComplexVec4) :
    Fin b → ComplexVec4 :=
  Function.update ζ j (ζ j + imagTimeShift ε)
def adjacentSwapMap {b : ℕ} (j : Fin b) :
    (Fin b → ComplexVec4) →ₗ[ℂ] (Fin b → ComplexVec4) where
  toFun ζ k :=
    if k = j then -ζ j
    else if (k : ℕ) + 1 = j ∨ (j : ℕ) + 1 = k then ζ k + ζ j
    else ζ k
  map_add' ζ ξ := by
    funext k
    simp only [Pi.add_apply]
    split_ifs <;> abel
  map_smul' t ζ := by
    funext k
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [smul_add]
def ImagBoostMapsIntoTube {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K)
    {b : ℕ} (j : Fin b) : Prop :=
  ∀ (ζ : Fin b → ComplexVec4) (hζ : ζ ∈ spacelikeSlab j) (a : ℝ), 0 < a → a ≤ maxBoostAngle j ζ →
    imagBoostTuple (spacelikeUnitDir j ζ hζ) a ζ ∈ tubeTuples b ∧
      vacuumExpectation E Ω A (b + 1) (imagBoostTuple (spacelikeUnitDir j ζ hζ) a ζ) =
        spacelikeContinuation E Ω A j ζ
def SpacelikeContinuationLocallyHolomorphic {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (E : FourBorelSet → BddOp K) (Ω : K)
    (A : ℝ → BddOp K) {b : ℕ} (j : Fin b) : Prop :=
  ∀ (ζ₀ : Fin b → ComplexVec4) (hζ₀ : ζ₀ ∈ spacelikeSlab j), ∃ r : ℝ, 0 < r ∧
    (∀ ζ ∈ tupleBall ζ₀ r,
      imagBoostTuple (spacelikeUnitDir j ζ₀ hζ₀) (maxBoostAngle j ζ₀ / 2) ζ ∈ tubeTuples b) ∧
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) (coordsToTuple ⁻¹' tupleBall ζ₀ r)
      (fun z _ => vacuumExpectation E Ω A (b + 1)
        (imagBoostTuple (spacelikeUnitDir j ζ₀ hζ₀) (maxBoostAngle j ζ₀ / 2)
          (coordsToTuple z))) ∧
    ∀ ζ ∈ tupleBall ζ₀ r ∩ spacelikeSlab j,
      vacuumExpectation E Ω A (b + 1)
          (imagBoostTuple (spacelikeUnitDir j ζ₀ hζ₀) (maxBoostAngle j ζ₀ / 2) ζ) =
        spacelikeContinuation E Ω A j ζ
def SpacelikeContinuationBoundaryValue {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (E : FourBorelSet → BddOp K) (Ω : K)
    (A : ℝ → BddOp K) (p C : ℝ) {b : ℕ} (j : Fin b) : Prop :=
  ∀ ζ ∈ spacelikeSlab j,
    (∀ ε : ℝ, 0 < ε → timeLiftedTuple j ε ζ ∈ tubeTuples b) ∧
    Tendsto (fun ε : ℝ => vacuumExpectation E Ω A (b + 1) (timeLiftedTuple j ε ζ)) (𝓝[>] 0)
      (𝓝 (spacelikeContinuation E Ω A j ζ)) ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖vacuumExpectation E Ω A (b + 1) (timeLiftedTuple j ε ζ)‖ ≤
        ((2 : ℝ) ^ p * C) ^ (b + 1) *
          min 1 (Real.sin (maxBoostAngle j ζ) *
            (spaceNorm (spacePart (MinkowskiSpace.rePart (ζ j))) -
              |MinkowskiSpace.rePart (ζ j) 0|)) ^ (-ceilExponent p (b + 1)) *
          ∏ k ∈ Finset.univ.erase j,
            min 1 (tubeGap (ζ k) / 2) ^ (-ceilExponent p (b + 1))
def SpacelikeContinuationSwapInvariant {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (E : FourBorelSet → BddOp K) (Ω : K)
    (A : ℝ → BddOp K) {b : ℕ} (j : Fin b) : Prop :=
  adjacentSwapMap j '' spacelikeSlab j = spacelikeSlab j ∧
    ∀ ζ ∈ spacelikeSlab j,
      spacelikeContinuation E Ω A j (adjacentSwapMap j ζ) =
        spacelikeContinuation E Ω A j ζ
namespace SpacelikeExtension
def Statement : Prop :=
  ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) (p C : ℝ),
    IsBoundedFieldForm E Ω A p C → IsEuclidean E Ω A →
    ∀ (b : ℕ) (j : Fin b),
      Function.Bijective (adjacentSwapMap j) ∧
      (∀ z : Fin (b + 1) → ComplexVec4,
        adjacentSwapMap j (successiveDiffs z) =
          successiveDiffs (z ∘ Equiv.swap j.castSucc j.succ)) ∧
      ImagBoostMapsIntoTube E Ω A j ∧
      SpacelikeContinuationLocallyHolomorphic E Ω A j ∧
      SpacelikeContinuationBoundaryValue E Ω A p C j ∧
      SpacelikeContinuationSwapInvariant E Ω A j
end SpacelikeExtension
end YangMills.Construction.FieldForms
