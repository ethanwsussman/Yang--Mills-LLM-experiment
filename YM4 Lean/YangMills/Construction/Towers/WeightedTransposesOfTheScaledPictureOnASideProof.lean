import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.NormOfTheColourCoefficients
import YangMills.Construction.Towers.WeightedTransposeOnFaithfulEvaluations
import YangMills.Construction.Towers.WeightedTransposesOfTheScaledPictureOnASide
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices
namespace WeightedTransposesOnTorus
theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_smul_add (a : Fin 3) (z : ℂ) {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (z • X + Y) = z * pauliCoeff a X + pauliCoeff a Y := by
  have e : z • X + Y =
      ∑ b, (z * pauliCoeff b X + pauliCoeff b Y) • ComplexMatrix2.pauliFamily b := by
    simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum,
      sum_pauliCoeff_smul hX, sum_pauliCoeff_smul hY]
  rw [e]
  exact pauliCoeff_sum_smul _ a
section Functions
variable {σ : Type}
theorem ofPauliCoeffs_mem_traceless (c : Fin 3 × σ → ℂ) (i : σ) :
    ofPauliCoeffs c i ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem toPauliCoeffs_ofPauliCoeffs (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
theorem ofPauliCoeffs_toPauliCoeffs {f : σ → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.traceless) : ofPauliCoeffs (toPauliCoeffs f) = f := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofPauliCoeffs_toPauliCoeffs <;> assumption
theorem toPauliCoeffs_smul_add (z : ℂ) {f g : σ → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.traceless) (hg : ∀ i, g i ∈ ComplexMatrix2.traceless) :
    toPauliCoeffs (z • f + g) = z • toPauliCoeffs f + toPauliCoeffs g :=
  funext fun ι => pauliCoeff_smul_add ι.1 z (hf ι.2) (hg ι.2)
theorem hasFiniteSupp_ofPauliCoeffs_iff (c : Fin 3 × σ → ℂ) :
    HasFiniteSupp (ofPauliCoeffs c) ↔ (Function.support c).Finite := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.hasFiniteSupp_ofPauliCoeffs_iff <;> assumption
theorem hasFiniteSupp_iff {f : σ → ComplexMatrix2} (hf : ∀ i, f i ∈ ComplexMatrix2.traceless) :
    HasFiniteSupp f ↔ PeriodicOperators.HasFiniteSupport (toPauliCoeffs f) := by
  have e := hasFiniteSupp_ofPauliCoeffs_iff (toPauliCoeffs f)
  rwa [ofPauliCoeffs_toPauliCoeffs hf] at e
theorem traceFinsumPairing_ofPauliCoeffs (hP : OneLoop.PauliMatrixRelations)
    (a b : Fin 3 × σ → ℂ) (hb : (Function.support b).Finite) :
    traceFinsumPairing (ofPauliCoeffs a) (ofPauliCoeffs b) = ∑ᶠ ι, a ι * b ι := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.traceFinsumPairing_ofPauliCoeffs <;> assumption
theorem traceFinsumPairing_eq_finsum (hP : OneLoop.PauliMatrixRelations)
    {g f : σ → ComplexMatrix2} (hg : ∀ i, g i ∈ ComplexMatrix2.traceless)
    (hf : ∀ i, f i ∈ ComplexMatrix2.traceless) (hs : HasFiniteSupp f) :
    traceFinsumPairing g f = ∑ᶠ ι, toPauliCoeffs g ι * toPauliCoeffs f ι := by
  have e := traceFinsumPairing_ofPauliCoeffs hP (toPauliCoeffs g) (toPauliCoeffs f)
    ((hasFiniteSupp_iff hf).1 hs)
  rwa [ofPauliCoeffs_toPauliCoeffs hg, ofPauliCoeffs_toPauliCoeffs hf] at e
theorem apply_mem_traceless {f : σ → ComplexMatrix2}
    (hf : f ∈ GroupLieProduct.tracelessFunctions σ) (i : σ) :
    f i ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.PauliCoefficientNorm.apply_mem_traceless <;> assumption
theorem vertexCoordinates_isFaithfulCoordinates (hP : OneLoop.PauliMatrixRelations) (σ : Type) :
    FaithfulCoordinates.IsFaithfulEvaluation (vertexCoordinate σ) where
  ofCoeffs_mem c := Submodule.mem_pi.2 fun i _ => ofPauliCoeffs_mem_traceless c i
  coeffs_ofCoeffs c := toPauliCoeffs_ofPauliCoeffs c
  ofCoeffs_coeffs _ hf := ofPauliCoeffs_toPauliCoeffs (apply_mem_traceless hf)
  coeffs_linear z _ hf _ hg :=
    toPauliCoeffs_smul_add z (apply_mem_traceless hf) (apply_mem_traceless hg)
  finitelySupported_iff _ hf := hasFiniteSupp_iff (apply_mem_traceless hf)
  pair_eq _ hg _ hf hs :=
    traceFinsumPairing_eq_finsum hP (apply_mem_traceless hg) (apply_mem_traceless hf) hs
end Functions
section Forms
variable {L m k j : ℕ}
theorem edgePauliCoordinates_ofCoeffs_eq (c : Fin 3 × PositiveEdge L m k j → ℂ) :
    (edgePauliCoordinates L m k j).ofCoeffs c = extendOddly (L := L) (n := m) (k := k) (j := j)
      (open Classical in
        fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0) :=
  rfl
theorem edgePauliCoordinates_ofCoeffs_apply_of_pos (c : Fin 3 × PositiveEdge L m k j → ℂ)
    (b : Edge L m k j) (hb : b.IsPositivelyOriented) :
    (edgePauliCoordinates L m k j).ofCoeffs c b = ofPauliCoeffs c ⟨b, hb⟩ := by
  refine (congrFun (edgePauliCoordinates_ofCoeffs_eq c) b).trans ?_
  unfold extendOddly
  rw [if_pos hb]
  exact dif_pos hb
theorem edgePauliCoordinates_ofCoeffs_apply_of_opposite (c : Fin 3 × PositiveEdge L m k j → ℂ)
    (b : Edge L m k j) (hb : ¬ b.IsPositivelyOriented) (hr : b.opposite.IsPositivelyOriented) :
    (edgePauliCoordinates L m k j).ofCoeffs c b = -(edgePauliCoordinates L m k j).ofCoeffs c b.opposite := by
  rw [edgePauliCoordinates_ofCoeffs_apply_of_pos c _ hr]
  refine (congrFun (edgePauliCoordinates_ofCoeffs_eq c) b).trans ?_
  unfold extendOddly
  rw [if_neg hb]
  exact congrArg Neg.neg (dif_pos hr)
theorem restrictToPositiveEdges_ofCoeffs (c : Fin 3 × PositiveEdge L m k j → ℂ) :
    restrictToPositiveEdges ((edgePauliCoordinates L m k j).ofCoeffs c) = ofPauliCoeffs c :=
  funext fun b => edgePauliCoordinates_ofCoeffs_apply_of_pos c b.1 b.2
theorem restrictToPositiveEdges_mem_traceless {B : Edge L m k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L m k j) (b : PositiveEdge L m k j) :
    restrictToPositiveEdges B b ∈ ComplexMatrix2.traceless :=
  hB.1 b.1 b.2
theorem edgePauliCoordinates_isFaithfulRepr (hP : OneLoop.PauliMatrixRelations)
    (hX : ∀ b : Edge L m k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    FaithfulCoordinates.IsFaithfulEvaluation (edgePauliCoordinates L m k j) where
  ofCoeffs_mem c := by
    refine ⟨fun b hb => ?_, fun b => ?_⟩
    · rw [edgePauliCoordinates_ofCoeffs_apply_of_pos c b hb]
      exact ofPauliCoeffs_mem_traceless c _
    · rcases hX b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact edgePauliCoordinates_ofCoeffs_apply_of_opposite c b.opposite h₂ h₁
      · rw [edgePauliCoordinates_ofCoeffs_apply_of_opposite c b h₂ h₁, neg_neg]
  coeffs_ofCoeffs c :=
    (congrArg toPauliCoeffs (restrictToPositiveEdges_ofCoeffs c)).trans
      (toPauliCoeffs_ofPauliCoeffs c)
  ofCoeffs_coeffs f hf := by
    set c := toPauliCoeffs (restrictToPositiveEdges f) with hc
    have hpos : ∀ b (hb : b.IsPositivelyOriented), (edgePauliCoordinates L m k j).ofCoeffs c b = f b :=
      fun b hb => by
        rw [edgePauliCoordinates_ofCoeffs_apply_of_pos c b hb, hc,
          ofPauliCoeffs_toPauliCoeffs (restrictToPositiveEdges_mem_traceless hf)]
        rfl
    show (edgePauliCoordinates L m k j).ofCoeffs c = f
    funext b
    rcases hX b with ⟨h₁, _⟩ | ⟨h₁, h₂⟩
    · exact hpos b h₁
    · rw [edgePauliCoordinates_ofCoeffs_apply_of_opposite c b h₂ h₁, hpos _ h₁, hf.2 b, neg_neg]
  coeffs_linear z _ hf _ hg :=
    toPauliCoeffs_smul_add z (restrictToPositiveEdges_mem_traceless hf)
      (restrictToPositiveEdges_mem_traceless hg)
  finitelySupported_iff _ hf := hasFiniteSupp_iff (restrictToPositiveEdges_mem_traceless hf)
  pair_eq _ hg _ hf hs :=
    traceFinsumPairing_eq_finsum hP (restrictToPositiveEdges_mem_traceless hg)
      (restrictToPositiveEdges_mem_traceless hf) hs
end Forms
theorem levelRestriction_isFaithful (hP : OneLoop.PauliMatrixRelations) {L m k j : ℕ}
    (hX : ∀ b : Edge L m k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (i : Fin 3) :
    FaithfulCoordinates.IsFaithfulEvaluation (RescaledConditions.levelRestriction L m k j i) :=
  match i with
  | 0 => vertexCoordinates_isFaithfulCoordinates hP _
  | 1 => edgePauliCoordinates_isFaithfulRepr hP hX
  | 2 => vertexCoordinates_isFaithfulCoordinates hP _
theorem claim_holds (hF : FaithfulCoordinates.TransposeScales)
    (hP : OneLoop.PauliMatrixRelations)
    (hO : PeriodicLattice.BondEndpointsOrientation.Statement) : Claim := by
  intro L hL k hk m hm i i' j j' hj hj'
  have hX : ∀ {q : ℕ}, q ≤ k →
      ∀ b : Edge L m k q, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun hq b => ((hO ⟨L, hL, ⟨k, hk⟩, ⟨m, hm⟩⟩ _ hq).2.2.2 b).2.2.2.2.2
  exact hF _ _ (levelRestriction_isFaithful hP (hX hj) i)
    (levelRestriction_isFaithful hP (hX hj') i') _ _
end WeightedTransposesOnTorus
end YangMills.Construction.Tower
end
