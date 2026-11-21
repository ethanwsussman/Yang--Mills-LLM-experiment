import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.PeriodicOperators.CalculusOfSymbols
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import YangMills.Construction.Towers.ImagesUnderTheResponseReadAtTheSideInfinity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseImagesFullSide
open YangMills.Construction.PeriodicOperators (ApplySummableAt colourEdges applyKernel shiftEdge)
open YangMills.Construction.PeriodicOperators.SymbolCalculus (TorusProperties IsSidePeriodic)
open YangMills.Construction.Tower.PeriodicForm (coeffsOnEdges)
open YangMills.Construction.Tower.CriticalBranchResponse (IsPeriodicImage periodicImage)
open YangMills.Construction.Tower.ResponseOperators (ClassFnEqForm PeriodicMatrixPreservesLieForms)
open YangMills.Construction.LocalKernels (projPositiveEdge)
open YangMills.Construction.LocalKernels.Periodisation (periodSide)
variable {L n k i j : ℕ}
theorem exists_edgeForm_of_positive_values
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {f : PositiveEdge L n k j → Matrices.ComplexMatrix2}
    (hf : f ∈ Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k j)) :
    ∃ B : edgeFormSpace L n k j,
      restrictToPositiveEdges (B : Edge L n k j → Matrices.ComplexMatrix2) = f := by
  classical
  have hf' : ∀ b, f b ∈ Matrices.ComplexMatrix2.hermitianTraceless := fun b => by
    simp only [Matrices.GroupLieProduct.hermitianTracelessFunctions] at hf
    rw [Submodule.mem_pi] at hf
    exact hf b trivial
  let v : Edge L n k j → Matrices.ComplexMatrix2 :=
    fun b => if h : b.IsPositivelyOriented then f ⟨b, h⟩ else 0
  have hv : ∀ (b : Edge L n k j) (h : b.IsPositivelyOriented), v b = f ⟨b, h⟩ :=
    fun b h => dif_pos h
  have hpos : ∀ {b : Edge L n k j}, b.IsPositivelyOriented → extendOddly v b = v b :=
    fun h => if_pos h
  have hneg : ∀ {b : Edge L n k j}, ¬b.IsPositivelyOriented → extendOddly v b = -v b.opposite :=
    fun h => if_neg h
  have hmem : extendOddly v ∈ edgeFormSpace L n k j := by
    refine ⟨fun b hb => ?_, fun b => ?_⟩
    · rw [hpos hb, hv b hb]
      exact hf' _
    · rcases hx b with ⟨hb, hr⟩ | ⟨hr, hb⟩
      · rw [hneg hr, hpos hb]
        rfl
      · rw [hpos hr, hneg hb, neg_neg]
  refine ⟨⟨extendOddly v, hmem⟩, ?_⟩
  funext b
  show extendOddly v b.1 = f b
  rw [hpos b.2, hv b.1 b.2]
theorem periodicImage_spec_and_coeffs
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hshift : ∀ (m : Fin 4 → ℤ) (b : PeriodicOperators.PosEdge L k i),
      projPositiveEdge L n k i (shiftEdge (periodSide L n • m) b) =
        projPositiveEdge L n k i b)
    (hfin : Finite ((colourEdges L k i).QuotMod (periodSide L n)))
    {T : (colourEdges L k j).Carrier → (colourEdges L k i).Carrier → ℂ}
    (hOT : TorusProperties (colourEdges L k i) (colourEdges L k j) (periodSide L n) T)
    (hM : PeriodicMatrixPreservesLieForms L n k i j T) (B : edgeFormSpace L n k i) :
    IsPeriodicImage L n k i j T B (periodicImage L n k i j T B) ∧
      (∀ ι', ApplySummableAt T (coeffsOnEdges L n k i B) ι') ∧
      coeffsOnEdges L n k j (periodicImage L n k i j T B) =
        applyKernel T (coeffsOnEdges L n k i B) := by
  have hinv : IsSidePeriodic (colourEdges L k i) (periodSide L n)
      (coeffsOnEdges L n k i B) := by
    intro m ι
    show toPauliCoeffs (restrictToPositiveEdges (B : Edge L n k i → Matrices.ComplexMatrix2))
        (ι.1, projPositiveEdge L n k i (shiftEdge (periodSide L n • m) ι.2)) =
      toPauliCoeffs (restrictToPositiveEdges (B : Edge L n k i → Matrices.ComplexMatrix2))
        (ι.1, projPositiveEdge L n k i ι.2)
    rw [hshift]
  obtain ⟨g, hg⟩ : ∃ g : (colourEdges L k i).QuotMod (periodSide L n) → ℂ,
      ∀ ι, g ((colourEdges L k i).mkQuot (periodSide L n) ι) = coeffsOnEdges L n k i B ι := by
    refine ⟨Quot.lift (coeffsOnEdges L n k i B) ?_, fun _ => rfl⟩
    rintro ι _ ⟨m, rfl⟩
    exact (hinv m ι).symm
  have hform : ClassFnEqForm L n k i
      (restrictToPositiveEdges (B : Edge L n k i → Matrices.ComplexMatrix2)) g := hg
  have hbd : ∃ C : ℝ, ∀ ι, ‖coeffsOnEdges L n k i B ι‖ ≤ C := by
    obtain ⟨C, hC⟩ := Finite.bddAbove_range (fun c => ‖g c‖)
    refine ⟨C, fun ι => ?_⟩
    rw [← hg ι]
    exact hC ⟨_, rfl⟩
  have hreal : restrictToPositiveEdges (B : Edge L n k i → Matrices.ComplexMatrix2) ∈
      Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k i) := by
    simp only [Matrices.GroupLieProduct.hermitianTracelessFunctions]
    rw [Submodule.mem_pi]
    intro b _
    exact B.2.1 b.1 b.2
  obtain ⟨f', hf', hcl⟩ := hM.preserves_lie_forms _ hreal g hform
  obtain ⟨B', hB'⟩ := exists_edgeForm_of_positive_values hx hf'
  have hex : ∃ X : edgeFormSpace L n k j, IsPeriodicImage L n k i j T B X :=
    ⟨B', g, hform, by rw [hB']; exact hcl⟩
  have hspec : IsPeriodicImage L n k i j T B (periodicImage L n k i j T B) :=
    Classical.epsilon_spec hex
  refine ⟨hspec, hOT.apply_summable _ hbd hinv, ?_⟩
  obtain ⟨g', hg', hread⟩ := hspec
  have e : g' = g := by
    funext c
    obtain ⟨ι, rfl⟩ : ∃ ι, (colourEdges L k i).mkQuot (periodSide L n) ι = c :=
      Quot.exists_rep c
    exact (hg' ι).trans (hg ι).symm
  subst e
  funext ι'
  exact (hread ι').symm.trans (hOT.periodicMatrix_apply _ hbd hinv g' hg ι')
theorem responseImagesHold (hR : ResponseOperators.Claim)
    (hC : PeriodicOperators.SymbolCalculus.Claim)
    (hI : PeriodicOperators.TowerIndexSets.Claim)
    (hY : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hQ : PeriodicOperators.Quotients.QuotientTransposeNorm) : ResponseImagesHold := by
  intro L hL k hk n hn B
  obtain ⟨δ₀, -, hδ⟩ := hR
  have hA := hδ L hL k hk
  have hs : 0 < periodSide L n := by
    have hL0 : 0 < L := by
      have := hL.2
      omega
    exact Nat.mul_pos (by norm_num) (pow_pos hL0 n)
  have iT := (hI L hL k k le_rfl).2.1
  have iB := (hI L hL k 0 (Nat.zero_le k)).2.1
  obtain ⟨-, -, -, -, -, hTorB, -⟩ := hC _ _ iT iB
  obtain ⟨-, -, -, -, -, hTorT, -⟩ := hC _ _ iT iT
  have hOTh := (hTorB _ hs).2 _ hA.resp_periodic
  have hOTn := (hTorT _ hs).2 _ hA.defect_periodic
  have hfin : Finite ((colourEdges L k k).QuotMod (periodSide L n)) :=
    (hQ _ _ iT iB _ hs).1.2.1
  have hcell := ((hY L hL k n hn).1 k le_rfl).1 LocalKernels.CellType.edge
  have hiff : ∀ x y : PeriodicOperators.PosEdge L k k,
      projPositiveEdge L n k k x = projPositiveEdge L n k k y ↔
        ∃ m : Fin 4 → ℤ, y = shiftEdge (periodSide L n • m) x := hcell.2
  have hshift : ∀ (m : Fin 4 → ℤ) (b : PeriodicOperators.PosEdge L k k),
      projPositiveEdge L n k k (shiftEdge (periodSide L n • m) b) =
        projPositiveEdge L n k k b := fun m b => ((hiff b _).2 ⟨m, rfl⟩).symm
  have hx : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun j hj b =>
    PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (by have := hL.2; omega)
      (by show -(n : ℤ) < (k : ℤ) - (j : ℤ); omega) b
  have hOn := hA.torus_sides n hn
  obtain ⟨a₁, a₂, a₃⟩ :=
    periodicImage_spec_and_coeffs (hx 0 (Nat.zero_le k)) hshift hfin hOTh hOn.resp B
  obtain ⟨b₁, b₂, b₃⟩ := periodicImage_spec_and_coeffs (hx k le_rfl) hshift hfin hOTn hOn.defect B
  exact ⟨a₁, b₁, a₂, b₂, a₃, b₃⟩
end YangMills.Construction.Tower.ResponseImagesFullSide
end
