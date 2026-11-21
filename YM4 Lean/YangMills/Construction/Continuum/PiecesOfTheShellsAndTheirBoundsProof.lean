import YangMills.Construction.ConfigurationSpace.WhitneyPieceBounds
import YangMills.Construction.Continuum.OneSpaceOfTestFunctionsFlatTensorsAndTheDualProof
import YangMills.Construction.Continuum.PiecesOfTheShellsAndTheirBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ShellPieceBounds
open scoped ENNReal
theorem unitBump_eq : Bumps.unitBump = BumpFunctions.normalizedBump := rfl
theorem mollifiedIndicator_eq : Bumps.mollifiedIndicator = BumpFunctions.mollifiedUnitIndicator := by
  funext t
  simp only [Bumps.mollifiedIndicator, BumpFunctions.mollifiedUnitIndicator, MeasureTheory.convolution, unitBump_eq]
  rfl
variable {n : ℕ}
theorem prod_coordIndex {M : Type*} [CommMonoid M] (f : ConfigurationSpace.CoordIndex n → M) :
    ∏ ι, f ι = ∏ i, ∏ c, f (toLex (i, c)) := by
  rw [← Fintype.prod_prod_type']
  exact (Equiv.prod_comp (toLex : Fin n × Fin 4 ≃ Lex (Fin n × Fin 4)) f).symm
theorem sum_coordIndex {M : Type*} [AddCommMonoid M] (f : ConfigurationSpace.CoordIndex n → M) :
    ∑ ι, f ι = ∑ i, ∑ c, f (toLex (i, c)) := by apply _root_.YangMills.Construction.Continuum.UnifiedTestSpace.sum_coordIndex_lex <;> assumption
def latticePtEquiv (n : ℕ) : ShellPieces.LatticePt n ≃ ConfigurationSpace.IntPoint n where
  toFun z := fun ι => z (ofLex ι).1 (ofLex ι).2
  invFun w := fun i c => w (toLex (i, c))
  left_inv _ := rfl
  right_inv _ := rfl
def toMultiIdx (γ : ConfigSpace.MultiIndex n) : ConfigurationSpace.MultiIdx (ConfigurationSpace.CoordIndex n) :=
  fun ι => γ (ofLex ι).1 (ofLex ι).2
theorem order_toMultiIdx (γ : ConfigSpace.MultiIndex n) :
    ConfigurationSpace.MultiIdx.order (toMultiIdx γ) = ConfigSpace.MultiIndex.order γ := by
  simp only [ConfigurationSpace.MultiIdx.order, ConfigSpace.MultiIndex.order, sum_coordIndex]
  rfl
theorem euclidNorm_eq_configNorm (x : ConfigSpace.Config n) : ConfigSpace.euclidNorm x = ConfigurationSpace.configNorm x := by
  simp only [ConfigSpace.euclidNorm, ConfigurationSpace.configNorm, ConfigurationSpace.l2Norm, sum_coordIndex]
  rfl
theorem supNormVec_eq_maxNorm (w : Fin 4 → ℝ) : PeriodicLattice.supNormVec w = ConfigurationSpace.maxNorm w := by
  have hle : ∀ c, |w c| ≤ PeriodicLattice.supNormVec w := fun c =>
    Finset.le_sup' (fun μ => |w μ|) (Finset.mem_univ c)
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun c _ => le_ciSup (f := fun c => |w c|) (Set.finite_range _).bddAbove c
  · exact ciSup_le hle
theorem minSeparation_eq (x : ConfigSpace.Config n) : ConfigSpace.minSeparation x = ConfigurationSpace.minSeparation x := by
  apply le_antisymm
  · refine le_iInf₂ fun p hp => ?_
    have hlt : p.1 < p.2 := by simpa [ConfigurationSpace.orderedPairs] using hp
    rw [← supNormVec_eq_maxNorm]
    exact (iInf_le _ p.1).trans ((iInf_le _ p.2).trans (iInf_le _ hlt))
  · refine le_iInf fun i => le_iInf fun i' => le_iInf fun h => ?_
    rw [supNormVec_eq_maxNorm]
    exact iInf₂_le (i, i') (by simpa [ConfigurationSpace.orderedPairs] using h)
theorem diagonalSet_eq (n : ℕ) : ConfigSpace.diagonalSet n = ConfigurationSpace.fatDiagonal n := by
  ext x
  simp [ConfigSpace.diagonalSet, ConfigurationSpace.fatDiagonal, ConfigurationSpace.orderedPairs, ConfigurationSpace.pairDiagonal]
theorem shellLayer_eq (j : ℕ) :
    (DiagonalShells.shellLayer j : ConfigSpace.Config n → ℝ) = ConfigurationSpace.shellDiff j := by
  cases j <;> rfl
theorem bumpProduct_eq (j : ℕ) (z : ShellPieces.LatticePt n) (x : ConfigSpace.Config n) :
    ShellPieces.bumpProduct j z x = ConfigurationSpace.blockProd j (latticePtEquiv n z) x := by
  simp only [ShellPieces.bumpProduct, ConfigurationSpace.blockProd, prod_coordIndex, mollifiedIndicator_eq]
  rfl
theorem piece_eq (j : ℕ) (z : ShellPieces.LatticePt n) :
    ShellPieces.piece j z = ConfigurationSpace.whitneyPiece j (latticePtEquiv n z) := by
  funext x
  simp only [ShellPieces.piece, ConfigurationSpace.whitneyPiece, shellLayer_eq, bumpProduct_eq]
theorem pieceCentre_eq (j : ℕ) (z : ShellPieces.LatticePt n) :
    ShellPieces.pieceCentre j z = ConfigurationSpace.pieceCenter j (latticePtEquiv n z) := rfl
theorem mem_activeIndices_iff (j : ℕ) (z : ShellPieces.LatticePt n) :
    (j, z) ∈ ShellPieces.activeIndices n ↔ (j, latticePtEquiv n z) ∈ ConfigurationSpace.pieceIndexSet n := by
  simp only [ShellPieces.activeIndices, ConfigurationSpace.pieceIndexSet, Set.mem_ofPred_eq, ConfigurationSpace.IsNonzeroSomewhere,
    piece_eq, Function.ne_iff]
  rfl
theorem shiftSet_box_eq (a : ConfigSpace.Config n) (A : Set ℝ) :
    ShellPieces.shiftSet a {x | ∀ i c, x i c ∈ A} =
      ConfigurationSpace.translateSet a {x | ∀ ι, ConfigurationSpace.coords x ι ∈ A} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, fun ι => hx _ _, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, fun i c => hx (toLex (i, c)), rfl⟩
theorem openBox_eq (j : ℕ) (z : ShellPieces.LatticePt n) :
    ShellPieces.openBox j z = ConfigurationSpace.pieceBox j (latticePtEquiv n z) :=
  shiftSet_box_eq _ _
theorem closedCoreBox_eq (j : ℕ) (z : ShellPieces.LatticePt n) :
    closedCoreBox j z =
      ConfigurationSpace.WhitneyPieceBounds.closedCoreBox j (latticePtEquiv n z) :=
  shiftSet_box_eq _ _
theorem unitBallVol_eq (D : ℕ) : ShellPieces.unitBallVol D = ConfigurationSpace.unitBallVol D := by
  cases D <;> rfl
theorem countConst_eq : ShellPieces.countConst n = ConfigurationSpace.pieceCountConst n := by
  simp only [ShellPieces.countConst, ConfigurationSpace.pieceCountConst, unitBallVol_eq]
  rfl
theorem sort_coordIndex (n : ℕ) :
    (Finset.univ : Finset (ConfigurationSpace.CoordIndex n)).sort (· ≤ ·) =
      (List.finRange n).flatMap fun i =>
        (List.finRange 4).map fun c => (toLex (i, c) : ConfigurationSpace.CoordIndex n) := by apply _root_.YangMills.Construction.Continuum.UnifiedTestSpace.sort_univ_coordIndex <;> assumption
theorem iteratedPartial_eq (γ : ConfigSpace.MultiIndex n) (f : ConfigSpace.Config n → ℂ) :
    ConfigSpace.iteratedPartial γ f = ConfigurationSpace.configMultiDeriv (toMultiIdx γ) f := by
  simp only [ConfigurationSpace.configMultiDeriv, ConfigurationSpace.iterDirDeriv, sort_coordIndex, List.foldr_flatMap,
    List.foldr_map]
  rfl
theorem encard_congr_of_equiv {α β : Type*} (e : α ≃ β) (A : Set α) (B : Set β)
    (h : ∀ a, a ∈ A ↔ e a ∈ B) : A.encard = B.encard := by
  have himage : e '' A = B := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (h a).1 ha
    · intro hb
      exact ⟨e.symm b, (h _).2 (by simpa using hb), by simp⟩
  rw [← himage, e.injective.encard_image]
def indexPairEquiv (n : ℕ) : ℕ × ShellPieces.LatticePt n ≃ ℕ × ConfigurationSpace.IntPoint n :=
  Equiv.prodCongr (Equiv.refl ℕ) (latticePtEquiv n)
def activeIndicesEquiv (n : ℕ) : ShellPieces.activeIndices n ≃ ConfigurationSpace.pieceIndexSet n :=
  Equiv.subtypeEquiv (indexPairEquiv n) fun p => mem_activeIndices_iff p.1 p.2
theorem shellPiecesBound_of_whitney (hW : ConfigurationSpace.WhitneyPieceBounds) : ShellPiecesBound := by
  intro n hn
  obtain ⟨hNest, hPiece, hPart, -, hCube, hCount⟩ := hW n hn
  refine ⟨?_, ?_, ?_, fun _ => rfl, ?_, ?_⟩
  · intro j z i
    exact hNest j (latticePtEquiv n z) i
  · intro j z
    obtain ⟨a, b, c, d, e, f, g, h⟩ := hPiece j (latticePtEquiv n z)
    have hf := piece_eq j z
    have hc : pieceC j z =
        ConfigurationSpace.ofRealFun (ConfigurationSpace.whitneyPiece j (latticePtEquiv n z)) := by
      funext x
      simp only [pieceC, ConfigurationSpace.ofRealFun, hf]
    unfold PieceProperties
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hc]
      exact a
    · intro x
      rw [hf]
      exact b x
    · rw [hf, closedCoreBox_eq]
      exact c
    · rw [closedCoreBox_eq, openBox_eq]
      exact d
    · rw [openBox_eq]
      exact e
    · rw [hf]
      exact f
    · rw [hf]
      exact g
    · intro γ x
      have hb := h (toMultiIdx γ) x
      rw [order_toMultiIdx] at hb
      rw [iteratedPartial_eq, hc]
      exact hb
  · intro x hx
    obtain ⟨h₁, h₂⟩ := hPart x hx
    constructor
    · have hcard : ShellPieces.cardOf
          {p : ℕ × ShellPieces.LatticePt n | ShellPieces.piece p.1 p.2 x ≠ 0} =
          ConfigurationSpace.setCard
            {p : ℕ × ConfigurationSpace.IntPoint n | ConfigurationSpace.whitneyPiece p.1 p.2 x ≠ 0} :=
        encard_congr_of_equiv (indexPairEquiv n) _ _ fun p => by
          show ShellPieces.piece p.1 p.2 x ≠ 0 ↔
            ConfigurationSpace.whitneyPiece p.1 (latticePtEquiv n p.2) x ≠ 0
          rw [piece_eq]
      rw [hcard]
      exact h₁
    · refine Eq.trans ?_ h₂
      rw [← Equiv.tsum_eq (activeIndicesEquiv n)]
      refine tsum_congr fun p => ?_
      rw [piece_eq]
      rfl
  · rintro ⟨j, z⟩ hp
    obtain ⟨a, b, c, d, e⟩ := hCube _ ((mem_activeIndices_iff j z).1 hp)
    unfold BoxGeometry
    refine ⟨a, b, c, ?_, ?_⟩
    · intro hj x hx
      rw [openBox_eq] at hx
      obtain ⟨u, y, hy, v⟩ := d hj x hx
      refine ⟨?_, y, ?_, ?_⟩
      · rw [minSeparation_eq]
        exact u
      · rw [diagonalSet_eq]
        exact hy
      · rw [euclidNorm_eq_configNorm]
        exact v
    · intro x hx
      rw [openBox_eq] at hx
      simp only [euclidNorm_eq_configNorm, pieceCentre_eq]
      exact e x hx
  · intro j t
    have hcard : ShellPieces.cardOf (centresInAnnulus n j t) =
        ConfigurationSpace.setCard (ConfigurationSpace.WhitneyPieceBounds.shellCenters n j t) :=
      encard_congr_of_equiv (latticePtEquiv n) _ _ fun z => by
        simp only [centresInAnnulus, ConfigurationSpace.WhitneyPieceBounds.shellCenters,
          Set.mem_ofPred_eq, mem_activeIndices_iff, euclidNorm_eq_configNorm, pieceCentre_eq]
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · rw [hcard, countConst_eq]
      exact (hCount j t).1 hj
    · rw [hcard, countConst_eq]
      exact (hCount j t).2 hj
end YangMills.Construction.ShellPieceBounds
end
