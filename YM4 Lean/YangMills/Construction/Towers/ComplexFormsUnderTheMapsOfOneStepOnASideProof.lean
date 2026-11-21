import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnASide
import YangMills.Construction.Towers.LinearMapsAreOnto
import YangMills.Construction.Towers.LinearMapsOnConstantForms
import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOfTheLinearMapsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.ComplexCoarsening
open YangMills.Construction.Matrices
def reComponent (X : ComplexMatrix2) : ComplexMatrix2 := (1 / 2 : ℂ) • (X + X.conjTranspose)
def imComponent (X : ComplexMatrix2) : ComplexMatrix2 := (-Complex.I / 2) • (X - X.conjTranspose)
theorem reComponent_add_I_smul_imComponent (X : ComplexMatrix2) :
    reComponent X + Complex.I • imComponent X = X := by
  have hI : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
  simp only [reComponent, imComponent]
  rw [smul_smul, hI]
  module
theorem reComponent_neg (X : ComplexMatrix2) : reComponent (-X) = -reComponent X := by
  simp only [reComponent, Matrix.conjTranspose_neg]
  module
theorem imComponent_neg (X : ComplexMatrix2) : imComponent (-X) = -imComponent X := by
  simp only [imComponent, Matrix.conjTranspose_neg]
  module
theorem reComponent_mem_hermitianTraceless {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) : reComponent X ∈ ComplexMatrix2.hermitianTraceless := by
  have t : Matrix.trace X = 0 := hX
  refine ⟨?_, ?_⟩
  · simp only [reComponent]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      add_comm X]
    congr 1
    simp
  · show Matrix.trace _ = 0
    simp only [reComponent]
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_conjTranspose, t]
    simp
theorem imComponent_mem_hermitianTraceless {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) : imComponent X ∈ ComplexMatrix2.hermitianTraceless := by
  have t : Matrix.trace X = 0 := hX
  refine ⟨?_, ?_⟩
  · simp only [imComponent]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    have hs : star (-Complex.I / 2) = Complex.I / 2 := by
      simp [Complex.conj_I]
    rw [hs]
    module
  · show Matrix.trace _ = 0
    simp only [imComponent]
    rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose, t]
    simp
theorem ofReal_norm_smul_sum_le {ι : Type*} (s : Finset ι) (w : ℝ) (hw : 0 ≤ w)
    (hwc : w * s.card ≤ 1) (f : ι → ComplexMatrix2) (C : ℝ≥0∞)
    (h : ∀ i ∈ s, ENNReal.ofReal ‖f i‖ ≤ C) :
    ENNReal.ofReal ‖(w : ℂ) • ∑ i ∈ s, f i‖ ≤ C := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_norm_smul_sum_le_of_card <;> assumption
theorem ofReal_norm_list_sum_le_length_mul {β : Type*} (A : β → ComplexMatrix2) (Γ : List β) :
    ENNReal.ofReal ‖(Γ.map A).sum‖ ≤ (Γ.length : ℝ≥0∞) * maxOperatorNorm A := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_norm_list_sum_le_length_mul <;> assumption
theorem ofReal_norm_weight_finsum_le {L : ℕ} (hL : 0 < L) {ι : Type*} {S : Set ι}
    (hS : S.Finite) (hc : S.ncard ≤ L ^ 4) (f : ι → ComplexMatrix2) (C : ℝ≥0∞)
    (h : ∀ x ∈ S, ENNReal.ofReal ‖f x‖ ≤ C) :
    ENNReal.ofReal ‖PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ S, f x‖ ≤ C := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_norm_weight_smul_finsum_le <;> assumption
theorem finsum_mem_add_smul {ι : Type*} {S : Set ι} (hS : S.Finite) (z : ℂ)
    (f g : ι → ComplexMatrix2) :
    ∑ᶠ x ∈ S, (f x + z • g x) = ∑ᶠ x ∈ S, f x + z • ∑ᶠ x ∈ S, g x := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS,
    finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_add_distrib, Finset.smul_sum]
section RealSubspace
variable (W : Submodule ℝ ComplexMatrix2)
theorem ofReal_smul_mem (w : ℝ) {X : ComplexMatrix2} (hX : X ∈ W) : (w : ℂ) • X ∈ W := by
  have h : (w : ℂ) • X = w • X := by
    ext i j
    simp
  rw [h]
  exact W.smul_mem w hX
theorem list_map_sum_mem {β : Type*} (A : β → ComplexMatrix2) (h : ∀ b, A b ∈ W)
    (Γ : List β) : (Γ.map A).sum ∈ W := by
  induction Γ with
  | nil => simp
  | cons b Γ ih => simpa using W.add_mem (h b) ih
theorem weight_smul_finsum_mem (L : ℕ) {ι : Type*} {S : Set ι} (hS : S.Finite)
    (f : ι → ComplexMatrix2) (h : ∀ x ∈ S, f x ∈ W) :
    PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ S, f x ∈ W := by
  refine ofReal_smul_mem W ((L : ℝ) ^ (-4 : ℤ)) ?_
  rw [finsum_mem_eq_finite_toFinset_sum f hS]
  exact W.sum_mem fun i hi => h i (hS.mem_toFinset.1 hi)
end RealSubspace
section Coarsening
variable {L n k : ℕ}
abbrev tracelessReal : Submodule ℝ ComplexMatrix2 := ComplexMatrix2.traceless.restrictScalars ℝ
theorem bondForm_apply_mem (W : Submodule ℝ ComplexMatrix2) {j : ℕ}
    {B : Edge L n k j → ComplexMatrix2}
    (hB : PeriodicLattice.IsBondForm (W : Set ComplexMatrix2) B) (b : Edge L n k j) : B b ∈ W := by
  obtain ⟨h, r⟩ := hB
  obtain ⟨μ, hμ | hμ⟩ := b.isNeighbour
  · exact h b ⟨μ, hμ⟩
  · have hp : b.opposite.IsPositivelyOriented := ⟨μ, by
      show b.source - b.target = _
      rw [← neg_sub, hμ, neg_neg]⟩
    have h' := W.neg_mem (h _ hp)
    rwa [r, neg_neg] at h'
theorem sitesInBlock_finite_and_ncard_le (hBlk : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    (y : Vertex L n k (j + 1)) :
    (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite ∧
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).ncard ≤ L ^ 4 := by apply _root_.YangMills.Construction.Tower.IterateBounds.sitesInBlock_finite_and_ncard_le <;> assumption
theorem contourFormAverage_mem (W : Submodule ℝ ComplexMatrix2) {i j : ℕ}
    {B : Edge L n k j → ComplexMatrix2}
    (hB : PeriodicLattice.IsBondForm (W : Set ComplexMatrix2) B) (y : Vertex L n k i)
    (x : Vertex L n k j) : PeriodicLattice.contourFormAverage B y x ∈ W :=
  ofReal_smul_mem W _ (W.sum_mem fun _ _ => list_map_sum_mem W B (bondForm_apply_mem W hB) _)
theorem crossingSmoothing_apply_mem (W : Submodule ℝ ComplexMatrix2) {j : ℕ}
    {B : Edge L n k j → ComplexMatrix2}
    (hfin : ∀ y : Vertex L n k (j + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite)
    (hB : PeriodicLattice.IsBondForm (W : Set ComplexMatrix2) B) (c : Edge L n k (j + 1)) :
    crossingSmoothing L n k j B c ∈ W :=
  weight_smul_finsum_mem W L (hfin c.source) _ fun _ _ =>
    list_map_sum_mem W B (bondForm_apply_mem W hB) _
theorem linearSmoothing_apply_mem (W : Submodule ℝ ComplexMatrix2) {j : ℕ}
    {B : Edge L n k j → ComplexMatrix2}
    (hfin : ∀ y : Vertex L n k (j + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite)
    (hB : PeriodicLattice.IsBondForm (W : Set ComplexMatrix2) B) (c : Edge L n k (j + 1)) :
    linearSmoothing L n k j B c ∈ W := by
  show PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum B c ∈ W
  unfold PeriodicLattice.linearBlockSum
  exact weight_smul_finsum_mem W L (hfin c.source) _ fun x _ =>
    W.sub_mem (W.add_mem (contourFormAverage_mem W hB _ _)
      (list_map_sum_mem W B (bondForm_apply_mem W hB) _)) (contourFormAverage_mem W hB _ _)
theorem cubeContourAverage_apply_mem (W : Submodule ℝ ComplexMatrix2) {j : ℕ}
    {B : Edge L n k j → ComplexMatrix2}
    (hfin : ∀ y : Vertex L n k (j + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite)
    (hB : PeriodicLattice.IsBondForm (W : Set ComplexMatrix2) B) (y : Vertex L n k (j + 1)) :
    cubeContourAverage L n k j B y ∈ W :=
  weight_smul_finsum_mem W L (hfin y) _ fun _ _ => contourFormAverage_mem W hB _ _
theorem vertexSmoothing_apply_mem (W : Submodule ℝ ComplexMatrix2) {j : ℕ}
    {l : Vertex L n k j → ComplexMatrix2}
    (hfin : ∀ y : Vertex L n k (j + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite)
    (hl : ∀ x, l x ∈ W) (y : Vertex L n k (j + 1)) : vertexSmoothing L n k j l y ∈ W :=
  weight_smul_finsum_mem W L (hfin y) _ fun x _ => hl x
theorem bondFormSumAlong_add_smul {j : ℕ} (A A' : Edge L n k j → ComplexMatrix2) (z : ℂ)
    (Γ : List (Edge L n k j)) :
    PeriodicLattice.bondFormSumAlong (A + z • A') Γ =
      PeriodicLattice.bondFormSumAlong A Γ + z • PeriodicLattice.bondFormSumAlong A' Γ := by
  induction Γ with
  | nil => simp [PeriodicLattice.bondFormSumAlong]
  | cons b Γ ih =>
    simp only [PeriodicLattice.bondFormSumAlong, List.map_cons, List.sum_cons, Pi.add_apply,
      Pi.smul_apply] at ih ⊢
    rw [ih, smul_add]
    abel
theorem contourFormAverage_add_smul {i j : ℕ} (A A' : Edge L n k j → ComplexMatrix2) (z : ℂ)
    (y : Vertex L n k i) (x : Vertex L n k j) :
    PeriodicLattice.contourFormAverage (A + z • A') y x =
      PeriodicLattice.contourFormAverage A y x + z • PeriodicLattice.contourFormAverage A' y x := by
  simp only [PeriodicLattice.contourFormAverage, bondFormSumAlong_add_smul,
    Finset.sum_add_distrib, ← Finset.smul_sum, smul_add]
  rw [smul_comm z]
variable {j : ℕ}
theorem crossingSmoothing_add_smul
    (hfin : ∀ y : Vertex L n k (j + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite)
    (A A' : Edge L n k j → ComplexMatrix2) (z : ℂ) :
    crossingSmoothing L n k j (A + z • A') =
      crossingSmoothing L n k j A + z • crossingSmoothing L n k j A' := by
  funext c
  simp only [crossingSmoothing, edgeFormPathSum, bondFormSumAlong_add_smul, Pi.add_apply,
    Pi.smul_apply]
  rw [finsum_mem_add_smul (hfin c.source), smul_add, smul_comm z]
theorem cubeContourAverage_add_smul
    (hfin : ∀ y : Vertex L n k (j + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite)
    (A A' : Edge L n k j → ComplexMatrix2) (z : ℂ) :
    cubeContourAverage L n k j (A + z • A') =
      cubeContourAverage L n k j A + z • cubeContourAverage L n k j A' := by
  funext y
  simp only [cubeContourAverage, contourFormAverage_add_smul, Pi.add_apply, Pi.smul_apply]
  rw [finsum_mem_add_smul (hfin y), smul_add, smul_comm z]
theorem vertexSmoothing_add_smul
    (hfin : ∀ y : Vertex L n k (j + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite)
    (l l' : Vertex L n k j → ComplexMatrix2) (z : ℂ) :
    vertexSmoothing L n k j (l + z • l') =
      vertexSmoothing L n k j l + z • vertexSmoothing L n k j l' := by
  funext y
  simp only [vertexSmoothing, Pi.add_apply, Pi.smul_apply]
  rw [finsum_mem_add_smul (hfin y), smul_add, smul_comm z]
theorem linearSmoothing_add_smul
    (hfin : ∀ y : Vertex L n k (j + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite)
    (A A' : Edge L n k j → ComplexMatrix2) (z : ℂ) :
    linearSmoothing L n k j (A + z • A') =
      linearSmoothing L n k j A + z • linearSmoothing L n k j A' := by
  funext c
  show PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum (A + z • A') c =
    PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum A c +
      z • PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum A' c
  unfold PeriodicLattice.linearBlockSum
  have key : ∀ x, PeriodicLattice.contourFormAverage (A + z • A') c.source x +
        PeriodicLattice.bondFormSumAlong (A + z • A') (PeriodicLattice.crossingPath c x) -
        PeriodicLattice.contourFormAverage (A + z • A') c.target
          (PeriodicLattice.shiftAcross c x) =
      (PeriodicLattice.contourFormAverage A c.source x +
        PeriodicLattice.bondFormSumAlong A (PeriodicLattice.crossingPath c x) -
        PeriodicLattice.contourFormAverage A c.target (PeriodicLattice.shiftAcross c x)) +
      z • (PeriodicLattice.contourFormAverage A' c.source x +
        PeriodicLattice.bondFormSumAlong A' (PeriodicLattice.crossingPath c x) -
        PeriodicLattice.contourFormAverage A' c.target (PeriodicLattice.shiftAcross c x)) :=
    fun x => by
      rw [contourFormAverage_add_smul, contourFormAverage_add_smul, bondFormSumAlong_add_smul]
      module
  simp only [key]
  rw [finsum_mem_add_smul (hfin c.source), smul_add, smul_comm z]
theorem vertexCoboundary_add_smul (l l' : Vertex L n k j → ComplexMatrix2) (z : ℂ) :
    vertexCoboundary (l + z • l') = vertexCoboundary l + z • vertexCoboundary l' := by
  funext b
  show (l b.target + z • l' b.target) - (l b.source + z • l' b.source) =
    (l b.target - l b.source) + z • (l' b.target - l' b.source)
  module
theorem restrictVertexFunction_add_smul (i : ℕ) (l l' : Vertex L n k j → ComplexMatrix2)
    (z : ℂ) :
    restrictVertexFunction i (l + z • l') =
      restrictVertexFunction i l + z • restrictVertexFunction i l' :=
  funext fun _ => rfl
theorem mem_complexEdgeForms_of_mem {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) : B ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_complexEdgeForms_of_mem <;> assumption
theorem exists_decomposition_edgeForm {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) :
    ∃ B₁ ∈ edgeFormSpace L n k j, ∃ B₂ ∈ edgeFormSpace L n k j, B = B₁ + Complex.I • B₂ := by
  obtain ⟨h, r⟩ := hB
  refine ⟨fun b => reComponent (B b),
    ⟨fun b hb => reComponent_mem_hermitianTraceless (h b hb), fun b => ?_⟩,
    fun b => imComponent (B b),
    ⟨fun b hb => imComponent_mem_hermitianTraceless (h b hb), fun b => ?_⟩,
    funext fun b => (reComponent_add_I_smul_imComponent (B b)).symm⟩
  · simp only [r, reComponent_neg]
  · simp only [r, imComponent_neg]
theorem exists_decomposition_vertexFunction {f : Vertex L n k j → ComplexMatrix2}
    (hf : f ∈ GroupLieProduct.tracelessFunctions (Vertex L n k j)) :
    ∃ l₁ ∈ vertexFunctionSpace L n k j, ∃ l₂ ∈ vertexFunctionSpace L n k j,
      f = l₁ + Complex.I • l₂ := by
  have h : ∀ x, f x ∈ ComplexMatrix2.traceless := fun x =>
    Submodule.mem_pi.1 hf x (Set.mem_univ x)
  exact ⟨fun x => reComponent (f x),
    Submodule.mem_pi.2 fun x _ => reComponent_mem_hermitianTraceless (h x),
    fun x => imComponent (f x),
    Submodule.mem_pi.2 fun x _ => imComponent_mem_hermitianTraceless (h x),
    funext fun x => (reComponent_add_I_smul_imComponent (f x)).symm⟩
theorem ofReal_norm_contourFormAverage_le (hLen : PeriodicLattice.DoubleBlockPathLengths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (B : Edge L n k j → ComplexMatrix2) (y : Vertex L n k (j + 1)) (x : Vertex L n k j)
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    ENNReal.ofReal ‖PeriodicLattice.contourFormAverage B y x‖ ≤
      2 * ((L : ℝ≥0∞) - 1) * maxOperatorNorm B := by
  refine ofReal_norm_smul_sum_le Finset.univ _ (by positivity) ?_ _ _ fun σ _ => ?_
  · rw [Finset.card_univ]
    exact inv_mul_le_one
  · have h := ofReal_norm_list_sum_le_length_mul B (PeriodicLattice.orderedContour y x σ)
    refine h.trans ?_
    have hlen := (hLen L n k j hL hn hj).contour y x hx σ
    have hc : ((PeriodicLattice.orderedContour y x σ).length : ℝ≥0∞) ≤
        2 * ((L : ℝ≥0∞) - 1) := by
      calc ((PeriodicLattice.orderedContour y x σ).length : ℝ≥0∞) ≤
            ((2 * (L - 1) : ℕ) : ℝ≥0∞) := by
            exact_mod_cast hlen
        _ = 2 * ((L : ℝ≥0∞) - 1) := by
            rw [Nat.cast_mul, ENNReal.natCast_sub]
            simp
    gcongr
theorem ofReal_norm_cubeContourAverage_le (hLen : PeriodicLattice.DoubleBlockPathLengths)
    (hBlk : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) (B : Edge L n k j → ComplexMatrix2) (y : Vertex L n k (j + 1)) :
    ENNReal.ofReal ‖cubeContourAverage L n k j B y‖ ≤
      2 * ((L : ℝ≥0∞) - 1) * maxOperatorNorm B := by
  obtain ⟨hfin, hcard⟩ := sitesInBlock_finite_and_ncard_le hBlk hL hn hj y
  have hpos : 0 < L := by have := hL.2; omega
  exact ofReal_norm_weight_finsum_le hpos hfin hcard _ _ fun x hx =>
    ofReal_norm_contourFormAverage_le hLen hL hn hj B y x hx
end Coarsening
theorem periodicCoarseningStep_holds (hStep : TrivialLinearization.OneStepIdentitiesHold)
    (hConst : LinearizationFacts.constantFormsStatement)
    (hOnto : LinearizationFacts.surjectivityStatement)
    (hRev : AxisPathReversal.MainStatement) (hBlk : BlockStructure)
    (hLen : PeriodicLattice.DoubleBlockPathLengths) : PeriodicCoarseningStep.Holds := by
  intro L hL m k i hm hi
  have hj : i < k := hi
  have hfin : ∀ y : Vertex L m k (i + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y).Finite :=
    fun y => (sitesInBlock_finite_and_ncard_le hBlk hL hm hj y).1
  have hrel := hStep L hL m k i hm hj
  have hcon := hConst L hL m k i hm hj
  have hont := hOnto L hL m k i 0 hm hj (Nat.zero_le k)
  have hrev := ((hRev L hL k).1 m hm).2 i hi
  have hcomplex : ∀ {B : Edge L m k i → ComplexMatrix2}, B ∈ complexEdgeForms L m k i →
      PeriodicLattice.IsBondForm ((tracelessReal : Submodule ℝ ComplexMatrix2) :
        Set ComplexMatrix2) B := fun hB => hB
  have hreal : ∀ {B : Edge L m k i → ComplexMatrix2}, B ∈ edgeFormSpace L m k i →
      PeriodicLattice.IsBondForm ((ComplexMatrix2.hermitianTraceless :
        Submodule ℝ ComplexMatrix2) : Set ComplexMatrix2) B := fun hB => hB
  refine
    { linearSmoothing_sub := ?_
      linearSmoothing_mapsTo := ?_
      crossingSmoothing_mapsTo := ?_
      linearSmoothing_mapsTo_real := ?_
      crossingSmoothing_mapsTo_real := ?_
      cubeContourAverage_mapsTo := ?_
      vertexSmoothing_mapsTo := ?_
      linearSmoothing_eq := ?_
      linearSmoothing_vertexCoboundary := ?_
      crossingSmoothing_vertexCoboundary := ?_
      cubeContourAverage_vertexCoboundary := ?_
      of_constant := ?_
      linearSmoothing_surjOn := ?_
      crossingSmoothing_surjOn := ?_
      linearSmoothing_surjOn_real := ?_
      crossingSmoothing_surjOn_real := ?_
      maxOperatorNorm_cubeContourAverage_le := ?_ }
  · intro B _ B' _
    have h : B - B' = B + (-1 : ℂ) • B' := by module
    rw [h, linearSmoothing_add_smul hfin]
    module
  · intro B hB
    exact ⟨fun c _ => linearSmoothing_apply_mem tracelessReal hfin (hcomplex hB) c,
      fun c => (hrev c B hB).2⟩
  · intro B hB
    refine ⟨fun c _ => crossingSmoothing_apply_mem tracelessReal hfin (hcomplex hB) c,
      fun c => ?_⟩
    simp only [crossingSmoothing]
    rw [(hrev c B hB).1, smul_neg]
  · intro B hB
    exact ⟨fun c _ => linearSmoothing_apply_mem ComplexMatrix2.hermitianTraceless hfin
        (hreal hB) c,
      fun c => (hrev c B (mem_complexEdgeForms_of_mem hB)).2⟩
  · intro B hB
    refine ⟨fun c _ => crossingSmoothing_apply_mem ComplexMatrix2.hermitianTraceless hfin
        (hreal hB) c, fun c => ?_⟩
    simp only [crossingSmoothing]
    rw [(hrev c B (mem_complexEdgeForms_of_mem hB)).1, smul_neg]
  · intro B hB
    exact Submodule.mem_pi.2 fun y _ =>
      cubeContourAverage_apply_mem tracelessReal hfin (hcomplex hB) y
  · intro l hl
    exact Submodule.mem_pi.2 fun y _ => vertexSmoothing_apply_mem tracelessReal hfin
      (fun x => Submodule.mem_pi.1 hl x (Set.mem_univ x)) y
  · intro B hB
    obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := exists_decomposition_edgeForm hB
    rw [linearSmoothing_add_smul hfin, crossingSmoothing_add_smul hfin,
      cubeContourAverage_add_smul hfin, vertexCoboundary_add_smul, hrel.1 B₁ h₁, hrel.1 B₂ h₂]
    module
  · intro f hf
    obtain ⟨l₁, h₁, l₂, h₂, rfl⟩ := exists_decomposition_vertexFunction hf
    rw [vertexCoboundary_add_smul, linearSmoothing_add_smul hfin,
      restrictVertexFunction_add_smul, vertexCoboundary_add_smul, (hrel.2 l₁ h₁).1,
      (hrel.2 l₂ h₂).1]
  · intro f hf
    obtain ⟨l₁, h₁, l₂, h₂, rfl⟩ := exists_decomposition_vertexFunction hf
    rw [vertexCoboundary_add_smul, crossingSmoothing_add_smul hfin,
      vertexSmoothing_add_smul hfin, vertexCoboundary_add_smul, (hrel.2 l₁ h₁).2.1,
      (hrel.2 l₂ h₂).2.1]
  · intro f hf
    obtain ⟨l₁, h₁, l₂, h₂, rfl⟩ := exists_decomposition_vertexFunction hf
    rw [vertexCoboundary_add_smul, cubeContourAverage_add_smul hfin,
      vertexSmoothing_add_smul hfin, restrictVertexFunction_add_smul, (hrel.2 l₁ h₁).2.2.1,
      (hrel.2 l₂ h₂).2.2.1]
    module
  · intro B hB a ha
    obtain ⟨h, r⟩ := id hB
    have hB₁ : (fun b => reComponent (B b)) ∈ edgeFormSpace L m k i :=
      ⟨fun b hb => reComponent_mem_hermitianTraceless (h b hb),
        fun b => by simp only [r, reComponent_neg]⟩
    have hB₂ : (fun b => imComponent (B b)) ∈ edgeFormSpace L m k i :=
      ⟨fun b hb => imComponent_mem_hermitianTraceless (h b hb),
        fun b => by simp only [r, imComponent_neg]⟩
    have hs : B = (fun b => reComponent (B b)) + Complex.I • (fun b => imComponent (B b)) :=
      funext fun b => (reComponent_add_I_smul_imComponent (B b)).symm
    obtain ⟨-, n₁, q₁, -, c₁⟩ := hcon _ hB₁ (fun μ => reComponent (a μ)) fun x μ => by
      simp only [ha]
    obtain ⟨-, n₂, q₂, -, c₂⟩ := hcon _ hB₂ (fun μ => imComponent (a μ)) fun x μ => by
      simp only [ha]
    refine ⟨?_, ?_, fun x μ => ?_⟩
    · rw [hs, cubeContourAverage_add_smul hfin, n₁, n₂]
      simp
    · rw [hs, linearSmoothing_add_smul hfin, crossingSmoothing_add_smul hfin, q₁, q₂]
    · rw [hs, crossingSmoothing_add_smul hfin, Pi.add_apply, Pi.smul_apply, c₁, c₂,
        smul_comm Complex.I, ← smul_add, reComponent_add_I_smul_imComponent]
  · intro C hC
    obtain ⟨C₁, h₁, C₂, h₂, rfl⟩ := exists_decomposition_edgeForm hC
    obtain ⟨B₁, g₁, e₁⟩ := hont.1 C₁ h₁
    obtain ⟨B₂, g₂, e₂⟩ := hont.1 C₂ h₂
    exact ⟨B₁ + Complex.I • B₂,
      (complexEdgeForms L m k i).add_mem (mem_complexEdgeForms_of_mem g₁)
        ((complexEdgeForms L m k i).smul_mem _ (mem_complexEdgeForms_of_mem g₂)),
      by rw [linearSmoothing_add_smul hfin, e₁, e₂]⟩
  · intro C hC
    obtain ⟨C₁, h₁, C₂, h₂, rfl⟩ := exists_decomposition_edgeForm hC
    obtain ⟨B₁, g₁, e₁⟩ := hont.2.1 C₁ h₁
    obtain ⟨B₂, g₂, e₂⟩ := hont.2.1 C₂ h₂
    exact ⟨B₁ + Complex.I • B₂,
      (complexEdgeForms L m k i).add_mem (mem_complexEdgeForms_of_mem g₁)
        ((complexEdgeForms L m k i).smul_mem _ (mem_complexEdgeForms_of_mem g₂)),
      by rw [crossingSmoothing_add_smul hfin, e₁, e₂]⟩
  · intro C hC
    obtain ⟨B, g, e⟩ := hont.1 C hC
    exact ⟨B, g, e⟩
  · intro C hC
    obtain ⟨B, g, e⟩ := hont.2.1 C hC
    exact ⟨B, g, e⟩
  · intro B _
    exact iSup_le fun y => ofReal_norm_cubeContourAverage_le hLen hBlk hL hm hj B y
end YangMills.Construction.Tower.ComplexCoarsening
end
