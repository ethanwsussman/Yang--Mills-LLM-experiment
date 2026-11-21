import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Towers.CriterionForLocalKernelsWithEntireEntries
import YangMills.Construction.Towers.EntireCoordinatesAreClosed
import YangMills.Construction.Towers.EntriesOfTheConfigurationOfAField
import YangMills.Construction.Towers.EntriesOfTheHessianCurvatureKernel
import YangMills.Construction.Towers.FourierSumsOnTheSitesOfTheFinestLatticeProof
import YangMills.Construction.Towers.HessianCurvatureKernelOfAFieldIsLocal
import YangMills.Construction.Towers.PlaquettesOfABond
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.TranslatedConfigurationOfAField
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.EntireDependence
open YangMills.Construction.Tower.FullSpace.BackgroundJets (gaugeFieldOfForm)
open YangMills.Construction.TorusMetric (euclidNormVec)
def cornerTransports (W : Fin 4 → ComplexMatrix2) : Fin 4 → ComplexMatrix2 :=
  ![1, W 0, W 0 * W 1 * (W 2)⁻¹, W 0 * W 1 * (W 2)⁻¹ * (W 3)⁻¹]
def cornerTransportsInv (W : Fin 4 → ComplexMatrix2) : Fin 4 → ComplexMatrix2 :=
  ![1, (W 0)⁻¹, W 2 * (W 1)⁻¹ * (W 0)⁻¹, W 3 * W 2 * (W 1)⁻¹ * (W 0)⁻¹]
theorem inv_cornerTransports {W : Fin 4 → ComplexMatrix2} (hW : ∀ i, (W i).det = 1) (i : Fin 4) :
    (cornerTransports W i)⁻¹ = cornerTransportsInv W i := by
  have hu : ∀ i, (W i)⁻¹⁻¹ = W i := fun i =>
    Matrix.nonsing_inv_nonsing_inv _ (by rw [hW i]; exact isUnit_one)
  fin_cases i
  · simp [cornerTransports, cornerTransportsInv]
  · simp [cornerTransports, cornerTransportsInv]
  · simp [cornerTransports, cornerTransportsInv, Matrix.mul_inv_rev, hu, mul_assoc]
  · simp [cornerTransports, cornerTransportsInv, Matrix.mul_inv_rev, hu, mul_assoc]
def conjugatedValues (W X : Fin 4 → ComplexMatrix2) : Fin 4 → ComplexMatrix2 :=
  fun i => transportSign i • (cornerTransports W i * X i * cornerTransportsInv W i)
def strengthMatrix (η : ℂ) (W : Fin 4 → ComplexMatrix2) : ComplexMatrix2 :=
  (1 / (2 * Complex.I * η ^ 2)) • (cornerTransports W 3 - cornerTransportsInv W 3)
def faceTerm (η : ℂ) (W X X' : Fin 4 → ComplexMatrix2) : ℂ :=
  (Complex.I / 2) * ComplexMatrix2.fullTrace
    (bracketSumOrdered (conjugatedValues W X) (conjugatedValues W X') * strengthMatrix η W)
def EntrywiseEntire (F : PeriodicData) (S : Finset F.Carrier)
    (A : (F.Carrier → ℂ) → ComplexMatrix2) : Prop :=
  ∀ r s, IsEntireOn F S fun ζ => A ζ r s
section Entrywise
variable {F : PeriodicData} {S : Finset F.Carrier}
theorem entrywiseEntire_const (hC : EntireDependenceClosed) (X : ComplexMatrix2) :
    EntrywiseEntire F S fun _ => X :=
  fun r s => (hC F S).1 (X r s)
theorem entrywiseEntire_add (hC : EntireDependenceClosed) {A B : (F.Carrier → ℂ) → ComplexMatrix2}
    (hA : EntrywiseEntire F S A) (hB : EntrywiseEntire F S B) :
    EntrywiseEntire F S fun ζ => A ζ + B ζ :=
  fun r s => ((hC F S).2.2.1 _ _ (hA r s) (hB r s)).1
theorem entrywiseEntire_mul (hC : EntireDependenceClosed) {A B : (F.Carrier → ℂ) → ComplexMatrix2}
    (hA : EntrywiseEntire F S A) (hB : EntrywiseEntire F S B) :
    EntrywiseEntire F S fun ζ => A ζ * B ζ := by
  intro r s
  have hm : ∀ t, IsEntireOn F S fun ζ => A ζ r t * B ζ t s := fun t =>
    ((hC F S).2.2.1 _ _ (hA r t) (hB t s)).2
  have := ((hC F S).2.2.1 _ _ (hm 0) (hm 1)).1
  simpa only [Matrix.mul_apply, Fin.sum_univ_two] using this
theorem entrywiseEntire_smul (hC : EntireDependenceClosed) (c : ℂ)
    {A : (F.Carrier → ℂ) → ComplexMatrix2}
    (hA : EntrywiseEntire F S A) : EntrywiseEntire F S fun ζ => c • A ζ := by
  intro r s
  have := ((hC F S).2.2.1 _ _ ((hC F S).1 c) (hA r s)).2
  simpa only [Matrix.smul_apply, smul_eq_mul] using this
theorem entrywiseEntire_sub (hC : EntireDependenceClosed) {A B : (F.Carrier → ℂ) → ComplexMatrix2}
    (hA : EntrywiseEntire F S A) (hB : EntrywiseEntire F S B) :
    EntrywiseEntire F S fun ζ => A ζ - B ζ := by
  have h := entrywiseEntire_add hC hA (entrywiseEntire_smul hC (-1) hB)
  have e : (fun ζ => A ζ - B ζ) = fun ζ => A ζ + (-1 : ℂ) • B ζ := by
    funext ζ
    rw [neg_one_smul, sub_eq_add_neg]
  rw [e]
  exact h
theorem entrywiseEntire_sum {α : Type} (hC : EntireDependenceClosed) (s : Finset α)
    {A : α → (F.Carrier → ℂ) → ComplexMatrix2} (hA : ∀ a ∈ s, EntrywiseEntire F S (A a)) :
    EntrywiseEntire F S fun ζ => ∑ a ∈ s, A a ζ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using entrywiseEntire_const (F := F) (S := S) hC 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact entrywiseEntire_add hC (hA a (Finset.mem_insert_self a s))
      (ih fun b hb => hA b (Finset.mem_insert_of_mem hb))
theorem isEntireOn_sum {α : Type} (hC : EntireDependenceClosed) (s : Finset α)
    {g : α → (F.Carrier → ℂ) → ℂ} (hg : ∀ a ∈ s, IsEntireOn F S (g a)) :
    IsEntireOn F S fun ζ => ∑ a ∈ s, g a ζ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (hC F S).1 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ((hC F S).2.2.1 _ _ (hg a (Finset.mem_insert_self a s))
      (ih fun b hb => hg b (Finset.mem_insert_of_mem hb))).1
theorem isEntireOn_fullTrace (hC : EntireDependenceClosed) {A : (F.Carrier → ℂ) → ComplexMatrix2}
    (hA : EntrywiseEntire F S A) : IsEntireOn F S fun ζ => ComplexMatrix2.fullTrace (A ζ) := by
  have := ((hC F S).2.2.1 _ _ (hA 0 0) (hA 1 1)).1
  simpa only [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using this
theorem entrywiseEntire_bracketSumOrdered (hC : EntireDependenceClosed)
    {Y Y' : (F.Carrier → ℂ) → Fin 4 → ComplexMatrix2}
    (hY : ∀ i, EntrywiseEntire F S fun ζ => Y ζ i) (hY' : ∀ i, EntrywiseEntire F S fun ζ => Y' ζ i) :
    EntrywiseEntire F S fun ζ => bracketSumOrdered (Y ζ) (Y' ζ) := by
  simp only [bracketSumOrdered]
  exact entrywiseEntire_sum hC _ fun i _ => entrywiseEntire_sum hC _ fun j _ =>
    entrywiseEntire_sub hC (entrywiseEntire_mul hC (hY i) (hY' j))
      (entrywiseEntire_mul hC (hY' j) (hY i))
theorem isEntireOn_faceTerm (hC : EntireDependenceClosed) (η : ℂ)
    {W : (F.Carrier → ℂ) → Fin 4 → ComplexMatrix2}
    (hR : ∀ i, EntrywiseEntire F S fun ζ => W ζ i) (hI : ∀ i, EntrywiseEntire F S fun ζ => (W ζ i)⁻¹)
    (X X' : Fin 4 → ComplexMatrix2) :
    IsEntireOn F S fun ζ => faceTerm η (W ζ) X X' := by
  have hT : ∀ i, EntrywiseEntire F S fun ζ => cornerTransports (W ζ) i := by
    intro i
    fin_cases i
    · exact entrywiseEntire_const hC 1
    · exact hR 0
    · exact entrywiseEntire_mul hC (entrywiseEntire_mul hC (hR 0) (hR 1)) (hI 2)
    · exact entrywiseEntire_mul hC
        (entrywiseEntire_mul hC (entrywiseEntire_mul hC (hR 0) (hR 1)) (hI 2)) (hI 3)
  have hTi : ∀ i, EntrywiseEntire F S fun ζ => cornerTransportsInv (W ζ) i := by
    intro i
    fin_cases i
    · exact entrywiseEntire_const hC 1
    · exact hI 0
    · exact entrywiseEntire_mul hC (entrywiseEntire_mul hC (hR 2) (hI 1)) (hI 0)
    · exact entrywiseEntire_mul hC
        (entrywiseEntire_mul hC (entrywiseEntire_mul hC (hR 3) (hR 2)) (hI 1)) (hI 0)
  have hV : ∀ (Z : Fin 4 → ComplexMatrix2) (i : Fin 4),
      EntrywiseEntire F S fun ζ => conjugatedValues (W ζ) Z i :=
    fun Z i => entrywiseEntire_smul hC _
      (entrywiseEntire_mul hC (entrywiseEntire_mul hC (hT i) (entrywiseEntire_const hC _)) (hTi i))
  have hS : EntrywiseEntire F S fun ζ => strengthMatrix η (W ζ) :=
    entrywiseEntire_smul hC _ (entrywiseEntire_sub hC (hT 3) (hTi 3))
  exact ((hC F S).2.2.1 _ _ ((hC F S).1 _)
    (isEntireOn_fullTrace hC (entrywiseEntire_mul hC
      (entrywiseEntire_bracketSumOrdered hC (hV X) (hV X')) hS))).2
end Entrywise
variable {L k : ℕ}
theorem coe_vertexImage_intShift (hL : Conventions.IsAdmissibleBlockingFactor L) (n : Fin 4 → ℤ)
    (x : Vertex L k 0) :
    ((vertexImage (PeriodicOperators.intShift n) x : Vertex L k 0) : InfiniteLattice.AmbientSpace) =
      x + castVec n := by apply _root_.YangMills.Construction.Tower.FinestFourierSums.coe_vertexImage_intShift <;> assumption
theorem vertexImage_intShift_sub (hL : Conventions.IsAdmissibleBlockingFactor L) (n : Fin 4 → ℤ)
    (x y : Vertex L k 0) :
    vertexImage (PeriodicOperators.intShift n) y - vertexImage (PeriodicOperators.intShift n) x =
      y - x :=
  Subtype.ext (by
    rw [AddSubgroup.coe_sub, AddSubgroup.coe_sub, coe_vertexImage_intShift hL,
      coe_vertexImage_intShift hL]
    abel)
theorem vertexImage_intShift_add_axisStep (hL : Conventions.IsAdmissibleBlockingFactor L)
    (n : Fin 4 → ℤ) (x : Vertex L k 0) (μ : Fin 4) :
    vertexImage (PeriodicOperators.intShift n) (x + InfiniteLattice.axisStep _ μ) =
      vertexImage (PeriodicOperators.intShift n) x + InfiniteLattice.axisStep _ μ :=
  Subtype.ext (by
    rw [AddSubgroup.coe_add, coe_vertexImage_intShift hL, coe_vertexImage_intShift hL,
      AddSubgroup.coe_add]
    abel)
theorem vertexImage_intShift_injective (hL : Conventions.IsAdmissibleBlockingFactor L)
    (n : Fin 4 → ℤ) :
    Function.Injective
      (vertexImage (PeriodicOperators.intShift n) : Vertex L k 0 → Vertex L k 0) := by
  intro x y h
  have := congrArg (fun z : Vertex L k 0 => (z : InfiniteLattice.AmbientSpace)) h
  simp only [coe_vertexImage_intShift hL] at this
  exact Subtype.ext (add_right_cancel this)
theorem edgeImage_intShift_spec (hL : Conventions.IsAdmissibleBlockingFactor L) (n : Fin 4 → ℤ)
    (b : Edge L k 0) :
    (FullSpace.edgeImage (PeriodicOperators.intShift n) b).initial =
        vertexImage (PeriodicOperators.intShift n) b.initial ∧
      (FullSpace.edgeImage (PeriodicOperators.intShift n) b).terminal =
        vertexImage (PeriodicOperators.intShift n) b.terminal :=
  Classical.epsilon_spec
    (p := fun b' : Edge L k 0 =>
      b'.initial = vertexImage (PeriodicOperators.intShift n) b.initial ∧
        b'.terminal = vertexImage (PeriodicOperators.intShift n) b.terminal)
    ⟨⟨vertexImage (PeriodicOperators.intShift n) b.initial,
      vertexImage (PeriodicOperators.intShift n) b.terminal, by
        rw [vertexImage_intShift_sub hL]
        exact b.isAdjacent⟩, rfl, rfl⟩
theorem edgeImage_intShift_forwardFrom (hL : Conventions.IsAdmissibleBlockingFactor L)
    (n : Fin 4 → ℤ) (x : Vertex L k 0) (μ : Fin 4) :
    FullSpace.edgeImage (PeriodicOperators.intShift n) (InfiniteLattice.Link.forwardFrom x μ) =
      InfiniteLattice.Link.forwardFrom (vertexImage (PeriodicOperators.intShift n) x) μ := by
  obtain ⟨h₁, h₂⟩ := edgeImage_intShift_spec hL n (InfiniteLattice.Link.forwardFrom x μ)
  refine InfiniteLattice.Link.ext h₁ (h₂.trans ?_)
  exact vertexImage_intShift_add_axisStep hL n x μ
theorem shiftEdge_val (hL : Conventions.IsAdmissibleBlockingFactor L) (n : Fin 4 → ℤ)
    (b : PeriodicOperators.PosEdge L k 0) :
    (shiftEdge n b).1 = FullSpace.edgeImage (PeriodicOperators.intShift n) b.1 := by
  refine Classical.epsilon_spec
    (p := fun b' : PeriodicOperators.PosEdge L k 0 =>
      b'.1 = FullSpace.edgeImage (PeriodicOperators.intShift n) b.1)
    ⟨⟨FullSpace.edgeImage (PeriodicOperators.intShift n) b.1, ?_⟩, rfl⟩
  obtain ⟨μ, hμ⟩ := b.2
  obtain ⟨h₁, h₂⟩ := edgeImage_intShift_spec hL n b.1
  exact ⟨μ, by rw [h₁, h₂, vertexImage_intShift_sub hL]; exact hμ⟩
theorem shiftEdge_injective (hL : Conventions.IsAdmissibleBlockingFactor L) (n : Fin 4 → ℤ) :
    Function.Injective
      (shiftEdge n : PeriodicOperators.PosEdge L k 0 → PeriodicOperators.PosEdge L k 0) := by
  intro b b' h
  have e := congrArg Subtype.val h
  rw [shiftEdge_val hL, shiftEdge_val hL] at e
  obtain ⟨h₁, h₂⟩ := edgeImage_intShift_spec hL n b.1
  obtain ⟨h₁', h₂'⟩ := edgeImage_intShift_spec hL n b'.1
  rw [e] at h₁ h₂
  exact Subtype.ext (InfiniteLattice.Link.ext
    (vertexImage_intShift_injective hL n (h₁.symm.trans h₁'))
    (vertexImage_intShift_injective hL n (h₂.symm.trans h₂')))
theorem shiftFace_bijective (hL : Conventions.IsAdmissibleBlockingFactor L) (n : Fin 4 → ℤ) :
    Function.Bijective (shiftFace n : Face L k 0 → Face L k 0) := by
  constructor
  · intro p q e
    have hb : vertexImage (PeriodicOperators.intShift n) p.corner =
        vertexImage (PeriodicOperators.intShift n) q.corner :=
      congrArg InfiniteLattice.ElementaryPlaquette.corner e
    have h1 : (shiftFace n p).lowAxis = (shiftFace n q).lowAxis :=
      congrArg InfiniteLattice.ElementaryPlaquette.lowAxis e
    have h2 : (shiftFace n p).highAxis = (shiftFace n q).highAxis :=
      congrArg InfiniteLattice.ElementaryPlaquette.highAxis e
    exact InfiniteLattice.ElementaryPlaquette.ext (vertexImage_intShift_injective hL n hb) h1 h2
  · intro p
    refine ⟨shiftFace (-n) p, InfiniteLattice.ElementaryPlaquette.ext ?_ rfl rfl⟩
    refine Subtype.ext ?_
    change ((vertexImage (PeriodicOperators.intShift n)
      (vertexImage (PeriodicOperators.intShift (-n)) p.corner) : Vertex L k 0) :
        InfiniteLattice.AmbientSpace) = p.corner
    rw [coe_vertexImage_intShift hL, coe_vertexImage_intShift hL]
    funext μ
    simp [castVec]
def edgeStart (p : Face L k 0) : Fin 4 → Vertex L k 0 :=
  ![p.corner, p.corner + InfiniteLattice.axisStep _ p.lowAxis,
    p.corner + InfiniteLattice.axisStep _ p.highAxis, p.corner]
def edgeAxis (p : Face L k 0) : Fin 4 → Fin 4 :=
  ![p.lowAxis, p.highAxis, p.lowAxis, p.highAxis]
theorem faceEdge_eq_forwardFrom (p : Face L k 0) (i : Fin 4) :
    faceEdge p i = InfiniteLattice.Link.forwardFrom (edgeStart p i) (edgeAxis p i) := by
  fin_cases i <;> rfl
def posEdgeOfFace (p : Face L k 0) (i : Fin 4) : PeriodicOperators.PosEdge L k 0 :=
  ⟨faceEdge p i, edgeAxis p i, by
    rw [faceEdge_eq_forwardFrom]
    simp [InfiniteLattice.Link.forwardFrom]⟩
theorem initial_posEdgeOfFace (p : Face L k 0) (i : Fin 4) :
    (posEdgeOfFace p i).1.initial = edgeStart p i := by
  change (faceEdge p i).initial = _
  rw [faceEdge_eq_forwardFrom]
  rfl
theorem faceEdge_shiftFace (hL : Conventions.IsAdmissibleBlockingFactor L) (n : Fin 4 → ℤ)
    (p : Face L k 0) (i : Fin 4) :
    faceEdge (shiftFace n p) i =
      FullSpace.edgeImage (PeriodicOperators.intShift n) (faceEdge p i) := by
  rw [faceEdge_eq_forwardFrom, faceEdge_eq_forwardFrom, edgeImage_intShift_forwardFrom hL]
  have hc : edgeStart (shiftFace n p) i =
      vertexImage (PeriodicOperators.intShift n) (edgeStart p i) := by
    fin_cases i
    · rfl
    · exact (vertexImage_intShift_add_axisStep hL n _ _).symm
    · exact (vertexImage_intShift_add_axisStep hL n _ _).symm
    · rfl
  have hd : edgeAxis (shiftFace n p) i = edgeAxis p i := by
    fin_cases i <;> rfl
  rw [hc, hd]
theorem posEdgeOfFace_shiftFace (hL : Conventions.IsAdmissibleBlockingFactor L) (n : Fin 4 → ℤ)
    (p : Face L k 0) (i : Fin 4) :
    posEdgeOfFace (shiftFace n p) i = shiftEdge n (posEdgeOfFace p i) :=
  Subtype.ext ((faceEdge_shiftFace hL n p i).trans (shiftEdge_val hL n (posEdgeOfFace p i)).symm)
theorem finestMesh_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < finestMesh L k := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.finestMesh_pos <;> assumption
theorem euclidNormVec_add_le (v w : Fin 4 → ℝ) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem euclidNormVec_edgeStart_sub_corner_le (hL : Conventions.IsAdmissibleBlockingFactor L)
    (p : Face L k 0) (i : Fin 4) :
    euclidNormVec ((edgeStart p i : InfiniteLattice.AmbientSpace) -
        (p.corner : InfiniteLattice.AmbientSpace)) ≤ finestMesh L k := by
  have hη : 0 < finestMesh L k := finestMesh_pos hL
  have h0 : euclidNormVec (0 : InfiniteLattice.AmbientSpace) = 0 := by simp [euclidNormVec]
  have hs : ∀ μ, euclidNormVec (((InfiniteLattice.axisStep (meshAt L k 0) μ : Vertex L k 0) :
      InfiniteLattice.AmbientSpace)) ≤ finestMesh L k := fun μ => by
    have : euclidNormVec (((InfiniteLattice.axisStep (meshAt L k 0) μ : Vertex L k 0) :
        InfiniteLattice.AmbientSpace)) = finestMesh L k := by
      change euclidNormVec (Pi.single μ (finestMesh L k)) = _
      rw [InfiniteLattice.euclidNormVec_single, abs_of_pos hη]
    exact this.le
  fin_cases i
  · simpa [edgeStart, h0] using hη.le
  · simpa [edgeStart] using hs _
  · simpa [edgeStart] using hs _
  · simpa [edgeStart, h0] using hη.le
theorem euclidNormVec_edgeStart_sub_le (hL : Conventions.IsAdmissibleBlockingFactor L)
    (p : Face L k 0) (i j : Fin 4) :
    euclidNormVec ((edgeStart p i : InfiniteLattice.AmbientSpace) -
        (edgeStart p j : InfiniteLattice.AmbientSpace)) ≤ 2 * finestMesh L k := by
  have e : (edgeStart p i : InfiniteLattice.AmbientSpace) -
      (edgeStart p j : InfiniteLattice.AmbientSpace) =
      ((edgeStart p i : InfiniteLattice.AmbientSpace) - (p.corner : InfiniteLattice.AmbientSpace)) +
        -((edgeStart p j : InfiniteLattice.AmbientSpace) -
          (p.corner : InfiniteLattice.AmbientSpace)) := by
    abel
  rw [e]
  refine (euclidNormVec_add_le _ _).trans ?_
  rw [euclidNormVec_neg]
  linarith [euclidNormVec_edgeStart_sub_corner_le hL p i,
    euclidNormVec_edgeStart_sub_corner_le hL p j]
def LiesOn (c : PeriodicOperators.PosEdge L k 0) (p : Face L k 0) : Prop :=
  ∃ i, posEdgeOfFace p i = c
theorem euclidNormVec_initial_sub_le (hL : Conventions.IsAdmissibleBlockingFactor L)
    {c c' : PeriodicOperators.PosEdge L k 0} {p : Face L k 0} (h : LiesOn c p) (h' : LiesOn c' p) :
    euclidNormVec ((c'.1.initial : InfiniteLattice.AmbientSpace) -
        (c.1.initial : InfiniteLattice.AmbientSpace)) ≤ 2 * finestMesh L k := by
  obtain ⟨i, rfl⟩ := h
  obtain ⟨j, rfl⟩ := h'
  rw [initial_posEdgeOfFace, initial_posEdgeOfFace]
  exact euclidNormVec_edgeStart_sub_le hL p j i
theorem finite_setOf_liesOn (hP : Tower.FacesContainingEdge.Holds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (c : PeriodicOperators.PosEdge L k 0) :
    {p : Face L k 0 | LiesOn c p}.Finite := by
  refine ((hP L hL k 0 (Nat.zero_le k)).2.2.2 {c} (Set.finite_singleton c)).subset ?_
  rintro p ⟨i, rfl⟩
  refine ⟨posEdgeOfFace p i, rfl, ?_⟩
  change faceEdge p i ∈ faceEdges p
  exact List.getElem_mem _
def facesOfEdge (hP : Tower.FacesContainingEdge.Holds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (c : PeriodicOperators.PosEdge L k 0) :
    Finset (Face L k 0) :=
  (finite_setOf_liesOn hP hL c).toFinset
def linkMatrices (U : Edge L k 0 → ComplexMatrix2) (p : Face L k 0) : Fin 4 → ComplexMatrix2 :=
  fun i => U (faceEdge p i)
def formValues (b : Edge L k 0 → ComplexMatrix2) (p : Face L k 0) : Fin 4 → ComplexMatrix2 :=
  fun i => b (faceEdge p i)
theorem faceTransports_eq {U : Edge L k 0 → ComplexMatrix2}
    (hU : ∀ b : Edge L k 0, U b.opposite = (U b)⁻¹) (p : Face L k 0) :
    faceTransports U p = cornerTransports (linkMatrices U p) := by
  funext i
  fin_cases i <;>
    simp [cornerTransports, linkMatrices, faceTransports, faceVariable, linkHolonomy, faceBoundary,
      faceEdge, faceEdges, hU, mul_assoc]
def faceContribution (U b b' : Edge L k 0 → ComplexMatrix2) (p : Face L k 0) : ℂ :=
  (Complex.I / 2) * ComplexMatrix2.fullTrace
    (bracketSumOrdered (transportedForm U b p) (transportedForm U b' p) * curvatureMatrix U p)
theorem faceContribution_eq {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (b b' : Edge L k 0 → ComplexMatrix2) (p : Face L k 0) :
    faceContribution U b b' p =
      faceTerm (finestMesh L k) (linkMatrices U p) (formValues b p) (formValues b' p) := by
  have hdet : ∀ i, (linkMatrices U p i).det = 1 := fun i => hU.1 _
  have hT := faceTransports_eq hU.2 p
  have hV : ∀ c : Edge L k 0 → ComplexMatrix2, transportedForm U c p =
      conjugatedValues (linkMatrices U p) (formValues c p) := fun c => by
    funext i
    simp only [transportedForm, conjugatedValues, hT, ComplexMatrix2.conjugateBy,
      inv_cornerTransports hdet, formValues]
  have h3 : faceVariable U p = cornerTransports (linkMatrices U p) 3 := congrFun hT 3
  have hS : curvatureMatrix U p = strengthMatrix (finestMesh L k) (linkMatrices U p) := by
    rw [curvatureMatrix, strengthMatrix, h3, inv_cornerTransports hdet]
  rw [faceContribution, faceTerm, hV, hV, hS]
theorem bracketSumOrdered_zero_left (Y : Fin 4 → ComplexMatrix2) : bracketSumOrdered 0 Y = 0 := by
  simp [bracketSumOrdered]
theorem bracketSumOrdered_zero_right (Y : Fin 4 → ComplexMatrix2) : bracketSumOrdered Y 0 = 0 := by
  simp [bracketSumOrdered]
theorem transportedForm_eq_zero (U b : Edge L k 0 → ComplexMatrix2) (p : Face L k 0)
    (h : ∀ i, b (faceEdge p i) = 0) : transportedForm U b p = 0 := by
  funext i
  simp [transportedForm, h, ComplexMatrix2.conjugateBy]
theorem faceContribution_eq_zero_left (U b b' : Edge L k 0 → ComplexMatrix2) (p : Face L k 0)
    (h : ∀ i, b (faceEdge p i) = 0) : faceContribution U b b' p = 0 := by
  simp [faceContribution, transportedForm_eq_zero U b p h, bracketSumOrdered_zero_left,
    ComplexMatrix2.fullTrace]
theorem faceContribution_eq_zero_right (U b b' : Edge L k 0 → ComplexMatrix2) (p : Face L k 0)
    (h : ∀ i, b' (faceEdge p i) = 0) : faceContribution U b b' p = 0 := by
  simp [faceContribution, transportedForm_eq_zero U b' p h, bracketSumOrdered_zero_right,
    ComplexMatrix2.fullTrace]
open Classical in
theorem basisForm_faceEdge (a : Fin 3) (c : PeriodicOperators.PosEdge L k 0)
    (p : Face L k 0) (i : Fin 4) :
    basisForm a c (faceEdge p i) =
      if posEdgeOfFace p i = c then ComplexMatrix2.pauliFamily a else 0 := by
  have hpos : (faceEdge p i).IsPositivelyOriented := (posEdgeOfFace p i).2
  simp only [basisForm, extendOddly, if_pos hpos]
  by_cases h : posEdgeOfFace p i = c
  · rw [if_pos h]
    exact if_pos (congrArg Subtype.val h)
  · rw [if_neg h]
    exact if_neg fun e => h (Subtype.ext e)
theorem basisForm_faceEdge_of_not_liesOn (a : Fin 3) {c : PeriodicOperators.PosEdge L k 0}
    {p : Face L k 0} (h : ¬ LiesOn c p) (i : Fin 4) :
    basisForm a c (faceEdge p i) = 0 := by
  classical
  rw [basisForm_faceEdge, if_neg fun e => h ⟨i, e⟩]
theorem curvatureBilinear_basisForm_eq_sum (U : Edge L k 0 → ComplexMatrix2) (a a' : Fin 3)
    (c c' : PeriodicOperators.PosEdge L k 0) (Ω : Finset (Face L k 0))
    (hΩ : ∀ p, LiesOn c p → LiesOn c' p → p ∈ Ω) :
    curvatureBilinear U (basisForm a c) (basisForm a' c') =
      ((finestMesh L k : ℂ) ^ 4) *
        ∑ p ∈ Ω, faceContribution U (basisForm a c) (basisForm a' c') p := by
  rw [curvatureBilinear]
  congr 1
  refine finsum_eq_sum_of_support_subset
    (fun p => faceContribution U (basisForm a c) (basisForm a' c') p) ?_
  intro p hp
  by_contra hne
  apply hp
  by_cases h : LiesOn c p
  · by_cases h' : LiesOn c' p
    · exact absurd (hΩ p h h') hne
    · exact faceContribution_eq_zero_right _ _ _ _ fun i => basisForm_faceEdge_of_not_liesOn a' h' i
  · exact faceContribution_eq_zero_left _ _ _ _ fun i => basisForm_faceEdge_of_not_liesOn a h i
theorem curvatureKernel_eq_sum (hK : CurvatureKernelEntries)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (U : Edge L k 0 → ComplexMatrix2)
    (a a' : Fin 3) (c c' : PeriodicOperators.PosEdge L k 0) (Ω : Finset (Face L k 0))
    (hΩ : ∀ p, LiesOn c p → LiesOn c' p → p ∈ Ω) :
    curvatureKernel U (a, c) (a', c') =
      (1 / 2 : ℂ) * (∑ p ∈ Ω, faceContribution U (basisForm a c) (basisForm a' c') p +
        ∑ p ∈ Ω, faceContribution U (basisForm a' c') (basisForm a c) p) := by
  have hη : ((finestMesh L k : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (finestMesh_pos (k := k) hL).ne'
  have h := hK L hL k hk U (a, c) (a', c')
  simp only at h
  rw [h, curvatureBilinear_basisForm_eq_sum U a a' c c' Ω hΩ,
    curvatureBilinear_basisForm_eq_sum U a' a c' c Ω fun p h h' => hΩ p h' h]
  push_cast
  field_simp
theorem curvatureBilinear_shift (hL : Conventions.IsAdmissibleBlockingFactor L) (n : Fin 4 → ℤ)
    {U U' : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (hU' : U' ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (hT : ∀ b, U' (FullSpace.edgeImage (PeriodicOperators.intShift n) b) = U b) (a a' : Fin 3)
    (c c' : PeriodicOperators.PosEdge L k 0) :
    curvatureBilinear U' (basisForm a (shiftEdge n c)) (basisForm a' (shiftEdge n c')) =
      curvatureBilinear U (basisForm a c) (basisForm a' c') := by
  classical
  have hW : ∀ p, linkMatrices U' (shiftFace n p) = linkMatrices U p := fun p => by
    funext i
    simp only [linkMatrices]
    rw [faceEdge_shiftFace hL]
    exact hT _
  have hX : ∀ (e : Fin 3) (d : PeriodicOperators.PosEdge L k 0) p,
      formValues (basisForm e (shiftEdge n d)) (shiftFace n p) =
        formValues (basisForm e d) p := fun e d p => by
    funext i
    simp only [formValues]
    rw [basisForm_faceEdge, basisForm_faceEdge, posEdgeOfFace_shiftFace hL]
    by_cases h : posEdgeOfFace p i = d
    · rw [if_pos (congrArg (shiftEdge n) h), if_pos h]
    · rw [if_neg fun e' => h (shiftEdge_injective hL n e'), if_neg h]
  have hterm : ∀ p, faceContribution U' (basisForm a (shiftEdge n c))
      (basisForm a' (shiftEdge n c')) (shiftFace n p) =
        faceContribution U (basisForm a c) (basisForm a' c') p := fun p => by
    rw [faceContribution_eq hU', faceContribution_eq hU, hW, hX, hX]
  have hs : ∑ᶠ p, faceContribution U' (basisForm a (shiftEdge n c))
      (basisForm a' (shiftEdge n c')) p =
        ∑ᶠ p, faceContribution U (basisForm a c) (basisForm a' c') p :=
    (finsum_comp (g := fun q => faceContribution U' (basisForm a (shiftEdge n c))
      (basisForm a' (shiftEdge n c')) q) (shiftFace n)
      (shiftFace_bijective hL n)).symm.trans (finsum_congr hterm)
  change ((finestMesh L k : ℂ) ^ 4) * ∑ᶠ p, faceContribution U' _ _ p =
    ((finestMesh L k : ℂ) ^ 4) * ∑ᶠ p, faceContribution U _ _ p
  rw [hs]
theorem curvatureKernelIsLocal_of (hCrit : EntireLocalCriterion.Criterion)
    (hEnt : GaugeFieldOfFormEntries)
    (hTr : ShiftedFieldGauge.ShiftCommutes)
    (hK : CurvatureKernelEntries)
    (hC : EntireDependenceClosed)
    (hP : Tower.FacesContainingEdge.Holds) : CurvatureKernelIsLocal := by
  classical
  intro L hL k hk
  have hcfg := (hEnt L hL k).1
  refine hCrit L hL k (colourEdges L k 0) (colourEdges L k 0) _ ?_ ?_ ?_ ?_
  · intro ι'
    exact ⟨ι', rfl⟩
  · rintro ζ ⟨a', c'⟩ ⟨a, c⟩ hfar
    change curvatureKernel (gaugeFieldOfForm L k ζ) (a', c') (a, c) = 0
    rw [curvatureKernel_eq_sum hK hL hk _ a' a c' c ∅
      fun p h h' => absurd (euclidNormVec_initial_sub_le hL h h') hfar]
    simp
  · rintro ⟨a', c'⟩ ⟨a, c⟩
    set Ω : Finset (Face L k 0) :=
      facesOfEdge hP hL c' ∩ facesOfEdge hP hL c with hΩdef
    have hΩ : ∀ p, LiesOn c' p → LiesOn c p → p ∈ Ω := fun p h h' =>
      Finset.mem_inter.2 ⟨(finite_setOf_liesOn hP hL c').mem_toFinset.2 h,
        (finite_setOf_liesOn hP hL c).mem_toFinset.2 h'⟩
    have hΩ' : ∀ p ∈ Ω, LiesOn c' p := fun p hp =>
      (finite_setOf_liesOn hP hL c').mem_toFinset.1 (Finset.mem_inter.1 hp).1
    let idx : Face L k 0 → Finset (remainderIndex L k).Carrier := fun p =>
      Finset.univ.biUnion fun i => edgeIndices L k (posEdgeOfFace p i)
    refine ⟨Ω.biUnion idx, ?_, ?_⟩
    · intro κ hκ
      obtain ⟨p, hp, hi⟩ := Finset.mem_biUnion.1 hκ
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hi
      obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hi
      exact euclidNormVec_initial_sub_le hL (hΩ' p hp) ⟨i, rfl⟩
    · have hsub : ∀ p ∈ Ω, ∀ i, edgeIndices L k (posEdgeOfFace p i) ⊆ Ω.biUnion idx :=
        fun p hp i =>
          (Finset.subset_biUnion_of_mem (fun i => edgeIndices L k (posEdgeOfFace p i))
            (Finset.mem_univ i)).trans (Finset.subset_biUnion_of_mem idx hp)
      have hterm : ∀ X X' : Face L k 0 → Fin 4 → ComplexMatrix2, ∀ p ∈ Ω,
          IsEntireOn (remainderIndex L k) (Ω.biUnion idx) fun ζ =>
            faceTerm (finestMesh L k) (linkMatrices (gaugeFieldOfForm L k ζ) p) (X p) (X' p) :=
        fun X X' p hp => isEntireOn_faceTerm hC _
          (W := fun ζ => linkMatrices (gaugeFieldOfForm L k ζ) p)
          (fun i r s => (hC _ _).2.2.2 _ _ (hsub p hp i) ((hEnt L hL k).2 (posEdgeOfFace p i) r s).1)
          (fun i r s => (hC _ _).2.2.2 _ _ (hsub p hp i) ((hEnt L hL k).2 (posEdgeOfFace p i) r s).2)
          (X p) (X' p)
      have e : (fun ζ => curvatureKernel (gaugeFieldOfForm L k ζ) (a', c') (a, c)) =
          fun ζ => (1 / 2 : ℂ) *
            (∑ p ∈ Ω, faceTerm (finestMesh L k) (linkMatrices (gaugeFieldOfForm L k ζ) p)
                (formValues (basisForm a' c') p) (formValues (basisForm a c) p) +
              ∑ p ∈ Ω, faceTerm (finestMesh L k) (linkMatrices (gaugeFieldOfForm L k ζ) p)
                (formValues (basisForm a c) p) (formValues (basisForm a' c') p)) := by
        funext ζ
        rw [curvatureKernel_eq_sum hK hL hk _ a' a c' c Ω hΩ]
        simp only [faceContribution_eq (hcfg ζ)]
      change IsEntireOn _ _ fun ζ =>
        curvatureKernel (gaugeFieldOfForm L k ζ) (a', c') (a, c)
      rw [e]
      have hop := (hC (remainderIndex L k) (Ω.biUnion idx)).2.2.1
      exact (hop _ _ ((hC _ _).1 _) (hop _ _
        (isEntireOn_sum hC Ω (hterm _ _)) (isEntireOn_sum hC Ω (hterm _ _))).1).2
  · rintro ζ n ⟨a', c'⟩ ⟨a, c⟩
    change curvatureKernel (gaugeFieldOfForm L k
        (shiftField (remainderIndex L k) n ζ)) (a', shiftEdge n c')
        (a, shiftEdge n c) =
      curvatureKernel (gaugeFieldOfForm L k ζ) (a', c') (a, c)
    have hT := hTr L hL k n ζ
    have h1 := hK L hL k hk (gaugeFieldOfForm L k
      (shiftField (remainderIndex L k) n ζ)) (a', shiftEdge n c')
      (a, shiftEdge n c)
    have h2 := hK L hL k hk (gaugeFieldOfForm L k ζ) (a', c') (a, c)
    simp only at h1 h2
    rw [h1, h2, curvatureBilinear_shift hL n (hcfg ζ) (hcfg _) hT,
      curvatureBilinear_shift hL n (hcfg ζ) (hcfg _) hT]
end YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality
end
