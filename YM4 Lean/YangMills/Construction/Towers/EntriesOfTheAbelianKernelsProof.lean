import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.AbelianOperatorsAreLocalAndSelfAdjointProof
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotionsProof
import YangMills.Construction.Towers.KernelsOfTheTwoOperatorsAreProductsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.AbelianKernelEntries
open Matrices
open AbelianFieldFacts UnitLatticeL2
open PeriodicOperators (Represents RowFinite KernelMatrix ApplySummable ApplySummableAt
  applyKernel compKernel swapKernel ColumnFinite PeriodicData shiftEdge colourVertices
  colourEdges intShift castVec)
open CovDiffTransposes (LatticeTransposeData matrixKernel transposeComp compTranspose)
section FourierModes
variable {E : Type}
theorem fourierMode_add [Finite E] (n m : E → ℤ) (φ : E → ℝ) :
    fourierMode (n + m) φ = fourierMode n φ * fourierMode m φ := by
  have : Fintype E := Fintype.ofFinite E
  unfold fourierMode
  rw [← Complex.exp_add, ← mul_add, ← Complex.ofReal_add]
  congr 3
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp [add_mul]
theorem fourierMode_zero (φ : E → ℝ) : fourierMode (0 : E → ℤ) φ = 1 := by
  simp [fourierMode]
theorem fourierMode_single [Finite E] [DecidableEq E] (β : E) (s : ℤ) (φ : E → ℝ) :
    fourierMode (Pi.single β s) φ = Complex.exp (Complex.I * (((s : ℝ) * φ β : ℝ) : ℂ)) := by
  have : Fintype E := Fintype.ofFinite E
  unfold fourierMode
  rw [finsum_eq_sum_of_fintype, Finset.sum_eq_single β]
  · simp
  · intro γ _ h
    simp [Pi.single_eq_of_ne h]
  · simp
def trigSpan (E : Type) : Submodule ℂ ((E → ℝ) → ℂ) :=
  Submodule.span ℂ (range (fourierMode (E := E)))
theorem mul_mem_trigSpan [Finite E] {P Q : (E → ℝ) → ℂ} (hP : P ∈ trigSpan E)
    (hQ : Q ∈ trigSpan E) : P * Q ∈ trigSpan E := by
  unfold trigSpan at hP hQ ⊢
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    induction hQ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      refine Submodule.subset_span ⟨n + m, ?_⟩
      funext φ
      exact fourierMode_add n m φ
    | zero => simp
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx
theorem hasFourierCoeffs_of_mem_trigSpan {P : (E → ℝ) → ℂ} (hP : P ∈ trigSpan E) :
    ∃ γ, HasFourierCoeffs P γ := by
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hP
  refine ⟨c, c.hasFiniteSupport, fun φ => ?_⟩
  rw [finsum_eq_sum_of_support_subset (s := c.support)]
  · simp [Finsupp.sum, Finset.sum_apply]
  · intro n hn
    simp only [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    exact hn (by simp [h0])
end FourierModes
section Dependence
variable {B : Type}
def DependsOn (S : Set B) (F : (B → ℝ) → ℂ) : Prop :=
  ∃ P ∈ trigSpan S, ∀ θ, F θ = P fun b => θ b
variable {S : Set B}
theorem DependsOn.congr {F G : (B → ℝ) → ℂ} (h : ∀ θ, F θ = G θ) (hG : DependsOn S G) :
    DependsOn S F := by
  rwa [funext h]
theorem DependsOn.const (c : ℂ) : DependsOn S fun _ => c := by
  refine ⟨c • fourierMode 0, Submodule.smul_mem _ c (Submodule.subset_span ⟨0, rfl⟩), fun θ => ?_⟩
  simp [fourierMode_zero]
theorem DependsOn.add {F G : (B → ℝ) → ℂ} (hF : DependsOn S F) (hG : DependsOn S G) :
    DependsOn S fun θ => F θ + G θ := by
  obtain ⟨P, hP, eP⟩ := hF
  obtain ⟨Q, hQ, eQ⟩ := hG
  exact ⟨P + Q, Submodule.add_mem _ hP hQ, fun θ => by simp [eP, eQ]⟩
theorem DependsOn.mul [Finite S] {F G : (B → ℝ) → ℂ} (hF : DependsOn S F) (hG : DependsOn S G) :
    DependsOn S fun θ => F θ * G θ := by
  obtain ⟨P, hP, eP⟩ := hF
  obtain ⟨Q, hQ, eQ⟩ := hG
  exact ⟨P * Q, mul_mem_trigSpan hP hQ, fun θ => by simp [eP, eQ]⟩
theorem DependsOn.smul (c : ℂ) {F : (B → ℝ) → ℂ} (hF : DependsOn S F) :
    DependsOn S fun θ => c * F θ := by
  obtain ⟨P, hP, eP⟩ := hF
  exact ⟨c • P, Submodule.smul_mem _ c hP, fun θ => by simp [eP]⟩
theorem DependsOn.neg {F : (B → ℝ) → ℂ} (hF : DependsOn S F) : DependsOn S fun θ => -F θ := by
  simpa using hF.smul (-1)
theorem DependsOn.sub {F G : (B → ℝ) → ℂ} (hF : DependsOn S F) (hG : DependsOn S G) :
    DependsOn S fun θ => F θ - G θ := by
  simpa [sub_eq_add_neg] using hF.add hG.neg
theorem DependsOn.sum {α : Type} (s : Finset α) {F : α → (B → ℝ) → ℂ}
    (hF : ∀ i ∈ s, DependsOn S (F i)) : DependsOn S fun θ => ∑ i ∈ s, F i θ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using DependsOn.const (S := S) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))
theorem DependsOn.exp [Finite S] {b : B} (hb : b ∈ S) (s : ℤ) :
    DependsOn S fun θ => Complex.exp (Complex.I * (((s : ℝ) * θ b : ℝ) : ℂ)) := by
  classical
  refine ⟨fourierMode (Pi.single (⟨b, hb⟩ : S) s), Submodule.subset_span ⟨_, rfl⟩, fun θ => ?_⟩
  exact (fourierMode_single (⟨b, hb⟩ : S) s fun b => θ b).symm
end Dependence
section MatrixDependence
variable {B : Type} {S : Set B}
def MatDependsOn (S : Set B) (M : (B → ℝ) → ComplexMatrix2) : Prop :=
  ∀ i j, DependsOn S fun θ => M θ i j
theorem MatDependsOn.const (X : ComplexMatrix2) : MatDependsOn S fun _ => X :=
  fun _ _ => DependsOn.const _
theorem MatDependsOn.sub {M N : (B → ℝ) → ComplexMatrix2} (hM : MatDependsOn S M)
    (hN : MatDependsOn S N) : MatDependsOn S fun θ => M θ - N θ :=
  fun i j => (hM i j).sub (hN i j)
theorem MatDependsOn.smul (c : ℂ) {M : (B → ℝ) → ComplexMatrix2} (hM : MatDependsOn S M) :
    MatDependsOn S fun θ => c • M θ := fun i j => (hM i j).smul c
theorem MatDependsOn.mul [Finite S] {M N : (B → ℝ) → ComplexMatrix2} (hM : MatDependsOn S M)
    (hN : MatDependsOn S N) : MatDependsOn S fun θ => M θ * N θ := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hM i 0).mul (hN 0 j)).add ((hM i 1).mul (hN 1 j))
theorem MatDependsOn.sum {α : Type} (s : Finset α) {M : α → (B → ℝ) → ComplexMatrix2}
    (hM : ∀ i ∈ s, MatDependsOn S (M i)) : MatDependsOn S fun θ => ∑ i ∈ s, M i θ := by
  intro i j
  simp only [Matrix.sum_apply]
  exact DependsOn.sum s fun k hk => hM k hk i j
theorem MatDependsOn.trace {M : (B → ℝ) → ComplexMatrix2} (hM : MatDependsOn S M) :
    DependsOn S fun θ => ComplexMatrix2.fullTrace (M θ) := by
  simp only [ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
  exact (hM 0 0).add (hM 1 1)
def phaseMatrix (φ : ℝ) : ComplexMatrix2 :=
  Matrix.diagonal ![Complex.exp (Complex.I * φ), Complex.exp (-(Complex.I * φ))]
theorem matExp_pauliZ_eq_phaseMatrix (φ : ℝ) :
    ComplexMatrix2.matExp (Complex.I • ((φ : ℂ) • ComplexMatrix2.pauliFamily 2)) =
      phaseMatrix φ := by
  have h : Complex.I • ((φ : ℂ) • ComplexMatrix2.pauliFamily 2) =
      Matrix.diagonal ![Complex.I * φ, -(Complex.I * φ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ComplexMatrix2.pauliFamily, OneLoop.pauliZ]
  rw [h, ComplexMatrix2.matExp, Matrix.exp_diagonal, phaseMatrix]
  congr 1
  ext i
  fin_cases i <;> simp [Complex.exp_eq_exp_ℂ, Pi.coe_exp]
theorem phaseMatrix_mul_neg (φ : ℝ) : phaseMatrix φ * phaseMatrix (-φ) = 1 := by
  rw [phaseMatrix, phaseMatrix, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp [← Complex.exp_add]
theorem phaseMatrix_inv (φ : ℝ) : (phaseMatrix φ)⁻¹ = phaseMatrix (-φ) :=
  Matrix.inv_eq_right_inv (phaseMatrix_mul_neg φ)
theorem phaseMatrix_neg_mul (φ : ℝ) : phaseMatrix (-φ) * phaseMatrix φ = 1 := by
  simpa using phaseMatrix_mul_neg (-φ)
theorem matDependsOn_phaseMatrix [Finite S] {b : B} (hb : b ∈ S) (s : ℤ) :
    MatDependsOn S fun θ => phaseMatrix ((s : ℝ) * θ b) := by
  intro i j
  fin_cases i <;> fin_cases j
  · have h := DependsOn.exp (S := S) hb s
    simpa [phaseMatrix] using h
  · simpa [phaseMatrix] using DependsOn.const (S := S) (0 : ℂ)
  · simpa [phaseMatrix] using DependsOn.const (S := S) (0 : ℂ)
  · have h := DependsOn.exp (S := S) hb (-s)
    simpa [phaseMatrix] using h
def InvDependsOn (S : Set B) (M : (B → ℝ) → ComplexMatrix2) : Prop :=
  MatDependsOn S M ∧ MatDependsOn S fun θ => (M θ)⁻¹
theorem InvDependsOn.one : InvDependsOn S fun _ => 1 :=
  ⟨MatDependsOn.const 1, by simpa using MatDependsOn.const (S := S) (1 : ComplexMatrix2)⟩
theorem InvDependsOn.mul [Finite S] {M N : (B → ℝ) → ComplexMatrix2} (hM : InvDependsOn S M)
    (hN : InvDependsOn S N) : InvDependsOn S fun θ => M θ * N θ := by
  refine ⟨hM.1.mul hN.1, ?_⟩
  simp only [Matrix.mul_inv_rev]
  exact hN.2.mul hM.2
theorem invDependsOn_phaseMatrix [Finite S] {b : B} (hb : b ∈ S) (s : ℤ) :
    InvDependsOn S fun θ => phaseMatrix ((s : ℝ) * θ b) := by
  refine ⟨matDependsOn_phaseMatrix hb s, ?_⟩
  have h := matDependsOn_phaseMatrix hb (-s)
  simpa [phaseMatrix_inv] using h
end MatrixDependence
section PauliCoefficients
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliCoeff_of_mem_traceless (a : Fin 3) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a X =
      (![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] : Fin 3 → ℂ) a := by
  unfold pauliCoeff
  rw [dif_pos hX]
  rfl
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem pauliCoeff_add (a : Fin 3) {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p106 <;> assumption
theorem ofPauliCoeffs_mem_traceless {σ : Type} (c : Fin 3 × σ → ℂ) (i : σ) :
    ofPauliCoeffs c i ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
theorem dependsOn_pauliCoeff {B : Type} {S : Set B} {M : (B → ℝ) → ComplexMatrix2}
    (hM : MatDependsOn S M) (hs : ∀ θ, M θ ∈ ComplexMatrix2.traceless) (c : Fin 3) :
    DependsOn S fun θ => pauliCoeff c (M θ) := by
  simp only [pauliCoeff_of_mem_traceless c (hs _)]
  fin_cases c
  · simpa [div_eq_inv_mul] using ((hM 0 1).add (hM 1 0)).smul (2⁻¹ : ℂ)
  · simpa [div_eq_inv_mul] using ((hM 1 0).sub (hM 0 1)).smul ((2 * Complex.I)⁻¹ : ℂ)
  · exact hM 0 0
theorem ofPauliCoeffs_indicator {σ : Type} (a : Fin 3) (x y : σ)
    {dec : ∀ κ : Fin 3 × σ, Decidable (κ = (a, x))} {dec' : Decidable (y = x)} :
    ofPauliCoeffs (fun κ : Fin 3 × σ => @ite _ (κ = (a, x)) (dec κ) (1 : ℂ) 0) y =
      @ite _ (y = x) dec' (ComplexMatrix2.pauliFamily a) 0 := by
  unfold ofPauliCoeffs
  by_cases h : y = x
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single a]
    · simp
    · intro c _ hc
      dsimp only
      rw [if_neg fun e => hc (congrArg Prod.fst e), zero_smul]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun c _ => ?_
    dsimp only
    rw [if_neg fun e => h (congrArg Prod.snd e), zero_smul]
end PauliCoefficients
section UnitLattice
variable {L : ℕ}
theorem meshAt_zero_zero (L : ℕ) : meshAt L 0 0 = 1 := by
  simp [meshAt]
theorem meshAt_zero_zero_pos (L : ℕ) : 0 < meshAt L 0 0 := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.meshAt_zero_pos <;> assumption
theorem euclidNormVec_axisStep (μ : Fin 4) :
    TorusMetric.euclidNormVec
      ((InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) :
        InfiniteLattice.AmbientSpace) = 1 := by apply _root_.YangMills.Construction.Tower.AbelianOperatorsLocalSelfAdjointProof.euclidNormVec_axisStep <;> assumption
theorem euclidNormVec_sub_le (v w : InfiniteLattice.AmbientSpace) :
    TorusMetric.euclidNormVec (v - w) ≤
      TorusMetric.euclidNormVec v + TorusMetric.euclidNormVec w := by apply _root_.YangMills.Construction.Tower.OrthogonalMotions.euclidNormVec_sub_le <;> assumption
theorem euclidNormVec_neg (v : InfiniteLattice.AmbientSpace) :
    TorusMetric.euclidNormVec (-v) = TorusMetric.euclidNormVec v := by
  simp [TorusMetric.euclidNormVec]
theorem euclidNormVec_zero :
    TorusMetric.euclidNormVec (0 : InfiniteLattice.AmbientSpace) = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
def translateEdge (v : FullSpace.Vertex L 0 0) (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.PositiveEdge (meshAt L 0 0) :=
  ⟨⟨b.1.initial + v, b.1.terminal + v, b.1.isAdjacent.imp fun μ h => h.imp
      (fun e => by rw [add_sub_add_right_eq_sub]; exact e)
      (fun e => by rw [add_sub_add_right_eq_sub]; exact e)⟩,
    b.2.imp fun μ e => by
      show b.1.terminal + v - (b.1.initial + v) = _
      rw [add_sub_add_right_eq_sub]; exact e⟩
theorem translateEdge_translateEdge (v w : FullSpace.Vertex L 0 0)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    translateEdge w (translateEdge v b) = translateEdge (v + w) b := by
  refine Subtype.ext (InfiniteLattice.Link.ext ?_ ?_)
  · exact add_assoc _ _ _
  · exact add_assoc _ _ _
theorem translateEdge_zero (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    translateEdge (0 : FullSpace.Vertex L 0 0) b = b := by
  refine Subtype.ext (InfiniteLattice.Link.ext ?_ ?_)
  · exact add_zero _
  · exact add_zero _
def translateEdgeEquiv (v : FullSpace.Vertex L 0 0) :
    FullSpace.PositiveEdge (meshAt L 0 0) ≃ FullSpace.PositiveEdge (meshAt L 0 0) where
  toFun := translateEdge v
  invFun := translateEdge (-v)
  left_inv b := by rw [translateEdge_translateEdge, add_neg_cancel, translateEdge_zero]
  right_inv b := by rw [translateEdge_translateEdge, neg_add_cancel, translateEdge_zero]
def translateFace (v : FullSpace.Vertex L 0 0) (p : FullSpace.Face L 0 0) :
    FullSpace.Face L 0 0 :=
  ⟨p.corner + v, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
def translateFaceEquiv (v : FullSpace.Vertex L 0 0) :
    FullSpace.Face L 0 0 ≃ FullSpace.Face L 0 0 where
  toFun := translateFace v
  invFun := translateFace (-v)
  left_inv p := by
    refine InfiniteLattice.ElementaryPlaquette.ext ?_ rfl rfl
    exact add_neg_cancel_right _ _
  right_inv p := by
    refine InfiniteLattice.ElementaryPlaquette.ext ?_ rfl rfl
    exact neg_add_cancel_right _ _
def vertexOfInt (L : ℕ) (n : Fin 4 → ℤ) : FullSpace.Vertex L 0 0 :=
  ⟨castVec n, n, fun μ => by simp [castVec, meshAt_zero_zero]⟩
theorem vertexImage_intShift (n : Fin 4 → ℤ) (x : FullSpace.Vertex L 0 0) :
    FullSpace.vertexImage (intShift n) x = x + vertexOfInt L n := by
  have h : ∃ x' : FullSpace.Vertex L 0 0, (x' : InfiniteLattice.AmbientSpace) =
      intShift n (x : InfiniteLattice.AmbientSpace) := ⟨x + vertexOfInt L n, rfl⟩
  have hs := Classical.epsilon_spec h
  exact Subtype.ext hs
theorem shiftEdge_eq_translateEdge (n : Fin 4 → ℤ) (b : PeriodicOperators.PosEdge L 0 0) :
    shiftEdge n b = translateEdge (vertexOfInt L n) b := by
  have hm : ∃ b' : FullSpace.Edge L 0 0,
      b'.initial = FullSpace.vertexImage (intShift n) b.1.initial ∧
        b'.terminal = FullSpace.vertexImage (intShift n) b.1.terminal :=
    ⟨(translateEdge (vertexOfInt L n) b).1, (vertexImage_intShift n _).symm,
      (vertexImage_intShift n _).symm⟩
  have hb := Classical.epsilon_spec hm
  have e : FullSpace.edgeImage (intShift n) b.1 = (translateEdge (vertexOfInt L n) b).1 :=
    InfiniteLattice.Link.ext (hb.1.trans (vertexImage_intShift n _))
      (hb.2.trans (vertexImage_intShift n _))
  have h : ∃ b' : PeriodicOperators.PosEdge L 0 0,
      b'.1 = FullSpace.edgeImage (intShift n) b.1 :=
    ⟨translateEdge (vertexOfInt L n) b, e.symm⟩
  exact Subtype.ext ((Classical.epsilon_spec h).trans e)
def translateField (v : FullSpace.Vertex L 0 0) (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) :
    FullSpace.PositiveEdge (meshAt L 0 0) → ℝ :=
  fun b => θ (translateEdge v b)
theorem abelianLinkField_positive {a : ℝ} (θ : FullSpace.PositiveEdge a → ℝ)
    (b : FullSpace.PositiveEdge a) :
    FullSpace.abelianLinkField θ b.1 = phaseMatrix (θ b) := by
  unfold FullSpace.abelianLinkField
  rw [dif_pos b.2]
  exact matExp_pauliZ_eq_phaseMatrix _
theorem abelianLinkField_translate (v : FullSpace.Vertex L 0 0)
    (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.abelianLinkField θ (translateEdge v b).1 =
      FullSpace.abelianLinkField (translateField v θ) b.1 := by
  rw [abelianLinkField_positive, abelianLinkField_positive]
  rfl
theorem euclidNormVec_initial_sub_endpoint (b : FullSpace.PositiveEdge (meshAt L 0 0))
    {y : FullSpace.Vertex L 0 0} (hy : b.1.terminal = y ∨ b.1.initial = y) :
    TorusMetric.euclidNormVec
      ((b.1.initial : InfiniteLattice.AmbientSpace) - (y : InfiniteLattice.AmbientSpace)) ≤ 1 := by
  obtain ⟨μ, hμ⟩ := b.2
  rcases hy with rfl | rfl
  · have e : (b.1.initial : InfiniteLattice.AmbientSpace) -
        (b.1.terminal : InfiniteLattice.AmbientSpace) =
        -((InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) :
          InfiniteLattice.AmbientSpace) := by
      rw [← hμ]
      simp
    rw [e, euclidNormVec_neg, euclidNormVec_axisStep]
  · simp [euclidNormVec_zero]
theorem euclidNormVec_initial_sub_le_two {b b' : FullSpace.PositiveEdge (meshAt L 0 0)}
    {y : InfiniteLattice.AmbientSpace}
    (h : TorusMetric.euclidNormVec ((b.1.initial : InfiniteLattice.AmbientSpace) - y) ≤ 1)
    (h' : TorusMetric.euclidNormVec ((b'.1.initial : InfiniteLattice.AmbientSpace) - y) ≤ 1) :
    TorusMetric.euclidNormVec
      ((b.1.initial : InfiniteLattice.AmbientSpace) -
        (b'.1.initial : InfiniteLattice.AmbientSpace)) ≤ 2 := by
  have e : (b.1.initial : InfiniteLattice.AmbientSpace) -
      (b'.1.initial : InfiniteLattice.AmbientSpace) =
      ((b.1.initial : InfiniteLattice.AmbientSpace) - y) -
        ((b'.1.initial : InfiniteLattice.AmbientSpace) - y) := by
    abel
  rw [e]
  linarith [euclidNormVec_sub_le ((b.1.initial : InfiniteLattice.AmbientSpace) - y)
    ((b'.1.initial : InfiniteLattice.AmbientSpace) - y)]
end UnitLattice
section CovariantDifferenceKernel
open UnitGaugeDirections (IsUniqueRowFiniteKernelAction basisFunction)
theorem applyKernel_basisFunction {N : Type} (T : KernelMatrix N N) (ι' ι : N) :
    applyKernel T (basisFunction ι) ι' = T ι' ι := by apply _root_.YangMills.Construction.Tower.AbelianOperatorsLocalSelfAdjointProof.applyKernel_basisFunction <;> assumption
theorem kernelOfMap_apply {N : Type} {M : (N → ℂ) → N → ℂ}
    (h : IsUniqueRowFiniteKernelAction M) (ι' ι : N) :
    PeriodicOperators.kernelOfMap M ι' ι = M (basisFunction ι) ι' := by
  obtain ⟨T, hG, hU, hE, -⟩ := h
  have hs : Represents (PeriodicOperators.kernelOfMap M) M :=
    Classical.epsilon_spec (p := fun T => Represents T M) ⟨T, hG⟩
  rw [hU _ hs, hE]
variable {a : ℝ}
theorem extendOddly_of_positive (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = f b := if_pos hb
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
variable {L : ℕ}
theorem vertexCoordinates_ofCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) :
    (vertexCoordinate σ).ofCoeffs c ∈ (vertexCoordinate σ).space.complexSubmodule :=
  fun i _ => ofPauliCoeffs_mem_traceless c i
theorem vertexCoordinate_coeffs_ofCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    (vertexCoordinate σ).coeffs ((vertexCoordinate σ).ofCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
theorem edgePauliCoordinates_ofCoeffs_mem (c : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c ∈
      (FullSpace.edgePauliCoordinates L 0 0).space.complexSubmodule := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.edge_ofCoeffs_mem <;> assumption
theorem edgePauliCoordinates_coeffs_ofCoeffs (c : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L 0 0).coeffs ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.edge_coeffs_ofCoeffs <;> assumption
abbrev TransposeDataAt (U : FullSpace.Edge L 0 0 → ComplexMatrix2) : Prop :=
  LatticeTransposeData (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.edgePauliCoordinates L 0 0)
    (vertexCoordinate (FullSpace.Face L 0 0)) (FullSpace.covDiff U)
    FullSpace.vertexCoboundary FullSpace.edgeCoboundary
    (FullSpace.complexHessianOperator U) (FullSpace.complexHessianKernel U)
abbrev covDiffKernel (U : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → Fin 3 × FullSpace.Vertex L 0 0 → ℂ :=
  matrixKernel (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.edgePauliCoordinates L 0 0)
    (FullSpace.covDiff U)
open Classical in
def covDiffBasisValue (U : FullSpace.Edge L 0 0 → ComplexMatrix2) (a : Fin 3)
    (x : FullSpace.Vertex L 0 0) (b : FullSpace.PositiveEdge (meshAt L 0 0)) : ComplexMatrix2 :=
  ComplexMatrix2.conjugateBy (U b.1) (if b.1.terminal = x then ComplexMatrix2.pauliFamily a else 0) -
    (if b.1.initial = x then ComplexMatrix2.pauliFamily a else 0)
theorem covDiffKernel_apply (U : FullSpace.Edge L 0 0 → ComplexMatrix2) (c a : Fin 3)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) (x : FullSpace.Vertex L 0 0) :
    covDiffKernel U (c, b) (a, x) = pauliCoeff c (covDiffBasisValue U a x b) := by
  show pauliCoeff c (FullSpace.covDiff U (ofPauliCoeffs _) b.1) = _
  refine congrArg (pauliCoeff c) ((extendOddly_of_positive _ b.2).trans ?_)
  exact congrArg₂ (fun X Y => ComplexMatrix2.conjugateBy (U b.1) X - Y)
    (ofPauliCoeffs_indicator a x b.1.terminal) (ofPauliCoeffs_indicator a x b.1.initial)
theorem abelianLaplacianKernel_apply {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
    (hC : TransposeDataAt (FullSpace.abelianLinkField θ))
    (hK : UnitGaugeDirections.CompositesAreKernels (FullSpace.abelianLinkField θ))
    (ι' ι : VertexIndex L) :
    abelianLaplacianKernel θ ι' ι =
      ∑' κ, covDiffKernel (FullSpace.abelianLinkField θ) κ ι' *
        covDiffKernel (FullSpace.abelianLinkField θ) κ ι := by
  have e₀ : abelianLaplacianKernel θ ι' ι = _ := kernelOfMap_apply hK.1 ι' ι
  rw [e₀]
  have e := (hC.transposeComp_represents.2 ((vertexCoordinate (FullSpace.Vertex L 0 0)).ofCoeffs
    (basisFunction ι)) (vertexCoordinates_ofCoeffs_mem _) ι').2
  have hc : (vertexCoordinate (FullSpace.Vertex L 0 0)).coeffs
      ((vertexCoordinate (FullSpace.Vertex L 0 0)).ofCoeffs (basisFunction ι)) =
      basisFunction ι := vertexCoordinate_coeffs_ofCoeffs _
  rw [hc] at e
  exact e.trans (applyKernel_basisFunction _ ι' ι)
theorem abelianHessianKernel_apply {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
    (hC : TransposeDataAt (FullSpace.abelianLinkField θ))
    (hK : UnitGaugeDirections.CompositesAreKernels (FullSpace.abelianLinkField θ))
    (ι' ι : EdgeIndex L) :
    abelianHessianKernel θ ι' ι =
      FullSpace.complexHessianKernel (FullSpace.abelianLinkField θ) ι' ι +
        ∑' κ, covDiffKernel (FullSpace.abelianLinkField θ) ι' κ *
          covDiffKernel (FullSpace.abelianLinkField θ) ι κ := by
  have e₀ : abelianHessianKernel θ ι' ι = _ := kernelOfMap_apply hK.2 ι' ι
  rw [e₀]
  have hB := edgePauliCoordinates_ofCoeffs_mem (L := L) (basisFunction ι)
  have e₂ := (hC.compTranspose_represents.2 _ hB ι').2
  rw [edgePauliCoordinates_coeffs_ofCoeffs] at e₂
  have e₂' := e₂.trans (applyKernel_basisFunction _ ι' ι)
  have e₁ : FullSpace.complexHessianOperator (FullSpace.abelianLinkField θ)
      ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (basisFunction ι)) ι'.2.1 =
      ofPauliCoeffs (applyKernel (FullSpace.complexHessianKernel (FullSpace.abelianLinkField θ))
        (basisFunction ι)) ι'.2 := by
    have e : toPauliCoeffs (FullSpace.restrictToPositiveEdges
        ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (basisFunction ι))) = basisFunction ι :=
      edgePauliCoordinates_coeffs_ofCoeffs _
    have e₃ : FullSpace.complexHessianOperator (FullSpace.abelianLinkField θ)
        ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (basisFunction ι)) ι'.2.1 =
        ofPauliCoeffs (applyKernel (FullSpace.complexHessianKernel (FullSpace.abelianLinkField θ))
          (toPauliCoeffs (FullSpace.restrictToPositiveEdges
            ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (basisFunction ι))))) ι'.2 := by
      show FullSpace.extendOddly _ _ = _
      rw [extendOddly_of_positive _ ι'.2.2]
      exact dif_pos ι'.2.2
    rw [e₃, e]
  have m₁ : FullSpace.complexHessianOperator (FullSpace.abelianLinkField θ)
      ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (basisFunction ι)) ι'.2.1 ∈
        ComplexMatrix2.traceless := by
    rw [e₁]
    exact ofPauliCoeffs_mem_traceless _ _
  have m₂ := (hC.compTranspose_mem _ hB).2.1 ι'.2.1 ι'.2.2
  have e₃ : pauliCoeff ι'.1 (FullSpace.complexHessianOperator (FullSpace.abelianLinkField θ)
      ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (basisFunction ι)) ι'.2.1) =
      FullSpace.complexHessianKernel (FullSpace.abelianLinkField θ) ι' ι := by
    rw [e₁]
    exact (congrFun (toPauliCoeffs_ofPauliCoeffs _) ι').trans
      (applyKernel_basisFunction _ ι' ι)
  exact (pauliCoeff_add ι'.1 m₁ m₂).trans (congrArg₂ (· + ·) e₃ e₂')
end CovariantDifferenceKernel
section CovariantDifferenceEntries
variable {L : ℕ}
theorem conjugateBy_phaseMatrix_mem (φ : ℝ) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy (phaseMatrix φ) X ∈ ComplexMatrix2.traceless := by
  show Matrix.trace (phaseMatrix φ * X * (phaseMatrix φ)⁻¹) = 0
  rw [Matrix.trace_mul_comm, ← mul_assoc, phaseMatrix_inv, phaseMatrix_neg_mul, one_mul]
  exact hX
theorem ite_pauliFamily_mem (P : Prop) [Decidable P] (a : Fin 3) :
    (if P then ComplexMatrix2.pauliFamily a else 0) ∈ ComplexMatrix2.traceless := by
  split_ifs
  · exact pauliFamily_mem_traceless a
  · exact Submodule.zero_mem _
theorem covDiffBasisValue_mem (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (a : Fin 3)
    (x : FullSpace.Vertex L 0 0) (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    covDiffBasisValue (FullSpace.abelianLinkField θ) a x b ∈ ComplexMatrix2.traceless := by
  unfold covDiffBasisValue
  rw [abelianLinkField_positive]
  exact Submodule.sub_mem _ (conjugateBy_phaseMatrix_mem _ (ite_pauliFamily_mem _ a))
    (ite_pauliFamily_mem _ a)
theorem dependsOn_covDiffKernel {S : Set (FullSpace.PositiveEdge (meshAt L 0 0))} [Finite S]
    (c a : Fin 3) (x : FullSpace.Vertex L 0 0) (b : FullSpace.PositiveEdge (meshAt L 0 0))
    (hb : b ∈ S ∨ (b.1.terminal ≠ x ∧ b.1.initial ≠ x)) :
    DependsOn S fun θ => covDiffKernel (FullSpace.abelianLinkField θ) (c, b) (a, x) := by
  simp only [covDiffKernel_apply]
  rcases hb with hb | ⟨h₁, h₂⟩
  · refine dependsOn_pauliCoeff ?_ (fun θ => covDiffBasisValue_mem θ a x b) c
    unfold covDiffBasisValue
    simp only [abelianLinkField_positive, ComplexMatrix2.conjugateBy]
    have hS := invDependsOn_phaseMatrix hb 1
    simp only [Int.cast_one, one_mul] at hS
    exact ((hS.1.mul (MatDependsOn.const _)).mul hS.2).sub (MatDependsOn.const _)
  · have e : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
        covDiffBasisValue (FullSpace.abelianLinkField θ) a x b = 0 := by
      intro θ
      simp [covDiffBasisValue, h₁, h₂, ComplexMatrix2.conjugateBy]
    simp only [e, pauliCoeff_zero]
    exact DependsOn.const 0
theorem covDiffKernel_eq_zero (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (c a : Fin 3)
    {x : FullSpace.Vertex L 0 0} {b : FullSpace.PositiveEdge (meshAt L 0 0)}
    (h₁ : b.1.terminal ≠ x) (h₂ : b.1.initial ≠ x) :
    covDiffKernel (FullSpace.abelianLinkField θ) (c, b) (a, x) = 0 := by
  rw [covDiffKernel_apply]
  have e : covDiffBasisValue (FullSpace.abelianLinkField θ) a x b = 0 := by
    simp [covDiffBasisValue, h₁, h₂, ComplexMatrix2.conjugateBy]
  rw [e, pauliCoeff_zero]
theorem covDiffKernel_translate (v : FullSpace.Vertex L 0 0)
    (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (c a : Fin 3)
    (x : FullSpace.Vertex L 0 0) (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    covDiffKernel (FullSpace.abelianLinkField θ) (c, translateEdge v b) (a, x + v) =
      covDiffKernel (FullSpace.abelianLinkField (translateField v θ)) (c, b) (a, x) := by
  rw [covDiffKernel_apply, covDiffKernel_apply]
  congr 1
  unfold covDiffBasisValue
  rw [abelianLinkField_translate]
  have h₁ : (translateEdge v b).1.terminal = x + v ↔ b.1.terminal = x := add_left_inj v
  have h₂ : (translateEdge v b).1.initial = x + v ↔ b.1.initial = x := add_left_inj v
  simp only [h₁, h₂]
end CovariantDifferenceEntries
section Products
variable {L : ℕ}
theorem dependsOn_abelianLaplacianKernel {S : Set (FullSpace.PositiveEdge (meshAt L 0 0))}
    [Finite S]
    (hC : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      TransposeDataAt (FullSpace.abelianLinkField θ))
    (hK : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      UnitGaugeDirections.CompositesAreKernels (FullSpace.abelianLinkField θ))
    (ι' ι : VertexIndex L)
    (hS : ∀ b : FullSpace.PositiveEdge (meshAt L 0 0),
      (b.1.terminal = ι'.2 ∨ b.1.initial = ι'.2) → b ∈ S) :
    DependsOn S fun θ => abelianLaplacianKernel θ ι' ι := by
  classical
  let F : Finset (Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0)) :=
    Finset.univ ×ˢ (Set.toFinite S).toFinset
  have e : ∀ θ, abelianLaplacianKernel θ ι' ι =
      ∑ κ ∈ F, covDiffKernel (FullSpace.abelianLinkField θ) κ ι' *
        covDiffKernel (FullSpace.abelianLinkField θ) κ ι := by
    intro θ
    rw [abelianLaplacianKernel_apply (hC θ) (hK θ)]
    refine tsum_eq_sum fun κ hκ => ?_
    have hb : κ.2 ∉ S := fun h => hκ (Finset.mem_product.mpr
      ⟨Finset.mem_univ _, (Set.toFinite S).mem_toFinset.mpr h⟩)
    have hz : covDiffKernel (FullSpace.abelianLinkField θ) κ ι' = 0 :=
      covDiffKernel_eq_zero θ κ.1 ι'.1 (fun h => hb (hS _ (Or.inl h)))
        (fun h => hb (hS _ (Or.inr h)))
    rw [hz, zero_mul]
  simp only [e]
  refine DependsOn.sum F fun κ hκ => ?_
  have hb : κ.2 ∈ S := (Set.toFinite S).mem_toFinset.mp (Finset.mem_product.mp hκ).2
  exact (dependsOn_covDiffKernel κ.1 ι'.1 ι'.2 κ.2 (Or.inl hb)).mul
    (dependsOn_covDiffKernel κ.1 ι.1 ι.2 κ.2 (Or.inl hb))
theorem abelianLaplacianKernel_translate
    (hC : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      TransposeDataAt (FullSpace.abelianLinkField θ))
    (hK : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      UnitGaugeDirections.CompositesAreKernels (FullSpace.abelianLinkField θ))
    (v : FullSpace.Vertex L 0 0) (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (ι' ι : VertexIndex L) :
    abelianLaplacianKernel θ (ι'.1, ι'.2 + v) (ι.1, ι.2 + v) =
      abelianLaplacianKernel (translateField v θ) ι' ι := by
  rw [abelianLaplacianKernel_apply (hC _) (hK _), abelianLaplacianKernel_apply (hC _) (hK _),
    ← Equiv.tsum_eq ((Equiv.refl (Fin 3)).prodCongr (translateEdgeEquiv v))]
  refine tsum_congr fun κ => ?_
  exact congrArg₂ (· * ·) (covDiffKernel_translate v θ κ.1 ι'.1 ι'.2 κ.2)
    (covDiffKernel_translate v θ κ.1 ι.1 ι.2 κ.2)
def covDiffGram (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (ι' ι : EdgeIndex L) : ℂ :=
  ∑' κ, covDiffKernel (FullSpace.abelianLinkField θ) ι' κ *
    covDiffKernel (FullSpace.abelianLinkField θ) ι κ
theorem dependsOn_covDiffGram {S : Set (FullSpace.PositiveEdge (meshAt L 0 0))} [Finite S]
    (ι' ι : EdgeIndex L) (hb' : ι'.2 ∈ S)
    (hS : ∀ y : FullSpace.Vertex L 0 0, (ι'.2.1.terminal = y ∨ ι'.2.1.initial = y) →
      (ι.2.1.terminal = y ∨ ι.2.1.initial = y) → ι.2 ∈ S) :
    DependsOn S fun θ => covDiffGram θ ι' ι := by
  classical
  let F : Finset (Fin 3 × FullSpace.Vertex L 0 0) :=
    Finset.univ ×ˢ {ι'.2.1.terminal, ι'.2.1.initial}
  have e : ∀ θ, covDiffGram θ ι' ι =
      ∑ κ ∈ F, covDiffKernel (FullSpace.abelianLinkField θ) ι' κ *
        covDiffKernel (FullSpace.abelianLinkField θ) ι κ := by
    intro θ
    refine tsum_eq_sum fun κ hκ => ?_
    have hy : κ.2 ≠ ι'.2.1.terminal ∧ κ.2 ≠ ι'.2.1.initial := by
      constructor
      · intro h
        exact hκ (Finset.mem_product.mpr ⟨Finset.mem_univ _, by simp [h]⟩)
      · intro h
        exact hκ (Finset.mem_product.mpr ⟨Finset.mem_univ _, by simp [h]⟩)
    have hz : covDiffKernel (FullSpace.abelianLinkField θ) ι' κ = 0 :=
      covDiffKernel_eq_zero θ ι'.1 κ.1 (fun h => hy.1 h.symm) (fun h => hy.2 h.symm)
    rw [hz, zero_mul]
  simp only [e]
  refine DependsOn.sum F fun κ hκ => ?_
  have hy : ι'.2.1.terminal = κ.2 ∨ ι'.2.1.initial = κ.2 := by
    have : κ.2 = ι'.2.1.terminal ∨ κ.2 = ι'.2.1.initial := by
      simpa using (Finset.mem_product.mp hκ).2
    exact this.imp Eq.symm Eq.symm
  refine (dependsOn_covDiffKernel ι'.1 κ.1 κ.2 ι'.2 (Or.inl hb')).mul
    (dependsOn_covDiffKernel ι.1 κ.1 κ.2 ι.2 ?_)
  by_cases h : ι.2.1.terminal = κ.2 ∨ ι.2.1.initial = κ.2
  · exact Or.inl (hS _ hy h)
  · exact Or.inr ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩
theorem covDiffGram_translate (v : FullSpace.Vertex L 0 0)
    (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (ι' ι : EdgeIndex L) :
    covDiffGram θ (ι'.1, translateEdge v ι'.2) (ι.1, translateEdge v ι.2) =
      covDiffGram (translateField v θ) ι' ι := by
  unfold covDiffGram
  rw [← Equiv.tsum_eq ((Equiv.refl (Fin 3)).prodCongr (Equiv.addRight v))]
  refine tsum_congr fun κ => ?_
  exact congrArg₂ (· * ·) (covDiffKernel_translate v θ ι'.1 κ.1 κ.2 ι'.2)
    (covDiffKernel_translate v θ ι.1 κ.1 κ.2 ι.2)
end Products
section HessianOfTheAction
open FaceTermDerivatives (secondDerivExpr commutatorSum)
open HessianKernel (IsSymmBilinearOn finiteSupportComplexForms)
variable {L : ℕ}
def faceSecondDeriv (U C : FullSpace.Edge L 0 0 → ComplexMatrix2) (p : FullSpace.Face L 0 0) : ℂ :=
  secondDerivExpr (FullSpace.transportedForm U C p) (FullSpace.faceVariable U p)
def facePolarization (U B' B : FullSpace.Edge L 0 0 → ComplexMatrix2) (p : FullSpace.Face L 0 0) :
    ℂ :=
  (1 / 2) * (faceSecondDeriv U (B' + B) p - faceSecondDeriv U B' p - faceSecondDeriv U B p)
theorem faceSecondDeriv_eq_zero (U C : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (p : FullSpace.Face L 0 0) (hC : ∀ i, C (FullSpace.faceEdge p i) = 0) :
    faceSecondDeriv U C p = 0 := by
  have e : FullSpace.transportedForm U C p = 0 := by
    funext i
    simp [FullSpace.transportedForm, hC, ComplexMatrix2.conjugateBy]
  unfold faceSecondDeriv
  rw [e]
  simp [secondDerivExpr, commutatorSum]
theorem facePolarization_eq_zero (U B' B : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (p : FullSpace.Face L 0 0) (hB : ∀ i, B' (FullSpace.faceEdge p i) = 0) :
    facePolarization U B' B p = 0 := by
  have e : FullSpace.transportedForm U (B' + B) p = FullSpace.transportedForm U B p := by
    funext i
    simp [FullSpace.transportedForm, hB]
  have e' : faceSecondDeriv U (B' + B) p = faceSecondDeriv U B p := by
    unfold faceSecondDeriv
    rw [e]
  unfold facePolarization
  rw [e', faceSecondDeriv_eq_zero U B' p hB]
  simp
theorem add_mem_finiteSupportComplexForms {B' B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB' : B' ∈ finiteSupportComplexForms L 0 0) (hB : B ∈ finiteSupportComplexForms L 0 0) :
    B' + B ∈ finiteSupportComplexForms L 0 0 := by
  refine ⟨Submodule.add_mem _ hB'.1 hB.1, (hB'.2.union hB.2).subset ?_⟩
  rintro b ⟨hp, hb⟩
  by_contra hn
  have h₁ : B' b = 0 := by
    by_contra h
    exact hn (Or.inl ⟨hp, h⟩)
  have h₂ : B b = 0 := by
    by_contra h
    exact hn (Or.inr ⟨hp, h⟩)
  exact hb (by simp [h₁, h₂])
theorem complexActionHessian_eq_sum_facePolarization
    {U B' B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hbil : IsSymmBilinearOn (finiteSupportComplexForms L 0 0)
      (FullSpace.complexActionHessian U))
    (hsec : ∀ C ∈ finiteSupportComplexForms L 0 0,
      ∑ᶠ p, faceSecondDeriv U C p = FullSpace.complexActionHessian U C C)
    (hB' : B' ∈ finiteSupportComplexForms L 0 0) (hB : B ∈ finiteSupportComplexForms L 0 0)
    (G : Finset (FullSpace.Face L 0 0))
    (hG : ∀ p ∉ G, (∀ i, B' (FullSpace.faceEdge p i) = 0) ∧
      ∀ i, B (FullSpace.faceEdge p i) = 0) :
    FullSpace.complexActionHessian U B' B = ∑ p ∈ G, facePolarization U B' B p := by
  have hC := add_mem_finiteSupportComplexForms hB' hB
  have sum_of : ∀ C : FullSpace.Edge L 0 0 → ComplexMatrix2,
      (∀ p ∉ G, ∀ i, C (FullSpace.faceEdge p i) = 0) →
      ∑ᶠ p, faceSecondDeriv U C p = ∑ p ∈ G, faceSecondDeriv U C p := by
    intro C hz
    refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
    by_contra hn
    exact hp (faceSecondDeriv_eq_zero U C p (hz p hn))
  have e₁ := sum_of B' fun p hp => (hG p hp).1
  have e₂ := sum_of B fun p hp => (hG p hp).2
  have e₃ := sum_of (B' + B) fun p hp i => by
    simp [(hG p hp).1 i, (hG p hp).2 i]
  rw [hsec _ hB'] at e₁
  rw [hsec _ hB] at e₂
  rw [hsec _ hC] at e₃
  have b₁ := (hbil 1 B' hB' B hB (B' + B) hC).1
  have b₂ := (hbil 1 B' hB' B hB B' hB').2.1
  have b₃ := (hbil 1 B' hB' B hB B hB).2.1
  have b₄ := (hbil 1 B' hB' B hB B hB).2.2
  rw [one_smul] at b₁ b₂ b₃
  simp only [one_mul] at b₁ b₂ b₃
  have key : FullSpace.complexActionHessian U (B' + B) (B' + B) =
      FullSpace.complexActionHessian U B' B' +
        2 * FullSpace.complexActionHessian U B' B +
        FullSpace.complexActionHessian U B B := by
    rw [b₁, b₂, b₃, ← b₄]
    ring
  unfold facePolarization
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← e₁, ← e₂, ← e₃, key]
  ring
theorem fin_four_forall {P : Fin 4 → Prop} (h₀ : P 0) (h₁ : P 1) (h₂ : P 2) (h₃ : P 3) :
    ∀ i, P i := by
  intro i
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂
  · exact h₃
theorem faceTransports_zero (U : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (p : FullSpace.Face L 0 0) : FullSpace.faceTransports U p 0 = 1 := rfl
theorem faceTransports_one (U : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (p : FullSpace.Face L 0 0) :
    FullSpace.faceTransports U p 1 = U (FullSpace.faceEdge p 0) := rfl
theorem faceTransports_two (U : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (p : FullSpace.Face L 0 0) :
    FullSpace.faceTransports U p 2 = U (FullSpace.faceEdge p 0) * U (FullSpace.faceEdge p 1) *
      (U (FullSpace.faceEdge p 2))⁻¹ := rfl
theorem faceTransports_three (U : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (p : FullSpace.Face L 0 0) :
    FullSpace.faceTransports U p 3 = FullSpace.faceVariable U p := rfl
theorem faceVariable_eq {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hU : FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup U) (p : FullSpace.Face L 0 0) :
    FullSpace.faceVariable U p = U (FullSpace.faceEdge p 0) * U (FullSpace.faceEdge p 1) *
      (U (FullSpace.faceEdge p 2))⁻¹ * (U (FullSpace.faceEdge p 3))⁻¹ :=
  FullSpace.faceVariable_eq_edge_product hU p
theorem invDependsOn_faceTransports {S : Set (FullSpace.PositiveEdge (meshAt L 0 0))} [Finite S]
    (hcfg : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup (FullSpace.abelianLinkField θ))
    (p : FullSpace.Face L 0 0) (hp : ∀ i, facePositiveEdge p i ∈ S) (i : Fin 4) :
    InvDependsOn S fun θ => FullSpace.faceTransports (FullSpace.abelianLinkField θ) p i := by
  have hU : ∀ (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (i : Fin 4),
      FullSpace.abelianLinkField θ (FullSpace.faceEdge p i) =
        phaseMatrix (θ (facePositiveEdge p i)) := by
    intro θ i
    rw [← facePositiveEdge_val, abelianLinkField_positive]
  have s₁ : ∀ i, InvDependsOn S fun θ => FullSpace.abelianLinkField θ (FullSpace.faceEdge p i) := by
    intro i
    have h := invDependsOn_phaseMatrix (hp i) 1
    simp only [Int.cast_one, one_mul] at h
    simpa only [hU] using h
  have s₂ : ∀ i, InvDependsOn S fun θ =>
      (FullSpace.abelianLinkField θ (FullSpace.faceEdge p i))⁻¹ := by
    intro i
    have h := invDependsOn_phaseMatrix (hp i) (-1)
    simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
    simpa only [hU, phaseMatrix_inv] using h
  revert i
  refine fin_four_forall ?_ ?_ ?_ ?_
  · simp only [faceTransports_zero]
    exact InvDependsOn.one
  · simp only [faceTransports_one]
    exact s₁ 0
  · simp only [faceTransports_two]
    exact ((s₁ 0).mul (s₁ 1)).mul (s₂ 2)
  · simp only [faceTransports_three, faceVariable_eq (hcfg _)]
    exact (((s₁ 0).mul (s₁ 1)).mul (s₂ 2)).mul (s₂ 3)
theorem dependsOn_faceSecondDeriv {S : Set (FullSpace.PositiveEdge (meshAt L 0 0))} [Finite S]
    (hcfg : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup (FullSpace.abelianLinkField θ))
    (C : FullSpace.Edge L 0 0 → ComplexMatrix2) (p : FullSpace.Face L 0 0)
    (hp : ∀ i, facePositiveEdge p i ∈ S) :
    DependsOn S fun θ => faceSecondDeriv (FullSpace.abelianLinkField θ) C p := by
  have hT := invDependsOn_faceTransports hcfg p hp
  have hW : InvDependsOn S fun θ => FullSpace.faceVariable (FullSpace.abelianLinkField θ) p :=
    hT 3
  have hY : ∀ i, MatDependsOn S fun θ =>
      FullSpace.transportedForm (FullSpace.abelianLinkField θ) C p i := fun i =>
    (((hT i).1.mul (MatDependsOn.const _)).mul (hT i).2).smul _
  have hS : MatDependsOn S fun θ =>
      ∑ i, FullSpace.transportedForm (FullSpace.abelianLinkField θ) C p i :=
    MatDependsOn.sum _ fun i _ => hY i
  have hc : MatDependsOn S fun θ =>
      commutatorSum (FullSpace.transportedForm (FullSpace.abelianLinkField θ) C p) :=
    MatDependsOn.sum _ fun i _ => MatDependsOn.sum _ fun m _ =>
      ((hY i).mul (hY m)).sub ((hY m).mul (hY i))
  exact ((hW.1.trace.smul (1 / 2)).mul ((hS.mul hS).trace.smul (1 / 2))).add
    ((hc.mul (hW.1.sub hW.2)).trace.smul (1 / 4))
theorem dependsOn_facePolarization {S : Set (FullSpace.PositiveEdge (meshAt L 0 0))} [Finite S]
    (hcfg : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup (FullSpace.abelianLinkField θ))
    (B' B : FullSpace.Edge L 0 0 → ComplexMatrix2) (p : FullSpace.Face L 0 0)
    (hp : ∀ i, facePositiveEdge p i ∈ S) :
    DependsOn S fun θ => facePolarization (FullSpace.abelianLinkField θ) B' B p :=
  (((dependsOn_faceSecondDeriv hcfg (B' + B) p hp).sub (dependsOn_faceSecondDeriv hcfg B' p hp)).sub
    (dependsOn_faceSecondDeriv hcfg B p hp)).smul (1 / 2)
theorem facePositiveEdge_translateFace (v : FullSpace.Vertex L 0 0) (p : FullSpace.Face L 0 0)
    (i : Fin 4) :
    facePositiveEdge (translateFace v p) i = translateEdge v (facePositiveEdge p i) := by
  refine Subtype.ext (InfiniteLattice.Link.ext ?_ ?_)
  · fin_cases i
    · rfl
    · exact add_right_comm _ _ _
    · exact add_right_comm _ _ _
    · rfl
  · fin_cases i
    · exact add_right_comm _ _ _
    · show p.corner + v + _ + _ = p.corner + _ + _ + v
      rw [add_right_comm p.corner v, add_right_comm (p.corner + _) v]
      rfl
    · show p.corner + v + _ + _ = p.corner + _ + _ + v
      rw [add_right_comm p.corner v, add_right_comm (p.corner + _) v]
      rfl
    · exact add_right_comm _ _ _
theorem faceSecondDeriv_translate
    (hcfg : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup (FullSpace.abelianLinkField θ))
    (v : FullSpace.Vertex L 0 0) (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (C' C : FullSpace.Edge L 0 0 → ComplexMatrix2) (p : FullSpace.Face L 0 0)
    (hC : ∀ i, C' (FullSpace.faceEdge (translateFace v p) i) = C (FullSpace.faceEdge p i)) :
    faceSecondDeriv (FullSpace.abelianLinkField θ) C' (translateFace v p) =
      faceSecondDeriv (FullSpace.abelianLinkField (translateField v θ)) C p := by
  have hu : ∀ i, FullSpace.abelianLinkField θ (FullSpace.faceEdge (translateFace v p) i) =
      FullSpace.abelianLinkField (translateField v θ) (FullSpace.faceEdge p i) := by
    intro i
    rw [← facePositiveEdge_val, ← facePositiveEdge_val, facePositiveEdge_translateFace,
      abelianLinkField_translate]
  have hW : FullSpace.faceVariable (FullSpace.abelianLinkField θ) (translateFace v p) =
      FullSpace.faceVariable (FullSpace.abelianLinkField (translateField v θ)) p := by
    rw [faceVariable_eq (hcfg θ), faceVariable_eq (hcfg _), hu, hu, hu, hu]
  have hT : ∀ i, FullSpace.faceTransports (FullSpace.abelianLinkField θ) (translateFace v p) i =
      FullSpace.faceTransports (FullSpace.abelianLinkField (translateField v θ)) p i := by
    refine fin_four_forall ?_ ?_ ?_ ?_
    · rw [faceTransports_zero, faceTransports_zero]
    · rw [faceTransports_one, faceTransports_one, hu]
    · rw [faceTransports_two, faceTransports_two, hu, hu, hu]
    · rw [faceTransports_three, faceTransports_three, hW]
  have hY : FullSpace.transportedForm (FullSpace.abelianLinkField θ) C' (translateFace v p) =
      FullSpace.transportedForm (FullSpace.abelianLinkField (translateField v θ)) C p := by
    funext i
    unfold FullSpace.transportedForm
    rw [hT, hC]
  unfold faceSecondDeriv
  rw [hY, hW]
end HessianOfTheAction
section BasisForms
open HessianKernel (IsSymmBilinearOn finiteSupportComplexForms)
variable {L : ℕ}
open Classical in
theorem basisForm_of_positive (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L 0 0))
    {c : FullSpace.Edge L 0 0} (hc : c.IsPositivelyOriented) :
    FullSpace.basisForm (k := 0) (j := 0) a b c =
      if c = b.1 then ComplexMatrix2.pauliFamily a else 0 :=
  extendOddly_of_positive _ hc
theorem basisForm_mem (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.basisForm (k := 0) (j := 0) a b ∈ finiteSupportComplexForms L 0 0 := by
  classical
  refine ⟨⟨fun c hc => ?_, fun c => extendOddly_opposite (meshAt_zero_zero_pos L) _ c⟩, ?_⟩
  · rw [basisForm_of_positive a b hc]
    exact ite_pauliFamily_mem _ a
  · refine (Set.finite_singleton b.1).subset ?_
    rintro c ⟨hc, hne⟩
    by_contra h
    apply hne
    rw [basisForm_of_positive a b hc, if_neg fun e => h (Set.mem_singleton_iff.mpr e)]
theorem basisForm_faceEdge_eq_zero (a : Fin 3) {b : FullSpace.PositiveEdge (meshAt L 0 0)}
    (p : FullSpace.Face L 0 0) (i : Fin 4) (h : facePositiveEdge p i ≠ b) :
    FullSpace.basisForm (k := 0) (j := 0) a b (FullSpace.faceEdge p i) = 0 := by
  rw [← facePositiveEdge_val, basisForm_of_positive a b (facePositiveEdge p i).2,
    if_neg fun e => h (Subtype.ext e)]
theorem basisForm_translate (v : FullSpace.Vertex L 0 0) (a : Fin 3)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) (p : FullSpace.Face L 0 0) (i : Fin 4) :
    FullSpace.basisForm (k := 0) (j := 0) a (translateEdge v b)
        (FullSpace.faceEdge (translateFace v p) i) =
      FullSpace.basisForm (k := 0) (j := 0) a b (FullSpace.faceEdge p i) := by
  classical
  rw [← facePositiveEdge_val, ← facePositiveEdge_val,
    basisForm_of_positive a _ (facePositiveEdge _ i).2,
    basisForm_of_positive a _ (facePositiveEdge _ i).2, facePositiveEdge_translateFace]
  by_cases h : facePositiveEdge p i = b
  · rw [h, if_pos rfl, if_pos rfl]
  · have hn : ¬ (translateEdge v (facePositiveEdge p i)).1 = (translateEdge v b).1 :=
      fun e => h ((translateEdgeEquiv v).injective (Subtype.ext e))
    rw [if_neg hn, if_neg fun e => h (Subtype.ext e)]
structure HessianInputs (L : ℕ) : Prop where
  isField : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
    FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup (FullSpace.abelianLinkField θ)
  symmBilinear : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
    IsSymmBilinearOn (finiteSupportComplexForms L 0 0)
      (FullSpace.complexActionHessian (FullSpace.abelianLinkField θ))
  finsum_eq : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
    ∀ C ∈ finiteSupportComplexForms L 0 0,
    ∑ᶠ p, faceSecondDeriv (FullSpace.abelianLinkField θ) C p =
      FullSpace.complexActionHessian (FullSpace.abelianLinkField θ) C C
  facesMeeting_finite : ∀ F : Set (FullSpace.Edge L 0 0), F.Finite →
    (∀ b ∈ F, b.IsPositivelyOriented) → (FaceEdgeFinsets.Unbounded.facesMeeting F).Finite
theorem exists_finset_faces (h : HessianInputs L) (b' b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    ∃ G : Finset (FullSpace.Face L 0 0), ∀ p ∉ G, ∀ i,
      facePositiveEdge p i ≠ b' ∧ facePositiveEdge p i ≠ b := by
  classical
  have hf := h.facesMeeting_finite {b'.1, b.1} (by simp) (by
    rintro c (rfl | rfl)
    · exact b'.2
    · exact b.2)
  refine ⟨hf.toFinset, fun p hp i => ⟨fun e => hp ?_, fun e => hp ?_⟩⟩
  · refine hf.mem_toFinset.mpr ⟨b'.1, by simp, ?_⟩
    rw [← e, facePositiveEdge_val]
    exact List.getElem_mem _
  · refine hf.mem_toFinset.mpr ⟨b.1, by simp, ?_⟩
    rw [← e, facePositiveEdge_val]
    exact List.getElem_mem _
theorem dependsOn_complexHessianKernel {S : Set (FullSpace.PositiveEdge (meshAt L 0 0))}
    [Finite S] (h : HessianInputs L) (ι' ι : EdgeIndex L)
    (hS : ∀ (p : FullSpace.Face L 0 0) (j : Fin 4), facePositiveEdge p j = ι'.2 →
      ∀ i, facePositiveEdge p i ∈ S) :
    DependsOn S fun θ => FullSpace.complexHessianKernel (FullSpace.abelianLinkField θ) ι' ι := by
  obtain ⟨G, hG⟩ := exists_finset_faces h ι'.2 ι.2
  have e : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      FullSpace.complexHessianKernel (FullSpace.abelianLinkField θ) ι' ι =
        ∑ p ∈ G, facePolarization (FullSpace.abelianLinkField θ)
          (FullSpace.basisForm ι'.1 ι'.2) (FullSpace.basisForm ι.1 ι.2) p := fun θ =>
    complexActionHessian_eq_sum_facePolarization (h.symmBilinear θ) (h.finsum_eq θ)
      (basisForm_mem _ _) (basisForm_mem _ _) G
      fun p hp => ⟨fun i => basisForm_faceEdge_eq_zero _ p i (hG p hp i).1,
        fun i => basisForm_faceEdge_eq_zero _ p i (hG p hp i).2⟩
  simp only [e]
  refine DependsOn.sum G fun p _ => ?_
  by_cases hj : ∃ j, facePositiveEdge p j = ι'.2
  · obtain ⟨j, hj⟩ := hj
    exact dependsOn_facePolarization h.isField _ _ p (hS p j hj)
  · have z : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
        facePolarization (FullSpace.abelianLinkField θ) (FullSpace.basisForm ι'.1 ι'.2)
          (FullSpace.basisForm ι.1 ι.2) p = 0 := fun θ =>
      facePolarization_eq_zero _ _ _ p fun i => basisForm_faceEdge_eq_zero _ p i fun e => hj ⟨i, e⟩
    simp only [z]
    exact DependsOn.const 0
theorem complexHessianKernel_eq_finsum (h : HessianInputs L)
    (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (ι' ι : EdgeIndex L) :
    FullSpace.complexHessianKernel (FullSpace.abelianLinkField θ) ι' ι =
      ∑ᶠ p, facePolarization (FullSpace.abelianLinkField θ)
        (FullSpace.basisForm ι'.1 ι'.2) (FullSpace.basisForm ι.1 ι.2) p := by
  obtain ⟨G, hG⟩ := exists_finset_faces h ι'.2 ι.2
  refine (complexActionHessian_eq_sum_facePolarization (h.symmBilinear θ) (h.finsum_eq θ)
    (basisForm_mem _ _) (basisForm_mem _ _) G
    fun p hp => ⟨fun i => basisForm_faceEdge_eq_zero _ p i (hG p hp i).1,
      fun i => basisForm_faceEdge_eq_zero _ p i (hG p hp i).2⟩).trans ?_
  refine (finsum_eq_sum_of_support_subset _ fun p hp => ?_).symm
  by_contra hn
  exact hp (facePolarization_eq_zero _ _ _ p fun i => basisForm_faceEdge_eq_zero _ p i (hG p hn i).1)
theorem complexHessianKernel_translate (h : HessianInputs L) (v : FullSpace.Vertex L 0 0)
    (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (ι' ι : EdgeIndex L) :
    FullSpace.complexHessianKernel (FullSpace.abelianLinkField θ)
        (ι'.1, translateEdge v ι'.2) (ι.1, translateEdge v ι.2) =
      FullSpace.complexHessianKernel (FullSpace.abelianLinkField (translateField v θ)) ι' ι := by
  rw [complexHessianKernel_eq_finsum h, complexHessianKernel_eq_finsum h,
    ← finsum_comp_equiv (translateFaceEquiv v)]
  refine finsum_congr fun p => ?_
  show facePolarization _ _ _ (translateFace v p) = _
  unfold facePolarization
  rw [faceSecondDeriv_translate h.isField v θ _ (FullSpace.basisForm ι'.1 ι'.2 +
      FullSpace.basisForm ι.1 ι.2) p (fun i => by
        simp only [Pi.add_apply, basisForm_translate]),
    faceSecondDeriv_translate h.isField v θ _ (FullSpace.basisForm ι'.1 ι'.2) p
      (basisForm_translate v _ _ p),
    faceSecondDeriv_translate h.isField v θ _ (FullSpace.basisForm ι.1 ι.2) p
      (basisForm_translate v _ _ p)]
end BasisForms
section MainClaim
variable {L : ℕ}
theorem euclidNormVec_faceEdge_initial_sub_corner (p : FullSpace.Face L 0 0) :
    ∀ i, TorusMetric.euclidNormVec
      (((facePositiveEdge p i).1.initial : InfiniteLattice.AmbientSpace) -
        (p.corner : InfiniteLattice.AmbientSpace)) ≤ 1 := by
  have z : TorusMetric.euclidNormVec ((p.corner : InfiniteLattice.AmbientSpace) -
      (p.corner : InfiniteLattice.AmbientSpace)) ≤ 1 := by
    simp [euclidNormVec_zero]
  have s : ∀ μ : Fin 4, TorusMetric.euclidNormVec
      (((p.corner + InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) :
        InfiniteLattice.AmbientSpace) - (p.corner : InfiniteLattice.AmbientSpace)) ≤ 1 := by
    intro μ
    have e : ((p.corner + InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) :
        InfiniteLattice.AmbientSpace) - (p.corner : InfiniteLattice.AmbientSpace) =
        ((InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) :
          InfiniteLattice.AmbientSpace) := by
      simp
    rw [e, euclidNormVec_axisStep]
  exact fin_four_forall z (s _) (s _) z
theorem edgesNear_finite (hI : EdgeIndexCount L) (y : FullSpace.Vertex L 0 0) :
    (edgesNear L (y : InfiniteLattice.AmbientSpace)).Finite := by
  have h := (hI.2 y).1
  refine (h.preimage (f := fun b : PeriodicOperators.PosEdge L 0 0 => ((0 : Fin 3), b))
    ?_).subset fun b hb => hb
  intro b _ b' _ e
  exact congrArg Prod.snd e
theorem forwardEdge_mem_edgesNear (x : FullSpace.Vertex L 0 0) :
    FullSpace.forwardEdge x 0 ∈ edgesNear L (x : InfiniteLattice.AmbientSpace) := by
  show TorusMetric.euclidNormVec ((x : InfiniteLattice.AmbientSpace) -
    (x : InfiniteLattice.AmbientSpace)) ≤ 2
  simp [euclidNormVec_zero]
theorem exists_trigPolynomial_of_dependsOn (I : PeriodicData)
    (T : (FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) → I.Carrier → I.Carrier → ℂ)
    (ι' ι : I.Carrier)
    (hfin : Finite (edgesNear L (I.pos ι')))
    (hne : Nonempty (edgesNear L (I.pos ι')))
    (hR : DependsOn (edgesNear L (I.pos ι')) fun θ => T θ ι' ι)
    (hc : ∀ (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (ζ : Fin 4 → ℤ),
      T θ (I.translate ζ ι') (I.translate ζ ι) = T (translateField (vertexOfInt L ζ) θ) ι' ι) :
    ∃ P : (edgesNear L (I.pos ι') → ℝ) → ℂ,
      IsTrigPolynomial P ∧
        ∀ (θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (ζ : Fin 4 → ℤ),
          T θ' (I.translate ζ ι') (I.translate ζ ι) =
            P fun b => θ' (shiftEdge ζ b.1) := by
  obtain ⟨P, hP, eP⟩ := hR
  refine ⟨P, ⟨hfin, hne, hasFourierCoeffs_of_mem_trigSpan hP⟩, fun θ' ζ => ?_⟩
  refine (hc θ' ζ).trans ((eP _).trans ?_)
  congr 1
  funext b
  show θ' (translateEdge _ b.1) = θ' (shiftEdge ζ b.1)
  rw [shiftEdge_eq_translateEdge]
end MainClaim
theorem entriesAreTrigPolynomials (hV : UnitLatticeL2Statement)
    (hX : CovDiffTransposes.Claim)
    (hY : UnitGaugeDirections.Claim)
    (hA : HessianKernel.KernelProperties)
    (hD : FaceTermDerivatives.Statement)
    (hF : FaceEdgeFinsets.FacesAndEdgesFinite)
    (hP : AbelianFieldPlaquettes.Claim) : EntriesAreTrigPolynomials := by
  intro L hL
  have hcfg : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup (FullSpace.abelianLinkField θ) := by
    intro θ
    have h : FullSpace.IsFieldIn PeriodicLattice.compactGaugeGroup (FullSpace.abelianLinkField θ) :=
      (hP L hL θ).abelianLinkField_mem
    exact ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.mp (h.1 b)).2, h.2⟩
  have hC : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      TransposeDataAt (FullSpace.abelianLinkField θ) := fun θ =>
    ((hX L hL 0 0 le_rfl).2 _ (hcfg θ)).1
  have hK : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      UnitGaugeDirections.CompositesAreKernels (FullSpace.abelianLinkField θ) := fun θ =>
    ((hY L hL).2 _ (hcfg θ)).2.2.2
  have hD' : HessianInputs L :=
    { isField := hcfg
      symmBilinear := fun θ => ((hA L hL 0 0 le_rfl).2 _ (hcfg θ)).1
      finsum_eq := fun θ C hc =>
        ((((hD L hL 0 0 le_rfl).2 C hc.1).2 hc.2).1 _ (hcfg θ)).1
      facesMeeting_finite := fun F h₁ h₂ => (((hF L hL 0 0 le_rfl).2).2.1 F h₁ h₂).1 }
  have hI : EdgeIndexCount L := (hV.2 L).2.2.2.2.2.1
  refine ⟨fun x => forwardEdge_mem_edgesNear x, fun ι' ι => ?_, fun ι' ι => ?_⟩
  · have hfin : Finite (edgesNear L ((colourVertices L 0 0).pos ι')) :=
      (edgesNear_finite hI ι'.2).to_subtype
    refine exists_trigPolynomial_of_dependsOn (colourVertices L 0 0) abelianLaplacianKernel ι' ι
      hfin ⟨⟨_, forwardEdge_mem_edgesNear ι'.2⟩⟩ ?_ fun θ ζ => ?_
    · refine dependsOn_abelianLaplacianKernel hC hK ι' ι fun b hb => ?_
      exact (euclidNormVec_initial_sub_endpoint b hb).trans (by norm_num)
    · have e : ∀ κ : VertexIndex L, (colourVertices L 0 0).translate ζ κ =
          (κ.1, κ.2 + vertexOfInt L ζ) := fun κ =>
        congrArg (Prod.mk κ.1) (vertexImage_intShift ζ κ.2)
      exact (congrArg₂ (abelianLaplacianKernel θ) (e ι') (e ι)).trans
        (abelianLaplacianKernel_translate hC hK _ θ ι' ι)
  · have hfin : Finite (edgesNear L ((colourEdges L 0 0).pos ι')) :=
      (edgesNear_finite hI ι'.2.1.initial).to_subtype
    have hmass : ∀ (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (κ' κ : EdgeIndex L),
        abelianHessianKernel θ κ' κ =
          FullSpace.complexHessianKernel (FullSpace.abelianLinkField θ) κ' κ +
            covDiffGram θ κ' κ := fun θ κ' κ => abelianHessianKernel_apply (hC θ) (hK θ) κ' κ
    refine exists_trigPolynomial_of_dependsOn (colourEdges L 0 0) abelianHessianKernel ι' ι hfin
      ⟨⟨_, forwardEdge_mem_edgesNear ι'.2.1.initial⟩⟩ ?_ fun θ ζ => ?_
    · have := hfin
      refine DependsOn.congr (fun θ => hmass θ ι' ι)
        (DependsOn.add (dependsOn_complexHessianKernel hD' ι' ι fun p j hj i => ?_)
          (dependsOn_covDiffGram ι' ι ?_ fun y h₁ h₂ => ?_))
      · have h₁ := euclidNormVec_faceEdge_initial_sub_corner p i
        have h₂ := euclidNormVec_faceEdge_initial_sub_corner p j
        rw [hj] at h₂
        exact euclidNormVec_initial_sub_le_two h₁ h₂
      · show TorusMetric.euclidNormVec ((ι'.2.1.initial : InfiniteLattice.AmbientSpace) -
          (ι'.2.1.initial : InfiniteLattice.AmbientSpace)) ≤ 2
        simp [euclidNormVec_zero]
      · exact euclidNormVec_initial_sub_le_two (euclidNormVec_initial_sub_endpoint ι.2 h₂)
          (euclidNormVec_initial_sub_endpoint ι'.2 h₁)
    · have e : ∀ κ : EdgeIndex L, (colourEdges L 0 0).translate ζ κ =
          (κ.1, translateEdge (vertexOfInt L ζ) κ.2) := fun κ =>
        congrArg (Prod.mk κ.1) (shiftEdge_eq_translateEdge ζ κ.2)
      refine (congrArg₂ (abelianHessianKernel θ) (e ι') (e ι)).trans ((hmass θ _ _).trans ?_)
      exact (congrArg₂ (· + ·) (complexHessianKernel_translate hD' _ θ ι' ι)
        (covDiffGram_translate _ θ ι' ι)).trans (hmass _ ι' ι).symm
end YangMills.Construction.Tower.AbelianKernelEntries
end
