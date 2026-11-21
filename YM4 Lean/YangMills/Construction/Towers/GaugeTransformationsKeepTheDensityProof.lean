import YangMills.Construction.Towers.MatrixFactsOfTheAlgebraOfTheLeftChartProof
import YangMills.Construction.Matrices.ConjugationOnTraceless
import YangMills.Construction.Matrices.LogarithmicChartsOfASpaceOfConfigurationsProof
import YangMills.Construction.OneLoop.PauliMatrixRelations
import YangMills.Construction.Towers.GaugeTransformationsKeepTheDensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.PeriodicOperators YangMills.Construction.Matrices
namespace Tower.AbelianFieldDensity.GaugeConjugation
open SectorDecomposition
section PauliCoordinates
variable (hP : OneLoop.PauliMatrixRelations)
include hP
theorem exists_pauli_basis :
    ∃ e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
      ∀ a, ((e a : ComplexMatrix2.traceless) : ComplexMatrix2) = ComplexMatrix2.pauliFamily a :=
  hP.2.2.2.1
theorem pauliFamily_mem (a : Fin 3) : ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by
  obtain ⟨e, he⟩ := exists_pauli_basis hP
  rw [← he a]
  exact (e a).2
theorem pauliCoeffs_sum_smul (c : Fin 3 → ℂ) :
    pauliCoeffs (∑ a, c a • ComplexMatrix2.pauliFamily a) = c := by
  obtain ⟨e, he⟩ := exists_pauli_basis hP
  have hs := Classical.epsilon_spec
    (p := fun c' : Fin 3 → ℂ => (∑ a, c a • ComplexMatrix2.pauliFamily a) =
      ∑ a, c' a • ComplexMatrix2.pauliFamily a) ⟨c, rfl⟩
  change (∑ a, c a • ComplexMatrix2.pauliFamily a) =
      ∑ a, pauliCoeffs (∑ a, c a • ComplexMatrix2.pauliFamily a) a • ComplexMatrix2.pauliFamily a
    at hs
  have hE : ∑ a, c a • e a =
      ∑ a, pauliCoeffs (∑ a, c a • ComplexMatrix2.pauliFamily a) a • e a := by
    apply Subtype.ext
    simpa [he] using hs
  have h1 := e.repr_sum_self c
  have h2 := e.repr_sum_self (pauliCoeffs (∑ a, c a • ComplexMatrix2.pauliFamily a))
  rw [← hE] at h2
  funext a
  rw [← h2, h1]
theorem sum_pauliCoeffs_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeffs X a • ComplexMatrix2.pauliFamily a = X := by
  obtain ⟨e, he⟩ := exists_pauli_basis hP
  have h := e.sum_repr ⟨X, hX⟩
  have h' : ∑ a, (e.repr ⟨X, hX⟩ a) • ComplexMatrix2.pauliFamily a = X := by
    calc ∑ a, (e.repr ⟨X, hX⟩ a) • ComplexMatrix2.pauliFamily a =
          ((∑ a, (e.repr ⟨X, hX⟩ a) • e a : ComplexMatrix2.traceless) : ComplexMatrix2) := by
          rw [AddSubmonoidClass.coe_finsetSum]
          exact Finset.sum_congr rfl fun a _ => by simp [he]
      _ = X := by rw [h]
  have hc := pauliCoeffs_sum_smul hP (fun a => e.repr ⟨X, hX⟩ a)
  rw [h'] at hc
  rw [hc]
  exact h'
theorem pauliCoeffs_linear_combination {X : Fin 3 → ComplexMatrix2}
    (hX : ∀ b, X b ∈ ComplexMatrix2.traceless) (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeffs (∑ b, c b • X b) a = ∑ b, c b * pauliCoeffs (X b) a := by
  have h : ∑ b, c b • X b =
      ∑ a, (∑ b, c b * pauliCoeffs (X b) a) • ComplexMatrix2.pauliFamily a := by
    calc ∑ b, c b • X b = ∑ b, c b • ∑ a, pauliCoeffs (X b) a • ComplexMatrix2.pauliFamily a :=
          Finset.sum_congr rfl fun b _ => by rw [sum_pauliCoeffs_smul hP (hX b)]
      _ = ∑ a, (∑ b, c b * pauliCoeffs (X b) a) • ComplexMatrix2.pauliFamily a := by
          simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
          exact Finset.sum_comm
  rw [h, pauliCoeffs_sum_smul hP]
theorem pauliCoeffs_pauliFamily (b a : Fin 3) :
    pauliCoeffs (ComplexMatrix2.pauliFamily b) a = (1 : Matrix (Fin 3) (Fin 3) ℂ) a b := by
  have h : ComplexMatrix2.pauliFamily b =
      ∑ a, (1 : Matrix (Fin 3) (Fin 3) ℂ) a b • ComplexMatrix2.pauliFamily a := by
    simp [Matrix.one_apply]
  rw [h, pauliCoeffs_sum_smul hP]
end PauliCoordinates
section Conjugation
theorem specialUnitary_inv_mem {g : ComplexMatrix2}
    (hg : g ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    g⁻¹ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by apply _root_.YangMills.SharedProofs.p33390 <;> assumption
theorem halfTraceProduct_conjugateBy {g : ComplexMatrix2}
    (hg : g ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) (X Y : ComplexMatrix2) :
    halfTraceProduct (ComplexMatrix2.conjugateBy g X) (ComplexMatrix2.conjugateBy g Y) =
      halfTraceProduct X Y := by apply _root_.YangMills.Construction.Tower.LeftChartAlgebra.MatrixIdentities.halfTraceProduct_conjugateBy <;> assumption
theorem conjugateBy_linear_combination (g : ComplexMatrix2) (c : Fin 3 → ℂ)
    (X : Fin 3 → ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (∑ b, c b • X b) = ∑ b, c b • ComplexMatrix2.conjugateBy g (X b) := by
  simp [ComplexMatrix2.conjugateBy, Finset.mul_sum, Finset.sum_mul]
end Conjugation
section PointwiseConjugation
variable {σ : Type}
def pointwiseConj (g F : σ → ComplexMatrix2) : σ → ComplexMatrix2 :=
  fun s => ComplexMatrix2.conjugateBy (g s) (F s)
def conjMatrix (g : σ → ComplexMatrix2) (s : σ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun a b => pauliCoeffs (ComplexMatrix2.conjugateBy (g s) (ComplexMatrix2.pauliFamily b)) a
theorem ofCoords_mem (hP : OneLoop.PauliMatrixRelations)
    (v : L2Field σ) (s : σ) : ofCoords v s ∈ ComplexMatrix2.traceless :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (pauliFamily_mem hP a)
theorem pauliCoeffs_ofCoords (hP : OneLoop.PauliMatrixRelations)
    (v : L2Field σ) (a : Fin 3) (s : σ) :
    pauliCoeffs (ofCoords v s) a = v (a, s) :=
  congrFun (pauliCoeffs_sum_smul hP fun a => v (a, s)) a
theorem ofCoords_injective (hP : OneLoop.PauliMatrixRelations)
    {v w : L2Field σ} (h : ofCoords v = ofCoords w) : v = w := by
  refine lp.ext (funext ?_)
  rintro ⟨a, s⟩
  rw [← pauliCoeffs_ofCoords hP v a s, ← pauliCoeffs_ofCoords hP w a s, h]
variable (hP : OneLoop.PauliMatrixRelations)
  (hA : ComplexMatrix2.ConjugationPreservesTraceless)
include hA in
theorem conjugateBy_mem_traceless {g X : ComplexMatrix2}
    (hg : g ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2))
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy g X ∈ ComplexMatrix2.traceless :=
  (hA.2.2 g (hA.2.1 g hg)).2.2.2.1 hX
include hA in
theorem conjugateBy_inv_cancel {g X : ComplexMatrix2}
    (hg : g ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2))
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy g⁻¹ (ComplexMatrix2.conjugateBy g X) = X ∧
      X = ComplexMatrix2.conjugateBy g (ComplexMatrix2.conjugateBy g⁻¹ X) :=
  (hA.2.2 g (hA.2.1 g hg)).2.2.2.2.2.2.2 X hX
include hA in
theorem exists_coords_of_pointwiseConj (hC : CoordsIsometry σ) {g : σ → ComplexMatrix2}
    (hg : ∀ s, g s ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) (f : L2Field σ) :
    ∃ w : L2Field σ, ofCoords w = pointwiseConj g (ofCoords f) := by
  have hf := (hC.2.2.1 f).1
  refine hC.2.2.2.1 _ ⟨fun s => conjugateBy_mem_traceless hA (hg s) (hf.1 s), ?_⟩
  have : (fun s => (halfTraceProduct (pointwiseConj g (ofCoords f) s)
      (pointwiseConj g (ofCoords f) s)).re) =
      fun s => (halfTraceProduct (ofCoords f s) (ofCoords f s)).re :=
    funext fun s => by rw [pointwiseConj, halfTraceProduct_conjugateBy (hg s)]
  rw [this]
  exact hf.2
include hP hA in
theorem apply_eq_conjMatrix_mul {g : σ → ComplexMatrix2}
    (hg : ∀ s, g s ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2))
    {V : L2Field σ → L2Field σ}
    (hV : ∀ f, ofCoords (V f) = pointwiseConj g (ofCoords f))
    (f : L2Field σ) (a : Fin 3) (s : σ) :
    V f (a, s) = ∑ b, conjMatrix g s a b * f (b, s) := by
  rw [← pauliCoeffs_ofCoords hP (V f) a s, hV f]
  change pauliCoeffs (ComplexMatrix2.conjugateBy (g s)
    (∑ b, f (b, s) • ComplexMatrix2.pauliFamily b)) a = _
  rw [conjugateBy_linear_combination, pauliCoeffs_linear_combination hP
    fun b => conjugateBy_mem_traceless hA (hg s) (pauliFamily_mem hP b)]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _
include hP hA in
theorem conjMatrix_inv_mul {g : σ → ComplexMatrix2}
    (hg : ∀ s, g s ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) (s : σ) :
    conjMatrix (fun s => (g s)⁻¹) s * conjMatrix g s = 1 := by
  ext c b
  rw [Matrix.mul_apply]
  have h := (conjugateBy_inv_cancel hA (hg s) (pauliFamily_mem hP b)).1
  have hm := conjugateBy_mem_traceless hA (hg s) (pauliFamily_mem hP b)
  have h2 : ComplexMatrix2.conjugateBy (g s)⁻¹
      (∑ a, pauliCoeffs (ComplexMatrix2.conjugateBy (g s) (ComplexMatrix2.pauliFamily b)) a •
        ComplexMatrix2.pauliFamily a) = ComplexMatrix2.pauliFamily b := by
    rw [sum_pauliCoeffs_smul hP hm, h]
  rw [conjugateBy_linear_combination] at h2
  have h3 : pauliCoeffs (∑ a, pauliCoeffs (ComplexMatrix2.conjugateBy (g s)
      (ComplexMatrix2.pauliFamily b)) a • ComplexMatrix2.conjugateBy (g s)⁻¹
        (ComplexMatrix2.pauliFamily a)) c = pauliCoeffs (ComplexMatrix2.pauliFamily b) c := by
    rw [h2]
  rw [pauliCoeffs_linear_combination hP fun a =>
      conjugateBy_mem_traceless hA (specialUnitary_inv_mem (hg s)) (pauliFamily_mem hP a),
    pauliCoeffs_pauliFamily hP] at h3
  rw [← h3]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _
open Classical in
theorem basisVec_apply {J : Type} (ι j : J) :
    (basisVec ι : lp (fun _ : J => ℂ) 2) j = if j = ι then 1 else 0 := by
  simp only [basisVec, lp.single_apply, Pi.single_apply]
theorem apply_basisVec (R : σ → Matrix (Fin 3) (Fin 3) ℂ)
    {V : L2Field σ → L2Field σ}
    (hV : ∀ f a s, V f (a, s) = ∑ b, R s a b * f (b, s)) (a : Fin 3) (s : σ) :
    V (basisVec (a, s)) = ∑ c, R s c a • basisVec (c, s) := by
  classical
  refine lp.ext (funext ?_)
  rintro ⟨b, s'⟩
  rw [hV, lp.coeFn_sum, Finset.sum_apply]
  by_cases hs : s' = s
  · subst hs
    simp [basisVec_apply]
  · simp [basisVec_apply, hs]
theorem diagonal_block_trace_eq (R R' : σ → Matrix (Fin 3) (Fin 3) ℂ)
    {V V' : L2Field σ → L2Field σ}
    (hV : ∀ f a s, V f (a, s) = ∑ b, R s a b * f (b, s))
    (hV' : ∀ f a s, V' f (a, s) = ∑ b, R' s a b * f (b, s))
    (hR : ∀ s, R' s * R s = 1)
    (S B : L2Field σ →L[ℂ] L2Field σ)
    (hB : ∀ ψ, B ψ = V (S (V' ψ))) (s : σ) :
    ∑ a, matrixEntry B (a, s) (a, s) = ∑ a, matrixEntry S (a, s) (a, s) := by
  let D : Matrix (Fin 3) (Fin 3) ℂ := Matrix.of fun b c => matrixEntry S (b, s) (c, s)
  have hent : ∀ a, matrixEntry B (a, s) (a, s) = ∑ b, ∑ c, R s a b * D b c * R' s c a := by
    intro a
    unfold matrixEntry
    rw [hB, hV, apply_basisVec R' hV', map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [lp.coeFn_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    simp only [D, matrixEntry, Matrix.of_apply]
    ring
  have htr : ∑ a, ∑ b, ∑ c, R s a b * D b c * R' s c a = Matrix.trace (R s * D * R' s) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  calc ∑ a, matrixEntry B (a, s) (a, s) = ∑ a, ∑ b, ∑ c, R s a b * D b c * R' s c a :=
        Finset.sum_congr rfl fun a _ => hent a
    _ = Matrix.trace (R s * D * R' s) := htr
    _ = Matrix.trace D := by
        rw [Matrix.trace_mul_comm, ← mul_assoc, hR, one_mul]
    _ = ∑ a, matrixEntry S (a, s) (a, s) := rfl
theorem coe_vertexAdd_zero {L : ℕ} (x : FullSpace.Vertex L 0 0) :
    (vertexAdd (L := L) 0 x : InfiniteLattice.AmbientSpace) =
      (x : InfiniteLattice.AmbientSpace) := by
  have hz : intShift 0 (x : InfiniteLattice.AmbientSpace) = x := by
    funext μ
    simp [intShift, castVec]
  have h : ∃ x' : FullSpace.Vertex L 0 0, (x' : InfiniteLattice.AmbientSpace) =
      intShift 0 (x : InfiniteLattice.AmbientSpace) := ⟨x, hz.symm⟩
  have hs := Classical.epsilon_spec h
  exact hs.trans hz
include hP hA in
theorem preservesTraceDensity_of_pointwiseConj {L : ℕ}
    (position : Fin 3 × σ → InfiniteLattice.AmbientSpace)
    (hC : CoordsIsometry σ) {g : σ → ComplexMatrix2}
    (hg : ∀ s, g s ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2))
    {V : L2Field σ → L2Field σ}
    (hV : ∀ f, ofCoords (V f) = pointwiseConj g (ofCoords f))
    (hfib : ∀ x : FullSpace.Vertex L 0 0, ∃ T : Finset σ,
      {ι | position ι = (x : InfiniteLattice.AmbientSpace)} =
        ((Finset.univ ×ˢ T : Finset (Fin 3 × σ)) : Set (Fin 3 × σ))) :
    PreservesTraceDensity (L := L) position V 0 := by
  have hg' : ∀ s, (fun s => (g s)⁻¹) s ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) :=
    fun s => specialUnitary_inv_mem (hg s)
  choose V' hV' using fun f => exists_coords_of_pointwiseConj hA hC hg' f
  have hVV' : ∀ f, V (V' f) = f := fun f => ofCoords_injective hP (by
    rw [hV, hV']
    funext s
    exact (conjugateBy_inv_cancel hA (hg s) (ofCoords_mem hP f s)).2.symm)
  have hV'V : ∀ f, V' (V f) = f := fun f => ofCoords_injective hP (by
    rw [hV', hV]
    funext s
    exact (conjugateBy_inv_cancel hA (hg s) (ofCoords_mem hP f s)).1)
  have hadd : ∀ f f', V (f + f') = V f + V f' := fun f f' => ofCoords_injective hP (by
    rw [hV, (hC.2.2.2.2.1 0 f f').1, (hC.2.2.2.2.1 0 (V f) (V f')).1, hV, hV]
    funext s
    simp [pointwiseConj, ComplexMatrix2.conjugateBy, mul_add, add_mul])
  have hsmul : ∀ (c : ℂ) f, V (c • f) = c • V f := fun c f => ofCoords_injective hP (by
    rw [hV, (hC.2.2.2.2.1 c f f).2, (hC.2.2.2.2.1 c (V f) (V f)).2, hV]
    funext s
    simp [pointwiseConj, ComplexMatrix2.conjugateBy])
  have hnorm : ∀ f, ‖V f‖ = ‖f‖ := fun f => by
    have h : inner ℂ (V f) (V f) = inner ℂ f f := by
      rw [← hC.2.2.2.2.2, ← hC.2.2.2.2.2, hV]
      exact tsum_congr fun s => halfTraceProduct_conjugateBy (hg s) _ _
    have h2 : ‖V f‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), h]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
  let E : L2Field σ ≃ₗᵢ[ℂ] L2Field σ :=
    { toFun := V
      invFun := V'
      map_add' := hadd
      map_smul' := hsmul
      left_inv := hV'V
      right_inv := hVV'
      norm_map' := hnorm }
  have hinj : Function.Injective V := E.injective
  have hinv : Function.invFun V = V' := by
    funext ψ
    have h := Function.leftInverse_invFun hinj (V' ψ)
    rwa [hVV'] at h
  refine ⟨⟨⟨hadd, hsmul⟩, E.bijective, hnorm⟩, fun S => ?_⟩
  rw [hinv]
  let B : L2Field σ →L[ℂ] L2Field σ :=
    (E.toContinuousLinearEquiv : _ →L[ℂ] _).comp
      (S.comp (E.symm.toContinuousLinearEquiv : _ →L[ℂ] _))
  have hB : ∀ ψ, B ψ = V (S (V' ψ)) := fun ψ => rfl
  refine ⟨⟨B, hB⟩, fun x => ?_⟩
  have hop : toBddOp (fun f => V (S (V' f))) = B := by
    have hex : ∃ B' : L2Field σ →L[ℂ] L2Field σ, ∀ ψ, B' ψ = V (S (V' ψ)) := ⟨B, hB⟩
    have hs := Classical.epsilon_spec hex
    ext1 ψ
    rw [hB]
    exact hs ψ
  rw [hop, coe_vertexAdd_zero]
  obtain ⟨T, hT⟩ := hfib x
  unfold traceAt
  rw [hT, finsum_mem_coe_finset, finsum_mem_coe_finset, Finset.sum_product_right,
    Finset.sum_product_right]
  exact Finset.sum_congr rfl fun s _ => diagonal_block_trace_eq _ _
    (apply_eq_conjMatrix_mul hP hA hg hV) (apply_eq_conjMatrix_mul hP hA hg' hV')
    (conjMatrix_inv_mul hP hA hg) S B hB s
end PointwiseConjugation
theorem gaugeKeepsTraceDensity_holds (hP : OneLoop.PauliMatrixRelations)
    (hA : ComplexMatrix2.ConjugationPreservesTraceless)
    (hS : UnitLatticeL2Statement) :
    GaugeKeepsTraceDensity := by
  classical
  intro L _ u hu
  obtain ⟨-, ⟨hCs, -, -, hIs, -, -⟩, hCb, -, -, hIb, -, -⟩ := hS.2 L
  have hu' : ∀ x, u x ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := hu
  refine ⟨preservesTraceDensity_of_pointwiseConj hP hA (vertexPos L) hCs hu' (fun f => ?_)
    fun x => ⟨{x}, ?_⟩, preservesTraceDensity_of_pointwiseConj hP hA (edgePos L) hCb
      (g := fun b : PosEdge L 0 0 => u b.1.initial) (fun b => hu' _)
      (fun f => ?_) fun x => ⟨Finset.univ.image (FullSpace.forwardEdge x), ?_⟩⟩
  · exact Classical.epsilon_spec (exists_coords_of_pointwiseConj hA hCs hu' f)
  · rw [(hIs.1 x).1]
    ext ⟨a, s⟩
    simp [eq_comm]
  · have hval : ∀ (F : PosEdge L 0 0 → ComplexMatrix2) (b : PosEdge L 0 0),
        FullSpace.adjointForm u (formOfPositiveValues F) b.1 =
          ComplexMatrix2.conjugateBy (u b.1.initial) (F b) := by
      intro F b
      simp [FullSpace.adjointForm, FullSpace.extendOddly, formOfPositiveValues, b.2]
    obtain ⟨w, hw⟩ := exists_coords_of_pointwiseConj hA hCb
      (g := fun b : PosEdge L 0 0 => u b.1.initial) (fun b => hu' _) f
    have hex : ∃ w : L2Field (PosEdge L 0 0),
        ∀ b : PosEdge L 0 0, ofCoords w b =
          FullSpace.adjointForm u (formOfPositiveValues (ofCoords f)) b.1 :=
      ⟨w, fun b => by rw [hw, hval]; rfl⟩
    funext b
    have hs := Classical.epsilon_spec hex b
    rw [hval] at hs
    exact hs
  · rw [(hIb.1 x).1]
    ext ⟨a, b⟩
    simp [eq_comm]
end Tower.AbelianFieldDensity.GaugeConjugation
end YangMills.Construction
end
