import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnASide
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAsAKernel
import YangMills.Construction.Towers.TransposesOfTheCovariantDifferenceAndOfTheDifferences
import YangMills.Construction.Towers.TransposesOfTheIteratedAveragesOfTheScaledPictureOnASideProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.ComplexFieldRescaledRelations
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.RescaledConditions
open YangMills.Construction.Tower.HessianKernel (IsSymmBilinearOn)
open YangMills.Construction.Tower.ScalarMultipleKernels (CoeffsRealHomogeneous)
section KernelAction
variable {I J : Type}
theorem applyKernel_smul (K : KernelMatrix I J) (w : ℂ) (g : I → ℂ) :
    applyKernel K (w • g) = w • applyKernel K g := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_smul <;> assumption
theorem applySummable_add_and_applyKernel_add {K K' : KernelMatrix I J} {g : I → ℂ}
    (hK : ApplySummable K g) (hK' : ApplySummable K' g) :
    ApplySummable (K + K') g ∧ applyKernel (K + K') g = applyKernel K g + applyKernel K' g := by
  refine ⟨fun j => ?_, ?_⟩
  · have s : Summable fun i => ‖K j i * g i‖ := hK j
    have s' : Summable fun i => ‖K' j i * g i‖ := hK' j
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) (s.add s')
    simp only [Pi.add_apply, add_mul]
    exact norm_add_le _ _
  · funext j
    have s : Summable fun i => ‖K j i * g i‖ := hK j
    have s' : Summable fun i => ‖K' j i * g i‖ := hK' j
    simp only [applyKernel, Pi.add_apply, add_mul]
    exact Summable.tsum_add s.of_norm s'.of_norm
theorem represents_smul {K : KernelMatrix I J} {F : (I → ℂ) → J → ℂ} (hK : Represents K F)
    (w : ℂ) : Represents (w • K) (w • F) := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.represents_smul <;> assumption
end KernelAction
theorem generalRelations_of_kernels (ρ β : PauliComponentsOfSymmetricKernel) {S E : Type}
    (q : RescaledOperators ρ.Place β.Place S E)
    (Dop : (ρ.space.index → Matrices.ComplexMatrix2) → β.space.index → Matrices.ComplexMatrix2)
    (Hop : (β.space.index → Matrices.ComplexMatrix2) → β.space.index → Matrices.ComplexMatrix2)
    (hComp : PeriodicOperators.RowFiniteKernels.ApplyComp)
    (hDop : PauliComponentsOfSymmetricKernel.HasLocalKernel ρ β Dop)
    (hDeq : q.D = (q.eta : ℂ)⁻¹ • PauliComponentsOfSymmetricKernel.kernel ρ β Dop)
    (hDteq : q.Dt = (q.eta : ℂ)⁻¹ • swapKernel (PauliComponentsOfSymmetricKernel.kernel ρ β Dop))
    (hHrep : Represents q.H (((q.eta : ℂ) ^ 2)⁻¹ • β.mapOnCoeffs β Hop))
    (ρInv : ∀ v ∈ ρ.space.complexSubmodule, ρ.ofCoeffs (ρ.coeffs v) = v)
    (ρMem : ∀ c, ρ.ofCoeffs c ∈ ρ.space.complexSubmodule)
    (βInv : ∀ W ∈ β.space.complexSubmodule, β.ofCoeffs (β.coeffs W) = W)
    (βMem : ∀ c, β.ofCoeffs c ∈ β.space.complexSubmodule)
    (βAdd : ∀ V ∈ β.space.complexSubmodule, ∀ W ∈ β.space.complexSubmodule,
      β.coeffs (V + W) = β.coeffs V + β.coeffs W)
    (hDmem : ∀ v ∈ ρ.space.complexSubmodule, Dop v ∈ β.space.complexSubmodule)
    (hTmem : ∀ W ∈ β.space.complexSubmodule,
      PairedFunctionSpace.transposeOfValues ρ.space β.space Dop W ∈ ρ.space.complexSubmodule)
    (hHmem : ∀ W ∈ β.space.complexSubmodule, Hop W ∈ β.space.complexSubmodule) :
    GeneralRelations ρ β q Dop Hop := by
  have rowD : RowFinite q.D := by
    rw [hDeq]
    exact hDop.smul_row_finite _
  have rowDt : RowFinite q.Dt := by
    rw [hDteq]
    exact hDop.smul_swap_row_finite _
  have repD : Represents q.D ((q.eta : ℂ)⁻¹ • ρ.mapOnCoeffs β Dop) := by
    rw [hDeq]
    exact hDop.smul_represents _
  have repDt : Represents q.Dt ((q.eta : ℂ)⁻¹ • ρ.transposeOnCoeffs β Dop) := by
    rw [hDteq]
    exact hDop.smul_swap_represents _
  have invSq : ((q.eta : ℂ) ^ 2)⁻¹ = (q.eta : ℂ)⁻¹ * (q.eta : ℂ)⁻¹ := by rw [sq, mul_inv]
  have compDtD := (hComp _ _ q.D rowD).2 _ q.Dt rowDt
  have compDDt := (hComp _ _ q.Dt rowDt).2 _ q.D rowD
  refine ⟨repDt, hHrep, ?_, ?_, compDtD.1, compDDt.1⟩
  · intro g
    obtain ⟨a₁, -, a₃⟩ := compDtD.2.2 g
    refine ⟨a₁, ?_⟩
    have hv := ρMem g
    have e₁ : applyKernel q.D g = (q.eta : ℂ)⁻¹ • β.coeffs (Dop (ρ.ofCoeffs g)) := (repD g).2
    have e₂ : applyKernel q.Dt (β.coeffs (Dop (ρ.ofCoeffs g))) = (q.eta : ℂ)⁻¹ •
        ρ.coeffs (PairedFunctionSpace.transposeOfValues ρ.space β.space Dop
          (Dop (ρ.ofCoeffs g))) := by
      refine (repDt _).2.trans ?_
      show (q.eta : ℂ)⁻¹ • ρ.coeffs (PairedFunctionSpace.transposeOfValues ρ.space β.space Dop
        (β.ofCoeffs (β.coeffs (Dop (ρ.ofCoeffs g))))) = _
      rw [βInv _ (hDmem _ hv)]
    show applyKernel (compKernel q.Dt q.D) g = ((q.eta : ℂ) ^ 2)⁻¹ •
      ρ.coeffs (PairedFunctionSpace.transposeOfValues ρ.space β.space Dop (Dop (ρ.ofCoeffs g)))
    rw [a₃, e₁, applyKernel_smul, e₂, invSq, mul_smul]
  · intro g
    obtain ⟨a₁, -, a₃⟩ := compDDt.2.2 g
    obtain ⟨s₁, s₂⟩ := applySummable_add_and_applyKernel_add (hHrep g).1 a₁
    refine ⟨s₁, ?_⟩
    have hW := βMem g
    have hT := hTmem _ hW
    have e₁ : applyKernel q.Dt g = (q.eta : ℂ)⁻¹ •
        ρ.coeffs (PairedFunctionSpace.transposeOfValues ρ.space β.space Dop (β.ofCoeffs g)) :=
      (repDt g).2
    have e₂ : applyKernel q.D
        (ρ.coeffs (PairedFunctionSpace.transposeOfValues ρ.space β.space Dop (β.ofCoeffs g))) =
        (q.eta : ℂ)⁻¹ • β.coeffs
          (Dop (PairedFunctionSpace.transposeOfValues ρ.space β.space Dop (β.ofCoeffs g))) := by
      refine (repD _).2.trans ?_
      show (q.eta : ℂ)⁻¹ • β.coeffs (Dop (ρ.ofCoeffs (ρ.coeffs
        (PairedFunctionSpace.transposeOfValues ρ.space β.space Dop (β.ofCoeffs g))))) = _
      rw [ρInv _ hT]
    have e₃ : applyKernel q.H g = ((q.eta : ℂ) ^ 2)⁻¹ • β.coeffs (Hop (β.ofCoeffs g)) :=
      (hHrep g).2
    show applyKernel (q.H + compKernel q.D q.Dt) g = ((q.eta : ℂ) ^ 2)⁻¹ • β.coeffs
      (Hop (β.ofCoeffs g) +
        Dop (PairedFunctionSpace.transposeOfValues ρ.space β.space Dop (β.ofCoeffs g)))
    rw [s₂, a₃, e₁, applyKernel_smul, e₂, e₃, βAdd _ (hHmem _ hW) _ (hDmem _ hT), invSq, smul_add,
      mul_smul, mul_smul]
theorem pauliFamily_mem_traceless (a : Fin 3) :
    Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem sum_smul_pauliFamily_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem sum_pauliCoeff_smul_pauliFamily {M : Matrices.ComplexMatrix2}
    (hM : M ∈ Matrices.ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a M • Matrices.ComplexMatrix2.pauliFamily a = M := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_add {M M' : Matrices.ComplexMatrix2}
    (hM : M ∈ Matrices.ComplexMatrix2.traceless) (hM' : M' ∈ Matrices.ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a (M + M') = pauliCoeff a M + pauliCoeff a M' := by
  unfold pauliCoeff
  rw [dif_pos (Matrices.ComplexMatrix2.traceless.add_mem hM hM'), dif_pos hM, dif_pos hM']
  have e : (⟨M + M', Matrices.ComplexMatrix2.traceless.add_mem hM hM'⟩ :
      Matrices.ComplexMatrix2.traceless) = ⟨M, hM⟩ + ⟨M', hM'⟩ := rfl
  rw [e, map_add]
  rfl
theorem pauliCoeff_real_smul (t : ℝ) (a : Fin 3) (M : Matrices.ComplexMatrix2) :
    pauliCoeff a (t • M) = (t : ℂ) * pauliCoeff a M := by apply _root_.YangMills.Construction.Tower.IterTransposesOnTorus.pauliCoeff_real_smul <;> assumption
theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
theorem symmBilinear_real_smul_smul {α : Type} {𝒮 : Set (α → Matrices.ComplexMatrix2)}
    {Φ : (α → Matrices.ComplexMatrix2) → (α → Matrices.ComplexMatrix2) → ℂ}
    (hΦ : IsSymmBilinearOn 𝒮 Φ) (h0 : (0 : α → Matrices.ComplexMatrix2) ∈ 𝒮) (t : ℝ)
    {V W : α → Matrices.ComplexMatrix2} (hV : V ∈ 𝒮) (hW : W ∈ 𝒮) (htW : (t : ℂ) • W ∈ 𝒮) :
    Φ (t • V) (t • W) = (t : ℂ) * ((t : ℂ) * Φ V W) := by
  have zl : ∀ Z ∈ 𝒮, Φ 0 Z = 0 := fun Z hZ => by
    have u := (hΦ 1 0 h0 0 h0 Z hZ).1
    simp only [smul_zero, add_zero, one_mul] at u
    linear_combination (-1 : ℂ) * u
  have zr : ∀ Z ∈ 𝒮, Φ Z 0 = 0 := fun Z hZ =>
    ((hΦ 0 0 h0 0 h0 Z hZ).2.2).symm.trans (zl Z hZ)
  have s : ∀ X : α → Matrices.ComplexMatrix2, t • X = (t : ℂ) • X := fun X => by
    funext b
    ext i j
    simp
  have a₁ := (hΦ (t : ℂ) V hV 0 h0 _ htW).1
  have a₂ := (hΦ (t : ℂ) W hW 0 h0 V hV).2.1
  rw [add_zero, zl _ htW, add_zero] at a₁
  rw [add_zero, zr _ hV, add_zero] at a₂
  rw [s, s, a₁, a₂]
theorem finestMesh_ne_zero {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    finestMesh L k ≠ 0 := by
  have h0 : (L : ℝ) ≠ 0 := by
    have := hL.2
    have : L ≠ 0 := by omega
    exact_mod_cast this
  exact zpow_ne_zero _ h0
section FiniteSide
variable {L m k : ℕ}
theorem edgePauliCoordinates_ofCoeffs_eq (c : Fin 3 × PositiveEdge L m k 0 → ℂ) :
    (edgePauliCoordinates L m k 0).ofCoeffs c = open Classical in
      extendOddly fun e => if h : e.IsPositivelyOriented then ofPauliCoeffs c ⟨e, h⟩ else 0 := rfl
theorem restrictToPositiveEdges_ofCoeffs (c : Fin 3 × PositiveEdge L m k 0 → ℂ) :
    restrictToPositiveEdges ((edgePauliCoordinates L m k 0).ofCoeffs c) = ofPauliCoeffs c := by
  classical
  funext e
  exact show (edgePauliCoordinates L m k 0).ofCoeffs c e.1 = ofPauliCoeffs c e from by
    rw [edgePauliCoordinates_ofCoeffs_eq]
    simp only [extendOddly, if_pos e.2, dif_pos e.2]
theorem edgePauliCoordinates_ofCoeffs_mem
    (hx : ∀ e : Edge L m k 0, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    (c : Fin 3 × PositiveEdge L m k 0 → ℂ) :
    (edgePauliCoordinates L m k 0).ofCoeffs c ∈ complexEdgeForms L m k 0 := by
  classical
  refine ⟨fun e he => ?_, fun e => ?_⟩
  · have h := congrFun (restrictToPositiveEdges_ofCoeffs c) ⟨e, he⟩
    have h' : (edgePauliCoordinates L m k 0).ofCoeffs c e = ofPauliCoeffs c ⟨e, he⟩ := h
    rw [h']
    exact sum_smul_pauliFamily_mem_traceless fun a => c (a, ⟨e, he⟩)
  · rw [edgePauliCoordinates_ofCoeffs_eq]
    rcases hx e with h | h
    · simp only [extendOddly, if_pos h.1, if_neg h.2]
      rfl
    · simp only [extendOddly, if_pos h.1, if_neg h.2, neg_neg]
theorem edgePauliCoordinates_ofCoeffs_coeffs
    (hx : ∀ e : Edge L m k 0, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    {W : Edge L m k 0 → Matrices.ComplexMatrix2} (hW : W ∈ complexEdgeForms L m k 0) :
    (edgePauliCoordinates L m k 0).ofCoeffs ((edgePauliCoordinates L m k 0).coeffs W) = W := by
  classical
  have hv : ∀ e (he : e.IsPositivelyOriented),
      (edgePauliCoordinates L m k 0).ofCoeffs ((edgePauliCoordinates L m k 0).coeffs W) e = W e := fun e he => by
    have h := congrFun (restrictToPositiveEdges_ofCoeffs ((edgePauliCoordinates L m k 0).coeffs W)) ⟨e, he⟩
    have h' : (edgePauliCoordinates L m k 0).ofCoeffs ((edgePauliCoordinates L m k 0).coeffs W) e =
        ofPauliCoeffs ((edgePauliCoordinates L m k 0).coeffs W) ⟨e, he⟩ := h
    rw [h']
    exact sum_pauliCoeff_smul_pauliFamily (hW.1 e he)
  funext e
  by_cases he : e.IsPositivelyOriented
  · exact hv e he
  · have hr : e.opposite.IsPositivelyOriented := by
      rcases hx e with h | h
      · exact absurd h.1 he
      · exact h.1
    have hm := edgePauliCoordinates_ofCoeffs_mem hx ((edgePauliCoordinates L m k 0).coeffs W)
    have f₁ := hm.2 e
    have f₂ := hW.2 e
    have f₃ := hv _ hr
    rw [f₁, f₂] at f₃
    exact neg_injective f₃
theorem edgePauliCoordinates_coeffs_add {V W : Edge L m k 0 → Matrices.ComplexMatrix2}
    (hV : V ∈ complexEdgeForms L m k 0) (hW : W ∈ complexEdgeForms L m k 0) :
    (edgePauliCoordinates L m k 0).coeffs (V + W) =
      (edgePauliCoordinates L m k 0).coeffs V + (edgePauliCoordinates L m k 0).coeffs W :=
  funext fun i => pauliCoeff_add (hV.1 _ i.2.2) (hW.1 _ i.2.2) i.1
theorem edgePauliCoordinates_coeffsRealHomogeneous : CoeffsRealHomogeneous (edgePauliCoordinates L m k 0) :=
  fun t _ => funext fun i => pauliCoeff_real_smul t i.1 _
theorem basisForm_mem
    (hx : ∀ e : Edge L m k 0, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    (a : Fin 3) (e : PositiveEdge L m k 0) :
    basisForm a e ∈ complexEdgeForms L m k 0 := by
  classical
  unfold basisForm
  refine ⟨fun e' he' => ?_, fun e' => ?_⟩
  · simp only [extendOddly, if_pos he']
    split_ifs
    · exact pauliFamily_mem_traceless a
    · exact Matrices.ComplexMatrix2.traceless.zero_mem
  · rcases hx e' with h | h
    · simp only [extendOddly, if_pos h.1, if_neg h.2]
      rfl
    · simp only [extendOddly, if_pos h.1, if_neg h.2, neg_neg]
theorem complexHessianKernel_represents (U : Edge L m k 0 → Matrices.ComplexMatrix2)
    (standingConstraints : RowFinite (complexHessianKernel U)) :
    Represents (complexHessianKernel U)
      ((edgePauliCoordinates L m k 0).mapOnCoeffs (edgePauliCoordinates L m k 0) (complexHessianOperator U)) := by
  classical
  intro g
  refine ⟨fun j => ?_, ?_⟩
  · refine summable_of_hasFiniteSupport ((standingConstraints j).subset ?_)
    intro i hi hz
    apply hi
    have hz' : complexHessianKernel U j i = 0 := by simpa using hz
    simp [hz']
  · have e : toPauliCoeffs (restrictToPositiveEdges ((edgePauliCoordinates L m k 0).ofCoeffs g)) = g := by
      rw [restrictToPositiveEdges_ofCoeffs]
      exact toPauliCoeffs_ofPauliCoeffs g
    have v : ∀ W : Edge L m k 0 → Matrices.ComplexMatrix2,
        restrictToPositiveEdges (complexHessianOperator U W) =
        ofPauliCoeffs (applyKernel (complexHessianKernel U)
          (toPauliCoeffs (restrictToPositiveEdges W))) := fun W => by
      funext b
      exact show complexHessianOperator U W b.1 = ofPauliCoeffs (applyKernel
          (complexHessianKernel U) (toPauliCoeffs (restrictToPositiveEdges W))) b from by
        unfold complexHessianOperator
        simp only [extendOddly, if_pos b.2, dif_pos b.2]
    have w := v ((edgePauliCoordinates L m k 0).ofCoeffs g)
    rw [e] at w
    exact ((congrArg toPauliCoeffs w).trans (toPauliCoeffs_ofPauliCoeffs _)).symm
end FiniteSide
theorem statement_holds (h₀ : ScalarMultipleKernels.Statement)
    (h₁ : ThreeMapKernels.Claim)
    (h₂ : PeriodicOperators.RowFiniteKernels.Claim)
    (h₃ : HessianKernel.KernelProperties)
    (h₄ : CovDiffTransposes.Claim)
    (h₅ : PeriodicLattice.BondEndpointsOrientation.Statement) : Statement := by
  classical
  intro L hL k hk m hm U hU
  have hη := finestMesh_ne_zero hL k
  have hηc : (finestMesh L k : ℂ) ≠ 0 := by exact_mod_cast hη
  have hx : ∀ e : Edge L m k 0, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented :=
    fun e => (h₅ ⟨L, hL, ⟨k, hk⟩, ⟨m, hm⟩⟩ 0 (Nat.zero_le _)).2.2.2 e |>.2.2.2.2.2
  have K3 := (h₁ L hL k hk).1 m hm
  have Uq := (K3.1 0 0 (Nat.zero_le _) (Nat.zero_le _)).2.1
  have hDk := K3.2.1 U hU
  obtain ⟨f₁, f₂⟩ := h₀ (vertexCoordinate (Vertex L m k 0)) (edgePauliCoordinates L m k 0) (covDiff U)
    edgePauliCoordinates_coeffsRealHomogeneous hDk Uq (finestMesh L k)⁻¹ (finestMesh L k) (finestMesh L k)
  obtain ⟨bil, -, standingConstraints, -, -, -⟩ := ((h₃ L hL k 0 (Nat.zero_le _)).1 m hm) U hU
  have C := ((h₄ L hL k 0 (Nat.zero_le _)).1 m hm) U hU
  have expansions' : RowFinite (complexHessianKernel U) := standingConstraints
  have hHeq : (rescaledOperators L m k U).H =
      ((finestMesh L k : ℂ) ^ 2)⁻¹ • complexHessianKernel U := by
    funext j i
    show (((finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) * complexActionHessian U
        (finestMesh L k • basisForm j.1 j.2) (finestMesh L k • basisForm i.1 i.2) =
      ((finestMesh L k : ℂ) ^ 2)⁻¹ * complexActionHessian U
        (basisForm j.1 j.2) (basisForm i.1 i.2)
    rw [symmBilinear_real_smul_smul bil (complexEdgeForms L m k 0).zero_mem (finestMesh L k)
      (basisForm_mem hx j.1 j.2) (basisForm_mem hx i.1 i.2)
      ((complexEdgeForms L m k 0).smul_mem _ (basisForm_mem hx i.1 i.2))]
    push_cast
    field_simp
  have hK := complexHessianKernel_represents U expansions'
  refine generalRelations_of_kernels (vertexCoordinate (Vertex L m k 0)) (edgePauliCoordinates L m k 0)
    (rescaledOperators L m k U) (covDiff U) (complexHessianOperator U) h₂.1 hDk
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact f₁.trans (congrArg (fun c : ℂ => c • PauliComponentsOfSymmetricKernel.kernel
      (vertexCoordinate (Vertex L m k 0)) (edgePauliCoordinates L m k 0) (covDiff U))
      (Complex.ofReal_inv _))
  · have c₂ : (((finestMesh L k)⁻¹ * (finestMesh L k ^ 4 * (finestMesh L k ^ 4)⁻¹) : ℝ) : ℂ) =
        ((finestMesh L k : ℝ) : ℂ)⁻¹ := by
      rw [mul_inv_cancel₀ (pow_ne_zero 4 hη), mul_one, Complex.ofReal_inv]
    exact f₂.trans (congrArg (fun c : ℂ => c • swapKernel (PauliComponentsOfSymmetricKernel.kernel
      (vertexCoordinate (Vertex L m k 0)) (edgePauliCoordinates L m k 0) (covDiff U))) c₂)
  · rw [hHeq]
    exact represents_smul hK _
  · intro v hv
    exact funext fun i => sum_pauliCoeff_smul_pauliFamily (hv i (mem_univ i))
  · intro c i _
    exact sum_smul_pauliFamily_mem_traceless fun a => c (a, i)
  · intro W hW
    exact edgePauliCoordinates_ofCoeffs_coeffs hx hW
  · exact edgePauliCoordinates_ofCoeffs_mem hx
  · intro V hV W hW
    exact edgePauliCoordinates_coeffs_add hV hW
  · intro v hv
    exact (C.transposeComp_mem v hv).1
  · intro W hW
    exact (C.compTranspose_mem W hW).1
  · intro W hW
    exact (C.operator_mem W hW).2.1
end YangMills.Construction.Tower.ComplexFieldRescaledRelations
end
