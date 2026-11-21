import YangMills.Construction.RunningCouplingSlope.MapsOfTheBackgroundGaugeInColours
import YangMills.Construction.RunningCouplingSlope.TheSaddleOfTheWholeChainHasABoundedInverseAtOneProof
import YangMills.Construction.Towers.BlocksOfTheTwoOperatorFunctionsDescend
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace BackgroundGaugeMaps
open Tower PeriodicOperators Tower.RescaledConditions
open Matrices (ComplexMatrix2)
private theorem ofPauliCoeffs_toPauliCoeffs {σ : Type} {l : σ → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) :
    ofPauliCoeffs (toPauliCoeffs l) = l := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofPauliCoeffs_toPauliCoeffs <;> assumption
variable {L n k j : ℕ}
private theorem ofCoeffs_coeffs
    (hX : ∀ e : Edge L n k j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    {A : Edge L n k j → ComplexMatrix2} (hA : A ∈ complexEdgeForms L n k j) :
    (edgePauliCoordinates L n k j).ofCoeffs ((edgePauliCoordinates L n k j).coeffs A) = A := by apply _root_.YangMills.SharedProofs.p21342 <;> assumption
private theorem adjoint_coordinate_eq {V V' I T : Type} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup V'] [Module ℝ V'] [Fintype I] [Fintype T] [DecidableEq I]
    (Ψ : V ≃ₗ[ℝ] (I → ℝ)) (Ψ' : V' ≃ₗ[ℝ] (T → ℝ)) (A : V → V') (A' : V' → V)
    (h : ∀ g f, ∑ i, Ψ (A' g) i * Ψ f i = ∑ t, Ψ' g t * Ψ' (A f) t) (g : V') (i : I) :
    Ψ (A' g) i = ∑ t, Ψ' g t * Ψ' (A (Ψ.symm (Pi.single i 1))) t := by
  have hg := h g (Ψ.symm (Pi.single i 1))
  rw [← hg]
  simp [Pi.single_apply]
private theorem mem_complexEdgeForms_of_mem {A : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ edgeFormSpace L n k j) :
    A ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_complexEdgeForms_of_mem <;> assumption
end BackgroundGaugeMaps
open BackgroundGaugeMaps Tower PeriodicOperators Tower.RescaledConditions
  Tower.RealQuadraticTransposes in
open Matrices (ComplexMatrix2) in
theorem backgroundGaugeMapsInColourCoeffs_holds
    (h₁ : PauliCoordsOrthonormal)
    (h₃ : Tower.OperatorBlocksDescend.BlocksDescend)
    (h₄ : Tower.RealLinearMaps.RealLinearMapsStatement)
    (h₅ : Tower.RealQuadraticTransposes.Statement)
    (h₆ : Tower.RescaledIterRelations) :
    BackgroundGaugeMapsInColourCoeffs := by
  intro L hL k n hk hn _ _ _ _
  classical
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  obtain ⟨ΨB, hΨB, hpB⟩ := (h₁ L n (i + 1) 0 hL hn (Nat.zero_le _)).1
  obtain ⟨ΨT, hΨT, hpT⟩ := (h₁ L n (i + 1) (i + 1) hL hn le_rfl).1
  obtain ⟨ΨS, hΨS, hpS⟩ := (h₁ L n (i + 1) 0 hL hn (Nat.zero_le _)).2
  obtain ⟨ΨY, hΨY, hpY⟩ := (h₁ L n (i + 1) (i + 1) hL hn le_rfl).2
  have hstep := ((h₄ L n (i + 1) hL hn hk).1 i (Nat.lt_succ_self i))
  have htow := (h₄ L n (i + 1) hL hn hk).2
  have e₂ := h₃ L hL (i + 1) hk n hn
  obtain ⟨hdt, e₃⟩ := h₅ L n (i + 1) hL hn hk
  have e₄ := hstep.iterCovariantDeriv_isLinear
  have e₅ := hstep.iterAdjointCubeAverage_isLinear
  unfold EventuallyNearIdentity at e₂ e₃ e₄ e₅ ⊢
  filter_upwards [e₂, e₃, e₄, e₅, self_mem_nhdsWithin] with U f₂ f₃ f₄ f₅ hUc
  obtain ⟨hsmall, -⟩ := f₂
  obtain ⟨-, hTr, -⟩ := f₃
  have hrel := h₆ L hL (i + 1) hk n hn U hsmall
  set p := rescaledOperators L n (i + 1) U with hp
  have hLpos : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  have heta : 0 < p.eta := zpow_pos hLpos _
  have hetaC : ((p.eta : ℝ) : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  have hcoarse : p.coarse = 1 := by
    change (L : ℝ) ^ (((i + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ)) = 1
    simp
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hX0 : ∀ e : Edge L n (i + 1) 0,
      Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented := fun e =>
    PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) e
  have vM : ∀ A : edgeFormSpace L n (i + 1) 0,
      (iterCovariantDerivLinear L n (i + 1) U A : Edge L n (i + 1) (i + 1) → ComplexMatrix2) =
        iterCovariantDeriv L n (i + 1) U (i + 1) A :=
    Classical.epsilon_spec
      (p := fun T : edgeFormSpace L n (i + 1) 0 →ₗ[ℝ] edgeFormSpace L n (i + 1) (i + 1) =>
        ∀ x : edgeFormSpace L n (i + 1) 0, (T x : Edge L n (i + 1) (i + 1) → ComplexMatrix2) =
          iterCovariantDeriv L n (i + 1) U (i + 1) x) f₄
  have vR : ∀ l : vertexFunctionSpace L n (i + 1) 0,
      (iterAverageLinear L n (i + 1) U l : Vertex L n (i + 1) (i + 1) → ComplexMatrix2) =
        iterAdjointCubeAverage L n (i + 1) U (i + 1) l :=
    Classical.epsilon_spec
      (p := fun T : vertexFunctionSpace L n (i + 1) 0 →ₗ[ℝ]
          vertexFunctionSpace L n (i + 1) (i + 1) =>
        ∀ x : vertexFunctionSpace L n (i + 1) 0,
          (T x : Vertex L n (i + 1) (i + 1) → ComplexMatrix2) =
            iterAdjointCubeAverage L n (i + 1) U (i + 1) x) f₅
  obtain ⟨T₀, hT₀⟩ := htow.covDiff_isLinear 0 (Nat.zero_le _) U hUc
  have vD : ∀ l : vertexFunctionSpace L n (i + 1) 0,
      (covDiffLinear L n (i + 1) U l : Edge L n (i + 1) 0 → ComplexMatrix2) = covDiff U l :=
    Classical.epsilon_spec
      (p := fun T : vertexFunctionSpace L n (i + 1) 0 →ₗ[ℝ] edgeFormSpace L n (i + 1) 0 =>
        ∀ x : vertexFunctionSpace L n (i + 1) 0,
          (T x : Edge L n (i + 1) 0 → ComplexMatrix2) = covDiff U x)
      ⟨T₀, hT₀⟩
  have hsum : ∀ {J : Type} [Fintype J] [DecidableEq J] (f : J → ℂ) (j : J),
      ∑ x, f x * (((Pi.single j (1 : ℝ) : J → ℝ) x : ℝ) : ℂ) = f j := by
    intro J _ _ f j
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  have cD : ∀ (l : vertexFunctionSpace L n (i + 1) 0) e,
      ((ΨB (covDiffLinear L n (i + 1) U l) e : ℝ) : ℂ) =
        ((p.eta : ℝ) : ℂ) * ∑ x, p.D e x * ((ΨS l x : ℝ) : ℂ) := by
    intro l e
    have g := congrFun
      (hrel.D_represents (toPauliCoeffs (l : Vertex L n (i + 1) 0 → ComplexMatrix2))).2 e
    have hl : ∀ x, (l : Vertex L n (i + 1) 0 → ComplexMatrix2) x ∈ ComplexMatrix2.traceless :=
      fun x => (l.2 x (Set.mem_univ x)).2
    change applyKernel p.D (toPauliCoeffs (l : Vertex L n (i + 1) 0 → ComplexMatrix2)) e =
      toPauliCoeffs (restrictToPositiveEdges (p.eta⁻¹ • covDiff U
        (ofPauliCoeffs (toPauliCoeffs (l : Vertex L n (i + 1) 0 → ComplexMatrix2))))) e at g
    rw [ofPauliCoeffs_toPauliCoeffs hl, ← vD l] at g
    have hsmul : p.eta⁻¹ • (covDiffLinear L n (i + 1) U l : Edge L n (i + 1) 0 → ComplexMatrix2) =
        ((p.eta⁻¹ • covDiffLinear L n (i + 1) U l : edgeFormSpace L n (i + 1) 0) :
          Edge L n (i + 1) 0 → ComplexMatrix2) := rfl
    rw [hsmul, hΨB, map_smul] at g
    simp only [applyKernel, tsum_fintype, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      Complex.ofReal_inv] at g
    simp only [hΨS] at g
    rw [g]
    field_simp
  have cR : ∀ (l : vertexFunctionSpace L n (i + 1) 0) y,
      toPauliCoeffs (iterAverageLinear L n (i + 1) U l :
          Vertex L n (i + 1) (i + 1) → ComplexMatrix2) y =
        ∑ x, p.R y x * toPauliCoeffs (l : Vertex L n (i + 1) 0 → ComplexMatrix2) x := by
    intro l y
    have g := congrFun
      (hrel.R_represents (toPauliCoeffs (l : Vertex L n (i + 1) 0 → ComplexMatrix2))).2 y
    have hl : ∀ x, (l : Vertex L n (i + 1) 0 → ComplexMatrix2) x ∈ ComplexMatrix2.traceless :=
      fun x => (l.2 x (Set.mem_univ x)).2
    change applyKernel p.R (toPauliCoeffs (l : Vertex L n (i + 1) 0 → ComplexMatrix2)) y =
      toPauliCoeffs (iterAdjointCubeAverage L n (i + 1) U (i + 1)
        (ofPauliCoeffs (toPauliCoeffs (l : Vertex L n (i + 1) 0 → ComplexMatrix2)))) y at g
    rw [ofPauliCoeffs_toPauliCoeffs hl, ← vR l] at g
    simp only [applyKernel, tsum_fintype] at g
    exact g.symm
  refine ⟨fun A t => ?_, cR, fun g x => ?_, fun l x => ?_⟩
  · have g := congrFun (hrel.Q_represents (toPauliCoeffs (restrictToPositiveEdges
      (A : Edge L n (i + 1) 0 → ComplexMatrix2)))).2 t
    change applyKernel p.Q (toPauliCoeffs (restrictToPositiveEdges
        (A : Edge L n (i + 1) 0 → ComplexMatrix2))) t =
      toPauliCoeffs (restrictToPositiveEdges (p.eta •
        iterCovariantDeriv L n (i + 1) U (i + 1) ((edgePauliCoordinates L n (i + 1) 0).ofCoeffs
          ((edgePauliCoordinates L n (i + 1) 0).coeffs (A : Edge L n (i + 1) 0 → ComplexMatrix2))))) t at g
    rw [ofCoeffs_coeffs hX0 (mem_complexEdgeForms_of_mem A.2), ← vM A] at g
    have hsmul : p.eta • (iterCovariantDerivLinear L n (i + 1) U A :
        Edge L n (i + 1) (i + 1) → ComplexMatrix2) =
        ((p.eta • iterCovariantDerivLinear L n (i + 1) U A : edgeFormSpace L n (i + 1) (i + 1)) :
          Edge L n (i + 1) (i + 1) → ComplexMatrix2) := rfl
    rw [hsmul, hΨT, map_smul] at g
    simp only [applyKernel, tsum_fintype, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul] at g
    rw [hΨT]
    have hη : finestMesh L (i + 1) = p.eta := rfl
    rw [hη]
    simp only [mul_assoc]
    rw [← Finset.mul_sum]
    change _ = ((p.eta : ℂ))⁻¹ * ∑ ι, p.Q t ι * toPauliCoeffs (restrictToPositiveEdges
      (A : Edge L n (i + 1) 0 → ComplexMatrix2)) ι
    rw [show (∑ ι, p.Q t ι * toPauliCoeffs (restrictToPositiveEdges
      (A : Edge L n (i + 1) 0 → ComplexMatrix2)) ι) = _ from g]
    field_simp
  · obtain ⟨T, -, -, -, hadj⟩ := hTr.average_transpose
    have hco := adjoint_coordinate_eq ΨS ΨY (iterAverageLinear L n (i + 1) U)
      (iterAverageRealTranspose L n (i + 1) U) (fun g f => by
        have hgf := hadj g f
        change traceFinsumPairing
          (iterAverageRealTranspose L n (i + 1) U g : Vertex L n (i + 1) 0 → ComplexMatrix2)
          (f : Vertex L n (i + 1) 0 → ComplexMatrix2) =
          traceFinsumPairing (g : Vertex L n (i + 1) (i + 1) → ComplexMatrix2)
          (iterAverageLinear L n (i + 1) U f : Vertex L n (i + 1) (i + 1) → ComplexMatrix2) at hgf
        rw [hpS, hpY] at hgf
        exact Complex.ofReal_injective hgf) g x
    rw [hΨS, hco]
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    have r := cR (ΨS.symm (Pi.single x 1)) y
    simp only [hΨS, hΨY, LinearEquiv.apply_symm_apply] at r
    rw [hsum] at r
    rw [r, hΨY]
    have hRt : p.Rt x y = (((p.coarse ^ 4 / p.eta ^ 4 : ℝ)) : ℂ) * p.R y x := rfl
    have hη : finestMesh L (i + 1) = p.eta := rfl
    rw [hRt, hcoarse, hη]
    push_cast
    field_simp
  · obtain ⟨T, -, -, -, hadj⟩ := hdt 0 (Nat.zero_le _) U hUc
    have hco := adjoint_coordinate_eq ΨS ΨB (covDiffLinear L n (i + 1) U)
      (covDiffRealTranspose L n (i + 1) U) (fun g f => by
        have hgf := hadj g f
        change traceFinsumPairing
          (covDiffRealTranspose L n (i + 1) U g : Vertex L n (i + 1) 0 → ComplexMatrix2)
          (f : Vertex L n (i + 1) 0 → ComplexMatrix2) =
          edgeFormPairing (g : Edge L n (i + 1) 0 → ComplexMatrix2)
          (covDiffLinear L n (i + 1) U f : Edge L n (i + 1) 0 → ComplexMatrix2) at hgf
        rw [hpS, hpB] at hgf
        exact Complex.ofReal_injective hgf) (covDiffLinear L n (i + 1) U l) x
    rw [hΨS, hco]
    push_cast
    have hterm : ∀ e,
        ((ΨB (covDiffLinear L n (i + 1) U (ΨS.symm (Pi.single x 1))) e : ℝ) : ℂ) =
          ((p.eta : ℝ) : ℂ) * p.D e x := by
      intro e
      rw [cD]
      simp only [LinearEquiv.apply_symm_apply]
      rw [hsum]
    have hDelta : ∀ x', p.Delta x x' = ∑ e, p.D e x * p.D e x' := by
      intro x'
      change ∑' e, p.Dt x e * p.D e x' = _
      rw [tsum_fintype]
      refine Finset.sum_congr rfl fun e _ => ?_
      have hDt : p.Dt x e = (((p.eta ^ 4 / p.eta ^ 4 : ℝ)) : ℂ) * p.D e x := rfl
      rw [hDt, div_self (pow_ne_zero 4 heta.ne')]
      simp
    have hη : finestMesh L (i + 1) = p.eta := rfl
    rw [hη]
    simp only [hterm, cD, hDelta, hΨS]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    push_cast
    ring
end YangMills.Construction.RunningCouplingSlope
end
