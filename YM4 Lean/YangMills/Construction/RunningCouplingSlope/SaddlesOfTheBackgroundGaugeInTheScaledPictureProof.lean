import YangMills.Construction.FormOnAFibre.SiteFormsAtAFiniteSideAreEuclidean
import YangMills.Construction.RunningCouplingSlope.GhostOfTheSoftChainIsTheMixedGhostProof
import YangMills.Construction.RunningCouplingSlope.MatrixOfTheBackgroundOperator
import YangMills.Construction.RunningCouplingSlope.SaddleDeterminantInCoordinates
import YangMills.Construction.RunningCouplingSlope.SaddlesOfTheBackgroundGaugeInTheScaledPicture
import Mathlib
set_option autoImplicit false
open Matrix Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace BlockScaling
open Tower PeriodicOperators
section Blocks
variable {I T : Type} [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]
private theorem det_fromBlocks_smul_four (x y x' y' : ℂ) (A : Matrix I I ℂ) (B : Matrix I T ℂ)
    (C : Matrix T I ℂ) (D : Matrix T T ℂ) :
    det (fromBlocks ((x * x') • A) ((x * y') • B) ((y * x') • C) ((y * y') • D)) =
      x ^ Fintype.card I * y ^ Fintype.card T * det (fromBlocks A B C D) *
        (x' ^ Fintype.card I * y' ^ Fintype.card T) := by apply _root_.YangMills.SharedProofs.p77281 <;> assumption
end Blocks
end BlockScaling
open BlockScaling Tower PeriodicOperators in
theorem backgroundGaugeSaddleDeterminants_of_coords
    (hcoord : SaddleDetInOrthonormalCoords)
    (hpauli : PauliCoordsOrthonormal)
    (hhess : BackgroundHessianMatrix)
    (hmaps : BackgroundGaugeMapsInColourCoeffs)
    (hspaces : Tower.FiniteSideFormSpaces)
    (hvert : FormOnAFibre.VertexFunctionsAreEuclidean.Statement) :
    BackgroundGaugeSaddleDeterminants := by
  intro L hL k n hk hn _ _ _ _ _ _ _ _
  classical
  obtain ⟨ΨB, hΨB, hpB⟩ := (hpauli L n k 0 hL hn (Nat.zero_le _)).1
  obtain ⟨ΨT, hΨT, hpT⟩ := (hpauli L n k k hL hn le_rfl).1
  obtain ⟨ΨS, hΨS, hpS⟩ := (hpauli L n k 0 hL hn (Nat.zero_le _)).2
  obtain ⟨ΨY, hΨY, hpY⟩ := (hpauli L n k k hL hn le_rfl).2
  have eucl : ∀ j, j ≤ k → EdgeFormsEuclidean L n k j := by
    intro j hj
    obtain ⟨-, hf, -, c, hc⟩ := hspaces L n k j hL hn hj
    refine ⟨hf, c, fun B B' => ?_⟩
    rw [hc]
    simp
  have hE : EdgeFormsEuclidean L n k 0 ∧ EdgeFormsEuclidean L n k k :=
    ⟨eucl 0 (Nat.zero_le _), eucl k le_rfl⟩
  have hG : VertexFunctionsEuclidean L n k 0 ∧ VertexFunctionsEuclidean L n k k :=
    ⟨hvert L n k 0 hL hn (Nat.zero_le _), hvert L n k k hL hn le_rfl⟩
  have := hE.1.1
  have := hE.2.1
  have := hG.1.1
  have := hG.2.1
  have hLpos : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  set η : ℝ := finestMesh L k with hη
  have heta : 0 < η := zpow_pos hLpos _
  have hetaC : ((η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  have htop : meshAt L k k = 1 := by
    change (L : ℝ) ^ ((k : ℤ) - (k : ℤ)) = 1
    simp
  refine ⟨(η ^ 2) ^ Fintype.card (Fin 3 × PositiveEdge L n k 0),
    (η ^ 2) ^ (Fintype.card (Fin 3 × Vertex L n k 0) + Fintype.card (Fin 3 × Vertex L n k k)),
    by positivity, by positivity, ?_⟩
  have e₃ := hhess L hL k n hk hn
  have e₄ := hmaps L hL k n hk hn
  unfold EventuallyNearIdentity at e₃ e₄ ⊢
  filter_upwards [e₃, e₄] with U f₃ f₄
  obtain ⟨fQ, fR, fRt, fΔ⟩ := f₄
  set p := rescaledOperators L n k U with hp
  have hpη : p.eta = η := rfl
  have hptop : p.coarse = 1 := htop
  refine ⟨?_, ?_⟩
  · have key := hcoord (edgeFormSpace L n k 0) (edgeFormSpace L n k k) _ _ hE.1.2.choose
      hE.2.2.choose ΨB ΨT
      (fun x y => by
        have := hE.1.2.choose_spec x y
        rw [this, hpB]
        simp)
      (fun x y => by
        have := hE.2.2.choose_spec x y
        rw [this, hpT]
        simp)
      (backgroundHessian U 0 0) (iterCovariantDerivLinear L n k U)
      (fun ι ι' => ((η ^ 2 : ℝ) : ℂ) * p.X ι ι') (fun t ι => ((η : ℂ))⁻¹ * p.Q t ι)
      (fun B ι => by
        rw [← hΨB, f₃ B ι]
        exact Finset.sum_congr rfl fun j _ => by rw [hΨB])
      (fun B t => by
        rw [← hΨT, fQ B t]
        exact Finset.sum_congr rfl fun j _ => by rw [hΨB])
    have e : fromBlocks (fun ι ι' => ((η ^ 2 : ℝ) : ℂ) * p.X ι ι')
        (Matrix.transpose fun t ι => ((η : ℂ))⁻¹ * p.Q t ι) (fun t ι => ((η : ℂ))⁻¹ * p.Q t ι) 0 =
        fromBlocks ((((η : ℂ) ^ 2) * 1) • Matrix.of p.X) ((((η : ℂ) ^ 2) * (η : ℂ)) • Matrix.of p.Qt)
          (((η : ℂ)⁻¹ * 1) • Matrix.of p.Q) (((η : ℂ)⁻¹ * (η : ℂ)) • (0 : Matrix _ _ ℂ)) := by
      congr 1
      · ext ι ι'
        simp
      · ext ι t
        have : p.Qt ι t = (((p.coarse ^ 4 / p.eta ^ 4 : ℝ)) : ℂ) * p.Q t ι := rfl
        change ((η : ℂ))⁻¹ * p.Q t ι = (((η : ℂ) ^ 2) * (η : ℂ)) * p.Qt ι t
        rw [this, hptop, hpη]
        push_cast
        field_simp
      · ext t ι
        simp
      · simp
    rw [hessianSaddleDet, saddleDetOnEdgeForms, dif_pos hE]
    refine key.trans ?_
    rw [e, det_fromBlocks_smul_four]
    have hs : Matrix.of p.saddleX =
        fromBlocks (Matrix.of p.X) (Matrix.of p.Qt) (Matrix.of p.Q) 0 := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [RescaledOperators.saddleX, PeriodicOperators.saddleMatrix]
    rw [hs]
    simp only [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heta,
      one_pow, norm_one]
    have h1 : η⁻¹ ^ Fintype.card (Fin 3 × PositiveEdge L n k k) *
        η ^ Fintype.card (Fin 3 × PositiveEdge L n k k) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ heta.ne', one_pow]
    linear_combination ((η ^ 2) ^ Fintype.card (Fin 3 × PositiveEdge L n k 0) *
      ‖det (fromBlocks (Matrix.of p.X) (Matrix.of p.Qt) (Matrix.of p.Q) 0)‖) * h1
  · have key := hcoord (vertexFunctionSpace L n k 0) (vertexFunctionSpace L n k k) _ _
      hG.1.2.choose hG.2.2.choose ΨS ΨY
      (fun x y => by
        have := hG.1.2.choose_spec x y
        rw [this, hpS]
        simp)
      (fun x y => by
        have := hG.2.2.choose_spec x y
        rw [this, hpY]
        simp)
      (covDiffRealTranspose L n k U ∘ₗ covDiffLinear L n k U)
      (iterAverageLinear L n k U)
      (fun x x' => ((η ^ 2 : ℝ) : ℂ) * p.Delta x x') (fun y x => p.R y x)
      (fun l x => by
        rw [← hΨS, LinearMap.comp_apply, fΔ l x]
        exact Finset.sum_congr rfl fun j _ => by rw [hΨS])
      (fun l y => by
        rw [← hΨY, fR l y]
        exact Finset.sum_congr rfl fun j _ => by rw [hΨS])
    have e : fromBlocks (fun x x' => ((η ^ 2 : ℝ) : ℂ) * p.Delta x x')
        (Matrix.transpose fun y x => p.R y x) (fun y x => p.R y x) 0 =
        fromBlocks ((((η : ℂ) ^ 2) * 1) • Matrix.of p.Delta)
          ((((η : ℂ) ^ 2) * ((η : ℂ) ^ 2)) • Matrix.of p.Rt) (((1 : ℂ) * 1) • Matrix.of p.R)
          (((1 : ℂ) * ((η : ℂ) ^ 2)) • (0 : Matrix _ _ ℂ)) := by
      congr 1
      · ext ι ι'
        simp
      · ext x y
        have : p.Rt x y = (((p.coarse ^ 4 / p.eta ^ 4 : ℝ)) : ℂ) * p.R y x := rfl
        change p.R y x = (((η : ℂ) ^ 2) * ((η : ℂ) ^ 2)) * p.Rt x y
        rw [this, hptop, hpη]
        push_cast
        field_simp
      · ext t ι
        simp
      · simp
    rw [ghostSaddleDet, saddleDetOnVertexFunctions, dif_pos hG]
    refine key.trans ?_
    rw [e, det_fromBlocks_smul_four]
    have hs : Matrix.of p.saddleDelta =
        fromBlocks (Matrix.of p.Delta) (Matrix.of p.Rt) (Matrix.of p.R) 0 := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [RescaledOperators.saddleDelta, PeriodicOperators.saddleMatrix]
    rw [hs]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heta,
      one_pow, mul_one, one_mul]
    ring
end YangMills.Construction.RunningCouplingSlope
end
