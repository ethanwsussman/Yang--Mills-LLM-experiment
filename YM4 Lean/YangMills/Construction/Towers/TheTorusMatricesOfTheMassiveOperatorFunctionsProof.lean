import YangMills.Construction.Averaging.AveragingMapRealAnalyticAtSmallRadiiProof
import YangMills.Construction.Towers.CovariantAveragesAsDifferentialsProof
import YangMills.Construction.Towers.DifferencesGiveTheTwoOperatorsAtOneOnTheUnitLatticeProof
import YangMills.Construction.Towers.KernelsOfAFieldAreRealAtRealFieldsProof
import YangMills.Construction.Towers.KernelsOfTheTwoOperatorsAreProductsProof
import YangMills.Construction.Towers.PeriodicExtensionsAndPeriodisation
import YangMills.Construction.Towers.TheTorusMatricesOfTheMassiveOperatorFunctions
import YangMills.Construction.Towers.TheTwoOperatorsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs (quotOperator)
open YangMills.Construction.Tower.Massive (shiftedDetOn restrictToSubmodule)
section Entries
variable {N N' N'' : Type}
theorem applyKernel_indicator [DecidableEq N] (K : N' → N → ℂ) (ι : N) (ι' : N') :
    applyKernel K (fun κ => if κ = ι then 1 else 0) ι' = K ι' ι := by
  unfold applyKernel
  rw [tsum_eq_single ι]
  · simp
  · intro j hj
    simp [hj]
theorem applyKernel_applyKernel_indicator [DecidableEq N] (S : N'' → N' → ℂ) (T : N' → N → ℂ)
    (ι : N) (ι' : N'') :
    applyKernel S (applyKernel T fun κ => if κ = ι then 1 else 0) ι' = compKernel S T ι' ι := by
  have h : applyKernel T (fun κ => if κ = ι then 1 else 0) = fun κ => T κ ι :=
    funext fun κ => applyKernel_indicator T ι κ
  rw [h]
  rfl
theorem applyKernel_compKernel [Finite N] [Finite N'] (S : N'' → N' → ℂ) (T : N' → N → ℂ)
    (f : N → ℂ) :
    applyKernel (compKernel S T) f = applyKernel S (applyKernel T f) := by
  classical
  have := Fintype.ofFinite N
  have := Fintype.ofFinite N'
  funext i
  simp only [applyKernel, compKernel, tsum_fintype, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]
theorem applyKernel_add [Finite N] (S T : N' → N → ℂ) (f : N → ℂ) :
    applyKernel (S + T) f = applyKernel S f + applyKernel T f := by
  classical
  have := Fintype.ofFinite N
  funext i
  simp only [applyKernel, tsum_fintype, Pi.add_apply, add_mul, Finset.sum_add_distrib]
theorem applyKernel_smul_unit [DecidableEq N] (z : ℂ) (f : N → ℂ) :
    applyKernel (z • fun i j : N => if i = j then (1 : ℂ) else 0) f = z • f := by
  funext i
  unfold applyKernel
  rw [tsum_eq_single i]
  · simp
  · intro j hj
    simp [Ne.symm hj]
theorem det_matrix_eq_det_of_real_coords {V P : Type} [AddCommGroup V] [Module ℝ V] [Fintype P]
    [DecidableEq P] (e : V ≃ₗ[ℝ] (P → ℝ)) (A : V →ₗ[ℝ] V) (M : P → P → ℂ)
    (h : ∀ (f : V) (i : P), applyKernel M (fun j => (e f j : ℂ)) i = (e (A f) i : ℂ)) :
    Matrix.det (Matrix.of M) = ((LinearMap.det A : ℝ) : ℂ) := by
  set g : (P → ℝ) →ₗ[ℝ] (P → ℝ) := e.toLinearMap ∘ₗ A ∘ₗ e.symm.toLinearMap with hg
  have hdet : LinearMap.det g = LinearMap.det A := LinearMap.det_conj A e
  have hent : Matrix.of M = (LinearMap.toMatrix' g).map Complex.ofRealHom := by
    ext i j
    have h₁ := h (e.symm fun k => if k = j then 1 else 0) i
    rw [LinearEquiv.apply_symm_apply] at h₁
    have h₂ : (fun k : P => (((if k = j then 1 else 0 : ℝ)) : ℂ)) =
        fun k => if k = j then 1 else 0 := by
      funext k
      split_ifs <;> simp
    rw [h₂, applyKernel_indicator] at h₁
    have h₃ : (Pi.single j 1 : P → ℝ) = fun k => if k = j then 1 else 0 := by
      funext k
      simp [Pi.single_apply]
    simp only [Matrix.of_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, hg,
      LinearMap.comp_apply, LinearEquiv.coe_coe, Complex.ofRealHom_eq_coe, h₃]
    exact h₁
  rw [hent, ← hdet, ← LinearMap.det_toMatrix' g]
  exact (RingHom.map_det Complex.ofRealHom _).symm
end Entries
section Classes
variable {P : Type}
theorem exists_quotEquiv (I : PeriodicData) (s : ℕ) (q : I.Carrier → P)
    (hs : Function.Surjective q)
    (hq : ∀ ι ι', q ι = q ι' ↔ ∃ m : Fin 4 → ℤ, ι' = I.translate (s • m) ι) :
    ∃ φ : I.QuotMod s ≃ P, ∀ ι, φ (I.mkQuot s ι) = q ι := by
  let f : I.QuotMod s → P := Quot.lift q fun a c h => (hq a c).2 h
  have hf : Function.Bijective f := by
    refine ⟨fun c c' => ?_, fun p => ?_⟩
    · induction c using Quot.ind with
      | mk a =>
        induction c' using Quot.ind with
        | mk a' =>
          intro h
          exact Quot.sound ((hq a a').1 h)
    · obtain ⟨ι, rfl⟩ := hs p
      exact ⟨I.mkQuot s ι, rfl⟩
  exact ⟨Equiv.ofBijective f hf, fun _ => rfl⟩
theorem descendMatrix_eq_of_factors (I : PeriodicData) (s : ℕ) {q : I.Carrier → P}
    {φ : I.QuotMod s ≃ P} (hφ : ∀ ι, φ (I.mkQuot s ι) = q ι) {F : I.Carrier → I.Carrier → ℂ}
    {M : P → P → ℂ} (hF : ∀ ι' ι, F ι' ι = M (q ι') (q ι)) (c' c : I.QuotMod s) :
    descendMatrix I I s F c' c = M (φ c') (φ c) := by
  have hex : ∃ w, ∀ ι' ι, I.mkQuot s ι' = c' → I.mkQuot s ι = c → F ι' ι = w :=
    ⟨M (φ c') (φ c), fun ι' ι h' h => by rw [hF, ← hφ, ← hφ, h', h]⟩
  have hspec := Classical.epsilon_spec hex
  obtain ⟨ι', rfl⟩ : ∃ ι', I.mkQuot s ι' = c' := Quot.exists_rep c'
  obtain ⟨ι, rfl⟩ : ∃ ι, I.mkQuot s ι = c := Quot.exists_rep c
  have := hspec ι' ι rfl rfl
  rw [hF, ← hφ, ← hφ] at this
  exact this.symm
theorem det_descendMatrix_of_factors [Finite P] (I : PeriodicData) (s : ℕ) {q : I.Carrier → P}
    (hs : Function.Surjective q)
    (hq : ∀ ι ι', q ι = q ι' ↔ ∃ m : Fin 4 → ℤ, ι' = I.translate (s • m) ι)
    {F : I.Carrier → I.Carrier → ℂ} {M : P → P → ℂ} (hF : ∀ ι' ι, F ι' ι = M (q ι') (q ι))
    {V : Type} [AddCommGroup V] [Module ℝ V] (e : V ≃ₗ[ℝ] (P → ℝ)) (A : V →ₗ[ℝ] V)
    (h : ∀ (f : V) (i : P), applyKernel M (fun j => (e f j : ℂ)) i = (e (A f) i : ℂ)) :
    LinearMap.det (linearMapOfEntries (descendMatrix I I s F)) = ((LinearMap.det A : ℝ) : ℂ) := by
  classical
  obtain ⟨φ, hφ⟩ := exists_quotEquiv I s q hs hq
  have := Fintype.ofFinite P
  have : Finite (I.QuotMod s) := Finite.of_equiv P φ.symm
  have := Fintype.ofFinite (I.QuotMod s)
  have e₁ : linearMapOfEntries (descendMatrix I I s F) =
      Matrix.toLin' (Matrix.of (descendMatrix I I s F)) := by
    refine LinearMap.ext fun g => ?_
    rw [linearMapOfEntries_eq_applyKernel]
    funext c'
    simp [applyKernel, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  have e₂ : Matrix.of (descendMatrix I I s F) = (Matrix.of M).submatrix φ φ := by
    ext c' c
    exact descendMatrix_eq_of_factors I s hφ hF c' c
  rw [e₁, LinearMap.det_toLin', e₂, Matrix.det_submatrix_equiv_self]
  exact det_matrix_eq_det_of_real_coords e A M h
end Classes
section Coefficients
theorem traceless_of_hermitianTraceless {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) : X ∈ ComplexMatrix2.traceless := hX.2
theorem pauli_sum_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_sum (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ c, x c • ComplexMatrix2.pauliFamily c) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem sum_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
theorem pauliCoeff_smul (c : ℂ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a (c • X) = c * pauliCoeff a X := by
  unfold pauliCoeff
  rw [dif_pos hX, dif_pos (ComplexMatrix2.traceless.smul_mem c hX)]
  exact congrFun (map_smul OneLoop.pauliCoordinateEquiv c ⟨X, hX⟩) a
theorem pauliCoeff_im_eq_zero {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (a : Fin 3) : (pauliCoeff a X).im = 0 := by apply _root_.YangMills.SharedProofs.p23717 <;> assumption
theorem ofReal_smul_matrix (c : ℝ) (X : ComplexMatrix2) : (c : ℂ) • X = c • X := by apply _root_.YangMills.Construction.Tower.AsDifferentials.ofReal_smul_matrix <;> assumption
theorem real_pauli_sum_mem_hermitianTraceless (c : Fin 3 → ℝ) :
    ∑ a, (c a : ℂ) • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless :=
  Submodule.sum_mem _ fun a _ => by
    rw [ofReal_smul_matrix]
    exact ComplexMatrix2.hermitianTraceless.smul_mem _
      (BondFunctions.Coordinates.pauliFamily_mem_hermitianTraceless a)
end Coefficients
structure IsRealForm (r : PauliComponentsOfSymmetricKernel) (V : Submodule ℝ (r.space.index → ComplexMatrix2)) :
    Prop where
  subset_complex : ∀ f ∈ V, f ∈ r.space.complexSubmodule
  coeffs_real : ∀ f ∈ V, ∀ κ, (r.coeffs f κ).im = 0
  ofCoeffs_mem : ∀ c : r.Index → ℝ, r.ofCoeffs (fun κ => (c κ : ℂ)) ∈ V
  coeffs_ofCoeffs : ∀ c, r.coeffs (r.ofCoeffs c) = c
  ofCoeffs_coeffs : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f
  coeffs_add : ∀ f ∈ r.space.complexSubmodule, ∀ g ∈ r.space.complexSubmodule,
    r.coeffs (f + g) = r.coeffs f + r.coeffs g
  coeffs_smul : ∀ (c : ℂ), ∀ f ∈ r.space.complexSubmodule, r.coeffs (c • f) = c • r.coeffs f
theorem ofReal_smul_fun {ι : Type} (c : ℝ) (f : ι → ComplexMatrix2) : (c : ℂ) • f = c • f := by apply _root_.YangMills.Construction.Tower.AsDifferentials.ofReal_smul_pi <;> assumption
namespace IsRealForm
variable {r : PauliComponentsOfSymmetricKernel} {V : Submodule ℝ (r.space.index → ComplexMatrix2)}
def realCoords (h : IsRealForm r V) : V ≃ₗ[ℝ] (r.Index → ℝ) where
  toFun f κ := (r.coeffs f κ).re
  map_add' f g := by
    funext κ
    have := congrFun (h.coeffs_add f (h.subset_complex f f.2) g (h.subset_complex g g.2)) κ
    simp [this]
  map_smul' c f := by
    funext κ
    have := congrFun (h.coeffs_smul (c : ℂ) f (h.subset_complex f f.2)) κ
    rw [ofReal_smul_fun] at this
    simp [this]
  invFun c := ⟨r.ofCoeffs fun κ => (c κ : ℂ), h.ofCoeffs_mem c⟩
  left_inv f := by
    apply Subtype.ext
    have e : (fun κ => (((r.coeffs f κ).re : ℝ) : ℂ)) = r.coeffs f :=
      funext fun κ => Complex.ext rfl (by simp [h.coeffs_real f f.2 κ])
    show r.ofCoeffs (fun κ => (((r.coeffs f κ).re : ℝ) : ℂ)) = f
    rw [e, h.ofCoeffs_coeffs f (h.subset_complex f f.2)]
  right_inv c := by
    funext κ
    show (r.coeffs (r.ofCoeffs fun κ => (c κ : ℂ)) κ).re = c κ
    rw [h.coeffs_ofCoeffs]
    simp
theorem coe_realCoords (h : IsRealForm r V) (f : V) (κ : r.Index) :
    ((h.realCoords f κ : ℝ) : ℂ) = r.coeffs f κ :=
  Complex.ext rfl (by simp [h.coeffs_real f f.2 κ])
end IsRealForm
theorem det_descendMatrix_eq_shiftedDetOn {r : PauliComponentsOfSymmetricKernel}
    {V : Submodule ℝ (r.space.index → ComplexMatrix2)} (h : IsRealForm r V) [Finite r.Index]
    {T : (r.space.index → ComplexMatrix2) → r.space.index → ComplexMatrix2}
    (hT : ∃ T' : V →ₗ[ℝ] V, ∀ f : V, (T' f : r.space.index → ComplexMatrix2) = T f) (z : ℝ)
    (I : PeriodicData) (s : ℕ) {q : I.Carrier → r.Index} (hs : Function.Surjective q)
    (hq : ∀ ι ι', q ι = q ι' ↔ ∃ m : Fin 4 → ℤ, ι' = I.translate (s • m) ι)
    {F : I.Carrier → I.Carrier → ℂ} {M : r.Index → r.Index → ℂ}
    (hF : ∀ ι' ι, F ι' ι = M (q ι') (q ι))
    (hM : ∀ f ∈ V, r.coeffs (T f + z • f) = applyKernel M (r.coeffs f)) :
    LinearMap.det (linearMapOfEntries (descendMatrix I I s F)) =
      ((shiftedDetOn V T z : ℝ) : ℂ) := by
  obtain ⟨T', hT'⟩ := hT
  have hA : ∀ f : V,
      (restrictToSubmodule V (fun f => T f + z • f) f : r.space.index → ComplexMatrix2) =
      T f + z • (f : r.space.index → ComplexMatrix2) :=
    Classical.epsilon_spec
      (p := fun T'' : V →ₗ[ℝ] V => ∀ f : V, (T'' f : r.space.index → ComplexMatrix2) =
        T f + z • (f : r.space.index → ComplexMatrix2))
      ⟨T' + z • LinearMap.id, fun f => by simp [hT' f]⟩
  unfold shiftedDetOn
  refine det_descendMatrix_of_factors I s hs hq hF h.realCoords _ fun f i => ?_
  have e₁ : (fun j => ((h.realCoords f j : ℝ) : ℂ)) = r.coeffs f :=
    funext fun j => h.coe_realCoords f j
  rw [e₁, h.coe_realCoords, hA, hM f f.2]
open YangMills.Construction.LocalKernels
open YangMills.Construction.LocalKernels.Periodisation
section BlockEvaluations
variable {L n : ℕ}
theorem edge_xor_opposite (hO : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (b : Edge L n 0 0) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
  ((hO ⟨L, hL, 1, ⟨n, hn⟩⟩ 1 le_rfl).2.2.2 b).2.2.2.2.2
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < meshAt L 0 0 := by apply _root_.YangMills.Construction.Tower.IdentityOperators.meshAt_zero_zero_pos <;> assumption
theorem full_opposite_isPositivelyOriented {b : FullSpace.Edge L 0 0}
    (hb : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · exact absurd ⟨μ, h⟩ hb
  · refine ⟨μ, ?_⟩
    show b.initial - b.terminal = _
    rw [← neg_sub, h, neg_neg]
theorem vertexCoordinates_isRealForm (σ : Type) :
    IsRealForm (vertexCoordinate σ) (GroupLieProduct.hermitianTracelessFunctions σ) where
  subset_complex f hf := Submodule.mem_pi.2 fun x _ =>
    traceless_of_hermitianTraceless (Submodule.mem_pi.1 hf x (mem_univ x))
  coeffs_real f hf κ := pauliCoeff_im_eq_zero (Submodule.mem_pi.1 hf κ.2 (mem_univ _)) κ.1
  ofCoeffs_mem c := Submodule.mem_pi.2 fun x _ =>
    real_pauli_sum_mem_hermitianTraceless fun a => c (a, x)
  coeffs_ofCoeffs c := funext fun ι => pauliCoeff_sum (fun a => c (a, ι.2)) ι.1
  ofCoeffs_coeffs f hf := funext fun x =>
    sum_pauliCoeff (Submodule.mem_pi.1 hf x (mem_univ x))
  coeffs_add f hf g hg := funext fun ι =>
    pauliCoeff_add (Submodule.mem_pi.1 hf ι.2 (mem_univ _))
      (Submodule.mem_pi.1 hg ι.2 (mem_univ _)) ι.1
  coeffs_smul c f hf := funext fun ι =>
    pauliCoeff_smul c (Submodule.mem_pi.1 hf ι.2 (mem_univ _)) ι.1
theorem edgePauliCoordinates_ofCoeffs_pos (c : (edgePauliCoordinates L n 0 0).Index → ℂ) {b : Edge L n 0 0}
    (hb : b.IsPositivelyOriented) :
    (edgePauliCoordinates L n 0 0).ofCoeffs c b = ofPauliCoeffs c ⟨b, hb⟩ := by
  unfold edgePauliCoordinates
  dsimp only
  rw [extendOddly, if_pos hb]
  exact dif_pos hb
theorem edgePauliCoordinates_ofCoeffs_neg (c : (edgePauliCoordinates L n 0 0).Index → ℂ) {b : Edge L n 0 0}
    (hb : ¬b.IsPositivelyOriented) (hb' : b.opposite.IsPositivelyOriented) :
    (edgePauliCoordinates L n 0 0).ofCoeffs c b = -ofPauliCoeffs c ⟨b.opposite, hb'⟩ := by
  unfold edgePauliCoordinates
  dsimp only
  rw [extendOddly, if_neg hb]
  exact congrArg Neg.neg (dif_pos hb')
theorem edgePauliCoordinates_ofCoeffs_opposite
    (hx : ∀ b : Edge L n 0 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (c : (edgePauliCoordinates L n 0 0).Index → ℂ) (b : Edge L n 0 0) :
    (edgePauliCoordinates L n 0 0).ofCoeffs c b.opposite = -(edgePauliCoordinates L n 0 0).ofCoeffs c b := by
  rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [edgePauliCoordinates_ofCoeffs_neg c h₂ h₁, edgePauliCoordinates_ofCoeffs_pos c h₁]
    rfl
  · rw [edgePauliCoordinates_ofCoeffs_pos c h₁, edgePauliCoordinates_ofCoeffs_neg c h₂ h₁, neg_neg]
theorem edgePauliCoordinates_ofCoeffs_coeffs
    (hx : ∀ b : Edge L n 0 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {f : Edge L n 0 0 → ComplexMatrix2} (hf : f ∈ complexEdgeForms L n 0 0) :
    (edgePauliCoordinates L n 0 0).ofCoeffs ((edgePauliCoordinates L n 0 0).coeffs f) = f := by
  have hpos : ∀ (p : Edge L n 0 0) (hp : p.IsPositivelyOriented),
      ofPauliCoeffs ((edgePauliCoordinates L n 0 0).coeffs f) ⟨p, hp⟩ = f p := fun p hp =>
    sum_pauliCoeff (hf.1 p hp)
  have key : ∀ b : Edge L n 0 0,
      (edgePauliCoordinates L n 0 0).ofCoeffs ((edgePauliCoordinates L n 0 0).coeffs f) b = f b := fun b => by
    rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact (edgePauliCoordinates_ofCoeffs_pos _ h₁).trans (hpos b h₁)
    · exact (edgePauliCoordinates_ofCoeffs_neg _ h₂ h₁).trans
        ((congrArg Neg.neg (hpos _ h₁)).trans (by rw [hf.2 b, neg_neg]))
  exact funext key
theorem edgePauliCoordinates_isRealForm
    (hx : ∀ b : Edge L n 0 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    IsRealForm (edgePauliCoordinates L n 0 0) (edgeFormSpace L n 0 0) where
  subset_complex f hf := ⟨fun b hb => traceless_of_hermitianTraceless (hf.1 b hb), hf.2⟩
  coeffs_real f hf κ := pauliCoeff_im_eq_zero (hf.1 κ.2.1 κ.2.2) κ.1
  ofCoeffs_mem c := ⟨fun b hb => by
      rw [edgePauliCoordinates_ofCoeffs_pos _ hb]
      exact real_pauli_sum_mem_hermitianTraceless fun a => c (a, ⟨b, hb⟩),
    edgePauliCoordinates_ofCoeffs_opposite hx _⟩
  coeffs_ofCoeffs c := funext fun ι => by
    show pauliCoeff ι.1 ((edgePauliCoordinates L n 0 0).ofCoeffs c ι.2.1) = c ι
    rw [edgePauliCoordinates_ofCoeffs_pos c ι.2.2]
    exact pauliCoeff_sum (fun a => c (a, ι.2)) ι.1
  ofCoeffs_coeffs f hf := edgePauliCoordinates_ofCoeffs_coeffs hx hf
  coeffs_add f hf g hg := funext fun ι => pauliCoeff_add (hf.1 ι.2.1 ι.2.2) (hg.1 ι.2.1 ι.2.2) ι.1
  coeffs_smul c f hf := funext fun ι => pauliCoeff_smul c (hf.1 ι.2.1 ι.2.2) ι.1
theorem fullEdgeBasis_ofCoeffs_pos (c : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ)
    {b : FullSpace.Edge L 0 0} (hb : b.IsPositivelyOriented) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c b = ofPauliCoeffs c ⟨b, hb⟩ := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.edge_ofCoeffs_apply <;> assumption
theorem fullEdgeBasis_ofCoeffs_neg (c : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ)
    {b : FullSpace.Edge L 0 0} (hb : ¬b.IsPositivelyOriented) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c b =
      -ofPauliCoeffs c ⟨b.opposite, full_opposite_isPositivelyOriented hb⟩ := by
  unfold FullSpace.edgePauliCoordinates
  dsimp only
  rw [FullSpace.extendOddly, if_neg hb]
  exact congrArg Neg.neg (dif_pos (full_opposite_isPositivelyOriented hb))
theorem fullEdgeBasis_ofCoeffs_mem (hL : Conventions.IsAdmissibleBlockingFactor L)
    (c : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [fullEdgeBasis_ofCoeffs_pos c hb]
    exact pauli_sum_mem_traceless fun a => c (a, ⟨b, hb⟩)
  · by_cases hb : b.IsPositivelyOriented
    · have h₂ := InfiniteLattice.Link.opposite_not_isPositivelyOriented (meshAt_pos hL) hb
      rw [fullEdgeBasis_ofCoeffs_neg c h₂, fullEdgeBasis_ofCoeffs_pos c hb]
      rfl
    · rw [fullEdgeBasis_ofCoeffs_pos c (full_opposite_isPositivelyOriented hb),
        fullEdgeBasis_ofCoeffs_neg c hb, neg_neg]
theorem fullEdgeBasis_coeffs_ofCoeffs (c : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L 0 0).coeffs ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.edge_coeffs_ofCoeffs <;> assumption
theorem fullEdgeBasis_coeffs_injective {f g : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hf : f ∈ FullSpace.complexEdgeForms (meshAt L 0 0))
    (hg : g ∈ FullSpace.complexEdgeForms (meshAt L 0 0))
    (h : (FullSpace.edgePauliCoordinates L 0 0).coeffs f = (FullSpace.edgePauliCoordinates L 0 0).coeffs g) :
    f = g := by
  have hpos : ∀ (p : FullSpace.Edge L 0 0), p.IsPositivelyOriented → f p = g p := fun p hp => by
    rw [← sum_pauliCoeff (hf.1 p hp), ← sum_pauliCoeff (hg.1 p hp)]
    exact Finset.sum_congr rfl fun a _ => by
      rw [show pauliCoeff a (f p) = pauliCoeff a (g p) from congrFun h (a, ⟨p, hp⟩)]
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact hpos b hb
  · have h₁ := hf.2 b
    have h₂ := hg.2 b
    rw [hpos _ (full_opposite_isPositivelyOriented hb)] at h₁
    exact neg_injective (h₁.symm.trans h₂)
end BlockEvaluations
theorem transposeOfValues_eq_transposeMap {S S' : PairedFunctionSpace}
    {m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2}
    (T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule)
    (hT : ∀ f : S.complexSubmodule, (T f : S'.index → ComplexMatrix2) = m f)
    (g : S'.index → ComplexMatrix2) (hg : g ∈ S'.complexSubmodule) :
    PairedFunctionSpace.transposeOfValues S S' m g =
      (PairedFunctionSpace.transposeMap T ⟨g, hg⟩ : S.complexSubmodule).1 := by
  have hc : PairedFunctionSpace.linearOfValues S S' m = T := by
    have hs := Classical.epsilon_spec
      (p := fun T' : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule =>
        ∀ f : S.complexSubmodule, (T' f : S'.index → ComplexMatrix2) = m f) ⟨T, hT⟩
    refine LinearMap.ext fun f => Subtype.ext ?_
    exact (hs f).trans (hT f).symm
  unfold PairedFunctionSpace.transposeOfValues
  rw [dif_pos hg, hc]
section Descent
variable (L n : ℕ)
abbrev vertexCells : CellClass 0 := verticesAtZero 0
abbrev edgeCells : CellClass 0 := edgesAtZero 0
variable {L n}
structure HessianKernelsDescend (V : Edge L n 0 0 → ComplexMatrix2)
    (T₁ : KernelMatrix (Idx L (vertexCells).colourPairs) (Idx L (edgeCells).colourPairs))
    (T₂ : KernelMatrix (Idx L (edgeCells).colourPairs) (Idx L (edgeCells).colourPairs))
    (M₁ : KernelMatrix ((vertexCells).colourPairs.ImageCarrier L n)
      ((edgeCells).colourPairs.ImageCarrier L n))
    (M₂ : KernelMatrix ((edgeCells).colourPairs.ImageCarrier L n)
      ((vertexCells).colourPairs.ImageCarrier L n))
    (M₃ : KernelMatrix ((edgeCells).colourPairs.ImageCarrier L n)
      ((edgeCells).colourPairs.ImageCarrier L n)) :
    Prop where
  local_diff : IsRLocal L (vertexCells).colourPairs (edgeCells).colourPairs 2 T₁
  local_diffT : IsRLocal L (edgeCells).colourPairs (vertexCells).colourPairs 2
    (kernelT L (vertexCells).colourPairs (edgeCells).colourPairs T₁)
  local_hessian : IsRLocal L (edgeCells).colourPairs (edgeCells).colourPairs 2 T₂
  descends_diff : KernelDescends L n (vertexCells).colourPairs (edgeCells).colourPairs T₁ M₁
  descends_diffT : KernelDescends L n (edgeCells).colourPairs (vertexCells).colourPairs
    (kernelT L (vertexCells).colourPairs (edgeCells).colourPairs T₁) M₂
  descends_hessian : KernelDescends L n (edgeCells).colourPairs (edgeCells).colourPairs T₂ M₃
  full_diff : ∀ l ∈ (CellClass.fullSpace L vertexCells).complexSubmodule,
    FullSpace.covDiff (liftGaugeField L n 0 0 V) l ∈
        (CellClass.fullSpace L edgeCells).complexSubmodule ∧
      CellClass.coeffsOn L edgeCells (FullSpace.covDiff (liftGaugeField L n 0 0 V) l) =
        applyKernel T₁ (CellClass.coeffsOn L vertexCells l)
  full_diffT : ∀ B ∈ (CellClass.fullSpace L edgeCells).complexSubmodule,
    FullSpace.covDiffAdjoint (liftGaugeField L n 0 0 V) B ∈
        (CellClass.fullSpace L vertexCells).complexSubmodule ∧
      CellClass.coeffsOn L vertexCells (FullSpace.covDiffAdjoint (liftGaugeField L n 0 0 V) B) =
        applyKernel (kernelT L (vertexCells).colourPairs (edgeCells).colourPairs T₁)
          (CellClass.coeffsOn L edgeCells B)
  full_hessian : ∀ B ∈ (CellClass.fullSpace L edgeCells).complexSubmodule,
    FullSpace.complexHessianOperator (liftGaugeField L n 0 0 V) B ∈
        (CellClass.fullSpace L edgeCells).complexSubmodule ∧
      CellClass.coeffsOn L edgeCells
          (FullSpace.complexHessianOperator (liftGaugeField L n 0 0 V) B) =
        applyKernel T₂ (CellClass.coeffsOn L edgeCells B)
  quot_diff : ∀ l ∈ (CellClass.quotSpace L n vertexCells).complexSubmodule,
    covDiff V l ∈ (CellClass.quotSpace L n edgeCells).complexSubmodule ∧
      CellClass.quotCoeffsOn L n edgeCells (covDiff V l) =
        applyKernel M₁ (CellClass.quotCoeffsOn L n vertexCells l)
  quot_diffT : ∀ B ∈ (CellClass.quotSpace L n edgeCells).complexSubmodule,
    PairedFunctionSpace.transposeOfValues (pairedFunctions (Vertex L n 0 0))
        (edgePairedSpace L n 0 0) (covDiff V) B ∈
        (CellClass.quotSpace L n vertexCells).complexSubmodule ∧
      CellClass.quotCoeffsOn L n vertexCells
          (PairedFunctionSpace.transposeOfValues (pairedFunctions (Vertex L n 0 0))
            (edgePairedSpace L n 0 0) (covDiff V) B) =
        applyKernel M₂ (CellClass.quotCoeffsOn L n edgeCells B)
  quot_hessian : ∀ B ∈ (CellClass.quotSpace L n edgeCells).complexSubmodule,
    complexHessianOperator V B ∈ (CellClass.quotSpace L n edgeCells).complexSubmodule ∧
      CellClass.quotCoeffsOn L n edgeCells (complexHessianOperator V B) =
        applyKernel M₃ (CellClass.quotCoeffsOn L n edgeCells B)
theorem exists_hessianKernels (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hEv : LocalKernelFacts (k := 0) L) (hBr : PairBracketTranspose (k := 0) L)
    (hAct : HessianDataDescend L n 0 0 (Nat.zero_le 0))
    {V : Edge L n 0 0 → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup) :
    ∃ T₁ T₂ M₁ M₂ M₃, HessianKernelsDescend V T₁ T₂ M₁ M₂ M₃ := by
  obtain ⟨_, hD, hH, _⟩ := hAct V hV 0 (Submodule.zero_mem _)
  obtain ⟨T₁, m₁, hl₁, hg₁, hv₁, ⟨M₁, hM₁, hd₁⟩, ⟨M₂, hM₂, hd₂⟩⟩ := hD
  obtain ⟨T₂, m₂, hl₂, hg₂, hv₂, ⟨M₃, hM₃, hd₃⟩, _⟩ := hH
  obtain ⟨m, m', hm, hm', -, -, hmm⟩ :=
    (hBr vertexCells edgeCells (by simp [vertexCells, verticesAtZero, CellClass.vertexClass])
      (by simp [edgeCells, edgesAtZero, CellClass.edgeClass])).2 2 (by norm_num) T₁ hl₁
  have hvalues : ∀ f : (CellClass.fullSpace L vertexCells).complexSubmodule,
      (m f : (CellClass.fullSpace L edgeCells).index → ComplexMatrix2) =
        FullSpace.covDiff (liftGaugeField L n 0 0 V) f.1 := fun f =>
    fullEdgeBasis_coeffs_injective (m f).2 (hg₁ f).1 (by
      have h₁ := (hm f).2
      have h₂ := (hg₁ f).2
      exact funext fun ι => congrFun (h₁.trans h₂.symm) ⟨(), ι⟩)
  refine ⟨T₁, T₂, M₁, M₂, M₃, ⟨hl₁, (hEv _ _ 2 (by norm_num) T₁ hl₁).2.2.1, hl₂, hd₁, hd₂, hd₃,
    fun l hl => hg₁ ⟨l, hl⟩, fun B hB => ?_, fun B hB => hg₂ ⟨B, hB⟩, fun l hl => ?_, fun B hB => ?_,
    fun B hB => ?_⟩⟩
  · have e : FullSpace.covDiffAdjoint (liftGaugeField L n 0 0 V) B =
        (m' ⟨B, hB⟩ : (CellClass.fullSpace L vertexCells).complexSubmodule).1 := by
      rw [hmm]
      exact transposeOfValues_eq_transposeMap m hvalues B hB
    rw [e]
    exact hm' ⟨B, hB⟩ |>.imp (fun _ => (m' ⟨B, hB⟩).2) id
  · have e : covDiff V l = (m₁ ⟨l, hl⟩).1 := (hv₁ ⟨l, hl⟩).symm
    rw [e]
    exact ⟨(m₁ ⟨l, hl⟩).2, hM₁ ⟨l, hl⟩⟩
  · have e : PairedFunctionSpace.transposeOfValues (pairedFunctions (Vertex L n 0 0))
        (edgePairedSpace L n 0 0) (covDiff V) B =
        (PairedFunctionSpace.transposeMap m₁ ⟨B, hB⟩).1 :=
      transposeOfValues_eq_transposeMap m₁ hv₁ B hB
    rw [e]
    exact ⟨(PairedFunctionSpace.transposeMap m₁ ⟨B, hB⟩).2, hM₂ ⟨B, hB⟩⟩
  · have e : complexHessianOperator V B = (m₂ ⟨B, hB⟩).1 := (hv₂ ⟨B, hB⟩).symm
    rw [e]
    exact ⟨(m₂ ⟨B, hB⟩).2, hM₃ ⟨B, hB⟩⟩
end Descent
section Periods
variable {L n : ℕ}
open Classical in
def idMatrix (N : Type) : N → N → ℂ := fun i j => if i = j then 1 else 0
theorem smul_idMatrix_isRLocal (J : WeightedIndexSet 0) (z : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IsRLocal L J J R (z • idMatrix (Idx L J)) := by
  intro ι' ι h
  have hne : ι' ≠ ι := by
    rintro rfl
    apply h
    simpa [TorusMetric.supNormVec] using hR
  simp [idMatrix, hne]
theorem smul_idMatrix_descends (J : WeightedIndexSet 0) (z : ℂ) :
    KernelDescends L n J J (z • idMatrix (Idx L J)) (z • idMatrix (J.ImageCarrier L n)) := by
  classical
  refine ⟨⟨0, le_rfl, smul_idMatrix_isRLocal J z le_rfl⟩, fun f => ?_⟩
  have h₁ : applyKernel (z • idMatrix (Idx L J)) (J.lift L n f) = z • J.lift L n f :=
    applyKernel_smul_unit z _
  have h₂ : applyKernel (z • idMatrix (J.ImageCarrier L n)) f = z • f := applyKernel_smul_unit z _
  rw [h₁, h₂]
  rfl
theorem periodization_add_smul_id (hSP : DescendsAlgebra (k := 0) L n) (J : WeightedIndexSet 0)
    {K : KernelMatrix (Idx L J) (Idx L J)}
    {M : KernelMatrix (J.ImageCarrier L n) (J.ImageCarrier L n)} {R : ℝ} (hR : 0 ≤ R)
    (hl : IsRLocal L J J R K) (hd : KernelDescends L n J J K M) (z : ℂ)
    (ι' ι : Idx L J) :
    periodization (J.toPeriodicData L) (J.toPeriodicData L) (K + z • idMatrix (Idx L J))
        (periodSide L n) ι' ι =
      (M + z • idMatrix (J.ImageCarrier L n)) (J.proj L n ι') (J.proj L n ι) := by
  obtain ⟨-, hl', hd', -⟩ := hSP J J J R hR K (z • idMatrix (Idx L J)) K M
    (z • idMatrix (J.ImageCarrier L n)) M hl (smul_idMatrix_isRLocal J z hR) hl hd
    (smul_idMatrix_descends J z) hd
  exact ((hSP J J J R hR _ _ _ _ _ _ hl' hl' hl' hd' hd' hd').1.1 ι' ι).symm
def quotCellEquiv (A : CellClass 0)
    (hs : Function.Surjective
      (Cell.proj n : Cell L 0 A.level A.cellType → QuotientCell L n 0 A.level A.cellType)) :
    (Fin 3 × QuotientCell L n 0 A.level A.cellType) ≃ A.colourPairs.ImageCarrier L n :=
  Equiv.ofBijective
    (fun c => ⟨(), ⟨c, by
      obtain ⟨x, hx⟩ := hs c.2
      exact ⟨(c.1, x), Prod.ext rfl hx⟩⟩⟩)
    ⟨fun c c' h => congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.1 h).2), by
      rintro ⟨⟨⟩, c, hc⟩
      exact ⟨c, rfl⟩⟩
theorem applyKernel_equiv {P Q : Type} (ψ : P ≃ Q) (M : Q → Q → ℂ) (h : Q → ℂ) (i : P) :
    applyKernel (fun i j => M (ψ i) (ψ j)) (fun j => h (ψ j)) i = applyKernel M h (ψ i) :=
  Equiv.tsum_eq ψ fun j => M (ψ i) j * h j
theorem vertex_proj_classes (hC : ProjCellsClassified L n 0 0) :
    Function.Surjective (fun ι : (colourVertices L 0 0).Carrier =>
        ((ι.1, FullSpace.projVertex L n 0 0 ι.2) : (vertexCoordinate (Vertex L n 0 0)).Index)) ∧
      ∀ ι ι' : (colourVertices L 0 0).Carrier,
        ((ι.1, FullSpace.projVertex L n 0 0 ι.2) : (vertexCoordinate (Vertex L n 0 0)).Index) =
            (ι'.1, FullSpace.projVertex L n 0 0 ι'.2) ↔
          ∃ m : Fin 4 → ℤ, ι' = (colourVertices L 0 0).translate ((2 * L ^ n) • m) ι := by
  obtain ⟨hs, hi⟩ := hC .vertex
  refine ⟨fun c => ?_, fun ι ι' => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨x, hx⟩ := hs c.2
    exact ⟨(c.1, x), Prod.ext rfl hx⟩
  · obtain ⟨m, hm⟩ := (hi ι.2 ι'.2).1 (congrArg Prod.snd h)
    exact ⟨m, Prod.ext (congrArg Prod.fst h).symm hm⟩
  · rintro ⟨m, rfl⟩
    exact Prod.ext rfl ((hi ι.2 _).2 ⟨m, rfl⟩)
theorem edge_proj_classes (hC : ProjCellsClassified L n 0 0) :
    Function.Surjective (fun ι : (colourEdges L 0 0).Carrier =>
        ((ι.1, projPositiveEdge L n 0 0 ι.2) : (edgePauliCoordinates L n 0 0).Index)) ∧
      ∀ ι ι' : (colourEdges L 0 0).Carrier,
        ((ι.1, projPositiveEdge L n 0 0 ι.2) : (edgePauliCoordinates L n 0 0).Index) =
            (ι'.1, projPositiveEdge L n 0 0 ι'.2) ↔
          ∃ m : Fin 4 → ℤ, ι' = (colourEdges L 0 0).translate ((2 * L ^ n) • m) ι := by
  obtain ⟨hs, hi⟩ := hC .edge
  refine ⟨fun c => ?_, fun ι ι' => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨x, hx⟩ := hs c.2
    exact ⟨(c.1, x), Prod.ext rfl hx⟩
  · obtain ⟨m, hm⟩ := (hi ι.2 ι'.2).1 (congrArg Prod.snd h)
    exact ⟨m, Prod.ext (congrArg Prod.fst h).symm hm⟩
  · rintro ⟨m, rfl⟩
    exact Prod.ext rfl ((hi ι.2 _).2 ⟨m, rfl⟩)
end Periods
section Determinants
variable {L n : ℕ} {V : Edge L n 0 0 → ComplexMatrix2}
  {T₁ : KernelMatrix (Idx L (vertexCells).colourPairs) (Idx L (edgeCells).colourPairs)}
  {T₂ : KernelMatrix (Idx L (edgeCells).colourPairs) (Idx L (edgeCells).colourPairs)}
  {M₁ : KernelMatrix ((vertexCells).colourPairs.ImageCarrier L n)
    ((edgeCells).colourPairs.ImageCarrier L n)}
  {M₂ : KernelMatrix ((edgeCells).colourPairs.ImageCarrier L n)
    ((vertexCells).colourPairs.ImageCarrier L n)}
  {M₃ : KernelMatrix ((edgeCells).colourPairs.ImageCarrier L n)
    ((edgeCells).colourPairs.ImageCarrier L n)}
theorem gaugeLaplacianAt_eq_compKernel (hK : HessianKernelsDescend V T₁ T₂ M₁ M₂ M₃)
    {G : KernelMatrix (Fin 3 × FullSpace.Vertex L 0 0) (Fin 3 × FullSpace.Vertex L 0 0)}
    (hG : Represents G ((vertexCoordinate (FullSpace.Vertex L 0 0)).mapOnCoeffs
      (vertexCoordinate (FullSpace.Vertex L 0 0))
      (FullSpace.gaugeLaplacian (liftGaugeField L n 0 0 V))))
    (a c : Fin 3 × FullSpace.Vertex L 0 0) :
    G a c = compKernel (kernelT L (vertexCells).colourPairs (edgeCells).colourPairs T₁) T₁
      (⟨(), a⟩ : Idx L (vertexCells).colourPairs) (⟨(), c⟩ : Idx L (vertexCells).colourPairs) := by
  classical
  set δ : Fin 3 × FullSpace.Vertex L 0 0 → ℂ := fun κ => if κ = c then 1 else 0 with hδ
  have hl : ofPauliCoeffs δ ∈ (CellClass.fullSpace L vertexCells).complexSubmodule :=
    Submodule.mem_pi.2 fun x _ => pauli_sum_mem_traceless _
  obtain ⟨hc₁, hr₁⟩ := hK.full_diff _ hl
  obtain ⟨-, hr₂⟩ := hK.full_diffT _ hc₁
  rw [hr₁] at hr₂
  have hread : CellClass.coeffsOn L vertexCells (ofPauliCoeffs δ) =
      fun κ : Idx L (vertexCells).colourPairs => if κ = ⟨(), c⟩ then 1 else 0 := by
    funext κ
    obtain ⟨⟨⟩, κ⟩ := κ
    have e : pauliCoeff κ.1 (ofPauliCoeffs δ κ.2) = δ κ :=
      pauliCoeff_sum (fun a => δ (a, κ.2)) κ.1
    refine e.trans ?_
    by_cases h : κ = c
    · subst h
      exact (if_pos rfl).trans (if_pos rfl).symm
    · have h' : (⟨(), κ⟩ : Idx L (vertexCells).colourPairs) ≠ ⟨(), c⟩ := fun e' =>
        h (eq_of_heq (Sigma.mk.inj_iff.1 e').2)
      exact (if_neg h).trans (if_neg h').symm
  have hr₃ := hr₂.trans (congrArg (fun h => applyKernel
    (kernelT L (vertexCells).colourPairs (edgeCells).colourPairs T₁) (applyKernel T₁ h)) hread)
  have h₄ := (congrFun hr₃ (⟨(), a⟩ : Idx L (vertexCells).colourPairs)).trans
    (applyKernel_applyKernel_indicator _ T₁ (⟨(), c⟩ : Idx L (vertexCells).colourPairs) _)
  have h₁ : G a c = applyKernel G δ a := (applyKernel_indicator G c a).symm
  rw [h₁, (hG δ).2]
  exact h₄
theorem massiveHessianAt_eq_kernel (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hK : HessianKernelsDescend V T₁ T₂ M₁ M₂ M₃)
    {G : KernelMatrix (FullSpace.edgePauliCoordinates L 0 0).Index (FullSpace.edgePauliCoordinates L 0 0).Index}
    (hG : Represents G ((FullSpace.edgePauliCoordinates L 0 0).mapOnCoeffs (FullSpace.edgePauliCoordinates L 0 0)
      (FullSpace.massiveHessian (liftGaugeField L n 0 0 V))))
    (a c : (FullSpace.edgePauliCoordinates L 0 0).Index) :
    G a c = (T₂ + compKernel T₁ (kernelT L (vertexCells).colourPairs (edgeCells).colourPairs T₁))
      (⟨(), a⟩ : Idx L (edgeCells).colourPairs) (⟨(), c⟩ : Idx L (edgeCells).colourPairs) := by
  classical
  set δ : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ := fun κ => if κ = c then 1 else 0 with hδ
  set l := (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs δ with hl'
  have hl : l ∈ (CellClass.fullSpace L edgeCells).complexSubmodule :=
    fullEdgeBasis_ofCoeffs_mem hL δ
  obtain ⟨hc₁, hr₁⟩ := hK.full_diffT _ hl
  obtain ⟨hc₂, hr₂⟩ := hK.full_diff _ hc₁
  obtain ⟨hc₃, hr₃⟩ := hK.full_hessian _ hl
  rw [hr₁] at hr₂
  have hread : CellClass.coeffsOn L edgeCells l =
      fun κ : Idx L (edgeCells).colourPairs => if κ = ⟨(), c⟩ then 1 else 0 := by
    funext κ
    obtain ⟨⟨⟩, κ⟩ := κ
    have e : (FullSpace.edgePauliCoordinates L 0 0).coeffs l κ = δ κ :=
      congrFun (fullEdgeBasis_coeffs_ofCoeffs δ) κ
    refine e.trans ?_
    by_cases h : κ = c
    · subst h
      exact (if_pos rfl).trans (if_pos rfl).symm
    · have h' : (⟨(), κ⟩ : Idx L (edgeCells).colourPairs) ≠ ⟨(), c⟩ := fun e' =>
        h (eq_of_heq (Sigma.mk.inj_iff.1 e').2)
      exact (if_neg h).trans (if_neg h').symm
  rw [hread] at hr₂ hr₃
  have h₁ : G a c = applyKernel G δ a := (applyKernel_indicator G c a).symm
  have h₂ : (FullSpace.edgePauliCoordinates L 0 0).coeffs
      (FullSpace.massiveHessian (liftGaugeField L n 0 0 V) l) a =
      (FullSpace.edgePauliCoordinates L 0 0).coeffs
        (FullSpace.complexHessianOperator (liftGaugeField L n 0 0 V) l) a +
      (FullSpace.edgePauliCoordinates L 0 0).coeffs
        (FullSpace.covDiff (liftGaugeField L n 0 0 V)
          (FullSpace.covDiffAdjoint (liftGaugeField L n 0 0 V) l)) a :=
    pauliCoeff_add (hc₃.1 a.2.1 a.2.2) (hc₂.1 a.2.1 a.2.2) a.1
  have h₃ := (congrFun hr₃ (⟨(), a⟩ : Idx L (edgeCells).colourPairs)).trans
    (applyKernel_indicator T₂ (⟨(), c⟩ : Idx L (edgeCells).colourPairs) _)
  have h₄ := (congrFun hr₂ (⟨(), a⟩ : Idx L (edgeCells).colourPairs)).trans
    (@applyKernel_applyKernel_indicator _ _ _ (fun _ _ => Classical.propDecidable _) T₁ _
      (⟨(), c⟩ : Idx L (edgeCells).colourPairs) _)
  rw [h₁, (hG δ).2]
  exact h₂.trans (congrArg₂ (· + ·) h₃ h₄)
theorem det_vertex_eq (hC : ProjCellsClassified L n 0 0)
    (hfin : ∀ I : WeightedIndexSet 0, Finite (I.ImageCarrier L n))
    (hSP : DescendsAlgebra (k := 0) L n)
    (hK : HessianKernelsDescend V T₁ T₂ M₁ M₂ M₃) (z : ℝ)
    (ζ : (colourEdges L 0 0).Carrier → ℂ)
    (hζ : FullSpace.expField ζ = liftGaugeField L n 0 0 V)
    (hG : Represents (FullSpace.gaugeLaplacianAt ζ)
      ((vertexCoordinate (FullSpace.Vertex L 0 0)).mapOnCoeffs
        (vertexCoordinate (FullSpace.Vertex L 0 0))
        (FullSpace.gaugeLaplacian (FullSpace.expField ζ))))
    (hT : ∃ T' : vertexFunctionSpace L n 0 0 →ₗ[ℝ] vertexFunctionSpace L n 0 0,
      ∀ f : vertexFunctionSpace L n 0 0,
        (T' f : Vertex L n 0 0 → ComplexMatrix2) = gaugeLaplacian V f) :
    LinearMap.det (linearMapOfEntries (descendMatrix (colourVertices L 0 0)
        (colourVertices L 0 0) (2 * L ^ n) (periodization (colourVertices L 0 0)
          (colourVertices L 0 0) (vertexOpFun L z ζ) (2 * L ^ n)))) =
      ((shiftedDetOn (vertexFunctionSpace L n 0 0) (gaugeLaplacian V) z : ℝ) : ℂ) := by
  classical
  rw [hζ] at hG
  obtain ⟨hsq, hqq⟩ := vertex_proj_classes hC
  let ψ := quotCellEquiv (L := L) (n := n) vertexCells (hC .vertex).1
  have : Finite (vertexCells.colourPairs.ImageCarrier L n) := hfin _
  have : Finite (edgeCells.colourPairs.ImageCarrier L n) := hfin _
  have : Finite (vertexCoordinate (Vertex L n 0 0)).Index := Finite.of_equiv _ ψ.symm
  obtain ⟨-, -, -, hpl, hpd, -⟩ := hSP (edgeCells).colourPairs (vertexCells).colourPairs
    (vertexCells).colourPairs 2 (by norm_num) _ _ T₁ M₂ M₂ M₁ hK.local_diffT hK.local_diffT
    hK.local_diff hK.descends_diffT hK.descends_diffT hK.descends_diff
  set Mh := compKernel M₂ M₁ + (z : ℂ) • idMatrix (vertexCells.colourPairs.ImageCarrier L n)
    with hMh
  refine det_descendMatrix_eq_shiftedDetOn (r := vertexCoordinate (Vertex L n 0 0))
    (V := vertexFunctionSpace L n 0 0) (vertexCoordinates_isRealForm _) hT z (colourVertices L 0 0)
    (2 * L ^ n) hsq hqq (M := fun i j => Mh (ψ i) (ψ j)) (fun ι' ι => ?_) fun f hf => ?_
  · have key := periodization_add_smul_id hSP (vertexCells).colourPairs (by norm_num) hpl hpd
      (z : ℂ) (⟨(), ι'⟩ : Idx L (vertexCells).colourPairs)
      (⟨(), ι⟩ : Idx L (vertexCells).colourPairs)
    refine Eq.trans ?_ key
    refine tsum_congr fun m => ?_
    have hi : ∀ x y : (colourVertices L 0 0).Carrier,
        idKernel (colourVertices L 0 0) x y =
          idMatrix (Idx L (vertexCells).colourPairs) ⟨(), x⟩ ⟨(), y⟩ := fun x y => by
      by_cases h : x = y
      · subst h
        exact (if_pos rfl).trans (if_pos rfl).symm
      · have h' : (⟨(), x⟩ : Idx L (vertexCells).colourPairs) ≠ ⟨(), y⟩ := fun e' =>
          h (eq_of_heq (Sigma.mk.inj_iff.1 e').2)
        exact (if_neg h).trans (if_neg h').symm
    have hk := gaugeLaplacianAt_eq_compKernel hK hG ι'
      ((colourVertices L 0 0).translate ((2 * L ^ n) • m) ι)
    have hi' := hi ι' ((colourVertices L 0 0).translate ((2 * L ^ n) • m) ι)
    show FullSpace.gaugeLaplacianAt ζ ι' _ + (z : ℂ) • idKernel _ ι' _ = _
    rw [hk, hi']
    rfl
  · obtain ⟨f, rfl⟩ : ∃ f' : Vertex L n 0 0 → ComplexMatrix2, f' = f := ⟨f, rfl⟩
    have hfc := (vertexCoordinates_isRealForm (Vertex L n 0 0)).subset_complex f hf
    obtain ⟨hc₁, hr₁⟩ := hK.quot_diff f hfc
    obtain ⟨hc₂, hr₂⟩ := hK.quot_diffT _ hc₁
    rw [hr₁] at hr₂
    have hr : CellClass.quotCoeffsOn L n vertexCells (gaugeLaplacian V f) =
        applyKernel (compKernel M₂ M₁) (CellClass.quotCoeffsOn L n vertexCells f) := by
      rw [applyKernel_compKernel]
      exact hr₂
    have hA : applyKernel Mh (CellClass.quotCoeffsOn L n vertexCells f) =
        applyKernel (compKernel M₂ M₁) (CellClass.quotCoeffsOn L n vertexCells f) +
          (z : ℂ) • CellClass.quotCoeffsOn L n vertexCells f := by
      rw [hMh, applyKernel_add]
      exact congrArg₂ (· + ·) rfl (applyKernel_smul_unit (z : ℂ) _)
    funext i
    have hR := vertexCoordinates_isRealForm (Vertex L n 0 0)
    have h₁ : (vertexCoordinate (Vertex L n 0 0)).coeffs (gaugeLaplacian V f + z • f) =
        (vertexCoordinate (Vertex L n 0 0)).coeffs (gaugeLaplacian V f) +
          (z : ℂ) • (vertexCoordinate (Vertex L n 0 0)).coeffs f := by
      rw [← ofReal_smul_fun]
      exact (hR.coeffs_add _ hc₂ _ (Submodule.smul_mem _ _ hfc)).trans
        (congrArg₂ (· + ·) rfl (hR.coeffs_smul _ _ hfc))
    refine (congrFun h₁ i).trans ?_
    refine Eq.trans ?_ (applyKernel_equiv ψ Mh (CellClass.quotCoeffsOn L n vertexCells f) i).symm
    rw [hA, ← hr]
    rfl
theorem det_edge_eq (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hC : ProjCellsClassified L n 0 0)
    (hx : ∀ b : Edge L n 0 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hfin : ∀ I : WeightedIndexSet 0, Finite (I.ImageCarrier L n))
    (hSP : DescendsAlgebra (k := 0) L n)
    (hK : HessianKernelsDescend V T₁ T₂ M₁ M₂ M₃) (z : ℝ)
    (ζ : (colourEdges L 0 0).Carrier → ℂ)
    (hζ : FullSpace.expField ζ = liftGaugeField L n 0 0 V)
    (hG : Represents (FullSpace.massiveHessianAt ζ)
      ((FullSpace.edgePauliCoordinates L 0 0).mapOnCoeffs (FullSpace.edgePauliCoordinates L 0 0)
        (FullSpace.massiveHessian (FullSpace.expField ζ))))
    (hT : ∃ T' : edgeFormSpace L n 0 0 →ₗ[ℝ] edgeFormSpace L n 0 0,
      ∀ f : edgeFormSpace L n 0 0, (T' f : Edge L n 0 0 → ComplexMatrix2) = massiveHessian V f) :
    LinearMap.det (linearMapOfEntries (descendMatrix (colourEdges L 0 0) (colourEdges L 0 0)
        (2 * L ^ n) (periodization (colourEdges L 0 0) (colourEdges L 0 0)
          (edgeOpFun L z ζ) (2 * L ^ n)))) =
      ((shiftedDetOn (edgeFormSpace L n 0 0) (massiveHessian V) z : ℝ) : ℂ) := by
  classical
  rw [hζ] at hG
  obtain ⟨hsq, hqq⟩ := edge_proj_classes hC
  let ψ := quotCellEquiv (L := L) (n := n) edgeCells (hC .edge).1
  have : Finite (vertexCells.colourPairs.ImageCarrier L n) := hfin _
  have : Finite (edgeCells.colourPairs.ImageCarrier L n) := hfin _
  have : Finite (edgePauliCoordinates L n 0 0).Index := Finite.of_equiv _ ψ.symm
  obtain ⟨-, -, -, hpl, hpd, -⟩ := hSP (vertexCells).colourPairs (edgeCells).colourPairs
    (edgeCells).colourPairs 2 (by norm_num) T₁ T₁ _ M₁ M₁ M₂ hK.local_diff hK.local_diff
    hK.local_diffT hK.descends_diff hK.descends_diff hK.descends_diffT
  have hl₂ : IsRLocal L (edgeCells).colourPairs (edgeCells).colourPairs (2 * 2) T₂ :=
    fun ι' ι h => hK.local_hessian ι' ι fun h' => h (h'.trans (by norm_num))
  obtain ⟨-, hsl, hsd, -⟩ := hSP (edgeCells).colourPairs (edgeCells).colourPairs
    (edgeCells).colourPairs (2 * 2) (by norm_num) T₂ _ T₂ M₃ _ M₃ hl₂ hpl hl₂
    hK.descends_hessian hpd hK.descends_hessian
  set Mh := (M₃ + compKernel M₁ M₂) +
    (z : ℂ) • idMatrix (edgeCells.colourPairs.ImageCarrier L n) with hMh
  refine det_descendMatrix_eq_shiftedDetOn (r := edgePauliCoordinates L n 0 0) (V := edgeFormSpace L n 0 0)
    (edgePauliCoordinates_isRealForm hx) hT z (colourEdges L 0 0) (2 * L ^ n) hsq hqq
    (M := fun i j => Mh (ψ i) (ψ j)) (fun ι' ι => ?_) fun f hf => ?_
  · have key := periodization_add_smul_id hSP (edgeCells).colourPairs (by norm_num) hsl hsd
      (z : ℂ) (⟨(), ι'⟩ : Idx L (edgeCells).colourPairs) (⟨(), ι⟩ : Idx L (edgeCells).colourPairs)
    refine Eq.trans ?_ key
    refine tsum_congr fun m => ?_
    have hi : ∀ x y : (colourEdges L 0 0).Carrier,
        idKernel (colourEdges L 0 0) x y =
          idMatrix (Idx L (edgeCells).colourPairs) ⟨(), x⟩ ⟨(), y⟩ := fun x y => by
      by_cases h : x = y
      · subst h
        exact (if_pos rfl).trans (if_pos rfl).symm
      · have h' : (⟨(), x⟩ : Idx L (edgeCells).colourPairs) ≠ ⟨(), y⟩ := fun e' =>
          h (eq_of_heq (Sigma.mk.inj_iff.1 e').2)
        exact (if_neg h).trans (if_neg h').symm
    have hk := massiveHessianAt_eq_kernel hL hK hG ι'
      ((colourEdges L 0 0).translate ((2 * L ^ n) • m) ι)
    have hi' := hi ι' ((colourEdges L 0 0).translate ((2 * L ^ n) • m) ι)
    show FullSpace.massiveHessianAt ζ ι' _ + (z : ℂ) • idKernel _ ι' _ = _
    rw [hk, hi']
    rfl
  · obtain ⟨f, rfl⟩ : ∃ f' : Edge L n 0 0 → ComplexMatrix2, f' = f := ⟨f, rfl⟩
    have hR := edgePauliCoordinates_isRealForm (L := L) (n := n) hx
    have hfc := hR.subset_complex f hf
    obtain ⟨hc₁, hr₁⟩ := hK.quot_diffT f hfc
    obtain ⟨hc₂, hr₂⟩ := hK.quot_diff _ hc₁
    obtain ⟨hc₃, hr₃⟩ := hK.quot_hessian f hfc
    rw [hr₁] at hr₂
    have hadd : ∀ g g' : Edge L n 0 0 → ComplexMatrix2, g ∈ complexEdgeForms L n 0 0 →
        g' ∈ complexEdgeForms L n 0 0 → CellClass.quotCoeffsOn L n edgeCells (g + g') =
          CellClass.quotCoeffsOn L n edgeCells g + CellClass.quotCoeffsOn L n edgeCells g' := by
      intro g g' hg hg'
      funext κ
      exact pauliCoeff_add (hg.1 κ.2.1.2.1 κ.2.1.2.2) (hg'.1 κ.2.1.2.1 κ.2.1.2.2) κ.2.1.1
    have hr : CellClass.quotCoeffsOn L n edgeCells (massiveHessian V f) =
        applyKernel (M₃ + compKernel M₁ M₂) (CellClass.quotCoeffsOn L n edgeCells f) := by
      rw [applyKernel_add, applyKernel_compKernel, ← hr₃, ← hr₂]
      exact hadd _ _ hc₃ hc₂
    have hA : applyKernel Mh (CellClass.quotCoeffsOn L n edgeCells f) =
        applyKernel (M₃ + compKernel M₁ M₂) (CellClass.quotCoeffsOn L n edgeCells f) +
          (z : ℂ) • CellClass.quotCoeffsOn L n edgeCells f := by
      rw [hMh, applyKernel_add]
      exact congrArg₂ (· + ·) rfl (applyKernel_smul_unit (z : ℂ) _)
    funext i
    have hmc : massiveHessian V f ∈ complexEdgeForms L n 0 0 := Submodule.add_mem _ hc₃ hc₂
    have h₁ : (edgePauliCoordinates L n 0 0).coeffs (massiveHessian V f + z • f) =
        (edgePauliCoordinates L n 0 0).coeffs (massiveHessian V f) +
          (z : ℂ) • (edgePauliCoordinates L n 0 0).coeffs f := by
      rw [← ofReal_smul_fun]
      exact (hR.coeffs_add _ hmc _ (Submodule.smul_mem _ _ hfc)).trans
        (congrArg₂ (· + ·) rfl (hR.coeffs_smul _ _ hfc))
    refine (congrFun h₁ i).trans ?_
    refine Eq.trans ?_ (applyKernel_equiv ψ Mh (CellClass.quotCoeffsOn L n edgeCells f) i).symm
    rw [hA, ← hr]
    rfl
end Determinants
section Field
variable {L n : ℕ}
theorem matExp_eq_inv_matExp_neg (Z : ComplexMatrix2) :
    ComplexMatrix2.matExp Z = (ComplexMatrix2.matExp (-Z))⁻¹ := by
  have := Matrix.exp_neg (-Z)
  rwa [neg_neg] at this
theorem matExp_I_smul_mem_compact (hE : ComplexMatrix2.ExpLogEstimates) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.matExp_I_smul_mem_specialUnitary <;> assumption
theorem expTwist_identityField_apply {B : Edge L n 0 0 → ComplexMatrix2}
    (hB : ∀ b : Edge L n 0 0, B b.opposite = -B b) (b : Edge L n 0 0) :
    PeriodicLattice.expTwist B (PeriodicOperators.Tempered.identityField L n) b =
      ComplexMatrix2.matExp (Complex.I • B b) := by
  unfold PeriodicLattice.expTwist PeriodicOperators.Tempered.identityField
  split_ifs with h
  · rw [mul_one]
  · rw [mul_one, hB, smul_neg, ← matExp_eq_inv_matExp_neg]
theorem full_expTwist_one_apply {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : ∀ b : FullSpace.Edge L 0 0, B b.opposite = -B b) (b : FullSpace.Edge L 0 0) :
    FullSpace.expTwist B (fun _ => 1) b = ComplexMatrix2.matExp (Complex.I • B b) := by
  unfold FullSpace.expTwist
  split_ifs with h
  · rw [mul_one]
  · rw [mul_one, hB, smul_neg, ← matExp_eq_inv_matExp_neg]
theorem expTwist_mem_fieldsIn (hE : ComplexMatrix2.ExpLogEstimates)
    (hx : ∀ b : Edge L n 0 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {B : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n 0 0) :
    PeriodicLattice.expTwist B (PeriodicOperators.Tempered.identityField L n) ∈
      fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup := by
  have hsu : ∀ b : Edge L n 0 0, B b ∈ ComplexMatrix2.hermitianTraceless := fun b => by
    rcases hx b with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact hB.1 b h₁
    · have h := hB.1 _ h₁
      rw [hB.2 b] at h
      simpa using ComplexMatrix2.hermitianTraceless.neg_mem h
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · rw [expTwist_identityField_apply hB.2]
    exact matExp_I_smul_mem_compact hE (hsu b)
  · rw [expTwist_identityField_apply hB.2, expTwist_identityField_apply hB.2, hB.2 b, smul_neg]
    exact Matrix.exp_neg _
theorem liftQuotField_remainder (hC : ProjCellsClassified L n 0 0)
    (B : Edge L n 0 0 → ComplexMatrix2) :
    liftQuotField (colourEdges L 0 0) (2 * L ^ n) (remainderQuotField B) =
      remainderCoeffs B := by
  obtain ⟨hs, hq⟩ := edge_proj_classes hC
  obtain ⟨φ, hφ⟩ := exists_quotEquiv (colourEdges L 0 0) (2 * L ^ n) _ hs hq
  have hex : ∃ f : (remainderIndex L 0).QuotMod (2 * L ^ n) → ℂ,
      ∀ κ : (remainderIndex L 0).Carrier,
        f ((remainderIndex L 0).mkQuot (2 * L ^ n) κ) = remainderCoeffs B κ :=
    ⟨fun c => (edgePauliCoordinates L n 0 0).coeffs B (φ c), fun κ => by
      show (edgePauliCoordinates L n 0 0).coeffs B (φ ((colourEdges L 0 0).mkQuot _ κ)) = _
      rw [hφ]
      rfl⟩
  funext κ
  exact Classical.epsilon_spec hex κ
theorem fullEdgeBasis_ofCoeffs_remainder (hBi : ProjEdgesCompatible L n 0 0)
    (hrev : ∀ b : FullSpace.Edge L 0 0,
      (FullSpace.projEdge L n 0 0 b).opposite = FullSpace.projEdge L n 0 0 b.opposite)
    {B : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n 0 0)
    (b : FullSpace.Edge L 0 0) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (remainderCoeffs B) b =
      B (FullSpace.projEdge L n 0 0 b) := by
  have hpos : ∀ (p : FullSpace.Edge L 0 0) (hp : p.IsPositivelyOriented),
      ofPauliCoeffs (remainderCoeffs B) ⟨p, hp⟩ = B (FullSpace.projEdge L n 0 0 p) := by
    intro p hp
    have hv := hBi.2.1 ⟨p, hp⟩
    have h := sum_pauliCoeff
      (traceless_of_hermitianTraceless (hB.1 _ (projPositiveEdge L n 0 0 ⟨p, hp⟩).2))
    rw [← hv]
    exact h
  by_cases hb : b.IsPositivelyOriented
  · exact (fullEdgeBasis_ofCoeffs_pos _ hb).trans (hpos b hb)
  · exact (fullEdgeBasis_ofCoeffs_neg _ hb).trans
      ((congrArg Neg.neg (hpos _ _)).trans (by rw [← hrev, hB.2, neg_neg]))
theorem expField_remainderCoeffs (hBi : ProjEdgesCompatible L n 0 0)
    (hrev : ∀ b : FullSpace.Edge L 0 0,
      (FullSpace.projEdge L n 0 0 b).opposite = FullSpace.projEdge L n 0 0 b.opposite)
    {B : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n 0 0) :
    FullSpace.expField (L := L) (remainderCoeffs B) =
      liftGaugeField L n 0 0
        (PeriodicLattice.expTwist B (PeriodicOperators.Tempered.identityField L n)) := by
  have hA := fullEdgeBasis_ofCoeffs_remainder hBi hrev hB
  have hanti : ∀ b : FullSpace.Edge L 0 0,
      (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (remainderCoeffs B) b.opposite =
        -(FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (remainderCoeffs B) b := fun b => by
    rw [hA, hA, ← hrev, hB.2]
  funext b
  show FullSpace.expTwist _ _ b = PeriodicLattice.expTwist B _ (FullSpace.projEdge L n 0 0 b)
  rw [full_expTwist_one_apply hanti, expTwist_identityField_apply hB.2, hA]
end Field
theorem detIdentities_holds (hY : LocalKernels.Periodisation.PeriodisationHolds)
    (hT : TwoOperators.AtTrivialField)
    (hD : HessianDeterminants.HessianSymmAndDetsPositive)
    (hQ : EdgeProjectionProperties)
    (hO : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hE : ComplexMatrix2.ExpLogEstimates) : DetIdentities := by
  intro L hL z hz
  have hall : ∀ n : ℕ, 0 < n → ∀ B ∈ edgeFormSpace L n 0 0, DetsMatch L n z B := by
    intro n hn B hB
    obtain ⟨hcells, hclasses, hSP, hEv, -, hBr, -, hAct, -⟩ := hY L hL 0 n hn
    obtain ⟨hC, hBi⟩ := hcells 0 le_rfl
    have hx := edge_xor_opposite hO hL hn
    have hVr := expTwist_mem_fieldsIn hE hx hB
    have hVc : PeriodicLattice.expTwist B (PeriodicOperators.Tempered.identityField L n) ∈
        fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup :=
      ⟨fun b hb => (Matrix.mem_specialUnitaryGroup_iff.1 (hVr.1 b hb)).2, hVr.2⟩
    obtain ⟨T₁, T₂, M₁, M₂, M₃, hK⟩ :=
      exists_hessianKernels hL hEv hBr (hAct 0 (Nat.zero_le 0)) hVc
    have hrev := fun b => ((hQ L n 0 0 hL hn le_rfl).1 b).2.2.2
    have hfield := liftQuotField_remainder hC B
    have hconf := expField_remainderCoeffs hBi hrev hB
    obtain ⟨-, -, hmaps⟩ := hT L hL
    obtain ⟨hsym₁, hsym₂, -⟩ := ((hD L hL).2 z hz n hn).1 _ hVr
    have hfin : ∀ I : WeightedIndexSet 0, Finite (I.ImageCarrier L n) := fun I => (hclasses I).1
    refine ⟨?_, ?_⟩
    · show LinearMap.det (linearMapOfEntries (descendMatrix _ _ _ (periodization _ _
        (vertexOpFun L z (liftQuotField _ _ _)) _))) = _
      rw [hfield]
      exact det_vertex_eq hC hfin hSP hK z _ hconf (hmaps.laplacian_kernel _) hsym₁.1
    · show LinearMap.det (linearMapOfEntries (descendMatrix _ _ _ (periodization _ _
        (edgeOpFun L z (liftQuotField _ _ _)) _))) = _
      rw [hfield]
      exact det_edge_eq hL hC hx hfin hSP hK z _ hconf (hmaps.massive_kernel _) hsym₂.1
  exact ⟨PeriodicLattice.torusSide L 1, ⟨1, one_pos, rfl⟩, fun s _ _ n hn _ => hall n hn⟩
end YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices
end
