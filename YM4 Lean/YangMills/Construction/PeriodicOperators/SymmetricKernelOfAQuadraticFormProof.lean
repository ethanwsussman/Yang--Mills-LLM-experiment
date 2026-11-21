import YangMills.Construction.PeriodicOperators.SymmetricKernelOfAQuadraticForm
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SymmetricKernels
section KernelFacts
variable {I : Type} {w : I → ℝ}
private theorem kernelPairing_eq_double_sum (w : I → ℝ) (K : KernelMatrix I I) {g' g : I → ℂ}
    {t' t : Finset I} (ht' : Function.support g' ⊆ t') (ht : Function.support g ⊆ t) :
    kernelPairing w K g' g = ∑ j' ∈ t', ∑ j ∈ t, (w j' : ℂ) * g' j' * K j' j * g j := by
  classical
  unfold kernelPairing
  rw [finsum_eq_sum_of_support_subset (s := t' ×ˢ t), Finset.sum_product]
  intro q hq
  have hq' : (w q.1 : ℂ) * g' q.1 * K q.1 q.2 * g q.2 ≠ 0 := hq
  have n1 : g' q.1 ≠ 0 := fun h => hq' (by simp [h])
  have n2 : g q.2 ≠ 0 := fun h => hq' (by simp [h])
  have m1 : q.1 ∈ t' := by exact_mod_cast ht' n1
  have m2 : q.2 ∈ t := by exact_mod_cast ht n2
  exact_mod_cast Finset.mem_product.2 ⟨m1, m2⟩
private theorem support_finite (g : finsuppFunctions I) :
    (Function.support (g : I → ℂ)).Finite := g.2
private theorem support_subset_toFinset (g : finsuppFunctions I) :
    Function.support (g : I → ℂ) ⊆ ((support_finite g).toFinset : Set I) := by
  simp
private theorem basisFunction_apply (j x : I) :
    (basisFunction j : I → ℂ) x = (open Classical in if x = j then 1 else 0) := rfl
private theorem eq_sum_smul_basis (g : finsuppFunctions I) {t : Finset I}
    (ht : Function.support (g : I → ℂ) ⊆ t) :
    g = ∑ j ∈ t, (g : I → ℂ) j • basisFunction j := by
  classical
  apply Subtype.ext
  funext x
  have hexp : ((∑ j ∈ t, (g : I → ℂ) j • basisFunction j : finsuppFunctions I) : I → ℂ) x
      = ∑ j ∈ t, (g : I → ℂ) j * (basisFunction j : I → ℂ) x := by
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    rfl
  rw [hexp]
  simp only [basisFunction_apply]
  by_cases hx : x ∈ t
  · simp [hx]
  · have hg0 : (g : I → ℂ) x = 0 := by
      by_contra hn
      exact hx (by exact_mod_cast ht hn)
    simp [hx, hg0]
private theorem bilin_eq_double_sum
    (B : finsuppFunctions I →ₗ[ℂ] finsuppFunctions I →ₗ[ℂ] ℂ)
    (g' g : finsuppFunctions I) {t' t : Finset I}
    (ht' : Function.support (g' : I → ℂ) ⊆ t') (ht : Function.support (g : I → ℂ) ⊆ t) :
    B g' g = ∑ j' ∈ t', ∑ j ∈ t,
      (g' : I → ℂ) j' * (g : I → ℂ) j * B (basisFunction j') (basisFunction j) := by
  have d1 := eq_sum_smul_basis g' ht'
  have d2 := eq_sum_smul_basis g ht
  calc B g' g = B (∑ j' ∈ t', (g' : I → ℂ) j' • basisFunction j')
        (∑ j ∈ t, (g : I → ℂ) j • basisFunction j) := by rw [← d1, ← d2]
    _ = _ := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      ring
private theorem kernelPairing_basis (K : KernelMatrix I I) (p q : I) :
    kernelPairing w K (basisFunction p : I → ℂ) (basisFunction q : I → ℂ) = (w p : ℂ) * K p q := by
  have hsupp : ∀ c : I, Function.support (basisFunction c : I → ℂ) ⊆ (({c} : Finset I) : Set I) := by
    intro c x hx
    by_contra hc
    apply hx
    rw [basisFunction_apply]
    exact if_neg (by simpa using hc)
  rw [kernelPairing_eq_double_sum w K (hsupp p) (hsupp q)]
  simp [basisFunction_apply]
private theorem kernel_eq_of_pairing_eq (hw : ∀ j, 0 < w j) {K K' : KernelMatrix I I}
    (h : ∀ g g' : finsuppFunctions I, kernelPairing w K g' g = kernelPairing w K' g' g) :
    K = K' := by
  funext p q
  have e := h (basisFunction q) (basisFunction p)
  rw [kernelPairing_basis, kernelPairing_basis] at e
  have hne : (w p : ℂ) ≠ 0 := by exact_mod_cast (hw p).ne'
  exact mul_left_cancel₀ hne e
private theorem kernelPairing_bilinKernel (hw : ∀ j, 0 < w j)
    (B : finsuppFunctions I →ₗ[ℂ] finsuppFunctions I →ₗ[ℂ] ℂ)
    (g g' : finsuppFunctions I) :
    kernelPairing w (bilinKernel w B) g' g = B g' g := by
  rw [kernelPairing_eq_double_sum w _ (support_subset_toFinset g') (support_subset_toFinset g),
    bilin_eq_double_sum B g' g (support_subset_toFinset g') (support_subset_toFinset g)]
  refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun j _ => ?_
  have hne : (w j' : ℂ) ≠ 0 := by exact_mod_cast (hw j').ne'
  simp only [bilinKernel]
  push_cast
  field_simp
private theorem kernelPairing_wTranspose (hw : ∀ j, 0 < w j) (K : KernelMatrix I I)
    (g g' : finsuppFunctions I) :
    kernelPairing w (wTranspose w w K) g' g = kernelPairing w K g g' := by
  rw [kernelPairing_eq_double_sum w _ (support_subset_toFinset g') (support_subset_toFinset g),
    kernelPairing_eq_double_sum w _ (support_subset_toFinset g) (support_subset_toFinset g'),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  have hne : (w j' : ℂ) ≠ 0 := by exact_mod_cast (hw j').ne'
  simp only [wTranspose]
  push_cast
  field_simp
private theorem kernelPairing_half_add (K K' : KernelMatrix I I)
    (g g' : finsuppFunctions I) :
    kernelPairing w ((1 / 2 : ℂ) • (K + K')) g' g =
      (1 / 2 : ℂ) * (kernelPairing w K g' g + kernelPairing w K' g' g) := by
  rw [kernelPairing_eq_double_sum w _ (support_subset_toFinset g') (support_subset_toFinset g),
    kernelPairing_eq_double_sum w K (support_subset_toFinset g') (support_subset_toFinset g),
    kernelPairing_eq_double_sum w K' (support_subset_toFinset g') (support_subset_toFinset g)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring
private theorem kernelPairing_add_self (K : KernelMatrix I I)
    (g' g : finsuppFunctions I) :
    kernelPairing w K ((g' + g : finsuppFunctions I) : I → ℂ)
        ((g' + g : finsuppFunctions I) : I → ℂ) =
      kernelPairing w K g' g' + kernelPairing w K g' g + kernelPairing w K g g' +
        kernelPairing w K g g := by
  classical
  set t : Finset I := (support_finite g').toFinset ∪ (support_finite g).toFinset with ht
  have s' : Function.support (g' : I → ℂ) ⊆ t := (support_subset_toFinset g').trans (by
    rw [ht, Finset.coe_union]; exact subset_union_left)
  have s : Function.support (g : I → ℂ) ⊆ t := (support_subset_toFinset g).trans (by
    rw [ht, Finset.coe_union]; exact subset_union_right)
  have sadd : Function.support ((g' + g : finsuppFunctions I) : I → ℂ) ⊆ t := by
    intro x hx
    by_contra hxt
    apply hx
    have z1 : (g' : I → ℂ) x = 0 := by
      by_contra hn
      exact hxt (s' hn)
    have z2 : (g : I → ℂ) x = 0 := by
      by_contra hn
      exact hxt (s hn)
    change (g' : I → ℂ) x + (g : I → ℂ) x = 0
    rw [z1, z2, add_zero]
  rw [kernelPairing_eq_double_sum w K sadd sadd, kernelPairing_eq_double_sum w K s' s',
    kernelPairing_eq_double_sum w K s' s, kernelPairing_eq_double_sum w K s s',
    kernelPairing_eq_double_sum w K s s]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun j _ => ?_
  change (w j' : ℂ) * ((g' : I → ℂ) j' + (g : I → ℂ) j') * K j' j *
    ((g' : I → ℂ) j + (g : I → ℂ) j) = _
  ring
private theorem bilinFormKernel_holds (hw : ∀ j, 0 < w j)
    (B : finsuppFunctions I →ₗ[ℂ] finsuppFunctions I →ₗ[ℂ] ℂ) :
    BilinFormKernel w B := by
  have hK := kernelPairing_bilinKernel hw B
  have hT : ∀ g g' : finsuppFunctions I,
      kernelPairing w (wTranspose w w (bilinKernel w B)) g' g = B g g' := fun g g' =>
    (kernelPairing_wTranspose hw _ g g').trans (hK g' g)
  refine ⟨ExistsUnique.intro _ hK fun K' hK' => kernel_eq_of_pairing_eq hw fun g g' =>
    (hK' g g').trans (hK g g').symm, hK, hT, ?_, ?_⟩
  · intro hs g g'
    have e : wTranspose w w (bilinKernel w B) = bilinKernel w B := hs
    calc B g' g = kernelPairing w (bilinKernel w B) g' g := (hK g g').symm
      _ = kernelPairing w (wTranspose w w (bilinKernel w B)) g' g := by rw [e]
      _ = B g g' := hT g g'
  · intro hsym
    exact kernel_eq_of_pairing_eq hw fun g g' => (hT g g').trans ((hsym g g').symm.trans (hK g g').symm)
private theorem quadFormKernel_holds (hw : ∀ j, 0 < w j)
    (B : finsuppFunctions I →ₗ[ℂ] finsuppFunctions I →ₗ[ℂ] ℂ) :
    QuadFormKernel w B := by
  have hK := kernelPairing_bilinKernel hw B
  have hT : ∀ g g' : finsuppFunctions I,
      kernelPairing w (wTranspose w w (bilinKernel w B)) g' g = B g g' := fun g g' =>
    (kernelPairing_wTranspose hw _ g g').trans (hK g' g)
  have hhalf : ∀ g g' : finsuppFunctions I,
      kernelPairing w ((1 / 2 : ℂ) • (bilinKernel w B +
        wTranspose w w (bilinKernel w B))) g' g = (1 / 2 : ℂ) * (B g' g + B g g') := by
    intro g g'
    rw [kernelPairing_half_add, hK g g', hT g g']
  have hsymm : IsSymmKernel w ((1 / 2 : ℂ) • (bilinKernel w B +
      wTranspose w w (bilinKernel w B))) := by
    refine kernel_eq_of_pairing_eq hw fun g g' => ?_
    rw [kernelPairing_wTranspose hw, hhalf g' g, hhalf g g', add_comm]
  have hdiag : ∀ g : finsuppFunctions I,
      kernelPairing w ((1 / 2 : ℂ) • (bilinKernel w B +
        wTranspose w w (bilinKernel w B))) g g = B g g := by
    intro g
    rw [hhalf g g]
    ring
  refine ⟨ExistsUnique.intro _ ⟨hsymm, hdiag⟩ ?_, ⟨hsymm, hdiag⟩, ?_⟩
  · rintro K' ⟨hs, hK'⟩
    refine kernel_eq_of_pairing_eq hw fun g g' => ?_
    have hcomm : kernelPairing w K' g g' = kernelPairing w K' g' g := by
      have e : wTranspose w w K' = K' := hs
      have tr := kernelPairing_wTranspose hw K' g g'
      rw [e] at tr
      exact tr.symm
    have h3 := hK' (g' + g)
    rw [kernelPairing_add_self, hK' g', hK' g, hcomm] at h3
    have hB : B (g' + g) (g' + g) = B g' g' + B g' g + B g g' + B g g := by
      simp only [map_add, LinearMap.add_apply]
      ring
    rw [hB] at h3
    rw [hhalf g g']
    linear_combination (1 / 2 : ℂ) * h3
  · intro hs
    refine kernel_eq_of_pairing_eq hw fun g g' => ?_
    rw [hhalf g g', hK g g', hs g g']
    ring
end KernelFacts
section PauliComponentsOfSymmetricKernel
private theorem coe_eq_sum_pauliFamily (A : Matrices.ComplexMatrix2.traceless) :
    (A : Matrices.ComplexMatrix2) =
      ∑ c, OneLoop.pauliCoordinateEquiv A c • Matrices.ComplexMatrix2.pauliFamily c := by
  have key : ∀ z : Fin 3 → ℂ,
      ((OneLoop.pauliCoordinateEquiv.symm z : Matrices.ComplexMatrix2.traceless) :
        Matrices.ComplexMatrix2) = ∑ c, z c • Matrices.ComplexMatrix2.pauliFamily c := by
    intro z
    rw [Fin.sum_univ_three]
    rfl
  have h := key (OneLoop.pauliCoordinateEquiv A)
  rwa [LinearEquiv.symm_apply_apply] at h
abbrev _root_.YangMills.SharedProofs.p15988 := @coe_eq_sum_pauliFamily
private theorem halfTrace_mul_eq_sum (hP : OneLoop.PauliMatrixRelations)
    {A C : Matrices.ComplexMatrix2}
    (hA : A ∈ Matrices.ComplexMatrix2.traceless) (hC : C ∈ Matrices.ComplexMatrix2.traceless) :
    Matrices.ComplexMatrix2.halfTrace (A * C) =
      ∑ c, Tower.pauliCoeff c A * Tower.pauliCoeff c C := by
  have h := hP.2.2.2.2.1 ⟨A, hA⟩ ⟨C, hC⟩ _ _ (coe_eq_sum_pauliFamily _) (coe_eq_sum_pauliFamily _)
  simp only [Tower.pauliCoeff, dif_pos hA, dif_pos hC]
  exact h
abbrev _root_.YangMills.SharedProofs.p22145 := @halfTrace_mul_eq_sum
private theorem pauliCoeff_zero (c : Fin 3) : Tower.pauliCoeff c 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private theorem pauliCoordsRepresentation_holds (hP : OneLoop.PauliMatrixRelations) (S : Type) (r : ℝ) :
    HasPauliCoordinates S r := by
  intro F F' hF hF' hfin _
  have hval : ∀ {G : S → Matrices.ComplexMatrix2},
      G ∈ Matrices.GroupLieProduct.tracelessFunctions S →
        ∀ x, G x ∈ Matrices.ComplexMatrix2.traceless :=
    fun hG x => Submodule.mem_pi.1 hG x (mem_univ x)
  have hzero : ∀ (c : Fin 3) (x : S), F x = 0 → Tower.toPauliCoeffs F (c, x) = 0 := by
    intro c x hx
    change Tower.pauliCoeff c (F x) = 0
    rw [hx, pauliCoeff_zero]
  have hmain : ∀ v : ℝ, (v : ℂ) * Tower.traceFinsumPairing F F' =
      wPairing (fun _ : Fin 3 × S => v) (Tower.toPauliCoeffs F) (Tower.toPauliCoeffs F') := by
    intro v
    classical
    have e1 : Tower.traceFinsumPairing F F' =
        ∑ x ∈ hfin.toFinset, Matrices.ComplexMatrix2.halfTrace (F x * F' x) := by
      unfold Tower.traceFinsumPairing
      refine finsum_eq_sum_of_support_subset _ fun x hx => ?_
      have hx' : Matrices.ComplexMatrix2.halfTrace (F x * F' x) ≠ 0 := hx
      have hne : F x ≠ 0 := fun h0 => hx' (by simp [h0, Matrices.ComplexMatrix2.halfTrace])
      exact Finset.mem_coe.2 (hfin.mem_toFinset.2 (Function.mem_support.2 hne))
    have e2 : wPairing (fun _ : Fin 3 × S => v) (Tower.toPauliCoeffs F) (Tower.toPauliCoeffs F') =
        ∑ q ∈ (Finset.univ : Finset (Fin 3)) ×ˢ hfin.toFinset, (v : ℂ) *
          (Tower.toPauliCoeffs F q * Tower.toPauliCoeffs F' q) := by
      unfold wPairing
      refine tsum_eq_sum fun q hq => ?_
      have hx : F q.2 = 0 := by
        by_contra hne
        exact hq (Finset.mem_product.2 ⟨Finset.mem_univ _, hfin.mem_toFinset.2 (Function.mem_support.2 hne)⟩)
      have e : Tower.toPauliCoeffs F q = 0 := hzero q.1 q.2 hx
      rw [e]
      simp
    rw [e1, e2, Finset.sum_product_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [halfTrace_mul_eq_sum hP (hval hF x) (hval hF' x), Finset.mul_sum]
    rfl
  refine ⟨?_, fun v _ => hmain v, ?_, rfl⟩
  · refine ((finite_univ (α := Fin 3)).prod hfin).subset fun q hq => ⟨mem_univ _, fun h0 => hq ?_⟩
    exact hzero q.1 q.2 h0
  · have h := hmain 1
    rwa [Complex.ofReal_one, one_mul] at h
end PauliComponentsOfSymmetricKernel
theorem claim_holds (hP : OneLoop.PauliMatrixRelations) : Claim :=
  ⟨fun _ _ hw B => ⟨bilinFormKernel_holds hw B, quadFormKernel_holds hw B⟩,
    fun _ _ _ _ _ _ => ⟨pauliCoordsRepresentation_holds hP _ _, fun _ _ => pauliCoordsRepresentation_holds hP _ _⟩⟩
end YangMills.Construction.PeriodicOperators.SymmetricKernels
end
