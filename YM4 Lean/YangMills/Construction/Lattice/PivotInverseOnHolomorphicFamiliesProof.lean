import YangMills.Construction.Lattice.EliminationMapOfAFormedSetProof
import YangMills.Construction.Lattice.LinearisedConstraintOnHolomorphicFamilies
import YangMills.Construction.Lattice.PivotInverseOnHolomorphicFamilies
import YangMills.Construction.Matrices.MatrixOperationsKeepHolomorphy
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice
namespace PivotInverse
section Forms
variable {L m : ℕ} {j : ℤ}
theorem isBondForm_singleBondForm {e : Bond L m j} (h : e ≠ e.opposite) {X : ComplexMatrix2}
    (hX : X ∈ complexLieAlgebra) : IsBondForm complexLieAlgebra (singleBondForm e X) := by apply _root_.YangMills.Construction.PeriodicLattice.EliminationConstruction.isBondForm_singleBondForm <;> assumption
theorem singleBondForm_add (e : Bond L m j) (X Y : ComplexMatrix2) :
    singleBondForm e (X + Y) = singleBondForm e X + singleBondForm e Y := by
  funext e'
  simp only [singleBondForm, Pi.add_apply]
  split_ifs <;> simp [add_comm]
theorem singleBondForm_smul (e : Bond L m j) (z : ℂ) (X : ComplexMatrix2) :
    singleBondForm e (z • X) = z • singleBondForm e X := by
  funext e'
  simp only [singleBondForm, Pi.smul_apply]
  split_ifs <;> simp
theorem ne_opposite_of_xor {e : Bond L m j}
    (hx : Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented) : e ≠ e.opposite := by apply _root_.YangMills.Construction.PeriodicLattice.EliminationConstruction.ne_opposite <;> assumption
end Forms
section Linear
variable {L m K k : ℕ}
theorem exists_linearMap_pivotCoeff {V : BondAtLevel L m K k → ComplexMatrix2}
    {c : BondAtLevel L m K (k + 1)} (h : LinearizedConstraintProperties V c)
    (hne : (pivot c : BondAtLevel L m K k) ≠ (pivot c : BondAtLevel L m K k).opposite) :
    ∃ T : ComplexMatrix2.traceless →ₗ[ℂ] ComplexMatrix2.traceless,
      ∀ X : ComplexMatrix2.traceless, (T X : ComplexMatrix2) = pivotCoeff V c X := by
  have hone : ∀ X : ComplexMatrix2.traceless,
      IsBondForm complexLieAlgebra
        (singleBondForm (pivot c : BondAtLevel L m K k) (X : ComplexMatrix2)) :=
    fun X => isBondForm_singleBondForm hne X.2
  refine ⟨{ toFun := fun X => ⟨pivotCoeff V c X, h.mem_complexLieAlgebra _ (hone X)⟩,
            map_add' := fun X Y => Subtype.ext ?_,
            map_smul' := fun z X => Subtype.ext ?_ }, fun X => rfl⟩
  · change linearizedConstraint V (singleBondForm _ ((X : ComplexMatrix2) + Y)) c =
      linearizedConstraint V (singleBondForm _ (X : ComplexMatrix2)) c +
        linearizedConstraint V (singleBondForm _ (Y : ComplexMatrix2)) c
    rw [singleBondForm_add, h.map_add _ _ (hone X) (hone Y)]
  · change linearizedConstraint V (singleBondForm _ (z • (X : ComplexMatrix2))) c =
      z • linearizedConstraint V (singleBondForm _ (X : ComplexMatrix2)) c
    rw [singleBondForm_smul, h.map_smul _ _ (hone X)]
theorem pivotCoeffInv_eq_symm {V : BondAtLevel L m K k → ComplexMatrix2}
    {c : BondAtLevel L m K (k + 1)}
    (T : ComplexMatrix2.traceless ≃ₗ[ℂ] ComplexMatrix2.traceless)
    (hT : ∀ X : ComplexMatrix2.traceless, (T X : ComplexMatrix2) = pivotCoeff V c X)
    (y : ComplexMatrix2.traceless) :
    pivotCoeffInv V c (y : ComplexMatrix2) = (T.symm y : ComplexMatrix2) := by
  have hex : ∃ a ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2),
      pivotCoeff V c a = (y : ComplexMatrix2) :=
    ⟨(T.symm y : ComplexMatrix2), (T.symm y).2, by rw [← hT]; simp⟩
  have hmem : pivotCoeffInv V c (y : ComplexMatrix2) ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2) :=
    Function.invFunOn_mem hex
  have heq : pivotCoeff V c (pivotCoeffInv V c (y : ComplexMatrix2)) = (y : ComplexMatrix2) :=
    Function.invFunOn_eq hex
  have hfix : T ⟨_, hmem⟩ = y := Subtype.ext (by rw [hT]; exact heq)
  exact congrArg Subtype.val (T.eq_symm_apply.2 hfix)
end Linear
section Scalars
variable {ι κ : Type} [Fintype ι] [Fintype κ] {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
  {W : Set (ι ⊕ κ → ComplexMatrix2)}
def IsScalarHolomorphic (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (ι ⊕ κ → ComplexMatrix2)) (s : (ι ⊕ κ → ComplexMatrix2) → ℂ) : Prop :=
  GroupLieProduct.IsHolomorphicToMatrixEntries b W fun p => s p • (1 : ComplexMatrix2)
variable (hM : GroupLieProduct.HolomorphyClosureStatement)
  (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
include hM hW
theorem holo_const (X : ComplexMatrix2) :
    GroupLieProduct.IsHolomorphicToMatrixEntries b W fun _ => X :=
  (hM ι κ b W hW).1 X
theorem holo_add {Φ Ψ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : GroupLieProduct.IsHolomorphicToMatrixEntries b W Φ)
    (hΨ : GroupLieProduct.IsHolomorphicToMatrixEntries b W Ψ) :
    GroupLieProduct.IsHolomorphicToMatrixEntries b W fun p => Φ p + Ψ p :=
  (hM ι κ b W hW).2.2.1 Φ Ψ hΦ hΨ
theorem holo_mul {Φ Ψ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : GroupLieProduct.IsHolomorphicToMatrixEntries b W Φ)
    (hΨ : GroupLieProduct.IsHolomorphicToMatrixEntries b W Ψ) :
    GroupLieProduct.IsHolomorphicToMatrixEntries b W fun p => Φ p * Ψ p :=
  (hM ι κ b W hW).2.2.2.1 Φ Ψ hΦ hΨ
theorem holo_linear (l : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2)
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : GroupLieProduct.IsHolomorphicToMatrixEntries b W Φ) :
    GroupLieProduct.IsHolomorphicToMatrixEntries b W fun p => l (Φ p) :=
  (hM ι κ b W hW).2.2.2.2.1 l Φ hΦ
theorem holo_inv {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : GroupLieProduct.IsHolomorphicToMatrixEntries b W Φ)
    (hu : ∀ p ∈ W, IsUnit (Φ p).det) :
    GroupLieProduct.IsHolomorphicToMatrixEntries b W fun p => (Φ p)⁻¹ :=
  (hM ι κ b W hW).2.2.2.2.2.1 Φ hΦ hu
theorem isRelativelyOpen_preimage {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : GroupLieProduct.IsHolomorphicToMatrixEntries b W Φ) {O : Set ComplexMatrix2}
    (hO : IsOpen O) : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) (W ∩ Φ ⁻¹' O) :=
  (hM ι κ b W hW).2.2.2.2.2.2.2.2.1 Φ hΦ O hO
theorem holo_mono {W' : Set (ι ⊕ κ → ComplexMatrix2)} (hsub : W' ⊆ W)
    (hW' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W')
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : GroupLieProduct.IsHolomorphicToMatrixEntries b W Φ) :
    GroupLieProduct.IsHolomorphicToMatrixEntries b W' Φ :=
  (hM ι κ b W hW).2.2.2.2.2.2.2.2.2.1 W' hsub hW' Φ hΦ
theorem holo_congr {Φ Ψ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : GroupLieProduct.IsHolomorphicToMatrixEntries b W Φ) (h : EqOn Ψ Φ W) :
    GroupLieProduct.IsHolomorphicToMatrixEntries b W Ψ :=
  (hM ι κ b W hW).2.2.2.2.2.2.2.2.2.2 Φ Ψ hΦ h
theorem holo_sum {σ : Type} (S : Finset σ) {Φ : σ → (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (h : ∀ i ∈ S, GroupLieProduct.IsHolomorphicToMatrixEntries b W (Φ i)) :
    GroupLieProduct.IsHolomorphicToMatrixEntries b W fun p => ∑ i ∈ S, Φ i p := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using holo_const hM hW (0 : ComplexMatrix2)
  | insert i S hi ih =>
    have h₁ := h i (Finset.mem_insert_self i S)
    have h₂ := ih fun a ha => h a (Finset.mem_insert_of_mem ha)
    refine holo_congr hM hW (holo_add hM hW h₁ h₂) fun p _ => ?_
    exact Finset.sum_insert hi
theorem scalarHolo_const (z : ℂ) : IsScalarHolomorphic b W fun _ => z :=
  holo_const hM hW _
theorem scalarHolo_mul {s t : (ι ⊕ κ → ComplexMatrix2) → ℂ} (hs : IsScalarHolomorphic b W s)
    (ht : IsScalarHolomorphic b W t) : IsScalarHolomorphic b W fun p => s p * t p :=
  holo_congr hM hW (holo_mul hM hW hs ht) fun p _ => by
    simp [smul_smul, mul_comm]
theorem scalarHolo_sum {σ : Type} (S : Finset σ) {s : σ → (ι ⊕ κ → ComplexMatrix2) → ℂ}
    (h : ∀ i ∈ S, IsScalarHolomorphic b W (s i)) :
    IsScalarHolomorphic b W fun p => ∑ i ∈ S, s i p :=
  holo_congr hM hW (holo_sum hM hW S h) fun _ _ => Finset.sum_smul
theorem scalarHolo_prod {σ : Type} (S : Finset σ) {s : σ → (ι ⊕ κ → ComplexMatrix2) → ℂ}
    (h : ∀ i ∈ S, IsScalarHolomorphic b W (s i)) :
    IsScalarHolomorphic b W fun p => ∏ i ∈ S, s i p := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using scalarHolo_const hM hW (1 : ℂ)
  | insert i S hi ih =>
    have h₁ := h i (Finset.mem_insert_self i S)
    have h₂ := ih fun a ha => h a (Finset.mem_insert_of_mem ha)
    have h₃ := scalarHolo_mul hM hW h₁ h₂
    refine holo_congr hM hW h₃ fun p _ => ?_
    simp only [Finset.prod_insert hi]
theorem scalarHolo_det {B : (ι ⊕ κ → ComplexMatrix2) → Matrix (Fin 3) (Fin 3) ℂ}
    (h : ∀ i j, IsScalarHolomorphic b W fun p => B p i j) :
    IsScalarHolomorphic b W fun p => (B p).det := by
  have h₁ := scalarHolo_sum hM hW (Finset.univ : Finset (Equiv.Perm (Fin 3)))
    (s := fun σ p => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, B p (σ i) i)
    fun σ _ => scalarHolo_mul hM hW (scalarHolo_const hM hW _)
      (scalarHolo_prod hM hW Finset.univ fun i _ => h (σ i) i)
  refine holo_congr hM hW h₁ fun p _ => ?_
  simp only [Matrix.det_apply']
theorem scalarHolo_inv {s : (ι ⊕ κ → ComplexMatrix2) → ℂ} (hs : IsScalarHolomorphic b W s)
    (h : ∀ p ∈ W, s p ≠ 0) : IsScalarHolomorphic b W fun p => (s p)⁻¹ := by
  have hu : ∀ p ∈ W, IsUnit (s p • (1 : ComplexMatrix2)).det := fun p hp => by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact (pow_ne_zero _ (h p hp)).isUnit
  refine holo_congr hM hW (holo_inv hM hW hs hu) fun p hp => ?_
  refine (Matrix.inv_eq_left_inv ?_).symm
  simp [smul_smul, h p hp]
end Scalars
theorem exists_coord_extension (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (j : Fin 3) :
    ∃ l : ComplexMatrix2 →ₗ[ℂ] ℂ, ∀ X : ComplexMatrix2.traceless, l (X : ComplexMatrix2) = b.repr X j := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (b.coord j)
  exact ⟨g, fun X => by simpa using congrArg (fun f => f X) hg⟩
def toScalarMatrix (l : ComplexMatrix2 →ₗ[ℂ] ℂ) : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 :=
  (LinearMap.toSpanSingleton ℂ ComplexMatrix2 1).comp l
end PivotInverse
open PivotInverse in
theorem PivotInverse.pivotInverseHolomorphic
    (hF : LinearizedConstraintAtBond.Statement)
    (hH : HolomorphicConstraint.claim)
    (hM : GroupLieProduct.HolomorphyClosureStatement)
    (hX : LevelBondOrientationDichotomy) :
    PivotInverseHolomorphic := by
  intro L m K k hL hm hk ι κ _ _ b W U hU c hc hWU
  have hW := hU.isOpen
  have hne : (pivot c : BondAtLevel L m K k) ≠ (pivot c : BondAtLevel L m K k).opposite :=
    ne_opposite_of_xor (hX L m K hL hm (by omega) k hk.le _)
  choose coord hcoord using exists_coord_extension b
  let A : (ι ⊕ κ → ComplexMatrix2) → Matrix (Fin 3) (Fin 3) ℂ := fun p =>
    Matrix.of fun j i => coord j (pivotCoeff (U p) c (b i : ComplexMatrix2))
  have hA : ∀ j i, IsScalarHolomorphic b W fun p => A p j i := by
    intro j i
    have hform : IsHolomorphicBondFormFamily b W
        fun _ => singleBondForm (pivot c : BondAtLevel L m K k) (b i : ComplexMatrix2) :=
      ⟨hW, fun _ _ => isBondForm_singleBondForm hne (b i).2, fun e => holo_const hM hW _⟩
    have h₁ := ((hH L m K k hL hm hk ι κ b W U hU c hc hWU).1 _ hform).2
    exact holo_linear hM hW (toScalarMatrix (coord j)) h₁
  have hD : IsScalarHolomorphic b W fun p => (A p).det := scalarHolo_det hM hW hA
  have hlin : ∀ p ∈ W, ∃ T : ComplexMatrix2.traceless →ₗ[ℂ] ComplexMatrix2.traceless,
      (∀ X : ComplexMatrix2.traceless, (T X : ComplexMatrix2) = pivotCoeff (U p) c X) ∧
        LinearMap.toMatrix b b T = A p := by
    intro p hp
    obtain ⟨T, hT⟩ := exists_linearMap_pivotCoeff (hF L m K k hL hm hk (U p) c hc (hWU p hp)) hne
    refine ⟨T, hT, ?_⟩
    ext j i
    rw [LinearMap.toMatrix_apply]
    change _ = coord j (pivotCoeff (U p) c (b i : ComplexMatrix2))
    rw [← hT, hcoord]
  have hiff : ∀ p ∈ W, PivotCoeffInvertible (U p) c ↔ (A p).det ≠ 0 := by
    intro p hp
    obtain ⟨T, hT, hTA⟩ := hlin p hp
    rw [← hTA, LinearMap.det_toMatrix]
    constructor
    · rintro ⟨E, hE⟩
      have e : (E : ComplexMatrix2.traceless →ₗ[ℂ] ComplexMatrix2.traceless) = T :=
        LinearMap.ext fun X => Subtype.ext (by rw [hT, ← hE]; rfl)
      rw [← e]
      exact (LinearEquiv.isUnit_det' E).ne_zero
    · intro h
      exact ⟨LinearMap.equivOfDetNeZero T h, fun X => by rw [← hT]; rfl⟩
  have hset : {p | p ∈ W ∧ PivotCoeffInvertible (U p) c} =
      W ∩ (fun p => (A p).det • (1 : ComplexMatrix2)) ⁻¹' {X : ComplexMatrix2 | X 0 0 ≠ 0} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hp, hi⟩
      exact ⟨hp, by simpa using (hiff p hp).1 hi⟩
    · rintro ⟨hp, hi⟩
      exact ⟨hp, (hiff p hp).2 (by simpa using hi)⟩
  have hO : IsOpen {X : ComplexMatrix2 | X 0 0 ≠ 0} :=
    isOpen_ne_fun (continuous_id.matrix_elem 0 0) continuous_const
  have hW' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ)
      {p | p ∈ W ∧ PivotCoeffInvertible (U p) c} := by
    rw [hset]
    exact isRelativelyOpen_preimage hM hW hD hO
  refine ⟨hW', fun ν hν => ?_⟩
  set W' := {p | p ∈ W ∧ PivotCoeffInvertible (U p) c} with hWdef
  have hsub : W' ⊆ W := fun p hp => hp.1
  have hA' : ∀ j i, IsScalarHolomorphic b W' fun p => A p j i :=
    fun j i => holo_mono hM hW hsub hW' (hA j i)
  have hD' : IsScalarHolomorphic b W' fun p => (A p).det := scalarHolo_det hM hW' hA'
  have hDinv : IsScalarHolomorphic b W' fun p => ((A p).det)⁻¹ :=
    scalarHolo_inv hM hW' hD' fun p hp => (hiff p hp.1).1 hp.2
  have hadj : ∀ j i, IsScalarHolomorphic b W' fun p => (A p).adjugate j i := by
    intro j i
    have h₁ : IsScalarHolomorphic b W' fun p => ((A p).updateRow i (Pi.single j 1)).det := by
      refine scalarHolo_det hM hW' fun r s => ?_
      by_cases hr : r = i
      · subst hr
        simpa using scalarHolo_const hM hW' ((Pi.single j (1 : ℂ) : Fin 3 → ℂ) s)
      · simpa [Matrix.updateRow_ne hr] using hA' r s
    refine holo_congr hM hW' h₁ fun p _ => ?_
    simp only [Matrix.adjugate_apply]
  have hn : ∀ i, IsScalarHolomorphic b W' fun p => coord i (ν p) :=
    fun i => holo_linear hM hW' (toScalarMatrix (coord i)) hν.2
  let x : Fin 3 → (ι ⊕ κ → ComplexMatrix2) → ℂ := fun j p =>
    ((A p).det)⁻¹ * ∑ i, (A p).adjugate j i * coord i (ν p)
  have hx : ∀ j, IsScalarHolomorphic b W' (x j) := fun j =>
    scalarHolo_mul hM hW' hDinv (scalarHolo_sum hM hW' Finset.univ fun i _ =>
      scalarHolo_mul hM hW' (hadj j i) (hn i))
  have hres : GroupLieProduct.IsHolomorphicToMatrixEntries b W'
      fun p => ∑ j, (x j p • (1 : ComplexMatrix2)) * (b j : ComplexMatrix2) :=
    holo_sum hM hW' Finset.univ fun j _ => holo_mul hM hW' (hx j) (holo_const hM hW' _)
  have hval : ∀ p ∈ W', ∃ z : ComplexMatrix2.traceless,
      pivotCoeffInv (U p) c (ν p) = (z : ComplexMatrix2) ∧
        (z : ComplexMatrix2) = ∑ j, (x j p • (1 : ComplexMatrix2)) * (b j : ComplexMatrix2) := by
    intro p hp
    obtain ⟨E, hE⟩ := hp.2
    obtain ⟨T, hT, hTA⟩ := hlin p hp.1
    have hdet : (A p).det ≠ 0 := (hiff p hp.1).1 hp.2
    have hETe : ∀ X : ComplexMatrix2.traceless, T X = E X := fun X =>
      Subtype.ext (by rw [hT, hE])
    let y : ComplexMatrix2.traceless := ⟨ν p, hν.1 hp⟩
    let z : ComplexMatrix2.traceless := E.symm y
    have hrepr : (A p).mulVec (b.repr z) = b.repr y := by
      rw [← hTA, LinearMap.toMatrix_mulVec_repr, hETe]
      simp [z]
    have hy : ∀ i, (b.repr y : Fin 3 → ℂ) i = coord i (ν p) := fun i => (hcoord i y).symm
    have hz : ∀ j, b.repr z j = x j p := by
      intro j
      have h₁ : (A p).adjugate.mulVec ((A p).mulVec (b.repr z)) =
          (A p).det • (b.repr z : Fin 3 → ℂ) := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [hrepr] at h₁
      have h₂ := congrFun h₁ j
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hy] at h₂
      change b.repr z j = ((A p).det)⁻¹ * _
      rw [h₂, inv_mul_cancel_left₀ hdet]
    refine ⟨z, pivotCoeffInv_eq_symm E hE y, ?_⟩
    have hsum := congrArg (Subtype.val) (b.sum_repr z)
    rw [← hsum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hz j]
    simp
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨z, e, _⟩ := hval p hp
    change pivotCoeffInv (U p) c (ν p) ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2)
    rw [e]
    exact z.2
  · refine holo_congr hM hW' hres fun p hp => ?_
    obtain ⟨z, e₁, e₂⟩ := hval p hp
    exact e₁.trans e₂
end PeriodicLattice
end YangMills.Construction
