import YangMills.Construction.Lattice.LatticeBoxKernel
import YangMills.Construction.Lattice.RingKernelsOverAFiniteSetAndTheLatticeBoxKernel
import YangMills.Construction.Lattice.RingsOnThreeAndFourIndicesAndRingKernelsOfOrdersFourAndTwo
import Mathlib

noncomputable section
namespace YangMills.Construction.CyclicKernels
open Tuples PeriodicLattice
variable {P : Type*}
def pairValue {n : ℕ} (C : P → P → ℝ) (hC : IsSymmetricKernelOn C) (p : Fin n → P) :
    Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun a b => C (p a) (p b), fun _ _ => hC _ _⟩
def sumOverFourRings [Fintype P] (C : P → P → ℝ) (hC : IsSymmetricKernelOn C)
    (φ : Fin 4 → P → ℝ) : ℝ :=
  ∑ᶠ R : {R : Set (Fin 4 → Fin 4) // IsRingOfTuples R}, ∑ p : Fin 4 → P,
    (∏ i, φ i (p i)) * ∏ᶠ e ∈ edgesOfRing R.1, pairValue C hC p e
def CyclicKernelOrderFour : Prop :=
  (∀ (P : Type) [Fintype P] (C : P → P → ℝ) (hC : IsSymmetricKernelOn C),
    {R : Set (Fin 4 → Fin 4) | IsRingOfTuples R}.ncard = 3 ∧
    (∀ R : Set (Fin 4 → Fin 4), IsRingOfTuples R →
      ∃ τ τ' : Equiv.Perm (TailPosition 4), τ ≠ τ' ∧
        {σ : Equiv.Perm (TailPosition 4) | ringClass (fixFirst σ) = R} = {τ, τ'} ∧
        {ς : Fin 4 → Fin 4 | ς ∈ R ∧ ς 0 = 0} = {fixFirst τ, fixFirst τ'} ∧
        rotationClass (fixFirst τ') = reversedSet (rotationClass (fixFirst τ)) ∧
        ∀ p : Fin 4 → P,
          ∏ i, C (p (fixFirst τ i)) (p (fixFirst τ (finRotate 4 i))) =
            ∏ i, C (p (fixFirst τ' i)) (p (fixFirst τ' (finRotate 4 i)))) ∧
    ∀ φ : Fin 4 → P → ℝ, cyclicKernelOn C φ = sumOverFourRings C hC φ) ∧
  ∀ S : Conventions.StandingParameters, Finite (Plaquette S.L S.m ((S.K : ℕ) : ℤ)) ∧
    ∀ [Fintype (Plaquette S.L S.m ((S.K : ℕ) : ℤ))],
      (∀ C : Plaquette S.L S.m ((S.K : ℕ) : ℤ) → Plaquette S.L S.m ((S.K : ℕ) : ℤ) → ℝ,
        IsSymmetricKernelOn C ↔ IsSymmetricKernel C) ∧
      (∀ φ : Plaquette S.L S.m ((S.K : ℕ) : ℤ) → ℝ, IsBoundedPlaquetteFunction φ) ∧
      (∀ n : ℕ, 2 ≤ n →
        ∀ C : Plaquette S.L S.m ((S.K : ℕ) : ℤ) → Plaquette S.L S.m ((S.K : ℕ) : ℤ) → ℝ,
          IsSymmetricKernelOn C → ∀ φ : Fin n → Plaquette S.L S.m ((S.K : ℕ) : ℤ) → ℝ,
            cyclicKernelOn C φ = cyclicKernel C φ) ∧
      ∀ s : ℕ, s ≤ (S.K : ℕ) →
        ∃ hC : IsSymmetricKernelOn (backgroundCurvatureCovariance S s),
          ∀ φ : Fin 4 → Plaquette S.L S.m ((S.K : ℕ) : ℤ) → ℝ,
            boxKernel S s φ = sumOverFourRings (backgroundCurvatureCovariance S s) hC φ
end YangMills.Construction.CyclicKernels
end

set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tuples PeriodicLattice Function
namespace CyclicKernels.OrderFour
variable {J P : Type*}
private theorem tuple_mem_own_ringClass {n : ℕ} (ς : Fin n → J) : ς ∈ ringClass ς :=
  Or.inl (mem_rotationClass_self ς)
private theorem isBijectiveTuple_of_mem_ringClass {ς w : Fin 4 → J} (hς : IsBijectiveTuple ς)
    (hw : w ∈ ringClass ς) : IsBijectiveTuple w := by
  rw [ringClass_eq_union] at hw
  rcases hw with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact hς.rotateBy t
  · exact hς.reversed.rotateBy t
private theorem prod_cyclic_rotateBy (g : J → J → ℝ) (t : ℤ) (ς : Fin 4 → J) :
    ∏ i, g (rotateBy t ς i) (rotateBy t ς (finRotate 4 i)) = ∏ i, g (ς i) (ς (finRotate 4 i)) := by
  have hcomm : ∀ i, (finRotate 4 ^ t) (finRotate 4 i) = finRotate 4 ((finRotate 4 ^ t) i) := fun i => by
    have := congrArg (fun f : Equiv.Perm (Fin 4) => f i)
      ((Commute.refl (finRotate 4)).zpow_left t).eq
    simpa only [Equiv.Perm.mul_apply] using this
  simp only [rotateBy, hcomm]
  exact Equiv.prod_comp (finRotate 4 ^ t) (fun j => g (ς j) (ς (finRotate 4 j)))
private theorem prod_cyclic_reversed (g : J → J → ℝ) (hsymm : ∀ a b, g a b = g b a) (ς : Fin 4 → J) :
    ∏ i, g (reversed ς i) (reversed ς (finRotate 4 i)) = ∏ i, g (ς i) (ς (finRotate 4 i)) := by
  have r0 : finRotate 4 0 = 1 := by decide +kernel
  have r1 : finRotate 4 1 = 2 := by decide +kernel
  have r2 : finRotate 4 2 = 3 := by decide +kernel
  have r3 : finRotate 4 3 = 0 := by decide +kernel
  have v0 : Fin.rev (0 : Fin 4) = 3 := by decide +kernel
  have v1 : Fin.rev (1 : Fin 4) = 2 := by decide +kernel
  have v2 : Fin.rev (2 : Fin 4) = 1 := by decide +kernel
  have v3 : Fin.rev (3 : Fin 4) = 0 := by decide +kernel
  simp only [Fin.prod_univ_four, reversed, r0, r1, r2, r3, v0, v1, v2, v3]
  rw [hsymm (ς 3) (ς 2), hsymm (ς 2) (ς 1), hsymm (ς 1) (ς 0), hsymm (ς 0) (ς 3)]
  ring
private theorem prod_cyclic_eq_of_mem_ringClass (g : J → J → ℝ) (hsymm : ∀ a b, g a b = g b a)
    {ς w : Fin 4 → J} (hw : w ∈ ringClass ς) :
    ∏ i, g (w i) (w (finRotate 4 i)) = ∏ i, g (ς i) (ς (finRotate 4 i)) := by
  rw [ringClass_eq_union] at hw
  rcases hw with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact prod_cyclic_rotateBy g t ς
  · exact (prod_cyclic_rotateBy g t (reversed ς)).trans (prod_cyclic_reversed g hsymm ς)
private theorem fixFirst_apply_zero (τ : Equiv.Perm (TailPosition 4)) : fixFirst τ 0 = 0 := by
  simp [fixFirst]
private theorem exists_fixFirst_eq {v : Fin 4 → Fin 4} (hv : IsBijectiveTuple v) (hv0 : v 0 = 0) :
    ∃ τ : Equiv.Perm (TailPosition 4), fixFirst τ = v := by
  have hbij : Bijective v := hv
  have hpos : ∀ x : Fin 4, 0 < (x : ℕ) ↔ 0 < ((Equiv.ofBijective v hbij) x : ℕ) := by
    intro x
    simp only [Equiv.ofBijective_apply]
    have : x = 0 ↔ v x = 0 := ⟨fun e => e ▸ hv0, fun e => hbij.1 (e.trans hv0.symm)⟩
    have e : ∀ y : Fin 4, 0 < (y : ℕ) ↔ y ≠ 0 := by decide +kernel
    rw [e, e, Ne, Ne, this]
  refine ⟨(Equiv.ofBijective v hbij).subtypeEquiv hpos, ?_⟩
  funext i
  by_cases hi : 0 < (i : ℕ)
  · simp [fixFirst, hi]
  · have : i = 0 := Fin.ext (by omega)
    subst this
    simp [fixFirst, hv0]
abbrev _root_.YangMills.SharedProofs.p51877 := @exists_fixFirst_eq
private theorem ring_members_fixing_zero {R : Set (Fin 4 → Fin 4)}
    {τ τ' : Equiv.Perm (TailPosition 4)}
    (hset : {σ : Equiv.Perm (TailPosition 4) | ringClass (fixFirst σ) = R} = {τ, τ'}) :
    {ς : Fin 4 → Fin 4 | ς ∈ R ∧ ς 0 = 0} = {fixFirst τ, fixFirst τ'} := by
  have hτ : ringClass (fixFirst τ) = R := by
    have : τ ∈ ({τ, τ'} : Set (Equiv.Perm (TailPosition 4))) := Or.inl rfl
    rw [← hset] at this
    exact this
  have hτ' : ringClass (fixFirst τ') = R := by
    have : τ' ∈ ({τ, τ'} : Set (Equiv.Perm (TailPosition 4))) := Or.inr rfl
    rw [← hset] at this
    exact this
  ext ς
  constructor
  · rintro ⟨hmem, h0⟩
    have hmem' : ς ∈ ringClass (fixFirst τ) := hτ ▸ hmem
    obtain ⟨σ, rfl⟩ := exists_fixFirst_eq
      (isBijectiveTuple_of_mem_ringClass (isBijectiveTuple_fixFirst τ) hmem') h0
    have hσ : σ ∈ {σ : Equiv.Perm (TailPosition 4) | ringClass (fixFirst σ) = R} :=
      (ringClass_eq_of_mem hmem').trans hτ
    rw [hset] at hσ
    rcases hσ with rfl | hσ
    · exact Or.inl rfl
    · have : σ = τ' := hσ
      subst this
      exact Or.inr rfl
  · rintro (rfl | hς)
    · exact ⟨hτ ▸ tuple_mem_own_ringClass _, fixFirst_apply_zero τ⟩
    · have : ς = fixFirst τ' := hς
      subst this
      exact ⟨hτ' ▸ tuple_mem_own_ringClass _, fixFirst_apply_zero τ'⟩
private theorem finprod_edgesOfRing_fixFirst (C : P → P → ℝ) (hC : IsSymmetricKernelOn C)
    (p : Fin 4 → P) (τ : Equiv.Perm (TailPosition 4)) :
    ∏ᶠ e ∈ edgesOfRing (ringClass (fixFirst τ)), pairValue C hC p e =
      ∏ i, C (p (fixFirst τ i)) (p (fixFirst τ (finRotate 4 i))) := by
  have hbase : Injective (fun i : Fin 4 => s(i, finRotate 4 i)) := by decide +kernel
  have hinj : Injective
      (fun i : Fin 4 => s(fixFirst τ i, fixFirst τ (finRotate 4 i))) := by
    intro a b hab
    exact hbase (Sym2.map.injective (isBijectiveTuple_fixFirst τ).1 hab)
  rw [edgesOfRing_ringClass, cyclicEdges, finprod_mem_range hinj, finprod_eq_prod_of_fintype]
  rfl
private theorem cyclicKernelOn_eq_twice_sum [Fintype P]
    (hrings : ∀ R : Set (Fin 4 → Fin 4), IsRingOfTuples R →
      ∃ τ τ' : Equiv.Perm (TailPosition 4), τ ≠ τ' ∧
        {σ : Equiv.Perm (TailPosition 4) | ringClass (fixFirst σ) = R} = {τ, τ'} ∧
        rotationClass (fixFirst τ') = reversedSet (rotationClass (fixFirst τ)))
    (C : P → P → ℝ) (hC : IsSymmetricKernelOn C) (φ : Fin 4 → P → ℝ) :
    cyclicKernelOn C φ = sumOverFourRings C hC φ := by
  classical
  let _ := Fintype.ofFinite {R : Set (Fin 4 → Fin 4) // IsRingOfTuples R}
  unfold sumOverFourRings
  rw [finsum_eq_sum_of_fintype]
  set H : {R : Set (Fin 4 → Fin 4) // IsRingOfTuples R} → ℝ := fun R =>
    ∑ p : Fin 4 → P, (∏ i, φ i (p i)) * ∏ᶠ e ∈ edgesOfRing R.1, pairValue C hC p e with hH
  let ρ : Equiv.Perm (TailPosition 4) → {R : Set (Fin 4 → Fin 4) // IsRingOfTuples R} := fun τ =>
    ⟨ringClass (fixFirst τ), isRingOfTuples_ringClass (isBijectiveTuple_fixFirst τ)⟩
  have hterm : ∀ τ : Equiv.Perm (TailPosition 4),
      (∑ p : Fin 4 → P, (∏ i, φ i (p i)) *
        ∏ i, C (p (fixFirst τ i)) (p (fixFirst τ (finRotate 4 i)))) = H (ρ τ) := by
    intro τ
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [finprod_edgesOfRing_fixFirst C hC p τ]
  have hfiber : ∀ R : {R : Set (Fin 4 → Fin 4) // IsRingOfTuples R},
      ∑ τ ∈ Finset.univ.filter (fun τ => ρ τ = R), H (ρ τ) = 2 * H R := by
    intro R
    obtain ⟨τ, τ', hne, hset, -⟩ := hrings R.1 R.2
    have hfilter : Finset.univ.filter (fun τ => ρ τ = R) = {τ, τ'} := by
      ext σ
      have hσ : ρ σ = R ↔ σ ∈ ({τ, τ'} : Set (Equiv.Perm (TailPosition 4))) := by
        rw [← hset]
        exact Subtype.ext_iff
      simpa using hσ
    have hτ : ρ τ = R := by
      apply Subtype.ext
      have : τ ∈ ({τ, τ'} : Set (Equiv.Perm (TailPosition 4))) := by simp
      rw [← hset] at this
      exact this
    have hτ' : ρ τ' = R := by
      apply Subtype.ext
      have : τ' ∈ ({τ, τ'} : Set (Equiv.Perm (TailPosition 4))) := by simp
      rw [← hset] at this
      exact this
    rw [hfilter, Finset.sum_pair hne, hτ, hτ']
    ring
  unfold cyclicKernelOn
  simp only [hterm]
  rw [← Finset.sum_fiberwise Finset.univ ρ, Finset.sum_congr rfl fun R _ => hfiber R,
    ← Finset.mul_sum]
  ring
private theorem cyclicKernelOn_eq_cyclicKernel {L m : ℕ} {j : ℤ} [Fintype (Plaquette L m j)] {n : ℕ}
    (C : Plaquette L m j → Plaquette L m j → ℝ) (φ : Fin n → Plaquette L m j → ℝ) :
    cyclicKernelOn C φ = cyclicKernel C φ := by
  unfold cyclicKernelOn cyclicKernel
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [finsum_eq_sum_of_fintype]
private theorem isBoundedPlaquetteFunction_of_fintype {L m : ℕ} {j : ℤ} [Fintype (Plaquette L m j)]
    (φ : Plaquette L m j → ℝ) : IsBoundedPlaquetteFunction φ :=
  ⟨∑ p, |φ p|, fun p =>
    Finset.single_le_sum (f := fun p => |φ p|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p)⟩
theorem cyclicKernelOrderFour_holds (h : RingsOfOrderThreeFourAndKernels) :
    CyclicKernelOrderFour := by
  refine ⟨fun P _ C hC => ⟨h.1.2.1, fun R hR => ?_, fun φ => cyclicKernelOn_eq_twice_sum h.2.1 C hC φ⟩,
    fun S => ⟨inferInstance, fun {_} => ⟨fun C => Iff.rfl, isBoundedPlaquetteFunction_of_fintype,
      fun n _ C _ φ => cyclicKernelOn_eq_cyclicKernel C φ, fun s _ =>
        ⟨isSymmetricKernel_backgroundCurvatureCovariance S s, fun φ => ?_⟩⟩⟩⟩
  · obtain ⟨τ, τ', hne, hset, hrev⟩ := h.2.1 R hR
    refine ⟨τ, τ', hne, hset, ring_members_fixing_zero hset, hrev, fun p => ?_⟩
    have hτ' : τ' ∈ {σ : Equiv.Perm (TailPosition 4) | ringClass (fixFirst σ) = R} := by
      rw [hset]
      exact Or.inr rfl
    have hτ : τ ∈ {σ : Equiv.Perm (TailPosition 4) | ringClass (fixFirst σ) = R} := by
      rw [hset]
      exact Or.inl rfl
    have hmem : fixFirst τ' ∈ ringClass (fixFirst τ) := by
      have e : ringClass (fixFirst τ') = ringClass (fixFirst τ) := hτ'.trans hτ.symm
      exact e ▸ tuple_mem_own_ringClass _
    exact (prod_cyclic_eq_of_mem_ringClass (fun a b => C (p a) (p b)) (fun _ _ => hC _ _) hmem).symm
  · exact (cyclicKernelOn_eq_cyclicKernel _ φ).symm.trans
      (cyclicKernelOn_eq_twice_sum h.2.1 _ (isSymmetricKernel_backgroundCurvatureCovariance S s) φ)
end CyclicKernels.OrderFour
end YangMills.Construction
