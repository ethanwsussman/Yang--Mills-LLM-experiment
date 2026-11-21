import YangMills.Construction.Matrices.TopologiesAndChartsThroughTheInterchange
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Coordinates
namespace Matrices.GroupLieProduct.Subspaces.Swap
variable {S R : Type}
private theorem isRelativelyOpen_iff_local {E : Type} [TopologicalSpace E] {P D : Set E} :
    ComplexMatrix2.IsRelativelyOpen P D ↔
      D ⊆ P ∧ ∀ p ∈ D, ∃ O : Set E, IsOpen O ∧ p ∈ O ∧ O ∩ P ⊆ D := by
  constructor
  · rintro ⟨O, hO, rfl⟩
    exact ⟨inter_subset_right, fun p hp => ⟨O, hO, hp.1, subset_rfl⟩⟩
  · rintro ⟨hDP, h⟩
    choose! O hO hpO hOD using h
    refine ⟨⋃ p ∈ D, O p, isOpen_biUnion hO, ?_⟩
    ext x
    constructor
    · intro hx
      exact ⟨mem_biUnion hx (hpO x hx), hDP hx⟩
    · rintro ⟨hx, hxP⟩
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hx
      exact hOD p hp ⟨hxp, hxP⟩
private theorem groupComponent_continuous :
    Continuous (groupComponent : (R ⊕ S → ComplexMatrix2) → R → ComplexMatrix2) :=
  continuous_pi fun _ => continuous_apply _
private theorem algebraComponent_continuous :
    Continuous (algebraComponent : (R ⊕ S → ComplexMatrix2) → S → ComplexMatrix2) :=
  continuous_pi fun _ => continuous_apply _
private theorem ofParts_continuous :
    Continuous fun x : (S → ComplexMatrix2) × (R → ComplexMatrix2) => ofParts x.2 x.1 := by
  refine continuous_pi ?_
  rintro (r | s)
  · exact (continuous_apply r).comp continuous_snd
  · exact (continuous_apply s).comp continuous_fst
private theorem ofParts_components (q : R ⊕ S → ComplexMatrix2) :
    ofParts (groupComponent q) (algebraComponent q) = q := by
  funext i
  cases i <;> rfl
private def withEmptyGroup (a : S → ComplexMatrix2) : Empty ⊕ S → ComplexMatrix2 :=
  ofParts (fun e : Empty => e.elim) a
private theorem withEmptyGroup_continuous :
    Continuous (withEmptyGroup : (S → ComplexMatrix2) → _) := by
  refine continuous_pi ?_
  rintro (e | s)
  · exact e.elim
  · exact continuous_apply s
private theorem mem_compactPi_of_empty (q : Empty → ComplexMatrix2) : q ∈ compactPi Empty :=
  fun e => e.elim
private theorem mem_hermitianTracelessFunctions_of_empty (q : Empty → ComplexMatrix2) :
    q ∈ hermitianTracelessFunctions Empty :=
  Submodule.mem_pi.2 fun e => e.elim
private theorem exists_familyToMatrices_eq {x : R → ComplexMatrix2} (hx : x ∈ compactPi R) :
    ∃ u : R → ComplexMatrix2.specialUnitary, familyToMatrices u = x :=
  ⟨fun r => ⟨x r, hx r⟩, rfl⟩
private theorem familyToMatrices_mem (u : R → ComplexMatrix2.specialUnitary) :
    familyToMatrices u ∈ compactPi R :=
  fun r => (u r).2
private theorem familyToMatrices_isInducing :
    Topology.IsInducing
      (familyToMatrices : (R → ComplexMatrix2.specialUnitary) → R → ComplexMatrix2) :=
  Topology.IsInducing.piMap fun _ => Topology.IsInducing.subtypeVal
private theorem powerTopologiesCoincide_holds (R : Type) : PowerTopologiesCoincide R := by
  intro V hV
  constructor
  · constructor
    · intro h
      obtain ⟨O, hO, hOV⟩ := familyToMatrices_isInducing.isOpen_iff.1 h
      refine ⟨O, hO, ?_⟩
      ext x
      constructor
      · intro hx
        obtain ⟨u, rfl⟩ := exists_familyToMatrices_eq (hV hx)
        have : u ∈ familyToMatrices ⁻¹' O := by
          rw [hOV]
          exact hx
        exact ⟨this, hV hx⟩
      · rintro ⟨hxO, hxP⟩
        obtain ⟨u, rfl⟩ := exists_familyToMatrices_eq hxP
        have : u ∈ familyToMatrices ⁻¹' V := by
          rw [← hOV]
          exact hxO
        exact this
    · rintro ⟨O, hO, rfl⟩
      have : familyToMatrices ⁻¹' (O ∩ compactPi R) = familyToMatrices ⁻¹' O := by
        ext u
        exact ⟨fun h => h.1, fun h => ⟨h, familyToMatrices_mem u⟩⟩
      rw [this]
      exact hO.preimage familyToMatrices_isInducing.continuous
  · constructor
    · rintro ⟨O, hO, rfl⟩
      refine ⟨le_rfl, groupComponent ⁻¹' O, hO.preimage groupComponent_continuous, ?_⟩
      ext q
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, mem_hermitianTracelessFunctions_of_empty _, h₂⟩
      · rintro ⟨h₁, _, h₂⟩
        exact ⟨h₁, h₂⟩
    · rintro ⟨-, O, hO, hEq⟩
      have hcont : Continuous fun w : R → ComplexMatrix2 =>
          (ofParts w (fun e : Empty => e.elim) : R ⊕ Empty → ComplexMatrix2) := by
        refine continuous_pi ?_
        rintro (r | e)
        · exact continuous_apply r
        · exact e.elim
      refine ⟨_, hO.preimage hcont, ?_⟩
      ext x
      have hmem : (ofParts x (fun e : Empty => e.elim) : R ⊕ Empty → ComplexMatrix2) ∈
          {q : R ⊕ Empty → ComplexMatrix2 | groupComponent q ∈ V} ↔
          (ofParts x (fun e : Empty => e.elim) : R ⊕ Empty → ComplexMatrix2) ∈
            O ∩ subspaceTimesGroup (hermitianTracelessFunctions Empty) R := by
        rw [← hEq]
      constructor
      · intro hx
        exact ⟨(hmem.1 hx).1, hV hx⟩
      · rintro ⟨hxO, hxP⟩
        exact hmem.2 ⟨hxO, mem_hermitianTracelessFunctions_of_empty _, hxP⟩
private theorem subspaceTopologyIsProduct_holds (S R : Type) :
    SubspaceTopologyIsProduct S R := by
  intro E hE D
  constructor
  · rintro ⟨-, O, hO, rfl⟩
    refine ⟨inter_subset_right, ?_⟩
    rintro p ⟨hpO, hpE, hpG⟩
    have hopen := hO.preimage (ofParts_continuous (S := S) (R := R))
    have hmem : (algebraComponent p, groupComponent p) ∈
        (fun x : (S → ComplexMatrix2) × (R → ComplexMatrix2) => ofParts x.2 x.1) ⁻¹' O := by
      change ofParts (groupComponent p) (algebraComponent p) ∈ O
      rwa [ofParts_components]
    obtain ⟨u, v, hu, hv, hau, hgv, huv⟩ := isOpen_prod_iff.1 hopen _ _ hmem
    refine ⟨u ∩ (E : Set (S → ComplexMatrix2)), v ∩ compactPi R, ⟨hE, ?_⟩, ⟨v, hv, rfl⟩,
      ⟨hau, hpE⟩, ⟨hgv, hpG⟩, ?_⟩
    · refine ⟨algebraComponent ⁻¹' u, hu.preimage algebraComponent_continuous, ?_⟩
      ext q
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₂, mem_compactPi_of_empty _⟩
      · rintro ⟨h₁, h₂, _⟩
        exact ⟨h₁, h₂⟩
    · intro q hq hqU hqV
      have : ofParts (groupComponent q) (algebraComponent q) ∈ O :=
        huv (mk_mem_prod hqU.1 hqV.1)
      rw [ofParts_components] at this
      exact ⟨this, hq⟩
  · rintro ⟨hD, h⟩
    refine ⟨hE, isRelativelyOpen_iff_local.2 ⟨hD, fun p hp => ?_⟩⟩
    obtain ⟨U, V, ⟨-, O₁, hO₁, hU⟩, ⟨O₂, hO₂, rfl⟩, hpU, hpV, hsub⟩ := h p hp
    refine ⟨(fun q => withEmptyGroup (algebraComponent q)) ⁻¹' O₁ ∩ groupComponent ⁻¹' O₂,
      (hO₁.preimage (withEmptyGroup_continuous.comp algebraComponent_continuous)).inter
        (hO₂.preimage groupComponent_continuous), ⟨?_, hpV.1⟩, ?_⟩
    · have : withEmptyGroup (algebraComponent p) ∈
          {q : Empty ⊕ S → ComplexMatrix2 | algebraComponent q ∈ U} := hpU
      rw [hU] at this
      exact this.1
    · rintro q ⟨⟨hq₁, hq₂⟩, hqP⟩
      have hqU : withEmptyGroup (algebraComponent q) ∈
          {q : Empty ⊕ S → ComplexMatrix2 | algebraComponent q ∈ U} := by
        rw [hU]
        exact ⟨hq₁, hqP.1, mem_compactPi_of_empty _⟩
      exact hsub q hqP hqU ⟨hq₂, hqP.2⟩
private theorem expChartViaSwap_holds (S R : Type) : ExpChartViaSwap S R := by
  intro Z₀ W₀ _
  refine ⟨fun q => ⟨fun h => ?_, ?_⟩, fun A _ B _ => ?_⟩
  · exact ⟨algebraComponent q, fun s => h (.inr s), groupComponent q, fun r => h (.inl r),
      (ofParts_components q).symm⟩
  · rintro ⟨A, hA, B, hB, rfl⟩ (r | s)
    · exact hB r
    · exact hA s
  · funext i
    cases i <;> rfl
private theorem isHolomorphicIn_reindex {N N' M : ℕ} (π : Fin N' ≃ Fin N)
    {O : Set (ComplexCoordinates N)} {f : ComplexCoordinates N → ComplexCoordinates M}
    (h : ComplexCoordinates.IsHolomorphicIn O f) :
    ComplexCoordinates.IsHolomorphicIn ((fun (z : ComplexCoordinates N) j => z (π j)) '' O)
      (f ∘ fun (w : ComplexCoordinates N') i => w (π.symm i)) := by
  obtain ⟨hO, hf, hd⟩ := h
  have hback : Continuous fun (w : ComplexCoordinates N') (i : Fin N) => w (π.symm i) :=
    continuous_pi fun _ => continuous_apply _
  have himage : (fun (z : ComplexCoordinates N) j => z (π j)) '' O =
      (fun (w : ComplexCoordinates N') i => w (π.symm i)) ⁻¹' O := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have : (fun i => z (π (π.symm i))) = z := by
        funext i
        rw [π.apply_symm_apply]
      change (fun i => z (π (π.symm i))) ∈ O
      rwa [this]
    · intro hw
      refine ⟨_, hw, ?_⟩
      funext j
      change w (π.symm (π j)) = w j
      rw [π.symm_apply_apply]
  rw [himage]
  refine ⟨hO.preimage hback, hf.comp hback.continuousOn fun _ hw => hw, fun a ha j => ?_⟩
  refine (hd _ ha (π j)).mono fun ζ hζ => ?_
  have hmove : ∀ ζ : ℂ, (fun i => (a + ζ • ComplexCoordinates.stdBasisVector j) (π.symm i)) =
      (fun i => a (π.symm i)) + ζ • ComplexCoordinates.stdBasisVector (π j) := by
    intro ζ
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, ComplexCoordinates.stdBasisVector, Pi.single_apply,
      Equiv.symm_apply_eq]
  have hfun : (fun ζ : ℂ => (f ∘ fun (w : ComplexCoordinates N') i => w (π.symm i))
      (a + ζ • ComplexCoordinates.stdBasisVector j)) = fun ζ : ℂ =>
        f ((fun i => a (π.symm i)) + ζ • ComplexCoordinates.stdBasisVector (π j)) := by
    funext ζ
    simp only [Function.comp_apply, hmove]
  rw [hfun]
  exact hζ
private def entryIndex {σ : Type} {k : ℕ} (ν : σ ≃ Fin k) :
    Fin (ComplexCoordinates.productDim fun _ : Fin k => ComplexCoordinates.Component.matrix) ≃
      σ × Fin 4 :=
  (finSigmaFinEquiv (m := k) (n := fun _ => 4)).symm.trans
    ((Equiv.sigmaEquivProd (Fin k) (Fin 4)).trans (Equiv.prodCongr ν.symm (Equiv.refl _)))
private theorem matrixPiEquiv_apply_eq {σ : Type} {k : ℕ} (ν : σ ≃ Fin k)
    (X : σ → ComplexMatrix2)
    (j : Fin (ComplexCoordinates.productDim fun _ : Fin k => ComplexCoordinates.Component.matrix)) :
    matrixPiEquiv ν X j =
      ComplexCoordinates.matrixEquiv (X (entryIndex ν j).1) (entryIndex ν j).2 :=
  rfl
private def swapComponents {k k' : ℕ} (μ : S ⊕ R ≃ Fin k) (ν : R ⊕ S ≃ Fin k') :
    Fin (ComplexCoordinates.productDim fun _ : Fin k' => ComplexCoordinates.Component.matrix) ≃
      Fin (ComplexCoordinates.productDim fun _ : Fin k => ComplexCoordinates.Component.matrix) :=
  (entryIndex ν).trans
    ((Equiv.prodCongr (Equiv.sumComm R S) (Equiv.refl _)).trans (entryIndex μ).symm)
private theorem matrixPiEquiv_ofParts_eq {k k' : ℕ} (μ : S ⊕ R ≃ Fin k) (ν : R ⊕ S ≃ Fin k')
    (x : (S → ComplexMatrix2) × (R → ComplexMatrix2))
    (j : Fin (ComplexCoordinates.productDim fun _ : Fin k' => ComplexCoordinates.Component.matrix)) :
    matrixPiEquiv ν (ofParts x.2 x.1) j =
      pairEquiv μ x (swapComponents μ ν j) := by
  have hentry : entryIndex μ (swapComponents μ ν j) =
      (Equiv.sumComm R S (entryIndex ν j).1, (entryIndex ν j).2) := by
    simp only [swapComponents, Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl
  change matrixPiEquiv ν (ofParts x.2 x.1) j =
    matrixPiEquiv μ (Sum.elim x.1 x.2) (swapComponents μ ν j)
  rw [matrixPiEquiv_apply_eq, matrixPiEquiv_apply_eq, hentry]
  rcases (entryIndex ν j).1 with r | s <;> rfl
private theorem holomorphicViaSwap_holds (S R : Type) : HolomorphicViaSwap S R := by
  intro T l k e μ O Φ hO hΦ
  refine ⟨?_, fun k' ν => ?_⟩
  · exact hO.preimage (algebraComponent_continuous.prodMk groupComponent_continuous)
  have key := isHolomorphicIn_reindex (swapComponents μ ν) hΦ
  have hc : ∀ x : (S → ComplexMatrix2) × (R → ComplexMatrix2),
      (fun (z : ComplexCoordinates _) j => z (swapComponents μ ν j)) (pairEquiv μ x) =
        matrixPiEquiv ν (ofParts x.2 x.1) := by
    intro x
    funext j
    exact (matrixPiEquiv_ofParts_eq μ ν x j).symm
  have hset : matrixPiEquiv ν '' swapSet O =
      (fun (z : ComplexCoordinates _) j => z (swapComponents μ ν j)) ''
        (pairEquiv μ '' O) := by
    ext w
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨_, ⟨_, hq, rfl⟩, ?_⟩
      rw [hc]
      change matrixPiEquiv ν (ofParts (groupComponent q) (algebraComponent q)) = _
      rw [ofParts_components]
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨ofParts x.2 x.1, hx, (hc x).symm⟩
  have hmap : e ∘ swapMap Φ ∘ (matrixPiEquiv ν).symm =
      (e ∘ Φ ∘ (pairEquiv μ).symm) ∘
        fun (w : ComplexCoordinates _) i => w ((swapComponents μ ν).symm i) := by
    funext w
    obtain ⟨q, rfl⟩ := (matrixPiEquiv ν).surjective w
    have hq : matrixPiEquiv ν q =
        (fun (z : ComplexCoordinates _) j => z (swapComponents μ ν j))
          (pairEquiv μ (algebraComponent q, groupComponent q)) := by
      rw [hc]
      change _ = matrixPiEquiv ν (ofParts (groupComponent q) (algebraComponent q))
      rw [ofParts_components]
    have hback : (fun i => matrixPiEquiv ν q ((swapComponents μ ν).symm i)) =
        pairEquiv μ (algebraComponent q, groupComponent q) := by
      funext i
      rw [hq]
      simp only [Equiv.apply_symm_apply]
    simp only [Function.comp_apply, Equiv.symm_apply_apply, hback]
    rfl
  change ComplexCoordinates.IsHolomorphicIn (matrixPiEquiv ν '' swapSet O)
    (e ∘ swapMap Φ ∘ (matrixPiEquiv ν).symm)
  rw [hset, hmap]
  exact key
theorem swapTheory_holds : SwapTheory := by
  intro S R _ _
  exact ⟨powerTopologiesCoincide_holds R, subspaceTopologyIsProduct_holds S R,
    expChartViaSwap_holds S R, holomorphicViaSwap_holds S R⟩
end Matrices.GroupLieProduct.Subspaces.Swap
end YangMills.Construction
