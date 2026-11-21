import YangMills.Construction.Matrices.CalculusOfTheFieldsOnPowersOfGProof
import YangMills.Construction.TransferOperators.ConditionalLawOfOneBlockOfOneLayer
import YangMills.Construction.TransferOperators.ConditioningOnAllBondsButOneBlockOfOneLayer
import YangMills.Construction.TransferOperators.DecayNumbersAdmissiblePairsAndTheOperatorHat
import Mathlib
import YangMills.Construction.TransferOperators.GaugeAveragesOfFunctionsOfLayersProof
import YangMills.Construction.TransferOperators.PeterWeylCoefficientsAndMultiplicationThroughTheBondKernel
import YangMills.Construction.TransferOperators.SymmetryBoundsAndInvarianceOfTheBondKernelAndTheLayerEnergy
set_option autoImplicit false

section
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice SpinHarmonics Matrices
namespace TransferOperators
section DisjointUnion
variable (A C : Type)
def inlSet : Set (A ⊕ C) := Set.range Sum.inl
variable {A C}
def toInlSet (a : A) : inlSet A C := ⟨Sum.inl a, a, rfl⟩
def restrictInl (f : (A → ComplexMatrix2.specialUnitary) → ℂ)
    (u : inlSet A C → ComplexMatrix2.specialUnitary) : ℂ :=
  f fun a => u (toInlSet a)
theorem isRealEntryPolynomial_restrictInl [Finite A] [Finite C]
    {f : (A → ComplexMatrix2.specialUnitary) → ℂ}
    (hf : IsRealEntryPolynomial f) : IsRealEntryPolynomial (restrictInl (C := C) f) := by
  obtain ⟨⟨q, hq⟩, hre⟩ := hf
  refine ⟨⟨MvPolynomial.rename
    (Sum.map (Prod.map toInlSet id) (Prod.map toInlSet id)) q, fun u => ?_⟩,
    fun u => hre _⟩
  have hcomp : entryEval (fun a => u (toInlSet a)) = entryEval u ∘
      Sum.map (Prod.map toInlSet id) (Prod.map toInlSet id) := by
    funext x
    rcases x with ⟨b, r, s⟩ | ⟨b, r, s⟩ <;> rfl
  rw [MvPolynomial.eval_rename, restrictInl, hq, hcomp]
end DisjointUnion
variable {μ : Fin 4}
structure Block.AdjacentPairs (B : Block μ) (j k : ℤ) (R : Finset (ℤ × SliceLink μ)) : Prop where
  avoids_block : ∀ p ∈ R, ¬(p.1 = j ∧ p.2 ∈ B.links)
  collar_mem : ∀ b ∈ B.thickened \ (B.links : Set (SliceLink μ)), (j, b) ∈ R
  adjacent_mem : ∀ b ∈ B.links, (k, b) ∈ R
namespace Block.AdjacentPairs
variable {B : Block μ} {j k : ℤ} {R : Finset (ℤ × SliceLink μ)} (h : B.AdjacentPairs j k R)
def collarPart (z : R → ComplexMatrix2.specialUnitary) :
    ↥(B.thickened \ (B.links : Set (SliceLink μ))) → ComplexMatrix2.specialUnitary :=
  fun b => z ⟨(j, b.1), h.collar_mem b.1 b.2⟩
def adjacentPart (z : R → ComplexMatrix2.specialUnitary) :
    B.links → ComplexMatrix2.specialUnitary :=
  fun b => z ⟨(k, b.1), h.adjacent_mem b.1 b.2⟩
def weighted (β : ℝ) (φ : (B.links ⊕ R → ComplexMatrix2.specialUnitary) → ℂ)
    (u : B.links ⊕ R → ComplexMatrix2.specialUnitary) : ℂ :=
  Complex.exp (-B.sliceEnergy β (fun b => u (Sum.inl b)) (h.collarPart fun p => u (Sum.inr p))) *
    linkProductKernel β (fun b => u (Sum.inl b)) (h.adjacentPart fun p => u (Sum.inr p)) * φ u
def flattened (β : ℝ) (H : (B.links ⊕ R → ComplexMatrix2.specialUnitary) → ℂ)
    (u : B.links ⊕ R → ComplexMatrix2.specialUnitary) : ℂ :=
  Complex.exp (B.sliceEnergy β (fun b => u (Sum.inl b)) (h.collarPart fun p => u (Sum.inr p))) /
    linkProductKernel β (fun b => u (Sum.inl b)) (h.adjacentPart fun p => u (Sum.inr p)) * H u
end Block.AdjacentPairs
namespace Stack
variable (S : Stack)
def pairVariables (R : Finset (ℤ × SliceLink μ)) (U : GaugeField 1) :
    R → ComplexMatrix2.specialUnitary :=
  fun p => S.transportedLinkVariable μ U p.1.1 p.1.2
def blockPairVariables (B : Block μ) (R : Finset (ℤ × SliceLink μ)) (U : GaugeField 1) (j : ℤ) :
    B.links ⊕ R → ComplexMatrix2.specialUnitary :=
  Sum.elim (S.blockValues B U j) (S.pairVariables R U)
variable (μ) in
def IsRealContinuousOfLevels (lo hi : ℤ) (F : GaugeField 1 → ℂ) : Prop :=
  Continuous F ∧ (∀ U, (F U).im = 0) ∧
    ∃ (T : Finset (ℤ × SliceLink μ)) (g : (T → ComplexMatrix2.specialUnitary) → ℂ), Continuous g ∧
      (∀ p ∈ T, lo ≤ p.1 ∧ p.1 ≤ hi) ∧ ∀ U, F U = g (S.pairVariables T U)
end Stack
def OuterSliceElimination (β : ℝ) (ν : Measure (GaugeField 1)) (S : Stack) {B : Block μ}
    {f : (B.links → ComplexMatrix2.specialUnitary) → ℂ} (hf : IsRealEntryPolynomial f) {j k : ℤ}
    {R : Finset (ℤ × SliceLink μ)} (h : B.AdjacentPairs j k R) (k' lo hi : ℤ)
    (φ : (B.links ⊕ R → ComplexMatrix2.specialUnitary) → ℂ) : Prop :=
  h.weighted β φ ∈ smoothSet ∧
    ∃ (hc : Continuous (h.weighted β φ))
      (hd : (⟨h.weighted β φ, hc⟩ : C(B.links ⊕ R → ComplexMatrix2.specialUnitary, ℂ)) ∈
        hatSummableSet β (inlSet B.links R) (restrictInl f) (isRealEntryPolynomial_restrictInl hf)),
      let flat := h.flattened β
        (hatMap β (inlSet B.links R) (restrictInl f) (isRealEntryPolynomial_restrictInl hf)
          ⟨⟨h.weighted β φ, hc⟩, hd⟩)
      flat ∈ smoothSet ∧ (∀ u, (flat u).im = 0) ∧
        S.IsRealContinuousOfLevels μ lo hi
          (fun U => flat (S.blockPairVariables B R U j)) ∧
        ∫ U, f (S.blockValues B U k') * φ (S.blockPairVariables B R U j) ∂ν =
          ∫ U, flat (S.blockPairVariables B R U j) ∂ν
namespace OutermostSliceElimination
def Statement : Prop :=
  ∀ (μ : Fin 4) (β : ℝ), 0 < β →
    ∀ ν ∈ gibbsClass (zero_lt_one (α := ℝ)) β,
    ∀ (S : Stack) (j : ℤ), S.IsInteriorLevel j →
    ∀ (B : Block μ) (f : (B.links → ComplexMatrix2.specialUnitary) → ℂ)
      (hf : IsRealEntryPolynomial f),
      (∀ (R : Finset (ℤ × SliceLink μ)) (h : B.AdjacentPairs j (j + 1) R),
        (∀ p ∈ R, j ≤ p.1 ∧ p.1 ≤ S.upper) →
        ∀ φ ∈ smoothSet, (∀ u, (φ u).im = 0) →
          OuterSliceElimination β ν S hf h (j - 1) j S.upper φ) ∧
      (∀ (R : Finset (ℤ × SliceLink μ)) (h : B.AdjacentPairs j (j - 1) R),
        (∀ p ∈ R, S.lower ≤ p.1 ∧ p.1 ≤ j) →
        ∀ φ ∈ smoothSet, (∀ u, (φ u).im = 0) →
          OuterSliceElimination β ν S hf h (j + 1) S.lower j φ)
end OutermostSliceElimination
end TransferOperators
end YangMills.Construction
end
end

open MeasureTheory Set YangMills.Construction.InfiniteLattice YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.TransferOperators.OutermostSliceElimination
variable {μ : Fin 4}
theorem im_cexp_of_im_eq_zero {x : ℂ} (hx : x.im = 0) : (Complex.exp x).im = 0 := by
  have e : x = (x.re : ℂ) := Complex.ext rfl (by simpa using hx)
  rw [e]
  exact Complex.exp_ofReal_im _
section Smooth
variable (hcalc : FieldCalculus.AllRules) {J : Type} [Finite J] [Nonempty J]
include hcalc
theorem mul_mem_smoothSet {F H : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet)
    (hH : H ∈ smoothSet) : (fun u => F u * H u) ∈ smoothSet := by
  obtain ⟨⟨A, hA⟩, -⟩ := (hcalc.2.2 J).2.1 ⊤
  have hA' : (A : Set ((J → specialUnitary) → ℂ)) = smoothSet := hA
  rw [← hA'] at hF hH ⊢
  exact A.mul_mem hF hH
theorem neg_mem_smoothSet {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet) :
    (fun u => -F u) ∈ smoothSet := by
  obtain ⟨⟨A, hA⟩, -⟩ := (hcalc.2.2 J).2.1 ⊤
  have hA' : (A : Set ((J → specialUnitary) → ℂ)) = smoothSet := hA
  rw [← hA'] at hF ⊢
  exact A.neg_mem hF
theorem finprod_mem_smoothSet {I : Type} [Finite I] (G : I → (J → specialUnitary) → ℂ)
    (hG : ∀ i, G i ∈ smoothSet) : (fun u => ∏ᶠ i, G i u) ∈ smoothSet := by
  obtain ⟨⟨A, hA⟩, -⟩ := (hcalc.2.2 J).2.1 ⊤
  have hA' : (A : Set ((J → specialUnitary) → ℂ)) = smoothSet := hA
  let _ : Fintype I := Fintype.ofFinite I
  have e : (fun u => ∏ᶠ i, G i u) = ∏ i, G i := by
    funext u
    simp [finprod_eq_prod_of_fintype, Finset.prod_apply]
  rw [e, ← hA']
  refine prod_mem fun i _ => ?_
  exact show G i ∈ (A : Set ((J → specialUnitary) → ℂ)) from by
    rw [hA']
    exact hG i
end Smooth
theorem continuous_of_mem_smoothSet {J : Type} {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet) :
    Continuous F :=
  Set.mem_iInter.1 hF 0
theorem isRealEntryPolynomial_comp_reindex {K J : Type} [Finite K] [Finite J] (e : K → J)
    {F : (K → specialUnitary) → ℂ} (hF : IsRealEntryPolynomial F) :
    IsRealEntryPolynomial fun u : J → specialUnitary => F fun a => u (e a) := by
  obtain ⟨⟨p, hp⟩, hr⟩ := hF
  refine ⟨⟨MvPolynomial.rename (Sum.map (Prod.map e id) (Prod.map e id)) p, fun u => ?_⟩,
    fun u => hr _⟩
  have ee : entryEval (fun a => u (e a)) =
      entryEval u ∘ Sum.map (Prod.map e id) (Prod.map e id) := by
    funext x
    rcases x with ⟨b, i, j⟩ | ⟨b, i, j⟩ <;> rfl
  rw [MvPolynomial.eval_rename, ← ee]
  exact hp _
section Transfer
variable (A C : Type)
def inlSetEquiv : A ≃ inlSet A C :=
  Equiv.ofBijective toInlSet
    ⟨fun _ _ h => Sum.inl_injective (congrArg Subtype.val h), fun ⟨_, a, rfl⟩ => ⟨a, rfl⟩⟩
def transferToInl : (A → specialUnitary) ≃ᵐ (inlSet A C → specialUnitary) :=
  MeasurableEquiv.piCongrLeft (fun _ => specialUnitary) (inlSetEquiv A C)
variable {A C}
theorem transferToInl_apply (x : A → specialUnitary) (a : A) :
    transferToInl A C x (toInlSet a) = x a :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => specialUnitary) (inlSetEquiv A C) x a
theorem integral_transferToInl [Countable A] [Countable C] (G : (inlSet A C → specialUnitary) → ℂ) :
    ∫ x, G (transferToInl A C x) ∂haarPi A = ∫ v, G v ∂haarPi (inlSet A C) := by
  have hmp : MeasurePreserving (transferToInl A C) (haarPi A)
      (haarPi (inlSet A C)) := by
    refine ⟨(transferToInl A C).measurable, ?_⟩
    unfold haarPi
    exact Measure.infinitePi_map_piCongrLeft (μ := fun _ => haarProb) (inlSetEquiv A C)
  exact hmp.integral_comp' G
theorem linkProductKernel_transferToInl (β : ℝ) (x x' : A → specialUnitary) :
    linkProductKernel β (transferToInl A C x) (transferToInl A C x') = linkProductKernel β x x' := by
  unfold linkProductKernel
  rw [← finprod_comp_equiv (inlSetEquiv A C)]
  refine finprod_congr fun a => ?_
  have h₁ : transferToInl A C x (inlSetEquiv A C a) = x a := transferToInl_apply x a
  have h₂ : transferToInl A C x' (inlSetEquiv A C a) = x' a := transferToInl_apply x' a
  rw [h₁, h₂]
theorem glue_transferToInl (x w : A → specialUnitary) (z : C → specialUnitary) :
    glue (inlSet A C) (transferToInl A C x)
        (restrictTo (inlSet A C)ᶜ (Sum.elim w z)) = Sum.elim x z := by
  funext c
  rcases c with a | r
  · exact (glue_of_mem (inlSet A C) _ _ (toInlSet a)).trans
      (transferToInl_apply x a)
  · have hr : Sum.inr r ∉ inlSet A C := by
      rintro ⟨a, ha⟩
      exact Sum.inl_ne_inr ha
    exact glue_of_notMem (inlSet A C) _ _ ⟨Sum.inr r, hr⟩
theorem restrictInl_transferToInl (f : (A → specialUnitary) → ℂ) (w : A → specialUnitary) :
    restrictInl f (transferToInl A C w) = f w := by
  unfold restrictInl
  congr 1
  funext a
  exact transferToInl_apply w a
theorem mul_integral_kernel_of_inl [Countable A] [Countable C] {β : ℝ} {f : (A → specialUnitary) → ℂ}
    {F H : (A ⊕ C → specialUnitary) → ℂ}
    (hp : ∀ (w : inlSet A C → specialUnitary) (z : ↥(inlSet A C)ᶜ → specialUnitary),
      restrictInl f w * ∫ v, linkProductKernel β v w * F (glue (inlSet A C) v z)
          ∂haarPi (inlSet A C) =
        ∫ v, linkProductKernel β v w * H (glue (inlSet A C) v z)
          ∂haarPi (inlSet A C))
    (w : A → specialUnitary) (z : C → specialUnitary) :
    f w * ∫ v, linkProductKernel β v w * F (Sum.elim v z) ∂haarPi A =
      ∫ v, linkProductKernel β v w * H (Sum.elim v z) ∂haarPi A := by
  have key := hp (transferToInl A C w) (restrictTo (inlSet A C)ᶜ (Sum.elim w z))
  rw [← integral_transferToInl, ← integral_transferToInl] at key
  simp only [linkProductKernel_transferToInl, glue_transferToInl, restrictInl_transferToInl] at key
  exact key
end Transfer
section Data
variable {B : Block μ} {j k : ℤ} {R : Finset (ℤ × SliceLink μ)} (h : B.AdjacentPairs j k R)
def sliceEnergyFn (β : ℝ) (u : B.links ⊕ R → specialUnitary) : ℂ :=
  B.sliceEnergy β (fun b => u (Sum.inl b)) (h.collarPart fun p => u (Sum.inr p))
def kernelFn (β : ℝ) (u : B.links ⊕ R → specialUnitary) : ℂ :=
  linkProductKernel β (fun b => u (Sum.inl b)) (h.adjacentPart fun p => u (Sum.inr p))
open Classical in
def thickenedIndex (b : B.thickened) : B.links ⊕ R :=
  if hb : b.1 ∈ B.links then Sum.inl ⟨b.1, hb⟩
  else Sum.inr ⟨(j, b.1), h.collar_mem b.1 ⟨b.2, fun x => hb (Finset.mem_coe.1 x)⟩⟩
theorem isRealEntryPolynomial_sliceEnergyFn
    (hker : KernelSymmetryAndGaugeInvariance.Statement)
    {β : ℝ} (hβ : 0 < β) : IsRealEntryPolynomial (sliceEnergyFn h β) := by
  have hV := ((hker β hβ).2.2.2 μ B).1
  have hr := isRealEntryPolynomial_comp_reindex (J := B.links ⊕ R) (thickenedIndex h) hV
  have e : sliceEnergyFn h β = fun u => B.sliceEnergyOnThickened β fun a => u (thickenedIndex h a) := by
    funext u
    unfold sliceEnergyFn Block.sliceEnergyOnThickened
    congr 1
    · funext b
      have hb : b.1 ∈ B.links := b.2
      simp only [thickenedIndex, dif_pos hb]
    · funext b
      have hb : b.1 ∉ B.links := fun x => b.2.2 (Finset.mem_coe.2 x)
      simp only [thickenedIndex, dif_neg hb]
      rfl
  rw [e]
  exact hr
theorem kernelFn_mem_smoothSet (hcalc : FieldCalculus.AllRules) [Nonempty (B.links ⊕ R)]
    {β : ℝ} (hβ : 0 < β) : kernelFn h β ∈ smoothSet := by
  have hw : ∀ b : B.links, (fun u : B.links ⊕ R → specialUnitary => singleBondWeight β
      (u (Sum.inl b) * (u (Sum.inr ⟨(k, b.1), h.adjacent_mem b.1 b.2⟩))⁻¹)) ∈ smoothSet :=
    fun b => ((hcalc.2.2 (B.links ⊕ R)).2.2.2.2.2.1.2 β hβ (Sum.inl b) (Sum.inr _)
      Sum.inl_ne_inr).1
  have hs := finprod_mem_smoothSet hcalc _ hw
  have e : kernelFn h β = fun u : B.links ⊕ R → specialUnitary => ∏ᶠ b : B.links, singleBondWeight β
      (u (Sum.inl b) * (u (Sum.inr ⟨(k, b.1), h.adjacent_mem b.1 b.2⟩))⁻¹) := by
    funext u
    rfl
  rw [e]
  exact hs
end Data
theorem linkProductKernel_real_pos
    (hker : KernelSymmetryAndGaugeInvariance.Statement)
    {β : ℝ} (hβ : 0 < β) (B : Block μ) (u u' : B.links → specialUnitary) :
    (linkProductKernel β u u').im = 0 ∧ 0 < (linkProductKernel β u u').re := by
  have : Nonempty B.links := B.links_nonempty.to_subtype
  obtain ⟨-, h₂, h₃, -⟩ := ((hker β hβ).1 B.links).1 u u'
  exact ⟨h₂, (Real.exp_pos _).trans_le h₃⟩
theorem hatSum_properties (hpass : MulThroughLinkKernelStatement)
    (hfacts : SeveralVariables.SeveralVariablesFacts) {A C : Type} [Finite A] [Finite C] [Nonempty A]
    {β : ℝ} (hβ : 0 < β) {f : (A → specialUnitary) → ℂ} (hf : IsRealEntryPolynomial f)
    (F : C(A ⊕ C → specialUnitary, ℂ)) (hF : (F : (A ⊕ C → specialUnitary) → ℂ) ∈ smoothSet)
    (hr : ∀ u, (F u).im = 0) :
    F ∈ hatSummableSet β (inlSet A C) (restrictInl f) (isRealEntryPolynomial_restrictInl hf) ∧
    (hatSum β (inlSet A C) (restrictInl f) (isRealEntryPolynomial_restrictInl hf) F :
      (A ⊕ C → specialUnitary) → ℂ) ∈ smoothSet ∧
    (∀ u, (hatSum β (inlSet A C) (restrictInl f) (isRealEntryPolynomial_restrictInl hf) F u).im = 0) ∧
    ∀ (w : A → specialUnitary) (z : C → specialUnitary),
      f w * ∫ v, linkProductKernel β v w * F (Sum.elim v z) ∂haarPi A =
        ∫ v, linkProductKernel β v w *
          hatSum β (inlSet A C) (restrictInl f) (isRealEntryPolynomial_restrictInl hf) F
            (Sum.elim v z) ∂haarPi A := by
  have : Nonempty (A ⊕ C) := ⟨Sum.inl (Classical.arbitrary A)⟩
  have : Nonempty (inlSet A C) := ⟨toInlSet (Classical.arbitrary A)⟩
  have hne : (inlSet A C).Nonempty := ⟨Sum.inl (Classical.arbitrary A), _, rfl⟩
  have hf' := isRealEntryPolynomial_restrictInl (C := C) hf
  obtain ⟨D, hD⟩ := ((hfacts (inlSet A C) (fun _ => ⟨0⟩) ⟨0⟩).2.2.2.2.2.2.2.1
    (restrictInl f) hf'.1).2
  obtain ⟨hser, hprop⟩ := (hpass (A ⊕ C)).2.2.2.2 β (inlSet A C) (restrictInl f) hf' D hβ hne hD
  obtain ⟨-, -, -, -, -, -, hdom, hsm, -⟩ := hser F hF
  obtain ⟨-, hreal, -, -, -, -, -, -, hid⟩ := hprop
  exact ⟨hdom, hsm, hreal F hF hr,
    mul_integral_kernel_of_inl fun w z => hid F w z hF⟩
section Continuity
variable (S : Stack)
theorem continuous_transportedLinkVariable (j : ℤ) (b : SliceLink μ) :
    Continuous fun U : GaugeField 1 => S.transportedLinkVariable μ U j b := by apply _root_.YangMills.Construction.TransferOperators.SliceMean.continuous_transportedLinkVariable <;> assumption
theorem continuous_blockValues (B : Block μ) (j : ℤ) :
    Continuous fun U : GaugeField 1 => S.blockValues B U j :=
  continuous_pi fun b => continuous_transportedLinkVariable S j b.1
theorem continuous_blockPairVariables (B : Block μ) (R : Finset (ℤ × SliceLink μ)) (j : ℤ) :
    Continuous fun U : GaugeField 1 => S.blockPairVariables B R U j := by
  refine continuous_pi ?_
  rintro (b | p)
  · exact continuous_transportedLinkVariable S j b.1
  · exact continuous_transportedLinkVariable S p.1.1 p.1.2
end Continuity
theorem exists_norm_bound_of_continuous {K : Type} {g : (K → specialUnitary) → ℂ} (hg : Continuous g) :
    ∃ C : ℝ, ∀ u, ‖g u‖ ≤ C := by apply _root_.YangMills.Construction.SpinHarmonics.FieldCalculus.exists_norm_bound <;> assumption
section Flat
variable {B : Block μ} {j k : ℤ} {R : Finset (ℤ × SliceLink μ)}
theorem isRealContinuousOfLevels_comp (S : Stack) (lo hi : ℤ) (hlj : lo ≤ j) (hjh : j ≤ hi)
    (hR : ∀ p ∈ R, lo ≤ p.1 ∧ p.1 ≤ hi) {F : (B.links ⊕ R → specialUnitary) → ℂ} (hF : Continuous F)
    (hr : ∀ u, (F u).im = 0) :
    S.IsRealContinuousOfLevels μ lo hi fun U => F (S.blockPairVariables B R U j) := by
  classical
  let T : Finset (ℤ × SliceLink μ) := R ∪ B.links.image fun b => (j, b)
  have hT₁ : ∀ b ∈ B.links, (j, b) ∈ T := fun b hb =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb)
  have hT₂ : ∀ p ∈ R, p ∈ T := fun p hp => Finset.mem_union_left _ hp
  let ι : B.links ⊕ R → T := Sum.elim (fun b => ⟨(j, b.1), hT₁ b.1 b.2⟩)
    fun p => ⟨p.1, hT₂ p.1 p.2⟩
  refine ⟨hF.comp (continuous_blockPairVariables S B R j), fun U => hr _, T,
    fun t => F fun x => t (ι x), ?_, ?_, fun U => ?_⟩
  · exact hF.comp (continuous_pi fun x => continuous_apply _)
  · intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · exact hR p hp
    · obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hp
      exact ⟨hlj, hjh⟩
  · refine congrArg F (funext ?_)
    rintro (b | p) <;> rfl
end Flat
section Elimination
variable {B : Block μ} {j k : ℤ} {R : Finset (ℤ × SliceLink μ)}
theorem flattened_properties
    (hcond : BlockConditionalLawStatement)
    (hker : KernelSymmetryAndGaugeInvariance.Statement)
    (hcalc : FieldCalculus.AllRules)
    {β : ℝ} (hβ : 0 < β) {ν : Measure (GaugeField 1)}
    (hν : ν ∈ gibbsClass (zero_lt_one (α := ℝ)) β) (S : Stack) (hj : S.IsInteriorLevel j)
    {f : (B.links → specialUnitary) → ℂ} (hf : IsRealEntryPolynomial f) (h : B.AdjacentPairs j k R)
    (k' lo hi : ℤ) (hk' : k' ∈ S.levels) (hne : k' ≠ j) (hlo : S.lower ≤ lo) (hhi : hi ≤ S.upper)
    (hlj : lo ≤ j) (hjh : j ≤ hi) (hR : ∀ p ∈ R, lo ≤ p.1 ∧ p.1 ≤ hi)
    (hdens : ∀ (U : GaugeField 1) (v : B.links → specialUnitary),
      S.densityAt B β U j v = linkProductKernel β v (S.blockValues B U k') *
        (Complex.exp (-B.sliceEnergy β v (S.rimValues B U j)) *
          linkProductKernel β v (S.blockValues B U k)))
    {φ : (B.links ⊕ R → specialUnitary) → ℂ} (hφc : Continuous φ)
    {H : (B.links ⊕ R → specialUnitary) → ℂ} (hH : H ∈ smoothSet) (hHr : ∀ u, (H u).im = 0)
    (hp : ∀ (w : B.links → specialUnitary) (z : R → specialUnitary),
      f w * ∫ v, linkProductKernel β v w * h.weighted β φ (Sum.elim v z) ∂haarPi B.links =
        ∫ v, linkProductKernel β v w * H (Sum.elim v z) ∂haarPi B.links) :
    h.flattened β H ∈ smoothSet ∧ (∀ u, (h.flattened β H u).im = 0) ∧
      S.IsRealContinuousOfLevels μ lo hi
        (fun U => h.flattened β H (S.blockPairVariables B R U j)) ∧
      ∫ U, f (S.blockValues B U k') * φ (S.blockPairVariables B R U j) ∂ν =
        ∫ U, h.flattened β H (S.blockPairVariables B R U j) ∂ν := by
  have : Nonempty B.links := B.links_nonempty.to_subtype
  have : Nonempty (B.links ⊕ R) := ⟨Sum.inl (Classical.arbitrary _)⟩
  have hE := isRealEntryPolynomial_sliceEnergyFn h hker hβ
  have hEs : sliceEnergyFn h β ∈ smoothSet :=
    (hcalc.2.2 (B.links ⊕ R)).2.2.2.2.2.1.1 _ hE.1
  have hexp : (fun u => Complex.exp (sliceEnergyFn h β u)) ∈ smoothSet :=
    (hcalc.2.2 (B.links ⊕ R)).2.2.2.2.1.1 _ hEs hE.2
  have hCp : ∀ u, (kernelFn h β u).im = 0 ∧ 0 < (kernelFn h β u).re := fun u =>
    linkProductKernel_real_pos hker hβ B _ _
  have hC : kernelFn h β ∈ smoothSet := kernelFn_mem_smoothSet h hcalc hβ
  have hCi : (fun u => (kernelFn h β u)⁻¹) ∈ smoothSet :=
    (hcalc.2.2 (B.links ⊕ R)).2.2.2.2.1.2 _ hC hCp
  have hC0 : ∀ u, kernelFn h β u ≠ 0 := fun u e => by
    have := (hCp u).2
    rw [e] at this
    simp at this
  have eflat : h.flattened β H =
      fun u => Complex.exp (sliceEnergyFn h β u) * (kernelFn h β u)⁻¹ * H u := by
    funext u
    rw [Block.AdjacentPairs.flattened, div_eq_mul_inv]
    rfl
  have hflat : h.flattened β H ∈ smoothSet := by
    rw [eflat]
    exact mul_mem_smoothSet hcalc (mul_mem_smoothSet hcalc hexp hCi) hH
  have hflatr : ∀ u, (h.flattened β H u).im = 0 := by
    intro u
    rw [eflat]
    have h₁ := im_cexp_of_im_eq_zero (hE.2 u)
    have h₂ := (hCp u).1
    have h₃ := hHr u
    simp [Complex.mul_im, Complex.inv_im, h₁, h₂, h₃]
  have hflatc : Continuous (h.flattened β H) := continuous_of_mem_smoothSet hflat
  refine ⟨hflat, hflatr, isRealContinuousOfLevels_comp S lo hi hlj hjh hR hflatc hflatr, ?_⟩
  have hHc : ∀ u, H u = Complex.exp (-sliceEnergyFn h β u) * kernelFn h β u *
      h.flattened β H u := by
    intro u
    rw [eflat, Complex.exp_neg]
    have h₁ := Complex.exp_ne_zero (sliceEnergyFn h β u)
    have h₂ := hC0 u
    field_simp
  obtain ⟨hrep, hce, -⟩ := hcond μ β hβ S j hj B
  have hav : ∀ U, S.blockAverage B β j
      (fun U => f (S.blockValues B U k') * φ (S.blockPairVariables B R U j)) U =
      S.blockAverage B β j
        (fun U => h.flattened β H (S.blockPairVariables B R U j)) U := by
    intro U
    have hblock : ∀ v, S.blockPairVariables B R (S.withTransported B U j v) j =
        Sum.elim v (S.pairVariables R U) := by
      intro v
      obtain ⟨-, hin, hout⟩ := hrep U v
      funext x
      rcases x with b | p
      · exact hin b
      · exact hout p.1.1 ⟨hlo.trans (hR p.1 p.2).1, (hR p.1 p.2).2.trans hhi⟩ p.1.2
          (h.avoids_block p.1 p.2)
    have hw : ∀ v, S.blockValues B (S.withTransported B U j v) k' =
        S.blockValues B U k' := by
      intro v
      obtain ⟨-, -, hout⟩ := hrep U v
      funext b
      exact hout k' hk' b.1 fun e => hne e.1
    have hψ : ∀ v, h.weighted β φ (Sum.elim v (S.pairVariables R U)) =
        Complex.exp (-B.sliceEnergy β v (S.rimValues B U j)) *
          linkProductKernel β v (S.blockValues B U k) * φ (Sum.elim v (S.pairVariables R U)) :=
      fun v => rfl
    have hHv : ∀ v, H (Sum.elim v (S.pairVariables R U)) =
        Complex.exp (-B.sliceEnergy β v (S.rimValues B U j)) *
          linkProductKernel β v (S.blockValues B U k) *
          h.flattened β H (Sum.elim v (S.pairVariables R U)) :=
      fun v => hHc _
    have h₁ : ∀ v, f (S.blockValues B (S.withTransported B U j v) k') *
        φ (S.blockPairVariables B R (S.withTransported B U j v) j) *
        S.densityAt B β U j v =
        f (S.blockValues B U k') * (linkProductKernel β v (S.blockValues B U k') *
          h.weighted β φ (Sum.elim v (S.pairVariables R U))) := by
      intro v
      rw [hblock, hw, hdens, hψ]
      ring
    have h₂ : ∀ v, h.flattened β H
        (S.blockPairVariables B R (S.withTransported B U j v) j) *
        S.densityAt B β U j v =
        linkProductKernel β v (S.blockValues B U k') * H (Sum.elim v (S.pairVariables R U)) := by
      intro v
      rw [hblock, hdens, hHv]
      ring
    unfold Stack.blockAverage
    simp only [h₁, h₂]
    rw [integral_const_mul, hp]
  have hc₁ : Continuous fun U : GaugeField 1 => f (S.blockValues B U k') :=
    hf.1.continuous.comp (continuous_blockValues S B k')
  have hc₂ : Continuous fun U : GaugeField 1 => φ (S.blockPairVariables B R U j) :=
    hφc.comp (continuous_blockPairVariables S B R j)
  have hc₃ : Continuous fun U : GaugeField 1 =>
      h.flattened β H (S.blockPairVariables B R U j) :=
    hflatc.comp (continuous_blockPairVariables S B R j)
  obtain ⟨M₁, hM₁⟩ := exists_norm_bound_of_continuous hf.1.continuous
  obtain ⟨M₂, hM₂⟩ := exists_norm_bound_of_continuous hφc
  obtain ⟨M₃, hM₃⟩ := exists_norm_bound_of_continuous hflatc
  have hobs₁ : IsBoundedObservable
      fun U => f (S.blockValues B U k') * φ (S.blockPairVariables B R U j) := by
    refine ⟨(hc₁.mul hc₂).measurable, M₁ * M₂, fun U => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hM₁ _) (hM₂ _) (norm_nonneg _) ((norm_nonneg _).trans (hM₁ (S.blockValues B U k')))
  have hobs₂ : IsBoundedObservable
      fun U => h.flattened β H (S.blockPairVariables B R U j) :=
    ⟨hc₃.measurable, M₃, fun U => hM₃ _⟩
  have e₁ := ((hce _ hobs₁).2.2 ν hν).2.2
  have e₂ := ((hce _ hobs₂).2.2 ν hν).2.2
  rw [← e₁, ← e₂]
  exact integral_congr_ae (Filter.Eventually.of_forall hav)
theorem eliminate_slice
    (hcond : BlockConditionalLawStatement)
    (hker : KernelSymmetryAndGaugeInvariance.Statement)
    (hpass : MulThroughLinkKernelStatement)
    (hfacts : SeveralVariables.SeveralVariablesFacts)
    (hcalc : FieldCalculus.AllRules)
    {β : ℝ} (hβ : 0 < β) {ν : Measure (GaugeField 1)}
    (hν : ν ∈ gibbsClass (zero_lt_one (α := ℝ)) β) (S : Stack) (hj : S.IsInteriorLevel j)
    {f : (B.links → specialUnitary) → ℂ} (hf : IsRealEntryPolynomial f) (h : B.AdjacentPairs j k R)
    (k' lo hi : ℤ) (hk' : k' ∈ S.levels) (hne : k' ≠ j) (hlo : S.lower ≤ lo) (hhi : hi ≤ S.upper)
    (hlj : lo ≤ j) (hjh : j ≤ hi) (hR : ∀ p ∈ R, lo ≤ p.1 ∧ p.1 ≤ hi)
    (hdens : ∀ (U : GaugeField 1) (v : B.links → specialUnitary),
      S.densityAt B β U j v = linkProductKernel β v (S.blockValues B U k') *
        (Complex.exp (-B.sliceEnergy β v (S.rimValues B U j)) *
          linkProductKernel β v (S.blockValues B U k)))
    {φ : (B.links ⊕ R → specialUnitary) → ℂ} (hφ : φ ∈ smoothSet) (hφr : ∀ u, (φ u).im = 0) :
    OuterSliceElimination β ν S hf h k' lo hi φ := by
  have : Nonempty B.links := B.links_nonempty.to_subtype
  have : Nonempty (B.links ⊕ R) := ⟨Sum.inl (Classical.arbitrary _)⟩
  have hE := isRealEntryPolynomial_sliceEnergyFn h hker hβ
  have hEs : sliceEnergyFn h β ∈ smoothSet :=
    (hcalc.2.2 (B.links ⊕ R)).2.2.2.2.2.1.1 _ hE.1
  have hnegr : ∀ u, (-sliceEnergyFn h β u).im = 0 := fun u => by
    rw [Complex.neg_im, hE.2 u, neg_zero]
  have hexp : (fun u => Complex.exp (-sliceEnergyFn h β u)) ∈ smoothSet :=
    (hcalc.2.2 (B.links ⊕ R)).2.2.2.2.1.1 _ (neg_mem_smoothSet hcalc hEs) hnegr
  have hψ : h.weighted β φ ∈ smoothSet :=
    mul_mem_smoothSet hcalc (mul_mem_smoothSet hcalc hexp (kernelFn_mem_smoothSet h hcalc hβ)) hφ
  have hψc : Continuous (h.weighted β φ) := continuous_of_mem_smoothSet hψ
  have hψr : ∀ u, (h.weighted β φ u).im = 0 := by
    intro u
    have h₁ : (Complex.exp (-sliceEnergyFn h β u)).im = 0 := im_cexp_of_im_eq_zero (hnegr u)
    have h₂ : (kernelFn h β u).im = 0 := (linkProductKernel_real_pos hker hβ B _ _).1
    have h₃ := hφr u
    have e : h.weighted β φ u =
        Complex.exp (-sliceEnergyFn h β u) * kernelFn h β u * φ u := rfl
    rw [e]
    simp [Complex.mul_im, h₁, h₂, h₃]
  obtain ⟨hdom, hHs, hHr, hHp⟩ := hatSum_properties hpass hfacts hβ hf
    ⟨h.weighted β φ, hψc⟩ hψ hψr
  refine ⟨hψ, hψc, hdom, ?_⟩
  exact flattened_properties hcond hker hcalc hβ hν S hj hf h k' lo hi hk' hne hlo hhi hlj hjh hR hdens
    (continuous_of_mem_smoothSet hφ) hHs hHr hHp
end Elimination
theorem statement_holds (hcond : BlockConditionalLawStatement)
    (hker : KernelSymmetryAndGaugeInvariance.Statement)
    (hpass : MulThroughLinkKernelStatement)
    (hfacts : SeveralVariables.SeveralVariablesFacts)
    (hcalc : FieldCalculus.AllRules) : Statement := by
  intro μ β hβ ν hν S j hj B f hf
  have : Nonempty B.links := B.links_nonempty.to_subtype
  have h₁ : S.lower < j := hj.1
  have h₂ : j < S.upper := hj.2
  have hsym : ∀ u u' : B.links → specialUnitary, linkProductKernel β u u' = linkProductKernel β u' u :=
    fun u u' => (((hker β hβ).1 B.links).1 u u').1
  refine ⟨fun R h hR φ hφ hφr => ?_, fun R h hR φ hφ hφr => ?_⟩
  · refine eliminate_slice hcond hker hpass hfacts hcalc hβ hν S hj hf h (j - 1) j S.upper
      ⟨by omega, by omega⟩ (by omega) h₁.le le_rfl le_rfl h₂.le hR (fun U v => ?_) hφ hφr
    have e : S.densityAt B β U j v =
        Complex.exp (-B.sliceEnergy β v (S.rimValues B U j)) *
          linkProductKernel β (S.blockValues B U (j - 1)) v * linkProductKernel β v (S.blockValues B U (j + 1)) :=
      rfl
    rw [e, hsym (S.blockValues B U (j - 1)) v]
    ring
  · refine eliminate_slice hcond hker hpass hfacts hcalc hβ hν S hj hf h (j + 1) S.lower j
      ⟨by omega, by omega⟩ (by omega) le_rfl h₂.le h₁.le le_rfl hR (fun U v => ?_) hφ hφr
    have e : S.densityAt B β U j v =
        Complex.exp (-B.sliceEnergy β v (S.rimValues B U j)) *
          linkProductKernel β (S.blockValues B U (j - 1)) v * linkProductKernel β v (S.blockValues B U (j + 1)) :=
      rfl
    rw [e, hsym (S.blockValues B U (j - 1)) v]
    ring
end YangMills.Construction.TransferOperators.OutermostSliceElimination
end
