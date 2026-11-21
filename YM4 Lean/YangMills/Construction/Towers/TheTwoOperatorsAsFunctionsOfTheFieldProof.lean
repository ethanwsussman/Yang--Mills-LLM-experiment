import YangMills.Construction.PeriodicOperators.JetOfALocalOperatorFunctionIsEntireProof
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.Towers.CovariantDifferenceOfAFieldIsLocalWithEntireKernels
import YangMills.Construction.Towers.FreeOperatorsAreRealOfFiniteRangeAndTrivialOnTheColourProof
import YangMills.Construction.Towers.SecondDifferentialOfAFieldIsLocalWithEntireKernelsProof
import YangMills.Construction.Towers.TheTwoOperatorsAsFunctionsOfTheField
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FieldFunctionsProof
open PeriodicOperators
open TwoOperators
open FieldHessian (kernelOfField)
section Entire
variable {F : PeriodicData}
def IsEntireInFinitelyMany (g : (F.Carrier → ℂ) → ℂ) : Prop :=
  ∃ (m : ℕ) (v : Fin m → F.Carrier) (h : (Fin m → ℂ) → ℂ),
    Differentiable ℂ h ∧ ∀ ζ, g ζ = h fun j => ζ (v j)
theorem differentiable_of_isHolomorphicIn
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) {l : ℕ}
    {h : Coordinates.ComplexCoordinates l → ℂ}
    (hh : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) univ fun z _ => h z) :
    Differentiable ℂ h := by
  intro b
  obtain ⟨D, hD⟩ := ((hH.1 l univ isOpen_univ).1 1 _ hh).2.2.1 b (mem_univ b)
  have hb : HasFDerivAt (fun z : Coordinates.ComplexCoordinates l => (fun _ : Fin 1 => h z)) D b :=
    hasFDerivAt_of_restrictScalars ℝ hD rfl
  exact (differentiableAt_pi.1 hb.differentiableAt) 0
theorem isHolomorphicIn_of_differentiable {l : ℕ} {h : Coordinates.ComplexCoordinates l → ℂ}
    (hd : Differentiable ℂ h) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) univ fun z _ => h z := by apply _root_.YangMills.Construction.PeriodicOperators.LocalJetEntire.holomorphicIn_of_differentiable <;> assumption
theorem isEntireInFinitelyMany_of_hasEntireKernelEntries
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) {I I' : PeriodicData}
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} (hT : HasEntireKernelEntries F I I' T)
    (i' : I'.Carrier) (i : I.Carrier) : IsEntireInFinitelyMany fun ζ => T ζ i' i := by
  obtain ⟨S, l, e, h, ⟨-, hh⟩, hv⟩ := hT i' i
  exact ⟨l, fun j => (e j : F.Carrier), h, differentiable_of_isHolomorphicIn hH hh, hv⟩
theorem IsEntireInFinitelyMany.zero : IsEntireInFinitelyMany (F := F) fun _ => 0 :=
  ⟨0, Fin.elim0, fun _ => 0, differentiable_const 0, fun _ => rfl⟩
theorem IsEntireInFinitelyMany.add {g g' : (F.Carrier → ℂ) → ℂ} (hg : IsEntireInFinitelyMany g)
    (hg' : IsEntireInFinitelyMany g') : IsEntireInFinitelyMany fun ζ => g ζ + g' ζ := by
  obtain ⟨m, v, h, hd, hv⟩ := hg
  obtain ⟨m', v', h', hd', hv'⟩ := hg'
  refine ⟨m + m', Fin.append v v', fun z => h (fun j => z (Fin.castAdd m' j)) +
    h' (fun j => z (Fin.natAdd m j)), ?_, fun ζ => ?_⟩
  · exact (hd.comp (differentiable_pi.2 fun j => differentiable_apply _)).add
      (hd'.comp (differentiable_pi.2 fun j => differentiable_apply _))
  · simp [hv, hv', Fin.append_left, Fin.append_right]
theorem IsEntireInFinitelyMany.mul {g g' : (F.Carrier → ℂ) → ℂ} (hg : IsEntireInFinitelyMany g)
    (hg' : IsEntireInFinitelyMany g') : IsEntireInFinitelyMany fun ζ => g ζ * g' ζ := by
  obtain ⟨m, v, h, hd, hv⟩ := hg
  obtain ⟨m', v', h', hd', hv'⟩ := hg'
  refine ⟨m + m', Fin.append v v', fun z => h (fun j => z (Fin.castAdd m' j)) *
    h' (fun j => z (Fin.natAdd m j)), ?_, fun ζ => ?_⟩
  · exact (hd.comp (differentiable_pi.2 fun j => differentiable_apply _)).mul
      (hd'.comp (differentiable_pi.2 fun j => differentiable_apply _))
  · simp [hv, hv', Fin.append_left, Fin.append_right]
theorem IsEntireInFinitelyMany.sum {J : Type} (s : Finset J) {g : J → (F.Carrier → ℂ) → ℂ}
    (hg : ∀ k, IsEntireInFinitelyMany (g k)) :
    IsEntireInFinitelyMany fun ζ => ∑ k ∈ s, g k ζ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsEntireInFinitelyMany.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hg a).add ih
theorem IsEntireInFinitelyMany.tsum_mul {J : Type} {M : Set J} (hM : M.Finite)
    {X Y : (F.Carrier → ℂ) → J → ℂ} (hz : ∀ ζ, ∀ k ∉ M, X ζ k * Y ζ k = 0)
    (hX : ∀ k, IsEntireInFinitelyMany fun ζ => X ζ k)
    (hY : ∀ k, IsEntireInFinitelyMany fun ζ => Y ζ k) :
    IsEntireInFinitelyMany fun ζ => ∑' k, X ζ k * Y ζ k := by
  have e : (fun ζ => ∑' k, X ζ k * Y ζ k) = fun ζ => ∑ k ∈ hM.toFinset, X ζ k * Y ζ k :=
    funext fun ζ => tsum_eq_sum fun k hk => hz ζ k (by simpa using hk)
  rw [e]
  exact IsEntireInFinitelyMany.sum _ fun k => (hX k).mul (hY k)
theorem IsEntireInFinitelyMany.congr {g g' : (F.Carrier → ℂ) → ℂ}
    (hg : IsEntireInFinitelyMany g) (e : ∀ ζ, g ζ = g' ζ) : IsEntireInFinitelyMany g' := by
  rwa [← funext e]
theorem IsEntireInFinitelyMany.exists_entry {g : (F.Carrier → ℂ) → ℂ} (k₀ : F.Carrier)
    (hg : IsEntireInFinitelyMany g) :
    ∃ (S : Set F.Carrier) (l : ℕ) (e : Fin l ≃ S) (h : Coordinates.ComplexCoordinates l → ℂ),
      IsEntireFn h ∧ ∀ ζ, g ζ = h (fieldValues e ζ) := by
  obtain ⟨m, v, h, hd, hv⟩ := hg
  have hS : (insert k₀ (range v)).Finite := (finite_range v).insert k₀
  have := hS.to_subtype
  have hne : Nonempty (insert k₀ (range v) : Set F.Carrier) := ⟨⟨k₀, mem_insert _ _⟩⟩
  let e := (Finite.equivFin (insert k₀ (range v) : Set F.Carrier)).symm
  refine ⟨_, _, e, fun w => h fun j => w (e.symm ⟨v j, Or.inr ⟨j, rfl⟩⟩), ⟨?_, ?_⟩, fun ζ => ?_⟩
  · exact Nat.card_pos
  · exact isHolomorphicIn_of_differentiable
      (hd.comp (differentiable_pi.2 fun j => differentiable_apply _))
  · rw [hv]
    refine congrArg h (funext fun j => ?_)
    exact congrArg (fun s : (insert k₀ (range v) : Set F.Carrier) => ζ s)
      (e.apply_symm_apply ⟨v j, Or.inr ⟨j, rfl⟩⟩).symm
end Entire
theorem tsum_im_eq_zero {J : Type} {a : J → ℂ} (h : ∀ k, (a k).im = 0) : (∑' k, a k).im = 0 := by apply _root_.YangMills.Construction.Tower.FreeOperatorsRealLocal.im_tsum_eq_zero <;> assumption
section Field
variable {L : ℕ}
theorem expField_mem (hE : Matrices.ComplexMatrix2.ExpLogEstimates)
    (hF : Matrices.ComplexMatrix2.NormExpLogBasics)
    (ζ : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ) :
    FullSpace.expField ζ ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldHessianEntries.expField_mem <;> assumption
end Field
section Middle
variable {L : ℕ}
theorem finite_setOf_endpoint_eq (x : FullSpace.Vertex L 0 0) :
    {k : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) |
      x = k.2.1.terminal ∨ x = k.2.1.initial}.Finite := by
  let T : Set (FullSpace.Vertex L 0 0) := {x} ∪
    range (fun μ : Fin 4 => x + InfiniteLattice.axisStep (meshAt L 0 0) μ) ∪
    range (fun μ : Fin 4 => x - InfiniteLattice.axisStep (meshAt L 0 0) μ)
  have hT : T.Finite := ((finite_singleton x).union (finite_range _)).union (finite_range _)
  have hf : ((univ : Set (Fin 3)) ×ˢ (T ×ˢ T)).Finite := finite_univ.prod (hT.prod hT)
  refine (hf.preimage (f := fun k : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) =>
    (k.1, k.2.1.terminal, k.2.1.initial)) ?_).subset ?_
  · rintro ⟨c, b⟩ _ ⟨c', b'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, h₁, h₂⟩ := h
    exact Prod.ext rfl (Subtype.ext (InfiniteLattice.Link.ext h₂ h₁))
  · rintro ⟨c, b⟩ hk
    obtain ⟨μ, hμ⟩ := b.2
    have hxs : x ∈ T := Or.inl (Or.inl rfl)
    refine ⟨mem_univ _, ?_, ?_⟩
    · rcases hk with h | h
      · change b.1.terminal ∈ T
        rw [← h]
        exact hxs
      · refine Or.inl (Or.inr ⟨μ, ?_⟩)
        change x + _ = b.1.terminal
        rw [h, ← hμ]
        abel
    · rcases hk with h | h
      · refine Or.inr ⟨μ, ?_⟩
        change x - _ = b.1.initial
        rw [h, ← hμ]
        abel
      · change b.1.initial ∈ T
        rw [← h]
        exact hxs
theorem finite_setOf_eq_endpoint (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    {k : Fin 3 × FullSpace.Vertex L 0 0 | k.2 = b.1.terminal ∨ k.2 = b.1.initial}.Finite := by
  have hf : ((univ : Set (Fin 3)) ×ˢ
      ({b.1.terminal, b.1.initial} : Set (FullSpace.Vertex L 0 0))).Finite :=
    finite_univ.prod ((finite_singleton _).insert _)
  exact hf.subset fun k hk => ⟨mem_univ _, hk⟩
end Middle
private def firstAxisEdge {L : ℕ} (x : FullSpace.Vertex L 0 0) :
    FullSpace.PositiveEdge (meshAt L 0 0) :=
  ⟨InfiniteLattice.Link.forwardFrom x 0, 0, by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem twoOperatorsAsFieldFunctions (hProd : TwoOperatorKernelProducts.Statement)
    (hD : CovDiffKernelLocalEntire)
    (hA : FieldHessian.Claim)
    (hR : RealFieldKernels.Statement)
    (hLoc : JetDomains.OpFunJetTheory)
    (hX : CovDiffTransposes.Claim)
    (hI : TowerIndexSets.Claim)
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : Matrices.ComplexMatrix2.ExpLogEstimates)
    (hF : Matrices.ComplexMatrix2.NormExpLogBasics) : TwoOperatorsAsFieldFunctions := by
  intro L hL
  have hc := fun ζ => expField_mem (L := L) hE hF ζ
  obtain ⟨hDl, hDe, hDz⟩ := hD L hL
  obtain ⟨hAl, hAe, -⟩ := hA L hL
  obtain ⟨pS, pB, -⟩ := hI L hL 0 0 le_rfl
  have lD : IsLocalOpFun (colourEdges L 0 0) (colourVertices L 0 0)
      (colourEdges L 0 0) FullSpace.covDiffKernelOfField := ⟨1, 2, hDl 1 one_pos⟩
  have lA : IsLocalOpFun (colourEdges L 0 0) (colourEdges L 0 0)
      (colourEdges L 0 0) (kernelOfField L) := ⟨1, 2, hAl 1 one_pos⟩
  have hLap : ∀ ζ, FullSpace.gaugeLaplacianAt ζ =
      compKernel (swapKernel (FullSpace.covDiffKernelOfField ζ))
        (FullSpace.covDiffKernelOfField ζ) :=
    fun ζ => (hProd L hL _ (hc ζ)).gaugeLaplacianKernel_eq
  have hMas : ∀ ζ i' i, FullSpace.massiveHessianAt ζ i' i = kernelOfField L ζ i' i +
      compKernel (FullSpace.covDiffKernelOfField ζ)
        (swapKernel (FullSpace.covDiffKernelOfField ζ)) i' i :=
    fun ζ => (hProd L hL _ (hc ζ)).massiveHessianKernel_eq
  have hTr : ∀ ζ, wTranspose (colourVertices L 0 0).weightOf (colourEdges L 0 0).weightOf
      (FullSpace.covDiffKernelOfField ζ) =
      swapKernel (FullSpace.covDiffKernelOfField ζ) :=
    fun ζ => ((hX L hL 0 0 le_rfl).2 _ (hc ζ)).2.1
  have lT : IsLocalOpFun (colourEdges L 0 0) (colourEdges L 0 0)
      (colourVertices L 0 0) (opFunTranspose FullSpace.covDiffKernelOfField) :=
    (hLoc.1 _ _ _ _ pB pS pB pB).2.2 _ lD
  have hDr : ∀ ζ ∈ realCoeffs L, ∀ i' i, (FullSpace.covDiffKernelOfField ζ i' i).im = 0 :=
    fun ζ hζ => (hR L hL ζ hζ).2.1
  have hAr : ∀ ζ ∈ realCoeffs L, ∀ i' i, (kernelOfField L ζ i' i).im = 0 :=
    fun ζ hζ => (hR L hL ζ hζ).2.2
  have eD := isEntireInFinitelyMany_of_hasEntireKernelEntries hH hDe
  have eA := isEntireInFinitelyMany_of_hasEntireKernelEntries hH hAe
  refine ⟨hc, fun ζ => (hProd L hL _ (hc ζ)).represents_gaugeLaplacian,
    fun ζ => (hProd L hL _ (hc ζ)).represents_massiveHessian, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · have e : FullSpace.gaugeLaplacianAt (L := L) = opFunComp (F := colourEdges L 0 0)
        (I' := colourVertices L 0 0) (I := colourEdges L 0 0) (I'' := colourVertices L 0 0)
        (opFunTranspose FullSpace.covDiffKernelOfField) FullSpace.covDiffKernelOfField := by
      funext ζ
      rw [hLap ζ]
      exact congrArg (fun K => compKernel K (FullSpace.covDiffKernelOfField ζ)) (hTr ζ).symm
    rw [e]
    exact (hLoc.1 _ _ _ _ pB pB pS pS).2.1 _ _ lT lD
  · intro i' i
    have hr : IsEntireInFinitelyMany (F := colourEdges L 0 0)
        fun ζ => FullSpace.gaugeLaplacianAt ζ i' i := by
      refine (IsEntireInFinitelyMany.tsum_mul (F := colourEdges L 0 0)
        (J := Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0))
        (X := fun ζ k => FullSpace.covDiffKernelOfField ζ k i')
        (Y := fun ζ k => FullSpace.covDiffKernelOfField ζ k i) (finite_setOf_endpoint_eq i'.2)
        (fun ζ k hk => ?_) (fun k => eD k i') (fun k => eD k i)).congr
        fun ζ => (congrFun (congrFun (hLap ζ) i') i).symm
      rw [hDz ζ k i' (fun h => hk (Or.inl h)) (fun h => hk (Or.inr h)), zero_mul]
    exact hr.exists_entry (0, firstAxisEdge i'.2)
  · intro ζ hζ i' i
    rw [hLap ζ]
    refine tsum_im_eq_zero fun k => ?_
    change (FullSpace.covDiffKernelOfField ζ k i' * FullSpace.covDiffKernelOfField ζ k i).im = 0
    rw [Complex.mul_im, hDr ζ hζ k i', hDr ζ hζ k i]
    simp
  · have e : FullSpace.massiveHessianAt (L := L) = opFunAdd (F := colourEdges L 0 0)
        (I' := colourEdges L 0 0) (I := colourEdges L 0 0) (kernelOfField L)
        (opFunComp (I := colourVertices L 0 0) FullSpace.covDiffKernelOfField
          (opFunTranspose FullSpace.covDiffKernelOfField)) := by
      funext ζ i' i
      rw [hMas ζ i' i]
      exact congrArg (fun K => kernelOfField L ζ i' i +
        compKernel (FullSpace.covDiffKernelOfField ζ) K i' i) (hTr ζ).symm
    rw [e]
    exact (hLoc.1 _ _ _ _ pB pB pB pB).1 _ _ lA
      ((hLoc.1 _ _ _ _ pB pS pB pB).2.1 _ _ lD lT)
  · intro i' i
    have hr : IsEntireInFinitelyMany (F := colourEdges L 0 0)
        fun ζ => FullSpace.massiveHessianAt ζ i' i := by
      refine ((eA i' i).add (IsEntireInFinitelyMany.tsum_mul (F := colourEdges L 0 0)
        (J := Fin 3 × FullSpace.Vertex L 0 0)
        (X := fun ζ k => FullSpace.covDiffKernelOfField ζ i' k)
        (Y := fun ζ k => FullSpace.covDiffKernelOfField ζ i k) (finite_setOf_eq_endpoint i'.2)
        (fun ζ k hk => ?_) (fun k => eD i' k) (fun k => eD i k))).congr
        fun ζ => (hMas ζ i' i).symm
      rw [hDz ζ i' k (fun h => hk (Or.inl h)) (fun h => hk (Or.inr h)), zero_mul]
    exact hr.exists_entry i'
  · intro ζ hζ i' i
    rw [hMas ζ i' i, Complex.add_im, hAr ζ hζ, zero_add]
    refine tsum_im_eq_zero fun k => ?_
    change (FullSpace.covDiffKernelOfField ζ i' k * FullSpace.covDiffKernelOfField ζ i k).im = 0
    rw [Complex.mul_im, hDr ζ hζ i' k, hDr ζ hζ i k]
    simp
end YangMills.Construction.Tower.FieldFunctionsProof
end
