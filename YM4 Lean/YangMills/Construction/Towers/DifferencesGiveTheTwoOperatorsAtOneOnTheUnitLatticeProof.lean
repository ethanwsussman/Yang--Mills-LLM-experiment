import YangMills.Construction.Towers.RelationsOfTheIteratedAveragesOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperatorsProof
import YangMills.Construction.Towers.DifferencesGiveTheTwoOperatorsAtOneOnTheUnitLattice
import YangMills.Construction.Towers.FactsOfTheLeftChart
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.IdentityOperators
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Matrices
open CovDiffTransposes (HasTransposeKernel matrixKernel)
section Coefficients
theorem pauliCombination_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
variable {σ : Type}
theorem ofPauliCoeffs_mem_traceless (c : Fin 3 × σ → ℂ) (i : σ) :
    ofPauliCoeffs c i ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem ofPauliCoeffs_toPauliCoeffs (g : σ → ComplexMatrix2)
    (hg : ∀ i, g i ∈ ComplexMatrix2.traceless) :
    ofPauliCoeffs (toPauliCoeffs g) = g := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofPauliCoeffs_toPauliCoeffs <;> assumption
theorem ofPauliCoeffs_add (c c' : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (c + c') = ofPauliCoeffs c + ofPauliCoeffs c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_add <;> assumption
theorem traceFinsumPairing_ofPauliCoeffs (hP : OneLoop.PauliMatrixRelations)
    (a b : Fin 3 × σ → ℂ) (hb : (Function.support b).Finite) :
    traceFinsumPairing (ofPauliCoeffs a) (ofPauliCoeffs b) = ∑ᶠ ι, a ι * b ι := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.traceFinsumPairing_ofPauliCoeffs <;> assumption
theorem finsum_mul_self_add {N : Type} {u v : N → ℂ} (hu : (Function.support u).Finite)
    (hv : (Function.support v).Finite) :
    ∑ᶠ κ, (u + v) κ * (u + v) κ =
      ∑ᶠ κ, u κ * u κ + 2 * ∑ᶠ κ, u κ * v κ + ∑ᶠ κ, v κ * v κ := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset N, S = hu.toFinset ∪ hv.toFinset := ⟨_, rfl⟩
  have u0 : ∀ κ, κ ∉ S → u κ = 0 := fun κ h => by
    by_contra hn
    exact h (hS ▸ Finset.mem_union_left _ (hu.mem_toFinset.2 hn))
  have v0 : ∀ κ, κ ∉ S → v κ = 0 := fun κ h => by
    by_contra hn
    exact h (hS ▸ Finset.mem_union_right _ (hv.mem_toFinset.2 hn))
  have sum_eq : ∀ f : N → ℂ, (∀ κ, κ ∉ S → f κ = 0) → ∑ᶠ κ, f κ = ∑ κ ∈ S, f κ := fun f h =>
    finsum_eq_sum_of_support_subset f fun κ hκ => by
      by_contra hn
      exact hκ (h κ hn)
  rw [sum_eq _ fun κ h => by simp [u0 κ h, v0 κ h], sum_eq _ fun κ h => by simp [u0 κ h],
    sum_eq _ fun κ h => by simp [u0 κ h], sum_eq _ fun κ h => by simp [v0 κ h], Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun κ _ => by
    simp only [Pi.add_apply]
    ring
end Coefficients
section Edges
variable {L k j : ℕ}
theorem opposite_isPositivelyOriented (ha : 0 < meshAt L k j) {b : FullSpace.Edge L k j}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  rcases InfiniteLattice.xor_mem_positiveLinks ha b with ⟨h₁, _⟩ | ⟨h₁, _⟩
  · exact absurd (InfiniteLattice.mem_positiveLinks_iff.1 h₁) hb
  · exact InfiniteLattice.mem_positiveLinks_iff.1 h₁
theorem opposite_not_isPositivelyOriented (ha : 0 < meshAt L k j) {b : FullSpace.Edge L k j}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  rcases InfiniteLattice.xor_mem_positiveLinks ha b with ⟨_, h₂⟩ | ⟨_, h₂⟩
  · exact fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)
  · exact absurd (InfiniteLattice.mem_positiveLinks_iff.2 hb) h₂
theorem ofCoeffs_of_positive (c : (FullSpace.edgePauliCoordinates L k j).Index → ℂ)
    {b : FullSpace.Edge L k j} (hb : b.IsPositivelyOriented) :
    (FullSpace.edgePauliCoordinates L k j).ofCoeffs c b = ofPauliCoeffs c ⟨b, hb⟩ := by apply _root_.YangMills.Construction.Tower.FreeOperators.edgePauliCoordinates_ofCoeffs_apply <;> assumption
theorem ofCoeffs_of_not_positive (ha : 0 < meshAt L k j)
    (c : (FullSpace.edgePauliCoordinates L k j).Index → ℂ)
    {b : FullSpace.Edge L k j} (hb : ¬ b.IsPositivelyOriented) :
    (FullSpace.edgePauliCoordinates L k j).ofCoeffs c b =
      -ofPauliCoeffs c ⟨b.opposite, opposite_isPositivelyOriented ha hb⟩ := by
  classical
  show FullSpace.extendOddly (a := meshAt L k j)
    (fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0) b = _
  simp only [FullSpace.extendOddly, if_neg hb, dif_pos (opposite_isPositivelyOriented ha hb)]
theorem ofCoeffs_mem (ha : 0 < meshAt L k j) (c : (FullSpace.edgePauliCoordinates L k j).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L k j).ofCoeffs c ∈ FullSpace.complexEdgeForms (meshAt L k j) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterRelations.edgePauliCoordinates_ofCoeffs_mem <;> assumption
theorem ofCoeffs_coeffs (ha : 0 < meshAt L k j) {B : FullSpace.Edge L k j → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k j)) :
    (FullSpace.edgePauliCoordinates L k j).ofCoeffs ((FullSpace.edgePauliCoordinates L k j).coeffs B) = B := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact (ofCoeffs_of_positive _ hb).trans (pauliCombination_pauliCoeff (hB.1 b hb))
  · have e : ofPauliCoeffs ((FullSpace.edgePauliCoordinates L k j).coeffs B)
        ⟨b.opposite, opposite_isPositivelyOriented ha hb⟩ = B b.opposite :=
      pauliCombination_pauliCoeff (hB.1 _ (opposite_isPositivelyOriented ha hb))
    rw [ofCoeffs_of_not_positive ha _ hb, e, hB.2 b, neg_neg]
theorem basisForm_eq_ofCoeffs_indicator (ha : 0 < meshAt L k j)
    (ι : (FullSpace.edgePauliCoordinates L k j).Index) :
    FullSpace.basisForm (L := L) (k := k) (j := j) ι.1 ι.2 =
      (FullSpace.edgePauliCoordinates L k j).ofCoeffs
        (open Classical in fun κ => if κ = ι then 1 else 0) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : (FullSpace.edgePauliCoordinates L k j).Index → ℂ,
    c = (open Classical in fun κ => if κ = ι then 1 else 0) := ⟨_, rfl⟩
  rw [← hc]
  have hc₁ : c ι = 1 := by
    rw [hc]
    exact if_pos rfl
  have hc₀ : ∀ κ, κ ≠ ι → c κ = 0 := fun κ h => by
    rw [hc]
    exact if_neg h
  obtain ⟨a, ⟨b₀, h₀⟩⟩ := ι
  have hpos : ∀ (b : FullSpace.Edge L k j) (hb : b.IsPositivelyOriented),
      (if b = b₀ then ComplexMatrix2.pauliFamily a else 0) = ofPauliCoeffs c ⟨b, hb⟩ :=
    fun b hb => by
      show _ = ∑ a', c (a', ⟨b, hb⟩) • ComplexMatrix2.pauliFamily a'
      by_cases e : b = b₀
      · subst e
        rw [if_pos rfl, Finset.sum_eq_single a]
        · rw [show c (a, ⟨b, hb⟩) = 1 from hc₁, one_smul]
        · intro a' _ h
          rw [hc₀ _ fun h' => h (Prod.ext_iff.1 h').1, zero_smul]
        · intro h
          exact absurd (Finset.mem_univ a) h
      · rw [if_neg e]
        refine (Finset.sum_eq_zero fun a' _ => ?_).symm
        rw [hc₀ _ fun h' => e (congrArg Subtype.val (Prod.ext_iff.1 h').2), zero_smul]
  funext b
  by_cases hb : b.IsPositivelyOriented
  · have e : FullSpace.basisForm (L := L) (k := k) (j := j) a ⟨b₀, h₀⟩ b =
        if b = b₀ then ComplexMatrix2.pauliFamily a else 0 := by
      simp only [FullSpace.basisForm, FullSpace.extendOddly, if_pos hb]
    exact e.trans ((hpos b hb).trans (ofCoeffs_of_positive c hb).symm)
  · have e : FullSpace.basisForm (L := L) (k := k) (j := j) a ⟨b₀, h₀⟩ b =
        -(if b.opposite = b₀ then ComplexMatrix2.pauliFamily a else 0) := by
      simp only [FullSpace.basisForm, FullSpace.extendOddly, if_neg hb]
    exact e.trans ((congrArg Neg.neg (hpos _ (opposite_isPositivelyOriented ha hb))).trans
      (ofCoeffs_of_not_positive ha c hb).symm)
theorem basisForm_hasFiniteEdgeSupport (a : Fin 3)
    (b₀ : FullSpace.PositiveEdge (meshAt L k j)) :
    FullSpace.HasFiniteEdgeSupport (FullSpace.basisForm (L := L) (k := k) (j := j) a b₀) := by
  classical
  refine (Set.finite_singleton b₀.1).subset ?_
  rintro b ⟨hp, hne⟩
  by_contra hb
  apply hne
  have hb' : b ≠ b₀.1 := hb
  simp [FullSpace.basisForm, FullSpace.extendOddly, hp, hb']
end Edges
section Kernel
variable {L : ℕ}
abbrev coboundaryKernel (L : ℕ) :
    KernelMatrix (FullSpace.edgePauliCoordinates L 0 0).Index (vertexCoordinate (FullSpace.Face L 0 0)).Index :=
  matrixKernel (FullSpace.edgePauliCoordinates L 0 0) (vertexCoordinate (FullSpace.Face L 0 0))
    FullSpace.edgeCoboundary
theorem map_mem_complexSubmodule {r r' : PauliComponentsOfSymmetricKernel}
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (h : HasTransposeKernel r r' m) {f : r.space.index → ComplexMatrix2}
    (hf : f ∈ r.space.complexSubmodule) :
    m f ∈ r'.space.complexSubmodule := by apply _root_.YangMills.Construction.Tower.FullSpace.RescaledTrivialRelationsProof.map_mem_complexSubmodule <;> assumption
theorem meshAt_zero_zero_pos (hL : Conventions.IsAdmissibleBlockingFactor L) :
    0 < meshAt L 0 0 := by
  have h0 : 0 < L := by
    have := hL.2
    omega
  exact zpow_pos (by exact_mod_cast h0) _
theorem complexHessianKernel_one_eq (hP : OneLoop.PauliMatrixRelations)
    (hD : FaceTermDerivatives.Statement)
    (hS : HessianKernel.KernelProperties) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hU : (fun _ => 1) ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup)
    (mw : HasTransposeKernel (FullSpace.edgePauliCoordinates L 0 0) (vertexCoordinate (FullSpace.Face L 0 0))
      FullSpace.edgeCoboundary)
    (ι ι' : (FullSpace.edgePauliCoordinates L 0 0).Index) :
    FullSpace.complexHessianKernel (fun _ => 1) ι ι' =
      ∑ᶠ κ, coboundaryKernel L κ ι * coboundaryKernel L κ ι' := by
  have ha := meshAt_zero_zero_pos hL
  have hA := ((hS L hL 0 0 le_rfl).2 _ hU).1
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = FullSpace.complexActionHessian
    (L := L) (k := 0) (j := 0) (fun _ => 1) := ⟨_, rfl⟩
  rw [← hQ] at hA
  have hmem : ∀ ι : (FullSpace.edgePauliCoordinates L 0 0).Index,
      FullSpace.basisForm (L := L) (k := 0) (j := 0) ι.1 ι.2 ∈
        HessianKernel.finiteSupportComplexForms L 0 0 := fun ι =>
    ⟨by rw [basisForm_eq_ofCoeffs_indicator ha ι]; exact ofCoeffs_mem ha _,
      basisForm_hasFiniteEdgeSupport _ _⟩
  have hsq : ∀ E ∈ HessianKernel.finiteSupportComplexForms L 0 0,
      Q E E = traceFinsumPairing (FullSpace.edgeCoboundary E) (FullSpace.edgeCoboundary E) :=
    fun E hE => by
      rw [hQ]
      exact (((hD L hL 0 0 le_rfl).2 E hE.1).2 hE.2).2
  have hcoef : ∀ ι : (FullSpace.edgePauliCoordinates L 0 0).Index,
      FullSpace.edgeCoboundary (FullSpace.basisForm (L := L) (k := 0) (j := 0) ι.1 ι.2) =
        ofPauliCoeffs fun κ => coboundaryKernel L κ ι := fun ι => by
    rw [basisForm_eq_ofCoeffs_indicator ha ι]
    have hm : FullSpace.edgeCoboundary ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs
        (open Classical in fun κ => if κ = ι then 1 else 0)) ∈
        (vertexCoordinate (FullSpace.Face L 0 0)).space.complexSubmodule :=
      map_mem_complexSubmodule mw (ofCoeffs_mem ha _)
    exact (ofPauliCoeffs_toPauliCoeffs _ fun p => hm p (mem_univ p)).symm
  obtain ⟨E₁, hE₁⟩ : ∃ E, E = FullSpace.basisForm (L := L) (k := 0) (j := 0) ι.1 ι.2 :=
    ⟨_, rfl⟩
  obtain ⟨E₂, hE₂⟩ : ∃ E, E = FullSpace.basisForm (L := L) (k := 0) (j := 0) ι'.1 ι'.2 :=
    ⟨_, rfl⟩
  have h₁ : E₁ ∈ HessianKernel.finiteSupportComplexForms L 0 0 := hE₁ ▸ hmem ι
  have h₂ : E₂ ∈ HessianKernel.finiteSupportComplexForms L 0 0 := hE₂ ▸ hmem ι'
  have h₁₂ : E₁ + E₂ ∈ HessianKernel.finiteSupportComplexForms L 0 0 := by
    refine ⟨Submodule.add_mem _ h₁.1 h₂.1, (h₁.2.union h₂.2).subset ?_⟩
    rintro b ⟨hp, hne⟩
    by_contra hn
    apply hne
    have e₁ : E₁ b = 0 := by
      by_contra h
      exact hn (Or.inl ⟨hp, h⟩)
    have e₂ : E₂ b = 0 := by
      by_contra h
      exact hn (Or.inr ⟨hp, h⟩)
    simp [e₁, e₂]
  obtain ⟨u₁, hu₁⟩ : ∃ u, u = fun κ => coboundaryKernel L κ ι := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u, u = fun κ => coboundaryKernel L κ ι' := ⟨_, rfl⟩
  have hf₁ : (Function.support u₁).Finite := hu₁ ▸ mw.column_finite ι
  have hf₂ : (Function.support u₂).Finite := hu₂ ▸ mw.column_finite ι'
  have hd₁ : FullSpace.edgeCoboundary E₁ = ofPauliCoeffs u₁ := by rw [hE₁, hu₁]; exact hcoef ι
  have hd₂ : FullSpace.edgeCoboundary E₂ = ofPauliCoeffs u₂ := by rw [hE₂, hu₂]; exact hcoef ι'
  have hd₁₂ : FullSpace.edgeCoboundary (E₁ + E₂) = ofPauliCoeffs (u₁ + u₂) := by
    rw [ofPauliCoeffs_add, ← hd₁, ← hd₂]
    funext p
    show FullSpace.edgeCoboundary (E₁ + E₂) p =
      FullSpace.edgeCoboundary E₁ p + FullSpace.edgeCoboundary E₂ p
    simp only [FullSpace.edgeCoboundary, Pi.add_apply]
    abel
  have p₁ : Q E₁ E₁ = ∑ᶠ κ, u₁ κ * u₁ κ := by
    rw [hsq _ h₁, hd₁]
    exact traceFinsumPairing_ofPauliCoeffs hP _ _ hf₁
  have p₂ : Q E₂ E₂ = ∑ᶠ κ, u₂ κ * u₂ κ := by
    rw [hsq _ h₂, hd₂]
    exact traceFinsumPairing_ofPauliCoeffs hP _ _ hf₂
  have p₁₂ : Q (E₁ + E₂) (E₁ + E₂) = ∑ᶠ κ, (u₁ + u₂) κ * (u₁ + u₂) κ := by
    rw [hsq _ h₁₂, hd₁₂]
    refine traceFinsumPairing_ofPauliCoeffs hP _ _ ((hf₁.union hf₂).subset ?_)
    exact Function.support_add u₁ u₂
  have b₁ := (hA 1 E₁ h₁ E₂ h₂ (E₁ + E₂) h₁₂).1
  have b₂ := (hA 1 E₁ h₁ E₂ h₂ E₁ h₁).2.1
  have b₃ := (hA 1 E₁ h₁ E₂ h₂ E₂ h₂).2.1
  have b₄ := (hA 0 E₁ h₁ E₁ h₁ E₂ h₂).2.2
  rw [one_smul] at b₁ b₂ b₃
  have key : (2 : ℂ) * Q E₁ E₂ = 2 * ∑ᶠ κ, u₁ κ * u₂ κ := by
    have hs := finsum_mul_self_add hf₁ hf₂
    rw [← p₁₂, ← p₁, ← p₂, b₁, b₂, b₃, ← b₄] at hs
    linear_combination hs
  have e : Q E₁ E₂ = ∑ᶠ κ, u₁ κ * u₂ κ := mul_left_cancel₀ two_ne_zero key
  have e' : FullSpace.complexHessianKernel (L := L) (k := 0) (j := 0) (fun _ => 1) ι ι' =
      Q E₁ E₂ := by
    rw [hQ, hE₁, hE₂]
    rfl
  rw [e', e, hu₁, hu₂]
end Kernel
theorem coboundariesAtIdentity_holds
    (h₁ : LeftChartFacts.HoldEverywhere)
    (h₂ : FaceTermDerivatives.Statement)
    (h₃ : HessianKernel.KernelProperties)
    (h₄ : CovDiffTransposes.Claim)
    (h₅ : RowFiniteKernels.Claim)
    (h₆ : OneLoop.PauliMatrixRelations) : CoboundariesAtIdentity := by
  intro L hL
  refine ⟨fun l _ => (h₁ L 0 0 0 0 hL le_rfl le_rfl le_rfl).2.2.2.2.2.1.2 l, fun B hB => ?_⟩
  have ha := meshAt_zero_zero_pos hL
  have hU : (fun _ => 1) ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup := by
    refine ⟨fun _ => ?_, fun _ => by simp⟩
    show (1 : ComplexMatrix2).det = 1
    simp
  have mw := ((h₄ L hL 0 0 le_rfl).2 _ hU).1.edgeCoboundary
  have hrows : RowFinite (coboundaryKernel L) := mw.row_finite
  have hcols : RowFinite (swapKernel (coboundaryKernel L)) := mw.column_finite
  have hkernel : FullSpace.complexHessianKernel (L := L) (k := 0) (j := 0) (fun _ => 1) =
      compKernel (swapKernel (coboundaryKernel L)) (coboundaryKernel L) := by
    funext ι ι'
    rw [complexHessianKernel_one_eq h₆ h₂ h₃ hL hU mw ι ι']
    have hs : (Function.support fun κ =>
        coboundaryKernel L κ ι * coboundaryKernel L κ ι').Finite :=
      (mw.column_finite ι).subset fun κ h h0 => h (by
        have h0' : coboundaryKernel L κ ι = 0 := h0
        simp [h0'])
    exact (tsum_eq_finsum hs).symm
  have hg := map_mem_complexSubmodule mw hB
  have hcompose := (((h₅.1 _ _ _ hrows).2 _ _ hcols).2.2
    ((FullSpace.edgePauliCoordinates L 0 0).coeffs B)).2.2
  have hd : (vertexCoordinate (FullSpace.Face L 0 0)).coeffs (FullSpace.edgeCoboundary B) =
      applyKernel (coboundaryKernel L) ((FullSpace.edgePauliCoordinates L 0 0).coeffs B) :=
    funext fun κ => (mw.represents B hB κ).2
  have ht : (FullSpace.edgePauliCoordinates L 0 0).coeffs
      (PairedFunctionSpace.transposeOfValues (FullSpace.edgePauliCoordinates L 0 0).space
        (vertexCoordinate (FullSpace.Face L 0 0)).space FullSpace.edgeCoboundary
        (FullSpace.edgeCoboundary B)) =
      applyKernel (swapKernel (coboundaryKernel L))
        ((vertexCoordinate (FullSpace.Face L 0 0)).coeffs (FullSpace.edgeCoboundary B)) :=
    funext fun κ => (mw.transpose_represents _ hg κ).2
  have hm : PairedFunctionSpace.transposeOfValues (FullSpace.edgePauliCoordinates L 0 0).space
      (vertexCoordinate (FullSpace.Face L 0 0)).space FullSpace.edgeCoboundary
      (FullSpace.edgeCoboundary B) ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by
    classical
    unfold PairedFunctionSpace.transposeOfValues
    rw [dif_pos hg]
    exact Subtype.coe_prop _
  rw [← ofCoeffs_coeffs ha hm, ht, hd, ← hcompose, ← hkernel]
  rfl
end YangMills.Construction.Tower.IdentityOperators
end
