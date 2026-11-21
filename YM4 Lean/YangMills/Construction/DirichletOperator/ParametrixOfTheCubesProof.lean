import YangMills.Construction.DirichletOperator.ChainOfRemaindersProof
import YangMills.Construction.Dirichlet.BlockGreenLinearProof
import YangMills.Construction.Dirichlet.CommutatorBounds
import YangMills.Construction.Dirichlet.CommutatorIdentity
import YangMills.Construction.Dirichlet.FormsOperatorsProof
import YangMills.Construction.DirichletOperator.ParametrixOfTheCubes
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
open YangMills.Construction.Dirichlet YangMills.Construction.Dirichlet.WalkExpansion
noncomputable section
namespace YangMills.Construction.Dirichlet.CubeParametrix
variable {d L : ℕ} {S aMinus aPlus : ℝ}
theorem restrictTo_of_mem {ξ : ℝ} {X : Set (PeriodicTorus d S)} (f : LatticeSite d S ξ → ℝ)
    {x : LatticeSite d S ξ} (hx : (x : PeriodicTorus d S) ∈ X) : restrictTo X f x = f x :=
  Set.indicator_of_mem (s := {x : LatticeSite d S ξ | (x : PeriodicTorus d S) ∈ X}) hx f
theorem restrictTo_of_not_mem {ξ : ℝ} {X : Set (PeriodicTorus d S)} (f : LatticeSite d S ξ → ℝ)
    {x : LatticeSite d S ξ} (hx : (x : PeriodicTorus d S) ∉ X) : restrictTo X f x = 0 := by apply _root_.YangMills.Construction.Dirichlet.RemainderChains.restrictTo_of_not_mem <;> assumption
theorem restrictTo_add {ξ : ℝ} (X : Set (PeriodicTorus d S)) (f g : LatticeSite d S ξ → ℝ) :
    restrictTo X (f + g) = restrictTo X f + restrictTo X g := by apply _root_.YangMills.Construction.Dirichlet.GreenLinearityProof.restrictTo_add <;> assumption
theorem dirichletLaplacian_add {ξ : ℝ} [Finite (LatticeSite d S ξ)]
    (W : Set (PeriodicTorus d S)) (E : Set (LatticeBond d S ξ)) (f g : LatticeSite d S ξ → ℝ) :
    dirichletLaplacian W E (f + g) = dirichletLaplacian W E f + dirichletLaplacian W E g := by apply _root_.YangMills.Construction.Dirichlet.GreenLinearityProof.dirichletLaplacian_add <;> assumption
theorem averagingOp_add (B : BlockSetting d L aMinus aPlus S)
    [Finite (LatticeSite d S B.ξ)] (f g : LatticeSite d S B.ξ → ℝ) :
    B.averagingOp (f + g) = B.averagingOp f + B.averagingOp g := by apply _root_.YangMills.Construction.Dirichlet.GreenLinearityProof.BlockOps.averagingOp_add <;> assumption
theorem fullOperator_add (B : BlockSetting d L aMinus aPlus S) [Finite (LatticeSite d S B.ξ)]
    (f g : LatticeSite d S B.ξ → ℝ) :
    B.fullOperator (f + g) = B.fullOperator f + B.fullOperator g := by
  simp only [BlockSetting.fullOperator, BlockSetting.blockOperator, dirichletLaplacian_add,
    restrictTo_add, averagingOp_add]
  abel
theorem fullOperator_zero (B : BlockSetting d L aMinus aPlus S) [Finite (LatticeSite d S B.ξ)] :
    B.fullOperator 0 = 0 := by
  have h := fullOperator_add B 0 0
  simpa using h
theorem fullOperator_sum (B : BlockSetting d L aMinus aPlus S) [Finite (LatticeSite d S B.ξ)]
    {ι : Type*} (s : Finset ι) (T : ι → LatticeSite d S B.ξ → ℝ) :
    B.fullOperator (∑ i ∈ s, T i) = ∑ i ∈ s, B.fullOperator (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fullOperator_zero B
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fullOperator_add, ih]
theorem finsum_mem_eq_sum_of_eq_zero_off {α : Type*} {C F : Set α} (hF : F.Finite) (hFC : F ⊆ C)
    {g : α → ℝ} (h : ∀ Q ∈ C, Q ∉ F → g Q = 0) :
    ∑ᶠ Q ∈ C, g Q = ∑ Q ∈ hF.toFinset, g Q := by
  rw [← finsum_mem_eq_finite_toFinset_sum g hF]
  refine finsum_mem_inter_support_eq g C F ?_
  ext Q
  constructor
  · rintro ⟨hQ, hs⟩
    exact ⟨by_contra fun hn => hs (h Q hQ hn), hs⟩
  · rintro ⟨hQ, hs⟩
    exact ⟨hFC hQ, hs⟩
theorem innerEnd_mem {ξ : ℝ} {W : Set (PeriodicTorus d S)} {b : LatticeBond d S ξ}
    (hb : IsBoundaryBond W b) : (innerEnd W b : PeriodicTorus d S) ∈ W := by apply _root_.YangMills.Construction.Dirichlet.Forms.innerEnd_mem <;> assumption
theorem innerEnd_eq {ξ : ℝ} (W : Set (PeriodicTorus d S)) (b : LatticeBond d S ξ) :
    b.source = innerEnd W b ∨ b.target = innerEnd W b := by
  unfold innerEnd
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl
theorem mem_baseNbhd (B : BlockSetting d L aMinus aPlus S) {p : PeriodicTorus d S}
    (hp : p ∈ B.Ω 0) : p ∈ B.baseNbhd := by
  have hzero : supNorm (p - p) ≤ 0 := by
    refine csInf_le ⟨0, ?_⟩ ⟨0, ?_, by simp⟩
    · rintro r ⟨v, _, rfl⟩
      exact norm_nonneg v
    · funext μ
      simp [torusProj]
  have hξ : 0 ≤ 4 * B.ξ := by
    have := B.isSeparatedChain.scale_pos
    linarith
  calc supSetDist {p} (B.Ω 0) ≤ ENNReal.ofReal (supNorm (p - p)) :=
        iInf₂_le_of_le p rfl (iInf₂_le_of_le p hp le_rfl)
    _ ≤ ENNReal.ofReal (4 * B.ξ) := ENNReal.ofReal_le_ofReal (hzero.trans hξ)
theorem claim_holds (hP : PartitionOfUnity.PartitionClaim)
    (hK : Commutator.CommutatorClaim) (hC : CommutatorFormulasHold)
    (hG : GreenLinearity.BlockGreenLinear) (hB : CentreCellFactsHold) : Claim := by
  intro d L aMinus aPlus hL S B hfl E hE f hf
  have hM : 3 * L * (L + 12) ≤ B.M := by
    have h₁ := hfl.1
    simp only [blockThreshold, blockLowerBound] at h₁
    have h₂ : 3 * (L : ℝ) * ((L : ℝ) + 12) ≤ (B.M : ℝ) := (le_max_left _ _).trans h₁
    exact_mod_cast h₂
  have hRM : L * (L + 9) ≤ B.R₁ * B.M := by
    have h₁ := hfl.2
    simp only [gapLowerBound] at h₁
    have h₂ : (L : ℝ) * ((L : ℝ) + 9) ≤ (B.R₁ : ℝ) * (B.M : ℝ) := (le_max_left _ _).trans h₁
    exact_mod_cast h₂
  obtain ⟨-, hbump, -, -⟩ := hP d L aMinus aPlus hL S B hM hRM
  obtain ⟨hformula, -, hsupp⟩ := hK d L aMinus aPlus hL S B
  have hsupp := hsupp hM hRM
  have facts := hB d L aMinus aPlus S hL B
  have := facts.finite_site
  have hWcell : ∀ Q : CentredCube d S, B.IsCellUnion (B.innerRegion Q) := fun Q =>
    ⟨{y | y ∈ B.centres ∧ B.cell y ⊆ B.cubePoints Q}, fun y hy => hy.1, rfl⟩
  have hWsub : ∀ Q : CentredCube d S, B.innerRegion Q ⊆ B.Ω 0 := by
    intro Q p hp
    simp only [BlockSetting.innerRegion, mem_iUnion] at hp
    obtain ⟨y, hy, hpy⟩ := hp
    exact facts.cell_subset y hy.1 hpy
  have key : ∀ Q ∈ B.coverCubes, ∀ x : LatticeSite d S B.ξ, (x : PeriodicTorus d S) ∈ B.Ω 0 →
      B.fullOperator (B.sandwichedGreen E Q f) x =
        B.latticeCutoff Q x ^ 2 * f x - B.cubeRemainder E Q f x := by
    intro Q hQ x hx
    have hrule := hE Q hQ
    have hgreen := hG d L aMinus aPlus hL S B (B.innerRegion Q) (E Q) (hWcell Q) hrule
    have hψ : VanishesOff (B.innerRegion Q)
        (B.cubeGreen E Q (pointwiseMul (B.latticeCutoff Q) f)) :=
      hgreen.vanishesOff _
    have hsol : B.blockOperator (B.innerRegion Q) (E Q)
        (B.cubeGreen E Q (pointwiseMul (B.latticeCutoff Q) f)) =
        restrictTo (B.innerRegion Q) (pointwiseMul (B.latticeCutoff Q) f) :=
      hgreen.blockOperator_blockGreen _
    have hvan : VanishesForRule B (B.innerRegion Q) (E Q) (B.latticeCutoff Q) :=
      { eq_zero_off := fun z hz hzW => by
          by_contra h0
          exact hzW ((hsupp Q hQ).site_facts z hz h0).mem_innerRegion
        eq_zero_innerEnd := fun b hb hbE => by
          by_contra h0
          have hz := hWsub Q (innerEnd_mem hb)
          exact hbE (((hsupp Q hQ).site_facts _ hz h0).boundary_mem_rule b hb (innerEnd_eq _ b)
            (E Q) hrule) }
    have hid := (hC d L aMinus aPlus hL S B (B.innerRegion Q) (E Q) (B.latticeCutoff Q)
      (hWcell Q) hrule hvan).1 _ hψ x hx
    have hres : restrictTo (B.Ω 0) (pointwiseMul (B.latticeCutoff Q)
        (B.cubeGreen E Q (pointwiseMul (B.latticeCutoff Q) f))) =
        B.sandwichedGreen E Q f := by
      funext z
      by_cases hz : (z : PeriodicTorus d S) ∈ B.Ω 0
      · exact restrictTo_of_mem _ hz
      · rw [restrictTo_of_not_mem _ hz]
        have h0 := hψ z fun hzW => hz (hWsub Q hzW)
        simp [BlockSetting.sandwichedGreen, pointwiseMul, h0]
    have hrem : B.cubeRemainder E Q f x =
        B.commutatorOp (B.latticeCutoff Q) (B.cubeGreen E Q (pointwiseMul (B.latticeCutoff Q) f)) x :=
      restrictTo_of_mem _ hx
    have hsq : pointwiseMul (B.latticeCutoff Q)
        (restrictTo (B.innerRegion Q) (pointwiseMul (B.latticeCutoff Q) f)) x =
        B.latticeCutoff Q x ^ 2 * f x := by
      by_cases h0 : B.latticeCutoff Q x = 0
      · simp [pointwiseMul, h0]
      · have hxW := ((hsupp Q hQ).site_facts x hx h0).mem_innerRegion
        simp only [pointwiseMul]
        rw [restrictTo_of_mem _ hxW]
        simp only [pointwiseMul]
        ring
    rw [hres, hsol, hsq] at hid
    rw [hid, hrem]
  have hfew : ∀ x : LatticeSite d S B.ξ,
      {Q | Q ∈ B.coverCubes ∧ B.latticeCutoff Q x ≠ 0}.Finite := by
    intro x
    refine (Set.finite_of_encard_le_coe (hbump.few_nonzero x)).subset ?_
    rintro Q ⟨hQ, h0⟩
    exact ⟨hQ, left_ne_zero_of_mul h0⟩
  have hF : {Q | Q ∈ B.coverCubes ∧ ∃ x, B.latticeCutoff Q x ≠ 0}.Finite := by
    refine (Set.finite_iUnion hfew).subset ?_
    rintro Q ⟨hQ, x, h0⟩
    exact mem_iUnion.mpr ⟨x, hQ, h0⟩
  have hFC : {Q | Q ∈ B.coverCubes ∧ ∃ x, B.latticeCutoff Q x ≠ 0} ⊆ B.coverCubes :=
    fun Q hQ => hQ.1
  have hoff : ∀ Q ∈ B.coverCubes, Q ∉ {Q | Q ∈ B.coverCubes ∧ ∃ x, B.latticeCutoff Q x ≠ 0} →
      ∀ x, B.latticeCutoff Q x = 0 := by
    intro Q hQ hn x
    by_contra h0
    exact hn ⟨hQ, x, h0⟩
  have hGf : B.approxGreen E f = ∑ Q ∈ hF.toFinset, B.sandwichedGreen E Q f := by
    funext z
    rw [Finset.sum_apply]
    refine finsum_mem_eq_sum_of_eq_zero_off hF hFC fun Q hQ hn => ?_
    simp [BlockSetting.sandwichedGreen, pointwiseMul, hoff Q hQ hn z]
  funext x
  by_cases hx : (x : PeriodicTorus d S) ∈ B.Ω 0
  · have hR : B.totalRemainder E f x = ∑ Q ∈ hF.toFinset, B.cubeRemainder E Q f x := by
      refine finsum_mem_eq_sum_of_eq_zero_off hF hFC fun Q hQ hn => ?_
      have hz : B.latticeCutoff Q = fun _ => 0 := funext (hoff Q hQ hn)
      have hrem : B.cubeRemainder E Q f x =
          B.commutatorOp (B.latticeCutoff Q)
            (B.cubeGreen E Q (pointwiseMul (B.latticeCutoff Q) f)) x :=
        restrictTo_of_mem _ hx
      rw [hrem, hformula _ _ x hx, hz]
      simp
    have hsq : ∑ Q ∈ hF.toFinset, B.latticeCutoff Q x ^ 2 = 1 := by
      rw [← hbump.squares_sum_one x (mem_baseNbhd B hx)]
      refine (finsum_mem_eq_sum_of_eq_zero_off hF hFC fun Q hQ hn => ?_).symm
      simp [hoff Q hQ hn x]
    rw [hGf, fullOperator_sum, Finset.sum_apply, Pi.sub_apply, hR,
      Finset.sum_congr rfl fun Q hQ => key Q (hFC (hF.mem_toFinset.mp hQ)) x hx,
      Finset.sum_sub_distrib, ← Finset.sum_mul, hsq, one_mul]
  · have hzero : ∀ g : LatticeSite d S B.ξ → ℝ, B.fullOperator g x = 0 := by
      intro g
      simp only [BlockSetting.fullOperator, BlockSetting.blockOperator, Pi.add_apply,
        dirichletLaplacian, restrictTo_of_not_mem _ hx, add_zero]
    have hR : B.totalRemainder E f x = 0 := by
      refine finsum_mem_eq_zero_of_forall_eq_zero fun Q _ => ?_
      exact restrictTo_of_not_mem _ hx
    rw [hzero, Pi.sub_apply, hR, hf x hx, sub_zero]
end YangMills.Construction.Dirichlet.CubeParametrix
