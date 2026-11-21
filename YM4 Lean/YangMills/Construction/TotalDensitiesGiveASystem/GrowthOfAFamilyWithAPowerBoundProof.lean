import YangMills.Construction.SystemsWithFiveBounds.ConditionsAtFixedConstantsProof
import YangMills.Construction.Torus.CentredFunctionalOfAFamilyOfConnectedFunctions
import YangMills.Construction.TotalDensitiesGiveASystem.GrowthOfAFamilyWithAPowerBound
import Mathlib
set_option autoImplicit false
open Filter Set
noncomputable section
namespace YangMills.Construction.TotalDensities
namespace PowerBoundedGrowth
private theorem mem_flatSchwartzSet_of_offDiagonal {n : ℕ} {φ : TestSpaces.PointTuple n → ℂ}
    (h : φ ∈ ConfigSpace.schwartzFlatOffDiagonal n) : φ ∈ TestSpaces.flatSchwartzSet n := by apply _root_.YangMills.SharedProofs.p12297 <;> assumption
private def flatSequenceOf (U : (p : ℕ) → TestSpaces.flatSchwartzSet p → ℂ) :
    ConfigSpace.FlatSequence
  | 0, c => c.1
  | m + 1, φ => U (m + 1) ⟨φ.1, mem_flatSchwartzSet_of_offDiagonal φ.2⟩
private theorem norm_le_of_ennreal_bound
    (hN : Continuum.TwoPresentations.PresentationsAgree) {n k : ℕ} {c : ℝ} {z : ℂ}
    (φ : ConfigSpace.SchwartzFn n) (hc : 0 ≤ c)
    (h : ENNReal.ofReal ‖z‖ ≤ ENNReal.ofReal c * TestSpaces.weightedSeminorm k φ.1) :
    ‖z‖ ≤ c * ConfigSpace.bracketNorm k φ := by apply _root_.YangMills.SharedProofs.p4988 <;> assumption
private theorem isSepFamilyFunctional_evalOnConfig {G : SeparatedTuples.TupleFunctional}
    (hf : TestSpaces.IsSepFunctional (LimitTheorem.evalOnMap G)) :
    ConfigSpace.IsSepFamilyFunctional (LimitTheorem.evalOnConfig G) := by apply _root_.YangMills.SharedProofs.p14370 <;> assumption
private theorem hasSchwingerSequence_flatSequenceOf
    (hN : Continuum.TwoPresentations.PresentationsAgree) {G : SeparatedTuples.TupleFunctional}
    {U : (p : ℕ) → TestSpaces.flatSchwartzSet p → ℂ}
    (hf : TestSpaces.IsSepFunctional (LimitTheorem.evalOnMap G))
    (hU : TestSpaces.IsSchwingerFamily (LimitTheorem.evalOnMap G) U) :
    LimitTheorem.HasSchwingerSequence G (flatSequenceOf U) := by
  refine ⟨isSepFamilyFunctional_evalOnConfig hf, fun _ => rfl, fun m => ⟨⟨?_, ?_⟩, fun X hX h => ?_⟩⟩
  · intro a b φ ψ χ e
    exact (hU.1 (m + 1) (by omega)).1 a b _ _ _ e
  · obtain ⟨k, c, hk, hc, hb⟩ := (hU.1 (m + 1) (by omega)).2.1
    exact ⟨k, c, hk, hc, fun φ =>
      norm_le_of_ennreal_bound hN (ConfigSpace.toSchwartzFn φ) hc
        (hb ⟨φ.1, mem_flatSchwartzSet_of_offDiagonal φ.2⟩)⟩
  · have hs : TestSpaces.HasSmoothComponents Set.univ X.1 := fun i => by
      obtain ⟨-, h₁, h₂, h₃⟩ := ConfigSpace.mem_realSmoothCompactIn_iff.1 (hX i)
      exact ⟨h₁, h₂, h₃⟩
    have et : ConfigSpace.tensorRealFamily X.1 = TestSpaces.tensorProdComplex X.1 := by
      funext x
      simp [ConfigSpace.tensorRealFamily, ConfigSpace.tensorFamily,
        TestSpaces.tensorProdComplex, TestSpaces.tensorProd]
    have hY : X.1 ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) (m + 1) :=
      (LimitTheorem.ofConfigTuple ⟨m + 1, X⟩).2.2
    have hv := (hU.1 (m + 1) (by omega)).2.2 ⟨X.1, hY⟩ hs (et ▸ mem_flatSchwartzSet_of_offDiagonal h)
    refine Eq.trans ?_ hv
    exact congrArg (U (m + 1)) (Subtype.ext et)
private theorem isRegular_of_testSpaces_isRegular {G : SeparatedTuples.TupleFunctional}
    (h : TestSpaces.IsRegular (LimitTheorem.evalOnMap G)) : LimitTheorem.IsRegular G := by apply _root_.YangMills.SharedProofs.p39455 <;> assumption
private theorem existsUnique_distribution_offDiagonal {n : ℕ} {Φ : TestSpaces.SepTupleOfCard n → ℝ}
    (h : ∃! u : TestSpaces.TestFnOn (TestSpaces.distinctLocus n) → ℂ,
      TestSpaces.IsDistribOn u ∧ ∀ X : TestSpaces.SepTupleOfCard n,
        TestSpaces.HasSmoothComponents Set.univ X.1 →
        ∃ h : TestSpaces.tensorProdComplex X.1 ∈
            TestSpaces.smoothCompactSupp (TestSpaces.distinctLocus n),
          u ⟨_, h⟩ = ((Φ X : ℝ) : ℂ)) :
    ∃! u, LimitTheorem.IsDistribution (LimitTheorem.offDiagonal n) u ∧
      LimitTheorem.AgreesOnTensors Φ u := by apply _root_.YangMills.SharedProofs.p64229 <;> assumption
private theorem evalOnMap_centredOf (S : LimitTheorem.CumulantFamily) :
    LimitTheorem.evalOnMap (LimitTheorem.centredOf S) = TestSpaces.centredOfCumulants S := by
  funext X
  show TestSpaces.centredOfCumulants S (TupleLists.ofList (TupleLists.toList X)) = _
  rw [TupleLists.ofList_toList]
end PowerBoundedGrowth
open PowerBoundedGrowth
theorem growthOfPowerBoundedFamily_holds (hG : SeparatedPowerBound.GrowthFromPowerSepBound)
    (hE : EntrywiseMultilinearity.Statement)
    (hCen : AmbientPoints.CentredOfConnectedFamilyProperties)
    (hN : Continuum.TwoPresentations.PresentationsAgree)
    (hD : TestSpaces.OffDiagonal.OffDiagonalFacts)
    (hOne : Continuum.UnifiedTestSpace.TestSpacesUnified)
    (hTwo : ConfigurationSpace.SmoothSubspaces) : GrowthOfPowerBoundedFamily := by
  intro C S hC hcl hP
  have hL : Conventions.IsAdmissibleBlockingFactor 13 := ⟨by decide, le_rfl⟩
  let s : Conventions.StandingParameters := ⟨13, hL, 1, 1⟩
  let F : AmbientPoints.ConnectedFamily s .euclidean :=
    ⟨(fun n hn X => S n hn (Continuum.SeparatedFourTuples.sepLenEquiv s n X)), hcl.multilinear s⟩
  have hone : ∀ (n : ℕ) (hn : 2 ≤ n),
      TestSpaces.UnifiedSeparatedTuples.AgreeOnComponents (F.fn n hn) (S n hn) := fun n hn f X e =>
    congrArg (S n hn) (Subtype.ext e)
  have hmult : ∀ (n : ℕ) (hn : 2 ≤ n), TestSpaces.IsMultilinearOnSep (S n hn) := fun n hn =>
    (((hE s).1 n (by omega)).2.2 _ _ (hone n hn)).1 (hcl.multilinear s n hn)
  obtain ⟨-, hFun, -, hCenE⟩ := (hE s).2
  have hfun : TestSpaces.IsSepFunctional (TestSpaces.centredOfCumulants S) :=
    (hFun.2.2 _ _ (hCenE F _ hone)).1 (hCen s .euclidean F).2.2.2.1
  have hcon := hG 1 5 C 6 S le_rfl hC (by norm_num) hmult hfun hP
  have hval : LimitTheorem.evalOnMap (LimitTheorem.centredOf S) = TestSpaces.centredOfCumulants S :=
    evalOnMap_centredOf S
  have hf : TestSpaces.IsSepFunctional (LimitTheorem.evalOnMap (LimitTheorem.centredOf S)) :=
    hval ▸ hfun
  have hg : TestSpaces.GrowthBound (10 + 5) (2 * SeparatedBound.extFactorAbs)
      (SeparatedPowerBound.powerBase 1 5 C) (20 + 6 : ℝ)
      (LimitTheorem.evalOnMap (LimitTheorem.centredOf S)) := hval ▸ hcon.growthBound (20 + 6) le_rfl
  obtain ⟨-, hc₀, hC₀, hκ₀, U, hU, hUb⟩ := hg
  have hreg : TestSpaces.IsRegular (LimitTheorem.evalOnMap (LimitTheorem.centredOf S)) :=
    ((hD 1 one_pos).2.2.1 (LimitTheorem.evalOnMap (LimitTheorem.centredOf S)) U hf hU).1
  refine ⟨⟨flatSequenceOf U, hasSchwingerSequence_flatSequenceOf hN hf hU, fun m φ => ?_⟩, hf,
    isRegular_of_testSpaces_isRegular hreg, fun n hn => ?_⟩
  · have hcoef : 0 ≤ 2 * SeparatedBound.extFactorAbs * SeparatedPowerBound.powerBase 1 5 C ^ (m + 1) *
        ((m + 1).factorial : ℝ) ^ (26 : ℝ) := by positivity
    have h := hUb (m + 1) (by omega) ⟨φ.1, mem_flatSchwartzSet_of_offDiagonal φ.2⟩
    have e : (20 + 6 : ℝ) = 26 := by norm_num
    rw [e] at h
    exact norm_le_of_ennreal_bound hN (ConfigSpace.toSchwartzFn φ) hcoef h
  obtain ⟨T, hT, -⟩ := hcon.existsUnique_extension n hn
  have hnpos : 0 < n := by omega
  obtain ⟨-, hres, -, -, -⟩ := hD n hnpos
  obtain ⟨⟨-, -, hs2, hs3⟩, -, -⟩ := hOne n hnpos
  have hin : ∀ φ : TestSpaces.flatSchwartzSet n, φ.1 ∈ FlatTensors.flatSchwartz n :=
    fun φ => hs3.symm ▸ φ.2
  let T' : TestSpaces.flatSchwartzSet n → ℂ := fun φ => T ⟨φ.1, hin φ⟩
  have hsm : ∀ (a : ℂ) (φ : TestSpaces.flatSchwartzSet n),
      a • φ.1 ∈ FlatTensors.flatSchwartz n := fun a φ => by
    have h : φ.1 ∈ ConfigurationSpace.flatSchwartzSet n := hin φ
    show a • φ.1 ∈ ConfigurationSpace.flatSchwartzSet n
    rw [ConfigurationSpace.flatSchwartzSet_eq_rapidDecaySet_inter] at h ⊢
    obtain ⟨-, ⟨-, -, -, hA⟩, -, -, -, hB⟩ := hTwo n hnpos
    exact ⟨hA a _ h.1, hB a _ h.2⟩
  have hlin : TestSpaces.IsCLinearOnFlat T' := fun a b φ ψ χ e => by
    obtain ⟨ha, hm⟩ := hT.1.1
    have e₁ := ha ⟨_, hsm a φ⟩ ⟨_, hsm b ψ⟩ ⟨χ.1, hin χ⟩ e
    have e₂ := hm a ⟨φ.1, hin φ⟩ ⟨_, hsm a φ⟩ rfl
    have e₃ := hm b ⟨ψ.1, hin ψ⟩ ⟨_, hsm b ψ⟩ rfl
    show T ⟨χ.1, hin χ⟩ = a * T ⟨φ.1, hin φ⟩ + b * T ⟨ψ.1, hin ψ⟩
    rw [e₁, e₂, e₃]
  set c : ℝ := 2 * SeparatedBound.extFactorAbs * SeparatedPowerBound.powerBase 1 5 C ^ n *
    (n.factorial : ℝ) ^ ((19 : ℝ) + 6) with hc
  have hb : ∀ φ : TestSpaces.flatSchwartzSet n, ENNReal.ofReal ‖T' φ‖ ≤
      ENNReal.ofReal |c| * TestSpaces.weightedSeminorm ((10 + 5) * n) φ.1 := fun φ => by
    have h := hcon.extension_bound n hn T hT ⟨φ.1, hin φ⟩
    have hk : 0 < (10 + 5) * n := Nat.mul_pos (by omega) hnpos
    have e : TestSpaces.weightedSeminorm ((10 + 5) * n) φ.1 =
        ConfigurationSpace.sobolevWeightNorm ((10 + 5) * n) φ.1 :=
      hs2 ⟨φ.1, (hin φ).1⟩ _ hk
    rw [e]
    exact h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_abs_self _)) _)
  obtain ⟨hsub, hdist⟩ :=
    hres T' ((10 + 5) * n) |c| hlin (Nat.mul_pos (by omega) hnpos) (abs_nonneg _) hb
  have hvalue : ∀ X : TestSpaces.SepTupleOfCard n, TestSpaces.HasSmoothComponents Set.univ X.1 →
      ∃ h : TestSpaces.tensorProdComplex X.1 ∈
          TestSpaces.smoothCompactSupp (TestSpaces.distinctLocus n),
        TestSpaces.OffDiagonal.restrictToCompactSupp hsub T' ⟨_, h⟩ = ((S n hn X : ℝ) : ℂ) := by
    intro X hX
    obtain ⟨u, -, hu⟩ := hreg.2 n hnpos
    obtain ⟨h, -⟩ := hu X hX
    refine ⟨h, ?_⟩
    have et : ConfigurationSpace.ofRealFun (TestSpaces.tensorProd X.1) =
        TestSpaces.tensorProdComplex X.1 := by
      funext x
      simp [ConfigurationSpace.ofRealFun, TestSpaces.tensorProdComplex, TestSpaces.tensorProd]
    have hflat : ConfigurationSpace.ofRealFun (TestSpaces.tensorProd X.1) ∈
        ConfigurationSpace.flatSchwartzSet n := by
      rw [et]
      exact hin ⟨_, hsub h⟩
    have e := hT.2 X.1 ⟨X.2, hX⟩ hflat
    have e₃ : TestSpaces.OffDiagonal.restrictToCompactSupp hsub T' ⟨_, h⟩ = T ⟨_, hflat⟩ :=
      congrArg T (Subtype.ext et.symm)
    rw [e₃]
    exact e
  refine existsUnique_distribution_offDiagonal
    ⟨TestSpaces.OffDiagonal.restrictToCompactSupp hsub T', ⟨hdist, hvalue⟩, ?_⟩
  rintro u ⟨hu, hv⟩
  refine (hD n hnpos).1 u _ hu hdist fun X hX h => ?_
  obtain ⟨h₁, e₁⟩ := hv X hX
  obtain ⟨h₂, e₂⟩ := hvalue X hX
  exact e₁.trans e₂.symm
end YangMills.Construction.TotalDensities
end
