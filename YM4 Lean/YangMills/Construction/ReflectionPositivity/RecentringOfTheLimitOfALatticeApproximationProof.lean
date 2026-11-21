import YangMills.Construction.ReflectionPositivity.ComplementsToTheReconstructionProof
import YangMills.Construction.Continuum.RecentringRespectsTheOperationsOnCombinations
import YangMills.Construction.Continuum.ValueOfAFunctionalAtARecentredTuple
import YangMills.Construction.ReflectionPositivity.ApproximationCentredAtThePlaquetteMeans
import YangMills.Construction.ReflectionPositivity.ConnectedFunctionsOfTheLimitAreLimitsOfCumulants
import YangMills.Construction.ReflectionPositivity.LatticeFormulaForTheScalarProductProof
import YangMills.Construction.ReflectionPositivity.RecentringOfTheLimitOfALatticeApproximation
import YangMills.Construction.ReflectionPositivity.SymmetriesAndMirrorsOfTheLimit
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitCentring
open YangMills.Construction.ReflectionPositivity.AxisMirror (MirrorData)
open YangMills.Construction.LimitConventions (ApproxTriple cubicMotionGroup)
open YangMills.Construction.ReflectionPositivity.ApproximatingSequences (LatticeApproximation)
open YangMills.Construction.ReflectionPositivity.ApproximatingSequences.LatticeApproximation (IsBoundedForSomeM)
open YangMills.Construction.TupleLists (ofList ofList_toList toList)
open YangMills.Construction.Mirrors (ReflectingHyperplane)
open YangMills.Construction.TestSpaces (IsMultilinearSepFunctional centredPart centredPartFunctional
  centredPartFunctional_spanExtension_basisVec cumulantOne cumulantOne_eq centring)
open YangMills.Construction.SeparatedTuples (FormalSpan TupleFunctional RealValued SepTuple push pushSpan
  pushList formalMul spanIn conjugation linearExtend_basisVec invMap basisVec supportedIn)
theorem mem_supportedIn_of_mem_support {O : Set (Fin 4 → ℝ)} {Z : FormalSpan}
    (hZ : Z ∈ spanIn O) : ∀ X ∈ Z.support, X ∈ supportedIn O := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.mem_supportedIn_of_mem_support <;> assumption
theorem exists_eq_push_of_mem_support_pushSpan {r : (Fin 4 → ℝ) → Fin 4 → ℝ} {Z : FormalSpan}
    {X : SepTuple} (hX : X ∈ (pushSpan r Z).support) : ∃ Y ∈ Z.support, X = push r Y := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.exists_of_mem_support_pushSpan <;> assumption
theorem mem_support_of_mem_support_conjugation {Z : FormalSpan} {X : SepTuple}
    (hX : X ∈ (conjugation Z).support) : X ∈ Z.support := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.mem_support_of_mem_support_conjugation <;> assumption
theorem composable_push_reflect (M : ReflectingHyperplane) (hsurj : Function.Surjective M.reflect)
    {X Y : SepTuple} (hX : X ∈ supportedIn M.positiveSide) (hY : Y ∈ supportedIn M.positiveSide) :
    SepTuple.Composable (push M.reflect X) Y := by
  classical
  intro g hg k hk
  unfold push at hg
  split_ifs at hg with hsep
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    have hsub : tsupport (f ∘ invMap M.reflect) ⊆ {x | M.normalVec ⬝ᵥ x ≤ M.offset} := by
      have hc : Continuous fun x : Fin 4 → ℝ => M.normalVec ⬝ᵥ x := by
        unfold dotProduct
        fun_prop
      refine closure_minimal ?_ (isClosed_le hc continuous_const)
      intro x hx
      have hy : invMap M.reflect x ∈ M.positiveSide := hX f hf (subset_tsupport f hx)
      have hxy : M.reflect (invMap M.reflect x) = x := Function.invFun_eq (hsurj x)
      have hn := YangMills.Construction.Mirrors.dotProduct_self_ne_zero_of_mem M.normalVec_mem
      have e : ∀ y, M.normalVec ⬝ᵥ M.reflect y = 2 * M.offset - M.normalVec ⬝ᵥ y := by
        intro y
        simp only [ReflectingHyperplane.reflect, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        field_simp
        ring
      have hy' : M.offset < M.normalVec ⬝ᵥ invMap M.reflect x := hy
      have e' := e (invMap M.reflect x)
      rw [hxy] at e'
      change M.normalVec ⬝ᵥ x ≤ M.offset
      linarith
    exact Set.disjoint_left.2 fun x hx hx' =>
      not_lt.2 (hsub hx) (show M.offset < M.normalVec ⬝ᵥ x from hY k hk hx')
  · simp [SepTuple.nil] at hg
theorem spanExtension_pushSpan (F : TupleFunctional) (r : (Fin 4 → ℝ) → Fin 4 → ℝ)
    (h : F.IsInvariant r) (Z : FormalSpan) :
    F.spanExtension (pushSpan r Z) = F.spanExtension Z := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.spanExtension_pushSpan <;> assumption
theorem limitCentringTheorem_of_parts (hV : YangMills.Construction.CentredTupleValue.centredValueFormula)
    (hO : YangMills.Construction.Continuum.CentringRespectsOperations.CentringPreservesStructure)
    (hA : YangMills.Construction.ReflectionPositivity.CentredAtPlaquetteMeans)
    (hC : YangMills.Construction.ReflectionPositivity.UrsellOfLimitIsLimitOfCumulants)
    (hS : YangMills.Construction.ReflectionPositivity.LimitSymmetries.LimitHasSymmetries)
    (hH : YangMills.Construction.ReflectionPositivity.LimitMomentumBound.MomentumBoundTheorem) :
    LimitCentringTheorem := by
  refine ⟨fun s hs => hV s hs (listFunctional s hs.1) fun _ => rfl, fun D T s hb hrp hl => ?_⟩
  obtain ⟨hm, ⟨ō, hō⟩, hnew, hone, hzero⟩ := hA D T s hb hrp hl
  obtain ⟨hσ, -, ⟨hinv, hmir⟩, hpos⟩ := hS D T (fun X => s (ofList X)) hb hrp hl
  obtain ⟨hP, hConj, hIn, hAct, hId⟩ := hO s
  obtain ⟨hb', hrp', hlim⟩ := hnew ō hō
  have hval : ∀ Z : FormalSpan, (centredPartFunctional s).spanExtension Z =
      (listFunctional s hm.1).spanExtension (centring s Z) :=
    (hV s hm (listFunctional s hm.1) fun _ => rfl).1
  have hinv' : ∀ r ∈ cubicMotionGroup, ∀ X : SepTuple, s (ofList (push r X)) = s (ofList X) :=
    fun r hr X => hinv r hr X
  have hsurj : ∀ M : ReflectingHyperplane, Function.Surjective M.reflect := by
    intro M
    obtain ⟨⟨r, -, hrθ⟩, -⟩ := hmir M
    rw [← hrθ]
    exact r.surjective
  have hcomm : ∀ (M : ReflectingHyperplane) (Z : FormalSpan),
      centring s (pushSpan M.reflect Z) = pushSpan M.reflect (centring s Z) := by
    intro M Z
    obtain ⟨⟨r, hr, hrθ⟩, -⟩ := hmir M
    rw [← hrθ]
    exact hAct r hr (hinv' r hr) Z
  have hprod : ∀ (M : ReflectingHyperplane), ∀ Z ∈ spanIn M.positiveSide,
      centring s (formalMul (pushSpan M.reflect (conjugation Z)) Z) =
        formalMul (pushSpan M.reflect (conjugation (centring s Z))) (centring s Z) := by
    intro M Z hZ
    have hdef : ∀ X ∈ (pushSpan M.reflect (conjugation Z)).support, ∀ Y ∈ Z.support,
        SepTuple.Composable X Y := by
      intro X hX Y hY
      obtain ⟨X', hX', rfl⟩ := exists_eq_push_of_mem_support_pushSpan hX
      exact composable_push_reflect M (hsurj M)
        (mem_supportedIn_of_mem_support hZ X' (mem_support_of_mem_support_conjugation hX'))
        (mem_supportedIn_of_mem_support hZ Y hY)
    rw [hP _ _ hdef, hcomm, hConj]
  refine ⟨hm, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨ō, hō, hb', hrp', hlim⟩,
      fun f hf => ⟨cumulantOne_eq s f hf, hone f hf⟩, fun n hn X => hC D T s hl n hn X⟩
  · exact ⟨hP, hConj, fun r hr Z => hAct r hr (hinv' r hr) Z, fun O _ Z hZ => hIn O Z hZ⟩
  · refine ⟨fun r hr W => ?_, fun M Z hZ => ⟨?_, ?_⟩, hH.1 D T (listFunctional s hm.1) hb hrp hl,
      hH.1 D (withOffset T ō) (centredPartFunctional s) hb' hrp' hlim⟩
    · rw [hval, hval, hAct r hr (hinv' r hr) W]
      exact spanExtension_pushSpan _ r (fun X => hinv' r hr X) _
    · rw [hval, hprod M Z hZ]
    · exact (hpos M).1 (centring s Z) (hIn _ Z hZ)
  · intro hT
    have h1 : ∀ (f : (Fin 4 → ℝ) → ℝ)
        (hf : f ∈ YangMills.Construction.TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))),
        cumulantOne s f hf = 0 := by
      intro f hf
      rw [cumulantOne_eq]
      have h0 : (fun j => ∫ U, LatticeApproximation.smearedField T j f U ∂T.state j) =
          fun _ => (0 : ℝ) :=
        funext (hzero hT f hf)
      have ht := hone f hf
      rw [h0] at ht
      exact tendsto_nhds_unique ht tendsto_const_nhds
    refine ⟨h1, hId h1, ?_⟩
    funext X
    have h2 := hval (basisVec (toList X))
    rw [centredPartFunctional_spanExtension_basisVec, hId h1] at h2
    have h3 : (listFunctional s hm.1).spanExtension (basisVec (toList X)) = ((s X : ℝ) : ℂ) := by
      simp only [TupleFunctional.spanExtension, linearExtend_basisVec]
      exact congrArg (fun Y => ((s Y : ℝ) : ℂ)) (ofList_toList X)
    exact_mod_cast h2.trans h3
end YangMills.Construction.ReflectionPositivity.LimitCentring
end
