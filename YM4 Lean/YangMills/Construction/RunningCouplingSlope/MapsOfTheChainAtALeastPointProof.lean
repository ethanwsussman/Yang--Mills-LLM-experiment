import YangMills.Construction.RunningCouplingSlope.DriftOfALeastPointIsLinearProof
import YangMills.Construction.RunningCouplingSlope.LeastPointsAreGaugeImagesOfSmallTangentsProof
import YangMills.Construction.RunningCouplingSlope.MapsOfTheChainAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.RelationsOfTheChainAtARealPoint
import YangMills.Construction.Towers.BackgroundFormOfTheFunctionalOnASideProof
import YangMills.Construction.Towers.ProductOfTheBlockAverageWithItsTransposeOnTheSidesProof
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOnTheSidesProof
import YangMills.Construction.Towers.StepOfTheCovariantAveragesAtOneAtTheSideInfinityProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Matrix.Norms.L2Operator Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.ChainMapsAtMinimizersProof
open Filter Tower Matrices
open scoped Topology
section Basics
variable {L n k j : ℕ} [NeZero L]
instance {L n k j : ℕ} [NeZero L] : Fintype (Edge L n k j) := Fintype.ofFinite _
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
theorem finite_face (j : ℕ) : Finite (Face L n k j) := by apply _root_.YangMills.SharedProofs.p23234 <;> assumption
instance {j : ℕ} : Finite (Face L n k j) := finite_face j
instance {j : ℕ} : Fintype (Face L n k j) := Fintype.ofFinite _
instance {j : ℕ} : Fintype (PositiveEdge L n k j) := Fintype.ofFinite _
theorem compact_mul_mem {g h : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hh : h ∈ PeriodicLattice.compactGaugeGroup) :
    g * h ∈ PeriodicLattice.compactGaugeGroup := ComplexMatrix2.specialUnitary.mul_mem hg hh
theorem compact_inv_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem compact_det {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
theorem compact_isUnit_det {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit g.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
theorem compact_pathHolonomy {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ e, V e ∈ PeriodicLattice.compactGaugeGroup)
    (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy V Γ ∈ PeriodicLattice.compactGaugeGroup := by
  induction Γ with
  | nil => simp [PeriodicLattice.pathHolonomy]
  | cons e Γ ih =>
    simp only [PeriodicLattice.pathHolonomy, List.map_cons, List.prod_cons] at ih ⊢
    exact compact_mul_mem (hV e) ih
theorem coe_toSublattice {m : ℕ} {i i' : ℤ} (h : i ≤ i') (y : PeriodicLattice.Site L m i) :
    ((y.toSublattice i' : PeriodicLattice.Site L m i') : PeriodicLattice.FourTorus L m) = y := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.coe_toSublattice <;> assumption
theorem restrictVertex_zero (v : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction 0 v = v := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.restrictVertexFunction_zero <;> assumption
theorem restrictVertex_toSublattice (v : Vertex L n k 0 → ComplexMatrix2) {j : ℕ} (hj : j ≤ k)
    (y : Vertex L n k (j + 1)) :
    restrictVertexFunction j v (y.toSublattice (PeriodicLattice.levelDepth k j)) =
      restrictVertexFunction (j + 1) v y := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.restrictVertexFunction_toSublattice <;> assumption
theorem fieldSpace_subset_fieldsIn {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) :
    V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
  ⟨fun e he => compact_det (hV.1 e he), hV.2⟩
theorem edgeForm_ext {A B : edgeFormSpace L n k j}
    (h : ∀ e : Edge L n k j, e.IsPositivelyOriented →
      (A : Edge L n k j → ComplexMatrix2) e = (B : Edge L n k j → ComplexMatrix2) e) :
    A = B := by
  apply Subtype.ext
  funext e
  by_cases he : e.IsPositivelyOriented
  · exact h e he
  · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented he
    have e1 : (A : Edge L n k j → ComplexMatrix2) e =
        -(A : Edge L n k j → ComplexMatrix2) e.opposite := A.2.2 e.opposite
    have e2 : (B : Edge L n k j → ComplexMatrix2) e =
        -(B : Edge L n k j → ComplexMatrix2) e.opposite := B.2.2 e.opposite
    rw [e1, e2, h _ hp]
theorem extendOddly_of_pos (f : Edge L n k j → ComplexMatrix2) {e : Edge L n k j}
    (he : e.IsPositivelyOriented) : extendOddly f e = f e := by
  simp [extendOddly, he]
theorem extendOddly_of_not_pos (f : Edge L n k j → ComplexMatrix2) {e : Edge L n k j}
    (he : ¬e.IsPositivelyOriented) : extendOddly f e = -f e.opposite := by
  simp [extendOddly, he]
theorem extendOddly_mem
    (hx : ∀ e : Edge L n k j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    (f : Edge L n k j → ComplexMatrix2)
    (h : ∀ e : Edge L n k j, e.IsPositivelyOriented → f e ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace L n k j := by
  refine ⟨fun e he => ?_, fun e => ?_⟩
  · rw [extendOddly_of_pos f he]
    exact h e he
  · by_cases he : e.IsPositivelyOriented
    · have h' : ¬e.opposite.IsPositivelyOriented := by
        rcases hx e with ⟨_, h2⟩ | h2
        · exact h2
        · exact absurd he h2.2
      rw [extendOddly_of_pos f he, extendOddly_of_not_pos f h']
      rfl
    · have h' := PeriodicLattice.Bond.opposite_isPositivelyOriented he
      rw [extendOddly_of_pos f h', extendOddly_of_not_pos f he, neg_neg]
theorem conjugateBy_mem {g A : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy g A ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p2904 <;> assumption
theorem conjugateBy_add (g A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (A + B) =
      ComplexMatrix2.conjugateBy g A + ComplexMatrix2.conjugateBy g B := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_real_smul (g : ComplexMatrix2) (r : ℝ) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (r • A) = r • ComplexMatrix2.conjugateBy g A := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.conjugateBy_real_smul <;> assumption
theorem vertexFunction_mem {j : ℕ} (l : vertexFunctionSpace L n k j) (x : Vertex L n k j) :
    (l : Vertex L n k j → ComplexMatrix2) x ∈ ComplexMatrix2.hermitianTraceless :=
  l.2 x (Set.mem_univ x)
def covDiffForm {j : ℕ} (W : Edge L n k j → ComplexMatrix2)
    (hW : ∀ e, W e ∈ PeriodicLattice.compactGaugeGroup)
    (hx : ∀ e : Edge L n k j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented) :
    vertexFunctionSpace L n k j →ₗ[ℝ] edgeFormSpace L n k j where
  toFun l := ⟨covDiff W l, extendOddly_mem hx _ fun e _ =>
    ComplexMatrix2.hermitianTraceless.sub_mem (conjugateBy_mem (hW e) (vertexFunction_mem l _))
      (vertexFunction_mem l _)⟩
  map_add' l l' := edgeForm_ext fun e he => by
    change covDiff W (l + l' : vertexFunctionSpace L n k j) e =
      covDiff W l e + covDiff W l' e
    simp only [covDiff, extendOddly_of_pos _ he]
    change ComplexMatrix2.conjugateBy (W e) ((l : Vertex L n k j → ComplexMatrix2) e.target +
        (l' : Vertex L n k j → ComplexMatrix2) e.target) -
      ((l : Vertex L n k j → ComplexMatrix2) e.source +
        (l' : Vertex L n k j → ComplexMatrix2) e.source) = _
    rw [conjugateBy_add]
    abel
  map_smul' r l := edgeForm_ext fun e he => by
    change covDiff W (r • l : vertexFunctionSpace L n k j) e =
      r • covDiff W l e
    simp only [covDiff, extendOddly_of_pos _ he]
    change ComplexMatrix2.conjugateBy (W e) (r • (l : Vertex L n k j → ComplexMatrix2) e.target) -
      r • (l : Vertex L n k j → ComplexMatrix2) e.source = _
    rw [conjugateBy_real_smul, smul_sub]
def extendByZeroLinear : vertexFunctionSpace L n k k →ₗ[ℝ] vertexFunctionSpace L n k 0 where
  toFun g := ⟨_root_.YangMills.Construction.Tower.extendByZero (g : Vertex L n k k → ComplexMatrix2), fun x _ => by
    simp only [extendByZero]
    split_ifs with h
    · exact vertexFunction_mem g _
    · exact ComplexMatrix2.hermitianTraceless.zero_mem⟩
  map_add' g g' := Subtype.ext (funext fun x => by
    change _root_.YangMills.Construction.Tower.extendByZero _ x = _root_.YangMills.Construction.Tower.extendByZero _ x + _root_.YangMills.Construction.Tower.extendByZero _ x
    simp only [extendByZero]
    split_ifs with h
    · rfl
    · simp)
  map_smul' r g := Subtype.ext (funext fun x => by
    change _root_.YangMills.Construction.Tower.extendByZero _ x = r • _root_.YangMills.Construction.Tower.extendByZero _ x
    simp only [extendByZero]
    split_ifs with h
    · rfl
    · simp)
theorem restrictVertex_extendByZero (g : Vertex L n k k → ComplexMatrix2) :
    restrictVertexFunction k (_root_.YangMills.Construction.Tower.extendByZero g) = g := by
  funext y
  simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap, _root_.YangMills.Construction.Tower.extendByZero]
  have hle : PeriodicLattice.levelDepth k k ≤ PeriodicLattice.levelDepth k 0 := by
    simp only [PeriodicLattice.levelDepth]; omega
  have hc := coe_toSublattice hle y
  have hex : ∃ y' : Vertex L n k k, (y' : PeriodicLattice.FourTorus L n) =
      (y.toSublattice (PeriodicLattice.levelDepth k 0) : Vertex L n k 0) := ⟨y, hc.symm⟩
  rw [dif_pos hex]
  congr 1
  exact Subtype.ext (hex.choose_spec.trans hc)
theorem complexLogMean_comp_equiv (e : ι ≃ κ) (V : κ → ComplexMatrix2) :
    PeriodicLattice.complexLogMean (V ∘ e) = PeriodicLattice.complexLogMean V := by apply _root_.YangMills.Construction.Averaging.ExplicitRadiiProof.complexLogMean_comp_equiv <;> assumption
theorem complexMeanContour_mem_compact
    (hMF : ∀ m : ℕ, 1 ≤ m → Averaging.ComplexLogMeanProperties m)
    {y : Vertex L n k (j + 1)} {x : Vertex L n k j} {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ e, V e ∈ PeriodicLattice.compactGaugeGroup)
    [Nonempty (PeriodicLattice.AxisOrdering y x)]
    (hs : ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies V y x) <
      Averaging.centreOfMassDiameter) :
    PeriodicLattice.complexMeanContourHolonomy V y x ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.complexMeanContourHolonomy_mem <;> assumption
theorem inverseFourthPowerWeight_smul (L : ℕ) (M : ComplexMatrix2) :
    PeriodicLattice.inverseFourthPowerWeight L • M = ((L : ℝ) ^ (-4 : ℤ)) • M := by
  rw [PeriodicLattice.inverseFourthPowerWeight, Complex.coe_smul]
theorem xor_isPositive_opposite
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → ∀ e : Edge L n k j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.xor_isPositivelyOriented_opposite <;> assumption
theorem restrictVertex_restrictVertex (l : Vertex L n k 0 → ComplexMatrix2) {j : ℕ} (hj : j ≤ k) :
    restrictVertexFunction (j + 1) (restrictVertexFunction j l) = restrictVertexFunction (j + 1) l := by
  funext y
  exact restrictVertex_toSublattice l hj y
theorem restrictVertex_mem (l : vertexFunctionSpace L n k 0) (j : ℕ) (x : Vertex L n k j) :
    restrictVertexFunction j (l : Vertex L n k 0 → ComplexMatrix2) x ∈
      ComplexMatrix2.hermitianTraceless :=
  vertexFunction_mem l _
theorem norm_sub_one_sq {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    ‖g - 1‖ ^ 2 = 2 * traceDefect g := by apply _root_.YangMills.SharedProofs.p32894 <;> assumption
theorem traceDefect_nonneg {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    0 ≤ traceDefect g := by apply _root_.YangMills.SharedProofs.p3544 <;> assumption
theorem plaquetteCost_eq_traceDefect (U : Edge L n k 0 → ComplexMatrix2) (p : Face L n k 0) :
    PeriodicLattice.plaquetteCost U p = traceDefect (PeriodicLattice.plaquetteHolonomy U p) := by apply _root_.YangMills.SharedProofs.p12545 <;> assumption
theorem plaquetteHolonomy_mem {j : ℕ} {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k j) (p : Face L n k j) :
    PeriodicLattice.plaquetteHolonomy U p ∈ PeriodicLattice.compactGaugeGroup :=
  compact_pathHolonomy (fun e => hU.1 e (Set.mem_univ _)) _
theorem plaquetteAction_eq_sum (U : Edge L n k 0 → ComplexMatrix2) :
    plaquetteAction L n k U =
      ∑ p : Face L n k 0, traceDefect (PeriodicLattice.plaquetteHolonomy U p) := by
  simp only [plaquetteAction, PeriodicLattice.wilsonAction, finsum_eq_sum_of_fintype,
    plaquetteCost_eq_traceDefect]
def noiseCost (X : ChainPoint L n k) (i : Fin k) (c : PositiveEdge L n k (i + 1)) : ℝ :=
  (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c)
theorem chainAction_eq (a : ℝ) (X : ChainPoint L n k) :
    chainAction a X = plaquetteAction L n k X.fine +
      a * ∑ i : Fin k, ∑ c : PositiveEdge L n k (i + 1), noiseCost X i c := by
  simp only [chainAction, noiseCost, finsum_eq_sum_of_fintype]
theorem exists_top_forward (hlat : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (c : PositiveEdge L n k k) :
    ∃ (z : TorusFields.TorusSite (2 * L ^ n)) (μ : Fin 4),
      c.1 = PeriodicLattice.Bond.forwardFrom (topVertexOf z) μ := by
  have hd : PeriodicLattice.levelDepth k k = 0 := by simp [PeriodicLattice.levelDepth]
  have hlc := (hlat L n hL.1 hL.2 hn).1 (PeriodicLattice.levelDepth k k) (by rw [hd]; omega)
  obtain ⟨-, -, -, hex, hiff, -⟩ := hlc
  obtain ⟨μ, hμ⟩ := c.2
  obtain ⟨m, hm⟩ := hex 0 c.1.source
  have hN : 2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k k) = 2 * L ^ n := by
    simp [PeriodicLattice.halfPeriod, hd]
  let z : TorusFields.TorusSite (2 * L ^ n) := fun ν => ((m ν : ℤ) : ZMod (2 * L ^ n))
  have hz : topVertexOf z = c.1.source := by
    rw [hm]
    refine (hiff 0 _ _).2 fun ν => ?_
    rw [hN]
    refine (ZMod.intCast_eq_intCast_iff _ _ _).1 ?_
    simp [z]
  refine ⟨z, μ, ?_⟩
  rw [hz]
  refine PeriodicLattice.Bond.ext rfl ?_
  change c.1.target = c.1.source + PeriodicLattice.unitStep L n _ μ
  rw [← hμ]
  abel
theorem traceDefect_quaternion (q : ℍ[ℝ]) :
    traceDefect (SoftAverages.quaternionToMatrix q) = 1 - q.re := by apply _root_.YangMills.SharedProofs.p14120 <;> assumption
end Basics
section FiniteSets
theorem mem_complexSubmodule {Z : Type} {f : Z → ComplexMatrix2} :
    f ∈ (pairedFunctions Z).complexSubmodule ↔ ∀ z, f z ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.IterRelationsProof.mem_complexSubmodule_iff <;> assumption
theorem mem_realFunctions {Z : Type} {f : Z → ComplexMatrix2} :
    f ∈ GroupLieProduct.hermitianTracelessFunctions Z ↔
      ∀ z, f z ∈ ComplexMatrix2.hermitianTraceless := by
  simp [GroupLieProduct.hermitianTracelessFunctions, Submodule.mem_pi]
def PreservesReal {X Y : Type}
    (T : (pairedFunctions X).complexSubmodule →ₗ[ℂ] (pairedFunctions Y).complexSubmodule) : Prop :=
  ∀ l : (pairedFunctions X).complexSubmodule,
    (∀ x, l.1 x ∈ ComplexMatrix2.hermitianTraceless) →
      ∀ y, (T l).1 y ∈ ComplexMatrix2.hermitianTraceless
def toComplex {X : Type} (f : (pairedFunctions X).realSubmodule) :
    (pairedFunctions X).complexSubmodule :=
  ⟨f.1, mem_complexSubmodule.2 fun x => (mem_realFunctions.1 f.2 x).2⟩
theorem toComplex_mem {X : Type} (f : (pairedFunctions X).realSubmodule) (x : X) :
    (toComplex f).1 x ∈ ComplexMatrix2.hermitianTraceless :=
  mem_realFunctions.1 f.2 x
def HasTransposePair {X Y : Type} (f : (X → ComplexMatrix2) → Y → ComplexMatrix2) (c : ℂ) :
    Prop :=
  ∃ (T : (pairedFunctions X).complexSubmodule →ₗ[ℂ] (pairedFunctions Y).complexSubmodule)
    (T' : (pairedFunctions Y).complexSubmodule →ₗ[ℂ] (pairedFunctions X).complexSubmodule),
    (∀ l, (T l).1 = f l.1) ∧
      (∀ g l, traceFinsumPairing (T' g).1 l.1 = traceFinsumPairing g.1 (T l).1) ∧
      (∀ g, (T (T' g)).1 = c • g.1) ∧ PreservesReal T ∧ PreservesReal T'
theorem hasTransposePair_id {X : Type} : HasTransposePair (fun l : X → ComplexMatrix2 => l) 1 :=
  ⟨LinearMap.id, LinearMap.id, fun _ => rfl, fun _ _ => rfl, fun g => by simp,
    fun _ h => h, fun _ h => h⟩
theorem HasTransposePair.comp {X Y Z : Type} {f : (X → ComplexMatrix2) → Y → ComplexMatrix2}
    {g : (Y → ComplexMatrix2) → Z → ComplexMatrix2}
    {c d : ℂ} (hf : HasTransposePair f c) (hg : HasTransposePair g d) :
    HasTransposePair (fun l => g (f l)) (c * d) := by
  obtain ⟨T, T', a1, a2, a3, a4, a5⟩ := hf
  obtain ⟨S, S', b1, b2, b3, b4, b5⟩ := hg
  refine ⟨S ∘ₗ T, T' ∘ₗ S', fun l => ?_, fun h l => ?_, fun h => ?_, fun l hl => ?_, fun h hh => ?_⟩
  · change (S (T l)).1 = _
    rw [b1, a1]
  · change traceFinsumPairing (T' (S' h)).1 l.1 = traceFinsumPairing h.1 (S (T l)).1
    rw [a2, b2]
  · change (S (T (T' (S' h)))).1 = _
    have e : T (T' (S' h)) = c • S' h := Subtype.ext (a3 _)
    rw [e, map_smul]
    change c • (S (S' h)).1 = _
    rw [b3, smul_smul]
  · exact b4 (T l) (a4 l hl)
  · exact a5 (S' h) (b5 h hh)
variable {X Y : Type} [Finite X] [Finite Y]
theorem conjugateBy_map_add (W A C : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy W (A + C) =
      ComplexMatrix2.conjugateBy W A + ComplexMatrix2.conjugateBy W C := by
  simp only [ComplexMatrix2.conjugateBy, Matrix.mul_add, Matrix.add_mul]
theorem conjugateBy_complex_smul (W : ComplexMatrix2) (c : ℂ) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy W (c • A) = c • ComplexMatrix2.conjugateBy W A := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
theorem fullTrace_conjugateBy {W : ComplexMatrix2} (hW : W.det ≠ 0) (A : ComplexMatrix2) :
    ComplexMatrix2.fullTrace (ComplexMatrix2.conjugateBy W A) = ComplexMatrix2.fullTrace A := by apply _root_.YangMills.Construction.Tower.CubeAverageTranspose.fullTrace_conjugateBy <;> assumption
theorem fullTrace_inv_conj {W : ComplexMatrix2} (hW : W.det ≠ 0) (A : ComplexMatrix2) :
    ComplexMatrix2.fullTrace (W⁻¹ * A * W) = ComplexMatrix2.fullTrace A := by apply _root_.YangMills.Construction.Tower.CubeAverageTranspose.fullTrace_inv_mul_mul <;> assumption
theorem conjugateBy_inv_conj {W : ComplexMatrix2} (hW : W.det ≠ 0) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy W (W⁻¹ * A * W) = A := by apply _root_.YangMills.Construction.Tower.CubeAverageTranspose.conjugateBy_inv_mul_mul <;> assumption
theorem fullTrace_inv_conj_mul (W A C : ComplexMatrix2) :
    ComplexMatrix2.fullTrace ((W⁻¹ * A * W) * C) =
      ComplexMatrix2.fullTrace (A * ComplexMatrix2.conjugateBy W C) := by apply _root_.YangMills.Construction.Tower.CubeAverageTranspose.fullTrace_inv_mul_mul_mul <;> assumption
def weightedBlockSum (B : Y → Set X) (w : ℂ) (W : Y → X → ComplexMatrix2)
    (l : X → ComplexMatrix2) : Y → ComplexMatrix2 :=
  fun y => w • ∑ᶠ x ∈ B y, ComplexMatrix2.conjugateBy (W y x) (l x)
theorem hasTransposePair_weightedBlockSum (B : Y → Set X) (r : ℝ) (W : Y → X → ComplexMatrix2)
    (hB : ∀ x, ∃! y, x ∈ B y) (hN : ∀ y, ((B y).ncard : ℂ) * (r : ℂ) = 1)
    (hWr : ∀ y, ∀ x ∈ B y, W y x ∈ PeriodicLattice.compactGaugeGroup) :
    HasTransposePair (weightedBlockSum B (r : ℂ) W) (r : ℂ) := by
  classical
  cases nonempty_fintype X
  cases nonempty_fintype Y
  set w : ℂ := (r : ℂ) with hw
  have hW : ∀ y, ∀ x ∈ B y, (W y x).det ≠ 0 := fun y x hx => by
    rw [compact_det (hWr y x hx)]
    exact one_ne_zero
  let p : X → Y := fun x => (hB x).exists.choose
  have hp : ∀ x, x ∈ B (p x) := fun x => (hB x).exists.choose_spec
  have hmem : ∀ x y, x ∈ B y ↔ p x = y :=
    fun x y => ⟨fun h => (hB x).unique (hp x) h, fun h => h ▸ hp x⟩
  have hW' : ∀ x, (W (p x) x).det ≠ 0 := fun x => hW _ x (hp x)
  have hsum : ∀ (l : X → ComplexMatrix2) (y : Y), weightedBlockSum B w W l y =
      w • ∑ x, if p x = y then ComplexMatrix2.conjugateBy (W y x) (l x) else 0 := by
    intro l y
    simp only [weightedBlockSum, hmem]
    rw [finsum_eq_sum_of_fintype]
    simp only [finsum_eq_if]
  have hadd : ∀ l l' : X → ComplexMatrix2,
      weightedBlockSum B w W (l + l') = weightedBlockSum B w W l + weightedBlockSum B w W l' := by
    intro l l'
    funext y
    simp only [Pi.add_apply, hsum, ← smul_add, ← Finset.sum_add_distrib]
    refine congrArg (fun S : ComplexMatrix2 => w • S) (Finset.sum_congr rfl fun x _ => ?_)
    split_ifs
    · exact conjugateBy_map_add _ _ _
    · simp
  have hsmul : ∀ (c : ℂ) (l : X → ComplexMatrix2),
      weightedBlockSum B w W (c • l) = c • weightedBlockSum B w W l := by
    intro c l
    funext y
    simp only [Pi.smul_apply, hsum]
    rw [smul_comm c w]
    refine congrArg (fun S : ComplexMatrix2 => w • S) ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs
    · exact conjugateBy_complex_smul _ _ _
    · simp
  have hin₀ : ∀ l : X → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
      weightedBlockSum B w W l ∈ (pairedFunctions Y).complexSubmodule := by
    intro l hl
    refine mem_complexSubmodule.mpr fun y => ?_
    rw [hsum]
    refine ComplexMatrix2.traceless.smul_mem _ (Submodule.sum_mem _ fun x _ => ?_)
    split_ifs with h
    · subst h
      show ComplexMatrix2.fullTrace _ = 0
      rw [fullTrace_conjugateBy (hW' x)]
      exact hl x
    · exact ComplexMatrix2.traceless.zero_mem
  have hin : ∀ l : (pairedFunctions X).complexSubmodule,
      weightedBlockSum B w W l.1 ∈ (pairedFunctions Y).complexSubmodule :=
    fun l => hin₀ l.1 (mem_complexSubmodule.1 l.2)
  let T : (pairedFunctions X).complexSubmodule →ₗ[ℂ] (pairedFunctions Y).complexSubmodule :=
    { toFun := fun l => ⟨weightedBlockSum B w W l.1, hin l⟩
      map_add' := fun l l' => Subtype.ext (hadd _ _)
      map_smul' := fun c l => Subtype.ext (hsmul c _) }
  let co : (Y → ComplexMatrix2) → X → ComplexMatrix2 :=
    fun g x => w • ((W (p x) x)⁻¹ * g (p x) * W (p x) x)
  have hcoin : ∀ g : (pairedFunctions Y).complexSubmodule,
      co g.1 ∈ (pairedFunctions X).complexSubmodule := by
    intro g
    refine mem_complexSubmodule.mpr fun x => ComplexMatrix2.traceless.smul_mem _ ?_
    show ComplexMatrix2.fullTrace _ = 0
    rw [fullTrace_inv_conj (hW' x)]
    exact mem_complexSubmodule.mp g.2 (p x)
  have hcoadd : ∀ g g' : Y → ComplexMatrix2, co (g + g') = co g + co g' := by
    intro g g'
    funext x
    simp only [co, Pi.add_apply, Matrix.mul_add, Matrix.add_mul, smul_add]
  have hcosmul : ∀ (c : ℂ) (g : Y → ComplexMatrix2), co (c • g) = c • co g := by
    intro c g
    funext x
    simp only [co, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
    rw [smul_comm]
  let T' : (pairedFunctions Y).complexSubmodule →ₗ[ℂ] (pairedFunctions X).complexSubmodule :=
    { toFun := fun g => ⟨co g.1, hcoin g⟩
      map_add' := fun g g' => Subtype.ext (hcoadd _ _)
      map_smul' := fun c g => Subtype.ext (hcosmul c _) }
  have hpair : ∀ (g : Y → ComplexMatrix2) (f : X → ComplexMatrix2),
      traceFinsumPairing (co g) f = traceFinsumPairing g (weightedBlockSum B w W f) := by
    intro g f
    simp only [traceFinsumPairing, finsum_eq_sum_of_fintype]
    have hy : ∀ y, ComplexMatrix2.halfTrace (g y * weightedBlockSum B w W f y) =
        ∑ x, if p x = y then ComplexMatrix2.halfTrace (co g x * f x) else 0 := by
      intro y
      rw [hsum, Matrix.mul_smul, Matrix.mul_sum]
      simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul,
        Matrix.trace_sum, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs with h
      · subst h
        have := fullTrace_inv_conj_mul (W (p x) x) (g (p x)) (f x)
        simp only [ComplexMatrix2.fullTrace] at this
        simp only [co, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, this]
      · simp
    simp only [hy]
    rw [Finset.sum_comm]
    simp
  have hprod : ∀ (g : Y → ComplexMatrix2) (y : Y), weightedBlockSum B w W (co g) y = w • g y := by
    intro g y
    rw [hsum]
    have hterm : ∀ x, (if p x = y then ComplexMatrix2.conjugateBy (W y x) (co g x) else 0) =
        if p x = y then w • g y else 0 := by
      intro x
      split_ifs with h
      · subst h
        show ComplexMatrix2.conjugateBy _ (w • _) = _
        rw [conjugateBy_complex_smul, conjugateBy_inv_conj (hW' x)]
      · rfl
    simp only [hterm]
    have hcount : B y = ↑(Finset.univ.filter fun x => p x = y) := by
      ext x
      simp [hmem]
    have hc : ∑ x, (if p x = y then w • g y else 0) =
        ((B y).ncard : ℂ) • (w • g y) := by
      rw [← Finset.sum_filter, Finset.sum_const, hcount, Set.ncard_coe_finset,
        Nat.cast_smul_eq_nsmul]
    rw [hc, smul_smul ((B y).ncard : ℂ) w, hN, one_smul]
  have hrealT : ∀ l : X → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) →
      ∀ y, weightedBlockSum B w W l y ∈ ComplexMatrix2.hermitianTraceless := by
    intro l hl y
    rw [hsum, hw, Complex.coe_smul]
    refine ComplexMatrix2.hermitianTraceless.smul_mem r
      (ComplexMatrix2.hermitianTraceless.sum_mem fun x _ => ?_)
    split_ifs with h
    · subst h
      exact conjugateBy_mem (hWr _ x (hp x)) (hl x)
    · exact ComplexMatrix2.hermitianTraceless.zero_mem
  refine ⟨T, T', fun l => rfl, fun g f => hpair g.1 f.1, fun g => funext fun y => hprod g.1 y,
    fun l hl y => hrealT l.1 hl y, fun g hg x => ?_⟩
  · show co g.1 x ∈ ComplexMatrix2.hermitianTraceless
    have hu : IsUnit (W (p x) x).det := isUnit_iff_ne_zero.mpr (hW' x)
    have e : (W (p x) x)⁻¹ * g.1 (p x) * W (p x) x =
        ComplexMatrix2.conjugateBy (W (p x) x)⁻¹ (g.1 (p x)) := by
      simp only [ComplexMatrix2.conjugateBy]
      rw [Matrix.nonsing_inv_nonsing_inv _ hu]
    simp only [co]
    rw [e, hw, Complex.coe_smul]
    exact ComplexMatrix2.hermitianTraceless.smul_mem r
      (conjugateBy_mem (compact_inv_mem (hWr _ x (hp x))) (hg _))
theorem exists_realRestriction
    {T : (pairedFunctions X).complexSubmodule →ₗ[ℂ] (pairedFunctions Y).complexSubmodule}
    (hr : PreservesReal T) :
    ∃ R : (pairedFunctions X).realSubmodule →ₗ[ℝ] (pairedFunctions Y).realSubmodule,
      ∀ f : (pairedFunctions X).realSubmodule, (R f).1 = (T (toComplex f)).1 := by
  refine ⟨{ toFun := fun f => ⟨(T (toComplex f)).1,
              mem_realFunctions.2 (hr (toComplex f) (toComplex_mem f))⟩
            map_add' := fun f f' => ?_
            map_smul' := fun c f => ?_ }, fun f => rfl⟩
  · refine Subtype.ext ?_
    have e : toComplex (f + f') = toComplex f + toComplex f' := Subtype.ext rfl
    change (T (toComplex (f + f'))).1 = (T (toComplex f)).1 + (T (toComplex f')).1
    rw [e, map_add]
    rfl
  · refine Subtype.ext ?_
    have e : toComplex (c • f) = (c : ℂ) • toComplex f := Subtype.ext (by
      change c • f.1 = (c : ℂ) • f.1
      rw [Complex.coe_smul])
    change (T (toComplex (c • f))).1 = c • (T (toComplex f)).1
    rw [e, map_smul]
    change (c : ℂ) • (T (toComplex f)).1 = _
    rw [Complex.coe_smul]
def hermitianComponent (X : ComplexMatrix2) : ComplexMatrix2 :=
  (1 / 2 : ℂ) • (X + X.conjTranspose)
def skewComponent (X : ComplexMatrix2) : ComplexMatrix2 :=
  (-(Complex.I / 2)) • (X - X.conjTranspose)
theorem fullTrace_conjTranspose_eq_zero {X : ComplexMatrix2} (h : ComplexMatrix2.fullTrace X = 0) :
    ComplexMatrix2.fullTrace X.conjTranspose = 0 := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.fullTrace_conjTranspose_eq_zero <;> assumption
theorem hermitianComponent_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    hermitianComponent X ∈ ComplexMatrix2.hermitianTraceless := by
  have hX : ComplexMatrix2.fullTrace X = 0 := h
  have hX' := fullTrace_conjTranspose_eq_zero hX
  refine ⟨?_, ?_⟩
  · simp only [hermitianComponent, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
    rw [add_comm]
    congr 1
    simp [Complex.ext_iff]
  · simp only [ComplexMatrix2.fullTrace] at hX hX' ⊢
    simp [hermitianComponent, Matrix.trace_smul, Matrix.trace_add, hX, hX']
theorem skewComponent_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    skewComponent X ∈ ComplexMatrix2.hermitianTraceless := by
  have hX : ComplexMatrix2.fullTrace X = 0 := h
  have hX' := fullTrace_conjTranspose_eq_zero hX
  refine ⟨?_, ?_⟩
  · simp only [skewComponent, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by
      simp [Complex.ext_iff]
      norm_num
    rw [this, ← neg_sub X, smul_neg, neg_smul]
  · simp only [ComplexMatrix2.fullTrace] at hX hX' ⊢
    simp [skewComponent, Matrix.trace_smul, Matrix.trace_sub, hX, hX']
theorem eq_hermitianComponent_add_skewComponent (X : ComplexMatrix2) :
    X = hermitianComponent X + Complex.I • skewComponent X := by
  simp only [hermitianComponent, skewComponent, smul_smul]
  have h : Complex.I * -(Complex.I / 2) = 1 / 2 := by
    have := Complex.I_mul_I
    linear_combination (-1 / 2 : ℂ) * this
  rw [h, ← smul_add]
  have : X + X.conjTranspose + (X - X.conjTranspose) = (2 : ℂ) • X := by
    rw [two_smul]; abel
  rw [this, smul_smul]
  norm_num
theorem eq_zero_of_halfTrace_mul {D : ComplexMatrix2} (hD : D ∈ ComplexMatrix2.traceless)
    (h : ∀ Y ∈ ComplexMatrix2.traceless, ComplexMatrix2.halfTrace (D * Y) = 0) : D = 0 := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.eq_zero_of_halfTrace_mul_eq_zero <;> assumption
theorem single_mem_complexSubmodule [DecidableEq X] {x : X} {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.traceless) :
    (Pi.single x Y : X → ComplexMatrix2) ∈ (pairedFunctions X).complexSubmodule := by
  refine mem_complexSubmodule.2 fun z => ?_
  by_cases hz : z = x
  · subst hz
    simpa using hY
  · simp [Pi.single_eq_of_ne hz]
theorem pairing_single [DecidableEq X] (A : X → ComplexMatrix2) (x : X) (Y : ComplexMatrix2) :
    traceFinsumPairing A (Pi.single x Y) = ComplexMatrix2.halfTrace (A x * Y) := by
  unfold traceFinsumPairing
  rw [finsum_eq_single _ x]
  · simp
  · intro z hz
    simp [Pi.single_eq_of_ne hz, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
theorem realTransposeMap_apply
    (T₀ : (pairedFunctions X).realSubmodule →ₗ[ℝ] (pairedFunctions Y).realSubmodule)
    (T : (pairedFunctions X).complexSubmodule →ₗ[ℂ] (pairedFunctions Y).complexSubmodule)
    (T' : (pairedFunctions Y).complexSubmodule →ₗ[ℂ] (pairedFunctions X).complexSubmodule)
    (hval : ∀ f : (pairedFunctions X).realSubmodule, (T₀ f).1 = (T (toComplex f)).1)
    (hp : ∀ g l, traceFinsumPairing (T' g).1 l.1 = traceFinsumPairing g.1 (T l).1)
    (hr : PreservesReal T')
    (g : (pairedFunctions Y).realSubmodule) :
    (PairedFunctionSpace.realTransposeMap T₀ g).1 = (T' (toComplex g)).1 := by
  classical
  have hCont : PairedFunctionSpace.IsComplexification T₀ T := by
    intro f f' h hh
    have e : h = toComplex f + Complex.I • toComplex f' := Subtype.ext hh
    rw [e, map_add, map_smul]
    change (T (toComplex f)).1 + Complex.I • (T (toComplex f')).1 = _
    rw [hval f, hval f']
  have hsplit : ∀ h : (pairedFunctions X).complexSubmodule,
      ∃ f f' : (pairedFunctions X).realSubmodule,
      (h.1 : X → ComplexMatrix2) = f.1 + Complex.I • (f'.1 : X → ComplexMatrix2) := by
    intro h
    refine ⟨⟨fun x => hermitianComponent (h.1 x), mem_realFunctions.2 fun x =>
        hermitianComponent_mem (mem_complexSubmodule.1 h.2 x)⟩,
      ⟨fun x => skewComponent (h.1 x), mem_realFunctions.2 fun x =>
        skewComponent_mem (mem_complexSubmodule.1 h.2 x)⟩, ?_⟩
    funext x
    exact eq_hermitianComponent_add_skewComponent (h.1 x)
  have hc : PairedFunctionSpace.complexification T₀ = T := by
    have hs : PairedFunctionSpace.IsComplexification T₀ (PairedFunctionSpace.complexification T₀) :=
      Classical.epsilon_spec (p := PairedFunctionSpace.IsComplexification T₀) ⟨T, hCont⟩
    refine LinearMap.ext fun h => Subtype.ext ?_
    obtain ⟨f, f', hp'⟩ := hsplit h
    rw [hs f f' h hp', hCont f f' h hp']
  have hTr : PairedFunctionSpace.IsTransposeMap T T' := fun g f _ => hp g f
  have hte : PairedFunctionSpace.transposeMap T = T' := by
    have hs : PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T) :=
      Classical.epsilon_spec (p := PairedFunctionSpace.IsTransposeMap T) ⟨T', hTr⟩
    refine LinearMap.ext fun g => Subtype.ext ?_
    funext x
    have hsub : (PairedFunctionSpace.transposeMap T g).1 x - (T' g).1 x = 0 := by
      refine eq_zero_of_halfTrace_mul (ComplexMatrix2.traceless.sub_mem
        (mem_complexSubmodule.1 (PairedFunctionSpace.transposeMap T g).2 x)
        (mem_complexSubmodule.1 (T' g).2 x)) fun Y hY => ?_
      let f : (pairedFunctions X).complexSubmodule :=
        ⟨(Pi.single (x : X) Y : X → ComplexMatrix2), single_mem_complexSubmodule hY⟩
      have hfs : (pairedFunctions X).IsFinitelySupported f :=
        Set.toFinite (Function.support (Pi.single (x : X) Y : X → ComplexMatrix2))
      let A₁ : X → ComplexMatrix2 := (PairedFunctionSpace.transposeMap T g).1
      let A₂ : X → ComplexMatrix2 := (T' g).1
      have e3 : traceFinsumPairing A₁ (Pi.single (x : X) Y) =
          traceFinsumPairing A₂ (Pi.single (x : X) Y) :=
        (hs g f hfs).trans (hTr g f hfs).symm
      have e4 : ComplexMatrix2.halfTrace (A₁ x * Y) = ComplexMatrix2.halfTrace (A₂ x * Y) :=
        (pairing_single A₁ x Y).symm.trans (e3.trans (pairing_single A₂ x Y))
      show ComplexMatrix2.halfTrace ((A₁ x - A₂ x) * Y) = 0
      rw [sub_mul]
      simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_sub] at e4 ⊢
      linear_combination e4
    exact sub_eq_zero.1 hsub
  obtain ⟨R, hR⟩ := exists_realRestriction hr
  have hRT : PairedFunctionSpace.IsRealTransposeMap T₀ R := by
    intro g h hh
    have e : h = toComplex g := Subtype.ext hh
    rw [hc, hte, e]
    exact hR g
  have hs : PairedFunctionSpace.IsRealTransposeMap T₀ (PairedFunctionSpace.realTransposeMap T₀) :=
    Classical.epsilon_spec (p := PairedFunctionSpace.IsRealTransposeMap T₀) ⟨R, hRT⟩
  rw [hs g (toComplex g) rfl, hc, hte]
end FiniteSets
section LevelAverages
variable {L n k : ℕ} [NeZero L]
theorem hasTransposePair_adjointCubeAverage (hBlk : Tower.BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j < k) {A : Edge L n k j → ComplexMatrix2}
    (hr : ∀ (y : Vertex L n k (j + 1)),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      PeriodicLattice.complexMeanContourHolonomy A y x ∈ PeriodicLattice.compactGaugeGroup) :
    HasTransposePair (adjointCubeAverage A) (PeriodicLattice.inverseFourthPowerWeight L) := by
  have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hblocks := (hBlk L k (j + 1) hL (by omega) (by omega) hj).1 n hn
  have hsort : ∀ x : Vertex L n k j,
      ∃! y : Vertex L n k (j + 1), x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :=
    hblocks.2.1.2.1
  have hcard : ∀ y : Vertex L n k (j + 1),
      (((PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).ncard : ℕ) : ℂ) *
        (((L : ℝ) ^ (-4 : ℤ) : ℝ) : ℂ) = 1 := by
    intro y
    obtain ⟨-, -, hn₄, hsub⟩ := hblocks.1 y
    have himg : Subtype.val '' PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y =
        PeriodicLattice.unitBlock y := by
      ext x
      constructor
      · rintro ⟨x', hx', rfl⟩
        exact hx'
      · intro hx
        exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
    have hnc : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).ncard = L ^ 4 := by
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg]
      exact hn₄
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hLpos.ne'
    rw [hnc]
    have : ((L ^ 4 : ℕ) : ℝ) * (L : ℝ) ^ (-4 : ℤ) = 1 := by
      push_cast
      rw [zpow_neg, mul_inv_eq_one₀ (zpow_ne_zero _ hL0)]
      norm_cast
    exact_mod_cast this
  exact hasTransposePair_weightedBlockSum
    (fun y => PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    ((L : ℝ) ^ (-4 : ℤ)) (fun y x => PeriodicLattice.complexMeanContourHolonomy A y x)
    hsort hcard hr
theorem hasTransposePair_levels
    (f : ∀ j : ℕ, (Vertex L n k j → ComplexMatrix2) → Vertex L n k (j + 1) → ComplexMatrix2)
    (G : ∀ j : ℕ, (Vertex L n k 0 → ComplexMatrix2) → Vertex L n k j → ComplexMatrix2) (c : ℂ)
    (h0 : ∀ l, G 0 l = l) (hS : ∀ j l, G (j + 1) l = f j (G j l))
    (hstep : ∀ j, j < k → HasTransposePair (f j) c) :
    ∀ j, j ≤ k → HasTransposePair (G j) (c ^ j) := by
  intro j
  induction j with
  | zero =>
    intro _
    have e : G 0 = fun l => l := funext h0
    rw [e, pow_zero]
    exact hasTransposePair_id
  | succ j ih =>
    intro hj
    have e : G (j + 1) = fun l => f j (G j l) := funext (hS j)
    rw [e, pow_succ]
    exact (ih (by omega)).comp (hstep j (by omega))
theorem inverseFourthPowerWeight_pow (hL : (L : ℝ) ≠ 0) (k : ℕ) :
    PeriodicLattice.inverseFourthPowerWeight L ^ k = ((((L : ℝ) ^ (4 * k))⁻¹ : ℝ) : ℂ) := by
  unfold PeriodicLattice.inverseFourthPowerWeight
  rw [← Complex.ofReal_pow]
  congr 1
  rw [zpow_neg, inv_pow, pow_mul]
  norm_cast
theorem linearMapWithValues_apply {α β : Type*} {p : Submodule ℝ (α → ComplexMatrix2)}
    {p' : Submodule ℝ (β → ComplexMatrix2)}
    {f : (α → ComplexMatrix2) → β → ComplexMatrix2}
    (h : ∃ T : p →ₗ[ℝ] p', ∀ x : p, (T x : β → ComplexMatrix2) = f x) (x : p) :
    (linearMapWithValues p p' f x : β → ComplexMatrix2) = f x := by apply _root_.YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide.linearMapWithValues_apply <;> assumption
def restrictToTop : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k where
  toFun l := ⟨restrictVertexFunction k (l : Vertex L n k 0 → ComplexMatrix2),
    fun y _ => restrictVertex_mem l k y⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem pairing_extendByZero (g : Vertex L n k k → ComplexMatrix2)
    (l : Vertex L n k 0 → ComplexMatrix2) :
    traceFinsumPairing (_root_.YangMills.Construction.Tower.extendByZero g) l = traceFinsumPairing g (restrictVertexFunction k l) := by
  classical
  haveI : Fintype (Vertex L n k 0) := Fintype.ofFinite _
  haveI : Fintype (Vertex L n k k) := Fintype.ofFinite _
  have hle : PeriodicLattice.levelDepth k k ≤ PeriodicLattice.levelDepth k 0 := by
    simp only [PeriodicLattice.levelDepth]; omega
  let e : Vertex L n k k → Vertex L n k 0 := fun y => y.toSublattice (PeriodicLattice.levelDepth k 0)
  have he : Function.Injective e := by
    intro a b h
    have h1 := congrArg (fun x : Vertex L n k 0 => (x : PeriodicLattice.FourTorus L n)) h
    simp only [e, coe_toSublattice hle] at h1
    exact Subtype.ext h1
  unfold traceFinsumPairing
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  symm
  refine Fintype.sum_of_injective e he _ _ (fun x hx => ?_) (fun y => ?_)
  · have h0 : _root_.YangMills.Construction.Tower.extendByZero g x = 0 := by
      simp only [_root_.YangMills.Construction.Tower.extendByZero]
      refine dif_neg ?_
      rintro ⟨y, hy⟩
      exact hx ⟨y, Subtype.ext ((coe_toSublattice hle y).trans hy)⟩
    rw [h0]
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
  · have h1 : _root_.YangMills.Construction.Tower.extendByZero g (e y) = g y := congrFun (restrictVertex_extendByZero g) y
    rw [h1]
    rfl
def extendAtLevel (j : ℕ) (g : Vertex L n k k → ComplexMatrix2) : Vertex L n k j → ComplexMatrix2 :=
  open Classical in
  fun x => if h : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = x then g h.choose else 0
theorem extendAtLevel_of_eq {j : ℕ} (g : Vertex L n k k → ComplexMatrix2) (z : Vertex L n k k)
    (x : Vertex L n k j)
    (h : (z : PeriodicLattice.FourTorus L n) = x) : extendAtLevel j g x = g z := by
  have hex : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = x := ⟨z, h⟩
  simp only [extendAtLevel, dif_pos hex]
  congr 1
  exact Subtype.ext (hex.choose_spec.trans h.symm)
theorem extendAtLevel_of_not_mem {j : ℕ} (g : Vertex L n k k → ComplexMatrix2) (x : Vertex L n k j)
    (h : ¬∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = x) :
    extendAtLevel j g x = 0 := by
  simp only [extendAtLevel, dif_neg h]
theorem conjugateBy_zero (g : ComplexMatrix2) : ComplexMatrix2.conjugateBy g 0 = 0 := by
  simp [ComplexMatrix2.conjugateBy]
theorem conjugateBy_one (A : ComplexMatrix2) : ComplexMatrix2.conjugateBy 1 A = A := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.conjugateBy_one <;> assumption
theorem adjointCubeAverage_extendAtLevel (hBlk : Tower.BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j < k) (W : Edge L n k j → ComplexMatrix2)
    (hone : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      (x : PeriodicLattice.FourTorus L n) = y →
        PeriodicLattice.complexMeanContourHolonomy W y x = 1)
    (g : Vertex L n k k → ComplexMatrix2) :
    adjointCubeAverage W (extendAtLevel j g) = ((L : ℝ) ^ (-4 : ℤ)) • extendAtLevel (j + 1) g := by
  funext y
  have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hblocks := (hBlk L k (j + 1) hL (by omega) (by omega) hj).1 n hn
  have hc := hblocks.2.1.1 y
  obtain ⟨-, -, -, hsub⟩ := hblocks.1 y
  have hyb : (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
    have h : (y : PeriodicLattice.FourTorus L n) ∈ ({(y : PeriodicLattice.FourTorus L n)} :
        Set (PeriodicLattice.FourTorus L n)) := rfl
    rw [← hc] at h
    exact h.1
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  have hlat : ∀ z : Vertex L n k k, (z : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (j + 1)) := fun z =>
    PeriodicLattice.sublattice_mono hLpos n (by simp only [PeriodicLattice.levelDepth]; omega) z.2
  have hcentre : ∀ (x : Vertex L n k j) (z : Vertex L n k k),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      (z : PeriodicLattice.FourTorus L n) = x → (x : PeriodicLattice.FourTorus L n) = y := by
    intro x z hx hz
    have h : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∩
        (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (j + 1)) :
          Set (PeriodicLattice.FourTorus L n)) := ⟨hx, hz ▸ hlat z⟩
    rw [hc] at h
    exact h
  rw [adjointCubeAverage, inverseFourthPowerWeight_smul]
  change ((L : ℝ) ^ (-4 : ℤ)) • _ = ((L : ℝ) ^ (-4 : ℤ)) • extendAtLevel (j + 1) g y
  congr 1
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  by_cases hy : ∃ z : Vertex L n k k, (z : PeriodicLattice.FourTorus L n) = y
  · obtain ⟨z, hz⟩ := hy
    let x₀ : Vertex L n k j := ⟨y, hsub hyb⟩
    have hx₀ : x₀ ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y := hyb
    rw [Finset.sum_eq_single_of_mem x₀ ((hfin.mem_toFinset).2 hx₀) (fun x hx hne => ?_),
      hone y x₀ rfl, conjugateBy_one, extendAtLevel_of_eq g z x₀ hz, extendAtLevel_of_eq g z y hz]
    have hx' : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :=
      hfin.mem_toFinset.1 hx
    have h0 : extendAtLevel j g x = 0 := by
      refine extendAtLevel_of_not_mem g x ?_
      rintro ⟨z', hz'⟩
      exact hne (Subtype.ext (hcentre x z' hx' hz'))
    rw [h0, conjugateBy_zero]
  · rw [extendAtLevel_of_not_mem g y hy]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :=
      hfin.mem_toFinset.1 hx
    have h0 : extendAtLevel j g x = 0 := by
      refine extendAtLevel_of_not_mem g x ?_
      rintro ⟨z', hz'⟩
      exact hy ⟨z', hz'.trans (hcentre x z' hx' hz')⟩
    rw [h0, conjugateBy_zero]
theorem adjointCubeAverage_smul {j : ℕ} (W : Edge L n k j → ComplexMatrix2) (c : ℝ)
    (a : Vertex L n k j → ComplexMatrix2) :
    adjointCubeAverage W (c • a) = c • adjointCubeAverage W a := by
  funext y
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  simp only [adjointCubeAverage, Pi.smul_apply]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp only [conjugateBy_real_smul]
  rw [← Finset.smul_sum, smul_comm]
theorem composedCubeAverage_extendByZero (hBlk : Tower.BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (X : ChainPoint L n k)
    (hone : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      (x : PeriodicLattice.FourTorus L n) = y →
      PeriodicLattice.complexMeanContourHolonomy (levelField X j) y x = 1)
    (g : Vertex L n k k → ComplexMatrix2) :
    ∀ j, j ≤ k → composedCubeAverage X j (_root_.YangMills.Construction.Tower.extendByZero g) =
      (((L : ℝ) ^ (-4 : ℤ)) ^ j) • extendAtLevel j g := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [pow_zero, one_smul]
    rfl
  | succ j ih =>
    intro hj
    have e : composedCubeAverage X (j + 1) (_root_.YangMills.Construction.Tower.extendByZero g) =
        adjointCubeAverage (levelField X j) (composedCubeAverage X j (_root_.YangMills.Construction.Tower.extendByZero g)) := rfl
    rw [e, ih (by omega), adjointCubeAverage_smul,
      adjointCubeAverage_extendAtLevel hBlk hL hn (by omega) _ (hone j (by omega)),
      smul_smul, pow_succ]
end LevelAverages
section Centres
variable {L n k j : ℕ} [NeZero L]
theorem complexMeanContour_centre
    (hMF : ∀ m : ℕ, 1 ≤ m → Averaging.ComplexLogMeanProperties m)
    (hCon : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (W : Edge L n k j → ComplexMatrix2)
    {y : Vertex L n k (j + 1)} {x : Vertex L n k j} [Nonempty (PeriodicLattice.AxisOrdering y x)]
    (hxy : (x : PeriodicLattice.FourTorus L n) = y) :
    PeriodicLattice.complexMeanContourHolonomy W y x = 1 := by
  have hF := (((hCon L hL k 1 (j + 1) (by omega) (by omega) (by omega)).1 n hn).2.2.2.2.2
    (by omega)).1
  have h0 : (0 : Fin 4 → ℤ) ∈ offsetBox L 1 := by
    intro μ
    have : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    simp only [Pi.zero_apply, Int.cast_zero, abs_zero, pow_one]
    linarith
  have hx : (x : PeriodicLattice.FourTorus L n) =
      offsetPoint (meshAt L k j) (y : PeriodicLattice.FourTorus L n) 0 := by
    rw [hxy]
    simp [offsetPoint, PeriodicLattice.pointOnAxis]
  have hpath : ∀ σ : PeriodicLattice.AxisOrdering y x,
      PeriodicLattice.pathHolonomy W (PeriodicLattice.orderedContour y x σ) = 1 := by
    intro σ
    have h := ((hF.contours y 0 h0 x hx).2 _ ⟨σ, rfl⟩).2.2.1
    have e : PeriodicLattice.orderedContour y x σ = [] := by
      simpa using h
    rw [e]
    simp [PeriodicLattice.pathHolonomy]
  set m := Fintype.card (PeriodicLattice.AxisOrdering y x) with hm
  have hm1 : 1 ≤ m := Fintype.card_pos
  let e : Fin m ≃ PeriodicLattice.AxisOrdering y x := (Fintype.equivFin _).symm
  have h1 : PeriodicLattice.complexMeanContourHolonomy W y x =
      PeriodicLattice.complexLogMean (PeriodicLattice.contourHolonomies W y x ∘ e) :=
    (complexLogMean_comp_equiv e _).symm
  have h2 : PeriodicLattice.contourHolonomies W y x ∘ e = fun _ : Fin m => (1 : ComplexMatrix2) := by
    funext i
    exact hpath _
  rw [h1, h2]
  exact (hMF m hm1).constantFamily 1
    (by simp [PeriodicLattice.complexGaugeGroup, ComplexMatrix2.unitDeterminant])
end Centres
section GaugeCopies
variable {L n k : ℕ} [NeZero L]
theorem smoothingIter_eq (hO : Tower.IteratedMeans.TorusConditions L n k)
    {U : Edge L n k 0 → ComplexMatrix2}
    (hF : ∀ i ≤ k, smoothingIter L n k i U ∈ fieldSpace L n k i ∧
      (∀ e, ComplexMatrix2.operatorNorm (smoothingIter L n k i U e - 1) < polydiscRadius L) ∧
      ∀ c, Tower.LevelwiseMeans.levelwiseMean U i c = some (smoothingIter L n k i U c)) :
    ∀ i ≤ k, smoothingIter L n k i U = PeriodicLattice.complexBlockFieldAtLevel i U := by
  have hreal : ∀ i {V : Edge L n k i → ComplexMatrix2}, V ∈ fieldSpace L n k i →
      V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup := fun i V hV => by
    have hV' : PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup Set.univ V := hV
    exact ⟨fun e he => (Matrix.mem_specialUnitaryGroup_iff.mp (hV'.1 e he)).2, hV'.2⟩
  intro i
  induction i with
  | zero =>
    intro _
    funext c
    have h := (hF 0 (Nat.zero_le _)).2.2 c
    simp only [Tower.LevelwiseMeans.levelwiseMean] at h
    exact (Option.some.inj h).symm
  | succ i ih =>
    intro hi
    have hi' : i < k := hi
    have hw : smoothingIter L n k i U ∈ Tower.MeanStableFields.fieldsNearOne L n k i :=
      ⟨hreal i (hF i hi'.le).1, (hF i hi'.le).2.1⟩
    have hval : ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
        smoothingIter L n k (i + 1) U c =
          PeriodicLattice.complexBlockAverage (smoothingIter L n k i U) c := by
      intro c hc
      have h₁ := (hF (i + 1) hi).2.2 c
      have h₂ := (hF i hi'.le).2.2
      have hfv : Tower.LevelwiseMeans.valuesOrOne (Tower.LevelwiseMeans.levelwiseMean U i) =
          smoothingIter L n k i U := by
        funext e
        simp [Tower.LevelwiseMeans.valuesOrOne, h₂ e]
      have h₃ : Tower.LevelwiseMeans.meanOfDefined (Tower.LevelwiseMeans.levelwiseMean U i) c =
          some (smoothingIter L n k (i + 1) U c) := by
        rw [← h₁]
        simp only [Tower.LevelwiseMeans.levelwiseMean, if_pos hc]
      simp only [Tower.LevelwiseMeans.meanOfDefined] at h₃
      split_ifs at h₃ with h
      rw [hfv] at h₃
      exact (Option.some.inj h₃).symm
    have h := (hO.meanStep_unique i hi' _ hw _ (hreal (i + 1) (hF (i + 1) hi).1)).mp hval
    rw [h, ih hi'.le]
    rfl
theorem complexBlockAverage_gaugeTransform {j : ℕ}
    (hρ : IsAdmissiblePolydiscRadius L (polydiscRadius L))
    (hn : 0 < n) (hj : j < k) {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L n k j) {u : Vertex L n k j → ComplexMatrix2}
    (hu : u ∈ gaugeGroupAt L n k j) (hu' : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup) :
    PeriodicLattice.complexBlockAverage (PeriodicLattice.gaugeTransform u V) =
      PeriodicLattice.gaugeTransform (restrictVertexFunction (j + 1) u)
        (PeriodicLattice.complexBlockAverage V) := by
  have hpoly : ∀ c : Edge L n k (j + 1), V ∈ nearIdentityPolydisc (polydiscRadius L) c :=
    fun c => ⟨⟨fun e _ => hV.1.1 e (Set.mem_univ e), fun e _ => hV.1.2 e (Set.mem_univ e)⟩,
      fun e _ => hV.2 e⟩
  have hpos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      PeriodicLattice.complexBlockAverage (PeriodicLattice.gaugeTransform u V) c =
        PeriodicLattice.gaugeTransform (restrictVertexFunction (j + 1) u)
          (PeriodicLattice.complexBlockAverage V) c :=
    fun c hc => ((hρ.periodic n k j hn hj c hc).gauge_covariant V (hpoly c) u hu).2.1
  funext c
  by_cases hc : c.IsPositivelyOriented
  · exact hpos c hc
  · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hc
    have h := hpos _ hp
    have e1 : ∀ A : Edge L n k j → ComplexMatrix2, PeriodicLattice.complexBlockAverage A c =
        (PeriodicLattice.complexBlockAverage A c.opposite)⁻¹ := by
      intro A
      simp only [PeriodicLattice.complexBlockAverage, if_neg hc, if_pos hp]
    have hr : ∀ y : Vertex L n k (j + 1),
        restrictVertexFunction (j + 1) u y ∈ PeriodicLattice.compactGaugeGroup :=
      fun y => hu' _
    have hinv : ∀ y : Vertex L n k (j + 1), (((restrictVertexFunction (j + 1) u) y)⁻¹)⁻¹ =
        restrictVertexFunction (j + 1) u y := fun y =>
      Matrix.nonsing_inv_nonsing_inv _ (compact_isUnit_det (hr y))
    rw [e1, h]
    simp only [PeriodicLattice.gaugeTransform]
    rw [e1 V, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hinv, mul_assoc]
    rfl
theorem eventually_complexMeanContour_mem
    (hMF : ∀ m : ℕ, 1 ≤ m → Averaging.ComplexLogMeanProperties m)
    (hS : Tower.SmoothingNearIdentity)
    (hH : Tower.LevelwiseMeans.LevelwiseMeansHold)
    (hO : Tower.IteratedMeans.IteratedMeansHold)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n)
    (hne : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      Nonempty (PeriodicLattice.AxisOrdering y x)) :
    EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
      ∀ w : Vertex L n k 0 → ComplexMatrix2, (∀ x, w x ∈ PeriodicLattice.compactGaugeGroup) →
        ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)),
          ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
            PeriodicLattice.complexMeanContourHolonomy
              (PeriodicLattice.complexBlockFieldAtLevel j (PeriodicLattice.gaugeTransform w U)) y x ∈
              PeriodicLattice.compactGaugeGroup := by
  have hH' := (hH L hL k hk).1 n hn
  have hO' := (hO L hL k hk).1 n hn
  have hρ := (hS.1 L hL).2.2
  filter_upwards [hH'.iterates_defined] with U hU w hw
  have e := smoothingIter_eq hO' (fun i hi => ⟨(hU i hi).1, (hU i hi).2.1, (hU i hi).2.2.1⟩)
  have hreal : ∀ i, i ≤ k → PeriodicLattice.complexBlockFieldAtLevel i U ∈ fieldSpace L n k i :=
    fun i hi => e i hi ▸ (hU i hi).1
  have hsmall : ∀ i, i ≤ k → PeriodicLattice.complexBlockFieldAtLevel i U ∈
      smallComplexFields L n k i := fun i hi =>
    ⟨fieldSpace_subset_fieldsIn (hreal i hi), fun e' => by
      have h := (hU i hi).2.1 e'
      rwa [e i hi] at h⟩
  have hwj : ∀ (i : ℕ) (x : Vertex L n k i),
      restrictVertexFunction i w x ∈ PeriodicLattice.compactGaugeGroup :=
    fun i x => hw _
  have hgauge : ∀ i, i ≤ k →
      PeriodicLattice.complexBlockFieldAtLevel i (PeriodicLattice.gaugeTransform w U) =
      PeriodicLattice.gaugeTransform (restrictVertexFunction i w)
        (PeriodicLattice.complexBlockFieldAtLevel i U) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [restrictVertex_zero]
      rfl
    | succ i ih =>
      intro hi
      have hlt : i < k := hi
      have e1 : ∀ A : Edge L n k 0 → ComplexMatrix2,
          PeriodicLattice.complexBlockFieldAtLevel (i + 1) A =
          PeriodicLattice.complexBlockAverage (PeriodicLattice.complexBlockFieldAtLevel i A) :=
        fun A => rfl
      rw [e1, e1, ih hlt.le, _root_.YangMills.Construction.RunningCouplingSlope.ChainMapsAtMinimizersProof.complexBlockAverage_gaugeTransform hρ hn hlt (hsmall i hlt.le)
        (fun x => hwj i x) (hwj i)]
      have e2 : restrictVertexFunction (i + 1) (restrictVertexFunction i w) =
          restrictVertexFunction (i + 1) w :=
        restrictVertex_restrictVertex w hlt.le
      rw [e2]
  intro j hj y x hx
  rw [hgauge j hj.le]
  have hc : (PeriodicLattice.Bond.forwardFrom y 0 : Edge L n k (j + 1)).IsPositivelyOriented :=
    ⟨0, by show y + PeriodicLattice.unitStep L n _ 0 - y = _; abel⟩
  have hV := hsmall j hj.le
  have hpoly : PeriodicLattice.complexBlockFieldAtLevel j U ∈
      nearIdentityPolydisc (polydiscRadius L) (PeriodicLattice.Bond.forwardFrom y 0) :=
    ⟨⟨fun e' _ => hV.1.1 e' (Set.mem_univ e'), fun e' _ => hV.1.2 e' (Set.mem_univ e')⟩,
      fun e' _ => hV.2 e'⟩
  have hserves := hρ.periodic n k j hn hj _ hc
  have hcov := ((hserves.gauge_covariant _ hpoly (restrictVertexFunction j w)
    (fun z => hwj j z)).2.2) y (Or.inl rfl) x hx
  rw [hcov]
  have hdom := hserves.subset_complexDomain hpoly
  have hs : ComplexMatrix2.familyDiameter
      (PeriodicLattice.contourHolonomies (PeriodicLattice.complexBlockFieldAtLevel j U) y x) <
        Averaging.centreOfMassDiameter := hdom.1.2.1 x hx
  haveI := hne j hj y x
  have hr := complexMeanContour_mem_compact hMF (fun e' => (hreal j hj.le).1 e' (Set.mem_univ _)) hs
  exact compact_mul_mem (compact_mul_mem (hwj j _) hr) (compact_inv_mem (hwj j _))
end GaugeCopies
section Connectedness
variable {L n k : ℕ} [NeZero L]
theorem site_eq_sum_unitStep {i : ℤ} (z : PeriodicLattice.Site L n i) :
    ∃ m : Fin 4 → ℤ, z = ∑ μ, m μ • PeriodicLattice.unitStep L n i μ := by
  obtain ⟨m, hm⟩ := z.2
  refine ⟨m, Subtype.ext ?_⟩
  funext μ
  rw [hm μ]
  simp only [AddSubgroup.val_finsetSum, AddSubgroup.coe_zsmul, Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single μ]
  · simp only [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_same]
    rw [← QuotientAddGroup.mk_zsmul, zsmul_eq_mul]
  · intro ν _ hν
    simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hν.symm]
  · intro h
    exact absurd (Finset.mem_univ _) h
theorem forall_of_step_iff {i : ℤ} (P : PeriodicLattice.Site L n i → Prop)
    (hs : ∀ x μ, P x ↔ P (x + PeriodicLattice.unitStep L n i μ)) {x₀ : PeriodicLattice.Site L n i}
    (h0 : P x₀) (x : PeriodicLattice.Site L n i) : P x := by
  have hz : ∀ (μ : Fin 4) (m : ℤ) (a : PeriodicLattice.Site L n i), P a →
      P (a + m • PeriodicLattice.unitStep L n i μ) := by
    intro μ m
    induction m using Int.induction_on with
    | zero => intro a ha; simpa using ha
    | succ m ih =>
      intro a ha
      have h := (hs _ μ).1 (ih a ha)
      have e : a + ((m : ℤ) + 1) • PeriodicLattice.unitStep L n i μ =
          a + (m : ℤ) • PeriodicLattice.unitStep L n i μ + PeriodicLattice.unitStep L n i μ := by
        rw [add_smul, one_smul, add_assoc]
      rw [e]
      exact h
    | pred m ih =>
      intro a ha
      have e : a + (-(m : ℤ)) • PeriodicLattice.unitStep L n i μ =
          a + (-(m : ℤ) - 1) • PeriodicLattice.unitStep L n i μ + PeriodicLattice.unitStep L n i μ := by
        rw [sub_smul, one_smul]
        abel
      have h := ih a ha
      rw [e] at h
      exact (hs _ μ).2 h
  obtain ⟨m, hm⟩ := site_eq_sum_unitStep (x - x₀)
  have e : x = x₀ + ∑ μ, m μ • PeriodicLattice.unitStep L n i μ := by
    rw [← hm]
    abel
  rw [e, Fin.sum_univ_four, ← add_assoc, ← add_assoc, ← add_assoc]
  exact hz _ _ _ (hz _ _ _ (hz _ _ _ (hz _ _ _ h0)))
theorem eq_zero_of_conjugateBy {g A : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (h : ComplexMatrix2.conjugateBy g A = 0) : A = 0 := by
  have hu := compact_isUnit_det hg
  have e : A = g⁻¹ * ComplexMatrix2.conjugateBy g A * g := by
    simp only [ComplexMatrix2.conjugateBy]
    calc A = (g⁻¹ * g) * A * (g⁻¹ * g) := by rw [Matrix.nonsing_inv_mul _ hu]; simp
      _ = _ := by simp only [mul_assoc]
  rw [e, h]
  simp
theorem gaugeOrbitMap_injective {X : ChainPoint L n k} (hX : IsCompactValued X)
    (hO : IsGaugeOrbitMap X (gaugeOrbitMap X)) :
    Function.Injective (gaugeOrbitMap X ∘ₗ (topVanishingGauges L n k).subtype) := by
  refine (injective_iff_map_eq_zero _).2 fun l hl => ?_
  have hval := hO l.1
  have h0 : gaugeOrbitMap X l.1 = 0 := hl
  rw [h0] at hval
  have hD : covDiff X.fine (l.1 : Vertex L n k 0 → ComplexMatrix2) = 0 :=
    (congrArg Prod.fst hval).symm
  have hUr : ∀ e, X.fine e ∈ PeriodicLattice.compactGaugeGroup :=
    fun e => (hX.2 0 (Nat.zero_le _)).1 e (Set.mem_univ _)
  let f : Vertex L n k 0 → ComplexMatrix2 := l.1
  have hstep : ∀ (x : Vertex L n k 0) (μ : Fin 4),
      f x = 0 ↔ f (x + PeriodicLattice.unitStep L n _ μ) = 0 := by
    intro x μ
    have hb : (PeriodicLattice.Bond.forwardFrom x μ : Edge L n k 0).IsPositivelyOriented :=
      ⟨μ, by show x + PeriodicLattice.unitStep L n _ μ - x = _; abel⟩
    have h1 := congrFun hD (PeriodicLattice.Bond.forwardFrom x μ)
    rw [covDiff, extendOddly_of_pos _ hb] at h1
    have h2 : ComplexMatrix2.conjugateBy (X.fine (PeriodicLattice.Bond.forwardFrom x μ))
        (f (x + PeriodicLattice.unitStep L n _ μ)) = f x := sub_eq_zero.1 h1
    constructor
    · intro h
      rw [h] at h2
      exact eq_zero_of_conjugateBy (hUr _) h2
    · intro h
      rw [h, conjugateBy_zero] at h2
      exact h2.symm
  have htop : f ((0 : Vertex L n k k).toSublattice (PeriodicLattice.levelDepth k 0)) = 0 := l.2 0
  have hall : ∀ x, f x = 0 := fun x => forall_of_step_iff (fun x => f x = 0) hstep htop x
  exact Subtype.ext (Subtype.ext (funext hall))
end Connectedness
section LinearMaps
variable {L n k : ℕ} [NeZero L]
theorem zpow_neg_four_pow (hL : (L : ℝ) ≠ 0) (k : ℕ) :
    ((L : ℝ) ^ (-4 : ℤ)) ^ k = ((L : ℝ) ^ (4 * k))⁻¹ := by
  rw [zpow_neg, inv_pow, pow_mul]
  norm_cast
theorem chainLinearMapsAt_of (hRel : ChainRelationsAtCompactPoint)
    (hBlk : Tower.BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hn : 0 < n)
    (hxor : ∀ j, j ≤ k → ∀ e : Edge L n k j,
      Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) (hpl : LevelCurvaturesSmall X)
    (hsoft : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        PeriodicLattice.complexMeanContourHolonomy (levelField X j) y x ∈
          PeriodicLattice.compactGaugeGroup)
    (hone : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      (x : PeriodicLattice.FourTorus L n) = y →
      PeriodicLattice.complexMeanContourHolonomy (levelField X j) y x = 1)
    (htext : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        PeriodicLattice.complexMeanContourHolonomy
          (PeriodicLattice.complexBlockFieldAtLevel j X.fine) y x ∈
          PeriodicLattice.compactGaugeGroup) :
    ChainLinearMapsAt X := by
  obtain ⟨hTop, hOrb, hOth, hDr, hSurj, hLev⟩ := hRel L hL k n hk hn X hX hpl
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hWk : ∀ e, levelField X k e ∈ PeriodicLattice.compactGaugeGroup :=
    fun e => (hX.2 k le_rfl).1 e (Set.mem_univ _)
  have hU : ∀ e, X.fine e ∈ PeriodicLattice.compactGaugeGroup :=
    fun e => (hX.2 0 (Nat.zero_le _)).1 e (Set.mem_univ _)
  have hres : ∀ l : vertexFunctionSpace L n k 0,
      (restrictToTopLinear L n k l : Vertex L n k k → ComplexMatrix2) =
      restrictVertexFunction k (l : Vertex L n k 0 → ComplexMatrix2) :=
    linearMapWithValues_apply ⟨restrictToTop, fun _ => rfl⟩
  have hext : ∀ g : vertexFunctionSpace L n k k,
      (extendFromTopLinear L n k g : Vertex L n k 0 → ComplexMatrix2) =
      _root_.YangMills.Construction.Tower.extendByZero (g : Vertex L n k k → ComplexMatrix2) :=
    linearMapWithValues_apply ⟨extendByZeroLinear, fun _ => rfl⟩
  have htd : ∀ g : vertexFunctionSpace L n k k,
      (topCovDiffLinear (levelField X k) g : Edge L n k k → ComplexMatrix2) =
        covDiff (levelField X k) (g : Vertex L n k k → ComplexMatrix2) :=
    linearMapWithValues_apply ⟨covDiffForm _ hWk (hxor k le_rfl), fun _ => rfl⟩
  have hcd : ∀ l : vertexFunctionSpace L n k 0,
      (covDiffLinear L n k X.fine l : Edge L n k 0 → ComplexMatrix2) =
        covDiff X.fine (l : Vertex L n k 0 → ComplexMatrix2) :=
    linearMapWithValues_apply ⟨covDiffForm _ hU (hxor 0 (Nat.zero_le _)), fun _ => rfl⟩
  obtain ⟨T, T', h1, h2, h3, h4, h5⟩ := hasTransposePair_levels
    (fun j => adjointCubeAverage (levelField X j)) (composedCubeAverage X)
    (PeriodicLattice.inverseFourthPowerWeight L) (fun _ => rfl) (fun _ _ => rfl)
    (fun j hj => hasTransposePair_adjointCubeAverage hBlk hL hn hj (hsoft j hj)) k le_rfl
  obtain ⟨R, hR⟩ := exists_realRestriction h4
  obtain ⟨R', hR'⟩ := exists_realRestriction h5
  have hsa : ∀ l : vertexFunctionSpace L n k 0,
      (composedCubeAverageLinear X l : Vertex L n k k → ComplexMatrix2) =
      composedCubeAverage X k (l : Vertex L n k 0 → ComplexMatrix2) :=
    linearMapWithValues_apply ⟨R, fun l => (hR l).trans (h1 (toComplex l))⟩
  have hsaT : ∀ l : vertexFunctionSpace L n k 0,
      (composedCubeAverageLinear X l : Vertex L n k k → ComplexMatrix2) =
      (T (toComplex l)).1 := fun l => (hsa l).trans (h1 (toComplex l)).symm
  obtain ⟨S, S', g1, g2, g3, g4, g5⟩ := hasTransposePair_levels
    (fun j => adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j X.fine))
    (iterAdjointCubeAverage L n k X.fine) (PeriodicLattice.inverseFourthPowerWeight L)
    (fun _ => rfl) (fun _ _ => rfl)
    (fun j hj => hasTransposePair_adjointCubeAverage hBlk hL hn hj (htext j hj)) k le_rfl
  obtain ⟨Q, hQ⟩ := exists_realRestriction g4
  have hia : ∀ l : vertexFunctionSpace L n k 0,
      (iterAverageLinear L n k X.fine l : Vertex L n k k → ComplexMatrix2) =
        iterAdjointCubeAverage L n k X.fine k (l : Vertex L n k 0 → ComplexMatrix2) :=
    linearMapWithValues_apply ⟨Q, fun l => (hQ l).trans (g1 (toComplex l))⟩
  have hM : ∀ l : vertexFunctionSpace L n k 0,
      (iterAverageLinear L n k X.fine l : Vertex L n k k → ComplexMatrix2) =
      (S (toComplex l)).1 :=
    fun l => (hia l).trans (g1 (toComplex l)).symm
  have htr : ∀ g : vertexFunctionSpace L n k k,
      (iterAverageRealTranspose L n k X.fine g : Vertex L n k 0 → ComplexMatrix2) =
      (S' (toComplex g)).1 :=
    fun g => realTransposeMap_apply (iterAverageLinear L n k X.fine) S S' hM g2 g5 g
  have hwt : ∀ g : Vertex L n k k → ComplexMatrix2,
      PeriodicLattice.inverseFourthPowerWeight L ^ k • g = ((L : ℝ) ^ (4 * k))⁻¹ • g := fun g => by
    rw [inverseFourthPowerWeight_pow hLR, Complex.coe_smul]
  have hext_pair : ∀ (g : vertexFunctionSpace L n k k) (l : vertexFunctionSpace L n k 0),
      traceFinsumPairing (extendFromTopLinear L n k g : Vertex L n k 0 → ComplexMatrix2)
        (l : Vertex L n k 0 → ComplexMatrix2) =
        traceFinsumPairing (g : Vertex L n k k → ComplexMatrix2)
          (restrictToTopLinear L n k l : Vertex L n k k → ComplexMatrix2) := by
    intro g l
    rw [hext g, hres l]
    exact pairing_extendByZero _ _
  have hres_ext : ∀ g, restrictToTopLinear L n k (extendFromTopLinear L n k g) = g := by
    intro g
    refine Subtype.ext ?_
    rw [hres, hext]
    exact restrictVertex_extendByZero _
  have htop_orbit : ∀ l, topDeriv X (gaugeOrbitMap X l) =
      topCovDiffLinear (levelField X k) (restrictToTopLinear L n k l) := by
    intro l
    refine Subtype.ext ((hTop _).trans ((hLev l k le_rfl).1.trans ?_))
    rw [htd, hres]
  have haverage : ∀ l, composedCubeAverageLinear X l =
      restrictToTopLinear L n k l + chainDriftMap X (gaugeOrbitMap X l) := by
    intro l
    refine Subtype.ext ((hsa l).trans ((hLev l k le_rfl).2.trans ?_))
    rw [Submodule.coe_add, hres, hDr]
  have hav_tr : ∃ t : vertexFunctionSpace L n k k →ₗ[ℝ] vertexFunctionSpace L n k 0,
      (∀ (g : vertexFunctionSpace L n k k) (l : vertexFunctionSpace L n k 0),
        traceFinsumPairing (t g : Vertex L n k 0 → ComplexMatrix2)
          (l : Vertex L n k 0 → ComplexMatrix2) =
          traceFinsumPairing (g : Vertex L n k k → ComplexMatrix2)
            (composedCubeAverageLinear X l : Vertex L n k k → ComplexMatrix2)) ∧
      ∀ g, composedCubeAverageLinear X (t g) = ((L : ℝ) ^ (4 * k))⁻¹ • g := by
    refine ⟨R', fun g l => ?_, fun g => ?_⟩
    · rw [hsaT l]
      exact ((congrArg (fun u => traceFinsumPairing u (l : Vertex L n k 0 → ComplexMatrix2))
        (hR' g)).trans (h2 (toComplex g) (toComplex l)))
    · refine Subtype.ext ?_
      have e : toComplex (R' g) = T' (toComplex g) := Subtype.ext (hR' g)
      exact (hsaT _).trans ((congrArg (fun u => (T u).1) e).trans
        ((h3 (toComplex g)).trans (hwt _)))
  have hav_ext : ∀ g, composedCubeAverageLinear X (extendFromTopLinear L n k g) =
      ((L : ℝ) ^ (4 * k))⁻¹ • g := by
    intro g
    refine Subtype.ext ?_
    rw [hsa, hext, composedCubeAverage_extendByZero hBlk hL hn X hone _ k le_rfl,
      zpow_neg_four_pow hLR]
    have e : extendAtLevel k (g : Vertex L n k k → ComplexMatrix2) = g :=
      funext fun y => extendAtLevel_of_eq _ y y rfl
    rw [e]
    rfl
  have hfirst : ∀ l, (gaugeOrbitMap X l).1 = covDiffLinear L n k X.fine l := fun l =>
    Subtype.ext ((congrArg Prod.fst (hOrb l)).trans (hcd l).symm)
  have hgt : ∀ (g : vertexFunctionSpace L n k k) (l : vertexFunctionSpace L n k 0),
      traceFinsumPairing (iterAverageRealTranspose L n k X.fine g : Vertex L n k 0 → ComplexMatrix2)
          (l : Vertex L n k 0 → ComplexMatrix2) =
        traceFinsumPairing (g : Vertex L n k k → ComplexMatrix2)
          (iterAverageLinear L n k X.fine l : Vertex L n k k → ComplexMatrix2) := by
    intro g l
    rw [hM l]
    exact (congrArg (fun u => traceFinsumPairing u (l : Vertex L n k 0 → ComplexMatrix2))
      (htr g)).trans (g2 (toComplex g) (toComplex l))
  have hga : ∀ g, iterAverageLinear L n k X.fine
      (iterAverageRealTranspose L n k X.fine g) = ((L : ℝ) ^ (4 * k))⁻¹ • g := by
    intro g
    refine Subtype.ext ?_
    have e : toComplex (iterAverageRealTranspose L n k X.fine g) = S' (toComplex g) :=
      Subtype.ext (htr g)
    exact (hM _).trans ((congrArg (fun u => (S u).1) e).trans ((g3 (toComplex g)).trans (hwt _)))
  exact
    { topDeriv_spec := hTop
      orbit_spec := hOrb
      shifted_spec := hOth
      drift_spec := hDr
      restrict_apply := hres
      extend_apply := hext
      extend_pairing := hext_pair
      restrict_extend := hres_ext
      topCovDiff_apply := htd
      topDeriv_surjective := hSurj
      topDeriv_orbit := htop_orbit
      mean_eq := haverage
      mean_transpose := hav_tr
      mean_extend := hav_ext
      orbit_fst := hfirst
      iterTranspose_pairing := hgt
      iterAverage_transpose := hga
      orbit_injective := gaugeOrbitMap_injective hX hOrb }
end LinearMaps
section Minimizers
variable {L n k : ℕ} [NeZero L]
theorem norm_inv_sub_one_of_compact {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : ‖g⁻¹ - 1‖ = ‖g - 1‖ := by apply _root_.YangMills.Construction.PeriodicLattice.HolonomyUnderReordering.norm_inv_sub_one_of_mem <;> assumption
theorem top_near_one (hlat : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {W : Edge L n k k → ComplexMatrix2}
    {V : TorusFields.TorusField (2 * L ^ n)} (hW : RepresentsTorusField W V) {δ : ℝ} (hδ : 0 < δ)
    (hV : ∀ (z : TorusFields.TorusSite (2 * L ^ n)) (μ : Fin 4),
      1 - ((V z μ : BlockAverages.UnitQuaternion) : Quaternion ℝ).re < δ ^ 2 / 2) :
    ∀ e, ComplexMatrix2.operatorNorm (W e - 1) < δ := by
  have hWr : ∀ e, W e ∈ PeriodicLattice.compactGaugeGroup := fun e => hW.1.1 e (Set.mem_univ _)
  have hpos : ∀ c : PositiveEdge L n k k, ‖W c.1 - 1‖ < δ := by
    intro c
    obtain ⟨z, μ, hz⟩ := exists_top_forward hlat hL hn c
    have h1 := norm_sub_one_sq (hWr c.1)
    have h2 : traceDefect (W c.1) =
        1 - ((V z μ : BlockAverages.UnitQuaternion) : Quaternion ℝ).re := by
      rw [hz, hW.2 z μ, traceDefect_quaternion]
    have h3 : ‖W c.1 - 1‖ ^ 2 < δ ^ 2 := by
      rw [h1, h2]
      linarith [hV z μ]
    exact lt_of_pow_lt_pow_left₀ 2 hδ.le h3
  intro e
  change ‖W e - 1‖ < δ
  by_cases he : e.IsPositivelyOriented
  · exact hpos ⟨e, he⟩
  · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented he
    have hinv : W e = (W e.opposite)⁻¹ := hW.1.2 e.opposite (Set.mem_univ _)
    rw [hinv, norm_inv_sub_one_of_compact (hWr _)]
    exact hpos ⟨e.opposite, hp⟩
theorem traceDefect_le {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε ≤ 1)
    (h : ComplexMatrix2.operatorNorm (g - 1) < ε) : traceDefect g ≤ ε := by apply _root_.YangMills.DeltaSharedProofs.p501672 <;> assumption
def chainActionBound (a : ℝ) (L n k : ℕ) [NeZero L] : ℝ :=
  (Fintype.card (Face L n k 0) : ℝ) +
    a * ∑ i : Fin k, (Fintype.card (PositiveEdge L n k (i + 1)) : ℝ) * 2
theorem chainActionBound_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ chainActionBound a L n k := by
  unfold chainActionBound
  positivity
theorem chainAction_le {a : ℝ} (ha : 0 < a) {X : ChainPoint L n k} (hX : IsCompactValued X)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1)
    (hp : ∀ p : Face L n k 0,
      ComplexMatrix2.operatorNorm (PeriodicLattice.plaquetteHolonomy X.fine p - 1) < ε)
    (hno : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      ComplexMatrix2.operatorNorm (X.noise i c - 1) < ε)
    (hle : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      ‖meanRadius (levelField X i) c.1 - 1‖ < ε) :
    chainAction a X ≤ ε * chainActionBound a L n k := by
  rw [chainAction_eq, plaquetteAction_eq_sum]
  have hA : ∑ p : Face L n k 0, traceDefect (PeriodicLattice.plaquetteHolonomy X.fine p) ≤
      (Fintype.card (Face L n k 0) : ℝ) * ε := by
    have := Finset.sum_le_card_nsmul Finset.univ
      (fun p : Face L n k 0 => traceDefect (PeriodicLattice.plaquetteHolonomy X.fine p)) ε
      (fun p _ => traceDefect_le (plaquetteHolonomy_mem (hX.2 0 (Nat.zero_le _)) p) h0 h1 (hp p))
    simpa using this
  have hN : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)), noiseCost X i c ≤ 2 * ε := by
    intro i c
    have hr : (meanRadius (levelField X i) c.1).re ≤ 2 := by
      have h := hle i c
      have h2 : ‖meanRadius (levelField X i) c.1‖ ≤ ‖meanRadius (levelField X i) c.1 - 1‖ + 1 := by
        simpa using norm_add_le (meanRadius (levelField X i) c.1 - 1) 1
      linarith [Complex.re_le_norm (meanRadius (levelField X i) c.1)]
    exact mul_le_mul hr (traceDefect_le (hX.1 i c) h0 h1 (hno i c)) (traceDefect_nonneg (hX.1 i c))
      (by norm_num)
  have hT : ∑ i : Fin k, ∑ c : PositiveEdge L n k (i + 1), noiseCost X i c ≤
      ε * ∑ i : Fin k, (Fintype.card (PositiveEdge L n k (i + 1)) : ℝ) * 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := Finset.sum_le_card_nsmul Finset.univ
      (fun c : PositiveEdge L n k (i + 1) => noiseCost X i c) (2 * ε) (fun c _ => hN i c)
    have e : ε * ((Fintype.card (PositiveEdge L n k (i + 1)) : ℝ) * 2) =
        (Fintype.card (PositiveEdge L n k (i + 1)) : ℝ) * (2 * ε) := by ring
    rw [e]
    simpa using this
  have e : ε * chainActionBound a L n k = (Fintype.card (Face L n k 0) : ℝ) * ε +
      a * (ε * ∑ i : Fin k, (Fintype.card (PositiveEdge L n k (i + 1)) : ℝ) * 2) := by
    unfold chainActionBound
    ring
  rw [e]
  have := mul_le_mul_of_nonneg_left hT ha.le
  linarith
theorem exists_ball_of_eventuallyNearIdentity {P : (Edge L n k 0 → ComplexMatrix2) → Prop}
    (h : EventuallyNearIdentity (fieldSpace L n k 0) P) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ U ∈ fieldSpace L n k 0,
      (∀ e, ComplexMatrix2.operatorNorm (U e - 1) < ε) → P U := by
  have h' : {U | P U} ∈ 𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)) := h
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.1 h'
  refine ⟨ε, hε, fun U hU hb => hsub ⟨?_, hU⟩⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro e
  rw [dist_eq_norm]
  exact hb e
theorem gaugeTransform_mem {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0)
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    PeriodicLattice.gaugeTransform v U ∈ fieldSpace L n k 0 := by
  refine ⟨fun e _ => compact_mul_mem (compact_mul_mem (hv _) (hU.1 e (Set.mem_univ _)))
    (compact_inv_mem (hv _)), fun e _ => ?_⟩
  show v e.target * U e.opposite * (v e.source)⁻¹ = (v e.source * U e * (v e.target)⁻¹)⁻¹
  rw [hU.2 e (Set.mem_univ _), Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ (compact_isUnit_det (hv _)), mul_assoc]
theorem gaugeTransform_inv_gaugeTransform {U : Edge L n k 0 → ComplexMatrix2}
    {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    PeriodicLattice.gaugeTransform (fun x => (v x)⁻¹) (PeriodicLattice.gaugeTransform v U) = U := by
  funext e
  show (v e.source)⁻¹ * (v e.source * U e * (v e.target)⁻¹) * ((v e.target)⁻¹)⁻¹ = U e
  rw [Matrix.nonsing_inv_nonsing_inv _ (compact_isUnit_det (hv _))]
  have e1 : (v e.source)⁻¹ * v e.source = 1 := Matrix.nonsing_inv_mul _ (compact_isUnit_det (hv _))
  have e2 : (v e.target)⁻¹ * v e.target = 1 := Matrix.nonsing_inv_mul _ (compact_isUnit_det (hv _))
  calc (v e.source)⁻¹ * (v e.source * U e * (v e.target)⁻¹) * v e.target
      = ((v e.source)⁻¹ * v e.source) * U e * ((v e.target)⁻¹ * v e.target) := by
        simp only [mul_assoc]
    _ = U e := by rw [e1, e2, one_mul, mul_one]
end Minimizers
theorem chainMapsAtMinimizers (hRel : ChainRelationsAtCompactPoint)
    (hFields : MinimizerFieldsNearOne)
    (hPts : SmallActionNearGaugeOrbit)
    (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hA : Averaging.BlockArguments.Holds)
    (hS : Tower.SmoothingNearIdentity)
    (hH : Tower.LevelwiseMeans.LevelwiseMeansHold)
    (hO : Tower.IteratedMeans.IteratedMeansHold)
    (hBlk : Tower.BlockStructure)
    (hCon : Tower.BlockPathContourPivotStatement)
    (hor : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (hlat : PeriodicLattice.CoordinateDescription) :
    ChainMapsAtMinimizers := by
  intro a ha L hL k n hk hn
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  have hxor : ∀ j, j ≤ k → ∀ e : Edge L n k j,
      Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented :=
    xor_isPositive_opposite hor hL hn
  obtain ⟨-, -, -, hMF, hsm⟩ := hM
  let s : Conventions.StandingParameters := ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩
  obtain ⟨hω, hfam⟩ := hsm s
  have hpos : 0 < PeriodicLattice.averagingRadiusCap L := hω.1
  have hne : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      Nonempty (PeriodicLattice.AxisOrdering y x) := by
    intro j hj y x
    exact (hA s j hj (PeriodicLattice.Bond.forwardFrom y 0)).axisOrdering_nonempty y (Or.inl rfl) x
  obtain ⟨ε₂, hε₂, hgood⟩ := exists_ball_of_eventuallyNearIdentity
    (eventually_complexMeanContour_mem (fun m hm => hMF m hm) hS hH hO hL hk hn hne)
  obtain ⟨δ, hδ, hpts⟩ := hPts a ha L hL k n hk hn ε₂ hε₂
  have hB0 : 0 ≤ chainActionBound a L n k := chainActionBound_nonneg ha
  set ε₀ : ℝ := min (min 1 (PeriodicLattice.averagingRadiusCap L))
    (δ / (2 * (chainActionBound a L n k + 1))) with hε₀def
  have hB1 : 0 < chainActionBound a L n k + 1 := by linarith
  have hε₀ : 0 < ε₀ := lt_min (lt_min one_pos hpos) (by positivity)
  have hε₀1 : ε₀ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hε₀ω : ε₀ ≤ PeriodicLattice.averagingRadiusCap L := (min_le_left _ _).trans (min_le_right _ _)
  have hε₀δ : ε₀ * chainActionBound a L n k < δ := by
    have h1 : ε₀ ≤ δ / (2 * (chainActionBound a L n k + 1)) := min_le_right _ _
    have h2 : ε₀ * (2 * (chainActionBound a L n k + 1)) ≤ δ := by
      rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith
  haveI : NeZero (2 * L ^ n) := ⟨by
    have := hL.2
    positivity⟩
  have hη : 0 < δ ^ 2 / 2 := by positivity
  have hev : ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
      ∀ (z : TorusFields.TorusSite (2 * L ^ n)) (μ : Fin 4),
      1 - ((V z μ : BlockAverages.UnitQuaternion) : Quaternion ℝ).re < δ ^ 2 / 2 := by
    refine eventually_all.2 fun z => eventually_all.2 fun μ => ?_
    have hc : Continuous fun V : TorusFields.TorusField (2 * L ^ n) =>
        1 - ((V z μ : BlockAverages.UnitQuaternion) : Quaternion ℝ).re :=
      continuous_const.sub (Quaternion.continuous_re.comp (continuous_subtype_val.comp
        ((continuous_apply μ).comp (continuous_apply z))))
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    have h1 : ((TorusFields.trivialField (2 * L ^ n) z μ : BlockAverages.UnitQuaternion) :
        Quaternion ℝ) = 1 :=
      rfl
    have h2 : (1 : Quaternion ℝ).re = 1 := rfl
    simp only [h1, h2, sub_self]
    exact hη
  filter_upwards [hFields a ha L hL k n hk hn ε₀ hε₀, hev] with V hV hV2 W hW X hLeast
  obtain ⟨hplaq, hno, hle⟩ := hV W hW X hLeast
  have hX : IsCompactValued X := hLeast.compact
  have hpl : LevelCurvaturesSmall X := fun j hj p =>
    (hplaq j hj.le p).trans_le hε₀ω
  have htop : ∀ e, ComplexMatrix2.operatorNorm (levelField X k e - 1) < δ := by
    rw [hLeast.top_eq]
    exact top_near_one hlat hL hn hW hδ hV2
  have hact : chainAction a X < δ :=
    (chainAction_le ha hX hε₀ hε₀1 (fun p => hplaq 0 (Nat.zero_le _) p) hno hle).trans_lt hε₀δ
  obtain ⟨v, hv, -, hb, -⟩ := hpts X hX htop hact
  have hU₀ : PeriodicLattice.gaugeTransform v X.fine ∈ fieldSpace L n k 0 :=
    _root_.YangMills.Construction.RunningCouplingSlope.ChainMapsAtMinimizersProof.gaugeTransform_mem (hX.2 0 (Nat.zero_le _)) hv
  have hgd := hgood _ hU₀ hb (fun x => (v x)⁻¹) (fun x => compact_inv_mem (hv x))
  rw [_root_.YangMills.Construction.RunningCouplingSlope.ChainMapsAtMinimizersProof.gaugeTransform_inv_gaugeTransform hv] at hgd
  have hs : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies (levelField X j) y x) <
        Averaging.centreOfMassDiameter := by
    intro j hj y x hx
    refine hfam (PeriodicLattice.averagingRadiusCap L) ⟨hpos, le_refl _⟩ j hj
      (PeriodicLattice.Bond.forwardFrom y 0) (levelField X j)
      ⟨hX.2 j hj.le, fun p _ => hpl j hj p⟩ y (Or.inl rfl) x hx
  refine chainLinearMapsAt_of hRel hBlk hL hk hn hxor hX hpl (fun j hj y x hx => ?_)
    (fun j hj y x hxy => ?_) hgd
  · haveI := hne j hj y x
    exact complexMeanContour_mem_compact (fun m hm => hMF m hm)
      (fun e => (hX.2 j hj.le).1 e (Set.mem_univ _)) (hs j hj y x hx)
  · haveI := hne j hj y x
    exact complexMeanContour_centre (fun m hm => hMF m hm) hCon hL hn hj _ hxy
end YangMills.Construction.RunningCouplingSlope.ChainMapsAtMinimizersProof
end
