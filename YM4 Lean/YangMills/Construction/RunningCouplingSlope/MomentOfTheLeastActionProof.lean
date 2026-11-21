import YangMills.Construction.ClusterExpansionOfAStep.SharesAreACurvatureFamilyProof
import YangMills.Construction.ColdChainAtEveryLevel.KernelsOnCellsProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdChainAtEveryLevel.PotentialsInAPatch
import YangMills.Construction.PeriodicOperators.NormOfTheSymbolProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheSharesAtDrawnParametersProof
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParametersProof
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ClusterExpansionOfAStep.TopFamiliesOnToriProof
import YangMills.Construction.RunningCouplingSlope.CoefficientOfTheLeastAction
import YangMills.Construction.RunningCouplingSlope.MomentOfTheLeastAction
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepCosts TopLevelSites SlopeCoefficient Filter
namespace RunningCouplingSlope.MinimalActionMoment
section Box
variable {n : ℕ}
private def offsetBox (r : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(r : ℤ)) r
private def offsetSize (z : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (z i).natAbs
private theorem natAbs_le_offsetSize (z : Fin 4 → ℤ) (i : Fin 4) : (z i).natAbs ≤ offsetSize z := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
private theorem mem_offsetBox {r : ℕ} {z : Fin 4 → ℤ} : z ∈ offsetBox r ↔ offsetSize z ≤ r := by apply _root_.YangMills.Construction.CellKernels.mem_centredBox_iff_supNorm <;> assumption
private theorem card_offsetBox (r : ℕ) : (((offsetBox r).card : ℕ) : ℝ) = (2 * (r : ℝ) + 1) ^ 4 := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolNorm.card_intCube <;> assumption
private theorem valMinAbs_intCast_of_le {r : ℕ} (hn : 2 * r + 1 < n) {u : ℤ} (h : u.natAbs ≤ r) :
    ((u : ZMod n)).valMinAbs = u := by
  have i1 : NeZero n := ⟨by omega⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩ <;> omega
private theorem supDist_zero_left (x : TorusSite n) [NeZero n] :
    _root_.YangMills.Construction.TorusFields.supDist (0 : TorusSite n) x = offsetSize fun i => (x i).valMinAbs := by
  unfold _root_.YangMills.Construction.TorusFields.supDist offsetSize
  refine Finset.sup_congr rfl fun i _ => ?_
  simp [ZMod.natAbs_valMinAbs_neg]
private theorem supDist_zero_siteOfInt {r : ℕ} (hn : 2 * r + 1 < n) {u : Fin 4 → ℤ} (h : offsetSize u ≤ r) :
    _root_.YangMills.Construction.TorusFields.supDist (0 : TorusSite n) (siteOfInt u) = offsetSize u := by
  have i1 : NeZero n := ⟨by omega⟩
  rw [supDist_zero_left]
  congr 1
  funext i
  exact valMinAbs_intCast_of_le hn ((natAbs_le_offsetSize u i).trans h)
private theorem siteOfInt_add_eq (u v : Fin 4 → ℤ) :
    (siteOfInt (u + v) : TorusSite n) = siteOfInt u + siteOfInt v := by apply _root_.YangMills.Construction.BlockOffsets.siteOfInt_add <;> assumption
private theorem siteOfInt_zero_eq : (siteOfInt 0 : TorusSite n) = 0 := by
  funext i
  simp [siteOfInt]
private theorem sum_near_origin [NeZero n] {r : ℕ} (hn : 2 * r + 1 < n) (f : TorusSite n → ℝ) :
    ∑ x ∈ Finset.univ.filter (fun x : TorusSite n => _root_.YangMills.Construction.TorusFields.supDist 0 x ≤ r), f x =
      ∑ u ∈ offsetBox r, f (siteOfInt u) := by
  refine Finset.sum_nbij' (fun x i => (x i).valMinAbs) siteOfInt ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_offsetBox]
    have := (Finset.mem_filter.mp hx).2
    rwa [supDist_zero_left] at this
  · intro u hu
    have hu' := mem_offsetBox.mp hu
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [supDist_zero_siteOfInt hn hu']
    exact hu'
  · intro x _
    funext i
    simp [siteOfInt, ZMod.coe_valMinAbs]
  · intro u hu
    funext i
    exact valMinAbs_intCast_of_le hn ((natAbs_le_offsetSize u i).trans (mem_offsetBox.mp hu))
  · intro x _
    congr 1
    funext i
    simp [siteOfInt, ZMod.coe_valMinAbs]
private theorem sum_split_near_far [NeZero n] {r : ℕ} (hn : 2 * r + 1 < n) (f : TorusSite n → ℝ) :
    ∑ x, f x = ∑ u ∈ offsetBox r, f (siteOfInt u) +
      ∑ x ∈ Finset.univ.filter (fun x : TorusSite n => r < _root_.YangMills.Construction.TorusFields.supDist 0 x), f x := by
  rw [← sum_near_origin hn,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : TorusSite n => _root_.YangMills.Construction.TorusFields.supDist 0 x ≤ r)]
  congr 2
  ext x
  simp
private theorem abs_sum_far_le [NeZero n] {δ M S : ℝ} {r : ℕ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hS : ∑ x : TorusSite n, Real.exp (-(δ / 2 * _root_.YangMills.Construction.TorusFields.supDist 0 x)) ≤ S) {g : TorusSite n → ℝ}
    (hg : ∀ x, |g x| ≤ M * Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist 0 x)) :
    |∑ x ∈ Finset.univ.filter (fun x : TorusSite n => r < _root_.YangMills.Construction.TorusFields.supDist 0 x), g x| ≤
      M * Real.exp (-(δ / 2 * r)) * S := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ x ∈ Finset.univ.filter (fun x : TorusSite n => r < _root_.YangMills.Construction.TorusFields.supDist 0 x), |g x| ≤
      M * Real.exp (-(δ / 2 * r)) * Real.exp (-(δ / 2 * _root_.YangMills.Construction.TorusFields.supDist 0 x)) := by
    intro x hx
    have hr : (r : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist 0 x := by exact_mod_cast (Finset.mem_filter.mp hx).2.le
    refine (hg x).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
    nlinarith
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  have hc : 0 ≤ M * Real.exp (-(δ / 2 * r)) := mul_nonneg hM (Real.exp_pos _).le
  refine mul_le_mul_of_nonneg_left ?_ hc
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ => (Real.exp_pos _).le) hS
private theorem sum_exp_offsetSize_le {δ S : ℝ}
    (hS : ∀ (N : ℕ) [NeZero N], ∑ x : TorusSite N, Real.exp (-(δ / 2 * _root_.YangMills.Construction.TorusFields.supDist 0 x)) ≤ S)
    (A : Finset (Fin 4 → ℤ)) : ∑ z ∈ A, Real.exp (-(δ / 2 * offsetSize z)) ≤ S := by
  classical
  set r := A.sup offsetSize with hr
  have hle : ∀ z ∈ A, offsetSize z ≤ r := fun z hz => Finset.le_sup (f := offsetSize) hz
  have hlt : 2 * r + 1 < 2 * r + 2 := by omega
  have i1 : NeZero (2 * r + 2) := ⟨by omega⟩
  have hinj : Set.InjOn (fun z : Fin 4 → ℤ => (siteOfInt z : TorusSite (2 * r + 2))) A := by
    intro u hu v hv h
    funext i
    have h1 := congrFun h i
    have h2 : ((u i : ℤ) : ZMod (2 * r + 2)) = ((v i : ℤ) : ZMod (2 * r + 2)) := h1
    have h3 := congrArg ZMod.valMinAbs h2
    rwa [valMinAbs_intCast_of_le hlt ((natAbs_le_offsetSize u i).trans (hle u hu)),
      valMinAbs_intCast_of_le hlt ((natAbs_le_offsetSize v i).trans (hle v hv))] at h3
  have e : ∑ z ∈ A, Real.exp (-(δ / 2 * offsetSize z)) =
      ∑ x ∈ A.image (fun z : Fin 4 → ℤ => (siteOfInt z : TorusSite (2 * r + 2))),
        Real.exp (-(δ / 2 * _root_.YangMills.Construction.TorusFields.supDist 0 x)) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [supDist_zero_siteOfInt hlt (hle z hz)]
  rw [e]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun _ _ _ => (Real.exp_pos _).le) (hS _)
end Box
section Top
variable {L t n : ℕ}
private theorem period_torusFrame (i : Fin 4) : (torusFrame L t n).period (torusFrame L t n).top i = n := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.torusFrame_period_top <;> assumption
private abbrev torusCells (L t n : ℕ) [NeZero n] : Finset (torusFrame L t n).Cell :=
  cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n))
private abbrev fieldAtTop (L t : ℕ) {n : ℕ} (V : TorusField n) :
    (torusFrame L t n).GaugeField (torusFrame L t n).top :=
  readAtLevel (torusFrame L t n) (torusFrame L t n).top V
private abbrev cellOfSite (L t : ℕ) {n : ℕ} (y : TorusSite n) : (torusFrame L t n).Cell :=
  torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y
private def bondsAtTop {k : ℕ} (L t : ℕ) (c : Fin k → TorusBond n) :
    Fin k → (torusFrame L t n).Site (torusFrame L t n).top × Fin 4 :=
  fun l => (cellOfSite L t (c l).1, (c l).2)
private theorem fieldAtTop_perturb [NeZero n] {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (V : TorusField n) :
    fieldAtTop L t (perturb c X σ V) = rotatedField (BlockAverages.bondSpread (bondsAtTop L t c) X σ) (fieldAtTop L t V) := by apply _root_.YangMills.DeltaSharedProofs.p501447 <;> assumption
private theorem mixedDeriv_fieldAtTop [NeZero n] (g : (torusFrame L t n).GaugeField (torusFrame L t n).top → ℝ)
    {k : ℕ} (V : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun W => g (fieldAtTop L t W)) V c X =
      mixedBondDerivative g (fieldAtTop L t V) (bondsAtTop L t c) X := by apply _root_.YangMills.DeltaSharedProofs.p501924 <;> assumption
private theorem natAbs_valMinAbs_cast_sub {m : ℕ} [NeZero n] (h : m = n) (u v : ZMod n) :
    (((((u.cast : ℤ) : ZMod m) - ((v.cast : ℤ) : ZMod m))).valMinAbs).natAbs =
      ((u - v).valMinAbs).natAbs := by apply _root_.YangMills.Construction.TopFamilyEvaluations.natAbs_valMinAbs_cast_sub <;> assumption
private theorem cellSupDist_cellOfSite [NeZero n] (y z : TorusSite n) :
    cellSupDist (F := torusFrame L t n) (cellOfSite L t y) (cellOfSite L t z) = supDist y z := by apply _root_.YangMills.Construction.TopFamilyEvaluations.siteSupDist_torusSiteInFrame <;> assumption
private theorem mem_torusCells [NeZero n] (z : (torusFrame L t n).Cell) : z ∈ torusCells L t n := by apply _root_.YangMills.Construction.ShareFamilies.CurvatureFamilyProof.mem_cellsOfSites_univ <;> assumption
private theorem isOrthantRegular_of_forall_mem {F : BlockFrame} (S : Finset F.Cell) (hS : ∀ z, z ∈ S) (m : ℕ) :
    IsOrthantRegular S m := by
  intro z
  exact ⟨fun _ => 1, fun _ => Or.inl rfl, fun q _ _ h _ _ => hS _⟩
private theorem isCold_trivialField {s : ℝ} (hs : 0 < s) : TorusFields.IsCold s (trivialField n) := by apply _root_.YangMills.Construction.AbelianSecondOrder.isCold_trivialField <;> assumption
private theorem isCold_fieldAtTop [NeZero n] {s : ℝ} {V : TorusField n} (hV : TorusFields.IsCold s V) :
    BlockAverages.IsCold (torusCells L t n) (torusFrame L t n).top s (fieldAtTop L t V) := by
  rintro ⟨x, μ, ν⟩ hp
  have hlt : μ < ν := (Finset.mem_filter.mp hp).2.1
  rw [plaquetteDefect_readAtLevel_eq period_torusFrame]
  exact hV _ μ ν hlt
private def cellShare (a : ℝ) (L t : ℕ) {n : ℕ} [NeZero n] (y : TorusSite n) (V : TorusField n) : ℝ :=
  minimalCellShare a (torusCells L t n) (cellOfSite L t y) (fieldAtTop L t V)
private theorem mixedDeriv_cellShare [NeZero n] (a : ℝ) (y : TorusSite n) {k : ℕ} (V : TorusField n)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (cellShare a L t y) V c X =
      mixedBondDerivative (minimalCellShare a (torusCells L t n) (cellOfSite L t y)) (fieldAtTop L t V)
        (bondsAtTop L t c) X :=
  mixedDeriv_fieldAtTop (fun W => minimalCellShare a (torusCells L t n) (cellOfSite L t y) W) V c X
private theorem minimalActionTotal_eq_fun [NeZero n] (a : ℝ) (L t : ℕ) :
    minimalActionTotal a L (t + 1) n =
      fun V => minimalAction a (torusCells L t n) (torusFrame L t n).top (fieldAtTop L t V) := by
  funext V
  unfold minimalActionTotal
  rw [dif_neg (NeZero.ne n)]
  rfl
private theorem minimalActionTotal_eq_sum (h3 : sumCellSharesEqAction) [NeZero n] {a : ℝ} (ha : 0 ≤ a)
    (hL : Odd L) (hn : 2 ≤ n) (V : TorusField n) :
    minimalActionTotal a L (t + 1) n V = ∑ y, cellShare a L t y V := by
  have hs : ∀ i, 2 ≤ (torusFrame L t n).extent i := fun _ => hn
  have hw : torusCells L t n = finiteCells (torusFrame L t n) := by
    ext z
    exact ⟨fun _ => _root_.YangMills.Construction.TopLevelSites.mem_finiteCells (fun i => by have := hs i; omega) z, fun _ => mem_torusCells z⟩
  have h5 := (h3 (torusFrame L t n) a (fun _ _ => 0) (fieldAtTop L t V) ha hL hs).1
  rw [minimalActionTotal_eq_fun]
  show minimalAction a (torusCells L t n) (torusFrame L t n).top (fieldAtTop L t V) = _
  rw [hw, ← h5]
  symm
  refine Finset.sum_bij (fun z _ => cellOfSite L t z)
    (fun z _ => _root_.YangMills.Construction.TopLevelSites.mem_finiteCells (fun i => by have := hs i; omega) _) ?_ ?_ ?_
  · intro z _ z' _ h
    have := congrArg (toTorusSite n) h
    rwa [toTorusSite_torusSiteInFrame period_torusFrame, toTorusSite_torusSiteInFrame period_torusFrame] at this
  · intro w _
    exact ⟨toTorusSite n w, Finset.mem_univ _, torusSiteInFrame_toTorusSite period_torusFrame w⟩
  · intro z _
    unfold cellShare
    rw [hw]
end Top
section Chain
private theorem neg_mul_le_neg_mul {δ u v : ℝ} (hδ : 0 < δ) (h : u ≤ v) : -δ * v ≤ -δ * u := by
  nlinarith
private theorem areUnitVectors_pair {X X' : imaginaryQuaternions} (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) :
    AreUnitVectors ![X, X'] := by apply _root_.YangMills.SharedProofs.p1051 <;> assumption
private theorem coldChain_trivialField (T : ParameterAssignment) (hD : T.Admissible) (t : ℕ) {n : ℕ} [NeZero n]
    (hn : 64 ≤ n) :
    HasRegularCellShares T.coupling T.δ₁ T.σA T.N (torusCells T.side t n) (fieldAtTop T.side t (trivialField n)) ∧
    ∀ (n' : ℕ) [NeZero n'], 64 ≤ n' → ∀ (y : TorusSite n) (y' : TorusSite n') (m : ℕ),
      2 * m + 2 < n → 2 * m + 2 < n' →
      HasComparableCellShares T.coupling T.δ₁ T.σA T.N (torusCells T.side t n)
        (fieldAtTop T.side t (trivialField n)) (torusCells T.side t n')
        (fieldAtTop T.side t (trivialField n')) (cellOfSite T.side t y) (cellOfSite T.side t y') m := by
  obtain ⟨-, -, -, -, -, hσA, -, -, hch⟩ := hD.chain
  have hamb : ∀ N : ℕ, 64 ≤ N → IsAdmissibleAmbient (torusFrame T.side t N) := fun N hN => Or.inr fun _ => hN
  obtain ⟨-, -, hAS, -, -, hloc⟩ := hch (torusFrame T.side t n) 1024 (torusCells T.side t n) rfl (hamb n hn)
    le_rfl (isOrthantRegular_of_forall_mem _ mem_torusCells _) T.σA _ hσA le_rfl
    (isCold_fieldAtTop (isCold_trivialField hσA))
  refine ⟨hAS, fun n' _ hn' y y' m h1 h1' => ?_⟩
  have hag : AgreeOnBall (torusCells T.side t n) (fieldAtTop T.side t (trivialField n)) (torusCells T.side t n')
      (fieldAtTop T.side t (trivialField n')) (cellOfSite T.side t y) (cellOfSite T.side t y') m :=
    ⟨fun _ => Or.inr h1, fun _ => Or.inr h1', fun _ _ => ⟨fun _ => mem_torusCells _, fun _ => mem_torusCells _⟩,
      fun _ _ => rfl⟩
  exact (hloc (torusFrame T.side t n') (torusCells T.side t n') (fieldAtTop T.side t (trivialField n')) _ _ m
    rfl rfl (hamb n' hn') (isOrthantRegular_of_forall_mem _ mem_torusCells _)
    (isCold_fieldAtTop (isCold_trivialField hσA)) hag).1
private theorem N_pos (T : ParameterAssignment) (hD : T.Admissible) (k : ℕ) : 0 < T.N k := by apply _root_.YangMills.Construction.StepFloors.N_pos <;> assumption
private theorem contDiffAt_cellShare (T : ParameterAssignment) (hD : T.Admissible) (t : ℕ) {n : ℕ} [NeZero n]
    (hn : 64 ≤ n) (y : TorusSite n) {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => cellShare T.coupling T.side t y (perturb c X σ (trivialField n))) 0 := by
  have hA := (coldChain_trivialField T hD t hn).1.2.1 (cellOfSite T.side t y) k (bondsAtTop T.side t c) X
  have e : (fun σ : Fin k → ℝ => cellShare T.coupling T.side t y (perturb c X σ (trivialField n))) =
      fun σ => minimalCellShare T.coupling (torusCells T.side t n) (cellOfSite T.side t y)
        (rotatedField (BlockAverages.bondSpread (bondsAtTop T.side t c) X σ) (fieldAtTop T.side t (trivialField n))) := by
    funext σ
    unfold cellShare
    rw [fieldAtTop_perturb]
  rw [e]
  exact hA.contDiffAt
private theorem abs_mixedDeriv_cellShare_le (T : ParameterAssignment) (hD : T.Admissible) (t : ℕ) {n : ℕ} [NeZero n]
    (hn : 64 ≤ n) (y : TorusSite n) (c c' : TorusBond n) {X X' : imaginaryQuaternions} (hX : ‖X‖ = 1)
    (hX' : ‖X'‖ = 1) :
    |mixedDeriv (cellShare T.coupling T.side t y) (trivialField n) ![c, c'] ![X, X']| ≤
      T.N 2 * Real.exp (-T.δ₁ * _root_.YangMills.Construction.TorusFields.supDist y c.1) := by
  obtain ⟨-, -, -, -, -, -, hDec, -⟩ := (coldChain_trivialField T hD t hn).1
  have hb := hDec (cellOfSite T.side t y) 2 (bondsAtTop T.side t ![c, c']) ![X, X'] (by norm_num)
    (areUnitVectors_pair hX hX')
  have hD' : bondListDistance (cellOfSite T.side t y) (bondsAtTop T.side t ![c, c']) =
      Finset.univ.sup fun l => _root_.YangMills.Construction.TorusFields.supDist y ((![c, c'] : Fin 2 → TorusBond n) l).1 := by
    unfold bondListDistance
    congr 1
    funext l
    exact cellSupDist_cellOfSite y _
  rw [hD'] at hb
  rw [mixedDeriv_cellShare]
  refine hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (N_pos T hD 2).le)
  have h1 : _root_.YangMills.Construction.TorusFields.supDist y c.1 ≤ Finset.univ.sup fun l => _root_.YangMills.Construction.TorusFields.supDist y ((![c, c'] : Fin 2 → TorusBond n) l).1 :=
    Finset.le_sup (f := fun l => _root_.YangMills.Construction.TorusFields.supDist y ((![c, c'] : Fin 2 → TorusBond n) l).1) (Finset.mem_univ (0 : Fin 2))
  have h2 : (_root_.YangMills.Construction.TorusFields.supDist y c.1 : ℝ) ≤
      ((Finset.univ.sup fun l => _root_.YangMills.Construction.TorusFields.supDist y ((![c, c'] : Fin 2 → TorusBond n) l).1 : ℕ) : ℝ) := by
    exact_mod_cast h1
  exact neg_mul_le_neg_mul hD.δ₁_pos h2
private theorem abs_mixedDeriv_cellShare_sub_le (T : ParameterAssignment) (hD : T.Admissible) (t : ℕ) {n n' : ℕ}
    [NeZero n] [NeZero n'] (hn : 64 ≤ n) (hn' : 64 ≤ n') (y : TorusSite n) (y' : TorusSite n') (m : ℕ)
    (h1 : 2 * m + 2 < n) (h1' : 2 * m + 2 < n') (b : Fin 2 → (Fin 4 → ℤ) × Fin 4)
    (X : Fin 2 → imaginaryQuaternions) (hb : ∀ l, BondWithinRadius m (b l)) (hX : AreUnitVectors X) :
    |mixedDeriv (cellShare T.coupling T.side t y) (trivialField n) (fun l => bondFrom y (b l)) X -
      mixedDeriv (cellShare T.coupling T.side t y') (trivialField n') (fun l => bondFrom y' (b l)) X| ≤
      T.N 2 * Real.exp (-T.δ₁ * m) := by
  have hl := (coldChain_trivialField T hD t hn).2 n' hn' y y' m h1 h1' 2 b X hb hX
  have eb : ∀ (N : ℕ) [NeZero N] (v : TorusSite N),
      (bondsAtTop T.side t fun l => bondFrom v (b l)) = offsetBonds (cellOfSite T.side t v) b := by
    intro N _ v
    funext l
    refine Prod.ext ?_ rfl
    show torusSiteInFrame (torusFrame T.side t N) (torusFrame T.side t N).top (v + siteOfInt (b l).1) =
      _ + siteOfCoords _ (b l).1
    rw [torusSiteInFrame_add period_torusFrame, torusSiteInFrame_siteOfInt period_torusFrame]
  rw [mixedDeriv_cellShare, mixedDeriv_cellShare, eb n y, eb n' y']
  have e : derivativeScale T.σA 2 = 1 := by
    unfold derivativeScale
    norm_num
  rw [e, one_mul] at hl
  exact hl
private theorem abs_hessian_minimalAction_le (T : ParameterAssignment) (hD : T.Admissible) (t : ℕ) {n : ℕ} [NeZero n]
    (hn : 64 ≤ n) (c c' : TorusBond n) {X X' : imaginaryQuaternions} (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) :
    |hessianAtTrivial (minimalActionTotal T.coupling T.side (t + 1)) n c c' X X'| ≤
      T.N 2 * Real.exp (-T.δ₁ * _root_.YangMills.Construction.TorusFields.supDist c.1 c'.1) := by
  obtain ⟨-, -, -, -, -, hAct, -⟩ := (coldChain_trivialField T hD t hn).1
  have hb := hAct 2 (bondsAtTop T.side t ![c, c']) ![X, X'] le_rfl (areUnitVectors_pair hX hX')
  unfold SlopeCoefficient.hessianAtTrivial
  rw [minimalActionTotal_eq_fun]
  have e := mixedDeriv_fieldAtTop (L := T.side) (t := t)
    (fun W => minimalAction T.coupling (torusCells T.side t n) (torusFrame T.side t n).top W)
    (trivialField n) ![c, c'] ![X, X']
  rw [e]
  refine hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (N_pos T hD 2).le)
  set b := bondsAtTop T.side t ![c, c'] with hbdef
  have h1 : cellSupDist (cellOfSite T.side t c.1) (cellOfSite T.side t c'.1) ≤ _root_.YangMills.Construction.BlockAverages.bondListDiameter b :=
    (Finset.le_sup (f := fun l' : Fin 2 => cellSupDist (b 0).1 (b l').1) (Finset.mem_univ (1 : Fin 2))).trans
      (Finset.le_sup (f := fun l : Fin 2 => Finset.univ.sup fun l' : Fin 2 => cellSupDist (b l).1 (b l').1)
        (Finset.mem_univ (0 : Fin 2)))
  rw [cellSupDist_cellOfSite] at h1
  have h2 : (_root_.YangMills.Construction.TorusFields.supDist c.1 c'.1 : ℝ) ≤ _root_.YangMills.Construction.BlockAverages.bondListDiameter b := by exact_mod_cast h1
  exact neg_mul_le_neg_mul hD.δ₁_pos h2
private theorem iteratedFDeriv_finset_sum_apply {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (f : ι → E → ℝ) (x : E) (hf : ∀ i, ContDiffAt ℝ 2 (f i) x) (v : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (fun y => ∑ i ∈ s, f i y) x v = ∑ i ∈ s, iteratedFDeriv ℝ 2 (f i) x v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : (fun _ : E => (0 : ℝ)) = fun _ => 0 := rfl
    rw [iteratedFDeriv_const_of_ne (by norm_num)]
    rfl
  | insert i s hi ih =>
    have e : (fun y => ∑ j ∈ insert i s, f j y) = f i + fun y => ∑ j ∈ s, f j y := by
      funext y
      simp [Finset.sum_insert hi]
    have hs : ContDiffAt ℝ 2 (fun y => ∑ j ∈ s, f j y) x := ContDiffAt.sum fun j _ => hf j
    rw [e, Finset.sum_insert hi, ← ih, iteratedFDeriv_add_apply (hf i) hs]
    rfl
private theorem hessian_eq_sum_cellShare (h3 : sumCellSharesEqAction) (T : ParameterAssignment) (hD : T.Admissible)
    (t : ℕ) {n : ℕ} [NeZero n] (hn : 64 ≤ n) (c c' : TorusBond n) (X X' : imaginaryQuaternions) :
    hessianAtTrivial (minimalActionTotal T.coupling T.side (t + 1)) n c c' X X' =
      ∑ y, mixedDeriv (cellShare T.coupling T.side t y) (trivialField n) ![c, c'] ![X, X'] := by
  have ha : 0 ≤ T.coupling := by linarith [hD.a_ge]
  unfold SlopeCoefficient.hessianAtTrivial mixedDeriv
  have e : (fun σ : Fin 2 → ℝ =>
      minimalActionTotal T.coupling T.side (t + 1) n (perturb ![c, c'] ![X, X'] σ (trivialField n))) =
      fun σ => ∑ y, cellShare T.coupling T.side t y (perturb ![c, c'] ![X, X'] σ (trivialField n)) := by
    funext σ
    exact minimalActionTotal_eq_sum h3 ha hD.L_odd (by omega) _
  rw [e]
  exact iteratedFDeriv_finset_sum_apply Finset.univ
    (fun y σ => cellShare T.coupling T.side t y (perturb ![c, c'] ![X, X'] σ (trivialField n))) 0
    (fun y => contDiffAt_cellShare T hD t hn y _ _) _
end Chain
section Kernel
private theorem abs_sub_le_three_parts (a b c d : ℝ) : |a + c - (b + d)| ≤ |a - b| + |c| + |d| := by
  have e : a + c - (b + d) = (a - b) + c + -d := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  have := abs_add_le (a - b) c
  linarith
private def kernelAt (a : ℝ) (L t n : ℕ) (X : imaginaryQuaternions) (z : Fin 4 → ℤ) : ℝ :=
  hessianAtTrivial (minimalActionTotal a L (t + 1)) n (bondFrom 0 (0, secondAxis)) (bondFrom 0 (z, secondAxis)) X X
private theorem offsetSize_neg (u : Fin 4 → ℤ) : offsetSize (-u) = offsetSize u := by apply _root_.YangMills.Construction.LatticePaths.supNorm_neg <;> assumption
private theorem offsetSize_sub_le (z u : Fin 4 → ℤ) : offsetSize (z - u) ≤ offsetSize z + offsetSize u := by apply _root_.YangMills.Construction.PatchPotentials.supNorm_sub_le <;> assumption
private theorem bondWithinRadius_of_le {m : ℕ} {v : Fin 4 → ℤ} (hv : offsetSize v + 1 ≤ m) (i : Fin 4) :
    BondWithinRadius m (v, i) := by
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have := natAbs_le_offsetSize v j
    show |v j| ≤ (m : ℤ)
    rw [Int.abs_eq_natAbs]
    omega
  · have := natAbs_le_offsetSize v j
    show |(v + (Pi.single i 1 : Fin 4 → ℤ)) j| ≤ (m : ℤ)
    rw [Int.abs_eq_natAbs, Pi.add_apply]
    by_cases h : j = i
    · subst h
      simp only [Pi.single_eq_same]
      omega
    · simp only [Pi.single_eq_of_ne h]
      omega
private theorem bondFrom_shift {N : ℕ} (u z : Fin 4 → ℤ) :
    (fun l => bondFrom (siteOfInt u : TorusSite N) (![(-u, secondAxis), (z - u, secondAxis)] l)) =
      ![bondFrom 0 (0, secondAxis), bondFrom 0 (z, secondAxis)] := by
  funext l
  fin_cases l
  · show ((siteOfInt u : TorusSite N) + siteOfInt (-u), secondAxis) = (0 + siteOfInt 0, secondAxis)
    rw [← siteOfInt_add_eq]
    simp
  · show ((siteOfInt u : TorusSite N) + siteOfInt (z - u), secondAxis) = (0 + siteOfInt z, secondAxis)
    rw [← siteOfInt_add_eq]
    simp
private theorem abs_kernelAt_sub_le (h3 : sumCellSharesEqAction) (T : ParameterAssignment) (hD : T.Admissible)
    (t : ℕ) {S : ℝ}
    (hS : ∀ (N : ℕ) [NeZero N], ∑ x : TorusSite N, Real.exp (-(T.δ₁ / 2 * supDist 0 x)) ≤ S)
    {n n' : ℕ} [NeZero n] [NeZero n'] (hn : 64 ≤ n) (hnn : n ≤ n') {X : imaginaryQuaternions} (hX : ‖X‖ = 1)
    {z : Fin 4 → ℤ} (hz : offsetSize z ≤ 2 * (n / 16)) :
    |kernelAt T.coupling T.side t n X z - kernelAt T.coupling T.side t n' X z| ≤
      (2 * ((n / 4 : ℕ) : ℝ) + 1) ^ 4 * (T.N 2 * Real.exp (-T.δ₁ * (((n - 3) / 2 : ℕ) : ℝ))) +
        2 * (T.N 2 * Real.exp (-(T.δ₁ / 2 * ((n / 4 : ℕ) : ℝ))) * S) := by
  have hδ := hD.δ₁_pos
  have hN := N_pos T hD 2
  set r := n / 4 with hr
  set m := (n - 3) / 2 with hm
  have hr1 : 2 * r + 1 < n := by omega
  have hr2 : 2 * r + 1 < n' := by omega
  have hm1 : 2 * m + 2 < n := by omega
  have hm2 : 2 * m + 2 < n' := by omega
  unfold kernelAt
  rw [hessian_eq_sum_cellShare h3 T hD t hn, hessian_eq_sum_cellShare h3 T hD t (hn.trans hnn),
    sum_split_near_far hr1, sum_split_near_far hr2]
  set D := fun x : TorusSite n => mixedDeriv (cellShare T.coupling T.side t x) (trivialField n)
    ![bondFrom 0 (0, secondAxis), bondFrom 0 (z, secondAxis)] ![X, X] with hDdef
  set D' := fun x : TorusSite n' => mixedDeriv (cellShare T.coupling T.side t x) (trivialField n')
    ![bondFrom 0 (0, secondAxis), bondFrom 0 (z, secondAxis)] ![X, X] with hD'def
  have near : ∀ u ∈ offsetBox r, |D (siteOfInt u) - D' (siteOfInt u)| ≤ T.N 2 * Real.exp (-T.δ₁ * (m : ℝ)) := by
    intro u hu
    have hu' := mem_offsetBox.mp hu
    have hb : ∀ l, BondWithinRadius m
        ((![(-u, secondAxis), (z - u, secondAxis)] : Fin 2 → (Fin 4 → ℤ) × Fin 4) l) := by
      intro l
      fin_cases l
      · refine bondWithinRadius_of_le ?_ _
        show offsetSize (-u) + 1 ≤ m
        rw [offsetSize_neg]
        omega
      · refine bondWithinRadius_of_le ?_ _
        show offsetSize (z - u) + 1 ≤ m
        have := offsetSize_sub_le z u
        omega
    have h := abs_mixedDeriv_cellShare_sub_le T hD t hn (hn.trans hnn) (siteOfInt u) (siteOfInt u) m hm1 hm2 _
      ![X, X] hb (areUnitVectors_pair hX hX)
    rwa [bondFrom_shift, bondFrom_shift] at h
  have b0 : ∀ (N : ℕ), (bondFrom (0 : TorusSite N) (0, secondAxis)).1 = 0 := by
    intro N
    show (0 : TorusSite N) + siteOfInt 0 = 0
    rw [siteOfInt_zero_eq, add_zero]
  have far1 := abs_sum_far_le (r := r) hδ hN.le (hS n) (g := D) fun x => by
    have := abs_mixedDeriv_cellShare_le T hD t hn x (bondFrom 0 (0, secondAxis)) (bondFrom 0 (z, secondAxis)) hX hX
    rwa [b0, supDist_comm] at this
  have far2 := abs_sum_far_le (r := r) hδ hN.le (hS n') (g := D') fun x => by
    have := abs_mixedDeriv_cellShare_le T hD t (hn.trans hnn) x (bondFrom 0 (0, secondAxis))
      (bondFrom 0 (z, secondAxis)) hX hX
    rwa [b0, supDist_comm] at this
  have hsum : |∑ u ∈ offsetBox r, D (siteOfInt u) - ∑ u ∈ offsetBox r, D' (siteOfInt u)| ≤
      (2 * (r : ℝ) + 1) ^ 4 * (T.N 2 * Real.exp (-T.δ₁ * (m : ℝ))) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum near).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul, card_offsetBox]
  have := abs_sub_le_three_parts (∑ u ∈ offsetBox r, D (siteOfInt u)) (∑ u ∈ offsetBox r, D' (siteOfInt u))
    (∑ x ∈ Finset.univ.filter (fun x : TorusSite n => r < _root_.YangMills.Construction.TorusFields.supDist 0 x), D x)
    (∑ x ∈ Finset.univ.filter (fun x : TorusSite n' => r < _root_.YangMills.Construction.TorusFields.supDist 0 x), D' x)
  linarith
end Kernel
section Limit
private theorem abs_intCast_eq_natAbs (u : ℤ) : |(u : ℝ)| = ((u.natAbs : ℕ) : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs]
private theorem inner_self_of_norm_eq_one {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    inner ℝ (X : ℍ[ℝ]) (X : ℍ[ℝ]) = 1 := by
  have h : ‖(X : ℍ[ℝ])‖ = 1 := hX
  rw [real_inner_self_eq_norm_sq, h]
  norm_num
abbrev _root_.YangMills.SharedProofs.p81345 := @inner_self_of_norm_eq_one
private theorem tendsto_kernelAt {a : ℝ} {L t : ℕ} {K : LatticeBond → LatticeBond → ℝ}
    (hK : IsLocalGaugeTotal atTop (minimalActionTotal a L (t + 1)) K) {X : imaginaryQuaternions} (hX : ‖X‖ = 1)
    (z : Fin 4 → ℤ) :
    Tendsto (fun n' => kernelAt a L t n' X z) atTop (𝓝 (K (0, secondAxis) (z, secondAxis))) := by
  have h := hK.tendsto_kernel (0, secondAxis) (z, secondAxis) X X
  rw [inner_self_of_norm_eq_one hX, one_mul] at h
  exact h
private theorem abs_kernelAt_sub_limit_le (h3 : sumCellSharesEqAction) (T : ParameterAssignment) (hD : T.Admissible)
    (t : ℕ) {S : ℝ}
    (hS : ∀ (N : ℕ) [NeZero N], ∑ x : TorusSite N, Real.exp (-(T.δ₁ / 2 * supDist 0 x)) ≤ S)
    {K : LatticeBond → LatticeBond → ℝ}
    (hK : IsLocalGaugeTotal atTop (minimalActionTotal T.coupling T.side (t + 1)) K)
    {n : ℕ} [NeZero n] (hn : 64 ≤ n) {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {z : Fin 4 → ℤ}
    (hz : offsetSize z ≤ 2 * (n / 16)) :
    |kernelAt T.coupling T.side t n X z - K (0, secondAxis) (z, secondAxis)| ≤
      (2 * ((n / 4 : ℕ) : ℝ) + 1) ^ 4 * (T.N 2 * Real.exp (-T.δ₁ * (((n - 3) / 2 : ℕ) : ℝ))) +
        2 * (T.N 2 * Real.exp (-(T.δ₁ / 2 * ((n / 4 : ℕ) : ℝ))) * S) := by
  have ht := ((tendsto_const_nhds (x := kernelAt T.coupling T.side t n X z)).sub (tendsto_kernelAt hK hX z)).abs
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop n] with n' hn'
  have i1 : NeZero n' := ⟨by omega⟩
  exact abs_kernelAt_sub_le h3 T hD t hS hn hn' hX hz
private theorem abs_limitKernel_le (T : ParameterAssignment) (hD : T.Admissible) (t : ℕ)
    {K : LatticeBond → LatticeBond → ℝ}
    (hK : IsLocalGaugeTotal atTop (minimalActionTotal T.coupling T.side (t + 1)) K)
    {X : imaginaryQuaternions} (hX : ‖X‖ = 1) (z : Fin 4 → ℤ) :
    |K (0, secondAxis) (z, secondAxis)| ≤ T.N 2 * Real.exp (-T.δ₁ * offsetSize z) := by
  have ht := (tendsto_kernelAt hK hX z).abs
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop (2 * offsetSize z + 2 + 64)] with n' hn'
  have i1 : NeZero n' := ⟨by omega⟩
  have h := abs_hessian_minimalAction_le T hD t (n := n') (by omega) (bondFrom 0 (0, secondAxis))
    (bondFrom 0 (z, secondAxis)) hX hX
  have e : _root_.YangMills.Construction.TorusFields.supDist (bondFrom (0 : TorusSite n') (0, secondAxis)).1 (bondFrom (0 : TorusSite n') (z, secondAxis)).1 =
      offsetSize z := by
    show _root_.YangMills.Construction.TorusFields.supDist ((0 : TorusSite n') + siteOfInt 0) ((0 : TorusSite n') + siteOfInt z) = offsetSize z
    rw [siteOfInt_zero_eq, add_zero, zero_add]
    exact supDist_zero_siteOfInt (r := offsetSize z) (by omega) le_rfl
  rw [e] at h
  exact h
private theorem abs_momentSummand_le {δ M : ℝ} {R : ℕ} {κ : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) {z : Fin 4 → ℤ}
    (hκ : |κ| ≤ M * Real.exp (-δ * offsetSize z)) (hR : R < offsetSize z) :
    |-(1 / 2) * κ * ((z 0 : ℤ) : ℝ) ^ 2| ≤
      16 * M / δ ^ 2 * Real.exp (-(δ / 4 * R)) * Real.exp (-(δ / 2 * offsetSize z)) := by
  set m : ℝ := ((offsetSize z : ℕ) : ℝ) with hm
  have hRm : (R : ℝ) ≤ m := by
    rw [hm]
    exact_mod_cast hR.le
  have hz : ((z 0 : ℤ) : ℝ) ^ 2 ≤ m ^ 2 := by
    have h1 : |((z 0 : ℤ) : ℝ)| ≤ m := by
      have := natAbs_le_offsetSize z 0
      rw [hm, abs_intCast_eq_natAbs]
      exact_mod_cast this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have he : m ^ 2 ≤ 32 / δ ^ 2 * Real.exp (δ / 4 * m) := by
    have hx : 0 ≤ δ / 4 * m := by positivity
    have hq := Real.quadratic_le_exp_of_nonneg hx
    have h1 : (δ / 4 * m) ^ 2 / 2 ≤ Real.exp (δ / 4 * m) := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have habs : |-(1 / 2) * κ * ((z 0 : ℤ) : ℝ) ^ 2| = 1 / 2 * |κ| * ((z 0 : ℤ) : ℝ) ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ((z 0 : ℤ) : ℝ))]
    norm_num
  rw [habs]
  calc 1 / 2 * |κ| * ((z 0 : ℤ) : ℝ) ^ 2
      ≤ 1 / 2 * (M * Real.exp (-δ * m)) * (32 / δ ^ 2 * Real.exp (δ / 4 * m)) := by
        gcongr
        exact hz.trans he
    _ = 16 * M / δ ^ 2 * Real.exp (-δ * m + δ / 4 * m) := by
        rw [Real.exp_add]
        ring
    _ ≤ 16 * M / δ ^ 2 * Real.exp (-(δ / 4 * R) + -(δ / 2 * m)) := by
        have hc : 0 ≤ 16 * M / δ ^ 2 := by positivity
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc
        nlinarith
    _ = _ := by
        rw [Real.exp_add]
        ring
private theorem abs_sum_offsetBox_sub_one_le {f : (Fin 4 → ℤ) → ℝ} {W S : ℝ} {δ : ℝ} {R : ℕ}
    (hsum : HasSum f 1) (hW : 0 ≤ W)
    (hb : ∀ z, R < offsetSize z → |f z| ≤ W * Real.exp (-(δ / 2 * offsetSize z)))
    (hS : ∀ A : Finset (Fin 4 → ℤ), ∑ z ∈ A, Real.exp (-(δ / 2 * offsetSize z)) ≤ S) :
    |∑ z ∈ offsetBox R, f z - 1| ≤ W * S := by
  have h0 : Tendsto (fun s : Finset (Fin 4 → ℤ) => ∑ z ∈ s, f z) atTop (𝓝 1) := by
    simpa [HasSum, SummationFilter.unconditional_filter] using hsum
  have ht := (h0.sub (tendsto_const_nhds (x := ∑ z ∈ offsetBox R, f z))).abs
  rw [abs_sub_comm]
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop (offsetBox R)] with s hs
  rw [← Finset.sum_sdiff hs, add_sub_cancel_right]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ z ∈ s \ offsetBox R, |f z| ≤ W * Real.exp (-(δ / 2 * offsetSize z)) := by
    intro z hz
    refine hb z ?_
    have := (Finset.mem_sdiff.mp hz).2
    rw [mem_offsetBox] at this
    omega
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hS _) hW
private theorem gaugeTotalMoment_eq_sum {n : ℕ} [NeZero n] (hn : 64 ≤ n) (a : ℝ) (L t : ℕ)
    (X : imaginaryQuaternions) :
    gaugeTotalMoment (minimalActionTotal a L (t + 1)) n X =
      ∑ z ∈ offsetBox (2 * momentCutoff n), -(1 / 2) * kernelAt a L t n X z * ((z 0 : ℤ) : ℝ) ^ 2 := by
  have hr : 2 * (2 * momentCutoff n) + 1 < n := by
    unfold momentCutoff
    omega
  unfold gaugeTotalMoment kernelSecondMoment
  rw [← Finset.sum_filter, sum_near_origin hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz' := mem_offsetBox.mp hz
  have e1 : firstCoordDiff (0 : TorusSite n) (siteOfInt z) = z 0 := by
    unfold firstCoordDiff
    show (((z 0 : ℤ) : ZMod n) - 0).valMinAbs = z 0
    rw [sub_zero]
    exact valMinAbs_intCast_of_le hr ((natAbs_le_offsetSize z 0).trans hz')
  have e2 : bondFrom (0 : TorusSite n) (0, secondAxis) = (0, secondAxis) := by
    show ((0 : TorusSite n) + siteOfInt 0, secondAxis) = _
    rw [siteOfInt_zero_eq, add_zero]
  have e3 : bondFrom (0 : TorusSite n) (z, secondAxis) = (siteOfInt z, secondAxis) := by
    show ((0 : TorusSite n) + siteOfInt z, secondAxis) = _
    rw [zero_add]
  unfold kernelAt
  rw [e1, e2, e3]
  ring
end Limit
section Numbers
private theorem final_estimate {δ N S R r m x : ℝ} (hδ : 0 < δ) (hN : 0 ≤ N) (hS : 0 ≤ S) (hx : 1 ≤ x)
    (hR1 : x / 16 ≤ R) (hR2 : 2 * R + 1 ≤ x) (hr1 : x / 8 ≤ r) (hr2 : 2 * r + 1 ≤ x) (hm : r ≤ m) :
    1 / 2 * R ^ 2 * (2 * R + 1) ^ 4 * ((2 * r + 1) ^ 4 * (N * Real.exp (-δ * m)) +
        2 * (N * Real.exp (-(δ / 2 * r)) * S)) + 16 * N / δ ^ 2 * Real.exp (-(δ / 4 * R)) * S ≤
      ((320 / δ) ^ 10 * N * (1 + 2 * S) + 16 * N / δ ^ 2 * S) * Real.exp (-(δ / 64 * x)) := by
  have hx0 : 0 < x := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hr0 : 0 ≤ r := by linarith
  set e := Real.exp (-(δ / 16 * x)) with he
  set y := Real.exp (-(δ / 64 * x)) with hy
  have he0 : 0 < e := Real.exp_pos _
  have h1 : Real.exp (-δ * m) ≤ e := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.exp (-(δ / 2 * r)) ≤ e := Real.exp_le_exp.mpr (by nlinarith)
  have h3 : Real.exp (-(δ / 4 * R)) ≤ y := Real.exp_le_exp.mpr (by nlinarith)
  have h4 : x ≤ 320 / δ * Real.exp (δ / 320 * x) := by
    have hq := Real.add_one_le_exp (δ / 320 * x)
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    nlinarith
  have h5 : x ^ 10 ≤ (320 / δ) ^ 10 * Real.exp (δ / 32 * x) := by
    have h := pow_le_pow_left₀ hx0.le h4 10
    rw [mul_pow, ← Real.exp_nat_mul] at h
    have e' : ((10 : ℕ) : ℝ) * (δ / 320 * x) = δ / 32 * x := by
      push_cast
      ring
    rwa [e'] at h
  have h6 : x ^ 10 * e ≤ (320 / δ) ^ 10 * y := by
    have hc : 0 ≤ (320 / δ) ^ 10 := by positivity
    calc x ^ 10 * e ≤ (320 / δ) ^ 10 * Real.exp (δ / 32 * x) * e :=
          mul_le_mul_of_nonneg_right h5 he0.le
      _ = (320 / δ) ^ 10 * Real.exp (δ / 32 * x + -(δ / 16 * x)) := by
          rw [Real.exp_add, he]
          ring
      _ ≤ (320 / δ) ^ 10 * y := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc
          nlinarith
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx
  have hR : R ≤ x := by linarith
  have hA : 1 / 2 * R ^ 2 * (2 * R + 1) ^ 4 ≤ x ^ 6 := by
    have a1 : R ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hR0 hR 2
    have a2 : (2 * R + 1) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by linarith) hR2 4
    calc 1 / 2 * R ^ 2 * (2 * R + 1) ^ 4 ≤ 1 * x ^ 2 * x ^ 4 := by gcongr; norm_num
      _ = x ^ 6 := by ring
  have hB : (2 * r + 1) ^ 4 * (N * Real.exp (-δ * m)) + 2 * (N * Real.exp (-(δ / 2 * r)) * S) ≤
      x ^ 4 * (1 + 2 * S) * (N * e) := by
    have b1 : (2 * r + 1) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by linarith) hr2 4
    have b2 : N * Real.exp (-δ * m) ≤ N * e := mul_le_mul_of_nonneg_left h1 hN
    have b3 : N * Real.exp (-(δ / 2 * r)) ≤ N * e := mul_le_mul_of_nonneg_left h2 hN
    have b5 : (2 * r + 1) ^ 4 * (N * Real.exp (-δ * m)) ≤ x ^ 4 * (N * e) := by
      have : 0 ≤ (2 * r + 1) ^ 4 := by positivity
      have : 0 ≤ N * Real.exp (-δ * m) := by positivity
      gcongr
    have b6 : 2 * (N * Real.exp (-(δ / 2 * r)) * S) ≤ x ^ 4 * (2 * S) * (N * e) := by
      calc 2 * (N * Real.exp (-(δ / 2 * r)) * S) ≤ 2 * (N * e * S) := by gcongr
        _ = 1 * (2 * S) * (N * e) := by ring
        _ ≤ x ^ 4 * (2 * S) * (N * e) := by gcongr
    nlinarith
  have hB0 : 0 ≤ (2 * r + 1) ^ 4 * (N * Real.exp (-δ * m)) + 2 * (N * Real.exp (-(δ / 2 * r)) * S) := by
    positivity
  have hF : 1 / 2 * R ^ 2 * (2 * R + 1) ^ 4 * ((2 * r + 1) ^ 4 * (N * Real.exp (-δ * m)) +
      2 * (N * Real.exp (-(δ / 2 * r)) * S)) ≤ (320 / δ) ^ 10 * N * (1 + 2 * S) * y := by
    calc _ ≤ x ^ 6 * (x ^ 4 * (1 + 2 * S) * (N * e)) := mul_le_mul hA hB hB0 (by positivity)
      _ = (x ^ 10 * e) * (N * (1 + 2 * S)) := by ring
      _ ≤ ((320 / δ) ^ 10 * y) * (N * (1 + 2 * S)) :=
          mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = _ := by ring
  have hG : 16 * N / δ ^ 2 * Real.exp (-(δ / 4 * R)) * S ≤ 16 * N / δ ^ 2 * S * y := by
    have : 0 ≤ 16 * N / δ ^ 2 := by positivity
    calc _ ≤ 16 * N / δ ^ 2 * y * S := by gcongr
      _ = _ := by ring
  calc _ ≤ (320 / δ) ^ 10 * N * (1 + 2 * S) * y + 16 * N / δ ^ 2 * S * y := add_le_add hF hG
    _ = _ := by ring
end Numbers
theorem minimalActionMomentNearOne_holds (h1 : MinimalActionHasUnitCoefficient) (h3 : sumCellSharesEqAction)
    (h4 : ExpDecayTorusSumBounded) : MinimalActionMomentNearOne := by
  choose! Sf hSf using h4
  refine ⟨fun l => |(320 / l.δ₁) ^ 10 * l.N 2 * (1 + 2 * Sf (l.δ₁ / 2)) + 16 * l.N 2 / l.δ₁ ^ 2 * Sf (l.δ₁ / 2)| + 1,
    fun l => if 0 < l.δ₁ then l.δ₁ / 64 else 1, fun l => by positivity, fun l => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · positivity
    · exact one_pos
  intro T hD t n _ X hn hX
  beta_reduce
  have hδ := hD.δ₁_pos
  have hN := N_pos T hD 2
  set δ := T.δ₁ with hδdef
  set S := Sf (δ / 2) with hSdef
  have hSp := hSf (δ / 2) (by positivity)
  have hS0 : 0 ≤ S := hSp.1.le
  have hS : ∀ (N : ℕ) [NeZero N], ∑ x : TorusSite N, Real.exp (-(δ / 2 * _root_.YangMills.Construction.TorusFields.supDist 0 x)) ≤ S :=
    fun N _ => hSp.2 N 0
  obtain ⟨K, hK, hsum⟩ := h1 T hD (t + 1)
  set R := 2 * momentCutoff n with hRdef
  have hRn : R = 2 * (n / 16) := rfl
  have hP : ∀ z ∈ offsetBox R,
      |-(1 / 2) * kernelAt T.coupling T.side t n X z * ((z 0 : ℤ) : ℝ) ^ 2 - secondMomentTerm K z| ≤
      1 / 2 * (R : ℝ) ^ 2 * ((2 * ((n / 4 : ℕ) : ℝ) + 1) ^ 4 *
        (T.N 2 * Real.exp (-δ * (((n - 3) / 2 : ℕ) : ℝ))) +
        2 * (T.N 2 * Real.exp (-(δ / 2 * ((n / 4 : ℕ) : ℝ))) * S)) := by
    intro z hz
    have hz' := mem_offsetBox.mp hz
    have hc := abs_kernelAt_sub_limit_le h3 T hD t hS hK hn hX hz'
    have e : -(1 / 2) * kernelAt T.coupling T.side t n X z * ((z 0 : ℤ) : ℝ) ^ 2 - secondMomentTerm K z =
        -(1 / 2) * (kernelAt T.coupling T.side t n X z - K (0, secondAxis) (z, secondAxis)) *
          ((z 0 : ℤ) : ℝ) ^ 2 := by
      unfold secondMomentTerm
      ring
    have hq : ((z 0 : ℤ) : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by
      have h0 := (natAbs_le_offsetSize z 0).trans hz'
      have h1 : |((z 0 : ℤ) : ℝ)| ≤ (R : ℝ) := by
        rw [abs_intCast_eq_natAbs]
        exact_mod_cast h0
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [e, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ((z 0 : ℤ) : ℝ))]
    have e2 : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
    rw [e2]
    calc _ ≤ 1 / 2 * ((2 * ((n / 4 : ℕ) : ℝ) + 1) ^ 4 * (T.N 2 * Real.exp (-δ * (((n - 3) / 2 : ℕ) : ℝ))) +
        2 * (T.N 2 * Real.exp (-(δ / 2 * ((n / 4 : ℕ) : ℝ))) * S)) * (R : ℝ) ^ 2 := by
          have := abs_nonneg (kernelAt T.coupling T.side t n X z - K (0, secondAxis) (z, secondAxis))
          gcongr
      _ = _ := by ring
  have hA : |∑ z ∈ offsetBox R, (-(1 / 2) * kernelAt T.coupling T.side t n X z * ((z 0 : ℤ) : ℝ) ^ 2) -
      ∑ z ∈ offsetBox R, secondMomentTerm K z| ≤
      1 / 2 * (R : ℝ) ^ 2 * (2 * (R : ℝ) + 1) ^ 4 *
        ((2 * ((n / 4 : ℕ) : ℝ) + 1) ^ 4 * (T.N 2 * Real.exp (-δ * (((n - 3) / 2 : ℕ) : ℝ))) +
          2 * (T.N 2 * Real.exp (-(δ / 2 * ((n / 4 : ℕ) : ℝ))) * S)) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hP).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul, card_offsetBox]
    exact le_of_eq (by ring)
  have hlat : ∀ A : Finset (Fin 4 → ℤ), ∑ z ∈ A, Real.exp (-(δ / 2 * offsetSize z)) ≤ S :=
    fun A => sum_exp_offsetSize_le hS A
  have hW : 0 ≤ 16 * T.N 2 / δ ^ 2 * Real.exp (-(δ / 4 * R)) := by positivity
  have hB : |∑ z ∈ offsetBox R, secondMomentTerm K z - 1| ≤ 16 * T.N 2 / δ ^ 2 * Real.exp (-(δ / 4 * R)) * S := by
    refine abs_sum_offsetBox_sub_one_le hsum hW (fun z hz => ?_) hlat
    exact abs_momentSummand_le hδ hN.le (abs_limitKernel_le T hD t hK hX z) hz
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hf := final_estimate (δ := δ) (N := T.N 2) (S := S) (R := R) (r := ((n / 4 : ℕ) : ℝ))
    (m := (((n - 3) / 2 : ℕ) : ℝ)) (x := n) hδ hN.le hS0 hn1
    (by
      have : n ≤ 16 * R := by omega
      have h' : (n : ℝ) ≤ 16 * (R : ℝ) := by exact_mod_cast this
      linarith)
    (by
      have : 2 * R + 1 ≤ n := by omega
      exact_mod_cast this)
    (by
      have : n ≤ 8 * (n / 4) := by omega
      have h' : (n : ℝ) ≤ 8 * ((n / 4 : ℕ) : ℝ) := by exact_mod_cast this
      linarith)
    (by
      have : 2 * (n / 4) + 1 ≤ n := by omega
      exact_mod_cast this)
    (by
      have : n / 4 ≤ (n - 3) / 2 := by omega
      exact_mod_cast this)
  rw [if_pos hδ, gaugeTotalMoment_eq_sum hn]
  have hfin : |∑ z ∈ offsetBox R, (-(1 / 2) * kernelAt T.coupling T.side t n X z * ((z 0 : ℤ) : ℝ) ^ 2) - 1| ≤
      ((320 / δ) ^ 10 * T.N 2 * (1 + 2 * S) + 16 * T.N 2 / δ ^ 2 * S) * Real.exp (-(δ / 64 * n)) := by
    have := abs_sub_le (∑ z ∈ offsetBox R, (-(1 / 2) * kernelAt T.coupling T.side t n X z * ((z 0 : ℤ) : ℝ) ^ 2))
      (∑ z ∈ offsetBox R, secondMomentTerm K z) 1
    linarith
  refine hfin.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  exact (le_abs_self _).trans (by linarith)
end RunningCouplingSlope.MinimalActionMoment
end YangMills.Construction
end
