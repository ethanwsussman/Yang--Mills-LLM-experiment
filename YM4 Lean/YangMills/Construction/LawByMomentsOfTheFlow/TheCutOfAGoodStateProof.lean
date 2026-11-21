import YangMills.Construction.ColdStepAtMirrorFrames.PlaquetteOfACutFieldProof
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.HoleBesideASecondHole.CellsPutBackProof
import YangMills.Construction.LawByMomentsOfTheFlow.TheCutOfAGoodState
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheScale
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheLocalChainProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MomentLaw
namespace GoodConfigCutoff
section Frames
variable {L n : ℕ} [NeZero n]
private theorem torusSiteInFrame_unitStep (i : Fin 4) :
    StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 (TorusFields.unitStep n i) =
      BlockAverages.unitStep (F := TorusLumps.stepBlockFrame L n) 1 i := by apply _root_.YangMills.SharedProofs.p8913 <;> assumption
private theorem torusSiteInFrame_add (x y : TorusFields.TorusSite n) :
    StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 (x + y) =
      StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 x +
        StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 y := by
  funext i
  exact BlockTrees.intCast_cast_add (BlockTrees.stepBlockFrame_period_one i) (x i) (y i)
private theorem torusSiteInFrame_siteOfInt (e : Fin 4 → ℤ) :
    StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 (TorusFields.siteOfInt e : TorusFields.TorusSite n) =
      BlockAverages.siteOfCoords (F := TorusLumps.stepBlockFrame L n) 1 e := by
  funext k
  exact BlockTrees.intCast_cast_intCast (BlockTrees.stepBlockFrame_period_one k) (e k)
private theorem toTorusSite_torusSiteInFrame (z : TorusFields.TorusSite n) :
    TorusLumps.toTorusSite n (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 z) = z := by
  funext k
  exact BlockTrees.intCast_cast_intCast_cast (BlockTrees.stepBlockFrame_period_one k).symm (z k)
end Frames
section Sites
variable {n : ℕ} [NeZero n]
private theorem mem_supBall_iff {o z : TorusFields.TorusSite n} {r : ℝ} :
    z ∈ ResponseInTheExpansion.supBall o r ↔ (TorusFields.supDist z o : ℝ) ≤ r := by
  simp [ResponseInTheExpansion.supBall]
private theorem unitStep_eq_siteOfInt (i : Fin 4) :
    TorusFields.unitStep n i = TorusFields.siteOfInt (Pi.single i 1) := by apply _root_.YangMills.Construction.TorusLumps.unitStep_eq_siteOfInt <;> assumption
private theorem supDist_add_unitStep_le (z o : TorusFields.TorusSite n) (i : Fin 4) :
    TorusFields.supDist (z + TorusFields.unitStep n i) o ≤ TorusFields.supDist z o + 1 := by apply _root_.YangMills.SharedProofs.p13239 <;> assumption
private theorem supDist_le_add_unitStep (z o : TorusFields.TorusSite n) (i : Fin 4) :
    TorusFields.supDist z o ≤ TorusFields.supDist (z + TorusFields.unitStep n i) o + 1 := by apply _root_.YangMills.SharedProofs.p7518 <;> assumption
private theorem plaquetteInBox_of_corners {o x : TorusFields.TorusSite n} {μ ν : Fin 4} {R : ℕ} {Rr : ℝ}
    (hR : (R : ℝ) ≤ Rr) (h : μ < ν)
    (h0 : TorusFields.supDist x o ≤ R) (h1 : TorusFields.supDist (x + TorusFields.unitStep n μ) o ≤ R)
    (h2 : TorusFields.supDist (x + TorusFields.unitStep n ν) o ≤ R)
    (h3 : TorusFields.supDist (x + TorusFields.unitStep n μ + TorusFields.unitStep n ν) o ≤ R) :
    MomentLaw.PlaquetteInBox o Rr (x, μ, ν) := by
  have key : ∀ z : TorusFields.TorusSite n, TorusFields.supDist z o ≤ R → z ∈ ResponseInTheExpansion.supBall o Rr :=
    fun z hz => mem_supBall_iff.2 (le_trans (by exact_mod_cast hz) hR)
  refine ⟨h, fun z hz => ?_⟩
  simp only [TorusFields.plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact key _ h0
  · exact key _ h1
  · exact key _ h2
  · exact key _ h3
private theorem curvature_le_boxCurvature (o : TorusFields.TorusSite n) (R : ℝ) (W : TorusFields.TorusField n)
    {x : TorusFields.TorusSite n} {μ ν : Fin 4} (h : MomentLaw.PlaquetteInBox o R (x, μ, ν)) :
    TorusFields.curvature W x μ ν ≤ MomentLaw.boxCurvature o R W :=
  le_ciSup (f := fun p : {p : TorusFields.TorusPlaquette n // MomentLaw.PlaquetteInBox o R p} =>
      TorusFields.curvature W p.1.1 p.1.2.1 p.1.2.2)
    (Set.finite_range _).bddAbove ⟨(x, μ, ν), h⟩
private theorem boxCurvature_nonneg (o : TorusFields.TorusSite n) (R : ℝ) (W : TorusFields.TorusField n) :
    0 ≤ MomentLaw.boxCurvature o R W :=
  Real.iSup_nonneg fun _ => norm_nonneg _
end Sites
section Chord
private theorem axialGauge_bond_near_one (hAx : WeightedResponses.axialGaugeNearOneStatement)
    (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n] (V : TorusFields.TorusField n) (o : TorusFields.TorusSite n)
    (r : ℕ) (hr : 2 * r + 2 < n) {c : ℝ} (hc0 : 0 ≤ c)
    (hcold : ∀ (x : TorusFields.TorusSite n) (μ ν : Fin 4), μ < ν → TorusFields.supDist x o ≤ r →
      TorusFields.supDist (x + TorusFields.unitStep n μ) o ≤ r →
      TorusFields.supDist (x + TorusFields.unitStep n ν) o ≤ r →
      TorusFields.supDist (x + TorusFields.unitStep n μ + TorusFields.unitStep n ν) o ≤ r →
      TorusFields.curvature V x μ ν ≤ c)
    (b : TorusFields.TorusBond n) (h1 : TorusFields.supDist b.1 o ≤ r)
    (h2 : TorusFields.supDist (b.1 + TorusFields.unitStep n b.2) o ≤ r) :
    ‖((ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ V o) V b : BlockAverages.UnitQuaternion) :
      ℍ[ℝ]) - 1‖ ≤ 3 * (r : ℝ) * c := by
  obtain ⟨x, i⟩ := b
  obtain ⟨e, he, hbd⟩ := TorusFields.exists_offset_of_supDist o x
  simp only at h1 h2
  have h1' : TorusFields.supDist o x ≤ r := by rwa [TorusFields.supDist_comm]
  have hin : BlockAverages.WithinRadius r e := fun k => by
    have := (hbd k).trans h1'
    rw [abs_le]
    omega
  have hkey : (e i + 1).natAbs ≤ r := by
    have hb := (hbd i).trans h1'
    have hv : (((e i + 1 : ℤ)) : ZMod n).valMinAbs = e i + 1 :=
      (ZMod.valMinAbs_spec _ _).2 ⟨rfl, ⟨by omega, by omega⟩⟩
    have hx : (x + TorusFields.unitStep n i) i - o i = (((e i + 1 : ℤ)) : ZMod n) := by
      rw [he]
      simp [TorusFields.siteOfInt, TorusFields.unitStep]
      ring
    have := (TorusFields.supDist_le_iff _ _ r).1 h2 i
    rwa [hx, hv] at this
  have hbond : BlockAverages.BondWithinRadius r (e, i) := by
    refine ⟨hin, fun k => ?_⟩
    by_cases hk : k = i
    · subst hk
      simp only [Pi.add_apply, Pi.single_eq_same]
      rw [abs_le]
      omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hk, add_zero]
      exact hin k
  have hmain := hAx (TorusLumps.stepBlockFrame ℓ.side n)
    (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 V)
    (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o) c r
    (fun _ => hr) hc0 ?_ (e, i) hbond
  · have hx : StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o +
          BlockAverages.siteOfCoords (F := TorusLumps.stepBlockFrame ℓ.side n) 1 e =
        StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 x := by
      rw [he, torusSiteInFrame_add, torusSiteInFrame_siteOfInt]
    have hval : BlockAverages.gaugeTransform
        (ColdStepAtMirrorFrames.axialGaugeHolonomy
          (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 V)
          (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o))
        (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 V)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o +
          BlockAverages.siteOfCoords (F := TorusLumps.stepBlockFrame ℓ.side n) 1 e) i =
        ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ V o) V (x, i) := by
      rw [hx]
      show _ * TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 V
          (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 x) i *
        (ColdStepAtMirrorFrames.axialGaugeHolonomy
          (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 V)
          (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o)
          (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 x +
            BlockAverages.unitStep (F := TorusLumps.stepBlockFrame ℓ.side n) 1 i))⁻¹ = _
      rw [BlockTrees.readAtLevel_torusSiteInFrame _ 1 BlockTrees.stepBlockFrame_period_one V x i,
        ← torusSiteInFrame_unitStep, ← torusSiteInFrame_add]
      rfl
    rw [← hval]
    exact hmain
  · intro a k l hkl g1 g2 g3 g4
    have hz : StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o +
          BlockAverages.siteOfCoords (F := TorusLumps.stepBlockFrame ℓ.side n) 1 a =
        StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 (o + TorusFields.siteOfInt a) := by
      rw [torusSiteInFrame_add, torusSiteInFrame_siteOfInt]
    show BlockAverages.plaquetteDefect (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 V)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o +
        BlockAverages.siteOfCoords (F := TorusLumps.stepBlockFrame ℓ.side n) 1 a, k, l) ≤ c
    rw [hz, TopLevelSites.plaquetteDefect_readAtLevel_eq BlockTrees.stepBlockFrame_period_one,
      toTorusSite_torusSiteInFrame]
    have hcorner : ∀ q : Fin 4 → ℤ, BlockAverages.WithinRadius r q →
        TorusFields.supDist (o + TorusFields.siteOfInt q) o ≤ r := fun q hq => by
      rw [TorusFields.supDist_comm]
      refine TorusFields.supDist_add_siteOfInt_le o q r fun j => ?_
      have := hq j
      rw [abs_le] at this
      omega
    refine hcold (o + TorusFields.siteOfInt a) k l hkl (hcorner a g1) ?_ ?_ ?_
    · rw [unitStep_eq_siteOfInt, add_assoc, ← TorusFields.siteOfInt_add]
      exact hcorner _ g2
    · rw [unitStep_eq_siteOfInt, add_assoc, ← TorusFields.siteOfInt_add]
      exact hcorner _ g3
    · rw [unitStep_eq_siteOfInt, unitStep_eq_siteOfInt, add_assoc, add_assoc, ← TorusFields.siteOfInt_add,
        ← TorusFields.siteOfInt_add, ← add_assoc]
      exact hcorner _ g4
private theorem norm_minimalLog_le_of_near_one (g : BlockAverages.UnitQuaternion) (h : ‖(g : ℍ[ℝ]) - 1‖ ≤ 1) :
    ‖(LumpContours.minimalLog g : ℍ[ℝ])‖ ≤ 4 / 3 * ‖(g : ℍ[ℝ]) - 1‖ := by
  set θ := ‖(LumpContours.minimalLog g : ℍ[ℝ])‖ with hθ
  have h0 : 0 ≤ θ := norm_nonneg _
  have h2 : θ ≤ 2 := (GaugeFixing.norm_minimalLog_le g).trans (by linarith)
  have hre : (g : ℍ[ℝ]).re = Real.cos θ := by
    have := GaugeFixing.re_coe_expUnit (LumpContours.minimalLog g)
    rw [GaugeFixing.expUnit_minimalLog] at this
    exact this
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h3 := Real.cos_two_mul (θ / 2)
    have h4 := Real.sin_sq_add_cos_sq (θ / 2)
    have : 2 * (θ / 2) = θ := by ring
    rw [this] at h3
    nlinarith
  have hsq := GaugeFixing.norm_coe_sub_one_sq g
  rw [hre, hc] at hsq
  rcases h0.eq_or_lt with h00 | hpos
  · rw [← h00]
    have := norm_nonneg ((g : ℍ[ℝ]) - 1)
    linarith
  have ht : 0 < θ / 2 := by linarith
  have hs := Real.sin_gt_sub_cube ht
  have hs2 : 3 / 8 * θ ≤ Real.sin (θ / 2) := by
    have : (θ / 2) ^ 3 ≤ θ / 2 := by
      have : (θ / 2) ^ 2 ≤ 1 := by nlinarith
      nlinarith
    nlinarith
  have h5 : (3 / 4 * θ) ^ 2 ≤ ‖(g : ℍ[ℝ]) - 1‖ ^ 2 := by
    nlinarith [mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 3 / 8 * θ) hs2]
  have h6 := abs_le_of_sq_le_sq' h5 (norm_nonneg _)
  linarith [h6.2]
end Chord
section Exponentials
private theorem expUnit_neg_eq_inv (r : BlockAverages.imaginaryQuaternions) :
    (BlockAverages.expUnit r)⁻¹ = BlockAverages.expUnit (-r) := by apply _root_.YangMills.Construction.LeastQuarticGauge.expUnit_inv <;> assumption
private theorem expUnit_zero_eq_one : BlockAverages.expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem norm_expUnit_sub_one_sub_le (w : BlockAverages.imaginaryQuaternions) (h : ‖w‖ ≤ 1) :
    ‖((BlockAverages.expUnit w : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 - (w : ℍ[ℝ])‖ ≤ ‖w‖ ^ 2 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FourPlaquette.norm_expUnit_sub_one_sub_le_sq <;> assumption
private theorem norm_signedSum_le_fourPlaquette (a : Fin 4 → BlockAverages.imaginaryQuaternions)
    (hs : ∑ i, ‖a i‖ ≤ 1) :
    ‖(a 0 : ℍ[ℝ]) + (a 1 : ℍ[ℝ]) - (a 2 : ℍ[ℝ]) - (a 3 : ℍ[ℝ])‖ ≤
      ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ColdStepAtMirrorFrames.fourPlaquette a) +
        2 * (∑ i, ‖a i‖) ^ 2 := by
  have hs' : ∀ i, ‖a i‖ ≤ 1 := fun i =>
    (Finset.single_le_sum (f := fun i => ‖a i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)).trans hs
  have p0 := norm_nonneg (a 0)
  have p1 := norm_nonneg (a 1)
  have p2 := norm_nonneg (a 2)
  have p3 := norm_nonneg (a 3)
  have s0 := norm_expUnit_sub_one_sub_le (a 0) (hs' 0)
  have s1 := norm_expUnit_sub_one_sub_le (a 1) (hs' 1)
  have s2 := norm_expUnit_sub_one_sub_le (-a 2) (by rw [norm_neg]; exact hs' 2)
  have s3 := norm_expUnit_sub_one_sub_le (-a 3) (by rw [norm_neg]; exact hs' 3)
  have g0 := ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le (a 0)
  have g1 := ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le (a 1)
  have g2 := ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le (-a 2)
  have g3 := ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le (-a 3)
  rw [norm_neg] at g2 g3 s2 s3
  have r2 : ColdStepAtMirrorFrames.BlockOffsets.distFromOne
      (BlockAverages.expUnit (-a 2) * BlockAverages.expUnit (-a 3)) ≤ ‖a 2‖ + ‖a 3‖ :=
    (ColdStepAtMirrorFrames.BlockOffsets.distFromOne_mul _ _).trans (add_le_add g2 g3)
  have r1 : ColdStepAtMirrorFrames.BlockOffsets.distFromOne
      (BlockAverages.expUnit (a 1) * (BlockAverages.expUnit (-a 2) * BlockAverages.expUnit (-a 3))) ≤
        ‖a 1‖ + (‖a 2‖ + ‖a 3‖) :=
    (ColdStepAtMirrorFrames.BlockOffsets.distFromOne_mul _ _).trans (add_le_add g1 r2)
  set q0 : ℍ[ℝ] := ((BlockAverages.expUnit (a 0) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) with hq0
  set q1 : ℍ[ℝ] := ((BlockAverages.expUnit (a 1) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) with hq1
  set q2 : ℍ[ℝ] := ((BlockAverages.expUnit (-a 2) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) with hq2
  set q3 : ℍ[ℝ] := ((BlockAverages.expUnit (-a 3) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) with hq3
  have hP : ((ColdStepAtMirrorFrames.fourPlaquette a : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = q0 * q1 * q2 * q3 := by
    simp only [ColdStepAtMirrorFrames.fourPlaquette, expUnit_neg_eq_inv]
    rfl
  have m2 : ((-a 2 : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) = -(a 2 : ℍ[ℝ]) := rfl
  have m3 : ((-a 3 : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) = -(a 3 : ℍ[ℝ]) := rfl
  rw [m2] at s2
  rw [m3] at s3
  have e : (a 0 : ℍ[ℝ]) + (a 1 : ℍ[ℝ]) - (a 2 : ℍ[ℝ]) - (a 3 : ℍ[ℝ]) =
      (q0 * q1 * q2 * q3 - 1) - ((q0 - 1 - (a 0 : ℍ[ℝ])) + (q1 - 1 - (a 1 : ℍ[ℝ])) + (q2 - 1 - -(a 2 : ℍ[ℝ])) +
        (q3 - 1 - -(a 3 : ℍ[ℝ])) + (q0 - 1) * (q1 * (q2 * q3) - 1) + (q1 - 1) * (q2 * q3 - 1) +
        (q2 - 1) * (q3 - 1)) := by
    noncomm_ring
  have n1 : ‖(q0 - 1) * (q1 * (q2 * q3) - 1)‖ ≤ ‖a 0‖ * (‖a 1‖ + (‖a 2‖ + ‖a 3‖)) := by
    rw [norm_mul]
    exact mul_le_mul g0 r1 (norm_nonneg _) p0
  have n2 : ‖(q1 - 1) * (q2 * q3 - 1)‖ ≤ ‖a 1‖ * (‖a 2‖ + ‖a 3‖) := by
    rw [norm_mul]
    exact mul_le_mul g1 r2 (norm_nonneg _) p1
  have n3 : ‖(q2 - 1) * (q3 - 1)‖ ≤ ‖a 2‖ * ‖a 3‖ := by
    rw [norm_mul]
    exact mul_le_mul g2 g3 (norm_nonneg _) p2
  have hg : ‖q0 * q1 * q2 * q3 - 1‖ =
      ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ColdStepAtMirrorFrames.fourPlaquette a) := by
    unfold ColdStepAtMirrorFrames.BlockOffsets.distFromOne
    rw [hP]
  rw [e, Fin.sum_univ_four]
  refine (norm_sub_le _ _).trans ?_
  rw [hg]
  have hsum := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add s0 s1)) s2)) s3)) n1)) n2)) n3)
  nlinarith [mul_nonneg p0 p1, mul_nonneg p0 p2, mul_nonneg p0 p3, mul_nonneg p1 p2, mul_nonneg p1 p3,
    mul_nonneg p2 p3, sq_nonneg (‖a 0‖), sq_nonneg (‖a 1‖), sq_nonneg (‖a 2‖), sq_nonneg (‖a 3‖)]
end Exponentials
section Cut
private theorem abs_clamp_sub_clamp_le (a b : ℝ) : |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |a - b| := by apply _root_.YangMills.Construction.Reinsertion.abs_clamp_sub_clamp_le <;> assumption
variable {n : ℕ} [NeZero n]
private theorem cutoffProfile_nonneg (o : TorusFields.TorusSite n) (m : ℕ) (z : TorusFields.TorusSite n) :
    0 ≤ MomentLaw.cutoffProfile o m z := le_max_left _ _
private theorem cutoffProfile_le_one (o : TorusFields.TorusSite n) (m : ℕ) (z : TorusFields.TorusSite n) :
    MomentLaw.cutoffProfile o m z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)
private theorem cutoffProfile_eq_one (o : TorusFields.TorusSite n) {m : ℕ} (hm : 2 ≤ m) {z : TorusFields.TorusSite n}
    (h : (TorusFields.supDist z o : ℝ) ≤ m) : MomentLaw.cutoffProfile o m z = 1 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have h1 : 1 ≤ (2 * (m : ℝ) - 1 - (TorusFields.supDist z o : ℝ)) / ((m : ℝ) - 1) := by
    rw [le_div_iff₀ hp]
    linarith
  unfold MomentLaw.cutoffProfile
  rw [min_eq_left h1]
  simp
private theorem cutoffProfile_eq_zero (o : TorusFields.TorusSite n) {m : ℕ} (hm : 2 ≤ m) {z : TorusFields.TorusSite n}
    (h : 2 * m ≤ TorusFields.supDist z o + 1) : MomentLaw.cutoffProfile o m z = 0 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have h' : 2 * (m : ℝ) ≤ (TorusFields.supDist z o : ℝ) + 1 := by exact_mod_cast h
  have h1 : (2 * (m : ℝ) - 1 - (TorusFields.supDist z o : ℝ)) / ((m : ℝ) - 1) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hp.le
  unfold MomentLaw.cutoffProfile
  exact max_eq_left ((min_le_right _ _).trans h1)
private theorem abs_cutoffProfile_sub_le (o : TorusFields.TorusSite n) {m : ℕ} (hm : 2 ≤ m)
    {z z' : TorusFields.TorusSite n} (h1 : TorusFields.supDist z o ≤ TorusFields.supDist z' o + 1)
    (h2 : TorusFields.supDist z' o ≤ TorusFields.supDist z o + 1) :
    |MomentLaw.cutoffProfile o m z - MomentLaw.cutoffProfile o m z'| ≤ 1 / ((m : ℝ) - 1) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  refine (abs_clamp_sub_clamp_le _ _).trans ?_
  have e : (2 * (m : ℝ) - 1 - (TorusFields.supDist z o : ℝ)) / ((m : ℝ) - 1) -
        (2 * (m : ℝ) - 1 - (TorusFields.supDist z' o : ℝ)) / ((m : ℝ) - 1) =
      ((TorusFields.supDist z' o : ℝ) - (TorusFields.supDist z o : ℝ)) / ((m : ℝ) - 1) := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hp]
  refine div_le_div_of_nonneg_right ?_ hp.le
  have h1' : (TorusFields.supDist z o : ℝ) ≤ (TorusFields.supDist z' o : ℝ) + 1 := by exact_mod_cast h1
  have h2' : (TorusFields.supDist z' o : ℝ) ≤ (TorusFields.supDist z o : ℝ) + 1 := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith
private def plaquetteBonds (ℓ : TorusLumps.StepParameters) (W : TorusFields.TorusField n)
    (o x : TorusFields.TorusSite n) (μ ν : Fin 4) : Fin 4 → BlockAverages.imaginaryQuaternions :=
  ![MomentLaw.axialCoords ℓ W o (x, μ), MomentLaw.axialCoords ℓ W o (x + TorusFields.unitStep n μ, ν),
    MomentLaw.axialCoords ℓ W o (x + TorusFields.unitStep n ν, μ), MomentLaw.axialCoords ℓ W o (x, ν)]
private def plaquetteCuts (o : TorusFields.TorusSite n) (m : ℕ) (x : TorusFields.TorusSite n) (μ ν : Fin 4) :
    Fin 4 → ℝ :=
  ![MomentLaw.cutoffProfile o m x, MomentLaw.cutoffProfile o m (x + TorusFields.unitStep n μ),
    MomentLaw.cutoffProfile o m (x + TorusFields.unitStep n ν), MomentLaw.cutoffProfile o m x]
private theorem fourPlaquette_plaquetteBonds (ℓ : TorusLumps.StepParameters) (W : TorusFields.TorusField n)
    (o x : TorusFields.TorusSite n) (μ ν : Fin 4) :
    ColdStepAtMirrorFrames.fourPlaquette (plaquetteBonds ℓ W o x μ ν) =
      ResponseInTheExpansion.axialGaugeAt ℓ W o x * TorusFields.holonomy W x μ ν *
        (ResponseInTheExpansion.axialGaugeAt ℓ W o x)⁻¹ := by
  have e : ∀ b : TorusFields.TorusBond n, BlockAverages.expUnit (MomentLaw.axialCoords ℓ W o b) =
      ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ W o) W b :=
    fun b => GaugeFixing.expUnit_minimalLog _
  show BlockAverages.expUnit (MomentLaw.axialCoords ℓ W o (x, μ)) *
      BlockAverages.expUnit (MomentLaw.axialCoords ℓ W o (x + TorusFields.unitStep n μ, ν)) *
      (BlockAverages.expUnit (MomentLaw.axialCoords ℓ W o (x + TorusFields.unitStep n ν, μ)))⁻¹ *
      (BlockAverages.expUnit (MomentLaw.axialCoords ℓ W o (x, ν)))⁻¹ = _
  rw [e, e, e, e]
  show (ResponseInTheExpansion.axialGaugeAt ℓ W o x * W x μ *
        (ResponseInTheExpansion.axialGaugeAt ℓ W o (x + TorusFields.unitStep n μ))⁻¹) *
      (ResponseInTheExpansion.axialGaugeAt ℓ W o (x + TorusFields.unitStep n μ) * W (x + TorusFields.unitStep n μ) ν *
        (ResponseInTheExpansion.axialGaugeAt ℓ W o (x + TorusFields.unitStep n μ + TorusFields.unitStep n ν))⁻¹) *
      (ResponseInTheExpansion.axialGaugeAt ℓ W o (x + TorusFields.unitStep n ν) * W (x + TorusFields.unitStep n ν) μ *
        (ResponseInTheExpansion.axialGaugeAt ℓ W o (x + TorusFields.unitStep n ν + TorusFields.unitStep n μ))⁻¹)⁻¹ *
      (ResponseInTheExpansion.axialGaugeAt ℓ W o x * W x ν *
        (ResponseInTheExpansion.axialGaugeAt ℓ W o (x + TorusFields.unitStep n ν))⁻¹)⁻¹ =
    ResponseInTheExpansion.axialGaugeAt ℓ W o x * (W x μ * W (x + TorusFields.unitStep n μ) ν *
      (W (x + TorusFields.unitStep n ν) μ)⁻¹ * (W x ν)⁻¹) * (ResponseInTheExpansion.axialGaugeAt ℓ W o x)⁻¹
  rw [add_right_comm x (TorusFields.unitStep n ν) (TorusFields.unitStep n μ)]
  group
private theorem distFromOne_fourPlaquette_plaquetteBonds (ℓ : TorusLumps.StepParameters)
    (W : TorusFields.TorusField n) (o x : TorusFields.TorusSite n) (μ ν : Fin 4) :
    ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ColdStepAtMirrorFrames.fourPlaquette (plaquetteBonds ℓ W o x μ ν)) =
      TorusFields.curvature W x μ ν := by
  rw [fourPlaquette_plaquetteBonds, ColdStepAtMirrorFrames.BlockOffsets.distFromOne_conj]
  rfl
private theorem holonomy_expField (ℓ : TorusLumps.StepParameters) (W : TorusFields.TorusField n)
    (o : TorusFields.TorusSite n) (m : ℕ) (w : ℝ) (x : TorusFields.TorusSite n) (μ ν : Fin 4) :
    TorusFields.holonomy (MomentLaw.expField w (MomentLaw.cutoffCoords ℓ W o m)) x μ ν =
      ColdStepAtMirrorFrames.fourPlaquette fun i => (w * plaquetteCuts o m x μ ν i) • plaquetteBonds ℓ W o x μ ν i := by
  show BlockAverages.expUnit (w • (MomentLaw.cutoffProfile o m x • MomentLaw.axialCoords ℓ W o (x, μ))) *
      BlockAverages.expUnit (w • (MomentLaw.cutoffProfile o m (x + TorusFields.unitStep n μ) •
        MomentLaw.axialCoords ℓ W o (x + TorusFields.unitStep n μ, ν))) *
      (BlockAverages.expUnit (w • (MomentLaw.cutoffProfile o m (x + TorusFields.unitStep n ν) •
        MomentLaw.axialCoords ℓ W o (x + TorusFields.unitStep n ν, μ))))⁻¹ *
      (BlockAverages.expUnit (w • (MomentLaw.cutoffProfile o m x • MomentLaw.axialCoords ℓ W o (x, ν))))⁻¹ =
    BlockAverages.expUnit ((w * MomentLaw.cutoffProfile o m x) • MomentLaw.axialCoords ℓ W o (x, μ)) *
      BlockAverages.expUnit ((w * MomentLaw.cutoffProfile o m (x + TorusFields.unitStep n μ)) •
        MomentLaw.axialCoords ℓ W o (x + TorusFields.unitStep n μ, ν)) *
      (BlockAverages.expUnit ((w * MomentLaw.cutoffProfile o m (x + TorusFields.unitStep n ν)) •
        MomentLaw.axialCoords ℓ W o (x + TorusFields.unitStep n ν, μ)))⁻¹ *
      (BlockAverages.expUnit ((w * MomentLaw.cutoffProfile o m x) • MomentLaw.axialCoords ℓ W o (x, ν)))⁻¹
  simp only [smul_smul]
private theorem curlNorm_toColourForm (B : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions)
    (p : TorusFields.TorusPlaquette n) :
    MomentLaw.curlNorm (MomentLaw.toColourForm B) p = ‖(ResponseInTheExpansion.lieFormCurl B p : ℍ[ℝ])‖ := by
  have hc : ∀ e : Fin 3, WeightedResponses.curl (MomentLaw.toColourForm B e) p =
      BlockAverages.imaginaryComponent e (ResponseInTheExpansion.lieFormCurl B p) := by
    intro e
    fin_cases e <;> simp [WeightedResponses.curl, MomentLaw.toColourForm, ResponseInTheExpansion.lieFormCurl,
      BlockAverages.imaginaryComponent]
  unfold MomentLaw.curlNorm
  simp only [hc]
  have h := Quaternion.normSq_eq_norm_mul_self (ResponseInTheExpansion.lieFormCurl B p : ℍ[ℝ])
  rw [Quaternion.normSq_def'] at h
  have hre : (ResponseInTheExpansion.lieFormCurl B p : ℍ[ℝ]).re = 0 := (ResponseInTheExpansion.lieFormCurl B p).2
  have hs : ∑ e : Fin 3, BlockAverages.imaginaryComponent e (ResponseInTheExpansion.lieFormCurl B p) ^ 2 =
      ‖(ResponseInTheExpansion.lieFormCurl B p : ℍ[ℝ])‖ ^ 2 := by
    rw [Fin.sum_univ_three]
    simp only [BlockAverages.imaginaryComponent]
    simp
    nlinarith
  rw [hs, Real.sqrt_sq (norm_nonneg _)]
end Cut
section Core
variable {n : ℕ} [NeZero n]
private theorem norm_axialCoords_le (hAx : WeightedResponses.axialGaugeNearOneStatement)
    (ℓ : TorusLumps.StepParameters) (W : TorusFields.TorusField n) (o : TorusFields.TorusSite n) (m : ℕ)
    (hn : 4 * m + 2 < n) (hs : 3 * (2 * (m : ℝ) + 1) * MomentLaw.boxCurvature o (2 * (m : ℝ)) W ≤ 1)
    (b : TorusFields.TorusBond n) (h1 : TorusFields.supDist b.1 o ≤ 2 * m)
    (h2 : TorusFields.supDist (b.1 + TorusFields.unitStep n b.2) o ≤ 2 * m) :
    ‖(MomentLaw.axialCoords ℓ W o b : ℍ[ℝ])‖ ≤
      4 * ((TorusFields.supDist b.1 o : ℝ) + 1) * MomentLaw.boxCurvature o (2 * (m : ℝ)) W := by
  have hv0 := boxCurvature_nonneg o (2 * (m : ℝ)) W
  set v := MomentLaw.boxCurvature o (2 * (m : ℝ)) W with hv
  obtain ⟨r, hrm, hrd, h1', h2'⟩ : ∃ r : ℕ, r ≤ 2 * m ∧ r ≤ TorusFields.supDist b.1 o + 1 ∧
      TorusFields.supDist b.1 o ≤ r ∧ TorusFields.supDist (b.1 + TorusFields.unitStep n b.2) o ≤ r :=
    ⟨min (TorusFields.supDist b.1 o + 1) (2 * m), min_le_right _ _, min_le_left _ _, le_min (Nat.le_succ _) h1,
      le_min (supDist_add_unitStep_le _ _ _) h2⟩
  have hRr : (r : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hrm
  have hg := axialGauge_bond_near_one hAx ℓ W o r (by omega) hv0
    (fun x μ ν hμ a0 a1 a2 a3 =>
      curvature_le_boxCurvature o _ W (plaquetteInBox_of_corners hRr hμ a0 a1 a2 a3)) b h1' h2'
  have hrd' : (r : ℝ) ≤ (TorusFields.supDist b.1 o : ℝ) + 1 := by exact_mod_cast hrd
  have hd : (TorusFields.supDist b.1 o : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast h1
  have hg' : ‖((ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ W o) W b :
      BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 3 * ((TorusFields.supDist b.1 o : ℝ) + 1) * v :=
    hg.trans (mul_le_mul_of_nonneg_right (by linarith) hv0)
  have hsm : ‖((ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ W o) W b :
      BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 1 :=
    hg'.trans (le_trans (mul_le_mul_of_nonneg_right (by linarith) hv0) hs)
  have hl := norm_minimalLog_le_of_near_one _ hsm
  show ‖(LumpContours.minimalLog (ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ W o) W b) :
    ℍ[ℝ])‖ ≤ _
  linarith
private theorem four_mul_sq_le_of_le {S Y v : ℝ} (hS0 : 0 ≤ S) (hS : S ≤ 16 * Y * v)
    (hs : 1024 * Y ^ 2 * v ≤ 1) (hv0 : 0 ≤ v) : 4 * S ^ 2 ≤ v := by
  have h1 : S ^ 2 ≤ (16 * Y * v) ^ 2 := pow_le_pow_left₀ hS0 hS 2
  have h2 := mul_le_mul_of_nonneg_right hs hv0
  nlinarith
private theorem plaquette_estimates_of_corners (hAx : WeightedResponses.axialGaugeNearOneStatement)
    (ℓ : TorusLumps.StepParameters) (W : TorusFields.TorusField n) (o : TorusFields.TorusSite n) {m : ℕ}
    (hm : 2 ≤ m) (hn : 4 * m + 2 < n)
    (hs : 1024 * (2 * (m : ℝ) + 1) ^ 2 * MomentLaw.boxCurvature o (2 * (m : ℝ)) W ≤ 1)
    {x : TorusFields.TorusSite n} {μ ν : Fin 4} (hμ : μ < ν)
    (h0 : TorusFields.supDist x o ≤ 2 * m) (h1 : TorusFields.supDist (x + TorusFields.unitStep n μ) o ≤ 2 * m)
    (h2 : TorusFields.supDist (x + TorusFields.unitStep n ν) o ≤ 2 * m)
    (h3 : TorusFields.supDist (x + TorusFields.unitStep n μ + TorusFields.unitStep n ν) o ≤ 2 * m) :
    ∑ i, ‖plaquetteBonds ℓ W o x μ ν i‖ ≤ 16 * (2 * (m : ℝ) + 1) * MomentLaw.boxCurvature o (2 * (m : ℝ)) W ∧
    ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ColdStepAtMirrorFrames.fourPlaquette (plaquetteBonds ℓ W o x μ ν)) ≤
      MomentLaw.boxCurvature o (2 * (m : ℝ)) W ∧
    |plaquetteCuts o m x μ ν 1 - plaquetteCuts o m x μ ν 0| * ‖plaquetteBonds ℓ W o x μ ν 1‖ ≤
      20 * MomentLaw.boxCurvature o (2 * (m : ℝ)) W ∧
    |plaquetteCuts o m x μ ν 2 - plaquetteCuts o m x μ ν 0| * ‖plaquetteBonds ℓ W o x μ ν 2‖ ≤
      20 * MomentLaw.boxCurvature o (2 * (m : ℝ)) W := by
  have hv0 := boxCurvature_nonneg o (2 * (m : ℝ)) W
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hgap : ColdStepAtMirrorFrames.BlockOffsets.distFromOne
      (ColdStepAtMirrorFrames.fourPlaquette (plaquetteBonds ℓ W o x μ ν)) ≤
        MomentLaw.boxCurvature o (2 * (m : ℝ)) W := by
    rw [distFromOne_fourPlaquette_plaquetteBonds]
    exact curvature_le_boxCurvature o _ W
      (plaquetteInBox_of_corners (R := 2 * m) (by push_cast; exact le_rfl) hμ h0 h1 h2 h3)
  set v := MomentLaw.boxCurvature o (2 * (m : ℝ)) W with hv
  have hs3 : 3 * (2 * (m : ℝ) + 1) * v ≤ 1 := by
    have hY : 3 * (2 * (m : ℝ) + 1) ≤ 1024 * (2 * (m : ℝ) + 1) ^ 2 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hY hv0).trans hs
  have q : ∀ b : TorusFields.TorusBond n, TorusFields.supDist b.1 o ≤ 2 * m →
      TorusFields.supDist (b.1 + TorusFields.unitStep n b.2) o ≤ 2 * m →
      ‖MomentLaw.axialCoords ℓ W o b‖ ≤ 4 * (2 * (m : ℝ) + 1) * v := fun b a c => by
    have h := norm_axialCoords_le hAx ℓ W o m hn hs3 b a c
    have hd : (TorusFields.supDist b.1 o : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast a
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hv0)
  have b0 := q (x, μ) h0 h1
  have b1 := q (x + TorusFields.unitStep n μ, ν) h1 h3
  have b2 := q (x + TorusFields.unitStep n ν, μ) h2 (by
    show TorusFields.supDist (x + TorusFields.unitStep n ν + TorusFields.unitStep n μ) o ≤ _
    rw [add_right_comm]
    exact h3)
  have b3 := q (x, ν) h0 h2
  have hm20 : 1 / ((m : ℝ) - 1) * (4 * (2 * (m : ℝ) + 1) * v) ≤ 20 * v := by
    have e : 1 / ((m : ℝ) - 1) * (4 * (2 * (m : ℝ) + 1)) ≤ 20 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hp]
      nlinarith
    have := mul_le_mul_of_nonneg_right e hv0
    calc 1 / ((m : ℝ) - 1) * (4 * (2 * (m : ℝ) + 1) * v) = 1 / ((m : ℝ) - 1) * (4 * (2 * (m : ℝ) + 1)) * v := by ring
      _ ≤ 20 * v := this
  have hB0 : 0 ≤ 1 / ((m : ℝ) - 1) := by positivity
  refine ⟨?_, hgap, ?_, ?_⟩
  · rw [Fin.sum_univ_four]
    show ‖MomentLaw.axialCoords ℓ W o (x, μ)‖ + ‖MomentLaw.axialCoords ℓ W o (x + TorusFields.unitStep n μ, ν)‖ +
      ‖MomentLaw.axialCoords ℓ W o (x + TorusFields.unitStep n ν, μ)‖ + ‖MomentLaw.axialCoords ℓ W o (x, ν)‖ ≤ _
    linarith
  · show |MomentLaw.cutoffProfile o m (x + TorusFields.unitStep n μ) - MomentLaw.cutoffProfile o m x| *
      ‖MomentLaw.axialCoords ℓ W o (x + TorusFields.unitStep n μ, ν)‖ ≤ _
    exact (mul_le_mul (abs_cutoffProfile_sub_le o hm (supDist_add_unitStep_le x o μ) (supDist_le_add_unitStep x o μ))
      b1 (norm_nonneg _) hB0).trans hm20
  · show |MomentLaw.cutoffProfile o m (x + TorusFields.unitStep n ν) - MomentLaw.cutoffProfile o m x| *
      ‖MomentLaw.axialCoords ℓ W o (x + TorusFields.unitStep n ν, μ)‖ ≤ _
    exact (mul_le_mul (abs_cutoffProfile_sub_le o hm (supDist_add_unitStep_le x o ν) (supDist_le_add_unitStep x o ν))
      b2 (norm_nonneg _) hB0).trans hm20
private theorem corners_near_or_plaquetteCuts_eq_zero (o : TorusFields.TorusSite n) {m : ℕ} (hm : 2 ≤ m)
    (x : TorusFields.TorusSite n) (μ ν : Fin 4) :
    (TorusFields.supDist x o ≤ 2 * m ∧ TorusFields.supDist (x + TorusFields.unitStep n μ) o ≤ 2 * m ∧
      TorusFields.supDist (x + TorusFields.unitStep n ν) o ≤ 2 * m ∧
      TorusFields.supDist (x + TorusFields.unitStep n μ + TorusFields.unitStep n ν) o ≤ 2 * m) ∨
    ∀ i, plaquetteCuts o m x μ ν i = 0 := by
  by_cases h : TorusFields.supDist x o ≤ 2 * m ∧ TorusFields.supDist (x + TorusFields.unitStep n μ) o ≤ 2 * m ∧
      TorusFields.supDist (x + TorusFields.unitStep n ν) o ≤ 2 * m ∧
      TorusFields.supDist (x + TorusFields.unitStep n μ + TorusFields.unitStep n ν) o ≤ 2 * m
  · exact Or.inl h
  · right
    have a1 := supDist_add_unitStep_le x o μ
    have a2 := supDist_le_add_unitStep x o μ
    have a3 := supDist_add_unitStep_le x o ν
    have a4 := supDist_le_add_unitStep x o ν
    have a5 := supDist_add_unitStep_le (x + TorusFields.unitStep n μ) o ν
    have a6 := supDist_le_add_unitStep (x + TorusFields.unitStep n μ) o ν
    have a7 := supDist_add_unitStep_le (x + TorusFields.unitStep n ν) o μ
    rw [add_right_comm] at a7
    have z0 : MomentLaw.cutoffProfile o m x = 0 := cutoffProfile_eq_zero o hm (by omega)
    have z1 : MomentLaw.cutoffProfile o m (x + TorusFields.unitStep n μ) = 0 := cutoffProfile_eq_zero o hm (by omega)
    have z2 : MomentLaw.cutoffProfile o m (x + TorusFields.unitStep n ν) = 0 := cutoffProfile_eq_zero o hm (by omega)
    intro i
    fin_cases i
    · exact z0
    · exact z1
    · exact z2
    · exact z0
private theorem plaquetteCuts_nonneg (o : TorusFields.TorusSite n) (m : ℕ) (x : TorusFields.TorusSite n)
    (μ ν : Fin 4) (i : Fin 4) : 0 ≤ plaquetteCuts o m x μ ν i := by
  fin_cases i <;> exact cutoffProfile_nonneg o m _
private theorem plaquetteCuts_le_one (o : TorusFields.TorusSite n) (m : ℕ) (x : TorusFields.TorusSite n)
    (μ ν : Fin 4) (i : Fin 4) : plaquetteCuts o m x μ ν i ≤ 1 := by
  fin_cases i <;> exact cutoffProfile_le_one o m _
private theorem curvature_expField_cutoff_le (hAx : WeightedResponses.axialGaugeNearOneStatement)
    (hPl : ColdStepAtMirrorFrames.ScaledPlaquetteBound) (ℓ : TorusLumps.StepParameters)
    (W : TorusFields.TorusField n) (o : TorusFields.TorusSite n) {m : ℕ} (hm : 2 ≤ m) (hn : 4 * m + 2 < n)
    (hs : 1024 * (2 * (m : ℝ) + 1) ^ 2 * MomentLaw.boxCurvature o (2 * (m : ℝ)) W ≤ 1) {w : ℝ} (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1) (x : TorusFields.TorusSite n) {μ ν : Fin 4} (hμ : μ < ν) :
    TorusFields.curvature (MomentLaw.expField w (MomentLaw.cutoffCoords ℓ W o m)) x μ ν ≤
      64 * MomentLaw.boxCurvature o (2 * (m : ℝ)) W := by
  have hv0 := boxCurvature_nonneg o (2 * (m : ℝ)) W
  show ColdStepAtMirrorFrames.BlockOffsets.distFromOne
    (TorusFields.holonomy (MomentLaw.expField w (MomentLaw.cutoffCoords ℓ W o m)) x μ ν) ≤ _
  rw [holonomy_expField]
  rcases corners_near_or_plaquetteCuts_eq_zero o hm x μ ν with ⟨d0, d1, d2, d3⟩ | hz
  · obtain ⟨hS, hG, c1, c2⟩ := plaquette_estimates_of_corners hAx ℓ W o hm hn hs hμ d0 d1 d2 d3
    set v := MomentLaw.boxCurvature o (2 * (m : ℝ)) W with hv
    set a := plaquetteBonds ℓ W o x μ ν with ha
    set c := plaquetteCuts o m x μ ν with hc
    have hS0 : 0 ≤ ∑ i, ‖a i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsq := four_mul_sq_le_of_le hS0 hS hs hv0
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hS1 : ∑ i, ‖a i‖ ≤ 1 := by
      have hY : 16 * (2 * (m : ℝ) + 1) ≤ 1024 * (2 * (m : ℝ) + 1) ^ 2 := by nlinarith
      exact hS.trans ((mul_le_mul_of_nonneg_right hY hv0).trans hs)
    have hP := hPl a (fun i => w * c i)
      (fun i => ⟨mul_nonneg hw0 (plaquetteCuts_nonneg o m x μ ν i),
        mul_le_one₀ hw1 (plaquetteCuts_nonneg o m x μ ν i) (plaquetteCuts_le_one o m x μ ν i)⟩) hS1
    refine hP.trans ?_
    rw [Fin.sum_univ_four (f := fun i => |w * c i - w * c 0| * ‖a i‖)]
    have e3 : c 3 = c 0 := rfl
    have hg0 : 0 ≤ ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ColdStepAtMirrorFrames.fourPlaquette a) :=
      ColdStepAtMirrorFrames.BlockOffsets.distFromOne_nonneg _
    have t0 : w * c 0 * ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ColdStepAtMirrorFrames.fourPlaquette a) ≤ v := by
      have : w * c 0 ≤ 1 := mul_le_one₀ hw1 (plaquetteCuts_nonneg o m x μ ν 0) (plaquetteCuts_le_one o m x μ ν 0)
      nlinarith [mul_nonneg (sub_nonneg.2 this) hg0]
    have tt : ∀ i, |c i - c 0| * ‖a i‖ ≤ 20 * v → |w * c i - w * c 0| * ‖a i‖ ≤ 20 * v := fun i h => by
      rw [← mul_sub, abs_mul, abs_of_nonneg hw0, mul_assoc]
      have : 0 ≤ |c i - c 0| * ‖a i‖ := by positivity
      nlinarith
    have t1 := tt 1 c1
    have t2 := tt 2 c2
    simp only [sub_self, abs_zero, zero_mul, zero_add, e3, add_zero]
    linarith
  · have e : (fun i => (w * plaquetteCuts o m x μ ν i) • plaquetteBonds ℓ W o x μ ν i) =
        fun _ => (0 : BlockAverages.imaginaryQuaternions) := by
      funext i
      rw [hz i]
      simp
    rw [e]
    have e1 : ColdStepAtMirrorFrames.fourPlaquette (fun _ : Fin 4 => (0 : BlockAverages.imaginaryQuaternions)) = 1 := by
      simp [ColdStepAtMirrorFrames.fourPlaquette, expUnit_zero_eq_one]
    rw [e1, ColdStepAtMirrorFrames.BlockOffsets.distFromOne_one]
    linarith
private theorem curlNorm_cutoff_le (hAx : WeightedResponses.axialGaugeNearOneStatement)
    (ℓ : TorusLumps.StepParameters) (W : TorusFields.TorusField n) (o : TorusFields.TorusSite n) {m : ℕ}
    (hm : 2 ≤ m) (hn : 4 * m + 2 < n)
    (hs : 1024 * (2 * (m : ℝ) + 1) ^ 2 * MomentLaw.boxCurvature o (2 * (m : ℝ)) W ≤ 1)
    (p : WeightedResponses.OrientedPlaquette n) :
    MomentLaw.curlNorm (MomentLaw.toColourForm (MomentLaw.cutoffCoords ℓ W o m)) p.1 ≤
      60 * MomentLaw.boxCurvature o (2 * (m : ℝ)) W := by
  have hv0 := boxCurvature_nonneg o (2 * (m : ℝ)) W
  obtain ⟨⟨x, μ, ν⟩, hμ⟩ := p
  have hμ' : μ < ν := hμ
  rw [curlNorm_toColourForm]
  set a := plaquetteBonds ℓ W o x μ ν with ha
  set c := plaquetteCuts o m x μ ν with hc
  have hform : (ResponseInTheExpansion.lieFormCurl (MomentLaw.cutoffCoords ℓ W o m) (x, μ, ν) : ℍ[ℝ]) =
      c 0 • ((a 0 : ℍ[ℝ]) + (a 1 : ℍ[ℝ]) - (a 2 : ℍ[ℝ]) - (a 3 : ℍ[ℝ])) +
        ((c 1 - c 0) • (a 1 : ℍ[ℝ]) - (c 2 - c 0) • (a 2 : ℍ[ℝ])) := by
    have e : (ResponseInTheExpansion.lieFormCurl (MomentLaw.cutoffCoords ℓ W o m) (x, μ, ν) : ℍ[ℝ]) =
        c 0 • (a 0 : ℍ[ℝ]) + c 1 • (a 1 : ℍ[ℝ]) - c 2 • (a 2 : ℍ[ℝ]) - c 0 • (a 3 : ℍ[ℝ]) := rfl
    rw [e]
    module
  rw [hform]
  rcases corners_near_or_plaquetteCuts_eq_zero o hm x μ ν with ⟨d0, d1, d2, d3⟩ | hz
  · obtain ⟨hS, hG, c1, c2⟩ := plaquette_estimates_of_corners hAx ℓ W o hm hn hs hμ' d0 d1 d2 d3
    set v := MomentLaw.boxCurvature o (2 * (m : ℝ)) W with hv
    have hS0 : 0 ≤ ∑ i, ‖a i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsq := four_mul_sq_le_of_le hS0 hS hs hv0
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hS1 : ∑ i, ‖a i‖ ≤ 1 := by
      have hY : 16 * (2 * (m : ℝ) + 1) ≤ 1024 * (2 * (m : ℝ) + 1) ^ 2 := by nlinarith
      exact hS.trans ((mul_le_mul_of_nonneg_right hY hv0).trans hs)
    have hL := norm_signedSum_le_fourPlaquette a hS1
    have c0 := plaquetteCuts_nonneg o m x μ ν 0
    have c0' := plaquetteCuts_le_one o m x μ ν 0
    refine (norm_add_le _ _).trans ?_
    have n1 : ‖c 0 • ((a 0 : ℍ[ℝ]) + (a 1 : ℍ[ℝ]) - (a 2 : ℍ[ℝ]) - (a 3 : ℍ[ℝ]))‖ ≤ v + v := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg c0]
      have hn0 := norm_nonneg ((a 0 : ℍ[ℝ]) + (a 1 : ℍ[ℝ]) - (a 2 : ℍ[ℝ]) - (a 3 : ℍ[ℝ]))
      have : c 0 * ‖(a 0 : ℍ[ℝ]) + (a 1 : ℍ[ℝ]) - (a 2 : ℍ[ℝ]) - (a 3 : ℍ[ℝ])‖ ≤
          ‖(a 0 : ℍ[ℝ]) + (a 1 : ℍ[ℝ]) - (a 2 : ℍ[ℝ]) - (a 3 : ℍ[ℝ])‖ := by nlinarith
      nlinarith
    have n2 : ‖(c 1 - c 0) • (a 1 : ℍ[ℝ]) - (c 2 - c 0) • (a 2 : ℍ[ℝ])‖ ≤ 20 * v + 20 * v := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        exact c1
      · rw [norm_smul, Real.norm_eq_abs]
        exact c2
    linarith
  · rw [show c 0 = 0 from hz 0, show c 1 = 0 from hz 1, show c 2 = 0 from hz 2]
    simp only [zero_smul, sub_self, smul_zero, add_zero, norm_zero]
    linarith
private theorem cutoff_estimates (hAx : WeightedResponses.axialGaugeNearOneStatement)
    (hPl : ColdStepAtMirrorFrames.ScaledPlaquetteBound) (ℓ : TorusLumps.StepParameters)
    (W : TorusFields.TorusField n) (o : TorusFields.TorusSite n) {m : ℕ} (hm : 2 ≤ m) (hn : 4 * m + 2 < n)
    (hs : 1024 * (2 * (m : ℝ) + 1) ^ 2 * MomentLaw.boxCurvature o (2 * (m : ℝ)) W ≤ 1) :
    (∀ c : TorusFields.TorusBond n, c.1 ∈ ResponseInTheExpansion.supBall o (2 * (m : ℝ)) →
      c.1 + TorusFields.unitStep n c.2 ∈ ResponseInTheExpansion.supBall o (2 * (m : ℝ)) →
      ‖(MomentLaw.axialCoords ℓ W o c : Quaternion ℝ)‖ ≤
        4 * ((TorusFields.supDist c.1 o : ℝ) + 1) * MomentLaw.boxCurvature o (2 * (m : ℝ)) W) ∧
    (∀ p : WeightedResponses.OrientedPlaquette n,
      MomentLaw.curlNorm (MomentLaw.toColourForm (MomentLaw.cutoffCoords ℓ W o m)) p.1 ≤
        60 * MomentLaw.boxCurvature o (2 * (m : ℝ)) W) ∧
    (∀ v : ℝ, 0 ≤ v → v ≤ 1 → ∀ (x : TorusFields.TorusSite n) (μ ν : Fin 4), μ < ν →
      TorusFields.curvature (MomentLaw.expField v (MomentLaw.cutoffCoords ℓ W o m)) x μ ν ≤
        64 * MomentLaw.boxCurvature o (2 * (m : ℝ)) W) ∧
    ∃ g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion, ∀ c : TorusFields.TorusBond n,
      c.1 ∈ ResponseInTheExpansion.supBall o (m : ℝ) → c.1 + TorusFields.unitStep n c.2 ∈ ResponseInTheExpansion.supBall o (m : ℝ) →
      MomentLaw.expField 1 (MomentLaw.cutoffCoords ℓ W o m) c.1 c.2 = ResponseInTheExpansion.gaugeTransform g W c := by
  have hv0 := boxCurvature_nonneg o (2 * (m : ℝ)) W
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hs3 : 3 * (2 * (m : ℝ) + 1) * MomentLaw.boxCurvature o (2 * (m : ℝ)) W ≤ 1 := by
    have hY : 3 * (2 * (m : ℝ) + 1) ≤ 1024 * (2 * (m : ℝ) + 1) ^ 2 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hY hv0).trans hs
  have hnat : ∀ z : TorusFields.TorusSite n, z ∈ ResponseInTheExpansion.supBall o (2 * (m : ℝ)) →
      TorusFields.supDist z o ≤ 2 * m := fun z hz => by
    have := mem_supBall_iff.1 hz
    exact_mod_cast this
  refine ⟨fun c h1 h2 => norm_axialCoords_le hAx ℓ W o m hn hs3 c (hnat _ h1) (hnat _ h2),
    curlNorm_cutoff_le hAx ℓ W o hm hn hs,
    fun v h0 h1 x μ ν hμ => curvature_expField_cutoff_le hAx hPl ℓ W o hm hn hs h0 h1 x hμ,
    ResponseInTheExpansion.axialGaugeAt ℓ W o, fun c h1 _ => ?_⟩
  have hc1 := cutoffProfile_eq_one o hm (mem_supBall_iff.1 h1)
  show BlockAverages.expUnit ((1 : ℝ) • (MomentLaw.cutoffProfile o m c.1 • MomentLaw.axialCoords ℓ W o (c.1, c.2))) = _
  rw [hc1, one_smul, one_smul]
  exact GaugeFixing.expUnit_minimalLog _
end Core
section Numbers
private theorem clusterRange_sq_estimates {x v : ℝ} (hx : (2 : ℝ) ^ 100 ≤ x) (hv : v ≤ x ^ (-(1 / 4) : ℝ))
    (hv0 : 0 ≤ v) :
    2 ≤ TorusLumps.clusterRange x ^ 2 ∧
      1024 * (2 * ((TorusLumps.clusterRange x ^ 2 : ℕ) : ℝ) + 1) ^ 2 * v ≤ 1 ∧
      4 * ((TorusLumps.clusterRange x ^ 2 : ℕ) : ℝ) + 2 < x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = x ^ ((1 : ℝ) / 100) := ⟨_, rfl⟩
  have hy0 : 0 < y := hy ▸ Real.rpow_pos_of_pos hx0 _
  have hy100 : y ^ 100 = x := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hy2 : 2 ≤ y := by
    by_contra h
    have := pow_lt_pow_left₀ (not_le.1 h) hy0.le (by norm_num : (100 : ℕ) ≠ 0)
    rw [hy100] at this
    linarith
  have hr1 : y ≤ (TorusLumps.clusterRange x : ℝ) := by
    unfold TorusLumps.clusterRange
    rw [hy]
    exact Nat.le_ceil _
  have hr2 : (TorusLumps.clusterRange x : ℝ) < y + 1 := by
    unfold TorusLumps.clusterRange
    rw [hy]
    exact Nat.ceil_lt_add_one (by rw [← hy]; exact hy0.le)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = TorusLumps.clusterRange x := ⟨_, rfl⟩
  rw [← hr] at hr1 hr2 ⊢
  have hr2' : (2 : ℝ) ≤ r := hy2.trans hr1
  have hrn : 2 ≤ r := by exact_mod_cast hr2'
  have hrs : (r : ℝ) ^ 2 ≤ 4 * y ^ 2 := by nlinarith
  have hvy : v * y ^ 25 ≤ 1 := by
    have e : x ^ (-(1 / 4) : ℝ) = (y ^ 25)⁻¹ := by
      rw [Real.rpow_neg hx0.le, hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    rw [e] at hv
    have hp : 0 < y ^ 25 := by positivity
    calc v * y ^ 25 ≤ (y ^ 25)⁻¹ * y ^ 25 := mul_le_mul_of_nonneg_right hv hp.le
      _ = 1 := inv_mul_cancel₀ hp.ne'
  have hy21 : (2 : ℝ) ^ 21 ≤ y ^ 21 := pow_le_pow_left₀ (by norm_num) hy2 21
  have hy98 : (2 : ℝ) ^ 98 ≤ y ^ 98 := pow_le_pow_left₀ (by norm_num) hy2 98
  have hysq : (4 : ℝ) ≤ y ^ 2 := by nlinarith
  refine ⟨by nlinarith, ?_, ?_⟩
  · push_cast
    have hY : 2 * (r : ℝ) ^ 2 + 1 ≤ 9 * y ^ 2 := by nlinarith
    have hY0 : 0 ≤ 2 * (r : ℝ) ^ 2 + 1 := by positivity
    have hYs : (2 * (r : ℝ) ^ 2 + 1) ^ 2 ≤ (9 * y ^ 2) ^ 2 := pow_le_pow_left₀ hY0 hY 2
    have h1 : 1024 * (2 * (r : ℝ) ^ 2 + 1) ^ 2 * v ≤ 82944 * (y ^ 4 * v) := by
      have := mul_le_mul_of_nonneg_right hYs hv0
      nlinarith
    have hyv : 0 ≤ y ^ 4 * v := by positivity
    have h2 : 82944 * (y ^ 4 * v) ≤ y ^ 21 * (y ^ 4 * v) :=
      mul_le_mul_of_nonneg_right (by norm_num at hy21 ⊢; linarith) hyv
    have h3 : y ^ 21 * (y ^ 4 * v) = v * y ^ 25 := by ring
    linarith
  · push_cast
    rw [← hy100]
    have e : y ^ 100 = y ^ 2 * y ^ 98 := by ring
    rw [e]
    have h1 : y ^ 2 * 2 ^ 98 ≤ y ^ 2 * y ^ 98 := mul_le_mul_of_nonneg_left hy98 (by positivity)
    have h2 : (17 : ℝ) * y ^ 2 < y ^ 2 * 2 ^ 98 := by
      have : (17 : ℝ) < 2 ^ 98 := by norm_num
      nlinarith
    nlinarith
private theorem le_pow_of_rpow_neg_le_inv (L N : ℕ) (hL : 0 < L) {x : ℝ} (hx : 1 ≤ x)
    (h : (L : ℝ) ^ (-(N : ℝ) / 4) ≤ x⁻¹) : x ≤ (L : ℝ) ^ N := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hx0 : 0 < x := by linarith
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = (L : ℝ) ^ ((N : ℝ) / 4) := ⟨_, rfl⟩
  have hP : 0 < P := hPd ▸ Real.rpow_pos_of_pos hLr _
  have e : (L : ℝ) ^ (-(N : ℝ) / 4) = P⁻¹ := by
    rw [neg_div, Real.rpow_neg hLr.le, hPd]
  rw [e] at h
  have hxP : x ≤ P := (inv_le_inv₀ hP hx0).1 h
  have e2 : (L : ℝ) ^ N = P ^ 4 := by
    rw [hPd, ← Real.rpow_natCast _ 4, ← Real.rpow_mul hLr.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [e2]
  exact hxP.trans (le_self_pow₀ (hx.trans hxP) (by norm_num))
end Numbers
end GoodConfigCutoff
open GoodConfigCutoff
private theorem cutoff_estimates_at_point (hAx : WeightedResponses.axialGaugeNearOneStatement)
    (hPl : ColdStepAtMirrorFrames.ScaledPlaquetteBound) {Λ : MomentLaw.MomentParameters}
    (S : MomentLaw.MomentPoint Λ) (hx : (2 : ℝ) ^ 100 ≤ S.scaleCoupling)
    (w1 : (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) ≤ S.scaleCoupling⁻¹) (u : ℕ)
    (hsd : Λ.stepParams.side ^ S.logIndex ≤ S.levelSide u) (n : ℕ) [NeZero n] (hn : n = S.levelSide u)
    (W : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n)) (hgood : S.IsGoodConfig u n W Y) :
    (∀ c : TorusFields.TorusBond n, c.1 ∈ ResponseInTheExpansion.supBall (S.originSite u n) (2 * S.rangeSq) →
      c.1 + TorusFields.unitStep n c.2 ∈ ResponseInTheExpansion.supBall (S.originSite u n) (2 * S.rangeSq) →
      ‖(MomentLaw.axialCoords Λ.stepParams W (S.originSite u n) c : Quaternion ℝ)‖ ≤
        4 * ((TorusFields.supDist c.1 (S.originSite u n) : ℝ) + 1) * S.localCurvature u n W) ∧
    (∀ p : WeightedResponses.OrientedPlaquette n,
      MomentLaw.curlNorm (S.cutoffColourForm u n W) p.1 ≤ 60 * S.localCurvature u n W) ∧
    (∀ v : ℝ, 0 ≤ v → v ≤ 1 → ∀ (x : TorusFields.TorusSite n) (μ ν : Fin 4), μ < ν →
      TorusFields.curvature (MomentLaw.expField v (S.cutoffLie u n W)) x μ ν ≤ 64 * S.localCurvature u n W) ∧
    ∃ g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion, ∀ c : TorusFields.TorusBond n,
      c.1 ∈ ResponseInTheExpansion.supBall (S.originSite u n) S.rangeSq →
      c.1 + TorusFields.unitStep n c.2 ∈ ResponseInTheExpansion.supBall (S.originSite u n) S.rangeSq →
      S.smoothedField u n W c.1 c.2 = ResponseInTheExpansion.gaugeTransform g W c := by
  have hv0 : 0 ≤ S.localCurvature u n W := boxCurvature_nonneg _ _ _
  obtain ⟨n1, n2, n3⟩ := clusterRange_sq_estimates hx hgood.curvature_le hv0
  have hL : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hx1 : 1 ≤ S.scaleCoupling := le_trans (by norm_num) hx
  have hxL := le_pow_of_rpow_neg_le_inv Λ.stepParams.side S.logIndex hL hx1 w1
  have hsdr : (Λ.stepParams.side : ℝ) ^ S.logIndex ≤ (S.levelSide u : ℝ) := by exact_mod_cast hsd
  have hn' : 4 * S.rangeSq + 2 < n := by
    have h : 4 * ((S.rangeSq : ℕ) : ℝ) + 2 < (n : ℝ) := by
      rw [hn]
      exact lt_of_lt_of_le (lt_of_lt_of_le n3 hxL) hsdr
    exact_mod_cast h
  exact cutoff_estimates hAx hPl Λ.stepParams W (S.originSite u n) n1 hn' n2
theorem goodConfigCutoffStatement_proof (hW : MomentLaw.scaleWindowStatement)
    (hAx : WeightedResponses.axialGaugeNearOneStatement) (hPl : ColdStepAtMirrorFrames.ScaledPlaquetteBound) :
    MomentLaw.goodConfigCutoffStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hpos, h⟩ := hW a ha
  refine ⟨L₀, rt₀, C₀, hpos, fun L hLo hL Tb t1 t2 t3 t4 t5 t6 t7 Kr hKr => ?_⟩
  obtain ⟨y₀, hy⟩ := h L hLo hL Tb t1 t2 t3 t4 t5 t6 t7 Kr hKr
  refine ⟨y₀, fun y h1 h2 h3 g hg hgy k _ hk2 hk8 R d hd => ?_⟩
  obtain ⟨C, c, X₀, hc, hyX, hQ⟩ := hy y h1 h2 h3 g hg hgy k hk2 hk8 R d hd
  refine ⟨C, c, max X₀ ((2 : ℝ) ^ 100), hc, hyX.trans (le_max_left _ _), fun S hx u hu1 hu2 n _ hn W Y hgood => ?_⟩
  obtain ⟨w1, -, -, -, -, -, hwu⟩ := hQ S ((le_max_left _ _).trans hx)
  exact cutoff_estimates_at_point hAx hPl S ((le_max_right _ _).trans hx) w1 u (hwu u hu1 hu2).2 n hn W Y hgood
end YangMills.Construction.MomentLaw
end
