import YangMills.Construction.ClusterExpansionOfAStep.CostsOfTwoSettingsProof
import YangMills.Construction.ClusterExpansionOfAStep.HessianOfAFamilyAtTheFlatFieldProof
import YangMills.Construction.FormsOnATorus.ActionOnTwoTori
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped Quaternion
namespace YangMills.Construction.LimitForms
open TorusFields TorusLumps TorusPaths TorusContours LevelAction RenormalizationStepParameters ShareFamilies ResponseInTheExpansion BoxGaussian
  TorusComparison ColdChain
open BlockAverages hiding unitStep
section Sites
variable {n : ℕ} [NeZero n]
private theorem valMinAbs_intCast_of_small {u : ℤ} (h : 2 * |u| < (n : ℤ)) : ((u : ZMod n)).valMinAbs = u := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
private def centredCoords (x : TorusSite n) : Fin 4 → ℤ := fun i => (x i).valMinAbs
omit [NeZero n] in
private theorem siteOfInt_centredCoords (x : TorusSite n) : siteOfInt (centredCoords x) = x := by
  funext i
  simp [siteOfInt, centredCoords]
private theorem centredCoords_siteOfInt {u : Fin 4 → ℤ} {p : ℕ} (hu : OffsetInBox p u) (hp : 2 * p < n) :
    centredCoords (siteOfInt u : TorusSite n) = u := by
  funext i
  have h1 := hu i
  exact valMinAbs_intCast_of_small (by omega)
abbrev _root_.YangMills.DeltaSharedProofs.p501837 := @centredCoords_siteOfInt
private theorem centredCoords_zero_add {u : Fin 4 → ℤ} {p : ℕ} (hu : OffsetInBox p u) (hp : 2 * p < n) :
    centredCoords ((0 : TorusSite n) + siteOfInt u) = u := by
  rw [zero_add]
  exact centredCoords_siteOfInt hu hp
private theorem mem_supBall_iff {o z : TorusSite n} {r : ℕ} : z ∈ supBall o (r : ℝ) ↔ _root_.YangMills.Construction.TorusFields.supDist z o ≤ r := by
  simp [supBall]
private theorem add_mem_supBall (o : TorusSite n) {u : Fin 4 → ℤ} {r : ℕ} (hu : OffsetInBox r u) :
    o + siteOfInt u ∈ supBall o (r : ℝ) := by
  rw [mem_supBall_iff, _root_.YangMills.Construction.TorusFields.supDist_comm]
  refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le o u r fun i => ?_
  have := hu i
  rw [Int.abs_eq_natAbs] at this
  omega
abbrev _root_.YangMills.SharedProofs.p7847 := @add_mem_supBall
private theorem supBall_isRegular (o : TorusSite n) {r : ℕ} (hr : 2048 ≤ r) (hn : 4 * r < n) :
    IsRegularRegion (supBall o (r : ℝ)) 1024 := by
  intro z
  refine ⟨fun i => if 0 ≤ (z i - o i).valMinAbs then -1 else 1, fun i => by dsimp only; split_ifs <;> simp, ?_⟩
  intro q hq hqz h hs hh
  rw [mem_supBall_iff] at hq ⊢
  rw [_root_.YangMills.Construction.TorusFields.supDist_le_iff]
  intro i
  have hv := (_root_.YangMills.Construction.TorusFields.supDist_le_iff q o r).mp hq i
  have he := (_root_.YangMills.Construction.TorusFields.supDist_le_iff z q 1024).mp (by rwa [_root_.YangMills.Construction.TorusFields.supDist_comm]) i
  have hsi := hs i
  have hhi := abs_le.mp (hh i)
  set v := (q i - o i).valMinAbs with hvdef
  set e := (z i - q i).valMinAbs with hedef
  have hzo : z i - o i = ((v + e : ℤ) : ZMod n) := by
    push_cast
    rw [hvdef, hedef, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs]
    ring
  have hve : |v + e| ≤ (r : ℤ) + 1024 := by
    rw [abs_le]
    constructor <;> omega
  have hw : (z i - o i).valMinAbs = v + e := by
    rw [hzo]
    exact valMinAbs_intCast_of_small (by omega)
  have hqo : (q + siteOfInt h : TorusSite n) i - o i = ((v + h i : ℤ) : ZMod n) := by
    push_cast
    rw [hvdef, ZMod.coe_valMinAbs]
    simp only [Pi.add_apply, siteOfInt]
    ring
  rw [hqo]
  refine (_root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le _).trans ?_
  simp only [hw] at hsi
  by_cases h0 : 0 ≤ v + e
  · rw [if_pos h0] at hsi
    omega
  · rw [if_neg h0] at hsi
    omega
abbrev _root_.YangMills.SharedProofs.p31712 := @supBall_isRegular
private theorem univ_isRegular : IsRegularRegion (Finset.univ : Finset (TorusSite n)) 1024 :=
  fun _ => ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => Finset.mem_univ _⟩
private theorem trivialField_isColdOn {s : ℝ} (hs : 0 < s) (X : Finset (TorusSite n)) : IsColdOn s X (trivialField n) := by
  intro p _
  have : holonomy (trivialField n) p.1 p.2.1 p.2.2 = 1 := by
    simp [holonomy, trivialField]
  simp [curvature, this, hs]
abbrev _root_.YangMills.SharedProofs.p25190 := @trivialField_isColdOn
private theorem exists_offsetInBox (u : Fin 4 → ℤ) : ∃ d : ℕ, OffsetInBox d u := by
  refine ⟨Finset.univ.sup fun i => (u i).natAbs, fun i => ?_⟩
  have : (u i).natAbs ≤ Finset.univ.sup fun i => (u i).natAbs :=
    Finset.le_sup (f := fun i => (u i).natAbs) (Finset.mem_univ i)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast this
abbrev _root_.YangMills.SharedProofs.p5953 := @exists_offsetInBox
private theorem offsetInBox_mono {e : Fin 4 → ℤ} {p p' : ℕ} (hp : p ≤ p') (he : OffsetInBox p e) :
    OffsetInBox p' e :=
  fun i => (he i).trans (by exact_mod_cast hp)
private theorem offsetInBox_add {e e' : Fin 4 → ℤ} {p p' : ℕ} (he : OffsetInBox p e) (he' : OffsetInBox p' e') :
    OffsetInBox (p + p') (e + e') := by
  intro i
  have a := abs_le.mp (he i)
  have b := abs_le.mp (he' i)
  simp only [Pi.add_apply]
  rw [abs_le]
  push_cast
  constructor <;> omega
abbrev _root_.YangMills.SharedProofs.p43430 := @offsetInBox_add
private theorem offsetInBox_single (μ : Fin 4) : OffsetInBox 1 (Pi.single μ 1 : Fin 4 → ℤ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockCosts.offsetInBox_single <;> assumption
private theorem natAbs_sub_le_bondSupDist (b b' : IntBond) (i : Fin 4) : (b.1 i - b'.1 i).natAbs ≤ bondSupDist b b' :=
  Finset.le_sup (f := fun i => (b.1 i - b'.1 i).natAbs) (Finset.mem_univ i)
private theorem supDist_bondFrom (o : TorusSite n) (b b' : IntBond) (h : ∀ i, 2 * |b.1 i - b'.1 i| < (n : ℤ)) :
    _root_.YangMills.Construction.TorusFields.supDist (bondFrom o b).1 (bondFrom o b').1 = bondSupDist b b' := by
  unfold _root_.YangMills.Construction.TorusFields.supDist bondSupDist
  congr 1
  funext i
  have e : (bondFrom o b).1 i - (bondFrom o b').1 i = ((b.1 i - b'.1 i : ℤ) : ZMod n) := by
    simp [bondFrom, siteOfInt]
  rw [e, valMinAbs_intCast_of_small (h i)]
abbrev _root_.YangMills.SharedProofs.p76264 := @supDist_bondFrom
end Sites
section Moves
variable {n : ℕ} [NeZero n]
omit [NeZero n] in
private theorem mixedDeriv_smul_signs {G : TorusField n → ℝ} {W : TorusField n} {k : ℕ} (c : Fin k → TorusBond n)
    (Xs : Fin k → imaginaryQuaternions) (ε : Fin k → ℝ) (hε : ∀ l, ε l * ε l = 1) :
    mixedDeriv G W c (fun l => ε l • Xs l) = (∏ l, ε l) * mixedDeriv G W c Xs := by
  classical
  let f : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) := ContinuousLinearMap.pi fun l => ε l • ContinuousLinearMap.proj l
  have hf : ∀ σ l, f σ l = ε l * σ l := fun σ l => rfl
  have hff : ∀ σ, f (f σ) = σ := by
    intro σ
    funext l
    rw [hf, hf, ← mul_assoc, hε, one_mul]
  let D : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ) := ContinuousLinearEquiv.equivOfInverse f f hff hff
  have hD : ∀ σ l, D σ l = ε l * σ l := fun σ l => rfl
  have hm : ∀ σ, perturb c (fun l => ε l • Xs l) σ W = perturb c Xs (D σ) W := by
    intro σ
    funext x i
    unfold TorusFields.perturb
    congr 2
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hD, smul_smul, mul_comm]
  unfold mixedDeriv
  have e : (fun σ : Fin k → ℝ => G (perturb c (fun l => ε l • Xs l) σ W)) =
      (fun σ : Fin k → ℝ => G (perturb c Xs σ W)) ∘ D := by
    funext σ
    simp only [Function.comp, hm]
  have hcomp := ContinuousLinearEquiv.iteratedFDerivWithin_comp_right D (fun σ : Fin k → ℝ => G (perturb c Xs σ W))
    (uniqueDiffOn_univ (𝕜 := ℝ)) (Set.mem_univ (D 0)) k
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hcomp
  rw [e, hcomp, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have e2 : (fun i : Fin k => (D : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) (Pi.single i 1)) =
      fun i => ε i • (Pi.single i 1 : Fin k → ℝ) := by
    funext i l
    show D (Pi.single i 1) l = _
    rw [hD]
    by_cases h : l = i
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  have e3 : D 0 = 0 := map_zero D
  rw [e3]
  show (iteratedFDeriv ℝ k _ 0) (fun i => (D : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) (Pi.single i 1)) = _
  rw [e2, ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
private theorem eventually_isCold_perturb {k : ℕ} (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) {s : ℝ}
    (hs : 0 < s) : ∀ᶠ σ in 𝓝 (0 : Fin k → ℝ), IsCold s (perturb c Xs σ (trivialField n)) := by apply _root_.YangMills.SharedProofs.p58478 <;> assumption
private theorem expUnit_neg (x : imaginaryQuaternions) : expUnit (-x) = (expUnit x)⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.expUnit_neg <;> assumption
private def imageBond (g : TorusIsometry) (b : TorusBond n) : TorusBond n :=
  if g.axisSign (g.axisPerm.symm b.2) = 1 then (g.mapSite b.1, g.axisPerm.symm b.2)
  else (g.mapSite b.1 - unitStep n (g.axisPerm.symm b.2), g.axisPerm.symm b.2)
private def imageSign (g : TorusIsometry) (k : Fin 4) : ℝ := if g.axisSign (g.axisPerm.symm k) = 1 then 1 else -1
private theorem imageSign_mul_self (g : TorusIsometry) (k : Fin 4) : imageSign g k * imageSign g k = 1 := by
  unfold imageSign
  split_ifs <;> norm_num
private theorem imageBond_injective (g : TorusIsometry) : Function.Injective (imageBond (n := n) g) := by
  rintro ⟨x, k⟩ ⟨x', k'⟩ he
  have hk : g.axisPerm.symm k = g.axisPerm.symm k' := by
    have := congrArg Prod.snd he
    unfold imageBond at this
    simp only at this
    split_ifs at this <;> exact this
  have hk' : k = k' := g.axisPerm.symm.injective hk
  subst hk'
  have hx : g.mapSite x = g.mapSite x' := by
    have := congrArg Prod.fst he
    unfold imageBond at this
    simp only at this
    split_ifs at this
    · exact this
    · exact sub_left_injective this
  rw [mapSite_injective g hx]
private theorem perturb_transports (g : TorusIsometry) {k : ℕ} (c : Fin k → TorusBond n)
    (Xs : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) :
    g.Transports (perturb c Xs σ (trivialField n))
      (perturb (fun l => imageBond g (c l)) (fun l => imageSign g (c l).2 • Xs l) σ (trivialField n)) := by
  classical
  intro x j
  by_cases hs : g.axisSign (g.axisPerm.symm j) = 1
  · rw [if_pos hs]
    have hb : imageBond g (x, j) = (g.mapSite x, g.axisPerm.symm j) := by simp [imageBond, hs]
    show expUnit (∑ l, if imageBond g (c l) = (g.mapSite x, g.axisPerm.symm j) then
        σ l • imageSign g (c l).2 • Xs l else 0) * 1 =
      expUnit (∑ l, if c l = (x, j) then σ l • Xs l else 0) * 1
    congr 2
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : c l = (x, j)
    · have h2 : imageBond g (c l) = (g.mapSite x, g.axisPerm.symm j) := by rw [h, hb]
      have h3 : imageSign g (c l).2 = 1 := by
        rw [h]
        simp [imageSign, hs]
      rw [if_pos h2, if_pos h, h3, one_smul]
    · have h2 : ¬ imageBond g (c l) = (g.mapSite x, g.axisPerm.symm j) :=
        fun he => h (imageBond_injective g (he.trans hb.symm))
      rw [if_neg h2, if_neg h]
  · rw [if_neg hs]
    have hb : imageBond g (x, j) = (g.mapSite x - unitStep n (g.axisPerm.symm j), g.axisPerm.symm j) := by
      simp [imageBond, hs]
    show (expUnit (∑ l, if imageBond g (c l) = (g.mapSite x - unitStep n (g.axisPerm.symm j), g.axisPerm.symm j) then
        σ l • imageSign g (c l).2 • Xs l else 0) * 1)⁻¹ = expUnit (∑ l, if c l = (x, j) then σ l • Xs l else 0) * 1
    have hsum : (∑ l, if imageBond g (c l) = (g.mapSite x - unitStep n (g.axisPerm.symm j), g.axisPerm.symm j) then
        σ l • imageSign g (c l).2 • Xs l else 0) = -∑ l, if c l = (x, j) then σ l • Xs l else 0 := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h : c l = (x, j)
      · have h2 : imageBond g (c l) = (g.mapSite x - unitStep n (g.axisPerm.symm j), g.axisPerm.symm j) := by
          rw [h, hb]
        have h3 : imageSign g (c l).2 = -1 := by
          rw [h]
          simp [imageSign, hs]
        rw [if_pos h2, if_pos h, h3]
        module
      · have h2 : ¬ imageBond g (c l) = (g.mapSite x - unitStep n (g.axisPerm.symm j), g.axisPerm.symm j) :=
          fun he => h (imageBond_injective g (he.trans hb.symm))
        rw [if_neg h2, if_neg h, neg_zero]
    rw [hsum, mul_one, mul_one, expUnit_neg, inv_inv]
omit [NeZero n] in
private theorem imageBond_bondFrom (g : TorusIsometry) (b : IntBond) :
    imageBond g (bondFrom (0 : TorusSite n) b) = bondFrom (0 : TorusSite n) (bondImage g b).1 := by
  have hs : ∀ i, g.mapSite ((0 : TorusSite n) + siteOfInt b.1) i =
      ((g.axisSign i * b.1 (g.axisPerm i) + g.offset i : ℤ) : ZMod n) := by
    intro i
    simp [TorusIsometry.mapSite, siteOfInt]
  unfold imageBond bondImage bondFrom
  by_cases h : g.axisSign (g.axisPerm.symm b.2) = 1
  · simp only [h, if_true, zero_add]
    refine Prod.ext ?_ rfl
    funext i
    have := hs i
    rw [zero_add] at this
    simpa [siteOfInt] using this
  · simp only [h, if_false, zero_add]
    refine Prod.ext ?_ rfl
    funext i
    have := hs i
    rw [zero_add] at this
    simp only [Pi.sub_apply, siteOfInt, this, unitStep]
    by_cases hi : i = g.axisPerm.symm b.2
    · subst hi
      simp
    · simp [Pi.single_eq_of_ne hi]
private theorem imageSign_eq (g : TorusIsometry) (b : IntBond) : imageSign g b.2 = (bondImage g b).2 := by
  unfold imageSign bondImage
  split_ifs <;> rfl
end Moves
section Whole
variable {n : ℕ} [NeZero n]
private theorem actionAtLevel_univ_transports (hS : LevelSharesFormCurvatureFamily) (Tb : ParameterAssignment)
    (hD : Tb.Admissible) (k : ℕ) (hn : Tb.n₀ ≤ n) (g : TorusIsometry) {W W' : TorusField n}
    (hW : IsCold Tb.threshold W) (hW' : IsCold Tb.threshold W') (hC : g.Transports W W') :
    actionAtLevel Tb.coupling Tb.side k (Finset.univ : Finset (TorusSite n)) W' =
      actionAtLevel Tb.coupling Tb.side k Finset.univ W := by
  cases k with
  | zero => exact wilsonAction_of_transports hC
  | succ t =>
    obtain ⟨-, h2, h3⟩ := hS Tb hD Tb.floorMin le_rfl t
    rw [← h3 n hn W' hW', ← h3 n hn W hW]
    exact h2 n hn g W W' hW hW' hC
private theorem mixedDeriv_univ_image (hS : LevelSharesFormCurvatureFamily) (Tb : ParameterAssignment) (hD : Tb.Admissible)
    (k : ℕ) (hn : Tb.n₀ ≤ n) (g : TorusIsometry) (b b' : IntBond) :
    mixedDeriv (actionAtLevel Tb.coupling Tb.side k (Finset.univ : Finset (TorusSite n))) (trivialField n)
        ![bondFrom 0 b, bondFrom 0 b'] ![imaginaryUnitI, imaginaryUnitI] =
      (bondImage g b).2 * (bondImage g b').2 *
        mixedDeriv (actionAtLevel Tb.coupling Tb.side k (Finset.univ : Finset (TorusSite n))) (trivialField n)
          ![bondFrom 0 (bondImage g b).1, bondFrom 0 (bondImage g b').1] ![imaginaryUnitI, imaginaryUnitI] := by
  have hσ := hD.σ_pos
  set c : Fin 2 → TorusBond n := ![bondFrom 0 b, bondFrom 0 b'] with hc
  set Xs : Fin 2 → imaginaryQuaternions := ![imaginaryUnitI, imaginaryUnitI] with hXs
  set A := actionAtLevel Tb.coupling Tb.side k (Finset.univ : Finset (TorusSite n)) with hA
  have hev : (fun σ : Fin 2 → ℝ => A (perturb c Xs σ (trivialField n))) =ᶠ[𝓝 0]
      fun σ => A (perturb (fun l => imageBond g (c l)) (fun l => imageSign g (c l).2 • Xs l) σ (trivialField n)) := by
    filter_upwards [eventually_isCold_perturb c Xs hσ,
      eventually_isCold_perturb (fun l => imageBond g (c l)) (fun l => imageSign g (c l).2 • Xs l) hσ] with σ h1 h2
    exact (actionAtLevel_univ_transports hS Tb hD k hn g h1 h2 (perturb_transports g c Xs σ)).symm
  have e1 : mixedDeriv A (trivialField n) c Xs =
      mixedDeriv A (trivialField n) (fun l => imageBond g (c l)) (fun l => imageSign g (c l).2 • Xs l) := by
    unfold mixedDeriv
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev 2).eq_of_nhds]
  have e2 := mixedDeriv_smul_signs (G := A) (W := trivialField n) (fun l => imageBond g (c l)) Xs
    (fun l => imageSign g (c l).2) (fun l => imageSign_mul_self g _)
  rw [e1, e2, Fin.prod_univ_two]
  have e3 : (fun l => imageBond g (c l)) = ![bondFrom 0 (bondImage g b).1, bondFrom 0 (bondImage g b').1] := by
    funext l
    fin_cases l
    · exact imageBond_bondFrom g b
    · exact imageBond_bondFrom g b'
  rw [e3]
  have e4 : imageSign g (c 0).2 = (bondImage g b).2 := imageSign_eq g b
  have e5 : imageSign g (c 1).2 = (bondImage g b').2 := imageSign_eq g b'
  rw [e4, e5]
end Whole
section Entries
private def boxEntry (a : ℝ) (L k : ℕ) {n : ℕ} [NeZero n] (o : TorusSite n) (X : Finset (TorusSite n))
    (b b' : IntBond) : ℝ :=
  mixedDeriv (actionAtLevel a L k X) (trivialField n) ![bondFrom o b, bondFrom o b'] ![imaginaryUnitI, imaginaryUnitI]
private theorem norm_imaginaryUnitI : ‖imaginaryUnitI‖ = 1 := by apply _root_.YangMills.SharedProofs.p16675 <;> assumption
private theorem unitVectors_imaginaryUnitI : AreUnitVectors ![imaginaryUnitI, imaginaryUnitI] := by
  intro l
  fin_cases l <;> exact norm_imaginaryUnitI
abbrev _root_.YangMills.SharedProofs.p1192 := @unitVectors_imaginaryUnitI
private def TwoTorusComparison (a δ : ℝ) (L : ℕ) (C : ℝ) : Prop :=
  ∀ (t n n' : ℕ) [NeZero n] [NeZero n'] (X : Finset (TorusSite n)) (X' : Finset (TorusSite n'))
    (z : TorusSite n) (z' : TorusSite n') (m r : ℕ), 64 ≤ n → 64 ≤ n' → IsRegularRegion X 1024 →
    IsRegularRegion X' 1024 → 4 * m + 2 < n → 4 * m + 2 < n' → 4 * r + 4 ≤ m →
    (∀ h, OffsetInBox (2 * m) h → (z + siteOfInt h ∈ X ↔ z' + siteOfInt h ∈ X')) →
    ∀ (k : ℕ) (c : Fin k → (Fin 4 → ℤ) × Fin 4) (Xs : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 2 →
      AreUnitVectors Xs → (∀ l, OffsetInBox r (c l).1) →
      |mixedDeriv (actionAtLevel a L t X) (trivialField n) (fun l => bondFrom z (c l)) Xs -
          mixedDeriv (actionAtLevel a L t X') (trivialField n') (fun l => bondFrom z' (c l)) Xs| ≤
        C * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8)
private def EntryDecay (a δ : ℝ) (L : ℕ) (C : ℝ) : Prop :=
  ∀ (t n : ℕ) [NeZero n] (X : Finset (TorusSite n)) (o : TorusSite n) (b b' : IntBond), 64 ≤ n →
    IsRegularRegion X 1024 → (∀ i, 2 * |b.1 i - b'.1 i| < (n : ℤ)) →
    |boxEntry a L t o X b b'| ≤ C * Real.exp (-δ * bondSupDist b b')
private theorem supDist_le_bondListSpread {n : ℕ} [NeZero n] (c : Fin 2 → TorusBond n) :
    _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1 ≤ bondListSpread c := by
  unfold bondListSpread
  exact le_trans (Finset.le_sup (f := fun l' => _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c l').1) (Finset.mem_univ 1))
    (Finset.le_sup (f := fun l => Finset.univ.sup fun l' => _root_.YangMills.Construction.TorusFields.supDist (c l).1 (c l').1) (Finset.mem_univ 0))
private theorem exists_entryDecay (hA : ActionSmoothAlongMoves) {a δ lam ρ σA cg : ℝ} {L : ℕ} {N : ℕ → ℝ}
    (ha : 0 < a) (hL : Odd L) (hc : ColdChainConstants a δ L lam ρ σA cg N) : ∃ C, 0 < C ∧ EntryDecay a δ L C := by
  obtain ⟨C, hC, H⟩ := hA a δ L lam ρ σA cg N ha hL hc
  obtain ⟨hδ, -, -, -, -, hσ, -, -, -⟩ := hc
  refine ⟨C, hC, fun t n _ X o b b' hn hreg hsm => ?_⟩
  have h := (H t n hn X (trivialField n) hreg (trivialField_isColdOn hσ X)).2.1 2 ![bondFrom o b, bondFrom o b']
    ![imaginaryUnitI, imaginaryUnitI] (by norm_num) (by norm_num) unitVectors_imaginaryUnitI
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le)
  have h2 : bondSupDist b b' ≤ bondListSpread (![bondFrom o b, bondFrom o b'] : Fin 2 → TorusBond n) := by
    rw [← supDist_bondFrom o b b' hsm]
    exact supDist_le_bondListSpread (![bondFrom o b, bondFrom o b'] : Fin 2 → TorusBond n)
  have h5 : (bondSupDist b b' : ℝ) ≤ (bondListSpread (![bondFrom o b, bondFrom o b'] : Fin 2 → TorusBond n) : ℝ) := by
    exact_mod_cast h2
  nlinarith
private theorem boxEntry_comparison {a δ C : ℝ} {L : ℕ} (hB : TwoTorusComparison a δ L C) (k : ℕ) {n n' : ℕ}
    [NeZero n] [NeZero n'] (o : TorusSite n) (o' : TorusSite n') (X : Finset (TorusSite n)) (X' : Finset (TorusSite n'))
    (e : Fin 4 → ℤ) (m d : ℕ) (b b' : IntBond) (hn : 64 ≤ n) (hn' : 64 ≤ n') (hX : IsRegularRegion X 1024)
    (hX' : IsRegularRegion X' 1024) (hm : 4 * m + 2 < n) (hm' : 4 * m + 2 < n') (hd : 4 * d + 4 ≤ m)
    (hag : ∀ h, OffsetInBox (2 * m) h → (o + siteOfInt e + siteOfInt h ∈ X ↔ o' + siteOfInt e + siteOfInt h ∈ X'))
    (hb : OffsetInBox d (b.1 - e)) (hb' : OffsetInBox d (b'.1 - e)) :
    |boxEntry a L k o X b b' - boxEntry a L k o' X' b b'| ≤ C * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8) := by
  have key := hB k n n' X X' (o + siteOfInt e) (o' + siteOfInt e) m d hn hn' hX hX' hm hm' hd hag 2
    ![(b.1 - e, b.2), (b'.1 - e, b'.2)] ![imaginaryUnitI, imaginaryUnitI] (by norm_num) (by norm_num)
    unitVectors_imaginaryUnitI (by
      intro l
      fin_cases l
      · exact hb
      · exact hb')
  have hf : ∀ (p : ℕ) [NeZero p] (w : TorusSite p), (fun l => bondFrom (w + siteOfInt e)
      ((![(b.1 - e, b.2), (b'.1 - e, b'.2)] : Fin 2 → (Fin 4 → ℤ) × Fin 4) l)) = ![bondFrom w b, bondFrom w b'] := by
    intro p _ w
    funext l
    fin_cases l
    · show (w + siteOfInt e + siteOfInt (b.1 - e), b.2) = (w + siteOfInt b.1, b.2)
      rw [add_assoc, ← siteOfInt_add, add_sub_cancel]
    · show (w + siteOfInt e + siteOfInt (b'.1 - e), b'.2) = (w + siteOfInt b'.1, b'.2)
      rw [add_assoc, ← siteOfInt_add, add_sub_cancel]
  rw [hf, hf] at key
  exact key
private theorem tendsto_poly_mul_exp (C β : ℝ) (hβ : 0 < β) :
    Tendsto (fun m : ℕ => C * ((m : ℝ) + 1) ^ 4 * Real.exp (-β * m)) atTop (𝓝 0) := by
  set r := Real.exp (-β) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : |r| < 1 := by
    rw [abs_of_pos hr0, hr, Real.exp_lt_one_iff]
    linarith
  have h1 := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 4 hr1).comp (tendsto_add_atTop_nat 1)
  have h2 := h1.const_mul (C * r⁻¹)
  rw [mul_zero] at h2
  refine h2.congr fun m => ?_
  have e : Real.exp (-β * m) = r ^ m := by
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    ring
  simp only [Function.comp, Nat.cast_add, Nat.cast_one]
  rw [e, pow_succ]
  field_simp
  ring
abbrev _root_.YangMills.SharedProofs.p40441 := @tendsto_poly_mul_exp
private theorem eventually_poly_mul_exp_lt (C β : ℝ) (hβ : 0 < β) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m, M ≤ m → C * ((m : ℝ) + 1) ^ 4 * Real.exp (-β * m) < ε := by
  have := (tendsto_poly_mul_exp C β hβ).eventually (Iio_mem_nhds hε)
  obtain ⟨M, hM⟩ := eventually_atTop.mp this
  exact ⟨M, hM⟩
abbrev _root_.YangMills.SharedProofs.p56559 := @eventually_poly_mul_exp_lt
private instance neZeroCubeSide (N : ℕ) : NeZero (16 * (N + 1)) := ⟨by omega⟩
private theorem cubeEntry_eq_boxEntry (a : ℝ) (L k N : ℕ) (b b' : IntBond) :
    cubeEntry a L k N b b' = boxEntry a L k (0 : TorusSite (16 * (N + 1))) (supBall 0 (N : ℝ)) b b' := rfl
private theorem cube_isRegular {N : ℕ} (hN : 2048 ≤ N) :
    IsRegularRegion (supBall (0 : TorusSite (16 * (N + 1))) (N : ℝ)) 1024 :=
  supBall_isRegular 0 hN (by omega)
private theorem add_siteOfInt_zero_add {p : ℕ} (w : TorusSite p) (h : Fin 4 → ℤ) :
    w + siteOfInt (0 : Fin 4 → ℤ) + siteOfInt h = w + siteOfInt h := by
  funext i
  simp [siteOfInt]
private theorem mem_cubes_iff {N N' q : ℕ} (hN : q ≤ N) (hN' : q ≤ N') {h : Fin 4 → ℤ} (hh : OffsetInBox q h) :
    (0 : TorusSite (16 * (N + 1))) + siteOfInt 0 + siteOfInt h ∈ supBall (0 : TorusSite (16 * (N + 1))) (N : ℝ) ↔
      (0 : TorusSite (16 * (N' + 1))) + siteOfInt 0 + siteOfInt h ∈
        supBall (0 : TorusSite (16 * (N' + 1))) (N' : ℝ) := by
  rw [add_siteOfInt_zero_add, add_siteOfInt_zero_add]
  exact ⟨fun _ => add_mem_supBall 0 (offsetInBox_mono hN' hh), fun _ => add_mem_supBall 0 (offsetInBox_mono hN hh)⟩
private theorem exists_cubeEntry_limit {a δ C : ℝ} {L : ℕ} (hδ : 0 < δ) (hB : TwoTorusComparison a δ L C) (k : ℕ)
    (b b' : IntBond) : ∃ q, Tendsto (fun N => cubeEntry a L k N b b') atTop (𝓝 q) := by
  have hcau : CauchySeq fun N => cubeEntry a L k N b b' := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨d₁, h₁⟩ := exists_offsetInBox b.1
    obtain ⟨d₂, h₂⟩ := exists_offsetInBox b'.1
    obtain ⟨M, hM⟩ := eventually_poly_mul_exp_lt C (δ / 8) (by linarith) hε
    obtain ⟨m, hm⟩ : ∃ m, m = M + 4 * (d₁ + d₂) + 4 := ⟨_, rfl⟩
    obtain ⟨N₀, hN₀⟩ : ∃ N₀, N₀ = 2 * m + 2048 := ⟨_, rfl⟩
    refine ⟨N₀, fun N hN => ?_⟩
    rw [Real.dist_eq, cubeEntry_eq_boxEntry, cubeEntry_eq_boxEntry]
    have hc := boxEntry_comparison hB k (0 : TorusSite (16 * (N + 1))) (0 : TorusSite (16 * (N₀ + 1)))
      (supBall 0 (N : ℝ)) (supBall 0 (N₀ : ℝ)) 0 m (d₁ + d₂) b b' (by omega) (by omega) (cube_isRegular (by omega))
      (cube_isRegular (by omega)) (by omega) (by omega) (by omega) (fun h hh => mem_cubes_iff (by omega) (by omega) hh)
      (by simpa using offsetInBox_mono (by omega) h₁) (by simpa using offsetInBox_mono (by omega) h₂)
    refine lt_of_le_of_lt hc ?_
    have h := hM m (by omega)
    have e : -(δ / 8) * (m : ℝ) = -δ * m / 8 := by ring
    rwa [e] at h
  exact cauchySeq_tendsto_of_complete hcau
private theorem tendsto_boxEntry_univ {a δ C : ℝ} {L : ℕ} (hδ : 0 < δ) (hB : TwoTorusComparison a δ L C) (k : ℕ)
    {b b' : IntBond} {q : ℝ} (hq : Tendsto (fun N => cubeEntry a L k N b b') atTop (𝓝 q)) :
    Tendsto (fun N => boxEntry a L k (0 : TorusSite (16 * (N + 1))) Finset.univ b b') atTop (𝓝 q) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨d₁, h₁⟩ := exists_offsetInBox b.1
  obtain ⟨d₂, h₂⟩ := exists_offsetInBox b'.1
  obtain ⟨M, hM⟩ := eventually_poly_mul_exp_lt C (δ / 8) (by linarith) (half_pos hε)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hq (ε / 2) (half_pos hε)
  obtain ⟨m, hm⟩ : ∃ m, m = M + 4 * (d₁ + d₂) + 4 := ⟨_, rfl⟩
  refine ⟨N₁ + 2 * m + 2048, fun N hN => ?_⟩
  have h1 := hN₁ N (by omega)
  rw [cubeEntry_eq_boxEntry] at h1
  have hc := boxEntry_comparison hB k (0 : TorusSite (16 * (N + 1))) (0 : TorusSite (16 * (N + 1)))
    (supBall 0 (N : ℝ)) Finset.univ 0 m (d₁ + d₂) b b' (by omega) (by omega) (cube_isRegular (by omega))
    univ_isRegular (by omega) (by omega) (by omega) (fun h hh => ?_) (by simpa using offsetInBox_mono (by omega) h₁)
    (by simpa using offsetInBox_mono (by omega) h₂)
  · have h2 := hM m (by omega)
    have e : -(δ / 8) * (m : ℝ) = -δ * m / 8 := by ring
    rw [e] at h2
    have h3 := lt_of_le_of_lt hc h2
    rw [Real.dist_eq] at h1 ⊢
    have h4 := abs_sub_lt_iff.mp h1
    have h5 := abs_sub_lt_iff.mp h3
    rw [abs_sub_lt_iff]
    constructor <;> linarith [h4.1, h4.2, h5.1, h5.2]
  · rw [add_siteOfInt_zero_add]
    exact ⟨fun _ => Finset.mem_univ _, fun _ => add_mem_supBall 0 (offsetInBox_mono (by omega) hh)⟩
private theorem boxEntry_sub_limit_le {a δ C₁ C₂ : ℝ} {L : ℕ} (hδ : 0 < δ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hB : TwoTorusComparison a δ L C₁) (hS : EntryDecay a δ L C₂) (k : ℕ) {Q : IntBond → IntBond → ℝ}
    (hQ : ∀ b b', Tendsto (fun N => cubeEntry a L k N b b') atTop (𝓝 (Q b b'))) {n : ℕ} [NeZero n]
    (o : TorusSite n) {R : ℕ} (hR : 1024 ≤ R) (hn : 16 * R < n) {b b' : IntBond}
    (hb : BondOffsetInBox (3 * R / 2) b) (hb' : BondOffsetInBox (3 * R / 2) b') :
    |boxEntry a L k o (supBall o ((2 * R : ℕ) : ℝ)) b b' - Q b b'| ≤
      C₁ * (((R / 4 : ℕ) : ℝ) + 1) ^ 4 * Real.exp (-δ * (R / 4 : ℕ) / 8) +
        2 * C₂ * Real.exp (-δ * (R / 16 - 1 : ℕ)) := by
  set E := boxEntry a L k o (supBall o ((2 * R : ℕ) : ℝ)) b b' with hE
  set m := R / 4 with hm
  set d := R / 16 - 1 with hd
  have hlim : Tendsto (fun N => |E - cubeEntry a L k N b b'|) atTop (𝓝 |E - Q b b'|) :=
    (tendsto_const_nhds.sub (hQ b b')).abs
  refine le_of_tendsto hlim ?_
  have hreg : IsRegularRegion (supBall o ((2 * R : ℕ) : ℝ)) 1024 := supBall_isRegular o (by omega) (by omega)
  have hsm : ∀ i, 2 * |b.1 i - b'.1 i| ≤ 6 * (R : ℤ) := by
    intro i
    have a1 := abs_le.mp (hb.1 i)
    have a2 := abs_le.mp (hb'.1 i)
    have : |b.1 i - b'.1 i| ≤ 3 * (R : ℤ) := by
      rw [abs_le]
      constructor <;> omega
    omega
  filter_upwards [eventually_ge_atTop (2 * R + 2048)] with N hN
  rw [cubeEntry_eq_boxEntry]
  have hp1 : 0 ≤ C₁ * (((m : ℕ) : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8) := by positivity
  have hp2 : 0 ≤ 2 * C₂ * Real.exp (-δ * d) := by positivity
  by_cases hclose : bondSupDist b b' ≤ d
  · have hc := boxEntry_comparison hB k o (0 : TorusSite (16 * (N + 1))) (supBall o ((2 * R : ℕ) : ℝ))
      (supBall 0 (N : ℝ)) b.1 m d b b' (by omega) (by omega) hreg (cube_isRegular (by omega)) (by omega) (by omega)
      (by omega) (fun h hh => ?_) (by
        intro i
        simp) (by
        intro i
        have := natAbs_sub_le_bondSupDist b' b i
        have h2 := natAbs_sub_le_bondSupDist b b' i
        rw [Int.abs_eq_natAbs]
        simp only [Pi.sub_apply]
        omega)
    · exact hc.trans (by linarith)
    · have h3 : OffsetInBox (2 * R) (b.1 + h) := offsetInBox_mono (by omega) (offsetInBox_add hb.1 hh)
      have h3' : OffsetInBox N (b.1 + h) := offsetInBox_mono (by omega) h3
      rw [add_assoc, add_assoc, ← siteOfInt_add, ← siteOfInt_add]
      exact ⟨fun _ => add_mem_supBall 0 h3', fun _ => add_mem_supBall o h3⟩
  · have hfar : Real.exp (-δ * bondSupDist b b') ≤ Real.exp (-δ * d) := by
      apply Real.exp_le_exp.mpr
      have : (d : ℝ) ≤ bondSupDist b b' := by exact_mod_cast (not_le.mp hclose).le
      nlinarith
    have h1 := hS k n (supBall o ((2 * R : ℕ) : ℝ)) o b b' (by omega) hreg (fun i => by
      have := hsm i
      omega)
    have h2 := hS k (16 * (N + 1)) (supBall 0 (N : ℝ)) 0 b b' (by omega) (cube_isRegular (by omega)) (fun i => by
      have := hsm i
      omega)
    have h3 := abs_sub (boxEntry a L k o (supBall o ((2 * R : ℕ) : ℝ)) b b')
      (boxEntry a L k (0 : TorusSite (16 * (N + 1))) (supBall 0 (N : ℝ)) b b')
    have h4 : C₂ * Real.exp (-δ * bondSupDist b b') ≤ C₂ * Real.exp (-δ * d) :=
      mul_le_mul_of_nonneg_left hfar hC₂.le
    linarith
end Entries
section Forms
variable {n : ℕ} [NeZero n]
private def liftedForm (v : IntBond → ℝ) : TorusBond n → imaginaryQuaternions :=
  fun c => v (centredCoords c.1, c.2) • imaginaryUnitI
private theorem imaginaryComponent_smul_unitI (e : Fin 3) (t : ℝ) :
    imaginaryComponent e (t • imaginaryUnitI) = if e = 0 then t else 0 := by
  have h0 : imaginaryComponent 0 (t • imaginaryUnitI) = t * 1 := rfl
  have h1 : imaginaryComponent 1 (t • imaginaryUnitI) = t * 0 := rfl
  have h2 : imaginaryComponent 2 (t • imaginaryUnitI) = t * 0 := rfl
  fin_cases e
  · simpa using h0
  · simpa using h1
  · simpa using h2
private theorem sum_torusBonds_eq (v : IntBond →₀ ℝ) {p : ℕ} (hv : ∀ b ∈ v.support, OffsetInBox p b.1)
    (hp : 2 * p < n) (f : TorusBond n → ℝ) :
    ∑ c : TorusBond n, f c * v (centredCoords c.1, c.2) = ∑ b ∈ v.support, f (bondFrom 0 b) * v b := by
  classical
  have hinj : Set.InjOn (bondFrom (0 : TorusSite n)) v.support := by
    intro b hb b' hb' he
    have h1 : centredCoords ((0 : TorusSite n) + siteOfInt b.1) = b.1 := centredCoords_zero_add (hv b hb) hp
    have h2 : centredCoords ((0 : TorusSite n) + siteOfInt b'.1) = b'.1 := centredCoords_zero_add (hv b' hb') hp
    have h3 : (bondFrom (0 : TorusSite n) b).1 = (bondFrom (0 : TorusSite n) b').1 := congrArg Prod.fst he
    have h4 : (bondFrom (0 : TorusSite n) b).2 = (bondFrom (0 : TorusSite n) b').2 := congrArg Prod.snd he
    have h3' : (0 : TorusSite n) + siteOfInt b.1 = 0 + siteOfInt b'.1 := h3
    exact Prod.ext (by rw [← h1, ← h2, h3']) h4
  have e1 : ∑ c ∈ v.support.image (bondFrom (0 : TorusSite n)), f c * v (centredCoords c.1, c.2) =
      ∑ b ∈ v.support, f (bondFrom 0 b) * v b := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun b hb => ?_
    have h1 : centredCoords ((0 : TorusSite n) + siteOfInt b.1) = b.1 := centredCoords_zero_add (hv b hb) hp
    have h2 : ((centredCoords (bondFrom (0 : TorusSite n) b).1, (bondFrom (0 : TorusSite n) b).2) : IntBond) = b :=
      Prod.ext h1 rfl
    rw [h2]
  rw [← e1]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_
  by_contra hne
  apply hc
  have h0 : v (centredCoords c.1, c.2) ≠ 0 := fun h => hne (by rw [h, mul_zero])
  refine Finset.mem_image.mpr ⟨(centredCoords c.1, c.2), Finsupp.mem_support_iff.mpr h0, ?_⟩
  refine Prod.ext ?_ rfl
  show (0 : TorusSite n) + siteOfInt (centredCoords c.1) = c.1
  rw [zero_add, siteOfInt_centredCoords]
private theorem form_liftedForm {F : TorusBond n → TorusBond n → ℝ}
    {G : (TorusBond n → imaginaryQuaternions) → (TorusBond n → imaginaryQuaternions) → ℝ}
    (hG : ∀ u v : TorusBond n → imaginaryQuaternions, G u v = ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
      F b b' * imaginaryComponent e (u b) * imaginaryComponent e (v b'))
    (v w : IntBond →₀ ℝ) {p : ℕ} (hv : ∀ b ∈ v.support, OffsetInBox p b.1)
    (hw : ∀ b ∈ w.support, OffsetInBox p b.1) (hp : 2 * p < n) :
    G (liftedForm v) (liftedForm w) =
      ∑ b ∈ v.support, ∑ b' ∈ w.support, v b * F (bondFrom 0 b) (bondFrom 0 b') * w b' := by
  classical
  rw [hG]
  have h1 : ∀ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
      F b b' * imaginaryComponent e (liftedForm v b) * imaginaryComponent e (liftedForm w b') =
      if e = 0 then ∑ b : TorusBond n, ∑ b' : TorusBond n,
        (F b b' * v (centredCoords b.1, b.2)) * w (centredCoords b'.1, b'.2) else 0 := by
    intro e
    by_cases he : e = 0
    · rw [if_pos he]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      simp only [liftedForm, imaginaryComponent_smul_unitI, if_pos he]
    · rw [if_neg he]
      refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
      simp only [liftedForm, imaginaryComponent_smul_unitI, if_neg he, mul_zero]
  simp only [h1, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h2 : ∀ b : TorusBond n, ∑ b' : TorusBond n, (F b b' * v (centredCoords b.1, b.2)) * w (centredCoords b'.1, b'.2) =
      ∑ b' ∈ w.support, (F b (bondFrom 0 b') * v (centredCoords b.1, b.2)) * w b' := fun b =>
    sum_torusBonds_eq w hw hp fun b' => F b b' * v (centredCoords b.1, b.2)
  simp only [h2]
  rw [Finset.sum_comm]
  have h3 : ∀ b' ∈ w.support, ∑ b : TorusBond n, (F b (bondFrom 0 b') * v (centredCoords b.1, b.2)) * w b' =
      ∑ b ∈ v.support, v b * F (bondFrom 0 b) (bondFrom 0 b') * w b' := by
    intro b' _
    have := sum_torusBonds_eq v hv hp fun c => F c (bondFrom 0 b') * w b'
    calc _ = ∑ c : TorusBond n, F c (bondFrom 0 b') * w b' * v (centredCoords c.1, c.2) :=
          Finset.sum_congr rfl fun c _ => by ring
      _ = ∑ b ∈ v.support, F (bondFrom 0 b) (bondFrom 0 b') * w b' * v b := this
      _ = _ := Finset.sum_congr rfl fun c _ => by ring
  rw [Finset.sum_congr rfl h3, Finset.sum_comm]
private theorem lieFormCurl_liftedForm (v : IntBond → ℝ) {h : Fin 4 → ℤ} {p : ℕ} (hh : OffsetInBox p h)
    (hp : 2 * (p + 1) < n) (μ ν : Fin 4) :
    lieFormCurl (liftedForm (n := n) v) (siteOfInt h, μ, ν) = intCurl v (h, μ, ν) • imaginaryUnitI := by
  have c0 : centredCoords (siteOfInt h : TorusSite n) = h := centredCoords_siteOfInt hh (by omega)
  have c1 : ∀ μ : Fin 4, centredCoords ((siteOfInt h : TorusSite n) + unitStep n μ) = h + Pi.single μ 1 := by
    intro μ
    rw [← siteOfInt_single, ← siteOfInt_add]
    exact centredCoords_siteOfInt (offsetInBox_add hh (offsetInBox_single μ)) hp
  simp only [lieFormCurl, liftedForm, c0, c1, intCurl]
  module
private theorem norm_smul_unitI_sq (t : ℝ) : ‖t • imaginaryUnitI‖ ^ 2 = t ^ 2 := by
  rw [norm_smul, norm_imaginaryUnitI, mul_one, Real.norm_eq_abs, sq_abs]
private theorem centredCoords_add_unitStep (φ : (Fin 4 → ℤ) →₀ ℝ) {p : ℕ} (hφ : ∀ x ∈ φ.support, OffsetInBox p x)
    (hp : 2 * (p + 1) < n) (x : TorusSite n) (i : Fin 4) :
    φ (centredCoords (x + unitStep n i)) = φ (centredCoords x + Pi.single i 1) := by
  by_cases h1 : φ (centredCoords (x + unitStep n i)) = 0
  · by_cases h2 : φ (centredCoords x + Pi.single i 1) = 0
    · rw [h1, h2]
    · have hb := hφ _ (Finsupp.mem_support_iff.mpr h2)
      have e : (siteOfInt (centredCoords x + Pi.single i 1) : TorusSite n) = x + unitStep n i := by
        rw [siteOfInt_add, siteOfInt_centredCoords, siteOfInt_single]
      have := centredCoords_siteOfInt (n := n) (offsetInBox_mono (by omega : p ≤ p + 1) hb) (by omega)
      rw [e] at this
      rw [this]
  · have hb := hφ _ (Finsupp.mem_support_iff.mpr h1)
    have e : (siteOfInt (centredCoords (x + unitStep n i) - Pi.single i 1) : TorusSite n) = x := by
      funext j
      have := congrFun (siteOfInt_centredCoords (x + unitStep n i)) j
      have h3 : (siteOfInt (Pi.single i 1) : TorusSite n) = unitStep n i := siteOfInt_single i
      have h4 := congrFun h3 j
      simp only [siteOfInt, Pi.sub_apply, Int.cast_sub] at this h4 ⊢
      rw [this, h4]
      simp
    have hbox : OffsetInBox (p + 1) (centredCoords (x + unitStep n i) - Pi.single i 1) := by
      intro j
      have a := abs_le.mp (hb j)
      have b := abs_le.mp (offsetInBox_single i j)
      simp only [Pi.sub_apply]
      rw [abs_le]
      push_cast at a b ⊢
      constructor <;> omega
    have h5 := centredCoords_siteOfInt (n := n) hbox hp
    rw [e] at h5
    rw [h5]
    simp
end Forms
theorem cubeLimitForm_holds (hT : FlatActionDerivativesAgree) (hA : ActionSmoothAlongMoves)
    (hF : cubeHessianStatement) (hS : LevelSharesFormCurvatureFamily) : cubeLimitFormStatement := by
  intro Tb hD
  have hc := hD.chain
  have hδ := hD.δ₁_pos
  have ha : 0 < Tb.coupling := by linarith [hD.a_ge]
  obtain ⟨C₁, hC₁, hB⟩ := hT Tb.coupling Tb.δ₁ Tb.side Tb.lam Tb.ρA Tb.σA Tb.cg Tb.N ha hD.L_odd hc
  obtain ⟨C₂, hC₂, hSp⟩ := exists_entryDecay hA ha hD.L_odd hc
  obtain ⟨CQ, R₁, -, hForm⟩ := hF Tb hD
  have hB' : TwoTorusComparison Tb.coupling Tb.δ₁ Tb.side C₁ := fun t n n' _ _ => hB t n n'
  set δ := Tb.δ₁ with hδdef
  obtain ⟨R₂, hR₂⟩ := eventually_poly_mul_exp_lt (C₁ * Real.exp δ + 2 * C₂ * Real.exp (2 * δ)) (δ / 64)
    (by linarith) one_pos
  refine ⟨δ / 64, C₂, max (max 1024 R₁) R₂, by linarith, fun k => ?_⟩
  choose Q hQ using fun b b' => exists_cubeEntry_limit hδ hB' k b b'
  refine ⟨Q, ⟨hQ, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g b b'
    have l1 := tendsto_boxEntry_univ hδ hB' k (hQ b b')
    have l2 := (tendsto_boxEntry_univ hδ hB' k (hQ (bondImage g b).1 (bondImage g b').1)).const_mul
      ((bondImage g b).2 * (bondImage g b').2)
    refine tendsto_nhds_unique (l2.congr' ?_) l1
    filter_upwards [eventually_ge_atTop Tb.n₀] with N hN
    exact (mixedDeriv_univ_image hS Tb hD k (by omega) g b b').symm
  · intro b b'
    refine le_of_tendsto (hQ b b').abs ?_
    obtain ⟨d₁, h₁⟩ := exists_offsetInBox b.1
    obtain ⟨d₂, h₂⟩ := exists_offsetInBox b'.1
    filter_upwards [eventually_ge_atTop (d₁ + d₂ + 2048)] with N hN
    rw [cubeEntry_eq_boxEntry]
    refine (hSp k (16 * (N + 1)) (supBall 0 (N : ℝ)) 0 b b' (by omega) (cube_isRegular (by omega))
      fun i => ?_).trans ?_
    · have a1 := abs_le.mp (h₁ i)
      have a2 := abs_le.mp (h₂ i)
      have : |b.1 i - b'.1 i| ≤ (d₁ : ℤ) + d₂ := by
        rw [abs_le]
        constructor <;> omega
      push_cast
      omega
    · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₂.le
      have h0 : (0 : ℝ) ≤ bondSupDist b b' := by positivity
      nlinarith
  · intro b φ
    classical
    obtain ⟨d₀, h₀⟩ := exists_offsetInBox b.1
    obtain ⟨p₀, hp₀⟩ : ∃ p : ℕ, ∀ x ∈ φ.support, OffsetInBox p x := by
      refine ⟨φ.support.sup fun x => Finset.univ.sup fun i => (x i).natAbs, fun x hx i => ?_⟩
      have h1 : (x i).natAbs ≤ Finset.univ.sup fun i => (x i).natAbs :=
        Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)
      have h2 : (Finset.univ.sup fun i => (x i).natAbs) ≤
          φ.support.sup fun x => Finset.univ.sup fun i => (x i).natAbs :=
        Finset.le_sup (f := fun x : Fin 4 → ℤ => Finset.univ.sup fun i => (x i).natAbs) hx
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h1.trans h2
    set gr : IntBond → ℝ := fun c => φ c.1 - φ (c.1 + Pi.single c.2 1) with hgr
    set sup₀ : Finset IntBond := (φ.support ∪ φ.support.biUnion fun x =>
      Finset.univ.image fun i : Fin 4 => x - Pi.single i 1) ×ˢ Finset.univ with hsup
    have hgrsup : ∀ c, gr c ≠ 0 → c ∈ sup₀ := by
      rintro ⟨x, i⟩ hne
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
      by_cases h1 : φ x = 0
      · have h2 : φ (x + Pi.single i 1) ≠ 0 := by
          intro h2
          apply hne
          simp [hgr, h1, h2]
        refine Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨x + Pi.single i 1, Finsupp.mem_support_iff.mpr h2, ?_⟩)
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp⟩
      · exact Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr h1)
    set gv : IntBond →₀ ℝ := Finsupp.onFinset sup₀ gr hgrsup with hgv
    have hgvapply : ∀ c, gv c = gr c := fun c => rfl
    have hbox : ∀ c ∈ gv.support, OffsetInBox (p₀ + 1) c.1 := by
      intro c hc
      have h1 := Finsupp.support_onFinset_subset hc
      have h2 := (Finset.mem_product.mp h1).1
      rcases Finset.mem_union.mp h2 with h3 | h3
      · exact offsetInBox_mono (by omega) (hp₀ _ h3)
      · obtain ⟨x, hx, h4⟩ := Finset.mem_biUnion.mp h3
        obtain ⟨i, -, h5⟩ := Finset.mem_image.mp h4
        rw [← h5]
        intro j
        have a := abs_le.mp (hp₀ x hx j)
        have b := abs_le.mp (offsetInBox_single i j)
        simp only [Pi.sub_apply]
        rw [abs_le]
        push_cast at a b ⊢
        constructor <;> omega
    set p := d₀ + p₀ + 1 with hp
    have hzero : ∀ᶠ R : ℕ in atTop,
        ∑ b' ∈ gv.support, cubeEntry Tb.coupling Tb.side k (2 * R) b b' * gv b' = 0 := by
      filter_upwards [eventually_ge_atTop (R₁ + p + 1024)] with R hR
      have : NeZero (16 * (2 * R + 1)) := neZeroCubeSide (2 * R)
      obtain ⟨-, -, hsym, -, -, hgrad, hent⟩ := hForm k (16 * (2 * R + 1)) (0 : TorusSite (16 * (2 * R + 1))) R
        (by omega) (by omega)
      have hsingle : ∀ c ∈ (Finsupp.single b (1 : ℝ)).support, OffsetInBox p c.1 := by
        intro c hc
        have := Finsupp.support_single_subset hc
        rw [Finset.mem_singleton] at this
        rw [this]
        exact offsetInBox_mono (by omega) h₀
      have hlift : latticeGrad (fun x : TorusSite (16 * (2 * R + 1)) => φ (centredCoords x) • imaginaryUnitI) =
          liftedForm gv := by
        funext c
        obtain ⟨x, i⟩ := c
        show φ (centredCoords x) • imaginaryUnitI - φ (centredCoords (x + unitStep _ i)) • imaginaryUnitI =
          gv (centredCoords x, i) • imaginaryUnitI
        rw [hgvapply, centredCoords_add_unitStep φ hp₀ (by omega)]
        exact (sub_smul _ _ _).symm
      have h1 := hgrad (fun x => φ (centredCoords x) • imaginaryUnitI) (liftedForm (Finsupp.single b 1))
      rw [hlift, hsym, form_liftedForm hent (Finsupp.single b 1) gv hsingle
        (fun c hc => offsetInBox_mono (by omega) (hbox c hc)) (by omega)] at h1
      rw [Finsupp.support_single _ one_ne_zero, Finset.sum_singleton] at h1
      refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) h1
      simp only [Finsupp.single_eq_same, one_mul]
      have e := cubeEntry_eq_boxEntry Tb.coupling Tb.side k (2 * R) b c
      rw [e]
      unfold boxEntry
      push_cast
      rfl
    have hlim : Tendsto (fun R : ℕ => ∑ b' ∈ gv.support, cubeEntry Tb.coupling Tb.side k (2 * R) b b' * gv b') atTop
        (𝓝 (∑ b' ∈ gv.support, Q b b' * gv b')) :=
      tendsto_finsetSum _ fun c _ =>
        ((hQ b c).comp (tendsto_id.const_mul_atTop' (by norm_num : (0 : ℕ) < 2))).mul_const _
    have hsum0 : ∑ b' ∈ gv.support, Q b b' * gv b' = 0 :=
      tendsto_nhds_unique (hlim.congr' hzero) tendsto_const_nhds
    have hs : HasSum (fun b' : IntBond => Q b b' * (φ b'.1 - φ (b'.1 + Pi.single b'.2 1)))
        (∑ b' ∈ gv.support, Q b b' * (φ b'.1 - φ (b'.1 + Pi.single b'.2 1))) :=
      hasSum_sum_of_ne_finset_zero (fun c hc => by
        have : gv c = 0 := by
          by_contra h
          exact hc (Finsupp.mem_support_iff.mpr h)
        rw [hgvapply] at this
        simp only [hgr] at this
        rw [this, mul_zero])
    have e2 : ∑ b' ∈ gv.support, Q b b' * (φ b'.1 - φ (b'.1 + Pi.single b'.2 1)) = 0 := by
      rw [← hsum0]
      exact Finset.sum_congr rfl fun c _ => rfl
    rwa [e2] at hs
  · intro v P hP
    classical
    obtain ⟨p₁, hp₁⟩ : ∃ p : ℕ, ∀ b ∈ v.support, OffsetInBox p b.1 := by
      refine ⟨v.support.sup fun b => Finset.univ.sup fun i => (b.1 i).natAbs, fun b hb i => ?_⟩
      have h1 : (b.1 i).natAbs ≤ Finset.univ.sup fun i => (b.1 i).natAbs :=
        Finset.le_sup (f := fun i => (b.1 i).natAbs) (Finset.mem_univ i)
      have h2 : (Finset.univ.sup fun i => (b.1 i).natAbs) ≤
          v.support.sup fun b => Finset.univ.sup fun i => (b.1 i).natAbs :=
        Finset.le_sup (f := fun b : IntBond => Finset.univ.sup fun i => (b.1 i).natAbs) hb
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h1.trans h2
    obtain ⟨p₂, hp₂⟩ : ∃ p : ℕ, ∀ π ∈ P, OffsetInBox p π.1 := by
      refine ⟨P.sup fun b => Finset.univ.sup fun i => (b.1 i).natAbs, fun b hb i => ?_⟩
      have h1 : (b.1 i).natAbs ≤ Finset.univ.sup fun i => (b.1 i).natAbs :=
        Finset.le_sup (f := fun i => (b.1 i).natAbs) (Finset.mem_univ i)
      have h2 : (Finset.univ.sup fun i => (b.1 i).natAbs) ≤ P.sup fun b => Finset.univ.sup fun i => (b.1 i).natAbs :=
        Finset.le_sup (f := fun b : (Fin 4 → ℤ) × Fin 4 × Fin 4 => Finset.univ.sup fun i => (b.1 i).natAbs) hb
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h1.trans h2
    set p := p₁ + p₂ + 4 with hp
    have hlim : Tendsto (fun R : ℕ => ∑ b ∈ v.support, ∑ b' ∈ v.support,
        v b * cubeEntry Tb.coupling Tb.side k (2 * R) b b' * v b')
        atTop (𝓝 (∑ b ∈ v.support, ∑ b' ∈ v.support, v b * Q b b' * v b')) :=
      tendsto_finsetSum _ fun b _ => tendsto_finsetSum _ fun c _ =>
        (((hQ b c).comp (tendsto_id.const_mul_atTop' (by norm_num : (0 : ℕ) < 2))).const_mul _).mul_const _
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (R₁ + p + 1024)] with R hR
    have : NeZero (16 * (2 * R + 1)) := neZeroCubeSide (2 * R)
    obtain ⟨-, -, -, -, hbounds, -, hent⟩ := hForm k (16 * (2 * R + 1)) (0 : TorusSite (16 * (2 * R + 1))) R
      (by omega) (by omega)
    have hv' : ∀ b ∈ v.support, OffsetInBox p b.1 := fun b hb => offsetInBox_mono (by omega) (hp₁ b hb)
    have h1 := (hbounds (liftedForm v)).1
    rw [form_liftedForm hent v v hv' hv' (by omega)] at h1
    have e1 : ∑ b ∈ v.support, ∑ b' ∈ v.support, v b * cubeEntry Tb.coupling Tb.side k (2 * R) b b' * v b' =
        ∑ b ∈ v.support, ∑ b' ∈ v.support, v b * mixedDeriv (actionAtLevel Tb.coupling Tb.side k
          (supBall (0 : TorusSite (16 * (2 * R + 1))) (2 * R))) (trivialField (16 * (2 * R + 1)))
          ![bondFrom 0 b, bondFrom 0 b'] ![imaginaryUnitI, imaginaryUnitI] * v b' := by
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
      rw [cubeEntry_eq_boxEntry]
      unfold boxEntry
      push_cast
      rfl
    rw [e1]
    refine le_trans ?_ h1
    refine mul_le_mul_of_nonneg_left ?_ (by linarith [hD.cK_pos])
    set ι : (Fin 4 → ℤ) × Fin 4 × Fin 4 → TorusPlaquette (16 * (2 * R + 1)) :=
      fun π => (siteOfInt π.1, π.2.1, π.2.2) with hι
    have hinj : Set.InjOn ι P := by
      rintro ⟨h, μ, ν⟩ h1 ⟨h', μ', ν'⟩ h2 he
      have e1 : (siteOfInt h : TorusSite (16 * (2 * R + 1))) = siteOfInt h' := congrArg Prod.fst he
      have e2 : (μ, ν) = (μ', ν') := congrArg Prod.snd he
      have c1 := centredCoords_siteOfInt (n := 16 * (2 * R + 1)) (hp₂ _ h1) (by omega)
      have c2 := centredCoords_siteOfInt (n := 16 * (2 * R + 1)) (hp₂ _ h2) (by omega)
      simp only at c1 c2
      rw [e1, c2] at c1
      rw [c1, e2]
    have hsub : P.image ι ⊆ plaquettesIn (supBall 0 (2 * (R : ℝ))) := by
      intro π hπ
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hπ
      have hb := hp₂ τ hτ
      refine mem_plaquettesIn.mpr ⟨hP τ hτ, fun w hw => ?_⟩
      have e2 : ((2 * R : ℕ) : ℝ) = 2 * (R : ℝ) := by push_cast; ring
      rw [← e2]
      have hsingle : ∀ {e : Fin 4 → ℤ} {q : ℕ} (μ : Fin 4), OffsetInBox q e →
          (siteOfInt e : TorusSite (16 * (2 * R + 1))) + unitStep _ μ = siteOfInt (e + Pi.single μ 1) ∧
            OffsetInBox (q + 1) (e + Pi.single μ 1) := by
        intro e q μ he
        exact ⟨by rw [siteOfInt_add, siteOfInt_single], offsetInBox_add he (offsetInBox_single μ)⟩
      have hin : ∀ {e : Fin 4 → ℤ}, OffsetInBox (p₂ + 2) e →
          (siteOfInt e : TorusSite (16 * (2 * R + 1))) ∈ supBall 0 ((2 * R : ℕ) : ℝ) := by
        intro e he
        have := add_mem_supBall (n := 16 * (2 * R + 1)) 0 (offsetInBox_mono (by omega : p₂ + 2 ≤ 2 * R) he)
        rwa [zero_add] at this
      obtain ⟨a1, a2⟩ := hsingle τ.2.1 hb
      obtain ⟨b1, b2⟩ := hsingle τ.2.2 hb
      obtain ⟨c1, c2⟩ := hsingle τ.2.2 a2
      simp only [plaquetteVertices, hι, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hin (offsetInBox_mono (by omega) hb)
      · rw [a1]
        exact hin (offsetInBox_mono (by omega) a2)
      · rw [b1]
        exact hin (offsetInBox_mono (by omega) b2)
      · rw [a1, c1]
        exact hin c2
    have hsq : ∀ π ∈ P, intCurl v π ^ 2 = ‖lieFormCurl (liftedForm v) (ι π)‖ ^ 2 := by
      intro π hπ
      obtain ⟨h, μ, ν⟩ := π
      have := lieFormCurl_liftedForm (n := 16 * (2 * R + 1)) v (hp₂ _ hπ) (by omega) μ ν
      show _ = ‖lieFormCurl (liftedForm v) (siteOfInt h, μ, ν)‖ ^ 2
      rw [this, norm_smul_unitI_sq]
    rw [Finset.sum_congr rfl hsq, ← Finset.sum_image (f := fun π => ‖lieFormCurl (liftedForm v) π‖ ^ 2) hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  · intro n _ o R hR hn b b' hb hb'
    have hR1 : 1024 ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
    have hR2 : R₂ ≤ R := le_trans (le_max_right _ _) hR
    have hmain := boxEntry_sub_limit_le hδ hC₁ hC₂ hB' hSp k hQ o hR1 hn hb hb'
    have e2 : ((2 * R : ℕ) : ℝ) = 2 * (R : ℝ) := by push_cast; ring
    rw [e2] at hmain
    refine hmain.trans ?_
    have hRr : (0 : ℝ) ≤ R := by positivity
    set K := C₁ * Real.exp δ + 2 * C₂ * Real.exp (2 * δ) with hK
    have hsmall := hR₂ R hR2
    have hm1 : (((R / 4 : ℕ) : ℝ) + 1) ^ 4 ≤ ((R : ℝ) + 1) ^ 4 := by
      have : ((R / 4 : ℕ) : ℝ) ≤ R := by exact_mod_cast Nat.div_le_self _ _
      exact pow_le_pow_left₀ (by positivity) (by linarith) 4
    have hq1 : (R : ℝ) ≤ 4 * ((R / 4 : ℕ) : ℝ) + 4 := by
      have : R ≤ 4 * (R / 4) + 4 := by omega
      exact_mod_cast this
    have hq2 : (R : ℝ) ≤ 16 * ((R / 16 - 1 : ℕ) : ℝ) + 32 := by
      have : R ≤ 16 * (R / 16 - 1) + 32 := by omega
      exact_mod_cast this
    have x1 : Real.exp (-δ * (R / 4 : ℕ) / 8) ≤ Real.exp δ * Real.exp (-(δ / 32) * R) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have x2 : Real.exp (-δ * (R / 16 - 1 : ℕ)) ≤ Real.exp (2 * δ) * Real.exp (-(δ / 32) * R) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have x3 : Real.exp (-(δ / 32) * R) = Real.exp (-(δ / 64) * R) * Real.exp (-(δ / 64 * R)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hp1 : (1 : ℝ) ≤ ((R : ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)
    set P4 := ((R : ℝ) + 1) ^ 4
    set e1 := Real.exp (-(δ / 64) * R)
    set e2' := Real.exp (-(δ / 64 * R))
    have he1 : 0 < e1 := Real.exp_pos _
    have he2 : 0 < e2' := Real.exp_pos _
    have hE1 : 0 < Real.exp δ := Real.exp_pos _
    have hE2 : 0 < Real.exp (2 * δ) := Real.exp_pos _
    rw [x3] at x1 x2
    have y1 : C₁ * (((R / 4 : ℕ) : ℝ) + 1) ^ 4 * Real.exp (-δ * (R / 4 : ℕ) / 8) ≤
        C₁ * P4 * (Real.exp δ * (e1 * e2')) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hm1 hC₁.le) x1 (Real.exp_pos _).le (by positivity)
    have y2 : 2 * C₂ * Real.exp (-δ * (R / 16 - 1 : ℕ)) ≤ 2 * C₂ * P4 * (Real.exp (2 * δ) * (e1 * e2')) := by
      have : 2 * C₂ ≤ 2 * C₂ * P4 := by nlinarith
      exact mul_le_mul this x2 (Real.exp_pos _).le (by positivity)
    have y3 : K * P4 * e1 * e2' ≤ 1 * e2' := mul_le_mul_of_nonneg_right hsmall.le he2.le
    have y4 : C₁ * P4 * (Real.exp δ * (e1 * e2')) + 2 * C₂ * P4 * (Real.exp (2 * δ) * (e1 * e2')) =
        K * P4 * e1 * e2' := by
      rw [hK]
      ring
    calc _ ≤ C₁ * P4 * (Real.exp δ * (e1 * e2')) + 2 * C₂ * P4 * (Real.exp (2 * δ) * (e1 * e2')) :=
          add_le_add y1 y2
      _ = K * P4 * e1 * e2' := y4
      _ ≤ 1 * e2' := y3
      _ = _ := one_mul _
end YangMills.Construction.LimitForms
end
