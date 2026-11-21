import YangMills.Construction.LawInAState.PlaquettesAtASiteProof
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.Lattice.StandardPartitionsAndLevelUnitsProof
import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPiecesProof
import YangMills.Construction.ResponseInTheExpansion.TheWeightsOfATupleAreLocal
import YangMills.Construction.Torus.CoveringMapOnSmallBallsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields BlockOffsets TorusLumps WeightedResponses TorusMetric TestFunctions PeriodicLattice
variable {L : ℕ} [NeZero L]
private theorem fineBlock_mem_form (hodd : Odd L) : (t n : ℕ) → [NeZero n] → (y : TorusSite n) →
    (c : TorusSite (fineSide L t n)) →
    c ∈ fineBlock L t n y → ∃ e : Fin 4 → ℤ, (∀ i, 2 * |e i| ≤ (L : ℤ) ^ t - 1) ∧
      c = siteOfInt fun i => (L : ℤ) ^ t * ((y i).cast : ℤ) + e i
  | 0, n, _, y, c, hc => by
    have hcy : c = y := Finset.mem_singleton.mp hc
    refine ⟨0, by simp, ?_⟩
    rw [hcy]
    funext i
    simp only [siteOfInt, pow_zero, one_mul, Pi.zero_apply, add_zero]
    exact (ZMod.intCast_zmod_cast (y i)).symm
  | t + 1, n, _, Y, c, hc => by
    obtain ⟨z, hz, hcz⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨e, he, hce⟩ := fineBlock_mem_form hodd t (n * L) z c hcz
    have hzY : parentBlock L z = Y := by simpa [sitesInBlocks] using hz
    obtain ⟨o, ho, hzo⟩ := exists_fineSite_of_parentBlock hodd Y z hzY
    have hoi := (mem_centredCube_iff o).1 ho
    have hL1 : (1 : ℤ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hQ : (0 : ℤ) < (L : ℤ) ^ t := by positivity
    refine ⟨fun i => (L : ℤ) ^ t * o i + e i, fun i => ?_, ?_⟩
    · obtain ⟨H, hH⟩ := hodd
      have hLH : ((L : ℤ) - 1) / 2 = (H : ℤ) := by subst hH; push_cast; omega
      have hLe : (L : ℤ) = 2 * H + 1 := by subst hH; push_cast; ring
      have h1 := hoi i
      rw [hLH] at h1
      have h2 : |o i| ≤ H := abs_le.mpr h1
      have h3 : |(L : ℤ) ^ t * o i + e i| ≤ (L : ℤ) ^ t * H + |e i| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        rw [abs_mul, abs_of_pos hQ]
        exact mul_le_mul_of_nonneg_left h2 hQ.le
      have h4 := he i
      have hq : (L : ℤ) ^ t * L = (L : ℤ) ^ t * (2 * H + 1) := by rw [← hLe]
      show 2 * |(L : ℤ) ^ t * o i + e i| ≤ (L : ℤ) ^ (t + 1) - 1
      rw [pow_succ]
      linarith [h3, h4, hq]
    · rw [hce]
      funext i
      simp only [siteOfInt]
      haveI hNL : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
      have hzi : z i = (((L : ℤ) * (((Y i).cast : ℤ) + 0) + o i : ℤ) : ZMod (n * L)) := by
        rw [hzo]
        rfl
      set a : ℤ := (L : ℤ) * (((Y i).cast : ℤ) + 0) + o i with ha
      have hk : ((z i).cast : ℤ) = a + ((n * L : ℕ) : ℤ) * (-(a / ((n * L : ℕ) : ℤ))) := by
        rw [hzi, ZMod.coe_intCast, Int.emod_def]
        ring
      have hM : ((((n * L : ℕ) : ℤ) * (L : ℤ) ^ t : ℤ) : ZMod (fineSide L t (n * L))) = 0 := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨1, ?_⟩
        rw [fineSide_eq]
        push_cast
        ring
      have hring : (L : ℤ) ^ t * ((z i).cast : ℤ) + e i =
          ((L : ℤ) ^ (t + 1) * ((Y i).cast : ℤ) + ((L : ℤ) ^ t * o i + e i)) +
            (((n * L : ℕ) : ℤ) * (L : ℤ) ^ t) * (-(a / ((n * L : ℕ) : ℤ))) := by
        rw [hk, ha]
        ring
      rw [hring, Int.cast_add, Int.cast_mul _ (-(a / ((n * L : ℕ) : ℤ))), hM, zero_mul, add_zero]
      rfl
private def axisCount (μ ν i : Fin 4) : ℤ := (if i = μ then 1 else 0) + (if i = ν then 1 else 0)
private theorem plaquetteVertex_form {m : ℕ} (x : TorusSite m) (μ ν : Fin 4) (hlt : μ < ν) (c : TorusSite m)
    (hc : c ∈ plaquetteVertices x μ ν) :
    ∃ ε : Fin 4 → ℤ, (∀ i, |axisCount μ ν i - 2 * ε i| ≤ 1) ∧ c = x + siteOfInt ε := by apply _root_.YangMills.DeltaSharedProofs.p500648 <;> assumption
private theorem torusProj_sub (S : ℝ) (u v : Fin 4 → ℝ) :
    torusProj S (u - v) = torusProj S u - torusProj S v := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
private theorem torusProj_surjective (S : ℝ) (x : Torus4 S) : ∃ v, torusProj S v = x := by apply _root_.YangMills.Construction.Weighted.DistBounds.torusProj_surjective <;> assumption
private theorem torusProj_eq_of_intShift {S : ℝ} {u v : Fin 4 → ℝ} (a : Fin 4 → ℤ)
    (h : ∀ i, u i = v i + a i * S) :
    torusProj S u = torusProj S v := by
  funext i
  show (u i : AddCircle S) = (v i : AddCircle S)
  rw [h i, AddCircle.coe_add]
  have : ((a i * S : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨a i, by simp⟩
  rw [this, add_zero]
private theorem exists_intShift_of_torusProj_eq {S : ℝ} {u v : Fin 4 → ℝ} (h : torusProj S u = torusProj S v) :
    ∃ a : Fin 4 → ℤ, ∀ i, u i = v i + a i * S := by apply _root_.YangMills.Construction.PeriodicLattice.PartitionFacts.exists_int_shift_of_torusProj_eq <;> assumption
private theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
private theorem torusEuclidNorm_le {S : ℝ} {x : Torus4 S} {v : Fin 4 → ℝ} (h : torusProj S v = x) :
    torusEuclidNorm x ≤ euclidNormVec v := by apply _root_.YangMills.Construction.TestFunctions.SmallBalls.torusEuclidNorm_le_of_proj_eq <;> assumption
private theorem euclidNormVec_le_of_abs_le {v : Fin 4 → ℝ} {b : ℝ} (hb : 0 ≤ b) (h : ∀ i, |v i| ≤ b) :
    euclidNormVec v ≤ 2 * b := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
private theorem abs_le_euclidNormVec (v : Fin 4 → ℝ) (i : Fin 4) : |v i| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem abs_sub_le_lipConstTorus_mul {ℓ : ℝ} {f : Torus4 ℓ → ℝ} (hl : IsLipschitzFor euclidDistTorus f)
    (x y : Torus4 ℓ) (hd : 0 ≤ euclidDistTorus x y) :
    |f x - f y| ≤ lipConstTorus f * euclidDistTorus x y := by
  obtain ⟨C₀, hC₀, h₀⟩ := hl
  have hne : {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * euclidDistTorus x y}.Nonempty := ⟨C₀, hC₀, h₀⟩
  by_cases h0 : euclidDistTorus x y = 0
  · have := h₀ x y
    rw [h0, mul_zero, Real.norm_eq_abs] at this
    rw [h0, mul_zero]
    exact this
  · have hp : 0 < euclidDistTorus x y := lt_of_le_of_ne hd (Ne.symm h0)
    rw [← div_le_iff₀ hp]
    refine le_csInf hne fun C hC => ?_
    rw [div_le_iff₀ hp]
    exact hC.2 x y
private def barycenterLift (k : ℕ) {S : ℕ} (p : TorusPlaquette S) : Fin 4 → ℝ := fun i =>
  (((p.1 i).val : ℝ) + (if i = p.2.1 then 1 / 2 else 0) + (if i = p.2.2 then 1 / 2 else 0)) / (L : ℝ) ^ k
private theorem plaquetteBarycenterAt_eq (k m : ℕ) (p : TorusPlaquette (fineSide L k (2 * L ^ m))) :
    plaquetteBarycenterAt L k m p = torusProj (PeriodicLattice.torusSide L m) (barycenterLift (L := L) k p) := rfl
private theorem natAbs_valMinAbs_le_abs {S : ℕ} [NeZero S] (a : ZMod S) (W : ℤ) (h : (W : ZMod S) = a) :
    (a.valMinAbs.natAbs : ℤ) ≤ |W| := by
  have h1 := ZMod.natAbs_min_of_le_div_two S a.valMinAbs W (by rw [ZMod.coe_valMinAbs, h])
    (ZMod.natAbs_valMinAbs_le a)
  have : (W.natAbs : ℤ) = |W| := Int.natCast_natAbs W
  rw [← this]
  exact_mod_cast h1
private theorem abs_le_one_of_uniformNorm_eq_one {X : Type} {f : X → ℝ} (h1 : uniformNorm f = 1) (x : X) :
    |f x| ≤ 1 := by
  have hb : BddAbove (Set.range fun x => ‖f x‖) := by
    by_contra hn
    have := Real.iSup_of_not_bddAbove hn
    unfold uniformNorm at h1
    rw [this] at h1
    norm_num at h1
  have := le_ciSup hb x
  unfold uniformNorm at h1
  rw [h1] at this
  simpa using this
abbrev _root_.YangMills.SharedProofs.p64038 := @abs_le_one_of_uniformNorm_eq_one
private theorem exists_ne_zero_of_uniformNorm_eq_one {X : Type} {f : X → ℝ} (h1 : uniformNorm f = 1) :
    ∃ x, f x ≠ 0 := by
  by_contra hn
  push_neg at hn
  unfold uniformNorm at h1
  simp [hn] at h1
abbrev _root_.YangMills.SharedProofs.p97669 := @exists_ne_zero_of_uniformNorm_eq_one
private theorem dist_barycenter_le (k m : ℕ) [NeZero (2 * L ^ m)] (p p' : TorusPlaquette (fineSide L k (2 * L ^ m))) :
    euclidDistTorus (plaquetteBarycenterAt L k m p) (plaquetteBarycenterAt L k m p') ≤ 2 * barycentreDist L k p p' := by
  have hL0 : (0 : ℝ) < (L : ℝ) ^ k := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  set S := PeriodicLattice.torusSide L m with hS
  set u : Fin 4 → ℤ := fun i => ((doubledBarycentre p i - doubledBarycentre p' i).valMinAbs) with hu
  set v : Fin 4 → ℝ := fun i => (u i : ℝ) / (2 * (L : ℝ) ^ k) with hv
  have hlift : torusProj S v = plaquetteBarycenterAt L k m p - plaquetteBarycenterAt L k m p' := by
    rw [plaquetteBarycenterAt_eq, plaquetteBarycenterAt_eq, ← torusProj_sub]
    have hm : ∀ i, ∃ a : ℤ, (u i : ℤ) =
        (2 * ((p.1 i).val : ℤ) + axisCount p.2.1 p.2.2 i) - (2 * ((p'.1 i).val : ℤ) + axisCount p'.2.1 p'.2.2 i) +
          a * (2 * (fineSide L k (2 * L ^ m) : ℤ)) := by
      intro i
      have h1 : ((u i : ℤ) : ZMod (2 * fineSide L k (2 * L ^ m))) = doubledBarycentre p i - doubledBarycentre p' i :=
        ZMod.coe_valMinAbs _
      have h2 : ∀ r : TorusPlaquette (fineSide L k (2 * L ^ m)), doubledBarycentre r i =
          (((2 * ((r.1 i).val : ℤ) + axisCount r.2.1 r.2.2 i : ℤ)) : ZMod (2 * fineSide L k (2 * L ^ m))) := by
        intro r
        simp only [doubledBarycentre, axisCount]
        push_cast
        split_ifs <;> simp <;> ring
      rw [h2 p, h2 p', ← Int.cast_sub, ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
      obtain ⟨a, ha⟩ := h1
      refine ⟨-a, ?_⟩
      push_cast at ha ⊢
      linarith
    choose a ha using hm
    refine torusProj_eq_of_intShift a fun i => ?_
    have h3 : ((fineSide L k (2 * L ^ m) : ℕ) : ℝ) = S * (L : ℝ) ^ k := by
      rw [fineSide_eq, hS]
      simp [PeriodicLattice.torusSide]
    have h4 := ha i
    have h5 : (u i : ℝ) = (2 * ((p.1 i).val : ℝ) + (axisCount p.2.1 p.2.2 i : ℝ)) -
        (2 * ((p'.1 i).val : ℝ) + (axisCount p'.2.1 p'.2.2 i : ℝ)) + (a i : ℝ) * (2 * (S * (L : ℝ) ^ k)) := by
      rw [h4, ← h3]
      push_cast
      ring
    have hd : ∀ (μ ν : Fin 4), ((axisCount μ ν i : ℤ) : ℝ) / 2 =
        (if i = μ then 1 / 2 else 0) + (if i = ν then 1 / 2 else 0) := by
      intro μ ν
      simp only [axisCount]
      split_ifs <;> norm_num
    simp only [hv, barycenterLift, Pi.sub_apply]
    have f1 : ((p.1 i).val : ℝ) + (if i = p.2.1 then 1 / 2 else 0) + (if i = p.2.2 then 1 / 2 else 0) =
        ((p.1 i).val : ℝ) + ((axisCount p.2.1 p.2.2 i : ℤ) : ℝ) / 2 := by
      rw [hd]
      ring
    have f2 : ((p'.1 i).val : ℝ) + (if i = p'.2.1 then 1 / 2 else 0) + (if i = p'.2.2 then 1 / 2 else 0) =
        ((p'.1 i).val : ℝ) + ((axisCount p'.2.1 p'.2.2 i : ℤ) : ℝ) / 2 := by
      rw [hd]
      ring
    rw [f1, f2, h5]
    field_simp
  have hsup : ∀ i, |v i| ≤ barycentreDist L k p p' := by
    intro i
    have h1 : (u i).natAbs ≤ supDist (doubledBarycentre p) (doubledBarycentre p') :=
      Finset.le_sup (f := fun i => ((doubledBarycentre p i - doubledBarycentre p' i).valMinAbs).natAbs)
        (Finset.mem_univ i)
    have h2 : |(u i : ℝ)| ≤ (supDist (doubledBarycentre p) (doubledBarycentre p') : ℝ) := by
      have : ((u i).natAbs : ℝ) = |(u i : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [← this]
      exact_mod_cast h1
    unfold barycentreDist
    simp only [hv]
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 * (L : ℝ) ^ k by positivity)]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  have hb0 : 0 ≤ barycentreDist L k p p' := (abs_nonneg _).trans (hsup 0)
  calc euclidDistTorus (plaquetteBarycenterAt L k m p) (plaquetteBarycenterAt L k m p')
      ≤ euclidNormVec v := torusEuclidNorm_le hlift
    _ ≤ 2 * barycentreDist L k p p' := euclidNormVec_le_of_abs_le hb0 hsup
private theorem mem_supBall_of_dist_le (hodd : Odd L) (k m : ℕ) [NeZero (2 * L ^ m)] {n : ℝ} (hn : 1 ≤ n)
    (v₀ : Fin 4 → ℝ) (p : TorusPlaquette (fineSide L k (2 * L ^ m))) (z : TorusSite (2 * L ^ m))
    (hat : IsPlaquetteAt L k z p)
    (hd : euclidDistTorus (torusProj (PeriodicLattice.torusSide L m) v₀) (plaquetteBarycenterAt L k m p) ≤ 10 * n) :
    z ∈ supBall (fun i => (((round (v₀ i) : ℤ)) : ZMod (2 * L ^ m))) (12 * n) := by
  set S := PeriodicLattice.torusSide L m with hS
  have hSN : S = ((2 * L ^ m : ℕ) : ℝ) := by
    simp [hS, PeriodicLattice.torusSide]
  have hLpos : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL0 : (0 : ℝ) < (L : ℝ) ^ k := by positivity
  obtain ⟨D, hD1, hD2⟩ : ∃ D : Fin 4 → ℝ, torusProj S D = torusProj S v₀ - plaquetteBarycenterAt L k m p ∧
      euclidNormVec D < 10 * n + 1 / 2 := by
    have hne : (euclidNormVec '' (torusProj S ⁻¹' {torusProj S v₀ - plaquetteBarycenterAt L k m p})).Nonempty := by
      obtain ⟨v, hv⟩ := torusProj_surjective S (torusProj S v₀ - plaquetteBarycenterAt L k m p)
      exact ⟨_, v, hv, rfl⟩
    have hlt : sInf (euclidNormVec '' (torusProj S ⁻¹' {torusProj S v₀ - plaquetteBarycenterAt L k m p})) <
        10 * n + 1 / 2 := by
      have : torusEuclidNorm (torusProj S v₀ - plaquetteBarycenterAt L k m p) ≤ 10 * n := hd
      unfold torusEuclidNorm at this
      linarith
    obtain ⟨_, ⟨D, hD, rfl⟩, h2⟩ := exists_lt_of_csInf_lt hne hlt
    exact ⟨D, hD, h2⟩
  rw [plaquetteBarycenterAt_eq, ← torusProj_sub] at hD1
  obtain ⟨a, ha⟩ := exists_intShift_of_torusProj_eq hD1
  obtain ⟨hlt, c, hc, hcz⟩ := hat
  obtain ⟨e, he, hce⟩ := fineBlock_mem_form hodd k (2 * L ^ m) z c hcz
  obtain ⟨ε, hε, hcε⟩ := plaquetteVertex_form p.1 p.2.1 p.2.2 hlt c hc
  have hbound : ∀ i, ((z i - (((round (v₀ i) : ℤ)) : ZMod (2 * L ^ m))).valMinAbs.natAbs : ℝ) ≤ 12 * n := by
    intro i
    set z₀ : ℤ := ((z i).cast : ℤ) with hz₀
    set vi : ℤ := (L : ℤ) ^ k * z₀ + e i - ε i with hvi
    have hp : (((vi : ℤ)) : ZMod (fineSide L k (2 * L ^ m))) = p.1 i := by
      have h1 : c i = (((L : ℤ) ^ k * z₀ + e i : ℤ) : ZMod (fineSide L k (2 * L ^ m))) := congrFun hce i
      have h2 : c i = p.1 i + ((ε i : ℤ) : ZMod (fineSide L k (2 * L ^ m))) := congrFun hcε i
      rw [hvi, Int.cast_sub, ← h1, h2]
      ring
    have hval : ((p.1 i).val : ℤ) = vi % (fineSide L k (2 * L ^ m) : ℤ) := by
      rw [← hp]
      exact ZMod.val_intCast vi
    set b : ℤ := -(vi / (fineSide L k (2 * L ^ m) : ℤ)) with hb
    have hvb : ((p.1 i).val : ℤ) = vi + (fineSide L k (2 * L ^ m) : ℤ) * b := by
      rw [hval, Int.emod_def, hb]
      ring
    have hfine : ((fineSide L k (2 * L ^ m) : ℕ) : ℝ) = S * (L : ℝ) ^ k := by
      rw [fineSide_eq, hSN]
      push_cast
      ring
    have hvbR : ((p.1 i).val : ℝ) = (vi : ℝ) + S * (L : ℝ) ^ k * b := by
      have := congrArg (fun t : ℤ => (t : ℝ)) hvb
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at this
      rw [this, hfine]
    set θ : ℝ := ((e i : ℝ) + ((axisCount p.2.1 p.2.2 i : ℝ) - 2 * (ε i : ℝ)) / 2) / (L : ℝ) ^ k with hθ
    have hdel : (if i = p.2.1 then (1 / 2 : ℝ) else 0) + (if i = p.2.2 then 1 / 2 else 0) =
        ((axisCount p.2.1 p.2.2 i : ℤ) : ℝ) / 2 := by
      simp only [axisCount]
      split_ifs <;> norm_num
    have hw : barycenterLift (L := L) k p i = (z₀ : ℝ) + θ + S * b := by
      simp only [barycenterLift]
      rw [add_assoc, hdel, hvbR, hθ, hvi]
      push_cast
      field_simp
      ring
    have hθb : |θ| ≤ 1 / 2 := by
      have h1 : 2 * |(e i : ℝ)| ≤ (L : ℝ) ^ k - 1 := by
        have := he i
        exact_mod_cast this
      have h2 : |((axisCount p.2.1 p.2.2 i : ℝ) - 2 * (ε i : ℝ))| ≤ 1 := by
        have := hε i
        exact_mod_cast this
      have h3 : |(e i : ℝ) + ((axisCount p.2.1 p.2.2 i : ℝ) - 2 * (ε i : ℝ)) / 2| ≤ (L : ℝ) ^ k / 2 := by
        have := abs_add_le (e i : ℝ) (((axisCount p.2.1 p.2.2 i : ℝ) - 2 * (ε i : ℝ)) / 2)
        rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] at this
        linarith
      rw [hθ, abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
      linarith
    set o₀ : ℤ := round (v₀ i) with ho₀
    have hρ : |v₀ i - (o₀ : ℝ)| ≤ 1 / 2 := abs_sub_round (v₀ i)
    set W : ℤ := z₀ - o₀ + (2 * (L : ℤ) ^ m) * (b - a i) with hW
    have hWD : (W : ℝ) = -D i - θ + (v₀ i - o₀) := by
      have h1 := ha i
      simp only [Pi.sub_apply] at h1
      rw [hw] at h1
      rw [hW]
      push_cast
      have hS2 : (2 * (L : ℝ) ^ m) = S := by simp [hS, PeriodicLattice.torusSide]
      rw [hS2, h1]
      ring
    have hWb : |(W : ℝ)| ≤ 10 * n + 3 / 2 := by
      have h1 : |D i| ≤ euclidNormVec D := abs_le_euclidNormVec D i
      rw [hWD]
      have h2 := abs_add_three (-D i) (-θ) (v₀ i - o₀)
      rw [abs_neg, abs_neg] at h2
      have e2 : -D i + -θ + (v₀ i - o₀) = -D i - θ + (v₀ i - o₀) := by ring
      rw [e2] at h2
      linarith
    have hWc : (W : ZMod (2 * L ^ m)) = z i - ((o₀ : ℤ) : ZMod (2 * L ^ m)) := by
      have h0 : ((2 * (L : ℤ) ^ m : ℤ) : ZMod (2 * L ^ m)) = 0 := by
        have : ((2 * L ^ m : ℕ) : ZMod (2 * L ^ m)) = 0 := ZMod.natCast_self _
        rw [← this]
        push_cast
        rfl
      rw [hW, Int.cast_add, Int.cast_mul, h0, zero_mul, add_zero, Int.cast_sub, hz₀, ZMod.intCast_zmod_cast]
    have h5 := natAbs_valMinAbs_le_abs _ W hWc
    have h6 : (((z i - (((round (v₀ i) : ℤ)) : ZMod (2 * L ^ m))).valMinAbs.natAbs : ℤ) : ℝ) ≤ |(W : ℝ)| := by
      have := (Int.cast_le (R := ℝ)).2 h5
      simpa using this
    have h7 : (((z i - (((round (v₀ i) : ℤ)) : ZMod (2 * L ^ m))).valMinAbs.natAbs : ℤ) : ℝ) =
        ((z i - (((round (v₀ i) : ℤ)) : ZMod (2 * L ^ m))).valMinAbs.natAbs : ℝ) := Int.cast_natCast _
    rw [← h7]
    linarith
  have hfl : ∀ i, (z i - (((round (v₀ i) : ℤ)) : ZMod (2 * L ^ m))).valMinAbs.natAbs ≤ ⌊12 * n⌋₊ :=
    fun i => Nat.le_floor (hbound i)
  have htd : supDist z (fun i => (((round (v₀ i) : ℤ)) : ZMod (2 * L ^ m))) ≤ ⌊12 * n⌋₊ :=
    Finset.sup_le fun i _ => hfl i
  have h12 : (0 : ℝ) ≤ 12 * n := by linarith
  unfold supBall
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  calc (supDist z (fun i => (((round (v₀ i) : ℤ)) : ZMod (2 * L ^ m))) : ℝ) ≤ (⌊12 * n⌋₊ : ℝ) := by
        exact_mod_cast htd
    _ ≤ 12 * n := Nat.floor_le h12
theorem testWeightsLocal : testWeightsLocalStatement := by
  intro ℓ hodd m k q n vt f hn hvt hT
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · refine Real.iSup_le (fun p => ?_) (by norm_num)
    exact abs_le_one_of_uniformNorm_eq_one (hT.uniformNorm_eq i) _
  · refine Real.iSup_le (fun pp => ?_) (by positivity)
    set d := barycentreDist ℓ.side k pp.1.1 pp.2.1 with hd
    have hd0 : 0 ≤ d := by
      unfold barycentreDist at hd
      rw [hd]
      positivity
    by_cases h0 : d = 0
    · rw [h0, div_zero]
      positivity
    · have hp : 0 < d := lt_of_le_of_ne hd0 (Ne.symm h0)
      rw [div_le_iff₀ hp]
      have h1 := dist_barycenter_le (L := ℓ.side) k m pp.1.1 pp.2.1
      have hdist0 : 0 ≤ euclidDistTorus (plaquetteBarycenterAt ℓ.side k m pp.1.1)
          (plaquetteBarycenterAt ℓ.side k m pp.2.1) := by
        refine le_csInf ?_ ?_
        · obtain ⟨v, hv⟩ := torusProj_surjective _
            (plaquetteBarycenterAt ℓ.side k m pp.1.1 - plaquetteBarycenterAt ℓ.side k m pp.2.1)
          exact ⟨_, v, hv, rfl⟩
        · rintro _ ⟨w, _, rfl⟩
          exact euclidNormVec_nonneg w
      have h2 := abs_sub_le_lipConstTorus_mul (hT.lipschitz i) _ _ hdist0
      have h3 := hT.lipConst_le i
      have h4 : 0 ≤ 1 / (vt * n) := by positivity
      have h5 : lipConstTorus (f i) * euclidDistTorus (plaquetteBarycenterAt ℓ.side k m pp.1.1)
          (plaquetteBarycenterAt ℓ.side k m pp.2.1) ≤ 1 / (vt * n) * (2 * d) :=
        mul_le_mul h3 h1 hdist0 h4
      show |f i (plaquetteBarycenterAt ℓ.side k m pp.1.1) - f i (plaquetteBarycenterAt ℓ.side k m pp.2.1)| ≤
        2 / (vt * n) * d
      have e : 1 / (vt * n) * (2 * d) = 2 / (vt * n) * d := by ring
      linarith
  · obtain ⟨x₀, hx₀⟩ := exists_ne_zero_of_uniformNorm_eq_one (hT.uniformNorm_eq 0)
    obtain ⟨v₀, hv₀⟩ := torusProj_surjective _ x₀
    refine ⟨fun i => (((round (v₀ i) : ℤ)) : ZMod (2 * ℓ.side ^ m)), fun i z p hz hat => ?_⟩
    by_contra hne
    refine hz (mem_supBall_of_dist_le hodd k m hn v₀ p z hat ?_)
    rw [hv₀]
    refine hT.dist_le 0 i x₀ (subset_tsupport _ ?_) _ (subset_tsupport _ ?_)
    · exact hx₀
    · exact hne
end YangMills.Construction.ResponseInTheExpansion
end
