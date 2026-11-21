import YangMills.Construction.LawInAState.PlaquettesAtASiteProof
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.FourPointCondition.RiemannSumOfTheBareTracesProof
import YangMills.Construction.Lattice.StandardPartitionCubeGeometryArgument
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPiecesProof
import YangMills.Construction.ResponseInTheExpansion.SitesAroundASite
import YangMills.Construction.ResponseInTheExpansion.SitesOfATuple
import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsInTheFineCaseProof
import YangMills.Construction.SystemOfAdmissibleConstants.TentsOfASmallSideProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction
open WeightedResponses TorusFields TorusLumps BlockOffsets TorusMetric TestFunctions LinearResponse PeriodicLattice
namespace ResponseInTheExpansion
variable {L : ℕ} [NeZero L]
private theorem mem_fineBlock_form (hodd : Odd L) : (t n : ℕ) → [NeZero n] → (y : TorusSite n) →
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
    obtain ⟨e, he, hce⟩ := mem_fineBlock_form hodd t (n * L) z c hcz
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
private def plaquetteDirCount (μ ν i : Fin 4) : ℤ := (if i = μ then 1 else 0) + (if i = ν then 1 else 0)
private theorem mem_plaquetteVertices_form {m : ℕ} (x : TorusSite m) (μ ν : Fin 4) (hlt : μ < ν)
    (c : TorusSite m) (hc : c ∈ plaquetteVertices x μ ν) :
    ∃ ε : Fin 4 → ℤ, (∀ i, |plaquetteDirCount μ ν i - 2 * ε i| ≤ 1) ∧ c = x + siteOfInt ε := by apply _root_.YangMills.DeltaSharedProofs.p500648 <;> assumption
private theorem addCircle_coe_add_int_mul (S x : ℝ) (κ : ℤ) :
    ((x + κ * S : ℝ) : AddCircle S) = (x : AddCircle S) := by apply _root_.YangMills.Construction.PeriodicLattice.StandardCubes.coe_add_int_mul_period <;> assumption
private theorem barycenter_near_site (hodd : Odd L) {k m : ℕ} (y : TorusSite (2 * L ^ m))
    (p : TorusPlaquette (fineSide L k (2 * L ^ m)))
    (hp : IsPlaquetteAt L k y p) : ∃ e : Fin 4 → ℝ, (∀ μ, |e μ| ≤ 1) ∧
      plaquetteBarycenterAt L k m p = torusProj (torusSide L m) (fun μ => ((y μ).val : ℝ) + e μ) := by
  obtain ⟨hlt, c, hc, hcy⟩ := hp
  obtain ⟨e, he, hce⟩ := mem_fineBlock_form hodd k (2 * L ^ m) y c hcy
  obtain ⟨ε, hε, hcε⟩ := mem_plaquetteVertices_form p.1 p.2.1 p.2.2 hlt c hc
  have hLk : (0 : ℝ) < (L : ℝ) ^ k := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  refine ⟨fun μ => (((e μ : ℤ) : ℝ) - (ε μ : ℤ) + (plaquetteDirCount p.2.1 p.2.2 μ : ℤ) / 2) / (L : ℝ) ^ k,
    fun μ => ?_, ?_⟩
  · rw [abs_div, abs_of_pos hLk, div_le_one hLk]
    have h1 : 2 * |((e μ : ℤ) : ℝ)| ≤ (L : ℝ) ^ k - 1 := by
      have := he μ
      have h2 : ((2 * |e μ| : ℤ) : ℝ) ≤ (((L : ℤ) ^ k - 1 : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at h2
      exact h2
    have h3 : |((plaquetteDirCount p.2.1 p.2.2 μ : ℤ) : ℝ) - 2 * ((ε μ : ℤ) : ℝ)| ≤ 1 := by
      have := hε μ
      have h2 : ((|plaquetteDirCount p.2.1 p.2.2 μ - 2 * ε μ| : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by
        exact_mod_cast this
      push_cast at h2
      exact h2
    have hs : ((e μ : ℤ) : ℝ) - (ε μ : ℤ) + (plaquetteDirCount p.2.1 p.2.2 μ : ℤ) / 2 =
        ((e μ : ℤ) : ℝ) + (((plaquetteDirCount p.2.1 p.2.2 μ : ℤ) : ℝ) - 2 * ((ε μ : ℤ) : ℝ)) / 2 := by ring
    rw [hs]
    calc _ ≤ |((e μ : ℤ) : ℝ)| +
          |(((plaquetteDirCount p.2.1 p.2.2 μ : ℤ) : ℝ) - 2 * ((ε μ : ℤ) : ℝ)) / 2| := abs_add_le _ _
      _ ≤ ((L : ℝ) ^ k - 1) / 2 + 1 / 2 := by
        refine add_le_add (by linarith) ?_
        rw [abs_div, abs_two]
        linarith
      _ ≤ (L : ℝ) ^ k := by linarith
  · funext i
    have hpi : p.1 i = (((L : ℤ) ^ k * ((y i).cast : ℤ) + e i - ε i : ℤ) : ZMod (fineSide L k (2 * L ^ m))) := by
      have h1 := congrFun hce i
      have h2 := congrFun hcε i
      simp only [siteOfInt, Pi.add_apply] at h1 h2
      have h3 : p.1 i = c i - ((ε i : ℤ) : ZMod (fineSide L k (2 * L ^ m))) := eq_sub_of_add_eq h2.symm
      rw [h3, h1, ← Int.cast_sub]
    set a : ℤ := (L : ℤ) ^ k * ((y i).cast : ℤ) + e i - ε i with ha
    have hval : ((p.1 i).val : ℤ) =
        a - ((fineSide L k (2 * L ^ m)) : ℤ) * (a / ((fineSide L k (2 * L ^ m)) : ℤ)) := by
      rw [hpi, ZMod.val_intCast, Int.emod_def]
    have hvalR : ((p.1 i).val : ℝ) =
        (a : ℝ) - ((fineSide L k (2 * L ^ m)) : ℝ) * ((a / ((fineSide L k (2 * L ^ m)) : ℤ) : ℤ) : ℝ) := by
      have : (((p.1 i).val : ℤ) : ℝ) =
          ((a - ((fineSide L k (2 * L ^ m)) : ℤ) * (a / ((fineSide L k (2 * L ^ m)) : ℤ)) : ℤ) : ℝ) := by
        rw [hval]
      push_cast at this
      exact_mod_cast this
    have hyc : (((y i).cast : ℤ) : ℝ) = ((y i).val : ℝ) := by
      have : ((y i).cast : ℤ) = ((y i).val : ℤ) := (ZMod.natCast_val _).symm
      rw [this]
      push_cast
      rfl
    have hMr : ((fineSide L k (2 * L ^ m)) : ℝ) = torusSide L m * (L : ℝ) ^ k := by
      rw [fineSide_eq]
      simp only [torusSide]
      push_cast
      ring
    have hdel : ((plaquetteDirCount p.2.1 p.2.2 i : ℤ) : ℝ) / 2 =
        (if i = p.2.1 then 1 / 2 else 0) + (if i = p.2.2 then 1 / 2 else 0) := by
      simp only [plaquetteDirCount]
      split_ifs <;> norm_num
    simp only [plaquetteBarycenterAt, torusProj]
    have hfin : (((p.1 i).val : ℝ) + (if i = p.2.1 then 1 / 2 else 0) + (if i = p.2.2 then 1 / 2 else 0)) /
          (L : ℝ) ^ k =
        (((y i).val : ℝ) + (((e i : ℤ) : ℝ) - (ε i : ℤ) + (plaquetteDirCount p.2.1 p.2.2 i : ℤ) / 2) / (L : ℝ) ^ k) +
          ((-(a / ((fineSide L k (2 * L ^ m)) : ℤ)) : ℤ) : ℝ) * torusSide L m := by
      rw [hvalR, hMr, hdel, ha]
      push_cast
      rw [hyc]
      field_simp
      ring
    rw [hfin, addCircle_coe_add_int_mul]
private theorem addCircle_norm_coe_le (S x : ℝ) : ‖(x : AddCircle S)‖ ≤ |x| := by apply _root_.YangMills.Construction.TorusMetric.addCircle_norm_coe_le_abs <;> assumption
private theorem euclidNormVec_le (w : Fin 4 → ℝ) (b : ℝ) (hb : 0 ≤ b) (h : ∀ μ, |w μ| ≤ b) :
    euclidNormVec w ≤ 2 * b := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
private theorem torusEuclidNorm_nonneg {S : ℝ} (x : Torus4 S) : 0 ≤ torusEuclidNorm x := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
private theorem torusEuclidNorm_torusProj_le {S : ℝ} (w : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj S w) ≤ euclidNormVec w := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
private theorem norm_apply_le_torusEuclidNorm {S : ℝ} (x : Torus4 S) (μ : Fin 4) : ‖x μ‖ ≤ torusEuclidNorm x := by apply _root_.YangMills.SharedProofs.p28925 <;> assumption
private theorem torusProj_sub {S : ℝ} (a b : Fin 4 → ℝ) : torusProj S a - torusProj S b = torusProj S (a - b) := by apply _root_.YangMills.SharedProofs.p13492 <;> assumption
private theorem abs_sub_le_lipConstTorus_mul {S : ℝ} (f : Torus4 S → ℝ) (hf : IsLipschitzFor euclidDistTorus f)
    (x y : Torus4 S) : |f x - f y| ≤ lipConstTorus f * euclidDistTorus x y := by apply _root_.YangMills.SharedProofs.p26625 <;> assumption
private theorem abs_torusDisplacement_eq_norm (N : ℕ) (S : ℝ) (hS : S = N) (z z' : TorusSite N) (μ : Fin 4) :
    |torusDisplacement z z' μ| = ‖((((z' μ).val : ℝ) - (z μ).val : ℝ) : AddCircle S)‖ := by
  rw [AddCircle.norm_eq, hS]
  simp only [torusDisplacement, circleSub]
  rw [div_eq_inv_mul, mul_comm (N : ℝ)]
private theorem abs_blockMean_sub_le (hM : BlockMeanIsLinearAndLocal) (hW : WeightsCloseToBlockMeans)
    (hodd : Odd L) (t n : ℕ) [NeZero n] (y : TorusSite n) (h : PlaquetteWeight (fineSide L t n)) (c b : ℝ)
    (hb : 0 ≤ b) (hh : ∀ p, IsPlaquetteAt L t y p → |h p - c| ≤ b) : |blockMean L t n y h - c| ≤ b := by apply _root_.YangMills.SharedProofs.p64490 <;> assumption
theorem tupleSupportSitesStatement_holds (hM : BlockMeanIsLinearAndLocal) (hW : WeightsCloseToBlockMeans)
    (hSites : ExpDecaySumAndBallCard) : tupleSupportSitesStatement := by
  intro ℓ hodd k m p n vt f hvt hn hside hf
  classical
  have hSN : torusSide ℓ.side m = ((2 * ℓ.side ^ m : ℕ) : ℝ) := by
    simp only [torusSide]
    push_cast
    ring
  let pt : TorusSite (2 * ℓ.side ^ m) → Fin 4 → ℝ := fun z μ => ((z μ).val : ℝ)
  let D : Fin p → Finset (TorusSite (2 * ℓ.side ^ m)) := fun i => Finset.univ.filter fun z =>
    ∃ e : Fin 4 → ℝ, (∀ μ, |e μ| ≤ 1) ∧ torusProj (torusSide ℓ.side m) (pt z + e) ∈ tsupport (f i)
  have hDmem : ∀ i z, z ∈ D i ↔ ∃ e : Fin 4 → ℝ, (∀ μ, |e μ| ≤ 1) ∧
      torusProj (torusSide ℓ.side m) (pt z + e) ∈ tsupport (f i) := fun i z => by simp [D]
  have hf1 : ∀ i x, |f i x| ≤ 1 := by
    intro i x
    have h1 := hf.uniformNorm_eq i
    simp only [uniformNorm] at h1
    have hb : BddAbove (Set.range fun x => ‖f i x‖) := by
      by_contra h
      rw [Real.iSup_of_not_bddAbove h] at h1
      exact zero_ne_one h1
    have := le_ciSup hb x
    rw [h1] at this
    simpa using this
  have hupper : ∀ i j, ∀ z ∈ D i, ∀ z' ∈ D j, ∀ μ, |torusDisplacement z z' μ| ≤ 10 * n + 2 := by
    intro i j z hz z' hz' μ
    obtain ⟨e, he, hP⟩ := (hDmem i z).1 hz
    obtain ⟨e', he', hP'⟩ := (hDmem j z').1 hz'
    have h1 := hf.dist_le i j _ hP _ hP'
    have h2 : ‖(torusProj (torusSide ℓ.side m) (pt z + e) - torusProj (torusSide ℓ.side m) (pt z' + e')) μ‖ ≤
        10 * n :=
      (norm_apply_le_torusEuclidNorm _ μ).trans h1
    rw [abs_torusDisplacement_eq_norm _ _ hSN]
    set W := (torusProj (torusSide ℓ.side m) (pt z + e) - torusProj (torusSide ℓ.side m) (pt z' + e')) μ
      with hWdef
    set Y : AddCircle (torusSide ℓ.side m) := ((e μ - e' μ : ℝ) : AddCircle (torusSide ℓ.side m)) with hY
    have hX : (((((z' μ).val : ℝ) - (z μ).val : ℝ)) : AddCircle (torusSide ℓ.side m)) = Y - W := by
      simp only [hWdef, hY, torusProj, Pi.sub_apply, Pi.add_apply, pt, AddCircle.coe_add, AddCircle.coe_sub]
      abel
    rw [hX]
    have hYn : ‖Y‖ ≤ 2 := by
      refine (addCircle_norm_coe_le _ _).trans ?_
      calc _ ≤ |e μ| + |e' μ| := abs_sub _ _
        _ ≤ 2 := by linarith [he μ, he' μ]
    calc _ ≤ ‖Y‖ + ‖W‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hlower : ∀ i j, i ≠ j → ∀ z ∈ D i, ∀ z' ∈ D j, ∃ μ, n / 3 - 2 ≤ |torusDisplacement z z' μ| := by
    intro i j hij z hz z' hz'
    obtain ⟨e, he, hP⟩ := (hDmem i z).1 hz
    obtain ⟨e', he', hP'⟩ := (hDmem j z').1 hz'
    let w : Fin 4 → ℝ := fun μ => -torusDisplacement z z' μ + (e μ - e' μ)
    have hcov : torusProj (torusSide ℓ.side m) (pt z + e) - torusProj (torusSide ℓ.side m) (pt z' + e') =
        torusProj (torusSide ℓ.side m) w := by
      rw [torusProj_sub]
      funext μ
      simp only [torusProj]
      have : (pt z + e - (pt z' + e')) μ = w μ +
          ((-round (((((z' μ).val : ℝ) - (z μ).val)) / ((2 * ℓ.side ^ m : ℕ) : ℝ)) : ℤ) : ℝ) *
            torusSide ℓ.side m := by
        simp only [w, pt, torusDisplacement, circleSub, Pi.sub_apply, Pi.add_apply, hSN]
        push_cast
        ring
      rw [this, addCircle_coe_add_int_mul]
    have hsep : n ≤ torusEuclidNorm (torusProj (torusSide ℓ.side m) (pt z + e) -
        torusProj (torusSide ℓ.side m) (pt z' + e')) := by
      have h1 := hf.separated.2 i j hij
      have h2 : setEuclidDist (tsupport (f i)) (tsupport (f j)) ≤
          ENNReal.ofReal (torusEuclidNorm (torusProj (torusSide ℓ.side m) (pt z + e) -
            torusProj (torusSide ℓ.side m) (pt z' + e'))) :=
        iInf₂_le_of_le _ hP (iInf₂_le_of_le _ hP' le_rfl)
      exact (ENNReal.ofReal_le_ofReal_iff (torusEuclidNorm_nonneg _)).1 (h1.trans h2)
    rw [hcov] at hsep
    have hw : n ≤ euclidNormVec w := hsep.trans (torusEuclidNorm_torusProj_le w)
    have hex : ∃ μ, n / 3 ≤ |w μ| := by
      by_contra hno
      have hall : ∀ μ, |w μ| ≤ n / 3 := fun μ => by
        by_contra h
        exact hno ⟨μ, (not_le.mp h).le⟩
      have := euclidNormVec_le w (n / 3) (by positivity) hall
      linarith
    obtain ⟨μ, hμ⟩ := hex
    have h3 : |w μ| ≤ |torusDisplacement z z' μ| + 2 := by
      calc _ ≤ |-torusDisplacement z z' μ| + |e μ - e' μ| := abs_add_le _ _
        _ ≤ |torusDisplacement z z' μ| + (|e μ| + |e' μ|) := by
          rw [abs_neg]
          exact add_le_add le_rfl (abs_sub _ _)
        _ ≤ _ := by linarith [he μ, he' μ]
    exact ⟨μ, by linarith⟩
  refine ⟨D, ?_, ?_, hlower, hupper, ?_, ?_, ?_, ?_, hf1, ?_⟩
  · intro i z hz
    obtain ⟨q, hq, hqf⟩ := (Finset.mem_filter.mp hz).2
    obtain ⟨e, he, hb⟩ := barycenter_near_site hodd z q hq
    refine (hDmem i z).2 ⟨e, he, ?_⟩
    have : f i (plaquetteBarycenterAt ℓ.side k m q) ≠ 0 := hqf
    rw [hb] at this
    exact subset_tsupport _ this
  · intro i
    by_cases hne : (D i).Nonempty
    · obtain ⟨z₀, hz₀⟩ := hne
      set R : ℕ := ⌈10 * n + 2⌉₊ with hR
      have hsub : D i ⊆ Finset.univ.filter fun a : TorusSite (2 * ℓ.side ^ m) => supDist a z₀ ≤ R := by
        intro z hz
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.sup_le fun μ _ => ?_⟩
        have hb := hupper i i z₀ hz₀ z hz μ
        set c : ℤ := round ((((z μ).val : ℝ) - (z₀ μ).val) / ((2 * ℓ.side ^ m : ℕ) : ℝ)) with hc
        set w : ℤ := ((z μ).val : ℤ) - ((z₀ μ).val : ℤ) - ((2 * ℓ.side ^ m : ℕ) : ℤ) * c with hw
        have hwr : (w : ℝ) = torusDisplacement z₀ z μ := by
          simp only [torusDisplacement, circleSub, hw, hc]
          push_cast
          ring
        have hwz : (w : ZMod (2 * ℓ.side ^ m)) = ((z μ - z₀ μ).valMinAbs : ZMod (2 * ℓ.side ^ m)) := by
          rw [ZMod.coe_valMinAbs, hw, Int.cast_sub, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
            Int.cast_natCast, ZMod.natCast_self]
          simp
        have h1 := ZMod.natAbs_min_of_le_div_two (2 * ℓ.side ^ m) (z μ - z₀ μ).valMinAbs w hwz.symm
          (ZMod.natAbs_valMinAbs_le _)
        have h2 : (w.natAbs : ℝ) ≤ R := by
          have : (w.natAbs : ℝ) = |(w : ℝ)| := by
            rw [Nat.cast_natAbs]
            simp
          rw [this, hwr]
          exact hb.trans (Nat.le_ceil _)
        have h3 : w.natAbs ≤ R := by exact_mod_cast h2
        exact h1.trans h3
      have hc1 := (Finset.card_le_card hsub).trans (hSites.2 (2 * ℓ.side ^ m) z₀ R)
      have hR2 : (R : ℝ) ≤ 10 * n + 3 := by
        have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 10 * n + 2 by positivity)
        linarith
      have hc2 : ((D i).card : ℝ) ≤ (2 * (R : ℝ) + 1) ^ 4 := by exact_mod_cast hc1
      refine hc2.trans (pow_le_pow_left₀ (by positivity) ?_ 4)
      linarith
    · have : D i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [this]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  · intro i z _ u hu
    refine abs_blockMean_sub_le hM hW hodd k (2 * ℓ.side ^ m) z _ _ _ (by positivity) fun q hq => ?_
    obtain ⟨e, he, hb⟩ := barycenter_near_site hodd z q hq
    have h1 := abs_sub_le_lipConstTorus_mul (f i) (hf.lipschitz i) (plaquetteBarycenterAt ℓ.side k m q)
      (torusProj (torusSide ℓ.side m) u)
    have h2 : euclidDistTorus (plaquetteBarycenterAt ℓ.side k m q) (torusProj (torusSide ℓ.side m) u) ≤ 4 := by
      simp only [euclidDistTorus]
      rw [hb, torusProj_sub]
      refine (torusEuclidNorm_torusProj_le _).trans ?_
      have := euclidNormVec_le ((fun μ => ((z μ).val : ℝ) + e μ) - u) 2 (by norm_num) fun μ => by
        have h3 := hu μ
        have h4 := abs_le.mp (he μ)
        simp only [Pi.sub_apply]
        rw [abs_le]
        constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
      linarith
    have h3 := hf.lipConst_le i
    have h4 : 0 ≤ euclidDistTorus (plaquetteBarycenterAt ℓ.side k m q) (torusProj (torusSide ℓ.side m) u) :=
      torusEuclidNorm_nonneg _
    calc _ ≤ lipConstTorus (f i) *
          euclidDistTorus (plaquetteBarycenterAt ℓ.side k m q) (torusProj (torusSide ℓ.side m) u) := h1
      _ ≤ 1 / (vt * n) * 4 := by
        have h6 : (0 : ℝ) ≤ 1 / (vt * n) := by positivity
        calc _ ≤ 1 / (vt * n) *
              euclidDistTorus (plaquetteBarycenterAt ℓ.side k m q) (torusProj (torusSide ℓ.side m) u) :=
              mul_le_mul_of_nonneg_right h3 h4
          _ ≤ _ := mul_le_mul_of_nonneg_left h2 h6
      _ = 4 / (vt * n) := by ring
  · intro i z hz u hu
    by_contra hne
    refine hz ((hDmem i z).2 ⟨u - pt z, fun μ => ?_, ?_⟩)
    · have h3 := hu μ
      simp only [Pi.sub_apply, pt]
      rw [abs_le]
      constructor <;> linarith [h3.1, h3.2]
    · have : pt z + (u - pt z) = u := by
        funext μ
        simp
      rw [this]
      exact subset_tsupport _ hne
  · intro i z
    haveI : Nonempty (OrientedPlaquette (fineSide ℓ.side k (2 * ℓ.side ^ m))) :=
      ⟨⟨⟨0, (0, 1)⟩, by show (0 : Fin 4) < 1; decide⟩⟩
    obtain ⟨w1, -, -⟩ := hW ℓ.side hodd k (2 * ℓ.side ^ m) z
    refine (w1 _).trans (ciSup_le fun q => ?_)
    exact hf1 i _
  · intro i z hz
    obtain ⟨-, h2, h3⟩ := hM ℓ.side hodd k (2 * ℓ.side ^ m) z
    have hzero : ∀ q, IsPlaquetteAt ℓ.side k z q → testWeight ℓ.side k m (f i) q =
        0 * testWeight ℓ.side k m (f i) q + 0 * testWeight ℓ.side k m (f i) q := by
      intro q hq
      by_contra hne
      refine hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, q, hq, ?_⟩)
      intro h0
      exact hne (by rw [h0]; simp)
    have := h3 _ (fun q => 0 * testWeight ℓ.side k m (f i) q + 0 * testWeight ℓ.side k m (f i) q) hzero
    rw [h2] at this
    simpa using this
  · intro i
    obtain ⟨C, hC0, hC⟩ := hf.lipschitz i
    have hlip : LipschitzWith (Real.toNNReal (C * 2)) fun v : Fin 4 → ℝ =>
        f i (torusProj (torusSide ℓ.side m) v) := by
      refine LipschitzWith.of_dist_le' fun v w => ?_
      rw [Real.dist_eq]
      have h1 := hC (torusProj (torusSide ℓ.side m) v) (torusProj (torusSide ℓ.side m) w)
      have h2 : euclidDistTorus (torusProj (torusSide ℓ.side m) v) (torusProj (torusSide ℓ.side m) w) ≤
          2 * dist v w := by
        simp only [euclidDistTorus]
        rw [torusProj_sub]
        refine (torusEuclidNorm_torusProj_le _).trans (euclidNormVec_le _ _ dist_nonneg fun μ => ?_)
        have := dist_le_pi_dist v w μ
        rwa [Real.dist_eq] at this
      calc _ ≤ C * euclidDistTorus (torusProj (torusSide ℓ.side m) v) (torusProj (torusSide ℓ.side m) w) := by
            simpa using h1
        _ ≤ C * (2 * dist v w) := mul_le_mul_of_nonneg_left h2 hC0
        _ = _ := by ring
    exact hlip.continuous
end ResponseInTheExpansion
end YangMills.Construction
end
