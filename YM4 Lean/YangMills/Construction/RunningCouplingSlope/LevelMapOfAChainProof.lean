import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import YangMills.Construction.RunningCouplingSlope.ChainNumberIsTheStepsOfTheChainProof
import YangMills.Construction.RunningCouplingSlope.FibreFormIsASumOverTheStepsProof
import YangMills.Construction.RunningCouplingSlope.LengthsOfAChainAreThoseOfItsStepsProof
import YangMills.Construction.Towers.StepOfTheCovariantAveragesAtOneAtTheSideInfinityProof
import YangMills.Construction.Towers.TranslationsAndIsometriesOfATowerProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower BlockAverages ColdStepAtMirrorFrames
namespace LevelFormMap
private def radialCoeff (θ : ℝ) : ℝ := (Real.cos θ - Real.sinc θ) / θ ^ 2
private def idCoeff (θ : ℝ) : ℝ := Real.sinc θ * Real.cos θ
private def crossCoeff (θ : ℝ) : ℝ := Real.sinc θ ^ 2
private def projCoeff (θ : ℝ) : ℝ := Real.sinc θ ^ 2 + radialCoeff θ * Real.cos θ
private theorem sin_eq_sinc_mul (θ : ℝ) : Real.sin θ = Real.sinc θ * θ := by
  by_cases h : θ = 0
  · simp [h]
  · rw [Real.sinc_of_ne_zero h]
    field_simp
private theorem hasDerivAt_norm_add_smul (w x : ℍ[ℝ]) (hw : w ≠ 0) :
    HasDerivAt (fun r : ℝ => ‖w + r • x‖)
      ((w.re * x.re + w.imI * x.imI + w.imJ * x.imJ + w.imK * x.imK) / ‖w‖) 0 := by
  set s := w.re * x.re + w.imI * x.imI + w.imJ * x.imJ + w.imK * x.imK with hs
  set P : ℝ → ℝ := fun r => Quaternion.normSq w + r * (2 * s) + r ^ 2 * Quaternion.normSq x with hPdef
  have hP : ∀ r : ℝ, ‖w + r • x‖ = Real.sqrt (P r) := by
    intro r
    have e : P r = Quaternion.normSq (w + r • x) := by
      show Quaternion.normSq w + r * (2 * s) + r ^ 2 * Quaternion.normSq x = _
      rw [Quaternion.normSq_def', Quaternion.normSq_def', Quaternion.normSq_def']
      simp [hs]
      ring
    rw [e, Quaternion.normSq_eq_norm_mul_self, Real.sqrt_mul_self (norm_nonneg _)]
  have hd : HasDerivAt P (2 * s) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (2 * s)).const_add (Quaternion.normSq w)
    have h2 := (hasDerivAt_pow 2 (0 : ℝ)).mul_const (Quaternion.normSq x)
    exact (h1.add h2).congr_deriv (by simp)
  have hP0 : P 0 = ‖w‖ * ‖w‖ := by
    simp [hPdef, Quaternion.normSq_eq_norm_mul_self]
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hne : P 0 ≠ 0 := by
    rw [hP0]
    exact mul_ne_zero hw' hw'
  have := hd.sqrt hne
  rw [funext hP]
  convert this using 1
  rw [hP0, Real.sqrt_mul_self (norm_nonneg _)]
  field_simp
private theorem exp_add_smul_of_re_eq_zero (w x : ℍ[ℝ]) (hw : w.re = 0) (hx : x.re = 0) (r : ℝ) :
    NormedSpace.exp (w + r • x) =
      Real.cos ‖w + r • x‖ • (1 : ℍ[ℝ]) + (Real.sin ‖w + r • x‖ / ‖w + r • x‖) • (w + r • x) := by
  rw [Quaternion.exp_of_re_eq_zero _ (by simp [hw, hx])]
  congr 1
  ext <;> simp
private theorem hasDerivAt_exp_add_smul (w x : ℍ[ℝ]) (hw : w.re = 0) (hx : x.re = 0) (h0 : w ≠ 0) :
    HasDerivAt (fun r : ℝ => NormedSpace.exp (w + r • x))
      ((-(Real.sinc ‖w‖) * (w.imI * x.imI + w.imJ * x.imJ + w.imK * x.imK)) • (1 : ℍ[ℝ]) +
        (radialCoeff ‖w‖ * (w.imI * x.imI + w.imJ * x.imJ + w.imK * x.imK)) • w + Real.sinc ‖w‖ • x) 0 := by
  set s := w.imI * x.imI + w.imJ * x.imJ + w.imK * x.imK with hs
  have hθ : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hρ := hasDerivAt_norm_add_smul w x h0
  rw [hw, hx] at hρ
  simp only [mul_zero, zero_add] at hρ
  have hs' : w.imI * x.imI + w.imJ * x.imJ + w.imK * x.imK = s := rfl
  rw [hs'] at hρ
  have e0 : ‖w + (0 : ℝ) • x‖ = ‖w‖ := by simp
  have hc : HasDerivAt (fun r : ℝ => Real.cos ‖w + r • x‖) (-Real.sin ‖w‖ * (s / ‖w‖)) 0 := by
    have := hρ.cos
    simpa [e0] using this
  have hsin : HasDerivAt (fun r : ℝ => Real.sin ‖w + r • x‖) (Real.cos ‖w‖ * (s / ‖w‖)) 0 := by
    have := hρ.sin
    simpa [e0] using this
  have hq : HasDerivAt (fun r : ℝ => Real.sin ‖w + r • x‖ / ‖w + r • x‖)
      ((Real.cos ‖w‖ * (s / ‖w‖) * ‖w‖ - Real.sin ‖w‖ * (s / ‖w‖)) / ‖w‖ ^ 2) 0 := by
    have := hsin.fun_div hρ (by simpa using hθ)
    simpa [e0] using this
  have hline : HasDerivAt (fun r : ℝ => w + r • x) x 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const x).const_add w
    simpa using this
  have hall := (hc.smul_const (1 : ℍ[ℝ])).add (hq.smul hline)
  have hfun : (fun r : ℝ => NormedSpace.exp (w + r • x)) =
      (fun r : ℝ => Real.cos ‖w + r • x‖ • (1 : ℍ[ℝ]) + (Real.sin ‖w + r • x‖ / ‖w + r • x‖) • (w + r • x)) :=
    funext (exp_add_smul_of_re_eq_zero w x hw hx)
  rw [hfun]
  refine HasDerivAt.congr_deriv hall ?_
  have hsn := sin_eq_sinc_mul ‖w‖
  have hsc : Real.sin ‖w‖ / ‖w‖ = Real.sinc ‖w‖ := by
    rw [Real.sinc_of_ne_zero hθ]
  simp only [zero_smul, add_zero, e0, hsc]
  rw [show -Real.sin ‖w‖ * (s / ‖w‖) = -Real.sinc ‖w‖ * s by rw [hsn]; field_simp,
    show (Real.cos ‖w‖ * (s / ‖w‖) * ‖w‖ - Real.sin ‖w‖ * (s / ‖w‖)) / ‖w‖ ^ 2 = radialCoeff ‖w‖ * s by
      unfold radialCoeff; rw [hsn]; field_simp]
  abel
private def expLeftDerivMatrix (w : ℍ[ℝ]) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![idCoeff ‖w‖ + projCoeff ‖w‖ * w.imI * w.imI, -crossCoeff ‖w‖ * w.imK + projCoeff ‖w‖ * w.imI * w.imJ,
      crossCoeff ‖w‖ * w.imJ + projCoeff ‖w‖ * w.imI * w.imK;
    crossCoeff ‖w‖ * w.imK + projCoeff ‖w‖ * w.imJ * w.imI, idCoeff ‖w‖ + projCoeff ‖w‖ * w.imJ * w.imJ,
      -crossCoeff ‖w‖ * w.imI + projCoeff ‖w‖ * w.imJ * w.imK;
    -crossCoeff ‖w‖ * w.imJ + projCoeff ‖w‖ * w.imK * w.imI, crossCoeff ‖w‖ * w.imI + projCoeff ‖w‖ * w.imK * w.imJ,
      idCoeff ‖w‖ + projCoeff ‖w‖ * w.imK * w.imK]
private theorem expLeftDeriv_zero (x : ℍ[ℝ]) : expLeftDeriv 0 x = x := by
  unfold expLeftDeriv
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) x (0 : ℝ)
  have e : (fun r : ℝ => NormedSpace.exp ((0 : ℍ[ℝ]) + r • x) * NormedSpace.exp (-(0 : ℍ[ℝ]))) =
      fun r : ℝ => NormedSpace.exp (r • x) := by
    funext r
    simp
  rw [e, h.deriv]
  simp
private theorem imaginaryComponents_expLeftDeriv (w x : ℍ[ℝ]) (hw : w.re = 0) (hx : x.re = 0) :
    imaginaryComponents (expLeftDeriv w x) = Matrix.mulVec (expLeftDerivMatrix w) (imaginaryComponents x) := by
  by_cases h0 : w = 0
  · subst h0
    rw [expLeftDeriv_zero]
    funext c
    fin_cases c <;>
      simp [imaginaryComponents, expLeftDerivMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, idCoeff]
  · have hd := (hasDerivAt_exp_add_smul w x hw hx h0).mul_const (NormedSpace.exp (-w))
    have he : NormedSpace.exp (-w) = Real.cos ‖w‖ • (1 : ℍ[ℝ]) + (-Real.sinc ‖w‖) • w := by
      have hθ : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr h0
      rw [Quaternion.exp_of_re_eq_zero _ (by simp [hw]), norm_neg, ← Real.sinc_of_ne_zero hθ]
      ext <;> simp
    have ht : expLeftDeriv w x = _ := hd.deriv
    rw [ht, he]
    funext c
    fin_cases c <;>
      simp [imaginaryComponents, expLeftDerivMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, idCoeff,
        crossCoeff, projCoeff, hw, hx] <;> ring
private theorem det_rotationLike (a b κ x y z : ℝ) :
    (!![a + κ * x * x, -b * z + κ * x * y, b * y + κ * x * z;
      b * z + κ * y * x, a + κ * y * y, -b * x + κ * y * z;
      -b * y + κ * z * x, b * x + κ * z * y, a + κ * z * z] : Matrix (Fin 3) (Fin 3) ℝ).det =
      (a + κ * (x ^ 2 + y ^ 2 + z ^ 2)) * (a ^ 2 + b ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2)) := by
  rw [Matrix.det_fin_three]
  simp
  ring
private theorem det_expLeftDerivMatrix (w : ℍ[ℝ]) (hw : w.re = 0) :
    (expLeftDerivMatrix w).det = Real.sinc ‖w‖ ^ 2 := by
  unfold expLeftDerivMatrix
  rw [det_rotationLike]
  have hS : w.imI ^ 2 + w.imJ ^ 2 + w.imK ^ 2 = ‖w‖ ^ 2 := by
    rw [sq ‖w‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def', hw]
    ring
  rw [hS]
  set θ := ‖w‖ with hθ
  by_cases h0 : θ = 0
  · simp [h0, idCoeff]
  · have h1 : idCoeff θ + projCoeff θ * θ ^ 2 = 1 := by
      unfold idCoeff projCoeff radialCoeff
      have := Real.sin_sq_add_cos_sq θ
      rw [sin_eq_sinc_mul] at this
      field_simp
      nlinarith [this]
    have h2 : idCoeff θ ^ 2 + crossCoeff θ ^ 2 * θ ^ 2 = Real.sinc θ ^ 2 := by
      unfold idCoeff crossCoeff
      have := Real.sin_sq_add_cos_sq θ
      rw [sin_eq_sinc_mul] at this
      calc _ = Real.sinc θ ^ 2 * ((Real.sinc θ * θ) ^ 2 + Real.cos θ ^ 2) := by ring
        _ = _ := by rw [this, mul_one]
    rw [h1, h2, one_mul]
private theorem exp_haarLogRatio (w : imaginaryQuaternions) (hw : ‖w‖ < Real.pi) :
    Real.exp (haarLogRatio w) = Real.sinc ‖w‖ ^ 2 := by
  have hp : 0 < Real.sinc ‖w‖ := by
    by_cases h0 : ‖w‖ = 0
    · simp [h0]
    · rw [Real.sinc_of_ne_zero h0]
      have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      exact div_pos (Real.sin_pos_of_pos_of_lt_pi hpos hw) hpos
  have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  unfold haarLogRatio haarRadialDensity
  rw [if_pos hw, if_pos Real.pi_pos, Real.sinc_zero]
  have : Real.sinc ‖w‖ ^ 2 / (2 * Real.pi ^ 2) / (1 ^ 2 / (2 * Real.pi ^ 2)) = Real.sinc ‖w‖ ^ 2 := by
    field_simp
  rw [this, Real.exp_log (by positivity)]
section Tree
variable {F : BlockFrame}
private def treeDepth (x : F.Site F.depth) : ℕ := ∑ l, (cellOffset x l).natAbs
private def lastNonzeroAxis (h : Fin 4 → ℤ) : Fin 4 :=
  if h 3 ≠ 0 then 3 else if h 2 ≠ 0 then 2 else if h 1 ≠ 0 then 1 else 0
private theorem lastNonzeroAxis_eq (h : Fin 4 → ℤ) (i : Fin 4) (hi : h i ≠ 0) (hl : ∀ l, i < l → h l = 0) :
    lastNonzeroAxis h = i := by
  unfold lastNonzeroAxis
  fin_cases i
  · have h1 := hl 1 (by decide)
    have h2 := hl 2 (by decide)
    have h3 := hl 3 (by decide)
    simp [h1, h2, h3]
  · have h2 := hl 2 (by decide)
    have h3 := hl 3 (by decide)
    have hi' : h 1 ≠ 0 := hi
    simp [h2, h3, hi']
  · have h3 := hl 3 (by decide)
    have hi' : h 2 ≠ 0 := hi
    simp [h3, hi']
  · have hi' : h 3 ≠ 0 := hi
    simp [hi']
private def treeParent (x : F.Site F.depth) : F.Site F.depth :=
  if 0 < cellOffset x (lastNonzeroAxis (cellOffset x)) then x - unitStep F.depth (lastNonzeroAxis (cellOffset x))
  else x + unitStep F.depth (lastNonzeroAxis (cellOffset x))
private def edgeToParent (x : F.Site F.depth) : F.Site F.depth × Fin 4 :=
  if 0 < cellOffset x (lastNonzeroAxis (cellOffset x)) then
    (x - unitStep F.depth (lastNonzeroAxis (cellOffset x)), lastNonzeroAxis (cellOffset x))
  else (x, lastNonzeroAxis (cellOffset x))
private def parentSign (x : F.Site F.depth) : ℝ :=
  if 0 < cellOffset x (lastNonzeroAxis (cellOffset x)) then 1 else -1
open Classical in
private def treeData (z : TreeCoord F → ℝ) (b : F.Site F.depth × Fin 4) : Fin 3 → ℝ :=
  if h : b ∈ treeEdges F then fun c => z (⟨b, h⟩, c) else 0
private def pathSum (z : TreeCoord F → ℝ) : ℕ → F.Site F.depth → Fin 3 → ℝ
  | 0, _ => 0
  | m + 1, x => pathSum z m (treeParent x) + parentSign x • treeData z (edgeToParent x)
private theorem treeData_add (z z' : TreeCoord F → ℝ) (b : F.Site F.depth × Fin 4) :
    treeData (z + z') b = treeData z b + treeData z' b := by
  unfold treeData
  split_ifs
  · rfl
  · simp
private theorem treeData_smul (r : ℝ) (z : TreeCoord F → ℝ) (b : F.Site F.depth × Fin 4) :
    treeData (r • z) b = r • treeData z b := by
  unfold treeData
  split_ifs
  · rfl
  · simp
private theorem pathSum_add (z z' : TreeCoord F → ℝ) :
    ∀ (m : ℕ) (x : F.Site F.depth), pathSum (z + z') m x = pathSum z m x + pathSum z' m x := by
  intro m
  induction m with
  | zero => intro x; simp [pathSum]
  | succ m ih =>
    intro x
    simp only [pathSum, ih, treeData_add, smul_add]
    abel
private theorem pathSum_smul (r : ℝ) (z : TreeCoord F → ℝ) :
    ∀ (m : ℕ) (x : F.Site F.depth), pathSum (r • z) m x = r • pathSum z m x := by
  intro m
  induction m with
  | zero => intro x; simp [pathSum]
  | succ m ih =>
    intro x
    simp only [pathSum, ih, treeData_smul, smul_add]
    rw [smul_comm]
private def treePotential : (TreeCoord F → ℝ) →ₗ[ℝ] (F.Site F.depth → Fin 3 → ℝ) where
  toFun z := fun x => pathSum z (treeDepth x) x
  map_add' z z' := by
    funext x
    exact pathSum_add z z' _ x
  map_smul' r z := by
    funext x
    exact pathSum_smul r z _ x
private theorem treePotential_apply (z : TreeCoord F → ℝ) (x : F.Site F.depth) :
    treePotential z x = pathSum z (treeDepth x) x := rfl
private theorem treePotential_of_cellOffset_eq_zero (z : TreeCoord F → ℝ) (x : F.Site F.depth)
    (h : cellOffset x = 0) : treePotential z x = 0 := by
  rw [treePotential_apply]
  have : treeDepth x = 0 := by simp [treeDepth, h]
  rw [this]
  rfl
private theorem siteOfCoords_add (j : ℕ) (z z' : Fin 4 → ℤ) :
    (siteOfCoords j (z + z') : F.Site j) = siteOfCoords j z + siteOfCoords j z' := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
private theorem cellOffset_add_unitStep (hs : SiteDecomposition) (hL : Odd F.blockSide)
    (hside : ∀ i, 2 ≤ F.extent i) (y : F.Site F.depth) (i : Fin 4) (hc : ¬ IsCrossingBond (y, i)) :
    cellOffset (y + unitStep F.depth i) = cellOffset y + Pi.single i 1 := by
  obtain ⟨c1, c2, c3, -⟩ := hs F hL hside
  obtain ⟨e, hm⟩ := c2 y
  have hne : cellOffset y i ≠ ((F.blockSide : ℤ) - 1) / 2 := fun h => hc ((c3 y i).2 h)
  have hm' : cellOffset y + Pi.single i 1 ∈ centredCube F.blockSide := by
    unfold centredCube at hm ⊢
    rw [Fintype.mem_piFinset] at hm ⊢
    intro l
    have := hm l
    rw [Finset.mem_Icc] at this ⊢
    by_cases hl : l = i
    · subst hl
      simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hl]
      omega
  have hy : y + unitStep F.depth i =
      cellCentre F.depth (enclosingCell y) + siteOfCoords F.depth (cellOffset y + Pi.single i 1) := by
    rw [siteOfCoords_add, ← add_assoc, e]
    rfl
  rw [hy]
  exact (c1 _ _ hm').2
private theorem sum_natAbs_add_single (h : Fin 4 → ℤ) (i : Fin 4) (hi : 0 ≤ h i) :
    (∑ l, ((h + Pi.single i 1 : Fin 4 → ℤ) l).natAbs) = (∑ l, (h l).natAbs) + 1 := by
  fin_cases i <;> simp [Fin.sum_univ_four, Pi.single_apply] at hi ⊢ <;> omega
private theorem treePotential_sub (hs : SiteDecomposition) (hL : Odd F.blockSide)
    (hside : ∀ i, 2 ≤ F.extent i) (z : TreeCoord F → ℝ) (y : F.Site F.depth) (i : Fin 4)
    (hb : (y, i) ∈ treeEdges F) :
    treePotential z (y + unitStep F.depth i) - treePotential z y = treeData z (y, i) := by
  classical
  have ht : IsAxialTreeBond (y, i) := (Finset.mem_filter.mp hb).2
  have hoff := cellOffset_add_unitStep hs hL hside y i ht.1
  have hl : ∀ l, i < l → cellOffset y l = 0 := ht.2
  have hdep : ∀ x : F.Site F.depth, treeDepth x = ∑ l, (cellOffset x l).natAbs := fun _ => rfl
  by_cases h0 : 0 ≤ cellOffset y i
  · have hpos : 0 < cellOffset (y + unitStep F.depth i) i := by
      rw [hoff]
      simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    have hlast : lastNonzeroAxis (cellOffset (y + unitStep F.depth i)) = i := by
      refine lastNonzeroAxis_eq _ i hpos.ne' fun l hil => ?_
      rw [hoff]
      simp [hl l hil, Pi.single_eq_of_ne hil.ne']
    have hd : treeDepth (y + unitStep F.depth i) = treeDepth y + 1 := by
      rw [hdep, hoff]
      exact sum_natAbs_add_single _ i h0
    rw [treePotential_apply, treePotential_apply, hd]
    simp only [pathSum, treeParent, edgeToParent, parentSign, hlast, if_pos hpos, add_sub_cancel_right,
      one_smul]
    abel
  · have hneg : cellOffset y i < 0 := not_le.mp h0
    have hlast : lastNonzeroAxis (cellOffset y) = i := lastNonzeroAxis_eq _ i hneg.ne hl
    have hnpos : ¬ 0 < cellOffset y i := by omega
    have hd : treeDepth y = treeDepth (y + unitStep F.depth i) + 1 := by
      have e := sum_natAbs_add_single (-(cellOffset y + Pi.single i 1)) i (by
        simp only [Pi.neg_apply, Pi.add_apply, Pi.single_eq_same]
        omega)
      have e2 : -(cellOffset y + Pi.single i 1) + Pi.single i 1 = -cellOffset y := by
        abel
      rw [e2] at e
      simp only [Pi.neg_apply, Int.natAbs_neg] at e
      rw [hdep, hdep, hoff]
      simpa using e
    rw [treePotential_apply, treePotential_apply, hd]
    simp only [pathSum, treeParent, edgeToParent, parentSign, hlast, if_neg hnpos]
    simp
end Tree
section LatticeSites
variable {L n k j : ℕ}
private def latticeSite (d : ℤ) (z : Fin 4 → ℤ) : PeriodicLattice.Site L n d :=
  PeriodicLattice.offsetSite 0 z
private theorem coe_latticeSite (d : ℤ) (z : Fin 4 → ℤ) (ν : Fin 4) :
    ((latticeSite (L := L) (n := n) d z : PeriodicLattice.Site L n d) : PeriodicLattice.FourTorus L n) ν =
      (((z ν : ℝ) * PeriodicLattice.meshSize L d : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
  have h1 : ((latticeSite (L := L) (n := n) d z : PeriodicLattice.Site L n d) : PeriodicLattice.FourTorus L n) =
      ∑ μ, z μ • PeriodicLattice.pointOnAxis L n μ (PeriodicLattice.meshSize L d) := by
    show (PeriodicLattice.sublattice L n d).subtype (latticeSite d z) = _
    simp only [latticeSite, PeriodicLattice.offsetSite, zero_add]
    rw [map_sum]
    exact Finset.sum_congr rfl fun μ _ => map_zsmul _ _ _
  rw [h1, Finset.sum_apply, Finset.sum_eq_single ν]
  · simp only [Pi.smul_apply, PeriodicLattice.pointOnAxis, Pi.single_eq_same]
    rw [← zsmul_eq_mul]
    exact (QuotientAddGroup.mk_zsmul _ _ _).symm
  · intro b _ hb
    simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hb.symm]
  · simp
private theorem latticeSite_eq_of_modEq (d : ℤ) {P : ℕ}
    (hP : (P : ℝ) * PeriodicLattice.meshSize L d = PeriodicLattice.torusSide L n) (z z' : Fin 4 → ℤ)
    (h : ∀ ν, ∃ m : ℤ, z ν - z' ν = m * P) : latticeSite (L := L) (n := n) d z = latticeSite d z' := by
  refine Subtype.ext (funext fun ν => ?_)
  rw [coe_latticeSite, coe_latticeSite, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  obtain ⟨m, hm⟩ := h ν
  refine ⟨m, ?_⟩
  rw [← hP, zsmul_eq_mul, ← mul_assoc, ← sub_mul]
  congr 1
  exact_mod_cast hm.symm
private theorem exists_latticeSite_eq (d : ℤ) (x : PeriodicLattice.Site L n d) :
    ∃ z : Fin 4 → ℤ, x = latticeSite d z := by
  obtain ⟨z, hz⟩ := x.2
  refine ⟨z, Subtype.ext (funext fun ν => ?_)⟩
  rw [coe_latticeSite, hz ν]
private theorem unitStep_eq_latticeSite (d : ℤ) (μ : Fin 4) :
    PeriodicLattice.unitStep L n d μ = latticeSite d (Pi.single μ 1) := by
  refine Subtype.ext (funext fun ν => ?_)
  rw [coe_latticeSite]
  by_cases h : ν = μ
  · subst h
    simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis]
  · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
private theorem latticeSite_add (d : ℤ) (z z' : Fin 4 → ℤ) :
    latticeSite (L := L) (n := n) d (z + z') = latticeSite d z + latticeSite d z' := by
  simp only [latticeSite, PeriodicLattice.offsetSite, zero_add, Pi.add_apply, add_smul,
    Finset.sum_add_distrib]
private theorem torusSideBelow_eq (L : ℕ) : ∀ s N : ℕ, torusSideBelow L s N = N * L ^ s := by apply _root_.YangMills.SharedProofs.p41915 <;> assumption
private theorem period_frameAtStep (hj : j < k) (i : Fin 4) :
    (frameAtStep L n k j).period (frameAtStep L n k j).depth i = 2 * L ^ (n + (k - j)) := by apply _root_.YangMills.SharedProofs.p69486 <;> assumption
private theorem two_le_extent_frameAtStep (hL : 0 < L) (hj : j < k) (i : Fin 4) :
    2 ≤ (frameAtStep L n k j).extent i := by
  simp only [frameAtStep, TorusFields.torusFrame, sideAtStep, torusSideBelow_eq]
  have h1 : 0 < L ^ n * L ^ (k - (j + 1)) := by positivity
  nlinarith
private theorem period_mul_meshSize (hL : 0 < L) (hj : j ≤ k) :
    ((2 * L ^ (n + (k - j)) : ℕ) : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j) =
      PeriodicLattice.torusSide L n := by
  have e : PeriodicLattice.levelDepth k j = ((k - j : ℕ) : ℤ) := by
    simp [PeriodicLattice.levelDepth, Nat.cast_sub hj]
  simp only [PeriodicLattice.meshSize, PeriodicLattice.torusSide, e]
  push_cast
  rw [zpow_neg, zpow_natCast, pow_add]
  field_simp
end LatticeSites
private def suTwoMatrix : (Fin 3 → ℝ) →ₗ[ℝ] Matrices.ComplexMatrix2 where
  toFun b := !![((b 0 : ℝ) : ℂ), ((b 2 : ℝ) : ℂ) - Complex.I * ((b 1 : ℝ) : ℂ);
    ((b 2 : ℝ) : ℂ) + Complex.I * ((b 1 : ℝ) : ℂ), -((b 0 : ℝ) : ℂ)]
  map_add' b b' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' r b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
private theorem suTwoComponents_suTwoMatrix (b : Fin 3 → ℝ) : suTwoComponents (suTwoMatrix b) = b := by
  funext c
  fin_cases c <;> simp [suTwoComponents, suTwoMatrix]
private theorem suTwoMatrix_mem (b : Fin 3 → ℝ) :
    suTwoMatrix b ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [suTwoMatrix, Matrix.conjTranspose_apply, Complex.conj_ofReal] <;> ring
  · simp [suTwoMatrix, Matrix.trace_fin_two]
private theorem suTwoComponents_add (A B : Matrices.ComplexMatrix2) :
    suTwoComponents (A + B) = suTwoComponents A + suTwoComponents B := by
  funext c
  fin_cases c <;> simp [suTwoComponents] <;> ring
abbrev _root_.YangMills.SharedProofs.p37688 := @suTwoComponents_add
private theorem suTwoComponents_smul (r : ℝ) (A : Matrices.ComplexMatrix2) :
    suTwoComponents (r • A) = r • suTwoComponents A := by
  funext c
  fin_cases c <;> simp [suTwoComponents]
abbrev _root_.YangMills.SharedProofs.p5119 := @suTwoComponents_smul
section Level
variable {L n k j : ℕ}
private theorem latticeSite_eq_of_zmod (hL : 0 < L) (hj : j < k) (z z' : Fin 4 → ℤ)
    (h : ∀ ν, ((z ν : ℤ) : ZMod ((frameAtStep L n k j).period (frameAtStep L n k j).depth ν)) = (z' ν : ℤ)) :
    latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) z = latticeSite _ z' := by
  refine latticeSite_eq_of_modEq _ (period_mul_meshSize hL hj.le) z z' fun ν => ?_
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (h ν)
  refine ⟨-m, ?_⟩
  have hc : (((frameAtStep L n k j).period (frameAtStep L n k j).depth ν : ℕ) : ℤ) =
      ((2 * L ^ (n + (k - j)) : ℕ) : ℤ) := by rw [period_frameAtStep hj]
  rw [hc] at hm
  have : z ν - z' ν = -(z' ν - z ν) := by ring
  rw [this, hm]
  ring
private theorem siteCoords_cast {F : BlockFrame} {l : ℕ} (x : F.Site l) (ν : Fin 4) :
    ((siteCoords x ν : ℤ) : ZMod (F.period l ν)) = x ν := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
private theorem exists_frameSite_equiv (hb : FramePositiveEdgesBijective)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k) :
    ∃ e : (frameAtStep L n k j).Site (frameAtStep L n k j).depth ≃ Vertex L n k j,
      ∀ x, e x = latticeSite (PeriodicLattice.levelDepth k j) (siteCoords x) := by
  obtain ⟨-, hinj, hsurj⟩ := hb L hL n k j hn hj.le (frameAtStep L n k j) (frameAtStep L n k j).depth
    (period_frameAtStep hj)
  refine ⟨Equiv.ofBijective (fun x => latticeSite (PeriodicLattice.levelDepth k j) (siteCoords x)) ⟨?_, ?_⟩,
    fun _ => rfl⟩
  · intro x x' h
    have e : edgeOfCoords (L := L) (n := n) (k := k) j (x, (0 : Fin 4)) =
        edgeOfCoords j (x', (0 : Fin 4)) := by
      have h' : PeriodicLattice.offsetSite 0 (siteCoords x) =
          (PeriodicLattice.offsetSite 0 (siteCoords x') : Vertex L n k j) := h
      simp only [edgeOfCoords, h']
    exact congrArg Prod.fst (hinj e)
  · intro s
    obtain ⟨b, hbb⟩ := hsurj (PeriodicLattice.Bond.forwardFrom s 0)
      ⟨0, by simp [PeriodicLattice.Bond.forwardFrom]⟩
    exact ⟨b.1, congrArg PeriodicLattice.Bond.source hbb⟩
private theorem source_edgeOfCoords (x : (frameAtStep L n k j).Site (frameAtStep L n k j).depth) (i : Fin 4) :
    (edgeOfCoords (L := L) (n := n) (k := k) j (x, i)).source =
      latticeSite (PeriodicLattice.levelDepth k j) (siteCoords x) := rfl
private theorem target_edgeOfCoords (hL : 0 < L) (hj : j < k)
    (x : (frameAtStep L n k j).Site (frameAtStep L n k j).depth) (i : Fin 4) :
    (edgeOfCoords (L := L) (n := n) (k := k) j (x, i)).target =
      latticeSite (PeriodicLattice.levelDepth k j) (siteCoords (x + unitStep (frameAtStep L n k j).depth i)) := by
  have e : (edgeOfCoords (L := L) (n := n) (k := k) j (x, i)).target =
      latticeSite (PeriodicLattice.levelDepth k j) (siteCoords x) +
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) i := rfl
  rw [e, unitStep_eq_latticeSite, ← latticeSite_add]
  refine latticeSite_eq_of_zmod hL hj _ _ fun ν => ?_
  rw [siteCoords_cast, Pi.add_apply, Int.cast_add, siteCoords_cast]
  rfl
private theorem siteOfCoords_mul_eq_cellCentre (F : BlockFrame) (z : Fin 4 → ℤ) :
    (siteOfCoords F.depth (fun i => (F.blockSide : ℤ) * z i) : F.Site F.depth) =
      cellCentre F.depth (siteOfCoords F.top z) := by
  funext ν
  simp only [siteOfCoords, cellCentre]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have h1 : F.top - F.depth = 1 := by simp [BlockFrame.top]
  have h2 : ((siteCoords (siteOfCoords F.top z : F.Site F.top) ν : ℤ) : ZMod (F.period F.top ν)) = (z ν : ℤ) :=
    ZMod.intCast_zmod_cast _
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h2
  have hp : F.period F.depth ν = F.extent ν * F.blockSide := by simp [BlockFrame.period, h1]
  have hp' : F.period F.top ν = F.extent ν := by simp [BlockFrame.period]
  rw [hp'] at hm
  rw [hp, h1]
  refine ⟨-m, ?_⟩
  push_cast
  have : (F.blockSide : ℤ) ^ 1 * siteCoords (siteOfCoords F.top z : F.Site F.top) ν - (F.blockSide : ℤ) * z ν =
      -((F.blockSide : ℤ) * (z ν - siteCoords (siteOfCoords F.top z : F.Site F.top) ν)) := by ring
  rw [this, hm]
  ring
private theorem exists_cellCentre_of_upper (hs : SiteDecomposition)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k) (s : Vertex L n k (j + 1)) :
    ∃ x : (frameAtStep L n k j).Site (frameAtStep L n k j).depth, cellOffset x = 0 ∧
      PeriodicLattice.Site.toSublattice s (PeriodicLattice.levelDepth k j) =
        latticeSite (PeriodicLattice.levelDepth k j) (siteCoords x) := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL0.ne'
  obtain ⟨z, rfl⟩ := exists_latticeSite_eq _ s
  set F := frameAtStep L n k j with hF
  set x : F.Site F.depth := siteOfCoords F.depth (fun i => (L : ℤ) * z i) with hx
  refine ⟨x, ?_, ?_⟩
  · obtain ⟨c1, -, -, -⟩ := hs F hL.1 (two_le_extent_frameAtStep hL0 hj)
    have h0 : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
      unfold centredCube
      rw [Fintype.mem_piFinset]
      intro l
      rw [Finset.mem_Icc]
      have : 13 ≤ F.blockSide := hL.2
      constructor <;> simp <;> omega
    have e := (c1 (siteOfCoords F.top z) 0 h0).2
    have e0 : (siteOfCoords F.depth (0 : Fin 4 → ℤ) : F.Site F.depth) = 0 := by
      funext i
      simp [siteOfCoords]
    rw [e0, add_zero, ← siteOfCoords_mul_eq_cellCentre] at e
    exact e
  · have hpt : ((latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) (fun i => (L : ℤ) * z i) :
        PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j)) : PeriodicLattice.FourTorus L n) =
        (latticeSite (PeriodicLattice.levelDepth k (j + 1)) z :
          PeriodicLattice.Site L n (PeriodicLattice.levelDepth k (j + 1))) := by
      funext ν
      rw [coe_latticeSite, coe_latticeSite]
      congr 1
      have e : PeriodicLattice.levelDepth k j = PeriodicLattice.levelDepth k (j + 1) + 1 := by
        simp [PeriodicLattice.levelDepth]
        ring
      simp only [PeriodicLattice.meshSize, e]
      rw [neg_add, zpow_add₀ hLr]
      push_cast
      simp
      field_simp
    have hsp := Classical.epsilon_spec (p := fun y : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j) =>
      (y : PeriodicLattice.FourTorus L n) = (latticeSite (PeriodicLattice.levelDepth k (j + 1)) z :
        PeriodicLattice.Site L n (PeriodicLattice.levelDepth k (j + 1)))) ⟨_, hpt⟩
    have e1 : PeriodicLattice.Site.toSublattice
        (latticeSite (L := L) (n := n) (PeriodicLattice.levelDepth k (j + 1)) z)
        (PeriodicLattice.levelDepth k j) =
          latticeSite (PeriodicLattice.levelDepth k j) (fun i => (L : ℤ) * z i) :=
      Subtype.ext (hsp.trans hpt.symm)
    rw [e1]
    refine latticeSite_eq_of_zmod hL0 hj _ _ fun ν => ?_
    rw [siteCoords_cast]
    rfl
private theorem exists_levelGauge (hs : SiteDecomposition)
    (hb : FramePositiveEdgesBijective) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) :
    ∃ g : (TreeCoord (frameAtStep L n k j) → ℝ) →ₗ[ℝ] (Vertex L n k j → Matrices.ComplexMatrix2),
      (∀ z, g z ∈ vertexFunctionSpace L n k j) ∧ (∀ z, restrictVertexFunction (j + 1) (g z) = 0) ∧
      ∀ z b, b ∈ treeEdges (frameAtStep L n k j) →
        g z (edgeOfCoords (L := L) (n := n) (k := k) j b).target -
          g z (edgeOfCoords (L := L) (n := n) (k := k) j b).source = suTwoMatrix (treeData z b) := by
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨e, he⟩ := exists_frameSite_equiv (j := j) hb hL hn hj
  refine ⟨{ toFun := fun z s => suTwoMatrix (treePotential z (e.symm s)), map_add' := ?_, map_smul' := ?_ },
    ?_, ?_, ?_⟩
  · intro z z'
    funext s
    simp
  · intro r z
    funext s
    simp
  · intro z s _
    exact suTwoMatrix_mem _
  · intro z
    funext s
    obtain ⟨x, hx, hs'⟩ := exists_cellCentre_of_upper hs hL hn hj s
    show suTwoMatrix (treePotential z (e.symm (PeriodicLattice.Site.toSublattice s
      (PeriodicLattice.levelDepth k j)))) = 0
    rw [hs', ← he, Equiv.symm_apply_apply, treePotential_of_cellOffset_eq_zero z x hx, map_zero]
  · rintro z ⟨y, i⟩ hbt
    show suTwoMatrix (treePotential z (e.symm _)) - suTwoMatrix (treePotential z (e.symm _)) = _
    rw [target_edgeOfCoords hL0 hj, source_edgeOfCoords, ← he, ← he, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply, ← map_sub,
      treePotential_sub hs hL.1 (two_le_extent_frameAtStep hL0 hj) z y i hbt]
end Level
section Blocks
variable {J : Type} [Fintype J] [DecidableEq J] {ι : J → Type} [∀ j, Fintype (ι j)]
  [∀ j, DecidableEq (ι j)]
private theorem mulVec_blockDiagonal'_apply (M : ∀ j, Matrix (ι j) (ι j) ℝ) (u : (Σ j, ι j) → ℝ) (j : J)
    (i : ι j) :
    Matrix.mulVec (Matrix.blockDiagonal' M) u ⟨j, i⟩ = Matrix.mulVec (M j) (fun i' => u ⟨j, i'⟩) i := by
  simp only [dotProduct, Matrix.mulVec]
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Matrix.blockDiagonal'_apply_eq]
  · intro j' _ hj'
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hj'), zero_mul]
  · simp
private theorem det_blockDiagonal'_eq_prod [LinearOrder J] (M : ∀ j, Matrix (ι j) (ι j) ℝ) :
    (Matrix.blockDiagonal' M).det = ∏ j, (M j).det := by apply _root_.YangMills.SharedProofs.p20357 <;> assumption
end Blocks
section Chart
variable {F : BlockFrame}
open Classical in
private def chordDerivMatrix (w : ↥(chordBonds (finiteCells F)) → ℍ[ℝ]) :
    Matrix (ReferenceDensity.ChartCoord F) (ReferenceDensity.ChartCoord F) ℝ :=
  (Matrix.blockDiagonal fun b => expLeftDerivMatrix (w b)).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _)
open Classical in
private theorem det_chordDerivMatrix (w : ↥(chordBonds (finiteCells F)) → ℍ[ℝ]) (hw : ∀ b, (w b).re = 0) :
    (chordDerivMatrix w).det = ∏ b, Real.sinc ‖w b‖ ^ 2 := by
  unfold chordDerivMatrix
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
  exact Finset.prod_congr rfl fun b _ => det_expLeftDerivMatrix _ (hw b)
open Classical in
private theorem chordDerivMatrix_mulVec (w : ↥(chordBonds (finiteCells F)) → ℍ[ℝ])
    (x : ReferenceDensity.ChartCoord F → ℝ) (i : ReferenceDensity.ChartCoord F) :
    Matrix.mulVec (chordDerivMatrix w) x i =
      Matrix.mulVec (expLeftDerivMatrix (w i.1)) (fun c => x (i.1, c)) i.2 := by
  simp only [Matrix.mulVec, dotProduct, chordDerivMatrix, Matrix.submatrix_apply]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i.1]
  · refine Finset.sum_congr rfl fun c _ => ?_
    simp [Matrix.blockDiagonal_apply]
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => ?_
    simp [Matrix.blockDiagonal_apply, Ne.symm hb]
  · simp
end Chart
private theorem imaginaryComponents_toImaginary (v : EuclideanSpace ℝ (Fin 3)) :
    imaginaryComponents ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]) = fun c => v c := by
  funext c
  fin_cases c <;> simp [imaginaryComponents, toImaginary]
private theorem quaternionToMatrix_one : SoftAverages.quaternionToMatrix 1 = 1 := by apply _root_.YangMills.Construction.SoftAverages.quaternionToMatrix_one <;> assumption
private theorem conjugateBy_one (A : Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2.conjugateBy 1 A = A := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.conjugateBy_one <;> assumption
private theorem conjugateBy_add (V A B : Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.conjugateBy V (A + B) =
      Matrices.ComplexMatrix2.conjugateBy V A + Matrices.ComplexMatrix2.conjugateBy V B := by
  simp [Matrices.ComplexMatrix2.conjugateBy, mul_add, add_mul]
private theorem conjugateBy_smul (V A : Matrices.ComplexMatrix2) (r : ℝ) :
    Matrices.ComplexMatrix2.conjugateBy V (r • A) = r • Matrices.ComplexMatrix2.conjugateBy V A := by
  simp [Matrices.ComplexMatrix2.conjugateBy]
section SeriesExpansions
variable {L n k j : ℕ}
private theorem covDiff_of_isPositivelyOriented (U : Edge L n k j → Matrices.ComplexMatrix2)
    (l : Vertex L n k j → Matrices.ComplexMatrix2) (c : Edge L n k j) (hc : c.IsPositivelyOriented) :
    covDiff U l c = Matrices.ComplexMatrix2.conjugateBy (U c) (l c.target) - l c.source := by apply _root_.YangMills.Construction.Tower.Translations.covDiff_of_pos <;> assumption
end SeriesExpansions
section Assembly
variable {L n k : ℕ}
private theorem isPositivelyOriented_edgeOfCoords (hb : FramePositiveEdgesBijective)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    (b : (frameAtStep L n k j).Site (frameAtStep L n k j).depth × Fin 4) :
    (edgeOfCoords (L := L) (n := n) (k := k) j b).IsPositivelyOriented :=
  (hb L hL n k j hn hj.le (frameAtStep L n k j) (frameAtStep L n k j).depth (period_frameAtStep hj)).1 b
open Classical in
private theorem exists_chordRows_matrix (hb : FramePositiveEdgesBijective)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (j : Fin k)
    (U : Edge L n k j → Matrices.ComplexMatrix2)
    (g : (TreeCoord (frameAtStep L n k j) → ℝ) →ₗ[ℝ] (Vertex L n k j → Matrices.ComplexMatrix2)) :
    ∃ C : Matrix (ReferenceDensity.ChartCoord (frameAtStep L n k j)) (TreeCoord (frameAtStep L n k j)) ℝ,
      ∀ z i, Matrix.mulVec C z i = levelCoords j (covDiff U (g z)) (.inl i) := by
  let Φ : (TreeCoord (frameAtStep L n k j) → ℝ) →ₗ[ℝ]
      (ReferenceDensity.ChartCoord (frameAtStep L n k j) → ℝ) :=
    { toFun := fun z i => levelCoords j (covDiff U (g z)) (.inl i)
      map_add' := fun z z' => by
        funext i
        have hp := isPositivelyOriented_edgeOfCoords hb hL hn j.2 i.1.1
        show suTwoComponents (covDiff U (g (z + z')) _) i.2 =
          suTwoComponents (covDiff U (g z) _) i.2 + suTwoComponents (covDiff U (g z') _) i.2
        rw [covDiff_of_isPositivelyOriented _ _ _ hp, covDiff_of_isPositivelyOriented _ _ _ hp,
          covDiff_of_isPositivelyOriented _ _ _ hp, map_add]
        have e : ∀ (s t s' t' : Matrices.ComplexMatrix2),
            Matrices.ComplexMatrix2.conjugateBy (U (edgeOfCoords j i.1.1)) (s + s') - (t + t') =
            (Matrices.ComplexMatrix2.conjugateBy (U (edgeOfCoords j i.1.1)) s - t) +
              (Matrices.ComplexMatrix2.conjugateBy (U (edgeOfCoords j i.1.1)) s' - t') := by
          intro s t s' t'
          rw [conjugateBy_add]
          abel
        simp only [Pi.add_apply]
        rw [e, suTwoComponents_add]
        rfl
      map_smul' := fun r z => by
        funext i
        have hp := isPositivelyOriented_edgeOfCoords hb hL hn j.2 i.1.1
        show suTwoComponents (covDiff U (g (r • z)) _) i.2 =
          r • suTwoComponents (covDiff U (g z) _) i.2
        rw [covDiff_of_isPositivelyOriented _ _ _ hp, covDiff_of_isPositivelyOriented _ _ _ hp, map_smul]
        simp only [Pi.smul_apply]
        rw [conjugateBy_smul, ← smul_sub, suTwoComponents_smul]
        rfl }
  exact ⟨LinearMap.toMatrix' Φ, fun z i => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩
private theorem norm_minimizerCoordAtStep_le (a ρ : ℝ) (hρ : 0 ≤ ρ) (L n k j : ℕ)
    (V : TorusFields.TorusField (2 * L ^ n)) (b : ↥(chordBonds (finiteCells (frameAtStep L n k j)))) :
    ‖minimizerCoordAtStep a ρ L n k j V b‖ ≤ ρ := by
  classical
  have hz : stepCoordinates (0 : StepVariable (finiteCells (frameAtStep L n k j))) b.1.1 b.1.2 = 0 := by
    unfold stepCoordinates
    split_ifs
    · ext <;> simp [toImaginary]
    · rfl
  unfold minimizerCoordAtStep coordsAboveFrame
  rw [hz, add_zero]
  simp only [ColdStepAtMirrorFrames.stepFrame, if_true, minimizingBondCoordinate, minimizingCoordinates]
  split_ifs with h
  · exact h.choose_spec.2.1 b.1 b.2
  · simpa using hρ
open Classical in
private theorem exists_level_matrix (hlev : ChainLevelIsStepMinimizer)
    (hb : FramePositiveEdgesBijective) (hs : SiteDecomposition)
    {a ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (V : TorusFields.TorusField (2 * L ^ n)) (X : ChainPoint L n k) (hR : RepresentsMinimizerChain a ρ V X)
    (j : Fin k) :
    ∃ M : Matrix (LevelCoord (frameAtStep L n k j)) (LevelCoord (frameAtStep L n k j)) ℝ,
      M.det = Real.exp (∑ b, haarLogRatio (minimizerCoordAtStep a ρ L n k j V b)) ∧
      ∀ u : LevelCoord (frameAtStep L n k j) → ℝ,
        (∃ g : Vertex L n k j → Matrices.ComplexMatrix2, g ∈ vertexFunctionSpace L n k j ∧
          restrictVertexFunction (j + 1) g = 0 ∧
          ∀ e, Matrix.mulVec M u e = chartDirection a ρ L n k V j (fun i => u (.inl i)) e +
            levelCoords j (covDiff (levelField X j) g) e) ∧
        ∀ i, Matrix.mulVec M u (.inr i) = u (.inr i) := by
  obtain ⟨g, hgm, hgr, hgt⟩ := exists_levelGauge (j := j) hs hb hL hn j.2
  obtain ⟨C, hC⟩ := exists_chordRows_matrix hb hL hn j (levelField X j) g
  set w : ↥(chordBonds (finiteCells (frameAtStep L n k j))) → ℍ[ℝ] :=
    fun b => (minimizerCoordAtStep a ρ L n k j V b : ℍ[ℝ]) with hw
  have hre : ∀ b, (w b).re = 0 := fun b => (minimizerCoordAtStep a ρ L n k j V b).2
  have hlt : ∀ b, ‖minimizerCoordAtStep a ρ L n k j V b‖ < Real.pi := fun b =>
    ((norm_minimizerCoordAtStep_le a ρ h0.le L n k j V b).trans h1).trans_lt
      (lt_of_lt_of_le (by norm_num) Real.pi_gt_three.le)
  have htree : ∀ (z : TreeCoord (frameAtStep L n k j) → ℝ) (i : TreeCoord (frameAtStep L n k j)),
      levelCoords j (covDiff (levelField X j) (g z)) (.inr i) = z i := by
    intro z i
    obtain ⟨⟨b, hbt⟩, c⟩ := i
    have hp := isPositivelyOriented_edgeOfCoords hb hL hn j.2 b
    have ht : IsAxialTreeBond b := (Finset.mem_filter.mp hbt).2
    have hW : levelField X j (edgeOfCoords j b) = 1 := by
      rw [hlev a ρ L hL k n hn V X hR j j.2 b]
      have e : fieldAboveFrame true a ρ 0 (topFieldAtStep a ρ L n k j V) 0 b.1 b.2 = 1 := by
        have hcr : ¬ IsCrossingBond (b.1, b.2) := ht.1
        have ht' : IsAxialTreeBond (b.1, b.2) := ht
        simp only [fieldAboveFrame, chartedField, if_neg hcr, if_pos ht']
      rw [e]
      exact quaternionToMatrix_one
    show suTwoComponents (covDiff (levelField X j) (g z) (edgeOfCoords j b)) c = _
    rw [covDiff_of_isPositivelyOriented _ _ _ hp, hW, conjugateBy_one, hgt z b hbt,
      suTwoComponents_suTwoMatrix]
    simp [treeData, hbt]
  refine ⟨Matrix.fromBlocks (chordDerivMatrix w) C 0 1, ?_, fun u => ?_⟩
  · have e := Matrix.det_fromBlocks_zero₂₁ (chordDerivMatrix w) C
      (1 : Matrix (TreeCoord (frameAtStep L n k j)) (TreeCoord (frameAtStep L n k j)) ℝ)
    rw [Matrix.det_one, mul_one, det_chordDerivMatrix w hre] at e
    rw [Real.exp_sum, ← Finset.prod_congr rfl fun b _ => (exp_haarLogRatio _ (hlt b)).symm]
    convert e
    rfl
  · have hmul := Matrix.fromBlocks_mulVec (chordDerivMatrix w) C 0
      (1 : Matrix (TreeCoord (frameAtStep L n k j)) (TreeCoord (frameAtStep L n k j)) ℝ) u
    have hinr : ∀ i, Matrix.mulVec (Matrix.fromBlocks (chordDerivMatrix w) C 0
        (1 : Matrix (TreeCoord (frameAtStep L n k j)) (TreeCoord (frameAtStep L n k j)) ℝ)) u (.inr i) =
          u (.inr i) := by
      intro i
      rw [hmul]
      simp
    have hinl : ∀ i, Matrix.mulVec (Matrix.fromBlocks (chordDerivMatrix w) C 0
        (1 : Matrix (TreeCoord (frameAtStep L n k j)) (TreeCoord (frameAtStep L n k j)) ℝ)) u (.inl i) =
        Matrix.mulVec (chordDerivMatrix w) (u ∘ Sum.inl) i + Matrix.mulVec C (u ∘ Sum.inr) i := by
      intro i
      rw [hmul]
      simp
    refine ⟨⟨g (u ∘ Sum.inr), hgm _, hgr _, ?_⟩, hinr⟩
    rintro (i | i)
    · rw [hinl, chordDerivMatrix_mulVec, hC]
      congr 1
      show _ = imaginaryComponents (expLeftDeriv (minimizerCoordAtStep a ρ L n k j V i.1 : ℍ[ℝ])
        (toImaginary (WithLp.toLp 2 fun c => u (.inl (i.1, c))) : ℍ[ℝ])) i.2
      rw [imaginaryComponents_expLeftDeriv _ _ (minimizerCoordAtStep a ρ L n k j V i.1).2 (toImaginary _).2,
        imaginaryComponents_toImaginary]
      rfl
    · rw [hinr, htree]
      show _ = 0 + _
      simp
end Assembly
end LevelFormMap
open LevelFormMap in
theorem existsLevelFormMap_holds
    (hlev : ChainLevelIsStepMinimizer)
    (hb : FramePositiveEdgesBijective)
    (hs : SiteDecomposition) :
    ExistsLevelFormMap := by
  classical
  intro a ha L hL k n hn ρ h0 h1
  refine Filter.Eventually.of_forall fun V W hW X hX hR => ?_
  choose M hdet hM using fun j : Fin (k + 1) => exists_level_matrix hlev hb hs h0 h1 hL hn V X hR j
  refine ⟨Matrix.blockDiagonal' M, ?_, fun u => ⟨fun j => ?_, fun j i => ?_⟩⟩
  · rw [det_blockDiagonal'_eq_prod, Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => hdet j
  · obtain ⟨⟨g, hg, hr, he⟩, -⟩ := hM j (fun e => u ⟨j, e⟩)
    refine ⟨g, hg, hr, fun e => ?_⟩
    rw [mulVec_blockDiagonal'_apply]
    exact he e
  · rw [mulVec_blockDiagonal'_apply]
    exact (hM j _).2 i
end YangMills.Construction.RunningCouplingSlope
end
