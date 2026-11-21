import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.SeparatedSequences.ExpansionsOfACoarseRegionProof
import YangMills.Construction.Torus.AveragesOfTheExpansionTestFormsProof
import YangMills.Construction.Torus.ObjectsOfASequenceOfRegionsOnAGeneralTorusProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace GeneralTorus.ClosedMeanFree
abbrev basisVec (μ : Fin 4) : Fin 4 → ℤ := Pi.single μ 1
def periodGroup (F : (Fin 4 → ℤ) → ℝ) : AddSubgroup (Fin 4 → ℤ) where
  carrier := {v | ∀ k, F (k + v) = F k}
  add_mem' := by
    intro a b ha hb k
    rw [← add_assoc, hb, ha]
  zero_mem' := fun k => by simp
  neg_mem' := by
    intro a ha k
    have h := ha (k + -a)
    rw [neg_add_cancel_right] at h
    exact h.symm
theorem exists_discrete_primitive (g : ℤ → ℝ) : ∃ G : ℤ → ℝ, ∀ n, G (n + 1) - G n = g n := by
  let G : ℤ → ℝ := fun n => match n with
    | .ofNat n => ∑ i ∈ Finset.range n, g i
    | .negSucc n => -∑ i ∈ Finset.range (n + 1), g (-((i : ℤ) + 1))
  refine ⟨G, fun n => ?_⟩
  match n with
  | .ofNat n =>
    have e : (Int.ofNat n + 1 : ℤ) = Int.ofNat (n + 1) := rfl
    rw [e]
    simp only [G, Finset.sum_range_succ]
    simp
  | .negSucc 0 =>
    have e : (Int.negSucc 0 + 1 : ℤ) = Int.ofNat 0 := rfl
    rw [e]
    simp only [G]
    simp
  | .negSucc (n + 1) =>
    have e : (Int.negSucc (n + 1) + 1 : ℤ) = Int.negSucc n := rfl
    rw [e]
    simp only [G]
    rw [Finset.sum_range_succ _ (n + 1)]
    have e2 : -(((n + 1 : ℕ) : ℤ) + 1) = Int.negSucc (n + 1) := by
      rw [Int.negSucc_eq]
    rw [e2]
    ring
def discretePrimitive (g : ℤ → ℝ) : ℤ → ℝ := (exists_discrete_primitive g).choose
section Numbers
variable (D : ScaleData)
theorem blockFactor_pos : 0 < D.L := D.blocking.odd_blockingFactor.pos
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem levelSpacing_succ (n : ℕ) : D.levelSpacing (n + 1) = (D.L : ℝ) * D.levelSpacing n := by
  simp only [ScaleData.levelSpacing, pow_succ]
  ring
theorem levelSpacing_lt_torusSide {n : ℕ} (hn : n ≤ D.lastLevel) :
    D.levelSpacing n < D.torusSide := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.levelSpacing_lt_torusSide <;> assumption
end Numbers
section Sites
variable (D : ScaleData)
def latticePt (n : ℕ) (m : Fin 4 → ℤ) : D.SiteAt n :=
  ⟨torusProj D.torusSide fun ν => D.levelSpacing n * (m ν : ℝ), ⟨m, rfl⟩⟩
theorem latticePt_add (n : ℕ) (m m' : Fin 4 → ℤ) :
    latticePt D n (m + m') = latticePt D n m + latticePt D n m' := by
  apply Subtype.ext
  funext ν
  simp [latticePt, torusProj, mul_add]
end Sites
theorem torusSupNorm_proj_le {S b : ℝ} {v : Fin 4 → ℝ} (h : ∀ ν, |v ν| ≤ b) :
    torusSupNorm (torusProj S v) ≤ b := by apply _root_.YangMills.Construction.GeneralTorus.CoarseRegionExpansions.torusSupNorm_proj_le <;> assumption
def linPairing (c : Fin 4 → ℝ) (m : Fin 4 → ℤ) : ℝ := ∑ μ, c μ * (m μ : ℝ)
section Closed
variable {D : ScaleData}
theorem posBondDir_bondFrom {n : ℕ} (hn : n ≤ D.lastLevel) (x : D.SiteAt n) (μ : Fin 4) :
    ScaleData.posBondDir (ScaleData.bondFrom x μ) = μ := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.posBondDir_bondFrom <;> assumption
theorem tgt_eq_src_add {n : ℕ} (c : D.PosBond n) :
    c.1.tgt = c.1.src + unitStep D.torusSide (D.levelSpacing n) (ScaleData.posBondDir c) := by
  have hs := c.2.choose_spec
  show c.1.tgt = c.1.src + unitStep D.torusSide (D.levelSpacing n) c.2.choose
  rw [← hs]
  abel
theorem bondFrom_src_dir {n : ℕ} (c : D.PosBond n) :
    ScaleData.bondFrom c.1.src (ScaleData.posBondDir c) = c :=
  Subtype.ext (LatticeBond.ext rfl (tgt_eq_src_add c).symm)
end Closed
def roundDiv (N z : ℤ) : ℤ := (z + (N - 1) / 2) / N
def intBox (a : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(a : ℤ)) a
theorem mem_intBox {a : ℕ} {j : Fin 4 → ℤ} : j ∈ intBox a ↔ ∀ ν, -(a : ℤ) ≤ j ν ∧ j ν ≤ a := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.mem_cubeBox <;> assumption
theorem card_intBox (a : ℕ) : (intBox a).card = (2 * a + 1) ^ 4 := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.card_cubeBox <;> assumption
section Cubes
variable {D : ScaleData}
theorem mem_centeredBox_iff {N a : ℕ} (h : N = 2 * a + 1) {j : Fin 4 → ℤ} :
    j ∈ ScaleData.centeredBox N ↔ j ∈ intBox a := by
  rw [mem_intBox]
  simp only [ScaleData.centeredBox, Set.mem_ofPred_eq]
  refine forall_congr' fun ν => ?_
  have e : ((N : ℝ) - 1) / 2 = a := by
    rw [h]
    push_cast
    ring
  rw [e, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
def nearestCenter (D : ScaleData) (n : ℕ) (k : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun ν => roundDiv (D.blockSize n) (k ν)
end Cubes
def shiftedMean (D : ScaleData) (f : D.SiteField) (c : Fin 4 → ℝ) (n : ℕ) (m : Fin 4 → ℤ) : ℝ :=
  D.blockSiteMean n f (latticePt D n m) + D.levelSpacing n * linPairing c m
structure Hyps (W : GaugeSetting) (A : ↥W.formSubspace) (f : W.data.SiteField) (c : Fin 4 → ℝ) :
    Prop where
  hm : W.chain.SetsAreCubeUnions
  hc : W.data.CubeSubdivision
  hb : W.data.BaseBlockEqSites
  hl : W.data.CoarseBlockEqSites
  hs : DiffAndMeans.BondMeanSitesWeights W.data
  hi : DiffAndMeans.MeanCommutesGrad W.data
  hk : DiffAndMeans.MeanComposition W.data
  hA : ∀ (x : W.data.BaseSite) (μ : Fin 4),
    W.data.formComponent μ (A : W.data.BondField) x = W.data.forwardDiff μ f x + c μ
  hQ : W.meanOp A = 0
  hM : W.data.L ≤ W.data.blockCount
section Averages
variable {W : GaugeSetting} {A : ↥W.formSubspace} {f : W.data.SiteField} {c : Fin 4 → ℝ}
theorem step_identity {ξ d u u' l e : ℝ} (hξ : ξ ≠ 0) (hd : d = u' - u) (h : ξ⁻¹ * d + e = 0) :
    u' + ξ * (l + e * ((1 : ℤ) : ℝ)) = u + ξ * l := by
  have h2 : ξ * (ξ⁻¹ * d) = d := mul_inv_cancel_left₀ hξ d
  push_cast
  subst hd
  linear_combination ξ * h - h2
end Averages
section Levels
variable {D : ScaleData} (B : SeparatedChain D)
open Classical in
def depth (k : Fin 4 → ℤ) : ℕ :=
  Nat.findGreatest (fun i => (latticePt D 0 k : D.Space) ∈ B.set i) D.lastLevel
theorem le_depth {k : Fin 4 → ℤ} {i : ℕ} (hi : i ≤ D.lastLevel)
    (h : (latticePt D 0 k : D.Space) ∈ B.set i) : i ≤ depth B k := by
  classical
  exact Nat.le_findGreatest (P := fun i => (latticePt D 0 k : D.Space) ∈ B.set i) hi h
theorem set_antitone {i j : ℕ} (hij : i ≤ j) (hj : j ≤ D.lastLevel) : B.set j ⊆ B.set i := by apply _root_.YangMills.Construction.GeneralTorus.CoarseTestFormMeansAux.set_antitone <;> assumption
end Levels
section Constancy
variable {W : GaugeSetting} {A : ↥W.formSubspace} {f : W.data.SiteField} {c : Fin 4 → ℝ}
def levelValue (W : GaugeSetting) (f : W.data.SiteField) (c : Fin 4 → ℝ) (k : Fin 4 → ℤ) : ℝ :=
  shiftedMean W.data f c (depth W.chain k) (nearestCenter W.data (depth W.chain k) k)
end Constancy
end GeneralTorus.ClosedMeanFree
end YangMills.Construction
