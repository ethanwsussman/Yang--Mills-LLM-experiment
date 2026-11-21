import YangMills.Construction.ColdChainAtEveryLevel.AveragesAndLocalSizesOfALevelProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdChainAtEveryLevel.LeastValuesOfAChainProof
import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages
def CutActionEqualsMinimalAction : Prop :=
  ∀ (F : BlockFrame) (a : ℝ), 0 ≤ a →
    (∀ (j : ℕ) (X : Finset (F.Site j)) (V : F.GaugeField j), 0 ≤ cutEffectiveAction a j X V ∧
      ∀ U : F.FieldChain, U j = V → cutEffectiveAction a j X V ≤ cutChainEnergy a j X U) ∧
    (Odd F.blockSide → ∀ (S : Finset F.Cell) (j : ℕ), j ≤ F.top → ∀ V : F.GaugeField j,
      cutEffectiveAction a j (sitesOfCells S j) V = minimalAction a S j V)
end YangMills.Construction.LumpContours
end

noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace LumpContours
open BlockAverages
namespace CutAction
variable {F : BlockFrame}
theorem norm_eq_one_of_mem_unitary {q : ℍ[ℝ]} (hq : q ∈ unitary ℍ[ℝ]) : ‖q‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.norm_eq_one_of_mem_unitary <;> assumption
theorem re_le_norm (q : ℍ[ℝ]) : q.re ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.quaternion_re_le_norm <;> assumption
theorem plaquetteEnergy_nonneg (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) :
    0 ≤ plaquetteEnergy U p := by
  unfold plaquetteEnergy
  have hre := re_le_norm ((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ])
  rw [norm_eq_one_of_mem_unitary (plaquetteHolonomy U p).2] at hre
  linarith
theorem siteOfCoords_add (j : ℕ) (u v : Fin 4 → ℤ) :
    (siteOfCoords j (u + v) : F.Site j) = siteOfCoords j u + siteOfCoords j v := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem period_eq_mul_pow {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (k : Fin 4) :
    F.period i k = F.period j k * F.blockSide ^ (j - i) := by
  simp only [BlockFrame.period]
  rw [mul_assoc, ← pow_add]
  congr 2
  omega
theorem siteOfCoords_scale_siteCoords {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (u e : Fin 4 → ℤ) :
    (siteOfCoords i (fun k => (F.blockSide : ℤ) ^ (j - i) * siteCoords (siteOfCoords j u : F.Site j) k + e k) :
        F.Site i) =
      siteOfCoords i fun k => (F.blockSide : ℤ) ^ (j - i) * u k + e k := by
  funext k
  simp only [siteOfCoords]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have hcoord : (((siteCoords (siteOfCoords j u : F.Site j) k : ℤ)) : ZMod (F.period j k)) =
      ((u k : ℤ) : ZMod (F.period j k)) := by
    simp [siteCoords, siteOfCoords]
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hcoord
  refine ⟨c, ?_⟩
  rw [period_eq_mul_pow hij hj k]
  push_cast
  linear_combination ((F.blockSide : ℤ) ^ (j - i)) * hc
theorem mem_centredCube (M : ℕ) (x : Fin 4 → ℤ) :
    x ∈ centredCube M ↔ ∀ k, -(((M : ℤ) - 1) / 2) ≤ x k ∧ x k ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LatticePaths.mem_centredCube_iff <;> assumption
theorem ediv_two_of_odd {M : ℕ} {m : ℤ} (hM : (M : ℤ) = 2 * m + 1) : ((M : ℤ) - 1) / 2 = m := by
  omega
theorem ediv_two_of_odd_mul {A B : ℕ} {a b : ℤ} (hA : (A : ℤ) = 2 * a + 1) (hB : (B : ℤ) = 2 * b + 1) :
    (((A * B : ℕ) : ℤ) - 1) / 2 = A * b + a := by
  have hsub : (((A * B : ℕ) : ℤ) - 1) = 2 * ((A : ℤ) * b + a) := by
    push_cast
    rw [hB]
    linear_combination hA
  rw [hsub]
  simp
theorem centredCube_combine {A B : ℕ} (hA : Odd A) (hB : Odd B) {x y : Fin 4 → ℤ} (hx : x ∈ centredCube B)
    (hy : y ∈ centredCube A) : (fun k => (A : ℤ) * x k + y k) ∈ centredCube (A * B) := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.mul_add_mem_centredCube <;> assumption
theorem centredCube_decompose {A B : ℕ} (hA : Odd A) (hB : Odd B) {x : Fin 4 → ℤ}
    (hx : x ∈ centredCube (A * B)) :
    ∃ y ∈ centredCube B, ∃ z ∈ centredCube A, x = fun k => (A : ℤ) * y k + z k := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hA' : (A : ℤ) = 2 * (a : ℤ) + 1 := by exact_mod_cast ha
  have hB' : (B : ℤ) = 2 * (b : ℤ) + 1 := by exact_mod_cast hb
  rw [mem_centredCube, ediv_two_of_odd_mul hA' hB'] at hx
  have hpos : (0 : ℤ) < A := by omega
  refine ⟨fun k => (x k + a) / A, ?_, fun k => (x k + a) % A - a, ?_, ?_⟩
  · rw [mem_centredCube, ediv_two_of_odd hB']
    intro k
    obtain ⟨hx₁, hx₂⟩ := hx k
    constructor
    · apply Int.le_ediv_of_mul_le hpos
      nlinarith
    · have hlt : (x k + a) / A < (b : ℤ) + 1 := by
        apply Int.ediv_lt_of_lt_mul hpos
        nlinarith
      omega
  · rw [mem_centredCube, ediv_two_of_odd hA']
    intro k
    have hr₁ := Int.emod_nonneg (x k + a) hpos.ne'
    have hr₂ := Int.emod_lt_of_pos (x k + a) hpos
    constructor <;> omega
  · funext k
    have hdiv := Int.mul_ediv_add_emod (x k + a) A
    simp only
    linarith
theorem cutBelow_sitesOfCells (hL : Odd F.blockSide) (S : Finset F.Cell) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ F.top) : cutBelow i (sitesOfCells S j) = sitesOfCells S i := by
  have hA : Odd (F.blockSide ^ (j - i)) := hL.pow
  have hB : Odd (F.blockSide ^ (F.top - j)) := hL.pow
  have hAB : F.blockSide ^ (F.top - i) = F.blockSide ^ (j - i) * F.blockSide ^ (F.top - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hsite : ∀ (z : F.Cell) (y w : Fin 4 → ℤ),
      (siteOfCoords i (fun k => (F.blockSide : ℤ) ^ (j - i) *
          siteCoords (cellCentre j z + siteOfCoords j y : F.Site j) k + w k) : F.Site i) =
        cellCentre i z + siteOfCoords i fun k => ((F.blockSide ^ (j - i) : ℕ) : ℤ) * y k + w k := by
    intro z y w
    have hcentre : (cellCentre j z + siteOfCoords j y : F.Site j) =
        siteOfCoords j ((fun k => (F.blockSide : ℤ) ^ (F.top - j) * siteCoords z k) + y) := by
      rw [siteOfCoords_add]
      rfl
    rw [hcentre, siteOfCoords_scale_siteCoords hij hj]
    funext k
    have hpow : ((F.blockSide : ZMod (F.period i k))) ^ (F.top - i) =
        (F.blockSide : ZMod (F.period i k)) ^ (j - i) * (F.blockSide : ZMod (F.period i k)) ^ (F.top - j) := by
      rw [← pow_add]
      congr 1
      omega
    simp only [cellCentre, siteOfCoords, Pi.add_apply]
    push_cast
    rw [hpow]
    ring
  ext x
  simp only [cutBelow, sitesOfCells, sitesBelow, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨s, ⟨z, hz, y, hy, rfl⟩, w, hw, rfl⟩
    exact ⟨z, hz, _, hAB ▸ centredCube_combine hA hB hy hw, (hsite z y w).symm⟩
  · rintro ⟨z, hz, e, he, rfl⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := centredCube_decompose hA hB (hAB ▸ he)
    exact ⟨cellCentre j z + siteOfCoords j y, ⟨z, hz, y, hy, rfl⟩, w, hw, hsite z y w⟩
def chainEnergyUpTo (a : ℝ) (S : Finset F.Cell) (j : ℕ) (U : F.FieldChain) : ℝ :=
  wilsonAction S (U 0) + a * ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1), blockFit (U i) (U (i + 1)) c
theorem cutChainEnergy_sitesOfCells (hL : Odd F.blockSide) (a : ℝ) (S : Finset F.Cell) {j : ℕ}
    (hj : j ≤ F.top) (U : F.FieldChain) :
    cutChainEnergy a j (sitesOfCells S j) U = chainEnergyUpTo a S j U := by
  unfold cutChainEnergy chainEnergyUpTo
  rw [cutBelow_sitesOfCells hL S (Nat.zero_le j) hj]
  congr 2
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cutBelow_sitesOfCells hL S (by have := Finset.mem_range.1 hi; omega) hj]
  rfl
theorem chainEnergyUpTo_succ (a : ℝ) (S : Finset F.Cell) (j : ℕ) (U : F.FieldChain) :
    chainEnergyUpTo a S (j + 1) U =
      chainEnergyUpTo a S j U + a * ∑ c ∈ innerBonds S (j + 1), blockFit (U j) (U (j + 1)) c := by
  unfold chainEnergyUpTo
  rw [Finset.sum_range_succ]
  ring
theorem minimalAction_le_chainEnergyUpTo (hv : minimalChainExistenceStatement) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset F.Cell) (j : ℕ) (U : F.FieldChain) : minimalAction a S j (U j) ≤ chainEnergyUpTo a S j U := by
  induction j with
  | zero => simp [chainEnergyUpTo, minimalAction]
  | succ j ih =>
    obtain ⟨W, hW, hmin⟩ := (hv F a S ha).2.2.1 j (U (j + 1))
    have hle := hmin (U j)
    rw [hW] at hle
    rw [chainEnergyUpTo_succ]
    unfold blockEnergy at hle
    linarith
theorem exists_chain_chainEnergyUpTo_eq (hv : minimalChainExistenceStatement) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset F.Cell) (j : ℕ) (V : F.GaugeField j) :
    ∃ U : F.FieldChain, U j = V ∧ chainEnergyUpTo a S j U = minimalAction a S j V := by
  induction j with
  | zero =>
    refine ⟨Function.update (fun _ _ _ => 1) 0 V, by simp, ?_⟩
    simp [chainEnergyUpTo, minimalAction]
  | succ j ih =>
    obtain ⟨W, hW, -⟩ := (hv F a S ha).2.2.1 j V
    obtain ⟨U, rfl, hU⟩ := ih W
    refine ⟨Function.update U (j + 1) V, by simp, ?_⟩
    have e0 : Function.update U (j + 1) V 0 = U 0 := Function.update_of_ne (by omega) _ _
    have e1 : Function.update U (j + 1) V j = U j := Function.update_of_ne (by omega) _ _
    have e2 : Function.update U (j + 1) V (j + 1) = V := Function.update_self ..
    have hterm : ∀ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1),
        blockFit (Function.update U (j + 1) V i) (Function.update U (j + 1) V (i + 1)) c =
        ∑ c ∈ innerBonds S (i + 1), blockFit (U i) (U (i + 1)) c := by
      intro i hi
      have := Finset.mem_range.1 hi
      have e3 : Function.update U (j + 1) V i = U i := Function.update_of_ne (by omega) _ _
      have e4 : Function.update U (j + 1) V (i + 1) = U (i + 1) := Function.update_of_ne (by omega) _ _
      rw [e3, e4]
    have hlow : chainEnergyUpTo a S j (Function.update U (j + 1) V) = chainEnergyUpTo a S j U := by
      unfold chainEnergyUpTo
      rw [e0, Finset.sum_congr rfl hterm]
    rw [chainEnergyUpTo_succ, ← hW, hlow, hU, e1, e2]
    simp only [blockEnergy]
end CutAction
open CutAction in
theorem cutActionEqualsMinimalAction_of_minimalChainExistence (hv : minimalChainExistenceStatement) :
    CutActionEqualsMinimalAction := by
  intro F a ha
  have hnn : ∀ (j : ℕ) (X : Finset (F.Site j)) (U : F.FieldChain), 0 ≤ cutChainEnergy a j X U := by
    intro j X U
    unfold cutChainEnergy
    refine add_nonneg (Finset.sum_nonneg fun p _ => plaquetteEnergy_nonneg _ _)
      (mul_nonneg ha (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ => ?_))
    exact (hv F a ∅ ha).1 _ _ _ _
  have hbd : ∀ (j : ℕ) (X : Finset (F.Site j)) (V : F.GaugeField j),
      BddBelow (Set.range fun U : {U : F.FieldChain // U j = V} => cutChainEnergy a j X U.1) := by
    intro j X V
    refine ⟨0, ?_⟩
    rintro _ ⟨U, rfl⟩
    exact hnn j X U.1
  refine ⟨fun j X V => ⟨Real.iInf_nonneg fun U => hnn j X U.1, fun U hU => ?_⟩, fun hL S j hj V => ?_⟩
  · exact ciInf_le (hbd j X V) (⟨U, hU⟩ : {U : F.FieldChain // U j = V})
  · obtain ⟨U₀, hU₀, ht⟩ := exists_chain_chainEnergyUpTo_eq hv a ha S j V
    have : Nonempty {U : F.FieldChain // U j = V} := ⟨⟨U₀, hU₀⟩⟩
    apply le_antisymm
    · have := ciInf_le (hbd j (sitesOfCells S j) V) (⟨U₀, hU₀⟩ : {U : F.FieldChain // U j = V})
      rw [cutChainEnergy_sitesOfCells hL a S hj, ht] at this
      exact this
    · refine le_ciInf fun U => ?_
      rw [cutChainEnergy_sitesOfCells hL a S hj]
      have := minimalAction_le_chainEnergyUpTo hv a ha S j U.1
      rwa [U.2] at this
end LumpContours
end YangMills.Construction
end
