import YangMills.Construction.ResponseInTheExpansion.TheStepsAddUpToTheMaxwellCovarianceProof
import YangMills.Construction.LawByMomentsOfTheFlow.CanonicalGaussianInTheTreeGaugeProof
import YangMills.Construction.LawByMomentsOfTheFlow.TreeGaugeOfAChain
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.MomentLaw
namespace GaugeFixing
open LatticeFractionalIntegration (basisVector)
open TorusFields (TorusSite siteOfInt unitStep TorusBond TorusPlaquette siteOfInt_add)
open TorusBlocks (blockCentreSite blockCentreSite_apply_add parentBlock_blockCentreSite_add exists_eq_blockCentreSite_add)
open TorusLumps (parentBlock offsetFromCentre_add_of_dvd offsetFromCentre_spec stepBlockFrame)
open LumpContours (offsetFromCentre)
open StepCosts (chartBonds torusSiteInFrame)
open TopLevelSites (halfWidth isAxialTreeBond_torusSiteInFrame_iff)
open TorusContours (contourIndex contourWeight contourWord pathToWord)
open TorusPaths (BondWord)
open BlockAverages (PathStep reversePath bondContour IsAxialTreeBond)
open FlatPairing (stepDisplacement)
open WeightedResponses (curl)
open LatticePaths (card_centredCube)
section Torus
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem exists_potential_axialGradient (hL : Odd L) (h2 : 2 ≤ n) (A : TorusBond (n * L) → ℝ)
    (ψ : TorusSite n → ℝ) :
    ∃ ψ' : TorusSite (n * L) → ℝ, (∀ Y, ψ' (blockCentreSite L Y) = ψ Y) ∧
      ∀ b ∉ chartBonds L n, latticeGradient ψ' b = A b := by apply _root_.YangMills.SharedProofs.p73176 <;> assumption
private theorem contourAverage_latticeGradient (hL : Odd L) (f : TorusSite (n * L) → ℝ) (c : TorusBond n) :
    contourAverage L (latticeGradient f) c =
      f (blockCentreSite L (c.1 + unitStep n c.2)) - f (blockCentreSite L c.1) := by apply _root_.YangMills.SharedProofs.p24879 <;> assumption
end Torus
section Chains
variable {L : ℕ} [NeZero L]
variable {n : ℕ}
private theorem chainTop_map_add : ∀ (s n : ℕ) (X Y : LevelChain L s n),
    chainTop s n (X + Y) = chainTop s n X + chainTop s n Y
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem chainTop_map_smul : ∀ (s n : ℕ) (r : ℝ) (X : LevelChain L s n),
    chainTop s n (r • X) = r • chainTop s n X
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem chainLower_map_add {s : ℕ} (X Y : LevelChain L (s + 1) n) :
    chainLower (X + Y) = chainLower X + chainLower Y := rfl
private theorem chainLower_map_smul {s : ℕ} (r : ℝ) (X : LevelChain L (s + 1) n) :
    chainLower (r • X) = r • chainLower X := rfl
private theorem chainDefect_map_add [NeZero n] {s : ℕ} (X Y : LevelChain L (s + 1) n) (e : Fin 3)
    (c : TorusBond n) :
    chainDefect (X + Y) e c = chainDefect X e c + chainDefect Y e c := by apply _root_.YangMills.SharedProofs.p32985 <;> assumption
private theorem chainDefect_map_smul [NeZero n] {s : ℕ} (r : ℝ) (X : LevelChain L (s + 1) n) (e : Fin 3)
    (c : TorusBond n) :
    chainDefect (r • X) e c = r * chainDefect X e c := by apply _root_.YangMills.SharedProofs.p30900 <;> assumption
private theorem curl_map_add {m : ℕ} (A B : TorusBond m → ℝ) (p : TorusPlaquette m) :
    curl (A + B) p = curl A p + curl B p := by apply _root_.YangMills.SharedProofs.p35838 <;> assumption
private theorem curl_map_smul {m : ℕ} (r : ℝ) (A : TorusBond m → ℝ) (p : TorusPlaquette m) :
    curl (r • A) p = r * curl A p := by apply _root_.YangMills.SharedProofs.p39240 <;> assumption
private def IsZeroEnergy : (s n : ℕ) → [NeZero n] → LevelChain L s n → Prop
  | 0, _, _, X => ∀ (e : Fin 3) (p : TorusPlaquette _), curl (chainTop 0 _ X e) p = 0
  | s + 1, n, _, X => IsZeroEnergy s (n * L) (chainLower X) ∧ ∀ (e : Fin 3) (c : TorusBond n), chainDefect X e c = 0
private theorem isZeroEnergy_add : ∀ (s n : ℕ) [NeZero n] (X Y : LevelChain L s n), IsZeroEnergy s n X →
    IsZeroEnergy s n Y → IsZeroEnergy s n (X + Y)
  | 0, n, _, X, Y, h1, h2 => fun e p => by
    rw [chainTop_map_add]
    show curl (chainTop 0 n X e + chainTop 0 n Y e) p = 0
    rw [curl_map_add, h1 e p, h2 e p, add_zero]
  | s + 1, n, _, X, Y, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨isZeroEnergy_add s (n * L) _ _ h1 h3, fun e c => by
      rw [chainDefect_map_add, h2 e c, h4 e c, add_zero]⟩
private theorem isZeroEnergy_smul : ∀ (s n : ℕ) [NeZero n] (r : ℝ) (X : LevelChain L s n), IsZeroEnergy s n X →
    IsZeroEnergy s n (r • X)
  | 0, n, _, r, X, h => fun e p => by
    rw [chainTop_map_smul]
    show curl (r • chainTop 0 n X e) p = 0
    rw [curl_map_smul, h e p, mul_zero]
  | s + 1, n, _, r, X, ⟨h1, h2⟩ => ⟨isZeroEnergy_smul s (n * L) r _ h1, fun e c => by
      rw [chainDefect_map_smul, h2 e c, mul_zero]⟩
private theorem isZeroEnergy_zero : ∀ (s n : ℕ) [NeZero n], IsZeroEnergy s n (0 : LevelChain L s n)
  | 0, n, _ => fun e p => by
    show curl (0 : TorusBond n → ℝ) p = 0
    simp [curl]
  | s + 1, n, _ => ⟨isZeroEnergy_zero s (n * L), fun e c => by
      have h := chainDefect_map_smul (L := L) (s := s) (n := n) (0 : ℝ) 0 e c
      rwa [zero_smul, zero_mul] at h⟩
private theorem levelEnergy_eq_zero_of_isZeroEnergy (a : ℝ) : ∀ (s n : ℕ) [NeZero n] (X : LevelChain L s n),
    IsZeroEnergy s n X → levelEnergy a s n X = 0
  | 0, n, _, X, h => by
    simp only [levelEnergy]
    refine Finset.sum_eq_zero fun p _ => ?_
    have : curlNorm (chainTop 0 n X) p = 0 := by
      unfold curlNorm
      rw [Finset.sum_eq_zero fun e _ => by rw [h e p]; simp]
      simp
    rw [this]
    simp
  | s + 1, n, _, X, ⟨h1, h2⟩ => by
    simp only [levelEnergy]
    rw [levelEnergy_eq_zero_of_isZeroEnergy a s (n * L) _ h1, zero_add]
    simp [h2]
private def zeroEnergySubmodule (s n : ℕ) [NeZero n] : Submodule ℝ (LevelChain L s n) where
  carrier := {X | IsZeroEnergy s n X}
  add_mem' := fun {X Y} hX hY => isZeroEnergy_add s n X Y hX hY
  zero_mem' := isZeroEnergy_zero s n
  smul_mem' := fun r X hX => isZeroEnergy_smul s n r X hX
private theorem isTreeGauge_add : ∀ (s n : ℕ) [NeZero n] (X Y : LevelChain L s n), IsTreeGauge s n X →
    IsTreeGauge s n Y → IsTreeGauge s n (X + Y)
  | 0, _, _, _, _, _, _ => trivial
  | s + 1, n, _, X, Y, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨fun e b hb => by
      rw [chainLower_map_add, chainTop_map_add, Pi.add_apply, Pi.add_apply, h1 e b hb, h3 e b hb, add_zero],
    isTreeGauge_add s (n * L) _ _ h2 h4⟩
private theorem isTreeGauge_smul : ∀ (s n : ℕ) [NeZero n] (r : ℝ) (X : LevelChain L s n), IsTreeGauge s n X →
    IsTreeGauge s n (r • X)
  | 0, _, _, _, _, _ => trivial
  | s + 1, n, _, r, X, ⟨h1, h2⟩ => ⟨fun e b hb => by
      rw [chainLower_map_smul, chainTop_map_smul, Pi.smul_apply, Pi.smul_apply, h1 e b hb, smul_zero],
    isTreeGauge_smul s (n * L) r _ h2⟩
private theorem isTreeGauge_zero : ∀ (s n : ℕ) [NeZero n], IsTreeGauge s n (0 : LevelChain L s n)
  | 0, _, _ => trivial
  | s + 1, n, _ => ⟨fun e b _ => by
      have h := chainTop_map_smul s (n * L) 0 (chainLower (0 : LevelChain L (s + 1) n))
      rw [zero_smul] at h
      have h' : chainLower (0 : LevelChain L (s + 1) n) = 0 := rfl
      rw [h', h]
      simp, isTreeGauge_zero s (n * L)⟩
private def treeGaugeSubmodule (s n : ℕ) [NeZero n] : Submodule ℝ (LevelChain L s n) where
  carrier := {X | IsTreeGauge s n X}
  add_mem' := fun {X Y} hX hY => isTreeGauge_add s n X Y hX hY
  zero_mem' := isTreeGauge_zero s n
  smul_mem' := fun r X hX => isTreeGauge_smul s n r X hX
private def chainOfLowerAndTop {s n : ℕ} (B : LevelChain L s (n * L)) (A : ColourForm n) :
    LevelChain L (s + 1) n := fun e =>
  (Sum.elim (B e) (A e) : LevelBond L s (n * L) ⊕ TorusBond n → ℝ)
private theorem curl_latticeGradient {m : ℕ} (f : TorusSite m → ℝ) (p : TorusPlaquette m) :
    curl (latticeGradient f) p = 0 := by apply _root_.YangMills.DeltaSharedProofs.p500719 <;> assumption
private theorem exists_zeroEnergy_gauge_split (hL : Odd L) : ∀ (s n : ℕ) [NeZero n], 2 ≤ n →
    ∀ (X : LevelChain L s n) (ψ : Fin 3 → TorusSite n → ℝ), ∃ k : LevelChain L s n, IsZeroEnergy s n k ∧
      chainTop s n k = (fun e => latticeGradient (ψ e)) ∧ IsTreeGauge s n (X - k)
  | 0, n, _, _, _, ψ => ⟨fun e => latticeGradient (ψ e), fun e p => curl_latticeGradient (ψ e) p, rfl, trivial⟩
  | s + 1, n, _, h2, X, ψ => by
    choose ψ' hc ht using fun e : Fin 3 =>
      exists_potential_axialGradient hL h2 (chainTop s (n * L) (chainLower X) e) (ψ e)
    obtain ⟨k, hk, htop, htree⟩ := exists_zeroEnergy_gauge_split hL s (n * L)
      (h2.trans (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero (NeZero.ne L)))) (chainLower X) ψ'
    refine ⟨chainOfLowerAndTop k fun e => latticeGradient (ψ e), ⟨hk, fun e c => ?_⟩, rfl, ⟨fun e b hb => ?_, htree⟩⟩
    · show latticeGradient (ψ e) c - contourAverage L (chainTop s (n * L) k e) c = 0
      rw [htop]
      show latticeGradient (ψ e) c - contourAverage L (latticeGradient (ψ' e)) c = 0
      rw [contourAverage_latticeGradient hL, hc, hc]
      simp [latticeGradient]
    · show chainTop s (n * L) (chainLower X - k) e b = 0
      have e1 : chainLower X - k = chainLower X + (-1 : ℝ) • k := by
        rw [neg_one_smul, ← sub_eq_add_neg]
      rw [e1, chainTop_map_add, chainTop_map_smul, htop]
      show chainTop s (n * L) (chainLower X) e b + (-1 : ℝ) * latticeGradient (ψ' e) b = 0
      rw [ht e b hb]
      ring
end Chains
end GaugeFixing
open GaugeFixing
theorem treeGaugeFixing : treeGaugeFixingStatement := by
  classical
  intro L _ hL s n _ h64
  have h2 : 2 ≤ n := by omega
  set K := zeroEnergySubmodule (L := L) s n with hK
  set T := treeGaugeSubmodule (L := L) s n with hT
  have hsurj : LinearMap.range (K.mkQ ∘ₗ T.subtype) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro q
    obtain ⟨X, rfl⟩ := K.mkQ_surjective q
    obtain ⟨k, hk, -, ht⟩ := exists_zeroEnergy_gauge_split hL s n h2 X fun _ _ => 0
    refine ⟨⟨X - k, ht⟩, ?_⟩
    show K.mkQ (X - k) = K.mkQ X
    rw [map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero K).2 hk, sub_zero]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective _ hsurj
  let R : LevelChain L s n →ₗ[ℝ] LevelChain L s n := T.subtype ∘ₗ g ∘ₗ K.mkQ
  have hRT : ∀ x, IsTreeGauge s n (R x) := fun x => (g (K.mkQ x)).2
  have hRK : ∀ x, IsZeroEnergy s n (R x - x) := by
    intro x
    have h1 : K.mkQ (R x) = K.mkQ x := LinearMap.congr_fun hg (K.mkQ x)
    have h3 : K.mkQ (R x - x) = 0 := by rw [map_sub, h1, sub_self]
    exact (Submodule.Quotient.mk_eq_zero K).1 h3
  exact ⟨R, fun X => ⟨hRT X, fun a => levelEnergy_eq_zero_of_isZeroEnergy a s n _ (hRK X)⟩⟩
end YangMills.Construction.MomentLaw
end
