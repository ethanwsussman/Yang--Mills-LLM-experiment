import YangMills.Construction.ClusterExpansionOfAStep.ConstantsOfTheColdChain
import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.HoleBesideASecondHole.TheInequalityOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace RenormalizationStepParameters
open BlockAverages LumpContours HoleBounds ColdStepAtMirrorFrames TorusLumps ColdChain
def CoercivityBound (cK a : ℝ) (L : ℕ) : Prop :=
  ∀ (F : BlockFrame), F.blockSide = L → IsAdmissibleAmbient F → ∀ (j : ℕ), j ≤ F.top →
    (∀ (p : F.Site j × Fin 4 × Fin 4) (U : F.FieldChain), p.2.1 < p.2.2 →
      cK * min (plaquetteDefect (U j) p ^ 2) ((L : ℝ) ^ (-4 : ℤ)) ≤ cutChainEnergy a j (plaquetteCorners p) U) ∧
    ∀ (X : Finset (F.Site j)) (V : F.GaugeField j),
      cK * ∑ p ∈ cutPlaquettes X, min (plaquetteDefect V p ^ 2) ((L : ℝ) ^ (-4 : ℤ)) ≤ cutEffectiveAction a j X V
def HoleSavingAt {L : ℕ} (g : LumpGrid L) (a κ Θ s cE : ℝ) (J₀ : ℕ) : Prop :=
  ∀ F : BlockFrame, F.blockSide = L → IsCubicTorus F 4096 →
    (L ∣ F.extent 0 → ∀ (H : Finset (Finset (F.Site F.top))), (∀ l ∈ H, IsLump g l) →
      ∀ (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Cell → F.Site F.depth) (Wl : F.GaugeField F.depth),
        HasLumpWall (cellsOffLumps F H) (hotLumps g s (cutBelow F.depth (cellsOffLumps F H)) W) →
        IsBaseChoice J₀ (hotLumps g s (cutBelow F.depth (cellsOffLumps F H)) W) b →
        IsMinimizingField a (cellsOffLumps F H \ lumpsNeighbourhood (hotLumps g (Θ * s) (cellsOffLumps F H) V)) V Wl →
        HoleSavingInequality g a κ s cE J₀ (cellsOffLumps F H)
          (cellsOffLumps F H \ lumpsNeighbourhood (hotLumps g (Θ * s) (cellsOffLumps F H) V))
          (hotLumps g (Θ * s) (cellsOffLumps F H) V) V W b Wl) ∧
    ∀ (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Cell → F.Site F.depth) (Wl : F.GaugeField F.depth),
      IsCold (torusCells F) F.top (Θ * s) V →
      IsBaseChoice J₀ (hotLumps g s (cutBelow F.depth (torusCells F)) W) b →
      IsMinimizingField a (torusCells F) V Wl →
      HoleSavingInequality g a κ s cE J₀ (torusCells F) (torusCells F) ∅ V W b Wl
def boxRadius (x : ℝ) : ℕ := clusterRange x / 2 ^ 11
structure ChainParameters where
  coupling : ℝ
  coercivity : ℝ
  κ : ℝ
  δ₁ : ℝ
  baseDepth : ℕ
  side : ℕ
  [side_ne : NeZero side]
  grid : LumpGrid side
  lam : ℝ
  ρA : ℝ
  σA : ℝ
  cg : ℝ
  N : ℕ → ℝ
  δc : ℝ
attribute [instance] ChainParameters.side_ne
structure ParameterAssignment extends ChainParameters where
  rt : ℝ
  η₃ : ℝ
  Ct : ℝ
  threshold : ℝ
  cutoff : ℝ → ℝ
  Cs : ℝ
  cE : ℝ
  n₀ : ℕ
  CE : ℝ
  yC : ℝ
  derivBound : ℝ
namespace ParameterAssignment
variable (T : ParameterAssignment)
def ballRadius : ℝ := T.threshold / 64
def n₁ : ℝ := (T.side : ℝ) ^ (1 / 640 : ℝ)
def κ₁ : ℝ := min (T.κ / 16) (T.cE / (4 * T.threshold ^ 2))
def gasRate : ℝ := 2⁻¹ ^ 8 * min T.cE (min (T.κ * T.threshold ^ 2) (T.κ₁ * T.threshold ^ 2))
def B : ℝ := expansionConstant T.Cs (maxOfFirstFour T.N) T.rt T.n₁
def E : ℝ := 4 * T.B
def E₃ : ℝ := T.E / T.η₃
def stepParameters (y : ℝ) : StepParameters where
  coupling := T.coupling
  side := T.side
  side_ne := T.side_ne
  grid := T.grid
  baseDepth := T.baseDepth
  threshold := T.threshold
  κ := T.κ
  κ₁ := T.κ₁
  rt := T.rt
  n₁ := T.n₁
  E := T.E
  E₃ := T.E₃
  derivBound := T.derivBound
  n₀ := T.n₀
  y₁ := y
  B := T.B
def floorMin : ℝ := max T.yC ((2 : ℝ) ^ 1600)
def weight (n : ℕ) : ℝ := (T.stepParameters 0).weight n
structure Admissible : Prop where
  a_ge : 1 ≤ T.coupling
  cK_pos : 0 < T.coercivity
  cK_le : T.coercivity ≤ 1
  coercive : CoercivityBound T.coercivity T.coupling T.side
  κ_pos : 0 < T.κ
  κ_le : T.κ ≤ 1 / 8
  δ₁_pos : 0 < T.δ₁
  J₀_ge : 625 ≤ T.baseDepth
  L_odd : Odd T.side
  L_ge : 2 ^ 40 ≤ T.side
  L_gt : 11 * 2 ^ 12 * T.baseDepth < T.side
  chain : ColdChainConstants T.coupling T.δ₁ T.side T.lam T.ρA T.σA T.cg T.N
  δc_pos : 0 < T.δc
  δc_le : T.δc ≤ T.δ₁ / 2 ^ 6
  rt_pos : 0 < T.rt
  rt_le : T.rt ≤ T.δc / 2 ^ 14
  η₃_pos : 0 < T.η₃
  η₃_le : T.η₃ ≤ 1
  Ct_pos : 0 < T.Ct
  σ_pos : 0 < T.threshold
  σ_one : T.threshold ≤ 1
  σ_L : 2 ^ 10 * (T.side : ℝ) * (T.N 0 + 1) * T.threshold ≤ 1
  σ_le : 2 * T.threshold ≤ T.σA
  ρ_le : 2 * T.N 0 * T.threshold + 2 * T.ballRadius ≤ T.ρA
  cold_le : 9 / 8 * T.threshold + 4 * (2 * T.N 0 * T.threshold + 2 * T.ballRadius) ≤ T.σA
  hole_one : HoleSavingAt T.grid T.coupling T.κ 1 T.threshold T.cE T.baseDepth
  hole_more : HoleSavingAt T.grid T.coupling T.κ (9 / 8) T.threshold T.cE T.baseDepth
  cE_pos : 0 < T.cE
  cut : IsCutoff T.ballRadius T.cutoff
  Cs_pos : 0 < T.Cs
  B_ge : 1 ≤ T.B
  n₀_ge : 4096 ≤ T.n₀
  CE_pos : 0 < T.CE
  yC_ge : 1 ≤ T.yC
  Cder_ge : 2 ^ 6 * (T.coupling + 1) ≤ T.derivBound
  fits : ∀ y : ℝ, T.floorMin ≤ y → (T.stepParameters y).Admissible
structure FloorConditions (C c x : ℝ) : Prop where
  coupling_le : 2 / T.coupling ≤ x
  drift_le : C * (1 + T.E₃) + x ^ C * Real.exp (-(c * clusterRange x)) ≤ x * T.lam / 16
  sqrt_bounds : C * (1 + T.E) + 1 ≤ Real.sqrt (x * T.lam / 4) ∧ 1 + T.E₃ ≤ Real.sqrt x
  radius_ge : 16 ≤ boxRadius x ∧ C ≤ boxRadius x
  cold_tail : C * Real.exp (-(T.δc / 4 * boxRadius x)) ≤ 2⁻¹ ^ 10 * T.threshold
  rate_tail : C * x ^ 2 * Real.exp (-(T.δc / 4 * boxRadius x)) ≤
    Real.exp (-(2 ^ 10 * T.rt * boxRadius x))
  square_tail : C * x ^ 2 * Real.exp (-(2 * T.δc * boxRadius x)) ≤ 1
  root_tail : C * Real.exp (-(T.δc / 4 * boxRadius x)) ≤ x ^ (-(1 / 2 : ℝ))
  weight_tail : ∀ n : ℕ, (n : ℝ) ≤ C → C * x ^ (-(1 / 2 : ℝ)) ≤ 2⁻¹ ^ 5 * T.E / T.weight n
  range_ge : C ≤ clusterRange x
  stretched_tail : C * x ^ C * Real.exp (-(c * clusterRange x)) ≤ Real.exp (-(x ^ (1 / 200 : ℝ))) ∧
    C * Real.exp (-(x ^ (1 / 200 : ℝ))) ≤ 1 / C
  log_powers : C * (clusterRange x : ℝ) ^ 8 * Real.log x ≤ x ^ (1 / 10 : ℝ) ∧
    C * (clusterRange x : ℝ) ^ 12 * Real.log x ≤ x ^ (1 / 6 : ℝ) ∧ x ^ (1 / 6 : ℝ) ≤ T.gasRate * x
  stable_nearby : 200 * T.B ≤ x ∧ ∀ x' : ℝ, |x' - x| ≤ 2 * T.B →
    x ≤ 1.01 * x' ∧ x' ≤ 1.01 * x ∧ clusterRange x ≤ clusterRange x' + 1 ∧ clusterRange x' ≤ clusterRange x + 1
  error_sum : C * x ^ (-(1 / 2 : ℝ)) +
      (C * x * Real.exp (-(T.δc / 8 * boxRadius x)) + Real.exp (-(T.gasRate * x / 2))) * C +
      x ^ C * Real.exp (-(c * clusterRange x)) ≤ min 1 (T.E / 64)
  gas_powers : 16 * T.rt * boxRadius x + 16 * T.rt ≤ x ^ (1 / 90 : ℝ) ∧ x ^ (1 / 90 : ℝ) ≤ T.gasRate * x ∧
    ∀ n : ℕ, x ^ C * (1 + (n : ℝ) / T.n₁) ^ 16000 *
      Real.exp (-(1 / 4 * (T.gasRate * x + T.rt * n / 2 ^ 8))) ≤ 1
  chain_tail : ∀ m : ℕ, (clusterRange x : ℝ) - 1 ≤ 64 * m →
    4 * Real.exp (-(15 / 16 * T.rt * m / 2 ^ 5)) +
        3 * Real.exp (-(T.gasRate * x) - T.rt * m / 2 ^ 8) +
        2 * x * T.N 0 * Real.exp (-(T.δ₁ * m / 2)) ≤ Real.exp (-(T.rt / 2 ^ 12 * m))
end ParameterAssignment
end RenormalizationStepParameters
end YangMills.Construction
end
