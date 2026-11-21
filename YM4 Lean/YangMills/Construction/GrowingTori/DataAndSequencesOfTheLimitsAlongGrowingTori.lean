import YangMills.Construction.FamiliesOfLimits.FamiliesOfLimitsDefs
import YangMills.Construction.GrowingTori.MultilinearFunctionalsOnTuplesAndPartialFamilies
import YangMills.Construction.GrowingTori.TuplesClassesAndAdmissibleFamiliesOfFourSpace
import Mathlib
set_option autoImplicit false
open Filter Set
noncomputable section
namespace YangMills.Construction.ToriLimits
structure Setup where
  params : FamiliesOfLimits.LimitSetup
  settingFloor : params.SettingFloor
  large_L : 8 * 105 ^ 4 ≤ params.L
  g : ℝ
  isReferenceCoupling : params.IsReferenceCoupling g
namespace Setup
variable (D : Setup)
abbrev L : ℕ := D.params.L
abbrev M : ℕ := D.params.choice.M
theorem admissible : Conventions.IsAdmissibleBlockingFactor D.L :=
  D.params.standingConstraints.factor_admissible
theorem one_lt_L : 1 < D.L := D.params.one_lt_L
theorem one_le_M : 1 ≤ D.M := D.params.toGrowth.one_le_M
abbrev referenceExponent : ℕ := D.params.referenceExponent D.g
def expectation (K m : ℕ+) (β : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (PeriodicLattice.Bond D.L m (K : ℤ) → Matrices.ComplexMatrix2) → E) : E :=
  PeriodicLattice.gibbsExpectation D.L m K β F
def connectedOnTorus (K m : ℕ+) (β : ℝ) {n : ℕ}
    (f : Fin n → PeriodicLattice.FourTorus D.L m → ℝ) : ℂ :=
  SchwingerFunctions.connectedSchwinger D.L m K β f
def centredOnTorus (K m : ℕ+) (β : ℝ) {q : ℕ}
    (f : Fin q → PeriodicLattice.FourTorus D.L m → ℝ) : ℂ :=
  SchwingerFunctions.centredSchwinger D.L m K β f
def connectedOnFourSpace (K m : ℕ+) (β : ℝ) {n : ℕ} (f : Fin n → RealFn) : ℂ :=
  D.connectedOnTorus K m β (SchwingerFunctions.periodizeAll D.L m f)
def centredOnFourSpace (K m : ℕ+) (β : ℝ) : {q : ℕ} → (Fin q → RealFn) → ℂ
  | 0, _ => 1
  | 1, _ => 0
  | _ + 2, h => D.centredOnTorus K m β (SchwingerFunctions.periodizeAll D.L m h)
end Setup
structure ToriSequence (D : Setup) where
  K : ℕ+ → ℕ+
  m : ℕ+ → ℕ+
  β : ℕ+ → ℝ
  β_pos : ∀ j, 0 < β j
  referenceExponent_le : ∀ j, D.referenceExponent ≤ (m j : ℕ)
  K_tendsto : Tendsto (fun j => (K j : ℕ)) atTop atTop
  m_tendsto : Tendsto (fun j => (m j : ℕ)) atTop atTop
namespace ToriSequence
variable {D : Setup} (S : ToriSequence D)
abbrev side (j : ℕ+) : ℝ := PeriodicLattice.torusSide D.L (S.m j)
theorem side_tendsto : Tendsto S.side atTop atTop := by
  have hL : (1 : ℝ) < D.L := by exact_mod_cast D.one_lt_L
  exact ((tendsto_pow_atTop_atTop_of_one_lt hL).comp S.m_tendsto).const_mul_atTop (by norm_num)
def spacing (j : ℕ+) : ℝ := PeriodicLattice.meshSize D.L (S.K j)
def radius (j : ℕ+) : ℝ := ((D.L : ℝ) ^ (S.m j : ℕ) - 2) / 2
def expectation (j : ℕ+) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (PeriodicLattice.Bond D.L (S.m j) (S.K j : ℤ) → Matrices.ComplexMatrix2) → E) : E :=
  D.expectation (S.K j) (S.m j) (S.β j) F
def connected (j : ℕ+) {n : ℕ} (f : Fin n → RealFn) : ℂ :=
  D.connectedOnFourSpace (S.K j) (S.m j) (S.β j) f
def centred (j : ℕ+) {q : ℕ} (h : Fin q → RealFn) : ℂ :=
  D.centredOnFourSpace (S.K j) (S.m j) (S.β j) h
def functional (j : ℕ+) (n : ℕ) :
    GrowingTori.lipTuplesInBall D.L n (S.radius j) → ℂ :=
  fun f => S.connected j f.1
def functionals (j : ℕ+) (n : ℕ) (_hn : 2 ≤ n) :
    GrowingTori.lipTuplesInBall D.L n (S.radius j) → ℂ :=
  S.functional j n
def IsSideIndex (n : ℕ) (R : ℝ) (j₀ : ℕ+) : Prop :=
  ∀ j, j₀ ≤ j → 16 * (n : ℝ) * (1 + R) ≤ S.side j
theorem exists_isSideIndex (n : ℕ) (R : ℝ) : ∃ j₀, S.IsSideIndex n R j₀ :=
  eventually_atTop.1 (S.side_tendsto.eventually_ge_atTop _)
open Classical in
def firstIndex (n : ℕ) (R : ℝ) : ℕ+ := PNat.find (S.exists_isSideIndex n R)
theorem isSideIndex_firstIndex (n : ℕ) (R : ℝ) :
    S.IsSideIndex n R (S.firstIndex n R) := by
  classical
  exact PNat.find_spec (S.exists_isSideIndex n R)
end ToriSequence
end YangMills.Construction.ToriLimits
end
