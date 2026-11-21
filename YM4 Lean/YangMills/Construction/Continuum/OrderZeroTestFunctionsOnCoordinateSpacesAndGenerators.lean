import YangMills.Construction.Continuum.SymbolsOfFourSpaceWithATimeAxis
import Mathlib
set_option autoImplicit false
open Filter Topology TopologicalSpace
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.ReflectionSpaces
open YangMills.Construction.TorusTransport.TestFunctionOrders
def orderZeroMoments : ℂ →ₗ[ℂ] ℂ :=
  LinearMap.id
def composeOrdered (ψ : ∀ q : ℕ, Configuration q → Configuration q) :
    {q : ℕ} → OrderedTestFun q → OrderedTestFun q
  | 0, F₀ => F₀
  | q + 1, F => fun x => F (ψ (q + 1) x)
def composeFamily (ψ : ∀ q : ℕ, Configuration q → Configuration q) (F : TestFamily) :
    TestFamily :=
  fun _ => composeOrdered ψ (F _)
def upperHalfOpen : Opens (Fin 4 → ℝ) where
  carrier := YangMills.Construction.TimeAxisSymbols.posTimeHalf
  is_open' := isOpen_lt continuous_const (continuous_apply 3)
namespace Euclidean
abbrev Coord (n : ℕ) : Type := Fin n → ℝ
variable {n : ℕ}
def partialDeriv {k : ℕ} (c : Fin k → Fin n) (F : Coord n → ℂ) : Coord n → ℂ :=
  fun x => iteratedFDeriv ℝ k F x fun j => Pi.single (c j) 1
abbrev DerivIndex (n ν : ℕ) : Type := Σ k : Fin (ν + 1), (Fin k → Fin n)
def cNorm (ν : ℕ) (F : Coord n → ℂ) : ℝ :=
  ⨆ p : DerivIndex n ν, YangMills.Construction.TestFunctions.uniformNorm (partialDeriv p.2 F)
def testFunctionSpace (W : Opens (Coord n)) : Submodule ℂ (Coord n → ℂ) where
  carrier := {F | ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ W}
  add_mem' := by
    rintro F G ⟨hF, cF, sF⟩ ⟨hG, cG, sG⟩
    exact ⟨hF.add hG, cF.add cG, (tsupport_add F G).trans (Set.union_subset sF sG)⟩
  zero_mem' := by
    refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
    simp [tsupport]
  smul_mem' := by
    rintro a F ⟨hF, cF, sF⟩
    have hs : Function.support (a • F) ⊆ Function.support F :=
      Function.support_const_smul_subset a F
    exact ⟨hF.const_smul a, cF.mono hs, (closure_mono hs).trans sF⟩
variable {W W' : Opens (Coord n)}
def HasOrderBound (T : Module.Dual ℂ (testFunctionSpace W)) (K : Set (Coord n)) (ν : ℕ) :
    Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ F : testFunctionSpace W, tsupport (F : Coord n → ℂ) ⊆ K →
    ‖T F‖ ≤ C * cNorm ν (F : Coord n → ℂ)
structure Distribution (W : Opens (Coord n)) where
  form : Module.Dual ℂ (testFunctionSpace W)
  bound : ∀ K : Set (Coord n), IsCompact K → K ⊆ W → ∃ ν : ℕ, HasOrderBound form K ν
def Distribution.HasOrderLE (T : Distribution W) (ν₀ : ℕ) : Prop :=
  ∀ K : Set (Coord n), IsCompact K → K ⊆ W → HasOrderBound T.form K ν₀
def inclusionMap (h : W' ≤ W) : testFunctionSpace W' →ₗ[ℂ] testFunctionSpace W where
  toFun F := ⟨F.1, F.2.1, F.2.2.1, F.2.2.2.trans h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def Distribution.restrict (T : Distribution W) (h : W' ≤ W) : Distribution W' where
  form := T.form ∘ₗ inclusionMap h
  bound K hK hKW := by
    obtain ⟨ν, C, hC, hb⟩ := T.bound K hK (hKW.trans h)
    exact ⟨ν, C, hC, fun F hF => hb (inclusionMap h F) hF⟩
def TendstoInTest (G : YangMills.Construction.TorusTransport.PositiveNat → testFunctionSpace W)
    (F : testFunctionSpace W) : Prop :=
  (∃ K : Set (Coord n), IsCompact K ∧ K ⊆ W ∧ tsupport (F : Coord n → ℂ) ⊆ K ∧
      ∀ t, tsupport (G t : Coord n → ℂ) ⊆ K) ∧
    ∀ ν : ℕ, Tendsto (fun t => cNorm ν ((G t : Coord n → ℂ) - (F : Coord n → ℂ))) atTop (𝓝 0)
end Euclidean
end YangMills.Construction.ReflectionSpaces
end
