import YangMills.Construction.PassageToTheLimit.ModuliOfContinuityOfAFunctionOfClassC1
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal Topology
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
namespace MirrorTranslation
variable (s : Conventions.StandingParameters)
def ReflectTranslateIdentities (E : Ambient) (μ : Fin 4) (Z : Type) : Prop :=
  ∀ (c c' : ℝ) (v : E.Carrier s) (f : E.Carrier s → Z),
    E.reflectFun s μ c' f =
        E.translateFunVec s ((2 * (c' - c)) • stdBasisVec μ) (E.reflectFun s μ c f) ∧
      ∀ w : Fin 4 → ℝ, E.IsLiftOf s v w →
        E.reflectFun s μ (c + w μ) (E.translateFun s v f) =
          E.translateFun s v (E.reflectFun s μ c f)
def TorusReflectPeriodic (μ : Fin 4) : Prop :=
  ∀ c c' : ℝ, c' - c ∈ multiplesOf (s.side / 2) →
    Ambient.periodic.reflect s μ c' = Ambient.periodic.reflect s μ c
def ReflectLiftInvariant (E : Ambient) (μ : Fin 4) : Prop :=
  ∀ (c : ℝ) (v : E.Carrier s) (w w' : Fin 4 → ℝ), E.IsLiftOf s v w → E.IsLiftOf s v w' →
    E.reflect s μ (c + w μ) = E.reflect s μ (c + w' μ)
def TranslateModulusBound (M : SharpParameter) (E : Ambient) : Prop :=
  ∀ (f : E.c1Compact s) (u v : E.Carrier s),
    ENNReal.ofReal (E.normSharp s M (E.translateFun s u f.1 - E.translateFun s v f.1)) ≤
      Ambient.continuityModulus M f (E.pointDist s u v).toNNReal
def ReflectModulusBound (M : SharpParameter) (E : Ambient) (μ : Fin 4) : Prop :=
  ∀ (f : E.c1Compact s) (c c' : ℝ),
    ENNReal.ofReal
        (E.normSharp s M (E.reflectFun s μ c' f.1 - E.reflectFun s μ c f.1)) ≤
      Ambient.continuityModulus M f (2 * |c' - c|).toNNReal
def ModulusFiniteTendsZero (M : SharpParameter) (E : Ambient) : Prop :=
  ∀ f : E.c1Compact s,
    (∀ δ : ℝ≥0, Ambient.continuityModulus M f δ < ∞) ∧
      Filter.Tendsto (Ambient.continuityModulus M f) (𝓝 0) (𝓝 0)
def Claim : Prop :=
  ∀ (s : Conventions.StandingParameters) (M : SharpParameter) (E : Ambient) (μ : Fin 4),
    ReflectTranslateIdentities s E μ ℝ ∧ ReflectTranslateIdentities s E μ ℂ ∧
      TorusReflectPeriodic s μ ∧
      ReflectLiftInvariant s E μ ∧
      TranslateModulusBound s M E ∧
      ReflectModulusBound s M E μ ∧
      ModulusFiniteTendsZero s M E
end MirrorTranslation
end LimitSpaces
end YangMills.Construction
