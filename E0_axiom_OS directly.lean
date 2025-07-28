import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Complex.Basic

noncomputable section
open Complex

/-ℝ⁴ as functions on `Fin 4` with 4 indicies-/
abbrev R4 : Type := Fin 4 → ℝ

/-- Schwartz test-functions. -/
abbrev TestFun (n : ℕ) : Type :=
  SchwartzMap (Fin n → R4) ℂ

/-- Distribution n is just a scalar C when n=0 and a tempered dist on a Schwartz function when n geq 1 -/
def Distribution : ℕ → Type
| 0      => ℂ
| n + 1  => TestFun (n + 1) →L[ℂ] ℂ

/-- Constant distribution 1. -/
abbrev oneDistribution : Distribution 0 := (1 : ℂ)

/-- Axiom E₀ — the 0-point Green function equals `1̂`. -/
class AxiomE0 (Ξ : ∀ n, Distribution n) : Prop where
  zero_eq_one : Ξ 0 = oneDistribution
end  -- closes the noncomputable section
/-! Test-/
section Test

/-- Toy family: `Ξtoy 0 = 1̂`; for every `n ≥ 1` it is the zero distribution. -/
noncomputable def Ξtoy : ∀ n, Distribution n
| 0      => oneDistribution
| n + 1  => (0 : TestFun (n + 1) →L[ℂ] ℂ)   -- genuine ℂ-linear zero map

/-- E₀ holds for this toy family  -/
instance : AxiomE0 Ξtoy := ⟨rfl⟩


#check (AxiomE0.zero_eq_one (Ξ := Ξtoy))

end Test
