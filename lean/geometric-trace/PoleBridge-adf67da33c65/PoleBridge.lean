import Mathlib
open Filter Topology
namespace MasulloGRH.Round7A
/-- Discharges the simple-root premise for the exact norm-twist clearing
polynomial. This computes no pole until the numerator is attached. -/
theorem clearing_derivative (t : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => (w + (t : ℂ) * Complex.I) *
      (w - (1 - (t : ℂ) * Complex.I)))
      (2 * z + 2 * (t : ℂ) * Complex.I - 1) z := by
  convert ((hasDerivAt_id z).add_const ((t : ℂ) * Complex.I)).mul
    ((hasDerivAt_id z).sub_const (1 - (t : ℂ) * Complex.I)) using 1 <;> simp only [id_eq] <;> ring
#check clearing_derivative
#print axioms clearing_derivative
run_elab do
  let env ← Lean.getEnv
  for (n, info) in env.constants.toList do
    if (n.toString.splitOn "meromorphicOrderAt").length > 1 then
      Lean.logInfo m!"{n} : {info.type}"
end MasulloGRH.Round7A
