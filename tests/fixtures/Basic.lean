import Lean

namespace Example

def base : Nat := 7
def derived : Nat := base + 1

theorem helper : derived = 8 := rfl

/-- This declaration should be deleted. -/
theorem irrelevant : 2 + 2 = 4 := rfl

/-- Keep this documentation and the original proof. -/
theorem target : derived = 8 := by
  exact helper

theorem later : True := by trivial

end Example
