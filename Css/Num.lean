/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Css.Escape

@[expose] public section

namespace Css

/-- An exact decimal, `mantissa × 10 ^ -exponent`, so that `1.5` renders as `1.5` rather than as
a binary float's approximation, and no value is infinite or NaN. -/
structure Num where
  mantissa : Int
  exponent : Nat := 0
  deriving DecidableEq, Repr

instance : OfNat Num n := ⟨⟨n, 0⟩⟩
instance : NatCast Num := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast Num := ⟨fun n => ⟨n, 0⟩⟩
instance : Neg Num := ⟨fun n => { n with mantissa := -n.mantissa }⟩

instance : OfScientific Num where
  ofScientific m neg e := if neg then ⟨m, e⟩ else ⟨m * 10 ^ e, 0⟩

namespace Num

/-- Drops trailing zeros after the decimal point. -/
def trim : Nat → Nat → Nat × Nat
  | m, 0 => (m, 0)
  | m, e + 1 => if m % 10 = 0 then trim (m / 10) e else (m, e + 1)

/-- Plain decimal notation, never an exponent, which `e` and a unit after it would misread. -/
def render (n : Num) : String :=
  let (m, e) := trim n.mantissa.natAbs n.exponent
  let fracDigits := Nat.toDigits 10 (m % 10 ^ e)
  let frac :=
    if e = 0 then ""
    else "." ++ String.ofList (List.replicate (e - fracDigits.length) '0' ++ fracDigits)
  (if n.mantissa < 0 && m != 0 then "-" else "") ++ String.ofList (Nat.toDigits 10 (m / 10 ^ e)) ++
    frac

private theorem digits_chars (k : Nat) :
    AllChars (fun c => c.isDigit || c == '.' || c == '-') (String.ofList (Nat.toDigits 10 k)) :=
  allChars_ofList fun c hc => by
    simp [Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc]

theorem render_chars (n : Num) : AllChars (fun c => c.isDigit || c == '.' || c == '-') n.render := by
  simp only [render, allChars_append]
  refine ⟨⟨by split <;> decide, digits_chars _⟩, ?_⟩
  split
  · decide
  · simp only [allChars_append]
    refine ⟨by decide, allChars_ofList fun c hc => ?_⟩
    simp only [List.mem_append, List.mem_replicate] at hc
    rcases hc with ⟨_, rfl⟩ | hc
    · decide
    · simp [Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc]

end Num

end Css
