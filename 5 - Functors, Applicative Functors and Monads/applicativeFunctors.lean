/- ==================== -/
/- Applicative Functors -/
/- ==================== -/

-- Applicative captures function application in a language that has side effects.

-- E1 <*> E2 is syntactic sugar for Seq.seq E1 (fun () => E2).

instance : Applicative Option where
  pure x  := .some x
  seq f x := match f with
             | none   => none
             | some g => g <$> x ()

instance : Applicative (Except ε) where
  pure x  := .ok x
  seq f x := match f with
             | .error e => .error e
             | .ok g    => g <$> x ()

class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := Nat.add 

#check some Plus.plus                      
#check some Plus.plus <*> some 4           
#check some Plus.plus <*> some 4 <*> some 7

structure Pair (α β : Type) : Type where
  first  : α
  second : β

#check Pair
#print Pair

instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩

#eval id <$> Pair.mk 1 2

def Pair.pure1 (x : β) : Pair α β := _

-- we have no α -> we cannot define a pure function for Applicative
def Pair.pure2 (x : β) : Pair α β := Pair.mk _ x

/- ------------------------- -/
/- A Non-Monadic Applicative -/
/- ------------------------- -/

/- ---------- -/
/- User Input -/
/- ---------- -/

structure RawInput where
  name      : String
  birthYear : String

/- -------- -/
/- Subtypes -/
/- -------- -/

structure MySubtype {α : Type} (p : α → Prop) where
  val      : α
  property : p val

-- Lean has special syntax for Subtype.
-- if p has type α → Prop, then the type Subtype p can also be written {x : α // p x} (or {x // p x} when the type α can be inferred automatically)

-- FastPos uses Nat's fast arbitrary-precision number libraries
def FastPos : Type := {x : Nat // x > 0}

def one : FastPos := ⟨1, by decide⟩

instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp⟩

def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else none

/- --------------- -/
/- Validated Input -/
/- --------------- -/

structure CheckedInput (thisYear : Nat) : Type where
  name      : {n : String // n ≠ ""}
  birthYear : {y : Nat    // y > 1900 ∧ y ≤ thisYear}

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

instance : Append (NonEmptyList α) where
  append xs ys := { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

inductive Validate (ε α : Type) : Type where
  | ok     : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α

instance : Functor (Validate ε) where
  map f
  | .ok x        => .ok (f x)
  | .errors errs => .errors errs

instance : Applicative (Validate ε) where
  pure    := .ok
  seq f x := match f with
             | .ok g        => g <$> (x ())
             | .errors errs =>
               match x () with
               | .ok _         => .errors errs
               | .errors errs' => .errors (errs ++ errs')

def Field := String
def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }

-- in the then branch h is bound to evidence that  name = ""
-- in the else branch h is bound to evidence that ¬name = "" 
def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x        => next x

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trimAscii.toNat? with
  | none   => reportError "birth year" "Must be digits"
  | some n => pure n

def checkBirthYear (thisYear birthYear : Nat) : Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : birthYear > 1900 then
    if h' : birthYear ≤ thisYear then
      pure ⟨birthYear, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"

def checkInput (thisYear : Nat) (input : RawInput) : Validate (Field × String) (CheckedInput thisYear) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen fun birthYearAsNat =>
      checkBirthYear thisYear birthYearAsNat

/- abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop := -/
/-   i ≤ xs.tail.length -/

/- def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α := -/
/-   match i with -/
/-   | 0     => xs.head -/
/-   | n + 1 => xs.tail[n] -/

/- instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where -/
/-   getElem := NonEmptyList.get -/

deriving instance Repr for NonEmptyList, Validate, CheckedInput

#eval checkInput 2023 {name := "David", birthYear := "1984"}  
#eval checkInput 2023 {name := "David", birthYear := "syzygy"}
#eval checkInput 2023 {name := "",      birthYear := "2045"}  

