/- ==================== -/
/- Applicative Functors -/
/- ==================== -/

-- Applicative captures function application in a language that has side effects.

-- E1 <*> E2 is syntactic sugar for `seq E1 E2`. (actually: seq E1 (fun () => E2))
-- E1 <$> E2 is syntactic sugar for `map E1 E2`.

-- `seq` is much like `map` but function (f) and data (x) are contained in the datatype.

-- Applicative needs an additional `pure` function in comparison to Functor.

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

-- Not every functor is applicative.
-- Pair is like the built-in product type Prod.
structure Pair (α β : Type) : Type where
  first  : α
  second : β
deriving BEq

#check Pair                                           
#print Pair                                           

instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩

#eval id <$> Pair.mk 1 2                              
#eval id <$> Pair.mk 1 2 == Pair.mk 1 2               

-- for an Applicative instance we need a `pure` function
-- we have no type for α (alpha)
-- we cannot define a pure function for Applicative
def Pair.pure1 (x : β) : Pair α β := _          
def Pair.pure2 (x : β) : Pair α β := Pair.mk _ x

/- ------------------------- -/
/- A Non-Monadic Applicative -/
/- ------------------------- -/

-- Applicative functor called Validate.
-- Used for input validation.
-- Validate allows multiple errors to be accumulated (unlike Except).

/- ---------- -/
/- User Input -/
/- ---------- -/

structure RawInput where
  name      : String  -- may not be empty
  birthYear : String  -- must be numeric and non-negative; must be greater than 1900, and less than or equal to the year in which the form is validated

/- -------- -/
/- Subtypes -/
/- -------- -/

-- Representing these constraints on name and birthYear as a datatype will require a new feature, called subtypes. 

structure MySubtype {α : Type} (p : α → Prop) where
  val      : α
  property : p val

#print Subtype

-- Lean has special syntax for Subtype.
-- If p has type α → Prop, then the type Subtype p can also be written {x : α // p x}
-- {x // p x} when the type α can be inferred automatically.
def evenNumbers                : Type := { n : Nat // n % 2 = 0 }
def arraysWithFiveCharsStrings : Type := { xs : Array String // xs.size = 5 }
def subLists (xs : List α) : Type := List { x : α // x ∈ xs } -- type of lists in which all elements are contained in `xs`

-- FastPos uses Nat's fast arbitrary-precision number libraries
def FastPos : Type := {x : Nat // x > 0}

-- Instead of being a constructor of an inductive type, it's an instance of a structure that's constructed with angle brackets.
-- The first argument is the underlying Nat, and the second argument is the evidence that said Nat is greater than zero.
def one : FastPos := ⟨1, by decide⟩

-- from Nat to FastPos
instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp⟩ -- tactic proof `simp` for n + 1 > 0; `simp` is needed because `decide` requires concrete values

-- evidence-providing/binding version of `if`
def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0       -- `h` is the name of the decidable proposition n > 0
    then some ⟨n, h⟩ -- evidence the proposition is true
    else none

-- Subtypes are a two-edged sword. They allow efficient representation of
-- validation rules, but they transfer the burden of maintaining these rules to
-- the users of the library, who have to prove that they are not violating
-- important invariants. Generally, it's a good idea to use them internally to a
-- library, providing an API to users that automatically ensures that all
-- invariants are satisfied, with any necessary proofs being internal to the
-- library.

/- --------------- -/
/- Validated Input -/
/- --------------- -/

structure CheckedInput (thisYear : Nat) : Type where
  name      : {n : String // n.trimAscii.copy ≠ ""}
  birthYear : {y : Nat    // y > 1900 ∧ y ≤ thisYear}

#print CheckedInput 

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

instance : Append (NonEmptyList α) where
  append xs ys := { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

def NEList1 := { head := 1, tail := [2, 3, 4, 5] : NonEmptyList Nat}
def NEList2 := { head := 6, tail := [7, 8, 9, 0] : NonEmptyList Nat}

#eval NEList1 ++ NEList2

-- ε is error, α is data
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
    | .ok g        => g <$> x ()
    | .errors errs => match x () with
        | .ok _         => .errors errs
        | .errors errs' => .errors (errs ++ errs')

-- While this function's type signature makes it suitable to be used as bind in a Monad instance, there are good reasons not to do so. 
-- see section 'Additional Stipulations' in applicativeContract.lean
def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x        => next x

def FieldName := String
def Message   := String

def reportError (f : FieldName) (msg : Message) : Validate (FieldName × Message) α :=
  .errors { head := (f, msg), tail := [] }

deriving instance Repr for NonEmptyList, Validate, CheckedInput

#eval (reportError "name" "required"             : Validate _ Empty)
#eval (reportError "birth year" "must be digits" : Validate _ Empty)

def checkName (name : String) : Validate (FieldName × Message) {n : String // n.trimAscii.copy ≠ ""} :=
  if h : name.trimAscii.copy = ""
    then reportError "name" "required"
    else pure ⟨name, h⟩

def checkYearIsNat (year : String) : Validate (FieldName × Message) Nat :=
  match year.trimAscii.toNat? with
  | none   => reportError "birth year" "must be digits"
  | some n => pure n

def checkBirthYear (thisYear birthYear : Nat) : Validate (FieldName × Message) {y // y > 1900 ∧ y ≤ thisYear} :=
  if h : birthYear > 1900
    then if h' : birthYear ≤ thisYear
           then pure ⟨birthYear, by simp [*]⟩ -- NOTE: `simp [*]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and all hypotheses
           else reportError "birth year" s!"must be no later than {thisYear}"
    else reportError "birth year" "must be after 1900"

-- compare to basically this form: CheckedInput.mk name birthYear
-- now everything is covered in Validate
def checkInput (input : RawInput) (thisYear : Nat) : Validate (FieldName × Message) (CheckedInput thisYear) :=
  pure CheckedInput.mk <*>
  checkName input.name <*>
  (checkYearIsNat input.birthYear).andThen (fun birthYearAsNat => checkBirthYear thisYear birthYearAsNat)

#eval checkInput {name := "David", birthYear := "1984"} 2023
#eval checkInput {name := "David", birthYear := "syzy"} 2023
#eval checkInput {name := "     ", birthYear := "1984"} 2023
#eval checkInput {name := "",      birthYear := "2045"} 2023

-- Applicative's <*> may run both of its arguments (in PARALLEL) before recombining the results.
-- Monad's >>= forces SEQUENTIAL execution. Each step must complete before the next may run.
