-- from previous chapters

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

def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = ""
    then reportError "name" "required"
    else pure ⟨name, h⟩

structure RawInput where
  name      : String
  birthYear : String

/- ============ -/
/- Alternatives -/
/- ============ -/

/- --------------------- -/
/- Recovery from Failure -/
/- --------------------- -/

abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970 : (birthYear : {y : Nat // y > 999 ∧ y < 1970}) → String → LegacyCheckedInput -- users born prior to 1970 do not need to provide names, due to incomplete older records
  | humanAfter1970  : (birthYear : {y : Nat // y > 1970}) → NonEmptyString → LegacyCheckedInput   -- users born after 1970 must provide names
  | company         : NonEmptyString → LegacyCheckedInput                                         -- companies should enter "FIRM" as their year of birth and provide a company name
deriving Repr

class MyOrElse (α : Type) where
  orElse : α → (Unit → α) → α                    

-- The expression E1 <|> E2 is short for OrElse.orElse E1 E2 (actually: OrElse.orElse E1 (fun () => E2)).

#print OrElse

def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
  match a with
  | .ok x         => .ok x
  | .errors errs1 => match b () with
                     | .ok x         => .ok x
                     | .errors errs2 => .errors (errs1 ++ errs2)

instance : OrElse (Validate ε α) where
  orElse := Validate.orElse

def checkThat (condition : Bool) (field : Field) (msg : String) : Validate (Field × String) Unit :=
  if condition
    then pure ()
    else reportError field msg

def checkCompany' (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  pure (fun () name => .company name)                                    <*> -- anonymous function of `()` and `name`
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" <*> -- ()
  checkName input.name                                                       -- name

deriving instance Repr for NonEmptyList, Validate

#eval checkCompany' ⟨"Johnny's Troll Groomers", "FIRM"⟩
#eval checkCompany' ⟨"Johnny", "1963"⟩                 

class MySeqRight (f : Type → Type) where
  seqRight : f α → (Unit → f β) → f β

-- E1 *> E2 is syntactic sugar for SeqRight.seqRight E1 E2 (actually: SeqRight.seqRight E1 (fun () => E2))

#print SeqRight
#print SeqLeft 

-- default implementation of seqRight in terms of seq:
-- seqRight (a : f α) (b : Unit → f β) : f β :=
--   pure (fun _ x => x) <*> a <*> b ()

def checkCompany'' (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  pure .company                                                         <*>
  checkName input.name

#eval checkCompany'' ⟨"Johnny's Troll Groomers", "FIRM"⟩
#eval checkCompany'' ⟨"Johnny", "1963"⟩                 

-- for every Applicative `pure f <*> E` is equivalent to `f <$> E` 
def checkCompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  .company                                                              <$>
  checkName input.name

#eval checkCompany ⟨"Johnny's Troll Groomers", "FIRM"⟩
#eval checkCompany ⟨"Johnny", "1963"⟩                 

-- NOTE: type class [Decidable (p v)] occurs after the specification of the at this point known arguments v and p
def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε) : Validate ε {x : α // p x} :=
  if h : p v
    then pure ⟨v, h⟩
    else .errors { head := err, tail := [] }

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trimAscii.toNat? with
  | none   => reportError "birth year" "must be digits"
  | some n => pure n

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x        => next x

def checkBirthYear (thisYear birthYear : Nat) : Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : birthYear > 1900
    then if h' : birthYear ≤ thisYear
           then pure ⟨birthYear, by simp [*]⟩
           else reportError "birth year" s!"must be no later than {thisYear}"
    else reportError "birth year" "must be after 1900"

def checkHumanBefore1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun birthYear =>
  .humanBefore1970                                                                      <$>
  checkSubtype birthYear (fun x => x > 999 ∧ x < 1970) ("birth year", "less than 1970") <*>
  pure input.name

def checkHumanAfter1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun birthYear =>
  .humanAfter1970                                                       <$>
  checkSubtype birthYear (· > 1970) ("birth year", "greater than 1970") <*>
  checkName input.name

def checkLegacyInput (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkCompany         input <|>
  checkHumanBefore1970 input <|>
  checkHumanAfter1970  input

deriving instance Repr for NonEmptyList, Validate

#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
#eval checkLegacyInput ⟨"Johnny", "1963"⟩                 
#eval checkLegacyInput ⟨"Jacky", "1973"⟩                  
#eval checkLegacyInput ⟨"", "1963"⟩                       
#eval checkLegacyInput ⟨"", "1970"⟩                       

/- --------------------- -/
/- The Alternative Class -/
/- --------------------- -/

class MyAlternative (f : Type → Type) extends Applicative f where
  failure : f α
  orElse  : f α → (Unit → f α) → f α

#print Alternative

-- implementors of Alternative get OrElse instances for free
instance [Alternative f] : OrElse (f α) where
  orElse := Alternative.orElse

-- keep the first non-none argument
instance : Alternative Option where
  failure := none
  orElse
    | some x, _ => some x -- take first  alternative
    | none,   g => g ()   -- take second alternative

inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, ys      => ys ()
  | .more x xs, ys => .more x (fun () => orElse (xs ()) ys)

def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

def Many.union : Many α → Many α → Many α
  | Many.none, ys      => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

def Many.takeAll : Many α → List α
  | Many.none      => []
  | Many.more x xs => x :: (xs ()).takeAll

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _      => Many.none
  | Many.more x xs, f => (f x).union $ bind (xs ()) f

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

instance : Alternative Many where
  failure := .none
  orElse  := Many.orElse

-- `Decidable` instances are primarily used via `if`-expressions and the tactic
-- `decide`. In conditional expressions, the `Decidable` instance for the
-- proposition is used to select a branch. At run time, this case distinction code
-- is identical to that which would be generated for a `Bool`-based conditional.
-- In proofs, the tactic `decide` synthesizes an instance of `Decidable p`,
-- attempts to reduce it to `isTrue h`, and then succeeds with the proof `h` if it can.

-- guard works for any Applicative Functor that implements Alternative
-- can be used to filter out a whole branch of a search
def my_guard [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p
    then pure ()
    else failure

def Many.countdown : Nat → Many Nat
  | 0     => .none
  | n + 1 => .more n (fun () => countdown n)

#eval (Many.countdown 10).takeAll

-- TODO: better understand this
def evenDivisors (n : Nat) : Many Nat := do
  let k ← .countdown (n + 1)
  guard $ k % 2 = 0 -- k is even
  guard $ n % k = 0 -- k is a divisor of n
  pure k

#eval (evenDivisors 20).takeAll 

/- ========= -/
/- Exercises -/
/- ========= -/

/- ------------------------------- -/
/- Improve Validation Friendliness -/
/- ------------------------------- -/

inductive TreeError where
  | field : Field → String → TreeError
  | path  : String → TreeError → TreeError
  | both  : TreeError → TreeError → TreeError

instance : Append TreeError where
  append := .both
