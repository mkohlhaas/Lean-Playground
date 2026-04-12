-- from previous chapters

-- State's result is a function (type) that takes an input state and returns a pair of an output state and a value
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)                             -- function from a starting state to a pair of a final state and a value

def get : State σ σ :=
  fun s => (s, s)

def set (s : σ) : State σ Unit :=
  fun _ => (s, ())

/- -------------------- -/
/- The Monad Type Class -/
/- -------------------- -/

class MyMonad (m : Type → Type) where
  pure   : α → m α                  -- was ok      in the previous chapter
  bind : m α → (α → m β) → m β    -- was andThen in the previous chapter

#check Monad

instance : Monad Option where
  pure x        := some x
  bind opt next := match opt with
                   | none   => none
                   | some x => next x

instance : Monad (Except ε) where
  pure x            := Except.ok x
  bind attempt next := match attempt with
                       | Except.error e => Except.error e
                       | Except.ok x    => next x
                       
-- infix version of bind is >>= (>> =)

-- defined polymorphically for ANY monad
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first   =>
  lookup xs 2 >>= fun third   =>
  lookup xs 4 >>= fun fifth   =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

def slowMammals : List String := ["Three-toed sloth", "Slow loris"]
def fastBirds   : List String := ["Peregrine falcon",
                                  "Saker falcon",
                                  "Golden eagle",
                                  "Gray-headed albatross",
                                  "Spur-winged goose",
                                  "Swift",
                                  "Anna's hummingbird"]

def getOrOpt (xs : List α) (i : Nat) : Option α :=
  xs[i]?
                              
#eval firstThirdFifthSeventh getOrOpt slowMammals   
#eval firstThirdFifthSeventh getOrOpt fastBirds     

def getOrExcept (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none   => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x

#eval firstThirdFifthSeventh getOrExcept slowMammals
#eval firstThirdFifthSeventh getOrExcept fastBirds  

/- ------------------------ -/
/- General Monad Operations -/
/- ------------------------ -/

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | []      => pure []
  | x :: xs => f x       >>= fun hd =>
               mapM f xs >>= fun tl =>
               pure (hd :: tl)

#check (State Int)

-- State α, e.g. State Int is a monad
instance : Monad (State σ) where
  pure x            := fun s => (s, x)
  bind initial next := fun s => let (s', x) := initial s
                                next x s'

-- increment increases a saved state by a given amount, returning the old value
def increment (howMuch : Int) : State Int Int :=
  get               >>= fun i  =>
  set (i + howMuch) >>= fun () =>
  pure i

#check (increment)                     

-- `mapM increment` has type List Int → State Int (List Int).
-- Expanding the definition of State yields List Int → Int → (Int × List Int).
-- It takes an initial sum/state as an argument, which should be 0.
#check mapM increment                  
#check mapM increment [1, 2, 3, 4, 5]  
#check mapM increment [1, 2, 3, 4, 5] 0

#eval  mapM increment [1, 2, 3, 4, 5] 0

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

#check (WithLog)                       
  
-- polymorphic with respect to the type of the logged data
instance : Monad (WithLog logged) where
  pure x            := {log := [], val := x}
  bind withLog next := let {log := thisOut, val := result}  := withLog
                       let {log := nextOut, val := result'} := next result
                       {log := thisOut ++ nextOut, val := result'}

def isEven (i : Int) : Bool :=
  i % 2 == 0                   
  
def save (data : α) : WithLog α Unit :=
  {log := [data], val := ()} 

-- logs even numbers and returns its argument unchanged
def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i
    then save i
    else pure ())
  >>= fun () => pure i

-- Using this function with mapM results in a log containing even numbers paired with an unchanged input list:
#eval mapM saveIfEven [1, 2, 3, 4, 5] 

/- ------------------ -/
/- The Identity Monad -/
/- ------------------ -/

-- The identity monad is a monad that has no effects.
-- It allows pure code to be used with monadic APIs.
def MyId (t : Type) : Type := t

#check (Id)

-- results are of type Id x, but
-- Id x == x
instance : Monad Id where
  pure x   := x
  bind x f := f x

-- Lean doesn't know which monad is used here.
def numbers1 := mapM (do return · + 1) [1, 2, 3, 4, 5]

-- type hint needed for m 
def numbers2 := mapM (m := Id) (do return · + 1) [1, 2, 3, 4, 5]

-- for Id mapM acts like map
#eval numbers2

/- ------------------ -/
/- The Monad Contract -/
/- ------------------ -/

-- see PureScript

/- --------- -/
/- Exercises -/
/- --------- -/

/- ----------------- -/
/- Mapping on a Tree -/
/- ----------------- -/

-- TBD

/- ------------------------- -/
/- The Option Monad Contract -/
/- ------------------------- -/

-- TBD
