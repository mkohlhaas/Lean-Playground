-- from previous chapters

structure LetterCounts where
  vowels     : Nat
  consonants : Nat
deriving Repr

inductive Err where
  | notALetter : Char → Err
deriving Repr

def vowels :=
  let lowerVowels := "aeiuoy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants :=
  let lowerConsonants := "bcdfghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper )

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

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _      => Many.none
  | Many.more x xs, f => (f x).union $ bind (xs ()) f

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

instance : Alternative Many where
  failure := .none
  orElse  := Many.orElse

-- ---------------- --
-- More do Features --
-- ---------------- --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#more-do-features

-- ------------------ --
-- Single-Branched if --
-- ------------------ --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#single-branched-if

def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | []      => pure ()
    | c :: cs => if c.isAlpha then                                              
                   if vowels.contains c then                                    
                     modify fun st => {st with vowels := st.vowels + 1}         
                   else if consonants.contains c then                           
                     modify fun st => {st with consonants := st.consonants + 1} 
                   else
                     pure () -- NOTE: superfluous! Lean inserts it automatically!
                 else throw $ .notALetter c                                     
                 loop cs
  loop str.toList

-- count the entries in a list that satisfy some monadic check
def count [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | []      => pure ()
  | x :: xs => do
               if ← p x
                 then modify (· + 1)
                 -- NOTE: missing else branch is replaced `pure ()`
               count p xs
 
def countNot [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
 | []      => pure ()
 | x :: xs => do
              unless ← p x do
                modify (· + 1)
              -- NOTE: missing else branch is replaced `pure ()`
              countNot p xs              

-- ------------ --
-- Early Return --
-- ------------ --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#early-return

def List.find'? (p : α → Bool) : List α → Option α
  | []      => none
  | x :: xs => if p x
                 then some x     
                 else find'? p xs 

def List.find''? (p : α → Bool) : List α → Option α
  | []      => failure
  | x :: xs => do
               if p x then return x
               find''? p xs

-- strip outer monad; exception type and return type are the same
def runCatch [Monad m] (action : ExceptT α m α) : m α := do
  match ← action with
  | Except.ok    x => pure x
  | Except.error x => pure x

#print ExceptT

def List.find'''? (p : α → Bool) : List α → Option α
  | []      => failure
  | x :: xs => runCatch do -- in `ExceptT α Option α` monad
                 if p x
                   then throw x
                   else pure () 
                 monadLift $ find'''? p xs        

-- typical main program; checking inputs
-- without early return; nested if's
def main' (argv : List String) : IO UInt32 := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  if argv != [] then
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    pure 1
  else
    stdout.putStrLn "How would you like to be addressed?"
    stdout.flush

    let name := (← stdin.getLine).trimAscii
    if name == "" then
      stderr.putStrLn s!"No name provided"
      pure 1
    else
      stdout.putStrLn s!"Hello, {name}!"
      pure 0

-- with early return
def main'' (argv : List String) : IO UInt32 := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  unless argv == [] do
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    return 1

  stdout.putStrLn "How would you like to be addressed?"
  stdout.flush

  let name := (← stdin.getLine).trimAscii
  if name == "" then
    stderr.putStrLn s!"No name provided"
    return 1

  stdout.putStrLn s!"Hello, {name}!"

  return 0

-- $ lean --run moreDoFeatures.lean
-- $ lean --run moreDoFeatures.lean Hans

-- NOTE: early return applies only to the current do-block
def greet (name : String) : String :=
  "Hello, " ++ Id.run do return name

-- "Hello, Hans", not just "Hans"
#eval greet "Hans"

-- ----- --
-- Loops --
-- ----- --

-- every loop can be rewritten as a recursive function

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#loops

-- ----------------- --
-- Looping with ForM --
-- ----------------- --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#looping-with-forM

-- type class describing looping over a container type in some monad
-- m is a monad with some desired effects
-- γ is the collection to be looped over
-- α is the type of elements from the collection.
-- Because forM is intended to be used in do-blocks, it uses Monad rather than Applicative.
class MyForM (m : Type u → Type v) (γ : Type w₁) (α : outParam (Type w₂)) where
  forM [Monad m] : γ → (α → m PUnit) → m PUnit
  
#print ForM

def List.myforM [Monad m] : List α → (α → m PUnit) → m PUnit
  | [], _           => pure ()
  | x :: xs, action => do
                       action x
                       myforM xs action

instance : MyForM m (List α) α where
  forM := List.myforM

def countLetters' (str : String) : StateT LetterCounts (Except Err) Unit :=
  forM str.toList 
       fun c => do
                if c.isAlpha then
                  if vowels.contains c then
                    modify fun st => {st with vowels := st.vowels + 1}
                  else if consonants.contains c then
                    modify fun st => {st with consonants := st.consonants + 1}
                else throw $ .notALetter c

def Many.forM [Monad m] : Many α → (α → m PUnit) → m PUnit
  | Many.none, _                 => pure ()
  | Many.more first rest, action => do
                                    action first
                                    forM (rest ()) action

-- TODO: should work for ForM
instance : MyForM m (Many α) α where
  forM := Many.forM

-- Because γ can be any type at all, ForM can support non-polymorphic collections.
structure AllLessThan where
  num : Nat

def AllLessThan.forM [Monad m] (coll : AllLessThan) (action : Nat → m Unit) : m Unit :=
  let rec countdown : Nat → m Unit
    | 0     => pure ()
    | n + 1 => do
               action n
               countdown n
  countdown coll.num

-- TODO: should work for ForM
instance : MyForM m AllLessThan Nat where
  forM := AllLessThan.forM

-- NOTE: should work when ForM instance for AllLessThan has been fixed
#eval forM { num := 5 : AllLessThan } IO.println

#eval AllLessThan.forM { num := 5 : AllLessThan } IO.println

structure LinesOf where
  stream : IO.FS.Stream

-- ForM instance that works only in a particular monad (IO in this case)
-- `forM` is marked partial because there is no guarantee that the stream is finite.
partial def LinesOf.forM (readFrom : LinesOf) (action : String → IO Unit) : IO Unit := do
  let line ← readFrom.stream.getLine -- getLine is in the IO monad (no other monad can be used)
  if line == "" then return ()
  action line
  forM readFrom action

instance : ForM IO LinesOf String where
  forM := LinesOf.forM

def main (argv : List String) : IO UInt32 := do
  if argv != [] then
    IO.eprintln "Unexpected arguments"
    return 1

  forM (LinesOf.mk (← IO.getStdin))
       fun line => do
                   if line.any (·.isAlpha) then
                     IO.print line
  return 0

-- ------------------ --
-- Stopping Iteration --
-- ------------------ --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#break

-- Terminating a loop early is difficult to do with ForM. 

-- discards information about both the return value and whether or not the transformed computation succeeded
-- in other words, discards everything
def OptionT.exec [Applicative m] (action : OptionT m α) : m Unit :=
  action *> pure ()

-- NOTE: should work when ForM instance for AllLessThan has been fixed
def countToThree' (n : Nat) : IO Unit :=
  let nums : AllLessThan := ⟨n⟩
  OptionT.exec $ forM nums fun i => do
    if i < 3 then failure else IO.println i

#eval countToThree' 7

-- NOTE: should work when ForM instance for AllLessThan has been fixed
-- Lean provides syntactic sugar to make this easier
def countToThree (n : Nat) : IO Unit := do
  let nums : AllLessThan := ⟨n⟩
  for i in nums do
    if i < 3 then break
    IO.println i

instance : ForIn m AllLessThan Nat where
  forIn := ForM.forIn

-- ----------------- --
-- Mutable Variables --
-- ----------------- --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#let-mut

-- -------------------------- --
-- What counts as a do block? --
-- -------------------------- --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#do-block-boundaries

-- ------------------------------------- --
-- Imperative or Functional Programming? --
-- ------------------------------------- --

-- Monads and monad transformers allow functional versus imperative programming to be a matter of perspective.

-- --------- --
-- Exercises --
-- --------- --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#monad-transformer-do-exercises
