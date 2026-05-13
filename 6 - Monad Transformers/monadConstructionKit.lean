-- ------------------------ --
-- A Monad Construction Kit --
-- ------------------------ --

-- Each monad transformer consists of the following:
--  · A definition or datatype T that takes a monad as an argument. It should have a type like (Type u → Type v) → Type u → Type v, though it may accept additional arguments prior to the monad.
--  · A Monad instance for T m that relies on an instance of Monad m. This enables the transformed monad to be used as a monad.
--  · A MonadLift instance that translates actions of type m α into actions of type T m α, for arbitrary monads m. This enables actions from the underlying monad to be used in the transformed monad.
-- -------------------- --
-- Failure with OptionT --
-- -------------------- --

-- OptionT IO String, aka IO (Option String)
def getSomeInput : OptionT IO String := do -- in OptionT IO
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trimAscii.copy
  if trimmed == ""
    then failure
    else pure trimmed

-- ReaderT and OptionT have different order of inner and outer monad
-- `(Type u → Type v)` is existing monad
#print ReaderT            
#print OptionT            

structure UserInfo where
  name           : String
  favoriteBeetle : String

#print UserInfo           

#check IO                 
#check UserInfo           
#check OptionT IO         
#check OptionT IO UserInfo
#check ReaderT UserInfo IO

-- OptionT IO UserInfo, aka IO (Option UserInfo)
def getUserInfo : OptionT IO UserInfo := do               -- in OptionT IO monad
  IO.println "What is your name?"                         -- IO (will be automatically lifted into OptionT IO)
  let name ← getSomeInput                                 -- OptionT IO String
  IO.println "What is your favorite species of beetle?"   -- IO (will be automatically lifted into OptionT IO)
  let beetle ← getSomeInput                               -- OptionT IO String
  pure ⟨name, beetle⟩                                     -- OptionT IO UserInfo

def interact : IO Unit := do -- in IO monad
  match ← getUserInfo with
  | none                => IO.eprintln "Missing info"
  | some ⟨name, beetle⟩ => IO.println s!"Hello {name}, whose favorite beetle is {beetle}."

-- ------------------ --
-- The Monad Instance --
-- ------------------ --

-- Errors: compiler selects the wrong Monad instance for `pure`
-- instance [Monad m] : Monad (OptionT m) where
--   pure x           := pure $ some x
--   bind action next := do
--                       match ← action with
--                       | none   => pure none
--                       | some v => next v

-- with noisy, ugly type annotations
instance [Monad m] : Monad (OptionT m) where
  pure x           := (pure $ some x : m (Option _))
  bind action next := (do
                       match ← action with
                       | none   => pure none
                       | some v => next v : m (Option _))

-- helps the type checker to find the correct monad instances
-- def OptionT.mk  (x : m (Option α)) : OptionT m α  := x  -- intends usage of OptionT
-- def OptionT.run (x : OptionT m α)  : m (Option α) := x  -- intends usage of underlying monad

-- with OptionT.mk
instance [Monad m] : Monad (OptionT m) where
  pure x           := OptionT.mk $ pure $ some x
  bind action next := OptionT.mk do
                                 match ← action with
                                 | none   => pure none
                                 | some v => next v
 
-- ----------------------- --
-- An Alternative Instance --
-- ----------------------- --

instance [Monad m] : Alternative (OptionT m) where
 failure    := OptionT.mk $ pure none
 orElse x y := OptionT.mk do
                          match ← x with
                          | none        => y ()
                          | some result => pure $ some result

-- ------- --
-- Lifting --
-- ------- --

instance [Monad m] : MonadLift m (OptionT m) where
  monadLift action := OptionT.mk do -- in `m (Option α)` monad
                                 pure $ some $ ← action

instance [Monad m] : MonadLift m (OptionT m) where
  monadLift action := OptionT.mk $ some <$> action

-- ---------- --
-- Exceptions --
-- ---------- --

#print Except  
#print ExceptT 

-- helps the type checker to find the correct monad instances
-- def ExceptT.mk  {ε α : Type u} (x : m (Except ε α)) : ExceptT ε m α  := x
-- def ExceptT.run {ε α : Type u} (x : ExceptT ε m α)  : m (Except ε α) := x

instance {ε : Type u} {m : Type u → Type v} [Monad m] : Monad (ExceptT ε m) where
  pure x           := ExceptT.mk $ pure $ .ok x
  bind result next := ExceptT.mk do -- in `m (Except ε α)` monad
                                 match ← result with
                                 | .error e => pure $ .error e
                                 | .ok x    => next x
 
instance [Monad m] : MonadLift (Except ε) (ExceptT ε m) where
  monadLift action := ExceptT.mk $ pure action                                

instance [Monad m] : MonadLift m (ExceptT ε m) where
  monadLift action := ExceptT.mk do
                                 pure $ .ok $ ← action                                
 
instance [Monad m] : MonadLift m (ExceptT ε m) where
  monadLift action := ExceptT.mk $ .ok <$> action                                

-- --------------------------- --
-- Type Classes for Exceptions --
-- --------------------------- --

class MyMonadExcept (ε : outParam (Type u)) (m : Type v → Type w) where
  throw    : ε → m α
  tryCatch : m α → (ε → m α) → m α

#print MonadExcept

inductive Err where
  | divByZero
  | notANumber : String → Err

def divBackend [Monad m] [MonadExcept Err m] (n k : Int) : m Int :=
  if k == 0
    then throw .divByZero
    else pure $ n / k

def asNumber [Monad m] [MonadExcept Err m] (s : String) : m Int :=
  match s.toInt? with
  | none   => throw $ .notANumber s
  | some i => pure i

def divFrontend' [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  tryCatch (do pure $ toString $ ← divBackend (← asNumber n) (← asNumber k))
           fun
             | .divByZero    => pure "Division by zero!"
             | .notANumber s => pure s!"Not a number: \"{s}\""

--  Special syntax:
-- `try` and `catch` can be used as shorthand for `tryCatch`

def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  try
    pure $ toString $ ← divBackend (← asNumber n) (← asNumber k)
  catch
    | .divByZero    => pure "Division by zero!"
    | .notANumber s => pure s!"Not a number: \"{s}\""

-- There are useful MonadExcept instances for other types that may not seem
-- like exceptions at first glance. For example, failure due to Option can be
-- seen as throwing an exception that contains no data whatsoever, so there is
-- an instance of `MonadExcept Unit Option` that allows try ...catch ... syntax
-- to be used with Option.

-- TODO: example for divFrontend
-- #eval divFrontend "55" "5"

-- ----- --
-- State --
-- ----- --

def MyStateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) := σ → m (α × σ)

#print StateT 

instance [Monad m] : Monad (StateT σ m) where
  pure x           := fun s => pure (x, s)
  bind result next := fun s => do
                               let (v, s') ← result s
                               next v s'

-- counting the number of diacritic-free English vowels and consonants in a string of letters

structure LetterCounts where
  vowels     : Nat
  consonants : Nat
deriving Repr

inductive Err1 where
  | notALetter : Char → Err1
deriving Repr

def vowels :=
  let lowerVowels := "aeiuoy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants :=
  let lowerConsonants := "bcdfghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper )

#eval vowels    
#eval consonants

def countLetters' (str : String) : StateT LetterCounts (Except Err1) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | []      => pure ()
    | c :: cs => let st  ← get                                         
                 let st' ← if c.isAlpha then                                                                               
                             if vowels.contains c then                         
                               pure {st with vowels := st.vowels + 1}          
                             else if consonants.contains c then                
                               pure {st with consonants := st.consonants + 1}  
                             else -- modified or non-English letter            
                               pure st                                         
                           else throw $ .notALetter c                          
                 set st' -- could be easily wrongly written as `set st`
                 loop cs                                              
  loop str.toList

#eval "hello".toList

#eval countLetters' "hello"  ⟨0, 0⟩
#eval countLetters' "hello!" ⟨0, 0⟩

-- NOTE: better to use `modify` (instead of `get` and `set`)
def countLetters (str : String) : StateT LetterCounts (Except Err1) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | []      => pure ()
    | c :: cs => if c.isAlpha then                                              
                   if vowels.contains c then                                    
                     modify fun st => {st with vowels := st.vowels + 1}         
                   else if consonants.contains c then                           
                     modify fun st => {st with consonants := st.consonants + 1} 
                   else -- modified or non-English letter                       
                     pure ()                                                    
                 else throw $ .notALetter c                                     
                 loop cs
  loop str.toList

#eval countLetters "hello"  ⟨0, 0⟩
#eval countLetters "hello!" ⟨0, 0⟩


class MyMonadState (σ : outParam (Type u)) (m : Type u → Type v) : Type (max (u+1) v) where
  get           : m σ
  set           : σ → m PUnit
  modifyGet : (σ → α × σ) → m α

def myModify [MonadState σ m] (f : σ → σ) : m Unit :=
  modifyGet fun s => ((), f s)

-- PUnit is a version of the Unit type that is universe-polymorphic to allow it to be in Type u instead of Type.
#print modify

-- ---------------------------- --
-- Of Classes and The Functions --
-- ---------------------------- --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/A-Monad-Construction-Kit/#of-and-the

-- ------------------- --
-- Transformers and Id --
-- ------------------- --

-- The identity monad Id is the monad that has no effects whatsoever, to be used
-- in contexts that expect a monad for some reason but where none is actually
-- necessary.

-- Another use of Id is to serve as the bottom of a stack of monad
-- transformers. For instance, `StateT σ Id` works just like `State σ`.
