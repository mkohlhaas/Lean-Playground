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

